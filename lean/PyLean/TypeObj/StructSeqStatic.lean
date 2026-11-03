import PyLean.TypeObj.StructSeqNewType

/-!
# Static struct sequence types: `PyStructSequence_InitType2` and `PyStructSequence_InitType`

Objects/structseq.c:573-593 (`initialize_static_fields`), :595-611 (`initialize_static_type`),
:672-704 (`PyStructSequence_InitType2`) and :706-710 (`PyStructSequence_InitType`), CPython
3.15.2. These fill a caller-provided `PyTypeObject` in place, the static twin of
`PyStructSequence_NewType`.

What is modelled besides `StructSeqC.lean`:

* The type's refcount on entry (:688-691; a zeroed `PyTypeObject` has 0). The `Py_TRACE_REFS`
  block (:678-685) exists only in that debug build and is not modelled.
* `PyType_Ready` on the static type (Objects/typeobject.c:9711-9736): it first makes the type
  immutable and immortal (:9719-9724), then runs `type_ready` (:9584-9668). The steps that
  depend on the struct sequence's layout are modelled: `inherit_special` turns a basicsize of 0
  into tuple's 32 (:8812-8813), and `type_ready_post_checks` refuses `tp_dictoffset +
  tp_basicsize <= 0` (:9571-9577). Unlike `PyType_FromMetaclass`, nothing compares the
  basicsize with tuple's, and nothing looks at member names such as `__dictoffset__`. The other
  steps are `ReadyRest`, arbitrary outcomes, its own and separate from the rest of
  `PyType_FromSpecWithBases` that `newType` takes: those before `type_ready_fill_dict`, the
  dict fill itself, which creates the member descriptors (pointing into `tp_members`) and may
  fail after some of them, and those after it. On failure `type_ready` keeps `tp_dict`
  (:9665-9667).
* What the call leaves behind (`StaticState`): whether it made the type immortal and ready,
  whether member descriptors over `tp_members` are in its dict, and whether it freed the
  `tp_members` array. The type's flags beyond immutability (`Py_TPFLAGS_DEFAULT |
  Py_TPFLAGS_HAVE_GC`, :590) are not modelled.
-/

namespace PyLean.TypeObj.StructSeq

open PyLean PyLean.UnicodeObj

/-- What a call leaves in the type object. -/
structure StaticState where
  /-- `PyType_Ready` ran: the type is immutable and immortal, so its refcount is no longer 0. -/
  immortal : Bool
  /-- `Py_TPFLAGS_READY` is set. -/
  ready : Bool
  /-- Member descriptors pointing into `tp_members` are in the type's dict. -/
  descriptors : Bool
  /-- The `tp_members` array was freed. -/
  membersFreed : Bool
  deriving DecidableEq, Repr

/-- The steps of `type_ready` the model does not mirror. -/
structure ReadyRest where
  /-- `type_ready_pre_checks` .. `type_ready_set_new` (typeobject.c:9591-9622). -/
  beforeFill : Py Unit
  /-- `type_ready_fill_dict` (:9623-9625), which adds the member descriptors. -/
  fill : Py Unit
  /-- When `fill` fails: whether some member descriptors were already added. -/
  fillPartial : Bool
  /-- `type_ready_inherit` .. `type_ready_managed_dict` (:9626-9645), but the basicsize rules. -/
  afterFill : Py Unit

/-- Every unmodelled step succeeds. -/
def ReadyRest.allOk : ReadyRest := ⟨.ok (), .ok (), false, .ok ()⟩

/-- `type->tp_basicsize` as `initialize_static_fields` sets it (:581-582), in `Py_ssize_t`:
`sizeof(PyStructSequence) + (n_hidden - 1) * sizeof(PyObject *)`, with no `(int)` cast. -/
def staticBasicsize (nMembers : Nat) (nInSeq : Int) : Int := 40 + ((nMembers : Int) - nInSeq - 1) * 8

/-- `PyType_Ready` of the static type, as far as `tp_basicsize` goes: the basicsize, or the
error; and whether the member descriptors are in the dict afterwards. -/
def typeReadyStatic (name : Bytes) (basicsize : Int) (r : ReadyRest) : CRes Nat × Bool :=
  match r.beforeFill with
  | .error e => (.exc e, false)
  | .ok () =>
    match r.fill with
    | .error e => (.exc e, r.fillPartial)
    | .ok () =>
      match r.afterFill with
      | .error e => (.exc e, true)
      | .ok () =>
        let bs := if basicsize = 0 then 32 else basicsize
        if bs ≤ 0 then
          (.exc (systemError s!"~type {String.ofList (name.map Char.ofNat)} has a tp_dictoffset that is too small"), true)
        else (.ok bs.toNat, true)

/-- `PyStructSequence_InitType2(type, desc)`, :672-704, with `initialize_static_fields`
(:573-593) and `initialize_static_type` (:595-611). `refcnt` is `Py_REFCNT(type)` on entry,
`malloc` the outcome of `PyMem_NEW` for `tp_members`, `ready` the unmodelled steps of
`PyType_Ready`. When `PyType_Ready` or the dict fails, :699-701 frees `members`, which the type
and its descriptors keep pointing at. -/
def initType2 (refcnt : Nat) (d : Desc) (malloc : Nat → Bool) (ready : ReadyRest) :
    CRes Built × StaticState :=
  if refcnt ≠ 0 then
    (.exc (systemError "Objects/structseq.c:689: bad argument to internal function"), ⟨false, false, false, false⟩)
  else
    let (n, u) := countMembers d.fields
    match initializeMembers d.fields n u malloc with
    | .ok ms =>
      match typeReadyStatic d.name (staticBasicsize n d.nInSeq) ready with
      | (.ok bs, descr) =>
        match initDict d n u with
        | .ok (dict, ma) =>
          (.ok { type := { name := d.name, members := ms, basicsize := bs, dict := dict }, matchArgs := ma },
            ⟨true, true, descr, false⟩)
        | .exc e => (.exc e, ⟨true, true, descr, true⟩)
        | .nullNoExc => (.nullNoExc, ⟨true, true, descr, true⟩)
        | .ub w => (.ub w, ⟨true, true, descr, true⟩)
      | (.exc e, descr) => (.exc e, ⟨true, false, descr, true⟩)
      | (.nullNoExc, descr) => (.nullNoExc, ⟨true, false, descr, true⟩)
      | (.ub w, descr) => (.ub w, ⟨true, false, descr, true⟩)
    | .exc e => (.exc e, ⟨false, false, false, false⟩)
    | .nullNoExc => (.nullNoExc, ⟨false, false, false, false⟩)
    | .ub w => (.ub w, ⟨false, false, false, false⟩)

/-- A `void` C call: it returns, possibly with an exception still set, or is undefined. -/
inductive VoidRes where
  | done
  | pending (e : PyExc)
  | ub (what : String)
  deriving DecidableEq, Repr

/-- `PyStructSequence_InitType(type, desc)`, :706-710: `(void)PyStructSequence_InitType2(...)`.
The caller cannot see a failure, and the exception stays set. -/
def initType (refcnt : Nat) (d : Desc) (malloc : Nat → Bool) (ready : ReadyRest) : VoidRes × StaticState :=
  let (r, st) := initType2 refcnt d malloc ready
  (match r with
   | .ok _ => .done
   | .exc e => .pending e
   | .nullNoExc => .done
   | .ub w => .ub w, st)

/-! ## The twin property -/

/-- For every valid desc (`0 ≤ n_in_sequence ≤ #fields`, fewer than `2^28 - 4` hidden fields,
where the `(int)` cast of `NewType` does not wrap) with no field named `__weaklistoffset__`,
`__dictoffset__` or `__vectorcalloffset__` (which only `PyType_FromMetaclass` treats
specially), and every allocator, when the steps neither model mirrors succeed on both sides,
`PyStructSequence_InitType2` on a fresh type gives exactly what `PyStructSequence_NewType` gives
(the same exception, or a type with the same name, `tp_members`, `tp_basicsize`, size attributes
and `__match_args__`), and on success leaves the type ready with its members.
`PyStructSequence_InitType` leaves no exception set exactly when InitType2 succeeds, and on a
failure returns with that exception still set. A type whose refcount is not 0 is refused with
`SystemError`. -/
def StaticTwin : Prop :=
  (∀ (refcnt : Nat) (d : Desc) (malloc : Nat → Bool) (ready : ReadyRest), refcnt ≠ 0 →
    (initType2 refcnt d malloc ready).1 =
      .exc (systemError "Objects/structseq.c:689: bad argument to internal function")) ∧
  (∀ (d : Desc) (malloc : Nat → Bool), specialCheck (namedFields d.fields) = none →
    0 ≤ d.nInSeq → d.nInSeq ≤ d.fields.length → (d.fields.length : Int) - d.nInSeq < 2 ^ 28 - 4 →
    (initType2 0 d malloc .allOk).1 = newType d malloc (.ok ()) ∧
    (∀ b, (initType2 0 d malloc .allOk).1 = .ok b → (initType2 0 d malloc .allOk).2 = ⟨true, true, true, false⟩)) ∧
  (∀ (refcnt : Nat) (d : Desc) (malloc : Nat → Bool) (ready : ReadyRest),
    ((initType refcnt d malloc ready).1 = .done ↔
      ((∃ b, (initType2 refcnt d malloc ready).1 = .ok b) ∨ (initType2 refcnt d malloc ready).1 = .nullNoExc)) ∧
    ∀ e, (initType refcnt d malloc ready).1 = .pending e ↔ (initType2 refcnt d malloc ready).1 = .exc e)

theorem staticTwin_proven : StaticTwin := by
  refine ⟨fun refcnt d malloc ready h => by simp [initType2, h], fun d malloc hs h0 h1 h2 => ?_, ?_⟩
  · have hst : staticBasicsize d.fields.length d.nInSeq = 40 + ((d.fields.length : Int) - d.nInSeq - 1) * 8 := rfl
    unfold initType2 newType
    rw [countMembers_eq]
    simp only [ne_eq, not_true_eq_false, if_false]
    unfold initializeMembers
    cases hm : malloc ((d.fields.length - d.fields.count .unnamed + 1) * 40) with
    | false => simp
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false, CRes.bind_ok, List.take_length]
      unfold typeReadyStatic fromSpecBasicsize
      rw [hst, toCInt_id _ (by omega) (by omega)]
      simp only [ReadyRest.allOk, initMembers_named, hs]
      rw [if_neg (show ¬ (40 + ((d.fields.length : Int) - d.nInSeq - 1) * 8 = 0) by omega),
        if_neg (show ¬ (40 + ((d.fields.length : Int) - d.nInSeq - 1) * 8 ≤ 0) by omega),
        if_neg (show ¬ (40 + ((d.fields.length : Int) - d.nInSeq - 1) * 8 < 0) by omega),
        if_neg (show ¬ (40 + ((d.fields.length : Int) - d.nInSeq - 1) * 8 = 0) by omega)]
      simp only [hs]
      rw [if_neg (show ¬ ((40 + ((d.fields.length : Int) - d.nInSeq - 1) * 8).toNat < 32) by omega)]
      simp only [CRes.bind_ok]
      cases initDict d d.fields.length (d.fields.count .unnamed) with
      | ok r =>
        obtain ⟨dict, ma⟩ := r
        exact ⟨rfl, fun _ _ => rfl⟩
      | exc e => exact ⟨rfl, fun _ h => by cases h⟩
      | nullNoExc => exact ⟨rfl, fun _ h => by cases h⟩
      | ub w => exact ⟨rfl, fun _ h => by cases h⟩
  · intro refcnt d malloc ready
    unfold initType
    cases initType2 refcnt d malloc ready with
    | mk r st =>
      cases r with
      | ok b => simp
      | exc e => simp
      | nullNoExc => simp
      | ub w => simp

/-! ## Where the twins differ -/

/-- Whether a call failed (returned `NULL` or -1) rather than built a type. -/
def CRes.failed {β : Type} : CRes β → Bool
  | .ok _ => false
  | _ => true

/-- `PyStructSequence_InitType2` and `PyStructSequence_NewType` agree on every desc, when the
steps neither model mirrors succeed. -/
def StaticTwinAll : Prop :=
  ∀ (d : Desc) (malloc : Nat → Bool), (initType2 0 d malloc .allOk).1 = newType d malloc (.ok ())

/-- One field, `n_in_sequence = 2`: `NewType`'s basicsize 24 is below tuple's and refused with
`TypeError`; `PyType_Ready` of the static type has no such check, so the `__match_args__` loop
reads the field array's terminator. -/
def descPlus1 : Desc := { name := lit "m.S", fields := [.named (lit "a")], nInSeq := 2 }

theorem staticTwinAll_refuted : ¬ StaticTwinAll := by
  intro h
  have := congrArg CRes.isUB (h descPlus1 (fun _ => true))
  revert this
  decide

/-- The twin on every valid desc (`0 ≤ n_in_sequence ≤ #fields`, fewer than `2^28 - 4` hidden
fields), field names unrestricted. -/
def StaticTwinValid : Prop :=
  ∀ (d : Desc) (malloc : Nat → Bool),
    0 ≤ d.nInSeq → d.nInSeq ≤ d.fields.length → (d.fields.length : Int) - d.nInSeq < 2 ^ 28 - 4 →
    (initType2 0 d malloc .allOk).1 = newType d malloc (.ok ())

/-- Fields `a` and `__dictoffset__`, both visible: `PyType_FromMetaclass` refuses the second
with `SystemError: type of __dictoffset__ must be Py_T_PYSSIZET`; `PyType_Ready` builds it. -/
def descDictoffset : Desc :=
  { name := lit "m.S", fields := [.named (lit "a"), .named (lit "__dictoffset__")], nInSeq := 2 }

theorem staticTwinValid_refuted : ¬ StaticTwinValid := by
  intro h
  have := congrArg CRes.failed (h descDictoffset (fun _ => true) (by decide) (by decide) (by decide))
  revert this
  decide

/-- After a failing `PyStructSequence_InitType2`, no member descriptor in the type's dict points
at a freed `tp_members` array. -/
def InitType2NoDangling : Prop :=
  ∀ (d : Desc) (malloc : Nat → Bool) (ready : ReadyRest),
    ¬ ((initType2 0 d malloc ready).2.descriptors = true ∧ (initType2 0 d malloc ready).2.membersFreed = true)

/-- One field, `n_in_sequence = 6`: `type_ready` has added the descriptor when its post check
refuses the negative basicsize; :699-701 frees the members, and the dict keeps the descriptor. -/
def descPlus5 : Desc := { name := lit "m.S", fields := [.named (lit "a")], nInSeq := 6 }

/-- One field, `n_in_sequence = -1`: `PyType_Ready` succeeds, `initialize_structseq_dict` fails
at `PyTuple_New(-1)`, and :699-701 frees the members of the now ready type. -/
def descNeg : Desc := { name := lit "m.S", fields := [.named (lit "a")], nInSeq := -1 }

theorem initType2NoDangling_refuted : ¬ InitType2NoDangling := by
  intro h
  exact h descPlus5 (fun _ => true) .allOk (by decide)

/-- The same through the dict failure, with the type left ready. -/
theorem initType2_dangling_ready :
    (initType2 0 descNeg (fun _ => true) .allOk).2 = ⟨true, true, true, true⟩ := by decide

end PyLean.TypeObj.StructSeq
