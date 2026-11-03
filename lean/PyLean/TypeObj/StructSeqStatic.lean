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
  immutable and immortal (:9719-9724), then runs `type_ready`. Of `type_ready`, the steps that
  depend on the struct sequence's layout are modelled: `inherit_special` turns a basicsize of 0
  into tuple's 32 (:8812-8813), and `type_ready_post_checks` refuses `tp_dictoffset +
  tp_basicsize <= 0` (:9571-9577). Unlike `PyType_FromSpecWithBases`, nothing compares the
  basicsize with tuple's. Every other step is `rest`, an arbitrary outcome (it includes creating
  the member descriptors, which decodes the member names).
* What the call leaves behind (`StaticState`): whether it made the type immortal and ready, and
  whether it freed the `tp_members` array the type points at. The type's flags beyond
  immutability (`Py_TPFLAGS_DEFAULT | Py_TPFLAGS_HAVE_GC`, :590) are not modelled.
-/

namespace PyLean.TypeObj.StructSeq

open PyLean PyLean.UnicodeObj

/-- What a call leaves in the type object. -/
structure StaticState where
  /-- `PyType_Ready` ran: the type is immutable and immortal, so its refcount is no longer 0. -/
  immortal : Bool
  /-- `Py_TPFLAGS_READY` is set. -/
  ready : Bool
  /-- The `tp_members` array the type and its member descriptors point at was freed. -/
  membersFreed : Bool
  deriving DecidableEq, Repr

/-- `type->tp_basicsize` as `initialize_static_fields` sets it (:581-582), in `Py_ssize_t`:
`sizeof(PyStructSequence) + (n_hidden - 1) * sizeof(PyObject *)`, with no `(int)` cast. -/
def staticBasicsize (nMembers : Nat) (nInSeq : Int) : Int := 40 + ((nMembers : Int) - nInSeq - 1) * 8

/-- `PyType_Ready` of the static type, as far as `tp_basicsize` goes. -/
def typeReadyStatic (name : Bytes) (basicsize : Int) (rest : Py Unit) : CRes Nat :=
  match rest with
  | .error e => .exc e
  | .ok () =>
    let bs := if basicsize = 0 then 32 else basicsize
    if bs ≤ 0 then
      .exc (systemError s!"~type {String.ofList (name.map Char.ofNat)} has a tp_dictoffset that is too small")
    else .ok bs.toNat

/-- `PyStructSequence_InitType2(type, desc)`, :672-704, with `initialize_static_fields`
(:573-593) and `initialize_static_type` (:595-611). `refcnt` is `Py_REFCNT(type)` on entry,
`malloc` the outcome of `PyMem_NEW` for `tp_members`, `ready` the rest of `PyType_Ready`.
When `PyType_Ready` or the dict fails, :699-701 frees `members`, which the type keeps pointing
at. -/
def initType2 (refcnt : Nat) (d : Desc) (malloc : Nat → Bool) (ready : Py Unit) :
    CRes Built × StaticState :=
  if refcnt ≠ 0 then
    (.exc (systemError "Objects/structseq.c:689: bad argument to internal function"), ⟨false, false, false⟩)
  else
    let (n, u) := countMembers d.fields
    match initializeMembers d.fields n u malloc with
    | .ok ms =>
      match typeReadyStatic d.name (staticBasicsize n d.nInSeq) ready with
      | .ok bs =>
        match initDict d n u with
        | .ok (dict, ma) =>
          (.ok { type := { name := d.name, members := ms, basicsize := bs, dict := dict }, matchArgs := ma },
            ⟨true, true, false⟩)
        | .exc e => (.exc e, ⟨true, true, true⟩)
        | .nullNoExc => (.nullNoExc, ⟨true, true, true⟩)
        | .ub w => (.ub w, ⟨true, true, true⟩)
      | .exc e => (.exc e, ⟨true, false, true⟩)
      | .nullNoExc => (.nullNoExc, ⟨true, false, true⟩)
      | .ub w => (.ub w, ⟨true, false, true⟩)
    | .exc e => (.exc e, ⟨false, false, false⟩)
    | .nullNoExc => (.nullNoExc, ⟨false, false, false⟩)
    | .ub w => (.ub w, ⟨false, false, false⟩)

/-- A `void` C call: it returns, possibly with an exception still set, or is undefined. -/
inductive VoidRes where
  | done
  | pending (e : PyExc)
  | ub (what : String)
  deriving DecidableEq, Repr

/-- `PyStructSequence_InitType(type, desc)`, :706-710: `(void)PyStructSequence_InitType2(...)`.
The caller cannot see a failure, and the exception stays set. -/
def initType (refcnt : Nat) (d : Desc) (malloc : Nat → Bool) (ready : Py Unit) : VoidRes × StaticState :=
  let (r, st) := initType2 refcnt d malloc ready
  (match r with
   | .ok _ => .done
   | .exc e => .pending e
   | .nullNoExc => .done
   | .ub w => .ub w, st)

/-! ## The twin property -/

/-- For every valid desc (`0 ≤ n_in_sequence ≤ #fields`, fewer than `2^28 - 4` hidden fields,
where the `(int)` cast of `NewType` does not wrap), every allocator and every outcome of the rest
of type creation, `PyStructSequence_InitType2` on a fresh type gives exactly what
`PyStructSequence_NewType` gives (the same exception, or a type with the same name,
`tp_members`, `tp_basicsize`, size attributes and `__match_args__`), and on success it leaves the
type ready with its members; `PyStructSequence_InitType` then leaves no exception set, and on a
failure it returns with that exception still set. A type whose refcount is not 0 is refused
with `SystemError`. -/
def StaticTwin : Prop :=
  (∀ (refcnt : Nat) (d : Desc) (malloc : Nat → Bool) (ready : Py Unit), refcnt ≠ 0 →
    (initType2 refcnt d malloc ready).1 =
      .exc (systemError "Objects/structseq.c:689: bad argument to internal function")) ∧
  (∀ (d : Desc) (malloc : Nat → Bool) (rest : Py Unit),
    0 ≤ d.nInSeq → d.nInSeq ≤ d.fields.length → (d.fields.length : Int) - d.nInSeq < 2 ^ 28 - 4 →
    (initType2 0 d malloc rest).1 = newType d malloc rest ∧
    (∀ b, (initType2 0 d malloc rest).1 = .ok b → (initType2 0 d malloc rest).2 = ⟨true, true, false⟩)) ∧
  (∀ (refcnt : Nat) (d : Desc) (malloc : Nat → Bool) (ready : Py Unit),
    ((initType refcnt d malloc ready).1 = .done ↔
      ((∃ b, (initType2 refcnt d malloc ready).1 = .ok b) ∨ (initType2 refcnt d malloc ready).1 = .nullNoExc)) ∧
    ∀ e, (initType refcnt d malloc ready).1 = .pending e ↔ (initType2 refcnt d malloc ready).1 = .exc e)

theorem staticTwin_proven : StaticTwin := by
  refine ⟨fun refcnt d malloc ready h => by simp [initType2, h], fun d malloc rest h0 h1 h2 => ?_, ?_⟩
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
      cases rest with
      | error e => simp
      | ok u =>
        cases u
        simp only
        rw [if_neg (show ¬ (40 + ((d.fields.length : Int) - d.nInSeq - 1) * 8 = 0) by omega),
          if_neg (show ¬ (40 + ((d.fields.length : Int) - d.nInSeq - 1) * 8 ≤ 0) by omega),
          if_neg (show ¬ (40 + ((d.fields.length : Int) - d.nInSeq - 1) * 8 < 0) by omega),
          if_neg (show ¬ (40 + ((d.fields.length : Int) - d.nInSeq - 1) * 8 = 0) by omega),
          if_neg (show ¬ ((40 + ((d.fields.length : Int) - d.nInSeq - 1) * 8).toNat < 32) by omega)]
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

/-- `PyStructSequence_InitType2` and `PyStructSequence_NewType` agree on every desc. -/
def StaticTwinAll : Prop :=
  ∀ (d : Desc) (malloc : Nat → Bool) (rest : Py Unit), (initType2 0 d malloc rest).1 = newType d malloc rest

/-- One field, `n_in_sequence = 2`: `NewType`'s basicsize 24 is below tuple's and refused with
`TypeError`; `PyType_Ready` of the static type has no such check, so the `__match_args__` loop
reads the field array's terminator. -/
def descPlus1 : Desc := { name := lit "m.S", fields := [.named (lit "a")], nInSeq := 2 }

theorem staticTwinAll_refuted : ¬ StaticTwinAll := by
  intro h
  have := congrArg CRes.isUB (h descPlus1 (fun _ => true) (.ok ()))
  revert this
  decide

/-- After a failing `PyStructSequence_InitType2`, the type is not left ready while pointing at a
freed `tp_members` array. -/
def InitType2NoDangling : Prop :=
  ∀ (d : Desc) (malloc : Nat → Bool) (ready : Py Unit),
    ¬ ((initType2 0 d malloc ready).2.ready = true ∧ (initType2 0 d malloc ready).2.membersFreed = true)

/-- One field, `n_in_sequence = -1`: `PyType_Ready` succeeds, `initialize_structseq_dict` fails
at `PyTuple_New(-1)`, and :699-701 frees the members of the now ready type. -/
def descNeg : Desc := { name := lit "m.S", fields := [.named (lit "a")], nInSeq := -1 }

theorem initType2NoDangling_refuted : ¬ InitType2NoDangling := by
  intro h
  exact h descNeg (fun _ => true) (.ok ()) (by decide)

end PyLean.TypeObj.StructSeq
