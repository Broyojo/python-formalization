import PyLean.TypeObj.PropsGetstate

/-!
The cases the review of `Objects/typeobject.c` (CPython 3.15.2) found unstated: `vectorcall_method`
with arguments after `self`, `find_best_base` with a layout conflict before a bad base, the slot
`object_richcompare` calls for `!=`, `same_slots_added` for non-heap types and types without
`__slots__`, `compatible_for_assignment` for `__bases__`, `__class__` assignment on a class, the
audit hooks of `object_set_class`, and one step of the slot loop of `object_getstate_default`.
-/

namespace PyLean.TypeObj

/-! ## `vectorcall_method`, `vectorcall_unbound` -/

/-- **`vectorcall_method`, every branch, for any arguments.** `Objects/typeobject.c:3156-3172`
with `vectorcall_unbound` (`:3086-3098`): the method is looked up on the type of `args[0]`
(`self`) by `lookup_method`; a missing one raises `AttributeError(name)`; an unbound method
descriptor is called with all of `args`, `self` first; anything else is bound by its `__get__`
(whose exception propagates) or taken as it is, and called with the arguments after `self`
(`args++`, `:3090-3095`), whatever their number: `__set__` passes two, `SLOT1` one. -/
def VectorcallMethodExact : Prop :=
  ∀ (rt : Rt) (name : Name) (self : Val) (rest : List Val) (w : World),
    (findInMro w (typeOf w self) name = none →
      vectorcallMethod rt name (self :: rest) w = (attrErr name : M Val) w) ∧
    (∀ f, findInMro w (typeOf w self) name = some f →
      (tdata w (typeOf w f)).methodDescriptor = true →
      vectorcallMethod rt name (self :: rest) w = rt.call f (self :: rest) [] w) ∧
    (∀ f, findInMro w (typeOf w self) name = some f →
      (tdata w (typeOf w f)).methodDescriptor = false →
      slotOf w (typeOf w f) .tp_descr_get = none →
      vectorcallMethod rt name (self :: rest) w = rt.call f rest [] w) ∧
    (∀ f g w', findInMro w (typeOf w self) name = some f →
      (tdata w (typeOf w f)).methodDescriptor = false →
      slotOf w (typeOf w f) .tp_descr_get = some g →
      (∀ v, callDescrGet rt g f (some self) (some (.obj (typeOf w self))) w = .ok v w' →
        vectorcallMethod rt name (self :: rest) w = rt.call v rest [] w') ∧
      (∀ e, callDescrGet rt g f (some self) (some (.obj (typeOf w self))) w = .err e w' →
        vectorcallMethod rt name (self :: rest) w = .err e w'))

theorem vectorcallMethodExact_proven : VectorcallMethodExact := by
  intro rt name self rest w
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; simp [vectorcallMethod, lookupMethodEx, h, attrErr, raiseC]
  · intro f h hm; simp [vectorcallMethod, lookupMethodEx, h, hm, callUnbound]
  · intro f h hm hg; simp [vectorcallMethod, lookupMethodEx, h, hm, hg, callUnbound]
  · intro f g w' h hm hg
    refine ⟨fun v hd => ?_, fun e hd => ?_⟩
    · simp [vectorcallMethod, lookupMethodEx, h, hm, hg, hd, callUnbound]
    · simp [vectorcallMethod, lookupMethodEx, h, hm, hg, hd]

/-! ## `find_best_base`: the first failure decides -/

/-- After a prefix of acceptable bases whose solid bases are pairwise related, the loop is at the
next base with the least solid base of the prefix as its winner. -/
theorem bestBase_prefix_min (w : World) (ho : SubtypeOrder w) (xs : List Val) :
    ∀ (pre : List Val) (win base : Addr), (∀ y ∈ pre, Acceptable w y) →
      (∀ y ∈ pre, ∀ z ∈ pre, Comparable w (solidOf w y) (solidOf w z)) →
      (∀ y ∈ pre, Comparable w win (solidOf w y)) →
      ∃ win' base', bestBaseLoop w (pre ++ xs) (some win) (some base) =
          bestBaseLoop w xs (some win') (some base') ∧
        isSubtype w win' win = true ∧ ∀ y ∈ pre, isSubtype w win' (solidOf w y) = true := by
  intro pre
  induction pre with
  | nil => intro win base _ _ _; exact ⟨win, base, rfl, ho.1 _, by simp⟩
  | cons y rest ih =>
    intro win base hacc hpair hcmp
    obtain ⟨bi, hy, hbt⟩ := hacc y List.mem_cons_self
    have hsy : solidOf w y = solidBase w bi := solidOf_of w y bi hy
    have hacc' := fun z hz => hacc z (List.mem_cons_of_mem y hz)
    have hpair' := fun a ha b hb => hpair a (List.mem_cons_of_mem y ha) b (List.mem_cons_of_mem y hb)
    simp only [List.cons_append, bestBaseLoop, hy, hbt, Bool.not_true, Bool.false_eq_true, ite_false]
    by_cases h1 : isSubtype w win (solidBase w bi) = true
    · simp only [h1, ite_true]
      obtain ⟨win', base', heq, hw, hall⟩ :=
        ih win base hacc' hpair' (fun z hz => hcmp z (List.mem_cons_of_mem y hz))
      refine ⟨win', base', heq, hw, ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · rw [hsy]; exact ho.2 _ _ _ hw h1
      · exact hall z hz
    · have h2 : isSubtype w (solidBase w bi) win = true := by
        rcases hcmp y List.mem_cons_self with h | h
        · rw [hsy] at h; exact absurd h h1
        · rw [hsy] at h; exact h
      simp only [h1, Bool.false_eq_true, ite_false, h2, ite_true]
      obtain ⟨win', base', heq, hw, hall⟩ := ih (solidBase w bi) bi hacc' hpair' (by
        intro z hz
        have := hpair y List.mem_cons_self z (List.mem_cons_of_mem y hz)
        rw [hsy] at this; exact this)
      refine ⟨win', base', heq, ho.2 _ _ _ hw h2, ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · rw [hsy]; exact hw
      · exact hall z hz

/-- **`find_best_base`: the first failing base decides, in base order.**
`Objects/typeobject.c:3747-3797`: the bases are checked one at a time, each is first required to
be a class, then to allow subclassing, then compared with the winner so far. So when the bases
before `x` are acceptable with pairwise related solid bases, `x` is the first failure if it is
one, and its error is the result whatever follows:
* `x` not a class: "bases must be types; got '%T'";
* `x` a class without `Py_TPFLAGS_BASETYPE`: "type '%.100s' is not an acceptable base type";
* `x` acceptable with a solid base unrelated to that of an earlier base: the lay-out conflict,
  before any later base is looked at (`type('C', (int, str, bool), {})` raises the conflict at
  `str`, not the `bool` error, on 3.15.2), when solid bases form a tree (`TreeOrder`, a type
  invariant of hierarchies built by `type_new`).
Together with `FindBestBaseExact` (the result when every base passes) this covers every list. -/
def FindBestBaseFirstFailure : Prop :=
  ∀ (w : World) (pre : List Val) (x : Val) (post : List Val), SubtypeOrder w →
    (∀ y ∈ pre, Acceptable w y) →
    (∀ y ∈ pre, ∀ z ∈ pre, Comparable w (solidOf w y) (solidOf w z)) →
    (asType w x = none →
      bestBaseLoop w (pre ++ x :: post) none none = .error s!"bases must be types; got '{objFQN w x}'") ∧
    (∀ t, asType w x = some t → (tdata w t).baseType = false →
      bestBaseLoop w (pre ++ x :: post) none none =
        .error s!"type '{trunc 100 (tpName w t)}' is not an acceptable base type") ∧
    (TreeOrder w → Acceptable w x → (∃ y ∈ pre, ¬ Comparable w (solidOf w y) (solidOf w x)) →
      bestBaseLoop w (pre ++ x :: post) none none = .error "multiple bases have instance lay-out conflict")

theorem findBestBaseFirstFailure_proven : FindBestBaseFirstFailure := by
  intro w pre x post ho hacc hpair
  refine ⟨fun hx => ?_, fun t hx hbt => ?_, fun htree hax ⟨y, hy, hyx⟩ => ?_⟩
  · have := (findBestBaseExact_proven w (pre ++ x :: post) ho).2.2.2 pre x post rfl hacc hpair
    exact this.1 hx
  · have := (findBestBaseExact_proven w (pre ++ x :: post) ho).2.2.2 pre x post rfl hacc hpair
    exact this.2 t hx hbt
  · cases pre with
    | nil => simp at hy
    | cons p rest =>
      obtain ⟨bp, hp, hbp⟩ := hacc p List.mem_cons_self
      have hsp : solidOf w p = solidBase w bp := solidOf_of w p bp hp
      have hacc' := fun z hz => hacc z (List.mem_cons_of_mem p hz)
      have hpair' := fun a ha b hb => hpair a (List.mem_cons_of_mem p ha) b (List.mem_cons_of_mem p hb)
      simp only [List.cons_append, bestBaseLoop, hp, hbp, Bool.not_true, Bool.false_eq_true, ite_false]
      obtain ⟨win, base, heq, hwin, hall⟩ := bestBase_prefix_min w ho (x :: post) rest
        (solidBase w bp) bp hacc' hpair' (by
          intro z hz
          have := hpair p List.mem_cons_self z (List.mem_cons_of_mem p hz)
          rw [hsp] at this; exact this)
      rw [heq]
      obtain ⟨bx, hx, hbx⟩ := hax
      have hsx : solidOf w x = solidBase w bx := solidOf_of w x bx hx
      have hminy : isSubtype w win (solidOf w y) = true := by
        rcases List.mem_cons.mp hy with rfl | hy'
        · rw [hsp]; exact hwin
        · exact hall y hy'
      have h1 : isSubtype w win (solidBase w bx) = false := by
        cases h : isSubtype w win (solidBase w bx) with
        | false => rfl
        | true =>
          rw [← hsx] at h
          exact absurd (htree _ _ _ hminy h) hyx
      have h2 : isSubtype w (solidBase w bx) win = false := by
        cases h : isSubtype w (solidBase w bx) win with
        | false => rfl
        | true =>
          rw [← hsx] at h
          exact absurd (Or.inr (ho.2 _ _ _ h hminy)) hyx
      simp [bestBaseLoop, hx, hbx, h1, h2]

/-! ## `object_richcompare` for `!=`: the slot of `type(self)` -/

/-- **`object.__ne__` asks the slot of the type of `self`.** `Objects/typeobject.c:7591-7611`, through
`callRichcompare` for the `tp_richcompare` that is `object_richcompare` (`_Py_BaseObject_RichCompare`,
`:7621-7624`, is the same function): `!=` reads `Py_TYPE(self)->tp_richcompare`; when it is NULL
the result is `NotImplemented`; otherwise it is called as `(self, other, Py_EQ)`, in that order, and
its result decides: `NotImplemented` passes through, an exception propagates, and any other value
is negated by its truth (`PyObject_IsTrue`, whose exception propagates). The slot of `type(other)`
is never consulted (`object.__ne__(F(), E())` is `NotImplemented` and runs no `E.__eq__` on 3.15.2).
`==` compares identity, and orderings are `NotImplemented`. -/
def ObjectNeSlotExact : Prop :=
  ∀ (rt : Rt) (self other : Val) (w : World),
    (∀ a b, self = .obj a → other = .obj b →
      callRichcompare rt (.c .object) self other .eq w = .ok (if a = b then .bool true else .notImpl) w) ∧
    (slotOf w (typeOf w self) .tp_richcompare = none →
      callRichcompare rt (.c .object) self other .ne w = .ok .notImpl w) ∧
    (∀ g, slotOf w (typeOf w self) .tp_richcompare = some g →
      (∀ w1, callRichcompareEq rt g self other .eq w = .ok .notImpl w1 →
        callRichcompare rt (.c .object) self other .ne w = .ok .notImpl w1) ∧
      (∀ e w1, callRichcompareEq rt g self other .eq w = .err e w1 →
        callRichcompare rt (.c .object) self other .ne w = .err e w1) ∧
      (∀ r w1, callRichcompareEq rt g self other .eq w = .ok r w1 → r.is .notImpl = false →
        (∀ b w2, rt.isTrue r w1 = .ok b w2 →
          callRichcompare rt (.c .object) self other .ne w = .ok (.bool (!b)) w2) ∧
        (∀ e w2, rt.isTrue r w1 = .err e w2 →
          callRichcompare rt (.c .object) self other .ne w = .err e w2))) ∧
    (∀ op, op ≠ .eq → op ≠ .ne → callRichcompare rt (.c .object) self other op w = .ok .notImpl w)

theorem objectNeSlotExact_proven : ObjectNeSlotExact := by
  intro rt self other w
  have base := fun eqSlot => objectRichcompareExact_proven rt eqSlot self other w
  refine ⟨fun a b ha hb => ?_, fun hn => ?_, fun g hg => ⟨fun w1 h => ?_, fun e w1 h => ?_,
    fun r w1 h hr => ⟨fun b w2 hb => ?_, fun e w2 he => ?_⟩⟩, fun op h1 h2 => ?_⟩
  · simp only [callRichcompare]; exact (base _).1 a b ha hb
  · simp only [callRichcompare]
    exact (base _).2.2.2.1 w (by simp [hn])
  · simp only [callRichcompare]
    exact (base _).2.2.2.1 w1 (by simp [hg, h])
  · simp only [callRichcompare]
    exact (base _).2.2.2.2.1 e w1 (by simp [hg, h])
  · simp only [callRichcompare]
    exact ((base _).2.2.2.2.2.1 r w1 (by simp [hg, h]) hr).1 b w2 hb
  · simp only [callRichcompare]
    exact ((base _).2.2.2.2.2.1 r w1 (by simp [hg, h]) hr).2 e w2 he
  · simp only [callRichcompare]
    exact (base _).2.2.2.2.2.2 op h1 h2

/-! ## `same_slots_added`: the other branches -/

/-- **`same_slots_added` when the slot check is skipped.** `Objects/typeobject.c:7643-7670`:
`size` starts at `tp_basicsize` of the common base and grows by a pointer for a `__dict__`, then
for a `__weakref__`, that both types add at that offset (`:7649-7655`); then
* either type not a heap type: `0` (`:7658-7661`), whatever the sizes;
* both heap types, either without `ht_slots`: the slot comparison is skipped (`:7662-7668`) and the
  answer is whether `size` is the `tp_basicsize` of both, so two types that add an unequal
  layout without `__slots__` still differ. -/
def SameSlotsAddedRest : Prop :=
  ∀ (rt : Rt) (a b base : Addr) (w : World),
    (tdata w a).base = some base →
    let size0 := (tdata w base).basicsize
    let size1 := if (tdata w a).dictoffset == size0 && (tdata w b).dictoffset == size0 then size0 + 8 else size0
    let size2 := if (tdata w a).weaklistoffset == size1 && (tdata w b).weaklistoffset == size1 then size1 + 8 else size1
    (((tdata w a).heap = false ∨ (tdata w b).heap = false) → sameSlotsAdded rt a b w = .ok false w) ∧
    ((tdata w a).heap = true → (tdata w b).heap = true →
      ((tdata w a).htSlots = none ∨ (tdata w b).htSlots = none) →
      sameSlotsAdded rt a b w =
        .ok (size2 == (tdata w a).basicsize && size2 == (tdata w b).basicsize) w)

theorem sameSlotsAddedRest_proven : SameSlotsAddedRest := by
  intro rt a b base w hb size0 size1 size2
  refine ⟨fun h => ?_, fun ha hb' hs => ?_⟩
  · rcases h with h | h <;> simp [sameSlotsAdded, hb, h]
  · rcases hs with h | h
    · simp [sameSlotsAdded, hb, ha, hb', h, size2, size1, size0]
    · cases hsa : (tdata w a).htSlots <;> simp [sameSlotsAdded, hb, ha, hb', h, hsa, size2, size1, size0]

/-! ## `compatible_for_assignment` for `__bases__` -/

/-- **`compatible_for_assignment` for `__bases__`, every branch.** `Objects/typeobject.c:7683-7750`
with `setclass = 0`, as `type_set_bases` calls it with the class `origto` and its new first base
`newto` (`:1960`): the old type compared is `origto->tp_base` (`:7688`); there is no deallocator
check (`:7690`); the layout flags of `newto` must be a subset of those of `origto`
(`compatible_flags`, `:7673-7681`), and `tp_dictoffset` and `tp_weaklistoffset` are compared only
where `newto` sets them (`:7708-7717`), else "'%s' object layout differs from '%s'"; then the
highest compatible bases of `newto` and the old base decide, as for `__class__`. -/
def CompatibleForAssignmentBases : Prop :=
  ∀ (rt : Rt) (origto newto : Addr) (w : World),
    let oldto := (tdata w origto).base.getD B.object
    let o := tdata w origto
    let n := tdata w newto
    let newbase := compatBase w w.heap.size newto
    let oldbase := compatBase w w.heap.size oldto
    let layoutErr : M Unit := typeErr s!"{("__bases__" : String)} assignment: '{tpName w newto}' object layout differs from '{tpName w oldto}'"
    ((!compatibleFlags false w origto newto ||
        (n.dictoffset != 0 && o.dictoffset != n.dictoffset) ||
        (n.weaklistoffset != 0 && o.weaklistoffset != n.weaklistoffset)) = true →
      compatibleForAssignment rt origto newto "__bases__" false w = layoutErr w) ∧
    ((!compatibleFlags false w origto newto ||
        (n.dictoffset != 0 && o.dictoffset != n.dictoffset) ||
        (n.weaklistoffset != 0 && o.weaklistoffset != n.weaklistoffset)) = false →
      (newbase = oldbase → compatibleForAssignment rt origto newto "__bases__" false w = .ok () w) ∧
      (newbase ≠ oldbase → (tdata w newbase).base ≠ (tdata w oldbase).base →
        compatibleForAssignment rt origto newto "__bases__" false w = layoutErr w) ∧
      (newbase ≠ oldbase → (tdata w newbase).base = (tdata w oldbase).base →
        (∀ w1, sameSlotsAdded rt newbase oldbase w = .ok true w1 →
          compatibleForAssignment rt origto newto "__bases__" false w = .ok () w1) ∧
        (∀ w1, sameSlotsAdded rt newbase oldbase w = .ok false w1 →
          compatibleForAssignment rt origto newto "__bases__" false w =
            (typeErr s!"{("__bases__" : String)} assignment: '{tpName w1 newto}' object layout differs from '{tpName w1 oldto}'" : M Unit) w1)))

theorem compatibleForAssignmentBases_proven : CompatibleForAssignmentBases := by
  intro rt origto newto w oldto o n newbase oldbase layoutErr
  refine ⟨fun hd => ?_, fun hd => ⟨fun he => ?_, fun hne hb => ?_,
    fun hne hb => ⟨fun w1 hs => ?_, fun w1 hs => ?_⟩⟩⟩
  all_goals
    simp only [compatibleForAssignment, M.bind_app, getW_app, Bool.false_and, Bool.false_eq_true,
      ite_false, M.pure_app, Bool.false_or]
    simp only [o, n] at hd
    simp only [hd, ite_true, Bool.false_eq_true, ite_false]
  · simp [layoutErr, oldto, typeErr, raiseC]
  · simp only [newbase, oldbase, oldto] at he
    simp [he]
  · simp only [newbase, oldbase, oldto] at hne hb
    have h1 : (compatBase w w.heap.size newto != compatBase w w.heap.size ((tdata w origto).base.getD B.object)) = true := by
      simpa using hne
    have h2 : ((tdata w (compatBase w w.heap.size newto)).base != (tdata w (compatBase w w.heap.size ((tdata w origto).base.getD B.object))).base) = true := by
      simpa using hb
    simp only [h1, h2, ite_true]
    simp [layoutErr, oldto, typeErr, raiseC]
  · simp only [newbase, oldbase, oldto] at hne hb hs
    have h1 : (compatBase w w.heap.size newto != compatBase w w.heap.size ((tdata w origto).base.getD B.object)) = true := by
      simpa using hne
    have h2 : ((tdata w (compatBase w w.heap.size newto)).base != (tdata w (compatBase w w.heap.size ((tdata w origto).base.getD B.object))).base) = false := by
      simpa using hb
    simp only [h1, h2, ite_true, Bool.false_eq_true, ite_false]
    simp only [M.bind_app, hs, Bool.not_true, Bool.false_eq_true, ite_false, M.pure_app]
  · simp only [newbase, oldbase, oldto] at hne hb hs
    have h1 : (compatBase w w.heap.size newto != compatBase w w.heap.size ((tdata w origto).base.getD B.object)) = true := by
      simpa using hne
    have h2 : ((tdata w (compatBase w w.heap.size newto)).base != (tdata w (compatBase w w.heap.size ((tdata w origto).base.getD B.object))).base) = false := by
      simpa using hb
    simp only [h1, h2, ite_true, Bool.false_eq_true, ite_false]
    simp only [M.bind_app, hs, Bool.not_false, ite_true, getW_app, oldto]

/-! ## `__class__` assignment on a class -/

/-- **`object_set_class_world_stopped` on a class.** `Objects/typeobject.c:7755-7853`: `self` may be
a class (`C.__class__ = MB` for two heap metaclasses succeeds on 3.15.2, and `type(C)` is then
`MB`); once the checks pass, its `ob_type` becomes the new metaclass and its type data, MRO and
dict included, is unchanged (`Py_SET_TYPE`, `:7843`). -/
def ObjectSetClassOnClass : Prop :=
  ∀ (rt : Rt) (a : Addr) (newto : Addr) (w : World),
    (!(isModuleSubtype w newto && isModuleSubtype w (typeOf w (.obj a))) &&
        ((tdata w newto).immutable || (tdata w (typeOf w (.obj a))).immutable)) = false →
    ∀ w1 c d, compatibleForAssignment rt (typeOf w (.obj a)) newto "__class__" true w = .ok () w1 →
      w1.get a = .ty c d →
      objectSetClassWorldStopped rt (.obj a) newto w = .ok () (w1.setCell a (.ty newto d))

theorem objectSetClassOnClass_proven : ObjectSetClassOnClass := by
  intro rt a newto w hc w1 c d he ho
  simp only [objectSetClassWorldStopped, M.bind_app, getW_app, hc, Bool.false_eq_true,
    ite_false, M.pure_app, he]
  simp [ho, modW]

/-! ## `object_set_class`: every check, every hook -/

/-- **`object_set_class`, every branch, for any number of audit hooks.**
`Objects/typeobject.c:7856-7894`:
* deleting raises "can't delete __class__ attribute" (`:7859-7863`);
* a value that is not a class raises "__class__ must be set to a class, not '%s' object"
  (`:7864-7869`); both before any hook runs;
* for a class, `PySys_Audit("object.__setattr__", "OsO", self, "__class__", value)` (`:7872`) runs
  every installed hook in order with that event, the first exception aborting the assignment
  before anything is checked or changed; then `object_set_class_world_stopped` decides. So with
  hooks that only observe, the assignment is decided by `object_set_class_world_stopped` whatever
  their number, and a hook that raises after any number of observing ones aborts it. -/
def ObjectSetClassAll : Prop :=
  ∀ (rt : Rt) (self : Val) (w : World),
    objectSetClass rt self none w = (typeErr "can't delete __class__ attribute" : M Unit) w ∧
    (∀ v, asType w v = none → objectSetClass rt self (some v) w =
      (typeErr s!"__class__ must be set to a class, not '{typeName w v}' object" : M Unit) w) ∧
    (∀ v newto, asType w v = some newto →
      let args := [Val.str "object.__setattr__", .tuple [self, .str "__class__", v]]
      objectSetClass rt self (some v) w =
        (do pySysAuditLoop rt "object.__setattr__" [self, .str "__class__", v] w.auditHooks
            objectSetClassWorldStopped rt self newto) w ∧
      ((∀ h ∈ w.auditHooks, ∃ r, rt.call h args [] w = .ok r w) →
        objectSetClass rt self (some v) w = objectSetClassWorldStopped rt self newto w) ∧
      (∀ pre h post e w1, w.auditHooks = pre ++ h :: post →
        (∀ g ∈ pre, ∃ r, rt.call g args [] w = .ok r w) →
        rt.call h args [] w = .err e w1 →
        objectSetClass rt self (some v) w = .err e w1))

theorem auditLoop_observing (rt : Rt) (ev : String) (args : List Val) (w : World) :
    ∀ hs : List Val, (∀ h ∈ hs, ∃ r, rt.call h [.str ev, .tuple args] [] w = .ok r w) →
      pySysAuditLoop rt ev args hs w = .ok () w := by
  intro hs
  induction hs with
  | nil => intro _; rfl
  | cons h hs ih =>
    intro hall
    obtain ⟨r, hr⟩ := hall h List.mem_cons_self
    simp only [pySysAuditLoop, M.bind_app, hr]
    exact ih (fun g hg => hall g (List.mem_cons_of_mem h hg))

theorem auditLoop_raises (rt : Rt) (ev : String) (args : List Val) (w : World) (h : Val)
    (post : List Val) (e : PyErr) (w1 : World)
    (hh : rt.call h [.str ev, .tuple args] [] w = .err e w1) :
    ∀ pre : List Val, (∀ g ∈ pre, ∃ r, rt.call g [.str ev, .tuple args] [] w = .ok r w) →
      pySysAuditLoop rt ev args (pre ++ h :: post) w = .err e w1 := by
  intro pre
  induction pre with
  | nil => intro _; simp [pySysAuditLoop, hh]
  | cons g gs ih =>
    intro hall
    obtain ⟨r, hr⟩ := hall g List.mem_cons_self
    simp only [List.cons_append, pySysAuditLoop, M.bind_app, hr]
    exact ih (fun x hx => hall x (List.mem_cons_of_mem g hx))

theorem objectSetClassAll_proven : ObjectSetClassAll := by
  intro rt self w
  refine ⟨by simp [objectSetClass], fun v hv => by simp [objectSetClass, hv], fun v newto hv => ?_⟩
  dsimp only
  have heq : objectSetClass rt self (some v) w =
      (do pySysAuditLoop rt "object.__setattr__" [self, .str "__class__", v] w.auditHooks
          objectSetClassWorldStopped rt self newto) w := by
    simp [objectSetClass, hv, pySysAudit]
  refine ⟨heq, fun hall => ?_, fun pre h post e w1 hhooks hpre hh => ?_⟩
  · rw [heq]
    simp only [M.bind_app, auditLoop_observing rt _ _ w w.auditHooks hall]
  · rw [heq]
    have := auditLoop_raises rt "object.__setattr__" [self, .str "__class__", v] w h post e w1 hh pre hpre
    rw [← hhooks] at this
    simp only [M.bind_app, this]

/-! ## One round of the slot loop of `object_getstate_default` -/

theorem dictSetAt_empty (rt : Rt) (a : Addr) (k v : Val) (hsh : Int) (w w1 : World) (o : Obj)
    (hh : rt.hash k w = .ok hsh w1) (ho : w1.get a = .val o) (hb : o.body = .dict []) :
    dictSetAt rt a k v w =
      .ok () (w1.setCell a (.val { o with body := .dict [(k, v)], keyHashes := (k, hsh) :: o.keyHashes })) := by
  have hd : dictEntries w1 a = [] := by
    simp [dictEntries, World.objAt, ho, hb]
  have hp : dictProbe rt a k hsh iterFuel 0 w1 = .ok none w1 := by
    rw [show iterFuel = 99999 + 1 from rfl, dictProbe]
    simp [hd]
  simp [dictSetAt, dictHashKey, hh, dictInsert, hp, modObj, ho, hb]

/-- **One round of the slot loop of `object_getstate_default`.** `Objects/typeobject.c:8046-8062`,
for the `i`-th name of `__slotnames__` (`PyList_GET_ITEM`, read again each round):
* a name that is not a `str` raises `PyObject_GetOptionalAttr`'s "attribute name must be string,
  not '%.200s'" (`Objects/object.c:1397-1402`);
* an exception from the attribute lookup propagates (`:8049-8052`);
* a missing attribute stores nothing and is not an error (`:8053-8056`);
* a found value is stored under the name object itself by `PyDict_SetItem` (`:8057-8061`); in the
  first round, into the empty dict, that makes the dict exactly `{name: value}` when hashing the
  name succeeds without side effects (an exact `str`). -/
def GetstateSlotStepExact : Prop :=
  ∀ (rt : Rt) (obj names : Val) (slots : Addr) (i : Nat) (w : World),
    let name := ((listOf w names).getD [])[i]?.getD .none
    (strOf w name = none →
      getstateSlotStep rt obj names slots i w =
        (typeErr s!"attribute name must be string, not '{trunc 200 (typeName w name)}'" : M Unit) w) ∧
    (∀ n, strOf w name = some n →
      (∀ e w1, rt.getOptionalAttr obj n w = .err e w1 → getstateSlotStep rt obj names slots i w = .err e w1) ∧
      (∀ w1, rt.getOptionalAttr obj n w = .ok none w1 → getstateSlotStep rt obj names slots i w = .ok () w1) ∧
      (∀ v w1, rt.getOptionalAttr obj n w = .ok (some v) w1 →
        getstateSlotStep rt obj names slots i w = dictSetAt rt slots name v w1 ∧
        (∀ hsh w2 o, rt.hash name w1 = .ok hsh w2 → w2.get slots = .val o → o.body = .dict [] →
          getstateSlotStep rt obj names slots i w =
            .ok () (w2.setCell slots
              (.val { o with body := .dict [(name, v)], keyHashes := (name, hsh) :: o.keyHashes })))))

theorem getstateSlotStepExact_proven : GetstateSlotStepExact := by
  intro rt obj names slots i w name
  refine ⟨fun h => ?_, fun n h => ⟨fun e w1 hg => ?_, fun w1 hg => ?_, fun v w1 hg => ?_⟩⟩
  · simp only [getstateSlotStep, M.bind_app, getW_app]
    simp only [name] at h ⊢
    simp [h, typeErr, raiseC]
  · simp only [name] at h
    simp [getstateSlotStep, h, hg]
  · simp only [name] at h
    simp [getstateSlotStep, h, hg]
  · simp only [name] at h
    have hs : getstateSlotStep rt obj names slots i w = dictSetAt rt slots name v w1 := by
      simp [getstateSlotStep, h, hg, name]
    exact ⟨hs, fun hsh w2 o hh ho hb => by rw [hs]; exact dictSetAt_empty rt slots name v hsh w1 w2 o hh ho hb⟩

/-! ## The rows, each with every branch -/

def FindBestBaseAll : Prop := FindBestBaseExact ∧ FindBestBaseFirstFailure
theorem findBestBaseAll_proven : FindBestBaseAll :=
  ⟨findBestBaseExact_proven, findBestBaseFirstFailure_proven⟩

def ObjectRichcompareAll : Prop := ObjectRichcompareExact ∧ ObjectNeSlotExact
theorem objectRichcompareAll_proven : ObjectRichcompareAll :=
  ⟨objectRichcompareExact_proven, objectNeSlotExact_proven⟩

def SameSlotsAddedAll : Prop := SameSlotsAddedExact ∧ SameSlotsAddedRest
theorem sameSlotsAddedAll_proven : SameSlotsAddedAll :=
  ⟨sameSlotsAddedExact_proven, sameSlotsAddedRest_proven⟩

def CompatibleForAssignmentAll : Prop := CompatibleForAssignmentExact ∧ CompatibleForAssignmentBases
theorem compatibleForAssignmentAll_proven : CompatibleForAssignmentAll :=
  ⟨compatibleForAssignmentExact_proven, compatibleForAssignmentBases_proven⟩

def ObjectSetClassWorldStoppedAll : Prop := ObjectSetClassWorldStoppedExact ∧ ObjectSetClassOnClass
theorem objectSetClassWorldStoppedAll_proven : ObjectSetClassWorldStoppedAll :=
  ⟨objectSetClassWorldStoppedExact_proven, objectSetClassOnClass_proven⟩

def GetstateDefaultAll : Prop := GetstateDefaultExact ∧ GetstateSlotStepExact ∧ GetstateSlotsGuard
theorem getstateDefaultAll_proven : GetstateDefaultAll :=
  ⟨getstateDefaultExact_proven, getstateSlotStepExact_proven, getstateSlotsGuard_proven⟩

end PyLean.TypeObj
