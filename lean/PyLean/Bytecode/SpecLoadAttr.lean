import PyLean.Bytecode.SpecCallGeneric

/-!
The attribute specializations of `Python/bytecodes.c` whose guards the machine has the state for:
`LOAD_ATTR_SLOT` (`:2999-3023`), `LOAD_ATTR_MODULE` (`:2918-2948`), `LOAD_ATTR_CLASS` and
`LOAD_ATTR_CLASS_WITH_METACLASS_CHECK` (`:3025-3054`), and `STORE_ATTR_SLOT` (`:3193-3212`), for
every object model.

Each is stated in the pattern of `SpecFast.lean`: on a state every guard accepts, the form does its
own body (which slot or cached object it reads, what it pushes, the `NULL` of
`_PUSH_NULL_CONDITIONAL` for the method form); on a state a guard rejects it is the generic
`LOAD_ATTR` (`STORE_ATTR`) on the same state, which is how `withDeopt` reads `DEOPT_IF`/`EXIT_IF`.
A guard dropped, a guard on the wrong version or cache word, or a body reading the wrong slot fails
one clause. `Py_TYPE(owner)->tp_version_tag` is the machine's `typeVersionOf`.
-/

namespace PyLean.Bytecode

open Uop

theorem guard_type_version (e : Env) (regs : Regs) (o : Val) (rest : List Val) (ver : Nat)
    (h : typeVersionOf o regs = .ok ver regs) :
    _GUARD_TYPE_VERSION e ⟨regs, o :: rest⟩ =
      if (ver != cacheNat e 0) = true then .error .deopt ⟨regs, o :: rest⟩ else .ok () ⟨regs, o :: rest⟩ := by
  refine guardTop_one regs rest _ o (ver != cacheNat e 0) ?_
  simp [bind, EStateM.bind, h, pure, EStateM.pure]

theorem pushNull_eval (e : Env) (regs : Regs) (stack : List Val) :
    _PUSH_NULL_CONDITIONAL e ⟨regs, stack⟩ = .ok () ⟨regs, List.replicate (e.oparg &&& 1) .null ++ stack⟩ := by
  simp [_PUSH_NULL_CONDITIONAL, stk, popN, bind, EStateM.bind, BM.lift, pure, EStateM.pure, pushAll,
    List.reverse_replicate]

/-! ## `LOAD_ATTR_SLOT` -/

/-- `LOAD_ATTR_SLOT` (`:3016-3023`: `_GUARD_TYPE_VERSION + _LOAD_ATTR_SLOT + POP_TOP +
_PUSH_NULL_CONDITIONAL`), cache `[type_version, index]`. When the owner's type has the cached
version and the owner is an instance whose slot `index` holds `v`, `v` replaces the owner (with a
`NULL` above it for the method form); a slot still `NULL` (`EXIT_IF(attr_o == NULL)`, `:3004`), or
any other version, is the generic `LOAD_ATTR`. -/
def LoadAttrSlotRules : Prop := ∀ (e : Env) (regs : Regs) (o : Val) (rest : List Val) (ver : Nat),
  typeVersionOf o regs = .ok ver regs →
  (ver ≠ cacheNat e 0 → execOp e .LOAD_ATTR_SLOT ⟨regs, o :: rest⟩ = execOp e .LOAD_ATTR ⟨regs, o :: rest⟩) ∧
  (ver = cacheNat e 0 → ∀ a i, o = .ref a → regs.rt.heap[a]? = some (.inst i) →
    (∀ v, i.slots[cacheNat e 1]? = some v → v ≠ .null →
      execOp e .LOAD_ATTR_SLOT ⟨regs, o :: rest⟩ = .ok () ⟨regs, List.replicate (e.oparg &&& 1) .null ++ v :: rest⟩) ∧
    (i.slots[cacheNat e 1]? = some .null ∨ i.slots[cacheNat e 1]? = none →
      execOp e .LOAD_ATTR_SLOT ⟨regs, o :: rest⟩ = execOp e .LOAD_ATTR ⟨regs, o :: rest⟩))

theorem loadAttrSlotRules_proven : LoadAttrSlotRules := by
  intro e regs o rest ver hv
  have hg := guard_type_version e regs o rest ver hv
  refine ⟨fun hne => ?_, fun heq a i hoa hi => ⟨fun v hs hn => ?_, fun hs => ?_⟩⟩
  · have hb : (ver != cacheNat e 0) = true := by simpa using hne
    rw [hb] at hg
    simp only [execOp]
    refine withDeopt_of (s' := ⟨regs, o :: rest⟩) ?_
    simp only [LOAD_ATTR_SLOT, bind, EStateM.bind, hg]
    simp
  · have hb : (ver != cacheNat e 0) = false := by simpa using heq
    rw [hb] at hg
    subst hoa
    simp only [execOp]
    apply withDeopt_ok
    simp only [LOAD_ATTR_SLOT, bind, EStateM.bind, hg, ↓Bool.false_eq_true, ↓reduceIte]
    have hb2 : (v == .null) = false := by simpa using hn
    simp [_LOAD_ATTR_SLOT, stk, popN, bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift,
      MonadLift.monadLift, instOf, getObj, hi, hs, hb2, pure, EStateM.pure, pushAll, pushNull_eval]
  · have hb : (ver != cacheNat e 0) = false := by simpa using heq
    rw [hb] at hg
    subst hoa
    simp only [execOp]
    refine withDeopt_of (s' := ⟨regs, rest⟩) ?_
    simp only [LOAD_ATTR_SLOT, bind, EStateM.bind, hg, ↓Bool.false_eq_true, ↓reduceIte]
    rcases hs with hs | hs <;>
    simp [_LOAD_ATTR_SLOT, stk, popN, bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift,
      MonadLift.monadLift, instOf, getObj, hi, hs, pure, EStateM.pure, throw, throwThe, MonadExcept.throw,
      EStateM.throw, MonadExceptOf.throw]

/-! ## `LOAD_ATTR_MODULE` -/

/-- `LOAD_ATTR_MODULE` (`:2943-2948`: `_LOAD_ATTR_MODULE + POP_TOP + _PUSH_NULL_CONDITIONAL`), cache
`[dict_version, index]`. On a module whose `md_dict` has the cached keys version and a non-`NULL`
value `v` at entry `index`, `v` replaces the owner (with a `NULL` above it for the method form);
anything but a module (`EXIT_IF(tp_getattro != PyModule_Type.tp_getattro)`, `:2920`), another
keys version (`:2924`), or a `NULL` value or missing entry (`:2929`) is the generic `LOAD_ATTR`. No
type version is checked. -/
def LoadAttrModuleRules : Prop := ∀ (e : Env) (regs : Regs) (o : Val) (rest : List Val),
  ((¬ ∃ a nm d, o = .ref a ∧ regs.rt.heap[a]? = some (.module nm d)) → Live regs.rt o →
    execOp e .LOAD_ATTR_MODULE ⟨regs, o :: rest⟩ = execOp e .LOAD_ATTR ⟨regs, o :: rest⟩) ∧
  (∀ a nm d dd, o = .ref a → regs.rt.heap[a]? = some (.module nm d) → regs.rt.heap[d]? = some (.dict dd) →
    (dd.version ≠ cacheNat e 0 →
      execOp e .LOAD_ATTR_MODULE ⟨regs, o :: rest⟩ = execOp e .LOAD_ATTR ⟨regs, o :: rest⟩) ∧
    (dd.version = cacheNat e 0 →
      (∀ en, dd.entries[cacheNat e 1]? = some en → en.value ≠ .null →
        execOp e .LOAD_ATTR_MODULE ⟨regs, o :: rest⟩ =
          .ok () ⟨regs, List.replicate (e.oparg &&& 1) .null ++ en.value :: rest⟩) ∧
      ((∀ en, dd.entries[cacheNat e 1]? = some en → en.value = .null) →
        execOp e .LOAD_ATTR_MODULE ⟨regs, o :: rest⟩ = execOp e .LOAD_ATTR ⟨regs, o :: rest⟩)))

theorem loadAttrModuleRules_proven : LoadAttrModuleRules := by
  intro e regs o rest
  refine ⟨fun hn hl => ?_, fun a nm d dd hoa ha hd =>
    ⟨fun hne => ?_, fun heq => ⟨fun en hen hnn => ?_, fun hnull => ?_⟩⟩⟩
  · simp only [execOp]
    refine withDeopt_of (s' := ⟨regs, rest⟩) ?_
    cases o with
    | ref a =>
      obtain ⟨ob, hob⟩ := live_obj hl
      cases ob with
      | module nm d => exact absurd ⟨a, nm, d, rfl, hob⟩ hn
      | _ => simp [LOAD_ATTR_MODULE, _LOAD_ATTR_MODULE, stk, popN, bind, EStateM.bind, BM.lift, RM.lift, liftM,
          monadLift, MonadLift.monadLift, getObj, hob, throw, throwThe, MonadExcept.throw, EStateM.throw,
          MonadExceptOf.throw]
    | _ => simp [LOAD_ATTR_MODULE, _LOAD_ATTR_MODULE, stk, popN, bind, EStateM.bind, BM.lift, throw, throwThe,
        MonadExcept.throw, EStateM.throw, MonadExceptOf.throw]
  · subst hoa
    simp only [execOp]
    refine withDeopt_of (s' := ⟨regs, rest⟩) ?_
    have hb : (dd.version != cacheNat e 0) = true := by simpa using hne
    simp [LOAD_ATTR_MODULE, _LOAD_ATTR_MODULE, stk, popN, bind, EStateM.bind, BM.lift, RM.lift, liftM,
      monadLift, MonadLift.monadLift, getObj, ha, hd, dictSlot, deoptIf, isExactDict, getDict, hb, pure,
      EStateM.pure, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw]
  · subst hoa
    simp only [execOp]
    apply withDeopt_ok
    have hb : (dd.version != cacheNat e 0) = false := by simpa using heq
    have hb2 : (en.value == .null) = false := by simpa using hnn
    simp [LOAD_ATTR_MODULE, _LOAD_ATTR_MODULE, stk, popN, bind, EStateM.bind, BM.lift, RM.lift, liftM,
      monadLift, MonadLift.monadLift, getObj, ha, hd, dictSlot, deoptIf, isExactDict, getDict, hb, hen, hb2,
      pure, EStateM.pure, pushAll, pushNull_eval]
  · subst hoa
    simp only [execOp]
    refine withDeopt_of (s' := ⟨regs, rest⟩) ?_
    have hb : (dd.version != cacheNat e 0) = false := by simpa using heq
    cases hen : dd.entries[cacheNat e 1]? with
    | none =>
      simp [LOAD_ATTR_MODULE, _LOAD_ATTR_MODULE, stk, popN, bind, EStateM.bind, BM.lift, RM.lift, liftM,
        monadLift, MonadLift.monadLift, getObj, ha, hd, dictSlot, deoptIf, isExactDict, getDict, hb, hen,
        pure, EStateM.pure, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw]
    | some en =>
      have hv := hnull en hen
      simp [LOAD_ATTR_MODULE, _LOAD_ATTR_MODULE, stk, popN, bind, EStateM.bind, BM.lift, RM.lift, liftM,
        monadLift, MonadLift.monadLift, getObj, ha, hd, dictSlot, deoptIf, isExactDict, getDict, hb, hen, hv,
        pure, EStateM.pure, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw]

/-! ## `LOAD_ATTR_CLASS`, `LOAD_ATTR_CLASS_WITH_METACLASS_CHECK` -/

/-- What `_CHECK_ATTR_CLASS` accepts: a class object whose own `tp_version_tag` is `ver`. -/
def ClassHit (rt : Rt) (o : Val) (ver : Nat) : Prop :=
  ∃ a c, o = .ref a ∧ rt.heap[a]? = some (.cls c) ∧ c.version = ver

/-- `LOAD_ATTR_CLASS` (`:3040-3046`: `_CHECK_ATTR_CLASS + _LOAD_ATTR_CLASS + _PUSH_NULL_CONDITIONAL`),
cache `[type_version, descr]`: on a class object whose own `tp_version_tag` is the cached one, the
cached object replaces it (with a `NULL` above for the method form); anything else
(`EXIT_IF(!PyType_Check(owner))`, another version, `:3025-3031`) is the generic `LOAD_ATTR`.
`LOAD_ATTR_CLASS_WITH_METACLASS_CHECK` (`:3048-3054`), cache `[metaclass version, class version,
descr]`, first asks `_GUARD_TYPE_VERSION` of the owner's type (the metaclass) and then the same of
the class itself: each mismatch is the generic `LOAD_ATTR`. -/
def LoadAttrClassRules : Prop := ∀ (e : Env) (regs : Regs) (o : Val) (rest : List Val), Live regs.rt o →
  (ClassHit regs.rt o (cacheNat e 0) →
      execOp e .LOAD_ATTR_CLASS ⟨regs, o :: rest⟩ =
        .ok () ⟨regs, List.replicate (e.oparg &&& 1) .null ++ (e.cache[1]?).getD .null :: rest⟩) ∧
  (¬ ClassHit regs.rt o (cacheNat e 0) →
      execOp e .LOAD_ATTR_CLASS ⟨regs, o :: rest⟩ = execOp e .LOAD_ATTR ⟨regs, o :: rest⟩) ∧
  (∀ ver, typeVersionOf o regs = .ok ver regs →
    (ver ≠ cacheNat e 0 → execOp e .LOAD_ATTR_CLASS_WITH_METACLASS_CHECK ⟨regs, o :: rest⟩ =
      execOp e .LOAD_ATTR ⟨regs, o :: rest⟩) ∧
    (ver = cacheNat e 0 → ClassHit regs.rt o (cacheNat e 1) →
        execOp e .LOAD_ATTR_CLASS_WITH_METACLASS_CHECK ⟨regs, o :: rest⟩ =
          .ok () ⟨regs, List.replicate (e.oparg &&& 1) .null ++ (e.cache[2]?).getD .null :: rest⟩) ∧
    (ver = cacheNat e 0 → ¬ ClassHit regs.rt o (cacheNat e 1) →
        execOp e .LOAD_ATTR_CLASS_WITH_METACLASS_CHECK ⟨regs, o :: rest⟩ = execOp e .LOAD_ATTR ⟨regs, o :: rest⟩))

theorem checkAttrClass_eval (e : Env) (regs : Regs) (o : Val) (rest : List Val) (i : Nat) (hl : Live regs.rt o) :
    ∃ b, checkAttrClassAt e i ⟨regs, o :: rest⟩ =
      (if b then .error .deopt ⟨regs, o :: rest⟩ else .ok () ⟨regs, o :: rest⟩) ∧
      (b = false ↔ ClassHit regs.rt o (cacheNat e i)) := by
  unfold checkAttrClassAt
  cases o with
  | ref a =>
    obtain ⟨ob, hob⟩ := live_obj hl
    cases ob with
    | cls c =>
      refine ⟨c.version != cacheNat e i, guardTop_one regs rest _ (.ref a) _ ?_, ?_⟩
      · simp [classVersion, getObj, hob, bind, EStateM.bind, pure, EStateM.pure, RM.lift, liftM, monadLift,
          MonadLift.monadLift]
      · simp [ClassHit, hob]
    | _ =>
      refine ⟨true, guardTop_one regs rest _ (.ref a) _ ?_, ?_⟩
      · simp [classVersion, getObj, hob, bind, EStateM.bind, pure, EStateM.pure, RM.lift, liftM, monadLift,
          MonadLift.monadLift]
      · simp [ClassHit, hob]
  | _ =>
    refine ⟨true, guardTop_one regs rest _ _ _ ?_, ?_⟩
    · simp [classVersion, bind, EStateM.bind, pure, EStateM.pure, RM.lift, liftM, monadLift, MonadLift.monadLift]
    · simp [ClassHit]

theorem loadAttrClassAt_eval (e : Env) (regs : Regs) (o : Val) (rest : List Val) (i : Nat) :
    loadAttrClassAt e i ⟨regs, o :: rest⟩ = .ok () ⟨regs, (e.cache[i]?).getD .null :: rest⟩ := by
  simp [loadAttrClassAt, stk, popN, bind, EStateM.bind, BM.lift, pure, EStateM.pure, pushAll]

theorem loadAttrClassRules_proven : LoadAttrClassRules := by
  intro e regs o rest hl
  obtain ⟨b0, hc0, hb0⟩ := checkAttrClass_eval e regs o rest 0 hl
  obtain ⟨b1, hc1, hb1⟩ := checkAttrClass_eval e regs o rest 1 hl
  refine ⟨fun hy => ?_, fun hn => ?_, fun ver hver => ⟨fun hne => ?_, fun heq hy => ?_, fun heq hn => ?_⟩⟩
  · have : b0 = false := hb0.2 hy
    subst this
    simp only [execOp]
    apply withDeopt_ok
    simp only [LOAD_ATTR_CLASS, _CHECK_ATTR_CLASS, _LOAD_ATTR_CLASS, bind, EStateM.bind, hc0,
      ↓Bool.false_eq_true, ↓reduceIte, loadAttrClassAt_eval, pushNull_eval]
  · have : b0 = true := by cases b0 <;> simp_all
    subst this
    simp only [execOp]
    refine withDeopt_of (s' := ⟨regs, o :: rest⟩) ?_
    simp only [LOAD_ATTR_CLASS, _CHECK_ATTR_CLASS, bind, EStateM.bind, hc0, ↓reduceIte]
  · have hg := guard_type_version e regs o rest ver hver
    have hb : (ver != cacheNat e 0) = true := by simpa using hne
    rw [hb] at hg
    simp only [execOp]
    refine withDeopt_of (s' := ⟨regs, o :: rest⟩) ?_
    simp only [LOAD_ATTR_CLASS_WITH_METACLASS_CHECK, bind, EStateM.bind, hg]
    simp
  · have hg := guard_type_version e regs o rest ver hver
    have hb : (ver != cacheNat e 0) = false := by simpa using heq
    rw [hb] at hg
    have : b1 = false := hb1.2 hy
    subst this
    simp only [execOp]
    apply withDeopt_ok
    simp only [LOAD_ATTR_CLASS_WITH_METACLASS_CHECK, bind, EStateM.bind, hg, ↓Bool.false_eq_true, ↓reduceIte,
      hc1, loadAttrClassAt_eval, pushNull_eval]
  · have hg := guard_type_version e regs o rest ver hver
    have hb : (ver != cacheNat e 0) = false := by simpa using heq
    rw [hb] at hg
    have : b1 = true := by cases b1 <;> simp_all
    subst this
    simp only [execOp]
    refine withDeopt_of (s' := ⟨regs, o :: rest⟩) ?_
    simp only [LOAD_ATTR_CLASS_WITH_METACLASS_CHECK, bind, EStateM.bind, hg, ↓Bool.false_eq_true, ↓reduceIte, hc1]

/-! ## `STORE_ATTR_SLOT` -/

/-- The runtime with `value` in slot `idx` of the instance at `a`. -/
def slotStored (rt : Rt) (a : Addr) (i : InstObj) (idx : Nat) (v : Val) : Rt :=
  { rt with heap := rt.heap.setIfInBounds a (.inst { i with slots := i.slots.setIfInBounds idx v }) }

/-- `STORE_ATTR_SLOT` (`:3207-3212`: `_GUARD_TYPE_VERSION + _STORE_ATTR_SLOT + POP_TOP`) on
`(value, owner)`, cache `[type_version, index]`: when the owner's type has the cached version and
the owner is an instance, `value` goes into its slot `index` and both operands are popped;
another version is the generic `STORE_ATTR`. -/
def StoreAttrSlotRules : Prop := ∀ (e : Env) (regs : Regs) (o v : Val) (rest : List Val) (ver : Nat),
  typeVersionOf o regs = .ok ver regs →
  (ver ≠ cacheNat e 0 →
    execOp e .STORE_ATTR_SLOT ⟨regs, o :: v :: rest⟩ = execOp e .STORE_ATTR ⟨regs, o :: v :: rest⟩) ∧
  (ver = cacheNat e 0 → ∀ a i, o = .ref a → regs.rt.heap[a]? = some (.inst i) →
    execOp e .STORE_ATTR_SLOT ⟨regs, o :: v :: rest⟩ = .ok () ⟨{ regs with rt := slotStored regs.rt a i (cacheNat e 1) v }, rest⟩)

theorem storeAttrSlotRules_proven : StoreAttrSlotRules := by
  intro e regs o v rest ver hv
  have hg := guard_type_version e regs o (v :: rest) ver hv
  refine ⟨fun hne => ?_, fun heq a i hoa hi => ?_⟩
  · have hb : (ver != cacheNat e 0) = true := by simpa using hne
    rw [hb] at hg
    simp only [execOp]
    refine withDeopt_of (s' := ⟨regs, o :: v :: rest⟩) ?_
    simp only [STORE_ATTR_SLOT, bind, EStateM.bind, hg]
    simp
  · have hb : (ver != cacheNat e 0) = false := by simpa using heq
    rw [hb] at hg
    subst hoa
    simp only [execOp]
    apply withDeopt_ok
    simp only [STORE_ATTR_SLOT, bind, EStateM.bind, hg, ↓Bool.false_eq_true, ↓reduceIte]
    simp [_STORE_ATTR_SLOT, stk, popN, bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift,
      MonadLift.monadLift, getObj, hi, setObj, slotStored, pure, EStateM.pure, pushAll]

def AttrSpecRules : Prop := LoadAttrSlotRules ∧ LoadAttrModuleRules ∧ LoadAttrClassRules ∧ StoreAttrSlotRules
theorem attrSpecRules_proven : AttrSpecRules :=
  ⟨loadAttrSlotRules_proven, loadAttrModuleRules_proven, loadAttrClassRules_proven, storeAttrSlotRules_proven⟩

end PyLean.Bytecode
