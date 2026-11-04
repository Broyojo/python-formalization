import PyLean.Bytecode.SpecUnpack

/-!
The container builders and updaters of `Python/bytecodes.c`: `SET_ADD` (`:1380-1392`),
`LIST_EXTEND` (`:2511-2533`), `SET_UPDATE` (`:2535-2545`), `DICT_UPDATE` (`:2610-2636`),
`DICT_MERGE` (`:2638-2654`) and `MAP_ADD` (`:2656-2666`), for every object model.

The container is `oparg` values below the top (`unused[oparg-1]` between them), so each statement
takes the stack as `top :: mid ++ [container] ++ below` with `mid.length + 1 = oparg`. What is pinned:
which slot is called on which operands; what is popped on success; that the four `ERROR_NO_POP` ops
keep every operand on failure while `SET_ADD` and `MAP_ADD` pop them (`ERROR_IF`); and the
rewriting of the error, with its message, in the cases the C rewrites it (`DICT_MERGE`'s duplicate
keyword and its `**` refusal, `DICT_UPDATE`'s "not a mapping", `LIST_EXTEND`'s "Value after *", and
`SET_ADD`'s 3.15 exact-set check).
-/

namespace PyLean.Bytecode

open Uop

theorem split_take_drop (L below : List Val) (p : Nat) (hL : L.length = p) :
    p ≤ (L ++ below).length ∧ (L ++ below).take p = L ∧ (L ++ below).drop p = below := by
  subst hL; simp

theorem stk_split_ok {p q : Nat} {f : List Val → BM (List Val)} {regs r : Regs} {L below outs : List Val}
    (hL : L.length = p) (hf : f L.reverse regs = .ok outs r) (hq : outs.length = q) :
    stk p q f ⟨regs, L ++ below⟩ = .ok () ⟨r, outs.reverse ++ below⟩ := by
  subst hL; subst hq
  simp [stk, popN, bind, EStateM.bind, BM.lift, hf, pushAll, pure, EStateM.pure]

theorem stk_split_err {p q : Nat} {f : List Val → BM (List Val)} {regs r : Regs} {L below : List Val} {x : Err}
    (hL : L.length = p) (hf : f L.reverse regs = .error x r) :
    stk p q f ⟨regs, L ++ below⟩ = .error x ⟨r, below⟩ := by
  subst hL
  simp [stk, popN, bind, EStateM.bind, BM.lift, hf]

theorem stkK_split_ok {p q : Nat} {f : List Val → BM (List Val)} {regs r : Regs} {L below outs : List Val}
    (hL : L.length = p) (hf : f L.reverse regs = .ok outs r) (hq : outs.length = q) :
    stkK p q f ⟨regs, L ++ below⟩ = .ok () ⟨r, outs.reverse ++ below⟩ := by
  subst hL; subst hq
  simp [stkK, peekN, popN, bind, EStateM.bind, BM.lift, hf, pushAll, pure, EStateM.pure]

theorem stkK_split_err {p q : Nat} {f : List Val → BM (List Val)} {regs r : Regs} {L below : List Val} {x : Err}
    (hL : L.length = p) (hf : f L.reverse regs = .error x r) :
    stkK p q f ⟨regs, L ++ below⟩ = .error x ⟨r, L ++ below⟩ := by
  subst hL
  simp [stkK, peekN, bind, EStateM.bind, BM.lift, hf]

theorem dropLast_cons_snoc (a : Val) (xs : List Val) (t : Val) : (a :: (xs ++ [t])).dropLast = a :: xs := by
  rw [← List.cons_append, List.dropLast_concat]

theorem getLast_cons_snoc (a : Val) (xs : List Val) (t : Val) : (a :: (xs ++ [t])).getLast? = some t := by
  rw [← List.cons_append, List.getLast?_append]; simp

theorem dropLast2_cons_snoc (a : Val) (xs : List Val) (k t : Val) :
    (a :: (xs ++ [k, t])).dropLast.dropLast = a :: xs := by
  have : xs ++ [k, t] = (xs ++ [k]) ++ [t] := by simp
  rw [this, dropLast_cons_snoc, dropLast_cons_snoc]

/-- The tactic for the body of a builder on a concrete input list. -/
syntax "body_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| body_simp $[[$xs,*]]?) => do
    let xs := (xs.map (·.getElems)).getD #[]
    `(tactic| simp [bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift,
        pure, EStateM.pure, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw,
        tryExc, List.getLastD_eq_getLast?, dropLast_cons_snoc, getLast_cons_snoc, $xs,*])

/-! ## `LIST_EXTEND`, `SET_UPDATE` -/

/-- `LIST_EXTEND oparg` (`:2511-2533`): `_PyList_Extend(list, iterable)` with the list `oparg` below
the iterable; on success the iterable is popped. On failure every operand stays (`ERROR_NO_POP`): a
`TypeError` on a value with neither `tp_iter` nor the sequence protocol becomes
`TypeError("Value after * must be an iterable, not T")` (`%.200s` of `tp_name`); a `TypeError` on an
iterable value, and any other exception, propagate unchanged. `SET_UPDATE oparg` (`:2535-2545`) is
`_PySet_Update(set, iterable)` with the same stack discipline and no rewriting. -/
def ListExtendRules : Prop := ∀ (e : Env) (regs : Regs) (it l : Val) (mid below : List Val),
  mid.length + 1 = e.oparg →
  (∀ rt, e.om.listExtend e.ctx l it regs.rt = .ok () rt →
    execOp e .LIST_EXTEND ⟨regs, (it :: (mid ++ [l])) ++ below⟩ = .ok () ⟨{ regs with rt := rt }, (mid ++ [l]) ++ below⟩) ∧
  (∀ x rt1 rt2, e.om.listExtend e.ctx l it regs.rt = .error (.exc x) rt1 →
    givenMatches x 8 (.cls "TypeError") rt1 = .ok false rt2 →
    execOp e .LIST_EXTEND ⟨regs, (it :: (mid ++ [l])) ++ below⟩ =
      .error (.exc x) ⟨{ regs with rt := rt2 }, (it :: (mid ++ [l])) ++ below⟩) ∧
  (∀ x rt1 rt2 rt3, e.om.listExtend e.ctx l it regs.rt = .error (.exc x) rt1 →
    givenMatches x 8 (.cls "TypeError") rt1 = .ok true rt2 → e.om.isIterable it rt2 = .ok true rt3 →
    execOp e .LIST_EXTEND ⟨regs, (it :: (mid ++ [l])) ++ below⟩ =
      .error (.exc x) ⟨{ regs with rt := rt3 }, (it :: (mid ++ [l])) ++ below⟩) ∧
  (∀ x rt1 rt2 rt3 tn rt4 y rt5, e.om.listExtend e.ctx l it regs.rt = .error (.exc x) rt1 →
    givenMatches x 8 (.cls "TypeError") rt1 = .ok true rt2 → e.om.isIterable it rt2 = .ok false rt3 →
    tpName it rt3 = .ok tn rt4 →
    typeError (α := Unit) s!"Value after * must be an iterable, not {trunc200 tn}" rt4 = .error y rt5 →
    execOp e .LIST_EXTEND ⟨regs, (it :: (mid ++ [l])) ++ below⟩ =
      .error y ⟨{ regs with rt := rt5 }, (it :: (mid ++ [l])) ++ below⟩) ∧
  (∀ rt, e.om.setUpdate e.ctx l it regs.rt = .ok () rt →
    execOp e .SET_UPDATE ⟨regs, (it :: (mid ++ [l])) ++ below⟩ = .ok () ⟨{ regs with rt := rt }, (mid ++ [l]) ++ below⟩) ∧
  (∀ x rt, e.om.setUpdate e.ctx l it regs.rt = .error x rt →
    execOp e .SET_UPDATE ⟨regs, (it :: (mid ++ [l])) ++ below⟩ =
      .error x ⟨{ regs with rt := rt }, (it :: (mid ++ [l])) ++ below⟩)

theorem listExtendRules_proven : ListExtendRules := by
  intro e regs it l mid below hm
  have hL : (it :: (mid ++ [l])).length = e.oparg + 1 := by simp; omega
  have hq : (l :: mid.reverse).length = e.oparg := by simp; omega
  refine ⟨fun rt h => ?_, fun x rt1 rt2 h hm1 => ?_, fun x rt1 rt2 rt3 h hm1 hi => ?_,
    fun x rt1 rt2 rt3 tn rt4 y rt5 h hm1 hi ht hy => ?_, fun rt h => ?_, fun x rt h => ?_⟩
  · simp only [execOp, LIST_EXTEND]
    refine (stkK_split_ok (outs := l :: mid.reverse) (r := { regs with rt := rt }) hL ?_ hq).trans (by simp)
    body_simp [h]
  · simp only [execOp, LIST_EXTEND]
    refine stkK_split_err hL ?_
    body_simp [h, hm1]
  · simp only [execOp, LIST_EXTEND]
    refine stkK_split_err hL ?_
    body_simp [h, hm1, hi]
  · simp only [execOp, LIST_EXTEND]
    refine stkK_split_err hL ?_
    body_simp [h, hm1, hi, ht, hy]
  · simp only [execOp, SET_UPDATE]
    refine (stkK_split_ok (outs := l :: mid.reverse) (r := { regs with rt := rt }) hL ?_ hq).trans (by simp)
    body_simp [h]
  · simp only [execOp, SET_UPDATE]
    refine stkK_split_err hL ?_
    body_simp [h]

/-! ## `DICT_UPDATE` -/

/-- `DICT_UPDATE oparg` (`:2610-2636`): `PyDict_Update(dict, update)` with the dict `oparg` below;
on success `update` is popped. On failure every operand stays (`ERROR_NO_POP`). An `AttributeError`
is taken out and `PyObject_HasAttrWithError(update, "keys")` asked: with no `keys` it becomes
`TypeError("'T' object is not a mapping")` (`%T`); with `keys` the original `AttributeError`
propagates as it was; when that probe raises, its exception propagates with the `AttributeError` as
`__context__` (`_PyErr_ChainExceptions1`). Any other exception propagates unchanged. -/
def DictUpdateRules : Prop := ∀ (e : Env) (regs : Regs) (upd d : Val) (mid below : List Val),
  mid.length + 1 = e.oparg →
  let S := (upd :: (mid ++ [d])) ++ below
  (∀ rt, e.om.dictUpdate e.ctx d upd regs.rt = .ok () rt →
    execOp e .DICT_UPDATE ⟨regs, S⟩ = .ok () ⟨{ regs with rt := rt }, (mid ++ [d]) ++ below⟩) ∧
  (∀ x rt1 rt2, e.om.dictUpdate e.ctx d upd regs.rt = .error (.exc x) rt1 →
    givenMatches x 8 (.cls "AttributeError") rt1 = .ok false rt2 →
    execOp e .DICT_UPDATE ⟨regs, S⟩ = .error (.exc x) ⟨{ regs with rt := rt2 }, S⟩) ∧
  (∀ x rt1 rt2 rt3, e.om.dictUpdate e.ctx d upd regs.rt = .error (.exc x) rt1 →
    givenMatches x 8 (.cls "AttributeError") rt1 = .ok true rt2 →
    hasAttrWithError e upd "keys" rt2 = .ok true rt3 →
    execOp e .DICT_UPDATE ⟨regs, S⟩ = .error (.exc x) ⟨{ regs with rt := rt3 }, S⟩) ∧
  (∀ x rt1 rt2 rt3 tn rt4 y rt5, e.om.dictUpdate e.ctx d upd regs.rt = .error (.exc x) rt1 →
    givenMatches x 8 (.cls "AttributeError") rt1 = .ok true rt2 →
    hasAttrWithError e upd "keys" rt2 = .ok false rt3 → typeFullName upd rt3 = .ok tn rt4 →
    typeError (α := Unit) s!"'{tn}' object is not a mapping" rt4 = .error y rt5 →
    execOp e .DICT_UPDATE ⟨regs, S⟩ = .error y ⟨{ regs with rt := rt5 }, S⟩) ∧
  (∀ x rt1 rt2 z rt3 y rt4, e.om.dictUpdate e.ctx d upd regs.rt = .error (.exc x) rt1 →
    givenMatches x 8 (.cls "AttributeError") rt1 = .ok true rt2 →
    hasAttrWithError e upd "keys" rt2 = .error (.exc z) rt3 →
    chainAndRaise (α := Option Bool) z x rt3 = .error y rt4 →
    execOp e .DICT_UPDATE ⟨regs, S⟩ = .error y ⟨{ regs with rt := rt4 }, S⟩)

theorem dictUpdateRules_proven : DictUpdateRules := by
  intro e regs upd d mid below hm
  have hL : (upd :: (mid ++ [d])).length = e.oparg + 1 := by simp; omega
  have hq : (d :: mid.reverse).length = e.oparg := by simp; omega
  refine ⟨fun rt h => ?_, fun x rt1 rt2 h hm1 => ?_, fun x rt1 rt2 rt3 h hm1 hk => ?_,
    fun x rt1 rt2 rt3 tn rt4 y rt5 h hm1 hk ht hy => ?_, fun x rt1 rt2 z rt3 y rt4 h hm1 hk hc => ?_⟩
  · simp only [execOp, DICT_UPDATE]
    refine (stkK_split_ok (outs := d :: mid.reverse) (r := { regs with rt := rt }) hL ?_ hq).trans (by simp)
    body_simp [h]
  · simp only [execOp, DICT_UPDATE]
    refine stkK_split_err hL ?_
    body_simp [h, hm1]
  · simp only [execOp, DICT_UPDATE]
    refine stkK_split_err hL ?_
    body_simp [h, hm1, hk, Functor.map, EStateM.map]
  · simp only [execOp, DICT_UPDATE]
    refine stkK_split_err hL ?_
    body_simp [h, hm1, hk, ht, hy, Functor.map, EStateM.map]
  · simp only [execOp, DICT_UPDATE]
    refine stkK_split_err hL ?_
    body_simp [h, hm1, hk, hc, Functor.map, EStateM.map]

/-! ## `DICT_MERGE` -/

/-- `DICT_MERGE oparg` (`:2638-2654`) on `(callable, x1, x2, dict, unused[oparg-1], update)`:
`_PyDict_MergeUniq(dict, update, &dupkey)`; on success `update` is popped. On failure every operand
stays (`ERROR_NO_POP`) and `_PyEval_FormatKwargsError` (`Python/ceval.c:3414-3446`) rewrites the
error: a duplicate key `k` gives `TypeError("F got multiple values for keyword argument 'K'")` with
`F` the `_PyObject_FunctionStr` of the callable, or `"function"` when that fails, and `K` the
`str()` of the key; with no duplicate, an `AttributeError` becomes `TypeError("Value after ** must
be a mapping, not T")` only when `update` has no `keys`, is restored as it was when it has, and is
the `__context__` of whatever the `keys` probe raised; any other exception propagates unchanged.
A `KeyError` raised by the mapping is such an other exception: since 3.15 it is not read as a
duplicate. -/
def DictMergeRules : Prop := ∀ (e : Env) (regs : Regs) (upd d x1 x2 callable : Val) (mid below : List Val),
  mid.length + 1 = e.oparg →
  let S := (upd :: (mid ++ [d, x2, x1, callable])) ++ below
  (∀ rt, e.om.dictMerge e.ctx d upd regs.rt = .ok none rt →
    execOp e .DICT_MERGE ⟨regs, S⟩ = .ok () ⟨{ regs with rt := rt }, (mid ++ [d, x2, x1, callable]) ++ below⟩) ∧
  (∀ k rt fs rt1 ks rt2 y rt3, e.om.dictMerge e.ctx d upd regs.rt = .ok (some k) rt →
    functionStr e callable rt = .ok fs rt1 → strText e k rt1 = .ok ks rt2 →
    typeError (α := List Val) s!"{fs.getD "function"} got multiple values for keyword argument '{ks}'" rt2 =
      .error y rt3 →
    execOp e .DICT_MERGE ⟨regs, S⟩ = .error y ⟨{ regs with rt := rt3 }, S⟩) ∧
  (∀ x rt1 rt2, e.om.dictMerge e.ctx d upd regs.rt = .error (.exc x) rt1 →
    givenMatches x 8 (.cls "AttributeError") rt1 = .ok false rt2 →
    execOp e .DICT_MERGE ⟨regs, S⟩ = .error (.exc x) ⟨{ regs with rt := rt2 }, S⟩) ∧
  (∀ x rt1 rt2 rt3, e.om.dictMerge e.ctx d upd regs.rt = .error (.exc x) rt1 →
    givenMatches x 8 (.cls "AttributeError") rt1 = .ok true rt2 →
    hasAttrWithError e upd "keys" rt2 = .ok true rt3 →
    execOp e .DICT_MERGE ⟨regs, S⟩ = .error (.exc x) ⟨{ regs with rt := rt3 }, S⟩) ∧
  (∀ x rt1 rt2 rt3 tn rt4 y rt5, e.om.dictMerge e.ctx d upd regs.rt = .error (.exc x) rt1 →
    givenMatches x 8 (.cls "AttributeError") rt1 = .ok true rt2 →
    hasAttrWithError e upd "keys" rt2 = .ok false rt3 → typeFullName upd rt3 = .ok tn rt4 →
    typeError (α := Option Val) s!"Value after ** must be a mapping, not {tn}" rt4 = .error y rt5 →
    execOp e .DICT_MERGE ⟨regs, S⟩ = .error y ⟨{ regs with rt := rt5 }, S⟩) ∧
  (∀ x rt1 rt2 z rt3 y rt4, e.om.dictMerge e.ctx d upd regs.rt = .error (.exc x) rt1 →
    givenMatches x 8 (.cls "AttributeError") rt1 = .ok true rt2 →
    hasAttrWithError e upd "keys" rt2 = .error (.exc z) rt3 →
    chainAndRaise (α := Option Bool) z x rt3 = .error y rt4 →
    execOp e .DICT_MERGE ⟨regs, S⟩ = .error y ⟨{ regs with rt := rt4 }, S⟩)

theorem dictMergeRules_proven : DictMergeRules := by
  intro e regs upd d x1 x2 callable mid below hm
  have hL : (upd :: (mid ++ [d, x2, x1, callable])).length = e.oparg + 4 := by simp; omega
  have hq : (callable :: x1 :: x2 :: d :: mid.reverse).length = e.oparg + 3 := by simp; omega
  refine ⟨fun rt h => ?_, fun k rt fs rt1 ks rt2 y rt3 h hf hk hy => ?_, fun x rt1 rt2 h hm1 => ?_,
    fun x rt1 rt2 rt3 h hm1 hk => ?_, fun x rt1 rt2 rt3 tn rt4 y rt5 h hm1 hk ht hy => ?_,
    fun x rt1 rt2 z rt3 y rt4 h hm1 hk hc => ?_⟩
  · simp only [execOp, DICT_MERGE]
    refine (stkK_split_ok (outs := callable :: x1 :: x2 :: d :: mid.reverse) (r := { regs with rt := rt }) hL ?_ hq).trans (by simp)
    body_simp [h]
  · simp only [execOp, DICT_MERGE]
    refine stkK_split_err hL ?_
    body_simp [h, formatKwargsError, hf, hk, hy]
  · simp only [execOp, DICT_MERGE]
    refine stkK_split_err hL ?_
    body_simp [h, formatKwargsError, hm1]
  · simp only [execOp, DICT_MERGE]
    refine stkK_split_err hL ?_
    body_simp [h, formatKwargsError, hm1, hk, Functor.map, EStateM.map]
  · simp only [execOp, DICT_MERGE]
    refine stkK_split_err hL ?_
    body_simp [h, formatKwargsError, hm1, hk, ht, hy, Functor.map, EStateM.map]
  · simp only [execOp, DICT_MERGE]
    refine stkK_split_err hL ?_
    body_simp [h, formatKwargsError, hm1, hk, hc, Functor.map, EStateM.map]

/-! ## `SET_ADD`, `MAP_ADD` -/

/-- `SET_ADD oparg` (`:1380-1392`) and `MAP_ADD oparg` (`:2656-2666`). `SET_ADD` first checks the
target, since 3.15 (gh-154902, user code can rebind `__conditional_annotations__`): anything but an
exact set raises `TypeError("'T' object is not a set")` (`%T`) without touching the value; on an
exact set it adds the value (`_PySet_AddTakeRef`) and pops it. `MAP_ADD` stores `dict[key] = value`
(`_PyDict_SetItem_Take2`) and pops both. Either way a failure pops every operand (`ERROR_IF`). -/
def SetMapAddRules : Prop := ∀ (e : Env) (regs : Regs) (v c : Val) (mid below : List Val),
  mid.length + 1 = e.oparg →
  ((∃ a items, c = .ref a ∧ regs.rt.heap[a]? = some (.set false items)) →
    (∀ rt, setAdd e.om e.ctx c v regs.rt = .ok () rt →
      execOp e .SET_ADD ⟨regs, (v :: (mid ++ [c])) ++ below⟩ = .ok () ⟨{ regs with rt := rt }, (mid ++ [c]) ++ below⟩) ∧
    (∀ x rt, setAdd e.om e.ctx c v regs.rt = .error x rt →
      execOp e .SET_ADD ⟨regs, (v :: (mid ++ [c])) ++ below⟩ = .error x ⟨{ regs with rt := rt }, below⟩)) ∧
  (Live regs.rt c → (¬ ∃ a items, c = .ref a ∧ regs.rt.heap[a]? = some (.set false items)) →
    ∀ tn rt1 y rt2, typeFullName c regs.rt = .ok tn rt1 →
      typeError (α := Unit) s!"'{tn}' object is not a set" rt1 = .error y rt2 →
      execOp e .SET_ADD ⟨regs, (v :: (mid ++ [c])) ++ below⟩ = .error y ⟨{ regs with rt := rt2 }, below⟩) ∧
  (∀ key rt, dictSet e.om e.ctx c key v regs.rt = .ok () rt →
    execOp e .MAP_ADD ⟨regs, (v :: key :: (mid ++ [c])) ++ below⟩ = .ok () ⟨{ regs with rt := rt }, (mid ++ [c]) ++ below⟩) ∧
  (∀ key x rt, dictSet e.om e.ctx c key v regs.rt = .error x rt →
    execOp e .MAP_ADD ⟨regs, (v :: key :: (mid ++ [c])) ++ below⟩ = .error x ⟨{ regs with rt := rt }, below⟩)

theorem isExactSet_true {rt : Rt} {c : Val} (h : ∃ a items, c = .ref a ∧ rt.heap[a]? = some (.set false items)) :
    isExactSet c rt = .ok true rt := by
  obtain ⟨a, items, rfl, ho⟩ := h
  simp [isExactSet, getObj, ho, bind, EStateM.bind, pure, EStateM.pure]

theorem isExactSet_false {rt : Rt} {c : Val} (hl : Live rt c)
    (h : ¬ ∃ a items, c = .ref a ∧ rt.heap[a]? = some (.set false items)) :
    isExactSet c rt = .ok false rt := by
  cases c with
  | ref a =>
    obtain ⟨o, ho⟩ := live_obj hl
    cases o with
    | set fr items =>
      cases fr with
      | false => exact absurd ⟨a, items, rfl, ho⟩ h
      | true => simp [isExactSet, getObj, ho, bind, EStateM.bind, pure, EStateM.pure]
    | _ => simp [isExactSet, getObj, ho, bind, EStateM.bind, pure, EStateM.pure]
  | _ => simp [isExactSet, pure, EStateM.pure]

theorem setMapAddRules_proven : SetMapAddRules := by
  intro e regs v c mid below hm
  have hL : (v :: (mid ++ [c])).length = e.oparg + 1 := by simp; omega
  have hq : (c :: mid.reverse).length = e.oparg := by simp; omega
  refine ⟨fun hs => ⟨fun rt h => ?_, fun x rt h => ?_⟩, fun hl hs tn rt1 y rt2 ht hy => ?_,
    fun key rt h => ?_, fun key x rt h => ?_⟩
  · have hx := isExactSet_true (rt := regs.rt) hs
    simp only [execOp, SET_ADD]
    refine (stk_split_ok (outs := c :: mid.reverse) (r := { regs with rt := rt }) hL ?_ hq).trans (by simp)
    body_simp [hx, h]
  · have hx := isExactSet_true (rt := regs.rt) hs
    simp only [execOp, SET_ADD]
    refine stk_split_err hL ?_
    body_simp [hx, h]
  · have hx := isExactSet_false hl hs
    simp only [execOp, SET_ADD]
    refine stk_split_err hL ?_
    body_simp [hx, ht, hy]
  · have hL2 : (v :: key :: (mid ++ [c])).length = e.oparg + 2 := by simp; omega
    have hk : (c :: (mid.reverse ++ [key, v]))[e.oparg]? = some key := by
      rw [← hm]; simp [List.getElem?_append_right]
    have hv : (mid.reverse ++ [key, v])[e.oparg]? = some v := by
      rw [← hm]; simp [List.getElem?_append_right]
    simp only [execOp, MAP_ADD]
    refine (stk_split_ok (outs := c :: mid.reverse) (r := { regs with rt := rt }) hL2 ?_ hq).trans (by simp)
    body_simp [h, hk, hv, dropLast2_cons_snoc]
  · have hL2 : (v :: key :: (mid ++ [c])).length = e.oparg + 2 := by simp; omega
    have hk : (c :: (mid.reverse ++ [key, v]))[e.oparg]? = some key := by
      rw [← hm]; simp [List.getElem?_append_right]
    have hv : (mid.reverse ++ [key, v])[e.oparg]? = some v := by
      rw [← hm]; simp [List.getElem?_append_right]
    simp only [execOp, MAP_ADD]
    refine stk_split_err hL2 ?_
    body_simp [h, hk, hv, dropLast2_cons_snoc]

/-! ## `BUILD_SET`, `BUILD_MAP` -/

/-- `f` run on each element of `xs` in order from `rt` succeeds every time and leaves `rt'`. -/
def RunChain {α : Type} (f : α → RM Unit) : Rt → List α → Rt → Prop
  | rt, [], rt' => rt' = rt
  | rt, x :: xs, rt' => ∃ rt1, f x rt = .ok () rt1 ∧ RunChain f rt1 xs rt'

theorem setAddAll_chain (e : Env) (s : Val) :
    ∀ (xs : List Val) (rt rt' : Rt), RunChain (setAdd e.om e.ctx s) rt xs rt' →
      setAddAll e s xs rt = .ok () rt' := by
  intro xs; induction xs with
  | nil => intro rt rt' h; simp only [RunChain] at h; subst h; rfl
  | cons x xs ih =>
    intro rt rt' h; obtain ⟨rt1, h1, h2⟩ := h
    simp [setAddAll, bind, EStateM.bind, h1, ih rt1 rt' h2]

theorem setAddAll_err (e : Env) (s : Val) (x : Val) (post : List Val) (err : Err) (rt3 : Rt) :
    ∀ (pre : List Val) (rt rt2 : Rt), RunChain (setAdd e.om e.ctx s) rt pre rt2 →
      setAdd e.om e.ctx s x rt2 = .error err rt3 → setAddAll e s (pre ++ x :: post) rt = .error err rt3 := by
  intro pre; induction pre with
  | nil => intro rt rt2 h hx; simp only [RunChain] at h; subst h; simp [setAddAll, bind, EStateM.bind, hx]
  | cons y ys ih =>
    intro rt rt2 h hx; obtain ⟨rt1, h1, h2⟩ := h
    simp [setAddAll, bind, EStateM.bind, h1, ih rt1 rt2 h2 hx]

/-- The pairs `(k0, v0), (k1, v1), ...` as the flat `k0, v0, k1, v1, ...` of the stack. -/
def flatPairs : List (Val × Val) → List Val
  | [] => []
  | (k, v) :: ps => k :: v :: flatPairs ps

theorem flatPairs_length (ps : List (Val × Val)) : (flatPairs ps).length = ps.length * 2 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => obtain ⟨k, v⟩ := p; simp [flatPairs, ih]; omega

theorem dictFromItems_chain (e : Env) (d : Val) :
    ∀ (ps : List (Val × Val)) (rt rt' : Rt), RunChain (fun p => dictSet e.om e.ctx d p.1 p.2) rt ps rt' →
      dictFromItems e (flatPairs ps) d rt = .ok () rt' := by
  intro ps; induction ps with
  | nil => intro rt rt' h; simp only [RunChain] at h; subst h; simp [flatPairs, dictFromItems, pure, EStateM.pure]
  | cons p ps ih =>
    intro rt rt' h; obtain ⟨rt1, h1, h2⟩ := h
    obtain ⟨k, v⟩ := p
    simp [flatPairs, dictFromItems, bind, EStateM.bind, h1, ih rt1 rt' h2]

theorem dictFromItems_err (e : Env) (d k v : Val) (post : List (Val × Val)) (err : Err) (rt3 : Rt) :
    ∀ (pre : List (Val × Val)) (rt rt2 : Rt), RunChain (fun p => dictSet e.om e.ctx d p.1 p.2) rt pre rt2 →
      dictSet e.om e.ctx d k v rt2 = .error err rt3 →
      dictFromItems e (flatPairs (pre ++ (k, v) :: post)) d rt = .error err rt3 := by
  intro pre; induction pre with
  | nil => intro rt rt2 h hx; simp only [RunChain] at h; subst h; simp [flatPairs, dictFromItems, bind, EStateM.bind, hx]
  | cons p ps ih =>
    intro rt rt2 h hx; obtain ⟨rt1, h1, h2⟩ := h
    obtain ⟨k', v'⟩ := p
    simp [flatPairs, dictFromItems, bind, EStateM.bind, h1, ih rt1 rt2 h2 hx]

/-- `BUILD_SET oparg` (`:2547-2573`) on `values[0..oparg)` (`values[0]` deepest): a new empty set
`s`, then `_PySet_AddTakeRef(s, values[i])` for `i = 0, 1, ...` in order, each in the runtime the
previous left, then `s` replaces the values. When an add fails the remaining values are not added
and the error propagates with every value popped. `BUILD_MAP oparg` (`:2575-2581`) does the same
with a new dict and `setitem(dict, key_i, value_i)` on the `oparg` pairs, keys and values
interleaved on the stack. For every object model, so for keys with Python `__hash__`/`__eq__`. -/
def BuildSetMapRules : Prop := ∀ (e : Env) (regs : Regs) (below : List Val),
  (∀ vs : List Val, vs.length = e.oparg →
    let s := Val.ref regs.rt.heap.size
    let rt1 := { regs.rt with heap := regs.rt.heap.push (.set false #[]) }
    (∀ rt2, RunChain (setAdd e.om e.ctx s) rt1 vs rt2 →
      execOp e .BUILD_SET ⟨regs, vs.reverse ++ below⟩ = .ok () ⟨{ regs with rt := rt2 }, s :: below⟩) ∧
    (∀ pre x post rt2 err rt3, vs = pre ++ x :: post → RunChain (setAdd e.om e.ctx s) rt1 pre rt2 →
      setAdd e.om e.ctx s x rt2 = .error err rt3 →
      execOp e .BUILD_SET ⟨regs, vs.reverse ++ below⟩ = .error err ⟨{ regs with rt := rt3 }, below⟩)) ∧
  (∀ ps : List (Val × Val), ps.length = e.oparg →
    let d := Val.ref regs.rt.heap.size
    let dv : DictObj := { version := regs.rt.nextVersion }
    let rt1 : Rt := { regs.rt with heap := regs.rt.heap.push (Obj.dict dv), nextVersion := regs.rt.nextVersion + 1 }
    (∀ rt2, RunChain (fun p => dictSet e.om e.ctx d p.1 p.2) rt1 ps rt2 →
      execOp e .BUILD_MAP ⟨regs, (flatPairs ps).reverse ++ below⟩ = .ok () ⟨{ regs with rt := rt2 }, d :: below⟩) ∧
    (∀ pre k v post rt2 err rt3, ps = pre ++ (k, v) :: post →
      RunChain (fun p => dictSet e.om e.ctx d p.1 p.2) rt1 pre rt2 → dictSet e.om e.ctx d k v rt2 = .error err rt3 →
      execOp e .BUILD_MAP ⟨regs, (flatPairs ps).reverse ++ below⟩ = .error err ⟨{ regs with rt := rt3 }, below⟩))

theorem buildSetMapRules_proven : BuildSetMapRules := by
  intro e regs below
  constructor
  · intro vs hlen
    have hL : vs.reverse.length = e.oparg := by simp [hlen]
    constructor
    · intro rt2 hc
      simp only [execOp, BUILD_SET]
      refine (stk_split_ok (outs := [Val.ref regs.rt.heap.size]) (r := { regs with rt := rt2 }) hL ?_ rfl).trans (by simp)
      have := setAddAll_chain e _ vs _ rt2 hc
      body_simp [alloc, this]
    · intro pre x post rt2 err rt3 hv hc hx
      simp only [execOp, BUILD_SET]
      refine stk_split_err hL ?_
      have := setAddAll_err e _ x post err rt3 pre _ rt2 hc hx
      rw [← hv] at this
      body_simp [alloc, this]
  · intro ps hlen
    have hL : (flatPairs ps).reverse.length = e.oparg * 2 := by simp [flatPairs_length, hlen]
    constructor
    · intro rt2 hc
      simp only [execOp, BUILD_MAP]
      refine (stk_split_ok (outs := [Val.ref regs.rt.heap.size]) (r := { regs with rt := rt2 }) hL ?_ rfl).trans (by simp)
      have := dictFromItems_chain e _ ps _ rt2 hc
      body_simp [mkDict, freshVersion, alloc, this]
    · intro pre k v post rt2 err rt3 hv hc hx
      simp only [execOp, BUILD_MAP]
      refine stk_split_err hL ?_
      have := dictFromItems_err e _ k v post err rt3 pre _ rt2 hc hx
      rw [← hv] at this
      body_simp [mkDict, freshVersion, alloc, this]

def BuildersRules : Prop := ListExtendRules ∧ DictUpdateRules ∧ DictMergeRules ∧ SetMapAddRules ∧ BuildSetMapRules
theorem buildersRules_proven : BuildersRules :=
  ⟨listExtendRules_proven, dictUpdateRules_proven, dictMergeRules_proven, setMapAddRules_proven,
    buildSetMapRules_proven⟩

end PyLean.Bytecode
