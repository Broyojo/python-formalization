import PyLean.Bytecode.SpecBuild

/-!
`GET_ITER` and its two specializations (`Python/bytecodes.c:3720-3781`, `_PyEval_GetIter`,
`Python/ceval.c:1131-1163`), the f-string opcodes `CONVERT_VALUE`, `FORMAT_SIMPLE` and
`FORMAT_WITH_SPEC` (`:5873-5904`), and `CALL_INTRINSIC_1`/`CALL_INTRINSIC_2` (`:1498-1529`), for
every object model.
-/

namespace PyLean.Bytecode

open Uop

/-! ## `GET_ITER` -/

/-- `tp->_tp_iteritem != NULL`: an exact list, tuple, str or bytes (`Objects/listobject.c`,
`tupleobject.c`, `unicodeobject.c`, `bytesobject.c` set the slot; `inherit_slots` does not copy it). -/
def IterItemType (rt : Rt) (v : Val) : Prop :=
  (∃ s, v = .str s) ∨ (∃ b, v = .bytes b) ∨
    ∃ a items, v = .ref a ∧ (rt.heap[a]? = some (.list items) ∨ rt.heap[a]? = some (.tuple items))

theorem hasIterItem_true (rt : Rt) (v : Val) (h : IterItemType rt v) : hasIterItem v rt = .ok true rt := by
  rcases h with ⟨s, rfl⟩ | ⟨b, rfl⟩ | ⟨a, items, rfl, ho | ho⟩
  · simp [hasIterItem, pure, EStateM.pure]
  · simp [hasIterItem, pure, EStateM.pure]
  · simp [hasIterItem, getObj, ho, bind, EStateM.bind, pure, EStateM.pure]
  · simp [hasIterItem, getObj, ho, bind, EStateM.bind, pure, EStateM.pure]

theorem hasIterItem_false (rt : Rt) (v : Val) (hl : Live rt v) (h : ¬ IterItemType rt v) :
    hasIterItem v rt = .ok false rt := by
  cases v with
  | str s => exact absurd (Or.inl ⟨s, rfl⟩) h
  | bytes b => exact absurd (Or.inr (Or.inl ⟨b, rfl⟩)) h
  | ref a =>
    obtain ⟨o, ho⟩ := live_obj hl
    cases o with
    | list items => exact absurd (Or.inr (Or.inr ⟨a, items, rfl, Or.inl ho⟩)) h
    | tuple items => exact absurd (Or.inr (Or.inr ⟨a, items, rfl, Or.inr ho⟩)) h
    | _ => simp [hasIterItem, getObj, ho, bind, EStateM.bind, pure, EStateM.pure]
  | _ => simp [hasIterItem, pure, EStateM.pure]

/-- A coroutine object (`tp == &PyCoro_Type`). -/
def IsCoro (rt : Rt) (v : Val) : Prop := ∃ a g, v = .ref a ∧ rt.heap[a]? = some (.gen g) ∧ g.kind = .coro

theorem genKindOf_notCoro (rt : Rt) (v : Val) (hl : Live rt v) (h : ¬ IsCoro rt v) :
    ∃ k, genKindOf v rt = .ok k rt ∧ k ≠ some .coro := by
  cases v with
  | ref a =>
    obtain ⟨o, ho⟩ := live_obj hl
    cases o with
    | gen g =>
      refine ⟨some g.kind, by simp [genKindOf, getObj, ho, bind, EStateM.bind, pure, EStateM.pure], ?_⟩
      intro hk; exact h ⟨a, g, rfl, ho, by simpa using hk⟩
    | _ => exact ⟨none, by simp [genKindOf, getObj, ho, bind, EStateM.bind, pure, EStateM.pure], by simp⟩
  | _ => exact ⟨none, by simp [genKindOf, pure, EStateM.pure], by simp⟩

/-- `GET_ITER oparg` (`:3736-3746`, `_PyEval_GetIter`, `Python/ceval.c:1131-1163`), for every object
model and live value `v`:
* a type with `_tp_iteritem` (exact list, tuple, str, bytes): `v` stays and a tagged `0` goes above
  it, and no `__iter__` runs;
* otherwise a type whose `tp_iter` is `PyObject_SelfIter` (the builtin iterators, generators): `v`
  stays with `NULL` above;
* otherwise (and not the coroutine case of a `yield from`): `PyObject_GetIter(v)`, whose result
  replaces `v` with `NULL` above, and whose exception propagates with `v` popped;
* a coroutine in the `yield from` of a plain generator (`GET_ITER_YIELD_FROM_CORO_CHECK`):
  `TypeError("cannot 'yield from' a coroutine object in a non-coroutine generator")`, `v` popped.
`GET_ITER_VIRTUAL` (`:3760-3774`) and `GET_ITER_SELF` (`:3748-3758`) give the same result as
`GET_ITER` on the values their guard accepts, and are `GET_ITER` itself on every other value. -/
def GetIterRules : Prop := ∀ (e : Env) (regs : Regs) (v : Val) (rest : List Val) (c : Code),
  Live regs.rt v → e.P[regs.frame.code]? = some c →
  (IterItemType regs.rt v →
    execOp e .GET_ITER ⟨regs, v :: rest⟩ = .ok () ⟨regs, .tagged 0 :: v :: rest⟩ ∧
    execOp e .GET_ITER_VIRTUAL ⟨regs, v :: rest⟩ = .ok () ⟨regs, .tagged 0 :: v :: rest⟩) ∧
  (¬ IterItemType regs.rt v →
    execOp e .GET_ITER_VIRTUAL ⟨regs, v :: rest⟩ = execOp e .GET_ITER ⟨regs, v :: rest⟩) ∧
  (¬ IterItemType regs.rt v → isSelfIter v regs.rt = .ok true regs.rt →
    execOp e .GET_ITER ⟨regs, v :: rest⟩ = .ok () ⟨regs, .null :: v :: rest⟩ ∧
    execOp e .GET_ITER_SELF ⟨regs, v :: rest⟩ = .ok () ⟨regs, .null :: v :: rest⟩) ∧
  (isSelfIter v regs.rt = .ok false regs.rt →
    execOp e .GET_ITER_SELF ⟨regs, v :: rest⟩ = execOp e .GET_ITER ⟨regs, v :: rest⟩) ∧
  (¬ IterItemType regs.rt v → isSelfIter v regs.rt = .ok false regs.rt →
    (fixupGetIter e.oparg c.flags = 0 ∨ ¬ IsCoro regs.rt v) →
    (∀ it rt, e.om.getIter e.ctx v regs.rt = .ok it rt →
      execOp e .GET_ITER ⟨regs, v :: rest⟩ = .ok () ⟨{ regs with rt := rt }, .null :: it :: rest⟩) ∧
    (∀ x rt, e.om.getIter e.ctx v regs.rt = .error x rt →
      execOp e .GET_ITER ⟨regs, v :: rest⟩ = .error x ⟨{ regs with rt := rt }, rest⟩)) ∧
  (¬ IterItemType regs.rt v → isSelfIter v regs.rt = .ok false regs.rt → IsCoro regs.rt v →
    fixupGetIter e.oparg c.flags = getIterYieldFromCoroCheck → ∀ x rt,
    typeError (α := Unit) "cannot 'yield from' a coroutine object in a non-coroutine generator" regs.rt =
      .error x rt →
    execOp e .GET_ITER ⟨regs, v :: rest⟩ = .error x ⟨{ regs with rt := rt }, rest⟩)

theorem isSelfIter_iterItem (rt : Rt) (v : Val) (h : IterItemType rt v) : isSelfIter v rt = .ok false rt := by
  rcases h with ⟨s, rfl⟩ | ⟨b, rfl⟩ | ⟨a, items, rfl, ho | ho⟩
  · simp [isSelfIter, pure, EStateM.pure]
  · simp [isSelfIter, pure, EStateM.pure]
  · simp [isSelfIter, getObj, ho, bind, EStateM.bind, pure, EStateM.pure]
  · simp [isSelfIter, getObj, ho, bind, EStateM.bind, pure, EStateM.pure]

theorem getIterRules_proven : GetIterRules := by
  intro e regs v rest c hl hc
  have hcode : getCode e.P regs = .ok c regs := by simp [getCode, hc]
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ?_, fun h hs => ⟨?_, ?_⟩, fun hs => ?_, fun h hs hco => ⟨?_, ?_⟩,
    fun h hs hco hf x rt hx => ?_⟩
  · have hi := hasIterItem_true regs.rt v h
    bc_simp [execOp, GET_ITER, _SPECIALIZE_GET_ITER, _GET_ITER, getIterStack, hcode, hi]
  · have hi := hasIterItem_true regs.rt v h
    simp only [execOp]
    apply withDeopt_ok
    bc_simp [GET_ITER_VIRTUAL, _GUARD_ITER_VIRTUAL, _PUSH_TAGGED_ZERO, hi]
  · have hi := hasIterItem_false regs.rt v hl h
    simp only [execOp]
    apply withDeopt_of (s' := ⟨regs, v :: rest⟩)
    bc_simp [GET_ITER_VIRTUAL, _GUARD_ITER_VIRTUAL, hi]
  · have hi := hasIterItem_false regs.rt v hl h
    bc_simp [execOp, GET_ITER, _SPECIALIZE_GET_ITER, _GET_ITER, getIterStack, hcode, hi, hs]
  · simp only [execOp]
    apply withDeopt_ok
    bc_simp [GET_ITER_SELF, _GUARD_ITERATOR, PUSH_NULL, hs]
  · simp only [execOp]
    apply withDeopt_of (s' := ⟨regs, v :: rest⟩)
    bc_simp [GET_ITER_SELF, _GUARD_ITERATOR, hs]
  · intro it rt hg
    have hi := hasIterItem_false regs.rt v hl h
    rcases hco with h0 | hnc
    · have h0' : (fixupGetIter e.oparg c.flags != 0) = false := by simp [h0]
      bc_simp [execOp, GET_ITER, _SPECIALIZE_GET_ITER, _GET_ITER, getIterStack, hcode, hi, hs, h0', hg]
    · obtain ⟨k, hk, hk'⟩ := genKindOf_notCoro regs.rt v hl hnc
      have hb : (k == some GenKind.coro) = false := by simpa using hk'
      by_cases hz : fixupGetIter e.oparg c.flags = 0
      · have h0' : (fixupGetIter e.oparg c.flags != 0) = false := by simp [hz]
        bc_simp [execOp, GET_ITER, _SPECIALIZE_GET_ITER, _GET_ITER, getIterStack, hcode, hi, hs, h0', hg]
      · have h0' : (fixupGetIter e.oparg c.flags != 0) = true := by simpa using hz
        bc_simp [execOp, GET_ITER, _SPECIALIZE_GET_ITER, _GET_ITER, getIterStack, hcode, hi, hs, h0', hk, hb, hk', hg]
  · intro x rt hg
    have hi := hasIterItem_false regs.rt v hl h
    rcases hco with h0 | hnc
    · have h0' : (fixupGetIter e.oparg c.flags != 0) = false := by simp [h0]
      bc_simp [execOp, GET_ITER, _SPECIALIZE_GET_ITER, _GET_ITER, getIterStack, hcode, hi, hs, h0', hg]
    · obtain ⟨k, hk, hk'⟩ := genKindOf_notCoro regs.rt v hl hnc
      have hb : (k == some GenKind.coro) = false := by simpa using hk'
      by_cases hz : fixupGetIter e.oparg c.flags = 0
      · have h0' : (fixupGetIter e.oparg c.flags != 0) = false := by simp [hz]
        bc_simp [execOp, GET_ITER, _SPECIALIZE_GET_ITER, _GET_ITER, getIterStack, hcode, hi, hs, h0', hg]
      · have h0' : (fixupGetIter e.oparg c.flags != 0) = true := by simpa using hz
        bc_simp [execOp, GET_ITER, _SPECIALIZE_GET_ITER, _GET_ITER, getIterStack, hcode, hi, hs, h0', hk, hb, hk', hg]
  · have hi := hasIterItem_false regs.rt v hl h
    obtain ⟨a, g, rfl, ho, hgk⟩ := hco
    have hk : genKindOf (.ref a) regs.rt = .ok (some .coro) regs.rt := by
      simp [genKindOf, getObj, ho, hgk, bind, EStateM.bind, pure, EStateM.pure]
    have hnz : fixupGetIter e.oparg c.flags ≠ 0 := by rw [hf]; decide
    have hnz' : (fixupGetIter e.oparg c.flags != 0) = true := by simpa using hnz
    bc_simp [execOp, GET_ITER, _SPECIALIZE_GET_ITER, _GET_ITER, getIterStack, hcode, hi, hs, hk, hnz', hf, hx, getIterYieldFromCoroCheck]

/-! ## f-strings -/

/-- `CONVERT_VALUE oparg` (`:5873-5881`): `_PyEval_ConversionFuncs[oparg]`, which is `PyObject_Str`,
`PyObject_Repr` and `PyObject_ASCII` for `FVC_STR` 1, `FVC_REPR` 2 and `FVC_ASCII` 3 (`!s`, `!r`,
`!a`), replaces the value; on failure the value is popped. `FORMAT_SIMPLE` (`:5883-5897`) leaves an
exact str as it is without calling anything, and replaces any other value by
`PyObject_Format(value, NULL)`, popping it on failure; `FORMAT_WITH_SPEC` (`:5899-5904`) replaces
value and spec by `PyObject_Format(value, spec)`, popping both on failure. For every object model. -/
def FormatRules : Prop := ∀ (e : Env) (regs : Regs) (v : Val) (rest : List Val),
  (∀ (conv : Ctx → Val → RM Val), (e.oparg = 1 ∧ conv = e.om.str ∨ e.oparg = 2 ∧ conv = e.om.repr ∨
      e.oparg = 3 ∧ conv = e.om.ascii) →
    (∀ r rt, conv e.ctx v regs.rt = .ok r rt →
      execOp e .CONVERT_VALUE ⟨regs, v :: rest⟩ = .ok () ⟨{ regs with rt := rt }, r :: rest⟩) ∧
    (∀ x rt, conv e.ctx v regs.rt = .error x rt →
      execOp e .CONVERT_VALUE ⟨regs, v :: rest⟩ = .error x ⟨{ regs with rt := rt }, rest⟩)) ∧
  (∀ s, execOp e .FORMAT_SIMPLE ⟨regs, .str s :: rest⟩ = .ok () ⟨regs, .str s :: rest⟩) ∧
  ((∀ s, v ≠ .str s) →
    (∀ r rt, e.om.format e.ctx v .null regs.rt = .ok r rt →
      execOp e .FORMAT_SIMPLE ⟨regs, v :: rest⟩ = .ok () ⟨{ regs with rt := rt }, r :: rest⟩) ∧
    (∀ x rt, e.om.format e.ctx v .null regs.rt = .error x rt →
      execOp e .FORMAT_SIMPLE ⟨regs, v :: rest⟩ = .error x ⟨{ regs with rt := rt }, rest⟩)) ∧
  (∀ spec,
    (∀ r rt, e.om.format e.ctx v spec regs.rt = .ok r rt →
      execOp e .FORMAT_WITH_SPEC ⟨regs, spec :: v :: rest⟩ = .ok () ⟨{ regs with rt := rt }, r :: rest⟩) ∧
    (∀ x rt, e.om.format e.ctx v spec regs.rt = .error x rt →
      execOp e .FORMAT_WITH_SPEC ⟨regs, spec :: v :: rest⟩ = .error x ⟨{ regs with rt := rt }, rest⟩))

theorem formatRules_proven : FormatRules := by
  intro e regs v rest
  refine ⟨fun conv hc => ?_, fun s => ?_, fun hv => ⟨fun r rt h => ?_, fun x rt h => ?_⟩,
    fun spec => ⟨fun r rt h => ?_, fun x rt h => ?_⟩⟩
  · rcases hc with ⟨h1, rfl⟩ | ⟨h2, rfl⟩ | ⟨h3, rfl⟩
    · exact ⟨fun r rt h => by bc_simp [execOp, CONVERT_VALUE, h1, h],
        fun x rt h => by bc_simp [execOp, CONVERT_VALUE, h1, h]⟩
    · exact ⟨fun r rt h => by bc_simp [execOp, CONVERT_VALUE, h2, h],
        fun x rt h => by bc_simp [execOp, CONVERT_VALUE, h2, h]⟩
    · exact ⟨fun r rt h => by bc_simp [execOp, CONVERT_VALUE, h3, h],
        fun x rt h => by bc_simp [execOp, CONVERT_VALUE, h3, h]⟩
  · bc_simp [execOp, FORMAT_SIMPLE]
  · cases v with
    | str s => exact absurd rfl (hv s)
    | _ => bc_simp [execOp, FORMAT_SIMPLE, h]
  · cases v with
    | str s => exact absurd rfl (hv s)
    | _ => bc_simp [execOp, FORMAT_SIMPLE, h]
  · bc_simp [execOp, FORMAT_WITH_SPEC, h]
  · bc_simp [execOp, FORMAT_WITH_SPEC, h]

/-! ## Intrinsics -/

/-- `CALL_INTRINSIC_1 oparg` (`:1498-1509`) calls `_PyIntrinsics_UnaryFunctions[oparg]` on the value
and replaces it by the result; `CALL_INTRINSIC_2 oparg` (`:1511-1529`) calls
`_PyIntrinsics_BinaryFunctions[oparg](tstate, value2, value1)`, `value2` being the deeper operand,
and replaces both. Since 3.15 both leave through `ERROR_NO_POP` when the intrinsic fails, with their
operands still on the stack. For every object model and oparg. -/
def IntrinsicRules : Prop := ∀ (e : Env) (regs : Regs) (v1 v2 : Val) (rest : List Val),
  (∀ r rt, e.om.intrinsic1 e.ctx regs.frame e.oparg v1 regs.rt = .ok r rt →
    execOp e .CALL_INTRINSIC_1 ⟨regs, v1 :: rest⟩ = .ok () ⟨{ regs with rt := rt }, r :: rest⟩) ∧
  (∀ x rt, e.om.intrinsic1 e.ctx regs.frame e.oparg v1 regs.rt = .error x rt →
    execOp e .CALL_INTRINSIC_1 ⟨regs, v1 :: rest⟩ = .error x ⟨{ regs with rt := rt }, v1 :: rest⟩) ∧
  (∀ r rt, e.om.intrinsic2 e.ctx regs.frame e.oparg v2 v1 regs.rt = .ok r rt →
    execOp e .CALL_INTRINSIC_2 ⟨regs, v1 :: v2 :: rest⟩ = .ok () ⟨{ regs with rt := rt }, r :: rest⟩) ∧
  (∀ x rt, e.om.intrinsic2 e.ctx regs.frame e.oparg v2 v1 regs.rt = .error x rt →
    execOp e .CALL_INTRINSIC_2 ⟨regs, v1 :: v2 :: rest⟩ = .error x ⟨{ regs with rt := rt }, v1 :: v2 :: rest⟩)

theorem intrinsicRules_proven : IntrinsicRules := by
  intro e regs v1 v2 rest
  refine ⟨fun r rt h => ?_, fun x rt h => ?_, fun r rt h => ?_, fun x rt h => ?_⟩ <;>
    bc_simp [execOp, CALL_INTRINSIC_1, CALL_INTRINSIC_2, getFrame, h]

end PyLean.Bytecode
