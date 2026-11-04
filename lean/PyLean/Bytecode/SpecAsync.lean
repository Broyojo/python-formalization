import PyLean.Bytecode.SpecExcMatch

/-!
`GET_AITER` (`Python/bytecodes.c:1607-1641`) and `GET_ANEXT` (`:1643-1649`) with
`_PyEval_GetANext` (`Python/ceval.c:3557-3594`). The instructions are stated for every object model;
the protocol inside them is the difftest object model's `getAIterImpl`/`getANextImpl`
(`Builtins.lean`), which `Proto.mkOM P (n + 1)` installs as `getAIter`/`getANext` (by definition),
stated for every inner object model.
-/

namespace PyLean.Bytecode

open Uop

/-- `GET_AITER` on `obj`: the result of `am_aiter` replaces it, and on failure it is popped
(`PyStackRef_CLOSE(obj)` before `ERROR_IF`, `:1621-1627`); the protocol (`getAIterImpl`): a type
with no `__aiter__` gives `TypeError("'async for' requires an object with __aiter__ method, got T")`
(`%.100s`), the lookup's or the call's error propagates, and a result whose type has no `__anext__`
gives `TypeError("'async for' received an object from __aiter__ that does not implement __anext__:
U")`; otherwise the result itself, whatever else it is. -/
def GetAIterRules : Prop :=
  (∀ (e : Env) (regs : Regs) (o : Val) (rest : List Val),
    (∀ it rt, e.om.getAIter e.ctx o regs.rt = .ok it rt →
      execOp e .GET_AITER ⟨regs, o :: rest⟩ = .ok () ⟨{ regs with rt := rt }, it :: rest⟩) ∧
    (∀ x rt, e.om.getAIter e.ctx o regs.rt = .error x rt →
      execOp e .GET_AITER ⟨regs, o :: rest⟩ = .error x ⟨{ regs with rt := rt }, rest⟩)) ∧
  (∀ (om : ObjModel) (ctx : Ctx) (o : Val) (rt : Rt),
    (∀ rt1 t rt2, Proto.callDunder om ctx o "__aiter__" [] rt = .ok none rt1 → tpName o rt1 = .ok t rt2 →
      Proto.getAIterImpl om ctx o rt =
        typeError s!"'async for' requires an object with __aiter__ method, got {trunc100 t}" rt2) ∧
    (∀ x rt1, Proto.callDunder om ctx o "__aiter__" [] rt = .error x rt1 → Proto.getAIterImpl om ctx o rt = .error x rt1) ∧
    (∀ it rt1 T rt2, Proto.callDunder om ctx o "__aiter__" [] rt = .ok (some it) rt1 → typeOf it rt1 = .ok T rt2 →
      (∀ rt3, Proto.userLookup T "__anext__" rt2 = .ok none rt3 → ∀ u rt4, tpName it rt3 = .ok u rt4 →
        ∀ x rt5, typeError (α := Unit)
          s!"'async for' received an object from __aiter__ that does not implement __anext__: {trunc100 u}" rt4 =
            .error x rt5 →
        Proto.getAIterImpl om ctx o rt = .error x rt5) ∧
      (∀ f rt3, Proto.userLookup T "__anext__" rt2 = .ok (some f) rt3 → Proto.getAIterImpl om ctx o rt = .ok it rt3)))

theorem getAIterRules_proven : GetAIterRules := by
  refine ⟨fun e regs o rest => ⟨fun it rt h => ?_, fun x rt h => ?_⟩, fun om ctx o rt => ?_⟩
  · bc_simp [execOp, GET_AITER, h]
  · bc_simp [execOp, GET_AITER, h]
  · refine ⟨fun rt1 t rt2 h1 h2 => ?_, fun x rt1 h => ?_, fun it rt1 T rt2 h1 h2 => ⟨fun rt3 h3 u rt4 h4 x rt5 h5 => ?_,
      fun f rt3 h3 => ?_⟩⟩
    · simp [Proto.getAIterImpl, h1, h2, bind, EStateM.bind]
    · simp [Proto.getAIterImpl, h, bind, EStateM.bind]
    · simp [Proto.getAIterImpl, h1, h2, h3, h4, h5, bind, EStateM.bind]
    · simp [Proto.getAIterImpl, h1, h2, h3, bind, EStateM.bind, pure, EStateM.pure]

/-- `GET_ANEXT` on `aiter`: it pushes the awaitable `_PyEval_GetANext` returns above `aiter` and keeps
`aiter` when it fails (`ERROR_NO_POP`, `:1643-1649`). `_PyEval_GetANext` (`getANextImpl`): a type
with no `__anext__` gives `TypeError("'async for' requires an iterator with __anext__ method, got
T")`; the lookup's or the call's error propagates; the result `n` goes through
`_PyCoro_GetAwaitableIter`, whose result is returned, and whose exception, any exception and not only
a `TypeError` (`__await__` raising `ValueError` included), becomes the `__cause__` and `__context__`
of a new `TypeError("'async for' received an invalid object from __anext__: U")` raised as it is
(`_PyErr_FormatFromCause`). -/
def GetANextRules : Prop :=
  (∀ (e : Env) (regs : Regs) (a : Val) (rest : List Val),
    (∀ w rt, e.om.getANext e.ctx a regs.rt = .ok w rt →
      execOp e .GET_ANEXT ⟨regs, a :: rest⟩ = .ok () ⟨{ regs with rt := rt }, w :: a :: rest⟩) ∧
    (∀ x rt, e.om.getANext e.ctx a regs.rt = .error x rt →
      execOp e .GET_ANEXT ⟨regs, a :: rest⟩ = .error x ⟨{ regs with rt := rt }, a :: rest⟩)) ∧
  (∀ (P : Program) (om : ObjModel) (ctx : Ctx) (o : Val) (rt : Rt),
    (∀ rt1 t rt2, Proto.callDunder om ctx o "__anext__" [] rt = .ok none rt1 → tpName o rt1 = .ok t rt2 →
      Proto.getANextImpl P om ctx o rt =
        typeError s!"'async for' requires an iterator with __anext__ method, got {trunc100 t}" rt2) ∧
    (∀ x rt1, Proto.callDunder om ctx o "__anext__" [] rt = .error x rt1 → Proto.getANextImpl P om ctx o rt = .error x rt1) ∧
    (∀ n rt1, Proto.callDunder om ctx o "__anext__" [] rt = .ok (some n) rt1 →
      (∀ r rt2, Proto.awaitableIter P om ctx n rt1 = .ok r rt2 → Proto.getANextImpl P om ctx o rt = .ok r rt2) ∧
      (∀ x rt2 t rt3 err rt4, Proto.awaitableIter P om ctx n rt1 = .error (.exc x) rt2 → tpName n rt2 = .ok t rt3 →
        newExc (.cls "TypeError") [.str s!"'async for' received an invalid object from __anext__: {trunc100 t}"] rt3 =
          .ok err rt4 →
        Proto.getANextImpl P om ctx o rt = (do setCause err x; setContext err x; throw (.exc err) : RM Val) rt4)))

theorem getANextRules_proven : GetANextRules := by
  refine ⟨fun e regs a rest => ⟨fun w rt h => ?_, fun x rt h => ?_⟩, fun P om ctx o rt => ?_⟩
  · bc_simp [execOp, GET_ANEXT, h]
  · bc_simp [execOp, GET_ANEXT, h]
  · refine ⟨fun rt1 t rt2 h1 h2 => ?_, fun x rt1 h => ?_, fun n rt1 h1 => ⟨fun r rt2 h2 => ?_,
      fun x rt2 t rt3 err rt4 h2 h3 h4 => ?_⟩⟩
    · simp [Proto.getANextImpl, h1, h2, bind, EStateM.bind]
    · simp [Proto.getANextImpl, h, bind, EStateM.bind]
    · simp [Proto.getANextImpl, h1, h2, tryExc, bind, EStateM.bind]
    · simp only [Proto.getANextImpl, h1, tryExc, bind, EStateM.bind]
      simp only [h2]
      simp only [h3, h4]

end PyLean.Bytecode
