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

/-! ## `LOAD_SPECIAL` -/

/-- `LOAD_SPECIAL` (`:4148-4151`: `_INSERT_NULL + _LOAD_SPECIAL`, `:4125-4146`) on `owner`, for every
object model: `_PyObject_LookupSpecialMethod` finding `(method, self)` replaces `owner` by the two,
`self` on top; its error is raised with `owner` kept (`ERROR_NO_POP`); not finding it raises
`TypeError` with `_Py_SpecialMethods[oparg].error`, or `.error_suggestion` when
`_PyEval_SpecialMethodCanSuggest` says the other protocol is there, formatted with `%T` of `owner`
(`typeFullName`, the `__qualname__` for a `__main__` class: `'O.I' object does not support ...`).
`type_has_special_method` (`Python/ceval.c:3742-3749`) counts a name only when what `_PyType_Lookup`
finds has `tp_descr_get`: a function does, an `int` or a builtin function (`__aenter__ = len`) does
not. -/
def LoadSpecialRules : Prop :=
  (∀ (e : Env) (regs : Regs) (o : Val) (rest : List Val),
    (∀ m s rt, e.om.lookupSpecial e.ctx o (specialName e.oparg) regs.rt = .ok (some (m, s)) rt →
      execOp e .LOAD_SPECIAL ⟨regs, o :: rest⟩ = .ok () ⟨{ regs with rt := rt }, s :: m :: rest⟩) ∧
    (∀ x rt, e.om.lookupSpecial e.ctx o (specialName e.oparg) regs.rt = .error x rt →
      execOp e .LOAD_SPECIAL ⟨regs, o :: rest⟩ = .error x ⟨{ regs with rt := rt }, o :: rest⟩) ∧
    (∀ rt b rt1 t rt2 x rt3, e.om.lookupSpecial e.ctx o (specialName e.oparg) regs.rt = .ok none rt →
      specialCanSuggest e o e.oparg rt = .ok b rt1 → typeFullName o rt1 = .ok t rt2 →
      typeError (α := List Val) (specialError e.oparg t b) rt2 = .error x rt3 →
      execOp e .LOAD_SPECIAL ⟨regs, o :: rest⟩ = .error x ⟨{ regs with rt := rt3 }, o :: rest⟩)) ∧
  (∀ (e : Env) (tp : Val) (name : String) (rt : Rt),
    (∀ rt1, e.om.typeLookup tp name rt = .ok none rt1 → typeHasSpecial e tp name rt = .ok false rt1) ∧
    (∀ k rt1, e.om.typeLookup tp name rt = .ok (some (.int k)) rt1 → typeHasSpecial e tp name rt = .ok false rt1) ∧
    (∀ n rt1, e.om.typeLookup tp name rt = .ok (some (.builtin n)) rt1 → typeHasSpecial e tp name rt = .ok false rt1) ∧
    (∀ a f rt1, e.om.typeLookup tp name rt = .ok (some (.ref a)) rt1 → rt1.heap[a]? = some (.func f) →
      typeHasSpecial e tp name rt = .ok true rt1))

theorem loadSpecialRules_proven : LoadSpecialRules := by
  refine ⟨fun e regs o rest => ⟨fun m s rt h => ?_, fun x rt h => ?_, fun rt b rt1 t rt2 x rt3 h1 h2 h3 h4 => ?_⟩,
    fun e tp name rt => ⟨fun rt1 h => ?_, fun k rt1 h => ?_, fun n rt1 h => ?_, fun a f rt1 h hf => ?_⟩⟩
  · bc_simp [execOp, LOAD_SPECIAL, h]
  · bc_simp [execOp, LOAD_SPECIAL, h]
  · bc_simp [execOp, LOAD_SPECIAL, h1, h2, h3, h4]
  · simp [typeHasSpecial, h, bind, EStateM.bind, pure, EStateM.pure]
  · simp [typeHasSpecial, hasDescrGet, h, bind, EStateM.bind, pure, EStateM.pure]
  · simp [typeHasSpecial, hasDescrGet, h, bind, EStateM.bind, pure, EStateM.pure]
  · simp [typeHasSpecial, hasDescrGet, h, hf, getObj, bind, EStateM.bind, pure, EStateM.pure]

/-! ## `LOAD_ATTR_METHOD_NO_DICT`, `LOAD_ATTR_NONDESCRIPTOR_NO_DICT`, `LOAD_ATTR_METHOD_LAZY_DICT` -/

/-- The attribute loads for types whose instances have no `__dict__` or have not created it yet
(`:4261-4333`), cache `[type_version, descr]` (and the unused `dictoffset` word), for every object
model: when `Py_TYPE(owner)->tp_version_tag` is not the cached version, `_GUARD_TYPE_VERSION` exits
and each is the generic `LOAD_ATTR` on the same state; under the cached version
`LOAD_ATTR_METHOD_NO_DICT` leaves the cached descriptor with `owner` above it as `self`
(`:4261-4270`), `LOAD_ATTR_NONDESCRIPTOR_NO_DICT` replaces `owner` by it (`:4295-4302`), and
`LOAD_ATTR_METHOD_LAZY_DICT` does what the `NO_DICT` method form does while the instance's dict has
not been created, and is `LOAD_ATTR` once it has (`_CHECK_ATTR_METHOD_LAZY_DICT`, `:4311-4316`). -/
def MethodLoadNoDictRules : Prop := ∀ (e : Env) (regs : Regs) (o : Val) (rest : List Val) (ver : Nat),
  typeVersionOf o regs = .ok ver regs →
  (ver ≠ cacheNat e 0 →
    execOp e .LOAD_ATTR_METHOD_NO_DICT ⟨regs, o :: rest⟩ = execOp e .LOAD_ATTR ⟨regs, o :: rest⟩ ∧
    execOp e .LOAD_ATTR_NONDESCRIPTOR_NO_DICT ⟨regs, o :: rest⟩ = execOp e .LOAD_ATTR ⟨regs, o :: rest⟩ ∧
    execOp e .LOAD_ATTR_METHOD_LAZY_DICT ⟨regs, o :: rest⟩ = execOp e .LOAD_ATTR ⟨regs, o :: rest⟩) ∧
  (ver = cacheNat e 0 →
    execOp e .LOAD_ATTR_METHOD_NO_DICT ⟨regs, o :: rest⟩ = .ok () ⟨regs, o :: (e.cache[1]?).getD .null :: rest⟩ ∧
    execOp e .LOAD_ATTR_NONDESCRIPTOR_NO_DICT ⟨regs, o :: rest⟩ = .ok () ⟨regs, (e.cache[1]?).getD .null :: rest⟩ ∧
    (∀ a i, instOf o regs.rt = .ok (some (a, i)) regs.rt →
      (i.dict = .null → execOp e .LOAD_ATTR_METHOD_LAZY_DICT ⟨regs, o :: rest⟩ =
        .ok () ⟨regs, o :: (e.cache[1]?).getD .null :: rest⟩) ∧
      (i.dict ≠ .null → execOp e .LOAD_ATTR_METHOD_LAZY_DICT ⟨regs, o :: rest⟩ = execOp e .LOAD_ATTR ⟨regs, o :: rest⟩)) ∧
    (instOf o regs.rt = .ok none regs.rt →
      execOp e .LOAD_ATTR_METHOD_LAZY_DICT ⟨regs, o :: rest⟩ = execOp e .LOAD_ATTR ⟨regs, o :: rest⟩))

theorem methodLoadNoDictRules_proven : MethodLoadNoDictRules := by
  intro e regs o rest ver hv
  refine ⟨fun h => ⟨?_, ?_, ?_⟩, fun h => ⟨?_, ?_, fun a i hi => ⟨fun hd => ?_, fun hd => ?_⟩, fun hi => ?_⟩⟩
  · bc_simp [execOp, withDeopt, LOAD_ATTR_METHOD_NO_DICT, _GUARD_TYPE_VERSION, hv, h]
  · bc_simp [execOp, withDeopt, LOAD_ATTR_NONDESCRIPTOR_NO_DICT, _GUARD_TYPE_VERSION, hv, h]
  · bc_simp [execOp, withDeopt, LOAD_ATTR_METHOD_LAZY_DICT, _GUARD_TYPE_VERSION, hv, h]
  · bc_simp [execOp, withDeopt, LOAD_ATTR_METHOD_NO_DICT, _GUARD_TYPE_VERSION, _LOAD_ATTR_METHOD_NO_DICT, hv, h]
  · bc_simp [execOp, withDeopt, LOAD_ATTR_NONDESCRIPTOR_NO_DICT, _GUARD_TYPE_VERSION,
      _LOAD_ATTR_NONDESCRIPTOR_NO_DICT, hv, h]
  · bc_simp [execOp, withDeopt, LOAD_ATTR_METHOD_LAZY_DICT, _GUARD_TYPE_VERSION, _CHECK_ATTR_METHOD_LAZY_DICT,
      _LOAD_ATTR_METHOD_LAZY_DICT, hv, h, hi, hd]
  · bc_simp [execOp, withDeopt, LOAD_ATTR_METHOD_LAZY_DICT, _GUARD_TYPE_VERSION, _CHECK_ATTR_METHOD_LAZY_DICT,
      hv, h, hi, hd]
  · bc_simp [execOp, withDeopt, LOAD_ATTR_METHOD_LAZY_DICT, _GUARD_TYPE_VERSION, _CHECK_ATTR_METHOD_LAZY_DICT,
      hv, h, hi]

end PyLean.Bytecode
