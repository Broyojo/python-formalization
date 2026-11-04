import PyLean.Bytecode.SpecLoadAttr

/-!
`IMPORT_NAME` and `IMPORT_FROM`, `Python/bytecodes.c:3456-3492`, CPython 3.15 with PEP 810 lazy
imports, for every object model.

`IMPORT_NAME oparg` takes its name from `co_names[oparg >> 2]`. Without bit 1 it goes to
`_PyEval_LazyImportName` with bit 0 (the `lazy` keyword) as `lazy`, which may still import eagerly
(the global mode, `__lazy_modules__`); with bit 1, which the compiler sets for an import in a
function, a class or an exception handler (`Python/codegen.c:2936-2946`), straight to
`_PyEval_ImportName`. Either way `level` and `fromlist` are popped, on failure too (`ERROR_IF`
after `DECREF_INPUTS`). `IMPORT_FROM` keeps the module and pushes the attribute: from a lazy import
object (`PyLazyImport_CheckExact`) through `_PyEval_LazyImportFrom`, from anything else through
`_PyEval_ImportFrom`; a failure keeps the module (`(from -- from, res)`, `ERROR_IF`). A body that
read the wrong bit, the wrong name, swapped `level` and `fromlist`, or popped the module fails a
clause.
-/

namespace PyLean.Bytecode

open Uop

/-- The two import instructions, on `(level, fromlist)` and on `(from)`. `name` is `co_names` of the
running code at the index the instruction reads. -/
def ImportRules : Prop := ∀ (e : Env) (regs : Regs) (rest : List Val) (co : Code) (name : String),
  e.P[regs.frame.code]? = some co →
  (∀ level fromlist, co.names[e.oparg >>> 2]? = some name →
    (e.oparg &&& 2 = 0 →
      (∀ v rt, e.om.lazyImportName e.ctx regs.frame name fromlist level (e.oparg &&& 1 != 0) regs.rt = .ok v rt →
        execOp e .IMPORT_NAME ⟨regs, fromlist :: level :: rest⟩ = .ok () ⟨{ regs with rt := rt }, v :: rest⟩) ∧
      (∀ x rt, e.om.lazyImportName e.ctx regs.frame name fromlist level (e.oparg &&& 1 != 0) regs.rt = .error x rt →
        execOp e .IMPORT_NAME ⟨regs, fromlist :: level :: rest⟩ = .error x ⟨{ regs with rt := rt }, rest⟩)) ∧
    (e.oparg &&& 2 ≠ 0 →
      (∀ v rt, e.om.importName e.ctx regs.frame name fromlist level regs.rt = .ok v rt →
        execOp e .IMPORT_NAME ⟨regs, fromlist :: level :: rest⟩ = .ok () ⟨{ regs with rt := rt }, v :: rest⟩) ∧
      (∀ x rt, e.om.importName e.ctx regs.frame name fromlist level regs.rt = .error x rt →
        execOp e .IMPORT_NAME ⟨regs, fromlist :: level :: rest⟩ = .error x ⟨{ regs with rt := rt }, rest⟩))) ∧
  (∀ m, co.names[e.oparg]? = some name →
    (e.om.isLazyImport m regs.rt = .ok true regs.rt →
      (∀ v rt, e.om.lazyImportFrom e.ctx regs.frame m name regs.rt = .ok v rt →
        execOp e .IMPORT_FROM ⟨regs, m :: rest⟩ = .ok () ⟨{ regs with rt := rt }, v :: m :: rest⟩) ∧
      (∀ x rt, e.om.lazyImportFrom e.ctx regs.frame m name regs.rt = .error x rt →
        execOp e .IMPORT_FROM ⟨regs, m :: rest⟩ = .error x ⟨{ regs with rt := rt }, m :: rest⟩)) ∧
    (e.om.isLazyImport m regs.rt = .ok false regs.rt →
      (∀ v rt, e.om.importFrom e.ctx m name regs.rt = .ok v rt →
        execOp e .IMPORT_FROM ⟨regs, m :: rest⟩ = .ok () ⟨{ regs with rt := rt }, v :: m :: rest⟩) ∧
      (∀ x rt, e.om.importFrom e.ctx m name regs.rt = .error x rt →
        execOp e .IMPORT_FROM ⟨regs, m :: rest⟩ = .error x ⟨{ regs with rt := rt }, m :: rest⟩)))

theorem importRules_proven : ImportRules := by
  intro e regs rest co name hco
  have hname : ∀ i, co.names[i]? = some name → getName e i regs = .ok name regs := by
    intro i hi
    simp [getName, getCode, hco, hi, bind, EStateM.bind, pure, EStateM.pure]
  refine ⟨fun level fromlist hn => ⟨fun hb => ⟨fun v rt hv => ?_, fun x rt hx => ?_⟩,
    fun hb => ⟨fun v rt hv => ?_, fun x rt hx => ?_⟩⟩, fun m hn => ⟨fun hl => ⟨fun v rt hv => ?_,
    fun x rt hx => ?_⟩, fun hl => ⟨fun v rt hv => ?_, fun x rt hx => ?_⟩⟩⟩
  all_goals first
    | (have hg := hname _ hn
       simp only [execOp, IMPORT_NAME]
       generalize (e.oparg &&& 1 != 0) = lz at hv ⊢
       simp [stk, popN, bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift,
         MonadLift.monadLift, hg, getFrame, hb, hv, pure, EStateM.pure, pushAll])
    | (have hg := hname _ hn
       simp only [execOp, IMPORT_NAME]
       generalize (e.oparg &&& 1 != 0) = lz at hx ⊢
       simp [stk, popN, bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift,
         MonadLift.monadLift, hg, getFrame, hb, hx, pure, EStateM.pure])
    | (have hg := hname _ hn
       simp [execOp, IMPORT_FROM, stkK, peekN, popN, bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift,
         MonadLift.monadLift, hg, getFrame, hl, hv, pure, EStateM.pure, pushAll])
    | (have hg := hname _ hn
       simp [execOp, IMPORT_FROM, stkK, peekN, bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift,
         MonadLift.monadLift, hg, getFrame, hl, hx, pure, EStateM.pure])

end PyLean.Bytecode
