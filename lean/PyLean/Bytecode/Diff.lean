import PyLean.DiffCore
import PyLean.Bytecode.Builtins

/-!
Differential-testing handler for `bytecode` cases (`"mod": "bytecode"`).

* `fn = "run"`: `codes` is every code object of a compiled module (flat, nested
  code constants by index), `main` the module code. The model runs it from a fresh
  heap and reports what `print` wrote and the uncaught exception, if any.
* `fn = "table"`: decode a raw `co_exceptiontable` and look up an offset.
* `fn = "effect"`: `numPopped`/`numPushed` for an opcode number and an oparg.
-/

namespace PyLean.Bytecode

open Lean PyLean PyLean.Diff PyLean.Bytecode.Proto

/-- A constant from the dump, built on the heap at load time. -/
def loadConst : Nat → Json → RM Val
  | 0, _ => fault "constant too deep"
  | n + 1, j => do
    let tag := (j.getArrVal? 0).toOption.bind (·.getStr?.toOption) |>.getD ""
    let arg := (j.getArrVal? 1).toOption.getD .null
    match tag with
    | "n" => pure .none
    | "e" => pure .ellipsis
    | "t" => pure (.bool true)
    | "F" => pure (.bool false)
    | "i" =>
      match arg.getStr?.toOption.bind String.toInt? with
      | some i => pure (.int i)
      | none => fault "bad int constant"
    | "f" =>
      match arg.getStr?.toOption.bind String.toNat? with
      | some b => pure (.float (UInt64.ofNat b))
      | none => fault "bad float constant"
    | "s" => pure (.str (arg.getStr?.toOption.getD ""))
    | "b" =>
      match arg.getArr? with
      | .ok xs => pure (.bytes (xs.toList.map fun x => UInt8.ofNat (x.getNat?.toOption.getD 0)))
      | .error _ => fault "bad bytes constant"
    | "c" => pure (.code (arg.getNat?.toOption.getD 0 + 2))
    | "S" =>
      match arg.getArr? with
      | .ok #[a, b, c] => do
        alloc (.slice (← loadConst n a) (← loadConst n b) (← loadConst n c))
      | _ => fault "bad slice constant"
    | "T" =>
      match arg.getArr? with
      | .ok xs => mkTuple (← xs.toList.mapM (loadConst n))
      | .error _ => fault "bad tuple constant"
    | "Z" =>
      match arg.getArr? with
      | .ok xs =>
        let vs ← xs.toList.mapM (loadConst n)
        -- frozenset constants hold ints and strs in practice
        alloc (.set true (vs.toArray.map fun v =>
          (match v with
           | .int i => hashInt i
           | .str s => hashStr s
           | _ => 0, v)))
      | .error _ => fault "bad frozenset constant"
    | _ => fault "bad constant tag"

def natArr (j : Json) (k : String) : Except String (Array Nat) := do
  let a ← (← field j k).getArr?
  a.mapM (·.getNat?)

def strArr (j : Json) (k : String) : Except String (Array String) := do
  let a ← (← field j k).getArr?
  a.mapM (·.getStr?)

/-- `co_code` as instructions, one per code unit. -/
def decodeInstrs (raw : Array Nat) : Except String (Array Instr) := do
  let mut out : Array Instr := #[]
  let mut i := 0
  while i + 1 < raw.size do
    match Op.ofNat? raw[i]! with
    | some o => out := out.push { op := o, arg := raw[i + 1]! }
    | none => throw s!"unknown opcode {raw[i]!}"
    i := i + 2
  pure out

/-- A code object from the dump, constants not yet loaded. -/
def loadCode (j : Json) : Except String (Code × Array Json) := do
  let consts ← (← field j "consts").getArr?
  let c : Code := {
    name := ← getStr j "name"
    qualname := ← getStr j "qualname"
    flags := ← getNat j "flags"
    argcount := ← getNat j "argcount"
    posonlyargcount := ← getNat j "posonly"
    kwonlyargcount := ← getNat j "kwonly"
    nlocalsplus := ← getNat j "nlocalsplus"
    ncellvars := ← getNat j "ncellvars"
    nfreevars := ← getNat j "nfreevars"
    stacksize := ← getNat j "stacksize"
    names := ← strArr j "names"
    localsplusnames := ← strArr j "localsplus"
    instrs := ← decodeInstrs (← natArr j "code")
    exceptiontable := ← natArr j "exctable"
    version := (← getNat j "index") + 1 }
  pure (c, consts)

/-- `_Py_INTERPRETER_TRAMPOLINE_INSTRUCTIONS`, `Python/ceval.c:1050-1058`. -/
def trampolineCode : Code :=
  { name := "<trampoline>", instrs := #[
      { op := .NOP, arg := 0 }, { op := .INTERPRETER_EXIT, arg := 0 },
      { op := .NOP, arg := 0 }, { op := .INTERPRETER_EXIT, arg := 0 },
      { op := .RESUME, arg := 4 }] }

/-- `_Py_InitCleanup`, `Python/specialize.c`. -/
def initCleanupCode : Code :=
  { name := "__init__", flags := coOptimized, stacksize := 2, instrs := #[
      { op := .EXIT_INIT_CHECK, arg := 0 }, { op := .RETURN_VALUE, arg := 0 },
      { op := .RESUME, arg := 0 }] }

/-- Builtin functions visible in `builtins` in the model. -/
def builtinFunctions : List String :=
  ["print", "len", "repr", "iter", "next", "abs", "min", "max", "sum", "sorted", "any", "all",
   "isinstance", "issubclass", "getattr", "setattr", "delattr", "hasattr", "callable", "hash",
   "ord", "chr", "divmod", "pow", "__build_class__", "format", "id"]

def builtinTypes : List String :=
  ["int", "float", "str", "bool", "list", "tuple", "set", "frozenset", "dict", "range", "slice",
   "object", "type", "super", "property", "staticmethod", "classmethod", "enumerate", "zip", "map",
   "filter", "reversed", "bytes"]

def builtinExceptions : List String :=
  ["BaseException", "Exception", "ArithmeticError", "AssertionError", "AttributeError",
   "BaseExceptionGroup", "BufferError", "EOFError", "ExceptionGroup", "FloatingPointError",
   "GeneratorExit", "ImportError", "IndexError", "KeyError", "KeyboardInterrupt", "LookupError",
   "MemoryError", "ModuleNotFoundError", "NameError", "NotImplementedError", "OSError",
   "OverflowError", "RecursionError", "ReferenceError", "RuntimeError", "StopAsyncIteration",
   "StopIteration", "SyntaxError", "SystemError", "SystemExit", "TimeoutError", "TypeError",
   "UnboundLocalError", "UnicodeError", "ValueError", "Warning", "UserWarning",
   "DeprecationWarning", "RuntimeWarning", "ZeroDivisionError"]

/-- The `builtins` dict. -/
def initBuiltins : RM Val := do
  let d ← mkDict
  for n in builtinFunctions do dictSetStr d n (.builtin n)
  for n in builtinTypes ++ builtinExceptions do dictSetStr d n (.cls n)
  dictSetStr d "None" .none
  dictSetStr d "True" (.bool true)
  dictSetStr d "False" (.bool false)
  dictSetStr d "NotImplemented" .notImpl
  dictSetStr d "Ellipsis" .ellipsis
  pure d

/-- `PyEval_EvalCode`, `Python/ceval.c:957-987`, on a fresh interpreter. -/
def runMain (fuel : Nat) (P : Program) (main : Nat) : RM Val := do
  let builtins ← initBuiltins
  let globals ← mkDict
  dictSetStr globals "__name__" (.str "__main__")
  dictSetStr globals "__builtins__" builtins
  let co ← getCodeR P main
  let f ← alloc (.func { code := main, globals := globals, builtins := builtins,
                         name := co.name, qualname := co.name })
  let om := builtinOM P
  let ctx : Ctx := { evalFrame := evalFrame P om fuel }
  evalVector P ctx f globals [] []

/-- `str(exc)`, or a description for a non-Python stop. -/
def describe (fuel : Nat) (P : Program) (v : Val) : RM (String × String) := do
  let om := builtinOM P
  let ctx : Ctx := { evalFrame := evalFrame P om fuel }
  let t ← tpName v
  match ← om.str ctx v with
  | .str s => pure (t, s)
  | _ => pure (t, "")

/-- Run a dumped module. -/
def runProgram (j : Json) (transform : Program → Program) : Except String Json := do
  let codes ← (← field j "codes").getArr?
  let main ← getNat j "main"
  let fuel := (getNat j "fuel" |>.toOption).getD 3000000
  let parsed ← codes.mapM loadCode
  -- constants go on the heap first
  let loadAll : RM (Array Code) := parsed.mapM fun (c, cs) => do
    let vals ← cs.mapM (loadConst 16)
    pure { c with consts := vals }
  match loadAll {} with
  | .error (.fault m) _ => throw s!"load: {m}"
  | .error _ _ => throw "load failed"
  | .ok cs rt =>
    let P : Program := transform (#[trampolineCode, initCleanupCode] ++ cs)
    let rt := match (getNat j "reclimit" |>.toOption) with
      | some n => { rt with pyRecursionRemaining := n, recursionLimit := n }
      | none => rt
    let out (rt : Rt) (e : Json) : Json :=
      Json.mkObj [("ok", Json.mkObj [("out", toJson (String.join rt.out.toList)), ("exc", e)])]
    match runMain fuel P (main + 2) rt with
    | .ok _ rt => pure (out rt .null)
    | .error (.exc v) rt =>
      match describe fuel P v rt with
      | .ok (t, m) rt' => pure (out rt' (Json.arr #[toJson t, toJson m]))
      | .error _ _ => throw "cannot describe the exception"
    | .error (.fault m) _ => throw s!"fault: {m}"
    | .error .fuel _ => throw "fuel"
    | .error _ _ => throw "stray control flow"

def run (fn : String) (j : Json) : Except String Json :=
  match fn with
  | "run" => runProgram j id
  | "table" => do
    let t ← natArr j "table"
    let i ← getNat j "index"
    match getExceptionHandler t i with
    | some (h, l, la) => pure (Json.mkObj [("ok", Json.arr #[toJson h, toJson l, toJson la])])
    | none => pure (Json.mkObj [("ok", Json.null)])
  | "effect" => do
    let o ← getNat j "opcode"
    let a ← getNat j "oparg"
    match Op.ofNat? o with
    | some op => pure (Json.mkObj [("ok", Json.arr #[toJson (numPopped op a), toJson (numPushed op a),
        toJson (Op.deopt op).toNat, toJson (Uop.instrSize op)])])
    | none => throw "unknown opcode"
  | _ => throw s!"unknown fn {fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.Bytecode
