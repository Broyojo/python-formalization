import PyLean.DiffCore
import PyLean.Bytecode.Specialize
import PyLean.Bytecode.FrameObj
import PyLean.Bytecode.IterObj
import PyLean.Bytecode.GenObj.Diff

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

/-- `_Py_INTERPRETER_TRAMPOLINE_INSTRUCTIONS`, `Python/ceval.c:1047-1056`. -/
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

/-- `PyEval_EvalCode`, `Python/ceval.c:674-704`, on a fresh interpreter. -/
def runMainWith (ev : Frame → Option Val → RM Val) (P : Program) (main : Nat) : RM Val := do
  let builtins ← initBuiltins
  let globals ← mkDict
  dictSetStr globals "__name__" (.str "__main__")
  dictSetStr globals "__builtins__" builtins
  let co ← getCodeR P main
  let f ← alloc (.func { code := main, globals := globals, builtins := builtins,
                         name := co.name, qualname := co.name })
  evalVector P { evalFrame := ev } f globals [] []

def runMain (fuel : Nat) (P : Program) (main : Nat) : RM Val :=
  runMainWith (evalFrame P (builtinOM P) fuel) P main

/-- Note what the specializer would do at the instruction about to execute. -/
def recordProfile (P : Program) (s : St) : St :=
  let c := s.regs.frame.code
  let ip := s.regs.next
  match P[c]? with
  | none => s
  | some co =>
    let filled := match s.regs.rt.profile[c]? with
      | some row => (row[ip]?.join).isSome
      | none => true
    let afterExtended := ip != 0 && (co.instrs[ip - 1]?.map (·.op)) == some .EXTENDED_ARG
    if filled || afterExtended then s
    else
      match co.instrs[ip]? with
      | none => s
      | some i =>
        match suggest P co i (co.instrs[ip + Uop.instrSize i.op]?) s.regs.frame s.stack s.regs.rt with
        | .ok (some i') _ =>
          let rt := s.regs.rt
          let row := (rt.profile.getD c #[]).setIfInBounds ip (some i')
          { s with regs := { s.regs with rt := { rt with profile := rt.profile.setIfInBounds c row } } }
        | _ => s

/-- `runLoop` with `recordProfile` before each instruction. -/
def runLoopP (P : Program) (om : ObjModel) : Nat → St → EStateM.Result Err Rt Val
  | 0, s => .error .fuel s.regs.rt
  | n + 1, s =>
    let s := recordProfile P s
    let ctx : Ctx := { evalFrame := evalWith P (runLoopP P om n) }
    match afterInstr P (stepInstr P om ctx s 6 0) with
    | .cont s' => runLoopP P om n s'
    | .ret v rt => .ok v rt
    | .raised v rt => .error (.exc v) rt
    | .stop e rt => .error e rt

/-- Rewrite each instruction the profile has an answer for. -/
def applyProfile (P : Program) (prof : Array (Array (Option Instr))) : Program :=
  (P.zipIdx).map fun (co, c) =>
    match prof[c]? with
    | none => co
    | some row =>
      { co with instrs := (co.instrs.zipIdx).map fun (i, ip) =>
          match row[ip]? with
          | some (some i') => i'
          | _ => i }

/-- `str(exc)`, or a description for a non-Python stop. -/
def describe (fuel : Nat) (P : Program) (v : Val) : RM (String × String) := do
  let om := builtinOM P
  let ctx : Ctx := { evalFrame := evalFrame P om fuel }
  let t ← tpName v
  match ← om.str ctx v with
  | .str s => pure (t, s)
  | _ => pure (t, "")

/-- Run a dumped module; with `quick`, profile a first run and report the run of
the specialized program. -/
def runProgram (j : Json) (quick : Bool) : Except String Json := do
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
    let P : Program := #[trampolineCode, initCleanupCode] ++ cs
    let rt := match (getNat j "reclimit" |>.toOption) with
      | some n => { rt with pyRecursionRemaining := n, recursionLimit := n }
      | none => rt
    let P ← if quick then do
        let rt1 := { rt with profile := P.map fun c => Array.replicate c.instrs.size none }
        match runMainWith (evalWith P (runLoopP P (builtinOM P) fuel)) P (main + 2) rt1 with
        | .ok _ r | .error (.exc _) r => pure (applyProfile P r.profile)
        | .error _ _ => pure P
      else pure P
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

/-- `fn = "frame_jump"`: `frame_lineno_set_impl` on a dumped function. -/
def runFrameJump (j : Json) : Except String Json := do
  let code ← (← field j "code").getArr?
  let units ← code.mapM fun u => do
    let op ← (u.getArrVal? 0 >>= (·.getNat?))
    let arg ← (u.getArrVal? 1 >>= (·.getNat?))
    match Op.ofNat? op with
    | some o => pure ({ op := o, arg := arg } : FrameObj.Unit')
    | none => throw s!"unknown opcode {op}"
  let table ← natArr j "table"
  let lines ← (← field j "lines").getArr?
  let lines ← lines.mapM (·.getInt?)
  let first ← getInt j "first"
  let value ← getInt j "value"
  let lasti ← getNat j "lasti"
  match FrameObj.linenoDecide units table lines first value lasti with
  | .error m => pure (Json.mkObj [("ok", Json.arr #[toJson "err", toJson m])])
  | .ok addr _ => pure (Json.mkObj [("ok", Json.arr #[toJson "ok", toJson addr])])

/-- `fn = "iter_seq"`: a script of `next`/`__length_hint__`/`__setstate__`/`__reduce__`
on `iter(seq)` or `reversed(seq)`. -/
def runIterSeq (j : Json) : Except String Json := do
  let script ← (← field j "script").getArr?
  let script ← script.mapM (·.getInt?)
  let ops ← (← field j "ops").getArr?
  let rev ← getBool j "rev"
  let getitem (i : Int) : Py Int :=
    if i < 0 then .error (.indexError "out") else
    match (script[i.toNat]?).getD (-1) with
    | -1 => .error (.indexError "out")
    | -2 => .error .stopIteration
    | -3 => .error (.valueError "v")
    | a => .ok a
  let enc : Py (Option Int) → Json
    | .ok (some v) => toJson v
    | .ok none => toJson "stop"
    | .error e => toJson e.className
  let size : Py Int := .ok script.size
  let mut it : IterObj.SeqIter := IterObj.seqIterNew
  let mut ro : IterObj.Rev := IterObj.revNew script.size
  let mut out : Array Json := #[]
  for o in ops do
    let op ← (o.getArrVal? 0 >>= (·.getStr?))
    let arg ← (o.getArrVal? 1 >>= (·.getInt?))
    match op, rev with
    | "next", false =>
      let (it', r) := IterObj.iterIternext getitem it
      it := it'
      out := out.push (enc r)
    | "next", true =>
      let (ro', r) := IterObj.revNext getitem ro
      ro := ro'
      out := out.push (enc r)
    | "hint", false =>
      out := out.push (match IterObj.iterLen (some size) it with
        | .ok (some v) => toJson v
        | _ => Json.null)
    | "hint", true =>
      out := out.push (match IterObj.revLen size ro with
        | .ok v => toJson v
        | .error e => toJson e.className)
    | "set", false =>
      it := IterObj.iterSetstate it arg
      out := out.push (toJson "set")
    | "set", true =>
      match IterObj.revSetstate size ro arg with
      | .ok r => ro := r
      | .error _ => pure ()
      out := out.push (toJson "set")
    | _, false =>
      out := out.push (match IterObj.iterReduce it with
        | some v => toJson v
        | none => Json.null)
    | _, true =>
      out := out.push (match IterObj.revReduce ro with
        | some v => toJson v
        | none => Json.null)
  pure (Json.mkObj [("ok", Json.arr out)])

/-- `fn = "enum_counts"`: indices of `enumerate(start)` and the pickled count. -/
def runEnum (j : Json) : Except String Json := do
  let start ← match (← getStr j "start").toInt? with
    | some i => pure i
    | none => throw "start"
  let n ← getNat j "n"
  let e0 := IterObj.enumNew start
  let idx := IterObj.enumIndices n e0
  let en := (List.range n).foldl (fun e _ => (IterObj.enumNext e).1) e0
  pure (Json.mkObj [("ok", Json.arr #[Json.arr (idx.map (fun i => toJson (toString i))).toArray,
    toJson (toString (IterObj.enumReduce en))])])

/-- `fn = "cell_cmp"`: the six comparisons of two cells of ints. -/
def runCell (j : Json) : Except String Json := do
  let get (k : String) : Except String (Option Int) := getOptInt j k
  let a ← get "a"
  let b ← get "b"
  let cmp (x y : Int) (op : Nat) : Py Bool := .ok (match op with
    | 0 => decide (x < y) | 1 => decide (x ≤ y) | 2 => decide (x = y)
    | 3 => decide (x ≠ y) | 4 => decide (x > y) | _ => decide (x ≥ y))
  let rs := (List.range 6).map fun op =>
    match IterObj.cellCompare cmp id a b op with
    | .ok r => toJson r
    | .error _ => Json.null
  pure (Json.mkObj [("ok", Json.arr rs.toArray)])

def run (fn : String) (j : Json) : Except String Json :=
  match fn with
  | "frame_jump" => runFrameJump j
  | "iter_seq" => runIterSeq j
  | "enum_counts" => runEnum j
  | "cell_cmp" => runCell j
  | "run" => runProgram j false
  | "quick" => runProgram j true
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
  | _ =>
    match GenObj.run? fn j with
    | some r => r
    | none => throw s!"unknown fn {fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.Bytecode
