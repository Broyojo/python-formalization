import Lean.Data.Json
import PyLean.DiffCore
import PyLean.Bytecode.GenObj.Script

/-!
Differential-testing entry points for `Objects/genobject.c`
(`fn` names start with `gen_`; driver: `difftest/bytecode_gen_diff.py`).
-/

namespace PyLean.Bytecode.GenObj

open Lean PyLean PyLean.Diff
open PyLean.Bytecode.GenObj.Script

abbrev EJ := Except String

def arr (j : Json) : EJ (List Json) := do
  match j with
  | .arr a => pure a.toList
  | _ => throw "expected array"

def jstr (j : Json) : EJ String := j.getStr?
def jnat (j : Json) : EJ Nat := j.getNat?
def jint (j : Json) : EJ Int := j.getInt?

def parseReOp (j : Json) : EJ ReOp := do
  match ← arr j with
  | [t] =>
    match ← jstr t with
    | "next" => pure .next
    | "close" => pure .close
    | "flags" => pure .flags
    | "anext" => pure .anext
    | "aclose" => pure .aclose
    | s => throw s!"bad reop {s}"
  | [t, a] =>
    match ← jstr t with
    | "send" => pure (.send (← jint a))
    | "throw" => pure (.throw (← jstr a))
    | "asend" => pure (.asend (← jint a))
    | "athrow" => pure (.athrow (← jstr a))
    | "hsend" => pure (.heldSend (← jnat a))
    | "hclose" => pure (.heldClose (← jnat a))
    | s => throw s!"bad reop {s}"
  | [t, a, b] =>
    match ← jstr t with
    | "hthrow" => pure (.heldThrow (← jnat a) (← jstr b))
    | s => throw s!"bad reop {s}"
  | _ => throw "bad reop"

mutual
  partial def parseAct (j : Json) : EJ Act := do
    match ← arr j with
    | t :: rest =>
      match ← jstr t, rest with
      | "y", [v] => pure (.yld (← jint v))
      | "yf", [s] => pure (.yldFrom (← parseSub s))
      | "ret", [.null] => pure (.ret none)
      | "ret", [v] => pure (.ret (some (← jint v)))
      | "raise", [c] => pure (.raise (← jstr c))
      | "try", [b, c, hd] => pure (.tryExc (← parseBody b) (← jstr c) (← parseBody hd))
      | "fin", [b, f] => pure (.tryFin (← parseBody b) (← parseBody f))
      | "loop", [n, b] => pure (.loop (← jnat n) (← parseBody b))
      | "re", [op, s] => pure (.reent (← parseReOp op) (← s.getBool?))
      | s, _ => throw s!"bad act {s}"
    | [] => throw "empty act"

  partial def parseBody (j : Json) : EJ (List Act) := do
    (← arr j).mapM parseAct

  partial def parseSub (j : Json) : EJ Sub := do
    match ← arr j with
    | t :: rest =>
      match ← jstr t, rest with
      | "s", [b] => pure (.script (← parseBody b))
      | "c", [b] => pure (.iterCoro (← parseBody b))
      | "bad", [k] => pure (.badAwait (← jnat k))
      | "f", [i, r, hs, tb, cb, re] =>
        pure (.foreign
          { items := ← jnat i
            retv := ← (match r with | .null => pure none | v => some <$> jint v)
            hasSend := ← hs.getBool?
            throwB := ← jnat tb
            closeB := ← jnat cb
            reent := ← (match re with | .null => pure none | v => some <$> jnat v) })
      | s, _ => throw s!"bad sub {s}"
    | [] => throw "empty sub"
end

def parseKind (s : String) : EJ GenKind :=
  match s with
  | "gen" => pure .gen
  | "coro" => pure .coro
  | "agen" => pure .asyncGen
  | _ => throw s!"bad kind {s}"

/-- A value argument: `null` is `None`, an int is an int, a string a string. -/
def parseArg (j : Json) : EJ O :=
  match j with
  | .null => pure .none
  | .str s => pure (.str s)
  | v => do pure (.other (.int (← jint v)))

/-- An argument of `throw()`. -/
def parseThrowArg (j : Json) : EJ O := do
  match ← arr j with
  | [t] =>
    match ← jstr t with
    | "none" => pure .none
    | "tb" => pure .traceback
    | "junk" => pure (.other (.int 42))
    | s => throw s!"bad throw arg {s}"
  | [t, a] =>
    match ← jstr t with
    | "cls" => let c ← jstr a; pure (.excClass (kindOfClass c) c)
    | "str" => pure (.str (← jstr a))
    | "int" => pure (.other (.int (← jint a)))
    | s => throw s!"bad throw arg {s}"
  | [t, a, m] =>
    match ← jstr t with
    | "inst" =>
      let c ← jstr a
      let e := raised c (← jstr m)
      pure e.toObj
    | s => throw s!"bad throw arg {s}"
  | _ => throw "bad throw arg"

def parseThrowArgs (j : Json) : EJ (List O) := do (← arr j).mapM parseThrowArg

def encRet : Ret SV → Json
  | .ok v => toJson ["ok", renderObj v]
  | .err none => toJson ["null"]
  | .err (some e) => toJson ["exc", e.cls, excStr e, renderObj e.value]

def encStatus (w : W) : CStatus SV → W × Json
  | .fail e => (w, encRet (.err e))
  | .ok => (w, toJson ["ok", "<aw>"])

/-- `yf`/`cr_await`/`ag_await`, or "None". -/
def yfRender (g : GenObj SV) : String := renderObj (genGetYieldFrom g)

/-- `inspect.getgeneratorstate` (`Lib/inspect.py`), and its two siblings. -/
def stateName (w : W) (r : Ref) : String :=
  let g := w.get r
  let prefix_ := match g.kind with | .gen => "GEN" | .coro => "CORO" | .asyncGen => "AGEN"
  if runningFlag w r then prefix_ ++ "_RUNNING"
  else if genGetSuspended g then prefix_ ++ "_SUSPENDED"
  else if g.state.finished then prefix_ ++ "_CLOSED"
  else prefix_ ++ "_CREATED"

def encFlags (w : W) (r : Ref) : Json :=
  let g := w.get r
  toJson [toJson (runningFlag w r), toJson (genGetSuspended g),
          toJson (g.state.finished), toJson (yfRender g), toJson (stateName w r)]

def nextConv : W × Ret SV → W × Ret SV
  | (w, .err none) => (w, .err (some Exc.stopIterationNone))
  | res => res

def heldAt (w : W) (i : Nat) : Option (Bool × Ref) := w.ext.held[i]?

def addHeld (w : W) (isAsend : Bool) (a : Ref) : W :=
  { w with ext.held := w.ext.held ++ [(isAsend, a)] }

/-- One driver operation on the top object; `none` means this case ended. -/
def runOp (w : W) (op : Json) : EJ (W × Json) := do
  let h := hooksAt depth
  let n := depth
  let r : Ref := 0
  let ret := fun (p : W × Ret SV) => (p.1, encRet p.2)
  match ← arr op with
  | t :: rest =>
    match ← jstr t, rest with
    | "next", [] => pure (ret (nextCall h w r))
    | "send", [a] => pure (ret (genSend h w r (some (← parseArg a))))
    | "close", [] => pure (ret (genCloseF h n w r))
    | "throw", [as] => pure (ret (genThrow h n w r (← parseThrowArgs as)))
    | "cw_next", [] => pure (ret (nextConv (coroWrapperIternext h w r)))
    | "cw_send", [a] => pure (ret (coroWrapperSend h w r (← parseArg a)))
    | "cw_throw", [as] => pure (ret (coroWrapperThrow h n w r (← parseThrowArgs as)))
    | "cw_close", [] => pure (ret (coroWrapperClose h n w r))
    | "new_anext", [] =>
      let (w0, a) := allocAw w
      match asyncGenAnext h w0 r a with
      | (w1, .ok) => pure (encStatus (addHeld w1 true a) .ok)
      | (w1, e) => pure (encStatus w1 e)
    | "new_asend", [v] =>
      let (w0, a) := allocAw w
      match asyncGenAsend h w0 r a (← parseArg v) with
      | (w1, .ok) => pure (encStatus (addHeld w1 true a) .ok)
      | (w1, e) => pure (encStatus w1 e)
    | "new_aclose", [] =>
      let (w0, a) := allocAw w
      match asyncGenAclose h w0 r a with
      | (w1, .ok) => pure (encStatus (addHeld w1 false a) .ok)
      | (w1, e) => pure (encStatus w1 e)
    | "new_athrow", [as] =>
      let (w0, a) := allocAw w
      match asyncGenAthrow h w0 r a (← parseThrowArgs as) with
      | (w1, .ok) => pure (encStatus (addHeld w1 false a) .ok)
      | (w1, e) => pure (encStatus w1 e)
    | "aw_next", [i] =>
      match heldAt w (← jnat i) with
      | some (true, a) => pure (ret (nextConvA (asyncGenAsendIternext h w a)))
      | some (false, a) => pure (ret (nextConvA (asyncGenAthrowIternext h n w a)))
      | none => pure (w, toJson ["skip"])
    | "aw_send", [i, v] =>
      match heldAt w (← jnat i) with
      | some (true, a) => pure (ret (asyncGenAsendSend h w a (some (← parseArg v))))
      | some (false, a) => pure (ret (asyncGenAthrowSend h n w a (← parseArg v)))
      | none => pure (w, toJson ["skip"])
    | "aw_throw", [i, as] =>
      match heldAt w (← jnat i) with
      | some (true, a) => pure (ret (asyncGenAsendThrow h n w a (← parseThrowArgs as)))
      | some (false, a) => pure (ret (asyncGenAthrowThrow h n w a (← parseThrowArgs as)))
      | none => pure (w, toJson ["skip"])
    | "aw_close", [i] =>
      match heldAt w (← jnat i) with
      | some (true, a) => pure (ret (asyncGenAsendClose h n w a))
      | some (false, a) => pure (ret (asyncGenAthrowClose h n w a))
      | none => pure (w, toJson ["skip"])
    | "del", [] =>
      let w1 := w.ext.held.foldl (fun w (p : Bool × Ref) =>
        if p.1 then asyncGenAsendFinalize h w p.2 else asyncGenAthrowFinalize h w p.2) w
      pure ({ genFinalize h n w1 r with ext.top := 0 }, toJson ["ok", "None"])
    | s, _ => throw s!"bad op {s}"
  | [] => throw "empty op"
where
  nextConvA (p : W × Ret SV) : W × Ret SV := nextConv p

def runDrive (j : Json) : EJ Json := do
  let kind ← parseKind (← getStr j "kind")
  let body ← parseBody (← field j "body")
  let ops ← arr (← field j "ops")
  let warnErr ← getBool j "warnerr"
  let w0 := initialWorld kind body warnErr (← getNat j "firstiter") (← getNat j "finalizer")
  let mut w := w0
  let mut out : Array Json := #[]
  for op in ops do
    let (w1, res) ← runOp w op
    w := w1
    let gone := (← arr op).head?.bind (fun t => t.getStr?.toOption) == some "del"
    out := out.push (toJson [res, if gone then toJson "gone" else encFlags w 0])
  return Json.mkObj [("ok", Json.mkObj
    [("steps", Json.arr out), ("trace", toJson w.ext.trace.reverse)])]

/-- Name getter and setter sequences on a fresh object. -/
def runNames (j : Json) : EJ Json := do
  let kind ← parseKind (← getStr j "kind")
  let code := codeFor kind
  let g : GenObj SV := pyGenNewWithKind kind code
  let w0 : W := (initialWorld kind [] false 0 0).set 0 g
  let mut w := w0
  let mut out : Array Json := #[]
  for op in ← arr (← field j "ops") do
    match ← arr op with
    | [t, v] =>
      let value : Option O ← (match v with
        | .null => pure none
        | .str s => pure (some (.str s))
        | i => do pure (some (.other (.int (← jint i)))))
      let st ← (match ← jstr t with
        | "name" => pure (genSetName w 0 value)
        | "qualname" => pure (genSetQualname w 0 value)
        | s => throw s!"bad op {s}")
      w := st.1
      out := out.push (match st.2 with
        | .ok => toJson ["ok"]
        | .fail e => encRet (.err e))
      out := out.push (toJson [renderObj (genGetName (w.get 0)), renderObj (genGetQualname (w.get 0))])
    | _ => throw "bad op"
  return Json.mkObj [("ok", Json.arr out)]
where
  pyGenNewWithKind (kind : GenKind) (code : Code) : GenObj SV :=
    genNewWithQualname kind code (some (.str "f")) (some (.str "f"))

/-- `compute_cr_origin` and `_Py_MakeCoro`'s use of it. The stack is `n` frames
named `f`, then the thread's frames. -/
def runOrigin (j : Json) : EJ Json := do
  let d ← getNat j "depth"
  let n ← getNat j "frames"
  let stack : List (String × Nat × String) :=
    (List.replicate n ("", 0, "f")) ++
      [("", 0, "target"), ("", 0, "run"), ("", 0, "_bootstrap_inner"), ("", 0, "_bootstrap")]
  let w : W := { initialWorld .coro [] false 0 0 with originDepth := d, callStack := stack }
  match pyMakeCoro w (codeFor .coro) (.str "f") (.str "f") with
  | some g =>
    match g.origin with
    | some o => return Json.mkObj [("ok", toJson (o.map (·.2.2)))]
    | none => return Json.mkObj [("ok", Json.null)]
  | none => throw "no object"

/-- Which object the `co_flags` select, and its initial state after
`RETURN_GENERATOR`. -/
def runMake (j : Json) : EJ Json := do
  let kind ← parseKind (← getStr j "kind")
  let w := initialWorld kind [] false 0 0
  let name ← getStr j "name"
  let qual ← getStr j "qualname"
  match pyMakeCoro w (codeFor kind) (.str name) (.str qual) with
  | some g =>
    let g' := { g with state := .created }
    return Json.mkObj [("ok", toJson
      [toJson (reprPrefix g'.kind), toJson (renderObj (genGetName g')),
       toJson (renderObj (genGetQualname g')), toJson (genGetRunning g'),
       toJson (genGetSuspended g'), toJson g'.state.finished,
       toJson (genRepr g' "ADDR" (renderObj g'.qualname))])]
  | none => throw "no object"

def genBase : Nat := 152

def runSizeof (j : Json) : EJ Json := do
  let code : Code := { nlocalsplus := ← getNat j "nlocals", stacksize := ← getNat j "stacksize" }
  let g : GenObj SV := { code := code }
  return Json.mkObj [("ok", toJson (genSizeof genBase g))]

def run? (fn : String) (j : Json) : Option (Except String Json) :=
  match fn with
  | "gen_drive" => some (runDrive j)
  | "gen_names" => some (runNames j)
  | "gen_origin" => some (runOrigin j)
  | "gen_make" => some (runMake j)
  | "gen_sizeof" => some (runSizeof j)
  | _ => none

end PyLean.Bytecode.GenObj
