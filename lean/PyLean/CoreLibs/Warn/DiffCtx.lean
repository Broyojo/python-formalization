import PyLean.CoreLibs.Warn.DiffOps
import PyLean.CoreLibs.Warn.Context

/-! `warn.ctx` cases: a script of `catch_warnings` objects entered and exited, warnings shown
through `_showwarnmsg`, `simplefilter` calls and `showwarning` reassignments, in either context
mode, run in a copy of the current `contextvars` context. Logs are numbered in the order they are
first seen (returned by `__enter__`, or receiving a warning). -/

namespace PyLean.CoreLibs.Warn

open Lean PyLean PyLean.Diff PyLean.CoreLibs.Misc

def pFnShow (s : String) : Option Fn :=
  match s with
  | "orig" => some .showOrig
  | "user" => some (.user 1)
  | "userraise" => some (.userRaises 1 (.valueError "hook failed"))
  | "noncallable" => some .noncallable
  | _ => none

def pFnImpl (s : String) : Fn :=
  match s with
  | "user" => .user 2
  | "userraise" => .userRaises 2 (.valueError "hook failed")
  | "noncallable" => .noncallable
  | _ => .implOrig

instance : Inhabited CW := ⟨cwInit "" false 0 none 0 (.int 0) false⟩

/-- Module ids: 0 the `warnings` module, 1 another module; their `repr`s as the harness writes them. -/
def dModRepr (m : Nat) : String := if m = 0 then "<W>" else "<X>"

def jPyStr (r : Py String) : Json :=
  match r with
  | .ok s => Json.arr #["ok", jStr s]
  | .error e => jRes (α := Unit) (.error e)

structure CtxRun where
  st : MState
  cws : Array CW
  seen : Array Ref

def seqId (seen : Array Ref) (l : Ref) : Array Ref × Nat :=
  match seen.findIdx? (· = l) with
  | some i => (seen, i)
  | none => (seen.push l, seen.size)

/-- `sys.modules['warnings']` during a `repr`: as usual, missing, or another module. -/
def sysW (v : String) : Option Nat :=
  match v with
  | "nosys" => none
  | "swap" => some 1
  | _ => some 0

def ctxOp (use : Bool) (op : Json) (R : CtxRun) : Except String (CtxRun × Json) := do
  let k ← jStrAt op 0
  match k with
  | "new" =>
    let a : Option ActA ← match ← jGetI op 2 with
      | .null => pure none
      -- `action=None` is the default: no filter
      | .arr #[.str "o", .str "None"] => pure none
      | v => some <$> pAct v
    let cw := cwInit "catch_warnings" (← jBoolAt op 1) 0 a (← jNatAt op 3) (← pIntA (← jGetI op 4))
      (← jBoolAt op 5)
    return ({ R with cws := R.cws.push cw }, Json.arr #["ok"])
  | "enter" =>
    let i ← jNatAt op 1
    let cw := R.cws[i]!
    let (cw', st', r) := cwEnter use cw R.st
    let R := { R with cws := R.cws.set! i cw', st := st' }
    match r with
    | .error e => return (R, jRes (α := Unit) (.error e))
    | .ok none => return (R, Json.arr #["ok", .null])
    | .ok (some l) =>
      let (seen, n) := seqId R.seen l
      return ({ R with seen := seen }, Json.arr #["ok", toJson n])
  | "exit" =>
    let i ← jNatAt op 1
    let (st', r) := cwExit use R.cws[i]! R.st
    return ({ R with st := st' }, jRes r)
  | "show" =>
    let m ← jNatAt op 1
    let st0 := { R.st with out := [] }
    match showwarnmsg use m st0 with
    | .error e => return (R, jRes (α := Unit) (.error e))
    | .ok st' =>
      let st' := { st' with out := R.st.out ++ st'.out }
      let R := { R with st := st' }
      match st'.out.getLast? with
      | some (.logged l) =>
        let (seen, n) := seqId R.seen l
        return ({ R with seen := seen }, Json.arr #["ok", Json.arr #["log", toJson n]])
      | some .written => return (R, Json.arr #["ok", Json.arr #["written"]])
      | some (.hook i) => return (R, Json.arr #["ok", Json.arr #["hook", toJson i]])
      | _ => return (R, Json.arr #["ok", Json.arr #["lost"]])
  | "sf" =>
    let fs := curFState use R.st
    match simplefilter R.st.hier (← pAct (← jGetI op 1)) (← jNatAt op 2) (← pIntA (← jGetI op 3)) (← jBoolAt op 4) fs with
    | .error e => return (R, jRes (α := Unit) (.error e))
    | .ok fs' => return ({ R with st := putFState use R.st fs' }, Json.arr #["ok"])
  | "setshow" =>
    return ({ R with st := { R.st with showwarning := pFnShow (← jStrAt op 1) } }, Json.arr #["ok"])
  | "mrepr" =>
    -- catch_warnings(module=<other module>, record=...), then repr under the variant
    let cw := cwInit "catch_warnings" (← jBoolAt op 1) 1 none 0 (.int 0) false
    return (R, jPyStr (cwRepr cw (sysW (← jStrAt op 2)) dModRepr))
  | _ => return (R, jPyStr (cwRepr R.cws[(← jNatAt op 1)]! (sysW (← jStrAt op 2)) dModRepr))

def runCtx (j : Json) : Except String Json := do
  let use ← (← j.getObjVal? "use").getBool?
  let init ← (← jArr (← j.getObjVal? "filters")).mapM pElem
  let stderr : Option (Py Unit) := match ← (← j.getObjVal? "stderr").getStr? with
    | "none" => none
    | "oserr" => some (.error (.named "OSError" "write failed"))
    | "keyerr" => some (.error (.keyError "'write failed'"))
    | "brokenpipe" => some (.error (.named "BrokenPipeError" "write failed"))
    | "unsupported" => some (.error (.named "UnsupportedOperation" "write failed"))
    | "myoserr" => some (.error (.named "MyOSError" "write failed"))
    | _ => some (.ok ())
  let sw := pFnShow (← (← j.getObjVal? "show").getStr?)
  let im := pFnImpl (← (← j.getObjVal? "impl").getStr?)
  let fmt : Option Fn := match j.getObjVal? "fmt" with
    | .ok (.str "raise") => some (.userRaises 3 (.valueError "fmt failed"))
    | _ => some .fmtOrig
  let st : MState := MState.mk (fun i => if i = 0 then init else []) (fun _ => []) 1 (some 0) sw im
    fmt 0 .unset (fun _ => ⟨0, none⟩) stderr [] (fun _ => false) dHier (some 0) dModRepr
  let mut R : CtxRun := ⟨st, #[], #[]⟩
  let mut outs : Array Json := #[]
  for op in ← jArr (← j.getObjVal? "ops") do
    let (R', o) ← ctxOp use op R
    R := R'
    outs := outs.push o
  let st := R.st
  let swk : Json := match st.showwarning with
    | none => jStr "deleted"
    | some .showOrig => jStr "orig"
    | some (.user _) => jStr "user"
    | some (.userRaises _ _) => jStr "userraise"
    | some .noncallable => jStr "noncallable"
    | some _ => jStr "other"
  let (seen, impk) : Array Ref × Json := match st.showImpl with
    | .implOrig => (R.seen, jStr "orig")
    | .noncallable => (R.seen, jStr "noncallable")
    | .logAppend l => let (s, n) := seqId R.seen l; (s, Json.arr #["log", toJson n])
    | .userRaises _ _ => (R.seen, jStr "userraise")
    | _ => (R.seen, jStr "user")
  let logs := seen.toList.map fun l => Json.arr ((st.logs l).map (fun m => jStr (toString m))).toArray
  let final := Json.arr #[Json.arr ((getFilters use st).map jElem).toArray, jBool (st.filters == some 0),
    swk, impk, jInt st.ver, Json.arr logs.toArray]
  return Json.mkObj [("ok", Json.arr #[Json.arr outs, final])]

def ctxHandler : Handler := fun fn j =>
  match fn with
  | "ctx" => some (runCtx j)
  | _ => none

end PyLean.CoreLibs.Warn
