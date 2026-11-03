import PyLean.CoreLibs.Misc.Common
import PyLean.CoreLibs.Warn.WarnCall
import PyLean.CoreLibs.Warn.Context
import PyLean.CoreLibs.Warn.DiffWe

/-! `warn.call_c` and `warn.call_py` cases: one `warnings.warn` call from a generated stack of
frames, run in a new thread so that the generated frames are the whole stack; empty filters and
the `default` action. Globals `0..k-1` are generated, `k` is `sys.__dict__`, `k+1` the Python
twin's own module (its `warn` frame, token `PYW`, is at line 505). -/

namespace PyLean.CoreLibs.Warn

open Lean PyLean PyLean.Diff PyLean.CoreLibs.Misc

def pGlob (j : Json) : Except String Globals := do
  let name : NameV := match ← jStrAt j 0 with
    | "m" => .str "m"
    | "n" => .str "n"
    | "none" => .none
    | "obj" => .obj
    | _ => .missing
  let reg : RegV := match ← jStrAt j 1 with
    | "empty" => .dict []
    | "stale" => .dict [(.version, exactInt (VER - 1))]
    | "none" => .none
    | "obj" => .obj
    | _ => .missing
  return ⟨name, reg⟩

def pCatA (j : Json) : Except String CatA := do
  match ← jStrAt j 0 with
  | "none" => return .none
  | "c" =>
    match ← jNatAt j 1 with
    | 1 => return .cls 1 "UserWarning" "UserWarning" true
    | 3 => return .cls 3 "DeprecationWarning" "DeprecationWarning" true
    | 5 => return .cls 5 "BadInit" "BadInit" true
    | 10 => return .cls 10 "int" "int" false
    | _ => return .cls 18 "OrderedDict" "collections.OrderedDict" false
  | _ =>
    match ← jStrAt j 1 with
    | "str" => return .obj "str" "str"
    | _ => return .obj "OrderedDict" "collections.OrderedDict"

def pMsgA (j : Json) : Except String MsgA := do
  match ← jStrAt j 0 with
  | "s" => return .str (← jStrAt j 1)
  | _ => return .warn (← jNatAt j 1) (← jStrAt j 2)

def pPElem (j : Json) : Except String PElem := do
  match ← jStrAt j 0 with
  | "s" => return .str (← jStrAt j 1)
  | "t" => return .tup (← (← jArr (← jGetI j 1)).mapM (fun x => x.getStr?))
  | _ => return .obj "int"

def pSkip (j : Json) : Except String SkipA := do
  match ← jStrAt j 0 with
  | "t" => return .tuple (← (← jArr (← jGetI j 1)).mapM pPElem)
  | _ => return .other "list"

def jRegV : RegV → Json
  | .missing => Json.arr #["missing"]
  | .none => Json.arr #["none"]
  | .obj => Json.arr #["obj"]
  | .dict r => Json.arr #["dict", jReg r]

def jModArg : ModArg → Json
  | .some s => jStr s
  | .none => .null
  | _ => Json.arr #["obj"]

def runCall (isC : Bool) (j : Json) : Except String Json := do
  let gs ← (← jArr (← j.getObjVal? "globals")).mapM pGlob
  let k := gs.length
  let globals : Nat → Globals := fun i =>
    if h : i < k then gs[i] else if i = k then ⟨.str "sys", .missing⟩
    else if i = k + 1 then ⟨.str "_py_warnings", .missing⟩ else ⟨.str "top", .missing⟩
  let frames ← (← jArr (← j.getObjVal? "frames")).mapM fun f => do
    return (⟨← jStrAt f 0, (← jIntAt f 2) + 2, ← jNatAt f 1⟩ : Frame)
  let W : WEnv := { frames := frames ++ [⟨"<top>", 3, k + 2⟩], self := ⟨"PYW", 505, k + 1⟩, globals := globals, sysG := k,
                    userWarning := 1,
                    mkMsg := fun c => if c = 5 then .error (.valueError "bad message") else .ok () }
  let E : Env := { isSub := isSub, isSubPy := fun _ b => b = 4, matchFilename := matchFilename,
                   showMsg := .ok () }
  let m ← pMsgA (← j.getObjVal? "msg")
  let c ← pCatA (← j.getObjVal? "cat")
  let s ← (← j.getObjVal? "sl").getInt?
  let skip ← pSkip (← j.getObjVal? "skip")
  let r := if isC then cWarn W E [] (some "default") VER [] m c s skip
    else pyWarn W E [] (some "default") VER [] m c s skip
  let sh : Json := match r.out, r.ctx with
    | .ok true, some x => Json.arr #[jStr x.filename, jInt x.lineno, jModArg x.module]
    | _, _ => .null
  let regs := (List.range (k + 3)).map fun i =>
    match r.reg with
    | some (g, r') => if g = i then jRegV (.dict r') else jRegV (globals i).reg
    | none => jRegV (globals i).reg
  return Json.mkObj [("ok", Json.arr #[encR jBool r.out, sh, Json.arr regs.toArray])]

def callHandler : Handler := fun fn j =>
  match fn with
  | "call_c" => some (runCall true j)
  | "call_py" => some (runCall false j)
  | _ => none

end PyLean.CoreLibs.Warn
