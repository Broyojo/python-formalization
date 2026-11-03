import PyLean.CoreLibs.Misc.Common
import PyLean.CoreLibs.Warn.Option

/-! `warn.filt_c`, `warn.filt_py`, `warn.opt` and `warn.defaults` cases: scripts of filters-list
operations on either twin, `-W` option lists, and the initial filters lists.

Object ids (`warn_OBJS` in `corelibs_diff.py`): 0 Warning, 1 UserWarning, 2 W1, 3
DeprecationWarning, 4 Odd, 5 BadInit, 6 PendingDeprecationWarning, 7 ImportWarning, 8
ResourceWarning, 9 RuntimeWarning, 10 int, 11 ValueError, 12 the int 5, 13 print, 14
SyntaxWarning, 15 OSError, 16 `_OptionError`, 17 `WarningMessage`. Patterns: `(` and `[` are not
valid regexes, `a{4294967296}` overflows the repetition count. Modules for `__import__`: builtins
(0), os (1), warnings (2), os.path (3). -/

namespace PyLean.CoreLibs.Warn

open Lean PyLean PyLean.Diff PyLean.CoreLibs.Misc

def dIsType (i : Nat) : Bool := i ≠ 12 ∧ i ≠ 13
def dIsWarn (i : Nat) : Bool := i ≤ 9 ∨ i = 14

def dCompile (p : String) (_ : Bool) : Py Unit :=
  match p with
  | "(" => .error (.named "PatternError" "missing ), unterminated subpattern at position 0")
  | "[" => .error (.named "PatternError" "unterminated character set at position 0")
  | "a{4294967296}" => .error (.overflowError "the repetition number is too large")
  | _ => .ok ()

/-- The exception classes of the difftest: the builtin ones, `io.UnsupportedOperation` (an
`OSError` and a `ValueError`), and user subclasses `MyOSError`, `MyValueError`, `MyImportError`. -/
def dHier : Hier := ⟨fun c b =>
  excIsA c b || (c == "UnsupportedOperation" && (excIsA "OSError" b || excIsA "ValueError" b)) ||
  (c == "MyOSError" && excIsA "OSError" b) || (c == "MyValueError" && excIsA "ValueError" b) ||
  (c == "MyImportError" && excIsA "ImportError" b) ||
  -- `class Y(UnicodeEncodeError, metaclass=M)` whose `M.mro` is `[cls, UnicodeEncodeError,
  -- BaseException, object]`: under `UnicodeEncodeError` and `BaseException`, not `ValueError`
  (c == "Y" && (b == "UnicodeEncodeError" || b == "BaseException")) ||
  -- `AE`, a plain subclass of `AttributeError`
  (c == "AE" && excIsA "AttributeError" b) || c == b⟩

def dFEnv : FEnv := ⟨dCompile, dIsType, dIsWarn, dHier⟩

def dImp (m _ : List Char) : Py Nat :=
  match str' m with
  | "" => .error (.valueError "Empty module name")
  | "builtins" => .ok 0
  | "os" => .ok 1
  | "warnings" => .ok 2
  | "os.path" => .ok 3
  | _ => .error (.named "ModuleNotFoundError" "~No module named")

def noAttrE : PyExc := .named "AttributeError" "~has no attribute"

def dGetattr (m : Nat) (k : List Char) : Py Found :=
  match m, str' k with
  | 0, "Warning" => .ok (.cls 0)
  | 0, "UserWarning" => .ok (.cls 1)
  | 0, "DeprecationWarning" => .ok (.cls 3)
  | 0, "PendingDeprecationWarning" => .ok (.cls 6)
  | 0, "ImportWarning" => .ok (.cls 7)
  | 0, "ResourceWarning" => .ok (.cls 8)
  | 0, "RuntimeWarning" => .ok (.cls 9)
  | 0, "SyntaxWarning" => .ok (.cls 14)
  | 0, "int" => .ok (.cls 10)
  | 0, "ValueError" => .ok (.cls 11)
  | 0, "print" => .ok .nonclass
  | 0, "None" => .ok .nonclass
  | 1, "path" => .ok .nonclass
  | 1, "sep" => .ok .nonclass
  | 1, "error" => .ok (.cls 15)
  | 2, "filters" => .ok .nonclass
  | 2, "_OptionError" => .ok (.cls 16)
  | 2, "WarningMessage" => .ok (.cls 17)
  | 3, "sep" => .ok .nonclass
  | _, _ => .error noAttrE

def dOEnv : OEnv := ⟨dFEnv, dImp, dGetattr, 0⟩

/-! ## Decoding -/

def pRx (j : Json) : Except String (Option Rx) :=
  match j with
  | .null => .ok none
  | v => do return some ⟨← jStrAt v 0, ← jBoolAt v 1⟩

def pElem (j : Json) : Except String Elem := do
  match ← jStrAt j 0 with
  | "o" =>
    let r : Py Bool := match ← jStrAt j 2 with
      | "t" => .ok true
      | "f" => .ok false
      | "verr" => .error (.valueError "eq")
      | "uerr" => .error (.named "UnicodeError" "eq")
      | "unsup" => .error (.named "UnsupportedOperation" "eq")
      | "myverr" => .error (.named "MyValueError" "eq")
      | "yerr" => .error (.named "Y" "y")
      | _ => .error (.keyError "'eq'")
    return .other (← jNatAt j 1) r
  | _ => return .item ⟨← jStrAt j 1, ← pRx (← jGetI j 2), ← jNatAt j 3, ← pRx (← jGetI j 4), ← jIntAt j 5⟩

def pCont (j : Json) : Except String Cont := do
  match ← jStrAt j 0 with
  | "list" => return .list (← (← jArr (← jGetI j 1)).mapM pElem)
  | "tuple" => return .tuple (← (← jArr (← jGetI j 1)).mapM pElem)
  | _ => return .deleted

def pAct (j : Json) : Except String ActA := do
  match ← jStrAt j 0 with
  | "s" => return .str (← jStrAt j 1)
  | "o" => return .obj (← jStrAt j 1)
  | _ => return .unhashable "list"

def pStrA (j : Json) : Except String StrA := do
  match ← jStrAt j 0 with
  | "s" => return .str (← jStrAt j 1)
  | _ => return .obj

def pIntA (j : Json) : Except String IntA := do
  match ← jStrAt j 0 with
  | "i" => return .int (← jIntAt j 1)
  | "b" => return .int (if ← jBoolAt j 1 then 1 else 0)
  | _ => return .obj

/-! ## Encoding -/

def jRx : Option Rx → Json
  | none => .null
  | some r => Json.arr #[jStr r.src, jBool r.ci]

def jElem : Elem → Json
  | .item f => Json.arr #["i", jStr f.action, jRx f.msg, toJson f.cat, jRx f.mod, jInt f.ln]
  | .other i _ => Json.arr #["o", toJson i]

def jCont : Cont → Json
  | .list xs => Json.arr #["list", Json.arr (xs.map jElem).toArray]
  | .tuple xs => Json.arr #["tuple", Json.arr (xs.map jElem).toArray]
  | .deleted => Json.arr #["deleted"]

def jRes {α : Type} : Py α → Json
  | .ok _ => Json.arr #["ok"]
  | .error e => Json.arr #["exc", jStr e.className, jStr e.message]

/-! ## Runs -/

/-- One operation of a `filt` script on twin `c` (lock state `d`; the main thread is 1, a helper
thread 2) or Python. `none` is an `_acquire_lock` that would block. -/
def runOp (isC : Bool) (op : Json) (d : LockSt) (s : FState) :
    Except String (Option (Py (LockSt × FState))) := do
  let k ← jStrAt op 0
  let lift := fun (r : Py FState) => some (r.map (fun s' => (d, s')))
  -- `with _wm._lock:` blocks while the helper thread holds the lock
  if isC && d.owner = some 2 && k ∈ ["fw", "sf", "reset", "mut"] then return none
  match k with
  | "fw" =>
    return lift (filterwarnings dFEnv (← pAct (← jGetI op 1)) (← pStrA (← jGetI op 2)) (← jNatAt op 3)
      (← pStrA (← jGetI op 4)) (← pIntA (← jGetI op 5)) (← jBoolAt op 6) s)
  | "sf" =>
    return lift (simplefilter dHier (← pAct (← jGetI op 1)) (← jNatAt op 2) (← pIntA (← jGetI op 3))
      (← jBoolAt op 4) s)
  | "reset" => return lift (resetwarnings s)
  | "mut" =>
    if isC then return (cFiltersMutated 1 d s.ver).map (fun r => r.map (fun (d', v) => (d', { s with ver := v })))
    else return some (.ok (d, { s with ver := s.ver + 1 }))
  | "acq" | "oacq" =>
    let t := if k = "acq" then 1 else 2
    if isC then return (cAcquire t d).map (fun d' => .ok (d', s)) else return some (.ok (d, s))
  | "rel" | "orel" =>
    let t := if k = "rel" then 1 else 2
    if isC then return some ((cRelease t d).map (fun d' => (d', s))) else return some (.ok (d, s))
  | _ =>
    if isC then return some ((cMutatedLockHeld d s.ver).map (fun v => (d, { s with ver := v })))
    else return some (.ok (d, { s with ver := pyMutatedLockHeld s.ver }))

def runFilt (isC : Bool) (j : Json) : Except String Json := do
  let s0 : FState := ⟨← pCont (← j.getObjVal? "init"), 0⟩
  let ops ← jArr (← j.getObjVal? "ops")
  let mut d : LockSt := ⟨none, 0⟩
  let mut s := s0
  let mut outs : Array Json := #[]
  for op in ops do
    match ← runOp isC op d s with
    | none => outs := outs.push (Json.arr #["blocked"])
    | some (.ok (d', s')) =>
      d := d'
      s := s'
      outs := outs.push (Json.arr #["ok"])
    | some (.error e) => outs := outs.push (jRes (α := Unit) (.error e))
  return Json.mkObj [("ok", Json.arr #[Json.arr outs, jCont s.cont, jInt s.ver])]

def runOpt (j : Json) : Except String Json := do
  let args ← (← jArr (← j.getObjVal? "args")).mapM (fun a => a.getStr?)
  let (lines, s, exc) := processoptions dOEnv (args.map String.toList) ⟨.list [], 0⟩
  let out : Py Unit := match exc with
    | some e => .error e
    | none => .ok ()
  return Json.mkObj [("ok", Json.arr #[Json.arr (lines.map jStr).toArray, jRes out, jCont s.cont])]

def dK : DefaultCats := ⟨3, 6, 7, 8⟩

def jPat : Option Pat → Json
  | none => .null
  | some (.plain s) => Json.arr #["plain", jStr s]
  | some (.regex _ _ _) => Json.arr #["regex"]

def runDefaults (j : Json) : Except String Json := do
  match ← (← j.getObjVal? "twin").getStr? with
  | "c" =>
    let fs := (initFilters false dK).map fun
      | .tuple f | .list5 f => Json.arr #[jStr (match f.action with | .str a => a | _ => ""), jPat f.msg,
          toJson f.cat, jPat f.mod, jInt (match f.ln with | .int v => v | .obj _ => 0)]
      | .other _ => Json.null
    return Json.mkObj [("ok", Json.arr fs.toArray)]
  | _ =>
    match setupDefaults dFEnv false dK ⟨.list [], 0⟩ with
    | .ok ⟨.list xs, _⟩ =>
      return Json.mkObj [("ok", Json.arr (xs.map fun
        | .item f => Json.arr #[jStr f.action, jRx f.msg, toJson f.cat, jRx f.mod, jInt f.ln]
        | .other i _ => toJson i).toArray)]
    | _ => throw "setupDefaults failed"

def opsHandler : Handler := fun fn j =>
  match fn with
  | "filt_c" => some (runFilt true j)
  | "filt_py" => some (runFilt false j)
  | "opt" => some (runOpt j)
  | "defaults" => some (runDefaults j)
  | _ => none

end PyLean.CoreLibs.Warn
