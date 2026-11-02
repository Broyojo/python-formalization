import PyLean.CoreLibs.Misc.Common
import PyLean.CoreLibs.Warn.Model

/-! `warn.c` and `warn.py` cases: one `warn_explicit` call against a filters list, a registry and
the once registry, through the C model or the Python one.

Categories: 0 Warning, 1 UserWarning, 2 a subclass of UserWarning, 3 DeprecationWarning, 4 a
subclass of UserWarning whose metaclass `__subclasscheck__` raises `KeyError('boom')`.
Patterns: `"a"`, `"ab"`, `"m"`, `"x"`, `".*b"` (compiled with `re.I` for messages), `"RAISE"` (an
object whose `match` raises `ValueError('bad pattern')`). The filters version is 7 here; the
Python side maps it to the real counter. -/

namespace PyLean.CoreLibs.Warn

open Lean PyLean PyLean.Diff PyLean.CoreLibs.Misc

def VER : Int := 7

def lower (s : String) : String := s.map Char.toLower

/-- `re.compile(p, re.I if ci else 0).match(s)`, for the patterns the generator uses (none has
`^`, so a match from position i is a match of the suffix). -/
def pat (ci : Bool) (p : String) : Option Pat :=
  let norm := fun (s : String) => if ci then lower s else s
  match p with
  | "a" => some ⟨fun s => .ok ((norm s).startsWith "a"), true⟩
  | "ab" => some ⟨fun s => .ok ((norm s).startsWith "ab"), true⟩
  | "m" => some ⟨fun s => .ok ((norm s).startsWith "m"), true⟩
  | "x" => some ⟨fun s => .ok ((norm s).startsWith "x"), true⟩
  | ".*b" => some ⟨fun s => .ok ((norm s).contains 'b'), true⟩
  | "RAISE" => some ⟨fun _ => .error (.valueError "bad pattern"), false⟩
  | _ => none

/-- The suffixes `_match_filename` tries: from 0 and after each `.`. -/
def dotSuffixes (s : String) : List String :=
  let cs := s.toList
  (List.range (cs.length + 1)).filterMap fun i =>
    if i = 0 ∨ cs[i - 1]? = some '.' then some (String.ofList (cs.drop i)) else none

def dropR (s : String) (n : Nat) : String := String.ofList (s.toList.take (s.length - n))

/-- `_py_warnings._match_filename` off Windows, _py_warnings.py:523-552. -/
def matchFilename (p : Pat) (fn : String) : Py Bool := do
  let m := p.call
  if fn.isEmpty then m "<unknown>"
  else if fn.startsWith "<" && fn.endsWith ">" then m fn
  else
    let isPy := fn.endsWith ".py"
    let f1 := if isPy then dropR fn 3 else fn
    if ← m f1 then return true
    let f2 := if isPy && f1.endsWith "/__init__" then dropR f1 9 else f1
    let f3 := f2.replace "/" "."
    for s in dotSuffixes f3 do
      if ← m s then return true
    return false

def isSub (a b : Nat) : Py Bool :=
  if b = 4 then .error (.keyError "'boom'")
  else .ok (b = 0 || a = b || (a = 2 && b = 1) || (a = 4 && b = 1))

def catName : Nat → String
  | 0 => "Warning" | 1 => "UserWarning" | 2 => "W1" | 3 => "DeprecationWarning" | _ => "Odd"

def pFilter (j : Json) : Except String Filter := do
  let msg ← (← jGetI j 1).getStr? <|> pure ""
  let mod ← (← jGetI j 3).getStr? <|> pure ""
  return { action := ← jStrAt j 0, msg := pat true msg, cat := ← jNatAt j 2, mod := pat false mod,
           ln := ← jIntAt j 4 }

def pVer (j : Json) : Except String Int :=
  match j with
  | .str "cur" => .ok VER
  | .str "stale" => .ok (VER - 1)
  | v => v.getInt?

def pEntry (j : Json) : Except String (Key × Int) := do
  match ← jStrAt j 0 with
  | "t" => return (.tri (← jStrAt j 1) (← jNatAt j 2) (← jIntAt j 3), ← jIntAt j 4)
  | "p" => return (.pair (← jStrAt j 1) (← jNatAt j 2), ← jIntAt j 3)
  | "v" => return (.version, ← pVer (← jGetI j 1))
  | o => throw s!"bad entry {o}"

def pReg (j : Json) : Except String Reg := do
  -- the dict as given: later entries overwrite earlier ones
  let es ← (← jArr j).mapM pEntry
  return es.foldl (fun r (k, v) => regSet r k v) []

def jVer (v : Int) : Json :=
  if v = VER then jStr "cur" else if v = VER - 1 then jStr "stale" else jInt v

def jEntry : Key × Int → Json
  | (.tri t c l, v) => Json.arr #["t", jStr t, toJson c, jInt l, jInt v]
  | (.pair t c, v) => Json.arr #["p", jStr t, toJson c, jInt v]
  | (.version, v) => Json.arr #["v", jVer v]

/-- Entries sorted by their compact JSON, as the Python side sorts them. -/
def jReg (r : Reg) : Json :=
  let es := (r.map jEntry).map (fun j => (j.compress, j))
  Json.arr ((es.mergeSort (fun a b => decide (a.1 ≤ b.1))).map (·.2)).toArray

def runCase (twin : String) (j : Json) : Except String Json := do
  let fs ← (← jArr (← j.getObjVal? "filters")).mapM pFilter
  let dflt ← (← j.getObjVal? "dflt").getStr?
  let modJ ← j.getObjVal? "module"
  let module ← match ← jStrAt modJ 0 with
    | "omit" => pure ModArg.omitted
    | "none" => pure ModArg.none
    | _ => pure (ModArg.some (← jStrAt modJ 1))
  let c : Call := { text := ← (← j.getObjVal? "text").getStr?, cat := ← (← j.getObjVal? "cat").getNat?,
                    filename := ← (← j.getObjVal? "filename").getStr?,
                    lineno := ← (← j.getObjVal? "lineno").getInt?, module := module }
  let reg ← match ← j.getObjVal? "reg" with
    | .null => pure none
    | v => some <$> pReg v
  let once ← pReg (← j.getObjVal? "once")
  let showRaise ← (← j.getObjVal? "showraise").getBool?
  let E : Env := { isSub := isSub, isSubPy := fun _ b => b = 4, matchFilename := matchFilename,
                   showMsg := if showRaise then .error (.valueError "show failed") else .ok () }
  let r := if twin = "c" then cWarnExplicit E fs dflt VER c reg once
    else pyWarnExplicit E fs dflt VER c reg once
  let out := match r.out with
    | .error e => if e = warnRaised c then Json.arr #["exc", jStr (catName c.cat), jStr c.text]
      else encR jBool (.error e)
    | .ok b => encR jBool (.ok b)
  return Json.mkObj [("ok", Json.arr #[out, jOpt jReg r.reg, jReg r.once])]

def handler : Handler := fun fn j =>
  match fn with
  | "c" => some (runCase "c" j)
  | "py" => some (runCase "py" j)
  | _ => none

end PyLean.CoreLibs.Warn
