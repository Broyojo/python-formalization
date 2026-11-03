import PyLean.CoreLibs.Misc.Common
import PyLean.CoreLibs.Warn.Model
import PyLean.CoreLibs.Warn.DiffOps

/-! `warn.c` and `warn.py` cases: one `warn_explicit` call against a filters list, a registry and
the once registry, through the C model or the Python one.

Categories: 0 Warning, 1 UserWarning, 2 a subclass of UserWarning, 3 DeprecationWarning, 4 a
subclass of UserWarning whose metaclass `__subclasscheck__` raises `KeyError('boom')`, 5 a subclass
of UserWarning whose `__init__` raises `ValueError('bad message')`, 6 `LieW`, a subclass of
UserWarning whose `__class__` property gives DeprecationWarning.
Messages (`msg`): a str; `lieU` and `lieI`, str subclasses whose `__class__` gives UserWarning or
`int`; `raise` and `raiseA`, str subclasses whose `__class__` raises `ValueError('cls')` or
`AttributeError('cls')`; `inst`, an instance of the category; `instlie`, a `LieW` instance.
`getattr` maps a deleted module attribute to what the module's `__getattr__` raises for it
(`key`: `KeyError('k')`, `ae`: `AE('a')`, an `AttributeError` subclass); `imp` is `raise`
(`builtins.__import__` raises `RuntimeError('no import')` for `warnings`) or `none`
(`sys.modules['warnings'] = None` during the call).
Patterns: `"a"`, `"ab"`, `"m"`, `"x"`, `".*b"` (compiled with `re.I` for messages), `"RAISE"` (an
object whose `match` raises `ValueError('bad pattern')`), `"PLAIN:s"` (the str `s`). A filter item
is `[action, msg, cat, mod, ln, shape]` with shape `tuple`, `list` or `short` (a 3-tuple) and an
action that may be the int 5. The filters version is 7 here; the Python side maps it to the real
counter. -/

namespace PyLean.CoreLibs.Warn

open Lean PyLean PyLean.Diff PyLean.CoreLibs.Misc

def VER : Int := 7

def lower (s : String) : String := s.map Char.toLower

def reTypeErr : PyExc := .typeError "expected string or bytes-like object, got 'int'"

/-- `re.compile(p, re.I if ci else 0)` for the patterns the generator uses (none has `^`, so a
match from position i is a match of the suffix), the raising object, or a plain str. -/
def pat (ci : Bool) (p : String) : Option Pat :=
  let norm := fun (s : String) => if ci then lower s else s
  let rxp := fun (f : String → Bool) => some (Pat.regex (fun s => .ok (f s)) true reTypeErr)
  if p.startsWith "PLAIN:" then some (.plain (p.drop 6).toString)
  else match p with
  | "a" => rxp fun s => (norm s).startsWith "a"
  | "ab" => rxp fun s => (norm s).startsWith "ab"
  | "m" => rxp fun s => (norm s).startsWith "m"
  | "x" => rxp fun s => (norm s).startsWith "x"
  | ".*b" => rxp fun s => (norm s).contains 'b'
  | "RAISE" => some (.regex (fun _ => .error (.valueError "bad pattern")) false (.valueError "bad pattern"))
  | _ => none

/-- The suffixes `_match_filename` tries: from 0 and after each `.`. -/
def dotSuffixes (s : String) : List String :=
  let cs := s.toList
  (List.range (cs.length + 1)).filterMap fun i =>
    if i = 0 ∨ cs[i - 1]? = some '.' then some (String.ofList (cs.drop i)) else none

def dropR (s : String) (n : Nat) : String := String.ofList (s.toList.take (s.length - n))

/-- `_py_warnings._match_filename` off Windows, _py_warnings.py:523-552. -/
def matchFilename (p : Pat) (fn : String) : Py Bool := do
  let m : String → Py Bool := match p with
    | .regex call _ _ => call
    | .plain _ => fun _ => .error noMatchAttr
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
  else .ok (b = 0 || a = b || ((a = 2 || a = 4 || a = 5 || a = 6) && b = 1))

def catName : Nat → String
  | 0 => "Warning" | 1 => "UserWarning" | 2 => "W1" | 3 => "DeprecationWarning" | 4 => "Odd"
  | 6 => "LieW" | _ => "BadInit"

/-- What the module `__getattr__` of the cases raises. -/
def gaErr (k : String) : PyExc :=
  if k = "key" then .keyError "'k'" else .named "AE" "a"

/-- The `getattr` entry of a case for attribute `a`. -/
def caseGetattr (j : Json) (a : String) : Option PyExc :=
  match j.getObjVal? "getattr" with
  | .ok o => match o.getObjVal? a with
    | .ok (.str k) => some (gaErr k)
    | _ => none
  | _ => none

def pItem (j : Json) : Except String Item := do
  let msg ← (← jGetI j 1).getStr? <|> pure ""
  let mod ← (← jGetI j 3).getStr? <|> pure ""
  let action : AV := match (← jGetI j 0) with
    | .str a => .str a
    | .arr _ => .unhashable "list"
    | _ => .hashable "int"
  let ln : LnV := match (← jGetI j 4) with
    | .str _ => .obj "str"
    | v => match v.getInt? with
      | .ok i => .int i
      | .error _ => .obj "str"
  let f : Filter := { action := action, msg := pat true msg, cat := ← jNatAt j 2, mod := pat false mod,
                      ln := ln }
  match ← jStrAt j 5 with
  | "list" => return .list5 f
  | "short" => return .other (.valueError "not enough values to unpack (expected 5, got 3)")
  | _ => return .tuple f

def pVer (j : Json) : Except String Val :=
  match j with
  | .str "cur" => .ok (exactInt VER)
  | .str "stale" => .ok (exactInt (VER - 1))
  | .str "true" => .ok ⟨1, false⟩
  | v => exactInt <$> v.getInt?

def pEntry (j : Json) : Except String (Key × Val) := do
  match ← jStrAt j 0 with
  | "t" => return (.tri (← jStrAt j 1) (← jNatAt j 2) (← jIntAt j 3), exactInt (← jIntAt j 4))
  | "p" => return (.pair (← jStrAt j 1) (← jNatAt j 2), exactInt (← jIntAt j 3))
  | "v" => return (.version, ← pVer (← jGetI j 1))
  | o => throw s!"bad entry {o}"

def pReg (j : Json) : Except String Reg := do
  -- the dict as given: later entries overwrite earlier ones
  let es ← (← jArr j).mapM pEntry
  return es.foldl (fun r (k, v) => regSet r k v) []

def jVer (v : Int) : Json :=
  if v = VER then jStr "cur" else if v = VER - 1 then jStr "stale" else jInt v

def jEntry : Key × Val → Json
  | (.tri t c l, v) => Json.arr #["t", jStr t, toJson c, jInt l, jInt v.n]
  | (.pair t c, v) => Json.arr #["p", jStr t, toJson c, jInt v.n]
  | (.version, v) => Json.arr #["v", jVer v.n]

/-- Entries sorted by their compact JSON, as the Python side sorts them. -/
def jReg (r : Reg) : Json :=
  let es := (r.map jEntry).map (fun j => (j.compress, j))
  Json.arr ((es.mergeSort (fun a b => decide (a.1 ≤ b.1))).map (·.2)).toArray

/-- `lineno` values that are not ints: `'5'`, `5.5`, `'x'`. -/
def pLine (j : Json) : Except String LineArg :=
  match j with
  | .arr #[.str "obj", .str "s5"] => .ok (.obj (.ok 5) (.typeError "'str' object cannot be interpreted as an integer"))
  | .arr #[.str "obj", .str "f"] => .ok (.obj (.ok 5) (.typeError "'float' object cannot be interpreted as an integer"))
  | .arr #[.str "obj", .str "x"] =>
    .ok (.obj (.error (.valueError "invalid literal for int() with base 10: 'x'"))
      (.typeError "'str' object cannot be interpreted as an integer"))
  | v => .int <$> v.getInt?

def optStr (j : Json) (k : String) (d : String) : String :=
  match j.getObjVal? k with
  | .ok (.str v) => v
  | _ => d

def optBool (j : Json) (k : String) : Bool :=
  match j.getObjVal? k with
  | .ok (.bool b) => b
  | _ => false

/-- The source unavailable to `linecache` (`_source_unavailable`): empty or `<...>`. -/
def srcUnavail (fn : String) : Bool := fn.isEmpty || (fn.startsWith "<" && fn.endsWith ">")

def runCase (twin : String) (j : Json) : Except String Json := do
  let fs ← (← jArr (← j.getObjVal? "filters")).mapM pItem
  let dfltJ ← j.getObjVal? "dflt"
  let dflt : DfltV := if optBool j "dfltdel" then
      (match caseGetattr j "defaultaction" with
       | some e => .raises e "ignore"
       | none => .deleted "ignore")
    else match dfltJ with
    | .str a => .val (.str a)
    | _ => .val (.hashable "int")
  let modJ ← j.getObjVal? "module"
  let module ← match ← jStrAt modJ 0 with
    | "omit" => pure ModArg.omitted
    | "none" => pure ModArg.none
    | "obj" => pure ModArg.obj
    | _ => pure (ModArg.some (← jStrAt modJ 1))
  let cat ← (← j.getObjVal? "cat").getNat?
  let filename ← (← j.getObjVal? "filename").getStr?
  let (globs, pyLines) : GlobA × Py Unit := match optStr j "globs" "none" with
    | "int" => (.obj "int",
        if srcUnavail filename then .ok () else .error (.typeError "module_globals must be a dict, not int"))
    | "empty" => (.dict (.ok ()), .ok ())
    | "bad" => (.dict (.error (.valueError "no source")),
        if srcUnavail filename then .ok () else .error (.valueError "no source"))
    | _ => (.none, .ok ())
  let mk := optStr j "msg" "str"
  let (cat, inst, pyCls) : Nat × Bool × ClsV := match mk with
    | "lieU" => (cat, false, .cls 1 "UserWarning" true)
    | "lieI" => (cat, false, .cls 10 "int" false)
    | "raise" => (cat, false, .raises (.valueError "cls"))
    | "raiseA" => (cat, false, .raises (.named "AttributeError" "cls"))
    | "inst" => (cat, true, .own)
    | "instlie" => (6, true, .cls 3 "DeprecationWarning" true)
    | _ => (cat, false, .own)
  let c : Call := { text := ← (← j.getObjVal? "text").getStr?, cat := cat, filename := filename,
                    lineno := ← pLine (← j.getObjVal? "lineno"), module := module,
                    mkMsg := if cat == 5 && !inst then .error (.valueError "bad message") else .ok (),
                    globs := globs, pyLines := pyLines, inst := inst, pyCls := pyCls }
  let reg ← match ← j.getObjVal? "reg" with
    | .null => pure RegArg.none
    | .str "obj" => pure RegArg.obj
    | .obj kv => match kv.toList with
      | [(_, v)] => RegArg.mapping <$> pReg v
      | _ => throw "bad reg"
    | v => RegArg.dict <$> pReg v
  let onceR ← pReg (← j.getObjVal? "once")
  let once : OnceV := match optStr j "oncek" "dict" with
    | "int" => .notDict "int" onceR
    | "deleted" => match caseGetattr j "onceregistry" with
      | some e => .raises e onceR
      | none => .deleted onceR
    | _ => .dict onceR
  let showA : ShowA := match optStr j "show" (if optBool j "showraise" then "raise" else "ok") with
    | "raise" => .call (.ok ()) (.error (.valueError "show failed"))
    | "deleted" => match caseGetattr j "_showwarnmsg" with
      | some e => .swRaises (.ok ()) e
      | none => .deleted
    | "noncallable" => .noncallable "int"
    | "nowm" => match caseGetattr j "WarningMessage" with
      | some e => .wmRaises e
      | none => .noWM
    | _ => .call (.ok ()) (.ok ())
  let importW : Py Unit := match optStr j "imp" "ok" with
    | "raise" => .error (.named "RuntimeError" "no import")
    | "none" => .error (.named "ModuleNotFoundError" "import of warnings halted; None in sys.modules")
    | _ => .ok ()
  let E : Env := { isSub := isSub, isSubPy := fun _ b => b = 4, matchFilename := matchFilename,
                   shw := showA, hier := dHier, importW := importW }
  let K : WCfg := ⟨optBool j "ctx", optBool j "tuple", dflt, once⟩
  let r := if twin = "c" then cWarnExplicit E K fs VER c reg else pyWarnExplicit E K fs VER c reg
  let out := match r.out with
    | .error e => if e = warnRaised c then Json.arr #["exc", jStr (catName c.cat), jStr c.text]
      else encR jBool (.error e)
    | .ok b => encR jBool (.ok b)
  let printed := twin = "c" && cFellBack E K fs VER c reg
  return Json.mkObj [("ok", Json.arr #[out, jOpt jReg r.reg, jReg r.once, jBool printed])]

def weHandler : Handler := fun fn j =>
  match fn with
  | "c" => some (runCase "c" j)
  | "py" => some (runCase "py" j)
  | _ => none

end PyLean.CoreLibs.Warn
