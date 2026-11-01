import PyLean.DiffCore

/-! Helpers shared by the `misc` difftest handlers. A case is a script of operations; each
operation's outcome is encoded by `encR`, so one exception in the middle of a script is compared
like any other value. -/

namespace PyLean.CoreLibs.Misc

open Lean PyLean PyLean.Diff

/-- `["ok", v]` or `["exc", <class>, <message>]`, matching `misc_res` in `corelibs_diff.py`. -/
def encR {α : Type} (enc : α → Json) : Py α → Json
  | .ok v => Json.arr #["ok", enc v]
  | .error e => Json.arr #["exc", toJson e.className, toJson e.message]

def jInt (i : Int) : Json := toJson i
def jStr (s : String) : Json := toJson s
def jBool (b : Bool) : Json := toJson b
def jUnit (_ : Unit) : Json := Json.null
def jList {α : Type} (enc : α → Json) (l : List α) : Json := Json.arr (l.map enc).toArray
def jOpt {α : Type} (enc : α → Json) : Option α → Json
  | some a => enc a
  | none => Json.null

def jArr (j : Json) : Except String (List Json) := do
  return (← j.getArr?).toList

def jGetI (j : Json) (i : Nat) : Except String Json :=
  match j with
  | .arr a => match a[i]? with
    | some v => .ok v
    | none => .error s!"no element {i}"
  | _ => .error "not an array"

def jIntAt (j : Json) (i : Nat) : Except String Int := do (← jGetI j i).getInt?
def jNatAt (j : Json) (i : Nat) : Except String Nat := do (← jGetI j i).getNat?
def jStrAt (j : Json) (i : Nat) : Except String String := do (← jGetI j i).getStr?
def jBoolAt (j : Json) (i : Nat) : Except String Bool := do (← jGetI j i).getBool?
def jIntList (j : Json) : Except String (List Int) := do
  (← jArr j).mapM (fun x => x.getInt?)
def jIntListAt (j : Json) (i : Nat) : Except String (List Int) := do jIntList (← jGetI j i)
def jOptInt (j : Json) : Except String (Option Int) :=
  match j with
  | .null => .ok none
  | v => some <$> v.getInt?
def jOptIntAt (j : Json) (i : Nat) : Except String (Option Int) := do jOptInt (← jGetI j i)

end PyLean.CoreLibs.Misc
