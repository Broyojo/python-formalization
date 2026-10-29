import Lean.Data.Json
import PyLean.Core

/-!
Helpers shared by the per-module differential-testing handlers
(`PyLean/<Module>/Diff.lean`). A handler receives the case's `fn` name and the
whole JSON case, and returns `none` for a name it does not know.
-/

namespace PyLean.Diff

open Lean

/-- `{"ok": v}` or `{"exc": "<class>", "msg": "<message>"}`. -/
def encPy {α : Type} (enc : α → Json) : Py α → Json
  | .ok v => Json.mkObj [("ok", enc v)]
  | .error e => Json.mkObj [("exc", toJson e.className), ("msg", toJson e.message)]

def field (j : Json) (key : String) : Except String Json := j.getObjVal? key

def getNat (j : Json) (key : String) : Except String Nat := do (← field j key).getNat?
def getInt (j : Json) (key : String) : Except String Int := do (← field j key).getInt?
def getStr (j : Json) (key : String) : Except String String := do (← field j key).getStr?
def getBool (j : Json) (key : String) : Except String Bool := do (← field j key).getBool?

/-- An optional int argument: absent or `null` is `none`. -/
def getOptInt (j : Json) (key : String) : Except String (Option Int) :=
  match j.getObjVal? key with
  | .ok .null | .error _ => .ok none
  | .ok v => some <$> v.getInt?

abbrev Handler := String → Json → Option (Except String Json)

end PyLean.Diff
