import PyLean.DiffCore
import PyLean.TextLibs.ShlexModel

/-! `shlex.*` difftest cases; see `difftest/textlibs_diff.py`. -/

namespace PyLean.TextLibs.Shlex

open Lean PyLean PyLean.Diff

def nats (j : Json) : Except String (List Nat) := do
  (← j.getArr?).toList.mapM Json.getNat?

def strOpt (j : Json) (k : String) (d : List Nat) : Except String (List Nat) :=
  match j.getObjVal? k with
  | .ok v => nats v
  | .error _ => pure d

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "shlex.split" =>
    let s ← nats (← field j "s")
    return encPy (fun (r : List (List Nat)) => toJson r) (split s (← getBool j "comments") (← getBool j "posix"))
  | "shlex.lex" =>
    let s ← nats (← field j "s")
    let posix ← getBool j "posix"
    let punct ← strOpt j "punct" []
    let c0 := defaults posix punct
    let c : Cfg := { c0 with
      whitespaceSplit := ← getBool j "wsplit"
      commenters := ← strOpt j "commenters" c0.commenters
      quotes := ← strOpt j "quotes" c0.quotes
      escape := ← strOpt j "escape" c0.escape }
    let failAt : Option (Nat × PyExc) := match j.getObjVal? "fail" with
      | .ok v => (v.getNat?.toOption).map (·, .valueError "boom")
      | .error _ => none
    let n := s.length * 3 + 16
    return encPy (fun (r : List (List Nat)) => toJson r)
      (lexAll c n (n + 2) { src := { data := s, failAt } })
  | "shlex.quote" =>
    let a : QArg ← match j.getObjVal? "s" with
      | .ok v => pure (.str (← nats v))
      | .error _ =>
        let t ← match j.getObjVal? "raise" with
          | .ok _ => pure (.error (.valueError "boom") : Py Bool)
          | .error _ => pure (.ok (← getBool j "truth"))
        pure (.other "Obj" t)
    return encPy (fun (r : List Nat) => toJson r) (quote a)
  | "shlex.join" =>
    let args ← (← (← field j "args").getArr?).toList.mapM nats
    return encPy (fun (r : List Nat) => toJson r) (.ok (joinS args) : Py (List Nat))
  | _ => throw s!"unknown fn {fn}"

end PyLean.TextLibs.Shlex
