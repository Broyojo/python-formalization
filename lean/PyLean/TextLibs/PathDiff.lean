import PyLean.DiffCore
import PyLean.TextLibs.PathModel

/-! `path.*` difftest cases; see `difftest/textlibs_diff.py`. -/

namespace PyLean.TextLibs.Path

open Lean PyLean PyLean.Diff

def nats (j : Json) : Except String (List Nat) := do
  (← j.getArr?).toList.mapM Json.getNat?

def decPV (j : Json) : Except String PV := do
  if let .ok b := j.getObjVal? "b" then return ⟨true, ← nats b⟩
  return ⟨false, ← nats (← field j "s")⟩

def decArg (j : Json) : Except String PathArg := do
  if let .ok x := j.getObjVal? "pl" then
    if let .ok e := x.getObjVal? "raise" then
      let a ← e.getArr?
      let cls ← a[0]!.getStr?
      let msg ← a[1]!.getStr?
      return .fsp "PL" (.error (match cls with
        | "ValueError" => .valueError msg
        | "TypeError" => .typeError msg
        | _ => .named cls msg)) ""
    if let .ok c := x.getObjVal? "bad" then return .fsp "PL" (.ok none) (← c.getStr?)
    return .fsp "PL" (.ok (some (← decPV x))) ""
  if let .ok c := j.getObjVal? "o" then return .other (← c.getStr?)
  return .val (← decPV j)

def encPV (v : PV) : Json := Json.arr #[toJson v.isb, toJson v.s]

def enc2 (x : PV × PV) : Json := Json.arr #[encPV x.1, encPV x.2]

def run (fn : String) (j : Json) : Except String Json := do
  let args ← (← (← field j "args").getArr?).toList.mapM decArg
  let a := args.headD (.other "NoneType")
  let rest := args.drop 1
  let lift (f : List Nat → PV → Json) : Json :=
    encPy id (do let v ← fspath a; return f v.s v)
  match fn with
  | "path.pisabs" => return encPy toJson (isabsP a)
  | "path.psplit" => return encPy enc2 (splitP a)
  | "path.psplitext" => return encPy enc2 (splitextP a)
  | "path.pbasename" => return encPy encPV (basenameP a)
  | "path.pdirname" => return encPy encPV (dirnameP a)
  | "path.pjoin" => return encPy encPV (joinP a rest)
  | "path.psplitroot" =>
    return lift fun s v => let (d, r, t) := splitrootP s
      Json.arr #[encPV ⟨v.isb, d⟩, encPV ⟨v.isb, r⟩, encPV ⟨v.isb, t⟩]
  | "path.pnormpath" =>
    return lift fun s v => Json.arr #[encPV ⟨v.isb, normpathC s⟩, encPV ⟨v.isb, normpathPy s⟩]
  | "path.nisabs" => return encPy toJson (isabsN a)
  | "path.nsplit" => return encPy enc2 (splitN a)
  | "path.nsplitext" => return encPy enc2 (splitextN a)
  | "path.nsplitroot" =>
    return lift fun s v => let (d, r, t) := splitrootN s
      Json.arr #[encPV ⟨v.isb, d⟩, encPV ⟨v.isb, r⟩, encPV ⟨v.isb, t⟩]
  | "path.njoin" => return encPy encPV (joinN a rest)
  | "path.nnormpath" => return lift fun s v => encPV ⟨v.isb, normpathN s⟩
  | _ => throw s!"unknown fn {fn}"

end PyLean.TextLibs.Path
