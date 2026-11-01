import PyLean.DiffCore
import PyLean.TextLibs.ReParse

/-! `re.*` difftest cases; see `difftest/textlibs_diff.py`. Trees travel as nested arrays with
the opcode's short name first. -/

namespace PyLean.TextLibs.Re

open Lean PyLean PyLean.Diff

def atName : AtCode → String
  | .beginning => "AT_BEGINNING" | .beginningString => "AT_BEGINNING_STRING"
  | .boundary => "AT_BOUNDARY" | .nonBoundary => "AT_NON_BOUNDARY"
  | .end_ => "AT_END" | .endString => "AT_END_STRING"

def catName : Cat → String
  | .digit => "CATEGORY_DIGIT" | .notDigit => "CATEGORY_NOT_DIGIT"
  | .space => "CATEGORY_SPACE" | .notSpace => "CATEGORY_NOT_SPACE"
  | .word => "CATEGORY_WORD" | .notWord => "CATEGORY_NOT_WORD"

def encItem : SetItem → Json
  | .literal c => toJson (["l"] : List String) |> fun _ => Json.arr #["l", toJson c]
  | .range lo hi => Json.arr #["r", toJson lo, toJson hi]
  | .category c => Json.arr #["c", toJson (catName c)]
  | .negate => Json.arr #["n"]

def kindName : RepeatKind → String
  | .max => "MAX_REPEAT" | .min => "MIN_REPEAT" | .possessive => "POSSESSIVE_REPEAT"

mutual
  def encNode : Node → Json
    | .literal c => Json.arr #["lit", toJson c]
    | .notLiteral c => Json.arr #["nlit", toJson c]
    | .any => Json.arr #["any"]
    | .in_ s => Json.arr #["in", Json.arr (s.map encItem).toArray]
    | .at_ a => Json.arr #["at", toJson (atName a)]
    | .groupref g => Json.arr #["gref", toJson g]
    | .grouprefExists g y n =>
      Json.arr #["gex", toJson g, encList y, (match n with
        | some l => encList l
        | none => Json.null)]
    | .branch alts => Json.arr #["br", encAlts alts]
    | .subpattern g a d p =>
      Json.arr #["sub", (match g with
        | some x => toJson x
        | none => Json.null), toJson a, toJson d, encList p]
    | .repeat_ k lo hi p => Json.arr #["rep", toJson (kindName k), toJson lo, toJson hi, encList p]
    | .atomic p => Json.arr #["atom", encList p]
    | .assert_ d p => Json.arr #["as", toJson d, encList p]
    | .assertNot d p => Json.arr #["nas", toJson d, encList p]
    | .failure => Json.arr #["fail"]

  def encList : List Node → Json
    | [] => Json.arr #[]
    | n :: ns =>
      match encList ns with
      | .arr a => Json.arr (#[encNode n] ++ a)
      | j => j

  def encAlts : List (List Node) → Json
    | [] => Json.arr #[]
    | a :: as =>
      match encAlts as with
      | .arr b => Json.arr (#[encList a] ++ b)
      | j => j
end

def nats (j : Json) : Except String (List Nat) := do
  (← j.getArr?).toList.mapM Json.getNat?

def encTItem : TItem → Json
  | .lit s => toJson s
  | .group g => Json.mkObj [("g", toJson g)]

def run (fn : String) (j : Json) : Except String Json := do
  let pat ← nats (← field j "pat")
  let text ← getBool j "text"
  let flags ← getNat j "flags"
  match fn with
  | "re.parse" =>
    return encPy (fun p => Json.mkObj [("p", encList p.p), ("flags", toJson p.flags),
      ("groups", toJson p.groups),
      ("width", toJson [(getwidth p.groupwidths p.p).1, (getwidth p.groupwidths p.p).2]),
      ("gd", Json.arr (p.groupdict.map fun x => Json.arr #[toJson x.1, toJson x.2]).toArray)])
      (parse text pat flags)
  | "re.template" =>
    let repl ← nats (← field j "repl")
    return encPy (fun (r : List TItem) => Json.arr (r.map encTItem).toArray) (do
      let p ← parse text pat flags
      parseTemplate text repl (p.groups - 1) p.groupdict)
  | _ => throw s!"unknown fn {fn}"

end PyLean.TextLibs.Re
