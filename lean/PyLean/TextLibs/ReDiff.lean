import PyLean.DiffCore
import PyLean.TextLibs.ReSem

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

def encOptSpan : Option (Nat × Nat) → Json
  | some (a, b) => Json.arr #[toJson a, toJson b]
  | none => Json.null

def encMatch (m : MatchR) : Json :=
  Json.mkObj [("spans", Json.arr (m.spans.map encOptSpan).toArray),
    ("lastindex", (match m.lastindex with
      | some i => toJson i
      | none => Json.null))]

def encGroupV : GroupV → Json
  | .str s => toJson s
  | .none => Json.null

def encItem2 : FindItem → Json
  | .one v => encGroupV v
  | .tuple vs => Json.arr (vs.map encGroupV).toArray

def liftS {α : Type} : Except String α → Py α
  | .ok v => .ok v
  | .error e => .error (.named "Harness" e)

def gidxOf (j : Json) : Except String GIdx :=
  match j with
  | .num _ => do return .int (← j.getInt?)
  | .arr _ => do return .name (← nats j)
  | _ => pure .unhashable

def gidxs (j : Json) : Except String (List GIdx) := do
  (← (← field j "gs").getArr?).toList.mapM gidxOf

def encPat (p : Pat) : Json := Json.mkObj [("code", toJson p.code.toList), ("groups", toJson p.groups)]

def run (fn : String) (j : Json) : Except String Json := do
  if fn == "re.sem" then
    let pat ← nats (← field j "pat")
    let flags ← getNat j "flags"
    let s ← nats (← field j "s")
    let full ← getBool j "full"
    return encPy id (do
      let p ← parse true pat flags
      match semMatch true p flags pat s 0 s.length full with
      | none => throw .modelFuel
      | some none => return Json.null
      | some (some o) =>
        return Json.mkObj [("stop", toJson o.stop), ("groups", Json.arr (o.groups.map encOptSpan).toArray),
          ("last", (match o.last with
            | some i => toJson i
            | none => Json.null))] : Py Json)
  if fn == "re.validate" then
    let code ← nats (← field j "code")
    let groups ← getInt j "groups"
    return encPy (fun (_ : Unit) => toJson true) (sreCompileCheck code.toArray groups)
  if fn == "re.escape" then
    return encPy toJson (.ok (escape (← nats (← field j "s"))) : Py (List Nat))
  if fn == "re.args" then
    let args ← (← (← field j "args").getArr?).toList.mapM Json.getInt?
    let kw (k : String) : Except String (Option Int) :=
      match j.getObjVal? k with
      | .ok v => do return some (← v.getInt?)
      | .error _ => pure none
    let f ← getStr j "f"
    let first := if f == "split" then "maxsplit" else "count"
    let least := if f == "split" then 2 else 3
    return encPy (fun (x : Int × Int) => Json.arr #[toJson x.1, toJson x.2])
      (shuffleArgs f first least args (← kw "kw1") (← kw "kw2"))
  if fn == "re.scanner" then
    let phrases ← (← (← field j "phrases").getArr?).toList.mapM nats
    let flags ← getNat j "flags"
    let subj ← nats (← field j "s")
    let acts : List (Option Nat) := (List.range phrases.length).map fun i =>
      if i % 3 == 2 then none else some i
    return encPy (fun (x : List Nat × List Nat) => Json.arr #[toJson x.1, toJson x.2]) (do
      let p ← scannerInit (← liftS (getBool j "text")) phrases flags
      scan p acts subj)
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
  | "re.code" =>
    return encPy toJson (do codeOf (← parse text pat flags) flags)
  | "re.exec" =>
    let subj ← nats (← field j "s")
    let pos ← getInt j "pos"
    let endpos ← getInt j "endpos"
    let mode ← getStr j "mode"
    let cnt ← getInt j "count"
    let repl ← match j.getObjVal? "repl" with
      | .ok v => nats v
      | .error _ => pure []
    let stext ← getBool j "stext"
    let p := compilePat text pat flags
    let body : Py Json := do
      let p ← p
      if mode != "prepr" && mode != "peq" && mode != "sub" && mode != "subcall" then checkSubject p !stext
      match mode with
      | "match" | "fullmatch" | "search" =>
        return (match ← runMatch p subj pos endpos mode with
          | some m => encMatch m
          | none => Json.null)
      | "findall" =>
        return Json.arr ((← findall p subj pos endpos).map encItem2).toArray
      | "finditer" =>
        return Json.arr ((← scanAll p subj pos endpos true).map encMatch).toArray
      | "scanmatch" =>
        return Json.arr ((← scanAll p subj pos endpos false).map encMatch).toArray
      | "split" =>
        return Json.arr ((← split p subj cnt).map encGroupV).toArray
      | "matchop" =>
        let op ← liftS (getStr j "op")
        let gs ← liftS (gidxs j)
        match ← runMatch p subj pos endpos "search" with
        | none => return Json.null
        | some m =>
          let g := gs.headD (.int 0)
          let pair (x : Int × Int) : Json := Json.arr #[toJson x.1, toJson x.2]
          match op with
          | "group" => return encItem2 (← matchGroup p subj m gs)
          | "getitem" => return encGroupV (← matchGetslice p subj m g)
          | "start" => return toJson (← matchStart p m g)
          | "end" => return toJson (← matchEnd p m g)
          | "span" => return pair (← matchSpan p m g)
          | "regs" => return Json.arr ((matchRegs m).map pair).toArray
          | "repr" => return toJson (matchRepr (p.isbytes > 0) subj m)
          | _ => throw (.named "Harness" "bad op")
      | "prepr" => return toJson (patternRepr p)
      | "peq" =>
        let q ← compilePat text (← liftS (nats (← liftS (field j "pat2")))) (← liftS (getNat j "flags2"))
        return toJson [patEq p q, patHashInput p == patHashInput q]
      | "sub" =>
        let (r, n) ← subx p repl subj cnt !stext
        return Json.arr #[toJson r, toJson n]
      | "subcall" =>
        let steps ← liftS (do (← (← field j "script").getArr?).toList.mapM fun x => do
          if let .ok v := x.getObjVal? "raise" then
            return (.error (.valueError (← v.getStr?)) : Py CallRet)
          if let .ok v := x.getObjVal? "other" then
            return (.ok (.other (← v.getStr?)) : Py CallRet)
          if x.isNull then return (.ok .none_ : Py CallRet)
          return (.ok (.text (← nats x)) : Py CallRet))
        let f : Nat → MatchR → Py CallRet := fun k _ => steps.getD k (.ok (.text []))
        let (r, n) ← subCall p f subj cnt !stext
        return Json.arr #[toJson r, toJson n]
      | "expand" =>
        match ← runMatch p subj pos endpos "search" with
        | none => return Json.null
        | some m => return toJson (← matchExpand p repl subj m)
      | "groups" =>
        match ← runMatch p subj pos endpos "search" with
        | none => return Json.null
        | some m =>
          return Json.mkObj [("groups", Json.arr ((matchGroups subj m).map encGroupV).toArray),
            ("gd", Json.arr ((matchGroupdict p subj m).map fun x =>
              Json.arr #[toJson x.1, encGroupV x.2]).toArray),
            ("lastgroup", (match matchLastgroup p m with
              | some n => toJson n
              | none => Json.null))]
      | _ => throw (.named "Harness" "bad mode")
    return encPy id body
  | "re.template" =>
    let repl ← nats (← field j "repl")
    return encPy (fun (r : List TItem) => Json.arr (r.map encTItem).toArray) (do
      let p ← parse text pat flags
      parseTemplate text repl (p.groups - 1) p.groupdict)
  | _ => throw s!"unknown fn {fn}"

end PyLean.TextLibs.Re
