import PyLean.DiffCore
import PyLean.CoreLibs.EnumDC.Model

/-! Differential-testing handler for `corelibs` cases with `"fn": "enumdc.<name>"`.
The dispatcher in `CoreLibs/Diff.lean` strips the `enumdc.` prefix. -/

namespace PyLean.CoreLibs.EnumDC

open Lean PyLean PyLean.Diff

def getArr (j : Json) (key : String) : Except String (List Json) := do
  pure (← (← field j key).getArr?).toList

def okJ (j : Json) : Json := Json.mkObj [("ok", j)]

def getCls (j : Json) : Except String FlagCls := do
  let members ← (← getArr j "members").mapM fun p => do
    pure (← (← p.getArrVal? 0).getStr?, ← (← p.getArrVal? 1).getNat?)
  let b ← match ← getStr j "boundary" with
    | "strict" => pure Boundary.strict
    | "conform" => pure .conform
    | "eject" => pure .eject
    | _ => pure .keep
  pure ⟨"F", members, b⟩

def outJ : FlagVal → Json
  | .flag v n => toJson [toJson "flag", toJson v, toJson n]
  | .plain v => toJson [toJson "plain", toJson v]

/-- `F(v)` and `F(w)`, as the Python side builds them; ejected or failing operands take the
same path there. -/
def withValues (c : FlagCls) (v w : Int) (f : Nat → Nat → Py FlagVal) : Json :=
  match c.call v with
  | .error e => encPy outJ (.error e)
  | .ok (.plain _) => okJ "skip"
  | .ok (.flag a _) =>
    match c.call w with
    | .error e => encPy outJ (.error e)
    | .ok (.plain _) => okJ "skip"
    | .ok (.flag b _) => encPy outJ (f a b)

def getFields (j : Json) : Except String (List FieldSpec) := do
  (← getArr j "fields").mapM fun f => do
    pure { name := ← getStr f "name", hasDefault := ← getBool f "default", init := ← getBool f "init",
           kwOnly := ← getBool f "kw" }

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "flag_call" =>
    let c ← getCls j
    pure (encPy outJ (c.call (← getInt j "v")))
  | "flag_or" =>
    let c ← getCls j
    pure (withValues c (← getInt j "v") (← getInt j "w") c.orOp)
  | "flag_and" =>
    let c ← getCls j
    pure (withValues c (← getInt j "v") (← getInt j "w") c.andOp)
  | "flag_xor" =>
    let c ← getCls j
    pure (withValues c (← getInt j "v") (← getInt j "w") c.xorOp)
  | "flag_invert" =>
    let c ← getCls j
    pure (withValues c (← getInt j "v") (← getInt j "w") (fun a _ => c.invert a))
  | "flag_iter" =>
    let c ← getCls j
    pure (encPy (fun x => match x with
      | .flag v _ => toJson [toJson v,
          toJson ((c.iterMembers v).map fun m => m.map Prod.fst), toJson (bitCount v)]
      | .plain _ => Json.null) (c.call (← getInt j "v")))
  | "names" =>
    let s := (← getStr j "s").toList
    pure (okJ (toJson [isDunder s, isSunder s, isPrivate ['F'] s]))
  | "bits" =>
    let n ← getNat j "n"
    let last ← (← getArr j "last").mapM (·.getNat?)
    let count ← getNat j "count"
    pure (okJ (toJson [toJson (bitsOf n), toJson (isSingleBit n), toJson (highBit n),
      toJson (flagNext none count last), toJson (enumNext 1 (last.map Int.ofNat))]))
  | "hash_action" =>
    let a := hashAction (← getBool j "u") (← getBool j "e") (← getBool j "f") (← getBool j "h")
    pure (okJ (match a with
      | .none => "none"
      | .setNone => "setNone"
      | .add => "add"
      | .exception => "exception"))
  | "dc_init" =>
    let fs ← getFields j
    let std := fs.filter (fun f => !f.kwOnly)
    pure (encPy (fun _ => toJson (fs.map (·.name))) (initDefaultOrder none std))
  | "dc_replace" =>
    let fs ← getFields j
    let std := fs.filter (fun f => !f.kwOnly)
    let changes ← (← getArr j "changes").mapM fun c => do pure ((← c.getStr?), (2 : Int))
    match initDefaultOrder none std with
    | .error e => pure (encPy (fun (_ : Unit) => Json.null) (.error e))
    | .ok () =>
      pure (encPy (fun (r : List (String × Int)) =>
        toJson ((r.map Prod.fst).mergeSort (fun a b => decide (a ≤ b))))
        (replaceArgs fs (fun _ => 1) changes))
  | _ => throw s!"unknown fn enumdc.{fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.CoreLibs.EnumDC
