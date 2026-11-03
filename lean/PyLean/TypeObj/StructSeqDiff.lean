import PyLean.DiffCore
import PyLean.TypeObj.StructSeqC

/-! Differential-testing cases for struct sequences (`difftest/typeobj_structseq_diff.py`).

Every case starts from a `PyStructSequence_Desc`; the type is the model's `newType` of it, so
`initialize_members` and the size dict are tested along with the function the case is about. A
real type (`os.terminal_size`, `time.struct_time`, ...) comes as the desc it was built from. -/

namespace PyLean.TypeObj.StructSeq.Diff

open Lean PyLean PyLean.Diff PyLean.UnicodeObj

def strOf (s : Str) : String := String.ofList (s.map Char.ofNat)

def bytesOf (j : Json) : Except String Bytes := do (← j.getArr?).toList.mapM (·.getNat?)

def parseFName : Json → Except String FName
  | .null => pure .unnamed
  | j => .named <$> bytesOf j

def parseDesc (j : Json) : Except String Desc := do
  let fs ← (← (← field j "fields").getArr?).toList.mapM parseFName
  pure { name := ← bytesOf (← field j "name"), fields := fs, nInSeq := ← getInt j "nseq" }

/-- A rebinding of a size attribute: `{"int": n}`, `"other"` (a non-int), or `"del"`. -/
def parseLie (j : Json) : Except String (Option SizeVal) :=
  match j with
  | .str "del" => pure none
  | .str "other" => pure (some .other)
  | j => do pure (some (.int (← getInt j "int")))

/-- The type's dict after the case's rebindings. -/
def applyLies (d : TDict) (j : Json) : Except String TDict := do
  let mut out := d
  for k in ["n_sequence_fields", "n_fields", "n_unnamed_fields"] do
    match j.getObjVal? k with
    | .ok v =>
      let l ← parseLie v
      let prev := out
      out := fun key => if key = k then .ok l else prev key
    | .error _ => pure ()
  pure out

def excJson (e : PyExc) : Json := Json.mkObj [("exc", toJson e.className), ("msg", toJson e.message)]

def cres {β : Type} (f : β → Json) : CRes β → Json
  | .ok a => Json.mkObj [("ok", f a)]
  | .exc e => excJson e
  | .nullNoExc => Json.mkObj [("exc", "SystemError"), ("msg", "~returned NULL without setting an exception")]
  | .ub w => Json.mkObj [("exc", "UB"), ("msg", toJson w)]

def malloc (n : Nat) : Bool := n < 2 ^ 40

def build (j : Json) : Except String (CRes Built) := do
  pure (newType (← parseDesc (← field j "desc")) malloc (.ok ()))

def slotJson : Slot Json → Json
  | .val v => v
  | .null => "NULL"
  | .junk => "JUNK"

def visible (o : CObj Json) : Json := toJson ((o.slots.take o.size).map slotJson)

/-- `{"r": text}` or `{"e": [class, message]}`: what `repr()` of the item does. -/
def repOf (v : Json) : Py Str :=
  match v.getObjVal? "r" with
  | .ok (.str s) => .ok (lit s)
  | _ =>
    match v.getObjVal? "e" with
    | .ok (.arr #[.str c, .str m]) => .error (.named c m)
    | _ => .error (.named "HarnessError" "bad item")

def kvList (j : Json) : Except String (List (Str × Json)) := do
  (← j.getArr?).toList.mapM fun p => do
    match p with
    | .arr #[.str k, v] => pure (lit k, v)
    | _ => throw "bad pair"

/-- The constructor's `dict` argument: `null`, `"notdict"`, or a list of pairs. -/
def dictArg (j : Json) : Except String (Option (CDictArg Json)) := do
  match j with
  | .null => pure none
  | .str "notdict" => pure (some .notDict)
  | j =>
    let kv ← kvList j
    pure (some (.dict (fun _ k => .ok ((kv.find? (·.1 == k)).map (·.2))) kv.length kv.length))

def seqArg (j : Json) : Except String (Py (List Json)) := do
  match j with
  | .str "notseq" => pure (.error (.typeError "constructor requires a sequence"))
  | j => pure (.ok (← j.getArr?).toList)

/-- An object built by the constructor while the type is honest. -/
def honestObj (t : CType) (j : Json) : Except String (CRes (CObj Json)) := do
  let arg ← seqArg (← field j "seq")
  let d ← dictArg (← field j "dict")
  pure (newImplC t { res := arg, dictAfter := t.dict } d .null malloc)

/-- `__reduce__`'s dict as Python builds it: a later key replaces the value in place. -/
def dictify (ps : List (Str × Json)) : List (Str × Json) :=
  ps.foldl (fun acc (k, v) =>
    if acc.any (·.1 == k) then acc.map (fun (k', v') => if k' == k then (k', v) else (k', v'))
    else acc ++ [(k, v)]) []

def reduceJson (r : List Json × List (Str × Json)) : Json :=
  toJson [toJson r.1, toJson ((dictify r.2).map fun (k, v) => toJson [toJson (strOf k), v])]

/-- `kwargs` holding exact-str keys, as the harness passes them: field `i`'s pop finds the key
unless an earlier field had the same name; what is left is the keys that name no field. -/
def kwOracle (t : CType) (n : Nat) (kv : List (Str × Json)) : KwArg Json :=
  let names := (t.members.take n).map fun m => (utf8Decode m.name .strict).toOption.getD []
  { pop := fun i key =>
      let rest := kv.filter fun p => !((names.take i).contains p.1)
      .ok ((rest.find? (·.1 == key)).map (·.2)),
    sizeAfter := (kv.filter fun p => !(names.contains p.1)).length }

inductive CapiOp where
  | set (i : Int) (v : Json)
  | get (i : Int)

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "ss_newtype" =>
    let r ← build j
    pure <| cres (fun (b : Built) =>
      let sz := fun k => match b.type.dict k with | .ok (some (.int n)) => toJson n | _ => Json.null
      toJson [sz "n_sequence_fields", sz "n_fields", sz "n_unnamed_fields",
        toJson (b.matchArgs.map strOf), toJson b.type.basicsize,
        toJson (b.type.members.map fun m =>
          toJson [toJson (match utf8Decode m.name .strict with | .ok s => strOf s | .error _ => "?"),
                  toJson m.slot])]) r
  | "ss_repr" =>
    let r ← build j
    match r with
    | .ok b =>
      let name := match j.getObjVal? "rename" with
        | .ok .null | .error _ => b.type.name
        | .ok v => (bytesOf v).toOption.getD b.type.name
      let t := { b.type with name := name, dict := ← applyLies b.type.dict (← field j "lies") }
      let sets ← (← (← field j "sets").getArr?).toList.mapM fun p => do
        match p with
        | .arr #[i, v] => pure ((← i.getInt?), v)
        | _ => throw "bad set"
      let o := sets.foldl (fun (o : CRes (CObj Json)) (i, v) => o.bind fun o => pssSetItem o i v)
        (pssNew (α := Json) t malloc)
      pure <| cres (fun s => toJson (strOf s)) (o.bind fun o => structseqRepr (fun n => decide (n < 2 ^ 45)) t o repOf)
    | r => pure (cres (fun _ => Json.null) r)
  | "ss_capi" =>
    let r ← build j
    match r with
    | .ok b =>
      let t := { b.type with dict := ← applyLies b.type.dict (← field j "lies") }
      let ops ← (← (← field j "ops").getArr?).toList.mapM fun p => do
        match p with
        | .arr #[.str "set", i, v] => pure (CapiOp.set (← i.getInt?) v)
        | .arr #[.str "get", i] => pure (CapiOp.get (← i.getInt?))
        | _ => throw "bad op"
      let step := fun (acc : CRes (CObj Json × List Json)) (op : CapiOp) =>
        acc.bind fun (o, outs) =>
          match op with
          | .set i v => (pssSetItem o i v).bind fun o => .ok (o, outs)
          | .get i => (pssGetItem o i).bind fun s => .ok (o, outs ++ [slotJson s])
      let res := ops.foldl step ((pssNew (α := Json) t malloc).bind fun o => .ok (o, []))
      pure <| cres (fun (o, outs) => toJson [toJson o.size, toJson outs]) res
    | r => pure (cres (fun _ => Json.null) r)
  | "ss_new" =>
    let r ← build j
    match r with
    | .ok b =>
      let t := { b.type with dict := ← applyLies b.type.dict (← field j "lies") }
      let o ← honestObj t j
      pure (cres visible o)
    | r => pure (cres (fun _ => Json.null) r)
  | "ss_reduce" =>
    let r ← build j
    match r with
    | .ok b =>
      match ← honestObj b.type j with
      | .ok o =>
        let t := { b.type with dict := ← applyLies b.type.dict (← field j "lies") }
        pure (cres reduceJson (reduceC t o))
      | r => pure (cres (fun _ => Json.null) r)
    | r => pure (cres (fun _ => Json.null) r)
  | "ss_replace" =>
    let r ← build j
    match r with
    | .ok b =>
      match ← honestObj b.type j with
      | .ok o =>
        let t := { b.type with dict := ← applyLies b.type.dict (← field j "lies") }
        let kws ← match ← field j "kws" with
          | .null => pure none
          | v => some <$> (kwOracle t (realSize t o.size) <$> kvList v)
        let nargs ← getNat j "nargs"
        let res := (replaceC t o nargs kws malloc).bind fun r =>
          (reduceC b.type r).bind fun red => .ok (visible r, reduceJson red)
        pure (cres (fun (v, red) => toJson [v, red]) res)
      | r => pure (cres (fun _ => Json.null) r)
    | r => pure (cres (fun _ => Json.null) r)
  | _ => throw s!"unknown fn {fn}"

end PyLean.TypeObj.StructSeq.Diff
