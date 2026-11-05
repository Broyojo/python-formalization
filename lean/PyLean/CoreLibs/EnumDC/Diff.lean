import PyLean.DiffCore
import PyLean.CoreLibs.EnumDC.EnumObj
import PyLean.CoreLibs.EnumDC.Dataclass
import PyLean.CoreLibs.EnumDC.DcAnnot

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

/-! ### Enum classes -/

def decAtom (j : Json) : Except String Atom := do
  let k ← (← j.getArrVal? 0).getStr?
  let v ← j.getArrVal? 1
  match k with
  | "int" => pure (.int (← v.getInt?))
  | "str" => pure (.str (← v.getStr?))
  | "obj" => pure (.obj (← v.getNat?))
  | "list" => pure (.list (← v.getNat?))
  | "auto" =>
    match v with
    | .null => pure (.auto none)
    | _ => pure (.auto (some (← v.getInt?)))
  | _ => throw "atom"

def decGen (j : Json) : Except String Gen := do
  match ← (← j.getArrVal? 0).getStr? with
  | "enum" => pure .enum
  | "strEnum" => pure .strEnum
  | "flag" => pure .flag
  | "const" => pure (.const (← decAtom (← j.getArrVal? 1)))
  | "raises" => pure (.raises (.named (← (← j.getArrVal? 1).getStr?) (← (← j.getArrVal? 2).getStr?)))
  | _ => throw "gen"

def decName (j : Json) : Except String Name := do pure (← j.getStr?).toList

def decEV : Nat → Json → Except String EV
  | 0, _ => throw "too deep"
  | f + 1, j => do
    let k ← (← j.getArrVal? 0).getStr?
    let v ← j.getArrVal? 1
    match k with
    | "tup" => pure (.tup (← (← v.getArr?).toList.mapM decAtom))
    | "member" => pure (.member (← decEV f v))
    | "nonmember" => pure (.nonmember (← decEV f v))
    | "descr" => pure (.descr (← v.getNat?))
    | "inner" => pure (.inner (← v.getNat?))
    | "names" => pure (.names (← (← v.getArr?).toList.mapM decName))
    | "gen" => pure (.gen (← decGen v))
    | _ => pure (.atom (← decAtom j))

def decItems (l : List Json) : Except String (List (Name × EV)) :=
  l.mapM fun p => do pure (← decName (← p.getArrVal? 0), ← decEV 4 (← p.getArrVal? 1))

def encAtom : Atom → Json
  | .int n => toJson [toJson "int", toJson n]
  | .str s => toJson [toJson "str", toJson s]
  | .obj i => toJson [toJson "obj", toJson i]
  | .list i => toJson [toJson "list", toJson i]
  | .auto _ => toJson [toJson "auto"]

def nameJ (n : Name) : Json := toJson (String.ofList n)

def encEV : EV → Json
  | .atom a => encAtom a
  | .tup l => toJson [toJson "tup", toJson (l.map encAtom)]
  | .descr i => toJson [toJson "descr", toJson i]
  | .inner i => toJson [toJson "inner", toJson i]
  | .names l => toJson [toJson "names", toJson (l.map nameJ)]
  | .gen _ => toJson [toJson "gen"]
  | _ => Json.null

def summaryJ (c : EClass) : Json :=
  toJson [toJson (c.memberNames.map nameJ),
    toJson (c.memberMap.map fun p => toJson [nameJ p.1, nameJ p.2, (c.valueOf p.2).elim Json.null encEV]),
    toJson (c.value2member.map fun p => toJson [encEV p.1, nameJ p.2]),
    toJson (c.hashableValues.map encEV), toJson (c.unhashableValues.map encEV),
    toJson (c.unhashableMap.map fun p => toJson [nameJ p.1, toJson (p.2.map encEV)]),
    if c.kind == .flag then toJson [c.flagMask, c.singlesMask, c.allBits] else Json.null]

def decKind (s : String) : EKind :=
  match s with
  | "flag" => .flag
  | "strEnum" => .strEnum
  | _ => .plain

def firstGen : EKind → Gen
  | .plain => .enum
  | .flag => .flag
  | .strEnum => .strEnum

def decMissing (c : EClass) (j : Json) : Except String MissingRet := do
  match ← (← j.getArrVal? 0).getStr? with
  | "none" => pure .none
  | "other" => pure .other
  | "raises" =>
    let cls ← (← j.getArrVal? 1).getStr?
    let m ← (← j.getArrVal? 2).getStr?
    pure (.raises (.named cls (if cls == "KeyError" then s!"'{m}'" else m)))
  | _ =>
    match c.memberMap.lookup (← decName (← j.getArrVal? 1)) with
    | some m => pure (.member m)
    | none => pure (.raises (.keyError "~name"))

def unitJ : Py Unit → Json := encPy (fun _ => Json.null)

def bodyDict (cls : Name) (k : EKind) (body : List (Name × EV)) : Py EnumDict :=
  match enumPrepare cls (firstGen k) with
  | .error e => .error e
  | .ok d =>
    match d.setAll body with
    | (_, some e) => .error e
    | (d', none) => .ok d'

/-- The attributes of the class that are not members. -/
def plainAttrs (d : EnumDict) (c : EClass) : List Name :=
  (d.items.map Prod.fst).filter (fun n => (c.memberMap.lookup n).isNone && !d.ignore.contains n &&
    n != "_order_".toList && n != "_ignore_".toList)

/-- `member.name`: a `name` in the class body that is not a member shadows `Enum.name`. -/
def nameAttr (d : EnumDict) (c : EClass) : Name → Name :=
  match d.items.lookup "name".toList with
  | some v =>
    if (c.memberMap.lookup "name".toList).isSome || d.ignore.contains "name".toList then id else
    match v with
    | .atom (.str s) => fun _ => s.toList
    | _ => fun _ => "?".toList
  | none => id

def classOp (d : EnumDict) (c : EClass) (op : Json) : Except String Json := do
  let k ← (← op.getArrVal? 0).getStr?
  let memberName := nameAttr d c
  match k with
  | "summary" => pure (okJ (summaryJ c))
  | "call" =>
    let a ← decAtom (← op.getArrVal? 1)
    let more ← (← (← op.getArrVal? 2).getArr?).toList.mapM decAtom
    let miss ← decMissing c (← op.getArrVal? 3)
    match enumCallG evOps c none a more {} miss with
    | .ok (.member n) => pure (okJ (nameJ n))
    | .ok (.create _ _ _) => pure (okJ "functional")
    | .error e => pure (unitJ (.error e))
  | "callself" =>
    let n ← decName (← op.getArrVal? 1)
    pure (encPy nameJ (match c.getItem n with
      | .error e => .error e
      | .ok m => c.toG.enumNew evOps (some m) (.atom (.int 0)) false .none))
  | "contains" =>
    pure (encPy (fun (b : Bool) => toJson b)
      (containsG evOps false none c.unhashableValues c.hashableValues (← decEV 4 (← op.getArrVal? 1))))
  | "getitem" => pure (encPy nameJ (c.getItem (← decName (← op.getArrVal? 1))))
  | "iter" => pure (okJ (toJson [toJson (c.iter.map nameJ), toJson (c.reversed.map nameJ), toJson c.len]))
  | "setattr" => pure (unitJ (c.setAttr (← decName (← op.getArrVal? 1))))
  | "delattr" => pure (unitJ (c.delAttr (plainAttrs d c) (← decName (← op.getArrVal? 1))))
  | "alias" =>
    let self ← decName (← op.getArrVal? 1)
    let n ← decName (← op.getArrVal? 2)
    pure (encPy summaryJ (match c.getItem self with
      | .error e => .error e
      | .ok m => c.addAlias m n))
  | "valias" =>
    let self ← decName (← op.getArrVal? 1)
    let v ← decEV 4 (← op.getArrVal? 2)
    pure (encPy summaryJ (match c.getItem self with
      | .error e => .error e
      | .ok m =>
        match c.toG.addValueAlias evOps memberName m v with
        | .error e => .error e
        | .ok g => .ok (c.ofG g)))
  | "valias_call" =>
    let self ← decName (← op.getArrVal? 1)
    let v ← decEV 4 (← op.getArrVal? 2)
    pure (encPy nameJ (match c.getItem self with
      | .error e => .error e
      | .ok m =>
        match c.toG.addValueAlias evOps memberName m v with
        | .error e => .error e
        | .ok g => g.enumNew evOps none v false .none))
  | "unique" => pure (unitJ (c.unique memberName))
  | "verify" =>
    let checks ← (← (← op.getArrVal? 1).getArr?).toList.mapM fun k => do
      match ← k.getStr? with
      | "unique" => pure Check.unique
      | "continuous" => pure Check.continuous
      | _ => pure Check.named
    pure (unitJ (verifyCallG evOps id c.toG memberName (.ok "C") (.enum (c.kind == .flag)) checks))
  | _ => throw "class op"

def runClass (j : Json) : Except String Json := do
  let kind := decKind (← getStr j "kind")
  let body ← decItems (← getArr j "body")
  match bodyDict "C".toList kind body with
  | .error e => pure (unitJ (.error e))
  | .ok d =>
    match enumTypeNew kind d with
    | .error e => pure (unitJ (.error e))
    | .ok c => classOp d c (← field j "op")

def dictJ (d : EnumDict) : Json :=
  toJson [toJson (d.items.map fun p => toJson [nameJ p.1, encEV p.2]), toJson (d.memberNames.map nameJ),
    toJson (d.lastValues.map encEV)]

def runUpdate (j : Json) : Except String Json := do
  let cls ← match ← field j "cls" with
    | .null => pure none
    | v => pure (some (← decName v))
  let gen ← getBool j "gen"
  let d : EnumDict := { clsName := cls, gen := if gen then .enum else .absent }
  let items ← decItems (← getArr j "members")
  let more ← decItems (← getArr j "more")
  let arg := if ← getBool j "mapping" then UpdateArg.mapping items else .pairs items
  pure (encPy dictJ (d.update arg more))

def runCreate (j : Json) : Except String Json := do
  let kind := decKind (← getStr j "kind")
  let start ← getInt j "start"
  let n ← field j "names"
  let v ← n.getArrVal? 1
  let names ← match ← (← n.getArrVal? 0).getStr? with
    | "text" => pure (Names.text (← v.getStr?).toList)
    | "seq" => pure (.seq (← (← v.getArr?).toList.mapM decName))
    | _ => pure (.pairs (← decItems (← v.getArr?).toList))
  pure (encPy summaryJ (enumCreate kind (firstGen kind) "C".toList start names))

def decBase (j : Json) : Except String BaseAttr := do
  match ← j.getStr? with
  | "prop" => pure .prop
  | "descr" => pure .descr
  | "plain" => pure .plain
  | _ => pure .absent

def bitOp : String → Nat → Nat → Nat
  | "or", a, b => a ||| b
  | "and", a, b => a &&& b
  | _, a, b => a ^^^ b

/-- A `Flag` operator on `F(v)`, with an object `other`; `self_none` takes the member whose value is `None`. -/
def runFlag (j : Json) : Except String Json := do
  let c ← getCls j
  let mixin ← getBool j "mixin"
  let op ← getStr j "op"
  let o ← field j "other"
  let kindO ← (← o.getArrVal? 0).getStr?
  let vO ← o.getArrVal? 1
  let selfNone ← getBool j "self_none"
  let v ← getInt j "v"
  let withSelf (f : Option Nat → Except String Json) : Except String Json := do
    if selfNone then f none else
    match c.call v with
    | .error e => pure (encPy outJ (.error e))
    | .ok (.plain _) => pure (okJ "skip")
    | .ok (.flag a _) => f (some a)
  let withOther (f : FlagArg → Except String Json) : Except String Json := do
    match kindO with
    | "other" => f .other
    | "mixin" => f (.mixin (← vO.getInt?))
    | "none" => f (.same none)
    | _ =>
      match c.call (← vO.getInt?) with
      | .error e => pure (encPy outJ (.error e))
      | .ok (.plain _) => pure (okJ "skip")
      | .ok (.flag b _) => f (.same (some b))
  match op with
  | "or" | "and" | "xor" =>
    withSelf fun s => withOther fun other =>
      match flagBin c mixin (bitOp op) s other with
      | none => pure (okJ "NotImplemented")
      | some r => pure (encPy outJ r)
  | "in" =>
    withSelf fun s => withOther fun other =>
      match s with
      | none => pure (okJ "skip")
      | some a => pure (encPy (fun (b : Bool) => toJson b) (flagIn a other))
  | "invert" =>
    withSelf fun s =>
      pure (encPy (fun (p : FlagVal × Option FlagVal) => toJson [outJ p.1,
        match flagInvert c p.2 s with
        | .ok (q, _) => toJson (q == p.1)
        | .error _ => Json.null]) (flagInvert c none s))
  | "bool" =>
    withSelf fun s =>
      match s with
      | none => pure (okJ "skip")
      | some a => pure (okJ (toJson (flagBool a)))
  | "class_in" =>
    match kindO with
    | "other" => pure (encPy (fun (b : Bool) => toJson b) (c.containsOf evOps false (.atom (.str "x"))))
    | _ => pure (encPy (fun (b : Bool) => toJson b) (c.containsOf evOps false (.atom (.int (← vO.getInt?)))))
  | _ => throw "flag op"

/-! ### Dataclasses -/

def getOptBool (j : Json) (key : String) : Except String (Option Bool) := do
  match ← field j key with
  | .null => pure none
  | v => pure (some (← v.getBool?))

def getOptInt (j : Json) (key : String) : Except String (Option Int) := do
  match ← field j key with
  | .null => pure none
  | v => pure (some (← v.getInt?))

def decFKind (s : String) : FKind :=
  match s with
  | "classvar" => .classVar
  | "initvar" => .initVar
  | _ => .plain

def decField (j : Json) : Except String DField := do
  pure { name := ← getStr j "name", kind := decFKind (← getStr j "kind"), dflt := ← getOptInt j "default",
         unhash := ← getBool j "unhash", factory := ← getOptInt j "factory", init := ← getBool j "init",
         repr := ← getBool j "repr", hash := ← getOptBool j "hash", compare := ← getBool j "compare",
         kwOnly := ← getOptBool j "kw" }

def decParams (j : Json) : Except String DParams := do
  pure { init := ← getBool j "init", repr := ← getBool j "repr", eq := ← getBool j "eq", order := ← getBool j "order",
         unsafeHash := ← getBool j "unsafe_hash", frozen := ← getBool j "frozen", matchArgs := ← getBool j "match_args",
         kwOnly := ← getBool j "kw_only", slots := ← getBool j "slots", weakrefSlot := ← getBool j "weakref_slot" }

/-- `getattr(cls, name, MISSING)` for a name the class does not set: the bases, the last in the reversed MRO first. -/
def baseAttr (bases : List (List DField × Bool)) (name : String) : ClsAttr :=
  match bases.reverse.findSome? (fun b => (b.1.find? (fun f => f.name == name && f.dflt.isSome))) with
  | some f =>
    match f.dflt with
    | some d => .value d f.unhash
    | none => .missing
  | none => .missing

def decAnn (bases : List (List DField × Bool)) (j : Json) : Except String Ann := do
  let name ← getStr j "name"
  let kind ← match ← getStr j "kind" with
    | "kw" => pure AnnKind.kwMarker
    | s => pure (.field (decFKind s))
  let a ← field j "attr"
  let attr ← match ← (← a.getArrVal? 0).getStr? with
    | "value" => pure (ClsAttr.value (← (← a.getArrVal? 1).getInt?) (← (← a.getArrVal? 2).getBool?))
    | "field" => pure (.field (← decField (← a.getArrVal? 1)))
    | _ => pure (baseAttr bases name)
  pure { name, kind, attr }

def infoJ (c : DClass) (i : DInfo) : Json :=
  let fieldJ (f : DField) : Json := toJson [toJson f.name, toJson (repr f.kind).pretty, toJson f.kwOnly, toJson f.dflt,
    toJson f.factory.isSome]
  let paramJ (f : DField) : Json := toJson [toJson f.name, toJson (f.dflt.isSome || f.factory.isSome)]
  let hashState : String := match i.hash with
    | .add => "gen"
    | .setNone => "None"
    | _ =>
      match c.hashAttr with
      | some true => "user"
      | some false => "None"
      | none => if c.defined.contains "__eq__" then "None" else "absent"
  toJson [toJson (i.fields.map fieldJ), toJson (i.std.map paramJ), toJson (i.kw.map paramJ), toJson i.matchArgs,
    toJson hashState, toJson i.generated]

def objJ (i : DInfo) (o : DObj) : Json :=
  toJson [toJson (i.real.map fun f =>
      match getAttrD i o f.name with
      | .ok v => toJson v
      | .error _ => toJson "unset"),
    toJson o.post]

def runDc (j : Json) : Except String Json := do
  let bases ← (← getArr j "bases").mapM fun b => do
    pure ((← (← getArr b "fields").mapM decField), ← getBool b "frozen")
  let anns ← (← getArr j "anns").mapM (decAnn bases)
  let defined ← (← getArr j "defined").mapM (·.getStr?)
  let c : DClass := { params := ← decParams (← field j "params"), bases, anns, defined,
                      stray := match ← field j "stray" with
                        | .str s => some s
                        | _ => none,
                      hashAttr := ← getOptBool j "hash", hasSlots := ← getBool j "has_slots" }
  let post ← getBool j "post"
  let op ← field j "op"
  match processClass c with
  | .error e => pure (unitJ (.error e))
  | .ok i =>
    match ← (← op.getArrVal? 0).getStr? with
    | "info" => pure (okJ (infoJ c i))
    | k =>
      let args ← (← (← op.getArrVal? 1).getArr?).toList.mapM (·.getInt?)
      let kw ← (← (← op.getArrVal? 2).getArr?).toList.mapM fun p => do
        pure ((← (← p.getArrVal? 0).getStr?), (← (← p.getArrVal? 1).getInt?))
      match callInit i post args kw with
      | .error e => pure (unitJ (.error e))
      | .ok o =>
        if k == "init" then pure (okJ (objJ i o)) else
        let ch ← (← (← op.getArrVal? 3).getArr?).toList.mapM fun p => do
          pure ((← (← p.getArrVal? 0).getStr?), (← (← p.getArrVal? 1).getInt?))
        pure (encPy (objJ i) (dcReplace i post o ch))

def decDV : Nat → Json → Except String DV
  | 0, _ => throw "too deep"
  | f + 1, j => do
    let k ← (← j.getArrVal? 0).getStr?
    let a ← j.getArrVal? 1
    let l := fun (x : Json) => do (← x.getArr?).toList.mapM (decDV f)
    match k with
    | "atom" => pure (.atom (← a.getInt?))
    | "str" => pure (.str (← a.getStr?))
    | "copied" => pure (.copied (← a.getInt?))
    | "unhash" => pure (.unhash (← a.getInt?))
    | "list" => pure (.list (← l a))
    | "tuple" => pure (.tuple (← l a))
    | "named" => pure (.named (← l a))
    | "listSub" => pure (.listSub (← l a))
    | "tupleSub" => pure (.tupleSub (← l a))
    | "inst" => pure (.inst (← (← a.getArr?).toList.mapM (·.getStr?)) (← l (← j.getArrVal? 2)))
    | "dict" => pure (.dict (← l a) (← l (← j.getArrVal? 2)))
    | "dictSub" => pure (.dictSub (← l a) (← l (← j.getArrVal? 2)))
    | "frozenDict" => pure (.frozenDict (← l a) (← l (← j.getArrVal? 2)))
    | "defaultDict" => pure (.defaultDict (← l a) (← l (← j.getArrVal? 2)))
    | "counter" => pure (.counter (← l a) (← l (← j.getArrVal? 2)))
    | _ => throw "dv"

/-- The objects of the harness's module for `dc_annotation`: `a.b.c`, with `none` for a `None` and two that raise. -/
def annWorld (o : String) (n : String) : Py (Option String) :=
  if o == "bad" then .error (.valueError "get")
  else if o == "boom" then .error (.named "Boom" "get")
  else
    match o, n with
    | "", "a" => .ok (some "a")
    | "", "bad" => .ok (some "bad")
    | "", "boom" => .ok (some "boom")
    | "a", "b" => .ok (some "a.b")
    | "a.b", "c" => .ok (some "a.b.c")
    | _, _ => .ok none

partial def encDV : DV → Json
  | .atom n => toJson [toJson "atom", toJson n]
  | .str s => toJson [toJson "str", toJson s]
  | .copied n => toJson [toJson "copied", toJson n]
  | .unhash n => toJson [toJson "unhash", toJson n]
  | .list l => toJson [toJson "list", toJson (l.map encDV)]
  | .tuple l => toJson [toJson "tuple", toJson (l.map encDV)]
  | .named l => toJson [toJson "named", toJson (l.map encDV)]
  | .listSub l => toJson [toJson "listSub", toJson (l.map encDV)]
  | .tupleSub l => toJson [toJson "tupleSub", toJson (l.map encDV)]
  | .dict k v => toJson [toJson "dict", toJson (k.map encDV), toJson (v.map encDV)]
  | .dictSub k v => toJson [toJson "dictSub", toJson (k.map encDV), toJson (v.map encDV)]
  | .frozenDict k v => toJson [toJson "frozenDict", toJson (k.map encDV), toJson (v.map encDV)]
  | .defaultDict k v => toJson [toJson "defaultDict", toJson (k.map encDV), toJson (v.map encDV)]
  | .counter k v => toJson [toJson "counter", toJson (k.map encDV), toJson (v.map encDV)]
  | .inst _ _ => Json.null

/-! ### Values that raise: `PV` -/

def getOptStrJ (j : Json) : Except String (Option String) :=
  match j with
  | .null => pure none
  | v => some <$> v.getStr?

def decKeys (j : Json) : Except String (List (Int × Option String × Option String)) := do
  (← getArr j "keys").mapM fun k => do
    pure (← (← k.getArrVal? 0).getInt?, ← getOptStrJ (← k.getArrVal? 1), ← getOptStrJ (← k.getArrVal? 2))

def decPV (keys : List (Int × Option String × Option String)) (j : Json) : Except String PV := do
  let k ← (← j.getArrVal? 0).getStr?
  let v ← j.getArrVal? 1
  match k with
  | "int" => pure (.int (← v.getInt?))
  | "str" => pure (.str (← v.getStr?))
  | "key" =>
    let i ← v.getNat?
    match keys[i]? with
    | some (kk, he, ee) => pure (.key kk he ee i)
    | none => throw "key"
  | "robj" => pure (.robj (← v.getStr?) (← (← j.getArrVal? 2).getNat?))
  | "rint" => pure (.rint (← v.getInt?) (← (← j.getArrVal? 2).getStr?))
  | _ => pure (.list (← v.getNat?))

def encPV : PV → Json
  | .int n => toJson [toJson "int", toJson n]
  | .str s => toJson [toJson "str", toJson s]
  | .key _ _ _ i => toJson [toJson "key", toJson i]
  | .list i => toJson [toJson "list", toJson i]
  | .robj _ i => toJson [toJson "robj", toJson i]
  | .rint n _ => toJson [toJson "int", toJson n]

/-- How each member is made: a plain class; `class C(int, Enum)` whose `__new__` returns `int.__new__(cls, 7)` without
setting `_value_`, so `int(value)` is called; and a class whose `__init__` raises `ValueError('init')` for
`value == 'boom'`. -/
def pvMaker (kind : String) (v : PV) : Maker PV :=
  match kind with
  | "customnew" =>
    { plain := false,
      callType := match v with
        | .int n => .ok (.int n)
        | .str s =>
          match s.toInt? with
          | some n => .ok (.int n)
          | none => .error (.valueError "~invalid literal for int() with base 10")
        | _ => .error (.typeError "~int() argument must be a string, a bytes-like object or a real number") }
  | "mnew" =>
    { plain := false,
      callType := match v with
        | .str "b" => .error (.named "BExc" "b")
        | .int n => .ok (.int n)
        | _ => .error (.valueError "v") }
  | "initfail" =>
    { init := match pvOps.eq v (.str "boom") with
        | .error e => .error e
        | .ok true => .error (.valueError "init")
        | .ok false => .ok () }
  | _ => {}

def summaryPV (c : EClassG PV) : Json :=
  toJson [toJson (c.memberNames.map nameJ),
    toJson (c.memberMap.map fun p => toJson [nameJ p.1, nameJ p.2, (c.values.lookup p.2).elim Json.null encPV]),
    toJson (c.value2member.map fun p => toJson [encPV p.1, nameJ p.2]),
    toJson (c.hashableValues.map encPV), toJson (c.unhashableValues.map encPV),
    toJson (c.unhashableMap.map fun p => toJson [nameJ p.1, toJson (p.2.map encPV)])]

def runEhClass (j : Json) : Except String Json := do
  let keys ← decKeys j
  let kind ← getStr j "kind"
  let body ← (← getArr j "body").mapM fun p => do
    pure (← decName (← p.getArrVal? 0), ← decPV keys (← p.getArrVal? 1))
  let op ← field j "op"
  match ({} : EClassG PV).build pvOps (pvMaker kind) body with
  | .error e => pure (unitJ (.error e))
  | .ok c =>
    match ← (← op.getArrVal? 0).getStr? with
    | "summary" => pure (okJ (summaryPV c))
    | "call" =>
      let v ← decPV keys (← op.getArrVal? 1)
      let mj ← op.getArrVal? 2
      let miss ← match ← (← mj.getArrVal? 0).getStr? with
        | "none" => pure MissingRet.none
        | "other" => pure .other
        | "raises" => pure (.raises (.named "KeyError" s!"'{← (← mj.getArrVal? 2).getStr?}'"))
        | _ =>
          match c.memberMap.lookup (← decName (← mj.getArrVal? 1)) with
          | some m => pure (.member m)
          | none => pure (.raises (.keyError "~name"))
      -- `EnumType.__call__`, Lib/enum.py:729-739: no members, no `names`, no `type`
      if c.memberMap.isEmpty then pure (unitJ (.error (.typeError "~has no members; specify `names=()`")))
      else pure (encPy nameJ (c.enumNew pvOps none v false miss))
    | "contains" =>
      let v ← decPV keys (← op.getArrVal? 1)
      pure (encPy (fun (b : Bool) => toJson b) (containsG pvOps false none c.unhashableValues c.hashableValues v))
    | "callself" =>
      let n ← decName (← op.getArrVal? 1)
      pure (encPy nameJ (match c.getItem n with
        | .error e => .error e
        | .ok m => c.enumNew pvOps (some m) (.int 0) false .none))
    | k =>
      let n ← decName (← op.getArrVal? 1)
      let v ← decPV keys (← op.getArrVal? 2)
      match c.getItem n with
      | .error e => pure (unitJ (.error e))
      | .ok m =>
        match c.addValueAlias pvOps id m v with
        | .error e => pure (unitJ (.error e))
        | .ok c' =>
          if k == "valias" then pure (okJ (summaryPV c'))
          else pure (encPy nameJ (c'.enumNew pvOps none v false .none))

/-- `verify(*checks)` on a class built from `int` and `str` values, or on `int`, `len` or `42`. `order` is the iteration
order of the set of values, as the generator saw it, as places in the set's insertion order. -/
def runEhVerify (j : Json) : Except String Json := do
  let kind := decKind (← getStr j "kind")
  let body ← decItems (← getArr j "body")
  let order : List EV → List EV ← match ← field j "order" with
    | .null => pure id
    | o => do
      let idx ← (← o.getArr?).toList.mapM (·.getNat?)
      pure (fun l => idx.filterMap (fun i => l[i]?))
  let checks ← (← getArr j "checks").mapM fun k => do
    match ← k.getStr? with
    | "unique" => pure Check.unique
    | "named" => pure Check.named
    | _ => pure Check.continuous
  match bodyDict "C".toList kind body with
  | .error e => pure (unitJ (.error e))
  | .ok d =>
    match enumTypeNew kind d with
    | .error e => pure (unitJ (.error e))
    | .ok c =>
      let vals := c.memberNames.filterMap c.valueOf
      let (name, target) : Py String × VTarget := match ← getStr j "target" with
        | "cls" => (.ok "C", .enum (kind == .flag))
        | "int" => (.ok "int", .cls)
        | "notcls_name" => (.ok "len", .notCls)
        | _ => (.error (.named "AttributeError" "'int' object has no attribute '__name__'"), .notCls)
      pure (unitJ (verifyCallG evOps order c.toG id name target checks))

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
    match c.callC [] (← getInt j "v") with
    | .error e => pure (unitJ (.error e))
    | .ok (.plain _, _) => pure (okJ Json.null)
    | .ok (.flag v _, cache) =>
      pure (encPy (fun (l : List (Option MapEntry)) => toJson [toJson v,
          toJson (l.map fun m => match m with
            | some (.member n _) => toJson n
            | some (.pseudo _ n) => toJson n
            | none => Json.null), toJson (bitCount v)]) (c.iterC cache v))
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
  | "ec_class" => runClass j
  | "ec_update" => runUpdate j
  | "ec_create" => runCreate j
  | "ec_scan" => do
    let s := scanBases 0 {} (← (← getArr j "bases").mapM decBase)
    pure (okJ (if s.found then toJson [toJson true, toJson s.attrType, toJson s.clsIndex] else toJson [false]))
  | "ec_progress" =>
    pure (encPy (fun (n : Name) => toJson (String.ofList n))
      (({} : EClassG EV).enumNew evOps none (.atom (.int 1)) true .none))
  | "ec_flag" => runFlag j
  | "dc_class" => runDc j
  | "dc_hash" =>
    let fs ← (← getArr j "fields").mapM decField
    pure (okJ (toJson ((hashFields fs).map (·.name))))
  | "dc_eq" =>
    let terms ← (← getArr j "terms").mapM fun t => do
      match ← t.getStr? with
      | "raise" => pure (Except.error (PyExc.valueError "eq") : Py (Int × Bool))
      | "t" => pure (.ok ((1 : Int), true))
      | _ => pure (.ok ((0 : Int), false))
    match dcEq (1 : Int) (← getBool j "same") (← getBool j "same_class") terms with
    | none => pure (okJ "NotImplemented")
    | some r => pure (encPy (fun (x : Int) => toJson x) r)
  | "dc_order" =>
    let a ← (← getArr j "a").mapM (·.getInt?)
    let b ← (← getArr j "b").mapM (·.getInt?)
    match dcOrder (← getStr j "op") (← getBool j "same_class") a b with
    | none => pure (okJ "NotImplemented")
    | some r => pure (okJ (toJson r))
  | "dc_frozen" =>
    let names ← (← getArr j "fields").mapM (·.getStr?)
    let n ← getStr j "name"
    let e ← getBool j "exact"
    if ← getBool j "del" then pure (unitJ (frozenDel e names n)) else pure (unitJ (frozenSet e names n))
  | "dc_make" =>
    let items ← (← getArr j "items").mapM fun i => do
      match ← (← i.getArrVal? 0).getStr? with
      | "name" => pure (MakeItem.name (← (← i.getArrVal? 1).getStr?))
      | "named" => pure (.named (← (← i.getArrVal? 1).getStr?))
      | "notStr" => pure .notStr
      | _ => pure .bad
    pure (encPy (fun (l : List String) => toJson l) (makeNames items []))
  | "dc_annotation" =>
    let isExc : PyExc → Bool := fun e => e.className != "Boom"
    let r := typeFromAnnotation annWorld isExc "" (← getStr j "s").toList
    pure (encPy (fun (o : Option String) => toJson o) r)
  | "dc_doc" =>
    let name ← getStr j "name"
    let sig : Py String ← match ← getStr j "sig" with
      | "typeerror" => pure (.error (.typeError "sig"))
      | "valueerror" => pure (.error (.valueError "sig"))
      | "keyerror" => pure (.error (.named "KeyError" "'sig'"))
      | s => pure (.ok s)
    let set : Option PyExc := if ← getBool j "setfail" then some (.named "AttributeError" "set") else none
    pure (encPy (fun (o : String) => toJson o) (autoDocGet name sig set))
  | "dc_asdict" =>
    let v ← decDV 8 (← field j "v")
    let f := match ← getStr j "fact" with
      | "dict" => DictFact.dict
      | "dictLike" => .dictLike
      | _ => .list
    pure (encPy encDV (asdictV f v))
  | "dc_astuple" =>
    let v ← decDV 8 (← field j "v")
    let f := if (← getStr j "fact") == "tuple" then TupFact.tuple else .list
    pure (encPy encDV (astupleV f v))
  | "ec_verify_other" => pure (unitJ (verifyCallG evOps id ({} : EClassG EV) id (.ok "int") .cls [.unique]))
  | "eh_class" => runEhClass j
  | "eh_flag_in" => do
    let keys ← decKeys j
    let c ← getCls j
    let v ← field j "v"
    if (← (← v.getArrVal? 0).getStr?) == "member" then
      pure (encPy (fun (b : Bool) => toJson b) (c.containsOf pvOps true (.int 0)))
    else pure (encPy (fun (b : Bool) => toJson b) (c.containsOf pvOps false (← decPV keys v)))
  | "eh_strenum" => do
    let args ← (← getArr j "args").mapM fun a => do
      let k ← (← a.getArrVal? 0).getStr?
      let v ← a.getArrVal? 1
      match k with
      | "str" => pure (SArg.str (α := PV) (← v.getStr?))
      | "bytes" => pure (.bytes (← (← v.getArr?).toList.mapM (·.getNat?)))
      | "bytearray" | "memoryview" => pure (.buffer (← (← v.getArr?).toList.mapM (·.getNat?)))
      | _ => pure (.other (.int (← v.getInt?)))
    pure (encPy (fun (s : String) => toJson s) (strEnumNewG pyCodec pvOps.repr args))
  | "eh_flag_gen" => do
    let keys ← decKeys j
    let start ← match ← field j "start" with
      | .null => pure none
      | s => pure (some (← decPV keys s))
    let last ← (← getArr j "last").mapM (decPV keys)
    pure (encPy encPV (flagGenerateG pvOps start (← getNat j "count") last))
  | "eh_iter" => do
    let c ← getCls j
    let calls ← (← getArr j "calls").mapM (·.getInt?)
    match c.callsC [] calls with
    | .error e => pure (unitJ (.error e))
    | .ok cache =>
      match c.callC cache (← getInt j "v") with
      | .error e => pure (unitJ (.error e))
      | .ok (.plain _, _) => pure (okJ "plain")
      | .ok (.flag v _, cache') =>
        pure (encPy (fun (l : List (Option MapEntry)) => toJson [toJson v,
          toJson (l.map fun m => match m with
            | some (.member n _) => toJson [toJson "member", toJson n]
            | some (.pseudo w n) => toJson [toJson "pseudo", toJson w, toJson n]
            | none => Json.null), toJson (bitCount v)]) (c.iterC cache' v))
  | "eh_bits" => do
    let a ← field j "arg"
    let n ← (← a.getArrVal? 1).getInt?
    let arg := if (← (← a.getArrVal? 0).getStr?) == "int" then BitsArg.int n else .member n s!"<N.X: {n}>"
    pure (encPy (fun (l : List Nat) => toJson l) (iterBitsLsb arg))
  | "eh_verify" => runEhVerify j
  | "eh_call" => do
    let body ← decItems (← getArr j "body")
    match bodyDict "C".toList .plain body with
    | .error e => pure (unitJ (.error e))
    | .ok d =>
      match enumTypeNew .plain d with
      | .error e => pure (unitJ (.error e))
      | .ok c =>
        let value ← decAtom (← field j "value")
        let more ← (← getArr j "more").mapM decAtom
        let kw : CallKw := { type := if ← getBool j "type" then some 0 else none,
                             start := ← decAtom (← field j "start"),
                             boundary := (← getOptStrJ (← field j "boundary")).map (fun s => if s == "strict" then 0 else 1),
                             module := ← getOptStrJ (← field j "module"),
                             qualname := ← getOptStrJ (← field j "qualname") }
        pure (encPy (fun (r : CallOut) => match r with
          | .member n => toJson [toJson "member", nameJ n]
          | .create cn names k => toJson [toJson "create", encAtom cn, names.elim Json.null encAtom, toJson k.type.isSome,
              encAtom k.start, toJson (k.boundary.map (fun b => if b == 0 then "strict" else "keep")), toJson k.module,
              toJson k.qualname])
          (enumCallG evOps c none value more kw .none))
  | _ => throw s!"unknown fn enumdc.{fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.CoreLibs.EnumDC
