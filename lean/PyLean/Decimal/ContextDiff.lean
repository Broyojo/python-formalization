import PyLean.DiffCore
import PyLean.Decimal.CContext

/-!
Difftest cases for the `Context` layer: `Context` methods on `Arg` operands,
reflected operators, `Context()` from a modified `DefaultContext`, attributes,
`SignalDict` over real condition bits, `IEEEContext` and `localcontext`.
-/

namespace PyLean.Decimal

open Lean PyLean PyLean.Diff

/-! ## The keyword form of `localcontext` in `_decimal` -/

/-- `_decimal.localcontext`'s keywords, _decimal.c:2051-2062: the clinic parser
refuses an unknown keyword before any field is set. -/
def cInitOfKwargs (kw : List (String × CtxArg)) : Py CtxInit := do
  if kw.any (fun p => !contextAttributes.contains p.1) then
    throw (.typeError "~is an invalid keyword argument")
  let get (k : String) : CtxArg := (kw.lookup k).getD .none
  return { prec := get "prec", rounding := get "rounding", emin := get "Emin", emax := get "Emax"
           capitals := get "capitals", clamp := get "clamp", flags := get "flags", traps := get "traps" }

/-! ## Decoding -/

/-- `RuntimeError("boom")`, what the difftest's raising `__str__`/`__repr__`/`__eq__` raise. -/
def boom : PyExc := .named "RuntimeError" "boom"

/-- What `str()` of a tuple element or plain object raises: `"h"`, `10**5000`; `"r"`, an object
whose `__str__` raises `boom`; anything else prints. -/
def strKindOf (j : Json) : Except String StrErr :=
  match j.getStr? with
  | .ok "h" => pure (intStrErr (10 ^ 5000))
  | .ok "r" => pure (some boom)
  | _ => pure none

/-- What the difftest's `EqKey.__eq__` answers for one signal: `y`, `n`, `i` (NotImplemented, so
unequal) or `r` (raises `boom`). -/
def eqAnsOf (c : Char) : EqAns :=
  match c with
  | 'y' => .yes
  | 'r' => .raises boom
  | _ => .no

def sigKeyOf (j : Json) : Except String SigKey := do
  -- `["eq", answers]`: an `EqKey`, hashable by identity, whose `__eq__` answers the nine signals
  if let .ok a := j.getArr? then
    return .other none none ((← (a[1]!).getStr?).toList.map eqAnsOf)
  let s ← j.getStr?
  -- `5`, an int; `hugeint`, `10**5000` (its repr raises the limit); `unhash`, `[]` (unhashable);
  -- `badrepr`, an object whose repr raises RuntimeError("boom").
  if s == "other" then return .other
  if s == "hugeint" then return intKey (10 ^ 5000)
  if s == "unhash" then return .other none (some (.typeError "unhashable type: 'list'"))
  if s == "badrepr" then return .other (some boom) none
  return .sig (← signalOfName s)
where
  signalOfName (s : String) : Except String Signal :=
    match pySignals.find? (fun x => x.name == s) with
    | some x => pure x
    | none => throw s!"bad signal {s}"

/-- The kind of a list element of the difftest: `eq` for an `EqKey`, else its name. -/
def keyKind (j : Json) : String :=
  match j.getArr? with
  | .ok _ => "eq"
  | .error _ => match j.getStr? with
    | .ok s => s
    | .error _ => ""

/-- The elements of a list passed as `flags` or `traps`, with what they answer against each other
and their hashes (`SigKey.other`'s `hv` and `prev`): `5` (`other`, one cached object) equals and
hashes as every other `5`; `10**5000` (`hugeint`) equals every other `10**5000`, with one hash;
`[]` (`unhash`) equals every other `[]` (unhashable, so no dict comparison); an object whose repr
raises (`badrepr`) is equal only to itself and hashes by identity. An `EqKey` at position `i`
(`["eq", answers, hv, prevs]`) hashes to `hv` (`null` or absent: by identity) and answers
`prevs[i']` against the `EqKey` at an earlier position `i'` (`y`, `n`, `r` raises `boom`, `i`
NotImplemented both ways, so unequal), and NotImplemented against anything else. An
identity hash is a value no other element has (`-(1000 + i)`). -/
def listKeysOf (js : List Json) : Except String (List SigKey) := do
  let kinds := js.map keyKind
  let mut out : List SigKey := []
  let mut i : Nat := 0
  for j in js do
    let k ← sigKeyOf j
    let kind := kinds.getD i ""
    let uniq : Int := -(1000 + (i : Int))
    let same (kd : String) : List EqAns :=
      (List.range i).map (fun i' => if kinds.getD i' "" == kd then .yes else .no)
    let k' : SigKey := match k with
      | .sig s => .sig s
      | .other r h eq _ _ =>
        if kind == "other" then .other r h eq 5 (same "other")
        else if kind == "hugeint" then .other r h eq (-1) (same "hugeint")
        else if kind == "unhash" then .other r h eq 0 (same "unhash")
        else if kind == "eq" then
          let a := (j.getArr?.toOption.getD #[])
          let hv : Int := match a[2]? with
            | some v => match v.getInt? with
              | .ok n => n
              | .error _ => uniq
            | none => uniq
          let ps : List Char := match a[3]? with
            | some v => (v.getStr?.toOption.getD "").toList
            | none => []
          .other r h eq hv ((List.range i).map (fun i' =>
            if kinds.getD i' "" == "eq" then eqAnsOf (ps.getD i' 'n') else .no))
        else .other r h eq uniq []
    out := out ++ [k']
    i := i + 1
  return out

/-- A dict value: `true`/`false`, or `"huge"`, `10**5000` (true, its repr raising the limit). -/
def sigValOf (j : Json) : Except String SigVal :=
  match j.getBool? with
  | .ok b => pure { truth := b }
  | .error _ => pure { truth := true, repr := intStrErr (10 ^ 5000) }

def hexNat (s : List Char) : Nat := s.foldl (fun a c =>
  a * 16 + (if c.toNat ≥ 97 then c.toNat - 87 else c.toNat - 48)) 0

/-- `hex(i)` back to the int, sign included. -/
def intOfHex (s : String) : Int :=
  match s.toList with
  | '-' :: '0' :: 'x' :: ds => -(hexNat ds : Int)
  | '0' :: 'x' :: ds => hexNat ds
  | _ => 0

/-- An int as `hex(i)`. -/
def ctxHex (i : Int) : Json :=
  toJson (String.ofList ((if i < 0 then ['-'] else []) ++ ['0', 'x'] ++ Nat.toDigits 16 i.natAbs))

def ctxArgOf (j : Json) : Except String CtxArg := do
  match j with
  | .null => return .none
  | _ =>
    let a ← j.getArr?
    let tag ← (a[0]!).getStr?
    match tag with
    | "int" => return .int ((← (a[1]!).getStr?).toInt?.getD 0)
    | "str" => return .str (← (a[1]!).getStr?)
    | "list" => return .list (← listKeysOf (← (a[1]!).getArr?).toList)
    | "dict" | "frozendict" | "frozendict_py" =>
      let pairs ← (← (a[1]!).getArr?).toList.mapM (fun p => do
        let q ← p.getArr?
        return ((← sigKeyOf q[0]!), (← sigValOf q[1]!)))
      -- `_pydecimal` takes a frozendict for a plain object (not a `dict`), whose `str()` is the
      -- dict's repr
      if tag == "frozendict_py" then return .obj (dictReprErr pairs)
      return .dict pairs
    | "obj" => return .obj (← strKindOf (a.getD 1 Json.null))
    | "tuple" => return .tuple (← (← (a[1]!).getArr?).toList.mapM strKindOf)
    | "idx" => return .int ((← (a[1]!).getStr?).toInt?.getD 0)
    | "hint" => return .int (intOfHex (← (a[1]!).getStr?))
    | "bool" => return .bool (← (a[1]!).getBool?)
    | "none" => return .none
    | "eqobj" =>
      let ans ← (← (a[1]!).getArr?).toList.mapM (fun x => do
        match ← x.getStr? with
        | "y" => pure EqAns.yes
        | "r" => pure (EqAns.raises (.named "RuntimeError" "boom"))
        | _ => pure EqAns.no)
      return .eqObj 0 ans (← strKindOf (a.getD 2 Json.null))
    | t => throw s!"bad ctx arg {t}"

def ctxInitOf (j : Json) : Except String CtxInit := do
  let get (k : String) : Except String CtxArg :=
    match j.getObjVal? k with
    | .ok v => ctxArgOf v
    | .error _ => pure .none
  return { prec := ← get "prec", rounding := ← get "rounding", emin := ← get "Emin", emax := ← get "Emax"
           capitals := ← get "capitals", clamp := ← get "clamp", flags := ← get "flags", traps := ← get "traps" }

def namesOf (j : Json) : Except String (List Signal) := do
  let ks ← (← j.getArr?).toList.mapM sigKeyOf
  return ks.filterMap (fun k => match k with
    | .sig s => some s
    | .other .. => none)

/-- A `DefaultContext` state, for each twin. -/
def templateOf (j : Json) : Except String (PyContext × CContext) := do
  let i (k : String) : Except String Int := do
    match (← (← j.getObjVal? k).getStr?).toInt? with
    | some v => pure v
    | none => throw "bad int"
  let r ← (← j.getObjVal? "rounding").getStr?
  let some rounding := roundingOfName r | throw "bad rounding"
  let fl ← namesOf (← j.getObjVal? "flags")
  let tr ← namesOf (← j.getObjVal? "traps")
  let py : PyContext :=
    { prec := ← i "prec", rounding := rounding, emin := ← i "Emin", emax := ← i "Emax"
      capitals := ← i "capitals", clamp := ← i "clamp"
      flags := pySignals.map (fun s => (s, fl.contains s))
      traps := pySignals.map (fun s => (s, tr.contains s)), ignored := [] }
  let bits (l : List Signal) : Status := l.foldl (fun st s => orBits st s.flagBits) []
  let cc : CContext :=
    { prec := py.prec, emax := py.emax, emin := py.emin, traps := bits tr, status := bits fl
      round := rounding, clamp := py.clamp, capitals := py.capitals }
  return (py, cc)

/-! ## Encoding -/

def sortStrs (l : List String) : Json := toJson (l.toArray.qsort (· < ·))

def encPyContext (c : PyContext) : Json :=
  Json.mkObj [("prec", ctxHex c.prec),
    ("rounding", toJson (if c.roundingObj.isSome then "obj" else c.rounding.name)),
    ("Emin", ctxHex c.emin), ("Emax", ctxHex c.emax),
    ("capitals", ctxHex c.capitals), ("clamp", ctxHex c.clamp),
    ("flags", sortStrs (setNames c.flags)), ("traps", sortStrs (setNames c.traps)),
    ("xf", toJson c.flagsExtra.length), ("xt", toJson c.trapsExtra.length)]

def encCContext (c : CContext) : Json :=
  Json.mkObj [("prec", ctxHex c.prec), ("rounding", toJson c.round.name),
    ("Emin", ctxHex c.emin), ("Emax", ctxHex c.emax),
    ("capitals", ctxHex c.capitals), ("clamp", ctxHex c.clamp),
    ("flags", sortStrs ((signalsAsList c.status).map Signal.name)),
    ("traps", sortStrs ((signalsAsList c.traps).map Signal.name)), ("xf", toJson 0), ("xt", toJson 0)]

/-! ## Actions that set condition bits -/

/-- The bits an action sets on a `Context(traps=[])`, and the signals `_pydecimal` flags. -/
def actionBits : String → Status
  | "div00" => [.divisionUndefined]
  | "conv" => [.conversionSyntax]
  | "impossible" => [.divisionImpossible]
  | "invalid" => [.invalidOperation]
  | "inexact" => [.inexact, .rounded]
  | "divzero" => [.divisionByZero]
  | _ => []

def actionSignals : String → List Signal
  | "inexact" => [.inexact, .rounded]
  | "divzero" => [.divisionByZero]
  | "" => []
  | _ => [.invalidOperation]

def statusOfActs (acts : List String) : Status :=
  acts.foldl (fun st a => orBits st (actionBits a)) []

/-- `Context(traps=[])`, the context the actions run in. -/
def noTrapsPy : PyContext :=
  { defaultContext with traps := pySignals.map (fun s => (s, false)) }

def noTrapsC (st : Status) : CContext := { dfltCtx with traps := [], status := st }

def flagsAfterPy (acts : List String) : PyContext :=
  let sigs := acts.flatMap actionSignals
  { noTrapsPy with flags := pySignals.map (fun s => (s, sigs.contains s)) }

/-- `signaldict` operations of the difftest. -/
def runSd (op : String) (sd : SigObj) (key : SigKey) (w : SdOperand) : Json :=
  match op with
  | "len" => encPy (fun (n : Nat) => toJson n) (signaldictLen sd)
  | "iter" => encPy (fun (l : List Signal) => toJson (l.map Signal.name)) (signaldictIter sd)
  | "get" => encPy (fun (b : Bool) => toJson b) (signaldictGetitem sd key)
  | "set" =>
    encPy (fun (st : Status) => toJson ((signalsAsList st).map Signal.name))
      (signaldictSetitem sd key (some true))
  | "clear" =>
    encPy (fun (st : Status) => toJson ((signalsAsList st).map Signal.name))
      (signaldictSetitem sd key (some false))
  | "del" =>
    encPy (fun (st : Status) => toJson ((signalsAsList st).map Signal.name))
      (signaldictSetitem sd key none)
  | "repr" => encPy (fun (s : String) => toJson s) (signaldictRepr sd)
  | "copy" => encPy (fun (d : SigDict) => toJson ((d.filter (·.2)).map (fun p => p.1.name))) (signaldictCopy sd)
  | "eq" => encPy (fun (o : Option Bool) => match o with
      | some b => toJson b
      | none => toJson "NotImplemented") (signaldictRichcompare sd w false)
  | "ne" => encPy (fun (o : Option Bool) => match o with
      | some b => toJson b
      | none => toJson "NotImplemented") (signaldictRichcompare sd w true)
  | _ => Json.null

end PyLean.Decimal
