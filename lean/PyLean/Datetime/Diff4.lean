import PyLean.Datetime.Diff3
import PyLean.Datetime.DeltaObjProps
import PyLean.Datetime.SubclassCtor
import PyLean.Datetime.IsoformatCProps

/-!
Differential-testing handler for the models added after review cbc4b092 (`"fn": "x4_..."`):
C timedelta objects (class, `zero_delta`, `__reduce__`), `microseconds_to_delta` on what an int
subclass's `__mul__` returns, the `*` and `/` dispatch, `timezone(0, name)` identity, `str()`
through `isoformat`, `replace()` on a subclass whose constructor takes no `fold`, and
`date.fromtimestamp` on ints, floats and a `str`. See difftest/datetime_x4.py.
-/

namespace PyLean.Datetime

open Lean PyLean PyLean.Diff

def x4Ints (j : Json) (key : String) : Except String (Array Int) := do
  let arr ← (← field j key).getArr?
  arr.mapM (·.getInt?)

def x4Delta (j : Json) (key : String) : Except String Delta := do
  let a ← x4Ints j key
  return ⟨a.getD 0 0, a.getD 1 0, a.getD 2 0⟩

def x4EncD (t : Delta) : Json := Json.arr #[toJson t.days, toJson t.seconds, toJson t.us]

/-- `["td", [d, s, us]]`, `["i", n]`, `["f", bits]` or `["o"]`. -/
def x4Op (j : Json) : Except String PlainOp := do
  let a ← j.getArr?
  match ← (a.getD 0 .null).getStr? with
  | "td" =>
    let v ← (a.getD 1 .null).getArr?
    let ints ← v.mapM (·.getInt?)
    return .td ⟨ints.getD 0 0, ints.getD 1 0, ints.getD 2 0⟩
  | "i" => return .int (← (a.getD 1 .null).getInt?)
  | "f" => return .float (Binary64.F64.ofBits (← (a.getD 1 .null).getNat?))
  | _ => return .other

/-- A float object whose `divmod` gives two floats (the `2.5` an `I.__mul__` returns). -/
def x4FloatObj : PObj :=
  .other "float" none (fun _ => .pair (.other "float" none (fun _ => .raise .modelFuel))
    (.other "float" none (fun _ => .raise .modelFuel)))

/-- What `I.__mul__` returns in the `x4_mulsub` cases, for the microseconds `u`. -/
def x4MulObj (kind : String) (n q r u : Int) : PObj :=
  match kind with
  | "int" => .int (n * u)
  | "float" => x4FloatObj
  | "nontuple" => .other "R" none (fun _ => .nontuple "int")
  | "tuple3" => .other "R" none (fun _ => .tupleOf 3)
  | "range" => .other "R" none (fun _ => .pair (.int q) (.int (1000000 + r.natAbs)))
  | "pairf" => .other "R" none (fun _ => .pair (.int q) x4FloatObj)
  | _ => .other "R" none (fun _ => .pair (.int q) (.int (r.natAbs % 1000000)))

def x4EncOptTd : Option Delta → Json
  | none => .null
  | some v => Json.arr #[toJson "td", x4EncD v]

def x4EncDiv : Option (Sum Delta LongObj.Cplx.Dbl) → Json
  | none => .null
  | some (.inl v) => Json.arr #[toJson "td", x4EncD v]
  | some (.inr _) => Json.arr #[toJson "?", toJson "float"]

/-- The constructor of the `x4_replsub` subclass `S`: with a keyword it refuses unless it
accepts `fold`, then `base.__new__(cls, *a, **kw)`. -/
def x4SubDT (accepts : Bool) : SubCall DT := fun args kw =>
  if kw.isSome ∧ ¬ accepts then .error (.typeError "~__new__() got an unexpected keyword argument 'fold'")
  else match args with
    | [.int y, .int m, .int d, .int h, .int mi, .int s, .int us, tz] =>
      datetimeDatetimeImplC y m d h mi s us tz (kw.getD 0)
    | _ => .error .modelFuel

def x4SubTM (accepts : Bool) : SubCall TM := fun args kw =>
  if kw.isSome ∧ ¬ accepts then .error (.typeError "~__new__() got an unexpected keyword argument 'fold'")
  else match args with
    | [.int h, .int mi, .int s, .int us, tz] => datetimeTimeImplC h mi s us tz (kw.getD 0)
    | _ => .error .modelFuel

/-- The clock of the difftest process for `date.fromtimestamp`: `TZ=XXX-2`. -/
def x4Clock : Clock where
  otherTimeT _ := .error .modelFuel
  now := .error .modelFuel
  localtime u := do
    let (y, m, d, _, _, _) ← fixedLocal 7200 u
    return (y, m, d)

def runX4 (fn : String) (j : Json) : Except String Json := do
  let isC := (j.getObjValAs? String "impl").toOption == some "c"
  match fn with
  | "x4_tdobj" =>
    let a ← x4Ints j "args"
    let sub ← getBool j "sub"
    let g (i : Nat) := a.getD i 0
    if isC then
      return encPy (fun (o : TdObjC) => Json.arr #[x4EncD o.val, toJson (decide (o = .zeroSingleton)), toJson (decide (o.cls ≠ .base))])
        (deltaObjC (if sub then .sub 1 else .base) (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6))
    else
      return encPy (fun (v : Delta) => Json.arr #[x4EncD v, toJson false, toJson sub])
        (deltaPy (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6))
  | "x4_reduce" =>
    let a ← x4Delta j "a"
    let sub ← getBool j "sub"
    let cls : TdCls := if sub then .sub 1 else .base
    if isC then
      let r : Py Json := do
        let o ← deltaObjC cls a.days a.seconds a.us 0 0 0 0
        let (k, args) := o.reduceC
        let back ← deltaObjC k (args.getD 0 0) (args.getD 1 0) (args.getD 2 0) 0 0 0 0
        return Json.arr #[toJson (decide (k ≠ .base)), toJson args, x4EncD back.val, toJson (decide (back.cls ≠ .base)),
          toJson (decide (back = .zeroSingleton))]
      return encPy id r
    else
      let r : Py Json := do
        let v ← deltaPy a.days a.seconds a.us 0 0 0 0
        let (_, args) := v.reducePy cls
        let back ← deltaPy (args.getD 0 0) (args.getD 1 0) (args.getD 2 0) 0 0 0 0
        return Json.arr #[toJson sub, toJson args, x4EncD back, toJson sub, toJson false]
      return encPy id r
  | "x4_mulsub" =>
    let a ← x4Delta j "a"
    let kind ← getStr j "kind"
    let n ← getInt j "n"
    let q ← getInt j "q"
    let r ← getInt j "r"
    if isC then
      return encPy (fun (o : TdObjC) => x4EncD o.val)
        (multiplyIntTimedeltaC ⟨n, fun u => .ok (x4MulObj kind n q r u)⟩ a)
    else return encPy x4EncD (a.mulPy n)
  | "x4_mul" =>
    let l ← x4Op (← field j "l")
    let r ← x4Op (← field j "r")
    if isC then return encPy x4EncOptTd ((Option.map TdObjC.val) <$> deltaMultiplyC l.op r.op)
    else return encPy x4EncOptTd (deltaMultiplyPy l.op r.op)
  | "x4_div" =>
    let l ← x4Op (← field j "l")
    let r ← x4Op (← field j "r")
    if isC then return encPy x4EncDiv ((Option.map (Sum.map TdObjC.val id)) <$> deltaTruedivideC l.op r.op)
    else return encPy x4EncDiv (deltaTruedividePy l.op r.op)
  | "x4_tzzero" =>
    let off ← x4Delta j "td"
    let name : TzName := match (j.getObjValAs? String "name").toOption with
      | some s => .str s
      | none => .omitted
    let r := (if isC then timezoneNewC else timezoneNewPy) 9 off name
    return encPy (fun (t : Tz) => Json.arr #[toJson (decide (t.oid = 0)), toJson off.toUs]) r
  | "x4_str" =>
    let kind ← getStr j "kind"
    let ov : IsoOverride := if (← getBool j "override") then some (.ok "X") else none
    if kind = "date" then
      let d ← x4Ints j "date"
      let (y, m, dd) := (d.getD 0 0, d.getD 1 0, d.getD 2 0)
      return encPy toJson ((if isC then dateStrC else dateStrPy) y m dd ov)
    else
      let t ← x4Ints j "time"
      let tm : TM := ⟨t.getD 0 0, t.getD 1 0, t.getD 2 0, t.getD 3 0, 0, none⟩
      let env := testEnv isC
      return encPy toJson ((if isC then timeStrC env tm ov else timeStrPy env tm ov))
  | "x4_replsub" =>
    let kind ← getStr j "kind"
    let accepts ← getBool j "accepts"
    let d ← x4Ints j "date"
    let t ← x4Ints j "time"
    let fold : Int := (j.getObjValAs? Int "fold").toOption.getD 0
    if kind = "dt" then
      let day : Int := (j.getObjValAs? Int "day").toOption.getD (d.getD 2 0)
      let args := (d.getD 0 0, d.getD 1 0, day, t.getD 0 0, t.getD 1 0, t.getD 2 0, t.getD 3 0)
      let r := (if isC then newDatetimeSubclassFoldExC else dtClsCallFoldPy)
        args.1 args.2.1 args.2.2.1 args.2.2.2.1 args.2.2.2.2.1 args.2.2.2.2.2.1 args.2.2.2.2.2.2 .none_ fold
        (.sub (x4SubDT accepts))
      -- creating `S(*date, *time)` first: its constructor runs with no keyword
      let first := datetimeDatetimeImplC (d.getD 0 0) (d.getD 1 0) (d.getD 2 0) (t.getD 0 0) (t.getD 1 0)
        (t.getD 2 0) (t.getD 3 0) .none_ 0
      return encPy (fun (v : DT) => toJson [v.y, v.m, v.d, v.h, v.mi, v.s, v.us, v.fold])
        (do let _ ← first; r)
    else
      let r := (if isC then newTimeSubclassFoldExC else tmClsCallFoldPy)
        (t.getD 0 0) (t.getD 1 0) (t.getD 2 0) (t.getD 3 0) .none_ fold (.sub (x4SubTM accepts))
      return encPy (fun (v : TM) => toJson [v.h, v.mi, v.s, v.us, v.fold]) r
  | "x4_fromts" =>
    let a ← (← field j "t").getArr?
    let arg : Arg ← match ← (a.getD 0 .null).getStr? with
      | "i" => pure (.int (← (a.getD 1 .null).getInt?))
      | "f" => pure (.float (Binary64.F64.ofBits (← (a.getD 1 .null).getNat?)))
      | _ => pure (.str [120])
    let r := (if isC then dateFromtimestampC else dateFromtimestampPy) x4Clock arg
    return encPy (fun (v : Int × Int × Int) => toJson [v.1, v.2.1, v.2.2]) r
  | _ => throw s!"unknown x4 case {fn}"

end PyLean.Datetime
