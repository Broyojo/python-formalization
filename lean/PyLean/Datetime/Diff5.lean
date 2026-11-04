import PyLean.Datetime.Diff4
import PyLean.Datetime.Misc3Props

/-!
Differential-testing handler for the models of review b666ff1d's rows (`"fn": "x5_..."`): the
class argument of `replace`, `combine`, `fromisoformat`, `utctimetuple` and `astimezone` (a
subclass whose `__new__` raises `Rec` with its arguments, so the call shape is the result),
`__reduce_ex__` with the clinic `int` converter, the separator search against Python's,
`timezone` comparison on every operator, `IsoCalendarDate`, `str()` through `isoformat`,
`datetime.now`'s tz check and the class attributes. See difftest/datetime_x5.py.
-/

namespace PyLean.Datetime

open Lean PyLean PyLean.Diff

/-- A fixed-offset `timezone` of `us` microseconds (`timezone.utc` for zero). -/
def x5Tz (oid : Nat) (us : Int) : Tz := if us = 0 then tzUTC else ⟨oid, .timezone (isoDeltaOfUs us) none⟩

def x5OptTz (oid : Nat) : Option Int → Option Tz
  | none => none
  | some us => some (x5Tz oid us)

def x5EncArg : Arg → String
  | .int n => toString n
  | .none_ => "N"
  | .tz z => "tz" ++ toString z.offsetOf.toUs
  | _ => "?"

/-- The message a recording subclass's `__new__` raises: the positional arguments, then the
`fold` keyword. -/
def x5RecMsg (args : List Arg) (kw : Option Int) : String :=
  ",".intercalate (args.map x5EncArg) ++ ";" ++ (match kw with | none => "-" | some f => "f" ++ toString f)

def x5Rec {α : Type} : SubCall α := fun args kw => .error (.named "Rec" (x5RecMsg args kw))

def x5Env : TzEnv := ⟨fun _ _ => .ok .none, fun _ _ => .ok .none, fun _ _ => .ok .none, fun _ => ""⟩

def x5OffUs : Option Tz → Json
  | none => .null
  | some z => toJson z.offsetOf.toUs

def x5EncDT (v : DT) : Json :=
  Json.arr #[toJson v.y, toJson v.m, toJson v.d, toJson v.h, toJson v.mi, toJson v.s, toJson v.us, toJson v.fold,
    x5OffUs v.tz]

def x5EncTM (v : TM) : Json :=
  Json.arr #[toJson v.h, toJson v.mi, toJson v.s, toJson v.us, toJson v.fold, x5OffUs v.tz]

def x5OptI (j : Json) (key : String) : Except String (Option Int) := getOptInt j key

def x5DT (j : Json) (key : String) : Except String DT := do
  let a ← x4Ints j key
  let tz ← x5OptI j (key ++ "_tz")
  return ⟨a.getD 0 1, a.getD 1 1, a.getD 2 1, a.getD 3 0, a.getD 4 0, a.getD 5 0, a.getD 6 0, a.getD 7 0, x5OptTz 1 tz⟩

def x5TM (j : Json) (key : String) : Except String TM := do
  let a ← x4Ints j key
  let tz ← x5OptI j (key ++ "_tz")
  return ⟨a.getD 0 0, a.getD 1 0, a.getD 2 0, a.getD 3 0, a.getD 4 0, x5OptTz 1 tz⟩

def x5EncState : StateTuple → Json
  | .one b => Json.arr #[toJson b]
  | .two b z => Json.arr #[toJson b, toJson z.offsetOf.toUs]

def runX5 (fn : String) (j : Json) : Except String Json := do
  let sub := (j.getObjValAs? Bool "sub").toOption.getD false
  match fn with
  | "x5_repl" =>
    let kind ← getStr j "kind"
    let f (k : String) := x5OptI j k
    if kind = "date" then
      let v ← x5DT j "v"
      let cls : DateClsC := if sub then .sub x5Rec else .date
      let r := dateReplaceClsC cls v.y v.m v.d ((← f "year").map .int) ((← f "month").map .int) ((← f "day").map .int)
      return encPy (fun (d : DT) => Json.arr #[toJson d.y, toJson d.m, toJson d.d]) r
    else if kind = "time" then
      let t ← x5TM j "v"
      let cls : ClsC TM := if sub then .sub x5Rec else .base
      return encPy x5EncTM (tmReplaceClsC cls t (← f "hour") (← f "minute") (← f "second") (← f "microsecond") (← f "fold") none)
    else
      let v ← x5DT j "v"
      let cls : ClsC DT := if sub then .sub x5Rec else .base
      return encPy x5EncDT (dtReplaceClsC cls v (← f "year") (← f "month") (← f "day") (← f "hour") (← f "minute")
        (← f "second") (← f "microsecond") (← f "fold") none)
  | "x5_combine" =>
    let d ← x4Ints j "date"
    let t ← x5TM j "time"
    let tzk ← getStr j "tzk"
    let tzp : TzParam := match tzk with
      | "omit" => .omitted
      | "none" => .obj .none_
      | _ => .obj (.tz (x5Tz 2 ((j.getObjValAs? Int "tzv").toOption.getD 0)))
    let cls : ClsC DT := if sub then .sub x5Rec else .base
    return encPy x5EncDT (dtCombineClsC cls (.date (d.getD 0 1) (d.getD 1 1) (d.getD 2 1)) (.time t) tzp)
  | "x5_fromiso" =>
    let kind ← getStr j "kind"
    let cps := (← x4Ints j "s").toList.map Int.toNat
    let encTV (v : TimeV) : Json := Json.arr #[toJson v.h, toJson v.mi, toJson v.s, toJson v.us, toJson v.tz]
    if kind = "time" then
      let cls : ClsC TimeV := if sub then .sub x5Rec else .base
      return encPy encTV (timeFromIsoClsC cls (cps.map Char.ofNat))
    else
      let cls : ClsC DateTimeV := if sub then .sub x5Rec else .base
      return encPy (fun (v : DateTimeV) => Json.arr #[toJson v.y, toJson v.m, toJson v.d, encTV v.t])
        (datetimeFromIsoClsC cls cps)
  | "x5_reduce" =>
    let kind ← getStr j "kind"
    let isC := (j.getObjValAs? String "impl").toOption == some "c"
    let p ← x5OptI j "p"
    let enc : Py (Nat × StateTuple) → Json := encPy (fun r => x5EncState r.2)
    if kind = "time" then
      let t ← x5TM j "v"
      match p, isC with
      | none, true => return enc (.ok (tmReduceClsC 0 t))
      | none, false => return enc (.ok (tmReduceExClsPy 0 t 2))
      | some p, true => return enc (tmReduceExClsC 0 t (.int p))
      | some p, false => return enc (.ok (tmReduceExClsPy 0 t p))
    else
      let v ← x5DT j "v"
      match p, isC with
      | none, true => return enc (.ok (dtReduceClsC 0 v))
      | none, false => return enc (.ok (dtReduceExClsPy 0 v 2))
      | some p, true => return enc (dtReduceExClsC 0 v (.int p))
      | some p, false => return enc (.ok (dtReduceExClsPy 0 v p))
  | "x5_sep" =>
    let cs := (← x4Ints j "s").toList.map (fun n => Char.ofNat n.toNat)
    let isC := (j.getObjValAs? String "impl").toOption == some "c"
    if isC then
      let r := findSepC (utf8 cs)
      return encPy (fun (n : Int) => toJson n)
        (if r = -1 then .error (.valueError "Invalid ISO string") else .ok r)
    else
      return encPy (fun (n : Nat) => toJson n) (findSepPy cs)
  | "x5_tzcmp" =>
    let a ← getInt j "a"
    let b ← x5OptI j "b"
    let op ← getStr j "op"
    let isC := (j.getObjValAs? String "impl").toOption == some "c"
    let cop : CmpOp := match op with
      | "lt" => .lt | "le" => .le | "eq" => .eq | "ne" => .ne | "gt" => .gt | _ => .ge
    let r := if isC then timezoneRichObjC cop (isoDeltaOfUs a) (b.map isoDeltaOfUs)
      else timezoneRichObjPy cop (isoDeltaOfUs a) (b.map isoDeltaOfUs)
    return Json.mkObj [("ok", match r with | none => .null | some v => toJson v)]
  | "x5_utctt" =>
    let v ← x5DT j "v"
    let cls : DtType := if sub then .sub 0 x5Rec else .base
    match dtUtctimetupleObjC x5Env cls v with
    | some r => return encPy (fun (t : TimeTuple) => toJson t) r
    | none => throw "undefined"
  | "x5_astz" =>
    let v ← x5DT j "v"
    let tgt ← getInt j "target"
    let cls : DtType := if sub then .sub 0 x5Rec else .base
    match dtAstimezoneObjC x5Env (fun _ => .error .modelFuel) 5 6 (builtinFromutcObj x5Env) cls v (.tz (x5Tz 2 tgt)) with
    | some r => return encPy (fun (o : DtAny) => match o with
        | .dt _ w => x5EncDT w
        | .other ty => toJson ty) r
    | none => throw "undefined"
  | "x5_isocal" =>
    let a ← x4Ints j "args"
    let t := isoCalTupC (.int (a.getD 0 0)) (.int (a.getD 1 0)) (.int (a.getD 2 0))
    return encPy id (do
      let t ← t
      return Json.arr #[toJson (← isoCalYearC t), toJson (← isoCalWeekC t), toJson (← isoCalWeekdayC t),
        toJson (isoCalReduceC t)])
  | "x5_str" =>
    let v ← x5DT j "v"
    let ov ← getBool j "override"
    let isC := (j.getObjValAs? String "impl").toOption == some "c"
    let meth : IsoformatMeth := if ov then
        fun pos kw => .ok ("P" ++ ",".intercalate (pos.map x5EncArg') ++ "K" ++ ",".intercalate (kw.map (·.1)))
      else builtinIsoformat x5Env v
    return encPy (fun (s : String) => toJson s) (if isC then datetimeStrC meth else datetimeStrPy meth)
  | "x5_now" =>
    return encPy (fun (_ : Unit) => Json.null) (datetimeNowC (fun _ => .error .modelFuel) (fun _ x => .ok x) .other)
  | "x5_init" =>
    return encPy (fun (a : ClassAttrs) => Json.arr #[x4EncD a.tdMin, x4EncD a.tdMax, x4EncD a.tdRes,
        toJson [a.dMin.1, a.dMin.2.1, a.dMin.2.2], toJson [a.dMax.1, a.dMax.2.1, a.dMax.2.2], x4EncD a.dRes,
        x5EncTM a.tMin, x5EncTM a.tMax, x4EncD a.tRes, x5EncDT a.dtMin, x5EncDT a.dtMax, x4EncD a.dtRes,
        toJson a.tzUtc.toUs, toJson a.tzMin.toUs, toJson a.tzMax.toUs]) initTypesC
  | _ => throw s!"unknown fn {fn}"
where
  /-- A `str` argument as the override sees it (its code points as text). -/
  x5EncArg' : Arg → String
    | .str cs => String.ofList (cs.map (fun n => Char.ofNat n))
    | a => x5EncArg a

end PyLean.Datetime
