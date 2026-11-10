import PyLean.Datetime.DiffObj
import PyLean.Datetime.Misc2Props

/-!
Differential-testing handler for the models added after review 50b4b958 (`"fn": "x2_..."`):
`tzinfo.__reduce__`, `isoformat(sep)`, `replace`/`combine` on any argument, the `timezone`
argument checks, `__getinitargs__`, pickling round trips, `repr` with the class,
`IsoCalendarDate`, `fromisoformat`/`__format__`/`astimezone` argument checks, and `_mktime`
over a fixed-offset `localtime`.
-/

namespace PyLean.Datetime

open Lean PyLean PyLean.Diff

/-- An optional field: absent is `none`, otherwise the `Arg` (JSON `null` is `None`). -/
def optArg (j : Json) (k : String) : Except String (Option Arg) :=
  match j.getObjVal? k with
  | .error _ => .ok none
  | .ok v => some <$> decArg v

/-- `"tzp"`: `"O"` omitted, `"T"` the object `True`, otherwise an encoded `Arg`. -/
def decTzParam (j : Json) : Except String TzParam := do
  match ← field j "tzp" with
  | .str "O" => pure .omitted
  | .str "T" => pure .true_
  | v => .obj <$> decArg v

def encArgItem : Arg → Json
  | .int n => Json.arr #[toJson "i", toJson n]
  | _ => Json.arr #[toJson "x"]

def reduceAttr (kind : String) : Py (Option (InitArgsObj (List Int))) :=
  match kind with
  | "absent" => .ok none
  | "none" => .ok (some ⟨.ok false, .error (.typeError "~'NoneType' object is not callable")⟩)
  | "zero" => .ok (some ⟨.ok false, .error (.typeError "~'int' object is not callable")⟩)
  | "method" => .ok (some ⟨.ok true, .ok [5]⟩)
  | "falsy" => .ok (some ⟨.ok false, .ok [5]⟩)
  | "raises" => .ok (some ⟨.ok true, .error (.valueError "gi")⟩)
  | _ => .ok (some ⟨.error (.valueError "bool"), .ok [5]⟩)

def encReduce (r : ReduceArgs (List Int) × Unit) : Json :=
  match r.1 with
  | .empty => toJson ([] : List Int)
  | .obj l => toJson l

def encInitArgs : TzInitArgs → Json
  | .one o => Json.arr #[encD o]
  | .two o n => Json.arr #[encD o, toJson n]

def encState (s : StateTuple) : Json :=
  match s with
  | .one b => Json.arr #[toJson b, .null]
  | .two b z => Json.arr #[toJson b, toJson z.oid]

/-- `localtime` of a zone with a fixed offset `off`: the UTC fields of `u + off`. -/
def fixedLocal (off : Int) (u : Int) : Py LocalTm := do
  let s := u + off
  let (y, m, d) ← fromordinalPy (s / 86400 + 719163)
  let r := s % 86400
  return (y, m, d, r / 3600, r % 3600 / 60, r % 60)

def reprCls (j : Json) (name : String) : ReprCls :=
  match (j.getObjValAs? Nat "cls").toOption.getD 0 with
  | 1 => .sub "__main__" name name
  | 2 => .sub "__main__" ("Outer." ++ name) name
  | _ => .base

def decTzMethArg (j : Json) : Except String TzMethArg := do
  let a ← (← field j "arg").getArr?
  match ← (a.getD 0 .null).getStr? with
  | "dt" => .dt <$> decDT (a.getD 1 .null)
  | "none" => pure .none_
  | _ => pure .other

def runX2 (fn : String) (j : Json) : Except String Json := do
  let isC := (j.getObjValAs? String "impl").toOption == some "c"
  let env := testEnv isC
  match fn with
  | "x2_reduce" =>
    let attr := reduceAttr (← getStr j "kind")
    return encPy encReduce ((if isC then tzinfoReduceC else tzinfoReducePy) attr (.ok ()))
  | "x2_iso_sep" =>
    let a ← decDT (← field j "a"); let sep ← decArg (← field j "sep")
    return encPy toJson ((if isC then dtIsoformatArgC else dtIsoformatArgPy) env a sep .auto)
  | "x2_tm_replace" =>
    let a ← decTM (← field j "a"); let tz ← decTzParam j
    let r := (if isC then tmReplaceArgC else tmReplaceArgPy) a (← optArg j "nh") (← optArg j "nmi")
      (← optArg j "ns") (← optArg j "nus") tz (← optArg j "nfold")
    return encPy encTMv r
  | "x2_dt_replace" =>
    let a ← decDT (← field j "a"); let tz ← decTzParam j
    let r := (if isC then dtReplaceArgC else dtReplaceArgPy) a (← optArg j "ny") (← optArg j "nm")
      (← optArg j "nd") (← optArg j "nh") (← optArg j "nmi") (← optArg j "ns") (← optArg j "nus") tz
      (← optArg j "nfold")
    return encPy encDTv r
  | "x2_combine" =>
    let da ← (← field j "d").getArr?
    let d : DateObj ← match ← (da.getD 0 .null).getStr? with
      | "d" => do let v ← getYMD (Json.mkObj [("v", da.getD 1 .null)]) "v"; pure (.date v.1 v.2.1 v.2.2)
      | "dt" => do let v ← decDT (da.getD 1 .null); pure (.date v.y v.m v.d)
      | _ => pure .other
    let ta ← (← field j "t").getArr?
    let t : TimeObj ← match ← (ta.getD 0 .null).getStr? with
      | "t" => .time <$> decTM (ta.getD 1 .null)
      | _ => pure .other
    let tz ← decTzParam j
    return encPy encDTv ((if isC then dtCombineArgC else dtCombineArgPy) d t tz)
  | "x2_tz_meth" =>
    let some tz := ← decTz (← field j "tz") | throw "tz"
    let .timezone off name := tz.kind | throw "not a timezone"
    let a ← decTzMethArg j
    match ← getStr j "meth" with
    | "utcoffset" => return encPy encD ((if isC then timezoneUtcoffsetArgC else timezoneUtcoffsetArgPy) off a)
    | "dst" => return encPy encOffOpt (if isC then timezoneDstArgC a else timezoneDstArgPy a)
    | "tzname" =>
      return encPy toJson (if isC then timezoneTznameArgC tz.oid off name a else timezoneTznameArgPy off name a)
    | _ => return encPy encDTv ((if isC then timezoneFromutcArgC else timezoneFromutcArgPy) tz off a)
  | "x2_tz_new_arg" =>
    -- "sub": the offset is an instance of a timedelta subclass; for `__bool__`, `__ge__` and
    -- `__le__` in turn, "inh" (not overridden), "t", "f" (returns that) or "r" (raises).
    let how (v : Json) (tag : String) (inherited : Bool) : Except String (Py Bool) := do
      match ← v.getStr? with
      | "inh" => pure (.ok inherited)
      | "t" => pure (.ok true)
      | "f" => pure (.ok false)
      | _ => pure (.error (.named "RuntimeError" tag))
    let off : TzOffsetArg ← match (← field j "td") with
      | .null => pure .other
      | v => do
        let o ← decDelta v
        match j.getObjVal? "sub" with
        | .error _ => pure (.delta o)
        | .ok sub =>
          let a ← sub.getArr?
          let truth ← how (a.getD 0 .null) "bool" o.bool
          let ge ← how (a.getD 1 .null) "ge" (decide (-86399999999 ≤ o.toUs))
          let le ← how (a.getD 2 .null) "le" (decide (o.toUs ≤ 86399999999))
          pure (.sub o truth ge le)
    let name : TzName ← match j.getObjVal? "name" with
      | .error _ => pure .omitted
      | .ok v => match v.getStr? with
        | .ok s => pure (.str s)
        | .error _ => pure .other
    return encPy encTzFull ((if isC then timezoneNewObjC else timezoneNewObjPy) 1 off name)
  | "x2_tz_initargs" =>
    let some tz := ← decTz (← field j "tz") | throw "tz"
    let .timezone off name := tz.kind | throw "not a timezone"
    let args := if isC then timezoneGetinitargsC off name else timezoneGetinitargsPy off name
    let rt : Py Tz := match args with
      | .one o => (if isC then timezoneNewC else timezoneNewPy) 9 o .omitted
      | .two o n => (if isC then timezoneNewC else timezoneNewPy) 9 o (.str n)
    let same : Bool := match rt with
      | .ok t => t.kind == tz.kind
      | .error _ => false
    let hk := if isC then timezoneHashKeyC off else timezoneHashKey off
    return Json.arr #[encInitArgs args, toJson (hk == off.hashKey), toJson same]
  | "x2_tm_reduce" =>
    let a ← decTM (← field j "a")
    let st : StateTuple := match (j.getObjValAs? Int "proto").toOption with
      | some p => if isC then tmReduceExC a p else tmReduceExPy a p
      | none => if isC then tmReduceC a else tmReducePy a
    let rt := if isC then timeNewC st.args (.int 0) else timeCallPy st.args (.int 0)
    return Json.arr #[encState st, encPy encTMv rt]
  | "x2_dt_reduce" =>
    let a ← decDT (← field j "a")
    let st : StateTuple := match (j.getObjValAs? Int "proto").toOption with
      | some p => if isC then dtReduceExC a p else dtReduceExPy a p
      | none => if isC then dtReduceC a else dtReducePy a
    let rt := if isC then datetimeNewC st.args (.int 0) else datetimeCallPy st.args (.int 0)
    return Json.arr #[encState st, encPy encDTv rt]
  | "x2_tm_repr_cls" =>
    let a ← decTM (← field j "a")
    return toJson ((if isC then tmReprClsC else tmReprClsPy) env (reprCls j "TSub") a)
  | "x2_dt_repr_cls" =>
    let a ← decDT (← field j "a")
    return toJson ((if isC then dtReprClsC else dtReprClsPy) env (reprCls j "DTSub") a)
  | "x2_isocal" =>
    let args ← getArgs j "args"
    let r := (if isC then isoCalNewC else isoCalNewPy) (args.getD 0 .none_) (args.getD 1 .none_) (args.getD 2 .none_)
    return encPy (fun v => Json.arr #[encArgItem v.1, encArgItem v.2.1, encArgItem v.2.2]) r
  | "x2_fromiso_arg" =>
    let k ← getStr j "arg"
    if (← getStr j "cls") = "time" then
      let a : IsoArg := if k = "u" then .surrogateStr else .other
      return encPy (fun _ => .null) ((if isC then timeFromIsoArgC else timeFromIsoArgPy) a)
    else return encPy (fun _ => .null) ((if isC then datetimeFromIsoArgC else datetimeFromIsoArgPy) .other)
  | "x2_tm_format" =>
    let a ← decTM (← field j "a")
    let fmt : FmtArg := match j.getObjVal? "f" with
      | .ok .null => .other
      | .error _ => .other
      | .ok v => match v.getArr? with
        | .ok arr => .str (arr.toList.map (fun x => Char.ofNat ((x.getNat?).toOption.getD 0)))
        | .error _ => .other
    let str := (if isC then tmIsoformatC else tmIsoformatPy) env a .auto
    let strf : List Char → Py String := fun _ => .ok "S"
    let r := (if isC then timeFormatC else timeFormatPy) fmt str strf
    return encPy (fun s => match s with | .inl x => toJson x | .inr x => toJson x) r
  | "x2_astz_arg" =>
    let a ← decDT (← field j "a")
    return encPy (fun _ => .null) ((if isC then dtAstimezoneArgC else dtAstimezoneArgPy) env a .other)
  | "x2_mktime" =>
    let a ← decDT (← field j "a"); let off ← getInt j "off"
    return encPy toJson ((if isC then dtLocalToSecondsC else dtMktimePy) (fixedLocal off) a)
  | other => throw s!"unknown fn {other}"

end PyLean.Datetime
