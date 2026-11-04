import PyLean.Datetime.Diff2
import PyLean.Datetime.TdFloat

/-!
Differential-testing handler for the models added after review 0506b7c0 (`"fn": "x3_..."`):
`timedelta(...)` on int and float arguments, `astimezone` and `_local_timezone` with the
local zone of the process (a fixed UTC+2 zone named `XXX`, `TZ=XXX-2`), `repr` with a tzinfo
whose `__repr__` raises or returns a non-`str`, and `time`/`datetime` from a `str` pickle state.
-/

namespace PyLean.Datetime

open Lean PyLean PyLean.Diff

/-- `["i", n]`, `["f", bits]` or `["o", type name]`. -/
def decTdNum (j : Json) : Except String TdNum := do
  let a ← j.getArr?
  match ← (a.getD 0 .null).getStr? with
  | "i" => return .int (← (a.getD 1 .null).getInt?)
  | "f" => return .float (Binary64.F64.ofBits (← (a.getD 1 .null).getNat?))
  | _ => return .other (← (a.getD 1 .null).getStr?)

/-- `localtime` of the difftest process: `TZ=XXX-2`, UTC+2 all year, `tm_zone` `XXX`. -/
def fixedZone (u : Int) : Py LocalTmZ := do
  let f ← fixedLocal 7200 u
  return (f, 7200, "XXX")

/-- A result's tzinfo by value for a `timezone`, by identity otherwise. -/
def encTzDesc : Option Tz → Json
  | none => .null
  | some t => match t.kind with
    | .timezone o n => Json.arr #[toJson "tz", toJson o.toUs, encStrOpt n]
    | .custom _ => Json.arr #[toJson "cu", toJson t.oid]

def encDTd (v : DT) : Json :=
  Json.arr #[toJson v.y, toJson v.m, toJson v.d, toJson v.h, toJson v.mi, toJson v.s, toJson v.us,
    toJson v.fold, encTzDesc v.tz]

/-- The `__repr__` of the repr-test tzinfo classes: `R()`, a `KeyError('boom')`, the int 5, and
a `str` subclass instance `S`. -/
def testReprEnv : TzReprEnv
  | 0 => .ok (.str "R()")
  | 1 => .error (.keyError "~boom")
  | 2 => .ok (.other "int")
  | _ => .ok (.str "S")

def runX3 (fn : String) (j : Json) : Except String Json := do
  let isC := (j.getObjValAs? String "impl").toOption == some "c"
  let env := testEnv isC
  match fn with
  | "x3_td" =>
    let a ← (← field j "args").getArr?
    let args ← a.toList.mapM fun x => match x with
      | .null => pure none
      | v => some <$> decTdNum v
    let g (i : Nat) : Option TdNum := args.getD i none
    let r := if isC then deltaNumC (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6)
      else
        let p (i : Nat) : TdNum := (g i).getD (.int 0)
        deltaNumPy (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6)
    return encPy encD r
  | "x3_astz" =>
    let a ← decDT (← field j "a")
    let arg : AstzArg ← match ← field j "tz" with
      | .null => pure .none_
      | .str _ => pure .other
      | v => do
        match ← decTz v with
        | some t => pure (.tz t)
        | none => pure .none_
    let r := (if isC then dtAstimezoneFullC else dtAstimezoneFullPy) env fixedZone 101 102 a arg
    return encPy encDTd r
  | "x3_localtz" =>
    let a ← decDT (← field j "a")
    return encPy (fun t => encTzDesc (some t)) (localTimezonePy env fixedZone 101 a)
  | "x3_repr" =>
    let isTime := (← getStr j "kind") == "tm"
    let c := reprCls j (if isTime then "TSub" else "DTSub")
    if isTime then
      let a ← decTM (← field j "a")
      return encPy toJson ((if isC then tmReprCF else tmReprPyF) testReprEnv c a)
    else
      let a ← decDT (← field j "a")
      return encPy toJson ((if isC then dtReprCF else dtReprPyF) testReprEnv c a)
  | "x3_new_str" =>
    let cs := (← (← field j "s").getArr?).toList.map (fun x => (x.getNat?).toOption.getD 0)
    let tz ← decTz (← field j "tz")
    let args : List Arg := match tz with
      | none => [.str cs]
      | some t => [.str cs, .tz t]
    if (← getStr j "kind") == "tm" then
      return encPy encTMv (if isC then timeNewC args (.int 0) else timeCallPy args (.int 0))
    else
      return encPy encDTv (if isC then datetimeNewC args (.int 0) else datetimeCallPy args (.int 0))
  | other => throw s!"unknown fn {other}"

end PyLean.Datetime
