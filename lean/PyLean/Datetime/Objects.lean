import PyLean.Datetime.Tz

/-!
Operators and methods of `timedelta`, `date`, `time`, `datetime` that the first
layer of the model did not cover: comparison, `datetime` arithmetic, `combine`,
`replace`, `fromutc`, `astimezone` with an explicit `tz`, time tuples, `repr`,
`ctime`, hash keys and pickle state. Python and C are mirrored separately where
they differ. Citations are to `Lib/_pydatetime.py` (Py) and
`Modules/_datetimemodule.c` (C) of 3.15.2.
-/

namespace PyLean.Datetime

open PyLean

/-! ### Comparison helpers -/

inductive CmpOp where
  | lt | le | eq | ne | gt | ge
  deriving Repr, DecidableEq, Inhabited

/-- Lexicographic comparison of int tuples, as Python tuples compare. -/
def tupleLt : List Int → List Int → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then tupleLt as bs else decide (a < b)

/-- Module-level `_cmp(x, y)` on tuples, _pydatetime.py:14-15. -/
def cmpTuple (x y : List Int) : Int :=
  if x = y then 0 else if tupleLt y x then 1 else -1

/-- `memcmp` on the packed data: the sign of the first difference. -/
def memcmpBytes : List Nat → List Nat → Int
  | a :: as, b :: bs => if a = b then memcmpBytes as bs else if a < b then -1 else 1
  | _, _ => 0

/-- `diff_to_bool(diff, op)`, _datetimemodule.c:2119-2122. -/
def diffToBool (diff : Int) : CmpOp → Bool
  | .lt => decide (diff < 0)
  | .le => decide (diff ≤ 0)
  | .eq => decide (diff = 0)
  | .ne => decide (diff ≠ 0)
  | .gt => decide (diff > 0)
  | .ge => decide (diff ≥ 0)

/-- A method result that is either the receiver itself (`return self`, the same object)
or a newly built object with the given value. Object identity is observable (`+t is t`),
so it is not a value. -/
inductive ObjRes (α : Type) where
  | self_ : ObjRes α
  | fresh : α → ObjRes α
  deriving Repr, DecidableEq

/-- The value of a result, given the receiver's value. -/
def ObjRes.value {α : Type} (recv : α) : ObjRes α → α
  | .self_ => recv
  | .fresh v => v

/-! ### `timedelta` -/

namespace Delta

/-- `timedelta._getstate`, Py:959-960; C `delta_getstate`, :3024-3029. -/
def getstate (t : Delta) : List Int := [t.days, t.seconds, t.us]

/-- `timedelta._cmp`, Py:943-945. -/
def cmpPy (a b : Delta) : Int := cmpTuple a.getstate b.getstate

/-- `delta_cmp`, :2536-2546. -/
def cmpC (a b : Delta) : Int :=
  let diff := a.days - b.days
  if diff = 0 then
    let diff := a.seconds - b.seconds
    if diff = 0 then a.us - b.us else diff
  else diff

/-- `timedelta.__eq__`..`__gt__`, Py:913-941, each operator on its own line of the source
(`__ne__` is the default inverse of `__eq__`). -/
def richPy (op : CmpOp) (a b : Delta) : Bool :=
  match op with
  | .eq => decide (a.cmpPy b = 0) -- :913-915
  | .ne => !decide (a.cmpPy b = 0) -- object.__ne__ inverts __eq__
  | .le => decide (a.cmpPy b ≤ 0) -- :919-921
  | .lt => decide (a.cmpPy b < 0) -- :925-927
  | .ge => decide (a.cmpPy b ≥ 0) -- :931-933
  | .gt => decide (a.cmpPy b > 0) -- :937-939

/-- `delta_richcompare`, :2549-2558. -/
def richC (op : CmpOp) (a b : Delta) : Bool := diffToBool (a.cmpC b) op

/-- `timedelta.__bool__`, Py:952-955; C `delta_bool`, :2935-2940. -/
def bool (t : Delta) : Bool := t.days != 0 || t.seconds != 0 || t.us != 0

/-- `timedelta.__pos__`, Py:849-850: `return self`, the receiver itself. -/
def posPy (_a : Delta) : ObjRes Delta := .self_

/-- `delta_positive`, :2486-2495: `new_delta(days, seconds, us, 0)` through `new_delta_ex`
(:1383-1411: the day-range check, no normalization), which returns the static `zero_delta`
for a zero `timedelta` (`look_up_delta`, :3173-3181) and a new object otherwise. Every zero
`timedelta` of the base type is that singleton, so `+t is t` exactly for zero. -/
def posC (a : Delta) : Py (ObjRes Delta) := do
  checkDeltaDayRange a.days
  if a.days = 0 ∧ a.seconds = 0 ∧ a.us = 0 then return .self_
  return .fresh ⟨a.days, a.seconds, a.us⟩

/-- `timedelta.__rsub__`, Py:837-840: `other - self` as `-self + other`. -/
def rsubPy (self other : Delta) : Py Delta := do
  let n ← self.negPy
  n.addPy other

/-- `delta_subtract` with the operands swapped, as the reflected call. -/
def rsubC (self other : Delta) : Py Delta := other.subC self

end Delta

/-! ### Packed data and hash keys -/

/-- `self->data` of a `date`. -/
def dateData (y m d : Int) : List Nat := [(y / 256).toNat, (y % 256).toNat, m.toNat, d.toNat]

/-- `self->data` of a `time`, without the fold bit. -/
def timeData (t : TM) : List Nat :=
  [t.h.toNat, t.mi.toNat, t.s.toNat, (t.us / 65536).toNat, (t.us / 256 % 256).toNat, (t.us % 256).toNat]

/-- `self->data` of a `datetime`, without the fold bit. -/
def dtData (dt : DT) : List Nat :=
  dateData dt.y dt.m dt.d ++
    [dt.h.toNat, dt.mi.toNat, dt.s.toNat, (dt.us / 65536).toNat, (dt.us / 256 % 256).toNat, (dt.us % 256).toNat]

/-- What a hash is computed from: two objects with the same key hash alike.
`bytes b` is `hash(bytes(b))` (`Py_HashBuffer`), `tuple1 b` is `hash((bytes(b),))`
and `ints xs` is `hash(tuple(xs))`. -/
inductive HashKey where
  | bytes (b : List Nat)
  | tuple1 (b : List Nat)
  | ints (xs : List Int)
  deriving Repr, DecidableEq, Inhabited

/-- `timedelta.__hash__`, Py:947-950: `hash(self._getstate())` (cached in `_hashcode`; a
Python hash is never -1, so the cache only saves the recomputation). -/
def Delta.hashKey (t : Delta) : HashKey := .ints t.getstate

/-- C `delta_getstate`, :3024-3029: `Py_BuildValue("iii", days, seconds, microseconds)`. -/
def Delta.getstateC (t : Delta) : List Int := [t.days, t.seconds, t.us]

/-- `delta_hash`, :2563-2576: `PyObject_Hash(delta_getstate(self))`, cached in `hashcode`. -/
def Delta.hashKeyC (t : Delta) : HashKey := .ints t.getstateC

/-! ### `date` -/

/-- `date._cmp`, Py:1223-1228. -/
def dateCmpPy (a b : Int × Int × Int) : Int :=
  cmpTuple [a.1, a.2.1, a.2.2] [b.1, b.2.1, b.2.2]

/-- `date.__eq__`..`__gt__`, Py:1198-1221, each operator on its own line of the source:
`none` is `NotImplemented` (a `datetime` operand). -/
def dateRichPy (op : CmpOp) (a b : Int × Int × Int) (otherIsDatetime : Bool) : Option Bool :=
  if otherIsDatetime then none else
  match op with
  | .eq => some (decide (dateCmpPy a b = 0))  -- :1198-1201
  | .ne => some (!decide (dateCmpPy a b = 0)) -- object.__ne__ inverts __eq__
  | .le => some (decide (dateCmpPy a b ≤ 0))  -- :1203-1206
  | .lt => some (decide (dateCmpPy a b < 0))  -- :1208-1211
  | .ge => some (decide (dateCmpPy a b ≥ 0))  -- :1213-1216
  | .gt => some (decide (dateCmpPy a b > 0))  -- :1218-1221

/-- `date_richcompare`, :3916-3934. -/
def dateRichC (op : CmpOp) (a b : Int × Int × Int) (otherIsDatetime : Bool) : Option Bool :=
  if otherIsDatetime then none
  else some (diffToBool (memcmpBytes (dateData a.1 a.2.1 a.2.2) (dateData b.1 b.2.1 b.2.2)) op)

/-- `date.__hash__`, Py:1230-1234: the hash of the one-element state tuple. -/
def dateHashKeyPy (y m d : Int) : HashKey := .tuple1 (dateData y m d)

/-- `date_hash` through `generic_hash`, :3964-3967. -/
def dateHashKeyC (y m d : Int) : HashKey := .bytes (dateData y m d)

/-- `date.weekday()`, Py:1259-1261. -/
def dateWeekdayPy (y m d : Int) : Int := (toordinal y m d + 6) % 7

/-- `date_weekday`, :3994-3998, through `weekday`. -/
def dateWeekdayC (y m d : Int) : Int := weekdayC y m d

/-- `date.isoweekday()`, Py:1265-1268. -/
def dateIsoweekdayPy (y m d : Int) : Int :=
  let r := toordinal y m d % 7
  if r = 0 then 7 else r

/-- `date_isoweekday`, :3705-3710. -/
def dateIsoweekdayC (y m d : Int) : Int := weekdayC y m d + 1

/-- `date.__sub__(date)`, Py:1249-1257. -/
def dateSubDatePy (a b : Int × Int × Int) : Py Delta :=
  deltaPy (toordinal a.1 a.2.1 a.2.2 - toordinal b.1 b.2.1 b.2.2) 0 0 0 0 0 0

/-- `date_subtract` with a date, :3589-3613: `new_delta(l - r, 0, 0, 0)`. -/
def dateSubDateC (a b : Int × Int × Int) : Py Delta := do
  let d := ymdToOrdC a.1 a.2.1 a.2.2 - ymdToOrdC b.1 b.2.1 b.2.2
  checkDeltaDayRange d
  return ⟨d, 0, 0⟩

/-- `date.__sub__(timedelta)`, Py:1249-1257: `self + timedelta(-other.days)`. -/
def dateSubDeltaPy (y m d : Int) (t : Delta) : Py (Int × Int × Int) := do
  dateAddPy y m d (← deltaPy (-t.days) 0 0 0 0 0 0)

/-- `add_date_timedelta` with `negate = 1`, :3547-3559. -/
def dateSubDeltaC (y m d : Int) (t : Delta) : Py (Int × Int × Int) := do
  let (y, m, d) ← normalizeDateC y m (d + -t.days)
  checkDate y m d

/-! ### Time tuples -/

/-- `time.struct_time` as nine ints. -/
abbrev TimeTuple := List Int

/-- `_build_struct_time`, Py:161-164. -/
def buildStructTimePy (y m d hh mm ss dstflag : Int) : TimeTuple :=
  let wday := (ymd2ord y m d + 6) % 7
  let dnum := daysBeforeMonth y m + d
  [y, m, d, hh, mm, ss, wday, dnum, dstflag]

/-- `build_struct_time`, :2091-2109. -/
def buildStructTimeC (y m d hh mm ss dstflag : Int) : TimeTuple :=
  [y, m, d, hh, mm, ss, weekdayC y m d, daysBeforeMonth y m + d, dstflag]

/-- `date.timetuple()`, Py:1171-1174. -/
def dateTimetuplePy (y m d : Int) : TimeTuple := buildStructTimePy y m d 0 0 0 (-1)

/-- `date_timetuple`, :3937-3943. -/
def dateTimetupleC (y m d : Int) : TimeTuple := buildStructTimeC y m d 0 0 0 (-1)

/-! ### `ctime` -/

def dayNames : List String := ["", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]
def monthNames : List String :=
  ["", "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]

/-- `'%2d' % n` for `0 <= n`. -/
def fmt2Space (n : Int) : String :=
  let s := fmtD n
  if s.length < 2 then " " ++ s else s

/-- `date.ctime()`, Py:1114-1120, and `datetime.ctime()`, Py:2164-2172. -/
def ctimePy (y m d hh mm ss : Int) : String :=
  let wd := toordinal y m d % 7
  let wd := if wd = 0 then 7 else wd
  s!"{dayNames.getD wd.toNat ""} {monthNames.getD m.toNat ""} {fmt2Space d} {fmt0 2 hh}:{fmt0 2 mm}:{fmt0 2 ss} {fmt0 4 y}"

/-- `format_ctime`, :1700-1716. -/
def ctimeC (y m d hh mm ss : Int) : String :=
  let wday := weekdayC y m d
  s!"{dayNames.getD (wday + 1).toNat ""} {monthNames.getD m.toNat ""} {fmt2Space d} {fmt0 2 hh}:{fmt0 2 mm}:{fmt0 2 ss} {fmt0 4 y}"

/-! ### `repr` -/

/-- `_get_class_module(self)`, Py:17-22. -/
def getClassModule (moduleName : String) : String :=
  if moduleName = "datetime" then "datetime." else ""

/-- `s[:-1] + ", tzinfo=%r" % tz + ")"`, and C `append_keyword_tzinfo`, :1628-1645. -/
def appendTzinfo (env : TzEnv) (s : String) (tz : Option Tz) : String :=
  match tz with
  | none => s
  | some t => (s.dropEnd 1).toString ++ s!", tzinfo={t.repr env})"

/-- `s[:-1] + ", fold=1)"`, and C `append_keyword_fold`, :1653-1669. -/
def appendFold (s : String) (fold : Int) : String :=
  if fold = 0 then s else (s.dropEnd 1).toString ++ s!", fold={fmtD fold})"

/-- The positional part of `time.__repr__`, Py:1606-1623. -/
def tmReprBasePy (t : TM) : String :=
  let s := if t.us ≠ 0 then s!", {fmtD t.s}, {fmtD t.us}"
    else if t.s ≠ 0 then s!", {fmtD t.s}" else ""
  s!"{getClassModule "datetime"}time({fmtD t.h}, {fmtD t.mi}{s})"

/-- `time.__repr__`, Py:1606-1623. -/
def timeReprPy (env : TzEnv) (t : TM) : String :=
  appendFold (appendTzinfo env (tmReprBasePy t) t.tz) t.fold

/-- The positional part of `time_repr`, :4852-4876. -/
def tmReprBaseC (t : TM) : String :=
  if t.us ≠ 0 then s!"datetime.time({fmtD t.h}, {fmtD t.mi}, {fmtD t.s}, {fmtD t.us})"
  else if t.s ≠ 0 then s!"datetime.time({fmtD t.h}, {fmtD t.mi}, {fmtD t.s})"
  else s!"datetime.time({fmtD t.h}, {fmtD t.mi})"

/-- `time_repr`, :4852-4876. -/
def timeReprC (env : TzEnv) (t : TM) : String :=
  appendFold (appendTzinfo env (tmReprBaseC t) t.tz) t.fold

/-- The positional part of `datetime.__repr__`, Py:2201-2218. -/
def dtReprBasePy (dt : DT) : String :=
  let L := [dt.y, dt.m, dt.d, dt.h, dt.mi, dt.s, dt.us]
  let L := if L.getLast? = some 0 then L.dropLast else L
  let L := if L.getLast? = some 0 then L.dropLast else L
  s!"{getClassModule "datetime"}datetime({", ".intercalate (L.map fmtD)})"

/-- `datetime.__repr__`, Py:2201-2218. The tzinfo keyword comes before fold. -/
def dtReprPy (env : TzEnv) (dt : DT) : String :=
  appendFold (appendTzinfo env (dtReprBasePy dt) dt.tz) dt.fold

/-- The positional part of `datetime_repr`, :6378-6413. -/
def dtReprBaseC (dt : DT) : String :=
  let f (xs : List Int) := s!"datetime.datetime({", ".intercalate (xs.map fmtD)})"
  if dt.us ≠ 0 then f [dt.y, dt.m, dt.d, dt.h, dt.mi, dt.s, dt.us]
  else if dt.s ≠ 0 then f [dt.y, dt.m, dt.d, dt.h, dt.mi, dt.s]
  else f [dt.y, dt.m, dt.d, dt.h, dt.mi]

/-- `datetime_repr`, :6378-6413: fold is appended first, then tzinfo. -/
def dtReprC (env : TzEnv) (dt : DT) : String :=
  appendTzinfo env (appendFold (dtReprBaseC dt) dt.fold) dt.tz

/-- `IsoCalendarDate.__repr__`, Py:1401-1403. -/
def isoReprPy (y w d : Int) : String :=
  s!"IsoCalendarDate(year={fmtD y}, week={fmtD w}, weekday={fmtD d})"

/-- `iso_calendar_date_repr`, :3723-3740. -/
def isoReprC (y w d : Int) : String :=
  s!"datetime.IsoCalendarDate(year={fmtD y}, week={fmtD w}, weekday={fmtD d})"

/-! ### Offsets in `isoformat` -/

/-- `time._tzstr`, Py:1601-1604: `_format_offset(self.utcoffset())`. -/
def tmTzstrPy (env : TzEnv) (t : TM) : Py String := do
  let off ← t.utcoffsetPy env
  return String.ofList (formatOffset (off.map Delta.toUs))

/-- `time.isoformat`, Py:1625-1640. -/
def tmIsoformatPy (env : TzEnv) (t : TM) (spec : TimeSpec) : Py String := do
  let s := String.ofList (formatTime t.h t.mi t.s t.us spec)
  return s ++ (← tmTzstrPy env t)

/-- `format_utcoffset`, :1731-1776, with the tzinfo argument of the caller. -/
def formatUtcoffsetC (sep : List Char) : Option Delta → List Char
  | none => []
  | some off =>
    -- :1749-1757: the sign from `days < 0`, then `delta_negative`
    let (sign, off) : Char × Delta :=
      if off.days < 0 then ('-', match off.negC with | .ok v => v | .error _ => off) else ('+', off)
    let microseconds := off.us
    let seconds := off.seconds
    -- :1760-1761: `divmod` by 60 twice
    let minutes := seconds / 60
    let seconds := seconds % 60
    let hours := minutes / 60
    let minutes := minutes % 60
    -- :1762-1775: three `snprintf` forms
    let s := sign :: (padInt 2 hours) ++ sep ++ (padInt 2 minutes)
    if microseconds ≠ 0 then s ++ sep ++ padInt 2 seconds ++ ['.'] ++ padInt 6 microseconds
    else if seconds ≠ 0 then s ++ sep ++ padInt 2 seconds
    else s

/-- `datetime_time_isoformat_impl`, :4900-4959: the fields, then `format_utcoffset` with
`sep = ":"` and the tzinfo argument `None` (:1731-1776, through `call_utcoffset`). -/
def tmIsoformatC (env : TzEnv) (t : TM) (spec : TimeSpec) : Py String := do
  let s := String.ofList (formatTime t.h t.mi t.s t.us spec)
  let off ← t.utcoffsetC env
  return s ++ String.ofList (formatUtcoffsetC [':'] off)

/-- `datetime.isoformat`, Py:2174-2199. -/
def dtIsoformatPy (env : TzEnv) (dt : DT) (sep : Char) (spec : TimeSpec) : Py String := do
  let s := String.ofList (dateIsoformat dt.y dt.m dt.d ++ [sep] ++ formatTime dt.h dt.mi dt.s dt.us spec)
  let off ← dt.utcoffsetPy env
  return s ++ String.ofList (formatOffset (off.map Delta.toUs))

/-- `datetime_datetime_isoformat_impl`, :6450-6510: the fields, then `format_utcoffset` with
`sep = ":"` and the datetime as tzinfo argument (:1731-1776). -/
def dtIsoformatC (env : TzEnv) (dt : DT) (sep : Char) (spec : TimeSpec) : Py String := do
  let s := String.ofList (dateIsoformat dt.y dt.m dt.d ++ [sep] ++ formatTime dt.h dt.mi dt.s dt.us spec)
  let off ← dt.utcoffsetC env
  return s ++ String.ofList (formatUtcoffsetC [':'] off)

/-! ### `time`: comparison and hash -/

/-- The fields compared in the base case. -/
def TM.base (t : TM) : List Int := [t.h, t.mi, t.s, t.us]

/-- `myoff // timedelta(minutes=1)`. -/
def floorMinutes (off : Delta) : Int := off.toUs / 60000000

/-- `time._cmp`, Py:1550-1576. -/
def tmCmpPy (env : TzEnv) (a b : TM) (allowMixed : Bool) : Py Int := do
  let (myoff, otoff, baseCompare) ←
    if sameTz a.tz b.tz then pure (none, none, true)
    else do
      let myoff ← a.utcoffsetPy env
      let otoff ← b.utcoffsetPy env
      pure (myoff, otoff, offEq myoff otoff)
  if baseCompare then return cmpTuple a.base b.base
  match myoff, otoff with
  | some mo, some oo =>
    let myhhmm := a.h * 60 + a.mi - floorMinutes mo
    let othhmm := b.h * 60 + b.mi - floorMinutes oo
    return cmpTuple [myhhmm, a.s, a.us] [othhmm, b.s, b.us]
  | _, _ =>
    if allowMixed then return 2
    else throw (.typeError "cannot compare naive and aware times")

/-- `time.__eq__`..`__gt__`, Py:1520-1548 (`__ne__` inverts `__eq__`). -/
def tmRichPy (env : TzEnv) (op : CmpOp) (a b : TM) : Py Bool := do
  match op with
  | .eq => return (← tmCmpPy env a b true) == 0
  | .ne => return (← tmCmpPy env a b true) != 0
  | .le => return diffToBool (← tmCmpPy env a b false) .le
  | .lt => return diffToBool (← tmCmpPy env a b false) .lt
  | .ge => return diffToBool (← tmCmpPy env a b false) .ge
  | .gt => return diffToBool (← tmCmpPy env a b false) .gt

/-- `time_richcompare`, :5027-5095. -/
def tmRichC (env : TzEnv) (op : CmpOp) (a b : TM) : Py Bool := do
  if sameTz a.tz b.tz then return diffToBool (memcmpBytes (timeData a) (timeData b)) op
  let offset1 ← a.utcoffsetC env
  let offset2 ← b.utcoffsetC env
  if offEq offset1 offset2 then return diffToBool (memcmpBytes (timeData a) (timeData b)) op
  match offset1, offset2 with
  | some o1, some o2 =>
    let offsecs1 := a.h * 3600 + a.mi * 60 + a.s - o1.days * 86400 - o1.seconds
    let offsecs2 := b.h * 3600 + b.mi * 60 + b.s - o2.days * 86400 - o2.seconds
    let diff := offsecs1 - offsecs2
    let diff := if diff = 0 then a.us - b.us else diff
    return diffToBool diff op
  | _, _ =>
    match op with
    | .eq => return false
    | .ne => return true
    | _ => throw (.typeError "can't compare offset-naive and offset-aware times")

/-- `time.replace(fold=0)` as `__hash__` uses it. -/
def TM.fold0 (t : TM) : TM := { t with fold := 0 }

/-- `time.__hash__`, Py:1578-1597; `none` key means the `assert` failed with
`AssertionError('whole minute')`. -/
def tmHashKeyPy (env : TzEnv) (self : TM) : Py HashKey := do
  let t := if self.fold ≠ 0 then self.fold0 else self
  let tzoff ← t.utcoffsetPy env
  match tzoff with
  | none => return .bytes (timeData t)
  | some o =>
    if o.toUs = 0 then return .bytes (timeData t)
    else
      -- `timedelta(hours=self.hour, minutes=self.minute) - tzoff`
      let x := (self.h * 3600 + self.mi * 60) * 1000000 - o.toUs
      let h := x / 3600000000
      let m := x % 3600000000
      if m % 60000000 ≠ 0 then throw (.assertionError "whole minute")
      let m := m / 60000000
      if 0 ≤ h ∧ h < 24 then
        return .bytes (timeData ⟨h, m, self.s, self.us, 0, none⟩)
      else return .ints [h, m, self.s, self.us]

/-- `time_hash`, :5098-5154. The `timedelta` arithmetic cannot leave its range. -/
def tmHashKeyC (env : TzEnv) (self : TM) : Py HashKey := do
  let self0 := if self.fold ≠ 0 then self.fold0 else self
  let offset ← self0.utcoffsetC env
  match offset with
  | none => return .bytes (timeData self)
  | some o =>
    let temp1 ← newDeltaNormC 0 (self.h * 3600 + self.mi * 60 + self.s) self.us
    let temp2 ← temp1.subC o
    return temp2.hashKey

/-! ### `datetime`: construction helpers -/

/-- `date`, `time` part fields of a `datetime` built from checked fields. -/
def DT.ymd (dt : DT) : Int × Int × Int := (dt.y, dt.m, dt.d)

/-- `datetime.date()`, Py:2081-2083, and `datetime_getdate`, :7121-7127. -/
def dtDate (dt : DT) : Int × Int × Int := dt.ymd

/-- `datetime.time()`, Py:2085-2087, and `datetime_gettime`, :7130-7139. -/
def dtTime (dt : DT) : TM := ⟨dt.h, dt.mi, dt.s, dt.us, dt.fold, none⟩

/-- `datetime.timetz()`, Py:2089-2092, and `datetime_gettimetz`, :7142-7151. -/
def dtTimetz (dt : DT) : TM := ⟨dt.h, dt.mi, dt.s, dt.us, dt.fold, dt.tz⟩

/-- The fold check at the end of `_check_time_fields`, Py:591-606, and
`check_time_args`, :706-710. -/
def checkFold (fold : Int) : Py Unit :=
  if fold = 0 ∨ fold = 1 then .ok ()
  else .error (.valueError s!"fold must be either 0 or 1, not {fold}")

/-- `datetime(year, ..., tzinfo, fold=fold)` for int fields: `_check_date_fields`,
`_check_time_fields`, Py:591-606; `new_datetime_ex2`, :1210-1240. -/
def newDT (dt : DT) : Py DT := do
  let _ ← checkDate dt.y dt.m dt.d
  let _ ← checkTime dt.h dt.mi dt.s dt.us
  checkFold dt.fold
  return dt

/-- `time(hour, ..., tzinfo, fold=fold)` for int fields: Py:1436-1473;
`new_time_ex2`, :1318-1345. -/
def newTM (t : TM) : Py TM := do
  let _ ← checkTime t.h t.mi t.s t.us
  checkFold t.fold
  return t

/-- `datetime.combine(date, time, tzinfo)`, Py:1952-1961, and `datetime_datetime_combine_impl`,
:5891-5911, for the date and time objects it takes. `tz = none` is the default
`tzinfo=True`, `tz = some x` an explicit value (`some none` is `None`). -/
def dtCombine (ymd : Int × Int × Int) (t : TM) (tz : Option (Option Tz)) : Py DT :=
  newDT ⟨ymd.1, ymd.2.1, ymd.2.2, t.h, t.mi, t.s, t.us, t.fold, tz.getD t.tz⟩

/-- `datetime.replace`, Py:2094-2117, for int fields. -/
def dtReplace (dt : DT) (y m d h mi s us fold : Option Int) (tz : Option (Option Tz)) : Py DT :=
  newDT ⟨y.getD dt.y, m.getD dt.m, d.getD dt.d, h.getD dt.h, mi.getD dt.mi, s.getD dt.s,
    us.getD dt.us, fold.getD dt.fold, tz.getD dt.tz⟩

/-- `time.replace`, Py:1732-1747, for int fields. -/
def tmReplace (t : TM) (h mi s us fold : Option Int) (tz : Option (Option Tz)) : Py TM :=
  newTM ⟨h.getD t.h, mi.getD t.mi, s.getD t.s, us.getD t.us, fold.getD t.fold, tz.getD t.tz⟩

/-- `datetime_datetime_replace_impl`, :6753-6762: the clinic `int` conversions, then the
fields checked as in `dtReplace`. -/
def dtReplaceC (dt : DT) (y m d h mi s us fold : Option Int) (tz : Option (Option Tz)) : Py DT :=
  if ¬(fitsCInt (y.getD dt.y) ∧ fitsCInt (m.getD dt.m) ∧ fitsCInt (d.getD dt.d) ∧
      fitsCInt (h.getD dt.h) ∧ fitsCInt (mi.getD dt.mi) ∧ fitsCInt (s.getD dt.s) ∧
      fitsCInt (us.getD dt.us) ∧ fitsCInt (fold.getD dt.fold)) then
    .error (.overflowError "Python int too large to convert to C int")
  else dtReplace dt y m d h mi s us fold tz

/-- `datetime_time_replace_impl`, :5171-5178: the clinic `int` conversions, then the fields
checked as in `tmReplace`. -/
def tmReplaceC (t : TM) (h mi s us fold : Option Int) (tz : Option (Option Tz)) : Py TM :=
  if ¬(fitsCInt (h.getD t.h) ∧ fitsCInt (mi.getD t.mi) ∧ fitsCInt (s.getD t.s) ∧
      fitsCInt (us.getD t.us) ∧ fitsCInt (fold.getD t.fold)) then
    .error (.overflowError "Python int too large to convert to C int")
  else tmReplace t h mi s us fold tz

/-! ### `datetime`: arithmetic -/

/-- `datetime.__add__`, Py:2340-2357. -/
def dtAddPy (dt : DT) (other : Delta) : Py DT := do
  let delta ← deltaPy (toordinal dt.y dt.m dt.d) dt.s dt.us 0 dt.mi dt.h 0
  let delta ← delta.addPy other
  let hour := delta.seconds / 3600
  let rem := delta.seconds % 3600
  let minute := rem / 60
  let second := rem % 60
  if 0 < delta.days ∧ delta.days ≤ MAXORDINAL then
    let ymd ← fromordinalPy delta.days
    let t ← newTM ⟨hour, minute, second, delta.us, 0, dt.tz⟩
    dtCombine ymd t none
  else throw (.overflowError "result out of range")

/-- The tail of `normalize_datetime`: the date normalized, the time fields carried. -/
def normalizeTailC (hh mi s us : Int) (r : Py (Int × Int × Int)) : Py DT :=
  match r with
  | .ok (y, m, d) => .ok ⟨y, m, d, hh, mi, s, us, 0, none⟩
  | .error e => .error e

/-- `normalize_datetime`, :847-856. -/
def normalizeDatetimeC (y m d hh mi s us : Int) : Py DT :=
  let (s, us) := normalizePair s us 1000000
  let (mi, s) := normalizePair mi s 60
  let (hh, mi) := normalizePair hh mi 60
  let (d, hh) := normalizePair d hh 24
  normalizeTailC hh mi s us (normalizeDateC y m d)

/-- `add_datetime_timedelta`, :6241-6266, with the `factor` of the caller. -/
def addDatetimeTimedeltaC (dt : DT) (delta : Delta) (factor : Int) : Py DT := do
  let r ← normalizeDatetimeC dt.y dt.m (dt.d + delta.days * factor) dt.h dt.mi
    (dt.s + delta.seconds * factor) (dt.us + delta.us * factor)
  newDT { r with tz := dt.tz }

/-- `datetime.__sub__(timedelta)`, Py:2361-2383: `self + -other`. -/
def dtSubDeltaPy (dt : DT) (other : Delta) : Py DT := do dtAddPy dt (← other.negPy)

/-- `datetime.__sub__(datetime)`, Py:2361-2383. -/
def dtSubPy (env : TzEnv) (self other : DT) : Py Delta := do
  let days1 := toordinal self.y self.m self.d
  let days2 := toordinal other.y other.m other.d
  let secs1 := self.s + self.mi * 60 + self.h * 3600
  let secs2 := other.s + other.mi * 60 + other.h * 3600
  let base ← deltaPy (days1 - days2) (secs1 - secs2) (self.us - other.us) 0 0 0 0
  if sameTz self.tz other.tz then return base
  let myoff ← self.utcoffsetPy env
  let otoff ← other.utcoffsetPy env
  if offEq myoff otoff then return base
  match myoff, otoff with
  | some mo, some oo =>
    let r ← base.addPy oo
    r.subPy mo
  | _, _ => throw (.typeError "cannot mix naive and timezone-aware time")

/-- `datetime_subtract` for two datetimes, :6290-6373. -/
def dtSubC (env : TzEnv) (left right : DT) : Py Delta := do
  let (offset1, offset2) ←
    if sameTz left.tz right.tz then pure (none, none)
    else do
      let o1 ← left.utcoffsetC env
      let o2 ← right.utcoffsetC env
      if o1.isSome != o2.isSome then
        throw (.typeError "can't subtract offset-naive and offset-aware datetimes")
      pure (o1, o2)
  let offdiff ← match offset1, offset2 with
    | some o1, some o2 => if o1.cmpC o2 ≠ 0 then some <$> o1.subC o2 else pure none
    | _, _ => pure none
  let delta_d := ymdToOrdC left.y left.m left.d - ymdToOrdC right.y right.m right.d
  let delta_s := (left.h - right.h) * 3600 + (left.mi - right.mi) * 60 + (left.s - right.s)
  let delta_us := left.us - right.us
  let result ← newDeltaNormC delta_d delta_s delta_us
  match offdiff with
  | some od => result.subC od
  | none => return result

/-! ### `datetime`: comparison and hash -/

/-- The fields compared in the base case. -/
def DT.base (dt : DT) : List Int := [dt.y, dt.m, dt.d, dt.h, dt.mi, dt.s, dt.us]

/-- `self.replace(fold=not self.fold)`. -/
def DT.flipFold (dt : DT) : DT := { dt with fold := if dt.fold = 0 then 1 else 0 }

/-- `datetime._cmp`, Py:2303-2338. -/
def dtCmpPy (env : TzEnv) (self other : DT) (allowMixed : Bool) : Py Int := do
  if sameTz self.tz other.tz then return cmpTuple self.base other.base
  let myoff ← self.utcoffsetPy env
  let otoff ← other.utcoffsetPy env
  if allowMixed then
    if !offEq myoff (← self.flipFold.utcoffsetPy env) then return 2
    if !offEq otoff (← other.flipFold.utcoffsetPy env) then return 2
  if offEq myoff otoff then return cmpTuple self.base other.base
  if myoff.isNone ∨ otoff.isNone then
    if allowMixed then return 2
    else throw (.typeError "cannot compare naive and aware datetimes")
  let diff ← dtSubPy env self other
  if diff.days < 0 then return -1
  return if diff.bool then 1 else 0

/-- `datetime.__eq__`..`__gt__`, Py:2273-2301. -/
def dtRichPy (env : TzEnv) (op : CmpOp) (a b : DT) : Py Bool := do
  match op with
  | .eq => return (← dtCmpPy env a b true) == 0
  | .ne => return (← dtCmpPy env a b true) != 0
  | .le => return diffToBool (← dtCmpPy env a b false) .le
  | .lt => return diffToBool (← dtCmpPy env a b false) .lt
  | .ge => return diffToBool (← dtCmpPy env a b false) .ge
  | .gt => return diffToBool (← dtCmpPy env a b false) .gt

/-- `get_flip_fold_offset`, :6541-6551, through `flip_fold`, :6525-6538. -/
def getFlipFoldOffsetC (env : TzEnv) (dt : DT) : Py (Option Delta) := dt.flipFold.utcoffsetC env

/-- `pep495_eq_exception`, :6560-6586. -/
def pep495EqExceptionC (env : TzEnv) (self other : DT) (o1 o2 : Option Delta) : Py Bool := do
  let f1 ← getFlipFoldOffsetC env self
  if !offEq f1 o1 then return true
  let f2 ← getFlipFoldOffsetC env other
  return !offEq f2 o2

/-- `datetime_richcompare`, :6589-6666. -/
def dtRichC (env : TzEnv) (op : CmpOp) (self other : DT) : Py Bool := do
  if sameTz self.tz other.tz then
    return diffToBool (memcmpBytes (dtData self) (dtData other)) op
  let offset1 ← self.utcoffsetC env
  let offset2 ← other.utcoffsetC env
  if offEq offset1 offset2 then
    let diff := memcmpBytes (dtData self) (dtData other)
    let diff ← if (op = .eq ∨ op = .ne) ∧ diff = 0 then do
        if ← pep495EqExceptionC env self other offset1 offset2 then pure 1 else pure diff
      else pure diff
    return diffToBool diff op
  if offset1.isSome ∧ offset2.isSome then
    let delta ← dtSubC env self other
    let diff := delta.days
    let diff := if diff = 0 then (if delta.seconds = 0 ∧ delta.us = 0 then 0 else 1) else diff
    let diff ← if (op = .eq ∨ op = .ne) ∧ diff = 0 then do
        if ← pep495EqExceptionC env self other offset1 offset2 then pure 1 else pure diff
      else pure diff
    return diffToBool diff op
  match op with
  | .eq => return false
  | .ne => return true
  | _ => throw (.typeError "can't compare offset-naive and offset-aware datetimes")

/-- `datetime.__hash__`, Py:2385-2398. -/
def dtHashKeyPy (env : TzEnv) (self : DT) : Py HashKey := do
  let t := if self.fold ≠ 0 then { self with fold := 0 } else self
  let tzoff ← t.utcoffsetPy env
  match tzoff with
  | none => return .bytes (dtData t)
  | some o =>
    let days := ymd2ord self.y self.m self.d
    let seconds := self.h * 3600 + self.mi * 60 + self.s
    let base ← deltaPy days seconds self.us 0 0 0 0
    let r ← base.subPy o
    return r.hashKey

/-- `datetime_hash`, :6669-6733. -/
def dtHashKeyC (env : TzEnv) (self : DT) : Py HashKey := do
  let self0 := if self.fold ≠ 0 then { self with fold := 0 } else self
  let offset ← self0.utcoffsetC env
  match offset with
  | none => return .bytes (dtData self)
  | some o =>
    let days := ymdToOrdC self.y self.m self.d
    let seconds := self.h * 3600 + self.mi * 60 + self.s
    let temp1 ← newDeltaNormC days seconds self.us
    let temp2 ← temp1.subC o
    return temp2.hashKey

/-! ### `datetime`: time tuples -/

/-- `datetime.timetuple()`, Py:2016-2027. -/
def dtTimetuplePy (env : TzEnv) (dt : DT) : Py TimeTuple := do
  let dst ← dt.dstPy env
  let flag : Int := match dst with
    | none => -1
    | some o => if o.bool then 1 else 0
  return buildStructTimePy dt.y dt.m dt.d dt.h dt.mi dt.s flag

/-- `datetime_timetuple`, :7007-7030. -/
def dtTimetupleC (env : TzEnv) (dt : DT) : Py TimeTuple := do
  let dst ← dt.dstC env
  let flag : Int := match dst with
    | none => -1
    | some o => if o.bool then 1 else 0
  return buildStructTimeC dt.y dt.m dt.d dt.h dt.mi dt.s flag

/-- `datetime.utctimetuple()`, Py:2072-2079. -/
def dtUtctimetuplePy (env : TzEnv) (self : DT) : Py TimeTuple := do
  let offset ← self.utcoffsetPy env
  let u ← match offset with
    | some o => if o.bool then dtSubDeltaPy self o else pure self
    | none => pure self
  return buildStructTimePy u.y u.m u.d u.h u.mi u.s 0

/-- `datetime_utctimetuple`, :7154-7191. -/
def dtUtctimetupleC (env : TzEnv) (self : DT) : Py TimeTuple := do
  let offset ← self.utcoffsetC env
  let u ← match offset with
    | some o => addDatetimeTimedeltaC self o (-1)
    | none => pure self
  return buildStructTimeC u.y u.m u.d u.h u.mi u.s 0

/-! ### `tzinfo.fromutc`, `timezone.fromutc`, `astimezone` -/

/-- `tzinfo.fromutc`, Py:1341-1366, for a `datetime` argument. `tzoid` is `self`. -/
def tzinfoFromutcPy (env : TzEnv) (tzoid : Nat) (dt : DT) : Py DT := do
  if dt.tz.map (·.oid) ≠ some tzoid then throw (.valueError "dt.tzinfo is not self")
  let dtoff ← dt.utcoffsetPy env
  let some dtoff := dtoff
    | throw (.valueError "fromutc() requires a non-None utcoffset() result")
  let dtdst ← dt.dstPy env
  let some dtdst := dtdst
    | throw (.valueError "fromutc() requires a non-None dst() result")
  let delta ← dtoff.subPy dtdst
  if delta.bool then
    let dt ← dtAddPy dt delta
    let dtdst ← dt.dstPy env
    let some dtdst := dtdst
      | throw (.valueError "fromutc(): dt.dst gave inconsistent results; cannot convert")
    dtAddPy dt dtdst
  else dtAddPy dt dtdst

/-- `tzinfo_fromutc`, :4179-4249. -/
def tzinfoFromutcC (env : TzEnv) (tzoid : Nat) (dt : DT) : Py DT := do
  if dt.tz.map (·.oid) ≠ some tzoid then throw (.valueError "fromutc: dt.tzinfo is not self")
  let off ← dt.utcoffsetC env
  let some off := off
    | throw (.valueError "fromutc: non-None utcoffset() result required")
  let dst ← dt.dstC env
  let some dst := dst
    | throw (.valueError "fromutc: non-None dst() result required")
  let delta ← off.subC dst
  let result ← addDatetimeTimedeltaC dt delta 1
  let dst ← result.dstC env
  let some dst := dst
    | throw (.valueError "fromutc: tz.dst() gave inconsistent results; cannot convert")
  if dst.bool then addDatetimeTimedeltaC result dst 1 else return result

/-- `timezone.fromutc`, Py:2544-2551. -/
def timezoneFromutcPy (tz : Tz) (offset : Delta) (dt : DT) : Py DT :=
  if dt.tz.map (·.oid) ≠ some tz.oid then .error (.valueError "fromutc: dt.tzinfo is not self")
  else dtAddPy dt offset

/-- `timezone_fromutc`, :4507-4523. -/
def timezoneFromutcC (tz : Tz) (offset : Delta) (dt : DT) : Py DT :=
  if dt.tz.map (·.oid) ≠ some tz.oid then .error (.valueError "fromutc: dt.tzinfo is not self")
  else addDatetimeTimedeltaC dt offset 1

/-- `tz.fromutc(dt)` in Python. -/
def tzFromutcPy (env : TzEnv) (tz : Tz) (dt : DT) : Py DT :=
  match tz.kind with
  | .timezone offset _ => timezoneFromutcPy tz offset dt
  | .custom _ => tzinfoFromutcPy env tz.oid dt

/-- `tz.fromutc(dt)` in C. -/
def tzFromutcC (env : TzEnv) (tz : Tz) (dt : DT) : Py DT :=
  match tz.kind with
  | .timezone offset _ => timezoneFromutcC tz offset dt
  | .custom _ => tzinfoFromutcC env tz.oid dt

/-- `datetime.astimezone(tz)`, Py:2137-2160, for an aware `self` whose tzinfo gives
a non-None offset. A naive `self` (or `utcoffset()` returning `None`) goes through
the local time zone and is reported as `platformLocal`. The result of
`mytz.utcoffset(self)` is not checked here, unlike `self.utcoffset()`. -/
def dtAstimezonePy (env : TzEnv) (self : DT) (tz : Tz) : Py (Option DT) := do
  let some mytz := self.tz | return none
  let myoffset ← tzUtcoffsetRaw env mytz (some self)
  match myoffset with
  | .none => return none
  | .other ty =>
    if tz.oid = mytz.oid then return some self
    throw (.typeError s!"~unsupported operand type(s) for -: 'datetime' and '{ty}'")
  | .delta o =>
    if tz.oid = mytz.oid then return some self
    let u ← dtSubDeltaPy self o
    let u ← dtReplace u none none none none none none none none (some (some tz))
    some <$> tzFromutcPy env tz u

/-- `datetime_datetime_astimezone_impl`, :6914-7004, same domain as `dtAstimezonePy`. -/
def dtAstimezoneC (env : TzEnv) (self : DT) (tz : Tz) : Py (Option DT) := do
  let some mytz := self.tz | return none
  if mytz.oid = tz.oid then return some self
  let offset ← callTzinfoCheckC "utcoffset" (← tzUtcoffsetRaw env mytz (some self))
  let some o := offset | return none
  let r ← addDatetimeTimedeltaC self o (-1)
  some <$> tzFromutcC env tz { r with tz := some tz }

/-! ### Pickle state -/

/-- `date._getstate`, Py:1300-1302, and `date_getstate`, :4004-4010. -/
def dateGetstate (y m d : Int) : List Nat := dateData y m d

/-- `date.__setstate`, Py:1304-1306, and `date_from_pickle`, :3221-3232. -/
def dateSetstate : List Nat → Option (Int × Int × Int)
  | [yhi, ylo, m, d] => some (yhi * 256 + ylo, m, d)
  | _ => none

/-- `time._getstate(protocol)`, Py:1753-1764, and `time_getstate`, :5269-5287. -/
def tmGetstate (t : TM) (protocol : Int) : List Nat :=
  match timeData t with
  | h :: rest => (if t.fold ≠ 0 ∧ protocol > 3 then h + 128 else h) :: rest
  | [] => []

/-- `time.__setstate`, Py:1766-1777, and `time_from_pickle`, :4678-4707. -/
def tmSetstate (tz : Option Tz) : List Nat → Option TM
  | [h, mi, s, us1, us2, us3] =>
    let (fold, h) := if h > 127 then (1, h - 128) else (0, h)
    some ⟨h, mi, s, ((us1 * 256 + us2) * 256 + us3 : Nat), fold, tz⟩
  | _ => none

/-- `datetime._getstate(protocol)`, Py:2402-2415, and `datetime_getstate`, :7201-7219. -/
def dtGetstate (dt : DT) (protocol : Int) : List Nat :=
  match dtData dt with
  | yhi :: ylo :: m :: rest => yhi :: ylo :: (if dt.fold ≠ 0 ∧ protocol > 3 then m + 128 else m) :: rest
  | l => l

/-- `datetime.__setstate`, Py:2417-2430, and `datetime_from_pickle`, :5455-5484. -/
def dtSetstate (tz : Option Tz) : List Nat → Option DT
  | [yhi, ylo, m, d, hh, mi, s, us1, us2, us3] =>
    let (fold, m) := if m > 127 then (1, m - 128) else (0, m)
    some ⟨(yhi * 256 + ylo : Nat), m, d, hh, mi, s, ((us1 * 256 + us2) * 256 + us3 : Nat), fold, tz⟩
  | _ => none

end PyLean.Datetime
