import PyLean.Datetime.Tz

/-!
Operators and methods of `timedelta`, `date`, `time`, `datetime` that the first
layer of the model did not cover: comparison, `datetime` arithmetic, `combine`,
`replace`, `fromutc`, `astimezone` with an explicit `tz`, time tuples, `repr`,
`ctime`, hash keys and pickle state. Python and C are mirrored separately where
they differ. Citations are to `Lib/_pydatetime.py` (Py) and
`Modules/_datetimemodule.c` (C) of 3.14.7.
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

/-- `diff_to_bool(diff, op)`, _datetimemodule.c:2109-2112. -/
def diffToBool (diff : Int) : CmpOp → Bool
  | .lt => decide (diff < 0)
  | .le => decide (diff ≤ 0)
  | .eq => decide (diff = 0)
  | .ne => decide (diff ≠ 0)
  | .gt => decide (diff > 0)
  | .ge => decide (diff ≥ 0)

/-! ### `timedelta` -/

namespace Delta

/-- `timedelta._getstate`, Py:940-941; C `delta_getstate`, :3013-3018. -/
def getstate (t : Delta) : List Int := [t.days, t.seconds, t.us]

/-- `timedelta._cmp`, Py:924-926. -/
def cmpPy (a b : Delta) : Int := cmpTuple a.getstate b.getstate

/-- `delta_cmp`, :2526-2536. -/
def cmpC (a b : Delta) : Int :=
  let diff := a.days - b.days
  if diff = 0 then
    let diff := a.seconds - b.seconds
    if diff = 0 then a.us - b.us else diff
  else diff

/-- `timedelta.__eq__`..`__gt__`, Py:894-922 (`__ne__` is the default inverse of `__eq__`). -/
def richPy (op : CmpOp) (a b : Delta) : Bool := diffToBool (a.cmpPy b) op

/-- `delta_richcompare`, :2539-2548. -/
def richC (op : CmpOp) (a b : Delta) : Bool := diffToBool (a.cmpC b) op

/-- `timedelta.__bool__`, Py:933-936; C `delta_bool`, :2924-2929. -/
def bool (t : Delta) : Bool := t.days != 0 || t.seconds != 0 || t.us != 0

/-- `timedelta.__pos__`, Py:830-831. -/
def posPy (a : Delta) : Delta := a

/-- `delta_positive`, :2476-2485 (no normalization, range already valid). -/
def posC (a : Delta) : Py Delta := do
  checkDeltaDayRange a.days
  return ⟨a.days, a.seconds, a.us⟩

/-- `timedelta.__rsub__`, Py:818-821: `other - self` as `-self + other`. -/
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

/-- `timedelta.__hash__`, Py:928-931, and `delta_hash`, :2553-2566. -/
def Delta.hashKey (t : Delta) : HashKey := .ints t.getstate

/-! ### `date` -/

/-- `date._cmp`, Py:1198-1203. -/
def dateCmpPy (a b : Int × Int × Int) : Int :=
  cmpTuple [a.1, a.2.1, a.2.2] [b.1, b.2.1, b.2.2]

/-- `date.__eq__`..`__gt__`, Py:1173-1196: `none` is `NotImplemented` (a `datetime` operand). -/
def dateRichPy (op : CmpOp) (a b : Int × Int × Int) (otherIsDatetime : Bool) : Option Bool :=
  if otherIsDatetime then none else some (diffToBool (dateCmpPy a b) op)

/-- `date_richcompare`, :3835-3853. -/
def dateRichC (op : CmpOp) (a b : Int × Int × Int) (otherIsDatetime : Bool) : Option Bool :=
  if otherIsDatetime then none
  else some (diffToBool (memcmpBytes (dateData a.1 a.2.1 a.2.2) (dateData b.1 b.2.1 b.2.2)) op)

/-- `date.__hash__`, Py:1205-1209: the hash of the one-element state tuple. -/
def dateHashKeyPy (y m d : Int) : HashKey := .tuple1 (dateData y m d)

/-- `date_hash` through `generic_hash`, :3883-3903. -/
def dateHashKeyC (y m d : Int) : HashKey := .bytes (dateData y m d)

/-- `date.weekday()`, Py:1234-1236. -/
def dateWeekdayPy (y m d : Int) : Int := (toordinal y m d + 6) % 7

/-- `date_weekday`, :3913-3917, through `weekday`. -/
def dateWeekdayC (y m d : Int) : Int := weekdayC y m d

/-- `date.isoweekday()`, Py:1240-1243. -/
def dateIsoweekdayPy (y m d : Int) : Int :=
  let r := toordinal y m d % 7
  if r = 0 then 7 else r

/-- `date_isoweekday`, :3641-3646. -/
def dateIsoweekdayC (y m d : Int) : Int := weekdayC y m d + 1

/-- `date.__sub__(date)`, Py:1224-1232. -/
def dateSubDatePy (a b : Int × Int × Int) : Py Delta :=
  deltaPy (toordinal a.1 a.2.1 a.2.2 - toordinal b.1 b.2.1 b.2.2) 0 0 0 0 0 0

/-- `date_subtract` with a date, :3540-3564: `new_delta(l - r, 0, 0, 0)`. -/
def dateSubDateC (a b : Int × Int × Int) : Py Delta := do
  let d := ymdToOrdC a.1 a.2.1 a.2.2 - ymdToOrdC b.1 b.2.1 b.2.2
  checkDeltaDayRange d
  return ⟨d, 0, 0⟩

/-- `date.__sub__(timedelta)`, Py:1226-1227: `self + timedelta(-other.days)`. -/
def dateSubDeltaPy (y m d : Int) (t : Delta) : Py (Int × Int × Int) := do
  dateAddPy y m d (← deltaPy (-t.days) 0 0 0 0 0 0)

/-- `add_date_timedelta` with `negate = 1`, :3496-3510. -/
def dateSubDeltaC (y m d : Int) (t : Delta) : Py (Int × Int × Int) := do
  let (y, m, d) ← normalizeYMDC y m (d + -t.days)
  checkDate y m d

/-- `date.replace`, Py:1159-1167. -/
def dateReplacePy (y m d : Int) (ny nm nd : Option Int) : Py (Int × Int × Int) :=
  checkDate (ny.getD y) (nm.getD m) (nd.getD d)

/-- `datetime_date_replace_impl`, :3875-3880, through `new_date_subclass_ex`
(:1182-1198) and `new_date_ex` (:1159-1171). The clinic `"i"` conversion is modelled
by `fitsCInt`. -/
def dateReplaceC (y m d : Int) (ny nm nd : Option Int) : Py (Int × Int × Int) :=
  let (y, m, d) := (ny.getD y, nm.getD m, nd.getD d)
  if ¬(fitsCInt y ∧ fitsCInt m ∧ fitsCInt d) then
    .error (.overflowError "~signed integer is greater than maximum")
  else checkDate y m d

/-! ### Time tuples -/

/-- `time.struct_time` as nine ints. -/
abbrev TimeTuple := List Int

/-- `_build_struct_time`, Py:161-164. -/
def buildStructTimePy (y m d hh mm ss dstflag : Int) : TimeTuple :=
  let wday := (ymd2ord y m d + 6) % 7
  let dnum := daysBeforeMonth y m + d
  [y, m, d, hh, mm, ss, wday, dnum, dstflag]

/-- `build_struct_time`, :2081-2099. -/
def buildStructTimeC (y m d hh mm ss dstflag : Int) : TimeTuple :=
  [y, m, d, hh, mm, ss, weekdayC y m d, daysBeforeMonth y m + d, dstflag]

/-- `date.timetuple()`, Py:1146-1149. -/
def dateTimetuplePy (y m d : Int) : TimeTuple := buildStructTimePy y m d 0 0 0 (-1)

/-- `date_timetuple`, :3856-3862. -/
def dateTimetupleC (y m d : Int) : TimeTuple := buildStructTimeC y m d 0 0 0 (-1)

/-! ### `ctime` -/

def dayNames : List String := ["", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]
def monthNames : List String :=
  ["", "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]

/-- `'%2d' % n` for `0 <= n`. -/
def fmt2Space (n : Int) : String :=
  let s := fmtD n
  if s.length < 2 then " " ++ s else s

/-- `date.ctime()`, Py:1091-1097, and `datetime.ctime()`, Py:2115-2123. -/
def ctimePy (y m d hh mm ss : Int) : String :=
  let wd := toordinal y m d % 7
  let wd := if wd = 0 then 7 else wd
  s!"{dayNames.getD wd.toNat ""} {monthNames.getD m.toNat ""} {fmt2Space d} {fmt0 2 hh}:{fmt0 2 mm}:{fmt0 2 ss} {fmt0 4 y}"

/-- `format_ctime`, :1692-1708. -/
def ctimeC (y m d hh mm ss : Int) : String :=
  let wday := weekdayC y m d
  s!"{dayNames.getD (wday + 1).toNat ""} {monthNames.getD m.toNat ""} {fmt2Space d} {fmt0 2 hh}:{fmt0 2 mm}:{fmt0 2 ss} {fmt0 4 y}"

/-! ### `repr` -/

/-- `_get_class_module(self)`, Py:17-22. -/
def getClassModule (moduleName : String) : String :=
  if moduleName = "datetime" then "datetime." else ""

/-- `date.__repr__`, Py:1073-1084. -/
def dateReprPy (y m d : Int) : String :=
  s!"{getClassModule "datetime"}date({fmtD y}, {fmtD m}, {fmtD d})"

/-- `date_repr`, :3570-3576. -/
def dateReprC (y m d : Int) : String := s!"datetime.date({fmtD y}, {fmtD m}, {fmtD d})"

/-- `s[:-1] + ", tzinfo=%r" % tz + ")"`, and C `append_keyword_tzinfo`, :1620-1637. -/
def appendTzinfo (env : TzEnv) (s : String) (tz : Option Tz) : String :=
  match tz with
  | none => s
  | some t => (s.dropEnd 1).toString ++ s!", tzinfo={t.repr env})"

/-- `s[:-1] + ", fold=1)"`, and C `append_keyword_fold`, :1645-1661. -/
def appendFold (s : String) (fold : Int) : String :=
  if fold = 0 then s else (s.dropEnd 1).toString ++ s!", fold={fmtD fold})"

/-- The positional part of `time.__repr__`, Py:1578-1585. -/
def tmReprBasePy (t : TM) : String :=
  let s := if t.us ≠ 0 then s!", {fmtD t.s}, {fmtD t.us}"
    else if t.s ≠ 0 then s!", {fmtD t.s}" else ""
  s!"{getClassModule "datetime"}time({fmtD t.h}, {fmtD t.mi}{s})"

/-- `time.__repr__`, Py:1576-1593. -/
def timeReprPy (env : TzEnv) (t : TM) : String :=
  appendFold (appendTzinfo env (tmReprBasePy t) t.tz) t.fold

/-- The positional part of `time_repr`, :4781-4787. -/
def tmReprBaseC (t : TM) : String :=
  if t.us ≠ 0 then s!"datetime.time({fmtD t.h}, {fmtD t.mi}, {fmtD t.s}, {fmtD t.us})"
  else if t.s ≠ 0 then s!"datetime.time({fmtD t.h}, {fmtD t.mi}, {fmtD t.s})"
  else s!"datetime.time({fmtD t.h}, {fmtD t.mi})"

/-- `time_repr`, :4771-4795. -/
def timeReprC (env : TzEnv) (t : TM) : String :=
  appendFold (appendTzinfo env (tmReprBaseC t) t.tz) t.fold

/-- The positional part of `datetime.__repr__`, Py:2154-2161. -/
def dtReprBasePy (dt : DT) : String :=
  let L := [dt.y, dt.m, dt.d, dt.h, dt.mi, dt.s, dt.us]
  let L := if L.getLast? = some 0 then L.dropLast else L
  let L := if L.getLast? = some 0 then L.dropLast else L
  s!"{getClassModule "datetime"}datetime({", ".intercalate (L.map fmtD)})"

/-- `datetime.__repr__`, Py:2152-2169. The tzinfo keyword comes before fold. -/
def dtReprPy (env : TzEnv) (dt : DT) : String :=
  appendFold (appendTzinfo env (dtReprBasePy dt) dt.tz) dt.fold

/-- The positional part of `datetime_repr`, :6216-6238. -/
def dtReprBaseC (dt : DT) : String :=
  let f (xs : List Int) := s!"datetime.datetime({", ".intercalate (xs.map fmtD)})"
  if dt.us ≠ 0 then f [dt.y, dt.m, dt.d, dt.h, dt.mi, dt.s, dt.us]
  else if dt.s ≠ 0 then f [dt.y, dt.m, dt.d, dt.h, dt.mi, dt.s]
  else f [dt.y, dt.m, dt.d, dt.h, dt.mi]

/-- `datetime_repr`, :6213-6248: fold is appended first, then tzinfo. -/
def dtReprC (env : TzEnv) (dt : DT) : String :=
  appendTzinfo env (appendFold (dtReprBaseC dt) dt.fold) dt.tz

/-- `IsoCalendarDate.__repr__`, Py:1376-1378. -/
def isoReprPy (y w d : Int) : String :=
  s!"IsoCalendarDate(year={fmtD y}, week={fmtD w}, weekday={fmtD d})"

/-- `iso_calendar_date_repr`, :3659-3676. -/
def isoReprC (y w d : Int) : String :=
  s!"datetime.IsoCalendarDate(year={fmtD y}, week={fmtD w}, weekday={fmtD d})"

/-! ### Offsets in `isoformat` -/

/-- `time._tzstr`, Py:1571-1574: `_format_offset(self.utcoffset())`. -/
def tmTzstrPy (env : TzEnv) (t : TM) : Py String := do
  let off ← t.utcoffsetPy env
  return String.ofList (formatOffset (off.map Delta.toUs))

/-- `time.isoformat`, Py:1595-1610. -/
def tmIsoformatPy (env : TzEnv) (t : TM) (spec : TimeSpec) : Py String := do
  let s := String.ofList (formatTime t.h t.mi t.s t.us spec)
  return s ++ (← tmTzstrPy env t)

/-- `time_isoformat`, :4804-4868, with `format_utcoffset` (:1723-1768). -/
def tmIsoformatC (env : TzEnv) (t : TM) (spec : TimeSpec) : Py String := do
  let s := String.ofList (formatTime t.h t.mi t.s t.us spec)
  let off ← t.utcoffsetC env
  return s ++ String.ofList (formatOffset (off.map Delta.toUs))

/-- `datetime.isoformat`, Py:2125-2150. -/
def dtIsoformatPy (env : TzEnv) (dt : DT) (sep : Char) (spec : TimeSpec) : Py String := do
  let s := String.ofList (dateIsoformat dt.y dt.m dt.d ++ [sep] ++ formatTime dt.h dt.mi dt.s dt.us spec)
  let off ← dt.utcoffsetPy env
  return s ++ String.ofList (formatOffset (off.map Delta.toUs))

/-- `datetime_isoformat`, :6263-6328. -/
def dtIsoformatC (env : TzEnv) (dt : DT) (sep : Char) (spec : TimeSpec) : Py String := do
  let s := String.ofList (dateIsoformat dt.y dt.m dt.d ++ [sep] ++ formatTime dt.h dt.mi dt.s dt.us spec)
  let off ← dt.utcoffsetC env
  return s ++ String.ofList (formatOffset (off.map Delta.toUs))

/-! ### `time`: comparison and hash -/

/-- The fields compared in the base case. -/
def TM.base (t : TM) : List Int := [t.h, t.mi, t.s, t.us]

/-- `myoff // timedelta(minutes=1)`. -/
def floorMinutes (off : Delta) : Int := off.toUs / 60000000

/-- `time._cmp`, Py:1520-1546. -/
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

/-- `time.__eq__`..`__gt__`, Py:1490-1518 (`__ne__` inverts `__eq__`). -/
def tmRichPy (env : TzEnv) (op : CmpOp) (a b : TM) : Py Bool := do
  match op with
  | .eq => return (← tmCmpPy env a b true) == 0
  | .ne => return (← tmCmpPy env a b true) != 0
  | .le => return diffToBool (← tmCmpPy env a b false) .le
  | .lt => return diffToBool (← tmCmpPy env a b false) .lt
  | .ge => return diffToBool (← tmCmpPy env a b false) .ge
  | .gt => return diffToBool (← tmCmpPy env a b false) .gt

/-- `time_richcompare`, :4907-4975. -/
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

/-- `time.__hash__`, Py:1548-1567; `none` key means the `assert` failed with
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

/-- `time_hash`, :4978-5034. The `timedelta` arithmetic cannot leave its range. -/
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

/-- `datetime.date()`, Py:2031-2033, and `datetime_getdate`, :6932-6938. -/
def dtDate (dt : DT) : Int × Int × Int := dt.ymd

/-- `datetime.time()`, Py:2035-2037, and `datetime_gettime`, :6941-6950. -/
def dtTime (dt : DT) : TM := ⟨dt.h, dt.mi, dt.s, dt.us, dt.fold, none⟩

/-- `datetime.timetz()`, Py:2039-2042, and `datetime_gettimetz`, :6953-6962. -/
def dtTimetz (dt : DT) : TM := ⟨dt.h, dt.mi, dt.s, dt.us, dt.fold, dt.tz⟩

/-- The fold check at the end of `_check_time_fields`, Py:585-586, and
`check_time_args`, :703-707. -/
def checkFold (fold : Int) : Py Unit :=
  if fold = 0 ∨ fold = 1 then .ok ()
  else .error (.valueError s!"fold must be either 0 or 1, not {fold}")

/-- `datetime(year, ..., tzinfo, fold=fold)` for int fields: `_check_date_fields`,
`_check_time_fields`, Py:1755-1788; `new_datetime_ex2`, :1202-1232. -/
def newDT (dt : DT) : Py DT := do
  let _ ← checkDate dt.y dt.m dt.d
  let _ ← checkTime dt.h dt.mi dt.s dt.us
  checkFold dt.fold
  return dt

/-- `time(hour, ..., tzinfo, fold=fold)` for int fields: Py:1411-1448;
`new_time_ex2`, :1310-1337. -/
def newTM (t : TM) : Py TM := do
  let _ ← checkTime t.h t.mi t.s t.us
  checkFold t.fold
  return t

/-- `datetime.combine(date, time, tzinfo)`, Py:1906-1916, and `datetime_combine`,
:5723-5752, for the date and time objects it takes. `tz = none` is the default
`tzinfo=True`, `tz = some x` an explicit value (`some none` is `None`). -/
def dtCombine (ymd : Int × Int × Int) (t : TM) (tz : Option (Option Tz)) : Py DT :=
  newDT ⟨ymd.1, ymd.2.1, ymd.2.2, t.h, t.mi, t.s, t.us, t.fold, tz.getD t.tz⟩

/-- `datetime.replace`, Py:2044-2067, for int fields. -/
def dtReplace (dt : DT) (y m d h mi s us fold : Option Int) (tz : Option (Option Tz)) : Py DT :=
  newDT ⟨y.getD dt.y, m.getD dt.m, d.getD dt.d, h.getD dt.h, mi.getD dt.mi, s.getD dt.s,
    us.getD dt.us, fold.getD dt.fold, tz.getD dt.tz⟩

/-- `time.replace`, Py:1687-1702, for int fields. -/
def tmReplace (t : TM) (h mi s us fold : Option Int) (tz : Option (Option Tz)) : Py TM :=
  newTM ⟨h.getD t.h, mi.getD t.mi, s.getD t.s, us.getD t.us, fold.getD t.fold, tz.getD t.tz⟩

/-! ### `datetime`: arithmetic -/

/-- `datetime.__add__`, Py:2287-2304. -/
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

/-- `normalize_datetime`, :844-853. -/
def normalizeDatetimeC (y m d hh mi s us : Int) : Py DT :=
  let (s, us) := normalizePair s us 1000000
  let (mi, s) := normalizePair mi s 60
  let (hh, mi) := normalizePair hh mi 60
  let (d, hh) := normalizePair d hh 24
  normalizeTailC hh mi s us (normalizeYMDC y m d)

/-- `add_datetime_timedelta`, :6076-6101, with the `factor` of the caller. -/
def addDatetimeTimedeltaC (dt : DT) (delta : Delta) (factor : Int) : Py DT := do
  let r ← normalizeDatetimeC dt.y dt.m (dt.d + delta.days * factor) dt.h dt.mi
    (dt.s + delta.seconds * factor) (dt.us + delta.us * factor)
  newDT { r with tz := dt.tz }

/-- `datetime.__sub__(timedelta)`, Py:2311-2313: `self + -other`. -/
def dtSubDeltaPy (dt : DT) (other : Delta) : Py DT := do dtAddPy dt (← other.negPy)

/-- `datetime.__sub__(datetime)`, Py:2308-2330. -/
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

/-- `datetime_subtract` for two datetimes, :6125-6208. -/
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

/-- `datetime._cmp`, Py:2250-2285. -/
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

/-- `datetime.__eq__`..`__gt__`, Py:2220-2248. -/
def dtRichPy (env : TzEnv) (op : CmpOp) (a b : DT) : Py Bool := do
  match op with
  | .eq => return (← dtCmpPy env a b true) == 0
  | .ne => return (← dtCmpPy env a b true) != 0
  | .le => return diffToBool (← dtCmpPy env a b false) .le
  | .lt => return diffToBool (← dtCmpPy env a b false) .lt
  | .ge => return diffToBool (← dtCmpPy env a b false) .ge
  | .gt => return diffToBool (← dtCmpPy env a b false) .gt

/-- `get_flip_fold_offset`, :6359-6369, through `flip_fold`, :6343-6356. -/
def getFlipFoldOffsetC (env : TzEnv) (dt : DT) : Py (Option Delta) := dt.flipFold.utcoffsetC env

/-- `pep495_eq_exception`, :6378-6404. -/
def pep495EqExceptionC (env : TzEnv) (self other : DT) (o1 o2 : Option Delta) : Py Bool := do
  let f1 ← getFlipFoldOffsetC env self
  if !offEq f1 o1 then return true
  let f2 ← getFlipFoldOffsetC env other
  return !offEq f2 o2

/-- `datetime_richcompare`, :6407-6485. -/
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

/-- `datetime.__hash__`, Py:2332-2345. -/
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

/-- `datetime_hash`, :6488-6552. -/
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

/-- `datetime.timetuple()`, Py:1966-1977. -/
def dtTimetuplePy (env : TzEnv) (dt : DT) : Py TimeTuple := do
  let dst ← dt.dstPy env
  let flag : Int := match dst with
    | none => -1
    | some o => if o.bool then 1 else 0
  return buildStructTimePy dt.y dt.m dt.d dt.h dt.mi dt.s flag

/-- `datetime_timetuple`, :6818-6841. -/
def dtTimetupleC (env : TzEnv) (dt : DT) : Py TimeTuple := do
  let dst ← dt.dstC env
  let flag : Int := match dst with
    | none => -1
    | some o => if o.bool then 1 else 0
  return buildStructTimeC dt.y dt.m dt.d dt.h dt.mi dt.s flag

/-- `datetime.utctimetuple()`, Py:2022-2029. -/
def dtUtctimetuplePy (env : TzEnv) (self : DT) : Py TimeTuple := do
  let offset ← self.utcoffsetPy env
  let u ← match offset with
    | some o => if o.bool then dtSubDeltaPy self o else pure self
    | none => pure self
  return buildStructTimePy u.y u.m u.d u.h u.mi u.s 0

/-- `datetime_utctimetuple`, :6965-7002. -/
def dtUtctimetupleC (env : TzEnv) (self : DT) : Py TimeTuple := do
  let offset ← self.utcoffsetC env
  let u ← match offset with
    | some o => addDatetimeTimedeltaC self o (-1)
    | none => pure self
  return buildStructTimeC u.y u.m u.d u.h u.mi u.s 0

/-! ### `tzinfo.fromutc`, `timezone.fromutc`, `astimezone` -/

/-- `tzinfo.fromutc`, Py:1316-1341, for a `datetime` argument. `tzoid` is `self`. -/
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

/-- `tzinfo_fromutc`, :4120-4190. -/
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

/-- `timezone.fromutc`, Py:2489-2496. -/
def timezoneFromutcPy (tz : Tz) (offset : Delta) (dt : DT) : Py DT :=
  if dt.tz.map (·.oid) ≠ some tz.oid then .error (.valueError "fromutc: dt.tzinfo is not self")
  else dtAddPy dt offset

/-- `timezone_fromutc`, :4444-4460. -/
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

/-- `datetime.astimezone(tz)`, Py:2088-2111, for an aware `self` whose tzinfo gives
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

/-- `datetime_astimezone`, :6720-6815, same domain as `dtAstimezonePy`. -/
def dtAstimezoneC (env : TzEnv) (self : DT) (tz : Tz) : Py (Option DT) := do
  let some mytz := self.tz | return none
  if mytz.oid = tz.oid then return some self
  let offset ← callTzinfoCheckC "utcoffset" (← tzUtcoffsetRaw env mytz (some self))
  let some o := offset | return none
  let r ← addDatetimeTimedeltaC self o (-1)
  some <$> tzFromutcC env tz { r with tz := some tz }

/-! ### Pickle state -/

/-- `date._getstate`, Py:1275-1277, and `date_getstate`, :3923-3929. -/
def dateGetstate (y m d : Int) : List Nat := dateData y m d

/-- `date.__setstate`, Py:1279-1281, and `date_from_pickle`, :3219-3230. -/
def dateSetstate : List Nat → Option (Int × Int × Int)
  | [yhi, ylo, m, d] => some (yhi * 256 + ylo, m, d)
  | _ => none

/-- `time._getstate(protocol)`, Py:1708-1719, and `time_getstate`, :5138-5156. -/
def tmGetstate (t : TM) (protocol : Int) : List Nat :=
  match timeData t with
  | h :: rest => (if t.fold ≠ 0 ∧ protocol > 3 then h + 128 else h) :: rest
  | [] => []

/-- `time.__setstate`, Py:1721-1732, and `time_from_pickle`, :4621-4650. -/
def tmSetstate (tz : Option Tz) : List Nat → Option TM
  | [h, mi, s, us1, us2, us3] =>
    let (fold, h) := if h > 127 then (1, h - 128) else (0, h)
    some ⟨h, mi, s, ((us1 * 256 + us2) * 256 + us3 : Nat), fold, tz⟩
  | _ => none

/-- `datetime._getstate(protocol)`, Py:2349-2362, and `datetime_getstate`, :7012-7030. -/
def dtGetstate (dt : DT) (protocol : Int) : List Nat :=
  match dtData dt with
  | yhi :: ylo :: m :: rest => yhi :: ylo :: (if dt.fold ≠ 0 ∧ protocol > 3 then m + 128 else m) :: rest
  | l => l

/-- `datetime.__setstate`, Py:2364-2377, and `datetime_from_pickle`, :5346-5375. -/
def dtSetstate (tz : Option Tz) : List Nat → Option DT
  | [yhi, ylo, m, d, hh, mi, s, us1, us2, us3] =>
    let (fold, m) := if m > 127 then (1, m - 128) else (0, m)
    some ⟨(yhi * 256 + ylo : Nat), m, d, hh, mi, s, ((us1 * 256 + us2) * 256 + us3 : Nat), fold, tz⟩
  | _ => none

end PyLean.Datetime
