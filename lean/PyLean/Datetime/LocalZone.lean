import PyLean.Datetime.Hollow0506Props

/-!
`datetime._local_timezone` (Lib/_pydatetime.py:2121-2135) and `datetime.astimezone`
(:2137-2160) with the local zone, against C's `local_timezone_from_local`,
`local_timezone`, `local_timezone_from_timestamp` and `datetime_datetime_astimezone_impl`
(Modules/_datetimemodule.c:6764-7004), CPython 3.15.2.

The C library's `localtime` is a parameter: `ltz u` is `time.localtime(u)` (or
`_PyTime_localtime`), the six fields, `tm_gmtoff` and `tm_zone`, or the `OSError` it raises.
The platform has `HAVE_STRUCT_TM_TM_ZONE` (as Linux and macOS do), and `tm_zone` is a `str`.
New `timezone` objects get the identities the caller passes (`o1` for the target zone, `o2`
for `self`'s), fresh by hypothesis in the theorems.
-/

namespace PyLean.Datetime
open PyLean

/-- `time.localtime(u)`: the six fields, `tm_gmtoff`, `tm_zone`. -/
abbrev LocalTmZ := LocalTm × Int × String

/-- The fields of `localtime(u)`, as `_mktime` and `local_to_seconds` read them. -/
def ltFields (ltz : Int → Py LocalTmZ) (u : Int) : Py LocalTm :=
  match ltz u with
  | .ok r => .ok r.1
  | .error e => .error e

/-- `_EPOCH = datetime(1970, 1, 1, tzinfo=timezone.utc)`, Py:2583, and C's `CONST_EPOCH`. -/
def epochDT : DT := ⟨1970, 1, 1, 0, 0, 0, 0, 0, some tzUTC⟩

/-! ### The zone from a timestamp -/

/-- Py:2131-2135 once `ts` is known: `localtm = _time.localtime(ts)` (an int `ts` is converted
to `time_t` first, `OverflowError` outside it), then
`timezone(timedelta(seconds=localtm.tm_gmtoff), localtm.tm_zone)`. -/
def localTzFromTsPy (ltz : Int → Py LocalTmZ) (oid : Nat) (ts : Int) : Py Tz := do
  if ¬ fitsTimeT ts then throw (.overflowError "timestamp out of range for platform time_t")
  let (_, gmtoff, zone) ← ltz ts
  let delta ← deltaPy 0 gmtoff 0 0 0 0 0
  timezoneNewPy oid delta (.str zone)

/-- `local_timezone_from_timestamp`, :6765-6823 with `HAVE_STRUCT_TM_TM_ZONE`:
`_PyTime_localtime(timestamp)` (:6776), `new_delta(0, tm_gmtoff, 0, 1)` (:6780), the zone
decoded (:6818-6822), and `new_timezone(delta, nameo)` (:6824), the range check and
`create_timezone` that `timezone_new_impl` also reaches with a `str` name. -/
def localTzFromTsC (ltz : Int → Py LocalTmZ) (oid : Nat) (ts : Int) : Py Tz := do
  let (_, gmtoff, zone) ← ltz ts
  let delta ← newDeltaNormC 0 gmtoff 0
  timezoneNewC oid delta (.str zone)

/-! ### `_local_timezone` and its C counterparts -/

/-- `datetime._local_timezone()`, Py:2121-2135: for a naive `self` the timestamp of
`localTimezoneTsPy` (`_mktime` for both folds, the gap test of :2124-2128); for an aware one
`(self - _EPOCH) // timedelta(seconds=1)` (:2130), which calls `self.utcoffset()` unless the
tzinfo is `timezone.utc` itself; then the zone of `localtime(ts)`. -/
def localTimezonePy (env : TzEnv) (ltz : Int → Py LocalTmZ) (oid : Nat) (self : DT) : Py Tz := do
  let ts ← if self.tz.isNone then localTimezoneTsPy (ltFields ltz) self 0
    else do
      let d ← dtSubPy env self epochDT
      pure (d.toUs / 1000000)
  localTzFromTsPy ltz oid ts

/-- `local_timezone_from_local`, :6873-6903: `local_to_seconds` of the fields with `fold` and
`!fold`, the gap test (:6897-6898), `timestamp = seconds - epoch` (:6901), then
`local_timezone_from_timestamp`. Only the fields are read, so a `self` with a tzinfo (the
`goto naive` of `astimezone`) is treated as naive. -/
def localTimezoneFromLocalC (ltz : Int → Py LocalTmZ) (oid : Nat) (self : DT) : Py Tz := do
  let ts ← localTimezoneTsC (ltFields ltz) { self with tz := none } 0
  localTzFromTsC ltz oid ts

/-- `local_timezone(utc_time)`, :6832-6870: `utc_time - CONST_EPOCH` (:6845),
`divide_timedelta_timedelta` by one second (floor division of the microseconds, :2407),
`_PyLong_AsTime_t` (:6861), then `local_timezone_from_timestamp`. -/
def localTimezoneC (env : TzEnv) (ltz : Int → Py LocalTmZ) (oid : Nat) (utc : DT) : Py Tz := do
  let d ← dtSubC env utc epochDT
  let secs := d.toUs / 1000000
  if ¬ fitsTimeT secs then throw (.overflowError "timestamp out of range for platform time_t")
  localTzFromTsC ltz oid secs

/-! ### `astimezone` with the local zone -/

/-- Py:2153-2160 once `tz`, `mytz` and `myoffset` are known: the identity shortcut, then
`(self - myoffset).replace(tzinfo=tz)` and `tz.fromutc(utc)`; `self - x` for a non-timedelta
`x` is the binary-operator `TypeError`. -/
def astzPyTail (env : TzEnv) (self : DT) (tz mytz : Tz) (myoffset : OffRet) : Py DT := do
  if tz.oid = mytz.oid then return self
  match myoffset with
  | .delta o =>
    let u ← dtSubDeltaPy self o
    let u ← dtReplace u none none none none none none none none (some (some tz))
    tzFromutcPy env tz u
  | .other ty => throw (.typeError s!"~unsupported operand type(s) for -: 'datetime' and '{ty}'")
  | .none => throw (.typeError "~unsupported operand type(s) for -: 'datetime' and 'NoneType'")

/-- `datetime.astimezone(tz)`, Py:2137-2160, every branch: `tz is None` takes
`self._local_timezone()` first (:2138-2139), a non-`tzinfo` is `TypeError` (:2140-2141); a
naive `self` uses `self._local_timezone()` as `mytz` (:2144-2146); an aware one asks
`mytz.utcoffset(self)` (unchecked, :2148) and on `None` uses
`self.replace(tzinfo=None)._local_timezone()` (:2149-2151); then `astzPyTail`. -/
def dtAstimezoneFullPy (env : TzEnv) (ltz : Int → Py LocalTmZ) (o1 o2 : Nat) (self : DT) (arg : AstzArg) :
    Py DT := do
  let tz ← match arg with
    | .none_ => localTimezonePy env ltz o1 self
    | .other => throw (.typeError "tz argument must be an instance of tzinfo")
    | .tz t => pure t
  match self.tz with
  | none =>
    let z ← localTimezonePy env ltz o2 self
    astzPyTail env self tz z (← tzUtcoffsetRaw env z (some self))
  | some z =>
    let o ← tzUtcoffsetRaw env z (some self)
    match o with
    | .none =>
      let naive ← dtReplace self none none none none none none none none (some none)
      let z' ← localTimezonePy env ltz o2 naive
      astzPyTail env self tz z' (← tzUtcoffsetRaw env z' (some self))
    | _ => astzPyTail env self tz z o

/-- :6957-7002 once the offset `o` is known: `self - offset` (`add_datetime_timedelta`), made
UTC (:6963-6984); for `tz` `None` the zone `local_timezone(result)` of the UTC result
(:6987-6993); then `tz.fromutc(result)` with `tz` attached (:6996-7002). -/
def astzCFinish (env : TzEnv) (ltz : Int → Py LocalTmZ) (o1 : Nat) (self : DT) (tzinfo : Option Tz) (o : Delta) :
    Py DT := do
  let r ← addDatetimeTimedeltaC self o (-1)
  let r : DT := { r with tz := some tzUTC }
  let t ← match tzinfo with
    | some t => pure t
    | none => localTimezoneC env ltz o1 r
  tzFromutcC env t { r with tz := some t }

/-- :6936-6957 once `self_tzinfo` is the local zone `z` (the `naive:` path): the identity
test, then `call_utcoffset` (checked), which a `timezone` never answers with `None`. -/
def astzCAfterLocal (env : TzEnv) (ltz : Int → Py LocalTmZ) (o1 : Nat) (self : DT) (tzinfo : Option Tz) (z : Tz) :
    Py DT := do
  if tzinfo.map (·.oid) = some z.oid then return self
  match ← callTzinfoCheckC "utcoffset" (← tzUtcoffsetRaw env z (some self)) with
  | some o => astzCFinish env ltz o1 self tzinfo o
  | none => throw .modelFuel

/-- `datetime_datetime_astimezone_impl`, :6914-7004, every branch: `check_tzinfo_subclass`
(:6923); a naive `self` takes `local_timezone_from_local(self)` (`naive:`, :6926-6930); an
aware one the identity test (:6936-6939) and `call_utcoffset` (:6942), a `None` going to
`naive:` (:6946-6949). -/
def dtAstimezoneFullC (env : TzEnv) (ltz : Int → Py LocalTmZ) (o1 o2 : Nat) (self : DT) (arg : AstzArg) :
    Py DT := do
  let tzinfo : Option Tz ← match arg with
    | .other => throw (.typeError "~tzinfo argument must be None or of a tzinfo subclass")
    | .none_ => pure none
    | .tz t => pure (some t)
  match self.tz with
  | none => astzCAfterLocal env ltz o1 self tzinfo (← localTimezoneFromLocalC ltz o2 self)
  | some z =>
    if tzinfo.map (·.oid) = some z.oid then return self
    match ← callTzinfoCheckC "utcoffset" (← tzUtcoffsetRaw env z (some self)) with
    | some o => astzCFinish env ltz o1 self tzinfo o
    | none => astzCAfterLocal env ltz o1 self tzinfo (← localTimezoneFromLocalC ltz o2 self)

end PyLean.Datetime

