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

/-- `local_timezone_from_timestamp`, :6764-6823 with `HAVE_STRUCT_TM_TM_ZONE`:
`_PyTime_localtime(timestamp)` (:6776), `new_delta(0, tm_gmtoff, 0, 1)` (:6780), the zone
decoded (:6815-6819), and `new_timezone(delta, nameo)` (:6820), the range check and
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

/-- `local_timezone(utc_time)`, :6831-6870: `utc_time - CONST_EPOCH` (:6843),
`divide_timedelta_timedelta` by one second (floor division of the microseconds, :2407),
`_PyLong_AsTime_t` (:6859), then `local_timezone_from_timestamp`. -/
def localTimezoneC (env : TzEnv) (ltz : Int → Py LocalTmZ) (oid : Nat) (utc : DT) : Py Tz := do
  let d ← dtSubC env utc epochDT
  let secs := d.toUs / 1000000
  if ¬ fitsTimeT secs then throw (.overflowError "timestamp out of range for platform time_t")
  localTzFromTsC ltz oid secs

/-! ### `astimezone` with the local zone -/

/-- `datetime.astimezone(tz)`, Py:2137-2160, every branch: `tz is None` takes
`self._local_timezone()` first (:2138-2139), a non-`tzinfo` is `TypeError` (:2140-2141); a
naive `self` uses `self._local_timezone()` as `mytz` (:2144-2146); an aware one asks
`mytz.utcoffset(self)` (unchecked, :2148) and on `None` uses
`self.replace(tzinfo=None)._local_timezone()` (:2149-2151); then the identity shortcut
(:2153-2154), `(self - myoffset).replace(tzinfo=tz)` (:2157) and `tz.fromutc` (:2160). -/
def dtAstimezoneFullPy (env : TzEnv) (ltz : Int → Py LocalTmZ) (o1 o2 : Nat) (self : DT) (arg : AstzArg) :
    Py DT := do
  let tz ← match arg with
    | .none_ => localTimezonePy env ltz o1 self
    | .other => throw (.typeError "tz argument must be an instance of tzinfo")
    | .tz t => pure t
  let (mytz, myoffset) ← match self.tz with
    | none => do
      let z ← localTimezonePy env ltz o2 self
      pure (z, ← tzUtcoffsetRaw env z (some self))
    | some z => do
      let o ← tzUtcoffsetRaw env z (some self)
      match o with
      | .none => do
        let naive ← dtReplace self none none none none none none none none (some none)
        let z' ← localTimezonePy env ltz o2 naive
        pure (z', ← tzUtcoffsetRaw env z' (some self))
      | _ => pure (z, o)
  if tz.oid = mytz.oid then return self
  match myoffset with
  | .delta o =>
    let u ← dtSubDeltaPy self o
    let u ← dtReplace u none none none none none none none none (some (some tz))
    tzFromutcPy env tz u
  | .other ty => throw (.typeError s!"~unsupported operand type(s) for -: 'datetime' and '{ty}'")
  | .none => throw (.typeError "~unsupported operand type(s) for -: 'datetime' and 'NoneType'")

/-- `datetime_datetime_astimezone_impl`, :6914-7004, every branch: `check_tzinfo_subclass`
(:6922); a naive `self` takes `local_timezone_from_local(self)` (`naive:`, :6925-6928); the
identity test (:6934-6937); `call_utcoffset` (checked, :6940), a `None` going back to `naive:`
(:6944-6947, where the local `timezone` never answers `None`); `self - offset` (:6955),
made UTC (:6962-6982); for `tz` `None` the zone `local_timezone(result)` of the UTC result
(:6985-6991); then `tz.fromutc` (:6996-6998). -/
def dtAstimezoneFullC (env : TzEnv) (ltz : Int → Py LocalTmZ) (o1 o2 : Nat) (self : DT) (arg : AstzArg) :
    Py DT := do
  let tzinfo : Option Tz ← match arg with
    | .other => throw (.typeError "~tzinfo argument must be None or of a tzinfo subclass")
    | .none_ => pure none
    | .tz t => pure (some t)
  let finish : Delta → Py DT := fun o => do
    let r ← addDatetimeTimedeltaC self o (-1)
    let r : DT := { r with tz := some tzUTC }
    let t ← match tzinfo with
      | some t => pure t
      | none => localTimezoneC env ltz o1 r
    tzFromutcC env t { r with tz := some t }
  let naive : Py DT := do
    let z ← localTimezoneFromLocalC ltz o2 self
    if tzinfo.map (·.oid) = some z.oid then return self
    match ← callTzinfoCheckC "utcoffset" (← tzUtcoffsetRaw env z (some self)) with
    | some o => finish o
    | none => throw .modelFuel
  match self.tz with
  | none => naive
  | some z =>
    if tzinfo.map (·.oid) = some z.oid then return self
    match ← callTzinfoCheckC "utcoffset" (← tzUtcoffsetRaw env z (some self)) with
    | some o => finish o
    | none => naive

end PyLean.Datetime
