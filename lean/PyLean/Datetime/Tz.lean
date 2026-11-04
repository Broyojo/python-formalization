import PyLean.Datetime.IsoC
import PyLean.Datetime.Format

/-!
`tzinfo`, `timezone` and the `time`/`datetime` objects that carry them.

`tzinfo` is an abstract class, so the model is generic over it: a `Tz` is either
a `timezone` instance or an instance of an arbitrary subclass, whose methods
come from a `TzEnv`. A subclass method may return any object or raise, which
`OffRet`/`NameRet` and `Py` express. Theorems quantify over every `TzEnv`; the
differential test instantiates one with real `tzinfo` subclasses.

Object identity matters (`mytz is ottz`), so a `Tz` carries an `oid`. The
singleton `timezone.utc` has `oid = 0`.
-/

namespace PyLean.Datetime

open PyLean

inductive TzKind where
  /-- A `datetime.timezone` instance. -/
  | timezone (offset : Delta) (name : Option String)
  /-- An instance of a `tzinfo` subclass; `impl` selects its methods in `TzEnv`. -/
  | custom (impl : Nat)
  deriving Repr, DecidableEq, Inhabited

structure Tz where
  /-- `id(obj)`. -/
  oid : Nat
  kind : TzKind
  deriving Repr, DecidableEq, Inhabited

/-- `timezone.utc`, _pydatetime.py:2576. -/
def tzUTC : Tz := ⟨0, .timezone ⟨0, 0, 0⟩ none⟩

/-- A `datetime` object. -/
structure DT where
  y : Int
  m : Int
  d : Int
  h : Int := 0
  mi : Int := 0
  s : Int := 0
  us : Int := 0
  fold : Int := 0
  tz : Option Tz := none
  deriving Repr, DecidableEq, Inhabited

/-- A `time` object. -/
structure TM where
  h : Int := 0
  mi : Int := 0
  s : Int := 0
  us : Int := 0
  fold : Int := 0
  tz : Option Tz := none
  deriving Repr, DecidableEq, Inhabited

/-- What a `utcoffset()`/`dst()` method returned. -/
inductive OffRet where
  | none
  | delta (d : Delta)
  /-- An object of another type, named as `type(x).__name__` prints it. -/
  | other (ty : String)
  deriving Repr, DecidableEq, Inhabited

/-- What a `tzname()` method returned. -/
inductive NameRet where
  | none
  | str (s : String)
  | other (ty : String)
  deriving Repr, DecidableEq, Inhabited

/-- The methods of the `tzinfo` subclasses in play. The argument is the
`datetime` the method is called for, or `none` for a call from `time`. -/
structure TzEnv where
  utcoffset : Nat → Option DT → Py OffRet
  dst : Nat → Option DT → Py OffRet
  tzname : Nat → Option DT → Py NameRet
  repr : Nat → String

/-- `mytz is ottz`, with `None is None`. -/
def sameTz : Option Tz → Option Tz → Bool
  | none, none => true
  | some a, some b => a.oid == b.oid
  | _, _ => false

/-- `timedelta` equality on `utcoffset()` results (`None == None`). -/
def offEq : Option Delta → Option Delta → Bool
  | none, none => true
  | some a, some b => a == b
  | _, _ => false

/-! ### Formatting helpers -/

/-- `'%0*d' % (w, n)` as a `String`. -/
def fmt0 (w : Nat) (n : Int) : String := String.ofList (padInt w n)

/-- `'%d' % n`. -/
def fmtD (n : Int) : String := String.ofList (showInt n)

/-- `repr(s)` for a `str`, for ASCII text (quote choice and backslash escapes of
`unicode_repr`, Objects/unicodeobject.c). Non-ASCII characters are passed through;
the differential test only feeds ASCII names. -/
def strRepr (s : String) : String :=
  let cs := s.toList
  let q := if cs.contains '\'' && !cs.contains '"' then '"' else '\''
  let hex (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  let esc (c : Char) : List Char :=
    if c = q ∨ c = '\\' then ['\\', c]
    else if c = '\t' then ['\\', 't']
    else if c = '\n' then ['\\', 'n']
    else if c = '\r' then ['\\', 'r']
    else if c.toNat < 32 ∨ c.toNat = 127 then ['\\', 'x', hex (c.toNat / 16), hex (c.toNat % 16)]
    else [c]
  String.ofList ([q] ++ cs.flatMap esc ++ [q])

/-! ### `timezone` -/

/-- `timezone._name_from_offset`, _pydatetime.py:2557-2574. -/
def nameFromOffset (delta : Delta) : String :=
  let t := delta.toUs
  if t = 0 then "UTC"
  else
    let sign := if t < 0 then "-" else "+"
    let a := t.natAbs
    let hours := a / 3600000000
    let rest := a % 3600000000
    let minutes := rest / 60000000
    let rest := rest % 60000000
    let seconds := rest / 1000000
    let microseconds := rest % 1000000
    let base := s!"UTC{sign}{fmt0 2 hours}:{fmt0 2 minutes}"
    if microseconds ≠ 0 then base ++ s!":{fmt0 2 seconds}.{fmt0 6 microseconds}"
    else if seconds ≠ 0 then base ++ s!":{fmt0 2 seconds}"
    else base

/-- `timezone.tzname`/`__str__`, _pydatetime.py:2521-2536. -/
def timezoneStrPy (offset : Delta) (name : Option String) : String :=
  match name with
  | none => nameFromOffset offset
  | some n => n

/-- `timezone_str`, _datetimemodule.c:4432-4476. `delta_negative` of an offset
inside ±24h cannot fail, and `C divmod` is on non-negative seconds. -/
def timezoneStrC (oid : Nat) (offset : Delta) (name : Option String) : String :=
  match name with
  | some n => n
  | none =>
    if oid = 0 ∨ (offset.days = 0 ∧ offset.seconds = 0 ∧ offset.us = 0) then "UTC"
    else
      let neg := offset.days < 0
      let sign := if neg then "-" else "+"
      let off : Delta := if neg then
          match newDeltaNormC (-offset.days) (-offset.seconds) (-offset.us) with
          | .ok t => t
          | .error _ => offset
        else offset
      let microseconds := off.us
      let seconds := off.seconds
      let minutes := seconds / 60
      let seconds := seconds % 60
      let hours := minutes / 60
      let minutes := minutes % 60
      let base := s!"UTC{sign}{fmt0 2 hours}:{fmt0 2 minutes}"
      if microseconds ≠ 0 then base ++ s!":{fmt0 2 seconds}.{fmt0 6 microseconds}"
      else if seconds ≠ 0 then base ++ s!":{fmt0 2 seconds}"
      else base

/-- `timezone.__repr__`, _pydatetime.py:2501-2519, and `timezone_repr`,
_datetimemodule.c:4413-4429. -/
def timezoneRepr (oid : Nat) (offset : Delta) (name : Option String) : String :=
  if oid = 0 then "datetime.timezone.utc"
  else match name with
    | none => s!"datetime.timezone({offset.repr})"
    | some n => s!"datetime.timezone({offset.repr}, {strRepr n})"

/-- `repr(tz)`. -/
def Tz.repr (env : TzEnv) (tz : Tz) : String :=
  match tz.kind with
  | .timezone offset name => timezoneRepr tz.oid offset name
  | .custom i => env.repr i

/-- `tz.utcoffset(dt)` without the check on the result: `timezone.utcoffset`,
_pydatetime.py:2524-2528 (C `timezone_utcoffset`, :4488-4495), or a subclass method.
The arguments here are always a `datetime` or `None`. -/
def tzUtcoffsetRaw (env : TzEnv) (tz : Tz) (arg : Option DT) : Py OffRet :=
  match tz.kind with
  | .timezone offset _ => .ok (.delta offset)
  | .custom i => env.utcoffset i arg

/-- `tz.dst(dt)`: `timezone.dst`, _pydatetime.py:2538-2542 (C `timezone_dst`,
:4498-4504), or a subclass method. -/
def tzDstRaw (env : TzEnv) (tz : Tz) (arg : Option DT) : Py OffRet :=
  match tz.kind with
  | .timezone _ _ => .ok .none
  | .custom i => env.dst i arg

/-- `tz.tzname(dt)` in Python. -/
def tzTznameRawPy (env : TzEnv) (tz : Tz) (arg : Option DT) : Py NameRet :=
  match tz.kind with
  | .timezone offset name => .ok (.str (timezoneStrPy offset name))
  | .custom i => env.tzname i arg

/-- `tz.tzname(dt)` in C: `timezone_tzname`, :4479-4485. -/
def tzTznameRawC (env : TzEnv) (tz : Tz) (arg : Option DT) : Py NameRet :=
  match tz.kind with
  | .timezone offset name => .ok (.str (timezoneStrC tz.oid offset name))
  | .custom i => env.tzname i arg

/-- `_check_utc_offset(name, offset)`, _pydatetime.py:566-576. -/
def checkUtcOffset (name : String) : OffRet → Py (Option Delta)
  | .none => .ok none
  | .other ty => .error (.typeError s!"tzinfo.{name}() must return None or timedelta, not '{ty}'")
  | .delta o =>
    if ¬(-86400000000 < o.toUs ∧ o.toUs < 86400000000) then
      .error (.valueError "~offset must be a timedelta strictly between -timedelta(hours=24) and timedelta(hours=24)")
    else .ok (some o)

/-- The result check of `call_tzinfo_method`, _datetimemodule.c:1525-1560. -/
def callTzinfoCheckC (name : String) : OffRet → Py (Option Delta)
  | .none => .ok none
  | .other ty => .error (.typeError s!"tzinfo.{name}() must return None or timedelta, not '{ty}'")
  | .delta o =>
    if (o.days = -1 ∧ o.seconds = 0 ∧ o.us < 1) ∨ o.days < -1 ∨ o.days ≥ 1 then
      .error (.valueError "~offset must be a timedelta strictly between -timedelta(hours=24) and timedelta(hours=24)")
    else .ok (some o)

/-- `_check_tzname(name)`, _pydatetime.py:555-558. -/
def checkTzname : NameRet → Py (Option String)
  | .none => .ok none
  | .str s => .ok (some s)
  | .other ty => .error (.typeError s!"tzinfo.tzname() must return None or string, not '{ty}'")

/-- The result check of `call_tzname`, _datetimemodule.c:1597-1620. -/
def callTznameCheckC : NameRet → Py (Option String)
  | .none => .ok none
  | .str s => .ok (some s)
  | .other ty => .error (.typeError s!"tzinfo.tzname() must return None or a string, not '{ty}'")

/-- `datetime.utcoffset()`, _pydatetime.py:2234-2241. -/
def DT.utcoffsetPy (env : TzEnv) (dt : DT) : Py (Option Delta) :=
  match dt.tz with
  | none => .ok none
  | some tz => do checkUtcOffset "utcoffset" (← tzUtcoffsetRaw env tz (some dt))

/-- `call_utcoffset(tzinfo, dt)` (:1571-1574) for `datetime_utcoffset`, :6216-6219. -/
def DT.utcoffsetC (env : TzEnv) (dt : DT) : Py (Option Delta) :=
  match dt.tz with
  | none => .ok none
  | some tz => do callTzinfoCheckC "utcoffset" (← tzUtcoffsetRaw env tz (some dt))

/-- `datetime.dst()`, _pydatetime.py:2256-2269. -/
def DT.dstPy (env : TzEnv) (dt : DT) : Py (Option Delta) :=
  match dt.tz with
  | none => .ok none
  | some tz => do checkUtcOffset "dst" (← tzDstRaw env tz (some dt))

/-- `call_dst` (:1585-1588) for `datetime_dst`, :6222-6225. -/
def DT.dstC (env : TzEnv) (dt : DT) : Py (Option Delta) :=
  match dt.tz with
  | none => .ok none
  | some tz => do callTzinfoCheckC "dst" (← tzDstRaw env tz (some dt))

/-- `datetime.tzname()`, _pydatetime.py:2243-2254. -/
def DT.tznamePy (env : TzEnv) (dt : DT) : Py (Option String) :=
  match dt.tz with
  | none => .ok none
  | some tz => do checkTzname (← tzTznameRawPy env tz (some dt))

/-- `call_tzname` for `datetime_tzname`, :6228-6231. -/
def DT.tznameC (env : TzEnv) (dt : DT) : Py (Option String) :=
  match dt.tz with
  | none => .ok none
  | some tz => do callTznameCheckC (← tzTznameRawC env tz (some dt))

/-- `time.utcoffset()`, _pydatetime.py:1695-1702 (the tzinfo gets `None`). -/
def TM.utcoffsetPy (env : TzEnv) (t : TM) : Py (Option Delta) :=
  match t.tz with
  | none => .ok none
  | some tz => do checkUtcOffset "utcoffset" (← tzUtcoffsetRaw env tz none)

/-- `time_utcoffset`, :4830-4833. -/
def TM.utcoffsetC (env : TzEnv) (t : TM) : Py (Option Delta) :=
  match t.tz with
  | none => .ok none
  | some tz => do callTzinfoCheckC "utcoffset" (← tzUtcoffsetRaw env tz none)

/-- `time.dst()`, _pydatetime.py:1717-1730. -/
def TM.dstPy (env : TzEnv) (t : TM) : Py (Option Delta) :=
  match t.tz with
  | none => .ok none
  | some tz => do checkUtcOffset "dst" (← tzDstRaw env tz none)

/-- `time_dst`, :4836-4839. -/
def TM.dstC (env : TzEnv) (t : TM) : Py (Option Delta) :=
  match t.tz with
  | none => .ok none
  | some tz => do callTzinfoCheckC "dst" (← tzDstRaw env tz none)

/-- `time.tzname()`, _pydatetime.py:1704-1715. -/
def TM.tznamePy (env : TzEnv) (t : TM) : Py (Option String) :=
  match t.tz with
  | none => .ok none
  | some tz => do checkTzname (← tzTznameRawPy env tz none)

/-- `time_tzname`, :4842-4845. -/
def TM.tznameC (env : TzEnv) (t : TM) : Py (Option String) :=
  match t.tz with
  | none => .ok none
  | some tz => do callTznameCheckC (← tzTznameRawC env tz none)

/-- `tzinfo.tzname`, `.utcoffset`, `.dst` of the abstract base class,
_pydatetime.py:1325-1339: the exception. -/
def tzinfoBasePy (meth : String) : PyExc :=
  .named "NotImplementedError" s!"tzinfo subclass must override {meth}()"

/-- `tzinfo_nogo`, _datetimemodule.c:4143-4149, for `tzinfo_tzname`,
`tzinfo_utcoffset` and `tzinfo_dst`. -/
def tzinfoNogoC (meth : String) : PyExc :=
  .named "NotImplementedError" s!"a tzinfo subclass must implement {meth}()"

end PyLean.Datetime
