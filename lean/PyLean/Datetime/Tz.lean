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

/-- `timezone.utc`, _pydatetime.py:2521. -/
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

/-- `timezone._name_from_offset`, _pydatetime.py:2502-2519. -/
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

/-- `timezone.tzname`/`__str__`, _pydatetime.py:2466-2481. -/
def timezoneStrPy (offset : Delta) (name : Option String) : String :=
  match name with
  | none => nameFromOffset offset
  | some n => n

/-- `timezone_str`, _datetimemodule.c:4369-4413. `delta_negative` of an offset
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

/-- `timezone.__repr__`, _pydatetime.py:2446-2464, and `timezone_repr`,
_datetimemodule.c:4350-4366. -/
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
_pydatetime.py:2469-2473 (C `timezone_utcoffset`, :4425-4432), or a subclass method.
The arguments here are always a `datetime` or `None`. -/
def tzUtcoffsetRaw (env : TzEnv) (tz : Tz) (arg : Option DT) : Py OffRet :=
  match tz.kind with
  | .timezone offset _ => .ok (.delta offset)
  | .custom i => env.utcoffset i arg

/-- `tz.dst(dt)`: `timezone.dst`, _pydatetime.py:2483-2487 (C `timezone_dst`,
:4435-4441), or a subclass method. -/
def tzDstRaw (env : TzEnv) (tz : Tz) (arg : Option DT) : Py OffRet :=
  match tz.kind with
  | .timezone _ _ => .ok .none
  | .custom i => env.dst i arg

/-- `tz.tzname(dt)` in Python. -/
def tzTznameRawPy (env : TzEnv) (tz : Tz) (arg : Option DT) : Py NameRet :=
  match tz.kind with
  | .timezone offset name => .ok (.str (timezoneStrPy offset name))
  | .custom i => env.tzname i arg

/-- `tz.tzname(dt)` in C: `timezone_tzname`, :4416-4422. -/
def tzTznameRawC (env : TzEnv) (tz : Tz) (arg : Option DT) : Py NameRet :=
  match tz.kind with
  | .timezone offset name => .ok (.str (timezoneStrC tz.oid offset name))
  | .custom i => env.tzname i arg

/-- `_check_utc_offset(name, offset)`, _pydatetime.py:547-557. -/
def checkUtcOffset (name : String) : OffRet → Py (Option Delta)
  | .none => .ok none
  | .other ty => .error (.typeError s!"tzinfo.{name}() must return None or timedelta, not '{ty}'")
  | .delta o =>
    if ¬(-86400000000 < o.toUs ∧ o.toUs < 86400000000) then
      .error (.valueError "~offset must be a timedelta strictly between -timedelta(hours=24) and timedelta(hours=24)")
    else .ok (some o)

/-- The result check of `call_tzinfo_method`, _datetimemodule.c:1517-1552. -/
def callTzinfoCheckC (name : String) : OffRet → Py (Option Delta)
  | .none => .ok none
  | .other ty => .error (.typeError s!"tzinfo.{name}() must return None or timedelta, not '{ty}'")
  | .delta o =>
    if (o.days = -1 ∧ o.seconds = 0 ∧ o.us < 1) ∨ o.days < -1 ∨ o.days ≥ 1 then
      .error (.valueError "~offset must be a timedelta strictly between -timedelta(hours=24) and timedelta(hours=24)")
    else .ok (some o)

/-- `_check_tzname(name)`, _pydatetime.py:536-539. -/
def checkTzname : NameRet → Py (Option String)
  | .none => .ok none
  | .str s => .ok (some s)
  | .other ty => .error (.typeError s!"tzinfo.tzname() must return None or string, not '{ty}'")

/-- The result check of `call_tzname`, _datetimemodule.c:1589-1612. -/
def callTznameCheckC : NameRet → Py (Option String)
  | .none => .ok none
  | .str s => .ok (some s)
  | .other ty => .error (.typeError s!"tzinfo.tzname() must return None or a string, not '{ty}'")

/-- `datetime.utcoffset()`, _pydatetime.py:2181-2188. -/
def DT.utcoffsetPy (env : TzEnv) (dt : DT) : Py (Option Delta) :=
  match dt.tz with
  | none => .ok none
  | some tz => do checkUtcOffset "utcoffset" (← tzUtcoffsetRaw env tz (some dt))

/-- `call_utcoffset(tzinfo, dt)` (:1563-1566) for `datetime_utcoffset`, :6051-6054. -/
def DT.utcoffsetC (env : TzEnv) (dt : DT) : Py (Option Delta) :=
  match dt.tz with
  | none => .ok none
  | some tz => do callTzinfoCheckC "utcoffset" (← tzUtcoffsetRaw env tz (some dt))

/-- `datetime.dst()`, _pydatetime.py:2203-2216. -/
def DT.dstPy (env : TzEnv) (dt : DT) : Py (Option Delta) :=
  match dt.tz with
  | none => .ok none
  | some tz => do checkUtcOffset "dst" (← tzDstRaw env tz (some dt))

/-- `call_dst` (:1577-1580) for `datetime_dst`, :6057-6060. -/
def DT.dstC (env : TzEnv) (dt : DT) : Py (Option Delta) :=
  match dt.tz with
  | none => .ok none
  | some tz => do callTzinfoCheckC "dst" (← tzDstRaw env tz (some dt))

/-- `datetime.tzname()`, _pydatetime.py:2190-2201. -/
def DT.tznamePy (env : TzEnv) (dt : DT) : Py (Option String) :=
  match dt.tz with
  | none => .ok none
  | some tz => do checkTzname (← tzTznameRawPy env tz (some dt))

/-- `call_tzname` for `datetime_tzname`, :6063-6066. -/
def DT.tznameC (env : TzEnv) (dt : DT) : Py (Option String) :=
  match dt.tz with
  | none => .ok none
  | some tz => do callTznameCheckC (← tzTznameRawC env tz (some dt))

/-- `time.utcoffset()`, _pydatetime.py:1650-1657 (the tzinfo gets `None`). -/
def TM.utcoffsetPy (env : TzEnv) (t : TM) : Py (Option Delta) :=
  match t.tz with
  | none => .ok none
  | some tz => do checkUtcOffset "utcoffset" (← tzUtcoffsetRaw env tz none)

/-- `time_utcoffset`, :4749-4752. -/
def TM.utcoffsetC (env : TzEnv) (t : TM) : Py (Option Delta) :=
  match t.tz with
  | none => .ok none
  | some tz => do callTzinfoCheckC "utcoffset" (← tzUtcoffsetRaw env tz none)

/-- `time.dst()`, _pydatetime.py:1672-1685. -/
def TM.dstPy (env : TzEnv) (t : TM) : Py (Option Delta) :=
  match t.tz with
  | none => .ok none
  | some tz => do checkUtcOffset "dst" (← tzDstRaw env tz none)

/-- `time_dst`, :4755-4758. -/
def TM.dstC (env : TzEnv) (t : TM) : Py (Option Delta) :=
  match t.tz with
  | none => .ok none
  | some tz => do callTzinfoCheckC "dst" (← tzDstRaw env tz none)

/-- `time.tzname()`, _pydatetime.py:1659-1670. -/
def TM.tznamePy (env : TzEnv) (t : TM) : Py (Option String) :=
  match t.tz with
  | none => .ok none
  | some tz => do checkTzname (← tzTznameRawPy env tz none)

/-- `time_tzname`, :4761-4764. -/
def TM.tznameC (env : TzEnv) (t : TM) : Py (Option String) :=
  match t.tz with
  | none => .ok none
  | some tz => do callTznameCheckC (← tzTznameRawC env tz none)

/-- `tzinfo.tzname`, `.utcoffset`, `.dst` of the abstract base class,
_pydatetime.py:1300-1314: the exception. -/
def tzinfoBasePy (meth : String) : PyExc :=
  .named "NotImplementedError" s!"tzinfo subclass must override {meth}()"

/-- `tzinfo_nogo`, _datetimemodule.c:4084-4090, for `tzinfo_tzname`,
`tzinfo_utcoffset` and `tzinfo_dst`. -/
def tzinfoNogoC (meth : String) : PyExc :=
  .named "NotImplementedError" s!"a tzinfo subclass must implement {meth}()"

end PyLean.Datetime
