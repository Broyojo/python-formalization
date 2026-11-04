import PyLean.Datetime.Twins
import PyLean.Datetime.Misc

/-!
Twin differences found by reading (review 50b4b958), each modelled on both sides:
`tzinfo.__reduce__`'s truth test, `datetime.isoformat`'s `sep`, `time.replace` and
`datetime.replace` on any argument, and `_mktime`/`local_to_seconds` over an abstract
`localtime` (with `_local_timezone`). `Lib/_pydatetime.py` and `Modules/_datetimemodule.c`,
3.15.2.
-/

namespace PyLean.Datetime

open PyLean

/-! ### `tzinfo.__reduce__` -/

/-- The object `getattr(self, '__getinitargs__', None)` found: `truth` is `bool(obj)` (its
`__bool__` or `__len__`, which may raise; a function or a bound method is always true, `None`
is false), `call` is `obj()` (which may raise; calling `None` or another non-callable is a
`TypeError`), returning the object `α`. -/
structure InitArgsObj (α : Type) where
  truth : Py Bool
  call : Py α

/-- The constructor arguments in the reduce tuple: the empty tuple `()` or the object
`__getinitargs__()` returned (any object; pickle checks it later). -/
inductive ReduceArgs (α : Type) where
  | empty
  | obj (a : α)
  deriving DecidableEq, Repr

/-- `tzinfo.__reduce__`, Py:1370-1376: `attr` is the lookup of `__getinitargs__` (`none`
when the attribute is missing; an exception other than `AttributeError` propagates), then
`if getinitargs:` tests its truth (:1372), calls it only when true, and then
`self.__getstate__()` (`state`). An attribute whose value is `None` is a present, false
object, so it gives `()`. -/
def tzinfoReducePy {α σ : Type} (attr : Py (Option (InitArgsObj α))) (state : Py σ) :
    Py (ReduceArgs α × σ) := do
  let g ← attr
  let args ← match g with
    | none => pure .empty
    | some o => do if (← o.truth) then ReduceArgs.obj <$> o.call else pure .empty
  return (args, ← state)

/-- `tzinfo_reduce`, :4256-4282: `PyObject_GetOptionalAttr` (:4261, `NULL` for a missing
attribute), and a found object is called whatever its truth (:4264-4266), so `None` is a
`TypeError`; then `_PyObject_GetState(self)` (:4275). -/
def tzinfoReduceC {α σ : Type} (attr : Py (Option (InitArgsObj α))) (state : Py σ) :
    Py (ReduceArgs α × σ) := do
  let g ← attr
  let args ← match g with
    | none => pure .empty
    | some o => ReduceArgs.obj <$> o.call
  return (args, ← state)

/-! ### `datetime.isoformat(sep)` -/

/-- `'%c' % sep` (`formatchar`, Objects/unicode_format.c:416-454) on any object, as a code
point: a `str` of length 1 is its character, another `str` a `TypeError`; anything else goes
through `PyLong_AsLongAndOverflow`, i.e. `__index__` (an int, a bool, an object with
`__index__`), and a `TypeError` there becomes the `%c` `TypeError` while another exception
propagates; a value outside `0..0x10FFFF` (an overflow of C `long` included) is
`OverflowError`. -/
def pctCharPy : Arg → Py Nat
  | .str cs =>
    match cs with
    | [c] => .ok c
    | _ => .error (.typeError "~%c requires an integer or a unicode character, not a string of length")
  | a =>
    match pyIndex a with
    | .ok n =>
      if 0 ≤ n ∧ n ≤ 0x10FFFF then .ok n.toNat
      else .error (.overflowError "~%c argument not in range(0x110000)")
    | .error e =>
      if e.className = "TypeError" then
        .error (.typeError "~%c requires an integer or a unicode character, not")
      else .error e

/-- The clinic converter of `sep` (`int(accept={str})`), clinic/_datetimemodule.c.h:1798-1811:
a `str` of length 1 is its character; another `str` and every other object is a `TypeError`. -/
def sepClinicC : Arg → Py Nat
  | .str [c] => .ok c
  | .str _ => .error (.typeError "~isoformat(): argument 'sep' must be a unicode character, not a string of length")
  | _ => .error (.typeError "~isoformat() argument 'sep' must be a unicode character")

/-- `datetime.isoformat(sep, timespec)`, Py:2174-2199, on any `sep`, as code points:
`"%04d-%02d-%02d%c" % (..., sep)` first (:2190), then `_format_time` and the offset. The
timespec is already parsed (`parseTimespecArgPy`). -/
def dtIsoformatArgPy (env : TzEnv) (dt : DT) (sep : Arg) (spec : TimeSpec) : Py (List Nat) := do
  let c ← pctCharPy sep
  let s := (dateIsoformat dt.y dt.m dt.d).map Char.toNat ++ [c] ++
    (formatTime dt.h dt.mi dt.s dt.us spec).map Char.toNat
  let off ← dt.utcoffsetPy env
  return s ++ (formatOffset (off.map Delta.toUs)).map Char.toNat

/-- `datetime_datetime_isoformat`, the clinic wrapper (`sep` converted first,
clinic/_datetimemodule.c.h:1798-1811), then `datetime_datetime_isoformat_impl`, :6450-6510. -/
def dtIsoformatArgC (env : TzEnv) (dt : DT) (sep : Arg) (spec : TimeSpec) : Py (List Nat) := do
  let c ← sepClinicC sep
  let s := (dateIsoformat dt.y dt.m dt.d).map Char.toNat ++ [c] ++
    (formatTime dt.h dt.mi dt.s dt.us spec).map Char.toNat
  let off ← dt.utcoffsetC env
  return s ++ (formatOffset (off.map Delta.toUs)).map Char.toNat

/-! ### `time.replace` and `datetime.replace` on any argument -/

/-- The `tzinfo` attribute as an argument object. -/
def tzArg : Option Tz → Arg
  | none => .none_
  | some z => .tz z

/-- `if tzinfo is True: tzinfo = self.tzinfo`: `none` is the default `True` (omitted, or
`True` passed). -/
def tzKeep (old : Option Tz) : Option Arg → Arg
  | none => tzArg old
  | some a => a

/-- `time.replace(hour, minute, second, microsecond, tzinfo, *, fold)`, Py:1732-1747: each
`None` or omitted field keeps the old value (:1735-1746), then
`type(self)(hour, minute, second, microsecond, tzinfo, fold=fold)` (:1747), i.e.
`time.__new__` with its pickle test, `_check_time_fields` and `_check_tzinfo_arg`. -/
def tmReplaceArgPy (t : TM) (h mi s us : Option Arg) (tz : Option Arg) (fold : Option Arg) : Py TM :=
  timeNewPy (replKeep t.h h) (replKeep t.mi mi) (replKeep t.s s) (replKeep t.us us) (tzKeep t.tz tz)
    (replKeep t.fold fold)

/-- `datetime_time_replace`, clinic/_datetimemodule.c.h:1089-1191: an omitted argument keeps
`TIME_GET_*(self)`, a given one goes through `PyLong_AsInt` (`None` is a `TypeError`) in the
order hour, minute, second, microsecond, fold (`tzinfo` is any object); then
`datetime_time_replace_impl`, :5171-5178, `new_time_subclass_fold_ex` (:1358-1373), for the
base class `new_time` and `new_time_ex2` (`check_time_args`, `check_tzinfo_subclass`). -/
def tmReplaceArgC (t : TM) (h mi s us : Option Arg) (tz : Option Arg) (fold : Option Arg) : Py TM := do
  let hh ← replConv t.h h
  let mm ← replConv t.mi mi
  let ss ← replConv t.s s
  let uu ← replConv t.us us
  let f ← replConv t.fold fold
  datetimeTimeImplC hh mm ss uu (tzKeep t.tz tz) f

/-- `datetime.replace(...)`, Py:2094-2117: as `time.replace`, then
`type(self)(year, month, day, hour, minute, second, microsecond, tzinfo, fold=fold)`. -/
def dtReplaceArgPy (dt : DT) (y m d h mi s us : Option Arg) (tz : Option Arg) (fold : Option Arg) :
    Py DT :=
  datetimeNewPy (replKeep dt.y y) (replKeep dt.m m) (replKeep dt.d d) (replKeep dt.h h)
    (replKeep dt.mi mi) (replKeep dt.s s) (replKeep dt.us us) (tzKeep dt.tz tz) (replKeep dt.fold fold)

/-- `datetime_datetime_replace`, clinic/_datetimemodule.c.h:1853-1985 (`int` converters for every field
and fold, `PyLong_AsInt`), then `datetime_datetime_replace_impl`, :6753-6762,
`new_datetime_subclass_fold_ex` (:1288-1305), for the base class `new_datetime_ex2`. -/
def dtReplaceArgC (dt : DT) (y m d h mi s us : Option Arg) (tz : Option Arg) (fold : Option Arg) :
    Py DT := do
  let yy ← replConv dt.y y
  let mo ← replConv dt.m m
  let dd ← replConv dt.d d
  let hh ← replConv dt.h h
  let mm ← replConv dt.mi mi
  let ss ← replConv dt.s s
  let uu ← replConv dt.us us
  let f ← replConv dt.fold fold
  datetimeDatetimeImplC yy mo dd hh mm ss uu (tzKeep dt.tz tz) f

/-! ### `_mktime` and `local_to_seconds` over `localtime` -/

/-- The first six fields of `localtime(t)`: year, month, day, hour, minute, second. -/
abbrev LocalTm := Int × Int × Int × Int × Int × Int

/-- `date(1970, 1, 1).toordinal() * 86400`, C `epoch` (:5567). -/
def epochC : Int := 719163 * 86400

/-- `time_t` is 64 bits. -/
def fitsTimeT (t : Int) : Prop := -2 ^ 63 ≤ t ∧ t < 2 ^ 63

instance (t : Int) : Decidable (fitsTimeT t) := by unfold fitsTimeT; infer_instance

/-- `_time.localtime(u)[:6]` for an int `u`: the conversion to `time_t` (OverflowError outside
it), then the C library's `localtime`, `lt`, an arbitrary function that may fail (`OSError`).
A leap-second-aware zone (`right/...`) makes `lt` return second 60. -/
def timeLocaltimePy (lt : Int → Py LocalTm) (u : Int) : Py LocalTm :=
  if fitsTimeT u then lt u else .error (.overflowError "timestamp out of range for platform time_t")

/-- `local(u)` inside `datetime._mktime`, Py:2034-2036:
`(datetime(y, m, d, hh, mm, ss) - epoch) // timedelta(0, 1)`. The constructor checks the
fields (`newDT`: `_check_date_fields`, `_check_time_fields`), so second 60 is a `ValueError`;
the difference of two valid naive datetimes, floor-divided by one second, is the whole
seconds `(ordinal - 719163) * 86400 + hh * 3600 + mm * 60 + ss`. -/
def localPy (lt : Int → Py LocalTm) (u : Int) : Py Int := do
  let (y, m, d, hh, mm, ss) ← timeLocaltimePy lt u
  let dt ← newDT ⟨y, m, d, hh, mm, ss, 0, 0, none⟩
  return (toordinal dt.y dt.m dt.d - 719163) * 86400 + dt.h * 3600 + dt.mi * 60 + dt.s

/-- `local(u)`, :5588-5607: `u - epoch` to `time_t` (OverflowError if it does not fit),
`_PyTime_localtime`, then `utc_to_seconds` of the fields, which checks only the year
(:5575-5579): the other fields, second 60 included, are used as they are. -/
def localC (lt : Int → Py LocalTm) (u : Int) : Py Int := do
  let t := u - epochC
  if ¬ fitsTimeT t then throw (.overflowError "timestamp out of range for platform time_t")
  let (y, m, d, hh, mm, ss) ← lt t
  utcToSecondsC y m d hh mm ss

/-- `datetime._mktime()`, Py:2029-2061, for a naive datetime `self` and the C library's
`localtime`: `t = (self - epoch) // timedelta(0, 1)`. -/
def dtMktimePy (lt : Int → Py LocalTm) (self : DT) : Py Int :=
  mktimePy (localPy lt) ((toordinal self.y self.m self.d - 719163) * 86400 + self.h * 3600 +
    self.mi * 60 + self.s) self.fold

/-- `local_to_seconds(...) - epoch`, :7032-7077, for a datetime's fields, as `datetime_timestamp`
(:7083-7107) and `local_timezone_from_local` use it. -/
def dtLocalToSecondsC (lt : Int → Py LocalTm) (self : DT) : Py Int := do
  let t ← utcToSecondsC self.y self.m self.d self.h self.mi self.s
  let r ← localToSecondsC (localC lt) t self.fold
  return r - epochC

/-- `datetime._local_timezone()`, Py:2121-2135, the timestamp it picks for a naive `self`:
`_mktime()` for its fold and for the other fold (`self.replace(fold=1-self.fold)`), and in a
gap or fold (`ts2 != ts`) the other one when `(ts2 > ts) == self.fold` (:2124-2128); an aware
`self` uses `(self - _EPOCH) // timedelta(seconds=1)` (`utcSecs`). The `timezone` is then built
from `localtime(ts)`'s `tm_gmtoff` and `tm_zone` (:2131-2135), the same call in both twins. -/
def localTimezoneTsPy (lt : Int → Py LocalTm) (self : DT) (utcSecs : Int) : Py Int := do
  if self.tz.isNone then
    let ts ← dtMktimePy lt self
    let ts2 ← dtMktimePy lt { self with fold := 1 - self.fold }
    if ts2 ≠ ts then
      if decide (ts2 > ts) = decide (self.fold = 1) then return ts2
    return ts
  else return utcSecs

/-- `local_timezone_from_local`, :6873-6903 (for a naive `self`: `local_to_seconds` with fold
and `!fold`, the gap test of :6897), or `local_timezone`, :6831-6870, for an aware one. -/
def localTimezoneTsC (lt : Int → Py LocalTm) (self : DT) (utcSecs : Int) : Py Int := do
  if self.tz.isNone then
    let s1 ← dtLocalToSecondsC lt self
    let s2 ← dtLocalToSecondsC lt { self with fold := if self.fold ≠ 0 then 0 else 1 }
    if s2 ≠ s1 ∧ decide (s2 > s1) = decide (self.fold ≠ 0) then return s2
    return s1
  else return utcSecs

end PyLean.Datetime
