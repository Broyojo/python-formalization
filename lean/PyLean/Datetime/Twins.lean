import PyLean.Datetime.Ctor
import PyLean.Datetime.Strftime
import PyLean.Datetime.Misc
import PyLean.Binary64.Float
import PyLean.LongObj.LongFloat

/-!
C twins that the first layer of the model shared with Python, now mirrored from their own
source, and the argument domains the first layer left out: an explicit `None` against an
omitted argument, a `datetime` operand of `date - x`, the class of a `repr`, the float
operands of `timedelta * x` and `timedelta / x`, and the clock of `date.fromtimestamp`.
`Lib/_pydatetime.py` (Py) and `Modules/_datetimemodule.c` (C) of CPython 3.15.2.
-/

namespace PyLean.Datetime

open PyLean

/-! ### Calendar and field checks in C -/

/-- `_check_time_fields(hour, minute, second, microsecond, fold)`, _pydatetime.py:591-606,
after the four `_index` calls. -/
def checkTimeFieldsPy (h m s us fold : Int) : Py (Int × Int × Int × Int × Int) := do
  let (h, m, s, us) ← checkTime h m s us
  checkFold fold
  return (h, m, s, us, fold)

/-- C `build_struct_time`'s argument tuple, :2091-2109, from the C helpers `weekday`
(:578-581) and `days_before_month` (:451-461), here with `ymd_to_ord`'s C division. -/
def buildStructTimeArgsC (y m d hh mm ss dstflag : Int) : TimeTuple :=
  [y, m, d, hh, mm, ss, (ymdToOrdC y m d + 6).tmod 7, daysBeforeMonth y m + d, dstflag]

/-! ### Float operands of `*` and `/` -/

/-- `float.as_integer_ratio`, the method both twins call (`other.as_integer_ratio()` in
Python, `get_float_as_integer_ratio` in C, :2312-2336, which calls the same method). -/
def asRatio (x : Binary64.F64) : Py (Int × Int) := Binary64.float_as_integer_ratio x

/-- `timedelta * float`, _pydatetime.py:865-868. -/
def Delta.mulFloatPy (a : Delta) (x : Binary64.F64) : Py Delta := do
  let usec := a.toUs
  let (n, d) ← asRatio x
  usToDeltaPy (← divideAndRound (usec * n) d)

/-- `multiply_truedivide_timedelta_float(delta, x, 0)`, :2339-2368: the microseconds times
`ratio[0]`, divided to nearest by `ratio[1]`. -/
def Delta.mulFloatC (a : Delta) (x : Binary64.F64) : Py Delta := do
  let pyusIn := a.toUs
  let ratio ← asRatio x
  let temp := pyusIn * ratio.1
  usToDeltaC (← divideNearestC temp ratio.2)

/-- `timedelta / float`, _pydatetime.py:894-896. -/
def Delta.truedivFloatPy (a : Delta) (x : Binary64.F64) : Py Delta := do
  let usec := a.toUs
  let (n, d) ← asRatio x
  usToDeltaPy (← divideAndRound (d * usec) n)

/-- `multiply_truedivide_timedelta_float(delta, x, 1)`, :2339-2368: the microseconds times
`ratio[1]`, divided to nearest by `ratio[0]`. -/
def Delta.truedivFloatC (a : Delta) (x : Binary64.F64) : Py Delta := do
  let pyusIn := a.toUs
  let ratio ← asRatio x
  let temp := pyusIn * ratio.2
  usToDeltaC (← divideNearestC temp ratio.1)

/-- `timedelta / timedelta`, _pydatetime.py:890-891: `usec / other._to_microseconds()`, the
int true division `long_true_divide` (Objects/longobject.c:4607-4861). -/
def Delta.truedivDeltaPy (a b : Delta) : Py LongObj.Cplx.Dbl :=
  let usec := a.toUs
  LongObj.trueDivide (.ofInt usec) (.ofInt b.toUs)

/-- `truedivide_timedelta_timedelta`, :2414-2434: `PyNumber_TrueDivide` of the two
microsecond counts, which is `long_true_divide`. -/
def Delta.truedivDeltaC (a b : Delta) : Py LongObj.Cplx.Dbl :=
  LongObj.trueDivide (.ofInt a.toUs) (.ofInt b.toUs)

/-! ### `date - x` with a `datetime` operand -/

/-- The right operand of `date - x`: a timedelta, a date, a datetime (given by its date
fields; its time fields play no part), or another object. -/
inductive SubOperand where
  | delta (t : Delta)
  | date (y m d : Int)
  | datetime (y m d : Int)
  | other
  deriving Repr, DecidableEq

/-- What `date - x` gives: a date, a timedelta, or `NotImplemented` (`none`), after which
the binary operator raises `TypeError` (no reflected method applies: `datetime` has no
`__rsub__` of its own for a `date` left operand, and the C slot is the same function). -/
inductive SubResult where
  | date (y m d : Int)
  | delta (t : Delta)
  deriving Repr, DecidableEq

/-- `date.__sub__`, _pydatetime.py:1249-1257: `isinstance(other, date)` is true for a
`datetime`. -/
def dateSubPy (y m d : Int) : SubOperand → Option (Py SubResult)
  | .delta t => some (do
      let (y, m, d) ← dateSubDeltaPy y m d t
      return .date y m d)
  | .date y2 m2 d2 => some (.delta <$> dateSubDatePy (y, m, d) (y2, m2, d2))
  | .datetime y2 m2 d2 => some (.delta <$> dateSubDatePy (y, m, d) (y2, m2, d2))
  | .other => none

/-- `date_subtract`, :3588-3616: `NotImplemented` first when either operand is a
`datetime` (:3591-3592), then date - date and date - timedelta. -/
def dateSubC (y m d : Int) : SubOperand → Option (Py SubResult)
  | .datetime _ _ _ => none
  | .date y2 m2 d2 => some (.delta <$> dateSubDateC (y, m, d) (y2, m2, d2))
  | .delta t => some (do
      let (y, m, d) ← dateSubDeltaC y m d t
      return .date y m d)
  | .other => none

/-- The binary operator `date - x` from the slot result: `NotImplemented` becomes the
`TypeError` of `binary_op1` (Objects/abstract.c). -/
def binarySub (r : Option (Py SubResult)) : Py SubResult :=
  match r with
  | some v => v
  | none => .error (.typeError "~unsupported operand type(s) for -")

/-! ### `date.replace` with omitted and `None` arguments -/

/-- `if year is None: year = self._year`, _pydatetime.py:1186-1191: an omitted argument and
`None` both keep the field. -/
def replKeep (old : Int) : Option Arg → Arg
  | none => .int old
  | some .none_ => .int old
  | some a => a

/-- The clinic wrapper's handling of one `replace` argument: omitted keeps the field, a given
one goes through `PyLong_AsInt`. -/
def replConv (old : Int) : Option Arg → Py Int
  | none => .ok old
  | some a => parseI a

/-- `date.replace(year=..., month=..., day=...)`, _pydatetime.py:1184-1192: `none` is an
omitted argument, `some a` the object passed, which may be `None`. Omitted and `None` both
keep the field; the result is `type(self)(year, month, day)`, i.e. `date.__new__`. -/
def dateReplacePy (y m d : Int) (ny nm nd : Option Arg) : Py (Int × Int × Int) :=
  dateNewPy (replKeep y ny) (replKeep m nm) (replKeep d nd)

/-- `datetime_date_replace`, clinic/_datetimemodule.c.h:587-658: an omitted argument keeps
`GET_YEAR(self)` etc.; a given one goes through `PyLong_AsInt` (so `None` is a `TypeError`);
then `datetime_date_replace_impl`, :3956-3961, `new_date_subclass_ex` (:1191-1206) and
`new_date_ex` (:1168-1187), which runs `check_date_args`. -/
def dateReplaceC (y m d : Int) (ny nm nd : Option Arg) : Py (Int × Int × Int) := do
  let year ← replConv y ny
  let month ← replConv m nm
  let day ← replConv d nd
  checkDateArgsC year month day
  return (year, month, day)

/-! ### `repr` and the class -/

/-- The class of a `date` for `repr`: the base class, or a Python subclass with its
`__module__`, `__qualname__` and `__name__`. For a heap type `tp_name` is `__name__`
(Objects/typeobject.c, `type_new_set_names`); classes are modelled by these names, a
metaclass that overrides them is out of scope. -/
inductive ReprCls where
  | base
  | sub (module qualname name : String)
  deriving Repr, DecidableEq

/-- `self.__class__.__module__`: `_pydatetime` sets `__name__ = "datetime"` (:6), so its
classes report module `datetime`. -/
def ReprCls.module : ReprCls → String
  | .base => "datetime"
  | .sub m _ _ => m

/-- `self.__class__.__qualname__`. -/
def ReprCls.qualname : ReprCls → String
  | .base => "date"
  | .sub _ q _ => q

/-- `Py_TYPE(self)->tp_name`: `"datetime.date"` for the static type, `__name__` for a heap
subclass. -/
def ReprCls.tpName : ReprCls → String
  | .base => "datetime.date"
  | .sub _ _ n => n

/-- `date.__repr__`, _pydatetime.py:1096-1107:
`"%s%s(%d, %d, %d)" % (_get_class_module(self), self.__class__.__qualname__, ...)`. -/
def dateReprClsPy (c : ReprCls) (y m d : Int) : String :=
  s!"{getClassModule c.module}{c.qualname}({fmtD y}, {fmtD m}, {fmtD d})"

/-- `date_repr`, :3618-3624: `"%s(%d, %d, %d)"` with `Py_TYPE(self)->tp_name`. -/
def dateReprClsC (c : ReprCls) (y m d : Int) : String :=
  s!"{c.tpName}({fmtD y}, {fmtD m}, {fmtD d})"

/-! ### `isoformat` text in C -/

/-- C `date_isoformat`, :3627-3633: `PyUnicode_FromFormat("%04d-%02d-%02d", ...)`. -/
def dateIsoformatC (y m d : Int) : List Char :=
  (fmt0 4 y ++ "-" ++ fmt0 2 m ++ "-" ++ fmt0 2 d).toList

/-- The `timespec` argument: a `str` (Lean's `String` has no lone surrogates), a `str` that
contains a lone surrogate code point (its other characters do not matter to either twin), or
another object, hashable or not. -/
inductive SpecArg where
  | str (s : String)
  | surrogateStr
  | other (hashable : Bool)
  deriving Repr, DecidableEq

/-- `_format_time(..., timespec)`'s spec handling, _pydatetime.py:175-184, on any object:
a `str` that is not a key (one with a NUL or a surrogate included) and a non-`str` compare
unequal to every key, so `specs[timespec]` raises `KeyError` (turned into `ValueError`), or
`TypeError` from hashing an unhashable object. -/
def parseTimespecArgPy : SpecArg → Py TimeSpec
  | .str s => parseTimespec s
  | .surrogateStr => .error (.valueError "Unknown timespec value")
  | .other true => .error (.valueError "Unknown timespec value")
  | .other false => .error (.typeError "~cannot use an unhashable object as a dict key")

/-- The `specs` table of `datetime_time_isoformat_impl`, :4907-4913, in order. -/
def specsC : List (String × TimeSpec) :=
  [("hours", .hours), ("minutes", .minutes), ("seconds", .seconds), ("milliseconds", .milliseconds),
   ("microseconds", .microseconds)]

/-- The clinic `str` converter of `timespec` (clinic/_datetimemodule.c.h:956-968 for
`time.isoformat`, :1815-1827 for `datetime.isoformat`): a non-`str` is a `TypeError`
(`PyUnicode_Check`, :956-959); `PyUnicode_AsUTF8AndSize` fails with `UnicodeEncodeError`
on a lone surrogate (:961-964); a NUL makes `strlen` differ from the length, `ValueError:
embedded null character` (:965-968). Then the search of `specs` in
`datetime_time_isoformat_impl`, :4916-4941. -/
def parseTimespecArgC : SpecArg → Py TimeSpec
  | .str s =>
    if s.toList.contains '\x00' then .error (.valueError "embedded null character")
    -- `timespec == NULL || strcmp(timespec, "auto") == 0`, then the loop over `specs`
    else if s = "auto" then .ok .auto
    else match specsC.find? (·.1 = s) with
      | some (_, sp) => .ok sp
      | none => .error (.valueError "Unknown timespec value")
  | .surrogateStr =>
    .error (.named "UnicodeEncodeError" "~'utf-8' codec can't encode character: surrogates not allowed")
  | .other _ => .error (.typeError "~isoformat() argument 'timespec' must be str")

/-- The time part of C `datetime_time_isoformat_impl`, :4900-4952 (and of
`datetime_datetime_isoformat_impl`): `specs[given_spec][1]` formatted with the four fields,
`us / 1000` (C division, `us >= 0`) for milliseconds. -/
def formatTimeC (hh mm ss us : Int) (spec : TimeSpec) : List Char :=
  let r : Nat × Int := match spec with
    | .auto => if us = 0 then (2, us) else (4, us)
    | .hours => (0, us)
    | .minutes => (1, us)
    | .seconds => (2, us)
    | .milliseconds => (3, us.tdiv 1000)
    | .microseconds => (4, us)
  let (given, us) := r
  match given with
  | 0 => (fmt0 2 hh).toList
  | 1 => (fmt0 2 hh ++ ":" ++ fmt0 2 mm).toList
  | 2 => (fmt0 2 hh ++ ":" ++ fmt0 2 mm ++ ":" ++ fmt0 2 ss).toList
  | 3 => (fmt0 2 hh ++ ":" ++ fmt0 2 mm ++ ":" ++ fmt0 2 ss ++ "." ++ fmt0 3 us).toList
  | _ => (fmt0 2 hh ++ ":" ++ fmt0 2 mm ++ ":" ++ fmt0 2 ss ++ "." ++ fmt0 6 us).toList

/-! ### `date.fromtimestamp` -/

/-- The operating system as `date.fromtimestamp` sees it. `otherTimeT` is
`_PyTime_ObjectToTime_t` on a non-int, non-`None` object (the float path), `now` is
`time(NULL)`, `localtime` is `_PyTime_localtime` as `(tm_year + 1900, tm_mon + 1, tm_mday)`. -/
structure Clock where
  otherTimeT : Arg → Py Int
  now : Py Int
  localtime : Int → Py (Int × Int × Int)

/-- `_PyTime_ObjectToTime_t(obj, ROUND_FLOOR)`, Python/pytime.c:484-520: an int through
`_PyLong_AsTime_t` (:205-224, a 64-bit `time_t`); otherwise `PyFloat_AsDouble`, whose
`TypeError` names the type for `None` and the other non-numbers. -/
def objectToTimeT (k : Clock) : Arg → Py Int
  | .int n => if -2 ^ 63 ≤ n ∧ n < 2 ^ 63 then .ok n
      else .error (.overflowError "timestamp out of range for platform time_t")
  | .other => k.otherTimeT .other
  | _ => .error (.typeError "~must be real number")

/-- `time.localtime(t)`, Modules/timemodule.c `time_localtime` and `parse_time_t_args`:
`None` means now. -/
def timeLocaltime (k : Clock) (t : Arg) : Py (Int × Int × Int) := do
  let whent ← (match t with
    | .none_ => k.now
    | a => objectToTimeT k a)
  k.localtime whent

/-- `date.fromtimestamp(t)`, _pydatetime.py:1036-1041, for `cls` the base class. -/
def dateFromtimestampPy (k : Clock) (t : Arg) : Py (Int × Int × Int) :=
  if t = .none_ then .error (.typeError "'NoneType' object cannot be interpreted as an integer")
  else do
    let (y, m, d) ← timeLocaltime k t
    checkDate y m d

/-- `date_fromtimestamp`, :3290-3305: the timestamp conversion, `_PyTime_localtime`, then
`new_date_subclass_ex` with the base class, i.e. `new_date_ex` and `check_date_args`. -/
def dateFromtimestampC (k : Clock) (t : Arg) : Py (Int × Int × Int) := do
  let tt ← objectToTimeT k t
  let (y, m, d) ← k.localtime tt
  checkDateArgsC y m d
  return (y, m, d)

/-! ### `date.__format__` -/

/-- The `fmt` argument of `__format__`: a `str` or another object. -/
inductive FmtArg where
  | str (cs : List Char)
  | other
  deriving Repr, DecidableEq

/-- `date.__format__(fmt)`, _pydatetime.py:1132-1137: the `isinstance(fmt, str)` check, then
`self.strftime(fmt)` for a nonempty format and `str(self)` otherwise. `str` and `strftime`
are the results of those method calls (a subclass may override them). -/
def dateFormatPy {α : Type} (fmt : FmtArg) (str : Py String) (strftime : List Char → Py α) :
    Py (Sum String α) :=
  match fmt with
  | .other => .error (.typeError "~must be str")
  | .str cs => if cs.length ≠ 0 then Sum.inr <$> strftime cs else Sum.inl <$> str

/-- `datetime_date___format__`, clinic/_datetimemodule.c.h:492-506 (the `unicode`
converter), then `datetime_date___format___impl`, :3691-3699: `PyObject_Str(self)` for a
zero-length format, otherwise the `strftime` method. -/
def dateFormatC {α : Type} (fmt : FmtArg) (str : Py String) (strftime : List Char → Py α) :
    Py (Sum String α) :=
  match fmt with
  | .other => .error (.typeError "~__format__() argument must be str")
  | .str cs => if cs.length = 0 then Sum.inl <$> str else Sum.inr <$> strftime cs

end PyLean.Datetime
