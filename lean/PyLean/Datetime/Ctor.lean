import PyLean.Datetime.Objects

/-!
The constructors `date(...)`, `time(...)`, `datetime(...)` on their full argument
domain: int fields, the bytes/str pickle state, and the arguments that are rejected.
`Lib/_pydatetime.py` and `Modules/_datetimemodule.c` (3.15.2).

In C the pickle check stays in `date_new`, `time_new` and `datetime_new`; everything else
goes through the generated wrappers `datetime_date`, `datetime_time` and `datetime_datetime`
(`Modules/clinic/_datetimemodule.c.h`) to the `_impl` functions. Those wrappers count the
arguments first (`_PyArg_UnpackKeywords`, `Python/getargs.c:2519-2695`) and convert them
afterwards, so a missing argument now wins over a bad one before it.
-/

namespace PyLean.Datetime

open PyLean

/-- A constructor argument. `none_` is `None`, or an omitted parameter whose
default is `None`; a `str` is its list of code points. -/
inductive Arg where
  | none_
  | int (n : Int)
  | bytes (b : List Nat)
  | str (cs : List Nat)
  | tz (t : Tz)
  | other
  deriving Repr, DecidableEq, Inhabited

/-- `operator.index(x)` (`_index`, _pydatetime.py:12). -/
def pyIndex : Arg → Py Int
  | .int n => .ok n
  | _ => .error (.typeError "~object cannot be interpreted as an integer")

/-- The clinic `int` converter, `PyLong_AsInt`, `Objects/longobject.c:690-702`: first
`__index__`, whose `TypeError` names the object's type, then the C `int` range. -/
def parseI : Arg → Py Int
  | .int n => asCInt n
  | _ => .error (.typeError "~object cannot be interpreted as an integer")

theorem parseI_int (n : Int) (h : fitsCInt n) : parseI (.int n) = .ok n := by
  unfold fitsCInt at h
  simp only [parseI, asCInt]
  rw [if_pos (by omega)]

/-- The arity checks of `_PyArg_UnpackKeywords`, `Python/getargs.c:2572-2603`, for a parser
with `maxargs >= 2` and `minpos < maxpos` or `maxpos = maxargs`. `nkw` is the number of
keywords given. -/
def clinicArity (fname : String) (maxpos maxargs nargs nkw : Nat) : Option PyExc :=
  if nargs + nkw > maxargs then
    some (.typeError s!"{fname}() takes at most {maxargs} {if nargs = 0 then "keyword " else ""}arguments ({nargs + nkw} given)")
  else if nargs > maxpos then
    some (.typeError s!"{fname}() takes at most {maxpos} positional arguments ({nargs} given)")
  else none

/-- The missing-argument error of `_PyArg_UnpackKeywords`, `Python/getargs.c:2652-2660`, for
the first absent parameter, at index `i` of `names`. -/
def clinicMissing (fname : String) (names : List String) (i : Nat) : PyExc :=
  .typeError s!"{fname}() missing required argument '{names.getD i ""}' (pos {i + 1})"

/-- Whether `x` is falsy (`minute or None`). -/
def Arg.falsy : Arg → Bool
  | .none_ => true
  | .int n => n == 0
  | .bytes b => b.isEmpty
  | .str s => s.isEmpty
  | _ => false

/-- A state string encoded to bytes: `str.encode('latin1')` with its error. -/
def latin1State (kind : String) (cs : List Nat) : Py (List Nat) :=
  if cs.any (· > 255) then
    .error (.valueError s!"Failed to encode latin1 string when unpickling a {kind} object. pickle.load(data, encoding='latin1') is assumed.")
  else .ok cs

/-- The bytes-or-str pickle state, its code units, and the encoder. -/
def stateOf (kind : String) : Arg → Option (List Nat × Py (List Nat))
  | .bytes b => some (b, .ok b)
  | .str cs => some (cs, latin1State kind cs)
  | _ => none

/-! ### `date` -/

/-- `date.__new__`, _pydatetime.py:1001-1031. -/
def dateNewPy (year month day : Arg) : Py (Int × Int × Int) :=
  let pickled : Option (Py (List Nat)) := match stateOf "date" year with
    | some (u, enc) =>
      if month = .none_ ∧ u.length = 4 ∧ 1 ≤ u.getD 2 0 ∧ u.getD 2 0 ≤ 12 then some enc else none
    | none => none
  match pickled with
  | some enc => do
    let st ← enc
    match dateSetstate st with
    | some v => return v
    | none => throw .modelFuel
  | none => do
    let y ← pyIndex year
    let m ← pyIndex month
    let d ← pyIndex day
    checkDate y m d

/-- `datetime_date_impl`, _datetimemodule.c:3284-3288: `new_date_ex`, which checks the fields
with `check_date_args`. -/
def datetimeDateImplC (y m d : Int) : Py (Int × Int × Int) := checkDateC y m d

/-- The clinic wrapper `datetime_date`, clinic/_datetimemodule.c.h:131-183: arity, then
`year`, `month`, `day` in turn, then the impl. -/
def datetimeDateClinicC (args : List Arg) : Py (Int × Int × Int) := do
  if let some e := clinicArity "date" 3 3 args.length 0 then throw e
  match args with
  | a :: b :: c :: _ =>
    let y ← parseI a
    let m ← parseI b
    let d ← parseI c
    datetimeDateImplC y m d
  | _ => throw (clinicMissing "date" ["year", "month", "day"] args.length)

/-- `date_new`, _datetimemodule.c:3235-3270. `MONTH_IS_SANE` is `1..12`. -/
def dateNewC (args : List Arg) : Py (Int × Int × Int) :=
  let pickled : Option (Py (List Nat)) := match args with
    | [state] => match stateOf "date" state with
      | some (u, enc) =>
        if u.length = 4 ∧ 1 ≤ u.getD 2 0 ∧ u.getD 2 0 ≤ 12 then some enc else none
      | none => none
    | _ => none
  match pickled with
  | some enc => do
    let st ← enc
    match dateSetstate st with
    | some v => return v
    | none => throw .modelFuel
  | none => datetimeDateClinicC args

/-! ### `tzinfo` argument -/

/-- `_check_tzinfo_arg(tz)`, _pydatetime.py:608-613. -/
def checkTzinfoArgPy : Arg → Py (Option Tz)
  | .none_ => .ok none
  | .tz t => .ok (some t)
  | _ => .error (.typeError "~tzinfo argument must be None or of a tzinfo subclass")

/-- `check_tzinfo_subclass`, _datetimemodule.c:1489-1498. -/
def checkTzinfoSubclassC : Arg → Py (Option Tz)
  | .none_ => .ok none
  | .tz t => .ok (some t)
  | _ => .error (.typeError "~tzinfo argument must be None or of a tzinfo subclass")

/-- The `tzinfo` check of `__setstate`, Py:1767-1768 and :2418-2419, and of
`time_from_pickle`/`datetime_from_pickle`. -/
def stateTz : Arg → Py (Option Tz)
  | .none_ => .ok none
  | .tz t => .ok (some t)
  | _ => .error (.typeError "bad tzinfo state arg")

/-! ### `time` -/

/-- `time.__new__`, _pydatetime.py:1436-1473. -/
def timeNewPy (hour minute second us tz : Arg) (fold : Int) : Py TM :=
  let pickled : Option (Py (List Nat)) := match stateOf "time" hour with
    | some (u, enc) => if u.length = 6 ∧ u.getD 0 0 % 128 < 24 then some enc else none
    | none => none
  match pickled with
  | some enc => do
    let st ← enc
    let tzi := if minute.falsy then Arg.none_ else minute
    let t ← stateTz tzi
    match tmSetstate t st with
    | some v => return v
    | none => throw .modelFuel
  | none => do
    let h ← pyIndex hour
    let mi ← pyIndex minute
    let s ← pyIndex second
    let u ← pyIndex us
    let _ ← checkTime h mi s u
    checkFold fold
    let t ← checkTzinfoArgPy tz
    return ⟨h, mi, s, u, fold, t⟩

/-- `datetime_time_impl`, _datetimemodule.c:4770-4775: `new_time_ex2`, :1318-1345. -/
def datetimeTimeImplC (h mi s u : Int) (tzi : Arg) (fold : Int) : Py TM := do
  let _ ← checkTime h mi s u
  checkFold fold
  let t ← checkTzinfoSubclassC tzi
  return ⟨h, mi, s, u, fold, t⟩

/-- The clinic wrapper `datetime_time`, clinic/_datetimemodule.c.h:746-871, for positional
arguments and the keyword `fold` (always passed here, so the arity check counts it). -/
def datetimeTimeClinicC (args : List Arg) (fold : Int) : Py TM := do
  if let some e := clinicArity "time" 5 6 args.length 1 then throw e
  let h ← match args with | a :: _ => parseI a | [] => pure 0
  let mi ← match args with | _ :: a :: _ => parseI a | _ => pure 0
  let s ← match args with | _ :: _ :: a :: _ => parseI a | _ => pure 0
  let u ← match args with | _ :: _ :: _ :: a :: _ => parseI a | _ => pure 0
  let tzi := args.getD 4 .none_
  let f ← parseI (.int fold)
  datetimeTimeImplC h mi s u tzi f

/-- `time_new`, _datetimemodule.c:4710-4749, for positional arguments and `fold`. -/
def timeNewC (args : List Arg) (fold : Int) : Py TM :=
  let pickled : Option (Py (List Nat) × Arg) := match args with
    | state :: rest =>
      if rest.length ≤ 1 then
        match stateOf "time" state with
        | some (u, enc) =>
          if u.length = 6 ∧ u.getD 0 0 % 128 < 24 then some (enc, rest.headD .none_) else none
        | none => none
      else none
    | [] => none
  match pickled with
  | some (enc, tzi) => do
    let st ← enc
    let t ← stateTz tzi
    match tmSetstate t st with
    | some v => return v
    | none => throw .modelFuel
  | none => datetimeTimeClinicC args fold

/-! ### `datetime` -/

/-- `datetime.__new__`, _pydatetime.py:1800-1833. -/
def datetimeNewPy (year month day hour minute second us tz : Arg) (fold : Int) : Py DT :=
  let pickled : Option (Py (List Nat)) := match stateOf "datetime" year with
    | some (u, enc) =>
      let m := u.getD 2 0 % 128
      if u.length = 10 ∧ 1 ≤ m ∧ m ≤ 12 then some enc else none
    | none => none
  match pickled with
  | some enc => do
    let st ← enc
    let t ← stateTz month
    match dtSetstate t st with
    | some v => return v
    | none => throw .modelFuel
  | none => do
    let y ← pyIndex year
    let m ← pyIndex month
    let d ← pyIndex day
    let _ ← checkDate y m d
    let h ← pyIndex hour
    let mi ← pyIndex minute
    let s ← pyIndex second
    let u ← pyIndex us
    let _ ← checkTime h mi s u
    checkFold fold
    let t ← checkTzinfoArgPy tz
    return ⟨y, m, d, h, mi, s, u, fold, t⟩

/-- `datetime_datetime_impl`, _datetimemodule.c:5550-5558: `new_datetime_ex2`, :1210-1240. -/
def datetimeDatetimeImplC (y m d h mi s u : Int) (tzi : Arg) (fold : Int) : Py DT := do
  let _ ← checkDate y m d
  let _ ← checkTime h mi s u
  checkFold fold
  let t ← checkTzinfoSubclassC tzi
  return ⟨y, m, d, h, mi, s, u, fold, t⟩

/-- The clinic wrapper `datetime_datetime`, clinic/_datetimemodule.c.h:1641-1771, for
positional arguments and the keyword `fold` (always passed here). -/
def datetimeDatetimeClinicC (args : List Arg) (fold : Int) : Py DT := do
  if let some e := clinicArity "datetime" 8 9 args.length 1 then throw e
  match args with
  | a :: b :: c :: rest =>
    let y ← parseI a
    let m ← parseI b
    let d ← parseI c
    let h ← match rest with | x :: _ => parseI x | [] => pure 0
    let mi ← match rest with | _ :: x :: _ => parseI x | _ => pure 0
    let s ← match rest with | _ :: _ :: x :: _ => parseI x | _ => pure 0
    let u ← match rest with | _ :: _ :: _ :: x :: _ => parseI x | _ => pure 0
    let tzi := rest.getD 4 .none_
    let f ← parseI (.int fold)
    datetimeDatetimeImplC y m d h mi s u tzi f
  | _ => throw (clinicMissing "datetime" ["year", "month", "day"] args.length)

/-- `datetime_new`, _datetimemodule.c:5487-5526, for positional arguments and `fold`. -/
def datetimeNewC (args : List Arg) (fold : Int) : Py DT :=
  let pickled : Option (Py (List Nat) × Arg) := match args with
    | state :: rest =>
      if rest.length ≤ 1 then
        match stateOf "datetime" state with
        | some (u, enc) =>
          let m := u.getD 2 0 % 128
          if u.length = 10 ∧ 1 ≤ m ∧ m ≤ 12 then some (enc, rest.headD .none_) else none
        | none => none
      else none
    | [] => none
  match pickled with
  | some (enc, tzi) => do
    let st ← enc
    let t ← stateTz tzi
    match dtSetstate t st with
    | some v => return v
    | none => throw .modelFuel
  | none => datetimeDatetimeClinicC args fold

/-! ### Calling the Python twins

The interpreter binds the arguments of `__new__` before the body runs. The text of its
`TypeError` is not part of `Lib/_pydatetime.py`, so it is compared by class only. -/

/-- The `TypeError` of a call that gives too many positional arguments or omits `year`. -/
def pyCallError : PyExc := .typeError "~__new__() got the wrong number of positional arguments"

/-- `date(*args)` in Python: `def __new__(cls, year, month=None, day=None)`. -/
def dateCallPy (args : List Arg) : Py (Int × Int × Int) :=
  if args.isEmpty ∨ args.length > 3 then .error pyCallError
  else dateNewPy (args.getD 0 .none_) (args.getD 1 .none_) (args.getD 2 .none_)

/-- `time(*args, fold=fold)` in Python: `def __new__(cls, hour=0, minute=0, second=0,
microsecond=0, tzinfo=None, *, fold=0)`. -/
def timeCallPy (args : List Arg) (fold : Int) : Py TM :=
  if args.length > 5 then .error pyCallError
  else timeNewPy (args.getD 0 (.int 0)) (args.getD 1 (.int 0)) (args.getD 2 (.int 0))
    (args.getD 3 (.int 0)) (args.getD 4 .none_) fold

/-- `datetime(*args, fold=fold)` in Python: `def __new__(cls, year, month=None, day=None,
hour=0, minute=0, second=0, microsecond=0, tzinfo=None, *, fold=0)`. -/
def datetimeCallPy (args : List Arg) (fold : Int) : Py DT :=
  if args.isEmpty ∨ args.length > 8 then .error pyCallError
  else datetimeNewPy (args.getD 0 .none_) (args.getD 1 .none_) (args.getD 2 .none_)
    (args.getD 3 (.int 0)) (args.getD 4 (.int 0)) (args.getD 5 (.int 0)) (args.getD 6 (.int 0))
    (args.getD 7 .none_) fold

end PyLean.Datetime
