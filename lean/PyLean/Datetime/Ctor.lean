import PyLean.Datetime.Objects

/-!
The constructors `date(...)`, `time(...)`, `datetime(...)` on their full argument
domain: int fields, the bytes/str pickle state, and the arguments that are rejected.
`Lib/_pydatetime.py` and `Modules/_datetimemodule.c` (3.14.7).
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

/-- `PyArg_ParseTuple` format `i`: first the int conversion, then the C `int` range. -/
def parseI : Arg → Py Int
  | .int n =>
    if fitsCInt n then .ok n else .error (.overflowError "~signed integer is out of range")
  | _ => .error (.typeError "~an integer is required")

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

/-- `date.__new__`, _pydatetime.py:982-1012. -/
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

/-- `date_new`, _datetimemodule.c:3233-3277. `MONTH_IS_SANE` is `1..12`. -/
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
  | none =>
    let missing : PyExc := .typeError "~function missing required argument"
    match args with
    | [] => .error missing
    | [a] => do let _ ← parseI a; throw missing
    | [a, b] => do let _ ← parseI a; let _ ← parseI b; throw missing
    | a :: b :: c :: _ => do
      let y ← parseI a
      let m ← parseI b
      let d ← parseI c
      checkDate y m d

/-! ### `tzinfo` argument -/

/-- `_check_tzinfo_arg(tz)`, _pydatetime.py:589-594. -/
def checkTzinfoArgPy : Arg → Py (Option Tz)
  | .none_ => .ok none
  | .tz t => .ok (some t)
  | _ => .error (.typeError "~tzinfo argument must be None or of a tzinfo subclass")

/-- `check_tzinfo_subclass`, _datetimemodule.c:1481-1490. -/
def checkTzinfoSubclassC : Arg → Py (Option Tz)
  | .none_ => .ok none
  | .tz t => .ok (some t)
  | _ => .error (.typeError "~tzinfo argument must be None or of a tzinfo subclass")

/-- The `tzinfo` check of `__setstate`, Py:1722-1723 and :2365-2366, and of
`time_from_pickle`/`datetime_from_pickle`. -/
def stateTz : Arg → Py (Option Tz)
  | .none_ => .ok none
  | .tz t => .ok (some t)
  | _ => .error (.typeError "bad tzinfo state arg")

/-! ### `time` -/

/-- `time.__new__`, _pydatetime.py:1411-1448. -/
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

/-- `time_new`, _datetimemodule.c:4653-4706, for positional arguments and `fold`. -/
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
  | none => do
    let h ← match args with | a :: _ => parseI a | [] => pure 0
    let mi ← match args with | _ :: a :: _ => parseI a | _ => pure 0
    let s ← match args with | _ :: _ :: a :: _ => parseI a | _ => pure 0
    let u ← match args with | _ :: _ :: _ :: a :: _ => parseI a | _ => pure 0
    let tzi := args.getD 4 .none_
    let _ ← checkTime h mi s u
    checkFold fold
    let t ← checkTzinfoSubclassC tzi
    return ⟨h, mi, s, u, fold, t⟩

/-! ### `datetime` -/

/-- `datetime.__new__`, _pydatetime.py:1755-1788. -/
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

/-- `datetime_new`, _datetimemodule.c:5378-5435, for positional arguments and `fold`. -/
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
  | none => do
    let missing : PyExc := .typeError "~function missing required argument"
    let y ← match args with | a :: _ => parseI a | [] => throw missing
    let m ← match args with | _ :: a :: _ => parseI a | _ => throw missing
    let d ← match args with | _ :: _ :: a :: _ => parseI a | _ => throw missing
    let h ← if args.length > 3 then parseI (args.getD 3 .none_) else pure 0
    let mi ← if args.length > 4 then parseI (args.getD 4 .none_) else pure 0
    let s ← if args.length > 5 then parseI (args.getD 5 .none_) else pure 0
    let u ← if args.length > 6 then parseI (args.getD 6 .none_) else pure 0
    let tzi := args.getD 7 .none_
    let _ ← checkDate y m d
    let _ ← checkTime h mi s u
    checkFold fold
    let t ← checkTzinfoSubclassC tzi
    return ⟨y, m, d, h, mi, s, u, fold, t⟩

end PyLean.Datetime
