import PyLean.Datetime.Ctor

/-!
Smaller pieces of `timedelta` and `timezone`: the C `str`/`repr`, `timezone`
construction, equality, hash and pickle arguments, `tzinfo.__reduce__`, and the
POSIX-time helpers that are pure once `time.localtime` is a parameter.
-/

namespace PyLean.Datetime

open PyLean

namespace Delta

/-- `delta_str`, _datetimemodule.c:2992-3018. -/
def strC (t : Delta) : String :=
  let us := t.us
  let minutes := t.seconds / 60
  let seconds := t.seconds % 60
  let hours := minutes / 60
  let minutes := minutes % 60
  let days := t.days
  let plural := if days = 1 ∨ days = -1 then "" else "s"
  if days ≠ 0 then
    if us ≠ 0 then
      s!"{fmtD days} day{plural}, {fmtD hours}:{fmt0 2 minutes}:{fmt0 2 seconds}.{fmt0 6 us}"
    else s!"{fmtD days} day{plural}, {fmtD hours}:{fmt0 2 minutes}:{fmt0 2 seconds}"
  else if us ≠ 0 then s!"{fmtD hours}:{fmt0 2 minutes}:{fmt0 2 seconds}.{fmt0 6 us}"
  else s!"{fmtD hours}:{fmt0 2 minutes}:{fmt0 2 seconds}"

/-- `delta_repr`, _datetimemodule.c:2943-2989. -/
def reprC (t : Delta) : String :=
  let args := if t.days ≠ 0 then s!"days={fmtD t.days}" else ""
  let sep := if t.days ≠ 0 then ", " else ""
  let (args, sep) := if t.seconds ≠ 0 then (s!"{args}{sep}seconds={fmtD t.seconds}", ", ") else (args, sep)
  let args := if t.us ≠ 0 then s!"{args}{sep}microseconds={fmtD t.us}" else args
  let args := if args.isEmpty then "0" else args
  s!"datetime.timedelta({args})"

/-- `timedelta.__reduce__`, Py:962-963, and `delta_reduce`, :3056-3060: the
constructor arguments. -/
def reduceArgs (t : Delta) : List Int := t.getstate

end Delta

/-- The `name` argument of `timezone(offset, name)`. -/
inductive TzName where
  | omitted
  | str (s : String)
  | other
  deriving Repr, DecidableEq, Inhabited

/-- `timezone.__new__`, Py:2462-2475, through `timezone._create`, Py:2481-2485:
`oid` is the identity of the new object. -/
def timezoneNewPy (oid : Nat) (offset : Delta) (name : TzName) : Py Tz :=
  match name with
  | .omitted =>
    if !offset.bool then .ok tzUTC
    else match timezonePy offset with
      | .ok _ => .ok ⟨oid, .timezone offset none⟩
      | .error e => .error e
  | .other => .error (.typeError "name must be a string")
  | .str s =>
    match timezonePy offset with
    | .ok _ => .ok ⟨oid, .timezone offset (some s)⟩
    | .error e => .error e

/-- `look_up_timezone`, :4603-4609: `timezone.utc` when `offset` is `utc_timezone`'s offset
object (the static `zero_delta`) and there is no name, else `NULL` (`none`). A zero
`timedelta` of the base class is that object (`new_delta_ex` hands out `zero_delta`,
`NewDeltaEx`), so a zero value stands for it here; a zero subclass instance reaches
`create_timezone` only with a name (`new_timezone` returns `timezone.utc` first for every
false offset without one), where the test fails either way. -/
def lookUpTimezoneC (offset : Delta) (name : Option String) : Option Tz :=
  if offset = ⟨0, 0, 0⟩ ∧ name = none then some tzUTC else none

/-- `create_timezone`, :1431-1453: the `look_up_timezone` singleton, else a new
`timezone` holding `offset` and `name` (allocation failure aside). -/
def createTimezoneC (oid : Nat) (offset : Delta) (name : Option String) : Tz :=
  match lookUpTimezoneC offset name with
  | some tz => tz
  | none => ⟨oid, .timezone offset name⟩

/-- `timezone_new_impl`, :4363-4367, and `new_timezone`, :1459-1479: `timezone.utc` for a
false offset without a name (:1465-1467), the range check with its `ValueError`
(:1468-1475), then `create_timezone` (:1478). The clinic wrapper checks `name` first;
`offset` is a `timedelta` in this signature. -/
def timezoneNewC (oid : Nat) (offset : Delta) (name : TzName) : Py Tz :=
  match name with
  | .other => .error (.typeError "~timezone() argument 'name' must be str")
  | .omitted =>
    if !offset.bool then .ok tzUTC
    else match newTimezoneC offset with
      | .ok _ => .ok (createTimezoneC oid offset none)
      | .error e => .error e
  | .str s =>
    if (offset.days = -1 ∧ offset.seconds = 0 ∧ offset.us < 1) ∨ offset.days < -1 ∨ offset.days ≥ 1 then
      .error (.valueError "~offset must be a timedelta strictly between -timedelta(hours=24) and timedelta(hours=24)")
    else .ok (createTimezoneC oid offset (some s))

/-- `timezone.__eq__`, Py:2493-2496: offsets compare, names do not. -/
def timezoneEqPy (a b : Delta) : Bool := a.richPy .eq b

/-- `timezone_richcompare`, :4379-4389: `none` is `NotImplemented`. -/
def timezoneRichC (op : CmpOp) (a b : Delta) : Option Bool :=
  if op = .eq ∨ op = .ne then some (a.richC op b) else none

/-- `timezone.__hash__`, Py:2498-2499, and `timezone_hash`, :4392-4396. -/
def timezoneHashKey (offset : Delta) : HashKey := offset.hashKey

/-- `tzinfo.__reduce__`, Py:1370-1376, and `tzinfo_reduce`, :4257-4283: the
constructor arguments (from `__getinitargs__` if there is one) and the state. -/
def tzinfoReduce {α σ : Type} (getinitargs : Option (Unit → Py (List α))) (state : Py σ) :
    Py (List α × σ) := do
  let args ← match getinitargs with
    | some f => f ()
    | none => pure []
  return (args, ← state)

/-- `isinstance(dt, datetime) or dt is None` for an argument of a `timezone` method:
Py:2469-2487 and `_timezone_check_argument`, :4403-4410. `ok` says the argument
is acceptable. -/
def timezoneCheckArg (ok : Bool) (meth : String) : Py Unit :=
  if ok then .ok () else .error (.typeError s!"~{meth}() argument must be a datetime instance or None")

/-- `timezone.__init_subclass__`, Py:2477-2478. -/
def timezoneInitSubclass : Py Unit :=
  .error (.typeError "type 'datetime.timezone' is not an acceptable base type")

/-! ### POSIX seconds -/

/-- `utc_to_seconds`, :5571-5585: `ord` here is `ymd_to_ord`. -/
def utcToSecondsC (y m d hh mi s : Int) : Py Int :=
  if y < MINYEAR ∨ y > MAXYEAR then .error (.valueError s!"year must be in 1..9999, not {y}")
  else .ok (((ymdToOrdC y m d * 24 + hh) * 60 + mi) * 60 + s)

/-- `datetime._mktime`, Py:2029-2061, over the local-time function. `loc u` is
`(datetime(*time.localtime(u)[:6]) - epoch) // timedelta(0, 1)`, `t` is
`(self - epoch) // timedelta(0, 1)`. -/
def mktimePy (loc : Int → Py Int) (t fold : Int) : Py Int := do
  let maxFoldSeconds : Int := 24 * 3600
  let a := (← loc t) - t
  let u1 := t - a
  let t1 ← loc u1
  let foldDelta := if fold = 0 then -maxFoldSeconds else maxFoldSeconds
  let (early, b) ← if t1 = t then do
      let u2 := u1 + foldDelta
      let b := (← loc u2) - u2
      pure (decide (a = b), b)
    else pure (false, t1 - u1)
  if early = true then return u1
  let u2 := t - b
  let t2 ← loc u2
  if t2 = t then return u2
  if t1 = t then return u1
  -- `(max, min)[self.fold](u1, u2)`
  return if fold = 0 then max u1 u2 else min u1 u2

/-- `local_to_seconds`, :7033-7077, over `local` (:5588-5607), here `loc`; `t` is
`utc_to_seconds` of the fields. -/
def localToSecondsC (loc : Int → Py Int) (t fold : Int) : Py Int := do
  let maxFoldSeconds : Int := 24 * 3600
  let lt ← loc t
  let a := lt - t
  let u1 := t - a
  let t1 ← loc u1
  let (early, b) ← if t1 = t then do
      let u2 := if fold ≠ 0 then u1 + maxFoldSeconds else u1 - maxFoldSeconds
      let lt ← loc u2
      let b := lt - u2
      pure (decide (a = b), b)
    else pure (false, t1 - u1)
  if early = true then return u1
  let u2 := t - b
  let t2 ← loc u2
  if t2 = t then return u2
  if t1 = t then return u1
  return if fold ≠ 0 then min u1 u2 else max u1 u2

end PyLean.Datetime
