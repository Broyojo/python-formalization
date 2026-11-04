import PyLean.Datetime.CmpProps
import PyLean.Datetime.Strftime
import PyLean.Datetime.Ctor

/-!
Twin disagreements in the object layer: the `strftime` format scan, `astimezone`
against a `tzinfo` with an out-of-range `utcoffset`, and the pickle form of `time()`.
-/

namespace PyLean.Datetime

open PyLean

/-- `strftime` format preprocessing: the two implementations hand the same format to
`time.strftime` for every format. -/
def StrftimeTwins : Prop :=
  ∀ (env : TzEnv) (obj : StrfObj) (format : List Char) (tt : TimeTuple) (gyear : Int) (norm : Bool),
    env.Valid → SameOutcome (wrapStrftimePy env obj format tt gyear norm) (wrapStrftimeC env obj format tt gyear norm)

/-- `date(2020, 1, 1).strftime('abc%:')`: Python drops the trailing `%:` (the loop's
`if i < n` has no `else`, _pydatetime.py:248-263), C copies it. -/
theorem strftimeTwins_refuted : ¬StrftimeTwins := by
  intro h
  have h1 := h emptyEnv .date ['a', 'b', 'c', '%', ':'] [2020] 0 false emptyEnv_valid
  have e1 : wrapStrftimePy emptyEnv .date ['a', 'b', 'c', '%', ':'] [2020] 0 false = .ok ['a', 'b', 'c'] := by
    decide
  have e2 : wrapStrftimeC emptyEnv .date ['a', 'b', 'c', '%', ':'] [2020] 0 false =
      .ok ['a', 'b', 'c', '%', ':'] := by
    decide
  rw [e1, e2] at h1
  simp [SameOutcome] at h1

/-- `astimezone`: the twins agree for every `tzinfo` and every valid `datetime`. -/
def AstimezoneTwins : Prop :=
  ∀ (env : TzEnv) (self : DT) (tz : Tz), env.Valid → self.Valid → tz.Ok →
    SameOutcome (dtAstimezonePy env self tz) (dtAstimezoneC env self tz)

/-- A `tzinfo` whose `utcoffset` is one day: out of range, but a valid `timedelta`. -/
def oneDayEnv : TzEnv :=
  ⟨fun _ _ => .ok (.delta ⟨1, 0, 0⟩), fun _ _ => .ok .none, fun _ _ => .ok .none, fun _ => ""⟩

theorem oneDayEnv_valid : oneDayEnv.Valid := by
  constructor
  · intro i a d h
    simp only [oneDayEnv, Except.ok.injEq, OffRet.delta.injEq] at h
    subst h
    simp [Delta.Valid, MAX_DELTA_DAYS]
  · intro i a d h
    simp [oneDayEnv] at h

/-- `datetime(2020, 1, 2, 12, tzinfo=T).astimezone(timezone.utc)` with `T.utcoffset`
returning `timedelta(1)`: `_pydatetime` subtracts it unchecked (`mytz.utcoffset(self)`,
Py:2099), C goes through `call_utcoffset` and raises `ValueError`. -/
theorem astimezoneTwins_refuted : ¬AstimezoneTwins := by
  intro h
  let self : DT := ⟨2020, 1, 2, 12, 0, 0, 0, 0, some ⟨1, .custom 0⟩⟩
  have hv : self.Valid := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, Or.inl rfl, trivial⟩
  have htz : tzUTC.Ok := by simp [Tz.Ok, tzUTC, Delta.Valid, MAX_DELTA_DAYS, Delta.toUs]
  have h1 := h oneDayEnv self tzUTC oneDayEnv_valid hv htz
  have e1 : Py.isOk (dtAstimezonePy oneDayEnv self tzUTC) = true := by decide
  have e2 : Py.isOk (dtAstimezoneC oneDayEnv self tzUTC) = false := by decide
  cases hp : dtAstimezonePy oneDayEnv self tzUTC with
  | error e => rw [hp] at e1; cases e1
  | ok a =>
    cases hc : dtAstimezoneC oneDayEnv self tzUTC with
    | ok c => rw [hc] at e2; cases e2
    | error e => rw [hp, hc] at h1; exact h1

/-- The pickle form `time(state, tzinfo)` takes the same second argument in both twins. -/
def TimePickleCtorTwins : Prop :=
  ∀ (state : List Nat) (tzarg : Arg),
    SameOutcome (timeNewPy (.bytes state) tzarg (.int 0) (.int 0) .none_ (.int 0)) (timeNewC [.bytes state, tzarg] (.int 0))

/-- `time(b'\x01\x00\x00\x00\x00\x00', 0)`: Python's `minute or None` turns the falsy
second argument into `None` (Py:1434), C raises `TypeError('bad tzinfo state arg')`. -/
theorem timePickleCtorTwins_refuted : ¬TimePickleCtorTwins := by
  intro h
  have h1 := h [1, 0, 0, 0, 0, 0] (.int 0)
  have e1 : Py.isOk (timeNewPy (.bytes [1, 0, 0, 0, 0, 0]) (.int 0) (.int 0) (.int 0) .none_ (.int 0)) = true := by decide
  have e2 : Py.isOk (timeNewC [.bytes [1, 0, 0, 0, 0, 0], .int 0] (.int 0)) = false := by decide
  cases hp : timeNewPy (.bytes [1, 0, 0, 0, 0, 0]) (.int 0) (.int 0) (.int 0) .none_ (.int 0) with
  | error e => rw [hp] at e1; cases e1
  | ok a =>
    cases hc : timeNewC [.bytes [1, 0, 0, 0, 0, 0], .int 0] (.int 0) with
    | ok c => rw [hc] at e2; cases e2
    | error e => rw [hp, hc] at h1; exact h1

end PyLean.Datetime
