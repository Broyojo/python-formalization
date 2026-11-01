import PyLean.Datetime.CmpProps
import PyLean.Datetime.Strftime
import PyLean.Datetime.IsoC
import PyLean.Datetime.Misc

/-!
Statements that are registered but not settled yet. Each is a real proposition about the
model; `lean/PyLean/Datetime.lean` carries the note on what its proof needs.
-/

namespace PyLean.Datetime

open PyLean

/-- `time.fromisoformat(t.isoformat())` returns `t`, naive or with any offset in range,
in both twins. `tz` is the offset in microseconds. -/
def TimeIsoformatRoundtrip : Prop :=
  ∀ t : TimeV, (0 ≤ t.h ∧ t.h ≤ 23) → (0 ≤ t.mi ∧ t.mi ≤ 59) → (0 ≤ t.s ∧ t.s ≤ 59) →
    (0 ≤ t.us ∧ t.us ≤ 999999) → (∀ o, t.tz = some o → -86400000000 < o ∧ o < 86400000000) →
    timeFromIsoPy (formatTime t.h t.mi t.s t.us .auto ++ formatOffset t.tz) = .ok t ∧
    timeFromIsoC (formatTime t.h t.mi t.s t.us .auto ++ formatOffset t.tz) = .ok t

/-- `datetime.fromisoformat(d.isoformat())` returns `d`, in both twins. -/
def DatetimeIsoformatRoundtrip : Prop :=
  ∀ (y m d : Int) (t : TimeV), ValidDate y m d → (0 ≤ t.h ∧ t.h ≤ 23) → (0 ≤ t.mi ∧ t.mi ≤ 59) →
    (0 ≤ t.s ∧ t.s ≤ 59) → (0 ≤ t.us ∧ t.us ≤ 999999) →
    (∀ o, t.tz = some o → -86400000000 < o ∧ o < 86400000000) →
    datetimeFromIsoPy (dateIsoformat y m d ++ ['T'] ++ formatTime t.h t.mi t.s t.us .auto ++ formatOffset t.tz) =
      .ok ⟨y, m, d, t⟩ ∧
    datetimeFromIsoC (dateIsoformat y m d ++ ['T'] ++ formatTime t.h t.mi t.s t.us .auto ++ formatOffset t.tz) =
      .ok ⟨y, m, d, t⟩

/-- Equal `datetime` objects hash alike: `a == b` implies `hash(a) == hash(b)`. -/
def DatetimeEqHash : Prop :=
  ∀ (env : TzEnv) (a b : DT), env.Valid → a.Valid → b.Valid → dtRichC env .eq a b = .ok true →
    dtHashKeyC env a = dtHashKeyC env b

/-- Every `%:` in the format starts `%:z`. -/
def NoBareColon : List Char → Prop
  | [] => True
  | '%' :: ':' :: 'z' :: r => NoBareColon r
  | '%' :: ':' :: _ => False
  | '%' :: _ :: r => NoBareColon r
  | _ :: r => NoBareColon r

/-- The refuted `StrftimeTwins` narrowed: without a bare `%:`, and when the century
normalization (which writes `%F` differently in the two twins and leaves the output
equal) is not in play, both twins hand the same format to `time.strftime`. -/
def StrftimeTwinsNoBareColon : Prop :=
  ∀ (env : TzEnv) (obj : StrfObj) (format : List Char) (tt : TimeTuple) (gyear : Int) (norm : Bool),
    env.Valid → NoBareColon format → (norm = false ∨ 1000 ≤ tt.getD 0 0) →
    SameOutcome (wrapStrftimePy env obj format tt gyear norm) (wrapStrftimeC env obj format tt gyear norm)

/-- The refuted `TimeCompareTwins` narrowed: with whole-minute offsets the twins agree. -/
def TimeCompareWholeMinutes : Prop :=
  ∀ (env : TzEnv) (op : CmpOp) (a b : TM), env.Valid → a.Valid → b.Valid →
    (∀ o, a.utcoffsetPy env = .ok (some o) → o.toUs % 60000000 = 0) →
    (∀ o, b.utcoffsetPy env = .ok (some o) → o.toUs % 60000000 = 0) →
    SameOutcome (tmRichPy env op a b) (tmRichC env op a b)

/-- The refuted `AstimezoneTwins` narrowed: to a `timezone`, from a `tzinfo` whose
`utcoffset(self)` returns `None` or a `timedelta` in range, the twins agree. Object
identity: a `tzinfo` with the target's id is the target. -/
def AstimezoneToTimezone : Prop :=
  ∀ (env : TzEnv) (self : DT) (tz : Tz) (off : Delta) (name : Option String) (mytz : Tz),
    env.Valid → self.Valid → tz.Ok → tz.kind = .timezone off name → self.tz = some mytz →
    (mytz.oid = tz.oid → mytz = tz) →
    (∃ o, tzUtcoffsetRaw env mytz (some self) = .ok (.delta o) ∧ -86400000000 < o.toUs ∧ o.toUs < 86400000000) →
    SameOutcome (dtAstimezonePy env self tz) (dtAstimezoneC env self tz)

/-- `tzinfo.fromutc`: for a subclass whose `dst()` is one constant `timedelta` in range, the
twins agree. `fold` of the intermediate result cannot then change `dst()`. -/
def TzinfoFromutcFixedDst : Prop :=
  ∀ (env : TzEnv) (tz : Nat) (i : Nat) (dt : DT) (d : Delta),
    env.Valid → dt.Valid → dt.tz = some ⟨tz, .custom i⟩ →
    (∀ a, env.dst i a = .ok (.delta d)) → -86400000000 < d.toUs → d.toUs < 86400000000 →
    SameOutcome (tzinfoFromutcPy env tz dt) (tzinfoFromutcC env tz dt)

/-- `timedelta.__str__` and `__repr__`: the twins print the same text. -/
def TimedeltaStrRepr : Prop :=
  ∀ t : Delta, t.Valid → t.str = t.strC ∧ t.repr = t.reprC

end PyLean.Datetime
