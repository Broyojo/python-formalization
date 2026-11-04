import PyLean.Datetime.LocalZoneProps
import PyLean.Datetime.SubclassCtor

/-!
`add_datetime_timedelta` (Modules/_datetimemodule.c:6241-6266), `datetime_utctimetuple`
(:7154-7191) and `datetime_datetime_astimezone_impl` (:6914-7004) over objects, CPython 3.15.2.

`add_datetime_timedelta` ends in `new_datetime_subclass_ex(..., Py_TYPE(date))`
(:6262-6265), which for a subclass is `cls(y, m, d, hh, mm, ss, us, tzinfo)` (through
`call_subclass_fold` with `fold = 0`, :1308-1314, :1254-1285) and returns whatever that call
returns. The callers then read the result as a `PyDateTime_DateTime` without checking its type:
`datetime_utctimetuple` reads `GET_YEAR(utcself)`..`DATE_GET_SECOND(utcself)` (:7182-7187),
`astimezone` reads `HASTZINFO(result)` (:6963) and writes `result->tzinfo` (:6983, :6996).

So a result is modelled as an object (`DtAny`): an instance of some `datetime` type, holding a
`DT`, or an object of an unrelated type. A C computation that reads or writes a datetime field
of the latter has no defined outcome; it is `none` in `Option (Py _)`. Classes are modelled by
identity (`DtType`): `datetime` itself (the fast path) or a subclass, given by what calling it
does. The receiver is a real instance (the method is bound), so its value is a `DT`.
-/

namespace PyLean.Datetime
open PyLean

/-- An object a Python call hands back to C. `dt ty v`: an instance of a `datetime` type
(`ty` its identity, `0` for `datetime` itself; `PyDateTime_Check` passes) whose struct holds `v`.
`other ty`: an object of any other type (`ty` its name), whose struct is not a
`PyDateTime_DateTime`. -/
inductive DtAny where
  | dt (ty : Nat) (v : DT)
  | other (ty : String)
  deriving DecidableEq, Repr

/-- A `datetime` type as `Py_TYPE(self)` or a classmethod's `type`: `datetime` itself (the fast
paths of the C helpers) or a subclass, by its identity `id` and what `cls(*args, fold=...)`
does (any object, or an exception). -/
inductive DtType where
  | base
  | sub (id : Nat) (call : SubCall DtAny)

/-- The identity of a type: `0` for `datetime`, `id + 1` for a subclass. -/
def DtType.tyId : DtType → Nat
  | .base => 0
  | .sub id _ => id + 1

/-- `HASTZINFO(dt) ? dt->tzinfo : Py_None` as a call argument. -/
def tzArgOf : Option Tz → Arg
  | some z => .tz z
  | none => .none_

/-- `new_datetime_subclass_fold_ex`, :1288-1305, with the object it returns: the fast path
`new_datetime` (`new_datetime_ex2`, :1209-1240) for `datetime`, otherwise
`call_subclass_fold(cls, fold, "iiiiiiiO", ...)`. -/
def newDtSubFoldObjC (y m d h mi s us : Int) (tz : Arg) (fold : Int) : DtType → Py DtAny
  | .base => (DtAny.dt 0 ·) <$> datetimeDatetimeImplC y m d h mi s us tz fold
  | .sub _ call => callSubclassFoldC call fold [.int y, .int m, .int d, .int h, .int mi, .int s, .int us, tz]

/-- `add_datetime_timedelta(date, delta, factor)`, :6241-6266: the fields with
`factor`-scaled `days`, `seconds`, `microseconds` added (:6247-6254), `normalize_datetime`
(:6257-6260), then `new_datetime_subclass_ex` with `date`'s tzinfo and `Py_TYPE(date)`
(:6262-6265; `new_datetime_subclass_ex` is the `fold = 0` case, :1308-1314). -/
def addDtDeltaObjC (cls : DtType) (date : DT) (delta : Delta) (factor : Int) : Py DtAny := do
  let r ← normalizeDatetimeC date.y date.m (date.d + delta.days * factor) date.h date.mi
    (date.s + delta.seconds * factor) (date.us + delta.us * factor)
  newDtSubFoldObjC r.y r.m r.d r.h r.mi r.s r.us (tzArgOf date.tz) 0 cls

/-! ### `utctimetuple` -/

/-- `datetime_utctimetuple`, :7154-7191, for a receiver of type `cls` holding `self`:
`GET_DT_TZINFO(self)` `None` keeps `self` (:7161-7163); otherwise `call_utcoffset` (:7166),
`None` keeps `self` (:7169-7172), any offset (zero included) is subtracted by
`add_datetime_timedelta` (:7174-7175); then the six fields of the result are read
(:7182-7187) and `build_struct_time(..., 0)`. `none` when that result is not a datetime. -/
def dtUtctimetupleObjC (env : TzEnv) (cls : DtType) (self : DT) : Option (Py TimeTuple) :=
  let utcself : Py DtAny := match self.tz with
    | none => .ok (.dt cls.tyId self)
    | some _ => do
      match ← self.utcoffsetC env with
      | none => pure (.dt cls.tyId self)
      | some o => addDtDeltaObjC cls self o (-1)
  match utcself with
  | .error e => some (.error e)
  | .ok (.dt _ u) => some (.ok (buildStructTimeC u.y u.m u.d u.h u.mi u.s 0))
  | .ok (.other _) => none

/-! ### `astimezone` -/

/-- :6963-6984: a naive result is rebuilt aware in UTC by
`new_datetime_ex2(..., CONST_UTC, DATE_GET_FOLD(result), Py_TYPE(result))` (:6964-6978, the
type's own allocation, no constructor call); an aware one gets `result->tzinfo = utc`
(:6981-6984). -/
def astzUtcC (r : DT) : Py DT :=
  if r.tz.isNone then datetimeDatetimeImplC r.y r.m r.d r.h r.mi r.s r.us (.tz tzUTC) r.fold
  else pure { r with tz := some tzUTC }

/-- :6987-6994: the target zone, `local_timezone(result)` for `tz` `None`. -/
def astzTargetC (env : TzEnv) (ltz : Int → Py LocalTmZ) (o1 : Nat) (tzinfo : Option Tz) (r : DT) : Py Tz :=
  match tzinfo with
  | some t => pure t
  | none => localTimezoneC env ltz o1 r

/-- :6957-7002 once the offset `o` is known: `result = add_datetime_timedelta(self, offset, -1)`
(:6957-6961); `HASTZINFO(result)` (:6963) and the UTC step `astzUtcC`; the target zone;
`result->tzinfo = tzinfo` (:6996) and `tzinfo.fromutc(result)` (:6998-7002), a method call
(`fromutc`). `none`: the result of the subtraction is not a datetime. -/
def astzObjFinishC (env : TzEnv) (ltz : Int → Py LocalTmZ) (o1 : Nat) (fromutc : Tz → DtAny → Py DtAny)
    (cls : DtType) (self : DT) (tzinfo : Option Tz) (o : Delta) : Option (Py DtAny) :=
  match addDtDeltaObjC cls self o (-1) with
  | .error e => some (.error e)
  | .ok (.other _) => none
  | .ok (.dt ty r) => some do
    let r ← astzUtcC r
    let t ← astzTargetC env ltz o1 tzinfo r
    fromutc t (.dt ty { r with tz := some t })

/-- :6936-6957 once `self_tzinfo` is the local zone `z` (the `naive:` path): the identity
test (`Py_NewRef(self)`), then `call_utcoffset`, which a `timezone` never answers with `None`. -/
def astzObjAfterLocalC (env : TzEnv) (ltz : Int → Py LocalTmZ) (o1 : Nat) (fromutc : Tz → DtAny → Py DtAny)
    (cls : DtType) (self : DT) (tzinfo : Option Tz) (z : Tz) : Option (Py DtAny) :=
  if tzinfo.map (·.oid) = some z.oid then some (.ok (.dt cls.tyId self))
  else match tzUtcoffsetRaw env z (some self) >>= callTzinfoCheckC "utcoffset" with
    | .error e => some (.error e)
    | .ok (some o) => astzObjFinishC env ltz o1 fromutc cls self tzinfo o
    | .ok none => some (.error .modelFuel)

/-- `datetime_datetime_astimezone_impl`, :6914-7004, for a receiver of type `cls` holding
`self`: `check_tzinfo_subclass` (:6923); a naive `self` takes `local_timezone_from_local`
(`naive:`, :6926-6930); an aware one the identity test (:6936-6939) and `call_utcoffset`
(:6942), `None` going to `naive:` (:6946-6949); then `astzObjFinishC`. -/
def dtAstimezoneObjC (env : TzEnv) (ltz : Int → Py LocalTmZ) (o1 o2 : Nat) (fromutc : Tz → DtAny → Py DtAny)
    (cls : DtType) (self : DT) (arg : AstzArg) : Option (Py DtAny) :=
  match arg with
  | .other => some (.error (.typeError "~tzinfo argument must be None or of a tzinfo subclass"))
  | .none_ | .tz _ =>
    let tzinfo : Option Tz := match arg with | .tz t => some t | _ => none
    match self.tz with
    | none =>
      match localTimezoneFromLocalC ltz o2 self with
      | .error e => some (.error e)
      | .ok z => astzObjAfterLocalC env ltz o1 fromutc cls self tzinfo z
    | some z =>
      if tzinfo.map (·.oid) = some z.oid then some (.ok (.dt cls.tyId self))
      else match tzUtcoffsetRaw env z (some self) >>= callTzinfoCheckC "utcoffset" with
        | .error e => some (.error e)
        | .ok (some o) => astzObjFinishC env ltz o1 fromutc cls self tzinfo o
        | .ok none =>
          match localTimezoneFromLocalC ltz o2 self with
          | .error e => some (.error e)
          | .ok z' => astzObjAfterLocalC env ltz o1 fromutc cls self tzinfo z'

/-- The built-in `fromutc` on base-class objects: `tzFromutcC` (`timezone_fromutc` or
`tzinfo_fromutc`) of the value, for a `tzinfo` that does not override `fromutc`. -/
def builtinFromutcObj (env : TzEnv) (t : Tz) : DtAny → Py DtAny
  | .dt 0 v => (DtAny.dt 0 ·) <$> tzFromutcC env t v
  | _ => .error .modelFuel

/-! ### `pep495_eq_exception` over objects -/

/-- A checked `utcoffset()` result as `pep495_eq_exception` holds it: the `None` singleton or a
`timedelta` object with its identity `oid`. -/
inductive OffObj where
  | none_
  | td (oid : Nat) (v : Delta)
  deriving DecidableEq, Repr

/-- `a != b` on the two pointers (`None` is one object). -/
def OffObj.ptrNe : OffObj → OffObj → Bool
  | .none_, .none_ => false
  | .td i _, .td j _ => i != j
  | _, _ => true

/-- The value, as the `Option Delta` model of `utcoffset()` has it. -/
def OffObj.val : OffObj → Option Delta
  | .none_ => none
  | .td _ v => some v

/-- `delta_cmp(a, b)`, :2536-2546: `GET_TD_DAYS`, `GET_TD_SECONDS`, `GET_TD_MICROSECONDS` of
both arguments, with no type check. Defined only when both are `timedelta` objects; on the
`None` singleton the reads fall outside its `PyObject` header (`none`). -/
def deltaCmpObjC : OffObj → OffObj → Option Int
  | .td _ a, .td _ b => some (a.cmpC b)
  | _, _ => none

/-- One test of `pep495_eq_exception`: `flip_offset != offset && delta_cmp(flip_offset,
offset)` (:6569-6570, :6579-6580), the pointer test first. `none`: `delta_cmp` read a
non-`timedelta` as one. -/
def pep495StepC (f o : OffObj) : Option Bool :=
  if f.ptrNe o then (deltaCmpObjC f o).map (fun c => decide (c ≠ 0)) else some false

/-- `pep495_eq_exception(self, other, offset_self, offset_other)`, :6560-6586, given what
`get_flip_fold_offset` returns for `self` (`flip1`, :6567) and `other` (`flip2`, :6576, called
only when the first test does not fire): the test for `self` (:6569-6574, `result = 1`), then
the one for `other` (:6579-6581). -/
def pep495EqExceptionObjC (flip1 flip2 : Py OffObj) (o1 o2 : OffObj) : Option (Py Bool) :=
  match flip1 with
  | .error e => some (.error e)
  | .ok f1 =>
    match pep495StepC f1 o1 with
    | none => none
    | some true => some (.ok true)
    | some false =>
      match flip2 with
      | .error e => some (.error e)
      | .ok f2 => (pep495StepC f2 o2).map .ok

/-- Python's PEP 495 exception in `datetime._cmp(..., allow_mixed=True)`, Py:2315-2319:
`myoff != self.replace(fold=not self.fold).utcoffset()` (a `timedelta` against `None` is
unequal: `timedelta.__ne__` returns `NotImplemented` and the fallback compares identity), then
the same for `other`. -/
def pep495EqExceptionPy (flip1 flip2 : Py (Option Delta)) (o1 o2 : Option Delta) : Py Bool := do
  if !offEq o1 (← flip1) then return true
  return !offEq o2 (← flip2)

end PyLean.Datetime
