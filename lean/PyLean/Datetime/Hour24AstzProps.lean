import PyLean.Datetime.ClsRowsProps
import PyLean.Datetime.SubObjProps

/-!
Two C-side statements, CPython 3.15.2: the hour-24 rule of `datetime_time_fromisoformat_impl`
(Modules/_datetimemodule.c:5224-5230), and `datetime_datetime_astimezone_impl`'s writes into
the object `add_datetime_timedelta` returned (:6957-6996), over a heap of datetime objects.
-/

namespace PyLean.Datetime

open PyLean

/-! ### `time.fromisoformat` and hour 24 -/

/-- `time.fromisoformat(s)` in C, for every class and every string whose time part parses with
hour 24 (after a leading `T` is dropped, :5204-5207): with minute, second and microsecond all
zero the hour becomes 0 (:5224-5226) and the result is that midnight with the parsed tzinfo,
built for `time` itself or by calling a subclass with `(0, 0, 0, 0, tzinfo)`; otherwise it is
`ValueError: minute, second, and microsecond must be 0 when hour is 24` (:5227-5228, :5248-5250),
raised before the tzinfo is built. -/
def TimeFromIsoHour24C : Prop :=
  ∀ (cls : ClsC TimeV) (s : List Char),
    let b := utf8 s
    let p := if byteAt b 0 = 84 then 1 else 0
    let len := if byteAt b 0 = 84 then b.length - 1 else b.length
    let r := parseIsoTimeC b p len
    0 ≤ r.rv → r.h = 24 →
      ((r.mi = 0 ∧ r.s = 0 ∧ r.us = 0) →
        timeFromIsoClsC cls s = (do
          let tz ← tzinfoFromIsoResults r.rv r.tzoffset r.tzus
          match cls with
          | .base => tmIsoBaseTail (0, 0, 0, 0, tz)
          | .sub call => call (tmIsoArgs (0, 0, 0, 0, tz)) none)) ∧
      (¬ (r.mi = 0 ∧ r.s = 0 ∧ r.us = 0) →
        timeFromIsoClsC cls s = .error (.valueError "minute, second, and microsecond must be 0 when hour is 24"))

theorem timeFromIsoHour24C_proven : TimeFromIsoHour24C := by
  intro cls s
  simp only
  intro h0 h24
  have hrv : ¬ (parseIsoTimeC (utf8 s) (if byteAt (utf8 s) 0 = 84 then 1 else 0)
      (if byteAt (utf8 s) 0 = 84 then (utf8 s).length - 1 else (utf8 s).length)).rv < 0 := by omega
  have e : ∀ {α : Type} (k : Int × Int × Int × Int × Option Int → Py α), timeFromIsoK s k = (do
      let r := parseIsoTimeC (utf8 s) (if byteAt (utf8 s) 0 = 84 then 1 else 0)
        (if byteAt (utf8 s) 0 = 84 then (utf8 s).length - 1 else (utf8 s).length)
      let hour ← if r.h = 24 then
          if r.mi = 0 ∧ r.s = 0 ∧ r.us = 0 then pure 0
          else throw (.valueError "minute, second, and microsecond must be 0 when hour is 24")
        else pure r.h
      let tz ← tzinfoFromIsoResults r.rv r.tzoffset r.tzus
      k (hour, r.mi, r.s, r.us, tz)) := by
    intro α k
    unfold timeFromIsoK
    by_cases hT : byteAt (utf8 s) 0 = 84
    · simp only [hT, ite_true] at hrv ⊢; simp [hrv]
    · simp only [hT, ite_false] at hrv ⊢; simp [hrv]
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · unfold timeFromIsoClsC
    rw [e]
    obtain ⟨h1, h2, h3⟩ := hz
    simp only [h24, ite_true, h1, h2, h3, and_self, pure, Except.pure, bind, Except.bind]
    rfl
  · unfold timeFromIsoClsC
    rw [e]
    simp only [h24, ite_true, hz, ite_false, bind, Except.bind]
    rfl

/-- The values on three strings, as CPython 3.15.2 gives them: `time.fromisoformat('24:00')`
is `time(0, 0)`, `'T24:00:00+01:00'` is `time(0, 0, tzinfo=timezone(timedelta(hours=1)))`, and
`'24:00:00.000001'` is the hour-24 `ValueError`. -/
theorem timeFromIsoHour24C_examples :
    timeFromIsoClsC .base "24:00".toList = .ok ⟨0, 0, 0, 0, none⟩ ∧
    timeFromIsoClsC .base "T24:00:00+01:00".toList = .ok ⟨0, 0, 0, 0, some 3600000000⟩ ∧
    timeFromIsoClsC .base "24:00:00.000001".toList =
      .error (.valueError "minute, second, and microsecond must be 0 when hour is 24") := by
  decide +kernel

/-! ### `astimezone` and the object the subclass call returned -/

/-- The `datetime` objects alive in the process, by identity, with the fields of their structs
(`none`: no such object). -/
abbrev DtHeap := Nat → Option DT

/-- `type(self)(...)` for a `datetime` subclass, over the heap: it returns the identity of a
`datetime` object, which may be a new one (the heap it returns has it) or one that already
existed (a cache), or raises. -/
abbrev HeapCall := DtHeap → List Arg → Py (Nat × DtHeap)

/-- Python code cannot write the struct of an existing `datetime`: a call may only add
objects. -/
def HeapCall.OnlyAllocates (call : HeapCall) : Prop :=
  ∀ h args i h', call h args = .ok (i, h') → ∀ j v, h j = some v → h' j = some v

/-- `tz.fromutc(dt)` over the heap, given the identity of its argument. -/
abbrev HeapFromutc := DtHeap → Nat → Py (Nat × DtHeap)

def HeapFromutc.OnlyAllocates (f : HeapFromutc) : Prop :=
  ∀ h i j h', f h i = .ok (j, h') → ∀ k v, h k = some v → h' k = some v

/-- Write the `tzinfo` member of object `i` (`Py_SETREF(result->tzinfo, ...)`). -/
def heapSetTz (h : DtHeap) (i : Nat) (tz : Tz) : DtHeap :=
  fun j => if j = i then (h i).map (fun v => { v with tz := some tz }) else h j

/-- `datetime_datetime_astimezone_impl`, :6957-7002, for an aware `self` of a subclass whose
`utcoffset()` gave the valid offset `o`, and a target `timezone` `tzinfo`: `result =
add_datetime_timedelta(self, offset, -1)` (:6957-6961, the subclass called with the eight
fields and `self`'s tzinfo); if `HASTZINFO(result)` the member is set to UTC in place
(:6981-6984), otherwise a new object is built (:6964-6980, allocated as `fresh`); then
`result->tzinfo = tzinfo` in place (:6996) and `tzinfo.fromutc(result)` (:6998-7002). -/
def astzHeapC (call : HeapCall) (fromutc : HeapFromutc) (fresh : Nat) (h : DtHeap) (self : DT) (o : Delta)
    (tzinfo : Tz) : Py (Nat × DtHeap) := do
  let r ← normalizeDatetimeC self.y self.m (self.d - o.days) self.h self.mi (self.s - o.seconds) (self.us - o.us)
  let (i, h) ← call h [.int r.y, .int r.m, .int r.d, .int r.h, .int r.mi, .int r.s, .int r.us, tzArgOf self.tz]
  match h i with
  | none => throw .modelFuel
  | some v =>
    let (i, h) := if v.tz.isNone then
        (fresh, fun j => if j = fresh then some { v with tz := some tzUTC } else h j)
      else (i, heapSetTz h i tzUTC)
    let h := heapSetTz h i tzinfo
    fromutc h i

/-- `datetime.astimezone(tz)`, Py:2137-2160, on the same path: `utc = (self -
myoffset).replace(tzinfo=tz)` (:2157), two calls of the class (`self - myoffset` through
`type(self).combine`, :2361-2365, :2340-2358 and :1959-1961; `replace` through `type(self)(...)`,
:2116-2117), then `tz.fromutc(utc)` (:2160). Nothing is written. -/
def astzHeapPy (call : HeapCall) (fromutc : HeapFromutc) (h : DtHeap) (self : DT) (o : Delta) (tzinfo : Tz) :
    Py (Nat × DtHeap) := do
  let r ← normalizeDatetimeC self.y self.m (self.d - o.days) self.h self.mi (self.s - o.seconds) (self.us - o.us)
  let (i, h) ← call h [.int r.y, .int r.m, .int r.d, .int r.h, .int r.mi, .int r.s, .int r.us, tzArgOf self.tz]
  match h i with
  | none => throw .modelFuel
  | some v =>
    let (j, h) ← call h [.int v.y, .int v.m, .int v.d, .int v.h, .int v.mi, .int v.s, .int v.us, .tz tzinfo]
    fromutc h j

/-- `astimezone` never changes a `datetime` that existed before the call, for every subclass
call and `fromutc` that only allocate: datetimes are immutable. -/
def AstimezoneKeepsObjects : Prop :=
  ∀ (call : HeapCall) (fromutc : HeapFromutc) (fresh : Nat) (h : DtHeap) (self : DT) (o : Delta) (tzinfo : Tz)
    (i : Nat) (h' : DtHeap),
    call.OnlyAllocates → fromutc.OnlyAllocates → (∀ v, h fresh ≠ some v) →
    astzHeapC call fromutc fresh h self o tzinfo = .ok (i, h') → ∀ j v, h j = some v → h' j = some v

/-- The Python twin keeps every object that existed before the call. -/
def AstimezoneKeepsObjectsPy : Prop :=
  ∀ (call : HeapCall) (fromutc : HeapFromutc) (h : DtHeap) (self : DT) (o : Delta) (tzinfo : Tz)
    (i : Nat) (h' : DtHeap),
    call.OnlyAllocates → fromutc.OnlyAllocates →
    astzHeapPy call fromutc h self o tzinfo = .ok (i, h') → ∀ j v, h j = some v → h' j = some v

/-- The Python twin keeps every object. -/
theorem astimezoneKeepsObjectsPy_proven : AstimezoneKeepsObjectsPy := by
  intro call fromutc h self o tzinfo i h' hc hf he j v hv
  unfold astzHeapPy at he
  cases hn : normalizeDatetimeC self.y self.m (self.d - o.days) self.h self.mi (self.s - o.seconds) (self.us - o.us) with
  | error e => rw [hn] at he; cases he
  | ok r =>
    rw [hn] at he
    simp only [bind, Except.bind] at he
    cases h1 : call h [.int r.y, .int r.m, .int r.d, .int r.h, .int r.mi, .int r.s, .int r.us, tzArgOf self.tz] with
    | error e => rw [h1] at he; cases he
    | ok p1 =>
      obtain ⟨i1, h1'⟩ := p1
      rw [h1] at he
      have k1 := hc _ _ _ _ h1 j v hv
      simp only at he
      cases hv1 : h1' i1 with
      | none => rw [hv1] at he; cases he
      | some w =>
        rw [hv1] at he
        simp only at he
        cases h2 : call h1' [.int w.y, .int w.m, .int w.d, .int w.h, .int w.mi, .int w.s, .int w.us, .tz tzinfo] with
        | error e => rw [h2] at he; cases he
        | ok p2 =>
          obtain ⟨i2, h2'⟩ := p2
          rw [h2] at he
          have k2 := hc _ _ _ _ h2 j v k1
          exact hf _ _ _ _ he j v k2

/-- A subclass whose `__new__` hands back a cached instance for the eight-argument call
(`if len(args) == 8: return D.cache`): C sets the cached object's tzinfo to UTC and then to
the target zone in place, so the shared object `D.cache` changes (on CPython 3.15.2 its repr
shows the new zone, it compares equal to `datetime(..., tzinfo=+02:00)` and keeps the hash it
had at UTC); Python only reads it, and its `fromutc` raises instead. -/
theorem astimezoneKeepsObjects_refuted : ¬ AstimezoneKeepsObjects := by
  intro hk
  have hc : HeapCall.OnlyAllocates (fun h _ => .ok (0, h)) := by
    intro h args i h' he j v hv
    simp only [Except.ok.injEq, Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    exact hv
  have hf : HeapFromutc.OnlyAllocates (fun h i => .ok (i, h)) := by
    intro h i j h' he k v hv
    simp only [Except.ok.injEq, Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    exact hv
  have hr := hk (fun h _ => .ok (0, h)) (fun h i => .ok (i, h)) 1
    (fun j => if j = 0 then some ⟨2000, 1, 1, 11, 0, 0, 0, 0, some tzUTC⟩ else none)
    ⟨2000, 1, 1, 12, 0, 0, 0, 0, some ⟨1, .timezone ⟨0, 3600, 0⟩ none⟩⟩ ⟨0, 3600, 0⟩ ⟨2, .timezone ⟨0, 7200, 0⟩ none⟩
    0 (heapSetTz (heapSetTz (fun j => if j = 0 then some ⟨2000, 1, 1, 11, 0, 0, 0, 0, some tzUTC⟩ else none) 0 tzUTC)
      0 ⟨2, .timezone ⟨0, 7200, 0⟩ none⟩) hc hf (by intro v; simp) rfl 0 ⟨2000, 1, 1, 11, 0, 0, 0, 0, some tzUTC⟩
    (by simp)
  simp [heapSetTz, tzUTC] at hr

end PyLean.Datetime
