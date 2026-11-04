import PyLean.Datetime.ClsRowsProps

/-!
`time.__reduce__` and `datetime.__reduce__` (Lib/_pydatetime.py:1782-1783, :2435-2436) are
`self.__reduce_ex__(2)`: an attribute lookup on the instance, so a subclass's own
`__reduce_ex__` runs. C's `datetime_time___reduce___impl` and
`datetime_datetime___reduce___impl` (Modules/_datetimemodule.c:5308-5312, :7241-7246) build
`(Py_TYPE(self), time_getstate(self, 2))` themselves and never look the method up. CPython 3.15.2.
-/

namespace PyLean.Datetime

open PyLean

/-- `time.__reduce__()`, Py:1782-1783: `self.__reduce_ex__(2)`. `reduceEx` is the bound method
the lookup finds on the receiver and what calling it returns: `time.__reduce_ex__` itself
(`fun p => .ok (tmReduceExClsPy ty t p)`) for a class that keeps it, a subclass's override
otherwise. -/
def tmReduceDispatchPy (reduceEx : Int → Py (Nat × StateTuple)) : Py (Nat × StateTuple) := reduceEx 2

/-- `datetime.__reduce__()`, Py:2435-2436: `self.__reduce_ex__(2)`, as `tmReduceDispatchPy`. -/
def dtReduceDispatchPy (reduceEx : Int → Py (Nat × StateTuple)) : Py (Nat × StateTuple) := reduceEx 2

/-- The broad twin: `time.__reduce__()` and `datetime.__reduce__()` agree between the twins
for every receiver class, whatever `__reduce_ex__` that class has. -/
def ReduceDispatchTwins : Prop :=
  (∀ (ty : Nat) (t : TM) (reduceEx : Int → Py (Nat × StateTuple)), t.Valid →
    tmReduceDispatchPy reduceEx = .ok (tmReduceClsC ty t)) ∧
  (∀ (ty : Nat) (dt : DT) (reduceEx : Int → Py (Nat × StateTuple)), dt.Valid →
    dtReduceDispatchPy reduceEx = .ok (dtReduceClsC ty dt))

/-- `class T(time)` whose `__reduce_ex__` is `return self.__reduce__()` (a delegation that
works with the C class): Python's `__reduce__` calls it back and the recursion ends in
`RecursionError`; C's `__reduce__` never consults it and returns `(T, state)`. -/
theorem reduceDispatchTwins_refuted : ¬ ReduceDispatchTwins := by
  intro h
  have h1 := h.1 0 {} (fun _ => .error (.named "RecursionError" "maximum recursion depth exceeded"))
    (by simp [TM.Valid, OptTzOk])
  simp [tmReduceDispatchPy] at h1

/-- The narrowed twin: for a class that keeps the inherited `__reduce_ex__`, Python's
`__reduce__` is C's for every valid time and datetime (the receiver's class and the protocol-2
state), and unpickling that state gives the value back with fold 0 in both twins. A
`__reduce__` that ignored the lookup (or called it with another protocol, keeping the fold)
fails. -/
def ReduceDispatchInherited : Prop :=
  (∀ (ty : Nat) (t : TM), t.Valid →
    tmReduceDispatchPy (fun p => .ok (tmReduceExClsPy ty t p)) = .ok (tmReduceClsC ty t) ∧
    timeCallPy (tmReduceClsC ty t).2.args (.int 0) = .ok { t with fold := 0 }) ∧
  (∀ (ty : Nat) (dt : DT), dt.Valid →
    dtReduceDispatchPy (fun p => .ok (dtReduceExClsPy ty dt p)) = .ok (dtReduceClsC ty dt) ∧
    datetimeCallPy (dtReduceClsC ty dt).2.args (.int 0) = .ok { dt with fold := 0 })

theorem reduceDispatchInherited_proven : ReduceDispatchInherited := by
  refine ⟨fun ty t hv => ?_, fun ty dt hv => ?_⟩
  · have e := (timeReduceExCls_proven ty t hv).2.2.2
    have r := (timeReduceRoundtrip_proven t 2 hv).2.2.2.2.1
    refine ⟨by simp [tmReduceDispatchPy, e], ?_⟩
    rw [e]
    simpa [tmReduceExClsPy, tmReducePy] using r
  · have e := (datetimeReduceExCls_proven ty dt hv).2.2.2
    have r := (datetimeReduceRoundtrip_proven dt 2 hv).2.2.2.2.1
    refine ⟨by simp [dtReduceDispatchPy, e], ?_⟩
    rw [e]
    simpa [dtReduceExClsPy, dtReducePy] using r

end PyLean.Datetime
