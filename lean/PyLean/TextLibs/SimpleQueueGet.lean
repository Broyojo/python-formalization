import PyLean.Core

/-!
`queue.SimpleQueue.get(block, timeout)` on a non-empty queue: the C accelerator
(`_queue_SimpleQueue_get_impl`, Modules/_queuemodule.c) against the pure-Python twin
(`queue._PySimpleQueue.get`, Lib/queue.py:338-355). Only the path where an item is already
available is modelled; waiting is not.

A timeout is `None`, a finite number of seconds, infinity or NaN. C converts it first with
`_PyTime_FromSecondsObject(..., _PyTime_ROUND_CEILING)` (Python/pytime.c): NaN is a `ValueError`,
a value whose nanoseconds leave `PyTime_t` (infinity included) an `OverflowError`; then a
negative timeout is a `ValueError`. The twin only rejects `timeout < 0` (false for NaN) and then
calls `self._count.acquire(block, timeout)`, which returns at once while the count is positive.
-/

namespace PyLean.TextLibs.SQ

/-- `num n d` is `n / d` seconds, `d > 0`. -/
inductive TO where
  | none
  | num (n : Int) (d : Nat)
  | inf
  | nan

/-- `ceil(n * 10^9 / d)` for `d > 0`: Lean's `Int` division floors for a positive divisor. -/
def ceilNs (n : Int) (d : Nat) : Int := -((-n * 1000000000) / (d : Int))

/-- `_PyTime_FromSecondsObject` with ceiling rounding, to nanoseconds. -/
def toNs : TO → Py Int
  | .none => .ok 0
  | .nan => .error (.valueError "Invalid value NaN (not a number)")
  | .inf => .error (.overflowError "timestamp out of range for C PyTime_t")
  | .num n d =>
    let ns := ceilNs n d
    if -(2 ^ 63) ≤ ns ∧ ns < 2 ^ 63 then .ok ns
    else .error (.overflowError "timestamp out of range for C PyTime_t")

/-- C: convert (when blocking with a timeout), check the sign, then take the head. -/
def getC {α : Type} (block : Bool) (t : TO) (x : α) : Py α :=
  match block, t with
  | true, .none => .ok x
  | false, _ => .ok x
  | true, t => match toNs t with
    | .error e => .error e
    | .ok ns => if ns < 0 then .error (.valueError "'timeout' must be a non-negative number") else .ok x

/-- The twin: `timeout < 0` raises; otherwise the semaphore is acquired at once. -/
def getPy {α : Type} (block : Bool) (t : TO) (x : α) : Py α :=
  if !block then .ok x
  else match t with
    | .num n _ => if n < 0 then .error (.valueError "'timeout' must be a non-negative number") else .ok x
    | _ => .ok x

/-- Whenever the twin returns the waiting item, so does C. -/
def GetTwins : Prop := ∀ (α : Type) (block : Bool) (t : TO) (x : α), getPy block t x = .ok x → getC block t x = .ok x

/-- `q.put(1); q.get(timeout=float('inf'))` raises `OverflowError` in C. -/
theorem getTwins_refuted : ¬ GetTwins := by
  intro h
  have := h Nat true .inf 1 rfl
  simp [getC, toNs] at this

/-- For `None` and for finite timeouts within `PyTime_t` that are non-negative or at most -1 ns,
the twins agree. Between -1 ns and 0 they do not: C rounds up to 0 ns and returns the item, the
twin raises `ValueError` (`getTwinsTinyNegative_refuted`). -/
def GetTwinsFinite : Prop :=
  ∀ (α : Type) (block : Bool) (n : Int) (d : Nat) (x : α), 0 < d →
    -(2 ^ 63) ≤ ceilNs n d → ceilNs n d < 2 ^ 63 → (0 ≤ n ∨ n * 1000000000 ≤ -(d : Int)) →
    getC block (.num n d) x = getPy block (.num n d) x ∧ getC block .none x = getPy block .none x

theorem getTwinsFinite_proven : GetTwinsFinite := by
  intro α block n d x hd h1 h2 hq
  cases block
  · simp [getC, getPy]
  · refine ⟨?_, by simp [getC, getPy]⟩
    simp only [getC, getPy, toNs, if_pos (And.intro h1 h2), Bool.not_true]
    unfold ceilNs
    have hdi : (0 : Int) < d := by omega
    rcases hq with hq | hq
    · have : 0 ≤ -((-n * 1000000000) / (d : Int)) := by
        have := Int.ediv_le_ediv hdi (show -n * 1000000000 ≤ 0 by omega)
        simp at this; omega
      generalize (-n * 1000000000) / (d : Int) = A at *
      simp only [show ¬ (-A < 0) by omega, show ¬ n < 0 by omega, if_false]; rfl
    · have : -((-n * 1000000000) / (d : Int)) < 0 := by
        have := Int.le_ediv_of_mul_le hdi (show 1 * (d : Int) ≤ -n * 1000000000 by omega)
        omega
      have hn : n < 0 := by omega
      generalize (-n * 1000000000) / (d : Int) = A at *
      simp only [this, hn, if_true]; rfl

/-- `q.get(timeout=-1e-10)` on a non-empty queue: C returns the item, the twin raises. -/
def GetTwinsTinyNegative : Prop := ∀ (α : Type) (n : Int) (d : Nat) (x : α), getC true (.num n d) x = getPy true (.num n d) x

theorem getTwinsTinyNegative_refuted : ¬ GetTwinsTinyNegative := by
  intro h
  have := h Nat (-1) 10000000000 1
  revert this
  decide

end PyLean.TextLibs.SQ
