import PyLean.Datetime.IsoC
import PyLean.Datetime.Format

/-!
Vocabulary for the `datetime` properties.
-/

namespace PyLean.Datetime

open PyLean

/-- Two results agree on the value, or both raise exceptions of the same class.
Exception messages are not compared: the C and Python twins word many of them
differently on purpose (e.g. `date value out of range` vs `result out of
range`), and CPython's tests do not check them. -/
def SameOutcome {α : Type} : Py α → Py α → Prop
  | .ok a, .ok b => a = b
  | .error e₁, .error e₂ => e₁.className = e₂.className
  | _, _ => False

/-- `True` when the computation returned a value. -/
def Py.isOk {α : Type} : Py α → Bool
  | .ok _ => true
  | .error _ => false

theorem sameOutcome_refl {α : Type} (x : Py α) : SameOutcome x x := by
  cases x <;> simp [SameOutcome]

end PyLean.Datetime
