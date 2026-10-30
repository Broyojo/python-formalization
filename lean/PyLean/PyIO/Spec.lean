import PyLean.PyIO.BytesIO
import PyLean.PyIO.StringC
import PyLean.PyIO.StringPy

/-!
Vocabulary for the `PyIO` properties: outcome equivalence and the
hypotheses of the narrowed twin properties.
-/

namespace PyLean.PyIO

open PyLean

/-- Two outcomes agree on the value, or both raise exceptions of the same
class (messages may differ). -/
def sameClass : Py Val → Py Val → Bool
  | .ok a, .ok b => a == b
  | .error e₁, .error e₂ => e₁.className == e₂.className
  | _, _ => false

def allSameClass : List (Py Val) → List (Py Val) → Bool
  | [], [] => true
  | a :: as, b :: bs => sameClass a b && allSameClass as bs
  | _, _ => false

/-- Every result of two runs agrees up to the exception message. -/
def AllSameClass (l₁ l₂ : List (Py Val)) : Prop := allSameClass l₁ l₂ = true

instance (l₁ l₂ : List (Py Val)) : Decidable (AllSameClass l₁ l₂) :=
  inferInstanceAs (Decidable (_ = true))

/-- Every int argument fits the C converter that receives it: `Py_ssize_t`
(and `long`) for sizes and positions, `int` for `whence`. -/
def BOp.InRange : BOp → Prop
  | .read (some n) | .read1 (some n) | .readline (some n) | .readlines (some n)
  | .truncate (some n) => InSsize n
  | .seek p w => InSsize p ∧ InCInt w
  | _ => True

instance (o : BOp) : Decidable o.InRange := by
  unfold BOp.InRange; split <;> infer_instance

/-- The operation is not `getbuffer()` (no exported views). -/
def BOp.NoExport : BOp → Prop
  | .getbuffer => False
  | _ => True

instance (o : BOp) : Decidable o.NoExport := by
  unfold BOp.NoExport; split <;> infer_instance

/-- In the Python run's state `s`, the operation keeps every position and
write extent below the allocation bound `memLimit`, so no allocation fails
(resource exhaustion is excluded). -/
def BOp.Small (s : BState) : BOp → Prop
  | .seek p w => (w = 0 → p < memLimit) ∧ (w = 1 → s.pos + p < memLimit) ∧
      (w = 2 → s.buf.length + p < memLimit)
  | .write b => s.pos + b.length < memLimit
  | _ => True

instance (s : BState) (o : BOp) : Decidable (o.Small s) := by
  unfold BOp.Small; split <;> infer_instance

/-- `readline(0)` is not called on a closed stream (`IOBase`: "calling any
method (even inquiries) on a closed stream is undefined", _pyio.py:323-324). -/
def BOp.NoReadline0Closed (s : BState) : BOp → Prop
  | .readline (some 0) => s.closed = false
  | _ => True

instance (s : BState) (o : BOp) : Decidable (o.NoReadline0Closed s) := by
  unfold BOp.NoReadline0Closed; split <;> infer_instance

/-- `Q` holds for every operation in the state the Python twin is in when the
operation runs. -/
def PyRunAll (Q : BState → BOp → Prop) : BState → List BOp → Prop
  | _, [] => True
  | s, o :: os => Q s o ∧ PyRunAll Q (P.step s o).1 os

def decPyRunAll (Q : BState → BOp → Prop) [∀ s o, Decidable (Q s o)] :
    ∀ s ops, Decidable (PyRunAll Q s ops)
  | _, [] => isTrue trivial
  | s, o :: os =>
    if h : Q s o then
      match decPyRunAll Q (P.step s o).1 os with
      | isTrue h' => isTrue ⟨h, h'⟩
      | isFalse h' => isFalse (fun ⟨_, h''⟩ => h' h'')
    else isFalse (fun ⟨h', _⟩ => h h')

instance (Q : BState → BOp → Prop) [∀ s o, Decidable (Q s o)] (s : BState) (ops : List BOp) :
    Decidable (PyRunAll Q s ops) := decPyRunAll Q s ops

end PyLean.PyIO
