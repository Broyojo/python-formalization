import PyLean.BytesObj.Seq.TupleModel

/-!
`slice.__eq__` and `slice.__hash__`, Objects/sliceobject.c, CPython 3.15.2, over an abstract part
type. A slice object has an identity (`oid`) and three parts. `eqB` is
`PyObject_RichCompareBool(x, y, Py_EQ)` on parts (identity first, then `==`; it may raise) and
`hashE` is `PyObject_Hash` on a part (it may raise).
-/

namespace PyLean.RangeSlice.SliceHash

open PyLean PyLean.BytesObj.Seq

variable {α : Type}

structure SObj (α : Type) where
  oid : Nat
  start : α
  stop : α
  step : α

/-- `slice_richcompare(v, w, Py_EQ)`, sliceobject.c:581-625: `v is w` is true; otherwise
`(v.start, v.stop, v.step) == (w.start, w.stop, w.step)`, which `tuple_richcompare` decides
part by part with `PyObject_RichCompareBool` and stops at the first part that differs. -/
def sliceEq (eqB : α → α → Py Bool) (v w : SObj α) : Py Bool :=
  if v.oid = w.oid then .ok true
  else
    match eqB v.start w.start with
    | .error e => .error e
    | .ok false => .ok false
    | .ok true =>
      match eqB v.stop w.stop with
      | .error e => .error e
      | .ok false => .ok false
      | .ok true => eqB v.step w.step

/-- `slice_hash(op)`, sliceobject.c:651-672: the tuple-hash rounds over start, stop and step
(`hashLoop`, with `PyObject_Hash` failing as `.error`), no length term, and the `-1` remap. -/
def sliceHash (hashE : α → Py Int) (v : SObj α) : Py Int :=
  match hashLoop hashE [v.start, v.stop, v.step] XXP5 with
  | .error e => .error e
  | .ok acc => .ok (toHash (if acc = U64 - 1 then 1546275796 else acc))

/-- If the part type's `__hash__` agrees with `==` (equal parts hash alike, a precondition of
hashing), and two references to one object hold the same parts, then equal slices have equal
hashes, including when hashing raises. -/
def SliceHashEq : Prop :=
  ∀ (α : Type) (eqB : α → α → Py Bool) (hashE : α → Py Int) (v w : SObj α),
    (∀ x y, eqB x y = .ok true → hashE x = hashE y) →
    (v.oid = w.oid → v.start = w.start ∧ v.stop = w.stop ∧ v.step = w.step) →
    sliceEq eqB v w = .ok true → sliceHash hashE v = sliceHash hashE w

theorem sliceHashEq_proven : SliceHashEq := by
  intro α eqB hashE v w hcons hid heq
  unfold sliceEq at heq
  by_cases ho : v.oid = w.oid
  · obtain ⟨h1, h2, h3⟩ := hid ho
    simp [sliceHash, h1, h2, h3]
  · rw [if_neg ho] at heq
    cases e1 : eqB v.start w.start with
    | error e => rw [e1] at heq; cases heq
    | ok b1 =>
      rw [e1] at heq
      cases b1
      · cases heq
      · cases e2 : eqB v.stop w.stop with
        | error e => simp only [e2] at heq; cases heq
        | ok b2 =>
          simp only [e2] at heq
          cases b2
          · cases heq
          · simp [sliceHash, hashLoop, hcons _ _ e1, hcons _ _ e2, hcons _ _ heq]

/-- The hash/eq contract fails without the precondition: a part type whose equal values hash
differently gives equal slices with different hashes (as `hash` does for such a type). -/
theorem sliceHashEq_needs_precondition :
    ¬ (∀ (eqB : Nat → Nat → Py Bool) (hashE : Nat → Py Int) (v w : SObj Nat),
        sliceEq eqB v w = .ok true → sliceHash hashE v = sliceHash hashE w) := by
  intro h
  have := h (fun _ _ => .ok true) (fun x => .ok x) ⟨0, 1, 1, 1⟩ ⟨1, 2, 2, 2⟩ rfl
  revert this
  decide

end PyLean.RangeSlice.SliceHash
