import PyLean.Core

/-!
`PySequence_Tuple(v)`, Objects/abstract.c:2005-2078, CPython 3.15.2 (what `tuple(v)` runs): an
exact tuple is returned as is, an exact list is copied, anything else is iterated. Since 3.15 the
first eight items go to a stack buffer, then the buffer moves into a list that grows by append.

The iterator is fallible: it yields `xs`, then ends (`err = none`) or raises `err`.
-/

namespace PyLean.TypeObj.SeqTuple

variable {α : Type}

inductive Src (α : Type) where
  | exactTuple (xs : List α)
  | exactList (xs : List α)
  | iter (xs : List α) (err : Option PyExc)
  | notIterable (msg : String)

/-- The result: the argument itself, or a new tuple. -/
inductive Out (α : Type) where
  | same
  | fresh (xs : List α)
  deriving DecidableEq

/-- The append loop, :2052-2066: `PyIter_Next` until it returns NULL; with an exception set the
list is dropped and NULL returned. -/
def appendLoop (err : Option PyExc) : List α → List α → Py (Out α)
  | [], acc => match err with | some e => .error e | none => .ok (.fresh acc)
  | x :: r, acc => appendLoop err r (acc ++ [x])

/-- The buffer loop, :2031-2041: up to eight items; ending early builds the tuple from the buffer
(`_PyTuple_FromArraySteal`), an exception drops the buffer; after eight items the buffer becomes
the first eight list items (:2042-2051). -/
def bufferLoop (err : Option PyExc) : Nat → List α → List α → Py (Out α)
  | n, rest, buf =>
    if n < 8 then
      match rest with
      | [] => match err with | some e => .error e | none => .ok (.fresh buf)
      | x :: r => bufferLoop err (n + 1) r (buf ++ [x])
    else appendLoop err rest buf
termination_by n => 8 - n

def seqTuple : Src α → Py (Out α)
  | .exactTuple _ => .ok .same
  | .exactList xs => .ok (.fresh xs)
  | .notIterable m => .error (.typeError m)
  | .iter xs err => bufferLoop err 0 xs []

/-- `tuple(v)` is `v` itself for an exact tuple, and otherwise a new tuple of exactly the items the
iterable yields, in order, or the iterator's exception, for every number of items (below, at and
above the eight-item buffer). -/
def SeqTupleSpec : Prop :=
  ∀ (α : Type) (xs : List α) (err : Option PyExc),
    seqTuple (.iter xs err) = (match err with | some e => .error e | none => .ok (.fresh xs)) ∧
    seqTuple (.exactList xs) = .ok (.fresh xs) ∧ seqTuple (.exactTuple xs) = (.ok .same : Py (Out α))

theorem appendLoop_spec (err : Option PyExc) (rest acc : List α) :
    appendLoop err rest acc = (match err with | some e => .error e | none => .ok (.fresh (acc ++ rest))) := by
  induction rest generalizing acc with
  | nil => cases err <;> simp [appendLoop]
  | cons x r ih => simp [appendLoop, ih, List.append_assoc]

theorem bufferLoop_spec (err : Option PyExc) (n : Nat) (rest buf : List α) :
    bufferLoop err n rest buf = (match err with | some e => .error e | none => .ok (.fresh (buf ++ rest))) := by
  induction rest generalizing n buf with
  | nil =>
    unfold bufferLoop
    split
    · cases err <;> simp
    · rw [appendLoop_spec]
  | cons x r ih =>
    unfold bufferLoop
    split
    · simp only []; rw [ih]; simp [List.append_assoc]
    · rw [appendLoop_spec]

theorem seqTupleSpec_proven : SeqTupleSpec := by
  intro α xs err
  refine ⟨?_, rfl, rfl⟩
  simp [seqTuple, bufferLoop_spec]

end PyLean.TypeObj.SeqTuple
