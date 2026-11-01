import PyLean.CoreLibs.Functools.Model

/-!
Properties of `reduce` and of the cache keys of `lru_cache`.
-/

namespace PyLean.CoreLibs.Functools

open PyLean

/-! ### `reduce` -/

theorem reduceCLoop_some {α : Type} (f : α → α → Py α) : ∀ (v : α) (xs : List α)
    (e : Option PyExc), reduceCLoop f (some v) xs e = reduceLoop f v xs e
  | v, [], none => rfl
  | v, [], some _ => rfl
  | v, x :: xs, e => by
    simp only [reduceCLoop, reduceLoop, bind, Except.bind]
    cases f v x with
    | error _ => rfl
    | ok r => exact reduceCLoop_some f r xs e

/-- `Except`-monadic left fold. -/
def foldlPy {α : Type} (f : α → α → Py α) : α → List α → Py α
  | v, [] => .ok v
  | v, x :: xs => do foldlPy f (← f v x) xs

theorem reduceLoop_fold {α : Type} (f : α → α → Py α) : ∀ (v : α) (xs : List α),
    reduceLoop f v xs none = foldlPy f v xs
  | _, [] => rfl
  | v, x :: xs => by
    simp only [reduceLoop, foldlPy, bind, Except.bind]
    cases f v x with
    | error _ => rfl
    | ok r => exact reduceLoop_fold f r xs

/-- `reduce` in C and in Python agree on every iterable, with or without `initial`, for any
function and any iterator that may raise; both compute the left fold; an empty iterable without
`initial` raises `TypeError`. A non-iterable raises `TypeError` in both, with different messages.
Docstring of `reduce`. -/
def ReduceTwins : Prop :=
  ∀ (α : Type) (f : α → α → Py α) (xs : List α) (e : Option PyExc) (i : Option α),
    reduceC f (.iter xs e) i = reducePy f (.iter xs e) i ∧
    (∀ v, reduceC f (.iter xs none) (some v) = foldlPy f v xs) ∧
    (∀ x rest, xs = x :: rest → reduceC f (.iter xs none) none = foldlPy f x rest) ∧
    reduceC f (.iter [] none) none = .error emptyReduce ∧
    (reduceC f .notIterable i).raises "TypeError" ∧ (reducePy f .notIterable i).raises "TypeError"

theorem reduceTwins_proven : ReduceTwins := by
  intro α f xs e i
  refine ⟨?_, ?_, ?_, rfl, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩
  · cases i with
    | some v => exact reduceCLoop_some f v xs e
    | none =>
      cases xs with
      | nil => cases e <;> rfl
      | cons x rest => exact reduceCLoop_some f x rest e
  · intro v
    simp only [reduceC, reduceCLoop_some, reduceLoop_fold]
  · intro x rest h
    subst h
    simp only [reduceC, reduceCLoop, reduceCLoop_some, reduceLoop_fold]

/-- `reduce` with an `iter()` that raises: Python passes on what `__iter__` raised. C does too, for anything that is not a
`TypeError`. -/
def ReduceIterRaises : Prop :=
  ∀ (α : Type) (f : α → α → Py α) (e : PyExc) (t : Bool) (i : Option α),
    reducePy f (.iterRaises e t) i = .error e ∧ (t = false → reduceC f (.iterRaises e t) i = .error e)

theorem reduceIterRaises_proven : ReduceIterRaises := by
  intro α f e t i
  refine ⟨rfl, ?_⟩
  intro h
  subst h
  rfl

/-- `reduce` in C raises what `__iter__` raises. False: a `TypeError`, a subclass too, is replaced by "reduce() arg 2 must
support iteration", so an error inside a user's `__iter__` is reported as a wrong argument. -/
def ReduceCKeepsIterError : Prop :=
  ∀ (α : Type) (f : α → α → Py α) (e : PyExc) (t : Bool) (i : Option α), reduceC f (.iterRaises e t) i = .error e

theorem reduceCKeepsIterError_refuted : ¬ReduceCKeepsIterError := by
  intro h
  have := h Nat (fun a _ => .ok a) (.typeError "mine") true none
  simp [reduceC] at this

/-- `_make_key` and `lru_cache_make_key` build the same key, for every positional and keyword
arguments, `typed` or not, including the single fast argument, as long as hashing the type of the argument does not
raise, for which see `MakeKeyHashesType`. The key is what decides hits, so this is the twin's agreement on cache
identity. -/
def MakeKeyTwins : Prop :=
  ∀ (α : Type) (O : MkKeyOps α) (args : List α) (kwds : List (String × α)) (typed : Bool),
    makeKeyPy O args kwds typed = makeKeyC O args kwds typed

theorem makeKeyTwins_proven : MakeKeyTwins := by
  intro α O args kwds typed
  cases typed with
  | true =>
    cases kwds <;> simp [makeKeyPy, makeKeyC]
  | false =>
    cases kwds with
    | cons p ps =>
      simp [makeKeyPy, makeKeyC]
      split
      · next a heq =>
        have := congrArg List.length heq
        simp at this
        omega
      · rfl
    | nil =>
      match args with
      | [] => simp [makeKeyPy, makeKeyC]
      | [a] => simp [makeKeyPy, makeKeyC]
      | a :: b :: rest => simp [makeKeyPy, makeKeyC]

/-- The whole of `_make_key` agrees with C. False: `type(key[0]) in fasttypes` hashes the type, so an instance of a class
whose metaclass defines `__eq__` without `__hash__` is a `TypeError` in Python, as the only argument of an untyped cache,
where C tests the exact type and gets on. -/
def MakeKeyHashesType : Prop :=
  ∀ (α : Type) (O : MkKeyOps α) (h : α → Py Unit) (args : List α) (kwds : List (String × α)) (t : Bool),
    makeKeyPyFull O h (.ok t) args kwds = .ok (makeKeyC O args kwds t)

theorem makeKeyHashesType_refuted : ¬MakeKeyHashesType := by
  intro h
  have := h Nat ⟨fun _ => false, fun _ => 0⟩ (fun _ => .error (.typeError "unhashable")) [1] [] false
  simp [makeKeyPyFull] at this

/-- The narrowed statement: with a type that hashes, the full `_make_key` is the key of C; and a truth test on `typed` that
raises comes out on the call in Python, where C has done it when the cache was made. -/
def MakeKeyFullTwins : Prop :=
  ∀ (α : Type) (O : MkKeyOps α) (h : α → Py Unit) (args : List α) (kwds : List (String × α)) (t : Bool) (e : PyExc),
    (∀ a, h a = .ok ()) → makeKeyPyFull O h (.ok t) args kwds = .ok (makeKeyC O args kwds t) ∧
    makeKeyPyFull O h (.error e) args kwds = .error e

theorem makeKeyFullTwins_proven : MakeKeyFullTwins := by
  intro α O h args kwds t e hh
  refine ⟨?_, rfl⟩
  rw [← makeKeyTwins_proven α O args kwds t]
  cases t with
  | true => rfl
  | false =>
    match args, kwds with
    | [], _ => rfl
    | [a], [] => simp [makeKeyPyFull, hh]
    | [_], _ :: _ => rfl
    | _ :: _ :: _, _ => rfl

end PyLean.CoreLibs.Functools
