import PyLean.ListSort.Model
import PyLean.BytesObj.Seq.AllocProps
import PyLean.BytesObj.Seq.SearchProps
import PyLean.BytesObj.Seq.SortAux

/-!
The remaining `tuple` and `list` properties: sharing and contents of the constructive
operations, GC tracking, the C API against the Python-level operations, the `sort`
helpers, and the three behaviours that do not hold as one might expect (`*_refuted`).
-/

namespace PyLean.BytesObj.Seq

open PyLean

variable {α ρ : Type}

/-- The longest possible tuple: `tuple_alloc` refuses anything longer. -/
def tupleLimit : Int := (ssizeMax - tupleBase) / 8

theorem tupleAlloc_ok (n : Int) (h0 : 0 ≤ n) (h1 : n ≤ tupleLimit) : tupleAlloc n = .ok () := by
  unfold tupleAlloc
  rw [if_neg (by omega), if_neg (by unfold tupleLimit at h1; omega)]

theorem tupleAlloc_neg (n : Int) (h : n < 0) : tupleAlloc n = .error systemError := by
  unfold tupleAlloc
  rw [if_pos h]

theorem tupleAlloc_big (n : Int) (h0 : 0 ≤ n) (h1 : n > tupleLimit) : tupleAlloc n = .error memoryError := by
  unfold tupleAlloc
  rw [if_neg (by omega), if_pos (by unfold tupleLimit at h1; omega)]

/-- `a + b` on tuples, for every tuple pair that fits: the items are `a` then `b`, and
the two sharing shortcuts of `tuple_concat` (`() + t is t` for an exact `t`, `t + ()
is t` for an exact `t`) return an argument rather than a copy. Anything but a tuple
on the right raises `TypeError` with the source's message. -/
def TupleConcatSpec : Prop :=
  ∀ (α : Type) (a b : Tup α), ((a.items.length + b.items.length : Nat) : Int) ≤ tupleLimit →
    (∃ r, tupleConcat a (.tuple b) = .ok r ∧ r.items a.items b.items = a.items ++ b.items ∧
      (a.items = [] → b.exact = true → r = .arg 1) ∧
      (b.items = [] → a.exact = true → (a.items ≠ [] ∨ b.exact = false) → r = .arg 0)) ∧
    (∀ name, tupleConcat a (.other name) =
      .error (.typeError s!"can only concatenate tuple (not \"{trunc200 name}\") to tuple"))

theorem tupleConcatSpec_proven : TupleConcatSpec := by
  intro α a b hlim
  refine ⟨?_, ?_⟩
  · by_cases h1 : a.items.length = 0 ∧ b.exact = true
    · have ha : a.items = [] := List.length_eq_zero_iff.mp h1.1
      refine ⟨.arg 1, ?_, by simp [TRes.items, ha], fun _ _ => rfl, ?_⟩
      · simp [tupleConcat, h1.1, h1.2]
      · intro hb _ hor
        rcases hor with h | h
        · exact absurd ha h
        · simp [h1.2] at h
    · by_cases h2 : b.items.length = 0 ∧ a.exact = true
      · have hb : b.items = [] := List.length_eq_zero_iff.mp h2.1
        refine ⟨.arg 0, ?_, by simp [TRes.items, hb], ?_, fun _ _ _ => rfl⟩
        · simp only [tupleConcat]
          rw [if_neg h1, if_pos h2]
        · intro ha he
          exact absurd ⟨by simp [ha], he⟩ h1
      · by_cases h3 : (a.items.length : Int) + b.items.length = 0
        · have ha : a.items = [] := List.length_eq_zero_iff.mp (by omega)
          have hb : b.items = [] := List.length_eq_zero_iff.mp (by omega)
          refine ⟨.empty, ?_, by simp [TRes.items, ha, hb], ?_, ?_⟩
          · simp only [tupleConcat]
            rw [if_neg h1, if_neg h2, if_pos h3]
          · intro _ he
            exact absurd ⟨by simp [ha], he⟩ h1
          · intro _ he
            exact absurd ⟨by simp [hb], he⟩ h2
        · have hal := tupleAlloc_ok ((a.items.length : Int) + b.items.length) (by omega) (by omega)
          refine ⟨.fresh { items := a.items ++ b.items, tracked := true }, ?_, rfl, ?_, ?_⟩
          · simp only [tupleConcat]
            rw [if_neg h1, if_neg h2, if_neg h3, hal]
          · intro ha he
            exact absurd ⟨by simp [ha], he⟩ h1
          · intro hb he
            exact absurd ⟨by simp [hb], he⟩ h2
  · intro name
    simp [tupleConcat]

/-- `t * n` and `l * n`, for every int count that fits `Py_ssize_t`: the sharing cases,
the empty cases, the repeated items, and `MemoryError` exactly when the result is too
long to allocate. The tuple and list limits differ by the object header. -/
def RepeatSpec : Prop :=
  ∀ (α : Type) (a : Tup α) (n : Int),
    let size : Int := a.items.length
    (((size = 0 ∨ n = 1) ∧ a.exact = true) → tupleRepeat a n = .ok (.arg 0)) ∧
    (¬ ((size = 0 ∨ n = 1) ∧ a.exact = true) → (size = 0 ∨ n ≤ 0) → tupleRepeat a n = .ok .empty) ∧
    (¬ ((size = 0 ∨ n = 1) ∧ a.exact = true) → 0 < size → 0 < n → size * n > tupleLimit →
      tupleRepeat a n = .error memoryError) ∧
    (¬ ((size = 0 ∨ n = 1) ∧ a.exact = true) → 0 < size → 0 < n → size * n ≤ tupleLimit →
      tupleRepeat a n = .ok (.fresh { items := (List.replicate n.toNat a.items).flatten, tracked := true })) ∧
    ((size = 0 ∨ n ≤ 0) → listRepeat a.items n = .ok LObj.empty) ∧
    (0 < size → 0 < n → size * n > ssizeMax / 8 → listRepeat a.items n = .error memoryError) ∧
    (0 < size → 0 < n → size * n ≤ ssizeMax / 8 →
      listRepeat a.items n = .ok (LObj.prealloc (List.replicate n.toNat a.items).flatten))

theorem mul_le_of_div {size n limit : Int} (hn : 0 < n) (h : size * n ≤ limit) (hl : limit ≤ ssizeMax) :
    ¬ size > ssizeMax / n := by
  have : size ≤ ssizeMax / n := Int.le_ediv_of_mul_le hn (by omega)
  omega

theorem repeatSpec_proven : RepeatSpec := by
  intro α a n size
  have hlimit : tupleLimit ≤ ssizeMax := by decide
  have hlist : ssizeMax / 8 ≤ ssizeMax := by decide
  have hnn : 0 ≤ size := by simp only [size]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    unfold tupleRepeat
    rw [if_pos h]
  · intro h1 h2
    unfold tupleRepeat
    rw [if_neg h1, if_pos h2]
  · intro h1 h2 h3 h4
    unfold tupleRepeat
    rw [if_neg h1, if_neg (by omega)]
    by_cases hd : size > ssizeMax / n
    · rw [if_pos hd]
    · rw [if_neg hd, tupleAlloc_big _ (Int.mul_nonneg hnn (by omega)) h4]
  · intro h1 h2 h3 h4
    unfold tupleRepeat
    rw [if_neg h1, if_neg (by omega), if_neg (mul_le_of_div h3 h4 hlimit),
      tupleAlloc_ok _ (Int.mul_nonneg hnn (by omega)) h4]
  · intro h
    unfold listRepeat
    rw [if_pos h]
  · intro h1 h2 h3
    unfold listRepeat
    rw [if_neg (by omega)]
    by_cases hd : size > ssizeMax / n
    · rw [if_pos hd]
    · rw [if_neg hd, if_pos h3]
  · intro h1 h2 h3
    unfold listRepeat
    rw [if_neg (by omega), if_neg (mul_le_of_div h2 h3 hlist), if_neg (Int.not_lt.mpr h3)]

/-- The construction paths of `tuple` and what they decide about GC tracking, which
`gc.is_tracked` shows. `_PyTuple_FromArray` and `PyTuple_Pack` track a tuple only if
some item may be tracked; `_PyTuple_FromArraySteal` always tracks; `_PyTuple_MaybeUntrack`
untracks an exact tracked tuple exactly when no item may be tracked and none is `NULL`;
`tuple(t) is t` for an exact tuple; `tuple()` is the singleton; `tuple_subtype_new`
gives a tracked subclass instance with an empty hash cache; the argument checks of
`tuple_vectorcall` run keywords first. `len <= tupleLimit` is the type invariant. -/
def TupleConstruct : Prop :=
  ∀ (α : Type) (mt mb : α → Bool) (l : List α) (t : Tup α) (exact tracked : Bool)
    (items : List (Option α)) (n : Nat),
    l ≠ [] → (l.length : Int) ≤ tupleLimit →
    tupleFromArray mt l = .ok (.fresh { items := l, tracked := l.any mt }) ∧
    tupleFromStackRef mt l = .ok (.fresh { items := l, tracked := l.any mt }) ∧
    tupleFromArraySteal l = .ok (.fresh { items := l, tracked := true }) ∧
    tuplePack mt l.length l = .ok (.fresh { items := l, tracked := l.any mt }) ∧
    tupleFromArray mt ([] : List α) = .ok .empty ∧
    tuplePack mt 0 l = .ok .empty ∧
    (tupleMaybeUntrack mb exact tracked items = false ↔
      (exact = true ∧ tracked = true ∧
        ∀ e ∈ items, ∃ x, e = some x ∧ mb x = false) ∨ tracked = false) ∧
    tupleNew mt (none : Option (TupleSrc α)) = .ok .empty ∧
    tupleNew mt (some (.exactTuple t)) = .ok (.arg 0) ∧
    tupleNew mt (some (.exactList l)) = tupleFromArray mt l ∧
    tupleNew mt (some (.iterable l)) = tupleFromArraySteal l ∧
    (∃ o, tupleSubtypeNew mt (some (.iterable l)) = .ok o ∧
      o.items = l ∧ o.exact = false ∧ o.tracked = true ∧ o.hash = -1) ∧
    tupleVectorcall mt ([] : List (TupleSrc α)) 0 = .ok .empty ∧
    tupleVectorcall mt [TupleSrc.iterable l] (n + 1) =
      .error (.typeError "tuple() takes no keyword arguments") ∧
    (t.exact = true → tupleGetnewargs mt t = .ok (.arg 0))

theorem tupleConstruct_proven : TupleConstruct := by
  intro α mt mb l t exact tracked items n hne hlim
  have h0 : l.length ≠ 0 := by
    intro h
    exact hne (List.length_eq_zero_iff.mp h)
  have hal := tupleAlloc_ok (l.length : Int) (by omega) hlim
  have hint : (l.length : Int) ≠ 0 := by omega
  have hfrom : tupleFromArray mt l = .ok (.fresh { items := l, tracked := l.any mt }) := by
    unfold tupleFromArray
    rw [if_neg h0, hal]
  have hsteal : tupleFromArraySteal l = .ok (.fresh { items := l, tracked := true }) := by
    unfold tupleFromArraySteal
    rw [if_neg h0, hal]
  refine ⟨hfrom, hfrom, hsteal, ?_, by simp [tupleFromArray], by simp [tuplePack], ?_, rfl, rfl,
    rfl, rfl, ?_, rfl, ?_, ?_⟩
  · unfold tuplePack
    rw [if_neg hint, hal]
  · unfold tupleMaybeUntrack
    cases hexact : exact <;> cases htracked : tracked <;> simp
    constructor
    · intro h e he
      have := h e he
      cases e with
      | none => simp at this
      | some x => simpa using this
    · intro h e he
      cases e with
      | none => simpa using h none he
      | some x => simpa using h (some x) he
  · refine ⟨{ items := l, exact := false, tracked := true, hash := -1 }, ?_, rfl, rfl, rfl, rfl⟩
    unfold tupleSubtypeNew
    simp only [tupleNew, pySequenceTuple, hsteal]
    rfl
  · simp [tupleVectorcall]
  · intro he
    unfold tupleGetnewargs tupleSlice
    have h1 : ¬ (0 : Int) < 0 := by omega
    have h2 : ¬ ((t.items.length : Int) > t.items.length) := by omega
    have h3 : ¬ ((t.items.length : Int) < 0) := by omega
    simp only [h1, h2, h3, if_false]
    rw [if_pos ⟨trivial, trivial, he⟩]

/-- `_PyTuple_FromPair` is `PyTuple_Pack(2, ...)`, which it replaced in `list_extend_dictitems`, GC
flag included. -/
def TupleFromPairIsPack : Prop :=
  ∀ (α : Type) (mt : α → Bool) (a b : α), tupleFromPair mt a b = tuplePack mt 2 [a, b]

theorem tupleFromPairIsPack_proven : TupleFromPairIsPack := by
  intro α mt a b
  simp [tupleFromPair, tuplePack]

end PyLean.BytesObj.Seq
