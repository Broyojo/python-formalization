import PyLean.Itertools.ProductSpec
import PyLean.Itertools.Islice

/-!
`__sizeof__` of the combinatoric iterators reports the object plus exactly the
index arrays its constructor allocated.
-/

namespace PyLean.Itertools

open PyLean

variable {α : Type} [Inhabited α]

theorem combNew_indices (o : Obj α) (r : Int) (s : CombState α) (h : cCombinationsNew o r = .ok s) :
    s.indices.length = s.r := by
  simp only [cCombinationsNew, bind, Except.bind] at h
  cases ha : asSsize r with
  | error e => simp [ha] at h
  | ok v =>
    cases hp : tupleOf o with
    | error e => simp [ha, hp] at h
    | ok pool =>
      simp only [ha, hp] at h
      by_cases h0 : v < 0
      · simp [h0, throw, throwThe, MonadExceptOf.throw, Except.bind] at h
      · by_cases hm : memNewOk v = true
        · simp [h0, hm, pure, Except.pure] at h
          subst h
          simp
        · simp [h0, hm, throw, throwThe, MonadExceptOf.throw] at h

theorem cwrNew_indices (o : Obj α) (r : Int) (s : CombState α) (h : cCwrNew o r = .ok s) :
    s.indices.length = s.r := by
  simp only [cCwrNew, bind, Except.bind] at h
  cases ha : asSsize r with
  | error e => simp [ha] at h
  | ok v =>
    cases hp : tupleOf o with
    | error e => simp [ha, hp] at h
    | ok pool =>
      simp only [ha, hp] at h
      by_cases h0 : v < 0
      · simp [h0, throw, throwThe, MonadExceptOf.throw, Except.bind] at h
      · by_cases hm : memNewOk v = true
        · simp [h0, hm, pure, Except.pure] at h
          subst h
          simp
        · simp [h0, hm, throw, throwThe, MonadExceptOf.throw] at h

theorem permNew_arrays (o : Obj α) (robj : Option Int) (s : PermState α)
    (h : cPermutationsNew o robj = .ok s) :
    s.indices.length = s.pool.length ∧ s.cycles.length = s.r := by
  simp only [cPermutationsNew, bind, Except.bind] at h
  cases hp : tupleOf o with
  | error e => simp [hp] at h
  | ok pool =>
    simp only [hp] at h
    have key : ∀ v : Int, (if v < 0 then (throw (.valueError "r must be non-negative") : Py PUnit)
        else pure PUnit.unit) = (if v < 0 then .error (.valueError "r must be non-negative") else .ok PUnit.unit) := by
      intro v; split <;> rfl
    cases robj with
    | none =>
      simp only [pure, Except.pure] at h
      by_cases h0 : (pool.length : Int) < 0
      · omega
      · simp only [h0, ↓reduceIte] at h
        by_cases hm : memNewOk (pool.length : Int) = true
        · simp [hm, pure, Except.pure] at h
          subst h
          simp
        · simp [hm, throw, throwThe, MonadExceptOf.throw] at h
    | some r =>
      cases ha : asSsize r with
      | error e => simp [ha] at h
      | ok v =>
        simp only [ha] at h
        by_cases h0 : v < 0
        · simp [h0, throw, throwThe, MonadExceptOf.throw, Except.bind] at h
        · by_cases hm : (!memNewOk (pool.length : Int) || !memNewOk v) = true
          · simp only [h0, ↓reduceIte, hm] at h
            simp [throw, throwThe, MonadExceptOf.throw, Except.bind] at h
          · simp only [h0, ↓reduceIte, hm] at h
            simp [pure, Except.pure] at h
            subst h
            simp

theorem productNew_lengths (args : List (Obj α)) (rep? : Option Int) (s : ProductState α)
    (h : cProductNew args rep? = .ok s) : s.indices.length = s.pools.length := by
  have fin : ∀ rep : Int, 0 ≤ rep → ∀ ls : List (List α),
      (if rep = 0 then (.ok [] : Py (List (List α))) else args.mapM tupleOf) = .ok ls →
      ((if rep = 0 then (0 : Int) else args.length) * rep).toNat = (prodPools ls rep).length := by
    intro rep h0 ls hls
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    rw [prodPools_length]
    by_cases hz : (m : Int) = 0
    · have hm : m = 0 := by omega
      subst hm
      simp
    · rw [if_neg hz] at hls ⊢
      have hl := mapM_length tupleOf args ls hls
      rw [← Int.natCast_mul, Int.toNat_natCast, hl]
  have rest : ∀ rep : Int, 0 ≤ rep →
      (let nargs : Int := if rep = 0 then 0 else args.length
       if rep ≠ 0 ∧ nargs > ssizeMax / 8 / rep then
        (.error (.overflowError "repeat argument too large") : Py (ProductState α))
       else
        let npools := nargs * rep
        if !memNewOk npools then .error memoryError
        else if !tupleNewOk npools then .error memoryError
        else
          match (if rep = 0 then .ok [] else args.mapM tupleOf) with
          | .error e => .error e
          | .ok ls =>
            .ok { pools := prodPools ls rep, indices := List.replicate npools.toNat 0,
                  started := false, stopped := false }) = .ok s →
      s.indices.length = s.pools.length := by
    intro rep h0 h
    dsimp only at h
    generalize hn : (if rep = 0 then (0 : Int) else (args.length : Int)) = nargs at h
    generalize hq : (if rep = 0 then (.ok [] : Py (List (List α))) else args.mapM tupleOf) = q at h
    cases q with
    | error e =>
      split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · simp at h
    | ok ls =>
      split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · simp only [Except.ok.injEq] at h
            subst h
            have := fin rep h0 ls hq
            rw [hn] at this
            simpa using this
  simp only [cProductNew] at h
  cases rep? with
  | none => exact rest 1 (by omega) h
  | some r =>
    cases ha : asSsize r with
    | error e => simp [ha] at h
    | ok v =>
      simp only [ha] at h
      by_cases h0 : v < 0
      · simp [h0] at h
      · simp only [h0, if_false] at h
        exact rest v (by omega) h

/-- The result of `__sizeof__` on a freshly constructed object is the object's
basic size plus 8 bytes for each element of its index arrays (`indices`, and
`cycles` for `permutations`): what the C code computes from `r` and the pool
sizes is the size of what the constructor allocated. For every input the
constructor accepts; no other hypothesis. -/
def SizeofReportsArrays : Prop :=
  ∀ (α : Type) [Inhabited α] (basic : Nat),
    (∀ (o : Obj α) (r : Int) (s : CombState α), cCombinationsNew o r = .ok s →
      cCombSizeof basic s = basic + s.indices.length * 8) ∧
    (∀ (o : Obj α) (r : Int) (s : CombState α), cCwrNew o r = .ok s →
      cCombSizeof basic s = basic + s.indices.length * 8) ∧
    (∀ (o : Obj α) (robj : Option Int) (s : PermState α), cPermutationsNew o robj = .ok s →
      cPermSizeof basic s = basic + s.indices.length * 8 + s.cycles.length * 8) ∧
    (∀ (args : List (Obj α)) (rep? : Option Int) (s : ProductState α), cProductNew args rep? = .ok s →
      cProductSizeof basic s = basic + s.indices.length * 8)

theorem sizeofReportsArrays_proven : SizeofReportsArrays := by
  intro α _ basic
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro o r s h
    rw [cCombSizeof, combNew_indices o r s h]
  · intro o r s h
    rw [cCombSizeof, cwrNew_indices o r s h]
  · intro o robj s h
    obtain ⟨h1, h2⟩ := permNew_arrays o robj s h
    rw [cPermSizeof, h1, h2]
  · intro args rep? s h
    rw [cProductSizeof, productNew_lengths args rep? s h]

/-- The checks around the constructors' bodies, for all inputs: `islice`
accepts exactly 2 to 4 positional arguments, and keywords only in a subclass
defining `__init__`; a non-int `r` to `permutations` is rejected, but only after
the iterable was read, so an error from the iterable wins. -/
def ArgChecks : Prop :=
  (∀ (n : Nat) (kw customInit : Bool), cIsliceArity n kw customInit = .ok () ↔
    ((kw = false ∨ customInit = true) ∧ 2 ≤ n ∧ n ≤ 4)) ∧
  (∀ (α : Type) [Inhabited α] (o : Obj α) (r : Option Int) (fuel : Nat),
    (∃ e, tupleOf o = .error e ∧ cPermutationsF fuel o r true = Run.err e) ∨
    (∃ l, tupleOf o = .ok l ∧
      cPermutationsF fuel o r true = Run.err (.typeError "Expected int as r")))

theorem argChecks_proven : ArgChecks := by
  refine ⟨?_, ?_⟩
  · intro n kw customInit
    simp only [cIsliceArity]
    cases kw <;> cases customInit <;> simp only [Bool.true_and, Bool.false_and, Bool.not_true,
      Bool.not_false, Bool.false_eq_true, if_true, if_false] <;>
      (try split) <;> (try split) <;> simp_all <;> omega
  · intro α _ o r fuel
    cases h : tupleOf o with
    | error e => exact Or.inl ⟨e, rfl, by simp [cPermutationsF, cPermutationsNew, h, bind, Except.bind]⟩
    | ok l =>
      exact Or.inr ⟨l, rfl, by
        simp [cPermutationsF, cPermutationsNew, h, bind, Except.bind, throw, throwThe,
          MonadExceptOf.throw]⟩

end PyLean.Itertools
