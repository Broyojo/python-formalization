import PyLean.Itertools.CombProps

/-!
What the combinatoric index machines enumerate: an explicit list of index
tuples, which gives the documented counts, lexicographic order and "no
repeats" (`Doc/library/itertools.rst`, "Elements are treated as unique based
on their position"). Tuples of positions are compared, so the statements hold
for every pool, sorted or not.
-/

namespace PyLean.Itertools

open PyLean

variable {α : Type} [Inhabited α]

/-! ## Iterating a partial step function -/

/-- From `a`, the step function goes through exactly the states `L` and arrives at `z`. -/
inductive Walk {σ : Type} (step : σ → Option σ) : σ → List σ → σ → Prop
  | nil (a : σ) : Walk step a [] a
  | cons {a b : σ} {L : List σ} {z : σ} : step a = some b → Walk step b L z → Walk step a (a :: L) z

/-- From `a`, the step function goes through exactly the states `L` and then stops. -/
inductive RunTo {σ : Type} (step : σ → Option σ) : σ → List σ → Prop
  | last {a : σ} : step a = none → RunTo step a [a]
  | cons {a b : σ} {L : List σ} : step a = some b → RunTo step b L → RunTo step a (a :: L)

theorem Walk.append_run {σ : Type} {step : σ → Option σ} {a z : σ} {L R : List σ}
    (h : Walk step a L z) (hr : RunTo step z R) : RunTo step a (L ++ R) := by
  induction h with
  | nil => exact hr
  | cons hs _ ih => exact RunTo.cons hs (ih hr)

theorem RunTo.head {σ : Type} {step : σ → Option σ} {a : σ} {L : List σ} (h : RunTo step a L) :
    ∃ t, L = a :: t := by
  cases h with
  | last _ => exact ⟨[], rfl⟩
  | cons _ _ => exact ⟨_, rfl⟩

/-- A run of `step` embeds in a run of `step'` under `f`, ending at `z`. -/
theorem RunTo.lift_walk {σ β : Type} {step : σ → Option σ} {step' : β → Option β} (f : σ → β)
    (P : σ → Prop) (z : β)
    (hs : ∀ x y, P x → step x = some y → P y ∧ step' (f x) = some (f y))
    (ht : ∀ x, P x → step x = none → step' (f x) = some z) {a : σ} {L : List σ}
    (h : RunTo step a L) (hP : P a) : Walk step' (f a) (L.map f) z := by
  induction h with
  | last h0 => exact Walk.cons (ht _ hP h0) (Walk.nil z)
  | cons h1 _ ih =>
    have := hs _ _ hP h1
    exact Walk.cons this.2 (ih this.1)

/-- A run of `step` embeds in a run of `step'` under `f`, stopping with it. -/
theorem RunTo.lift_run {σ β : Type} {step : σ → Option σ} {step' : β → Option β} (f : σ → β)
    (P : σ → Prop)
    (hs : ∀ x y, P x → step x = some y → P y ∧ step' (f x) = some (f y))
    (ht : ∀ x, P x → step x = none → step' (f x) = none) {a : σ} {L : List σ}
    (h : RunTo step a L) (hP : P a) : RunTo step' (f a) (L.map f) := by
  induction h with
  | last h0 => exact RunTo.last (ht _ hP h0)
  | cons h1 _ ih =>
    have := hs _ _ hP h1
    exact RunTo.cons this.2 (ih this.1)

/-! ## Lexicographic order on index tuples -/

/-- `<` on equal-length tuples of ints, as Python compares them. -/
def LexLt : List Nat → List Nat → Prop
  | a :: as, b :: bs => a < b ∨ (a = b ∧ LexLt as bs)
  | _, _ => False

theorem pairwise_lex_cons (k : Nat) (L : List (List Nat)) (h : L.Pairwise LexLt) :
    (L.map (k :: ·)).Pairwise LexLt := by
  rw [List.pairwise_map]
  exact h.imp (fun hab => Or.inr ⟨rfl, hab⟩)

/-! ## combinations -/

/-- The positions `combinations` visits: strictly increasing `r`-tuples from
the `s` positions starting at `k`, in lexicographic order. -/
def cp : Nat → Nat → Nat → List (List Nat)
  | _, 0, _ => [[]]
  | 0, _ + 1, _ => []
  | s + 1, r + 1, k => (cp s r (k + 1)).map (k :: ·) ++ cp s (r + 1) (k + 1)

theorem cp_length : ∀ s r k, (cp s r k).length = choose s r
  | _, 0, _ => by cases ‹Nat› <;> simp [cp, choose]
  | 0, r + 1, _ => by simp [cp, choose]
  | s + 1, r + 1, k => by
    simp [cp, choose, cp_length s r (k + 1), cp_length s (r + 1) (k + 1)]

theorem cp_empty : ∀ s r k, s < r → cp s r k = []
  | 0, r + 1, _, _ => by simp [cp]
  | s + 1, r + 1, k, h => by
    simp only [cp]
    rw [cp_empty s r (k + 1) (by omega), cp_empty s (r + 1) (k + 1) (by omega)]
    rfl

/-- The tuple is strictly increasing, lies in `[k, k + s)` and has length `r`. -/
def IncIn (k s r : Nat) (x : List Nat) : Prop :=
  x.length = r ∧ x.Pairwise (· < ·) ∧ ∀ v ∈ x, k ≤ v ∧ v < k + s

theorem cp_valid : ∀ s r k x, x ∈ cp s r k → IncIn k s r x
  | _, 0, _, x, h => by
    cases ‹Nat› <;> simp [cp] at h <;> subst h <;> simp [IncIn]
  | 0, r + 1, _, x, h => by simp [cp] at h
  | s + 1, r + 1, k, x, h => by
    simp only [cp, List.mem_append, List.mem_map] at h
    rcases h with ⟨y, hy, rfl⟩ | h
    · obtain ⟨h1, h2, h3⟩ := cp_valid s r (k + 1) y hy
      refine ⟨by simp [h1], ?_, ?_⟩
      · exact List.pairwise_cons.2 ⟨fun v hv => by have := h3 v hv; omega, h2⟩
      · intro v hv
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · omega
        · have := h3 v hv; omega
    · obtain ⟨h1, h2, h3⟩ := cp_valid s (r + 1) (k + 1) x h
      exact ⟨h1, h2, fun v hv => by have := h3 v hv; omega⟩

theorem cp_sorted : ∀ s r k, (cp s r k).Pairwise LexLt
  | _, 0, _ => by cases ‹Nat› <;> simp [cp]
  | 0, r + 1, _ => by simp [cp]
  | s + 1, r + 1, k => by
    simp only [cp]
    refine List.pairwise_append.2 ⟨pairwise_lex_cons k _ (cp_sorted s r (k + 1)),
      cp_sorted s (r + 1) (k + 1), ?_⟩
    intro a ha b hb
    simp only [List.mem_map] at ha
    obtain ⟨y, _, rfl⟩ := ha
    obtain ⟨h1, _, h3⟩ := cp_valid s (r + 1) (k + 1) b hb
    cases b with
    | nil => simp at h1
    | cons c cs =>
      have := h3 c (by simp)
      exact Or.inl (by omega)

/-- One step of the C index machine, without the result tuple. -/
def combStep (n r : Nat) (idx : List Nat) : Option (List Nat) :=
  match cCombScan n r idx r with
  | none => none
  | some i => some (cCombFill (i + 1) (r - (i + 1)) (idx.set i (ix idx i + 1)))

theorem combScan_cons (n r a : Nat) (t : List Nat) : ∀ k,
    cCombScan n (r + 1) (a :: t) (k + 1) =
      match cCombScan n r t k with
      | some i => some (i + 1)
      | none => cCombScan n (r + 1) (a :: t) 1
  | 0 => rfl
  | k + 1 => by
    have ih := combScan_cons n r a t k
    have hx : ix (a :: t) (k + 1) = ix t k := by simp [ix]
    have hb : k + 1 + n - (r + 1) = k + n - r := by omega
    rw [cCombScan, hx, hb]
    simp only [cCombScan]
    by_cases h : ix t k = k + n - r
    · simp only [h, ↓reduceIte]; exact ih
    · simp [h]

theorem combFill_length : ∀ (k j : Nat) (idx : List Nat), (cCombFill j k idx).length = idx.length
  | 0, _, _ => rfl
  | k + 1, j, idx => by simp only [cCombFill]; rw [combFill_length k (j + 1)]; simp

theorem combFill_cons : ∀ (k j a : Nat) (t : List Nat), 1 ≤ j →
    cCombFill (j + 1) k (a :: t) = a :: cCombFill j k t
  | 0, _, _, _, _ => rfl
  | k + 1, j, a, t, hj => by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simp only [cCombFill, Nat.add_sub_cancel, List.set_cons_succ]
    rw [show ix (a :: t) (i + 1) = ix t i by simp [ix]]
    exact combFill_cons k (i + 1 + 1) a _ (by omega)

/-- The refill loop writes consecutive values. -/
theorem combFill_range : ∀ (k j : Nat) (idx : List Nat), 1 ≤ j → j + k = idx.length →
    cCombFill j k idx = idx.take j ++ List.range' (ix idx (j - 1) + 1) k
  | 0, j, idx, _, h => by
    obtain rfl : j = idx.length := by omega
    simp [cCombFill]
  | k + 1, j, idx, hj, h => by
    simp only [cCombFill]
    have hl : (idx.set j (ix idx (j - 1) + 1)).length = idx.length := by simp
    rw [combFill_range k (j + 1) _ (by omega) (by omega)]
    rw [List.set_eq_take_append_cons_drop, if_pos (by omega)]
    have htl : (idx.take j).length = j := by simp; omega
    have h1 : ix (idx.take j ++ (ix idx (j - 1) + 1) :: idx.drop (j + 1)) (j + 1 - 1) = ix idx (j - 1) + 1 := by
      simp [ix, List.getD_eq_getElem?_getD, List.getElem?_append_right, htl]
    rw [h1, List.take_append, htl, List.take_of_length_le (by omega), show j + 1 - j = 1 by omega]
    simp [List.range'_succ]

theorem combStep_tail (n r a : Nat) (t t' : List Nat) (hl : t.length = r)
    (h : combStep n r t = some t') : combStep n (r + 1) (a :: t) = some (a :: t') := by
  simp only [combStep] at h ⊢
  cases hs : cCombScan n r t r with
  | none => simp [hs] at h
  | some i =>
    simp only [hs, Option.some.injEq] at h
    subst h
    rw [combScan_cons, hs]
    simp only [List.set_cons_succ]
    rw [show ix (a :: t) (i + 1) = ix t i by simp [ix],
      show r + 1 - (i + 1 + 1) = r - (i + 1) by omega]
    rw [combFill_cons _ _ _ _ (by omega)]

theorem combStep_carry (n r a : Nat) (t : List Nat) (hl : t.length = r) (ha : a + r + 1 < n)
    (h : combStep n r t = none) :
    combStep n (r + 1) (a :: t) = some ((a + 1) :: List.range' (a + 2) r) := by
  simp only [combStep] at h ⊢
  have hs : cCombScan n r t r = none := by
    cases hs : cCombScan n r t r with
    | none => rfl
    | some i => simp [hs] at h
  rw [combScan_cons, hs]
  have hne : ¬ a = 0 + n - (r + 1) := by omega
  simp only [cCombScan, ix, List.getD_cons_zero, hne, ↓reduceIte, List.set_cons_zero]
  rw [combFill_range _ _ _ (by omega) (by simp; omega)]
  simp [ix]

theorem combStep_stop (n r a : Nat) (t : List Nat) (ha : a + r + 1 = n)
    (h : combStep n r t = none) : combStep n (r + 1) (a :: t) = none := by
  simp only [combStep] at h ⊢
  have hs : cCombScan n r t r = none := by
    cases hs : cCombScan n r t r with
    | none => rfl
    | some i => simp [hs] at h
  rw [combScan_cons, hs]
  have hc : cCombScan n (r + 1) (a :: t) 1 = none := by
    simp only [cCombScan, ix, List.getD_cons_zero]
    rw [if_pos (by omega)]
  simp only [hc]

theorem combStep_length (n r : Nat) (t t' : List Nat) (h : combStep n r t = some t') :
    t'.length = t.length := by
  simp only [combStep] at h
  cases hs : cCombScan n r t r with
  | none => simp [hs] at h
  | some i =>
    simp only [hs, Option.some.injEq] at h
    subst h
    rw [combFill_length]; simp

/-- The C machine, started at `k, k+1, ..., k+r-1`, runs through `cp`. -/
theorem comb_run : ∀ (s r k : Nat), r ≤ s → RunTo (combStep (k + s) r) (List.range' k r) (cp s r k)
  | s, 0, k, _ => by
    have : cp s 0 k = [[]] := by cases s <;> rfl
    rw [this]
    exact RunTo.last (by simp [combStep, cCombScan])
  | 0, r + 1, _, h => by omega
  | s + 1, r + 1, k, h => by
    have hn : k + (s + 1) = k + 1 + s := by omega
    rw [hn]
    simp only [List.range'_succ, cp]
    have ih1 := comb_run s r (k + 1) (by omega)
    have hstep : ∀ x y, x.length = r → combStep (k + 1 + s) r x = some y →
        y.length = r ∧ combStep (k + 1 + s) (r + 1) (k :: x) = some (k :: y) := fun x y hx hy =>
      ⟨by rw [combStep_length _ _ _ _ hy, hx], combStep_tail _ _ _ _ _ hx hy⟩
    by_cases hrs : r < s
    · have hw := RunTo.lift_walk (step := combStep (k + 1 + s) r) (step' := combStep (k + 1 + s) (r + 1))
        (k :: ·) (fun t => t.length = r) ((k + 1) :: List.range' (k + 2) r) hstep
        (fun x hx hn => combStep_carry _ _ _ _ hx (by omega) hn) ih1 (by simp)
      have ih2 := comb_run s (r + 1) (k + 1) (by omega)
      rw [List.range'_succ] at ih2
      exact hw.append_run ih2
    · have hr := RunTo.lift_run (step := combStep (k + 1 + s) r) (step' := combStep (k + 1 + s) (r + 1))
        (k :: ·) (fun t => t.length = r) hstep
        (fun x _ hn => combStep_stop _ _ _ _ (by omega) hn) ih1 (by simp)
      rw [cp_empty s (r + 1) (k + 1) (by omega), List.append_nil]
      exact hr

/-- From a started state, the C iterator drains the tuples of the run. -/
theorem combDrain (pool : List α) (r : Nat) {idx : List Nat} {L : List (List Nat)}
    (h : RunTo (combStep pool.length r) idx L) : ∀ fuel, L.length ≤ fuel →
    drain cCombinationsNext fuel
        { pool := pool, indices := idx, r := r, started := true, stopped := false } =
      Run.ok (L.tail.map (pick pool)) := by
  induction h with
  | @last a h0 =>
    intro fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simp only [combStep] at h0
    rw [drain_succ]
    simp only [cCombinationsNext, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
    cases hs : cCombScan pool.length r a r with
    | none => rfl
    | some i => simp [hs] at h0
  | @cons a b L h1 hr ih =>
    intro fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    obtain ⟨t, rfl⟩ := hr.head
    simp only [combStep] at h1
    rw [drain_succ]
    simp only [cCombinationsNext, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
    cases hs : cCombScan pool.length r a r with
    | none => simp [hs] at h1
    | some i =>
      simp only [hs, Option.some.injEq] at h1
      simp only [h1]
      rw [ih f (by simp at hf ⊢; omega)]
      rfl

/-- For `r >= 0` that can be allocated and enough fuel, `combinations(pool, r)`
yields the tuples at exactly the positions in a list `L` that has
`math.comb(n, r)` elements (zero when `r > n`), is strictly increasing in
lexicographic order (so no repeats), and consists of all-distinct, increasing
`r`-tuples of positions `< n`. Type invariant: the pool tuple is in memory. -/
def CombinationsSpec : Prop :=
  ∀ (α : Type) [Inhabited α] (pool : List α) (r : Int) (fuel : Nat), tupleNewOk pool.length = true → 0 ≤ r →
    memNewOk r = true → tupleNewOk r = true → choose pool.length r.toNat < fuel →
    ∃ L : List (List Nat), cCombinationsF fuel (.iter pool none) r = Run.ok (L.map (pick pool)) ∧
      L.length = choose pool.length r.toNat ∧ L.Pairwise LexLt ∧
      ∀ x ∈ L, IncIn 0 pool.length r.toNat x

theorem choose_gt : ∀ n k, n < k → choose n k = 0
  | 0, k + 1, _ => by simp [choose]
  | n + 1, k + 1, h => by
    simp [choose, choose_gt n k (by omega), choose_gt n (k + 1) (by omega)]

theorem combinationsSpec_proven : CombinationsSpec := by
  intro α _ pool r fuel _ h0 hm ht hf
  have hle := memNewOk_le hm
  have hmin : ssizeMin ≤ r := by rw [ssizeMin_eq]; omega
  have hrn : ((r.toNat : Nat) : Int) = r := Int.toNat_of_nonneg h0
  refine ⟨cp pool.length r.toNat 0, ?_, cp_length _ _ _, cp_sorted _ _ _, fun x hx => cp_valid _ _ _ x hx⟩
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  simp only [cCombinationsF, cCombinationsNew, asSsize_ok hmin hle, tupleOf]
  simp only [bind, Except.bind, show ¬ r < 0 by omega, ↓reduceIte, hm, Bool.not_true,
    Bool.false_eq_true, pure, Except.pure]
  by_cases hn : r > pool.length
  · rw [cp_empty _ _ _ (by omega)]
    rw [drain_succ]
    simp [hn, cCombinationsNext, Run.ok]
  · have hrun := comb_run pool.length r.toNat 0 (by omega)
    simp only [Nat.zero_add] at hrun
    rw [drain_succ]
    simp only [hn, decide_false, cCombinationsNext, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      hrn, ht, Bool.not_true]
    obtain ⟨t, ht'⟩ := hrun.head
    have hd := combDrain pool r.toNat hrun f (by rw [cp_length] at *; omega)
    have hr0 : List.range r.toNat = List.range' 0 r.toNat := by simp [List.range_eq_range']
    rw [hr0, hd, ht']
    rfl

end PyLean.Itertools
