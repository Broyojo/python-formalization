import PyLean.Itertools.CombSpec

/-!
What `combinations_with_replacement` enumerates, with the documented count
`(n + r - 1)! / r! / (n - 1)!` (rst:274-276), i.e. `math.comb(n + r - 1, r)`.
-/

namespace PyLean.Itertools

open PyLean

variable {α : Type} [Inhabited α]

/-- Non-decreasing `r`-tuples from the `s` positions starting at `k`, in
lexicographic order: first the tuples starting with `k`, then the others. -/
def cw : Nat → Nat → Nat → List (List Nat)
  | _, 0, _ => [[]]
  | 0, _ + 1, _ => []
  | s + 1, r + 1, k => (cw (s + 1) r k).map (k :: ·) ++ cw s (r + 1) (k + 1)
termination_by s r => s + r

theorem cw_zero (s k : Nat) : cw s 0 k = [[]] := by cases s <;> simp [cw]
theorem cw_empty (r k : Nat) : cw 0 (r + 1) k = [] := by simp [cw]
theorem cw_succ (s r k : Nat) :
    cw (s + 1) (r + 1) k = (cw (s + 1) r k).map (k :: ·) ++ cw s (r + 1) (k + 1) := by
  rw [cw]

theorem cw_length : ∀ s r k, (cw (s + 1) r k).length = choose (s + r) r
  | s, 0, k => by rw [cw_zero]; cases s <;> simp [choose]
  | 0, r + 1, k => by
    rw [cw_succ, cw_empty]
    have := cw_length 0 r k
    simp only [List.length_append, List.length_map, List.length_nil, Nat.add_zero, this]
    rw [show 0 + (r + 1) = r + 1 from by omega, choose, choose_gt r (r + 1) (by omega)]
    simp
  | s + 1, r + 1, k => by
    rw [cw_succ]
    have h1 := cw_length (s + 1) r k
    have h2 := cw_length s (r + 1) (k + 1)
    simp only [List.length_append, List.length_map, h1, h2]
    rw [show s + 1 + (r + 1) = (s + 1 + r) + 1 from by omega, choose,
      show s + (r + 1) = s + 1 + r from by omega]
termination_by s r => s + r

/-- Non-decreasing, in `[k, k + s)`, of length `r`. -/
def NondecIn (k s r : Nat) (x : List Nat) : Prop :=
  x.length = r ∧ x.Pairwise (· ≤ ·) ∧ ∀ v ∈ x, k ≤ v ∧ v < k + s

theorem cw_valid : ∀ s r k x, x ∈ cw s r k → NondecIn k s r x
  | s, 0, k, x, h => by
    rw [cw_zero] at h; simp at h; subst h; simp [NondecIn]
  | 0, r + 1, k, x, h => by rw [cw_empty] at h; simp at h
  | s + 1, r + 1, k, x, h => by
    rw [cw_succ] at h
    simp only [List.mem_append, List.mem_map] at h
    rcases h with ⟨y, hy, rfl⟩ | h
    · obtain ⟨h1, h2, h3⟩ := cw_valid (s + 1) r k y hy
      refine ⟨by simp [h1], List.pairwise_cons.2 ⟨fun v hv => (h3 v hv).1, h2⟩, ?_⟩
      intro v hv
      simp only [List.mem_cons] at hv
      rcases hv with rfl | hv
      · omega
      · exact h3 v hv
    · obtain ⟨h1, h2, h3⟩ := cw_valid s (r + 1) (k + 1) x h
      exact ⟨h1, h2, fun v hv => by have := h3 v hv; omega⟩
termination_by s r => s + r

theorem cw_sorted : ∀ s r k, (cw s r k).Pairwise LexLt
  | s, 0, k => by rw [cw_zero]; simp
  | 0, r + 1, k => by rw [cw_empty]; simp
  | s + 1, r + 1, k => by
    rw [cw_succ]
    refine List.pairwise_append.2 ⟨pairwise_lex_cons k _ (cw_sorted (s + 1) r k),
      cw_sorted s (r + 1) (k + 1), ?_⟩
    intro a ha b hb
    simp only [List.mem_map] at ha
    obtain ⟨y, _, rfl⟩ := ha
    obtain ⟨h1, _, h3⟩ := cw_valid s (r + 1) (k + 1) b hb
    cases b with
    | nil => simp at h1
    | cons c cs =>
      have := h3 c (by simp)
      exact Or.inl (by omega)
termination_by s r => s + r

/-- One step of the C index machine. -/
def cwrStep (n r : Nat) (idx : List Nat) : Option (List Nat) :=
  match cCwrScan n idx r with
  | none => none
  | some i => some (cCwrFill (ix idx i + 1) i (r - i) idx)

theorem cwrScan_cons (n a : Nat) (t : List Nat) : ∀ k,
    cCwrScan n (a :: t) (k + 1) =
      match cCwrScan n t k with
      | some i => some (i + 1)
      | none => cCwrScan n (a :: t) 1
  | 0 => rfl
  | k + 1 => by
    have ih := cwrScan_cons n a t k
    have hx : ix (a :: t) (k + 1) = ix t k := by simp [ix]
    rw [cCwrScan, hx]
    simp only [cCwrScan]
    by_cases h : ((ix t k : Nat) : Int) = (n : Int) - 1
    · simp only [h, ↓reduceIte]; exact ih
    · simp [h]

theorem cCwrScan_lt (n : Nat) (idx : List Nat) (k i : Nat) (h : cCwrScan n idx k = some i) : i < k :=
  docCwrScan_lt n idx k i (by rw [← cwrScan_eq]; exact h)

theorem cwrStep_tail (n r a : Nat) (t t' : List Nat) (hl : t.length = r)
    (h : cwrStep n r t = some t') : cwrStep n (r + 1) (a :: t) = some (a :: t') := by
  simp only [cwrStep] at h ⊢
  cases hs : cCwrScan n t r with
  | none => simp [hs] at h
  | some i =>
    have hi := cCwrScan_lt _ _ _ _ hs
    simp only [hs, Option.some.injEq] at h
    subst h
    rw [cwrScan_cons, hs]
    simp only [Option.some.injEq]
    rw [show ix (a :: t) (i + 1) = ix t i by simp [ix], show r + 1 - (i + 1) = r - i by omega,
      cwrFill_eq _ _ _ _ (by simp; omega), cwrFill_eq _ _ _ _ (by omega)]
    simp

theorem cwrStep_carry (n r a : Nat) (t : List Nat) (hl : t.length = r) (ha : a + 1 < n)
    (h : cwrStep n r t = none) :
    cwrStep n (r + 1) (a :: t) = some ((a + 1) :: List.replicate r (a + 1)) := by
  simp only [cwrStep] at h ⊢
  have hs : cCwrScan n t r = none := by
    cases hs : cCwrScan n t r with
    | none => rfl
    | some i => simp [hs] at h
  rw [cwrScan_cons, hs]
  have hne : ¬ ((a : Int) = (n : Int) - 1) := by omega
  simp only [cCwrScan, ix, List.getD_cons_zero, hne, ↓reduceIte, Option.some.injEq]
  rw [cwrFill_eq _ _ _ _ (by simp; omega)]
  simp [List.replicate_succ]

theorem cwrStep_stop (n r a : Nat) (t : List Nat) (ha : a + 1 = n)
    (h : cwrStep n r t = none) : cwrStep n (r + 1) (a :: t) = none := by
  simp only [cwrStep] at h ⊢
  have hs : cCwrScan n t r = none := by
    cases hs : cCwrScan n t r with
    | none => rfl
    | some i => simp [hs] at h
  rw [cwrScan_cons, hs]
  have hc : cCwrScan n (a :: t) 1 = none := by
    simp only [cCwrScan, ix, List.getD_cons_zero]
    rw [if_pos (by omega)]
  simp only [hc]

theorem cwrStep_length (n r : Nat) (t t' : List Nat) (h : cwrStep n r t = some t') :
    t'.length = t.length := by
  simp only [cwrStep] at h
  cases hs : cCwrScan n t r with
  | none => simp [hs] at h
  | some i =>
    simp only [hs, Option.some.injEq] at h
    subst h
    rw [cwrFill_length]

/-- The C machine, started at `k, k, ..., k`, runs through `cw`. -/
theorem cwr_run : ∀ (s r k : Nat), RunTo (cwrStep (k + (s + 1)) r) (List.replicate r k) (cw (s + 1) r k)
  | s, 0, k => by
    rw [cw_zero]
    exact RunTo.last (by simp [cwrStep, cCwrScan])
  | 0, r + 1, k => by
    rw [cw_succ, cw_empty, List.append_nil, List.replicate_succ]
    exact RunTo.lift_run (step := cwrStep (k + (0 + 1)) r) (step' := cwrStep (k + (0 + 1)) (r + 1))
      (k :: ·) (fun t => t.length = r)
      (fun x y hx hy => ⟨by rw [cwrStep_length _ _ _ _ hy, hx], cwrStep_tail _ _ _ _ _ hx hy⟩)
      (fun x _ hn => cwrStep_stop _ _ _ _ (by omega) hn) (cwr_run 0 r k) (by simp)
  | s + 1, r + 1, k => by
    rw [cw_succ, List.replicate_succ]
    have hw := RunTo.lift_walk (step := cwrStep (k + (s + 1 + 1)) r)
      (step' := cwrStep (k + (s + 1 + 1)) (r + 1)) (k :: ·) (fun t => t.length = r)
      ((k + 1) :: List.replicate r (k + 1))
      (fun x y hx hy => ⟨by rw [cwrStep_length _ _ _ _ hy, hx], cwrStep_tail _ _ _ _ _ hx hy⟩)
      (fun x hx hn => cwrStep_carry _ _ _ _ hx (by omega) hn) (cwr_run (s + 1) r k) (by simp)
    have ih2 := cwr_run s (r + 1) (k + 1)
    rw [show k + 1 + (s + 1) = k + (s + 1 + 1) from by omega, List.replicate_succ] at ih2
    exact hw.append_run ih2
termination_by s r => s + r

theorem cwrDrain (pool : List α) (r : Nat) {idx : List Nat} {L : List (List Nat)}
    (h : RunTo (cwrStep pool.length r) idx L) : ∀ fuel, L.length ≤ fuel →
    drain cCwrNext fuel
        { pool := pool, indices := idx, r := r, started := true, stopped := false } =
      Run.ok (L.tail.map (pick pool)) := by
  induction h with
  | @last a h0 =>
    intro fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simp only [cwrStep] at h0
    rw [drain_succ]
    simp only [cCwrNext, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
    cases hs : cCwrScan pool.length a r with
    | none => rfl
    | some i => simp [hs] at h0
  | @cons a b L h1 hr ih =>
    intro fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    obtain ⟨t, rfl⟩ := hr.head
    simp only [cwrStep] at h1
    rw [drain_succ]
    simp only [cCwrNext, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
    cases hs : cCwrScan pool.length a r with
    | none => simp [hs] at h1
    | some i =>
      simp only [hs, Option.some.injEq] at h1
      simp only [h1]
      rw [ih f (by simp at hf ⊢; omega)]
      rfl

/-- The documented number of tuples: `(n + r - 1)! / r! / (n - 1)!` for
`n > 0`; for `n = 0` one empty tuple if `r = 0`, else none. -/
def cwrCount (n r : Nat) : Nat :=
  if n = 0 then (if r = 0 then 1 else 0) else choose (n + r - 1) r

/-- For `r >= 0` that can be allocated and enough fuel,
`combinations_with_replacement(pool, r)` yields the tuples at exactly the
positions in a list `L` of `cwrCount n r` non-decreasing `r`-tuples of
positions `< n`, strictly increasing in lexicographic order (so no repeats). -/
def CwrSpec : Prop :=
  ∀ (α : Type) [Inhabited α] (pool : List α) (r : Int) (fuel : Nat), tupleNewOk pool.length = true → 0 ≤ r →
    memNewOk r = true → tupleNewOk r = true → cwrCount pool.length r.toNat < fuel →
    ∃ L : List (List Nat), cCwrF fuel (.iter pool none) r = Run.ok (L.map (pick pool)) ∧
      L.length = cwrCount pool.length r.toNat ∧ L.Pairwise LexLt ∧
      ∀ x ∈ L, NondecIn 0 pool.length r.toNat x

theorem cw_count (n r k : Nat) : (cw n r k).length = cwrCount n r := by
  cases n with
  | zero => cases r <;> simp [cwrCount, cw]
  | succ n =>
    rw [cw_length]
    simp only [cwrCount, Nat.succ_ne_zero, ↓reduceIte]
    rw [show n + 1 + r - 1 = n + r by omega]

theorem cwrSpec_proven : CwrSpec := by
  intro α _ pool r fuel _ h0 hm ht hf
  have hle := memNewOk_le hm
  have hmin : ssizeMin ≤ r := by rw [ssizeMin_eq]; omega
  have hrn : ((r.toNat : Nat) : Int) = r := Int.toNat_of_nonneg h0
  refine ⟨cw pool.length r.toNat 0, ?_, cw_count _ _ _, cw_sorted _ _ _, fun x hx => cw_valid _ _ _ x hx⟩
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  simp only [cCwrF, cCwrNew, asSsize_ok hmin hle, tupleOf]
  simp only [bind, Except.bind, show ¬ r < 0 by omega, ↓reduceIte, hm, Bool.not_true,
    Bool.false_eq_true, pure, Except.pure]
  by_cases hzr : pool.length = 0 ∧ r ≠ 0
  · have hst : (pool.length == 0 && r != 0) = true := by
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne]; exact hzr
    obtain ⟨k, hk⟩ : ∃ k, r.toNat = k + 1 := ⟨r.toNat - 1, by omega⟩
    have hc : cw pool.length r.toNat 0 = [] := by rw [hzr.1, hk, cw_empty]
    rw [hc, drain_succ]
    simp only [hst, cCwrNext, ↓reduceIte]
    rfl
  · have hst : (pool.length == 0 && r != 0) = false := by
      simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq]; omega
    have hrun : RunTo (cwrStep pool.length r.toNat) (List.replicate r.toNat 0)
        (cw pool.length r.toNat 0) := by
      by_cases hz : pool.length = 0
      · have hr0 : r = 0 := by omega
        subst hr0
        rw [hz]
        simp only [Int.toNat_zero, cw_zero, List.replicate_zero]
        exact RunTo.last (by simp [cwrStep, cCwrScan])
      · obtain ⟨n, hn⟩ : ∃ n, pool.length = n + 1 := ⟨pool.length - 1, by omega⟩
        have := cwr_run n r.toNat 0
        simpa [hn] using this
    rw [drain_succ]
    simp only [hst, cCwrNext, Bool.false_eq_true, ↓reduceIte, Bool.not_false, hrn, ht, Bool.not_true]
    obtain ⟨t, ht'⟩ := hrun.head
    have hd := cwrDrain pool r.toNat hrun f (by rw [cw_count]; omega)
    rw [hd, ht']
    rfl

end PyLean.Itertools
