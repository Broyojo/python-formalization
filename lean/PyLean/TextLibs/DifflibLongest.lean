import PyLean.TextLibs.DifflibSound

/-!
The docstring of `find_longest_match`: with no junk, the result is a longest block, the one that starts
earliest in `a`, and of those the one that starts earliest in `b`.
-/

namespace PyLean.TextLibs.Difflib

open PyLean

/-- A match of size at least 1 inside the box, except for its right end in `a`. -/
def Mt (s : SM) (alo blo bhi i j m : Nat) : Prop :=
  1 ≤ m ∧ alo ≤ i ∧ blo ≤ j ∧ j + m ≤ bhi ∧ Eqs s.a s.b i j m

/-- `b` is at least as good as the match `(i, j, m)`. -/
def Dom (b : Best) (i j m : Nat) : Prop :=
  m ≤ b.2.2 ∧ (m = b.2.2 → b.1 < i ∨ (b.1 = i ∧ b.2.1 ≤ j))

/-- `j2len` at row `i` has an entry at least as long as each match that ends there. -/
def RowC (s : SM) (alo blo bhi i : Nat) (m : List (Nat × Nat)) : Prop :=
  ∀ i' j' k, Mt s alo blo bhi i' j' k → i' + k = i → ∃ v, m.lookup (j' + k - 1) = some v ∧ k ≤ v

/-- `best` dominates each match that ends before row `r`. -/
def BestMax (s : SM) (alo blo bhi r : Nat) (b : Best) : Prop :=
  ∀ i' j' m, Mt s alo blo bhi i' j' m → i' + m ≤ r → Dom b i' j' m

def ZeroB (alo blo : Nat) (b : Best) : Prop := b.2.2 = 0 → b.1 = alo ∧ b.2.1 = blo

theorem eqs_prefix {a b : List Nat} {i j k m : Nat} (h : Eqs a b i j k) (hm : m ≤ k) : Eqs a b i j m :=
  ⟨by have := h.1; omega, by have := h.2.1; omega, fun t ht => h.2.2 t (by omega)⟩

/-- The last column of a match that ends at row `i` holds `a[i]`. -/
theorem mt_end {s : SM} {alo blo bhi i i' j' k x : Nat} (h : Mt s alo blo bhi i' j' k) (he : i' + k = i + 1)
    (hi : s.a[i]? = some x) : s.b[j' + k - 1]? = some x := by
  obtain ⟨h1, _, _, _, _, _, h5⟩ := h
  have := h5 (k - 1) (by omega)
  have e1 : i' + (k - 1) = i := by omega
  have e2 : j' + (k - 1) = j' + k - 1 := by omega
  rw [e1, e2, hi] at this
  exact this.symm

theorem step_ok (s : SM) (alo blo bhi i j x : Nat) (old new : List (Nat × Nat)) (best : Best)
    (hi : s.a[i]? = some x) (hj : s.b[j]? = some x) (halo : alo ≤ i) (hb1 : ¬ j < blo) (hb2 : ¬ j ≥ bhi)
    (hbhi : bhi ≤ s.b.length) (hold : RowOk s alo blo bhi i old) (h1 : RowOk s alo blo bhi (i + 1) new)
    (h2 : BestOk s alo blo bhi (i + 1) best) :
    RowOk s alo blo bhi (i + 1) ((j, j2get old j + 1) :: new) ∧
    BestOk s alo blo bhi (i + 1)
      (if j2get old j + 1 > best.2.2 then (i + 1 - (j2get old j + 1), j + 1 - (j2get old j + 1), j2get old j + 1) else best) := by
  have hlen : i < s.a.length := by
    rcases List.getElem?_eq_some_iff.mp hi with ⟨h, _⟩
    exact h
  have hjl : j < s.b.length := by
    rcases List.getElem?_eq_some_iff.mp hj with ⟨h, _⟩
    exact h
  obtain ⟨g1, g2, g3⟩ := j2get_ok s alo blo bhi i j old (by omega) (by omega) halo (by omega) hold
  generalize j2get old j = g at g1 g2 g3 ⊢
  have ext : Eqs s.a s.b (i - g) (j - g) (g + 1) := by
    refine eqs_right g3 ?_ ?_ ?_
    · omega
    · omega
    · have e1 : i - g + g = i := by omega
      have e2 : j - g + g = j := by omega
      rw [e1, e2, hi, hj]
  constructor
  · intro y v hv
    by_cases hy : y = j
    · subst hy
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hv
      subst hv
      refine ⟨by omega, by omega, by omega, by omega, ?_⟩
      have e1 : i + 1 - (g + 1) = i - g := by omega
      have e2 : y + 1 - (g + 1) = y - g := by omega
      rw [e1, e2]
      exact ext
    · have : (y == j) = false := by simpa using hy
      simp only [List.lookup, this] at hv
      exact h1 y v hv
  · split
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only; omega
      · simp only; omega
      · simp only; omega
      · simp only; omega
      · simp only
        have e1 : i + 1 - (g + 1) = i - g := by omega
        have e2 : j + 1 - (g + 1) = j - g := by omega
        rw [e1, e2]
        exact ext
    · exact h2

theorem inner_max (s : SM) (alo blo bhi i x : Nat) (old : List (Nat × Nat)) (hi : s.a[i]? = some x)
    (halo : alo ≤ i) (hbhi : bhi ≤ s.b.length) (hold : RowOk s alo blo bhi i old)
    (hc : RowC s alo blo bhi i old) :
    ∀ (l : List Nat) (new : List (Nat × Nat)) (best : Best) (lim : Nat),
      (∀ j ∈ l, s.b[j]? = some x) → l.Pairwise (· < ·) → (∀ j ∈ l, lim ≤ j) →
      (∀ e, lim ≤ e → s.b[e]? = some x → e ∈ l) →
      RowOk s alo blo bhi (i + 1) new → BestOk s alo blo bhi (i + 1) best → ZeroB alo blo best →
      (∀ i' j' k, Mt s alo blo bhi i' j' k → i' + k = i + 1 → j' + k ≤ lim →
        ∃ v, new.lookup (j' + k - 1) = some v ∧ k ≤ v) →
      (∀ i' j' m, Mt s alo blo bhi i' j' m → (i' + m ≤ i ∨ (i' + m = i + 1 ∧ j' + m ≤ lim)) → Dom best i' j' m) →
      (best.1 + best.2.2 ≤ i ∨ best.2.1 + best.2.2 ≤ lim) →
      RowC s alo blo bhi (i + 1) (innerLoop blo bhi i old l new best).1 ∧
      BestMax s alo blo bhi (i + 1) (innerLoop blo bhi i old l new best).2 ∧
      ZeroB alo blo (innerLoop blo bhi i old l new best).2 := by
  intro l
  induction l with
  | nil =>
    intro new best lim _ _ _ h4 _ _ h7 h8 h9 _
    have cov : ∀ i' j' k, Mt s alo blo bhi i' j' k → i' + k = i + 1 → j' + k ≤ lim := by
      intro i' j' k hm he
      by_cases hc : j' + k ≤ lim
      · exact hc
      · have := h4 (j' + k - 1) (by omega) (mt_end hm he hi)
        simp at this
    refine ⟨fun i' j' k hm he => h8 i' j' k hm he (cov _ _ _ hm he), ?_, h7⟩
    intro i' j' m hm he
    by_cases hr : i' + m ≤ i
    · exact h9 i' j' m hm (.inl hr)
    · exact h9 i' j' m hm (.inr ⟨by omega, cov i' j' m hm (by omega)⟩)
  | cons j r ih =>
    intro new best lim h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    obtain ⟨p1, p2⟩ := List.pairwise_cons.mp h2
    have hj : s.b[j]? = some x := h1 j (by simp)
    have hlimj : lim ≤ j := h3 j (by simp)
    have hr1 : ∀ y ∈ r, s.b[y]? = some x := fun y hy => h1 y (by simp [hy])
    have hr3 : ∀ y ∈ r, j + 1 ≤ y := fun y hy => p1 y hy
    have hr4 : ∀ e, j + 1 ≤ e → s.b[e]? = some x → e ∈ r := by
      intro e he hb
      rcases List.mem_cons.mp (h4 e (by omega) hb) with rfl | hm
      · omega
      · exact hm
    -- matches ending in `[lim, j)` do not exist: all those columns were skipped by no `j` at all
    have hgap : ∀ i' j' k, Mt s alo blo bhi i' j' k → i' + k = i + 1 → j' + k ≤ j → j' + k ≤ lim := by
      intro i' j' k hm he hlt
      by_cases hc' : j' + k ≤ lim
      · exact hc'
      · have := h4 (j' + k - 1) (by omega) (mt_end hm he hi)
        rcases List.mem_cons.mp this with he2 | hm2
        · have := hm.1; omega
        · have := p1 _ hm2; have := hm.1; omega
    simp only [innerLoop]
    split
    · rename_i hb1
      refine ih new best (j + 1) hr1 p2 hr3 hr4 h5 h6 h7 ?_ ?_ ?_
      · intro i' j' k hm he hl
        have := hm.2.2.1; have := hm.1
        omega
      · intro i' j' m hm he
        rcases he with he | ⟨_, hl⟩
        · exact h9 i' j' m hm (.inl he)
        · have := hm.2.2.1; have := hm.1
          omega
      · rcases h10 with h | h
        · exact .inl h
        · exact .inr (by omega)
    · rename_i hb1
      split
      · rename_i hb2
        have cov : ∀ i' j' k, Mt s alo blo bhi i' j' k → i' + k = i + 1 → j' + k ≤ lim := by
          intro i' j' k hm he
          exact hgap i' j' k hm he (by have := hm.2.2.2.1; omega)
        refine ⟨fun i' j' k hm he => h8 i' j' k hm he (cov _ _ _ hm he), ?_, h7⟩
        intro i' j' m hm he
        by_cases hr : i' + m ≤ i
        · exact h9 i' j' m hm (.inl hr)
        · exact h9 i' j' m hm (.inr ⟨by omega, cov i' j' m hm (by omega)⟩)
      · rename_i hb2
        obtain ⟨n1, n2⟩ := step_ok s alo blo bhi i j x old new best hi hj halo hb1 hb2 hbhi hold h5 h6
        -- a match ending at `(i, j)` is no longer than the new entry
        have hup : ∀ i' j' m, Mt s alo blo bhi i' j' m → i' + m = i + 1 → j' + m - 1 = j → m ≤ j2get old j + 1 := by
          intro i' j' m hm he he2
          by_cases hm1 : m = 1
          · omega
          · have hm2 : 2 ≤ m := by have := hm.1; omega
            have hsub : Mt s alo blo bhi i' j' (m - 1) :=
              ⟨by omega, hm.2.1, hm.2.2.1, by have := hm.2.2.2.1; omega, eqs_prefix hm.2.2.2.2 (by omega)⟩
            obtain ⟨v, hv1, hv2⟩ := hc i' j' (m - 1) hsub (by omega)
            have hjpos : j = (j' + (m - 1) - 1) + 1 := by omega
            have : j2get old j = v := by
              rw [hjpos]
              simp only [j2get, hv1, Option.getD_some]
            omega
        generalize hk : j2get old j + 1 = k at n1 n2 hup
        refine ih ((j, k) :: new) _ (j + 1) hr1 p2 hr3 hr4 n1 n2 ?_ ?_ ?_ ?_
        · intro hz
          split at hz
          · simp only at hz; omega
          · rename_i hnot
            have : (if k > best.2.2 then (i + 1 - k, j + 1 - k, k) else best) = best := if_neg hnot
            rw [this]
            exact h7 hz
        · intro i' j' m hm he hl
          by_cases hend : j' + m - 1 = j
          · refine ⟨k, ?_, hup i' j' m hm he hend⟩
            rw [hend]
            simp
          · have hl2 : j' + m ≤ j := by have := hm.1; omega
            obtain ⟨v, hv1, hv2⟩ := h8 i' j' m hm he (hgap i' j' m hm he hl2)
            refine ⟨v, ?_, hv2⟩
            have : ((j' + m - 1) == j) = false := by simpa using hend
            simp only [List.lookup, this]
            exact hv1
        · intro i' j' m hm he
          have hprev : (i' + m ≤ i ∨ (i' + m = i + 1 ∧ j' + m ≤ lim)) ∨ (i' + m = i + 1 ∧ j' + m - 1 = j) := by
            rcases he with he | ⟨he, hl⟩
            · exact .inl (.inl he)
            · by_cases hend : j' + m - 1 = j
              · exact .inr ⟨he, hend⟩
              · exact .inl (.inr ⟨he, hgap i' j' m hm he (by have := hm.1; omega)⟩)
          split
          · rename_i hgt
            rcases hprev with hp | ⟨he1, he2⟩
            · have := h9 i' j' m hm hp
              have h11 := this.1
              refine ⟨by simp only; omega, ?_⟩
              simp only
              intro hm3
              omega
            · have hle := hup i' j' m hm he1 he2
              refine ⟨by simp only; exact hle, ?_⟩
              simp only
              intro hm3
              right
              exact ⟨by omega, by omega⟩
          · rename_i hnot
            have hnot' : k ≤ best.2.2 := by omega
            rcases hprev with hp | ⟨he1, he2⟩
            · exact h9 i' j' m hm hp
            · have hle := hup i' j' m hm he1 he2
              refine ⟨by omega, ?_⟩
              intro hm3
              have hb2 := h6.2.1
              rcases h10 with h | h
              · left; omega
              · by_cases heq : best.1 = i'
                · right
                  exact ⟨heq, by omega⟩
                · left; omega
        · split
          · right
            have := (n1 j k (by simp)).2.2.1
            simp only
            omega
          · rcases h10 with h | h
            · exact .inl h
            · exact .inr (by omega)

/-- All the indices of each element are in `b2j`. -/
def Compl (s : SM) : Prop := ∀ e x, s.b[e]? = some x → e ∈ lookupIdx s.b2j x

theorem outer_max (s : SM) (hs : Ready s) (hC : Compl s) (alo blo bhi ahi : Nat) (ha : ahi ≤ s.a.length)
    (hb : bhi ≤ s.b.length) :
    ∀ (fuel i : Nat) (old : List (Nat × Nat)) (best : Best), i + fuel = ahi → alo ≤ i →
      RowOk s alo blo bhi i old → RowC s alo blo bhi i old → BestOk s alo blo bhi i best → ZeroB alo blo best →
      BestMax s alo blo bhi i best →
      ∃ b', outerLoop s blo bhi ahi fuel i old best = .ok b' ∧ BestOk s alo blo bhi ahi b' ∧ ZeroB alo blo b' ∧
        BestMax s alo blo bhi ahi b' := by
  intro fuel
  induction fuel with
  | zero =>
    intro i old best h1 _ _ _ h4 h5 h6
    have : i = ahi := by omega
    subst this
    exact ⟨best, rfl, h4, h5, h6⟩
  | succ f ih =>
    intro i old best h1 h2 h3 h3c h4 h5 h6
    obtain ⟨x, hx, hxa⟩ := at_ok s.a i (by omega)
    have hasc : (lookupIdx s.b2j x).Pairwise (· < ·) := by
      unfold lookupIdx
      cases hl : s.b2j.lookup x with
      | none => simp
      | some l => exact (hs x l hl).2
    have hin := inner_ok s alo blo bhi i x old hxa h2 hb h3 (lookupIdx s.b2j x) [] best (lookupIdx_ok s hs x)
      (by intro j k hl; simp at hl) (bestOk_mono h4 (by omega))
    obtain ⟨m1, m2, m3⟩ := inner_max s alo blo bhi i x old hxa h2 hb h3 h3c (lookupIdx s.b2j x) [] best 0
      (lookupIdx_ok s hs x) hasc (by simp) (fun e _ hb' => hC e x hb') (by intro j k hl; simp at hl)
      (bestOk_mono h4 (by omega)) h5
      (by intro i' j' k hm _ hl; have := hm.1; omega)
      (by
        intro i' j' m hm he
        rcases he with he | ⟨_, hl⟩
        · exact h6 i' j' m hm he
        · have := hm.1; omega)
      (.inl h4.2.1)
    simp only [outerLoop, hx]
    exact ih (i + 1) _ _ (by omega) (by omega) hin.1 m1 hin.2 m3 m2

theorem extL_same (s : SM) (junk : Bool) (alo ahi blo bhi : Nat) : ∀ (f i j k : Nat), Eqs s.a s.b i j k → alo ≤ i → blo ≤ j →
    i + k ≤ ahi → j + k ≤ bhi → (∀ m, Mt s alo blo bhi (i - 1) (j - 1) m → i - 1 + m ≤ ahi → m ≤ k) →
    extendLeft s junk alo blo f (i, j, k) = .ok (i, j, k) := by
  intro f
  cases f with
  | zero => intro _ _ _ _ _ _ _ _ _; rfl
  | succ f =>
    intro i j k h h1 h2 h3 h4 hmax
    simp only [extendLeft]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨c1, c2⟩ := hc
      obtain ⟨r, hr, he⟩ := extTest_ok s junk (i - 1) (j - 1) (by have := h.1; omega) (by have := h.2.1; omega)
      rw [hr]
      cases r with
      | false => rfl
      | true =>
        exfalso
        have e1 : i = (i - 1) + 1 := by omega
        have e2 : j = (j - 1) + 1 := by omega
        have h' : Eqs s.a s.b ((i - 1) + 1) ((j - 1) + 1) k := by rw [← e1, ← e2]; exact h
        have := hmax (k + 1) ⟨by omega, by omega, by omega, by omega, eqs_left h' (he rfl)⟩ (by omega)
        omega
    · rfl

theorem extR_same (s : SM) (junk : Bool) (alo ahi blo bhi : Nat) (hA : ahi ≤ s.a.length) (hB : bhi ≤ s.b.length) (f i j k : Nat)
    (h : Eqs s.a s.b i j k) (h1 : alo ≤ i) (h2 : blo ≤ j)
    (hmax : ∀ m, Mt s alo blo bhi i j m → i + m ≤ ahi → m ≤ k) :
    extendRight s junk ahi bhi f (i, j, k) = .ok (i, j, k) := by
  cases f with
  | zero => rfl
  | succ f =>
    simp only [extendRight]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨c1, c2⟩ := hc
      obtain ⟨r, hr, he⟩ := extTest_ok s junk (i + k) (j + k) (by omega) (by omega)
      rw [hr]
      cases r with
      | false => rfl
      | true =>
        exfalso
        have := hmax (k + 1) ⟨by omega, h1, h2, by omega, eqs_right h (by omega) (by omega) (he rfl)⟩ (by omega)
        omega
    · rfl

/-- `find_longest_match` on a box in range, with all of `b` in `b2j`. -/
theorem findLongest_max (s : SM) (hs : Ready s) (hC : Compl s) (alo ahi blo bhi : Nat) (h1 : alo ≤ ahi)
    (h2 : ahi ≤ s.a.length) (h3 : blo ≤ bhi) (h4 : bhi ≤ s.b.length) :
    ∃ i j k, findLongest s alo ahi blo bhi = .ok (i, j, k) ∧ alo ≤ i ∧ i + k ≤ ahi ∧ blo ≤ j ∧ j + k ≤ bhi ∧
      Eqs s.a s.b i j k ∧ ∀ i' j' k', alo ≤ i' → i' + k' ≤ ahi → blo ≤ j' → j' + k' ≤ bhi → Eqs s.a s.b i' j' k' →
        k' ≤ k ∧ (k' = k → i < i' ∨ (i = i' ∧ j ≤ j')) := by
  obtain ⟨b, hb, b0, bz, bm⟩ := outer_max s hs hC alo blo bhi ahi h2 h4 (ahi - alo) alo [] (alo, blo, 0)
    (by omega) (by omega) (by intro j k hl; simp at hl)
    (by intro i' j' k hm he; have := hm.1; have := hm.2.1; omega)
    ⟨Nat.le_refl _, by simp, Nat.le_refl _, by simpa using h3, eqs_zero _ _ _ _ (by simp only; omega) (by simp only; omega)⟩
    (by intro _; exact ⟨rfl, rfl⟩)
    (by intro i' j' m hm he; have := hm.1; have := hm.2.1; omega)
  obtain ⟨i, j, k⟩ := b
  obtain ⟨c1, c2, c3, c4, c5⟩ := b0
  simp only at c1 c2 c3 c4 c5
  have hleft : ∀ jk, extendLeft s jk alo blo (ahi + bhi + 1) (i, j, k) = .ok (i, j, k) := by
    intro jk
    refine extL_same s jk alo ahi blo bhi _ i j k c5 c1 c3 c2 c4 ?_
    intro m hm hl
    exact (bm _ _ _ hm hl).1
  have hright : ∀ jk, extendRight s jk ahi bhi (ahi + bhi + 1) (i, j, k) = .ok (i, j, k) := by
    intro jk
    refine extR_same s jk alo ahi blo bhi h2 h4 _ i j k c5 c1 c3 ?_
    intro m hm hl
    exact (bm _ _ _ hm hl).1
  refine ⟨i, j, k, ?_, c1, c2, c3, c4, c5, ?_⟩
  · simp only [findLongest, hb, hleft, hright]
  · intro i' j' k' d1 d2 d3 d4 d5
    by_cases hz : k' = 0
    · subst hz
      refine ⟨by omega, ?_⟩
      intro he
      obtain ⟨z1, z2⟩ := bz he.symm
      simp only at z1 z2
      by_cases hlt : i < i'
      · exact .inl hlt
      · exact .inr ⟨by omega, by omega⟩
    · exact bm i' j' k' ⟨by omega, d1, d3, d4, d5⟩ d2

/-! ### `b2j` holds all of `b` when nothing is purged -/

def CompInv (b : List Nat) (n : Nat) (m : List (Nat × List Nat)) : Prop :=
  ∀ j x, j < n → b[j]? = some x → j ∈ (m.lookup x).getD []

theorem comp_step (b : List Nat) (n e : Nat) (m : List (Nat × List Nat)) (he : b[n]? = some e)
    (h : CompInv b n m) : CompInv b (n + 1) (addIdx m e n) := by
  intro j x hj hb
  rw [lookup_addIdx]
  split
  · rename_i hx
    have hx : x = e := by simpa using hx
    subst hx
    simp only [Option.getD_some, List.mem_append, List.mem_singleton]
    by_cases hn : j = n
    · exact .inr hn
    · exact .inl (h j x (by omega) hb)
  · rename_i hx
    have hx : x ≠ e := by simpa using hx
    by_cases hn : j = n
    · subst hn
      rw [he] at hb
      simp only [Option.some.injEq] at hb
      exact absurd hb.symm hx
    · exact h j x (by omega) hb

theorem comp_loop (b : List Nat) : ∀ (rest : List Nat) (n : Nat) (m : List (Nat × List Nat)),
    (∀ t, rest[t]? = b[n + t]?) → CompInv b n m →
    CompInv b (n + rest.length) ((rest.zipIdx n).foldl (fun m p => addIdx m p.1 p.2) m) := by
  intro rest
  induction rest with
  | nil => intro n m _ h; simpa using h
  | cons e r ih =>
    intro n m hr h
    simp only [List.zipIdx_cons, List.foldl_cons, List.length_cons]
    have he : b[n]? = some e := by
      have := hr 0
      simpa using this.symm
    have := ih (n + 1) _ (fun t => by
      have := hr (t + 1)
      have e1 : n + (t + 1) = n + 1 + t := by omega
      rw [e1] at this
      simpa using this) (comp_step b n e m he h)
    have e2 : n + 1 + r.length = n + (r.length + 1) := by omega
    rwa [e2] at this

theorem buildB2j_comp (b : List Nat) (e x : Nat) (h : b[e]? = some x) : e ∈ lookupIdx (buildB2j b) x := by
  have hc := comp_loop b b 0 [] (fun t => by simp) (fun j x hj => absurd hj (Nat.not_lt_zero _))
  have hlt : e < b.length := by
    rcases List.getElem?_eq_some_iff.mp h with ⟨h', _⟩
    exact h'
  exact hc e x (by omega) h

theorem make_plain (a b : List Nat) (auto : Bool) (s : SM) (hp : auto = false ∨ b.length < 200)
    (h : make none a b auto = .ok s) : s.b2j = buildB2j b := by
  have hc : (auto && decide (b.length ≥ 200)) = false := by
    rcases hp with rfl | hp
    · rfl
    · have : ¬ b.length ≥ 200 := by omega
      simp [this]
  have h' := make_ok _ _ _ _ _ h
  simp only [chainB, junkStep, hc, Bool.false_eq_true, if_false, Prod.mk.injEq, and_true] at h'
  subst h'
  simp

/-- The docstring of `find_longest_match`, for a box in range, with no `isjunk` and nothing popular: of
all matching blocks in the box, the result is one of the longest, the earliest in `a` among those, and
the earliest in `b` among those, and `(alo, blo, 0)` if there is none. -/
def FindLongestDoc : Prop :=
  ∀ (a b : List Nat) (auto : Bool) (s : SM) (alo ahi blo bhi : Nat), (auto = false ∨ b.length < 200) →
    make none a b auto = .ok s → alo ≤ ahi → ahi ≤ a.length → blo ≤ bhi → bhi ≤ b.length →
    ∃ i j k, findLongest s alo ahi blo bhi = .ok (i, j, k) ∧ alo ≤ i ∧ i + k ≤ ahi ∧ blo ≤ j ∧ j + k ≤ bhi ∧
      Eqs a b i j k ∧ ∀ i' j' k', alo ≤ i' → i' + k' ≤ ahi → blo ≤ j' → j' + k' ≤ bhi → Eqs a b i' j' k' →
        k' ≤ k ∧ (k' = k → i < i' ∨ (i = i' ∧ j ≤ j'))

theorem findLongestDoc_proven : FindLongestDoc := by
  intro a b auto s alo ahi blo bhi hp h h1 h2 h3 h4
  obtain ⟨hr, rfl, rfl⟩ := make_ready _ _ _ _ _ h
  have hb2j := make_plain _ _ _ _ hp h
  have hC : Compl s := by
    intro e x he
    rw [hb2j]
    exact buildB2j_comp _ e x he
  exact findLongest_max s hr hC alo ahi blo bhi h1 h2 h3 h4

end PyLean.TextLibs.Difflib
