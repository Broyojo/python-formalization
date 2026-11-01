import PyLean.LongObj.PylongDiv

/-!
`compute_powers` of `Lib/_pylong.py`, over an abstract base type. The assumption on
the type is only what the third loop uses: `base ** (n + 1) == base ** n * base` and
`base ** (n + n) == base ** n * base ** n`, which hold for `int` and for `Decimal` in
an unbounded context.

The result has every exponent the recursive callers ask for, and no other (the claim
that the `consumer` block at _pylong.py:706-722 tests): `Reach` is that recursion.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt

/-- The exponent a level of width `x` asks for: `hi if need_hi else lo`. -/
def whichOf (needHi : Bool) (x : Nat) : Nat := if needHi then x - x >>> 1 else x >>> 1

/-- The widths the recursive functions reach from `w`. -/
inductive Reach (M w : Nat) : Nat → Prop
  | top : Reach M w w
  | lo {x : Nat} : Reach M w x → M < x → Reach M w (x >>> 1)
  | hi {x : Nat} : Reach M w x → M < x → Reach M w (x - x >>> 1)

def Cov (M : Nat) (ws seen : List Nat) (y : Nat) : Prop := y ∈ seen ∨ y ∈ ws ∨ y ≤ M

structure WorkInv (needHi : Bool) (M w : Nat) (ws seen need : List Nat) : Prop where
  top : Cov M ws seen w
  step : ∀ x ∈ seen, whichOf needHi x ∈ need ∧ Cov M ws seen (x >>> 1) ∧
    Cov M ws seen (x - x >>> 1)
  seenR : ∀ x ∈ seen, Reach M w x ∧ M < x
  wsR : ∀ x ∈ ws, Reach M w x
  needR : ∀ k ∈ need, ∃ x, Reach M w x ∧ M < x ∧ k = whichOf needHi x
  nd : need.Nodup

def wt (M : Nat) (seen : List Nat) (x : Nat) : Nat := if x ∈ seen ∨ x ≤ M then 1 else 4 * x - 1

def mu (M : Nat) (ws seen : List Nat) : Nat := (ws.map (wt M seen)).sum

theorem sum_insert (f : Nat → Nat) (a : Nat) (l : List Nat) :
    ((l.insert a).map f).sum ≤ (l.map f).sum + f a := by
  by_cases h : a ∈ l
  · rw [List.insert_of_mem h]; omega
  · rw [List.insert_of_not_mem h]; simp; omega

theorem sum_mono {f g : Nat → Nat} (h : ∀ x, f x ≤ g x) : ∀ l : List Nat,
    (l.map f).sum ≤ (l.map g).sum
  | [] => Nat.le_refl _
  | x :: l => by
    have := sum_mono h l
    have := h x
    simp only [List.map_cons, List.sum_cons]
    omega

theorem nodup_insert {a : Nat} {l : List Nat} (h : l.Nodup) : (l.insert a).Nodup := by
  by_cases ha : a ∈ l
  · rw [List.insert_of_mem ha]; exact h
  · rw [List.insert_of_not_mem ha]; exact List.nodup_cons.2 ⟨ha, h⟩

theorem cpWork_spec {needHi : Bool} {M w : Nat} : ∀ (f : Nat) (ws seen need : List Nat),
    mu M ws seen < f → WorkInv needHi M w ws seen need →
    ∃ need' seen', cpWork needHi M f ws seen need = .ok need' ∧ WorkInv needHi M w [] seen' need'
  | 0, _, _, _, h, _ => by omega
  | f + 1, [], seen, need, _, h => ⟨need, seen, rfl, h⟩
  | f + 1, x :: ws, seen, need, hm, h => by
    have hmu : mu M (x :: ws) seen = wt M seen x + mu M ws seen := by simp [mu]
    rw [hmu] at hm
    by_cases hc : x ∈ seen ∨ x ≤ M
    · rw [cpWork, if_pos hc]
      have hw : wt M seen x = 1 := if_pos hc
      apply cpWork_spec f ws seen need (by omega)
      have cov : ∀ y, Cov M (x :: ws) seen y → Cov M ws seen y := by
        rintro y (h1 | h1 | h1)
        · exact Or.inl h1
        · rcases List.mem_cons.1 h1 with rfl | h2
          · rcases hc with h3 | h3
            · exact Or.inl h3
            · exact Or.inr (Or.inr h3)
          · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr h1)
      exact ⟨cov _ h.top, fun y hy => ⟨(h.step y hy).1, cov _ (h.step y hy).2.1,
        cov _ (h.step y hy).2.2⟩, h.seenR, fun y hy => h.wsR y (List.mem_cons_of_mem _ hy),
        h.needR, h.nd⟩
    · rw [cpWork, if_neg hc]
      have hxM : M < x := by
        apply Nat.lt_of_not_le
        intro hx
        exact hc (Or.inr hx)
      have hxs : x ∉ seen := fun hx => hc (Or.inl hx)
      have hxR : Reach M w x := h.wsR x (by simp)
      obtain ⟨lo, hlo⟩ : ∃ lo, x >>> 1 = lo := ⟨_, rfl⟩
      obtain ⟨hi, hhi⟩ : ∃ hi, x - lo = hi := ⟨_, rfl⟩
      have hlo2 : lo = x / 2 := by rw [← hlo, shr1]
      have hRlo : Reach M w lo := hlo ▸ Reach.lo hxR hxM
      have hRhi : Reach M w hi := by
        rw [← hhi, ← hlo]
        exact Reach.hi hxR hxM
      simp only [hlo, hhi]
      obtain ⟨wh, hwh⟩ : ∃ wh, (if needHi = true then hi else lo) = wh := ⟨_, rfl⟩
      rw [hwh]
      have hwhOf : whichOf needHi x = wh := by
        unfold whichOf
        rw [hlo, hhi]
        exact hwh
      obtain ⟨ot, hot⟩ : ∃ ot, x - wh = ot := ⟨_, rfl⟩
      rw [hot]
      have hcases : (wh = lo ∧ ot = hi) ∨ (wh = hi ∧ ot = lo) := by
        cases needHi
        · simp at hwh
          left; omega
        · simp at hwh
          right; omega
      have hwhR : Reach M w wh := by
        rcases hcases with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> assumption
      have hotR : Reach M w ot := by
        rcases hcases with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption
      obtain ⟨ws'', hws⟩ : ∃ ws'', (if lo ≠ hi then List.insert ot (List.insert wh ws)
          else List.insert wh ws) = ws'' := ⟨_, rfl⟩
      rw [hws]
      have hsub : ∀ y, y ∈ ws → y ∈ ws'' := by
        intro y hy
        rw [← hws]
        split
        · exact List.mem_insert_iff.2 (Or.inr (List.mem_insert_iff.2 (Or.inr hy)))
        · exact List.mem_insert_iff.2 (Or.inr hy)
      have hwhm : wh ∈ ws'' := by
        rw [← hws]
        split
        · exact List.mem_insert_iff.2 (Or.inr (List.mem_insert_iff.2 (Or.inl rfl)))
        · exact List.mem_insert_iff.2 (Or.inl rfl)
      have hotm : ot ∈ ws'' := by
        rw [← hws]
        split
        · exact List.mem_insert_iff.2 (Or.inl rfl)
        · rename_i hne
          have hn : lo = hi := by omega
          have : ot = wh := by
            rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
          rw [this]
          exact List.mem_insert_iff.2 (Or.inl rfl)
      have hlom : lo ∈ ws'' := by
        rcases hcases with ⟨rfl, _⟩ | ⟨_, rfl⟩ <;> assumption
      have hhim : hi ∈ ws'' := by
        rcases hcases with ⟨_, rfl⟩ | ⟨rfl, _⟩ <;> assumption
      have hws2 : ∀ y, y ∈ ws'' → y ∈ ws ∨ y = wh ∨ y = ot := by
        intro y hy
        rw [← hws] at hy
        split at hy
        · rcases List.mem_insert_iff.1 hy with h1 | h1
          · exact Or.inr (Or.inr h1)
          · rcases List.mem_insert_iff.1 h1 with h2 | h2
            · exact Or.inr (Or.inl h2)
            · exact Or.inl h2
        · rcases List.mem_insert_iff.1 hy with h1 | h1
          · exact Or.inr (Or.inl h1)
          · exact Or.inl h1
      have cov : ∀ y, Cov M (x :: ws) seen y → Cov M ws'' (x :: seen) y := by
        rintro y (h1 | h1 | h1)
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · rcases List.mem_cons.1 h1 with rfl | h2
          · exact Or.inl (by simp)
          · exact Or.inr (Or.inl (hsub y h2))
        · exact Or.inr (Or.inr h1)
      have hnew : WorkInv needHi M w ws'' (x :: seen) (List.insert wh need) := by
        refine ⟨cov _ h.top, ?_, ?_, ?_, ?_, nodup_insert h.nd⟩
        · intro y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · refine ⟨?_, ?_, ?_⟩
            · rw [hwhOf]; exact List.mem_insert_iff.2 (Or.inl rfl)
            · rw [hlo]; exact Or.inr (Or.inl hlom)
            · rw [hlo, hhi]; exact Or.inr (Or.inl hhim)
          · obtain ⟨h1, h2, h3⟩ := h.step y hy
            exact ⟨List.mem_insert_iff.2 (Or.inr h1), cov _ h2, cov _ h3⟩
        · intro y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · exact ⟨hxR, hxM⟩
          · exact h.seenR y hy
        · intro y hy
          rcases hws2 y hy with h1 | rfl | rfl
          · exact h.wsR y (List.mem_cons_of_mem _ h1)
          · exact hwhR
          · exact hotR
        · intro k hk
          rcases List.mem_insert_iff.1 hk with rfl | hk
          · exact ⟨x, hxR, hxM, hwhOf.symm⟩
          · exact h.needR k hk
      refine cpWork_spec f ws'' (x :: seen) (List.insert wh need) ?_ hnew
      -- The measure drops.
      have hwx : wt M seen x = 4 * x - 1 := if_neg hc
      have hmono : ∀ y, wt M (x :: seen) y ≤ wt M seen y := by
        intro y
        unfold wt
        by_cases h1 : y ∈ seen ∨ y ≤ M
        · have h2 : y ∈ x :: seen ∨ y ≤ M := by
            rcases h1 with h3 | h3
            · exact Or.inl (List.mem_cons_of_mem _ h3)
            · exact Or.inr h3
          rw [if_pos h1, if_pos h2]
          exact Nat.le_refl _
        · rw [if_neg h1]
          have hy1 : 1 ≤ y := by
            have : ¬ y ≤ M := fun h3 => h1 (Or.inr h3)
            omega
          split <;> omega
      have hms : mu M ws (x :: seen) ≤ mu M ws seen := sum_mono hmono ws
      have hW : ∀ y, y ≠ x → wt M (x :: seen) y ≤ (if y = 0 then 1 else 4 * y - 1) := by
        intro y _
        unfold wt
        split
        · split <;> omega
        · rename_i h3
          have : ¬ y ≤ M := fun h4 => h3 (Or.inr h4)
          have : y ≠ 0 := by omega
          simp [this]
      have hWx : wt M (x :: seen) x = 1 := if_pos (Or.inl (by simp))
      have hmu2 : mu M ws'' (x :: seen) ≤ mu M ws (x :: seen) +
          (if lo ≠ hi then wt M (x :: seen) lo + wt M (x :: seen) hi
           else wt M (x :: seen) lo) := by
        rw [← hws]
        unfold mu
        by_cases hne : lo ≠ hi
        · rw [if_pos hne, if_pos hne]
          have h1 := sum_insert (wt M (x :: seen)) ot (List.insert wh ws)
          have h2 := sum_insert (wt M (x :: seen)) wh ws
          rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
        · rw [if_neg hne, if_neg hne]
          have h2 := sum_insert (wt M (x :: seen)) wh ws
          have hn : lo = hi := by omega
          have hwl : wh = lo := by
            rcases hcases with ⟨h3, _⟩ | ⟨h3, _⟩ <;> omega
          rw [hwl] at h2 ⊢
          exact h2
      have hbound : 1 + (if lo ≠ hi then wt M (x :: seen) lo + wt M (x :: seen) hi
          else wt M (x :: seen) lo) ≤ 4 * x - 1 := by
        by_cases hx1 : x = 1
        · subst hx1
          have h0 : lo = 0 := by omega
          have h1 : hi = 1 := by omega
          subst h0 h1
          have h2 := hW 0 (by decide)
          simp only [if_true] at h2
          rw [if_pos (by decide)]
          omega
        · have hx2 : 2 ≤ x := by omega
          have hl := hW lo (by omega)
          have hh := hW hi (by omega)
          rw [if_neg (by omega)] at hl
          rw [if_neg (by omega)] at hh
          split <;> omega
      omega

theorem reach_mem {needHi : Bool} {M w : Nat} {seen need : List Nat}
    (h : WorkInv needHi M w [] seen need) : ∀ y, Reach M w y → M < y → y ∈ seen := by
  intro y hy
  have hcov : ∀ z, Cov M [] seen z → M < z → z ∈ seen := by
    rintro z (h1 | h1 | h1) hz
    · exact h1
    · cases h1
    · omega
  induction hy with
  | top => exact hcov _ h.top
  | lo _ hM ih => exact hcov _ (h.step _ (ih hM)).2.1
  | hi _ hM ih => exact hcov _ (h.step _ (ih hM)).2.2

/-- The first loop of `compute_powers`: `need` is exactly the set the recursion needs. -/
theorem cpWork_result (needHi : Bool) (M w : Nat) :
    ∃ need, cpWork needHi M (4 * w + 4) [w] [] [] = .ok need ∧ need.Nodup ∧
      (∀ y, Reach M w y → M < y → whichOf needHi y ∈ need) ∧
      (∀ k ∈ need, ∃ x, Reach M w x ∧ M < x ∧ k = whichOf needHi x) := by
  have h0 : WorkInv needHi M w [w] [] [] :=
    ⟨Or.inr (Or.inl (by simp)), fun _ h => by simp at h, fun _ h => by simp at h,
      fun x hx => by
        simp only [List.mem_singleton] at hx
        subst hx
        exact Reach.top, fun _ h => by simp at h, List.nodup_nil⟩
  have hm : mu M [w] [] < 4 * w + 4 := by
    simp only [mu, wt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    split <;> omega
  obtain ⟨need, seen, e, hi⟩ := cpWork_spec _ _ _ _ hm h0
  exact ⟨need, e, hi.nd, fun y hy hM => (hi.step y (reach_mem hi y hy hM)).1, hi.needR⟩

/-! ## The second loop -/

theorem fold_max_le : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], a => ⟨Nat.le_refl _, fun _ h => by simp at h⟩
  | c :: l, a => by
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := fold_max_le l (max a c)
    refine ⟨by omega, ?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · omega
    · exact h2 x hx

theorem fold_max_mem : ∀ (l : List Nat) (a : Nat), l.foldl max a = a ∨ l.foldl max a ∈ l
  | [], _ => Or.inl rfl
  | c :: l, a => by
    simp only [List.foldl_cons]
    rcases fold_max_mem l (max a c) with h | h
    · rw [h]
      by_cases hc : a ≤ c
      · right
        have : max a c = c := by omega
        rw [this]
        simp
      · left; omega
    · right; exact List.mem_cons_of_mem _ h

theorem nodup_foldr_insert {e : List Nat} (he : e.Nodup) : ∀ l : List Nat,
    (l.foldr List.insert e).Nodup
  | [] => he
  | _ :: l => nodup_insert (nodup_foldr_insert he l)

theorem mem_foldr_insert {e : List Nat} {x : Nat} : ∀ l : List Nat,
    x ∈ l.foldr List.insert e ↔ x ∈ l ∨ x ∈ e
  | [] => by simp
  | a :: l => by
    simp only [List.foldr_cons, List.mem_insert_iff, mem_foldr_insert l, List.mem_cons]
    constructor
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

theorem fold_max_nonempty (c : Nat) (cs : List Nat) :
    (c :: cs).foldl max 0 ∈ c :: cs ∧ ∀ x ∈ c :: cs, x ≤ (c :: cs).foldl max 0 := by
  obtain ⟨_, h2⟩ := fold_max_le (c :: cs) 0
  refine ⟨?_, h2⟩
  rcases fold_max_mem (c :: cs) 0 with h | h
  · have := h2 c (by simp)
    rw [h]
    have hc : c = 0 := by omega
    subst hc
    simp
  · exact h

theorem sum_erase {a : Nat} : ∀ {l : List Nat}, a ∈ l →
    ((l.erase a).map (· + 1)).sum + (a + 1) = (l.map (· + 1)).sum
  | [], h => by simp at h
  | x :: l, h => by
    by_cases hx : x = a
    · subst hx
      simp [List.erase_cons_head]
      omega
    · have hm : a ∈ l := (List.mem_cons.1 h).resolve_left (Ne.symm hx)
      have := sum_erase hm
      rw [List.erase_cons_tail (by simpa using hx)]
      simp only [List.map_cons, List.sum_cons]
      omega

theorem cpExtra_term {M : Nat} : ∀ (f : Nat) (C extra : List Nat),
    (C.map (· + 1)).sum < f → extra.Nodup →
    ∃ e, cpExtra M f C extra = .ok e ∧ e.Nodup
  | 0, _, _, h, _ => by omega
  | f + 1, [], extra, _, hn => ⟨extra, rfl, hn⟩
  | f + 1, c :: cs, extra, hs, hn => by
    rw [cpExtra]
    obtain ⟨hmem, hle⟩ := fold_max_nonempty c cs
    obtain ⟨w, hw⟩ : ∃ w, (c :: cs).foldl max 0 = w := ⟨_, rfl⟩
    rw [hw] at hmem hle
    simp only [hw]
    have hsum := sum_erase hmem
    obtain ⟨cands, hc⟩ : ∃ cands, (c :: cs).erase w = cands := ⟨_, rfl⟩
    rw [hc] at hsum
    simp only [hc]
    by_cases hif : w >>> 1 > M ∧ w - 1 ∉ cands ∧ w >>> 1 ∉ cands
    · rw [if_pos hif]
      have h1 := sum_insert (· + 1) (w >>> 1) cands
      have hsh : w >>> 1 = w / 2 := shr1 w
      have hlt : w >>> 1 < w := by
        have := hif.1
        omega
      exact cpExtra_term f _ _ (by omega) (nodup_insert hn)
    · rw [if_neg hif]
      exact cpExtra_term f _ _ (by omega) hn

theorem length_le_sum : ∀ l : List Nat, l.length ≤ (l.map (· + 1)).sum
  | [] => Nat.le_refl _
  | x :: l => by
    have := length_le_sum l
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- With `need_hi` false, `need` already has every exponent's half: `assert need_hi or not
extra`, _pylong.py:97. -/
theorem cpExtra_false {M : Nat} : ∀ (f : Nat) (C : List Nat), C.length < f →
    (∀ w ∈ C, M < w >>> 1 → w >>> 1 ∈ C) → cpExtra M f C [] = .ok []
  | 0, _, h, _ => by omega
  | f + 1, [], _, _ => rfl
  | f + 1, c :: cs, hl, hc => by
    rw [cpExtra]
    obtain ⟨hmem, hle⟩ := fold_max_nonempty c cs
    obtain ⟨w, hw⟩ : ∃ w, (c :: cs).foldl max 0 = w := ⟨_, rfl⟩
    rw [hw] at hmem hle
    simp only [hw]
    obtain ⟨cands, hcd⟩ : ∃ cands, (c :: cs).erase w = cands := ⟨_, rfl⟩
    have hlen : cands.length + 1 = (c :: cs).length := by
      rw [← hcd, List.length_erase_of_mem hmem]
      have : 0 < (c :: cs).length := by simp
      omega
    have hkeep : ∀ y, y ∈ c :: cs → y ≠ w → y ∈ cands := by
      intro y hy hne
      rw [← hcd]
      exact (List.mem_erase_of_ne hne).2 hy
    have hshr : ∀ y, y >>> 1 = y / 2 := shr1
    simp only [hcd]
    have hnot : ¬ (w >>> 1 > M ∧ w - 1 ∉ cands ∧ w >>> 1 ∉ cands) := by
      rintro ⟨h1, _, h3⟩
      have hin := hc w hmem h1
      have hne : w >>> 1 ≠ w := by
        have := hshr w
        omega
      exact h3 (hkeep _ hin hne)
    rw [if_neg hnot]
    apply cpExtra_false f cands (by have h5 : (c :: cs).length = cs.length + 1 := rfl; omega)
    intro x hx hM
    have hxm : x ∈ c :: cs := by
      rw [← hcd] at hx
      exact List.mem_of_mem_erase hx
    have hin := hc x hxm hM
    have hxw : x ≤ w := hle x hxm
    have hne : x >>> 1 ≠ w := by
      have := hshr x
      omega
    exact hkeep _ hin hne

/-! ## The third loop -/

theorem dGet_append {α : Type} (k : Nat) (d e : PowDict α) :
    dGet k (d ++ e) = (dGet k d).or (dGet k e) := List.lookup_append

theorem dGet_single {α : Type} (k n : Nat) (r : α) :
    dGet k [(n, r)] = if k = n then some r else none := by
  simp only [dGet, List.lookup_cons, List.lookup_nil]
  by_cases h : k = n
  · simp [h]
  · have : (k == n) = false := by simpa using h
    simp [this, h]

theorem dGet_filter {α : Type} (k : Nat) (need : List Nat) : ∀ d : PowDict α,
    dGet k (d.filter (fun kv => decide (kv.1 ∈ need))) = if k ∈ need then dGet k d else none
  | [] => by simp [dGet]
  | (a, v) :: d => by
    have ih := dGet_filter k need d
    rw [List.filter_cons]
    by_cases ha : a ∈ need
    · simp only [ha, decide_true, if_true]
      unfold dGet at ih ⊢
      simp only [List.lookup_cons]
      by_cases hk : k = a
      · subst hk
        simp [ha]
      · have : (k == a) = false := by simpa using hk
        simp only [this, ih]
    · simp only [ha, decide_false, Bool.false_eq_true, if_false]
      rw [ih]
      by_cases hk : k ∈ need
      · have hne : k ≠ a := fun h => ha (h ▸ hk)
        have : (k == a) = false := by simpa using hne
        simp [hk, dGet, List.lookup_cons, this]
      · simp [hk]

theorem dGet_isSome_of_mem {α : Type} {k : Nat} {v : α} : ∀ {d : PowDict α}, (k, v) ∈ d →
    (dGet k d).isSome
  | [], h => by simp at h
  | (a, w) :: d, h => by
    unfold dGet
    simp only [List.lookup_cons]
    by_cases hk : k = a
    · subst hk
      simp
    · have : (k == a) = false := by simpa using hk
      simp only [this]
      rcases List.mem_cons.1 h with h1 | h1
      · simp at h1
        exact absurd h1.1 hk
      · exact dGet_isSome_of_mem h1

section
variable {α : Type} {mul : α → α → α} {pow : α → Nat → α} {base : α}

theorem cpBuild_spec (hs : ∀ n, pow base (n + 1) = mul (pow base n) base)
    (hd : ∀ n, pow base (n + n) = mul (pow base n) (pow base n)) :
    ∀ (ns : List Nat) (d : PowDict α), ns.Nodup → (∀ k v, dGet k d = some v → v = pow base k) →
      (∀ n ∈ ns, dGet n d = none) →
      ∃ d', cpBuild mul pow base ns d = .ok d' ∧ (∀ k v, dGet k d' = some v → v = pow base k) ∧
        ∀ k, (dGet k d').isSome ↔ ((dGet k d).isSome ∨ k ∈ ns)
  | [], d, _, h1, _ => ⟨d, rfl, h1, fun k => by simp⟩
  | n :: ns, d, hn, h1, h2 => by
    obtain ⟨hn1, hn2⟩ := List.nodup_cons.1 hn
    have hdn : dGet n d = none := h2 n (by simp)
    -- One extension of the dictionary with the right value.
    have hext : ∀ r, r = pow base n →
        (∃ d', cpBuild mul pow base ns (d ++ [(n, r)]) = .ok d' ∧
          (∀ k v, dGet k d' = some v → v = pow base k) ∧
          ∀ k, (dGet k d').isSome ↔ ((dGet k d).isSome ∨ k ∈ n :: ns)) := by
      intro r hr
      have hget : ∀ k, dGet k (d ++ [(n, r)]) = (dGet k d).or (if k = n then some r else none) := by
        intro k
        rw [dGet_append, dGet_single]
      obtain ⟨d', e, a, b⟩ := cpBuild_spec hs hd ns (d ++ [(n, r)]) hn2
        (by
          intro k v hv
          rw [hget] at hv
          by_cases hk : k = n
          · subst hk
            rw [hdn] at hv
            simp at hv
            rw [← hv, hr]
          · rw [if_neg hk] at hv
            simp only [Option.or_none] at hv
            exact h1 k v hv)
        (by
          intro m hm
          rw [hget, h2 m (List.mem_cons_of_mem _ hm)]
          have : m ≠ n := fun h => hn1 (h ▸ hm)
          simp [this])
      refine ⟨d', e, a, fun k => ?_⟩
      rw [b k, hget k]
      by_cases hk : k = n
      · subst hk
        simp [hdn]
      · simp [hk]
    rw [cpBuild]
    dsimp only
    cases h3 : dGet (n - 1) d with
    | some v =>
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [show 0 - 1 = 0 from rfl, hdn] at h3
        cases h3
      have hv := h1 _ _ h3
      have : mul v base = pow base n := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [hv, Nat.add_sub_cancel, hs]
      exact hext _ this
    | none =>
      dsimp only
      cases h4 : dGet (n >>> 1) d with
      | some v =>
        dsimp only
        have hv := h1 _ _ h4
        have hsh := shr1 n
        by_cases hne : n - n >>> 1 ≠ n >>> 1
        · rw [if_pos hne, if_pos (by omega)]
          apply hext
          rw [hv, ← hd, ← hs]
          congr 1
          omega
        · rw [if_neg hne]
          apply hext
          rw [hv, ← hd]
          congr 1
          omega
      | none => exact hext _ rfl

/-- `compute_powers` returns every power the recursion asks for, correctly, and no others;
none of its assertions fire. -/
theorem computePowers_spec (hs : ∀ n, pow base (n + 1) = mul (pow base n) base)
    (hd : ∀ n, pow base (n + n) = mul (pow base n) (pow base n)) (w M : Nat) (needHi : Bool) :
    ∃ d, computePowers mul pow base w M needHi = .ok d ∧
      (∀ k v, dGet k d = some v → v = pow base k) ∧
      ∀ k, (dGet k d).isSome ↔ ∃ x, Reach M w x ∧ M < x ∧ k = whichOf needHi x := by
  obtain ⟨need, e1, hn, hc, hr⟩ := cpWork_result needHi M w
  obtain ⟨extra, e2, hex⟩ := cpExtra_term (M := M) ((need.map (· + 1)).sum + 1) need []
    (by omega) List.nodup_nil
  obtain ⟨keys, hkeys⟩ : ∃ keys, (need.foldr List.insert extra).mergeSort (· ≤ ·) = keys :=
    ⟨_, rfl⟩
  have hperm := List.mergeSort_perm (need.foldr List.insert extra) (· ≤ ·)
  rw [hkeys] at hperm
  have hkn : keys.Nodup := hperm.nodup_iff.2 (nodup_foldr_insert hex need)
  have hkm : ∀ x, x ∈ keys ↔ x ∈ need ∨ x ∈ extra := fun x => by
    rw [hperm.mem_iff, mem_foldr_insert]
  obtain ⟨d, e3, a, b⟩ := cpBuild_spec hs hd keys ([] : PowDict α) hkn
    (fun _ _ h => by simp [dGet] at h) (fun _ _ => rfl)
  have hkd : ∀ k, (dGet k d).isSome ↔ k ∈ keys := by
    intro k
    rw [b k]
    simp [dGet]
  have hextra : needHi = false → extra = [] := by
    intro hf
    subst hf
    have hclosed : ∀ w' ∈ need, M < w' >>> 1 → w' >>> 1 ∈ need := by
      intro w' hw' hM
      obtain ⟨x, hx, hxM, rfl⟩ := hr w' hw'
      have hlo : Reach M w (whichOf false x) := by
        simpa [whichOf] using Reach.lo hx hxM
      have hM2 : M < whichOf false x := by
        have h5 : whichOf false x = x >>> 1 := by simp [whichOf]
        rw [h5] at hM ⊢
        have := shr1 (x >>> 1)
        omega
      simpa [whichOf] using hc _ hlo hM2
    have := cpExtra_false (M := M) ((need.map (· + 1)).sum + 1) need
      (by have := length_le_sum need; omega) hclosed
    rw [this] at e2
    injection e2 with h
    exact h.symm
  have hassert1 : needHi = true ∨ extra = [] := by
    cases needHi
    · exact Or.inr (hextra rfl)
    · exact Or.inl rfl
  have hall : (need.all (fun k => (dGet k d).isSome)) = true := by
    rw [List.all_eq_true]
    intro k hk
    exact (hkd k).2 ((hkm k).2 (Or.inl hk))
  have hexcess : ¬ (d.filter (fun kv => decide (kv.1 ∉ need)) ≠ [] ∧ ¬ needHi = true) := by
    rintro ⟨h1, h2⟩
    apply h1
    have hno : extra = [] := hextra (by simpa using h2)
    apply List.filter_eq_nil_iff.2
    rintro ⟨k, v⟩ hkv
    have h3 : (dGet k d).isSome := dGet_isSome_of_mem hkv
    have h4 := (hkm k).1 ((hkd k).1 h3)
    rw [hno] at h4
    simpa using h4.resolve_right (by simp)
  refine ⟨d.filter (fun kv => decide (kv.1 ∈ need)), ?_, ?_, ?_⟩
  · unfold computePowers
    simp only [e1, bindOk, e2]
    rw [if_neg (fun h => h hassert1)]
    simp only [hkeys, e3, bindOk]
    rw [if_neg (fun h => h hall), if_neg hexcess]
    rfl
  · intro k v hv
    rw [dGet_filter] at hv
    split at hv
    · exact a k v hv
    · cases hv
  · intro k
    rw [dGet_filter]
    by_cases hk : k ∈ need
    · rw [if_pos hk]
      constructor
      · intro _
        exact hr k hk
      · intro _
        exact (hkd k).2 ((hkm k).2 (Or.inl hk))
    · rw [if_neg hk]
      constructor
      · simp
      · rintro ⟨x, hx, hM, rfl⟩
        exact absurd (hc x hx hM) hk

end

/-- `compute_powers` over the `int`s. -/
theorem computePowersNat_spec (w base M : Nat) (needHi : Bool) :
    ∃ d, computePowersNat w base M needHi = .ok d ∧
      (∀ k v, dGet k d = some v → v = base ^ k) ∧
      ∀ k, (dGet k d).isSome ↔ ∃ x, Reach M w x ∧ M < x ∧ k = whichOf needHi x :=
  computePowers_spec (mul := (· * ·)) (pow := (· ^ ·)) (base := base)
    (fun n => Nat.pow_succ ..) (fun n => Nat.pow_add ..) w M needHi

end PyLean.LongObj

