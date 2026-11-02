import PyLean.CoreLibs.Coll.CounterOps

/-!
`Counter.__xor__` and `Counter.__ixor__`, new in 3.15.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PyLean.CoreLibs.Coll

open PyLean D

variable {κ : Type} [DecidableEq κ]

section ops
variable (a b : Ctr κ)

def gXor : κ → Int → Option Int := fun e count =>
  let newcount := absI (count - cGet b e)
  if newcount ≠ 0 then some newcount else none
def hXor : κ → Int → Option Int := fun e count =>
  if !D.mem a e && decide (count ≠ 0) then some (absI count) else none

end ops

theorem absI_pos (x : Int) (h : absI x ≠ 0) : absI x > 0 := by
  unfold absI at *
  by_cases h0 : x < 0 <;> simp only [h0, if_true, if_false] at h ⊢ <;> omega

theorem absI_ne (x : Int) (h : x ≠ 0) : absI x ≠ 0 := by
  unfold absI
  split <;> omega

theorem absI_nonneg (x : Int) : absI x ≥ 0 := by
  unfold absI
  split <;> omega

theorem absI_zero_sub (x : Int) : absI (0 - x) = absI x := by
  unfold absI
  split <;> split <;> omega

theorem okXor {a b : Ctr κ} (ha : WF a) (hb : WF b) : OpOk (gXor b) (hXor a) a b := by
  refine ⟨ha, hb, ?_, ?_, ?_⟩
  · intro p _ hs
    simp only [hXor] at hs
    split at hs
    · next hc =>
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
      exact D.mem_false_iff.mp hc.1
    · simp at hs
  · intro e c n h
    simp only [gXor] at h
    split at h
    · next hc =>
      simp only [Option.some.injEq] at h
      rw [← h]
      exact absI_pos _ hc
    · simp at h
  · intro e c n h
    simp only [hXor] at h
    split at h
    · next hc =>
      simp only [Option.some.injEq] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      rw [← h]
      exact absI_pos _ (absI_ne _ hc.2)
    · simp at h

theorem xorC_res {a b : Ctr κ} (ha : WF a) (hb : WF b) : xorC a b = res (gXor b) (hXor a) a b :=
  two_loops a b (gXor b) ha hb (hXor a) (okXor ha hb).fresh

theorem cGet_xorC {a b : Ctr κ} (ha : WF a) (hb : WF b) (x : κ) :
    cGet (xorC a b) x = absI (cGet a x - cGet b x) := by
  rw [xorC_res ha hb, res_cGet (okXor ha hb)]
  by_cases hxa : x ∈ keys a
  · simp only [hxa, if_true, gXor]
    by_cases h : absI (cGet a x - cGet b x) = 0
    · simp [h]
    · simp [h]
  · have h0 := cGet_eq_zero hxa
    simp only [hxa, if_false, hXor, h0, absI_zero_sub]
    have hm : D.mem a x = false := D.mem_false_iff.mpr hxa
    by_cases hxb : x ∈ keys b
    · simp only [hxb, if_true, hm]
      by_cases hp : cGet b x = 0
      · simp [hp, absI]
      · simp [hp]
    · have h1 := cGet_eq_zero hxb
      simp [hxb, h1, absI]

theorem set_append_left {l : Ctr κ} {x : κ} (v : Int) (r : Ctr κ) (h : x ∉ keys l) :
    D.set (l ++ r) x v = l ++ D.set r x v := by
  induction l with
  | nil => rfl
  | cons q t ih =>
    obtain ⟨k, c⟩ := q
    have hne : k ≠ x := by
      intro e
      exact h (by simp [keys, e])
    have ht : x ∉ keys t := by
      intro hm
      exact h (by simp only [keys, List.map_cons, List.mem_cons]; exact Or.inr hm)
    simp [D.set, hne, ih ht]

/-- The first loop of `__ixor__`: a value is rewritten where it stands. -/
theorem ixor_first (F : κ × Int → Int) : ∀ (rest done : Ctr κ), WF (done ++ rest) →
    rest.foldl (fun s p => D.set s p.1 (F p)) (done ++ rest) =
      done ++ rest.map (fun p => (p.1, F p)) := by
  intro rest
  induction rest with
  | nil => intro done _; simp
  | cons p t ih =>
    intro done hw
    obtain ⟨k, c⟩ := p
    have hw' : (keys done ++ k :: keys t).Nodup := by
      simpa [WF, keys, List.map_append] using hw
    have hk : k ∉ keys done := by
      have := (List.nodup_append.1 hw').2.2
      intro hm
      exact this k hm k (by simp) rfl
    have hs : D.set (done ++ (k, c) :: t) k (F (k, c)) = (done ++ [(k, F (k, c))]) ++ t := by
      rw [set_append_left _ _ hk]
      simp [D.set]
    have hw2 : WF ((done ++ [(k, F (k, c))]) ++ t) := by
      have e : keys ((done ++ [(k, F (k, c))]) ++ t) = keys (done ++ (k, c) :: t) := by
        simp [keys, List.map_append]
      unfold WF
      rw [e]
      exact hw
    simp only [List.foldl_cons, hs]
    rw [ih _ hw2]
    simp [List.map_cons]

theorem foldlM_pure_xor (b : Ctr κ) (l s : Ctr κ) :
    l.foldlM (m := Except PyExc) (fun s p => Except.ok (D.set s p.1 (absI (p.2 - cGet b p.1)))) s =
    .ok (l.foldl (fun s p => D.set s p.1 (absI (p.2 - cGet b p.1))) s) := by
  induction l generalizing s with
  | nil => rfl
  | cons p t ih =>
    simp only [List.foldlM_cons, List.foldl_cons]
    exact ih _

/-- The second loop of `__ixor__`: what is not in the left operand is appended, in order. -/
theorem ixor_second (a : Ctr κ) : ∀ (b s : Ctr κ), WF b → (∀ p ∈ b, p.1 ∈ keys s ↔ p.1 ∈ keys a) →
    b.foldl (fun s p => if D.mem s p.1 then s else D.set s p.1 (absI p.2)) s =
      s ++ (b.filter (fun p => decide (p.1 ∉ keys a))).map (fun p => (p.1, absI p.2)) := by
  intro b
  induction b with
  | nil => intro s _ _; simp
  | cons p t ih =>
    intro s hw hk
    have hwt : WF t := WF_of_cons hw
    have hnot := notMem_of_cons hw
    have hp := hk p (by simp)
    simp only [List.foldl_cons]
    by_cases hin : p.1 ∈ keys a
    · have hm : D.mem s p.1 = true := D.mem_iff.2 (hp.2 hin)
      simp only [hm, if_true, List.filter_cons, hin, not_true_eq_false, decide_false, Bool.false_eq_true, if_false]
      exact ih s hwt (fun q hq => hk q (List.mem_cons_of_mem _ hq))
    · have hns : p.1 ∉ keys s := fun h => hin (hp.1 h)
      have hm : D.mem s p.1 = false := D.mem_false_iff.2 hns
      simp only [hm, Bool.false_eq_true, if_false, set_of_notMem _ hns, List.filter_cons, hin, not_false_eq_true,
        decide_true, if_true, List.map_cons]
      rw [ih (s ++ [(p.1, absI p.2)]) hwt]
      · simp
      · intro q hq
        have hne : q.1 ≠ p.1 := by
          intro e
          exact hnot (e ▸ D.mem_keys_of_mem hq)
        have := hk q (List.mem_cons_of_mem _ hq)
        simp only [keys, List.map_append, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton] at this ⊢
        constructor
        · rintro (h | h)
          · exact this.1 h
          · exact absurd h hne
        · intro h
          exact Or.inl (this.2 h)

/-- `c ^= d` is `c ^ d` for two counters: the same items, in the same order. The two bodies are different: `__xor__` stores
only what is not zero, and `__ixor__` stores everything and then drops what is not positive. -/
theorem ixorC_eq {a b : Ctr κ} (ha : WF a) (hb : WF b) : ixorC a b = xorC a b := by
  have hA := ixor_first (fun p => absI (p.2 - cGet b p.1)) a [] (by simpa using ha)
  simp only [List.nil_append] at hA
  let A : Ctr κ := a.map (fun p => (p.1, absI (p.2 - cGet b p.1)))
  have hkA : keys A = keys a := by
    simp [A, keys, List.map_map, Function.comp_def]
  have hB := ixor_second a b A hb (fun p _ => by rw [hkA])
  let B : Ctr κ := (b.filter (fun p => decide (p.1 ∉ keys a))).map (fun p => (p.1, absI p.2))
  have hkB : keys B = (keys b).filter (fun x => decide (x ∉ keys a)) := by
    simp [B, keys, List.map_map, Function.comp_def, List.filter_map]
  have hwAB : WF (A ++ B) := by
    unfold WF
    rw [keys_append, hkA, hkB, List.nodup_append]
    refine ⟨ha, hb.filter _, ?_⟩
    intro x hx y hy e
    subst e
    simp only [List.mem_filter, decide_eq_true_eq] at hy
    exact hy.2 hx
  unfold ixorC ixorWith
  simp only [bind, Except.bind, pure, Except.pure]
  rw [foldlM_pure_xor]
  simp only
  rw [hA]
  change keepPositive (b.foldl _ A) = _
  rw [hB]
  change keepPositive (A ++ B) = _
  rw [keepPositive_eq hwAB, xorC_res ha hb]
  unfold res
  rw [List.filter_append]
  congr 1
  · apply filter_map_pos
    intro p _
    simp only [gXor]
    by_cases h : absI (p.2 - cGet b p.1) = 0
    · simp [h]
    · have := absI_pos _ h
      simp [h, this]
  · apply filter_map_filter_pos
    intro p _
    simp only [hXor, D.mem]
    by_cases hx : p.1 ∈ keys a
    · have : (D.get? a p.1).isSome = true := D.get?_isSome_iff.mpr hx
      simp [hx, this]
    · have h1 : (D.get? a p.1).isSome = false := by
        have := D.mem_false_iff.mpr hx
        simpa [D.mem] using this
      by_cases h0 : p.2 = 0
      · simp [hx, h1, h0, absI]
      · have := absI_pos _ (absI_ne _ h0)
        simp [hx, h1, h0, this]

/-- The docstring of `__xor__`: for each element the result is `max(p[e], q[e]) - min(p[e], q[e])`, the absolute difference, for
all counters, zero and negative counts included, and `p ^ q` is `(p - q) | (q - p)` item by item. Only positive counts are in
the result, in the order of the left operand and then of the right one. `^=` gives the same items in the same order, on a
`dict` a missing key is a `KeyError`, and a `Counter` guards `^` with `NotImplemented`. -/
def XorPointwise : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (a b : Ctr κ) (x : κ), WF a → WF b →
    cGet (xorC a b) x = absI (cGet a x - cGet b x) ∧
    cGet (xorC a b) x = max (cGet a x) (cGet b x) - min (cGet a x) (cGet b x) ∧
    cGet (xorC a b) x = cGet (orC (subC a b) (subC b a)) x ∧
    OutputContract (xorC a b) a b ∧
    ixorC a b = xorC a b ∧
    dunderIxor (fun _ => "k") a (.ctr b) = .ok (xorC a b) ∧
    guarded (xorC a) (.other : Opnd κ) = none

theorem xorPointwise_proven : XorPointwise := by
  intro κ _ a b x ha hb
  have h1 := cGet_xorC ha hb x
  have hs1 : WF (subC a b) := by
    rw [subC_res ha hb]
    exact res_WF (okSub ha hb)
  have hs2 : WF (subC b a) := by
    rw [subC_res hb ha]
    exact res_WF (okSub hb ha)
  refine ⟨h1, ?_, ?_, ?_, ixorC_eq ha hb, ?_, rfl⟩
  · rw [h1]
    unfold absI
    simp only [Int.max_def, Int.min_def]
    repeat' split
    all_goals omega
  · rw [h1, cGet_orC hs1 hs2, cGet_subC ha hb, cGet_subC hb ha]
    unfold absI
    simp only [Int.max_def]
    repeat' split
    all_goals omega
  · rw [xorC_res ha hb]
    exact contract_of (okXor ha hb)
  · have := ixorC_eq ha hb
    unfold ixorC at this
    simp only [dunderIxor]
    cases h : ixorWith a (fun e => .ok (cGet b e)) b with
    | error e =>
      exfalso
      unfold ixorWith at h
      simp only [bind, Except.bind, pure, Except.pure] at h
      rw [foldlM_pure_xor] at h
      simp at h
    | ok r =>
      rw [h] at this
      simp only at this
      rw [this]

end PyLean.CoreLibs.Coll
