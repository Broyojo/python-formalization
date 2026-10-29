import PyLean.Accel.HeapTwins

/-!
Correctness of the heap primitives for any strict weak order `lt` (Python's
`<` on ints, `maxLt` of it, and the lexicographic tuple orders used by
`nsmallest`/`nlargest`/`merge`). The proofs run on the C twins (whose loops
are sequences of swaps) and transfer to the Python twins through
`HeapTwins.lean`.

* `Desc s c`: position `c` is in the subtree rooted at `s` (children of `p`
  are `2p+1` and `2p+2`).
* `HeapIn lt l s`: every parent/child pair inside the subtree of `s` is in
  heap order (`not l[c] < l[parent]`).
* `IsHeap lt l = HeapIn lt l 0`: the heapq invariant `a[k] <= a[2k+1]`,
  `a[k] <= a[2k+2]` (Lib/heapq.py:3-4) read with `<=` as `not >`.
-/

namespace PyLean.Accel

open PyLean

/-- `lt` is a strict weak order. -/
structure StrictWeak {α : Type} (lt : α → α → Bool) : Prop where
  irrefl : ∀ a, lt a a = false
  trans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true
  negTrans : ∀ a b c, lt a c = true → lt a b = true ∨ lt b c = true

theorem StrictWeak.asymm {α : Type} {lt : α → α → Bool} (h : StrictWeak lt) (a b : α) (hab : lt a b = true) :
    lt b a = false := by
  cases hba : lt b a
  · rfl
  · have := h.trans _ _ _ hab hba; rw [h.irrefl] at this; cases this

/-- `not b < a` and `not c < b` give `not c < a`. -/
theorem StrictWeak.le_trans {α : Type} {lt : α → α → Bool} (h : StrictWeak lt) (a b c : α)
    (hab : lt b a = false) (hbc : lt c b = false) : lt c a = false := by
  cases hca : lt c a
  · rfl
  · rcases h.negTrans c b a hca with h1 | h1
    · rw [hbc] at h1; cases h1
    · rw [hab] at h1; cases h1

theorem StrictWeak.maxLt {α : Type} {lt : α → α → Bool} (h : StrictWeak lt) : StrictWeak (maxLt lt) where
  irrefl a := h.irrefl a
  trans _ _ _ hab hbc := h.trans _ _ _ hbc hab
  negTrans _ b _ hac := (h.negTrans _ b _ hac).symm

theorem strictWeak_int : StrictWeak (fun a b : Int => decide (a < b)) where
  irrefl a := by simp
  trans _ _ _ h1 h2 := by simp at *; omega
  negTrans _ _ _ h := by simp at *; omega

variable {α : Type} [Inhabited α]

/-! ### Subtrees -/

/-- `par c = (c - 1) >> 1`, the parent position. -/
abbrev par (c : Nat) : Nat := (c - 1) / 2

inductive Desc (s : Nat) : Nat → Prop
  | refl : Desc s s
  | left {c : Nat} : Desc s c → Desc s (2 * c + 1)
  | right {c : Nat} : Desc s c → Desc s (2 * c + 2)

theorem Desc.le {s c : Nat} (h : Desc s c) : s ≤ c := by
  induction h with
  | refl => exact Nat.le_refl _
  | left _ ih => omega
  | right _ ih => omega

theorem Desc.up {s c : Nat} (h : Desc s c) (hne : c ≠ s) : Desc s (par c) := by
  cases h with
  | refl => exact absurd rfl hne
  | @left c h => have : par (2 * c + 1) = c := by simp only [par]; omega
                 rw [this]; exact h
  | @right c h => have : par (2 * c + 2) = c := by simp only [par]; omega
                  rw [this]; exact h

theorem Desc.child {s p c : Nat} (h : Desc s p) (hc : par c = p) (h0 : c ≠ 0) : Desc s c := by
  rcases Nat.mod_two_eq_zero_or_one c with h2 | h2
  · have : c = 2 * p + 2 := by simp only [par] at hc; omega
    subst this; exact Desc.right h
  · have : c = 2 * p + 1 := by simp only [par] at hc; omega
    subst this; exact Desc.left h

theorem desc_zero : ∀ c, Desc 0 c := by
  intro c
  induction c using Nat.strongRecOn with
  | _ c ih =>
    by_cases h0 : c = 0
    · subst h0; exact Desc.refl
    · exact Desc.child (ih (par c) (by simp only [par]; omega)) rfl h0

theorem Desc.trans {a b c : Nat} (h1 : Desc a b) (h2 : Desc b c) : Desc a c := by
  induction h2 with
  | refl => exact h1
  | left _ ih => exact Desc.left ih
  | right _ ih => exact Desc.right ih

/-- Outside the subtree, a child's parent is also outside (or the child is the root). -/
theorem not_desc_par {s c : Nat} (h : ¬ Desc s c) (hc : c ≠ 0) (hs : c ≠ s) : ¬ Desc s (par c) :=
  fun hp => h (Desc.child hp rfl hc)

theorem shr1 (n : Nat) : n >>> 1 = n / 2 := by rw [Nat.shiftRight_eq_div_pow]

/-! ### Swaps -/

/-- `l` with positions `i` and `j` exchanged (the C sift step). -/
def sw (l : List α) (i j : Nat) : List α := (l.set i (at! l j)).set j (at! l i)

theorem sw_length (l : List α) (i j : Nat) : (sw l i j).length = l.length := by simp [sw]

theorem at!_sw (l : List α) (i j k : Nat) (hi : i < l.length) (hj : j < l.length) :
    at! (sw l i j) k = if k = j then at! l i else if k = i then at! l j else at! l k := by
  unfold sw
  rw [at!_set, List.length_set, at!_set]
  by_cases h1 : k = j
  · subst h1; rw [if_pos ⟨rfl, hj⟩, if_pos rfl]
  · rw [if_neg (fun h => h1 h.1.symm), if_neg h1]
    by_cases h2 : k = i
    · subst h2; rw [if_pos ⟨rfl, hi⟩, if_pos rfl]
    · rw [if_neg (fun h => h2 h.1.symm), if_neg h2]

theorem sw_perm (l : List α) (i j : Nat) (hi : i < l.length) (hj : j < l.length) :
    (sw l i j).Perm l := by
  have := List.set_set_perm (as := l) hi hj
  have e1 : at! l i = l[i] := by simp [at!, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have e2 : at! l j = l[j] := by simp [at!, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  simp only [sw, e1, e2]
  exact this

/-! ### Invariants -/

/-- The pair `(par c, c)` is in heap order. -/
def PairOk (lt : α → α → Bool) (l : List α) (c : Nat) : Prop := lt (at! l c) (at! l (par c)) = false

def HeapIn (lt : α → α → Bool) (l : List α) (s : Nat) : Prop :=
  ∀ c, c < l.length → Desc s c → c ≠ s → PairOk lt l c

def IsHeap (lt : α → α → Bool) (l : List α) : Prop := HeapIn lt l 0

/-- Bubbling up from `pos` towards `s`: every pair but `(par pos, pos)` is in
order, and `par pos` is no larger than the children of `pos`. -/
def UpInv (lt : α → α → Bool) (l : List α) (s pos : Nat) : Prop :=
  (∀ c, c < l.length → Desc s c → c ≠ s → c ≠ pos → PairOk lt l c) ∧
  (pos ≠ s → ∀ c, c < l.length → c ≠ 0 → par c = pos → lt (at! l c) (at! l (par pos)) = false) ∧
  Desc s pos

/-- Sinking from `pos` (Floyd's bottom-up pass): every pair not touching `pos`
is in order, and `par pos` is no larger than the children of `pos`. -/
def DownInv (lt : α → α → Bool) (l : List α) (s pos : Nat) : Prop :=
  (∀ c, c < l.length → Desc s c → c ≠ s → c ≠ pos → par c ≠ pos → PairOk lt l c) ∧
  (pos ≠ s → ∀ c, c < l.length → c ≠ 0 → par c = pos → lt (at! l c) (at! l (par pos)) = false) ∧
  Desc s pos

/-- Positions outside the subtree of `s` are unchanged. -/
def Frame (l l' : List α) (s : Nat) : Prop := ∀ p, ¬ Desc s p → at! l' p = at! l p

theorem Frame.refl (l : List α) (s : Nat) : Frame l l s := fun _ _ => rfl

theorem Frame.trans {l1 l2 l3 : List α} {s : Nat} (h1 : Frame l1 l2 s) (h2 : Frame l2 l3 s) :
    Frame l1 l3 s := fun p hp => (h2 p hp).trans (h1 p hp)

theorem frame_sw (l : List α) (s i j : Nat) (hi : i < l.length) (hj : j < l.length)
    (hdi : Desc s i) (hdj : Desc s j) : Frame l (sw l i j) s := by
  intro p hp
  rw [at!_sw l i j p hi hj]
  have : p ≠ j := fun e => hp (e ▸ hdj)
  have : p ≠ i := fun e => hp (e ▸ hdi)
  simp [*]

/-! ### The bubble-up loop (`siftdown`) -/

theorem cSiftdownLoop_correct {lt : α → α → Bool} (hlt : StrictWeak lt) (newitem : α) (s : Nat) :
    ∀ (fuel : Nat) (a : List α) (pos : Nat), pos < a.length → at! a pos = newitem →
      UpInv lt a s pos → pos ≤ fuel + s →
      let b := cSiftdownLoop lt newitem s fuel a pos
      HeapIn lt b s ∧ b.Perm a ∧ Frame a b s ∧ b.length = a.length := by
  intro fuel
  induction fuel with
  | zero =>
    intro a pos hpos hnew hinv hf
    have hps : pos = s := Nat.le_antisymm (by omega) hinv.2.2.le
    subst hps
    exact ⟨fun c h1 h2 h3 => hinv.1 c h1 h2 h3 h3, List.Perm.refl _, Frame.refl _ _, rfl⟩
  | succ fuel ih =>
    intro a pos hpos hnew hinv hf
    obtain ⟨h1, h2, hd⟩ := hinv
    simp only [cSiftdownLoop, shr1]
    by_cases hgt : pos > s
    · rw [if_pos hgt]
      have hne : pos ≠ s := by omega
      have hpp : par pos < pos := by simp only [par]; omega
      have hdp : Desc s (par pos) := hd.up hne
      have hpe : (pos - 1) / 2 = par pos := rfl
      rw [hpe]
      by_cases hl : lt newitem (at! a (par pos)) = true
      · rw [if_pos hl]
        have hb : (a.set (par pos) (at! a pos)).set pos (at! a (par pos)) = sw a (par pos) pos := rfl
        rw [hb]
        have hlen := sw_length a (par pos) pos
        have hat := fun k => at!_sw a (par pos) pos k (by omega) hpos
        have hpos' : par pos < (sw a (par pos) pos).length := by rw [hlen]; omega
        have hpnp : par pos ≠ pos := by omega
        have hnew' : at! (sw a (par pos) pos) (par pos) = newitem := by
          rw [hat]; simp only [hpnp, ↓reduceIte, hnew]
        have hinv' : UpInv lt (sw a (par pos) pos) s (par pos) := by
          refine ⟨?_, ?_, hdp⟩
          · intro c hc hdc hcs hcp
            rw [hlen] at hc
            unfold PairOk
            rw [hat c, hat (par c)]
            have hc0 : c ≠ 0 := by have := hdc.le; omega
            have hpc : par c < c := by simp only [par]; omega
            by_cases e1 : c = pos
            · subst e1
              simp only [hpnp, ↓reduceIte, hnew]
              exact hlt.asymm _ _ hl
            · by_cases e2 : par c = par pos
              · -- a sibling of pos
                have e3 : par c ≠ pos := by omega
                simp only [e1, e2, hcp, e3, hpnp, ↓reduceIte, hnew]
                have hok := h1 c hc hdc hcs e1
                unfold PairOk at hok
                rw [e2] at hok
                cases hcn : lt (at! a c) newitem
                · rfl
                · have := hlt.trans _ _ _ hcn hl; rw [hok] at this; cases this
              · by_cases e3 : par c = pos
                · simp only [e1, hcp, e3, ↓reduceIte]
                  exact h2 hne c hc hc0 e3
                · simp only [e1, hcp, e2, e3, ↓reduceIte]
                  exact h1 c hc hdc hcs e1
          · intro hps c hc hc0 hcp
            rw [hlen] at hc
            have hp1 : par pos ≥ 1 := by have := hdp.le; omega
            have hpar2 : par (par pos) ≠ pos := by unfold par at hp1 ⊢; omega
            have hpar3 : par (par pos) ≠ par pos := by unfold par at hp1 ⊢; omega
            rw [hat c, hat (par (par pos))]
            simp only [hpar2, hpar3, ↓reduceIte]
            have hokp := h1 (par pos) (by omega) hdp hps hpnp
            unfold PairOk at hokp
            by_cases e1 : c = pos
            · simp only [e1, ↓reduceIte]; exact hokp
            · have e2 : c ≠ par pos := by simp only [par] at *; omega
              simp only [e1, e2, ↓reduceIte]
              have hdc : Desc s c := Desc.child hdp hcp hc0
              have hcs : c ≠ s := by have := hdp.le; simp only [par] at *; omega
              have hokc := h1 c hc hdc hcs e1
              unfold PairOk at hokc
              rw [hcp] at hokc
              exact hlt.le_trans _ _ _ hokp hokc
        obtain ⟨r1, r2, r3, r4⟩ := ih (sw a (par pos) pos) (par pos) hpos' hnew' hinv' (by omega)
        exact ⟨r1, r2.trans (sw_perm a _ _ (by omega) hpos),
          (frame_sw a s _ _ (by omega) hpos hdp hd).trans r3, by rw [r4, hlen]⟩
      · rw [if_neg hl]
        simp only [Bool.not_eq_true] at hl
        refine ⟨?_, List.Perm.refl _, Frame.refl _ _, rfl⟩
        intro c hc hdc hcs
        by_cases e : c = pos
        · subst e; unfold PairOk; rw [hnew]; exact hl
        · exact h1 c hc hdc hcs e
    · rw [if_neg hgt]
      have hps : pos = s := Nat.le_antisymm (by omega) hd.le
      subst hps
      exact ⟨fun c h1' h2' h3' => h1 c h1' h2' h3' h3', List.Perm.refl _, Frame.refl _ _, rfl⟩

theorem cSiftdown_correct {lt : α → α → Bool} (hlt : StrictWeak lt) (a : List α) (s pos : Nat)
    (hpos : pos < a.length) (hinv : UpInv lt a s pos) :
    ∃ b, cSiftdown lt a s pos = .ok b ∧ HeapIn lt b s ∧ b.Perm a ∧ Frame a b s ∧ b.length = a.length := by
  simp only [cSiftdown, if_neg (Nat.not_le.2 hpos)]
  exact ⟨_, rfl, cSiftdownLoop_correct hlt (at! a pos) s pos a pos hpos rfl hinv (by omega)⟩

/-! ### The sink loop (`siftup`) -/

theorem cSiftupLoop_correct {lt : α → α → Bool} (hlt : StrictWeak lt) (s endpos : Nat) :
    ∀ (fuel : Nat) (a : List α) (pos : Nat), a.length = endpos → pos < a.length →
      DownInv lt a s pos → endpos ≤ fuel + pos →
      let r := cSiftupLoop lt endpos (endpos >>> 1) fuel a pos
      UpInv lt r.1 s r.2 ∧ at! r.1 r.2 = at! a pos ∧ r.2 < a.length ∧ r.1.Perm a ∧
        Frame a r.1 s ∧ r.1.length = a.length := by
  intro fuel
  induction fuel with
  | zero => intro a pos hl hpos _ hf; omega
  | succ fuel ih =>
    intro a pos hl hpos hinv hf
    obtain ⟨h1, h2, hd⟩ := hinv
    simp only [shr1] at ih
    simp only [cSiftupLoop, shr1]
    by_cases hlim : pos < endpos / 2
    · rw [if_pos hlim]
      have hc1 : 2 * pos + 1 < endpos := by omega
      -- the chosen child
      generalize hch : (if 2 * pos + 1 + 1 < endpos then
          (if lt (at! a (2 * pos + 1)) (at! a (2 * pos + 1 + 1)) = true then 2 * pos + 1
           else 2 * pos + 1 + 1) else 2 * pos + 1) = ch
      have hchp : par ch = pos ∧ pos < ch ∧ ch < endpos := by
        rw [← hch]; split
        · split <;> simp [par] <;> omega
        · simp [par]; omega
      have hmin : ∀ c, c < endpos → c ≠ 0 → par c = pos → lt (at! a c) (at! a ch) = false := by
        intro c hc hc0 hcp
        have hcc : c = 2 * pos + 1 ∨ c = 2 * pos + 2 := by simp [par] at hcp; omega
        rw [← hch]
        by_cases e2 : 2 * pos + 1 + 1 < endpos
        · rw [if_pos e2]
          by_cases e3 : lt (at! a (2 * pos + 1)) (at! a (2 * pos + 1 + 1)) = true
          · rw [if_pos e3]
            rcases hcc with rfl | rfl
            · exact hlt.irrefl _
            · exact hlt.asymm _ _ e3
          · rw [if_neg e3]
            simp only [Bool.not_eq_true] at e3
            rcases hcc with rfl | rfl
            · exact e3
            · exact hlt.irrefl _
        · rw [if_neg e2]
          rcases hcc with rfl | rfl
          · exact hlt.irrefl _
          · omega
      have hb : (a.set ch (at! a pos)).set pos (at! a ch) = sw a ch pos := rfl
      rw [hb]
      have hdch : Desc s ch := Desc.child hd hchp.1 (by omega)
      have hlen := sw_length a ch pos
      have hat := fun k => at!_sw a ch pos k (by omega) hpos
      have hinv' : DownInv lt (sw a ch pos) s ch := by
        refine ⟨?_, ?_, hdch⟩
        · intro c hc hdc hcs hcch hpch
          rw [hlen] at hc
          unfold PairOk
          rw [hat c, hat (par c)]
          by_cases e1 : c = pos
          · subst e1
            have hc1 : c ≥ 1 := by have := hdc.le; omega
            have hq1 : par c ≠ c := by unfold par; omega
            have hq2 : par c ≠ ch := by unfold par; omega
            simp only [hq1, hq2, ↓reduceIte]
            exact h2 hcs ch (by omega) (by omega) hchp.1
          · rw [if_neg e1, if_neg hcch]
            by_cases e2 : par c = pos
            · rw [if_pos e2]
              exact hmin c (by omega) (by intro h; subst h; have := hdc.le; omega) e2
            · rw [if_neg e2, if_neg hpch]
              exact h1 c hc hdc hcs e1 e2
        · intro hchs c hc hc0 hcp
          rw [hlen] at hc
          rw [hat c, hat (par ch), hchp.1, if_pos rfl]
          have hcpos : c ≠ pos := by simp [par] at hcp hchp; omega
          have hcch : c ≠ ch := by simp [par] at hcp; omega
          rw [if_neg hcpos, if_neg hcch]
          have := h1 c hc (Desc.child hdch hcp hc0) (by
            intro e; subst e; have := hdch.le; simp [par] at hcp; omega) hcpos (by rw [hcp]; omega)
          unfold PairOk at this
          rw [hcp] at this
          exact this
      have := ih (sw a ch pos) ch (by rw [hlen]; exact hl) (by rw [hlen]; omega) hinv' (by omega)
      obtain ⟨r1, r2, r3, r4, r5, r6⟩ := this
      refine ⟨r1, ?_, by rw [← hlen]; exact r3, r4.trans (sw_perm a _ _ (by omega) hpos),
        (frame_sw a s _ _ (by omega) hpos hdch hd).trans r5, by rw [r6, hlen]⟩
      rw [r2, hat, if_neg (by omega), if_pos rfl]
    · rw [if_neg hlim]
      dsimp only
      refine ⟨⟨?_, ?_, hd⟩, rfl, hpos, List.Perm.refl _, Frame.refl _ _, rfl⟩
      · intro c hc hdc hcs hcp
        refine h1 c hc hdc hcs hcp ?_
        intro e
        have hc1 : c ≥ 1 := by have := hdc.le; omega
        unfold par at e; omega
      · intro hps c hc hc0 hcp
        unfold par at hcp; omega

/-- `siftup` at `s` turns "heap below `s`" into "heap at `s`", permuting only
the subtree of `s`. -/
theorem cSiftup_correct {lt : α → α → Bool} (hlt : StrictWeak lt) (a : List α) (s : Nat)
    (hs : s < a.length)
    (hpre : ∀ c, c < a.length → Desc s c → c ≠ s → par c ≠ s → PairOk lt a c) :
    ∃ b, cSiftup lt a s = .ok b ∧ HeapIn lt b s ∧ b.Perm a ∧ Frame a b s ∧ b.length = a.length := by
  simp only [cSiftup, if_neg (Nat.not_le.2 hs)]
  have hinv : DownInv lt a s s := ⟨fun c h1 h2 h3 _ h5 => hpre c h1 h2 h3 h5, fun h => absurd rfl h, Desc.refl⟩
  obtain ⟨r1, -, r3, r4, r5, r6⟩ :=
    cSiftupLoop_correct hlt s a.length a.length a s rfl hs hinv (by omega)
  obtain ⟨b, hb1, hb2, hb3, hb4, hb5⟩ := cSiftdown_correct hlt _ s _ (by rw [r6]; exact r3) r1
  exact ⟨b, hb1, hb2, hb3.trans r4, r5.trans hb4, by rw [hb5, r6]⟩

theorem pySiftup_correct {lt : α → α → Bool} (hlt : StrictWeak lt) (a : List α) (s : Nat)
    (hs : s < a.length)
    (hpre : ∀ c, c < a.length → Desc s c → c ≠ s → par c ≠ s → PairOk lt a c) :
    HeapIn lt (pySiftup lt a s) s ∧ (pySiftup lt a s).Perm a ∧ Frame a (pySiftup lt a s) s := by
  obtain ⟨b, hb, h1, h2, h3, -⟩ := cSiftup_correct hlt a s hs hpre
  rw [cSiftup_eq lt a s hs] at hb
  cases hb
  exact ⟨h1, h2, h3⟩

theorem pySiftdown_correct {lt : α → α → Bool} (hlt : StrictWeak lt) (a : List α) (s pos : Nat)
    (hpos : pos < a.length) (hinv : UpInv lt a s pos) :
    HeapIn lt (pySiftdown lt a s pos) s ∧ (pySiftdown lt a s pos).Perm a := by
  obtain ⟨b, hb, h1, h2, -⟩ := cSiftdown_correct hlt a s pos hpos hinv
  rw [cSiftdown_eq lt a s pos hpos] at hb
  cases hb
  exact ⟨h1, h2⟩

end PyLean.Accel
