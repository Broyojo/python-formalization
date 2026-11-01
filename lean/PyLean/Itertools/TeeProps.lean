import PyLean.Itertools.GroupbyTee
import PyLean.Itertools.CombProps

/-!
`tee`: the C chain of `LINKCELLS`-sized `teedataobject` blocks (with
`jumplink` creating the next block lazily) simulates the doc's linked list of
`[value, next]` cells, for every interleaving of `next()`, `tee()` and
`__copy__()` on the returned iterators.
-/

namespace PyLean.Itertools

open PyLean

/-! ## Blocks -/

/-- Every block but the last is full. -/
def FullBlocks (bl : List (List Int)) : Prop :=
  ∀ j, j + 1 < bl.length → (bl.getD j []).length = LINKCELLS

theorem LINKCELLS_eq : LINKCELLS = 57 := rfl

theorem flat_getD : ∀ (bl : List (List Int)) (b i : Nat), FullBlocks bl → b < bl.length →
    i < (bl.getD b []).length → bl.flatten.getD (LINKCELLS * b + i) 0 = (bl.getD b []).getD i 0
  | [], _, _, _, h, _ => by simp at h
  | B :: rest, 0, i, _, _, hi => by
    simp only [List.getD_cons_zero] at hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  | B :: rest, b + 1, i, hf, hb, hi => by
    have hB : B.length = LINKCELLS := by have := hf 0 (by simp at hb ⊢; omega); simpa using this
    have hf' : FullBlocks rest := fun j hj => by
      have := hf (j + 1) (by simp; omega); simpa using this
    have ih := flat_getD rest b i hf' (by simp at hb; omega) (by simpa using hi)
    simp only [List.flatten_cons, List.getD_cons_succ] at ih ⊢
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hB]; simp [LINKCELLS]; omega), hB,
      show LINKCELLS * (b + 1) + i - LINKCELLS = LINKCELLS * b + i by simp [LINKCELLS]; omega,
      ← List.getD_eq_getElem?_getD, ih]

theorem flat_length : ∀ (bl : List (List Int)), bl ≠ [] → FullBlocks bl →
    bl.flatten.length = LINKCELLS * (bl.length - 1) + (bl.getD (bl.length - 1) []).length
  | [], h, _ => by simp at h
  | [B], _, _ => by simp
  | B :: C :: rest, _, hf => by
    have hB : B.length = LINKCELLS := by have := hf 0 (by simp); simpa using this
    have hf' : FullBlocks (C :: rest) := fun j hj => by
      have := hf (j + 1) (by simp at hj ⊢; omega); simpa using this
    have ih := flat_length (C :: rest) (by simp) hf'
    simp only [List.flatten_cons, List.length_append, List.length_cons] at ih ⊢
    rw [ih, hB]
    simp only [Nat.add_sub_cancel, List.getD_cons_succ]
    simp [LINKCELLS]; omega

theorem flat_set_last : ∀ (bl : List (List Int)) (v : Int), bl ≠ [] →
    (bl.set (bl.length - 1) (bl.getD (bl.length - 1) [] ++ [v])).flatten = bl.flatten ++ [v]
  | [], _, h => by simp at h
  | [B], v, _ => by simp
  | B :: C :: rest, v, _ => by
    have ih := flat_set_last (C :: rest) v (by simp)
    simp only [List.length_cons, Nat.add_sub_cancel] at ih ⊢
    simp only [List.set_cons_succ, List.flatten_cons, List.getD_cons_succ]
    rw [ih]; simp

theorem flat_len_ge (bl : List (List Int)) (hne : bl ≠ []) (hf : FullBlocks bl) (b : Nat)
    (hb : b < bl.length) : LINKCELLS * b + (bl.getD b []).length ≤ bl.flatten.length := by
  rw [flat_length bl hne hf]
  by_cases hl : b + 1 < bl.length
  · rw [hf b hl]
    have : LINKCELLS * b + LINKCELLS ≤ LINKCELLS * (bl.length - 1) := by
      have : b + 1 ≤ bl.length - 1 := by omega
      have := Nat.mul_le_mul_left LINKCELLS this
      simp [Nat.mul_add] at this; omega
    omega
  · obtain rfl : b = bl.length - 1 := by omega
    omega

/-! ## The simulation relation -/

/-- C tee `(block, index)` is at doc link number `p`. -/
def TeeAt (bl : List (List Int)) (bi : Nat × Nat) (p : Nat) : Prop :=
  bi.1 < bl.length ∧ bi.2 ≤ LINKCELLS ∧ bi.2 ≤ (bl.getD bi.1 []).length ∧ p = LINKCELLS * bi.1 + bi.2

structure TeeRel (c : CTee) (d : DocTee) : Prop where
  hit : c.it = d.it
  hvals : d.values = c.blocks.flatten
  hne : c.blocks ≠ []
  hfull : FullBlocks c.blocks
  hlast : (c.blocks.getD (c.blocks.length - 1) []).length ≤ LINKCELLS
  hlen : c.tees.length = d.tees.length
  htees : ∀ k, k < c.tees.length → TeeAt c.blocks (c.tees.getD k (0, 0)) (d.tees.getD k 0)

theorem blk_le (c : CTee) (d : DocTee) (h : TeeRel c d) (b : Nat) (hb : b < c.blocks.length) :
    (c.blocks.getD b []).length ≤ LINKCELLS := by
  by_cases hl : b + 1 < c.blocks.length
  · rw [h.hfull b hl]; exact Nat.le_refl _
  · have := h.hlast; rw [show c.blocks.length - 1 = b by omega] at this; exact this

/-- `getD` on a list after `set`. -/
theorem getD_set_eq {α : Type} (l : List α) (k : Nat) (v d : α) (hk : k < l.length) :
    (l.set k v).getD k d = v := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, hk]

theorem getD_set_ne {α : Type} (l : List α) (k j : Nat) (v d : α) (h : k ≠ j) :
    (l.set k v).getD j d = l.getD j d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, h]

theorem getD_append_lt {α : Type} (l m : List α) (j : Nat) (d : α) (h : j < l.length) :
    (l ++ m).getD j d = l.getD j d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

/-- After the jump, the C tee points into the chain at the same link, with
`index < LINKCELLS`. -/
theorem teeJump_rel (c : CTee) (d : DocTee) (h : TeeRel c d) (k b i : Nat) (hk : k < c.tees.length)
    (hbi : c.tees.getD k (0, 0) = (b, i)) :
    TeeRel { (teeJump c b i).1 with
      tees := (teeJump c b i).1.tees.set k ((teeJump c b i).2.1, (teeJump c b i).2.2) } d ∧
      (teeJump c b i).2.2 < LINKCELLS ∧ (teeJump c b i).1.tees = c.tees ∧ (teeJump c b i).1.it = c.it := by
  have hat := h.htees k hk
  rw [hbi] at hat
  obtain ⟨hb, hi, hil, hp⟩ := hat
  simp only at hb hi hil hp
  have L57 : LINKCELLS = 57 := rfl
  simp only [teeJump]
  by_cases hj : i ≥ LINKCELLS
  · have hfullb : (c.blocks.getD b []).length = LINKCELLS := by
      have := blk_le c d h b hb; omega
    simp only [hj, ↓reduceIte]
    by_cases hnext : b + 1 < c.blocks.length
    · simp only [hnext, ↓reduceIte]
      refine ⟨⟨h.hit, h.hvals, h.hne, h.hfull, h.hlast, by simp [h.hlen], ?_⟩, by simp [L57], by simp, by simp⟩
      intro j hj'
      simp only [List.length_set] at hj'
      by_cases hjk : k = j
      · subst hjk
        rw [getD_set_eq _ _ _ _ hk]
        refine ⟨hnext, by simp [L57], by simp, ?_⟩
        rw [hp]; simp only [L57] at hj ⊢; omega
      · rw [getD_set_ne _ _ _ _ _ hjk]; exact h.htees j hj'
    · simp only [hnext, ↓reduceIte]
      refine ⟨⟨h.hit, by rw [h.hvals]; simp, by simp, ?_, ?_, by simp [h.hlen], ?_⟩, by simp [L57],
        by simp, by simp⟩
      · intro j hj'
        simp only [List.length_append, List.length_cons, List.length_nil] at hj'
        rw [getD_append_lt _ _ _ _ (by omega)]
        by_cases hjl : j + 1 < c.blocks.length
        · exact h.hfull j hjl
        · rw [show j = b by omega]; exact hfullb
      · simp [List.getD_eq_getElem?_getD]
      · intro j hj'
        simp only [List.length_set] at hj'
        by_cases hjk : k = j
        · subst hjk
          rw [getD_set_eq _ _ _ _ hk]
          refine ⟨by simp; omega, by simp [L57], by simp, ?_⟩
          rw [hp]; simp only [L57] at hj ⊢; omega
        · rw [getD_set_ne _ _ _ _ _ hjk]
          obtain ⟨h1, h2, h3, h4⟩ := h.htees j hj'
          exact ⟨by simp only [List.length_append, List.length_cons, List.length_nil]; omega, h2,
            by rw [getD_append_lt _ _ _ _ h1]; exact h3, h4⟩
  · simp only [hj, ↓reduceIte]
    refine ⟨⟨h.hit, h.hvals, h.hne, h.hfull, h.hlast, by simp [h.hlen], ?_⟩, by omega, by simp, by simp⟩
    intro j hj'
    simp only [List.length_set] at hj'
    by_cases hjk : k = j
    · subst hjk
      rw [getD_set_eq _ _ _ _ hk]
      exact ⟨hb, hi, hil, hp⟩
    · rw [getD_set_ne _ _ _ _ _ hjk]; exact h.htees j hj'

theorem teeGetitem_rel (c : CTee) (d : DocTee) (h : TeeRel c d) (k b i : Nat) (hk : k < c.tees.length)
    (hbi : c.tees.getD k (0, 0) = (b, i)) (hi : i < LINKCELLS) :
    (teeGetitem c k b i).1 = (docTeeNext d k).1 ∧ TeeRel (teeGetitem c k b i).2 (docTeeNext d k).2 := by
  have hat := h.htees k hk
  rw [hbi] at hat
  obtain ⟨hb, -, hil, hp⟩ := hat
  simp only at hb hil hp
  have hkd : k < d.tees.length := by rw [← h.hlen]; exact hk
  have L57 : LINKCELLS = 57 := rfl
  simp only [teeGetitem, docTeeNext]
  by_cases hlt : i < (c.blocks.getD b []).length
  · have hge := flat_len_ge c.blocks h.hne h.hfull b hb
    have hpv : d.tees.getD k 0 < d.values.length := by rw [h.hvals, hp]; omega
    simp only [hlt, ↓reduceIte, hpv]
    refine ⟨?_, ⟨h.hit, h.hvals, h.hne, h.hfull, h.hlast, by simp [h.hlen], ?_⟩⟩
    · rw [h.hvals, hp, flat_getD c.blocks b i h.hfull hb hlt]
    · intro j hj
      simp only [List.length_set] at hj
      by_cases hjk : k = j
      · subst hjk
        rw [getD_set_eq _ _ _ _ hk, getD_set_eq _ _ _ _ hkd]
        refine ⟨hb, show i + 1 ≤ LINKCELLS by omega, show i + 1 ≤ (c.blocks.getD b []).length by omega,
          show d.tees.getD k 0 + 1 = LINKCELLS * b + (i + 1) by omega⟩
      · rw [getD_set_ne _ _ _ _ _ hjk, getD_set_ne _ _ _ _ _ hjk]; exact h.htees j hj
  · have hieq : i = (c.blocks.getD b []).length := by omega
    have hlastb : b = c.blocks.length - 1 := by
      by_cases hl : b + 1 < c.blocks.length
      · have := h.hfull b hl; omega
      · omega
    have hlen := flat_length c.blocks h.hne h.hfull
    have hpv : ¬ d.tees.getD k 0 < d.values.length := by rw [h.hvals, hp, hlen, ← hlastb]; omega
    simp only [hlt, ↓reduceIte, hpv, ← h.hit]
    cases hit : c.it with
    | nil => exact ⟨rfl, h⟩
    | cons v rest =>
      simp only
      have hpl : d.tees.getD k 0 = d.values.length := by rw [h.hvals, hp, hlen, ← hlastb]; omega
      refine ⟨?_, ⟨by simp, ?_, ?_, ?_, ?_, by simp [h.hlen], ?_⟩⟩
      · rw [hpl]; simp [List.getD_eq_getElem?_getD]
      · rw [h.hvals, hlastb, flat_set_last c.blocks v h.hne]
      · simp [h.hne]
      · intro j hj
        simp only [List.length_set] at hj
        rw [getD_set_ne _ _ _ _ _ (by omega)]
        exact h.hfull j hj
      · simp only [List.length_set]
        rw [← hlastb, getD_set_eq _ _ _ _ hb]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · intro j hj
        simp only [List.length_set] at hj
        by_cases hjk : k = j
        · subst hjk
          rw [getD_set_eq _ _ _ _ hk, getD_set_eq _ _ _ _ hkd]
          refine ⟨by simp only [List.length_set]; exact hb, show i + 1 ≤ LINKCELLS by omega, ?_,
            show d.tees.getD k 0 + 1 = LINKCELLS * b + (i + 1) by omega⟩
          show i + 1 ≤ ((c.blocks.set b (c.blocks.getD b [] ++ [v])).getD b []).length
          rw [getD_set_eq _ _ _ _ hb]
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        · rw [getD_set_ne _ _ _ _ _ hjk, getD_set_ne _ _ _ _ _ hjk]
          obtain ⟨h1, h2, h3, h4⟩ := h.htees j hj
          refine ⟨by simp only [List.length_set]; exact h1, h2, ?_, h4⟩
          by_cases hb' : b = (c.tees.getD j (0, 0)).1
          · rw [← hb', getD_set_eq _ _ _ _ hb]; rw [← hb'] at h3
            simp only [List.length_append, List.length_cons, List.length_nil]; omega
          · rw [getD_set_ne _ _ _ _ _ hb']; exact h3

theorem teeNext_rel (c : CTee) (d : DocTee) (h : TeeRel c d) (k : Nat) (hk : k < c.tees.length) :
    (cTeeNext c k).1 = (docTeeNext d k).1 ∧ TeeRel (cTeeNext c k).2 (docTeeNext d k).2 := by
  cases hbi : c.tees.getD k (0, 0) with
  | mk b i =>
    have hj := teeJump_rel c d h k b i hk hbi
    cases hr : teeJump c b i with
    | mk c1 rest =>
      cases rest with
      | mk b1 i1 =>
        rw [hr] at hj
        simp only at hj
        obtain ⟨hrel, hi1, htees, _⟩ := hj
        have hc : cTeeNext c k = teeGetitem { c1 with tees := c1.tees.set k (b1, i1) } k b1 i1 := by
          simp only [cTeeNext, hbi, hr]
        rw [hc]
        have hk1 : k < c1.tees.length := by rw [htees]; exact hk
        exact teeGetitem_rel _ d hrel k b1 i1 (by simpa using hk1)
          (getD_set_eq _ _ _ _ hk1) hi1

/-- `tee(t_k, m)` / `t_k.__copy__()`: `m` more iterators at the same position. -/
theorem teeRel_extend (c : CTee) (d : DocTee) (h : TeeRel c d) (k m : Nat) (hk : k < c.tees.length) :
    TeeRel { c with tees := c.tees ++ List.replicate m (c.tees.getD k (0, 0)) }
      { d with tees := d.tees ++ List.replicate m (d.tees.getD k 0) } := by
  refine ⟨h.hit, h.hvals, h.hne, h.hfull, h.hlast, by simp [h.hlen], ?_⟩
  intro j hj
  simp only [List.length_append, List.length_replicate] at hj
  by_cases hjl : j < c.tees.length
  · rw [getD_append_lt _ _ _ _ hjl, getD_append_lt _ _ _ _ (by rw [← h.hlen]; exact hjl)]
    exact h.htees j hjl
  · have h1 : (c.tees ++ List.replicate m (c.tees.getD k (0, 0))).getD j (0, 0) = c.tees.getD k (0, 0) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_of_not_lt hjl),
        List.getElem?_replicate, show j - c.tees.length < m by omega]
    have h2 : (d.tees ++ List.replicate m (d.tees.getD k 0)).getD j 0 = d.tees.getD k 0 := by
      have hjd : d.tees.length ≤ j := by rw [← h.hlen]; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hjd,
        List.getElem?_replicate, show j - d.tees.length < m by rw [← h.hlen]; omega]
    rw [h1, h2]
    exact h.htees k hk

theorem teeOps_rel : ∀ (ops : List TeeOp) (c : CTee) (d : DocTee), TeeRel c d →
    (cTeeOps c ops).1 = (docTeeOps d ops).1 ∧ TeeRel (cTeeOps c ops).2 (docTeeOps d ops).2
  | [], _, _, h => ⟨rfl, h⟩
  | .next k :: ops, c, d, h => by
    simp only [cTeeOps, docTeeOps, ← h.hlen]
    by_cases hk : k < c.tees.length
    · have hs := teeNext_rel c d h k hk
      have ih := teeOps_rel ops _ _ hs.2
      simp only [hk, ↓reduceIte]
      exact ⟨by simp [hs.1, ih.1], ih.2⟩
    · simp only [hk, ↓reduceIte]
      exact teeOps_rel ops c d h
  | .tee k m :: ops, c, d, h => by
    simp only [cTeeOps, docTeeOps, ← h.hlen]
    by_cases hk : k < c.tees.length
    · simp only [hk, ↓reduceIte]
      exact teeOps_rel ops _ _ (teeRel_extend c d h k m hk)
    · simp only [hk, ↓reduceIte]
      exact teeOps_rel ops c d h
  | .copy k :: ops, c, d, h => by
    simp only [cTeeOps, docTeeOps, ← h.hlen]
    by_cases hk : k < c.tees.length
    · simp only [hk, ↓reduceIte]
      exact teeOps_rel ops _ _ (teeRel_extend c d h k 1 hk)
    · simp only [hk, ↓reduceIte]
      exact teeOps_rel ops c d h

/-- Both give the same value, or both raise (the doc's `ValueError` is bare). -/
def pyAgree {β : Type} : Py β → Py β → Prop
  | .ok x, .ok y => x = y
  | .error _, .error _ => True
  | _, _ => False

/-- For every int `n` whose `n`-tuple of iterators fits in memory, and every
interleaving of `next()`, `tee()` and `__copy__()` on the iterators, the C
block chain (including the jump at `LINKCELLS` items and exhausted iterators
that are retried) gives the doc's linked-list results and pulls the same
number of input items; for `n < 0` both raise. -/
def TeeDocAgree : Prop :=
  ∀ (l : List Int) (n : Int) (ops : List TeeOp), (0 ≤ n → tupleNewOk n = true) →
    pyAgree (cTee l n ops) (docTee l n ops)

theorem teeDocAgree_proven : TeeDocAgree := by
  intro l n ops ht
  by_cases hn : n < 0
  · have hd : docTee l n ops = .error (.valueError "") := by simp [docTee, hn, throw, throwThe,
      MonadExceptOf.throw, bind, Except.bind]
    have hc : ∃ e, cTee l n ops = .error e := by
      cases ha : asSsize n with
      | error e => exact ⟨e, by simp [cTee, ha, bind, Except.bind]⟩
      | ok v =>
        have hv : v = n := by simp only [asSsize] at ha; split at ha <;> simp_all
        subst hv
        exact ⟨.valueError "n must be >= 0",
          by simp [cTee, ha, hn, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]⟩
    obtain ⟨e, he⟩ := hc
    rw [hd, he]
    trivial
  · have h0 : 0 ≤ n := by omega
    have htn := ht h0
    have hle : n ≤ ssizeMax := by
      simp only [tupleNewOk, ssizeMax_eq, mallocLimit_eq, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
        decide_eq_true_eq] at htn ⊢
      omega
    have hrel : TeeRel { it := l, blocks := [[]], tees := List.replicate n.toNat (0, 0) }
        { it := l, values := [], tees := List.replicate n.toNat 0 } := by
      refine ⟨rfl, by simp, by simp, ?_, by simp [LINKCELLS], by simp, ?_⟩
      · intro j hj; simp at hj
      · intro j hj
        simp only [List.length_replicate] at hj
        have h1 : (List.replicate n.toNat ((0 : Nat), (0 : Nat))).getD j (0, 0) = (0, 0) := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, hj, ↓reduceIte,
            Option.getD_some]
        have h2 : (List.replicate n.toNat (0 : Nat)).getD j 0 = 0 := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, hj, ↓reduceIte,
            Option.getD_some]
        rw [h1, h2]
        simp [TeeAt, LINKCELLS]
    have hops := teeOps_rel ops _ _ hrel
    simp only [cTee, docTee, asSsize_ok (by rw [ssizeMin_eq]; omega) hle, hn, htn, ↓reduceIte,
      Bool.not_true, Bool.false_eq_true, bind, Except.bind, pure, Except.pure, pyAgree]
    rw [hops.1, hops.2.hit]

end PyLean.Itertools
