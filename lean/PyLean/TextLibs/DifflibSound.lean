import PyLean.TextLibs.DifflibProps

/-!
`find_longest_match` returns a match inside its box, whatever `isjunk` and the popular test removed from
`b2j`, and `get_matching_blocks` and `get_opcodes` build on that.
-/

namespace PyLean.TextLibs.Difflib

open PyLean

/-- The entries of `j2len`, at row `i`: `j -> k` is a match of length `k` ending just before `(i, j+1)`. -/
def RowOk (s : SM) (alo blo bhi i : Nat) (m : List (Nat × Nat)) : Prop :=
  ∀ j k, m.lookup j = some k → 1 ≤ k ∧ alo + k ≤ i ∧ blo + k ≤ j + 1 ∧ j < bhi ∧
    Eqs s.a s.b (i - k) (j + 1 - k) k

/-- The best so far, with its end in `a` at most `h`. -/
def BestOk (s : SM) (alo blo bhi h : Nat) (b : Best) : Prop :=
  alo ≤ b.1 ∧ b.1 + b.2.2 ≤ h ∧ blo ≤ b.2.1 ∧ b.2.1 + b.2.2 ≤ bhi ∧ Eqs s.a s.b b.1 b.2.1 b.2.2

theorem j2get_ok (s : SM) (alo blo bhi i j : Nat) (old : List (Nat × Nat)) (hi : i ≤ s.a.length)
    (hj : j ≤ s.b.length) (halo : alo ≤ i) (hblo : blo ≤ j) (hold : RowOk s alo blo bhi i old) :
    alo + j2get old j ≤ i ∧ blo + j2get old j ≤ j ∧ Eqs s.a s.b (i - j2get old j) (j - j2get old j) (j2get old j) := by
  have base : alo + 0 ≤ i ∧ blo + 0 ≤ j ∧ Eqs s.a s.b (i - 0) (j - 0) 0 :=
    ⟨by omega, by omega, eqs_zero _ _ _ _ (by omega) (by omega)⟩
  cases j with
  | zero => exact base
  | succ j =>
    simp only [j2get]
    cases hl : old.lookup j with
    | none => exact base
    | some v =>
      obtain ⟨h1, h2, h3, _, h5⟩ := hold j v hl
      simpa using ⟨h2, by omega, h5⟩

theorem inner_ok (s : SM) (alo blo bhi i x : Nat) (old : List (Nat × Nat)) (hi : s.a[i]? = some x)
    (halo : alo ≤ i) (hbhi : bhi ≤ s.b.length) (hold : RowOk s alo blo bhi i old) :
    ∀ (l : List Nat) (new : List (Nat × Nat)) (best : Best), (∀ j ∈ l, s.b[j]? = some x) →
      RowOk s alo blo bhi (i + 1) new → BestOk s alo blo bhi (i + 1) best →
      RowOk s alo blo bhi (i + 1) (innerLoop blo bhi i old l new best).1 ∧
      BestOk s alo blo bhi (i + 1) (innerLoop blo bhi i old l new best).2 := by
  have hlen : i < s.a.length := by
    rcases List.getElem?_eq_some_iff.mp hi with ⟨h, _⟩
    exact h
  intro l
  induction l with
  | nil => intro new best _ h1 h2; exact ⟨h1, h2⟩
  | cons j r ih =>
    intro new best hl h1 h2
    have hr : ∀ y ∈ r, s.b[y]? = some x := fun y hy => hl y (by simp [hy])
    simp only [innerLoop]
    split
    · exact ih new best hr h1 h2
    · rename_i hb
      split
      · exact ⟨h1, h2⟩
      · rename_i hb2
        have hj : s.b[j]? = some x := hl j (by simp)
        have hjl : j < s.b.length := by
          rcases List.getElem?_eq_some_iff.mp hj with ⟨h, _⟩
          exact h
        obtain ⟨g1, g2, g3⟩ := j2get_ok s alo blo bhi i j old (by omega) (by omega) halo (by omega) hold
        generalize hg : j2get old j = g at g1 g2 g3
        have ext : Eqs s.a s.b (i - g) (j - g) (g + 1) := by
          refine eqs_right g3 ?_ ?_ ?_
          · omega
          · omega
          · have e1 : i - g + g = i := by omega
            have e2 : j - g + g = j := by omega
            rw [e1, e2, hi, hj]
        have hnew : RowOk s alo blo bhi (i + 1) ((j, g + 1) :: new) := by
          intro y v hv
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
        have hbest : BestOk s alo blo bhi (i + 1)
            (if g + 1 > best.2.2 then (i + 1 - (g + 1), j + 1 - (g + 1), g + 1) else best) := by
          split
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
        exact ih _ _ hr hnew hbest

theorem at_ok (l : List Nat) (i : Nat) (h : i < l.length) : ∃ x, at? l i = .ok x ∧ l[i]? = some x := by
  refine ⟨l[i], ?_, List.getElem?_eq_getElem h⟩
  simp [at?, List.getElem?_eq_getElem h]

theorem lookupIdx_ok (s : SM) (hs : Ready s) (x : Nat) : ∀ j ∈ lookupIdx s.b2j x, s.b[j]? = some x := by
  intro j hj
  unfold lookupIdx at hj
  cases hl : s.b2j.lookup x with
  | none => simp [hl] at hj
  | some l =>
    rw [hl] at hj
    exact (hs x l hl).1 j hj

theorem bestOk_mono {s : SM} {alo blo bhi h h' : Nat} {b : Best} (hb : BestOk s alo blo bhi h b) (hh : h ≤ h') :
    BestOk s alo blo bhi h' b :=
  ⟨hb.1, by have := hb.2.1; omega, hb.2.2⟩

theorem outer_ok (s : SM) (hs : Ready s) (alo blo bhi ahi : Nat) (ha : ahi ≤ s.a.length) (hb : bhi ≤ s.b.length) :
    ∀ (fuel i : Nat) (old : List (Nat × Nat)) (best : Best), i + fuel = ahi → alo ≤ i →
      RowOk s alo blo bhi i old → BestOk s alo blo bhi i best →
      ∃ b', outerLoop s blo bhi ahi fuel i old best = .ok b' ∧ BestOk s alo blo bhi ahi b' := by
  intro fuel
  induction fuel with
  | zero =>
    intro i old best h1 _ _ h4
    refine ⟨best, rfl, ?_⟩
    have : i = ahi := by omega
    subst this
    exact h4
  | succ f ih =>
    intro i old best h1 h2 h3 h4
    obtain ⟨x, hx, hxa⟩ := at_ok s.a i (by omega)
    have hin := inner_ok s alo blo bhi i x old hxa h2 hb h3 (lookupIdx s.b2j x) [] best (lookupIdx_ok s hs x)
      (by intro j k hl; simp at hl) (bestOk_mono h4 (by omega))
    simp only [outerLoop, hx]
    exact ih (i + 1) _ _ (by omega) (by omega) hin.1 hin.2

theorem extTest_ok (s : SM) (junk : Bool) (ia ib : Nat) (ha : ia < s.a.length) (hb : ib < s.b.length) :
    ∃ r : Bool, extTest s junk ia ib = .ok r ∧ (r = true → s.a[ia]? = s.b[ib]?) := by
  obtain ⟨y, hy, hyb⟩ := at_ok s.b ib hb
  obtain ⟨x, hx, hxa⟩ := at_ok s.a ia ha
  simp only [extTest, hy]
  split
  · exact ⟨false, rfl, by simp⟩
  · simp only [hx]
    refine ⟨x == y, rfl, ?_⟩
    intro h
    have : x = y := by simpa using h
    rw [hxa, hyb, this]

/-- The block keeps its end and grows to the left. -/
theorem extL_ok (s : SM) (junk : Bool) (alo blo : Nat) : ∀ (f i j k : Nat), Eqs s.a s.b i j k → alo ≤ i → blo ≤ j →
    ∃ i' j' k', extendLeft s junk alo blo f (i, j, k) = .ok (i', j', k') ∧ Eqs s.a s.b i' j' k' ∧
      alo ≤ i' ∧ blo ≤ j' ∧ i' + k' = i + k ∧ j' + k' = j + k := by
  intro f
  induction f with
  | zero =>
    intro i j k h h1 h2
    exact ⟨i, j, k, rfl, h, h1, h2, rfl, rfl⟩
  | succ f ih =>
    intro i j k h h1 h2
    simp only [extendLeft]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨c1, c2⟩ := hc
      obtain ⟨r, hr, he⟩ := extTest_ok s junk (i - 1) (j - 1) (by have := h.1; omega) (by have := h.2.1; omega)
      rw [hr]
      cases r with
      | true =>
        simp only
        have e1 : i = (i - 1) + 1 := by omega
        have e2 : j = (j - 1) + 1 := by omega
        have h' : Eqs s.a s.b ((i - 1) + 1) ((j - 1) + 1) k := by rw [← e1, ← e2]; exact h
        obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ :=
          ih (i - 1) (j - 1) (k + 1) (eqs_left h' (he rfl)) (by omega) (by omega)
        exact ⟨a1, a2, a3, a4, a5, a6, a7, by omega, by omega⟩
      | false => exact ⟨i, j, k, rfl, h, h1, h2, rfl, rfl⟩
    · exact ⟨i, j, k, rfl, h, h1, h2, rfl, rfl⟩

/-- The block keeps its start and grows to the right, up to the box. -/
theorem extR_ok (s : SM) (junk : Bool) (ahi bhi : Nat) (hA : ahi ≤ s.a.length) (hB : bhi ≤ s.b.length) :
    ∀ (f i j k : Nat), Eqs s.a s.b i j k →
    i + k ≤ ahi → j + k ≤ bhi →
    ∃ k', extendRight s junk ahi bhi f (i, j, k) = .ok (i, j, k') ∧ Eqs s.a s.b i j k' ∧
      i + k' ≤ ahi ∧ j + k' ≤ bhi ∧ k ≤ k' := by
  intro f
  induction f with
  | zero =>
    intro i j k h h1 h2
    exact ⟨k, rfl, h, h1, h2, Nat.le_refl _⟩
  | succ f ih =>
    intro i j k h h1 h2
    simp only [extendRight]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨c1, c2⟩ := hc
      have ha : i + k < s.a.length := by omega
      have hb : j + k < s.b.length := by omega
      obtain ⟨r, hr, he⟩ := extTest_ok s junk (i + k) (j + k) ha hb
      rw [hr]
      cases r with
      | true =>
        simp only
        obtain ⟨k', a1, a2, a3, a4, a5⟩ := ih i j (k + 1) (eqs_right h ha hb (he rfl)) (by omega) (by omega)
        exact ⟨k', a1, a2, a3, a4, by omega⟩
      | false => exact ⟨k, rfl, h, h1, h2, Nat.le_refl _⟩
    · exact ⟨k, rfl, h, h1, h2, Nat.le_refl _⟩

/-- `find_longest_match` on a box in range: it returns, and the block is a real match inside the box. -/
theorem findLongest_ok (s : SM) (hs : Ready s) (alo ahi blo bhi : Nat) (h1 : alo ≤ ahi) (h2 : ahi ≤ s.a.length)
    (h3 : blo ≤ bhi) (h4 : bhi ≤ s.b.length) :
    ∃ i j k, findLongest s alo ahi blo bhi = .ok (i, j, k) ∧ alo ≤ i ∧ i + k ≤ ahi ∧ blo ≤ j ∧ j + k ≤ bhi ∧
      Eqs s.a s.b i j k := by
  obtain ⟨b, hb, b1, b2, b3, b4, b5⟩ := outer_ok s hs alo blo bhi ahi h2 h4 (ahi - alo) alo [] (alo, blo, 0)
    (by omega) (by omega) (by intro j k hl; simp at hl)
    ⟨Nat.le_refl _, by simp, Nat.le_refl _, by simpa using h3, eqs_zero _ _ _ _ (by simp only; omega) (by simp only; omega)⟩
  obtain ⟨i0, j0, k0⟩ := b
  simp only at b1 b2 b3 b4 b5
  obtain ⟨i1, j1, k1, l1, l2, l3, l4, l5, l6⟩ := extL_ok s false alo blo (ahi + bhi + 1) i0 j0 k0 b5 b1 b3
  obtain ⟨k2, r1, r2, r3, r4, r5⟩ := extR_ok s false ahi bhi h2 h4 (ahi + bhi + 1) i1 j1 k1 l2 (by omega) (by omega)
  obtain ⟨i3, j3, k3, m1, m2, m3, m4, m5, m6⟩ := extL_ok s true alo blo (ahi + bhi + 1) i1 j1 k2 r2 l3 l4
  obtain ⟨k4, n1, n2, n3, n4, n5⟩ := extR_ok s true ahi bhi h2 h4 (ahi + bhi + 1) i3 j3 k3 m2 (by omega) (by omega)
  refine ⟨i3, j3, k4, ?_, m3, n3, m4, n4, n2⟩
  simp only [findLongest, hb, l1, r1, m1, n1]

/-! ### The queue -/

/-- A block as a box. -/
def toBox (t : T) : Box := (t.1, t.1 + t.2.2, t.2.1, t.2.1 + t.2.2)

/-- `x` is entirely before `y`, in both sequences. -/
def Bf (x y : Box) : Prop := x.2.1 ≤ y.1 ∧ x.2.2.2 ≤ y.2.2.1

def Rel (x y : Box) : Prop := Bf x y ∨ Bf y x

/-- `y` is inside `x`. -/
def Sub (y x : Box) : Prop := x.1 ≤ y.1 ∧ y.2.1 ≤ x.2.1 ∧ x.2.2.1 ≤ y.2.2.1 ∧ y.2.2.2 ≤ x.2.2.2

def BoxOk (s : SM) (x : Box) : Prop := x.1 ≤ x.2.1 ∧ x.2.1 ≤ s.a.length ∧ x.2.2.1 ≤ x.2.2.2 ∧ x.2.2.2 ≤ s.b.length

theorem rel_sub {x y z : Box} (h : Rel x z) (hs : Sub y x) : Rel y z := by
  obtain ⟨s1, s2, s3, s4⟩ := hs
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact .inl ⟨by omega, by omega⟩
  · exact .inr ⟨by omega, by omega⟩

theorem rel_symm {x y : Box} (h : Rel x y) : Rel y x := h.symm

structure LoopInv (s : SM) (q : List Box) (found : List T) : Prop where
  boxes : ∀ x ∈ q, BoxOk s x
  blocks : ∀ t ∈ found, 1 ≤ t.2.2 ∧ Eqs s.a s.b t.1 t.2.1 t.2.2
  pq : q.Pairwise Rel
  pf : found.Pairwise (fun u v => Rel (toBox u) (toBox v))
  cross : ∀ x ∈ q, ∀ t ∈ found, Rel x (toBox t)

theorem inv_push {s : SM} {q : List Box} {found : List T} (Z : Box) (hb : BoxOk s Z)
    (h1 : ∀ x ∈ q, Rel Z x) (h2 : ∀ t ∈ found, Rel Z (toBox t)) (h : LoopInv s q found) :
    LoopInv s (Z :: q) found := by
  refine ⟨?_, h.blocks, ?_, h.pf, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hb
    · exact h.boxes x hx
  · exact List.pairwise_cons.mpr ⟨h1, h.pq⟩
  · intro x hx t ht
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h2 t ht
    · exact h.cross x hx t ht

/-- The bound on the steps of the queue. -/
def blockMeasure : List Box → Nat
  | [] => 0
  | x :: r => 2 * (x.2.1 - x.1) + 1 + blockMeasure r

theorem block_loop (s : SM) (hs : Ready s) : ∀ (fuel : Nat) (q : List Box) (found : List T),
    blockMeasure q < fuel → LoopInv s q found →
    ∃ r, blockLoop s fuel q found = .ok r ∧ LoopInv s [] r := by
  intro fuel
  induction fuel with
  | zero => intro _ _ h; omega
  | succ f ih =>
    intro q found hm hi
    cases q with
    | nil => exact ⟨found, by simp [blockLoop], hi⟩
    | cons X q' =>
      obtain ⟨alo, ahi, blo, bhi⟩ := X
      have hX : BoxOk s (alo, ahi, blo, bhi) := hi.boxes _ (by simp)
      obtain ⟨x1, x2, x3, x4⟩ := hX
      simp only at x1 x2 x3 x4
      obtain ⟨i, j, k, he, b1, b2, b3, b4, b5⟩ := findLongest_ok s hs alo ahi blo bhi x1 x2 x3 x4
      have hrelq : ∀ z ∈ q', Rel (alo, ahi, blo, bhi) z := (List.pairwise_cons.mp hi.pq).1
      have hrelf : ∀ t ∈ found, Rel (alo, ahi, blo, bhi) (toBox t) := hi.cross _ (by simp)
      have hq' : LoopInv s q' found :=
        ⟨fun x hx => hi.boxes x (by simp [hx]), hi.blocks, (List.pairwise_cons.mp hi.pq).2, hi.pf,
          fun x hx t ht => hi.cross x (by simp [hx]) t ht⟩
      simp only [blockMeasure] at hm
      simp only [blockLoop, he]
      by_cases hk : k = 0
      · subst hk
        simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
        exact ih q' found (by omega) hq'
      · have hk' : (k != 0) = true := by simpa using hk
        simp only [hk', if_true]
        have subY : Sub (toBox (i, j, k)) (alo, ahi, blo, bhi) := ⟨b1, b2, b3, b4⟩
        have inv1 : LoopInv s q' ((i, j, k) :: found) := by
          refine ⟨hq'.boxes, ?_, hq'.pq, ?_, ?_⟩
          · intro t ht
            rcases List.mem_cons.mp ht with rfl | ht
            · exact ⟨by simp only; omega, b5⟩
            · exact hi.blocks t ht
          · exact List.pairwise_cons.mpr ⟨fun t ht => rel_sub (hrelf t ht) subY, hi.pf⟩
          · intro x hx t ht
            rcases List.mem_cons.mp ht with rfl | ht
            · exact rel_symm (rel_sub (hrelq x hx) subY)
            · exact hq'.cross x hx t ht
        have subL : Sub (alo, i, blo, j) (alo, ahi, blo, bhi) :=
          ⟨Nat.le_refl _, by simp only; omega, Nat.le_refl _, by simp only; omega⟩
        have subR : Sub (i + k, ahi, j + k, bhi) (alo, ahi, blo, bhi) :=
          ⟨by simp only; omega, Nat.le_refl _, by simp only; omega, Nat.le_refl _⟩
        have okL : alo < i ∧ blo < j → BoxOk s (alo, i, blo, j) := by
          intro _
          exact ⟨by simp only; omega, by simp only; omega, by simp only; omega, by simp only; omega⟩
        have okR : BoxOk s (i + k, ahi, j + k, bhi) :=
          ⟨by simp only; omega, x2, by simp only; omega, x4⟩
        have relLY : Rel (alo, i, blo, j) (toBox (i, j, k)) :=
          .inl ⟨Nat.le_refl _, Nat.le_refl _⟩
        have relRY : Rel (i + k, ahi, j + k, bhi) (toBox (i, j, k)) :=
          .inr ⟨Nat.le_refl _, Nat.le_refl _⟩
        have relLR : Rel (i + k, ahi, j + k, bhi) (alo, i, blo, j) :=
          .inr ⟨by simp only; omega, by simp only; omega⟩
        -- the two optional pushes
        have stepL : ∀ (c : Bool), (c = true → alo < i ∧ blo < j) →
            LoopInv s (if c then (alo, i, blo, j) :: q' else q') ((i, j, k) :: found) := by
          intro c hc
          cases c with
          | false => exact inv1
          | true =>
            refine inv_push _ (okL (hc rfl)) (fun z hz => rel_sub (hrelq z hz) subL) ?_ inv1
            intro t ht
            rcases List.mem_cons.mp ht with rfl | ht
            · exact relLY
            · exact rel_sub (hrelf t ht) subL
        have stepR : ∀ (c d : Bool), (c = true → alo < i ∧ blo < j) →
            LoopInv s (if d then (i + k, ahi, j + k, bhi) :: (if c then (alo, i, blo, j) :: q' else q') else
              (if c then (alo, i, blo, j) :: q' else q')) ((i, j, k) :: found) := by
          intro c d hc
          cases d with
          | false => exact stepL c hc
          | true =>
            refine inv_push _ okR ?_ ?_ (stepL c hc)
            · intro z hz
              cases c with
              | false => exact rel_sub (hrelq z hz) subR
              | true =>
                rcases List.mem_cons.mp hz with rfl | hz
                · exact relLR
                · exact rel_sub (hrelq z hz) subR
            · intro t ht
              rcases List.mem_cons.mp ht with rfl | ht
              · exact relRY
              · exact rel_sub (hrelf t ht) subR
        have hmL : ∀ c : Bool, (c = true → alo < i ∧ blo < j) →
            blockMeasure (if c then (alo, i, blo, j) :: q' else q') ≤ 2 * (i - alo) + 1 + blockMeasure q' := by
          intro c _
          cases c <;> simp [blockMeasure]
        have hmR : ∀ c d : Bool, (c = true → alo < i ∧ blo < j) → (d = true → i + k < ahi ∧ j + k < bhi) →
            blockMeasure (if d then (i + k, ahi, j + k, bhi) :: (if c then (alo, i, blo, j) :: q' else q') else
              (if c then (alo, i, blo, j) :: q' else q')) < 2 * (ahi - alo) + 1 + blockMeasure q' := by
          intro c d hc hd
          have := hmL c hc
          cases d with
          | false =>
            simp only [Bool.false_eq_true, if_false]
            cases c with
            | false => simp only [Bool.false_eq_true, if_false]; omega
            | true =>
              have := hc rfl
              simp only [if_true, blockMeasure]
              omega
          | true =>
            have hd' := hd rfl
            simp only [if_true, blockMeasure]
            cases c with
            | false => simp only [Bool.false_eq_true, if_false]; omega
            | true =>
              have := hc rfl
              simp only [if_true, blockMeasure]
              omega
        refine ih _ _ ?_ (stepR _ _ (by simp) )
        have := hmR (decide (alo < i) && decide (blo < j)) (decide (i + k < ahi) && decide (j + k < bhi))
          (by simp) (by simp)
        omega

end PyLean.TextLibs.Difflib
