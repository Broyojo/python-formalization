import PyLean.TextLibs.DifflibObjSim

/-!
The laws of `SequenceMatcher` for any hashable element, under `Lawful`: what a `dict` asks of its keys. A
statement that speaks of the classes `cls o (a ++ b)` speaks of `__eq__`: `eqsO_iff` says so. Then what
happens when `__hash__` or `__eq__` raises, where nothing is assumed of the elements involved.
-/

namespace PyLean.TextLibs.Difflib

open PyLean

set_option linter.unusedSimpArgs false

variable {α : Type}

/-- `a[i:i+k] == b[j:j+k]`, both in range, element by element with `__eq__`. -/
def EqsO (o : Ops α) (a b : List α) (i j k : Nat) : Prop :=
  i + k ≤ a.length ∧ j + k ≤ b.length ∧
    ∀ t, t < k → ∃ x y, a[i + t]? = some x ∧ b[j + t]? = some y ∧ o.eq x y = .ok true

/-- Equal classes are `__eq__`, element by element: the statements on classes mean what they say. -/
theorem eqsO_iff {o : Ops α} {a b : List α} (L : Lawful o (a ++ b)) (i j k : Nat) :
    EqsO o a b i j k ↔ Eqs (a.map (cls o (a ++ b))) (b.map (cls o (a ++ b))) i j k := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by simpa using h1, by simpa using h2, fun t ht => ?_⟩
    obtain ⟨x, y, e1, e2, e3⟩ := h3 t ht
    have hx : x ∈ a ++ b := mem_left (List.mem_of_getElem? e1)
    have hy : y ∈ a ++ b := mem_right (List.mem_of_getElem? e2)
    simp only [List.getElem?_map, e1, e2, Option.map_some]
    rw [cls_of_eq L x y hx hy e3]
  · rintro ⟨h1, h2, h3⟩
    simp only [List.length_map] at h1 h2
    refine ⟨h1, h2, fun t ht => ?_⟩
    have ha : i + t < a.length := by omega
    have hb : j + t < b.length := by omega
    refine ⟨a[i + t], b[j + t], by simp [ha], by simp [hb], ?_⟩
    have h4 := h3 t ht
    simp only [List.getElem?_map, List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb, Option.map_some,
      Option.some.injEq] at h4
    exact eq_of_cls L _ _ (mem_left (List.getElem_mem ha)) (mem_right (List.getElem_mem hb)) h4

/-- The docstring of `find_longest_match`, for a box in range, with no `isjunk` and nothing popular, for any
lawful elements: of all matching blocks in the box, the result is one of the longest, the earliest in `a`
among those, and the earliest in `b` among those, and `(alo, blo, 0)` if there is none. -/
def FindLongestDocO : Prop :=
  ∀ (α : Type) (o : Ops α) (a b : List α) (auto : Bool) (s : SMO α) (alo ahi blo bhi : Nat), Lawful o (a ++ b) →
    (auto = false ∨ b.length < 200) → makeO o none a b auto = .ok s →
    alo ≤ ahi → ahi ≤ a.length → blo ≤ bhi → bhi ≤ b.length →
    ∃ i j k, findLongestO o s alo ahi blo bhi = .ok (i, j, k) ∧ alo ≤ i ∧ i + k ≤ ahi ∧ blo ≤ j ∧ j + k ≤ bhi ∧
      EqsO o a b i j k ∧ ∀ i' j' k', alo ≤ i' → i' + k' ≤ ahi → blo ≤ j' → j' + k' ≤ bhi → EqsO o a b i' j' k' →
        k' ≤ k ∧ (k' = k → i < i' ∨ (i = i' ∧ j ≤ j'))

theorem findLongestDocO_proven : FindLongestDocO := by
  intro α o a b auto s alo ahi blo bhi L hp h h1 h2 h3 h4
  obtain ⟨F, t, hF, h5, S, _⟩ := make_sim L none auto s h
  rw [hF rfl] at h5
  obtain ⟨i, j, k, e, r1, r2, r3, r4, r5, r6⟩ := findLongestDoc_proven _ _ auto t alo ahi blo bhi (by simpa using hp) h5 h1
    (by simpa using h2) h3 (by simpa using h4)
  refine ⟨i, j, k, by rw [find_val L S, e], r1, r2, r3, r4, (eqsO_iff L _ _ _).mpr r5, ?_⟩
  intro i' j' k' g1 g2 g3 g4 g5
  exact r6 i' j' k' g1 g2 g3 g4 ((eqsO_iff L _ _ _).mp g5)

/-- `get_matching_blocks` on a new matcher over lawful elements: a chain of real matches, in order in both
sequences, that do not touch, and the sentinel `(len(a), len(b), 0)`, the only block of size 0. -/
def BlocksLawO : Prop :=
  ∀ (α : Type) (o : Ops α) (isjunk : Option (α → Py Bool)) (a b : List α) (auto : Bool) (s : SMO α), Lawful o (a ++ b) →
    makeO o isjunk a b auto = .ok s →
    ∃ s' l, getBlocksO o s = .ok (s', l ++ [(a.length, b.length, 0)]) ∧
      ChainFrom (a.map (cls o (a ++ b))) (b.map (cls o (a ++ b))) 0 0 l ∧ NA l

theorem blocksLawO_proven : BlocksLawO := by
  intro α o isjunk a b auto s L h
  obtain ⟨F, t, _, h5, S, _⟩ := make_sim L isjunk auto s h
  obtain ⟨t', l, e, r1, r2⟩ := blocksLaw_proven _ _ _ _ _ h5
  simp only [List.length_map] at e
  obtain ⟨s', e2, _⟩ := blocks_val L S e
  exact ⟨s', l, e2, r1, r2⟩

/-- `get_opcodes` on a new matcher over lawful elements: the opcodes go from the start to the ends of both
sequences with no gap, an `equal` is a real match under `__eq__`, and each tag means what it says. -/
def OpcodesLawO : Prop :=
  ∀ (α : Type) (o : Ops α) (isjunk : Option (α → Py Bool)) (a b : List α) (auto : Bool) (s : SMO α), Lawful o (a ++ b) →
    makeO o isjunk a b auto = .ok s →
    ∃ s' ops, getOpcodesO o s = (s', .ok ops) ∧ Cover (a.map (cls o (a ++ b))) (b.map (cls o (a ++ b))) 0 0 ops

theorem opcodesLawO_proven : OpcodesLawO := by
  intro α o isjunk a b auto s L h
  obtain ⟨F, t, _, h5, S, h6, _⟩ := make_sim L isjunk auto s h
  obtain ⟨t', ops, e, r⟩ := opcodesLaw_proven _ _ _ _ _ h5
  obtain ⟨s', e2, _⟩ := opcodes_val L S h6 (make_fresh _ _ _ _ _ h5).2 e
  exact ⟨s', ops, e2, r⟩

/-- `get_grouped_opcodes` on a new matcher over lawful elements: every change is in a group, in order, and no
`equal` in a group is longer than `2n`. -/
def GroupedLawO : Prop :=
  ∀ (α : Type) (o : Ops α) (isjunk : Option (α → Py Bool)) (a b : List α) (auto : Bool) (s : SMO α) (n : Nat),
    Lawful o (a ++ b) → makeO o isjunk a b auto = .ok s →
    ∃ s1 ops s2 gs, getOpcodesO o s = (s1, .ok ops) ∧ getGroupedO o s n = (s2, .ok gs) ∧
      nonEq gs.flatten = nonEq ops ∧ ∀ g ∈ gs, Small n g

theorem groupedLawO_proven : GroupedLawO := by
  intro α o isjunk a b auto s n L h
  obtain ⟨F, t, _, h5, S, h6, _⟩ := make_sim L isjunk auto s h
  obtain ⟨t1, ops, t2, gs, e1, e2, r1, r2⟩ := groupedLaw_proven _ _ _ _ _ n h5
  obtain ⟨s1, e3, _⟩ := opcodes_val L S h6 (make_fresh _ _ _ _ _ h5).2 e1
  obtain ⟨s2, e4⟩ := grouped_val e3 e1 e2
  exact ⟨s1, ops, s2, gs, e3, e4, r1, r2⟩

/-- `ratio() <= real_quick_ratio()`, exactly, on a new matcher over lawful elements: the matches number at most
the shorter length. -/
def RatioBoundO : Prop :=
  ∀ (α : Type) (o : Ops α) (isjunk : Option (α → Py Bool)) (a b : List α) (auto : Bool) (s : SMO α), Lawful o (a ++ b) →
    makeO o isjunk a b auto = .ok s →
    ∃ s' m l, ratioPairO o s = .ok (s', m, l) ∧ l = a.length + b.length ∧ m ≤ min a.length b.length

theorem ratioBoundO_proven : RatioBoundO := by
  intro α o isjunk a b auto s L h
  obtain ⟨F, t, _, h5, S, _⟩ := make_sim L isjunk auto s h
  obtain ⟨t', m, l, e, r1, r2⟩ := ratioBound_proven _ _ _ _ _ h5
  obtain ⟨s', e2⟩ := ratio_val L S e
  obtain ⟨_, ha, hb⟩ := make_ready _ _ _ _ _ h5
  simp only [realQuickPair, ha, hb, List.length_map] at r2
  simp only [List.length_map] at r1
  exact ⟨s', m, l, e2, r1, r2⟩

/-- The docstring of `quick_ratio`, "an upper bound on ratio()", exactly, as counts of matches, on a new matcher
over lawful elements. -/
def QuickBoundO : Prop :=
  ∀ (α : Type) (o : Ops α) (isjunk : Option (α → Py Bool)) (a b : List α) (auto : Bool) (s : SMO α), Lawful o (a ++ b) →
    makeO o isjunk a b auto = .ok s →
    ∃ s1 m l s2 q k, ratioPairO o s = .ok (s1, m, l) ∧ quickPairO o s = (s2, .ok (q, k)) ∧ m ≤ q

theorem quickBoundO_proven : QuickBoundO := by
  intro α o isjunk a b auto s L h
  obtain ⟨F, t, _, h5, S, _, h7⟩ := make_sim L isjunk auto s h
  obtain ⟨t', m, l, e, r⟩ := quickBound_proven _ _ _ _ _ h5
  obtain ⟨s', e2⟩ := ratio_val L S e
  have hf : t.fullb = none := (chainB_spec _ _ (make_ok _ _ _ _ _ h5)).2.2.2.2.2.1
  obtain ⟨s2, e3⟩ := quickPair_val L S h7 hf
  exact ⟨s', m, l, s2, _, _, e2, e3, r⟩

/-! ### `set_seqs` -/

theorem chainBO_congr (o : Ops α) (x y : SMO α) (h1 : x.a = y.a) (h2 : x.b = y.b) (h3 : x.isjunk = y.isjunk)
    (h4 : x.autojunk = y.autojunk) (h5 : x.blocks = y.blocks) (h6 : x.opcodes = y.opcodes) (h7 : x.fullb = y.fullb) :
    (chainBO o x).2 = (chainBO o y).2 ∧ ((chainBO o y).2 = .ok () → (chainBO o x).1 = (chainBO o y).1) := by
  cases x
  cases y
  simp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6 h7
  simp only [chainBO]
  split
  · simp
  · split
    · simp
    · simp

/-- `set_seqs` with new objects leaves what `__init__` would on those sequences, caches included, and raises
what `__init__` would raise, for any elements at all: nothing of the old sequences survives. -/
def SetSeqsFreshO : Prop :=
  ∀ (α : Type) (o : Ops α) (isjunk : Option (α → Py Bool)) (a b a' b' : List α) (auto : Bool) (s : SMO α),
    makeO o isjunk a b auto = .ok s →
    match makeO o isjunk a' b' auto with
    | .ok s' => setSeqsO o s a' b' false false = (s', .ok ())
    | .error e => (setSeqsO o s a' b' false false).2 = .error e

theorem setSeqsFreshO_proven : SetSeqsFreshO := by
  intro α o isjunk a b a' b' auto s h
  have hc : chainBO o { a, b, isjunk, autojunk := auto, blocks := none, opcodes := none, fullb := none } = (s, .ok ()) := by
    simp only [makeO, setSeq2O, Bool.false_eq_true, if_false] at h
    split at h
    · rename_i s1 he
      simp only [Except.ok.injEq] at h
      subst h
      exact he
    · simp at h
  obtain ⟨_, _, hj, ha⟩ := chainBO_fields o _ s _ hc
  obtain ⟨c1, c2⟩ := chainBO_congr o
    { s with a := a', blocks := none, opcodes := none, b := b', fullb := none }
    { a := a', b := b', isjunk, autojunk := auto, blocks := none, opcodes := none, fullb := none }
    rfl rfl hj ha rfl rfl rfl
  simp only [setSeqsO, setSeq1O, setSeq2O, Bool.false_eq_true, if_false]
  unfold makeO
  simp only [setSeq2O, Bool.false_eq_true, if_false]
  generalize hr : chainBO o { a := a', b := b', isjunk, autojunk := auto, blocks := none, opcodes := none, fullb := none } = r at c1 c2
  obtain ⟨st, res⟩ := r
  cases res with
  | error e => simpa using c1
  | ok u =>
    cases u
    have h1 := c2 rfl
    simp only at h1 c1
    exact Prod.ext h1 c1

/-! ### When `__hash__` or `__eq__` raises -/

theorem build_append {o : Ops α} {p : List α} (L : Lawful o p) (rest : List α) :
    ∀ (q : List α) (i : Nat) (m : DictO α (List Nat)), (∀ x ∈ q, x ∈ p) → Good o p m →
      buildO o (q ++ rest) i m = buildO o rest (i + q.length) (buildO o q i m).1 := by
  intro q
  induction q with
  | nil => intro i m _ _; rfl
  | cons x r ih =>
    intro i m hb hg
    have hX := hb x (by simp)
    obtain ⟨hx, he⟩ := L.hash_ok x hX
    obtain ⟨m', h1, h2, _⟩ := addIdx_val L x hx i hX he m hg
    have e : i + (x :: r).length = i + 1 + r.length := by simp; omega
    simp only [List.cons_append, buildO, he, h1, e]
    exact ih (i + 1) m' (fun y hy => hb y (by simp [hy])) h2

def valsOf (m : DictO α (List Nat)) : List Nat := (m.map (·.2.2)).flatten

theorem addIdx_vals (e i j : Nat) : ∀ m : List (Nat × List Nat),
    j ∈ ((addIdx m e i).map (·.2)).flatten ↔ j ∈ (m.map (·.2)).flatten ∨ j = i := by
  intro m
  induction m with
  | nil => simp [addIdx]
  | cons p r ih =>
    obtain ⟨k, v⟩ := p
    simp only [addIdx]
    split
    · simp only [List.map_cons, List.flatten_cons, List.mem_append, List.mem_singleton]
      by_cases h1 : j ∈ v <;> by_cases h2 : j = i <;> simp [h1, h2]
    · simp only [List.map_cons, List.flatten_cons, List.mem_append]
      rw [ih]
      simp only [or_assoc]

theorem vals_proj {o : Ops α} {xs : List α} (m : DictO α (List Nat)) :
    ((proj o xs m).map (·.2)).flatten = valsOf m := by
  simp [proj, valsOf, Function.comp_def]

theorem build_idx {o : Ops α} {p : List α} (L : Lawful o p) (j : Nat) :
    ∀ (q : List α) (i : Nat) (m : DictO α (List Nat)), (∀ x ∈ q, x ∈ p) → Good o p m →
      (j ∈ valsOf (buildO o q i m).1 ↔ j ∈ valsOf m ∨ (i ≤ j ∧ j < i + q.length)) := by
  intro q
  induction q with
  | nil =>
    intro i m _ _
    simp only [buildO, List.length_nil, Nat.add_zero]
    constructor
    · exact Or.inl
    · rintro (h | ⟨h1, h2⟩)
      · exact h
      · omega
  | cons x r ih =>
    intro i m hb hg
    have hX := hb x (by simp)
    obtain ⟨hx, he⟩ := L.hash_ok x hX
    obtain ⟨m', h1, h2, h3⟩ := addIdx_val L x hx i hX he m hg
    simp only [buildO, he, h1]
    rw [ih (i + 1) m' (fun y hy => hb y (by simp [hy])) h2]
    have e : j ∈ valsOf m' ↔ j ∈ valsOf m ∨ j = i := by
      rw [← vals_proj (o := o) (xs := p) m', ← vals_proj (o := o) (xs := p) m, h3]
      exact addIdx_vals _ _ _ _
    rw [e]
    simp only [List.length_cons]
    by_cases h4 : j ∈ valsOf m
    · simp [h4]
    · simp only [h4, false_or]
      omega

/-- `__chain_b` when `__hash__` of an element raises, after lawful elements: the exception comes out and
the matcher is left half done, as `:281-283` leaves it. `b` is set, the caches are cleared, `bjunk` and
`bpopular` are the old ones, and `b2j` has exactly the indices of the elements before it. -/
def ChainHashFail : Prop :=
  ∀ (α : Type) (o : Ops α) (s : SMO α) (p rest : List α) (x : α) (e : PyExc), Lawful o p → o.hash x = .error e →
    let r := setSeq2O o s (p ++ x :: rest) false
    r.2 = .error e ∧ r.1.b = p ++ x :: rest ∧ r.1.blocks = none ∧ r.1.opcodes = none ∧ r.1.bjunk = s.bjunk ∧
      r.1.bpopular = s.bpopular ∧ ∀ j, j ∈ valsOf r.1.b2j ↔ j < p.length

theorem chainHashFail_proven : ChainHashFail := by
  intro α o s p rest x e L he
  have hg : Good o p ([] : DictO α (List Nat)) := by intro e he; simp at he
  have h1 := build_append L (x :: rest) p 0 [] (fun _ h => h) hg
  have h2 : buildO o (p ++ x :: rest) 0 [] = ((buildO o p 0 []).1, .error e) := by
    rw [h1]
    simp only [buildO, he]
  simp only [setSeq2O, Bool.false_eq_true, if_false, chainBO, h2, true_and]
  intro j
  rw [build_idx L j p 0 [] (fun _ h => h) hg]
  simp [valsOf]

/-- A condition of the first extension loop runs `==` on the elements before the best match, in that
order, with no identity shortcut, and what it raises comes out of `find_longest_match`. `__eq__` is
reached here for elements the dict never compared, which is how an `__eq__` that raises gets this far. -/
def LongestEqFail : Prop :=
  ∀ (α : Type) (o : Ops α) (s : SMO α) (alo ahi blo bhi i j k h : Nat) (x y : α) (e : PyExc),
    outerO o s blo bhi ahi (ahi - alo) alo [] (alo, blo, 0) = .ok (i, j, k) → alo < i → blo < j →
    s.b[j - 1]? = some y → s.a[i - 1]? = some x → o.hash y = .ok h → scontains o y h s.bjunk = .ok false →
    o.eq x y = .error e → findLongestO o s alo ahi blo bhi = .error e

theorem longestEqFail_proven : LongestEqFail := by
  intro α o s alo ahi blo bhi i j k h x y e h1 h2 h3 h4 h5 h6 h7 h8
  have hT : extTestO o s false (i - 1) (j - 1) = .error e := by
    simp only [extTestO, atO, h4, h5, h6, h7, h8]
    simp
  have hf : ahi + bhi + 1 = (ahi + bhi) + 1 := rfl
  have hc : (decide (i > alo) && decide (j > blo)) = true := by simp [h2, h3]
  simp only [findLongestO, h1, hf, extendLeftO, hc, if_true, hT]

/-- `a[i]` is hashed in the outer loop of `find_longest_match`, in order, so the first element of the box
whose `__hash__` raises decides the exception, whatever follows it. -/
def LongestHashFail : Prop :=
  ∀ (α : Type) (o : Ops α) (s : SMO α) (alo ahi blo bhi i : Nat) (x : α) (e : PyExc), alo ≤ i → i < ahi →
    (∀ m, alo ≤ m → m < i → ∃ y h v, s.a[m]? = some y ∧ o.hash y = .ok h ∧ dget o y h s.b2j = .ok v) →
    s.a[i]? = some x → o.hash x = .error e → findLongestO o s alo ahi blo bhi = .error e

theorem outer_fail (o : Ops α) (s : SMO α) (blo bhi ahi i : Nat) (x : α) (e : PyExc) (ha : s.a[i]? = some x)
    (he : o.hash x = .error e) : ∀ (f c : Nat) (j : List (Nat × Nat)) (best : Best), i + 1 ≤ c + f → c ≤ i →
      (∀ m, c ≤ m → m < i → ∃ y h v, s.a[m]? = some y ∧ o.hash y = .ok h ∧ dget o y h s.b2j = .ok v) →
      outerO o s blo bhi ahi f c j best = .error e := by
  intro f
  induction f with
  | zero => intro c _ _ h1 h2; omega
  | succ f ih =>
    intro c j best h1 h2 h3
    by_cases hc : c = i
    · subst hc
      simp only [outerO, atO, ha, he]
    · obtain ⟨y, h, v, e1, e2, e3⟩ := h3 c (Nat.le_refl _) (by omega)
      simp only [outerO, atO, e1, e2, e3]
      exact ih (c + 1) _ _ (by omega) (by omega) (fun m h4 h5 => h3 m (by omega) h5)

theorem longestHashFail_proven : LongestHashFail := by
  intro α o s alo ahi blo bhi i x e h1 h2 h3 h4 h5
  have h := outer_fail o s blo bhi ahi i x e h4 h5 (ahi - alo) alo [] (alo, blo, 0) (by omega) h1 h3
  simp only [findLongestO, h]

/-! ### `get_opcodes` after a failure -/

/-- What happens to `get_opcodes` is what happens to a call that failed: a second call fails the same way.
It does not. `self.opcodes = answer = []` at `Lib/difflib.py:525` runs ahead of `get_matching_blocks`, so
after a failure the second call returns `[]`, which says the sequences have no differences to report. -/
def OpcodesFailAgain : Prop :=
  ∀ (α : Type) (o : Ops α) (s s1 : SMO α) (e : PyExc), getOpcodesO o s = (s1, .error e) →
    (getOpcodesO o s1).2 = .error e

/-- `a` holds an element whose `__hash__` raises. -/
def badOps : Ops Nat where
  hash n := if n = 0 then .error (.typeError "unhashable type: 'list'") else .ok n
  eq x y := .ok (x == y)
  same x y := x == y

def badS : SMO Nat := { a := [0], b := [1], b2j := [(1, 1, [0])] }

theorem opcodesFailAgain_refuted : ¬OpcodesFailAgain := by
  intro h
  have h1 := h Nat badOps badS { badS with opcodes := some [] } (.typeError "unhashable type: 'list'") rfl
  have h2 : (getOpcodesO badOps { badS with opcodes := some [] }).2 = .ok [] := rfl
  rw [h2] at h1
  cases h1

end PyLean.TextLibs.Difflib
