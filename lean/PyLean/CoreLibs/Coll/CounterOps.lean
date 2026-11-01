import PyLean.Accel.SelectProps
import PyLean.CoreLibs.Coll.CounterProps

/-!
Properties of `Counter`, part 2: `most_common`, `elements`, `__repr__`, and the
multiset operators with their in-place forms.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PyLean.CoreLibs.Coll

open PyLean D

variable {κ : Type} [DecidableEq κ]

/-! ### The result of a multiset operator -/

/-- The shape of every operator's result. -/
def res (g h : κ → Int → Option Int) (a b : Ctr κ) : Ctr κ := nf g a ++ nf h b

/-- Side conditions of an operator: the second loop only stores keys absent from
the left operand, and only positive values are stored. -/
structure OpOk (g h : κ → Int → Option Int) (a b : Ctr κ) : Prop where
  ha : WF a
  hb : WF b
  fresh : ∀ p ∈ b, (h p.1 p.2).isSome → p.1 ∉ keys a
  gpos : ∀ e c n, g e c = some n → n > 0
  hpos : ∀ e c n, h e c = some n → n > 0

theorem res_mem_keys {g h : κ → Int → Option Int} {a b : Ctr κ} {x : κ} (hb : WF b)
    (hx : x ∈ keys (nf h b)) : ∃ c, D.get? b x = some c ∧ (h x c).isSome :=
  (mem_keys_nf hb).mp hx

theorem pos_of_mem_nf {f : κ → Int → Option Int} (hf : ∀ e c n, f e c = some n → n > 0)
    {src : Ctr κ} {p : κ × Int} (hp : p ∈ nf f src) : p.2 > 0 := by
  unfold nf at hp
  simp only [List.mem_filterMap, Option.map_eq_some_iff] at hp
  obtain ⟨q, _, n, hn, e⟩ := hp
  rw [← e]
  exact hf _ _ _ hn

theorem res_WF {g h : κ → Int → Option Int} {a b : Ctr κ} (hok : OpOk g h a b) : WF (res g h a b) := by
  unfold res WF
  rw [keys_append, List.nodup_append]
  refine ⟨WF_nf g hok.ha, WF_nf h hok.hb, ?_⟩
  intro x hx y hy e
  subst e
  obtain ⟨c, hc, hs⟩ := (mem_keys_nf hok.hb).mp hy
  have hbp : (x, c) ∈ b := by
    have hk := D.get?_isSome_iff (d := b) (x := x)
    have hmem : x ∈ keys b := hk.mp (by simp [hc])
    obtain ⟨q, hq, e⟩ := List.mem_map.mp hmem
    have := D.get?_of_mem_pair (d := b) hok.hb (x := q.1) (v := q.2) hq
    rw [e, hc] at this
    have h2 : c = q.2 := by simpa using this
    subst h2
    have : q = (x, q.2) := by rw [← e]
    rwa [← this]
  exact hok.fresh (x, c) hbp hs ((keys_nf_sublist g a).subset hx)

theorem res_pos {g h : κ → Int → Option Int} {a b : Ctr κ} (hok : OpOk g h a b) :
    ∀ p ∈ res g h a b, p.2 > 0 := by
  intro p hp
  simp only [res, List.mem_append] at hp
  rcases hp with hp | hp
  · exact pos_of_mem_nf hok.gpos hp
  · exact pos_of_mem_nf hok.hpos hp

theorem res_keys {g h : κ → Int → Option Int} {a b : Ctr κ} (hok : OpOk g h a b) :
    (keys (res g h a b)).Sublist (keys a ++ (keys b).filter (fun x => decide (x ∉ keys a))) := by
  unfold res
  rw [keys_append]
  apply (keys_nf_sublist g a).append
  have : (keys (nf h b)) = (keys (nf h b)).filter (fun x => decide (x ∉ keys a)) := by
    symm
    apply List.filter_eq_self.mpr
    intro x hx
    obtain ⟨c, hc, hs⟩ := (mem_keys_nf hok.hb).mp hx
    have hmem : x ∈ keys b := D.get?_isSome_iff.mp (by simp [hc])
    obtain ⟨q, hq, e⟩ := List.mem_map.mp hmem
    have h2 := D.get?_of_mem_pair (d := b) hok.hb (x := q.1) (v := q.2) hq
    rw [e, hc] at h2
    have h3 : c = q.2 := by simpa using h2
    have h4 := hok.fresh q hq (by rw [e, ← h3]; exact hs)
    rw [e] at h4
    simpa using h4
  rw [this]
  exact (keys_nf_sublist h b).filter _

theorem res_cGet {g h : κ → Int → Option Int} {a b : Ctr κ} (hok : OpOk g h a b) (x : κ) :
    cGet (res g h a b) x =
      if x ∈ keys a then (g x (cGet a x)).getD 0
      else if x ∈ keys b then (h x (cGet b x)).getD 0 else 0 := by
  unfold res
  by_cases hx : x ∈ keys (nf g a)
  · rw [cGet_append_left hx, cGet_nf hok.ha]
    have : x ∈ keys a := (keys_nf_sublist g a).subset hx
    simp [this]
  · rw [cGet_append_right hx, cGet_nf hok.hb]
    by_cases ha : x ∈ keys a
    · simp only [ha, if_true]
      have h0 : (g x (cGet a x)).getD 0 = 0 := by
        cases hg : g x (cGet a x) with
        | none => rfl
        | some n =>
          exfalso
          apply hx
          refine (mem_keys_nf hok.ha).mpr ?_
          have : D.get? a x = some (cGet a x) := by
            obtain ⟨q, hq, e⟩ := List.mem_map.mp ha
            have := D.get?_of_mem_pair (d := a) hok.ha (x := q.1) (v := q.2) hq
            rw [e] at this
            simp [cGet, this]
          exact ⟨_, this, by simp [hg]⟩
      rw [h0]
      split
      · next hb =>
        cases hh : h x (cGet b x) with
        | none => rfl
        | some n =>
          exfalso
          obtain ⟨q, hq, e⟩ := List.mem_map.mp hb
          have h2 := cGet_of_mem hok.hb hq
          rw [e] at h2
          have h3 := hok.fresh q hq (by rw [e, ← h2]; simp [hh])
          rw [e] at h3
          exact h3 ha
      · rfl
    · simp [ha]

theorem res_nil_right (g h : κ → Int → Option Int) (a : Ctr κ) :
    res g h a [] = nf g a := by simp [res, nf]

/-! Each operator as a `res`. -/

section ops
variable (a b : Ctr κ)

def gAdd : κ → Int → Option Int := fun e count =>
  let newcount := count + cGet b e
  if newcount > 0 then some newcount else none
def hAdd : κ → Int → Option Int := fun e count =>
  if !D.mem a e && decide (count > 0) then some count else none
def gSub : κ → Int → Option Int := fun e count =>
  let newcount := count - cGet b e
  if newcount > 0 then some newcount else none
def hSub : κ → Int → Option Int := fun e count =>
  if !D.mem a e && decide (count < 0) then some (0 - count) else none
def gOr : κ → Int → Option Int := fun e count =>
  let other_count := cGet b e
  let newcount := if count < other_count then other_count else count
  if newcount > 0 then some newcount else none
def gAnd : κ → Int → Option Int := fun e count =>
  let other_count := cGet b e
  let newcount := if count < other_count then count else other_count
  if newcount > 0 then some newcount else none
def noH : κ → Int → Option Int := fun _ _ => none
def gPos : κ → Int → Option Int := fun _ count => if count > 0 then some count else none
def gNeg : κ → Int → Option Int := fun _ count => if count < 0 then some (0 - count) else none

end ops

private theorem isSome_ite_pos {c : Prop} [Decidable c] {v : Int} (h : (if c then some v else none).isSome = true) : c := by
  by_cases hc : c
  · exact hc
  · simp [hc] at h

theorem okAdd {a b : Ctr κ} (ha : WF a) (hb : WF b) : OpOk (gAdd b) (hAdd a) a b := by
  refine ⟨ha, hb, ?_, ?_, ?_⟩
  · intro p _ hs
    have := isSome_ite_pos hs
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
    exact D.mem_false_iff.mp this.1
  · intro e c n h
    simp only [gAdd] at h
    split at h
    · simp only [Option.some.injEq] at h; omega
    · simp at h
  · intro e c n h
    simp only [hAdd] at h
    split at h
    · next hc =>
      simp only [Option.some.injEq] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      omega
    · simp at h

theorem okSub {a b : Ctr κ} (ha : WF a) (hb : WF b) : OpOk (gSub b) (hSub a) a b := by
  refine ⟨ha, hb, ?_, ?_, ?_⟩
  · intro p _ hs
    have := isSome_ite_pos hs
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
    exact D.mem_false_iff.mp this.1
  · intro e c n h
    simp only [gSub] at h
    split at h
    · simp only [Option.some.injEq] at h; omega
    · simp at h
  · intro e c n h
    simp only [hSub] at h
    split at h
    · next hc =>
      simp only [Option.some.injEq] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      omega
    · simp at h

theorem okOr {a b : Ctr κ} (ha : WF a) (hb : WF b) : OpOk (gOr b) (hAdd a) a b := by
  refine ⟨ha, hb, (okAdd ha hb).fresh, ?_, (okAdd ha hb).hpos⟩
  intro e c n h
  simp only [gOr] at h
  split at h <;> simp at h <;> omega

theorem okAnd {a b : Ctr κ} (ha : WF a) (hb : WF b) : OpOk (gAnd b) noH a [] := by
  refine ⟨ha, WF_nil, by simp, ?_, by simp [noH]⟩
  intro e c n h
  simp only [gAnd] at h
  split at h <;> simp at h <;> omega

theorem okPos {a : Ctr κ} (ha : WF a) : OpOk gPos noH a [] := by
  refine ⟨ha, WF_nil, by simp, ?_, by simp [noH]⟩
  intro e c n h
  simp only [gPos] at h
  split at h
  · simp only [Option.some.injEq] at h; omega
  · simp at h

theorem okNeg {a : Ctr κ} (ha : WF a) : OpOk gNeg noH a [] := by
  refine ⟨ha, WF_nil, by simp, ?_, by simp [noH]⟩
  intro e c n h
  simp only [gNeg] at h
  split at h
  · simp only [Option.some.injEq] at h; omega
  · simp at h

theorem addC_res {a b : Ctr κ} (ha : WF a) (hb : WF b) : addC a b = res (gAdd b) (hAdd a) a b :=
  two_loops a b (gAdd b) ha hb (hAdd a) (okAdd ha hb).fresh

theorem subC_res {a b : Ctr κ} (ha : WF a) (hb : WF b) : subC a b = res (gSub b) (hSub a) a b :=
  two_loops a b (gSub b) ha hb (hSub a) (okSub ha hb).fresh

theorem orC_res {a b : Ctr κ} (ha : WF a) (hb : WF b) : orC a b = res (gOr b) (hAdd a) a b :=
  two_loops a b (gOr b) ha hb (hAdd a) (okOr ha hb).fresh

theorem andC_res {a b : Ctr κ} (ha : WF a) : andC a b = res (gAnd b) noH a [] := by
  rw [res_nil_right]; exact loopInto_one a (gAnd b) ha

theorem posC_res {a : Ctr κ} (ha : WF a) : posC a = res gPos noH a [] := by
  rw [res_nil_right]; exact loopInto_one a gPos ha

theorem negC_res {a : Ctr κ} (ha : WF a) : negC a = res gNeg noH a [] := by
  rw [res_nil_right]; exact loopInto_one a gNeg ha

theorem cGet_addC {a b : Ctr κ} (ha : WF a) (hb : WF b) (x : κ) :
    cGet (addC a b) x = max (cGet a x + cGet b x) 0 := by
  rw [addC_res ha hb, res_cGet (okAdd ha hb)]
  by_cases hxa : x ∈ keys a
  · simp only [hxa, if_true, gAdd]
    split
    · simp; omega
    · simp; omega
  · have h0 := cGet_eq_zero hxa
    simp only [hxa, if_false, hAdd, h0]
    have hm : D.mem a x = false := D.mem_false_iff.mpr hxa
    by_cases hxb : x ∈ keys b
    · simp only [hxb, if_true, hm]
      by_cases hp : cGet b x > 0 <;> simp [hp] <;> omega
    · have h1 := cGet_eq_zero hxb
      simp [hxb, h1]

theorem cGet_subC {a b : Ctr κ} (ha : WF a) (hb : WF b) (x : κ) :
    cGet (subC a b) x = max (cGet a x - cGet b x) 0 := by
  rw [subC_res ha hb, res_cGet (okSub ha hb)]
  by_cases hxa : x ∈ keys a
  · simp only [hxa, if_true, gSub]
    split
    · simp; omega
    · simp; omega
  · have h0 := cGet_eq_zero hxa
    simp only [hxa, if_false, hSub, h0]
    have hm : D.mem a x = false := D.mem_false_iff.mpr hxa
    by_cases hxb : x ∈ keys b
    · simp only [hxb, if_true, hm]
      by_cases hp : cGet b x < 0 <;> simp [hp] <;> omega
    · have h1 := cGet_eq_zero hxb
      simp [hxb, h1]

theorem cGet_orC {a b : Ctr κ} (ha : WF a) (hb : WF b) (x : κ) :
    cGet (orC a b) x = max (max (cGet a x) (cGet b x)) 0 := by
  rw [orC_res ha hb, res_cGet (okOr ha hb)]
  by_cases hxa : x ∈ keys a
  · simp only [hxa, if_true, gOr]
    split <;> split <;> simp <;> omega
  · have h0 := cGet_eq_zero hxa
    simp only [hxa, if_false, hAdd, h0]
    have hm : D.mem a x = false := D.mem_false_iff.mpr hxa
    by_cases hxb : x ∈ keys b
    · simp only [hxb, if_true, hm]
      by_cases hp : cGet b x > 0 <;> simp [hp] <;> omega
    · have h1 := cGet_eq_zero hxb
      simp [hxb, h1]

theorem cGet_andC {a b : Ctr κ} (ha : WF a) (hb : WF b) (x : κ) :
    cGet (andC a b) x = max (min (cGet a x) (cGet b x)) 0 := by
  rw [andC_res ha, res_cGet (okAnd ha hb)]
  by_cases hxa : x ∈ keys a
  · simp only [hxa, if_true, gAnd]
    split <;> split <;> simp <;> omega
  · have h0 := cGet_eq_zero hxa
    simp [hxa, h0]
    omega

theorem cGet_posC {a : Ctr κ} (ha : WF a) (x : κ) : cGet (posC a) x = max (cGet a x) 0 := by
  rw [posC_res ha, res_cGet (okPos ha)]
  by_cases hxa : x ∈ keys a
  · simp only [hxa, if_true, gPos]
    split <;> simp <;> omega
  · have h0 := cGet_eq_zero hxa
    simp [hxa, h0]

theorem cGet_negC {a : Ctr κ} (ha : WF a) (x : κ) : cGet (negC a) x = max (0 - cGet a x) 0 := by
  rw [negC_res ha, res_cGet (okNeg ha)]
  by_cases hxa : x ∈ keys a
  · simp only [hxa, if_true, gNeg]
    split <;> simp <;> omega
  · have h0 := cGet_eq_zero hxa
    simp [hxa, h0]

/-- The operators are the multiset operations of their docstrings (:837-924),
computed pointwise on counts with missing as zero and the result clipped at
zero: `+` adds, `-` subtracts, `|` takes the maximum, `&` the minimum, unary `+`
and `-` keep the positive part of the count and of its negation. This holds for all
counters, zero and negative counts included. -/
def OperatorsPointwise : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (a b : Ctr κ) (x : κ), WF a → WF b →
    cGet (addC a b) x = max (cGet a x + cGet b x) 0 ∧
    cGet (subC a b) x = max (cGet a x - cGet b x) 0 ∧
    cGet (orC a b) x = max (max (cGet a x) (cGet b x)) 0 ∧
    cGet (andC a b) x = max (min (cGet a x) (cGet b x)) 0 ∧
    cGet (posC a) x = max (cGet a x) 0 ∧
    cGet (negC a) x = max (0 - cGet a x) 0

theorem operatorsPointwise_proven : OperatorsPointwise :=
  fun _ _ a b x ha hb => ⟨cGet_addC ha hb x, cGet_subC ha hb x, cGet_orC ha hb x, cGet_andC ha hb x,
    cGet_posC ha x, cGet_negC ha x⟩

/-- `r` is a multiset-operator result of `a` and `b`: valid dict, only positive
counts, and its keys follow the left operand's order and then the right one's. -/
def OutputContract (r a b : Ctr κ) : Prop :=
  WF r ∧ (∀ p ∈ r, p.2 > 0) ∧
    (keys r).Sublist (keys a ++ (keys b).filter (fun x => decide (x ∉ keys a)))

theorem contract_of {g h : κ → Int → Option Int} {a b : Ctr κ} (hok : OpOk g h a b) :
    OutputContract (res g h a b) a b := ⟨res_WF hok, res_pos hok, res_keys hok⟩

/-- Comments at :770 and :775-777: "Outputs guaranteed to only include positive
counts", and "Results are ordered according to when an element is first encountered
in the left operand and then by the order encountered in the right operand." -/
def OperatorsOutputContract : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (a b : Ctr κ), WF a → WF b →
    OutputContract (addC a b) a b ∧ OutputContract (subC a b) a b ∧
    OutputContract (orC a b) a b ∧ OutputContract (andC a b) a [] ∧
    OutputContract (posC a) a [] ∧ OutputContract (negC a) a []

theorem operatorsOutputContract_proven : OperatorsOutputContract := by
  intro κ _ a b ha hb
  rw [addC_res ha hb, subC_res ha hb, orC_res ha hb, andC_res ha, posC_res ha, negC_res ha]
  exact ⟨contract_of (okAdd ha hb), contract_of (okSub ha hb), contract_of (okOr ha hb),
    contract_of (okAnd ha hb), contract_of (okPos ha), contract_of (okNeg ha)⟩

/-- `__pos__` "Adds an empty counter" (:912), `__neg__` "Subtracts from an empty
counter" (:920), and `Counter()`-operand forms agree with the unary operators
item for item, in order. -/
def UnaryAreBinary : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (a : Ctr κ), WF a → posC a = addC a [] ∧ negC a = subC [] a

theorem unaryAreBinary_proven : UnaryAreBinary := by
  intro κ _ a ha
  constructor
  · rw [posC_res ha, addC_res ha WF_nil]
    simp only [res, nf, List.filterMap_nil, List.append_nil]
    congr 1
    funext p
    simp [gPos, gAdd]
  · rw [negC_res ha, subC_res WF_nil ha]
    simp only [res, nf, List.filterMap_nil, List.nil_append, List.append_nil]
    congr 1
    funext p
    simp [gNeg, hSub, D.mem, Bool.not_false, Bool.true_and]

/-! ### In-place forms -/

theorem filter_map_filter_pos (b : Ctr κ) (P : κ × Int → Bool) (F : κ × Int → κ × Int)
    (G : κ × Int → Option (κ × Int))
    (h : ∀ p ∈ b, G p = if P p ∧ (F p).2 > 0 then some (F p) else none) :
    ((b.filter P).map F).filter (fun p => decide (p.2 > 0)) = b.filterMap G := by
  induction b with
  | nil => rfl
  | cons p t ih =>
    have ih := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [List.filterMap_cons, h p (by simp)]
    by_cases hP : P p = true
    · by_cases hp : (F p).2 > 0
      · simp [List.filter_cons, hP, hp, ih]
      · simp [List.filter_cons, hP, hp, ih]
    · simp [List.filter_cons, hP, ih]

/-- The common last step: `keepPositive (inf ...) = nf g a ++ nf h b`. -/
theorem keep_inf (cond : Int → Int → Bool) (f : Int → Int → Int) {a b : Ctr κ} (ha : WF a) (hb : WF b)
    (g h : κ → Int → Option Int)
    (h1 : ∀ p ∈ a, (g p.1 p.2).map (Prod.mk p.1) =
      let F : κ × Int := if p.1 ∈ keys b then (p.1, upd cond f p.2 (cGet b p.1)) else p
      if F.2 > 0 then some F else none)
    (h2 : ∀ p ∈ b, (h p.1 p.2).map (Prod.mk p.1) =
      if (decide (p.1 ∉ keys a) && cond 0 p.2) = true ∧ f 0 p.2 > 0 then some (p.1, f 0 p.2) else none) :
    keepPositive (inf cond f a b) = res g h a b := by
  rw [keepPositive_eq (WF_inf cond f ha hb)]
  unfold inf res
  rw [List.filter_append]
  congr 1
  · exact filter_map_pos a _ _ h1
  · exact filter_map_filter_pos b _ (fun p => (p.1, f 0 p.2)) _ h2

theorem iaddC_eq {a b : Ctr κ} (ha : WF a) (hb : WF b) : iaddC a b = addC a b := by
  have hs : (fun s (p : κ × Int) => D.set s p.1 (cGet s p.1 + p.2)) = stepI (fun _ _ => true) (· + ·) := by
    funext s p; simp [stepI]
  unfold iaddC
  rw [hs, foldl_stepI _ _ a b ha hb, addC_res ha hb]
  apply keep_inf _ _ ha hb
  · intro p hp
    by_cases hx : p.1 ∈ keys b
    · simp only [gAdd, hx, if_true, upd]
      by_cases hn : p.2 + cGet b p.1 > 0 <;> simp [hn]
    · have h0 := cGet_eq_zero hx
      simp only [gAdd, hx, if_false, h0]
      by_cases hn : p.2 > 0 <;> simp [hn]
  · intro p hp
    simp only [hAdd, Bool.and_true, D.mem]
    by_cases hx : p.1 ∈ keys a
    · have : (D.get? a p.1).isSome = true := D.get?_isSome_iff.mpr hx
      simp [hx, this]
    · have : (D.get? a p.1).isSome = false := by
        have := D.mem_false_iff.mpr hx; simpa [D.mem] using this
      by_cases hn : p.2 > 0 <;> simp [hx, this, hn]

theorem isubC_eq {a b : Ctr κ} (ha : WF a) (hb : WF b) : isubC a b = subC a b := by
  have hs : (fun s (p : κ × Int) => D.set s p.1 (cGet s p.1 - p.2)) = stepI (fun _ _ => true) (· - ·) := by
    funext s p; simp [stepI]
  unfold isubC
  rw [hs, foldl_stepI _ _ a b ha hb, subC_res ha hb]
  apply keep_inf _ _ ha hb
  · intro p hp
    by_cases hx : p.1 ∈ keys b
    · simp only [gSub, hx, if_true, upd]
      by_cases hn : p.2 - cGet b p.1 > 0 <;> simp [hn]
    · have h0 := cGet_eq_zero hx
      simp only [gSub, hx, if_false, h0]
      by_cases hn : p.2 > 0 <;> simp [hn]
  · intro p hp
    simp only [hSub, Bool.and_true, D.mem]
    by_cases hx : p.1 ∈ keys a
    · have : (D.get? a p.1).isSome = true := D.get?_isSome_iff.mpr hx
      simp [hx, this]
    · have : (D.get? a p.1).isSome = false := by
        have := D.mem_false_iff.mpr hx; simpa [D.mem] using this
      by_cases hn : p.2 < 0
      · have : (0 - p.2 > 0) := by omega
        simp [hx, *]
      · have h3 : ¬ (0 - p.2 > 0) := by omega
        simp [hx, *]

theorem iorC_eq {a b : Ctr κ} (ha : WF a) (hb : WF b) : iorC a b = orC a b := by
  have hs : (fun s (p : κ × Int) =>
      let count := cGet s p.1
      if p.2 > count then D.set s p.1 p.2 else s) =
      stepI (fun c o => decide (o > c)) (fun _ o => o) := by
    funext s p; simp [stepI]
  unfold iorC
  rw [hs, foldl_stepI _ _ a b ha hb, orC_res ha hb]
  apply keep_inf _ _ ha hb
  · intro p hp
    by_cases hx : p.1 ∈ keys b
    · simp only [gOr, hx, if_true, upd, decide_eq_true_eq]
      by_cases hl : p.2 < cGet b p.1
      · have h2 : cGet b p.1 > p.2 := hl
        by_cases hn : cGet b p.1 > 0 <;> simp [hl, h2, hn]
      · have h2 : ¬ cGet b p.1 > p.2 := hl
        by_cases hn : p.2 > 0 <;> simp [hl, h2, hn]
    · have h0 := cGet_eq_zero hx
      simp only [gOr, hx, if_false, h0]
      by_cases hl : p.2 > 0
      · have h2 : ¬ p.2 < 0 := by omega
        simp [hl, h2]
      · by_cases hz : p.2 < 0
        · simp [hl, hz]
        · have : ¬ (0 : Int) > 0 := by omega
          simp [hl, hz]
  · intro p hp
    simp only [hAdd, D.mem]
    by_cases hx : p.1 ∈ keys a
    · have : (D.get? a p.1).isSome = true := D.get?_isSome_iff.mpr hx
      simp [hx, this]
    · have : (D.get? a p.1).isSome = false := by
        have := D.mem_false_iff.mpr hx; simpa [D.mem] using this
      by_cases hn : p.2 > 0 <;> simp [hx, this, hn]

theorem foldlM_pure_and (b : Ctr κ) (l : Ctr κ) (s : Ctr κ) :
    l.foldlM (m := Except PyExc) (fun s p =>
      pure (if cGet b p.1 < cGet s p.1 then D.set s p.1 (cGet b p.1) else s)) s =
    .ok (l.foldl (fun s p => if cGet b p.1 < cGet s p.1 then D.set s p.1 (cGet b p.1) else s) s) := by
  induction l generalizing s with
  | nil => rfl
  | cons p t ih =>
    simp only [List.foldlM_cons, List.foldl_cons]
    exact ih _

theorem iandC_eq {a b : Ctr κ} (ha : WF a) : iandC a b = andC a b := by
  have hb' : WF (a.map (fun p => (p.1, cGet b p.1))) := by
    unfold WF keys at *
    rw [List.map_map]
    exact ha
  have hk : keys (a.map (fun p => (p.1, cGet b p.1))) = keys a := by
    unfold keys; rw [List.map_map]; rfl
  have hstep : a.foldl (fun s p => if cGet b p.1 < cGet s p.1 then D.set s p.1 (cGet b p.1) else s) a =
      (a.map (fun p => (p.1, cGet b p.1))).foldl (stepI (fun c o => decide (o < c)) (fun _ o => o)) a := by
    rw [List.foldl_map]
    congr 1
    funext s p
    simp [stepI]
  have hval : ∀ p ∈ a, cGet (a.map (fun p => (p.1, cGet b p.1))) p.1 = cGet b p.1 := by
    intro p hp
    have := cGet_of_mem (c := a.map (fun p => (p.1, cGet b p.1))) hb' (p := (p.1, cGet b p.1))
      (List.mem_map.mpr ⟨p, hp, rfl⟩)
    exact this
  unfold iandC iandWith
  simp only [bind, Except.bind]
  rw [foldlM_pure_and]
  simp only [pure, Except.pure]
  rw [hstep, foldl_stepI _ _ a _ ha hb', andC_res ha, res_nil_right,
    keepPositive_eq (WF_inf _ _ ha hb')]
  unfold inf
  have hempty : (a.map (fun p => (p.1, cGet b p.1))).filter
      (fun p => decide (p.1 ∉ keys a) && decide (p.2 < 0)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro q hq
    have hmem : q.1 ∈ keys a := by rw [← hk]; exact D.mem_keys_of_mem hq
    simp [hmem]
  rw [hempty]
  simp only [List.map_nil, List.append_nil]
  apply filter_map_pos
  intro p hp
  have hmem : p.1 ∈ keys (a.map (fun p => (p.1, cGet b p.1))) := by
    rw [hk]; exact D.mem_keys_of_mem hp
  simp only [hmem, if_true, hval p hp, upd, gAnd, decide_eq_true_eq]
  by_cases hl : cGet b p.1 < p.2
  · have h2 : ¬ p.2 < cGet b p.1 := by omega
    by_cases hn : cGet b p.1 > 0 <;> simp [hl, h2, hn]
  · by_cases he : p.2 < cGet b p.1
    · by_cases hn : p.2 > 0 <;> simp [hl, he, hn]
    · have h3 : p.2 = cGet b p.1 := by omega
      by_cases hn : p.2 > 0
      · simp [hl, he, hn, ← h3]
      · simp [hl, he, hn, ← h3]

/-- In-place operators agree with the binary ones, items and order: `c += d`,
`c -= d`, `c |= d`, `c &= d` leave `c` equal to `c + d`, `c - d`, `c | d`, `c & d`
for all counters. The two families share no code: the binary ones build a new
`Counter`, the in-place ones write through `self` and call `_keep_positive`. -/
def InplaceAgreesBinary : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (a b : Ctr κ), WF a → WF b →
    iaddC a b = addC a b ∧ isubC a b = subC a b ∧ iorC a b = orC a b ∧ iandC a b = andC a b

theorem inplaceAgreesBinary_proven : InplaceAgreesBinary :=
  fun _ _ _ _ ha hb => ⟨iaddC_eq ha hb, isubC_eq ha hb, iorC_eq ha hb, iandC_eq ha⟩

/-- `_keep_positive` (:930-935) removes exactly the non-positive counts and keeps the rest
in place, which is unary `+` computed in place. -/
def KeepPositiveFilters : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (c : Ctr κ), WF c →
    keepPositive c = c.filter (fun p => decide (p.2 > 0)) ∧ keepPositive c = posC c

theorem keepPositiveFilters_proven : KeepPositiveFilters := by
  intro κ _ c h
  refine ⟨keepPositive_eq h, ?_⟩
  rw [keepPositive_eq h, posC_res h, res_nil_right]
  unfold nf
  have := filter_map_pos c id (fun p => (gPos p.1 p.2).map (Prod.mk p.1)) (by
    intro p _
    by_cases hp : p.2 > 0 <;> simp [gPos, hp])
  simpa using this

/-! ### The correspondence with sets, comment at :779-798 -/

theorem mem_keys_iff_pos {r : Ctr κ} (hw : WF r) (hp : ∀ p ∈ r, p.2 > 0) (x : κ) :
    x ∈ keys r ↔ cGet r x > 0 := by
  constructor
  · intro hx
    obtain ⟨q, hq, e⟩ := List.mem_map.mp hx
    have := cGet_of_mem hw hq
    rw [e] at this
    rw [this]
    exact hp q hq
  · intro h
    exact Classical.byContradiction fun hx => by
      rw [cGet_eq_zero hx] at h
      omega

/-- All multiplicities are zero or one. -/
def ZeroOne (c : Ctr κ) : Prop := ∀ p ∈ c, p.2 = 0 ∨ p.2 = 1

theorem zeroOne_get {c : Ctr κ} (hw : WF c) (h : ZeroOne c) (x : κ) : cGet c x = 0 ∨ cGet c x = 1 := by
  by_cases hx : x ∈ keys c
  · obtain ⟨q, hq, e⟩ := List.mem_map.mp hx
    have := cGet_of_mem hw hq
    rw [e] at this
    rw [this]
    exact h q hq
  · exact Or.inl (cGet_eq_zero hx)

/-- The comment at :779-798: "When the multiplicities are all zero or one,
multiset operations are guaranteed to be equivalent to the corresponding operations
for regular sets", with the set of a counter being the elements of count one.
`set(r)` for a result `r` is its keys. -/
def SetCorrespondence : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (a b : Ctr κ), WF a → WF b → ZeroOne a → ZeroOne b →
    let sp := fun x => cGet a x = 1
    let sq := fun x => cGet b x = 1
    (∀ x, x ∈ keys (addC a b) ↔ (sp x ∨ sq x)) ∧
    (∀ x, x ∈ keys (subC a b) ↔ (sp x ∧ ¬ sq x)) ∧
    (∀ x, x ∈ keys (orC a b) ↔ (sp x ∨ sq x)) ∧
    (∀ x, x ∈ keys (andC a b) ↔ (sp x ∧ sq x)) ∧
    (eqC a b = true ↔ ∀ x, sp x ↔ sq x) ∧
    (neC a b = true ↔ ∃ x, ¬ (sp x ↔ sq x)) ∧
    (leC a b = true ↔ ∀ x, sp x → sq x) ∧
    (ltC a b = true ↔ (∀ x, sp x → sq x) ∧ ∃ x, sq x ∧ ¬ sp x) ∧
    (geC a b = true ↔ ∀ x, sq x → sp x) ∧
    (gtC a b = true ↔ (∀ x, sq x → sp x) ∧ ∃ x, sp x ∧ ¬ sq x)

theorem setCorrespondence_proven : SetCorrespondence := by
  intro κ _ a b ha hb za zb sp sq
  have ga := zeroOne_get ha za
  have gb := zeroOne_get hb zb
  have hsp : ∀ x, sp x ↔ cGet a x = 1 := fun _ => Iff.rfl
  have hsq : ∀ x, sq x ↔ cGet b x = 1 := fun _ => Iff.rfl
  have kAdd : ∀ x, x ∈ keys (addC a b) ↔ (sp x ∨ sq x) := by
    intro x
    have c := contract_of (okAdd ha hb)
    rw [← addC_res ha hb] at c
    rw [mem_keys_iff_pos c.1 c.2.1, cGet_addC ha hb, hsp, hsq]
    have := ga x; have := gb x; omega
  have kSub : ∀ x, x ∈ keys (subC a b) ↔ (sp x ∧ ¬ sq x) := by
    intro x
    have c := contract_of (okSub ha hb)
    rw [← subC_res ha hb] at c
    rw [mem_keys_iff_pos c.1 c.2.1, cGet_subC ha hb, hsp, hsq]
    have := ga x; have := gb x; omega
  have kOr : ∀ x, x ∈ keys (orC a b) ↔ (sp x ∨ sq x) := by
    intro x
    have c := contract_of (okOr ha hb)
    rw [← orC_res ha hb] at c
    rw [mem_keys_iff_pos c.1 c.2.1, cGet_orC ha hb, hsp, hsq]
    have := ga x; have := gb x; omega
  have kAnd : ∀ x, x ∈ keys (andC a b) ↔ (sp x ∧ sq x) := by
    intro x
    have c := contract_of (okAnd (b := b) ha hb)
    rw [← andC_res ha] at c
    rw [mem_keys_iff_pos c.1 c.2.1, cGet_andC ha hb, hsp, hsq]
    have := ga x; have := gb x; omega
  obtain ⟨hE, hN, hL, hG, hLt, hGt⟩ := comparisonsPointwise_proven κ a b
  refine ⟨kAdd, kSub, kOr, kAnd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hE]
    constructor
    · intro h x; rw [hsp, hsq, h x]
    · intro h x
      have := h x
      rw [hsp, hsq] at this
      have := ga x; have := gb x; omega
  · rw [hN]
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      rw [hsp, hsq]
      have := ga x; have := gb x; omega
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      rw [hsp, hsq] at hx
      intro e
      exact hx (by rw [e])
  · rw [hL]
    constructor
    · intro h x hx
      rw [hsp] at hx
      rw [hsq]
      have := h x; have := gb x; omega
    · intro h x
      have h1 := h x
      rw [hsp, hsq] at h1
      have := ga x; have := gb x; omega
  · rw [hLt]
    constructor
    · rintro ⟨h, x, hx⟩
      refine ⟨fun y hy => ?_, x, ?_⟩
      · rw [hsp] at hy
        rw [hsq]
        have := h y; have := gb y; omega
      · rw [hsp, hsq]
        have := ga x; have := gb x; omega
    · rintro ⟨h, x, h1, h2⟩
      refine ⟨fun y => ?_, x, ?_⟩
      · have h1 := h y
        rw [hsp, hsq] at h1
        have := ga y; have := gb y; omega
      · rw [hsq] at h1
        rw [hsp] at h2
        have := ga x; omega
  · rw [hG]
    constructor
    · intro h x hx
      rw [hsq] at hx
      rw [hsp]
      have := h x; have := ga x; omega
    · intro h x
      have h1 := h x
      rw [hsp, hsq] at h1
      have := ga x; have := gb x; omega
  · rw [hGt]
    constructor
    · rintro ⟨h, x, hx⟩
      refine ⟨fun y hy => ?_, x, ?_⟩
      · rw [hsq] at hy
        rw [hsp]
        have := h y; have := ga y; omega
      · rw [hsp, hsq]
        have := ga x; have := gb x; omega
    · rintro ⟨h, x, h1, h2⟩
      refine ⟨fun y => ?_, x, ?_⟩
      · have h1 := h y
        rw [hsp, hsq] at h1
        have := ga y; have := gb y; omega
      · rw [hsp] at h1
        rw [hsq] at h2
        have := gb x; omega

end PyLean.CoreLibs.Coll
