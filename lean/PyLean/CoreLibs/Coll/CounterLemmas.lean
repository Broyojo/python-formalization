import PyLean.CoreLibs.Coll.Counter

/-! Normal forms for the `Counter` loops: every operator is a `filterMap` of its
operands, which turns questions about folds of `dict` writes into list facts. -/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PyLean.CoreLibs.Coll

open PyLean

variable {κ : Type} [DecidableEq κ]

open D (keys WF)

/-! ### `cGet` -/

theorem cGet_eq_zero {c : Ctr κ} {x : κ} (h : x ∉ keys c) : cGet c x = 0 := by
  simp [cGet, D.get?_eq_none_iff.mpr h]

theorem cGet_set (c : Ctr κ) (e x : κ) (v : Int) :
    cGet (D.set c e v) x = if e = x then v else cGet c x := by
  simp only [cGet, D.get?_set]; split <;> simp

theorem cGet_of_mem {c : Ctr κ} (hw : WF c) {p : κ × Int} (h : p ∈ c) : cGet c p.1 = p.2 := by
  obtain ⟨a, b⟩ := p
  simp [cGet, D.get?_of_mem_pair hw h]

theorem cGet_append_left {a b : Ctr κ} {x : κ} (h : x ∈ keys a) : cGet (a ++ b) x = cGet a x := by
  induction a with
  | nil => simp at h
  | cons p t ih =>
    obtain ⟨u, v⟩ := p
    by_cases hu : u = x
    · subst hu; simp [cGet, D.get?_cons]
    · have : x ∈ keys t := by
        simp only [D.keys_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm hu
        · exact h
      have := ih this
      simpa [cGet, D.get?_cons, hu] using this

theorem cGet_append_right {a b : Ctr κ} {x : κ} (h : x ∉ keys a) : cGet (a ++ b) x = cGet b x := by
  induction a with
  | nil => simp
  | cons p t ih =>
    obtain ⟨u, v⟩ := p
    simp only [D.keys_cons, List.mem_cons, not_or] at h
    have hu : u ≠ x := fun e => h.1 e.symm
    have := ih h.2
    simpa [cGet, D.get?_cons, hu] using this

/-! ### The `loopInto` normal form -/

/-- What one `loopInto` produces from `src`. -/
def nf (f : κ → Int → Option Int) (src : Ctr κ) : Ctr κ :=
  src.filterMap (fun p => (f p.1 p.2).map (Prod.mk p.1))

theorem keys_nf_sublist (f : κ → Int → Option Int) (src : Ctr κ) : (keys (nf f src)).Sublist (keys src) := by
  induction src with
  | nil => simp [nf]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    unfold nf at *
    simp only [List.filterMap_cons]
    cases h : f a b with
    | none =>
      simp only [Option.map_none]
      exact ih.trans (List.sublist_cons_self _ _)
    | some n =>
      simp only [Option.map_some, D.keys_cons]
      exact ih.cons_cons _

theorem WF_nf (f : κ → Int → Option Int) {src : Ctr κ} (h : WF src) : WF (nf f src) :=
  List.Nodup.sublist (keys_nf_sublist f src) h

theorem mem_keys_nf {f : κ → Int → Option Int} {src : Ctr κ} (hw : WF src) {x : κ} :
    x ∈ keys (nf f src) ↔ ∃ c, D.get? src x = some c ∧ (f x c).isSome := by
  induction src with
  | nil => simp [nf]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    have hn := D.notMem_of_cons hw
    have ih := ih (D.WF_of_cons hw)
    unfold nf at *
    simp only [List.filterMap_cons, D.get?_cons]
    by_cases hax : a = x
    · subst hax
      have hnil : ¬ a ∈ keys (t.filterMap (fun p => (f p.1 p.2).map (Prod.mk p.1))) := by
        intro hm
        have := (keys_nf_sublist f t).subset hm
        exact hn this
      cases hf : f a b with
      | none => simp [hnil, hf]
      | some n => simp [hf]
    · cases hf : f a b with
      | none => simpa [hax] using ih
      | some n =>
        simp only [Option.map_some, D.keys_cons, List.mem_cons, hax, ite_false]
        constructor
        · rintro (h | h)
          · exact absurd h.symm hax
          · exact ih.mp h
        · intro h; exact Or.inr (ih.mpr h)

theorem get?_nf {f : κ → Int → Option Int} {src : Ctr κ} (hw : WF src) (x : κ) :
    D.get? (nf f src) x = (D.get? src x).bind (f x) := by
  induction src with
  | nil => simp [nf]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    have hn := D.notMem_of_cons hw
    have ih := ih (D.WF_of_cons hw)
    unfold nf at *
    simp only [List.filterMap_cons, D.get?_cons]
    by_cases hax : a = x
    · subst hax
      have hnil : D.get? (t.filterMap (fun p => (f p.1 p.2).map (Prod.mk p.1))) a = none := by
        rw [ih, D.get?_eq_none_iff.mpr hn]; rfl
      cases hf : f a b with
      | none => simp [hnil, hf]
      | some n => simp [D.get?_cons, hf]
    · cases hf : f a b with
      | none => simpa [hax] using ih
      | some n => simpa [hax, D.get?_cons] using ih

theorem cGet_nf {f : κ → Int → Option Int} {src : Ctr κ} (hw : WF src) (x : κ) :
    cGet (nf f src) x = if x ∈ keys src then (f x (cGet src x)).getD 0 else 0 := by
  simp only [cGet, get?_nf hw]
  by_cases h : x ∈ keys src
  · simp only [h, if_true]
    cases hg : D.get? src x with
    | none => exact absurd (D.get?_eq_none_iff.mp hg) (by simpa using h)
    | some c => simp
  · simp [h, D.get?_eq_none_iff.mpr h]

/-- A `loopInto` on a dict where every stored key is fresh appends its normal form. -/
theorem loopInto_eq (src : Ctr κ) (f : κ → Int → Option Int) (r : Ctr κ) (h : WF src)
    (hf : ∀ p ∈ src, (f p.1 p.2).isSome → p.1 ∉ keys r) :
    loopInto src f r = r ++ nf f src := by
  induction src generalizing r with
  | nil => simp [loopInto, nf]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    have hn := D.notMem_of_cons h
    have hwt := D.WF_of_cons h
    have hft : ∀ p ∈ t, (f p.1 p.2).isSome → p.1 ∉ keys r := fun q hq => hf q (List.mem_cons_of_mem _ hq)
    simp only [loopInto, List.foldl_cons, nf, List.filterMap_cons] at ih ⊢
    cases hc : f a b with
    | none =>
      simp only [Option.map_none]
      exact ih r hwt hft
    | some n =>
      have hax : a ∉ keys r := hf (a, b) (by simp) (by simp [hc])
      simp only [Option.map_some]
      rw [D.set_of_notMem _ hax, ih (r ++ [(a, n)]) hwt ?_]
      · simp
      · intro q hq hs
        simp only [D.keys_append, D.keys_cons, D.keys_nil, List.mem_append, List.mem_singleton, not_or]
        refine ⟨hft q hq hs, ?_⟩
        intro e
        have := D.mem_keys_of_mem hq
        rw [e] at this
        exact hn this

theorem loopInto_one (src : Ctr κ) (f : κ → Int → Option Int) (h : WF src) :
    loopInto src f [] = nf f src := by
  simpa using loopInto_eq src f [] h (by simp)

/-! ### Fresh-key side of the two-loop operators -/

theorem two_loops (a b : Ctr κ) (g : κ → Int → Option Int) (ha : WF a) (hb : WF b)
    (h : κ → Int → Option Int) (hh : ∀ p ∈ b, (h p.1 p.2).isSome → p.1 ∉ keys a) :
    loopInto b h (loopInto a g []) = nf g a ++ nf h b := by
  rw [loopInto_one a g ha]
  apply loopInto_eq b h _ hb
  intro p hp hs hm
  exact hh p hp hs ((keys_nf_sublist g a).subset hm)

/-! ### `keepPositive` -/

theorem del_eq_filter {d : Ctr κ} (hw : WF d) (x : κ) :
    D.del d x = d.filter (fun p => !decide (p.1 = x)) := by
  induction d with
  | nil => simp [D.del]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    have hn := D.notMem_of_cons hw
    have hwt := D.WF_of_cons hw
    by_cases hax : a = x
    · subst hax
      simp only [D.del, ite_true, List.filter_cons, decide_true, Bool.not_true, Bool.false_eq_true]
      symm
      apply List.filter_eq_self.mpr
      intro q hq
      have : q.1 ≠ a := by
        intro e
        have := D.mem_keys_of_mem hq
        rw [e] at this
        exact hn this
      simp [this]
    · simp [D.del, hax, List.filter_cons, ih hwt]

theorem delitem_eq_filter {d : Ctr κ} (hw : WF d) (x : κ) :
    delitem d x = d.filter (fun p => !decide (p.1 = x)) := by
  unfold delitem
  cases hm : D.mem d x with
  | true => simpa using del_eq_filter hw x
  | false =>
    have hx := D.mem_false_iff.mp hm
    simp only [Bool.false_eq_true, if_false]
    symm
    apply List.filter_eq_self.mpr
    intro q hq
    have : q.1 ≠ x := by
      intro e
      have := D.mem_keys_of_mem hq
      rw [e] at this
      exact hx this
    simp [this]

theorem WF_filter {d : Ctr κ} (h : WF d) (p : κ × Int → Bool) : WF (d.filter p) := by
  have : (keys (d.filter p)).Sublist (keys d) := (List.filter_sublist).map _
  exact List.Nodup.sublist this h

theorem foldl_delitem {d : Ctr κ} (hw : WF d) (ks : List κ) :
    ks.foldl delitem d = d.filter (fun p => !decide (p.1 ∈ ks)) := by
  induction ks generalizing d with
  | nil =>
    have : d.filter (fun _ => true) = d := List.filter_eq_self.mpr (by simp)
    simp [this]
  | cons k t ih =>
    simp only [List.foldl_cons]
    rw [delitem_eq_filter hw, ih (WF_filter hw _), List.filter_filter]
    apply List.filter_congr
    intro q _
    by_cases h1 : q.1 = k <;> by_cases h2 : q.1 ∈ t <;> simp [h1, h2]

theorem keepPositive_eq {c : Ctr κ} (hw : WF c) : keepPositive c = c.filter (fun p => decide (p.2 > 0)) := by
  unfold keepPositive
  simp only []
  rw [foldl_delitem hw]
  apply List.filter_congr
  intro q hq
  have key : q.1 ∈ (c.filter (fun p => !decide (p.2 > 0))).map (·.1) ↔ ¬ q.2 > 0 := by
    simp only [List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨r, ⟨hr, hp⟩, e⟩
      have h1 := D.get?_of_mem_pair (d := c) hw (x := r.1) (v := r.2) hr
      have h2 := D.get?_of_mem_pair (d := c) hw (x := q.1) (v := q.2) hq
      rw [e, h2] at h1
      have : q.2 = r.2 := by simpa using h1
      rw [this]
      simpa using hp
    · intro h
      exact ⟨q, ⟨hq, by simpa using h⟩, rfl⟩
  by_cases h : q.2 > 0
  · have h2 : q.1 ∉ (c.filter (fun p => !decide (p.2 > 0))).map (·.1) := fun m => key.mp m h
    simp [h, h2]
  · have h2 : q.1 ∈ (c.filter (fun p => !decide (p.2 > 0))).map (·.1) := key.mpr h
    simp [h, h2]

/-! ### The in-place loops -/

/-- One `for elem, o in other.items()` step: if `cond old o`, store `f old o`. -/
def stepI (cond : Int → Int → Bool) (f : Int → Int → Int) (s : Ctr κ) (p : κ × Int) : Ctr κ :=
  if cond (cGet s p.1) p.2 then D.set s p.1 (f (cGet s p.1) p.2) else s

/-- The value a key of the left operand ends with. -/
def upd (cond : Int → Int → Bool) (f : Int → Int → Int) (c o : Int) : Int :=
  if cond c o then f c o else c

/-- Normal form of the in-place loop: keys of `a` keep their place and their
updated value, and the new keys follow in the order of `b`. -/
def inf (cond : Int → Int → Bool) (f : Int → Int → Int) (a b : Ctr κ) : Ctr κ :=
  a.map (fun p => if p.1 ∈ keys b then (p.1, upd cond f p.2 (cGet b p.1)) else p) ++
    (b.filter (fun p => decide (p.1 ∉ keys a) && cond 0 p.2)).map (fun p => (p.1, f 0 p.2))

theorem WF_stepI (cond : Int → Int → Bool) (f : Int → Int → Int) {a : Ctr κ} (ha : WF a) (p : κ × Int) :
    WF (stepI cond f a p) := by
  unfold stepI
  split
  · exact D.WF_set ha _ _
  · exact ha

theorem foldl_stepI (cond : Int → Int → Bool) (f : Int → Int → Int) (a b : Ctr κ)
    (ha : WF a) (hb : WF b) : b.foldl (stepI cond f) a = inf cond f a b := by
  induction b generalizing a with
  | nil => simp [inf]
  | cons p t ih =>
    obtain ⟨e, o⟩ := p
    have hn : e ∉ keys t := D.notMem_of_cons hb
    have hwt := D.WF_of_cons hb
    have hne : ∀ q ∈ t, q.1 ≠ e := by
      intro q hq h
      have := D.mem_keys_of_mem hq
      rw [h] at this
      exact hn this
    simp only [List.foldl_cons]
    by_cases hea : e ∈ keys a
    · -- `e` is an old key, updated in place
      have hcg : cGet ((e, o) :: t) e = o := by simp [cGet, D.get?_cons]
      have hstep : stepI cond f a (e, o) =
          a.map (fun p => if p.1 = e then (p.1, upd cond f p.2 o) else p) := by
        unfold stepI
        dsimp only
        by_cases hc : cond (cGet a e) o = true
        · simp only [hc, if_true]
          rw [D.set_of_mem_map ha _ hea]
          apply List.map_congr_left
          intro q hq
          by_cases hq1 : q.1 = e
          · have hq2 : cGet a e = q.2 := by rw [← hq1]; exact cGet_of_mem ha hq
            have hc' : cond q.2 o = true := by rw [← hq2]; exact hc
            simp [hq1, upd, hc', hq2]
          · simp [hq1]
        · simp only [hc, Bool.false_eq_true, if_false]
          have hm : a.map (fun p => if p.1 = e then (p.1, upd cond f p.2 o) else p) = a.map id := by
            apply List.map_congr_left
            intro q hq
            by_cases hq1 : q.1 = e
            · have hq2 : cGet a e = q.2 := by rw [← hq1]; exact cGet_of_mem ha hq
              have hc' : ¬ cond q.2 o = true := by rw [← hq2]; exact hc
              obtain ⟨q1, q2⟩ := q
              simp only at hq1 hc' ⊢
              simp [hq1, upd, hc']
            · simp [hq1]
          rw [hm]; simp
      have hWF' : WF (stepI cond f a (e, o)) := WF_stepI cond f ha (e, o)
      have hk' : keys (stepI cond f a (e, o)) = keys a := by
        unfold stepI
        dsimp only
        split
        · exact D.keys_set_of_mem _ hea
        · rfl
      rw [ih _ hWF' hwt]
      unfold inf
      rw [hk', hstep]
      congr 1
      · rw [List.map_map]
        apply List.map_congr_left
        intro q _
        by_cases hq1 : q.1 = e
        · simp [hq1, hn, hcg]
        · have h3 : (q.1 ∈ keys ((e, o) :: t)) = (q.1 ∈ keys t) := by simp [hq1]
          have hne' : ¬ e = q.1 := fun h => hq1 h.symm
          have hg : cGet ((e, o) :: t) q.1 = cGet t q.1 := by
            simp [cGet, D.get?_cons, hne']
          simp only [Function.comp_apply, hq1, if_false, h3, hg]
      · simp [List.filter_cons, hea]
    · -- `e` is a new key
      have hg0 : cGet a e = 0 := cGet_eq_zero hea
      have hcg : ∀ q : κ × Int, q ∈ a → cGet ((e, o) :: t) q.1 = cGet t q.1 := by
        intro q hq
        have : e ≠ q.1 := by
          intro h
          have := D.mem_keys_of_mem hq
          rw [← h] at this
          exact hea this
        simp [cGet, D.get?_cons, this]
      have hneq : ∀ q : κ × Int, q ∈ a → q.1 ≠ e := by
        intro q hq h
        have := D.mem_keys_of_mem hq
        rw [h] at this
        exact hea this
      by_cases hc : cond 0 o = true
      · have hstep : stepI cond f a (e, o) = a ++ [(e, f 0 o)] := by
          unfold stepI
          simp only [hg0, hc, if_true]
          exact D.set_of_notMem _ hea
        have hw' := WF_stepI cond f ha (e, o)
        rw [hstep] at hw'
        rw [hstep, ih _ hw' hwt]
        unfold inf
        simp only [List.map_append, List.map_cons, List.map_nil, hn, if_false, D.keys_append,
          D.keys_cons, D.keys_nil, List.mem_append, List.mem_singleton, not_or, List.append_assoc]
        congr 1
        · apply List.map_congr_left
          intro q hq
          simp [hneq q hq, hcg q hq]
        · simp only [List.filter_cons, hea, not_false_eq_true, decide_true, hc, Bool.and_true, if_true,
            List.map_cons, List.singleton_append, List.cons.injEq, true_and]
          congr 1
          apply List.filter_congr
          intro q hq
          simp [hne q hq]
      · have hstep : stepI cond f a (e, o) = a := by
          unfold stepI
          simp [hg0, hc]
        rw [hstep, ih _ ha hwt]
        unfold inf
        congr 1
        · apply List.map_congr_left
          intro q hq
          simp [hneq q hq, hcg q hq]
        · simp [List.filter_cons, hc]

theorem WF_foldl_stepI (cond : Int → Int → Bool) (f : Int → Int → Int) :
    ∀ (b : Ctr κ) {a : Ctr κ}, WF a → WF (b.foldl (stepI cond f) a)
  | [], _, ha => ha
  | p :: t, _, ha => WF_foldl_stepI cond f t (WF_stepI cond f ha p)

theorem WF_inf (cond : Int → Int → Bool) (f : Int → Int → Int) {a b : Ctr κ} (ha : WF a) (hb : WF b) :
    WF (inf cond f a b) := by
  rw [← foldl_stepI cond f a b ha hb]
  exact WF_foldl_stepI cond f b ha

/-- Filtering a `map` to positive values is a `filterMap`. -/
theorem filter_map_pos (a : Ctr κ) (F : κ × Int → κ × Int) (G : κ × Int → Option (κ × Int))
    (h : ∀ p ∈ a, G p = if (F p).2 > 0 then some (F p) else none) :
    (a.map F).filter (fun p => decide (p.2 > 0)) = a.filterMap G := by
  induction a with
  | nil => rfl
  | cons p t ih =>
    have ih := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [List.map_cons, List.filter_cons, List.filterMap_cons, h p (by simp), ih]
    by_cases hp : (F p).2 > 0 <;> simp [hp]

end PyLean.CoreLibs.Coll
