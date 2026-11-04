import PyLean.CoreLibs.Coll.CounterProps4

/-!
Properties of the generic `Counter` model, continued: the `Mapping` branch of `update` and
`subtract` on a non-empty counter, the keyword path, the constructor on a `Mapping`, and the
arithmetic of the in-place operators, key by key.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PyLean.CoreLibs.Coll

open PyLean

variable {κ ν : Type} [DecidableEq κ]

/-! ### A loop that rewrites each key at most once -/

/-- One `self[elem] = f(elem, count, self[elem])` step, or no store when `f` gives `none`. -/
def stepG (H : κ → ν → ν → Option ν) (z : ν) (s : D κ ν) (p : κ × ν) : D κ ν :=
  match H p.1 p.2 ((D.get? s p.1).getD z) with
  | some w => D.set s p.1 w
  | none => s

theorem get?_foldl_stepG (H : κ → ν → ν → Option ν) (z : ν) (k : κ) :
    ∀ (L d : D κ ν), D.WF L →
      D.get? (L.foldl (stepG H z) d) k = match D.get? L k with
        | some v => (match H k v ((D.get? d k).getD z) with
          | some w => some w
          | none => D.get? d k)
        | none => D.get? d k
  | [], d, _ => rfl
  | p :: t, d, hw => by
    obtain ⟨a, b⟩ := p
    have hn := D.notMem_of_cons hw
    simp only [List.foldl_cons]
    rw [get?_foldl_stepG H z k t _ (D.WF_of_cons hw)]
    by_cases hk : a = k
    · subst hk
      have ht : D.get? t a = none := D.get?_eq_none_iff.2 hn
      simp only [ht, D.get?_cons, if_pos rfl]
      cases hH : H a b ((D.get? d a).getD z) <;> simp [stepG, hH, D.get?_set]
    · simp only [D.get?_cons, hk, if_false, stepG]
      cases hH : H a b ((D.get? d a).getD z) with
      | none => rfl
      | some w => simp [D.get?_set, hk]

theorem WF_foldl_stepG (H : κ → ν → ν → Option ν) (z : ν) :
    ∀ (L d : D κ ν), D.WF d → D.WF (L.foldl (stepG H z) d)
  | [], _, h => h
  | p :: t, d, h => by
    simp only [List.foldl_cons]
    apply WF_foldl_stepG H z t
    unfold stepG
    split
    · exact D.WF_set h _ _
    · exact h

theorem HashOk_set {K : KOps κ} {s : D κ ν} (hs : HashOk K s) {k : κ} (hk : K.hash k = .ok ()) (v : ν) :
    HashOk K (D.set s k v) := by
  intro x hx
  rw [D.keys_set] at hx
  split at hx
  · exact hs x hx
  · rcases List.mem_append.1 hx with h | h
    · exact hs x h
    · simp at h; subst h; exact hk

theorem HashOk_foldl_stepG {K : KOps κ} (H : κ → ν → ν → Option ν) (z : ν) :
    ∀ (L d : D κ ν), HashOk K d → HashOk K L → HashOk K (L.foldl (stepG H z) d)
  | [], _, h, _ => h
  | p :: t, d, h, hL => by
    simp only [List.foldl_cons]
    apply HashOk_foldl_stepG H z t _ _ (fun x hx => hL x (by simp [hx]))
    unfold stepG
    split
    · exact HashOk_set h (hL p.1 (by simp)) _
    · exact h

theorem get?_filter_val {d : D κ ν} (hw : D.WF d) (G : ν → Bool) (k : κ) :
    D.get? (d.filter (fun p => G p.2)) k = (D.get? d k).filter G := by
  induction d with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    have hn := D.notMem_of_cons hw
    have iht := ih (D.WF_of_cons hw)
    by_cases hk : a = k
    · subst hk
      have ht : D.get? t a = none := D.get?_eq_none_iff.2 hn
      cases hg : G b
      · simp only [List.filter_cons, hg, Bool.false_eq_true, if_false, iht, ht, D.get?_cons, if_true]
        simp [Option.filter, hg]
      · simp [List.filter_cons, hg, D.get?_cons, Option.filter]
    · cases hg : G b <;> simp [List.filter_cons, hg, D.get?_cons, hk, iht]

/-- A pure loop over a counter's items is the fold of its steps. -/
theorem loopS_stepG {K : KOps κ} (H : κ → ν → ν → Option ν) (z : ν) (f : D κ ν → κ × ν → Py (D κ ν))
    (L d : D κ ν) (hf : ∀ s, ∀ p ∈ L, f s p = .ok (stepG H z s p)) :
    loopS f d L = (L.foldl (stepG H z) d, none) :=
  loopS_pure L d hf

/-! ### `update` and `subtract` with a `Mapping`, keywords, the constructor -/

/-- **The `Mapping` branch adds (or subtracts) counts in the source's order of operands, and the
keywords go through it after the positional argument.** `d.subtract(**kw)` is
`d.subtract(kw)`: each keyword `k=v` stores `d.get(k, 0) - v`. For every key type, every count type
whose `+` and `-` are pure functions `A`, `S` (any functions: non-commutative, non-numeric), and
every dict `L` of hashable keys: on a non-empty counter `d`, `d.update(L)` stores
`L[k] + d.get(k, 0)` (that operand order, `:702`) for each key of `L`, every other key keeping
its count, where `dict.update` would store `L[k]`; `d.subtract(L)` stores `d.get(k, 0) - L[k]`
(`:731`) on any counter. `update(src, **kw)` and `subtract(src, **kw)` are the call without
keywords followed by the same call on the keyword dict alone, and `Counter(**kw)` holds `kw`'s
items; `Counter(L)` holds `L`'s items, and `Counter(L, **kw)` adds the keywords to them by the
same rule when `L` is non-empty.

Source: docstrings, Lib/collections/__init__.py:606-615 ('initialize the count from another
mapping'), :678 ('Like dict.update() but add counts instead of replacing them'), :712-714. -/
def UpdateMappingKw : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] [DecidableEq ν] (K : KOps κ) (N : Num ν) (A S : ν → ν → ν)
    (d L kw : D κ ν) (src : Src κ ν) (k : κ), D.WF L → D.WF kw → HashOk K L → HashOk K kw →
    N.add = (fun x y => .ok (A x y)) → N.sub = (fun x y => .ok (S x y)) →
    (d ≠ [] → update K N {} d (.mapping (dictSrc L)) [] =
        (L.foldl (stepG (fun _ v c => some (A v c)) N.zero) d, none) ∧
      D.get? (update K N {} d (.mapping (dictSrc L)) []).1 k =
        (match D.get? L k with
         | some v => some (A v (at0 N d k))
         | none => D.get? d k)) ∧
    (subtract K N {} d (.mapping (dictSrc L)) []).2 = none ∧
    D.get? (subtract K N {} d (.mapping (dictSrc L)) []).1 k =
      (match D.get? L k with
       | some v => some (S (at0 N d k) v)
       | none => D.get? d k) ∧
    update K N {} d src kw = (update K N {} d src []).andThen (fun d' => update K N {} d' .none kw) ∧
    subtract K N {} d src kw = (subtract K N {} d src []).andThen (fun d' => subtract K N {} d' .none kw) ∧
    counterNew K N .none kw = .ok kw ∧
    counterNew K N (.mapping (dictSrc L)) [] = .ok L ∧
    (L ≠ [] → ∃ r, counterNew K N (.mapping (dictSrc L)) kw = .ok r ∧
      D.get? r k = (match D.get? kw k with
        | some w => some (A w (at0 N L k))
        | none => D.get? L k)) ∧
    subtract K N {} d .none kw = subtract K N {} d (.mapping (dictSrc kw)) [] ∧
    (subtract K N {} d .none kw).2 = none ∧
    D.get? (subtract K N {} d .none kw).1 k =
      (match D.get? kw k with
       | some v => some (S (at0 N d k) v)
       | none => D.get? d k)

theorem updateLoop_dict (K : KOps κ) (N : Num ν) (A : ν → ν → ν) (d L : D κ ν) (hh : HashOk K L)
    (hA : N.add = fun x y => .ok (A x y)) :
    updateLoop K N {} d (dictSrc L) = (L.foldl (stepG (fun _ v c => some (A v c)) N.zero) d, none) := by
  show forIt _ d (FIt.ofList L) = _
  simp only [forIt, FIt.ofList]
  rw [loopS_stepG (K := K) (fun _ v c => some (A v c)) N.zero _ L d (by
    intro s p hp
    dsimp only [boundGet, setItem]
    rw [dGet_ok s N.zero (hash_of_mem hh hp), ok_bind, hA]
    simp only [ok_bind]
    rw [dSet_ok s _ (hash_of_mem hh hp)]
    rfl)]

theorem subtract_dict (K : KOps κ) (N : Num ν) (S : ν → ν → ν) (d L : D κ ν) (hh : HashOk K L)
    (hS : N.sub = fun x y => .ok (S x y)) :
    subtract K N {} d (.mapping (dictSrc L)) [] =
      (L.foldl (stepG (fun _ v c => some (S c v)) N.zero) d, none) := by
  unfold subtract subtractSrc
  simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ite_false]
  show Out.andThen (forIt _ d (FIt.ofList L)) _ = _
  simp only [forIt, FIt.ofList]
  rw [loopS_stepG (K := K) (fun _ v c => some (S c v)) N.zero _ L d (by
    intro s p hp
    dsimp only [boundGet, setItem]
    rw [dGet_ok s N.zero (hash_of_mem hh hp), ok_bind, hS]
    simp only [ok_bind]
    rw [dSet_ok s _ (hash_of_mem hh hp)]
    rfl)]
  rfl

theorem update_nonempty_dict [DecidableEq ν] (K : KOps κ) (N : Num ν) (A : ν → ν → ν) (d L : D κ ν)
    (hd : d ≠ []) (hh : HashOk K L) (hA : N.add = fun x y => .ok (A x y)) :
    update K N {} d (.mapping (dictSrc L)) [] = (L.foldl (stepG (fun _ v c => some (A v c)) N.zero) d, none) := by
  have he : d.isEmpty = false := by cases d <;> simp_all
  have h1 : update K N {} d (.mapping (dictSrc L)) [] = (updateMapping K N {} d (dictSrc L)).andThen
      (fun d => (d, none)) := rfl
  rw [h1]
  simp only [updateMapping, he, Bool.not_false, if_true, updateLoop_dict K N A d L hh hA]
  rfl

theorem subtract_kw_eq (K : KOps κ) (N : Num ν) (d kw : D κ ν) :
    subtract K N {} d .none kw = subtract K N {} d (.mapping (dictSrc kw)) [] := by
  cases kw with
  | nil => rfl
  | cons p t =>
    show subtractSrc K N {} d (.mapping (dictSrc (p :: t))) =
      (subtractSrc K N {} d (.mapping (dictSrc (p :: t)))).andThen (fun d => (d, none))
    cases subtractSrc K N {} d (.mapping (dictSrc (p :: t))) with
    | mk s e => cases e <;> rfl

theorem updateMappingKw_proven : UpdateMappingKw := by
  intro κ ν _ _ K N A S d L kw src k hwL hwkw hhL hhkw hA hS
  have hsub := subtract_dict K N S d L hhL hS
  have hkeq := subtract_kw_eq K N d kw
  have hsubkw := subtract_dict K N S d kw hhkw hS
  refine ⟨fun hd => ⟨update_nonempty_dict K N A d L hd hhL hA, ?_⟩, by rw [hsub], ?_, ?_, ?_, ?_, ?_, ?_,
    hkeq, by rw [hkeq, hsubkw], ?_⟩
  · rw [update_nonempty_dict K N A d L hd hhL hA]
    rw [get?_foldl_stepG _ _ k L d hwL]
    cases D.get? L k <;> rfl
  · rw [hsub, get?_foldl_stepG _ _ k L d hwL]
    cases D.get? L k <;> rfl
  · unfold update
    cases updateSrc K N {} d src with
    | mk s e => cases e <;> rfl
  · unfold subtract
    cases subtractSrc K N {} d src with
    | mk s e => cases e <;> rfl
  · cases kw with
    | nil => rfl
    | cons p t =>
      show (Out.andThen ([], none) (fun d => if !(p :: t).isEmpty then
        updateSrc K N {} d (.mapping (dictSrc (p :: t))) else (d, none))).toPy = _
      simp only [Out.andThen, List.isEmpty_cons, Bool.not_false, if_true, updateSrc, updateMapping,
        List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false, dictMerge, dictSrc, Out.toPy]
      rw [update_nil_WF hwkw]
  · show (Out.andThen (updateMapping K N {} [] (dictSrc L)) (fun d => (d, none))).toPy = _
    simp only [updateMapping, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false, dictMerge,
      dictSrc, update_nil_WF hwL]
    rfl
  · intro hL
    have hu : counterNew K N (.mapping (dictSrc L)) kw =
        (update K N {} L .none kw).toPy := by
      show (Out.andThen (updateMapping K N {} [] (dictSrc L)) _).toPy = _
      simp only [updateMapping, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false, dictMerge,
        dictSrc, update_nil_WF hwL]
      rfl
    cases kw with
    | nil =>
      refine ⟨L, by rw [hu]; rfl, ?_⟩
      simp [D.get?]
    | cons p t =>
      have hk : update K N {} L .none (p :: t) = updateMapping K N {} L (dictSrc (p :: t)) := rfl
      have he : L.isEmpty = false := by cases L <;> simp_all
      refine ⟨(p :: t).foldl (stepG (fun _ v c => some (A v c)) N.zero) L, ?_, ?_⟩
      · rw [hu, hk]
        simp only [updateMapping, he, Bool.not_false, if_true, updateLoop_dict K N A L _ hhkw hA]
        rfl
      · rw [get?_foldl_stepG _ _ k _ L hwkw]
        cases D.get? (p :: t) k <;> rfl
  · rw [hkeq, hsubkw, get?_foldl_stepG _ _ k kw d hwkw]
    cases D.get? kw k <;> rfl

/-! ### In-place operators -/

/-- **The in-place operators' arithmetic, key by key.** For every key type, every count type
whose `+=`, `-=`, `<` and `>` (with their truth tests) are pure functions `IA`, `IS`, `LT`,
`GT`, and every pair of counters: `a += b` leaves at each key `a[k] += b[k]` for the keys of `b`
(new keys starting from `0`), `a[k]` for the others, and then only the counts `> 0`; `a -= b`
the same with `-=`; `a |= b` takes `b[k]` where `b[k] > a[k]` and keeps `a[k]` (or no key)
otherwise; `a &= b` takes `b[k]` (`0` when missing) where `b[k] < a[k]` and keeps `a[k]`
otherwise; none raises. An `+=` that replaced counts, or an `|=` that took the minimum, fails.

Source: docstrings, Lib/collections/__init__.py:964-1011 ('Inplace add from another counter,
keeping only positive counts', 'Inplace union is the maximum of value from either counter',
'Inplace intersection is the minimum of corresponding counts'). -/
def InplaceArith : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (K : KOps κ) (rk : κ → String) (N : Num ν) (IA IS : ν → ν → ν)
    (LT GT : ν → ν → Bool) (a b : D κ ν) (k : κ),
    D.WF a → D.WF b → HashOk K a → HashOk K b →
    N.iadd = (fun x y => .ok (IA x y)) → N.isub = (fun x y => .ok (IS x y)) →
    N.lt = (fun x y => .ok (LT x y)) → N.gt = (fun x y => .ok (GT x y)) →
    let pos := fun n => GT n N.zero
    (iaddC K rk N a (ctrOpnd K N b)).2 = none ∧
    D.get? (iaddC K rk N a (ctrOpnd K N b)).1 k =
      (match D.get? b k with
       | some v => some (IA (at0 N a k) v)
       | none => D.get? a k).filter pos ∧
    (isubC K rk N a (ctrOpnd K N b)).2 = none ∧
    D.get? (isubC K rk N a (ctrOpnd K N b)).1 k =
      (match D.get? b k with
       | some v => some (IS (at0 N a k) v)
       | none => D.get? a k).filter pos ∧
    (iorC K rk N a (ctrOpnd K N b)).2 = none ∧
    D.get? (iorC K rk N a (ctrOpnd K N b)).1 k =
      (match D.get? b k with
       | some v => if GT v (at0 N a k) then some v else D.get? a k
       | none => D.get? a k).filter pos ∧
    (iandC K rk N a (ctrOpnd K N b)).2 = none ∧
    D.get? (iandC K rk N a (ctrOpnd K N b)).1 k =
      (match D.get? a k with
       | some v => if LT (at0 N b k) v then some (at0 N b k) else D.get? a k
       | none => D.get? a k).filter pos

theorem inplace_tail {K : KOps κ} {rk : κ → String} {N : Num ν} {GT : ν → ν → Bool}
    (hG : N.gt = fun x y => .ok (GT x y)) (H : κ → ν → ν → Option ν) (L a : D κ ν)
    (wa : D.WF a) (wL : D.WF L) (ha : HashOk K a) (hL : HashOk K L) (k : κ) :
    let U := L.foldl (stepG H N.zero) a
    Out.andThen (U, none) (keepPositive K rk N) = (U.filter (fun p => GT p.2 N.zero), none) ∧
    D.get? (U.filter (fun p => GT p.2 N.zero)) k =
      (match D.get? L k with
        | some v => (match H k v ((D.get? a k).getD N.zero) with
          | some w => some w
          | none => D.get? a k)
        | none => D.get? a k).filter (fun n => GT n N.zero) := by
  intro U
  have hw : D.WF U := WF_foldl_stepG H N.zero L a wa
  have hh : HashOk K U := HashOk_foldl_stepG H N.zero L a ha hL
  refine ⟨(keepPositiveFilters_proven κ ν K rk N GT U hw hh hG).1, ?_⟩
  rw [get?_filter_val hw (fun n => GT n N.zero), get?_foldl_stepG H N.zero k L a wL]

theorem inplaceArith_proven : InplaceArith := by
  intro κ ν _ K rk N IA IS LT GT a b k wa wb ha hb hIA hIS hL hG
  simp only
  have hadd : iaddC K rk N a (ctrOpnd K N b) =
      Out.andThen (b.foldl (stepG (fun _ v c => some (IA c v)) N.zero) a, none) (keepPositive K rk N) := by
    unfold iaddC
    show Out.andThen (forIt _ a (FIt.ofList b)) _ = _
    simp only [forIt, FIt.ofList]
    rw [loopS_stepG (K := K) (fun _ v c => some (IA c v)) N.zero _ b a (by
      intro s p hp
      rw [dGet_ok s N.zero (hash_of_mem hb hp), ok_bind, hIA]
      simp only [ok_bind]
      rw [dSet_ok s _ (hash_of_mem hb hp)]
      rfl)]
  have hsub : isubC K rk N a (ctrOpnd K N b) =
      Out.andThen (b.foldl (stepG (fun _ v c => some (IS c v)) N.zero) a, none) (keepPositive K rk N) := by
    unfold isubC
    show Out.andThen (forIt _ a (FIt.ofList b)) _ = _
    simp only [forIt, FIt.ofList]
    rw [loopS_stepG (K := K) (fun _ v c => some (IS c v)) N.zero _ b a (by
      intro s p hp
      rw [dGet_ok s N.zero (hash_of_mem hb hp), ok_bind, hIS]
      simp only [ok_bind]
      rw [dSet_ok s _ (hash_of_mem hb hp)]
      rfl)]
  have hor : iorC K rk N a (ctrOpnd K N b) =
      Out.andThen (b.foldl (stepG (fun _ v c => if GT v c then some v else none) N.zero) a, none)
        (keepPositive K rk N) := by
    unfold iorC
    show Out.andThen (forIt _ a (FIt.ofList b)) _ = _
    simp only [forIt, FIt.ofList]
    rw [loopS_stepG (K := K) (fun _ v c => if GT v c then some v else none) N.zero _ b a (by
      intro s p hp
      rw [dGet_ok s N.zero (hash_of_mem hb hp), ok_bind, hG]
      simp only [ok_bind, stepG]
      cases GT p.2 ((D.get? s p.1).getD N.zero)
      · rfl
      · simp only [if_true]; rw [dSet_ok s _ (hash_of_mem hb hp)])]
  have hand : iandC K rk N a (ctrOpnd K N b) =
      Out.andThen (a.foldl (stepG (fun k v _ => if LT (at0 N b k) v then some (at0 N b k) else none) N.zero) a,
        none) (keepPositive K rk N) := by
    unfold iandC
    rw [loopS_stepG (K := K) (fun k v _ => if LT (at0 N b k) v then some (at0 N b k) else none) N.zero _ a a (by
      intro s p hp
      show (do let oc ← dGet K b p.1 N.zero; let lt ← N.lt oc p.2; if lt then dSet K s p.1 oc else pure s) = _
      rw [dGet_ok b N.zero (hash_of_mem ha hp), ok_bind, hL]
      simp only [ok_bind, stepG, at0]
      by_cases hl : LT ((D.get? b p.1).getD N.zero) p.2 = true <;> simp [hl, dSet_ok s _ (hash_of_mem ha hp)])]
  have t1 := inplace_tail (K := K) (rk := rk) hG (fun _ v c => some (IA c v)) b a wa wb ha hb k
  have t2 := inplace_tail (K := K) (rk := rk) hG (fun _ v c => some (IS c v)) b a wa wb ha hb k
  have t3 := inplace_tail (K := K) (rk := rk) hG (fun _ v c => if GT v c then some v else none) b a wa wb ha hb k
  have t4 := inplace_tail (K := K) (rk := rk) hG
    (fun k v _ => if LT (at0 N b k) v then some (at0 N b k) else none) a a wa wa ha ha k
  simp only at t1 t2 t3 t4
  rw [hadd, t1.1, hsub, t2.1, hor, t3.1, hand, t4.1]
  refine ⟨rfl, ?_, rfl, ?_, rfl, ?_, rfl, ?_⟩
  · rw [t1.2]; cases D.get? b k <;> rfl
  · rw [t2.2]; cases D.get? b k <;> rfl
  · rw [t3.2]
    cases hbk : D.get? b k with
    | none => rfl
    | some v => by_cases hc : GT v ((D.get? a k).getD N.zero) = true <;> simp [hc, at0]
  · rw [t4.2]
    cases hak : D.get? a k with
    | none => rfl
    | some v => by_cases hc : LT ((D.get? b k).getD N.zero) v = true <;> simp [hc, at0, hak]

end PyLean.CoreLibs.Coll
