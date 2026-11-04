import PyLean.CoreLibs.Coll.ODictUpd

/-!
More `OrderedDict` properties: absent keys for `__delitem__`/`pop`, `__eq__` in full, the views and
`__reversed__`, `__init__` with keywords, and `|=`, `|`, reflected `|`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PyLean.CoreLibs.Coll

open PyLean

variable {κ ν : Type} [DecidableEq κ]

theorem get?_none_of_inv {o : OD κ ν} {L : List (Nat × κ)} (I : ODInv o L) {k : κ} (h : k ∉ L.map (·.2)) :
    D.get? o.d k = none := by
  have := I.mem k
  unfold D.mem at this
  cases hg : D.get? o.d k with
  | none => rfl
  | some v => rw [hg] at this; simp [h] at this

theorem get?_some_of_inv {o : OD κ ν} {L : List (Nat × κ)} (I : ODInv o L) {k : κ} (h : k ∈ L.map (·.2)) :
    ∃ v, D.get? o.d k = some v := by
  have := I.mem k
  unfold D.mem at this
  exact Option.isSome_iff_exists.1 (by rw [this]; simpa using h)

/-- **An absent key: `del` raises, `pop` raises or returns the default.** For every instance and every
hashable key not in it: `del od[key]` raises `KeyError(key)` (from `dict_delitem`, :137), `od.pop(key)`
raises `KeyError(key)` (no default: the `__marker` test of :264-265), and `od.pop(key, d)` returns `d` and
leaves `od` as it was (:266).

Source: docstrings, Lib/collections/__init__.py:247-250. -/
def ODAbsent : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (K : KOps κ) (rk : κ → String) (o : OD κ ν) (L : List (Nat × κ)) (key : κ)
    (v : ν), ODInv o L → K.hash key = .ok () → key ∉ L.map (·.2) →
    odDel K rk o key = .error (.keyError (rk key)) ∧ odPop K rk o key none = .error (.keyError (rk key)) ∧
    odPop K rk o key (some v) = .ok (v, o)

theorem odAbsent_proven : ODAbsent := by
  intro κ ν _ K rk o L key v I hk hn
  have hm : D.mem o.d key = false := by rw [I.mem key]; simp [hn]
  have hg := get?_none_of_inv I hn
  refine ⟨?_, ?_, ?_⟩
  · simp [odDel, dictDelitem, dHash_ok hk, hm]
  · cases he : o.d.isEmpty <;> simp [odPop, he, dHash_ok hk, hg]
  · cases he : o.d.isEmpty <;> simp [odPop, he, dHash_ok hk, hg]

theorem dictEq_reverse [DecidableEq ν] (veq : ν → ν → Py Bool) {a : D κ ν} (hw : D.WF a) :
    dictEq veq a a.reverse = .ok true := by
  have hwr : D.WF a.reverse := by unfold D.WF D.keys at *; rw [List.map_reverse]; exact (List.reverse_perm _).nodup_iff.2 hw
  unfold dictEq
  rw [if_neg (by simp)]
  rw [allM_pure (P := fun _ => true) a (fun p hp => by
    rw [D.get?_of_mem_pair hwr (List.mem_reverse.2 hp)]; simp)]
  simp

theorem zip_all_eq_true (l : List κ) : (l.zip l).all (fun q => decide (q.1 = q.2)) = true := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.zip_cons_cons, ih]

/-- **`==` in full.** For every pair of instances: equal items in the same order give `True`; unequal
items (`dict.__eq__` false) give `False`; an exception from a value `==` propagates; equal items in a
different order give `False` (see `ODOrderViews`). Against a plain dict the order is ignored: `od` equals
the dict of its items in reverse order.

Source: docstring, Lib/collections/__init__.py:317-321. -/
def ODEqFull : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] [DecidableEq ν] (veq : ν → ν → Py Bool) (o p : OD κ ν) (L M : List (Nat × κ))
    (e : PyExc), ODInv o L → ODInv p M →
    (dictEq veq o.d p.d = .ok true → L.map (·.2) = M.map (·.2) → odEq veq o (.od p) = .ok true) ∧
    (dictEq veq o.d p.d = .ok false → odEq veq o (.od p) = .ok false) ∧
    (dictEq veq o.d p.d = .error e → odEq veq o (.od p) = .error e) ∧
    odEq veq o (.dict o.d.reverse) = .ok true

theorem odEqFull_proven : ODEqFull := by
  intro κ ν _ _ veq o p L M e I J
  have hk := keysList_inv I
  have hk' := keysList_inv J
  refine ⟨fun he hs => ?_, fun he => ?_, fun he => ?_, ?_⟩
  · simp only [odEq, he, ok_bind, if_true, hk, hk', hs, zip_all_eq_true]; rfl
  · simp only [odEq, he, ok_bind]; rfl
  · simp only [odEq, he]; rfl
  · exact dictEq_reverse veq I.wfd

/-! ### `__reversed__` and the views -/

theorem genRun_back (o : OD κ ν) (n : Nat) :
    ∀ (L : List (Nat × κ)), L.length = n → ∀ (fuel : Nat) (g : OGen) (m : Nat), g ≠ .done →
      (∀ x ∈ L.map (·.1), x ≠ 0) → L.length < fuel → Chain o.heap 0 L m →
      (o.link g.from_).prev = some (lastOf 0 L) → odGenRun o true fuel g = .ok (L.map (·.2)).reverse := by
  induction n with
  | zero =>
    intro L hL fuel g m hg _ hf _ hp
    have : L = [] := List.eq_nil_of_length_eq_zero hL
    subst this
    cases fuel with
    | zero => simp at hf
    | succ f =>
      cases g with
      | done => exact absurd rfl hg
      | fresh => simp only [OGen.from_, OD.link, lastOf] at hp; simp [odGenRun, odGenNext, OD.link, hp]
      | at_ i => simp only [OGen.from_, OD.link, lastOf] at hp; simp [odGenRun, odGenNext, OD.link, hp]
  | succ n ih =>
    intro L hL fuel g m hg hz hf hch hp
    obtain ⟨A, q, rfl⟩ : ∃ A q, L = A ++ [q] := by
      rcases List.eq_nil_or_concat L with h | ⟨A, q, h⟩
      · subst h; simp at hL
      · exact ⟨A, q, by rw [h, List.concat_eq_append]⟩
    obtain ⟨i, k⟩ := q
    rw [chain_append] at hch
    have hi : o.heap i = ⟨some k, some (lastOf 0 A), some m⟩ :=
      (show o.heap i = ⟨some k, some (lastOf 0 A), some (nxt ([] : List (Nat × κ)) m)⟩ ∧ True from hch.2).1
    have hi0 : i ≠ 0 := hz i (by simp)
    have hlast : lastOf 0 (A ++ [(i, k)]) = i := by simp [lastOf]
    rw [hlast] at hp
    cases fuel with
    | zero => simp at hf
    | succ f =>
      have hstep : odGenNext o true g = (.ok (some k), .at_ i) := by
        cases g with
        | done => exact absurd rfl hg
        | fresh => simp only [OGen.from_, OD.link] at hp; simp [odGenNext, OD.link, hp, hi0, hi]
        | at_ j => simp only [OGen.from_, OD.link] at hp; simp [odGenNext, OD.link, hp, hi0, hi]
      simp only [odGenRun, hstep]
      rw [ih A (by simp at hL; omega) f (.at_ i) i (by simp) (fun x hx => hz x (by simp [hx]))
        (by simp at hf; omega) hch.1 (by simp [OGen.from_, OD.link, hi])]
      simp
      rfl

theorem mapM_items (rk : κ → String) (o : OD κ ν) :
    ∀ (ks : List κ), (∀ k ∈ ks, ∃ v, D.get? o.d k = some v) →
      ks.mapM (fun k => do let v ← odGetitem rk o k; pure (k, v)) =
        .ok (ks.filterMap (fun k => (D.get? o.d k).map (k, ·)))
  | [], _ => rfl
  | k :: ks, h => by
    obtain ⟨v, hv⟩ := h k (by simp)
    rw [List.mapM_cons, mapM_items rk o ks (fun k' hk' => h k' (by simp [hk']))]
    simp [odGetitem, hv]

theorem mapM_values (rk : κ → String) (o : OD κ ν) :
    ∀ (ks : List κ), (∀ k ∈ ks, ∃ v, D.get? o.d k = some v) →
      ks.mapM (odGetitem rk o) = .ok (ks.filterMap (D.get? o.d))
  | [], _ => rfl
  | k :: ks, h => by
    obtain ⟨v, hv⟩ := h k (by simp)
    rw [List.mapM_cons, mapM_values rk o ks (fun k' hk' => h k' (by simp [hk']))]
    simp [odGetitem, hv]

/-- **The views iterate in link order, forwards and backwards.** For every instance with list `L`:
`list(od.keys())` is `list(od)`, the keys of `L`; `list(od.items())` and `list(od.values())` are their
items and values in that order; `reversed(od)`, `reversed(od.keys())`, `reversed(od.items())` and
`reversed(od.values())` give the same lists reversed, walking the `prev` links back from the root.

Source: Lib/collections/__init__.py:69-84, :155-162, :228-240. -/
def ODViewsOrder : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (rk : κ → String) (o : OD κ ν) (L : List (Nat × κ)), ODInv o L →
    let ks := L.map (·.2)
    odKeysView o false = .ok o.keysList ∧ o.keysList = ks ∧
    odItemsView rk o false = .ok (ks.filterMap (fun k => (D.get? o.d k).map (k, ·))) ∧
    odValuesView rk o false = .ok (ks.filterMap (D.get? o.d)) ∧
    odKeysView o true = .ok ks.reverse ∧
    odItemsView rk o true = .ok (ks.reverse.filterMap (fun k => (D.get? o.d k).map (k, ·))) ∧
    odValuesView rk o true = .ok (ks.reverse.filterMap (D.get? o.d))

theorem odViewsOrder_proven : ODViewsOrder := by
  intro κ ν _ rk o L I
  simp only
  have hz : ∀ x ∈ L.map (·.1), x ≠ 0 := fun x hx => Nat.pos_iff_ne_zero.1 (I.pos x hx).1
  have hf : L.length < o.next + 1 := by have := I.len; omega
  have hfwd : odKeysView o false = .ok (L.map (·.2)) :=
    (odIterGen_proven κ ν o L 0 (o.next + 1) I hf).1
  have hback : odKeysView o true = .ok (L.map (·.2)).reverse :=
    genRun_back o L.length L rfl (o.next + 1) .fresh 0 (by simp) hz hf I.chain
      (by simp [OGen.from_, OD.link, I.root])
  have hval : ∀ k ∈ L.map (·.2), ∃ v, D.get? o.d k = some v := fun k hk => get?_some_of_inv I hk
  have hvalr : ∀ k ∈ (L.map (·.2)).reverse, ∃ v, D.get? o.d k = some v := fun k hk => hval k (List.mem_reverse.1 hk)
  refine ⟨by rw [hfwd, keysList_inv I], keysList_inv I, ?_, ?_, hback, ?_, ?_⟩
  · simp only [odItemsView, hfwd, ok_bind]; exact mapM_items rk o _ hval
  · simp only [odValuesView, hfwd, ok_bind]; exact mapM_values rk o _ hval
  · simp only [odItemsView, hback, ok_bind]; exact mapM_items rk o _ hvalr
  · simp only [odValuesView, hback, ok_bind]; exact mapM_values rk o _ hvalr

/-! ### `__init__` with keywords, `|=`, `|`, reflected `|` -/

/-- `od.update(other)` for another `OrderedDict` `other` with list `M`: the keys of `other` in its order,
after those of `od`. -/
theorem odUpdate_src_inv (K : KOps κ) (o n : OD κ ν) (L M : List (Nat × κ)) (I : ODInv o L) (J : ODInv n M)
    (hL : ∀ k ∈ L.map (·.2), K.hash k = .ok ()) :
    ∃ n' M', odUpdate K n (odSrc o) = (n', none) ∧ ODInv n' M' ∧ M'.map (·.2) = firstSeen (M.map (·.2)) (L.map (·.2)) := by
  have hval : ∀ k ∈ L.map (·.2), ∃ w, D.get? o.d k = some w := fun k hk => get?_some_of_inv I hk
  have hk := keysList_inv I
  let g : κ → Py ν := fun k => match D.get? o.d k with
    | some w => .ok w
    | none => .error (.keyError "~key")
  obtain ⟨n', M', h, J', hM'⟩ := setLoop_inv K (fun n' k => do let w ← g k; odSet K n' k w) id (L.map (·.2))
    n M J hL (fun n' k hk' => by
      obtain ⟨w, hw⟩ := hval k hk'
      exact ⟨w, by simp [g, hw]⟩)
  refine ⟨n', M', ?_, J', by simpa using hM'⟩
  show forIt (fun n' k => do let w ← g k; odSet K n' k w) n (FIt.ofList o.keysList) = _
  rw [hk]
  simp only [forIt, FIt.ofList, h]

theorem odUpdate_pairs_inv (K : KOps κ) (o : OD κ ν) (L : List (Nat × κ)) (ps : List (κ × ν)) (I : ODInv o L)
    (hps : ∀ q ∈ ps, K.hash q.1 = .ok ()) :
    ∃ o' L', odUpdate K o (.pairs (.ok (FIt.ofList (ps.map .ok)))) = (o', none) ∧ ODInv o' L' ∧
      L'.map (·.2) = firstSeen (L.map (·.2)) (ps.map (·.1)) := by
  obtain ⟨o', L', h, I', hL'⟩ := setLoop_inv K (fun o (q : κ × ν) => odSet K o q.1 q.2) (·.1) ps o L I hps
    (fun o q _ => ⟨q.2, rfl⟩)
  refine ⟨o', L', ?_, I', hL'⟩
  show forIt (fun o (p : Py (κ × ν)) => do let (k, v) ← p; odSet K o k v) o
    (FIt.ofList (ps.map (Except.ok (ε := PyExc)))) = _
  simp only [forIt, FIt.ofList]
  rw [loopS_map]
  have : loopS (fun o (q : κ × ν) => (do let (k, v) ← (Except.ok q : Py (κ × ν)); odSet K o k v)) o ps =
      loopS (fun o (q : κ × ν) => odSet K o q.1 q.2) o ps := rfl
  rw [this, h]

/-- **Keyword order is preserved, and `|=`, `|`, reflected `|` merge in order.** For every key type
with hashable keys and non-raising sources: `OrderedDict(pairs, **kw)` has the pairs' keys in
first-seen order and then the new keyword keys in keyword order; `od |= pairs` is `update`, appending
the new keys in first-seen order; `od | other` (another `OrderedDict`) is a copy of `od` with `other`'s new
keys after; `other | od` (reflected) starts from `other`'s keys, then `od`'s new ones.

Source: docstring, Lib/collections/__init__.py:114-116 ('Keyword argument order is preserved'); :325-342;
PEP 584. -/
def ODInitMerge : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (K : KOps κ) (o p : OD κ ν) (L M : List (Nat × κ)) (ps kw : List (κ × ν)),
    ODInv o L → ODInv p M → (∀ q ∈ ps, K.hash q.1 = .ok ()) → (∀ q ∈ kw, K.hash q.1 = .ok ()) →
    (∀ k ∈ L.map (·.2), K.hash k = .ok ()) → (∀ k ∈ M.map (·.2), K.hash k = .ok ()) →
    (∃ o' L', odInit K (some (.pairs (.ok (FIt.ofList (ps.map .ok))))) kw = .ok o' ∧ ODInv o' L' ∧
      L'.map (·.2) = firstSeen (firstSeen [] (ps.map (·.1))) (kw.map (·.1))) ∧
    (∃ o' L', odIor K o (.pairs (.ok (FIt.ofList (ps.map .ok)))) = (o', none) ∧ ODInv o' L' ∧
      L'.map (·.2) = firstSeen (L.map (·.2)) (ps.map (·.1))) ∧
    (∃ r R, odOr K o (some (odSrc p)) = some (.ok r) ∧ ODInv r R ∧
      R.map (·.2) = firstSeen (L.map (·.2)) (M.map (·.2))) ∧
    (∃ r R, odRor K o (some (odSrc p)) = some (.ok r) ∧ ODInv r R ∧
      R.map (·.2) = firstSeen (M.map (·.2)) (L.map (·.2)))

theorem odInitMerge_proven : ODInitMerge := by
  intro κ ν _ K o p L M ps kw I J hps hkw hL hM
  refine ⟨?_, odUpdate_pairs_inv K o L ps I hps, ?_, ?_⟩
  · obtain ⟨o1, L1, h1, I1, hL1⟩ := odUpdate_pairs_inv K OD.new [] ps odInv_new hps
    obtain ⟨o2, L2, h2, I2, hL2⟩ := setLoop_inv K (fun o (q : κ × ν) => odSet K o q.1 q.2) (·.1) kw o1 L1 I1 hkw
      (fun o q _ => ⟨q.2, rfl⟩)
    refine ⟨o2, L2, ?_, I2, by rw [hL2, hL1]; rfl⟩
    simp only [odInit, h1, Out.andThen, h2, Out.toPy]
  · obtain ⟨n1, N1, h1, J1, hN1⟩ := odUpdate_src_inv K o OD.new L [] I odInv_new hL
    obtain ⟨n2, N2, h2, J2, hN2⟩ := odUpdate_src_inv K p n1 M N1 J J1 hM
    refine ⟨n2, N2, ?_, J2, ?_⟩
    · simp only [odOr, odCopy, h1, Out.toPy, ok_bind, Option.map_some, h2]
    · rw [hN2, hN1]; simp only [List.map_nil]; rw [firstSeen_nodup _ I.keys]
  · obtain ⟨n1, N1, h1, J1, hN1⟩ := odUpdate_src_inv K p OD.new M [] J odInv_new hM
    obtain ⟨n2, N2, h2, J2, hN2⟩ := odUpdate_src_inv K o n1 L N1 I J1 hL
    refine ⟨n2, N2, ?_, J2, ?_⟩
    · simp only [odRor, h1, Out.toPy, ok_bind, Option.map_some, h2]
    · rw [hN2, hN1]; simp only [List.map_nil]; rw [firstSeen_nodup _ J.keys]

end PyLean.CoreLibs.Coll
