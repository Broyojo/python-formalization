import PyLean.CoreLibs.Coll.ODictMore2

/-!
`OrderedDict.copy` as a new object, `__reduce__` with `__getstate__`, and `__repr__` under
`reprlib.recursive_repr`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PyLean.CoreLibs.Coll

open PyLean

variable {κ ν : Type} [DecidableEq κ]

/-- `od[k] = v` with a hashable `k` sets the dict entry. -/
theorem odSet_d (K : KOps κ) (o : OD κ ν) (k : κ) (v : ν) (hk : K.hash k = .ok ()) :
    ∃ o', odSet K o k v = .ok o' ∧ o'.d = D.set o.d k v := by
  cases hm : D.mem o.d k
  · exact ⟨{ addLink o ((o.heap 0).prev.getD 0) k with d := D.set o.d k v }, by
      simp only [odSet, dMem_ok o.d hk, hm, ok_bind, Bool.not_false, if_true, dSet_ok o.map _ hk, OD.link,
        pure_py, OD.setPrev, OD.setNext, setLink_d, dSet_ok o.d v hk]
      rfl, rfl⟩
  · exact ⟨{ o with d := D.set o.d k v }, by simp [odSet, dMem_ok o.d hk, hm, dSet_ok o.d v hk], rfl⟩

/-- A loop of `od[key x] = v` steps whose value for each key is `W key`: afterwards the dict holds
`W k` for every key the loop set, and the old value elsewhere. -/
theorem setLoop_vals (K : KOps κ) {α : Type} (f : OD κ ν → α → Py (OD κ ν)) (key : α → κ) (W : κ → Option ν) :
    ∀ (xs : List α) (o o' : OD κ ν), (∀ x ∈ xs, K.hash (key x) = .ok ()) →
      (∀ o, ∀ x ∈ xs, ∃ v, f o x = odSet K o (key x) v ∧ W (key x) = some v) →
      loopS f o xs = (o', none) →
      ∀ k, D.get? o'.d k = if k ∈ xs.map key then W k else D.get? o.d k
  | [], o, o', _, _, h, k => by
    simp only [loopS, Prod.mk.injEq] at h
    rw [← h.1]; simp
  | x :: xs, o, o', hh, hf, h, k => by
    obtain ⟨v, hfx, hW⟩ := hf o x (by simp)
    obtain ⟨o1, h1, hd⟩ := odSet_d K o (key x) v (hh x (by simp))
    simp only [loopS, hfx, h1] at h
    have ih := setLoop_vals K f key W xs o1 o' (fun y hy => hh y (by simp [hy]))
      (fun o y hy => hf o y (by simp [hy])) h k
    rw [ih, hd, D.get?_set]
    by_cases hx : key x = k
    · subst hx; simp [hW]
    · by_cases hk : k ∈ xs.map key <;> simp [hx, hk, Ne.symm hx]

/-- **`copy` is a new object of the same class with the same items, in the same order.** For every
key type, every instance `self` of class `cls` with hashable keys and every unused id `fresh` (the
allocator's): `self.copy()` is the object `fresh` (so `copy is not self`), of class `cls`, whose links
list the keys of `self` in order and whose value for each key is `self`'s value (the same object:
a shallow copy); `self` and every other object are left as they were.

Source: Lib/collections/__init__.py:304-306 (`self.__class__(self)`), :104-117; docstring 'a shallow
copy of od'. -/
def ODCopyObj : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (K : KOps κ) (objs : ODHeap κ ν) (self fresh : Nat) (cls : String)
    (o : OD κ ν) (L : List (Nat × κ)), objs self = some (cls, o) → objs fresh = none → ODInv o L →
    (∀ k ∈ L.map (·.2), K.hash k = .ok ()) →
    ∃ n N objs', odCopyH K objs fresh self = .ok (fresh, objs') ∧ fresh ≠ self ∧
      objs' self = some (cls, o) ∧ objs' fresh = some (cls, n) ∧ (∀ j, j ≠ fresh → objs' j = objs j) ∧
      ODInv n N ∧ N.map (·.2) = L.map (·.2) ∧ ∀ k, D.get? n.d k = D.get? o.d k

theorem odCopyObj_proven : ODCopyObj := by
  intro κ ν _ K objs self fresh cls o L hs hf I hL
  have hne : fresh ≠ self := fun h => by rw [h, hs] at hf; cases hf
  let g : κ → Py ν := fun k => match D.get? o.d k with
    | some w => .ok w
    | none => .error (.keyError "~key")
  have hstep : ∀ (n' : OD κ ν), ∀ k ∈ L.map (·.2), ∃ v,
      (fun n' k => do let w ← g k; odSet K n' k w) n' k = odSet K n' (id k) v ∧ D.get? o.d (id k) = some v := by
    intro n' k hk
    obtain ⟨w, hw⟩ := get?_some_of_inv I hk
    exact ⟨w, by simp [g, hw], hw⟩
  obtain ⟨n, N, h, J, hN⟩ := setLoop_inv K (fun n' k => do let w ← g k; odSet K n' k w) id (L.map (·.2))
    OD.new [] odInv_new hL (fun n' k hk => (hstep n' k hk).imp fun _ h => h.1)
  have hv := setLoop_vals K (fun n' k => do let w ← g k; odSet K n' k w) id (D.get? o.d) (L.map (·.2))
    OD.new n hL hstep h
  have hcopy : odCopy K o = .ok n := by
    show (forIt (fun n' k => do let w ← g k; odSet K n' k w) OD.new (FIt.ofList o.keysList)).toPy = _
    rw [keysList_inv I]
    simp only [forIt, FIt.ofList, h, Out.toPy]
  refine ⟨n, N, fun j => if j = fresh then some (cls, n) else objs j, ?_, hne, ?_, ?_, ?_, J, ?_, ?_⟩
  · simp only [odCopyH, hs, hcopy, ok_bind, pure_py]
  · simp [Ne.symm hne, hs]
  · simp
  · intro j hj; simp [hj]
  · rw [hN]; simp only [List.map_nil, List.map_id]; exact firstSeen_nodup _ I.keys
  · intro k
    rw [hv k]
    by_cases hk : k ∈ L.map (·.2)
    · simp [hk]
    · rw [if_neg (by simpa using hk), get?_none_of_inv I hk]; rfl

/-- The items of `od` in link order: the keys of `L`, each with its value. -/
theorem filterMap_items (d : D κ ν) : ∀ (ks : List κ), (∀ k ∈ ks, ∃ v, D.get? d k = some v) →
    (ks.filterMap (fun k => (D.get? d k).map (k, ·))).map (·.1) = ks ∧
    ∀ q ∈ ks.filterMap (fun k => (D.get? d k).map (k, ·)), D.get? d q.1 = some q.2
  | [], _ => by simp
  | k :: ks, h => by
    obtain ⟨v, hv⟩ := h k (by simp)
    obtain ⟨ih1, ih2⟩ := filterMap_items d ks (fun k' hk' => h k' (by simp [hk']))
    simp only [List.filterMap_cons, hv, Option.map_some]
    refine ⟨by simp [ih1], ?_⟩
    intro q hq
    simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact hv
    · exact ih2 q hq

/-- **`__reduce__`: the state without the private attributes, and the items in order.** For every
instance with list `L`, the three private attributes `priv` (`vars(OrderedDict())`), user attributes
`attrs` and slot values `slots` (none of them private names), there is one item list `its`, the keys of
`L` in order each with its value, such that `od.__reduce__()` is `(cls, (), state, None, its)` where:
with the default `__getstate__` (`__dict__`, no slots) `state` is `attrs`, or `None` when there are
none; with slots, `(attrs, slots)` (even with `attrs` empty), or as before when `slots` is empty; an
override returning `None` or `{}` passes it as it is; one returning `(None, slots)` raises
`AttributeError` from `None.copy()`; one that raises propagates.

Source: Lib/collections/__init__.py:285-302; Objects/typeobject.c `object_getstate_default`. -/
def ODReduce : Prop :=
  ∀ (κ ν α : Type) [DecidableEq κ] (cls : String) (o : OD κ ν) (L : List (Nat × κ))
    (priv attrs slots : List (String × α)) (e : PyExc), ODInv o L → priv.map (·.1) = odPriv →
    (∀ p ∈ attrs ++ slots, p.1 ∉ odPriv) →
    ∃ its : List (κ × ν), its.map (·.1) = L.map (·.2) ∧ (∀ q ∈ its, D.get? o.d q.1 = some q.2) ∧
      odReduceG cls (.ok (.dict (priv ++ attrs))) o =
        .ok (cls, [], (if attrs.isEmpty then .none else .dict attrs), none, its) ∧
      odReduceG cls (.ok (.pair (some (priv ++ attrs)) slots)) o =
        .ok (cls, [], (if slots.isEmpty then (if attrs.isEmpty then .none else .dict attrs)
          else .pair attrs slots), none, its) ∧
      odReduceG cls (.ok (GState.none (α := α))) o = .ok (cls, [], .none, none, its) ∧
      odReduceG cls (.ok (GState.dict (α := α) [])) o = .ok (cls, [], .dict [], none, its) ∧
      odReduceG cls (.ok (.pair none slots)) o =
        .error (.named "AttributeError" "'NoneType' object has no attribute 'copy'") ∧
      odReduceG (α := α) cls (.error e) o = .error e

theorem odReduce_proven : ODReduce := by
  intro κ ν α _ cls o L priv attrs slots e I hp ha
  obtain ⟨p, ps, rfl⟩ : ∃ p ps, priv = p :: ps := by
    cases priv with
    | nil => simp [odPriv] at hp
    | cons p ps => exact ⟨p, ps, rfl⟩
  have hdp : (p :: ps).filter (fun p => !decide (p.1 ∈ odPriv)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro q hq
    have : q.1 ∈ odPriv := hp ▸ List.mem_map_of_mem hq
    simp [this]
  have hda : attrs.filter (fun p => !decide (p.1 ∈ odPriv)) = attrs :=
    List.filter_eq_self.2 (fun q hq => by simp [ha q (by simp [hq])])
  have hds : slots.filter (fun p => !decide (p.1 ∈ odPriv)) = slots :=
    List.filter_eq_self.2 (fun q hq => by simp [ha q (by simp [hq])])
  have hdrop : (p :: (ps ++ attrs)).filter (fun p => !decide (p.1 ∈ odPriv)) = attrs := by
    rw [← List.cons_append, List.filter_append, hdp, hda]; rfl
  have hval : ∀ k ∈ o.keysList, ∃ v, D.get? o.d k = some v := by
    rw [keysList_inv I]; exact fun k hk => get?_some_of_inv I hk
  obtain ⟨h1, h2⟩ := filterMap_items o.d o.keysList hval
  refine ⟨o.keysList.filterMap (fun k => (D.get? o.d k).map (k, ·)), by rw [h1, keysList_inv I], h2,
    ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp only [odReduceG, ok_bind, List.cons_append, hdrop]; rfl
  · simp only [odReduceG, ok_bind, List.cons_append, hdrop, hds]; rfl

theorem mapM_cons_map {α β γ : Type} (F : β → Py γ) (g : α → β) (q : α) (t : List α) :
    List.mapM F (g q :: t.map g) = List.mapM (fun x => F (g x)) (q :: t) := by
  rw [← List.map_cons, List.mapM_map]; rfl

/-- **`__repr__` under `recursive_repr`.** For every key and value type, `repr` functions `rk`, `rv`
(free to raise) and objects `heap`: an instance whose `repr` is running gives `...`; an empty one
`Cls()`; one that holds itself as the value of `k` gives `Cls({k: ...})`; one that holds the same
other instance twice repeats it in full (the running mark is dropped when the inner `repr` returns);
with plain values it is `Cls(%r)` of its items in link order (`odRepr`); a raising key or value
`repr` propagates.

Source: Lib/collections/__init__.py:278-283; Lib/reprlib.py:9-24. -/
def ODReprRec : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (rk : κ → Py String) (rv : ν → Py String)
    (heap : Nat → Option (String × List (κ × ODRef ν))) (fuel : Nat) (running : List Nat) (i j : Nat)
    (cls cls' : String) (k k' : κ) (sk sk' : String) (v : ν) (e : PyExc) (o : OD κ ν) (L : List (Nat × κ)),
    i ∉ running →
    odReprR rk rv heap (fuel + 1) (i :: running) i = .ok "..." ∧
    (heap i = some (cls, []) → odReprR rk rv heap (fuel + 1) running i = .ok (cls ++ "()")) ∧
    (heap i = some (cls, [(k, .od i)]) → rk k = .ok sk →
      odReprR rk rv heap (fuel + 2) running i =
        .ok (cls ++ "(" ++ ("{" ++ ", ".intercalate [sk ++ ": " ++ "..."] ++ "}") ++ ")")) ∧
    (heap i = some (cls, [(k, .od j), (k', .od j)]) → heap j = some (cls', []) → j ≠ i → j ∉ running →
      rk k = .ok sk → rk k' = .ok sk' →
      odReprR rk rv heap (fuel + 2) running i =
        .ok (cls ++ "(" ++ ("{" ++ ", ".intercalate [sk ++ ": " ++ (cls' ++ "()"), sk' ++ ": " ++ (cls' ++ "()")]
          ++ "}") ++ ")")) ∧
    (ODInv o L → L ≠ [] →
      heap i = some (cls, (o.keysList.filterMap (fun k => (D.get? o.d k).map (k, ·))).map
        (fun q => (q.1, ODRef.plain q.2))) →
      odReprR rk rv heap (fuel + 1) running i = odRepr rk rv cls o) ∧
    (heap i = some (cls, [(k, .plain v)]) → rk k = .error e → odReprR rk rv heap (fuel + 1) running i = .error e) ∧
    (heap i = some (cls, [(k, .plain v)]) → rk k = .ok sk → rv v = .error e →
      odReprR rk rv heap (fuel + 1) running i = .error e)

theorem odReprRec_proven : ODReprRec := by
  intro κ ν _ rk rv heap fuel running i j cls cls' k k' sk sk' v e o L hi
  refine ⟨by simp [odReprR], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [odReprR, hi, h]
  · intro h hk
    simp [odReprR, hi, h, hk]
  · intro h hj hji hjr hk hk'
    have hjr' : j ∉ i :: running := by simp [hji, hjr]
    simp [odReprR, hi, h, hj, hk, hk', hji, hjr]
  · intro I hL h
    have hval : ∀ k ∈ o.keysList, ∃ v, D.get? o.d k = some v := by
      rw [keysList_inv I]; exact fun k hk => get?_some_of_inv I hk
    obtain ⟨h1, _⟩ := filterMap_items o.d o.keysList hval
    obtain ⟨q, t, hqt⟩ : ∃ q t, o.keysList.filterMap (fun k => (D.get? o.d k).map (k, ·)) = q :: t := by
      cases hc : o.keysList.filterMap (fun k => (D.get? o.d k).map (k, ·)) with
      | nil =>
        rw [hc, keysList_inv I] at h1
        exact absurd (List.map_eq_nil_iff.1 h1.symm) hL
      | cons q t => exact ⟨q, t, rfl⟩
    have hne : o.d.isEmpty = false := by
      obtain ⟨⟨a, b⟩, M, hLM⟩ : ∃ a M, L = a :: M := by
        cases L with
        | nil => exact absurd rfl hL
        | cons a M => exact ⟨a, M, rfl⟩
      have hm := I.mem b
      rw [hLM] at hm
      cases hd : o.d with
      | nil => rw [hd] at hm; simp [D.mem] at hm
      | cons _ _ => rfl
    rw [hqt] at h
    simp only [odReprR, hi, if_false, h, List.map_cons]
    rw [mapM_cons_map _ (fun (q : κ × ν) => (q.fst, ODRef.plain q.snd))]
    simp only [odRepr, hne, hqt, reprDict, Bool.false_eq_true, if_false, bind_assoc, pure_bind]
  · intro h hk; simp [odReprR, hi, h, hk]
  · intro h hk hv; simp [odReprR, hi, h, hk, hv]

end PyLean.CoreLibs.Coll
