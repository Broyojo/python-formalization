import PyLean.CoreLibs.Coll.ChainMap

/-!
Properties of `ChainMap`: the flat-dict view, writes that stay in `maps[0]`, the union
operators, `new_child`/`parents`. Hypotheses `∀ m ∈ maps, D.WF m` say each map is a dict.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PyLean.CoreLibs.Coll

open PyLean D

variable {κ ν : Type} [DecidableEq κ]

/-! ### Dict lemmas -/

theorem get?_update_WF {items : D κ ν} (h : WF items) (d : D κ ν) (x : κ) :
    get? (D.update d items) x = (get? items x).or (get? d x) := by
  induction items generalizing d with
  | nil => simp [D.update]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    have hn := notMem_of_cons h
    have : D.update d ((a, b) :: t) = D.update (set d a b) t := rfl
    rw [this, ih (WF_of_cons h), get?_set, get?_cons]
    by_cases hax : a = x
    · subst hax
      simp [get?_eq_none_iff.mpr hn]
    · simp [hax]

theorem mem_foldl_addK (l s : List κ) (x : κ) : x ∈ l.foldl addK s ↔ x ∈ s ∨ x ∈ l := by
  induction l generalizing s with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, ih, addK, List.mem_cons]
    split
    · next ha =>
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl h
        · subst h; exact Or.inl ha
        · exact Or.inr h
    · simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h

theorem nodup_addK {s : List κ} (h : s.Nodup) (x : κ) : (addK s x).Nodup := by
  unfold addK
  split
  · exact h
  · next hx =>
    rw [List.nodup_append]
    refine ⟨h, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    intro e; subst e; exact hx ha

theorem nodup_foldl_addK (l : List κ) {s : List κ} (h : s.Nodup) : (l.foldl addK s).Nodup := by
  induction l generalizing s with
  | nil => exact h
  | cons a t ih => exact ih (nodup_addK h a)

theorem foldl_addK_acc (l A s : List κ) :
    (l.foldl addK A).foldl addK s = l.foldl addK (A.foldl addK s) := by
  induction l generalizing A with
  | nil => rfl
  | cons x t ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    by_cases hx : x ∈ A
    · have hx' : x ∈ A.foldl addK s := (mem_foldl_addK A s x).mpr (Or.inr hx)
      simp [addK, hx, hx']
    · have : addK A x = A ++ [x] := by simp [addK, hx]
      rw [this, List.foldl_append]
      rfl

theorem foldl_addK_foldl (s l : List κ) : (l.foldl addK []).foldl addK s = l.foldl addK s :=
  foldl_addK_acc l [] s

theorem keys_update (d items : D κ ν) : keys (D.update d items) = (keys items).foldl addK (keys d) := by
  induction items generalizing d with
  | nil => rfl
  | cons p t ih =>
    have : D.update d (p :: t) = D.update (set d p.1 p.2) t := rfl
    rw [this, ih, keys_set]
    rfl

theorem update_update_nil {d : D κ ν} (hd : WF d) (L : D κ ν) :
    D.update d (D.update [] L) = D.update d L := by
  apply ext_keys (WF_update hd _) (WF_update hd _)
  · rw [keys_update, keys_update, keys_update, keys_nil, foldl_addK_foldl]
  · intro x
    rw [get?_update_WF (WF_update WF_nil L), get?_update, get?_update]
    simp

theorem update_append (d a b : D κ ν) : D.update d (a ++ b) = D.update (D.update d a) b := by
  simp [D.update, List.foldl_append]

theorem update_nil_WF {items : D κ ν} (h : WF items) : D.update [] items = items := by
  rw [update_fresh h (by simp)]; rfl

theorem update_assoc {d m : D κ ν} (hd : WF d) (hm : WF m) (o : D κ ν) :
    D.update d (D.update m o) = D.update (D.update d m) o := by
  have : D.update m o = D.update [] (m ++ o) := by rw [update_append, update_nil_WF hm]
  rw [this, update_update_nil hd, update_append]

theorem foldl_update (l : List (D κ ν)) (d : D κ ν) : l.foldl D.update d = D.update d l.flatten := by
  induction l generalizing d with
  | nil => rfl
  | cons a t ih => simp [ih, update_append]

theorem flat_eq (maps : List (D κ ν)) : flat maps = D.update [] maps.reverse.flatten := by
  induction maps with
  | nil => rfl
  | cons m t ih => simp [flat, ih, update_append, List.flatten_append]

theorem WF_flat (maps : List (D κ ν)) : WF (flat maps) := by
  rw [flat_eq]; exact WF_update WF_nil _

theorem get?_flat {maps : List (D κ ν)} (hw : ∀ m ∈ maps, WF m) (k : κ) :
    get? (flat maps) k = cmLookup maps k := by
  induction maps with
  | nil => rfl
  | cons m t ih =>
    have ih := ih (fun n hn => hw n (List.mem_cons_of_mem _ hn))
    simp only [flat, cmLookup]
    rw [get?_update_WF (hw m (by simp)), ih]
    cases get? m k <;> rfl

theorem keys_fromkeys {l : List κ} (h : l.Nodup) (v : ν) : keys (fromkeys l v) = l := by
  have gen : ∀ (l : List κ) (d : D κ ν), l.Nodup → (∀ x ∈ l, x ∉ keys d) →
      keys (l.foldl (fun d x => set d x v) d) = keys d ++ l := by
    intro l
    induction l with
    | nil => intro d _ _; simp
    | cons a t ih =>
      intro d hn hf
      simp only [List.nodup_cons] at hn
      simp only [List.foldl_cons]
      rw [ih _ hn.2]
      · rw [set_of_notMem _ (hf a (by simp))]; simp
      · intro x hx
        rw [set_of_notMem _ (hf a (by simp))]
        simp only [keys_append, keys_cons, keys_nil, List.mem_append, List.mem_singleton, not_or]
        refine ⟨hf x (by simp [hx]), ?_⟩
        intro e
        rw [e] at hx
        exact hn.1 hx
  simpa [fromkeys] using gen l [] h (by simp)

theorem iter_eq {maps : List (D κ ν)} (hw : ∀ m ∈ maps, WF m) :
    cmIter ⟨maps⟩ = keys (flat maps) := by
  unfold cmIter
  simp only
  induction maps with
  | nil => rfl
  | cons m t ih =>
    have ih := ih (fun n hn => hw n (List.mem_cons_of_mem _ hn))
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
      List.foldl_cons, List.foldl_nil, flat, or_]
    rw [keys_update, keys_update, ih, keys_fromkeys (hw m (by simp))]

theorem mem_flat_iff {maps : List (D κ ν)} (hw : ∀ m ∈ maps, WF m) (k : κ) :
    k ∈ keys (flat maps) ↔ ∃ m ∈ maps, k ∈ keys m := by
  induction maps with
  | nil => simp [flat]
  | cons m t ih =>
    have ih := ih (fun n hn => hw n (List.mem_cons_of_mem _ hn))
    simp only [flat]
    rw [keys_update, mem_foldl_addK, ih]
    constructor
    · rintro (⟨n, hn, h⟩ | h)
      · exact ⟨n, List.mem_cons_of_mem _ hn, h⟩
      · exact ⟨m, by simp, h⟩
    · rintro ⟨n, hn, h⟩
      rcases List.mem_cons.mp hn with e | e
      · subst e; exact Or.inr h
      · exact Or.inl ⟨n, e, h⟩

theorem mem_union_iff (maps : List (D κ ν)) (s : List κ) (k : κ) :
    k ∈ maps.foldl (fun s m => (keys m).foldl addK s) s ↔ k ∈ s ∨ ∃ m ∈ maps, k ∈ keys m := by
  induction maps generalizing s with
  | nil => simp
  | cons m t ih =>
    simp only [List.foldl_cons]
    rw [ih, mem_foldl_addK]
    constructor
    · rintro ((h | h) | ⟨n, hn, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨m, by simp, h⟩
      · exact Or.inr ⟨n, List.mem_cons_of_mem _ hn, h⟩
    · rintro (h | ⟨n, hn, h⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hn with e | e
        · subst e; exact Or.inl (Or.inr h)
        · exact Or.inr ⟨n, e, h⟩

theorem nodup_union (maps : List (D κ ν)) {s : List κ} (h : s.Nodup) :
    (maps.foldl (fun s m => (keys m).foldl addK s) s).Nodup := by
  induction maps generalizing s with
  | nil => exact h
  | cons m t ih => exact ih (nodup_foldl_addK _ h)

theorem len_eq {maps : List (D κ ν)} (hw : ∀ m ∈ maps, WF m) :
    cmLen ⟨maps⟩ = (keys (flat maps)).length := by
  unfold cmLen
  apply List.Perm.length_eq
  apply (List.perm_ext_iff_of_nodup (nodup_union maps List.nodup_nil) (WF_flat maps)).mpr
  intro k
  rw [mem_union_iff, mem_flat_iff hw]
  simp

theorem contains_iff {maps : List (D κ ν)} (k : κ) :
    cmContains ⟨maps⟩ k = true ↔ ∃ m ∈ maps, k ∈ keys m := by
  simp [cmContains, D.mem_iff]

/-- A `ChainMap` reads like the flat dict obtained by updating an empty dict from the
last map to the first. Doc/library/collections.rst: "Lookups search the underlying
mappings successively until a key is found", "Iterating over a ChainMap ... scanning
the mappings last to first", and `__len__`, `__contains__`, `__bool__` and `get` agree. -/
def ChainMapFlatView : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (rk : κ → String) (maps : List (D κ ν)) (k : κ) (miss : κ → Py ν)
    (default : Option ν), (∀ m ∈ maps, WF m) →
    cmIter ⟨maps⟩ = keys (flat maps) ∧
    cmLen ⟨maps⟩ = (keys (flat maps)).length ∧
    cmContains ⟨maps⟩ k = D.mem (flat maps) k ∧
    cmBool ⟨maps⟩ = !(flat maps).isEmpty ∧
    cmGetitem miss ⟨maps⟩ k =
      (match D.get? (flat maps) k with
       | some v => .ok v
       | none => miss k) ∧
    cmGet miss ⟨maps⟩ k default = .ok ((D.get? (flat maps) k).or default) ∧
    (D.get? (flat maps) k = none → cmGetitem (cmMissing rk) ⟨maps⟩ k = .error (.keyError (rk k)))

theorem chainMapFlatView_proven : ChainMapFlatView := by
  intro κ ν _ rk maps k miss default hw
  have hc : cmContains ⟨maps⟩ k = D.mem (flat maps) k := by
    apply Bool.eq_iff_iff.mpr
    rw [contains_iff, D.mem_iff, mem_flat_iff hw]
  have hg : cmGetitem miss ⟨maps⟩ k =
      (match D.get? (flat maps) k with
       | some v => .ok v
       | none => miss k) := by
    rw [cmGetitem, get?_flat hw]; rfl
  refine ⟨iter_eq hw, len_eq hw, hc, ?_, hg, ?_, ?_⟩
  · apply Bool.eq_iff_iff.mpr
    simp only [cmBool, List.any_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff]
    constructor
    · rintro ⟨m, hm, hne⟩
      obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil m (by simpa using hne)
      have : p.1 ∈ keys (flat maps) :=
        (mem_flat_iff hw p.1).mpr ⟨m, hm, mem_keys_of_mem hp⟩
      intro e
      rw [e] at this
      simp at this
    · intro hne
      obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hne
      obtain ⟨m, hm, hk⟩ := (mem_flat_iff hw p.1).mp (mem_keys_of_mem hp)
      refine ⟨m, hm, ?_⟩
      intro e
      simp [e] at hk
  · unfold cmGet
    rw [hc]
    cases hd : D.mem (flat maps) k with
    | true =>
      have hs : (D.get? (flat maps) k).isSome = true := hd
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
      simp [hg, hv, Except.map]
    | false =>
      have hs : (D.get? (flat maps) k).isSome = false := hd
      have : D.get? (flat maps) k = none := by simpa using hs
      simp [this]
  · intro h
    have hl : cmLookup maps k = none := by rw [← get?_flat hw]; exact h
    simp [cmGetitem, hl, cmMissing]

/-- Doc/library/collections.rst, ChainMap: "writes, updates, and deletions only operate
on the first mapping", with the `KeyError` of `__delitem__`/`pop` and `popitem` decided
by `maps[0]` alone, even if a later map holds the key. -/
def ChainMapWritesFirst : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (rk : κ → String) (m : D κ ν) (t : List (D κ ν)) (k x : κ) (v : ν)
    (default : Option ν), WF m →
    cmSetitem ⟨m :: t⟩ k v = .ok ⟨D.set m k v :: t⟩ ∧
    cmLookup (D.set m k v :: t) k = some v ∧
    (x ≠ k → cmLookup (D.set m k v :: t) x = cmLookup (m :: t) x) ∧
    (D.get? m k = none → cmDelitem rk ⟨m :: t⟩ k = .error (notInFirst rk k)) ∧
    (D.get? m k = some v →
      cmDelitem rk ⟨m :: t⟩ k = .ok ⟨D.del m k :: t⟩ ∧
      cmPop rk ⟨m :: t⟩ k default = .ok (v, ⟨D.del m k :: t⟩) ∧
      cmLookup (D.del m k :: t) k = cmLookup t k) ∧
    (D.get? m k = none → cmPop rk ⟨m :: t⟩ k none = .error (notInFirst rk k)) ∧
    (D.get? m k = none → cmPop rk ⟨m :: t⟩ k (some v) = .ok (v, ⟨m :: t⟩)) ∧
    (m = [] → cmPopitem (⟨m :: t⟩ : CMap κ ν) = .error (keyErrorStr "No keys found in the first mapping.")) ∧
    (∀ p, m.getLast? = some p → cmPopitem (⟨m :: t⟩ : CMap κ ν) = .ok (p, ⟨m.dropLast :: t⟩)) ∧
    cmClear (⟨m :: t⟩ : CMap κ ν) = .ok ⟨[] :: t⟩

theorem cmLookup_cons_none {m : D κ ν} {t : List (D κ ν)} {k : κ} (h : D.get? m k = none) :
    cmLookup (m :: t) k = cmLookup t k := by
  simp [cmLookup, h]

theorem chainMapWritesFirst_proven : ChainMapWritesFirst := by
  intro κ ν _ rk m t k x v default hw
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · simp [cmLookup, get?_set]
  · intro hx
    have : ¬ k = x := fun e => hx e.symm
    simp [cmLookup, get?_set, this]
  · intro h
    simp [cmDelitem, D.mem, h]
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simp [cmDelitem, D.mem, h]
    · simp [cmPop, h]
    · apply cmLookup_cons_none
      rw [get?_del hw]
      simp
  · intro h
    simp [cmPop, h]
  · intro h
    simp [cmPop, h]
  · intro h
    subst h
    simp [cmPopitem, D.popitem?]
  · intro p hp
    simp [cmPopitem, D.popitem?, hp]

/-! ### Union operators -/

/-- `|`, `|=` against a flat dict: `cm | other` reads like `dict(cm) | other`,
`other | cm` is `other | dict(cm)`, and `|=` writes to `maps[0]`. Items and order
are preserved. `copy()` reads the same as the original. (PEP 584) -/
def ChainMapUnionFlat : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (m : D κ ν) (t : List (D κ ν)) (o : D κ ν),
    WF m → WF o →
    (∃ r, cmOr ⟨m :: t⟩ (some o) = some (.ok r) ∧ flat r.maps = D.or_ (flat (m :: t)) o ∧
      r.maps.tail = t) ∧
    (∃ r, cmIor ⟨m :: t⟩ o = .ok r ∧ flat r.maps = D.or_ (flat (m :: t)) o) ∧
    (∃ r, cmRor ⟨m :: t⟩ (some o) = some r ∧ r.maps = [D.or_ o (flat (m :: t))]) ∧
    (∃ r, cmCopy ⟨m :: t⟩ = .ok r ∧ flat r.maps = flat (m :: t)) ∧
    cmOr (⟨m :: t⟩ : CMap κ ν) none = none ∧ cmRor (⟨m :: t⟩ : CMap κ ν) none = none

theorem chainMapUnionFlat_proven : ChainMapUnionFlat := by
  intro κ ν _ m t o hm ho
  have hflat : flat (D.update m o :: t) = D.or_ (flat (m :: t)) o := by
    simp only [flat, or_]
    exact update_assoc (WF_flat t) hm o
  refine ⟨⟨⟨D.update m o :: t⟩, ?_, hflat, rfl⟩, ⟨⟨D.update m o :: t⟩, rfl, hflat⟩, ?_, ?_, rfl, rfl⟩
  · simp [cmOr, cmCopy, cmNew, cmIor, bind, Except.bind]
  · refine ⟨cmNew [D.or_ o (flat (m :: t))], ?_, rfl⟩
    simp only [cmRor, Option.map_some, Option.some.injEq]
    congr 2
    rw [foldl_update, update_nil_WF ho, or_, flat_eq, update_update_nil ho]
  · exact ⟨cmNew (m :: t), rfl, rfl⟩

/-! ### Construction, `new_child`, `parents`, `fromkeys` -/

/-- `__init__` establishes "always at least one map" (:1017), and `new_child` and
`parents` are inverse on the map list: `new_child(m)` puts `m` (updated from the
keywords, or the keywords alone when `m` is `None`) in front and `.parents` takes
it off again, an empty `maps` coming back as the `[{}]` of `__init__`.
`fromkeys` is a one-map `ChainMap` reading like `dict.fromkeys`. -/
def ChainMapChildParents : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (c : CMap κ ν) (l : List (D κ ν)) (m kw : D κ ν) (it : List κ)
    (v : ν),
    (cmNew l).maps ≠ [] ∧ (l ≠ [] → (cmNew l).maps = l) ∧
    (cmNewChild c none kw).maps = kw :: c.maps ∧
    (cmNewChild c (some m) kw).maps = D.update m kw :: c.maps ∧
    (cmParents (cmNewChild c (some m) kw)).maps = (cmNew c.maps).maps ∧
    flat (cmFromkeys it v).maps = D.fromkeys it v

theorem chainMapChildParents_proven : ChainMapChildParents := by
  intro κ ν _ c l m kw it v
  refine ⟨?_, ?_, rfl, ?_, ?_, ?_⟩
  · cases l <;> simp [cmNew]
  · intro h
    cases l with
    | nil => exact absurd rfl h
    | cons a t => rfl
  · simp only [cmNewChild, cmNew]
    cases kw <;> simp [D.update]
  · cases c with
    | mk maps => simp only [cmParents, cmNewChild, cmNew, List.tail_cons]
  · simp only [cmFromkeys, cmNew, flat]
    have hw : WF (D.fromkeys it v) := by
      unfold D.fromkeys
      have : ∀ (l : List κ) (d : D κ ν), WF d → WF (l.foldl (fun d x => set d x v) d) := by
        intro l
        induction l with
        | nil => intro d h; exact h
        | cons a t ih => intro d h; exact ih _ (WF_set h a v)
      exact this it [] WF_nil
    exact update_nil_WF hw

/-- `repr` of a `ChainMap` shows the maps in order, so pushing a child prepends its repr;
`ChainMap()` prints its single empty dict. -/
def ChainMapRepr : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (cls : String) (rk : κ → String) (rv : ν → String)
    (m h : D κ ν) (t : List (D κ ν)),
    cmRepr cls rk rv (cmNewChild ⟨h :: t⟩ (some m) []) =
      cls ++ "(" ++ reprD rk rv m ++ ", " ++ ", ".intercalate ((h :: t).map (reprD rk rv)) ++ ")" ∧
    cmRepr cls rk rv (cmNew ([] : List (D κ ν))) = cls ++ "(" ++ reprD rk rv ([] : D κ ν) ++ ")"

theorem chainMapRepr_proven : ChainMapRepr := by
  intro κ ν _ cls rk rv m h t
  constructor
  · have hu : (cmNewChild ⟨h :: t⟩ (some m) [] : CMap κ ν).maps = m :: h :: t := by
      simp [cmNewChild, cmNew]
    simp only [cmRepr, hu, List.map_cons]
    simp [String.intercalate_cons_cons, String.append_assoc]
  · rfl

end PyLean.CoreLibs.Coll
