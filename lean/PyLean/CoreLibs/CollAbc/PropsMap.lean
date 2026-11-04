import PyLean.CoreLibs.CollAbc.PropsSeq

/-!
`Mapping`, the views and `MutableMapping` against `dict`, over abstract key and value types.
A `dict` is its item list in insertion order, with distinct keys as the type invariant.
-/

namespace PyLean.CoreLibs.CollAbc

open PyLean

section
variable {K V : Type} [DecidableEq K]

theorem lookup_of_mem : ∀ (d : List (K × V)) (k : K) (v : V), (d.map Prod.fst).Nodup →
    (k, v) ∈ d → d.lookup k = some v
  | [], _, _, _, h => by cases h
  | (a, b) :: rest, k, v, hn, h => by
    have hn' := List.nodup_cons.mp hn
    rcases List.mem_cons.mp h with e | e
    · cases e; simp [List.lookup]
    · have hka : k ≠ a := by
        rintro rfl
        exact hn'.1 (List.mem_map.mpr ⟨(k, v), e, rfl⟩)
      have : (k == a) = false := by simpa using hka
      simp only [List.lookup, this]
      exact lookup_of_mem rest k v hn'.2 e

theorem itemsOf_dict (d : List (K × V)) (hn : (d.map Prod.fst).Nodup) :
    ∀ suf : List (K × V), (∀ p ∈ suf, p ∈ d) →
    (dictMap d).itemsOf (suf.map Prod.fst) = .ok suf
  | [], _ => by simp [MapV.itemsOf, raiseTail, dictMap]
  | (a, b) :: rest, h => by
    have hg : (dictMap d).getitem a = .ok b := by
      simp [dictMap, dictGet, lookup_of_mem d a b hn (h _ (by simp))]
    have ih := itemsOf_dict d hn rest (fun p hp => h p (by simp [hp]))
    simp only [List.map_cons, MapV.itemsOf, hg, ih, bind, Except.bind, pure, Except.pure]

theorem dict_items (d : List (K × V)) (hn : (d.map Prod.fst).Nodup) :
    (dictMap d).items = .ok d := by
  simp only [MapV.items, dictMap, bind, Except.bind]
  exact itemsOf_dict d hn d (fun _ h => h)

theorem contains_values (E : EqOps V) (d : List (K × V)) (hn : (d.map Prod.fst).Nodup)
    (value : V) : ∀ suf : List (K × V), (∀ p ∈ suf, p ∈ d) →
    (dictMap d).valuesLoop E value (suf.map Prod.fst) =
      listContains E value (suf.map Prod.snd)
  | [], _ => by simp [MapV.valuesLoop, listContains, raiseTail, dictMap]
  | (a, b) :: rest, h => by
    have hg : (dictMap d).getitem a = .ok b := by
      simp [dictMap, dictGet, lookup_of_mem d a b hn (h _ (by simp))]
    have ih := contains_values E d hn value rest (fun p hp => h p (by simp [hp]))
    simp only [List.map_cons, MapV.valuesLoop, hg, listContains, bind, Except.bind, ih]

theorem valuesOf_dict (d : List (K × V)) (hn : (d.map Prod.fst).Nodup) :
    ∀ suf : List (K × V), (∀ p ∈ suf, p ∈ d) →
    (dictMap d).valuesOf (suf.map Prod.fst) = .ok (suf.map Prod.snd)
  | [], _ => by simp [MapV.valuesOf, raiseTail, dictMap]
  | (a, b) :: rest, h => by
    have hg : (dictMap d).getitem a = .ok b := by
      simp [dictMap, dictGet, lookup_of_mem d a b hn (h _ (by simp))]
    have ih := valuesOf_dict d hn rest (fun p hp => h p (by simp [hp]))
    simp only [List.map_cons, MapV.valuesOf, hg, ih, bind, Except.bind, pure, Except.pure]

theorem lookup_isSome_any : ∀ (d : List (K × V)) (k : K),
    (d.lookup k).isSome = d.any (fun p => decide (p.1 = k))
  | [], _ => rfl
  | (a, b) :: rest, k => by
    by_cases h : k = a
    · subst h; simp [List.lookup]
    · have h1 : (k == a) = false := by simpa using h
      have h2 : a ≠ k := fun e => h e.symm
      simp [List.lookup, h1, h2, lookup_isSome_any rest k]

end

/-- `Mapping.get`, `__contains__`, and the view methods `KeysView.__contains__`, `ItemsView.__iter__`,
`ValuesView.__iter__`, `ValuesView.__contains__` and `MappingView.__repr__` agree with `dict` and its views, on `dict`
primitives. Type invariant: keys are distinct. `Mapping` docs. -/
def MappingMatchesDict : Prop :=
  ∀ (K V : Type) [DecidableEq K] (d : List (K × V)) (k : K) (default value : V) (E : EqOps V)
    (cls r : String),
    (d.map Prod.fst).Nodup →
    let m := dictMap d
    m.get k default = .ok ((d.lookup k).getD default) ∧
    m.contains k = .ok (d.lookup k).isSome ∧
    m.keyIn k = .ok (d.lookup k).isSome ∧
    m.items = .ok d ∧
    m.values = .ok (d.map Prod.snd) ∧
    m.valuesContain E value = listContains E value (d.map Prod.snd) ∧
    viewRepr cls r = cls ++ "(" ++ r ++ ")"

theorem mappingMatchesDict_proven : MappingMatchesDict := by
  intro K V _ d k default value E cls r hn m
  have hi := dict_items d hn
  refine ⟨?_, ?_, ?_, hi, ?_, ?_, ?_⟩
  · cases h : d.lookup k <;> simp [m, MapV.get, dictMap, dictGet, h, isKeyError]
  · cases h : d.lookup k <;> simp [m, MapV.contains, dictMap, dictGet, h, isKeyError]
  · cases h : d.lookup k <;>
      simp [m, MapV.keyIn, MapV.contains, dictMap, dictGet, h, isKeyError]
  · simp only [m, MapV.values, dictMap, bind, Except.bind]
    exact valuesOf_dict d hn d (fun _ h => h)
  · simp only [m, MapV.valuesContain, dictMap, bind, Except.bind]
    exact contains_values E d hn value d (fun _ h => h)
  · simp [viewRepr, String.append_assoc]
    rfl

/-- `ItemsView.__contains__` agrees with `dict_items.__contains__` on 2-tuples, with the same
identity-then-`==` comparison. Narrowed twin property, over any mapping primitives. -/
def ItemsContainMatchesOnTuples : Prop :=
  ∀ (K V : Type) (m : MapV K V) (E : EqOps V) (k : K) (v : V),
    m.itemsContain E (.two k v none) = dictItemsContain m E true (.two k v none)

theorem itemsContainMatchesOnTuples_proven : ItemsContainMatchesOnTuples := by
  intro K V m E k v
  simp [MapV.itemsContain, dictItemsContain, unpack2, bind, Except.bind]

/-- `x in mapping.items()` agrees with `x in dict.items()` for every `x`. False: `dict_items`
answers `False` for a non-tuple or a tuple of the wrong length, while `ItemsView.__contains__` runs
`key, value = item` outside its `try`, so a non-iterable raises `TypeError`, a wrong-length
iterable raises `ValueError`, and a 2-element list can be `True`. This propagates to every `Set`
mixin that calls `__contains__`. -/
def ItemsContainMatchesDictItems : Prop :=
  ∀ (K V : Type) (m : MapV K V) (E : EqOps V) (isTuple : Bool) (x : ItemArg K V),
    m.itemsContain E x = dictItemsContain m E isTuple x

theorem itemsContainMatchesDictItems_refuted : ¬ItemsContainMatchesDictItems := by
  intro h
  have := h Nat Nat { getitem := fun _ => .ok 0, iter := .ok [], len := .ok 0 } ⟨fun _ _ => true, fun _ _ => .ok true⟩
    false (.notIterable "int")
  simp [MapV.itemsContain, dictItemsContain, unpack2, bind, Except.bind] at this

theorem dictSet_fresh {K V : Type} [DecidableEq K] (acc : List (K × V)) (k : K) (v : V)
    (h : k ∉ acc.map Prod.fst) : dictSet acc k v = acc ++ [(k, v)] := by
  have : acc.any (fun p => decide (p.1 = k)) = false := by
    simp only [List.any_eq_false, decide_eq_true_eq]
    intro p hp e
    exact h (List.mem_map.mpr ⟨p, hp, e⟩)
  simp [dictSet, this]

theorem dictOfItems_dict {K V : Type} [DecidableEq K] (hk : K → Py Unit) (hok : ∀ k, hk k = .ok ())
    (d : List (K × V)) (hn : (d.map Prod.fst).Nodup) :
    ∀ (suf acc : List (K × V)), (∀ p ∈ suf, p ∈ d) → ((acc ++ suf).map Prod.fst).Nodup →
    dictOfItems hk (dictMap d) acc (suf.map Prod.fst) = .ok (acc ++ suf)
  | [], acc, _, _ => by simp [dictOfItems, raiseTail, dictMap]
  | (a, b) :: rest, acc, h, hu => by
    have hg : (dictMap d).getitem a = .ok b := by
      simp [dictMap, dictGet, lookup_of_mem d a b hn (h _ (by simp))]
    have hfresh : a ∉ acc.map Prod.fst := by
      intro ha
      simp only [List.map_append, List.map_cons] at hu
      exact (List.nodup_append.mp hu).2.2 a ha a (by simp) rfl
    have ih := dictOfItems_dict hk hok d hn rest (acc ++ [(a, b)]) (fun p hp => h p (by simp [hp]))
      (by simpa using hu)
    simp only [List.map_cons, dictOfItems, hg, hok, dictSet_fresh acc a b hfresh, bind, Except.bind]
    simpa using ih

/-- `Mapping.__eq__` on two `dict`-backed mappings whose keys hash without error is the `dict` comparison of their
item lists, whatever that comparison is; anything that is not a `Mapping` gives `NotImplemented`.
Type invariant: keys are distinct. -/
def MappingEqIsDictEq : Prop :=
  ∀ (K V : Type) [DecidableEq K] (hashKey : K → Py Unit) (dictEq : List (K × V) → List (K × V) → Py Bool)
    (a b : List (K × V)), (∀ k, hashKey k = .ok ()) → (a.map Prod.fst).Nodup → (b.map Prod.fst).Nodup →
    mappingEq hashKey dictEq (dictMap a) (some (dictMap b)) = (Ret.val <$> dictEq a b) ∧
    mappingEq hashKey dictEq (dictMap a) none = .ok .notImplemented

theorem mappingEqIsDictEq_proven : MappingEqIsDictEq := by
  intro K V _ hashKey dictEq a b hk ha hb
  refine ⟨?_, rfl⟩
  have h1 := dictOfItems_dict hashKey hk a ha a [] (fun _ h => h) (by simpa using ha)
  have h2 := dictOfItems_dict hashKey hk b hb b [] (fun _ h => h) (by simpa using hb)
  simp only [List.nil_append] at h1 h2
  have i1 : (dictMap a).iter = .ok (a.map Prod.fst) := rfl
  have i2 : (dictMap b).iter = .ok (b.map Prod.fst) := rfl
  simp only [mappingEq, i1, i2, h1, h2, bind, Except.bind, pure, Except.pure]
  cases dictEq a b <;> rfl

/-! ### MutableMapping -/

section
variable {K V : Type} [DecidableEq K]

theorem dict_del_some (d : List (K × V)) (k : K) (v : V) (h : d.lookup k = some v) :
    dictDel d k = .ok (d.filter (fun p => p.1 ≠ k)) := by
  have h1 := lookup_isSome_any d k
  rw [h] at h1
  have h2 : d.any (fun p => decide (p.1 = k)) = true := by simpa using h1.symm
  simp [dictDel, h2]

theorem filter_ne_of_nodup : ∀ (rest : List (K × V)) (k : K), k ∉ rest.map Prod.fst →
    rest.filter (fun p => p.1 ≠ k) = rest
  | [], _, _ => rfl
  | (a, b) :: rest, k, h => by
    have h' : ¬ (k = a ∨ k ∈ rest.map Prod.fst) := by simpa using h
    have hne : a ≠ k := fun e => h' (Or.inl e.symm)
    rw [List.filter_cons_of_pos (by simpa using hne),
      filter_ne_of_nodup rest k (fun e => h' (Or.inr e))]

theorem setAll_dict : ∀ (xs d : List (K × V)),
    (dictMMap (K := K) (V := V)).setAll d xs = .ok (builtinDictUpdate d xs)
  | [], d => rfl
  | (k, v) :: xs, d => by
    simp only [MMap.setAll, dictMMap, bind, Except.bind, builtinDictUpdate, List.foldl_cons]
    exact setAll_dict xs (dictSet d k v)

theorem updateKeys_dict (o : List (K × V)) (hn : (o.map Prod.fst).Nodup) :
    ∀ (suf d : List (K × V)), (∀ p ∈ suf, p ∈ o) →
    (dictMMap (K := K) (V := V)).updateKeys (dictMap o).getitem none d (suf.map Prod.fst) =
      .ok (builtinDictUpdate d suf)
  | [], d, _ => rfl
  | (k, v) :: rest, d, h => by
    have hg : (dictMap o).getitem k = .ok v := by
      simp [dictMap, dictGet, lookup_of_mem o k v hn (h _ (by simp))]
    simp only [List.map_cons, MMap.updateKeys, hg, dictMMap, bind, Except.bind, builtinDictUpdate,
      List.foldl_cons]
    exact updateKeys_dict o hn rest (dictSet d k v) (fun p hp => h p (by simp [hp]))

/-- Pairs as `key, value = item` sees 2-tuples. -/
def pairArgs {K V : Type} (xs : List (K × V)) : List (ItemArg K V) := xs.map (fun p => .two p.1 p.2 none)

theorem setPairs_dict : ∀ (xs d : List (K × V)),
    (dictMMap (K := K) (V := V)).setPairs none d (pairArgs xs) = .ok (builtinDictUpdate d xs)
  | [], d => rfl
  | (k, v) :: xs, d => by
    simp only [pairArgs, List.map_cons, MMap.setPairs, unpack2, dictMMap, bind, Except.bind, builtinDictUpdate,
      List.foldl_cons]
    exact setPairs_dict xs (dictSet d k v)

theorem mmap_popitem_cons (a : K) (b : V) (rest : List (K × V))
    (hn : (((a, b) :: rest).map Prod.fst).Nodup) :
    (dictMMap (K := K) (V := V)).popitem ((a, b) :: rest) = .ok ((a, b), rest) := by
  have hna : a ∉ rest.map Prod.fst := (List.nodup_cons.mp hn).1
  have hl : ((a, b) :: rest).lookup a = some b := by simp [List.lookup]
  have hg : (dictMap ((a, b) :: rest)).getitem a = .ok b := by simp [dictMap, dictGet, hl]
  have hd := dict_del_some _ a b hl
  have hf : ((a, b) :: rest).filter (fun p => p.1 ≠ a) = rest := by
    rw [List.filter_cons_of_neg (by simp), filter_ne_of_nodup rest a hna]
  rw [hf] at hd
  simp [MMap.popitem, dictMMap, dictMap, bind, Except.bind, pure, Except.pure, dictGet, hl, hd]

theorem mmap_clear : ∀ (fuel : Nat) (d : List (K × V)), (d.map Prod.fst).Nodup → d.length < fuel →
    (dictMMap (K := K) (V := V)).clear fuel d = .ok []
  | 0, _, _, h => by omega
  | fuel + 1, [], _, _ => by
    simp [MMap.clear, MMap.popitem, dictMMap, dictMap, bind, Except.bind, isKeyError, bareKeyError,
      throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
  | fuel + 1, (a, b) :: rest, hn, h => by
    simp only [MMap.clear, mmap_popitem_cons a b rest hn]
    exact mmap_clear fuel rest (List.nodup_cons.mp hn).2 (by simp at h; omega)

end

/-- `MutableMapping.pop`, `setdefault`, `update` (from a mapping, from pairs, then keywords) and
`clear` on `dict` primitives give `dict`'s results and leave the same dictionary, including key
order. `popitem` raises `KeyError` on an empty mapping and removes what it returns, but takes the
first key, not the last as `dict.popitem` does; the ABC's docstring says "some (key, value) pair".
Type invariant: distinct keys. -/
def MMapMatchesDict : Prop :=
  ∀ (K V : Type) [DecidableEq K] (d o : List (K × V)) (xs kwds : List (K × V)) (k : K)
    (default : V) (dflt : Option V) (fuel : Nat),
    (d.map Prod.fst).Nodup → (o.map Prod.fst).Nodup → d.length < fuel →
    let M : MMap (List (K × V)) K V := dictMMap
    M.pop d k dflt = builtinDictPop d k dflt ∧
    M.setdefault d k default = .ok (builtinDictSetdefault d k default) ∧
    (∀ gi : K → Py V, M.update d (.other (.ok false) (.ok []) none gi (.ok (pairArgs xs)) none) kwds =
      .ok (builtinDictUpdate (builtinDictUpdate d xs) kwds)) ∧
    M.update d (.mapping (dictMap o)) kwds = .ok (builtinDictUpdate (builtinDictUpdate d o) kwds) ∧
    (∀ ps : Py (List (ItemArg K V)), M.update d (.other (.ok true) (.ok (o.map Prod.fst)) none (dictMap o).getitem ps none)
      kwds = .ok (builtinDictUpdate (builtinDictUpdate d o) kwds)) ∧
    M.clear fuel d = .ok [] ∧
    (d = [] → (M.popitem d).raises "KeyError") ∧
    (∀ a b rest, d = (a, b) :: rest → M.popitem d = .ok ((a, b), rest))

theorem mMapMatchesDict_proven : MMapMatchesDict := by
  intro K V _ d o xs kwds k default dflt fuel hd ho hf M
  have h1 : (dictMMap (K := K) (V := V)).updateKeys (dictMap o).getitem none d (o.map Prod.fst) =
      .ok (builtinDictUpdate d o) := updateKeys_dict o ho o d (fun _ h => h)
  refine ⟨?_, ?_, ?_, ?_, ?_, mmap_clear fuel d hd hf, ?_, ?_⟩
  · cases h : d.lookup k with
    | none =>
      cases dflt <;> simp [M, MMap.pop, builtinDictPop, dictMMap, dictMap, dictGet, h, isKeyError]
    | some v =>
      have hg : (dictMap d).getitem k = .ok v := by simp [dictMap, dictGet, h]
      simp [M, MMap.pop, builtinDictPop, dictMMap, hg, h, dict_del_some d k v h, bind, Except.bind,
        pure, Except.pure]
  · cases h : d.lookup k with
    | none =>
      have h1 := lookup_isSome_any d k
      rw [h] at h1
      have hs : dictSet d k default = d ++ [(k, default)] := by
        have hany : d.any (fun p => decide (p.1 = k)) = false := h1.symm
        simp only [dictSet]
        rw [if_neg (by simp only [hany]; simp)]
      simp [M, MMap.setdefault, builtinDictSetdefault, dictMMap, dictMap, dictGet, h, isKeyError,
        hs, bind, Except.bind, pure, Except.pure]
    | some v =>
      simp [M, MMap.setdefault, builtinDictSetdefault, dictMMap, dictMap, dictGet, h]
  · intro gi
    simp only [M, MMap.update, setPairs_dict, setAll_dict, bind, Except.bind, Bool.false_eq_true, ite_false]
  · have i : (dictMap o).iter = .ok (o.map Prod.fst) := rfl
    have t : (dictMap o).tail = none := rfl
    simp only [M, MMap.update, i, t, h1, setAll_dict, bind, Except.bind]
  · intro ps
    simp only [M, MMap.update, h1, setAll_dict, bind, Except.bind, ite_true]
  · intro h
    subst h
    refine ⟨bareKeyError, ?_, rfl⟩
    rfl
  · intro a b rest h
    subst h
    exact mmap_popitem_cons a b rest hd

end PyLean.CoreLibs.CollAbc
