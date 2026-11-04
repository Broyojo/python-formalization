import PyLean.CoreLibs.CollAbc.Builtins

/-!
`Set` and `MutableSet` mixins against `set`, over an abstract element type with decidable
equality. A builtin set is the duplicate-free list of its elements (`listSet`), and its constructor
inserts each element in turn (`listBuilder`).
-/

namespace PyLean.CoreLibs.CollAbc

open PyLean

section
variable {α : Type} [DecidableEq α]

@[simp] theorem listBuilder_start : (listBuilder (α := α)).start = .ok [] := rfl
@[simp] theorem listBuilder_push (r : List α) (x : α) : (listBuilder (α := α)).push r x = .ok (listAdd r x) := rfl
@[simp] theorem listBuilder_done (r : List α) : (listBuilder (α := α)).done r = .ok (listSet r) := rfl
@[simp] theorem listSet_iter (l : List α) : (listSet l).iter = .ok l := rfl
@[simp] theorem listSet_tail (l : List α) : (listSet l).tail = none := rfl
@[simp] theorem listSet_len (l : List α) : (listSet l).len = .ok l.length := rfl
@[simp] theorem listSet_contains (l : List α) (x : α) : (listSet l).contains x = .ok (decide (x ∈ l)) := rfl

theorem subset_len : ∀ (xs ys : List α), xs.Nodup → (∀ x ∈ xs, x ∈ ys) →
    xs.length ≤ ys.length ∧ (ys.length ≤ xs.length → ∀ y ∈ ys, y ∈ xs)
  | [], ys, _, _ => by
    constructor
    · simp
    · intro h y hy
      cases ys with
      | nil => cases hy
      | cons a as => simp at h
  | x :: xs, ys, hn, hsub => by
    have hx : x ∈ ys := hsub x (by simp)
    have hnx : x ∉ xs := (List.nodup_cons.mp hn).1
    have hxs : xs.Nodup := (List.nodup_cons.mp hn).2
    have hsub' : ∀ z ∈ xs, z ∈ ys.erase x := by
      intro z hz
      have hne : z ≠ x := fun e => hnx (e ▸ hz)
      exact (List.mem_erase_of_ne hne).mpr (hsub z (by simp [hz]))
    have ih := subset_len xs (ys.erase x) hxs hsub'
    have hl : (ys.erase x).length = ys.length - 1 := List.length_erase_of_mem hx
    have hpos : 0 < ys.length := List.length_pos_of_mem hx
    constructor
    · simp only [List.length_cons]; omega
    · intro hle y hy
      by_cases hyx : y = x
      · simp [hyx]
      · have : y ∈ ys.erase x := (List.mem_erase_of_ne hyx).mpr hy
        have h2 := ih.2 (by simp only [List.length_cons] at hle; omega) y this
        simp [h2]

theorem allInT_list (ys : List α) : ∀ xs : List α,
    allInT (fun x => .ok (decide (x ∈ ys))) none xs = .ok (decide (∀ x, x ∈ xs → x ∈ ys))
  | [] => by simp [allInT, raiseTail]
  | a :: as => by
    have ih := allInT_list ys as
    by_cases h : a ∈ ys
    · simp [allInT, h, bind, Except.bind, ih]
    · simp [allInT, h, bind, Except.bind, pure, Except.pure]

theorem append_single_nodup {s : List α} {y : α} (h : s.Nodup) (hy : y ∉ s) : (s ++ [y]).Nodup := by
  rw [List.nodup_append]
  simp only [List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
    and_self, List.mem_singleton, true_and]
  refine ⟨h, ?_⟩
  intro a ha b hb
  rw [hb]; intro e; exact hy (e ▸ ha)

theorem listAdd_nodup {r : List α} (h : r.Nodup) (x : α) : (listAdd r x).Nodup := by
  unfold listAdd
  split
  · exact h
  · exact append_single_nodup h ‹_›

theorem listAdd_mem (r : List α) (x z : α) : z ∈ listAdd r x ↔ z ∈ r ∨ z = x := by
  unfold listAdd
  split
  · rename_i hx
    constructor
    · exact Or.inl
    · rintro (h | rfl)
      · exact h
      · exact hx
  · simp

theorem feedIf_list (keep : α → Py Bool) (p : α → Bool) (hk : ∀ x, keep x = .ok (p x)) :
    ∀ (xs r : List α), r.Nodup →
    ∃ r', feedIf listBuilder keep none r xs = .ok r' ∧ r'.Nodup ∧
      ∀ z, z ∈ r' ↔ z ∈ r ∨ (z ∈ xs ∧ p z = true)
  | [], r, h => ⟨r, rfl, h, by simp⟩
  | x :: xs, r, h => by
    cases hp : p x with
    | true =>
      obtain ⟨r', h1, h2, h3⟩ := feedIf_list keep p hk xs (listAdd r x) (listAdd_nodup h x)
      refine ⟨r', ?_, h2, ?_⟩
      · simpa [feedIf, hk, hp, bind, Except.bind] using h1
      · intro z
        rw [h3, listAdd_mem]
        simp only [List.mem_cons]
        constructor
        · rintro ((a | rfl) | ⟨b, c⟩)
          · exact Or.inl a
          · exact Or.inr ⟨Or.inl rfl, hp⟩
          · exact Or.inr ⟨Or.inr b, c⟩
        · rintro (a | ⟨rfl | b, c⟩)
          · exact Or.inl (Or.inl a)
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr ⟨b, c⟩
    | false =>
      obtain ⟨r', h1, h2, h3⟩ := feedIf_list keep p hk xs r h
      refine ⟨r', ?_, h2, ?_⟩
      · simpa [feedIf, hk, hp, bind, Except.bind] using h1
      · intro z
        rw [h3]
        simp only [List.mem_cons]
        constructor
        · rintro (a | ⟨b, c⟩)
          · exact Or.inl a
          · exact Or.inr ⟨Or.inr b, c⟩
        · rintro (a | ⟨rfl | b, c⟩)
          · exact Or.inl a
          · rw [hp] at c; cases c
          · exact Or.inr ⟨b, c⟩

theorem feedAll_list : ∀ (xs r : List α), r.Nodup →
    ∃ r', feedAll listBuilder none r xs = .ok r' ∧ r'.Nodup ∧ ∀ z, z ∈ r' ↔ z ∈ r ∨ z ∈ xs
  | [], r, h => ⟨r, rfl, h, by simp⟩
  | x :: xs, r, h => by
    obtain ⟨r', h1, h2, h3⟩ := feedAll_list xs (listAdd r x) (listAdd_nodup h x)
    refine ⟨r', ?_, h2, ?_⟩
    · simpa [feedAll, bind, Except.bind] using h1
    · intro z
      rw [h3, listAdd_mem]
      simp only [List.mem_cons]
      constructor
      · rintro ((a | rfl) | b)
        · exact Or.inl a
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr b)
      · rintro (a | rfl | b)
        · exact Or.inl (Or.inl a)
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr b

/-- `o` is an operand holding the elements `ys`: a `Set`, or an iterable that `isinstance(o, Iterable)` accepts. -/
def IsOperandOf (o : Operand α) (ys : List α) : Prop :=
  (o = .set (listSet ys) ∧ ys.Nodup) ∨ o = .iterable true (.ok ys)

theorem operand_spec {o : Operand α} {ys : List α} (h : IsOperandOf o ys) :
    o.items = .ok ys ∧ o.tail = none ∧ o.isIterable = true := by
  rcases h with ⟨rfl, _⟩ | rfl <;> exact ⟨rfl, rfl, rfl⟩

theorem build_list (ys : List α) :
    ∃ r, build listBuilder (.ok ys) none = .ok (listSet r) ∧ r.Nodup ∧ ∀ z, z ∈ r ↔ z ∈ ys := by
  obtain ⟨r', h1, h2, h3⟩ := feedAll_list ys [] List.nodup_nil
  exact ⟨r', by simp [build, h1, bind, Except.bind], h2, by simpa using h3⟩

theorem asSet_spec {o : Operand α} {ys : List α} (h : IsOperandOf o ys) :
    ∃ zs, o.asSet? listBuilder = some (.ok (listSet zs)) ∧ zs.Nodup ∧ ∀ z, z ∈ zs ↔ z ∈ ys := by
  rcases h with ⟨rfl, hn⟩ | rfl
  · exact ⟨ys, rfl, hn, fun _ => Iff.rfl⟩
  · obtain ⟨r, h1, h2, h3⟩ := build_list ys
    exact ⟨r, by simp [Operand.asSet?, h1], h2, h3⟩

theorem sub_listSet (xs zs : List α) :
    ∃ r, (listSet xs).sub listBuilder (.set (listSet zs)) = .ok (.val (listSet r)) ∧ r.Nodup ∧
      ∀ z, z ∈ r ↔ z ∈ xs ∧ z ∉ zs := by
  obtain ⟨r, h1, h2, h3⟩ := feedIf_list (notIn (listSet zs)) (fun x => !decide (x ∈ zs))
    (fun x => by simp [notIn, bind, Except.bind, pure, Except.pure]) xs [] List.nodup_nil
  exact ⟨r, by simp [SetV.sub, Operand.asSet?, h1, bind, Except.bind, pure, Except.pure], h2, by simpa using h3⟩

theorem or_listSet (xs zs : List α) :
    ∃ r, (listSet xs).or listBuilder (.set (listSet zs)) = .ok (.val (listSet r)) ∧ r.Nodup ∧
      ∀ z, z ∈ r ↔ z ∈ xs ∨ z ∈ zs := by
  obtain ⟨r1, h1, h2, h3⟩ := feedAll_list xs [] List.nodup_nil
  obtain ⟨r2, h4, h5, h6⟩ := feedAll_list zs r1 h2
  refine ⟨r2, ?_, h5, ?_⟩
  · simp [SetV.or, Operand.isIterable, Operand.items, Operand.tail, h1, h4, bind, Except.bind, pure, Except.pure]
  · intro z; rw [h6, h3]; simp

end

/-- Comparison mixins on two sets: `<=`, `<`, `>=`, `>`, `==` are subset, proper subset,
superset, proper superset and equal elements, as for `set`, and `NotImplemented` for anything
that is not a `Set`, which lets the reflected operator run. `Set` docs. Type invariant: the
element lists are duplicate-free. -/
def SetCmpMatchBuiltin : Prop :=
  ∀ (α : Type) [DecidableEq α] (xs ys : List α), xs.Nodup → ys.Nodup →
    let a := listSet xs
    let o : Operand α := .set (listSet ys)
    let sub := ∀ x ∈ xs, x ∈ ys
    let sup := ∀ y ∈ ys, y ∈ xs
    (∃ b, a.le o = .ok (.val b) ∧ (b = true ↔ sub)) ∧
    (∃ b, a.ge o = .ok (.val b) ∧ (b = true ↔ sup)) ∧
    (∃ b, a.eq o = .ok (.val b) ∧ (b = true ↔ sub ∧ sup)) ∧
    (∃ b, a.lt o = .ok (.val b) ∧ (b = true ↔ sub ∧ ¬ sup)) ∧
    (∃ b, a.gt o = .ok (.val b) ∧ (b = true ↔ sup ∧ ¬ sub)) ∧
    (∀ (abc : Bool) (it : Py (List α)) (t : Option PyExc), a.le (.iterable abc it t) = .ok .notImplemented ∧
      a.ge (.iterable abc it t) = .ok .notImplemented ∧ a.eq (.iterable abc it t) = .ok .notImplemented ∧
      a.lt (.iterable abc it t) = .ok .notImplemented ∧ a.gt (.iterable abc it t) = .ok .notImplemented)

theorem le_listSet {α : Type} [DecidableEq α] (xs ys : List α) (hx : xs.Nodup) :
    ∃ b, (listSet xs).le (.set (listSet ys)) = .ok (.val b) ∧ (b = true ↔ ∀ x ∈ xs, x ∈ ys) := by
  by_cases hl : xs.length > ys.length
  · refine ⟨false, by simp [SetV.le, bind, Except.bind, hl, pure, Except.pure], ?_⟩
    simp only [Bool.false_eq_true, false_iff]
    intro h
    have := (subset_len xs ys hx h).1
    omega
  · refine ⟨decide (∀ x, x ∈ xs → x ∈ ys), ?_, by simp⟩
    have := allInT_list ys xs
    simp only [SetV.le, listSet_len, listSet_iter, listSet_tail, bind, Except.bind, hl, pure, Except.pure,
      ite_false]
    simp only [listSet] at this ⊢
    rw [this]

theorem ge_listSet {α : Type} [DecidableEq α] (xs ys : List α) (hy : ys.Nodup) :
    ∃ b, (listSet xs).ge (.set (listSet ys)) = .ok (.val b) ∧ (b = true ↔ ∀ y ∈ ys, y ∈ xs) := by
  by_cases hl : xs.length < ys.length
  · refine ⟨false, by simp [SetV.ge, bind, Except.bind, hl, pure, Except.pure], ?_⟩
    simp only [Bool.false_eq_true, false_iff]
    intro h
    have := (subset_len ys xs hy h).1
    omega
  · refine ⟨decide (∀ x, x ∈ ys → x ∈ xs), ?_, by simp⟩
    have := allInT_list xs ys
    simp only [SetV.ge, listSet_len, listSet_iter, listSet_tail, bind, Except.bind, hl, pure, Except.pure,
      ite_false]
    simp only [listSet] at this ⊢
    rw [this]

theorem setCmpMatchBuiltin_proven : SetCmpMatchBuiltin := by
  intro α _ xs ys hx hy a o sub sup
  obtain ⟨b1, h1, h1'⟩ := le_listSet xs ys hx
  obtain ⟨b2, h2, h2'⟩ := ge_listSet xs ys hy
  have hsub := subset_len xs ys hx
  have hsup := subset_len ys xs hy
  refine ⟨⟨b1, h1, h1'⟩, ⟨b2, h2, h2'⟩, ?_, ?_, ?_, ?_⟩
  · by_cases hl : xs.length = ys.length
    · refine ⟨b1, ?_, ?_⟩
      · simp only [a, o, SetV.eq, listSet_len, bind, Except.bind, hl, ite_true, pure, Except.pure] at h1 ⊢
        exact h1
      · rw [h1']
        constructor
        · intro h; exact ⟨h, (hsub h).2 (by omega)⟩
        · exact fun h => h.1
    · refine ⟨false, by simp [a, o, SetV.eq, bind, Except.bind, hl, pure, Except.pure], ?_⟩
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨s1, s2⟩
      have := (hsub s1).1
      have := (hsup s2).1
      omega
  · by_cases hl : xs.length < ys.length
    · refine ⟨b1, ?_, ?_⟩
      · simp only [a, o, SetV.lt, listSet_len, bind, Except.bind, hl, ite_true, pure, Except.pure] at h1 ⊢
        exact h1
      · rw [h1']
        constructor
        · intro h
          refine ⟨h, fun s2 => ?_⟩
          have := (hsup s2).1
          omega
        · exact fun h => h.1
    · refine ⟨false, by simp [a, o, SetV.lt, bind, Except.bind, hl, pure, Except.pure], ?_⟩
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨s1, s2⟩
      exact s2 ((hsub s1).2 (by omega))
  · by_cases hl : xs.length > ys.length
    · refine ⟨b2, ?_, ?_⟩
      · simp only [a, o, SetV.gt, listSet_len, bind, Except.bind, hl, ite_true, pure, Except.pure] at h2 ⊢
        exact h2
      · rw [h2']
        constructor
        · intro h
          refine ⟨h, fun s2 => ?_⟩
          have := (hsub s2).1
          omega
        · exact fun h => h.1
    · refine ⟨false, by simp [a, o, SetV.gt, bind, Except.bind, hl, pure, Except.pure], ?_⟩
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨s1, s2⟩
      exact s2 ((hsup s1).2 (by omega))
  · intro abc it t
    simp [a, SetV.le, SetV.ge, SetV.eq, SetV.lt, SetV.gt]

/-- The operators on a set and either another set or any iterable that `isinstance(o, Iterable)` accepts: `&`, `|`,
`-`, reflected `-` and `^` (with `-` and `|` of the same class) produce a duplicate-free result with the elements of
the intersection, union, differences and symmetric difference, the same result as `set`, through `_from_iterable`. An
operand that is not `Iterable`, an object with only `__getitem__` included, gives `NotImplemented`. `Set` docs; type
invariant: `listSet` lists are duplicate-free; `ys` in `IsOperandOf`. -/
def SetAlgebraMatchesBuiltin : Prop :=
  ∀ (α : Type) [DecidableEq α] (xs ys : List α) (o : Operand α), xs.Nodup → IsOperandOf o ys →
    let a := listSet xs
    let spec (r : Py (Ret (SetV α))) (P : α → Prop) : Prop :=
      ∃ s zs, r = .ok (.val s) ∧ s.iter = .ok zs ∧ zs.Nodup ∧ ∀ z, z ∈ zs ↔ P z
    spec (a.and listBuilder o) (fun z => z ∈ xs ∧ z ∈ ys) ∧
    spec (a.or listBuilder o) (fun z => z ∈ xs ∨ z ∈ ys) ∧
    spec (a.sub listBuilder o) (fun z => z ∈ xs ∧ z ∉ ys) ∧
    spec (a.rsub listBuilder o) (fun z => z ∈ ys ∧ z ∉ xs) ∧
    spec (a.xor listBuilder mixinMinus mixinOr o) (fun z => (z ∈ xs ∧ z ∉ ys) ∨ (z ∈ ys ∧ z ∉ xs)) ∧
    (∀ (it : Py (List α)) (t : Option PyExc),
      a.and listBuilder (.iterable false it t) = .ok .notImplemented ∧
      a.or listBuilder (.iterable false it t) = .ok .notImplemented ∧
      a.sub listBuilder (.iterable false it t) = .ok .notImplemented ∧
      a.rsub listBuilder (.iterable false it t) = .ok .notImplemented ∧
      a.xor listBuilder mixinMinus mixinOr (.iterable false it t) = .ok .notImplemented)

theorem setAlgebraMatchesBuiltin_proven : SetAlgebraMatchesBuiltin := by
  intro α _ xs ys o hx ho a spec
  obtain ⟨zs, hzs, hzn, hmem⟩ := asSet_spec ho
  obtain ⟨hit, ht, hab⟩ := operand_spec ho
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨r, h1, h2, h3⟩ := feedIf_list (listSet xs).contains (fun x => decide (x ∈ xs)) (fun _ => rfl) ys []
      List.nodup_nil
    refine ⟨listSet r, r, ?_, rfl, h2, ?_⟩
    · simp [a, SetV.and, hab, hit, ht, h1, bind, Except.bind, pure, Except.pure]
    · intro z; rw [h3]; simp [and_comm]
  · obtain ⟨r1, h1, h2, h3⟩ := feedAll_list xs [] List.nodup_nil
    obtain ⟨r2, h4, h5, h6⟩ := feedAll_list ys r1 h2
    refine ⟨listSet r2, r2, ?_, rfl, h5, ?_⟩
    · simp [a, SetV.or, hab, hit, ht, h1, h4, bind, Except.bind, pure, Except.pure]
    · intro z; rw [h6, h3]; simp
  · obtain ⟨r, h1, h2, h3⟩ := sub_listSet xs zs
    refine ⟨listSet r, r, ?_, rfl, h2, ?_⟩
    · have e : a.sub listBuilder o = (listSet xs).sub listBuilder (.set (listSet zs)) := by
        simp only [a, SetV.sub, hzs]
        rfl
      rw [e, h1]
    · intro z; rw [h3, hmem]
  · obtain ⟨r, h1, h2, h3⟩ := feedIf_list (notIn (listSet xs)) (fun x => !decide (x ∈ xs))
      (fun x => by simp [notIn, bind, Except.bind, pure, Except.pure]) zs [] List.nodup_nil
    refine ⟨listSet r, r, ?_, rfl, h2, ?_⟩
    · simp [a, SetV.rsub, hzs, h1, bind, Except.bind, pure, Except.pure]
    · intro z; rw [h3]; simp [hmem]
  · obtain ⟨r1, h1, h2, h3⟩ := sub_listSet xs zs
    obtain ⟨r2, h4, h5, h6⟩ := sub_listSet zs xs
    obtain ⟨r3, h7, h8, h9⟩ := or_listSet r1 r2
    refine ⟨listSet r3, r3, ?_, rfl, h8, ?_⟩
    · simp [a, SetV.xor, hzs, mixinMinus, mixinOr, retOr, h1, h4, h7, bind, Except.bind, pure, Except.pure]
    · intro z; rw [h9, h3, h6, hmem]
  · intro it t
    simp [a, SetV.and, SetV.or, SetV.sub, SetV.rsub, SetV.xor, Operand.isIterable, Operand.asSet?]

/-- `Set.isdisjoint(other)` answers whether no element of the iterable `other` is in the set, for any iterable `iter()`
accepts, an object with only `__getitem__` included (`isinstance(other, Iterable)` is not tested), and an object
`iter()` refuses raises its `TypeError`. Docstring: "Return True if two sets have a null intersection." -/
def SetIsdisjointSpec : Prop :=
  ∀ (α : Type) [DecidableEq α] (xs ys : List α) (abc : Bool),
    (∃ b, (listSet xs).isdisjoint (.iterable abc (.ok ys)) = .ok b ∧ (b = true ↔ ∀ z ∈ ys, z ∉ xs)) ∧
    (∃ b, (listSet xs).isdisjoint (.set (listSet ys)) = .ok b ∧ (b = true ↔ ∀ z ∈ ys, z ∉ xs)) ∧
    ((listSet xs).isdisjoint .other).raises "TypeError"

theorem disjoint_go {α : Type} [DecidableEq α] (xs : List α) :
    ∀ ys : List α, ∃ b, disjointLoop (listSet xs).contains none ys = .ok b ∧ (b = true ↔ ∀ z ∈ ys, z ∉ xs)
  | [] => ⟨true, by simp [disjointLoop, raiseTail], by simp⟩
  | y :: ys => by
    by_cases h : y ∈ xs
    · refine ⟨false, ?_, ?_⟩
      · simp [disjointLoop, h, bind, Except.bind, pure, Except.pure]
      · simp only [Bool.false_eq_true, false_iff]
        intro hall
        exact hall y (by simp) h
    · obtain ⟨b, h1, h2⟩ := disjoint_go xs ys
      refine ⟨b, ?_, ?_⟩
      · simpa [disjointLoop, h, bind, Except.bind] using h1
      · rw [h2]
        simp [h]

theorem setIsdisjointSpec_proven : SetIsdisjointSpec := by
  intro α _ xs ys abc
  obtain ⟨b, h1, h2⟩ := disjoint_go xs ys
  refine ⟨⟨b, ?_, h2⟩, ⟨b, ?_, h2⟩, ⟨_, rfl, rfl⟩⟩
  · simpa [SetV.isdisjoint, Operand.items, Operand.tail, bind, Except.bind] using h1
  · simpa [SetV.isdisjoint, Operand.items, Operand.tail, bind, Except.bind] using h1

/-! ### MutableSet -/

section
variable {α : Type} [DecidableEq α]

theorem forAdd_add : ∀ (ys s : List α), s.Nodup →
    ∃ r, forAddT (listMSet (α := α)).add none s ys = .ok r ∧ r.Nodup ∧ ∀ z, z ∈ r ↔ z ∈ s ∨ z ∈ ys
  | [], s, h => ⟨s, rfl, h, by simp⟩
  | y :: ys, s, h => by
    obtain ⟨r, h1, h2, h3⟩ := forAdd_add ys (listAdd s y) (listAdd_nodup h y)
    refine ⟨r, ?_, h2, ?_⟩
    · simpa [forAddT, listMSet, bind, Except.bind] using h1
    · intro z; rw [h3, listAdd_mem]; simp only [List.mem_cons]
      constructor
      · rintro ((a | rfl) | a)
        · exact Or.inl a
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr a)
      · rintro (a | rfl | a)
        · exact Or.inl (Or.inl a)
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr a

theorem forAdd_discard : ∀ (ys s : List α), s.Nodup →
    ∃ r, forAddT (listMSet (α := α)).discard none s ys = .ok r ∧ r.Nodup ∧
      ∀ z, z ∈ r ↔ z ∈ s ∧ z ∉ ys
  | [], s, h => ⟨s, rfl, h, by simp⟩
  | y :: ys, s, h => by
    have hn : (s.erase y).Nodup := h.erase y
    obtain ⟨r, h1, h2, h3⟩ := forAdd_discard ys (s.erase y) hn
    refine ⟨r, ?_, h2, ?_⟩
    · simpa [forAddT, listMSet, bind, Except.bind] using h1
    · intro z; rw [h3, h.mem_erase_iff]; simp only [List.mem_cons, not_or]
      constructor
      · rintro ⟨⟨a, b⟩, c⟩; exact ⟨b, a, c⟩
      · rintro ⟨a, b, c⟩; exact ⟨⟨b, a⟩, c⟩

theorem toggle_spec (s : List α) (y : α) (h : s.Nodup) :
    ∃ r, (listMSet (α := α)).toggle s y = .ok r ∧ r.Nodup ∧
      (∀ z, z ≠ y → (z ∈ r ↔ z ∈ s)) ∧ (y ∈ r ↔ y ∉ s) := by
  by_cases hy : y ∈ s
  · refine ⟨s.erase y, ?_, h.erase y, ?_, ?_⟩
    · simp [MSet.toggle, listMSet, hy, bind, Except.bind, pure, Except.pure]
    · intro z hz; rw [h.mem_erase_iff]; simp [hz]
    · simp [h.mem_erase_iff, hy]
  · refine ⟨s ++ [y], ?_, append_single_nodup h hy, ?_, ?_⟩
    · simp [MSet.toggle, listMSet, listAdd, hy, bind, Except.bind, pure, Except.pure]
    · intro z hz; simp [hz]
    · simp [hy]

theorem forAdd_toggle : ∀ (ys s : List α), s.Nodup → ys.Nodup →
    ∃ r, forAddT (listMSet (α := α)).toggle none s ys = .ok r ∧ r.Nodup ∧
      ∀ z, z ∈ r ↔ ((z ∈ s ∧ z ∉ ys) ∨ (z ∈ ys ∧ z ∉ s))
  | [], s, h, _ => ⟨s, rfl, h, by simp⟩
  | y :: ys, s, h, hy => by
    obtain ⟨t, ht, htn, ht1, ht2⟩ := toggle_spec s y h
    have hyn : y ∉ ys := (List.nodup_cons.mp hy).1
    obtain ⟨r, h1, h2, h3⟩ := forAdd_toggle ys t htn (List.nodup_cons.mp hy).2
    refine ⟨r, ?_, h2, ?_⟩
    · simp only [forAddT, ht, bind, Except.bind]; exact h1
    · intro z
      rw [h3]
      by_cases hz : z = y
      · subst hz
        simp only [List.mem_cons, true_or, not_true_eq_false, and_false, false_or, true_and]
        constructor
        · rintro (⟨a, _⟩ | ⟨a, _⟩)
          · exact ht2.mp a
          · exact absurd a hyn
        · intro a; exact Or.inl ⟨ht2.mpr a, hyn⟩
      · have := ht1 z hz
        simp only [this, List.mem_cons, hz, false_or]

end

/-- In-place operators and element removal on a `list`-backed set behave like `set`:
`|=`, `&=`, `^=`, `-=` with a `Set` or any `Iterable`; `s ^= s` and `s -= s` empty the set; `remove` raises `KeyError`
for an absent element; `pop` raises `KeyError` on an empty set, and otherwise removes what it returns; `clear` empties
the set. `fuel > len(s)`. Type invariant: duplicate-free. -/
def MSetMatchesBuiltin : Prop :=
  ∀ (α : Type) [DecidableEq α] (s ys : List α) (o : Operand α) (v : α) (fuel : Nat),
    s.Nodup → IsOperandOf o ys → s.length < fuel →
    let M := listMSet (α := α)
    let spec (r : Py (List α)) (P : α → Prop) : Prop :=
      ∃ t, r = .ok t ∧ t.Nodup ∧ ∀ z, z ∈ t ↔ P z
    spec (M.ior s o) (fun z => z ∈ s ∨ z ∈ ys) ∧
    spec (M.iand s o none false) (fun z => z ∈ s ∧ z ∈ ys) ∧
    spec (M.isub s (some o) fuel) (fun z => z ∈ s ∧ z ∉ ys) ∧
    spec (M.ixor s (some o) fuel) (fun z => (z ∈ s ∧ z ∉ ys) ∨ (z ∈ ys ∧ z ∉ s)) ∧
    M.ixor s none fuel = .ok [] ∧ M.isub s none fuel = .ok [] ∧
    M.clear fuel s = .ok [] ∧
    (v ∈ s → M.remove s v = .ok (s.erase v)) ∧
    (v ∉ s → (M.remove s v).raises "KeyError") ∧
    (s = [] → (M.pop s).raises "KeyError") ∧
    (∀ a as, s = a :: as → M.pop s = .ok (a, as))

theorem mset_pop_nil {α : Type} [DecidableEq α] :
    (listMSet (α := α)).pop [] = .error bareKeyError := rfl

theorem mset_pop_cons {α : Type} [DecidableEq α] (a : α) (as : List α) :
    (listMSet (α := α)).pop (a :: as) = .ok (a, as) := by
  simp [MSet.pop, listMSet, bind, Except.bind, pure, Except.pure]

theorem clear_set {α : Type} [DecidableEq α] : ∀ (fuel : Nat) (s : List α),
    s.length < fuel → (listMSet (α := α)).clear fuel s = .ok []
  | 0, s, h => by omega
  | fuel + 1, [], _ => by
    simp only [MSet.clear, mset_pop_nil, isKeyError, bareKeyError, ite_true]
  | fuel + 1, a :: as, h => by
    simp only [MSet.clear, mset_pop_cons]
    exact clear_set fuel as (by simp at h; omega)

theorem mSetMatchesBuiltin_proven : MSetMatchesBuiltin := by
  intro α _ s ys o v fuel hs ho hf M spec
  obtain ⟨hit, ht, hab⟩ := operand_spec ho
  obtain ⟨zs, hzs, hzn, hmem⟩ := asSet_spec ho
  have hclr : M.clear fuel s = .ok [] := clear_set fuel s hf
  refine ⟨?_, ?_, ?_, ?_, hclr, hclr, hclr, ?_, ?_, ?_, ?_⟩
  · obtain ⟨r, h1, h2, h3⟩ := forAdd_add ys s hs
    refine ⟨r, ?_, h2, h3⟩
    simp only [M, MSet.ior, hit, ht, bind, Except.bind]
    exact h1
  · obtain ⟨d, hd1, hd2, hd3⟩ := sub_listSet s zs
    obtain ⟨r, h1, h2, h3⟩ := forAdd_discard d s hs
    refine ⟨r, ?_, h2, ?_⟩
    · have hsub : (M.view s).sub M.fromIter o = .ok (.val (listSet d)) := by
        have e : (M.view s).sub M.fromIter o = (listSet s).sub listBuilder (.set (listSet zs)) := by
          simp only [M, show (listMSet (α := α)).view s = listSet s from rfl,
            show (listMSet (α := α)).fromIter = listBuilder from rfl, SetV.sub, hzs]
          rfl
        rw [e, hd1]
      simp only [MSet.iand, binaryOp, retOr, hsub, listSet_iter, listSet_tail, bind, Except.bind, pure,
        Except.pure]
      exact h1
    · intro z
      rw [h3, hd3, hmem]
      by_cases a : z ∈ s <;> by_cases b : z ∈ ys <;> simp [a, b]
  · obtain ⟨r, h1, h2, h3⟩ := forAdd_discard ys s hs
    refine ⟨r, ?_, h2, h3⟩
    simp only [M, MSet.isub, hit, ht, bind, Except.bind]
    exact h1
  · rcases ho with ⟨rfl, hyn⟩ | rfl
    · obtain ⟨r, h1, h2, h3⟩ := forAdd_toggle ys s hs hyn
      exact ⟨r, by simpa [M, MSet.ixor, bind, Except.bind] using h1, h2, h3⟩
    · obtain ⟨b, hb1, hb2, hb3⟩ := build_list ys
      obtain ⟨r, h1, h2, h3⟩ := forAdd_toggle b s hs hb2
      refine ⟨r, ?_, h2, ?_⟩
      · have e : build M.fromIter (.ok ys) none = .ok (listSet b) := hb1
        simp only [M, MSet.ixor, e, listSet_iter, listSet_tail, bind, Except.bind]
        exact h1
      · intro z; rw [h3, hb3]
  · intro h
    simp [M, MSet.remove, listMSet, h, bind, Except.bind, pure, Except.pure]
  · intro h
    refine ⟨.keyError "~value", ?_, rfl⟩
    simp [M, MSet.remove, listMSet, h, bind, Except.bind, throw, throwThe,
      MonadExcept.throw, MonadExceptOf.throw]
  · intro h
    subst h
    exact ⟨bareKeyError, mset_pop_nil, rfl⟩
  · intro a as h
    subst h
    exact mset_pop_cons a as


/-! ### `_from_iterable` -/

section
variable {α : Type} [DecidableEq α]

theorem feedAll_setb (hash : α → Py Unit) (t : Option PyExc) : ∀ (xs r : List α), r.Nodup →
    (∀ x ∈ xs, hash x = .ok ()) →
    ∃ r', feedAll (setBuilder hash) t r xs = raiseTail t r' ∧ r'.Nodup ∧ ∀ z, z ∈ r' ↔ z ∈ r ∨ z ∈ xs
  | [], r, h, _ => ⟨r, rfl, h, by simp⟩
  | x :: xs, r, h, hh => by
    have hx := hh x (by simp)
    obtain ⟨r', h1, h2, h3⟩ := feedAll_setb hash t xs (listAdd r x) (listAdd_nodup h x)
      (fun y hy => hh y (by simp [hy]))
    refine ⟨r', ?_, h2, ?_⟩
    · simp only [feedAll, setBuilder, hx, bind, Except.bind, pure, Except.pure]
      exact h1
    · intro z
      rw [h3, listAdd_mem]
      simp only [List.mem_cons]
      constructor
      · rintro ((a | rfl) | b)
        · exact Or.inl a
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr b)
      · rintro (a | rfl | b)
        · exact Or.inl (Or.inl a)
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr b

theorem feedAll_setb_err (hash : α → Py Unit) (t : Option PyExc) (z : α) (post : List α) (e : PyExc)
    (hz : hash z = .error e) : ∀ (pre r : List α), (∀ x ∈ pre, hash x = .ok ()) →
    feedAll (setBuilder hash) t r (pre ++ z :: post) = .error e
  | [], r, _ => by simp [feedAll, setBuilder, hz, bind, Except.bind]
  | x :: xs, r, hh => by
    have hx := hh x (by simp)
    simp only [List.cons_append, feedAll, setBuilder, hx, bind, Except.bind, pure, Except.pure]
    exact feedAll_setb_err hash t z post e hz xs _ (fun y hy => hh y (by simp [hy]))

end

/-- `KeysView._from_iterable` and `ItemsView._from_iterable` ignore `cls` and build a builtin `set`:
`iter(it)` failing is the outcome, then the first element whose hash fails (after the earlier ones were inserted),
then the iterator's end; with every element hashable the result holds exactly the elements, once each.
Lib/_collections_abc.py:851-853, 869-871. -/
def FromIterableSpec : Prop :=
  ∀ (C α : Type) [DecidableEq α] (hash : α → Py Unit) (cls cls' : C) (it : Py (List α)) (t : Option PyExc)
    (xs pre post : List α) (z : α) (e : PyExc),
    viewFromIterable hash cls it t = viewFromIterable hash cls' it t ∧
    viewFromIterable hash cls (.error e) t = .error e ∧
    (hash z = .error e → (∀ x ∈ pre, hash x = .ok ()) →
      viewFromIterable hash cls (.ok (pre ++ z :: post)) t = .error e) ∧
    ((∀ x ∈ xs, hash x = .ok ()) →
      ∃ r, viewFromIterable hash cls (.ok xs) none = .ok r ∧ r.Nodup ∧ ∀ w, w ∈ r ↔ w ∈ xs) ∧
    ((∀ x ∈ xs, hash x = .ok ()) → viewFromIterable hash cls (.ok xs) (some e) = .error e)

theorem fromIterableSpec_proven : FromIterableSpec := by
  intro C α _ hash cls cls' it t xs pre post z e
  have hs : (setBuilder hash).start = .ok [] := rfl
  have hd : ∀ r, (setBuilder hash).done r = .ok r := fun _ => rfl
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro hz hp
    simp only [viewFromIterable, build, hs, feedAll_setb_err hash t z post e hz pre [] hp, bind, Except.bind]
  · intro hh
    obtain ⟨r, h1, h2, h3⟩ := feedAll_setb hash none xs [] List.nodup_nil hh
    refine ⟨r, ?_, h2, by simpa using h3⟩
    simp only [raiseTail] at h1
    simp only [viewFromIterable, build, hs, hd, h1, bind, Except.bind]
  · intro hh
    obtain ⟨r, h1, _, _⟩ := feedAll_setb hash (some e) xs [] List.nodup_nil hh
    simp only [raiseTail] at h1
    simp only [viewFromIterable, build, hs, h1, bind, Except.bind]

end PyLean.CoreLibs.CollAbc
