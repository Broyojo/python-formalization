import PyLean.CoreLibs.CollAbc.Builtins

/-!
`Set` and `MutableSet` mixins against `set`, over an abstract element type with decidable
equality. A builtin set is the duplicate-free list of its elements (`listSet`).
-/

namespace PyLean.CoreLibs.CollAbc

open PyLean

section
variable {α : Type} [DecidableEq α]

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

theorem allIn_list (ys : List α) : ∀ xs : List α,
    allIn (fun x => .ok (decide (x ∈ ys))) xs =
      .ok (decide (∀ x, x ∈ xs → x ∈ ys))
  | [] => by simp [allIn]
  | a :: as => by
    have ih := allIn_list ys as
    by_cases h : a ∈ ys
    · simp [allIn, h, bind, Except.bind, ih]
    · simp [allIn, h, bind, Except.bind, pure, Except.pure]

theorem filterPy_ok (p : α → Bool) : ∀ xs : List α,
    filterPy (fun x => .ok (p x)) xs = .ok (xs.filter p)
  | [] => rfl
  | a :: as => by
    simp only [filterPy, bind, Except.bind, pure, Except.pure, filterPy_ok p as, List.filter_cons]

theorem notIn_list (ys xs : List α) :
    notIn (listSet ys) xs = .ok (xs.filter (fun x => !decide (x ∈ ys))) := by
  have := filterPy_ok (fun x => !decide (x ∈ ys)) xs
  simpa [notIn, listSet, bind, Except.bind, pure, Except.pure] using this

theorem dedup_mem : ∀ (l seen : List α) (z : α), z ∈ dedup seen l ↔ z ∈ seen ∨ z ∈ l
  | [], seen, z => by simp [dedup]
  | x :: xs, seen, z => by
    simp only [dedup]
    split
    · rw [dedup_mem xs seen z]
      simp only [List.mem_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | rfl | h)
        · exact Or.inl h
        · exact Or.inl ‹_›
        · exact Or.inr h
    · rw [dedup_mem xs (x :: seen) z]
      simp only [List.mem_cons]
      constructor
      · rintro ((rfl | h) | h)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | rfl | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr h

theorem dedup_nodup : ∀ (l seen : List α), seen.Nodup → (dedup seen l).Nodup
  | [], seen, h => by simpa [dedup] using (List.reverse_perm seen).symm.nodup h
  | x :: xs, seen, h => by
    simp only [dedup]
    split
    · exact dedup_nodup xs seen h
    · exact dedup_nodup xs (x :: seen) (List.nodup_cons.mpr ⟨‹_›, h⟩)

/-- `o` is an operand holding the elements `ys`: a `Set`, or a plain iterable. -/
def IsOperandOf (o : Operand α) (ys : List α) : Prop :=
  (o = .set (listSet ys) ∧ ys.Nodup) ∨ o = .iterable (.ok ys)

theorem asSet_spec {o : Operand α} {ys : List α} (h : IsOperandOf o ys) :
    ∃ zs, o.asSet? mkSet = some (.ok (listSet zs)) ∧ zs.Nodup ∧ ∀ z, z ∈ zs ↔ z ∈ ys := by
  rcases h with ⟨rfl, hn⟩ | rfl
  · exact ⟨ys, rfl, hn, fun _ => Iff.rfl⟩
  · refine ⟨dedup [] ys, ?_, dedup_nodup ys [] (by simp), ?_⟩
    · simp [Operand.asSet?, mkSet, raiseTail, bind, Except.bind, pure, Except.pure]
    · intro z; simp [dedup_mem]

theorem items_spec {o : Operand α} {ys : List α} (h : IsOperandOf o ys) :
    o.items? = some (.ok ys) := by
  rcases h with ⟨rfl, _⟩ | rfl <;> rfl

theorem tail_spec {o : Operand α} {ys : List α} (h : IsOperandOf o ys) : o.tail = none := by
  rcases h with ⟨rfl, _⟩ | rfl <;> rfl

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
    (∀ it : Py (List α), a.le (.iterable it) = .ok .notImplemented ∧
      a.ge (.iterable it) = .ok .notImplemented ∧ a.eq (.iterable it) = .ok .notImplemented ∧
      a.lt (.iterable it) = .ok .notImplemented ∧ a.gt (.iterable it) = .ok .notImplemented)

theorem le_listSet {α : Type} [DecidableEq α] (xs ys : List α) (hx : xs.Nodup) :
    ∃ b, (listSet xs).le (.set (listSet ys)) = .ok (.val b) ∧ (b = true ↔ ∀ x ∈ xs, x ∈ ys) := by
  by_cases hl : xs.length > ys.length
  · refine ⟨false, by simp [SetV.le, listSet, bind, Except.bind, hl, pure, Except.pure], ?_⟩
    simp only [Bool.false_eq_true, false_iff]
    intro h
    have := (subset_len xs ys hx h).1
    omega
  · refine ⟨decide (∀ x, x ∈ xs → x ∈ ys), ?_, by simp⟩
    have := allIn_list ys xs
    simp only [SetV.le, listSet, bind, Except.bind, hl, pure, Except.pure, ite_false, allInT_none, this]

theorem ge_listSet {α : Type} [DecidableEq α] (xs ys : List α) (hy : ys.Nodup) :
    ∃ b, (listSet xs).ge (.set (listSet ys)) = .ok (.val b) ∧ (b = true ↔ ∀ y ∈ ys, y ∈ xs) := by
  by_cases hl : xs.length < ys.length
  · refine ⟨false, by simp [SetV.ge, listSet, bind, Except.bind, hl, pure, Except.pure], ?_⟩
    simp only [Bool.false_eq_true, false_iff]
    intro h
    have := (subset_len ys xs hy h).1
    omega
  · refine ⟨decide (∀ x, x ∈ ys → x ∈ xs), ?_, by simp⟩
    have := allIn_list xs ys
    simp only [SetV.ge, listSet, bind, Except.bind, hl, pure, Except.pure, ite_false, allInT_none, this]

theorem setCmpMatchBuiltin_proven : SetCmpMatchBuiltin := by
  intro α _ xs ys hx hy a o sub sup
  obtain ⟨b1, h1, h1'⟩ := le_listSet xs ys hx
  obtain ⟨b2, h2, h2'⟩ := ge_listSet xs ys hy
  have hsub := subset_len xs ys hx
  have hsup := subset_len ys xs hy
  refine ⟨⟨b1, h1, h1'⟩, ⟨b2, h2, h2'⟩, ?_, ?_, ?_, ?_⟩
  · by_cases hl : xs.length = ys.length
    · refine ⟨b1, ?_, ?_⟩
      · simp only [a, o, SetV.eq, listSet, bind, Except.bind, hl, ite_true, pure, Except.pure] at h1 ⊢
        simpa [listSet, hl] using h1
      · rw [h1']
        constructor
        · intro h; exact ⟨h, (hsub h).2 (by omega)⟩
        · exact fun h => h.1
    · refine ⟨false, by simp [a, o, SetV.eq, listSet, bind, Except.bind, hl, pure, Except.pure], ?_⟩
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨s1, s2⟩
      have := (hsub s1).1
      have := (hsup s2).1
      omega
  · by_cases hl : xs.length < ys.length
    · refine ⟨b1, ?_, ?_⟩
      · simp only [a, o, SetV.lt, listSet, bind, Except.bind, hl, ite_true, pure, Except.pure] at h1 ⊢
        simpa [listSet] using h1
      · rw [h1']
        constructor
        · intro h
          refine ⟨h, fun s2 => ?_⟩
          have := (hsup s2).1
          omega
        · exact fun h => h.1
    · refine ⟨false, by simp [a, o, SetV.lt, listSet, bind, Except.bind, hl, pure, Except.pure], ?_⟩
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨s1, s2⟩
      exact s2 ((hsub s1).2 (by omega))
  · by_cases hl : xs.length > ys.length
    · refine ⟨b2, ?_, ?_⟩
      · simp only [a, o, SetV.gt, listSet, bind, Except.bind, hl, ite_true, pure, Except.pure] at h2 ⊢
        simpa [listSet] using h2
      · rw [h2']
        constructor
        · intro h
          refine ⟨h, fun s2 => ?_⟩
          have := (hsub s2).1
          omega
        · exact fun h => h.1
    · refine ⟨false, by simp [a, o, SetV.gt, listSet, bind, Except.bind, hl, pure, Except.pure], ?_⟩
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨s1, s2⟩
      exact s2 ((hsup s1).2 (by omega))
  · intro it
    simp [a, SetV.le, SetV.ge, SetV.eq, SetV.lt, SetV.gt]

/-- The operators on a set and either another set or any iterable: `&`, `|`, `-`, reflected `-`
and `^` produce a duplicate-free result with the elements of the intersection, union, differences
and symmetric difference, the same result as `set`, through `_from_iterable`. An operand that is
not iterable gives `NotImplemented`. `isdisjoint` answers whether no element is shared. `Set` docs;
type invariant: `listSet` lists are duplicate-free; `ys` in `IsOperandOf`. -/
def SetAlgebraMatchesBuiltin : Prop :=
  ∀ (α : Type) [DecidableEq α] (xs ys : List α) (o : Operand α), xs.Nodup → IsOperandOf o ys →
    let a := listSet xs
    let spec (r : Py (Ret (SetV α))) (P : α → Prop) : Prop :=
      ∃ s zs, r = .ok (.val s) ∧ s.iter = .ok zs ∧ zs.Nodup ∧ ∀ z, z ∈ zs ↔ P z
    spec (a.and mkSet o) (fun z => z ∈ xs ∧ z ∈ ys) ∧
    spec (a.or mkSet o) (fun z => z ∈ xs ∨ z ∈ ys) ∧
    spec (a.sub mkSet o) (fun z => z ∈ xs ∧ z ∉ ys) ∧
    spec (a.rsub mkSet o) (fun z => z ∈ ys ∧ z ∉ xs) ∧
    spec (a.xor mkSet o) (fun z => (z ∈ xs ∧ z ∉ ys) ∨ (z ∈ ys ∧ z ∉ xs)) ∧
    a.and mkSet .other = .ok .notImplemented ∧
    a.or mkSet .other = .ok .notImplemented ∧
    a.sub mkSet .other = .ok .notImplemented ∧
    a.rsub mkSet .other = .ok .notImplemented ∧
    a.xor mkSet .other = .ok .notImplemented

theorem mkSet_iter {α : Type} [DecidableEq α] (l : List α) : (mkSet l).iter = .ok (dedup [] l) := rfl

theorem mkSet_spec {α : Type} [DecidableEq α] (l : List α) (P : α → Prop)
    (h : ∀ z, z ∈ l ↔ P z) :
    ∃ s zs, (Except.ok (Ret.val (mkSet l)) : Py (Ret (SetV α))) = .ok (.val s) ∧ s.iter = .ok zs ∧
      zs.Nodup ∧ ∀ z, z ∈ zs ↔ P z := by
  refine ⟨mkSet l, dedup [] l, rfl, rfl, dedup_nodup l [] (by simp), ?_⟩
  intro z
  simp [dedup_mem, h]

theorem listSet_iter {α : Type} [DecidableEq α] (l : List α) : (listSet l).iter = .ok l := rfl

theorem listSet_tail {α : Type} [DecidableEq α] (l : List α) : (listSet l).tail = none := rfl

theorem mkSet_tail {α : Type} [DecidableEq α] (l : List α) : (mkSet l).tail = none := rfl
theorem listSet_len {α : Type} [DecidableEq α] (l : List α) :
    (listSet l).len = .ok l.length := rfl

theorem setAlgebraMatchesBuiltin_proven : SetAlgebraMatchesBuiltin := by
  intro α _ xs ys o hx ho a spec
  obtain ⟨zs, hzs, _, hmem⟩ := asSet_spec ho
  have hit := items_spec ho
  have ht := tail_spec ho
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hf := filterPy_ok (fun x => decide (x ∈ xs)) ys
    have : a.and mkSet o = .ok (.val (mkSet (ys.filter (fun x => decide (x ∈ xs))))) := by
      simp only [a, SetV.and, hit, ht, filterT_none, listSet, bind, Except.bind, pure, Except.pure]
      rw [hf]
    rw [this]
    refine mkSet_spec _ _ ?_
    intro z; simp [and_comm]
  · have : a.or mkSet o = .ok (.val (mkSet (xs ++ ys))) := by
      simp only [a, SetV.or, hit, ht, raiseTail, listSet, bind, Except.bind, pure, Except.pure]
    rw [this]
    refine mkSet_spec _ _ ?_
    intro z; simp
  · have : a.sub mkSet o = .ok (.val (mkSet (xs.filter (fun x => !decide (x ∈ zs))))) := by
      simp only [a, SetV.sub, hzs, listSet_iter, listSet_tail, notInT_none, notIn_list, bind, Except.bind, pure,
        Except.pure]
    rw [this]
    refine mkSet_spec _ _ ?_
    intro z; simp [hmem]
  · have : a.rsub mkSet o = .ok (.val (mkSet (zs.filter (fun x => !decide (x ∈ xs))))) := by
      simp only [a, SetV.rsub, hzs, listSet_iter, listSet_tail, notInT_none, notIn_list, bind, Except.bind, pure,
        Except.pure]
    rw [this]
    refine mkSet_spec _ _ ?_
    intro z; simp [hmem]
  · have : a.xor mkSet o = .ok (.val (mkSet
        (dedup [] (xs.filter (fun x => !decide (x ∈ zs))) ++
         dedup [] (zs.filter (fun x => !decide (x ∈ xs)))))) := by
      simp only [a, SetV.xor, hzs, listSet_iter, listSet_tail, notInT_none, notIn_list, mkSet_iter, bind,
        Except.bind, pure, Except.pure]
    rw [this]
    refine mkSet_spec _ _ ?_
    intro z; simp [dedup_mem, hmem]
  · simp [a, SetV.and, SetV.or, SetV.sub, SetV.rsub, SetV.xor, Operand.items?, Operand.asSet?]

theorem isdisjoint_go {α : Type} [DecidableEq α] (xs : List α) (o : Operand α) (ht : o.tail = none) :
    ∀ ys : List α, ∃ b, SetV.isdisjoint.go (listSet xs) o ys = .ok b ∧ (b = true ↔ ∀ z ∈ ys, z ∉ xs)
  | [] => ⟨true, by simp [SetV.isdisjoint.go, ht, raiseTail], by simp⟩
  | y :: ys => by
    by_cases h : y ∈ xs
    · refine ⟨false, ?_, ?_⟩
      · simp [SetV.isdisjoint.go, listSet, h, bind, Except.bind, pure, Except.pure]
      · simp only [Bool.false_eq_true, false_iff]
        intro hall
        exact hall y (by simp) h
    · obtain ⟨b, h1, h2⟩ := isdisjoint_go xs o ht ys
      refine ⟨b, ?_, ?_⟩
      · simpa [SetV.isdisjoint.go, listSet, h, bind, Except.bind] using h1
      · rw [h2]
        simp [h]

/-- `Set.isdisjoint(other)` answers whether no element of the iterable `other` is in the set, and a
non-iterable raises `TypeError`. Docstring: "Return True if two sets have a null intersection." -/
def SetIsdisjointSpec : Prop :=
  ∀ (α : Type) [DecidableEq α] (xs ys : List α) (o : Operand α), IsOperandOf o ys →
    (∃ b, (listSet xs).isdisjoint o = .ok b ∧ (b = true ↔ ∀ z ∈ ys, z ∉ xs)) ∧
    ((listSet xs).isdisjoint .other).raises "TypeError"

theorem setIsdisjointSpec_proven : SetIsdisjointSpec := by
  intro α _ xs ys o ho
  refine ⟨?_, ⟨_, rfl, rfl⟩⟩
  obtain ⟨b, h1, h2⟩ := isdisjoint_go xs o (tail_spec ho) ys
  refine ⟨b, ?_, h2⟩
  simp only [SetV.isdisjoint, items_spec ho, bind, Except.bind]
  exact h1

/-! ### MutableSet -/

section
variable {α : Type} [DecidableEq α]

theorem forAdd_add : ∀ (ys s : List α), s.Nodup →
    ∃ r, forAdd (listMSet (α := α)).add s ys = .ok r ∧ r.Nodup ∧ ∀ z, z ∈ r ↔ z ∈ s ∨ z ∈ ys
  | [], s, h => ⟨s, rfl, h, by simp⟩
  | y :: ys, s, h => by
    by_cases hy : y ∈ s
    · obtain ⟨r, h1, h2, h3⟩ := forAdd_add ys s h
      refine ⟨r, ?_, h2, ?_⟩
      · simpa [forAdd, listMSet, hy, bind, Except.bind] using h1
      · intro z; rw [h3]; simp only [List.mem_cons]
        constructor
        · rintro (a | a)
          · exact Or.inl a
          · exact Or.inr (Or.inr a)
        · rintro (a | rfl | a)
          · exact Or.inl a
          · exact Or.inl hy
          · exact Or.inr a
    · have hn : (s ++ [y]).Nodup := by
        rw [List.nodup_append]
        simp only [List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
          and_self, List.mem_singleton, true_and]
        refine ⟨h, ?_⟩
        intro a ha b hb
        rw [hb]; intro e; exact hy (e ▸ ha)
      obtain ⟨r, h1, h2, h3⟩ := forAdd_add ys (s ++ [y]) hn
      refine ⟨r, ?_, h2, ?_⟩
      · simpa [forAdd, listMSet, hy, bind, Except.bind] using h1
      · intro z; rw [h3]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        constructor
        · rintro ((a | a) | a)
          · exact Or.inl a
          · exact Or.inr (Or.inl a)
          · exact Or.inr (Or.inr a)
        · rintro (a | a | a)
          · exact Or.inl (Or.inl a)
          · exact Or.inl (Or.inr a)
          · exact Or.inr a

theorem forAdd_discard : ∀ (ys s : List α), s.Nodup →
    ∃ r, forAdd (listMSet (α := α)).discard s ys = .ok r ∧ r.Nodup ∧
      ∀ z, z ∈ r ↔ z ∈ s ∧ z ∉ ys
  | [], s, h => ⟨s, rfl, h, by simp⟩
  | y :: ys, s, h => by
    have hn : (s.erase y).Nodup := h.erase y
    obtain ⟨r, h1, h2, h3⟩ := forAdd_discard ys (s.erase y) hn
    refine ⟨r, ?_, h2, ?_⟩
    · simpa [forAdd, listMSet, bind, Except.bind] using h1
    · intro z; rw [h3, h.mem_erase_iff]; simp only [List.mem_cons, not_or]
      constructor
      · rintro ⟨⟨a, b⟩, c⟩; exact ⟨b, a, c⟩
      · rintro ⟨a, b, c⟩; exact ⟨⟨b, a⟩, c⟩

theorem toggle_spec (s : List α) (y : α) (h : s.Nodup) :
    ∃ r, (listMSet (α := α)).toggle s y = .ok r ∧ r.Nodup ∧
      (∀ z, z ≠ y → (z ∈ r ↔ z ∈ s)) ∧ (y ∈ r ↔ y ∉ s) := by
  by_cases hy : y ∈ s
  · refine ⟨s.erase y, ?_, h.erase y, ?_, ?_⟩
    · simp [MSet.toggle, listMSet, listSet, hy, bind, Except.bind, pure, Except.pure]
    · intro z hz; rw [h.mem_erase_iff]; simp [hz]
    · simp [h.mem_erase_iff, hy]
  · have hn : (s ++ [y]).Nodup := by
      rw [List.nodup_append]
      simp only [List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
        and_self, List.mem_singleton, true_and]
      refine ⟨h, ?_⟩
      intro a ha b hb
      rw [hb]; intro e; exact hy (e ▸ ha)
    refine ⟨s ++ [y], ?_, hn, ?_, ?_⟩
    · simp [MSet.toggle, listMSet, listSet, hy, bind, Except.bind, pure, Except.pure]
    · intro z hz; simp [hz]
    · simp [hy]

theorem forAdd_toggle : ∀ (ys s : List α), s.Nodup → ys.Nodup →
    ∃ r, forAdd (listMSet (α := α)).toggle s ys = .ok r ∧ r.Nodup ∧
      ∀ z, z ∈ r ↔ ((z ∈ s ∧ z ∉ ys) ∨ (z ∈ ys ∧ z ∉ s))
  | [], s, h, _ => ⟨s, rfl, h, by simp⟩
  | y :: ys, s, h, hy => by
    obtain ⟨t, ht, htn, ht1, ht2⟩ := toggle_spec s y h
    have hyn : y ∉ ys := (List.nodup_cons.mp hy).1
    obtain ⟨r, h1, h2, h3⟩ := forAdd_toggle ys t htn (List.nodup_cons.mp hy).2
    refine ⟨r, ?_, h2, ?_⟩
    · simp only [forAdd, ht, bind, Except.bind]; exact h1
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
`|=`, `&=`, `^=`, `-=` with a `Set` or (except `^=`, which goes through `_from_iterable`) any
iterable; `s ^= s` and `s -= s` empty the set; `remove` raises `KeyError` for an absent element;
`pop` raises `KeyError` on an empty set, and otherwise removes what it returns; `clear` empties
the set. `fuel > len(s)`. Type invariant: duplicate-free. -/
def MSetMatchesBuiltin : Prop :=
  ∀ (α : Type) [DecidableEq α] (s ys : List α) (o : Operand α) (v : α) (fuel : Nat),
    s.Nodup → IsOperandOf o ys → s.length < fuel →
    let M : MSet (List α) α := listMSet
    let spec (r : Py (List α)) (P : α → Prop) : Prop :=
      ∃ t, r = .ok t ∧ t.Nodup ∧ ∀ z, z ∈ t ↔ P z
    spec (M.ior s o) (fun z => z ∈ s ∨ z ∈ ys) ∧
    spec (M.iand s o) (fun z => z ∈ s ∧ z ∈ ys) ∧
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
  simp [MSet.pop, listMSet, listSet, bind, Except.bind, pure, Except.pure]

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
  have hit := items_spec ho
  have ht := tail_spec ho
  obtain ⟨zs, hzs, hzn, hmem⟩ := asSet_spec ho
  have hclr : M.clear fuel s = .ok [] := clear_set fuel s hf
  refine ⟨?_, ?_, ?_, ?_, hclr, hclr, hclr, ?_, ?_, ?_, ?_⟩
  · obtain ⟨r, h1, h2, h3⟩ := forAdd_add ys s hs
    refine ⟨r, ?_, h2, h3⟩
    simp only [M, MSet.ior, hit, ht, forAddT_none, bind, Except.bind]
    exact h1
  · obtain ⟨r, h1, h2, h3⟩ := forAdd_discard (dedup [] (s.filter (fun x => !decide (x ∈ zs)))) s hs
    refine ⟨r, ?_, h2, ?_⟩
    · have hsub : (M.view s).sub M.fromIter o =
          .ok (.val (mkSet (s.filter (fun x => !decide (x ∈ zs))))) := by
        simp only [M, show (listMSet (α := α)).view s = listSet s from rfl,
          show (listMSet (α := α)).fromIter = mkSet from rfl, SetV.sub, hzs, listSet_iter, listSet_tail,
          notInT_none, notIn_list, bind, Except.bind, pure, Except.pure]
      simp only [MSet.iand, hsub, mkSet_iter, mkSet_tail, forAddT_none, bind, Except.bind]
      exact h1
    · intro z
      rw [h3]
      by_cases a : z ∈ s <;> by_cases b : z ∈ ys <;> simp [dedup_mem, hmem, a, b]
  · obtain ⟨r, h1, h2, h3⟩ := forAdd_discard ys s hs
    refine ⟨r, ?_, h2, h3⟩
    simp only [M, MSet.isub, hit, ht, forAddT_none, bind, Except.bind]
    exact h1
  · rcases ho with ⟨rfl, hyn⟩ | rfl
    · obtain ⟨r, h1, h2, h3⟩ := forAdd_toggle ys s hs hyn
      exact ⟨r, by simpa [M, MSet.ixor, listSet_iter, listSet_tail, bind, Except.bind] using h1, h2, h3⟩
    · obtain ⟨r, h1, h2, h3⟩ := forAdd_toggle (dedup [] ys) s hs (dedup_nodup ys [] (by simp))
      refine ⟨r, ?_, h2, ?_⟩
      · simpa [M, MSet.ixor, show (listMSet (α := α)).fromIter = mkSet from rfl, mkSet_iter, raiseTail, bind,
          Except.bind, pure, Except.pure] using h1
      · intro z; rw [h3]; simp [dedup_mem]
  · intro h
    simp [M, MSet.remove, listMSet, listSet, h, bind, Except.bind, pure, Except.pure]
  · intro h
    refine ⟨.keyError "~value", ?_, rfl⟩
    simp [M, MSet.remove, listMSet, listSet, h, bind, Except.bind, throw, throwThe,
      MonadExcept.throw, MonadExceptOf.throw]
  · intro h
    subst h
    exact ⟨bareKeyError, mset_pop_nil, rfl⟩
  · intro a as h
    subst h
    exact mset_pop_cons a as

end PyLean.CoreLibs.CollAbc
