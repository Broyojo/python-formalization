import PyLean.TextLibs.DifflibObj
import PyLean.TextLibs.DifflibQuick
import PyLean.TextLibs.DifflibLongest

/-!
On lawful elements a matcher over objects does what the matcher over natural numbers does on the classes
of those elements under `__eq__`. So the theorems of `DifflibProps` and the files after it carry over to
any hashable element.
-/

namespace PyLean.TextLibs.Difflib

open PyLean

set_option linter.unusedSimpArgs false

variable {α : Type}

/-- The elements of `xs` are what `dict` asks of its keys: `__hash__` and `__eq__` do not raise, `__eq__` is
an equivalence that `is` implies, and equal elements have equal hashes. `float('nan')` fails this, since
it does not equal itself; a class that defines `__eq__` as most do passes. -/
structure Lawful (o : Ops α) (xs : List α) : Prop where
  hash_ok : ∀ x ∈ xs, ∃ h, o.hash x = .ok h
  eq_ok : ∀ x ∈ xs, ∀ y ∈ xs, ∃ b, o.eq x y = .ok b
  refl : ∀ x ∈ xs, o.eq x x = .ok true
  symm : ∀ x ∈ xs, ∀ y ∈ xs, o.eq x y = o.eq y x
  trans : ∀ x ∈ xs, ∀ y ∈ xs, ∀ z ∈ xs, o.eq x y = .ok true → o.eq y z = .ok true → o.eq x z = .ok true
  hash_eq : ∀ x ∈ xs, ∀ y ∈ xs, o.eq x y = .ok true → o.hash x = o.hash y
  same_eq : ∀ x ∈ xs, ∀ y ∈ xs, o.same x y = true → o.eq x y = .ok true

/-- Is the result `True`? -/
def isT : Py Bool → Bool
  | .ok true => true
  | _ => false

/-- The class of `x` under `__eq__`, among `xs`: the place of the first element of `xs` equal to it. -/
def cls (o : Ops α) (xs : List α) (x : α) : Nat := xs.findIdx fun y => isT (o.eq y x)

theorem findIdx_ext {β : Type} (p q : β → Bool) : ∀ l : List β, (∀ y ∈ l, p y = q y) → l.findIdx p = l.findIdx q := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a r ih =>
    intro h
    have h1 := h a (by simp)
    have h2 := ih (fun y hy => h y (by simp [hy]))
    simp [List.findIdx_cons, h1, h2]

section Class

variable {o : Ops α} {xs : List α} (L : Lawful o xs)

include L

theorem isT_of (x y z : α) (hx : x ∈ xs) (hy : y ∈ xs) (hz : z ∈ xs) (h : o.eq y z = .ok true) :
    isT (o.eq x y) = isT (o.eq x z) := by
  have hs : o.eq z y = .ok true := by rw [← L.symm y hy z hz]; exact h
  cases h1 : o.eq x y with
  | error e =>
    obtain ⟨b, hb⟩ := L.eq_ok x hx y hy
    rw [hb] at h1
    cases h1
  | ok b =>
    cases b with
    | true =>
      rw [L.trans x hx y hy z hz h1 h]
    | false =>
      cases h2 : o.eq x z with
      | error e => rfl
      | ok c =>
        cases c with
        | false => rfl
        | true =>
          have := L.trans x hx z hz y hy h2 hs
          rw [h1] at this
          cases this

theorem cls_of_eq (x y : α) (hx : x ∈ xs) (hy : y ∈ xs) (h : o.eq x y = .ok true) : cls o xs x = cls o xs y :=
  findIdx_ext _ _ xs fun z hz => isT_of L z x y hz hx hy h

theorem cls_spec (w : α) (hw : w ∈ xs) : ∃ h : cls o xs w < xs.length, o.eq (xs[cls o xs w]'h) w = .ok true := by
  have hlt : cls o xs w < xs.length :=
    List.findIdx_lt_length_of_exists ⟨w, hw, by simp [L.refl w hw, isT]⟩
  refine ⟨hlt, ?_⟩
  have := List.findIdx_getElem (w := hlt)
  have e : ∀ r : Py Bool, isT r = true → r = .ok true := by
    intro r hr
    match r, hr with
    | .ok true, _ => rfl
  exact e _ this

theorem eq_of_cls (x y : α) (hx : x ∈ xs) (hy : y ∈ xs) (h : cls o xs x = cls o xs y) : o.eq x y = .ok true := by
  obtain ⟨h1, h2⟩ := cls_spec L x hx
  obtain ⟨h3, h4⟩ := cls_spec L y hy
  have hm : xs[cls o xs x]'h1 ∈ xs := List.getElem_mem h1
  have e : xs[cls o xs x]'h1 = xs[cls o xs y]'h3 := by simp only [h]
  rw [← e] at h4
  have h5 : o.eq x (xs[cls o xs x]'h1) = .ok true := by rw [L.symm x hx _ hm]; exact h2
  exact L.trans x hx _ hm y hy h5 h4

/-- `==` on lawful elements is equality of classes. -/
theorem eq_val (x y : α) (hx : x ∈ xs) (hy : y ∈ xs) : o.eq x y = .ok (cls o xs x == cls o xs y) := by
  obtain ⟨b, hb⟩ := L.eq_ok x hx y hy
  by_cases h : cls o xs x = cls o xs y
  · rw [eq_of_cls L x y hx hy h]
    simp [h]
  · cases b with
    | true => exact absurd (cls_of_eq L x y hx hy hb) h
    | false =>
      rw [hb]
      simp [h]

theorem keyIs_val (k x : α) (h hx : Nat) (hk : k ∈ xs) (hX : x ∈ xs) (e1 : o.hash k = .ok h) (e2 : o.hash x = .ok hx) :
    keyIs o k h x hx = .ok (cls o xs k == cls o xs x) := by
  unfold keyIs
  by_cases h1 : o.same k x = true
  · have := cls_of_eq L k x hk hX (L.same_eq k hk x hX h1)
    simp [h1, this]
  · simp only [h1, Bool.false_eq_true, if_false]
    by_cases h2 : h = hx
    · subst h2
      simp only [beq_self_eq_true, if_true]
      exact eq_val L k x hk hX
    · have h3 : (h == hx) = false := by simpa using h2
      have h4 : cls o xs k ≠ cls o xs x := by
        intro e
        have := L.hash_eq k hk x hX (eq_of_cls L k x hk hX e)
        rw [e1, e2] at this
        exact h2 (by simpa using this)
      simp [h3, h4]

end Class

/-- Every key of a dict is one of `xs` and is stored with its hash. -/
def Good (o : Ops α) (xs : List α) {V : Type} (m : DictO α V) : Prop :=
  ∀ e ∈ m, e.1 ∈ xs ∧ o.hash e.1 = .ok e.2.1

/-- A dict with its keys replaced by their classes. -/
def proj (o : Ops α) (xs : List α) {V : Type} (m : DictO α V) : List (Nat × V) :=
  m.map fun e => (cls o xs e.1, e.2.2)

section Dict

variable {o : Ops α} {xs : List α} (L : Lawful o xs) {V : Type}

include L

theorem dget_val (x : α) (hx : Nat) (hX : x ∈ xs) (he : o.hash x = .ok hx) :
    ∀ m : DictO α V, Good o xs m → dget o x hx m = .ok ((proj o xs m).lookup (cls o xs x)) := by
  intro m
  induction m with
  | nil => intro _; rfl
  | cons p r ih =>
    intro hg
    obtain ⟨k, h, v⟩ := p
    obtain ⟨g1, g2⟩ := hg (k, h, v) (by simp)
    have hr := ih (fun e he => hg e (by simp [he]))
    simp only at g1 g2
    simp only [dget, keyIs_val L k x h hx g1 hX g2 he, proj, List.map_cons, List.lookup_cons]
    by_cases hc : cls o xs k = cls o xs x
    · simp [hc]
    · have h1 : (cls o xs k == cls o xs x) = false := by simpa using hc
      have h2 : (cls o xs x == cls o xs k) = false := by simpa using Ne.symm hc
      simp only [h1, h2]
      exact hr

theorem scontains_val (x : α) (hx : Nat) (hX : x ∈ xs) (he : o.hash x = .ok hx) :
    ∀ m : SetO α, (∀ e ∈ m, e.1 ∈ xs ∧ o.hash e.1 = .ok e.2) →
      scontains o x hx m = .ok ((m.map fun e => cls o xs e.1).contains (cls o xs x)) := by
  intro m
  induction m with
  | nil => intro _; rfl
  | cons p r ih =>
    intro hg
    obtain ⟨k, h⟩ := p
    obtain ⟨g1, g2⟩ := hg (k, h) (by simp)
    have hr := ih (fun e he => hg e (by simp [he]))
    simp only at g1 g2
    simp only [scontains, keyIs_val L k x h hx g1 hX g2 he, List.map_cons, List.contains_cons]
    by_cases hc : cls o xs k = cls o xs x
    · simp [hc]
    · have h1 : (cls o xs k == cls o xs x) = false := by simpa using hc
      have h2 : (cls o xs x == cls o xs k) = false := by simpa using Ne.symm hc
      simp only [h1, h2, Bool.false_or]
      exact hr

/-- `d[x] = f(old)` on lawful keys cannot fail, and acts on the classes. -/
theorem dput_val (x : α) (hx : Nat) (hX : x ∈ xs) (he : o.hash x = .ok hx) (f : Option V → V) :
    ∀ m : DictO α V, Good o xs m → ∃ m', dput o x hx f m = .ok m' ∧ Good o xs m' ∧
      (∀ n, (proj o xs m').lookup n =
        if n = cls o xs x then some (f ((proj o xs m).lookup (cls o xs x))) else (proj o xs m).lookup n) := by
  intro m
  induction m with
  | nil =>
    intro _
    refine ⟨_, rfl, ?_, ?_⟩
    · intro e hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      subst hm
      exact ⟨hX, he⟩
    · intro n
      by_cases h : n = cls o xs x
      · simp [proj, List.lookup_cons, h]
      · have h2 : (n == cls o xs x) = false := by simpa using h
        simp [proj, List.lookup_cons, h, h2]
  | cons p r ih =>
    intro hg
    obtain ⟨k, h, v⟩ := p
    obtain ⟨g1, g2⟩ := hg (k, h, v) (by simp)
    simp only at g1 g2
    obtain ⟨m', h1, h2, h3⟩ := ih (fun e he => hg e (by simp [he]))
    by_cases hc : cls o xs k = cls o xs x
    · have hb : (cls o xs k == cls o xs x) = true := by simp [hc]
      refine ⟨(k, h, f (some v)) :: r, by simp only [dput, keyIs_val L k x h hx g1 hX g2 he, hb], ?_, ?_⟩
      · intro e hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact ⟨g1, g2⟩
        · exact hg e (by simp [hm])
      · intro n
        by_cases hn : n = cls o xs x
        · subst hn
          simp [proj, List.lookup_cons, hc]
        · have h5 : (n == cls o xs k) = false := by simpa [hc] using hn
          have h6 : (n == cls o xs x) = false := by simpa using hn
          simp [proj, List.lookup_cons, hc, hn, h5, h6]
    · have hb : (cls o xs k == cls o xs x) = false := by simpa using hc
      refine ⟨(k, h, v) :: m', by simp only [dput, keyIs_val L k x h hx g1 hX g2 he, hb, h1], ?_, ?_⟩
      · intro e hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact ⟨g1, g2⟩
        · exact h2 e hm
      · intro n
        have hx2 : (cls o xs x == cls o xs k) = false := by simpa using Ne.symm hc
        by_cases hn : n = cls o xs k
        · subst hn
          simp [proj, List.lookup_cons, hc]
        · have h4 := h3 n
          have h5 : (n == cls o xs k) = false := by simpa using hn
          simp only [proj, List.map_cons, List.lookup_cons, h5, hx2] at h4 ⊢
          exact h4

/-- `b2j.setdefault(elt, []).append(i)` on lawful keys is `addIdx` on the classes. -/
theorem addIdx_val (x : α) (hx i : Nat) (hX : x ∈ xs) (he : o.hash x = .ok hx) :
    ∀ m : DictO α (List Nat), Good o xs m → ∃ m', dput o x hx (fun v => v.getD [] ++ [i]) m = .ok m' ∧ Good o xs m' ∧
      proj o xs m' = addIdx (proj o xs m) (cls o xs x) i := by
  intro m
  induction m with
  | nil =>
    intro _
    refine ⟨_, rfl, ?_, rfl⟩
    intro e hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm
    exact ⟨hX, he⟩
  | cons p r ih =>
    intro hg
    obtain ⟨k, h, v⟩ := p
    obtain ⟨g1, g2⟩ := hg (k, h, v) (by simp)
    simp only at g1 g2
    obtain ⟨m', h1, h2, h3⟩ := ih (fun e he => hg e (by simp [he]))
    by_cases hc : cls o xs k = cls o xs x
    · have hb : (cls o xs k == cls o xs x) = true := by simp [hc]
      refine ⟨(k, h, v ++ [i]) :: r, by simp [dput, keyIs_val L k x h hx g1 hX g2 he, hb], ?_, ?_⟩
      · intro e hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact ⟨g1, g2⟩
        · exact hg e (by simp [hm])
      · simp [proj, addIdx, hc]
    · have hb : (cls o xs k == cls o xs x) = false := by simpa using hc
      refine ⟨(k, h, v) :: m', by simp only [dput, keyIs_val L k x h hx g1 hX g2 he, hb, h1], ?_, ?_⟩
      · intro e hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact ⟨g1, g2⟩
        · exact h2 e hm
      · have e : proj o xs ((k, h, v) :: m') = (cls o xs k, v) :: proj o xs m' := rfl
        have e2 : proj o xs ((k, h, v) :: r) = (cls o xs k, v) :: proj o xs r := rfl
        rw [e, e2, h3, addIdx]
        simp [hc]

theorem build_val : ∀ (b : List α) (i : Nat) (m : DictO α (List Nat)), (∀ x ∈ b, x ∈ xs) → Good o xs m →
    (buildO o b i m).2 = .ok () ∧ Good o xs (buildO o b i m).1 ∧
      proj o xs (buildO o b i m).1 =
        ((b.map (cls o xs)).zipIdx i).foldl (fun m p => addIdx m p.1 p.2) (proj o xs m) := by
  intro b
  induction b with
  | nil => intro i m _ hg; exact ⟨rfl, hg, rfl⟩
  | cons x r ih =>
    intro i m hb hg
    have hX := hb x (by simp)
    obtain ⟨hx, he⟩ := L.hash_ok x hX
    obtain ⟨m', h1, h2, h3⟩ := addIdx_val L x hx i hX he m hg
    have hr := ih (i + 1) m' (fun y hy => hb y (by simp [hy])) h2
    simp only [buildO, he, h1, List.map_cons, List.zipIdx_cons, List.foldl_cons, Nat.add_comm 1 i]
    rw [← h3]
    simpa using hr

end Dict

/-- `__chain_b` leaves `opcodes` and `fullbcount` as it found them. -/
theorem chainBO_fields (o : Ops α) (s s' : SMO α) (r : Py Unit) (h : chainBO o s = (s', r)) :
    s'.opcodes = s.opcodes ∧ s'.fullb = s.fullb ∧ s'.isjunk = s.isjunk ∧ s'.autojunk = s.autojunk := by
  simp only [chainBO] at h
  split at h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · split at h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨rfl, rfl, rfl, rfl⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨rfl, rfl, rfl, rfl⟩

/-! ### Keys are distinct -/

def keysOf {V : Type} (m : List (Nat × V)) : List Nat := m.map (·.1)

theorem addIdx_sub (e i : Nat) : ∀ (m : List (Nat × List Nat)) (k : Nat), k ∈ keysOf (addIdx m e i) → k = e ∨ k ∈ keysOf m := by
  intro m
  induction m with
  | nil => intro k h; simpa [addIdx, keysOf] using h
  | cons p r ih =>
    intro k h
    obtain ⟨a, v⟩ := p
    simp only [addIdx] at h
    split at h
    · right
      simpa [keysOf] using h
    · simp only [keysOf, List.map_cons, List.mem_cons] at h ⊢
      rcases h with h | h
      · exact Or.inr (Or.inl h)
      · rcases ih k h with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)

theorem addIdx_nodup (e i : Nat) : ∀ m : List (Nat × List Nat), (keysOf m).Nodup → (keysOf (addIdx m e i)).Nodup := by
  intro m
  induction m with
  | nil => intro _; simp [addIdx, keysOf]
  | cons p r ih =>
    intro h
    obtain ⟨a, v⟩ := p
    simp only [keysOf, List.map_cons, List.nodup_cons] at h
    simp only [addIdx]
    split
    · simpa [keysOf] using h
    · rename_i hne
      simp only [keysOf, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih h.2⟩
      intro hm
      rcases addIdx_sub e i r a hm with h1 | h1
      · exact hne (by simpa using h1)
      · exact h.1 h1

theorem foldl_nodup : ∀ (l : List (Nat × Nat)) (m : List (Nat × List Nat)), (keysOf m).Nodup →
    (keysOf (l.foldl (fun m p => addIdx m p.1 p.2) m)).Nodup := by
  intro l
  induction l with
  | nil => intro m h; exact h
  | cons p r ih =>
    intro m h
    exact ih _ (addIdx_nodup _ _ _ h)

theorem find_key (ρ : α → Nat) {V : Type} : ∀ (m : DictO α V), (keysOf (m.map fun e => (ρ e.1, e.2.2))).Nodup → ∀ e ∈ m,
    m.find? (fun e' => ρ e'.1 == ρ e.1) = some e := by
  intro m
  induction m with
  | nil => intro _ e h; simp at h
  | cons p r ih =>
    intro hn e he
    simp only [keysOf, List.map_map, List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp he with rfl | he'
    · simp
    · have h1 : ρ p.1 ≠ ρ e.1 := by
        intro h
        apply hn.1
        simp only [List.mem_map]
        exact ⟨e, he', by simp [h]⟩
      have h2 : (ρ p.1 == ρ e.1) = false := by simpa using h1
      simp only [List.find?_cons, h2]
      exact ih (by simpa [keysOf, List.map_map] using hn.2) e he'

/-! ### `isjunk` -/

/-- `isjunk` on classes: the key of the class in the dict decides. -/
def juF (ρ : α → Nat) (f : α → Py Bool) (full : DictO α (List Nat)) (n : Nat) : Py Bool :=
  match full.find? (fun e => ρ e.1 == n) with
  | some e => f e.1
  | none => .ok false

theorem junk_val (ρ : α → Nat) (F : Nat → Py Bool) (f : α → Py Bool) : ∀ r : DictO α (List Nat), (∀ e ∈ r, F (ρ e.1) = f e.1) →
    (junkOf F (r.map fun e => (ρ e.1, e.2.2))).1 = (junkO f r).2.1.map (fun e => ρ e.1) ∧
      (junkOf F (r.map fun e => (ρ e.1, e.2.2))).2 = (junkO f r).2.2 := by
  intro r
  induction r with
  | nil => intro _; exact ⟨rfl, rfl⟩
  | cons p r ih =>
    intro h
    obtain ⟨k, hh, v⟩ := p
    have h0 := h (k, hh, v) (by simp)
    simp only at h0
    obtain ⟨h1, h2⟩ := ih (fun e he => h e (by simp [he]))
    simp only [List.map_cons, junkOf, junkO, h0]
    cases hf : f k with
    | error e => exact ⟨rfl, rfl⟩
    | ok b =>
      cases b with
      | true => simp [h1, h2]
      | false => exact ⟨h1, h2⟩

theorem junk_sub (F : Nat → Py Bool) : ∀ (r : List (Nat × List Nat)) (x : Nat), x ∈ (junkOf F r).1 → x ∈ keysOf r := by
  intro r
  induction r with
  | nil => intro x h; simp [junkOf] at h
  | cons p r ih =>
    intro x h
    obtain ⟨k, v⟩ := p
    simp only [junkOf] at h
    split at h
    · simp at h
    · simp only [List.mem_cons] at h
      simp only [keysOf, List.map_cons, List.mem_cons]
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (ih x h)
    · simp only [keysOf, List.map_cons, List.mem_cons]
      exact Or.inr (ih x h)

theorem junk_filter (ρ : α → Nat) (f : α → Py Bool) (F : Nat → Py Bool) : ∀ r : DictO α (List Nat),
    (∀ e ∈ r, F (ρ e.1) = f e.1) → (keysOf (r.map fun e => (ρ e.1, e.2.2))).Nodup → (junkO f r).2.2 = .ok () →
    (r.map fun e => (ρ e.1, e.2.2)).filter (fun p => !(junkOf F (r.map fun e => (ρ e.1, e.2.2))).1.contains p.1) =
      (junkO f r).1.map fun e => (ρ e.1, e.2.2) := by
  intro r
  induction r with
  | nil => intro _ _ _; rfl
  | cons p r ih =>
    intro h hn hok
    obtain ⟨k, hh, v⟩ := p
    have h0 := h (k, hh, v) (by simp)
    simp only at h0
    have hR : ∀ e ∈ r, F (ρ e.1) = f e.1 := fun e he => h e (by simp [he])
    simp only [keysOf, List.map_cons, List.nodup_cons] at hn
    have hN : (keysOf (r.map fun e => (ρ e.1, e.2.2))).Nodup := hn.2
    have hk : ρ k ∉ keysOf (r.map fun e => (ρ e.1, e.2.2)) := hn.1
    cases hf : f k with
    | error e =>
      simp only [junkO, hf] at hok
      cases hok
    | ok b =>
      cases b with
      | true =>
        simp only [junkO, hf] at hok
        have ih' := ih hR hN hok
        simp only [List.map_cons, junkOf, h0, hf, junkO]
        have hc : ((ρ k, v).1 :: (junkOf F (r.map fun e => (ρ e.1, e.2.2))).1).contains (ρ k) = true := by simp
        rw [List.filter_cons_of_neg (by simp)]
        rw [← ih']
        apply List.filter_congr
        intro q hq
        have hne : q.1 ≠ ρ k := by
          intro e
          apply hk
          rw [← e]
          exact List.mem_map_of_mem hq
        simp [hne]
      | false =>
        simp only [junkO, hf] at hok
        have ih' := ih hR hN hok
        simp only [List.map_cons, junkOf, h0, hf, junkO]
        have hc : (junkOf F (r.map fun e => (ρ e.1, e.2.2))).1.contains (ρ k) = false := by
          have : ρ k ∉ (junkOf F (r.map fun e => (ρ e.1, e.2.2))).1 := fun hm => hk (junk_sub F _ _ hm)
          cases hd : (junkOf F (r.map fun e => (ρ e.1, e.2.2))).1.contains (ρ k) with
          | false => rfl
          | true => exact absurd (List.contains_iff_mem.mp hd) this
        have hp : (!(junkOf F (r.map fun e => (ρ e.1, e.2.2))).1.contains (ρ k)) = true := by rw [hc]; rfl
        have e := List.filter_cons_of_pos (p := fun (p : Nat × List Nat) => !(junkOf F (r.map fun e => (ρ e.1, e.2.2))).1.contains p.1)
          (a := (ρ k, v)) (l := r.map fun e => (ρ e.1, e.2.2)) hp
        rw [e, ih']

theorem nodup_key {V : Type} : ∀ l : List (Nat × V), (keysOf l).Nodup → ∀ p ∈ l, ∀ p' ∈ l, p.1 = p'.1 → p = p' := by
  intro l
  induction l with
  | nil => intro _ p h; simp at h
  | cons x r ih =>
    intro hn p hp p' hp' he
    simp only [keysOf, List.map_cons, List.nodup_cons] at hn
    have hx : ∀ q ∈ r, q.1 ≠ x.1 := fun q hq e => hn.1 (e ▸ List.mem_map_of_mem hq)
    rcases List.mem_cons.mp hp with rfl | h1
    · rcases List.mem_cons.mp hp' with rfl | h2
      · rfl
      · exact absurd he.symm (hx p' h2)
    · rcases List.mem_cons.mp hp' with rfl | h2
      · exact absurd he (hx p h1)
      · exact ih hn.2 p h1 p' h2 he

/-- Filtering by "is the key among the keys that pass `q`" is filtering by `q`, as keys are distinct. -/
theorem filter_keys {V : Type} (q : Nat × V → Bool) (l : List (Nat × V)) (hn : (keysOf l).Nodup) :
    l.filter (fun p => !((l.filter q).map (·.1)).contains p.1) = l.filter (fun p => !q p) := by
  apply List.filter_congr
  intro p hp
  cases hq : q p with
  | true =>
    have : ((l.filter q).map (·.1)).contains p.1 = true := by
      simp only [List.contains_iff_mem, List.mem_map]
      exact ⟨p, List.mem_filter.mpr ⟨hp, hq⟩, rfl⟩
    simp only [this, hq, Bool.not_true]
  | false =>
    have : ((l.filter q).map (·.1)).contains p.1 = false := by
      cases hc : ((l.filter q).map (·.1)).contains p.1 with
      | false => rfl
      | true =>
        simp only [List.contains_iff_mem, List.mem_map] at hc
        obtain ⟨p', h1, h2⟩ := hc
        obtain ⟨h3, h4⟩ := List.mem_filter.mp h1
        rw [nodup_key l hn p' h3 p hp h2, hq] at h4
        cases h4
    simp only [this, hq, Bool.not_false]

theorem junkO_kept (f : α → Py Bool) : ∀ (r : DictO α (List Nat)) (e), e ∈ (junkO f r).1 → e ∈ r := by
  intro r
  induction r with
  | nil => intro e h; simpa [junkO] using h
  | cons p r ih =>
    intro e h
    obtain ⟨k, hh, v⟩ := p
    simp only [junkO] at h
    split at h
    · simp at h
    · exact List.mem_cons_of_mem _ (ih e h)
    · rcases List.mem_cons.mp h with rfl | h1
      · simp
      · exact List.mem_cons_of_mem _ (ih e h1)

theorem junkO_set (f : α → Py Bool) : ∀ (r : DictO α (List Nat)) (e), e ∈ (junkO f r).2.1 → ∃ v, (e.1, e.2, v) ∈ r := by
  intro r
  induction r with
  | nil => intro e h; simp [junkO] at h
  | cons p r ih =>
    intro e h
    obtain ⟨k, hh, v⟩ := p
    simp only [junkO] at h
    split at h
    · simp at h
    · rcases List.mem_cons.mp h with rfl | h1
      · exact ⟨v, by simp⟩
      · obtain ⟨w, hw⟩ := ih e h1
        exact ⟨w, List.mem_cons_of_mem _ hw⟩
    · obtain ⟨w, hw⟩ := ih e h
      exact ⟨w, List.mem_cons_of_mem _ hw⟩

/-! ### The matcher -/

/-- The object matcher `s` and the matcher `t` on the classes of its elements hold the same things. -/
structure Sim (o : Ops α) (xs : List α) (s : SMO α) (t : SM) : Prop where
  ha : ∀ x ∈ s.a, x ∈ xs
  hb : ∀ x ∈ s.b, x ∈ xs
  a : t.a = s.a.map (cls o xs)
  b : t.b = s.b.map (cls o xs)
  b2j : t.b2j = proj o xs s.b2j
  good : Good o xs s.b2j
  junk : t.bjunk = s.bjunk.map fun e => cls o xs e.1
  goodJ : ∀ e ∈ s.bjunk, e.1 ∈ xs ∧ o.hash e.1 = .ok e.2
  blocks : t.blocks = s.blocks

theorem at_map (ρ : α → Nat) (l : List α) (i : Nat) :
    at? (l.map ρ) i = match atO l i with
      | .ok x => .ok (ρ x)
      | .error e => .error e := by
  simp only [at?, atO, List.getElem?_map]
  cases l[i]? <;> rfl

theorem atO_mem (l : List α) (i : Nat) (x : α) (h : atO l i = .ok x) : x ∈ l := by
  simp only [atO] at h
  cases hl : l[i]? with
  | none =>
    rw [hl] at h
    cases h
  | some y =>
    rw [hl] at h
    simp only [Except.ok.injEq] at h
    subst h
    exact List.mem_of_getElem? hl

section Run

variable {o : Ops α} {xs : List α} (L : Lawful o xs) {s : SMO α} {t : SM} (S : Sim o xs s t)

include L S

theorem outer_val (blo bhi ahi : Nat) : ∀ (f i : Nat) (j : List (Nat × Nat)) (best : Best),
    outerO o s blo bhi ahi f i j best = outerLoop t blo bhi ahi f i j best := by
  intro f
  induction f with
  | zero => intro _ _ _; rfl
  | succ f ih =>
    intro i j best
    simp only [outerO, outerLoop]
    rw [S.a, at_map]
    cases hx : atO s.a i with
    | error e => rfl
    | ok x =>
      have hX := S.ha x (atO_mem _ _ _ hx)
      obtain ⟨h, he⟩ := L.hash_ok x hX
      simp only [he, dget_val L x h hX he _ S.good, lookupIdx, S.b2j]
      exact ih _ _ _

theorem extTest_val (junk : Bool) (ia ib : Nat) : extTestO o s junk ia ib = extTest t junk ia ib := by
  simp only [extTestO, extTest]
  rw [S.b, at_map]
  cases hy : atO s.b ib with
  | error e => rfl
  | ok y =>
    have hY := S.hb y (atO_mem _ _ _ hy)
    obtain ⟨h, he⟩ := L.hash_ok y hY
    simp only [he, scontains_val L y h hY he _ S.goodJ, S.junk]
    split
    · rfl
    · rw [S.a, at_map]
      cases hx : atO s.a ia with
      | error e => rfl
      | ok x =>
        exact eq_val L x y (S.ha x (atO_mem _ _ _ hx)) hY

theorem extL_val (junk : Bool) (alo blo : Nat) : ∀ (f : Nat) (b : Best),
    extendLeftO o s junk alo blo f b = extendLeft t junk alo blo f b := by
  intro f
  induction f with
  | zero => intro _; rfl
  | succ f ih =>
    intro b
    obtain ⟨i, j, k⟩ := b
    simp only [extendLeftO, extendLeft, extTest_val L S]
    split
    · cases extTest t junk (i - 1) (j - 1) with
      | error e => rfl
      | ok c =>
        cases c with
        | true => exact ih _
        | false => rfl
    · rfl

theorem extR_val (junk : Bool) (ahi bhi : Nat) : ∀ (f : Nat) (b : Best),
    extendRightO o s junk ahi bhi f b = extendRight t junk ahi bhi f b := by
  intro f
  induction f with
  | zero => intro _; rfl
  | succ f ih =>
    intro b
    obtain ⟨i, j, k⟩ := b
    simp only [extendRightO, extendRight, extTest_val L S]
    split
    · cases extTest t junk (i + k) (j + k) with
      | error e => rfl
      | ok c =>
        cases c with
        | true => exact ih _
        | false => rfl
    · rfl

theorem find_val (alo ahi blo bhi : Nat) : findLongestO o s alo ahi blo bhi = findLongest t alo ahi blo bhi := by
  simp only [findLongestO, findLongest]
  rw [outer_val L S]
  cases outerLoop t blo bhi ahi (ahi - alo) alo [] (alo, blo, 0) with
  | error e => rfl
  | ok b =>
    simp only
    rw [extL_val L S]
    cases extendLeft t false alo blo (ahi + bhi + 1) b with
    | error e => rfl
    | ok b =>
      simp only
      rw [extR_val L S]
      cases extendRight t false ahi bhi (ahi + bhi + 1) b with
      | error e => rfl
      | ok b =>
        simp only
        rw [extL_val L S]
        cases extendLeft t true alo blo (ahi + bhi + 1) b with
        | error e => rfl
        | ok b => exact extR_val L S _ _ _ _ _

theorem blockLoop_val : ∀ (f : Nat) (q : List Box) (found : List T),
    blockLoopO o s f q found = blockLoop t f q found := by
  intro f
  induction f with
  | zero => intro _ _; rfl
  | succ f ih =>
    intro q found
    cases q with
    | nil => rfl
    | cons b q =>
      obtain ⟨alo, ahi, blo, bhi⟩ := b
      simp only [blockLoopO, blockLoop, find_val L S]
      cases findLongest t alo ahi blo bhi with
      | error e => rfl
      | ok r =>
        obtain ⟨i, j, k⟩ := r
        simp only
        split
        · exact ih _ _
        · exact ih _ _

theorem blocks_val {t' : SM} {bs : List T} (h : getBlocks t = .ok (t', bs)) :
    ∃ s', getBlocksO o s = .ok (s', bs) ∧ Sim o xs s' t' := by
  have la : t.a.length = s.a.length := by rw [S.a]; simp
  have lb : t.b.length = s.b.length := by rw [S.b]; simp
  simp only [getBlocks, S.blocks] at h
  simp only [getBlocksO]
  cases hb : s.blocks with
  | some x =>
    simp only [hb, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨s, rfl, S⟩
  | none =>
    simp only [hb, la, lb] at h ⊢
    rw [blockLoop_val L S]
    cases hf : blockLoop t (2 * s.a.length + 2) [(0, s.a.length, 0, s.b.length)] [] with
    | error e =>
      rw [hf] at h
      cases h
    | ok found =>
      rw [hf] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, rfl, S.ha, S.hb, S.a, S.b, S.b2j, S.good, S.junk, S.goodJ, rfl⟩

theorem opcodes_val (h0 : s.opcodes = none) (h1 : t.opcodes = none) {t' : SM} {ops : List Op}
    (h : getOpcodes t = .ok (t', ops)) : ∃ s', getOpcodesO o s = (s', .ok ops) ∧ Sim o xs s' t' := by
  simp only [getOpcodes, h1] at h
  cases hb : getBlocks t with
  | error e =>
    rw [hb] at h
    cases h
  | ok r =>
    obtain ⟨t1, bs⟩ := r
    rw [hb] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have S0 : Sim o xs { s with opcodes := some [] } t :=
      ⟨S.ha, S.hb, S.a, S.b, S.b2j, S.good, S.junk, S.goodJ, S.blocks⟩
    obtain ⟨s1, h2, S1⟩ := blocks_val L S0 hb
    refine ⟨{ s1 with opcodes := some (opLoop bs 0 0) }, ?_, ?_⟩
    · simp only [getOpcodesO, h0, h2]
    · exact ⟨S1.ha, S1.hb, S1.a, S1.b, S1.b2j, S1.good, S1.junk, S1.goodJ, S1.blocks⟩

theorem ratio_val {t' : SM} {m l : Nat} (h : ratioPair t = .ok (t', m, l)) : ∃ s', ratioPairO o s = .ok (s', m, l) := by
  simp only [ratioPair] at h
  cases hb : getBlocks t with
  | error e =>
    rw [hb] at h
    cases h
  | ok r =>
    obtain ⟨t1, bs⟩ := r
    rw [hb] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨s1, h2, S1⟩ := blocks_val L S hb
    refine ⟨s1, ?_⟩
    simp only [ratioPairO, h2, S1.a, S1.b, List.length_map]

end Run

theorem grouped_val {o : Ops α} {s : SMO α} {t : SM} {n : Nat} {s1 : SMO α} {t1 t2 : SM} {ops : List Op} {gs : List (List Op)}
    (h1 : getOpcodesO o s = (s1, .ok ops)) (h2 : getOpcodes t = .ok (t1, ops)) (h : getGrouped t n = .ok (t2, gs)) :
    ∃ s2, getGroupedO o s n = (s2, .ok gs) := by
  simp only [getGrouped, h2, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  refine ⟨(getGroupedO o s n).1, ?_⟩
  simp only [getGroupedO, h1]

section Quick

variable {o : Ops α} {xs : List α} (L : Lawful o xs)

include L

theorem count_val : ∀ (b : List α) (m : DictO α Nat) (F : List (Nat × Nat)), (∀ x ∈ b, x ∈ xs) → Good o xs m →
    (∀ n, (proj o xs m).lookup n = F.lookup n) →
    ∃ m', countO o b m = (m', .ok ()) ∧ Good o xs m' ∧
      ∀ n, (proj o xs m').lookup n = (countB (b.map (cls o xs)) F).lookup n := by
  intro b
  induction b with
  | nil => intro m F _ hg hl; exact ⟨m, rfl, hg, hl⟩
  | cons x r ih =>
    intro m F hb hg hl
    have hX := hb x (by simp)
    obtain ⟨hx, he⟩ := L.hash_ok x hX
    obtain ⟨m1, h1, h2, h3⟩ := dput_val L x hx hX he (fun v => v.getD 0 + 1) m hg
    obtain ⟨m2, h4, h5, h6⟩ := ih m1 ((cls o xs x, (F.lookup (cls o xs x)).getD 0 + 1) :: F)
      (fun y hy => hb y (by simp [hy])) h2 (by
        intro n
        rw [h3 n]
        simp only [hl]
        by_cases hn : n = cls o xs x
        · simp [hn]
        · have : (n == cls o xs x) = false := by simpa using hn
          simp [hn, List.lookup_cons, this])
    exact ⟨m2, by simp only [countO, he, h1, h4], h5, by simpa [countB] using h6⟩

theorem quick_val (full : DictO α Nat) (F : List (Nat × Nat)) (hF : Good o xs full)
    (hl : ∀ n, (proj o xs full).lookup n = F.lookup n) :
    ∀ (a : List α) (avail : DictO α Int) (A : List (Nat × Int)) (m : Nat), (∀ x ∈ a, x ∈ xs) → Good o xs avail →
      (∀ n, (proj o xs avail).lookup n = A.lookup n) →
      quickO o full a avail m = .ok (quickLoop F (a.map (cls o xs)) A m) := by
  intro a
  induction a with
  | nil => intro _ _ _ _ _ _; rfl
  | cons x r ih =>
    intro avail A m hb hg hA
    have hX := hb x (by simp)
    obtain ⟨hx, he⟩ := L.hash_ok x hX
    have h1 : dget o x hx avail = .ok (A.lookup (cls o xs x)) := by
      rw [dget_val L x hx hX he _ hg, hA]
    have h2 : dget o x hx full = .ok (F.lookup (cls o xs x)) := by
      rw [dget_val L x hx hX he _ hF, hl]
    have step : ∀ numb : Int, (match dput o x hx (fun _ => numb - 1) avail with
        | .error er => .error er
        | .ok avail => quickO o full r avail (if numb > 0 then m + 1 else m)) =
        (.ok (quickLoop F (r.map (cls o xs)) ((cls o xs x, numb - 1) :: A) (if numb > 0 then m + 1 else m)) : Py Nat) := by
      intro numb
      obtain ⟨m1, h3, h4, h5⟩ := dput_val L x hx hX he (fun _ => numb - 1) avail hg
      rw [h3]
      refine ih m1 _ _ (fun y hy => hb y (by simp [hy])) h4 ?_
      intro n
      rw [h5 n]
      by_cases hc : n = cls o xs x
      · simp [hc]
      · have : (n == cls o xs x) = false := by simpa using hc
        simp [hc, List.lookup_cons, this, hA]
    simp only [quickO, he, List.map_cons, quickLoop, h1]
    cases hv : A.lookup (cls o xs x) with
    | some v => exact step v
    | none =>
      simp only [h2]
      exact step _

theorem quickPair_val {s : SMO α} {t : SM} (S : Sim o xs s t) (h0 : s.fullb = none) (h1 : t.fullb = none) :
    ∃ s', quickPairO o s = (s', .ok ((quickPair t).2.1, (quickPair t).2.2)) := by
  obtain ⟨m, h2, h3, h4⟩ := count_val L s.b [] [] S.hb (by intro e he; simp at he) (by intro n; rfl)
  have h5 := quick_val L m (countB (s.b.map (cls o xs)) []) h3 h4 s.a [] [] 0 S.ha (by intro e he; simp at he) (by intro n; rfl)
  refine ⟨{ s with fullb := some m }, ?_⟩
  simp only [quickPairO, h0, h2, h5, quickPair, h1, S.a, S.b, List.length_map]

end Quick

/-! ### `__init__` -/

theorem pop_val (ρ : α → Nat) (kept : DictO α (List Nat)) (c : Bool) (t : Nat)
    (hn : (keysOf (kept.map fun e => (ρ e.1, e.2.2))).Nodup) :
    (kept.map fun e => (ρ e.1, e.2.2)).filter (fun p => !(if c = true then
        (((kept.map fun e => (ρ e.1, e.2.2)).filter fun p => decide (p.2.length > t)).map (·.1)) else []).contains p.1) =
      (kept.filter fun e => !(c && decide (e.2.2.length > t))).map fun e => (ρ e.1, e.2.2) := by
  cases c with
  | false =>
    simp only [Bool.false_eq_true, if_false, Bool.false_and, Bool.not_false]
    rw [List.filter_eq_self.mpr (by simp), List.filter_eq_self.mpr (by simp)]
  | true =>
    simp only [if_true, Bool.true_and]
    rw [filter_keys _ _ hn, List.filter_map]
    rfl

section Init

variable {o : Ops α} {xs : List α} (L : Lawful o xs)

include L

theorem chain_val (s0 : SMO α) (T : SM) (hA : ∀ x ∈ s0.a, x ∈ xs) (hB : ∀ x ∈ s0.b, x ∈ xs)
    (ta : T.a = s0.a.map (cls o xs)) (tb : T.b = s0.b.map (cls o xs)) (tauto : T.autojunk = s0.autojunk)
    (tblocks : T.blocks = s0.blocks)
    (tj : T.isjunk = s0.isjunk.map fun f => juF (cls o xs) f (buildO o s0.b 0 []).1)
    (s' : SMO α) (h : chainBO o s0 = (s', .ok ())) :
    ∃ t', chainB T = (t', .ok ()) ∧ Sim o xs s' t' := by
  obtain ⟨b1, g1, p1⟩ := build_val L s0.b 0 [] hB (by intro e he; simp at he)
  generalize hr : buildO o s0.b 0 [] = r at b1 g1 p1 tj
  obtain ⟨full, res⟩ := r
  simp only at b1 g1 p1
  subst b1
  have pB : buildB2j T.b = proj o xs full := by rw [p1, tb]; rfl
  have hnd : (keysOf (proj o xs full)).Nodup := by
    rw [p1]
    exact foldl_nodup _ _ (by simp [keysOf, proj])
  have lenB : T.b.length = s0.b.length := by rw [tb]; simp
  -- the junk step, on both sides
  obtain ⟨kept, js, hjO, hjN, hfilt, hk, hjs⟩ : ∃ (kept : DictO α (List Nat)) (js : SetO α),
      junkStepO s0.isjunk full = (kept, js, .ok ()) ∧
      junkStep T.isjunk (buildB2j T.b) = (js.map (fun e => cls o xs e.1), .ok ()) ∧
      (proj o xs full).filter (fun p => !(js.map fun e => cls o xs e.1).contains p.1) = proj o xs kept ∧
      (∀ e ∈ kept, e ∈ full) ∧ (∀ e ∈ js, ∃ v, (e.1, e.2, v) ∈ full) := by
    cases hj : s0.isjunk with
    | none =>
      rw [hj] at tj
      simp only [Option.map_none] at tj
      refine ⟨full, [], rfl, by simp [tj, junkStep], by simp, fun e he => he, by simp⟩
    | some f =>
      rw [hj] at tj
      simp only [Option.map_some] at tj
      have hF : ∀ e ∈ full, juF (cls o xs) f full (cls o xs e.1) = f e.1 := by
        intro e he
        simp only [juF]
        rw [find_key (cls o xs) full hnd e he]
      obtain ⟨n1, n2⟩ := junk_val (cls o xs) _ f full hF
      have hok : (junkO f full).2.2 = .ok () := by
        simp only [chainBO, hr, hj, junkStepO] at h
        cases hg : (junkO f full).2.2 with
        | error e =>
          rw [hg] at h
          cases h
        | ok u => rfl
      refine ⟨(junkO f full).1, (junkO f full).2.1, ?_, ?_, ?_, junkO_kept f full, junkO_set f full⟩
      · simp only [junkStepO]
        rw [← hok]
      · rw [tj, pB]
        simp only [junkStep]
        have e1 : proj o xs full = full.map fun e => (cls o xs e.1, e.2.2) := rfl
        rw [e1]
        apply Prod.ext
        · exact n1
        · exact n2.trans hok
      · have := junk_filter (cls o xs) f _ full hF hnd hok
        rw [n1] at this
        exact this
  have hnk : (keysOf (proj o xs kept)).Nodup := by
    rw [← hfilt]
    exact List.Nodup.sublist ((List.filter_sublist).map _) hnd
  have hks : Good o xs kept := fun e he => g1 e (hk e he)
  have hc : (T.autojunk && decide (T.b.length ≥ 200)) = (s0.autojunk && decide (s0.b.length ≥ 200)) := by
    rw [tauto, lenB]
  have hpv := pop_val (cls o xs) kept (s0.autojunk && decide (s0.b.length ≥ 200)) (s0.b.length / 100 + 1) hnk
  simp only [chainBO, hr, hjO] at h
  obtain rfl := (Prod.mk.inj h).1
  have hTb : (buildB2j T.b).filter (fun p => !(js.map fun e => cls o xs e.1).contains p.1) = proj o xs kept := by
    rw [pB, hfilt]
  let P : List Nat :=
    if (T.autojunk && decide (T.b.length ≥ 200)) = true then
      ((proj o xs kept).filter fun p => decide (p.2.length > T.b.length / 100 + 1)).map (·.1)
    else []
  have hT : chainB T = (({ T with
      b2j := (proj o xs kept).filter (fun p => !P.contains p.1),
      bjunk := js.map (fun e => cls o xs e.1),
      bpopular := P } : SM), .ok ()) := by
    simp only [chainB, hjN, hTb, P]
  refine ⟨_, hT, hA, hB, ta, tb, ?_, ?_, rfl, ?_, tblocks⟩
  · simp only [P, tauto, lenB]
    exact hpv
  · intro e he
    exact hks e (List.mem_filter.mp he).1
  · intro e he
    obtain ⟨v, hv⟩ := hjs e he
    exact g1 _ hv

end Init

theorem mem_left {a b : List α} {x : α} (h : x ∈ a) : x ∈ a ++ b := List.mem_append_left _ h
theorem mem_right {a b : List α} {x : α} (h : x ∈ b) : x ∈ a ++ b := List.mem_append_right _ h

/-- A new matcher over lawful elements, and the matcher on the classes of its elements. -/
theorem make_sim {o : Ops α} {a b : List α} (L : Lawful o (a ++ b)) (isjunk : Option (α → Py Bool)) (auto : Bool) (s : SMO α)
    (h : makeO o isjunk a b auto = .ok s) :
    ∃ F t, (isjunk = none → F = none) ∧ make F (a.map (cls o (a ++ b))) (b.map (cls o (a ++ b))) auto = .ok t ∧
      Sim o (a ++ b) s t ∧ s.opcodes = none ∧ s.fullb = none := by
  have hc : chainBO o { a, b, isjunk, autojunk := auto, blocks := none, opcodes := none, fullb := none } = (s, .ok ()) := by
    simp only [makeO, setSeq2O, Bool.false_eq_true, if_false] at h
    split at h
    · rename_i s1 he
      simp only [Except.ok.injEq] at h
      subst h
      exact he
    · simp at h
  let F := isjunk.map fun f => juF (cls o (a ++ b)) f (buildO o b 0 []).1
  obtain ⟨t, h1, S⟩ := chain_val L { a, b, isjunk, autojunk := auto, blocks := none, opcodes := none, fullb := none }
    { a := a.map (cls o (a ++ b)), b := b.map (cls o (a ++ b)), isjunk := F, autojunk := auto, blocks := none, opcodes := none, fullb := none }
    (fun _ h => mem_left h) (fun _ h => mem_right h) rfl rfl rfl rfl rfl s hc
  have e : make F (a.map (cls o (a ++ b))) (b.map (cls o (a ++ b))) auto = .ok t := by
    simp only [make, setSeq2, Bool.false_eq_true, if_false, h1]
  have hf : s.opcodes = none ∧ s.fullb = none := by
    have := chainBO_fields o _ s (.ok ()) hc
    exact ⟨this.1, this.2.1⟩
  exact ⟨F, t, (fun h0 => by simp [F, h0]), e, S, hf⟩

end PyLean.TextLibs.Difflib
