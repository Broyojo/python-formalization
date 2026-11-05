import PyLean.CoreLibs.EnumDC.EnumProps

/-!
What `_proto_member.__set_name__` builds, for every class body: an invariant of the tables, kept by each call.
-/

namespace PyLean.CoreLibs.EnumDC

open PyLean

section Lookup

variable {α β : Type} [BEq α] [LawfulBEq α] [DecidableEq α]

theorem lookup_snoc (l : List (α × β)) (a k : α) (v : β) :
    (l ++ [(k, v)]).lookup a = (l.lookup a).or (if a = k then some v else none) := by
  rw [List.lookup_append]
  by_cases h : a = k
  · subst h; simp
  · have hb : (a == k) = false := by simpa using h
    simp [List.lookup_cons, hb, h]

theorem lookup_mem {l : List (α × β)} {a : α} {x : β} (h : l.lookup a = some x) : (a, x) ∈ l := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    obtain ⟨b, w⟩ := y
    by_cases hab : a = b
    · subst hab
      simp at h
      simp [h]
    · have hb : (a == b) = false := by simpa using hab
      simp only [List.lookup_cons, hb] at h
      exact List.mem_cons_of_mem _ (ih h)

end Lookup

/-- The first name of a body with this value: the canonical member, by the docs' "aliases". -/
def canon (s : List (Name × EV)) (v : EV) : Option Name := (s.find? (fun p => p.2 == v)).map Prod.fst

theorem canon_snoc (s : List (Name × EV)) (n : Name) (v x : EV) :
    canon (s ++ [(n, v)]) x = (canon s x).or (if v = x then some n else none) := by
  simp only [canon, List.find?_append, Option.map_or]
  by_cases h : v = x
  · subst h; simp
  · have hb : (v == x) = false := by simpa using h
    simp [List.find?, hb, h]

theorem canon_mem {s : List (Name × EV)} {x : EV} {m : Name} (h : canon s x = some m) : (m, x) ∈ s := by
  simp only [canon, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  have h1 := List.find?_some hp
  have h2 := List.mem_of_find?_eq_some hp
  have : p.2 = x := by simpa using h1
  rw [← this]
  exact h2

theorem canon_of_mem {s : List (Name × EV)} {n : Name} {x : EV} (h : (n, x) ∈ s) : (canon s x).isSome = true := by
  simp only [canon, Option.isSome_map, List.find?_isSome]
  exact ⟨(n, x), h, by simp⟩

/-- The tables after a prefix `s` of the body. -/
structure Inv (c : EClass) (s : List (Name × EV)) : Prop where
  kind : c.kind = .plain
  keys : ∀ n, (c.memberMap.lookup n).isSome = true ↔ n ∈ s.map Prod.fst
  map : ∀ n v, (n, v) ∈ s → c.memberMap.lookup n = canon s v
  vals : ∀ m v, c.valueOf m = some v ↔ canon s v = some m
  hash : ∀ v, v.hashable = true → c.value2member.lookup v = canon s v
  unh : ∀ k l x, (k, l) ∈ c.unhashableMap → x ∈ l → (k, x) ∈ s
  lists : ∀ v, (c.hashableValues.contains v || c.unhashableValues.contains v) = (canon s v).isSome
  names : ∀ m, m ∈ c.memberNames ↔ ∃ v, canon s v = some m
  nodup : c.memberNames.Nodup
  pairs : ∀ n m, (n, m) ∈ c.memberMap → c.memberMap.lookup n = some m

theorem aliasOf_canon {c : EClass} {s : List (Name × EV)} (i : Inv c s) (v : EV) : c.aliasOf v = canon s v := by
  unfold EClass.aliasOf
  split
  · exact i.hash v (by simpa using ‹_›)
  · unfold EClass.findEqual
    cases hc : canon s v with
    | some m =>
      have hv : c.valueOf m = some v := (i.vals m v).2 hc
      have hmem : m ∈ s.map Prod.fst := List.mem_map.2 ⟨(m, v), canon_mem hc, rfl⟩
      have hl : c.memberMap.lookup m = some m := by
        rw [i.map m v (canon_mem hc), hc]
      have hin : (m, m) ∈ c.memberMap := lookup_mem hl
      have hsome : (c.memberMap.find? (fun p => c.valueOf p.2 == some v)).isSome = true :=
        List.find?_isSome.2 ⟨(m, m), hin, by simpa using hv⟩
      cases hf : c.memberMap.find? (fun p => c.valueOf p.2 == some v) with
      | none => simp [hf] at hsome
      | some p =>
        have hp := List.find?_some hf
        have hp' : c.valueOf p.2 = some v := by simpa using hp
        have := (i.vals p.2 v).1 hp'
        rw [hc] at this
        simpa using this.symm
    | none =>
      have : c.memberMap.find? (fun p => c.valueOf p.2 == some v) = none := by
        apply List.find?_eq_none.2
        intro p _ hp
        have hp' : c.valueOf p.2 = some v := by simpa using hp
        have := (i.vals p.2 v).1 hp'
        rw [hc] at this
        simp at this
      simp [this]

theorem mem_appendTo {m : List (Name × List EV)} {n : Name} {v : EV} {k : Name} {l : List EV}
    (h : (k, l) ∈ appendTo m n v) :
    (k, l) ∈ m ∨ (k = n ∧ ((l = [v]) ∨ ∃ old, (k, old) ∈ m ∧ l = old ++ [v])) := by
  induction m with
  | nil =>
    simp only [appendTo, List.mem_singleton, Prod.mk.injEq] at h
    exact .inr ⟨h.1, .inl h.2⟩
  | cons x xs ih =>
    obtain ⟨a, w⟩ := x
    simp only [appendTo] at h
    split at h
    · rename_i hb
      have ha : a = n := by simpa using hb
      rcases List.mem_cons.1 h with h | h
      · simp only [Prod.mk.injEq] at h
        exact .inr ⟨h.1.trans ha, .inr ⟨w, by simp [h.1], h.2⟩⟩
      · exact .inl (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.1 h with h | h
      · exact .inl (by simp [h])
      · rcases ih h with h | ⟨h1, h2⟩
        · exact .inl (List.mem_cons_of_mem _ h)
        · refine .inr ⟨h1, ?_⟩
          rcases h2 with h2 | ⟨old, h3, h4⟩
          · exact .inl h2
          · exact .inr ⟨old, List.mem_cons_of_mem _ h3, h4⟩

theorem noteValue_lists (c : EClass) (n m : Name) (v x : EV) :
    ((c.noteValue n m v).hashableValues.contains x || (c.noteValue n m v).unhashableValues.contains x) =
      (c.hashableValues.contains x || c.unhashableValues.contains x || v == x) := by
  unfold EClass.noteValue
  split
  · simp only
    split
    · rename_i h
      by_cases hx : v = x
      · subst hx
        rw [h]
        simp
      · have : (v == x) = false := by simpa using hx
        simp [this]
    · by_cases hx : v = x
      · subst hx
        simp [List.contains_append]
      · have hxv : x ≠ v := fun e => hx e.symm
        have : (v == x) = false := by simpa using hx
        simp [List.contains_append, hxv, this, List.contains_cons]
  · simp only
    by_cases hx : v = x
    · subst hx
      simp [List.contains_append]
    · have hxv : x ≠ v := fun e => hx e.symm
      have : (v == x) = false := by simpa using hx
      simp [List.contains_append, hxv, this, List.contains_cons]

theorem noteValue_values (c : EClass) (n m : Name) (v : EV) : (c.noteValue n m v).values = c.values := by
  unfold EClass.noteValue; split <;> rfl

theorem noteValue_map (c : EClass) (n m : Name) (v : EV) : (c.noteValue n m v).memberMap = c.memberMap := by
  unfold EClass.noteValue; split <;> rfl

theorem noteValue_names (c : EClass) (n m : Name) (v : EV) : (c.noteValue n m v).memberNames = c.memberNames := by
  unfold EClass.noteValue; split <;> rfl

theorem noteValue_kind (c : EClass) (n m : Name) (v : EV) : (c.noteValue n m v).kind = c.kind := by
  unfold EClass.noteValue; split <;> rfl

theorem noteValue_table (c : EClass) (n m : Name) (v x : EV) (hx : x.hashable = true) :
    (c.noteValue n m v).value2member.lookup x =
      if v.hashable = true then (c.value2member.lookup x).or (if x = v then some m else none)
      else c.value2member.lookup x := by
  unfold EClass.noteValue
  split
  · rename_i h
    simp only [h, ↓reduceIte, setDefault]
    split
    · rename_i hs
      by_cases he : x = v
      · subst he
        cases hl : c.value2member.lookup x with
        | none => simp [hl] at hs
        | some y => simp
      · simp [he]
    · rw [lookup_snoc]
  · rename_i h
    simp [h]

theorem noteValue_unh {c : EClass} {n m : Name} {v : EV} {k : Name} {l : List EV}
    (h : (k, l) ∈ (c.noteValue n m v).unhashableMap) :
    (k, l) ∈ c.unhashableMap ∨ (k = n ∧ ((l = [v]) ∨ ∃ old, (k, old) ∈ c.unhashableMap ∧ l = old ++ [v])) := by
  unfold EClass.noteValue at h
  split at h
  · exact .inl h
  · exact mem_appendTo h

/-- The next member, with a name not in the body so far. -/
theorem setName_inv {c : EClass} {s : List (Name × EV)} (i : Inv c s) (n : Name) (v : EV)
    (hn : n ∉ s.map Prod.fst) :
    ∃ c', c.setName n v = .ok c' ∧ Inv c' (s ++ [(n, v)]) := by
  have hl : c.memberMap.lookup n = none := by
    cases h : c.memberMap.lookup n with
    | none => rfl
    | some y =>
      have := (i.keys n).1 (by simp [h])
      exact absurd this hn
  have hfresh : ∀ x, canon s x ≠ some n := fun x h =>
    hn (List.mem_map.2 ⟨(n, x), canon_mem h, rfl⟩)
  have hflag : c.flagUpdate v = c := by
    simp only [EClass.flagUpdate, i.kind]
  have hvalue : memberValue c.kind v = .ok v := by
    simp only [i.kind, memberValue]
  have keys' : ∀ x, x ∈ (s ++ [(n, v)]).map Prod.fst ↔ x ∈ s.map Prod.fst ∨ x = n := by
    intro x; simp
  have unh' : ∀ (c1 : EClass) (m : Name), c1.unhashableMap = c.unhashableMap →
      ∀ k l x, (k, l) ∈ (c1.noteValue n m v).unhashableMap → x ∈ l → (k, x) ∈ s ++ [(n, v)] := by
    intro c1 m he k l x h hx
    rcases noteValue_unh h with h1 | ⟨h2, h3⟩
    · rw [he] at h1
      exact List.mem_append_left _ (i.unh k l x h1 hx)
    · rcases h3 with h3 | ⟨old, h4, h5⟩
      · rw [h3] at hx
        simp only [List.mem_singleton] at hx
        rw [hx, h2]
        simp
      · rw [h5] at hx
        rcases List.mem_append.1 hx with hx | hx
        · rw [he] at h4
          exact List.mem_append_left _ (i.unh _ old x h4 hx)
        · simp only [List.mem_singleton] at hx
          rw [hx, h2]
          simp
  cases hc : canon s v with
  | some m0 =>
    -- an alias
    have hcanon : ∀ x, canon (s ++ [(n, v)]) x = canon s x := by
      intro x
      rw [canon_snoc]
      by_cases h : v = x
      · subst h; simp [hc]
      · simp [h]
    let c1 : EClass := { c with memberMap := c.memberMap ++ [(n, m0)] }
    have hset : c.setName n v = .ok (c1.noteValue n m0 v) := by
      simp only [EClass.setName, hvalue, hflag, aliasOf_canon i, hc, EClass.addToMap, hl]
      rfl
    refine ⟨_, hset, ?_⟩
    constructor
    · rw [noteValue_kind]; exact i.kind
    · intro x
      rw [noteValue_map, keys']
      simp only [c1, lookup_snoc]
      by_cases hx : x = n
      · subst hx; simp [hl]
      · simp [hx, i.keys x]
    · intro x w hm
      rw [noteValue_map, hcanon]
      simp only [c1, lookup_snoc]
      rcases List.mem_append.1 hm with hm | hm
      · have hxn : x ≠ n := fun e => hn (e ▸ List.mem_map.2 ⟨(x, w), hm, rfl⟩)
        simp [hxn, i.map x w hm]
      · simp only [List.mem_singleton, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        simp [hl, hc]
    · intro x w
      rw [hcanon, ← i.vals x w]
      simp only [EClass.valueOf, noteValue_values, c1]
    · intro x hx
      rw [hcanon, noteValue_table _ _ _ _ _ hx]
      have hkeep : ∀ (h : v.hashable = true), (c1.value2member.lookup x).or (if x = v then some m0 else none) =
          canon s x := by
        intro hv
        have : c1.value2member.lookup x = canon s x := i.hash x hx
        rw [this]
        by_cases he : x = v
        · subst he; simp [hc]
        · simp [he]
      split
      · exact hkeep ‹_›
      · exact i.hash x hx
    · exact unh' c1 m0 rfl
    · intro x
      rw [noteValue_lists, hcanon]
      have : (c1.hashableValues.contains x || c1.unhashableValues.contains x) = (canon s x).isSome := i.lists x
      rw [this]
      by_cases he : v = x
      · subst he; simp [hc]
      · have : (v == x) = false := by simpa using he
        simp [this]
    · intro x
      rw [noteValue_names]
      simp only [hcanon]
      exact i.names x
    · rw [noteValue_names]; exact i.nodup
    · intro x y hm
      rw [noteValue_map] at hm ⊢
      simp only [c1] at hm ⊢
      rw [lookup_snoc]
      rcases List.mem_append.1 hm with hm | hm
      · simp [i.pairs x y hm]
      · simp only [List.mem_singleton, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        simp [hl]
  | none =>
    -- a new member
    have hcanon : ∀ x, canon (s ++ [(n, v)]) x = if v = x then some n else canon s x := by
      intro x
      rw [canon_snoc]
      by_cases h : v = x
      · subst h; simp [hc]
      · simp [h]
    have hval : c.values.lookup n = none := by
      cases h : c.values.lookup n with
      | none => rfl
      | some w =>
        have : canon s w = some n := (i.vals n w).1 h
        exact absurd this (hfresh w)
    let c1 : EClass := { (c.newMember n v) with memberMap := c.memberMap ++ [(n, n)] }
    have hkeep : keepsName c.kind v = true := by
      simp only [i.kind, keepsName]
    have hset : c.setName n v = .ok (c1.noteValue n n v) := by
      simp only [EClass.setName, hvalue, hflag, aliasOf_canon i, hc]
      simp only [EClass.addToMap]
      have : ((c.newMember n v).memberMap.lookup n) = none := hl
      rw [this]
      rfl
    refine ⟨_, hset, ?_⟩
    constructor
    · rw [noteValue_kind]; exact i.kind
    · intro x
      rw [noteValue_map, keys']
      simp only [c1, lookup_snoc]
      by_cases hx : x = n
      · subst hx; simp [hl]
      · simp [hx, i.keys x]
    · intro x w hm
      rw [noteValue_map, hcanon]
      simp only [c1, lookup_snoc]
      rcases List.mem_append.1 hm with hm | hm
      · have hxn : x ≠ n := fun e => hn (e ▸ List.mem_map.2 ⟨(x, w), hm, rfl⟩)
        have hvw : v ≠ w := by
          intro e
          subst e
          have := canon_of_mem hm
          simp [hc] at this
        simp [hxn, hvw, i.map x w hm]
      · simp only [List.mem_singleton, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        simp [hl]
    · intro x w
      rw [hcanon]
      simp only [EClass.valueOf, noteValue_values, c1, EClass.newMember, lookup_snoc]
      by_cases hx : x = n
      · subst hx
        simp only [hval, Option.none_or, ↓reduceIte, Option.some.injEq]
        by_cases hw : v = w
        · simp [hw]
        · have : w ≠ v := fun e => hw e.symm
          simp [hw, this, hfresh w]
      · have e := i.vals x w
        simp only [EClass.valueOf] at e
        by_cases hw : v = w
        · subst hw
          simp [hx, hc, e, Ne.symm hx]
        · simp [hx, hw, e]
    · intro x hx
      rw [hcanon, noteValue_table _ _ _ _ _ hx]
      have h0 : c1.value2member.lookup x = canon s x := i.hash x hx
      split
      · rw [h0]
        by_cases he : x = v
        · subst he; simp [hc]
        · have : v ≠ x := fun e => he e.symm
          simp [he, this]
      · rename_i hv
        by_cases he : x = v
        · subst he; exact absurd hx hv
        · have : v ≠ x := fun e => he e.symm
          simp [this, h0]
    · exact unh' c1 n rfl
    · intro x
      rw [noteValue_lists, hcanon]
      have : (c1.hashableValues.contains x || c1.unhashableValues.contains x) = (canon s x).isSome := i.lists x
      rw [this]
      by_cases he : v = x
      · subst he; simp [hc]
      · have : (v == x) = false := by simpa using he
        simp [this, he]
    · intro x
      rw [noteValue_names]
      simp only [hcanon, c1, EClass.newMember, hkeep, ↓reduceIte, List.mem_append, List.mem_singleton, i.names x]
      constructor
      · rintro (⟨w, hw⟩ | rfl)
        · refine ⟨w, ?_⟩
          by_cases he : v = w
          · subst he; simp [hc] at hw
          · simp [he, hw]
        · exact ⟨v, by simp⟩
      · rintro ⟨w, hw⟩
        by_cases he : v = w
        · simp only [he, ↓reduceIte, Option.some.injEq] at hw
          exact .inr hw.symm
        · simp only [he, ↓reduceIte] at hw
          exact .inl ⟨w, hw⟩
    · rw [noteValue_names]
      simp only [c1, EClass.newMember, hkeep, ↓reduceIte]
      refine List.nodup_append.2 ⟨i.nodup, by simp, ?_⟩
      intro x h1 y h2 he
      simp only [List.mem_singleton] at h2
      rw [he, h2] at h1
      obtain ⟨w, hw⟩ := (i.names n).1 h1
      exact hfresh w hw
    · intro x y hm
      rw [noteValue_map] at hm ⊢
      simp only [c1] at hm ⊢
      rw [lookup_snoc]
      rcases List.mem_append.1 hm with hm | hm
      · simp [i.pairs x y hm]
      · simp only [List.mem_singleton, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        simp [hl]

theorem build_inv (rest : List (Name × EV)) :
    ∀ (c : EClass) (s : List (Name × EV)), Inv c s → ((s ++ rest).map Prod.fst).Nodup →
      ∃ c', c.build rest = .ok c' ∧ Inv c' (s ++ rest) := by
  induction rest with
  | nil => intro c s i _; exact ⟨c, rfl, by simpa using i⟩
  | cons p r ih =>
    intro c s i hn
    obtain ⟨n, v⟩ := p
    have hn' : (s.map Prod.fst ++ n :: r.map Prod.fst).Nodup := by simpa using hn
    have hfresh : n ∉ s.map Prod.fst := by
      intro h
      exact (List.nodup_append.1 hn').2.2 n h n (by simp) rfl
    obtain ⟨c1, h1, i1⟩ := setName_inv i n v hfresh
    have hn2 : (((s ++ [(n, v)]) ++ r).map Prod.fst).Nodup := by simpa using hn
    obtain ⟨c2, h2, i2⟩ := ih c1 _ i1 hn2
    refine ⟨c2, ?_, by simpa using i2⟩
    simp only [EClass.build, h1]
    exact h2

theorem inv_empty : Inv ({} : EClass) [] := by
  constructor
  · rfl
  · intro n; simp
  · intro n v h; simp at h
  · intro m v; simp [EClass.valueOf, canon]
  · intro v _; simp [canon]
  · intro k l x h; simp at h
  · intro v; simp [canon]
  · intro m; simp [canon]
  · simp
  · intro n m h; simp at h

theorem found_canon {c : EClass} {s : List (Name × EV)} (i : Inv c s) (v : EV) : c.found v = .ok (canon s v) := by
  unfold EClass.found
  split
  · congr 1
    exact i.hash v (by simpa using ‹_›)
  · unfold EClass.search
    cases hf : c.unhashableMap.find? (fun p => p.2.contains v) with
    | none =>
      simp only
      rw [show c.findEqual v = canon s v from ?_]
      have h := aliasOf_canon i v
      simp only [EClass.aliasOf] at h
      split at h
      · rename_i hh
        exact absurd hh ‹_›
      · exact h
    | some p =>
      have hp := List.find?_some hf
      have hmem := List.mem_of_find?_eq_some hf
      have hx : v ∈ p.2 := by simpa using hp
      have hin : (p.1, v) ∈ s := i.unh p.1 p.2 v hmem hx
      have hl := i.map p.1 v hin
      obtain ⟨m, hm⟩ : ∃ m, canon s v = some m := by
        cases h : canon s v with
        | none =>
          have := canon_of_mem hin
          simp [h] at this
        | some m => exact ⟨m, rfl⟩
      simp only [hl, hm]

/-- What `class C(Enum)` builds, for every body with different names and whatever its values: hashable or not, aliased
or not, `C` is built without an error. Each name goes to the first name with its value, which is what `C[name]` and
`C(value)` return, so that a member comes back from its own value: the round trip of `__reduce_ex__`, and the docs'
"aliases". A value is in the class exactly when a name has it, and the two lookups agree. Two members never share a
value. Iteration, `reversed` and `len` run over `_member_names_`, which has no repeats. -/
def MemberRoundTrip : Prop :=
  ∀ body : List (Name × EV), (body.map Prod.fst).Nodup → ∃ c, ({} : EClass).build body = .ok c ∧
    (∀ n v, (n, v) ∈ body → ∃ m, canon body v = some m ∧ c.getItem n = .ok m ∧ c.valueOf m = some v ∧
      enumNew c none v false .none = .ok m) ∧
    (∀ v m, c.valueOf m = some v → enumContains c false v = true) ∧
    (∀ v, (∀ m, c.valueOf m ≠ some v) → enumContains c false v = false ∧
      (c.memberMap.isEmpty = false → (enumNew c none v false .none).raises "ValueError")) ∧
    (∀ m1 m2 v, c.valueOf m1 = some v → c.valueOf m2 = some v → m1 = m2) ∧
    (∀ m, m ∈ c.memberNames ↔ ∃ v, canon body v = some m) ∧ c.memberNames.Nodup ∧
    c.iter = c.memberNames ∧ c.reversed = c.memberNames.reverse ∧
    (∀ n, (c.memberMap.lookup n).isSome = true ↔ n ∈ body.map Prod.fst)

private theorem filterMap_self (c : EClass) (l : List Name) (h : ∀ m ∈ l, c.memberMap.lookup m = some m) :
    l.filterMap (fun n => c.memberMap.lookup n) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filterMap_cons, h x (by simp)]
    rw [ih (fun m hm => h m (by simp [hm]))]

theorem memberRoundTrip_proven : MemberRoundTrip := by
  intro body hn
  obtain ⟨c, hc, i⟩ := build_inv body {} [] inv_empty (by simpa using hn)
  simp only [List.nil_append] at i
  have hself : ∀ m ∈ c.memberNames, c.memberMap.lookup m = some m := by
    intro m hm
    obtain ⟨v, hv⟩ := (i.names m).1 hm
    rw [i.map m v (canon_mem hv), hv]
  refine ⟨c, hc, ?_, ?_, ?_, ?_, i.names, i.nodup, ?_, ?_, i.keys⟩
  · intro n v hm
    obtain ⟨m, hcm⟩ : ∃ m, canon body v = some m := by
      cases h : canon body v with
      | none =>
        have := canon_of_mem hm
        simp [h] at this
      | some m => exact ⟨m, rfl⟩
    refine ⟨m, hcm, ?_, (i.vals m v).2 hcm, ?_⟩
    · simp [EClass.getItem, i.map n v hm, hcm]
    · simp [enumNew, found_canon i, hcm]
  · intro v m h
    have := (i.vals m v).1 h
    have e := i.lists v
    simp only [this, Option.isSome_some] at e
    simp only [enumContains, Bool.false_or]
    rw [Bool.or_comm]
    exact e
  · intro v h
    have hc0 : canon body v = none := by
      cases hh : canon body v with
      | none => rfl
      | some m => exact absurd ((i.vals m v).2 hh) (h m)
    refine ⟨?_, ?_⟩
    · have e := i.lists v
      simp only [hc0, Option.isSome_none] at e
      simp only [enumContains, Bool.false_or]
      rw [Bool.or_comm]
      exact e
    · intro he
      exact ⟨.valueError "~is not a valid enum value", by simp [enumNew, found_canon i, hc0, he], rfl⟩
  · intro m1 m2 v h1 h2
    have e1 := (i.vals m1 v).1 h1
    have e2 := (i.vals m2 v).1 h2
    rw [e1] at e2
    simpa using e2
  · exact filterMap_self c _ hself
  · simp only [EClass.reversed]
    exact filterMap_self c _ (fun m hm => hself m (by simpa using hm))

/-- `unique`, on a class that does not redefine `name`, is the statement that no two names of the body have the same
value: "Class decorator for enumerations ensuring unique member values". Run on `UniqueNamed` and the invariant. -/
def UniqueIffDistinct : Prop :=
  ∀ (body : List (Name × EV)) (c : EClass), (body.map Prod.fst).Nodup → ({} : EClass).build body = .ok c →
    (c.unique id = .ok () ↔ (body.map Prod.snd).Nodup)

private theorem canon_self_of_nodup {s : List (Name × EV)} (h : (s.map Prod.snd).Nodup) {n : Name} {v : EV}
    (hm : (n, v) ∈ s) : canon s v = some n := by
  induction s with
  | nil => simp at hm
  | cons x xs ih =>
    obtain ⟨a, w⟩ := x
    simp only [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 hm with he | he
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp [canon]
    · have hne : w ≠ v := fun e => h.1 (List.mem_map.2 ⟨(n, v), he, by simp [e]⟩)
      have hb : (w == v) = false := by simpa using hne
      simp only [canon, List.find?_cons, hb]
      exact ih h.2 he

private theorem nodup_of_self {s : List (Name × EV)} (hn : (s.map Prod.fst).Nodup)
    (h : ∀ n v, (n, v) ∈ s → canon s v = some n) : (s.map Prod.snd).Nodup := by
  induction s with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨a, w⟩ := x
    simp only [List.map_cons, List.nodup_cons] at hn ⊢
    refine ⟨?_, ?_⟩
    · intro hw
      obtain ⟨p, hp, hpw⟩ := List.mem_map.1 hw
      obtain ⟨b, u⟩ := p
      simp only at hpw
      subst hpw
      have h1 := h b u (List.mem_cons_of_mem _ hp)
      have h2 := h a u (by simp)
      rw [h1] at h2
      have : b = a := by simpa using h2
      subst this
      exact hn.1 (List.mem_map.2 ⟨(b, u), hp, rfl⟩)
    · apply ih hn.2
      intro b u hm
      have h1 := h b u (List.mem_cons_of_mem _ hm)
      have hne : b ≠ a := fun e => hn.1 (e ▸ List.mem_map.2 ⟨(b, u), hm, rfl⟩)
      by_cases he : w = u
      · subst he
        have h2 := h a w (by simp)
        rw [h2] at h1
        exact absurd (by simpa using h1.symm) hne
      · have hb : (w == u) = false := by simpa using he
        simpa [canon, List.find?_cons, hb] using h1

theorem uniqueIffDistinct_proven : UniqueIffDistinct := by
  intro body c hn hb
  obtain ⟨c', hc', i⟩ := build_inv body {} [] inv_empty (by simpa using hn)
  simp only [List.nil_append] at i
  have hcc : c = c' := by
    rw [hb] at hc'
    simpa using hc'
  subst hcc
  rw [(uniqueNamed_proven c).1]
  constructor
  · intro h
    apply nodup_of_self hn
    intro n v hm
    have hl := i.map n v hm
    cases hc : canon body v with
    | none =>
      have := canon_of_mem hm
      simp [hc] at this
    | some m =>
      rw [hc] at hl
      have := h (n, m) (lookup_mem hl)
      simp only at this
      rw [this]
  · intro h p hp
    obtain ⟨n, m⟩ := p
    have hl := i.pairs n m hp
    have hk := (i.keys n).1 (by simp [hl])
    obtain ⟨⟨a, v⟩, hmem, he⟩ := List.mem_map.1 hk
    simp only at he
    subst he
    have h1 := i.map a v hmem
    rw [canon_self_of_nodup h hmem, hl] at h1
    simpa using h1.symm

/-! ### `Flag` masks -/

theorem noteValue_masks (c : EClass) (n m : Name) (v : EV) :
    (c.noteValue n m v).flagMask = c.flagMask ∧ (c.noteValue n m v).singlesMask = c.singlesMask ∧
      (c.noteValue n m v).allBits = c.allBits := by
  unfold EClass.noteValue; split <;> exact ⟨rfl, rfl, rfl⟩

private theorem flag_step (c : EClass) (n : Name) (v : Nat) (hk : c.kind = .flag)
    (hl : c.memberMap.lookup n = none) :
    ∃ c', c.setName n (.atom (.int (v : Int))) = .ok c' ∧ c'.kind = .flag ∧ c'.flagMask = c.flagMask ||| v ∧
      c'.singlesMask = (if isSingleBit v then c.singlesMask ||| v else c.singlesMask) ∧
      c'.allBits = 2 ^ bitLength (c.flagMask ||| v) - 1 ∧
      ∀ x, (c'.memberMap.lookup x).isSome = true ↔ (c.memberMap.lookup x).isSome = true ∨ x = n := by
  obtain ⟨c1, hd⟩ : ∃ c1, c1 = c.flagUpdate (.atom (.int (v : Int))) := ⟨_, rfl⟩
  have hc1 : c1.flagMask = c.flagMask ||| v ∧
      c1.singlesMask = (if isSingleBit v then c.singlesMask ||| v else c.singlesMask) ∧
      c1.allBits = 2 ^ bitLength (c.flagMask ||| v) - 1 ∧ c1.memberMap = c.memberMap ∧ c1.kind = .flag := by
    simp [hd, EClass.flagUpdate, hk]
  obtain ⟨a1, a2, a3, a4, a5⟩ := hc1
  have hval : memberValue c.kind (.atom (.int (v : Int))) = .ok (.atom (.int (v : Int))) := by
    simp [hk, memberValue]
  have hkeys : ∀ (l : List (Name × Name)) (k x : Name), l.lookup n = none →
      (((l ++ [(n, k)]).lookup x).isSome = true ↔ (l.lookup x).isSome = true ∨ x = n) := by
    intro l k x hh
    rw [lookup_snoc]
    by_cases hx : x = n
    · subst hx; simp [hh]
    · simp [hx]
  cases ha : c1.aliasOf (.atom (.int (v : Int))) with
  | some m =>
    refine ⟨({ c1 with memberMap := c1.memberMap ++ [(n, m)] }).noteValue n m (.atom (.int (v : Int))), ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · have : c1.addToMap n m = .ok { c1 with memberMap := c1.memberMap ++ [(n, m)] } := by
        simp [EClass.addToMap, a4, hl]
      simp only [EClass.setName, hval, ← hd, ha, this]
    · rw [noteValue_kind]; exact a5
    · rw [(noteValue_masks _ _ _ _).1]; exact a1
    · rw [(noteValue_masks _ _ _ _).2.1]; exact a2
    · rw [(noteValue_masks _ _ _ _).2.2]; exact a3
    · intro x
      rw [noteValue_map]
      simp only [a4]
      exact hkeys _ _ x hl
  | none =>
    obtain ⟨c2, hd2⟩ : ∃ c2, c2 = c1.newMember n (.atom (.int (v : Int))) := ⟨_, rfl⟩
    have b1 : c2.memberMap = c.memberMap := by rw [hd2]; exact a4
    have b2 : c2.flagMask = c1.flagMask ∧ c2.singlesMask = c1.singlesMask ∧ c2.allBits = c1.allBits ∧
        c2.kind = c1.kind := by
      rw [hd2]
      exact ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨({ c2 with memberMap := c2.memberMap ++ [(n, n)] }).noteValue n n (.atom (.int (v : Int))), ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · have : c2.addToMap n n = .ok { c2 with memberMap := c2.memberMap ++ [(n, n)] } := by
        simp [EClass.addToMap, b1, hl]
      simp only [EClass.setName, hval, ← hd, ha, ← hd2, this]
    · rw [noteValue_kind]; exact b2.2.2.2.trans a5
    · rw [(noteValue_masks _ _ _ _).1]; exact b2.1.trans a1
    · rw [(noteValue_masks _ _ _ _).2.1]; exact b2.2.1.trans a2
    · rw [(noteValue_masks _ _ _ _).2.2]; exact b2.2.2.1.trans a3
    · intro x
      rw [noteValue_map]
      simp only [b1]
      exact hkeys _ _ x hl

private theorem flag_build (rest : List (String × Nat)) :
    ∀ (c : EClass) (seen : List Name), c.kind = .flag → c.allBits = 2 ^ bitLength c.flagMask - 1 →
      (∀ x, (c.memberMap.lookup x).isSome = true → x ∈ seen) →
      (seen ++ rest.map (fun p => p.1.toList)).Nodup →
      ∃ c', c.build (rest.map (fun p => (p.1.toList, .atom (.int (p.2 : Int))))) = .ok c' ∧
        c'.flagMask = rest.foldl (fun m p => m ||| p.2) c.flagMask ∧
        c'.singlesMask = rest.foldl (fun m p => if isSingleBit p.2 then m ||| p.2 else m) c.singlesMask ∧
        c'.allBits = 2 ^ bitLength c'.flagMask - 1 := by
  induction rest with
  | nil => intro c _ _ h _ _; exact ⟨c, rfl, rfl, rfl, h⟩
  | cons p r ih =>
    intro c seen hk ha hs hn
    obtain ⟨name, v⟩ := p
    simp only [List.map_cons, List.foldl_cons]
    have hn' := List.nodup_append.1 (by simpa using hn : (seen ++ name.toList :: r.map (fun p => p.1.toList)).Nodup)
    have hfresh : name.toList ∉ seen := fun h => hn'.2.2 _ h _ (by simp) rfl
    have hl : c.memberMap.lookup name.toList = none := by
      cases h : c.memberMap.lookup name.toList with
      | none => rfl
      | some y => exact absurd (hs _ (by simp [h])) hfresh
    obtain ⟨c1, h1, k1, m1, s1, b1, l1⟩ := flag_step c name.toList v hk hl
    obtain ⟨c2, h2, m2, s2, b2⟩ := ih c1 (seen ++ [name.toList]) k1 (by rw [b1, m1]) (by
      intro x hx
      rcases (l1 x).1 hx with h | h
      · exact List.mem_append_left _ (hs x h)
      · simp [h]) (by simpa using hn)
    refine ⟨c2, ?_, ?_, ?_, b2⟩
    · simp only [EClass.build, h1]
      exact h2
    · rw [m2, m1]
    · rw [s2, s1]

/-- `_flag_mask_`, `_singles_mask_` and `_all_bits_`, as `__set_name__` keeps them one member at a time, are what the
definitions in the rest of this model read off the list of members, so that the `FlagCls` that `_missing_` runs on is
the class that was built. Every member value is an `int` that is not negative, and names do not repeat, both invariants
of a `Flag` class body. -/
def FlagBuildMasks : Prop :=
  ∀ (members : List (String × Nat)) (b : Boundary), (members.map (fun p => p.1.toList)).Nodup →
    ∃ c, ({ kind := .flag } : EClass).build (members.map (fun p => (p.1.toList, .atom (.int (p.2 : Int))))) = .ok c ∧
      let f : FlagCls := { name := "F", members := members, boundary := b }
      c.flagMask = f.flagMask ∧ c.singlesMask = f.singlesMask ∧ c.allBits = f.allBits

theorem flagBuildMasks_proven : FlagBuildMasks := by
  intro members b hn
  obtain ⟨c, h1, h2, h3, h4⟩ := flag_build members { kind := .flag } [] rfl rfl (by simp) (by simpa using hn)
  exact ⟨c, h1, h2, h3, by simpa [FlagCls.allBits, FlagCls.flagMask, h2] using h4⟩

end PyLean.CoreLibs.EnumDC
