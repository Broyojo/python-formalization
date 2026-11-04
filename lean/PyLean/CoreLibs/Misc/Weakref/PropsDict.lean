import PyLean.CoreLibs.Misc.Weakref.Model

/-!
Lemmas on the `dict` with fallible keys (`pFind`, `pSet`, ...) and on association lists. `strip`
forgets the stored hashes. `Plain` keys have the default `object.__eq__` (identity) and a `__hash__`
that does not raise; for them a lookup is the first identical key.
-/

namespace PyLean.CoreLibs.Misc.Weakref

open PyLean

variable {K β : Type} [DecidableEq K]

/-- `data` of a dict has distinct keys: the identity test of a lookup comes first, so the same key
object is never stored twice. -/
def Keys (d : List (K × β)) : Prop := (d.map (·.1)).Nodup

theorem dGet_cons (a : K) (b : β) (rest : List (K × β)) (k : K) :
    dGet ((a, b) :: rest) k = if a = k then some b else dGet rest k := by
  simp only [dGet, List.lookup]
  by_cases h : a = k
  · simp [h]
  · have : (k == a) = false := by simp [Ne.symm h]
    simp [this, h]

theorem dGet_dSet (d : List (K × β)) (k a : K) (v : β) :
    dGet (dSet d k v) a = if k = a then some v else dGet d a := by
  induction d with
  | nil =>
    simp only [dSet]
    rw [dGet_cons]
  | cons p rest ih =>
    obtain ⟨x, y⟩ := p
    simp only [dSet]
    by_cases hx : x = k
    · subst hx
      simp only [if_true, dGet_cons]
      by_cases h : x = a <;> simp [h]
    · simp only [hx, if_false, dGet_cons, ih]
      by_cases h : x = a
      · subst h
        simp [Ne.symm hx]
      · simp [h]

theorem keys_dSet (d : List (K × β)) (k : K) (v : β) :
    (dSet d k v).map (·.1) = if k ∈ d.map (·.1) then d.map (·.1) else d.map (·.1) ++ [k] := by
  induction d with
  | nil => simp [dSet]
  | cons p rest ih =>
    obtain ⟨x, y⟩ := p
    simp only [dSet]
    by_cases hx : x = k
    · subst hx
      simp
    · simp only [hx, if_false, List.map_cons, ih, List.mem_cons]
      have : (k = x) = False := by simp [Ne.symm hx]
      simp only [this, false_or]
      split <;> simp

theorem Keys_dSet {d : List (K × β)} (h : Keys d) (k : K) (v : β) : Keys (dSet d k v) := by
  unfold Keys at *
  rw [keys_dSet]
  split
  · exact h
  · rename_i hk
    rw [List.nodup_append]
    refine ⟨h, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    intro e
    subst e
    exact hk ha

theorem dGet_absent (l : List (K × β)) (x : K) (h : x ∉ l.map (·.1)) : dGet l x = none := by
  induction l with
  | nil => rfl
  | cons q r ihr =>
    obtain ⟨u, w⟩ := q
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [dGet_cons, if_neg (Ne.symm h.1)]
    exact ihr h.2

theorem dGet_dDel {d : List (K × β)} (hd : Keys d) (k a : K) :
    dGet (dDel d k) a = if k = a then none else dGet d a := by
  induction d with
  | nil => simp [dDel, dGet]
  | cons p rest ih =>
    obtain ⟨x, y⟩ := p
    have hn : x ∉ rest.map (·.1) ∧ Keys rest := by
      unfold Keys at hd ⊢
      simpa using hd
    simp only [dDel]
    by_cases hx : x = k
    · subst hx
      simp only [if_true, dGet_cons]
      by_cases h : x = a
      · subst h
        simp only [if_true]
        exact dGet_absent rest x hn.1
      · simp [h]
    · simp only [hx, if_false, dGet_cons, ih hn.2]
      by_cases h : x = a
      · subst h
        simp [Ne.symm hx]
      · simp [h]

theorem keys_dDel_sub (d : List (K × β)) (k : K) : ∀ a ∈ (dDel d k).map (·.1), a ∈ d.map (·.1) := by
  induction d with
  | nil => simp [dDel]
  | cons p r ih =>
    intro a ha
    obtain ⟨u, v⟩ := p
    simp only [dDel] at ha
    split at ha
    · simp only [List.map_cons, List.mem_cons]
      exact .inr ha
    · simp only [List.map_cons, List.mem_cons] at ha ⊢
      rcases ha with e | ha
      · exact .inl e
      · exact .inr (ih a ha)

theorem Keys_dDel {d : List (K × β)} (h : Keys d) (k : K) : Keys (dDel d k) := by
  induction d with
  | nil => simp [dDel, Keys]
  | cons p rest ih =>
    obtain ⟨u, v⟩ := p
    unfold Keys at h
    simp only [List.map_cons, List.nodup_cons] at h
    simp only [dDel]
    split
    · exact h.2
    · unfold Keys
      simp only [List.map_cons, List.nodup_cons]
      exact ⟨fun hm => h.1 (keys_dDel_sub rest k u hm), ih h.2⟩

theorem dSet_absent (d : List (K × β)) (k : K) (v : β) (h : k ∉ d.map (·.1)) :
    dSet d k v = d ++ [(k, v)] := by
  induction d with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨x, y⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [dSet, if_neg (Ne.symm h.1), List.cons_append, ih h.2]

theorem deref_cons (o : Nat) (w : World) (r : Nat) :
    deref (o :: w) r = if r = o then none else deref w r := by
  by_cases h : r = o
  · subst h
    simp [deref, alive]
  · simp [deref, alive, List.contains_cons, h]

theorem deref_some {w : World} {r : Nat} {v : PV} (h : deref w r = some v) : v = .obj r := by
  simp only [deref] at h
  split at h
  · simpa using h.symm
  · cases h

/-! ### The dict with fallible keys -/

/-- The items without their stored hashes. -/
def strip (d : List (Ent K β)) : List (K × β) := d.map (fun e => (e.1, e.2.2))

/-- Keys with the default identity `__eq__` (`object.__eq__`, or interned `str` keys) and a
`__hash__` that does not raise. -/
structure Plain (ops : KOps K) : Prop where
  hash : ∀ k, ∃ h, ops.hash k = .ok h
  eq : ∀ a b, a ≠ b → ops.eq a b = .ok false

/-- The first entry whose key is `k` itself. -/
def idFind (k : K) : List (Ent K β) → Option (Nat × β)
  | [] => none
  | (k0, _, v0) :: rest =>
    if k0 = k then some (0, v0) else (idFind k rest).map (fun p => (p.1 + 1, p.2))

theorem shift_ok (r : Option (Nat × β)) :
    shift (.ok r : Py (Option (Nat × β))) = .ok (r.map (fun p => (p.1 + 1, p.2))) := rfl

theorem pFind_cons (eq : K → K → Py Bool) (k : K) (h : Int) (k0 : K) (h0 : Int) (v0 : β)
    (rest : List (Ent K β)) :
    pFind eq k h ((k0, h0, v0) :: rest) =
      if k0 = k then .ok (some (0, v0))
      else if h0 = h then
        (match eq k0 k with
         | .error e => .error e
         | .ok true => .ok (some (0, v0))
         | .ok false => shift (pFind eq k h rest))
      else shift (pFind eq k h rest) := rfl

theorem pFind_plain (eq : K → K → Py Bool) (k : K) (h : Int)
    (heq : ∀ a, a ≠ k → eq a k = .ok false) :
    ∀ d : List (Ent K β), pFind eq k h d = .ok (idFind k d) := by
  intro d
  induction d with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k0, h0, v0⟩ := p
    rw [pFind_cons]
    simp only [idFind]
    by_cases hk : k0 = k
    · simp [hk]
    · simp only [hk, if_false, heq k0 hk, ih, shift_ok]
      split <;> rfl

theorem dhash_plain {ops : KOps K} (hp : Plain ops) (k : K) : ∃ h, ops.dhash k = .ok h := by
  obtain ⟨h, hh⟩ := hp.hash k
  exact ⟨h, by simp [KOps.dhash, hh, unhashable]⟩

theorem pLookup_plain {ops : KOps K} (hp : Plain ops) (d : List (Ent K β)) (k : K) :
    pLookup ops d k = .ok (idFind k d) := by
  obtain ⟨h, hh⟩ := dhash_plain hp k
  simp only [pLookup, hh]
  exact pFind_plain ops.eq k h (fun a ha => hp.eq a k ha) d

theorem idFind_dGet (k : K) : ∀ d : List (Ent K β), (idFind k d).map (·.2) = dGet (strip d) k := by
  intro d
  induction d with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k0, h0, v0⟩ := p
    simp only [idFind, strip, List.map_cons]
    rw [dGet_cons]
    by_cases hk : k0 = k
    · simp [hk]
    · simp only [hk, if_false, Option.map_map]
      have e : ((fun x : Nat × β => x.2) ∘ fun p : Nat × β => (p.1 + 1, p.2)) =
          (fun x : Nat × β => x.2) := rfl
      rw [e, ih]
      rfl

theorem idFind_none (k : K) (d : List (Ent K β)) (h : idFind k d = none) :
    k ∉ (strip d).map (·.1) := by
  induction d with
  | nil => simp [strip]
  | cons p rest ih =>
    obtain ⟨k0, h0, v0⟩ := p
    simp only [idFind] at h
    by_cases hk : k0 = k
    · simp [hk] at h
    · simp only [hk, if_false, Option.map_eq_none_iff] at h
      simp only [strip, List.map_cons, List.mem_cons, not_or]
      exact ⟨Ne.symm hk, by simpa [strip] using ih h⟩

theorem strip_append (d : List (Ent K β)) (k : K) (h : Int) (v : β) :
    strip (d ++ [(k, h, v)]) = strip d ++ [(k, v)] := by
  simp [strip]

theorem strip_setAt (k : K) (v : β) : ∀ (d : List (Ent K β)) (i : Nat) (x : β),
    idFind k d = some (i, x) → strip (setAt d i v) = dSet (strip d) k v := by
  intro d
  induction d with
  | nil => intro i x h; simp [idFind] at h
  | cons p rest ih =>
    intro i x h
    obtain ⟨k0, h0, v0⟩ := p
    simp only [idFind] at h
    by_cases hk : k0 = k
    · simp only [hk, if_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst hk
      simp [setAt, strip, dSet]
    · simp only [hk, if_false] at h
      cases hr : idFind k rest with
      | none => rw [hr] at h; simp at h
      | some p =>
        rw [hr] at h
        obtain ⟨j, y⟩ := p
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have := ih j _ hr
        simp only [strip] at this
        simp [setAt, strip, dSet, hk, this]

theorem strip_delAt (k : K) : ∀ (d : List (Ent K β)) (i : Nat) (x : β),
    idFind k d = some (i, x) → strip (delAt d i) = dDel (strip d) k := by
  intro d
  induction d with
  | nil => intro i x h; simp [idFind] at h
  | cons p rest ih =>
    intro i x h
    obtain ⟨k0, h0, v0⟩ := p
    simp only [idFind] at h
    by_cases hk : k0 = k
    · simp only [hk, if_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst hk
      simp [delAt, strip, dDel]
    · simp only [hk, if_false] at h
      cases hr : idFind k rest with
      | none => rw [hr] at h; simp at h
      | some p =>
        rw [hr] at h
        obtain ⟨j, y⟩ := p
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have := ih j _ hr
        simp only [strip] at this
        simp [delAt, strip, dDel, hk, this]

/-- For plain keys a store is `dSet` on the items. -/
theorem pSet_plain {ops : KOps K} (hp : Plain ops) (d : List (Ent K β)) (k : K) (v : β) :
    ∃ d', pSet ops d k v = .ok d' ∧ strip d' = dSet (strip d) k v := by
  obtain ⟨h, hh⟩ := dhash_plain hp k
  have hf := pFind_plain ops.eq k h (fun a ha => hp.eq a k ha) d
  simp only [pSet, hh, hf]
  cases hi : idFind k d with
  | none =>
    refine ⟨_, rfl, ?_⟩
    rw [strip_append, dSet_absent _ _ _ (idFind_none k d hi)]
  | some p =>
    obtain ⟨i, x⟩ := p
    exact ⟨_, rfl, strip_setAt k v d i x hi⟩

/-- For plain keys a deletion is `dDel` on the items, or `err` for a missing key. -/
theorem pDel_plain {ops : KOps K} (hp : Plain ops) (err : PyExc) (d : List (Ent K β)) (k : K) :
    (dGet (strip d) k = none → pDel ops err d k = .error err) ∧
    (∀ x, dGet (strip d) k = some x → ∃ d', pDel ops err d k = .ok d' ∧ strip d' = dDel (strip d) k) := by
  have hl := pLookup_plain hp d k
  have hg := idFind_dGet k d
  constructor
  · intro h
    rw [← hg] at h
    have : idFind k d = none := by simpa using h
    simp [pDel, hl, this]
  · intro x h
    rw [← hg] at h
    cases hi : idFind k d with
    | none => rw [hi] at h; simp at h
    | some p =>
      obtain ⟨i, y⟩ := p
      exact ⟨_, by simp [pDel, hl, hi], strip_delAt k d i y hi⟩

/-! ### Any keys: a store reads back -/

theorem pFind_setAt (eq : K → K → Py Bool) (k : K) (h : Int) (v : β) :
    ∀ (d : List (Ent K β)) (i : Nat) (x : β), pFind eq k h d = .ok (some (i, x)) →
      pFind eq k h (setAt d i v) = .ok (some (i, v)) := by
  intro d
  induction d with
  | nil => intro i x hf; simp [pFind] at hf
  | cons p rest ih =>
    intro i x hf
    obtain ⟨k0, h0, v0⟩ := p
    rw [pFind_cons] at hf
    by_cases hk : k0 = k
    · simp only [hk, if_true, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp [setAt, pFind_cons, hk]
    · simp only [hk, if_false] at hf
      have hrec : ∀ (r : Py (Option (Nat × β))), shift r = .ok (some (i, x)) →
          ∃ j, i = j + 1 ∧ r = .ok (some (j, x)) := by
        intro r hr
        cases r with
        | error e => simp [shift] at hr
        | ok o =>
          cases o with
          | none => simp [shift] at hr
          | some q =>
            obtain ⟨j, y⟩ := q
            simp only [shift, Option.map_some, Except.ok.injEq, Option.some.injEq,
              Prod.mk.injEq] at hr
            exact ⟨j, hr.1.symm, by rw [hr.2]⟩
      by_cases hh : h0 = h
      · simp only [hh, if_true] at hf
        cases he : eq k0 k with
        | error e => rw [he] at hf; simp at hf
        | ok b =>
          cases b with
          | true =>
            rw [he] at hf
            simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hf
            obtain ⟨rfl, rfl⟩ := hf
            simp [setAt, pFind_cons, hk, hh, he]
          | false =>
            rw [he] at hf
            obtain ⟨j, rfl, hj⟩ := hrec _ hf
            simp [setAt, pFind_cons, hk, hh, he, ih j x hj, shift]
      · simp only [hh, if_false] at hf
        obtain ⟨j, rfl, hj⟩ := hrec _ hf
        simp [setAt, pFind_cons, hk, hh, ih j x hj, shift]

theorem pFind_append (eq : K → K → Py Bool) (k : K) (h : Int) (v : β) :
    ∀ d : List (Ent K β), pFind eq k h d = .ok none →
      pFind eq k h (d ++ [(k, h, v)]) = .ok (some (d.length, v)) := by
  intro d
  induction d with
  | nil => intro _; simp [pFind_cons]
  | cons p rest ih =>
    intro hf
    obtain ⟨k0, h0, v0⟩ := p
    rw [pFind_cons] at hf
    have hrec : ∀ (r : Py (Option (Nat × β))), shift r = .ok none → r = .ok none := by
      intro r hr
      cases r with
      | error e => simp [shift] at hr
      | ok o => cases o with
        | none => rfl
        | some q => simp [shift] at hr
    by_cases hk : k0 = k
    · simp [hk] at hf
    · simp only [hk, if_false] at hf
      by_cases hh : h0 = h
      · simp only [hh, if_true] at hf
        cases he : eq k0 k with
        | error e => rw [he] at hf; simp at hf
        | ok b =>
          cases b with
          | true => rw [he] at hf; simp at hf
          | false =>
            rw [he] at hf
            have := ih (hrec _ hf)
            simp [pFind_cons, hk, hh, he, this, shift]
      · simp only [hh, if_false] at hf
        have := ih (hrec _ hf)
        simp [pFind_cons, hk, hh, this, shift]

/-- A store, whatever `__eq__` does, is found again by the same key with the stored value: the
lookup repeats the comparisons that led to the store. -/
theorem pSet_lookup (ops : KOps K) (d d' : List (Ent K β)) (k : K) (v : β)
    (h : pSet ops d k v = .ok d') : ∃ i, pLookup ops d' k = .ok (some (i, v)) := by
  simp only [pSet] at h
  cases hh : ops.dhash k with
  | error e => simp [hh] at h
  | ok hv =>
    simp only [hh] at h
    cases hf : pFind ops.eq k hv d with
    | error e => simp [hf] at h
    | ok r =>
      simp only [hf] at h
      cases r with
      | none =>
        simp only [Except.ok.injEq] at h
        subst h
        exact ⟨d.length, by simp [pLookup, hh, pFind_append ops.eq k hv v d hf]⟩
      | some p =>
        obtain ⟨i, x⟩ := p
        simp only [Except.ok.injEq] at h
        subst h
        exact ⟨i, by simp [pLookup, hh, pFind_setAt ops.eq k hv v d i x hf]⟩

/-- The entries of `delAt` are a sublist. -/
theorem delAt_sub {α : Type} : ∀ (d : List α) (i : Nat), (delAt d i).Sublist d := by
  intro d
  induction d with
  | nil => intro i; simp [delAt]
  | cons p rest ih =>
    intro i
    cases i with
    | zero => simp [delAt]
    | succ j => simp only [delAt]; exact (ih j).cons_cons p

/-- `filterMap` after removing an entry `f` drops. -/
theorem filterMap_delAt {α γ : Type} (f : α → Option γ) : ∀ (d : List α) (i : Nat),
    (∀ a, d[i]? = some a → f a = none) → (delAt d i).filterMap f = d.filterMap f := by
  intro d
  induction d with
  | nil => intro i _; simp [delAt]
  | cons p rest ih =>
    intro i h
    cases i with
    | zero =>
      have := h p rfl
      simp [delAt, List.filterMap_cons, this]
    | succ j =>
      simp only [delAt, List.filterMap_cons]
      rw [ih j (fun a ha => h a (by simpa using ha))]

theorem pFind_index (eq : K → K → Py Bool) (k : K) (h : Int) :
    ∀ (d : List (Ent K β)) (i : Nat) (x : β), pFind eq k h d = .ok (some (i, x)) →
      ∃ k0 h0, d[i]? = some (k0, h0, x) := by
  intro d
  induction d with
  | nil => intro i x hf; simp [pFind] at hf
  | cons p rest ih =>
    intro i x hf
    obtain ⟨k0, h0, v0⟩ := p
    rw [pFind_cons] at hf
    have hrec : ∀ (r : Py (Option (Nat × β))), shift r = .ok (some (i, x)) →
        ∃ j, i = j + 1 ∧ r = .ok (some (j, x)) := by
      intro r hr
      cases r with
      | error e => simp [shift] at hr
      | ok o =>
        cases o with
        | none => simp [shift] at hr
        | some q =>
          obtain ⟨j, y⟩ := q
          simp only [shift, Option.map_some, Except.ok.injEq, Option.some.injEq,
            Prod.mk.injEq] at hr
          exact ⟨j, hr.1.symm, by rw [hr.2]⟩
    by_cases hk : k0 = k
    · simp only [hk, if_true, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      exact ⟨k0, h0, rfl⟩
    · simp only [hk, if_false] at hf
      by_cases hh : h0 = h
      · simp only [hh, if_true] at hf
        cases he : eq k0 k with
        | error e => rw [he] at hf; simp at hf
        | ok b =>
          cases b with
          | true =>
            rw [he] at hf
            simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hf
            obtain ⟨rfl, rfl⟩ := hf
            exact ⟨k0, h0, rfl⟩
          | false =>
            rw [he] at hf
            obtain ⟨j, rfl, hj⟩ := hrec _ hf
            obtain ⟨a, b, hab⟩ := ih j x hj
            exact ⟨a, b, by simpa using hab⟩
      · simp only [hh, if_false] at hf
        obtain ⟨j, rfl, hj⟩ := hrec _ hf
        obtain ⟨a, b, hab⟩ := ih j x hj
        exact ⟨a, b, by simpa using hab⟩

end PyLean.CoreLibs.Misc.Weakref
