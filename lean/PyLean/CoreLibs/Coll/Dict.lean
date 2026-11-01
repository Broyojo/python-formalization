import PyLean.Core

/-!
Insertion-ordered `dict` over an abstract key type, the substrate of `Counter`,
`ChainMap` and `UserDict` (Lib/collections/__init__.py, CPython 3.14.7).

Keys are a type with decidable equality. That stands for the Python contract on
keys (hash and `==` consistent, `==` an equivalence relation, key objects not
mutated while in the dict); a user-defined key type that breaks the contract is
out of scope. A dict is its items in insertion order, and the type invariant of
a real dict is `Nodup` on the keys, which properties assume as `D.WF`.

Observable order is the reason for a list and not a function: `most_common`,
`elements`, iteration and every multiset operator's result expose it.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PyLean.CoreLibs.Coll

open PyLean

/-- A `dict`: `(key, value)` pairs in insertion order. -/
abbrev D (κ ν : Type) := List (κ × ν)

namespace D

variable {κ ν : Type} [DecidableEq κ]

/-- `list(d)`. -/
def keys (d : D κ ν) : List κ := d.map (·.1)

/-- `d.values()`. -/
def values (d : D κ ν) : List ν := d.map (·.2)

/-- The dict type invariant: no key occurs twice. -/
def WF (d : D κ ν) : Prop := (keys d).Nodup

/-- `d.get(x)` with `None` as `none`; also the probe behind `d[x]`. -/
def get? : D κ ν → κ → Option ν
  | [], _ => none
  | (a, b) :: t, x => if a = x then some b else get? t x

/-- `x in d`. -/
def mem (d : D κ ν) (x : κ) : Bool := (get? d x).isSome

/-- `d[x] = v`: replaces the value in place, or appends a new key. -/
def set : D κ ν → κ → ν → D κ ν
  | [], x, v => [(x, v)]
  | (a, b) :: t, x, v => if a = x then (a, v) :: t else (a, b) :: set t x v

/-- `del d[x]` once `x in d` is known; a no-op on an absent key. -/
def del : D κ ν → κ → D κ ν
  | [], _ => []
  | (a, b) :: t, x => if a = x then t else (a, b) :: del t x

/-- `d.update(items)`, also `d |= items`: `dict_merge` in iteration order. -/
def update (d : D κ ν) (items : List (κ × ν)) : D κ ν :=
  items.foldl (fun d p => set d p.1 p.2) d

/-- `dict.fromkeys(iterable, value)`. -/
def fromkeys (it : List κ) (v : ν) : D κ ν := it.foldl (fun d x => set d x v) []

/-- `a | b`: `dict_or` copies `a` and merges `b`. -/
def or_ (a b : D κ ν) : D κ ν := update a b

/-! ### Lemmas -/

@[simp] theorem keys_nil : keys ([] : D κ ν) = [] := rfl
@[simp] theorem keys_cons (p : κ × ν) (t : D κ ν) : keys (p :: t) = p.1 :: keys t := rfl
@[simp] theorem keys_append (a b : D κ ν) : keys (a ++ b) = keys a ++ keys b := by simp [keys]

@[simp] theorem get?_nil (x : κ) : get? ([] : D κ ν) x = none := rfl
theorem get?_cons (a : κ) (b : ν) (t : D κ ν) (x : κ) :
    get? ((a, b) :: t) x = if a = x then some b else get? t x := rfl

theorem mem_keys_of_mem {q : κ × ν} {t : D κ ν} (h : q ∈ t) : q.1 ∈ keys t := List.mem_map_of_mem h

theorem get?_eq_none_iff {d : D κ ν} {x : κ} : get? d x = none ↔ x ∉ keys d := by
  induction d with
  | nil => simp
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    simp only [get?_cons, keys_cons, List.mem_cons, not_or]
    by_cases h : a = x
    · subst h; simp
    · simp only [h, ite_false, ih]
      constructor
      · intro hx; exact ⟨fun e => h e.symm, hx⟩
      · intro hx; exact hx.2

theorem get?_isSome_iff {d : D κ ν} {x : κ} : (get? d x).isSome ↔ x ∈ keys d := by
  have := @get?_eq_none_iff κ ν _ d x
  cases h : get? d x with
  | none => simp [this.mp h]
  | some v =>
    simp only [Option.isSome_some, true_iff]
    exact Classical.byContradiction fun hx => by
      have := this.mpr hx
      simp [h] at this

theorem mem_iff {d : D κ ν} {x : κ} : mem d x = true ↔ x ∈ keys d := get?_isSome_iff

theorem mem_false_iff {d : D κ ν} {x : κ} : mem d x = false ↔ x ∉ keys d := by
  rw [← mem_iff]; simp

theorem get?_set (d : D κ ν) (x y : κ) (v : ν) :
    get? (set d x v) y = if x = y then some v else get? d y := by
  induction d with
  | nil => simp [set, get?_cons]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    simp only [set]
    by_cases h : a = x
    · subst h; simp only [ite_true, get?_cons]; by_cases h2 : a = y <;> simp [h2]
    · simp only [h, ite_false, get?_cons, ih]; grind

theorem set_of_notMem {d : D κ ν} {x : κ} (v : ν) (h : x ∉ keys d) : set d x v = d ++ [(x, v)] := by
  induction d with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    simp only [keys_cons, List.mem_cons, not_or] at h
    have : a ≠ x := fun e => h.1 e.symm
    simp [set, this, ih h.2]

theorem keys_set (d : D κ ν) (x : κ) (v : ν) :
    keys (set d x v) = if x ∈ keys d then keys d else keys d ++ [x] := by
  induction d with
  | nil => simp [set]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    simp only [set]
    by_cases h : a = x
    · subst h; simp
    · have hne : ¬ x = a := fun e => h e.symm
      simp only [h, ite_false, keys_cons, ih, List.mem_cons, hne, false_or]
      split <;> simp

theorem keys_set_of_mem {d : D κ ν} {x : κ} (v : ν) (h : x ∈ keys d) : keys (set d x v) = keys d := by
  simp [keys_set, h]

theorem WF_set {d : D κ ν} (h : WF d) (x : κ) (v : ν) : WF (set d x v) := by
  unfold WF at *
  rw [keys_set]
  split
  · exact h
  · next hx =>
    rw [List.nodup_append]
    refine ⟨h, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    intro e; subst e; exact hx ha

theorem WF_nil : WF ([] : D κ ν) := by simp [WF]

theorem WF_of_cons {p : κ × ν} {t : D κ ν} (h : WF (p :: t)) : WF t := by
  unfold WF at *; simp only [keys_cons, List.nodup_cons] at h; exact h.2

theorem notMem_of_cons {p : κ × ν} {t : D κ ν} (h : WF (p :: t)) : p.1 ∉ keys t := by
  unfold WF at h; simp only [keys_cons, List.nodup_cons] at h; exact h.1

/-- On a dict with unique keys, `set` of a present key is a pointwise map. -/
theorem set_of_mem_map {d : D κ ν} (hw : WF d) {x : κ} (v : ν) (h : x ∈ keys d) :
    set d x v = d.map (fun p => if p.1 = x then (p.1, v) else p) := by
  induction d with
  | nil => simp at h
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    have hn := notMem_of_cons hw
    have hwt := WF_of_cons hw
    by_cases hax : a = x
    · subst hax
      simp only [set, ite_true, List.map_cons, Prod.mk.injEq]
      have : ∀ q ∈ t, ¬ q.1 = a := by
        intro q hq e
        apply hn
        have : q.1 ∈ keys t := List.mem_map_of_mem hq
        simpa [e] using this
      have hm : t.map (fun p => if p.1 = a then (p.1, v) else p) = t.map id :=
        List.map_congr_left (fun q hq => by simp [this q hq])
      simp [hm]
    · have hxt : x ∈ keys t := by
        simp only [keys_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h.symm hax
        · exact h
      simp [set, hax, ih hwt hxt]

theorem get?_of_mem_pair {d : D κ ν} (hw : WF d) {x : κ} {v : ν} (h : (x, v) ∈ d) :
    get? d x = some v := by
  induction d with
  | nil => simp at h
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    have hn := notMem_of_cons hw
    simp only [List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨e1, e2⟩ | h
    · subst e1 e2; simp [get?_cons]
    · have hxt : x ∈ keys t := List.mem_map_of_mem (f := Prod.fst) h
      have hax : a ≠ x := by
        intro e; subst e; exact hn hxt
      simp [get?_cons, hax, ih (WF_of_cons hw) h]

theorem get?_del {d : D κ ν} (hw : WF d) (x y : κ) :
    get? (del d x) y = if x = y then none else get? d y := by
  induction d with
  | nil => simp [del]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    have hwt := WF_of_cons hw
    simp only [del]
    by_cases hax : a = x
    · subst hax
      simp only [ite_true, get?_cons]
      by_cases h : a = y
      · subst h
        simp [get?_eq_none_iff.mpr (notMem_of_cons hw)]
      · simp [h]
    · simp only [hax, ite_false, get?_cons, ih hwt]
      grind

theorem keys_del_sublist (d : D κ ν) (x : κ) : (keys (del d x)).Sublist (keys d) := by
  induction d with
  | nil => simp [del]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    simp only [del]
    split
    · exact List.sublist_cons_self _ _
    · simp only [keys_cons]; exact ih.cons_cons a

theorem WF_del {d : D κ ν} (h : WF d) (x : κ) : WF (del d x) :=
  List.Nodup.sublist (keys_del_sublist d x) h

/-- Two well-formed dicts with the same key order and the same lookups are equal. -/
theorem ext_keys {a b : D κ ν} (ha : WF a) (hb : WF b) (hk : keys a = keys b)
    (hg : ∀ x, get? a x = get? b x) : a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons q t => simp at hk
  | cons p t ih =>
    cases b with
    | nil => simp at hk
    | cons q s =>
      obtain ⟨a1, a2⟩ := p
      obtain ⟨b1, b2⟩ := q
      simp only [keys_cons, List.cons.injEq] at hk
      obtain ⟨e1, e2⟩ := hk
      subst e1
      have h0 := hg a1
      simp only [get?_cons, ite_true, Option.some.injEq] at h0
      subst h0
      congr 1
      apply ih (WF_of_cons ha) (WF_of_cons hb) e2
      intro x
      have := hg x
      simp only [get?_cons] at this
      by_cases h : a1 = x
      · subst h
        rw [get?_eq_none_iff.mpr (notMem_of_cons ha), get?_eq_none_iff.mpr (notMem_of_cons hb)]
      · simpa [h] using this

theorem WF_update {d : D κ ν} (h : WF d) (items : List (κ × ν)) : WF (update d items) := by
  induction items generalizing d with
  | nil => exact h
  | cons p t ih => exact ih (WF_set h _ _)

/-- `update` with pairs of fresh, distinct keys appends them. -/
theorem update_fresh {d : D κ ν} {items : List (κ × ν)} (h : WF items)
    (hf : ∀ x ∈ keys items, x ∉ keys d) : update d items = d ++ items := by
  induction items generalizing d with
  | nil => simp [update]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    have hn := notMem_of_cons h
    have hfa : a ∉ keys d := hf a (by simp)
    simp only [update, List.foldl_cons]
    rw [set_of_notMem _ hfa]
    have := @ih (d ++ [(a, b)]) (WF_of_cons h) (by
      intro x hx
      simp only [keys_append, keys_cons, keys_nil, List.mem_append, List.mem_singleton, not_or]
      refine ⟨hf x (by simp [hx]), ?_⟩
      intro e; subst e; exact hn hx)
    simpa [update] using this

theorem get?_update (d : D κ ν) (items : List (κ × ν)) (x : κ) :
    get? (update d items) x = (get? items.reverse x).or (get? d x) := by
  induction items generalizing d with
  | nil => simp [update]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    simp only [update, List.foldl_cons, List.reverse_cons] at ih ⊢
    rw [ih, get?_set]
    have : ∀ (l : D κ ν), get? (l ++ [(a, b)]) x = (get? l x).or (if a = x then some b else none) := by
      intro l
      induction l with
      | nil => simp [get?_cons]
      | cons q s ih2 =>
        obtain ⟨c, d'⟩ := q
        simp only [List.cons_append, get?_cons]
        by_cases hc : c = x <;> simp [hc, ih2]
    rw [this]
    by_cases h : a = x <;> simp [h]

end D

end PyLean.CoreLibs.Coll
