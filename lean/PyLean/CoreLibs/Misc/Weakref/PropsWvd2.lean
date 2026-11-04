import PyLean.CoreLibs.Misc.Weakref.PropsWvd

/-! `WeakValueDictionary`: the generators, `valuerefs`, `popitem`, `copy`, `|`, `update`,
`__init__`. -/

namespace PyLean.CoreLibs.Misc.Weakref

open PyLean

namespace WVD

/-! ### Generators -/

/-- Run a generator to its end: at most `n` calls of `next()`, in one world. -/
def drain {α γ : Type} (step : Option (List α) → Option (List α) × Option γ) :
    Nat → Option (List α) → List γ
  | 0, _ => []
  | n + 1, g =>
    match step g with
    | (g', some y) => y :: drain step n g'
    | (_, none) => []

theorem snapNext_spec {α γ : Type} (f : α → Option γ) : ∀ s : List α,
    (snapNext f s).map (·.1) = (s.filterMap f).head? ∧
    ((snapNext f s).map (·.2) |>.getD []).filterMap f = (s.filterMap f).tail := by
  intro s
  induction s with
  | nil => simp [snapNext]
  | cons a rest ih =>
    simp only [snapNext, List.filterMap_cons]
    cases f a with
    | some g => simp
    | none => exact ih

/-- One `next()`: the first entry of what is left of the snapshot that the body keeps in the world
of this call, and what is left after it. -/
theorem genNext_spec {α γ : Type} (f : World → α → Option γ) (cur : List α) (w : World)
    (g : Option (List α)) :
    (genNext f cur w g).2 = ((g.getD cur).filterMap (f w)).head? ∧
    ∃ rest, (genNext f cur w g).1 = some rest ∧
      rest.filterMap (f w) = ((g.getD cur).filterMap (f w)).tail := by
  have h := snapNext_spec (f w) (g.getD cur)
  simp only [genNext]
  cases hs : snapNext (f w) (g.getD cur) with
  | none =>
    rw [hs] at h
    simp only [Option.map_none, Option.getD_none, List.filterMap_nil] at h
    exact ⟨h.1, [], rfl, h.2⟩
  | some p =>
    obtain ⟨x, rest⟩ := p
    rw [hs] at h
    exact ⟨h.1, rest, rfl, h.2⟩

theorem drain_spec {α γ : Type} (f : World → α → Option γ) (cur : List α) (w : World) :
    ∀ (n : Nat) (s : List α), (s.filterMap (f w)).length < n →
      drain (genNext f cur w) n (some s) = s.filterMap (f w) := by
  intro n
  induction n with
  | zero => intro s h; simp at h
  | succ n ih =>
    intro s hs
    obtain ⟨h1, rest, h2, h3⟩ := genNext_spec f cur w (some s)
    simp only [Option.getD_some] at h1 h3
    simp only [drain]
    cases hg : genNext f cur w (some s) with
    | mk g' y =>
      rw [hg] at h1 h2
      simp only at h1 h2
      subst h2
      cases y with
      | none =>
        simp only
        cases hl : s.filterMap (f w) with
        | nil => rfl
        | cons a t => rw [hl] at h1; simp at h1
      | some y =>
        simp only
        cases hl : s.filterMap (f w) with
        | nil => rw [hl] at h1; simp at h1
        | cons a t =>
          rw [hl] at h1 h3 hs
          simp only [List.head?_cons, Option.some.injEq] at h1
          simp only [List.tail_cons] at h3
          subst h1
          rw [ih rest (by rw [h3]; simp at hs; omega), h3]

theorem drain_fresh {α γ : Type} (f : World → α → Option γ) (cur : List α) (w : World) :
    drain (genNext f cur w) (cur.length + 1) none = cur.filterMap (f w) := by
  have : drain (genNext f cur w) (cur.length + 1) none =
      drain (genNext f cur w) (cur.length + 1) (some cur) := by
    simp only [drain, genNext, Option.getD_none, Option.getD_some]
  rw [this]
  apply drain_spec
  have := List.length_filterMap_le (f w) cur
  omega

variable {K : Type} [DecidableEq K]

/-- The four generators of `WeakValueDictionary` (`items`, `keys`/`__iter__`, `values`,
`itervaluerefs`) are lazy: the snapshot `self.data.copy()` is taken at the first `next()`, so a store
before it is seen, and nothing done to the dictionary after it is seen or raises; each `next()` reads
the references in the world of that call, so a value that dies between two calls is skipped by
`items` and `values` (and its reference still yielded by `itervaluerefs`). Run to the end in one
world they give the live items, their keys, their values, and every reference of `valuerefs()`, in
order. `valuerefs()` is the list of the stored references themselves: as many as `len()`, and the
live ones read the values of `items()`. -/
def WvdIters : Prop :=
  ∀ (K : Type) [DecidableEq K] (w : World) (d d' : WVD K) (s : List (Ent K (KRef K))),
    d.itemsNext w none = d.itemsNext w (some d.data) ∧
    d.itemsNext w (some s) = d'.itemsNext w (some s) ∧
    d.keysNext w (some s) = d'.keysNext w (some s) ∧
    d.valuesNext w (some s) = d'.valuesNext w (some s) ∧
    d.irefsNext w (some s) = d'.irefsNext w (some s) ∧
    (d.itemsNext w (some s)).2 = (s.filterMap (itemF w)).head? ∧
    (d.valuesNext w (some s)).2 = (s.filterMap (valueF w)).head? ∧
    (d.keysNext w (some s)).2 = (s.filterMap (keyF w)).head? ∧
    (d.irefsNext w (some s)).2 = s.head?.map (·.2.2) ∧
    drain (d.itemsNext w) (d.data.length + 1) none = liveItems w d ∧
    drain (d.keysNext w) (d.data.length + 1) none = (liveItems w d).map (·.1) ∧
    drain (d.valuesNext w) (d.data.length + 1) none = (liveItems w d).map (·.2) ∧
    drain (d.irefsNext w) (d.data.length + 1) none = d.valuerefs ∧
    d.valuerefs.length = d.data.length ∧
    d.valuerefs.filterMap (fun r => deref w r.ob) = (liveItems w d).map (·.2)

theorem wvdIters_proven : WvdIters := by
  intro K _ w d d' s
  have fm1 : ∀ l : List (Ent K (KRef K)), l.filterMap (keyF w) = (l.filterMap (itemF w)).map (·.1) := by
    intro l
    induction l with
    | nil => rfl
    | cons e rest ih =>
      simp only [List.filterMap_cons, keyF, itemF]
      cases deref w e.2.2.ob <;> simp [ih]
  have fm2 : ∀ l : List (Ent K (KRef K)), l.filterMap (valueF w) = (l.filterMap (itemF w)).map (·.2) := by
    intro l
    induction l with
    | nil => rfl
    | cons e rest ih =>
      simp only [List.filterMap_cons, valueF, itemF]
      cases deref w e.2.2.ob <;> simp [ih]
  have fm3 : ∀ l : List (Ent K (KRef K)), l.filterMap (refF w) = l.map (·.2.2) := by
    intro l
    induction l with
    | nil => rfl
    | cons e rest ih => simp [refF, ih]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (genNext_spec itemF d.data w (some s)).1
  · exact (genNext_spec valueF d.data w (some s)).1
  · exact (genNext_spec keyF d.data w (some s)).1
  · have := (genNext_spec refF d.data w (some s)).1
    simp only [irefsNext, this, Option.getD_some, fm3]
    cases s <;> rfl
  · exact drain_fresh itemF d.data w
  · rw [show d.keysNext w = genNext keyF d.data w from rfl, drain_fresh, fm1]; rfl
  · rw [show d.valuesNext w = genNext valueF d.data w from rfl, drain_fresh, fm2]; rfl
  · rw [show d.irefsNext w = genNext refF d.data w from rfl, drain_fresh, fm3]; rfl
  · simp [valuerefs]
  · simp only [valuerefs, liveItems]
    induction d.data with
    | nil => rfl
    | cons e rest ih =>
      simp only [List.map_cons, List.filterMap_cons]
      cases deref w e.2.2.ob <;> simp [ih]

/-! ### `popitem` -/

/-- `popitem` pops from the end, as `dict.popitem` does, and skips dead references: it returns the
last live item and drops everything after it. With no live item it raises the `KeyError` of the
empty dict, after emptying `data`. No key is hashed. -/
def WvdPopitem : Prop :=
  ∀ (K : Type) [DecidableEq K] (w : World) (d : WVD K),
    (liveItems w d = [] → (d.popitem w).2 = .error popEmpty ∧ (d.popitem w).1.data = []) ∧
    (∀ pre k v, liveItems w d = pre ++ [(k, v)] → (d.popitem w).2 = .ok (k, v) ∧
      liveItems w (d.popitem w).1 = pre)

theorem popitem_loop (w : World) :
    ∀ (n : Nat) (d : WVD K), d.data.length = n →
      (liveItems w d = [] → (popitemLoop w (n + 1) d).2 = .error popEmpty ∧
        (popitemLoop w (n + 1) d).1.data = []) ∧
      (∀ pre k v, liveItems w d = pre ++ [(k, v)] → (popitemLoop w (n + 1) d).2 = .ok (k, v) ∧
        liveItems w (popitemLoop w (n + 1) d).1 = pre) := by
  intro n
  induction n with
  | zero =>
    intro d hn
    have hq : d.data = [] := List.length_eq_zero_iff.1 hn
    have hp : popitemLoop w 1 d = (d, .error popEmpty) := by
      simp [popitemLoop, dPopLast, hq]
    constructor
    · intro _; simp [hp, hq]
    · intro pre k v h
      simp [liveItems, hq] at h
  | succ n ih =>
    intro d hn
    have hne : d.data ≠ [] := by
      intro e
      simp [e] at hn
    obtain ⟨init, p, hd⟩ : ∃ init p, d.data = init ++ [p] :=
      ⟨d.data.dropLast, d.data.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    obtain ⟨k0, h0, r0⟩ := p
    let d' : WVD K := { d with data := init }
    have hlen : d'.data.length = n := by
      simp [d', hd] at hn ⊢
      omega
    have hpop : dPopLast d.data = some ((k0, h0, r0), init) := by simp [dPopLast, hd]
    have hlive : liveItems w d = liveItems w d' ++
        match deref w r0.ob with
        | some o => [(k0, o)]
        | none => [] := by
      simp only [liveItems, hd, d', List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
      cases deref w r0.ob <;> simp
    obtain ⟨i1, i2⟩ := ih d' hlen
    cases hr : deref w r0.ob with
    | none =>
      have hstep : popitemLoop w (n + 1 + 1) d = popitemLoop w (n + 1) d' := by
        rw [popitemLoop]
        simp only [hpop, hr]
        rfl
      rw [hstep]
      rw [hr] at hlive
      simp only [List.append_nil] at hlive
      rw [hlive]
      exact ⟨i1, i2⟩
    | some o =>
      have hstep : popitemLoop w (n + 1 + 1) d = (d', .ok (k0, o)) := by
        rw [popitemLoop]
        simp only [hpop, hr]
        rfl
      rw [hstep]
      rw [hr] at hlive
      simp only at hlive
      rw [hlive]
      constructor
      · intro h; simp at h
      · intro pre k v h
        have h2 := List.append_inj' h rfl
        simp only [List.cons.injEq, Prod.mk.injEq, and_true] at h2
        obtain ⟨h3, h4, h5⟩ := h2
        subst h3 h4 h5
        exact ⟨rfl, rfl⟩

theorem wvdPopitem_proven : WvdPopitem := by
  intro K _ w d
  exact popitem_loop w d.data.length d rfl

/-! ### Stores in turn -/

/-- The values written by a list of stores of objects. -/
def refsOf (b : Bool) (l : List (K × Nat)) : List (K × KRef K) := l.map (fun kv => (kv.1, ⟨kv.2, b, kv.1⟩))

def objsOf (l : List (K × Nat)) : List (K × PV) := l.map (fun kv => (kv.1, PV.obj kv.2))

/-- A sequence of stores of objects, with identity keys: `dSet` in turn. -/
theorem storeAll_objs {ops : KOps K} (hp : Plain ops) : ∀ (l : List (K × Nat)) (rest : List (Py (K × PV)))
    (stop : Option PyExc) (d : WVD K), ∃ d', strip d'.data =
      l.foldl (fun acc kv => dSet acc kv.1 ⟨kv.2, d.eager, kv.1⟩) (strip d.data) ∧ d'.eager = d.eager ∧
      storeAll ops ((objsOf l).map Except.ok ++ rest) stop d = storeAll ops rest stop d' := by
  intro l
  induction l with
  | nil => intro rest stop d; exact ⟨d, rfl, rfl, rfl⟩
  | cons p t ih =>
    intro rest stop d
    obtain ⟨k, o⟩ := p
    obtain ⟨d1, h1, h2, h3⟩ := setitem_plain hp d k o
    obtain ⟨d2, e1, e2, e3⟩ := ih rest stop d1
    refine ⟨d2, ?_, by rw [e2, h3], ?_⟩
    · rw [e1, h2, h3]; rfl
    · simp only [objsOf, List.map_cons, List.cons_append, storeAll, h1]
      exact e3

theorem setAll_objs {ops : KOps K} (hp : Plain ops) : ∀ (l : List (K × Nat)) (d : WVD K),
    ∃ d', setAll ops (objsOf l) d = .ok d' ∧ strip d'.data =
      l.foldl (fun acc kv => dSet acc kv.1 ⟨kv.2, d.eager, kv.1⟩) (strip d.data) ∧ d'.eager = d.eager := by
  intro l
  induction l with
  | nil => intro d; exact ⟨d, rfl, rfl, rfl⟩
  | cons p t ih =>
    intro d
    obtain ⟨k, o⟩ := p
    obtain ⟨d1, h1, h2, h3⟩ := setitem_plain hp d k o
    obtain ⟨d2, e1, e2, e3⟩ := ih d1
    refine ⟨d2, ?_, ?_, by rw [e3, h3]⟩
    · simp only [objsOf, List.map_cons, setAll, h1]; exact e1
    · rw [e2, h2, h3]; rfl

/-- The live entries, as key and object id. -/
def liveRefs (w : World) (d : WVD K) : List (K × Nat) :=
  d.data.filterMap (fun e => if alive w e.2.2.ob then some (e.1, e.2.2.ob) else none)

theorem liveItems_eq (w : World) (d : WVD K) : liveItems w d = objsOf (liveRefs w d) := by
  simp only [liveItems, liveRefs, objsOf]
  induction d.data with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.filterMap_cons]
    by_cases h : alive w e.2.2.ob = true
    · have : deref w e.2.2.ob = some (.obj e.2.2.ob) := by simp [deref, h]
      simp only [this, h, if_true, Option.map_some, List.map_cons, ih]
    · have : deref w e.2.2.ob = none := by simp [deref, h]
      simp only [this, h, Bool.false_eq_true, if_false, Option.map_none, ih]

theorem liveRefs_keys (w : World) (d : WVD K) (hd : Keys (strip d.data)) : Keys (liveRefs w d) := by
  unfold Keys strip liveRefs at *
  have hsub : ∀ l : List (Ent K (KRef K)),
      ((l.filterMap (fun e => if alive w e.2.2.ob then some (e.1, e.2.2.ob) else none)).map (·.1)).Sublist
        (l.map (fun e => e.1)) := by
    intro l
    induction l with
    | nil => simp
    | cons e rest ih =>
      simp only [List.filterMap_cons]
      by_cases h : alive w e.2.2.ob = true
      · simp only [h, if_true, List.map_cons]; exact ih.cons_cons e.1
      · simp only [h, Bool.false_eq_true, if_false, List.map_cons]; exact ih.cons e.1
  have : (d.data.map (fun e => e.1)).Nodup := by simpa [List.map_map, Function.comp_def] using hd
  exact (hsub d.data).nodup this

theorem liveRefs_alive (w : World) (d : WVD K) : ∀ kv ∈ liveRefs w d, alive w kv.2 = true := by
  intro kv h
  simp only [liveRefs, List.mem_filterMap] at h
  obtain ⟨a, _, h2⟩ := h
  split at h2
  · rename_i h3
    simp only [Option.some.injEq] at h2
    subst h2
    exact h3
  · cases h2

theorem fold_fresh (b : Bool) : ∀ (l : List (K × Nat)) (acc : List (K × KRef K)),
    (acc.map (·.1) ++ l.map (·.1)).Nodup →
      l.foldl (fun acc kv => dSet acc kv.1 ⟨kv.2, b, kv.1⟩) acc = acc ++ refsOf b l := by
  intro l
  induction l with
  | nil => intro acc _; simp [refsOf]
  | cons p rest ih =>
    intro acc h
    obtain ⟨k, o⟩ := p
    have hk : k ∉ acc.map (·.1) := by
      intro hm
      exact (List.nodup_append.1 h).2.2 k hm k (by simp) rfl
    simp only [List.foldl_cons]
    rw [dSet_absent _ _ _ hk, ih]
    · simp [refsOf]
    · simpa using h

theorem liveL_refsOf (w : World) (b : Bool) (l : List (K × Nat)) (hl : ∀ kv ∈ l, alive w kv.2 = true) :
    liveL w (refsOf b l) = objsOf l := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    simp only [refsOf, liveL, List.map_cons, List.filterMap_cons, objsOf] at ih ⊢
    rw [show deref w p.2 = some (.obj p.2) by simp [deref, hl p (by simp)]]
    simp only [Option.map_some]
    rw [ih (fun kv h => hl kv (by simp [h]))]

/-- `copy` makes a new dictionary (with the removing callback) holding the same live items in order,
for identity keys with distinct stored keys. Dead entries do not come along. -/
def WvdCopy : Prop :=
  ∀ (K : Type) [DecidableEq K] (ops : KOps K) (w : World) (d : WVD K), Plain ops → Keys (strip d.data) →
    ∃ c, d.copy ops w = .ok c ∧ liveItems w c = liveItems w d ∧ c.eager = true ∧
      c.data.length = (liveItems w d).length

theorem copy_spec {ops : KOps K} (hp : Plain ops) (w : World) (d : WVD K) (hk : Keys (strip d.data)) :
    ∃ c, d.copy ops w = .ok c ∧ strip c.data = refsOf true (liveRefs w d) ∧ c.eager = true := by
  obtain ⟨c, h1, h2, h3⟩ := setAll_objs hp (liveRefs w d) (WVD.empty : WVD K)
  refine ⟨c, by rw [copy, liveItems_eq]; exact h1, ?_, h3⟩
  rw [h2]
  have := fold_fresh true (liveRefs w d) [] (by simpa [Keys] using liveRefs_keys w d hk)
  simpa [empty, strip] using this

theorem wvdCopy_proven : WvdCopy := by
  intro K _ ops w d hp hk
  obtain ⟨c, h1, h2, h3⟩ := copy_spec hp w d hk
  refine ⟨c, h1, ?_, h3, ?_⟩
  · rw [liveItems_strip, h2, liveL_refsOf w true _ (liveRefs_alive w d), liveItems_eq]
  · have : c.data.length = (strip c.data).length := by simp [strip]
    rw [this, h2, liveItems_eq]
    simp [refsOf, objsOf]

/-! ### `|`, `|=` -/

/-- The value after a sequence of writes: the last write to `k`, else `dflt`. -/
def ovr {β : Type} (items : List (K × β)) (dflt : Option β) (k : K) : Option β :=
  items.foldl (fun acc kv => if kv.1 = k then some kv.2 else acc) dflt

theorem dGet_fold (b : Bool) (items : List (K × Nat)) : ∀ (base : List (K × KRef K)) (k : K),
    (dGet (items.foldl (fun acc kv => dSet acc kv.1 ⟨kv.2, b, kv.1⟩) base) k).map (·.ob) =
      ovr items ((dGet base k).map (·.ob)) k := by
  induction items with
  | nil => intro base k; rfl
  | cons p rest ih =>
    intro base k
    simp only [List.foldl_cons, ih, ovr]
    congr 1
    simp only [dGet_dSet]
    split <;> simp

theorem dGet_refsOf (b : Bool) (l : List (K × Nat)) (k : K) :
    (dGet (refsOf b l) k).map (·.ob) = dGet l k := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨x, o⟩ := p
    simp only [refsOf, List.map_cons, dGet_cons] at ih ⊢
    split
    · rfl
    · exact ih

/-- The items `dict(pairs)` gives, as key and object id. -/
def dictPairs (l : List (K × Nat)) : List (K × Nat) := l.foldl (fun a kv => dSet a kv.1 kv.2) []

/-- `d | other`, `other | d`, `d |= other`, for identity keys: in `d | other` a key takes `other`'s
value and otherwise `d`'s live value; in `other | d` a live value of `d` wins, as in
`{**other, **d}`. Anything but a `Mapping` gives `NotImplemented`. `d |= other` updates `d` like
`update`, so an iterable of pairs that is no `Mapping` goes through `dict()` first (its items,
`dictPairs`, are stored), and a failing `other` leaves `d` as it was. -/
def WvdOr : Prop :=
  ∀ (K : Type) [DecidableEq K] (ops : KOps K) (w : World) (d : WVD K) (items : List (K × Nat))
    (e : PyExc),
    Plain ops → Keys (strip d.data) →
    d.or_ ops w none = none ∧ d.ror ops w none = none ∧
    (∃ c, d.or_ ops w (some (objsOf items)) = some (.ok c) ∧ ∀ k,
      (dGet (strip c.data) k).map (·.ob) = ovr items (dGet (liveRefs w d) k) k) ∧
    (∃ c, d.ror ops w (some (objsOf items)) = some (.ok c) ∧ ∀ k,
      (dGet (strip c.data) k).map (·.ob) = ovr (liveRefs w d) (ovr items none k) k) ∧
    (∃ c, d.ior ops (.seq (.ok ⟨(objsOf items).map (fun kv => SeqEl.pair kv.1 kv.2), none⟩)) = (c, .ok ()) ∧
      ∀ k, (dGet (strip c.data) k).map (·.ob) = ovr (dictPairs items) ((dGet (strip d.data) k).map (·.ob)) k) ∧
    d.ior ops (.hasattrErr e) = (d, .error e) ∧
    d.ior ops (.seq (.error e)) = (d, .error e)

/-- `dict(pairs)` of objects for identity keys: `dSet` in turn. -/
theorem dictOfSeq_objs {ops : KOps K} (hp : Plain ops) : ∀ (l : List (K × Nat)) (i : Nat)
    (acc : List (Ent K PV)), ∃ dd, dictOfSeq ops none i acc ((objsOf l).map (fun kv => SeqEl.pair kv.1 kv.2)) = .ok dd ∧
      strip dd = l.foldl (fun a kv => dSet a kv.1 (PV.obj kv.2)) (strip acc) := by
  intro l
  induction l with
  | nil => intro i acc; exact ⟨acc, rfl, rfl⟩
  | cons p t ih =>
    intro i acc
    obtain ⟨k, o⟩ := p
    obtain ⟨a1, h1, h2⟩ := pSet_plain hp acc k (PV.obj o)
    obtain ⟨dd, e1, e2⟩ := ih (i + 1) a1
    refine ⟨dd, ?_, ?_⟩
    · simp only [objsOf, List.map_cons, dictOfSeq, h1]; exact e1
    · rw [e2, h2]; rfl

theorem keys_fold_dSet {β : Type} (l : List (K × β)) : ∀ acc : List (K × β), Keys acc →
    Keys (l.foldl (fun a kv => dSet a kv.1 kv.2) acc) := by
  induction l with
  | nil => intro acc h; exact h
  | cons p t ih => intro acc h; exact ih _ (Keys_dSet h _ _)

theorem fold_map_obj : ∀ (l : List (K × Nat)) (acc : List (K × Nat)),
    l.foldl (fun a kv => dSet a kv.1 (PV.obj kv.2)) (objsOf acc) = objsOf (l.foldl (fun a kv => dSet a kv.1 kv.2) acc) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons p t ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    induction acc with
    | nil => rfl
    | cons q r ihr =>
      simp only [objsOf, List.map_cons, dSet] at ihr ⊢
      split <;> simp [ihr]

theorem dictOfSeq_strip {ops : KOps K} (hp : Plain ops) (l : List (K × Nat)) :
    ∃ dd, dictOfSeq ops none 0 [] ((objsOf l).map (fun kv => SeqEl.pair kv.1 kv.2)) = .ok dd ∧
      dd.map (fun e => (Except.ok (e.1, e.2.2) : Py (K × PV))) =
        (objsOf (dictPairs l)).map (Except.ok : K × PV → Py (K × PV)) := by
  obtain ⟨dd, h1, h2⟩ := dictOfSeq_objs hp l 0 []
  refine ⟨dd, h1, ?_⟩
  have : strip dd = objsOf (dictPairs l) := by
    rw [h2]
    exact fold_map_obj l []
  rw [← this]
  simp [strip]

theorem update_mapping_objs {ops : KOps K} (hp : Plain ops) (d : WVD K) (l : List (K × Nat)) :
    ∃ c, d.update ops (.mapping (.ok ⟨(objsOf l).map Except.ok, none⟩)) = (c, .ok ()) ∧
      strip c.data = l.foldl (fun acc kv => dSet acc kv.1 ⟨kv.2, d.eager, kv.1⟩) (strip d.data) ∧
      c.eager = d.eager := by
  obtain ⟨c, h1, h2, h3⟩ := storeAll_objs hp l [] none d
  refine ⟨c, ?_, h1, h2⟩
  simp only [update]
  rw [show (objsOf l).map Except.ok = (objsOf l).map Except.ok ++ [] by simp, h3]
  simp [storeAll]

theorem wvdOr_proven : WvdOr := by
  intro K _ ops w d items e hp hk
  obtain ⟨c0, hc0, hs0, he0⟩ := copy_spec hp w d hk
  refine ⟨rfl, rfl, ?_, ?_, ?_, rfl, rfl⟩
  · obtain ⟨c, h1, h2, _⟩ := update_mapping_objs hp c0 items
    refine ⟨c, by simp [or_, hc0, h1], ?_⟩
    intro k
    rw [h2, dGet_fold, hs0, dGet_refsOf]
  · obtain ⟨c1, h1, h2, h3⟩ := update_mapping_objs hp (WVD.empty : WVD K) items
    obtain ⟨c, g1, g2, _⟩ := update_mapping_objs hp c1 (liveRefs w d)
    refine ⟨c, ?_, ?_⟩
    · simp only [ror, h1]
      rw [liveItems_eq, g1]
    · intro k
      rw [g2, dGet_fold, h2, dGet_fold]
      rfl
  · obtain ⟨dd, h1, h2⟩ := dictOfSeq_strip hp items
    obtain ⟨c, g1, g2, _⟩ := update_mapping_objs hp d (dictPairs items)
    refine ⟨c, ?_, ?_⟩
    · simp only [ior, update, h1, h2]
      simp only [update] at g1
      exact g1
    · intro k
      rw [g2, dGet_fold]

/-! ### `update`, `__init__` -/

/-- `update`. An exception from `hasattr(other, "items")`, from `other.items()` or from
`iter(other)` changes nothing. `dict(other)` is built first, so its failure changes nothing either; a
bad element is reported with its index. Otherwise the items are stored in turn, keywords after; the
first failure (an element that does not unpack, an int value, the iterable's own exception) stops
there with the earlier items stored and the keywords not applied. -/
def WvdUpdate : Prop :=
  ∀ (K : Type) [DecidableEq K] (ops : KOps K) (d : WVD K) (e : PyExc) (kw : List (K × PV)),
    d.update ops (.hasattrErr e) kw = (d, .error e) ∧
    d.update ops (.mapping (.error e)) kw = (d, .error e) ∧
    d.update ops (.seq (.error e)) kw = (d, .error e) ∧
    (∀ els stop, dictOfSeq ops stop 0 [] els = .error e →
      d.update ops (.seq (.ok ⟨els, stop⟩)) kw = (d, .error e)) ∧
    (Plain ops → ∀ (pre : List (K × Nat)) (n : Nat) (post : List (SeqEl K)) (stop : Option PyExc),
      dictOfSeq ops stop 0 [] ((objsOf pre).map (fun kv => SeqEl.pair kv.1 kv.2) ++ .badLen n :: post) =
        .error (.valueError
          s!"dictionary update sequence element #{pre.length} has length {n}; 2 is required")) ∧
    (Plain ops → ∀ (pre : List (K × Nat)) (x : Py (K × PV)) post stop err,
      (x = .error err ∨
        ∃ k m, x = .ok (k, .int m) ∧ err = .typeError "cannot create weak reference to 'int' object") →
      ∃ d', strip d'.data = pre.foldl (fun acc kv => dSet acc kv.1 ⟨kv.2, d.eager, kv.1⟩) (strip d.data) ∧
        d.update ops (.mapping (.ok ⟨(objsOf pre).map Except.ok ++ x :: post, stop⟩)) kw = (d', .error err)) ∧
    (Plain ops → ∀ (items kwo : List (K × Nat)),
      (∃ d', strip d'.data =
          (items ++ kwo).foldl (fun acc kv => dSet acc kv.1 ⟨kv.2, d.eager, kv.1⟩) (strip d.data) ∧
        d.update ops (.mapping (.ok ⟨(objsOf items).map Except.ok, none⟩)) (objsOf kwo) = (d', .ok ())) ∧
      (∃ d', strip d'.data = items.foldl (fun acc kv => dSet acc kv.1 ⟨kv.2, d.eager, kv.1⟩) (strip d.data) ∧
        d.update ops (.mapping (.ok ⟨(objsOf items).map Except.ok, some e⟩)) (objsOf kwo) = (d', .error e)))

theorem dictOfSeq_badLen {ops : KOps K} (hp : Plain ops) (n : Nat) (post : List (SeqEl K))
    (stop : Option PyExc) : ∀ (pre : List (K × Nat)) (i : Nat) (acc : List (Ent K PV)),
    dictOfSeq ops stop i acc ((objsOf pre).map (fun kv => SeqEl.pair kv.1 kv.2) ++ .badLen n :: post) =
      .error (.valueError
        s!"dictionary update sequence element #{i + pre.length} has length {n}; 2 is required") := by
  intro pre
  induction pre with
  | nil => intro i acc; simp [dictOfSeq, objsOf]
  | cons p t ih =>
    intro i acc
    obtain ⟨k, o⟩ := p
    obtain ⟨a1, h1, _⟩ := pSet_plain hp acc k (PV.obj o)
    simp only [objsOf, List.map_cons, List.cons_append, dictOfSeq, h1]
    rw [show (t.map (fun kv => (kv.1, PV.obj kv.2))).map (fun kv => SeqEl.pair kv.1 kv.2) =
      (objsOf t).map (fun kv => SeqEl.pair kv.1 kv.2) from rfl, ih]
    simp only [List.length_cons]
    rw [show i + 1 + t.length = i + (t.length + 1) by omega]

theorem wvdUpdate_proven : WvdUpdate := by
  intro K _ ops d e kw
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro els stop h
    simp [update, h]
  · intro hp pre n post stop
    have := dictOfSeq_badLen hp n post stop pre 0 []
    simpa using this
  · intro hp pre x post stop err hx
    obtain ⟨d', h1, h2, h3⟩ := storeAll_objs hp pre (x :: post) stop d
    refine ⟨d', h1, ?_⟩
    simp only [update, h3]
    rcases hx with hx | ⟨k, m, hx, he⟩
    · subst hx; rfl
    · subst hx he
      simp [storeAll, setitem, KRef.new, refOf]
  · intro hp items kwo
    obtain ⟨d1, h1, h2, h3⟩ := storeAll_objs hp items [] none d
    obtain ⟨d2, g1, g2, g3⟩ := storeAll_objs hp kwo [] none d1
    obtain ⟨d3, f1, f2, f3⟩ := storeAll_objs hp items [] (some e) d
    refine ⟨⟨d2, ?_, ?_⟩, ⟨d3, f1, ?_⟩⟩
    · rw [g1, h1, h2, List.foldl_append]
    · simp only [update]
      rw [show (objsOf items).map Except.ok = (objsOf items).map Except.ok ++ [] by simp, h3]
      simp only [storeAll]
      rw [show (objsOf kwo).map Except.ok = (objsOf kwo).map Except.ok ++ [] by simp, g3]
      rfl
    · simp only [update]
      rw [show (objsOf items).map Except.ok = (objsOf items).map Except.ok ++ [] by simp, f3]
      rfl

/-- `WeakValueDictionary(other, **kw)`: `other` defaults to `()`, which gives an empty dictionary;
an `other` that fails raises; for identity keys a list of pairs gives the items of `dict(pairs)`,
then the keywords, all with the removing callback. -/
def WvdInit : Prop :=
  ∀ (K : Type) [DecidableEq K] (ops : KOps K) (pairs kwo : List (K × Nat)) (e : PyExc),
    WVD.init ops = .ok WVD.empty ∧
    WVD.init ops (.seq (.error e)) = .error e ∧
    WVD.init ops (.hasattrErr e) = .error e ∧
    (Plain ops → ∃ d, WVD.init ops (.seq (.ok ⟨(objsOf pairs).map (fun kv => SeqEl.pair kv.1 kv.2), none⟩))
        (objsOf kwo) = .ok d ∧ d.eager = true ∧
      strip d.data = (dictPairs pairs ++ kwo).foldl (fun acc kv => dSet acc kv.1 ⟨kv.2, true, kv.1⟩) [])

theorem wvdInit_proven : WvdInit := by
  intro K _ ops pairs kwo e
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro hp
  obtain ⟨dd, h1, h2⟩ := dictOfSeq_strip hp pairs
  obtain ⟨d1, g1, g2, g3⟩ := storeAll_objs hp (dictPairs pairs) [] none (WVD.empty : WVD K)
  obtain ⟨d2, f1, f2, f3⟩ := storeAll_objs hp kwo [] none d1
  refine ⟨d2, ?_, by rw [f2, g2]; rfl, ?_⟩
  · simp only [init, update, h1, h2]
    rw [show (objsOf (dictPairs pairs)).map Except.ok = (objsOf (dictPairs pairs)).map Except.ok ++ [] by simp, g3]
    simp only [storeAll]
    rw [show (objsOf kwo).map Except.ok = (objsOf kwo).map Except.ok ++ [] by simp, f3]
    rfl
  · rw [f1, g1, g2, List.foldl_append]
    rfl

end WVD

end PyLean.CoreLibs.Misc.Weakref
