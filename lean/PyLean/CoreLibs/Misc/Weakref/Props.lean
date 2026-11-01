import PyLean.CoreLibs.Misc.Weakref.Model

/-!
Properties of `Lib/weakref.py`. Dictionaries have distinct keys, a type invariant of `dict`, stated as
`Keys`. `liveItems` is the mapping a program sees, so the statements say that each method reads and
writes that mapping, and that a death removes what referred to the dead object.
-/

namespace PyLean.CoreLibs.Misc.Weakref

open PyLean

variable {K : Type} [DecidableEq K]

/-- `data` of a dict has distinct keys. -/
def Keys {β : Type} (d : List (K × β)) : Prop := (d.map (·.1)).Nodup

theorem dGet_cons {β : Type} (a : K) (b : β) (rest : List (K × β)) (k : K) :
    dGet ((a, b) :: rest) k = if a = k then some b else dGet rest k := by
  simp only [dGet, List.lookup]
  by_cases h : a = k
  · simp [h]
  · have : (k == a) = false := by simp [Ne.symm h]
    simp [this, h]

theorem dGet_dSet {β : Type} (d : List (K × β)) (k a : K) (v : β) :
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

theorem keys_dSet {β : Type} (d : List (K × β)) (k : K) (v : β) :
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

theorem Keys_dSet {β : Type} {d : List (K × β)} (h : Keys d) (k : K) (v : β) : Keys (dSet d k v) := by
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

theorem dGet_dDel {β : Type} {d : List (K × β)} (hd : Keys d) (k a : K) :
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
        have : ∀ (l : List (K × β)), x ∉ l.map (·.1) → dGet l x = none := by
          intro l
          induction l with
          | nil => intro _; rfl
          | cons q r ihr =>
            intro hq
            obtain ⟨u, w⟩ := q
            simp only [List.map_cons, List.mem_cons, not_or] at hq
            rw [dGet_cons, if_neg (Ne.symm hq.1)]
            exact ihr hq.2
        exact this rest hn.1
      · simp [h]
    · simp only [hx, if_false, dGet_cons, ih hn.2]
      by_cases h : x = a
      · subst h
        simp [Ne.symm hx]
      · simp [h]

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

/-! ### `WeakValueDictionary` -/

namespace WVD

/-- The function behind `liveItems`. -/
def liveF (w : World) (kv : K × KRef K) : Option (K × PV) := (deref w kv.2.ob).map (fun x => (kv.1, x))

/-- The function behind `liveRefs`. -/
def refF (w : World) (kv : K × KRef K) : Option (K × Nat) :=
  if alive w kv.2.ob then some (kv.1, kv.2.ob) else none

theorem liveItems_def (w : World) (d : WVD K) : liveItems w d = d.data.filterMap (liveF w) := rfl

/-- What a key maps to, seen through the references. -/
theorem lookup_live (w : World) (d : WVD K) (hd : Keys d.data) (key : K) :
    (liveItems w d).lookup key = (dGet d.data key).bind (fun r => deref w r.ob) := by
  obtain ⟨data, eager⟩ := d
  simp only [liveItems] at *
  induction data with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨x, r⟩ := p
    have hn : x ∉ rest.map (·.1) ∧ Keys rest := by
      unfold Keys at hd ⊢
      simpa using hd
    have hnl : (rest.filterMap (fun kv => (deref w kv.2.ob).map (fun o => (kv.1, o)))).lookup x
        = none := by
      have : ∀ (l : List (K × KRef K)), x ∉ l.map (·.1) →
          (l.filterMap (fun kv => (deref w kv.2.ob).map (fun o => (kv.1, o)))).lookup x = none := by
        intro l
        induction l with
        | nil => intro _; rfl
        | cons q t iht =>
          intro hq
          obtain ⟨u, v⟩ := q
          simp only [List.map_cons, List.mem_cons, not_or] at hq
          simp only [List.filterMap_cons]
          cases deref w v.ob with
          | none => exact iht hq.2
          | some o =>
            simp only [Option.map_some, List.lookup]
            have : (x == u) = false := by simp [hq.1]
            simp only [this]
            exact iht hq.2
      exact this rest hn.1
    simp only [List.filterMap_cons, dGet_cons]
    by_cases hk : x = key
    · subst hk
      cases hr : deref w r.ob with
      | none => simpa [hr] using hnl
      | some o => simp [hr, List.lookup]
    · have hk' : (key == x) = false := by simp [Ne.symm hk]
      have := ih hn.2
      cases hr : deref w r.ob with
      | none => simpa [hr, hk] using this
      | some o => simpa [hr, hk, List.lookup, hk'] using this

/-- `WeakValueDictionary` reads the mapping of live values: for a dictionary with distinct keys,
`__getitem__`, `get` and `in` agree with `items()`, `keys()` and `values()` are its two columns,
`itervaluerefs()` and `valuerefs()` list the references in the same order, and `__repr__` shows only
the class and the address. -/
def WvdReads : Prop :=
  ∀ (K : Type) [DecidableEq K] (r : ReprK K) (w : World) (d : WVD K) (key : K) (dflt : PV)
    (cn a : String), Keys d.data →
    ((d.items w).lookup key = none →
      d.getitem r w key = .error (.keyError (r key)) ∧ d.contains w key = false ∧
        d.get w key dflt = dflt) ∧
    (∀ v, (d.items w).lookup key = some v →
      d.getitem r w key = .ok v ∧ d.contains w key = true ∧ d.get w key dflt = v) ∧
    d.keys w = (d.items w).map (·.1) ∧
    d.values w = (d.items w).map (·.2) ∧
    d.itervaluerefs = d.valuerefs ∧
    d.len = d.data.length ∧
    WVD.repr cn a = s!"<{cn} at {a}>"

theorem wvdReads_proven : WvdReads := by
  intro K _ r w d key dflt cn a hd
  have hl := lookup_live w d hd key
  have hk : d.keys w = (d.items w).map (·.1) := by
    simp only [keys, items, liveItems]
    induction d.data with
    | nil => rfl
    | cons p rest ih =>
      simp only [List.filter_cons, List.filterMap_cons]
      cases hr : deref w p.2.ob <;> simp [hr, ih]
  have hv : d.values w = (d.items w).map (·.2) := by
    simp only [values, items, liveItems]
    induction d.data with
    | nil => rfl
    | cons p rest ih =>
      simp only [List.filterMap_cons]
      cases hr : deref w p.2.ob <;> simp [hr, ih]
  refine ⟨?_, ?_, hk, hv, rfl, rfl, rfl⟩
  · intro h
    rw [show d.items w = liveItems w d from rfl, hl] at h
    simp only [getitem, contains, get]
    cases hg : dGet d.data key with
    | none => simp
    | some wr =>
      rw [hg] at h
      have : deref w wr.ob = none := by simpa using h
      simp [this]
  · intro v h
    rw [show d.items w = liveItems w d from rfl, hl] at h
    simp only [getitem, contains, get]
    cases hg : dGet d.data key with
    | none => rw [hg] at h; simp at h
    | some wr =>
      rw [hg] at h
      have : deref w wr.ob = some v := by simpa using h
      simp [this]

/-- A death removes the object from the mapping at once: with the callback (`eager`), every entry
that referred to it leaves `data`, so `len` no longer counts it. Without the callback the entry stays
in `data` but no read sees it. In both cases the live items are the old ones without that object, in
the same order. -/
def WvdDeath : Prop :=
  ∀ (K : Type) [DecidableEq K] (w : World) (d : WVD K) (o : Nat),
    liveItems (o :: w) (d.onDeath o) = (liveItems w d).filter (fun kv => kv.2 ≠ .obj o) ∧
    (d.eager = true → ∀ kv ∈ (d.onDeath o).data, kv.2.ob ≠ o)

theorem wvdDeath_proven : WvdDeath := by
  intro K _ w d o
  have key : ∀ l : List (K × KRef K),
      l.filterMap (liveF (o :: w)) = (l.filterMap (liveF w)).filter (fun kv => kv.2 ≠ .obj o) := by
    intro l
    induction l with
    | nil => rfl
    | cons p rest ih =>
      obtain ⟨x0, r⟩ := p
      by_cases h1 : r.ob = o
      · have e1 : liveF (o :: w) (x0, r) = none := by
          simp only [liveF]
          rw [deref_cons, if_pos h1]
          rfl
        rw [List.filterMap_cons_none e1]
        cases hd : deref w r.ob with
        | none =>
          have e2 : liveF w (x0, r) = none := by simp only [liveF]; rw [hd]; rfl
          rw [List.filterMap_cons_none e2]
          exact ih
        | some v =>
          have hv := deref_some hd
          have e2 : liveF w (x0, r) = some (x0, v) := by simp only [liveF]; rw [hd]; rfl
          rw [List.filterMap_cons_some e2, List.filter_cons_of_neg (by simp [hv, h1])]
          exact ih
      · cases hd : deref w r.ob with
        | none =>
          have e1 : liveF (o :: w) (x0, r) = none := by
            simp only [liveF]
            rw [deref_cons, if_neg h1, hd]
            rfl
          have e2 : liveF w (x0, r) = none := by simp only [liveF]; rw [hd]; rfl
          rw [List.filterMap_cons_none e1, List.filterMap_cons_none e2]
          exact ih
        | some v =>
          have hv := deref_some hd
          have e1 : liveF (o :: w) (x0, r) = some (x0, v) := by
            simp only [liveF]
            rw [deref_cons, if_neg h1, hd]
            rfl
          have e2 : liveF w (x0, r) = some (x0, v) := by simp only [liveF]; rw [hd]; rfl
          rw [List.filterMap_cons_some e1, List.filterMap_cons_some e2,
            List.filter_cons_of_pos (by simp [hv, h1]), ih]
  constructor
  · unfold onDeath
    split
    · have hf : ∀ l : List (K × KRef K),
          (l.filter (fun kv => decide (kv.2.ob ≠ o))).filterMap (liveF (o :: w)) =
            l.filterMap (liveF (o :: w)) := by
        intro l
        induction l with
        | nil => rfl
        | cons p rest ih =>
          obtain ⟨x, r⟩ := p
          by_cases h1 : r.ob = o
          · have e1 : liveF (o :: w) (x, r) = none := by
              simp only [liveF]
              rw [deref_cons, if_pos h1]
              rfl
            rw [List.filter_cons_of_neg (by simp [h1]), List.filterMap_cons_none e1]
            exact ih
          · rw [List.filter_cons_of_pos (by simp [h1]), List.filterMap_cons, List.filterMap_cons, ih]
      rw [liveItems_def, liveItems_def]
      simp only
      rw [hf, key]
    · rw [liveItems_def, liveItems_def]
      rw [key]
  · intro h kv hkv
    simp only [onDeath, h, if_true] at hkv
    have := (List.mem_filter.1 hkv).2
    simpa using this

/-- A value that is alive can be read back: `d[k] = v` makes `d[k]` give `v` and leaves the other
keys. A value that cannot be weakly referenced raises `TypeError` and changes nothing. `del` removes
the key and raises `KeyError` for a missing key. -/
def WvdWrites : Prop :=
  ∀ (K : Type) [DecidableEq K] (r : ReprK K) (w : World) (d : WVD K) (k a : K) (o : Nat) (n : Int),
    Keys d.data → alive w o = true →
    (∃ d', d.setitem k (.obj o) = .ok d' ∧ d'.getitem r w k = .ok (.obj o) ∧ Keys d'.data ∧
      (a ≠ k → d'.getitem r w a = d.getitem r w a)) ∧
    d.setitem k (.int n) = .error (.typeError "cannot create weak reference to 'int' object") ∧
    (dGet d.data k = none → d.delitem r k = .error (.keyError (r k))) ∧
    (∀ d', d.delitem r k = .ok d' → d'.contains w k = false)

theorem wvdWrites_proven : WvdWrites := by
  intro K _ r w d k a o n hd ho
  refine ⟨⟨{ d with data := dSet d.data k ⟨o, k⟩ }, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [setitem, KRef.new, refOf, bind, Except.bind, pure, Except.pure]
  · simp [getitem, dGet_dSet, deref, ho]
  · exact Keys_dSet hd _ _
  · intro h
    simp only [getitem, dGet_dSet]
    simp [Ne.symm h]
  · rfl
  · intro h; simp [delitem, h]
  · intro d' h
    simp only [delitem] at h
    cases hg : dGet d.data k with
    | none => rw [hg] at h; simp at h
    | some wr =>
      rw [hg] at h
      simp only [Except.ok.injEq] at h
      subst h
      simp [contains, dGet_dDel hd]

/-- `pop` with a live value returns it and removes the key. When the key is missing, or its value
has died, the entry goes, and the default or `KeyError` is the result. `setdefault` returns a live
value and otherwise stores the default, so a dead value is replaced. -/
def WvdPopSetdefault : Prop :=
  ∀ (K : Type) [DecidableEq K] (r : ReprK K) (w : World) (d : WVD K) (k : K) (o : Nat) (a : PV)
    (wr : KRef K), Keys d.data →
    (dGet d.data k = some wr → alive w wr.ob = true →
      (d.pop r w k []).2 = .ok (.obj wr.ob) ∧ (d.pop r w k []).1.contains w k = false ∧
      d.setdefault w k a = (d, .ok (.obj wr.ob))) ∧
    ((dGet d.data k).bind (fun x => deref w x.ob) = none →
      (d.pop r w k [a]).2 = .ok a ∧ (d.pop r w k []).2 = .error (.keyError (r k)) ∧
      (alive w o = true →
        (d.setdefault w k (.obj o)).2 = .ok (.obj o) ∧
        ((d.setdefault w k (.obj o)).1).getitem r w k = .ok (.obj o)))

theorem wvdPopSetdefault_proven : WvdPopSetdefault := by
  intro K _ r w d k o a wr hd
  constructor
  · intro h1 h2
    have hderef : deref w wr.ob = some (.obj wr.ob) := by simp [deref, h2]
    refine ⟨?_, ?_, ?_⟩
    · simp [pop, h1, hderef]
    · simp [pop, h1, hderef, contains, dGet_dDel hd]
    · simp [setdefault, h1, hderef]
  · intro h
    have hs : alive w o = true → d.setdefault w k (.obj o) =
        ({ d with data := dSet d.data k ⟨o, k⟩ }, .ok (.obj o)) := by
      intro _
      cases hg : dGet d.data k with
      | none =>
        simp [setdefault, hg, setitem, KRef.new, refOf, bind, Except.bind, pure, Except.pure]
      | some x =>
        have hx : deref w x.ob = none := by
          rw [hg] at h
          simpa using h
        simp [setdefault, hg, hx, setitem, KRef.new, refOf, bind, Except.bind, pure, Except.pure]
    refine ⟨?_, ?_, ?_⟩
    · cases hg : dGet d.data k with
      | none => simp [pop, hg]
      | some x =>
        have hx : deref w x.ob = none := by
          rw [hg] at h
          simpa using h
        simp [pop, hg, hx]
    · cases hg : dGet d.data k with
      | none => simp [pop, hg]
      | some x =>
        have hx : deref w x.ob = none := by
          rw [hg] at h
          simpa using h
        simp [pop, hg, hx]
    · intro ho
      rw [hs ho]
      simp [getitem, dGet_dSet, deref, ho]

/-- `popitem` pops from the end, as `dict.popitem` does, and skips dead references: it returns the
last live item and drops everything after it. With no live item it raises the `KeyError` of the
empty dict, after emptying `data`. -/
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
    obtain ⟨k0, r0⟩ := p
    let d' : WVD K := { d with data := init }
    have hlen : d'.data.length = n := by
      simp [d', hd] at hn ⊢
      omega
    have hpop : dPopLast d.data = some ((k0, r0), init) := by simp [dPopLast, hd]
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

/-- `update` is `__setitem__` of each item in turn, keywords after `other`, and an item that cannot
be referenced stops there with the earlier ones kept. -/
def WvdUpdate : Prop :=
  ∀ (K : Type) [DecidableEq K] (d : WVD K) (items kw : List (K × Nat)),
    (d.update (some (items.map (fun kv => (kv.1, PV.obj kv.2)))) (kw.map (fun kv => (kv.1, PV.obj kv.2)))) =
      ({ d with data := (items ++ kw).foldl (fun acc kv => dSet acc kv.1 ⟨kv.2, kv.1⟩) d.data }, .ok ())

theorem wvdUpdate_proven : WvdUpdate := by
  intro K _ d items kw
  simp only [update, Option.getD_some, ← List.map_append]
  generalize items ++ kw = l
  induction l generalizing d with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k, o⟩ := p
    simp only [List.map_cons, List.foldl_cons]
    have : setitem d k (.obj o) = .ok { d with data := dSet d.data k ⟨o, k⟩ } := by
      simp [setitem, KRef.new, refOf, bind, Except.bind, pure, Except.pure]
    simp only [this]
    exact ih { d with data := dSet d.data k ⟨o, k⟩ }

/-- The live entries, as key and object id. -/
def liveRefs (w : World) (d : WVD K) : List (K × Nat) := d.data.filterMap (refF w)

theorem liveItems_eq (w : World) (d : WVD K) :
    liveItems w d = (liveRefs w d).map (fun kv => (kv.1, PV.obj kv.2)) := by
  rw [liveItems_def]
  show d.data.filterMap (liveF w) = (d.data.filterMap (refF w)).map _
  induction d.data with
  | nil => rfl
  | cons p rest ih =>
    by_cases h : alive w p.2.ob = true
    · have e1 : liveF w p = some (p.1, .obj p.2.ob) := by
        simp [liveF, deref, h]
      have e2 : refF w p = some (p.1, p.2.ob) := by
        simp [refF, h]
      rw [List.filterMap_cons_some e1, List.filterMap_cons_some e2, List.map_cons, ih]
    · have e1 : liveF w p = none := by
        simp [liveF, deref, h]
      have e2 : refF w p = none := by
        simp [refF, h]
      rw [List.filterMap_cons_none e1, List.filterMap_cons_none e2, ih]

theorem dSet_absent {β : Type} (d : List (K × β)) (k : K) (v : β) (h : k ∉ d.map (·.1)) :
    dSet d k v = d ++ [(k, v)] := by
  induction d with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨x, y⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [dSet, if_neg (Ne.symm h.1), List.cons_append, ih h.2]

theorem copy_fold :
    ∀ (l : List (K × Nat)) (n : WVD K), (n.data.map (·.1) ++ l.map (·.1)).Nodup →
      (l.map (fun kv => (kv.1, PV.obj kv.2))).foldlM (fun n kv => setitem n kv.1 kv.2) n =
        .ok { n with data := n.data ++ l.map (fun kv => (kv.1, ⟨kv.2, kv.1⟩)) } := by
  intro l
  induction l with
  | nil => intro n _; simp [pure, Except.pure]
  | cons p rest ih =>
    intro n h
    obtain ⟨k, o⟩ := p
    have hk : k ∉ n.data.map (·.1) := by
      intro hm
      have := (List.nodup_append.1 h).2.2 k hm k (by simp)
      exact this rfl
    have hs : setitem n k (.obj o) = .ok { n with data := n.data ++ [(k, ⟨o, k⟩)] } := by
      simp [setitem, KRef.new, refOf, bind, Except.bind, pure, Except.pure, dSet_absent _ _ _ hk]
    simp only [List.map_cons, List.foldlM_cons, hs, bind, Except.bind]
    have := ih { n with data := n.data ++ [(k, ⟨o, k⟩)] } (by
      simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        List.singleton_append]
      simpa using h)
    rw [this]
    simp

theorem liveRefs_keys (w : World) (d : WVD K) (hd : Keys d.data) : Keys (liveRefs w d) := by
  obtain ⟨data, eager⟩ := d
  simp only [Keys, liveRefs] at *
  induction data with
  | nil => simp
  | cons p rest ih =>
    obtain ⟨x, r⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hd
    have hsub : ∀ a ∈ (rest.filterMap (fun kv => if alive w kv.2.ob then some (kv.1, kv.2.ob)
        else none)).map (·.1), a ∈ rest.map (·.1) := by
      intro a ha
      simp only [List.mem_map, List.mem_filterMap] at ha ⊢
      obtain ⟨⟨k, v⟩, ⟨⟨u, r2⟩, h1, h2⟩, rfl⟩ := ha
      refine ⟨(u, r2), h1, ?_⟩
      simp only [refF] at h2
      split at h2
      · simp only [Option.some.injEq, Prod.mk.injEq] at h2
        exact h2.1
      · cases h2
    by_cases hal : alive w r.ob = true
    · have e2 : refF w (x, r) = some (x, r.ob) := by simp [refF, hal]
      rw [List.filterMap_cons_some e2, List.map_cons, List.nodup_cons]
      exact ⟨fun hm => hd.1 (hsub _ hm), ih hd.2⟩
    · have e2 : refF w (x, r) = none := by simp [refF, hal]
      rw [List.filterMap_cons_none e2]
      exact ih hd.2

/-- `copy` makes a new dictionary with the same live items in order and the `eager` callback of a
fresh dictionary, so dead entries do not come along. `__deepcopy__` copies the keys and shares the
values: with `deepcopy` injective on keys, it gives the items with copied keys. -/
def WvdCopy : Prop :=
  ∀ (K : Type) [DecidableEq K] (dc : K → K) (w : World) (d : WVD K), Keys d.data →
    (∀ a b, dc a = dc b → a = b) →
    (∃ c, d.copy w = .ok c ∧ liveItems w c = liveItems w d ∧ c.eager = true ∧ c.data.length =
      (liveItems w d).length) ∧
    (∃ c, d.deepcopy dc w = .ok c ∧
      liveItems w c = (liveItems w d).map (fun kv => (dc kv.1, kv.2)))

theorem live_after_copy (w : World) (l : List (K × Nat)) (hl : ∀ kv ∈ l, alive w kv.2 = true) :
    (l.map (fun kv => ((kv.1, (⟨kv.2, kv.1⟩ : KRef K))))).filterMap (liveF w) =
      l.map (fun kv => (kv.1, PV.obj kv.2)) := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    have h1 := hl p (by simp)
    have e1 : liveF w (p.1, (⟨p.2, p.1⟩ : KRef K)) = some (p.1, .obj p.2) := by
      simp [liveF, deref, h1]
    rw [List.map_cons, List.map_cons, List.filterMap_cons_some e1,
      ih (fun kv h => hl kv (by simp [h]))]

theorem live_of_refs (w : World) (l : List (K × Nat)) (hl : ∀ kv ∈ l, alive w kv.2 = true) :
    liveItems w ({ (empty : WVD K) with
      data := [] ++ l.map (fun kv => (kv.1, (⟨kv.2, kv.1⟩ : KRef K))) }) =
      l.map (fun kv => (kv.1, PV.obj kv.2)) := by
  rw [liveItems_def]
  simp only [List.nil_append]
  exact live_after_copy w l hl

theorem fold_dc (dc : K → K) : ∀ (l : List (K × PV)) (n : WVD K),
    l.foldlM (fun n kv => setitem n (dc kv.1) kv.2) n =
      (l.map (fun kv => (dc kv.1, kv.2))).foldlM (fun n kv => setitem n kv.1 kv.2) n := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons p rest ih =>
    intro n
    simp only [List.map_cons, List.foldlM_cons, bind, Except.bind]
    cases setitem n (dc p.1) p.2 with
    | error e => rfl
    | ok n' => exact ih n'

theorem liveRefs_alive (w : World) (d : WVD K) : ∀ kv ∈ liveRefs w d, alive w kv.2 = true := by
  intro kv h
  simp only [liveRefs, List.mem_filterMap] at h
  obtain ⟨a, _, h2⟩ := h
  simp only [refF] at h2
  split at h2
  · rename_i h3
    simp only [Option.some.injEq] at h2
    subst h2
    exact h3
  · cases h2

theorem wvdCopy_proven : WvdCopy := by
  intro K _ dc w d hd hinj
  have hk := liveRefs_keys w d hd
  have hk' : Keys ((liveRefs w d).map (fun kv => (dc kv.1, kv.2))) := by
    unfold Keys at *
    rw [List.map_map]
    have : ((fun x : K × Nat => x.1) ∘ fun kv : K × Nat => (dc kv.1, kv.2)) =
        (dc ∘ fun x : K × Nat => x.1) := rfl
    rw [this, ← List.map_map]
    exact List.Pairwise.map _ (fun _ _ h e => h (hinj _ _ e)) hk
  have hmap : ((liveRefs w d).map (fun kv => (kv.1, PV.obj kv.2))).map (fun kv => (dc kv.1, kv.2)) =
      ((liveRefs w d).map (fun kv => (dc kv.1, kv.2))).map (fun kv => (kv.1, PV.obj kv.2)) := by
    simp [List.map_map, Function.comp_def]
  constructor
  · refine ⟨{ (empty : WVD K) with
      data := [] ++ (liveRefs w d).map (fun kv => (kv.1, ⟨kv.2, kv.1⟩)) }, ?_, ?_, rfl, ?_⟩
    · simp only [copy]
      rw [liveItems_eq]
      exact copy_fold (liveRefs w d) empty (by simpa [empty, Keys] using hk)
    · rw [live_of_refs w _ (liveRefs_alive w d), liveItems_eq]
    · simp [empty, liveItems_eq]
  · refine ⟨{ (empty : WVD K) with
      data := [] ++ ((liveRefs w d).map (fun kv => (dc kv.1, kv.2))).map
        (fun kv => (kv.1, ⟨kv.2, kv.1⟩)) }, ?_, ?_⟩
    · simp only [deepcopy]
      rw [fold_dc, liveItems_eq, hmap]
      exact copy_fold ((liveRefs w d).map (fun kv => (dc kv.1, kv.2))) empty
        (by simpa [empty, Keys] using hk')
    · rw [live_of_refs w _ (by
        intro kv hkv
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hkv
        exact liveRefs_alive w d a ha), liveItems_eq, hmap]

/-- The value after a sequence of writes: the last write to `k`, else `dflt`. -/
def ovr {β : Type} (items : List (K × β)) (dflt : Option β) (k : K) : Option β :=
  items.foldl (fun acc kv => if kv.1 = k then some kv.2 else acc) dflt

theorem dGet_fold (items : List (K × Nat)) : ∀ (base : List (K × KRef K)) (k : K),
    (dGet (items.foldl (fun acc kv => dSet acc kv.1 ⟨kv.2, kv.1⟩) base) k).map (·.ob) =
      ovr items ((dGet base k).map (·.ob)) k := by
  induction items with
  | nil => intro base k; rfl
  | cons p rest ih =>
    intro base k
    simp only [List.foldl_cons, ih, ovr]
    congr 1
    simp only [dGet_dSet]
    split <;> simp

/-- `d | other`, `other | d`, `d |= other`: in `d | other` a key takes `other`'s value and otherwise
`d`'s live value. In `other | d` a live value of `d` wins, as in `{**other, **d}`. Anything but a
`Mapping` gives `NotImplemented`. `|=` is `update`. -/
def WvdOr : Prop :=
  ∀ (K : Type) [DecidableEq K] (w : World) (d : WVD K) (items : List (K × Nat)),
    Keys d.data →
    let objs := items.map (fun kv => (kv.1, PV.obj kv.2))
    d.or_ w none = none ∧ d.ror w none = none ∧
    d.ior objs = d.update (some objs) ∧
    (∃ c, d.or_ w (some objs) = some (.ok c) ∧ ∀ k,
      (dGet c.data k).map (·.ob) = ovr items ((dGet (liveRefs w d) k)) k) ∧
    (∃ c, d.ror w (some objs) = some (.ok c) ∧ ∀ k,
      (dGet c.data k).map (·.ob) = ovr (liveRefs w d) (ovr items none k) k)

theorem update_objs (d : WVD K) (items : List (K × Nat)) :
    d.update (some (items.map (fun kv => (kv.1, PV.obj kv.2)))) =
      ({ d with data := items.foldl (fun acc kv => dSet acc kv.1 ⟨kv.2, kv.1⟩) d.data }, .ok ()) := by
  have := wvdUpdate_proven K d items []
  simpa using this

theorem dGet_live_map (l : List (K × Nat)) (k : K) :
    (dGet (l.map (fun kv => ((kv.1, (⟨kv.2, kv.1⟩ : KRef K))))) k).map (·.ob) = dGet l k := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨x, o⟩ := p
    simp only [List.map_cons, dGet_cons]
    split
    · rfl
    · exact ih

theorem wvdOr_proven : WvdOr := by
  intro K _ w d items hd objs
  have hk := liveRefs_keys w d hd
  have hcopy : d.copy w = .ok { (empty : WVD K) with
      data := [] ++ (liveRefs w d).map (fun kv => (kv.1, ⟨kv.2, kv.1⟩)) } := by
    simp only [copy]
    rw [liveItems_eq]
    exact copy_fold (liveRefs w d) empty (by simpa [empty, Keys] using hk)
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · refine ⟨{ (empty : WVD K) with
      data := items.foldl (fun acc kv => dSet acc kv.1 ⟨kv.2, kv.1⟩)
        ([] ++ (liveRefs w d).map (fun kv => (kv.1, ⟨kv.2, kv.1⟩))) }, ?_, ?_⟩
    · simp only [or_, hcopy, bind, Except.bind, objs, update_objs]
    · intro k
      rw [dGet_fold]
      congr 1
      simpa using dGet_live_map (liveRefs w d) k
  · refine ⟨{ (empty : WVD K) with
      data := (liveRefs w d).foldl (fun acc kv => dSet acc kv.1 ⟨kv.2, kv.1⟩)
        (items.foldl (fun acc kv => dSet acc kv.1 ⟨kv.2, kv.1⟩) []) }, ?_, ?_⟩
    · simp only [ror, objs, update_objs, liveItems_eq]
      rfl
    · intro k
      rw [dGet_fold]
      congr 1
      rw [dGet_fold]
      rfl

/-- `WeakValueDictionary(other, **kw)` is an empty dictionary updated with `other`, `dict(other)`
when `other` is a list of pairs, then `kw`. `KeyedRef(ob, callback, key)` holds the referent and the
key, and refuses what cannot be referenced. -/
def WvdInit : Prop :=
  ∀ (K : Type) [DecidableEq K] (pairs : List (K × Nat)) (key : K) (o : Nat) (n : Int) (w : World),
    (∃ d, WVD.init (pairs.map (fun kv => (kv.1, PV.obj kv.2))) = .ok d ∧ d.eager = true) ∧
    KRef.new (.obj o) key = .ok { ob := o, key } ∧
    KRef.new (.int n) key = .error (.typeError "cannot create weak reference to 'int' object") ∧
    (alive w o = true → deref w o = some (.obj o)) ∧
    deref (o :: w) o = none

theorem dictFrom_objs (pairs : List (K × Nat)) :
    ∃ l : List (K × Nat), dictFrom (pairs.map (fun kv => (kv.1, PV.obj kv.2))) =
      l.map (fun kv => (kv.1, PV.obj kv.2)) := by
  have step : ∀ (acc : List (K × Nat)) (k : K) (o : Nat),
      dSet (acc.map (fun kv => (kv.1, PV.obj kv.2))) k (PV.obj o) =
        (dSet acc k o).map (fun kv => (kv.1, PV.obj kv.2)) := by
    intro acc k o
    induction acc with
    | nil => rfl
    | cons p rest ih =>
      obtain ⟨x, y⟩ := p
      simp only [List.map_cons, dSet]
      split
      · rfl
      · simp [ih]
  have go : ∀ (ps acc : List (K × Nat)), ∃ l : List (K × Nat),
      (ps.map (fun kv => (kv.1, PV.obj kv.2))).foldl (fun d kv => dSet d kv.1 kv.2)
        (acc.map (fun kv => (kv.1, PV.obj kv.2))) = l.map (fun kv => (kv.1, PV.obj kv.2)) := by
    intro ps
    induction ps with
    | nil => intro acc; exact ⟨acc, rfl⟩
    | cons p rest ih =>
      intro acc
      obtain ⟨l, hl⟩ := ih (dSet acc p.1 p.2)
      refine ⟨l, ?_⟩
      simp only [List.map_cons, List.foldl_cons]
      rw [step]
      exact hl
  exact go pairs []

theorem wvdInit_proven : WvdInit := by
  intro K _ pairs key o n w
  refine ⟨?_, rfl, rfl, ?_, ?_⟩
  · obtain ⟨l, hl⟩ := dictFrom_objs pairs
    simp only [init, updatePairs, hl]
    have := wvdUpdate_proven K (empty : WVD K) l []
    simp only [List.map_nil, List.append_nil] at this
    rw [this]
    exact ⟨_, rfl, rfl⟩
  · intro h; simp [deref, h]
  · simp [deref, alive]

end WVD

/-! ### `WeakKeyDictionary` -/

namespace WKD

variable {V : Type}

/-- The value stored for `a`. -/
def valOf (q : Eqv) (w : World) (d : WKD V) (a : Nat) : Option V := (find q w d a).map (·.2)

/-- `__eq__` on the key objects is an equivalence, the rule for hashable objects. -/
structure EqvOk (q : Eqv) : Prop where
  refl : ∀ a, q a a = true
  symm : ∀ a b, q a b = q b a
  trans : ∀ a b c, q a b = true → q b c = true → q a c = true

theorem find_map_value {q : Eqv} {w : World} (r : WRef) (v0 value : V) (key : Nat) :
    ∀ l : List (WRef × V), l.find? (fun kv => refEq q w kv.1 key) = some (r, v0) →
      (l.map (fun kv => if kv.1 = r then (r, value) else kv)).find?
        (fun kv => refEq q w kv.1 key) = some (r, value) := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons p rest ih =>
    intro h
    obtain ⟨x, y⟩ := p
    simp only [List.find?_cons, List.map_cons] at h ⊢
    by_cases hm : refEq q w x key = true
    · simp only [hm] at h
      have e : x = r := by simpa using (congrArg (fun o => o.map Prod.fst) h)
      subst e
      simp [hm]
    · have hm' : refEq q w x key = false := by simpa using hm
      simp only [hm'] at h
      by_cases e : x = r
      · subst e
        simp [hm', ih h]
      · simp [e, hm', ih h]

theorem find_append_none {q : Eqv} {w : World} (r : WRef) (v : V) (key : Nat) :
    ∀ l : List (WRef × V), l.find? (fun kv => refEq q w kv.1 key) = none →
      refEq q w r key = true →
      (l ++ [(r, v)]).find? (fun kv => refEq q w kv.1 key) = some (r, v) := by
  intro l
  induction l with
  | nil => intro _ h; simp [h]
  | cons p rest ih =>
    intro h h2
    simp only [List.find?_cons] at h
    cases hp : refEq q w p.1 key with
    | true => simp [hp] at h
    | false =>
      simp only [hp] at h
      simp [hp, ih h h2]

theorem setRef_same (q : Eqv) (hq : EqvOk q) (w : World) (d : WKD V) (k : Nat) (v : V)
    (hk : alive w k = true) : valOf q w (setRef q w d k v) k = some v := by
  unfold valOf setRef
  cases hf : find q w d k with
  | none =>
    simp only [find] at hf ⊢
    have : (d.data ++ [((⟨d.nextRid, k⟩ : WRef), v)]).find? (fun kv => refEq q w kv.1 k) =
        some ((⟨d.nextRid, k⟩ : WRef), v) :=
      find_append_none (⟨d.nextRid, k⟩ : WRef) v k _ hf (by simp [refEq, hk, hq.refl])
    simp [this]
  | some p =>
    obtain ⟨r, v0⟩ := p
    simp only [find] at hf ⊢
    rw [find_map_value r v0 v k _ hf]
    rfl

theorem refEq_other {q : Eqv} (hq : EqvOk q) {w : World} {k a : Nat} (hka : q k a = false) (r : WRef)
    (hr : refEq q w r k = true) : refEq q w r a = false := by
  simp only [refEq, Bool.and_eq_true] at hr
  have h3 := hr.2
  simp only [refEq]
  cases h4 : q r.ob a with
  | false => simp
  | true =>
    have := hq.trans k r.ob a (by rw [hq.symm]; exact h3) h4
    rw [hka] at this
    cases this

end WKD

end PyLean.CoreLibs.Misc.Weakref
