import PyLean.CoreLibs.Misc.Weakref.Props

/-! Properties of `WeakKeyDictionary`, `WeakMethod` and `finalize`. -/

namespace PyLean.CoreLibs.Misc.Weakref

open PyLean

namespace WKD

variable {V : Type}

/-- The function behind `liveItems`. -/
def liveF (w : World) (kv : WRef × V) : Option (PV × V) := (deref w kv.1.ob).map (fun x => (x, kv.2))

/-- The function behind `livePairs`. -/
def pairF (w : World) (kv : WRef × V) : Option (Nat × V) :=
  if alive w kv.1.ob then some (kv.1.ob, kv.2) else none

theorem liveItems_def (w : World) (d : WKD V) : liveItems w d = d.data.filterMap (liveF w) := rfl

/-- A key that cannot be weakly referenced: `in` says `False`, and the other reads and writes raise
the `TypeError` of `ref()`. This is the one place `__contains__` differs from `__getitem__`
(Lib/weakref.py:359-364). -/
def WkdNonWeak : Prop :=
  ∀ (V : Type) (q : Eqv) (w : World) (d : WKD V) (n : Int) (v : V),
    let e : PyExc := .typeError "cannot create weak reference to 'int' object"
    d.contains q w (.int n) = false ∧ d.getitem q w (.int n) = .error e ∧
    d.get q w (.int n) v = .error e ∧ d.setitem q w (.int n) v = .error e ∧
    d.delitem q w (.int n) = .error e ∧ (d.pop q w (.int n) [v]).2 = .error e ∧
    (d.setdefault q w (.int n) v).2 = .error e

theorem wkdNonWeak_proven : WkdNonWeak := by
  intro V q w d n v e
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Reads agree: for an object key, `d[k]`, `get`, `in` report the entry whose `ref` equals `ref(k)`,
`keys()` and `values()` are the columns of `items()`, `keyrefs()` lists every `ref`, and `__repr__`
shows only the class and the address. -/
def WkdReads : Prop :=
  ∀ (V : Type) (q : Eqv) (w : World) (d : WKD V) (k : Nat) (dflt : V) (cn a : String),
    (valOf q w d k = none →
      d.getitem q w (.obj k) = .error keyErr ∧ d.contains q w (.obj k) = false ∧
      d.get q w (.obj k) dflt = .ok dflt) ∧
    (∀ v, valOf q w d k = some v →
      d.getitem q w (.obj k) = .ok v ∧ d.contains q w (.obj k) = true ∧
      d.get q w (.obj k) dflt = .ok v) ∧
    d.keys w = (d.items w).map (·.1) ∧
    d.values w = (d.items w).map (·.2) ∧
    d.keyrefs.length = d.len ∧
    WKD.repr cn a = s!"<{cn} at {a}>"

theorem wkdReads_proven : WkdReads := by
  intro V q w d k dflt cn a
  have hk : d.keys w = (d.items w).map (·.1) := by
    simp only [keys, items, liveItems]
    induction d.data with
    | nil => rfl
    | cons p rest ih =>
      simp only [List.filterMap_cons]
      cases hr : deref w p.1.ob <;> simp [ih]
  have hv : d.values w = (d.items w).map (·.2) := by
    simp only [values, items, liveItems]
    induction d.data with
    | nil => rfl
    | cons p rest ih =>
      simp only [List.filter_cons, List.filterMap_cons]
      cases hr : deref w p.1.ob <;> simp [hr, ih]
  refine ⟨?_, ?_, hk, hv, by simp [keyrefs, len], rfl⟩
  · intro h
    have hf : find q w d k = none := by simpa [valOf] using h
    simp [getitem, contains, get, refOf, hf, bind, Except.bind, pure, Except.pure]
  · intro v h
    simp only [valOf] at h
    cases hf : find q w d k with
    | none => simp [hf] at h
    | some p =>
      obtain ⟨r, v'⟩ := p
      simp only [hf, Option.map_some, Option.some.injEq] at h
      subst h
      simp [getitem, contains, get, refOf, hf, bind, Except.bind, pure, Except.pure]

theorem find?_upd_other {q : Eqv} {w : World} (r : WRef) (value : V) (a : Nat)
    (hr : refEq q w r a = false) : ∀ l : List (WRef × V),
    (l.map (fun kv => if kv.1 = r then (r, value) else kv)).find? (fun kv => refEq q w kv.1 a) =
      l.find? (fun kv => refEq q w kv.1 a) := by
  intro l
  induction l with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨x, y⟩ := p
    simp only [List.map_cons, List.find?_cons]
    by_cases e : x = r
    · subst e
      simp [hr, ih]
    · simp only [e, if_false]
      cases h : refEq q w x a <;> simp [ih]

theorem find?_append_other {q : Eqv} {w : World} (r : WRef) (v : V) (a : Nat)
    (hr : refEq q w r a = false) (l : List (WRef × V)) :
    (l ++ [(r, v)]).find? (fun kv => refEq q w kv.1 a) = l.find? (fun kv => refEq q w kv.1 a) := by
  rw [List.find?_append]
  simp [hr]

theorem setRef_other (q : Eqv) (hq : EqvOk q) (w : World) (d : WKD V) (k a : Nat) (v : V)
    (hka : q k a = false) : valOf q w (setRef q w d k v) a = valOf q w d a := by
  unfold valOf setRef
  cases hf : find q w d k with
  | none =>
    simp only [find]
    rw [find?_append_other _ _ _ (by simp [refEq, hka])]
  | some p =>
    obtain ⟨r, v0⟩ := p
    have hm : refEq q w r k = true := by
      have := List.find?_some hf
      simpa using this
    simp only [find]
    rw [find?_upd_other r v a (refEq_other hq hka r hm)]

/-- Writes through an object key: with `__eq__` an equivalence, `d[k] = v` makes `d[k]` give `v` for
a live `k` and leaves every key that does not compare equal to `k`. An equal key is the same key, so
it sees `v` too. -/
def WkdWrites : Prop :=
  ∀ (V : Type) (q : Eqv) (w : World) (d : WKD V) (k a : Nat) (v : V), EqvOk q → alive w k = true →
    (∃ d', d.setitem q w (.obj k) v = .ok d' ∧ d'.getitem q w (.obj k) = .ok v ∧
      (q k a = false → valOf q w d' a = valOf q w d a))

theorem wkdWrites_proven : WkdWrites := by
  intro V q w d k a v hq hk
  refine ⟨setRef q w d k v, by simp [setitem, refOf, bind, Except.bind, pure, Except.pure], ?_,
    fun h => setRef_other q hq w d k a v h⟩
  have := setRef_same q hq w d k v hk
  exact ((wkdReads_proven V q w _ k v "" "").2.1 v this).1

/-- `del` removes the entry for `k`, and `KeyError` is the result when there is none. `pop` returns
and removes the value or takes the default or raises. `setdefault` keeps an existing value and stores
the default otherwise. -/
def WkdPopSetdefault : Prop :=
  ∀ (V : Type) (q : Eqv) (w : World) (d : WKD V) (k : Nat) (v dflt : V), EqvOk q → alive w k = true →
    (valOf q w d k = none →
      d.delitem q w (.obj k) = .error keyErr ∧
      (d.pop q w (.obj k) []).2 = .error keyErr ∧ (d.pop q w (.obj k) [dflt]).2 = .ok dflt ∧
      (d.setdefault q w (.obj k) dflt).2 = .ok dflt ∧
      valOf q w (d.setdefault q w (.obj k) dflt).1 k = some dflt) ∧
    (valOf q w d k = some v →
      (d.pop q w (.obj k) []).2 = .ok v ∧
      (d.setdefault q w (.obj k) dflt) = (d, .ok v))

theorem wkdPopSetdefault_proven : WkdPopSetdefault := by
  intro V q w d k v dflt hq hk
  constructor
  · intro h
    have hf : find q w d k = none := by simpa [valOf] using h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [delitem, refOf, hf, bind, Except.bind]
    · simp [pop, refOf, hf]
    · simp [pop, refOf, hf]
    · simp [setdefault, refOf, hf]
    · simp only [setdefault, refOf, hf]
      exact setRef_same q hq w d k dflt hk
  · intro h
    simp only [valOf] at h
    cases hf : find q w d k with
    | none => simp [hf] at h
    | some p =>
      obtain ⟨r, v'⟩ := p
      simp only [hf, Option.map_some, Option.some.injEq] at h
      subst h
      simp [pop, setdefault, refOf, hf]

/-- A death removes the key at once, exactly as for `WeakValueDictionary`: live items lose that
object, and with the callback the entry leaves `data`. -/
def WkdDeath : Prop :=
  ∀ (V : Type) (w : World) (d : WKD V) (o : Nat),
    liveItems (o :: w) (d.onDeath o) = (liveItems w d).filter (fun kv => kv.1 ≠ .obj o) ∧
    (d.eager = true → ∀ kv ∈ (d.onDeath o).data, kv.1.ob ≠ o)

theorem wkdDeath_proven : WkdDeath := by
  intro V w d o
  have key : ∀ l : List (WRef × V),
      l.filterMap (liveF (o :: w)) = (l.filterMap (liveF w)).filter (fun kv => kv.1 ≠ .obj o) := by
    intro l
    induction l with
    | nil => rfl
    | cons p rest ih =>
      obtain ⟨r, x0⟩ := p
      by_cases h1 : r.ob = o
      · have e1 : liveF (o :: w) (r, x0) = none := by
          simp only [liveF]
          rw [deref_cons, if_pos h1]
          rfl
        rw [List.filterMap_cons_none e1]
        cases hd : deref w r.ob with
        | none =>
          have e2 : liveF w (r, x0) = none := by simp only [liveF]; rw [hd]; rfl
          rw [List.filterMap_cons_none e2]
          exact ih
        | some v =>
          have hv := deref_some hd
          have e2 : liveF w (r, x0) = some (v, x0) := by simp only [liveF]; rw [hd]; rfl
          rw [List.filterMap_cons_some e2, List.filter_cons_of_neg (by simp [hv, h1])]
          exact ih
      · cases hd : deref w r.ob with
        | none =>
          have e1 : liveF (o :: w) (r, x0) = none := by
            simp only [liveF]
            rw [deref_cons, if_neg h1, hd]
            rfl
          have e2 : liveF w (r, x0) = none := by simp only [liveF]; rw [hd]; rfl
          rw [List.filterMap_cons_none e1, List.filterMap_cons_none e2]
          exact ih
        | some v =>
          have hv := deref_some hd
          have e1 : liveF (o :: w) (r, x0) = some (v, x0) := by
            simp only [liveF]
            rw [deref_cons, if_neg h1, hd]
            rfl
          have e2 : liveF w (r, x0) = some (v, x0) := by simp only [liveF]; rw [hd]; rfl
          rw [List.filterMap_cons_some e1, List.filterMap_cons_some e2,
            List.filter_cons_of_pos (by simp [hv, h1]), ih]
  constructor
  · unfold onDeath
    split
    · have hf : ∀ l : List (WRef × V),
          (l.filter (fun kv => decide (kv.1.ob ≠ o))).filterMap (liveF (o :: w)) =
            l.filterMap (liveF (o :: w)) := by
        intro l
        induction l with
        | nil => rfl
        | cons p rest ih =>
          obtain ⟨r, x⟩ := p
          by_cases h1 : r.ob = o
          · have e1 : liveF (o :: w) (r, x) = none := by
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

/-- `popitem` returns the last entry with a live key, dropping what is behind it, and raises the
`KeyError` of the empty dict when none is left. -/
def WkdPopitem : Prop :=
  ∀ (V : Type) (w : World) (d : WKD V),
    (liveItems w d = [] → (d.popitem w).2 = .error popEmpty ∧ (d.popitem w).1.data = []) ∧
    (∀ pre k v, liveItems w d = pre ++ [(k, v)] → (d.popitem w).2 = .ok (k, v) ∧
      liveItems w (d.popitem w).1 = pre)

theorem popitem_loop (w : World) :
    ∀ (n : Nat) (d : WKD V), d.data.length = n →
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
    obtain ⟨r0, v0⟩ := p
    let d' : WKD V := { d with data := init }
    have hlen : d'.data.length = n := by
      simp [d', hd] at hn ⊢
      omega
    have hpop : dPopLast d.data = some ((r0, v0), init) := by simp [dPopLast, hd]
    have hlive : liveItems w d = liveItems w d' ++
        match deref w r0.ob with
        | some o => [(o, v0)]
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
      have hstep : popitemLoop w (n + 1 + 1) d = (d', .ok (o, v0)) := by
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

theorem wkdPopitem_proven : WkdPopitem := by
  intro V w d
  exact popitem_loop w d.data.length d rfl

/-- The value after writing `items` in order. -/
def ovrQ (q : Eqv) (items : List (Nat × V)) (dflt : Option V) (a : Nat) : Option V :=
  items.foldl (fun acc kv => if q kv.1 a then some kv.2 else acc) dflt

/-- `update` is `__setitem__` on each item in turn. -/
theorem update_objs (q : Eqv) (w : World) (d : WKD V) (items : List (Nat × V)) :
    (d.update q w (some (items.map (fun kv => (PV.obj kv.1, kv.2))))) =
      (items.foldl (fun d kv => setRef q w d kv.1 kv.2) d, .ok ()) := by
  simp only [update, Option.getD_some, Bool.false_eq_true, if_false]
  induction items generalizing d with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.map_cons, List.foldl_cons]
    have : setitem q w d (.obj p.1) p.2 = .ok (setRef q w d p.1 p.2) := by
      simp [setitem, refOf, bind, Except.bind, pure, Except.pure]
    simp only [this]
    exact ih (setRef q w d p.1 p.2)

theorem valOf_fold (q : Eqv) (hq : EqvOk q) (w : World) (a : Nat) (ha : alive w a = true) :
    ∀ (items : List (Nat × V)) (d : WKD V), (∀ kv ∈ items, alive w kv.1 = true) →
      valOf q w (items.foldl (fun d kv => setRef q w d kv.1 kv.2) d) a =
        ovrQ q items (valOf q w d a) a := by
  intro items
  induction items with
  | nil => intro d _; rfl
  | cons p rest ih =>
    intro d hal
    simp only [List.foldl_cons, ovrQ]
    rw [ih _ (fun kv h => hal kv (by simp [h]))]
    simp only [ovrQ]
    congr 1
    cases hqa : q p.1 a with
    | false => simp [setRef_other q hq w d p.1 a p.2 hqa]
    | true =>
      simp only [if_true]
      -- an equal key: the entry for `a` is the entry for `p.1`
      have h1 := setRef_same q hq w d p.1 p.2 (hal p (by simp))
      unfold valOf at h1 ⊢
      have heq : ∀ r : WRef, refEq q w r a = refEq q w r p.1 := by
        intro r
        simp only [refEq, ha, hal p (by simp)]
        cases h2 : q r.ob a <;> cases h3 : q r.ob p.1 <;> simp
        · have := hq.trans _ _ _ h3 hqa
          rw [h2] at this
          cases this
        · have := hq.trans r.ob a p.1 h2 (by rw [hq.symm]; exact hqa)
          rw [h3] at this
          cases this
      have hff : find q w (setRef q w d p.1 p.2) a = find q w (setRef q w d p.1 p.2) p.1 := by
        simp only [find, heq]
      rw [hff]
      exact h1

/-- The live entries of `d`. -/
def livePairs (w : World) (d : WKD V) : List (Nat × V) := d.data.filterMap (pairF w)

theorem liveItems_eq (w : World) (d : WKD V) :
    liveItems w d = (livePairs w d).map (fun kv => (PV.obj kv.1, kv.2)) := by
  rw [liveItems_def]
  show d.data.filterMap (liveF w) = (d.data.filterMap (pairF w)).map _
  induction d.data with
  | nil => rfl
  | cons p rest ih =>
    by_cases h : alive w p.1.ob = true
    · have e1 : liveF w p = some (.obj p.1.ob, p.2) := by
        simp [liveF, deref, h]
      have e2 : pairF w p = some (p.1.ob, p.2) := by
        simp [pairF, h]
      rw [List.filterMap_cons_some e1, List.filterMap_cons_some e2, List.map_cons, ih]
    · have e1 : liveF w p = none := by
        simp [liveF, deref, h]
      have e2 : pairF w p = none := by
        simp [pairF, h]
      rw [List.filterMap_cons_none e1, List.filterMap_cons_none e2, ih]

theorem livePairs_alive (w : World) (d : WKD V) : ∀ kv ∈ livePairs w d, alive w kv.1 = true := by
  intro kv h
  simp only [livePairs, List.mem_filterMap] at h
  obtain ⟨a, _, h2⟩ := h
  simp only [pairF] at h2
  split at h2
  · rename_i h3
    simp only [Option.some.injEq] at h2
    subst h2
    exact h3
  · cases h2

/-- `foldlM setitem` on object keys is the fold of `setRef`. -/
theorem foldM_objs (q : Eqv) (w : World) (f : V → V) :
    ∀ (items : List (Nat × V)) (n : WKD V),
      (items.map (fun kv => (PV.obj kv.1, kv.2))).foldlM
          (fun n kv => setitem q w n kv.1 (f kv.2)) n =
        .ok (items.foldl (fun d kv => setRef q w d kv.1 (f kv.2)) n) := by
  intro items
  induction items with
  | nil => intro n; rfl
  | cons p rest ih =>
    intro n
    have : setitem q w n (.obj p.1) (f p.2) = .ok (setRef q w n p.1 (f p.2)) := by
      simp [setitem, refOf, bind, Except.bind, pure, Except.pure]
    simp only [List.map_cons, List.foldlM_cons, this, bind, Except.bind]
    exact ih _

/-- The first live entry equal to `a`. -/
def valList (q : Eqv) : List (Nat × V) → Nat → Option V
  | [], _ => none
  | (k, v) :: r, a => if q k a then some v else valList q r a

theorem valOf_live (q : Eqv) (w : World) (d : WKD V) (a : Nat) (ha : alive w a = true) :
    valOf q w d a = valList q (livePairs w d) a := by
  simp only [valOf, find, livePairs]
  induction d.data with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨r, x⟩ := p
    cases hal : alive w r.ob with
    | false =>
      have e2 : pairF w (r, x) = none := by simp [pairF, hal]
      have hf : refEq q w r a = false := by simp [refEq, hal]
      rw [List.filterMap_cons_none e2, List.find?_cons_of_neg (by simp [hf])]
      exact ih
    | true =>
      have e2 : pairF w (r, x) = some (r.ob, x) := by simp [pairF, hal]
      rw [List.filterMap_cons_some e2]
      simp only [valList]
      cases hq : q r.ob a with
      | false =>
        have hf : refEq q w r a = false := by simp [refEq, hq]
        rw [List.find?_cons_of_neg (by simp [hf])]
        simpa using ih
      | true =>
        have hf : refEq q w r a = true := by simp [refEq, hq, hal, ha]
        rw [List.find?_cons_of_pos (by simp [hf])]
        simp

theorem ovr_nomatch (q : Eqv) (a : Nat) (d : Option V) :
    ∀ l : List (Nat × V), (∀ kv ∈ l, q kv.1 a = false) → ovrQ q l d a = d := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons p rest ih =>
    intro h
    simp only [ovrQ, List.foldl_cons, h p (by simp)]
    simpa [ovrQ] using ih (fun kv hk => h kv (by simp [hk]))

theorem ovr_val (q : Eqv) (hq : EqvOk q) (a : Nat) :
    ∀ l : List (Nat × V), l.Pairwise (fun x y => q x.1 y.1 = false) →
      ovrQ q l none a = valList q l a := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons p rest ih =>
    intro h
    obtain ⟨k, v⟩ := p
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 h
    simp only [ovrQ, List.foldl_cons, valList]
    cases hka : q k a with
    | false =>
      simpa [ovrQ] using ih h2
    | true =>
      simp only [if_true]
      apply ovr_nomatch q a
      intro kv hkv
      cases hv : q kv.1 a with
      | false => rfl
      | true =>
        have := hq.trans k a kv.1 hka (by rw [hq.symm]; exact hv)
        rw [h1 kv hkv] at this
        cases this

theorem valOf_empty (q : Eqv) (w : World) (a : Nat) : valOf q w (empty : WKD V) a = none := rfl

/-- `copy` and `__deepcopy__`: while the live keys are pairwise different (a dict's invariant), a
copy maps every live key to the same value, and the deep copy to a copy of the value. The keys are the
same objects, weakly held. -/
def WkdCopy : Prop :=
  ∀ (V : Type) (dc : V → V) (q : Eqv) (w : World) (d : WKD V) (a : Nat),
    EqvOk q → alive w a = true →
    (livePairs w d).Pairwise (fun x y => q x.1 y.1 = false) →
    (∃ c, d.copy q w = .ok c ∧ valOf q w c a = valOf q w d a) ∧
    (∃ c, d.deepcopy dc q w = .ok c ∧ valOf q w c a = (valOf q w d a).map dc)

theorem wkdCopy_proven : WkdCopy := by
  intro V dc q w d a hq ha hu
  have hal := livePairs_alive w d
  constructor
  · refine ⟨(livePairs w d).foldl (fun d kv => setRef q w d kv.1 kv.2) empty, ?_, ?_⟩
    · simp only [copy, liveItems_eq]
      have := foldM_objs q w (fun v : V => v) (livePairs w d) empty
      exact this
    · rw [valOf_fold q hq w a ha _ _ hal, valOf_empty, ovr_val q hq a _ hu, valOf_live q w d a ha]
  · refine ⟨(livePairs w d).foldl (fun d kv => setRef q w d kv.1 (dc kv.2)) empty, ?_, ?_⟩
    · simp only [deepcopy, liveItems_eq]
      exact foldM_objs q w dc (livePairs w d) empty
    · have hmap : (livePairs w d).foldl (fun d kv => setRef q w d kv.1 (dc kv.2)) empty =
          ((livePairs w d).map (fun kv => (kv.1, dc kv.2))).foldl
            (fun d kv => setRef q w d kv.1 kv.2) empty := by
        rw [List.foldl_map]
      rw [hmap, valOf_fold q hq w a ha _ _ (by
        intro kv hkv
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hkv
        exact hal b hb)]
      rw [valOf_empty, ovr_val q hq a _ (by
        rw [List.pairwise_map]
        exact hu), valOf_live q w d a ha]
      generalize livePairs w d = l
      induction l with
      | nil => rfl
      | cons p rest ih =>
        obtain ⟨k, v⟩ := p
        simp only [List.map_cons, valList]
        split
        · rfl
        · exact ih

/-- `d | other`, `other | d`, `d |= other`, as for `WeakValueDictionary`: on a dict `d`, a key in
`other` takes its value in `d | other`, and a live key of `d` keeps its value in `other | d`.
Anything but a `Mapping` gives `NotImplemented`. Keywords to `update` raise `TypeError`, because a
plain `str` cannot be weakly referenced, after `dict` has been applied. -/
def WkdOr : Prop :=
  ∀ (V : Type) (q : Eqv) (w : World) (d : WKD V) (items : List (Nat × V)) (a : Nat),
    EqvOk q → alive w a = true → (∀ kv ∈ items, alive w kv.1 = true) →
    (livePairs w d).Pairwise (fun x y => q x.1 y.1 = false) →
    let objs := items.map (fun kv => (PV.obj kv.1, kv.2))
    d.or_ q w none = none ∧ d.ror q w none = none ∧
    d.ior q w objs = d.update q w (some objs) ∧
    d.update q w (some objs) true =
      (d, .error (.typeError "Keyword arguments are not supported: cannot create weak reference to 'str' object")) ∧
    (∃ c, d.or_ q w (some objs) = some (.ok c) ∧ valOf q w c a = ovrQ q items (valOf q w d a) a) ∧
    (∃ c, d.ror q w (some objs) = some (.ok c) ∧
      valOf q w c a = ovrQ q (livePairs w d) (ovrQ q items none a) a)

theorem wkdOr_proven : WkdOr := by
  intro V q w d items a hq ha hit hu objs
  have hal := livePairs_alive w d
  have hcopy := (wkdCopy_proven V id q w d a hq ha hu).1
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · rfl
  · have hc : d.copy q w = .ok ((livePairs w d).foldl (fun d kv => setRef q w d kv.1 kv.2) empty) := by
      simp only [copy, liveItems_eq]
      exact foldM_objs q w (fun v : V => v) (livePairs w d) empty
    refine ⟨items.foldl (fun d kv => setRef q w d kv.1 kv.2)
      ((livePairs w d).foldl (fun d kv => setRef q w d kv.1 kv.2) empty), ?_, ?_⟩
    · simp only [or_, hc, bind, Except.bind, objs, update_objs]
    · rw [valOf_fold q hq w a ha _ _ hit]
      congr 1
      rw [valOf_fold q hq w a ha _ _ hal, valOf_empty, ovr_val q hq a _ hu, valOf_live q w d a ha]
  · refine ⟨(livePairs w d).foldl (fun d kv => setRef q w d kv.1 kv.2)
      (items.foldl (fun d kv => setRef q w d kv.1 kv.2) empty), ?_, ?_⟩
    · simp only [ror, objs, update_objs, liveItems_eq]
    · rw [valOf_fold q hq w a ha _ _ hal, valOf_fold q hq w a ha _ _ hit, valOf_empty]

/-- `WeakKeyDictionary(dict)` is an empty dictionary updated with `dict`; `dict=None` gives an empty
one; a list of pairs goes through `dict(...)` first. -/
def WkdInit : Prop :=
  ∀ (V : Type) (q : Eqv) (w : World) (items : List (Nat × V)),
    WKD.init (V := V) q w none = .ok empty ∧
    WKD.init q w (some (items.map (fun kv => (PV.obj kv.1, kv.2)))) =
      .ok (items.foldl (fun d kv => setRef q w d kv.1 kv.2) empty) ∧
    (∀ d : WKD V, d.updatePairs q w (items.map (fun kv => (PV.obj kv.1, kv.2))) =
      d.update q w (some (dictOf q (items.map (fun kv => (PV.obj kv.1, kv.2))))))

theorem wkdInit_proven : WkdInit := by
  intro V q w items
  refine ⟨rfl, ?_, fun _ => rfl⟩
  simp only [init, update_objs]

end WKD

/-! ### `WeakMethod` -/

/-- `WeakMethod`: `__new__` refuses what is not a bound method. `__call__` rebuilds the bound method
while both the object and the function live, and gives `None` otherwise. `__ne__` is the negation of
`__eq__` on two weak methods, both are `NotImplemented` against anything else, and a dead one equals
only itself. -/
def WeakMethodBasics : Prop :=
  ∀ (q : Eqv) (w : World) (m o : WM) (i : Nat) (cb : Bool) (ob f : Nat) (tp : String),
    WM.new i (.bound ob f) cb = .ok { id := i, obj := ob, func := f, alive := true, callback := cb } ∧
    WM.new i (.other tp) cb = .error (.typeError s!"argument should be a bound method, not {tp}") ∧
    (alive w m.obj = true → alive w m.func = true → m.call w = some (m.obj, m.func)) ∧
    (alive w m.obj = false → m.call w = none) ∧
    (alive w m.func = false → m.call w = none) ∧
    m.ne q w (some o) = (m.eq q w (some o)).map not ∧
    m.eq q w none = none ∧ m.ne q w none = none ∧
    (m.alive = false → m.eq q w (some o) = some (m.id == o.id))

theorem weakMethodBasics_proven : WeakMethodBasics := by
  intro q w m o i cb ob f tp
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · intro h1 h2; simp [WM.call, h1, h2]
  · intro h; simp [WM.call, h]
  · intro h; simp [WM.call, h]
  · simp only [WM.ne, WM.eq]
    split
    · simp [bne]
    · cases refCmp q w m.id m.obj o.id o.obj <;> simp
  · intro h; simp [WM.eq, h]

/-- The callback of a `WeakMethod` runs at most once: the first death of the object or the function
clears `_alive` and fires it if there is one, and later deaths do nothing. The death of anything else
changes nothing. -/
def WeakMethodCallbackOnce : Prop :=
  ∀ (m : WM) (o o' : Nat),
    (m.alive = true → (m.obj = o ∨ m.func = o) →
      m.onDeath o = ({ m with alive := false }, m.callback)) ∧
    (m.alive = false → m.onDeath o = (m, false)) ∧
    (m.obj ≠ o → m.func ≠ o → m.onDeath o = (m, false)) ∧
    ((m.onDeath o).1.alive = false → ((m.onDeath o).1.onDeath o').2 = false)

theorem weakMethodCallbackOnce_proven : WeakMethodCallbackOnce := by
  intro m o o'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h1 h2
    have : (m.obj == o || m.func == o) = true := by
      rcases h2 with h | h <;> simp [h]
    simp [WM.onDeath, h1, this]
  · intro h; simp [WM.onDeath, h]
  · intro h1 h2
    simp [WM.onDeath, h1, h2]
  · intro h
    have key : ∀ m' : WM, m'.alive = false → (m'.onDeath o').2 = false := by
      intro m' h'
      simp [WM.onDeath, h']
    exact key _ h

/-! ### `finalize` -/

namespace Fin

variable {F σ : Type}

/-- `finalize`: "The first time the finalizer is called it evaluates func ... After this the finalizer
is dead, and calling it just returns None." `detach` kills it and returns the object and function
while the object lives; `peek` returns them and leaves it alive. Once `_shutdown` is set, a call pops
the entry without running it. `atexit` reads and writes the flag of a live finalizer, and is `False`
for a dead one. -/
def FinalizeOnce : Prop :=
  ∀ (F : Type) (st : Fin F) (w : World) (self : Nat) (info : Info F) (b : Bool),
    (st.registry.map (·.1)).Nodup →
    dGet st.registry self = some info →
    (st.shutdown = false → (st.call self).2 = some info.func) ∧
    (st.shutdown = true → (st.call self).2 = none) ∧
    ((st.call self).1.call self).2 = none ∧
    (st.call self).1.isAlive self = false ∧
    st.isAlive self = true ∧
    (alive w info.obj = true →
      st.peek w self = some (.obj info.obj, info.func) ∧
      (st.detach w self).2 = some (.obj info.obj, info.func) ∧
      (st.detach w self).1.isAlive self = false) ∧
    (alive w info.obj = false → st.peek w self = none ∧ st.detach w self = (st, none)) ∧
    st.atexit self = info.atexit ∧
    (st.setAtexit self b).atexit self = b

theorem finalizeOnce_proven : FinalizeOnce := by
  intro F st w self info b hk hg
  have hdel : dGet (dDel st.registry self) self = none := by
    have := dGet_dDel (K := Nat) (β := Info F) hk self self
    simpa using this
  have hc : (st.call self).1 = { st with registry := dDel st.registry self } := by
    simp only [call, hg]
    cases st.shutdown <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [call, hg, h]
  · intro h; simp [call, hg, h]
  · rw [hc]; simp [call, hdel]
  · rw [hc]; simp [isAlive, hdel]
  · simp [isAlive, hg]
  · intro h
    have hd : deref w info.obj = some (.obj info.obj) := by simp [deref, h]
    refine ⟨by simp [peek, hg, hd], by simp [detach, hg, hd], ?_⟩
    simp [detach, hg, hd, isAlive, hdel]
  · intro h
    have hd : deref w info.obj = none := by simp [deref, h]
    exact ⟨by simp [peek, hg, hd], by simp [detach, hg, hd]⟩
  · simp [atexit, hg]
  · simp [setAtexit, hg, atexit, dGet_dSet]

/-- `finalize.__init__` registers an alive finalizer with the next index and marks the registry
dirty. A target that cannot be weakly referenced raises `TypeError` and registers nothing, but the
`atexit` hook is registered already. `__repr__` shows the object while finalizer and object live and
says `dead` otherwise. -/
def FinalizeInit : Prop :=
  ∀ (F : Type) (st : Fin F) (w : World) (self o : Nat) (n : Int) (f : F) (a b t : String),
    (st.init self (.obj o) f).2 = .ok () ∧
    (st.init self (.obj o) f).1.isAlive self = true ∧
    (st.init self (.obj o) f).1.dirty = true ∧
    (st.init self (.obj o) f).1.indexIter = st.indexIter + 1 ∧
    (st.init self (.int n) f).1.registry = st.registry ∧
    (st.init self (.int n) f).1.registeredWithAtexit = true ∧
    (dGet st.registry self = none → st.repr w self a b t = s!"<finalize object at {a}; dead>") ∧
    (∀ info, dGet st.registry self = some info → alive w info.obj = true →
      st.repr w self a b t = s!"<finalize object at {a}; for '{t}' at {b}>")

theorem finalizeInit_proven : FinalizeInit := by
  intro F st w self o n f a b t
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simp [init, refOf, isAlive, dGet_dSet, bind]
  · intro h; simp [repr, h]
  · intro info h1 h2
    simp [repr, h1, deref, h2]

theorem sorted_insert (kv : Nat × Info F) :
    ∀ l : List (Nat × Info F), l.Pairwise (fun a b => a.2.index ≤ b.2.index) →
      (insertByIndex kv l).Pairwise (fun a b => a.2.index ≤ b.2.index) := by
  intro l
  induction l with
  | nil => intro _; simp [insertByIndex]
  | cons x rest ih =>
    intro h
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 h
    simp only [insertByIndex]
    split
    · rename_i hlt
      refine List.pairwise_cons.2 ⟨?_, h⟩
      intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · omega
      · have := h1 b hb
        omega
    · rename_i hge
      refine List.pairwise_cons.2 ⟨?_, ih h2⟩
      have hmem : ∀ b ∈ insertByIndex kv rest, b = kv ∨ b ∈ rest := by
        clear ih h h1 h2
        induction rest with
        | nil => simp [insertByIndex]
        | cons y r ihr =>
          intro b hb
          simp only [insertByIndex] at hb
          split at hb
          · rcases List.mem_cons.1 hb with e | hb
            · exact .inl e
            · exact .inr hb
          · rcases List.mem_cons.1 hb with e | hb
            · exact .inr (by simp [e])
            · rcases ihr b hb with e | e
              · exact .inl e
              · exact .inr (by simp [e])
      intro b hb
      rcases hmem b hb with rfl | e
      · omega
      · exact h1 b e

theorem insert_perm (kv : Nat × Info F) (l : List (Nat × Info F)) :
    (insertByIndex kv l).Perm (kv :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x rest ih =>
    simp only [insertByIndex]
    split
    · exact List.Perm.refl _
    · exact (ih.cons x).trans (List.Perm.swap _ _ _)

/-- `_select_for_exit` lists the live finalizers marked for exit, "oldest first": a permutation of
those whose `atexit` is true, by ascending creation index. -/
def SelectForExit : Prop :=
  ∀ (F : Type) (st : Fin F),
    let l := (st.registry.filter (fun kv => kv.2.atexit)).foldr insertByIndex []
    selectForExit st = l.map (·.1) ∧ l.Perm (st.registry.filter (fun kv => kv.2.atexit)) ∧
    l.Pairwise (fun a b => a.2.index ≤ b.2.index)

theorem selectForExit_proven : SelectForExit := by
  intro F st
  refine ⟨rfl, ?_, ?_⟩
  · generalize st.registry.filter (fun kv => kv.2.atexit) = r
    induction r with
    | nil => exact List.Perm.refl _
    | cons x rest ih =>
      simp only [List.foldr_cons]
      exact (insert_perm x _).trans (ih.cons x)
  · generalize st.registry.filter (fun kv => kv.2.atexit) = r
    induction r with
    | nil => simp
    | cons x rest ih =>
      simp only [List.foldr_cons]
      exact sorted_insert x _ ih

/-- A `run` that records the function and neither touches the class state nor fails. -/
structure PlainRun (run : RunF σ F) (log : σ → List F) : Prop where
  same : ∀ f st s, (run f st s).1 = st
  ok : ∀ f st s, (run f st s).2.2 = none
  logs : ∀ f st s, log (run f st s).2.1 = log s ++ [f]

/-- `_exitfunc`: "any remaining finalizers for which the atexit attribute is true will be run in
reverse order of creation". With functions that do not fail or create finalizers, it runs each one
selected exactly once, newest first, drops them from the registry, keeps the ones with `atexit` false,
and sets `_shutdown`, so nothing can run afterwards. -/
def ExitfuncOrder : Prop :=
  ∀ (F σ : Type) (run : RunF σ F) (hook : σ → PyExc → σ) (log : σ → List F) (st : Fin F) (s : σ),
    PlainRun run log → st.dirty = false → st.shutdown = false → st.registry ≠ [] →
    (st.registry.map (·.1)).Nodup →
    let sel := selectForExit st
    let r := exitfunc run hook (sel.length + 1) st s
    r.2.2 = none ∧
    log r.2.1 = log s ++ (sel.reverse.filterMap (fun f => (dGet st.registry f).map (·.func))) ∧
    r.1.shutdown = true

theorem exit_loop_order (run : RunF σ F) (hook : σ → PyExc → σ) (log : σ → List F)
    (hr : PlainRun run log) :
    ∀ (n : Nat) (pending : List Nat) (st : Fin F) (s : σ), pending.length = n →
      st.dirty = false → st.shutdown = false → pending.Nodup →
      (st.registry.map (·.1)).Nodup →
      (exitLoop run hook (n + 1) st s (some pending)).2.2 = none ∧
      log (exitLoop run hook (n + 1) st s (some pending)).2.1 = log s ++
        (pending.reverse.filterMap (fun f => (dGet st.registry f).map (·.func))) := by
  intro n
  induction n with
  | zero =>
    intro pending st s hn hd _ _ _
    have : pending = [] := List.length_eq_zero_iff.1 hn
    subst this
    simp [exitLoop, hd]
  | succ n ih =>
    intro pending st s hn hd hsh hnd hk
    have hne : pending ≠ [] := by
      intro e
      simp [e] at hn
    obtain ⟨init, f, hp⟩ : ∃ init f, pending = init ++ [f] :=
      ⟨pending.dropLast, pending.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    subst hp
    have hl : init.length = n := by
      simp at hn
      omega
    have hnd' : init.Nodup := (List.nodup_append.1 hnd).1
    have hnf : f ∉ init := by
      intro hm
      exact (List.nodup_append.1 hnd).2.2 f hm f (by simp) rfl
    have hgl : (init ++ [f]).getLast? = some f := by simp
    have hdl : (init ++ [f]).dropLast = init := by simp
    rw [exitLoop]
    simp only [Option.isNone_some, hd, Bool.or_false, Bool.false_eq_true, if_false,
      Option.getD_some, hgl, hdl]
    cases hg : dGet st.registry f with
    | none =>
      have hc : st.call f = (st, none) := by simp [call, hg]
      simp only [hc]
      obtain ⟨a, b⟩ := ih init st s hl hd hsh hnd' hk
      refine ⟨a, ?_⟩
      rw [b]
      simp [hg]
    | some info =>
      let st' : Fin F := { st with registry := dDel st.registry f }
      have hc : st.call f = (st', some info.func) := by
        simp [call, hg, hsh, st']
      simp only [hc]
      generalize hrun : run info.func st' s = rr
      obtain ⟨st2, s2, x⟩ := rr
      have h1 : st2 = st' := by
        have := hr.same info.func st' s
        rw [hrun] at this
        exact this
      have h2 : x = none := by
        have := hr.ok info.func st' s
        rw [hrun] at this
        exact this
      have h3 : log s2 = log s ++ [info.func] := by
        have := hr.logs info.func st' s
        rw [hrun] at this
        exact this
      subst h1 h2
      simp only
      have hk' : (st'.registry.map (·.1)).Nodup := by
        have hsub : ∀ l : List (Nat × Info F), (l.map (·.1)).Nodup →
            ((dDel l f).map (·.1)).Nodup := by
          intro l
          induction l with
          | nil => simp [dDel]
          | cons p rest ih2 =>
            intro h
            obtain ⟨u, v⟩ := p
            simp only [List.map_cons, List.nodup_cons] at h
            simp only [dDel]
            split
            · exact h.2
            · simp only [List.map_cons, List.nodup_cons]
              refine ⟨?_, ih2 h.2⟩
              intro hm
              have hsubset : ∀ (l : List (Nat × Info F)), ∀ a ∈ (dDel l f).map (·.1), a ∈ l.map (·.1) := by
                intro l
                induction l with
                | nil => simp [dDel]
                | cons p2 r2 ih3 =>
                  intro a ha
                  simp only [dDel] at ha
                  split at ha
                  · simp only [List.map_cons, List.mem_cons]
                    exact .inr ha
                  · simp only [List.map_cons, List.mem_cons] at ha ⊢
                    rcases ha with e | ha
                    · exact .inl e
                    · exact .inr (ih3 a ha)
              exact h.1 (hsubset _ _ hm)
        exact hsub _ hk
      obtain ⟨a, b⟩ := ih init st' s2 hl hd hsh hnd' hk'
      refine ⟨a, ?_⟩
      rw [b, h3]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append, List.filterMap_cons, hg, Option.map_some, List.append_assoc,
        List.cons_append]
      have hrest : (init.reverse.filterMap (fun f' => (dGet st'.registry f').map (·.func))) =
          (init.reverse.filterMap (fun f' => (dGet st.registry f').map (·.func))) := by
        have hcongr : ∀ l : List Nat, f ∉ l →
            l.filterMap (fun f' => (dGet st'.registry f').map (·.func)) =
            l.filterMap (fun f' => (dGet st.registry f').map (·.func)) := by
          intro l
          induction l with
          | nil => intro _; rfl
          | cons x r ihl =>
            intro hl
            have hxf : f ≠ x := fun e => hl (by simp [e])
            have e1 : dGet st'.registry x = dGet st.registry x := by
              simp only [st', dGet_dDel hk, hxf, if_false]
            simp only [List.filterMap_cons, e1, ihl (fun h => hl (by simp [h]))]
        exact hcongr _ (fun h => hnf (List.mem_reverse.1 h))
      rw [hrest]

theorem selectForExit_nodup (st : Fin F) (hk : (st.registry.map (·.1)).Nodup) :
    (selectForExit st).Nodup := by
  obtain ⟨h1, h2, _⟩ := selectForExit_proven F st
  rw [h1]
  have hf : ((st.registry.filter (fun kv => kv.2.atexit)).map (·.1)).Nodup :=
    (List.Sublist.map _ List.filter_sublist).nodup hk
  exact ((h2.map _).nodup_iff).2 hf

theorem exitfuncOrder_proven : ExitfuncOrder := by
  intro F σ run hook log st s hr hd hsh hne hk sel r
  have hsel : sel = selectForExit st := rfl
  have hnd := selectForExit_nodup st hk
  have hstart : exitLoop run hook (sel.length + 1) st s none =
      exitLoop run hook (sel.length + 1) st s (some sel) := by
    have hst : ({ st with dirty := false } : Fin F) = st := by
      cases st
      simp only at hd
      simp [hd]
    rw [exitLoop, exitLoop]
    simp only [Option.isNone_none, Option.isNone_some, Bool.true_or, Bool.false_or, if_true, hd,
      Bool.false_eq_true, if_false, Option.getD_some, hst, hsel]
  have hempty : (!st.registry.isEmpty) = true := by
    cases hreg : st.registry with
    | nil => exact absurd hreg hne
    | cons _ _ => rfl
  have hrun : r = ({ (exitLoop run hook (sel.length + 1) st s (some sel)).1 with shutdown := true },
      (exitLoop run hook (sel.length + 1) st s (some sel)).2.1,
      (exitLoop run hook (sel.length + 1) st s (some sel)).2.2) := by
    simp only [r, exitfunc, hempty, if_true, hstart]
  obtain ⟨a, b⟩ := exit_loop_order run hook log hr sel.length sel st s rfl hd hsh hnd hk
  rw [hrun]
  exact ⟨a, b, rfl⟩

end Fin

end PyLean.CoreLibs.Misc.Weakref
