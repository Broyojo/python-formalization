import PyLean.CoreLibs.Misc.Weakref.PropsWkd

/-! Properties of `WeakValueDictionary` (Lib/weakref.py:92-274) and `KeyedRef` (:277-295). -/

namespace PyLean.CoreLibs.Misc.Weakref

open PyLean

variable {K : Type} [DecidableEq K]

namespace WVD

/-- The live items of an association list of references. -/
def liveL (w : World) (l : List (K × KRef K)) : List (K × PV) :=
  l.filterMap (fun kv => (deref w kv.2.ob).map (fun o => (kv.1, o)))

theorem liveItems_strip (w : World) (d : WVD K) : liveItems w d = liveL w (strip d.data) := by
  simp only [liveItems, liveL, strip, List.filterMap_map]
  rfl

theorem lookup_liveL (w : World) (key : K) : ∀ l : List (K × KRef K), Keys l →
    (liveL w l).lookup key = (dGet l key).bind (fun r => deref w r.ob) := by
  intro l hd
  induction l with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨x, r⟩ := p
    have hn : x ∉ rest.map (·.1) ∧ Keys rest := by
      unfold Keys at hd ⊢
      simpa using hd
    have hnl : (liveL w rest).lookup x = none := by
      have : ∀ (l : List (K × KRef K)), x ∉ l.map (·.1) → (liveL w l).lookup x = none := by
        intro l
        induction l with
        | nil => intro _; rfl
        | cons q t iht =>
          intro hq
          obtain ⟨u, v⟩ := q
          simp only [List.map_cons, List.mem_cons, not_or] at hq
          simp only [liveL, List.filterMap_cons]
          cases deref w v.ob with
          | none => exact iht hq.2
          | some o =>
            simp only [Option.map_some, List.lookup]
            have : (x == u) = false := by simp [hq.1]
            simp only [this]
            exact iht hq.2
      exact this rest hn.1
    simp only [liveL, List.filterMap_cons, dGet_cons] at hnl ih ⊢
    by_cases hk : x = key
    · subst hk
      cases hr : deref w r.ob with
      | none => simpa [hr] using hnl
      | some o => simp [hr, List.lookup]
    · have hk' : (key == x) = false := by simp [Ne.symm hk]
      have := ih hn.2
      cases hr : deref w r.ob with
      | none => simpa [hk] using this
      | some o => simpa [hk, List.lookup, hk'] using this

/-- `except KeyError:` around a read: a `KeyError`, whatever raised it, becomes `dflt`. -/
def catchKE {α β : Type} (x : Py α) (f : α → β) (dflt : β) : Py β :=
  match x with
  | .ok v => .ok (f v)
  | .error e => if isKeyErr e then .ok dflt else .error e

theorem getitem_plain {ops : KOps K} (hp : Plain ops) (r : ReprK K) (w : World) (d : WVD K)
    (key : K) : d.getitem ops r w key =
      match dGet (strip d.data) key with
      | none => .error (.keyError (r key))
      | some wr =>
        match deref w wr.ob with
        | none => .error (.keyError (r key))
        | some o => .ok o := by
  have hl := pLookup_plain hp d.data key
  have hg := idFind_dGet key d.data
  simp only [getitem, hl]
  rw [← hg]
  cases idFind key d.data with
  | none => rfl
  | some p => rfl

/-- `__getitem__`, `in` and `get` read one lookup. `in` and `get` are `d[key]` with a `KeyError`
caught, whatever raised it: a missing key, a dead value, or a key's own `__hash__` or `__eq__`;
any other exception passes through. An exception from the key's `__hash__` ends the read, an exact
`TypeError` renamed by the dict. A stored key of the same hash is compared first, and an exception
from its `__eq__` ends the read. With identity keys (`Plain`) and distinct stored keys, `d[key]` is
the live value of `key` in `items()`. -/
def WvdLookup : Prop :=
  ∀ (K : Type) [DecidableEq K] (ops : KOps K) (r : ReprK K) (w : World) (d : WVD K) (key : K)
    (dflt : PV),
    d.contains ops w key = catchKE (d.getitem ops r w key) (fun _ => true) false ∧
    d.get ops w key dflt = catchKE (d.getitem ops r w key) id dflt ∧
    (∀ e, ops.hash key = .error e → d.getitem ops r w key = .error (renameTE (ops.tn key) e)) ∧
    (∀ k0 h0 wr rest h e, d.data = (k0, h0, wr) :: rest → k0 ≠ key → ops.hash key = .ok h →
      h0 = h → ops.eq k0 key = .error e → d.getitem ops r w key = .error e) ∧
    (Plain ops → Keys (strip d.data) →
      d.getitem ops r w key =
        match (liveItems w d).lookup key with
        | none => .error (.keyError (r key))
        | some v => .ok v)

theorem wvdLookup_proven : WvdLookup := by
  intro K _ ops r w d key dflt
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [contains, getitem, catchKE]
    cases pLookup ops d.data key with
    | error e => rfl
    | ok x =>
      cases x with
      | none => rfl
      | some p =>
        obtain ⟨_, wr⟩ := p
        cases hdr : deref w wr.ob <;> simp [hdr, isKeyErr]
  · simp only [get, getitem, catchKE]
    cases pLookup ops d.data key with
    | error e => rfl
    | ok x =>
      cases x with
      | none => rfl
      | some p =>
        obtain ⟨_, wr⟩ := p
        cases hdr : deref w wr.ob <;> simp [hdr, isKeyErr]
  · intro e he
    simp [getitem, pLookup, KOps.dhash, he, unhashable_error]
  · intro k0 h0 wr rest h e hd hk hh hh0 he
    simp [getitem, pLookup, KOps.dhash, hh, unhashable, hd, pFind_cons, hk, hh0, he]
  · intro hp hk
    rw [getitem_plain hp, liveItems_strip, lookup_liveL w key _ hk]
    cases dGet (strip d.data) key with
    | none => rfl
    | some wr => cases hdr : deref w wr.ob <;> simp [hdr, isKeyErr]

/-! ### Stores -/

theorem setitem_plain {ops : KOps K} (hp : Plain ops) (d : WVD K) (k : K) (o : Nat) :
    ∃ d', d.setitem ops k (.obj o) = .ok d' ∧
      strip d'.data = dSet (strip d.data) k ⟨o, d.eager, k⟩ ∧ d'.eager = d.eager := by
  obtain ⟨data', h1, h2⟩ := pSet_plain hp d.data k (⟨o, d.eager, k⟩ : KRef K)
  exact ⟨{ d with data := data' }, by simp [setitem, KRef.new, refOf, h1], h2, rfl⟩

/-- Stores. `KeyedRef(value, ...)` comes first, so an int value raises its `TypeError` before the
key is hashed. A key whose `__hash__` raises ends the store or the deletion. Whatever the keys'
`__eq__` does, a store that succeeds is read back by the same key, and a deletion that succeeds
removes the one entry the lookup found, or raises `KeyError` for a missing key. With identity keys
the other keys are left as they were. -/
def WvdWrites : Prop :=
  ∀ (K : Type) [DecidableEq K] (ops : KOps K) (r : ReprK K) (w : World) (d : WVD K) (k a : K)
    (o : Nat) (n : Int),
    d.setitem ops k (.int n) = .error (.typeError "cannot create weak reference to 'int' object") ∧
    (∀ e, ops.hash k = .error e →
      d.setitem ops k (.obj o) = .error (renameTE (ops.tn k) e) ∧
      d.delitem ops r k = .error (renameTE (ops.tn k) e)) ∧
    (∀ d', d.setitem ops k (.obj o) = .ok d' → alive w o = true →
      d'.getitem ops r w k = .ok (.obj o)) ∧
    (∀ d', d.delitem ops r k = .ok d' →
      ∃ i x, pLookup ops d.data k = .ok (some (i, x)) ∧ d'.data = delAt d.data i) ∧
    (pLookup ops d.data k = .ok none → d.delitem ops r k = .error (.keyError (r k))) ∧
    (Plain ops → Keys (strip d.data) →
      (∃ d', d.setitem ops k (.obj o) = .ok d' ∧ Keys (strip d'.data) ∧
        (a ≠ k → d'.getitem ops r w a = d.getitem ops r w a)) ∧
      (∀ d', d.delitem ops r k = .ok d' →
        strip d'.data = dDel (strip d.data) k ∧ d'.contains ops w k = .ok false ∧
        (a ≠ k → d'.getitem ops r w a = d.getitem ops r w a)))

theorem wvdWrites_proven : WvdWrites := by
  intro K _ ops r w d k a o n
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    have hh : ops.dhash k = .error (renameTE (ops.tn k) e) := by
      simp [KOps.dhash, he, unhashable_error]
    refine ⟨?_, ?_⟩
    · simp [setitem, KRef.new, refOf, pSet, hh]
    · simp [delitem, pDel, pLookup, hh]
  · intro d' hs ho
    simp only [setitem, KRef.new, refOf] at hs
    cases hps : pSet ops d.data k (⟨o, d.eager, k⟩ : KRef K) with
    | error e => simp [hps] at hs
    | ok data =>
      simp only [hps, Except.ok.injEq] at hs
      subst hs
      obtain ⟨i, hi⟩ := pSet_lookup ops d.data data k _ hps
      simp [getitem, hi, deref, ho]
  · intro d' hd
    simp only [delitem, pDel] at hd
    cases hl : pLookup ops d.data k with
    | error e => simp [hl] at hd
    | ok x =>
      cases x with
      | none => simp [hl] at hd
      | some p =>
        obtain ⟨i, y⟩ := p
        simp only [hl, Except.ok.injEq] at hd
        exact ⟨i, y, rfl, by rw [← hd]⟩
  · intro hl
    simp [delitem, pDel, hl]
  · intro hp hk
    constructor
    · obtain ⟨d', h1, h2, _⟩ := setitem_plain hp d k o
      refine ⟨d', h1, by rw [h2]; exact Keys_dSet hk _ _, ?_⟩
      intro hak
      rw [getitem_plain hp, getitem_plain hp, h2, dGet_dSet]
      simp [Ne.symm hak]
    · intro d' hd
      have hpd := pDel_plain hp (.keyError (r k)) d.data k
      cases hg : dGet (strip d.data) k with
      | none =>
        have := hpd.1 hg
        simp [delitem, this] at hd
      | some x =>
        obtain ⟨data', h1, h2⟩ := hpd.2 x hg
        simp only [delitem, h1, Except.ok.injEq] at hd
        subst hd
        refine ⟨h2, ?_, ?_⟩
        · have hl := pLookup_plain hp data' k
          have hg' := idFind_dGet k data'
          rw [h2, dGet_dDel hk] at hg'
          simp only [if_true] at hg'
          have : idFind k data' = none := by simpa using hg'
          simp [contains, hl, this]
        · intro hak
          rw [getitem_plain hp, getitem_plain hp]
          show (match dGet (strip data') a with
            | none => _ | some wr => _) = _
          rw [h2, dGet_dDel hk]
          simp [Ne.symm hak]

/-! ### `pop` -/

/-- The result of `pop` for a missing key: `args[0]`, or `KeyError(key)`. -/
def missOf (r : ReprK K) (key : K) : List PV → Py PV
  | a :: _ => .ok a
  | [] => .error (.keyError (r key))

/-- `pop`. On an empty dict it answers before the key is hashed (an unhashable key gets the
default). A `KeyError` from the lookup is caught like a missing key, any other exception passes
through and changes nothing. A found entry leaves `data` whether its value lives or not; a live
value is the result, a dead one is treated as missing. With identity keys, the key is gone
afterwards and the other entries stay. -/
def WvdPop : Prop :=
  ∀ (K : Type) [DecidableEq K] (ops : KOps K) (r : ReprK K) (w : World) (d : WVD K) (key : K)
    (args : List PV),
    (d.data = [] → d.pop ops r w key args = (d, missOf r key args)) ∧
    (d.data ≠ [] → ∀ e, pLookup ops d.data key = .error e →
      d.pop ops r w key args = (d, if isKeyErr e then missOf r key args else .error e)) ∧
    (pLookup ops d.data key = .ok none → d.pop ops r w key args = (d, missOf r key args)) ∧
    (d.data ≠ [] → ∀ i wr, pLookup ops d.data key = .ok (some (i, wr)) →
      (d.pop ops r w key args).1.data = delAt d.data i ∧
      (d.pop ops r w key args).2 = (match deref w wr.ob with
        | some o => .ok o
        | none => missOf r key args)) ∧
    (Plain ops → Keys (strip d.data) → ∀ wr, dGet (strip d.data) key = some wr →
      strip (d.pop ops r w key args).1.data = dDel (strip d.data) key ∧
      (d.pop ops r w key args).1.contains ops w key = .ok false)

theorem pop_empty (ops : KOps K) (r : ReprK K) (w : World) (d : WVD K) (key : K) (args : List PV)
    (h : d.data = []) : d.pop ops r w key args = (d, missOf r key args) := by
  cases args <;> simp [pop, pPop, h, missOf]

theorem pop_ne (ops : KOps K) (r : ReprK K) (w : World) (d : WVD K) (key : K) (args : List PV)
    (hne : d.data ≠ []) : d.pop ops r w key args =
      match pLookup ops d.data key with
      | .error e => if isKeyErr e then (d, missOf r key args) else (d, .error e)
      | .ok none => (d, missOf r key args)
      | .ok (some (i, wr)) =>
        match deref w wr.ob with
        | some o => ({ d with data := delAt d.data i }, .ok o)
        | none => ({ d with data := delAt d.data i }, missOf r key args) := by
  have he : d.data.isEmpty = false := by
    cases hd : d.data with
    | nil => exact absurd hd hne
    | cons _ _ => rfl
  cases hl : pLookup ops d.data key with
  | error e => cases args <;> simp [pop, pPop, he, hl, missOf]
  | ok x =>
    cases x with
    | none => cases args <;> simp [pop, pPop, he, hl, missOf]
    | some p =>
      obtain ⟨i, wr⟩ := p
      cases hd : deref w wr.ob <;> cases args <;> simp [pop, pPop, he, hl, hd, missOf]

theorem wvdPop_proven : WvdPop := by
  intro K _ ops r w d key args
  refine ⟨pop_empty ops r w d key args, ?_, ?_, ?_, ?_⟩
  · intro hne e he
    simp only [pop_ne ops r w d key args hne, he]
    cases isKeyErr e <;> rfl
  · intro hn
    by_cases hne : d.data = []
    · exact pop_empty ops r w d key args hne
    · simp only [pop_ne ops r w d key args hne, hn]
  · intro hne i wr hl
    simp only [pop_ne ops r w d key args hne, hl]
    cases hd : deref w wr.ob <;> simp
  · intro hp hk wr hg
    have hl := pLookup_plain hp d.data key
    have hgi := idFind_dGet key d.data
    rw [hg] at hgi
    cases hi : idFind key d.data with
    | none => rw [hi] at hgi; simp at hgi
    | some p =>
      obtain ⟨i, x⟩ := p
      have hne : d.data ≠ [] := by intro e; simp [e, idFind] at hi
      have hs := strip_delAt key d.data i x hi
      have hpop : (d.pop ops r w key args).1 = { d with data := delAt d.data i } := by
        simp only [pop_ne ops r w d key args hne, hl, hi]
        cases hd : deref w x.ob <;> simp
      rw [hpop]
      refine ⟨hs, ?_⟩
      have hl' := pLookup_plain hp (delAt d.data i) key
      have hg' := idFind_dGet key (delAt d.data i)
      rw [hs, dGet_dDel hk] at hg'
      simp only [if_true] at hg'
      have : idFind key (delAt d.data i) = none := by simpa using hg'
      simp [contains, hl', this]

/-- `WeakValueDictionary.pop` takes the `*args` of `dict.pop` (and of `WeakKeyDictionary.pop`,
which hands them to `dict.pop`): two or more defaults raise `TypeError`. -/
def WvdPopArity : Prop :=
  ∀ (K : Type) [DecidableEq K] (ops : KOps K) (r : ReprK K) (w : World) (d : WVD K) (key : K)
    (a b : PV) (rest : List PV),
    (d.pop ops r w key (a :: b :: rest)).2 = .error (WKD.popArity (rest.length + 2))

/-- Refuted: on an empty dictionary `pop('k', 1, 2)` returns `1`, as on a missing key of any
dictionary. -/
theorem wvdPopArity_refuted : ¬ WvdPopArity := by
  intro h
  have := h Nat ⟨fun _ => .ok 0, fun _ _ => .ok false, fun _ => "int"⟩ (fun _ => "") [] WVD.empty 0
    (.int 1) (.int 2) []
  simp [pop, pPop, WVD.empty] at this

/-! ### `setdefault` -/

/-- `setdefault`. The read catches `KeyError` and the store after it does not, so a key whose
`__hash__` raises `KeyError` gets it from the store, and any other exception from the read passes
through with nothing stored. With identity keys, a live value is returned and nothing changes; a
missing or dead one is replaced by the default, read back afterwards; an int default raises
`TypeError` and changes nothing. -/
def WvdSetdefault : Prop :=
  ∀ (K : Type) [DecidableEq K] (ops : KOps K) (r : ReprK K) (w : World) (d : WVD K) (key : K)
    (o : Nat) (n : Int),
    (∀ m, ops.hash key = .error (.keyError m) →
      d.setdefault ops w key (.obj o) = (d, .error (.keyError m))) ∧
    (∀ e, pLookup ops d.data key = .error e → isKeyErr e = false →
      ∀ v, d.setdefault ops w key v = (d, .error e)) ∧
    (Plain ops → Keys (strip d.data) →
      (∀ wr, dGet (strip d.data) key = some wr → alive w wr.ob = true →
        ∀ v, d.setdefault ops w key v = (d, .ok (.obj wr.ob))) ∧
      ((dGet (strip d.data) key).bind (fun x => deref w x.ob) = none →
        alive w o = true →
        (d.setdefault ops w key (.obj o)).2 = .ok (.obj o) ∧
        (d.setdefault ops w key (.obj o)).1.getitem ops r w key = .ok (.obj o) ∧
        d.setdefault ops w key (.int n) =
          (d, .error (.typeError "cannot create weak reference to 'int' object"))))

theorem wvdSetdefault_proven : WvdSetdefault := by
  intro K _ ops r w d key o n
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    have hh : ops.dhash key = .error (.keyError m) := by simp [KOps.dhash, hm, unhashable]
    simp [setdefault, pLookup, hh, isKeyErr, setitem, KRef.new, refOf, pSet]
  · intro e he hk v
    simp [setdefault, he, hk]
  · intro hp hk
    have hl := pLookup_plain hp d.data key
    have hg := idFind_dGet key d.data
    constructor
    · intro wr hw ha v
      rw [hw] at hg
      cases hi : idFind key d.data with
      | none => rw [hi] at hg; simp at hg
      | some p =>
        obtain ⟨i, x⟩ := p
        rw [hi] at hg
        simp only [Option.map_some, Option.some.injEq] at hg
        subst hg
        simp [setdefault, hl, hi, deref, ha]
    · intro hnone ho
      obtain ⟨d', h1, h2, _⟩ := setitem_plain hp d key o
      have hrd : ∀ v, d.setdefault ops w key v = match d.setitem ops key v with
          | .error e => (d, .error e)
          | .ok d => (d, .ok v) := by
        intro v
        cases hi : idFind key d.data with
        | none => (simp [setdefault, hl, hi]) <;> rfl
        | some p =>
          obtain ⟨i, x⟩ := p
          have hx : deref w x.ob = none := by
            rw [← hg, hi] at hnone
            simpa using hnone
          (simp [setdefault, hl, hi, hx]) <;> rfl
      have hsd : d.setdefault ops w key (.obj o) = (d', .ok (.obj o)) := by rw [hrd, h1]
      refine ⟨by rw [hsd], ?_, ?_⟩
      · rw [hsd, getitem_plain hp, h2, dGet_dSet]
        simp [deref, ho]
      · rw [hrd]
        simp [setitem, KRef.new, refOf]

/-! ### Death and `KeyedRef`'s callback -/

theorem keys_unique {β : Type} : ∀ {d : List (Ent K β)}, Keys (strip d) →
    ∀ {a b : Ent K β}, a ∈ d → b ∈ d → a.1 = b.1 → a = b := by
  intro d
  induction d with
  | nil => intro _ a b ha; simp at ha
  | cons p rest ih =>
    intro hk a b ha hb e
    have hn : p.1 ∉ (strip rest).map (·.1) ∧ Keys (strip rest) := by
      unfold Keys strip at hk ⊢
      simpa using hk
    have hmem : ∀ x ∈ rest, x.1 ≠ p.1 := by
      intro x hx hxp
      apply hn.1
      simp only [strip, List.map_map, List.mem_map]
      exact ⟨x, hx, hxp⟩
    rcases List.mem_cons.1 ha with ha' | ha'
    · rcases List.mem_cons.1 hb with hb' | hb'
      · rw [ha', hb']
      · rw [ha'] at e; exact absurd e.symm (hmem b hb')
    · rcases List.mem_cons.1 hb with hb' | hb'
      · rw [hb'] at e; exact absurd e (hmem a ha')
      · exact ih hn.2 ha' hb' e

theorem idFind_of_mem {β : Type} (e : Ent K β) : ∀ {d : List (Ent K β)}, Keys (strip d) → e ∈ d →
    ∃ i, idFind e.1 d = some (i, e.2.2) := by
  intro d
  induction d with
  | nil => intro _ h; simp at h
  | cons p rest ih =>
    intro hk he
    have hk' : Keys (strip rest) := by
      unfold Keys strip at hk ⊢
      simp only [List.map_map, List.map_cons, List.nodup_cons] at hk ⊢
      exact hk.2
    obtain ⟨k0, h0, v0⟩ := p
    by_cases h1 : k0 = e.1
    · have : (k0, h0, v0) = e := keys_unique hk (List.mem_cons_self) he h1
      subst this
      exact ⟨0, by simp [idFind]⟩
    · have he' : e ∈ rest := by
        rcases List.mem_cons.1 he with h | h
        · subst h; exact absurd rfl h1
        · exact h
      obtain ⟨i, hi⟩ := ih hk' he'
      exact ⟨i + 1, by simp [idFind, h1, hi]⟩

theorem delAt_idFind {β : Type} (k : K) : ∀ {d : List (Ent K β)} {i : Nat} {x : β}, Keys (strip d) →
    idFind k d = some (i, x) → delAt d i = d.filter (fun e => e.1 ≠ k) := by
  intro d
  induction d with
  | nil => intro i x _ h; simp [idFind] at h
  | cons p rest ih =>
    intro i x hk h
    obtain ⟨k0, h0, v0⟩ := p
    have hn : k0 ∉ (strip rest).map (·.1) ∧ Keys (strip rest) := by
      unfold Keys strip at hk ⊢
      simpa using hk
    simp only [idFind] at h
    by_cases h1 : k0 = k
    · simp only [h1, if_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst h1
      simp only [delAt, List.filter_cons, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, if_false]
      symm
      rw [List.filter_eq_self]
      intro a ha
      have : a.1 ≠ k0 := by
        intro e
        apply hn.1
        simp only [strip, List.map_map, List.mem_map]
        exact ⟨a, ha, e⟩
      simpa using this
    · simp only [h1, if_false] at h
      cases hr : idFind k rest with
      | none => rw [hr] at h; simp at h
      | some q =>
        rw [hr] at h
        obtain ⟨j, y⟩ := q
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [delAt, h1, ih hn.2 hr]

theorem Keys_filter {β : Type} (d : List (Ent K β)) (p : Ent K β → Bool) (h : Keys (strip d)) :
    Keys (strip (d.filter p)) := by
  unfold Keys strip at *
  simp only [List.map_map] at *
  exact (List.Sublist.map _ List.filter_sublist).nodup h

/-- Under identity keys, the callbacks of the references to a dead object remove exactly the entries
that hold them. -/
theorem fold_remove {ops : KOps K} (hp : Plain ops) (w' : World) (data0 : List (Ent K (KRef K)))
    (hk : Keys (strip data0)) :
    ∀ (L R : List (Ent K (KRef K))), (∀ e ∈ L, e ∈ data0 ∧ e ∉ R ∧ alive w' e.2.2.ob = false) →
      L.Nodup →
      L.foldl (fun data e => removeDead ops w' data e.1) (data0.filter (fun x => x ∉ R)) =
        data0.filter (fun x => x ∉ L ∧ x ∉ R) := by
  intro L
  induction L with
  | nil => intro R _ _; simp
  | cons e L ih =>
    intro R hL hn
    obtain ⟨he0, heR, hdead⟩ := hL e (by simp)
    have hcur : Keys (strip (data0.filter (fun x => x ∉ R))) := Keys_filter _ _ hk
    have hmem : e ∈ data0.filter (fun x => x ∉ R) := List.mem_filter.2 ⟨he0, by simpa using heR⟩
    obtain ⟨i, hi⟩ := idFind_of_mem e hcur hmem
    have hstep : removeDead ops w' (data0.filter (fun x => x ∉ R)) e.1 =
        data0.filter (fun x => x ∉ e :: R) := by
      simp only [removeDead, pLookup_plain hp, hi, hdead, Bool.false_eq_true, if_false]
      rw [delAt_idFind e.1 hcur hi, List.filter_filter]
      apply List.filter_congr
      intro x hx
      by_cases hxe : x = e
      · subst hxe; simp
      · have : x.1 ≠ e.1 := fun h => hxe (keys_unique hk hx he0 h)
        simp [hxe, this]
    simp only [List.foldl_cons]
    rw [hstep]
    have hn' : L.Nodup := (List.nodup_cons.1 hn).2
    have := ih (e :: R) (fun x hx => ?_) hn'
    · rw [this]
      apply List.filter_congr
      intro x _
      simp only [List.mem_cons]
      by_cases a : x = e <;> simp [a]
    · obtain ⟨h1, h2, h3⟩ := hL x (by simp [hx])
      refine ⟨h1, ?_, h3⟩
      simp only [List.mem_cons, not_or]
      refine ⟨?_, h2⟩
      intro hxe
      subst hxe
      exact (List.nodup_cons.1 hn).1 hx

theorem nodup_of_map {α γ : Type} (f : α → γ) : ∀ {l : List α}, (l.map f).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    rw [List.map_cons, List.nodup_cons] at h
    exact List.nodup_cons.2 ⟨fun hm => h.1 (List.mem_map.2 ⟨_, hm, rfl⟩), nodup_of_map f h.2⟩

theorem nodup_of_keys {β : Type} {d : List (Ent K β)} (h : Keys (strip d)) : d.Nodup := by
  unfold Keys strip at h
  simp only [List.map_map] at h
  exact nodup_of_map _ h

/-- Under identity keys, a death removes exactly the entries whose reference to `o` carries the
removing callback. -/
theorem onDeath_plain {ops : KOps K} (hp : Plain ops) (w : World) (d : WVD K) (o : Nat)
    (hk : Keys (strip d.data)) :
    (d.onDeath ops w o).data = d.data.filter (fun e => !(e.2.2.ob == o && e.2.2.cb)) := by
  simp only [onDeath]
  have hfold := fold_remove hp (o :: w) d.data hk
    (d.data.filter (fun e => e.2.2.ob == o && e.2.2.cb)).reverse [] (by
      intro e he
      rw [List.mem_reverse, List.mem_filter] at he
      refine ⟨he.1, by simp, ?_⟩
      have : e.2.2.ob = o := by
        have h2 := he.2
        simp at h2
        exact h2.1
      simp [alive, this]) (by
      exact (List.reverse_perm _).nodup_iff.2 ((nodup_of_keys hk).filter _))
  have h0 : d.data.filter (fun x => decide (x ∉ ([] : List (Ent K (KRef K))))) = d.data :=
    List.filter_eq_self.2 (by simp)
  rw [h0] at hfold
  simp only [List.not_mem_nil, not_false_eq_true, and_true] at hfold
  rw [hfold]
  apply List.filter_congr
  intro x hx
  simp only [List.mem_reverse, List.mem_filter]
  cases hc : (x.2.2.ob == o && x.2.2.cb) <;> simp [hx, hc]

theorem liveL_removeDead (ops : KOps K) (w' : World) (data : List (Ent K (KRef K))) (k : K) :
    (removeDead ops w' data k).filterMap (itemF w') = data.filterMap (itemF w') := by
  unfold removeDead
  cases hl : pLookup ops data k with
  | error e => rfl
  | ok x =>
    cases x with
    | none => rfl
    | some p =>
      obtain ⟨i, wr⟩ := p
      simp only
      split
      · rfl
      · rename_i hdead
        apply filterMap_delAt
        intro a ha
        simp only [pLookup] at hl
        cases hh : ops.dhash k with
        | error e => simp [hh] at hl
        | ok h =>
          simp only [hh] at hl
          obtain ⟨k0, h0, hab⟩ := pFind_index ops.eq k h data i wr hl
          rw [hab] at ha
          simp only [Option.some.injEq] at ha
          subst ha
          simp [itemF, deref, hdead]

/-- A death. Whatever the keys do, the live items lose exactly that object. With identity keys, every
entry whose reference to it carries the removing callback leaves `data`, and the other entries stay.
A key whose `__eq__` raises in the callback's lookup leaves its dead entry, which only `len` sees. -/
def WvdDeath : Prop :=
  ∀ (K : Type) [DecidableEq K] (ops : KOps K) (w : World) (d : WVD K) (o : Nat),
    liveItems (o :: w) (d.onDeath ops w o) = (liveItems w d).filter (fun kv => kv.2 ≠ .obj o) ∧
    (Plain ops → Keys (strip d.data) →
      (∀ e ∈ (d.onDeath ops w o).data, e.2.2.ob = o → e.2.2.cb = false) ∧
      (∀ e ∈ d.data, e.2.2.ob ≠ o → e ∈ (d.onDeath ops w o).data))

theorem wvdDeath_proven : WvdDeath := by
  intro K _ ops w d o
  refine ⟨?_, ?_⟩
  · have key : ∀ l : List (Ent K (KRef K)),
        l.filterMap (itemF (o :: w)) = (l.filterMap (itemF w)).filter (fun kv => kv.2 ≠ .obj o) := by
      intro l
      induction l with
      | nil => rfl
      | cons p rest ih =>
        obtain ⟨x0, h0, r⟩ := p
        by_cases h1 : r.ob = o
        · have e1 : itemF (o :: w) (x0, h0, r) = none := by
            simp only [itemF]
            rw [deref_cons, if_pos h1]
            rfl
          rw [List.filterMap_cons_none e1]
          cases hd : deref w r.ob with
          | none =>
            have e2 : itemF w (x0, h0, r) = none := by simp only [itemF]; rw [hd]; rfl
            rw [List.filterMap_cons_none e2]
            exact ih
          | some v =>
            have hv := deref_some hd
            have e2 : itemF w (x0, h0, r) = some (x0, v) := by simp only [itemF]; rw [hd]; rfl
            rw [List.filterMap_cons_some e2, List.filter_cons_of_neg (by simp [hv, h1])]
            exact ih
        · cases hd : deref w r.ob with
          | none =>
            have e1 : itemF (o :: w) (x0, h0, r) = none := by
              simp only [itemF]
              rw [deref_cons, if_neg h1, hd]
              rfl
            have e2 : itemF w (x0, h0, r) = none := by simp only [itemF]; rw [hd]; rfl
            rw [List.filterMap_cons_none e1, List.filterMap_cons_none e2]
            exact ih
          | some v =>
            have hv := deref_some hd
            have e1 : itemF (o :: w) (x0, h0, r) = some (x0, v) := by
              simp only [itemF]
              rw [deref_cons, if_neg h1, hd]
              rfl
            have e2 : itemF w (x0, h0, r) = some (x0, v) := by simp only [itemF]; rw [hd]; rfl
            rw [List.filterMap_cons_some e1, List.filterMap_cons_some e2,
              List.filter_cons_of_pos (by simp [hv, h1]), ih]
    have hfold : ∀ (L : List (Ent K (KRef K))) (data : List (Ent K (KRef K))),
        (L.foldl (fun data e => removeDead ops (o :: w) data e.1) data).filterMap (itemF (o :: w)) =
          data.filterMap (itemF (o :: w)) := by
      intro L
      induction L with
      | nil => intro _; rfl
      | cons e L ih =>
        intro data
        simp only [List.foldl_cons]
        rw [ih, liveL_removeDead]
    have hli : ∀ (w' : World) (d' : WVD K), liveItems w' d' = d'.data.filterMap (itemF w') := by
      intro w' d'
      rfl
    rw [hli, hli]
    simp only [onDeath]
    rw [hfold, key]
  · intro hp hk
    rw [onDeath_plain hp w d o hk]
    refine ⟨?_, ?_⟩
    · intro e he hob
      have := (List.mem_filter.1 he).2
      simpa [hob] using this
    · intro e he hne
      exact List.mem_filter.2 ⟨he, by simp [hne]⟩

/-- `KeyedRef(value, self._remove, key)` keeps the callback it was made with: the stored reference
holds the value, the key, and the callback of the dictionary at that moment. A value stored while
the callback is the removing one leaves the dictionary when it dies, even if `_remove` has been
replaced since; one stored while it was a no-op stays, a dead entry that `len` counts.
`KeyedRef(int, ...)` raises `TypeError`. -/
def KeyedRefCallback : Prop :=
  ∀ (K : Type) [DecidableEq K] (ops : KOps K) (w : World) (d : WVD K) (k : K) (o : Nat) (n : Int)
    (b : Bool),
    KRef.new (.int n) b k = .error (.typeError "cannot create weak reference to 'int' object") ∧
    (Plain ops → Keys (strip d.data) → ∀ d', d.setitem ops k (.obj o) = .ok d' →
      (∃ wr, dGet (strip d'.data) k = some wr ∧ wr.ob = o ∧ wr.cb = d.eager ∧ wr.key = k) ∧
      (d.eager = true → dGet (strip (({ d' with eager := b } : WVD K).onDeath ops w o).data) k = none) ∧
      (d.eager = false → ∃ wr, dGet (strip (d'.onDeath ops w o).data) k = some wr ∧ wr.ob = o))

theorem dGet_strip_filter (k : K) (p : Ent K (KRef K) → Bool) (c : Bool) :
    ∀ (l : List (Ent K (KRef K))), Keys (strip l) → (∀ e ∈ l, e.1 = k → p e = c) →
      dGet (strip (l.filter p)) k = if c then dGet (strip l) k else none := by
  intro l hk hc
  induction l with
  | nil => cases c <;> rfl
  | cons e rest ih =>
    obtain ⟨k0, h0, v0⟩ := e
    have hn : k0 ∉ (strip rest).map (·.1) ∧ Keys (strip rest) := by
      unfold Keys strip at hk ⊢
      simpa using hk
    have ih' := ih hn.2 (fun e he hek => hc e (by simp [he]) hek)
    by_cases h1 : k0 = k
    · subst h1
      have hpe := hc (k0, h0, v0) (by simp) rfl
      have habs : dGet (strip rest) k0 = none := dGet_absent _ _ hn.1
      rw [habs] at ih'
      rw [List.filter_cons, hpe]
      cases c with
      | true => simp [strip, dGet_cons]
      | false => simpa using ih'
    · rw [List.filter_cons]
      split
      · simp only [strip, List.map_cons] at ih' ⊢
        rw [dGet_cons, dGet_cons]
        simp [h1, ih']
      · simp only [strip, List.map_cons] at ih' ⊢
        rw [dGet_cons]
        simp [h1, ih']

theorem keyedRefCallback_proven : KeyedRefCallback := by
  intro K _ ops w d k o n b
  refine ⟨rfl, ?_⟩
  intro hp hk d' hs
  obtain ⟨d2, h1, h2, h3⟩ := setitem_plain hp d k o
  rw [h1] at hs
  simp only [Except.ok.injEq] at hs
  subst hs
  have hk' : Keys (strip d2.data) := by rw [h2]; exact Keys_dSet hk _ _
  have hget : dGet (strip d2.data) k = some ⟨o, d.eager, k⟩ := by rw [h2, dGet_dSet]; simp
  have hfind : ∀ e ∈ d2.data, e.1 = k → e.2.2 = ⟨o, d.eager, k⟩ := by
    intro e he hek
    obtain ⟨i, hi⟩ := idFind_of_mem e hk' he
    have := idFind_dGet e.1 d2.data
    rw [hi, hek, hget] at this
    simpa using this
  have hp' : ∀ e ∈ d2.data, e.1 = k → (!(e.2.2.ob == o && e.2.2.cb)) = !d.eager := by
    intro e he hek
    rw [hfind e he hek]
    simp
  refine ⟨⟨_, hget, rfl, rfl, rfl⟩, ?_, ?_⟩
  · intro he
    have := dGet_strip_filter k _ (!d.eager) d2.data hk' hp'
    rw [onDeath_plain hp w ({ d2 with eager := b } : WVD K) o hk']
    simp only [he, Bool.not_true] at this
    simpa using this
  · intro he
    have := dGet_strip_filter k _ (!d.eager) d2.data hk' hp'
    rw [onDeath_plain hp w _ o hk']
    simp only [he, Bool.not_false, if_true] at this
    rw [this, hget]
    exact ⟨_, rfl, rfl⟩

end WVD

end PyLean.CoreLibs.Misc.Weakref
