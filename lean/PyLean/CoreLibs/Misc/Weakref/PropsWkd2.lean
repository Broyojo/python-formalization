import PyLean.CoreLibs.Misc.Weakref.PropsWvd2

/-! `WeakKeyDictionary`: the generators, `keyrefs`, `copy`, `|`, `update`, `__init__`. -/

namespace PyLean.CoreLibs.Misc.Weakref

open PyLean

namespace WKD

variable {V : Type}

/-- The generators of `WeakKeyDictionary` (`items`, `keys`/`__iter__`, `values`) are lazy in the same
way as those of `WeakValueDictionary`: the snapshot is taken at the first `next()`, later changes to
the dictionary are not seen, and each `next()` reads the keys in the world of that call. Run to the
end in one world they give the live items, their keys and their values. `keyrefs()` is the list of
the stored `ref`s: as many as `len()`, and the live ones read the keys of `items()`. -/
def WkdIters : Prop :=
  ∀ (V : Type) (w : World) (d d' : WKD V) (s : List (WRef × V)),
    d.itemsNext w none = d.itemsNext w (some d.data) ∧
    d.itemsNext w (some s) = d'.itemsNext w (some s) ∧
    d.keysNext w (some s) = d'.keysNext w (some s) ∧
    d.valuesNext w (some s) = d'.valuesNext w (some s) ∧
    (d.itemsNext w (some s)).2 = (s.filterMap (itemF w)).head? ∧
    (d.keysNext w (some s)).2 = (s.filterMap (keyF w)).head? ∧
    (d.valuesNext w (some s)).2 = (s.filterMap (valueF w)).head? ∧
    WVD.drain (d.itemsNext w) (d.data.length + 1) none = liveItems w d ∧
    WVD.drain (d.keysNext w) (d.data.length + 1) none = (liveItems w d).map (·.1) ∧
    WVD.drain (d.valuesNext w) (d.data.length + 1) none = (liveItems w d).map (·.2) ∧
    d.keyrefs.length = d.data.length ∧
    d.keyrefs.filterMap (fun r => deref w r.ob) = (liveItems w d).map (·.1)

theorem wkdIters_proven : WkdIters := by
  intro V w d d' s
  have fm1 : ∀ l : List (WRef × V), l.filterMap (keyF w) = (l.filterMap (itemF w)).map (·.1) := by
    intro l
    induction l with
    | nil => rfl
    | cons e rest ih =>
      simp only [List.filterMap_cons, keyF, itemF]
      cases deref w e.1.ob <;> simp [ih]
  have fm2 : ∀ l : List (WRef × V), l.filterMap (valueF w) = (l.filterMap (itemF w)).map (·.2) := by
    intro l
    induction l with
    | nil => rfl
    | cons e rest ih =>
      simp only [List.filterMap_cons, valueF, itemF]
      cases deref w e.1.ob <;> simp [ih]
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (WVD.genNext_spec itemF d.data w (some s)).1
  · exact (WVD.genNext_spec keyF d.data w (some s)).1
  · exact (WVD.genNext_spec valueF d.data w (some s)).1
  · exact WVD.drain_fresh itemF d.data w
  · rw [show d.keysNext w = WVD.genNext keyF d.data w from rfl, WVD.drain_fresh, fm1]; rfl
  · rw [show d.valuesNext w = WVD.genNext valueF d.data w from rfl, WVD.drain_fresh, fm2]; rfl
  · simp [keyrefs]
  · simp only [keyrefs, liveItems]
    induction d.data with
    | nil => rfl
    | cons e rest ih =>
      simp only [List.map_cons, List.filterMap_cons]
      cases deref w e.1.ob <;> simp [ih]

/-! ### Stores in turn, for hashable keys -/

/-- `d[k] = v` for a hashable key. -/
def putH (q : ROps) (w : World) (d : WKD V) (k : Nat) (v : V) : WKD V :=
  match q.hash k with
  | .ok h => storeAt d k h (d.data.find? (pr q w k)) v
  | .error _ => d

theorem setitem_putH (q : ROps) (hq : Hashable q) (w : World) (d : WKD V) (k : Nat) (v : V)
    (hd : HashOk q d) : d.setitem q w (.obj k) v = .ok (putH q w d k v) ∧ HashOk q (putH q w d k v) := by
  obtain ⟨h, hh, hs⟩ := setitem_hashable q hq w d k v hd
  have hp : putH q w d k v = storeAt d k h (d.data.find? (pr q w k)) v := by simp [putH, hh]
  rw [hp]
  exact ⟨hs, storeAt_hashOk q d k h hh v hd _ (fun r x e => List.mem_of_find?_eq_some e)⟩

theorem valOf_putH (q : ROps) (hq : Hashable q) (w : World) (d : WKD V) (k a : Nat) (v : V)
    (hk : alive w k = true) (ha : alive w a = true) :
    valOf q w (putH q w d k v) a = if qb q k a then some v else valOf q w d a := by
  obtain ⟨h, hh⟩ := hq.hash k
  have hp : putH q w d k v = storeAt d k h (d.data.find? (pr q w k)) v := by simp [putH, hh]
  rw [hp]
  obtain ⟨t, ht⟩ := hq.eq k a
  rw [qb_of ht]
  cases t with
  | false => simp [valOf_storeAt_other q hq w d k a h v ht]
  | true =>
    simp only [if_true]
    have heq : ∀ kv : WRef × V, pr q w a kv = pr q w k kv := by
      intro kv
      simp only [pr]
      obtain ⟨t1, h1⟩ := hq.eq kv.1.ob a
      obtain ⟨t2, h2⟩ := hq.eq kv.1.ob k
      rw [qb_of h1, qb_of h2]
      cases t1 <;> cases t2 <;> simp
      · have := hq.trans _ _ _ h2 ht
        rw [h1] at this; simp at this
      · have h3 : q.eq a k = .ok true := by rw [hq.symm]; exact ht
        have := hq.trans _ _ _ h1 h3
        rw [h2] at this; simp at this
    have := valOf_storeAt_same q hq w d k h v hk
    unfold valOf at this ⊢
    have hf : pr q w a = pr q w k := funext heq
    rw [hf]
    exact this

theorem hashOk_fold (q : ROps) (hq : Hashable q) (w : World) : ∀ (items : List (Nat × V)) (d : WKD V),
    HashOk q d → HashOk q (items.foldl (fun d kv => putH q w d kv.1 kv.2) d) := by
  intro items
  induction items with
  | nil => intro d h; exact h
  | cons p t ih => intro d h; exact ih _ (setitem_putH q hq w d p.1 p.2 h).2

/-- The value after writing `items` in order. -/
def ovrQ (q : ROps) (items : List (Nat × V)) (dflt : Option V) (a : Nat) : Option V :=
  items.foldl (fun acc kv => if qb q kv.1 a then some kv.2 else acc) dflt

theorem valOf_fold (q : ROps) (hq : Hashable q) (w : World) (a : Nat) (ha : alive w a = true) :
    ∀ (items : List (Nat × V)) (d : WKD V), (∀ kv ∈ items, alive w kv.1 = true) →
      valOf q w (items.foldl (fun d kv => putH q w d kv.1 kv.2) d) a = ovrQ q items (valOf q w d a) a := by
  intro items
  induction items with
  | nil => intro d _; rfl
  | cons p rest ih =>
    intro d hal
    simp only [List.foldl_cons, ovrQ]
    rw [ih _ (fun kv h => hal kv (by simp [h])), valOf_putH q hq w d p.1 a p.2 (hal p (by simp)) ha]
    rfl

def objsK (l : List (Nat × V)) : List (PV × V) := l.map (fun kv => (PV.obj kv.1, kv.2))

theorem setAll_objsK (q : ROps) (hq : Hashable q) (w : World) : ∀ (items : List (Nat × V)) (n : WKD V),
    HashOk q n → setAll q w (objsK items) n = .ok (items.foldl (fun d kv => putH q w d kv.1 kv.2) n) := by
  intro items
  induction items with
  | nil => intro n _; rfl
  | cons p rest ih =>
    intro n hn
    have h := setitem_putH q hq w n p.1 p.2 hn
    simp only [objsK, List.map_cons, setAll, h.1]
    exact ih _ h.2

theorem storeAll_objsK (q : ROps) (hq : Hashable q) (w : World) (rest : List (Py (PV × V)))
    (stop : Option PyExc) : ∀ (items : List (Nat × V)) (n : WKD V), HashOk q n →
    storeAll q w ((objsK items).map Except.ok ++ rest) stop n =
      storeAll q w rest stop (items.foldl (fun d kv => putH q w d kv.1 kv.2) n) := by
  intro items
  induction items with
  | nil => intro n _; rfl
  | cons p t ih =>
    intro n hn
    have h := setitem_putH q hq w n p.1 p.2 hn
    simp only [objsK, List.map_cons, List.cons_append, storeAll, h.1]
    exact ih _ h.2

/-- The live entries of `d`. -/
def livePairs (w : World) (d : WKD V) : List (Nat × V) :=
  d.data.filterMap (fun kv => if alive w kv.1.ob then some (kv.1.ob, kv.2) else none)

theorem liveItems_eq (w : World) (d : WKD V) : liveItems w d = objsK (livePairs w d) := by
  simp only [liveItems, livePairs, objsK]
  induction d.data with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.filterMap_cons]
    by_cases h : alive w e.1.ob = true
    · have : deref w e.1.ob = some (.obj e.1.ob) := by simp [deref, h]
      simp only [this, h, if_true, Option.map_some, List.map_cons, ih]
    · have : deref w e.1.ob = none := by simp [deref, h]
      simp only [this, h, Bool.false_eq_true, if_false, Option.map_none, ih]

theorem livePairs_alive (w : World) (d : WKD V) : ∀ kv ∈ livePairs w d, alive w kv.1 = true := by
  intro kv h
  simp only [livePairs, List.mem_filterMap] at h
  obtain ⟨a, _, h2⟩ := h
  split at h2
  · rename_i h3
    simp only [Option.some.injEq] at h2
    subst h2
    exact h3
  · cases h2

/-- The first live entry equal to `a`. -/
def valList (q : ROps) : List (Nat × V) → Nat → Option V
  | [], _ => none
  | (k, v) :: r, a => if qb q k a then some v else valList q r a

theorem valOf_live (q : ROps) (w : World) (d : WKD V) (a : Nat) :
    valOf q w d a = valList q (livePairs w d) a := by
  simp only [valOf, livePairs]
  induction d.data with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨r, x⟩ := p
    simp only [List.find?_cons, List.filterMap_cons]
    cases hal : alive w r.ob with
    | false =>
      have : pr q w a (r, x) = false := by simp [pr, hal]
      simp only [this, Bool.false_eq_true, if_false]
      exact ih
    | true =>
      simp only [if_true, valList]
      cases hq : qb q r.ob a with
      | false =>
        have : pr q w a (r, x) = false := by simp [pr, hal, hq]
        simp only [this]
        exact ih
      | true =>
        have : pr q w a (r, x) = true := by simp [pr, hal, hq]
        simp [this]

theorem ovr_nomatch (q : ROps) (a : Nat) (d : Option V) :
    ∀ l : List (Nat × V), (∀ kv ∈ l, qb q kv.1 a = false) → ovrQ q l d a = d := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons p rest ih =>
    intro h
    simp only [ovrQ, List.foldl_cons, h p (by simp)]
    simpa [ovrQ] using ih (fun kv hk => h kv (by simp [hk]))

theorem ovr_val (q : ROps) (hq : Hashable q) (a : Nat) :
    ∀ l : List (Nat × V), l.Pairwise (fun x y => qb q x.1 y.1 = false) →
      ovrQ q l none a = valList q l a := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons p rest ih =>
    intro h
    obtain ⟨k, v⟩ := p
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 h
    simp only [ovrQ, List.foldl_cons, valList]
    cases hka : qb q k a with
    | false =>
      simpa [ovrQ] using ih h2
    | true =>
      simp only [if_true]
      apply ovr_nomatch q a
      intro kv hkv
      cases hv : qb q kv.1 a with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨t1, e1⟩ := hq.eq k a
        obtain ⟨t2, e2⟩ := hq.eq kv.1 a
        rw [qb_of e1] at hka
        rw [qb_of e2] at hv
        subst hka hv
        have e3 : q.eq a kv.1 = .ok true := by rw [hq.symm]; exact e2
        have := hq.trans _ _ _ e1 e3
        have h4 := h1 kv hkv
        rw [qb_of this] at h4
        simp at h4

theorem valOf_empty (q : ROps) (w : World) (a : Nat) : valOf q w (empty : WKD V) a = none := rfl

theorem hashOk_empty (q : ROps) : HashOk q (empty : WKD V) := by intro kv h; simp [empty] at h

/-- `copy` and `|`: while the live keys are pairwise unequal (a dict's invariant for hashable keys),
a copy maps every live key to the same value; in `d | other` a key in `other` takes its last value
there and otherwise its value in `d`; in `other | d` a live key of `d` keeps its value. Anything but
a `Mapping` gives `NotImplemented`. The keys are the same objects, weakly held. -/
def WkdCopyOr : Prop :=
  ∀ (V : Type) (q : ROps) (w : World) (d : WKD V) (items : List (Nat × V)) (a : Nat),
    Hashable q → alive w a = true → (∀ kv ∈ items, alive w kv.1 = true) →
    (livePairs w d).Pairwise (fun x y => qb q x.1 y.1 = false) →
    (∃ c, d.copy q w = .ok c ∧ valOf q w c a = valOf q w d a ∧ HashOk q c) ∧
    d.or_ q w none = none ∧ d.ror q w none = none ∧
    (∃ c, d.or_ q w (some (objsK items)) = some (.ok c) ∧ valOf q w c a = ovrQ q items (valOf q w d a) a) ∧
    (∃ c, d.ror q w (some (objsK items)) = some (.ok c) ∧
      valOf q w c a = ovrQ q (livePairs w d) (ovrQ q items none a) a)

theorem wkdCopyOr_proven : WkdCopyOr := by
  intro V q w d items a hq ha hit hu
  have hal := livePairs_alive w d
  have hc : d.copy q w = .ok ((livePairs w d).foldl (fun d kv => putH q w d kv.1 kv.2) empty) := by
    rw [copy, liveItems_eq]
    exact setAll_objsK q hq w _ _ (hashOk_empty q)
  have hcv : valOf q w ((livePairs w d).foldl (fun d kv => putH q w d kv.1 kv.2) empty) a = valOf q w d a := by
    rw [valOf_fold q hq w a ha _ _ hal, valOf_empty, ovr_val q hq a _ hu, valOf_live q w d a]
  have hco : HashOk q ((livePairs w d).foldl (fun d kv => putH q w d kv.1 kv.2) empty) :=
    hashOk_fold q hq w _ _ (hashOk_empty q)
  refine ⟨⟨_, hc, hcv, hco⟩, rfl, rfl, ?_, ?_⟩
  · refine ⟨items.foldl (fun d kv => putH q w d kv.1 kv.2)
      ((livePairs w d).foldl (fun d kv => putH q w d kv.1 kv.2) empty), ?_, ?_⟩
    · simp only [or_, hc, update, Bool.false_eq_true, if_false]
      rw [show (objsK items).map Except.ok = (objsK items).map Except.ok ++ [] by simp,
        storeAll_objsK q hq w [] none items _ hco]
      rfl
    · rw [valOf_fold q hq w a ha _ _ hit, hcv]
  · have h0 := hashOk_fold q hq w items _ (hashOk_empty q)
    refine ⟨(livePairs w d).foldl (fun d kv => putH q w d kv.1 kv.2)
      (items.foldl (fun d kv => putH q w d kv.1 kv.2) empty), ?_, ?_⟩
    · simp only [ror, update, Bool.false_eq_true, if_false]
      rw [show (objsK items).map Except.ok = (objsK items).map Except.ok ++ [] by simp,
        storeAll_objsK q hq w [] none items _ (hashOk_empty q)]
      simp only [storeAll, liveItems_eq]
      rw [show (objsK (livePairs w d)).map Except.ok = (objsK (livePairs w d)).map Except.ok ++ [] by simp,
        storeAll_objsK q hq w [] none _ _ h0]
      rfl
    · rw [valOf_fold q hq w a ha _ _ hal, valOf_fold q hq w a ha _ _ hit, valOf_empty]

/-- `update`, `|=`, `__init__`. Any keyword is refused first, so nothing of `dict` is applied
(3.15.2, Lib/weakref.py:411-414). An exception from `hasattr(dict, "items")`, from `dict.items()`, from
`iter(dict)` or from building `type({})(dict)` changes nothing. Otherwise the items are stored in turn,
and the first failure (a key that `ref()` refuses, an element that does not unpack, the iterable's own
exception) stops there with the earlier items stored. `|=` is the same update; `__init__` with
`dict=None` is empty, and with a dict of hashable keys holds its items. -/
def WkdUpdate : Prop :=
  ∀ (V : Type) (q : ROps) (w : World) (d : WKD V) (e : PyExc) (it : KOther V) (pre : List (Nat × V))
    (x : Py (PV × V)) (post : List (Py (PV × V))) (stop : Option PyExc) (err : PyExc),
    d.update q w it true = (d, .error (.typeError
      "Keyword arguments are not supported: cannot create weak reference to 'str' object")) ∧
    d.update q w (.hasattrErr e) = (d, .error e) ∧
    d.update q w (.mapping (.error e)) = (d, .error e) ∧
    d.update q w (.seq (.error e)) = (d, .error e) ∧
    (∀ els, dictOfPairs q stop [] els = .error e → d.update q w (.seq (.ok ⟨els, stop⟩)) = (d, .error e)) ∧
    d.ior q w it = d.update q w it ∧
    WKD.init (V := V) q w .none = .ok empty ∧
    WKD.init (V := V) q w (.hasattrErr e) = .error e ∧
    (Hashable q → HashOk q d → (∀ kv ∈ pre, alive w kv.1 = true) →
      (x = .error err ∨ ∃ n v, x = .ok (.int n, v) ∧
        err = .typeError "cannot create weak reference to 'int' object") →
      d.update q w (.mapping (.ok ⟨(objsK pre).map Except.ok ++ x :: post, stop⟩)) =
        (pre.foldl (fun d kv => putH q w d kv.1 kv.2) d, .error err)) ∧
    (Hashable q → HashOk q d →
      d.update q w (.mapping (.ok ⟨(objsK pre).map Except.ok, stop⟩)) =
        (pre.foldl (fun d kv => putH q w d kv.1 kv.2) d, match stop with
          | some e => .error e
          | none => .ok ()) ∧
      WKD.init q w (.mapping (.ok ⟨(objsK pre).map Except.ok, none⟩)) =
        .ok (pre.foldl (fun d kv => putH q w d kv.1 kv.2) empty))

theorem wkdUpdate_proven : WkdUpdate := by
  intro V q w d e it pre x post stop err
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, ?_, ?_⟩
  · intro els h
    simp [update, h]
  · intro hq hd _ hx
    simp only [update, Bool.false_eq_true, if_false]
    rw [storeAll_objsK q hq w (x :: post) stop pre d hd]
    rcases hx with hx | ⟨n, v, hx, he⟩
    · subst hx; rfl
    · subst hx he
      simp [storeAll, setitem, lookup, refOf]
  · intro hq hd
    constructor
    · simp only [update, Bool.false_eq_true, if_false]
      rw [show (objsK pre).map Except.ok = (objsK pre).map Except.ok ++ [] by simp,
        storeAll_objsK q hq w [] stop pre d hd]
      cases stop <;> rfl
    · simp only [init, update, Bool.false_eq_true, if_false]
      rw [show (objsK pre).map Except.ok = (objsK pre).map Except.ok ++ [] by simp,
        storeAll_objsK q hq w [] none pre _ (hashOk_empty q)]
      rfl

end WKD

end PyLean.CoreLibs.Misc.Weakref
