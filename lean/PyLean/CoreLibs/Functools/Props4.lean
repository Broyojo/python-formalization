import PyLean.CoreLibs.Functools.Props3

/-!
Properties of `functools`, part four: `singledispatch` and the small helpers.
-/

namespace PyLean.CoreLibs.Functools

open PyLean

/-! ### C3 -/

theorem c3Merge_sublist : ∀ (fuel : Nat) (seqs : List (List Cls)) (r : List Cls),
    c3Merge fuel seqs = .ok r → ∀ s ∈ seqs, s.Sublist r
  | 0, _, _, h, _, _ => by simp [c3Merge] at h
  | fuel + 1, seqs, r, h, s, hs => by
    by_cases hempty : s = []
    · subst hempty; exact List.nil_sublist r
    have hsf : s ∈ seqs.filter (fun s => !s.isEmpty) :=
      List.mem_filter.mpr ⟨hs, by cases s <;> simp_all⟩
    simp only [c3Merge] at h
    split at h
    · next he =>
      have : seqs.filter (fun s => !s.isEmpty) = [] := by simpa using he
      rw [this] at hsf
      cases hsf
    · split at h
      · cases h
      · next c _ =>
        simp only [bind, Except.bind] at h
        split at h
        · cases h
        · next rest hrest =>
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          have hm : (if s.head? = some c then s.tail else s) ∈
              (seqs.filter (fun s => !s.isEmpty)).map
                (fun s => if s.head? = some c then s.tail else s) :=
            List.mem_map.mpr ⟨s, hsf, rfl⟩
          have ih := c3Merge_sublist fuel _ rest hrest _ hm
          by_cases hh : s.head? = some c
          · simp only [hh, ite_true] at ih
            cases s with
            | nil => exact absurd rfl hempty
            | cons x xs =>
              simp only [List.head?_cons, Option.some.injEq] at hh
              subst hh
              exact List.Sublist.cons₂ _ ih
          · simp only [hh, ite_false] at ih
            exact List.Sublist.cons _ ih

/-- `_c3_merge` keeps the order of every input sequence: each is a subsequence of the result. This
is the monotonicity that makes it a linearization. Its docstring, and the C3 definition. -/
def C3MergeMonotone : Prop :=
  ∀ (fuel : Nat) (seqs : List (List Cls)) (r : List Cls), c3Merge fuel seqs = .ok r →
    ∀ s ∈ seqs, s.Sublist r

theorem c3MergeMonotone_proven : C3MergeMonotone := c3Merge_sublist

/-- `_c3_mro(cls, abcs)` lists `cls`, and keeps the explicit and the other bases in their order
from `__bases__`, for any hierarchy and any ABC list: what `_compose_mro` relies on. -/
def C3MroKeepsBases : Prop :=
  ∀ (W : World) (fuel : Nat) (cls : Cls) (abcs r : List Cls), c3Mro W (fuel + 1) cls abcs = .ok r →
    cls ∈ r ∧ ((W.bases cls).take (boundaryOf W (W.bases cls))).Sublist r ∧
      ((W.bases cls).drop (boundaryOf W (W.bases cls))).Sublist r

theorem c3MroKeepsBases_proven : C3MroKeepsBases := by
  intro W fuel cls abcs r h
  simp only [c3Mro, bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · have key := c3Merge_sublist _ _ _ h
        refine ⟨?_, key _ (by simp), key _ (by simp)⟩
        have := key [cls] (by simp)
        exact this.subset (by simp)

/-- `_compose_mro` for a class has that class in the result, and a successful composition is a
`_c3_mro`, so the base order is kept as above. -/
def ComposeMroIsC3 : Prop :=
  ∀ (W : World) (fuel : Nat) (cls : Cls) (types r : List Cls),
    composeMro W (fuel + 1) cls types = .ok r → cls ∈ r

theorem composeMroIsC3_proven : ComposeMroIsC3 := by
  intro W fuel cls types r h
  exact (c3MroKeepsBases_proven W fuel cls _ r h).1

/-! ### `_find_impl` -/

theorem findLoop_some {ι : Type} (W : World) (cls : Cls) (reg : Registry ι) :
    ∀ (mro : List Cls) (m : Cls), findLoop W cls reg none mro = .ok (some m) →
    ∃ pre post, mro = pre ++ m :: post ∧ (reg.lookup m).isSome ∧ ∀ t ∈ pre, (reg.lookup t).isNone
  | [], _, h => by simp [findLoop] at h
  | t :: rest, m, h => by
    simp only [findLoop] at h
    by_cases hr : (reg.lookup t).isSome = true
    · rw [if_pos hr] at h
      cases rest with
      | nil =>
        simp only [findLoop, Except.ok.injEq, Option.some.injEq] at h
        subst h
        exact ⟨[], [], rfl, hr, by simp⟩
      | cons u us =>
        simp only [findLoop] at h
        split at h
        · cases h
        · simp only [Except.ok.injEq, Option.some.injEq] at h
          subst h
          exact ⟨[], u :: us, rfl, hr, by simp⟩
    · rw [if_neg hr] at h
      obtain ⟨pre, post, h1, h2, h3⟩ := findLoop_some W cls reg rest m h
      refine ⟨t :: pre, post, by simp [h1], h2, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · cases hv : reg.lookup x with
        | none => rfl
        | some v => exact absurd (by simp [hv]) hr
      · exact h3 x hx

/-- `_find_impl` takes the first class of the composed MRO that has a registered implementation:
everything before it has none. Its docstring: "the best matching implementation". `_compose_mro`
may raise, which a separate step reports as ambiguous dispatch. -/
def FindImplFirstMatch : Prop :=
  ∀ (ι : Type) (W : World) (cls : Cls) (reg : Registry ι) (mro : List Cls) (m : Cls),
    findLoop W cls reg none mro = .ok (some m) →
    ∃ pre post, mro = pre ++ m :: post ∧ (reg.lookup m).isSome ∧ ∀ t ∈ pre, (reg.lookup t).isNone

theorem findImplFirstMatch_proven : FindImplFirstMatch :=
  fun _ W cls reg mro m h => findLoop_some W cls reg mro m h

/-! ### `register` and `dispatch` -/

section
variable {ι : Type}

theorem regSet_lookup : ∀ (reg : Registry ι) (c : Cls) (i : ι), (regSet reg c i).lookup c = some i
  | [], c, i => by simp [regSet, List.lookup]
  | p :: ps, c, i => by
    by_cases e : p.1 = c
    · simp [regSet, e, List.lookup]
    · have e1 : (p.1 == c) = false := by simpa using e
      have e2 : (c == p.1) = false := by
        have : c ≠ p.1 := fun x => e x.symm
        simpa using this
      simp only [regSet, e1, Bool.false_eq_true, ite_false, List.lookup, e2]
      exact regSet_lookup ps c i

theorem regSet_lookup_ne : ∀ (reg : Registry ι) (c d : Cls) (i : ι), c ≠ d →
    (regSet reg d i).lookup c = reg.lookup c
  | [], c, d, i, h => by
    have : (c == d) = false := by simpa using h
    simp [regSet, List.lookup, this]
  | p :: ps, c, d, i, h => by
    by_cases e : p.1 = d
    · have e1 : (c == p.1) = false := by
        have : c ≠ p.1 := by rw [e]; exact h
        simpa using this
      have e2 : (c == d) = false := by simpa using h
      simp [regSet, e, List.lookup, e2]
    · have e1 : (p.1 == d) = false := by simpa using e
      simp only [regSet, e1, Bool.false_eq_true, ite_false, List.lookup]
      rw [regSet_lookup_ne ps c d i h]

theorem foldl_regSet_lookup (f : ι) : ∀ (cs : List Cls) (r : Registry ι) (c : Cls),
    (c ∈ cs ∨ r.lookup c = some f) → (cs.foldl (fun r c => regSet r c f) r).lookup c = some f
  | [], _, _, h => by simpa using h
  | d :: ds, r, c, h => by
    simp only [List.foldl_cons]
    apply foldl_regSet_lookup f ds
    by_cases e : c = d
    · subst e
      exact Or.inr (regSet_lookup r c f)
    · rcases h with h | h
      · rcases List.mem_cons.mp h with h | h
        · exact absurd h e
        · exact Or.inl h
      · right
        rw [regSet_lookup_ne r c d f e, h]

theorem cached_keeps (W : World) (fuel : Nat) (d : Dispatcher ι) (c : Cls) :
    (dispatchCached W fuel d c).2.registry = d.registry ∧
    (dispatchCached W fuel d c).2.token = d.token := by
  unfold dispatchCached
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

theorem cached_hit (W : World) (fuel : Nat) (d : Dispatcher ι) (c : Cls) (r : Option ι)
    (h : (dispatchCached W fuel d c).1 = .ok r) :
    (dispatchCached W fuel d c).2.cache.lookup c = some r := by
  unfold dispatchCached at h ⊢
  have e : (c == c) = true := by simp
  split
  · next i hi =>
    rw [hi] at h
    simp only [Except.ok.injEq] at h
    subst h
    simpa using hi
  · next hi =>
    rw [hi] at h
    simp only at h ⊢
    split
    · next i hj =>
      rw [hj] at h
      simp only [Except.ok.injEq] at h
      subst h
      simp [List.lookup]
    · next hj =>
      rw [hj] at h
      simp only at h ⊢
      split
      · next e' hk =>
        rw [hk] at h
        cases h
      · next i hk =>
        rw [hk] at h
        simp only [Except.ok.injEq] at h
        subst h
        simp [List.lookup]

theorem sync_token (tok : Nat) (d : Dispatcher ι) :
    (tokenSync tok d).token = none ∨ (tokenSync tok d).token = some tok := by
  unfold tokenSync
  cases ht : d.token with
  | none => simp [ht]
  | some t =>
    by_cases h : t ≠ tok
    · simp [h]
    · simp [h, ht]
      omega

theorem sync_noop (tok : Nat) (x : Dispatcher ι)
    (h : x.token = none ∨ x.token = some tok) : tokenSync tok x = x := by
  unfold tokenSync
  rcases h with h | h <;> simp [h]

end

/-- `register` wins over everything for its own class: right after `register(c, f)`, and for each
member of a union `register(a | b, f)`, `dispatch(c)` returns `f`. Docs of `singledispatch`; the
registration clears the cache. -/
def RegisterThenDispatch : Prop :=
  ∀ (ι : Type) (W : World) (fuel t tok : Nat) (d : Dispatcher ι) (f : ι) (c : Cls) (cs : List Cls),
    (dispatch W fuel tok (register W t d (.cls c) f) c).1 = .ok (some f) ∧
    (c ∈ cs → (dispatch W fuel tok (register W t d (.union cs) f) c).1 = .ok (some f))

theorem registerThenDispatch_proven : RegisterThenDispatch := by
  intro ι W fuel t tok d f c cs
  have reset : ∀ (x : Dispatcher ι), x.cache = [] → (x.registry.lookup c = some f) →
      (dispatch W fuel tok x c).1 = .ok (some f) := by
    intro x hc hl
    have hs : (tokenSync tok x).cache = [] ∧ (tokenSync tok x).registry = x.registry := by
      unfold tokenSync
      cases x.token with
      | none => exact ⟨hc, rfl⟩
      | some u =>
        by_cases h : u ≠ tok
        · simp [h]
        · simp [h, hc]
    simp only [dispatch, dispatchCached, hs.1, hs.2, hl, List.lookup]
  constructor
  · exact reset _ rfl (regSet_lookup _ _ _)
  · intro h
    exact reset _ rfl (foldl_regSet_lookup f cs _ c (Or.inl h))

/-- `dispatch(cls)` is stable while nothing changes: a second call with the same ABC token gives the
first answer, from the cache. Invariant of the cache. -/
def DispatchIdempotent : Prop :=
  ∀ (ι : Type) (W : World) (fuel tok : Nat) (d : Dispatcher ι) (c : Cls) (r : Option ι),
    (dispatch W fuel tok d c).1 = .ok r →
    (dispatch W fuel tok (dispatch W fuel tok d c).2 c).1 = .ok r

theorem dispatchIdempotent_proven : DispatchIdempotent := by
  intro ι W fuel tok d c r h
  simp only [dispatch] at h ⊢
  have hk := (cached_keeps W fuel (tokenSync tok d) c).2
  rw [sync_noop tok _ (by rw [hk]; exact sync_token tok d)]
  have hit := cached_hit W fuel (tokenSync tok d) c r h
  simp only [dispatchCached.eq_def (d := (dispatchCached W fuel (tokenSync tok d) c).2), hit]

/-- `singledispatch` notices a new virtual subclass of a registered ABC: after `register(abc, f)`, a
change of the ABC cache token drops what was cached, so `dispatch` recomputes in the new world. This
is the purpose of `cache_token`, Lib/functools.py:900-905, 973-974. -/
def AbcRegistrationInvalidates : Prop :=
  ∀ (ι : Type) (W W' : World) (fuel t tok : Nat) (o a c : Cls) (f g : ι), W.isAbc a = true →
    t ≠ tok →
    let d1 := register W t (newDispatcher o g) (.cls a) f
    (dispatch W' fuel tok (dispatch W fuel t d1 c).2 c).1 = (dispatch W' fuel tok d1 c).1

theorem abcRegistrationInvalidates_proven : AbcRegistrationInvalidates := by
  intro ι W W' fuel t tok o a c f g hab hne d1
  have hd1t : d1.token = some t := by simp [d1, register, newDispatcher, hab]
  have hsame : tokenSync t d1 = d1 := sync_noop t d1 (Or.inr hd1t)
  have hk := cached_keeps W fuel d1 c
  simp only [dispatch, hsame]
  generalize dispatchCached W fuel d1 c = q at hk
  obtain ⟨hr, ht⟩ := hk
  have e1 : tokenSync tok q.2 = tokenSync tok d1 := by
    simp only [tokenSync, ht, hd1t, ne_eq, hne, not_false_eq_true, ite_true, hr]
  rw [e1]

/-- The same for a union: `register(abc | other, f)` notices a new virtual subclass of `abc` as
`register(abc, f)` does. False: at Lib/functools.py:973 the test `hasattr(cls, '__abstractmethods__')`
sees the `UnionType`, so `cache_token` stays `None`, and a stale `dispatch_cache` entry survives
`abc.register`. -/
def UnionAbcRegistrationInvalidates : Prop :=
  ∀ (W W' : World) (fuel t tok : Nat) (o c : Cls) (cs : List Cls) (f g : Nat),
    (∃ a ∈ cs, W.isAbc a = true) → t ≠ tok →
    let d1 := register W t (newDispatcher o g) (.union cs) f
    (dispatch W' fuel tok (dispatch W fuel t d1 c).2 c).1 = (dispatch W' fuel tok d1 c).1

/-- A world of `object` (0), an ABC (1) and a plain class (2). -/
def world0 : World where
  bases c := if c = 0 then [] else [0]
  mro c := if c = 0 then [0] else [c, 0]
  isSub a b := a == b || b == 0
  isAbc c := c == 1
  subclasses _ := []

/-- The same world after `abc.register(cls)`. -/
def world1 : World := { world0 with isSub := fun a b => a == b || b == 0 || (a == 2 && b == 1) }

theorem unionAbcRegistrationInvalidates_refuted : ¬UnionAbcRegistrationInvalidates := by
  intro h
  have := h world0 world1 4 0 1 0 2 [1] 5 9 ⟨1, by simp, rfl⟩ (by omega)
  revert this
  decide

end PyLean.CoreLibs.Functools
