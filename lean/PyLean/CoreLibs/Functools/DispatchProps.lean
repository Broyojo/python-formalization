import PyLean.CoreLibs.Functools.Dispatch
import PyLean.CoreLibs.Functools.PartialProps

/-!
Properties of `singledispatch`.
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

theorem filterPy_mem {α : Type} (p : α → Py Bool) : ∀ (l r : List α) (x : α), filterPy p l = .ok r →
    x ∈ l → p x = .ok true → x ∈ r
  | [], _, _, _, h, _ => by cases h
  | y :: ys, r, x, h, hm, hp => by
    simp only [filterPy] at h
    split at h
    · cases h
    · next b hb =>
      split at h
      · cases h
      · next t ht =>
        simp only [Except.ok.injEq] at h
        subst h
        rcases List.mem_cons.mp hm with rfl | hm
        · rw [hp] at hb
          cases hb
          simp
        · have := filterPy_mem p ys t x ht hm hp
          cases b <;> simp [this]

theorem filterPy_sat {α : Type} (p : α → Py Bool) : ∀ (l r : List α) (x : α), filterPy p l = .ok r →
    x ∈ r → x ∈ l ∧ p x = .ok true
  | [], r, _, h, hm => by cases h; cases hm
  | y :: ys, r, x, h, hm => by
    simp only [filterPy] at h
    split at h
    · cases h
    · next b hb =>
      split at h
      · cases h
      · next t ht =>
        simp only [Except.ok.injEq] at h
        subst h
        cases b with
        | false =>
          have := filterPy_sat p ys t x ht (by simpa using hm)
          exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
        | true =>
          simp only [ite_true, List.mem_cons] at hm
          rcases hm with rfl | hm
          · exact ⟨by simp, hb⟩
          · have := filterPy_sat p ys t x ht hm
            exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

theorem anyPy_false {α : Type} (p : α → Py Bool) : ∀ l : List α, (∀ x ∈ l, p x = .ok false) →
    anyPy p l = .ok false
  | [], _ => rfl
  | x :: xs, h => by
    simp only [anyPy, h x (by simp)]
    exact anyPy_false p xs (fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- `_c3_mro(cls, abcs)` keeps the explicit and the other bases of `cls` in `__bases__` order, and inserts
each ABC that `cls` introduces: `issubclass(cls, abc)` holds and no direct base is a subclass of it. The
docstring's "inserts ABCs where their functionality is introduced". `issubclass` is fallible, so a raising
hook is an error of the whole call, not a false; the hypotheses say that the reads involved give those
answers. -/
def C3MroInsertsAbcs : Prop :=
  ∀ (W : World) (fuel : Nat) (cls b : Cls) (abcs r : List Cls), c3Mro W (fuel + 1) cls abcs = .ok r →
    cls ∈ r ∧ ((W.bases cls).take (boundaryOf W (W.bases cls))).Sublist r ∧
      ((W.bases cls).drop (boundaryOf W (W.bases cls))).Sublist r ∧
      (b ∈ abcs → W.isSub cls b = .ok true → (∀ x ∈ W.bases cls, W.isSub x b = .ok false) → b ∈ r)

theorem c3MroInsertsAbcs_proven : C3MroInsertsAbcs := by
  intro W fuel cls b abcs r h
  simp only [c3Mro, bind, Except.bind] at h
  split at h
  · cases h
  · next ab hab =>
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · have key := c3Merge_sublist _ _ _ h
          refine ⟨?_, key _ (by simp), key _ (by simp), ?_⟩
          · exact (key [cls] (by simp)).subset (by simp)
          · intro hb h1 h2
            have hi : introduces W cls b = .ok true := by
              simp only [introduces, h1, anyPy_false _ _ h2]
              rfl
            have hm := filterPy_mem _ _ _ b hab hb hi
            exact (key ab (by simp)).subset hm

/-- `_c3_mro` raises what `issubclass(cls, base)` raises: a failing `__subclasshook__` is not swallowed. -/
def C3MroHookPropagates : Prop :=
  ∀ (W : World) (fuel : Nat) (cls b : Cls) (rest : List Cls) (e : PyExc),
    W.isSub cls b = .error e → c3Mro W (fuel + 1) cls (b :: rest) = .error e

theorem c3MroHookPropagates_proven : C3MroHookPropagates := by
  intro W fuel cls b rest e h
  simp [c3Mro, filterPy, introduces, h, bind, Except.bind]

theorem foldPy_step_mem (W : World) (cls : Cls) (types : List Cls) (t : Cls)
    (ht : foundFor W cls types t = .ok []) : ∀ (l : List Cls) (acc r : List Cls),
    foldPy (composeStep W cls types) acc l = .ok r → (t ∈ acc ∨ t ∈ l) → t ∈ r
  | [], acc, r, h, hm => by
    simp only [foldPy, Except.ok.injEq] at h
    subst h
    simpa using hm
  | x :: xs, acc, r, h, hm => by
    simp only [foldPy] at h
    split at h
    · cases h
    · next a' ha =>
      refine foldPy_step_mem W cls types t ht xs a' r h ?_
      have hsub : ∀ y ∈ acc, y ∈ a' := by
        intro y hy
        simp only [composeStep, bind, Except.bind] at ha
        split at ha
        · cases ha
        · next found _ =>
          simp only [pure, Except.pure] at ha
          split at ha
          · cases ha
            simp [hy]
          · cases ha
            have step : ∀ (ss : List (List Cls)) (a : List Cls), y ∈ a →
                y ∈ ss.foldl (fun acc sub =>
                  sub.foldl (fun acc s => if s ∈ acc then acc else acc ++ [s]) acc) a := by
              intro ss
              induction ss with
              | nil => intro a h; exact h
              | cons s ss ih =>
                intro a h
                apply ih
                have inner : ∀ (l : List Cls) (a : List Cls), y ∈ a →
                    y ∈ l.foldl (fun acc s => if s ∈ acc then acc else acc ++ [s]) a := by
                  intro l
                  induction l with
                  | nil => intro a h; exact h
                  | cons u us ih2 =>
                    intro a h
                    apply ih2
                    by_cases hu : u ∈ a <;> simp [hu, h]
                exact inner s a h
            exact step _ _ hy
      rcases hm with hm | hm
      · exact Or.inl (hsub t hm)
      · rcases List.mem_cons.mp hm with rfl | hm
        · left
          simp only [composeStep, ht, bind, Except.bind, pure, Except.pure, List.isEmpty_nil, ite_true,
            Except.ok.injEq] at ha
          subst ha
          simp
        · exact Or.inr hm

/-- `_compose_mro` passes on a related type: one that is not in `cls.__mro__`, is a real class and not a
`GenericAlias`, that `cls` is a subclass of, not a strict base of another selected type, and with no
subclass implemented by `cls`. So the selection at Lib/functools.py:816-828 is not vacuous; a type that
fails `is_related` raises nothing and is dropped. The docstring's "includes relevant abstract base classes". -/
def ComposeSelectsRelated : Prop :=
  ∀ (W : World) (cls t : Cls) (types selected r : List Cls),
    filterPy (isRelated W cls) types = .ok selected →
    composeAbcs W cls types = .ok r →
    t ∈ types → isRelated W cls t = .ok true → isStrictBase W selected t = false →
    foundFor W cls (selected.filter (fun x => !isStrictBase W selected x)) t = .ok [] → t ∈ r

theorem composeSelectsRelated_proven : ComposeSelectsRelated := by
  intro W cls t types selected r hs hr ht hrel hb hf
  simp only [composeAbcs, hs, bind, Except.bind] at hr
  have hm := filterPy_mem _ _ _ t hs ht hrel
  refine foldPy_step_mem W cls _ t hf _ [] r hr (Or.inr ?_)
  exact List.mem_filter.mpr ⟨hm, by simp [hb]⟩

/-- Only related types are selected: a type already in `cls.__mro__`, or without `__mro__`, or a
`GenericAlias`, or that `cls` does not subclass, is never in the list. -/
def ComposeDropsUnrelated : Prop :=
  ∀ (W : World) (cls t : Cls) (types selected : List Cls), filterPy (isRelated W cls) types = .ok selected →
    t ∈ selected → t ∉ W.mro cls ∧ W.isType t = true ∧ W.isAlias t = false ∧ W.isSub cls t = .ok true

theorem composeDropsUnrelated_proven : ComposeDropsUnrelated := by
  intro W cls t types selected h hm
  have hr := (filterPy_sat _ _ _ t h hm).2
  simp only [isRelated] at hr
  split at hr
  · simp at hr
  · next c =>
    simp only [not_or] at c
    have c2 : W.isType t = true := by simpa using c.2.1
    have c3 : W.isAlias t = false := by simpa using c.2.2
    exact ⟨c.1, c2, c3, hr⟩


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
        · split at h
          · cases h
          · simp only [Except.ok.injEq, Option.some.injEq] at h
            subst h
            exact ⟨[], u :: us, rfl, hr, by simp⟩
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

/-- `_find_impl` returns the implementation of the first class of the composed MRO that has one: everything
before that class has none. Its docstring: "the best matching implementation". -/
def FindImplFirstMatch : Prop :=
  ∀ (ι : Type) (W : World) (fuel : Nat) (cls : Cls) (reg : Registry ι) (i : ι),
    findImpl W fuel cls reg = .ok (some i) → ∃ pre m post,
      composeMro W fuel cls (reg.map Prod.fst) = .ok (pre ++ m :: post) ∧ reg.lookup m = some i ∧
      ∀ t ∈ pre, (reg.lookup t).isNone

theorem findImplFirstMatch_proven : FindImplFirstMatch := by
  intro ι W fuel cls reg i h
  simp only [findImpl, bind, Except.bind] at h
  split at h
  · cases h
  · next mro hm =>
    split at h
    · cases h
    · next m hl =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      cases m with
      | none => simp at h
      | some c =>
        simp only [Option.bind_some] at h
        obtain ⟨pre, post, h1, _, h3⟩ := findLoop_some W cls reg mro c hl
        exact ⟨pre, c, post, by rw [hm, h1], h, h3⟩

/-- When the match and the next class of the MRO are two unrelated ABCs with implementations, neither in
`cls.__mro__`, `_find_impl` refuses to guess: `RuntimeError`, the path at Lib/functools.py:865-869. If
`issubclass(match, t)` raises, that exception comes out instead. -/
def FindImplAmbiguous : Prop :=
  ∀ (ι : Type) (W : World) (cls m t : Cls) (reg : Registry ι) (rest : List Cls),
    (reg.lookup m).isSome → (reg.lookup t).isSome → m ∉ W.mro cls → t ∉ W.mro cls →
    (W.isSub m t = .ok false → (findLoop W cls reg none (m :: t :: rest)).raises "RuntimeError") ∧
    (∀ e, W.isSub m t = .error e → findLoop W cls reg none (m :: t :: rest) = .error e) ∧
    (W.isSub m t = .ok true → findLoop W cls reg none (m :: t :: rest) = .ok (some m))

theorem findImplAmbiguous_proven : FindImplAmbiguous := by
  intro ι W cls m t reg rest h1 h2 h3 h4
  have hc1 : (W.mro cls).contains t = false := by simpa using h4
  have hc2 : (W.mro cls).contains m = false := by simpa using h3
  have base : findLoop W cls reg none (m :: t :: rest) =
      match W.isSub m t with
      | .error e => .error e
      | .ok true => .ok (some m)
      | .ok false => .error (.named "RuntimeError" "~Ambiguous dispatch") := by
    simp only [findLoop, h1, ite_true, h2, hc1, hc2, Bool.not_false, Bool.and_self]
    rfl
  refine ⟨fun h => ?_, fun e h => ?_, fun h => ?_⟩
  · rw [base, h]
    exact ⟨_, rfl, rfl⟩
  · rw [base, h]
  · rw [base, h]

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
    (dispatchCached W fuel d c).2.token = d.token ∧ (dispatchCached W fuel d c).2.name = d.name := by
  unfold dispatchCached
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl⟩

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
    (dispatch W fuel tok (regStore W t d (.cls c) f) c).1 = .ok (some f) ∧
    (c ∈ cs → (dispatch W fuel tok (regStore W t d (.union cs) f) c).1 = .ok (some f))

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
  have hk := (cached_keeps W fuel (tokenSync tok d) c).2.1
  rw [sync_noop tok _ (by rw [hk]; exact sync_token tok d)]
  have hit := cached_hit W fuel (tokenSync tok d) c r h
  simp only [dispatchCached.eq_def (d := (dispatchCached W fuel (tokenSync tok d) c).2), hit]

/-- `singledispatch` notices a new virtual subclass of a registered ABC: after `register(abc, f)`, a
change of the ABC cache token drops what was cached, so `dispatch` recomputes in the new world. This
is the purpose of `cache_token`, Lib/functools.py:900-905, 973-974. -/
def AbcRegistrationInvalidates : Prop :=
  ∀ (ι : Type) (W W' : World) (fuel t tok : Nat) (o a c : Cls) (f g : ι), W.isAbc a = true →
    t ≠ tok →
    let d1 := regStore W t (newDispatcher o g) (.cls a) f
    (dispatch W' fuel tok (dispatch W fuel t d1 c).2 c).1 = (dispatch W' fuel tok d1 c).1

theorem abcRegistrationInvalidates_proven : AbcRegistrationInvalidates := by
  intro ι W W' fuel t tok o a c f g hab hne d1
  have hd1t : d1.token = some t := by simp [d1, regStore, newDispatcher, hab]
  have hsame : tokenSync t d1 = d1 := sync_noop t d1 (Or.inr hd1t)
  have hk := cached_keeps W fuel d1 c
  simp only [dispatch, hsame]
  generalize dispatchCached W fuel d1 c = q at hk
  obtain ⟨hr, ht, hn⟩ := hk
  have e1 : tokenSync tok q.2 = tokenSync tok d1 := by
    simp only [tokenSync, ht, hd1t, ne_eq, hne, not_false_eq_true, ite_true, hr, hn]
  rw [e1]

/-- The same for a union: `register(abc | other, f)` notices a new virtual subclass of `abc` as
`register(abc, f)` does. False: at Lib/functools.py:973 the test `hasattr(cls, '__abstractmethods__')`
sees the `UnionType`, so `cache_token` stays `None`, and a stale `dispatch_cache` entry survives
`abc.register`. -/
def UnionAbcRegistrationInvalidates : Prop :=
  ∀ (W W' : World) (fuel t tok : Nat) (o c : Cls) (cs : List Cls) (f g : Nat),
    (∃ a ∈ cs, W.isAbc a = true) → t ≠ tok →
    let d1 := regStore W t (newDispatcher o g) (.union cs) f
    (dispatch W' fuel tok (dispatch W fuel t d1 c).2 c).1 = (dispatch W' fuel tok d1 c).1

/-- A world of `object` (0), an ABC (1) and a plain class (2). -/
def world0 : World where
  bases c := if c = 0 then [] else [0]
  mro c := if c = 0 then [0] else [c, 0]
  isSub a b := .ok (a == b || b == 0)
  isAbc c := c == 1
  subclasses _ := []
  isType _ := true
  isAlias _ := false

/-- The same world after `abc.register(cls)`. -/
def world1 : World := { world0 with isSub := fun a b => .ok (a == b || b == 0 || (a == 2 && b == 1)) }

theorem unionAbcRegistrationInvalidates_refuted : ¬UnionAbcRegistrationInvalidates := by
  intro h
  have := h world0 world1 4 0 1 0 2 [1] 5 9 ⟨1, by simp, rfl⟩ (by omega)
  revert this
  decide

/-! ### `register` -/

/-- `register` as a whole: a class stores and returns the function; a class with no function returns a
decorator and changes nothing; a value that is not a class, given with a function, is a `TypeError`; so is a
union with a non-class member; a function with no annotations is a `TypeError`; an annotation that is not a
class is a `TypeError`, for a union, a forward reference and anything else; an exception from
`get_type_hints` propagates. Each `TypeError` leaves the registry alone, because the state is only returned on
success. The checks at Lib/functools.py:929-966. -/
def RegisterValidates : Prop :=
  ∀ (ι : Type) (W : World) (tok : Nat) (d : Dispatcher ι) (f g : ι) (c : Cls) (e : PyExc)
    (as : List (Option Cls)) (n : String),
    (∃ d', register W tok d (.val (.cls c)) (some f) = .ok (.func f, d') ∧ d'.registry.lookup c = some f) ∧
    (∃ a, register W tok d (.val (.cls c)) none = .ok (a, d)) ∧
    (register W tok d (.val .other) (some f)).raises "TypeError" ∧
    (register W tok d (.val .other) none).raises "TypeError" ∧
    (none ∈ as → (register W tok d (.val (.union as)) (some f)).raises "TypeError") ∧
    (register W tok d (.func g none) none).raises "TypeError" ∧
    (register W tok d (.func g (some (.ok [(n, .other)]))) none).raises "TypeError" ∧
    (register W tok d (.func g (some (.ok [(n, .forwardRef)]))) none).raises "TypeError" ∧
    (none ∈ as → (register W tok d (.func g (some (.ok [(n, .union as)]))) none).raises "TypeError") ∧
    register W tok d (.func g (some (.error e))) none = .error e

theorem validType_union_none (as : List (Option Cls)) (h : none ∈ as) : validType (.union as) = none := by
  simp only [validType]
  have : as.mapM id = none := by
    induction as with
    | nil => cases h
    | cons x xs ih =>
      rcases List.mem_cons.mp h with rfl | hm
      · simp
      · cases x with
        | none => simp
        | some v => simp [ih hm]
  simp [this]

theorem registerValidates_proven : RegisterValidates := by
  intro ι W tok d f g c e as n
  refine ⟨⟨_, rfl, ?_⟩, ⟨_, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ?_, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩,
    ⟨_, rfl, rfl⟩, ?_, rfl⟩
  · exact regSet_lookup _ _ _
  · intro h
    exact ⟨_, by simp [register, validType_union_none as h]; rfl, rfl⟩
  · intro h
    exact ⟨_, by simp [register, validType_union_none as h]; rfl, rfl⟩

/-- `@f.register` on a function dispatches on its first parameter's annotation: the type hint of the first
parameter, not a later one and not the return annotation. The docs: "for functions annotated with types, the
decorator will infer the type of the first argument automatically". False: `next(iter(hints))` takes the first
entry of `get_type_hints`, so `def g(x) -> int` registers `int`, and `def g(x, y: int)` registers `int`
for the first parameter's slot. -/
def RegisterAnnotationIsFirstParam : Prop :=
  ∀ (W : World) (tok : Nat) (d : Dispatcher Nat) (g : Nat) (params : List String)
    (hints : List (String × TypeVal)) (r : Registered Nat) (d' : Dispatcher Nat),
    register W tok d (.func g (some (.ok hints))) none = .ok (r, d') →
    ∃ h, hints.head? = some h ∧ params.head? = some h.1

theorem registerAnnotationIsFirstParam_refuted : ¬RegisterAnnotationIsFirstParam := by
  intro h
  have := h world0 0 ⟨[], [], none, ""⟩ 7 ["x"] [("return", .cls 1)] (.func 7) _ rfl
  obtain ⟨p, h1, h2⟩ := this
  simp only [List.head?_cons, Option.some.injEq] at h1 h2
  subst h1
  simp at h2

/-- `register` never lets a `StopIteration` escape: every failure is a `TypeError` or what `get_type_hints`
raised. False: `next(iter(...))` at Lib/functools.py:950 on a function whose `__annotate__` returns no
annotations raises a bare `StopIteration`. -/
def RegisterNoStopIteration : Prop :=
  ∀ (W : World) (tok : Nat) (d : Dispatcher Nat) (g : Nat) (hints : List (String × TypeVal)),
    ¬(register W tok d (.func g (some (.ok hints))) none).raises "StopIteration"

theorem registerNoStopIteration_refuted : ¬RegisterNoStopIteration := by
  intro h
  exact h world0 0 ⟨[], [], none, ""⟩ 7 [] ⟨_, rfl, rfl⟩

/-- `dispatch` raises what `_find_impl` raises and leaves its cache alone, so a raising `__subclasshook__` or an
ambiguous dispatch raises again on the next call instead of being cached. The second call in the property
is on the state the first left. -/
def DispatchErrorNotCached : Prop :=
  ∀ (ι : Type) (W : World) (fuel tok : Nat) (d : Dispatcher ι) (c : Cls) (e : PyExc),
    (dispatch W fuel tok d c).1 = .error e →
    (dispatch W fuel tok (dispatch W fuel tok d c).2 c).1 = .error e

theorem dispatchErrorNotCached_proven : DispatchErrorNotCached := by
  intro ι W fuel tok d c e h
  simp only [dispatch] at h ⊢
  generalize hs : tokenSync tok d = s at h ⊢
  have htok : s.token = none ∨ s.token = some tok := by rw [← hs]; exact sync_token tok d
  simp only [dispatchCached] at h ⊢
  cases hc : s.cache.lookup c with
  | some i =>
    rw [hc] at h
    cases h
  | none =>
    rw [hc] at h
    simp only at h ⊢
    cases hr : s.registry.lookup c with
    | some i =>
      rw [hr] at h
      cases h
    | none =>
      rw [hr] at h
      simp only at h ⊢
      cases hf : findImpl W fuel c s.registry with
      | ok i =>
        rw [hf] at h
        cases h
      | error e' =>
        rw [hf] at h
        simp only at h ⊢
        rw [sync_noop tok s htok]
        simp only [dispatchCached, hc, hr, hf]
        exact h

end PyLean.CoreLibs.Functools
