import PyLean.CoreLibs.Functools.Props2

/-!
Properties of `functools`, part three: the `lru_cache` wrappers and `singledispatch`.
-/

namespace PyLean.CoreLibs.Functools

open PyLean

section Lru
variable {K V : Type} [DecidableEq K]

theorem filterMap_ring (l : List (K × V)) :
    ((none :: l.map some : List (Option (K × V))).filterMap id) = l := by
  simp only [List.filterMap_cons, id, List.filterMap_map]
  simp

theorem ringExtract_eq (k : K) (l : List (K × V)) :
    ringExtract k (none :: l.map some) = none :: (extract k l).map some := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [ringExtract, extract, List.map_cons, List.filter_cons, ite_true] at ih ⊢
    by_cases h : p.1 = k <;> simp [h] <;> simpa using ih

theorem lookup_mem : ∀ (l : List (K × V)) (k : K) (v : V), l.lookup k = some v → (k, v) ∈ l
  | [], _, _, h => by cases h
  | (a, b) :: rest, k, v, h => by
    by_cases e : k = a
    · subst e
      simp [List.lookup] at h
      simp [h]
    · have e' : (k == a) = false := by simpa using e
      simp only [List.lookup, e'] at h
      exact List.mem_cons_of_mem _ (lookup_mem rest k v h)

theorem length_extract : ∀ (l : List (K × V)) (k : K) (v : V), (l.map Prod.fst).Nodup →
    l.lookup k = some v → (extract k l).length + 1 = l.length
  | [], _, _, _, h => by cases h
  | (a, b) :: rest, k, v, hn, h => by
    have hn' := List.nodup_cons.mp hn
    by_cases e : k = a
    · subst e
      have : extract k rest = rest := by
        apply List.filter_eq_self.mpr
        intro p hp
        have : p.1 ≠ k := fun e => hn'.1 (List.mem_map.mpr ⟨p, hp, e⟩)
        simpa using this
      simp [extract, List.filter_cons] at this ⊢
      omega
    · have e' : (k == a) = false := by simpa using e
      simp only [List.lookup, e'] at h
      have ih := length_extract rest k v hn'.2 h
      have ne : a ≠ k := fun x => e x.symm
      simp only [extract] at ih ⊢
      rw [List.filter_cons_of_pos (by simpa using ne)]
      simp only [List.length_cons]
      omega

theorem mem_extract_keys (k : K) (l : List (K × V)) :
    (extract k l).map Prod.fst = (l.map Prod.fst).filter (· ≠ k) := by
  simp [extract, List.filter_map, Function.comp_def]

theorem nodup_extract_snoc (k : K) (v : V) (l : List (K × V)) (hn : (l.map Prod.fst).Nodup) :
    ((extract k l ++ [(k, v)]).map Prod.fst).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨?_, by simp, ?_⟩
  · rw [mem_extract_keys]
    exact hn.sublist List.filter_sublist
  · intro a ha b hb
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
    subst hb
    rw [mem_extract_keys] at ha
    have := (List.mem_filter.mp ha).2
    simpa using this

theorem lookup_none_not_mem : ∀ (l : List (K × V)) (k : K), l.lookup k = none →
    k ∉ l.map Prod.fst
  | [], _, _ => by simp
  | (a, b) :: rest, k, h => by
    by_cases e : k = a
    · subst e
      simp [List.lookup] at h
    · have e' : (k == a) = false := by simpa using e
      simp only [List.lookup, e'] at h
      have := lookup_none_not_mem rest k h
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨e, this⟩

theorem nodup_snoc_of_lookup_none (k : K) (v : V) (l : List (K × V)) (hn : (l.map Prod.fst).Nodup)
    (h : l.lookup k = none) : ((l ++ [(k, v)]).map Prod.fst).Nodup := by
  have hk := lookup_none_not_mem l k h
  rw [List.map_append, List.nodup_append]
  refine ⟨hn, by simp, ?_⟩
  intro a ha b hb
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
  subst hb
  intro e
  exact hk (e ▸ ha)

/-- The C state and the Python state describe the same cache. -/
structure Rel (m : Nat) (c : CLru K V) (p : PyLru K V) : Prop where
  ring : p.ring = none :: c.links.map some
  hits : p.hits = c.hits
  misses : p.misses = c.misses
  full : p.full = decide (c.links.length ≥ m)
  bound : c.links.length ≤ m
  nodup : (c.links.map Prod.fst).Nodup

theorem step_rel (m : Nat) (hm : 0 < m) (f : K → Py V) (c : CLru K V) (p : PyLru K V) (key : K)
    (h : Rel m c p) :
    (stepPy m f p key).1 = (stepC m f c key).1 ∧ Rel m (stepC m f c key).2 (stepPy m f p key).2 := by
  have hfm : (p.ring.filterMap id) = c.links := by rw [h.ring, filterMap_ring]
  cases hl : c.links.lookup key with
  | some r =>
    have hext := length_extract c.links key r h.nodup hl
    have hp : stepPy m f p key =
        (.ok r, { p with ring := ringExtract key p.ring ++ [some (key, r)], hits := p.hits + 1 }) := by
      simp only [stepPy, hfm, hl]
    have hc : stepC m f c key =
        (.ok r, { c with links := extract key c.links ++ [(key, r)], hits := c.hits + 1 }) := by
      simp only [stepC, hl]
    rw [hp, hc]
    refine ⟨rfl, ?_⟩
    have hlen : (extract key c.links ++ [(key, r)]).length = c.links.length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    constructor
    · simp [h.ring, ringExtract_eq]
    · simp [h.hits]
    · exact h.misses
    · simp only [hlen]; exact h.full
    · simp only [hlen]; exact h.bound
    · exact nodup_extract_snoc key r c.links h.nodup
  | none =>
    cases hf : f key with
    | error e =>
      have hp : stepPy m f p key = (.error e, { p with misses := p.misses + 1 }) := by
        simp only [stepPy, hfm, hl, hf]
      have hc : stepC m f c key = (.error e, { c with misses := c.misses + 1 }) := by
        simp only [stepC, hl, hf]
      rw [hp, hc]
      exact ⟨rfl, ⟨h.ring, h.hits, by simp [h.misses], h.full, h.bound, h.nodup⟩⟩
    | ok r =>
      by_cases hfull : c.links.length ≥ m
      · have hpf : p.full = true := by rw [h.full]; simpa using hfull
        cases hlinks : c.links with
        | nil =>
          rw [hlinks] at hfull
          simp at hfull
          omega
        | cons a rest =>
          have hring : p.ring = none :: some a :: rest.map some := by rw [h.ring, hlinks]; rfl
          have hp : stepPy m f p key = (.ok r,
              { p with ring := none :: rest.map some ++ [some (key, r)], misses := p.misses + 1 }) := by
            simp only [stepPy, hfm, hl, hf, hpf, ite_true]
            simp only [hring]
          have hne : ¬ (c.links.length < m ∨ c.links.isEmpty = true) := by
            simp [hlinks] at hfull ⊢
            omega
          have hc : stepC m f c key =
              (.ok r, { c with links := rest ++ [(key, r)], misses := c.misses + 1 }) := by
            simp only [stepC, hl, hf, if_neg hne]
            simp only [hlinks, List.tail_cons]
          rw [hp, hc]
          refine ⟨rfl, ?_⟩
          have hb := h.bound
          rw [hlinks] at hb hfull
          have hnd := h.nodup
          rw [hlinks] at hnd
          have hnd' := (List.nodup_cons.mp hnd).2
          have hlk : rest.lookup key = none := by
            have h2 := hl
            rw [hlinks] at h2
            by_cases e : key = a.1
            · simp [List.lookup, e] at h2
            · have e' : (key == a.1) = false := by simpa using e
              simpa [List.lookup, e'] using h2
          constructor
          · simp
          · exact h.hits
          · simp [h.misses]
          · simp only [List.length_append, List.length_cons, List.length_nil] at hfull ⊢
            rw [hpf]
            simpa using hfull
          · simp only [List.length_append, List.length_cons, List.length_nil] at hb ⊢
            omega
          · exact nodup_snoc_of_lookup_none key r rest hnd' hlk
      · have hpf : p.full = false := by rw [h.full]; simpa using hfull
        have hlt : c.links.length < m := by omega
        have hp : stepPy m f p key = (.ok r,
            { p with ring := p.ring ++ [some (key, r)], misses := p.misses + 1, full := decide (((p.ring ++ [some (key, r)]).filterMap id).length ≥ m) }) := by
          simp only [stepPy, hfm, hl, hf, hpf, Bool.false_eq_true, ite_false]
        have hc : stepC m f c key =
            (.ok r, { c with links := c.links ++ [(key, r)], misses := c.misses + 1 }) := by
          have : c.links.length < m ∨ c.links.isEmpty = true := Or.inl hlt
          simp only [stepC, hl, hf, if_pos this]
        rw [hp, hc]
        refine ⟨rfl, ?_⟩
        have hfm2 : ((p.ring ++ [some (key, r)]).filterMap id) = c.links ++ [(key, r)] := by
          simp [List.filterMap_append, hfm]
        constructor
        · simp [h.ring]
        · exact h.hits
        · simp [h.misses]
        · simp only [hfm2]
        · simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        · exact nodup_snoc_of_lookup_none key r c.links h.nodup hl

theorem rel_empty (m : Nat) (hm : 0 < m) : Rel m (emptyC : CLru K V) (emptyPy : PyLru K V) :=
  ⟨rfl, rfl, rfl, by simp [emptyC, emptyPy]; omega, by simp [emptyC], by simp [emptyC]⟩

theorem run_rel (m : Nat) (hm : 0 < m) (f : K → Py V) : ∀ (ops : List (LruOp K)) (c : CLru K V)
    (p : PyLru K V), Rel m c p →
    (runPy m f p ops).1 = (runC m f c ops).1 ∧ Rel m (runC m f c ops).2 (runPy m f p ops).2
  | [], c, p, h => ⟨rfl, h⟩
  | .clear :: ops, _, _, _ => run_rel m hm f ops emptyC emptyPy (rel_empty m hm)
  | .call k :: ops, c, p, h => by
    obtain ⟨h1, h2⟩ := step_rel m hm f c p k h
    obtain ⟨h3, h4⟩ := run_rel m hm f ops _ _ h2
    simp only [runPy, runC]
    exact ⟨by simp [h1, h3], h4⟩

end Lru

/-- The bounded `lru_cache` wrappers in C (linked list) and in Python (ring that rotates its root)
behave identically on every sequence of calls and `cache_clear`s, for every `maxsize > 0`, any key
type and any user function that does not reenter the cache: the same results and exceptions, the
same `cache_info()`, and the cache never exceeds `maxsize`. Twin property. The C source's comment
at Modules/_functoolsmodule.c:1063 lists the structural differences this covers. -/
def LruBoundedTwins : Prop :=
  ∀ (K V : Type) [DecidableEq K] (m : Nat) (f : K → Py V) (ops : List (LruOp K)), 0 < m →
    (runPy m f emptyPy ops).1 = (runC m f emptyC ops).1 ∧
    infoPy m (runPy m f emptyPy ops).2 = infoC m (runC m f emptyC ops).2 ∧
    (runC m f emptyC ops).2.links.length ≤ m

theorem lruBoundedTwins_proven : LruBoundedTwins := by
  intro K V _ m f ops hm
  obtain ⟨h1, h2⟩ := run_rel m hm f ops emptyC emptyPy (rel_empty m hm)
  refine ⟨h1, ?_, h2.bound⟩
  simp only [infoPy, infoC, h2.ring, filterMap_ring, h2.hits, h2.misses]

/-- Every cached entry is what the user function returns for that key. -/
def Memo {K V : Type} (f : K → Py V) (l : List (K × V)) : Prop := ∀ p ∈ l, f p.1 = .ok p.2

/-- Caching is transparent: for a deterministic user function, each call of the bounded or the
unbounded wrapper returns what the user function would, value or exception, and the cache keeps
only correct entries. Every call counts as exactly one hit or one miss, and an exception caches
nothing. `lru_cache` docs. The `Memo` hypothesis is the invariant; it holds of the empty cache. -/
def LruTransparent : Prop :=
  ∀ (K V : Type) [DecidableEq K] (m : Nat) (f : K → Py V) (s : CLru K V) (k : K),
    Memo f s.links →
    (stepC m f s k).1 = f k ∧ Memo f (stepC m f s k).2.links ∧
    (stepC m f s k).2.hits + (stepC m f s k).2.misses = s.hits + s.misses + 1 ∧
    (stepInfinite f s k).1 = f k ∧ Memo f (stepInfinite f s k).2.links ∧
    (stepInfinite f s k).2.hits + (stepInfinite f s k).2.misses = s.hits + s.misses + 1

theorem lruTransparent_proven : LruTransparent := by
  intro K V _ m f s k hm
  have snoc : ∀ (l : List (K × V)) (r : V), f k = .ok r → Memo f l → Memo f (l ++ [(k, r)]) := by
    intro l r hr h p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact h p hp
    · simp only [List.mem_singleton] at hp
      subst hp
      exact hr
  cases hl : s.links.lookup k with
  | some r =>
    have hr : f k = .ok r := hm (k, r) (lookup_mem _ _ _ hl)
    have hsub : Memo f (extract k s.links) := fun p hp => hm p (List.mem_filter.mp hp).1
    have hc : stepC m f s k =
        (.ok r, { s with links := extract k s.links ++ [(k, r)], hits := s.hits + 1 }) := by
      simp only [stepC, hl]
    have hi : stepInfinite f s k = (.ok r, { s with hits := s.hits + 1 }) := by
      simp only [stepInfinite, hl]
    rw [hc, hi]
    exact ⟨hr.symm, snoc _ r hr hsub, by simp only; omega, hr.symm, hm, by simp only; omega⟩
  | none =>
    cases hf : f k with
    | error e =>
      have hc : stepC m f s k = (.error e, { s with misses := s.misses + 1 }) := by
        simp only [stepC, hl, hf]
      have hi : stepInfinite f s k = (.error e, { s with misses := s.misses + 1 }) := by
        simp only [stepInfinite, hl, hf]
      rw [hc, hi]
      exact ⟨rfl, hm, by simp only; omega, rfl, hm, by simp only; omega⟩
    | ok r =>
      have hi : stepInfinite f s k =
          (.ok r, { s with misses := s.misses + 1, links := s.links ++ [(k, r)] }) := by
        simp only [stepInfinite, hl, hf]
      rw [hi]
      by_cases hcond : s.links.length < m ∨ s.links.isEmpty = true
      · have hc : stepC m f s k =
            (.ok r, { s with misses := s.misses + 1, links := s.links ++ [(k, r)] }) := by
          simp only [stepC, hl, hf, if_pos hcond]
        rw [hc]
        exact ⟨rfl, snoc _ r hf hm, by simp only; omega, rfl, snoc _ r hf hm, by simp only; omega⟩
      · have hc : stepC m f s k =
            (.ok r, { s with misses := s.misses + 1, links := s.links.tail ++ [(k, r)] }) := by
          simp only [stepC, hl, hf, if_neg hcond]
        rw [hc]
        exact ⟨rfl, snoc _ r hf (fun p hp => hm p (List.mem_of_mem_tail hp)), by simp only; omega,
          rfl, snoc _ r hf hm, by simp only; omega⟩

/-- `maxsize=0` never caches: every call runs the user function and counts as a miss. -/
def LruUncached : Prop :=
  ∀ (K V : Type) (f : K → Py V) (n : Nat) (k : K), stepUncached f n k = (f k, n + 1)

theorem lruUncached_proven : LruUncached := fun _ _ _ _ _ => rfl

/-- `lru_cache` selects the same wrapper in both twins for every `maxsize` up to `sys.maxsize`, for
`None`, and for the bare-decorator form, a negative `maxsize` being `0`, and rejects the same bad
arguments. Twin property, narrowed to the `Py_ssize_t` range: see `LruMaxsizeTwinsAlways`. -/
def LruModeTwins : Prop :=
  ∀ a : MaxsizeArg, (∀ n, a = .int n → n ≤ ssizeMax) →
    (do wrapperCMode (← lruCacheArg a)) = (do wrapperPyMode (← lruCacheArg a))

theorem lruModeTwins_proven : LruModeTwins := by
  intro a h
  cases a with
  | none => rfl
  | other => rfl
  | callable b => cases b <;> rfl
  | int n =>
    have hn := h n rfl
    simp only [lruCacheArg, bind, Except.bind]
    unfold ssizeMax at hn
    by_cases h0 : n < 0
    · simp [h0, wrapperCMode, wrapperPyMode, ssizeMax, ssizeMin]
    · simp only [h0, ite_false]
      by_cases h1 : n = 0
      · subst h1
        simp [wrapperCMode, wrapperPyMode, ssizeMax, ssizeMin]
      · have h2 : ¬ (n > ssizeMax ∨ n < ssizeMin) := by
          unfold ssizeMax ssizeMin; omega
        have h3 : ¬ n ≤ 0 := by omega
        simp only [wrapperCMode, h2, ite_false, h3]
        cases n with
        | ofNat k =>
          cases k with
          | zero => exact absurd rfl h1
          | succ k => rfl
        | negSucc k => omega

/-- `lru_cache(maxsize=n)` selects the same wrapper in both twins for every `int`. False: the C
wrapper converts `maxsize` to `Py_ssize_t` and raises `OverflowError` above `sys.maxsize`. -/
def LruMaxsizeTwinsAlways : Prop :=
  ∀ n : Int, wrapperCMode (some n) = wrapperPyMode (some n)

theorem lruMaxsizeTwinsAlways_refuted : ¬LruMaxsizeTwinsAlways := by
  intro h
  have := h (2 ^ 63)
  simp [wrapperCMode, wrapperPyMode, ssizeMax, ssizeMin] at this

end PyLean.CoreLibs.Functools
