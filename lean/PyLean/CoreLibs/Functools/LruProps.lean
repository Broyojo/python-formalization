import PyLean.CoreLibs.Functools.Lru

/-!
Properties of `lru_cache`: the twins agree on every re-entrant program while the dict's store and delete
succeed, and disagree when an insertion fails.
-/

namespace PyLean.CoreLibs.Functools

open PyLean

section
variable {K V : Type} [DecidableEq K]

theorem dropLastP_map {α β : Type} (f : α → β) (p : β → Bool) : ∀ l : List α,
    dropLastP p (l.map f) = (dropLastP (fun a => p (f a)) l).map f
  | [] => rfl
  | x :: xs => by
    have ih := dropLastP_map f p xs
    have hany : (xs.map f).any p = xs.any (fun a => p (f a)) := by
      rw [List.any_map]
      rfl
    simp only [List.map_cons, dropLastP, hany]
    by_cases h1 : xs.any (fun a => p (f a)) = true
    · simp [h1, ih]
    · by_cases h2 : p (f x) = true <;> simp [h1, h2]

theorem lookup_mem_iff (l : List (K × V)) (k : K) :
    (l.lookup k).isSome = true ↔ k ∈ l.map Prod.fst := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    by_cases e : k = p.1
    · simp [List.lookup, e]
    · have e' : (k == p.1) = false := by simpa using e
      simp only [List.lookup, e', List.map_cons, List.mem_cons, e, false_or]
      exact ih

theorem lastP_sat {α : Type} (p : α → Bool) : ∀ (l : List α) (y : α), lastP p l = some y → p y = true
  | [], _, h => by cases h
  | x :: xs, y, h => by
    simp only [lastP] at h
    cases hl : lastP p xs with
    | some z =>
      rw [hl] at h
      cases h
      exact lastP_sat p xs _ hl
    | none =>
      rw [hl] at h
      simp only at h
      split at h
      · next hp =>
        cases h
        exact hp
      · cases h

theorem lastP_ring (k : K) : ∀ l : List (K × V), (l.map Prod.fst).Nodup →
    (lastP (ringIs k) (l.map some)).join.map Prod.snd = l.lookup k
  | [], _ => rfl
  | p :: ps, hn => by
    have hn' := List.nodup_cons.mp hn
    have ih := lastP_ring k ps hn'.2
    by_cases e : k = p.1
    · have hno : ps.lookup k = none := by
        cases h : ps.lookup k with
        | none => rfl
        | some v =>
          have := (lookup_mem_iff ps k).mp (by simp [h])
          rw [e] at this
          exact absurd this hn'.1
      rw [hno] at ih
      cases hl : lastP (ringIs k) (ps.map some) with
      | some y =>
        rw [hl] at ih
        cases y with
        | none => exact absurd (lastP_sat _ _ _ hl) (by simp [ringIs])
        | some q => simp at ih
      | none =>
        have h1 : ringIs k (some p) = true := by simp [ringIs, e]
        have h2 : lastP (ringIs k) ((p :: ps).map some) = some (some p) := by
          simp only [List.map_cons, lastP, hl, h1, ite_true]
        rw [h2]
        simp [List.lookup, e]
    · have e' : (k == p.1) = false := by simpa using e
      have h1 : ringIs k (some p) = false := by
        have : p.1 ≠ k := fun x => e x.symm
        simp [ringIs, this]
      simp only [List.map_cons, lastP, List.lookup, e', h1]
      cases hl : lastP (ringIs k) (ps.map some) with
      | some y => simpa [hl] using ih
      | none => simpa [hl] using ih

theorem ringValue_links (k : K) (l : List (K × V)) (hn : (l.map Prod.fst).Nodup) :
    ringValue k (none :: l.map some) = l.lookup k := by
  simp only [ringValue, lastP]
  have h := lastP_ring k l hn
  cases hl : lastP (ringIs k) (l.map some) with
  | some y =>
    rw [hl] at h
    exact h
  | none =>
    rw [hl] at h
    simpa [ringIs] using h

/-- The C state and the Python state describe the same cache. -/
structure Rel (m : Nat) (c : CLru K V) (p : PyLru K V) : Prop where
  ring : p.ring = none :: c.links.map some
  cache : p.cache = c.cache
  hits : p.hits = c.hits
  misses : p.misses = c.misses
  full : p.full = decide (c.links.length ≥ m)
  broken : p.broken = false
  bound : c.links.length ≤ m
  nodup : (c.links.map Prod.fst).Nodup
  perm : c.cache.Perm (c.links.map Prod.fst)

theorem rel_empty (m : Nat) (hm : 0 < m) : Rel m (emptyC : CLru K V) (emptyPy : PyLru K V) :=
  ⟨rfl, rfl, rfl, rfl, by simp [emptyC, emptyPy]; omega, rfl, by simp [emptyC], by simp [emptyC],
    by simp [emptyC]⟩

theorem nodup_snoc (l : List (K × V)) (k : K) (v : V) (hn : (l.map Prod.fst).Nodup)
    (hk : k ∉ l.map Prod.fst) : ((l ++ [(k, v)]).map Prod.fst).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨hn, by simp, ?_⟩
  intro a ha b hb
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
  subst hb
  intro e
  exact hk (e ▸ ha)

theorem dropLastP_nodup (k : K) : ∀ l : List (K × V), (l.map Prod.fst).Nodup →
    (dropLastP (fun p => decide (p.1 = k)) l).map Prod.fst = (l.map Prod.fst).filter (· ≠ k)
  | [], _ => rfl
  | x :: xs, hn => by
    have hn' := List.nodup_cons.mp hn
    have ih := dropLastP_nodup k xs hn'.2
    by_cases h1 : (xs.any fun p => decide (p.1 = k)) = true
    · have hx : x.1 ≠ k := by
        obtain ⟨q, hq, e⟩ := List.any_eq_true.mp h1
        have e' : q.1 = k := by simpa using e
        intro hk
        exact hn'.1 (List.mem_map.mpr ⟨q, hq, by rw [e', hk]⟩)
      simp [dropLastP, h1, ih, hx]
    · have hall : ∀ q ∈ xs, q.1 ≠ k := by
        intro q hq e
        exact h1 (List.any_eq_true.mpr ⟨q, hq, by simpa using e⟩)
      have hf : (xs.map Prod.fst).filter (· ≠ k) = xs.map Prod.fst := by
        apply List.filter_eq_self.mpr
        intro a ha
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
        simpa using hall q hq
      have h1' : (xs.any fun p => decide (p.1 = k)) = false := Bool.eq_false_iff.mpr h1
      by_cases h2 : x.1 = k
      · have hd : dropLastP (fun p => decide (p.1 = k)) (x :: xs) = xs := by
          simp only [dropLastP, h1', Bool.false_eq_true, ite_false, h2, decide_true, ite_true]
        rw [hd, List.map_cons, List.filter_cons_of_neg (by simpa using h2), hf]
      · have hd : dropLastP (fun p => decide (p.1 = k)) (x :: xs) = x :: xs := by
          simp only [dropLastP, h1', Bool.false_eq_true, ite_false, h2, decide_false]
        rw [hd, List.map_cons, List.filter_cons_of_pos (by simpa using h2), hf]

theorem hit_rel (m : Nat) (c : CLru K V) (p : PyLru K V) (key : K) (r : V) (h : Rel m c p)
    (hl : c.links.lookup key = some r) :
    Rel m { c with links := dropLastP (fun q => decide (q.1 = key)) c.links ++ [(key, r)], hits := c.hits + 1 }
      { p with ring := dropLastP (ringIs key) p.ring ++ [some (key, r)], hits := p.hits + 1 } := by
  have hk : key ∈ c.links.map Prod.fst := (lookup_mem_iff _ _).mp (by simp [hl])
  have hd := dropLastP_nodup key c.links h.nodup
  have hring : dropLastP (ringIs key) (none :: c.links.map some) =
      none :: (dropLastP (fun q => decide (q.1 = key)) c.links).map some := by
    have e1 : dropLastP (ringIs key) (c.links.map some) =
        (dropLastP (fun q => ringIs key (some q)) c.links).map some := dropLastP_map _ _ _
    have e2 : (fun q : K × V => ringIs key (some q)) = fun q => decide (q.1 = key) := rfl
    rw [e2] at e1
    have hany : (c.links.map some).any (ringIs key) = true := by
      obtain ⟨q, hq, e⟩ := List.mem_map.mp hk
      exact List.any_eq_true.mpr ⟨some q, List.mem_map.mpr ⟨q, hq, rfl⟩, by simp [ringIs, e]⟩
    simp only [dropLastP, hany, ite_true, e1]
  have hperm : (((dropLastP (fun q => decide (q.1 = key)) c.links) ++ [(key, r)]).map Prod.fst).Perm
      (c.links.map Prod.fst) := by
    rw [List.map_append, hd]
    have h1 := List.perm_cons_erase hk
    rw [h.nodup.erase_eq_filter key] at h1
    have e3 : (fun x => x != key) = fun x => decide (x ≠ key) := by
      funext x
      by_cases hx : x = key <;> simp [hx]
    rw [e3] at h1
    exact (List.perm_append_singleton _ _).trans h1.symm
  have hlen : (dropLastP (fun q => decide (q.1 = key)) c.links ++ [(key, r)]).length =
      c.links.length := by
    have := hperm.length_eq
    simpa using this
  refine ⟨?_, h.cache, ?_, h.misses, ?_, h.broken, ?_, ?_, ?_⟩
  · simp only [h.ring, hring, List.map_append, List.map_cons, List.map_nil, List.cons_append]
  · simp [h.hits]
  · simp only [hlen]; exact h.full
  · simp only [hlen]; exact h.bound
  · exact hperm.nodup_iff.mpr h.nodup
  · exact h.perm.trans hperm.symm

theorem miss_rel (m : Nat) (c : CLru K V) (p : PyLru K V) (h : Rel m c p) :
    Rel m { c with misses := c.misses + 1 } { p with misses := p.misses + 1 } :=
  ⟨h.ring, h.cache, h.hits, by simp [h.misses], h.full, h.broken, h.bound, h.nodup, h.perm⟩

/-- A new key goes at the newest end of a cache that is not full. -/
theorem grow_rel (m : Nat) (c : CLru K V) (p : PyLru K V) (key : K) (r : V) (h : Rel m c p)
    (hk : key ∉ c.links.map Prod.fst) (hlt : c.links.length < m) :
    Rel m { c with links := c.links ++ [(key, r)], cache := c.cache ++ [key] }
      { p with ring := p.ring ++ [some (key, r)], cache := p.cache ++ [key],
               full := decide ((p.cache ++ [key]).length ≥ m) } := by
  have hlen : c.cache.length = c.links.length := by simpa using h.perm.length_eq
  refine ⟨?_, ?_, h.hits, h.misses, ?_, h.broken, ?_, ?_, ?_⟩
  · simp [h.ring]
  · simp [h.cache]
  · simp [h.cache, hlen]
  · simp; omega
  · exact nodup_snoc _ _ _ h.nodup hk
  · simp only [List.map_append, List.map_cons, List.map_nil]
    exact h.perm.append_right _

/-- The oldest link is reused for the new key. -/
theorem evict_rel (m : Nat) (c : CLru K V) (p : PyLru K V) (key : K) (r : V) (old : K × V)
    (rest : List (K × V)) (h : Rel m c p) (hl : c.links = old :: rest)
    (hk : key ∉ c.links.map Prod.fst) :
    Rel m { c with links := rest ++ [(key, r)], cache := c.cache.erase old.1 ++ [key] }
      { p with ring := none :: rest.map some ++ [some (key, r)],
               cache := p.cache.erase old.1 ++ [key] } := by
  have hn := h.nodup
  rw [hl] at hn
  have hn' := List.nodup_cons.mp hn
  have hkr : key ∉ rest.map Prod.fst := fun hx => hk (by rw [hl]; exact List.mem_cons_of_mem _ hx)
  have hmap : c.links.map Prod.fst = old.1 :: rest.map Prod.fst := by rw [hl]; rfl
  have hpe : (c.cache.erase old.1).Perm (rest.map Prod.fst) := by
    have := h.perm.erase old.1
    rw [hmap] at this
    simpa using this
  have hlen : (rest ++ [(key, r)]).length = c.links.length := by rw [hl]; simp
  refine ⟨?_, ?_, h.hits, h.misses, ?_, h.broken, ?_, ?_, ?_⟩
  · simp
  · simp [h.cache]
  · simp only [hlen]; exact h.full
  · simp only [hlen]; exact h.bound
  · exact nodup_snoc _ _ _ hn'.2 hkr
  · simp only [List.map_append, List.map_cons, List.map_nil]
    exact hpe.append_right _

local macro "finish " t:term : tactic =>
  `(tactic| first
    | exact ⟨rfl, $t⟩
    | exact ⟨trivial, $t⟩
    | (simp only; exact ⟨rfl, $t⟩)
    | (simp only; exact ⟨trivial, $t⟩))

/-- The twins step together. The theorem is by induction on the fuel because the user function may
call back into the cache, so a call and a run of the user function are proved together. -/
theorem sim (cfg : Cfg K V) (hm : 0 < cfg.maxsize) (hi : ∀ k ks, cfg.F.insert k ks = none)
    (he : ∀ k ks, cfg.F.evict k ks = none) : ∀ fuel,
    (∀ key c p, Rel cfg.maxsize c p →
      (callPy cfg fuel key p).1 = (callC cfg fuel key c).1 ∧
      Rel cfg.maxsize (callC cfg fuel key c).2 (callPy cfg fuel key p).2) ∧
    (∀ prog c p, Rel cfg.maxsize c p →
      (runPy cfg fuel prog p).1 = (runC cfg fuel prog c).1 ∧
      Rel cfg.maxsize (runC cfg fuel prog c).2 (runPy cfg fuel prog p).2)
  | 0 => by
    refine ⟨?_, ?_⟩
    · intro key c p h
      simp only [callPy, callC]
      finish h
    · intro prog c p h
      simp only [runPy, runC]
      finish h
  | fuel + 1 => by
    obtain ⟨ihc, ihr⟩ := sim cfg hm hi he fuel
    refine ⟨?_, ?_⟩
    · intro key c p h
      have hb := h.broken
      have hmem : key ∈ c.cache ↔ (c.links.lookup key).isSome = true := by
        rw [lookup_mem_iff]
        exact h.perm.mem_iff
      simp only [callPy, callC, hb, Bool.false_eq_true, ite_false, h.cache]
      cases hg : cfg.F.get key c.cache with
      | some e => finish h
      | none =>
        try simp only
        cases hl : c.links.lookup key with
        | some r =>
          have hin : key ∈ c.cache := hmem.mpr (by simp [hl])
          have hv : ringValue key p.ring = some r := by
            rw [h.ring, ringValue_links key c.links h.nodup, hl]
          simp only [hin, ite_true, hv]
          have g := hit_rel _ c p key r h hl
          simp only [h.cache, hb] at g
          finish g
        | none =>
          have hnin : key ∉ c.cache := by
            intro hx
            have := hmem.mp hx
            simp [hl] at this
          simp only [hnin, ite_false]
          have hrel : Rel cfg.maxsize { c with misses := c.misses + 1 }
              { ring := p.ring, cache := c.cache, hits := p.hits, misses := c.misses + 1,
                full := p.full, broken := false, stale := p.stale } :=
            ⟨h.ring, rfl, h.hits, rfl, h.full, rfl, h.bound, h.nodup, h.perm⟩
          obtain ⟨h1, h2⟩ := ihr (cfg.f key (c.misses + 1)) _ _ hrel
          simp only [h.misses]
          revert h1 h2
          generalize runPy cfg fuel (cfg.f key (c.misses + 1))
            { ring := p.ring, cache := c.cache, hits := p.hits, misses := c.misses + 1,
              full := p.full, broken := false, stale := p.stale } = rp
          generalize runC cfg fuel (cfg.f key (c.misses + 1)) { c with misses := c.misses + 1 } = rc
          obtain ⟨r1, s⟩ := rp
          obtain ⟨r2, t⟩ := rc
          intro h1 h2
          simp only at h1 h2
          subst h1
          cases r1 with
          | error e =>
            simp only
            finish h2
          | ok result =>
            simp only [h2.cache]
            cases hrc : cfg.F.recheck key t.cache with
            | some e => finish h2
            | none =>
              simp only
              have hmem2 : key ∈ t.cache ↔ (t.links.lookup key).isSome = true := by
                rw [lookup_mem_iff]
                exact h2.perm.mem_iff
              cases hl2 : t.links.lookup key with
              | some v =>
                have : key ∈ t.cache := hmem2.mpr (by simp [hl2])
                simp only [this, ite_true]
                finish h2
              | none =>
                have hk : key ∉ t.cache := by
                  intro hx
                  have := hmem2.mp hx
                  simp [hl2] at this
                have hkl : key ∉ t.links.map Prod.fst := fun hx =>
                  hk (h2.perm.mem_iff.mpr hx)
                have hlen : t.cache.length = t.links.length := by
                  simpa using h2.perm.length_eq
                simp only [hk, ite_false]
                by_cases hf : t.links.length ≥ cfg.maxsize
                · cases hlk : t.links with
                  | nil =>
                    rw [hlk] at hf
                    simp at hf
                    omega
                  | cons old rest =>
                    have hne : ¬ (t.cache.length < cfg.maxsize ∨ (old :: rest).isEmpty = true) := by
                      simp only [List.isEmpty_cons, Bool.false_eq_true, or_false]
                      omega
                    have hring : s.ring = none :: some old :: rest.map some := by
                      rw [h2.ring, hlk]
                      rfl
                    have hold : old.1 ∈ t.cache :=
                      h2.perm.mem_iff.mpr (by rw [hlk]; simp)
                    have hfull : s.full = true := by
                      rw [h2.full]
                      exact decide_eq_true hf
                    have g := evict_rel _ t s key result old rest h2 hlk hkl
                    simp only [h2.cache, hfull] at g
                    simp only [hfull, ite_true, hring, h2.cache, hold, not_true_eq_false,
                      ite_false, he, hi, if_neg hne]
                    finish g
                · have hlt : t.links.length < cfg.maxsize := by omega
                  have hne : t.cache.length < cfg.maxsize ∨ t.links.isEmpty = true :=
                    Or.inl (by omega)
                  have hfull : s.full = false := by
                    rw [h2.full]
                    exact decide_eq_false hf
                  have g := grow_rel _ t s key result h2 hkl hlt
                  simp only [h2.cache, hfull] at g
                  simp only [hfull, Bool.false_eq_true, ite_false, if_pos hne, hi, h2.cache]
                  finish g
    · intro prog c p h
      cases prog with
      | ret v => simp only [runPy, runC]; finish h
      | raise e => simp only [runPy, runC]; finish h
      | clear k =>
        simp only [runPy, runC]
        exact ihr k _ _ (rel_empty _ hm)
      | call k cont =>
        simp only [runPy, runC]
        obtain ⟨h1, h2⟩ := ihc k c p h
        revert h1 h2
        generalize callPy cfg fuel k p = rp
        generalize callC cfg fuel k c = rc
        obtain ⟨r1, s⟩ := rp
        obtain ⟨r2, t⟩ := rc
        intro h1 h2
        simp only at h1 h2
        subst h1
        exact ihr (cont r1) t s h2

/-- Twin agreement on one call of a bounded cache, for every re-entrant user function, every key and
every reachable pair of states. Failures of `__hash__` or `__eq__` in the two lookups are allowed; the
hypotheses `hi` and `he` exclude failures of the store and of the deletion, which are refuted below. -/
def LruTwinsNoStoreFaults : Prop :=
  ∀ (cfg : Cfg Nat Nat), 0 < cfg.maxsize → (∀ k ks, cfg.F.insert k ks = none) →
    (∀ k ks, cfg.F.evict k ks = none) → ∀ fuel key (c : CLru Nat Nat) (p : PyLru Nat Nat),
    Rel cfg.maxsize c p →
    (callPy cfg fuel key p).1 = (callC cfg fuel key c).1 ∧
      Rel cfg.maxsize (callC cfg fuel key c).2 (callPy cfg fuel key p).2

theorem lruTwinsNoStoreFaults_proven : LruTwinsNoStoreFaults :=
  fun cfg hm hi he fuel key c p h => (sim cfg hm hi he fuel).1 key c p h

/-- Drive a cache with a list of keys from an empty state, keeping the results. -/
def driveC (cfg : Cfg K V) (fuel : Nat) : List K → CLru K V → List (Py V) × CLru K V
  | [], s => ([], s)
  | k :: ks, s =>
    let (r, s) := callC cfg fuel k s
    let (rs, s) := driveC cfg fuel ks s
    (r :: rs, s)

def drivePy (cfg : Cfg K V) (fuel : Nat) : List K → PyLru K V → List (Py V) × PyLru K V
  | [], s => ([], s)
  | k :: ks, s =>
    let (r, s) := callPy cfg fuel k s
    let (rs, s) := drivePy cfg fuel ks s
    (r :: rs, s)

/-- The twins over a sequence of calls. -/
theorem drive_sim (cfg : Cfg K V) (hm : 0 < cfg.maxsize) (hi : ∀ k ks, cfg.F.insert k ks = none)
    (he : ∀ k ks, cfg.F.evict k ks = none) (fuel : Nat) : ∀ (keys : List K) (c : CLru K V) (p : PyLru K V),
    Rel cfg.maxsize c p →
    (drivePy cfg fuel keys p).1 = (driveC cfg fuel keys c).1 ∧
      Rel cfg.maxsize (driveC cfg fuel keys c).2 (drivePy cfg fuel keys p).2
  | [], _, _, h => ⟨rfl, h⟩
  | k :: ks, c, p, h => by
    obtain ⟨h1, h2⟩ := (sim cfg hm hi he fuel).1 k c p h
    simp only [drivePy, driveC]
    revert h1 h2
    generalize callPy cfg fuel k p = rp
    generalize callC cfg fuel k c = rc
    obtain ⟨r1, s⟩ := rp
    obtain ⟨r2, t⟩ := rc
    intro h1 h2
    simp only at h1 h2
    subst h1
    obtain ⟨h3, h4⟩ := drive_sim cfg hm hi he fuel ks t s h2
    simp only
    revert h3 h4
    generalize drivePy cfg fuel ks s = dp
    generalize driveC cfg fuel ks t = dc
    obtain ⟨a, b⟩ := dp
    obtain ⟨c', d⟩ := dc
    intro h3 h4
    simp only at h3 h4
    subst h3
    exact ⟨rfl, h4⟩

/-- From empty caches, the twins return the same results for every key sequence and report the same
`cache_info()`, while the store and the deletion of the dict succeed. So a failing `__eq__` in a lookup is
covered, and a failing store is refuted below. -/
def LruTwinsFromEmpty : Prop :=
  ∀ (cfg : Cfg Nat Nat), 0 < cfg.maxsize → (∀ k ks, cfg.F.insert k ks = none) →
    (∀ k ks, cfg.F.evict k ks = none) → ∀ (fuel : Nat) (keys : List Nat),
    (drivePy cfg fuel keys emptyPy).1 = (driveC cfg fuel keys emptyC).1 ∧
    infoPy cfg.maxsize (drivePy cfg fuel keys emptyPy).2 = infoC cfg.maxsize (driveC cfg fuel keys emptyC).2

theorem lruTwinsFromEmpty_proven : LruTwinsFromEmpty := by
  intro cfg hm hi he fuel keys
  obtain ⟨h1, h2⟩ := drive_sim cfg hm hi he fuel keys emptyC emptyPy (rel_empty _ hm)
  refine ⟨h1, ?_⟩
  simp only [infoPy, infoC, h2.cache, h2.hits, h2.misses]

/-- The cache never exceeds `maxsize` and holds each key once, under re-entrant user functions, a clear in the
middle of a call, and failing lookups: the invariant of the C wrapper, and of the Python one by `Rel`. -/
def LruBounded : Prop :=
  ∀ (cfg : Cfg Nat Nat), 0 < cfg.maxsize → (∀ k ks, cfg.F.insert k ks = none) →
    (∀ k ks, cfg.F.evict k ks = none) → ∀ (fuel : Nat) (keys : List Nat),
    (driveC cfg fuel keys emptyC).2.links.length ≤ cfg.maxsize ∧
    ((driveC cfg fuel keys emptyC).2.links.map Prod.fst).Nodup

theorem lruBounded_proven : LruBounded := by
  intro cfg hm hi he fuel keys
  have h2 := (drive_sim cfg hm hi he fuel keys emptyC emptyPy (rel_empty _ hm)).2
  exact ⟨h2.bound, h2.nodup⟩

/-- The re-check at Lib/functools.py:674-679 and Modules/_functoolsmodule.c:1457-1464: when the user function
stored the same key through a re-entrant call, the outer call returns its own result and leaves the cache as
it found it, so the inner value stays. Both twins, for every `maxsize`. -/
def LruRecheckKeepsInner : Prop :=
  ∀ (cfg : Cfg Nat Nat) (fuel key : Nat) (c : CLru Nat Nat) (result v : Nat) (s : CLru Nat Nat),
    c.links.lookup key = none → cfg.F.get key c.cache = none →
    runC cfg fuel (cfg.f key (c.misses + 1)) { c with misses := c.misses + 1 } = (.ok result, s) →
    cfg.F.recheck key s.cache = none → s.links.lookup key = some v →
    callC cfg (fuel + 1) key c = (.ok result, s)

theorem lruRecheckKeepsInner_proven : LruRecheckKeepsInner := by
  intro cfg fuel key c result v s h1 h2 h3 h4 h5
  simp only [callC, h2, h1, h3, h4, h5]

/-- The unbounded wrapper has no re-check, so there the outer result overwrites what a re-entrant call stored:
the difference between the two branches, Lib/functools.py:640-645 against :674-679. -/
def LruInfiniteOverwrites : Prop :=
  ∀ (f : Nat → Nat → Prog Nat Nat) (F : Faults Nat) (fuel key : Nat) (c s : CLru Nat Nat) (result : Nat),
    c.links.lookup key = none → F.get key c.cache = none →
    runInf f F fuel (f key (c.misses + 1)) { c with misses := c.misses + 1 } = (.ok result, s) →
    F.insert key s.cache = none →
    (callInf f F (fuel + 1) key c).1 = .ok result ∧
      (callInf f F (fuel + 1) key c).2.links.lookup key = some result

theorem setKey_lookup (d : List (K × V)) (k : K) (v : V) : (setKey d k v).lookup k = some v := by
  unfold setKey
  by_cases h : d.any (fun p => decide (p.1 = k)) = true
  · simp only [h, ite_true]
    induction d with
    | nil => simp at h
    | cons p ps ih =>
      by_cases e : p.1 = k
      · simp [e, List.lookup]
      · have e2 : (k == p.1) = false := by
          have : k ≠ p.1 := fun x => e x.symm
          simpa using this
        have h' : ps.any (fun p => decide (p.1 = k)) = true := by simpa [e] using h
        simp only [List.map_cons, e, ite_false, List.lookup, e2]
        exact ih h'
  · have h' : d.any (fun p => decide (p.1 = k)) = false := Bool.eq_false_iff.mpr h
    simp only [h', Bool.false_eq_true, ite_false]
    induction d with
    | nil => simp [List.lookup]
    | cons p ps ih =>
      have e : ¬ p.1 = k := by
        intro x
        simp [x] at h'
      have e2 : (k == p.1) = false := by
        have : k ≠ p.1 := fun x => e x.symm
        simpa using this
      simp only [List.cons_append, List.lookup, e2]
      have h2 : ps.any (fun p => decide (p.1 = k)) = false := by simpa [e] using h'
      exact ih (by simp [h2]) h2

theorem lruInfiniteOverwrites_proven : LruInfiniteOverwrites := by
  intro f F fuel key c s result h1 h2 h3 h4
  simp only [callInf, h2, h1, h3, h4]
  exact ⟨trivial, setKey_lookup _ _ _⟩

/-- A user function that raises leaves its key uncached in every mode: the failure goes up as it is, after
being counted as a miss. Docs: "If the user function raises, nothing is cached". -/
def LruFailureNotCached : Prop :=
  ∀ (cfg : Cfg Nat Nat) (fuel key : Nat) (e : PyExc) (c : CLru Nat Nat) (p : PyLru Nat Nat),
    (∀ n, cfg.f key n = .raise e) → cfg.F.get key c.cache = none → cfg.F.get key p.cache = none →
    c.links.lookup key = none → key ∉ p.cache → p.broken = false →
    callC cfg (fuel + 2) key c = (.error e, { c with misses := c.misses + 1 }) ∧
    callPy cfg (fuel + 2) key p = (.error e, { p with misses := p.misses + 1 }) ∧
    (callInf cfg.f cfg.F (fuel + 2) key c = (.error e, { c with misses := c.misses + 1 }))

theorem lruFailureNotCached_proven : LruFailureNotCached := by
  intro cfg fuel key e c p hf h1 h2 h3 h4 h5
  refine ⟨?_, ?_, ?_⟩
  · simp only [callC, h1, h3, hf, runC]
  · simp only [callPy, h5, Bool.false_eq_true, ite_false, h2, h4, hf, runPy]
  · simp only [callInf, h1, h3, hf, runInf]

/-- When the deletion of the oldest key fails, the C wrapper puts the link back where it was and the failure
goes up as if from the user function: `lru_cache_prepend_link`, Modules/_functoolsmodule.c:1531-1541. So a
failed eviction keeps every entry, in the same order. -/
def LruEvictFailureKeepsLinks : Prop :=
  ∀ (cfg : Cfg Nat Nat) (fuel key r : Nat) (e : PyExc) (c : CLru Nat Nat) (old : Nat × Nat)
    (rest : List (Nat × Nat)),
    c.links = old :: rest → (∀ n, cfg.f key n = .ret r) → cfg.F.get key c.cache = none →
    cfg.F.recheck key c.cache = none → c.links.lookup key = none → cfg.maxsize ≤ c.cache.length →
    cfg.F.evict old.1 c.cache = some e →
    (callC cfg (fuel + 2) key c).1 = .error e ∧ (callC cfg (fuel + 2) key c).2.links = old :: rest

theorem lruEvictFailureKeepsLinks_proven : LruEvictFailureKeepsLinks := by
  intro cfg fuel key r e c old rest hl hf hg hr hk hm he
  have hne : ¬ (c.cache.length < cfg.maxsize ∨ (c.links).isEmpty = true) := by
    rw [hl]
    simp only [List.isEmpty_cons, Bool.false_eq_true, or_false]
    omega
  have hne' : ¬ (c.cache.length < cfg.maxsize ∨ (old :: rest).isEmpty = true) := by
    rw [hl] at hne
    exact hne
  have hk' : (old :: rest).lookup key = none := hl ▸ hk
  simp only [callC, hg, hl, hk', hf, runC, hr, if_neg hne', he]
  exact ⟨trivial, trivial⟩

/-- What a pure user function computes. -/
def Memo (g : K → V) (l : List (K × V)) : Prop := ∀ p ∈ l, p.2 = g p.1

theorem lookup_mem (l : List (K × V)) (k : K) (v : V) (h : l.lookup k = some v) : (k, v) ∈ l := by
  induction l with
  | nil => simp at h
  | cons p ps ih =>
    by_cases e : k = p.1
    · have e' : (k == p.1) = true := by simpa using e
      simp only [List.lookup, e', Option.some.injEq] at h
      subst h
      exact List.mem_cons.mpr (Or.inl (by rw [e]))
    · have e' : (k == p.1) = false := by simpa using e
      simp only [List.lookup, e'] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem dropLastP_sub {α : Type} (p : α → Bool) : ∀ l : List α, ∀ x ∈ dropLastP p l, x ∈ l
  | [], _, h => by cases h
  | y :: ys, x, h => by
    simp only [dropLastP] at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (dropLastP_sub p ys x h)
    · split at h
      · exact List.mem_cons_of_mem _ h
      · exact h

theorem memo_snoc (g : K → V) (l : List (K × V)) (k : K) (h : Memo g l) : Memo g (l ++ [(k, g k)]) := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact h q hq
  · simp only [List.mem_singleton] at hq
    subst hq
    rfl

/-- A cached pure function returns what the function returns, at every step, from any state that holds only
its values. The eviction and hit paths included: `cache` and `lru_cache` are transparent. This is the
whole point of the decorator. -/
def LruTransparent : Prop :=
  ∀ (g : Nat → Nat) (cfg : Cfg Nat Nat), (∀ k n, cfg.f k n = .ret (g k)) → cfg.F = noFaults Nat →
    ∀ (fuel key : Nat) (c : CLru Nat Nat), Memo g c.links →
    (callC cfg (fuel + 2) key c).1 = .ok (g key) ∧ Memo g (callC cfg (fuel + 2) key c).2.links ∧
    (callInf cfg.f cfg.F (fuel + 2) key c).1 = .ok (g key) ∧
    (callNone cfg.f (fuel + 2) key c.misses).1 = .ok (g key)

theorem lruTransparent_proven : LruTransparent := by
  intro g cfg hf hF fuel key c hm
  have hg : cfg.F.get = fun _ _ => none := by rw [hF]; rfl
  have hr : cfg.F.recheck = fun _ _ => none := by rw [hF]; rfl
  have hi : cfg.F.insert = fun _ _ => none := by rw [hF]; rfl
  have he : cfg.F.evict = fun _ _ => none := by rw [hF]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases hl : c.links.lookup key with
    | some r =>
      have := hm _ (lookup_mem _ _ _ hl)
      simp only [callC, hg, hl]
      rw [show r = g key from this]
    | none =>
      simp only [callC, hg, hl, hf, runC, hr, hi]
      split
      · rfl
      · next hc =>
        cases hk : c.links with
        | nil => exact absurd (Or.inr (by simp [hk])) hc
        | cons old rest =>
          simp only [he]
          split <;> rfl
  · cases hl : c.links.lookup key with
    | some r =>
      have e : r = g key := hm _ (lookup_mem _ _ _ hl)
      subst e
      simp only [callC, hg, hl]
      exact memo_snoc g _ key (fun q hq => hm q (dropLastP_sub _ _ q hq))
    | none =>
      simp only [callC, hg, hl, hf, runC, hr, hi]
      split
      · exact memo_snoc g _ key hm
      · cases hc : c.links with
        | nil =>
          intro q hq
          simp at hq
        | cons old rest =>
          simp only [he]
          have hm' : Memo g (old :: rest) := hc ▸ hm
          split
          · exact fun q hq => hm' q (List.mem_cons_of_mem _ hq)
          · exact memo_snoc g _ key (fun q hq => hm' q (List.mem_cons_of_mem _ hq))
  · cases hl : c.links.lookup key with
    | some r =>
      have e : r = g key := hm _ (lookup_mem _ _ _ hl)
      subst e
      simp only [callInf, hg, hl]
    | none => simp only [callInf, hg, hl, hf, runInf, hi]
  · simp only [callNone, hf, runNone]

end

/-- `maxsize=2`, identity user function, and a store of key 2 that raises once while the cache holds only
key 1: a key whose `__eq__` raises against a colliding key. -/
def staleCfg : Cfg Nat Nat :=
  ⟨2, fun k _ => .ret k,
    { noFaults Nat with
      insert := fun k ks => if k = 2 ∧ ks = [1] then some (.valueError "eq") else none }, 0⟩

/-- `maxsize=2`, a user function that gives `k + 1`, and a `del` of key 2 that raises: a key colliding with key 1, whose
`__eq__` raises while the entry is looked for. `None` is `0`, which the function never gives. -/
def delCfg : Cfg Nat Nat :=
  ⟨2, fun k _ => .ret (k + 1), { noFaults Nat with evict := fun k _ => if k = 2 then some (.valueError "eq") else none }, 0⟩

/-- All the Python wrapper returns is something the user function returned. False: after `del cache[oldkey]` raises at
Lib/functools.py:699, the dict still has `oldkey`, and its link is the new root, whose result is `None`, so the next call with
that key is a hit that returns `None`. C puts the link back, and keeps the value. -/
def LruResultsFromFunction : Prop :=
  ∀ (keys : List Nat) (v : Nat), Except.ok v ∈ (drivePy delCfg 8 keys emptyPy).1 → ∃ k, v = k + 1

theorem lruResultsFromFunction_refuted : ¬LruResultsFromFunction := by
  intro h
  obtain ⟨k, hk⟩ := h [1, 2, 1, 3, 2] 0 (by decide +kernel)
  omega

/-- The same sequence in C keeps to the results of the function: the failed `del` is on record as an exception, and the value
of the key is still there. -/
def LruDeleteFailureC : Prop :=
  (driveC delCfg 8 [1, 2, 1, 3, 2] emptyC).1 =
    [.ok 2, .ok 3, .ok 2, .error (.valueError "eq"), .ok 3]

theorem lruDeleteFailureC_proven : LruDeleteFailureC := by
  unfold LruDeleteFailureC
  decide +kernel

/-- A failed store must not break later calls with unrelated keys. The sequence is 1, then 2 (the store
raises), then 2 again, 3, 4. C recovers. Python's ring keeps a link for the failed key, the wrapper fills
up and evicts that link, and `del cache[oldkey]` raises `KeyError` for a key that was never cached.
Status: refuted, a twin difference. -/
def LruFailedStoreRecovers : Prop :=
  ∀ (keys : List Nat), (drivePy staleCfg 8 keys emptyPy).1 = (driveC staleCfg 8 keys emptyC).1

theorem lruFailedStoreRecovers_refuted : ¬LruFailedStoreRecovers := by
  intro h
  have := h [1, 2, 3, 4, 5, 6]
  revert this
  decide +kernel

/-- `lru_cache` selects the same wrapper in both twins for every `maxsize` up to `sys.maxsize`, for
`None`, and for the bare-decorator form, a negative `maxsize` being `0`, and rejects the same bad
arguments, when the user function is callable. Twin property, narrowed to the `Py_ssize_t` range: see
`LruMaxsizeTwinsAlways`. A user function that is not callable is `LruAcceptsSameFunctions`. -/
def LruModeTwins : Prop :=
  ∀ a : MaxsizeArg, (∀ n, a = .int n → n ≤ ssizeMax) →
    (do wrapperCMode true (← lruCacheArg a)) = (do wrapperPyMode true (← lruCacheArg a))

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
        simp only [wrapperCMode, Bool.not_true, Bool.false_eq_true, ite_false, h2, h3]
        cases n with
        | ofNat k =>
          cases k with
          | zero => exact absurd rfl h1
          | succ k => rfl
        | negSucc k => omega

/-- `lru_cache(maxsize=n)` selects the same wrapper in both twins for every `int`. False: the C
wrapper converts `maxsize` to `Py_ssize_t` and raises `OverflowError` above `sys.maxsize`. -/
def LruMaxsizeTwinsAlways : Prop :=
  ∀ n : Int, wrapperCMode true (some n) = wrapperPyMode true (some n)

theorem lruMaxsizeTwinsAlways_refuted : ¬LruMaxsizeTwinsAlways := by
  intro h
  have := h (2 ^ 63)
  simp [wrapperCMode, wrapperPyMode, ssizeMax, ssizeMin] at this

/-- Both wrappers refuse a user function that is not callable, with one message and for every `maxsize`, before they
look at `maxsize`: Lib/functools.py:605-606 and Modules/_functoolsmodule.c:1637-1641. -/
def LruAcceptsSameFunctions : Prop :=
  ∀ m : Option Int,
    wrapperCMode false m = .error (.typeError "the first argument must be callable") ∧
    wrapperPyMode false m = .error (.typeError "the first argument must be callable")

theorem lruAcceptsSameFunctions_proven : LruAcceptsSameFunctions := by
  intro m
  exact ⟨rfl, rfl⟩

end PyLean.CoreLibs.Functools
