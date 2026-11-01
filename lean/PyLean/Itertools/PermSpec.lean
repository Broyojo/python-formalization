import PyLean.Itertools.CombSpec

/-!
What `permutations` enumerates. The `cycles` machine is read recursively: the
part of `indices` and `cycles` from position `i` on is a smaller machine
(`sufStep`) that either yields or "carries" to position `i - 1`. A full run of
the suffix machine visits the elements of its suffix in order and restores it,
which is what makes the rotation in the `cycles[i] == 0` branch correct.
-/

namespace PyLean.Itertools

open PyLean

variable {α : Type} [Inhabited α]

/-! ## The suffix machine -/

inductive SufRes where
  | yield (t : List Nat) (cs : List Int)
  | carry (t : List Nat) (cs : List Int)

def SufRes.indices : SufRes → List Nat
  | .yield t _ => t
  | .carry t _ => t

def SufRes.cycles : SufRes → List Int
  | .yield _ cs => cs
  | .carry _ cs => cs

/-- One `next()` on the suffix `t` of `indices` and the suffix `cs` of `cycles`. -/
def sufStep : List Nat → List Int → SufRes
  | t, [] => .carry t []
  | [], _ :: _ => .carry [] []
  | x :: t, c :: cs =>
    match sufStep t cs with
    | .yield t' cs' => .yield (x :: t') (c :: cs')
    | .carry t' cs' =>
      if c - 1 = 0 then .carry (t' ++ [x]) (((t'.length + 1 : Nat) : Int) :: cs')
      else
        let p := t'.length + 1 - (c - 1).toNat
        .yield (ix t' (p - 1) :: t'.set (p - 1) x) ((c - 1) :: cs')

theorem sufStep_length : ∀ (t : List Nat) (cs : List Int), (sufStep t cs).indices.length = t.length
  | t, [] => by cases t <;> rfl
  | [], _ :: _ => rfl
  | x :: t, c :: cs => by
    have ih := sufStep_length t cs
    simp only [sufStep]
    cases h : sufStep t cs with
    | yield t' cs' =>
      rw [h] at ih
      simpa [SufRes.indices] using ih
    | carry t' cs' =>
      rw [h] at ih
      simp only [SufRes.indices] at ih
      simp only
      split <;> simp [SufRes.indices, ih]

/-- `cycles` bounds: entry `i` lies in `[1, n - i]`. -/
def CycOk : Nat → List Int → Prop
  | _, [] => True
  | m, c :: cs => 1 ≤ c ∧ c ≤ m ∧ CycOk (m - 1) cs

theorem sufStep_cycles_length : ∀ (t : List Nat) (cs : List Int), CycOk t.length cs →
    (sufStep t cs).cycles.length = cs.length
  | [], [], _ => rfl
  | _ :: _, [], _ => rfl
  | [], c :: cs, h => by simp only [CycOk, List.length_nil] at h; omega
  | x :: t, c :: cs, h => by
    have ih := sufStep_cycles_length t cs (by simpa [CycOk] using h.2.2)
    simp only [sufStep]
    cases hs : sufStep t cs with
    | yield t' cs' =>
      rw [hs] at ih
      simpa [SufRes.cycles] using ih
    | carry t' cs' =>
      rw [hs] at ih
      simp only [SufRes.cycles] at ih
      simp only
      split <;> simp [SufRes.cycles, ih]

/-- The full loop's result, given the suffix machine's. -/
def sufMatch (n : Nat) (pre : List Nat) (cpre : List Int) : SufRes → (List Nat × List Int) ⊕ Unit
  | .yield t cs => .inl (pre ++ t, cpre ++ cs)
  | .carry t cs => docPermLoop n pre.length (pre ++ t) (cpre ++ cs)

theorem getD_mid {α : Type} (l r : List α) (a d : α) : (l ++ a :: r).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem set_mid {α : Type} (l r : List α) (a b : α) : (l ++ a :: r).set l.length b = l ++ b :: r := by
  simp

/-- The doc's `for i in reversed(range(r))` loop on `pre ++ suf` is the suffix
machine, then the rest of the loop on the prefix. -/
theorem loop_suf (n : Nat) : ∀ (cs : List Int) (pre suf : List Nat) (cpre : List Int),
    cpre.length = pre.length → pre.length + suf.length = n → CycOk suf.length cs →
    docPermLoop n (pre.length + cs.length) (pre ++ suf) (cpre ++ cs) =
      sufMatch n pre cpre (sufStep suf cs)
  | [], pre, suf, cpre, _, _, _ => by cases suf <;> simp [sufStep, sufMatch]
  | c :: cs, _, [], _, _, _, h => by simp only [CycOk, List.length_nil] at h; omega
  | c :: cs, pre, x :: t, cpre, hc, hn, hok => by
    obtain ⟨hc1, hc2, hok'⟩ := hok
    simp only [List.length_cons, Nat.add_sub_cancel] at hok' hc2
    have ih := loop_suf n cs (pre ++ [x]) t (cpre ++ [c]) (by simp [hc]) (by simp at hn ⊢; omega) hok'
    have hi : pre.length + (cs.length + 1) = (pre ++ [x]).length + cs.length := by simp; omega
    have e1 : pre ++ x :: t = (pre ++ [x]) ++ t := by simp
    have e2 : cpre ++ c :: cs = (cpre ++ [c]) ++ cs := by simp
    simp only [List.length_cons]
    rw [hi, e1, e2, ih]
    simp only [sufStep]
    have hlen := sufStep_length t cs
    cases hs : sufStep t cs with
    | yield t' cs' => simp [sufMatch]
    | carry t' cs' =>
      rw [hs] at hlen
      simp only [SufRes.indices] at hlen
      have h1 : (pre ++ [x]).length = pre.length + 1 := by simp
      simp only [sufMatch]
      rw [h1, List.append_assoc, List.append_assoc]
      simp only [List.singleton_append, docPermLoop]
      rw [← hc]
      have g1 : (cpre ++ c :: cs').getD cpre.length 0 = c := getD_mid _ _ _ _
      have s1 : ∀ w, (cpre ++ c :: cs').set cpre.length w = cpre ++ w :: cs' := fun w => set_mid _ _ _ _
      have g2 : (cpre ++ (c - 1) :: cs').getD cpre.length 0 = c - 1 := getD_mid _ _ _ _
      simp only [g1, s1, g2]
      rw [hc]
      by_cases hz : c - 1 = 0
      · simp only [hz, ↓reduceIte, sufMatch]
        have t1 : (pre ++ x :: t').take pre.length = pre := by simp
        have t2 : (pre ++ x :: t').drop (pre.length + 1) = t' := by simp
        have t3 : ((pre ++ x :: t').drop pre.length).take 1 = [x] := by simp
        have hset : (cpre ++ (0 : Int) :: cs').set pre.length ((n : Int) - (pre.length : Int)) =
            cpre ++ ((t'.length + 1 : Nat) : Int) :: cs' := by
          rw [← hc, set_mid, hc]
          simp at hn
          congr 2
          omega
        rw [t1, t2, t3, hset]
      · simp only [hz, ↓reduceIte, sufMatch]
        simp only [List.length_cons] at hn
        obtain ⟨q, hq⟩ : ∃ q, t'.length + 1 - (c - 1).toNat - 1 = q := ⟨_, rfl⟩
        have hnj : n - (c - 1).toNat = pre.length + (q + 1) := by omega
        have a1 : ix (pre ++ x :: t') pre.length = x := by simp [ix, List.getD_eq_getElem?_getD]
        have a2 : ix (pre ++ x :: t') (pre.length + (q + 1)) = ix t' q := by
          simp [ix, List.getD_eq_getElem?_getD, List.getElem?_append_right]
        have a3 : (pre ++ ix t' q :: t').set (pre.length + (q + 1)) x = pre ++ ix t' q :: t'.set q x := by
          rw [List.set_append, if_neg (by omega)]
          simp
        rw [hq, hnj, a1, a2, set_mid, a3]

/-! ## The enumeration -/

/-- Position tuples, by first choosing an element of `S`, in `S`'s order. -/
def pe : List Nat → Nat → List (List Nat)
  | _, 0 => [[]]
  | S, r + 1 => (List.range S.length).flatMap (fun k => (pe (S.eraseIdx k) r).map (ix S k :: ·))

theorem flatMap_len_const {β : Type} (l : List Nat) (f : Nat → List β) (c : Nat)
    (h : ∀ k ∈ l, (f k).length = c) : (l.flatMap f).length = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [h a (by simp), ih (fun k hk => h k (by simp [hk])), Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem pe_length : ∀ (r : Nat) (S : List Nat), (pe S r).length = perm S.length r
  | 0, S => by cases S <;> rfl
  | r + 1, S => by
    simp only [pe]
    rw [flatMap_len_const _ _ (perm (S.length - 1) r)]
    · cases S with
      | nil => simp [perm]
      | cons a T => simp [perm]
    · intro k hk
      rw [List.mem_range] at hk
      simp only [List.length_map]
      rw [pe_length r, List.length_eraseIdx_of_lt hk]

theorem perm_gt : ∀ n r, n < r → perm n r = 0
  | 0, r + 1, _ => rfl
  | n + 1, r + 1, h => by simp [perm, perm_gt n r (by omega)]

theorem ix_lt_of_sorted (S : List Nat) (h : S.Pairwise (· < ·)) (k k' : Nat) (hk : k < k')
    (hk' : k' < S.length) : ix S k < ix S k' := by
  rw [ix_eq S k (by omega), ix_eq S k' hk']
  exact (List.pairwise_iff_getElem.1 h) k k' (by omega) hk' hk

theorem ix_mem (S : List Nat) (k : Nat) (hk : k < S.length) : ix S k ∈ S := by
  rw [ix_eq S k hk]; exact List.getElem_mem hk

theorem ix_not_mem_erase : ∀ (S : List Nat) (k : Nat), S.Pairwise (· < ·) → k < S.length →
    ix S k ∉ S.eraseIdx k
  | [], _, _, h => by simp at h
  | a :: T, 0, h, _ => by
    simp only [ix, List.getD_cons_zero, List.eraseIdx_cons_zero]
    intro hm
    have := (List.pairwise_cons.1 h).1 a hm
    omega
  | a :: T, k + 1, h, hk => by
    have hkT : k < T.length := by simpa using hk
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 h
    have ih := ix_not_mem_erase T k h2 hkT
    have hx : ix (a :: T) (k + 1) = ix T k := by simp [ix]
    rw [hx]
    simp only [List.eraseIdx_cons_succ, List.mem_cons, not_or]
    refine ⟨?_, ih⟩
    have := h1 _ (ix_mem T k hkT)
    omega

theorem pe_valid : ∀ (r : Nat) (S x : List Nat), S.Pairwise (· < ·) → x ∈ pe S r →
    x.length = r ∧ x.Nodup ∧ ∀ v ∈ x, v ∈ S
  | 0, S, x, _, hx => by simp [pe] at hx; subst hx; simp
  | r + 1, S, x, hS, hx => by
    simp only [pe, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨k, hk, y, hy, rfl⟩ := hx
    obtain ⟨h1, h2, h3⟩ := pe_valid r _ y (hS.sublist (List.eraseIdx_sublist _ _)) hy
    refine ⟨by simp [h1], ?_, ?_⟩
    · refine List.nodup_cons.2 ⟨?_, h2⟩
      exact fun hm => ix_not_mem_erase S k hS hk (h3 _ hm)
    · intro v hv
      simp only [List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact ix_mem S k hk
      · exact List.mem_of_mem_eraseIdx (h3 v hv)

theorem pe_sorted : ∀ (r : Nat) (S : List Nat), S.Pairwise (· < ·) → (pe S r).Pairwise LexLt
  | 0, S, _ => by simp [pe]
  | r + 1, S, h => by
    simp only [pe]
    rw [List.pairwise_flatMap]
    refine ⟨fun k _ => pairwise_lex_cons _ _ (pe_sorted r _ (h.sublist (List.eraseIdx_sublist _ _))), ?_⟩
    refine List.pairwise_lt_range.imp_of_mem ?_
    intro k k' _ hk' hlt a ha b hb
    simp only [List.mem_map] at ha hb
    obtain ⟨y, _, rfl⟩ := ha
    obtain ⟨y', _, rfl⟩ := hb
    exact Or.inl (ix_lt_of_sorted S h k k' hlt (by simpa using hk'))

/-! ## A full run of the suffix machine -/

/-- Initial `cycles`: `n, n-1, ..., n-r+1`. -/
def cyc0 (m r : Nat) : List Int := (List.range r).map (fun (i : Nat) => (m : Int) - (i : Int))

theorem cyc0_succ (m r : Nat) : cyc0 (m + 1) (r + 1) = ((m + 1 : Nat) : Int) :: cyc0 m r := by
  simp only [cyc0, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  simp
  intro a _
  omega

theorem cyc0_length (m r : Nat) : (cyc0 m r).length = r := by simp [cyc0]

theorem cyc0_ok : ∀ (r m : Nat), r ≤ m → CycOk m (cyc0 m r)
  | 0, _, _ => by simp [cyc0, CycOk]
  | r + 1, 0, h => by omega
  | r + 1, m + 1, h => by
    rw [cyc0_succ]
    exact ⟨by omega, by omega, by simpa using cyc0_ok r m (by omega)⟩

/-- From `(t, cs)` the suffix machine yields the `r`-prefixes `L`, then carries
out with `(tf, cf)`. -/
inductive CarryRun (m r : Nat) : List Nat → List Int → List (List Nat) → List Nat → List Int → Prop
  | stop {t cs tf cf} : t.length = m → CycOk m cs → sufStep t cs = .carry tf cf →
      CarryRun m r t cs [t.take r] tf cf
  | step {t cs t1 cs1 L tf cf} : t.length = m → CycOk m cs → sufStep t cs = .yield t1 cs1 →
      CarryRun m r t1 cs1 L tf cf → CarryRun m r t cs (t.take r :: L) tf cf

theorem CarryRun.head {m r t cs L tf cf} (h : CarryRun m r t cs L tf cf) :
    ∃ rest, L = t.take r :: rest := by
  cases h with
  | stop _ _ _ => exact ⟨[], rfl⟩
  | step _ _ _ _ => exact ⟨_, rfl⟩

theorem lift_carry (x : Nat) (c : Int) (m r : Nat) (hc1 : 1 ≤ c) (hc2 : c ≤ (m + 1 : Nat))
    (hz : c - 1 = 0) {t cs L tf cf} (h : CarryRun m r t cs L tf cf) :
    CarryRun (m + 1) (r + 1) (x :: t) (c :: cs) (L.map (x :: ·)) (tf ++ [x])
      (((tf.length + 1 : Nat) : Int) :: cf) := by
  induction h with
  | @stop t cs tf cf hl hok hs =>
    exact CarryRun.stop (by simp [hl]) ⟨hc1, hc2, by simpa using hok⟩ (by simp [sufStep, hs, hz])
  | @step t cs t1 cs1 L tf cf hl hok hs _ ih =>
    exact CarryRun.step (by simp [hl]) ⟨hc1, hc2, by simpa using hok⟩ (by simp [sufStep, hs]) ih

theorem lift_yield (x : Nat) (c c1 : Int) (m r q : Nat) (hc1 : 1 ≤ c) (hc2 : c ≤ (m + 1 : Nat))
    (hz : c - 1 ≠ 0) (hc : c - 1 = c1) {t cs L tf cf} {R Sf Cf}
    (hq : tf.length + 1 - (c - 1).toNat - 1 = q) (h : CarryRun m r t cs L tf cf)
    (hR : CarryRun (m + 1) (r + 1) (ix tf q :: tf.set q x) (c1 :: cf) R Sf Cf) :
    CarryRun (m + 1) (r + 1) (x :: t) (c :: cs) (L.map (x :: ·) ++ R) Sf Cf := by
  subst hc
  induction h with
  | @stop t cs tf cf hl hok hs =>
    refine CarryRun.step (by simp [hl]) ⟨hc1, hc2, by simpa using hok⟩ ?_ hR
    simp only [sufStep, hs, hz, ↓reduceIte, hq]
  | @step t cs t1 cs1 L tf cf hl hok hs _ ih =>
    exact CarryRun.step (by simp [hl]) ⟨hc1, hc2, by simpa using hok⟩ (by simp [sufStep, hs]) (ih hq hR)

theorem erase_ix : ∀ (S : List Nat) (k : Nat), k + 1 < S.length → ix (S.eraseIdx k) k = ix S (k + 1)
  | a :: b :: T, 0, _ => by simp [ix]
  | a :: T, k + 1, h => by
    have := erase_ix T k (by simpa using h)
    simpa [ix] using this
  | [], _, h => by simp at h
  | [_], 0, h => by simp at h

theorem erase_set : ∀ (S : List Nat) (k : Nat), k + 1 < S.length →
    (S.eraseIdx k).set k (ix S k) = S.eraseIdx (k + 1)
  | a :: b :: T, 0, _ => by simp [ix]
  | a :: T, k + 1, h => by
    have := erase_set T k (by simpa using h)
    simpa [ix] using this
  | [], _, h => by simp at h
  | [_], 0, h => by simp at h

theorem erase_last : ∀ (S : List Nat) (k : Nat), k + 1 = S.length →
    S.eraseIdx k ++ [ix S k] = S
  | [a], 0, _ => by simp [ix]
  | a :: b :: T, k + 1, h => by
    have := erase_last (b :: T) k (by simpa using h)
    simpa [ix] using this
  | [], _, h => by simp at h
  | a :: b :: T, 0, h => by simp at h

theorem perm_rows (S : List Nat) (m r : Nat) (hS : S.length = m + 1)
    (hI : ∀ E : List Nat, E.length = m → CarryRun m r E (cyc0 m r) (pe E r) E (cyc0 m r)) :
    ∀ d k, k + d = m →
      CarryRun (m + 1) (r + 1) (ix S k :: S.eraseIdx k) (((d + 1 : Nat) : Int) :: cyc0 m r)
        ((List.range' k (d + 1)).flatMap (fun k => (pe (S.eraseIdx k) r).map (ix S k :: ·))) S
        (((m + 1 : Nat) : Int) :: cyc0 m r)
  | 0, k, h => by
    have hE : (S.eraseIdx k).length = m := by rw [List.length_eraseIdx_of_lt (by omega)]; omega
    have := lift_carry (ix S k) ((0 + 1 : Nat) : Int) m (r) (by omega) (by omega) (by omega)
      (hI _ hE)
    rw [erase_last S k (by omega), hE] at this
    simpa [List.range'_succ] using this
  | d + 1, k, h => by
    have hE : (S.eraseIdx k).length = m := by rw [List.length_eraseIdx_of_lt (by omega)]; omega
    have hR := perm_rows S m r hS hI d (k + 1) (by omega)
    rw [← erase_ix S k (by omega), ← erase_set S k (by omega)] at hR
    have := lift_yield (ix S k) ((d + 1 + 1 : Nat) : Int) ((d + 1 : Nat) : Int) m r k (by omega)
      (by omega) (by omega) (by omega) (by rw [hE]; omega) (hI _ hE) hR
    rw [List.range'_succ, List.flatMap_cons]
    exact this

theorem perm_run : ∀ (r : Nat) (S : List Nat), r ≤ S.length →
    CarryRun S.length r S (cyc0 S.length r) (pe S r) S (cyc0 S.length r)
  | 0, S, _ => by
    have hs : sufStep S [] = .carry S [] := by cases S <;> rfl
    exact CarryRun.stop rfl (by simp [cyc0, CycOk]) (by simpa [cyc0] using hs)
  | r + 1, S, h => by
    obtain ⟨m, hm⟩ : ∃ m, S.length = m + 1 := ⟨S.length - 1, by omega⟩
    have hI : ∀ E : List Nat, E.length = m → CarryRun m r E (cyc0 m r) (pe E r) E (cyc0 m r) := by
      intro E hE
      have := perm_run r E (by omega)
      rwa [hE] at this
    have hrows := perm_rows S m r hm hI m 0 (by omega)
    have hhead : ix S 0 :: S.eraseIdx 0 = S := by
      cases S with
      | nil => simp at hm
      | cons a T => simp [ix]
    rw [hhead] at hrows
    rw [hm, cyc0_succ]
    have hr : List.range S.length = List.range' 0 (m + 1) := by rw [hm, List.range_eq_range']
    simp only [pe, hr]
    exact hrows

/-! ## The full iterator -/

theorem pySliceTo_nat (l : List Nat) (r : Nat) : pySliceTo l (r : Int) = l.take r := by
  simp [pySliceTo]

/-- From a started state, the doc's `while n:` loop gives the tuples of the run. -/
theorem outer_run (pool : List α) (r : Nat) (hn : pool.length ≠ 0) {t cs L tf cf}
    (h : CarryRun pool.length r t cs L tf cf) (hcs : cs.length = r) : ∀ fuel, L.length ≤ fuel →
    docPermOuter pool (r : Int) fuel t cs = Run.ok (L.tail.map (pick pool)) := by
  induction h with
  | @stop t cs tf cf hl hok hs =>
    intro fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hloop := loop_suf pool.length cs [] t [] rfl (by simp [hl]) (by rwa [hl])
    simp only [List.length_nil, Nat.zero_add, List.nil_append, hs, sufMatch, hcs] at hloop
    simp only [docPermOuter, hn, ↓reduceIte, Int.toNat_natCast, hloop, docPermLoop]
    rfl
  | @step t cs t1 cs1 L tf cf hl hok hs hr ih =>
    intro fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hloop := loop_suf pool.length cs [] t [] rfl (by simp [hl]) (by rwa [hl])
    simp only [List.length_nil, Nat.zero_add, List.nil_append, hs, sufMatch, hcs] at hloop
    have hcl : cs1.length = r := by
      have := sufStep_cycles_length t cs (by rwa [hl])
      rw [hs] at this
      simp only [SufRes.cycles] at this
      omega
    obtain ⟨rest, rfl⟩ := hr.head
    simp only [docPermOuter, hn, ↓reduceIte, Int.toNat_natCast, hloop, pySliceTo_nat]
    rw [ih hcl f (by simp at hf ⊢; omega)]
    rfl

/-- `docPermutationsF` for `0 <= r <= n` and enough fuel. -/
theorem docPerm_spec (pool : List α) (robj : Option Int) (r : Nat)
    (hrobj : robj.getD pool.length = (r : Int)) (hr : r ≤ pool.length) (fuel : Nat)
    (hf : perm pool.length r ≤ fuel) :
    docPermutationsF fuel (.iter pool none) robj = Run.ok ((pe (List.range pool.length) r).map (pick pool)) := by
  have hrun := perm_run r (List.range pool.length) (by simpa using hr)
  simp only [List.length_range] at hrun
  have hlen : (pe (List.range pool.length) r).length = perm pool.length r := by
    rw [pe_length, List.length_range]
  obtain ⟨rest, hL⟩ := hrun.head
  have hcyc : (List.range r).map (fun (i : Nat) => (pool.length : Int) - (i : Int)) = cyc0 pool.length r := rfl
  simp only [docPermutationsF, tupleOf, hrobj, show ¬ ((r : Int) > pool.length) by omega, ↓reduceIte,
    Int.toNat_natCast, hcyc, pySliceTo_nat]
  rw [hL]
  by_cases hn : pool.length = 0
  · have hr0 : r = 0 := by omega
    subst hr0
    have hpe : pe (List.range pool.length) 0 = [[]] := rfl
    rw [hL] at hpe
    have hrest : rest = [] := by simpa using hpe
    subst hrest
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by
      rw [hn] at hf
      simp only [perm] at hf
      omega⟩
    simp only [docPermOuter, hn, ↓reduceIte]
    rfl
  · have ho := outer_run pool r hn hrun (cyc0_length _ _) fuel (by omega)
    rw [hL] at ho
    simp only [List.tail_cons] at ho
    rw [ho]
    rfl

/-- `cPermutationsF` runs the doc code in lockstep. -/
theorem cPerm_eq (pool : List α) (robj : Option Int) (r : Nat)
    (hrobj : robj.getD pool.length = (r : Int)) (hp : tupleNewOk pool.length = true)
    (hm : memNewOk r = true) (ht : tupleNewOk r = true) (fuel : Nat) :
    cPermutationsF (fuel + 1) (.iter pool none) robj = docPermutationsF fuel (.iter pool none) robj := by
  have hpn : memNewOk (pool.length : Int) = true := memNewOk_of_tuple hp (by omega)
  have hle := memNewOk_le hm
  have hmin : ssizeMin ≤ (r : Int) := by rw [ssizeMin_eq]; omega
  have hnew : cPermutationsNew (.iter pool none) robj =
      .ok { pool := pool, indices := List.range pool.length, r := r,
            cycles := cyc0 pool.length r, started := false,
            stopped := decide ((r : Int) > pool.length) } := by
    cases robj with
    | none =>
      simp only [Option.getD_none] at hrobj
      have hrl : r = pool.length := by omega
      subst hrl
      simp only [cPermutationsNew, tupleOf, bind, Except.bind, show ¬ ((pool.length : Int) < 0) by omega,
        ↓reduceIte, hpn, Bool.not_true, Bool.or_false, Bool.false_eq_true, pure, Except.pure,
        Int.toNat_natCast]
      rfl
    | some v =>
      simp only [Option.getD_some] at hrobj
      subst hrobj
      simp only [cPermutationsNew, tupleOf, asSsize_ok hmin hle, bind, Except.bind,
        show ¬ ((r : Int) < 0) by omega, ↓reduceIte, hpn, hm, Bool.not_true, Bool.or_false,
        Bool.false_eq_true, pure, Except.pure, Int.toNat_natCast]
      rfl
  simp only [cPermutationsF, hnew]
  rw [drain_succ]
  by_cases hrn : (r : Int) > pool.length
  · simp [hrn, cPermutationsNext, docPermutationsF, tupleOf, hrobj, Run.ok]
  · simp only [hrn, decide_false, cPermutationsNext, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      ht, Bool.not_true]
    have := permOuter_eq pool r (by omega) fuel (List.range pool.length) (cyc0 pool.length r)
      (by simp) (cyc0_length _ _)
    rw [this]
    have hcyc : (List.range r).map (fun (i : Nat) => (pool.length : Int) - (i : Int)) = cyc0 pool.length r := rfl
    simp only [docPermutationsF, tupleOf, hrobj, hrn, ↓reduceIte, Int.toNat_natCast, hcyc, pySliceTo_nat, Run.cons]

/-- For `r` (or `r=None`, meaning `n`) that can be allocated and enough fuel,
`permutations(pool, r)` yields the tuples at exactly the positions in a list
`L` of `math.perm(n, r)` tuples (`n!/(n-r)!`, zero when `r > n`) of `r` distinct
positions `< n`, strictly increasing in lexicographic order, so no repeats. -/
def PermutationsSpec : Prop :=
  ∀ (α : Type) [Inhabited α] (pool : List α) (robj : Option Int) (fuel : Nat), tupleNewOk pool.length = true →
    0 ≤ robj.getD pool.length → memNewOk (robj.getD pool.length) = true →
    tupleNewOk (robj.getD pool.length) = true →
    perm pool.length (robj.getD pool.length).toNat < fuel →
    ∃ L : List (List Nat), cPermutationsF fuel (.iter pool none) robj = Run.ok (L.map (pick pool)) ∧
      L.length = perm pool.length (robj.getD pool.length).toNat ∧ L.Pairwise LexLt ∧
      ∀ x ∈ L, x.length = (robj.getD pool.length).toNat ∧ x.Nodup ∧ ∀ v ∈ x, v < pool.length

theorem permutationsSpec_proven : PermutationsSpec := by
  intro α _ pool robj fuel hp h0 hm ht hf
  obtain ⟨r, hr⟩ : ∃ r : Nat, robj.getD pool.length = (r : Int) :=
    ⟨(robj.getD pool.length).toNat, by omega⟩
  rw [hr] at hm ht hf ⊢
  simp only [Int.toNat_natCast] at hf ⊢
  have hsorted : (List.range pool.length).Pairwise (· < ·) := List.pairwise_lt_range
  refine ⟨pe (List.range pool.length) r, ?_, by rw [pe_length, List.length_range],
    pe_sorted r _ hsorted, ?_⟩
  · obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [cPerm_eq pool robj r hr hp hm ht f]
    by_cases hn : r ≤ pool.length
    · exact docPerm_spec pool robj r hr hn f (by omega)
    · have hzero : pe (List.range pool.length) r = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [pe_length, List.length_range]
        exact perm_gt _ _ (by omega)
      rw [hzero]
      simp [docPermutationsF, tupleOf, hr, show (r : Int) > pool.length by omega, Run.ok]
  · intro x hx
    obtain ⟨h1, h2, h3⟩ := pe_valid r _ x hsorted hx
    exact ⟨h1, h2, fun v hv => by simpa using h3 v hv⟩

end PyLean.Itertools
