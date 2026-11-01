import PyLean.CoreLibs.Rand.ExactProps
import PyLean.Accel.BisectProps

/-!
`sample(population, k, counts=...)`, Lib/random.py:422-433, against the docstring:
"`sample(['red', 'blue'], counts=[4, 2], k=5)` is equivalent to
`sample(['red', 'red', 'red', 'red', 'blue', 'blue'], k=5)`".
-/

namespace PyLean.CoreLibs.Rand

open PyLean PyLean.RangeSlice RM Flt

variable {σ α : Type}

/-- The population a `counts` argument stands for. -/
def expandCounts : List α → List Int → List α
  | x :: xs, c :: cs => List.replicate c.toNat x ++ expandCounts xs cs
  | _, _ => []

/-- For non-negative counts, `sample(p, k, counts=c)` and `sample(expanded, k)` are the
same computation: the same result or exception and the same generator state, for
every `k`. The hypotheses are the documented ones: one count per element, each
non-negative, and the two lists fit in `Py_ssize_t` (a real expanded list does). -/
def SampleCountsEquivalent : Prop :=
  ∀ (σ α : Type) (below : Nat → RM σ Nat) (fuel : Nat) (p : List α) (cs : List Int) (k : Int) (s : σ),
    BelowValid below → cs.length = p.length → (∀ c ∈ cs, 0 ≤ c) →
    (p.length : Int) ≤ ssizeMax → ((expandCounts p cs).length : Int) ≤ ssizeMax →
    sample below fuel (listSeq p) k (some (.seq (cs.map some))) s =
      sample below fuel (listSeq (expandCounts p cs)) k none s

/-! ### Prefix sums -/

/-- The prefix sums of `cs` after `acc`. -/
def scan : Int → List Int → List Int
  | _, [] => []
  | acc, x :: xs => (acc + x) :: scan (acc + x) xs

def tot : List Int → Int
  | [] => 0
  | c :: cs => c + tot cs

theorem go_eq : ∀ (xs : List Int) (acc : Int),
    accumulateCounts.go (some acc) (xs.map some) = (scan acc xs).map some
  | [], _ => rfl
  | x :: xs, acc => by
    simp only [List.map_cons, accumulateCounts.go, scan]
    rw [go_eq xs (acc + x)]

theorem accumulate_eq (cs : List Int) : accumulateCounts (cs.map some) = (scan 0 cs).map some := by
  cases cs with
  | nil => rfl
  | cons c t =>
    simp only [List.map_cons, accumulateCounts, scan, Int.zero_add]
    rw [go_eq]

theorem scan_length : ∀ (cs : List Int) (o : Int), (scan o cs).length = cs.length
  | [], _ => rfl
  | c :: cs, o => by simp [scan, scan_length cs]

theorem scan_last : ∀ (cs : List Int) (o : Int), cs ≠ [] → (scan o cs).getLast? = some (o + tot cs)
  | [], _, h => absurd rfl h
  | [c], o, _ => by simp [scan, tot]
  | c :: d :: r, o, _ => by
    have ih := scan_last (d :: r) (o + c) (by simp)
    have e : scan o (c :: d :: r) = (o + c) :: (scan (o + c + d) r |>.cons (o + c + d)) := rfl
    have e' : scan (o + c) (d :: r) = (o + c + d) :: scan (o + c + d) r := rfl
    rw [e, List.getLast?_cons_cons, ← e', ih]
    simp only [tot, Option.some.injEq]
    omega

theorem scan_ge : ∀ (cs : List Int) (o : Int), (∀ c ∈ cs, 0 ≤ c) → ∀ x ∈ scan o cs, o ≤ x
  | [], _, _, _, h => by simp [scan] at h
  | c :: cs, o, hc, x, h => by
    simp only [scan, List.mem_cons] at h
    have h0 := hc c (by simp)
    rcases h with rfl | h
    · omega
    · have := scan_ge cs (o + c) (fun d hd => hc d (by simp [hd])) x h
      omega

theorem scan_sorted : ∀ (cs : List Int) (o : Int), (∀ c ∈ cs, 0 ≤ c) →
    (scan o cs).Pairwise (· ≤ ·)
  | [], _, _ => List.Pairwise.nil
  | c :: cs, o, hc => by
    simp only [scan]
    refine List.Pairwise.cons ?_ (scan_sorted cs (o + c) (fun d hd => hc d (by simp [hd])))
    exact scan_ge cs (o + c) (fun d hd => hc d (by simp [hd]))

theorem tot_nonneg : ∀ cs : List Int, (∀ c ∈ cs, 0 ≤ c) → 0 ≤ tot cs
  | [], _ => by simp [tot]
  | c :: cs, h => by
    have := tot_nonneg cs (fun d hd => h d (by simp [hd]))
    have := h c (by simp)
    simp only [tot]
    omega

theorem expand_length : ∀ (p : List α) (cs : List Int), cs.length = p.length → (∀ c ∈ cs, 0 ≤ c) →
    ((expandCounts p cs).length : Int) = tot cs
  | [], [], _, _ => by simp [expandCounts, tot]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: xs, c :: cs, h, hc => by
    have ih := expand_length xs cs (by simpa using h) (fun d hd => hc d (by simp [hd]))
    have h0 := hc c (by simp)
    simp only [expandCounts, List.length_append, List.length_replicate, tot]
    omega

theorem filterMap_some (l : List Int) : (l.map some).filterMap id = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simpa using ih

/-! ### `population[bisect(cum_counts, s)]` -/

theorem pick_spec : ∀ (p : List α) (cs : List Int) (o s : Int) (ip : Nat),
    cs.length = p.length → (∀ c ∈ cs, 0 ≤ c) → cs ≠ [] → o ≤ s → s < o + tot cs →
    ip ≤ (scan o cs).dropLast.length →
    (∀ k, k < ip → (scan o cs).dropLast.getD k 0 ≤ s) →
    (∀ k, ip ≤ k → k < (scan o cs).dropLast.length → s < (scan o cs).dropLast.getD k 0) →
    p[ip]? = (expandCounts p cs)[(s - o).toNat]?
  | [], _, _, _, _, h, _, hne, _, _, _, _, _ => by
    cases ‹List Int› with
    | nil => exact absurd rfl hne
    | cons _ _ => simp at h
  | _ :: _, [], _, _, _, _, _, hne, _, _, _, _, _ => absurd rfl hne
  | x :: xs, [c], o, s, ip, h, hc, _, h1, h2, h3, _, _ => by
    have hx : xs = [] := by
      simp only [List.length_cons, List.length_nil] at h
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hx
    have hip : ip = 0 := by simpa [scan] using h3
    subst hip
    simp only [tot] at h2
    have h0 := hc c (by simp)
    have hlt : (s - o).toNat < c.toNat := by omega
    simp only [expandCounts, List.append_nil, List.getElem?_cons_zero]
    rw [List.getElem?_replicate]
    simp [hlt]
  | x :: xs, c :: d :: r, o, s, ip, h, hc, _, h1, h2, h3, h4, h5 => by
    have hc0 := hc c (by simp)
    have hdrop : (scan o (c :: d :: r)).dropLast = (o + c) :: (scan (o + c) (d :: r)).dropLast := rfl
    rw [hdrop] at h3 h4 h5
    have hrep : (List.replicate c.toNat x).length = c.toNat := by simp
    cases ip with
    | zero =>
      have := h5 0 (Nat.le_refl _) (by simp)
      simp only [List.getD_cons_zero] at this
      have hlt : (s - o).toNat < c.toNat := by omega
      simp only [expandCounts, List.getElem?_cons_zero]
      rw [List.getElem?_append_left (by omega), List.getElem?_replicate]
      simp [hlt]
    | succ i =>
      have hge := h4 0 (by omega)
      simp only [List.getD_cons_zero] at hge
      have hrest : xs.length = (d :: r).length := by
        simp only [List.length_cons] at h ⊢
        omega
      have ih := pick_spec xs (d :: r) (o + c) s i hrest.symm (fun e he => hc e (by simp [he])) (by simp)
        hge (by simp only [tot] at h2 ⊢; omega) (by simpa using h3)
        (fun k hk => by simpa [List.getD_cons_succ] using h4 (k + 1) (by omega))
        (fun k h6 h7 => by simpa [List.getD_cons_succ] using h5 (k + 1) (by omega) (by simpa using h7))
      simp only [List.getElem?_cons_succ]
      rw [ih]
      simp only [expandCounts]
      rw [List.getElem?_append_right (by omega), hrep]
      congr 1
      omega

/-! ### The two runs -/

/-- The result of a run, its list mapped by `f`. -/
def mapR (f : Nat → α) (r : Py (List Nat) × σ) : Py (List α) × σ :=
  match r with
  | (.ok l, t) => (.ok (l.map f), t)
  | (.error e, t) => (.error e, t)

theorem listGet_map (f : Nat → α) (l : List Nat) (j : Nat) :
    listGet (l.map f) j = match listGet l j with
      | .ok x => .ok (f x)
      | .error e => .error e := by
  simp only [listGet, List.getElem?_map]
  cases l[j]? <;> rfl

theorem poolLoop_map (below : Nat → RM σ Nat) (n : Nat) (f : Nat → α) :
    ∀ (c i : Nat) (pool : List Nat) (s : σ),
      poolLoop below n c i (pool.map f) s = mapR f (poolLoop below n c i pool s)
  | 0, _, _, _ => rfl
  | c + 1, i, pool, s => by
    simp only [poolLoop, RM.bind_apply, RM.lift_apply, listGet_map]
    cases hb : below (n - i) s with
    | mk r t =>
      cases r with
      | error e => rfl
      | ok j =>
        simp only
        cases hx : listGet pool j with
        | error e => rfl
        | ok x =>
          simp only
          cases hv : listGet pool (n - i - 1) with
          | error e => rfl
          | ok v =>
            simp only
            have hset : (pool.map f).set j (f v) = (pool.set j v).map f := by
              rw [List.map_set]
            rw [hset, poolLoop_map below n f c (i + 1) (pool.set j v) t]
            cases poolLoop below n c (i + 1) (pool.set j v) t with
            | mk r2 t2 =>
              cases r2 <;> rfl

theorem setLoop_map (below : Nat → RM σ Nat) (hv : BelowValid below) (T fuel : Nat) (hT : 0 < T)
    (e : List α) (f : Nat → α) (hf : ∀ j, j < T → listGet e j = .ok (f j)) :
    ∀ (c : Nat) (sel : List Nat) (s : σ),
      setLoop below (listSeq e) T fuel c sel s = mapR f (setLoop below (rangeSeq T) T fuel c sel s)
  | 0, _, _ => rfl
  | c + 1, sel, s => by
    simp only [setLoop, RM.bind_apply, RM.lift_apply]
    cases hb : below T s with
    | mk r t =>
      cases r with
      | error err => rfl
      | ok j =>
        have hj : j < T := hv T hT s j t hb
        simp only
        cases hp : pickLoop below T sel fuel j t with
        | mk r2 t2 =>
          cases r2 with
          | error err => rfl
          | ok j' =>
            have hj' : j' < T := (pickLoop_spec below hv T hT sel fuel j hj t j' t2 hp).1
            have h1 : (listSeq e).getItem j' = .ok (f j') := hf j' hj'
            have h2 : (rangeSeq T).getItem j' = .ok j' := by
              simp [rangeSeq, hj']
            simp only [h1, h2]
            rw [setLoop_map below hv T fuel hT e f hf c (j' :: sel) t2]
            cases setLoop below (rangeSeq T) T fuel c (j' :: sel) t2 with
            | mk r3 t3 =>
              cases r3 <;> rfl

theorem sampleCore_map (below : Nat → RM σ Nat) (hv : BelowValid below) (fuel T : Nat) (k : Int)
    (e : List α) (f : Nat → α) (he : e.length = T) (hf : ∀ j, j < T → listGet e j = .ok (f j))
    (s : σ) :
    sampleCore below fuel (listSeq e) T k s = mapR f (sampleCore below fuel (rangeSeq T) T k s) := by
  unfold sampleCore
  by_cases hk : ¬(0 ≤ k ∧ k ≤ (T : Int))
  · simp only [if_pos hk]
    rfl
  · simp only [if_neg hk]
    by_cases hp : T ≤ setsize k.toNat
    · simp only [if_pos hp]
      have hmap : (listSeq e).toList () = ((rangeSeq T).toList ()).map f := by
        apply List.ext_getElem?
        intro j
        show e[j]? = ((List.range T).map f)[j]?
        rw [List.getElem?_map]
        by_cases hj : j < T
        · have hg := hf j hj
          obtain ⟨hl, hx⟩ := listGet_ok hg
          have hr : (List.range T)[j]? = some j := by simp [hj]
          rw [hr, List.getElem?_eq_getElem hl, hx]
          rfl
        · have h1 : e[j]? = none := List.getElem?_eq_none (by omega)
          have h2 : (List.range T)[j]? = none := List.getElem?_eq_none (by simpa using (by omega))
          rw [h1, h2]
          rfl
      rw [hmap]
      exact poolLoop_map below T f _ 0 _ s
    · simp only [if_neg hp]
      have hT : 0 < T := by
        have : 21 ≤ setsize k.toNat := by simp only [setsize]; omega
        omega
      exact setLoop_map below hv T fuel hT e f hf _ [] s

theorem map_some_inj : ∀ a b : List Nat, a.map some = b.map some → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    simp only [List.map_cons, List.cons.injEq, Option.some.injEq] at h
    rw [h.1, map_some_inj xs ys h.2]

/-- Everything a run on `range(T)` selects is below `T`. -/
theorem sampleCore_range_lt (below : Nat → RM σ Nat) (hv : BelowValid below) (fuel T : Nat) (k : Int) :
    Post (sampleCore below fuel (rangeSeq T) T k) (fun l => ∀ j ∈ l, j < T) := by
  unfold sampleCore
  split
  · exact Post.raise
  simp only
  have hmapr : (List.range T).map some = (List.range T).map some := rfl
  split
  · refine Post.mono (poolLoop_spec below hv T some k.toNat 0 (List.range T) (List.range T)
      (by omega) (by simp) (by simp) rfl) ?_
    rintro l ⟨_, pos, rest, hperm, _, hm⟩
    intro j hj
    have hpos : pos = l := map_some_inj _ _ hm
    subst hpos
    have : j ∈ pos ++ rest := List.mem_append_left _ hj
    have := hperm.mem_iff.mp this
    simp only [Nat.sub_zero] at this
    have h2 := List.mem_of_mem_take this
    simpa using h2
  · rename_i hk hset
    have hn0 : 0 < T := by
      have : 21 ≤ setsize k.toNat := by simp only [setsize]; omega
      omega
    refine Post.mono (setLoop_spec below hv (rangeSeq T) T fuel hn0 some ?_ k.toNat []) ?_
    · intro j x hx
      simp only [rangeSeq] at hx
      split at hx
      · cases hx
        rfl
      · cases hx
    · rintro l ⟨_, pos, _, _, hall, hm⟩
      intro j hj
      have hpos : pos = l := map_some_inj _ _ hm
      subst hpos
      exact (hall j hj).1

theorem mapSelections_ok (p : List α) (D : List Int) (f : Nat → α) (T : Nat)
    (h : ∀ s, s < T → ∃ i : Int, bisectCounts D s = .ok i ∧ listGet p i.toNat = .ok (f s)) :
    ∀ l : List Nat, (∀ j ∈ l, j < T) → mapSelections (listSeq p) D l = .ok (l.map f)
  | [], _ => rfl
  | s :: ss, hl => by
    obtain ⟨i, h1, h2⟩ := h s (hl s (by simp))
    have ih := mapSelections_ok p D f T h ss (fun j hj => hl j (by simp [hj]))
    have h3 : (listSeq p).getItem i.toNat = .ok (f s) := h2
    simp only [mapSelections, bind, Except.bind, h1, h3, ih, pure, Except.pure]
    rfl

theorem rangeSeq_len (T : Nat) (hT : (T : Int) ≤ ssizeMax) : (rangeSeq T).len = .ok T := by
  have hc : computeRangeLength 0 T 1 = T := by
    rw [computeRangeLength_eq 0 T 1 (by decide), rrLen_one]
    omega
  simp only [rangeSeq, rangeLength, range1, makeRangeObject, hc]
  rw [if_pos hT]
  simp [bind, Except.bind, pure, Except.pure]

/-- `sample` with non-negative counts, unfolded up to the run on `range(total)`. -/
theorem sample_counts_unfold (below : Nat → RM σ Nat) (fuel : Nat) (p : List α) (cs : List Int) (k : Int)
    (hlen : cs.length = p.length) (hnn : ∀ c ∈ cs, 0 ≤ c) :
    sample below fuel (listSeq p) k (some (.seq (cs.map some))) =
      (sampleRange below fuel (tot cs).toNat k >>= fun sel =>
        RM.lift (mapSelections (listSeq p) (scan 0 cs).dropLast sel)) := by
  have hcum := accumulate_eq cs
  have hL : (accumulateCounts (cs.map some)).length = p.length := by
    rw [hcum, List.length_map, scan_length, hlen]
  have hlast : (accumulateCounts (cs.map some)).getLast?.getD (some 0) = some (tot cs) := by
    rw [hcum, List.getLast?_map]
    cases cs with
    | nil => rfl
    | cons c t =>
      rw [scan_last (c :: t) 0 (by simp)]
      simp
  have hdrop : (accumulateCounts (cs.map some)).dropLast.filterMap id = (scan 0 cs).dropLast := by
    have hd : ∀ l : List Int, (l.map some).dropLast = l.dropLast.map some := by
      intro l
      apply List.ext_getElem?
      intro i
      simp only [List.getElem?_map, List.getElem?_dropLast, List.length_map]
      split <;> simp
    rw [hcum, hd, filterMap_some]
  have htot := tot_nonneg cs hnn
  funext s
  have hseq : (listSeq p).isSequence = true := rfl
  have hlenSeq : (listSeq p).len = .ok p.length := rfl
  simp only [sample, hseq, hlenSeq, Bool.not_true, Bool.false_eq_true, if_false, RM.bind_apply,
    RM.lift_apply, hL, hlast, hdrop]
  rw [if_neg (by simp), if_neg (by omega)]
  rfl

theorem sampleCountsEquivalent_proven : SampleCountsEquivalent := by
  intro σ α below fuel p cs k s hv hlen hnn hp hT
  have hTint := expand_length p cs hlen hnn
  have htot := tot_nonneg cs hnn
  rw [sample_counts_unfold below fuel p cs k hlen hnn]
  generalize he : expandCounts p cs = e at hTint hT ⊢
  have hto : (tot cs).toNat = e.length := by omega
  rw [hto]
  have hrun : sampleRange below fuel e.length k =
      sampleCore below fuel (rangeSeq e.length) e.length k := by
    funext t
    simp only [sampleRange, RM.bind_apply, RM.lift_apply, rangeSeq_len e.length hT]
  have hrhs : sample below fuel (listSeq e) k none =
      sampleCore below fuel (listSeq e) e.length k := rfl
  rw [hrun, hrhs]
  cases hc : e with
  | nil =>
    subst hc
    simp only [List.length_nil, RM.bind_apply, sampleCore]
    by_cases hk : ¬(0 ≤ k ∧ k ≤ ((0 : Nat) : Int))
    · simp only [if_pos hk]
      rfl
    · have hk0 : k = 0 := by omega
      subst hk0
      rfl
  | cons d rest =>
    rw [← hc]
    have hne : 0 < e.length := by rw [hc]; simp
    let f : Nat → α := fun j => e.getD j d
    have hf : ∀ j, j < e.length → listGet e j = .ok (f j) := by
      intro j hj
      simp [listGet, f, hj, List.getD]
    rw [sampleCore_map below hv fuel e.length k e f rfl hf s, RM.bind_apply]
    cases hrunR : sampleCore below fuel (rangeSeq e.length) e.length k s with
    | mk r t =>
      cases r with
      | error err => rfl
      | ok l =>
        have hlt := sampleCore_range_lt below hv fuel e.length k s l t hrunR
        have hsel : ∀ x, x < e.length →
            ∃ i : Int, bisectCounts (scan 0 cs).dropLast x = .ok i ∧ listGet p i.toNat = .ok (f x) := by
          intro x hx
          have hDlen : ((scan 0 cs).dropLast.length : Int) ≤ ssizeMax := by
            simp only [List.length_dropLast, scan_length]
            omega
          have hsort : PyLean.Accel.SortedBy none (scan 0 cs).dropLast :=
            (scan_sorted cs 0 hnn).sublist (List.dropLast_sublist _)
          obtain ⟨ip, _, h2, h3, h4, h5, h6⟩ := PyLean.Accel.bisectRightPartition_proven
            (scan 0 cs).dropLast (x : Int) 0 none none hDlen hsort (by omega) (by simp) (by simp)
          refine ⟨ip, h2, ?_⟩
          have hcsne : cs ≠ [] := by
            intro h0
            subst h0
            have h00 : tot ([] : List Int) = 0 := rfl
            rw [h00] at hTint
            omega
          have hip : (ip.toNat : Int) = ip := by omega
          have hpick := pick_spec p cs 0 (x : Int) ip.toNat hlen hnn hcsne (by omega)
            (by rw [Int.zero_add]; omega) (by simp only [Option.getD_none] at h4; omega)
            (fun k hk => h5 k (by omega) (by omega))
            (fun k h7 h8 => h6 k (by omega) (by simpa using h8))
          have hidx : ((x : Int) - 0).toNat = x := by omega
          have hgetE : e[x]? = some (f x) := by
            simp [f, hx, List.getD]
          rw [hidx, he, hgetE] at hpick
          simp [listGet, hpick]
        have hm := mapSelections_ok p _ f e.length hsel l hlt
        simp only [RM.lift_apply, hm]
        rfl

end PyLean.CoreLibs.Rand
