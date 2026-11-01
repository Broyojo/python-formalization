import PyLean.Itertools.CombSpec

/-!
`product`: the C odometer visits exactly the cartesian product of the pools in
lexicographic order, which is also what the doc's list comprehension builds.
-/

namespace PyLean.Itertools

open PyLean

theorem snoc_induction {α : Type} {P : List α → Prop} (h0 : P [])
    (hs : ∀ (l : List α) (a : α), P l → P (l ++ [a])) (l : List α) : P l := by
  have : ∀ m : List α, P m.reverse := fun m => by
    induction m with
    | nil => simpa using h0
    | cons a t ih => simpa using hs _ a ih
  simpa using this l.reverse

/-- The tuple of pool items at the given positions. -/
def vals (pools : List (List Int)) (idx : List Nat) : List Int :=
  List.zipWith (fun p i => at! p i) pools idx

/-- One step of the C odometer. -/
def prodStep (pools : List (List Int)) (idx : List Nat) : Option (List Nat) :=
  cProductAdvance pools pools.length idx

def pxStep (acc : List (List Nat)) (p : List Int) : List (List Nat) :=
  acc.flatMap (fun x => (List.range p.length).map (fun y => x ++ [y]))

/-- All position tuples, in the order of nested `for` loops. -/
def pxs (pools : List (List Int)) : List (List Nat) := pools.foldl pxStep [[]]

theorem pxs_snoc (ps : List (List Int)) (p : List Int) : pxs (ps ++ [p]) = pxStep (pxs ps) p := by
  simp [pxs, List.foldl_append]

/-- The number of tuples: the product of the pool sizes. -/
def prodLen (pools : List (List Int)) : Nat := (pools.map List.length).foldr (· * ·) 1

theorem prodLen_snoc (ps : List (List Int)) (p : List Int) :
    prodLen (ps ++ [p]) = prodLen ps * p.length := by
  induction ps with
  | nil => simp [prodLen]
  | cons q ps ih =>
    simp only [prodLen, List.cons_append, List.map_cons, List.foldr_cons] at ih ⊢
    rw [ih, Nat.mul_assoc]

theorem pxStep_length (acc : List (List Nat)) (p : List Int) :
    (pxStep acc p).length = acc.length * p.length := by
  induction acc with
  | nil => simp [pxStep]
  | cons x acc ih =>
    simp only [pxStep, List.flatMap_cons, List.length_append, List.length_map, List.length_range,
      List.length_cons] at ih ⊢
    rw [ih, Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem pxs_length (pools : List (List Int)) : (pxs pools).length = prodLen pools := by
  induction pools using snoc_induction with
  | h0 => rfl
  | hs ps p ih => rw [pxs_snoc, pxStep_length, ih, prodLen_snoc]

/-- A position tuple of the right length, each position inside its pool. -/
def Below (pools : List (List Int)) (x : List Nat) : Prop :=
  x.length = pools.length ∧ ∀ i, i < x.length → ix x i < (pools.getD i []).length

theorem pxs_below (pools : List (List Int)) : ∀ x ∈ pxs pools, Below pools x := by
  induction pools using snoc_induction with
  | h0 =>
    intro x hx
    simp only [pxs, List.foldl_nil, List.mem_singleton] at hx
    subst hx
    simp [Below]
  | hs ps p ih =>
    intro x hx
    rw [pxs_snoc] at hx
    simp only [pxStep, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨a, ha, y, hy, rfl⟩ := hx
    obtain ⟨h1, h2⟩ := ih a ha
    refine ⟨by simp [h1], ?_⟩
    intro i hi
    simp only [List.length_append, List.length_cons, List.length_nil] at hi
    by_cases hia : i < a.length
    · have h3 := h2 i hia
      have e1 : ix (a ++ [y]) i = ix a i := by
        simp [ix, List.getD_eq_getElem?_getD, List.getElem?_append_left hia]
      have e2 : (ps ++ [p]).getD i [] = ps.getD i [] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show i < ps.length by omega)]
      rw [e1, e2]; exact h3
    · obtain rfl : i = a.length := by omega
      have e1 : ix (a ++ [y]) a.length = y := by simp [ix, List.getD_eq_getElem?_getD]
      have e2 : (ps ++ [p]).getD a.length [] = p := by
        rw [h1]; simp [List.getD_eq_getElem?_getD]
      rw [e1, e2]; exact hy

/-! ## Lexicographic order -/

theorem lexLt_append : ∀ (x x' a b : List Nat), LexLt x x' → LexLt (x ++ a) (x' ++ b)
  | u :: x, v :: x', a, b, h => by
    simp only [LexLt, List.cons_append] at h ⊢
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, lexLt_append x x' a b h2⟩
  | [], _, _, _, h => by simp [LexLt] at h
  | _ :: _, [], _, _, h => by simp [LexLt] at h

theorem lexLt_snoc : ∀ (x : List Nat) (y y' : Nat), y < y' → LexLt (x ++ [y]) (x ++ [y'])
  | [], y, y', h => by simp [LexLt, h]
  | a :: x, y, y', h => by
    show LexLt (a :: (x ++ [y])) (a :: (x ++ [y']))
    exact Or.inr ⟨rfl, lexLt_snoc x y y' h⟩

theorem pxStep_sorted (acc : List (List Nat)) (p : List Int) (h : acc.Pairwise LexLt) :
    (pxStep acc p).Pairwise LexLt := by
  induction acc with
  | nil => simp [pxStep]
  | cons x acc ih =>
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 h
    simp only [pxStep, List.flatMap_cons] at ih ⊢
    refine List.pairwise_append.2 ⟨?_, ih h2, ?_⟩
    · rw [List.pairwise_map]
      exact (List.pairwise_lt_range).imp (fun hab => lexLt_snoc x _ _ hab)
    · intro a ha b hb
      simp only [List.mem_map, List.mem_flatMap] at ha hb
      obtain ⟨y, _, rfl⟩ := ha
      obtain ⟨x', hx', y', _, rfl⟩ := hb
      exact lexLt_append _ _ _ _ (h1 x' hx')

theorem pxs_sorted (pools : List (List Int)) : (pxs pools).Pairwise LexLt := by
  induction pools using snoc_induction with
  | h0 => simp [pxs]
  | hs ps p ih => rw [pxs_snoc]; exact pxStep_sorted _ _ ih

/-! ## The odometer -/

theorem adv_length (pools : List (List Int)) : ∀ (k : Nat) (idx idx' : List Nat),
    cProductAdvance pools k idx = some idx' → idx'.length = idx.length
  | 0, _, _, h => by simp [cProductAdvance] at h
  | k + 1, idx, idx', h => by
    simp only [cProductAdvance] at h
    split at h
    · have := adv_length pools k _ _ h
      simpa using this
    · simp at h; subst h; simp

theorem adv_snoc (ps : List (List Int)) (p : List Int) (z : Nat) : ∀ (j : Nat) (x : List Nat),
    j ≤ ps.length → x.length = ps.length →
    cProductAdvance (ps ++ [p]) j (x ++ [z]) = (cProductAdvance ps j x).map (· ++ [z])
  | 0, _, _, _ => rfl
  | j + 1, x, hj, hx => by
    have hg : (ps ++ [p]).getD j [] = ps.getD j [] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show j < ps.length by omega)]
    have hi : ix (x ++ [z]) j = ix x j := by
      simp [ix, List.getD_eq_getElem?_getD, List.getElem?_append_left (show j < x.length by omega)]
    have hs : ∀ w, (x ++ [z]).set j w = x.set j w ++ [z] := fun w => by
      rw [List.set_append, if_pos (by omega)]
    simp only [cProductAdvance, hg, hi, hs]
    split
    · exact adv_snoc ps p z j _ (by omega) (by simp; omega)
    · rfl

theorem adv_last (ps : List (List Int)) (p : List Int) (x : List Nat) (y : Nat)
    (hx : x.length = ps.length) :
    prodStep (ps ++ [p]) (x ++ [y]) =
      if y + 1 = p.length then (prodStep ps x).map (· ++ [0]) else some (x ++ [y + 1]) := by
  have hlen : (ps ++ [p]).length = ps.length + 1 := by simp
  simp only [prodStep, hlen, cProductAdvance]
  have hg : (ps ++ [p]).getD ps.length [] = p := by simp [List.getD_eq_getElem?_getD]
  have hi : ix (x ++ [y]) ps.length = y := by rw [← hx]; simp [ix, List.getD_eq_getElem?_getD]
  have hs : ∀ w, (x ++ [y]).set ps.length w = x ++ [w] := fun w => by rw [← hx]; simp
  simp only [hg, hi, hs]
  split
  · exact adv_snoc ps p 0 ps.length x (by omega) hx
  · rfl

theorem rowWalk (ps : List (List Int)) (p : List Int) (x : List Nat) (z : List Nat)
    (hx : x.length = ps.length) (hz : prodStep ps x = some (z.dropLast) ∧ z = z.dropLast ++ [0]) :
    ∀ (d y : Nat), y + d + 1 = p.length →
      Walk (prodStep (ps ++ [p])) (x ++ [y]) ((List.range' y (d + 1)).map (fun v => x ++ [v])) z
  | 0, y, h => by
    have := adv_last ps p x y hx
    rw [if_pos (by omega), hz.1] at this
    simp only [Option.map_some] at this
    simp only [List.range'_succ, List.range'_zero, List.map_cons, List.map_nil]
    exact Walk.cons (b := z) (by rw [this, ← hz.2]) (Walk.nil z)
  | d + 1, y, h => by
    have := adv_last ps p x y hx
    rw [if_neg (by omega)] at this
    rw [List.range'_succ, List.map_cons]
    exact Walk.cons this (rowWalk ps p x z hx hz d (y + 1) (by omega))

theorem rowRun (ps : List (List Int)) (p : List Int) (x : List Nat)
    (hx : x.length = ps.length) (hz : prodStep ps x = none) :
    ∀ (d y : Nat), y + d + 1 = p.length →
      RunTo (prodStep (ps ++ [p])) (x ++ [y]) ((List.range' y (d + 1)).map (fun v => x ++ [v]))
  | 0, y, h => by
    have := adv_last ps p x y hx
    rw [if_pos (by omega), hz] at this
    simp only [Option.map_none] at this
    simp only [List.range'_succ, List.range'_zero, List.map_cons, List.map_nil]
    exact RunTo.last this
  | d + 1, y, h => by
    have := adv_last ps p x y hx
    rw [if_neg (by omega)] at this
    rw [List.range'_succ, List.map_cons]
    exact RunTo.cons this (rowRun ps p x hx hz d (y + 1) (by omega))

theorem prod_run_snoc (ps : List (List Int)) (p : List Int) (hp : p ≠ []) {a : List Nat} {L : List (List Nat)}
    (h : RunTo (prodStep ps) a L) (ha : a.length = ps.length) :
    RunTo (prodStep (ps ++ [p])) (a ++ [0]) (pxStep L p) := by
  obtain ⟨d, hd⟩ : ∃ d, p.length = d + 1 := by
    cases p with
    | nil => contradiction
    | cons _ t => exact ⟨t.length, by simp⟩
  have hr : List.range p.length = List.range' 0 (d + 1) := by rw [hd, List.range_eq_range']
  induction h with
  | @last x h0 =>
    simp only [pxStep, List.flatMap_cons, List.flatMap_nil, List.append_nil, hr]
    exact rowRun ps p x ha h0 d 0 (by omega)
  | @cons x x' L h1 _ ih =>
    have hl : x'.length = ps.length := by
      rw [adv_length ps _ _ _ h1, ha]
    have hw := rowWalk ps p x (x' ++ [0]) ha (by simp [h1]) d 0 (by omega)
    simp only [pxStep, List.flatMap_cons, hr] at ih ⊢
    exact hw.append_run (ih hl)

theorem prod_run (pools : List (List Int)) (h : ∀ p ∈ pools, p ≠ []) :
    RunTo (prodStep pools) (List.replicate pools.length 0) (pxs pools) := by
  induction pools using snoc_induction with
  | h0 => exact RunTo.last rfl
  | hs ps p ih =>
    have h1 := ih (fun q hq => h q (by simp [hq]))
    have h2 := prod_run_snoc ps p (h p (by simp)) h1 (by simp)
    rw [pxs_snoc, List.length_append, List.length_singleton, List.replicate_succ']
    exact h2

theorem pxs_empty (pools : List (List Int)) (h : ∃ p ∈ pools, p = []) : pxs pools = [] := by
  induction pools using snoc_induction with
  | h0 => simp at h
  | hs ps p ih =>
    rw [pxs_snoc]
    by_cases hp : p = []
    · subst hp; simp [pxStep]
    · have : ∃ q ∈ ps, q = [] := by
        obtain ⟨q, hq, rfl⟩ := h
        simp only [List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | hq
        · exact ⟨_, hq, rfl⟩
        · exact absurd hq.symm hp
      rw [ih this]; rfl

theorem prodDrain (pools : List (List Int)) {idx : List Nat} {L : List (List Nat)}
    (h : RunTo (prodStep pools) idx L) : ∀ fuel, L.length ≤ fuel →
    drain cProductNext fuel { pools := pools, indices := idx, started := true, stopped := false } =
      Run.ok (L.tail.map (vals pools)) := by
  induction h with
  | @last a h0 =>
    intro fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    rw [drain_succ]
    simp only [prodStep] at h0
    simp only [cProductNext, Bool.false_eq_true, ↓reduceIte, Bool.not_true, h0]
    rfl
  | @cons a b L h1 hr ih =>
    intro fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    obtain ⟨t, rfl⟩ := hr.head
    rw [drain_succ]
    simp only [prodStep] at h1
    simp only [cProductNext, Bool.false_eq_true, ↓reduceIte, Bool.not_true, h1]
    rw [ih f (by simp at hf ⊢; omega)]
    rfl

theorem vals_zero : ∀ (pools : List (List Int)),
    pools.map (at! · 0) = vals pools (List.replicate pools.length 0)
  | [] => rfl
  | p :: ps => by simp [vals, List.replicate_succ, vals_zero ps]

/-- For an in-memory set of pools and enough fuel, the odometer yields the
values at each tuple of `pxs`. -/
theorem prod_run_new (pools : List (List Int)) (fuel : Nat) (hf : prodLen pools < fuel) :
    drain cProductNext fuel
        { pools := pools, indices := List.replicate pools.length 0, started := false, stopped := false } =
      Run.ok ((pxs pools).map (vals pools)) := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  rw [drain_succ]
  by_cases hany : pools.any (·.isEmpty) = true
  · have h0 : pxs pools = [] := by
      simp only [List.any_eq_true, List.isEmpty_iff] at hany
      obtain ⟨p, hp, h⟩ := hany
      exact pxs_empty pools ⟨p, hp, h⟩
    simp only [cProductNext, Bool.false_eq_true, ↓reduceIte, Bool.not_false, hany, h0]
    rfl
  · have hne : ∀ p ∈ pools, p ≠ [] := by
      intro p hp hz
      apply hany
      simp only [List.any_eq_true, List.isEmpty_iff]
      exact ⟨p, hp, hz⟩
    have hrun := prod_run pools hne
    obtain ⟨t, ht⟩ := hrun.head
    have hd := prodDrain pools hrun f (by rw [pxs_length]; omega)
    simp only [cProductNext, Bool.false_eq_true, ↓reduceIte, Bool.not_false, hany, vals_zero]
    rw [hd, ht]
    rfl

/-! ## The doc's list comprehension -/

theorem map_at_range (p : List Int) : (List.range p.length).map (at! p) = p := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [at!, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem vals_snoc (ps : List (List Int)) (p : List Int) (x : List Nat) (y : Nat)
    (hx : x.length = ps.length) : vals (ps ++ [p]) (x ++ [y]) = vals ps x ++ [at! p y] := by
  simp only [vals]
  rw [List.zipWith_append hx.symm]
  simp

theorem docStep_eq (ps : List (List Int)) (p : List Int) (acc : List (List Nat))
    (h : ∀ x ∈ acc, x.length = ps.length) :
    docProductStep (acc.map (vals ps)) p = (pxStep acc p).map (vals (ps ++ [p])) := by
  induction acc with
  | nil => rfl
  | cons x acc ih =>
    have h1 := ih (fun y hy => h y (by simp [hy]))
    simp only [docProductStep, pxStep, List.map_cons, List.flatMap_cons, List.map_append] at h1 ⊢
    rw [h1]
    congr 1
    calc List.map (fun y => vals ps x ++ [y]) p
        = List.map (fun y => vals ps x ++ [y]) ((List.range p.length).map (at! p)) := by
          rw [map_at_range]
      _ = _ := by
          simp only [List.map_map]
          apply List.map_congr_left
          intro y _
          simp only [Function.comp, vals_snoc ps p x y (h x (by simp))]

theorem doc_foldl (pools : List (List Int)) :
    pools.foldl docProductStep [[]] = (pxs pools).map (vals pools) := by
  induction pools using snoc_induction with
  | h0 => rfl
  | hs ps p ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih, pxs_snoc]
    exact docStep_eq ps p _ (fun x hx => (pxs_below ps x hx).1)

/-! ## Arguments -/

theorem prodPools_length (args : List (List Int)) (rep : Nat) :
    (prodPools args rep).length = args.length * rep := by
  simp only [prodPools, Int.toNat_natCast]
  by_cases h : args.length = 0
  · simp [h]
  · simp [h, List.length_flatten, Nat.mul_comm]

theorem prodLen_append (a b : List (List Int)) : prodLen (a ++ b) = prodLen a * prodLen b := by
  induction a with
  | nil => simp [prodLen]
  | cons q a ih =>
    simp only [prodLen, List.cons_append, List.map_cons, List.foldr_cons] at ih ⊢
    rw [ih, Nat.mul_assoc]

theorem prodLen_pools (args : List (List Int)) (m : Nat) :
    prodLen (prodPools args m) = prodLen args ^ m := by
  simp only [prodPools, Int.toNat_natCast]
  by_cases h : args.length = 0
  · have : args = [] := List.eq_nil_of_length_eq_zero h
    subst this
    simp [prodLen]
  · simp only [h, ↓reduceIte]
    induction m with
    | zero => simp [prodLen]
    | succ m ih =>
      rw [List.replicate_succ, List.flatten_cons, prodLen_append, ih, Nat.pow_succ, Nat.mul_comm]

theorem product_new_ok (args : List (List Int)) (rep? : Option Int) (m : Nat)
    (hrep : ((m : Nat) : Int) = rep?.getD 1) (hle : (m : Int) ≤ ssizeMax)
    (ht : tupleNewOk (args.length * (m : Int)) = true) :
    cProductNew args rep? =
      .ok { pools := prodPools args m, indices := List.replicate (prodPools args m).length 0,
            started := false, stopped := false } := by
  have hmin : ssizeMin ≤ (m : Int) := by rw [ssizeMin_eq]; omega
  have hmem : memNewOk (args.length * (m : Int)) = true :=
    memNewOk_of_tuple ht (Int.mul_nonneg (by omega) (by omega))
  have hP := prodPools_length args m
  have hparsed : cProductNew args rep? = cProductNew args (some (m : Int)) := by
    cases rep? with
    | none =>
      simp only [Option.getD_none] at hrep
      have hone : asSsize (1 : Int) = .ok 1 := asSsize_ok (by decide) (by decide)
      rw [hrep]
      simp only [cProductNew, hone, show ¬ ((1 : Int) < 0) by omega, ↓reduceIte]
    | some r => simp only [Option.getD_some] at hrep; rw [hrep]
  rw [hparsed]
  simp only [cProductNew, asSsize_ok hmin hle, show ¬ ((m : Int) < 0) by omega, ↓reduceIte]
  by_cases hm0 : m = 0
  · subst hm0
    simp only [hP]
    have a : (0 : Int) ≤ ssizeMax / 8 := by decide
    have b : mallocLimit ≠ 0 := by decide
    simp [tupleNewOk, memNewOk, a, b]
  · have hne : (m : Int) ≠ 0 := by omega
    have hdiv : ¬ ((args.length : Int) > ssizeMax / 8 / (m : Int)) := by
      have h1 := hmem
      simp only [memNewOk, Bool.and_eq_true, decide_eq_true_eq] at h1
      have : (args.length : Int) ≤ ssizeMax / 8 / (m : Int) :=
        Int.le_ediv_of_mul_le (by omega) h1.1
      omega
    have hto : ((args.length : Int) * (m : Int)).toNat = args.length * m := by
      rw [← Int.natCast_mul, Int.toNat_natCast]
    simp only [hne, ↓reduceIte, ne_eq, not_false_eq_true, hdiv, and_false, hmem, ht, Bool.not_true,
      Bool.false_eq_true, hP, hto]

/-- For a `repeat` in `Py_ssize_t` range with `pools = args * repeat` fitting in
memory (documented: "keeping pools of values in memory") and enough fuel,
`product` yields the tuples at exactly the positions in a list `L`, one
position per pool, of `(len(args[0]) * len(args[1]) * ...) ** repeat` tuples,
strictly increasing in lexicographic order. -/
def ProductSpec : Prop :=
  ∀ (args : List (List Int)) (rep? : Option Int) (fuel : Nat), 0 ≤ rep?.getD 1 →
    rep?.getD 1 ≤ ssizeMax → tupleNewOk (args.length * rep?.getD 1) = true →
    prodLen args ^ (rep?.getD 1).toNat < fuel →
    ∃ L : List (List Nat),
      cProductF fuel args rep? = Run.ok (L.map (vals (prodPools args (rep?.getD 1)))) ∧
      L.length = prodLen args ^ (rep?.getD 1).toNat ∧ L.Pairwise LexLt ∧
      ∀ x ∈ L, Below (prodPools args (rep?.getD 1)) x

theorem productSpec_proven : ProductSpec := by
  intro args rep? fuel h0 hle ht hf
  obtain ⟨m, hm⟩ : ∃ m : Nat, (m : Int) = rep?.getD 1 := ⟨(rep?.getD 1).toNat, by omega⟩
  rw [← hm] at hle ht hf ⊢
  simp only [Int.toNat_natCast] at hf ⊢
  refine ⟨pxs (prodPools args m), ?_, ?_, pxs_sorted _, pxs_below _⟩
  · simp only [cProductF, product_new_ok args rep? m hm hle ht]
    exact prod_run_new _ _ (by rw [prodLen_pools]; exact hf)
  · rw [pxs_length, prodLen_pools]

/-- For every `repeat` (negative or above `sys.maxsize`: both raise) whose
pools fit in memory, and enough fuel, the C odometer and the doc's list
comprehension give the same tuples in the same order. -/
def ProductDocAgree : Prop :=
  ∀ (args : List (List Int)) (rep? : Option Int) (fuel : Nat),
    (0 ≤ rep?.getD 1 → rep?.getD 1 ≤ ssizeMax → tupleNewOk (args.length * rep?.getD 1) = true) →
    prodLen args ^ (rep?.getD 1).toNat < fuel →
    runAgree (cProductF fuel args rep?) (docProduct args rep?)

theorem cProduct_err_neg (args : List (List Int)) (r : Int) (h : r < 0 ∨ r > ssizeMax) :
    ∃ e, cProductNew args (some r) = .error e := by
  cases ha : asSsize r with
  | error e => exact ⟨e, by simp [cProductNew, ha]⟩
  | ok v =>
    have hv : v = r ∧ r ≤ ssizeMax := by
      simp only [asSsize] at ha; split at ha <;> simp_all
    obtain ⟨rfl, hle⟩ := hv
    have : v < 0 := by omega
    exact ⟨.valueError "repeat argument cannot be negative", by simp [cProductNew, ha, this]⟩

theorem productDocAgree_proven : ProductDocAgree := by
  intro args rep? fuel hmem hf
  by_cases hbad : rep?.getD 1 < 0 ∨ rep?.getD 1 > ssizeMax
  · have hsome : ∃ r, rep? = some r ∧ (r < 0 ∨ r > ssizeMax) := by
      cases rep? with
      | none =>
        have : (1 : Int) ≤ ssizeMax := by decide
        simp only [Option.getD_none] at hbad
        omega
      | some r => exact ⟨r, rfl, by simpa using hbad⟩
    obtain ⟨r, rfl, hr⟩ := hsome
    obtain ⟨e, he⟩ := cProduct_err_neg args r hr
    have hc : cProductF fuel args (some r) = Run.err e := by simp [cProductF, he]
    have hd : ∃ e', docProduct args (some r) = Run.err e' := by
      simp only [docProduct, Option.getD_some]
      by_cases hneg : r < 0
      · exact ⟨.valueError "repeat argument cannot be negative", by simp [hneg]⟩
      · have hgt : r > ssizeMax := by omega
        have hchk : listRepeatCheck args.length r =
            .error (.overflowError "cannot fit 'int' into an index-sized integer") := by
          simp [listRepeatCheck, hgt]
        exact ⟨.overflowError "cannot fit 'int' into an index-sized integer", by simp [hneg, hchk]⟩
    obtain ⟨e', hd'⟩ := hd
    rw [hc, hd']
    exact ⟨rfl, rfl⟩
  · have h0 : 0 ≤ rep?.getD 1 := by omega
    have hle : rep?.getD 1 ≤ ssizeMax := by omega
    have ht := hmem h0 hle
    obtain ⟨m, hm⟩ : ∃ m : Nat, (m : Int) = rep?.getD 1 := ⟨(rep?.getD 1).toNat, by omega⟩
    rw [← hm] at hle ht hf
    simp only [Int.toNat_natCast] at hf
    have hc : cProductF fuel args rep? = Run.ok ((pxs (prodPools args m)).map (vals (prodPools args m))) := by
      simp only [cProductF, product_new_ok args rep? m hm hle ht]
      exact prod_run_new _ _ (by rw [prodLen_pools]; exact hf)
    have hmemN : memNewOk (args.length * (m : Int)) = true :=
      memNewOk_of_tuple ht (Int.mul_nonneg (by omega) (by omega))
    have hchk : listRepeatCheck args.length (m : Int) = .ok () := by
      simp only [listRepeatCheck]
      have h1 : ¬ ((m : Int) < ssizeMin ∨ (m : Int) > ssizeMax) := by rw [ssizeMin_eq]; omega
      rw [if_neg h1]
      by_cases h2 : args.length = 0 ∨ (m : Int) ≤ 0
      · rw [if_pos h2]
      · rw [if_neg h2]
        have h3 := hmemN
        simp only [memNewOk, Bool.and_eq_true, decide_eq_true_eq] at h3
        have h4 : (args.length : Int) * (m : Int) ≤ ssizeMax := by
          rw [ssizeMax_eq] at h3 ⊢; omega
        have h5 : (args.length : Int) ≤ ssizeMax / (m : Int) := Int.le_ediv_of_mul_le (by omega) h4
        rw [if_neg (by omega), hmemN]
        rfl
    have hd : docProduct args rep? = Run.ok ((pxs (prodPools args m)).map (vals (prodPools args m))) := by
      simp only [docProduct, ← hm, show ¬ ((m : Int) < 0) by omega, ↓reduceIte, hchk, doc_foldl]
    rw [hc, hd]
    exact ⟨rfl, rfl⟩

end PyLean.Itertools
