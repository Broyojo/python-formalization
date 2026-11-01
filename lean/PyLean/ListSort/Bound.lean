import PyLean.ListSort.Perm

/-!
# The stack bound for the merge policy and for the whole sort

* `stackInv_bound`: below the top entry there are `k` entries with `2^k < 2N`.
* `policyRun`: the merge policy alone driven by an arbitrary list of positive
  run lengths (the run structure `count_run`/`minrun` would produce is one of
  them).
* `sortCore_pushOk`: the full sort, for every comparison function, never
  violates `assert(ms.n < MAX_MERGE_PENDING)` when `N <= PY_SSIZE_T_MAX`.
-/

namespace PyLean.ListSort

theorem stackInv_bound {N pos : Nat} {t : Slice} {stk : List Slice}
    (h : StackInv N pos (t :: stk)) : 2 ^ stk.length < 2 * N := by
  obtain ⟨xs, hmap, htop⟩ := h
  match xs, hmap, htop with
  | (e, g) :: rest, hmap, htop =>
    simp only [List.map_cons, List.cons.injEq] at hmap
    obtain ⟨rfl, rfl⟩ := hmap
    obtain ⟨_, hlen, hend, hpos, hbel⟩ := htop
    rcases below_bound rest hlen (by omega) hbel with h | ⟨e', g', rest', rfl, hl, hp⟩
    · subst h; simp; omega
    · simp only [List.length_map]
      exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hl) hp

/-- The powers of the entries below the top strictly decrease downwards and are
`>= 1` (`listsort.txt:426-427`; `found_new_run`'s `assert`). -/
def PowersStrict (stk : List Slice) : Prop :=
  Chn (fun e e' => e'.power < e.power) (stk.drop 1) ∧ ∀ e ∈ stk.drop 1, 1 ≤ e.power

theorem below_strict {N : Nat} :
    ∀ {f : Run} {ap : Option Nat} (xs : List (Slice × List Run)), Below N f ap xs →
      Chn (fun e e' => e'.power < e.power) (xs.map Prod.fst) ∧ ∀ e ∈ xs.map Prod.fst, 1 ≤ e.power
  | _, _, [], _ => ⟨trivial, by simp⟩
  | f, _, (e, g) :: rest, h => by
    obtain ⟨fst, lst, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
    have ih := below_strict rest h11
    refine ⟨?_, ?_⟩
    · match rest, h11, ih with
      | [], _, _ => trivial
      | (e', g') :: rest', h11, ih =>
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hlt, _⟩ := h11
        exact ⟨hlt e.power rfl, ih.1⟩
    · intro e' he'
      simp only [List.map_cons, List.mem_cons] at he'
      rcases he' with rfl | he'
      · exact h9
      · exact ih.2 e' he'

theorem stackInv_strict {N pos : Nat} {stk : List Slice} (h : StackInv N pos stk) :
    PowersStrict stk := by
  obtain ⟨xs, rfl, htop⟩ := h
  match xs, htop with
  | [], _ => exact ⟨trivial, by simp⟩
  | (e, g) :: rest, htop =>
    obtain ⟨_, _, _, _, hbel⟩ := htop
    simpa [PowersStrict] using below_strict rest hbel

/-! ## Preservation of a property of the merge state -/

theorem mergeWhile_pres {σ : Type} (mf : Nat → Nat → Nat → σ → σ) (P : σ → Prop)
    (hP : ∀ b na nb s, P s → P (mf b na nb s)) (p : Nat) :
    ∀ (n : Nat) (stk : List Slice) (s : σ), stk.length ≤ n → P s → P (mergeWhile mf p stk s).2 := by
  intro n
  induction n with
  | zero => intro stk s h hs; match stk with | [] => simp [mergeWhile]; exact hs
  | succ n ih =>
    intro stk s h hs
    match stk with
    | t :: u :: rest =>
      rw [mergeWhile]
      split
      · exact ih _ _ (by simp at h ⊢; omega) (hP _ _ _ _ hs)
      · exact hs
    | [t] => simp [mergeWhile]; exact hs
    | [] => simp [mergeWhile]; exact hs

theorem foundNewRun_pres {σ : Type} (mf : Nat → Nat → Nat → σ → σ) (P : σ → Prop)
    (hP : ∀ b na nb s, P s → P (mf b na nb s)) (N n2 : Nat) (stk : List Slice) (s : σ) (hs : P s) :
    P (foundNewRun mf N n2 stk s).2 := by
  unfold foundNewRun
  split
  · exact hs
  · rename_i top rest
    have := mergeWhile_pres mf P hP (powerloop top.base top.len n2 N) _ (top :: rest) s
      (Nat.le_refl _) hs
    dsimp only
    generalize mergeWhile mf (powerloop top.base top.len n2 N) (top :: rest) s = R at this ⊢
    obtain ⟨stk', s'⟩ := R
    cases stk' <;> exact this

theorem forceCollapse_pres {σ : Type} (mf : Nat → Nat → Nat → σ → σ) (P : σ → Prop)
    (hP : ∀ b na nb s, P s → P (mf b na nb s)) :
    ∀ (n : Nat) (stk : List Slice) (s : σ), stk.length ≤ n → P s → P (forceCollapse mf stk s).2 := by
  intro n
  induction n with
  | zero => intro stk s h hs; match stk with | [] => simp [forceCollapse]; exact hs
  | succ n ih =>
    intro stk s h hs
    match stk with
    | t :: u :: v :: rest =>
      rw [forceCollapse]
      split
      · exact ih _ _ (by simp at h ⊢; omega) (hP _ _ _ _ hs)
      · exact ih _ _ (by simp at h ⊢; omega) (hP _ _ _ _ hs)
    | [t, u] => rw [forceCollapse]; exact ih _ _ (by simp at h ⊢; omega) (hP _ _ _ _ hs)
    | [t] => simp [forceCollapse]; exact hs
    | [] => simp [forceCollapse]; exact hs

theorem forceCollapse_len {σ : Type} (mf : Nat → Nat → Nat → σ → σ) :
    ∀ (n : Nat) (stk : List Slice) (s : σ), stk.length ≤ n →
      (forceCollapse mf stk s).1.length = min stk.length 1 := by
  intro n
  induction n with
  | zero => intro stk s h; match stk with | [] => simp [forceCollapse]
  | succ n ih =>
    intro stk s h
    match stk with
    | t :: u :: v :: rest =>
      rw [forceCollapse]
      split
      · rw [ih _ _ (by simp at h ⊢; omega)]; simp
      · rw [ih _ _ (by simp at h ⊢; omega)]; simp
    | [t, u] => rw [forceCollapse, ih _ _ (by simp at h ⊢; omega)]; simp
    | [t] => simp [forceCollapse]
    | [] => simp [forceCollapse]

/-! ## The merge policy on its own -/

/-- One run of length `n2`: `found_new_run` (merges are no-ops on the data) and
the push, recording whether `assert(ms.n < MAX_MERGE_PENDING)` held. -/
def policyStep (N : Nat) (st : List Slice × Nat × Bool) (n2 : Nat) : List Slice × Nat × Bool :=
  let stk := (foundNewRun (fun _ _ _ (u : Unit) => u) N n2 st.1 ()).1
  (⟨st.2.1, n2, 0⟩ :: stk, st.2.1 + n2, st.2.2 && decide (stk.length < MAX_MERGE_PENDING))

/-- The policy over a sequence of run lengths: final stack, position, and
whether every push satisfied the `assert`. -/
def policyRun (N : Nat) (lens : List Nat) : List Slice × Nat × Bool :=
  lens.foldl (policyStep N) ([], 0, true)

theorem policy_foldl (N : Nat) (hN : N ≤ 2 ^ 63 - 1) :
    ∀ (lens : List Nat) (stk : List Slice) (pos : Nat) (ok : Bool),
      StackInv N pos stk → (ok = true → stk.length ≤ MAX_MERGE_PENDING) →
      (∀ l ∈ lens, 0 < l) → pos + lens.sum ≤ N →
      StackInv N (pos + lens.sum) (lens.foldl (policyStep N) (stk, pos, ok)).1 ∧
        (lens.foldl (policyStep N) (stk, pos, ok)).2.1 = pos + lens.sum ∧
        (lens.foldl (policyStep N) (stk, pos, ok)).2.2 = ok
  | [], stk, pos, ok, h, _, _, _ => by simpa using h
  | l :: lens, stk, pos, ok, h, hok, hl, hs => by
    simp only [List.foldl_cons, List.sum_cons]
    have hinv := foundNewRun_inv (fun _ _ _ (u : Unit) => u) N pos l stk () h (hl l (by simp))
      (by simp at hs; omega)
    have hb := stackInv_bound hinv
    have h64 : (foundNewRun (fun _ _ _ (u : Unit) => u) N l stk ()).1.length < MAX_MERGE_PENDING := by
      unfold MAX_MERGE_PENDING
      have : 2 * N < 2 ^ 64 := by omega
      have := Nat.lt_trans hb this
      exact (Nat.pow_lt_pow_iff_right (by decide)).1 this
    have := policy_foldl N hN lens _ (pos + l) (ok && decide ((foundNewRun (fun _ _ _ (u : Unit) => u)
      N l stk ()).1.length < MAX_MERGE_PENDING)) hinv (fun _ => by simp; unfold MAX_MERGE_PENDING at h64 ⊢; omega)
      (fun x hx => hl x (by simp [hx])) (by simp at hs; omega)
    simp only [policyStep] at this ⊢
    rw [show pos + (l + lens.sum) = pos + l + lens.sum by omega]
    refine ⟨this.1, this.2.1, ?_⟩
    rw [this.2.2]
    simp [h64]

theorem policyRun_spec (N : Nat) (hN : N ≤ 2 ^ 63 - 1) (lens : List Nat) (hl : ∀ l ∈ lens, 0 < l)
    (hs : lens.sum ≤ N) :
    StackInv N lens.sum (policyRun N lens).1 ∧ (policyRun N lens).2.2 = true := by
  have := policy_foldl N hN lens [] 0 true ⟨[], rfl, rfl⟩ (fun _ => by simp) hl (by simpa using hs)
  simp only [Nat.zero_add] at this
  exact ⟨this.1, this.2.2⟩

/-! ## The full sort, for every comparison function -/

variable {α : Type}

/-- Invariant of the main loop at array position `pos`. -/
def LoopOK (xs : List α) (N pos : Nat) (st : Sorter α) : Prop :=
  st.arr.Perm xs ∧ StackInv N pos st.stk ∧ pos ≤ N ∧ (N ≤ 2 ^ 63 - 1 → st.pushOk = true)

theorem len_lt_64 {N k : Nat} (hN : N ≤ 2 ^ 63 - 1) (h : 2 ^ k < 2 * N) : k < MAX_MERGE_PENDING := by
  unfold MAX_MERGE_PENDING
  have : 2 * N < 2 ^ 64 := by omega
  exact (Nat.pow_lt_pow_iff_right (by decide)).1 (Nat.lt_trans h this)

theorem sortStep_ok (lt : α → α → Bool) (xs : List α) (N minrun pos : Nat) (st : Sorter α)
    (hNx : xs.length = N) (h : LoopOK xs N pos st) (hpos : pos < N) :
    1 ≤ (sortStep lt N minrun pos st).2 ∧ pos + (sortStep lt N minrun pos st).2 ≤ N ∧
      LoopOK xs N (pos + (sortStep lt N minrun pos st).2) (sortStep lt N minrun pos st).1 := by
  obtain ⟨hperm, hstk, _, hok⟩ := h
  have hlen : st.arr.length = N := by rw [hperm.length_eq, hNx]
  have hdl : (st.arr.drop pos).length = N - pos := by simp [hlen]
  have hcr := countRun_perm lt (st.arr.drop pos) st.ms
  simp only [sortStep]
  generalize countRun lt (st.arr.drop pos) st.ms = CR at hcr
  obtain ⟨n0, rest0, ms0⟩ := CR
  simp only at hcr
  obtain ⟨hp0, hn0, hn0'⟩ := hcr
  have hn0 := hn0 (by intro h; rw [h] at hdl; simp at hdl; omega)
  rw [hdl] at hn0'
  -- the run after the optional binarysort
  have hrun : ∃ n rest ms, (if n0 < minrun then
      ((if N - pos ≤ minrun then N - pos else minrun),
        (binarysort lt rest0 (if N - pos ≤ minrun then N - pos else minrun) n0 ms0).1,
        (binarysort lt rest0 (if N - pos ≤ minrun then N - pos else minrun) n0 ms0).2)
      else (n0, rest0, ms0)) = (n, rest, ms) ∧ 1 ≤ n ∧ n ≤ N - pos ∧ rest.Perm (st.arr.drop pos) := by
    split
    · refine ⟨_, _, _, rfl, by split <;> omega, by split <;> omega, ?_⟩
      refine (binarysort_perm lt rest0 _ n0 ms0 ?_).trans hp0
      have : n0 ≠ 0 := by omega
      simp only [this, ↓reduceIte]; split <;> omega
    · exact ⟨_, _, _, rfl, hn0, hn0', hp0⟩
  obtain ⟨n, rest, ms, hEq2, hn1, hn2, hrp⟩ := hrun
  -- the `let` of the binarysort branch is exactly the `if` above
  have hlet : (if n0 < minrun then
      (let force := if N - pos ≤ minrun then N - pos else minrun
       let (rest, ms) := binarysort lt rest0 force n0 ms0
       (force, rest, ms))
      else (n0, rest0, ms0)) = (n, rest, ms) := by
    rw [← hEq2]
  rw [hlet]
  simp only
  have harr : (st.arr.take pos ++ rest).Perm xs := by
    refine List.Perm.trans ?_ hperm
    conv => rhs; rw [← List.take_append_drop pos st.arr]
    exact hrp.append_left _
  have hinv := foundNewRun_inv (mergeAtArr lt) N pos n st.stk (st.arr.take pos ++ rest, ms) hstk
    (by omega) (by omega)
  have hpres := foundNewRun_pres (mergeAtArr lt) (fun s => s.1.Perm xs)
    (fun b na nb s hs => (mergeAtArr_perm lt b na nb s).trans hs) N n st.stk
    (st.arr.take pos ++ rest, ms) harr
  generalize foundNewRun (mergeAtArr lt) N n st.stk (st.arr.take pos ++ rest, ms) = F at hinv hpres
  obtain ⟨stk', arr', ms'⟩ := F
  simp only at hinv hpres ⊢
  refine ⟨hn1, by omega, hpres, hinv, by omega, fun hN => ?_⟩
  simp only [hok hN, Bool.true_and, decide_eq_true_eq]
  exact len_lt_64 hN (stackInv_bound hinv)

theorem sortLoop_ok (lt : α → α → Bool) (xs : List α) (N minrun : Nat) (hNx : xs.length = N) :
    ∀ (fuel pos : Nat) (st : Sorter α), LoopOK xs N pos st → pos < N → N ≤ pos + fuel →
      LoopOK xs N N (sortLoop lt N minrun fuel pos st)
  | 0, pos, st, _, hpos, hf => by omega
  | fuel + 1, pos, st, h, hpos, hf => by
    have hs := sortStep_ok lt xs N minrun pos st hNx h hpos
    simp only [sortLoop]
    generalize sortStep lt N minrun pos st = S at hs
    obtain ⟨st', n⟩ := S
    simp only at hs ⊢
    split
    · exact sortLoop_ok lt xs N minrun hNx fuel (pos + n) st' hs.2.2 (by omega) (by omega)
    · have : pos + n = N := by omega
      rw [this] at hs
      exact hs.2.2

/-- The sort's result is a permutation of the input, for every comparison
function, and when `len(xs) <= PY_SSIZE_T_MAX` it never violates
`assert(ms.n < MAX_MERGE_PENDING)`. -/
theorem sortCore_ok (lt : α → α → Bool) (xs : List α) :
    (xs.length ≤ 2 ^ 63 - 1 → (sortCore lt xs).pushOk = true) ∧ (sortCore lt xs).arr.Perm xs := by
  unfold sortCore
  dsimp only
  split
  · exact ⟨fun _ => rfl, List.Perm.refl _⟩
  · have h0 : LoopOK xs xs.length 0 { arr := xs, ms := {}, stk := [], pushOk := true } :=
      ⟨List.Perm.refl _, ⟨[], rfl, rfl⟩, by omega, fun _ => rfl⟩
    have h := sortLoop_ok lt xs xs.length (computeMinrun xs.length) rfl xs.length 0 _ h0
      (by omega) (by omega)
    generalize sortLoop lt xs.length (computeMinrun xs.length) xs.length 0 _ = st at h ⊢
    obtain ⟨hperm, _, _, hok⟩ := h
    have hfc := forceCollapse_pres (mergeAtArr lt) (fun s => s.1.Perm xs)
      (fun b na nb s hs => (mergeAtArr_perm lt b na nb s).trans hs) _ st.stk (st.arr, st.ms)
      (Nat.le_refl _) hperm
    generalize forceCollapse (mergeAtArr lt) st.stk (st.arr, st.ms) = F at hfc
    obtain ⟨stk', arr', ms'⟩ := F
    exact ⟨hok, hfc⟩

end PyLean.ListSort
