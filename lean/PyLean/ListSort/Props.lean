import PyLean.ListSort.Sort
import PyLean.ListSort.Minrun
import PyLean.ListSort.Compare

/-!
# Properties of `list.sort` (registry statements and proofs)

Every statement quantifies over all inputs. Hypotheses are documented
preconditions or type invariants:

* `n <= PY_SSIZE_T_MAX = 2**63 - 1`: a list length is a `Py_ssize_t`;
* `n <= 2**62` (powerloop overflow): real lists have at most
  `PY_SSIZE_T_MAX / sizeof(PyObject *) = 2**60 - 1` items (`list_resize`);
* sortedness/non-emptiness of the runs handed to `gallop_*`/`merge_at`: the
  preconditions in their C comments, established by the callers (and the
  end-to-end theorems need none of them).
-/

namespace PyLean.ListSort

/-! ## Goal 1: the merge policy and the pending stack -/

/-- `powerloop(s1, n1, n2, n)` returns the first bit position `L >= 1` at which
the binary expansions of the two run midpoints `(s1 + n1/2)/n` and
`(s1 + n1 + n2/2)/n` differ (`listsort.txt:453-464`), and `2^L < 2n`. -/
def PowerloopFirstBit : Prop :=
  ∀ s1 n1 n2 n : Nat, 0 < n1 → 0 < n2 → s1 + n1 + n2 ≤ n →
    1 ≤ powerloop s1 n1 n2 n ∧
    (∀ L, L < powerloop s1 n1 n2 n → gq n L (2 * s1 + n1) = gq n L (2 * s1 + n1 + n1 + n2)) ∧
    gq n (powerloop s1 n1 n2 n) (2 * s1 + n1) < gq n (powerloop s1 n1 n2 n) (2 * s1 + n1 + n1 + n2) ∧
    2 ^ powerloop s1 n1 n2 n < 2 * n

theorem powerloopFirstBit_proven : PowerloopFirstBit := fun s1 n1 n2 n h1 h2 hn =>
  let h := powerloop_spec s1 n1 n2 n h1 h2 hn
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- No intermediate value of `powerloop` (`2*s1 + n1`, `a + n1 + n2`, the
shifted `a` and `b`) leaves `Py_ssize_t`, for every list length `n <= 2**62`. -/
def PowerloopNoOverflow : Prop :=
  ∀ s1 n1 n2 n : Nat, 0 < n1 → 0 < n2 → s1 + n1 + n2 ≤ n → n ≤ 2 ^ 62 →
    (powerloopOvf s1 n1 n2 n).2 = false

theorem powerloopNoOverflow_proven : PowerloopNoOverflow := fun s1 n1 n2 n h1 h2 hn h62 =>
  (powerloop_spec s1 n1 n2 n h1 h2 hn).2.2.2.2 h62

/-- For every list length `N <= PY_SSIZE_T_MAX` and every sequence of positive run
lengths (any run structure, not only the ones `count_run`/`minrun_next` produce),
after each `found_new_run` + push the stored powers strictly increase towards
the top and are `>= 1` (the `assert` at `listobject.c:2739`,
`listsort.txt:497-498`). -/
def PolicyPowersStrict : Prop :=
  ∀ (N : Nat) (lens : List Nat), N ≤ 2 ^ 63 - 1 → (∀ l ∈ lens, 0 < l) → lens.sum ≤ N →
    PowersStrict (policyRun N lens).1

theorem policyPowersStrict_proven : PolicyPowersStrict := fun N lens hN hl hs =>
  stackInv_strict (policyRun_spec N hN lens hl hs).1

/-- For every `N <= PY_SSIZE_T_MAX` and every non-empty sequence of positive run
lengths summing to at most `N`, after each push the stack holds `s` entries
with `2^s < 4N` (i.e. `s <= ceil(log2 N) + 1`), and no push violates
`assert(ms.n < MAX_MERGE_PENDING)` (`listobject.c:3165`). -/
def PolicyStackBound : Prop :=
  ∀ (N : Nat) (lens : List Nat), N ≤ 2 ^ 63 - 1 → (∀ l ∈ lens, 0 < l) → lens.sum ≤ N → lens ≠ [] →
    2 ^ (policyRun N lens).1.length < 4 * N ∧ (policyRun N lens).2.2 = true

theorem policy_nonempty (N : Nat) :
    ∀ (lens : List Nat) (st : List Slice × Nat × Bool), lens ≠ [] →
      ∃ t rest, (lens.foldl (policyStep N) st).1 = t :: rest
  | [], _, h => absurd rfl h
  | [l], st, _ => ⟨_, _, rfl⟩
  | l :: l' :: lens, st, _ => policy_nonempty N (l' :: lens) _ (by simp)

theorem policyStackBound_proven : PolicyStackBound := by
  intro N lens hN hl hs hne
  have h := policyRun_spec N hN lens hl hs
  refine ⟨?_, h.2⟩
  obtain ⟨t, rest, he⟩ := policy_nonempty N lens ([], 0, true) hne
  have hst := h.1
  unfold policyRun at hst ⊢
  rw [he] at hst ⊢
  have := stackInv_bound hst
  simp only [List.length_cons, Nat.pow_succ]
  omega

/-- The run lengths `[2^k, 2^k, 2^(k-1), ..., 2, 1, 1]` (sum `3 * 2^k`). -/
def tightLens (k : Nat) : List Nat := 2 ^ k :: ((List.range (k + 1)).reverse.map (fun i => 2 ^ i)) ++ [1]

/-- The bound is attained: for `N = 3 * 2**61 <= PY_SSIZE_T_MAX` there is a run
structure that fills all `MAX_MERGE_PENDING = 64` slots (the `assert` still
holds). So 64 is exactly, not "plenty", large enough for arbitrary runs. -/
def PolicyStackTight : Prop :=
  3 * 2 ^ 61 ≤ 2 ^ 63 - 1 ∧ (∀ l ∈ tightLens 61, 0 < l) ∧ (tightLens 61).sum = 3 * 2 ^ 61 ∧
    (policyRun (3 * 2 ^ 61) (tightLens 61)).1.length = MAX_MERGE_PENDING ∧
    (policyRun (3 * 2 ^ 61) (tightLens 61)).2.2 = true

set_option maxRecDepth 100000 in
theorem policyStackTight_proven : PolicyStackTight := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩
  · intro l hl
    have : l = 2 ^ 61 ∨ (∃ i, 2 ^ i = l) ∨ l = 1 := by
      simp only [tightLens, List.mem_cons, List.mem_append, List.mem_map, List.mem_reverse,
        List.mem_range, List.not_mem_nil] at hl
      rcases hl with (h | ⟨i, _, h⟩) | h | h
      · exact .inl h
      · exact .inr (.inl ⟨i, h⟩)
      · exact .inr (.inr h)
      · exact h.elim
    rcases this with h | ⟨i, h⟩ | h
    · rw [h]; exact Nat.two_pow_pos _
    · rw [← h]; exact Nat.two_pow_pos _
    · rw [h]; decide
  · simp [tightLens, List.range, List.range.loop]
  · simp [tightLens, List.range, List.range.loop, policyRun, policyStep, foundNewRun, mergeWhile, powerloop,
      powerloopOvf, powerIter, MAX_MERGE_PENDING]
  · simp [tightLens, List.range, List.range.loop, policyRun, policyStep, foundNewRun, mergeWhile, powerloop,
      powerloopOvf, powerIter, MAX_MERGE_PENDING]

/-- The comment at `listobject.c:1739-1743`: "For a list with n elements, this
needs at most floor(log2(n)) + 1 entries even if we didn't force runs to a
minimal length." -/
def StackCommentLog2 : Prop :=
  ∀ (N : Nat) (lens : List Nat), (∀ l ∈ lens, 0 < l) → lens.sum = N →
    (policyRun N lens).1.length ≤ Nat.log2 N + 1

theorem stackCommentLog2_refuted : ¬ StackCommentLog2 := by
  intro h
  have := h 3 [1, 1, 1] (by decide) rfl
  have e : (policyRun 3 [1, 1, 1]).1.length = 3 := by
    simp [policyRun, policyStep, foundNewRun, mergeWhile, powerloop, powerloopOvf, powerIter]
  rw [e] at this
  have : Nat.log2 3 = 1 := by decide
  omega

/-- The whole sort, for every item type, every comparison function (including
inconsistent ones) and every list of length `<= PY_SSIZE_T_MAX`, never violates
`assert(ms.n < MAX_MERGE_PENDING)` before a push (`listobject.c:3165`). In a
release build that `assert` is compiled out, so a violation would write past
`ms.pending[]`. -/
def SortPushAssert : Prop :=
  ∀ (α : Type) (lt : α → α → Bool) (xs : List α), xs.length ≤ 2 ^ 63 - 1 → (sortCore lt xs).pushOk = true

theorem sortPushAssert_proven : SortPushAssert := fun _ lt xs h => (sortCore_ok lt xs).1 h

/-- The generator `merge_init` (`listobject.c:2282-2288`) sets up and `minrun_next`
(:2767-2775) runs, for every list length `N`, with `e = mr_e` and `P = 2^e`:

* for `N < 64`, `e = 0` and every value is `N`;
* for `N >= 64`, `32 * P <= N < 64 * P`, so every value lies in `[32, MAX_MINRUN]`,
  which is `binarysort`'s `assert(n <= MAX_MINRUN)` at :1843;
* after `k` calls `mr_current` is `kN mod P`, and call `k` returns
  `⌊(k+1)N / P⌋ - ⌊kN / P⌋`;
* any `m` consecutive values add up to `⌊mN / P⌋` or one more: "the lengths of run
  pairs merged never differ by more than one" (`listsort.txt:311-314`), at every level;
* the first `P` values add up to exactly `N`, so a list of short natural runs splits
  into a power of two of runs (`listsort.txt:311`);
* for `N = 2^j >= 64` every value is 32 (`listsort.txt:277-282`);
* for `N <= 2**62`, `mr_current + listlen` stays in `Py_ssize_t`
  (`assert(ms->mr_current >= 0)`, :2771).

The bound on `N` is the one `PowerloopNoOverflow` has: real lists have at most
`2**60 - 1` items. -/
def MinrunSpec : Prop :=
  ∀ N : Nat,
    (mergeInitMr N).mask = 2 ^ mrE N - 1 ∧
    (N < 64 → mrE N = 0 ∧ ∀ k, minrunAt N k = N) ∧
    (64 ≤ N → 32 * 2 ^ mrE N ≤ N ∧ N < 64 * 2 ^ mrE N ∧
      ∀ k, 32 ≤ minrunAt N k ∧ minrunAt N k ≤ MAX_MINRUN) ∧
    (∀ k, (mrAfter (mergeInitMr N) k).current = k * N % 2 ^ mrE N) ∧
    (∀ k, minrunAt N k = (k + 1) * N / 2 ^ mrE N - k * N / 2 ^ mrE N) ∧
    (∀ k m, m * N / 2 ^ mrE N ≤ minrunSum N k m ∧ minrunSum N k m ≤ m * N / 2 ^ mrE N + 1) ∧
    minrunSum N 0 (2 ^ mrE N) = N ∧
    (∀ j, 6 ≤ j → N = 2 ^ j → ∀ k, minrunAt N k = MAX_MINRUN / 2) ∧
    (N ≤ 2 ^ 62 → ∀ k, (mrAfter (mergeInitMr N) k).current + N < 2 ^ 63)

theorem minrunSpec_proven : MinrunSpec := by
  intro N
  refine ⟨mergeInitMr_mask N, ?_, ?_, mrAfter_current N, minrunAt_formula N, minrunSum_bounds N,
    minrunSum_full N, ?_, fun h k => current_add_lt N k h⟩
  · intro h
    have he := (mrE_bounds N).1 h
    refine ⟨he, fun k => minrunAt_of_dvd N N (by simp [he]) k⟩
  · intro h
    obtain ⟨h1, h2⟩ := (mrE_bounds N).2 h
    refine ⟨h1, h2, fun k => ?_⟩
    have hb := minrunAt_bounds N k
    have hP : 0 < 2 ^ mrE N := Nat.two_pow_pos _
    have h32 : 32 ≤ N / 2 ^ mrE N := (Nat.le_div_iff_mul_le hP).2 h1
    have h64 : N / 2 ^ mrE N < 64 := (Nat.div_lt_iff_lt_mul hP).2 h2
    have hM : MAX_MINRUN = 64 := rfl
    omega
  · intro j hj hN k
    subst hN
    exact minrunAt_pow j hj k

/-! ## Goal 2: the pieces and the whole sort -/

/-- `gallop_left`/`gallop_right` on a sorted vector, for every `hint < n`:
`gallop_left` returns the number of items `< key` (`a[k-1] < key <= a[k]`,
`listobject.c:2077-2079`), `gallop_right` the number of items `<= key`
(`a[k-1] <= key < a[k]`, `:2166-2168`). -/
def GallopSpec : Prop :=
  ∀ (α : Type) (kf : α → Int) (key : α) (A : List α) (hint : Nat) (ms : MS),
    Sorted kf A → hint < A.length →
      (gallopLeft (ltOf kf) key (fun i => A.getD i key) A.length hint ms).1 =
        (A.takeWhile (fun x => decide (kf x < kf key))).length ∧
      (gallopRight (ltOf kf) key (fun i => A.getD i key) A.length hint ms).1 =
        (A.takeWhile (fun x => decide (kf x ≤ kf key))).length

theorem gallopSpec_proven : GallopSpec := by
  intro α kf key A hint ms hs hh
  have hget : ∀ i (hi : i < A.length), A.getD i key = A[i] := fun i hi => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact ⟨gallopLeft_spec kf key A _ hint ms hs hget hh, gallopRight_spec kf key A _ hint ms hs hget hh⟩

/-- `binarysort(a, n, ok)` with `a[:max(ok,1)]` sorted and `max(ok,1) <= n`
leaves the stable sort of `a[:n]` followed by `a[n:]` (`listobject.c:1822-1831`). -/
def BinarysortStable : Prop :=
  ∀ (α : Type) (kf : α → Int) (a : List α) (n ok : Nat) (ms : MS),
    (if ok = 0 then 1 else ok) ≤ n → Sorted kf (a.take (if ok = 0 then 1 else ok)) →
      (binarysort (ltOf kf) a n ok ms).1 = stableSort kf (a.take n) ++ a.drop n

theorem binarysortStable_proven : BinarysortStable := by
  intro α kf a n ok ms h1 h2
  obtain ⟨R, hR, hss⟩ := binarysort_spec kf a n ok ms h1 h2
  rw [hR, ss_eq_stableSort hss]

/-- `count_run` on a non-empty slice returns `1 <= n <= len` and leaves the
stable sort of the first `n` items (ascending runs, descending runs with their
all-equal groups kept in order, plus the ascending extension;
`listobject.c:1963-2064`), the rest untouched. -/
def CountRunSpec : Prop :=
  ∀ (α : Type) (kf : α → Int) (xs : List α) (ms : MS), xs ≠ [] →
    1 ≤ (countRun (ltOf kf) xs ms).1 ∧ (countRun (ltOf kf) xs ms).1 ≤ xs.length ∧
      (countRun (ltOf kf) xs ms).2.1 =
        stableSort kf (xs.take (countRun (ltOf kf) xs ms).1) ++ xs.drop (countRun (ltOf kf) xs ms).1

theorem countRunSpec_proven : CountRunSpec := by
  intro α kf xs ms hne
  have hp := countRun_perm (ltOf kf) xs ms
  obtain ⟨R, hR, hss⟩ := countRun_spec kf xs ms hne
  exact ⟨hp.2.1 hne, hp.2.2, by rw [hR, ss_eq_stableSort hss]⟩

/-- `merge_at` on two sorted non-empty adjacent runs produces their stable merge
(through `merge_lo` or `merge_hi`, galloping or not), for every merge state
(`min_gallop`). -/
def MergeAtStable : Prop :=
  ∀ (α : Type) (kf : α → Int) (A B : List α) (ms : MS), Sorted kf A → Sorted kf B → A ≠ [] → B ≠ [] →
    (mergeAt (ltOf kf) A B ms).1 = stableSort kf (A ++ B)

theorem mergeAtStable_proven : MergeAtStable := fun _ kf A B ms hA hB hAne hBne =>
  ss_eq_stableSort (mergeAt_spec kf A B ms hA hB hAne hBne)

/-- "Even in case of error, the list will be some permutation of its input
state (nothing is lost or duplicated)" (`listobject.c:2940-2944`): for every
comparison function, however inconsistent, the result of `list.sort` (with or
without `reverse`) is a permutation of the input. -/
def PermAnyCompare : Prop :=
  ∀ (α : Type) (lt : α → α → Bool) (xs : List α) (reverse : Bool), (listSort lt xs reverse).Perm xs

theorem permAnyCompare_proven : PermAnyCompare := by
  intro α lt xs rev
  unfold listSort listSortCnt
  split
  · exact List.Perm.refl _
  · have h := (sortCore_ok lt (if rev then xs.reverse else xs)).2
    cases rev
    · simpa using h
    · simp only [↓reduceIte]
      exact (List.reverse_perm _).trans (h.trans (List.reverse_perm _))

theorem stableSort_short (kf : α → Int) (xs : List α) (h : xs.length < 2) : stableSort kf xs = xs := by
  apply (ss_eq_stableSort _).symm
  apply Sorted.ss
  match xs, h with
  | [], _ => simp [Sorted]
  | [x], _ => simp [Sorted]

theorem listSort_eq (kf : α → Int) (xs : List α) : listSort (ltOf kf) xs false = stableSort kf xs := by
  unfold listSort listSortCnt
  split
  · rename_i h; exact (stableSort_short kf xs h).symm
  · simpa using sortCore_eq kf xs

theorem listSort_rev_eq (kf : α → Int) (xs : List α) :
    listSort (ltOf kf) xs true = (stableSort kf xs.reverse).reverse := by
  unfold listSort listSortCnt
  split
  · rename_i h
    rw [stableSort_short kf _ (by simpa using h), List.reverse_reverse]
  · simp only [↓reduceIte]
    rw [sortCore_eq]

/-- For every item type and integer-valued key, `list.sort()` with items
compared by `<` on the key is the stable sort: sorted, a permutation, and items
with equal keys keep their order (the docstring, `listobject.c:2953-2956`). -/
def SortIsStableSort : Prop :=
  ∀ (α : Type) (kf : α → Int) (xs : List α),
    let r := listSort (ltOf kf) xs
    r.Pairwise (fun a b => kf a ≤ kf b) ∧ r.Perm xs ∧
      ∀ k, r.filter (fun e => kf e == k) = xs.filter (fun e => kf e == k)

theorem sortIsStableSort_proven : SortIsStableSort := by
  intro α kf xs
  have h := stableSort_spec kf xs
  simp only [listSort_eq]
  exact ⟨h.1, h.perm.symm, fun k => (h.2 k).symm⟩

/-- Python ints sorted with `<`: `sorted(xs)` is non-decreasing and a
permutation; on `(value, index)` pairs sorted by value, items with equal values
keep increasing indices (stability made visible). -/
def IntSortStable : Prop :=
  ∀ xs : List Int,
    (listSort (fun a b => decide (a < b)) xs).Pairwise (· ≤ ·) ∧
    (listSort (fun a b => decide (a < b)) xs).Perm xs ∧
    (listSort (fun p q : Int × Nat => decide (p.1 < q.1)) xs.zipIdx).Pairwise
      (fun p q => p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2))

theorem pairwise_of_filters {β : Type} (key : β → Int) (Q : β → β → Prop) :
    ∀ (L : List β), (∀ k, (L.filter (fun e => key e == k)).Pairwise Q) →
      L.Pairwise (fun p q => key p = key q → Q p q)
  | [], _ => List.Pairwise.nil
  | a :: L, h => by
    refine List.pairwise_cons.2 ⟨fun q hq hk => ?_, pairwise_of_filters key Q L (fun k => ?_)⟩
    · have := h (key a)
      simp only [List.filter_cons, beq_self_eq_true, ↓reduceIte] at this
      exact (List.pairwise_cons.1 this).1 q (List.mem_filter.2 ⟨hq, by simp [hk]⟩)
    · have := h k
      rw [List.filter_cons] at this
      split at this
      · exact (List.pairwise_cons.1 this).2
      · exact this

theorem intSortStable_proven : IntSortStable := by
  intro xs
  have h1 := sortIsStableSort_proven Int id xs
  have h2 := sortIsStableSort_proven (Int × Nat) Prod.fst xs.zipIdx
  refine ⟨h1.1, h1.2.1, ?_⟩
  obtain ⟨hs, _, hf⟩ := h2
  have hidx : xs.zipIdx.Pairwise (fun p q => p.2 < q.2) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp [List.getElem_zipIdx]; omega
  have hq := pairwise_of_filters Prod.fst (fun p q => p.2 < q.2)
    (listSort (ltOf Prod.fst) xs.zipIdx) (fun k => by rw [hf k]; exact hidx.filter _)
  have := hs.and hq
  refine this.imp (fun ⟨ha, hb⟩ => ?_)
  rcases Int.lt_or_eq_of_le ha with h | h
  · exact .inl h
  · exact .inr ⟨h, hb h⟩

theorem stableSort_reverse (kf : α → Int) (xs : List α) :
    (stableSort kf xs.reverse).reverse = stableSort (fun x => -kf x) xs := by
  apply ss_eq_stableSort
  have h := stableSort_spec kf xs.reverse
  refine ⟨?_, fun k => ?_⟩
  · unfold Sorted
    rw [List.pairwise_reverse]
    exact h.1.imp (fun hab => by dsimp only; omega)
  · rw [List.filter_reverse]
    have e : ∀ l : List α, l.filter (fun e => -kf e == k) = l.filter (fun e => kf e == -k) := fun l =>
      List.filter_congr (fun x _ => by
        show (-kf x == k) = (kf x == -k)
        rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; omega)
    rw [e, e, ← h.2 (-k), List.filter_reverse, List.reverse_reverse]

/-- `reverse=True`: the result is the stable sort of the reversed list,
reversed (`listobject.c:3132-3138`, `:3201-3202`), which is the stable sort by
descending key: equal keys keep their original order ("The reverse parameter
still maintains sort stability", Doc/howto/sorting.rst). -/
def ReverseStable : Prop :=
  ∀ (α : Type) (kf : α → Int) (xs : List α),
    listSort (ltOf kf) xs true = (stableSort kf xs.reverse).reverse ∧
    listSort (ltOf kf) xs true = stableSort (fun x => -kf x) xs

theorem reverseStable_proven : ReverseStable := fun _ kf xs =>
  ⟨listSort_rev_eq kf xs, (listSort_rev_eq kf xs).trans (stableSort_reverse kf xs)⟩

theorem ss_congr_key {β : Type} {k1 k2 : β → Int} {L R : List β} (h : ∀ x ∈ L, k1 x = k2 x)
    (hs : SS k1 L R) : SS k2 L R := by
  have hm := hs.2.mem
  refine ⟨?_, fun k => ?_⟩
  · exact List.Pairwise.imp_of_mem (fun {a b} ha hb hab => by
      rw [← h a ((hm a).2 ha), ← h b ((hm b).2 hb)]; exact hab) hs.1
  · have e : ∀ M : List β, (∀ x ∈ M, x ∈ L) → M.filter (fun e => k2 e == k) = M.filter (fun e => k1 e == k) :=
      fun M hM => List.filter_congr (fun x hx => by rw [h x (hM x hx)])
    rw [e L (fun _ h => h), e R (fun x hx => (hm x).2 hx)]
    exact hs.2 k

theorem ss_map_snd {β : Type} (f : β → Int) {L R : List (Int × β)} (hs : SS (fun p => f p.2) L R) :
    SS f (L.map Prod.snd) (R.map Prod.snd) := by
  refine ⟨?_, fun k => ?_⟩
  · unfold Sorted; rw [List.pairwise_map]; exact hs.1
  · rw [List.filter_map, List.filter_map]
    exact congrArg (List.map Prod.snd) (hs.2 k)

/-- `key=f`: the keys are computed once per item and the items are sorted
stably by key; with `reverse=True` stably by descending key (the docstring,
`listobject.c:2958-2959`). -/
def KeySortStable : Prop :=
  ∀ (β : Type) (f : β → Int) (xs : List β) (reverse : Bool),
    listSortKey f (fun a b => decide (a < b)) xs reverse =
      if reverse then stableSort (fun x => -f x) xs else stableSort f xs

theorem keySortStable_proven : KeySortStable := by
  intro β f xs rev
  have hpairs : ∀ L : List (Int × β), (∀ p ∈ L, p.1 = f p.2) →
      (stableSort Prod.fst L).map Prod.snd = stableSort f (L.map Prod.snd) := by
    intro L hL
    apply ss_eq_stableSort
    exact ss_map_snd f (ss_congr_key (fun p hp => hL p hp) (stableSort_spec Prod.fst L))
  have hP : ∀ p ∈ xs.map (fun x => (f x, x)), p.1 = f p.2 := by
    intro p hp; simp at hp; obtain ⟨x, _, rfl⟩ := hp; rfl
  have hsnd : (xs.map (fun x => (f x, x))).map Prod.snd = xs := by
    clear hP hpairs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons, ih]
  unfold listSortKey listSortKeyCnt
  cases rev
  · show (listSort (ltOf Prod.fst) _ false).map Prod.snd = _
    rw [listSort_eq, hpairs _ hP, hsnd]; rfl
  · show (listSort (ltOf Prod.fst) _ true).map Prod.snd = _
    rw [listSort_rev_eq, List.map_reverse, hpairs _ (fun p hp => hP p (by simpa using hp)),
      List.map_reverse, hsnd, stableSort_reverse]
    rfl

/-! ## Goal 3: the type-specialised compare for int keys -/

/-- For all-int keys of every size, the compare the pre-sort check selects
(`unsafe_long_compare` when all keys are compact, `unsafe_object_compare` over
`long_richcompare` otherwise) agrees with `<` on every pair of keys. An
int is compact exactly when `|x| < 2**30`, and then `_PyLong_CompactValue` is
`x`. The hypotheses `x, y ∈ keys` are needed: `unsafe_long_compare` is only sound
for compact values, which the check guarantees for the list's own keys. -/
def LongCompareAgrees : Prop :=
  (∀ x : Int, (PyLong.ofInt x).isCompact = decide (x.natAbs < digitBase)) ∧
  (∀ x : Int, (PyLong.ofInt x).isCompact = true → (PyLong.ofInt x).compactValue = x) ∧
  (∀ x y : Int, longCompare (.ofInt x) (.ofInt y) < 0 ↔ x < y) ∧
  (∀ (keys : List Int) (x y : Int), x ∈ keys → y ∈ keys →
    selectCompare (allCompact keys) x y = decide (x < y))

theorem longCompareAgrees_proven : LongCompareAgrees :=
  ⟨isCompact_iff, compactValue_eq, longCompare_lt, selectCompare_eq⟩

/-- `unsafe_object_compare`, for every result type: when `v`'s type lost the slot, or the
slot answers `NotImplemented`, the answer is `PyObject_RichCompareBool`'s; the slot's
exception propagates; a `bool` is taken as it is; and any other object is decided by
`PyObject_IsTrue`, whose own exception propagates. The result of `__lt__` is an
arbitrary object, not a `bool`. -/
def ObjectCompareSpec : Prop :=
  ∀ (ρ : Type) (rich : Py (RichRes ρ)) (isTrue : ρ → Py Bool) (fallback : Py Bool),
    unsafeObjectCompare false rich isTrue fallback = fallback ∧
    (rich = .ok .notImplemented → unsafeObjectCompare true rich isTrue fallback = fallback) ∧
    (∀ e, rich = .error e → unsafeObjectCompare true rich isTrue fallback = .error e) ∧
    (∀ b, rich = .ok (.bool b) → unsafeObjectCompare true rich isTrue fallback = .ok b) ∧
    (∀ o, rich = .ok (.other o) → unsafeObjectCompare true rich isTrue fallback = isTrue o)

theorem objectCompareSpec_proven : ObjectCompareSpec := by
  intro ρ rich isTrue fallback
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro h; subst h; rfl
  · intro e h; subst h; rfl
  · intro b h; subst h; rfl
  · intro o h; subst h; rfl

end PyLean.ListSort
