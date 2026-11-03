import PyLean.ListSort.FallibleExits

/-!
# Every `goto fail`, at every point of every loop

`SortFailExits` uses a comparison that raises on every call, so it reaches only each function's first
comparison. Here every comparison site is stated for an arbitrary state of its loop and any comparison:
when that comparison raises, the function stops there, passes the exception on and leaves the array as
the C code leaves it. A model that swallowed a later error, or put the rest of a run in the wrong place,
fails the clause for that site.
-/

namespace PyLean.ListSort

open PyLean

variable {α : Type}

/-- The failure clauses of the sort, each for every state of its loop (listobject.c line numbers as in
`Fallible.lean`):

* the binary-search loop (`binarysort`'s `IFLT`, :1914, and the gallops' final search, :2150, :2239)
  returns the error of the probe that raised;
* the gallops' outward loops (:2105, :2125, :2194, :2215) do the same, and `gallop_left`/`gallop_right`
  return any of them (:2158, :2247);
* `binarysort` fails on any pivot with the sorted prefix, that pivot and the rest in place (:1951);
* `count_run`'s ascending scan fails with the slice untouched (:2004-2006);
* `merge_lo`'s straight loop (:2383) and both galloping probes (:2419, :2442) leave
  `merged ++ rest of A ++ rest of B`; `merge_hi`'s (:2521, :2555, :2573) leave
  `rest of A ++ rest of B ++ merged`;
* `merge_at`'s second gallop (:2660-2662) fails with the runs untouched, and whatever `merge_lo` or
  `merge_hi` leaves is what `merge_at` leaves (:2667-2670);
* once a merge has failed, later merges do nothing, and the main loop stops (`goto fail`, :3148-3175);
* `PyList_Sort` (:3241-3244) returns `0` with the sorted list when the sort succeeds. -/
def SortFailSteps : Prop :=
  ∀ (α : Type) (lt : PLt α) (e : PyExc) (test : Nat → MS → Py Bool × MS) (ms ms1 ms2 : MS)
    (fuel lo hi hint maxofs lastofs ofs mg ac bc k n : Nat) (a b : α) (out A A' B' sorted ps : List α),
    (lo < hi → test (lo + (hi - lo) / 2) ms = (.error e, ms1) → binLoopF test (fuel + 1) lo hi ms = (.error e, ms1)) ∧
    (ofs < maxofs → test (hint + ofs) ms = (.error e, ms1) →
      gallopUpF test hint maxofs (fuel + 1) lastofs ofs ms = (.error e, ms1)) ∧
    (ofs < maxofs → test (hint - ofs) ms = (.error e, ms1) →
      gallopDownF test hint maxofs (fuel + 1) lastofs ofs ms = (.error e, ms1)) ∧
    (test hint ms = (.error e, ms1) → gallopCoreF test n hint ms = (.error e, ms1)) ∧
    (test hint ms = (.ok true, ms1) → gallopUpF test hint (n - hint) (n + 1) 0 1 ms1 = (.error e, ms2) →
      gallopCoreF test n hint ms = (.error e, ms2)) ∧
    (test hint ms = (.ok false, ms1) → gallopDownF test hint (hint + 1) (n + 1) 0 1 ms1 = (.error e, ms2) →
      gallopCoreF test n hint ms = (.error e, ms2)) ∧
    (bsInsertF lt sorted a ms = (.error e, ms1) → bsLoopF lt sorted (a :: ps) ms = (sorted ++ a :: ps, ms1, some e)) ∧
    (binLoopF (fun m ms => notF (isltF lt ms a (sorted.getD m a))) (sorted.length + 1) 0 sorted.length ms =
      (.error e, ms1) → bsInsertF lt sorted a ms = (.error e, ms1)) ∧
    (isltF lt ms b a = (.error e, ms1) → ascTakeF lt a (b :: ps) ms = ([], b :: ps, ms1, some e)) ∧
    (isltF lt ms b a = (.error e, ms1) →
      loLoopF lt (fuel + 1) false mg ac bc out (a :: A') (b :: B') ms = (out ++ (a :: A') ++ (b :: B'), ms1, some e)) ∧
    (gallopRightF lt b (fun i => A'.getD i b) A'.length 0 { ms with minGallop := mg - (if mg > 1 then 1 else 0) } =
      (.error e, ms1) →
      loLoopF lt (fuel + 1) true mg ac bc out A' (b :: B') ms = (out ++ A' ++ (b :: B'), ms1, some e)) ∧
    (gallopRightF lt b (fun i => (A.take k ++ a :: A').getD i b) (A.take k ++ a :: A').length 0
        { ms with minGallop := mg - (if mg > 1 then 1 else 0) } = (.ok k, ms1) →
      (A.take k).length = k → ¬ (k ≠ 0 ∧ A'.length + 1 = 1) → B' ≠ [] →
      gallopLeftF lt a (fun i => B'.getD i a) B'.length 0 ms1 = (.error e, ms2) →
      loLoopF lt (fuel + 1) true mg ac bc out (A.take k ++ a :: A') (b :: B') ms =
        (out ++ A.take k ++ [b] ++ (a :: A') ++ B', ms2, some e)) ∧
    (isltF lt ms b a = (.error e, ms1) →
      hiLoopF lt (fuel + 1) false mg ac bc out (a :: A') (b :: B') ms =
        ((a :: A').reverse ++ (b :: B').reverse ++ out, ms1, some e)) ∧
    (gallopRightF lt b (fun i => A'.getD (A'.length - 1 - i) b) A'.length (A'.length - 1)
        { ms with minGallop := mg - (if mg > 1 then 1 else 0) } = (.error e, ms1) →
      hiLoopF lt (fuel + 1) true mg ac bc out A' (b :: B') ms = (A'.reverse ++ (b :: B').reverse ++ out, ms1, some e)) ∧
    (mergeAtArrF lt lo hi n (A, ms, some e) = (A, ms, some e)) ∧
    (∀ (st st' : Sorter α), sortStepF lt n lo st = (st', k, some e) → sortLoopF lt n (fuel + 1) lo st = (st', some e)) ∧
    (∀ (f : α → α → Bool) (l : List α), pyListSortF (pureLt f) (some l) = (.ok (), listSort f l false))

theorem sortFailSteps_proven : SortFailSteps := by
  intro α lt e test ms ms1 ms2 fuel lo hi hint maxofs lastofs ofs mg ac bc k n a b out A A' B' sorted ps
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_,
    fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h1 hk hc hB h2 => ?_, fun h => ?_,
    fun h => ?_, rfl, fun st st' h => ?_, fun f l => ?_⟩
  · simp only [binLoopF, h1, ↓reduceIte, h2]
  · simp only [gallopUpF, h1, ↓reduceIte, h2]
  · simp only [gallopDownF, h1, ↓reduceIte, h2]
  · simp only [gallopCoreF, h]
  · simp only [gallopCoreF, h1, ↓reduceIte, h2]
  · simp only [gallopCoreF, h1, Bool.false_eq_true, ↓reduceIte, h2]
  · simp only [bsLoopF, h]
  · simp only [bsInsertF, h]
  · simp only [ascTakeF, h]
  · simp only [loLoopF, h]
  · simp only [loLoopF, h]
  · simp only [loLoopF, h1, List.drop_left' hk, List.take_left' hk]
    rw [if_neg (show ¬ (k ≠ 0 ∧ (a :: A').length = 1) by simpa using hc),
      if_neg (show ¬ (k ≠ 0 ∧ (a :: A').length = 0) by simp), if_neg hB]
    simp only [h2]
  · simp only [hiLoopF, h]
  · simp only [hiLoopF, h]
  · simp only [sortLoopF, h]
  · simp only [pyListSortF, listSortImplF, listSortCntF_pure, listSort]

/-- The remaining failure clauses, each for every state: `merge_hi`'s galloping `gallop_left` (:2573)
leaves `rest of A ++ rest of B ++ merged` with the B item already copied; `merge_at`'s second gallop
(:2660-2662) fails with the runs untouched, and what `merge_lo`/`merge_hi` leave, error or not, is what
`merge_at` leaves (:2667-2670); `count_run` passes on an error of its ascending scan with the slice
untouched (:2004-2006, :2058-2059), and its descending loop fails on either comparison with the current
equal group not yet reversed (:2031-2041). -/
def SortFailSteps2 : Prop :=
  ∀ (α : Type) (lt : PLt α) (e : PyExc) (ms ms1 ms2 ms3 : MS) (fuel mg ac bc k k0 nb : Nat)
    (a b b0 alast x0 z prev : α) (out T R A B' m t r done grp rest : List α) (er : Option PyExc),
    (gallopRightF lt b (fun i => (T ++ a :: R).getD ((T ++ a :: R).length - 1 - i) b) (T ++ a :: R).length
        ((T ++ a :: R).length - 1) { ms with minGallop := mg - (if mg > 1 then 1 else 0) } = (.ok k0, ms1) →
      (T ++ a :: R).length - k0 = T.length → B'.length ≠ 1 →
      gallopLeftF lt a (fun i => B'.getD (B'.length - 1 - i) a) B'.length (B'.length - 1) ms1 = (.error e, ms2) →
      hiLoopF lt (fuel + 1) true mg ac bc out (T ++ a :: R) (b :: B') ms =
        ((a :: R).reverse ++ B'.reverse ++ b :: (T.reverse ++ out), ms2, some e)) ∧
    (gallopRightF lt b0 (fun i => A.getD i b0) A.length 0 ms = (.ok k, ms1) → (A.drop k).getLast? = some alast →
      gallopLeftF lt alast (fun i => (b0 :: B').getD i alast) (b0 :: B').length ((b0 :: B').length - 1) ms1 =
        (.error e, ms2) →
      mergeAtF lt A (b0 :: B') ms = (A.take k ++ A.drop k ++ b0 :: B', ms2, some e)) ∧
    (gallopRightF lt b0 (fun i => A.getD i b0) A.length 0 ms = (.ok k, ms1) → (A.drop k).getLast? = some alast →
      gallopLeftF lt alast (fun i => (b0 :: B').getD i alast) (b0 :: B').length ((b0 :: B').length - 1) ms1 =
        (.ok nb, ms2) → nb ≠ 0 →
      (if (A.drop k).length ≤ ((b0 :: B').take nb).length then mergeLoF lt (A.drop k) ((b0 :: B').take nb) ms2
        else mergeHiF lt (A.drop k) ((b0 :: B').take nb) ms2) = (m, ms3, er) →
      mergeAtF lt A (b0 :: B') ms = (A.take k ++ m ++ (b0 :: B').drop nb, ms3, er)) ∧
    (ascTakeF lt x0 rest ms = (t, r, ms1, some e) → countRunF lt (x0 :: rest) ms = (0, x0 :: rest, ms1, some e)) ∧
    (isltF lt ms z prev = (.error e, ms1) →
      descLoopF lt done grp prev (z :: rest) ms = (done ++ grp, z :: rest, ms1, some e)) ∧
    (isltF lt ms z prev = (.ok false, ms1) → isltF lt ms1 prev z = (.error e, ms2) →
      descLoopF lt done grp prev (z :: rest) ms = (done ++ grp, z :: rest, ms2, some e))

theorem sortFailSteps2_proven : SortFailSteps2 := by
  intro α lt e ms ms1 ms2 ms3 fuel mg ac bc k k0 nb a b b0 alast x0 z prev out T R A B' m t r done grp rest er
  refine ⟨fun h1 hk hB h2 => ?_, fun h1 hl h2 => ?_, fun h1 hl h2 hn h3 => ?_, fun h => ?_, fun h => ?_,
    fun h1 h2 => ?_⟩
  · simp only [hiLoopF, h1]
    rw [hk, List.drop_left, List.take_left]
    rw [if_neg (by simp), if_neg hB]
    simp only [h2]
  · simp only [mergeAtF, h1, hl, h2]
  · simp only [mergeAtF, h1, hl, h2, hn, ↓reduceIte]
    rw [h3]
  · simp only [countRunF, h]
  · simp only [descLoopF, h]
  · simp only [descLoopF, h1, h2]

end PyLean.ListSort
