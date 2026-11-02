import PyLean.Registry
import PyLean.Itertools.Diff
import PyLean.Itertools.IsliceProps
import PyLean.Itertools.CombProps
import PyLean.Itertools.SimpleProps
import PyLean.Itertools.BatchedProps
import PyLean.Itertools.CountRepeatProps
import PyLean.Itertools.TeeProps
import PyLean.Itertools.GroupbyProps
import PyLean.Itertools.CwrSpec
import PyLean.Itertools.ProductSpec
import PyLean.Itertools.PermSpec
import PyLean.Itertools.Counts
import PyLean.Itertools.Sizeof
import PyLean.Itertools.GroupbyRaising
import PyLean.Itertools.TeeReentry
import PyLean.Itertools.PairwiseReentry
import PyLean.Itertools.CountFloat

/-!
`Modules/itertoolsmodule.c` vs the equivalents in `Doc/library/itertools.rst`, CPython 3.15.2.
-/

namespace PyLean.Itertools

open PyLean.Registry

def entries : List Entry := [
  { id := "itertools-islice-doc-agree", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["islice_new"]
    statement := "For every element type, every input object (not iterable, or raising after its items) and every int (or None) start/stop/step, C islice yields the same items as the doc equivalent, consumes the same number of input items, and raises the same exception class."
    source := "Doc/library/itertools.rst:481-501 (Roughly equivalent to)", status := .refuted
    prop := ``IsliceDocAgree, thm := some ``isliceDocAgree_refuted
    bug := some "itertools-ssize-arguments"
    notes := "islice(it, 2**63): C raises ValueError ('0 <= x <= sys.maxsize'), the doc code slices. Intended (gh-50554 closed as won't fix)." },
  { id := "itertools-islice-doc-agree-ssize", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["islice_new", "islice_next"]
    statement := "The same for Py_ssize_t (or None) arguments."
    source := "Doc/library/itertools.rst:481-501 (Roughly equivalent to)", status := .refuted
    prop := ``IsliceDocAgreeSsize, thm := some ``isliceDocAgreeSsize_refuted
    bug := some "itertools-islice-step-overflow"
    notes := "islice(range(10), 1, None, sys.maxsize) yields [1, 2]: lz->next += step wraps, and with stop=None the overflow branch sets next = stop = -1." },
  { id := "itertools-islice-doc-agree-nowrap", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["islice_new", "islice_next"]
    statement := "For every element type and input object, with Py_ssize_t arguments, and len + step <= sys.maxsize + 1 when stop is None, C islice agrees with the doc equivalent on items, consumption and exception class."
    source := "Doc/library/itertools.rst:481-501 (Roughly equivalent to)", status := .proven
    prop := ``IsliceDocAgreeNoWrap, thm := some ``isliceDocAgreeNoWrap_proven
    notes := "With an int stop the wrap is harmless (next is clamped to stop either way); the extra hypothesis only excludes the refuted case above." },
  { id := "itertools-islice-consumes-max-start-stop", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["islice_next"]
    statement := "For every element type and input iterator (ending or raising after its items), with Py_ssize_t start and stop and a valid step, fully consuming C islice takes min(len, max(start, stop)) input items, whatever the step."
    source := "Doc/library/itertools.rst:503-505", status := .proven
    prop := ``IsliceConsumesMaxStartStop, thm := some ``isliceConsumesMaxStartStop_proven },
  { id := "itertools-islice-step-message", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["islice_new"]
    statement := "islice raises ValueError('Step for islice() must be a positive integer or None.') only for steps that are not positive integers."
    source := "invariant: error message describes the violated constraint", status := .refuted
    prop := ``IsliceStepMessageAccurate, thm := some ``isliceStepMessageAccurate_refuted
    bug := some "itertools-islice-step-message" },
  { id := "itertools-combinatorics-doc-agree", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_combinations_impl"]
    statement := "For every element type, every input object and every int r (and r=None for permutations) the C combinations, combinations_with_replacement and permutations yield the same tuples as their doc equivalents and raise in the same cases."
    source := "Doc/library/itertools.rst:237-259, :275-294, :548-576 (Roughly equivalent to)", status := .refuted
    prop := ``CombDocAgree, thm := some ``combDocAgree_refuted
    bug := some "itertools-doc-combinatorics-negative-r"
    notes := "r = -1: C raises ValueError, the doc code yields [()] (and [('a', 'b')] for permutations)." },
  { id := "itertools-combinatorics-doc-agree-nonneg", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_combinations_impl"]
    statement := "The same for every r >= 0."
    source := "Doc/library/itertools.rst (Roughly equivalent to)", status := .refuted
    prop := ``CombDocAgreeNonneg, thm := some ``combDocAgreeNonneg_refuted
    bug := some "itertools-ssize-arguments"
    notes := "r = 2**63: C OverflowError (Py_ssize_t converter), the doc code returns an empty iterator. Intended." },
  { id := "itertools-combinatorics-doc-agree-ssize", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_combinations_impl"]
    statement := "The same for every 0 <= r <= sys.maxsize."
    source := "Doc/library/itertools.rst:224-228, :536-539 (zero when r > n)", status := .refuted
    prop := ``CombDocAgreeSsize, thm := some ``combDocAgreeSsize_refuted
    bug := some "itertools-combinatorics-r-prealloc"
    notes := "r = sys.maxsize: C allocates r indices before noticing r > n and raises MemoryError; the documented result is empty." },
  { id := "itertools-combinatorics-doc-agree-alloc", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_combinations_impl", "combinations_next", "combinations_next_lock_held", "itertools_combinations_with_replacement_impl", "cwr_next", "cwr_next_lock_held", "itertools_permutations_impl", "permutations_next", "permutations_next_lock_held"]
    statement := "For every r >= 0 whose r-entry index array and r-tuple can be allocated, the C index machines (right-to-left scans, refill loops, the permutations cycles array and its C rotation loop) run in lockstep with the doc generators: same tuples, same end, for every iteration bound."
    source := "Doc/library/itertools.rst (Roughly equivalent to)", status := .proven
    prop := ``CombDocAgreeAlloc, thm := some ``combDocAgreeAlloc_proven
    notes := "Hypotheses: the pool tuple is in memory (type invariant) and memNewOk r ∧ tupleNewOk r (excludes exactly the MemoryError case above; r <= n always satisfies them)." },
  { id := "itertools-simple-doc-agree", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_accumulate_impl", "accumulate_next", "accumulate_next_lock_held", "chain_new", "chain_new_internal", "itertools_chain_from_iterable_impl", "chain_next", "chain_next_lock_held", "itertools_compress_impl", "compress_next", "itertools_cycle_impl", "cycle_next", "itertools_dropwhile_impl", "dropwhile_next", "itertools_takewhile_impl", "takewhile_next", "itertools_filterfalse_impl", "filterfalse_next", "itertools_starmap_impl", "starmap_next", "zip_longest_new", "zip_longest_next", "zip_longest_next_lock_held"]
    statement := "For every element type, every input object (not iterable, or raising after its items) and every callback (which may raise), each of these C iterators, from its constructor on, including the fields it sets (dropwhile's start, takewhile's stop, cycle's saved list), drains to exactly the doc equivalent's items and exception (cycle: the first k items, for every k; starmap: exception class, since the doc's f(*args) words a non-iterable differently), including initial= for accumulate, None for filterfalse, chain.from_iterable, and fillvalue for zip_longest."
    source := "Doc/library/itertools.rst (Roughly equivalent to)", status := .proven
    prop := ``SimpleDocAgree, thm := some ``simpleDocAgree_proven },
  { id := "itertools-constructor-errors", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_cycle_impl", "itertools_accumulate_impl", "itertools_compress_impl", "batched_new_impl", "chain_new", "itertools_chain_from_iterable_impl", "zip_longest_new"]
    statement := "Each constructor that calls iter() on an argument fails with iter()'s own TypeError for a non-iterable, the first such argument winning (compress: data, then selectors); chain() accepts any arguments unchecked until iterated and rejects keywords, unless a subclass defines __init__ (:1916); zip_longest rejects any single keyword but fillvalue."
    source := "invariant: argument checks run at construction, in source order", status := .proven
    prop := ``CtorErrors, thm := some ``ctorErrors_proven },
  { id := "itertools-arg-checks", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["islice_new", "itertools_permutations_impl", "itertools_combinations_impl", "itertools_combinations_with_replacement_impl", "itertools_tee_impl"]
    statement := "islice accepts exactly 2 to 4 positional arguments, and keywords only in a subclass defining __init__; permutations with a non-int r fails with TypeError('Expected int as r') for every input, but only after the iterable was read, so the iterable's error wins. A negative r in Py_ssize_t range to combinations or combinations_with_replacement, or n to tee, raises ValueError('r cannot be negative') or ValueError('n cannot be negative') for every input, without reading it; permutations reads the iterable first, so there the iterable's error wins."
    source := "invariant: argument checks in source order; Modules/clinic/itertoolsmodule.c.h:347-352, :577-582, :656-661", status := .proven
    prop := ``ArgChecks, thm := some ``argChecks_proven },
  { id := "itertools-sizeof", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["product_sizeof", "combinations_sizeof", "cwr_sizeof", "permutations_sizeof"]
    statement := "For every object a constructor accepts, __sizeof__ is the basic size plus 8 bytes per entry of the index arrays the constructor allocated (indices, and cycles for permutations)."
    source := "invariant: __sizeof__ reports the allocation", status := .proven
    prop := ``SizeofReportsArrays, thm := some ``sizeofReportsArrays_proven
    notes := "basic is a parameter: it is tp_basicsize, a platform constant, which the difftest passes in." },
  { id := "itertools-batched-doc-agree", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["batched_new_impl", "batched_next"]
    statement := "For every element type, input object, int n and strict, C batched yields the doc equivalent's batches and raises in the same cases."
    source := "Doc/library/itertools.rst:150-180", status := .refuted
    prop := ``BatchedDocAgree, thm := some ``batchedDocAgree_refuted
    bug := some "itertools-batched-n-prealloc"
    notes := "n = sys.maxsize: PyTuple_New(n) raises MemoryError; the doc code (tuple(islice(it, n))) returns the input as one batch. For n > sys.maxsize both raise." },
  { id := "itertools-batched-doc-agree-alloc", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["batched_new_impl", "batched_next"]
    statement := "For every element type, input object and n whose n-tuple can be allocated (any n < 1 included), C batched and the doc equivalent (using the C islice) yield the same batches and raise in the same cases, strict or not."
    source := "Doc/library/itertools.rst:150-180", status := .proven
    prop := ``BatchedDocAgreeAlloc, thm := some ``batchedDocAgreeAlloc_proven },
  { id := "itertools-count-fast-slow", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_count_impl", "count_next", "count_nextlong", "count_repr"]
    statement := "For all int start and step and every sequence of next()/repr() calls, count returns start + k*step and reprs as count(V) (step 1) or count(V, step): the Py_ssize_t fast mode, the PyLong slow mode and the switch at sys.maxsize are invisible."
    source := "invariant: fast path agrees with slow path", status := .proven
    prop := ``CountFastSlowConsistent, thm := some ``countFastSlowConsistent_proven },
  { id := "itertools-count-consistent", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_count_impl", "count_next", "count_nextlong", "count_repr"]
    statement := "For every number type, start and step that are numbers but not int subclasses, and every sequence of next()/repr() calls, count follows one spec on either path: next adds first, so a failed add raises and changes nothing; repr shows the current value, and the step unless it is an int equal to 1, and a failing repr propagates."
    source := "invariant: fast path agrees with slow path", status := .proven
    prop := ``CountConsistent, thm := some ``countConsistent_proven
    notes := "PyNumber_Add and %R are parameters with no assumptions, except exact ints, which are built in. The hypothesis on int subclasses is real: see itertools-count-doc-agree-total-add." },
  { id := "itertools-count-new-modes", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_count_impl"]
    statement := "count(a, b) raises TypeError('a number is required') exactly for non-numbers, and takes the fast path exactly when both are ints (or omitted), the start fits a Py_ssize_t and the step is 1; otherwise cnt is PY_SSIZE_T_MAX."
    source := "the asserts at Modules/itertoolsmodule.c:3578-3581", status := .proven
    prop := ``CountNewModes, thm := some ``countNewModes_proven },
  { id := "itertools-count-doc-agree", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_count_impl", "count_next", "count_nextlong"]
    statement := "For all numbers, count gives the values and the end of the doc generator."
    source := "Doc/library/itertools.rst:325-331", status := .refuted
    prop := ``CountDocAgreeAll, thm := some ``countDocAgreeAll_refuted
    bug := some "itertools-count-add-before-yield"
    notes := "C adds before returning the current value, the doc generator after yielding it, so a failing add loses a value: count(10**400, 1.0) raises at once, the doc yields 10**400 first." },
  { id := "itertools-count-doc-agree-total-add", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_count_impl", "count_next"]
    statement := "The same, when adding the step cannot fail on the values reached."
    source := "Doc/library/itertools.rst:325-331", status := .refuted
    prop := ``CountDocAgreeTotalAdd, thm := some ``countDocAgreeTotalAdd_refuted
    bug := some "itertools-count-int-subclass-fast-path"
    notes := "The fast path keeps a C integer: count(True) gives the int 1, the doc gives True." },
  { id := "itertools-count-doc-agree-closed", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_count_impl", "count_next", "count_nextlong"]
    statement := "For every number type, when adding the step cannot fail on the values reached and neither argument is an int subclass, count gives the doc generator's values, for every number of calls."
    source := "Doc/library/itertools.rst:325-331", status := .proven
    prop := ``CountDocAgreeClosed, thm := some ``countDocAgreeClosed_proven
    notes := "The two hypotheses exclude exactly the two refuted cases above." },
  { id := "itertools-count-failed-add", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["count_next", "count_nextlong"]
    statement := "For every number type and slow-mode state, when adding the step to the current value fails, next() raises that exception and leaves the state as it was. On the call that leaves fast mode at sys.maxsize, long_cnt keeps PY_SSIZE_T_MAX, otherwise the same, and repr does not change."
    source := "invariant: the sum is stored only after PyNumber_Add succeeded (:3635-3639); the switch to slow mode at :3622-3628", status := .proven
    prop := ``CountFailedAddRaisesFirst, thm := some ``countFailedAddRaisesFirst_proven },
  { id := "itertools-count-float", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_count_impl", "count_next", "count_nextlong"]
    statement := "For all floats x and y and every k, the first k values of count(x, y) are x, x + y, x + y + y, ... by repeated IEEE-754 addition, as the doc generator computes them, with no exception."
    source := "Doc/library/itertools.rst:325-335, Modules/itertoolsmodule.c:3500", status := .proven
    prop := ``CountFloatDocAgree, thm := some ``countFloatDocAgree_proven
    notes := "Over the exact binary64 model, so NaN results are not distinguished by payload." },
  { id := "itertools-repeat-consistent", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["repeat_new", "repeat_next", "repeat_len", "repeat_repr"]
    statement := "For every element type, with times omitted or a Py_ssize_t, after any sequence of next()/repr()/__length_hint__() calls, __length_hint__ is exactly the number of items left (TypeError when endless), repr is repeat(x, left) or repeat(x), and next stops exactly when none are left."
    source := "invariant: length hint and repr track the iterator; length_hint_doc", status := .proven
    prop := ``RepeatConsistent, thm := some ``repeatConsistent_proven },
  { id := "itertools-repeat-doc-agree", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["repeat_new"]
    statement := "For every int times, repeat yields the doc generator's items."
    source := "Doc/library/itertools.rst:624-638", status := .refuted
    prop := ``RepeatDocAgree, thm := some ``repeatDocAgree_refuted
    bug := some "itertools-ssize-arguments"
    notes := "times = 2**63: OverflowError in C, range(times) in the doc code. Intended." },
  { id := "itertools-repeat-doc-agree-ssize", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["repeat_new", "repeat_next"]
    statement := "For times omitted or any Py_ssize_t (negative meaning 0), repeat yields the doc generator's items."
    source := "Doc/library/itertools.rst:624-638", status := .proven
    prop := ``RepeatDocAgreeSsize, thm := some ``repeatDocAgreeSsize_proven },
  { id := "itertools-combinations-spec", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_combinations_impl", "combinations_next", "combinations_next_lock_held"]
    statement := "For every element type and every r >= 0 that can be allocated, combinations(pool, r) yields the items at exactly the positions in a list of math.comb(n, r) strictly increasing r-tuples of positions < n (zero when r > n), and that list is strictly increasing lexicographically, so nothing repeats."
    source := "Doc/library/itertools.rst:220-235", status := .proven
    prop := ``CombinationsSpec, thm := some ``combinationsSpec_proven
    notes := "choose is Pascal's rule, i.e. math.comb. Statements are over positions ('treated as unique based on their position'), so they hold for every pool." },
  { id := "itertools-cwr-spec", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_combinations_with_replacement_impl", "cwr_next", "cwr_next_lock_held"]
    statement := "For every element type and every r >= 0 that can be allocated, combinations_with_replacement(pool, r) yields the items at exactly the positions in a list of comb(n + r - 1, r) non-decreasing r-tuples (for n = 0: one empty tuple if r = 0, else none), strictly increasing lexicographically."
    source := "Doc/library/itertools.rst:262-278", status := .proven
    prop := ``CwrSpec, thm := some ``cwrSpec_proven },
  { id := "itertools-product-spec", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["product_new", "product_next", "product_next_lock_held"]
    statement := "For every element type, and repeat in Py_ssize_t range whose pools fit in memory, product(*args, repeat=repeat) yields the items at exactly the positions in a list of prod(len(p) for p in args)**repeat tuples, one in-range position per pool, strictly increasing lexicographically (the rightmost position advances fastest)."
    source := "Doc/library/itertools.rst:584-600", status := .proven
    prop := ``ProductSpec, thm := some ``productSpec_proven },
  { id := "itertools-product-doc-agree", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["product_new", "product_next", "product_next_lock_held"]
    statement := "For every element type, every input object and every int repeat whose pools fit in memory, the C odometer and the doc's list comprehension give the same tuples in the same order and raise in the same cases."
    source := "Doc/library/itertools.rst:601-617 (roughly equivalent to)", status := .refuted
    prop := ``ProductObjAgree, thm := some ``productObjAgree_refuted
    bug := some "itertools-product-repeat-zero-skips-iterables"
    notes := "product(5, repeat=0): C yields one empty tuple without touching the arguments, the doc code raises TypeError from tuple(5)." },
  { id := "itertools-product-doc-agree-iterable", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["product_new", "product_next", "product_next_lock_held"]
    statement := "The same, when repeat=0 is not combined with arguments that raise when read."
    source := "Doc/library/itertools.rst:601-617 (roughly equivalent to)", status := .proven
    prop := ``ProductDocAgree, thm := some ``productDocAgree_proven
    notes := "Hypotheses: tupleNewOk(len(args) * repeat), both sides keep the pools in memory; and at repeat = 0 the arguments read without error, which excludes exactly the refuted case above. With repeat above the limit, C says OverflowError or MemoryError and the doc code MemoryError; the model compares only that both raise." },
  { id := "itertools-permutations-spec", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_permutations_impl", "permutations_next", "permutations_next_lock_held"]
    statement := "For every element type and r (or None) that can be allocated, permutations(pool, r) yields the items at exactly the positions in a list of math.perm(n, r) tuples of r distinct positions < n (zero when r > n), strictly increasing lexicographically, so nothing repeats."
    source := "Doc/library/itertools.rst:531-551", status := .proven
    prop := ``PermutationsSpec, thm := some ``permutationsSpec_proven
    notes := "Proved by reading the cycles array recursively: a full run of the machine on a suffix of indices visits it in order and restores it, which is why the rotation at cycles[i] == 0 is correct." },
  { id := "itertools-count-formulas", pyFile := "Doc/library/itertools.rst"
    pyFns := []
    statement := "The counts in the three specs above are the documented factorial formulas: n!/(n-r)!, n!/r!/(n-r)! for r <= n, and (n+r-1)!/r!/(n-1)! for n > 0, written without division."
    source := "Doc/library/itertools.rst:224-228, :263-265, :536-539", status := .proven
    prop := ``CountFormulas, thm := some ``countFormulas_proven },
  { id := "itertools-groupby-doc-agree", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_groupby_impl", "groupby_next", "Py_LOCAL_INLINE", "_grouper_next", "_grouper_create"]
    statement := "For every element type, key type with decidable equality, key function and input object that do not raise, and interleaving of next() on the groupby object and on any group it returned (including old groups), the C object returns exactly what the doc's generators return, and nothing crashes."
    source := "Doc/library/itertools.rst:429-461 (roughly equivalent to)", status := .proven
    prop := ``GroupbyDocAgreeR, thm := some ``groupbyDocAgreeR_proven
    notes := "The hypotheses are preconditions, not the interesting case hidden: the doc generators die at their first exception and the C object does not, so there is nothing to compare past one. The failing paths are covered by itertools-groupby-eq-error, itertools-groupby-failed-step and the difftest." },
  { id := "itertools-groupby-no-crash", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_groupby_impl", "groupby_next", "Py_LOCAL_INLINE", "_grouper_next", "_grouper_create"]
    statement := "For every comparison, key function, input, re-entrant __eq__ and sequence of operations, the process survives."
    source := "invariant: Python code cannot crash the interpreter", status := .refuted
    prop := ``GroupbyNoCrash, thm := some ``groupbyNoCrash_refuted
    bug := some "itertools-groupby-eq-reentry-null-currkey"
    notes := "An __eq__ that starts a new group and reads it clears currkey; when it then answers False, groupby_next takes the break and does Py_INCREF(NULL) at :569." },
  { id := "itertools-groupby-no-crash-no-reentry", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["groupby_next", "_grouper_next"]
    statement := "With nothing re-entering, the process survives every sequence of operations, for every comparison, key function and input, including raising ones."
    source := "invariant: the break of groupby_next is only taken with currkey set", status := .proven
    prop := ``GroupbyNoCrashWithoutHooks, thm := some ``groupbyNoCrashWithoutHooks_proven },
  { id := "itertools-groupby-eq-error", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["groupby_next", "_grouper_next"]
    statement := "For every comparison, key function and state, a raising __eq__ propagates out of groupby_next, which leaves every field but currgrouper as it was, and out of _grouper_next, which changes nothing."
    source := "invariant: the rcmp == -1 returns (:560-561, :691-693)", status := .proven
    prop := ``GroupbyEqError, thm := some ``groupbyEqError_proven },
  { id := "itertools-grouper-eq-false", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["_grouper_next"]
    statement := "For every comparison and state, a comparison answering false ends the group and changes nothing."
    source := "invariant: the rcmp == 0 return (:691-693)", status := .proven
    prop := ``GrouperEqFalseStops, thm := some ``grouperEqFalseStops_proven },
  { id := "itertools-groupby-failed-step", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["Py_LOCAL_INLINE"]
    statement := "For every key function and state, a failed groupby_step leaves currkey, currvalue, tgtkey, currgrouper and the groupers as they were, loses at most the one item it took, and reports no exception exactly when the input ended cleanly."
    source := "invariant: currvalue and currkey are assigned only after both calls succeeded (:526-529)", status := .proven
    prop := ``GroupbyFailedStepKeepsState, thm := some ``groupbyFailedStepKeepsState_proven },
  { id := "itertools-grouper-direct", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools__grouper_impl", "_grouper_create", "_grouper_next"]
    statement := "Creating a _grouper directly on a groupby replaces the current grouper, so every grouper made earlier stops at once and leaves the state alone, for every comparison, key function and input."
    source := "invariant: only the current grouper reads the shared input (:637, :673-674)", status := .proven
    prop := ``GrouperDirectInvalidates, thm := some ``grouperDirectInvalidates_proven },
  { id := "itertools-groupby-ctor-error", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_groupby_impl"]
    statement := "groupby on a non-iterable fails in the constructor with iter()'s TypeError."
    source := "invariant: argument checks run at construction", status := .proven
    prop := ``GroupbyCtorError, thm := some ``groupbyCtorError_proven },
  { id := "itertools-tee-doc-agree", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_tee_impl", "tee_next", "teedataobject_newinternal", "teedataobject_jumplink", "teedataobject_getitem", "teedataobject_getitem_lock_held", "tee_fromiterable", "tee_copy", "tee_copy_impl", "itertools__tee_impl"]
    statement := "With an input that does not re-enter, for every element type, every input object (not iterable, or raising after its items), every n whose result tuple fits in memory and every interleaving of next(), tee(), _tee() and __copy__() on the iterators, the C chain of LINKCELLS-sized blocks returns the same results as the doc's linked list and pulls the same number of input items; for n < 0 both raise."
    source := "Doc/library/itertools.rst:686-729 (Roughly equivalent to, flattening)", status := .proven
    prop := ``TeeDocAgreeR, thm := some ``teeDocAgreeR_proven
    notes := "The doc side uses _tee(t) for __copy__, which the doc text defines as the same flattening. Hypotheses: tupleNewOk n, both sides need n objects in memory; and no re-entry, since the doc's pure Python _tee has no guard." },
  { id := "itertools-tee-reentry-guard", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_tee_impl", "tee_next", "teedataobject_getitem", "teedataobject_getitem_lock_held", "tee_fromiterable"]
    statement := "For every state, next() on a tee at the frontier of a block whose pull is in progress raises RuntimeError('cannot re-enter the tee iterator') and changes nothing, and an input that re-enters does reach this, after which the outer next() still delivers its item."
    source := "Doc/library/itertools.rst:751-753, Modules/itertoolsmodule.c:791-795", status := .proven
    prop := ``TeeReentryGuard, thm := some ``teeReentryGuard_proven },
  { id := "itertools-tee-running-balanced", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["tee_next", "teedataobject_getitem", "teedataobject_getitem_lock_held"]
    statement := "For every state, hook and sequence of operations, including raising inputs and hooks that hit the guard, the running flags end as they began, so no later next() gets a spurious RuntimeError."
    source := "invariant: running is cleared before the result of PyIter_Next is looked at (:800-802)", status := .proven
    prop := ``TeeRunningBalanced, thm := some ``teeRunningBalanced_proven },
  { id := "itertools-tee-wrap", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools__tee_impl", "tee_fromiterable", "teedataobject_newinternal"]
    statement := "itertools._tee(x) on an input that is not a tee behaves as tee(x, 1)[0], for every input, hook and sequence of operations, and a non-iterable fails with iter()'s TypeError."
    source := "Modules/itertoolsmodule.c:1089 (Iterator wrapped to make it copyable)", status := .proven
    prop := ``TeeWrapIsTeeOne, thm := some ``teeWrapIsTeeOne_proven },
  { id := "itertools-tee-clear", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["tee_clear", "tee_dealloc"]
    statement := "For references created in any order and callbacks that may raise, destroying a tee runs each callback once, newest first, whether or not the others raised; nothing raises out of it; dataobj and the list end up cleared; and a second tee_clear runs nothing."
    source := "invariant: the Doc/library/weakref.rst callback contract, and Objects/weakrefobject.c:392-399, :1056-1082", status := .proven
    prop := ``TeeClearCallbacks, thm := some ``teeClearCallbacks_proven
    notes := "Proxies are not modelled. A reference dropped before the tee is simply not in the list." },
  { id := "itertools-pairwise-doc-agree", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["pairwise_new_impl", "pairwise_next"]
    statement := "With an input that does not re-enter, for every element type and input object, next() on pairwise gives the doc generator's pairs and its end."
    source := "Doc/library/itertools.rst:518-526 (Roughly equivalent to)", status := .proven
    prop := ``PairwiseDocAgreeR, thm := some ``pairwiseDocAgreeR_proven
    notes := "No re-entry is a precondition: the doc's generator raises ValueError when re-entered." },
  { id := "itertools-pairwise-reentry", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["pairwise_next"]
    statement := "For every hook and state, once po->it is cleared next() stops and changes nothing; if a re-entrant call cleared it while the outer call took its first item, the outer call stops and clears old (:363-367); and an input like map(f, [0, 1, 2]) whose f(0) drains the pairwise object does reach this."
    source := "invariant: po->it is re-read after calling Python code", status := .proven
    prop := ``PairwiseReentryStops, thm := some ``pairwiseReentryStops_proven },
  { id := "itertools-teedataobject-args", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_teedataobject_impl"]
    statement := "_tee_dataobject(it, values, next) succeeds exactly when values has at most LINKCELLS items and next is None, or values has exactly LINKCELLS items and next is another dataobject; otherwise ValueError('Invalid arguments')."
    source := "invariant: a block is linked onward only when full (:889-930)", status := .proven
    prop := ``TeeDataObjectArgs, thm := some ``teeDataObjectArgs_proven }
]

end PyLean.Itertools
