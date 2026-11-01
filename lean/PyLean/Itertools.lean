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

/-!
`Modules/itertoolsmodule.c` vs the equivalents in `Doc/library/itertools.rst`, CPython 3.14.7.
-/

namespace PyLean.Itertools

open PyLean.Registry

def entries : List Entry := [
  { id := "itertools-islice-doc-agree", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["islice_new", "islice_next"]
    statement := "For every int (or None) start/stop/step, C islice yields the same items as the doc equivalent, consumes the same number of input items, and raises in the same cases."
    source := "Doc/library/itertools.rst:476-496 (Roughly equivalent to)", status := .refuted
    prop := ``IsliceDocAgree, thm := some ``isliceDocAgree_refuted
    bug := some "itertools-ssize-arguments"
    notes := "islice(it, 2**63): C raises ValueError ('0 <= x <= sys.maxsize'), the doc code slices. Intended (gh-50554 closed as won't fix)." },
  { id := "itertools-islice-doc-agree-ssize", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["islice_new", "islice_next"]
    statement := "For Py_ssize_t (or None) arguments, C islice yields the same items as the doc equivalent, consumes the same input, and raises in the same cases."
    source := "Doc/library/itertools.rst:476-496 (Roughly equivalent to)", status := .refuted
    prop := ``IsliceDocAgreeSsize, thm := some ``isliceDocAgreeSsize_refuted
    bug := some "itertools-islice-step-overflow"
    notes := "islice(range(10), 1, None, sys.maxsize) yields [1, 2]: lz->next += step wraps, and with stop=None the overflow branch sets next = stop = -1." },
  { id := "itertools-islice-doc-agree-nowrap", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["islice_new", "islice_next"]
    statement := "For Py_ssize_t arguments, and len + step <= sys.maxsize + 1 when stop is None, C islice agrees with the doc equivalent on items, consumption and when it raises."
    source := "Doc/library/itertools.rst:476-496 (Roughly equivalent to)", status := .proven
    prop := ``IsliceDocAgreeNoWrap, thm := some ``isliceDocAgreeNoWrap_proven
    notes := "With an int stop the wrap is harmless (next is clamped to stop either way); the extra hypothesis only excludes the refuted case above." },
  { id := "itertools-islice-consumes-max-start-stop", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["islice_next"]
    statement := "With an int stop, fully consuming C islice consumes min(len, max(start, stop)) input items, for every step."
    source := "Doc/library/itertools.rst:498-500", status := .proven
    prop := ``IsliceConsumesMaxStartStop, thm := some ``isliceConsumesMaxStartStop_proven },
  { id := "itertools-islice-step-message", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["islice_new"]
    statement := "islice raises ValueError('Step for islice() must be a positive integer or None.') only for steps that are not positive integers."
    source := "invariant: error message describes the violated constraint", status := .refuted
    prop := ``IsliceStepMessageAccurate, thm := some ``isliceStepMessageAccurate_refuted
    bug := some "itertools-islice-step-message" },
  { id := "itertools-combinatorics-doc-agree", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["combinations", "combinations_with_replacement", "permutations"]
    statement := "For every int r (and r=None for permutations) the C combinations, combinations_with_replacement and permutations yield the same tuples as their doc equivalents and raise in the same cases."
    source := "Doc/library/itertools.rst:232-254, :275-294, :548-576 (Roughly equivalent to)", status := .refuted
    prop := ``CombDocAgree, thm := some ``combDocAgree_refuted
    bug := some "itertools-doc-combinatorics-negative-r"
    notes := "r = -1: C raises ValueError, the doc code yields [()] (and [('a', 'b')] for permutations)." },
  { id := "itertools-combinatorics-doc-agree-nonneg", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["combinations", "combinations_with_replacement", "permutations"]
    statement := "The same for every r >= 0."
    source := "Doc/library/itertools.rst (Roughly equivalent to)", status := .refuted
    prop := ``CombDocAgreeNonneg, thm := some ``combDocAgreeNonneg_refuted
    bug := some "itertools-ssize-arguments"
    notes := "r = 2**63: C OverflowError (Py_ssize_t converter), the doc code returns an empty iterator. Intended." },
  { id := "itertools-combinatorics-doc-agree-ssize", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_combinations_impl", "itertools_permutations_impl", "itertools_combinations_with_replacement_impl"]
    statement := "The same for every 0 <= r <= sys.maxsize."
    source := "Doc/library/itertools.rst:219-223, :536-539 (zero when r > n)", status := .refuted
    prop := ``CombDocAgreeSsize, thm := some ``combDocAgreeSsize_refuted
    bug := some "itertools-combinatorics-r-prealloc"
    notes := "r = sys.maxsize: C allocates r indices before noticing r > n and raises MemoryError; the documented result is empty." },
  { id := "itertools-combinatorics-doc-agree-alloc", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["combinations_next", "cwr_next", "permutations_next"]
    statement := "For every r >= 0 whose r-entry index array and r-tuple can be allocated, the C index machines (right-to-left scans, refill loops, the permutations cycles array and its C rotation loop) run in lockstep with the doc generators: same tuples, same end, for every iteration bound."
    source := "Doc/library/itertools.rst (Roughly equivalent to)", status := .proven
    prop := ``CombDocAgreeAlloc, thm := some ``combDocAgreeAlloc_proven
    notes := "Hypotheses: the pool tuple is in memory (type invariant) and memNewOk r ∧ tupleNewOk r (excludes exactly the MemoryError case above; r <= n always satisfies them)." },
  { id := "itertools-simple-doc-agree", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["accumulate", "chain", "chain.from_iterable", "compress", "cycle", "dropwhile", "takewhile", "filterfalse", "pairwise", "starmap", "zip_longest"]
    statement := "For all int inputs and pure callbacks, each of these C iterators drains to exactly the doc equivalent's output (cycle: the first k items, for every k), including initial= for accumulate, None for filterfalse and fillvalue for zip_longest."
    source := "Doc/library/itertools.rst (Roughly equivalent to)", status := .proven
    prop := ``SimpleDocAgree, thm := some ``simpleDocAgree_proven },
  { id := "itertools-batched-doc-agree", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["batched_new_impl", "batched_next"]
    statement := "For every int n and strict, C batched yields the doc equivalent's batches and raises in the same cases."
    source := "Doc/library/itertools.rst:153-183", status := .refuted
    prop := ``BatchedDocAgree, thm := some ``batchedDocAgree_refuted
    bug := some "itertools-batched-n-prealloc"
    notes := "n = sys.maxsize: PyTuple_New(n) raises MemoryError; the doc code (tuple(islice(it, n))) returns the input as one batch. For n > sys.maxsize both raise." },
  { id := "itertools-batched-doc-agree-alloc", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["batched_new_impl", "batched_next"]
    statement := "For every n whose n-tuple can be allocated (any n < 1 included), C batched and the doc equivalent (using the C islice) yield the same batches and raise in the same cases, strict or not."
    source := "Doc/library/itertools.rst:153-183", status := .proven
    prop := ``BatchedDocAgreeAlloc, thm := some ``batchedDocAgreeAlloc_proven },
  { id := "itertools-count-fast-slow", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_count_impl", "count_next", "count_nextlong", "count_repr"]
    statement := "For all int start and step and every sequence of next()/repr() calls, count returns start + k*step and reprs as count(V) (step 1) or count(V, step): the Py_ssize_t fast mode, the PyLong slow mode and the switch at sys.maxsize are invisible."
    source := "invariant: fast path agrees with slow path", status := .proven
    prop := ``CountFastSlowConsistent, thm := some ``countFastSlowConsistent_proven },
  { id := "itertools-count-doc-agree", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["count_next"]
    statement := "For all int start and step, the first k values of count(start, step) are those of the doc generator, for every k."
    source := "Doc/library/itertools.rst:313-326", status := .proven
    prop := ``CountDocAgree, thm := some ``countDocAgree_proven },
  { id := "itertools-repeat-consistent", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["repeat_new", "repeat_next", "repeat_len", "repeat_repr"]
    statement := "For times omitted or a Py_ssize_t, after any sequence of next()/repr()/__length_hint__() calls, __length_hint__ is exactly the number of items left (TypeError when endless), repr is repeat(x, left) or repeat(x), and next stops exactly when none are left."
    source := "invariant: length hint and repr track the iterator; length_hint_doc", status := .proven
    prop := ``RepeatConsistent, thm := some ``repeatConsistent_proven },
  { id := "itertools-repeat-doc-agree", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["repeat_new", "repeat_next"]
    statement := "For every int times, repeat yields the doc generator's items."
    source := "Doc/library/itertools.rst:619-633", status := .refuted
    prop := ``RepeatDocAgree, thm := some ``repeatDocAgree_refuted
    bug := some "itertools-ssize-arguments"
    notes := "times = 2**63: OverflowError in C, range(times) in the doc code. Intended." },
  { id := "itertools-repeat-doc-agree-ssize", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["repeat_new", "repeat_next"]
    statement := "For times omitted or any Py_ssize_t (negative meaning 0), repeat yields the doc generator's items."
    source := "Doc/library/itertools.rst:619-633", status := .proven
    prop := ``RepeatDocAgreeSsize, thm := some ``repeatDocAgreeSsize_proven },
  { id := "itertools-combinations-spec", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["combinations_next"]
    statement := "For every r >= 0 that can be allocated, combinations(pool, r) yields the items at exactly the positions in a list of math.comb(n, r) strictly increasing r-tuples of positions < n (zero when r > n), and that list is strictly increasing lexicographically, so nothing repeats."
    source := "Doc/library/itertools.rst:215-230", status := .proven
    prop := ``CombinationsSpec, thm := some ``combinationsSpec_proven
    notes := "choose is Pascal's rule, i.e. math.comb. Statements are over positions ('treated as unique based on their position'), so they hold for every pool." },
  { id := "itertools-cwr-spec", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["cwr_next"]
    statement := "For every r >= 0 that can be allocated, combinations_with_replacement(pool, r) yields the items at exactly the positions in a list of comb(n + r - 1, r) non-decreasing r-tuples (for n = 0: one empty tuple if r = 0, else none), strictly increasing lexicographically."
    source := "Doc/library/itertools.rst:257-273", status := .proven
    prop := ``CwrSpec, thm := some ``cwrSpec_proven },
  { id := "itertools-product-spec", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["product_new", "product_next"]
    statement := "For repeat in Py_ssize_t range whose pools fit in memory, product(*args, repeat=repeat) yields the items at exactly the positions in a list of prod(len(p) for p in args)**repeat tuples, one in-range position per pool, strictly increasing lexicographically (the rightmost position advances fastest)."
    source := "Doc/library/itertools.rst:579-595", status := .proven
    prop := ``ProductSpec, thm := some ``productSpec_proven },
  { id := "itertools-product-doc-agree", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["product_new", "product_next"]
    statement := "For every int repeat (raising in both for negative and above sys.maxsize) whose pools fit in memory, the C odometer and the doc's list comprehension give the same tuples in the same order."
    source := "Doc/library/itertools.rst:596-612 (roughly equivalent to)", status := .proven
    prop := ``ProductDocAgree, thm := some ``productDocAgree_proven
    notes := "Hypothesis tupleNewOk(len(args) * repeat): both sides keep the pools in memory. With repeat above that, C says OverflowError or MemoryError and the doc code MemoryError; model only compares raising, and the hypothesis keeps the model's malloc limit out of the statement." },
  { id := "itertools-permutations-spec", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["permutations_next"]
    statement := "For r (or None) that can be allocated, permutations(pool, r) yields the items at exactly the positions in a list of math.perm(n, r) tuples of r distinct positions < n (zero when r > n), strictly increasing lexicographically, so nothing repeats."
    source := "Doc/library/itertools.rst:526-546", status := .proven
    prop := ``PermutationsSpec, thm := some ``permutationsSpec_proven
    notes := "Proved by reading the cycles array recursively: a full run of the machine on a suffix of indices visits it in order and restores it, which is why the rotation at cycles[i] == 0 is correct." },
  { id := "itertools-count-formulas", pyFile := "Doc/library/itertools.rst"
    pyFns := ["combinations", "combinations_with_replacement", "permutations"]
    statement := "The counts in the three specs above are the documented factorial formulas: n!/(n-r)!, n!/r!/(n-r)! for r <= n, and (n+r-1)!/r!/(n-1)! for n > 0, written without division."
    source := "Doc/library/itertools.rst:219-223, :263-265, :536-539", status := .proven
    prop := ``CountFormulas, thm := some ``countFormulas_proven },
  { id := "itertools-groupby-doc-agree", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["groupby_next", "groupby_step", "_grouper_next"]
    statement := "For every key function, input and interleaving of next() on the groupby object and on any group it returned (including old groups), the C object returns exactly what the doc's generators return."
    source := "Doc/library/itertools.rst:424-456 (roughly equivalent to)", status := .proven
    prop := ``GroupbyDocAgree, thm := some ``groupbyDocAgree_proven },
  { id := "itertools-tee-doc-agree", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_tee_impl", "tee_next", "teedataobject_jumplink", "teedataobject_getitem_lock_held", "tee_copy_impl"]
    statement := "For every n whose result tuple fits in memory and every interleaving of next(), tee() and __copy__() on the iterators, the C chain of LINKCELLS-sized blocks returns the same results as the doc's linked list and pulls the same number of input items; for n < 0 both raise."
    source := "Doc/library/itertools.rst:681-724 (Roughly equivalent to, flattening)", status := .proven
    prop := ``TeeDocAgree, thm := some ``teeDocAgree_proven
    notes := "The doc side uses _tee(t) for __copy__, which the doc text defines as the same flattening. Hypothesis tupleNewOk n: both sides need n objects in memory." }
]

end PyLean.Itertools
