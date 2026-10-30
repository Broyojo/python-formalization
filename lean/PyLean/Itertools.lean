import PyLean.Registry
import PyLean.Itertools.Diff
import PyLean.Itertools.IsliceProps
import PyLean.Itertools.CombProps
import PyLean.Itertools.SimpleProps
import PyLean.Itertools.BatchedProps
import PyLean.Itertools.CountRepeatProps

/-!
`Modules/itertoolsmodule.c` vs the equivalents in `Doc/library/itertools.rst`, CPython 3.14.7.
-/

namespace PyLean.Itertools

open PyLean.Registry

def entries : List Entry := [
  { id := "itertools-islice-doc-agree", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["islice_new", "islice_next"]
    statement := "For every int (or None) start/stop/step, C islice yields the same items as the doc equivalent, consumes the same number of input items, and raises in the same cases."
    source := "Doc/library/itertools.rst:465-487 (Roughly equivalent to)", status := .refuted
    prop := ``IsliceDocAgree, thm := some ``isliceDocAgree_refuted
    bug := some "itertools-ssize-arguments"
    notes := "islice(it, 2**63): C raises ValueError ('0 <= x <= sys.maxsize'), the doc code slices. Intended (gh-50554 closed as won't fix)." },
  { id := "itertools-islice-doc-agree-ssize", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["islice_new", "islice_next"]
    statement := "For Py_ssize_t (or None) arguments, C islice yields the same items as the doc equivalent, consumes the same input, and raises in the same cases."
    source := "Doc/library/itertools.rst:465-487 (Roughly equivalent to)", status := .refuted
    prop := ``IsliceDocAgreeSsize, thm := some ``isliceDocAgreeSsize_refuted
    bug := some "itertools-islice-step-overflow"
    notes := "islice(range(10), 1, None, sys.maxsize) yields [1, 2]: lz->next += step wraps, and with stop=None the overflow branch sets next = stop = -1." },
  { id := "itertools-islice-doc-agree-nowrap", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["islice_new", "islice_next"]
    statement := "For Py_ssize_t arguments, and len + step <= sys.maxsize + 1 when stop is None, C islice agrees with the doc equivalent on items, consumption and when it raises."
    source := "Doc/library/itertools.rst:465-487 (Roughly equivalent to)", status := .proven
    prop := ``IsliceDocAgreeNoWrap, thm := some ``isliceDocAgreeNoWrap_proven
    notes := "With an int stop the wrap is harmless (next is clamped to stop either way); the extra hypothesis only excludes the refuted case above." },
  { id := "itertools-islice-consumes-max-start-stop", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["islice_next"]
    statement := "With an int stop, fully consuming C islice consumes min(len, max(start, stop)) input items, for every step."
    source := "Doc/library/itertools.rst:485-487", status := .proven
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
    source := "Doc/library/itertools.rst:239-295, :572-598 (Roughly equivalent to)", status := .refuted
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
    source := "Doc/library/itertools.rst:221-224, :530-533 (zero when r > n)", status := .refuted
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
    source := "Doc/library/itertools.rst:139-167", status := .refuted
    prop := ``BatchedDocAgree, thm := some ``batchedDocAgree_refuted
    bug := some "itertools-batched-n-prealloc"
    notes := "n = sys.maxsize: PyTuple_New(n) raises MemoryError; the doc code (tuple(islice(it, n))) returns the input as one batch. For n > sys.maxsize both raise." },
  { id := "itertools-batched-doc-agree-alloc", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["batched_new_impl", "batched_next"]
    statement := "For every n whose n-tuple can be allocated (any n < 1 included), C batched and the doc equivalent (using the C islice) yield the same batches and raise in the same cases, strict or not."
    source := "Doc/library/itertools.rst:139-167", status := .proven
    prop := ``BatchedDocAgreeAlloc, thm := some ``batchedDocAgreeAlloc_proven },
  { id := "itertools-count-fast-slow", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["itertools_count_impl", "count_next", "count_nextlong", "count_repr"]
    statement := "For all int start and step and every sequence of next()/repr() calls, count returns start + k*step and reprs as count(V) (step 1) or count(V, step): the Py_ssize_t fast mode, the PyLong slow mode and the switch at sys.maxsize are invisible."
    source := "invariant: fast path agrees with slow path", status := .proven
    prop := ``CountFastSlowConsistent, thm := some ``countFastSlowConsistent_proven },
  { id := "itertools-count-doc-agree", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["count_next"]
    statement := "For all int start and step, the first k values of count(start, step) are those of the doc generator, for every k."
    source := "Doc/library/itertools.rst:315-334", status := .proven
    prop := ``CountDocAgree, thm := some ``countDocAgree_proven },
  { id := "itertools-repeat-consistent", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["repeat_new", "repeat_next", "repeat_len", "repeat_repr"]
    statement := "For times omitted or a Py_ssize_t, after any sequence of next()/repr()/__length_hint__() calls, __length_hint__ is exactly the number of items left (TypeError when endless), repr is repeat(x, left) or repeat(x), and next stops exactly when none are left."
    source := "invariant: length hint and repr track the iterator; length_hint_doc", status := .proven
    prop := ``RepeatConsistent, thm := some ``repeatConsistent_proven },
  { id := "itertools-repeat-doc-agree", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["repeat_new", "repeat_next"]
    statement := "For every int times, repeat yields the doc generator's items."
    source := "Doc/library/itertools.rst:615-631", status := .refuted
    prop := ``RepeatDocAgree, thm := some ``repeatDocAgree_refuted
    bug := some "itertools-ssize-arguments"
    notes := "times = 2**63: OverflowError in C, range(times) in the doc code. Intended." },
  { id := "itertools-repeat-doc-agree-ssize", pyFile := "Modules/itertoolsmodule.c"
    pyFns := ["repeat_new", "repeat_next"]
    statement := "For times omitted or any Py_ssize_t (negative meaning 0), repeat yields the doc generator's items."
    source := "Doc/library/itertools.rst:615-631", status := .proven
    prop := ``RepeatDocAgreeSsize, thm := some ``repeatDocAgreeSsize_proven }
]

end PyLean.Itertools
