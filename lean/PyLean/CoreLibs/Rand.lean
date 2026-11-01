import PyLean.Registry
import PyLean.CoreLibs.Rand.Diff
import PyLean.CoreLibs.Rand.MtProps
import PyLean.CoreLibs.Rand.ExactProps
import PyLean.CoreLibs.Rand.CountsProps
import PyLean.CoreLibs.Rand.SeedProps
import PyLean.CoreLibs.Rand.DistProps
import PyLean.CoreLibs.Rand.SystemProps
import PyLean.CoreLibs.Rand.OpenProps

/-! Registry for the `Rand` area of CoreLibs: Lib/random.py, Modules/_randommodule.c, CPython 3.14.7. -/

namespace PyLean.CoreLibs.Rand

open PyLean.Registry

def entries : List Entry := [
  /- The C core -/
  { id := "rand-genrand-in-bounds", pyFile := "Modules/_randommodule.c"
    pyFns := ["genrand_uint32"]
    statement := "From any valid state genrand_uint32 reads a slot below N after its refill test, keeps N words, and leaves 1 <= index <= N."
    source := "invariant: no out-of-bounds read", status := .proven
    prop := ``GenrandInBounds, thm := some ``genrandInBounds_proven },
  { id := "rand-genrand-twist-recurrence", pyFile := "Modules/_randommodule.c"
    pyFns := ["genrand_uint32"]
    statement := "The in-place refill loops compute the MT19937 recurrence on all N words, including the slots that read already-updated words."
    source := "Matsumoto and Nishimura's definition, as cited at _randommodule.c:3-5", status := .proven
    prop := ``TwistRecurrence, thm := some ``twistRecurrence_proven },
  { id := "rand-random-exact-rational", pyFile := "Modules/_randommodule.c"
    pyFns := ["_random_Random_random_impl"]
    statement := "random() is the exact rational (a*67108864+b)/2**53 from two consecutive words, with numerator below 2**53, in [0, 1)."
    source := "_randommodule.c:168-175; random() docstring", status := .proven
    prop := ``RandomIsExactRational, thm := some ``randomIsExactRational_proven },
  { id := "rand-init-genrand-recurrence", pyFile := "Modules/_randommodule.c"
    pyFns := ["init_genrand"]
    statement := "init_genrand writes mt[0] = s and mt[i] = 1812433253 * (mt[i-1] ^ (mt[i-1] >> 30)) + i for every i, and sets index = N."
    source := "_randommodule.c:195-214", status := .proven
    prop := ``InitGenrandRecurrence, thm := some ``initGenrandRecurrence_proven },
  { id := "rand-init-by-array-complete", pyFile := "Modules/_randommodule.c"
    pyFns := ["init_by_array"]
    statement := "init_by_array's result depends on the key alone, is valid with index = N, and has mt[0] = 0x80000000, so seeding never reaches the all-zero state."
    source := "_randommodule.c:243 comment", status := .proven
    prop := ``InitByArrayComplete, thm := some ``initByArrayComplete_proven },
  { id := "rand-seed-key-words", pyFile := "Modules/_randommodule.c"
    pyFns := ["random_seed"]
    statement := "Splitting a non-negative int into 32-bit words loses nothing: the key reads back as the int, has at least one word, and different ints give different keys."
    source := "Lib/random.py:137 'all bits are used'", status := .proven
    prop := ``SeedKeyWords, thm := some ``seedKeyWords_proven },
  { id := "rand-seed-arg-kinds", pyFile := "Modules/_randommodule.c"
    pyFns := ["random_seed"]
    statement := "random_seed uses abs(n) for an int and for an int subclass (without its __abs__), (size_t)hash(x) for anything else, and an unhashable object raises TypeError."
    source := "_randommodule.c:316-333", status := .proven
    prop := ``SeedArgKinds, thm := some ``seedArgKinds_proven },
  { id := "rand-seed-none", pyFile := "Modules/_randommodule.c"
    pyFns := ["random_seed", "random_seed_urandom", "random_seed_time_pid"]
    statement := "seed(None) uses the OS key when there is one, else the time-and-pid key, and either way gives a valid state; NULL behaves as None."
    source := "_randommodule.c:303-314", status := .proven
    prop := ``SeedNone, thm := some ``seedNone_proven },
  { id := "rand-seed-time-words", pyFile := "Modules/_randommodule.c"
    pyFns := ["random_seed_time_pid"]
    statement := "The two key words made from a PyTime_t, read back as an unsigned integer, equal the time modulo 2**64, for negative times too."
    source := "invariant: no bits of the clock are lost", status := .proven
    prop := ``TimeWordsExact, thm := some ``timeWordsExact_proven },
  { id := "rand-seed-independent-of-state", pyFile := "Modules/_randommodule.c"
    pyFns := ["random_seed", "_random_Random_seed_impl", "random_init_impl"]
    statement := "seed(x) on any instance and _random.Random(x) give the same state or the same exception: no old state survives."
    source := "bpo-42008, test_bug_42008", status := .proven
    prop := ``SeedIndependentOfState, thm := some ``seedIndependentOfState_proven },
  { id := "rand-new-instance-produces-randomness", pyFile := "Modules/_randommodule.c"
    pyFns := ["random_init_impl", "genrand_uint32"]
    statement := "However an instance is created, its stream contains a non-zero word."
    source := "Lib/random.py:103-115 (subclassing Random); behaviour before 3.11", status := .refuted
    prop := ``NewInstanceProducesRandomness, thm := some ``newInstanceProducesRandomness_refuted
    bug := some "corelibs-random-unseeded-subclass"
    notes := "tp_new does not seed since bpo-44260, so a subclass __init__ that skips super().__init__() stays on the all-zero fixed point: random() is 0.0 forever." },
  { id := "rand-c-state-round-trip", pyFile := "Modules/_randommodule.c"
    pyFns := ["_random_Random_getstate_impl", "_random_Random_setstate_impl"]
    statement := "getstate gives N+1 values in [0, 2**32), and setstate restores exactly the state it was read from, at any point of the stream."
    source := "getstate/setstate docstrings", status := .proven
    prop := ``CStateRoundTrip, thm := some ``cStateRoundTrip_proven },
  { id := "rand-c-setstate-validates", pyFile := "Modules/_randommodule.c"
    pyFns := ["_random_Random_setstate_impl"]
    statement := "Anything setstate accepts is a valid state with 0 <= index <= N whose words are the elements truncated to uint32_t; a non-tuple or a wrong size raises."
    source := "bpo-29960, _randommodule.c:463-487", status := .proven
    prop := ``CSetstateValidates, thm := some ``cSetstateValidates_proven
    notes := "Elements up to 2**64 - 1 are accepted and truncated: this describes the behaviour, it is not reported." },
  { id := "rand-getrandbits-bound", pyFile := "Modules/_randommodule.c"
    pyFns := ["_random_Random_getrandbits_impl"]
    statement := "getrandbits(k) < 2**k on all three paths, for every allocator."
    source := "getrandbits docstring: 'an int with k random bits'", status := .proven
    prop := ``GetrandbitsBound, thm := some ``getrandbitsBound_proven },
  { id := "rand-getrandbits-words", pyFile := "Modules/_randommodule.c"
    pyFns := ["_random_Random_getrandbits_impl"]
    statement := "For 0 < k < 2**64: the size check at :521 cannot fire, the k <= 32 fast path equals the word loop, a failed malloc raises MemoryError before any draw, and otherwise exactly (k-1)//32+1 words are used."
    source := "invariant: fast path agrees with slow path", status := .proven
    prop := ``GetrandbitsWords, thm := some ``getrandbitsWords_proven },
  { id := "rand-getrandbits-recursive", pyFile := "Modules/_randommodule.c"
    pyFns := ["_random_Random_getrandbits_impl"]
    statement := "getrandbits(k) for k > 32 is getrandbits(32) + 2**32 * getrandbits(k - 32) on the following state, and getrandbits(32*w) is the next w words, least significant first."
    source := "_randommodule.c:532-533", status := .proven
    prop := ``GetrandbitsRecursive, thm := some ``getrandbitsRecursive_proven },
  { id := "rand-getrandbits-arg-errors", pyFile := "Modules/_randommodule.c"
    pyFns := ["_random_Random_getrandbits_impl"]
    statement := "getrandbits raises ValueError for k < 0, OverflowError for k >= 2**64 and TypeError for a non-index, before any draw; a bool counts as 0 or 1 and k = 0 draws nothing."
    source := "Doc/library/random.rst getrandbits", status := .proven
    prop := ``GetrandbitsArgErrors, thm := some ``getrandbitsArgErrors_proven },
  { id := "rand-random-valid-generator", pyFile := "Lib/random.py"
    pyFns := ["_random_Random_random_impl", "_random_Random_getrandbits_impl"]
    statement := "Random meets the getrandbits contract for every allocator and random() advances the stream by exactly two words."
    source := "Lib/random.py:277-282", status := .proven
    prop := ``MtGenValid, thm := some ``mtGenValid_proven },

  /- `seed`, state and pickling -/
  { id := "rand-init-matches-seed", pyFile := "Lib/random.py"
    pyFns := ["Random.__init__", "Random.seed"]
    statement := "Random(x) gives the same object, or the same exception, as seed(x) on any existing instance."
    source := "Random.__init__ docstring", status := .proven
    prop := ``InitMatchesSeed, thm := some ``initMatchesSeed_proven },
  { id := "rand-seed-str-bytes-agree", pyFile := "Lib/random.py"
    pyFns := ["Random.seed"]
    statement := "Under version 2 a str seeds like its UTF-8 bytes, and bytes like the equal bytearray."
    source := "invariant: str vs bytes", status := .proven
    prop := ``SeedStrBytesAgree, thm := some ``seedStrBytesAgree_proven },
  { id := "rand-seed-v2-all-bits", pyFile := "Lib/random.py"
    pyFns := ["Random.seed"]
    statement := "The int built from a version 2 seed holds the seed in its upper bits and the 512-bit SHA-512 digest below them."
    source := "Lib/random.py:139 'all of the bits are used'", status := .proven
    prop := ``SeedV2AllBits, thm := some ``seedV2AllBits_proven },
  { id := "rand-seed-v1-hash", pyFile := "Lib/random.py"
    pyFns := ["Random.seed"]
    statement := "The version 1 hash is a non-negative 64-bit int, so the x == -1 branch is dead, and str and latin-1 bytes agree."
    source := "Lib/random.py:146-152", status := .proven
    prop := ``SeedV1Hash, thm := some ``seedV1Hash_proven },
  { id := "rand-seed-unsupported-type", pyFile := "Lib/random.py"
    pyFns := ["Random.seed"]
    statement := "Any other seed type raises the documented TypeError for every version, and changes nothing."
    source := "Random.seed docstring; Lib/random.py:169-171", status := .proven
    prop := ``SeedUnsupportedType, thm := some ``seedUnsupportedType_proven },
  { id := "rand-seed-all-or-nothing", pyFile := "Lib/random.py"
    pyFns := ["Random.seed"]
    statement := "seed clears gauss_next when it succeeds and changes nothing when it raises."
    source := "test_seed_when_randomness_source_not_found area; Lib/random.py:173-174", status := .proven
    prop := ``SeedAllOrNothing, thm := some ``seedAllOrNothing_proven },
  { id := "rand-state-round-trip", pyFile := "Lib/random.py"
    pyFns := ["Random.getstate", "Random.setstate"]
    statement := "setstate(getstate()) restores the object exactly from any object, at any point of the stream, including gauss_next."
    source := "Random.getstate docstring", status := .proven
    prop := ``StateRoundTrip, thm := some ``stateRoundTrip_proven },
  { id := "rand-setstate-keeps-core", pyFile := "Lib/random.py"
    pyFns := ["Random.setstate"]
    statement := "A setstate that raises leaves the generator state unchanged."
    source := "bpo-29960", status := .proven
    prop := ``SetstateFailureKeepsCore, thm := some ``setstateFailureKeepsCore_proven },
  { id := "rand-setstate-atomic", pyFile := "Lib/random.py"
    pyFns := ["Random.setstate"]
    statement := "A setstate that raises leaves the whole object unchanged, gauss_next included."
    source := "bpo-29960 (the C part was made atomic for this reason)", status := .refuted
    prop := ``SetstateAtomic, thm := some ``setstateAtomic_refuted
    bug := some "corelibs-random-setstate-gauss-next"
    notes := "Lib/random.py:184 assigns self.gauss_next while unpacking, before the C call validates the state." },
  { id := "rand-setstate-versions", pyFile := "Lib/random.py"
    pyFns := ["Random.setstate", "Random.__setstate__"]
    statement := "A version 2 state equals the version 3 state reduced modulo 2**32; another version raises ValueError naming it; a wrong length fails to unpack; __setstate__ is setstate."
    source := "Lib/random.py:186-200", status := .proven
    prop := ``SetstateVersions, thm := some ``setstateVersions_proven },
  { id := "rand-pickle-round-trip", pyFile := "Lib/random.py"
    pyFns := ["Random.__reduce__", "Random.__getstate__", "Random.__setstate__"]
    statement := "Unpickling what __reduce__ gives restores the object exactly, whatever entropy the fresh instance read."
    source := "pickle support, Lib/random.py:208-220", status := .proven
    prop := ``PickleRoundTrip, thm := some ``pickleRoundTrip_proven },

  /- Integers and sequences -/
  { id := "rand-randbelow-in-range", pyFile := "Lib/random.py"
    pyFns := ["Random._randbelow_with_getrandbits"]
    statement := "For every n > 0 and generator, _randbelow_with_getrandbits(n) returns a value in [0, n), and each draw is below 2*n."
    source := "docstring, Lib/random.py:246", status := .proven
    prop := ``RandbelowInRange, thm := some ``randbelowInRange_proven,
    notes := "Termination of the loop depends on the generator and is not claimed." },
  { id := "rand-randbelow-without-in-range", pyFile := "Lib/random.py"
    pyFns := ["Random._randbelow_without_getrandbits"]
    statement := "For 0 < n < 2**53, _randbelow_without_getrandbits(n) returns a value in [0, n)."
    source := "docstring, Lib/random.py:255", status := .proven
    prop := ``RandbelowWithoutInRange, thm := some ``randbelowWithoutInRange_proven },
  { id := "rand-randbytes-spec", pyFile := "Lib/random.py"
    pyFns := ["Random.randbytes"]
    statement := "randbytes(n) gives n bytes, which are getrandbits(8*n) little-endian from the same draw; to_bytes cannot overflow."
    source := "docstring; Doc/library/random.rst randbytes", status := .proven
    prop := ``RandbytesSpec, thm := some ``randbytesSpec_proven },
  { id := "rand-randrange-is-range-choice", pyFile := "Lib/random.py"
    pyFns := ["Random.randrange"]
    statement := "With L = len(range(a, b, c)): if L > 0, randrange(a, b, c) is one _randbelow(L) and range(a, b, c)[that]; if L = 0 it raises ValueError without a draw."
    source := "docstring, Lib/random.py:297", status := .proven
    prop := ``RandrangeIsRangeChoice, thm := some ``randrangeIsRangeChoice_proven },
  { id := "rand-randrange-bounds", pyFile := "Lib/random.py"
    pyFns := ["Random.randrange"]
    statement := "randrange(a) is in [0, a), and randrange(a, b, c) is a + k*c for a k >= 0 strictly before b in the direction of c, with c != 0."
    source := "docstring", status := .proven
    prop := ``RandrangeBounds, thm := some ``randrangeBounds_proven },
  { id := "rand-randrange-arg-errors", pyFile := "Lib/random.py"
    pyFns := ["Random.randrange"]
    statement := "A non-integer start, a step without stop, and randrange(a) with a <= 0 raise the source's exceptions before any draw."
    source := "Lib/random.py:304-312", status := .proven
    prop := ``RandrangeArgErrors, thm := some ``randrangeArgErrors_proven },
  { id := "rand-randint-spec", pyFile := "Lib/random.py"
    pyFns := ["Random.randint"]
    statement := "randint(a, b) equals randrange(a, b+1) for a <= b and lies in [a, b]; for b < a it raises ValueError without a draw."
    source := "Doc/library/random.rst randint", status := .proven
    prop := ``RandintSpec, thm := some ``randintSpec_proven },
  { id := "rand-choice-spec", pyFile := "Lib/random.py"
    pyFns := ["Random.choice"]
    statement := "choice on an empty sequence raises IndexError before any draw; otherwise the result is seq[j] for j in range, an element for a list."
    source := "docstring", status := .proven
    prop := ``ChoiceSpec, thm := some ``choiceSpec_proven },
  { id := "rand-shuffle-permutation", pyFile := "Lib/random.py"
    pyFns := ["Random.shuffle"]
    statement := "shuffle permutes the list; if _randbelow meets its contract and does not raise, shuffle cannot raise."
    source := "docstring", status := .proven
    prop := ``ShuffleSpec, thm := some ``shuffleSpec_proven },
  { id := "rand-shuffle-immutable", pyFile := "Lib/random.py"
    pyFns := ["Random.shuffle"]
    statement := "An immutable sequence of at least two items raises TypeError after one draw; a shorter one is left alone."
    source := "Lib/random.py:360-363", status := .proven
    prop := ``ShuffleImmutable, thm := some ``shuffleImmutable_proven },
  { id := "rand-sample-distinct-positions", pyFile := "Lib/random.py"
    pyFns := ["Random.sample"]
    statement := "sample(p, k) on a list returns k items from k distinct positions of p, in the pool branch and in the set branch."
    source := "docstring, Lib/random.py:366-376", status := .proven
    prop := ``SampleDistinctPositions, thm := some ``sampleDistinctPositions_proven },
  { id := "rand-sample-arg-errors", pyFile := "Lib/random.py"
    pyFns := ["Random.sample"]
    statement := "A non-sequence, k outside [0, n] and a wrong number of counts raise the source's exceptions before any draw."
    source := "Lib/random.py:418-436", status := .proven
    prop := ``SampleArgErrors, thm := some ``sampleArgErrors_proven },
  { id := "rand-sample-counts-equivalent", pyFile := "Lib/random.py"
    pyFns := ["Random.sample"]
    statement := "For non-negative counts, sample(p, k, counts=c) equals sample(expanded, k) with the same draws, value or exception."
    source := "docstring, Lib/random.py:378-385", status := .proven
    prop := ``SampleCountsEquivalent, thm := some ``sampleCountsEquivalent_proven },
  { id := "rand-sample-rejects-negative-counts", pyFile := "Lib/random.py"
    pyFns := ["Random.sample"]
    statement := "sample raises ValueError when a count is negative."
    source := "the message 'Counts must be non-negative', Lib/random.py:430", status := .refuted
    prop := ``SampleRejectsNegativeCounts, thm := some ``sampleRejectsNegativeCounts_refuted
    bug := some "corelibs-random-sample-negative-counts"
    notes := "Only the total is checked." },

  { id := "rand-choices-spec", pyFile := "Lib/random.py"
    pyFns := ["Random.choices"]
    statement := "choices returns k items (none for k <= 0), each population[j] for some j, using exactly k calls of random(), weighted or not; both weights and cum_weights, or a wrong number of them, raise before any draw."
    source := "docstring, Lib/random.py:461-465; Lib/random.py:483-486", status := .proven
    prop := ``ChoicesSpec, thm := some ``choicesSpec_proven },

  /- Distributions -/
  { id := "rand-one-draw", pyFile := "Lib/random.py"
    pyFns := ["Random.uniform", "Random.triangular", "Random.expovariate", "Random.paretovariate", "Random.weibullvariate"]
    statement := "uniform, triangular, expovariate, paretovariate and weibullvariate use exactly one random() on every path that returns."
    source := "Lib/random.py:277-282", status := .proven
    prop := ``OneDraw, thm := some ``oneDraw_proven },
  { id := "rand-gauss-draws", pyFile := "Lib/random.py"
    pyFns := ["Random.gauss"]
    statement := "gauss draws twice and stores a value when gauss_next is empty, and otherwise draws nothing and empties it."
    source := "Lib/random.py:584-593", status := .proven
    prop := ``GaussDraws, thm := some ``gaussDraws_proven },
  { id := "rand-rejection-draws", pyFile := "Lib/random.py"
    pyFns := ["Random.normalvariate", "Random.lognormvariate", "Random.vonmisesvariate", "Random.gammavariate", "Random.betavariate"]
    statement := "The rejection samplers use a whole number of random() calls of the shape the source fixes for each branch."
    source := "Lib/random.py:277-282", status := .proven
    prop := ``RejectionDraws, thm := some ``rejectionDraws_proven },
  { id := "rand-gamma-checks-first", pyFile := "Lib/random.py"
    pyFns := ["Random.gammavariate"]
    statement := "gammavariate with alpha <= 0 or beta <= 0 raises ValueError before any draw."
    source := "Doc/library/random.rst gammavariate", status := .proven
    prop := ``GammaChecksFirst, thm := some ``gammaChecksFirst_proven },
  { id := "rand-gamma-exits", pyFile := "Lib/random.py"
    pyFns := ["Random.gammavariate", "Random.betavariate"]
    statement := "For all parameters gammavariate raises or leaves its loop for some sequence of draws, under IEEE NaN rules."
    source := "invariant: no hang", status := .refuted
    prop := ``GammaExitsForSomeDraws, thm := some ``gammaExitsForSomeDraws_refuted
    bug := some "corelibs-random-nan-parameters"
    notes := "alpha = nan passes alpha <= 0.0 and no draw leaves the loop." },
  { id := "rand-vonmises-exits", pyFile := "Lib/random.py"
    pyFns := ["Random.vonmisesvariate"]
    statement := "For all parameters vonmisesvariate raises or leaves its loop for some sequence of draws, under IEEE NaN rules."
    source := "invariant: no hang; python/cpython#61343", status := .refuted
    prop := ``VonmisesExitsForSomeDraws, thm := some ``vonmisesExitsForSomeDraws_refuted
    bug := some "corelibs-random-nan-parameters" },
  { id := "rand-binomial-edges", pyFile := "Lib/random.py"
    pyFns := ["Random.binomialvariate"]
    statement := "binomialvariate raises for n < 0, returns 0 and n without a draw for p == 0.0 and p == 1.0, draws once for n == 1, and uses a whole number of draws otherwise."
    source := "docstring, Lib/random.py:811-825", status := .proven
    prop := ``BinomialEdges, thm := some ``binomialEdges_proven },
  { id := "rand-binomial-rejects-nan", pyFile := "Lib/random.py"
    pyFns := ["Random.binomialvariate"]
    statement := "A NaN p raises the ValueError for p outside [0, 1]."
    source := "Lib/random.py:819", status := .refuted
    prop := ``BinomialRejectsNaN, thm := some ``binomialRejectsNaN_refuted
    bug := some "corelibs-random-nan-parameters"
    notes := "AssertionError for n != 1, the value 0 for n == 1." },

  /- `SystemRandom`, subclasses, the command line -/
  { id := "rand-sysrandom-bound", pyFile := "Lib/random.py"
    pyFns := ["SystemRandom.random"]
    statement := "Given the os.urandom contract, the numerator of SystemRandom.random() is below 2**53."
    source := "docstring, Lib/random.py:907", status := .proven
    prop := ``SysRandomBound, thm := some ``sysRandomBound_proven },
  { id := "rand-sysrandom-getrandbits", pyFile := "Lib/random.py"
    pyFns := ["SystemRandom.getrandbits"]
    statement := "SystemRandom.getrandbits(k) < 2**k and k < 0 raises ValueError, so SystemRandom is a valid core generator."
    source := "docstring, Lib/random.py:911", status := .proven
    prop := ``SysGetrandbitsBound, thm := some ``sysGetrandbitsBound_proven },
  { id := "rand-sysrandom-randbytes", pyFile := "Lib/random.py"
    pyFns := ["SystemRandom.randbytes"]
    statement := "SystemRandom.randbytes(n) gives n bytes for n >= 0, and a negative n raises ValueError."
    source := "comment, Lib/random.py:920-921", status := .proven
    prop := ``SysRandbytes, thm := some ``sysRandbytes_proven },
  { id := "rand-sysrandom-no-state", pyFile := "Lib/random.py"
    pyFns := ["SystemRandom.seed", "SystemRandom._notimplemented"]
    statement := "SystemRandom.seed does nothing for any arguments, and getstate and setstate raise NotImplementedError."
    source := "docstrings, Lib/random.py:925-930", status := .proven
    prop := ``SysNoState, thm := some ``sysNoState_proven },
  { id := "rand-init-subclass-pick", pyFile := "Lib/random.py"
    pyFns := ["Random.__init_subclass__"]
    statement := "The first class in the MRO defining one of _randbelow, getrandbits, random decides, in that order within a class; an MRO containing Random always gets an answer."
    source := "docstring, Lib/random.py:226-231", status := .proven
    prop := ``InitSubclassPick, thm := some ``initSubclassPick_proven },
  { id := "rand-main-positional-matches-option", pyFile := "Lib/random.py"
    pyFns := ["main"]
    statement := "python -m random N behaves as python -m random --integer N for every integer N."
    source := "help text, Lib/random.py@3.14.7:1041 'integer: same as --integer'", status := .refuted
    prop := ``MainPositionalMatchesOption, thm := some ``mainPositionalMatchesOption_refuted
    bug := some "corelibs-random-cli-positional-int-fallback"
    notes := "N < 1: the except ValueError meant for int(val) also catches randint's, and float(val) runs on the int." },
  { id := "rand-main-positional-positive", pyFile := "Lib/random.py"
    pyFns := ["main"]
    statement := "For N >= 1 the positional form and --integer are the same call, with a result in [1, N]."
    source := "help text, narrowed as the refuted entry shows", status := .proven
    prop := ``MainPositionalPositive, thm := some ``mainPositionalPositive_proven },
  { id := "rand-main-choices", pyFile := "Lib/random.py"
    pyFns := ["main"]
    statement := "--choice picks from its list, and with no argument main returns the help text."
    source := "Doc/library/random.rst, command-line usage", status := .proven
    prop := ``MainChoices, thm := some ``mainChoices_proven },

  /- Float values: stated, not settled until the Binary64 model is merged. -/
  { id := "rand-randbelow-without-huge", pyFile := "Lib/random.py"
    pyFns := ["Random._randbelow_without_getrandbits"]
    statement := "For n >= 2**53, floor(random() * n) is below n."
    source := "docstring, Lib/random.py:255", status := .open, prop := ``RandbelowWithoutHuge
    notes := "Needs binary64 rounding of the product; the difftest compares it bit for bit." },
  { id := "rand-choices-index-in-range", pyFile := "Lib/random.py"
    pyFns := ["Random.choices"]
    statement := "choices on a non-empty population never raises IndexError: floor(random() * n) < n and the bisect result is at most n - 1."
    source := "Doc/library/random.rst choices", status := .open, prop := ``ChoicesIndexInRange
    notes := "Needs binary64 rounding. The exact part is rand-choices-spec." },
  { id := "rand-uniform-range", pyFile := "Lib/random.py"
    pyFns := ["Random.uniform"]
    statement := "uniform(a, b) lies between a and b, up to rounding, for finite a and b whose difference does not overflow."
    source := "docstring, Lib/random.py:501", status := .open, prop := ``UniformInRange
    notes := "Needs binary64 rounding. python/cpython#134668 records the overflow case as not worth changing." },
  { id := "rand-binomial-range", pyFile := "Lib/random.py"
    pyFns := ["Random.binomialvariate"]
    statement := "binomialvariate(n, p) lies in [0, n] for valid arguments."
    source := "docstring, Lib/random.py:797-799", status := .open, prop := ``BinomialInRange
    notes := "The BTRS branch rejects k outside [0, n], but the BG branch needs the float reasoning on its loop." }
]

end PyLean.CoreLibs.Rand
