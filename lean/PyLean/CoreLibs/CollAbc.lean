import PyLean.Registry
import PyLean.CoreLibs.CollAbc.Diff
import PyLean.CoreLibs.CollAbc.Props
import PyLean.CoreLibs.CollAbc.PropsSeq
import PyLean.CoreLibs.CollAbc.PropsSet
import PyLean.CoreLibs.CollAbc.PropsMap
import PyLean.CoreLibs.CollAbc.PropsHash

/-! Registry for the `CollAbc` area of CoreLibs: Lib/_collections_abc.py, Lib/collections/abc.py, CPython 3.14.7. -/

namespace PyLean.CoreLibs.CollAbc

open PyLean.Registry

private def file := "Lib/_collections_abc.py"

def entries : List Entry := [
  { id := "corelibs-collabc-check-methods"
    pyFile := file
    pyFns := ["_check_methods"]
    statement := "_check_methods(C, *methods) is True exactly when, for every method, the first definition along C's MRO exists and is not None; otherwise NotImplemented, never False."
    source := "invariant; collections.abc docs on setting a method to None"
    status := .proven
    prop := ``CheckMethodsSpec
    thm := some ``checkMethodsSpec_proven },
  { id := "corelibs-collabc-subclasshooks"
    pyFile := file
    pyFns := ["Hashable.__subclasshook__", "Awaitable.__subclasshook__", "Coroutine.__subclasshook__",
      "AsyncIterable.__subclasshook__", "AsyncIterator.__subclasshook__",
      "AsyncGenerator.__subclasshook__", "Iterable.__subclasshook__", "Iterator.__subclasshook__",
      "Reversible.__subclasshook__", "Generator.__subclasshook__", "Sized.__subclasshook__",
      "Container.__subclasshook__", "Collection.__subclasshook__", "Buffer.__subclasshook__",
      "Callable.__subclasshook__"]
    statement := "A hook answers only for its own ABC; the structural tests respect the hierarchy (sub-ABC implies super-ABC); Collection's test is the conjunction of Sized, Iterable and Container."
    source := "invariant of the ABC hierarchy"
    status := .proven
    prop := ``HookFamily
    thm := some ``hookFamily_proven },
  { id := "corelibs-collabc-abstract-bodies"
    pyFile := file
    pyFns := ["Hashable.__hash__", "Awaitable.__await__", "Coroutine.send", "AsyncIterable.__aiter__",
      "AsyncIterator.__anext__", "AsyncGenerator.asend", "Iterable.__iter__", "Iterator.__next__",
      "Reversible.__reversed__", "Generator.send", "Sized.__len__", "Container.__contains__",
      "Buffer.__buffer__", "Callable.__call__", "MutableSet.add", "MutableSet.discard",
      "Mapping.__getitem__", "MutableMapping.__setitem__", "MutableMapping.__delitem__",
      "Sequence.__getitem__", "MutableSequence.__setitem__", "MutableSequence.__delitem__",
      "MutableSequence.insert"]
    statement := "The abstract bodies, reachable through super(), describe the empty collection, and the mixins built on the abstract __getitem__ see an empty Sequence and an empty Mapping."
    source := "invariant; ABC method tables"
    status := .proven
    prop := ``StubsAreEmpty
    thm := some ``stubsAreEmpty_proven },
  { id := "corelibs-collabc-throw"
    pyFile := file
    pyFns := ["Generator.throw", "Coroutine.throw", "AsyncGenerator.athrow"]
    statement := "throw(typ, val, tb) raises val's class when val is given, else typ's, with tb attached exactly when tb was given."
    source := "docstring of Generator.throw"
    status := .proven
    prop := ``ThrowRaisesGiven
    thm := some ``throwRaisesGiven_proven },
  { id := "corelibs-collabc-close-up-to-value"
    pyFile := file
    pyFns := ["Generator.close", "Coroutine.close", "AsyncGenerator.aclose"]
    statement := "The close mixins raise what the builtin close raises and leave the generator in the same state, up to the returned value."
    source := "twin: generator.close, Objects/genobject.c"
    status := .proven
    prop := ``CloseMatchesBuiltinUpToValue
    thm := some ``closeMatchesBuiltinUpToValue_proven },
  { id := "corelibs-collabc-close-value"
    pyFile := file
    pyFns := ["Generator.close"]
    statement := "The Generator.close mixin returns what the builtin generator.close() returns."
    source := "twin: generator.close docs since 3.13"
    status := .refuted
    prop := ``CloseReturnsSameValue
    thm := some ``closeReturnsSameValue_refuted
    bug := some "corelibs-generator-close-drops-return-value" },
  { id := "corelibs-collabc-next-is-send"
    pyFile := file
    pyFns := ["Generator.__next__", "AsyncGenerator.__anext__", "Iterator.__iter__",
      "AsyncIterator.__aiter__"]
    statement := "next(gen) takes the same step as gen.send(None)."
    source := "docs of generator.__next__"
    status := .proven
    prop := ``NextIsSendNone
    thm := some ``nextIsSendNone_proven
    notes := "Iterator.__iter__ and AsyncIterator.__aiter__ are `return self`; the difftest calls them through the scripted generators." },
  { id := "corelibs-collabc-callable-alias"
    pyFile := file
    pyFns := ["_CallableGenericAlias.__new__", "_CallableGenericAlias.__repr__",
      "_CallableGenericAlias.__reduce__", "_CallableGenericAlias.__getitem__", "_is_param_expr"]
    statement := "Callable[[...], r] flattens to __args__, __reduce__ rebuilds the same alias, repr lists the arguments, and substitution reflattens."
    source := "collections.abc.Callable docs; pickling round-trip"
    status := .proven
    prop := ``CallableRoundTrip
    thm := some ``callableRoundTrip_proven },
  { id := "corelibs-collabc-sequence"
    pyFile := file
    pyFns := ["Sequence.__iter__", "Sequence.__contains__", "Sequence.count", "Sequence.__reversed__"]
    statement := "Sequence.__iter__, __contains__, count and __reversed__ on list primitives equal list's, including == order and which exception escapes."
    source := "collections.abc.Sequence docs; twin with list"
    status := .proven
    prop := ``SeqMixinsMatchList
    thm := some ``seqMixinsMatchList_proven },
  { id := "corelibs-collabc-sequence-index"
    pyFile := file
    pyFns := ["Sequence.index"]
    statement := "Sequence.index(value, start, stop) agrees with list.index for all int bounds, negative, out of range or huge, with stop=None as sys.maxsize."
    source := "docstring; twin with list.index"
    status := .proven
    prop := ``SeqIndexMatchesList
    thm := some ``seqIndexMatchesList_proven },
  { id := "corelibs-collabc-mseq-pop"
    pyFile := file
    pyFns := ["MutableSequence.pop"]
    statement := "MutableSequence.pop(index) on list primitives has list.pop's result, with IndexError on both sides for an empty list or a bad index."
    source := "docstring; twin with list.pop"
    status := .proven
    prop := ``MSeqPopMatchesList
    thm := some ``mseqPopMatchesList_proven },
  { id := "corelibs-collabc-mseq-grow"
    pyFile := file
    pyFns := ["MutableSequence.append", "MutableSequence.extend", "MutableSequence.__iadd__",
      "MutableSequence.clear"]
    statement := "append, extend, __iadd__ (also with values is self) and clear on list primitives give list's results."
    source := "docstrings; twin with list"
    status := .proven
    prop := ``MSeqGrowMatchesList
    thm := some ``mseqGrowMatchesList_proven },
  { id := "corelibs-collabc-mseq-reverse"
    pyFile := file
    pyFns := ["MutableSequence.reverse"]
    statement := "MutableSequence.reverse reverses a list in place, for every length."
    source := "docstring"
    status := .proven
    prop := ``MSeqReverseMatchesList
    thm := some ``mseqReverseMatchesList_proven },
  { id := "corelibs-collabc-mseq-remove"
    pyFile := file
    pyFns := ["MutableSequence.remove"]
    statement := "MutableSequence.remove on list primitives removes the first equal element as list.remove does, with ValueError when absent."
    source := "docstring; twin with list.remove"
    status := .proven
    prop := ``MSeqRemoveMatchesList
    thm := some ``mseqRemoveMatchesList_proven },
  { id := "corelibs-collabc-set-compare"
    pyFile := file
    pyFns := ["Set.__le__", "Set.__lt__", "Set.__gt__", "Set.__ge__", "Set.__eq__"]
    statement := "Set comparisons are subset, proper subset, superset, proper superset and equal elements, and NotImplemented for a non-Set."
    source := "collections.abc.Set docs; twin with set"
    status := .proven
    prop := ``SetCmpMatchBuiltin
    thm := some ``setCmpMatchBuiltin_proven },
  { id := "corelibs-collabc-set-algebra"
    pyFile := file
    pyFns := ["Set.__and__", "Set.__or__", "Set.__sub__", "Set.__rsub__", "Set.__xor__",
      "Set._from_iterable", "KeysView._from_iterable", "ItemsView._from_iterable"]
    statement := "&, |, -, reflected - and ^ with a set or any iterable give the duplicate-free intersection, union, differences and symmetric difference; NotImplemented for a non-iterable."
    source := "collections.abc.Set docs; twin with set"
    status := .proven
    prop := ``SetAlgebraMatchesBuiltin
    thm := some ``setAlgebraMatchesBuiltin_proven },
  { id := "corelibs-collabc-set-isdisjoint"
    pyFile := file
    pyFns := ["Set.isdisjoint"]
    statement := "Set.isdisjoint answers whether no element of the iterable is in the set; a non-iterable raises TypeError."
    source := "docstring"
    status := .proven
    prop := ``SetIsdisjointSpec
    thm := some ``setIsdisjointSpec_proven },
  { id := "corelibs-collabc-mutableset"
    pyFile := file
    pyFns := ["MutableSet.remove", "MutableSet.pop", "MutableSet.clear", "MutableSet.__ior__",
      "MutableSet.__iand__", "MutableSet.__ixor__", "MutableSet.__isub__"]
    statement := "In-place operators, remove, pop and clear on a list-backed set behave like set, including s ^= s and s -= s."
    source := "collections.abc.MutableSet docs; twin with set"
    status := .proven
    prop := ``MSetMatchesBuiltin
    thm := some ``mSetMatchesBuiltin_proven },
  { id := "corelibs-collabc-mapping"
    pyFile := file
    pyFns := ["Mapping.get", "Mapping.__contains__", "Mapping.keys", "Mapping.items", "Mapping.values",
      "MappingView.__init__", "MappingView.__len__", "MappingView.__repr__", "KeysView.__contains__",
      "KeysView.__iter__", "ItemsView.__iter__", "ValuesView.__contains__", "ValuesView.__iter__"]
    statement := "Mapping.get, __contains__ and the views agree with dict and its views on dict primitives."
    source := "collections.abc.Mapping docs; twin with dict"
    status := .proven
    prop := ``MappingMatchesDict
    thm := some ``mappingMatchesDict_proven },
  { id := "corelibs-collabc-itemsview-tuples"
    pyFile := file
    pyFns := ["ItemsView.__contains__"]
    statement := "ItemsView.__contains__ agrees with dict_items.__contains__ on 2-tuples."
    source := "twin: dict_items"
    status := .proven
    prop := ``ItemsContainMatchesOnTuples
    thm := some ``itemsContainMatchesOnTuples_proven },
  { id := "corelibs-collabc-itemsview-contains"
    pyFile := file
    pyFns := ["ItemsView.__contains__"]
    statement := "x in mapping.items() agrees with x in dict.items() for every x."
    source := "twin: dict_items, which returns False for a non-pair"
    status := .refuted
    prop := ``ItemsContainMatchesDictItems
    thm := some ``itemsContainMatchesDictItems_refuted
    bug := some "corelibs-itemsview-contains-unpack" },
  { id := "corelibs-collabc-mapping-eq"
    pyFile := file
    pyFns := ["Mapping.__eq__"]
    statement := "Mapping.__eq__ on dict-backed mappings is the dict comparison of their items, NotImplemented for a non-Mapping."
    source := "collections.abc.Mapping docs"
    status := .proven
    prop := ``MappingEqIsDictEq
    thm := some ``mappingEqIsDictEq_proven },
  { id := "corelibs-collabc-mutablemapping"
    pyFile := file
    pyFns := ["MutableMapping.pop", "MutableMapping.popitem", "MutableMapping.clear",
      "MutableMapping.update", "MutableMapping.setdefault"]
    statement := "MutableMapping.pop, setdefault, update and clear on dict primitives give dict's results and order; popitem removes and returns the first pair, KeyError when empty."
    source := "docstrings; twin with dict"
    status := .proven
    prop := ``MMapMatchesDict
    thm := some ``mMapMatchesDict_proven },
  { id := "corelibs-collabc-set-hash"
    pyFile := file
    pyFns := ["Set._hash"]
    statement := "Set._hash equals the builtin frozenset hash, for every table and all element hashes."
    source := "docstring: We match the algorithm used by the built-in frozenset type"
    status := .proven
    prop := ``SetHashMatchesFrozenset
    thm := some ``setHashMatchesFrozenset_proven },
  { id := "corelibs-collabc-bytestring-meta"
    pyFile := file
    pyFns := ["_DeprecateByteStringMeta.__new__", "_DeprecateByteStringMeta.__instancecheck__"]
    statement := "Creating a class with this metaclass warns unless it is named ByteString; isinstance always warns and keeps ABCMeta's answer."
    source := "deprecation in Doc/whatsnew/3.14"
    status := .proven
    prop := ``ByteStringMeta
    thm := some ``byteStringMeta_proven }
]

end PyLean.CoreLibs.CollAbc
