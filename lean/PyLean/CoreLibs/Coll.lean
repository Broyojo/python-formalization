import PyLean.Registry
import PyLean.CoreLibs.Coll.Diff
import PyLean.CoreLibs.Coll.CounterProps5
import PyLean.CoreLibs.Coll.ChainMapGProps
import PyLean.CoreLibs.Coll.UserDictGProps
import PyLean.CoreLibs.Coll.NamedtupleP
import PyLean.CoreLibs.Coll.UserListGProps
import PyLean.CoreLibs.Coll.UserStringG
import PyLean.CoreLibs.Coll.UserDictProps
import PyLean.CoreLibs.Coll.UserListProps
import PyLean.CoreLibs.Coll.UserStringProps
import PyLean.CoreLibs.Coll.NamedtupleProps

/-! Registry for the `Coll` area of CoreLibs: Lib/collections/__init__.py (everything except OrderedDict), CPython 3.15.2. -/

namespace PyLean.CoreLibs.Coll

open PyLean.Registry

private def file : String := "Lib/collections/__init__.py"

def counterEntries : List Entry := [
  { id := "coll-count-elements-twins", pyFile := file, pyFns := ["_count_elements"]
    statement := "The C _count_elements and the Python twin leave the same dict and raise the same exception for every target and iterable. False: an instance attribute get is seen by mapping.get but not by the C fast-path test, Counter() with c.get set stores 11 in Python and 1 in C."
    source := "invariant: C and Python twins; Lib/collections/__init__.py:540-549, Modules/_collectionsmodule.c:2563-2617"
    status := .refuted, prop := ``CountElementsTwins, thm := some ``countElementsTwins_refuted
    bug := some "corelibs-count-elements-twins" },
  { id := "coll-count-elements-twins-hashable", pyFile := file, pyFns := ["_count_elements"]
    statement := "Without an instance get, the twins agree. False: for an unhashable element the C fast path raises the bare hash TypeError, the Python twin dict.get's 'cannot use ... as a dict key' TypeError."
    source := "invariant: C and Python twins; Modules/_collectionsmodule.c:2591-2594, Objects/dictobject.c:2442-2460"
    status := .refuted, prop := ``CountElementsTwinsHashable, thm := some ``countElementsTwinsHashable_refuted
    bug := some "corelibs-count-elements-twins" },
  { id := "coll-count-elements-twins-narrow", pyFile := file, pyFns := ["_count_elements"]
    statement := "With no instance get and keys whose __hash__ never raises a bare TypeError, the C function (fast or slow path, overridden get/__setitem__ free to raise) and the Python one leave the same dict and raise the same exception, partial updates included, for any count type with 0 + 1 == 1."
    source := "narrowing of coll-count-elements-twins"
    status := .proven, prop := ``CountElementsTwinsNarrow, thm := some ``countElementsTwinsNarrow_proven },
  { id := "coll-counter-count-iter-int", pyFile := file
    pyFns := ["Counter.__init__", "Counter.update", "Counter.subtract", "_count_elements"]
    statement := "On ints, update(iterable) adds each element's number of occurrences, appends new keys in first-seen order and raises what the iterator raised keeping the counts before it; subtract lowers the same counts, so it undoes update; Counter(iterable) is the update of an empty counter or the exception."
    source := "docstrings, Lib/collections/__init__.py:606-615, :678-688, :712-725"
    status := .proven, prop := ``CountIterInt, thm := some ``countIterInt_proven },
  { id := "coll-counter-update-fast-slow", pyFile := file, pyFns := ["Counter.update"]
    statement := "On an empty counter, the dict.update fast path and the general count + self_get(elem, 0) loop leave the same items for every Mapping whose items() agrees with its storage or keys()/[] and every count type with x + 0 == x."
    source := "invariant: fast and slow path, Lib/collections/__init__.py:698-705"
    status := .proven, prop := ``UpdateFastSlow, thm := some ``updateFastSlow_proven },
  { id := "coll-counter-copy-reduce", pyFile := file, pyFns := ["Counter.copy", "Counter.__reduce__"]
    statement := "copy() is a new object of self's class with self's items in order; __reduce__ is (self.__class__, (d,)) for a new plain dict d of the items, and the class rebuilds them from d."
    source := "docstring 'Return a shallow copy.', Lib/collections/__init__.py:739; pickle protocol"
    status := .proven, prop := ``CopyReduce, thm := some ``copyReduce_proven },
  { id := "coll-counter-delitem", pyFile := file, pyFns := ["Counter.__delitem__"]
    statement := "del c[e] removes a hashable e, and leaves the counter unchanged on an absent e where dict.__delitem__ raises KeyError; an unhashable e raises exactly the dict operation's exception."
    source := "docstring, Lib/collections/__init__.py:746"
    status := .proven, prop := ``DelitemGuard, thm := some ``delitemGuard_proven },
  { id := "coll-counter-most-common", pyFile := file, pyFns := ["Counter.most_common"]
    statement := "For counts ordered by a strict weak order and a correct stable list.sort, most_common() is the items in non-increasing count order with ties in insertion order, and most_common(n), n >= 0, through every nlargest path, is its first n items."
    source := "docstring, Lib/collections/__init__.py:629-630; Doc/library/collections.rst"
    status := .proven, prop := ``MostCommonSorted, thm := some ``mostCommonSorted_proven },
  { id := "coll-counter-most-common-neg", pyFile := file, pyFns := ["Counter.most_common"]
    statement := "most_common(n) for n < 0 is [] for every count type, no count being compared."
    source := "invariant; Lib/heapq.py:537-593"
    status := .proven, prop := ``MostCommonNeg, thm := some ``mostCommonNeg_proven },
  { id := "coll-counter-repr", pyFile := file, pyFns := ["Counter.__repr__"]
    statement := "repr prints Cls() when empty, the items in most_common() order for ordered counts, and, when every < raises, the items in insertion order if that is a TypeError and the exception otherwise."
    source := "comments, Lib/collections/__init__.py:754, :757"
    status := .proven, prop := ``ReprOrders, thm := some ``reprOrders_proven },
  { id := "coll-counter-elements", pyFile := file, pyFns := ["Counter.elements"]
    statement := "elements() yields each key max(0, n) times in insertion order; it yields the elements before the first count whose __index__ raises or overflows Py_ssize_t, then raises."
    source := "docstring, Lib/collections/__init__.py:643-658"
    status := .proven, prop := ``ElementsLazy, thm := some ``elementsLazy_proven },
  { id := "coll-counter-compare-pointwise", pyFile := file
    pyFns := ["Counter.__eq__", "Counter.__ne__", "Counter.__le__", "Counter.__lt__", "Counter.__ge__", "Counter.__gt__"]
    statement := "For any pure ==, <=, >= on counts, the six comparisons test every key of both counters with missing counts as zero, < and > add !=, and each returns NotImplemented exactly for a non-Counter operand."
    source := "docstrings, Lib/collections/__init__.py:800-830"
    status := .proven, prop := ``ComparePointwise, thm := some ``comparePointwise_proven },
  { id := "coll-counter-compare-raises", pyFile := file, pyFns := ["Counter.__eq__", "Counter.__le__", "Counter.__ge__"]
    statement := "If comparing some key's counts raises and no earlier key compared false, ==, <= and >= raise."
    source := "invariant"
    status := .proven, prop := ``CompareRaises, thm := some ``compareRaises_proven },
  { id := "coll-counter-ops-pointwise", pyFile := file
    pyFns := ["Counter.__add__", "Counter.__sub__", "Counter.__or__", "Counter.__and__"]
    statement := "For any pure +, -, <, > on counts, +, -, | and & store a's keys with the combined count when it is > 0, then b's keys not in a under the operator's test, in that order, and return NotImplemented for a non-Counter operand."
    source := "docstrings and comments, Lib/collections/__init__.py:765-772, :836-908"
    status := .proven, prop := ``OperatorsPointwise, thm := some ``operatorsPointwise_proven },
  { id := "coll-counter-unary", pyFile := file, pyFns := ["Counter.__pos__", "Counter.__neg__"]
    statement := "-c is Counter() - c for every count type, result and exception alike; +c is c + Counter() when x + 0 is x."
    source := "docstrings, Lib/collections/__init__.py:938, :946-947"
    status := .proven, prop := ``UnaryAsBinary, thm := some ``unaryAsBinary_proven },
  { id := "coll-counter-keep-positive", pyFile := file, pyFns := ["Counter._keep_positive", "Counter.__pos__"]
    statement := "For any pure > on counts (NaN-like included), _keep_positive leaves exactly the items with count > 0, in order, the items +c returns."
    source := "docstrings, Lib/collections/__init__.py:938, :957"
    status := .proven, prop := ``KeepPositiveFilters, thm := some ``keepPositiveFilters_proven },
  { id := "coll-counter-inplace-operands", pyFile := file
    pyFns := ["Counter.__iadd__", "Counter.__isub__", "Counter.__ior__", "Counter.__iand__"]
    statement := "+=, -=, |= read only other.items(): a dict and a Counter with the same items agree, and a raising .items() leaves self unchanged; &= reads other[elem]: Counter() &= 5 succeeds and a dict missing the first key raises its KeyError with self unchanged."
    source := "invariant; Lib/collections/__init__.py:972, :985, :998, :1013-1014"
    status := .proven, prop := ``InplaceOperands, thm := some ``inplaceOperands_proven },
  { id := "coll-counter-update-mapping-kw", pyFile := file
    pyFns := ["Counter.update", "Counter.subtract", "Counter.__init__"]
    statement := "For any pure + and - on counts, update(L) on a non-empty counter stores L[k] + self.get(k, 0) for L's keys (dict.update's replacement fails), subtract(L) stores self.get(k, 0) - L[k], the keywords are applied after the positional argument by the same branch, Counter(**kw) holds kw, Counter(L) holds L, and Counter(L, **kw) adds kw to L."
    source := "docstrings, Lib/collections/__init__.py:606-615, :678, :712-714"
    status := .proven, prop := ``UpdateMappingKw, thm := some ``updateMappingKw_proven },
  { id := "coll-counter-inplace-arith", pyFile := file
    pyFns := ["Counter.__iadd__", "Counter.__isub__", "Counter.__ior__", "Counter.__iand__"]
    statement := "For any pure +=, -=, <, > on counts, a += b leaves a[k] += b[k] at b's keys and a[k] elsewhere, -= likewise, |= takes b[k] where b[k] > a[k], &= takes b[k] (0 when missing) where b[k] < a[k], each keeping only counts > 0, without raising."
    source := "docstrings, Lib/collections/__init__.py:964-1011"
    status := .proven, prop := ``InplaceArith, thm := some ``inplaceArith_proven },
  { id := "coll-counter-total", pyFile := file, pyFns := []
    statement := "total() is sum(self.values()) for every count type."
    source := "docstring 'Sum of the counts', Lib/collections/__init__.py:625"
    status := .open, prop := ``TotalTracksUpdate
    notes := "Open: needs a model of builtin sum (Python/bltinmodule.c builtin_sum_impl, with its int and compensated float fast paths); the Int fold it had was withdrawn." },
  { id := "coll-counter-fromkeys", pyFile := file, pyFns := []
    statement := "Counter.fromkeys raises NotImplementedError for every input."
    source := "Doc/library/collections.rst, Counter.fromkeys; Lib/collections/__init__.py:665-675"
    status := .proven, prop := ``FromkeysUndefined, thm := some ``fromkeysUndefined_proven }
]

def chainMapEntries : List Entry := [
  { id := "coll-chainmap-flat-view", pyFile := file
    pyFns := ["ChainMap.__missing__", "ChainMap.get", "ChainMap.__len__", "ChainMap.__iter__",
      "ChainMap.__contains__", "ChainMap.__bool__"]
    statement := "Subscript, get, in, len, iter and bool on a ChainMap agree with the flat dict built by updating from the last map to the first."
    source := "Doc/library/collections.rst, ChainMap"
    status := .proven, prop := ``ChainMapFlatView, thm := some ``chainMapFlatView_proven },
  { id := "coll-chainmap-writes-first", pyFile := file
    pyFns := ["ChainMap.__setitem__", "ChainMap.__delitem__", "ChainMap.popitem", "ChainMap.pop"]
    statement := "Writes and deletions change maps[0] only, their KeyError (whose str is the real repr of the message) is decided by maps[0] alone, and a key removed from maps[0] then reads from the later maps."
    source := "Doc/library/collections.rst, ChainMap: 'writes, updates, and deletions only operate on the first mapping'"
    status := .proven, prop := ``ChainMapWritesFirst, thm := some ``chainMapWritesFirst_proven },
  { id := "coll-chainmap-union-flat", pyFile := file
    pyFns := ["ChainMap.__ror__"]
    statement := "cm | o reads as dict(cm) | o with the tail maps kept, cm |= o likewise, o | cm is the one-map o | dict(cm), copy reads the same, items and order, and non-mappings get NotImplemented."
    source := "PEP 584; Lib/collections/__init__.py:1151-1168"
    status := .proven, prop := ``ChainMapUnionFlat, thm := some ``chainMapUnionFlat_proven },
  { id := "coll-chainmap-child-parents", pyFile := file
    pyFns := ["ChainMap.new_child", "ChainMap.parents"]
    statement := "__init__ always leaves at least one map, new_child and parents are inverse on the map list, and fromkeys reads like dict.fromkeys."
    source := "docstrings and comment, Lib/collections/__init__.py:1055-1059, :1099, :1109-1121"
    status := .proven, prop := ``ChainMapChildParents, thm := some ``chainMapChildParents_proven },
  { id := "coll-chainmap-repr", pyFile := file, pyFns := []
    statement := "repr shows the maps in order, so new_child prepends the child's repr, and ChainMap() prints its empty dict."
    source := "invariant; Lib/collections/__init__.py:1093-1095"
    status := .proven, prop := ``ChainMapRepr, thm := some ``chainMapRepr_proven },
  { id := "coll-chainmap-init", pyFile := file, pyFns := ["ChainMap.__init__"]
    statement := "ChainMap() has exactly the one map {}; with arguments, maps is their list."
    source := "docstring, Lib/collections/__init__.py:1055-1057"
    status := .proven, prop := ``ChainMapInit, thm := some ``chainMapInit_proven },
  { id := "coll-chainmap-getitem-any", pyFile := file, pyFns := ["ChainMap.__getitem__"]
    statement := "__getitem__ asks each mapping's [] in turn: on dicts it is the flat lookup; a map answering (a defaultdict for a key it lacks, while `in` says no) wins; a KeyError or subclass moves on; any other exception propagates."
    source := "Doc/library/collections.rst, ChainMap; comment, Lib/collections/__init__.py:1067"
    status := .proven, prop := ``ChainMapGetitemAny, thm := some ``chainMapGetitemAny_proven },
  { id := "coll-chainmap-repr-guard", pyFile := file, pyFns := ["ChainMap.__repr__"]
    statement := "repr prints Cls(r1, r2, ...) from the maps' reprs (cmRepr on dicts), a ChainMap holding itself prints ... in its place, and a raising map repr raises."
    source := "Lib/collections/__init__.py:1093-1095; Lib/reprlib.py:9-24"
    status := .proven, prop := ``ChainMapReprGuard, thm := some ``chainMapReprGuard_proven },
  { id := "coll-chainmap-fromkeys", pyFile := file, pyFns := ["ChainMap.fromkeys"]
    statement := "ChainMap.fromkeys(xs, v) has exactly the one map dict.fromkeys(xs, v); an exception from the iterable propagates."
    source := "docstring, Lib/collections/__init__.py:1099"
    status := .proven, prop := ``ChainMapFromkeys, thm := some ``chainMapFromkeys_proven },
  { id := "coll-chainmap-objects", pyFile := file
    pyFns := ["ChainMap.copy", "ChainMap.__or__", "ChainMap.__ior__", "ChainMap.clear"]
    statement := "copy() is a new ChainMap with a new copy of maps[0] and maps[1:]'s own objects; cm | o puts maps[0] | o in that new dict and leaves self's maps[0] alone, NotImplemented for a non-Mapping, and raises (discarding the copy) when o fails; cm |= o returns self with maps[0] updated in place and maps[1:] untouched, a non-iterable raising with self unchanged and an operand failing part way raising with its earlier pairs kept in maps[0]; clear() empties maps[0] in place so later maps answer."
    source := "docstrings, Lib/collections/__init__.py:1103, :1148; PEP 584"
    status := .proven, prop := ``ChainMapObjects, thm := some ``chainMapObjects_proven },
  { id := "coll-chainmap-ror-p", pyFile := file, pyFns := ["ChainMap.__ror__"]
    statement := "other | cm builds dict(other) first: its value gives the one-map ChainMap of coll-chainmap-union-flat, its exception propagates, and a non-Mapping gets NotImplemented."
    source := "PEP 584; Lib/collections/__init__.py:1162-1168"
    status := .proven, prop := ``ChainMapRorP, thm := some ``chainMapRorP_proven }
]

def userDictEntries : List Entry := [
  { id := "coll-userdict-matches-dict", pyFile := file
    pyFns := ["UserDict.__len__", "UserDict.get"]
    statement := "Without __missing__, subscript, get, in, len, iter, pop, setdefault and (k, v) in items() give what the wrapped dict gives, on every dict."
    source := "Doc/library/collections.rst, UserDict: 'simulates a dictionary'"
    status := .proven, prop := ``UserDictMatchesDict, thm := some ``userDictMatchesDict_proven },
  { id := "coll-userdict-set-del", pyFile := file, pyFns := ["UserDict.__setitem__", "UserDict.__delitem__"]
    statement := "u[k] = v then u[k] gives v; del u[k] removes that key only, and raises KeyError(k) when it is absent."
    source := "invariant of a mapping"
    status := .proven, prop := ``UserDictSetDel, thm := some ``userDictSetDel_proven },
  { id := "coll-userdict-constructors-union", pyFile := file
    pyFns := ["UserDict.__or__", "UserDict.__ror__"]
    statement := "|, |= and the constructors agree with dict's and keep the class, for dict and UserDict operands alike; copy and copy.copy preserve items, order and class."
    source := "Doc/library/collections.rst, UserDict; PEP 584"
    status := .proven, prop := ``UserDictConstructorsUnion, thm := some ``userDictConstructorsUnion_proven },
  { id := "coll-userdict-clear-repr", pyFile := file, pyFns := []
    statement := "clear() empties any UserDict through its popitem loop, and repr(UserDict(d)) == repr(d)."
    source := "invariant; Lib/collections/__init__.py:1216-1217"
    status := .proven, prop := ``UserDictClearRepr, thm := some ``userDictClearRepr_proven },
  { id := "coll-userdict-popitem-lifo", pyFile := file, pyFns := ["UserDict.popitem"]
    statement := "UserDict.popitem is dict.popitem on self.data: it removes the last item, and raises dict's KeyError on an empty one."
    source := "Lib/collections/__init__.py:1260-1268; Doc/builtins/stdtypes.rst, dict.popitem: 'LIFO order'"
    status := .proven, prop := ``UserDictPopitemMatchesDict, thm := some ``userDictPopitemMatchesDict_proven },
  { id := "coll-userdict-reversible", pyFile := file, pyFns := ["UserDict.__reversed__"]
    statement := "reversed(UserDict(d)) yields what reversed(d) yields. False: TypeError, Mapping.__reversed__ is None."
    source := "Doc/builtins/stdtypes.rst, dict: 'Dictionaries and dictionary views are reversible'; Doc/library/collections.rst, UserDict"
    status := .refuted, prop := ``UserDictReversible, thm := some ``userDictReversible_refuted
    bug := some "corelibs-userdict-not-reversible" },
  { id := "coll-userdict-missing-like-dict", pyFile := file, pyFns := ["UserDict.__getitem__", "UserDict.__contains__", "UserDict.get"]
    statement := "A UserDict subclass with __missing__ behaves like a dict subclass with __missing__ in pop(k, default), setdefault and items(). False: __missing__ answers inside the inherited self[key], so pop(k, d) raises KeyError, setdefault stores nothing, and (k, v) in items() is true for an absent k."
    source := "comment, Lib/collections/__init__.py:1204-1205: 'work like dict does when __missing__ is present'"
    status := .refuted, prop := ``UserDictMissingLikeDict, thm := some ``userDictMissingLikeDict_refuted
    bug := some "corelibs-userdict-missing-pop-setdefault" },
  { id := "coll-userdict-missing-narrow", pyFile := file, pyFns := ["UserDict.__contains__", "UserDict.get"]
    statement := "With __missing__, get and in never call it, and on a present key pop, setdefault and items() agree with dict."
    source := "narrowing of coll-userdict-missing-like-dict; gh-83445"
    status := .proven, prop := ``UserDictMissingNarrow, thm := some ``userDictMissingNarrow_proven },
  { id := "coll-userdict-init-p", pyFile := file, pyFns := ["UserDict.__init__"]
    statement := "UserDict(src, **kw) holds dict(src, **kw)'s items for a dict or an iterable of the same pairs; an argument whose iter(), next(), pair unpacking or [] raises makes it raise."
    source := "Doc/library/collections.rst, UserDict; Lib/collections/__init__.py:1177-1182; Lib/_collections_abc.py:965-984"
    status := .proven, prop := ``UserDictInitP, thm := some ``userDictInitP_proven },
  { id := "coll-userdict-getitem-p", pyFile := file, pyFns := ["UserDict.__getitem__", "UserDict.__contains__"]
    statement := "u[k] is the value of a present key, else exactly what __missing__ returns or raises, else KeyError(k); k in u is k in u.data, false for an absent key even when __missing__ answers; an unhashable key raises the dict's error from both."
    source := "Lib/collections/__init__.py:1188-1193, :1204-1207"
    status := .proven, prop := ``UserDictGetitemP, thm := some ``userDictGetitemP_proven },
  { id := "coll-userdict-iter-order", pyFile := file, pyFns := ["UserDict.__iter__"]
    statement := "iter(u) follows insertion order: u[k] = v keeps a present key in place and appends a new one, del u[k] removes k from the order."
    source := "Doc/library/stdtypes.rst, dict; Lib/collections/__init__.py:1201-1202"
    status := .proven, prop := ``UserDictIterOrder, thm := some ``userDictIterOrder_proven },
  { id := "coll-userdict-repr-r", pyFile := file, pyFns := ["UserDict.__repr__"]
    statement := "repr(u) is repr(u.data): the dict's repr for ordinary values, {...} where u holds itself, and the exception of a raising key repr."
    source := "Lib/collections/__init__.py:1216-1217; Objects/dictobject.c:3647-3650"
    status := .proven, prop := ``UserDictReprR, thm := some ``userDictReprR_proven },
  { id := "coll-userdict-ior-p", pyFile := file, pyFns := ["UserDict.__ior__"]
    statement := "u |= other merges other's items into u.data from either branch (UserDict or anything dict |= reads); a non-iterable raises TypeError with u unchanged, an iterable failing part way raises with its earlier pairs merged."
    source := "PEP 584; Lib/collections/__init__.py:1233-1238"
    status := .proven, prop := ``UserDictIorP, thm := some ``userDictIorP_proven },
  { id := "coll-userdict-copy-o", pyFile := file, pyFns := ["UserDict.__copy__", "UserDict.copy"]
    statement := "copy.copy(u) and u.copy() are new objects of u's class whose data is a new dict (not u.data) with u's items (and, for __copy__ and subclasses, u's other attributes); when a subclass's copy.copy raises, copy raises it and u.data is restored."
    source := "Lib/collections/__init__.py:1240-1257"
    status := .proven, prop := ``UserDictCopyO, thm := some ``userDictCopyO_proven },
  { id := "coll-userdict-fromkeys-p", pyFile := file, pyFns := ["UserDict.fromkeys"]
    statement := "cls.fromkeys(xs, v) is an instance of cls with dict.fromkeys(xs, v)'s items; an exception from the iterable propagates."
    source := "Lib/collections/__init__.py:1272-1277"
    status := .proven, prop := ``UserDictFromkeysP, thm := some ``userDictFromkeysP_proven }
]

def userListEntries : List Entry := [
  { id := "coll-userlist-simulates", pyFile := file
    pyFns := ["UserList.append", "UserList.insert", "UserList.pop", "UserList.remove", "UserList.clear", "UserList.extend",
      "UserList.reverse", "UserList.sort", "UserList.__setitem__", "UserList.__delitem__", "UserList.__iadd__",
      "UserList.__imul__"]
    statement := "For every program of mutating calls, a UserList and a list with the same contents stop at the same exception or end with the same contents, and the class is kept."
    source := "Doc/library/collections.rst, UserList: 'simulates a list'"
    status := .proven, prop := ``UserListSimulatesList, thm := some ``userListSimulatesList_proven },
  { id := "coll-userlist-observers", pyFile := file
    pyFns := ["UserList.__repr__", "UserList.__contains__", "UserList.__len__", "UserList.__getitem__", "UserList.__mul__",
      "UserList.count", "UserList.index"]
    statement := "len, in, count, index, item access and repr answer as the wrapped list; slices and * re-wrap the list's result in the class."
    source := "Doc/library/collections.rst, UserList"
    status := .proven, prop := ``UserListObservers, thm := some ``userListObservers_proven },
  { id := "coll-userlist-operands", pyFile := file
    pyFns := ["UserList.__init__", "UserList.__lt__", "UserList.__le__", "UserList.__eq__", "UserList.__gt__", "UserList.__ge__",
      "UserList.__cast", "UserList.__add__", "UserList.__radd__", "UserList.__iadd__", "UserList.extend"]
    statement := "__add__, __radd__, __iadd__, extend and __init__ treat a UserList, a list and any iterable with the same items alike, a non-iterable is the same TypeError, and comparison with a UserList is comparison with its list."
    source := "invariant: sibling methods; Lib/collections/__init__.py:1288-1359"
    status := .proven, prop := ``UserListOperandsAgree, thm := some ``userListOperandsAgree_proven },
  { id := "coll-userlist-copies", pyFile := file, pyFns := ["UserList.copy", "UserList.__copy__"]
    statement := "copy() and copy.copy keep contents and class."
    source := "invariant; Lib/collections/__init__.py:1370-1393"
    status := .proven, prop := ``UserListCopies, thm := some ``userListCopies_proven },
  { id := "coll-userlist-int-instance", pyFile := file
    pyFns := ["UserList.reverse", "UserList.sort", "UserList.__eq__", "UserList.__le__", "UserList.__lt__"]
    statement := "With the real list on ints, reverse and sort give the reversal and the stable order, and a UserList is ==, <= and not < a list or UserList of the same items."
    source := "invariant"
    status := .proven, prop := ``UserListIntInstance, thm := some ``userListIntInstance_proven },
  { id := "coll-userlist-iadd-atomic", pyFile := file
    pyFns := ["UserList.__iadd__", "UserList.extend", "UserList.__add__", "UserList.__radd__"]
    statement := "For an iterator that yields xs then raises e, u += it raises e with u unchanged while u.extend(it) and list += it keep xs; u + it and it + u raise e; without the failure all append xs, and a non-iterable's TypeError leaves u unchanged."
    source := "Lib/collections/__init__.py:1338-1359, :1407-1411; Objects/listobject.c list_extend"
    status := .proven, prop := ``UserListIaddAtomic, thm := some ``userListIaddAtomic_proven },
  { id := "coll-userlist-init-copy", pyFile := file, pyFns := ["UserList.__init__", "UserList.copy", "UserList.__copy__"]
    statement := "UserList(x) holds a new list: an exact list's items copied (not aliased), a UserList's data, a list subclass's __iter__ items, another iterable's items or its exception; copy() and copy.copy() are new objects with a new data list."
    source := "Lib/collections/__init__.py:1288-1297, :1370-1375, :1392-1393"
    status := .proven, prop := ``UserListInitCopy, thm := some ``userListInitCopy_proven },
  { id := "coll-userlist-compare-p", pyFile := file
    pyFns := ["UserList.__lt__", "UserList.__le__", "UserList.__eq__", "UserList.__gt__", "UserList.__ge__",
      "UserList.__cast"]
    statement := "Comparisons are list_richcompare on data with the elements' own results: lengths shortcut ==, the first non-identical pair whose == is false decides (== False, orderings return that pair's object), a raising element == raises; a UserList compares by its data; any other operand's reflected method answers (UserList([1]) == mock.ANY), else == is False and orderings raise TypeError."
    source := "Lib/collections/__init__.py:1302-1318; Objects/listobject.c:3459-3519"
    status := .proven, prop := ``UserListCompareP, thm := some ``userListCompareP_proven },
  { id := "coll-userlist-contains-count", pyFile := file, pyFns := ["UserList.__contains__", "UserList.count"]
    statement := "x in u and u.count(x) use each element's == after identity; a raising == raises."
    source := "Lib/collections/__init__.py:1320-1321, :1395-1396; Objects/listobject.c:677-690, :3387-3410"
    status := .proven, prop := ``UserListContainsCount, thm := some ``userListContainsCount_proven }
]

def userStringEntries : List Entry := [
  { id := "coll-userstring-simulates", pyFile := file
    pyFns := ["UserString.__repr__", "UserString.__int__", "UserString.__float__", "UserString.__complex__", "UserString.__hash__",
      "UserString.__eq__", "UserString.__lt__", "UserString.__le__", "UserString.__gt__", "UserString.__ge__",
      "UserString.__contains__", "UserString.__len__", "UserString.__getitem__", "UserString.__mul__", "UserString.__mod__",
      "UserString.capitalize", "UserString.casefold", "UserString.center", "UserString.count", "UserString.removeprefix",
      "UserString.removesuffix", "UserString.encode", "UserString.endswith", "UserString.expandtabs", "UserString.find",
      "UserString.format", "UserString.format_map", "UserString.index", "UserString.isalpha", "UserString.isalnum",
      "UserString.isascii", "UserString.isdecimal", "UserString.isdigit", "UserString.isidentifier", "UserString.islower",
      "UserString.isnumeric", "UserString.isprintable", "UserString.isspace", "UserString.istitle", "UserString.isupper",
      "UserString.join", "UserString.ljust", "UserString.lower", "UserString.lstrip", "UserString.partition",
      "UserString.replace", "UserString.rfind", "UserString.rindex", "UserString.rjust", "UserString.rpartition",
      "UserString.rstrip", "UserString.split", "UserString.rsplit", "UserString.splitlines", "UserString.startswith",
      "UserString.strip", "UserString.swapcase", "UserString.title", "UserString.translate", "UserString.upper",
      "UserString.zfill"]
    statement := "For every method and str arguments, the UserString method gives the str method's result or exception, a UserString result being read as its data."
    source := "Doc/library/collections.rst, UserString: 'simulates a string object'"
    status := .proven, prop := ``UserStringSimulatesStr, thm := some ``userStringSimulatesStr_proven },
  { id := "coll-userstring-unwrap-siblings", pyFile := file
    pyFns := ["UserString.startswith", "UserString.endswith", "UserString.partition", "UserString.rpartition",
      "UserString.split", "UserString.rsplit", "UserString.strip", "UserString.lstrip", "UserString.rstrip",
      "UserString.center", "UserString.ljust", "UserString.rjust", "UserString.join"]
    statement := "Every method taking a str gives the same result for the equal UserString. False: count, find, replace and others unwrap the argument; partition, split, strip, center, join, startswith and endswith do not and raise TypeError (3.15.2 :1538-1539, :1648-1649)."
    source := "invariant: sibling methods; gh-159868 fixed startswith and endswith on main"
    status := .refuted, prop := ``UserStringUnwrapSiblings, thm := some ``userStringUnwrapSiblings_refuted
    bug := some "corelibs-userstring-unwrap-siblings" },
  { id := "coll-userstring-unwrap-narrow", pyFile := file
    pyFns := ["UserString.count", "UserString.find", "UserString.index", "UserString.rfind", "UserString.rindex",
      "UserString.replace", "UserString.removeprefix", "UserString.removesuffix", "UserString.__contains__",
      "UserString.__eq__", "UserString.__lt__", "UserString.__le__", "UserString.__gt__", "UserString.__ge__"]
    statement := "The methods with the isinstance test give the same result, exception included, for a UserString argument as for the equal str."
    source := "narrowing of coll-userstring-unwrap-siblings"
    status := .proven, prop := ``UserStringUnwrapNarrow, thm := some ``userStringUnwrapNarrow_proven },
  { id := "coll-userstring-result-class", pyFile := file
    pyFns := ["UserString.__getitem__", "UserString.__mul__", "UserString.__mod__", "UserString.capitalize", "UserString.casefold",
      "UserString.center", "UserString.removeprefix", "UserString.removesuffix", "UserString.expandtabs", "UserString.format",
      "UserString.format_map", "UserString.join", "UserString.ljust", "UserString.lower", "UserString.lstrip",
      "UserString.partition", "UserString.replace", "UserString.rjust", "UserString.rpartition", "UserString.rstrip",
      "UserString.split", "UserString.rsplit", "UserString.splitlines", "UserString.strip", "UserString.swapcase",
      "UserString.title", "UserString.translate", "UserString.upper", "UserString.zfill"]
    statement := "Exactly the listed methods return self.__class__; format, format_map, join, partition, split and the rest return the plain type str returns."
    source := "invariant; describes behaviour under discussion in python/cpython#76022"
    status := .proven, prop := ``UserStringResultClass, thm := some ``userStringResultClass_proven
    notes := "Not filed: gh-76022 is open and the join case was deliberately left." },
  { id := "coll-userstring-replace-count", pyFile := file, pyFns := ["UserString.replace"]
    statement := "u.replace(old, new, count=n) does what str.replace does. False: the parameter is named maxsplit, TypeError."
    source := "Doc/builtins/stdtypes.rst, str.replace: 'count is now supported as a keyword argument' (3.13)"
    status := .refuted, prop := ``UserStringReplaceCountKeyword, thm := some ``userStringReplaceCountKeyword_refuted
    bug := some "corelibs-userstring-replace-count-keyword" },
  { id := "coll-userstring-format-spec", pyFile := file, pyFns := ["UserString.__format__"]
    statement := "format(u, spec) gives what format(u.data, spec) gives. False: no __format__, so object.__format__ raises TypeError for any non-empty spec."
    source := "Doc/library/collections.rst, UserString: 'simulates a string object'"
    status := .refuted, prop := ``UserStringFormatSpec, thm := some ``userStringFormatSpec_refuted
    bug := some "corelibs-userstring-no-format" },
  { id := "coll-userstring-order-hash", pyFile := file
    pyFns := ["UserString.__eq__", "UserString.__lt__", "UserString.__le__", "UserString.__gt__", "UserString.__ge__", "UserString.__hash__"]
    statement := "Against a str or UserString, exactly one of <, ==, > holds, <= and >= are the weak forms, == is equality of text, and equal objects have equal hashes."
    source := "invariant: total order; hash and eq contract"
    status := .proven, prop := ``UserStringOrderHash, thm := some ``userStringOrderHash_proven },
  { id := "coll-userstring-construct-add", pyFile := file
    pyFns := ["UserString.__init__", "UserString.__str__", "UserString.__int__", "UserString.__float__", "UserString.__complex__",
      "UserString.__getnewargs__", "UserString.__add__", "UserString.__radd__", "UserString.__rmod__", "UserString.encode"]
    statement := "__init__ reads a str, a UserString and str(obj) alike; __getnewargs__ and __str__ rebuild the object; + and radd concatenate with the same str(other) and keep the class; __rmod__ keeps the class; encode(None, None) means the defaults."
    source := "Lib/collections/__init__.py:1420-1426, :1485-1506, :1533-1536"
    status := .proven, prop := ``UserStringConstructAdd, thm := some ``userStringConstructAdd_proven },
  { id := "coll-userstring-mul", pyFile := file, pyFns := ["UserString.__mul__"]
    statement := "u * n is empty for n <= 0 and has length n * len(u), keeping the class, when that fits Py_ssize_t."
    source := "Doc/builtins/stdtypes.rst, common sequence operations"
    status := .proven, prop := ``UserStringMul, thm := some ``userStringMul_proven },
  { id := "coll-userstring-str-calls", pyFile := file
    pyFns := ["UserString.__init__", "UserString.__add__", "UserString.__radd__", "UserString.__rmod__",
      "UserString.__getnewargs__"]
    statement := "UserString(x), u + x, x + u and x % u call str(x) on other objects and raise what its __str__ raises; __getnewargs__ is the 1-tuple (data,) and the class rebuilds u from it."
    source := "Lib/collections/__init__.py:1420-1426, :1446-1447, :1485-1495, :1505-1506"
    status := .proven, prop := ``UserStringStrCalls, thm := some ``userStringStrCalls_proven },
  { id := "coll-userstring-compare-p", pyFile := file
    pyFns := ["UserString.__eq__", "UserString.__lt__", "UserString.__le__", "UserString.__gt__", "UserString.__ge__"]
    statement := "A UserString operand compares by its data; another object's reflected method answers with its object (UserString('a') == mock.ANY), else == is False and orderings raise TypeError."
    source := "Lib/collections/__init__.py:1449-1472"
    status := .proven, prop := ``UserStringCompareP, thm := some ``userStringCompareP_proven },
  { id := "coll-userstring-no-unwrap", pyFile := file
    pyFns := ["UserString.strip", "UserString.lstrip", "UserString.rstrip", "UserString.rpartition",
      "UserString.split", "UserString.rsplit", "UserString.center", "UserString.ljust", "UserString.rjust",
      "UserString.join"]
    statement := "strip, lstrip, rstrip, rpartition, split, rsplit, center, ljust, rjust and join raise str's TypeError for a UserString argument; join(5) raises 'can only join an iterable' and a raising iterator raises before any item check."
    source := "Lib/collections/__init__.py:1515-1652; Objects/unicodeobject.c"
    status := .proven, prop := ``UserStringNoUnwrap, thm := some ``userStringNoUnwrap_proven },
  { id := "coll-str-clinic-order", pyFile := file
    pyFns := ["UserString.center", "UserString.ljust", "UserString.rjust", "UserString.split", "UserString.rsplit"]
    statement := "center/ljust/rjust with a width outside Py_ssize_t and split/rsplit with such a maxsplit raise OverflowError whatever the fill or sep: clinic converts the integer first."
    source := "Objects/clinic/unicodeobject.c.h:115-132; Objects/unicodeobject.c:12900-12912"
    status := .proven, prop := ``StrClinicOrder, thm := some ``strClinicOrder_proven }
]

def namedtupleEntries : List Entry := [
  { id := "coll-namedtuple-rename-total", pyFile := file, pyFns := ["namedtuple"]
    statement := "namedtuple(valid_name, names, rename=True) succeeds for every list of names. False: distinct names with one NFKC form pass every check and then fail in the compiler, ['ﬁ', 'fi'] with SyntaxError."
    source := "Doc/library/collections.rst, namedtuple: 'If rename is true, invalid fieldnames are automatically replaced with positional names'"
    status := .refuted, prop := ``NamedtupleRenameTotal, thm := some ``namedtupleRenameTotal_refuted
    bug := some "corelibs-namedtuple-nfkc-field-names" },
  { id := "coll-namedtuple-rename-narrow", pyFile := file, pyFns := ["namedtuple"]
    statement := "On names NFKC leaves alone, rename=True always gives a class whose fields are the names or _i, without repeats, and whose __new__ has those parameters."
    source := "narrowing of coll-namedtuple-rename-total"
    status := .proven, prop := ``NamedtupleRenameNarrow, thm := some ``namedtupleRenameNarrow_proven },
  { id := "coll-namedtuple-validation", pyFile := file, pyFns := ["namedtuple"]
    statement := "Without rename, on names NFKC leaves alone, namedtuple succeeds exactly when the type name and fields are non-keyword identifiers, no field starts with an underscore and none repeats."
    source := "Doc/library/collections.rst, namedtuple"
    status := .proven, prop := ``NamedtupleValidation, thm := some ``namedtupleValidation_proven },
  { id := "coll-namedtuple-asdict-roundtrip", pyFile := file, pyFns := ["namedtuple"]
    statement := "T(**p._asdict()) == p. False: _asdict has the raw field names, __new__ the NFKC-normalised ones."
    source := "docstring, Lib/collections/__init__.py:375-379"
    status := .refuted, prop := ``NamedtupleAsdictRoundTrip, thm := some ``namedtupleAsdictRoundTrip_refuted
    bug := some "corelibs-namedtuple-nfkc-field-names" },
  { id := "coll-namedtuple-asdict-narrow", pyFile := file, pyFns := ["namedtuple"]
    statement := "When NFKC leaves the fields alone, T(**p._asdict()) == p for every rename, defaults and tuple."
    source := "narrowing of coll-namedtuple-asdict-roundtrip"
    status := .proven, prop := ``NamedtupleAsdictNarrow, thm := some ``namedtupleAsdictNarrow_proven },
  { id := "coll-namedtuple-source-attribute", pyFile := file, pyFns := ["namedtuple"]
    statement := "p.f written in source reaches every field f. False: attributes are stored under the raw name, source identifiers are normalised."
    source := "docstring, Lib/collections/__init__.py:373"
    status := .refuted, prop := ``NamedtupleSourceAttribute, thm := some ``namedtupleSourceAttribute_refuted
    bug := some "corelibs-namedtuple-nfkc-field-names" },
  { id := "coll-namedtuple-instance-methods", pyFile := file, pyFns := ["namedtuple"]
    statement := "On every generated class: _make returns the items and refuses a wrong length, _replace changes the named field only and refuses an unknown name, getattr and _asdict follow _fields."
    source := "docstring, Lib/collections/__init__.py:362-382"
    status := .proven, prop := ``NamedtupleInstanceMethods, thm := some ``namedtupleInstanceMethods_proven },
  { id := "coll-namedtuple-defaults", pyFile := file, pyFns := ["namedtuple"]
    statement := "Defaults fill the rightmost parameters in order, and _field_defaults has exactly the last len(defaults) fields."
    source := "Doc/library/collections.rst, namedtuple"
    status := .proven, prop := ``NamedtupleDefaults, thm := some ``namedtupleDefaults_proven },
  { id := "coll-namedtuple-conversions", pyFile := file, pyFns := ["namedtuple"]
    statement := "A str field_names is its comma/whitespace-separated words; an iterable of names whose str() or next() raises raises before any check; tuple(defaults) raising does so only after the name checks pass."
    source := "Lib/collections/__init__.py:387-389, :421-423; Doc/library/collections.rst, namedtuple"
    status := .proven, prop := ``NamedtupleConversions, thm := some ``namedtupleConversions_proven },
  { id := "coll-namedtuple-getnewargs", pyFile := file, pyFns := ["namedtuple"]
    statement := "T(*p.__getnewargs__()) gives back p's values for every generated class and tuple of the right length."
    source := "docstring, Lib/collections/__init__.py:481"
    status := .proven, prop := ``NamedtupleGetnewargs, thm := some ``namedtupleGetnewargs_proven },
  { id := "coll-namedtuple-repr", pyFile := file, pyFns := ["namedtuple"]
    statement := "repr(p) is Cls(f1=r1, ..., fn=rn) with the instance's class name and the class's _fields (the names given, after rename) in order, and raises when a value's repr raises."
    source := "docstring, Lib/collections/__init__.py:473; :435"
    status := .proven, prop := ``NamedtupleRepr, thm := some ``namedtupleRepr_proven }
]

def entries : List Entry :=
  counterEntries ++ chainMapEntries ++ userDictEntries ++ userListEntries ++ userStringEntries ++
    namedtupleEntries

end PyLean.CoreLibs.Coll
