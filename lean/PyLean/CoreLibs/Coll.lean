import PyLean.Registry
import PyLean.CoreLibs.Coll.Diff
import PyLean.CoreLibs.Coll.CounterMost
import PyLean.CoreLibs.Coll.CounterXor
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
    statement := "The Python _count_elements, the C fast path and the C slow path write the same dict, keys in the same order, for every mapping of int counts and every iterable."
    source := "invariant: C and Python twins; Lib/collections/__init__.py:540-549, Modules/_collectionsmodule.c:2544-2644"
    status := .proven, prop := ``CountElementsTwins, thm := some ``countElementsTwins_proven },
  { id := "coll-counter-update-fast-slow", pyFile := file, pyFns := ["Counter.update"]
    statement := "The fast path of update on an empty Counter (dict.update) builds the same dict, order included, as the general adding loop, for every dict of int counts."
    source := "invariant: fast and slow path, Lib/collections/__init__.py:698-705"
    status := .proven, prop := ``UpdateFastEqSlow, thm := some ``updateFastEqSlow_proven },
  { id := "coll-counter-update-adds", pyFile := file
    pyFns := ["Counter.update", "Counter.__init__", "Counter.__missing__", "_count_elements"]
    statement := "After update(src, **kw) the count of x is its old count plus the source's and the keywords' contribution, for every counter; Counter(src, **kw) is the empty-counter case, and a missing element counts zero."
    source := "docstrings, Lib/collections/__init__.py:606-615, :683"
    status := .proven, prop := ``UpdateAddsCounts, thm := some ``updateAddsCounts_proven },
  { id := "coll-counter-first-seen-order", pyFile := file, pyFns := ["Counter.__init__", "_count_elements"]
    statement := "Counter(iterable) holds its elements in the order of dict.fromkeys(iterable)."
    source := "Doc/library/collections.rst, Counter (order of first occurrence since 3.7)"
    status := .proven, prop := ``CounterFirstSeenOrder, thm := some ``counterFirstSeenOrder_proven },
  { id := "coll-counter-subtract", pyFile := file, pyFns := ["Counter.subtract", "Counter.update"]
    statement := "subtract lowers counts by the source's contribution, and subtract after update with the same arguments restores every count."
    source := "docstring, Lib/collections/__init__.py:712-717"
    status := .proven, prop := ``SubtractUndoesUpdate, thm := some ``subtractUndoesUpdate_proven },
  { id := "coll-counter-total", pyFile := file, pyFns := ["Counter.total"]
    statement := "total() rises by n when n elements are counted and by another mapping's total when it is merged."
    source := "docstring 'Sum of the counts', Lib/collections/__init__.py:625"
    status := .proven, prop := ``TotalTracksUpdate, thm := some ``totalTracksUpdate_proven },
  { id := "coll-counter-copy-reduce", pyFile := file, pyFns := ["Counter.copy", "Counter.__reduce__"]
    statement := "copy() and the __reduce__ payload keep the items and their order, non-positive counts included."
    source := "invariant; docstring 'Return a shallow copy.', Lib/collections/__init__.py:739"
    status := .proven, prop := ``CopyReduceFaithful, thm := some ``copyReduceFaithful_proven },
  { id := "coll-counter-delitem", pyFile := file, pyFns := ["Counter.__delitem__"]
    statement := "del c[e] never raises, removes exactly e, and is a no-op on a missing element."
    source := "docstring, Lib/collections/__init__.py:746"
    status := .proven, prop := ``DelitemTotal, thm := some ``delitemTotal_proven },
  { id := "coll-counter-compare-pointwise", pyFile := file
    pyFns := ["Counter.__eq__", "Counter.__ne__", "Counter.__le__", "Counter.__lt__", "Counter.__ge__", "Counter.__gt__"]
    statement := "The six comparisons are the pointwise order on count functions with missing as zero, for all counters."
    source := "docstrings, Lib/collections/__init__.py:800-830"
    status := .proven, prop := ``ComparisonsPointwise, thm := some ``comparisonsPointwise_proven },
  { id := "coll-counter-compare-order", pyFile := file
    pyFns := ["Counter.__eq__", "Counter.__le__", "Counter.__lt__", "Counter.__ge__", "Counter.__gt__"]
    statement := "a <= b and b <= a exactly when a == b; < and > are converses, as are <= and >=."
    source := "invariant"
    status := .proven, prop := ``ComparisonsAreOrder, thm := some ``comparisonsAreOrder_proven },
  { id := "coll-counter-fromkeys", pyFile := file, pyFns := []
    statement := "Counter.fromkeys raises NotImplementedError for every input."
    source := "Doc/library/collections.rst, Counter.fromkeys; Lib/collections/__init__.py:665-675"
    status := .proven, prop := ``FromkeysUndefined, thm := some ``fromkeysUndefined_proven },
  { id := "coll-counter-ops-pointwise", pyFile := file
    pyFns := ["Counter.__add__", "Counter.__sub__", "Counter.__or__", "Counter.__and__", "Counter.__pos__", "Counter.__neg__"]
    statement := "+, -, |, & and unary + and - compute sum, difference, maximum, minimum, positive part and negated positive part of counts, clipped at zero, for all counters including non-positive counts."
    source := "docstrings, Lib/collections/__init__.py:836-950"
    status := .proven, prop := ``OperatorsPointwise, thm := some ``operatorsPointwise_proven },
  { id := "coll-counter-ops-contract", pyFile := file
    pyFns := ["Counter.__add__", "Counter.__sub__", "Counter.__or__", "Counter.__and__", "Counter.__pos__", "Counter.__neg__"]
    statement := "Operator results hold only positive counts, and keys appear in left-operand order, then right-operand order."
    source := "comments, Lib/collections/__init__.py:765, :775-777"
    status := .proven, prop := ``OperatorsOutputContract, thm := some ``operatorsOutputContract_proven },
  { id := "coll-counter-unary-binary", pyFile := file, pyFns := ["Counter.__pos__", "Counter.__neg__"]
    statement := "+c equals c + Counter() and -c equals Counter() - c, items and order."
    source := "docstrings, Lib/collections/__init__.py:938, :920"
    status := .proven, prop := ``UnaryAreBinary, thm := some ``unaryAreBinary_proven },
  { id := "coll-counter-inplace", pyFile := file
    pyFns := ["Counter.__iadd__", "Counter.__isub__", "Counter.__ior__", "Counter.__iand__", "Counter._keep_positive"]
    statement := "c += d, c -= d, c |= d, c &= d leave c equal to c + d, c - d, c | d, c & d, items and order, for all counters."
    source := "invariant: in-place and binary forms; docstrings, Lib/collections/__init__.py:964-1011"
    status := .proven, prop := ``InplaceAgreesBinary, thm := some ``inplaceAgreesBinary_proven },
  { id := "coll-counter-xor", pyFile := file, pyFns := ["Counter.__xor__", "Counter.__ixor__"]
    statement := "c ^ d is the absolute difference of counts, for all counters including zero and negative counts, equal to (c - d) | (d - c), with positive counts only, in the operators' key order; c ^= d gives the same items in the same order."
    source := "docstrings, Lib/collections/__init__.py:910-935, :1019-1033"
    status := .proven, prop := ``XorPointwise, thm := some ``xorPointwise_proven },
  { id := "coll-counter-keep-positive", pyFile := file, pyFns := ["Counter._keep_positive"]
    statement := "_keep_positive removes exactly the non-positive counts, in place order kept, and equals unary +."
    source := "docstring, Lib/collections/__init__.py:957"
    status := .proven, prop := ``KeepPositiveFilters, thm := some ``keepPositiveFilters_proven },
  { id := "coll-counter-set-correspondence", pyFile := file
    pyFns := ["Counter.__add__", "Counter.__sub__", "Counter.__or__", "Counter.__and__", "Counter.__eq__",
      "Counter.__ne__", "Counter.__le__", "Counter.__lt__", "Counter.__ge__", "Counter.__gt__"]
    statement := "With multiplicities zero or one, all ten relations of the comment hold between multiset and set operations."
    source := "comment, Lib/collections/__init__.py:774-792"
    status := .proven, prop := ``SetCorrespondence, thm := some ``setCorrespondence_proven },
  { id := "coll-counter-most-common-prefix", pyFile := file, pyFns := ["Counter.most_common"]
    statement := "most_common(n) is most_common()[:n] for every n >= 0, ties included, across the max, sorted and heap paths; a negative n gives []."
    source := "docstring, Lib/collections/__init__.py:629-630"
    status := .proven, prop := ``MostCommonPrefix, thm := some ``mostCommonPrefix_proven },
  { id := "coll-counter-most-common-sorted", pyFile := file, pyFns := ["Counter.most_common"]
    statement := "most_common() is a permutation of the items in non-increasing order of count, equal counts staying in insertion order."
    source := "Doc/library/collections.rst, most_common"
    status := .proven, prop := ``MostCommonSorted, thm := some ``mostCommonSorted_proven },
  { id := "coll-counter-elements", pyFile := file, pyFns := ["Counter.elements"]
    statement := "For counts that fit Py_ssize_t, counting c.elements() gives +c, the elements coming in insertion order."
    source := "docstring, Lib/collections/__init__.py:643-657"
    status := .proven, prop := ``ElementsRoundTrip, thm := some ``elementsRoundTrip_proven },
  { id := "coll-counter-repr", pyFile := file, pyFns := ["Counter.__repr__"]
    statement := "repr of a non-empty counter lists items in most_common order and an empty one prints Counter()."
    source := "comment, Lib/collections/__init__.py:754"
    status := .proven, prop := ``ReprMostCommonOrder, thm := some ``reprMostCommonOrder_proven }
]

def chainMapEntries : List Entry := [
  { id := "coll-chainmap-flat-view", pyFile := file
    pyFns := ["ChainMap.__getitem__", "ChainMap.__missing__", "ChainMap.get", "ChainMap.__len__", "ChainMap.__iter__",
      "ChainMap.__contains__", "ChainMap.__bool__"]
    statement := "Subscript, get, in, len, iter and bool on a ChainMap agree with the flat dict built by updating from the last map to the first."
    source := "Doc/library/collections.rst, ChainMap"
    status := .proven, prop := ``ChainMapFlatView, thm := some ``chainMapFlatView_proven },
  { id := "coll-chainmap-writes-first", pyFile := file
    pyFns := ["ChainMap.__setitem__", "ChainMap.__delitem__", "ChainMap.popitem", "ChainMap.pop", "ChainMap.clear"]
    statement := "Writes and deletions change maps[0] only, their KeyError is decided by maps[0] alone, and a key removed from maps[0] then reads from the later maps."
    source := "Doc/library/collections.rst, ChainMap: 'writes, updates, and deletions only operate on the first mapping'"
    status := .proven, prop := ``ChainMapWritesFirst, thm := some ``chainMapWritesFirst_proven },
  { id := "coll-chainmap-union-flat", pyFile := file
    pyFns := ["ChainMap.__ior__", "ChainMap.__or__", "ChainMap.__ror__", "ChainMap.copy"]
    statement := "cm | o reads as dict(cm) | o with the tail maps kept, cm |= o likewise, o | cm is the one-map o | dict(cm), copy reads the same, items and order, and non-mappings get NotImplemented."
    source := "PEP 584; Lib/collections/__init__.py:1151-1168"
    status := .proven, prop := ``ChainMapUnionFlat, thm := some ``chainMapUnionFlat_proven },
  { id := "coll-chainmap-child-parents", pyFile := file
    pyFns := ["ChainMap.__init__", "ChainMap.new_child", "ChainMap.parents", "ChainMap.fromkeys"]
    statement := "__init__ always leaves at least one map, new_child and parents are inverse on the map list, and fromkeys reads like dict.fromkeys."
    source := "docstrings and comment, Lib/collections/__init__.py:1055-1059, :1057, :1067-1079"
    status := .proven, prop := ``ChainMapChildParents, thm := some ``chainMapChildParents_proven },
  { id := "coll-chainmap-repr", pyFile := file, pyFns := ["ChainMap.__repr__"]
    statement := "repr shows the maps in order, so new_child prepends the child's repr, and ChainMap() prints its empty dict."
    source := "invariant; Lib/collections/__init__.py:1093-1095"
    status := .proven, prop := ``ChainMapRepr, thm := some ``chainMapRepr_proven }
]

def userDictEntries : List Entry := [
  { id := "coll-userdict-matches-dict", pyFile := file
    pyFns := ["UserDict.__len__", "UserDict.__getitem__", "UserDict.__iter__", "UserDict.__contains__", "UserDict.get"]
    statement := "Without __missing__, subscript, get, in, len, iter, pop, setdefault and (k, v) in items() give what the wrapped dict gives, on every dict."
    source := "Doc/library/collections.rst, UserDict: 'simulates a dictionary'"
    status := .proven, prop := ``UserDictMatchesDict, thm := some ``userDictMatchesDict_proven },
  { id := "coll-userdict-set-del", pyFile := file, pyFns := ["UserDict.__setitem__", "UserDict.__delitem__"]
    statement := "u[k] = v then u[k] gives v; del u[k] removes that key only, and raises KeyError(k) when it is absent."
    source := "invariant of a mapping"
    status := .proven, prop := ``UserDictSetDel, thm := some ``userDictSetDel_proven },
  { id := "coll-userdict-constructors-union", pyFile := file
    pyFns := ["UserDict.__init__", "UserDict.__or__", "UserDict.__ror__", "UserDict.__ior__", "UserDict.__copy__",
      "UserDict.copy", "UserDict.fromkeys"]
    statement := "|, |= and the constructors agree with dict's and keep the class, for dict and UserDict operands alike; copy and copy.copy preserve items, order and class."
    source := "Doc/library/collections.rst, UserDict; PEP 584"
    status := .proven, prop := ``UserDictConstructorsUnion, thm := some ``userDictConstructorsUnion_proven },
  { id := "coll-userdict-clear-repr", pyFile := file, pyFns := ["UserDict.__repr__"]
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
    status := .proven, prop := ``UserDictMissingNarrow, thm := some ``userDictMissingNarrow_proven }
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
    status := .proven, prop := ``UserListIntInstance, thm := some ``userListIntInstance_proven }
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
    statement := "Every method taking a str gives the same result for the equal UserString. False: count, find, replace and others unwrap the argument; partition, split, strip, center, join and, on 3.14, startswith do not and raise TypeError."
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
    source := "Lib/collections/__init__.py:1420-1426, :1430-1451, :1478-1481"
    status := .proven, prop := ``UserStringConstructAdd, thm := some ``userStringConstructAdd_proven },
  { id := "coll-userstring-mul", pyFile := file, pyFns := ["UserString.__mul__"]
    statement := "u * n is empty for n <= 0 and has length n * len(u), keeping the class, when that fits Py_ssize_t."
    source := "Doc/builtins/stdtypes.rst, common sequence operations"
    status := .proven, prop := ``UserStringMul, thm := some ``userStringMul_proven }
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
    status := .proven, prop := ``NamedtupleDefaults, thm := some ``namedtupleDefaults_proven }
]

def entries : List Entry :=
  counterEntries ++ chainMapEntries ++ userDictEntries ++ userListEntries ++ userStringEntries ++
    namedtupleEntries

end PyLean.CoreLibs.Coll
