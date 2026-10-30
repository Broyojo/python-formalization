import PyLean.Registry
import PyLean.StrSearch.Diff
import PyLean.StrSearch.Model
import PyLean.StrSearch.Basic
import PyLean.StrSearch.Find
import PyLean.StrSearch.Pad
import PyLean.StrSearch.Strip

/-!
Search and split methods of `str`, `bytes`, `bytearray`: `Objects/stringlib/`, `Objects/unicodeobject.c`, `Objects/bytes_methods.c`, CPython 3.14.7.
-/

namespace PyLean.StrSearch

open PyLean.Registry

def entries : List Entry := [
  { id := "strsearch-find-str-bytes", pyFile := "Objects/unicodeobject.c"
    pyFns := ["str.find", "str.rfind", "str.index", "str.rindex", "str.count",
      "bytes.find", "bytes.rfind", "bytes.index", "bytes.rindex", "bytes.count"]
    statement := "For byte-valued strings, str and bytes agree on find/rfind/index/rindex/count for every start/end, and bytes accepts an int v in range(256) exactly like bytes([v])."
    source := "invariant: str vs bytes (any_find_slice, unicodeobject.c:9681-9761, vs find_internal, bytes_methods.c:452-509)"
    status := .proven, prop := ``FindStrBytes, thm := some ``findStrBytes_proven
    notes := "index/rindex messages differ ('substring not found' vs 'subsection not found'); the property compares the outcomes." },
  { id := "strsearch-find-extreme", pyFile := "Objects/unicodeobject.c"
    pyFns := ["str.find", "str.rfind"]
    statement := "find returns the least and rfind the greatest i with start' <= i and i + len(sub) <= end' and s[i:i+len(sub)] == sub (start', end' normalised by ADJUST_INDICES), or -1 if there is none."
    source := "find/rfind docstrings, read as in python/cpython#68431"
    status := .proven, prop := ``FindExtreme, thm := some ``findExtreme_proven
    notes := "Holds for every str (any kinds) and every start/end, including +-2**63 and beyond (clamped by slice_index)." },
  { id := "strsearch-find-slice-literal", pyFile := "Objects/unicodeobject.c"
    pyFns := ["str.find", "str.count", "str.startswith"]
    statement := "s.find/count/startswith(sub, start, end) equal the same operation on the slice s[start:end] (find shifted by the slice start)."
    source := "find docstring ('such that sub is contained within S[start:end]'), count docstring, Doc/library/stdtypes.rst"
    status := .refuted, prop := ``FindSliceLiteral, thm := some ``findSliceLiteral_refuted
    bug := some "strsearch-empty-sub-past-slice-end"
    notes := "Only an empty sub with start' > end' (after ADJUST_INDICES) differs; known as python/cpython#68431 (open). See strsearch-find-extreme for the reading that holds." },
  { id := "strsearch-tailmatch-str-bytes", pyFile := "Objects/bytes_methods.c"
    pyFns := ["str.startswith", "str.endswith", "bytes.startswith", "bytes.endswith"]
    statement := "The two tailmatch implementations agree: str.startswith/endswith and bytes.startswith/endswith give the same answer for every receiver, prefix or tuple, start and end."
    source := "invariant: str vs bytes (unicodeobject.c:9946-10007 vs bytes_methods.c:640-686)"
    status := .proven, prop := ``TailmatchStrBytes, thm := some ``tailmatchStrBytes_proven },
  { id := "strsearch-rfind-reverse", pyFile := "Objects/stringlib/fastsearch.h"
    pyFns := ["str.rfind", "str.find"]
    statement := "s.rfind(sub) == len(s) - len(sub) - s[::-1].find(sub[::-1]) when the latter is found, and -1 otherwise."
    source := "invariant: rfind is find from the right (default_rfind vs default_find/two-way)"
    status := .proven, prop := ``RFindReverse, thm := some ``rfindReverse_proven
    notes := "Precondition len(s) <= sys.maxsize (type invariant)." },
  { id := "strsearch-count-repeated-find", pyFile := "Objects/unicodeobject.c"
    pyFns := ["str.count", "str.find"]
    statement := "For non-empty sub, s.count(sub, start, end) equals the number of rounds of i = start; while (j := s.find(sub, i, end)) >= 0: i = j + len(sub)."
    source := "count docstring ('non-overlapping occurrences'); method vs equivalent method"
    status := .proven, prop := ``CountRepeatedFind, thm := some ``countRepeatedFind_proven
    notes := "Precondition len(s) < sys.maxsize (type invariant)." },
  { id := "strsearch-partition-find", pyFile := "Objects/stringlib/partition.h"
    pyFns := ["str.partition", "str.rpartition", "bytes.partition", "bytes.rpartition"]
    statement := "partition(sep) is (s[:i], sep, s[i+len(sep):]) for i = s.find(sep), or (s, '', '') when i == -1; rpartition likewise with rfind and ('', '', s); empty sep raises ValueError."
    source := "partition/rpartition docstrings; method vs equivalent method"
    status := .proven, prop := ``PartitionFind, thm := some ``partitionFind_proven
    notes := "Values only: bytes.partition returns the separator object itself (python/cpython#137217, not modelled)." },
  { id := "strsearch-pad-str-bytes", pyFile := "Objects/stringlib/transmogrify.h"
    pyFns := ["str.center", "str.ljust", "str.rjust", "str.zfill", "bytes.center", "bytes.ljust",
      "bytes.rjust", "bytes.zfill"]
    statement := "str and bytes agree on center/ljust/rjust/zfill for every width and fill; the OverflowError branch of str's pad is unreachable for a Py_ssize_t width."
    source := "invariant: str vs bytes (pad, unicodeobject.c:10492-10531, vs transmogrify.h:103-246)"
    status := .proven, prop := ``PadStrBytes, thm := some ``padStrBytes_proven
    notes := "Allocation failures are not modelled: for width near sys.maxsize str raises MemoryError and bytes OverflowError('byte string is too large')." },
  { id := "strsearch-center-balanced", pyFile := "Objects/unicodeobject.c"
    pyFns := ["str.center"]
    statement := "s.center(width) is s when width <= len(s), else s padded with l fills before and r after, l + len(s) + r == width, |l - r| <= 1."
    source := "center docstring and stdtypes.rst:1889-1893"
    status := .proven, prop := ``CenterBalanced, thm := some ``centerBalanced_proven },
  { id := "strsearch-zfill-spec", pyFile := "Objects/unicodeobject.c"
    pyFns := ["str.zfill"]
    statement := "s.zfill(width) is s when width <= len(s); otherwise '0' * (width - len(s)) is inserted after a leading '+'/'-', or before s."
    source := "zfill docstring and stdtypes.rst:2892-2898"
    status := .proven, prop := ``ZfillSpec, thm := some ``zfillSpec_proven },
  { id := "strsearch-expandtabs-str-bytes", pyFile := "Objects/stringlib/transmogrify.h"
    pyFns := ["str.expandtabs", "bytes.expandtabs"]
    statement := "str.expandtabs and bytes.expandtabs return the same expansion when it has at most sys.maxsize characters and both raise OverflowError otherwise, for every C int tabsize (negative and zero included)."
    source := "invariant: str vs bytes, no silent wraparound (unicodeobject.c:11893-11917 vs transmogrify.h:44-70)"
    status := .proven, prop := ``ExpandtabsStrBytes, thm := some ``expandtabsStrBytes_proven
    notes := "The two first passes use different overflow checks (running total vs per-line column + line sums); both are exact." },
  { id := "strsearch-strip-paths", pyFile := "Objects/unicodeobject.c"
    pyFns := ["str.strip", "str.lstrip", "str.rstrip", "bytes.strip", "bytearray.strip"]
    statement := "str.strip()'s ASCII fast path agrees with the general path; bytearray.strip()'s explicit whitespace list agrees with bytes'; str and bytes agree with chars given, and without chars on byte strings free of \\x1c-\\x1f, \\x85, \\xa0."
    source := "invariant: fast vs slow path, bytes vs bytearray, str vs bytes"
    status := .proven, prop := ``StripPaths, thm := some ``stripPaths_proven },
  { id := "strsearch-splitlines-str-bytes", pyFile := "Objects/stringlib/split.h"
    pyFns := ["str.splitlines", "bytes.splitlines"]
    statement := "str.splitlines and bytes.splitlines agree on byte strings without \\v, \\f, \\x1c-\\x1e, \\x85; splitlines(True) concatenates back to the string."
    source := "invariant: str vs bytes away from the documented line-boundary differences; round trip"
    status := .proven, prop := ``SplitlinesStrBytes, thm := some ``splitlinesStrBytes_proven }
]

end PyLean.StrSearch
