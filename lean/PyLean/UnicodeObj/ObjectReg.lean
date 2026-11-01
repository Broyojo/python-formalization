import PyLean.Registry
import PyLean.UnicodeObj.ObjectKinds

/-! Registry entries of the object slice. -/

namespace PyLean.UnicodeObj

open PyLean.Registry

def objectEntries : List Entry := [
  { id := "unicodeobj-object-isascii-kind", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_isascii_impl"]
    statement := "PyUnicode_IS_ASCII, a flag of the representation, holds exactly when every character is below 128."
    source := "invariant: PEP 393 canonical kind"
    status := .proven, prop := ``IsAsciiKind, thm := some ``isAsciiKind_proven },
  { id := "unicodeobj-object-concat-kind", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "str + str allocates the canonical kind of the result, from the operands' kinds alone."
    source := "invariant: PEP 393 canonical kind (_PyUnicode_CheckConsistency)"
    status := .proven, prop := ``ConcatKind, thm := some ``concatKind_proven },
  { id := "unicodeobj-object-slice-kind", pyFile := "Objects/unicodeobject.c"
    pyFns := ["kind_maxchar_limit"]
    statement := "An extended slice allocates the canonical kind of its result, despite the early break of its max_char loop."
    source := "invariant: PEP 393 canonical kind (_PyUnicode_CheckConsistency)"
    status := .proven, prop := ``SliceKind, thm := some ``sliceKind_proven },
  { id := "unicodeobj-object-repeat-length", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_repeat"]
    statement := "s * n has n * len(s) characters, and OverflowError is raised exactly when that exceeds PY_SSIZE_T_MAX."
    source := "invariant: no silent wraparound"
    status := .proven, prop := ``RepeatLength, thm := some ``repeatLength_proven },
  { id := "unicodeobj-object-compare-order", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "unicode_compare is antisymmetric and is 0 exactly on equal strings."
    source := "invariant: total order on code points"
    status := .proven, prop := ``CompareOrder, thm := some ``compareOrder_proven
    notes := "The twelve kind pairs and memcmp paths are modelled by their result; difftested through ==, < and sorted." }
]

end PyLean.UnicodeObj
