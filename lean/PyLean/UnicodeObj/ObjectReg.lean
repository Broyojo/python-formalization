import PyLean.Registry
import PyLean.UnicodeObj.ObjectKinds
import PyLean.UnicodeObj.ObjectWriterProps

/-! Registry entries of the object slice. -/

namespace PyLean.UnicodeObj

open PyLean.Registry

def objectEntries : List Entry := [
  { id := "unicodeobj-writer-text", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicodeWriter_WriteStr", "PyUnicodeWriter_WriteRepr", "PyUnicodeWriter_WriteASCII",
      "PyUnicodeWriter_WriteWideChar", "find_maxchar_surrogates", "PyUnicodeWriter_WriteUTF8"]
    statement := "For every script of writer operations, the text is what the successful ones wrote, in order: WriteStr is str(), WriteRepr is repr(), a decode is bytes.decode, each raises what they raise, and a failed operation leaves no characters."
    source := "implementation against itself: the exact-str and exact-int fast paths and the writer's decoder against the object-level functions; Doc/c-api/unicode.rst"
    status := .proven, prop := ``WriterText, thm := some ``writerText_proven },
  { id := "unicodeobj-writer-consumed", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "PyUnicodeWriter_DecodeUTF8Stateful writes the text and reports the *consumed of PyUnicode_DecodeUTF8Stateful, for every built-in handler."
    source := "implementation against itself: the writer path against the stateful decoder; Doc/c-api/unicode.rst"
    status := .proven, prop := ``WriterConsumed, thm := some ``writerConsumed_proven },
  { id := "unicodeobj-writer-consumed-failure", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "When the stateful decoder raises, PyUnicodeWriter_DecodeUTF8Stateful raises the same exception, keeps no text, and sets *consumed to 0, for every built-in handler."
    source := "implementation against itself: the writer path against the stateful decoder; unicodeobject.c:14185-14190"
    status := .proven, prop := ``WriterConsumedFailure, thm := some ``writerConsumedFailure_proven },
  { id := "unicodeobj-writer-cap-value", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "writer->maxchar stays the limit of a kind through every operation, failed ones included."
    source := "invariant: _PyUnicodeWriter_Update"
    status := .proven, prop := ``WriterCapValue, thm := some ``writerCapValue_proven },
  { id := "unicodeobj-writer-finish-canonical", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicodeWriter_Create", "_PyUnicodeWriter_Init", "PyUnicodeWriter_Finish", "unicode_result"]
    statement := "Unless a decode fails, the str that PyUnicodeWriter_Finish returns has the canonical kind, for every script from any PyUnicodeWriter_Create."
    source := "invariant: _PyUnicode_CheckConsistency"
    status := .proven, prop := ``WriterFinishCanonical, thm := some ``writerFinishCanonical_proven },
  { id := "unicodeobj-writer-always-canonical", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "The str that PyUnicodeWriter_Finish returns has the canonical kind for every script, failed decodes included."
    source := "invariant: _PyUnicode_CheckConsistency"
    status := .refuted, prop := ``WriterAlwaysCanonical, thm := some ``writerAlwaysCanonical_refuted
    bug := some "unicodeobj-writer-rollback-noncanonical" },
  { id := "unicodeobj-writer-failure-keeps-state", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "An operation other than a decode leaves the writer unchanged when it fails."
    source := "Doc/c-api/unicode.rst: On error, set an exception, leave the writer unchanged"
    status := .proven, prop := ``WriterFailureKeepsState, thm := some ``writerFailureKeepsState_proven },
  { id := "unicodeobj-writer-failure-unobservable", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "After any failed operation, Finish and every later write behave as if it had not been made."
    source := "Doc/c-api/unicode.rst: On error, set an exception, leave the writer unchanged"
    status := .refuted, prop := ``WriterFailureUnobservable, thm := some ``writerFailureUnobservable_refuted
    bug := some "unicodeobj-writer-rollback-noncanonical" },
  { id := "unicodeobj-writer-paths-agree", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicodeWriter_WriteChar", "_PyUnicodeWriter_WriteChar", "_PyUnicodeWriter_WriteCharInline",
      "PyUnicodeWriter_WriteUCS4"]
    statement := "WriteStr, WriteUCS4, WriteWideChar, WriteSubstring of all of it, WriteChar for each character, and WriteUTF8 or DecodeUTF8Stateful of its encoding leave the same writer, from every writer."
    source := "implementation against itself: six ways to write one string"
    status := .proven, prop := ``WriterPathsAgree, thm := some ``writerPathsAgree_proven },
  { id := "unicodeobj-writer-substring-slice", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicodeWriter_WriteSubstring", "_PyUnicodeWriter_WriteSubstring"]
    statement := "WriteSubstring(s, a, b) is WriteStr(s[a:b]) for every in-range slice and every writer, whichever way the kind check goes."
    source := "implementation against itself: the scan skipped when the whole string's kind fits"
    status := .proven, prop := ``WriterSubstringIsSlice, thm := some ``writerSubstringIsSlice_proven },
  { id := "unicodeobj-object-isascii-kind", pyFile := "Objects/unicodeobject.c"
    pyFns := []
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
