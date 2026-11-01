import PyLean.Registry
import PyLean.CoreLibs.EnumDC.Diff
import PyLean.CoreLibs.EnumDC.Props

/-! Registry for the `EnumDC` area of CoreLibs: Lib/enum.py, Lib/dataclasses.py, CPython 3.14.7. -/

namespace PyLean.CoreLibs.EnumDC

open PyLean.Registry

def entries : List Entry := [
  { id := "corelibs-enum-flag-ops-commute"
    pyFile := "Lib/enum.py"
    pyFns := []
    statement := "|, & and ^ on two values of a Flag class commute under every boundary."
    source := "Flag docs"
    status := .proven
    prop := ``FlagOpsCommute
    thm := some ``flagOpsCommute_proven },
  { id := "corelibs-enum-flag-contains"
    pyFile := "Lib/enum.py"
    pyFns := []
    statement := "other in self is bit containment."
    source := "docstring of Flag.__contains__"
    status := .proven
    prop := ``FlagContainsBits
    thm := some ``flagContainsBits_proven },
  { id := "corelibs-enum-conform"
    pyFile := "Lib/enum.py"
    pyFns := ["Flag._missing_"]
    statement := "Under CONFORM an out-of-range value keeps only defined bits."
    source := "FlagBoundary docs"
    status := .proven
    prop := ``ConformKeepsMask
    thm := some ``conformKeepsMask_proven },
  { id := "corelibs-enum-strict-named"
    pyFile := "Lib/enum.py"
    pyFns := ["Flag._missing_", "Enum.__new__"]
    statement := "A nonzero value accepted by a STRICT flag class has a name."
    source := "FlagBoundary.STRICT docs; the check at Lib/enum.py:1526"
    status := .refuted
    prop := ``StrictValuesAreNamed
    thm := some ``strictValuesAreNamed_refuted
    bug := some "corelibs-enum-strict-unnamed-bit" },
  { id := "corelibs-enum-len-iter"
    pyFile := "Lib/enum.py"
    pyFns := ["Flag.__len__", "Flag.__iter__", "Flag._iter_member_by_value_", "_iter_bits_lsb"]
    statement := "len(x) is the number of members iter(x) yields."
    source := "Doc/library/enum.rst: Returns number of members in flag"
    status := .refuted
    prop := ``LenMatchesIter
    thm := some ``lenMatchesIter_refuted
    bug := some "corelibs-enum-flag-len-counts-unknown-bits" },
  { id := "corelibs-enum-auto-values"
    pyFile := "Lib/enum.py"
    pyFns := []
    statement := "The auto() value rules: Enum follows the largest value, and Flag starts at start or 1."
    source := "enum docs on auto"
    status := .proven
    prop := ``AutoValues
    thm := some ``autoValues_proven },
  { id := "corelibs-enum-flag-repr"
    pyFile := "Lib/enum.py"
    pyFns := []
    statement := "repr and str of a flag show its name, or the number when nameless."
    source := "Flag docs"
    status := .proven
    prop := ``FlagReprShape
    thm := some ``flagReprShape_proven },
  { id := "corelibs-dataclasses-hash-table"
    pyFile := "Lib/dataclasses.py"
    pyFns := []
    statement := "The sixteen rows of _hash_action are one rule on unsafe_hash, eq, frozen and an explicit __hash__."
    source := "dataclass docs on hash"
    status := .proven
    prop := ``HashTableIsRule
    thm := some ``hashTableIsRule_proven },
  { id := "corelibs-dataclasses-init-order"
    pyFile := "Lib/dataclasses.py"
    pyFns := ["_fields_in_init_order"]
    statement := "A field reaches __init__ exactly when init is true, positional ones first."
    source := "dataclass docs"
    status := .proven
    prop := ``InitOrderPartition
    thm := some ``initOrderPartition_proven },
  { id := "corelibs-dataclasses-default-order"
    pyFile := "Lib/dataclasses.py"
    pyFns := []
    statement := "An accepted class has no init field without default after one with a default."
    source := "dataclass docs"
    status := .proven
    prop := ``InitDefaultOrderSound
    thm := some ``initDefaultOrderSound_proven },
  { id := "corelibs-dataclasses-helpers"
    pyFile := "Lib/dataclasses.py"
    pyFns := []
    statement := "_tuple_str keeps a single field a tuple, fields lists no pseudo-field, field rejects both defaults."
    source := "dataclass docs"
    status := .proven
    prop := ``DataclassHelpers
    thm := some ``dataclassHelpers_proven },
  { id := "corelibs-dataclasses-replace"
    pyFile := "Lib/dataclasses.py"
    pyFns := []
    statement := "replace keeps the changes and adds every other field from the instance."
    source := "dataclasses.replace docs"
    status := .proven
    prop := ``ReplaceFillsFields
    thm := some ``replaceFillsFields_proven }
]

end PyLean.CoreLibs.EnumDC
