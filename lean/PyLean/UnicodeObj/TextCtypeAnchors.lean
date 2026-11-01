import PyLean.UnicodeObj.TextProps2

/-!
What `CaseTables` cannot say. It checks that the tables agree with each other, and a table of
identity mappings would too. Here the tables are compared with an independent definition, the
ASCII rules, on all of ASCII: an always-true predicate, an identity case map or a record lookup that
ignores its index all fail.

This pins the functions, not the data above 127, which rests on the difftest and on `CaseTables`.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- `unicodectype.c` on ASCII. The predicates and the case maps are compared with the ranges of the
ASCII table, for every one of the 128 characters. -/
def CtypeAscii : Prop :=
  ∀ c, c < 128 →
    isUppercase c = decide (65 ≤ c ∧ c ≤ 90) ∧
    isLowercase c = decide (97 ≤ c ∧ c ≤ 122) ∧
    isTitlecase c = false ∧
    isCased c = decide ((65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122)) ∧
    isXidStart c = decide ((65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122)) ∧
    isXidContinue c = decide ((65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122) ∨ (48 ≤ c ∧ c ≤ 57) ∨ c = 95) ∧
    toDecimalDigit c = (if 48 ≤ c ∧ c ≤ 57 then (c : Int) - 48 else -1) ∧
    toDigit c = (if 48 ≤ c ∧ c ≤ 57 then (c : Int) - 48 else -1) ∧
    isDecimalDigit c = decide (48 ≤ c ∧ c ≤ 57) ∧
    isDigit c = decide (48 ≤ c ∧ c ≤ 57) ∧
    isNumeric c = decide (48 ≤ c ∧ c ≤ 57) ∧
    toUppercase c = (if 97 ≤ c ∧ c ≤ 122 then c - 32 else c) ∧
    toLowercase c = (if 65 ≤ c ∧ c ≤ 90 then c + 32 else c) ∧
    toTitlecase c = (if 97 ≤ c ∧ c ≤ 122 then c - 32 else c) ∧
    toUpperFull c = [if 97 ≤ c ∧ c ≤ 122 then c - 32 else c] ∧
    toLowerFull c = [if 65 ≤ c ∧ c ≤ 90 then c + 32 else c] ∧
    toTitleFull c = [if 97 ≤ c ∧ c ≤ 122 then c - 32 else c] ∧
    toFoldedFull c = [if 65 ≤ c ∧ c ≤ 90 then c + 32 else c]

theorem ctypeAscii_proven : CtypeAscii := by
  unfold CtypeAscii
  decide +kernel

end PyLean.UnicodeObj
