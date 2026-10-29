import PyLean.Ipaddress.Spec

/-!
`summarize_address_range`.
-/

namespace PyLean.Ipaddress

open PyLean

/-- `summarize_address_range` docstring, ipaddress.py:201-232: for
`first <= last` it returns networks that cover exactly the range
`first..last`, in ascending order, each a valid network of the same version. -/
def SummarizeExactCover : Prop :=
  ∀ bits first last : Nat, IsVersion bits → first ≤ last → last < 2 ^ bits →
    ∃ nets, summarizeAddressRange bits first last = .ok nets ∧
      (∀ n ∈ nets, n.bits = bits ∧ n.Valid) ∧ Tiles nets first last

theorem summarizeExactCover_proven : SummarizeExactCover := by
  sorry

/-- The docstring's error contract: `first > last` raises `ValueError`. -/
def SummarizeRejectsReversed : Prop :=
  ∀ bits first last : Nat, first > last →
    summarizeAddressRange bits first last =
      .error (.valueError "last IP address must be greater than first")

theorem summarizeRejectsReversed_proven : SummarizeRejectsReversed := by
  intro bits first last h
  simp [summarizeAddressRange, h]

end PyLean.Ipaddress
