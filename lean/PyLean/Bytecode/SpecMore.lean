import PyLean.Bytecode.SpecHeap

/-!
The other specialized families. As in `SpecHeap.lean`: every theorem is for all
stacks. A guard that fails falls back, so the only hypotheses are the laws of the
object model, a live stack, and the specializer's choice of family member.
-/

namespace PyLean.Bytecode

open Uop

/-- `oparg` of `COMPARE_OP`: the operator in the high bits, the outcome mask
`compare_masks[op]` of `Python/compile.c` in the low four, bit 4 for "convert to
bool". -/
def compareMask : Nat → Nat
  | 0 => 2 | 1 => 10 | 2 => 8 | 3 => 7 | 4 => 4 | _ => 12

def compareOparg (op : Nat) (toBool : Bool) : Nat :=
  op * 32 + compareMask op + (if toBool then 16 else 0)

/-- `long_richcompare`'s result on a comparison, as `_COMPARE_OP_INT` computes it. -/
theorem compare_bits (op : Nat) (hop : op < 6) (tb : Bool) (a b : Int) :
    (comparisonBit (decide (a ≥ b)) (decide (a ≤ b)) &&& compareOparg op tb != 0) =
      (match op with
        | 0 => decide (a < b) | 1 => decide (a ≤ b) | 2 => decide (a = b)
        | 3 => decide (a ≠ b) | 4 => decide (a > b) | _ => decide (a ≥ b)) := by
  rcases Int.lt_trichotomy a b with h | h | h
  · have h1 : ¬ a ≥ b := by omega
    have h2 : a ≤ b := by omega
    have h3 : a ≠ b := by omega
    have h4 : ¬ a > b := by omega
    interval_cases_op
  · subst h
    interval_cases_eq
  · have h1 : a ≥ b := by omega
    have h2 : ¬ a ≤ b := by omega
    have h3 : a ≠ b := by omega
    have h4 : ¬ a < b := by omega
    interval_cases_gt
where
  _unused : Unit := ()

end PyLean.Bytecode
