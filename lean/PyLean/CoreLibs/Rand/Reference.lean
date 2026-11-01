import PyLean.CoreLibs.Rand.Mt

/-!
Conformance of the model with the published MT19937 reference output, checked in
the kernel. In a separate file because this one takes minutes.
-/

namespace PyLean.CoreLibs.Rand

/-- The published MT19937 reference vector (`mt19937ar.out`):
`init_by_array({0x123, 0x234, 0x345, 0x456}, 4)` followed by `genrand_int32`. -/
def ReferenceVector : Prop :=
  (stream 5 (initByArray genericNew #[0x123, 0x234, 0x345, 0x456])).map UInt32.toNat
    = [1067595299, 955945823, 477289528, 4107218783, 4228976476]

set_option maxRecDepth 100000 in
theorem referenceVector_proven : ReferenceVector := by
  unfold ReferenceVector
  decide +kernel

end PyLean.CoreLibs.Rand
