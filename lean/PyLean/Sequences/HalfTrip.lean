import PyLean.Sequences.FloatBits

/-!
The round trip of every binary16 pattern through `e_getitem` and `e_setitem`
(`Modules/arraymodule.c:618-641`): `PyFloat_Unpack2`, the `float` of `PyArg_Parse("f")`,
its promotion to `double`, `PyFloat_Pack2`. The 65536 patterns are checked by the kernel, in
chunks of 8192.
-/

namespace PyLean.Sequences

open PyLean

/-! ### Round trips -/

/-- A binary16 pattern with its quiet bit set if it is a signalling NaN (exponent all ones,
fraction non-zero, bit 9 clear). -/
def quiet16 (h : Nat) : Nat :=
  if 31744 < h % 32768 ∧ h % 1024 < 512 then h + 512 else h

/-- What `e_setitem` stores for the value `e_getitem` read from the half pattern `h`. -/
def eTrip (h : Nat) : Py Nat := packHalf (floatToDouble (doubleToFloat (halfToDouble h)))

def eTripOk (h : Nat) : Bool := eTrip h == .ok (quiet16 h)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem eTrip_0 : ∀ k < 8, ∀ lo < 1024, eTripOk (k * 1024 + lo) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem eTrip_1 : ∀ k < 8, ∀ lo < 1024, eTripOk ((8 + k) * 1024 + lo) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem eTrip_2 : ∀ k < 8, ∀ lo < 1024, eTripOk ((16 + k) * 1024 + lo) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem eTrip_3 : ∀ k < 8, ∀ lo < 1024, eTripOk ((24 + k) * 1024 + lo) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem eTrip_4 : ∀ k < 8, ∀ lo < 1024, eTripOk ((32 + k) * 1024 + lo) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem eTrip_5 : ∀ k < 8, ∀ lo < 1024, eTripOk ((40 + k) * 1024 + lo) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem eTrip_6 : ∀ k < 8, ∀ lo < 1024, eTripOk ((48 + k) * 1024 + lo) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem eTrip_7 : ∀ k < 8, ∀ lo < 1024, eTripOk ((56 + k) * 1024 + lo) = true := by decide +kernel

theorem eTrip_all (h : Nat) (hh : h < 65536) : eTrip h = .ok (quiet16 h) := by
  have hk : h / 1024 < 64 := by omega
  have hl : h % 1024 < 1024 := Nat.mod_lt _ (by decide)
  have he : h = h / 1024 * 1024 + h % 1024 := by omega
  have r : eTripOk h = true := by
    rw [he]
    generalize h / 1024 = k at hk
    generalize h % 1024 = lo at hl
    by_cases c0 : k < 8
    · exact eTrip_0 k c0 lo hl
    by_cases c1 : k < 16
    · have := eTrip_1 (k - 8) (by omega) lo hl; rwa [show 8 + (k - 8) = k by omega] at this
    by_cases c2 : k < 24
    · have := eTrip_2 (k - 16) (by omega) lo hl; rwa [show 16 + (k - 16) = k by omega] at this
    by_cases c3 : k < 32
    · have := eTrip_3 (k - 24) (by omega) lo hl; rwa [show 24 + (k - 24) = k by omega] at this
    by_cases c4 : k < 40
    · have := eTrip_4 (k - 32) (by omega) lo hl; rwa [show 32 + (k - 32) = k by omega] at this
    by_cases c5 : k < 48
    · have := eTrip_5 (k - 40) (by omega) lo hl; rwa [show 40 + (k - 40) = k by omega] at this
    by_cases c6 : k < 56
    · have := eTrip_6 (k - 48) (by omega) lo hl; rwa [show 48 + (k - 48) = k by omega] at this
    · have := eTrip_7 (k - 56) (by omega) lo hl; rwa [show 56 + (k - 56) = k by omega] at this
  unfold eTripOk at r
  exact beq_iff_eq.mp r

end PyLean.Sequences
