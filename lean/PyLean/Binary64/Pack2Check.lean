import PyLean.Binary64.Float

/-!
The exhaustive half-precision round trip. This file alone takes about a quarter of an
hour in the kernel, so it stays separate and nothing it depends on changes often.
-/

namespace PyLean.Binary64

/-- The check behind `Pack2RoundTrip`: `n` consecutive 16-bit patterns from `lo`, in
both byte orders. -/
def pack2Check (lo : Nat) : Nat → Bool
  | 0 => true
  | n + 1 =>
    decide (PyFloat_Pack2 (PyFloat_Unpack2 (layout 2 (lo + n) false) false) false = .ok (layout 2 (lo + n) false)) &&
    decide (PyFloat_Pack2 (PyFloat_Unpack2 (layout 2 (lo + n) true) true) true = .ok (layout 2 (lo + n) true)) &&
    pack2Check lo n

theorem pack2Check_0 : pack2Check 0 2048 = true := by decide +kernel
theorem pack2Check_1 : pack2Check 2048 2048 = true := by decide +kernel
theorem pack2Check_2 : pack2Check 4096 2048 = true := by decide +kernel
theorem pack2Check_3 : pack2Check 6144 2048 = true := by decide +kernel
theorem pack2Check_4 : pack2Check 8192 2048 = true := by decide +kernel
theorem pack2Check_5 : pack2Check 10240 2048 = true := by decide +kernel
theorem pack2Check_6 : pack2Check 12288 2048 = true := by decide +kernel
theorem pack2Check_7 : pack2Check 14336 2048 = true := by decide +kernel
theorem pack2Check_8 : pack2Check 16384 2048 = true := by decide +kernel
theorem pack2Check_9 : pack2Check 18432 2048 = true := by decide +kernel
theorem pack2Check_10 : pack2Check 20480 2048 = true := by decide +kernel
theorem pack2Check_11 : pack2Check 22528 2048 = true := by decide +kernel
theorem pack2Check_12 : pack2Check 24576 2048 = true := by decide +kernel
theorem pack2Check_13 : pack2Check 26624 2048 = true := by decide +kernel
theorem pack2Check_14 : pack2Check 28672 2048 = true := by decide +kernel
theorem pack2Check_15 : pack2Check 30720 2048 = true := by decide +kernel
theorem pack2Check_16 : pack2Check 32768 2048 = true := by decide +kernel
theorem pack2Check_17 : pack2Check 34816 2048 = true := by decide +kernel
theorem pack2Check_18 : pack2Check 36864 2048 = true := by decide +kernel
theorem pack2Check_19 : pack2Check 38912 2048 = true := by decide +kernel
theorem pack2Check_20 : pack2Check 40960 2048 = true := by decide +kernel
theorem pack2Check_21 : pack2Check 43008 2048 = true := by decide +kernel
theorem pack2Check_22 : pack2Check 45056 2048 = true := by decide +kernel
theorem pack2Check_23 : pack2Check 47104 2048 = true := by decide +kernel
theorem pack2Check_24 : pack2Check 49152 2048 = true := by decide +kernel
theorem pack2Check_25 : pack2Check 51200 2048 = true := by decide +kernel
theorem pack2Check_26 : pack2Check 53248 2048 = true := by decide +kernel
theorem pack2Check_27 : pack2Check 55296 2048 = true := by decide +kernel
theorem pack2Check_28 : pack2Check 57344 2048 = true := by decide +kernel
theorem pack2Check_29 : pack2Check 59392 2048 = true := by decide +kernel
theorem pack2Check_30 : pack2Check 61440 2048 = true := by decide +kernel
theorem pack2Check_31 : pack2Check 63488 2048 = true := by decide +kernel

theorem pack2Check_spec (lo : Nat) : ∀ n, pack2Check lo n = true → ∀ b, lo ≤ b → b < lo + n →
    ∀ le : Bool, PyFloat_Pack2 (PyFloat_Unpack2 (layout 2 b le) le) le = .ok (layout 2 b le) := by
  intro n
  induction n with
  | zero => intro _ b _ hb; omega
  | succ n ih =>
    intro h b hl hb le
    simp only [pack2Check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    by_cases hbn : b = lo + n
    · subst hbn
      cases le
      · exact h1
      · exact h2
    · exact ih h3 b hl (by omega) le

/-- `struct.pack('e', struct.unpack('e', b))` gives back every one of the 65536 half
precision patterns, NaN payloads included, in both byte orders. -/
def Pack2RoundTrip : Prop :=
  ∀ b, b < 65536 → ∀ le : Bool,
    PyFloat_Pack2 (PyFloat_Unpack2 (layout 2 b le) le) le = .ok (layout 2 b le)

theorem pack2RoundTrip_proven : Pack2RoundTrip := by
  intro b hb le
  by_cases h0 : b < 2048
  · exact pack2Check_spec 0 2048 pack2Check_0 b (by omega) (by omega) le
  by_cases h1 : b < 4096
  · exact pack2Check_spec 2048 2048 pack2Check_1 b (by omega) (by omega) le
  by_cases h2 : b < 6144
  · exact pack2Check_spec 4096 2048 pack2Check_2 b (by omega) (by omega) le
  by_cases h3 : b < 8192
  · exact pack2Check_spec 6144 2048 pack2Check_3 b (by omega) (by omega) le
  by_cases h4 : b < 10240
  · exact pack2Check_spec 8192 2048 pack2Check_4 b (by omega) (by omega) le
  by_cases h5 : b < 12288
  · exact pack2Check_spec 10240 2048 pack2Check_5 b (by omega) (by omega) le
  by_cases h6 : b < 14336
  · exact pack2Check_spec 12288 2048 pack2Check_6 b (by omega) (by omega) le
  by_cases h7 : b < 16384
  · exact pack2Check_spec 14336 2048 pack2Check_7 b (by omega) (by omega) le
  by_cases h8 : b < 18432
  · exact pack2Check_spec 16384 2048 pack2Check_8 b (by omega) (by omega) le
  by_cases h9 : b < 20480
  · exact pack2Check_spec 18432 2048 pack2Check_9 b (by omega) (by omega) le
  by_cases h10 : b < 22528
  · exact pack2Check_spec 20480 2048 pack2Check_10 b (by omega) (by omega) le
  by_cases h11 : b < 24576
  · exact pack2Check_spec 22528 2048 pack2Check_11 b (by omega) (by omega) le
  by_cases h12 : b < 26624
  · exact pack2Check_spec 24576 2048 pack2Check_12 b (by omega) (by omega) le
  by_cases h13 : b < 28672
  · exact pack2Check_spec 26624 2048 pack2Check_13 b (by omega) (by omega) le
  by_cases h14 : b < 30720
  · exact pack2Check_spec 28672 2048 pack2Check_14 b (by omega) (by omega) le
  by_cases h15 : b < 32768
  · exact pack2Check_spec 30720 2048 pack2Check_15 b (by omega) (by omega) le
  by_cases h16 : b < 34816
  · exact pack2Check_spec 32768 2048 pack2Check_16 b (by omega) (by omega) le
  by_cases h17 : b < 36864
  · exact pack2Check_spec 34816 2048 pack2Check_17 b (by omega) (by omega) le
  by_cases h18 : b < 38912
  · exact pack2Check_spec 36864 2048 pack2Check_18 b (by omega) (by omega) le
  by_cases h19 : b < 40960
  · exact pack2Check_spec 38912 2048 pack2Check_19 b (by omega) (by omega) le
  by_cases h20 : b < 43008
  · exact pack2Check_spec 40960 2048 pack2Check_20 b (by omega) (by omega) le
  by_cases h21 : b < 45056
  · exact pack2Check_spec 43008 2048 pack2Check_21 b (by omega) (by omega) le
  by_cases h22 : b < 47104
  · exact pack2Check_spec 45056 2048 pack2Check_22 b (by omega) (by omega) le
  by_cases h23 : b < 49152
  · exact pack2Check_spec 47104 2048 pack2Check_23 b (by omega) (by omega) le
  by_cases h24 : b < 51200
  · exact pack2Check_spec 49152 2048 pack2Check_24 b (by omega) (by omega) le
  by_cases h25 : b < 53248
  · exact pack2Check_spec 51200 2048 pack2Check_25 b (by omega) (by omega) le
  by_cases h26 : b < 55296
  · exact pack2Check_spec 53248 2048 pack2Check_26 b (by omega) (by omega) le
  by_cases h27 : b < 57344
  · exact pack2Check_spec 55296 2048 pack2Check_27 b (by omega) (by omega) le
  by_cases h28 : b < 59392
  · exact pack2Check_spec 57344 2048 pack2Check_28 b (by omega) (by omega) le
  by_cases h29 : b < 61440
  · exact pack2Check_spec 59392 2048 pack2Check_29 b (by omega) (by omega) le
  by_cases h30 : b < 63488
  · exact pack2Check_spec 61440 2048 pack2Check_30 b (by omega) (by omega) le
  by_cases h31 : b < 65536
  · exact pack2Check_spec 63488 2048 pack2Check_31 b (by omega) (by omega) le
  omega

end PyLean.Binary64
