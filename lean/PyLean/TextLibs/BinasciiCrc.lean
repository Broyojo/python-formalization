import PyLean.TextLibs.BinasciiProps2

/-!
`crc_hqx` against the bitwise definition of CRC-CCITT: for every byte, xor it into the top of the
16-bit register, then eight times shift left and xor in the polynomial `0x1021` when a bit falls out.
The table step of `Modules/binascii.c:2010` is that, for every register value and byte.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

theorem xor_mul2pow (a b n : Nat) : (a ^^^ b) * 2 ^ n = a * 2 ^ n ^^^ b * 2 ^ n := by
  rw [← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq, Nat.shiftLeft_xor_distrib]

theorem xor_disj (q r n : Nat) (h : r < 2 ^ n) : q * 2 ^ n ^^^ r = q * 2 ^ n + r := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_mul_two_pow, Nat.mul_comm q, Nat.testBit_two_pow_mul_add _ h]
  by_cases hj : j < n
  · have : ¬ n ≤ j := by omega
    simp [hj, this]
  · have hr : r.testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))
    have : n ≤ j := by omega
    simp [hj, this, hr]

/-- One turn of the bit loop. -/
def crcShift (crc : Nat) : Nat :=
  let c := crc * 2
  if c ≥ 65536 then (c - 65536) ^^^ 0x1021 else c

theorem crcBit_succ (crc i : Nat) : crcBit crc (i + 1) = crcBit (crcShift crc) i := rfl

theorem crcShift_form (z : Nat) (hz : z < 65536) :
    crcShift z = (z * 2 % 2 ^ 16) ^^^ (if z / 2 ^ 15 % 2 = 1 then 0x1021 else 0) := by
  unfold crcShift
  by_cases h : z ≥ 32768
  · have e1 : z / 2 ^ 15 % 2 = 1 := by omega
    have e2 : z * 2 - 65536 = z * 2 % 2 ^ 16 := by omega
    simp only [e1, if_true, if_pos (by omega : z * 2 ≥ 65536), e2]
  · have e1 : z / 2 ^ 15 % 2 = 0 := by omega
    have e2 : z * 2 = z * 2 % 2 ^ 16 := by omega
    simp only [e1, if_neg (by omega : ¬ z * 2 ≥ 65536), Nat.zero_ne_one, if_false, Nat.xor_zero]
    exact e2

theorem crcShift_lt (z : Nat) (hz : z < 65536) : crcShift z < 65536 := by
  rw [crcShift_form z hz]
  apply Nat.xor_lt_two_pow (n := 16) (Nat.mod_lt _ (by decide))
  split <;> decide

theorem crcShift_xor (x y : Nat) (hx : x < 65536) (hy : y < 65536) :
    crcShift (x ^^^ y) = crcShift x ^^^ crcShift y := by
  have hxy : x ^^^ y < 65536 := Nat.xor_lt_two_pow (n := 16) hx hy
  rw [crcShift_form _ hxy, crcShift_form _ hx, crcShift_form _ hy]
  have m1 : (x ^^^ y) * 2 % 2 ^ 16 = x * 2 % 2 ^ 16 ^^^ y * 2 % 2 ^ 16 := by
    have := xor_mul2pow x y 1
    simp only [Nat.pow_one] at this
    rw [this, Nat.xor_mod_two_pow]
  have m2 : (x ^^^ y) / 2 ^ 15 % 2 = (x / 2 ^ 15 % 2) ^^^ (y / 2 ^ 15 % 2) := by
    rw [Nat.xor_div_two_pow]
    have := Nat.xor_mod_two_pow (a := x / 2 ^ 15) (b := y / 2 ^ 15) (n := 1)
    simpa using this
  rw [m1, m2]
  generalize x * 2 % 2 ^ 16 = A
  generalize y * 2 % 2 ^ 16 = B
  have bx : x / 2 ^ 15 % 2 = 0 ∨ x / 2 ^ 15 % 2 = 1 := by omega
  have byy : y / 2 ^ 15 % 2 = 0 ∨ y / 2 ^ 15 % 2 = 1 := by omega
  rcases bx with h1 | h1 <;> rcases byy with h2 | h2 <;> rw [h1, h2] <;>
    simp only [Nat.zero_xor, Nat.xor_zero, Nat.xor_self, Nat.zero_ne_one, if_false, if_true,
      show (1 : Nat) ^^^ 0 = 1 by decide, show (0 : Nat) ^^^ 1 = 1 by decide, show (1 : Nat) ^^^ 1 = 0 by decide] <;>
    (apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_xor, Nat.testBit_zero];
     cases A.testBit i <;> cases B.testBit i <;> cases (0x1021 : Nat).testBit i <;> rfl)

theorem crcBit_lt : ∀ (k x : Nat), x < 65536 → crcBit x k < 65536 := by
  intro k
  induction k with
  | zero => intro x h; exact h
  | succ k ih => intro x h; rw [crcBit_succ]; exact ih _ (crcShift_lt x h)

theorem crcBit_xor : ∀ (k x y : Nat), x < 65536 → y < 65536 → crcBit (x ^^^ y) k = crcBit x k ^^^ crcBit y k := by
  intro k
  induction k with
  | zero => intro x y _ _; rfl
  | succ k ih =>
    intro x y hx hy
    rw [crcBit_succ, crcBit_succ, crcBit_succ, crcShift_xor x y hx hy]
    exact ih _ _ (crcShift_lt x hx) (crcShift_lt y hy)

theorem crcBit_small : ∀ (k x : Nat), x * 2 ^ k < 65536 → crcBit x k = x * 2 ^ k := by
  intro k
  induction k with
  | zero => intro x _; simp [crcBit]
  | succ k ih =>
    intro x h
    rw [crcBit_succ]
    have h2 : x * 2 < 65536 := by
      have : x * 2 ≤ x * 2 ^ (k + 1) := Nat.mul_le_mul_left x (Nat.le_self_pow (by omega) 2)
      omega
    have e : crcShift x = x * 2 := by
      unfold crcShift
      simp only [if_neg (by omega : ¬ x * 2 ≥ 65536)]
    rw [e, ih _ (by rw [Nat.mul_assoc, ← Nat.pow_succ']; exact h)]
    rw [Nat.mul_assoc, ← Nat.pow_succ']

theorem low_lt (crc : Nat) : crc % 256 * 2 ^ 8 < 65536 := by
  have h1 : crc % 256 < 256 := Nat.mod_lt _ (by decide)
  have e : (2 : Nat) ^ 8 = 256 := rfl
  rw [e]
  omega

theorem low_eq (crc : Nat) : crc * 256 % 65536 = crc % 256 * 2 ^ 8 := by
  have e : (2 : Nat) ^ 8 = 256 := rfl
  rw [e]
  omega

/-- The table step is the bitwise step, for every register value and byte. -/
theorem crcStep_bitwise (crc b : Nat) (hc : crc < 65536) (hb : b < 256) :
    crcStep crc b = crcBit (crc ^^^ b * 256) 8 := by
  have hq : crc / 256 < 256 := by omega
  have hi : crc / 256 ^^^ b < 256 := Nat.xor_lt_two_pow (n := 8) hq hb
  have split : crc = crc / 256 * 2 ^ 8 ^^^ crc % 256 := by
    have h8 : crc % 256 < 2 ^ 8 := Nat.mod_lt _ (by decide)
    rw [xor_disj _ _ 8 h8]
    have : (2 : Nat) ^ 8 = 256 := rfl
    rw [this]
    omega
  have e1 : crc ^^^ b * 256 = crc % 256 ^^^ (crc / 256 ^^^ b) * 2 ^ 8 := by
    conv => lhs; rw [split]
    rw [xor_mul2pow, show (2 : Nat) ^ 8 = 256 from rfl, Nat.xor_comm (crc / 256 * 256), Nat.xor_assoc]
  have tab : crctabHqx.getD (crc / 256 ^^^ b) 0 = crcBit ((crc / 256 ^^^ b) * 256) 8 :=
    crcTableIsCcitt_proven.2 _ hi
  have hl : crc % 256 < 65536 := by omega
  have hh : (crc / 256 ^^^ b) * 2 ^ 8 < 65536 := by
    have : (crc / 256 ^^^ b) * 2 ^ 8 < 256 * 2 ^ 8 := Nat.mul_lt_mul_of_pos_right hi (by decide)
    simpa using this
  have hs : crc % 256 * 2 ^ 8 < 65536 := low_lt crc
  rw [e1, crcBit_xor 8 _ _ hl hh, crcBit_small 8 (crc % 256) hs]
  unfold crcStep
  rw [tab]
  rw [low_eq crc]

/-- One byte of CRC-CCITT, bit by bit: xor the byte into the top of the register, then eight turns of
the shift register with polynomial `0x1021`, most significant bit first. -/
def ccittByte (r x : Nat) : Nat := crcBit (r ^^^ x * 256) 8

/-- The CRC-CCITT recurrence over the data: `crc_hqx(data, crc)` starts from `crc & 0xffff` and runs
`ccittByte` over every byte in order. This pins every byte of the data: a function that ignores the
data, or reads it in another order, does not satisfy it. -/
def CrcHqxCcitt : Prop :=
  ∀ (d : List Nat) (c : Int), (∀ x ∈ d, x < 256) →
    crcHqx d c = d.foldl ccittByte ((c % 2 ^ 32).toNat % 65536)

theorem crcStep_ccitt (r x : Nat) (h0 : r < 65536) (hx : x < 256) : crcStep r x = ccittByte r x :=
  crcStep_bitwise r x h0 hx

theorem ccittByte_lt (r x : Nat) (h0 : r < 65536) (hx : x < 256) : ccittByte r x < 65536 :=
  crcBit_lt 8 _ (Nat.xor_lt_two_pow (n := 16) h0 (by omega))

attribute [local irreducible] crcStep ccittByte in
theorem fold_ccitt : ∀ (d : List Nat) (r : Nat), (∀ x ∈ d, x < 256) → r < 65536 →
    d.foldl crcStep r = d.foldl ccittByte r := by
  intro d
  induction d with
  | nil => intro r _ _; rfl
  | cons x t ih =>
    intro r hd h0
    have hx : x < 256 := hd x (by simp)
    rw [List.foldl_cons, List.foldl_cons]
    rw [crcStep_ccitt r x h0 hx]
    exact ih _ (fun y hy => hd y (by simp [hy])) (ccittByte_lt r x h0 hx)

theorem crcHqxCcitt_proven : CrcHqxCcitt := by
  intro d c hd
  exact fold_ccitt d _ hd (Nat.mod_lt _ (by decide))

end PyLean.TextLibs.Binascii
