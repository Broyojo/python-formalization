import PyLean.TextLibs.StructProps

/-!
Integer round trip through the real dispatch: every integer entry of every format
table, `runPack` then `runUnpack`, for every in-range value. This is what credits the
`np_*`, `nu_*`, `bp_*`, `bu_*`, `lp_*`, `lu_*` integer routines, so it includes
the pre-swap `lilendianTable0`, whose `lu_short` etc. CPython replaces at start-up on
a little-endian build and the difftest therefore cannot reach.
-/

namespace PyLean.TextLibs.Struct

open PyLean PyLean.TextLibs

set_option linter.unusedSimpArgs false




/-! ### The C sign extension -/

theorem xor_low (k x : Nat) (h : x < 2 ^ k) : x ^^^ 2 ^ k = 2 ^ k + x := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hi : i = k
  · subst hi
    simp [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow h]
  · by_cases hlt : i < k
    · rw [Nat.testBit_two_pow_add_gt hlt]
      simp [Ne.symm hi]
    · have hgt : k < i := by omega
      have h1 : x.testBit i = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hgt)))
      have h2 : (2 ^ k + x).testBit i = false := by
        apply Nat.testBit_lt_two_pow
        have : 2 ^ (k + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hgt
        rw [Nat.pow_succ] at this
        omega
      simp [h1, h2, Ne.symm hi]

theorem xor_high (k r : Nat) (h : r < 2 ^ k) : (2 ^ k + r) ^^^ 2 ^ k = r := by
  rw [← xor_low k r h, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem and_low (k x : Nat) (h : x < 2 ^ k) : x &&& 2 ^ k = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
  by_cases hi : i = k
  · subst hi
    simp [Nat.testBit_lt_two_pow h]
  · simp [Ne.symm hi]

/-- `signExtC` on a value below the sign bit returns it unchanged. -/
theorem signExtC_low (k x : Nat) (hk : k < 64) (h : x < 2 ^ k) :
    signExtC (2 ^ k) x = x := by
  have hw : (2 : Nat) ^ k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hk)
  have hy : ((x ^^^ 2 ^ k) + 2 ^ 64 - 2 ^ k) % 2 ^ 64 = x := by
    rw [xor_low k x h]
    have e : 2 ^ k + x + 2 ^ 64 - 2 ^ k = x + 2 ^ 64 := by omega
    rw [e, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  simp only [signExtC]
  rw [hy, and_low k x h]
  simp

/-- `signExtC` at the three widths the C uses, on a value with the sign bit set. -/
theorem signExtC_high (k r : Nat) (hk : k = 15 ∨ k = 31 ∨ k = 63) (h : r < 2 ^ k) :
    signExtC (2 ^ k) (2 ^ k + r) = (r : Int) - 2 ^ k := by
  have hy : (((2 ^ k + r) ^^^ 2 ^ k) + 2 ^ 64 - 2 ^ k) % 2 ^ 64 = r + 2 ^ 64 - 2 ^ k := by
    rw [xor_high k r h]
    rcases hk with rfl | rfl | rfl <;> exact Nat.mod_eq_of_lt (by omega)
  have hbit : (r + 2 ^ 64 - 2 ^ k).testBit k = true := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    rcases hk with rfl | rfl | rfl <;> (simp only [decide_eq_true_eq]; omega)
  simp only [signExtC]
  rw [hy]
  have hne : (r + 2 ^ 64 - 2 ^ k) &&& 2 ^ k ≠ 0 := by
    intro h0
    have := congrArg (fun v => v.testBit k) h0
    simp [Nat.testBit_and, hbit] at this
  rw [if_pos hne]
  rcases hk with rfl | rfl | rfl <;> omega

/-! ### Decoding what the pack loops wrote -/

theorem leBytes_length : ∀ (i x : Nat), (leBytes i x).length = i
  | 0, _ => rfl
  | i + 1, x => by simp [leBytes, leBytes_length i]

theorem twos_length (s : Nat) (x : Int) : (twos s x).length = s := leBytes_length _ _

theorem lpLoop_length : ∀ (i : Nat) (x : Int), (lpLoop i x).length = i
  | 0, _ => rfl
  | i + 1, x => by simp [lpLoop, lpLoop_length i]

theorem bpLoop_length : ∀ (i : Nat) (x : Int), (bpLoop i x).length = i
  | 0, _ => rfl
  | i + 1, x => by simp [bpLoop, bpLoop_length i]

/-- One step of `x & 0xff; x >>= 8`: `x % (256 * P)` from the byte and the shifted rest. -/
theorem emod_step (x P : Int) (hP : 0 < P) :
    x % (256 * P) = x % 256 + 256 * ((x / 256) % P) := by
  have h1 := Int.emod_add_mul_ediv x 256
  have h2 := Int.emod_add_mul_ediv (x / 256) P
  have h3 := Int.emod_nonneg (x / 256) (Int.ne_of_gt hP)
  have h4 := Int.emod_lt_of_pos (x / 256) hP
  have h5 : 0 ≤ x % 256 := Int.emod_nonneg _ (by decide)
  have h6 : x % 256 < 256 := Int.emod_lt_of_pos _ (by decide)
  generalize hu : (x / 256) % P = u at *
  generalize hv : (x / 256) / P = t at *
  generalize hb : x % 256 = b at *
  generalize hq : x / 256 = q at *
  have hx : x = (b + 256 * u) + (256 * P) * t := by
    rw [← h1, ← h2, Int.mul_add, Int.mul_assoc]
    omega
  rw [hx, Int.add_mul_emod_self_left]
  apply Int.emod_eq_of_lt <;> omega

theorem pow8_succ (i : Nat) : (2 : Int) ^ (8 * (i + 1)) = 256 * 2 ^ (8 * i) := by
  rw [Nat.mul_add, Int.pow_add, Int.mul_comm]
  rfl

theorem leVal_lpLoop : ∀ (i : Nat) (x : Int), (leVal (lpLoop i x) : Int) = x % 2 ^ (8 * i)
  | 0, x => by simp [lpLoop, leVal, Int.emod_one]
  | i + 1, x => by
    have hb : 0 ≤ x % 256 := Int.emod_nonneg _ (by decide)
    simp only [lpLoop, leVal, Int.natCast_add, Int.natCast_mul, leVal_lpLoop i (x / 256)]
    rw [pow8_succ, emod_step x _ (Int.pow_pos (by decide))]
    rw [Int.toNat_of_nonneg hb]
    rfl

theorem beVal_snoc (l : List Nat) (b : Nat) : beVal (l ++ [b]) = beVal l * 256 + b := by
  simp [beVal, List.foldl_append]

theorem beVal_bpLoop : ∀ (i : Nat) (x : Int), (beVal (bpLoop i x) : Int) = x % 2 ^ (8 * i)
  | 0, x => by simp [bpLoop, beVal, Int.emod_one]
  | i + 1, x => by
    have hb : 0 ≤ x % 256 := Int.emod_nonneg _ (by decide)
    simp only [bpLoop, beVal_snoc, Int.natCast_add, Int.natCast_mul, beVal_bpLoop i (x / 256)]
    rw [pow8_succ, emod_step x _ (Int.pow_pos (by decide)), Int.toNat_of_nonneg hb]
    show _ * 256 + _ = _
    omega

/-! ### Integer entries: the conversions on an in-range `int` -/

theorem asC_ok {lo hi n : Int} (m : String) (h1 : lo ≤ n) (h2 : n ≤ hi) :
    asC lo hi m n = .ok n := by
  unfold asC
  rw [if_neg (by omega)]

theorem getLong_int {n : Int} (h1 : -9223372036854775808 ≤ n) (h2 : n ≤ 9223372036854775807) :
    getLong (.int n) = .ok n := asC_ok _ h1 h2
theorem getLonglong_int {n : Int} (h1 : -9223372036854775808 ≤ n) (h2 : n ≤ 9223372036854775807) :
    getLonglong (.int n) = .ok n := asC_ok _ h1 h2
theorem getSsizeT_int {n : Int} (h1 : -9223372036854775808 ≤ n) (h2 : n ≤ 9223372036854775807) :
    getSsizeT (.int n) = .ok n := asC_ok _ h1 h2

theorem getUlong_int {n : Int} (h1 : 0 ≤ n) (h2 : n ≤ 18446744073709551615) :
    getUlong (.int n) = .ok n := by
  show (if n < 0 then _ else asC 0 ulongMax _ n : Py Int) = _
  rw [if_neg (by omega)]
  exact asC_ok _ h1 h2
theorem getUlonglong_int {n : Int} (h1 : 0 ≤ n) (h2 : n ≤ 18446744073709551615) :
    getUlonglong (.int n) = .ok n := by
  show (if n < 0 then _ else asC 0 ulongMax _ n : Py Int) = _
  rw [if_neg (by omega)]
  exact asC_ok _ h1 h2
theorem getSizeT_int {n : Int} (h1 : 0 ≤ n) (h2 : n ≤ 18446744073709551615) :
    getSizeT (.int n) = .ok n := by
  show (if n < 0 then _ else asC 0 ulongMax _ n : Py Int) = _
  rw [if_neg (by omega)]
  exact asC_ok _ h1 h2

theorem npSigned_ok {f : FormatDef} {lo hi x : Int} (h1 : lo ≤ x) (h2 : x ≤ hi) :
    npSigned f lo hi x = .ok (twos f.size x) := by
  unfold npSigned
  rw [if_neg (by omega)]

theorem npUnsigned_ok {f : FormatDef} {hi x : Int} (h1 : 0 ≤ x) (h2 : x ≤ hi) :
    npUnsigned f hi x = .ok (twos f.size x) := by
  unfold npUnsigned
  rw [if_neg (by omega)]

/-- Unsigned and signed codes; `P` reads back unsigned (`nu_void_p`). -/
def isUnsignedCode (c : Char) : Bool :=
  c == 'B' || c == 'H' || c == 'I' || c == 'L' || c == 'N' || c == 'Q' || c == 'P'

def loOf (e : FormatDef) : Int := if isUnsignedCode e.format then 0 else -(2 ^ (e.size * 8 - 1))
def hiOf (e : FormatDef) : Int :=
  if isUnsignedCode e.format then 2 ^ (e.size * 8) - 1 else 2 ^ (e.size * 8 - 1) - 1

/-- Packing `n` in the entry's documented range succeeds, gives `size` bytes, and
unpacking them returns `n`. -/
def IntEntryRoundTrip (e : FormatDef) : Prop :=
  ∀ n : Int, loOf e ≤ n → n ≤ hiOf e →
    ∃ w, runPack e (.int n) = .ok w ∧ w.length = e.size ∧ runUnpack e w = .ok (.int n)

theorem twos_unsigned (s : Nat) (n : Int) (h1 : 0 ≤ n) (h2 : n < 2 ^ (s * 8)) :
    (leVal (twos s n) : Int) = n := by
  have hm : n % (2 : Int) ^ (s * 8) = n := Int.emod_eq_of_lt h1 h2
  unfold twos
  rw [hm, leVal_leBytes, Nat.mul_comm 8]
  have hlt : n.toNat < 2 ^ (s * 8) := by
    have : ((2 : Nat) ^ (s * 8) : Int) = (2 : Int) ^ (s * 8) := by norm_cast
    omega
  rw [Nat.mod_eq_of_lt hlt]
  exact Int.toNat_of_nonneg h1

/-- Decoding `signExtC` from a value congruent to `n`. -/
theorem signExt_of_emod (k v : Nat) (n : Int) (hk : k = 15 ∨ k = 31 ∨ k = 63)
    (hv : (v : Int) = n % 2 ^ (k + 1)) (h1 : -(2 ^ k : Int) ≤ n) (h2 : n < 2 ^ k) :
    signExtC (2 ^ k) v = n := by
  have hP : (2 : Int) ^ (k + 1) = 2 * 2 ^ k := by rw [Int.pow_succ, Int.mul_comm]
  have hpos : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
  have hNk : ((2 : Nat) ^ k : Int) = (2 : Int) ^ k := by norm_cast
  by_cases h0 : 0 ≤ n
  · have hm : n % (2 : Int) ^ (k + 1) = n := Int.emod_eq_of_lt h0 (by omega)
    have hvn : (v : Int) = n := by rw [hv, hm]
    rw [signExtC_low k v (by omega) (by omega)]
    exact hvn
  · have hm : n % (2 : Int) ^ (k + 1) = n + 2 ^ (k + 1) := by
      have h3 : (n + (2 : Int) ^ (k + 1)) % 2 ^ (k + 1) = n % 2 ^ (k + 1) := by simp
      rw [← h3]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    have hvn : (v : Int) = n + 2 ^ (k + 1) := by rw [hv, hm]
    have hr : v = 2 ^ k + (v - 2 ^ k) := by omega
    rw [hr, signExtC_high k (v - 2 ^ k) hk (by omega)]
    omega

/-- A native signed entry (`np_*` then `nu_*`). -/
theorem rt_signed (e : FormatDef) (hs : e.size ≠ 0) (hc : isUnsignedCode e.format = false)
    (hp : ∀ n, loOf e ≤ n → n ≤ hiOf e → runPack e (.int n) = .ok (twos e.size n))
    (hu : ∀ p, runUnpack e p = .ok (.int (signedOf e.size (leVal (p.take e.size))))) :
    IntEntryRoundTrip e := by
  intro n h1 h2
  refine ⟨_, hp n h1 h2, twos_length _ _, ?_⟩
  rw [hu, List.take_of_length_le (by rw [twos_length]; exact Nat.le_refl _)]
  simp only [loOf, hiOf, hc] at h1 h2
  rw [nativeSignedRoundTrip_proven e.size n hs (by simpa using h1) (by simp at h2; omega)]

/-- A native unsigned entry. -/
theorem rt_unsigned (e : FormatDef) (hc : isUnsignedCode e.format = true)
    (hp : ∀ n, loOf e ≤ n → n ≤ hiOf e → runPack e (.int n) = .ok (twos e.size n))
    (hu : ∀ p, runUnpack e p = .ok (.int (leVal (p.take e.size)))) :
    IntEntryRoundTrip e := by
  intro n h1 h2
  refine ⟨_, hp n h1 h2, twos_length _ _, ?_⟩
  rw [hu, List.take_of_length_le (by rw [twos_length]; exact Nat.le_refl _)]
  simp only [loOf, hiOf, hc] at h1 h2
  rw [twos_unsigned e.size n (by simpa using h1) (by simp at h2; omega)]

/-- A standard entry, given how its loop's output decodes. -/
theorem rt_std (e : FormatDef) (w : Int → List Nat) (dec : List Nat → Nat) (k : Nat)
    (hk : k = 15 ∨ k = 31 ∨ k = 63) (hsz : e.size * 8 = k + 1)
    (hc : isUnsignedCode e.format = false)
    (hl : ∀ n, (w n).length = e.size)
    (hd : ∀ n, (dec (w n) : Int) = n % 2 ^ (k + 1))
    (hp : ∀ n, loOf e ≤ n → n ≤ hiOf e → runPack e (.int n) = .ok (w n))
    (hu : ∀ p, runUnpack e p = .ok (.int (signExtC (2 ^ k) (dec (p.take e.size))))) :
    IntEntryRoundTrip e := by
  intro n h1 h2
  refine ⟨_, hp n h1 h2, hl n, ?_⟩
  rw [hu, List.take_of_length_le (by rw [hl]; exact Nat.le_refl _)]
  simp only [loOf, hiOf, hc, hsz] at h1 h2
  rw [signExt_of_emod k _ n hk (hd n) (by simpa using h1) (by simp at h2; omega)]

/-- A standard unsigned entry. -/
theorem rt_std_u (e : FormatDef) (w : Int → List Nat) (dec : List Nat → Nat)
    (hc : isUnsignedCode e.format = true)
    (hl : ∀ n, (w n).length = e.size)
    (hd : ∀ n, (dec (w n) : Int) = n % 2 ^ (8 * e.size))
    (hp : ∀ n, loOf e ≤ n → n ≤ hiOf e → runPack e (.int n) = .ok (w n))
    (hu : ∀ p, runUnpack e p = .ok (.int (dec (p.take e.size)))) :
    IntEntryRoundTrip e := by
  intro n h1 h2
  refine ⟨_, hp n h1 h2, hl n, ?_⟩
  rw [hu, List.take_of_length_le (by rw [hl]; exact Nat.le_refl _)]
  simp only [loOf, hiOf, hc] at h1 h2
  have h1' : 0 ≤ n := by simpa using h1
  have h2' : n < 2 ^ (8 * e.size) := by
    simp at h2
    rw [Nat.mul_comm]
    omega
  rw [hd, Int.emod_eq_of_lt h1' h2']

theorem packVoidP_ok {f : FormatDef} {n : Int} (h1 : 0 ≤ n) (h2 : n ≤ 18446744073709551615)
    (hf : f.pack = .npVoidP := by rfl) : runPack f (.int n) = .ok (twos 8 n) := by
  simp only [runPack, hf]
  show (if n < 0 then _ else _ : Py (List Nat)) = _
  rw [if_neg (by omega), asC_ok (hi := ulongMax) _ h1 (by simp only [ulongMax]; omega)]
  rfl

theorem packLonglongStd_ok (f : FormatDef) (n : Int) (le : Bool)
    (h1 : -9223372036854775808 ≤ n) (h2 : n ≤ 9223372036854775807) :
    packLonglongStd f (.int n) le = .ok (if le then lpLoop 8 n else bpLoop 8 n) := by
  show (if n < longMin ∨ n > longMax then _ else _ : Py (List Nat)) = _
  rw [if_neg (by simp only [longMin, longMax]; omega)]
  rfl

theorem packUlonglongStd_ok (f : FormatDef) (n : Int) (le : Bool)
    (h1 : 0 ≤ n) (h2 : n ≤ 18446744073709551615) :
    packUlonglongStd f (.int n) le = .ok (if le then lpLoop 8 n else bpLoop 8 n) := by
  show (if n < 0 ∨ n > ulongMax then _ else _ : Py (List Nat)) = _
  rw [if_neg (by simp only [ulongMax]; omega)]
  rfl

theorem packIntStd_ok (f : FormatDef) (n : Int) (le : Bool) (hs : f.size = 2 ∨ f.size = 4)
    (h1 : -(2 ^ (f.size * 8 - 1) : Int) ≤ n) (h2 : n ≤ 2 ^ (f.size * 8 - 1) - 1) :
    packIntStd f (.int n) le = .ok (if le then lpLoop f.size n else bpLoop f.size n) := by
  have hL : getLong (.int n) = .ok n := by
    apply getLong_int <;> rcases hs with h | h <;> rw [h] at h1 h2 <;> simp at h1 h2 <;> omega
  unfold packIntStd
  rw [hL]
  rcases hs with h | h <;> rw [h] at h1 h2 ⊢ <;> simp at h1 h2 <;> simp [orRange, bind, Except.bind, pure, Except.pure] <;> omega

theorem packUintStd_ok (f : FormatDef) (n : Int) (le : Bool) (hs : f.size = 2 ∨ f.size = 4)
    (h1 : 0 ≤ n) (h2 : n ≤ 2 ^ (f.size * 8) - 1) :
    packUintStd f (.int n) le = .ok (if le then lpLoop f.size n else bpLoop f.size n) := by
  have hL : getUlong (.int n) = .ok n := by
    apply getUlong_int h1
    rcases hs with h | h <;> rw [h] at h2 <;> simp at h2 <;> omega
  unfold packUintStd
  rw [hL]
  rcases hs with h | h <;> rw [h] at h2 ⊢ <;> simp at h2 <;> simp [orRange, bind, Except.bind, pure, Except.pure] <;> omega

theorem rt_nuByte_npByte_0 : IntEntryRoundTrip ⟨'b', 1, 0, .nuByte, .npByte⟩ :=
  rt_signed _ (by decide) (by decide) (fun n h1 h2 => by
    rw [show loOf (⟨'b', 1, 0, .nuByte, .npByte⟩ : FormatDef) = (-128) by decide] at h1; rw [show hiOf (⟨'b', 1, 0, .nuByte, .npByte⟩ : FormatDef) = (127) by decide] at h2
    simp (disch := omega) only [runPack, orRange, getLong_int, getUlong_int, getLonglong_int, getUlonglong_int, getSsizeT_int, getSizeT_int, npSigned_ok, npUnsigned_ok, bind, Except.bind, pure, Except.pure]) (fun _ => rfl)

theorem rt_nuUbyte_npUbyte_0 : IntEntryRoundTrip ⟨'B', 1, 0, .nuUbyte, .npUbyte⟩ :=
  rt_unsigned _ (by decide) (fun n h1 h2 => by
    rw [show loOf (⟨'B', 1, 0, .nuUbyte, .npUbyte⟩ : FormatDef) = (0) by decide] at h1; rw [show hiOf (⟨'B', 1, 0, .nuUbyte, .npUbyte⟩ : FormatDef) = (255) by decide] at h2
    simp (disch := omega) only [runPack, orRange, getLong_int, getUlong_int, getLonglong_int, getUlonglong_int, getSsizeT_int, getSizeT_int, npSigned_ok, npUnsigned_ok, bind, Except.bind, pure, Except.pure]) (fun _ => rfl)

theorem rt_nuShort_npShort_2 : IntEntryRoundTrip ⟨'h', 2, 2, .nuShort, .npShort⟩ :=
  rt_signed _ (by decide) (by decide) (fun n h1 h2 => by
    rw [show loOf (⟨'h', 2, 2, .nuShort, .npShort⟩ : FormatDef) = (-32768) by decide] at h1; rw [show hiOf (⟨'h', 2, 2, .nuShort, .npShort⟩ : FormatDef) = (32767) by decide] at h2
    simp (disch := omega) only [runPack, orRange, getLong_int, getUlong_int, getLonglong_int, getUlonglong_int, getSsizeT_int, getSizeT_int, npSigned_ok, npUnsigned_ok, bind, Except.bind, pure, Except.pure]) (fun _ => rfl)

theorem rt_nuUshort_npUshort_2 : IntEntryRoundTrip ⟨'H', 2, 2, .nuUshort, .npUshort⟩ :=
  rt_unsigned _ (by decide) (fun n h1 h2 => by
    rw [show loOf (⟨'H', 2, 2, .nuUshort, .npUshort⟩ : FormatDef) = (0) by decide] at h1; rw [show hiOf (⟨'H', 2, 2, .nuUshort, .npUshort⟩ : FormatDef) = (65535) by decide] at h2
    simp (disch := omega) only [runPack, orRange, getLong_int, getUlong_int, getLonglong_int, getUlonglong_int, getSsizeT_int, getSizeT_int, npSigned_ok, npUnsigned_ok, bind, Except.bind, pure, Except.pure]) (fun _ => rfl)

theorem rt_nuInt_npInt_4 : IntEntryRoundTrip ⟨'i', 4, 4, .nuInt, .npInt⟩ :=
  rt_signed _ (by decide) (by decide) (fun n h1 h2 => by
    rw [show loOf (⟨'i', 4, 4, .nuInt, .npInt⟩ : FormatDef) = (-2147483648) by decide] at h1; rw [show hiOf (⟨'i', 4, 4, .nuInt, .npInt⟩ : FormatDef) = (2147483647) by decide] at h2
    simp (disch := omega) only [runPack, orRange, getLong_int, getUlong_int, getLonglong_int, getUlonglong_int, getSsizeT_int, getSizeT_int, npSigned_ok, npUnsigned_ok, bind, Except.bind, pure, Except.pure]) (fun _ => rfl)

theorem rt_nuUint_npUint_4 : IntEntryRoundTrip ⟨'I', 4, 4, .nuUint, .npUint⟩ :=
  rt_unsigned _ (by decide) (fun n h1 h2 => by
    rw [show loOf (⟨'I', 4, 4, .nuUint, .npUint⟩ : FormatDef) = (0) by decide] at h1; rw [show hiOf (⟨'I', 4, 4, .nuUint, .npUint⟩ : FormatDef) = (4294967295) by decide] at h2
    simp (disch := omega) only [runPack, orRange, getLong_int, getUlong_int, getLonglong_int, getUlonglong_int, getSsizeT_int, getSizeT_int, npSigned_ok, npUnsigned_ok, bind, Except.bind, pure, Except.pure]) (fun _ => rfl)

theorem rt_nuLong_npLong_8 : IntEntryRoundTrip ⟨'l', 8, 8, .nuLong, .npLong⟩ :=
  rt_signed _ (by decide) (by decide) (fun n h1 h2 => by
    rw [show loOf (⟨'l', 8, 8, .nuLong, .npLong⟩ : FormatDef) = (-9223372036854775808) by decide] at h1; rw [show hiOf (⟨'l', 8, 8, .nuLong, .npLong⟩ : FormatDef) = (9223372036854775807) by decide] at h2
    simp (disch := omega) only [runPack, orRange, getLong_int, getUlong_int, getLonglong_int, getUlonglong_int, getSsizeT_int, getSizeT_int, npSigned_ok, npUnsigned_ok, bind, Except.bind, pure, Except.pure]) (fun _ => rfl)

theorem rt_nuUlong_npUlong_8 : IntEntryRoundTrip ⟨'L', 8, 8, .nuUlong, .npUlong⟩ :=
  rt_unsigned _ (by decide) (fun n h1 h2 => by
    rw [show loOf (⟨'L', 8, 8, .nuUlong, .npUlong⟩ : FormatDef) = (0) by decide] at h1; rw [show hiOf (⟨'L', 8, 8, .nuUlong, .npUlong⟩ : FormatDef) = (18446744073709551615) by decide] at h2
    simp (disch := omega) only [runPack, orRange, getLong_int, getUlong_int, getLonglong_int, getUlonglong_int, getSsizeT_int, getSizeT_int, npSigned_ok, npUnsigned_ok, bind, Except.bind, pure, Except.pure]) (fun _ => rfl)

theorem rt_nuSsizeT_npSsizeT_8 : IntEntryRoundTrip ⟨'n', 8, 8, .nuSsizeT, .npSsizeT⟩ :=
  rt_signed _ (by decide) (by decide) (fun n h1 h2 => by
    rw [show loOf (⟨'n', 8, 8, .nuSsizeT, .npSsizeT⟩ : FormatDef) = (-9223372036854775808) by decide] at h1; rw [show hiOf (⟨'n', 8, 8, .nuSsizeT, .npSsizeT⟩ : FormatDef) = (9223372036854775807) by decide] at h2
    simp (disch := omega) only [runPack, orRange, getLong_int, getUlong_int, getLonglong_int, getUlonglong_int, getSsizeT_int, getSizeT_int, npSigned_ok, npUnsigned_ok, bind, Except.bind, pure, Except.pure]) (fun _ => rfl)

theorem rt_nuSizeT_npSizeT_8 : IntEntryRoundTrip ⟨'N', 8, 8, .nuSizeT, .npSizeT⟩ :=
  rt_unsigned _ (by decide) (fun n h1 h2 => by
    rw [show loOf (⟨'N', 8, 8, .nuSizeT, .npSizeT⟩ : FormatDef) = (0) by decide] at h1; rw [show hiOf (⟨'N', 8, 8, .nuSizeT, .npSizeT⟩ : FormatDef) = (18446744073709551615) by decide] at h2
    simp (disch := omega) only [runPack, orRange, getLong_int, getUlong_int, getLonglong_int, getUlonglong_int, getSsizeT_int, getSizeT_int, npSigned_ok, npUnsigned_ok, bind, Except.bind, pure, Except.pure]) (fun _ => rfl)

theorem rt_nuLonglong_npLonglong_8 : IntEntryRoundTrip ⟨'q', 8, 8, .nuLonglong, .npLonglong⟩ :=
  rt_signed _ (by decide) (by decide) (fun n h1 h2 => by
    rw [show loOf (⟨'q', 8, 8, .nuLonglong, .npLonglong⟩ : FormatDef) = (-9223372036854775808) by decide] at h1; rw [show hiOf (⟨'q', 8, 8, .nuLonglong, .npLonglong⟩ : FormatDef) = (9223372036854775807) by decide] at h2
    simp (disch := omega) only [runPack, orRange, getLong_int, getUlong_int, getLonglong_int, getUlonglong_int, getSsizeT_int, getSizeT_int, npSigned_ok, npUnsigned_ok, bind, Except.bind, pure, Except.pure]) (fun _ => rfl)

theorem rt_nuUlonglong_npUlonglong_8 : IntEntryRoundTrip ⟨'Q', 8, 8, .nuUlonglong, .npUlonglong⟩ :=
  rt_unsigned _ (by decide) (fun n h1 h2 => by
    rw [show loOf (⟨'Q', 8, 8, .nuUlonglong, .npUlonglong⟩ : FormatDef) = (0) by decide] at h1; rw [show hiOf (⟨'Q', 8, 8, .nuUlonglong, .npUlonglong⟩ : FormatDef) = (18446744073709551615) by decide] at h2
    simp (disch := omega) only [runPack, orRange, getLong_int, getUlong_int, getLonglong_int, getUlonglong_int, getSsizeT_int, getSizeT_int, npSigned_ok, npUnsigned_ok, bind, Except.bind, pure, Except.pure]) (fun _ => rfl)

theorem rt_nuVoidP_npVoidP_8 : IntEntryRoundTrip ⟨'P', 8, 8, .nuVoidP, .npVoidP⟩ :=
  rt_unsigned _ (by decide) (fun n h1 h2 => by
    rw [show loOf (⟨'P', 8, 8, .nuVoidP, .npVoidP⟩ : FormatDef) = (0) by decide] at h1; rw [show hiOf (⟨'P', 8, 8, .nuVoidP, .npVoidP⟩ : FormatDef) = (18446744073709551615) by decide] at h2
    exact packVoidP_ok h1 h2) (fun _ => rfl)

theorem rt_nuShort_npShort_0 : IntEntryRoundTrip ⟨'h', 2, 0, .nuShort, .npShort⟩ :=
  rt_signed _ (by decide) (by decide) (fun n h1 h2 => by
    rw [show loOf (⟨'h', 2, 0, .nuShort, .npShort⟩ : FormatDef) = (-32768) by decide] at h1; rw [show hiOf (⟨'h', 2, 0, .nuShort, .npShort⟩ : FormatDef) = (32767) by decide] at h2
    simp (disch := omega) only [runPack, orRange, getLong_int, getUlong_int, getLonglong_int, getUlonglong_int, getSsizeT_int, getSizeT_int, npSigned_ok, npUnsigned_ok, bind, Except.bind, pure, Except.pure]) (fun _ => rfl)

theorem rt_nuUshort_npUshort_0 : IntEntryRoundTrip ⟨'H', 2, 0, .nuUshort, .npUshort⟩ :=
  rt_unsigned _ (by decide) (fun n h1 h2 => by
    rw [show loOf (⟨'H', 2, 0, .nuUshort, .npUshort⟩ : FormatDef) = (0) by decide] at h1; rw [show hiOf (⟨'H', 2, 0, .nuUshort, .npUshort⟩ : FormatDef) = (65535) by decide] at h2
    simp (disch := omega) only [runPack, orRange, getLong_int, getUlong_int, getLonglong_int, getUlonglong_int, getSsizeT_int, getSizeT_int, npSigned_ok, npUnsigned_ok, bind, Except.bind, pure, Except.pure]) (fun _ => rfl)

theorem rt_nuInt_npInt_0 : IntEntryRoundTrip ⟨'i', 4, 0, .nuInt, .npInt⟩ :=
  rt_signed _ (by decide) (by decide) (fun n h1 h2 => by
    rw [show loOf (⟨'i', 4, 0, .nuInt, .npInt⟩ : FormatDef) = (-2147483648) by decide] at h1; rw [show hiOf (⟨'i', 4, 0, .nuInt, .npInt⟩ : FormatDef) = (2147483647) by decide] at h2
    simp (disch := omega) only [runPack, orRange, getLong_int, getUlong_int, getLonglong_int, getUlonglong_int, getSsizeT_int, getSizeT_int, npSigned_ok, npUnsigned_ok, bind, Except.bind, pure, Except.pure]) (fun _ => rfl)

theorem rt_nuUint_npUint_0 : IntEntryRoundTrip ⟨'I', 4, 0, .nuUint, .npUint⟩ :=
  rt_unsigned _ (by decide) (fun n h1 h2 => by
    rw [show loOf (⟨'I', 4, 0, .nuUint, .npUint⟩ : FormatDef) = (0) by decide] at h1; rw [show hiOf (⟨'I', 4, 0, .nuUint, .npUint⟩ : FormatDef) = (4294967295) by decide] at h2
    simp (disch := omega) only [runPack, orRange, getLong_int, getUlong_int, getLonglong_int, getUlonglong_int, getSsizeT_int, getSizeT_int, npSigned_ok, npUnsigned_ok, bind, Except.bind, pure, Except.pure]) (fun _ => rfl)

theorem rt_nuLonglong_npLonglong_0 : IntEntryRoundTrip ⟨'q', 8, 0, .nuLonglong, .npLonglong⟩ :=
  rt_signed _ (by decide) (by decide) (fun n h1 h2 => by
    rw [show loOf (⟨'q', 8, 0, .nuLonglong, .npLonglong⟩ : FormatDef) = (-9223372036854775808) by decide] at h1; rw [show hiOf (⟨'q', 8, 0, .nuLonglong, .npLonglong⟩ : FormatDef) = (9223372036854775807) by decide] at h2
    simp (disch := omega) only [runPack, orRange, getLong_int, getUlong_int, getLonglong_int, getUlonglong_int, getSsizeT_int, getSizeT_int, npSigned_ok, npUnsigned_ok, bind, Except.bind, pure, Except.pure]) (fun _ => rfl)

theorem rt_nuUlonglong_npUlonglong_0 : IntEntryRoundTrip ⟨'Q', 8, 0, .nuUlonglong, .npUlonglong⟩ :=
  rt_unsigned _ (by decide) (fun n h1 h2 => by
    rw [show loOf (⟨'Q', 8, 0, .nuUlonglong, .npUlonglong⟩ : FormatDef) = (0) by decide] at h1; rw [show hiOf (⟨'Q', 8, 0, .nuUlonglong, .npUlonglong⟩ : FormatDef) = (18446744073709551615) by decide] at h2
    simp (disch := omega) only [runPack, orRange, getLong_int, getUlong_int, getLonglong_int, getUlonglong_int, getSsizeT_int, getSizeT_int, npSigned_ok, npUnsigned_ok, bind, Except.bind, pure, Except.pure]) (fun _ => rfl)

theorem rt_buShort_bpInt_h : IntEntryRoundTrip ⟨'h', 2, 0, .buShort, .bpInt⟩ :=
  rt_std _ (bpLoop 2) beVal 15 (by decide) (by decide) (by decide) (bpLoop_length 2) (beVal_bpLoop 2) (fun n h1 h2 => by
    rw [show loOf (⟨'h', 2, 0, .buShort, .bpInt⟩ : FormatDef) = (-32768) by decide] at h1; rw [show hiOf (⟨'h', 2, 0, .buShort, .bpInt⟩ : FormatDef) = (32767) by decide] at h2
    exact packIntStd_ok _ _ _ (by decide) (by first | omega | (simp; omega)) (by first | omega | (simp; omega))) (fun _ => rfl)

theorem rt_buUint_bpUint_H : IntEntryRoundTrip ⟨'H', 2, 0, .buUint, .bpUint⟩ :=
  rt_std_u _ (bpLoop 2) beVal (by decide) (bpLoop_length 2) (beVal_bpLoop 2) (fun n h1 h2 => by
    rw [show loOf (⟨'H', 2, 0, .buUint, .bpUint⟩ : FormatDef) = (0) by decide] at h1; rw [show hiOf (⟨'H', 2, 0, .buUint, .bpUint⟩ : FormatDef) = (65535) by decide] at h2
    exact packUintStd_ok _ _ _ (by decide) (by first | omega | (simp; omega)) (by first | omega | (simp; omega))) (fun _ => rfl)

theorem rt_buInt_bpInt_i : IntEntryRoundTrip ⟨'i', 4, 0, .buInt, .bpInt⟩ :=
  rt_std _ (bpLoop 4) beVal 31 (by decide) (by decide) (by decide) (bpLoop_length 4) (beVal_bpLoop 4) (fun n h1 h2 => by
    rw [show loOf (⟨'i', 4, 0, .buInt, .bpInt⟩ : FormatDef) = (-2147483648) by decide] at h1; rw [show hiOf (⟨'i', 4, 0, .buInt, .bpInt⟩ : FormatDef) = (2147483647) by decide] at h2
    exact packIntStd_ok _ _ _ (by decide) (by first | omega | (simp; omega)) (by first | omega | (simp; omega))) (fun _ => rfl)

theorem rt_buUint_bpUint_I : IntEntryRoundTrip ⟨'I', 4, 0, .buUint, .bpUint⟩ :=
  rt_std_u _ (bpLoop 4) beVal (by decide) (bpLoop_length 4) (beVal_bpLoop 4) (fun n h1 h2 => by
    rw [show loOf (⟨'I', 4, 0, .buUint, .bpUint⟩ : FormatDef) = (0) by decide] at h1; rw [show hiOf (⟨'I', 4, 0, .buUint, .bpUint⟩ : FormatDef) = (4294967295) by decide] at h2
    exact packUintStd_ok _ _ _ (by decide) (by first | omega | (simp; omega)) (by first | omega | (simp; omega))) (fun _ => rfl)

theorem rt_buInt_bpInt_l : IntEntryRoundTrip ⟨'l', 4, 0, .buInt, .bpInt⟩ :=
  rt_std _ (bpLoop 4) beVal 31 (by decide) (by decide) (by decide) (bpLoop_length 4) (beVal_bpLoop 4) (fun n h1 h2 => by
    rw [show loOf (⟨'l', 4, 0, .buInt, .bpInt⟩ : FormatDef) = (-2147483648) by decide] at h1; rw [show hiOf (⟨'l', 4, 0, .buInt, .bpInt⟩ : FormatDef) = (2147483647) by decide] at h2
    exact packIntStd_ok _ _ _ (by decide) (by first | omega | (simp; omega)) (by first | omega | (simp; omega))) (fun _ => rfl)

theorem rt_buUint_bpUint_L : IntEntryRoundTrip ⟨'L', 4, 0, .buUint, .bpUint⟩ :=
  rt_std_u _ (bpLoop 4) beVal (by decide) (bpLoop_length 4) (beVal_bpLoop 4) (fun n h1 h2 => by
    rw [show loOf (⟨'L', 4, 0, .buUint, .bpUint⟩ : FormatDef) = (0) by decide] at h1; rw [show hiOf (⟨'L', 4, 0, .buUint, .bpUint⟩ : FormatDef) = (4294967295) by decide] at h2
    exact packUintStd_ok _ _ _ (by decide) (by first | omega | (simp; omega)) (by first | omega | (simp; omega))) (fun _ => rfl)

theorem rt_buLonglong_bpLonglong_q : IntEntryRoundTrip ⟨'q', 8, 0, .buLonglong, .bpLonglong⟩ :=
  rt_std _ (bpLoop 8) beVal 63 (by decide) (by decide) (by decide) (bpLoop_length 8) (beVal_bpLoop 8) (fun n h1 h2 => by
    rw [show loOf (⟨'q', 8, 0, .buLonglong, .bpLonglong⟩ : FormatDef) = (-9223372036854775808) by decide] at h1; rw [show hiOf (⟨'q', 8, 0, .buLonglong, .bpLonglong⟩ : FormatDef) = (9223372036854775807) by decide] at h2
    exact packLonglongStd_ok _ _ _ h1 h2) (fun _ => rfl)

theorem rt_buUlonglong_bpUlonglong_Q : IntEntryRoundTrip ⟨'Q', 8, 0, .buUlonglong, .bpUlonglong⟩ :=
  rt_std_u _ (bpLoop 8) beVal (by decide) (bpLoop_length 8) (beVal_bpLoop 8) (fun n h1 h2 => by
    rw [show loOf (⟨'Q', 8, 0, .buUlonglong, .bpUlonglong⟩ : FormatDef) = (0) by decide] at h1; rw [show hiOf (⟨'Q', 8, 0, .buUlonglong, .bpUlonglong⟩ : FormatDef) = (18446744073709551615) by decide] at h2
    exact packUlonglongStd_ok _ _ _ h1 h2) (fun _ => rfl)

theorem rt_luShort_lpInt_h : IntEntryRoundTrip ⟨'h', 2, 0, .luShort, .lpInt⟩ :=
  rt_std _ (lpLoop 2) leVal 15 (by decide) (by decide) (by decide) (lpLoop_length 2) (leVal_lpLoop 2) (fun n h1 h2 => by
    rw [show loOf (⟨'h', 2, 0, .luShort, .lpInt⟩ : FormatDef) = (-32768) by decide] at h1; rw [show hiOf (⟨'h', 2, 0, .luShort, .lpInt⟩ : FormatDef) = (32767) by decide] at h2
    exact packIntStd_ok _ _ _ (by decide) (by first | omega | (simp; omega)) (by first | omega | (simp; omega))) (fun _ => rfl)

theorem rt_luUint_lpUint_H : IntEntryRoundTrip ⟨'H', 2, 0, .luUint, .lpUint⟩ :=
  rt_std_u _ (lpLoop 2) leVal (by decide) (lpLoop_length 2) (leVal_lpLoop 2) (fun n h1 h2 => by
    rw [show loOf (⟨'H', 2, 0, .luUint, .lpUint⟩ : FormatDef) = (0) by decide] at h1; rw [show hiOf (⟨'H', 2, 0, .luUint, .lpUint⟩ : FormatDef) = (65535) by decide] at h2
    exact packUintStd_ok _ _ _ (by decide) (by first | omega | (simp; omega)) (by first | omega | (simp; omega))) (fun _ => rfl)

theorem rt_luInt_lpInt_i : IntEntryRoundTrip ⟨'i', 4, 0, .luInt, .lpInt⟩ :=
  rt_std _ (lpLoop 4) leVal 31 (by decide) (by decide) (by decide) (lpLoop_length 4) (leVal_lpLoop 4) (fun n h1 h2 => by
    rw [show loOf (⟨'i', 4, 0, .luInt, .lpInt⟩ : FormatDef) = (-2147483648) by decide] at h1; rw [show hiOf (⟨'i', 4, 0, .luInt, .lpInt⟩ : FormatDef) = (2147483647) by decide] at h2
    exact packIntStd_ok _ _ _ (by decide) (by first | omega | (simp; omega)) (by first | omega | (simp; omega))) (fun _ => rfl)

theorem rt_luUint_lpUint_I : IntEntryRoundTrip ⟨'I', 4, 0, .luUint, .lpUint⟩ :=
  rt_std_u _ (lpLoop 4) leVal (by decide) (lpLoop_length 4) (leVal_lpLoop 4) (fun n h1 h2 => by
    rw [show loOf (⟨'I', 4, 0, .luUint, .lpUint⟩ : FormatDef) = (0) by decide] at h1; rw [show hiOf (⟨'I', 4, 0, .luUint, .lpUint⟩ : FormatDef) = (4294967295) by decide] at h2
    exact packUintStd_ok _ _ _ (by decide) (by first | omega | (simp; omega)) (by first | omega | (simp; omega))) (fun _ => rfl)

theorem rt_luInt_lpInt_l : IntEntryRoundTrip ⟨'l', 4, 0, .luInt, .lpInt⟩ :=
  rt_std _ (lpLoop 4) leVal 31 (by decide) (by decide) (by decide) (lpLoop_length 4) (leVal_lpLoop 4) (fun n h1 h2 => by
    rw [show loOf (⟨'l', 4, 0, .luInt, .lpInt⟩ : FormatDef) = (-2147483648) by decide] at h1; rw [show hiOf (⟨'l', 4, 0, .luInt, .lpInt⟩ : FormatDef) = (2147483647) by decide] at h2
    exact packIntStd_ok _ _ _ (by decide) (by first | omega | (simp; omega)) (by first | omega | (simp; omega))) (fun _ => rfl)

theorem rt_luUint_lpUint_L : IntEntryRoundTrip ⟨'L', 4, 0, .luUint, .lpUint⟩ :=
  rt_std_u _ (lpLoop 4) leVal (by decide) (lpLoop_length 4) (leVal_lpLoop 4) (fun n h1 h2 => by
    rw [show loOf (⟨'L', 4, 0, .luUint, .lpUint⟩ : FormatDef) = (0) by decide] at h1; rw [show hiOf (⟨'L', 4, 0, .luUint, .lpUint⟩ : FormatDef) = (4294967295) by decide] at h2
    exact packUintStd_ok _ _ _ (by decide) (by first | omega | (simp; omega)) (by first | omega | (simp; omega))) (fun _ => rfl)

theorem rt_luLonglong_lpLonglong_q : IntEntryRoundTrip ⟨'q', 8, 0, .luLonglong, .lpLonglong⟩ :=
  rt_std _ (lpLoop 8) leVal 63 (by decide) (by decide) (by decide) (lpLoop_length 8) (leVal_lpLoop 8) (fun n h1 h2 => by
    rw [show loOf (⟨'q', 8, 0, .luLonglong, .lpLonglong⟩ : FormatDef) = (-9223372036854775808) by decide] at h1; rw [show hiOf (⟨'q', 8, 0, .luLonglong, .lpLonglong⟩ : FormatDef) = (9223372036854775807) by decide] at h2
    exact packLonglongStd_ok _ _ _ h1 h2) (fun _ => rfl)

theorem rt_luUlonglong_lpUlonglong_Q : IntEntryRoundTrip ⟨'Q', 8, 0, .luUlonglong, .lpUlonglong⟩ :=
  rt_std_u _ (lpLoop 8) leVal (by decide) (lpLoop_length 8) (leVal_lpLoop 8) (fun n h1 h2 => by
    rw [show loOf (⟨'Q', 8, 0, .luUlonglong, .lpUlonglong⟩ : FormatDef) = (0) by decide] at h1; rw [show hiOf (⟨'Q', 8, 0, .luUlonglong, .lpUlonglong⟩ : FormatDef) = (18446744073709551615) by decide] at h2
    exact packUlonglongStd_ok _ _ _ h1 h2) (fun _ => rfl)

/-- `lilendianTable` after `init_endian_tables`, spelled out. -/
def lilExplicit : List FormatDef :=
  [⟨'x', 1, 0, .none, .none⟩, ⟨'b', 1, 0, .nuByte, .npByte⟩, ⟨'B', 1, 0, .nuUbyte, .npUbyte⟩,
   ⟨'c', 1, 0, .nuChar, .npChar⟩, ⟨'s', 1, 0, .none, .none⟩, ⟨'p', 1, 0, .none, .none⟩,
   ⟨'h', 2, 0, .nuShort, .npShort⟩, ⟨'H', 2, 0, .nuUshort, .npUshort⟩,
   ⟨'i', 4, 0, .nuInt, .npInt⟩, ⟨'I', 4, 0, .nuUint, .npUint⟩,
   ⟨'l', 4, 0, .luInt, .lpInt⟩, ⟨'L', 4, 0, .luUint, .lpUint⟩,
   ⟨'q', 8, 0, .nuLonglong, .npLonglong⟩, ⟨'Q', 8, 0, .nuUlonglong, .npUlonglong⟩,
   ⟨'?', 1, 0, .buBool, .bpBool⟩, ⟨'e', 2, 0, .nuHalffloat, .npHalffloat⟩,
   ⟨'f', 4, 0, .luFloat, .lpFloat⟩, ⟨'d', 8, 0, .luDouble, .lpDouble⟩,
   ⟨'F', 8, 0, .nuFloatComplex, .npFloatComplex⟩, ⟨'D', 16, 0, .nuDoubleComplex, .npDoubleComplex⟩]

/-- The integer format codes of `Modules/_struct.c`. -/
def isIntCode (c : Char) : Bool := "bBhHiIlLnNqQP".toList.contains c

/-- Every integer entry of every table, including the pre-swap little-endian table. -/
def intEntries : List FormatDef :=
  (nativeTable ++ bigendianTable ++ lilendianTable0 ++ lilendianTable).filter
    (fun e => isIntCode e.format)

/-- Every integer entry of every table round-trips every value in its range. -/
def IntCodesRoundTrip : Prop := ∀ e ∈ intEntries, IntEntryRoundTrip e

/-- `intEntries`, spelled out in table order. -/
def intEntriesExplicit : List FormatDef :=
  [⟨'b', 1, 0, .nuByte, .npByte⟩,
   ⟨'B', 1, 0, .nuUbyte, .npUbyte⟩,
   ⟨'h', 2, 2, .nuShort, .npShort⟩,
   ⟨'H', 2, 2, .nuUshort, .npUshort⟩,
   ⟨'i', 4, 4, .nuInt, .npInt⟩,
   ⟨'I', 4, 4, .nuUint, .npUint⟩,
   ⟨'l', 8, 8, .nuLong, .npLong⟩,
   ⟨'L', 8, 8, .nuUlong, .npUlong⟩,
   ⟨'n', 8, 8, .nuSsizeT, .npSsizeT⟩,
   ⟨'N', 8, 8, .nuSizeT, .npSizeT⟩,
   ⟨'q', 8, 8, .nuLonglong, .npLonglong⟩,
   ⟨'Q', 8, 8, .nuUlonglong, .npUlonglong⟩,
   ⟨'P', 8, 8, .nuVoidP, .npVoidP⟩,
   ⟨'b', 1, 0, .nuByte, .npByte⟩,
   ⟨'B', 1, 0, .nuUbyte, .npUbyte⟩,
   ⟨'h', 2, 0, .buShort, .bpInt⟩,
   ⟨'H', 2, 0, .buUint, .bpUint⟩,
   ⟨'i', 4, 0, .buInt, .bpInt⟩,
   ⟨'I', 4, 0, .buUint, .bpUint⟩,
   ⟨'l', 4, 0, .buInt, .bpInt⟩,
   ⟨'L', 4, 0, .buUint, .bpUint⟩,
   ⟨'q', 8, 0, .buLonglong, .bpLonglong⟩,
   ⟨'Q', 8, 0, .buUlonglong, .bpUlonglong⟩,
   ⟨'b', 1, 0, .nuByte, .npByte⟩,
   ⟨'B', 1, 0, .nuUbyte, .npUbyte⟩,
   ⟨'h', 2, 0, .luShort, .lpInt⟩,
   ⟨'H', 2, 0, .luUint, .lpUint⟩,
   ⟨'i', 4, 0, .luInt, .lpInt⟩,
   ⟨'I', 4, 0, .luUint, .lpUint⟩,
   ⟨'l', 4, 0, .luInt, .lpInt⟩,
   ⟨'L', 4, 0, .luUint, .lpUint⟩,
   ⟨'q', 8, 0, .luLonglong, .lpLonglong⟩,
   ⟨'Q', 8, 0, .luUlonglong, .lpUlonglong⟩,
   ⟨'b', 1, 0, .nuByte, .npByte⟩,
   ⟨'B', 1, 0, .nuUbyte, .npUbyte⟩,
   ⟨'h', 2, 0, .nuShort, .npShort⟩,
   ⟨'H', 2, 0, .nuUshort, .npUshort⟩,
   ⟨'i', 4, 0, .nuInt, .npInt⟩,
   ⟨'I', 4, 0, .nuUint, .npUint⟩,
   ⟨'l', 4, 0, .luInt, .lpInt⟩,
   ⟨'L', 4, 0, .luUint, .lpUint⟩,
   ⟨'q', 8, 0, .nuLonglong, .npLonglong⟩,
   ⟨'Q', 8, 0, .nuUlonglong, .npUlonglong⟩]

theorem intCodesRoundTrip_proven : IntCodesRoundTrip := by
  unfold IntCodesRoundTrip
  rw [show intEntries = intEntriesExplicit by decide +kernel]
  exact List.forall_mem_cons.2 ⟨rt_nuByte_npByte_0,
    List.forall_mem_cons.2 ⟨rt_nuUbyte_npUbyte_0,
    List.forall_mem_cons.2 ⟨rt_nuShort_npShort_2,
    List.forall_mem_cons.2 ⟨rt_nuUshort_npUshort_2,
    List.forall_mem_cons.2 ⟨rt_nuInt_npInt_4,
    List.forall_mem_cons.2 ⟨rt_nuUint_npUint_4,
    List.forall_mem_cons.2 ⟨rt_nuLong_npLong_8,
    List.forall_mem_cons.2 ⟨rt_nuUlong_npUlong_8,
    List.forall_mem_cons.2 ⟨rt_nuSsizeT_npSsizeT_8,
    List.forall_mem_cons.2 ⟨rt_nuSizeT_npSizeT_8,
    List.forall_mem_cons.2 ⟨rt_nuLonglong_npLonglong_8,
    List.forall_mem_cons.2 ⟨rt_nuUlonglong_npUlonglong_8,
    List.forall_mem_cons.2 ⟨rt_nuVoidP_npVoidP_8,
    List.forall_mem_cons.2 ⟨rt_nuByte_npByte_0,
    List.forall_mem_cons.2 ⟨rt_nuUbyte_npUbyte_0,
    List.forall_mem_cons.2 ⟨rt_buShort_bpInt_h,
    List.forall_mem_cons.2 ⟨rt_buUint_bpUint_H,
    List.forall_mem_cons.2 ⟨rt_buInt_bpInt_i,
    List.forall_mem_cons.2 ⟨rt_buUint_bpUint_I,
    List.forall_mem_cons.2 ⟨rt_buInt_bpInt_l,
    List.forall_mem_cons.2 ⟨rt_buUint_bpUint_L,
    List.forall_mem_cons.2 ⟨rt_buLonglong_bpLonglong_q,
    List.forall_mem_cons.2 ⟨rt_buUlonglong_bpUlonglong_Q,
    List.forall_mem_cons.2 ⟨rt_nuByte_npByte_0,
    List.forall_mem_cons.2 ⟨rt_nuUbyte_npUbyte_0,
    List.forall_mem_cons.2 ⟨rt_luShort_lpInt_h,
    List.forall_mem_cons.2 ⟨rt_luUint_lpUint_H,
    List.forall_mem_cons.2 ⟨rt_luInt_lpInt_i,
    List.forall_mem_cons.2 ⟨rt_luUint_lpUint_I,
    List.forall_mem_cons.2 ⟨rt_luInt_lpInt_l,
    List.forall_mem_cons.2 ⟨rt_luUint_lpUint_L,
    List.forall_mem_cons.2 ⟨rt_luLonglong_lpLonglong_q,
    List.forall_mem_cons.2 ⟨rt_luUlonglong_lpUlonglong_Q,
    List.forall_mem_cons.2 ⟨rt_nuByte_npByte_0,
    List.forall_mem_cons.2 ⟨rt_nuUbyte_npUbyte_0,
    List.forall_mem_cons.2 ⟨rt_nuShort_npShort_0,
    List.forall_mem_cons.2 ⟨rt_nuUshort_npUshort_0,
    List.forall_mem_cons.2 ⟨rt_nuInt_npInt_0,
    List.forall_mem_cons.2 ⟨rt_nuUint_npUint_0,
    List.forall_mem_cons.2 ⟨rt_luInt_lpInt_l,
    List.forall_mem_cons.2 ⟨rt_luUint_lpUint_L,
    List.forall_mem_cons.2 ⟨rt_nuLonglong_npLonglong_0,
    List.forall_mem_cons.2 ⟨rt_nuUlonglong_npUlonglong_0,
    List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end PyLean.TextLibs.Struct

namespace PyLean.TextLibs.Struct

/-- Every non-NaN half-float pattern survives unpack then pack. Stated, not yet proven. -/
def HalfRoundTrip : Prop :=
  ∀ h < 65536, ¬(h / 1024 % 32 = 31 ∧ h % 1024 ≠ 0) →
    pyFloatPack2Bits (pyFloatUnpack2Bits h) = .ok h

end PyLean.TextLibs.Struct
