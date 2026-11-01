import PyLean.MathInt.BytesBase

/-!
`int.from_bytes` (`_PyLong_FromByteArray`, longobject.c:1000-1107) computes the
unsigned or two's-complement value of its bytes.
-/

namespace PyLean.MathInt

open PyLean

/-- Signed (two's complement) or unsigned value of little-endian bytes. -/
def bytesSigned (bs : List Nat) (signed : Bool) : Int :=
  if signed ∧ bs.getLastD 0 ≥ 128 then (bytesVal bs : Int) - 256 ^ bs.length else bytesVal bs

/-- One byte entering the 30-bit digit accumulator (longobject.c:1072-1084). -/
theorem pack_step (accum bits b R : Nat) (ha : accum < 2 ^ bits) (hb : b < 256) :
    accum ||| (b <<< bits) = accum + b * 2 ^ bits ∧
    accum + b * 2 ^ bits < 2 ^ (bits + 8) ∧
    (((accum + b * 2 ^ bits) &&& digitMask) + 2 ^ 30 * ((accum + b * 2 ^ bits) >>> 30 +
        2 ^ (bits + 8 - 30) * R) = accum + 2 ^ bits * (b + 256 * R) ∨ bits + 8 < 30) := by
  have e := or_shift_eq_add accum b bits ha
  have hlt : accum + b * 2 ^ bits < 2 ^ (bits + 8) := by
    rw [Nat.pow_add]
    have : b * 2 ^ bits ≤ 255 * 2 ^ bits := Nat.mul_le_mul_right _ (by omega)
    omega
  refine ⟨e, hlt, ?_⟩
  by_cases h30 : bits + 8 < 30
  · exact Or.inr h30
  · left
    unfold digitMask
    rw [and_mask_eq_mod, Nat.shiftRight_eq_div_pow]
    have d := Nat.div_add_mod (accum + b * 2 ^ bits) (2 ^ 30)
    have hp : 2 ^ 30 * 2 ^ (bits + 8 - 30) = 2 ^ bits * 256 := by
      rw [← Nat.pow_add, show 30 + (bits + 8 - 30) = bits + 8 by omega, Nat.pow_add]
    have hpR : 2 ^ 30 * (2 ^ (bits + 8 - 30) * R) = 2 ^ bits * (256 * R) := by
      rw [← Nat.mul_assoc, hp, Nat.mul_assoc]
    rw [Nat.mul_add (2 ^ 30), hpR]
    grind

theorem fromByteArrayLoop_unsigned :
    ∀ xs c accum bits, accum < 2 ^ bits → bits < 30 → AllBytes xs →
      digitsValue (fromByteArrayLoop false xs c accum bits) = accum + 2 ^ bits * bytesVal xs := by
  intro xs
  induction xs with
  | nil =>
    intro c accum bits ha hb _
    simp only [fromByteArrayLoop, bytesVal, Nat.mul_zero, Nat.add_zero]
    split
    · simp [digitsValue]
    · rename_i h; have : bits = 0 := by omega
      subst this; simp [digitsValue]; omega
  | cons b bs ih =>
    intro c accum bits ha hb hall
    have hb256 := hall b (by simp)
    have hrest : AllBytes bs := fun x hx => hall x (by simp [hx])
    obtain ⟨e, hlt, hstep⟩ := pack_step accum bits b (bytesVal bs) ha hb256
    simp only [fromByteArrayLoop, Bool.false_eq_true, ite_false, e, bytesVal]
    split
    · rename_i h30
      simp only [digitsValue]
      rw [ih c _ _ (by
          rw [Nat.shiftRight_eq_div_pow]
          apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
          rw [← Nat.pow_add, show bits + 8 - 30 + 30 = bits + 8 by omega]; exact hlt)
        (by omega) hrest]
      rcases hstep with h | h
      · exact h
      · omega
    · rename_i h30
      rw [ih c _ _ hlt (by omega) hrest]
      rw [Nat.pow_add]
      grind

/-- The two's complement image of `xs` with incoming carry `c`. -/
def twosVal (xs : List Nat) (c : Nat) : Nat :=
  (256 ^ xs.length - 1 - bytesVal xs + c) % 256 ^ xs.length

theorem twosVal_cons (b : Nat) (bs : List Nat) (c : Nat) (hb : b < 256) (hc : c ≤ 1)
    (hbs : AllBytes bs) :
    ((255 - b + c) % 256) + 256 * twosVal bs ((255 - b + c) / 256) = twosVal (b :: bs) c := by
  have hB := bytesVal_lt bs hbs
  generalize hm : bs.length = m at *
  unfold twosVal
  simp only [List.length_cons, bytesVal, hm]
  generalize bytesVal bs = B at *
  have hP : 256 ^ (m + 1) = 256 * 256 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
  by_cases ht : 255 - b + c < 256
  · rw [Nat.mod_eq_of_lt ht, Nat.div_eq_of_lt ht, Nat.add_zero,
      Nat.mod_eq_of_lt (show 256 ^ m - 1 - B < 256 ^ m by omega)]
    rw [hP, Nat.mod_eq_of_lt]
    · have : 256 * (256 ^ m - 1 - B) = 256 * 256 ^ m - 256 - 256 * B := by
        rw [Nat.mul_sub, Nat.mul_sub, Nat.mul_one]
      have : 256 * B + 256 ≤ 256 * 256 ^ m := by
        have := Nat.mul_le_mul_left 256 (show B + 1 ≤ 256 ^ m by omega); omega
      omega
    · have : 256 * B + 256 ≤ 256 * 256 ^ m := by
        have := Nat.mul_le_mul_left 256 (show B + 1 ≤ 256 ^ m by omega); omega
      omega
  · have hbc : b = 0 ∧ c = 1 := by omega
    obtain ⟨rfl, rfl⟩ := hbc
    simp only [show 255 - 0 + 1 = 256 from rfl, Nat.mod_self, Nat.div_self (show 0 < 256 by decide),
      Nat.zero_add, Nat.add_zero]
    rw [hP, show 256 * 256 ^ m - 1 - 256 * B + 1 = 256 * (256 ^ m - B) by
      have : 256 * B + 256 ≤ 256 * 256 ^ m := by
        have := Nat.mul_le_mul_left 256 (show B + 1 ≤ 256 ^ m by omega); omega
      rw [Nat.mul_sub]; omega]
    rw [Nat.mul_mod_mul_left, show 256 ^ m - 1 - B + 1 = 256 ^ m - B by omega]

theorem xor255 (b : Nat) (hb : b < 256) : 255 ^^^ b = 255 - b := xor_mask 8 b hb

theorem fromByteArrayLoop_signed :
    ∀ xs c accum bits, accum < 2 ^ bits → bits < 30 → AllBytes xs → c ≤ 1 →
      digitsValue (fromByteArrayLoop true xs c accum bits) = accum + 2 ^ bits * twosVal xs c := by
  intro xs
  induction xs with
  | nil =>
    intro c accum bits ha hb _ _
    simp only [fromByteArrayLoop, twosVal, List.length_nil, Nat.pow_zero, Nat.mod_one,
      Nat.mul_zero, Nat.add_zero]
    split
    · simp [digitsValue]
    · rename_i h; have : bits = 0 := by omega
      subst this; simp [digitsValue]; omega
  | cons b bs ih =>
    intro c accum bits ha hb hall hc
    have hb256 := hall b (by simp)
    have hrest : AllBytes bs := fun x hx => hall x (by simp [hx])
    simp only [fromByteArrayLoop, ite_true, xor255 b hb256]
    rw [and_mask_eq_mod (255 - b + c) 8, Nat.shiftRight_eq_div_pow]
    have hb' : (255 - b + c) % 2 ^ 8 < 256 := Nat.mod_lt _ (by decide)
    have hc' : (255 - b + c) / 2 ^ 8 ≤ 1 := by
      apply Nat.le_of_lt_succ; apply (Nat.div_lt_iff_lt_mul (by decide)).mpr; omega
    obtain ⟨e, hlt, hstep⟩ := pack_step accum bits ((255 - b + c) % 2 ^ 8)
      (twosVal bs ((255 - b + c) / 2 ^ 8)) ha hb'
    rw [e]
    have hcons := twosVal_cons b bs c hb256 hc hrest
    simp only [show (2 : Nat) ^ 8 = 256 from rfl] at *
    split
    · rename_i h30
      simp only [digitsValue]
      rw [ih _ _ _ (by
          rw [Nat.shiftRight_eq_div_pow]
          apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
          rw [← Nat.pow_add, show bits + 8 - 30 + 30 = bits + 8 by omega]; exact hlt)
        (by omega) hrest hc']
      rcases hstep with h | h
      · rw [h, hcons]
      · omega
    · rename_i h30
      rw [ih _ _ _ hlt (by omega) hrest hc', ← hcons, Nat.pow_add]
      grind

theorem countInsignificant_spec (ins : Nat) : ∀ l : List Nat,
    l = List.replicate (countInsignificant ins l) ins ++ l.drop (countInsignificant ins l) ∧
      countInsignificant ins l ≤ l.length := by
  intro l
  induction l with
  | nil => simp [countInsignificant]
  | cons b bs ih =>
    unfold countInsignificant
    by_cases h : b ≠ ins
    · simp [h]
    · have hb : b = ins := by omega
      simp only [h, ite_false, List.replicate_succ, List.drop_succ_cons, List.cons_append,
        List.length_cons]
      exact ⟨by rw [hb]; congr 1; exact ih.1, by omega⟩

theorem bytesVal_pos_of_last (bs : List Nat) (h : 128 ≤ bs.getLastD 0) : 1 ≤ bytesVal bs := by
  refine Classical.byContradiction fun h0 => ?_
  have hz : ∀ b ∈ bs, b = 0 := by
    clear h
    induction bs with
    | nil => simp
    | cons x xs ih =>
      simp only [bytesVal] at h0
      intro b hb
      rcases List.mem_cons.mp hb with e | e
      · omega
      · exact ih (by omega) b e
  cases bs with
  | nil => simp at h
  | cons x xs =>
    have hm : (x :: xs).getLastD 0 ∈ x :: xs := by
      rw [List.getLastD_eq_getLast?]
      have := List.getLast_mem (l := x :: xs) (by simp)
      rw [List.getLast?_eq_getLast (by simp)]; simpa using this
    have := hz _ hm; omega

/-- `_PyLong_FromByteArray`, longobject.c:1000-1107: the unsigned value of the
bytes, or their two's-complement value when `is_signed` and the top bit is set. -/
theorem fromByteArray_spec (lsb : List Nat) (signed : Bool) (hall : AllBytes lsb) :
    fromByteArray lsb signed = bytesSigned lsb signed := by
  unfold fromByteArray bytesSigned
  by_cases hn : lsb.length = 0
  · have : lsb = [] := List.eq_nil_of_length_eq_zero hn
    subst this; simp [bytesVal]
  simp only [hn, ite_false]
  generalize hS : (signed && decide (lsb.getLastD 0 ≥ 128)) = isS
  have hcond : (signed = true ∧ lsb.getLastD 0 ≥ 128) ↔ isS = true := by
    rw [← hS]; simp
  generalize hins : (if isS = true then 255 else 0) = ins
  obtain ⟨hsplit, hile⟩ := countInsignificant_spec ins lsb.reverse
  generalize hi : countInsignificant ins lsb.reverse = i at hsplit hile
  simp only [List.length_reverse] at hile
  generalize hP : (lsb.reverse.drop i).reverse = P
  have hlsb : lsb = P ++ List.replicate i ins := by
    have := congrArg List.reverse hsplit
    rw [List.reverse_reverse, List.reverse_append, List.reverse_replicate] at this
    rw [← hP]; exact this
  have hPlen : P.length = lsb.length - i := by
    rw [← hP]; simp
  have hPall : AllBytes P := fun x hx => hall x (by rw [hlsb]; simp [hx])
  have htake : lsb.take (lsb.length - i) = P := by
    rw [← hPlen]
    have : (P ++ List.replicate i ins).take P.length = P := by simp
    rw [← hlsb] at this; exact this
  generalize hN : lsb.length = n at *
  cases isS with
  | false =>
    have hins0 : ins = 0 := by rw [← hins]; rfl
    subst hins0
    simp only [Bool.false_eq_true, false_and, ite_false]
    rw [htake, fromByteArrayLoop_unsigned P 1 0 0 (by decide) (by decide) hPall]
    have : ¬ (signed = true ∧ lsb.getLastD 0 ≥ 128) := by rw [hcond]; simp
    simp only [this, ite_false, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
    rw [hlsb, bytesVal_append, bytesVal_replicate_zero, Nat.mul_zero, Nat.add_zero]
  | true =>
    have hins255 : ins = 255 := by rw [← hins]; rfl
    subst hins255
    have hsg := hcond.mpr rfl
    simp only [hsg, and_self, ite_true]
    by_cases hi0 : i = 0
    · subst hi0
      simp only [Nat.sub_zero, Nat.lt_irrefl, and_false, ite_false, Int.neg_neg] at htake ⊢
      have hlsb' : lsb = P := by simpa using hlsb
      rw [htake, fromByteArrayLoop_signed P 1 0 0 (by decide) (by decide) hPall (by decide)]
      have hB1 := bytesVal_pos_of_last lsb hsg.2
      rw [hlsb'] at hB1 hN
      have hB2 := bytesVal_lt P hPall
      rw [hN] at hB2
      have key : twosVal P 1 = 256 ^ n - bytesVal P := by
        unfold twosVal
        rw [hN, show 256 ^ n - 1 - bytesVal P + 1 = 256 ^ n - bytesVal P by omega,
          Nat.mod_eq_of_lt (by omega)]
      rw [key, hlsb']
      simp only [Nat.pow_zero, Nat.one_mul, Nat.zero_add]
      have c1 : ((256 : Nat) : Int) ^ n = (256 : Int) ^ n := rfl
      omega
    · have hk : (if n - i < n then n - i + 1 else n - i) = n - i + 1 := by simp; omega
      simp only [show n - i < n by omega, and_self, ite_true]
      have htake2 : lsb.take (n - i + 1) = P ++ [255] := by
        rw [hlsb, List.take_append, List.take_of_length_le (by omega), hPlen,
          show n - i + 1 - (n - i) = 1 by omega]
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        simp [List.replicate_succ]
      rw [htake2, fromByteArrayLoop_signed _ 1 0 0 (by decide) (by decide)
        (fun x hx => by simp at hx; rcases hx with hx | hx; exact hPall x hx; omega) (by decide)]
      have hB2 := bytesVal_lt P hPall
      unfold twosVal
      simp only [List.length_append, List.length_singleton, bytesVal_append, bytesVal,
        hPlen, hN, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
      rw [hPlen] at hB2
      have hpow : 256 ^ (n - i + 1) = 256 * 256 ^ (n - i) := by rw [Nat.pow_succ, Nat.mul_comm]
      have e1 : 256 ^ (n - i + 1) - 1 - (bytesVal P + 256 ^ (n - i) * 255) + 1 =
          256 ^ (n - i) - bytesVal P := by rw [hpow]; omega
      rw [e1, Nat.mod_eq_of_lt (by rw [hpow]; omega)]
      have hrep := bytesVal_replicate_255 i
      have hL : bytesVal lsb = bytesVal P + 256 ^ (n - i) * bytesVal (List.replicate i 255) := by
        rw [hlsb, bytesVal_append, hPlen]
      have hpn : 256 ^ (n - i) * 256 ^ i = 256 ^ n := by rw [← Nat.pow_add]; congr 1; omega
      rw [hL]
      have : 256 ^ (n - i) * bytesVal (List.replicate i 255) = 256 ^ n - 256 ^ (n - i) := by
        rw [← hpn, show bytesVal (List.replicate i 255) = 256 ^ i - 1 by omega, Nat.mul_sub,
          Nat.mul_one]
      rw [this]
      have : 256 ^ (n - i) ≤ 256 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
      have c1 : ((256 : Nat) : Int) ^ n = (256 : Int) ^ n := rfl
      omega

end PyLean.MathInt
