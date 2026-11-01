import PyLean.LongObj.PylongPow

/-!
The string conversions of `Lib/_pylong.py` are exact, and with them the whole of
`str(int)` and, below the `_decimal` switch, `int(str)`.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt

/-! ## Dictionaries of powers -/

theorem dGet_key {d : PowDict Nat} {b M W needHi x}
    (hv : ∀ k v, dGet k d = some v → v = b ^ k)
    (hk : ∀ k, (dGet k d).isSome ↔ ∃ x, Reach M W x ∧ M < x ∧ k = whichOf needHi x)
    (hr : Reach M W x) (hx : M < x) : dGet (whichOf needHi x) d = some (b ^ whichOf needHi x) := by
  have hs := (hk _).2 ⟨x, hr, hx, rfl⟩
  cases h : dGet (whichOf needHi x) d with
  | none => rw [h] at hs; cases hs
  | some v => rw [hv _ _ h]

theorem whichOf_false (x : Nat) : whichOf false x = x >>> 1 := by simp [whichOf]

/-! ## `int_to_decimal` -/

theorem itdec_spec {d : PowDict Nat} {W : Nat} (hk : ∀ x, Reach 200 W x → 200 < x →
    dGet (x >>> 1) d = some (2 ^ (x >>> 1))) : ∀ (f n w : Nat), w < f → Reach 200 W w →
    itdecInner d f n w = .ok n
  | 0, _, _, h, _ => by omega
  | f + 1, n, w, h, hr => by
    rw [itdecInner]
    by_cases hw : w ≤ 200
    · rw [if_pos hw]
    · rw [if_neg hw]
      have hsh := shr1 w
      obtain ⟨w2, hw2⟩ : ∃ w2, w >>> 1 = w2 := ⟨_, rfl⟩
      have hM : 200 < w := by omega
      have r1 : Reach 200 W w2 := hw2 ▸ Reach.lo hr hM
      have r2 : Reach 200 W (w - w2) := hw2 ▸ Reach.hi hr hM
      have e1 := itdec_spec hk f (n &&& ((1 <<< w2) - 1)) w2 (by omega) r1
      have e2 := itdec_spec hk f (n >>> w2) (w - w2) (by omega) r2
      have e3 := hk w hr hM
      rw [hw2] at e3
      simp only [hw2, e1, e2, bindOk, e3, pureOk]
      congr 1
      rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
        Nat.mul_comm]
      exact Nat.mod_add_div n (2 ^ w2)

/-- `int_to_decimal` returns a `Decimal` equal to `n`. -/
theorem intToDecimal_spec (n : Int) : intToDecimal n = .ok n := by
  obtain ⟨d, e, hv, hk⟩ := computePowersNat_spec (bitLength n.natAbs) 2 200 false
  have hkey : ∀ x, Reach 200 (bitLength n.natAbs) x → 200 < x →
      dGet (x >>> 1) d = some (2 ^ (x >>> 1)) := by
    intro x hr hx
    have := dGet_key hv hk hr hx
    simpa [whichOf_false] using this
  unfold intToDecimal
  simp only [e, bindOk, itdec_spec hkey _ _ _ (Nat.lt_succ_self _) Reach.top, pureOk]
  congr 1
  split <;> omega

/-! ## `int_to_decimal_string` -/

theorem zdigits_zero (E : Nat) : zdigits 10 E 0 = List.replicate E '0' := by
  induction E with
  | zero => rfl
  | succ E ih =>
    simp only [zdigits, Nat.zero_div, Nat.zero_mod, ih]
    rw [List.replicate_succ']
    rfl

theorem zdigits_form (E : Nat) : ∀ x, x < 10 ^ (E + 1) → zdigits 10 (E + 1) x =
    List.replicate (E + 1 - (Nat.toDigits 10 x).length) '0' ++ Nat.toDigits 10 x := by
  induction E with
  | zero =>
    intro x hx
    have hx10 : x < 10 := by simpa using hx
    have hm : x % 10 = x := Nat.mod_eq_of_lt hx10
    rw [Nat.toDigits_of_lt_base hx10]
    simp [zdigits, hm]
  | succ E ih =>
    intro x hx
    rw [show E + 1 + 1 = (E + 1) + 1 from rfl, zdigits]
    by_cases hx10 : x < 10
    · have hd : x / 10 = 0 := Nat.div_eq_of_lt hx10
      have hm : x % 10 = x := Nat.mod_eq_of_lt hx10
      rw [hd, hm, zdigits_zero, Nat.toDigits_of_lt_base hx10]
      simp
    · have hge : 10 ≤ x := by omega
      have hlt : x / 10 < 10 ^ (E + 1) := by
        apply Nat.div_lt_of_lt_mul
        rw [Nat.pow_succ 10 (E + 1), Nat.mul_comm] at hx
        exact hx
      rw [ih _ hlt, Nat.toDigits_of_base_le (by decide) hge, List.append_assoc]
      have hl : (Nat.toDigits 10 (x / 10) ++ [(x % 10).digitChar]).length =
          (Nat.toDigits 10 (x / 10)).length + 1 := by simp
      rw [hl, show E + 1 + 1 - ((Nat.toDigits 10 (x / 10)).length + 1) =
        E + 1 - (Nat.toDigits 10 (x / 10)).length by omega]

/-- A string of zeros and the digits of `n`. -/
def ZForm (s : List Char) (n : Nat) : Prop := ∃ k, s = List.replicate k '0' ++ Nat.toDigits 10 n

theorem zform_zdigits {s : List Char} {n E : Nat} (h : ZForm s n) (hlen : s.length = E + 1)
    (hn : n < 10 ^ (E + 1)) : s = zdigits 10 (E + 1) n := by
  obtain ⟨k, rfl⟩ := h
  rw [zdigits_form E n hn]
  simp only [List.length_append, List.length_replicate] at hlen
  rw [show E + 1 - (Nat.toDigits 10 n).length = k by omega]

theorem length_zfill {b : List Char} {w : Nat} (h : b.length ≤ w) : (zfill b w).length = w := by
  simp [zfill]; omega

theorem zform_zfill {b : List Char} {n w : Nat} (h : ZForm b n) : ZForm (zfill b w) n := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨w - (List.replicate k '0' ++ Nat.toDigits 10 n).length + k, ?_⟩
  simp only [zfill, ← List.append_assoc, List.replicate_append_replicate]

theorem itds_spec {strf : Int → Py (List Char)} {d : PowDict Nat} {W : Nat}
    (hleaf : ∀ n : Nat, n < 10 ^ 1001 → strf n = .ok (Nat.toDigits 10 n))
    (hk : ∀ x, Reach 1000 W x → 1000 < x → dGet (x >>> 1) d = some (10 ^ (x >>> 1))) :
    ∀ (f n w : Nat), w < f → Reach 1000 W w → n < 10 ^ (w + 1) → 1 ≤ w →
      ∃ s, itdsInner strf d f n w = .ok s ∧ ZForm s n ∧ (n < 10 ^ w → s.length ≤ w)
  | 0, _, _, h, _, _, _ => by omega
  | f + 1, n, w, h, hr, hn, hw1 => by
    rw [itdsInner]
    by_cases hw : w ≤ 1000
    · rw [if_pos hw]
      have hb : n < 10 ^ 1001 :=
        Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) (by omega))
      refine ⟨_, hleaf n hb, ⟨0, by simp⟩, fun hlt => ?_⟩
      exact (Nat.length_toDigits_le_iff (by decide) hw1).2 hlt
    · rw [if_neg hw]
      have hsh := shr1 w
      have hM : 1000 < w := by omega
      have e3 := hk w hr hM
      obtain ⟨w2, hw2⟩ : ∃ w2, w >>> 1 = w2 := ⟨_, rfl⟩
      rw [hw2] at e3 hsh
      have r1 : Reach 1000 W w2 := hw2 ▸ Reach.lo hr hM
      have r2 : Reach 1000 W (w - w2) := hw2 ▸ Reach.hi hr hM
      have hw2pos : 1 ≤ w2 := by omega
      simp only [hw2, e3]
      have hP : 0 < 10 ^ w2 := Nat.pow_pos (by decide)
      have hlo : n % 10 ^ w2 < 10 ^ w2 := Nat.mod_lt _ hP
      have hlo2 : n % 10 ^ w2 < 10 ^ (w2 + 1) :=
        Nat.lt_of_lt_of_le hlo (Nat.pow_le_pow_right (by decide) (by omega))
      have hsplit : 10 ^ (w + 1) = 10 ^ w2 * 10 ^ (w - w2 + 1) := by
        rw [← Nat.pow_add]; congr 1; omega
      have hhi : n / 10 ^ w2 < 10 ^ (w - w2 + 1) := by
        apply Nat.div_lt_of_lt_mul
        rw [← hsplit]; exact hn
      obtain ⟨a, ea, a1, a2⟩ := itds_spec hleaf hk f _ (w - w2) (by omega) r2 hhi (by omega)
      obtain ⟨b, eb, b1, b2⟩ := itds_spec hleaf hk f _ w2 (by omega) r1 hlo2 hw2pos
      have hblen := b2 hlo
      have hz : zfill b w2 = zdigits 10 w2 (n % 10 ^ w2) := by
        obtain ⟨E, rfl⟩ : ∃ E, w2 = E + 1 := ⟨w2 - 1, by omega⟩
        exact zform_zdigits (zform_zfill b1) (length_zfill hblen) hlo
      have hndec : n = n / 10 ^ w2 * 10 ^ w2 + n % 10 ^ w2 := by
        rw [Nat.mul_comm]; exact (Nat.div_add_mod n _).symm
      refine ⟨a ++ zfill b w2, by simp only [ea, eb, bindOk, pureOk], ?_, ?_⟩
      · rw [hz]
        obtain ⟨k, rfl⟩ := a1
        by_cases h0 : n / 10 ^ w2 = 0
        · have hnl : n = n % 10 ^ w2 := by rw [h0, Nat.zero_mul, Nat.zero_add] at hndec; exact hndec
          obtain ⟨E, hE⟩ : ∃ E, w2 = E + 1 := ⟨w2 - 1, by omega⟩
          have hzf := zdigits_form E (n % 10 ^ w2) (by rw [← hE]; exact hlo)
          rw [← hE] at hzf
          rw [hzf, h0, Nat.toDigits_zero]
          refine ⟨k + (1 + (w2 - (Nat.toDigits 10 (n % 10 ^ w2)).length)), ?_⟩
          conv => rhs; rw [hnl]
          rw [← List.replicate_append_replicate, ← List.replicate_append_replicate]
          simp [List.append_assoc]
        · have hpos : 0 < n / 10 ^ w2 := Nat.pos_of_ne_zero h0
          refine ⟨k, ?_⟩
          conv => rhs; rw [hndec]
          rw [toDigits_add_pow (by decide) w2 _ _ hpos hlo, List.append_assoc]
      · intro hlt
        have hhi2 : n / 10 ^ w2 < 10 ^ (w - w2) := by
          apply Nat.div_lt_of_lt_mul
          rw [← Nat.pow_add, show w2 + (w - w2) = w by omega]
          exact hlt
        have := a2 hhi2
        rw [List.length_append, length_zfill hblen]
        omega

theorem dGet_mapK (g : Nat → Nat → Nat) (k : Nat) : ∀ d : PowDict Nat,
    dGet k (d.map (fun kv => (kv.1, g kv.1 kv.2))) = (dGet k d).map (g k)
  | [] => rfl
  | (a, v) :: d => by
    have ih := dGet_mapK g k d
    unfold dGet at ih ⊢
    simp only [List.map_cons, List.lookup_cons]
    by_cases hk : k = a
    · subst hk
      simp
    · have : (k == a) = false := by simpa using hk
      simp only [this]
      exact ih

/-- The estimate of `int_to_decimal_string` is within one digit of an upper bound. -/
theorem decEstimate_bound {w0 : Nat} (h : w0 ≤ 450000) : 2 ^ w0 ≤ 10 ^ (decEstimate w0 + 1) := by
  have h1 : (2 : Nat) ^ 13301 ≤ 10 ^ 4004 := by decide +kernel
  obtain ⟨E, hE⟩ : ∃ E, decEstimate w0 + 1 = E := ⟨_, rfl⟩
  rw [hE]
  have hlin : 4004 * w0 ≤ E * 13301 := by
    unfold decEstimate at hE
    omega
  have hp : (2 ^ w0) ^ 13301 ≤ (10 ^ E) ^ 13301 := by
    calc (2 ^ w0) ^ 13301 = (2 ^ 13301) ^ w0 := by
          rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]
      _ ≤ (10 ^ 4004) ^ w0 := Nat.pow_le_pow_left h1 _
      _ = 10 ^ (4004 * w0) := (Nat.pow_mul ..).symm
      _ ≤ 10 ^ (E * 13301) := Nat.pow_le_pow_right (by decide) hlin
      _ = (10 ^ E) ^ 13301 := Nat.pow_mul ..
  exact (Nat.pow_le_pow_iff_left (by decide)).1 hp

theorem toDigits_head : ∀ {m : Nat}, 0 < m → ∃ c t, Nat.toDigits 10 m = c :: t ∧ c ≠ '0' := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hm
    by_cases h : m < 10
    · refine ⟨_, _, Nat.toDigits_of_lt_base h, ?_⟩
      simp
      omega
    · have hge : 10 ≤ m := by omega
      obtain ⟨c, t, e, hc⟩ := ih (m / 10) (by omega) (by omega)
      refine ⟨c, t ++ [(m % 10).digitChar], ?_, hc⟩
      rw [Nat.toDigits_of_base_le (by decide) hge, e]
      rfl

theorem dropWhile_zeros {c : Char} {t : List Char} (hc : c ≠ '0') : ∀ k,
    (List.replicate k '0' ++ c :: t).dropWhile (· == '0') = c :: t
  | 0 => by simp [List.dropWhile_cons, hc]
  | k + 1 => by
    rw [List.replicate_succ, List.cons_append, List.dropWhile_cons, if_pos (by simp)]
    exact dropWhile_zeros hc k

/-- `int_to_decimal_string` returns the decimal digits of `n` whenever `str` does on the
small pieces. -/
theorem intToDecimalString_spec {strf : Int → Py (List Char)}
    (hleaf : ∀ n : Nat, n < 10 ^ 1001 → strf n = .ok (Nat.toDigits 10 n)) (n : Int) :
    intToDecimalString strf n = .ok (decStr n) := by
  unfold intToDecimalString
  dsimp only
  by_cases hw : bitLength n.natAbs > 450000
  · rw [if_pos hw]
    simp only [intToDecimal_spec, bindOk, pureOk]
  · rw [if_neg hw]
    obtain ⟨m, hm⟩ : ∃ m, n.natAbs = m := ⟨_, rfl⟩
    rw [hm] at hw ⊢
    unfold decStr
    rw [hm]
    have hw0 : bitLength m ≤ 450000 := by omega
    have hbound := decEstimate_bound hw0
    obtain ⟨W, hW⟩ : ∃ W, decEstimate (bitLength m) = W := ⟨_, rfl⟩
    rw [hW] at hbound
    have hW1 : 1 ≤ W := by
      rw [← hW]
      unfold decEstimate
      omega
    obtain ⟨d, e, hv, hk⟩ := computePowersNat_spec W 5 1000 false
    have hkey : ∀ x, Reach 1000 W x → 1000 < x →
        dGet (x >>> 1) (d.map (fun kv => (kv.1, kv.2 <<< kv.1))) = some (10 ^ (x >>> 1)) := by
      intro x hr hx
      have h1 := dGet_key hv hk hr hx
      rw [whichOf_false] at h1
      have h2 := dGet_mapK (fun k v => v <<< k) (x >>> 1) d
      rw [h2, h1]
      simp only [Option.map_some]
      congr 1
      rw [Nat.shiftLeft_eq, ← Nat.mul_pow]
    have hlt : m < 10 ^ (W + 1) := Nat.lt_of_lt_of_le (lt_two_pow_bitLength' _) hbound
    obtain ⟨s, es, ⟨k, hs⟩, _⟩ := itds_spec hleaf hkey (W + 1) m W (Nat.lt_succ_self _) Reach.top
      hlt hW1
    simp only [hW, e, bindOk, es, pureOk]
    congr 2
    by_cases hm0 : m = 0
    · subst hm0
      have hW2 : W = 1 := by
        rw [← hW]
        decide
      subst hW2
      have hes := es
      rw [itdsInner, if_pos (by decide), hleaf 0 (Nat.pow_pos (by decide))] at hes
      injection hes with hes
      rw [← hes]
      simp
    · obtain ⟨c, t, ed, hc⟩ := toDigits_head (by omega : 0 < m)
      rw [hs, ed]
      cases k with
      | zero =>
        have : ¬ (((List.replicate 0 '0' ++ c :: t).head? = some '0') ∧ m ≠ 0) := by
          simp [hc]
        rw [if_neg this]
        rfl
      | succ k =>
        have : ((List.replicate (k + 1) '0' ++ c :: t).head? = some '0') ∧ m ≠ 0 := by
          refine ⟨by simp [List.replicate_succ], hm0⟩
        rw [if_pos this]
        exact dropWhile_zeros hc (k + 1)

/-! ## `str(int)` -/

/-- `_PyLong_DigitCount` of `v`. -/
def sizeOf' (v : Int) : Nat := digitCount v.natAbs

/-- Decimal digits of `v`, without the sign. -/
def numDigits (v : Int) : Nat := (Nat.toDigits 10 v.natAbs).length

theorem ofInt_ds (v : Int) : (Long.ofInt v).ds = digitsOf v.natAbs := rfl
theorem ofInt_neg_flag (v : Int) : (Long.ofInt v).neg = decide (v < 0) := rfl

theorem length_ofInt (v : Int) : (Long.ofInt v).ds.length = sizeOf' v := by
  rw [ofInt_ds, length_digitsOf]
  rfl

theorem val_ofInt (v : Int) : val (Long.ofInt v).ds = v.natAbs := by
  rw [ofInt_ds, val_digitsOf]

/-- The whole of `long_to_decimal_string_internal` up to the switch. -/
theorem longToDecimalWith_eq (pyl : Long → Py (List Char)) {lim : Nat} (hlim : ValidLimit lim)
    (v : Int) :
    longToDecimalWith pyl lim (Long.ofInt v) =
      if sizeOf' v ≥ 73 ∧ lim > 0 ∧ lim / 90 ≤ (sizeOf' v - 11) / 10 then
        .error (.valueError (limitToStrMsg lim))
      else if sizeOf' v > 1000 then pyl (Long.ofInt v)
      else if lim > 0 ∧ numDigits v > lim then .error (.valueError (limitToStrMsg lim))
      else .ok (decStr v) := by
  unfold longToDecimalWith decPreCheck
  dsimp only
  rw [length_ofInt]
  have h73 : 10 * strDigitsThreshold / (3 * 30) + 2 = 73 := by decide
  have h90 : 3 * 30 = 90 := by decide
  rw [h73, h90]
  by_cases h1 : sizeOf' v ≥ 73 ∧ lim > 0 ∧ lim / 90 ≤ (sizeOf' v - 11) / 10
  · rw [if_pos h1, if_pos h1.1, if_pos h1.2]
    rfl
  · rw [if_neg h1]
    have hcheck : (if sizeOf' v ≥ 73 then
        (if lim > 0 ∧ lim / 90 ≤ (sizeOf' v - 11) / 10 then
          (.error (.valueError (limitToStrMsg lim)) : Py Unit) else .ok ()) else .ok ()) = .ok () := by
      by_cases h2 : sizeOf' v ≥ 73
      · rw [if_pos h2, if_neg (fun h3 => h1 ⟨h2, h3⟩)]
      · rw [if_neg h2]
    rw [hcheck]
    simp only [bindOk]
    by_cases h3 : sizeOf' v > 1000
    · rw [if_pos h3, if_pos h3]
    · rw [if_neg h3, if_neg h3]
      have hs : 1 + (Long.ofInt v).ds.length + (Long.ofInt v).ds.length / 99 ≤ maxLongDigits := by
        rw [length_ofInt]
        have : maxLongDigits = 307445734561825860 := by decide
        omega
      rw [decCore_spec lim _ (digitsOf_digits _) hs, val_ofInt]
      obtain ⟨D, hD⟩ : ∃ D, (Nat.toDigits 10 v.natAbs).length = D := ⟨_, rfl⟩
      rw [hD]
      have hnum : numDigits v = D := hD
      rw [hnum]
      have hthr : strDigitsThreshold = 640 := rfl
      have heq : ((if (Long.ofInt v).neg = true then 1 else 0) + D > strDigitsThreshold ∧ lim > 0 ∧
          D > lim) ↔ (lim > 0 ∧ D > lim) := by
        constructor
        · exact fun h => h.2
        · intro h
          refine ⟨?_, h⟩
          rcases hlim with h0 | h0
          · omega
          · have : 0 ≤ (if (Long.ofInt v).neg = true then 1 else 0) := Nat.zero_le _
            omega
      by_cases h4 : lim > 0 ∧ D > lim
      · rw [if_pos (heq.2 h4), if_pos h4]
      · rw [if_neg (fun h => h4 (heq.1 h)), if_neg h4, ofInt_neg_flag]
        unfold decStr
        simp only [val_ofInt, decide_eq_true_eq]

theorem numDigits_lt_of_lt {v : Int} {L : Nat} (hL : 0 < L) (h : v.natAbs < 10 ^ L) :
    numDigits v ≤ L := (Nat.length_toDigits_le_iff (by decide) hL).2 h

theorem precheck_digits {lim : Nat} {v : Int} (h1 : sizeOf' v ≥ 73) (h2 : lim > 0)
    (h3 : lim / 90 ≤ (sizeOf' v - 11) / 10) : numDigits v > lim := by
  have hV : 1 ≤ v.natAbs := by
    rcases Nat.eq_zero_or_pos v.natAbs with h | h
    · have hs : sizeOf' v = 0 := by
        unfold sizeOf'
        rw [h]
        decide
      omega
    · exact h
  exact decPreCheck_sound h2 hV h3 (by unfold sizeOf' at h1; omega)

/-- Pieces of `int_to_decimal_string` are below the `_pylong` switch and the limit. -/
theorem leaf_str {f lim : Nat} (hlim : ValidLimit lim) (hl : lim = 0 ∨ 1001 ≤ lim) (n : Nat)
    (hn : n < 10 ^ 1001) : longStrF (f + 1) lim (Long.ofInt (n : Int)) = .ok (Nat.toDigits 10 n) := by
  have h2 : (10 : Nat) ^ 1001 ≤ 2 ^ 30000 := by decide +kernel
  have hb : bitLength n ≤ 30000 := bitLength_le_of_lt' (by omega)
  have hsz : sizeOf' (n : Int) ≤ 1000 := by
    unfold sizeOf' digitCount
    simp only [Int.natAbs_natCast]
    omega
  have hD : numDigits (n : Int) ≤ 1001 := numDigits_lt_of_lt (by decide) (by simpa using hn)
  rw [longStrF, longToDecimalWith_eq _ hlim]
  have hn1 : ¬ (sizeOf' (n : Int) ≥ 73 ∧ lim > 0 ∧ lim / 90 ≤ (sizeOf' (n : Int) - 11) / 10) := by
    rintro ⟨h3, h4, h5⟩
    have := precheck_digits h3 h4 h5
    omega
  have hn2 : ¬ sizeOf' (n : Int) > 1000 := by omega
  have hn3 : ¬ (lim > 0 ∧ numDigits (n : Int) > lim) := by omega
  rw [if_neg hn1, if_neg hn2, if_neg hn3]
  simp [decStr]

/-- `str(v)`: the complete behaviour, for every limit `sys.set_int_max_str_digits` admits.
Beyond 1000 digits of `2**30` only the pre-check guards the limit. -/
theorem longToDecimalString_eq {lim : Nat} (hlim : ValidLimit lim) (v : Int) :
    longToDecimalString lim (Long.ofInt v) =
      if sizeOf' v ≤ 1000 then
        if lim > 0 ∧ numDigits v > lim then .error (.valueError (limitToStrMsg lim))
        else .ok (decStr v)
      else
        if lim > 0 ∧ lim / 90 ≤ (sizeOf' v - 11) / 10 then
          .error (.valueError (limitToStrMsg lim))
        else .ok (decStr v) := by
  unfold longToDecimalString
  rw [longStrF, longToDecimalWith_eq _ hlim]
  by_cases hs : sizeOf' v ≤ 1000
  · rw [if_pos hs, if_neg (by omega : ¬ sizeOf' v > 1000)]
    by_cases h1 : sizeOf' v ≥ 73 ∧ lim > 0 ∧ lim / 90 ≤ (sizeOf' v - 11) / 10
    · rw [if_pos h1, if_pos ⟨h1.2.1, precheck_digits h1.1 h1.2.1 h1.2.2⟩]
    · rw [if_neg h1]
  · rw [if_neg hs]
    have hbig : sizeOf' v > 1000 := by omega
    by_cases h1 : lim > 0 ∧ lim / 90 ≤ (sizeOf' v - 11) / 10
    · rw [if_pos ⟨by omega, h1⟩, if_pos h1]
    · rw [if_neg (fun h => h1 h.2), if_neg h1, if_pos hbig]
      have hl : lim = 0 ∨ 1001 ≤ lim := by
        by_cases h0 : lim = 0
        · exact Or.inl h0
        · right
          have : ¬ lim / 90 ≤ (sizeOf' v - 11) / 10 := fun h => h1 ⟨by omega, h⟩
          omega
      have := intToDecimalString_spec (strf := fun n => longStrF 2 lim (Long.ofInt n))
        (fun n hn => leaf_str (f := 1) hlim hl n hn) v
      simpa [Long.toInt_ofInt] using this

end PyLean.LongObj
