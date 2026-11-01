import PyLean.Binary64.Round

/-!
Theorems about `F64`: bit layout, the exact value of a datum, and the correctness of
`F64.ofRat`. `ofRat_nearest`, `ofRat_tie` and `ofRat_inf_iff` together say that it is
IEEE 754 round-to-nearest, ties to even, and every arithmetic operation of the model
is `ofRat` of the exact result.
-/

namespace PyLean.Binary64

theorem dyadic_eq (m : Nat) (e : Int) : dyadic m e = (m : Rat) * pw e := by
  cases e with
  | ofNat k =>
    have : pw (Int.ofNat k) = ((2 ^ k : Nat) : Rat) := pw_natCast k
    rw [this, ← Rat.natCast_mul]; rfl
  | negSucc k =>
    have h : Int.negSucc k = -((k + 1 : Nat) : Int) := by omega
    rw [h, pw_neg, pw_natCast]
    show mkRat m (2 ^ (k + 1)) = _
    have := Rat.mkRat_eq_div (m : Int) (2 ^ (k + 1))
    rw [show mkRat m (2 ^ (k + 1)) = mkRat (m : Int) (2 ^ (k + 1)) from rfl, this]
    rfl

namespace F64

@[ext] theorem ext {x y : F64} (h : x.bits = y.bits) : x = y := by
  cases x; cases y; simp_all

theorem bits_ofBits (n : Nat) : (ofBits n).bits = n % 2 ^ 64 := rfl

theorem bits_ofBits_of_lt {n : Nat} (h : n < 2 ^ 64) : (ofBits n).bits = n :=
  Nat.mod_eq_of_lt h

theorem ofBits_bits (x : F64) : ofBits x.bits = x := by
  ext; exact bits_ofBits_of_lt x.isLt

theorem frac_lt (x : F64) : x.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)

theorem bexp_lt (x : F64) : x.bexp < 2048 := Nat.mod_lt _ (by decide)

theorem bits_decomp (x : F64) :
    x.bits = (if x.sign then 2 ^ 63 else 0) + x.bexp * 2 ^ 52 + x.frac := by
  have := x.isLt
  unfold sign bexp frac
  by_cases h : 2 ^ 63 ≤ x.bits
  · simp only [h, decide_true, ↓reduceIte]; omega
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]; omega

/-- Equal sign, exponent and fraction fields mean equal data. -/
theorem eq_of_fields {x y : F64} (h1 : x.sign = y.sign) (h2 : x.bexp = y.bexp)
    (h3 : x.frac = y.frac) : x = y := by
  ext; rw [bits_decomp x, bits_decomp y, h1, h2, h3]

theorem isNaN_eq (x : F64) : x.isNaN = true ↔ x.bexp = 2047 ∧ x.frac ≠ 0 := by
  simp [isNaN]

theorem isInf_eq (x : F64) : x.isInf = true ↔ x.bexp = 2047 ∧ x.frac = 0 := by
  simp [isInf]

theorem isFinite_eq (x : F64) : x.isFinite = true ↔ x.bexp ≠ 2047 := by
  simp [isFinite]

theorem isZero_eq (x : F64) : x.isZero = true ↔ x.bexp = 0 ∧ x.frac = 0 := by
  simp [isZero]

/-- The three classes partition `F64`. -/
theorem classify (x : F64) : x.isFinite = true ∨ x.isInf = true ∨ x.isNaN = true := by
  simp only [isFinite_eq, isInf_eq, isNaN_eq]; omega

theorem isNaN_false_of_finite {x : F64} (h : x.isFinite = true) : x.isNaN = false := by
  rw [isFinite_eq] at h
  cases hn : x.isNaN
  · rfl
  · rw [isNaN_eq] at hn; omega

theorem isInf_false_of_finite {x : F64} (h : x.isFinite = true) : x.isInf = false := by
  rw [isFinite_eq] at h
  cases hn : x.isInf
  · rfl
  · rw [isInf_eq] at hn; omega

theorem isFinite_of_isZero {x : F64} (h : x.isZero = true) : x.isFinite = true := by
  rw [isZero_eq] at h; rw [isFinite_eq]; omega

theorem mant_lt (x : F64) : x.mant < 2 ^ 53 := by
  have := frac_lt x
  unfold mant; split <;> omega

theorem lsbExp_ge (x : F64) : -1074 ≤ x.lsbExp := by
  unfold lsbExp; omega

theorem lsbExp_le (x : F64) (h : x.isFinite = true) : x.lsbExp ≤ 971 := by
  rw [isFinite_eq] at h
  have := bexp_lt x
  unfold lsbExp; omega

theorem mant_canon (x : F64) : 2 ^ 52 ≤ x.mant ∨ x.lsbExp = -1074 := by
  unfold mant lsbExp
  split
  · right; omega
  · left; omega

theorem toRat_of_finite {x : F64} (h : x.isFinite = true) :
    x.toRat = if x.sign then -((x.mant : Rat) * pw x.lsbExp) else (x.mant : Rat) * pw x.lsbExp := by
  unfold toRat
  simp only [h, ↓reduceIte, dyadic_eq]

theorem toRat_rep {x : F64} (h : x.isFinite = true) : Rep binary64 x.toRat := by
  refine ⟨x.mant, x.lsbExp, mant_lt x, ?_, ?_⟩
  · have := lsbExp_ge x; simpa [Fmt.etiny, binary64] using this
  · rw [toRat_of_finite h]
    split
    · right; rfl
    · left; rfl

theorem toRat_of_not_finite {x : F64} (h : x.isFinite = false) : x.toRat = 0 := by
  simp [toRat, h]

/-! ## Decoding what `encode` produces -/

theorem encode_some (neg : Bool) (m : Nat) (e : Int) :
    binary64.encode neg (some (m, e)) = (if neg then 2 ^ 63 else 0) +
      (if m < 2 ^ 52 then m else (e + 1075).toNat * 2 ^ 52 + (m - 2 ^ 52)) := by
  show (if m < 2 ^ 52 then (if neg then 2 ^ 63 else 0) + m
    else (if neg then 2 ^ 63 else 0) + (e + ((52 : Nat) : Int) + ((1023 : Nat) : Int)).toNat * 2 ^ 52
      + (m - 2 ^ 52)) = _
  have : e + ((52 : Nat) : Int) + ((1023 : Nat) : Int) = e + 1075 := by omega
  rw [this]
  split <;> omega

theorem encode_none (neg : Bool) : ofBits (binary64.encode neg none) = inf neg := by
  cases neg <;> rfl

structure Decoded (x : F64) (neg : Bool) (m : Nat) (e : Int) : Prop where
  sign : x.sign = neg
  finite : x.isFinite = true
  mant : x.mant = m
  lsb : x.lsbExp = e

/-- A canonical `(m, e)` encodes to a datum that decodes back to it. -/
theorem encode_decode (neg : Bool) {m : Nat} {e : Int} (h1 : m < 2 ^ 53) (h2 : -1074 ≤ e)
    (h3 : 2 ^ 52 ≤ m ∨ e = -1074) (h4 : e ≤ 971) :
    Decoded (ofBits (binary64.encode neg (some (m, e)))) neg m e := by
  rw [encode_some]
  by_cases hm : m < 2 ^ 52
  · have he : e = -1074 := by omega
    simp only [hm, ↓reduceIte]
    generalize hb : (if neg then 2 ^ 63 else 0) + m = b
    have hbn : b = (if neg then 9223372036854775808 else 0) + m := by rw [← hb]
    have hlt : b < 2 ^ 64 := by split at hbn <;> omega
    have hbits : (ofBits b).bits = b := bits_ofBits_of_lt hlt
    have hexp : (ofBits b).bexp = 0 := by
      unfold bexp; rw [hbits]; split at hbn <;> omega
    have hfr : (ofBits b).frac = m := by
      unfold frac; rw [hbits]; split at hbn <;> omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold sign; rw [hbits]; cases neg <;> simp at hbn ⊢ <;> try omega
    · rw [isFinite_eq, hexp]; omega
    · unfold mant; simp [hexp, hfr]
    · unfold lsbExp; rw [hexp, he]; rfl
  · have he : 1 ≤ (e + 1075).toNat ∧ (e + 1075).toNat ≤ 2046 := by
      rcases h3 with h3 | h3 <;> omega
    have hee : ((e + 1075).toNat : Int) = e + 1075 := by omega
    simp only [hm, ↓reduceIte]
    generalize (e + 1075).toNat = be at he hee
    generalize hb : (if neg then 2 ^ 63 else 0) + (be * 2 ^ 52 + (m - 2 ^ 52)) = b
    have hbn : b = (if neg then 9223372036854775808 else 0) + (be * 4503599627370496 + (m - 4503599627370496)) := by
      rw [← hb]
    have hlt : b < 2 ^ 64 := by split at hbn <;> omega
    have hbits : (ofBits b).bits = b := bits_ofBits_of_lt hlt
    have hexp : (ofBits b).bexp = be := by
      unfold bexp; rw [hbits]; split at hbn <;> omega
    have hfr : (ofBits b).frac = m - 2 ^ 52 := by
      unfold frac; rw [hbits]; split at hbn <;> omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold sign; rw [hbits]; cases neg <;> simp at hbn ⊢ <;> try omega
    · rw [isFinite_eq, hexp]; omega
    · unfold mant; rw [hexp, hfr]; split <;> omega
    · unfold lsbExp; rw [hexp]; omega

theorem toRat_decoded {x : F64} {neg : Bool} {m : Nat} {e : Int} (h : Decoded x neg m e) :
    x.toRat = if neg then -((m : Rat) * pw e) else (m : Rat) * pw e := by
  rw [toRat_of_finite h.finite, h.sign, h.mant, h.lsb]

end F64

/-! ## What `roundPos` returns -/

/-- The integer `roundPos` rounds to, before any carry. -/
def roundedInt (f : Fmt) (n d : Nat) : Nat :=
  roundInt (divPow2 n d (roundExp f n d)).1 (divPow2 n d (roundExp f n d)).2.1
    (divPow2 n d (roundExp f n d)).2.2

/-- The bounds on `q` that come from the scale. -/
theorem quotient_bounds (f : Fmt) (hp : 2 ≤ f.p) {n d : Nat} (hn : 0 < n) (hd : 0 < d) :
    (divPow2 n d (roundExp f n d)).1 < 2 ^ f.p ∧
      (roundExp f n d = f.etiny ∨ 2 ^ (f.p - 1) ≤ (divPow2 n d (roundExp f n d)).1) := by
  obtain ⟨h1, h2, _⟩ := roundExp_spec f (by omega) hn hd
  obtain ⟨hD, hr, hQ⟩ := divPow2_spec (n := n) hd (roundExp f n d)
  obtain ⟨hx0, hx1, _⟩ := frac_facts hD hr
  generalize roundExp f n d = e at *
  generalize (divPow2 n d e).1 = q at *
  generalize (divPow2 n d e).2.1 = r at *
  generalize (divPow2 n d e).2.2 = D at *
  have hep := pw_pos e
  have hQlt : (n : Rat) / d / pw e < ((2 ^ f.p : Nat) : Rat) := by
    rw [Rat.div_lt_iff hep, ← pw_natCast, ← pw_add, Int.add_comm]; exact h1
  refine ⟨?_, ?_⟩
  · have : (q : Rat) < ((2 ^ f.p : Nat) : Rat) := by grind
    exact Rat.natCast_lt_natCast.1 this
  · rcases h2 with h2 | h2
    · left; exact h2
    · right
      have hQge : ((2 ^ (f.p - 1) : Nat) : Rat) ≤ (n : Rat) / d / pw e := by
        apply Rat.not_lt.1
        intro hc
        rw [Rat.div_lt_iff hep, ← pw_natCast, ← pw_add, Int.add_comm] at hc
        exact absurd h2 (Rat.not_le.2 hc)
      have : ((2 ^ (f.p - 1) : Nat) : Rat) < ((q + 1 : Nat) : Rat) := by
        rw [cast_succ]; grind
      have := Rat.natCast_lt_natCast.1 this
      omega

theorem roundPos_some (f : Fmt) (hp : 2 ≤ f.p) {n d m : Nat} {e : Int} (hn : 0 < n) (hd : 0 < d)
    (h : roundPos f n d = some (m, e)) :
    m < 2 ^ f.p ∧ f.etiny ≤ e ∧ (2 ^ (f.p - 1) ≤ m ∨ e = f.etiny) ∧
      e + ((f.p - 1 : Nat) : Int) ≤ f.emax ∧
      (m : Rat) * pw e = (roundedInt f n d : Rat) * pw (roundExp f n d) ∧
      (roundedInt f n d % 2 = 0 → m % 2 = 0) := by
  obtain ⟨hq1, hq2⟩ := quotient_bounds f hp hn hd
  obtain ⟨_, _, h3⟩ := roundExp_spec f (by omega) hn hd
  have hq' : (roundedInt f n d = (divPow2 n d (roundExp f n d)).1 ∨
      roundedInt f n d = (divPow2 n d (roundExp f n d)).1 + 1) := by
    unfold roundedInt
    rcases roundInt_cases (divPow2 n d (roundExp f n d)).1 (divPow2 n d (roundExp f n d)).2.1
      (divPow2 n d (roundExp f n d)).2.2 with ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ <;> simp [e]
  have hdef : roundPos f n d = (if (f.emax : Int) <
      (if roundedInt f n d = 2 ^ f.p then ((2 ^ (f.p - 1), roundExp f n d + 1) : Nat × Int)
        else (roundedInt f n d, roundExp f n d)).2 + ((f.p - 1 : Nat) : Int) then none
      else some (if roundedInt f n d = 2 ^ f.p then ((2 ^ (f.p - 1), roundExp f n d + 1) : Nat × Int)
        else (roundedInt f n d, roundExp f n d))) := rfl
  rw [hdef] at h
  generalize roundedInt f n d = q' at *
  generalize roundExp f n d = e0 at *
  generalize (divPow2 n d e0).1 = q at *
  have h2p : 2 ^ f.p = 2 * 2 ^ (f.p - 1) := by
    rw [show f.p = f.p - 1 + 1 by omega, Nat.pow_succ]; simp; omega
  have h2p' : 2 ^ (f.p - 1) = 2 * 2 ^ (f.p - 2) := by
    rw [show f.p - 1 = f.p - 2 + 1 by omega, Nat.pow_succ]; omega
  by_cases hc : q' = 2 ^ f.p
  · simp only [hc, ↓reduceIte] at h
    split at h
    · simp at h
    · rename_i hle
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst hc
      refine ⟨by omega, by omega, Or.inl (Nat.le_refl _), by omega, ?_, ?_⟩
      · rw [pw_succ, h2p]; push_cast; grind
      · intro _; omega
  · simp only [hc, ↓reduceIte] at h
    split at h
    · simp at h
    · rename_i hle
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by omega, h3, ?_, by omega, rfl, id⟩
      rcases hq2 with h | h
      · right; exact h
      · left; omega

/-- Halfway between `DBL_MAX` and `2 ^ 1024`: from here on a value rounds to infinity. -/
def overflowLimit : Rat := ((2 ^ 54 - 1 : Nat) : Rat) * pw 970

/-- A rational as the pair `ofRat` rounds. -/
theorem natAbs_div_den {q : Rat} (h : q ≠ 0) :
    0 < q.num.natAbs ∧ 0 < q.den ∧
      (((q.num.natAbs : Nat) : Rat) / q.den = if q < 0 then -q else q) := by
  have hnum : q.num ≠ 0 := fun h0 => h (Rat.num_eq_zero.1 h0)
  refine ⟨Int.natAbs_pos.2 hnum, q.den_pos, ?_⟩
  have hdiv : (q.num : Rat) / q.den = q := by rw [← Rat.mkRat_eq_div, Rat.mkRat_self]
  split
  · rename_i hq
    have hneg : q.num < 0 := by
      apply Int.not_le.1
      intro h0
      exact absurd (Rat.num_nonneg.1 h0) (Rat.not_le.2 hq)
    have : ((q.num.natAbs : Nat) : Rat) = -(q.num : Rat) := by
      have : ((q.num.natAbs : Nat) : Int) = -q.num := by omega
      rw [← Rat.intCast_natCast, this]; simp
    rw [this]
    conv => rhs; rw [← hdiv]
    simp only [Rat.div_def]; grind
  · rename_i hq
    have hpos : 0 ≤ q.num := by
      have : 0 ≤ q := Rat.not_lt.1 hq
      exact Rat.num_nonneg.2 this
    have : ((q.num.natAbs : Nat) : Rat) = (q.num : Rat) := by
      have : ((q.num.natAbs : Nat) : Int) = q.num := by omega
      rw [← Rat.intCast_natCast, this]
    rw [this, hdiv]

/-- `n / d` at or past the limit is exactly when `roundPos` overflows. -/
theorem roundPos_none_iff {n d : Nat} (hn : 0 < n) (hd : 0 < d) :
    roundPos binary64 n d = none ↔ overflowLimit ≤ (n : Rat) / d := by
  obtain ⟨hlt, h2, h3⟩ := roundExp_spec binary64 (by decide) hn hd
  obtain ⟨hq1, hq2⟩ := quotient_bounds binary64 (by decide) hn hd
  obtain ⟨hD, hr, hQ⟩ := divPow2_spec (n := n) hd (roundExp binary64 n d)
  obtain ⟨hx0, hx1, hup, htie, hdown⟩ := frac_facts hD hr
  have hc := roundInt_cases (divPow2 n d (roundExp binary64 n d)).1
    (divPow2 n d (roundExp binary64 n d)).2.1 (divPow2 n d (roundExp binary64 n d)).2.2
  have hdef : roundPos binary64 n d = (if ((1023 : Nat) : Int) <
      (if roundedInt binary64 n d = 2 ^ 53 then ((2 ^ 52, roundExp binary64 n d + 1) : Nat × Int)
        else (roundedInt binary64 n d, roundExp binary64 n d)).2 + ((52 : Nat) : Int) then none
      else some (if roundedInt binary64 n d = 2 ^ 53 then ((2 ^ 52, roundExp binary64 n d + 1) : Nat × Int)
        else (roundedInt binary64 n d, roundExp binary64 n d))) := rfl
  have hv : (n : Rat) / d = (n : Rat) / d / pw (roundExp binary64 n d) * pw (roundExp binary64 n d) :=
    (Rat.div_mul_cancel (pw_ne _)).symm
  rw [← hQ] at hv
  rw [hdef]
  unfold roundedInt
  have hlt' : (n : Rat) / d < pw (roundExp binary64 n d + 53) := hlt
  have h2' : roundExp binary64 n d = -1074 ∨ pw (roundExp binary64 n d + 52) ≤ (n : Rat) / d := h2
  have hq1' : (divPow2 n d (roundExp binary64 n d)).1 < 2 ^ 53 := hq1
  clear hlt h2 h3 hq1 hq2 hdef hQ
  generalize (n : Rat) / d = v at *
  generalize roundExp binary64 n d = e0 at *
  generalize roundInt (divPow2 n d e0).1 (divPow2 n d e0).2.1 (divPow2 n d e0).2.2 = q' at *
  generalize (divPow2 n d e0).1 = q at *
  generalize (divPow2 n d e0).2.1 = r at *
  generalize (divPow2 n d e0).2.2 = D at *
  generalize (r : Rat) / (D : Nat) = x at *
  have hL := pw_pos 970
  have h971 : pw 971 = 2 * pw 970 := pw_succ 970
  have h53 : pw 53 = 9007199254740992 := by
    have := pw_natCast 53
    simpa using this
  have h1023 : pw 1023 = 9007199254740992 * pw 970 := by
    rw [show (1023 : Int) = 970 + 53 from rfl, pw_add, h53, Rat.mul_comm]
  have h1024 : pw 1024 = 18014398509481984 * pw 970 := by
    rw [show (1024 : Int) = 1023 + 1 from rfl, pw_succ, h1023]; grind
  have hlim : overflowLimit = 18014398509481983 * pw 970 := by
    unfold overflowLimit; congr 1
  rw [hlim]
  have hq'cast : (q : Rat) ≤ 9007199254740991 := by
    have : q ≤ 9007199254740991 := by omega
    exact_mod_cast Rat.natCast_le_natCast.2 this
  constructor
  · intro hnone
    by_cases hcq : q' = 2 ^ 53
    · have he : 971 ≤ e0 := by
        simp only [hcq, ↓reduceIte] at hnone
        by_cases h9 : ((1023 : Nat) : Int) < ((2 ^ 52, e0 + 1) : Nat × Int).2 + ((52 : Nat) : Int)
        · simp only at h9; omega
        · simp only [h9, ↓reduceIte] at hnone; cases hnone
      have hqeq : q = 9007199254740991 := by
        rcases hc with ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ <;> omega
      have hx12 : 1 / 2 ≤ x := by
        rcases hc with ⟨c, e⟩ | ⟨c, _, e⟩ | ⟨c, _, e⟩ | ⟨c, _, e⟩
        · exact Rat.le_of_lt (hup c)
        · have := htie c; grind
        · omega
        · omega
      have hqr : (q : Rat) = 9007199254740991 := by rw [hqeq]; rfl
      have hp : pw 971 ≤ pw e0 := pw_le he
      rw [hv, hqr]
      have h5 : (9007199254740991 + 1 / 2) * pw 971 ≤ ((9007199254740991 : Rat) + x) * pw e0 := by
        have a1 : (9007199254740991 + 1 / 2) * pw 971 ≤ (9007199254740991 + 1 / 2) * pw e0 :=
          Rat.mul_le_mul_of_nonneg_left hp (by decide +kernel)
        have a2 : (9007199254740991 + 1 / 2) * pw e0 ≤ ((9007199254740991 : Rat) + x) * pw e0 :=
          Rat.mul_le_mul_of_nonneg_right (by grind) (Rat.le_of_lt (pw_pos e0))
        exact Rat.le_trans a1 a2
      rw [h971] at h5
      grind
    · have he : 972 ≤ e0 := by
        simp only [hcq, ↓reduceIte] at hnone
        by_cases h9 : ((1023 : Nat) : Int) < ((q', e0) : Nat × Int).2 + ((52 : Nat) : Int)
        · simp only at h9; omega
        · simp only [h9, ↓reduceIte] at hnone; cases hnone
      have hp : pw 1024 ≤ pw (e0 + 52) := pw_le (by omega)
      rcases h2' with h | h
      · omega
      · grind
  · intro hge
    have he0 : 971 ≤ e0 := by
      apply Int.not_lt.1
      intro h
      have : pw (e0 + 53) ≤ pw 1023 := pw_le (by omega)
      grind
    by_cases he9 : 972 ≤ e0
    · split
      · simp only []
        split
        · rfl
        · omega
      · simp only []
        split
        · rfl
        · omega
    · have he : e0 = 971 := by omega
      subst he
      have hQ1 : 9007199254740991 + 1 / 2 ≤ (q : Rat) + x := by
        rw [hv] at hge
        rw [h971] at hge
        apply Rat.le_of_mul_le_mul_right _ (pw_pos 970)
        grind
      have hqeq : q = 9007199254740991 := by
        have : (9007199254740990 : Rat) < (q : Rat) := by grind
        have h2 : ((9007199254740990 : Nat) : Rat) < (q : Rat) := by exact_mod_cast this
        have := Rat.natCast_lt_natCast.1 h2
        omega
      have hx12 : 1 / 2 ≤ x := by
        have hqr : (q : Rat) = 9007199254740991 := by rw [hqeq]; rfl
        grind
      have hq'' : q' = 2 ^ 53 := by
        rcases hc with ⟨c, e⟩ | ⟨c, _, e⟩ | ⟨c, c2, e⟩ | ⟨c, c2, e⟩
        · omega
        · omega
        · omega
        · exfalso
          have := hdown c c2
          grind
      simp [hq'']

namespace F64

theorem ofRat_zero : ofRat 0 = zero false := by simp [ofRat]

theorem ofRat_of_ne {q : Rat} (h : q ≠ 0) :
    ofRat q = ofBits (binary64.encode (decide (q < 0)) (roundPos binary64 q.num.natAbs q.den)) := by
  simp [ofRat, h]

/-- `ofRat` of a nonzero rational is an infinity or a rounded finite number. -/
theorem ofRat_cases {q : Rat} (h : q ≠ 0) :
    (overflowLimit ≤ (if q < 0 then -q else q) ∧ ofRat q = inf (decide (q < 0))) ∨
      ∃ (m : Nat) (e : Int), Decoded (ofRat q) (decide (q < 0)) m e ∧
        (m : Rat) * pw e = (roundedInt binary64 q.num.natAbs q.den : Rat) *
          pw (roundExp binary64 q.num.natAbs q.den) ∧
        (roundedInt binary64 q.num.natAbs q.den % 2 = 0 → m % 2 = 0) := by
  obtain ⟨hn, hd, hv⟩ := natAbs_div_den h
  rw [ofRat_of_ne h]
  cases hr : roundPos binary64 q.num.natAbs q.den with
  | none =>
    left
    have := (roundPos_none_iff hn hd).1 hr
    rw [hv] at this
    exact ⟨this, encode_none _⟩
  | some r =>
    right
    obtain ⟨m, e⟩ := r
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := roundPos_some binary64 (by decide) hn hd hr
    have h1' : m < 2 ^ 53 := h1
    have h2' : -1074 ≤ e := h2
    have h3' : 2 ^ 52 ≤ m ∨ e = -1074 := h3
    have h4' : e ≤ 971 := by
      have : e + 52 ≤ 1023 := by simpa [binary64] using h4
      omega
    exact ⟨m, e, encode_decode _ h1' h2' h3' h4', h5, h6⟩

theorem abs_neg (a : Rat) : Rat.abs (-a) = Rat.abs a := by
  by_cases h : 0 ≤ a
  · rw [abs_of_nonneg h, abs_of_nonpos (by grind)]; simp [Rat.neg_neg]
  · have h' : a ≤ 0 := by grind
    rw [abs_of_nonpos h', abs_of_nonneg (by grind)]

theorem rep_neg {y : Rat} (h : Rep binary64 y) : Rep binary64 (-y) := by
  obtain ⟨M, E, hM, hE, hy⟩ := h
  refine ⟨M, E, hM, hE, ?_⟩
  rcases hy with rfl | rfl
  · right; rfl
  · left; simp [Rat.neg_neg]

theorem rep_zero : Rep binary64 0 :=
  ⟨0, 0, by decide, by decide, Or.inl (by simp)⟩

/-- `ofRat q`, when finite, is at least as close to `q` as every number of the format.
This is the heart of round-to-nearest. -/
theorem ofRat_nearest_rep (q : Rat) (h : (ofRat q).isFinite = true) {y : Rat}
    (hy : Rep binary64 y) : Rat.abs (q - (ofRat q).toRat) ≤ Rat.abs (q - y) := by
  by_cases hq : q = 0
  · subst hq
    rw [ofRat_zero]
    have : (zero false).toRat = 0 := by decide +kernel
    rw [this]
    simp only [Rat.sub_self]
    exact (by rw [abs_of_nonneg (by decide)]; exact abs_nonneg _)
  · obtain ⟨hn, hd, hv⟩ := natAbs_div_den hq
    rcases ofRat_cases hq with ⟨_, hinf⟩ | ⟨m, e, hdec, hval, _⟩
    · exfalso
      rw [hinf] at h
      cases hneg : decide (q < 0) <;> rw [hneg] at h <;> revert h <;> decide +kernel
    · rw [toRat_decoded hdec, hval]
      by_cases hneg : q < 0
      · simp only [hneg, decide_true, ↓reduceIte] at hv ⊢
        have hnear := rounded_nearest binary64 (by decide) hn hd (rep_neg hy)
        rw [hv] at hnear
        have e1 : -q - (roundedInt binary64 q.num.natAbs q.den : Rat) * pw (roundExp binary64 q.num.natAbs q.den)
            = -(q - -((roundedInt binary64 q.num.natAbs q.den : Rat) * pw (roundExp binary64 q.num.natAbs q.den))) := by
          grind
        have e2 : -q - -y = -(q - y) := by grind
        unfold roundedInt at e1 ⊢
        rw [e1, e2, abs_neg, abs_neg] at hnear
        exact hnear
      · simp only [hneg, decide_false, Bool.false_eq_true, ↓reduceIte] at hv ⊢
        have hnear := rounded_nearest binary64 (by decide) hn hd hy
        rw [hv] at hnear
        exact hnear

theorem abs_le_zero {a : Rat} (h : Rat.abs a ≤ 0) : a = 0 := by
  have h0 := abs_nonneg a
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha] at h; grind
  · rw [abs_of_nonpos (by grind)] at h; grind

theorem abs_eq_ite (q : Rat) : Rat.abs q = if q < 0 then -q else q := by
  by_cases h : q < 0
  · simp only [h, ↓reduceIte]; exact abs_of_nonpos (Rat.le_of_lt h)
  · simp only [h, ↓reduceIte]; exact abs_of_nonneg (Rat.not_lt.1 h)

theorem inf_isInf (neg : Bool) : (inf neg).isInf = true := by cases neg <;> decide +kernel

theorem inf_isNaN (neg : Bool) : (inf neg).isNaN = false := by cases neg <;> decide +kernel

theorem inf_isFinite (neg : Bool) : (inf neg).isFinite = false := by cases neg <;> decide +kernel

theorem zero_isFinite (neg : Bool) : (zero neg).isFinite = true := by cases neg <;> decide +kernel

theorem zero_isZero (neg : Bool) : (zero neg).isZero = true := by cases neg <;> decide +kernel

theorem zero_sign (neg : Bool) : (zero neg).sign = neg := by cases neg <;> decide +kernel

theorem zero_toRat (neg : Bool) : (zero neg).toRat = 0 := by cases neg <;> decide +kernel

theorem overflowLimit_pos : 0 < overflowLimit :=
  Rat.mul_pos (natCast_pos' (by decide)) (pw_pos 970)

/-- `ofRat` never makes a NaN, and it makes an infinity exactly past the limit. -/
theorem ofRat_class (q : Rat) :
    (ofRat q).isNaN = false ∧ ((ofRat q).isInf = true ↔ overflowLimit ≤ Rat.abs q) := by
  by_cases hq : q = 0
  · subst hq
    rw [ofRat_zero]
    have h1 := zero_isFinite false
    refine ⟨isNaN_false_of_finite h1, ?_⟩
    rw [isInf_false_of_finite h1]
    have h2 : Rat.abs 0 = 0 := abs_of_nonneg (by decide)
    rw [h2]
    constructor
    · intro h; cases h
    · intro h; exact absurd h (Rat.not_le.2 overflowLimit_pos)
  · rw [abs_eq_ite]
    rcases ofRat_cases hq with ⟨hge, hinf⟩ | ⟨m, e, hdec, hval, _⟩
    · rw [hinf]
      exact ⟨inf_isNaN _, ⟨fun _ => hge, fun _ => inf_isInf _⟩⟩
    · refine ⟨isNaN_false_of_finite hdec.finite, ?_⟩
      rw [isInf_false_of_finite hdec.finite]
      constructor
      · intro h; cases h
      · intro hge
        exfalso
        obtain ⟨hn, hd, hv⟩ := natAbs_div_den hq
        rw [← hv] at hge
        have hnone := (roundPos_none_iff hn hd).2 hge
        rw [ofRat_of_ne hq, hnone, encode_none] at hdec
        have := hdec.finite
        rw [inf_isFinite] at this
        cases this

theorem ofRat_isNaN (q : Rat) : (ofRat q).isNaN = false := (ofRat_class q).1

theorem ofRat_isInf (q : Rat) : (ofRat q).isInf = true ↔ overflowLimit ≤ Rat.abs q :=
  (ofRat_class q).2

theorem ofRat_isFinite (q : Rat) : (ofRat q).isFinite = true ↔ Rat.abs q < overflowLimit := by
  have h1 := ofRat_isInf q
  have h2 := ofRat_isNaN q
  constructor
  · intro hf
    apply Rat.not_le.1
    intro hge
    have := h1.2 hge
    rw [isInf_false_of_finite hf] at this
    cases this
  · intro hlt
    rcases classify (ofRat q) with h | h | h
    · exact h
    · exact absurd (h1.1 h) (Rat.not_le.2 hlt)
    · rw [h2] at h; cases h

/-- Round to nearest: `ofRat q` is as close to `q` as any finite `F64`. -/
theorem ofRat_nearest (q : Rat) (h : (ofRat q).isFinite = true) {y : F64}
    (hy : y.isFinite = true) : Rat.abs (q - (ofRat q).toRat) ≤ Rat.abs (q - y.toRat) :=
  ofRat_nearest_rep q h (toRat_rep hy)

/-- An exactly representable rational survives `ofRat`. -/
theorem ofRat_exact {q : Rat} (hrep : Rep binary64 q) (hlt : Rat.abs q < overflowLimit) :
    (ofRat q).toRat = q := by
  have := ofRat_nearest_rep q ((ofRat_isFinite q).2 hlt) hrep
  simp only [Rat.sub_self] at this
  rw [abs_of_nonneg (a := 0) (by decide)] at this
  have h0 := abs_le_zero this
  grind

/-- Ties to even: on a tie with a different finite value, the mantissa of `ofRat q` is
even. -/
theorem ofRat_tie (q : Rat) (h : (ofRat q).isFinite = true) {y : F64} (hy : y.isFinite = true)
    (heq : Rat.abs (q - (ofRat q).toRat) = Rat.abs (q - y.toRat))
    (hne : y.toRat ≠ (ofRat q).toRat) : (ofRat q).mant % 2 = 0 := by
  by_cases hq : q = 0
  · subst hq
    exfalso
    rw [ofRat_zero, zero_toRat] at heq hne
    simp only [Rat.sub_self] at heq
    rw [abs_of_nonneg (a := 0) (by decide)] at heq
    have := abs_le_zero (a := 0 - y.toRat) (by rw [← heq]; exact Rat.le_refl)
    grind
  · obtain ⟨hn, hd, hv⟩ := natAbs_div_den hq
    rcases ofRat_cases hq with ⟨_, hinf⟩ | ⟨m, e, hdec, hval, hpar⟩
    · exfalso
      rw [hinf, inf_isFinite] at h
      cases h
    · rw [hdec.mant]
      apply hpar
      rw [toRat_decoded hdec, hval] at heq hne
      have hrep := toRat_rep hy
      by_cases hneg : q < 0
      · simp only [hneg, decide_true, ↓reduceIte] at hv heq hne
        apply rounded_tie binary64 (by decide) hn hd (rep_neg hrep)
        · rw [hv]
          have e1 : -q - (roundedInt binary64 q.num.natAbs q.den : Rat) * pw (roundExp binary64 q.num.natAbs q.den)
              = -(q - -((roundedInt binary64 q.num.natAbs q.den : Rat) * pw (roundExp binary64 q.num.natAbs q.den))) := by
            grind
          have e2 : -q - -y.toRat = -(q - y.toRat) := by grind
          unfold roundedInt at e1 heq
          rw [e1, e2, abs_neg, abs_neg]; exact heq
        · intro hc
          apply hne
          unfold roundedInt
          rw [← Rat.neg_neg y.toRat, hc]
      · simp only [hneg, decide_false, Bool.false_eq_true, ↓reduceIte] at hv heq hne
        apply rounded_tie binary64 (by decide) hn hd hrep
        · rw [hv]; exact heq
        · exact hne

/-! ## Sign bit operations -/

theorem neg_fields (x : F64) :
    x.neg.sign = !x.sign ∧ x.neg.bexp = x.bexp ∧ x.neg.frac = x.frac := by
  have hb := x.isLt
  have hbits : x.neg.bits = if 2 ^ 63 ≤ x.bits then x.bits - 2 ^ 63 else x.bits + 2 ^ 63 := by
    unfold neg
    apply bits_ofBits_of_lt
    split <;> omega
  unfold sign bexp frac
  rw [hbits]
  by_cases h : 2 ^ 63 ≤ x.bits
  · simp only [h, ↓reduceIte, decide_true, Bool.not_true]
    refine ⟨by simp <;> omega, by omega, by omega⟩
  · simp only [h, ↓reduceIte, decide_false, Bool.not_false]
    refine ⟨by simp <;> omega, by omega, by omega⟩

theorem neg_neg (x : F64) : x.neg.neg = x := by
  obtain ⟨h1, h2, h3⟩ := neg_fields x
  obtain ⟨h4, h5, h6⟩ := neg_fields x.neg
  apply eq_of_fields
  · rw [h4, h1]; simp
  · rw [h5, h2]
  · rw [h6, h3]

theorem neg_isFinite (x : F64) : x.neg.isFinite = x.isFinite := by
  obtain ⟨_, h2, _⟩ := neg_fields x
  unfold isFinite; rw [h2]

theorem neg_isNaN (x : F64) : x.neg.isNaN = x.isNaN := by
  obtain ⟨_, h2, h3⟩ := neg_fields x
  unfold isNaN; rw [h2, h3]

theorem neg_isInf (x : F64) : x.neg.isInf = x.isInf := by
  obtain ⟨_, h2, h3⟩ := neg_fields x
  unfold isInf; rw [h2, h3]

theorem neg_isZero (x : F64) : x.neg.isZero = x.isZero := by
  obtain ⟨_, h2, h3⟩ := neg_fields x
  unfold isZero; rw [h2, h3]

theorem toRat_neg (x : F64) : x.neg.toRat = -x.toRat := by
  obtain ⟨h1, h2, h3⟩ := neg_fields x
  cases hf : x.isFinite
  · rw [toRat_of_not_finite hf, toRat_of_not_finite (by rw [neg_isFinite]; exact hf)]; rfl
  · have hf' : x.neg.isFinite = true := by rw [neg_isFinite]; exact hf
    rw [toRat_of_finite hf, toRat_of_finite hf', h1]
    have hm : x.neg.mant = x.mant := by unfold mant; rw [h2, h3]
    have hl : x.neg.lsbExp = x.lsbExp := by unfold lsbExp; rw [h2]
    rw [hm, hl]
    cases x.sign <;> simp [Rat.neg_neg]

/-! ## Exact value and injectivity -/

theorem mant_pos_of_not_zero {x : F64} (h : x.isZero = false) : 0 < x.mant := by
  unfold mant
  have h' : ¬ (x.bexp = 0 ∧ x.frac = 0) := by
    intro hc; rw [(isZero_eq x).2 hc] at h; cases h
  split <;> omega

theorem mant_eq_zero_of_zero {x : F64} (h : x.isZero = true) : x.mant = 0 := by
  rw [isZero_eq] at h
  unfold mant; simp [h.1, h.2]

theorem toRat_of_isZero {x : F64} (h : x.isZero = true) : x.toRat = 0 := by
  rw [toRat_of_finite (isFinite_of_isZero h), mant_eq_zero_of_zero h]
  simp

/-- `m * 2 ^ e` determines a canonical `(m, e)`: the half where `e₁ < e₂` is impossible. -/
theorem canon_no_lt {m1 m2 : Nat} {e1 e2 : Int} (h1 : m1 < 2 ^ 53) (h2 : 2 ^ 52 ≤ m2)
    (heq : (m1 : Rat) * pw e1 = (m2 : Rat) * pw e2) : ¬ e1 < e2 := by
  intro hlt
  have hk : pw e2 = ((2 ^ (e2 - e1).toNat : Nat) : Rat) * pw e1 := by
    rw [← pw_natCast, ← pw_add]; congr 1; omega
  rw [hk] at heq
  have hne := pw_ne e1
  have h3 : (m1 : Rat) = (m2 : Rat) * ((2 ^ (e2 - e1).toNat : Nat) : Rat) := by
    have h5 : (m1 : Rat) * pw e1 * (pw e1)⁻¹ = (m2 : Rat) * (((2 ^ (e2 - e1).toNat : Nat) : Rat) * pw e1) * (pw e1)⁻¹ := by
      rw [heq]
    rw [Rat.mul_assoc, Rat.mul_assoc, Rat.mul_assoc, pw_mul_inv, Rat.mul_one, Rat.mul_one] at h5
    exact h5
  have h4 : m1 = m2 * 2 ^ (e2 - e1).toNat := by exact_mod_cast h3
  have h5 : 2 ≤ 2 ^ (e2 - e1).toNat := by
    have : 1 ≤ (e2 - e1).toNat := by omega
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (e2 - e1).toNat := Nat.pow_le_pow_right (by omega) this
  have : m2 * 2 ≤ m2 * 2 ^ (e2 - e1).toNat := Nat.mul_le_mul_left _ h5
  omega

/-- Exact value determines a nonzero datum. -/
theorem toRat_inj {x y : F64} (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hz : x.isZero = false) (h : x.toRat = y.toRat) : x = y := by
  have hm := mant_pos_of_not_zero hz
  have hxv : 0 < (x.mant : Rat) * pw x.lsbExp := Rat.mul_pos (natCast_pos' hm) (pw_pos _)
  have hyv : 0 ≤ (y.mant : Rat) * pw y.lsbExp :=
    Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (pw_pos _))
  rw [toRat_of_finite hx, toRat_of_finite hy] at h
  have hsign : x.sign = y.sign := by
    cases hs1 : x.sign <;> cases hs2 : y.sign <;> simp [hs1, hs2] at h ⊢ <;> grind
  have hval : (x.mant : Rat) * pw x.lsbExp = (y.mant : Rat) * pw y.lsbExp := by
    rw [hsign] at h
    cases hs : y.sign <;> simp [hs] at h <;> grind
  have he : x.lsbExp = y.lsbExp := by
    have c1 := mant_canon x
    have c2 := mant_canon y
    have l1 := lsbExp_ge x
    have l2 := lsbExp_ge y
    have m1 := mant_lt x
    have m2 := mant_lt y
    by_cases hlt : x.lsbExp < y.lsbExp
    · exact absurd hlt (canon_no_lt m1 (by omega) hval)
    · by_cases hgt : y.lsbExp < x.lsbExp
      · exact absurd hgt (canon_no_lt m2 (by omega) hval.symm)
      · omega
  have hmm : x.mant = y.mant := by
    rw [he] at hval
    have hne := pw_ne y.lsbExp
    have h5 : (x.mant : Rat) * pw y.lsbExp * (pw y.lsbExp)⁻¹ = (y.mant : Rat) * pw y.lsbExp * (pw y.lsbExp)⁻¹ := by
      rw [hval]
    rw [Rat.mul_assoc, Rat.mul_assoc, pw_mul_inv, Rat.mul_one, Rat.mul_one] at h5
    exact Rat.natCast_inj.1 h5
  have fx := frac_lt x
  have fy := frac_lt y
  unfold mant at hmm
  unfold lsbExp at he
  apply eq_of_fields hsign
  · split at hmm <;> split at hmm <;> omega
  · split at hmm <;> split at hmm <;> omega

theorem abs_toRat_lt {x : F64} (hx : x.isFinite = true) : Rat.abs x.toRat < overflowLimit := by
  have h1 : x.mant ≤ 9007199254740991 := by have := mant_lt x; omega
  have h2 : (x.mant : Rat) ≤ 9007199254740991 := by exact_mod_cast Rat.natCast_le_natCast.2 h1
  have h3 : pw x.lsbExp ≤ pw 971 := pw_le (lsbExp_le x hx)
  have h4 : (x.mant : Rat) * pw x.lsbExp ≤ 9007199254740991 * pw 971 := by
    have a1 := Rat.mul_le_mul_of_nonneg_right h2 (Rat.le_of_lt (pw_pos x.lsbExp))
    have a2 := Rat.mul_le_mul_of_nonneg_left h3 (by decide : (0 : Rat) ≤ 9007199254740991)
    exact Rat.le_trans a1 a2
  have h0 : 0 ≤ (x.mant : Rat) * pw x.lsbExp :=
    Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (pw_pos _))
  have hL := pw_pos 970
  have h971 : pw 971 = 2 * pw 970 := pw_succ 970
  have hlim : overflowLimit = 18014398509481983 * pw 970 := by
    unfold overflowLimit; congr 1
  rw [hlim, toRat_of_finite hx]
  rw [h971] at h4
  split
  · rw [abs_of_nonpos (by grind)]; grind
  · rw [abs_of_nonneg h0]; grind

/-- Rounding the exact value of a nonzero finite datum gives it back. -/
theorem ofRat_toRat {x : F64} (hx : x.isFinite = true) (hz : x.isZero = false) :
    ofRat x.toRat = x := by
  have hlt := abs_toRat_lt hx
  have hf := (ofRat_isFinite x.toRat).2 hlt
  have he := ofRat_exact (toRat_rep hx) hlt
  have hzr : (ofRat x.toRat).isZero = false := by
    cases hc : (ofRat x.toRat).isZero
    · rfl
    · exfalso
      rw [toRat_of_isZero hc] at he
      have hm := mant_pos_of_not_zero hz
      have hxv : 0 < (x.mant : Rat) * pw x.lsbExp := Rat.mul_pos (natCast_pos' hm) (pw_pos _)
      rw [toRat_of_finite hx] at he
      split at he <;> grind
  exact toRat_inj hf hx hzr he

end F64

end PyLean.Binary64
