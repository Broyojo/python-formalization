import PyLean.MathInt.FltPow

/-!
# Property: `prod`

`math_prod_impl` (Modules/mathmodule.c:2697-2832) keeps running products in a C `long` and a
C `double` while the items allow it, guarding the `long` product with
`_check_long_mult_overflow` (:2630-2678), which compares the wrapped `long` product with the
`double` product. The property: for every iterable and start, the fast paths give exactly what
the generic loop `PyNumber_Multiply(result, item)` gives, i.e. `functools.reduce(operator.mul,
iterable, start)` (Doc/library/math.rst, "prod"). Its core is that the overflow check never
misses an overflow.
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64 PyLean.Binary64.F64

/-! ## Relative rounding error -/

/-- `ofRat` is within a relative `2 ** -52` of a positive rational in the normal range. -/
theorem rnd_rel {q : Rat} (hq : pw (-1022) ≤ q) (hf : (ofRat q).isFinite = true) :
    Rat.abs (q - rnd q) ≤ q * pw (-52) := by
  have hq0 : 0 < q := by have := pw_pos (-1022); grind
  have hne : q ≠ 0 := by grind
  obtain ⟨hn, hd, hv⟩ := natAbs_div_den hne
  have hqv : q = (q.num.natAbs : Rat) / (q.den : Rat) := by
    have : ¬ q < 0 := by grind
    simp only [this, ↓reduceIte] at hv; exact hv.symm
  obtain ⟨s1, s2⟩ := floorLog2Q_spec hn hd
  rw [← hqv] at s1 s2
  generalize floorLog2Q q.num.natAbs q.den = e at s1 s2
  have he : -1022 ≤ e := by
    apply Classical.byContradiction; intro h
    have : pw (e + 1) ≤ pw (-1022) := pw_le (by omega)
    grind
  have hu : 0 < pw (e - 52) := pw_pos _
  have hsplit : pw (e + 1) = ((2 ^ 53 : Nat) : Rat) * pw (e - 52) := by
    rw [← pw_natCast, ← pw_add]; congr 1; omega
  have hpe : pw e = ((2 ^ 52 : Nat) : Rat) * pw (e - 52) := by
    rw [← pw_natCast, ← pw_add]; congr 1; omega
  generalize hk : Rat.floor (q / pw (e - 52)) = k
  have hk1 := Rat.floor_le (q / pw (e - 52))
  have hk2 := Rat.lt_floor_add_one (q / pw (e - 52))
  rw [hk] at hk1 hk2
  have hdiv : q / pw (e - 52) * pw (e - 52) = q := Rat.div_mul_cancel (by grind)
  have hpos : 0 < q / pw (e - 52) := by
    apply Classical.byContradiction; intro h
    have h' : q / pw (e - 52) ≤ 0 := by grind
    have := Rat.mul_le_mul_of_nonneg_right h' (Rat.le_of_lt hu)
    rw [hdiv] at this; grind
  have hk0 : 0 ≤ k := by
    rw [Rat.intCast_add] at hk2
    have h1 : ((1 : Int) : Rat) = 1 := rfl
    rw [h1] at hk2
    have : ((-1 : Int) : Rat) < (k : Rat) := by
      rw [show ((-1 : Int) : Rat) = -1 from rfl]; grind
    have := Rat.intCast_lt_intCast.1 this
    omega
  have hqu1 : (k : Rat) * pw (e - 52) ≤ q := by
    have := Rat.mul_le_mul_of_nonneg_right hk1 (Rat.le_of_lt hu)
    rwa [hdiv] at this
  have hqu2 : q < ((k + 1 : Int) : Rat) * pw (e - 52) := by
    have := (Rat.mul_lt_mul_right hu).2 hk2
    rwa [hdiv] at this
  have hkM : k < 9007199254740992 := by
    have : (k : Rat) * pw (e - 52) < ((2 ^ 53 : Nat) : Rat) * pw (e - 52) := by
      rw [← hsplit]; grind
    have h2 := (Rat.mul_lt_mul_right hu).1 this
    have h3 : ((k : Int) : Rat) < ((9007199254740992 : Int) : Rat) := by
      rw [show ((9007199254740992 : Int) : Rat) = ((2 ^ 53 : Nat) : Rat) from rfl]; exact h2
    exact Rat.intCast_lt_intCast.1 h3
  have hrep : Rep binary64 ((k.toNat : Nat) * pw (e - 52)) := by
    refine ⟨k.toNat, e - 52, by show k.toNat < 2 ^ 53; omega, by simp [Fmt.etiny, binary64]; omega,
      Or.inl rfl⟩
  have hkn : ((k.toNat : Nat) : Rat) = (k : Rat) := by
    have : ((k.toNat : Int)) = k := by omega
    exact_mod_cast this
  have hnear := ofRat_nearest_rep q hf hrep
  rw [hkn] at hnear
  have hgap : Rat.abs (q - (k : Rat) * pw (e - 52)) ≤ q * pw (-52) := by
    rw [abs_of_nonneg (by grind)]
    have h1 : q - (k : Rat) * pw (e - 52) < pw (e - 52) := by
      rw [Rat.intCast_add] at hqu2
      have : ((1 : Int) : Rat) = 1 := rfl
      rw [this] at hqu2; grind
    have h2 : pw (e - 52) ≤ q * pw (-52) := by
      have : pw (e - 52) = pw e * pw (-52) := by rw [← pw_add]; congr 1
      rw [this]
      exact Rat.mul_le_mul_of_nonneg_right s1 (Rat.le_of_lt (pw_pos _))
    grind
  exact Rat.le_trans hnear hgap

/-- `rnd_rel` for either sign. -/
theorem rnd_rel_abs {q : Rat} (hq : pw (-1022) ≤ Rat.abs q) (hf : (ofRat q).isFinite = true) :
    Rat.abs (q - rnd q) ≤ Rat.abs q * pw (-52) := by
  rcases abs_cases (a := q) with ⟨h0, ha⟩ | ⟨h0, ha⟩
  · rw [ha] at hq ⊢; exact rnd_rel hq hf
  · rw [ha] at hq ⊢
    have hf' : (ofRat (-q)).isFinite = true := by
      rw [ofRat_neg (by grind), neg_isFinite]; exact hf
    have := rnd_rel hq hf'
    rw [rnd_neg] at this
    rw [show q - rnd q = -(-q - -rnd q) by grind, abs_neg]; exact this

theorem eps_val : pw (-52) = 1 / 4503599627370496 := by
  rw [pw_neg, show pw 52 = ((2 ^ 52 : Nat) : Rat) from pw_natCast 52]; decide +kernel

/-- The magnitude bounds that one rounding gives, in the form the products below use. -/
theorem rnd_bounds {q : Rat} (hq : pw (-1022) ≤ Rat.abs q) (hf : (ofRat q).isFinite = true) :
    Rat.abs q - Rat.abs q * pw (-52) ≤ Rat.abs (rnd q) ∧ Rat.abs (rnd q) ≤ Rat.abs q + Rat.abs q * pw (-52) ∧
    (0 < q → 0 < rnd q) ∧ (q < 0 → rnd q < 0) := by
  have h := rnd_rel_abs hq hf
  have he : pw (-52) = 1 / 4503599627370496 := eps_val
  rw [he] at h ⊢
  have hq0 : 0 < Rat.abs q := by have := pw_pos (-1022); grind
  rcases abs_cases (a := q) with ⟨h0, ha⟩ | ⟨h0, ha⟩ <;>
  rcases abs_cases (a := rnd q) with ⟨h1, hb⟩ | ⟨h1, hb⟩ <;>
  rcases abs_cases (a := q - rnd q) with ⟨h2, hc⟩ | ⟨h2, hc⟩ <;>
  rw [ha] at h hq0 ⊢ <;> rw [hc] at h <;> rw [hb] <;>
  refine ⟨?_, ?_, fun hp => ?_, fun hn => ?_⟩ <;> grind

/-! ## Wrapped products -/

theorem wrapLong_lit (P : Int) : wrapLong P =
    (if P % 18446744073709551616 < 9223372036854775808 then P % 18446744073709551616
     else P % 18446744073709551616 - 18446744073709551616) := rfl

theorem wrap_range (P : Int) : -(2 ^ 63) ≤ wrapLong P ∧ wrapLong P < 2 ^ 63 := by
  rw [wrapLong_lit]; split <;> omega

theorem wrap_eq_of_range {P : Int} (h1 : -(2 ^ 63) ≤ P) (h2 : P < 2 ^ 63) : wrapLong P = P := by
  rw [wrapLong_lit]; split <;> omega

theorem wrap_diff (P : Int) : ∃ k : Int, P = wrapLong P + k * 2 ^ 64 := by
  rw [wrapLong_lit]
  split
  · exact ⟨P / 18446744073709551616, by omega⟩
  · exact ⟨P / 18446744073709551616 + 1, by omega⟩

/-! ## The overflow check -/

/-- `ofInt` of an int of magnitude at most `2 ** 63`: finite, of the same weak sign, at most
`2 ** 63` in magnitude. -/
theorem ofInt_small_long {z : Int} (h1 : -(2 ^ 63) ≤ z) (h2 : z ≤ 2 ^ 63) :
    (F64.ofInt z).isFinite = true ∧ Rat.abs (F64.ofInt z).toRat ≤ pw 63 ∧
    (0 ≤ z → 0 ≤ (F64.ofInt z).toRat) ∧ (z ≤ 0 → (F64.ofInt z).toRat ≤ 0) := by
  have hP : pw 63 = ((2 ^ 63 : Nat) : Rat) := pw_natCast 63
  have hlim : pw 63 < overflowLimit := by decide +kernel
  have hzq : Rat.abs (z : Rat) ≤ pw 63 := by
    rw [hP, abs_intCast]
    have : z.natAbs ≤ 2 ^ 63 := by omega
    exact Rat.natCast_le_natCast.2 this
  have hf : (F64.ofInt z).isFinite = true := (ofRat_isFinite _).2 (by grind)
  have h63 : ofRat (pw 63) = ofRat (pw 63) := rfl
  have hr63 : (ofRat (pw 63)).toRat = pw 63 := by
    apply ofRat_exact _ (by rw [abs_of_nonneg (Rat.le_of_lt (pw_pos _))]; exact hlim)
    exact ⟨1, 63, by decide, by decide, Or.inl (by simp)⟩
  have hf63 : (ofRat (pw 63)).isFinite = true := (ofRat_isFinite _).2
    (by rw [abs_of_nonneg (Rat.le_of_lt (pw_pos _))]; exact hlim)
  have hfn63 : (ofRat (-pw 63)).isFinite = true := by
    rw [ofRat_neg (Rat.ne_of_gt (pw_pos _)), neg_isFinite]; exact hf63
  have hrn63 : (ofRat (-pw 63)).toRat = -pw 63 := by
    rw [ofRat_neg (Rat.ne_of_gt (pw_pos _)), toRat_neg, hr63]
  refine ⟨hf, ?_, fun hz => ?_, fun hz => ?_⟩
  · have hz1 : (z : Rat) ≤ pw 63 ∧ -pw 63 ≤ (z : Rat) := by
      rw [abs_eq_ite] at hzq; split at hzq <;> constructor <;> grind
    have u := ofRat_mono hz1.1 hf hf63
    have l := ofRat_mono hz1.2 hfn63 hf
    rw [hr63] at u; rw [hrn63] at l
    show Rat.abs (ofRat (z : Rat)).toRat ≤ pw 63
    rw [abs_eq_ite]; split <;> grind
  · have := ofRat_mono (show (0 : Rat) ≤ (z : Rat) by exact_mod_cast hz) ofRat_zero_finite hf
    rwa [ofRat_zero, zero_toRat] at this
  · have := ofRat_mono (show (z : Rat) ≤ 0 by exact_mod_cast hz) hf ofRat_zero_finite
    rwa [ofRat_zero, zero_toRat] at this

theorem absval_toRat {v : F64} (hv : v.isFinite = true) :
    (if F64.ge v c0 then v else F64.neg v).toRat = Rat.abs v.toRat := by
  unfold F64.ge
  rw [le_val c0_facts.1 hv, c0_facts.2.2.1]
  by_cases h : 0 ≤ v.toRat
  · simp [h, abs_of_nonneg h]
  · simp [h, toRat_neg, abs_of_nonpos (by grind : v.toRat ≤ 0)]

theorem absval_finite {v : F64} (hv : v.isFinite = true) :
    (if F64.ge v c0 then v else F64.neg v).isFinite = true := by
  split
  · exact hv
  · rw [neg_isFinite]; exact hv

/-- Once the double product and the wrapped long product are a quarter of the product apart,
`_check_long_mult_overflow` reports an overflow. -/
theorem far_reports {L D : F64} (hL : L.isFinite = true) (hD : D.isFinite = true)
    (hD1 : 1 ≤ Rat.abs D.toRat) (hDb : Rat.abs D.toRat ≤ pw 200) (hLb : Rat.abs L.toRat ≤ pw 200)
    (hfar : Rat.abs D.toRat ≤ 4 * Rat.abs (L.toRat - D.toRat)) :
    (if F64.eq L D then false
     else
       let diff := F64.sub L D
       let absdiff := if F64.ge diff c0 then diff else F64.neg diff
       let absprod := if F64.ge D c0 then D else F64.neg D
       if F64.le (F64.mul (F64.ofInt 32) absdiff) absprod then false else true) = true := by
  have he : pw (-52) = 1 / 4503599627370496 := eps_val
  have hsm : pw (-1022) ≤ 1 / 4 := by
    rw [pw_neg, show pw 1022 = ((2 ^ 1022 : Nat) : Rat) from pw_natCast 1022]; decide +kernel
  have hlim : pw 202 < overflowLimit := by decide +kernel
  have hneq : F64.eq L D = false := by
    rw [eq_of_finite hL hD]
    apply decide_eq_false
    intro h
    have h0 : L.toRat - D.toRat = 0 := by grind
    rw [h0, abs_of_nonneg (Rat.le_refl)] at hfar
    grind
  simp only [hneq, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨dv, df, _⟩ := sub_facts hL hD
  have hdq : pw (-1022) ≤ Rat.abs (L.toRat - D.toRat) := by grind
  have hdlim : Rat.abs (L.toRat - D.toRat) < overflowLimit := by
    have : Rat.abs (L.toRat - D.toRat) ≤ Rat.abs L.toRat + Rat.abs D.toRat := by
      rw [abs_eq_ite (L.toRat - D.toRat), abs_eq_ite L.toRat, abs_eq_ite D.toRat]
      split <;> split <;> split <;> grind
    have : pw 200 + pw 200 ≤ pw 202 := by
      rw [show (202 : Int) = 200 + 2 by rfl, pw_add, show pw 2 = 4 by decide +kernel]
      have := pw_pos 200; grind
    grind
  have hdf : (ofRat (L.toRat - D.toRat)).isFinite = true := (ofRat_isFinite _).2 hdlim
  have hdiffin : (F64.sub L D).isFinite = true := by rw [df]; exact hdf
  obtain ⟨b1, b2, _, _⟩ := rnd_bounds hdq hdf
  rw [he] at b1 b2
  have hA := absval_toRat hdiffin
  have hAf := absval_finite hdiffin
  rw [dv] at hA
  generalize (if F64.ge (F64.sub L D) c0 then F64.sub L D else F64.neg (F64.sub L D)) = A at hA hAf
  have hP := absval_toRat hD
  have hPf := absval_finite hD
  generalize (if F64.ge D c0 then D else F64.neg D) = Pr at hP hPf
  have h32 : (F64.ofInt 32).isFinite = true ∧ (F64.ofInt 32).toRat = 32 := by decide +kernel
  obtain ⟨mv, mf, _⟩ := mul_facts h32.1 hAf
  rw [h32.2, hA] at mv mf
  -- 32 * |rnd (L - D)| rounds above |D|
  have hX : pw (-1022) ≤ Rat.abs (32 * Rat.abs (rnd (L.toRat - D.toRat))) := by
    rw [abs_of_nonneg (by have := abs_nonneg (rnd (L.toRat - D.toRat)); grind)]; grind
  have hXlim : (ofRat (32 * Rat.abs (rnd (L.toRat - D.toRat)))).isFinite = true := by
    apply (ofRat_isFinite _).2
    rw [abs_of_nonneg (by have := abs_nonneg (rnd (L.toRat - D.toRat)); grind)]
    have : pw 200 + pw 200 ≤ pw 202 := by
      rw [show (202 : Int) = 200 + 2 by rfl, pw_add, show pw 2 = 4 by decide +kernel]
      have := pw_pos 200; grind
    have : 32 * pw 202 < overflowLimit := by decide +kernel
    have : Rat.abs (L.toRat - D.toRat) ≤ Rat.abs L.toRat + Rat.abs D.toRat := by
      rw [abs_eq_ite (L.toRat - D.toRat), abs_eq_ite L.toRat, abs_eq_ite D.toRat]
      split <;> split <;> split <;> grind
    grind
  obtain ⟨c1', _, _, _⟩ := rnd_bounds hX hXlim
  rw [he] at c1'
  rw [abs_of_nonneg (by have := abs_nonneg (rnd (L.toRat - D.toRat)); grind)] at c1'
  have hfin : (F64.mul (F64.ofInt 32) A).isFinite = true := by rw [mf]; exact hXlim
  rw [le_val hfin hPf, mv, hP]
  have hpos : 0 ≤ rnd (32 * Rat.abs (rnd (L.toRat - D.toRat))) := rnd_nonneg (by
    have := abs_nonneg (rnd (L.toRat - D.toRat)); grind)
  simp only [decide_eq_true_eq]
  rw [if_neg]
  intro hle
  rw [abs_of_nonneg hpos] at c1'
  grind


theorem mul_le_mul' {a b c d : Rat} (h1 : a ≤ b) (h2 : c ≤ d) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    a * c ≤ b * d := by
  have hb : 0 ≤ b := Rat.le_trans ha h1
  exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_left h2 ha) (Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_trans hc h2))

theorem abs_mul' (a b : Rat) : Rat.abs (a * b) = Rat.abs a * Rat.abs b := by
  rcases abs_cases (a := a) with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
  rcases abs_cases (a := b) with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;> rw [e1, e2]
  · exact abs_of_nonneg (Rat.mul_nonneg h1 h2)
  · rw [abs_of_nonpos (by have := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt h2) h1; grind)]; grind
  · rw [abs_of_nonpos (by have := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt h1) h2; grind)]; grind
  · rw [abs_of_nonneg]
    · grind
    · have := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt h2) (show 0 ≤ -a by grind); grind

/-- The `double` product of two `long`s has the sign of the exact product and is within a few
per cent of it. -/
theorem dprod_bounds {a b : Int} (ha1 : -(2 ^ 63) ≤ a) (ha2 : a ≤ 2 ^ 63) (hb1 : -(2 ^ 63) ≤ b)
    (hb2 : b ≤ 2 ^ 63) (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    let D := F64.mul (F64.ofInt a) (F64.ofInt b)
    D.isFinite = true ∧ (3 / 4) * Rat.abs ((a * b : Int) : Rat) ≤ Rat.abs D.toRat ∧
    Rat.abs D.toRat ≤ 2 * Rat.abs ((a * b : Int) : Rat) ∧
    (0 < a * b → 0 < D.toRat) ∧ (a * b < 0 → D.toRat < 0) := by
  have he : pw (-52) = 1 / 4503599627370496 := eps_val
  have hsm : pw (-1022) ≤ 1 / 2 := by
    rw [pw_neg, show pw 1022 = ((2 ^ 1022 : Nat) : Rat) from pw_natCast 1022]; decide +kernel
  obtain ⟨fA, bA, _, _⟩ := ofInt_small_long ha1 ha2
  obtain ⟨fB, bB, _, _⟩ := ofInt_small_long hb1 hb2
  have ga : 1 ≤ Rat.abs (a : Rat) := by
    rw [abs_intCast]; have : 1 ≤ a.natAbs := by omega
    exact_mod_cast this
  have gb : 1 ≤ Rat.abs (b : Rat) := by
    rw [abs_intCast]; have : 1 ≤ b.natAbs := by omega
    exact_mod_cast this
  obtain ⟨a1, a2, a3, a4⟩ := rnd_bounds (q := (a : Rat)) (by grind) fA
  obtain ⟨b1, b2, b3, b4⟩ := rnd_bounds (q := (b : Rat)) (by grind) fB
  rw [he] at a1 a2 b1 b2
  -- the exact product of the two rounded factors
  have hA : (F64.ofInt a).toRat = rnd (a : Rat) := rfl
  have hB : (F64.ofInt b).toRat = rnd (b : Rat) := rfl
  obtain ⟨mv, mf, _⟩ := mul_facts fA fB
  rw [hA, hB] at mv mf
  generalize hx : rnd (a : Rat) = x at a1 a2 a3 a4 mv mf
  generalize hy : rnd (b : Rat) = y at b1 b2 b3 b4 mv mf
  generalize hα : Rat.abs (a : Rat) = α at a1 a2 ga
  generalize hβ : Rat.abs (b : Rat) = β at b1 b2 gb
  have hP : Rat.abs ((a * b : Int) : Rat) = α * β := by rw [Rat.intCast_mul, abs_mul', hα, hβ]
  have hxy : Rat.abs (x * y) = Rat.abs x * Rat.abs y := abs_mul' x y
  have lo : (99 / 100) * α * ((99 / 100) * β) ≤ Rat.abs (x * y) := by
    rw [hxy]; apply mul_le_mul' <;> grind
  have hi : Rat.abs (x * y) ≤ (101 / 100) * α * ((101 / 100) * β) := by
    rw [hxy]; apply mul_le_mul' <;> (try grind) <;> exact abs_nonneg _
  have hαβ : 1 ≤ α * β := by
    have := mul_le_mul' (show (1 : Rat) ≤ α from ga) (show (1 : Rat) ≤ β from gb) (by decide) (by decide)
    simpa using this
  have hαβ2 : α * β ≤ pw 126 := by
    have h1 : α ≤ pw 63 := by
      rw [← hα, abs_intCast, show pw 63 = ((2 ^ 63 : Nat) : Rat) from pw_natCast 63]
      exact_mod_cast (show a.natAbs ≤ 2 ^ 63 by omega)
    have h2 : β ≤ pw 63 := by
      rw [← hβ, abs_intCast, show pw 63 = ((2 ^ 63 : Nat) : Rat) from pw_natCast 63]
      exact_mod_cast (show b.natAbs ≤ 2 ^ 63 by omega)
    have := mul_le_mul' h1 h2 (by grind) (by grind)
    rwa [← pw_add] at this
  have elo : (99 / 100) * α * ((99 / 100) * β) = (9801 / 10000) * (α * β) := by grind
  have ehi : (101 / 100) * α * ((101 / 100) * β) = (10201 / 10000) * (α * β) := by grind
  rw [elo] at lo
  rw [ehi] at hi
  have hlimxy : Rat.abs (x * y) < overflowLimit := by
    have : 2 * pw 126 < overflowLimit := by decide +kernel
    grind
  have hfxy : (ofRat (x * y)).isFinite = true := (ofRat_isFinite _).2 hlimxy
  obtain ⟨d1, d2, d3, d4⟩ := rnd_bounds (q := x * y) (by grind) hfxy
  rw [he] at d1 d2
  simp only []
  refine ⟨by rw [mf]; exact hfxy, ?_, ?_, fun hp => ?_, fun hn => ?_⟩
  · rw [mv, hP]; grind
  · rw [mv, hP]; grind
  · rw [mv]; apply d3
    have : 0 < (a : Rat) * (b : Rat) := by exact_mod_cast hp
    rcases abs_cases (a := (a : Rat)) with ⟨h1, _⟩ | ⟨h1, _⟩
    · have hpa : 0 < (a : Rat) := by
        rcases Rat.le_iff_lt_or_eq.1 h1 with h | h
        · exact h
        · rw [← h] at this; simp at this
      have hpb : 0 < (b : Rat) := by
        apply Classical.byContradiction; intro hb
        have := Rat.mul_le_mul_of_nonneg_left (show (b : Rat) ≤ 0 by grind) (Rat.le_of_lt hpa)
        grind
      have := a3 hpa; have := b3 hpb; exact Rat.mul_pos (by grind) (by grind)
    · have hpb : (b : Rat) < 0 := by
        apply Classical.byContradiction; intro hb
        have := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt h1) (show 0 ≤ (b : Rat) by grind)
        grind
      have := a4 h1; have := b4 hpb
      have := Rat.mul_pos (show 0 < -x by grind) (show 0 < -y by grind); grind
  · rw [mv]; apply d4
    have : (a : Rat) * (b : Rat) < 0 := by exact_mod_cast hn
    rcases abs_cases (a := (a : Rat)) with ⟨h1, _⟩ | ⟨h1, _⟩
    · have hpa : 0 < (a : Rat) := by
        rcases Rat.le_iff_lt_or_eq.1 h1 with h | h
        · exact h
        · rw [← h] at this; simp at this
      have hpb : (b : Rat) < 0 := by
        apply Classical.byContradiction; intro hb
        have := Rat.mul_nonneg (Rat.le_of_lt hpa) (show 0 ≤ (b : Rat) by grind); grind
      have := a3 hpa; have := b4 hpb
      have := Rat.mul_pos (show 0 < x by grind) (show 0 < -y by grind); grind
    · have hpb : 0 < (b : Rat) := by
        apply Classical.byContradiction; intro hb
        have := Rat.mul_nonneg (show 0 ≤ -(a : Rat) by grind) (show 0 ≤ -(b : Rat) by grind); grind
      have := a4 h1; have := b3 hpb
      have := Rat.mul_pos (show 0 < -x by grind) (show 0 < y by grind); grind

/-- `_check_long_mult_overflow` never misses an overflow: when it returns `0`, the wrapped
`long` product is the exact product, for all `long` arguments. -/
theorem check_sound {a b : Int} (ha1 : LONG_MIN ≤ a) (ha2 : a ≤ LONG_MAX) (hb1 : LONG_MIN ≤ b)
    (hb2 : b ≤ LONG_MAX) (h : _check_long_mult_overflow a b = false) : wrapLong (a * b) = a * b := by
  unfold LONG_MIN LONG_MAX at *
  apply Classical.byContradiction
  intro hne
  have hout : a * b < -(2 ^ 63) ∨ 2 ^ 63 ≤ a * b := by
    apply Classical.byContradiction; intro hin
    exact hne (wrap_eq_of_range (by omega) (by omega))
  have ha0 : a ≠ 0 := by intro h0; subst h0; simp at hout
  have hb0 : b ≠ 0 := by intro h0; subst h0; simp at hout
  obtain ⟨fD, lD, uD, pD, nD⟩ := dprod_bounds (a := a) (b := b) (by omega) (by omega) (by omega)
    (by omega) ha0 hb0
  obtain ⟨wl, wu⟩ := wrap_range (a * b)
  obtain ⟨fL, bL, pL, nL⟩ := ofInt_small_long (z := wrapLong (a * b)) wl (by omega)
  obtain ⟨k, hk⟩ := wrap_diff (a * b)
  have h63 : pw 63 = 9223372036854775808 := by
    rw [show pw 63 = ((2 ^ 63 : Nat) : Rat) from pw_natCast 63]; rfl
  have habs : Rat.abs ((a * b : Int) : Rat) = ((a * b).natAbs : Rat) := abs_intCast _
  have hfar : Rat.abs (F64.mul (F64.ofInt a) (F64.ofInt b)).toRat ≤
      4 * Rat.abs ((F64.ofInt (wrapLong (a * b))).toRat - (F64.mul (F64.ofInt a) (F64.ofInt b)).toRat) := by
    generalize hD : (F64.mul (F64.ofInt a) (F64.ofInt b)).toRat = D at lD uD pD nD
    generalize hL : (F64.ofInt (wrapLong (a * b))).toRat = L at bL pL nL
    rw [h63] at bL
    rw [abs_eq_ite L] at bL
    rcases hout with hn | hp
    · have hD0 := nD (by omega)
      have hPm : (9223372036854775808 : Rat) ≤ Rat.abs ((a * b : Int) : Rat) := by
        rw [habs]; exact_mod_cast (show 9223372036854775808 ≤ (a * b).natAbs by omega)
      rw [abs_of_nonpos (Rat.le_of_lt hD0)] at lD uD ⊢
      by_cases hw : 0 ≤ wrapLong (a * b)
      · have := pL hw
        rw [abs_eq_ite]; split <;> grind
      · have hk1 : k ≤ -1 := by omega
        have hbig : (18446744073709551616 : Rat) ≤ Rat.abs ((a * b : Int) : Rat) := by
          rw [habs]; exact_mod_cast (show 18446744073709551616 ≤ (a * b).natAbs by omega)
        have := nL (by omega)
        rw [abs_eq_ite]; split at bL <;> split <;> grind
    · have hD0 := pD (by omega)
      have hPm : (9223372036854775808 : Rat) ≤ Rat.abs ((a * b : Int) : Rat) := by
        rw [habs]; exact_mod_cast (show 9223372036854775808 ≤ (a * b).natAbs by omega)
      rw [abs_of_nonneg (Rat.le_of_lt hD0)] at lD uD ⊢
      by_cases hw : wrapLong (a * b) ≤ 0
      · have := nL hw
        rw [abs_eq_ite]; split <;> grind
      · have hk1 : 1 ≤ k := by omega
        have hbig : (18446744073709551616 : Rat) ≤ Rat.abs ((a * b : Int) : Rat) := by
          rw [habs]; exact_mod_cast (show 18446744073709551616 ≤ (a * b).natAbs by omega)
        have := pL (by omega)
        rw [abs_eq_ite]; split at bL <;> split <;> grind
  have hD1 : 1 ≤ Rat.abs (F64.mul (F64.ofInt a) (F64.ofInt b)).toRat := by
    have hPm : (9223372036854775808 : Rat) ≤ Rat.abs ((a * b : Int) : Rat) := by
      rw [habs]
      exact_mod_cast (show 9223372036854775808 ≤ (a * b).natAbs by rcases hout with h | h <;> omega)
    grind
  have hDb : Rat.abs (F64.mul (F64.ofInt a) (F64.ofInt b)).toRat ≤ pw 200 := by
    have hPm : Rat.abs ((a * b : Int) : Rat) ≤ pw 126 := by
      rw [habs, show pw 126 = ((2 ^ 126 : Nat) : Rat) from pw_natCast 126]
      have : (a * b).natAbs ≤ 2 ^ 126 := by
        rw [Int.natAbs_mul]
        have h1 : a.natAbs ≤ 2 ^ 63 := by omega
        have h2 : b.natAbs ≤ 2 ^ 63 := by omega
        calc a.natAbs * b.natAbs ≤ 2 ^ 63 * 2 ^ 63 := Nat.mul_le_mul h1 h2
          _ = 2 ^ 126 := by rw [← Nat.pow_add]
      exact_mod_cast this
    have : 2 * pw 126 ≤ pw 200 := by decide +kernel
    grind
  have hLb : Rat.abs (F64.ofInt (wrapLong (a * b))).toRat ≤ pw 200 := by
    have : pw 63 ≤ pw 200 := pw_le (by omega)
    grind
  have := far_reports fL fD hD1 hDb hLb hfar
  have hdef : _check_long_mult_overflow a b =
      (if F64.eq (F64.ofInt (wrapLong (a * b))) (F64.mul (F64.ofInt a) (F64.ofInt b)) then false
       else
         let diff := F64.sub (F64.ofInt (wrapLong (a * b))) (F64.mul (F64.ofInt a) (F64.ofInt b))
         let absdiff := if F64.ge diff c0 then diff else F64.neg diff
         let absprod := if F64.ge (F64.mul (F64.ofInt a) (F64.ofInt b)) c0
           then F64.mul (F64.ofInt a) (F64.ofInt b) else F64.neg (F64.mul (F64.ofInt a) (F64.ofInt b))
         if F64.le (F64.mul (F64.ofInt 32) absdiff) absprod then false else true) := rfl
  rw [hdef, this] at h
  cases h


/-! ## The fast paths agree with the generic loop -/

theorem prodGeneric_nil (r : Ret) (it : It) : prodGeneric r it [] = it.finish r := by
  simp [prodGeneric, bind, Except.bind, pure, Except.pure]

theorem prodGeneric_cons (r : Ret) (it : It) (item : Arg) (rest : List Arg) :
    prodGeneric r it (item :: rest) =
      (match pyMul r item.toRet with
       | .ok r' => prodGeneric r' it rest
       | .error e => .error e) := by
  unfold prodGeneric
  simp only [List.foldlM_cons, bind, Except.bind]
  cases pyMul r item.toRet <;> rfl

theorem longAsDouble_long {n : Int} (h1 : LONG_MIN ≤ n) (h2 : n ≤ LONG_MAX) :
    PyLong_AsDouble n = .ok (F64.ofInt n) := by
  unfold LONG_MIN LONG_MAX at *
  obtain ⟨hf, _, _, _⟩ := ofInt_small_long (z := n) (by omega) (by omega)
  unfold PyLong_AsDouble
  simp [isInf_false_of_finite hf]

theorem prodFloat_eq (it : It) : ∀ (items : List Arg) (f : F64),
    prodFloat f it items = prodGeneric (.float f) it items := by
  intro items
  induction items with
  | nil => intro f; rw [prodGeneric_nil]; rfl
  | cons item rest ih =>
    intro f
    rw [prodGeneric_cons]
    cases item with
    | float x =>
      simp only [prodFloat, Arg.toRet, pyMul]
      exact ih _
    | int n =>
      simp only [prodFloat]
      split
      · rename_i hr
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
        rw [ih]
        simp only [Arg.toRet, pyMul, longAsDouble_long hr.1 hr.2, bind, Except.bind, pure, Except.pure]
      · simp only [Arg.toRet, bind, Except.bind]
        cases pyMul (.float f) (.int n) <;> rfl
    | floatSub t x fl ce tr =>
      simp only [prodFloat, bind, Except.bind]
      cases pyMul (.float f) (Arg.floatSub t x fl ce tr).toRet <;> rfl
    | bool b =>
      simp only [prodFloat, bind, Except.bind]
      cases pyMul (.float f) (Arg.bool b).toRet <;> rfl
    | other ty fq df di fl ce tr =>
      simp only [prodFloat, bind, Except.bind]
      cases pyMul (.float f) (Arg.other ty fq df di fl ce tr).toRet <;> rfl

theorem prodInt_eq (it : It) : ∀ (items : List Arg) (i : Int), LONG_MIN ≤ i → i ≤ LONG_MAX →
    prodInt i it items = prodGeneric (.int i) it items := by
  intro items
  induction items with
  | nil => intro i _ _; rw [prodGeneric_nil]; rfl
  | cons item rest ih =>
    intro i hi1 hi2
    rw [prodGeneric_cons]
    have slow : ∀ r : Py Ret, (match r with
        | .ok r' => prodGeneric r' it rest
        | .error e => .error e) =
        (do
          let r ← r
          match r with
          | .float f => prodFloat f it rest
          | r => prodGeneric r it rest) := by
      intro r
      cases r with
      | error e => rfl
      | ok r' =>
        simp only [bind, Except.bind]
        cases r' <;> try rfl
        exact (prodFloat_eq it rest _).symm
    cases item with
    | int b =>
      simp only [prodInt]
      split
      · rename_i x hx
        split at hx
        · rename_i hc
          cases hx
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
          obtain ⟨⟨hb1, hb2⟩, hck⟩ := hc
          have hw := check_sound hi1 hi2 hb1 hb2 hck
          rw [hw]
          have hr := wrap_range (i * b)
          rw [hw] at hr
          rw [ih (i * b) (by unfold LONG_MIN; omega) (by unfold LONG_MAX; omega)]
          rfl
        · cases hx
      · rename_i hx
        rw [slow]
        rfl
    | float x =>
      simp only [prodInt]; rw [slow]; rfl
    | floatSub t x fl ce tr =>
      simp only [prodInt]; rw [slow]; rfl
    | bool b =>
      simp only [prodInt]; rw [slow]; rfl
    | other ty fq df di fl ce tr =>
      simp only [prodInt]; rw [slow]; rfl

/-- `math.prod(iterable, start=start)` is `functools.reduce(operator.mul, iterable, start)` for
every iterable (including one whose iteration fails at the end) and start: the `long` and
`double` fast paths of `math_prod_impl` give exactly what the generic `PyNumber_Multiply` loop
gives. The core is `check_sound`: `_check_long_mult_overflow` never misses an overflow of the
C `long` product. Scope: items and start are ints, bools, floats, float subclasses or objects
without `__mul__`. -/
def ProdTwin : Prop :=
  ∀ (it : It) (start : Option Arg),
    math_prod it start = prodGeneric ((start.map Arg.toRet).getD (.int 1)) it it.items

theorem prodTwin_proven : ProdTwin := by
  intro it start
  unfold math_prod
  cases start with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    exact prodInt_eq it it.items 1 (by decide) (by decide)
  | some s =>
    simp only [Option.map_some, Option.getD_some]
    cases s with
    | int i =>
      simp only [Arg.toRet]
      split
      · rename_i h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact prodInt_eq it it.items i h.1 h.2
      · rfl
    | float f => exact prodFloat_eq it it.items f
    | floatSub t x fl ce tr => rfl
    | bool b => rfl
    | other ty fq df di fl ce tr => rfl


end PyLean.MathInt
