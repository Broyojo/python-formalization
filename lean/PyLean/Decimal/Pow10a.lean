import PyLean.Decimal.Division
import PyLean.Decimal.Lemmas
import PyLean.Decimal.DelegateExact
import PyLean.Binary64.Props2

/-!
`_is_less_than_pow10a` (new in 3.15, used by `remainder_near`) decides `len(str(q)) <= a`
exactly for every `math.log10` accurate to 19 ulps.

The float facts it needs (`math.ulp` of a positive normal double is its last bit, and the
three float operations of the helper) are proved here, in this module's own namespace, since
`Binary64` has no lemmas about `ulp`.
-/

namespace PyLean.Binary64
namespace F64

/-- The bits of the next float up from a positive finite non-maximal one. -/
theorem dec_next_up (z : F64) (hf : z.isFinite = true) (hs : z.sign = false)
    (hmax : z.bits ≠ 0x7fefffffffffffff) :
    let y := ofBits (z.bits + 1)
    y.isFinite = true ∧ y.sign = false ∧ y.toRat = z.toRat + pw z.lsbExp := by
  intro y
  have hd := bits_decomp z
  simp only [hs, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hd
  have hB := bexp_lt z
  have hF := frac_lt z
  have hfin := (isFinite_eq z).1 hf
  have hlt : z.bits + 1 < 2 ^ 64 := by omega
  have hyb : y.bits = z.bits + 1 := bits_ofBits_of_lt hlt
  have hz := toRat_of_finite hf
  simp only [hs, Bool.false_eq_true, ↓reduceIte] at hz
  by_cases hc : z.frac + 1 < 2 ^ 52
  · have e1 : y.bexp = z.bexp := by
      unfold bexp; rw [hyb, hd]
      have : (z.bexp * 2 ^ 52 + z.frac + 1) / 2 ^ 52 = z.bexp := by omega
      rw [this]; omega
    have e2 : y.frac = z.frac + 1 := by
      unfold frac; rw [hyb, hd]; omega
    have e3 : y.sign = false := by
      unfold sign; rw [hyb, hd]; simp; omega
    have yf : y.isFinite = true := by rw [isFinite_eq, e1]; exact hfin
    have hm : y.mant = z.mant + 1 := by unfold mant; rw [e1, e2]; split <;> omega
    have hl : y.lsbExp = z.lsbExp := by unfold lsbExp; rw [e1]
    refine ⟨yf, e3, ?_⟩
    rw [toRat_of_finite yf, e3, hz, hm, hl]
    simp only [Bool.false_eq_true, ↓reduceIte]
    push_cast; grind
  · have hF' : z.frac = 2 ^ 52 - 1 := by omega
    have hB' : z.bexp + 1 ≠ 2047 := by
      intro h; apply hmax; rw [hd, hF']; omega
    have e1 : y.bexp = z.bexp + 1 := by
      unfold bexp; rw [hyb, hd, hF']
      have : (z.bexp * 2 ^ 52 + (2 ^ 52 - 1) + 1) / 2 ^ 52 = z.bexp + 1 := by omega
      rw [this]; omega
    have e2 : y.frac = 0 := by
      unfold frac; rw [hyb, hd, hF']; omega
    have e3 : y.sign = false := by
      unfold sign; rw [hyb, hd]; simp; omega
    have yf : y.isFinite = true := by rw [isFinite_eq, e1]; exact hB'
    refine ⟨yf, e3, ?_⟩
    rw [toRat_of_finite yf, e3, hz]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hb0 : z.bexp = 0
    · have hm : y.mant = 2 ^ 52 := by unfold mant; rw [e1, e2]; simp
      have hzm : z.mant = 2 ^ 52 - 1 := by unfold mant; rw [hF']; simp [hb0]
      have hl : y.lsbExp = z.lsbExp := by unfold lsbExp; rw [e1, hb0]; rfl
      rw [hm, hzm, hl]
      push_cast; grind
    · have hm : y.mant = 2 ^ 52 := by unfold mant; rw [e1, e2]; simp
      have hzm : z.mant = 2 ^ 53 - 1 := by unfold mant; rw [hF']; simp [hb0]
      have hl : y.lsbExp = z.lsbExp + 1 := by unfold lsbExp; rw [e1]; omega
      rw [hm, hzm, hl, pw_succ]
      push_cast; grind

theorem dec_ulp_pos (z : F64) (hf : z.isFinite = true) (hs : z.sign = false)
    (hmax : z.bits ≠ 0x7fefffffffffffff) :
    (ulp z).isFinite = true ∧ (ulp z).toRat = pw z.lsbExp := by
  obtain ⟨yf, ys, yv⟩ := dec_next_up z hf hs hmax
  have ha : z.abs = z := by simp [abs, hs]
  have hu : ulp z = sub (ofBits (z.bits + 1)) z := by
    simp [ulp, isNaN_false_of_finite hf, isInf_false_of_finite hf, ha, hmax]
  rw [hu]
  unfold sub
  rw [add_of_finite yf (by rw [neg_isFinite]; exact hf), toRat_neg, yv]
  have hq : z.toRat + pw z.lsbExp + -z.toRat = pw z.lsbExp := by grind
  rw [hq, if_neg (pw_ne _)]
  have hrep : Rep binary64 (pw z.lsbExp) :=
    ⟨1, z.lsbExp, by decide, by have := lsbExp_ge z; simpa [Fmt.etiny, binary64] using this,
      Or.inl (by simp)⟩
  have hlt : Rat.abs (pw z.lsbExp) < overflowLimit := by
    rw [abs_of_nonneg (Rat.le_of_lt (pw_pos _))]
    have h1 : pw z.lsbExp ≤ pw 971 := pw_le (lsbExp_le z hf)
    have h2 : pw 971 < overflowLimit := by
      unfold overflowLimit
      rw [show (971 : Int) = 1 + 970 by rfl, pw_add, pw_one]
      have : (2 : Rat) < ((2 ^ 54 - 1 : Nat) : Rat) := by
        have h := Rat.natCast_lt_natCast.2 (show 2 < 2 ^ 54 - 1 by decide)
        exact h
      have hp := pw_pos 970
      grind
    grind
  exact ⟨(ofRat_isFinite _).2 hlt, ofRat_exact hrep hlt⟩

/-- A float in `[1, 2^40)` is normal, with its last bit between `2^-52` and `2^-13`. -/
theorem dec_pos_normal (z : F64) (hf : z.isFinite = true) (h1 : 1 ≤ z.toRat) (h2 : z.toRat < pw 40) :
    z.sign = false ∧ 2 ^ 52 ≤ z.mant ∧ -52 ≤ z.lsbExp ∧ z.lsbExp ≤ -13 ∧
      z.toRat = (z.mant : Rat) * pw z.lsbExp := by
  have hv := toRat_of_finite hf
  have hm := mant_lt z
  have e53 : pw 53 = ((2 ^ 53 : Nat) : Rat) := pw_natCast 53
  have hmr : (z.mant : Rat) < pw 53 := by
    rw [e53]; exact Rat.natCast_lt_natCast.2 hm
  have hs : z.sign = false := by
    cases h : z.sign
    · rfl
    · rw [h] at hv; simp only [↓reduceIte] at hv
      have : 0 ≤ (z.mant : Rat) * pw z.lsbExp := Rat.mul_nonneg (by exact_mod_cast Nat.zero_le _) (Rat.le_of_lt (pw_pos _))
      grind
  rw [hs] at hv; simp only [Bool.false_eq_true, ↓reduceIte] at hv
  have hk1 : -52 ≤ z.lsbExp := by
    rcases Int.lt_or_le z.lsbExp (-52) with hk | hk
    · exfalso
      have : pw z.lsbExp ≤ pw (-53) := pw_le (by omega)
      have e : pw 53 * pw (-53) = 1 := by rw [← pw_add]; exact pw_zero
      have hp := pw_pos z.lsbExp
      have hmn : (0 : Rat) ≤ z.mant := by exact_mod_cast Nat.zero_le _
      have a := Rat.mul_le_mul_of_nonneg_left this hmn
      have b := Rat.mul_lt_mul_of_pos_right hmr (pw_pos (-53))
      grind
    · exact hk
  have hmc : 2 ^ 52 ≤ z.mant := by
    rcases mant_canon z with h | h
    · exact h
    · omega
  have hk2 : z.lsbExp ≤ -13 := by
    rcases Int.lt_or_le z.lsbExp (-12) with hk | hk
    · omega
    exfalso
    have : pw (-12) ≤ pw z.lsbExp := pw_le (by omega)
    have e : pw 52 * pw (-12) = pw 40 := by rw [← pw_add]; rfl
    have e52 : pw 52 = ((2 ^ 52 : Nat) : Rat) := pw_natCast 52
    have hmr2 : pw 52 ≤ (z.mant : Rat) := by
      rw [e52]; exact Rat.natCast_le_natCast.2 hmc
    have : pw 52 * pw (-12) ≤ (z.mant : Rat) * pw z.lsbExp :=
      Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hmr2 (Rat.le_of_lt (pw_pos _)))
        (Rat.mul_le_mul_of_nonneg_left this (by exact_mod_cast Nat.zero_le _))
    grind
  exact ⟨hs, hmc, hk1, hk2, hv⟩

theorem dec_limit_big : pw 41 < overflowLimit := by
  unfold overflowLimit
  have : pw 41 ≤ pw 970 := pw_le (by decide)
  have h : (1 : Rat) < ((2 ^ 54 - 1 : Nat) : Rat) := by
    have h := Rat.natCast_lt_natCast.2 (show 1 < 2 ^ 54 - 1 by decide)
    exact h
  have hp := pw_pos 970
  grind

theorem dec_exact_of (q : Rat) (M : Nat) (E : Int) (hM : M < 2 ^ 53) (hE : -1074 ≤ E) (hq : q = (M : Rat) * pw E)
    (hlt : Rat.abs q < overflowLimit) : (ofRat q).isFinite = true ∧ (ofRat q).toRat = q :=
  ⟨(ofRat_isFinite _).2 hlt, ofRat_exact ⟨M, E, hM, by simpa [Fmt.etiny, binary64] using hE, Or.inl hq⟩ hlt⟩

/-- The three floats `_is_less_than_pow10a` computes from `z = math.log10(q)` in `[1, 2^40)`:
`t = ulp(z) * 20` and `z - t` are exact, `z + t` is rounded to nearest. -/
theorem dec_pow10a_floats (z : F64) (hf : z.isFinite = true) (h1 : 1 ≤ z.toRat) (h2 : z.toRat < pw 40) :
    let u := pw z.lsbExp
    let t := mul (ulp z) (ofInt 20)
    64 * u ≤ 1 ∧ 0 < u ∧
    (sub z t).isFinite = true ∧ (sub z t).toRat = z.toRat - 20 * u ∧
    (add z t).isFinite = true ∧ (add z t).toRat ≤ z.toRat + 40 * u ∧
    (∀ m : Int, m.natAbs < 2 ^ 53 → (m : Rat) ≤ z.toRat + 20 * u → (m : Rat) ≤ (add z t).toRat) := by
  intro u t
  obtain ⟨hs, hmc, hk1, hk2, hv⟩ := dec_pos_normal z hf h1 h2
  have hmax : z.bits ≠ 0x7fefffffffffffff := by
    intro h
    have : z.lsbExp = 971 := by
      unfold lsbExp bexp; rw [h]; rfl
    omega
  obtain ⟨uf, uv⟩ := dec_ulp_pos z hf hs hmax
  have hu0 : 0 < u := pw_pos _
  have hu13 : u ≤ pw (-13) := pw_le hk2
  have hp13 : pw (-13) < 1 := by
    have := pw_lt (show (-13 : Int) < 0 by decide); rw [pw_zero] at this; exact this
  have h64 : 64 * u ≤ 1 := by
    have e6 : pw 6 = ((2 ^ 6 : Nat) : Rat) := pw_natCast 6
    have : pw (6 + z.lsbExp) ≤ pw 0 := pw_le (by omega)
    rw [pw_add, e6, pw_zero] at this
    have e64 : ((2 ^ 6 : Nat) : Rat) = 64 := by simp
    rw [e64] at this
    exact this
  obtain ⟨tf20, tv20⟩ := ofInt_small (n := (20 : Int)) (by decide : (20 : Int).natAbs < 2 ^ 53)
  have htq : (ulp z).toRat * (ofInt 20).toRat = 20 * u := by rw [uv, tv20]; push_cast; grind
  have htf : t.isFinite = true ∧ t.toRat = 20 * u := by
    simp only [t]
    rw [mul_of_finite uf tf20, htq, if_neg (by grind)]
    refine dec_exact_of _ 20 z.lsbExp (by decide) (lsbExp_ge z) (by push_cast; grind) ?_
    rw [abs_of_nonneg (by grind)]
    have := dec_limit_big
    have : pw z.lsbExp ≤ pw 41 := pw_le (by omega)
    grind
  obtain ⟨tf, tv⟩ := htf
  have hmr : (2 ^ 52 : Rat) ≤ z.mant := by exact_mod_cast hmc
  have hlo : (sub z t).isFinite = true ∧ (sub z t).toRat = z.toRat - 20 * u := by
    unfold sub
    rw [add_of_finite hf (by rw [neg_isFinite]; exact tf), toRat_neg, tv]
    have hne : z.toRat + -(20 * u) ≠ 0 := by
      rw [hv]
      have : (20 : Rat) < z.mant := by grind
      have : 20 * u < (z.mant : Rat) * u := Rat.mul_lt_mul_of_pos_right this hu0
      grind
    rw [if_neg hne]
    have hM : z.mant - 20 < 2 ^ 53 := by have := mant_lt z; omega
    obtain ⟨a1, a2⟩ := dec_exact_of (z.toRat + -(20 * u)) (z.mant - 20) z.lsbExp hM (lsbExp_ge z)
      (by rw [hv]
          have hud : u = pw z.lsbExp := rfl
          obtain ⟨m', hm'⟩ : ∃ m', z.mant = m' + 20 := ⟨z.mant - 20, by omega⟩
          rw [show z.mant - 20 = m' by omega, hm', hud]
          push_cast; grind)
      (by rw [abs_of_nonneg (by grind)]; have := dec_limit_big; have : pw 40 ≤ pw 41 := pw_le (by decide); grind)
    exact ⟨a1, by rw [a2]; grind⟩
  obtain ⟨lf, lv⟩ := hlo
  have hq0 : z.toRat + t.toRat ≠ 0 := by rw [tv]; grind
  have hadd : add z t = ofRat (z.toRat + t.toRat) := by rw [add_of_finite hf tf, if_neg hq0]
  have hqlt : Rat.abs (z.toRat + t.toRat) < overflowLimit := by
    rw [tv, abs_of_nonneg (by grind)]
    have := dec_limit_big
    have e : pw 41 = 2 * pw 40 := by rw [show (41 : Int) = 40 + 1 by rfl, pw_succ]
    grind
  have hf2 : (add z t).isFinite = true := by rw [hadd]; exact (ofRat_isFinite _).2 hqlt
  have near := fun (y : F64) (hy : y.isFinite = true) => ofRat_nearest (z.toRat + t.toRat) (by rw [← hadd]; exact hf2) hy
  rw [← hadd] at near
  refine ⟨h64, hu0, lf, lv, hf2, ?_, ?_⟩
  · have := near z hf
    rw [tv] at this
    rw [abs_eq_ite, abs_eq_ite] at this
    split at this <;> split at this <;> grind
  · intro m hm hle
    obtain ⟨mf, mv⟩ := ofInt_small hm
    have := near (ofInt m) mf
    rw [tv, mv] at this
    rw [abs_eq_ite, abs_eq_ite] at this
    split at this <;> split at this <;> grind

end F64
end PyLean.Binary64

namespace PyLean.Decimal

open PyLean Binary64

/-- What `_is_less_than_pow10a` relies on `math.log10` for (its `ulp_order=20` margin): for every
int `q ≥ 10` with fewer than `2^40` digits, `math.log10(q)` is a finite double in `[1, 2^40)`
whose interval of 19 ulps on either side meets `[len(str(q)) - 1, len(str(q)))`, the interval
the exact `log10(q)` lies in. CPython's `math.log10` of an int is within about one ulp
(libm's `log10` of the correctly rounded double, or `fma(log10(2), e, log10(x))` past `2^1024`;
the largest error measured over 2824 ints up to `2^1000000` bits is 0.56 ulp). The digit bound
excludes only ints of more than a trillion digits (several hundred gigabytes). -/
def Log10Accurate (lg : Nat → Binary64.F64) : Prop :=
  ∀ q : Nat, 10 ≤ q → numDigits q < 2 ^ 40 →
    (lg q).isFinite = true ∧ 1 ≤ (lg q).toRat ∧ (lg q).toRat < pw 40 ∧
    (lg q).toRat - 19 * (Binary64.F64.ulp (lg q)).toRat < numDigits q ∧
    ((numDigits q : Rat) - 1) ≤ (lg q).toRat + 19 * (Binary64.F64.ulp (lg q)).toRat

theorem floor_le_of_lt' {x : Rat} {k : Int} (h : x < (k : Rat) + 1) : x.floor ≤ k := by
  have h1 := Rat.floor_le x
  have h2 : ((x.floor : Int) : Rat) < ((k + 1 : Int) : Rat) := by push_cast; grind
  have := Rat.intCast_lt_intCast.1 h2
  omega

theorem le_floor_of_le' {x : Rat} {k : Int} (h : (k : Rat) ≤ x) : k ≤ x.floor := by
  have h1 := Rat.lt_floor_add_one x
  have h2 : ((k : Int) : Rat) < ((x.floor + 1 : Int) : Rat) := by push_cast; grind
  have := Rat.intCast_lt_intCast.1 h2
  omega

theorem truncInt_nonneg {x : Binary64.F64} (hx : x.isFinite = true) (h : 0 ≤ x.toRat) :
    x.truncInt = x.toRat.floor := by
  unfold Binary64.F64.truncInt Binary64.F64.floorInt Binary64.F64.ceilInt
  cases hs : x.sign
  · rfl
  · simp only [↓reduceIte]
    have hv := Binary64.F64.toRat_of_finite hx
    rw [hs] at hv; simp only [↓reduceIte] at hv
    have : 0 ≤ (x.mant : Rat) * pw x.lsbExp :=
      Rat.mul_nonneg (by exact_mod_cast Nat.zero_le _) (Rat.le_of_lt (pw_pos _))
    have h0 : x.toRat = 0 := by grind
    rw [h0]; rfl

theorem floatToInt_finite {x : Binary64.F64} (hx : x.isFinite = true) : floatToInt x = .ok x.truncInt := by
  simp [floatToInt, Binary64.F64.isNaN_false_of_finite hx, Binary64.F64.isInf_false_of_finite hx]

theorem tento_eq (n : Nat) : tento n = 10 ^ n := by
  unfold tento; rw [← Nat.mul_pow]

/-- `_is_less_than_pow10a(q, a)` is `len(str(q)) <= a`, for every `math.log10` accurate in the
sense of `Log10Accurate`, every `a` and every `q` with fewer than `2^40` digits: the two
assertions hold and the exact `_tento` comparison settles the band where `z ± 20 ulp` straddles
an integer. -/
def Pow10aExact : Prop :=
  ∀ (lg : Nat → Binary64.F64), Log10Accurate lg → ∀ q a : Nat, numDigits q < 2 ^ 40 →
    isLessThanPow10a lg q a = .ok (decide (numDigits q ≤ a))

theorem pow10aExact_proven : Pow10aExact := by
  intro lg hacc q a hq
  by_cases h10 : q < 10
  · have : numDigits q = 1 := by
      have := (numDigits_le_iff (k := 1) (by decide)).2 (by omega : q < 10 ^ 1)
      have := numDigits_pos q
      omega
    rw [this]
    simp only [isLessThanPow10a, h10, ↓reduceIte, pure, Except.pure, ge_iff_le]
  obtain ⟨hf, h1, h2, hlo, hhi⟩ := hacc q (by omega) hq
  simp only [isLessThanPow10a, h10, ↓reduceIte]
  generalize lg q = z at hf h1 h2 hlo hhi
  obtain ⟨hs, _, _, _, _⟩ := Binary64.F64.dec_pos_normal z hf h1 h2
  have hmax : z.bits ≠ 0x7fefffffffffffff := by
    intro h
    have : z.lsbExp = 971 := by unfold Binary64.F64.lsbExp Binary64.F64.bexp; rw [h]; rfl
    obtain ⟨_, _, _, hk, _⟩ := Binary64.F64.dec_pos_normal z hf h1 h2
    omega
  obtain ⟨_, uv⟩ := Binary64.F64.dec_ulp_pos z hf hs hmax
  obtain ⟨h64, hu0, lf, lv, hf2, hup, hdn⟩ := Binary64.F64.dec_pow10a_floats z hf h1 h2
  rw [uv] at hlo hhi
  generalize pw z.lsbExp = u at h64 hu0 lv hup hdn hlo hhi
  generalize Binary64.F64.sub z (Binary64.F64.mul (Binary64.F64.ulp z) (Binary64.F64.ofInt 20)) = lo at lf lv
  generalize Binary64.F64.add z (Binary64.F64.mul (Binary64.F64.ulp z) (Binary64.F64.ofInt 20)) = hi at hf2 hup hdn
  have hnd2 : 2 ≤ numDigits q := by
    have hp := numDigits_pos q
    rcases Nat.lt_or_ge (numDigits q) 2 with hc | hc
    · have : numDigits q ≤ 1 := by omega
      have := (numDigits_le_iff (k := 1) (by decide) (n := q)).1 this
      omega
    · exact hc
  generalize hN : numDigits q = N at *
  have hlo0 : 0 ≤ lo.toRat := by rw [lv]; grind
  rw [floatToInt_finite lf, truncInt_nonneg lf hlo0, lv]
  have hhi0 : 0 ≤ hi.toRat := by
    have := hdn 0 (by decide) (by push_cast; grind)
    simpa using this
  rw [floatToInt_finite hf2, truncInt_nonneg hf2 hhi0]
  simp only [bind, Except.bind, pure, Except.pure]
  have A : (z.toRat - 20 * u).floor ≤ (N : Int) - 1 :=
    floor_le_of_lt' (by push_cast; grind)
  have B : (N : Int) - 2 ≤ (z.toRat - 20 * u).floor :=
    le_floor_of_le' (by push_cast; grind)
  have C : (N : Int) - 1 ≤ hi.toRat.floor := by
    apply le_floor_of_le'
    apply hdn
    · omega
    · push_cast; grind
  have D : hi.toRat.floor ≤ (N : Int) := floor_le_of_lt' (by push_cast; grind)
  have E : ¬((z.toRat - 20 * u).floor = (N : Int) - 2 ∧ hi.toRat.floor = (N : Int)) := by
    intro ⟨e1, e2⟩
    have f1 := Rat.lt_floor_add_one (z.toRat - 20 * u)
    have f2 := Rat.floor_le hi.toRat
    rw [e1] at f1; rw [e2] at f2
    push_cast at f1 f2
    grind
  generalize (z.toRat - 20 * u).floor = lo' at A B E
  generalize hi.toRat.floor = hi' at C D E
  have hql : 10 ^ (N - 1) ≤ q := by rw [← hN]; exact pow_numDigits_le (by omega)
  have hqu : q < 10 ^ N := by rw [← hN]; exact lt_pow_numDigits q
  by_cases hd0 : hi' - lo' = 0
  · have : hi' = (N : Int) - 1 := by omega
    simp only [hd0, true_or, not_true_eq_false, ↓reduceIte, show ¬ ((0 : Int) = 1) by decide]
    rw [this]
    simp only [Except.ok.injEq, decide_eq_decide]
    omega
  · have hd1 : hi' - lo' = 1 := by omega
    simp only [hd1, or_true, not_true_eq_false, ↓reduceIte, show ¬ hi' < 0 by omega, tento_eq]
    by_cases hh : hi' = (N : Int) - 1
    · have : hi'.toNat = N - 1 := by omega
      rw [this]
      simp only [show ¬ q < 10 ^ (N - 1) by omega, ↓reduceIte, Except.ok.injEq, decide_eq_decide]
      omega
    · have hh2 : hi' = (N : Int) := by omega
      have : hi'.toNat = N := by omega
      rw [this]
      have hdiv : 10 ^ N / 10 = 10 ^ (N - 1) := by
        obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
        simp [Nat.pow_succ]
      simp only [hqu, ↓reduceIte, hdiv, show q ≥ 10 ^ (N - 1) by omega, not_true_eq_false,
        Except.ok.injEq, decide_eq_decide, hh2]
      omega

end PyLean.Decimal

namespace PyLean.Decimal

open PyLean Binary64

/-- The stand-in `log10Stand` the difftest and the `Context` wrappers run with is accurate. -/
theorem log10Stand_accurate : Log10Accurate log10Stand := by
  intro q hq hnd
  have hnd2 : 2 ≤ numDigits q := by
    have hp := numDigits_pos q
    rcases Nat.lt_or_ge (numDigits q) 2 with hc | hc
    · have : numDigits q ≤ 1 := by omega
      have := (numDigits_le_iff (k := 1) (by decide) (n := q)).1 this
      omega
    · exact hc
  simp only [log10Stand]
  obtain ⟨zf, zv⟩ := Binary64.ofInt_small (n := (numDigits q : Int) - 1) (by omega)
  generalize Binary64.F64.ofInt ((numDigits q : Int) - 1) = z at zf zv ⊢
  have e40 : pw 40 = ((2 ^ 40 : Nat) : Rat) := pw_natCast 40
  have hz1 : (1 : Rat) ≤ z.toRat := by
    rw [zv]
    have : ((1 : Int) : Rat) ≤ (((numDigits q : Int) - 1 : Int) : Rat) := Rat.intCast_le_intCast.2 (by omega)
    simpa using this
  have hz2 : z.toRat < pw 40 := by
    rw [zv, e40]
    have : (((numDigits q : Int) - 1 : Int) : Rat) < (((2 ^ 40 : Nat) : Int) : Rat) :=
      Rat.intCast_lt_intCast.2 (by omega)
    simpa using this
  obtain ⟨hs, _, _, hk, _⟩ := Binary64.F64.dec_pos_normal z zf hz1 hz2
  have hmax : z.bits ≠ 0x7fefffffffffffff := by
    intro h
    have : z.lsbExp = 971 := by
      unfold Binary64.F64.lsbExp Binary64.F64.bexp; rw [h]; rfl
    omega
  obtain ⟨_, uv⟩ := Binary64.F64.dec_ulp_pos z zf hs hmax
  have hu := pw_pos z.lsbExp
  refine ⟨zf, hz1, hz2, ?_, ?_⟩
  · rw [uv, zv]; push_cast; grind
  · rw [uv, zv]; push_cast; grind

/-- `remainder_near`'s correction (_pydecimal.py:1605-1611) is the nearest integer quotient,
ties to even, written without the source's `q & 1` trick. -/
theorem nearestQR_spec (x y : Nat) (hy : 0 < y) :
    let n := if 2 * (x % y) > y ∨ (2 * (x % y) = y ∧ (x / y) % 2 = 1) then x / y + 1 else x / y
    nearestQR x y = (n, (x : Int) - n * y) ∧
    (2 * ((x : Int) - n * y).natAbs < y ∨ (2 * ((x : Int) - n * y).natAbs = y ∧ n % 2 = 0)) := by
  intro n
  have hdm := Nat.div_add_mod x y
  have hlt := Nat.mod_lt x hy
  have h2 : (x / y) % 2 < 2 := Nat.mod_lt _ (by decide)
  unfold nearestQR
  by_cases hc : 2 * (x % y) > y ∨ (2 * (x % y) = y ∧ (x / y) % 2 = 1)
  · have hc' : 2 * (x % y) + (x / y) % 2 > y := by omega
    have hn : n = x / y + 1 := by simp only [n, hc, ↓reduceIte]
    simp only [hc', ↓reduceIte, hn]
    refine ⟨by simp only [Prod.mk.injEq, true_and]; push_cast; grind, ?_⟩
    have e : ((x : Int) - ((x / y + 1 : Nat) : Int) * y) = (x % y : Int) - y := by push_cast; grind
    rw [e]
    omega
  · have hc' : ¬ (2 * (x % y) + (x / y) % 2 > y) := by omega
    have hn : n = x / y := by simp only [n, hc, ↓reduceIte]
    simp only [hc', ↓reduceIte, hn]
    refine ⟨by simp only [Prod.mk.injEq, true_and]; push_cast; grind, ?_⟩
    have e : ((x : Int) - ((x / y : Nat) : Int) * y) = (x % y : Int) := by push_cast; grind
    rw [e]
    omega

/-- `remainder_near(a, b)` (_pydecimal.py:1550-1625) for finite non-zero operands whose adjusted
exponents differ by -1 to prec, for every `math.log10` accurate in the sense of `Log10Accurate`:
with both operands as integers `x`, `y` at the lower exponent, `n` the integer nearest `x / y`
(ties to the even one) and `r = x - n·y`, so that `2·|r| ≤ y`, the result is InvalidOperation
(DivisionImpossible) exactly when `n` has more than `prec` digits, and otherwise `±|r|` (the
sign of `a`, flipped when `r < 0`) at exponent `min(ea, eb)`, rounded into the context by `_fix`;
the int/str-limit `ValueError` of `str(r)` is the only other outcome. The other branches: a NaN
goes through `_check_nans`, an infinite `a` or a zero `b` is InvalidOperation, an infinite `b`
gives `a` through `_fix`. The quotient is assumed to have fewer than `2^40` digits. -/
def RemainderNearExact : Prop :=
  ∀ (lg : Nat → Binary64.F64), Log10Accurate lg → ∀ (c : Ctx) (fl : List Signal), 1 ≤ c.prec →
    (∀ (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int),
      ca ≠ 0 → cb ≠ 0 → numDigits ca ≤ maxStrDigits → numDigits cb ≤ maxStrDigits →
      let ex := (ea + numDigits ca - 1) - (eb + numDigits cb - 1)
      (-2 : Int) < ex → ex < c.prec + 1 →
      let x := (scaled ca ea cb eb).1
      let y := (scaled ca ea cb eb).2
      let n := if 2 * (x % y) > y ∨ (2 * (x % y) = y ∧ (x / y) % 2 = 1) then x / y + 1 else x / y
      let r : Int := x - n * y
      numDigits n < 2 ^ 40 →
      (2 * r.natAbs < y ∨ (2 * r.natAbs = y ∧ n % 2 = 0)) ∧
      (remainderNearL lg c (.fin sa ca ea) (.fin sb cb eb)).run fl =
        (if 10 ^ c.prec ≤ n then afterSig c .invalidOperation fl (.nan false false 0)
        else if maxStrDigits < numDigits r.natAbs then Except.error (PyExc.valueError limitToStrMsg)
        else (fix c (.fin (if r < 0 then !sa else sa) r.natAbs (min ea eb))).run fl)) ∧
    (∀ (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (eb : Int), nanKind (.fin sa ca ea) = 0 →
      (remainderNearL lg c (.fin sa ca ea) (.fin sb 0 eb)).run fl = afterSig c .invalidOperation fl (.nan false false 0)) ∧
    (∀ (na : Bool) (b : Dec), nanKind b = 0 →
      (remainderNearL lg c (.inf na) b).run fl = afterSig c .invalidOperation fl (.nan false false 0)) ∧
    (∀ (sa : Bool) (ca : Nat) (ea : Int) (nb : Bool), ca ≠ 0 →
      (remainderNearL lg c (.fin sa ca ea) (.inf nb)).run fl = (fix c (.fin sa ca ea)).run fl)

theorem scaled_pos (ca cb : Nat) (ea eb : Int) (hb : cb ≠ 0) : 0 < (scaled ca ea cb eb).2 := by
  unfold scaled; split
  · exact Nat.pos_of_ne_zero hb
  · exact Nat.mul_pos (Nat.pos_of_ne_zero hb) (Nat.pow_pos (by decide))

theorem remainderNearExact_proven : RemainderNearExact := by
  intro lg hacc c fl hprec
  have hz : ∀ (s : Bool) (co : Nat) (e : Int), co ≠ 0 → decBool (.fin s co e) = true := by
    intro s co e hc; cases co with
    | zero => exact absurd rfl hc
    | succ n => rfl
  refine ⟨fun sa ca ea sb cb eb ha hb la lb => ?_, fun sa ca ea sb eb hna => ?_,
    fun na b hnb => ?_, fun sa ca ea nb hca => ?_⟩
  · intro ex h1 h2 x y n r hn
    have hy := scaled_pos ca cb ea eb hb
    obtain ⟨hqr, hnear⟩ := nearestQR_spec x y hy
    refine ⟨hnear, ?_⟩
    have hp := pow10aExact_proven lg hacc n c.prec hn
    have hiff : decide (numDigits n ≤ c.prec) = !decide (10 ^ c.prec ≤ n) := by
      have := numDigits_le_iff (n := n) (k := c.prec) (by omega)
      by_cases h : 10 ^ c.prec ≤ n
      · simp [h]; omega
      · simp [h]; omega
    simp only [remainderNearL, bind_assoc]
    rw [checkNans_none_bind c _ _ rfl rfl]
    simp only [isinfinity, hz sb cb eb hb, hz sa ca ea ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      ne_eq, not_true_eq_false, expOf, Dec.adjusted, adjustedD]
    simp only [show ¬ (ea + numDigits ca - 1 - (eb + numDigits cb - 1) ≥ c.prec + 1) by omega,
      show ¬ (ea + numDigits ca - 1 - (eb + numDigits cb - 1) ≤ -2) by omega, ↓reduceIte]
    have w1 : workRep (.fin sa ca ea) = .ok (sa, ca, ea) := by
      simp [workRep, intLimit, show ¬ numDigits ca > maxStrDigits by omega, bind, Except.bind, pure, Except.pure]
    have w2 : workRep (.fin sb cb eb) = .ok (sb, cb, eb) := by
      simp [workRep, intLimit, show ¬ numDigits cb > maxStrDigits by omega, bind, Except.bind, pure, Except.pure]
    rw [liftPy_run, w1]
    simp only []
    rw [liftPy_run, w2]
    simp only []
    rw [hqr]
    simp only [n] at hp hiff
    rw [liftPy_run, hp]
    simp only []
    rw [hiff, Bool.not_not]
    by_cases hbig : 10 ^ c.prec ≤ n
    · have hbig' : 10 ^ c.prec ≤ (if 2 * (x % y) > y ∨ 2 * (x % y) = y ∧ x / y % 2 = 1 then x / y + 1 else x / y) := hbig
      simp only [hbig, hbig', decide_true, ↓reduceIte]
      exact invalid_run c fl
    · have hbig' : ¬ 10 ^ c.prec ≤ (if 2 * (x % y) > y ∨ 2 * (x % y) = y ∧ x / y % 2 = 1 then x / y + 1 else x / y) := hbig
      simp only [hbig, hbig', decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [liftPy_run]
      by_cases hl : maxStrDigits < numDigits r.natAbs
      · have hl' : numDigits ((x : Int) - ((if 2 * (x % y) > y ∨ 2 * (x % y) = y ∧ x / y % 2 = 1 then x / y + 1
            else x / y : Nat) : Int) * (y : Int)).natAbs > maxStrDigits := hl
        simp only [strLimit, hl', hl, ↓reduceIte]
      · have hl' : ¬ numDigits ((x : Int) - ((if 2 * (x % y) > y ∨ 2 * (x % y) = y ∧ x / y % 2 = 1 then x / y + 1
            else x / y : Nat) : Int) * (y : Int)).natAbs > maxStrDigits := hl
        simp only [strLimit, hl', hl, ↓reduceIte]
        rfl
  · simp only [remainderNearL]
    rw [checkNans_none_bind c _ _ rfl rfl]
    simp only [isinfinity, decBool, isZero, Bool.not_true, Bool.not_false, ↓reduceIte, ne_eq,
      not_true_eq_false]
    exact invalid_run c fl
  · simp only [remainderNearL]
    rw [checkNans_none_bind c _ _ rfl hnb]
    simp only [isinfinity, ne_eq]
    cases na <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.reduceNeg, Int.reduceEq, not_false_eq_true] <;>
      exact invalid_run c fl
  · simp only [remainderNearL]
    rw [checkNans_none_bind c _ _ rfl rfl]
    simp only [isinfinity, decBool, isZero, Bool.not_true, Bool.not_false, ↓reduceIte, ne_eq,
      not_true_eq_false, Bool.false_eq_true]
    cases nb <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.reduceNeg, Int.reduceEq, not_false_eq_true] <;>
      (rw [bind_pure])

end PyLean.Decimal
