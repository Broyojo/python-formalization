import PyLean.Binary64.Props4

/-!
`roundPos` leaves a number of the format alone, for any format, and with that the binary32
pack and unpack routines invert each other.
-/

namespace PyLean.Binary64

open F64

/-- The half of canonical uniqueness where `e₁ < e₂` is impossible, for any precision. -/
theorem canon_no_lt_gen {p m1 m2 : Nat} {e1 e2 : Int} (hp : 1 ≤ p) (h1 : m1 < 2 ^ p)
    (h2 : 2 ^ (p - 1) ≤ m2) (heq : (m1 : Rat) * pw e1 = (m2 : Rat) * pw e2) : ¬ e1 < e2 := by
  intro hlt
  have hk : pw e2 = ((2 ^ (e2 - e1).toNat : Nat) : Rat) * pw e1 := by
    rw [← pw_natCast, ← pw_add]; congr 1; omega
  rw [hk] at heq
  have h3 : (m1 : Rat) = (m2 : Rat) * ((2 ^ (e2 - e1).toNat : Nat) : Rat) := by
    have h5 : (m1 : Rat) * pw e1 * (pw e1)⁻¹ =
        (m2 : Rat) * (((2 ^ (e2 - e1).toNat : Nat) : Rat) * pw e1) * (pw e1)⁻¹ := by
      rw [heq]
    rw [Rat.mul_assoc, Rat.mul_assoc, Rat.mul_assoc, pw_mul_inv, Rat.mul_one, Rat.mul_one] at h5
    exact h5
  have h4 : m1 = m2 * 2 ^ (e2 - e1).toNat := by exact_mod_cast h3
  have h5 : 2 ≤ 2 ^ (e2 - e1).toNat := by
    have : 1 ≤ (e2 - e1).toNat := by omega
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (e2 - e1).toNat := Nat.pow_le_pow_right (by omega) this
  have h6 : m2 * 2 ≤ m2 * 2 ^ (e2 - e1).toNat := Nat.mul_le_mul_left _ h5
  have h7 : 2 ^ p = 2 * 2 ^ (p - 1) := by
    rw [show p = p - 1 + 1 by omega, Nat.pow_succ]; simp; omega
  omega

/-- `roundPos` returns a canonical `(m, e)` of the format for the number it denotes. -/
theorem roundPos_exact (f : Fmt) (hp : 2 ≤ f.p) {n d m : Nat} {e : Int} (hn : 0 < n) (hd : 0 < d)
    (hm : m < 2 ^ f.p) (he : f.etiny ≤ e) (hc : 2 ^ (f.p - 1) ≤ m ∨ e = f.etiny)
    (hmax : e + ((f.p - 1 : Nat) : Int) ≤ f.emax) (hv : (n : Rat) / d = (m : Rat) * pw e) :
    roundPos f n d = some (m, e) := by
  have hrep : Rep f ((m : Rat) * pw e) := ⟨m, e, hm, he, Or.inl rfl⟩
  have hnear := rounded_nearest f (by omega) hn hd hrep
  rw [hv] at hnear
  simp only [Rat.sub_self] at hnear
  rw [abs_of_nonneg (a := 0) (by decide)] at hnear
  have h0 := abs_le_zero hnear
  have hval : (m : Rat) * pw e = (roundedInt f n d : Rat) * pw (roundExp f n d) := by
    unfold roundedInt; grind
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
  rw [hdef]
  generalize roundedInt f n d = q' at *
  generalize roundExp f n d = e0 at *
  generalize (divPow2 n d e0).1 = q at *
  have h2p : 2 ^ f.p = 2 * 2 ^ (f.p - 1) := by
    rw [show f.p = f.p - 1 + 1 by omega, Nat.pow_succ]; simp; omega
  have huniq : ∀ (M : Nat) (E : Int), M < 2 ^ f.p → f.etiny ≤ E → (2 ^ (f.p - 1) ≤ M ∨ E = f.etiny) →
      (M : Rat) * pw E = (m : Rat) * pw e → M = m ∧ E = e := by
    intro M E h1 h2 h4 h5
    have hE : E = e := by
      by_cases hlt : E < e
      · have : e ≠ f.etiny := by omega
        have hmm : 2 ^ (f.p - 1) ≤ m := by rcases hc with h | h; exact h; exact absurd h this
        exact absurd hlt (canon_no_lt_gen (by omega) h1 hmm h5)
      · by_cases hgt : e < E
        · have : E ≠ f.etiny := by omega
          have hmm : 2 ^ (f.p - 1) ≤ M := by rcases h4 with h | h; exact h; exact absurd h this
          exact absurd hgt (canon_no_lt_gen (by omega) hm hmm h5.symm)
        · omega
    subst hE
    have h6 : (M : Rat) * pw E * (pw E)⁻¹ = (m : Rat) * pw E * (pw E)⁻¹ := by rw [h5]
    rw [Rat.mul_assoc, Rat.mul_assoc, pw_mul_inv, Rat.mul_one, Rat.mul_one] at h6
    exact ⟨Rat.natCast_inj.1 h6, rfl⟩
  by_cases hcq : q' = 2 ^ f.p
  · simp only [hcq, ↓reduceIte]
    obtain ⟨u1, u2⟩ := huniq (2 ^ (f.p - 1)) (e0 + 1) (by omega) (by omega) (Or.inl (Nat.le_refl _)) (by
      rw [hval, hcq, pw_succ, h2p]; push_cast; grind)
    have hle : ¬ (f.emax : Int) < e0 + 1 + ((f.p - 1 : Nat) : Int) := by omega
    rw [if_neg hle, u1, u2]
  · simp only [hcq, ↓reduceIte]
    obtain ⟨u1, u2⟩ := huniq q' e0 (by omega) h3 (by
      rcases hq2 with h | h
      · right; exact h
      · left; omega) hval.symm
    have hle : ¬ (f.emax : Int) < e0 + ((f.p - 1 : Nat) : Int) := by omega
    rw [if_neg hle, u1, u2]

theorem byte_layout4 (v : Nat) (h : v < 2 ^ 32) (le : Bool) : unlayout (layout 4 v le) le = v := by
  cases le <;> simp [unlayout, layout, List.range, List.range.loop] <;> omega

theorem etiny32 : binary32.etiny = -149 := by decide

/-- The fields of a binary32 pattern. -/
theorem view32 (v : Nat) (h : v < 2 ^ 32) :
    binary32.view v =
      if (v / 2 ^ 23) % 256 = 255 then
        (if v % 2 ^ 23 = 0 then View.inf (decide (2 ^ 31 ≤ v)) else View.nan (decide (2 ^ 31 ≤ v)) (v % 2 ^ 23))
      else if (v / 2 ^ 23) % 256 = 0 then View.finite (decide (2 ^ 31 ≤ v)) (v % 2 ^ 23) (-149)
      else View.finite (decide (2 ^ 31 ≤ v)) (2 ^ 23 + v % 2 ^ 23) ((((v / 2 ^ 23) % 256 : Nat) : Int) - 150) := by
  have hm : v % 2 ^ 32 = v := Nat.mod_eq_of_lt h
  unfold Fmt.view
  simp only [show binary32.width - 1 = 31 from rfl, show binary32.width = 32 from rfl,
    show binary32.p - 1 = 23 from rfl, show binary32.bexpMax + 1 = 256 from rfl,
    show binary32.bexpMax = 255 from rfl, etiny32, hm]
  have : ∀ x : Int, x + -149 - 1 = x - 150 := by intro x; omega
  simp only [this]

theorem encode32 (neg : Bool) (m : Nat) (e : Int) :
    binary32.encode neg (some (m, e)) = (if neg then 2 ^ 31 else 0) +
      (if m < 2 ^ 23 then m else (e + 150).toNat * 2 ^ 23 + (m - 2 ^ 23)) := by
  show (if m < 2 ^ 23 then (if neg then 2 ^ 31 else 0) + m
    else (if neg then 2 ^ 31 else 0) + (e + ((23 : Nat) : Int) + ((127 : Nat) : Int)).toNat * 2 ^ 23
      + (m - 2 ^ 23)) = _
  have : e + ((23 : Nat) : Int) + ((127 : Nat) : Int) = e + 150 := by omega
  rw [this]
  split <;> omega

theorem value_bound {m : Nat} {e : Int} (hm : m < 2 ^ 24) (hmax : e ≤ 104) :
    (m : Rat) * pw e < overflowLimit := by
  have a1 : (m : Rat) < ((2 ^ 24 : Nat) : Rat) := Rat.natCast_lt_natCast.2 hm
  have a2 : pw e ≤ pw 104 := pw_le hmax
  have a3 : (m : Rat) * pw e < ((2 ^ 24 : Nat) : Rat) * pw e := (Rat.mul_lt_mul_right (pw_pos _)).2 a1
  have a4 := Rat.mul_le_mul_of_nonneg_left a2 (Rat.le_of_lt (natCast_pos' (Nat.two_pow_pos 24)))
  have a5 : ((2 ^ 24 : Nat) : Rat) * pw 104 ≤ overflowLimit := by
    have e1 : ((2 ^ 24 : Nat) : Rat) * pw 104 = pw 128 := by
      rw [← pw_natCast, ← pw_add]; rfl
    rw [e1]
    have hlim : overflowLimit = ((2 ^ 54 - 1 : Nat) : Rat) * pw 970 := rfl
    have h6 : pw 128 ≤ pw 970 := pw_le (by decide)
    have h7 : (1 : Rat) ≤ ((2 ^ 54 - 1 : Nat) : Rat) := by decide +kernel
    have h8 := Rat.mul_le_mul_of_nonneg_right h7 (Rat.le_of_lt (pw_pos 970))
    rw [hlim]
    simp only [Rat.one_mul] at h8
    exact Rat.le_trans h6 h8
  grind

/-- A nonzero value of binary32, held in a double, narrows back to its own pattern. -/
theorem narrow_widen {neg : Bool} {m : Nat} {e : Int} (hm0 : 0 < m) (hm : m < 2 ^ 24)
    (he : -149 ≤ e) (hc : 2 ^ 23 ≤ m ∨ e = -149) (hmax : e ≤ 104) :
    toFloat32Bits (ofRat (if neg then -((m : Rat) * pw e) else (m : Rat) * pw e)) =
      binary32.encode neg (some (m, e)) := by
  have hv0 : 0 < (m : Rat) * pw e := Rat.mul_pos (natCast_pos' hm0) (pw_pos _)
  have hrep0 : Rep binary64 ((m : Rat) * pw e) :=
    ⟨m, e, by show m < 2 ^ 53; omega, by show (-1074 : Int) ≤ e; omega, Or.inl rfl⟩
  have hbound : Rat.abs ((m : Rat) * pw e) < overflowLimit := by
    rw [abs_of_nonneg (Rat.le_of_lt hv0)]; exact value_bound hm hmax
  generalize hq : (if neg then -((m : Rat) * pw e) else (m : Rat) * pw e) = q
  have hqabs : Rat.abs q = (m : Rat) * pw e := by
    rw [← hq]; cases neg
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact abs_of_nonneg (Rat.le_of_lt hv0)
    · simp only [↓reduceIte]; rw [abs_neg]; exact abs_of_nonneg (Rat.le_of_lt hv0)
  have hqr : Rep binary64 q := by
    rw [← hq]; cases neg
    · simpa using hrep0
    · simpa using rep_neg hrep0
  have hf := (ofRat_isFinite q).2 (by rw [hqabs]; rw [← abs_of_nonneg (Rat.le_of_lt hv0)]; exact hbound)
  have hval := ofRat_exact hqr (by rw [hqabs]; rw [← abs_of_nonneg (Rat.le_of_lt hv0)]; exact hbound)
  have hq0 : q ≠ 0 := by
    intro h0; rw [h0, abs_of_nonneg (a := 0) (by decide)] at hqabs; grind
  have hz : (ofRat q).isZero = false := by
    cases hc2 : (ofRat q).isZero
    · rfl
    · exact absurd (by rw [← hval]; exact toRat_of_isZero hc2) hq0
  have hs : (ofRat q).sign = neg := by
    have hmv := mantVal_nonneg (ofRat q)
    have hmp : 0 < (ofRat q).mant := mant_pos_of_not_zero hz
    have hmv' : 0 < ((ofRat q).mant : Rat) * pw (ofRat q).lsbExp :=
      Rat.mul_pos (natCast_pos' hmp) (pw_pos _)
    have hv2 := hval
    rw [toRat_of_finite hf] at hv2
    cases hc2 : (ofRat q).sign <;> cases hn : neg <;> simp only [hc2, hn, ↓reduceIte, Bool.false_eq_true] at hv2 hq ⊢ <;> grind
  obtain ⟨hn, hd, hnd⟩ := natAbs_div_den hq0
  have hnd' : (((ofRat q).toRat.num.natAbs : Nat) : Rat) / (ofRat q).toRat.den = (m : Rat) * pw e := by
    rw [hval, hnd, ← abs_eq_ite, hqabs]
  have hn' : 0 < (ofRat q).toRat.num.natAbs := by rw [hval]; exact hn
  have hd' : 0 < (ofRat q).toRat.den := (ofRat q).toRat.den_pos
  have hr := roundPos_exact binary32 (by decide) hn' hd' (show m < 2 ^ 24 by omega)
    (by rw [etiny32]; exact he) (by rw [etiny32]; exact hc) (by show e + ((23 : Nat) : Int) ≤ ((127 : Nat) : Int); omega) hnd'
  unfold toFloat32Bits
  simp only [isNaN_false_of_finite hf, isInf_false_of_finite hf, hz, Bool.false_eq_true, ↓reduceIte, hr, hs]

theorem byte_layout4' (v : Nat) (h : v < 2 ^ 32) (le : Bool) : unlayout (layout 4 v le) le = v :=
  byte_layout4 v h le

/-- `PyFloat_Pack4` inverts `PyFloat_Unpack4` on every binary32 pattern, in both byte orders,
signaling NaNs included. -/
def Pack4RoundTrip : Prop :=
  ∀ b, b < 2 ^ 32 → ∀ le : Bool,
    PyFloat_Pack4 (PyFloat_Unpack4 (layout 4 b le) le) le = .ok (layout 4 b le)

/-- The finite case of the round trip. -/
theorem pack4_finite {b : Nat} (hb : b < 2 ^ 32) {neg : Bool} {m : Nat} {e : Int}
    (hm : m < 2 ^ 24) (hbits : binary32.encode neg (some (m, e)) = b)
    (hview : binary32.view b = .finite neg m e) (hmax : e ≤ 104) (he : -149 ≤ e)
    (hc : 2 ^ 23 ≤ m ∨ e = -149) (le : Bool) :
    PyFloat_Pack4 (PyFloat_Unpack4 (layout 4 b le) le) le = .ok (layout 4 b le) := by
  have hU : PyFloat_Unpack4 (layout 4 b le) le = ofFloat32Bits b := by
    simp only [PyFloat_Unpack4, byte_layout4 b hb le, hview]
  rw [hU]
  have hO : ofFloat32Bits b = if m == 0 then zero neg
      else ofRat (if neg then -dyadic m e else dyadic m e) := by
    simp only [ofFloat32Bits, hview]
  rw [hO]
  by_cases hm0 : m = 0
  · subst hm0
    simp only [beq_self_eq_true, ↓reduceIte]
    have hbz : toFloat32Bits (zero neg) = b := by
      rw [← hbits, encode32]
      simp only [show (0 : Nat) < 2 ^ 23 by decide, ↓reduceIte]
      cases neg <;> decide +kernel
    have hni : (zero neg).isInf = false := isInf_false_of_finite (zero_isFinite neg)
    have hnn : (zero neg).isNaN = false := isNaN_false_of_finite (zero_isFinite neg)
    have hinf : (b % 2 ^ 31 == 0x7f800000) = false := by
      rw [← hbits, encode32]
      simp only [show (0 : Nat) < 2 ^ 23 by decide, ↓reduceIte]
      cases neg <;> decide
    simp [PyFloat_Pack4, hbz, hni, hnn, hinf]
  · have hmb : (m == 0) = false := by simpa using hm0
    simp only [hmb, Bool.false_eq_true, ↓reduceIte, dyadic_eq]
    have hw := narrow_widen (neg := neg) (by omega) hm he hc hmax
    rw [hbits] at hw
    generalize hy : ofRat (if neg then -((m : Rat) * pw e) else (m : Rat) * pw e) = y at *
    have hv0 : 0 < (m : Rat) * pw e := Rat.mul_pos (natCast_pos' (by omega)) (pw_pos _)
    have hlt : Rat.abs (if neg then -((m : Rat) * pw e) else (m : Rat) * pw e) < overflowLimit := by
      have := value_bound hm hmax
      cases neg
      · simp only [Bool.false_eq_true, ↓reduceIte]; rw [abs_of_nonneg (Rat.le_of_lt hv0)]; exact this
      · simp only [↓reduceIte]; rw [abs_neg, abs_of_nonneg (Rat.le_of_lt hv0)]; exact this
    have hfy : y.isFinite = true := by rw [← hy]; exact (ofRat_isFinite _).2 hlt
    have hni := isInf_false_of_finite hfy
    have hnn := isNaN_false_of_finite hfy
    have hinf : (b % 2 ^ 31 == 0x7f800000) = false := by
      have h1 : b % 2 ^ 31 ≠ 0x7f800000 := by
        intro hc2
        have hv := view32 b hb
        have hex : (b / 2 ^ 23) % 256 = 255 := by omega
        have hfr : b % 2 ^ 23 = 0 := by omega
        rw [hview, hex] at hv
        simp [hfr] at hv
      simpa using h1
    simp [PyFloat_Pack4, hw, hni, hnn, hinf]

theorem nan_payload {q p : Nat} (h : p < 2 ^ 22) : ((q * 2 ^ 51 + p * 2 ^ 29) / 2 ^ 29) % 2 ^ 22 = p := by
  omega

theorem nan_frac_ne {q p : Nat} (h : q * 2 ^ 22 + p ≠ 0) : q * 2 ^ 51 + p * 2 ^ 29 ≠ 0 := by
  intro h0
  obtain ⟨a, b⟩ := Nat.add_eq_zero_iff.1 h0
  have h1 : q = 0 := by
    rcases Nat.mul_eq_zero.1 a with h | h
    · exact h
    · exact absurd h (Nat.ne_of_gt (Nat.two_pow_pos 51))
  have h2 : p = 0 := by
    rcases Nat.mul_eq_zero.1 b with h | h
    · exact h
    · exact absurd h (Nat.ne_of_gt (Nat.two_pow_pos 29))
  apply h; rw [h1, h2]

theorem nan_quiet (S p : Nat) : S + 0x7ff8000000000000 + p * 2 ^ 29 =
    S + 0x7ff0000000000000 + 1 * 2 ^ 51 + p * 2 ^ 29 := by
  omega

theorem nan_word {S q p : Nat} (hS : S = 2 ^ 63 ∨ S = 0) (hq : q ≤ 1) (hp : p < 2 ^ 22) :
    ((S + 0x7ff0000000000000 + q * 2 ^ 51 + p * 2 ^ 29) / 2 ^ 52) % 2048 = 2047 ∧
    (S + 0x7ff0000000000000 + q * 2 ^ 51 + p * 2 ^ 29) % 2 ^ 52 = q * 2 ^ 51 + p * 2 ^ 29 ∧
    ((S + 0x7ff0000000000000 + q * 2 ^ 51 + p * 2 ^ 29) / 2 ^ 51) % 2 = q ∧
    (2 ^ 63 ≤ S + 0x7ff0000000000000 + q * 2 ^ 51 + p * 2 ^ 29 ↔ S = 2 ^ 63) := by
  rcases hS with h | h <;> subst h <;> refine ⟨by omega, by omega, by omega, by omega⟩

theorem pack4_inf {b : Nat} (hb : b < 2 ^ 32) (le : Bool) (he1 : (b / 2 ^ 23) % 256 = 255)
    (hf0 : b % 2 ^ 23 = 0) :
    PyFloat_Pack4 (PyFloat_Unpack4 (layout 4 b le) le) le = .ok (layout 4 b le) := by
  have hv := view32 b hb
  simp only [he1, hf0, ↓reduceIte] at hv
  have hU : PyFloat_Unpack4 (layout 4 b le) le = F64.inf (decide (2 ^ 31 ≤ b)) := by
    simp [PyFloat_Unpack4, byte_layout4 b hb le, hv, ofFloat32Bits]
  rw [hU]
  have hi := F64.inf_isInf (decide (2 ^ 31 ≤ b))
  have hn := F64.inf_isNaN (decide (2 ^ 31 ≤ b))
  have ht : toFloat32Bits (F64.inf (decide (2 ^ 31 ≤ b))) = b := by
    unfold toFloat32Bits
    simp only [hn, hi, Bool.false_eq_true, ↓reduceIte]
    have hs : (F64.inf (decide (2 ^ 31 ≤ b))).sign = decide (2 ^ 31 ≤ b) := by
      cases decide (2 ^ 31 ≤ b) <;> decide +kernel
    rw [hs]
    by_cases h : 2 ^ 31 ≤ b
    · simp only [h, decide_true, ↓reduceIte]; omega
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]; omega
  simp [PyFloat_Pack4, ht, hi, hn]

theorem pack4_nan {b : Nat} (hb : b < 2 ^ 32) (le : Bool) (he1 : (b / 2 ^ 23) % 256 = 255)
    (hf0 : ¬ b % 2 ^ 23 = 0) :
    PyFloat_Pack4 (PyFloat_Unpack4 (layout 4 b le) le) le = .ok (layout 4 b le) := by
  have hv := view32 b hb
  simp only [he1, hf0, ↓reduceIte] at hv
  generalize hS : (if 2 ^ 31 ≤ b then 2 ^ 63 else 0 : Nat) = S
  generalize hp : (b % 2 ^ 23) % 2 ^ 22 = p
  generalize hq : (b / 2 ^ 22) % 2 = q
  have hq1 : q ≤ 1 := by omega
  have hp1 : p < 2 ^ 22 := by omega
  have hfr : b % 2 ^ 23 = q * 2 ^ 22 + p := by omega
  have hS' : S = 2 ^ 63 ∨ S = 0 := by
    rw [← hS]; split
    · left; rfl
    · right; rfl
  have hY : (PyFloat_Unpack4 (layout 4 b le) le).bits =
      S + 0x7ff0000000000000 + q * 2 ^ 51 + p * 2 ^ 29 := by
    have hy0 : (ofFloat32Bits b).bits = S + 0x7ff8000000000000 + p * 2 ^ 29 := by
      have e0 : ofFloat32Bits b = F64.ofBits (((if decide (2 ^ 31 ≤ b) = true then 2 ^ 63 else 0) +
          0x7ff8000000000000) + ((b % 2 ^ 23) % 2 ^ 22) * 2 ^ 29) := by
        simp only [ofFloat32Bits, hv]
      rw [e0, hp]
      have e1 : (if decide (2 ^ 31 ≤ b) = true then 2 ^ 63 else 0) = S := by
        rw [← hS]; simp
      rw [e1]
      apply bits_ofBits_of_lt
      rcases hS' with h | h <;> omega
    have e2 : PyFloat_Unpack4 (layout 4 b le) le = if q == 0 then
        F64.ofBits ((ofFloat32Bits b).bits - 2 ^ 51) else ofFloat32Bits b := by
      simp only [PyFloat_Unpack4, byte_layout4 b hb le, hv, hq]
    rw [e2]
    by_cases hq0 : q = 0
    · simp only [hq0, beq_self_eq_true, ↓reduceIte]
      rw [bits_ofBits_of_lt (by rw [hy0]; rcases hS' with h | h <;> omega), hy0]
      omega
    · have hq0' : (q == 0) = false := by simpa using hq0
      have hq11 : q = 1 := by omega
      simp only [hq0', Bool.false_eq_true, ↓reduceIte]
      rw [hq11]
      exact hy0.trans (nan_quiet S p)
  generalize PyFloat_Unpack4 (layout 4 b le) le = u at *
  obtain ⟨w1, w2, w3, w4⟩ := nan_word hS' hq1 hp1
  have ubexp : u.bexp = 2047 := by
    show (u.bits / 2 ^ 52) % 2048 = 2047
    rw [hY]; exact w1
  have ufrac : u.frac = q * 2 ^ 51 + p * 2 ^ 29 := by
    show u.bits % 2 ^ 52 = _
    rw [hY]; exact w2
  have usign : u.sign = decide (2 ^ 31 ≤ b) := by
    show decide (2 ^ 63 ≤ u.bits) = _
    rw [hY]
    by_cases h : 2 ^ 31 ≤ b
    · simp only [h, ↓reduceIte] at hS
      simp only [h, decide_true, decide_eq_true_eq]
      exact w4.2 hS.symm
    · simp only [h, ↓reduceIte] at hS
      simp only [h, decide_false, decide_eq_false_iff_not]
      intro hc
      have := w4.1 hc
      omega
  have hpq : q * 2 ^ 22 + p ≠ 0 := by omega
  have unan : u.isNaN = true := by
    rw [isNaN_eq, ubexp, ufrac]; exact ⟨rfl, nan_frac_ne hpq⟩
  have hT : toFloat32Bits u = (if 2 ^ 31 ≤ b then 2 ^ 31 else 0) + 0x7fc00000 + p := by
    unfold toFloat32Bits
    simp only [unan, ↓reduceIte, usign, ufrac, decide_eq_true_eq]
    rw [nan_payload hp1]
  have ubit : (u.bits / 2 ^ 51) % 2 = q := by
    rw [hY]; exact w3
  have uinf : u.isInf = false := not_inf_of_nan unan
  have hT2 : (((if 2 ^ 31 ≤ b then 2 ^ 31 else 0) + 0x7fc00000 + p) % 2 ^ 31 == 0x7f800000) = false := by
    split <;> simp <;> omega
  have hfinal : (if (q == 0) && ((if 2 ^ 31 ≤ b then 2 ^ 31 else 0) + 0x7fc00000 + p) % 2 ^ 22 != 0
      then (if 2 ^ 31 ≤ b then 2 ^ 31 else 0) + 0x7fc00000 + p - 2 ^ 22
      else (if 2 ^ 31 ≤ b then 2 ^ 31 else 0) + 0x7fc00000 + p) = b := by
    by_cases hq0 : q = 0
    · have hpne : p ≠ 0 := by omega
      have c1 : (((if 2 ^ 31 ≤ b then 2 ^ 31 else 0) + 0x7fc00000 + p) % 2 ^ 22 != 0) = true := by
        split <;> simp <;> omega
      simp only [hq0, beq_self_eq_true, Bool.true_and, c1, ↓reduceIte]
      split <;> omega
    · have hq11 : q = 1 := by omega
      simp only [hq11, Nat.reduceBEq, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      split <;> omega
  unfold PyFloat_Pack4
  simp only [hT, hT2, Bool.false_and, Bool.false_eq_true, ↓reduceIte, unan, Bool.true_and, ubit]
  rw [hfinal]

theorem pack4RoundTrip_proven : Pack4RoundTrip := by
  intro b hb le
  have hv := view32 b hb
  by_cases he1 : (b / 2 ^ 23) % 256 = 255
  · by_cases hf0 : b % 2 ^ 23 = 0
    · exact pack4_inf hb le he1 hf0
    · exact pack4_nan hb le he1 hf0
  · by_cases he0 : (b / 2 ^ 23) % 256 = 0
    · simp only [he1, he0, ↓reduceIte] at hv
      have hbe : binary32.encode (decide (2 ^ 31 ≤ b)) (some (b % 2 ^ 23, -149)) = b := by
        rw [encode32]
        have : b % 2 ^ 23 < 2 ^ 23 := Nat.mod_lt _ (by decide)
        simp only [this, ↓reduceIte]
        by_cases h : 2 ^ 31 ≤ b
        · simp only [h, decide_true, ↓reduceIte]; omega
        · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]; omega
      exact pack4_finite hb (by omega) hbe hv (by decide) (by decide) (Or.inr rfl) le
    · simp only [he1, he0, ↓reduceIte] at hv
      have hbe : binary32.encode (decide (2 ^ 31 ≤ b)) (some (2 ^ 23 + b % 2 ^ 23, (((b / 2 ^ 23) % 256 : Nat) : Int) - 150)) = b := by
        rw [encode32]
        have h1 : ¬ 2 ^ 23 + b % 2 ^ 23 < 2 ^ 23 := by omega
        have h2 : ((((b / 2 ^ 23) % 256 : Nat) : Int) - 150 + 150).toNat = (b / 2 ^ 23) % 256 := by omega
        simp only [h1, ↓reduceIte, h2]
        by_cases h : 2 ^ 31 ≤ b
        · simp only [h, decide_true, ↓reduceIte]; omega
        · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]; omega
      exact pack4_finite hb (by omega) hbe hv (by omega) (by omega) (Or.inl (by omega)) le

end PyLean.Binary64
