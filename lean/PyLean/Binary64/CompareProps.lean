import PyLean.Binary64.Props4

/-!
`float_richcompare` against an int gives the exact answer, for ints of any size. The C
code never converts a large int to a double; this proof follows its branches.
-/

namespace PyLean.Binary64

open F64

/-- The comparison `op` on exact rationals. -/
def exactCompare (op : CmpOp) (a b : Rat) : Bool :=
  match op with
  | .eq => decide (a = b)
  | .ne => decide (a ≠ b)
  | .le => decide (a ≤ b)
  | .ge => decide (b ≤ a)
  | .lt => decide (a < b)
  | .gt => decide (b < a)

/-- `exactCompare` depends only on the order of its arguments. -/
theorem exactCompare_congr {a b c d : Rat} (op : CmpOp) (h1 : a < b ↔ c < d) (h2 : a = b ↔ c = d)
    (h3 : b < a ↔ d < c) : exactCompare op a b = exactCompare op c d := by
  have le1 : a ≤ b ↔ c ≤ d := by
    rw [Rat.le_iff_lt_or_eq, Rat.le_iff_lt_or_eq, h1, h2]
  have le2 : b ≤ a ↔ d ≤ c := by
    rw [← Rat.not_lt, ← Rat.not_lt, h1]
  cases op <;> simp [exactCompare, h1, h2, h3, le1, le2]

theorem le_of_finite {x y : F64} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    F64.le x y = decide (x.toRat ≤ y.toRat) := by
  unfold F64.le
  rw [lt_of_finite hx hy, eq_of_finite hx hy]
  by_cases h : x.toRat ≤ y.toRat
  · have := Rat.le_iff_lt_or_eq.1 h
    simp only [h, decide_true]
    rcases this with h1 | h1 <;> simp [h1]
  · have h1 : ¬ x.toRat < y.toRat := fun c => h (Rat.le_of_lt c)
    have h2 : ¬ x.toRat = y.toRat := fun c => h (by rw [c]; exact Rat.le_refl)
    simp [h, h1, h2]

theorem compareDoubles_finite (op : CmpOp) {i j : F64} (hi : i.isFinite = true) (hj : j.isFinite = true) :
    compareDoubles op i j = exactCompare op i.toRat j.toRat := by
  cases op
  · exact lt_of_finite hi hj
  · exact le_of_finite hi hj
  · exact eq_of_finite hi hj
  · simp only [compareDoubles, exactCompare, F64.ne, eq_of_finite hi hj]
    by_cases h : i.toRat = j.toRat <;> simp [h]
  · exact lt_of_finite hj hi
  · exact le_of_finite hj hi

theorem compareInts_exact (op : CmpOp) (a b : Int) :
    compareInts op a b = exactCompare op (a : Rat) (b : Rat) := by
  have h1 : (a : Rat) < b ↔ a < b := Rat.intCast_lt_intCast
  have h2 : (a : Rat) ≤ b ↔ a ≤ b := Rat.intCast_le_intCast
  have h3 : (b : Rat) ≤ a ↔ b ≤ a := Rat.intCast_le_intCast
  have h4 : (b : Rat) < a ↔ b < a := Rat.intCast_lt_intCast
  have h5 : (a : Rat) = b ↔ a = b := Rat.intCast_inj
  cases op <;> by_cases he : a = b <;> simp [compareInts, exactCompare, h1, h2, h3, h4, h5, he]

/-- A finite nonzero `x`, up to sign, sits in `[2 ^ (e - 1), 2 ^ e)` for `frexp`'s `e`. -/
theorem frexp_exp_bounds {x : F64} (hx : x.isFinite = true) (hz : x.isZero = false) :
    pw ((F64.frexp x).2 - 1) ≤ Rat.abs x.toRat ∧ Rat.abs x.toRat < pw (F64.frexp x).2 := by
  have hm := mant_pos_of_not_zero hz
  have he : (F64.frexp x).2 = x.lsbExp + ((Nat.log2 x.mant + 1 : Nat) : Int) := by
    simp [F64.frexp, hx, hz]
  have hab : Rat.abs x.toRat = (x.mant : Rat) * pw x.lsbExp := by
    rw [toRat_of_finite hx]
    split
    · rw [abs_neg, abs_of_nonneg (mantVal_nonneg x)]
    · rw [abs_of_nonneg (mantVal_nonneg x)]
  have h1 : ((2 ^ x.mant.log2 : Nat) : Rat) ≤ x.mant :=
    Rat.natCast_le_natCast.2 (Nat.log2_self_le (by omega))
  have h2 : (x.mant : Rat) < ((2 ^ (x.mant.log2 + 1) : Nat) : Rat) :=
    Rat.natCast_lt_natCast.2 Nat.lt_log2_self
  rw [← pw_natCast] at h1 h2
  have hp := pw_pos x.lsbExp
  rw [hab, he]
  constructor
  · have e : x.lsbExp + ((x.mant.log2 + 1 : Nat) : Int) - 1 = (x.mant.log2 : Int) + x.lsbExp := by omega
    rw [e, pw_add]
    exact Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hp)
  · have e : x.lsbExp + ((x.mant.log2 + 1 : Nat) : Int) = ((x.mant.log2 + 1 : Nat) : Int) + x.lsbExp := by omega
    rw [e, pw_add]
    exact (Rat.mul_lt_mul_right hp).2 h2

/-- A nonzero int sits in `[2 ^ (nbits - 1), 2 ^ nbits)`. -/
theorem numBits_bounds {n : Int} (h : n ≠ 0) :
    pw ((numBits n : Int) - 1) ≤ Rat.abs (n : Rat) ∧ Rat.abs (n : Rat) < pw (numBits n : Int) := by
  have hm : n.natAbs ≠ 0 := by omega
  have e : numBits n = n.natAbs.log2 + 1 := by simp [numBits, bitLength, hm]
  rw [abs_intCast, e]
  constructor
  · have : ((n.natAbs.log2 + 1 : Nat) : Int) - 1 = (n.natAbs.log2 : Int) := by omega
    rw [this, pw_natCast]
    exact Rat.natCast_le_natCast.2 (Nat.log2_self_le hm)
  · rw [pw_natCast]
    exact Rat.natCast_lt_natCast.2 Nat.lt_log2_self

/-- A nonzero rational on the `2 ^ -1074` grid does not round to zero. -/
theorem ofRat_ne_zero_of_grid {q : Rat} {Z : Int} (hq : q = (Z : Rat) * pw (-1074)) (hZ : Z ≠ 0) :
    (ofRat q).isZero = false := by
  cases hz : (ofRat q).isZero
  · rfl
  · exfalso
    have hf := isFinite_of_isZero hz
    have ht := toRat_of_isZero hz
    have hp := pw_pos (-1074)
    have hrep1 : Rep binary64 (pw (-1074)) := ⟨1, -1074, by decide, by decide, Or.inl (by simp)⟩
    have hrep2 : Rep binary64 (-pw (-1074)) := rep_neg hrep1
    have n1 := ofRat_nearest_rep q hf hrep1
    have n2 := ofRat_nearest_rep q hf hrep2
    rw [ht] at n1 n2
    have hZr : (1 : Rat) ≤ (Z : Rat) ∨ (Z : Rat) ≤ -1 := by
      rcases Int.lt_or_gt_of_ne hZ with h | h
      · right
        have h2 : Z ≤ -1 := by omega
        have := Rat.intCast_le_intCast.2 h2
        simpa using this
      · left
        have h2 : 1 ≤ Z := by omega
        have := Rat.intCast_le_intCast.2 h2
        simpa using this
    rcases hZr with h | h
    · have hge : pw (-1074) ≤ q := by
        rw [hq]
        have := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hp)
        simpa using this
      rw [abs_of_nonneg (a := q - 0) (by grind), abs_of_nonneg (a := q - pw (-1074)) (by grind)] at n1
      grind
    · have hle : q ≤ -pw (-1074) := by
        rw [hq]
        have := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hp)
        simpa [Rat.neg_mul] using this
      rw [abs_of_nonpos (a := q - 0) (by grind), abs_of_nonpos (a := q - -pw (-1074)) (by grind)] at n2
      grind

/-- The value of a finite float is on the `2 ^ -1074` grid. -/
theorem toRat_grid (x : F64) (hx : x.isFinite = true) :
    ∃ Z : Int, x.toRat = (Z : Rat) * pw (-1074) := by
  have he := lsbExp_ge x
  have e1 : pw x.lsbExp = ((2 ^ (x.lsbExp + 1074).toNat : Nat) : Rat) * pw (-1074) := by
    rw [← pw_natCast, ← pw_add]; congr 1; omega
  rw [toRat_of_finite hx, e1]
  split
  · refine ⟨-((x.mant * 2 ^ (x.lsbExp + 1074).toNat : Nat) : Int), ?_⟩
    rw [Rat.intCast_neg, Rat.intCast_natCast, Rat.natCast_mul, Rat.neg_mul, Rat.mul_assoc]
  · refine ⟨((x.mant * 2 ^ (x.lsbExp + 1074).toNat : Nat) : Int), ?_⟩
    rw [Rat.intCast_natCast, Rat.natCast_mul, Rat.mul_assoc]

/-- An int is on the grid. -/
theorem int_grid (t : Int) : ∃ Z : Int, (t : Rat) = (Z : Rat) * pw (-1074) := by
  refine ⟨t * ((2 ^ 1074 : Nat) : Int), ?_⟩
  rw [Rat.intCast_mul, Rat.intCast_natCast, ← pw_natCast, Rat.mul_assoc, ← pw_add]
  simp [pw_zero]

/-- `trunc` keeps the value exactly as `truncInt`. -/
theorem trunc_value {x : F64} (hx : x.isFinite = true) (hz : x.isZero = false) :
    (F64.trunc x).isFinite = true ∧ (F64.trunc x).toRat = x.truncInt := by
  have hn := isNaN_false_of_finite hx
  have e : F64.trunc x = ofIntS x.sign x.truncInt := by simp [F64.trunc, hn, hx, hz]
  rw [e]
  apply ofIntS_value _ hx hz
  rcases int_or_small hx with ⟨t, ht⟩ | h
  · left; rw [truncInt_of_int ht]; exact ht
  · right
    unfold truncInt
    split
    · exact ceilInt_bound h
    · exact floorInt_bound h

/-- Comparing a finite float with an int gives the exact answer, for ints of any size. A
NaN compares false except for `!=`, and an infinity compares like its sign. -/
def FloatIntCompareExact : Prop :=
  ∀ (x : F64) (n : Int) (op : CmpOp),
    (x.isFinite = true → float_richcompare x (.int n) op = some (exactCompare op x.toRat n)) ∧
    (x.isNaN = true → float_richcompare x (.int n) op = some (op == .ne)) ∧
    (x.isInf = true → float_richcompare x (.int n) op =
      some (exactCompare op (if x.sign then -1 else 1) 0))

theorem sign_facts_v {x : F64} (hx : x.isFinite = true) :
    let vs : Int := if F64.eq x d0 then 0 else if F64.lt x d0 then -1 else 1
    (vs = 0 ∧ x.toRat = 0) ∨ (vs = -1 ∧ x.toRat < 0) ∨ (vs = 1 ∧ 0 < x.toRat) := by
  simp only [eq_of_finite hx d0_isFinite, lt_of_finite hx d0_isFinite, d0_toRat, decide_eq_true_eq]
  by_cases h0 : x.toRat = 0
  · simp [h0]
  · by_cases h1 : x.toRat < 0
    · simp [h0, h1]
    · have : 0 < x.toRat := by grind
      simp [h0, h1, this]

theorem sign_facts_w (n : Int) :
    (n.sign = 0 ∧ (n : Rat) = 0) ∨ (n.sign = -1 ∧ (n : Rat) < 0) ∨ (n.sign = 1 ∧ 0 < (n : Rat)) := by
  have h1 : (n : Rat) < 0 ↔ n < 0 := Rat.intCast_lt_intCast
  have h2 : 0 < (n : Rat) ↔ 0 < n := Rat.intCast_lt_intCast
  rcases Int.lt_trichotomy n 0 with h | h | h
  · right; left; exact ⟨Int.sign_eq_neg_one_of_neg h, h1.2 h⟩
  · left; subst h; simp
  · right; right; exact ⟨Int.sign_eq_one_of_pos h, h2.2 h⟩

theorem small_exact (s : Int) (h : s = 0 ∨ s = 1 ∨ s = -1 ∨ s = 2 ∨ s = -2) :
    (ofInt s).isFinite = true ∧ (ofInt s).toRat = s :=
  ofInt_small (by rcases h with rfl | rfl | rfl | rfl | rfl <;> decide)

theorem qlt_le {a b c : Rat} (h1 : a < b) (h2 : b ≤ c) : a < c := by grind

theorem exactCompare_lt {a b c d : Rat} (op : CmpOp) (h1 : a < b) (h2 : c < d) :
    exactCompare op a b = exactCompare op c d := by
  apply exactCompare_congr
  · exact ⟨fun _ => h2, fun _ => h1⟩
  · constructor <;> intro h <;> grind
  · constructor <;> intro h <;> grind

theorem exactCompare_gt {a b c d : Rat} (op : CmpOp) (h1 : b < a) (h2 : d < c) :
    exactCompare op a b = exactCompare op c d := by
  apply exactCompare_congr
  · constructor <;> intro h <;> grind
  · constructor <;> intro h <;> grind
  · exact ⟨fun _ => h2, fun _ => h1⟩

theorem limit_le_pw1024 : overflowLimit ≤ pw 1024 := by
  have hlim : overflowLimit = 18014398509481983 * pw 970 := by
    unfold overflowLimit; congr 1
  have h53 : pw 54 = 18014398509481984 := by
    have := pw_natCast 54
    simpa using this
  have e : pw 1024 = 18014398509481984 * pw 970 := by
    rw [show (1024 : Int) = 970 + 54 from rfl, pw_add, h53, Rat.mul_comm]
  have hL := pw_pos 970
  rw [hlim, e]; grind

theorem natAbs_lt_numBits (w : Int) : w.natAbs < 2 ^ numBits w := by
  by_cases h : w.natAbs = 0
  · simp [numBits, bitLength, h]
  · simp only [numBits, bitLength, h, ↓reduceIte]
    exact Nat.lt_log2_self

theorem abs_cases {a : Rat} : (0 ≤ a ∧ Rat.abs a = a) ∨ (a < 0 ∧ Rat.abs a = -a) := by
  by_cases h : 0 ≤ a
  · left; exact ⟨h, abs_of_nonneg h⟩
  · right; exact ⟨by grind, abs_of_nonpos (by grind)⟩

/-- The truncated integer of a finite float: below it for positive values, above it for
negative ones, and at it for integers. -/
theorem trunc_bounds {x : F64} (hx : x.isFinite = true) :
    (0 < x.toRat → (x.truncInt : Rat) ≤ x.toRat ∧ x.toRat < (x.truncInt : Rat) + 1) ∧
    (x.toRat < 0 → x.toRat ≤ (x.truncInt : Rat) ∧ (x.truncInt : Rat) - 1 < x.toRat) := by
  have hv := mantVal_nonneg x
  constructor
  · intro hp
    have hs : x.sign = false := by
      cases hc : x.sign
      · rfl
      · rw [toRat_of_finite hx, hc] at hp
        simp only [↓reduceIte] at hp
        grind
    have h1 := Rat.floor_le x.toRat
    have h2 := Rat.lt_floor_add_one x.toRat
    rw [Rat.intCast_add] at h2
    have e1 : ((1 : Int) : Rat) = 1 := rfl
    rw [e1] at h2
    have : x.truncInt = x.toRat.floor := by simp [F64.truncInt, F64.floorInt, hs]
    rw [this]
    exact ⟨h1, h2⟩
  · intro hn
    have hs : x.sign = true := by
      cases hc : x.sign
      · rw [toRat_of_finite hx, hc] at hn
        simp only [Bool.false_eq_true, ↓reduceIte] at hn
        grind
      · rfl
    have h1 := Rat.floor_le (-x.toRat)
    have h2 := Rat.lt_floor_add_one (-x.toRat)
    rw [Rat.intCast_add] at h2
    have e1 : ((1 : Int) : Rat) = 1 := rfl
    rw [e1] at h2
    have e : x.ceilInt = -((-x.toRat).floor) := Rat.ceil_eq_neg_floor_neg _
    have hc : ((x.truncInt : Int) : Rat) = -(((-x.toRat).floor : Int) : Rat) := by
      have : x.truncInt = x.ceilInt := by simp [F64.truncInt, hs]
      rw [this, e]; rfl
    rw [hc]
    constructor <;> grind

/-- `modf`'s fractional part vanishes exactly at an integer value. -/
theorem frac_isZero {x : F64} (hx : x.isFinite = true) (hz : x.isZero = false) :
    (F64.sub x (F64.trunc x)).isZero = decide (x.toRat = (x.truncInt : Rat)) := by
  obtain ⟨i1, i2⟩ := trunc_value hx hz
  have hn : (F64.trunc x).neg.isFinite = true := by rw [neg_isFinite]; exact i1
  unfold F64.sub
  rw [add_of_finite hx hn, toRat_neg, i2]
  by_cases h : x.toRat + -(x.truncInt : Rat) = 0
  · have h2 : x.toRat = (x.truncInt : Rat) := by grind
    rw [if_pos h, zero_isZero]; simp [h2]
  · have h2 : ¬ x.toRat = (x.truncInt : Rat) := by intro c; apply h; rw [c]; grind
    rw [if_neg h]
    have hd : decide (x.toRat = (x.truncInt : Rat)) = false := by simp [h2]
    rw [hd]
    obtain ⟨Z1, h3⟩ := toRat_grid x hx
    obtain ⟨Z2, h4⟩ := int_grid x.truncInt
    apply ofRat_ne_zero_of_grid (Z := Z1 - Z2)
    · rw [Rat.intCast_sub, h3, h4]
      generalize pw (-1074) = p
      generalize (Z1 : Rat) = a
      generalize (Z2 : Rat) = b
      grind
    · intro hZ
      apply h
      have : Z1 = Z2 := by omega
      rw [h3, h4, this]; grind

/-- The branch where the two signs differ: the signs alone decide. -/
theorem compare_signs {x : F64} {vs : Int} {w : Int} (op : CmpOp)
    (hv : (vs = 0 ∧ x.toRat = 0) ∨ (vs = -1 ∧ x.toRat < 0) ∨ (vs = 1 ∧ 0 < x.toRat))
    (hw : (w.sign = 0 ∧ (w : Rat) = 0) ∨ (w.sign = -1 ∧ (w : Rat) < 0) ∨ (w.sign = 1 ∧ 0 < (w : Rat)))
    (hne : vs ≠ w.sign) :
    compareDoubles op (ofInt vs) (ofInt w.sign) = exactCompare op x.toRat (w : Rat) := by
  have a := small_exact vs (by omega)
  have b := small_exact w.sign (by omega)
  rw [compareDoubles_finite op a.1 b.1, a.2, b.2]
  rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hw with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rw [h1, h3] <;> first
    | (exfalso; omega)
    | exact exactCompare_lt op (by decide +kernel) (by grind)
    | exact exactCompare_gt op (by decide +kernel) (by grind)

/-- The branch where the int has more than 1024 bits: it dominates. -/
theorem compare_huge {x : F64} {vs : Int} {w : Int} (op : CmpOp) (hx : x.isFinite = true)
    (hv : (vs = 0 ∧ x.toRat = 0) ∨ (vs = -1 ∧ x.toRat < 0) ∨ (vs = 1 ∧ 0 < x.toRat))
    (hw : (w.sign = 0 ∧ (w : Rat) = 0) ∨ (w.sign = -1 ∧ (w : Rat) < 0) ∨ (w.sign = 1 ∧ 0 < (w : Rat)))
    (heq : vs = w.sign) (hbig : 1024 < numBits w) :
    compareDoubles op (ofInt vs) (ofInt (w.sign * 2)) = exactCompare op x.toRat (w : Rat) := by
  have w0 : w ≠ 0 := by
    intro h; subst h; simp [numBits, bitLength] at hbig
  obtain ⟨n1, _⟩ := numBits_bounds w0
  have h1024 : pw 1024 ≤ Rat.abs (w : Rat) := Rat.le_trans (pw_le (by omega)) n1
  have hxa := qlt_le (abs_toRat_lt hx) limit_le_pw1024
  have c1 : ((1 : Int) : Rat) = 1 := rfl
  have c3 : ((-1 : Int) : Rat) = -1 := rfl
  have c4 : ((2 : Int) : Rat) = 2 := rfl
  have c5 : ((-2 : Int) : Rat) = -2 := rfl
  rcases hw with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exfalso; exact w0 (Int.sign_eq_zero_iff_zero.1 h3)
  · have hv1 : vs = -1 := by omega
    have a := small_exact vs (by omega)
    have b := small_exact (w.sign * 2) (by omega)
    rw [compareDoubles_finite op a.1 b.1, a.2, b.2, h3, hv1]
    have hvn : x.toRat < 0 := by rcases hv with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> first | omega | exact h
    rw [abs_of_nonpos (Rat.le_of_lt hvn)] at hxa
    rw [abs_of_nonpos (Rat.le_of_lt h4)] at h1024
    exact exactCompare_gt op (by decide +kernel) (by grind)
  · have hv1 : vs = 1 := by omega
    have a := small_exact vs (by omega)
    have b := small_exact (w.sign * 2) (by omega)
    rw [compareDoubles_finite op a.1 b.1, a.2, b.2, h3, hv1]
    have hvp : 0 < x.toRat := by rcases hv with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ <;> first | omega | exact h
    rw [abs_of_nonneg (Rat.le_of_lt hvp)] at hxa
    rw [abs_of_nonneg (Rat.le_of_lt h4)] at h1024
    exact exactCompare_lt op (by decide +kernel) (by grind)

/-- Same number of bits: compare the integer part, with the operator adjusted for a
fractional part, floatobject.c:466-511. -/
theorem compare_same_bits {x : F64} {w : Int} (op : CmpOp) (hx : x.isFinite = true)
    (hz : x.isZero = false) (vs : Int)
    (hv : (vs = -1 ∧ x.toRat < 0) ∨ (vs = 1 ∧ 0 < x.toRat)) :
    (let intpart := F64.trunc x
     let fracpart := F64.sub x intpart
     let op' : Option CmpOp :=
       if !fracpart.isZero then
         match op with
         | .eq => none
         | .ne => none
         | .lt | .le => some (if 0 < vs then .lt else .le)
         | .gt | .ge => some (if 0 < vs then .ge else .gt)
       else some op
     match op' with
     | none => op == .ne
     | some o => compareInts o intpart.truncInt w) = exactCompare op x.toRat (w : Rat) := by
  obtain ⟨i1, i2⟩ := trunc_value hx hz
  have hfr := frac_isZero hx hz
  have ht : (F64.trunc x).truncInt = x.truncInt := truncInt_of_int i2
  simp only []
  rw [hfr, ht]
  obtain ⟨tb1, tb2⟩ := trunc_bounds hx
  generalize x.truncInt = t at *
  by_cases hint : x.toRat = (t : Rat)
  · simp only [hint, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact compareInts_exact op t w
  · simp only [hint, decide_false, Bool.not_false, ↓reduceIte]
    have hi1 : ∀ a b : Int, a < b → (a : Rat) + 1 ≤ (b : Rat) := by
      intro a b h
      have := Rat.intCast_le_intCast.2 (show a + 1 ≤ b from h)
      rw [Rat.intCast_add] at this
      exact this
    have hne : x.toRat ≠ (w : Rat) := by
      intro he
      rcases hv with ⟨_, h⟩ | ⟨_, h⟩
      · obtain ⟨b1, b2⟩ := tb2 h
        by_cases hc : t = w
        · subst hc; exact hint he
        · rcases Int.lt_or_gt_of_ne hc with c | c
          · have := hi1 _ _ c; grind
          · have := hi1 _ _ c; grind
      · obtain ⟨b1, b2⟩ := tb1 h
        by_cases hc : t = w
        · subst hc; exact hint he
        · rcases Int.lt_or_gt_of_ne hc with c | c
          · have := hi1 _ _ c; grind
          · have := hi1 _ _ c; grind
    have l1 : ¬ x.toRat = (w : Rat) := hne
    rcases hv with ⟨hs, h⟩ | ⟨hs, h⟩
    · obtain ⟨b1, b2⟩ := tb2 h
      have b1' : x.toRat < (t : Rat) := by
        rcases Rat.le_iff_lt_or_eq.1 b1 with h5 | h5
        · exact h5
        · exact absurd h5 hint
      have hnp : ¬ (0 : Int) < vs := by omega
      have k1 : t ≤ w ↔ x.toRat < (w : Rat) := by
        constructor
        · intro c
          have := Rat.intCast_le_intCast.2 c
          grind
        · intro c
          apply Int.not_lt.1
          intro c2
          have := hi1 _ _ c2
          grind
      have k2 : w < t ↔ (w : Rat) < x.toRat := by
        constructor
        · intro c
          have := hi1 _ _ c
          grind
        · intro c
          apply Int.not_le.1
          intro c2
          have := Rat.intCast_le_intCast.2 c2
          grind
      cases op <;> simp [hnp, compareInts, exactCompare, l1, k1, k2, Rat.le_iff_lt_or_eq, Rat.lt_irrefl] <;> grind
    · obtain ⟨b1, b2⟩ := tb1 h
      have b1' : (t : Rat) < x.toRat := by
        rcases Rat.le_iff_lt_or_eq.1 b1 with h5 | h5
        · exact h5
        · exact absurd h5.symm hint
      have hnp : (0 : Int) < vs := by omega
      have k1 : t < w ↔ x.toRat < (w : Rat) := by
        constructor
        · intro c
          have := hi1 _ _ c
          grind
        · intro c
          apply Int.not_le.1
          intro c2
          have := Rat.intCast_le_intCast.2 c2
          grind
      have k2 : w ≤ t ↔ (w : Rat) < x.toRat := by
        constructor
        · intro c
          have := Rat.intCast_le_intCast.2 c
          grind
        · intro c
          apply Int.not_lt.1
          intro c2
          have := hi1 _ _ c2
          grind
      cases op <;> simp [hnp, compareInts, exactCompare, l1, k1, k2, Rat.le_iff_lt_or_eq] <;> grind

theorem compareFiniteInt_exact {x : F64} (hx : x.isFinite = true) (w : Int) (op : CmpOp) :
    compareFiniteInt op x w = exactCompare op x.toRat (w : Rat) := by
  have hv := sign_facts_v hx
  have hw := sign_facts_w w
  unfold compareFiniteInt
  simp only [] at hv ⊢
  generalize (if F64.eq x d0 then (0 : Int) else if F64.lt x d0 then -1 else 1) = vs at *
  by_cases hne : (vs != w.sign) = true
  · simp only [hne, ↓reduceIte]
    exact compare_signs op hv hw (by simpa using hne)
  · have heq : vs = w.sign := by simpa using hne
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    by_cases hbig : 1024 < numBits w
    · simp only [hbig, ↓reduceIte]
      exact compare_huge op hx hv hw heq hbig
    · simp only [hbig, ↓reduceIte]
      by_cases hsmall : numBits w ≤ 48
      · simp only [hsmall, ↓reduceIte]
        have hlt : w.natAbs < 2 ^ 53 := Nat.lt_of_lt_of_le (natAbs_lt_numBits w)
          (Nat.pow_le_pow_right (by omega) (by omega))
        obtain ⟨f1, f2⟩ := ofInt_small hlt
        rw [compareDoubles_finite op hx f1, f2]
      · simp only [hsmall, ↓reduceIte]
        have w0 : w ≠ 0 := by
          intro h; subst h; simp [numBits, bitLength] at hsmall
        obtain ⟨n1, n2⟩ := numBits_bounds w0
        have hvz : x.toRat ≠ 0 := by
          rcases hv with ⟨h1, _⟩ | ⟨_, h⟩ | ⟨_, h⟩
          · have : w.sign ≠ 0 := by
              intro hc; exact w0 (Int.sign_eq_zero_iff_zero.1 hc)
            omega
          · intro h0; rw [h0] at h; exact absurd h (by decide)
          · exact Rat.ne_of_gt h
        have hz : x.isZero = false := by
          cases hc : x.isZero
          · rfl
          · exact absurd (toRat_of_isZero hc) hvz
        obtain ⟨e1, e2⟩ := frexp_exp_bounds hx hz
        have hd0 := d0_isFinite
        by_cases hlt : (F64.frexp x).2 < numBits w
        · simp only [hlt, ↓reduceIte]
          rw [compareDoubles_finite op hd0 hx, d0_toRat]
          have hab : Rat.abs x.toRat < Rat.abs (w : Rat) :=
            qlt_le e2 (Rat.le_trans (pw_le (by omega)) n1)
          rcases hv with ⟨_, h1⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact absurd h1 hvz
          · have h4 : (w : Rat) < 0 := by
              rcases hw with ⟨h3, _⟩ | ⟨_, h3⟩ | ⟨h3, _⟩ <;> first | omega | exact h3
            rw [abs_of_nonpos (Rat.le_of_lt h2), abs_of_nonpos (Rat.le_of_lt h4)] at hab
            exact exactCompare_gt op h2 (by grind)
          · have h4 : 0 < (w : Rat) := by
              rcases hw with ⟨h3, _⟩ | ⟨h3, _⟩ | ⟨_, h3⟩ <;> first | omega | exact h3
            rw [abs_of_nonneg (Rat.le_of_lt h2), abs_of_nonneg (Rat.le_of_lt h4)] at hab
            exact exactCompare_lt op h2 (by grind)
        · simp only [hlt, ↓reduceIte]
          by_cases hgt : (numBits w : Int) < (F64.frexp x).2
          · simp only [hgt, ↓reduceIte]
            rw [compareDoubles_finite op hx hd0, d0_toRat]
            have hab : Rat.abs (w : Rat) < Rat.abs x.toRat :=
              qlt_le n2 (Rat.le_trans (pw_le (by omega)) e1)
            rcases hv with ⟨_, h1⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact absurd h1 hvz
            · have h4 : (w : Rat) < 0 := by
                rcases hw with ⟨h3, _⟩ | ⟨_, h3⟩ | ⟨h3, _⟩ <;> first | omega | exact h3
              rw [abs_of_nonpos (Rat.le_of_lt h2), abs_of_nonpos (Rat.le_of_lt h4)] at hab
              exact exactCompare_lt op h2 (by grind)
            · have h4 : 0 < (w : Rat) := by
                rcases hw with ⟨h3, _⟩ | ⟨h3, _⟩ | ⟨_, h3⟩ <;> first | omega | exact h3
              rw [abs_of_nonneg (Rat.le_of_lt h2), abs_of_nonneg (Rat.le_of_lt h4)] at hab
              exact exactCompare_gt op h2 (by grind)
          · simp only [hgt, ↓reduceIte]
            have hv' : (vs = -1 ∧ x.toRat < 0) ∨ (vs = 1 ∧ 0 < x.toRat) := by
              rcases hv with ⟨_, h⟩ | h | h
              · exact absurd h hvz
              · exact Or.inl h
              · exact Or.inr h
            exact compare_same_bits op hx hz vs hv'

theorem floatIntCompareExact_proven : FloatIntCompareExact := by
  intro x n op
  refine ⟨fun hx => ?_, fun hn => ?_, fun hi => ?_⟩
  · simp only [float_richcompare, hx, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [compareFiniteInt_exact hx]
  · have hf : x.isFinite = false := by
      cases hc : x.isFinite
      · rfl
      · rw [isNaN_false_of_finite hc] at hn; cases hn
    simp only [float_richcompare, hf, Bool.not_false, ↓reduceIte]
    cases op <;> simp [compareDoubles, F64.ne, F64.eq, F64.lt, F64.gt, F64.ge, F64.le, hn]
  · have hf := not_finite_of_inf hi
    simp only [float_richcompare, hf, Bool.not_false, ↓reduceIte]
    rw [eq_inf_of_isInf hi]
    have hs : (F64.inf x.sign).sign = x.sign := by cases hs : x.sign <;> decide +kernel
    rw [hs]
    cases x.sign <;> cases op <;> decide +kernel

end PyLean.Binary64
