import PyLean.Binary64.Model

/-!
Correctness of `roundPos`, the one rounding step every `F64` operation goes through.

The statements are `Fmt`-generic, so they serve binary32 and binary16 as well. With
`e = roundExp f n d` and `Q = v / 2 ^ e`, the rounded integer `q'` is a nearest
integer to `Q` and is even on a tie, and `e` is the right scale for `v`. From these,
`rounded_nearest` says that `q' * 2 ^ e` is at least as close to `v` as every number
of the format.
-/

namespace PyLean.Binary64

/-- `2 ^ e` as a rational. -/
abbrev pw (e : Int) : Rat := (2 : Rat) ^ e

theorem pw_pos (e : Int) : 0 < pw e := Rat.zpow_pos (by decide)

theorem pw_ne (e : Int) : pw e ≠ 0 := Rat.ne_of_gt (pw_pos e)

theorem pw_add (a b : Int) : pw (a + b) = pw a * pw b :=
  Rat.zpow_add (by decide) a b

theorem pw_zero : pw 0 = 1 := by simp [pw]

theorem pw_one : pw 1 = 2 := by simp [pw]

theorem pw_natCast (k : Nat) : pw (k : Int) = ((2 ^ k : Nat) : Rat) := by
  simp [pw, Rat.zpow_natCast]

theorem pw_neg (k : Int) : pw (-k) = (pw k)⁻¹ := Rat.zpow_neg 2 k

theorem pw_sub (a b : Int) : pw (a - b) = pw a * (pw b)⁻¹ := by
  rw [Int.sub_eq_add_neg, pw_add, pw_neg]

theorem pw_mul_inv (a : Int) : pw a * (pw a)⁻¹ = 1 := Rat.mul_inv_cancel _ (pw_ne a)

theorem pw_succ (k : Int) : pw (k + 1) = 2 * pw k := by
  rw [pw_add, pw_one, Rat.mul_comm]

/-- `2 ^ a ≤ 2 ^ b` when `a ≤ b`. -/
theorem pw_le {a b : Int} (h : a ≤ b) : pw a ≤ pw b := by
  obtain ⟨k, hk⟩ := Int.le.dest h
  rw [← hk, pw_add, pw_natCast]
  have h1 : (1 : Rat) ≤ ((2 ^ k : Nat) : Rat) := by
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    exact_mod_cast this
  have := Rat.mul_le_mul_of_nonneg_left h1 (Rat.le_of_lt (pw_pos a))
  simpa using this

theorem pw_lt {a b : Int} (h : a < b) : pw a < pw b := by
  have h1 : pw (a + 1) ≤ pw b := pw_le (by omega)
  rw [pw_succ] at h1
  have := pw_pos a
  grind

/-- `pw e` as a ratio of two naturals, whichever way `e` points. -/
theorem pw_eq_div (e : Int) :
    pw e = ((2 ^ e.toNat : Nat) : Rat) / ((2 ^ (-e).toNat : Nat) : Rat) := by
  rcases Int.le_total 0 e with h | h
  · have h1 : (e.toNat : Int) = e := Int.toNat_of_nonneg h
    have h2 : (-e).toNat = 0 := by omega
    have h3 : (1 : Rat)⁻¹ = 1 := Rat.inv_eq_of_mul_eq_one (by simp)
    rw [h2, ← pw_natCast, h1]
    simp [Rat.div_def, h3]
  · obtain ⟨k, rfl⟩ : ∃ k : Nat, e = -(k : Int) := ⟨(-e).toNat, by omega⟩
    have h1 : (-(-(k : Int))).toNat = k := by omega
    have h2 : (-(k : Int)).toNat = 0 := by omega
    rw [h1, h2, pw_neg, pw_natCast]; simp [Rat.div_def]

theorem natCast_pos' {n : Nat} (h : 0 < n) : 0 < (n : Rat) := Rat.natCast_pos.2 h

/-- The comparison `floorLog2Q` makes, cross-multiplied, is `2 ^ k ≤ n / d`. -/
theorem cross_le {n d : Nat} (hd : 0 < d) (k : Int) :
    d * 2 ^ k.toNat ≤ n * 2 ^ (-k).toNat ↔ pw k ≤ (n : Rat) / d := by
  have hA : 0 < ((2 ^ k.toNat : Nat) : Rat) := natCast_pos' (Nat.two_pow_pos _)
  have hB : 0 < ((2 ^ (-k).toNat : Nat) : Rat) := natCast_pos' (Nat.two_pow_pos _)
  have hD : 0 < (d : Rat) := natCast_pos' hd
  rw [pw_eq_div, ← Rat.natCast_le_natCast, Rat.natCast_mul, Rat.natCast_mul]
  generalize ((2 ^ k.toNat : Nat) : Rat) = a at *
  generalize ((2 ^ (-k).toNat : Nat) : Rat) = b at *
  generalize (d : Rat) = D at *
  generalize (n : Rat) = N at *
  have e1 : a / b = a * b⁻¹ := rfl
  have e2 : N / D = N * D⁻¹ := rfl
  constructor
  · intro h
    have h1 : a / b * (b * D) ≤ N / D * (b * D) := by
      have e3 : a / b * (b * D) = D * a := by
        rw [e1]; grind
      have e4 : N / D * (b * D) = N * b := by
        rw [e2]; grind
      rw [e3, e4]; exact h
    exact Rat.le_of_mul_le_mul_right h1 (Rat.mul_pos hB hD)
  · intro h
    have h1 := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt (Rat.mul_pos hB hD))
    have e3 : a / b * (b * D) = D * a := by
      rw [e1]; grind
    have e4 : N / D * (b * D) = N * b := by
      rw [e2]; grind
    rwa [e3, e4] at h1

/-- `floorLog2Q` is `⌊log₂ (n / d)⌋`. -/
theorem floorLog2Q_spec {n d : Nat} (hn : 0 < n) (hd : 0 < d) :
    pw (floorLog2Q n d) ≤ (n : Rat) / d ∧ (n : Rat) / d < pw (floorLog2Q n d + 1) := by
  have hD : 0 < (d : Rat) := natCast_pos' hd
  have ha1 : pw (n.log2 : Int) ≤ (n : Rat) := by
    rw [pw_natCast]; exact Rat.natCast_le_natCast.2 (Nat.log2_self_le (by omega))
  have ha2 : (n : Rat) < pw ((n.log2 : Int) + 1) := by
    have : pw ((n.log2 : Int) + 1) = ((2 ^ (n.log2 + 1) : Nat) : Rat) := by
      rw [← pw_natCast]; simp
    rw [this]; exact Rat.natCast_lt_natCast.2 Nat.lt_log2_self
  have hb1 : pw (d.log2 : Int) ≤ (d : Rat) := by
    rw [pw_natCast]; exact Rat.natCast_le_natCast.2 (Nat.log2_self_le (by omega))
  have hb2 : (d : Rat) < pw ((d.log2 : Int) + 1) := by
    have : pw ((d.log2 : Int) + 1) = ((2 ^ (d.log2 + 1) : Nat) : Rat) := by
      rw [← pw_natCast]; simp
    rw [this]; exact Rat.natCast_lt_natCast.2 Nat.lt_log2_self
  generalize ha : (n.log2 : Int) = a at *
  generalize hb : (d.log2 : Int) = b at *
  have upper : (n : Rat) / d < pw (a - b + 1) := by
    rw [Rat.div_lt_iff hD]
    have e : pw (a + 1) = pw (a - b + 1) * pw b := by
      rw [← pw_add]; congr 1; omega
    have h2 : pw (a - b + 1) * pw b ≤ pw (a - b + 1) * d :=
      Rat.mul_le_mul_of_nonneg_left hb1 (Rat.le_of_lt (pw_pos _))
    rw [e] at ha2
    grind
  have lower : pw (a - b - 1) ≤ (n : Rat) / d := by
    apply Rat.le_of_lt
    rw [Rat.lt_div_iff hD]
    have e : pw a = pw (a - b - 1) * pw (b + 1) := by
      rw [← pw_add]; congr 1; omega
    have h2 : pw (a - b - 1) * d < pw (a - b - 1) * pw (b + 1) :=
      (Rat.mul_lt_mul_left (pw_pos _)).2 hb2
    rw [← e] at h2
    grind
  unfold floorLog2Q
  simp only [ha, hb]
  split
  · rename_i h
    exact ⟨(cross_le hd _).1 h, upper⟩
  · rename_i h
    have h' : (n : Rat) / d < pw (a - b) := by
      have := fun x => (cross_le (n := n) hd (a - b)).2 x
      exact Rat.not_le.1 (fun x => h (this x))
    refine ⟨lower, ?_⟩
    have : a - b - 1 + 1 = a - b := by omega
    rwa [this]

/-- `divPow2`: `n / d = (q + r / D) * 2 ^ e`. -/
theorem divPow2_spec {n d : Nat} (hd : 0 < d) (e : Int) :
    0 < (divPow2 n d e).2.2 ∧ (divPow2 n d e).2.1 < (divPow2 n d e).2.2 ∧
      ((divPow2 n d e).1 : Rat) + ((divPow2 n d e).2.1 : Rat) / ((divPow2 n d e).2.2 : Nat)
        = (n : Rat) / d / pw e := by
  simp only [divPow2]
  have hDp : 0 < d * 2 ^ e.toNat := Nat.mul_pos hd (Nat.two_pow_pos _)
  refine ⟨hDp, Nat.mod_lt _ hDp, ?_⟩
  generalize hN : n * 2 ^ (-e).toNat = N
  generalize hDD : d * 2 ^ e.toNat = D at hDp
  have h1 : (N : Rat) = (D : Rat) * ((N / D : Nat) : Rat) + ((N % D : Nat) : Rat) := by
    have := Nat.div_add_mod N D
    exact_mod_cast this.symm
  have hA : 0 < ((2 ^ e.toNat : Nat) : Rat) := natCast_pos' (Nat.two_pow_pos _)
  have hB : 0 < ((2 ^ (-e).toNat : Nat) : Rat) := natCast_pos' (Nat.two_pow_pos _)
  have hd' : 0 < (d : Rat) := natCast_pos' hd
  have hDr : (D : Rat) = (d : Rat) * ((2 ^ e.toNat : Nat) : Rat) := by
    rw [← hDD]; exact_mod_cast rfl
  have hNr : (N : Rat) = (n : Rat) * ((2 ^ (-e).toNat : Nat) : Rat) := by
    rw [← hN]; exact_mod_cast rfl
  rw [pw_eq_div]
  generalize ((2 ^ e.toNat : Nat) : Rat) = a at *
  generalize ((2 ^ (-e).toNat : Nat) : Rat) = b at *
  generalize ((N / D : Nat) : Rat) = q at *
  generalize ((N % D : Nat) : Rat) = r at *
  generalize (d : Rat) = dd at *
  generalize (n : Rat) = nn at *
  generalize (D : Rat) = DD at *
  generalize (N : Rat) = NN at *
  subst hDr hNr
  have hDD' : dd * a ≠ 0 := Rat.ne_of_gt (Rat.mul_pos hd' hA)
  have ha' : a ≠ 0 := Rat.ne_of_gt hA
  have hb' : b ≠ 0 := Rat.ne_of_gt hB
  have hdd' : dd ≠ 0 := Rat.ne_of_gt hd'
  have : r / (dd * a) = nn / dd * (b / a) - q := by
    grind
  have e3 : nn / dd / (a / b) = nn / dd * (b / a) := by grind
  rw [e3, this]; grind

/-- A rational's absolute value. -/
theorem abs_nonneg (a : Rat) : 0 ≤ Rat.abs a := by
  unfold Rat.abs; split <;> grind

theorem abs_of_nonneg {a : Rat} (h : 0 ≤ a) : Rat.abs a = a := by
  unfold Rat.abs; simp [h]

theorem abs_of_nonpos {a : Rat} (h : a ≤ 0) : Rat.abs a = -a := by
  unfold Rat.abs; split <;> grind

/-- The fractional facts `roundInt` branches on. -/
theorem frac_facts {r D : Nat} (hD : 0 < D) (hr : r < D) :
    0 ≤ (r : Rat) / D ∧ (r : Rat) / D < 1 ∧
    (D < 2 * r → 1 / 2 < (r : Rat) / D) ∧ (2 * r = D → (r : Rat) / D = 1 / 2) ∧
    (¬ D < 2 * r → ¬ 2 * r = D → (r : Rat) / D < 1 / 2) := by
  have hDr : 0 < (D : Rat) := natCast_pos' hD
  have hrr : (0 : Rat) ≤ r := Rat.natCast_nonneg
  have key : ∀ c : Rat, c * D < r ↔ c < (r : Rat) / D := fun c => (Rat.lt_div_iff hDr).symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have e : (r : Rat) / D = r * (D : Rat)⁻¹ := rfl
    have : 0 < (D : Rat)⁻¹ := Rat.inv_pos.2 hDr
    rw [e]; exact Rat.mul_nonneg hrr (Rat.le_of_lt this)
  · rw [Rat.div_lt_iff hDr]
    have := Rat.natCast_lt_natCast.2 hr
    simpa using this
  · intro h
    apply (key _).1
    have : (D : Rat) < 2 * r := by exact_mod_cast Rat.natCast_lt_natCast.2 h
    grind
  · intro h
    have h1 : (2 : Rat) * r = D := by exact_mod_cast congrArg (fun x : Nat => (x : Rat)) h
    have hne : (D : Rat) ≠ 0 := Rat.ne_of_gt hDr
    grind
  · intro h1 h2
    rw [Rat.div_lt_iff hDr]
    have : 2 * r < D := by omega
    have h3 : (2 : Rat) * r < D := by exact_mod_cast Rat.natCast_lt_natCast.2 this
    grind

/-- An integer on one side of `q`, or on the other. -/
theorem int_cases (q : Nat) (t : Int) :
    (t : Rat) ≤ (q : Rat) ∧ (t ≠ q → (t : Rat) ≤ (q : Rat) - 1) ∨ (q : Rat) + 1 ≤ (t : Rat) ∧
      (t ≠ (q : Int) + 1 → (q : Rat) + 2 ≤ (t : Rat)) := by
  have cast : ∀ a b : Int, a ≤ b → (a : Rat) ≤ (b : Rat) := fun a b h => Rat.intCast_le_intCast.2 h
  by_cases h : t ≤ q
  · left
    refine ⟨by have := cast _ _ h; push_cast at this; exact this, fun hne => ?_⟩
    have h2 : t ≤ (q : Int) - 1 := by omega
    have := cast _ _ h2; push_cast at this; exact this
  · right
    have h1 : (q : Int) + 1 ≤ t := by omega
    refine ⟨by have := cast _ _ h1; push_cast at this; exact this, fun hne => ?_⟩
    have h2 : (q : Int) + 2 ≤ t := by omega
    have := cast _ _ h2; push_cast at this; exact this

theorem roundInt_cases (q r D : Nat) :
    (D < 2 * r ∧ roundInt q r D = q + 1) ∨ (2 * r = D ∧ q % 2 = 1 ∧ roundInt q r D = q + 1) ∨
      (2 * r = D ∧ q % 2 = 0 ∧ roundInt q r D = q) ∨
      (¬ D < 2 * r ∧ ¬ 2 * r = D ∧ roundInt q r D = q) := by
  unfold roundInt
  by_cases c1 : D < 2 * r
  · left; simp [c1]
  · by_cases c2 : 2 * r = D
    · by_cases c3 : q % 2 = 1
      · right; left; simp [c1, c2, c3]
      · right; right; left
        have : q % 2 = 0 := by omega
        simp [c1, c2, this]
    · right; right; right; simp [c1, c2]

theorem cast_succ (q : Nat) : ((q + 1 : Nat) : Rat) = (q : Rat) + 1 := by push_cast; rfl

/-- `roundInt` picks a nearest integer. -/
theorem roundInt_nearest {q r D : Nat} (hD : 0 < D) (hr : r < D) (t : Int) :
    Rat.abs ((q : Rat) + (r : Rat) / D - (roundInt q r D : Nat)) ≤
      Rat.abs ((q : Rat) + (r : Rat) / D - t) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := frac_facts hD hr
  have hc := int_cases q t
  generalize hx : (r : Rat) / D = x at *
  rcases roundInt_cases q r D with ⟨c1, e⟩ | ⟨c1, _, e⟩ | ⟨c1, _, e⟩ | ⟨c1, c2, e⟩ <;> rw [e]
  · have := h2 c1
    rw [cast_succ]; unfold Rat.abs
    split <;> split <;> grind
  · have := h3 c1
    rw [cast_succ]; unfold Rat.abs
    split <;> split <;> grind
  · have := h3 c1
    unfold Rat.abs
    split <;> split <;> grind
  · have := h4 c1 c2
    unfold Rat.abs
    split <;> split <;> grind

/-- On a tie with a different integer, `roundInt` returned the even one. -/
theorem roundInt_tie {q r D : Nat} (hD : 0 < D) (hr : r < D) (t : Int)
    (h : Rat.abs ((q : Rat) + (r : Rat) / D - (roundInt q r D : Nat)) =
      Rat.abs ((q : Rat) + (r : Rat) / D - t))
    (hne : t ≠ (roundInt q r D : Nat)) : (roundInt q r D) % 2 = 0 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := frac_facts hD hr
  have hc := int_cases q t
  generalize hx : (r : Rat) / D = x at *
  rcases roundInt_cases q r D with ⟨c1, e⟩ | ⟨c1, c3, e⟩ | ⟨c1, c3, e⟩ | ⟨c1, c2, e⟩ <;> rw [e] at h hne ⊢
  · exfalso
    have := h2 c1
    have hne' : t ≠ (q : Int) + 1 := by intro h'; exact hne (by rw [h']; rfl)
    rw [cast_succ] at h; unfold Rat.abs at h
    split at h <;> split at h <;> grind
  · omega
  · exact c3
  · exfalso
    have := h4 c1 c2
    unfold Rat.abs at h
    split at h <;> split at h <;> grind

/-- `y` is a number of the format, with no exponent ceiling. -/
def Rep (f : Fmt) (y : Rat) : Prop :=
  ∃ (M : Nat) (E : Int), M < 2 ^ f.p ∧ f.etiny ≤ E ∧ (y = (M : Rat) * pw E ∨ y = -((M : Rat) * pw E))

/-- The scale `roundExp` picks. -/
theorem roundExp_spec (f : Fmt) (hp : 1 ≤ f.p) {n d : Nat} (hn : 0 < n) (hd : 0 < d) :
    (n : Rat) / d < pw (roundExp f n d + (f.p : Int)) ∧
      (roundExp f n d = f.etiny ∨ pw (roundExp f n d + ((f.p - 1 : Nat) : Int)) ≤ (n : Rat) / d) ∧
      f.etiny ≤ roundExp f n d := by
  obtain ⟨h1, h2⟩ := floorLog2Q_spec hn hd
  unfold roundExp
  generalize floorLog2Q n d = k at *
  have hpp : ((f.p - 1 : Nat) : Int) = (f.p : Int) - 1 := by omega
  refine ⟨?_, ?_, by omega⟩
  · have : pw (k + 1) ≤ pw (max (k - ((f.p - 1 : Nat) : Int)) f.etiny + (f.p : Int)) :=
      pw_le (by omega)
    grind
  · by_cases h : k - ((f.p - 1 : Nat) : Int) ≤ f.etiny
    · left; omega
    · right
      have : max (k - ((f.p - 1 : Nat) : Int)) f.etiny + ((f.p - 1 : Nat) : Int) = k := by omega
      rw [this]; exact h1

theorem abs_mul_pos (a : Rat) {c : Rat} (hc : 0 < c) : Rat.abs (a * c) = Rat.abs a * c := by
  by_cases h : 0 ≤ a
  · rw [abs_of_nonneg h, abs_of_nonneg (Rat.mul_nonneg h (Rat.le_of_lt hc))]
  · have h' : a ≤ 0 := by grind
    rw [abs_of_nonpos h', abs_of_nonpos]
    · grind
    · have := Rat.mul_le_mul_of_nonneg_right h' (Rat.le_of_lt hc)
      simpa using this

/-- The nearest-integer fact, scaled by `2 ^ e`. -/
theorem rounded_near {n d : Nat} (hd : 0 < d) (e : Int) (t : Int) :
    Rat.abs ((n : Rat) / d - ((roundInt (divPow2 n d e).1 (divPow2 n d e).2.1 (divPow2 n d e).2.2 : Nat) : Rat) * pw e) ≤
      Rat.abs ((n : Rat) / d - (t : Rat) * pw e) := by
  obtain ⟨hD, hr, hQ⟩ := divPow2_spec (n := n) hd e
  have h := roundInt_nearest (q := (divPow2 n d e).1) hD hr t
  rw [hQ] at h
  generalize roundInt (divPow2 n d e).1 (divPow2 n d e).2.1 (divPow2 n d e).2.2 = q' at *
  have hp := pw_pos e
  have hv : (n : Rat) / d = (n : Rat) / d / pw e * pw e := (Rat.div_mul_cancel (pw_ne e)).symm
  generalize (n : Rat) / d / pw e = Q at *
  rw [hv]
  have e1 : ∀ z : Rat, Q * pw e - z * pw e = (Q - z) * pw e := by intro z; grind
  rw [e1, e1, abs_mul_pos _ hp, abs_mul_pos _ hp]
  exact Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hp)

/-- Every number of a coarser or equal grid is an integer multiple of `2 ^ e`. -/
theorem grid_multiple {M : Nat} {E e : Int} (h : e ≤ E) :
    ∃ t : Nat, (M : Rat) * pw E = (t : Rat) * pw e := by
  refine ⟨M * 2 ^ (E - e).toNat, ?_⟩
  have h1 : pw E = pw (E - e) * pw e := by rw [← pw_add]; congr 1; omega
  have h2 : pw (E - e) = ((2 ^ (E - e).toNat : Nat) : Rat) := by
    rw [← pw_natCast]; congr 1; omega
  rw [h1, h2, Rat.natCast_mul]; grind

/-- A number of a finer grid sits below `2 ^ (e + p - 1)`. -/
theorem finer_small {f : Fmt} (hp : 1 ≤ f.p) {M : Nat} {E e : Int} (hM : M < 2 ^ f.p) (h : E < e) :
    (M : Rat) * pw E ≤ pw (e + ((f.p - 1 : Nat) : Int)) := by
  have h1 : (M : Rat) ≤ ((2 ^ f.p : Nat) : Rat) := Rat.natCast_le_natCast.2 (Nat.le_of_lt hM)
  rw [← pw_natCast] at h1
  have h2 : pw ((f.p : Int) + E) ≤ pw (e + ((f.p - 1 : Nat) : Int)) := pw_le (by omega)
  have h3 := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt (pw_pos E))
  rw [← pw_add] at h3
  grind

/-- `q' * 2 ^ e` is at least as close to `n / d` as any number of the format. -/
theorem rounded_nearest (f : Fmt) (hp : 1 ≤ f.p) {n d : Nat} (hn : 0 < n) (hd : 0 < d)
    {y : Rat} (hy : Rep f y) :
    Rat.abs ((n : Rat) / d - ((roundInt (divPow2 n d (roundExp f n d)).1 (divPow2 n d (roundExp f n d)).2.1
        (divPow2 n d (roundExp f n d)).2.2 : Nat) : Rat) * pw (roundExp f n d)) ≤
      Rat.abs ((n : Rat) / d - y) := by
  obtain ⟨_, h2, h3⟩ := roundExp_spec f hp hn hd
  generalize roundExp f n d = e at *
  obtain ⟨M, E, hM, hE, hyy⟩ := hy
  by_cases hle : e ≤ E
  · obtain ⟨t, ht⟩ := grid_multiple (M := M) hle
    rcases hyy with rfl | rfl
    · rw [ht]
      have := rounded_near (n := n) hd e (t : Int)
      rwa [Rat.intCast_natCast] at this
    · rw [ht]
      have := rounded_near (n := n) hd e (-(t : Int))
      have e1 : ((-(t : Int) : Int) : Rat) * pw e = -((t : Rat) * pw e) := by
        simp [Rat.neg_mul, Rat.intCast_natCast]
      rwa [e1] at this
  · have hlt : E < e := by omega
    have hne : e ≠ f.etiny := by omega
    have hT : pw (e + ((f.p - 1 : Nat) : Int)) ≤ (n : Rat) / d := by
      rcases h2 with h | h
      · exact absurd h hne
      · exact h
    have hS := finer_small hp hM hlt
    have hnear := rounded_near (n := n) hd e ((2 ^ (f.p - 1) : Nat) : Int)
    have e2 : (((2 ^ (f.p - 1) : Nat) : Int) : Rat) * pw e = pw (e + ((f.p - 1 : Nat) : Int)) := by
      rw [Rat.intCast_natCast, pw_add, ← pw_natCast (f.p - 1), Rat.mul_comm]
    rw [e2, abs_of_nonneg (a := (n : Rat) / d - pw (e + ((f.p - 1 : Nat) : Int))) (by grind)] at hnear
    have hM0 : (0 : Rat) ≤ (M : Rat) * pw E :=
      Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (pw_pos E))
    rcases hyy with rfl | rfl
    · rw [abs_of_nonneg (a := (n : Rat) / d - (M : Rat) * pw E) (by grind)]; grind
    · rw [abs_of_nonneg (a := (n : Rat) / d - -((M : Rat) * pw E)) (by grind)]; grind

/-- The strict version of `finer_small`. -/
theorem finer_small_lt {f : Fmt} (hp : 1 ≤ f.p) {M : Nat} {E e : Int} (hM : M < 2 ^ f.p) (h : E < e) :
    (M : Rat) * pw E < pw (e + ((f.p - 1 : Nat) : Int)) := by
  have h1 : (M : Rat) < ((2 ^ f.p : Nat) : Rat) := Rat.natCast_lt_natCast.2 hM
  rw [← pw_natCast] at h1
  have h2 : pw ((f.p : Int) + E) ≤ pw (e + ((f.p - 1 : Nat) : Int)) := pw_le (by omega)
  have h3 := (Rat.mul_lt_mul_right (pw_pos E)).2 h1
  rw [← pw_add] at h3
  grind

/-- The tie fact, scaled by `2 ^ e`. -/
theorem rounded_near_tie {n d : Nat} (hd : 0 < d) (e : Int) (t : Int)
    (h : Rat.abs ((n : Rat) / d - ((roundInt (divPow2 n d e).1 (divPow2 n d e).2.1 (divPow2 n d e).2.2 : Nat) : Rat) * pw e) =
      Rat.abs ((n : Rat) / d - (t : Rat) * pw e))
    (hne : (t : Rat) * pw e ≠ ((roundInt (divPow2 n d e).1 (divPow2 n d e).2.1 (divPow2 n d e).2.2 : Nat) : Rat) * pw e) :
    (roundInt (divPow2 n d e).1 (divPow2 n d e).2.1 (divPow2 n d e).2.2) % 2 = 0 := by
  obtain ⟨hD, hr, hQ⟩ := divPow2_spec (n := n) hd e
  apply roundInt_tie hD hr t
  · rw [hQ]
    have hp := pw_pos e
    have hv : (n : Rat) / d = (n : Rat) / d / pw e * pw e := (Rat.div_mul_cancel (pw_ne e)).symm
    generalize (roundInt (divPow2 n d e).1 (divPow2 n d e).2.1 (divPow2 n d e).2.2) = q' at *
    generalize (n : Rat) / d / pw e = Q at *
    rw [hv] at h
    have e1 : ∀ z : Rat, Q * pw e - z * pw e = (Q - z) * pw e := by intro z; grind
    rw [e1, e1, abs_mul_pos _ hp, abs_mul_pos _ hp] at h
    have h5 : Rat.abs (Q - (q' : Rat)) * pw e * (pw e)⁻¹ = Rat.abs (Q - (t : Rat)) * pw e * (pw e)⁻¹ := by
      rw [h]
    rwa [Rat.mul_assoc, Rat.mul_assoc, pw_mul_inv, Rat.mul_one, Rat.mul_one] at h5
  · intro h'
    apply hne
    have : (t : Rat) = ((roundInt (divPow2 n d e).1 (divPow2 n d e).2.1 (divPow2 n d e).2.2 : Nat) : Rat) := by
      rw [h']; exact Rat.intCast_natCast _
    rw [this]

/-- On a tie with a different number of the format, the rounded integer is even. -/
theorem rounded_tie (f : Fmt) (hp : 1 ≤ f.p) {n d : Nat} (hn : 0 < n) (hd : 0 < d)
    {y : Rat} (hy : Rep f y)
    (htie : Rat.abs ((n : Rat) / d - ((roundInt (divPow2 n d (roundExp f n d)).1 (divPow2 n d (roundExp f n d)).2.1
        (divPow2 n d (roundExp f n d)).2.2 : Nat) : Rat) * pw (roundExp f n d)) =
      Rat.abs ((n : Rat) / d - y))
    (hne : y ≠ ((roundInt (divPow2 n d (roundExp f n d)).1 (divPow2 n d (roundExp f n d)).2.1
        (divPow2 n d (roundExp f n d)).2.2 : Nat) : Rat) * pw (roundExp f n d)) :
    (roundInt (divPow2 n d (roundExp f n d)).1 (divPow2 n d (roundExp f n d)).2.1
        (divPow2 n d (roundExp f n d)).2.2) % 2 = 0 := by
  obtain ⟨_, h2, h3⟩ := roundExp_spec f hp hn hd
  generalize roundExp f n d = e at *
  obtain ⟨M, E, hM, hE, hyy⟩ := hy
  by_cases hle : e ≤ E
  · obtain ⟨t, ht⟩ := grid_multiple (M := M) hle
    rcases hyy with rfl | rfl
    · rw [ht] at htie hne
      apply rounded_near_tie (n := n) hd e (t : Int)
      · rwa [Rat.intCast_natCast]
      · rwa [Rat.intCast_natCast]
    · rw [ht] at htie hne
      have e1 : ((-(t : Int) : Int) : Rat) * pw e = -((t : Rat) * pw e) := by
        simp [Rat.neg_mul, Rat.intCast_natCast]
      apply rounded_near_tie (n := n) hd e (-(t : Int))
      · rwa [e1]
      · rwa [e1]
  · exfalso
    have hlt : E < e := by omega
    have hne' : e ≠ f.etiny := by omega
    have hT : pw (e + ((f.p - 1 : Nat) : Int)) ≤ (n : Rat) / d := by
      rcases h2 with h | h
      · exact absurd h hne'
      · exact h
    have hS := finer_small_lt hp hM hlt
    have hnear := rounded_near (n := n) hd e ((2 ^ (f.p - 1) : Nat) : Int)
    have e2 : (((2 ^ (f.p - 1) : Nat) : Int) : Rat) * pw e = pw (e + ((f.p - 1 : Nat) : Int)) := by
      rw [Rat.intCast_natCast, pw_add, ← pw_natCast (f.p - 1), Rat.mul_comm]
    rw [e2, abs_of_nonneg (a := (n : Rat) / d - pw (e + ((f.p - 1 : Nat) : Int))) (by grind)] at hnear
    have hM0 : (0 : Rat) ≤ (M : Rat) * pw E :=
      Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (pw_pos E))
    have hTp := pw_pos (e + ((f.p - 1 : Nat) : Int))
    rcases hyy with rfl | rfl
    · rw [abs_of_nonneg (a := (n : Rat) / d - (M : Rat) * pw E) (by grind)] at htie; grind
    · rw [abs_of_nonneg (a := (n : Rat) / d - -((M : Rat) * pw E)) (by grind)] at htie; grind

end PyLean.Binary64
