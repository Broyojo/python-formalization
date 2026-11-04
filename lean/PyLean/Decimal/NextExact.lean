import PyLean.Decimal.AddExact

/-!
`next_plus`, `next_minus` and `next_toward`: the smallest representable number above (largest
below) a finite operand, and the twin relation between them.

A value is *representable* in a context when it is `±cz·10^ez` with `cz < 10^prec` and
`Etiny ≤ ez ≤ Etop` (`RepAt`): every value `_fix` returns has that form (a finite value of
exponent above `Etop`, which `clamp=0` allows, is the same number as one at `Etop` with trailing
zeros). Values are compared as integers after scaling to a common exponent `L` (`scl`).
-/

namespace PyLean.Decimal

open PyLean

/-- `±c·10^(e-L)` as an integer, for `L ≤ e`. -/
def scl (neg : Bool) (c : Nat) (e L : Int) : Int :=
  if neg then -((c * 10 ^ (e - L).toNat : Nat) : Int) else ((c * 10 ^ (e - L).toNat : Nat) : Int)

/-- `Z` is, scaled to the exponent `L`, a value representable in `c`: `±cz·10^ez` with
`cz < 10^prec` and `Etiny ≤ ez ≤ Etop`. -/
def RepAt (c : Ctx) (L : Int) (Z : Int) : Prop :=
  ∃ (b : Bool) (cz : Nat) (ez : Int), cz < 10 ^ c.prec ∧ c.etiny ≤ ez ∧ ez ≤ c.etop ∧ Z = scl b cz ez L

/-! ## Arithmetic on powers of ten -/

theorem pow10_le {a b : Nat} (h : a ≤ b) : 10 ^ a ≤ 10 ^ b := Nat.pow_le_pow_right (by decide) h

theorem pow10_pos (a : Nat) : 0 < 10 ^ a := Nat.pow_pos (by decide)

/-- A representable magnitude is at most the largest finite value. -/
theorem rep_le_max {p : Nat} {cz a aU : Nat} (hc : cz < 10 ^ p) (ha : a ≤ aU) :
    cz * 10 ^ a ≤ (10 ^ p - 1) * 10 ^ aU :=
  Nat.mul_le_mul (by omega) (pow10_le ha)

/-- A magnitude below `10^p` at an exponent below `m` is below `10^(p-1)·10^m`. -/
theorem small_lt {p : Nat} (hp : 1 ≤ p) {cz a m : Nat} (hc : cz < 10 ^ p) (ha : a + 1 ≤ m) :
    cz * 10 ^ a < 10 ^ (p - 1) * 10 ^ m := by
  have h1 : cz * 10 ^ a < 10 ^ p * 10 ^ a := Nat.mul_lt_mul_of_pos_right hc (pow10_pos a)
  have h2 : 10 ^ p * 10 ^ a ≤ 10 ^ (p - 1) * 10 ^ m := by
    rw [← Nat.pow_add, ← Nat.pow_add]; exact pow10_le (by omega)
  omega

/-- A magnitude at an exponent of at least `m` is a multiple of `10^m`. -/
theorem mult_of_ge {cz a m : Nat} (ha : m ≤ a) : cz * 10 ^ a = (cz * 10 ^ (a - m)) * 10 ^ m := by
  rw [Nat.mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel ha]

/-- `(q0 + 1)·M` is the least multiple of `M` above `q0·M`. -/
theorem mult_succ_le {w q M : Nat} (h : q * M < w * M) : (q + 1) * M ≤ w * M :=
  Nat.mul_le_mul_right M (Nat.lt_of_mul_lt_mul_right h)

theorem mult_le_of_lt_succ {w q M : Nat} (h : w * M < (q + 1) * M) : w * M ≤ q * M :=
  Nat.mul_le_mul_right M (Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_right h))

/-- A coefficient of `nd` digits at exponent `b` is at least `10^(nd-1+b)`. -/
theorem co_ge {co : Nat} (hc : co ≠ 0) (b : Nat) : 10 ^ (numDigits co - 1 + b) ≤ co * 10 ^ b := by
  rw [Nat.pow_add]
  exact Nat.mul_le_mul_right _ (numDigits_bounds hc).1

/-! ## Rounding toward +∞ is the least representable value at or above -/

/-- `sigRun` in a context that traps nothing returns its value. -/
theorem sigRun_noTraps (c : Ctx) (h : c.traps = []) : ∀ (ss fl : List Signal) (v : Dec),
    ∃ fl', sigRun c ss fl v = .ok (v, fl')
  | [], fl, v => ⟨fl, rfl⟩
  | s :: ss, fl, v => by
    have : s ∉ c.traps := by rw [h]; simp
    simp only [sigRun, this, ↓reduceIte]
    exact sigRun_noTraps c h ss _ v

theorem sigRun_val {c : Ctx} (h : c.traps = []) {ss fl fl1 : List Signal} {v w : Dec}
    (hr : sigRun c ss fl v = .ok (w, fl1)) : w = v := by
  obtain ⟨fl', h'⟩ := sigRun_noTraps c h ss fl v
  rw [h'] at hr
  cases hr
  rfl

/-- What rounding toward `+∞` into `c` gives for the value `X` (scaled to `L`): `+Infinity` when
every representable value is below `X`; otherwise a finite `±cv·10^ev` with `ev ≥ Etiny`, at least
`X`, at most every representable value at least `X`, and either `X` itself or representable. -/
def CeilGoal (c : Ctx) (L X : Int) (v : Dec) : Prop :=
  (v = .inf false ∧ ∀ Z, RepAt c L Z → Z < X) ∨
  (∃ sv cv ev, v = .fin sv cv ev ∧ c.etiny ≤ ev ∧ X ≤ scl sv cv ev L ∧
     (scl sv cv ev L = X ∨ (cv < 10 ^ c.prec ∧ ev ≤ c.etop)) ∧
     ∀ Z, RepAt c L Z → X ≤ Z → scl sv cv ev L ≤ Z)

/-- A representable value, unpacked at `L ≤ Etiny`. -/
theorem repAt_cases {c : Ctx} {L Z : Int} (hL : L ≤ c.etiny) (h : RepAt c L Z) :
    ∃ (bz : Bool) (cz az : Nat), cz < 10 ^ c.prec ∧ (c.etiny - L).toNat ≤ az ∧ az ≤ (c.etop - L).toNat ∧
      Z = (if bz then -((cz * 10 ^ az : Nat) : Int) else ((cz * 10 ^ az : Nat) : Int)) := by
  obtain ⟨bz, cz, ez, hc, h1, h2, rfl⟩ := h
  exact ⟨bz, cz, (ez - L).toNat, hc, by omega, by omega, rfl⟩

/-- Every representable value lies within the largest finite magnitude. -/
theorem repAt_bound {c : Ctx} {L Z : Int} (hL : L ≤ c.etiny) (h : RepAt c L Z) :
    Z ≤ (((10 ^ c.prec - 1) * 10 ^ (c.etop - L).toNat : Nat) : Int) ∧
    -(((10 ^ c.prec - 1) * 10 ^ (c.etop - L).toNat : Nat) : Int) ≤ Z := by
  obtain ⟨bz, cz, az, hc, _, h2, rfl⟩ := repAt_cases hL h
  have := rep_le_max hc h2
  cases bz <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem overflowResult_ceiling (q : Ctx) (h : q.rounding = .ceiling) (neg : Bool) :
    overflowResult q neg = if neg then .fin true (10 ^ q.prec - 1) (q.emax - q.prec + 1) else .inf false := by
  cases neg <;> simp [overflowResult, h]

/-- The overflow branch: a value above every finite one. -/
theorem ceil_over (q : Ctx) (hp : 1 ≤ q.prec) (hE : q.emin ≤ q.emax) (hr : q.rounding = .ceiling)
    (neg : Bool) (co : Nat) (e L : Int) (hc : co ≠ 0) (hL1 : L ≤ e) (hL2 : L ≤ q.etiny)
    (ho : e + (numDigits co : Int) - 1 > q.emax) :
    CeilGoal q L (scl neg co e L) (overflowResult q neg) := by
  have hT : q.etiny = q.emin - q.prec + 1 := rfl
  have hU : q.etop = q.emax - q.prec + 1 := rfl
  have hbig : (10 ^ q.prec - 1) * 10 ^ (q.etop - L).toNat < co * 10 ^ (e - L).toNat := by
    have h1 := co_ge hc (e - L).toNat
    have h2 : 10 ^ (q.prec + (q.etop - L).toNat) ≤ 10 ^ (numDigits co - 1 + (e - L).toNat) :=
      pow10_le (by omega)
    have h3 : (10 ^ q.prec - 1) * 10 ^ (q.etop - L).toNat < 10 ^ q.prec * 10 ^ (q.etop - L).toNat :=
      Nat.mul_lt_mul_of_pos_right (by have := pow10_pos q.prec; omega) (pow10_pos _)
    rw [← Nat.pow_add] at h3
    omega
  rw [overflowResult_ceiling q hr]
  cases neg with
  | false =>
    left
    refine ⟨rfl, fun Z hZ => ?_⟩
    have := (repAt_bound hL2 hZ).1
    simp only [scl, Bool.false_eq_true, ↓reduceIte]
    omega
  | true =>
    right
    refine ⟨true, 10 ^ q.prec - 1, q.emax - q.prec + 1, rfl, by omega, ?_, Or.inr ⟨by have := pow10_pos q.prec; omega, by omega⟩, ?_⟩
    · have e1 : (q.emax - q.prec + 1 - L).toNat = (q.etop - L).toNat := by rw [hU]
      simp only [scl, ↓reduceIte, e1]
      omega
    · intro Z hZ _
      have := (repAt_bound hL2 hZ).2
      have e1 : (q.emax - q.prec + 1 - L).toNat = (q.etop - L).toNat := by rw [hU]
      simp only [scl, ↓reduceIte, e1]
      omega

/-- The branch that keeps the value: it is the operand itself. -/
theorem ceil_keep (q : Ctx) (neg : Bool) (cv : Nat) (ev : Int) (co : Nat) (e L : Int)
    (hT : q.etiny ≤ ev) (hv : scl neg cv ev L = scl neg co e L) :
    CeilGoal q L (scl neg co e L) (.fin neg cv ev) := by
  right
  exact ⟨neg, cv, ev, rfl, hT, Int.le_of_eq hv.symm, Or.inl hv, fun Z _ hZ => by rw [hv]; exact hZ⟩

theorem scl_fold (neg : Bool) (co : Nat) (e U L : Int) (hU : U < e) (hL : L ≤ U) :
    scl neg (co * 10 ^ (e - U).toNat) U L = scl neg co e L := by
  have : co * 10 ^ (e - U).toNat * 10 ^ (U - L).toNat = co * 10 ^ (e - L).toNat := by
    rw [Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    omega
  simp only [scl, this]

/-- Leastness above: a representable value at least `q0·M + rb` (with `0 < rb`) is at least
`(q0+1)·M`, when every representable value at an exponent below `M`'s has a magnitude below
`q0·M`. -/
theorem least_pos {c : Ctx} {L Z : Int} (hL : L ≤ c.etiny) (hZ : RepAt c L Z) (q0 rb m : Nat)
    (hrb : 0 < rb) (hX : (((q0 * 10 ^ m + rb : Nat)) : Int) ≤ Z)
    (hsm : ∀ cz az, cz < 10 ^ c.prec → (c.etiny - L).toNat ≤ az → az < m → cz * 10 ^ az < q0 * 10 ^ m) :
    (((q0 + 1) * 10 ^ m : Nat) : Int) ≤ Z := by
  obtain ⟨bz, cz, az, hc, h1, _, rfl⟩ := repAt_cases hL hZ
  cases bz with
  | true => simp only [↓reduceIte] at hX; omega
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hX ⊢
    by_cases ha : m ≤ az
    · rw [mult_of_ge ha] at hX ⊢
      have : q0 * 10 ^ m < cz * 10 ^ (az - m) * 10 ^ m := by omega
      have := mult_succ_le this
      omega
    · have := hsm cz az hc h1 (by omega)
      omega

/-- Leastness below zero: a representable value at least `-(q0·M + rb)` (with `rb < M`) is at
least `-(q0·M)`. -/
theorem least_neg {c : Ctx} {L Z : Int} (hL : L ≤ c.etiny) (hZ : RepAt c L Z) (q0 rb m : Nat)
    (hrb : rb < 10 ^ m) (hX : -(((q0 * 10 ^ m + rb : Nat)) : Int) ≤ Z)
    (hsm : ∀ cz az, cz < 10 ^ c.prec → (c.etiny - L).toNat ≤ az → az < m → cz * 10 ^ az < q0 * 10 ^ m) :
    -((q0 * 10 ^ m : Nat) : Int) ≤ Z := by
  obtain ⟨bz, cz, az, hc, h1, _, rfl⟩ := repAt_cases hL hZ
  cases bz with
  | false => simp only [Bool.false_eq_true, ↓reduceIte]; omega
  | true =>
    simp only [↓reduceIte] at hX ⊢
    by_cases ha : m ≤ az
    · rw [mult_of_ge ha] at hX ⊢
      have h2 : cz * 10 ^ (az - m) * 10 ^ m < (q0 + 1) * 10 ^ m := by rw [Nat.succ_mul]; omega
      have := mult_le_of_lt_succ h2
      omega
    · have := hsm cz az hc h1 (by omega)
      omega

/-- The rounding branch of `_fix` under `ROUND_CEILING`: the kept prefix `q0` of `co`, plus one
when digits that are not all zero are dropped from a positive value, at the exponent `emn`. -/
theorem ceil_round (q : Ctx) (hp : 1 ≤ q.prec) (hE : q.emin ≤ q.emax) (hr : q.rounding = .ceiling)
    (neg : Bool) (co : Nat) (e L emn : Int) (k : Nat) (hc : co ≠ 0) (hL1 : L ≤ e) (hL2 : L ≤ q.etiny)
    (hemn1 : (numDigits co : Int) + e - q.prec ≤ emn) (hemn2 : q.emin - q.prec + 1 ≤ emn)
    (hemn3 : emn = (numDigits co : Int) + e - q.prec ∨ emn = q.emin - q.prec + 1)
    (hno : ¬ e + (numDigits co : Int) - 1 > q.emax) (hlt : e < emn) (hk : (k : Int) = emn - e) :
    CeilGoal q L (scl neg co e L)
      (if decide ((if numDigits (roundSpec .ceiling neg (co / 10 ^ k) (co % 10 ^ k) (10 ^ k)) > q.prec
            then emn + 1 else emn) > q.emax - q.prec + 1) = true
        then overflowResult q neg
        else .fin neg (if numDigits (roundSpec .ceiling neg (co / 10 ^ k) (co % 10 ^ k) (10 ^ k)) > q.prec
            then roundSpec .ceiling neg (co / 10 ^ k) (co % 10 ^ k) (10 ^ k) / 10
            else roundSpec .ceiling neg (co / 10 ^ k) (co % 10 ^ k) (10 ^ k))
          (if numDigits (roundSpec .ceiling neg (co / 10 ^ k) (co % 10 ^ k) (10 ^ k)) > q.prec
            then emn + 1 else emn)) := by
  have hT : q.etiny = q.emin - q.prec + 1 := rfl
  have hU : q.etop = q.emax - q.prec + 1 := rfl
  obtain ⟨b, hb⟩ : ∃ b : Nat, (b : Int) = e - L := ⟨(e - L).toNat, by omega⟩
  have heb : (e - L).toNat = b := by omega
  have hemb : (emn - L).toNat = b + k := by omega
  have hemb1 : (emn + 1 - L).toNat = b + k + 1 := by omega
  have hrk : co % 10 ^ k < 10 ^ k := Nat.mod_lt _ (pow10_pos k)
  have hco := Nat.div_add_mod co (10 ^ k)
  have hnd := (numDigits_bounds hc)
  have hq0lt : co / 10 ^ k < 10 ^ q.prec := by
    rw [Nat.div_lt_iff_lt_mul (pow10_pos k), ← Nat.pow_add]
    exact Nat.lt_of_lt_of_le hnd.2 (pow10_le (by omega))
  have hq0big : emn ≠ q.emin - q.prec + 1 → 10 ^ (q.prec - 1) ≤ co / 10 ^ k := by
    intro hne
    rw [Nat.le_div_iff_mul_le (pow10_pos k), ← Nat.pow_add]
    exact Nat.le_trans (pow10_le (by omega)) hnd.1
  have hemnU : emn ≤ q.emax - q.prec + 1 := by omega
  generalize co / 10 ^ k = q0 at *
  generalize co % 10 ^ k = r at *
  have hM : 10 ^ (b + k) = 10 ^ k * 10 ^ b := by rw [Nat.pow_add, Nat.mul_comm]
  have hX : co * 10 ^ b = q0 * 10 ^ (b + k) + r * 10 ^ b := by
    rw [← hco, hM, Nat.add_mul]
    congr 1
    rw [Nat.mul_comm (10 ^ k) q0, Nat.mul_assoc]
  have hrb : r * 10 ^ b < 10 ^ (b + k) := by
    rw [hM]; exact Nat.mul_lt_mul_of_pos_right hrk (pow10_pos b)
  have hsm : ∀ cz az, cz < 10 ^ q.prec → (q.etiny - L).toNat ≤ az → az < b + k →
      cz * 10 ^ az < q0 * 10 ^ (b + k) := by
    intro cz az hcz h1 h2
    have := hq0big (by omega)
    exact Nat.lt_of_lt_of_le (small_lt hp hcz (by omega)) (Nat.mul_le_mul_right _ this)
  have hq0d : ¬ numDigits q0 > q.prec := by
    have := (numDigits_le_iff (by omega : 0 < q.prec)).mpr hq0lt; omega
  cases neg with
  | true =>
    have hq : roundSpec .ceiling true q0 r (10 ^ k) = q0 := by simp [roundSpec]
    have hov : ¬ (emn > q.emax - q.prec + 1) := by omega
    simp only [hq, hq0d, ↓reduceIte, hov, decide_false, Bool.false_eq_true]
    right
    refine ⟨true, q0, emn, rfl, by omega, ?_, Or.inr ⟨hq0lt, by omega⟩, ?_⟩
    · simp only [scl, ↓reduceIte, heb, hemb, hX]; omega
    · intro Z hZ hXZ
      simp only [scl, ↓reduceIte, heb, hX] at hXZ
      simp only [scl, ↓reduceIte, hemb]
      exact least_neg hL2 hZ q0 (r * 10 ^ b) (b + k) hrb hXZ hsm
  | false =>
    by_cases hr0 : r = 0
    · subst hr0
      have hq : roundSpec .ceiling false q0 0 (10 ^ k) = q0 := by simp [roundSpec]
      have hov : ¬ (emn > q.emax - q.prec + 1) := by omega
      simp only [hq, hq0d, ↓reduceIte, hov, decide_false, Bool.false_eq_true]
      apply ceil_keep q false q0 emn co e L (by omega)
      simp only [scl, Bool.false_eq_true, ↓reduceIte, heb, hemb, hX, Nat.zero_mul, Nat.add_zero]
    · have hq : roundSpec .ceiling false q0 r (10 ^ k) = q0 + 1 := by simp [roundSpec, hr0]
      have hrb0 : 0 < r * 10 ^ b := Nat.mul_pos (by omega) (pow10_pos b)
      have hXv : scl false co e L = ((q0 * 10 ^ (b + k) + r * 10 ^ b : Nat) : Int) := by
        simp only [scl, Bool.false_eq_true, ↓reduceIte, heb, hX]
      simp only [hq]
      by_cases hd : numDigits (q0 + 1) > q.prec
      · have h10 : q0 + 1 = 10 ^ q.prec := by
          have : ¬ (q0 + 1 < 10 ^ q.prec) := fun h =>
            absurd ((numDigits_le_iff (by omega : 0 < q.prec)).mpr h) (by omega)
          omega
        simp only [hd, ↓reduceIte]
        by_cases hov : emn + 1 > q.emax - q.prec + 1
        · simp only [hov, decide_true, ↓reduceIte, overflowResult_ceiling q hr, Bool.false_eq_true]
          left
          refine ⟨rfl, fun Z hZ => ?_⟩
          have hb' := (repAt_bound hL2 hZ).1
          have e1 : (q.etop - L).toNat = b + k := by rw [hU]; omega
          rw [e1] at hb'
          have : 10 ^ q.prec - 1 = q0 := by omega
          rw [this] at hb'
          rw [hXv]; omega
        · simp only [hov, decide_false, ↓reduceIte, Bool.false_eq_true]
          have hV : (q0 + 1) / 10 * 10 ^ (b + k + 1) = (q0 + 1) * 10 ^ (b + k) := by
            rw [h10]
            obtain ⟨j, hj⟩ : ∃ j, q.prec = j + 1 := ⟨q.prec - 1, by omega⟩
            have h1 : 10 ^ (j + 1) / 10 = 10 ^ j := by
              rw [Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]
            rw [hj, h1, ← Nat.pow_add, ← Nat.pow_add]
            congr 1
            omega
          have hS : (q0 + 1) * 10 ^ (b + k) = q0 * 10 ^ (b + k) + 10 ^ (b + k) := by
            rw [Nat.add_mul, Nat.one_mul]
          right
          refine ⟨false, (q0 + 1) / 10, emn + 1, rfl, by omega, ?_, Or.inr ⟨?_, by omega⟩, ?_⟩
          · rw [hXv]; simp only [scl, Bool.false_eq_true, ↓reduceIte, hemb1, hV, hS]
            omega
          · exact Nat.lt_of_lt_of_le (Nat.div_lt_self (by omega) (by decide)) (by omega)
          · intro Z hZ hXZ
            simp only [scl, Bool.false_eq_true, ↓reduceIte, hemb1, hV]
            rw [hXv] at hXZ
            exact least_pos hL2 hZ q0 (r * 10 ^ b) (b + k) hrb0 hXZ hsm
      · have hov : ¬ (emn > q.emax - q.prec + 1) := by omega
        simp only [hd, ↓reduceIte, hov, decide_false, Bool.false_eq_true]
        right
        refine ⟨false, q0 + 1, emn, rfl, by omega, ?_, Or.inr ⟨?_, by omega⟩, ?_⟩
        · have hS : (q0 + 1) * 10 ^ (b + k) = q0 * 10 ^ (b + k) + 10 ^ (b + k) := by
            rw [Nat.add_mul, Nat.one_mul]
          rw [hXv]; simp only [scl, Bool.false_eq_true, ↓reduceIte, hemb, hS]
          omega
        · exact (numDigits_le_iff (by omega : 0 < q.prec)).mp (by omega)
        · intro Z hZ hXZ
          simp only [scl, Bool.false_eq_true, ↓reduceIte, hemb]
          rw [hXv] at hXZ
          exact least_pos hL2 hZ q0 (r * 10 ^ b) (b + k) hrb0 hXZ hsm

end PyLean.Decimal
