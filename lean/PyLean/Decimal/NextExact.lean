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

/-- `_fix` under `ROUND_CEILING`, in a context that traps nothing, of every finite non-zero value:
the least representable value at or above it (`CeilGoal`). -/
theorem ceil_fixSpec (q : Ctx) (hp : 1 ≤ q.prec) (hE : q.emin ≤ q.emax) (hr : q.rounding = .ceiling)
    (htr : q.traps = []) (neg : Bool) (co : Nat) (e L : Int) (hc : co ≠ 0) (hL1 : L ≤ e)
    (hL2 : L ≤ q.etiny) (fl0 fl1 : List Signal) (v : Dec) (h : fixSpec q neg co e fl0 = .ok (v, fl1)) :
    CeilGoal q L (scl neg co e L) v := by
  have hT : q.etiny = q.emin - q.prec + 1 := rfl
  have hU : q.etop = q.emax - q.prec + 1 := rfl
  unfold fixSpec at h
  simp only at h
  split at h
  · rename_i ho
    rw [sigRun_val htr h]
    exact ceil_over q hp hE hr neg co e L hc hL1 hL2 ho
  · rename_i ho
    split at h
    · rename_i hk
      split at h
      · rename_i hcl
        rw [sigRun_val htr h]
        exact ceil_keep q neg _ _ co e L (by omega) (scl_fold neg co e _ L hcl.2 (by omega))
      · rw [sigRun_val htr h]
        exact ceil_keep q neg co e co e L (by omega) rfl
    · rename_i hk
      split at h
      · exact absurd h (by simp)
      · rw [sigRun_val htr h]
        simp only [hr]
        exact ceil_round q hp hE hr neg co e L _ _ hc hL1 hL2 (Int.le_max_left _ _) (Int.le_max_right _ _)
          (by omega) ho (by omega) (by omega)

/-- What `next_plus` gives for the value `X` (scaled to `L`): `+Infinity` when no representable
value is above `X`, otherwise the least representable value above it. -/
def NextGoal (c : Ctx) (L X : Int) (y : Dec) : Prop :=
  (y = .inf false ∧ ∀ Z, RepAt c L Z → Z ≤ X) ∨
  (∃ sy cy ey, y = .fin sy cy ey ∧ cy < 10 ^ c.prec ∧ c.etiny ≤ ey ∧ ey ≤ c.etop ∧
     X < scl sy cy ey L ∧ ∀ Z, RepAt c L Z → X < Z → scl sy cy ey L ≤ Z)

/-- A rounded value that differs from the operand is the least representable value above it. -/
theorem next_of_ceil_ne {c : Ctx} {L X : Int} {v : Dec} (h : CeilGoal c L X v)
    (hne : ∀ sv cv ev, v = .fin sv cv ev → c.etiny ≤ ev → scl sv cv ev L ≠ X) : NextGoal c L X v := by
  rcases h with ⟨rfl, h2⟩ | ⟨sv, cv, ev, rfl, h1, h2, h3, h4⟩
  · exact Or.inl ⟨rfl, fun Z hZ => Int.le_of_lt (h2 Z hZ)⟩
  · have hn := hne sv cv ev rfl h1
    rcases h3 with h3 | ⟨h3, h3'⟩
    · exact absurd h3 hn
    · exact Or.inr ⟨sv, cv, ev, rfl, h3, h1, h3', by omega, fun Z hZ hXZ => h4 Z hZ (by omega)⟩

/-- `10^(Etiny - L)` as an integer, for `L < Etiny`. -/
def gapD (c : Ctx) (L : Int) : Int := ((10 ^ (c.etiny - L).toNat : Nat) : Int)
def gapd (c : Ctx) (L : Int) : Int := ((10 ^ (c.etiny - 1 - L).toNat : Nat) : Int)

theorem gapD_eq {c : Ctx} {L : Int} (hL : L < c.etiny) : gapD c L = 10 * gapd c L := by
  have : (c.etiny - L).toNat = (c.etiny - 1 - L).toNat + 1 := by omega
  simp only [gapD, gapd, this, Nat.pow_succ]
  omega

theorem gapd_pos (c : Ctx) (L : Int) : 0 < gapd c L := by
  have := pow10_pos (c.etiny - 1 - L).toNat
  simp only [gapd]; omega

/-- Values on the grid of `10^Etiny`: from `u·D < w·D`, `w·D ≥ u·D + D`. -/
theorem grid_step {u w D : Int} (hD : 0 < D) (h : u * D < w * D) : u * D + D ≤ w * D := by
  have h1 : u < w := Int.lt_of_mul_lt_mul_right h (by omega)
  have h2 : 1 * D ≤ (w - u) * D := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  rw [Int.sub_mul, Int.one_mul] at h2
  omega

/-- A finite value at an exponent of at least `Etiny` is on the grid of `10^Etiny`. -/
theorem fin_grid (c : Ctx) (L : Int) (sv : Bool) (cv : Nat) (ev : Int) (hT : c.etiny ≤ ev) (hL : L ≤ c.etiny) :
    ∃ w : Int, scl sv cv ev L = w * gapD c L := by
  have h := mult_of_ge (cz := cv) (show (c.etiny - L).toNat ≤ (ev - L).toNat by omega)
  refine ⟨sgnVal sv (cv * 10 ^ ((ev - L).toNat - (c.etiny - L).toNat)), ?_⟩
  simp only [scl, gapD, sgnVal, h]
  cases sv <;> simp [Int.natCast_mul, Int.neg_mul]

theorem repAt_grid {c : Ctx} {L Z : Int} (hL : L ≤ c.etiny) (hZ : RepAt c L Z) :
    ∃ w : Int, Z = w * gapD c L := by
  obtain ⟨b, cz, ez, _, h1, _, rfl⟩ := hZ
  exact fin_grid c L b cz ez h1 hL

/-- `next_plus` after the rounding returned the operand itself: the value one tenth of a unit
of `Etiny` above it, rounded up, is the least representable value above the operand. -/
theorem next_of_ceil_add {c : Ctx} {L X : Int} {y : Dec} (hL : L < c.etiny) (hX : ∃ u, X = u * gapD c L)
    (h : CeilGoal c L (X + gapd c L) y) : NextGoal c L X y := by
  obtain ⟨u, rfl⟩ := hX
  have hD := gapD_eq hL
  have hd := gapd_pos c L
  have hDp : 0 < gapD c L := by omega
  rcases h with ⟨rfl, h2⟩ | ⟨sy, cy, ey, rfl, h1, h2, h3, h4⟩
  · refine Or.inl ⟨rfl, fun Z hZ => ?_⟩
    have := h2 Z hZ
    obtain ⟨w, rfl⟩ := repAt_grid (by omega) hZ
    by_cases hc : u * gapD c L < w * gapD c L
    · have := grid_step hDp hc; omega
    · omega
  · obtain ⟨w, hw⟩ := fin_grid c L sy cy ey h1 (by omega)
    have hne : scl sy cy ey L ≠ u * gapD c L + gapd c L := by
      rw [hw]; intro heq
      by_cases hc : u * gapD c L < w * gapD c L
      · have := grid_step hDp hc; omega
      · omega
    rcases h3 with h3 | ⟨h3, h3'⟩
    · exact absurd h3 hne
    · refine Or.inr ⟨sy, cy, ey, rfl, h3, h1, h3', by omega, fun Z hZ hXZ => h4 Z hZ ?_⟩
      obtain ⟨w', rfl⟩ := repAt_grid (by omega) hZ
      have := grid_step hDp hXZ; omega

/-! ## `next_plus` on a finite operand -/

/-- The body of `next_plus` on a finite operand (_pydecimal.py:3612-3619): `_fix` under
`ROUND_CEILING` in a copy that ignores every flag, then the sum with `1E(Etiny-1)` when that left
the value unchanged; the caller's flags are untouched. -/
theorem nextPlus_fin_run (c : Ctx) (s : Bool) (co : Nat) (e : Int) (fl : List Signal) :
    (nextPlus c (.fin s co e)).run fl =
      match (fix (quietCtx c .ceiling) (.fin s co e)).run fl with
      | .error x => .error x
      | .ok (v, fl2) =>
        if cmpVal v (.fin s co e) ≠ .eq then .ok (v, fl)
        else match (add (quietCtx c .ceiling) (.fin s co e)
            (.fin false 1 ((quietCtx c .ceiling).etiny - 1))).run fl2 with
          | .error x => .error x
          | .ok (y, _) => .ok (y, fl) := by
  simp only [nextPlus, checkNans, isinfinity, StateT.run, bind, StateT.bind, pure, StateT.pure,
    Except.bind, Except.pure]
  simp only [show ¬ ((0 : Int) = 1) by decide, show ¬ ((0 : Int) = -1) by decide, ↓reduceIte]
  unfold quietly
  simp only [StateT.bind, bind, Except.bind, pure, Except.pure]
  cases fix (quietCtx c .ceiling) (.fin s co e) fl with
  | error x => rfl
  | ok p =>
    obtain ⟨v, fl2⟩ := p
    simp only
    by_cases hc : cmpVal v (.fin s co e) ≠ .eq
    · simp only [hc, ↓reduceIte, ne_eq, not_false_eq_true]; rfl
    · simp only [hc, ↓reduceIte]
      cases add (quietCtx c .ceiling) (.fin s co e) (.fin false 1 ((quietCtx c .ceiling).etiny - 1)) fl2 with
      | error x => rfl
      | ok p => rfl

theorem ordOf_eq_iff (x y : Int) : ordOf x y = .eq ↔ x = y := by
  unfold ordOf
  by_cases h1 : x < y
  · simp only [h1, ↓reduceIte, reduceCtorEq, false_iff]; omega
  · by_cases h2 : x = y <;> simp [h1, h2]

theorem scl_split (n : Bool) (c : Nat) (e m L : Int) (h1 : m ≤ e) (h2 : L ≤ m) :
    scl n c e L = sgnVal n (c * 10 ^ (e - m).toNat) * ((10 ^ (m - L).toNat : Nat) : Int) := by
  have : (e - L).toNat = (e - m).toNat + (m - L).toNat := by omega
  simp only [scl, sgnVal, this, Nat.pow_add, ← Nat.mul_assoc]
  cases n <;> simp [Int.natCast_mul, Int.neg_mul]

/-- `_cmp` finds two finite values equal exactly when they agree scaled to any lower exponent. -/
theorem finOrder_eq_iff (n1 : Bool) (c1 : Nat) (e1 : Int) (n2 : Bool) (c2 : Nat) (e2 L : Int)
    (h1 : L ≤ e1) (h2 : L ≤ e2) :
    finOrder n1 c1 e1 n2 c2 e2 = .eq ↔ scl n1 c1 e1 L = scl n2 c2 e2 L := by
  unfold finOrder
  rw [ordOf_eq_iff, scl_split n1 c1 e1 (min e1 e2) L (by omega) (by omega),
    scl_split n2 c2 e2 (min e1 e2) L (by omega) (by omega)]
  have hD : ((10 ^ (min e1 e2 - L).toNat : Nat) : Int) ≠ 0 := by
    have := pow10_pos (min e1 e2 - L).toNat; omega
  constructor
  · intro h; rw [h]
  · intro h; exact Int.eq_of_mul_eq_mul_right hD h

theorem scl_natAbs (x L : Int) : scl (decide (x < 0)) x.natAbs L L = x := by
  by_cases hx : x < 0 <;> simp [scl, hx] <;> omega

theorem scl_zero (s : Bool) (e L : Int) : scl s 0 e L = 0 := by cases s <;> simp [scl]

/-- The exact sum `next_plus` forms, at the lower exponent `L = min(e, Etiny - 1)`. -/
theorem exactSum_next (c : Ctx) (s : Bool) (co : Nat) (e : Int) :
    exactSum s co e false 1 (c.etiny - 1) = scl s co e (min e (c.etiny - 1)) + gapd c (min e (c.etiny - 1)) := by
  cases s <;> simp [exactSum, scl, gapd]

theorem grid_ne_zero {c : Ctx} {L : Int} (hL : L < c.etiny) (u : Int) : u * gapD c L + gapd c L ≠ 0 := by
  have hD := gapD_eq hL
  have hd := gapd_pos c L
  intro h
  by_cases hu : 0 ≤ u
  · have : 0 ≤ u * gapD c L := Int.mul_nonneg hu (by omega)
    omega
  · have h2 : u * gapD c L ≤ (-1) * gapD c L := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    omega

/-- `next_plus` of every finite operand, when it returns, is the least representable value above
the operand (`+Infinity` when there is none), and leaves the flags unchanged. -/
theorem nextPlus_correct_fin (c : Ctx) (fl : List Signal) (hp : 1 ≤ c.prec) (hE : c.emin ≤ c.emax)
    (s : Bool) (co : Nat) (e : Int) (y : Dec) (fl' : List Signal)
    (h : (nextPlus c (.fin s co e)).run fl = .ok (y, fl')) :
    fl' = fl ∧ NextGoal c (min e (c.etiny - 1)) (scl s co e (min e (c.etiny - 1))) y := by
  have hLT : min e (c.etiny - 1) < c.etiny := by omega
  rw [nextPlus_fin_run] at h
  generalize hqd : quietCtx c .ceiling = q at h
  have hqp : 1 ≤ q.prec := by rw [← hqd]; exact hp
  have hqE : q.emin ≤ q.emax := by rw [← hqd]; exact hE
  have hqr : q.rounding = .ceiling := by rw [← hqd]; rfl
  have hqt : q.traps = [] := by rw [← hqd]; rfl
  have hqT : q.etiny = c.etiny := by rw [← hqd]; rfl
  have hfin : ∀ y X, CeilGoal q (min e (c.etiny - 1)) X y → CeilGoal c (min e (c.etiny - 1)) X y := by
    intro y X hg; subst hqd; exact hg
  by_cases hc : co = 0
  · subst hc
    have hz := (fixExact_proven q fl hqp).2.1 s e
    obtain ⟨ne, fl2, hfz⟩ : ∃ ne fl2, (fix q (.fin s 0 e)).run fl = .ok (.fin s 0 ne, fl2) := by
      rw [hz]
      split <;> split
      all_goals first
        | exact ⟨e, fl, rfl⟩
        | exact ⟨_, _, (sigRun_noTraps q hqt _ fl _).choose_spec⟩
    have hcm : cmpVal (.fin s 0 ne) (.fin s 0 e) = .eq := by simp [cmpVal]
    rw [hfz] at h
    simp only [hcm, ne_eq, not_true_eq_false, ↓reduceIte] at h
    rw [add_zero_left q fl2 hqp s e false 1 (q.etiny - 1) (by decide), hqT] at h
    generalize hE2 : max (min e (c.etiny - 1)) (c.etiny - 1 - ↑q.prec - 1) = E2 at h
    cases hfs : fixSpec q false (1 * 10 ^ (c.etiny - 1 - E2).toNat) E2 fl2 with
    | error x => rw [hfs] at h; exact absurd h (by simp)
    | ok p =>
      obtain ⟨y', fl3⟩ := p
      rw [hfs] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨rfl, ?_⟩
      have hg := ceil_fixSpec q hqp hqE hqr hqt false _ E2 (min e (c.etiny - 1))
        (Nat.mul_ne_zero (by decide) (Nat.pos_iff_ne_zero.mp (pow10_pos _)))
        (by omega) (by omega) fl2 fl3 y' hfs
      have hv : scl false (1 * 10 ^ (c.etiny - 1 - E2).toNat) E2 (min e (c.etiny - 1)) =
          scl s 0 e (min e (c.etiny - 1)) + gapd c (min e (c.etiny - 1)) := by
        rw [scl_zero]
        have : (c.etiny - 1 - E2).toNat + (E2 - min e (c.etiny - 1)).toNat =
            (c.etiny - 1 - min e (c.etiny - 1)).toNat := by omega
        simp only [scl, gapd, Bool.false_eq_true, ↓reduceIte, Nat.one_mul, ← Nat.pow_add, this]
        omega
      rw [hv] at hg
      exact next_of_ceil_add hLT ⟨0, by rw [scl_zero, Int.zero_mul]⟩ (hfin _ _ hg)
  · have hfx := fixExact_fin q s co e fl hqp hc
    rw [hfx] at h
    cases hfs : fixSpec q s co e fl with
    | error x => rw [hfs] at h; exact absurd h (by simp)
    | ok p =>
      obtain ⟨v, fl2⟩ := p
      rw [hfs] at h
      simp only at h
      have hg := hfin _ _ (ceil_fixSpec q hqp hqE hqr hqt s co e (min e (c.etiny - 1)) hc (by omega)
        (by omega) fl fl2 v hfs)
      by_cases hcmp : cmpVal v (.fin s co e) ≠ .eq
      · simp only [hcmp, ne_eq, not_false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, next_of_ceil_ne hg ?_⟩
        intro sv cv ev hv hT heq
        subst hv
        rw [cmpVal_fin_exact, ne_eq, finOrder_eq_iff sv cv ev s co e (min e (c.etiny - 1)) (by omega)
          (by omega)] at hcmp
        exact hcmp heq
      · simp only [hcmp, ne_eq, not_false_eq_true, ↓reduceIte, Decidable.not_not] at h
        simp only [ne_eq, Decidable.not_not] at hcmp
        -- the rounding kept the value: it is finite, on the grid of 10^Etiny
        obtain ⟨u, hu⟩ : ∃ u, scl s co e (min e (c.etiny - 1)) = u * gapD c (min e (c.etiny - 1)) := by
          rcases hg with ⟨rfl, _⟩ | ⟨sv, cv, ev, rfl, h1, _, _, _⟩
          · simp [cmpVal] at hcmp
          · rw [cmpVal_fin_exact, finOrder_eq_iff sv cv ev s co e (min e (c.etiny - 1)) (by omega)
              (by omega)] at hcmp
            obtain ⟨w, hw⟩ := fin_grid c (min e (c.etiny - 1)) sv cv ev h1 (by omega)
            exact ⟨w, by rw [← hcmp, hw]⟩
        cases hadd : (add q (.fin s co e) (.fin false 1 (q.etiny - 1))).run fl2 with
        | error x => rw [hadd] at h; exact absurd h (by simp)
        | ok p =>
        obtain ⟨y', fl3⟩ := p
        rw [hadd] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, ?_⟩
        rw [add_fin_exact q fl2 hqp s co e false 1 (q.etiny - 1) hc (by decide), hqT] at hadd
        have hsum := exactSum_next c s co e
        split at hadd
        · exact absurd hadd (by simp)
        split at hadd
        · exact absurd hadd (by simp)
        split at hadd
        · rename_i h0
          rw [hsum, hu] at h0
          exact absurd h0 (grid_ne_zero hLT u)
        rename_i h0
        split at hadd
        · exact absurd hadd (by simp)
        have hg2 := hfin _ _ (ceil_fixSpec q hqp hqE hqr hqt _ _ _ (min e (c.etiny - 1))
          (by intro hz; exact h0 (Int.natAbs_eq_zero.mp hz)) (Int.le_refl _) (by omega) fl2 fl3 _ hadd)
        rw [scl_natAbs, hsum] at hg2
        exact next_of_ceil_add hLT ⟨u, hu⟩ hg2

/-! ## `next_plus` returns below the int/str limit -/

/-- `_fix` in a context that traps nothing and whose `prec + 1` is within the int/str limit
always returns. -/
theorem fixSpec_ok (q : Ctx) (hp : 1 ≤ q.prec) (htr : q.traps = []) (hlim : q.prec + 1 ≤ maxStrDigits)
    (neg : Bool) (co : Nat) (e : Int) (hc : co ≠ 0) (fl : List Signal) :
    ∃ r, fixSpec q neg co e fl = .ok r := by
  unfold fixSpec
  simp only
  split
  · exact ⟨_, (sigRun_noTraps q htr _ fl _).choose_spec⟩
  · split
    · split
      · exact ⟨_, (sigRun_noTraps q htr _ fl _).choose_spec⟩
      · exact ⟨_, (sigRun_noTraps q htr _ fl _).choose_spec⟩
    · rename_i _ hk
      split
      · rename_i hbad
        exfalso
        have hnd := numDigits_bounds hc
        generalize hk' : (max ((numDigits co : Int) + e - q.prec) (q.emin - q.prec + 1) - e).toNat = k at hbad
        have hq0 : co / 10 ^ k < 10 ^ q.prec := by
          rw [Nat.div_lt_iff_lt_mul (pow10_pos k), ← Nat.pow_add]
          exact Nat.lt_of_lt_of_le hnd.2 (pow10_le (by omega))
        have h1 := roundSpec_le q.rounding neg (co / 10 ^ k) (co % 10 ^ k) (10 ^ k)
        have h2 : roundSpec q.rounding neg (co / 10 ^ k) (co % 10 ^ k) (10 ^ k) < 10 ^ (q.prec + 1) := by
          have : 10 ^ q.prec < 10 ^ (q.prec + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
          omega
        have := (numDigits_le_iff (by omega)).mpr h2
        omega
      · exact ⟨_, (sigRun_noTraps q htr _ fl _).choose_spec⟩

theorem natAbs_sum_le (s : Bool) (a b : Nat) :
    ((if s then -1 else 1) * (a : Int) + 1 * (b : Int)).natAbs ≤ a + b := by
  cases s <;> simp <;> omega

theorem numDigits_le_of_lt {n j : Nat} (hj : 0 < j) (h : n < 10 ^ j) : numDigits n ≤ j :=
  (numDigits_le_iff hj).mpr h

/-- The digits `__add__` formats for `x + 1E(eb)` (`str(result.int)` after `_normalize`) are at
most the operand's digits plus `prec + 3`. -/
theorem workDigits_le (p : Nat) (hp : 1 ≤ p) (s : Bool) (co : Nat) (hc : co ≠ 0) (e eb : Int) :
    (numDigits (exactSum s co e false 1 eb).natAbs : Int) + min e eb - addWorkExp p co e 1 eb ≤
      numDigits co + p + 3 := by
  have hnd := numDigits_bounds hc
  have hS := natAbs_sum_le s (co * 10 ^ (e - min e eb).toNat) (1 * 10 ^ (eb - min e eb).toNat)
  have hsum : exactSum s co e false 1 eb =
      (if s then -1 else 1) * ((co * 10 ^ (e - min e eb).toNat : Nat) : Int) +
        1 * ((1 * 10 ^ (eb - min e eb).toNat : Nat) : Int) := by
    simp [exactSum]
  rw [hsum]
  generalize hN : ((if s then -1 else 1) * ((co * 10 ^ (e - min e eb).toNat : Nat) : Int) +
        1 * ((1 * 10 ^ (eb - min e eb).toNat : Nat) : Int)).natAbs = N at hS
  have h1 : numDigits (1 : Nat) = 1 := rfl
  simp only [addWorkExp, normExp, normSub, normX, h1]
  by_cases hlt : e < eb
  · -- the operand 1E(eb) has the larger exponent
    simp only [hlt, ↓reduceIte]
    obtain ⟨d, hd⟩ : ∃ d : Nat, (d : Int) = eb - e := ⟨(eb - e).toNat, by omega⟩
    have e1 : (e - min e eb).toNat = 0 := by omega
    have e2 : (eb - min e eb).toNat = d := by omega
    rw [e1, e2] at hS
    simp only [Nat.pow_zero, Nat.mul_one, Nat.one_mul] at hS
    split
    · rename_i hsub
      have hco : co < 10 ^ (d - 1) := Nat.lt_of_lt_of_le hnd.2 (pow10_le (by omega))
      have hd1 : 10 ^ d = 10 * 10 ^ (d - 1) := by
        rw [← Nat.pow_succ']; congr 1; omega
      have : N < 10 ^ (d + 1) := by rw [Nat.pow_succ, hd1]; omega
      have := numDigits_le_of_lt (by omega) this
      omega
    · rename_i hsub
      have hmx : co + 10 ^ d < 10 ^ (max (numDigits co) d + 1) := by
        have a1 : co < 10 ^ max (numDigits co) d := Nat.lt_of_lt_of_le hnd.2 (pow10_le (by omega))
        have a2 : 10 ^ d ≤ 10 ^ max (numDigits co) d := pow10_le (by omega)
        rw [Nat.pow_succ]; omega
      have := numDigits_le_of_lt (by omega) (Nat.lt_of_le_of_lt hS hmx)
      omega
  · simp only [hlt, ↓reduceIte]
    obtain ⟨d, hd⟩ : ∃ d : Nat, (d : Int) = e - eb := ⟨(e - eb).toNat, by omega⟩
    have e1 : (e - min e eb).toNat = d := by omega
    have e2 : (eb - min e eb).toNat = 0 := by omega
    rw [e1, e2] at hS
    simp only [Nat.pow_zero, Nat.mul_one] at hS
    have hb : co * 10 ^ d + 1 < 10 ^ (numDigits co + d + 1) := by
      have a1 : co * 10 ^ d < 10 ^ numDigits co * 10 ^ d := Nat.mul_lt_mul_of_pos_right hnd.2 (pow10_pos d)
      rw [← Nat.pow_add] at a1
      have a2 : 10 ^ (numDigits co + d) < 10 ^ (numDigits co + d + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
      omega
    have := numDigits_le_of_lt (by omega) (Nat.lt_of_le_of_lt hS hb)
    split
    · omega
    · omega

/-- `next_plus` of a finite operand returns, flags untouched, whenever its coefficient has at most
`4300 - prec - 3` digits (beyond that `__add__`'s `str(result.int)` can hit the int/str limit). -/
theorem nextPlus_ok_fin (c : Ctx) (fl : List Signal) (hp : 1 ≤ c.prec) (s : Bool) (co : Nat) (e : Int)
    (hd : numDigits co + c.prec + 3 ≤ maxStrDigits) :
    ∃ y, (nextPlus c (.fin s co e)).run fl = .ok (y, fl) := by
  rw [nextPlus_fin_run]
  generalize hqd : quietCtx c .ceiling = q
  have hqp : 1 ≤ q.prec := by rw [← hqd]; exact hp
  have hqt : q.traps = [] := by rw [← hqd]; rfl
  have hqP : q.prec = c.prec := by rw [← hqd]; rfl
  have hlim : q.prec + 1 ≤ maxStrDigits := by have := numDigits_pos co; omega
  have hzero : ∀ sz ez fl0, ∃ r, (fix q (.fin sz 0 ez)).run fl0 = .ok r := by
    intro sz ez fl0
    rw [(fixExact_proven q fl0 hqp).2.1 sz ez]
    split <;> split
    all_goals first
      | exact ⟨_, rfl⟩
      | exact ⟨_, (sigRun_noTraps q hqt _ fl0 _).choose_spec⟩
  have haddOk : ∀ fl2, ∃ r, (add q (.fin s co e) (.fin false 1 (q.etiny - 1))).run fl2 = .ok r := by
    intro fl2
    by_cases hc : co = 0
    · subst hc
      rw [add_zero_left q fl2 hqp s e false 1 (q.etiny - 1) (by decide)]
      exact fixSpec_ok q hqp hqt hlim _ _ _ (Nat.mul_ne_zero (by decide)
        (Nat.pos_iff_ne_zero.mp (pow10_pos _))) fl2
    · rw [add_fin_exact q fl2 hqp s co e false 1 (q.etiny - 1) hc (by decide)]
      have hw := workDigits_le q.prec hqp s co hc e (q.etiny - 1)
      have h1 : ¬ maxStrDigits < numDigits co := by omega
      have h2 : ¬ maxStrDigits < numDigits 1 := by decide
      simp only [h1, h2, ↓reduceIte]
      split
      · exact hzero _ _ fl2
      · split
        · rename_i hbad; exfalso; omega
        · rename_i hz _
          exact fixSpec_ok q hqp hqt hlim _ _ _ (fun h0 => hz (Int.natAbs_eq_zero.mp h0)) fl2
  by_cases hc : co = 0
  · subst hc
    obtain ⟨⟨v, fl2⟩, hf⟩ := hzero s e fl
    rw [hf]
    simp only
    split
    · exact ⟨_, rfl⟩
    · obtain ⟨⟨y, fl3⟩, ha⟩ := haddOk fl2
      rw [ha]
      exact ⟨y, rfl⟩
  · obtain ⟨⟨v, fl2⟩, hf⟩ := fixSpec_ok q hqp hqt hlim s co e hc fl
    rw [fixExact_fin q s co e fl hqp hc, hf]
    simp only
    split
    · exact ⟨_, rfl⟩
    · obtain ⟨⟨y, fl3⟩, ha⟩ := haddOk fl2
      rw [ha]
      exact ⟨y, rfl⟩

end PyLean.Decimal
