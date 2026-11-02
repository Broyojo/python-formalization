import PyLean.MathInt.FltWrap
import PyLean.MathInt.FltGamma
import PyLean.MathInt.FltLogProps

/-!
# Properties: `gamma` and `lgamma`

`m_tgamma`, `m_lgamma` (Modules/mathmodule.c:381-524) through `math_1a`, for every C library
whose `sin`, `cos`, `exp`, `log` and `pow` report nothing but range errors through `errno`:
`gamma(n)` is `(n-1)!` from the table for `n <= 23`, `ValueError` is raised exactly at the
poles (`-inf` too for `gamma`), the special values of C99 Annex F, and `gamma(x)` overflows
for `x > 200`.
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64 PyLean.Binary64.F64

def gfact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * gfact n

/-- A C library function that reports only range errors through `errno` (POSIX: `ERANGE`
on overflow or underflow; `EDOM` only outside the domain, and CPython calls these functions
inside it). -/
def RangeOnly (f : CFun1) : Prop := ∀ x, (f x).2 = .zero ∨ (f x).2 = .erange
def RangeOnly2 (f : CFun2) : Prop := ∀ x y, (f x y).2 = .zero ∨ (f x y).2 = .erange

def GammaLibmErrno (L : GammaLibm) : Prop :=
  RangeOnly L.sin ∧ RangeOnly L.cos ∧ RangeOnly L.exp ∧ RangeOnly L.log ∧ RangeOnly2 L.pow

/-- A pole of the gamma function: a finite integer `<= 0` (both zeros included). -/
def isPole (x : F64) : Prop := x.isFinite = true ∧ F64.le x c0 = true ∧ ∃ n : Int, x.toRat = n

/-- `math.gamma` and `math.lgamma`, for every C library `L`.

* Conversion errors are raised unchanged.
* `gamma(n)` is `(n-1)!` exactly for `n = 1, ..., 23` (the `gamma_integral` table).
* `gamma(nan)` and `lgamma(nan)` are the NaN; `gamma(inf)`, `lgamma(inf)` and `lgamma(-inf)` are
  `inf`; `lgamma(1.0)` and `lgamma(2.0)` are `0.0`.
* `gamma(x)` raises `OverflowError` for every finite `x > 200`.
* When `L` reports only range errors: `gamma(x)` raises `ValueError` exactly when `x` is `-inf`
  or a pole (an integer `<= 0`), and `lgamma(x)` exactly when `x` is a pole. -/
def GammaDoc : Prop := ∀ L : GammaLibm,
  (∀ o e, asDouble o = .error e → math_gamma L o = .error e ∧ math_lgamma L o = .error e) ∧
  (∀ n : Nat, 1 ≤ n → n ≤ 23 → math_gamma L (.float (F64.ofInt n)) = .ok (F64.ofInt (gfact (n - 1)))) ∧
  (∀ x : F64, x.isNaN = true → math_gamma L (.float x) = .ok x ∧ math_lgamma L (.float x) = .ok x) ∧
  math_gamma L (.float (F64.inf false)) = .ok (F64.inf false) ∧
  math_lgamma L (.float (F64.inf false)) = .ok (F64.inf false) ∧
  math_lgamma L (.float (F64.inf true)) = .ok (F64.inf false) ∧
  math_lgamma L (.float c1) = .ok c0 ∧ math_lgamma L (.float c2) = .ok c0 ∧
  (∀ x : F64, x.isFinite = true → F64.lt c200 x = true →
    math_gamma L (.float x) = .error (.overflowError "math range error")) ∧
  (GammaLibmErrno L → ∀ x : F64,
    ((math_gamma L (.float x)).raises "ValueError" ↔ (x = F64.inf true ∨ isPole x)) ∧
    ((math_lgamma L (.float x)).raises "ValueError" ↔ isPole x))

/-! ## `errno` bookkeeping -/

def RangeE (e : Errno) : Prop := e = .zero ∨ e = .erange

theorem after_range {a b : Errno} (ha : RangeE a) (hb : RangeE b) : RangeE (a.after b) := by
  unfold Errno.after
  rcases hb with h | h <;> subst h
  · simpa using ha
  · right; rfl

theorem call1_range {f : CFun1} (hf : RangeOnly f) (x : F64) {e : Errno} (he : RangeE e) :
    RangeE (call1 f x e).2 := after_range he (hf x)

theorem call2_range {f : CFun2} (hf : RangeOnly2 f) (x y : F64) {e : Errno} (he : RangeE e) :
    RangeE (call2 f x y e).2 := after_range he (hf x y)

theorem sinpi_range {L : GammaLibm} (hL : GammaLibmErrno L) (x : F64) {e : Errno} (he : RangeE e) :
    RangeE (m_sinpi L x e).2 := by
  obtain ⟨hs, hc, _, _, _⟩ := hL
  unfold m_sinpi
  simp only []
  split
  · exact call1_range hs _ he
  · exact call1_range hc _ he
  · exact call1_range hs _ he
  · exact call1_range hc _ he
  · exact call1_range hs _ he

theorem zero_range : RangeE .zero := Or.inl rfl
theorem erange_range : RangeE .erange := Or.inr rfl

theorem ite_range {e : Errno} (c : Bool) (he : RangeE e) : RangeE (if c then .erange else e) := by
  split
  · exact erange_range
  · exact he

theorem tgammaLanczos_range {L : GammaLibm} (hL : GammaLibmErrno L) (x absx : F64) :
    RangeE (tgammaLanczos L x absx).2 := by
  have hL' := hL
  obtain ⟨_, _, he, _, hp⟩ := hL
  unfold tgammaLanczos
  simp only []
  apply ite_range
  split
  · split
    · exact call2_range hp _ _ (call1_range he _ (sinpi_range hL' _ zero_range))
    · exact call2_range hp _ _ (call1_range he _ (sinpi_range hL' _ zero_range))
  · split
    · exact call2_range hp _ _ (call1_range he _ zero_range)
    · exact call2_range hp _ _ (call1_range he _ zero_range)

theorem lgammaLanczos_range {L : GammaLibm} (hL : GammaLibmErrno L) (x absx : F64) :
    RangeE (lgammaLanczos L x absx).2 := by
  have hL' := hL
  obtain ⟨_, _, _, hl, _⟩ := hL
  unfold lgammaLanczos
  simp only []
  apply ite_range
  split
  · exact call1_range hl _ (call1_range hl _ (sinpi_range hL' _
      (call1_range hl _ (call1_range hl _ zero_range))))
  · exact call1_range hl _ (call1_range hl _ zero_range)

theorem range_ne_edom {e : Errno} (h : RangeE e) : e ≠ .edom := by
  rcases h with h | h <;> subst h <;> decide

/-! ## Integers among floats -/

theorem eq_floor_iff {x : F64} (hf : x.isFinite = true) :
    F64.eq x (F64.floor x) = true ↔ ∃ n : Int, x.toRat = n := by
  obtain ⟨h1, h2⟩ := floor_value hf
  rw [eq_of_finite hf h1, h2]
  simp only [decide_eq_true_eq]
  constructor
  · intro h; exact ⟨_, h⟩
  · rintro ⟨n, hn⟩
    unfold floorInt; rw [hn, Rat.floor_intCast]

theorem pole_iff {x : F64} (hf : x.isFinite = true) :
    isPole x ↔ (x.isZero = true ∨ (F64.eq x (F64.floor x) = true ∧ F64.lt x c0 = true)) := by
  unfold isPole
  rw [eq_floor_iff hf, le_of_finite hf c0_facts.1, lt_of_finite hf c0_facts.1, c0_facts.2.2.1]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨_, hle, hn⟩
    by_cases hz : x.isZero = true
    · left; exact hz
    · right
      refine ⟨hn, ?_⟩
      have : x.toRat ≠ 0 := fun h0 => hz ((isZero_iff_toRat hf).2 h0)
      grind
  · rintro (hz | ⟨hn, hlt⟩)
    · refine ⟨hf, ?_, 0, ?_⟩
      · rw [toRat_of_isZero hz]; exact Rat.le_refl
      · rw [toRat_of_isZero hz]; rfl
    · exact ⟨hf, Rat.le_of_lt hlt, hn⟩

/-! ## The proofs -/

theorem gamma_errno_iff {L : GammaLibm} (hL : GammaLibmErrno L) (x : F64) :
    RangeE (m_tgamma L x).2 ∨ (m_tgamma L x).2 = .edom ∧ (x = F64.inf true ∨ isPole x) := by
  unfold m_tgamma
  by_cases hf : x.isFinite = true
  · simp only [hf, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    by_cases hz : isZeroC x = true
    · simp only [hz, ↓reduceIte]
      right; refine ⟨by first | rfl | trivial, Or.inr ((pole_iff hf).2 (Or.inl ?_))⟩
      rwa [isZeroC_eq] at hz
    · simp only [hz, Bool.false_eq_true, ↓reduceIte]
      by_cases hn : (F64.eq x (F64.floor x) && F64.lt x c0) = true
      · simp only [hn, ↓reduceIte]
        right; refine ⟨by first | rfl | trivial, Or.inr ((pole_iff hf).2 (Or.inr ?_))⟩
        simpa using hn
      · simp only [hn, Bool.false_eq_true, ↓reduceIte]
        left
        split
        · exact zero_range
        · split
          · exact ite_range _ zero_range
          · split
            · split
              · exact sinpi_range hL _ zero_range
              · exact erange_range
            · exact tgammaLanczos_range hL _ _
  · have hf' : x.isFinite = false := by simpa using hf
    simp only [hf', Bool.not_false, ↓reduceIte]
    split
    · left; exact zero_range
    · right
      rename_i h
      refine ⟨rfl, Or.inl ?_⟩
      rcases classify x with h1 | h1 | h1
      · rw [hf'] at h1; cases h1
      · have hs : x.sign = true := by
          cases hsx : x.sign
          · exfalso; apply h
            rw [eq_inf_of_isInf h1, hsx]; decide +kernel
          · rfl
        rw [eq_inf_of_isInf h1, hs]
      · simp [h1] at h

theorem gamma_pole_edom (L : GammaLibm) {x : F64} (h : x = F64.inf true ∨ isPole x) :
    (m_tgamma L x).2 = .edom := by
  rcases h with h | h
  · subst h
    have : (F64.inf true).isFinite = false ∧ (F64.inf true).isNaN = false ∧
        F64.lt c0 (F64.inf true) = false := by decide +kernel
    simp [m_tgamma, this]
  · have hf := h.1
    unfold m_tgamma
    simp only [hf, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rcases (pole_iff hf).1 h with hz | ⟨hn, hlt⟩
    · simp [isZeroC_eq, hz]
    · by_cases hz : isZeroC x = true
      · simp [hz]
      · simp [hz, hn, hlt]

theorem lgamma_errno_iff {L : GammaLibm} (hL : GammaLibmErrno L) (x : F64) :
    RangeE (m_lgamma L x).2 ∨ (m_lgamma L x).2 = .edom ∧ isPole x := by
  unfold m_lgamma
  split
  · split
    · left; exact zero_range
    · left; exact zero_range
  · rename_i hf
    have hf' : x.isFinite = true := by simpa using hf
    split
    · rename_i hc
      split
      · rename_i hle
        right; refine ⟨by first | rfl | trivial, hf', hle, ?_⟩
        have : F64.eq x (F64.floor x) = true := by simp at hc; exact hc.1
        exact (eq_floor_iff hf').1 this
      · left; exact zero_range
    · dsimp only
      split
      · exact Or.inl (call1_range hL.2.2.2.1 _ zero_range)
      · exact Or.inl (lgammaLanczos_range hL _ _)

theorem lgamma_pole_edom (L : GammaLibm) {x : F64} (h : isPole x) : (m_lgamma L x).2 = .edom := by
  obtain ⟨hf, hle, hn⟩ := h
  have hfl := (eq_floor_iff hf).2 hn
  have hle2 : F64.le x c2 = true := by
    rw [le_of_finite hf (by decide +kernel)]
    rw [le_of_finite hf c0_facts.1, c0_facts.2.2.1] at hle
    have : c2.toRat = 2 := by decide +kernel
    rw [this]; simp only [decide_eq_true_eq] at hle ⊢; grind
  simp [m_lgamma, hf, hfl, hle2, hle]

/-- What `math_1a` does with a `(result, errno)` pair whose `errno` is `0`, `EDOM` or `ERANGE`. -/
theorem math1a_valueError_iff (f : CFun1) (msg : String) (x : F64)
    (h : RangeE (f x).2 ∨ (f x).2 = .edom) :
    (math_1a (.float x) f (some msg)).raises "ValueError" ↔ (f x).2 = .edom := by
  obtain ⟨_, rules⟩ := math1aRules_proven f (some msg) (.float x)
  obtain ⟨hz, hd, hr, _⟩ := rules x rfl
  constructor
  · intro hv
    rcases h with (h | h) | h
    · rw [hz h] at hv; obtain ⟨_, he, _⟩ := hv; cases he
    · rw [hr h] at hv
      obtain ⟨e, he, hc⟩ := hv
      unfold erangeOutcome at he
      split at he
      · cases he
      · cases he; simp [PyExc.className] at hc
    · exact h
  · intro he
    rw [hd he]
    exact ⟨_, rfl, by simp [math_1_domainErr, domainMsg, PyExc.className]⟩

theorem table_facts : ∀ n : Fin 23,
    let x := F64.ofInt ((n : Nat) + 1 : Nat)
    x.isFinite = true ∧ isZeroC x = false ∧ F64.eq x (F64.floor x) = true ∧ F64.lt x c0 = false ∧
    F64.le x NGAMMA_INTEGRAL = true ∧
    gamma_integral.getD (x.truncInt.toNat - 1) c0 = F64.ofInt (gfact n) := by
  decide +kernel

/-- The `err_msg` of `math.gamma` and `math.lgamma`, mathmodule.c:1121, :1125. -/
abbrev gmsg : String := "expected a noninteger or positive integer, got "

theorem gammaDoc_proven : GammaDoc := by
  intro L
  refine ⟨fun o e he => ⟨?_, ?_⟩, fun n h1 h23 => ?_, fun x hn => ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_,
    fun x hf hgt => ?_, fun hL x => ⟨?_, ?_⟩⟩
  · simp [math_gamma, math_1a, he, bind, Except.bind]
  · simp [math_lgamma, math_1a, he, bind, Except.bind]
  · obtain ⟨k, hk⟩ : ∃ k : Fin 23, (k : Nat) + 1 = n := ⟨⟨n - 1, by omega⟩, by simp; omega⟩
    obtain ⟨t1, t2, t3, t4, t5, t6⟩ := table_facts k
    rw [hk] at t1 t2 t3 t4 t5 t6
    have hm : m_tgamma L (F64.ofInt n) = (F64.ofInt (gfact k), .zero) := by
      simp only [m_tgamma, t1, t2, t3, t4, t5, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        Bool.and_false, Bool.and_self]
      rw [t6]
    have := ((math1aRules_proven (m_tgamma L) (some gmsg) (.float (F64.ofInt n))).2 _ rfl).1
    rw [hm] at this
    rw [show n - 1 = (k : Nat) by omega]
    unfold math_gamma; exact this rfl
  · have hf : x.isFinite = false := by
      cases h : x.isFinite
      · rfl
      · rw [isNaN_false_of_finite h] at hn; cases hn
    have hm : m_tgamma L x = (x, .zero) := by simp [m_tgamma, hf, hn]
    have := ((math1aRules_proven (m_tgamma L) (some gmsg) (.float x)).2 _ rfl).1
    rw [hm] at this; unfold math_gamma; exact this rfl
  · have hf : x.isFinite = false := by
      cases h : x.isFinite
      · rfl
      · rw [isNaN_false_of_finite h] at hn; cases hn
    have hm : m_lgamma L x = (x, .zero) := by simp [m_lgamma, hf, hn]
    have := ((math1aRules_proven (m_lgamma L) (some gmsg) (.float x)).2 _ rfl).1
    rw [hm] at this; unfold math_lgamma; exact this rfl
  · have hm : m_tgamma L (F64.inf false) = (F64.inf false, .zero) := by
      simp [m_tgamma, inf_facts]
    have := ((math1aRules_proven (m_tgamma L) (some gmsg) (.float (F64.inf false))).2 _ rfl).1
    rw [hm] at this; unfold math_gamma; exact this rfl
  · have hm : m_lgamma L (F64.inf false) = (F64.inf false, .zero) := by
      simp [m_lgamma, inf_facts]; rfl
    have := ((math1aRules_proven (m_lgamma L) (some gmsg) (.float (F64.inf false))).2 _ rfl).1
    rw [hm] at this; unfold math_lgamma; exact this rfl
  · have hm : m_lgamma L (F64.inf true) = (F64.inf false, .zero) := by
      simp [m_lgamma, inf_facts]; rfl
    have := ((math1aRules_proven (m_lgamma L) (some gmsg) (.float (F64.inf true))).2 _ rfl).1
    rw [hm] at this; unfold math_lgamma; exact this rfl
  · have hc : c1.isFinite = true ∧ F64.eq c1 (F64.floor c1) = true ∧ F64.le c1 c2 = true ∧
        F64.le c1 c0 = false := by decide +kernel
    have hm : m_lgamma L c1 = (c0, .zero) := by simp [m_lgamma, hc]
    have := ((math1aRules_proven (m_lgamma L) (some gmsg) (.float c1)).2 _ rfl).1
    rw [hm] at this; unfold math_lgamma; exact this rfl
  · have hc : c2.isFinite = true ∧ F64.eq c2 (F64.floor c2) = true ∧ F64.le c2 c2 = true ∧
        F64.le c2 c0 = false := by decide +kernel
    have hm : m_lgamma L c2 = (c0, .zero) := by simp [m_lgamma, hc]
    have := ((math1aRules_proven (m_lgamma L) (some gmsg) (.float c2)).2 _ rfl).1
    rw [hm] at this; unfold math_lgamma; exact this rfl
  · have h200 : c200.isFinite = true ∧ c200.toRat = 200 := by decide +kernel
    have hlt := hgt
    rw [lt_of_finite h200.1 hf, h200.2] at hlt
    simp only [decide_eq_true_eq] at hlt
    have hz : isZeroC x = false := by
      rw [isZeroC_eq]; cases h : x.isZero
      · rfl
      · rw [toRat_of_isZero h] at hlt; exact absurd hlt (by decide)
    have hneg : F64.lt x c0 = false := by
      rw [lt_of_finite hf c0_facts.1, c0_facts.2.2.1]; simp; grind
    have hle : F64.le x NGAMMA_INTEGRAL = false := by
      have h23 : NGAMMA_INTEGRAL.isFinite = true ∧ NGAMMA_INTEGRAL.toRat = 23 := by decide +kernel
      rw [le_of_finite hf h23.1, h23.2]; simp; grind
    have habs : F64.abs x = x := by
      unfold F64.abs
      have : x.sign = false := by
        cases hs : x.sign
        · rfl
        · exfalso
          have hz' : x.isZero = false := by rwa [isZeroC_eq] at hz
          have := (toRat_neg_iff_sign hf hz')
          rw [hs] at this; simp at this; grind
      simp [this]
    have hsmall : F64.lt x c1em20 = false := by
      have h20 : c1em20.isFinite = true ∧ c1em20.toRat < 1 := by decide +kernel
      rw [lt_of_finite hf h20.1]; simp; grind
    have hm : m_tgamma L x = (cInf, .erange) := by
      simp [m_tgamma, hf, hz, hneg, hle, habs, hsmall, hgt]
    have := ((math1aRules_proven (m_tgamma L) (some gmsg) (.float x)).2 _ rfl).2.2.1
    rw [hm] at this
    unfold math_gamma
    rw [this rfl]
    decide +kernel
  · have hrel : RangeE (m_tgamma L x).2 ∨ (m_tgamma L x).2 = .edom := by
      rcases gamma_errno_iff hL x with h | h
      · exact Or.inl h
      · exact Or.inr h.1
    unfold math_gamma
    rw [math1a_valueError_iff _ _ x hrel]
    constructor
    · intro he
      rcases gamma_errno_iff hL x with h | h
      · exact absurd he (range_ne_edom h)
      · exact h.2
    · exact gamma_pole_edom L
  · have hrel : RangeE (m_lgamma L x).2 ∨ (m_lgamma L x).2 = .edom := by
      rcases lgamma_errno_iff hL x with h | h
      · exact Or.inl h
      · exact Or.inr h.1
    unfold math_lgamma
    rw [math1a_valueError_iff _ _ x hrel]
    constructor
    · intro he
      rcases lgamma_errno_iff hL x with h | h
      · exact absurd he (range_ne_edom h)
      · exact h.2
    · exact lgamma_pole_edom L

end PyLean.MathInt
