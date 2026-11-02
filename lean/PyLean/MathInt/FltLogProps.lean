import PyLean.MathInt.FltWrap
import PyLean.MathInt.FltLog
import PyLean.Binary64.Props2

/-!
# Properties: `log`, `log2`, `log10`

`m_log`, `m_log2`, `m_log10`, `loghelper_int`, `loghelper`, `math_log`, `math_log2`, `math_log10`
(Modules/mathmodule.c:628-707, 1573-1705), for every C library `log` that is sane on positive
finite numbers: the int path agrees with the float path, ints beyond the float range work,
objects with `__index__` behave as the int they stand for (the 3.15 retry), the special values
are those of C99 Annex F with `ValueError` for invalid arguments, and `log2` is exact on powers of
two.
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64 PyLean.Binary64.F64

/-- A C library logarithm that, on a positive finite argument, returns a finite number and leaves
`errno` alone. (Every logarithm of a positive finite double is finite and well inside the range.) -/
def SaneLog (f : CFun1) : Prop :=
  ∀ x : F64, x.isFinite = true → F64.lt c0 x = true → (f x).1.isFinite = true ∧ (f x).2 = .zero

/-- The facts about one of `math.log` (one argument), `math.log2`, `math.log10`, built on the C
function `f`. -/
def LogFacts (f : CFun1) (pub : Arg → Py F64) : Prop :=
  -- the int path and the float path agree on every int that converts to a float
  (∀ n x, 0 < n → PyLong_AsDouble n = .ok x → pub (.int n) = pub (.float x)) ∧
  -- a positive int never raises, however large
  (∀ n, 0 < n → ∃ v, pub (.int n) = .ok v) ∧
  -- an object with `__index__` (and no `__float__`) is the int it returns
  (∀ ty fq fl ce tr n, 0 < n →
    pub (.other ty fq none (some (.ok (.int n))) fl ce tr) = pub (.int n)) ∧
  (∀ ty fq fl ce tr e, pub (.other ty fq none (some (.error e)) fl ce tr) = .error e) ∧
  -- invalid arguments raise `ValueError`
  (∀ n, n ≤ 0 → pub (.int n) = .error (.valueError "expected a positive input")) ∧
  (∀ ty fq fl ce tr n, n ≤ 0 → (pub (.other ty fq none (some (.ok (.int n))) fl ce tr)).raises "ValueError") ∧
  (∀ x : F64, x.isNaN = false → F64.le x c0 = true → (pub (.float x)).raises "ValueError") ∧
  -- special values
  (∀ x : F64, x.isNaN = true → pub (.float x) = .ok x) ∧
  pub (.float (F64.inf false)) = .ok (F64.inf false) ∧
  -- otherwise the C library's value, unaltered
  (∀ x : F64, x.isFinite = true → F64.lt c0 x = true → pub (.float x) = .ok (f x).1)

/-- `math.log`, `math.log2` and `math.log10`, for every sane C library logarithm; and
`math.log(x, base)` is `log(x) / log(base)` as Python divides floats (Doc/library/math.rst:
"calculated as `log(x)/log(base)`"), `ZeroDivisionError` for base `1`. -/
def LogTwins : Prop :=
  ∀ f : CFun1, SaneLog f →
    LogFacts f (fun o => math_log f [o]) ∧ LogFacts f (math_log2 f) ∧ LogFacts f (math_log10 f) ∧
    ∀ a b, math_log f [a, b] =
      (do
        let num ← math_log f [a]
        let den ← math_log f [b]
        match float_div (.float num) (.float den) with
        | .ok (some q) => .ok q
        | .ok none => .error (.typeError "unreachable")
        | .error e => .error e)

/-- `math.log2(2**k)` is exactly `k`, for a C `log2` exact on the powers of two a double holds
(as glibc's is), for every `k` up to `2 ** 53 - 2`; past `2 ** 1023` the int path computes
`fma(log2(2.0), e, log2(0.5))`. (`2 ** (2 ** 53)` would take a petabyte; past that bound the
conversion of the exponent to `double` rounds.) Objects with `__index__` returning `2**k` too. -/
def Log2PowersOfTwo : Prop :=
  ∀ f : CFun1, SaneLog f →
    (∀ j : Int, -1074 ≤ j → j ≤ 1023 → f (ofRat (pw j)) = (F64.ofInt j, .zero)) →
    ∀ k : Nat, k + 1 < 2 ^ 53 →
      math_log2 f (.int (2 ^ k)) = .ok (F64.ofInt k) ∧
      ∀ ty fq fl ce tr, math_log2 f (.other ty fq none (some (.ok (.int (2 ^ k)))) fl ce tr) =
        .ok (F64.ofInt k)

/-! ## Proofs -/

theorem c0_facts : c0.isFinite = true ∧ c0.isZero = true ∧ c0.toRat = 0 ∧ c0.isNaN = false ∧
    c0.isInf = false := by decide +kernel

theorem asDouble_int (n : Int) : asDouble (.int n) = PyLong_AsDouble n := rfl

/-- The three wrappers agree on special values. -/
structure WrapSpec (w : CFun1) (f : CFun1) : Prop where
  pos : ∀ x : F64, x.isFinite = true → F64.lt c0 x = true → w x = f x
  zero : ∀ x : F64, x.isZero = true → w x = (F64.neg cInf, .edom)
  neg : ∀ x : F64, x.isFinite = true → F64.lt x c0 = true → w x = (cNaN, .edom)
  nan : ∀ x : F64, x.isNaN = true → w x = (x, .zero)
  pinf : w (F64.inf false) = (F64.inf false, .zero)
  ninf : w (F64.inf true) = (cNaN, .edom)

theorem lt_c0_of_zero {x : F64} (hz : x.isZero = true) : F64.lt c0 x = false ∧ F64.lt x c0 = false := by
  have hf := isFinite_of_isZero hz
  rw [lt_of_finite c0_facts.1 hf, lt_of_finite hf c0_facts.1, toRat_of_isZero hz, c0_facts.2.2.1]
  simp

theorem inf_facts : (F64.inf false).isFinite = false ∧ (F64.inf false).isNaN = false ∧
    (F64.inf false).isInf = true ∧ F64.lt c0 (F64.inf false) = true ∧
    (F64.inf true).isFinite = false ∧ (F64.inf true).isNaN = false ∧
    (F64.inf true).isInf = true ∧ F64.lt c0 (F64.inf true) = false := by decide +kernel

theorem nan_facts : cNaN.isNaN = true ∧ (F64.neg cInf).isInf = true ∧ (F64.neg cInf).isNaN = false := by
  decide +kernel

theorem wrap_log (f : CFun1) : WrapSpec (m_log f) f where
  pos x hf hp := by simp [m_log, hf, hp]
  zero x hz := by
    have hf := isFinite_of_isZero hz
    simp [m_log, hf, (lt_c0_of_zero hz).1, isZeroC_eq, hz]
  neg x hf hn := by
    have hp : F64.lt c0 x = false := by
      rw [lt_of_finite c0_facts.1 hf] at *; rw [lt_of_finite hf c0_facts.1] at hn
      simp at hn ⊢; grind
    have hz : x.isZero = false := by
      cases h : x.isZero
      · rfl
      · rw [(lt_c0_of_zero h).2] at hn; cases hn
    simp [m_log, hf, hp, isZeroC_eq, hz]
  nan x hn := by
    have : x.isFinite = false := by
      cases h : x.isFinite
      · rfl
      · rw [isNaN_false_of_finite h] at hn; cases hn
    simp [m_log, this, hn]
  pinf := by simp [m_log, inf_facts]
  ninf := by simp [m_log, inf_facts]

theorem wrap_log10 (f : CFun1) : WrapSpec (m_log10 f) f where
  pos x hf hp := by simp [m_log10, hf, hp]
  zero x hz := by
    have hf := isFinite_of_isZero hz
    simp [m_log10, hf, (lt_c0_of_zero hz).1, isZeroC_eq, hz]
  neg x hf hn := by
    have hp : F64.lt c0 x = false := by
      rw [lt_of_finite c0_facts.1 hf] at *; rw [lt_of_finite hf c0_facts.1] at hn
      simp at hn ⊢; grind
    have hz : x.isZero = false := by
      cases h : x.isZero
      · rfl
      · rw [(lt_c0_of_zero h).2] at hn; cases hn
    simp [m_log10, hf, hp, isZeroC_eq, hz]
  nan x hn := by
    have : x.isFinite = false := by
      cases h : x.isFinite
      · rfl
      · rw [isNaN_false_of_finite h] at hn; cases hn
    simp [m_log10, this, hn]
  pinf := by simp [m_log10, inf_facts]
  ninf := by simp [m_log10, inf_facts]

theorem wrap_log2 (f : CFun1) : WrapSpec (m_log2 f) f where
  pos x hf hp := by simp [m_log2, hf, hp]
  zero x hz := by
    have hf := isFinite_of_isZero hz
    simp [m_log2, hf, (lt_c0_of_zero hz).1, isZeroC_eq, hz]
  neg x hf hn := by
    have hp : F64.lt c0 x = false := by
      rw [lt_of_finite c0_facts.1 hf] at *; rw [lt_of_finite hf c0_facts.1] at hn
      simp at hn ⊢; grind
    have hz : x.isZero = false := by
      cases h : x.isZero
      · rfl
      · rw [(lt_c0_of_zero h).2] at hn; cases hn
    simp [m_log2, hf, hp, isZeroC_eq, hz]
  nan x hn := by
    have : x.isFinite = false := by
      cases h : x.isFinite
      · rfl
      · rw [isNaN_false_of_finite h] at hn; cases hn
    simp [m_log2, this, hn]
  pinf := by simp [m_log2, inf_facts]
  ninf := by simp [m_log2, inf_facts]

/-- An int that converts is a positive finite float when positive. -/
theorem pos_conv {n : Int} {x : F64} (hn : 0 < n) (hx : PyLong_AsDouble n = .ok x) :
    x.isFinite = true ∧ F64.lt c0 x = true := by
  obtain ⟨hxe, hf⟩ := longAsDouble_ok hx
  subst hxe
  · refine ⟨hf, ?_⟩
    have h1 : (1 : Rat) ≤ (n : Rat) := by
      have : ((1 : Int) : Rat) ≤ (n : Rat) := Rat.intCast_le_intCast.2 (by omega)
      simpa using this
    have := ofRat_ge_one h1 hf
    rw [lt_of_finite c0_facts.1 hf, c0_facts.2.2.1]
    simp only [decide_eq_true_eq]
    exact qlt_le (by decide) this

/-- `math_1` on a converted value `x`, through a wrapper satisfying `WrapSpec`. -/
theorem math1_wrap {w f : CFun1} (hw : WrapSpec w f) (hs : SaneLog f) {o : Arg} {x : F64}
    (hx : asDouble o = .ok x) (msg : Option String) :
    (x.isFinite = true → F64.lt c0 x = true → math_1 o w false msg = .ok (f x).1) ∧
    (x.isNaN = false → F64.le x c0 = true → (math_1 o w false msg).raises "ValueError") ∧
    (x.isNaN = true → math_1 o w false msg = .ok x) ∧
    (x = F64.inf false → math_1 o w false msg = .ok x) := by
  have rules := (math1Rules_proven w false msg o).2 x hx
  obtain ⟨_, hnan, hinf, _, _, hok, _⟩ := rules
  refine ⟨fun hf hp => ?_, fun hn hle => ?_, fun hn => ?_, fun he => ?_⟩
  · rw [hw.pos x hf hp] at hok
    obtain ⟨h1, h2⟩ := hs x hf hp
    exact hok h2 (fun h => by rw [isNaN_false_of_finite h1] at h; cases h)
      (fun h => by rw [isInf_false_of_finite h1] at h; cases h)
  · rcases classify x with h | h | h
    · by_cases hz : x.isZero = true
      · rw [hw.zero x hz] at hinf
        have := hinf nan_facts.2.1 h
        rw [this]; exact ⟨_, rfl, by simp [math_1_domainErr]; split <;> rfl⟩
      · have hz' : x.isZero = false := by simpa using hz
        have hneg : F64.lt x c0 = true := by
          rw [le_of_finite h c0_facts.1] at hle
          rw [lt_of_finite h c0_facts.1]
          simp only [decide_eq_true_eq] at hle ⊢
          have : x.toRat ≠ 0 := fun h0 => by rw [(isZero_iff_toRat h).2 h0] at hz'; cases hz'
          rw [c0_facts.2.2.1] at hle ⊢
          grind
        rw [hw.neg x h hneg] at hnan
        have := hnan nan_facts.1 hn
        rw [this]; exact ⟨_, rfl, by simp [math_1_domainErr]; split <;> rfl⟩
    · have hs' : x.sign = true := by
        cases hsg : x.sign
        · exfalso
          have : x = F64.inf false := by rw [eq_inf_of_isInf h, hsg]
          rw [this] at hle; revert hle; decide +kernel
        · rfl
      have : x = F64.inf true := by rw [eq_inf_of_isInf h, hs']
      subst this
      rw [hw.ninf] at hnan
      have := hnan nan_facts.1 hn
      rw [this]; exact ⟨_, rfl, by simp [math_1_domainErr]; split <;> rfl⟩
    · rw [hn] at h; cases h
  · rw [hw.nan x hn] at hok
    exact hok rfl (fun _ => hn) (fun h => by rw [not_inf_of_nan hn] at h; cases h)
  · subst he
    rw [hw.pinf] at hok
    exact hok rfl (fun h => by rw [inf_facts.2.1] at h; cases h) (fun _ => inf_facts.1)

theorem loghelper_float {w f : CFun1} (hw : WrapSpec w f) (hs : SaneLog f) (x : F64) :
    (x.isFinite = true → F64.lt c0 x = true → loghelper (.float x) w = .ok (f x).1) ∧
    (x.isNaN = false → F64.le x c0 = true → (loghelper (.float x) w).raises "ValueError") ∧
    (x.isNaN = true → loghelper (.float x) w = .ok x) ∧
    (x = F64.inf false → loghelper (.float x) w = .ok x) := by
  obtain ⟨a, b, c, d⟩ := math1_wrap hw hs (o := .float x) (x := x) rfl
    (some "expected a positive input, got ")
  refine ⟨fun hf hp => ?_, fun hn hle => ?_, fun hn => ?_, fun he => ?_⟩
  · simp only [loghelper, Arg.intVal]; rw [a hf hp]
  · obtain ⟨e, he, hc⟩ := b hn hle
    simp only [loghelper, Arg.intVal]; rw [he]
    refine ⟨e, ?_, hc⟩
    split
    · rename_i m hm; cases hm; simp [PyExc.className] at hc
    · rfl
  · simp only [loghelper, Arg.intVal]; rw [c hn]
  · simp only [loghelper, Arg.intVal]; rw [d he]

theorem logFacts {w f : CFun1} (hw : WrapSpec w f) (hs : SaneLog f) (pub : Arg → Py F64)
    (hpub : ∀ o, pub o = loghelper o w) : LogFacts f pub := by
  have intPath : ∀ n x, 0 < n → PyLong_AsDouble n = .ok x → pub (.int n) = .ok (f x).1 := by
    intro n x hn hx
    obtain ⟨hf, hp⟩ := pos_conv hn hx
    rw [hpub]; simp only [loghelper, Arg.intVal, loghelper_int]
    have : ¬ n ≤ 0 := by omega
    simp only [this, ↓reduceIte, hx]
    rw [hw.pos x hf hp]
  refine ⟨fun n x hn hx => ?_, fun n hn => ?_, fun ty fq fl ce tr n hn => ?_,
    fun ty fq fl ce tr e => ?_, fun n hn => ?_, fun ty fq fl ce tr n hn => ?_, fun x hn hle => ?_,
    fun x hn => ?_, ?_, fun x hf hp => ?_⟩
  · rw [intPath n x hn hx, hpub]
    obtain ⟨hf, hp⟩ := pos_conv hn hx
    exact ((loghelper_float hw hs x).1 hf hp).symm
  · rw [hpub]; simp only [loghelper, Arg.intVal, loghelper_int]
    have : ¬ n ≤ 0 := by omega
    simp only [this, ↓reduceIte]
    split <;> exact ⟨_, rfl⟩
  · rw [hpub, hpub (.int n)]
    have hidx : _PyNumber_Index (.other ty fq none (some (.ok (.int n))) fl ce tr) = .ok n := rfl
    have has : asDouble (.other ty fq none (some (.ok (.int n))) fl ce tr) = PyLong_AsDouble n := by
      simp [asDouble, hidx, bind, Except.bind]
    cases hc : PyLong_AsDouble n with
    | ok x =>
      obtain ⟨hf, hp⟩ := pos_conv hn hc
      have := (math1_wrap hw hs (o := .other ty fq none (some (.ok (.int n))) fl ce tr) (x := x)
        (by rw [has, hc]) (some "expected a positive input, got ")).1 hf hp
      simp only [loghelper, Arg.intVal]
      rw [this]
      simp only [loghelper_int]
      have : ¬ n ≤ 0 := by omega
      simp only [this, ↓reduceIte, hc]
      rw [hw.pos x hf hp]
    | error e =>
      have he : e = .overflowError "int too large to convert to float" := longAsDouble_err hc
      subst he
      have hm : math_1 (.other ty fq none (some (.ok (.int n))) fl ce tr) w false
          (some "expected a positive input, got ") =
          .error (.overflowError "int too large to convert to float") := by
        simp [math_1, has, hc, bind, Except.bind]
      simp only [loghelper, Arg.intVal, hm, Arg.indexCheck, Option.isSome_some, ↓reduceIte, hidx,
        bind, Except.bind]
  · rw [hpub]
    simp [loghelper, Arg.intVal, math_1, asDouble, _PyNumber_Index, bind, Except.bind,
      Arg.indexCheck]
    split
    · rename_i m hm
      simp [hm]
    · rfl
  · rw [hpub]; simp [loghelper, Arg.intVal, loghelper_int, show n ≤ 0 from hn]
  · rw [hpub]
    have hidx : _PyNumber_Index (.other ty fq none (some (.ok (.int n))) fl ce tr) = .ok n := rfl
    have has : asDouble (.other ty fq none (some (.ok (.int n))) fl ce tr) = PyLong_AsDouble n := by
      simp [asDouble, hidx, bind, Except.bind]
    cases hc : PyLong_AsDouble n with
    | ok x =>
      have hxle : x.isNaN = false ∧ F64.le x c0 = true := by
        obtain ⟨hxe, hf⟩ := longAsDouble_ok hc
        subst hxe
        · refine ⟨isNaN_false_of_finite hf, ?_⟩
          rw [le_of_finite hf c0_facts.1, c0_facts.2.2.1]
          simp only [decide_eq_true_eq]
          have h1 : (n : Rat) ≤ 0 := by
            have : (n : Rat) ≤ ((0 : Int) : Rat) := Rat.intCast_le_intCast.2 hn
            simpa using this
          have hz : ofRat 0 = c0 := by decide +kernel
          have := ofRat_mono h1 hf (by rw [hz]; exact c0_facts.1)
          rwa [hz, c0_facts.2.2.1] at this
      obtain ⟨e, he, hcls⟩ := (math1_wrap hw hs (o := .other ty fq none (some (.ok (.int n))) fl ce tr)
        (x := x) (by rw [has, hc]) (some "expected a positive input, got ")).2.1 hxle.1 hxle.2
      refine ⟨e, ?_, hcls⟩
      simp only [loghelper, Arg.intVal, he]
      split
      · rename_i m hm; cases hm; simp [PyExc.className] at hcls
      · rfl
    | error e =>
      have he : e = .overflowError "int too large to convert to float" := longAsDouble_err hc
      subst he
      have hm : math_1 (.other ty fq none (some (.ok (.int n))) fl ce tr) w false
          (some "expected a positive input, got ") =
          .error (.overflowError "int too large to convert to float") := by
        simp [math_1, has, hc, bind, Except.bind]
      simp only [loghelper, Arg.intVal, hm, Arg.indexCheck, Option.isSome_some, ↓reduceIte, hidx,
        bind, Except.bind, loghelper_int, show n ≤ 0 from hn]
      exact ⟨_, rfl, rfl⟩
  · rw [hpub]; exact (loghelper_float hw hs x).2.1 hn hle
  · rw [hpub]; exact (loghelper_float hw hs x).2.2.1 hn
  · rw [hpub]; exact (loghelper_float hw hs _).2.2.2 rfl
  · rw [hpub]; exact (loghelper_float hw hs x).1 hf hp

theorem logTwins_proven : LogTwins := by
  intro f hs
  refine ⟨logFacts (wrap_log f) hs _ (fun o => ?_), logFacts (wrap_log2 f) hs _ (fun o => rfl),
    logFacts (wrap_log10 f) hs _ (fun o => rfl), fun a b => ?_⟩
  · simp [math_log, checkPositional, bind, Except.bind]
    cases loghelper o (m_log f) <;> rfl
  · simp only [math_log, checkPositional, List.length_cons, List.length_nil, bind, Except.bind]
    simp only [show ¬ (1 + 1 < 1) by omega, show ¬ (2 < 1 + 1) by omega, show ¬ ((0 + 1) < 1) by omega,
      show ¬ (2 < 0 + 1) by omega, ↓reduceIte, List.getD_cons_zero, List.getD_cons_succ]
    cases h1 : loghelper a (m_log f) with
    | error e => rfl
    | ok num =>
      cases h2 : loghelper b (m_log f) with
      | error e => rfl
      | ok den =>
        have hd : c0 = d0 := rfl
        simp only [pure, Except.pure, float_div, withDoubles, convertToDouble, zeroDiv, hd]
        by_cases hz : F64.eq den d0 = true
        · simp [hz, bind, Except.bind]
        · simp [hz, bind, Except.bind]

theorem cHalf_eq : cHalf = ofRat (pw (-1)) := by decide +kernel
theorem c2_eq : c2 = ofRat (pw 1) := by decide +kernel

theorem two_pow_int_pos (k : Nat) : (0 : Int) < 2 ^ k := by
  have := Nat.two_pow_pos k
  exact_mod_cast this

theorem frexp_pow2 (k : Nat) : _PyLong_Frexp ((2 : Int) ^ k) = (cHalf, (k : Int) + 1) := by
  have hb : bitLength ((2 : Int) ^ k).natAbs = k + 1 := by
    rw [show ((2 : Int) ^ k).natAbs = 2 ^ k by rw [Int.natAbs_pow]; rfl]
    unfold bitLength
    simp [Nat.log2_two_pow]
  have hq : (((2 : Int) ^ k : Int) : Rat) / ((2 ^ (k + 1) : Nat) : Rat) = pw (-1) := by
    have e1 : (((2 : Int) ^ k : Int) : Rat) = ((2 ^ k : Nat) : Rat) := by push_cast; rfl
    rw [e1, ← pw_natCast, ← pw_natCast, Rat.div_def, ← pw_neg, ← pw_add]; congr 1; omega
  have hx : ofRat ((((2 : Int) ^ k : Int) : Rat) / ((2 ^ (k + 1) : Nat) : Rat)) = cHalf := by
    rw [hq, cHalf_eq]
  unfold _PyLong_Frexp
  dsimp only
  rw [hb, hx]
  simp only [show F64.eq cHalf c1 = false by decide +kernel, Bool.false_eq_true, ↓reduceIte]
  push_cast; rfl

theorem log2PowersOfTwo_proven : Log2PowersOfTwo := by
  intro f hs hpow k hk
  have hw := wrap_log2 f
  have main : math_log2 f (.int (2 ^ k)) = .ok (F64.ofInt k) := by
    unfold math_log2
    simp only [loghelper, Arg.intVal, loghelper_int]
    have hpos : ¬ ((2 : Int) ^ k ≤ 0) := by
      have := two_pow_int_pos k; omega
    simp only [hpos, ↓reduceIte]
    have hcast : (((2 : Int) ^ k : Int) : Rat) = pw k := by
      rw [show ((2 : Int) ^ k : Int) = ((2 ^ k : Nat) : Int) by push_cast; rfl, pw_natCast]
      rfl
    by_cases hk1 : k ≤ 1023
    · have hconv : PyLong_AsDouble (2 ^ k) = .ok (ofRat (pw k)) := by
        unfold PyLong_AsDouble
        have hlt : Rat.abs (pw k) < overflowLimit := by
          rw [abs_of_nonneg (Rat.le_of_lt (pw_pos _))]
          have : pw k ≤ pw 1023 := pw_le (by omega)
          have h2 : pw 1023 < overflowLimit := by decide +kernel
          grind
        have hfin := (ofRat_isFinite _).2 hlt
        simp only [F64.ofInt, hcast, isInf_false_of_finite hfin, Bool.false_eq_true, ↓reduceIte]
      rw [hconv]
      have hfin : (ofRat (pw k)).isFinite = true := by
        apply (ofRat_isFinite _).2
        rw [abs_of_nonneg (Rat.le_of_lt (pw_pos _))]
        have : pw k ≤ pw 1023 := pw_le (by omega)
        have h2 : pw 1023 < overflowLimit := by decide +kernel
        grind
      have hp : F64.lt c0 (ofRat (pw k)) = true := by
        have h1 : (1 : Rat) ≤ pw k := by
          have := pw_le (show (0 : Int) ≤ k by omega); rwa [pw_zero] at this
        have := ofRat_ge_one h1 hfin
        rw [lt_of_finite c0_facts.1 hfin, c0_facts.2.2.1]
        simp only [decide_eq_true_eq]; exact qlt_le (by decide) this
      simp only []
      rw [hw.pos _ hfin hp, hpow k (by omega) (by omega)]
    · have hconv : PyLong_AsDouble (2 ^ k) = .error (.overflowError "int too large to convert to float") := by
        unfold PyLong_AsDouble
        have hge : overflowLimit ≤ Rat.abs (pw k) := by
          rw [abs_of_nonneg (Rat.le_of_lt (pw_pos _))]
          have : pw 1024 ≤ pw k := pw_le (by omega)
          exact Rat.le_trans limit_le_pw1024 this
        simp only [F64.ofInt, hcast, (ofRat_isInf _).2 hge, ↓reduceIte]
      rw [hconv]
      simp only []
      have hfrexp : _PyLong_Frexp (2 ^ k) = (cHalf, (k : Int) + 1) := frexp_pow2 k
      rw [hfrexp]
      simp only []
      have hhalf : (cHalf).isFinite = true ∧ F64.lt c0 cHalf = true := by decide +kernel
      have htwo : (c2).isFinite = true ∧ F64.lt c0 c2 = true := by decide +kernel
      rw [hw.pos _ hhalf.1 hhalf.2, hw.pos _ htwo.1 htwo.2, cHalf_eq, c2_eq,
        hpow (-1) (by omega) (by omega), hpow 1 (by omega) (by omega)]
      simp only []
      -- fma(1, k + 1, -1) = k, all exact
      obtain ⟨f1, v1⟩ := ofInt_small (n := 1) (by decide)
      obtain ⟨fm, vm⟩ := ofInt_small (n := -1) (by decide)
      obtain ⟨fk, vk⟩ := ofInt_small (n := (k : Int) + 1) (by omega)
      unfold F64.fma
      simp only [isNaN_false_of_finite f1, isNaN_false_of_finite fk, isNaN_false_of_finite fm,
        isInf_false_of_finite f1, isInf_false_of_finite fk, isInf_false_of_finite fm, Bool.or_false,
        Bool.false_eq_true, ↓reduceIte, v1, vk, vm]
      have hne : ((1 : Int) : Rat) * (((k : Int) + 1 : Int) : Rat) + ((-1 : Int) : Rat) = (k : Rat) := by
        push_cast; grind
      rw [hne]
      by_cases hk0 : (k : Rat) = 0
      · exfalso; have : (k : Nat) = 0 := by exact_mod_cast hk0
        omega
      · simp only [hk0, ↓reduceIte]; rfl
  refine ⟨main, fun ty fq fl ce tr => ?_⟩
  have hfacts := logFacts hw hs (math_log2 f) (fun o => rfl)
  rw [hfacts.2.2.1 ty fq fl ce tr (2 ^ k) (two_pow_int_pos k)]
  exact main

end PyLean.MathInt
