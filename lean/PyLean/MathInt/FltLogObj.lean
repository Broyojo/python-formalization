import PyLean.MathInt.FltLogProps

/-!
# Properties: `loghelper` on arbitrary objects, `math_log`'s arity, logs of huge ints

`loghelper` (Modules/mathmodule.c:1614-1639) sends an `int` (or `bool`) to `loghelper_int`
and everything else through `math_1`, whose conversion is `PyFloat_AsDouble`
(Objects/floatobject.c:247-303); when that raises `OverflowError` and the object has
`__index__`, it retries with the int `__index__` returns. `loghelper_int` (:1582-1612)
computes the log of an int beyond the float range as `fma(func(2.0), e, func(x))`.
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64 PyLean.Binary64.F64

/-- The facts about `loghelper` on objects that are not `int`, for one of `math.log` (one
argument), `math.log2`, `math.log10`. -/
def LogObjFacts (pub : Arg → Py F64) : Prop :=
  -- `bool` is the int it equals
  (∀ b : Bool, pub (.bool b) = pub (.int (if b then 1 else 0))) ∧
  -- a float subclass is its value
  (∀ fq x fl ce tr, pub (.floatSub fq x fl ce tr) = pub (.float x)) ∧
  -- `__float__` returning a float (or a float subclass) is that float; `__index__` is not used
  (∀ ty fq di fl ce tr x, pub (.other ty fq (some (.ok (.float x))) di fl ce tr) = pub (.float x)) ∧
  (∀ ty fq t di fl ce tr x,
    pub (.other ty fq (some (.ok (.floatSub t x))) di fl ce tr) = pub (.float x)) ∧
  -- `__float__` raising `OverflowError` with `__index__` defined: the int `__index__` returns
  (∀ ty fq m fl ce tr n,
    pub (.other ty fq (some (.error (.overflowError m))) (some (.ok (.int n))) fl ce tr) =
      pub (.int n)) ∧
  (∀ ty fq m fl ce tr e,
    pub (.other ty fq (some (.error (.overflowError m))) (some (.error e)) fl ce tr) = .error e) ∧
  -- without `__index__` that `OverflowError` propagates
  (∀ ty fq m fl ce tr,
    pub (.other ty fq (some (.error (.overflowError m))) none fl ce tr) =
      .error (.overflowError m)) ∧
  -- any other exception of `__float__` propagates, whether or not `__index__` exists
  (∀ ty fq e di fl ce tr, (∀ m, e ≠ .overflowError m) →
    pub (.other ty fq (some (.error e)) di fl ce tr) = .error e) ∧
  -- `__float__` returning a non-float
  (∀ ty fq r di fl ce tr, (∀ x, r ≠ .float x) → (∀ t x, r ≠ .floatSub t x) →
    pub (.other ty fq (some (.ok r)) di fl ce tr) =
      .error (.typeError s!"{fq}.__float__() must return a float, not {r.fq}")) ∧
  -- `__index__` (and no `__float__`) returning a non-int
  (∀ ty fq r fl ce tr, (∀ n, r ≠ .int n) → (∀ t n, r ≠ .intSub t n) →
    pub (.other ty fq none (some (.ok r)) fl ce tr) =
      .error (.typeError s!"{fq}.__index__() must return an int, not {r.fq}")) ∧
  -- neither `__float__` nor `__index__`
  (∀ ty fq fl ce tr, pub (.other ty fq none none fl ce tr) =
    .error (.typeError s!"must be real number, not {tpNameCut 50 ty}"))

/-- `math.log`, `math.log2` and `math.log10` on objects that are not ints, for every sane C
logarithm (Doc/library/math.rst; PyFloat_AsDouble's conversion rules, floatobject.c:247-303;
the `OverflowError` retry through `__index__`, mathmodule.c:1621-1636); and `math.log` takes
one or two arguments (`_PyArg_CheckPositional("log", nargs, 1, 2)`, :1650-1651). -/
def LogObjects : Prop :=
  ∀ f : CFun1, SaneLog f →
    LogObjFacts (fun o => math_log f [o]) ∧ LogObjFacts (math_log2 f) ∧
    LogObjFacts (math_log10 f) ∧
    math_log f [] = .error (.typeError "log expected at least 1 argument, got 0") ∧
    (∀ args : List Arg, 3 ≤ args.length →
      math_log f args = .error (.typeError s!"log expected at most 2 arguments, got {args.length}"))

/-- For an int `2**k` beyond the float range, `math.log` and `math.log10` return `k * func(2.0)`
rounded once, for every sane C logarithm with `func(0.5) == -func(2.0)` (true of a correctly
rounded one, as `log(1/2) = -log(2)`). That is `fma(func(2.0), k + 1, func(0.5))` of
`loghelper_int` (mathmodule.c:1597-1606: "Value is ~= x * 2**e, so the log ~= log(x) + log(2) * e"),
with `_PyLong_Frexp(2**k) = (0.5, k + 1)`. Below the float range the C function's own value is
returned instead, which for `log` differs from this rounding at 211 of the `k < 1024` (glibc). -/
def LogBigPowersOfTwo : Prop :=
  ∀ f : CFun1, SaneLog f → (f cHalf).1 = F64.neg (f c2).1 →
    ∀ k : Nat, 1024 ≤ k → k + 1 < 2 ^ 53 →
      math_log f [.int (2 ^ k)] = .ok (ofRat ((k : Rat) * (f c2).1.toRat)) ∧
      math_log10 f (.int (2 ^ k)) = .ok (ofRat ((k : Rat) * (f c2).1.toRat))

/-! ## Proofs -/

theorem math_1_congr {o o' : Arg} (h : asDouble o = asDouble o') (f : CFun1) (c : Bool)
    (m : Option String) : math_1 o f c m = math_1 o' f c m := by
  simp only [math_1, h]

theorem not_ovf_of_raises {r : Py F64} (h : r.raises "ValueError") (m : String) :
    r ≠ .error (.overflowError m) := by
  obtain ⟨e, he, hc⟩ := h
  rw [he]; intro h'; cases h'; simp [PyExc.className] at hc

/-- Through a `WrapSpec` wrapper of a sane log, `math_1` never raises `OverflowError` once the
conversion succeeded. -/
theorem math1_not_ovf {w f : CFun1} (hw : WrapSpec w f) (hs : SaneLog f) {o : Arg} {x : F64}
    (hx : asDouble o = .ok x) (msg : Option String) (m : String) :
    math_1 o w false msg ≠ .error (.overflowError m) := by
  obtain ⟨a, b, c, d⟩ := math1_wrap hw hs hx msg
  rcases classify x with h | h | h
  · by_cases hp : F64.lt c0 x = true
    · rw [a h hp]; intro h'; cases h'
    · apply not_ovf_of_raises
      apply b (isNaN_false_of_finite h)
      rw [le_of_finite h c0_facts.1]
      rw [lt_of_finite c0_facts.1 h] at hp
      simp only [decide_eq_true_eq] at hp ⊢
      rw [c0_facts.2.2.1] at hp ⊢
      grind
  · cases hsg : x.sign
    · have : x = F64.inf false := by rw [eq_inf_of_isInf h, hsg]
      rw [d this]; intro h'; cases h'
    · have : x = F64.inf true := by rw [eq_inf_of_isInf h, hsg]
      apply not_ovf_of_raises
      apply b (not_nan_of_inf h)
      rw [this]; decide +kernel
  · rw [c h]; intro h'; cases h'

/-- `loghelper` on a non-int whose conversion succeeds is `math_1`. -/
theorem loghelper_conv {w f : CFun1} (hw : WrapSpec w f) (hs : SaneLog f) {o : Arg} {x : F64}
    (hint : o.intVal = none) (hx : asDouble o = .ok x) :
    loghelper o w = math_1 (.float x) w false (some "expected a positive input, got ") := by
  have hne := math1_not_ovf hw hs hx (some "expected a positive input, got ")
  have hc : math_1 o w false (some "expected a positive input, got ") =
      math_1 (.float x) w false (some "expected a positive input, got ") :=
    math_1_congr (by rw [hx]; rfl) _ _ _
  have hne' : ∀ m, math_1 (.float x) w false (some "expected a positive input, got ") ≠
      .error (.overflowError m) := by rw [← hc]; exact hne
  unfold loghelper
  rw [hint]
  dsimp only
  rw [hc]
  cases h : math_1 (.float x) w false (some "expected a positive input, got ") with
  | ok v => rfl
  | error e =>
    cases e with
    | overflowError m => exact absurd h (hne' m)
    | _ => rfl

theorem loghelper_float_eq {w f : CFun1} (hw : WrapSpec w f) (hs : SaneLog f) (x : F64) :
    loghelper (.float x) w = math_1 (.float x) w false (some "expected a positive input, got ") :=
  loghelper_conv hw hs rfl rfl

theorem logObjFacts {w f : CFun1} (hw : WrapSpec w f) (hs : SaneLog f) (pub : Arg → Py F64)
    (hpub : ∀ o, pub o = loghelper o w) : LogObjFacts pub := by
  refine ⟨fun b => ?_, fun fq x fl ce tr => ?_, fun ty fq di fl ce tr x => ?_,
    fun ty fq t di fl ce tr x => ?_, fun ty fq m fl ce tr n => ?_, fun ty fq m fl ce tr e => ?_,
    fun ty fq m fl ce tr => ?_, fun ty fq e di fl ce tr he => ?_,
    fun ty fq r di fl ce tr h1 h2 => ?_, fun ty fq r fl ce tr h1 h2 => ?_, fun ty fq fl ce tr => ?_⟩
  · rw [hpub, hpub]; cases b <;> rfl
  · rw [hpub, hpub, loghelper_float_eq hw hs, loghelper_conv hw hs rfl rfl]
  · rw [hpub, hpub, loghelper_float_eq hw hs, loghelper_conv hw hs rfl rfl]
  · rw [hpub, hpub, loghelper_float_eq hw hs, loghelper_conv hw hs rfl rfl]
  · rw [hpub, hpub]
    simp [loghelper, Arg.intVal, math_1, asDouble, bind, Except.bind, Arg.indexCheck,
      _PyNumber_Index]
  · rw [hpub]
    simp [loghelper, Arg.intVal, math_1, asDouble, bind, Except.bind, Arg.indexCheck,
      _PyNumber_Index]
  · rw [hpub]
    simp [loghelper, Arg.intVal, math_1, asDouble, bind, Except.bind, Arg.indexCheck]
  · rw [hpub]
    have hm : math_1 (.other ty fq (some (.error e)) di fl ce tr) w false
        (some "expected a positive input, got ") = .error e := by
      simp [math_1, asDouble, bind, Except.bind]
    unfold loghelper
    simp only [Arg.intVal, hm]
    split
    · rename_i m hm'; cases hm'; exact absurd rfl (he m)
    · rfl
  · rw [hpub]
    have hm : math_1 (.other ty fq (some (.ok r)) di fl ce tr) w false
        (some "expected a positive input, got ") =
        .error (.typeError s!"{fq}.__float__() must return a float, not {r.fq}") := by
      cases r with
      | float x => exact absurd rfl (h1 x)
      | floatSub t x => exact absurd rfl (h2 t x)
      | _ => simp [math_1, asDouble, bind, Except.bind]
    unfold loghelper
    simp only [Arg.intVal, hm]
  · rw [hpub]
    have hm : math_1 (.other ty fq none (some (.ok r)) fl ce tr) w false
        (some "expected a positive input, got ") =
        .error (.typeError s!"{fq}.__index__() must return an int, not {r.fq}") := by
      cases r with
      | int n => exact absurd rfl (h1 n)
      | intSub t n => exact absurd rfl (h2 t n)
      | _ => simp [math_1, asDouble, _PyNumber_Index, Arg.intVal, bind, Except.bind]
    unfold loghelper
    simp only [Arg.intVal, hm]
  · rw [hpub]
    simp [loghelper, Arg.intVal, math_1, asDouble, bind, Except.bind]

theorem logObjects_proven : LogObjects := by
  intro f hs
  refine ⟨logObjFacts (wrap_log f) hs _ (fun o => ?_), logObjFacts (wrap_log2 f) hs _ (fun o => rfl),
    logObjFacts (wrap_log10 f) hs _ (fun o => rfl), ?_, fun args hl => ?_⟩
  · simp [math_log, checkPositional, bind, Except.bind]
    cases loghelper o (m_log f) <;> rfl
  · simp [math_log, checkPositional, bind, Except.bind]
    all_goals decide
  · have h1 : ¬ args.length < 1 := by omega
    have h2 : 2 < args.length := by omega
    simp [math_log, checkPositional, h1, h2, bind, Except.bind]
    all_goals decide

/-- `fma(a, k + 1, -a)` is `k * a` rounded once, for finite `a`. -/
theorem fma_pow2 {a : F64} (ha : a.isFinite = true) (k : Nat) (hk : k + 1 < 2 ^ 53) :
    F64.fma a (F64.ofInt ((k : Int) + 1)) (F64.neg a) = ofRat ((k : Rat) * a.toRat) := by
  obtain ⟨fk, vk⟩ := ofInt_small (n := (k : Int) + 1) (by omega)
  have hna : (F64.neg a).isFinite = true := by rw [neg_isFinite]; exact ha
  unfold F64.fma
  simp only [isNaN_false_of_finite ha, isNaN_false_of_finite fk, isNaN_false_of_finite hna,
    isInf_false_of_finite ha, isInf_false_of_finite fk, isInf_false_of_finite hna, Bool.or_false,
    Bool.false_eq_true, ↓reduceIte, vk, toRat_neg]
  have hq : a.toRat * (((k : Int) + 1 : Int) : Rat) + -a.toRat = (k : Rat) * a.toRat := by
    push_cast; grind
  rw [hq]
  by_cases h0 : (k : Rat) * a.toRat = 0
  · simp only [h0, ↓reduceIte, ofRat_zero]
    -- an exact zero is `+0.0`: the product has the sign of `a` and `-a` the other one
    have hsn : (F64.neg a).sign = !a.sign := (neg_fields a).1
    have hks : (F64.ofInt ((k : Int) + 1)).sign = false := by
      have hp : (((k : Int) + 1 : Int) : Rat) ≠ 0 := by push_cast; grind
      unfold F64.ofInt
      rw [ofRat_sign hp]; simp only [decide_eq_false_iff_not]; push_cast; grind
    rw [hsn, hks]
    cases a.sign <;> rfl
  · simp only [h0, ↓reduceIte]

theorem log_big_pow2 {w f : CFun1} (hw : WrapSpec w f) (hs : SaneLog f)
    (hh : (f cHalf).1 = F64.neg (f c2).1) (k : Nat) (hk1 : 1024 ≤ k) (hk : k + 1 < 2 ^ 53) :
    loghelper (.int (2 ^ k)) w = .ok (ofRat ((k : Rat) * (f c2).1.toRat)) := by
  simp only [loghelper, Arg.intVal, loghelper_int]
  have hpos : ¬ ((2 : Int) ^ k ≤ 0) := by
    have := two_pow_int_pos k; omega
  simp only [hpos, ↓reduceIte]
  have hcast : (((2 : Int) ^ k : Int) : Rat) = pw k := by
    rw [show ((2 : Int) ^ k : Int) = ((2 ^ k : Nat) : Int) by push_cast; rfl, pw_natCast]
    rfl
  have hconv : PyLong_AsDouble (2 ^ k) = .error (.overflowError "int too large to convert to float") := by
    unfold PyLong_AsDouble
    have hge : overflowLimit ≤ Rat.abs (pw k) := by
      rw [abs_of_nonneg (Rat.le_of_lt (pw_pos _))]
      have : pw 1024 ≤ pw k := pw_le (by omega)
      exact Rat.le_trans limit_le_pw1024 this
    simp only [F64.ofInt, hcast, (ofRat_isInf _).2 hge, ↓reduceIte]
  rw [hconv]
  simp only []
  rw [frexp_pow2 k]
  simp only []
  have hhalf : (cHalf).isFinite = true ∧ F64.lt c0 cHalf = true := by decide +kernel
  have htwo : (c2).isFinite = true ∧ F64.lt c0 c2 = true := by decide +kernel
  rw [hw.pos _ hhalf.1 hhalf.2, hw.pos _ htwo.1 htwo.2, hh]
  exact congrArg Except.ok (fma_pow2 (hs c2 htwo.1 htwo.2).1 k hk)

theorem logBigPowersOfTwo_proven : LogBigPowersOfTwo := by
  intro f hs hh k hk1 hk
  refine ⟨?_, log_big_pow2 (wrap_log10 f) hs hh k hk1 hk⟩
  have := log_big_pow2 (wrap_log f) hs hh k hk1 hk
  simp [math_log, checkPositional, bind, Except.bind, this]
  all_goals rfl

end PyLean.MathInt
