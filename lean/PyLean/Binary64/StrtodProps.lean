import PyLean.Binary64.Props4

/-!
Properties of the string conversions: `Python/pystrtod.c` and `_Py_dg_strtod`.
-/

namespace PyLean.Binary64

open F64

/-! ## Scanning -/

theorem scan_stop {s : List Nat} {p : Nat → Bool} {i fuel : Nat} (h : p (at_ s i) = false) :
    scan s p (fuel + 1) i = i := by simp [scan, h]

theorem scanFrom_stop {s : List Nat} {p : Nat → Bool} {i : Nat} (h : p (at_ s i) = false) :
    scanFrom s p i = i := scan_stop h

/-! ## `case_insensitive_match` and `_Py_parse_inf_or_nan` -/

/-- `case_insensitive_match` is true exactly when the lowered input spells `t`. -/
def CaseInsensitiveMatch : Prop :=
  ∀ (s t : List Nat) (i : Nat), case_insensitive_match s i t = true ↔
    ∀ j, j < t.length → toLower (at_ s (i + j)) = t.getD j 0

theorem caseInsensitiveMatch_proven : CaseInsensitiveMatch := by
  intro s t
  induction t with
  | nil => intro i; simp [case_insensitive_match]
  | cons c cs ih =>
    intro i
    simp only [case_insensitive_match, Bool.and_eq_true, beq_iff_eq, ih]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      cases j with
      | zero => simpa using h1
      | succ j =>
        have := h2 j (by simpa using hj)
        have e : i + 1 + j = i + (j + 1) := by omega
        rw [e] at this
        simpa using this
    · intro h
      refine ⟨by simpa using h 0 (by simp), fun j hj => ?_⟩
      have := h (j + 1) (by simpa using hj)
      have e : i + 1 + j = i + (j + 1) := by omega
      rw [e]
      simpa using this

/-- `_Py_parse_inf_or_nan`: on failure the value is `-1.0` and the end is the start;
on success the value is an infinity or a NaN and the end has moved past it. -/
def ParseInfOrNan : Prop :=
  ∀ (s : List Nat) (p : Nat),
    ((_Py_parse_inf_or_nan s p).2 = p ∧ (_Py_parse_inf_or_nan s p).1 = dm1) ∨
    (p < (_Py_parse_inf_or_nan s p).2 ∧
      ((_Py_parse_inf_or_nan s p).1.isInf = true ∨ (_Py_parse_inf_or_nan s p).1.isNaN = true))

theorem qnan_neg_isNaN : (qnan.neg).isNaN = true := by decide +kernel

theorem parseInfOrNan_proven : ParseInfOrNan := by
  intro s p
  unfold _Py_parse_inf_or_nan
  simp only []
  generalize hq : (if at_ s p == 45 then (true, p + 1) else if at_ s p == 43 then (false, p + 1) else (false, p)) = q
  obtain ⟨negate, i⟩ := q
  have hi : p ≤ i := by
    by_cases c1 : (at_ s p == 45) = true
    · simp only [c1, ↓reduceIte, Prod.mk.injEq] at hq; omega
    · by_cases c2 : (at_ s p == 43) = true
      · simp only [c1, c2, ↓reduceIte, Bool.false_eq_true, Prod.mk.injEq] at hq; omega
      · simp only [c1, c2, ↓reduceIte, Bool.false_eq_true, Prod.mk.injEq] at hq; omega
  dsimp only
  by_cases h1 : case_insensitive_match s i [105, 110, 102] = true
  · simp only [h1, ↓reduceIte]
    right
    refine ⟨?_, Or.inl (inf_isInf _)⟩
    split <;> omega
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : case_insensitive_match s i [110, 97, 110] = true
    · simp only [h2, ↓reduceIte]
      right
      refine ⟨by omega, Or.inr ?_⟩
      cases negate
      · exact qnan_facts.2
      · exact qnan_neg_isNaN
    · simp [h2]

/-! ## `_PyOS_ascii_strtod` and `PyOS_string_to_double` -/

/-- `_PyOS_ascii_strtod` keeps a successful `_Py_dg_strtod` result and otherwise tries
`inf` and `nan`. -/
def AsciiStrtodFallback : Prop :=
  ∀ (s : List Nat) (p : Nat) (r : F64) (e : Nat) (er : Bool),
    _Py_dg_strtod s p = some (r, e, er) →
    _PyOS_ascii_strtod s p =
      if e = p then some ((_Py_parse_inf_or_nan s p).1, (_Py_parse_inf_or_nan s p).2, er)
      else some (r, e, er)

theorem asciiStrtodFallback_proven : AsciiStrtodFallback := by
  intro s p r e er h
  simp only [_PyOS_ascii_strtod, h]
  by_cases he : e = p
  · simp [he]
  · simp [he]

/-- With `endptr == NULL`, `PyOS_string_to_double` succeeds only when the conversion
consumed the string up to its NUL. With `overflow_exception` it raises on overflow
instead of returning an infinity. -/
def StringToDoubleContract : Prop :=
  ∀ (s : List Nat) (p : Nat) (o : Option String) (x : F64) (e : Nat),
    PyOS_string_to_double s p false o = some (.ok x, e) → e ≠ p ∧ at_ s e = 0

theorem stringToDoubleContract_proven : StringToDoubleContract := by
  intro s p o x e h
  unfold PyOS_string_to_double at h
  cases hr : _PyOS_ascii_strtod s p with
  | none => simp [hr] at h
  | some r =>
    obtain ⟨v, fp, er⟩ := r
    simp only [hr] at h
    by_cases c : ((fp == p) || (at_ s fp != 0)) = true
    · simp [c] at h
    · have c1 : (fp == p) = false := by
        cases hc : (fp == p)
        · rfl
        · simp [hc] at c
      have c2 : (at_ s fp != 0) = false := by
        cases hc : (at_ s fp != 0)
        · rfl
        · simp [hc] at c
      simp only [c1, c2, Bool.not_false, Bool.true_and, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at h
      have hne : fp ≠ p := by simpa using c1
      have hz : at_ s fp = 0 := by simpa using c2
      split at h
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2]; exact ⟨hne, hz⟩

/-! ## Underscores -/

/-- The copy `underscoreScan` makes is the input up to its first NUL, without
underscores. -/
theorem underscoreScan_copy : ∀ (s : List Nat) (prev i : Nat) (acc dup : List Nat) (st p : Nat),
    underscoreScan s prev i acc = some (dup, st, p) →
    dup = acc.reverse ++ (s.takeWhile (· != 0)).filter (· != 95) := by
  intro s
  induction s with
  | nil => intro prev i acc dup st p h; simp [underscoreScan] at h; simp [h.1]
  | cons c cs ih =>
    intro prev i acc dup st p h
    unfold underscoreScan at h
    by_cases hc : c = 0
    · subst hc; simp at h; simp [h.1]
    · have hc' : (c == 0) = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ↓reduceIte] at h
      by_cases h95 : c = 95
      · subst h95
        simp only [beq_self_eq_true, ↓reduceIte] at h
        split at h
        · cases h
        · rw [ih _ _ _ _ _ _ h]; simp
      · have h95' : (c == 95) = false := by simpa using h95
        simp only [h95', Bool.false_eq_true, ↓reduceIte] at h
        split at h
        · cases h
        · rw [ih _ _ _ _ _ _ h]
          simp [hc, h95]

/-- With no underscore before the first NUL, `_Py_string_to_number_with_underscores`
hands the input to the inner conversion untouched. With one, a successful scan hands it
the input without underscores. A string that starts with an underscore raises
`ValueError`. -/
def UnderscoreRule : Prop :=
  ∀ {α : Type} (s : List Nat) (what : String) (inner : List Nat → Nat → Py α),
    ((s.takeWhile (· != 0)).contains 95 = false →
      _Py_string_to_number_with_underscores s what inner = inner s s.length) ∧
    (∀ dup st p, underscoreScan s 0 0 [] = some (dup, st, p) →
      dup = (s.takeWhile (· != 0)).filter (· != 95)) ∧
    (s.head? = some 95 →
      _Py_string_to_number_with_underscores s what inner =
        .error (.valueError s!"~could not convert string to {what}: "))

theorem underscoreRule_proven : UnderscoreRule := by
  intro α s what inner
  refine ⟨?_, ?_, ?_⟩
  · intro h
    unfold _Py_string_to_number_with_underscores
    simp only [h, Bool.not_false, ↓reduceIte]
  · intro dup st p h
    simpa using underscoreScan_copy s 0 0 [] dup st p h
  · intro h
    cases s with
    | nil => simp at h
    | cons c cs =>
      simp only [List.head?_cons, Option.some.injEq] at h
      subst h
      simp [_Py_string_to_number_with_underscores, underscoreScan, isDigit]

/-! ## `float(str)` -/

/-- An empty string, or one that is only spaces, raises `ValueError`. -/
def FloatBlankRaises : Prop :=
  ∀ n : Nat, (PyFloat_FromString (.bytes (List.replicate n 32))).raises "ValueError" ∧
    (PyFloat_FromString (.str (List.replicate n 32))).raises "ValueError"

theorem at_replicate {n i : Nat} (h : i < n) : at_ (List.replicate n 32) i = 32 := by
  simp [at_, h]

theorem scanLimit_blank (n : Nat) : ∀ (f i : Nat), i ≤ n → n ≤ i + f →
    float_from_string_inner.scanLimit.go (List.replicate n 32) isSpace n f i = n := by
  intro f
  induction f with
  | zero =>
    intro i h1 h2
    simp only [float_from_string_inner.scanLimit.go]
    omega
  | succ f ih =>
    intro i h1 h2
    unfold float_from_string_inner.scanLimit.go
    by_cases hi : i < n
    · have hs : isSpace 32 = true := by decide
      simp only [hi, decide_true, at_replicate hi, hs, Bool.true_and, ↓reduceIte]
      exact ih (i + 1) (by omega) (by omega)
    · simp only [hi, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      omega

theorem inner_blank (n : Nat) :
    float_from_string_inner (List.replicate n 32) n = strToFloatError := by
  unfold float_from_string_inner float_from_string_inner.scanLimit
  simp only [scanLimit_blank n (n + 1) 0 (by omega) (by omega)]
  simp

theorem blank_no_underscore (n : Nat) :
    ((List.replicate n 32).takeWhile (· != 0)).contains 95 = false := by
  cases hc : ((List.replicate n 32).takeWhile (· != 0)).contains 95
  · rfl
  · exfalso
    have h1 := List.contains_iff_mem.1 hc
    have h2 := (List.takeWhile_sublist (· != 0)).subset h1
    have := List.eq_of_mem_replicate h2
    omega

theorem floatBlankRaises_proven : FloatBlankRaises := by
  intro n
  have key : PyFloat_FromString (.bytes (List.replicate n 32)) = strToFloatError := by
    unfold PyFloat_FromString _Py_string_to_number_with_underscores
    simp only [blank_no_underscore n, Bool.not_false, ↓reduceIte, List.length_replicate]
    exact inner_blank n
  have key2 : PyFloat_FromString (.str (List.replicate n 32)) = strToFloatError := by
    have ht : transformDecimalAndSpace (List.replicate n 32) = List.replicate n 32 := by
      unfold transformDecimalAndSpace
      have : (List.replicate n 32).all (· < 128) = true := by simp
      simp [this]
    unfold PyFloat_FromString
    simp only [ht]
    unfold _Py_string_to_number_with_underscores
    simp only [blank_no_underscore n, Bool.not_false, ↓reduceIte, List.length_replicate]
    exact inner_blank n
  refine ⟨?_, ?_⟩
  · rw [key]; exact ⟨_, rfl, rfl⟩
  · rw [key2]; exact ⟨_, rfl, rfl⟩

/-! ## `_Py_dg_strtod` -/

theorem isDigit_of (c : Nat) (h : isDigit c = false) : (c == 48) = false := by
  simp only [isDigit, Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
  simp; omega

/-- With no sign, digit or point at the start, nothing is consumed and the result is
`0.0`, so that `_PyOS_ascii_strtod` goes on to try `inf` and `nan`. -/
def StrtodNoNumber : Prop :=
  ∀ (s : List Nat) (p : Nat), isDigit (at_ s p) = false → at_ s p ≠ 45 → at_ s p ≠ 43 →
    at_ s p ≠ 46 → _Py_dg_strtod s p = some (d0, p, false)

theorem strtodNoNumber_proven : StrtodNoNumber := by
  intro s p hd h1 h2 h3
  have hz := isDigit_of _ hd
  have h1' : (at_ s p == 45) = false := by simpa using h1
  have h2' : (at_ s p == 43) = false := by simpa using h2
  have h3' : (at_ s p == 46) = false := by simpa using h3
  have e1 : scanFrom s (· == 48) p = p := scanFrom_stop hz
  have e2 : scanFrom s isDigit p = p := scanFrom_stop hd
  simp [_Py_dg_strtod, strtodParse, h1', h2', h3', e1, e2]

/-- The sign is applied last: `strtodValue` on a negative parse is the negated value of
the positive one, with the same `errno`, so `float('-' + s) == -float(s)` holds at every
magnitude, zero and infinity included. -/
def StrtodSign : Prop :=
  ∀ (s : List Nat) (p : Parsed),
    strtodValue s { p with sign := true } =
      (strtodValue s { p with sign := false }).map fun r => (r.1.neg, r.2)

theorem strtodSign_proven : StrtodSign := by
  intro s p
  have e : strtodAbs s { p with sign := true } = strtodAbs s { p with sign := false } := rfl
  unfold strtodValue
  rw [e]
  cases strtodAbs s { p with sign := false } <;> rfl

theorem tens_exact : ∀ e, e < 23 → (tens e).isFinite = true ∧ (tens e).toRat = ((10 ^ e : Nat) : Rat) := by
  decide +kernel

theorem ofRat_mul_nonzero {x y : F64} (hx : x.isFinite = true) (hy : y.isFinite = true)
    (h : x.toRat * y.toRat ≠ 0) : F64.mul x y = ofRat (x.toRat * y.toRat) := by
  rw [mul_of_finite hx hy]; simp [h]

/-- The Clinger fast path of `_Py_dg_strtod`: for a significand below `10 ** 15` and an
exponent up to `22` in size, one floating-point operation gives the correctly rounded
result. -/
def StrtodFastPathExact : Prop :=
  ∀ (n nd e : Nat), 0 < n → n < 10 ^ 15 → nd ≤ 15 → e ≤ 22 →
    strtodFast (ofInt n) nd e = some (ofRat ((n : Rat) * ((10 ^ e : Nat) : Rat))) ∧
    (0 < e → strtodFast (ofInt n) nd (-(e : Int)) = some (ofRat ((n : Rat) / ((10 ^ e : Nat) : Rat))))

theorem strtodFastPathExact_proven : StrtodFastPathExact := by
  intro n nd e h0 h1 hnd he
  have hsmall : (n : Int).natAbs < 2 ^ 53 := by
    have : (n : Int).natAbs = n := by omega
    rw [this]; omega
  obtain ⟨f1, f2⟩ := ofInt_small hsmall
  obtain ⟨t1, t2⟩ := tens_exact e (by omega)
  have hnr : ((n : Int) : Rat) = (n : Rat) := Rat.intCast_natCast n
  rw [hnr] at f2
  have hn0 : (n : Rat) ≠ 0 := Rat.ne_of_gt (natCast_pos' h0)
  have ht0 : ((10 ^ e : Nat) : Rat) ≠ 0 := Rat.ne_of_gt (natCast_pos' (Nat.pow_pos (by omega)))
  have hnd' : (nd ≤ 15) = True := by simp [hnd]
  constructor
  · unfold strtodFast
    simp only [hnd', ↓reduceIte]
    by_cases hz : e = 0
    · subst hz
      simp [ofInt]
      rfl
    · have hz' : ((e : Int) == 0) = false := by simpa using hz
      have hp : (0 : Int) < e := by omega
      have hle : (e : Int) ≤ 22 := by omega
      have hmul := ofRat_mul_nonzero f1 t1 (by
        rw [f2, t2]
        exact Rat.ne_of_gt (Rat.mul_pos (natCast_pos' h0) (natCast_pos' (Nat.pow_pos (by omega)))))
      simp only [hz', Bool.false_eq_true, ↓reduceIte, hp, hle, Int.toNat_natCast]
      rw [hmul, f2, t2]
  · intro hp
    unfold strtodFast
    simp only [hnd', ↓reduceIte]
    have hz' : ((-(e : Int)) == 0) = false := by simp; omega
    have hn : ¬ (0 : Int) < -(e : Int) := by omega
    have hg : (-22 : Int) ≤ -(e : Int) := by omega
    have hk : (-(-(e : Int))).toNat = e := by omega
    simp only [hz', Bool.false_eq_true, ↓reduceIte, hn, hg, hk]
    have tz : (tens e).isZero = false := by
      cases hc : (tens e).isZero
      · rfl
      · exfalso; rw [toRat_of_isZero hc] at t2; exact ht0 t2.symm
    rw [div_of_finite f1 t1 tz, f2, t2]
    have hq : (n : Rat) / ((10 ^ e : Nat) : Rat) ≠ 0 := by
      intro hc
      have := congrArg (· * ((10 ^ e : Nat) : Rat)) hc
      simp only [Rat.div_mul_cancel ht0, Rat.zero_mul] at this
      exact hn0 this
    simp only [hq, ↓reduceIte]

/-- `bigcomp` chooses between `rv` and `rv + ulp`, as its comment says: dtoa.c:1235-1240. -/
def BigcompChoice : Prop :=
  ∀ (rv : F64) (dig : Nat → Nat) (bc : BCinfo),
    bigcomp rv dig bc = rv ∨ bigcomp rv dig bc = F64.add rv (sulp rv bc.scale)

theorem bigcompRound_choice (rv : F64) (scale : Nat) (dd : Int) (odd : Bool) :
    bigcompRound rv scale dd odd = rv ∨ bigcompRound rv scale dd odd = F64.add rv (sulp rv scale) := by
  unfold bigcompRound
  split
  · right; rfl
  · left; rfl

theorem bigcompChoice_proven : BigcompChoice := by
  intro rv dig bc
  unfold bigcomp
  exact bigcompRound_choice rv bc.scale _ _

end PyLean.Binary64
