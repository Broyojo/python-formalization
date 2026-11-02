import PyLean.MathInt.FltLemmas

/-!
# Properties: `math_1`, `math_1a`, `math_2`, `is_error`

The error rules the comments above `math_1` (Modules/mathmodule.c:757-785), `math_1a`
(:827-829), `math_2` (:854-879) and `is_error` (:710-713, 725-744) state, for every C
library function: the wrappers turn a NaN from non-NaN arguments into `ValueError`, an
infinity from finite arguments into `OverflowError` (or `ValueError` where the function has
a singularity), honour `errno`, ignore `ERANGE` on results below `1.5` in magnitude (an
underflow), and otherwise return what the C library returned. Together with the
documentation's "A NaN will not be returned from any of the functions above unless one or
more of the input arguments was a NaN", for the functions built on `math_1` and `math_2`.
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64 PyLean.Binary64.F64

/-- What `is_error` does with a nonzero `errno` once `raise_edom` is decided: `ERANGE` with a
result below `1.5` in magnitude is an underflow and is ignored, larger is `OverflowError`. -/
def erangeOutcome (r : F64) : Py F64 :=
  if F64.lt (F64.abs r) c1p5 then .ok r else .error (.overflowError "math range error")

/-- `math_1(arg, func, can_overflow, err_msg)` for every C function `func`, flag and message. -/
def Math1Rules : Prop :=
  ∀ (func : CFun1) (canOverflow : Bool) (errMsg : Option String) (o : Arg),
    let call := math_1 o func canOverflow errMsg
    (∀ e, asDouble o = .error e → call = .error e) ∧
    (∀ x, asDouble o = .ok x →
      let r := (func x).1
      let errno := (func x).2
      (∀ v, call = .ok v → (v.isNaN = true → x.isNaN = true) ∧ (v.isInf = true → x.isFinite = false)) ∧
      (r.isNaN = true → x.isNaN = false → call = .error (math_1_domainErr x errMsg)) ∧
      (r.isInf = true → x.isFinite = true →
        call = .error (if canOverflow then .overflowError "math range error" else math_1_domainErr x errMsg)) ∧
      (r.isFinite = true → errno = .edom → call = .error (.valueError "math domain error")) ∧
      (r.isFinite = true → errno = .erange → call = erangeOutcome r) ∧
      (errno = .zero → (r.isNaN = true → x.isNaN = true) → (r.isInf = true → x.isFinite = false) →
        call = .ok r))

/-- `math_1a(arg, func, err_msg)` for every C function `func` that sets `errno` itself:
`errno` alone decides. -/
def Math1aRules : Prop :=
  ∀ (func : CFun1) (errMsg : Option String) (o : Arg),
    let call := math_1a o func errMsg
    (∀ e, asDouble o = .error e → call = .error e) ∧
    (∀ x, asDouble o = .ok x →
      let r := (func x).1
      let errno := (func x).2
      (errno = .zero → call = .ok r) ∧
      (errno = .edom → call = .error (math_1_domainErr x errMsg)) ∧
      (errno = .erange → call = erangeOutcome r))

/-- `math_2(args, func, name)` for every two-argument C function `func`. -/
def Math2Rules : Prop :=
  ∀ (func : CFun2) (name : String) (args : List Arg),
    let call := math_2 args func name
    (args.length ≠ 2 → call.raises "TypeError") ∧
    (∀ a b, args = [a, b] →
      (∀ e, asDouble a = .error e → call = .error e) ∧
      (∀ x e, asDouble a = .ok x → asDouble b = .error e → call = .error e) ∧
      (∀ x y, asDouble a = .ok x → asDouble b = .ok y →
        let r := (func x y).1
        let errno := (func x y).2
        (∀ v, call = .ok v → (v.isNaN = true → x.isNaN || y.isNaN) ∧
          (v.isInf = true → !(x.isFinite && y.isFinite))) ∧
        (r.isNaN = true → (x.isNaN || y.isNaN) = false → call = .error (.valueError "math domain error")) ∧
        (r.isInf = true → (x.isFinite && y.isFinite) = true →
          call = .error (.overflowError "math range error")) ∧
        (r.isNaN = true → (x.isNaN || y.isNaN) = true → call = .ok r) ∧
        (r.isInf = true → (x.isFinite && y.isFinite) = false → call = .ok r) ∧
        (r.isFinite = true → errno = .edom → call = .error (.valueError "math domain error")) ∧
        (r.isFinite = true → errno = .erange → call = erangeOutcome r) ∧
        (r.isFinite = true → errno = .zero → call = .ok r)))

theorem is_error_erange (r : F64) : (match is_error r .erange true with
    | .ok => Except.ok r | .raise e => .error e | .silent => .error (.valueError "math domain error"))
    = erangeOutcome r := by
  unfold is_error erangeOutcome
  by_cases h : (F64.abs r).lt c1p5 = true <;> simp [h]

theorem math1Rules_proven : Math1Rules := by
  intro func canOverflow errMsg o
  refine ⟨fun e he => ?_, fun x hx => ?_⟩
  · simp [math_1, he, bind, Except.bind]
  · have base : math_1 o func canOverflow errMsg =
        (if (func x).1.isNaN && !x.isNaN then .error (math_1_domainErr x errMsg)
        else if (func x).1.isInf && x.isFinite then
          (if canOverflow then .error (.overflowError "math range error")
           else .error (math_1_domainErr x errMsg))
        else if (func x).1.isFinite && (func x).2 != .zero then
          match is_error (func x).1 (func x).2 true with
          | .ok => .ok (func x).1
          | .raise e => .error e
          | .silent => .error (.valueError "math domain error")
        else .ok (func x).1) := by
      simp only [math_1, hx, bind, Except.bind]; rfl
    rw [base]
    generalize (func x).1 = r
    generalize (func x).2 = errno
    refine ⟨fun v hv => ?_, fun hn hx' => ?_, fun hi hf => ?_, fun hf he => ?_, fun hf he => ?_,
      fun he hn hi => ?_⟩
    · constructor
      · intro hvn
        cases hxn : x.isNaN
        · exfalso
          rcases classify r with h | h | h
          · rw [isNaN_false_of_finite h, isInf_false_of_finite h] at hv
            simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, h, Bool.true_and] at hv
            split at hv
            · split at hv
              · cases hv; rw [isNaN_false_of_finite h] at hvn; cases hvn
              · cases hv
              · cases hv
            · cases hv; rw [isNaN_false_of_finite h] at hvn; cases hvn
          · rw [not_nan_of_inf h] at hv
            simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, h, Bool.true_and,
              not_finite_of_inf h] at hv
            split at hv
            · split at hv <;> cases hv
            · cases hv; rw [not_nan_of_inf h] at hvn; cases hvn
          · simp [h, hxn] at hv
        · rfl
      · intro hvi
        cases hxf : x.isFinite
        · rfl
        · exfalso
          rcases classify r with h | h | h
          · simp only [isNaN_false_of_finite h, isInf_false_of_finite h, h, Bool.false_and,
              Bool.false_eq_true, ↓reduceIte, Bool.true_and] at hv
            split at hv
            · split at hv
              · cases hv; rw [isInf_false_of_finite h] at hvi; cases hvi
              · cases hv
              · cases hv
            · cases hv; rw [isInf_false_of_finite h] at hvi; cases hvi
          · simp only [not_nan_of_inf h, h, hxf, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              Bool.and_self] at hv
            split at hv <;> cases hv
          · have hxn : x.isNaN = false := isNaN_false_of_finite hxf
            simp [h, hxn] at hv
    · simp [hn, hx']
    · simp only [not_nan_of_inf hi, hi, hf, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        Bool.and_self]
      cases canOverflow <;> rfl
    · simp only [isNaN_false_of_finite hf, isInf_false_of_finite hf, hf, he, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte, Bool.true_and]
      rfl
    · simp only [isNaN_false_of_finite hf, isInf_false_of_finite hf, hf, he, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte, Bool.true_and]
      exact is_error_erange r
    · subst he
      cases hrn : r.isNaN
      · cases hri : r.isInf
        · simp
        · simp [hrn, hri, not_finite_of_inf hri, hi hri]
      · simp [hrn, hn hrn, not_inf_of_nan hrn]

theorem math1aRules_proven : Math1aRules := by
  intro func errMsg o
  refine ⟨fun e he => ?_, fun x hx => ?_⟩
  · simp [math_1a, he, bind, Except.bind]
  · have base : math_1a o func errMsg =
        (if (func x).2 != .zero then
          match is_error (func x).1 (func x).2 errMsg.isNone with
          | .ok => .ok (func x).1
          | .raise e => .error e
          | .silent =>
            match errMsg with
            | some m => .error (domainMsg m x)
            | none => .error (.valueError "math domain error")
        else .ok (func x).1) := by
      simp only [math_1a, hx, bind, Except.bind]; rfl
    rw [base]
    generalize (func x).1 = r
    refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩
    · rw [he]; rfl
    · rw [he]
      cases errMsg <;> rfl
    · rw [he]
      simp only [bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte, is_error,
        erangeOutcome]
      by_cases h : (F64.abs r).lt c1p5 = true <;> simp [h]

theorem math2Rules_proven : Math2Rules := by
  intro func name args
  refine ⟨fun hl => ?_, fun a b hab => ?_⟩
  · unfold math_2 checkPositional
    have : ¬ (2 ≤ args.length ∧ args.length ≤ 2) := by omega
    by_cases h1 : args.length < 2
    · simp [h1, bind, Except.bind, Py.raises, PyExc.className]
    · have h2 : 2 < args.length := by omega
      simp [h1, h2, bind, Except.bind, Py.raises, PyExc.className]
  · subst hab
    have hcp : checkPositional name [a, b].length 2 2 = .ok () := by
      simp [checkPositional]
    refine ⟨fun e he => ?_, fun x e hx he => ?_, fun x y hx hy => ?_⟩
    · unfold math_2; rw [hcp]; simp [bind, Except.bind, he]
    · unfold math_2; rw [hcp]; simp [bind, Except.bind, he, hx]
    · have base : math_2 [a, b] func name =
          (let r := (func x y).1
           let errno : Errno :=
             if r.isNaN then (if !x.isNaN && !y.isNaN then Errno.edom else .zero)
             else if r.isInf then (if x.isFinite && y.isFinite then .erange else .zero)
             else (func x y).2
           if errno != .zero then
             match is_error r errno true with
             | .ok => .ok r
             | .raise e => .error e
             | .silent => .error (.valueError "math domain error")
           else .ok r) := by
        have ha : asDouble ([a, b].getD 0 default) = .ok x := hx
        have hb' : asDouble ([a, b].getD 1 default) = .ok y := hy
        unfold math_2; rw [hcp]; simp only [bind, Except.bind, ha, hb']; rfl
      rw [base]
      simp only []
      generalize (func x y).1 = r
      generalize (func x y).2 = e0
      have er : ∀ s, (match is_error (F64.inf s) .erange true with
          | .ok => Except.ok (F64.inf s) | .raise e => .error e
          | .silent => .error (.valueError "math domain error"))
          = .error (.overflowError "math range error") := by
        intro s; cases s <;> decide +kernel
      refine ⟨fun v hv => ?_, fun hn hxy => ?_, fun hi hxy => ?_, fun hn hxy => ?_,
        fun hi hxy => ?_, fun hf he => ?_, fun hf he => ?_, fun hf he => ?_⟩
      · rcases classify r with h | h | h
        · simp only [isNaN_false_of_finite h, isInf_false_of_finite h, Bool.false_eq_true,
            ↓reduceIte] at hv
          split at hv
          · split at hv
            · cases hv; exact ⟨fun h' => (by rw [isNaN_false_of_finite h] at h'; cases h'),
                fun h' => (by rw [isInf_false_of_finite h] at h'; cases h')⟩
            · cases hv
            · cases hv
          · cases hv; exact ⟨fun h' => (by rw [isNaN_false_of_finite h] at h'; cases h'),
              fun h' => (by rw [isInf_false_of_finite h] at h'; cases h')⟩
        · simp only [not_nan_of_inf h, h, Bool.false_eq_true, ↓reduceIte] at hv
          cases hxy : (x.isFinite && y.isFinite)
          · simp only [hxy, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false] at hv
            cases hv
            exact ⟨fun h' => (by rw [not_nan_of_inf h] at h'; cases h'), fun _ => (by simp)⟩
          · simp only [hxy, ↓reduceIte, bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true] at hv
            rw [eq_inf_of_isInf h, er] at hv; cases hv
        · simp only [h, ↓reduceIte] at hv
          cases hxy : (!x.isNaN && !y.isNaN)
          · simp only [hxy, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false] at hv
            cases hv
            refine ⟨fun _ => ?_, fun h' => (by rw [not_inf_of_nan h] at h'; cases h')⟩
            cases hx : x.isNaN <;> cases hy : y.isNaN <;> simp_all
          · simp [hxy, is_error] at hv
      · have : (!x.isNaN && !y.isNaN) = true := by
          cases hx : x.isNaN <;> cases hy : y.isNaN <;> simp_all
        simp [hn, this, is_error]
      · simp only [not_nan_of_inf hi, hi, hxy, Bool.false_eq_true, ↓reduceIte, bne_iff_ne, ne_eq,
          reduceCtorEq, not_false_eq_true]
        rw [eq_inf_of_isInf hi, er]
      · have : (!x.isNaN && !y.isNaN) = false := by
          cases hx : x.isNaN <;> cases hy : y.isNaN <;> simp_all
        simp [hn, this]
      · simp [not_nan_of_inf hi, hi, hxy]
      · simp only [isNaN_false_of_finite hf, isInf_false_of_finite hf, he, Bool.false_eq_true,
          ↓reduceIte, bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, is_error]
      · simp only [isNaN_false_of_finite hf, isInf_false_of_finite hf, he, Bool.false_eq_true,
          ↓reduceIte, bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true]
        exact is_error_erange r
      · simp [isNaN_false_of_finite hf, isInf_false_of_finite hf, he]

end PyLean.MathInt
