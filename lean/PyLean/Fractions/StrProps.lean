import PyLean.Fractions.Format
import PyLean.Fractions.Ctor

/-!
`__str__` and `__format__` against the string constructor.
-/

namespace PyLean.Fractions

open PyLean

/-- Decimal digits of `n`, as `str(n)` spells them. -/
abbrev D (n : Nat) : List Char := Nat.toDigits 10 n

theorem mem_D {n : Nat} {c : Char} (h : c ∈ D n) : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  have := Char.isDigit_iff_toNat.mp (Nat.isDigit_of_mem_toDigits (by decide) (by decide) h)
  simpa using this

theorem ascii_digit_props {c : Char} (h : 48 ≤ c.toNat ∧ c.toNat ≤ 57) :
    isDigit c = true ∧ digitVal c = some (c.toNat - 48) ∧ isWs c = false ∧
    c ≠ '_' ∧ c ≠ '-' ∧ c ≠ '+' ∧ c ≠ '.' ∧ c ≠ '/' ∧ c ≠ 'e' ∧ c ≠ 'E' := by
  have hv : digitVal c = some (c.toNat - 48) := by
    simp only [digitVal]; rw [ite_eq_left (by omega)]
  refine ⟨by simp [isDigit, hv], hv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases hw : isWs c
    · rfl
    · exfalso
      simp [isWs] at hw
      omega
  all_goals (intro hc; subst hc; simp at h)

theorem D_ne_nil (n : Nat) : D n ≠ [] := Nat.toDigits_ne_nil

theorem foldl_digits (l : List Char) (hl : ∀ c ∈ l, 48 ≤ c.toNat ∧ c.toNat ≤ 57) (acc : Nat) :
    l.foldl digitStep acc = Nat.ofDigitChars 10 l acc := by
  induction l generalizing acc with
  | nil => simp
  | cons c cs ih =>
    have hc := hl c (by simp)
    simp only [List.foldl_cons, digitStep, (ascii_digit_props hc).2.1]
    rw [ih (fun x hx => hl x (by simp [hx])), Nat.ofDigitChars_cons]
    congr 1
    have : '0'.toNat = 48 := rfl
    rw [this]
    omega

theorem digitsValue_D (n : Nat) : digitsValue (D n) = n := by
  simp only [digitsValue]
  rw [foldl_digits _ (fun c hc => mem_D hc)]
  exact Nat.ofDigitChars_ten_toDigits

/-- `runTail` stops exactly after a run of ASCII digits followed by a
character that is neither a digit nor `_`. -/
theorem runTail_digits (ds rest : List Char) (hds : ∀ c ∈ ds, 48 ≤ c.toNat ∧ c.toNat ≤ 57)
    (hrest : ∀ c r, rest = c :: r → isDigit c = false ∧ c ≠ '_') :
    runTail (ds ++ rest) = (ds, rest) := by
  induction ds with
  | nil =>
    cases rest with
    | nil => rfl
    | cons c r =>
      obtain ⟨h1, h2⟩ := hrest c r rfl
      rw [List.nil_append, runTail.eq_def]
      simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
  | cons c cs ih =>
    have hc := ascii_digit_props (hds c (by simp))
    rw [List.cons_append, runTail.eq_def]
    simp only [hc.1, ↓reduceIte]
    rw [ih (fun x hx => hds x (by simp [hx]))]

theorem digitRun_D (n : Nat) (rest : List Char)
    (hrest : ∀ c r, rest = c :: r → isDigit c = false ∧ c ≠ '_') :
    digitRun (D n ++ rest) = (D n, rest) := by
  obtain ⟨c, cs, hcs⟩ : ∃ c cs, D n = c :: cs := by
    cases h : D n with
    | nil => exact absurd h (D_ne_nil n)
    | cons c cs => exact ⟨c, cs, rfl⟩
  have hall : ∀ x ∈ D n, 48 ≤ x.toNat ∧ x.toNat ≤ 57 := fun x hx => mem_D hx
  rw [hcs] at hall ⊢
  have hc := ascii_digit_props (hall c (by simp))
  simp only [List.cons_append, digitRun, hc.1, ↓reduceIte]
  rw [runTail_digits cs rest (fun x hx => hall x (by simp [hx])) hrest]

theorem skipWs_D (n : Nat) (rest : List Char) : skipWs (D n ++ rest) = D n ++ rest := by
  obtain ⟨c, cs, hcs⟩ : ∃ c cs, D n = c :: cs := by
    cases h : D n with
    | nil => exact absurd h (D_ne_nil n)
    | cons c cs => exact ⟨c, cs, rfl⟩
  have hc := ascii_digit_props (mem_D (show c ∈ D n by rw [hcs]; simp))
  rw [hcs]
  simp [skipWs, hc.2.2.1]

theorem D_head (n : Nat) : ∃ c cs, D n = c :: cs ∧ 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  cases h : D n with
  | nil => exact absurd h (D_ne_nil n)
  | cons c cs => exact ⟨c, cs, rfl, mem_D (show c ∈ D n by rw [h]; simp)⟩

theorem splitSign_D (n : Nat) (rest : List Char) : splitSign (D n ++ rest) = (false, D n ++ rest) := by
  obtain ⟨c, cs, hcs, hc⟩ := D_head n
  have hp := ascii_digit_props hc
  rw [hcs, List.cons_append]
  unfold splitSign
  split
  · rename_i h; simp at h; exact absurd h.1 hp.2.2.2.2.1
  · rename_i h; simp at h; exact absurd h.1 hp.2.2.2.2.2.1
  · rfl

theorem pyIntOfDigits_D (n : Nat) (h : numDigits n ≤ maxStrDigits) :
    pyIntOfDigits (D n) = .ok n := by
  have hfilter : (D n).filter isDigit = D n := by
    apply List.filter_eq_self.mpr
    intro x hx; exact (ascii_digit_props (mem_D hx)).1
  have hs := splitSign_D n []
  simp only [List.append_nil] at hs
  simp only [pyIntOfDigits, hs, hfilter]
  rw [ite_eq_right (show ¬ (D n).length > maxStrDigits by unfold numDigits at h; simp only [D]; omega), digitsValue_D]
  rfl

/-- The text after the numerator digits in `str(x)`. -/
def denSuffix : Option Nat → List Char
  | none => []
  | some k => '/' :: D k

/-- `matchRational` on `[-]digits` and `[-]digits/digits`. -/
theorem match_D (neg : Bool) (m : Nat) (den : Option Nat) :
    matchRational ((if neg then ['-'] else []) ++ D m ++ denSuffix den) =
    some ⟨neg, D m, den.map D, none, none⟩ := by
  obtain ⟨c, cs, hcs, hc⟩ := D_head m
  have hp := ascii_digit_props hc
  have hrest : ∀ x r, denSuffix den = x :: r → isDigit x = false ∧ x ≠ '_' := by
    intro x r h
    cases den with
    | none => simp [denSuffix] at h
    | some k => simp [denSuffix] at h; rw [← h.1]; decide
  have hrun := digitRun_D m _ hrest
  have hsk : skipWs (D m ++ denSuffix den) = D m ++ denSuffix den := skipWs_D m _
  have hs1 : skipWs ((if neg then ['-'] else []) ++ D m ++ denSuffix den) =
      (if neg then ['-'] else []) ++ D m ++ denSuffix den := by
    cases neg
    · simpa using hsk
    · simp [skipWs, isWs]
  have hsign : splitSign ((if neg then ['-'] else []) ++ D m ++ denSuffix den) =
      (neg, D m ++ denSuffix den) := by
    cases neg
    · simpa using splitSign_D m (denSuffix den)
    · simp [splitSign]
  have hlook : lookahead (D m ++ denSuffix den) = true := by
    rw [hcs]; simp [lookahead, hp.1]
  simp only [matchRational, hs1, hsign, hlook, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hrun]
  cases den with
  | none => simp [skipWs, denSuffix]
  | some k =>
    have hrun' : digitRun (D k) = (D k, []) := by
      have := digitRun_D k [] (by intro x r h; simp at h)
      simpa using this
    have hsk' : skipWs (D k) = D k := by simpa using skipWs_D k []
    simp [denSuffix, skipWs, isWs, hsk', hrun', D_ne_nil]

theorem parse_of_match (s : List Char) (neg : Bool) (m : Nat) (den : Option Nat)
    (hm : matchRational s = some ⟨neg, D m, den.map D, none, none⟩)
    (hlim : numDigits m ≤ maxStrDigits) (hlimd : ∀ k, den = some k → numDigits k ≤ maxStrDigits) :
    parse s = normalize (if neg then -(m : Int) else m) (den.elim 1 (fun k => (k : Int))) := by
  cases den with
  | none =>
    cases neg <;>
      simp [parse, hm, D_ne_nil, pyIntOfDigits_D _ hlim, bind, Except.bind, pure, Except.pure]
  | some k =>
    have hk := hlimd k rfl
    cases neg <;>
      simp [parse, hm, D_ne_nil, pyIntOfDigits_D _ hlim, pyIntOfDigits_D _ hk, bind, Except.bind,
        pure, Except.pure]

theorem normalize_of_normal (x : Frac) (hx : x.Normal) : normalize x.num x.den = .ok x := by
  simp only [normalize, show x.den ≠ 0 by have := hx.1; omega, ↓reduceIte, hx.2, Int.natCast_one,
    show ¬ x.den < 0 by have := hx.1; omega]
  simp only [pyDiv, Int.fdiv_one]
  rfl

/-- Round trip: `Fraction(str(x)) == x` for every Fraction `x` whose `str`
succeeds (an invariant of `__str__`/`__new__`; both sides go through the int
string conversion, so a value too large for `str` is outside the claim). -/
def StrRoundTrip : Prop :=
  ∀ x : Frac, x.Normal → ∀ s, str x = .ok s → parse s = .ok x

theorem strRoundTrip_proven : StrRoundTrip := by
  intro x ⟨hd, hg⟩ s hs
  -- the pieces of `str x`
  have hnum : ∀ t, strInt x.num = .ok t →
      t = (if x.num < 0 then ['-'] else []) ++ D x.num.natAbs ∧ numDigits x.num.natAbs ≤ maxStrDigits := by
    intro t ht
    simp only [strInt] at ht
    split at ht
    · cases ht
    · cases ht; exact ⟨rfl, by omega⟩
  have hden : ∀ t, strInt x.den = .ok t → t = D x.den.natAbs ∧ numDigits x.den.natAbs ≤ maxStrDigits := by
    intro t ht
    simp only [strInt] at ht
    split at ht
    · cases ht
    · cases ht; exact ⟨by simp [show ¬ x.den < 0 by omega], by omega⟩
  have hsign : ((if x.num < 0 then -((x.num.natAbs : Nat) : Int) else (x.num.natAbs : Int))) = x.num := by
    split <;> omega
  have hnorm := normalize_of_normal x ⟨hd, hg⟩
  have hsgn : (if decide (x.num < 0) = true then -((x.num.natAbs : Nat) : Int) else
      ((x.num.natAbs : Nat) : Int)) = x.num := by
    by_cases h : x.num < 0 <;> simp [h] <;> omega
  by_cases h1 : x.den = 1
  · simp only [str, h1, ↓reduceIte] at hs
    obtain ⟨hst, hlim⟩ := hnum s hs
    have hm := match_D (decide (x.num < 0)) x.num.natAbs none
    simp only [decide_eq_true_eq, denSuffix, List.append_nil] at hm
    subst hst
    rw [parse_of_match _ (decide (x.num < 0)) x.num.natAbs none (by simpa using hm) hlim
      (by intro k hk; cases hk)]
    simp only [Option.elim]
    rw [hsgn, ← h1]
    exact hnorm
  · simp only [str, h1, ↓reduceIte] at hs
    cases hn : strInt x.num with
    | error e => simp [hn, bind, Except.bind] at hs
    | ok tn =>
      cases hdn : strInt x.den with
      | error e => simp [hn, hdn, bind, Except.bind] at hs
      | ok td =>
        simp only [hn, hdn, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hs
        obtain ⟨htn, hlim⟩ := hnum tn hn
        obtain ⟨htd, hlimd⟩ := hden td hdn
        subst htn htd hs
        have hm := match_D (decide (x.num < 0)) x.num.natAbs (some x.den.natAbs)
        simp only [decide_eq_true_eq, Option.map_some, denSuffix] at hm
        rw [show (if x.num < 0 then ['-'] else []) ++ D x.num.natAbs ++ ['/'] ++ D x.den.natAbs =
          (if x.num < 0 then ['-'] else []) ++ D x.num.natAbs ++ ('/' :: D x.den.natAbs) by simp]
        rw [parse_of_match _ (decide (x.num < 0)) x.num.natAbs (some x.den.natAbs)
          (by simpa using hm) hlim (by intro k hk; cases hk; exact hlimd)]
        simp only [Option.elim]
        rw [hsgn, show ((x.den.natAbs : Nat) : Int) = x.den by omega]
        exact hnorm

end PyLean.Fractions
