import PyLean.Decimal.Parse
import PyLean.Decimal.Digits
import PyLean.Decimal.Lemmas

/-!
`mpd_qset_string` on numeric strings: `scan_dpoint_exp` and the coefficient
extraction, for strings of the shape `digits [. digits] [e [sign] digits]`.
-/

namespace PyLean.Decimal

open PyLean

/-- All characters are ASCII digits. -/
abbrev AD (D : List Char) : Prop := ∀ c ∈ D, c.isDigit = true

theorem isAsciiDigit_iff {c : Char} : isAsciiDigit c = true ↔ c.isDigit = true := by
  rw [isDigit_iff']
  simp only [isAsciiDigit, Bool.and_eq_true, decide_eq_true_eq, Char.le_def]
  rfl

theorem not_digit_of_toNat {c : Char} (h : c.toNat < 48 ∨ 57 < c.toNat) : isAsciiDigit c = false := by
  cases hd : isAsciiDigit c with
  | false => rfl
  | true =>
    have := isDigit_iff'.mp (isAsciiDigit_iff.mp hd)
    omega

theorem ne_of_digit {c d : Char} (hc : c.isDigit = true) (hd : d.toNat < 48 ∨ 57 < d.toNat) : c ≠ d := by
  intro h; subst h
  have := isDigit_iff'.mp hc
  omega

/-- The non-digit characters of the grammar. -/
theorem digit_facts {c : Char} (hc : c.isDigit = true) :
    isAsciiDigit c = true ∧ (c == '.') = false ∧ (c == 'E') = false ∧ (c == 'e') = false ∧
    (c == '+') = false ∧ (c == '-') = false := by
  refine ⟨isAsciiDigit_iff.mpr hc, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact beq_false_of_ne (ne_of_digit hc (by decide))

theorem zero_isDigit : ('0' : Char).isDigit = true := by decide

/-- `scan_dpoint_exp` while the first relevant digit has not been seen: a
leading zero followed by a digit, or by `.` and a digit, is skipped. -/
def Skips (T : List Char) : Prop :=
  (∃ d r, T = d :: r ∧ d.isDigit = true) ∨ (∃ d r, T = '.' :: d :: r ∧ d.isDigit = true)

abbrev Fresh (st : ScanState) : Prop :=
  st.coeff = none ∧ st.exp = none ∧ st.afterE = false

theorem look_skips {T : List Char} (h : Skips T) : lookNone T = false := by
  rcases h with ⟨d, r, rfl, hd⟩ | ⟨d, r, rfl, hd⟩
  · simp [lookNone, isAsciiDigit_iff.mpr hd]
  · have h1 : isAsciiDigit '.' = false := by decide
    simp [lookNone, isAsciiDigit_iff.mpr hd, h1]

theorem look_noskip {T : List Char} (h : ¬ Skips T) : lookNone T = true := by
  have h1 : ¬ (∃ d r, T = d :: r ∧ d.isDigit = true) := fun x => h (Or.inl x)
  have h2 : ¬ (∃ d r, T = '.' :: d :: r ∧ d.isDigit = true) := fun x => h (Or.inr x)
  cases T with
  | nil => rfl
  | cons x xs =>
    cases hx : isAsciiDigit x with
    | true => exact absurd ⟨x, xs, rfl, isAsciiDigit_iff.mp hx⟩ h1
    | false =>
      cases xs with
      | nil => simp [lookNone, hx]
      | cons y ys =>
        by_cases hd : x = '.'
        · subst hd
          cases hy : isAsciiDigit y with
          | true => exact absurd ⟨y, ys, rfl, isAsciiDigit_iff.mp hy⟩ h2
          | false => simp [lookNone, hx, hy]
        · simp [lookNone, hx, hd]

/-- One step of the scan on a digit. -/
theorem scan_digit (i : Nat) (x : Char) (cs : List Char) (st : ScanState) (hx : x.isDigit = true) :
    scanLoop i (x :: cs) st =
      if (st.coeff.isNone && st.exp.isNone) = true then
        if x = '0' ∧ lookNone cs = false then scanLoop (i + 1) cs { st with afterE := false }
        else scanLoop (i + 1) cs { st with afterE := false, coeff := some i }
      else scanLoop (i + 1) cs { st with afterE := false } := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := digit_facts hx
  rw [scanLoop]
  simp only [f2, f3, f4, f5, f6, Bool.or_self, Bool.and_false, Bool.false_eq_true, ↓reduceIte, f1,
    Bool.not_true]
  by_cases hb : (st.coeff.isNone && st.exp.isNone) = true
  · simp only [hb, ↓reduceIte]
    by_cases h0 : x = '0'
    · have h0' : (x == '0') = true := by simp [h0]
      cases hl : lookNone cs
      · simp [h0', h0]
      · simp [h0']
    · have h0' : (x == '0') = false := beq_false_of_ne h0
      simp only [h0', Bool.false_eq_true, ↓reduceIte, h0, false_and]
  · simp only [hb, Bool.false_eq_true, ↓reduceIte]

theorem scan_zero_skip (i : Nat) (T : List Char) (st : ScanState) (hst : Fresh st) (hT : Skips T) :
    scanLoop i ('0' :: T) st = scanLoop (i + 1) T st := by
  rw [scan_digit _ _ _ _ zero_isDigit]
  obtain ⟨h1, h2, h3⟩ := hst
  obtain ⟨d0, e0, c0, a0⟩ := st
  simp only at h1 h2 h3
  subst h1 h2 h3
  simp [look_skips hT]

theorem scan_zeros (Z T : List Char) (i : Nat) (st : ScanState) (hst : Fresh st)
    (hZ : ∀ c ∈ Z, c = '0') (hT : Skips T) :
    scanLoop i (Z ++ T) st = scanLoop (i + Z.length) T st := by
  induction Z generalizing i with
  | nil => rfl
  | cons z rest ih =>
    obtain rfl : z = '0' := hZ z (by simp)
    have hrest : ∀ c ∈ rest, c = '0' := fun c hc => hZ c (by simp [hc])
    have hsk : Skips (rest ++ T) := by
      cases rest with
      | nil => exact hT
      | cons y ys =>
        obtain rfl : y = '0' := hrest y (by simp)
        exact Or.inl ⟨'0', ys ++ T, rfl, zero_isDigit⟩
    simp only [List.cons_append]
    rw [scan_zero_skip _ _ _ hst hsk, ih _ hrest, List.length_cons]
    congr 1
    omega

/-- Digits after the first relevant one change nothing. -/
theorem scan_settled (X T : List Char) (i : Nat) (st : ScanState) (hX : AD X)
    (hs : st.coeff.isSome = true ∨ st.exp.isSome = true) (ha : st.afterE = false) :
    scanLoop i (X ++ T) st = scanLoop (i + X.length) T st := by
  induction X generalizing i with
  | nil => rfl
  | cons x rest ih =>
    obtain ⟨d0, e0, c0, a0⟩ := st
    simp only at ha hs
    subst ha
    have hb : (c0.isNone && e0.isNone) = false := by
      cases c0 <;> cases e0 <;> simp_all
    simp only [List.cons_append]
    rw [scan_digit _ _ _ _ (hX x (by simp))]
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    rw [ih _ (fun c hc => hX c (by simp [hc])), List.length_cons]
    congr 1
    omega

/-- The significant digits start here: their first character sets `coeff`. -/
theorem scan_first (c : Char) (R T : List Char) (i : Nat) (st : ScanState) (hst : Fresh st)
    (hc : c.isDigit = true) (hc0 : c ≠ '0' ∨ (R = [] ∧ ¬ Skips T)) (hR : AD R) :
    scanLoop i (c :: R ++ T) st = scanLoop (i + 1 + R.length) T { st with coeff := some i } := by
  obtain ⟨h1, h2, h3⟩ := hst
  obtain ⟨d0, e0, c0, a0⟩ := st
  simp only at h1 h2 h3
  subst h1 h2 h3
  have hstep : scanLoop i (c :: R ++ T) ⟨d0, none, none, false⟩ =
      scanLoop (i + 1) (R ++ T) ⟨d0, none, some i, false⟩ := by
    simp only [List.cons_append]
    rw [scan_digit _ _ _ _ hc]
    simp only [Option.isNone_none, Bool.and_self, ↓reduceIte]
    have hnot : ¬ (c = '0' ∧ lookNone (R ++ T) = false) := by
      rintro ⟨h0, hl⟩
      rcases hc0 with h | ⟨rfl, hT⟩
      · exact h h0
      · have := look_noskip hT
        simp only [List.nil_append] at hl
        rw [this] at hl
        cases hl
    rw [if_neg hnot]
  rw [hstep, scan_settled R T _ _ hR (Or.inl rfl) rfl]

/-! ## Shapes of numeric strings -/

/-- The exponent part: indicator, optional sign, digits. -/
abbrev ExPart := Option (Char × List Char × List Char)

def expPart : ExPart → List Char
  | none => []
  | some (ind, sg, D) => ind :: (sg ++ D)

/-- A well-formed exponent part. -/
def ExOk : ExPart → Prop
  | none => True
  | some (ind, sg, D) => (ind = 'e' ∨ ind = 'E') ∧ (sg = [] ∨ sg = ['+'] ∨ sg = ['-']) ∧ D ≠ [] ∧ AD D

/-- Value of the exponent part, as `strtoll` reads it before saturating. -/
def exVal : ExPart → Int
  | none => 0
  | some (_, sg, D) => if sg = ['-'] then -(digitsValue D : Int) else digitsValue D

theorem not_skips_exp (ex : ExPart) (h : ExOk ex) : ¬ Skips (expPart ex) := by
  cases ex with
  | none => rintro (⟨_, _, h1, _⟩ | ⟨_, _, h1, _⟩) <;> cases h1
  | some t =>
    obtain ⟨ind, sg, D⟩ := t
    have hi : ind = 'e' ∨ ind = 'E' := h.1
    rintro (⟨d, r, h1, h2⟩ | ⟨d, r, h1, _⟩)
    · simp only [expPart, List.cons.injEq] at h1
      rw [← h1.1] at h2
      rcases hi with rfl | rfl <;> revert h2 <;> decide
    · simp only [expPart, List.cons.injEq] at h1
      rcases hi with rfl | rfl <;> exact absurd h1.1 (by decide)

theorem scan_exp (ex : ExPart) (h : ExOk ex) (i : Nat) (st : ScanState) (hc : st.coeff.isSome = true)
    (he : st.exp = none) (ha : st.afterE = false) :
    scanLoop i (expPart ex) st = some { st with exp := ex.map (fun _ => i) } := by
  cases ex with
  | none =>
    obtain ⟨d0, e0, c0, a0⟩ := st
    simp only at he ha
    subst he ha
    simp [expPart, scanLoop]
  | some t =>
    obtain ⟨ind, sg, D⟩ := t
    obtain ⟨hi, hs, hD, hA⟩ := h
    obtain ⟨d0, e0, c0, a0⟩ := st
    simp only at hc he ha
    subst he ha
    have hind : (ind == '.') = false ∧ (ind == 'E' || ind == 'e') = true := by
      rcases hi with rfl | rfl <;> decide
    have h1 : scanLoop i (ind :: (sg ++ D)) ⟨d0, none, c0, false⟩ =
        scanLoop (i + 1) (sg ++ D) ⟨d0, some i, c0, true⟩ := by
      rw [scanLoop]
      simp [hind.1, hind.2]
    obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hD
    have hdig := hA d (by simp)
    have hrest : AD ds := fun c hc => hA c (by simp [hc])
    have h2 : ∃ j, scanLoop (i + 1) (sg ++ d :: ds) ⟨d0, some i, c0, true⟩ =
        scanLoop j (d :: ds) ⟨d0, some i, c0, false⟩ ∨
        scanLoop (i + 1) (sg ++ d :: ds) ⟨d0, some i, c0, true⟩ = scanLoop j ds ⟨d0, some i, c0, false⟩ := by
      rcases hs with rfl | rfl | rfl
      · refine ⟨i + 2, Or.inr ?_⟩
        simp only [List.nil_append]
        rw [scan_digit _ _ _ _ hdig]
        simp
      · exact ⟨i + 2, Or.inl (by rw [List.singleton_append, scanLoop]; simp)⟩
      · exact ⟨i + 2, Or.inl (by rw [List.singleton_append, scanLoop]; simp)⟩
    have hfin : ∀ j, scanLoop j (d :: ds) ⟨d0, some i, c0, false⟩ = some ⟨d0, some i, c0, false⟩ := by
      intro j
      have := scan_settled (d :: ds) [] j ⟨d0, some i, c0, false⟩ hA (Or.inr rfl) rfl
      simpa [scanLoop] using this
    have hfin2 : ∀ j, scanLoop j ds ⟨d0, some i, c0, false⟩ = some ⟨d0, some i, c0, false⟩ := by
      intro j
      have := scan_settled ds [] j ⟨d0, some i, c0, false⟩ hrest (Or.inr rfl) rfl
      simpa [scanLoop] using this
    simp only [expPart, Option.map_some]
    rw [h1]
    obtain ⟨j, h3 | h3⟩ := h2
    · rw [h3, hfin]
    · rw [h3, hfin2]

theorem strtoexp_ok (sg D : List Char) (hs : sg = [] ∨ sg = ['+'] ∨ sg = ['-']) (hD : D ≠ []) (hA : AD D)
    (hlo : mpdSsizeMin ≤ (if sg = ['-'] then -(digitsValue D : Int) else digitsValue D))
    (hhi : (if sg = ['-'] then -(digitsValue D : Int) else digitsValue D) ≤ mpdSsizeMax) :
    strtoexp (sg ++ D) = some (if sg = ['-'] then -(digitsValue D : Int) else digitsValue D) := by
  obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hD
  obtain ⟨_, _, _, _, f5, f6⟩ := digit_facts (hA d (by simp))
  have hp : d ≠ '+' := by simpa using f5
  have hm : d ≠ '-' := by simpa using f6
  have hsp : expSign (d :: ds) = (false, d :: ds) := by
    unfold expSign
    split <;> simp_all
  rcases hs with rfl | rfl | rfl
  · simp only [show ¬ ([] : List Char) = ['-'] by simp, ↓reduceIte] at hlo hhi ⊢
    simp only [List.nil_append, strtoexp, hsp, Bool.false_eq_true, ↓reduceIte, reduceCtorEq]
    congr 1
    omega
  · simp only [show ¬ (['+'] : List Char) = ['-'] by decide, ↓reduceIte] at hlo hhi ⊢
    have : expSign (['+'] ++ d :: ds) = (false, d :: ds) := rfl
    simp only [strtoexp, this, Bool.false_eq_true, ↓reduceIte, reduceCtorEq]
    congr 1
    omega
  · simp only [↓reduceIte] at hlo hhi ⊢
    have : expSign (['-'] ++ d :: ds) = (true, d :: ds) := rfl
    simp only [strtoexp, this, ↓reduceIte, reduceCtorEq]
    congr 1
    omega

/-- Evaluation of `mpdNumeric` from the facts about the scan. -/
theorem mpdNumeric_eval (neg : Bool) (P : List Char) (ex : ExPart) (hx : ExOk ex) (st : ScanState)
    (p f D : Nat) (C : List Char)
    (hscan : scanLoop 0 (P ++ expPart ex) {} = some st)
    (hexp : st.exp = ex.map (fun _ => P.length))
    (hc : st.coeff = some p) (hpL : p ≤ P.length)
    (hdp : (st.dpoint = none ∧ f = 0 ∧ D = P.length - p) ∨
      ∃ d, st.dpoint = some d ∧ f = P.length - d - 1 ∧
        D = (if d > p then P.length - p - 1 else P.length - p))
    (hC : ((P.drop p).take (P.length - p)).filter (· != '.') = C)
    (hf : (f : Int) ≤ mpdMaxPrec) (hD : (D : Int) ≤ mpdMaxPrec)
    (he1 : mpdMinEtiny ≤ exVal ex - f) (he2 : exVal ex - f ≤ mpdMaxEmax) :
    mpdNumeric neg (P ++ expPart ex) = .fin neg (digitsValue C) D (exVal ex - f) := by
  have hC' : (((P ++ expPart ex).drop p).take (P.length - p)).filter (· != '.') = C := by
    rw [List.drop_append_of_le_length hpL, List.take_append_of_le_length (by simp)]
    exact hC
  have hrng : mpdSsizeMin ≤ exVal ex ∧ exVal ex ≤ mpdSsizeMax := by
    simp only [mpdMinEtiny, mpdMinEmin, mpdMaxPrec, mpdMaxEmax, mpdSsizeMin, mpdSsizeMax] at *
    omega
  have hend : st.exp.getD (P ++ expPart ex).length = P.length := by
    cases ex with
    | none => simp [hexp, expPart]
    | some t => simp [hexp]
  have hex : (scanExponent st (P ++ expPart ex)).map (fun o => o.getD 0) = some (exVal ex) ∧
      (scanExponent st (P ++ expPart ex)).isSome = true := by
    cases ex with
    | none => simp [scanExponent, hexp, exVal]
    | some t =>
      obtain ⟨ind, sg, E⟩ := t
      obtain ⟨_, hs, hE, hA⟩ := hx
      have hdrop : (P ++ expPart (some (ind, sg, E))).drop (P.length + 1) = sg ++ E := by
        simp [expPart, List.drop_append]
      simp only [exVal] at hrng ⊢
      simp only [scanExponent, hexp, Option.map_some, hdrop]
      rw [strtoexp_ok sg E hs hE hA hrng.1 hrng.2]
      simp
  obtain ⟨o, ho, hoi⟩ : ∃ o, scanExponent st (P ++ expPart ex) = some o ∧ o.getD 0 = exVal ex := by
    cases hs : scanExponent st (P ++ expPart ex) with
    | none => rw [hs] at hex; simp at hex
    | some o =>
      refine ⟨o, rfl, ?_⟩
      rw [hs] at hex
      simpa using hex.1
  have hfin : ∀ fr : Option Nat, (fr = none ∧ f = 0) ∨ fr = some f →
      finalExp (exVal ex) fr = exVal ex - f := by
    simp only [mpdSsizeMin, mpdMinEtiny, mpdMinEmin, mpdMaxPrec, mpdMaxEmax] at he1 he2 hf
    rintro fr (⟨rfl, rfl⟩ | rfl)
    · simp only [finalExp, mpdExpInf, mpdSsizeMin]
      repeat' split
      all_goals omega
    · simp only [finalExp, mpdExpInf, mpdSsizeMin]
      repeat' split
      all_goals omega
  unfold mpdNumeric
  rw [hscan]
  simp only [hc, ho, hend, hC', hoi]
  rcases hdp with ⟨h3, rfl, rfl⟩ | ⟨d, h3, rfl, rfl⟩
  · have h4 : digitsFrac st.dpoint p P.length = (P.length - p, none) := by simp [digitsFrac, h3]
    simp only [h4, fracOk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [if_neg (Int.not_lt.mpr hD), hfin none (Or.inl ⟨rfl, rfl⟩)]
  · have h4 : digitsFrac st.dpoint p P.length =
        (if d > p then P.length - p - 1 else P.length - p, some (P.length - d - 1)) := by
      simp [digitsFrac, h3]
    simp only [h4, fracOk, hf, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [if_neg (Int.not_lt.mpr hD), hfin _ (Or.inr rfl)]

/-! ## The shape theorem -/

/-- `digits`, or `digits . digits`. -/
def numBody (I : List Char) (fr : Option (List Char)) : List Char :=
  I ++ (match fr with | none => [] | some F => '.' :: F)

theorem scan_dot (i : Nat) (T : List Char) (st : ScanState) (hd : st.dpoint = none) (he : st.exp = none)
    (ha : st.afterE = false) :
    scanLoop i ('.' :: T) st = scanLoop (i + 1) T { st with dpoint := some i } := by
  obtain ⟨d0, e0, c0, a0⟩ := st
  simp only at hd he ha
  subst hd he ha
  rw [scanLoop]
  simp

theorem filter_AD {X : List Char} (hX : AD X) : X.filter (· != '.') = X := by
  apply List.filter_eq_self.mpr
  intro c hc
  have := (digit_facts (hX c hc)).2.1
  simpa using this

theorem digitVal_zero : digitVal '0' = some 0 := by decide

theorem foldl_zeros (Z : List Char) (hZ : ∀ c ∈ Z, c = '0') :
    Z.foldl (fun acc c => acc * 10 + (digitVal c).getD 0) 0 = 0 := by
  induction Z with
  | nil => rfl
  | cons z rest ih =>
    obtain rfl : z = '0' := hZ z (by simp)
    simp only [List.foldl_cons, digitVal_zero, Option.getD_some, Nat.zero_mul, Nat.zero_add]
    exact ih (fun c hc => hZ c (by simp [hc]))

theorem digitsValue_zeros (Z X : List Char) (hZ : ∀ c ∈ Z, c = '0') :
    digitsValue (Z ++ X) = digitsValue X := by
  simp only [digitsValue, List.foldl_append, foldl_zeros Z hZ]

/-- A digit string of length `n` reads as less than `10^n`. -/
theorem digits_lt (X : List Char) (hX : AD X) : Nat.ofDigitChars 10 X 0 < 10 ^ X.length := by
  induction X with
  | nil => simp [Nat.ofDigitChars]
  | cons x xs ih =>
    have hd := isDigit_iff'.mp (hX x (by simp))
    have hi := ih (fun c hc => hX c (by simp [hc]))
    rw [Nat.ofDigitChars_cons, Nat.ofDigitChars_eq_ofDigitChars_zero]
    simp only [List.length_cons, Nat.mul_zero, Nat.zero_add, show '0'.toNat = 48 from rfl]
    have hk : x.toNat - 48 ≤ 9 := by omega
    have hp : 10 ^ xs.length * (x.toNat - 48) ≤ 10 ^ xs.length * 9 := Nat.mul_le_mul_left _ hk
    rw [Nat.pow_succ]
    omega

theorem digit_split (X : List Char) (hX : AD X) (hne : X ≠ []) :
    ∃ Z c R, X = Z ++ c :: R ∧ (∀ z ∈ Z, z = '0') ∧ (c ≠ '0' ∨ R = []) := by
  induction X with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    by_cases hx : x = '0'
    · cases xs with
      | nil => exact ⟨[], x, [], rfl, by simp, Or.inr rfl⟩
      | cons y ys =>
        obtain ⟨Z, c, R, h1, h2, h3⟩ := ih (fun a ha => hX a (by simp [ha])) (by simp)
        refine ⟨'0' :: Z, c, R, by rw [h1, hx]; rfl, ?_, h3⟩
        intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with rfl | hz
        · rfl
        · exact h2 z hz
    · exact ⟨[], x, xs, rfl, by simp, Or.inl hx⟩

/-- The value of significant digits and their count. -/
theorem numDigits_sig (c : Char) (R : List Char) (hc : c.isDigit = true) (hR : AD R)
    (h0 : c ≠ '0' ∨ R = []) : numDigits (digitsValue (c :: R)) = (c :: R).length := by
  have hA : AD (c :: R) := by
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hc
    · exact hR x hx
  by_cases hz : c = '0'
  · subst hz
    have : R = [] := h0.resolve_left (fun h => h rfl)
    subst this
    decide
  · have := toDigits_ofDigitChars _ (c :: R) rfl hA (by simp) (by simpa using hz)
    rw [digitsValue_eq _ hA]
    simp only [numDigits, this]

theorem mpd_caseA (neg : Bool) (Z : List Char) (c : Char) (R : List Char) (fr : Option (List Char))
    (ex : ExPart) (hZ : ∀ z ∈ Z, z = '0') (hc : c.isDigit = true) (hR : AD R)
    (hF : AD (fr.getD [])) (hx : ExOk ex)
    (h0 : c ≠ '0' ∨ (R = [] ∧ fr.getD [] = []))
    (hf : ((fr.getD []).length : Int) ≤ mpdMaxPrec)
    (hD : (((c :: R) ++ fr.getD []).length : Int) ≤ mpdMaxPrec)
    (he1 : mpdMinEtiny ≤ exVal ex - (fr.getD []).length)
    (he2 : exVal ex - ((fr.getD []).length : Int) ≤ mpdMaxEmax) :
    mpdNumeric neg (numBody (Z ++ c :: R) fr ++ expPart ex) =
      .fin neg (digitsValue ((Z ++ c :: R) ++ fr.getD [])) ((c :: R) ++ fr.getD []).length
        (exVal ex - (fr.getD []).length) := by
  have hcd : Skips (c :: (R ++ (match fr with | none => [] | some F => '.' :: F) ++ expPart ex)) :=
    Or.inl ⟨c, _, rfl, hc⟩
  have hval : digitsValue ((Z ++ c :: R) ++ fr.getD []) = digitsValue ((c :: R) ++ fr.getD []) := by
    rw [List.append_assoc, digitsValue_zeros Z _ hZ]
  have hAll : AD (c :: R ++ fr.getD []) := by
    intro x hx'
    simp only [List.cons_append, List.mem_cons, List.mem_append] at hx'
    rcases hx' with rfl | h | h
    · exact hc
    · exact hR x h
    · exact hF x h
  cases fr with
  | none =>
    simp only [Option.getD_none] at *
    have hT : c ≠ '0' ∨ (R = [] ∧ ¬ Skips (expPart ex)) :=
      h0.imp id (fun h => ⟨h.1, not_skips_exp ex hx⟩)
    have hsc : scanLoop 0 (numBody (Z ++ c :: R) none ++ expPart ex) {} =
        some { coeff := some Z.length, exp := ex.map (fun _ => Z.length + 1 + R.length) } := by
      simp only [numBody, List.append_nil, List.append_assoc, List.cons_append]
      rw [scan_zeros Z _ 0 ({} : ScanState) ⟨rfl, rfl, rfl⟩ hZ (Or.inl ⟨c, _, rfl, hc⟩), Nat.zero_add]
      have hfirst := scan_first c R (expPart ex) Z.length {} ⟨rfl, rfl, rfl⟩ hc hT hR
      simp only [List.cons_append] at hfirst
      rw [hfirst, scan_exp ex hx _ _ rfl rfl rfl]
    have hP : (numBody (Z ++ c :: R) none).length = Z.length + 1 + R.length := by
      simp [numBody]; omega
    simp only [List.append_nil] at hval ⊢
    rw [hval]
    refine mpdNumeric_eval neg _ ex hx _ Z.length 0 _ (c :: R) hsc ?_ rfl (by rw [hP]; omega)
      (Or.inl ⟨rfl, rfl, ?_⟩) ?_ (by simp [mpdMaxPrec]) ?_ (by simpa using he1) (by simpa using he2)
    · simp [hP]
    · rw [hP]; simp; omega
    · have h1 : numBody (Z ++ c :: R) none = Z ++ c :: R := by simp [numBody]
      have h2 : (Z ++ c :: R).drop Z.length = c :: R := by simp
      rw [hP, h1, h2]
      have : Z.length + 1 + R.length - Z.length = (c :: R).length := by simp; omega
      rw [this, List.take_length]
      apply filter_AD
      simpa using hAll
    · simpa using hD
  | some F =>
    simp only [Option.getD_some] at *
    have hnotsk : c ≠ '0' ∨ (R = [] ∧ ¬ Skips ('.' :: (F ++ expPart ex))) := by
      refine h0.imp id (fun h => ⟨h.1, ?_⟩)
      have hF0 : F = [] := by simpa using h.2
      rw [hF0]
      rintro (⟨d, r, h1, h2⟩ | ⟨d, r, h1, h2⟩)
      · simp only [List.nil_append, List.cons.injEq] at h1
        rw [← h1.1] at h2
        revert h2; decide
      · simp only [List.nil_append, List.cons.injEq, true_and] at h1
        exact not_skips_exp ex hx (Or.inl ⟨d, r, h1, h2⟩)
    have hsc : scanLoop 0 (numBody (Z ++ c :: R) (some F) ++ expPart ex) {} =
        some { dpoint := some (Z.length + 1 + R.length), coeff := some Z.length,
               exp := ex.map (fun _ => Z.length + 1 + R.length + 1 + F.length) } := by
      simp only [numBody, List.append_assoc, List.cons_append]
      rw [scan_zeros Z _ 0 ({} : ScanState) ⟨rfl, rfl, rfl⟩ hZ (Or.inl ⟨c, _, rfl, hc⟩), Nat.zero_add]
      have hfirst := scan_first c R ('.' :: (F ++ expPart ex)) Z.length {} ⟨rfl, rfl, rfl⟩ hc hnotsk hR
      simp only [List.cons_append] at hfirst
      rw [hfirst, scan_dot _ _ _ rfl rfl rfl,
        scan_settled F _ _ _ hF (Or.inl rfl) rfl, scan_exp ex hx _ _ rfl rfl rfl]
    have hP : (numBody (Z ++ c :: R) (some F)).length = Z.length + 1 + R.length + 1 + F.length := by
      simp [numBody]; omega
    rw [hval]
    refine mpdNumeric_eval neg _ ex hx _ Z.length F.length _ (c :: R ++ F) hsc ?_ rfl (by rw [hP]; omega)
      (Or.inr ⟨Z.length + 1 + R.length, rfl, ?_, ?_⟩) ?_ hf ?_ he1 he2
    · simp [hP]
    · rw [hP]; omega
    · rw [hP, if_pos (by omega)]; simp; omega
    · have h1 : numBody (Z ++ c :: R) (some F) = Z ++ c :: (R ++ '.' :: F) := by simp [numBody]
      have h2 : (Z ++ c :: (R ++ '.' :: F)).drop Z.length = c :: (R ++ '.' :: F) := by simp
      rw [hP, h1, h2]
      have : Z.length + 1 + R.length + 1 + F.length - Z.length = (c :: (R ++ '.' :: F)).length := by
        simp; omega
      rw [this, List.take_length]
      have hdot : (c :: (R ++ '.' :: F)).filter (· != '.') = c :: R ++ F := by
        have hk : c :: (R ++ '.' :: F) = (c :: R) ++ '.' :: F := rfl
        have h3 : ('.' :: F).filter (· != '.') = F.filter (· != '.') := by simp
        rw [hk, List.filter_append, h3]
        rw [filter_AD (fun x hx' => hAll x (by
          simp only [List.cons_append, List.mem_cons, List.mem_append] at hx' ⊢
          rcases hx' with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h))), filter_AD (X := F) hF]
      exact hdot
    · exact hD

theorem mpd_caseB (neg : Bool) (I Z : List Char) (c : Char) (R : List Char) (ex : ExPart)
    (hI : ∀ z ∈ I, z = '0') (hZ : ∀ z ∈ Z, z = '0') (hc : c.isDigit = true) (hR : AD R)
    (hx : ExOk ex) (h0 : c ≠ '0' ∨ R = [])
    (hf : (((Z ++ c :: R)).length : Int) ≤ mpdMaxPrec)
    (he1 : mpdMinEtiny ≤ exVal ex - (Z ++ c :: R).length)
    (he2 : exVal ex - ((Z ++ c :: R).length : Int) ≤ mpdMaxEmax) :
    mpdNumeric neg (numBody I (some (Z ++ c :: R)) ++ expPart ex) =
      .fin neg (digitsValue (I ++ (Z ++ c :: R))) (c :: R).length (exVal ex - (Z ++ c :: R).length) := by
  have hcd : Skips (c :: (R ++ expPart ex)) := Or.inl ⟨c, _, rfl, hc⟩
  have hzd : AD Z := fun z hz => by rw [hZ z hz]; exact zero_isDigit
  have hAD : AD (Z ++ c :: R) := by
    intro x hx'
    simp only [List.mem_append, List.mem_cons] at hx'
    rcases hx' with h | rfl | h
    · exact hzd x h
    · exact hc
    · exact hR x h
  -- the head of the fraction is a digit, so the zeros of `I` are skipped
  have hdot : Skips ('.' :: (Z ++ c :: (R ++ expPart ex))) := by
    cases Z with
    | nil => exact Or.inr ⟨c, _, rfl, hc⟩
    | cons z zs => exact Or.inr ⟨z, _, rfl, hzd z (by simp)⟩
  have hsc : scanLoop 0 (numBody I (some (Z ++ c :: R)) ++ expPart ex) {} =
      some { dpoint := some I.length, coeff := some (I.length + 1 + Z.length),
             exp := ex.map (fun _ => I.length + 1 + (Z ++ c :: R).length) } := by
    simp only [numBody, List.append_assoc, List.cons_append]
    rw [scan_zeros I _ 0 ({} : ScanState) ⟨rfl, rfl, rfl⟩ hI hdot, Nat.zero_add]
    rw [scan_dot _ _ _ rfl rfl rfl]
    rw [scan_zeros Z _ _ { dpoint := some I.length } ⟨rfl, rfl, rfl⟩ hZ hcd]
    have hfirst := scan_first c R (expPart ex) (I.length + 1 + Z.length) { dpoint := some I.length }
      ⟨rfl, rfl, rfl⟩ hc (h0.imp id (fun h => ⟨h, not_skips_exp ex hx⟩)) hR
    simp only [List.cons_append] at hfirst
    rw [hfirst]
    have hlen : I.length + 1 + Z.length + 1 + R.length = I.length + 1 + (Z ++ c :: R).length := by
      simp; omega
    rw [hlen, scan_exp ex hx _ _ rfl rfl rfl]
  have hP : (numBody I (some (Z ++ c :: R))).length = I.length + 1 + (Z ++ c :: R).length := by
    simp [numBody]; omega
  have hsplit : numBody I (some (Z ++ c :: R)) = (I ++ '.' :: Z) ++ c :: R := by
    simp [numBody]
  have hdrop : (numBody I (some (Z ++ c :: R))).drop (I.length + 1 + Z.length) = c :: R := by
    rw [hsplit]
    have : I.length + 1 + Z.length = (I ++ '.' :: Z).length := by simp; omega
    rw [this, List.drop_left]
  have hval : digitsValue (I ++ (Z ++ c :: R)) = digitsValue (c :: R) := by
    rw [digitsValue_zeros I _ hI, digitsValue_zeros Z _ hZ]
  rw [hval]
  apply mpdNumeric_eval neg _ ex hx _ (I.length + 1 + Z.length) _ _ (c :: R) hsc
  · rw [hP]
  · rfl
  · rw [hP]; simp
  · right
    refine ⟨I.length, rfl, ?_, ?_⟩
    · rw [hP]; omega
    · rw [hP, if_neg (by omega)]
      simp; omega
  · rw [hdrop, hP]
    have hR' : AD (c :: R) := by
      intro x hx'
      simp only [List.mem_cons] at hx'
      rcases hx' with rfl | h
      · exact hc
      · exact hR x h
    have : I.length + 1 + (Z ++ c :: R).length - (I.length + 1 + Z.length) = (c :: R).length := by
      simp; omega
    rw [this, List.take_length, filter_AD hR']
  · exact hf
  · have : ((c :: R).length : Int) ≤ ((Z ++ c :: R).length : Int) := by simp; omega
    omega
  · exact he1
  · exact he2

/-- `mpd_qset_string`'s numeric branch on `digits [. digits] [e [sign] digits]`
returns the exact value and exponent, given that the fraction is at most
`MPD_MAX_PREC` digits long, the significant digits fit, and the exponent is
within libmpdec's range. -/
theorem mpd_num (neg : Bool) (I : List Char) (fr : Option (List Char)) (ex : ExPart)
    (hI : AD I) (hF : AD (fr.getD [])) (hne : I ++ fr.getD [] ≠ []) (hx : ExOk ex)
    (hf : ((fr.getD []).length : Int) ≤ mpdMaxPrec)
    (hD : (numDigits (digitsValue (I ++ fr.getD [])) : Int) ≤ mpdMaxPrec)
    (he1 : mpdMinEtiny ≤ exVal ex - (fr.getD []).length)
    (he2 : exVal ex - ((fr.getD []).length : Int) ≤ mpdMaxEmax) :
    mpdNumeric neg (numBody I fr ++ expPart ex) =
      .fin neg (digitsValue (I ++ fr.getD [])) (numDigits (digitsValue (I ++ fr.getD [])))
        (exVal ex - (fr.getD []).length) := by
  have hAD : AD (I ++ fr.getD []) := by
    intro x hx'
    rcases List.mem_append.mp hx' with h | h
    · exact hI x h
    · exact hF x h
  have allZero : ∀ {L : List Char}, (∀ z ∈ L, z = '0') → AD L :=
    fun h z hz => by rw [h z hz]; exact zero_isDigit
  -- does the integer part hold a significant digit?
  by_cases hsig : ∃ Z c R, I = Z ++ c :: R ∧ (∀ z ∈ Z, z = '0') ∧ (c ≠ '0' ∨ (R = [] ∧ fr.getD [] = []))
  · obtain ⟨Z, c, R, rfl, hZ, h0⟩ := hsig
    have hc : c.isDigit = true := hI c (by simp)
    have hR : AD R := fun x h => hI x (by simp [h])
    have hsg : c ≠ '0' ∨ (R ++ fr.getD []) = [] := by
      rcases h0 with h | ⟨h1, h2⟩
      · exact Or.inl h
      · right; simp [h1, h2]
    have hval : digitsValue ((Z ++ c :: R) ++ fr.getD []) = digitsValue (c :: (R ++ fr.getD [])) := by
      rw [List.append_assoc, digitsValue_zeros Z _ hZ]; rfl
    have hnum := numDigits_sig c (R ++ fr.getD []) hc
      (fun x h => by
        rcases List.mem_append.mp h with h | h
        · exact hR x h
        · exact hF x h) hsg
    rw [hval, hnum] at hD
    rw [hval, hnum]
    have := mpd_caseA neg Z c R fr ex hZ hc hR hF hx h0 hf (by simpa using hD) he1 he2
    rw [this]
    congr 1
  · -- the integer part is all zeros, and the digits are in the fraction
    have hIz : ∀ z ∈ I, z = '0' := by
      by_cases hI0 : I = []
      · subst hI0; simp
      obtain ⟨Z, c, R, h1, h2, h3⟩ := digit_split I hI hI0
      have hc0 : c = '0' := by
        by_cases hc : c = '0'
        · exact hc
        · exact absurd ⟨Z, c, R, h1, h2, Or.inl hc⟩ hsig
      subst hc0
      have hR : R = [] := h3.resolve_left (fun h => h rfl)
      subst hR
      intro z hz
      rw [h1] at hz
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with h | h
      · exact h2 z h
      · exact h
    have hFne : fr.getD [] ≠ [] := by
      intro hF0
      by_cases hI0 : I = []
      · subst hI0; rw [hF0] at hne; exact hne rfl
      obtain ⟨Z, c, R, h1, h2, h3⟩ := digit_split I hI hI0
      have hc0 : c = '0' := hIz c (by rw [h1]; simp)
      subst hc0
      have hR : R = [] := h3.resolve_left (fun h => h rfl)
      exact hsig ⟨Z, '0', R, h1, h2, Or.inr ⟨hR, hF0⟩⟩
    cases fr with
    | none => exact absurd rfl hFne
    | some F =>
      simp only [Option.getD_some] at *
      obtain ⟨Z, c, R, rfl, hZ, h0⟩ := digit_split F hF hFne
      have hc : c.isDigit = true := hF c (by simp)
      have hR : AD R := fun x h => hF x (by simp [h])
      have hval : digitsValue (I ++ (Z ++ c :: R)) = digitsValue (c :: R) := by
        rw [digitsValue_zeros I _ hIz, digitsValue_zeros Z _ hZ]
      have hnum := numDigits_sig c R hc hR h0
      rw [hval] at hD ⊢
      rw [hnum] at hD ⊢
      have := mpd_caseB neg I Z c R ex hIz hZ hc hR hx h0 hf he1 he2
      rw [this, hval]

end PyLean.Decimal
