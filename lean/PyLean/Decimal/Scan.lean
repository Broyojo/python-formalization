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

end PyLean.Decimal
