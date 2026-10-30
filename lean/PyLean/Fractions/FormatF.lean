import PyLean.Fractions.FormatProps
import PyLean.Fractions.Round

/-!
Fixed-point formatting (`'.{p}f'`) against `round(x, p)` and the string
constructor: `Fraction(format(x, f'.{p}f')) == round(x, p)`.
-/

namespace PyLean.Fractions

open PyLean

/-! ## Half-even rounding is unique -/

theorem halfEven_le_succ {S T n d : Int} (hd : 0 < d) (hS : 2 * (n - S * d) ≤ d)
    (hT : -d ≤ 2 * (n - T * d)) : T ≤ S + 1 := by
  apply Int.le_of_not_gt
  intro hc
  have := mul_le_mul_r (show S + 2 ≤ T by omega) (Int.le_of_lt hd)
  grind

theorem halfEven_unique {R R' n d : Int} (hd : 0 < d) (h : HalfEven R n d) (h' : HalfEven R' n d) :
    R = R' := by
  obtain ⟨a1, a2, a3⟩ := h
  obtain ⟨b1, b2, b3⟩ := h'
  have hle : ∀ {S T : Int}, 2 * (n - S * d) ≤ d → -d ≤ 2 * (n - T * d) → T ≤ S + 1 :=
    fun hS hT => halfEven_le_succ hd hS hT
  have h1 := hle a2 b1
  have h2 := hle b2 a1
  rcases Int.lt_trichotomy R R' with hlt | heq | hgt
  · have e : R' = R + 1 := by omega
    subst e
    have t1 : 2 * (n - R * d) = d := by grind
    have := a3 (Or.inl t1)
    have := b3 (Or.inr (by grind))
    omega
  · exact heq
  · have e : R = R' + 1 := by omega
    subst e
    have t1 : 2 * (n - R' * d) = d := by grind
    have := b3 (Or.inl t1)
    have := a3 (Or.inr (by grind))
    omega

/-- The half-even rounding of a negative value is `<= 0`, of a non-negative one `>= 0`. -/
theorem halfEven_sign {R n d : Int} (hd : 0 < d) (h : HalfEven R n d) :
    (n < 0 → R ≤ 0) ∧ (0 ≤ n → 0 ≤ R) := by
  obtain ⟨a1, a2, _⟩ := h
  constructor
  · intro hn
    apply Int.le_of_not_gt; intro hR
    have := mul_le_mul_r (show 1 ≤ R by omega) (Int.le_of_lt hd)
    grind
  · intro hn
    apply Int.le_of_not_gt; intro hR
    have := mul_le_mul_r (show R ≤ -1 by omega) (Int.le_of_lt hd)
    grind

/-- `_round_to_exponent` rounds half to even. -/
theorem roundToExponent_halfEven (n d : Int) (hd : 0 < d) :
    let r := pyDiv (n + d / 2) d
    let q := if pyMod (n + d / 2) d = 0 ∧ d % 2 = 0 then r - pyMod r 2 else r
    HalfEven q n d := by
  intro r q
  have hdiv : pyDiv (n + d / 2) d = (n + d / 2) / d := pyDiv_of_nonneg _ (by omega)
  have hmod : pyMod (n + d / 2) d = (n + d / 2) % d := pyMod_of_nonneg _ (by omega)
  have hm2 : pyMod r 2 = r % 2 := pyMod_of_nonneg _ (by decide)
  have e := Int.mul_ediv_add_emod (n + d / 2) d
  have r0 := Int.emod_nonneg (n + d / 2) (show d ≠ 0 by omega)
  have r1 := Int.emod_lt_of_pos (n + d / 2) hd
  have hh := Int.mul_ediv_add_emod d 2
  have hh0 := Int.emod_nonneg d (show (2 : Int) ≠ 0 by decide)
  have hh1 := Int.emod_lt_of_pos d (show (0 : Int) < 2 by decide)
  simp only [q, hm2, hmod]
  rw [show r = (n + d / 2) / d from hdiv] at *
  generalize (n + d / 2) / d = r0' at e ⊢
  generalize (n + d / 2) % d = rr at e r0 r1 ⊢
  generalize d / 2 = h at e hh ⊢
  generalize d % 2 = dd at hh hh0 hh1 ⊢
  have base : n - r0' * d = rr - h := by grind
  split
  · rename_i hc
    obtain ⟨hr, hdd⟩ := hc
    subst hr; subst hdd
    have hr2 := Int.emod_def r0' 2
    have hq0 := Int.emod_nonneg r0' (show (2 : Int) ≠ 0 by decide)
    have hq1 := Int.emod_lt_of_pos r0' (show (0 : Int) < 2 by decide)
    have e2 : n - (r0' - r0' % 2) * d = (r0' % 2) * d - h := by grind
    unfold HalfEven
    rw [e2]
    rcases (show r0' % 2 = 0 ∨ r0' % 2 = 1 by omega) with hz | hz
    · rw [hz]; refine ⟨by omega, by omega, fun _ => by omega⟩
    · rw [hz]; refine ⟨by omega, by omega, fun _ => by omega⟩
  · rename_i hc
    unfold HalfEven
    rw [base]
    refine ⟨by omega, by omega, fun ht => ?_⟩
    exfalso; apply hc; omega

/-! ## Parsing strings of ASCII digits -/

/-- All characters are ASCII digits. -/
def Asc (l : List Char) : Prop := ∀ c ∈ l, 48 ≤ c.toNat ∧ c.toNat ≤ 57

theorem asc_append {l m : List Char} (h1 : Asc l) (h2 : Asc m) : Asc (l ++ m) := by
  intro c hc; rcases List.mem_append.mp hc with h | h; exact h1 c h; exact h2 c h

theorem asc_take {l : List Char} (h : Asc l) (k : Nat) : Asc (l.take k) :=
  fun c hc => h c (List.mem_of_mem_take hc)

theorem asc_drop {l : List Char} (h : Asc l) (k : Nat) : Asc (l.drop k) :=
  fun c hc => h c (List.mem_of_mem_drop hc)

theorem asc_D (n : Nat) : Asc (D n) := fun _ hc => mem_D hc

theorem asc_zfill {l : List Char} (h : Asc l) (w : Int) : Asc (zfill l w) := by
  apply asc_append _ h
  intro c hc
  rw [List.eq_of_mem_replicate hc]; decide

theorem asc_head {l : List Char} (h : Asc l) (hne : l ≠ []) :
    ∃ c cs, l = c :: cs ∧ 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  cases l with
  | nil => exact absurd rfl hne
  | cons c cs => exact ⟨c, cs, rfl, h c (by simp)⟩

theorem digitRun_asc (L rest : List Char) (hL : Asc L) (hne : L ≠ [])
    (hrest : ∀ c r, rest = c :: r → isDigit c = false ∧ c ≠ '_') :
    digitRun (L ++ rest) = (L, rest) := by
  obtain ⟨c, cs, hcs, hc⟩ := asc_head hL hne
  subst hcs
  have hp := ascii_digit_props hc
  simp only [List.cons_append, digitRun, hp.1, ↓reduceIte]
  rw [runTail_digits cs rest (fun x hx => hL x (by simp [hx])) hrest]

theorem skipWs_asc (L rest : List Char) (hL : Asc L) (hne : L ≠ []) :
    skipWs (L ++ rest) = L ++ rest := by
  obtain ⟨c, cs, hcs, hc⟩ := asc_head hL hne
  subst hcs
  simp [skipWs, (ascii_digit_props hc).2.2.1]

theorem splitSign_asc (L rest : List Char) (hL : Asc L) (hne : L ≠ []) :
    splitSign (L ++ rest) = (false, L ++ rest) := by
  obtain ⟨c, cs, hcs, hc⟩ := asc_head hL hne
  subst hcs
  have hp := ascii_digit_props hc
  rw [List.cons_append]
  unfold splitSign
  split
  · rename_i h; simp at h; exact absurd h.1 hp.2.2.2.2.1
  · rename_i h; simp at h; exact absurd h.1 hp.2.2.2.2.2.1
  · rfl

theorem digitsValue_asc (L : List Char) (hL : Asc L) : digitsValue L = Nat.ofDigitChars 10 L 0 := by
  simp only [digitsValue]; exact foldl_digits L hL 0

theorem pyIntOfDigits_asc (L : List Char) (hL : Asc L) (hne : L ≠ []) (hlen : L.length ≤ maxStrDigits) :
    pyIntOfDigits L = .ok (digitsValue L) := by
  have hfilter : L.filter isDigit = L := by
    apply List.filter_eq_self.mpr
    intro x hx; exact (ascii_digit_props (hL x hx)).1
  have hs := splitSign_asc L [] hL hne
  simp only [List.append_nil] at hs
  simp only [pyIntOfDigits, hs, hfilter]
  rw [ite_eq_right (show ¬ L.length > maxStrDigits by omega)]
  rfl

theorem sign_prefix_parse (neg : Bool) (L rest : List Char) (hL : Asc L) (hne : L ≠ []) :
    skipWs ((if neg then ['-'] else []) ++ L ++ rest) = (if neg then ['-'] else []) ++ L ++ rest ∧
    splitSign ((if neg then ['-'] else []) ++ L ++ rest) = (neg, L ++ rest) ∧
    lookahead (L ++ rest) = true := by
  obtain ⟨c, cs, hcs, hc⟩ := asc_head hL hne
  have hp := ascii_digit_props hc
  refine ⟨?_, ?_, ?_⟩
  · cases neg
    · simpa using skipWs_asc L rest hL hne
    · simp [skipWs, isWs]
  · cases neg
    · simpa using splitSign_asc L rest hL hne
    · simp [splitSign]
  · rw [hcs]; simp [lookahead, hp.1]

/-- `_RATIONAL_FORMAT` on `[-]digits`. -/
theorem match_int (neg : Bool) (L : List Char) (hL : Asc L) (hne : L ≠ []) :
    matchRational ((if neg then ['-'] else []) ++ L) = some ⟨neg, L, none, none, none⟩ := by
  obtain ⟨h1, h2, h3⟩ := sign_prefix_parse neg L [] hL hne
  simp only [List.append_nil] at h1 h2 h3
  have hrun : digitRun L = (L, []) := by
    simpa using digitRun_asc L [] hL hne (by intro c r h; simp at h)
  simp only [matchRational, h1, h2, h3, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hrun]
  simp [skipWs]

/-- `_RATIONAL_FORMAT` on `[-]digits.digits`. -/
theorem match_dec (neg : Bool) (L F : List Char) (hL : Asc L) (hne : L ≠ []) (hF : Asc F)
    (hFne : F ≠ []) :
    matchRational ((if neg then ['-'] else []) ++ L ++ ('.' :: F)) =
      some ⟨neg, L, none, some F, none⟩ := by
  obtain ⟨h1, h2, h3⟩ := sign_prefix_parse neg L ('.' :: F) hL hne
  have hrun : digitRun (L ++ '.' :: F) = (L, '.' :: F) :=
    digitRun_asc L _ hL hne (by intro c r h; simp at h; rw [← h.1]; decide)
  have hrunF : digitRun F = (F, []) := by
    simpa using digitRun_asc F [] hF hFne (by intro c r h; simp at h)
  simp only [matchRational, h1, h2, h3, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hrun]
  simp [skipWs, isWs, hrunF, expGroup]

theorem no_underscore {F : List Char} (hF : Asc F) : F.filter (· ≠ '_') = F := by
  apply List.filter_eq_self.mpr
  intro x hx
  have := (ascii_digit_props (hF x hx)).2.2.2.1
  simpa using this

theorem parse_int (neg : Bool) (L : List Char) (hL : Asc L) (hne : L ≠ [])
    (hlen : L.length ≤ maxStrDigits) :
    parse ((if neg then ['-'] else []) ++ L) =
      normalize (if neg then -(digitsValue L : Int) else digitsValue L) 1 := by
  have hm := match_int neg L hL hne
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.singleton_append, List.cons_append]
    at hm ⊢ <;>
    simp [parse, hm, hne, pyIntOfDigits_asc L hL hne hlen, bind, Except.bind, pure, Except.pure]

theorem parse_dec (neg : Bool) (L F : List Char) (hL : Asc L) (hne : L ≠ []) (hF : Asc F)
    (hFne : F ≠ []) (hlen : L.length ≤ maxStrDigits) (hlenF : F.length ≤ maxStrDigits) :
    parse ((if neg then ['-'] else []) ++ L ++ ('.' :: F)) =
      normalize (if neg then -((digitsValue L : Int) * 10 ^ F.length + digitsValue F)
        else (digitsValue L : Int) * 10 ^ F.length + digitsValue F) (10 ^ F.length) := by
  have hm := match_dec neg L F hL hne hF hFne
  have hnu : F.filter (fun x => !decide (x = '_')) = F := by simpa using no_underscore hF
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.singleton_append, List.cons_append]
    at hm ⊢ <;>
    simp [parse, hm, hne, hFne, hnu, pyIntOfDigits_asc L hL hne hlen,
      pyIntOfDigits_asc F hF hFne hlenF, bind, Except.bind, pure, Except.pure]

/-! ## The `'.{p}f'` spec -/

/-- The rounded integer `_round_to_exponent` computes, before taking `abs`. -/
def rteQ (n d : Int) : Int :=
  let r := pyDiv (n + d / 2) d
  if pyMod (n + d / 2) d = 0 ∧ d % 2 = 0 then r - pyMod r 2 else r

theorem rteQ_halfEven (n d : Int) (hd : 0 < d) : HalfEven (rteQ n d) n d :=
  roundToExponent_halfEven n d hd

theorem roundToExponent_f (n d : Int) (p : Nat) :
    roundToExponent n d (-(p : Int)) false =
      (decide (n * 10 ^ p < 0), ((rteQ (n * 10 ^ p) d).natAbs : Int)) := by
  by_cases hp : p = 0
  · subst hp
    simp [roundToExponent, rteQ]
  · have : ¬ (0 ≤ -(p : Int)) := by omega
    simp only [roundToExponent, this, ↓reduceIte, Bool.false_eq_true, rteQ]
    have e : (-(-(p : Int))).toNat = p := by omega
    simp only [e]

theorem isAsciiDigit_eq (c : Char) : isAsciiDigit c = c.isDigit := rfl

theorem isAsciiDigit_of {c : Char} (h : 48 ≤ c.toNat ∧ c.toNat ≤ 57) : isAsciiDigit c = true := by
  rw [isAsciiDigit_eq]
  exact Char.isDigit_iff_toNat.mpr (by simpa using h)

theorem asciiDigits_asc (L r : List Char) (hL : Asc L) (hr : ∀ c t, r = c :: t → isAsciiDigit c = false) :
    asciiDigits (L ++ r) = (L, r) := by
  induction L with
  | nil =>
    cases r with
    | nil => rfl
    | cons c t => simp [asciiDigits, hr c t rfl]
  | cons c cs ih =>
    have hdig := isAsciiDigit_of (hL c (by simp))
    rw [List.cons_append]
    simp only [asciiDigits, hdig, ↓reduceIte]
    rw [ih (fun x hx => hL x (by simp [hx]))]

theorem match_spec_f (p : Nat) :
    matchGeneral ('.' :: (D p ++ ['f'])) = none ∧
    matchFloat ('.' :: (D p ++ ['f'])) =
      some ⟨none, none, [], false, false, false, none, none, some (D p), none, 'f'⟩ := by
  obtain ⟨c, cs, hcs, hc⟩ := D_head p
  have hdig := isAsciiDigit_of hc
  have hal : isAlign c = false := by
    cases h : isAlign c
    · rfl
    · exfalso
      simp only [isAlign, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with ((h | h) | h) | h <;> (rw [h] at hc; simp at hc)
  have hspan := asciiDigits_asc (D p) ['f'] (asc_D p) (by intro c t h; simp at h; rw [← h.1]; decide)
  have hascs : Asc cs := fun x hx => asc_D p x (by rw [hcs]; simp [hx])
  have hspan' := asciiDigits_asc cs ['f'] hascs (by intro c t h; simp at h; rw [← h.1]; decide)
  rw [hcs] at hspan ⊢
  have hdot : isAsciiDigit '.' = false := by decide
  have hdotal : isAlign '.' = false := by decide
  refine ⟨?_, ?_⟩
  · simp [matchGeneral, fillAlign, hal, hdotal, signPart, optChar, sepPart, isAsciiDigit]
  · simp [matchFloat, fillAlign, hal, hdotal, signPart, optChar, sepPart, asciiDigits, hdot, hdig,
      hspan, hspan', isFloatType]

theorem numDigits_le_of_le {p : Nat} (hp : p ≤ maxStrDigits) : numDigits p ≤ maxStrDigits := by
  unfold numDigits
  have : p < 10 ^ maxStrDigits := by
    have := Nat.lt_pow_self (n := p) (a := 10) (by decide)
    have h2 : 10 ^ p ≤ 10 ^ maxStrDigits := Nat.pow_le_pow_right (by decide) hp
    omega
  exact (Nat.length_toDigits_le_iff (by decide) (by unfold maxStrDigits; decide)).mpr this

theorem zfill_length (l : List Char) (w : Nat) : (zfill l w).length = max w l.length := by
  simp [zfill]; omega

theorem digitsValue_zfill (n : Nat) (w : Int) : digitsValue (zfill (D n) w) = n := by
  rw [digitsValue_asc _ (asc_zfill (asc_D n) w)]
  simp only [zfill, Nat.ofDigitChars_append, Nat.ofDigitChars_replicate_zero, Nat.mul_zero]
  exact Nat.ofDigitChars_ten_toDigits

theorem digitsValue_split (L F : List Char) (hL : Asc L) (hF : Asc F) :
    digitsValue (L ++ F) = digitsValue L * 10 ^ F.length + digitsValue F := by
  rw [digitsValue_asc _ (asc_append hL hF), digitsValue_asc _ hL, digitsValue_asc _ hF,
    Nat.ofDigitChars_append, Nat.ofDigitChars_eq_ofDigitChars_zero]
  rw [Nat.mul_comm]

theorem normalize_den_one (n : Int) : normalize n 1 = .ok ⟨n, 1⟩ := by
  simp [normalize, pyDiv]; rfl

/-- `round(x, p)` is the half-even rounding of `x * 10**p`, as an equation. -/
theorem roundTo_eq (x : Frac) (hx : x.Normal) (p : Nat) (q : Int)
    (hq : HalfEven q (x.num * 10 ^ p) x.den) :
    roundTo x p = (if p = 0 then .ok ⟨q, 1⟩ else normalize q (10 ^ p)) := by
  by_cases hp0 : p = 0
  · subst hp0
    have hb : (ofInt (10 ^ (0 : Int).natAbs)).Normal := ⟨by simp [ofInt], by simp [ofInt]⟩
    obtain ⟨m, hm, hmn, hmv⟩ := div_spec x (ofInt (10 ^ (0 : Int).natAbs)) hx hb (by simp [ofInt])
    have hR := round_halfEven m hmn.1
    have hR' : HalfEven (round m) (x.num * 10 ^ 0) x.den := by
      apply halfEven_congr hmn.1 hx.1 _ hR
      simp only [ofInt] at hmv; simp at hmv ⊢; rw [hmv]
    have := halfEven_unique hx.1 hR' hq
    have hm' : div x ⟨1, 1⟩ = .ok m := by simpa [ofInt] using hm
    simp [roundTo, bind, Except.bind, pure, Except.pure, ofInt, hm', this]
  · have hpos : (0 : Int) < (p : Int) := by omega
    obtain ⟨hmn, hmv⟩ := mul_spec x (ofInt (10 ^ (p : Int).natAbs)) hx ⟨by simp [ofInt], by simp [ofInt]⟩
    have hR := round_halfEven (mul x (ofInt (10 ^ (p : Int).natAbs))) hmn.1
    have hR' : HalfEven (round (mul x (ofInt (10 ^ (p : Int).natAbs)))) (x.num * 10 ^ p) x.den := by
      apply halfEven_congr hmn.1 hx.1 _ hR
      simp only [ofInt, Int.mul_one, Int.natAbs_natCast] at hmv ⊢
      exact hmv
    have := halfEven_unique hx.1 hR' hq
    simp only [Int.natAbs_natCast] at this
    simp only [roundTo, hpos, ↓reduceIte, hp0, ofInts, Int.natAbs_natCast, this]

/-- Fixed-point formatting agrees with `round` (an implementation
self-consistency property: `format`, `round` and the string constructor are
three separate code paths). For every Fraction `x` and precision
`0 <= p <= 4300` (the int string-conversion limit applies to the `p`
fractional digits when the string is parsed back), whenever
`format(x, f'.{p}f')` returns `s`, `Fraction(s) == round(x, p)`. -/
def FormatFRoundTrip : Prop :=
  ∀ x : Frac, x.Normal → ∀ p : Nat, p ≤ maxStrDigits → ∀ s,
    format x ('.' :: (D p ++ ['f'])) = .ok s → parse s = roundTo x p

theorem formatFRoundTrip_proven : FormatFRoundTrip := by
  intro x hx p hp s hs
  obtain ⟨hG, hF⟩ := match_spec_f p
  have hprec : pyIntOfDigits (D p) = .ok p := pyIntOfDigits_D p (numDigits_le_of_le hp)
  have hrte := roundToExponent_f x.num x.den p
  generalize hqdef : rteQ (x.num * 10 ^ p) x.den = q at hrte
  have hstr : ∀ t, strInt (q.natAbs : Int) = .ok t → t = D q.natAbs ∧ numDigits q.natAbs ≤ maxStrDigits := by
    intro t ht
    simp only [strInt] at ht
    split at ht
    · cases ht
    · cases ht
      rename_i hlt
      simp only [Int.natAbs_natCast] at hlt
      exact ⟨by simp, by omega⟩
  cases hsq : strInt (q.natAbs : Int) with
  | error e =>
    simp [format, hG, hF, formatFloat, specInt, hprec, hrte, bind, Except.bind, pure, Except.pure,
      hsq] at hs
  | ok t =>
    obtain ⟨ht, hlim⟩ := hstr t hsq
    subst ht
    simp [format, hG, hF, formatFloat, specInt, hprec, hrte, bind, Except.bind, pure, Except.pure,
      hsq, alignPad, Option.getD] at hs
    have h4300 : maxStrDigits = 4300 := rfl
    rw [rep_nonpos _ _ (by omega), List.nil_append] at hs
    have hq := rteQ_halfEven (x.num * 10 ^ p) x.den hx.1
    rw [hqdef] at hq
    have hsgn := halfEven_sign hx.1 hq
    have hval : (if x.num * 10 ^ p < 0 then -((q.natAbs : Nat) : Int) else ((q.natAbs : Nat) : Int)) = q := by
      split
      · have := hsgn.1 (by assumption); omega
      · have := hsgn.2 (by omega); omega
    generalize hZ : zfill (D q.natAbs) (↑p + 1) = Z at hs
    have hZlen : Z.length = max (p + 1) (D q.natAbs).length := by
      rw [← hZ, show ((p : Int) + 1) = ((p + 1 : Nat) : Int) by omega, zfill_length]
    have hZasc : Asc Z := hZ ▸ asc_zfill (asc_D _) _
    have hZval : digitsValue Z = q.natAbs := hZ ▸ digitsValue_zfill _ _
    have hDlen : (D q.natAbs).length ≤ maxStrDigits := hlim
    have hLasc : Asc (Z.take (Z.length - p)) := asc_take hZasc _
    have hFasc : Asc (Z.drop (Z.length - p)) := asc_drop hZasc _
    have hLne : Z.take (Z.length - p) ≠ [] := by
      intro h; have := congrArg List.length h; simp at this; omega
    have hLlen : (Z.take (Z.length - p)).length ≤ maxStrDigits := by simp; omega
    have hFlen : (Z.drop (Z.length - p)).length = p := by simp; omega
    have hsplit : Z = Z.take (Z.length - p) ++ Z.drop (Z.length - p) := (List.take_append_drop _ _).symm
    have hvsplit := digitsValue_split _ _ hLasc hFasc
    rw [← hsplit, hFlen, hZval] at hvsplit
    rw [roundTo_eq x hx p q hq, ← hs]
    by_cases hp0 : p = 0
    · subst hp0
      have hZne : Z ≠ [] := by
        intro h; rw [h] at hZlen; simp only [List.length_nil] at hZlen; omega
      have e1 : (if x.num * 10 ^ 0 < 0 then ['-'] else []) ++ (List.take (Z.length - 0) Z ++
          ((if Z.length ≤ Z.length - 0 then [] else ['.']) ++ List.drop (Z.length - 0) Z)) =
          (if decide (x.num * 10 ^ 0 < 0) = true then ['-'] else []) ++ Z := by simp
      have := parse_int (decide (x.num * 10 ^ 0 < 0)) Z hZasc hZne (by rw [hZlen]; omega)
      rw [e1, this, hZval, normalize_den_one]
      simp only [decide_eq_true_eq]
      rw [hval]
      simp
    · have hcond : ¬ (Z.length ≤ Z.length - p) := by omega
      simp only [hcond, ↓reduceIte, hp0]
      have hFne : Z.drop (Z.length - p) ≠ [] := by
        intro h; have := congrArg List.length h; simp at this; omega
      have := parse_dec (decide (x.num * 10 ^ p < 0)) _ _ hLasc hLne hFasc hFne hLlen
        (by rw [hFlen]; exact hp)
      simp only [decide_eq_true_eq] at this
      rw [show ['.'] ++ Z.drop (Z.length - p) = '.' :: Z.drop (Z.length - p) by rfl,
        ← List.append_assoc, this, hFlen]
      have e : ((digitsValue (Z.take (Z.length - p)) : Int) * 10 ^ p +
          (digitsValue (Z.drop (Z.length - p)) : Int)) = ((q.natAbs : Nat) : Int) := by
        rw [hvsplit]; push_cast; rfl
      rw [e, hval]

end PyLean.Fractions
