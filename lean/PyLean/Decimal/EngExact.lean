import PyLean.Decimal.RoundTrip
import PyLean.Decimal.Ops

/-!
`to_eng_string` (_pydecimal.py:1128-1135, `__str__(eng=True)`, :1076-1126): the engineering
spelling reads back to the same value, with the one or two trailing zeros it may add moved into
the coefficient, and its exponent, when it has one, is a multiple of three with one to three digits
before the point.
-/

namespace PyLean.Decimal

open PyLean

/-- The body of `__str__` for a given `dotplace` (_pydecimal.py:1110-1126). -/
def fmtDot (neg : Bool) (ds : List Char) (e dotplace : Int) (caps : Bool) : List Char :=
  let sign := if neg then ['-'] else []
  let leftdigits : Int := e + ds.length
  let (intpart, fracpart) :=
    if dotplace ≤ 0 then (['0'], '.' :: (List.replicate (-dotplace).toNat '0' ++ ds))
    else if dotplace ≥ ds.length then (ds ++ List.replicate (dotplace - ds.length).toNat '0', [])
    else (ds.take dotplace.toNat, '.' :: ds.drop dotplace.toNat)
  let exp := if leftdigits = dotplace then [] else
    (if caps then 'E' else 'e') :: fmtSigned (leftdigits - dotplace)
  sign ++ intpart ++ fracpart ++ exp

theorem engFinite_eq (neg : Bool) (ds : List Char) (e : Int) (caps : Bool) :
    engFinite neg ds e caps = fmtDot neg ds e (engDot (ds == ['0']) e (e + ds.length)) caps := rfl

/-- The trailing zeros the engineering spelling of `c·10^e` adds to the coefficient. -/
def engPad (c : Nat) (e : Int) : Nat :=
  let dp := engDot (Nat.toDigits 10 c == ['0']) e (e + numDigits c)
  if (numDigits c : Int) ≤ dp then (dp - numDigits c).toNat else 0

/-- What `Decimal(d.to_eng_string())` gives back: `d` with `engPad` zeros moved into the
coefficient (the same value and sign); the specials unchanged. -/
def engBack : Dec → Dec
  | .fin neg c e => .fin neg (c * 10 ^ engPad c e) (e - engPad c e)
  | d => d

theorem digitsValue_append_zeros (X : List Char) : ∀ z : Nat,
    digitsValue (X ++ List.replicate z '0') = digitsValue X * 10 ^ z
  | 0 => by simp
  | z + 1 => by
    rw [List.replicate_succ', ← List.append_assoc]
    have ih := digitsValue_append_zeros X z
    have h0 : (digitVal '0').getD 0 = 0 := by decide
    unfold digitsValue at ih ⊢
    rw [List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, h0, Nat.add_zero, Nat.pow_succ, Nat.mul_assoc]

/-- The engineering spelling has the shape `[-] I [. F] [E sign digits]` with `I ++ F` reading as
the coefficient with `z` zeros appended and the exponent reading back to `e - z`. -/
theorem fmtDot_shape (neg : Bool) (ds : List Char) (e dp : Int) (hA : AD ds) (hne : ds ≠ [])
    (h1 : dp ≤ 0 → -dp ≤ 5) (h2 : (ds.length : Int) ≤ dp → dp - ds.length ≤ 2) :
    ∃ I fr, fmtDot neg ds e dp true = (if neg then ['-'] else []) ++ numBody I fr ++
        expPart (if e + ds.length = dp then none else sciExp (e + ds.length - dp)) ∧
      I ≠ [] ∧ AD I ∧ AD (fr.getD []) ∧
      digitsValue (I ++ fr.getD []) =
        digitsValue ds * 10 ^ (if (ds.length : Int) ≤ dp then (dp - ds.length).toNat else 0) ∧
      exVal (if e + ds.length = dp then none else sciExp (e + ds.length - dp)) - ((fr.getD []).length : Int) =
        e - ((if (ds.length : Int) ≤ dp then (dp - ds.length).toNat else 0 : Nat) : Int) ∧
      (fr.getD []).length ≤ ds.length + 5 ∧ (I ++ fr.getD []).length ≤ ds.length + 6 ∧
      (1 ≤ dp → (I.length : Int) = dp) := by
  have hlen : 0 < ds.length := List.length_pos_iff.mpr hne
  have hexv : exVal (if e + ds.length = dp then none else sciExp (e + ds.length - dp)) = e + ds.length - dp := by
    split
    · simp [exVal]; omega
    · exact sciExp_val _
  have hexp : expPart (if e + ds.length = dp then none else sciExp (e + ds.length - dp)) =
      (if e + ds.length = dp then [] else 'E' :: fmtSigned (e + ds.length - dp)) := by
    split
    · rfl
    · exact sciExp_part _
  rw [hexv]
  simp only [fmtDot, hexp, ↓reduceIte]
  by_cases hd0 : dp ≤ 0
  · simp only [hd0, ↓reduceIte]
    refine ⟨['0'], some (List.replicate (-dp).toNat '0' ++ ds), ?_, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [numBody]
    · intro x hx; simp at hx; subst hx; exact zero_isDigit
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact replicate_zero_AD _ x h
      · exact hA x h
    · have hz : ¬ ((ds.length : Int) ≤ dp) := by omega
      simp only [hz, ↓reduceIte, Nat.pow_zero, Nat.mul_one, Option.getD_some, List.singleton_append]
      have : '0' :: (List.replicate (-dp).toNat '0' ++ ds) = List.replicate ((-dp).toNat + 1) '0' ++ ds := by
        simp [List.replicate_succ]
      rw [this, digitsValue_zeros _ _ (fun z hz => List.eq_of_mem_replicate hz)]
    · have hz : ¬ ((ds.length : Int) ≤ dp) := by omega
      simp only [hz, ↓reduceIte, Option.getD_some, List.length_append, List.length_replicate]
      omega
    · simp only [Option.getD_some, List.length_append, List.length_replicate]; omega
    · simp only [Option.getD_some, List.length_append, List.length_replicate, List.length_cons,
        List.length_nil]; omega
    · intro h; omega
  · simp only [hd0, ↓reduceIte]
    by_cases hd1 : dp ≥ ds.length
    · simp only [hd1, ↓reduceIte, ge_iff_le]
      refine ⟨ds ++ List.replicate (dp - ds.length).toNat '0', none, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [numBody]
      · simp [hne]
      · intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact hA x h
        · exact replicate_zero_AD _ x h
      · intro x hx; simp at hx
      · simp only [Option.getD_none, List.append_nil, digitsValue_append_zeros]
      · simp only [Option.getD_none, List.length_nil]; omega
      · simp
      · simp only [Option.getD_none, List.append_nil, List.length_append, List.length_replicate]; omega
      · intro _; simp only [List.length_append, List.length_replicate]; omega
    · simp only [hd1, ↓reduceIte, ge_iff_le]
      have hk : ds.take dp.toNat ++ ds.drop dp.toNat = ds := List.take_append_drop _ _
      have ht := take_drop_AD hA dp.toNat
      refine ⟨ds.take dp.toNat, some (ds.drop dp.toNat), ?_, ?_, ht.1, ht.2, ?_, ?_, ?_, ?_, ?_⟩
      · simp [numBody]
      · intro h0
        have hl := @List.length_take _ dp.toNat ds
        rw [h0] at hl
        simp only [List.length_nil] at hl
        omega
      · have hz : ¬ ((ds.length : Int) ≤ dp) := by omega
        simp only [hz, ↓reduceIte, Nat.pow_zero, Nat.mul_one, Option.getD_some, hk]
      · have hz : ¬ ((ds.length : Int) ≤ dp) := by omega
        simp only [hz, ↓reduceIte, Option.getD_some, List.length_drop]
        omega
      · simp only [Option.getD_some, List.length_drop]; omega
      · simp only [Option.getD_some, hk]; omega
      · intro _; simp only [List.length_take]; omega

/-- The `dotplace` of the engineering spelling stays within the bounds `fmtDot_shape` needs, and
puts the exponent, when there is one, at a multiple of three. -/
theorem engDot_bounds (z : Bool) (e : Int) (n : Nat) (hn : 1 ≤ n) (hz : z = true → n = 1) :
    let dp := engDot z e (e + n)
    (dp ≤ 0 → -dp ≤ 5) ∧ ((n : Int) ≤ dp → dp - n ≤ 2) ∧
    (e + n ≠ dp → (e + n - dp) % 3 = 0 ∧ (z = false → 1 ≤ dp ∧ dp ≤ 3)) := by
  intro dp
  simp only [dp, engDot]
  by_cases h : e ≤ 0 ∧ e + (n : Int) > -6
  · simp only [h, and_self, ↓reduceIte]
    refine ⟨fun _ => by omega, fun _ => by omega, fun h' => absurd rfl h'⟩
  · simp only [h, ↓reduceIte]
    cases z
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨fun _ => by omega, fun _ => by omega, fun _ => ⟨by omega, fun _ => ⟨by omega, by omega⟩⟩⟩
    · have := hz rfl
      subst this
      simp only [↓reduceIte]
      refine ⟨fun _ => by omega, fun _ => by omega, fun _ => ⟨by omega, fun h => nomatch h⟩⟩

theorem toDigits_eq_zero_iff (c : Nat) : (Nat.toDigits 10 c == ['0']) = true → numDigits c = 1 := by
  intro h
  have : Nat.toDigits 10 c = ['0'] := by simpa using h
  show (Nat.toDigits 10 c).length = 1
  rw [this]; rfl

theorem toDigits_ne_zero {c : Nat} (hc : c ≠ 0) : (Nat.toDigits 10 c == ['0']) = false := by
  have h := digitsValue_toDigits c
  cases hb : (Nat.toDigits 10 c == ['0'])
  · rfl
  · have : Nat.toDigits 10 c = ['0'] := by simpa using hb
    rw [this] at h
    have h0 : digitsValue ['0'] = 0 := by decide
    rw [h0] at h
    exact absurd h.symm hc


/-! ## The spellings, as the specification gives them

General Decimal Arithmetic, "to-scientific-string" and "to-engineering-string" (and the decimal
docs, `to_eng_string`): a finite number whose exponent is at most 0 and whose adjusted exponent is at
least -6 is written without an exponent, with `-e` digits after the point and a `0` before it when
needed; otherwise scientific notation puts one digit before the point and the adjusted exponent after
`E`, and engineering notation picks the exponent that is a multiple of three with one to three
digits before the point (for a zero: the least multiple of three at or above the exponent, the
places in between written as zeros after the point). These are written from that description, not
from `__str__`'s `dotplace` arithmetic. -/

def signSpec (neg : Bool) : List Char := if neg then ['-'] else []

/-- The digits `D` with `m` of them after a decimal point and at least one digit before it. -/
def plainSpec (D : List Char) (m : Nat) : List Char :=
  if m = 0 then D
  else if m < D.length then D.take (D.length - m) ++ '.' :: D.drop (D.length - m)
  else '0' :: '.' :: (List.replicate (m - D.length) '0' ++ D)

/-- `E±X` (`e±X` when `capitals` is 0), nothing for `X = 0`. -/
def expSpec (caps : Bool) (X : Int) : List Char :=
  if X = 0 then [] else (if caps then 'E' else 'e') :: fmtSigned X

/-- `Infinity`, `NaN` and `sNaN` with the sign and the payload digits. -/
def specialSpell : Dec → List Char
  | .inf neg => signSpec neg ++ "Infinity".toList
  | .nan neg sig p => signSpec neg ++ (if sig then "sNaN" else "NaN").toList ++
      (if p = 0 then [] else Nat.toDigits 10 p)
  | .fin _ _ _ => []

/-- Plain notation: exponent at most 0 and adjusted exponent at least -6. -/
def PlainNot (c : Nat) (e : Int) : Prop := e ≤ 0 ∧ e + (numDigits c : Int) - 1 ≥ -6

instance (c : Nat) (e : Int) : Decidable (PlainNot c e) := by unfold PlainNot; infer_instance

/-- The scientific spelling of `±c·10^e`. -/
def sciSpec (neg : Bool) (c : Nat) (e : Int) (caps : Bool) : List Char :=
  if PlainNot c e then signSpec neg ++ plainSpec (Nat.toDigits 10 c) (-e).toNat
  else signSpec neg ++ (Nat.toDigits 10 c).take 1 ++
    (if 1 < numDigits c then '.' :: (Nat.toDigits 10 c).drop 1 else []) ++
    expSpec caps (e + numDigits c - 1)

/-- The exponent the engineering spelling prints (`0`: none). -/
def engX (c : Nat) (e : Int) : Int :=
  if PlainNot c e then 0
  else if c = 0 then e + (-e) % 3
  else (e + numDigits c - 1) - (e + numDigits c - 1) % 3

/-- The engineering spelling of `±c·10^e`. -/
def engSpec (neg : Bool) (c : Nat) (e : Int) (caps : Bool) : List Char :=
  if PlainNot c e then signSpec neg ++ plainSpec (Nat.toDigits 10 c) (-e).toNat
  else if c = 0 then
    signSpec neg ++ '0' :: ((if engX c e = e then [] else '.' :: List.replicate (engX c e - e).toNat '0') ++
      expSpec caps (engX c e))
  else
    signSpec neg ++
      (Nat.toDigits 10 c ++ List.replicate ((e + numDigits c - engX c e).toNat - numDigits c) '0').take
        (e + numDigits c - engX c e).toNat ++
      (if (e + numDigits c - engX c e).toNat < numDigits c then
        '.' :: (Nat.toDigits 10 c).drop (e + numDigits c - engX c e).toNat else []) ++
      expSpec caps (engX c e)

/-! ## `__str__`'s arithmetic gives these spellings -/

theorem fmtDot_exp (e n dp : Int) (caps : Bool) :
    (if e + n = dp then [] else (if caps then 'E' else 'e') :: fmtSigned (e + n - dp)) =
      expSpec caps (e + n - dp) := by
  unfold expSpec
  by_cases h : e + n = dp
  · rw [if_pos h, if_pos (show e + n - dp = 0 by omega)]
  · rw [if_neg h, if_neg (show ¬ (e + n - dp = 0) by omega)]

theorem fmtDot_plain (neg : Bool) (D : List Char) (e : Int) (caps : Bool) (hn : 0 < D.length)
    (hp : e ≤ 0 ∧ e + (D.length : Int) - 1 ≥ -6) :
    fmtDot neg D e (e + D.length) caps = signSpec neg ++ plainSpec D (-e).toNat := by
  simp only [fmtDot, signSpec, plainSpec, ↓reduceIte, List.append_nil]
  by_cases h2 : e + (D.length : Int) ≤ 0
  · have m0 : ¬ (-e).toNat = 0 := by omega
    have m1 : ¬ ((-e).toNat < D.length) := by omega
    have m2 : (-e).toNat - D.length = (-(e + (D.length : Int))).toNat := by omega
    simp only [h2, ↓reduceIte, m0, m1, m2, List.append_assoc, List.singleton_append, List.cons_append,
      List.nil_append]
  · by_cases h3 : e + (D.length : Int) ≥ D.length
    · have he : e = 0 := by omega
      subst he
      have h4 : ¬ ((D.length : Int) ≤ 0) := by omega
      have hD : D ≠ [] := List.ne_nil_of_length_pos hn
      simp [h4, hD]
    · have m0 : ¬ (-e).toNat = 0 := by omega
      have m1 : (-e).toNat < D.length := by omega
      have m2 : D.length - (-e).toNat = (e + (D.length : Int)).toNat := by omega
      simp only [h2, h3, ↓reduceIte, m0, m1, m2, List.append_assoc]

theorem sciFinite_spec (neg : Bool) (c : Nat) (e : Int) (caps : Bool) :
    sciFinite neg (Nat.toDigits 10 c) e caps = sciSpec neg c e caps := by
  have hn : 0 < (Nat.toDigits 10 c).length := numDigits_pos c
  unfold sciSpec PlainNot
  by_cases hp : e ≤ 0 ∧ e + (numDigits c : Int) - 1 ≥ -6
  · rw [if_pos hp]
    have h1 : e ≤ 0 ∧ e + ((Nat.toDigits 10 c).length : Int) > -6 := by
      rw [toDigits_len]; omega
    have := fmtDot_plain neg (Nat.toDigits 10 c) e caps hn (by rw [toDigits_len]; omega)
    rw [← this]
    simp only [sciFinite, fmtDot, h1, and_self, ↓reduceIte]
  · rw [if_neg hp]
    have h1 : ¬ (e ≤ 0 ∧ e + (numDigits c : Int) > -6) := by omega
    have hx := fmtDot_exp e (numDigits c : Int) 1 caps
    rw [toDigits_len] at hn
    simp only [sciFinite, toDigits_len, h1, ↓reduceIte, signSpec, show ¬ ((1 : Int) ≤ 0) by omega,
      show ((1 : Int).toNat = 1) from rfl]
    rw [hx]
    by_cases h3 : (1 : Int) ≥ (numDigits c : Int)
    · have hl1 : numDigits c = 1 := by omega
      have ht : (Nat.toDigits 10 c).take 1 = Nat.toDigits 10 c :=
        List.take_of_length_le (by rw [toDigits_len]; omega)
      simp only [h3, ↓reduceIte, hl1, ht, Nat.lt_irrefl, List.append_nil,
        show ((1 : Int) - ((1 : Nat) : Int)).toNat = 0 from rfl, List.replicate_zero]
      simp
    · have hl1 : 1 < numDigits c := by omega
      simp only [h3, ↓reduceIte, hl1, List.append_assoc]

theorem fmtDot_pos (neg : Bool) (D : List Char) (e dp : Int) (caps : Bool) (hd : 1 ≤ dp) :
    fmtDot neg D e dp caps = signSpec neg ++
      (D ++ List.replicate (dp.toNat - D.length) '0').take dp.toNat ++
      (if dp.toNat < D.length then '.' :: D.drop dp.toNat else []) ++
      expSpec caps (e + D.length - dp) := by
  have hx := fmtDot_exp e (D.length : Int) dp caps
  simp only [fmtDot, signSpec]
  rw [hx]
  have h0 : ¬ dp ≤ 0 := by omega
  by_cases h3 : dp ≥ D.length
  · have hk : ¬ dp.toNat < D.length := by omega
    have hr : (dp - D.length).toNat = dp.toNat - D.length := by omega
    have ht : (D ++ List.replicate (dp.toNat - D.length) '0').take dp.toNat =
        D ++ List.replicate (dp.toNat - D.length) '0' :=
      List.take_of_length_le (by simp; omega)
    simp only [h0, h3, ↓reduceIte, hk, hr, ht, List.append_nil]
  · have hk : dp.toNat < D.length := by omega
    have hr : dp.toNat - D.length = 0 := by omega
    simp only [h0, h3, ↓reduceIte, hk, hr, List.replicate_zero, List.append_nil, List.append_assoc]

theorem fmtDot_zero (neg : Bool) (e dp : Int) (caps : Bool) (h1 : -1 ≤ dp) (h2 : dp ≤ 1) :
    fmtDot neg ['0'] e dp caps = signSpec neg ++ '0' ::
      ((if dp = 1 then [] else '.' :: List.replicate (1 - dp).toNat '0') ++ expSpec caps (e + 1 - dp)) := by
  have hx := fmtDot_exp e (1 : Int) dp caps
  simp only [fmtDot, signSpec, List.length_singleton, show ((1 : Nat) : Int) = 1 from rfl]
  rw [hx]
  by_cases hd : dp = 1
  · subst hd
    simp
  · have h0 : dp ≤ 0 := by omega
    have hr : (1 - dp).toNat = (-dp).toNat + 1 := by omega
    simp only [h0, hd, ↓reduceIte, hr, List.replicate_succ', List.append_assoc, List.cons_append,
      List.nil_append]

theorem engDot_plain (z : Bool) (e l : Int) (h : e ≤ 0 ∧ l > -6) : engDot z e l = l := by
  unfold engDot; rw [if_pos h]

/-- The engineering `dotplace` arithmetic gives the exponent `engX`. -/
theorem eng_dp (c : Nat) (e : Int) :
    e + ((Nat.toDigits 10 c).length : Int) -
      engDot (Nat.toDigits 10 c == ['0']) e (e + (Nat.toDigits 10 c).length) = engX c e := by
  have hn := numDigits_pos c
  rw [toDigits_len]
  unfold engX PlainNot
  by_cases hp : e ≤ 0 ∧ e + (numDigits c : Int) - 1 ≥ -6
  · rw [engDot_plain _ _ _ (by omega), if_pos hp]; omega
  · rw [if_neg hp]
    unfold engDot
    rw [if_neg (by omega)]
    by_cases hc : c = 0
    · subst hc
      have hz : (Nat.toDigits 10 0 == ['0']) = true := rfl
      have h0 : numDigits 0 = 1 := rfl
      simp only [hz, ↓reduceIte, h0]
      omega
    · rw [toDigits_ne_zero hc, if_neg hc]
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega

theorem engFinite_spec (neg : Bool) (c : Nat) (e : Int) (caps : Bool) :
    engFinite neg (Nat.toDigits 10 c) e caps = engSpec neg c e caps := by
  have hn : 0 < (Nat.toDigits 10 c).length := numDigits_pos c
  have hX := eng_dp c e
  rw [engFinite_eq]
  unfold engSpec
  by_cases hp : PlainNot c e
  · rw [if_pos hp]
    unfold PlainNot at hp
    rw [engDot_plain _ _ _ (by rw [toDigits_len]; omega)]
    exact fmtDot_plain neg _ e caps hn (by rw [toDigits_len]; omega)
  · rw [if_neg hp]
    by_cases hc : c = 0
    · subst hc
      rw [if_pos rfl]
      have hz : Nat.toDigits 10 0 = ['0'] := rfl
      rw [hz] at hX ⊢
      simp only [List.length_singleton, show ((1 : Nat) : Int) = 1 from rfl] at hX ⊢
      generalize hdp : engDot (['0'] == ['0']) e (e + 1) = dp at hX ⊢
      have hb : -1 ≤ dp ∧ dp ≤ 1 := by
        rw [← hdp]; unfold engDot
        split
        · unfold PlainNot at hp; rw [show numDigits 0 = 1 from rfl] at hp; omega
        · simp only [show (['0'] == ['0']) = true from rfl, ↓reduceIte]; omega
      rw [fmtDot_zero neg e dp caps hb.1 hb.2, hX]
      have e1 : (engX 0 e = e) ↔ dp = 1 := by omega
      have e2 : (engX 0 e - e).toNat = (1 - dp).toNat := by omega
      by_cases hd : dp = 1
      · rw [if_pos hd, if_pos (e1.mpr hd)]
      · rw [if_neg hd, if_neg (fun h => hd (e1.mp h)), e2]
    · rw [if_neg hc]
      generalize hdp : engDot (Nat.toDigits 10 c == ['0']) e (e + (Nat.toDigits 10 c).length) = dp at hX ⊢
      have hb : 1 ≤ dp := by
        rw [← hdp]; unfold engDot
        split
        · unfold PlainNot at hp; rw [toDigits_len] at *; omega
        · rw [toDigits_ne_zero hc]; simp only [Bool.false_eq_true, ↓reduceIte]; omega
      rw [fmtDot_pos neg _ e dp caps hb, hX]
      rw [toDigits_len] at hX
      have hk : e + (numDigits c : Int) - engX c e = dp := by omega
      rw [hk, toDigits_len]

/-- `str(d)` of a finite value: the scientific spelling, raising the int/str-limit `ValueError`
when it prints an adjusted exponent of more than 4300 digits. -/
theorem pyStr_fin_spell (neg : Bool) (c : Nat) (e : Int) (caps : Bool) :
    pyStr (.fin neg c e) caps =
      if ¬ PlainNot c e ∧ maxStrDigits < numDigits (e + numDigits c - 1).natAbs then
        .error (.valueError limitToStrMsg)
      else .ok (sciSpec neg c e caps) := by
  have hn := numDigits_pos c
  rw [← sciFinite_spec]
  simp only [pyStr, Dec.toPyObj, pyStrObj, toDigits_len]
  unfold PlainNot
  by_cases hp : e ≤ 0 ∧ e + (numDigits c : Int) - 1 ≥ -6
  · have h1 : e ≤ 0 ∧ e + (numDigits c : Int) > -6 := by omega
    simp only [h1, and_self, ↓reduceIte, ne_eq, not_true_eq_false, hp, not_false_eq_true,
      false_and]
    rfl
  · have h1 : ¬ (e ≤ 0 ∧ e + (numDigits c : Int) > -6) := by omega
    have h2 : e + (numDigits c : Int) ≠ 1 := by omega
    simp only [h1, ↓reduceIte, ne_eq, h2, not_false_eq_true, hp, true_and, strLimit, gt_iff_lt]
    by_cases hl : maxStrDigits < numDigits (e + (numDigits c : Int) - 1).natAbs
    · rw [if_pos hl, if_pos hl]; rfl
    · rw [if_neg hl, if_neg hl]; rfl

theorem pyStr_special (d : Dec) (caps : Bool) (h : isSpecial d = true) :
    pyStr d caps = .ok (specialSpell d) := by
  cases d with
  | fin => exact absurd h (by simp [isSpecial])
  | inf neg => cases neg <;> rfl
  | nan neg sig p => cases neg <;> cases sig <;> rfl

theorem pyEngObj_num_eq (neg : Bool) (I : List Char) (x : Int) (caps : Bool) :
    pyEngObj ⟨neg, I, .num x⟩ caps =
      (strLimit (x + (I.length : Int) - engDot (I == ['0']) x (x + I.length)).natAbs).bind
        (fun _ => .ok (engFinite neg I x caps)) := by
  simp only [pyEngObj]
  split
  · rfl
  · rename_i h
    have h0 : x + (I.length : Int) - engDot (I == ['0']) x (x + I.length) = 0 := by
      simp only [ne_eq, Decidable.not_not] at h; omega
    rw [h0]; rfl

theorem pyEng_fin_spell (neg : Bool) (c : Nat) (e : Int) (caps : Bool) :
    pyEng (.fin neg c e) caps =
      if maxStrDigits < numDigits (engX c e).natAbs then .error (.valueError limitToStrMsg)
      else .ok (engSpec neg c e caps) := by
  rw [← engFinite_spec]
  show pyEngObj ⟨neg, Nat.toDigits 10 c, .num e⟩ caps = _
  rw [pyEngObj_num_eq, eng_dp]
  simp only [strLimit, gt_iff_lt]
  by_cases hl : maxStrDigits < numDigits (engX c e).natAbs
  · rw [if_pos hl, if_pos hl]; rfl
  · rw [if_neg hl, if_neg hl]; rfl

theorem pyEng_special (d : Dec) (caps : Bool) (h : isSpecial d = true) :
    pyEng d caps = .ok (specialSpell d) := by
  cases d with
  | fin => exact absurd h (by simp [isSpecial])
  | inf neg => cases neg <;> rfl
  | nan neg sig p => cases neg <;> cases sig <;> rfl

/-! ## Reading the spelling back -/

theorem pyEngObj_num (neg : Bool) (I : List Char) (x : Int)
    (h : strLimit (x + (I.length : Int) - engDot (I == ['0']) x (x + I.length)).natAbs = .ok ()) :
    pyEngObj ⟨neg, I, .num x⟩ = .ok (engFinite neg I x true) := by
  simp only [pyEngObj]
  split
  · rw [h]; rfl
  · rfl

theorem engPad_eq (c : Nat) (e : Int) :
    engPad c e = (if ((Nat.toDigits 10 c).length : Int) ≤ engDot (Nat.toDigits 10 c == ['0']) e (e + (Nat.toDigits 10 c).length)
      then (engDot (Nat.toDigits 10 c == ['0']) e (e + (Nat.toDigits 10 c).length) - (Nat.toDigits 10 c).length).toNat
      else 0) := rfl

/-- The finite case: the spelling, its shape, and what it reads back as, whenever the printed
exponent has at most 4300 digits. -/
theorem eng_fin (neg : Bool) (c : Nat) (e : Int) (hXd : numDigits (engX c e).natAbs ≤ maxStrDigits) :
    ∃ I fr x, pyEng (.fin neg c e) = .ok ((if neg then ['-'] else []) ++ numBody I fr ++ expPart x) ∧
      I ≠ [] ∧ AD I ∧ AD (fr.getD []) ∧ ExOk x ∧
      digitsValue (I ++ fr.getD []) = c * 10 ^ engPad c e ∧
      exVal x - ((fr.getD []).length : Int) = e - engPad c e ∧
      (I ++ fr.getD []).length ≤ numDigits c + 6 ∧
      (∀ ind sg D, x = some (ind, sg, D) → D.length ≤ maxStrDigits) := by
  have hn := numDigits_pos c
  have hds := toDigits_AD c
  have hlen := toDigits_len c
  have hne : Nat.toDigits 10 c ≠ [] := Nat.toDigits_ne_nil
  have hval := digitsValue_toDigits c
  have hXdp := eng_dp c e
  have hz1 : (Nat.toDigits 10 c == ['0']) = true → (Nat.toDigits 10 c).length = 1 := by
    intro h; rw [hlen]; exact toDigits_eq_zero_iff c h
  obtain ⟨b1, b2, b3⟩ := engDot_bounds (Nat.toDigits 10 c == ['0']) e (Nat.toDigits 10 c).length
    (by rw [hlen]; exact hn) hz1
  generalize hdp : engDot (Nat.toDigits 10 c == ['0']) e (e + (Nat.toDigits 10 c).length) = dp at b1 b2 b3 hXdp
  obtain ⟨I, fr, h1, hI0, hI, hF, hv, he, hfl, hl, hId⟩ := fmtDot_shape neg (Nat.toDigits 10 c) e dp hds hne b1 b2
  refine ⟨I, fr, if e + (Nat.toDigits 10 c).length = dp then none else sciExp (e + (Nat.toDigits 10 c).length - dp),
    ?_, hI0, hI, hF, ?_, ?_, ?_, ?_, ?_⟩
  · have hs : pyEng (.fin neg c e) = .ok (engFinite neg (Nat.toDigits 10 c) e true) := by
      apply pyEngObj_num
      rw [hdp, hXdp]
      unfold strLimit
      rw [if_neg (Nat.not_lt.mpr hXd)]
    rw [hs, engFinite_eq, hdp, h1]
  · split
    · trivial
    · exact sciExp_ok _
  · rw [hv, hval, engPad_eq, hdp]
  · rw [he, engPad_eq, hdp]
  · rw [hlen] at hl; exact hl
  · intro ind sg D hD
    split at hD
    · cases hD
    · simp only [sciExp, Option.some.injEq, Prod.mk.injEq] at hD
      rw [← hD.2.2, hXdp]
      exact hXd

theorem engPad_zero (e : Int) : engPad 0 e = 0 := by
  unfold engPad engDot
  simp only [show (Nat.toDigits 10 0 == ['0']) = true from rfl, show numDigits 0 = 1 from rfl, ↓reduceIte]
  (repeat' split) <;> omega

/-! ## The statements -/

/-- `str(d)` in `_pydecimal` (`Decimal.__str__`, _pydecimal.py:1076-1126, `eng=False`, with
`capitals` from the context, :1122-1124), for every value and both `capitals` settings: a finite
`±c·10^e` is spelled `sciSpec` (plain notation when the exponent is at most 0 and the adjusted
exponent at least -6, otherwise one digit, the rest after a point, and `E`/`e` with the signed
adjusted exponent), and raises the int/str-limit `ValueError` of `"%+d"` (:1124) exactly when it
would print an adjusted exponent of more than 4300 digits; infinities and NaNs are `Infinity`, `NaN`,
`sNaN` with the sign and the payload. There is no other bound: `_pydecimal`'s exponents are ints. -/
def StrSpellExact : Prop :=
  (∀ (neg : Bool) (c : Nat) (e : Int) (caps : Bool),
    pyStr (.fin neg c e) caps =
      if ¬ PlainNot c e ∧ maxStrDigits < numDigits (e + numDigits c - 1).natAbs then
        .error (.valueError limitToStrMsg)
      else .ok (sciSpec neg c e caps)) ∧
  (∀ (d : Dec) (caps : Bool), isSpecial d = true → pyStr d caps = .ok (specialSpell d))

theorem strSpellExact_proven : StrSpellExact :=
  ⟨pyStr_fin_spell, pyStr_special⟩

/-- `Decimal.to_eng_string()` in `_pydecimal` (_pydecimal.py:1128-1135, `__str__(eng=True)` with the
context's `capitals`, :1076-1126), for every value and both `capitals` settings:

* a finite `±c·10^e` is spelled `engSpec`: plain notation as `str()` when the exponent is at most 0
  and the adjusted exponent at least -6; otherwise the exponent `engX` is a multiple of three, the
  greatest at or below the adjusted exponent for a non-zero value (one to three digits before the
  point, trailing zeros added when the coefficient is shorter), the least at or above the exponent
  for a zero (the places in between written as zeros after the point), and is omitted when it is 0;
* it raises the int/str-limit `ValueError` of `"%+d"` (:1124) exactly when that exponent has more
  than 4300 digits (the C twin has no such limit);
* infinities and NaNs as in `str()`;
* `Decimal(d.to_eng_string())` is `d` with the zero to two trailing zeros the spelling adds moved into
  the coefficient (same sign and value), for every `d` whose spelling stays inside `int()`'s
  limit (coefficient of at most 4294 digits, printed exponent and NaN payload of at most 4300). -/
def EngStringExact : Prop :=
  (∀ (neg : Bool) (c : Nat) (e : Int) (caps : Bool),
    pyEng (.fin neg c e) caps =
      if maxStrDigits < numDigits (engX c e).natAbs then .error (.valueError limitToStrMsg)
      else .ok (engSpec neg c e caps)) ∧
  (∀ (d : Dec) (caps : Bool), isSpecial d = true → pyEng d caps = .ok (specialSpell d)) ∧
  (∀ (c : Nat) (e : Int), engX c e % 3 = 0 ∧
    (¬ PlainNot c e → c ≠ 0 → 1 ≤ e + numDigits c - engX c e ∧ e + numDigits c - engX c e ≤ 3) ∧
    (¬ PlainNot c e → c = 0 → e ≤ engX c e ∧ engX c e - e ≤ 2)) ∧
  (∀ d : Dec,
    (∀ neg c e, d = .fin neg c e → numDigits c + 6 ≤ maxStrDigits ∧ numDigits (engX c e).natAbs ≤ maxStrDigits) →
    (∀ neg s p, d = .nan neg s p → numDigits p ≤ maxStrDigits) →
    (pyEng d >>= pyParse) = .ok (engBack d)) ∧
  (∀ (c : Nat) (e : Int), engPad c e ≤ 2 ∧ (c = 0 → engPad c e = 0))

theorem engX_facts (c : Nat) (e : Int) : engX c e % 3 = 0 ∧
    (¬ PlainNot c e → c ≠ 0 → 1 ≤ e + numDigits c - engX c e ∧ e + numDigits c - engX c e ≤ 3) ∧
    (¬ PlainNot c e → c = 0 → e ≤ engX c e ∧ engX c e - e ≤ 2) := by
  unfold engX
  refine ⟨?_, fun hp hc => ?_, fun hp hc => ?_⟩
  · split
    · rfl
    · split <;> omega
  · rw [if_neg hp, if_neg hc]; omega
  · rw [if_neg hp, if_pos hc]; omega

theorem engStringExact_proven : EngStringExact := by
  refine ⟨pyEng_fin_spell, pyEng_special, engX_facts, fun d hb1 hb2 => ?_, fun c e => ?_⟩
  · cases d with
    | inf neg => cases neg <;> decide
    | nan neg sig p =>
      have hs : pyEng (.nan neg sig p) =
          .ok ((if neg then ['-'] else []) ++ (if sig then "sNaN" else "NaN").toList ++ payDigits p) := by
        cases sig <;> simp only [pyEng, Dec.toPyObj, pyEngObj, payDigits] <;> rfl
      rw [hs]
      exact pyParse_nan neg sig p (hb2 neg sig p rfl)
    | fin neg c e =>
      obtain ⟨hb, hXd⟩ := hb1 neg c e rfl
      obtain ⟨I, fr, x, hs, hI0, hI, hF, hx, hv, he, hl, hD⟩ := eng_fin neg c e hXd
      rw [hs]
      show pyParse _ = _
      simp only [pyParse]
      rw [pyFilter_plain _ (plain_body I fr x hI hF hx neg), pyMatch_shape neg I fr x hI0 hI hF hx]
      simp only
      rw [pyNum_shape neg I _ x hx (by omega) hD, hv, he]
      rfl
  · have hn := numDigits_pos c
    have hz1 : (Nat.toDigits 10 c == ['0']) = true → (Nat.toDigits 10 c).length = 1 := by
      intro h; rw [toDigits_len]; exact toDigits_eq_zero_iff c h
    obtain ⟨_, b2, _⟩ := engDot_bounds (Nat.toDigits 10 c == ['0']) e (Nat.toDigits 10 c).length
      (by rw [toDigits_len]; exact hn) hz1
    refine ⟨?_, fun hc => ?_⟩
    · rw [engPad_eq]; split
      · have := b2 (by assumption); omega
      · omega
    · subst hc
      exact engPad_zero e

/-- `repr(d)` in `_pydecimal` (_pydecimal.py:1071-1074, `"Decimal('%s')" % str(self)`, with
`str(self)` reading `getcontext().capitals`, :1122-1124; the comment states the invariant
`eval(repr(d)) == d`), for every value and both `capitals` settings: the quoted `sciSpec` spelling
for a finite value, raising the int/str-limit `ValueError` exactly when `str()` would print an
adjusted exponent of more than 4300 digits (`Decimal((0, (1,), 10**4300))`); the quoted special
spellings; and for every value whose `str()` stays inside `int()`'s limit (coefficient of at most
4294 digits, adjusted exponent and NaN payload of at most 4300; exponents beyond the C module's
`10**18` are fine, `Decimal((0, (1,), 10**19))`), the quoted string reads back to `d` exactly. -/
def ReprExact : Prop :=
  (∀ (neg : Bool) (c : Nat) (e : Int) (caps : Bool),
    pyRepr (.fin neg c e) caps =
      if ¬ PlainNot c e ∧ maxStrDigits < numDigits (e + numDigits c - 1).natAbs then
        .error (.valueError limitToStrMsg)
      else .ok ("Decimal('".toList ++ sciSpec neg c e caps ++ "')".toList)) ∧
  (∀ (d : Dec) (caps : Bool), isSpecial d = true →
    pyRepr d caps = .ok ("Decimal('".toList ++ specialSpell d ++ "')".toList)) ∧
  (∀ (d : Dec) (caps : Bool),
    (∀ neg c e, d = .fin neg c e →
      numDigits c + 6 ≤ maxStrDigits ∧ numDigits (e + numDigits c - 1).natAbs ≤ maxStrDigits) →
    (∀ neg s p, d = .nan neg s p → numDigits p ≤ maxStrDigits) →
    ∃ s, pyRepr d caps = .ok ("Decimal('".toList ++ s ++ "')".toList) ∧ pyParse s = .ok d)

theorem pyRepr_eq (d : Dec) (caps : Bool) :
    pyRepr d caps = (fun s => "Decimal('".toList ++ s ++ "')".toList) <$> pyStr d caps := by
  simp only [pyRepr, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

theorem reprExact_proven : ReprExact := by
  refine ⟨fun neg c e caps => ?_, fun d caps h => ?_, fun d caps h1 h2 => ?_⟩
  · rw [pyRepr_eq, pyStr_fin_spell]
    split <;> rfl
  · rw [pyRepr_eq, pyStr_special d caps h]; rfl
  · have h := strRoundTripPyBounded_proven d caps h1 h2
    cases hs : pyStr d caps with
    | error x => rw [hs] at h; exact absurd h (by simp [bind, Except.bind])
    | ok s =>
      rw [hs] at h
      exact ⟨s, by rw [pyRepr_eq, hs]; rfl, h⟩

end PyLean.Decimal
