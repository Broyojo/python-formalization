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

/-- `Decimal.to_eng_string()` in `_pydecimal`, for every value within the C limits whose
coefficient has at most 4294 digits (NaN payload at most 4300), as `decimal-str-roundtrip-py-bounded`
bounds `str()`:

* `Decimal(d.to_eng_string())` is `d` with the `engPad c e ≤ 2` trailing zeros the spelling adds
  moved into the coefficient (`engBack`): the same sign and value, the exponent lowered by as much;
  zeros and the specials come back exactly;
* the spelling of a finite `d` is `[-] I [. F] [E±x]`, and when it has an exponent (that is, unless
  `d`'s exponent is at most 0 and its adjusted exponent at least -6), `x` is a multiple of three
  and, for a non-zero `d`, `I` has one to three digits. -/
def EngStringExact : Prop :=
  (∀ d : Dec, InCLimits d →
    (∀ neg c e, d = .fin neg c e → numDigits c + 6 ≤ maxStrDigits) →
    (∀ neg s p, d = .nan neg s p → numDigits p ≤ maxStrDigits) →
    (pyEng d >>= pyParse) = .ok (engBack d)) ∧
  (∀ (neg : Bool) (c : Nat) (e : Int), engPad c e ≤ 2 ∧ (c = 0 → engPad c e = 0)) ∧
  (∀ (neg : Bool) (c : Nat) (e : Int), InCLimits (.fin neg c e) →
    ∃ I fr x, pyEng (.fin neg c e) = .ok ((if neg then ['-'] else []) ++ numBody I fr ++ expPart x) ∧
      (∀ y, x = sciExp y → y % 3 = 0 ∧ (c ≠ 0 → 1 ≤ I.length ∧ I.length ≤ 3)))

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

/-- The finite case: the spelling, its shape, and what it reads back as, within the C limits. -/
theorem eng_fin (neg : Bool) (c : Nat) (e : Int) (hlim : InCLimits (.fin neg c e)) :
    ∃ I fr x, pyEng (.fin neg c e) = .ok ((if neg then ['-'] else []) ++ numBody I fr ++ expPart x) ∧
      I ≠ [] ∧ AD I ∧ AD (fr.getD []) ∧ ExOk x ∧
      digitsValue (I ++ fr.getD []) = c * 10 ^ engPad c e ∧
      exVal x - ((fr.getD []).length : Int) = e - engPad c e ∧
      (I ++ fr.getD []).length ≤ numDigits c + 6 ∧
      (∀ ind sg D, x = some (ind, sg, D) → D.length ≤ maxStrDigits) ∧
      (∀ y, x = sciExp y → y % 3 = 0 ∧ (c ≠ 0 → 1 ≤ I.length ∧ I.length ≤ 3)) := by
  obtain ⟨_, hl2, hl3⟩ := hlim
  simp only [mpdMaxEmax, mpdMinEtiny, mpdMinEmin, mpdMaxPrec] at hl2 hl3
  have hn := numDigits_pos c
  have hds := toDigits_AD c
  have hlen := toDigits_len c
  have hne : Nat.toDigits 10 c ≠ [] := Nat.toDigits_ne_nil
  have hval := digitsValue_toDigits c
  have hsl : ∀ m : Nat, m < 10 ^ 20 → numDigits m ≤ maxStrDigits := by
    intro m hm
    have := (numDigits_le_iff (n := m) (k := 20) (by decide)).mpr hm
    simp only [maxStrDigits]; omega
  have hsz : ∀ m : Nat, m < 10 ^ 20 → strLimit m = .ok () := by
    intro m hm
    unfold strLimit
    rw [if_neg (Nat.not_lt.mpr (hsl m hm))]
  have hz1 : (Nat.toDigits 10 c == ['0']) = true → (Nat.toDigits 10 c).length = 1 := by
    intro h; rw [hlen]; exact toDigits_eq_zero_iff c h
  obtain ⟨b1, b2, b3⟩ := engDot_bounds (Nat.toDigits 10 c == ['0']) e (Nat.toDigits 10 c).length
    (by rw [hlen]; exact hn) hz1
  generalize hdp : engDot (Nat.toDigits 10 c == ['0']) e (e + (Nat.toDigits 10 c).length) = dp at b1 b2 b3
  have hdpB : e + (Nat.toDigits 10 c).length - dp = 0 ∨ (-5 ≤ dp ∧ dp ≤ 3) := by
    rw [← hdp]
    unfold engDot; split
    · left; omega
    · right; split <;> omega
  obtain ⟨I, fr, h1, hI0, hI, hF, hv, he, hfl, hl, hId⟩ := fmtDot_shape neg (Nat.toDigits 10 c) e dp hds hne b1 b2
  refine ⟨I, fr, if e + (Nat.toDigits 10 c).length = dp then none else sciExp (e + (Nat.toDigits 10 c).length - dp),
    ?_, hI0, hI, hF, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hs : pyEng (.fin neg c e) = .ok (engFinite neg (Nat.toDigits 10 c) e true) := by
      apply pyEngObj_num
      rw [hdp]
      exact hsz _ (by rw [hlen] at hdpB ⊢; omega)
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
      rw [← hD.2.2]
      exact hsl _ (by rw [hlen] at hdpB ⊢; omega)
  · intro y hy
    split at hy
    · cases hy
    · rename_i hne'
      have hyv : y = e + (Nat.toDigits 10 c).length - dp := by
        have := congrArg exVal hy
        rw [sciExp_val, sciExp_val] at this
        exact this.symm
      obtain ⟨h3a, h3b⟩ := b3 hne'
      refine ⟨by rw [hyv]; exact h3a, fun hc => ?_⟩
      have := h3b (toDigits_ne_zero hc)
      have := hId this.1
      omega

/-- `repr(d)` in `_pydecimal` (_pydecimal.py:1071-1074, whose comment states the invariant
`eval(repr(d)) == d`): it is `Decimal('` + `str(d)` + `')`, raising what `str(d)` raises, and for
every value within the C limits whose coefficient has at most 4294 digits (NaN payload at most 4300)
the quoted string reads back to `d` exactly: sign, coefficient, exponent, NaN kind and payload. -/
def ReprExact : Prop :=
  (∀ d : Dec, pyRepr d = (fun s => "Decimal('".toList ++ s ++ "')".toList) <$> pyStr d) ∧
  (∀ d : Dec, InCLimits d →
    (∀ neg c e, d = .fin neg c e → numDigits c + 6 ≤ maxStrDigits) →
    (∀ neg s p, d = .nan neg s p → numDigits p ≤ maxStrDigits) →
    ∃ s, pyRepr d = .ok ("Decimal('".toList ++ s ++ "')".toList) ∧ pyParse s = .ok d)

theorem reprExact_proven : ReprExact := by
  refine ⟨fun d => ?_, fun d hl h1 h2 => ?_⟩
  · simp only [pyRepr, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  · have h := strRoundTripPyBounded_proven d hl h1 h2
    cases hs : pyStr d with
    | error x => rw [hs] at h; exact absurd h (by simp [bind, Except.bind])
    | ok s =>
      rw [hs] at h
      exact ⟨s, by simp [pyRepr, hs, bind, Except.bind, pure, Except.pure], h⟩

theorem engPad_zero (e : Int) : engPad 0 e = 0 := by
  unfold engPad engDot
  simp only [show (Nat.toDigits 10 0 == ['0']) = true from rfl, show numDigits 0 = 1 from rfl, ↓reduceIte]
  (repeat' split) <;> omega

theorem engStringExact_proven : EngStringExact := by
  refine ⟨fun d hlim hb1 hb2 => ?_, fun neg c e => ?_, fun neg c e hlim => ?_⟩
  · cases d with
    | inf neg => cases neg <;> decide
    | nan neg sig p =>
      have hs : pyEng (.nan neg sig p) =
          .ok ((if neg then ['-'] else []) ++ (if sig then "sNaN" else "NaN").toList ++ payDigits p) := by
        cases sig <;> simp only [pyEng, Dec.toPyObj, pyEngObj, payDigits] <;> rfl
      rw [hs]
      exact pyParse_nan neg sig p (hb2 neg sig p rfl)
    | fin neg c e =>
      obtain ⟨I, fr, x, hs, hI0, hI, hF, hx, hv, he, hl, hD, _⟩ := eng_fin neg c e hlim
      have hb := hb1 neg c e rfl
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
  · obtain ⟨I, fr, x, hs, _, _, _, _, _, _, _, _, h3⟩ := eng_fin neg c e hlim
    exact ⟨I, fr, x, hs, h3⟩

end PyLean.Decimal
