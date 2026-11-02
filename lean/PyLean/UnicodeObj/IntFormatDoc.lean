import PyLean.UnicodeObj.StrFormatDoc
import PyLean.UnicodeObj.FormatProps
import PyLean.UnicodeObj.FormatGroupDoc

/-!
`format(n, fill + align + width + 'd')` against `format(str(n), fill + align + width + 's')`: with
`<`, `>` or `^` an int is laid out like its decimal string. On the model of `FormatSpec.lean`:
`_PyLong_FormatAdvancedWriter` (`formatLongAdvanced`), `format_long_internal`, the slow path's
`calc_number_widths` and `fill_number`, Objects/unicode_formatter.c.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- `str(n)` for an int within the int/str digit limit: a `-`, then the decimal digits. -/
def decimalStr (v : Int) : Str := (if v < 0 then [45] else []) ++ digitsOf 10 v.natAbs

/-- The head parse with any defaults, fill and alignment given. -/
theorem parseHead_spec' (fill align : Nat) (d : Nat) (rest : List Nat) (dt da : Nat)
    (hal : isAlignmentToken align = true) (hd : d < 10) :
    parseHead (fill :: align :: (d + 48) :: rest) dt da =
      ({ align := align, type := dt, fillChar := fill }, (d + 48) :: rest) := by
  have h1 : isSignElement (d + 48) = false := by revert d; decide
  have h2 : (d + 48 == 122) = false := by revert d; decide
  have h3 : (d + 48 == 35) = false := by revert d; decide
  simp [parseHead, parseAlign, hal, parseFlags, h1, headIs, h2, h3]

theorem d_nondigit : toDecimalDigit 100 < 0 := by decide

/-- For every int `n` within the 4300-digit limit, every fill character, alignment `<`, `>` or
`^` and width in ASCII digits (at most `sys.maxsize`), `format(n, fill + align + width + 'd')` is
the documented padding of `str(n)`, and so equals `format(str(n), fill + align + width + 's')`. -/
def IntFormatAsStr : Prop :=
  ∀ (v : Int) (fill align : Nat) (wd : List Nat) (emptyStr : Str),
    (align = 60 ∨ align = 62 ∨ align = 94) →
    wd ≠ [] → (∀ d ∈ wd, d < 10) → accum 0 wd ≤ ssizeMax → (digitsOf 10 v.natAbs).length ≤ 4300 →
    formatLongAdvanced v "int" ([fill, align] ++ asciiDigits wd ++ [100]) emptyStr
      = .ok (some (docFormat (decimalStr v) fill align (accum 0 wd) none)) ∧
    formatStrAdvanced (decimalStr v) ([fill, align] ++ asciiDigits wd ++ [115])
      = .ok (docFormat (decimalStr v) fill align (accum 0 wd) none)

theorem intFormatAsStr_proven : IntFormatAsStr := by
  intro v fill align wd emptyStr halign hwne hwd hwbig hlim
  refine ⟨?_, by
    have := strFormatDoc_proven (decimalStr v) fill align wd none halign hwne hwd hwbig (by simp)
    simpa using this⟩
  have hal : isAlignmentToken align = true := by rcases halign with h | h | h <;> subst h <;> decide
  have h61 : align ≠ 61 := by omega
  obtain ⟨d, ds, rfl⟩ : ∃ d ds, wd = d :: ds := by
    cases wd with | nil => exact absurd rfl hwne | cons d ds => exact ⟨d, ds, rfl⟩
  have hd := hwd d (by simp)
  have hhead := parseHead_spec' fill align d (asciiDigits ds ++ [100]) 100 62 hal hd
  have hw := getInteger_digits (d :: ds) [100] 0 0 (Int.le_refl _) hwd (by simp [d_nondigit]) hwbig
  have hw0 : 0 ≤ accum 0 (d :: ds) := accum_mono _ 0 (Int.le_refl _)
  unfold formatLongAdvanced parseFormatSpec
  simp only [asciiDigits, List.map_cons, List.cons_append, List.nil_append, List.append_assoc] at hhead hw ⊢
  rw [hhead]
  simp [List.isEmpty, parseTail, parseWidth, hw, headIs, bind, Except.bind, pure, Except.pure, parseType,
    validateSpec, LT_NO_LOCALE]
  -- format_long_internal: no precision, no z, type 'd', a width, so the slow path
  have hwne1 : accum 0 (d :: ds) ≠ -1 := by omega
  obtain ⟨hdne, hdm⟩ := digitsOf_spec 10 v.natAbs
  simp only [formatLongInternal, formatLongSlow, longFormat, hwne1, Functor.map, Except.map]
  simp [hlim, bind, Except.bind, pure, Except.pure, localeInfo, LT_CURRENT_LOCALE, LT_DEFAULT_LOCALE,
    LT_UNDERSCORE_LOCALE, LT_UNDER_FOUR_LOCALE]
  rw [if_neg hwne1, if_neg (by omega)]
  generalize hds : digitsOf 10 v.natAbs = D at hdne hdm
  generalize hW : accum 0 (d :: ds) = W at hw0 hwne1
  have hD0 : (D.head? == some 45) = false := by
    cases D with
    | nil => exact absurd rfl hdne
    | cons x xs => simpa using hdm x (by simp)
  have hng := noGroup D hdne 0 (Int.le_refl 0)
  have hfill : ((fill == 48 && align == 61) = true) ↔ False := by simp [h61]
  by_cases hv : v < 0
  · simp only [hv, if_true, List.cons_append, List.nil_append, List.head?_cons, List.tail_cons]
    simp [calcNumberWidths, hfill, hng, bind, Except.bind, pure, Except.pure, fillNumber, docFormat, decimalStr,
      hv, hds, keptText, hdne]
    have e1 : (W - (1 + (D.length : Int))).toNat = W.toNat - (D.length + 1) := by omega
    by_cases hp : 1 + (D.length : Int) < W
    · rcases halign with h | h | h <;> subst h <;> simp [hp, e1]
    · have e0 : W.toNat - (D.length + 1) = 0 := by omega
      rcases halign with h | h | h <;> subst h <;> simp [hp, e0]
  · have hD0' : D.head? ≠ some 45 := by simpa using hD0
    simp only [hv, if_false, List.nil_append, hD0]
    simp [hD0', calcNumberWidths, hfill, hng, bind, Except.bind, pure, Except.pure, fillNumber, docFormat, decimalStr,
      hv, hds, keptText, hdne]
    have e1 : (W - (D.length : Int)).toNat = W.toNat - D.length := by omega
    by_cases hp : (D.length : Int) < W
    · rcases halign with h | h | h <;> subst h <;> simp [hp, e1]
    · have e0 : W.toNat - D.length = 0 := by omega
      rcases halign with h | h | h <;> subst h <;> simp [hp, e0]

/-! ## Every int spec -/

/-- The message of the int/str digit limit (`sys.get_int_max_str_digits()`, default 4300). -/
def intLimitMessage : String :=
  "Exceeds the limit (4300 digits) for integer string conversion; use sys.set_int_max_str_digits() to increase the limit"

/-- `format(v, spec)` for an int and a parsed spec with an integer type, as the docs describe it
(Doc/library/string.rst, "integer presentation types"): no precision and no `z`; for `c` no sign and
no `#`, and the character `chr(v)` (refused outside `range(0x110000)`, and first outside a C `long`);
for `b`, `o`, `x`, `X`, `d`, `n` the digits of `|v|` in base 2, 8, 16 or 10 (`Nat.toDigits`), upper
case for `X`, after the prefix `0b`, `0o`, `0x` or `0X` that `#` adds, grouped by 3 for `,` and `_`
and by 4 for `_` with `b`, `o`, `x`, `X`, and laid out by `docNumber`. `n` is `d` in the C locale.
Base 10 keeps the 4300-digit limit of `str(int)`. -/
def docInt (v : Int) (f : FormatSpec) : Py Str :=
  if f.precision ≠ -1 then .error (.valueError "Precision not allowed in integer format specifier")
  else if f.noNeg0 then
    .error (.valueError "Negative zero coercion (z) not allowed in integer format specifier")
  else if f.type = 99 then
    if f.sign ≠ 0 then .error (.valueError "Sign not allowed with integer format specifier 'c'")
    else if f.alternate then
      .error (.valueError "Alternate form (#) not allowed with integer format specifier 'c'")
    else if v > 2 ^ 63 - 1 ∨ v < -(2 ^ 63) then
      .error (.overflowError "Python int too large to convert to C long")
    else if v < 0 ∨ v > 0x10ffff then .error (.overflowError "%c arg not in range(0x110000)")
    else .ok (docNumber [] [] [] 0 [] [v.toNat] f)
  else
    let base : Nat := if f.type = 98 then 2 else if f.type = 111 then 8
      else if f.type = 120 ∨ f.type = 88 then 16 else 10
    let digits := Nat.toDigits base v.natAbs
    if base = 10 ∧ 4300 < digits.length then .error (.valueError intLimitMessage)
    else
      let ds : Str := if f.type = 88 then digits.map (fun c => c.toUpper.toNat) else digits.map Char.toNat
      let pfx : Str := if f.alternate ∧ base ≠ 10 then [48, f.type] else []
      let gs : Nat × Str := if f.thousands = 44 then (3, [44]) else if f.thousands = 95 then (3, [95])
        else if f.thousands = 96 then (4, [95]) else (0, [])
      .ok (docNumber (signStr f.sign (v < 0)) pfx ds gs.1 gs.2 [] f)

theorem digitChar_hex (d : Nat) (h : d < 16) : (Nat.digitChar d).toNat = hexLower d := by
  revert d; decide

theorem digitChar_upper (d : Nat) (h : d < 16) :
    pyToUpper (Nat.digitChar d).toNat = (Nat.digitChar d).toUpper.toNat := by
  revert d; decide

theorem natDigits_eq (b : Nat) (hb : 0 < b) (hb16 : b ≤ 16) :
    ∀ (fuel n : Nat) (acc : List Char),
      natDigits b fuel n (acc.map Char.toNat) = (Nat.toDigitsCore b fuel n acc).map Char.toNat := by
  intro fuel
  induction fuel with
  | zero => intro n acc; rfl
  | succ fuel ih =>
    intro n acc
    have hd := digitChar_hex (n % b) (by have := Nat.mod_lt n hb; omega)
    simp only [natDigits, Nat.toDigitsCore]
    have e : hexLower (n % b) :: acc.map Char.toNat = (Nat.digitChar (n % b) :: acc).map Char.toNat := by
      simp [hd]
    rw [e]
    split
    · rfl
    · exact ih _ _

theorem digitsOf_eq (b n : Nat) (hb : 0 < b) (hb16 : b ≤ 16) :
    digitsOf b n = (Nat.toDigits b n).map Char.toNat :=
  natDigits_eq b hb hb16 (n + 1) n []

theorem toDigitsCore_mem (b : Nat) (hb : 0 < b) :
    ∀ (fuel n : Nat) (acc : List Char), (∀ c ∈ acc, ∃ d < b, c = Nat.digitChar d) →
      ∀ c ∈ Nat.toDigitsCore b fuel n acc, ∃ d < b, c = Nat.digitChar d := by
  intro fuel
  induction fuel with
  | zero => intro n acc h; exact h
  | succ fuel ih =>
    intro n acc h
    have h' : ∀ c ∈ Nat.digitChar (n % b) :: acc, ∃ d < b, c = Nat.digitChar d := by
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ⟨n % b, Nat.mod_lt n hb, rfl⟩
      · exact h c hc
    simp only [Nat.toDigitsCore]
    split
    · exact h'
    · exact ih _ _ h'

theorem toDigits_upper (n : Nat) :
    ((Nat.toDigits 16 n).map Char.toNat).map pyToUpper = (Nat.toDigits 16 n).map (fun c => c.toUpper.toNat) := by
  have hm := toDigitsCore_mem 16 (by omega) (n + 1) n [] (by simp)
  simp only [List.map_map]
  apply List.map_congr_left
  intro c hc
  obtain ⟨d, hd, rfl⟩ := hm c hc
  exact digitChar_upper d hd

theorem toDigits_ne (b n : Nat) : Nat.toDigits b n ≠ [] := by
  unfold Nat.toDigits
  simp only [Nat.toDigitsCore]
  split
  · simp
  · rename_i h
    intro e
    have : ∀ fuel m (acc : List Char), acc ≠ [] → Nat.toDigitsCore b fuel m acc ≠ [] := by
      intro fuel
      induction fuel with
      | zero => intro m acc h; exact h
      | succ fuel ih =>
        intro m acc h
        simp only [Nat.toDigitsCore]
        split
        · simp
        · exact ih _ _ (by simp)
    exact this n (n / b) [Nat.digitChar (n % b)] (by simp) e

/-- `calc_number_widths` and `fill_number` for an int (no decimal point, fraction or remainder),
unicode_formatter.c:759-1012, against `docNumber`: the sign switch, the padding switch, the zero
padding through `n_min_width`, the prefix, and `toupper` on the prefix and the digits. -/
theorem calc_doc (nPrefix signChar : Nat) (ds sep : Str) (gr : List Nat) (f : FormatSpec) (pfx : Str)
    (up : Bool) (g : Nat) (hds : ds ≠ []) (hpfx : pfx.length = nPrefix) (hsc : signChar = 0 ∨ signChar = 45)
    (hgr : (0 < g ∧ g < 127 ∧ gr = [g]) ∨ (g = 0 ∧ (gr = [127] ∨ gr = [])))
    (hal : f.align = 60 ∨ f.align = 62 ∨ f.align = 61 ∨ f.align = 94)
    (hsg : f.sign = 0 ∨ f.sign = 32 ∨ f.sign = 43 ∨ f.sign = 45) :
    ∃ l sign s r text, calcNumberWidths nPrefix signChar ds 0 sep gr f = .ok (l, sign, s, r, text) ∧
      fillNumber l sign pfx s text [] r f.fillChar up =
        docNumber (signStr f.sign (signChar = 45)) (if up then pfx.map pyToUpper else pfx)
          (if up then ds.map pyToUpper else ds) g (if up then sep.map pyToUpper else sep) [] f := by
  obtain ⟨nS, so, hS, hso, hnS⟩ : ∃ (nS : Nat) (so : Option Nat),
      (if f.sign == 43 then ((1 : Nat), some (if signChar == 45 then 45 else 43))
        else if f.sign == 32 then (1, some (if signChar == 45 then 45 else 32))
        else if signChar == 45 then (1, some 45) else (0, none)) = (nS, so) ∧
      so.toList = signStr f.sign (signChar = 45) ∧ nS = (signStr f.sign (signChar = 45)).length := by
    rcases hsc with rfl | rfl <;> rcases hsg with h | h | h | h <;> rw [h] <;>
      exact ⟨_, _, rfl, by decide, by decide⟩
  generalize hsgS : signStr f.sign (signChar = 45) = sgS at hso hnS
  have hdl : ¬ ds.length = 0 := fun h => hds (List.eq_nil_of_length_eq_zero h)
  generalize hmw : (if (f.fillChar == 48 && f.align == 61) = true then
      f.width - ((nS : Int) + (nPrefix : Int) + ((0 : Nat) : Int)) else 0) = mw
  obtain ⟨it, hins⟩ := insert_doc ds hds mw gr g sep hgr
  generalize hzg : zeroGrouped g sep ds mw = zg at hins
  refine ⟨(padFields (f.width - ((nS : Int) + nPrefix + ((0 : Nat) : Int) + zg.length)) f.align).1, so,
    (padFields (f.width - ((nS : Int) + nPrefix + ((0 : Nat) : Int) + zg.length)) f.align).2.1,
    (padFields (f.width - ((nS : Int) + nPrefix + ((0 : Nat) : Int) + zg.length)) f.align).2.2, zg, ?_, ?_⟩
  · simp only [calcNumberWidths, hS, hdl, if_false, bind, Except.bind, pure, Except.pure, hmw, hins]
    rfl
  · obtain ⟨φ, hφ⟩ : ∃ φ : Nat → Nat, φ = fun c => if up then pyToUpper c else c := ⟨_, rfl⟩
    have hU : ∀ x : Str, (if up then x.map pyToUpper else x) = x.map φ := by
      intro x; subst hφ; cases up <;> simp
    have h48 : φ 48 = 48 := by subst hφ; cases up <;> rfl
    simp only [fillNumber, hU]
    have hUz : zg.map φ = zeroGrouped g (sep.map φ) (ds.map φ) mw := by
      rw [← hzg, zeroGrouped_map φ h48]
    have hzl : zg.length = (zeroGrouped g (sep.map φ) (ds.map φ) mw).length := by
      rw [← hUz, List.length_map]
    rw [hUz]
    have hUne : ds.map φ ≠ [] := by simpa using hds
    have hPl : (pfx.map φ).length = nPrefix := by rw [List.length_map, hpfx]
    generalize pfx.map φ = P at hPl
    generalize ds.map φ = D at hUne hzl
    generalize sep.map φ = Sp at hzl
    unfold docNumber
    by_cases hz : f.fillChar = 48 ∧ f.align = 61
    · have hz' : (f.fillChar == 48 && f.align == 61) = true := by simp [hz.1, hz.2]
      rw [if_pos ⟨hz.1, hz.2, hUne⟩]
      have hmwv : mw = f.width - ((nS : Int) + nPrefix) := by rw [← hmw, if_pos hz']; omega
      have hreach := zerosFor_reach g Sp D mw
      rw [padFields_nonpos _ _ (by rw [hzl]; omega)]
      have : f.width - (sgS.length : Int) - P.length - (([] : Str).length : Int) = mw := by
        rw [hmwv, hPl, ← hnS]; simp; omega
      rw [this, ← hso]
      simp
    · have hz' : (f.fillChar == 48 && f.align == 61) = false := by
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]; omega
      have hm0 : mw = 0 := by rw [← hmw, if_neg (by simp [hz'])]
      rw [if_neg (by intro h; exact hz ⟨h.1, h.2.1⟩)]
      have hb : zeroGrouped g Sp D mw = groupFR g Sp D := by
        unfold zeroGrouped; rw [hm0, zerosFor_nonpos _ _ _ _ (Int.le_refl 0)]; simp
      rw [hb] at hzl ⊢
      rw [hso]
      exact padLayout_eq f sgS P (groupFR g Sp D) [] _ (by rw [hzl, hPl, ← hnS]; simp) hal

/-- The general path of `format_long_internal` against the docs, unicode_formatter.c:1312-1368. -/
theorem longSlow_doc (v : Int) (f : FormatSpec) (base skip : Nat) (hf : SpecInv f)
    (hbt : (f.type = 98 ∧ base = 2 ∧ skip = 2) ∨ (f.type = 111 ∧ base = 8 ∧ skip = 2) ∨
      ((f.type = 120 ∨ f.type = 88) ∧ base = 16 ∧ skip = 2) ∨
      ((f.type = 100 ∨ f.type = 110) ∧ base = 10 ∧ skip = 0)) :
    formatLongSlow v f base skip =
      (let digits := Nat.toDigits base v.natAbs
       if base = 10 ∧ 4300 < digits.length then .error (.valueError intLimitMessage)
       else
        let ds : Str := if f.type = 88 then digits.map (fun c => c.toUpper.toNat) else digits.map Char.toNat
        let pfx : Str := if f.alternate ∧ base ≠ 10 then [48, f.type] else []
        let gs : Nat × Str := if f.thousands = 44 then (3, [44]) else if f.thousands = 95 then (3, [95])
          else if f.thousands = 96 then (4, [95]) else (0, [])
        .ok (docNumber (signStr f.sign (v < 0)) pfx ds gs.1 gs.2 [] f)) := by
  have hb0 : 0 < base ∧ base ≤ 16 := by omega
  have hdig := digitsOf_eq base v.natAbs hb0.1 hb0.2
  have hne := toDigits_ne base v.natAbs
  have hD45 : ∀ c ∈ (Nat.toDigits base v.natAbs).map Char.toNat, c ≠ 45 := by
    rw [← hdig]; exact (digitsOf_spec base v.natAbs).2
  -- the prefix `_PyLong_Format` writes
  obtain ⟨pf, hpf, hpl, hp0⟩ : ∃ pf : Str, ((if base == 2 then [48, 98] else if base == 8 then [48, 111]
      else if base == 16 then [48, 120] else []) : Str) = pf ∧ pf.length = skip ∧
      (pf = [] ∨ pf.head? = some 48) := by
    rcases hbt with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ <;> simp
  have hLF : longFormat v base =
      if base = 10 ∧ 4300 < (Nat.toDigits base v.natAbs).length then .error (.valueError intLimitMessage)
      else .ok ((if v < 0 then [45] else []) ++ pf ++ (Nat.toDigits base v.natAbs).map Char.toNat) := by
    unfold longFormat
    simp only [hdig, List.length_map, Bool.not_true, Bool.false_eq_true, if_false, hpf, intLimitMessage]
    by_cases h : base = 10 ∧ 4300 < (Nat.toDigits base v.natAbs).length
    · rw [if_pos h, if_pos (by simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]; exact ⟨h.1, h.2⟩)]
    · rw [if_neg h, if_neg (by simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]; omega)]
  unfold formatLongSlow
  rw [hLF]
  by_cases hlim : base = 10 ∧ 4300 < (Nat.toDigits base v.natAbs).length
  · obtain ⟨hb10, hl⟩ := hlim
    subst hb10
    simp [hl, bind, Except.bind]
  simp only [hlim, if_false, bind, Except.bind]
  generalize hDs : (Nat.toDigits base v.natAbs).map Char.toNat = ds at hD45
  have hdsne : ds ≠ [] := by rw [← hDs]; simpa using hne
  -- the sign `_PyLong_Format` wrote, and what follows it
  have hsplit : (if (((if v < 0 then [45] else []) ++ pf ++ ds).head? == some 45) = true then
      ((45 : Nat), ((if v < 0 then [45] else []) ++ pf ++ ds).tail)
      else (0, (if v < 0 then [45] else []) ++ pf ++ ds)) = (if v < 0 then 45 else 0, pf ++ ds) := by
    by_cases hv : v < 0
    · simp [hv]
    · simp only [hv, if_false, List.nil_append]
      have : ((pf ++ ds).head? == some 45) = false := by
        rcases hp0 with rfl | h
        · cases ds with
          | nil => exact absurd rfl hdsne
          | cons c t => simpa using hD45 c (by simp)
        · cases pf with
          | nil => simp at h
          | cons c t => simp at h; subst h; rfl
      rw [this]; rfl
  simp only [hsplit]
  have hpfx : (pf ++ ds).take (if f.alternate then skip else 0) = if f.alternate then pf else [] := by
    cases f.alternate <;> simp [← hpl]
  have hdrop : (pf ++ ds).drop skip = ds := by rw [← hpl]; simp
  rw [hpfx, hdrop]
  -- the grouping `get_locale_info` gives, in the C locale
  have hth := hf.thousands
  obtain ⟨g, hgr, hgs⟩ : ∃ g, ((0 < g ∧ g < 127 ∧
      (localeInfo (if f.type == 110 then LT_CURRENT_LOCALE else f.thousands)).2 = [g]) ∨
      (g = 0 ∧ ((localeInfo (if f.type == 110 then LT_CURRENT_LOCALE else f.thousands)).2 = [127] ∨
        (localeInfo (if f.type == 110 then LT_CURRENT_LOCALE else f.thousands)).2 = []))) ∧
      ((if f.thousands = 44 then ((3 : Nat), ([44] : Str)) else if f.thousands = 95 then (3, [95])
        else if f.thousands = 96 then (4, [95]) else (0, [])) =
        (g, (localeInfo (if f.type == 110 then LT_CURRENT_LOCALE else f.thousands)).1)) := by
    by_cases hn : f.type = 110
    · have h0 : f.thousands = 0 := by
        rcases hth with h | ⟨-, h⟩ | ⟨-, h⟩
        · exact h
        · simp [hn] at h
        · simp [hn] at h
      refine ⟨0, Or.inr ⟨rfl, Or.inr ?_⟩, ?_⟩ <;> simp [hn, h0, localeInfo, LT_CURRENT_LOCALE]
    · have hn' : (f.type == 110) = false := by simpa using hn
      simp only [hn', Bool.false_eq_true, if_false]
      rcases hth with h | ⟨h | h, -⟩ | ⟨h, -⟩
      · exact ⟨0, Or.inr ⟨rfl, Or.inl (by simp [h, localeInfo, LT_CURRENT_LOCALE, LT_DEFAULT_LOCALE,
          LT_UNDERSCORE_LOCALE, LT_UNDER_FOUR_LOCALE])⟩, by simp [h, localeInfo, LT_CURRENT_LOCALE,
          LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE, LT_UNDER_FOUR_LOCALE]⟩
      · exact ⟨3, Or.inl ⟨by omega, by omega, by simp [h, localeInfo, LT_CURRENT_LOCALE, LT_DEFAULT_LOCALE]⟩,
          by simp [h, localeInfo, LT_CURRENT_LOCALE, LT_DEFAULT_LOCALE]⟩
      · exact ⟨3, Or.inl ⟨by omega, by omega, by simp [h, localeInfo, LT_CURRENT_LOCALE, LT_DEFAULT_LOCALE,
          LT_UNDERSCORE_LOCALE]⟩, by simp [h, localeInfo, LT_CURRENT_LOCALE, LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE]⟩
      · exact ⟨4, Or.inl ⟨by omega, by omega, by simp [h, localeInfo, LT_CURRENT_LOCALE, LT_DEFAULT_LOCALE,
          LT_UNDERSCORE_LOCALE, LT_UNDER_FOUR_LOCALE]⟩, by simp [h, localeInfo, LT_CURRENT_LOCALE,
          LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE, LT_UNDER_FOUR_LOCALE]⟩
  rw [hgs]
  generalize localeInfo (if f.type == 110 then LT_CURRENT_LOCALE else f.thousands) = loc at hgr hgs ⊢
  obtain ⟨sep, gr⟩ := loc
  simp only at hgr ⊢
  obtain ⟨l, sign, s, r, text, hc, hfill⟩ := calc_doc (if f.alternate then skip else 0)
    (if v < 0 then 45 else 0) ds sep gr f (if f.alternate then pf else []) (f.type == 88) g hdsne
    (by cases f.alternate <;> simp [hpl]) (by by_cases hv : v < 0 <;> simp [hv]) hgr hf.align hf.sign
  rw [hc]
  simp only [hfill]
  have hneg : ((if v < 0 then (45 : Nat) else 0) = 45) = (v < 0) := by
    by_cases hv : v < 0 <;> simp [hv]
  simp only [hneg]
  have hsepX : f.type = 88 → sep.map pyToUpper = sep := by
    intro hx
    have : f.thousands = 0 ∨ f.thousands = 96 := by
      rcases hth with h | ⟨-, h⟩ | ⟨h, -⟩
      · exact Or.inl h
      · simp [hx] at h
      · exact Or.inr h
    rcases this with h | h
    · have : sep = [] := by simp [h] at hgs; exact hgs.2
      simp [this]
    · have : sep = [95] := by simp [h] at hgs; exact hgs.2.symm
      simp [this, pyToUpper, pyIsLower]
  by_cases hx : f.type = 88
  · have hb : base = 16 := by omega
    subst hb
    have hpf' : pf = [48, 120] := by rw [← hpf]; rfl
    have hup : ((Nat.toDigits 16 v.natAbs).map Char.toNat).map pyToUpper =
        (Nat.toDigits 16 v.natAbs).map (fun c => c.toUpper.toNat) := toDigits_upper v.natAbs
    rw [hDs] at hup
    simp only [hx, beq_self_eq_true, if_true, hup, hsepX hx, hpf']
    cases f.alternate <;> simp [hx, pyToUpper, pyIsLower]
  · have hx' : (f.type == 88) = false := by simpa using hx
    simp only [hx', hx, Bool.false_eq_true, if_false, ← hDs]
    cases ha : f.alternate
    · simp
    · rcases hbt with ⟨ht, rfl, rfl⟩ | ⟨ht, rfl, rfl⟩ | ⟨ht | ht, rfl, rfl⟩ | ⟨ht | ht, rfl, rfl⟩ <;>
        simp [← hpf, ht] <;> omega

/-- `calc_number_widths` for the `c` type: no digits, the character as the remainder. -/
theorem calc_c (sep : Str) (gr : List Nat) (f : FormatSpec) (hs : f.sign = 0) :
    calcNumberWidths 0 0 [] 1 sep gr f =
      .ok ((padFields (f.width - 1) f.align).1, none, (padFields (f.width - 1) f.align).2.1,
        (padFields (f.width - 1) f.align).2.2, []) := by
  have e : f.width - (((0 : Nat) : Int) + ((0 : Nat) : Int) + ((1 : Nat) : Int) + ((0 : Nat) : Int)) =
      f.width - 1 := by omega
  simp only [calcNumberWidths, hs, show ((0 : Nat) == 43) = false from rfl,
    show ((0 : Nat) == 32) = false from rfl, show ((0 : Nat) == 45) = false from rfl, Bool.false_eq_true,
    if_false, List.length_nil, if_true, bind, Except.bind, pure, Except.pure]
  rw [← e]
  rfl

theorem fill_c (v : Int) (f : FormatSpec) (hal : f.align = 60 ∨ f.align = 62 ∨ f.align = 61 ∨ f.align = 94) :
    fillNumber (padFields (f.width - 1) f.align).1 none [] (padFields (f.width - 1) f.align).2.1 []
      [v.toNat] (padFields (f.width - 1) f.align).2.2 f.fillChar false =
      docNumber [] [] [] 0 [] [v.toNat] f := by
  unfold docNumber
  rw [if_neg (by simp), groupFR_zero]
  simp only [fillNumber, Option.toList_none, Bool.false_eq_true, if_false]
  exact padLayout_eq f [] [] [] [v.toNat] (f.width - 1) (by simp) hal

/-- `format_long_internal` against the docs, for every int, every parsed spec with an integer type
and either answer to `PyLong_CheckExact`: the fast path `_PyLong_FormatWriter`, the general path,
the `c` type and every refusal give what `docInt` describes. -/
def IntFormatDoc : Prop :=
  ∀ (v : Int) (f : FormatSpec) (exact : Bool), SpecInv f → f.type ∈ [98, 99, 100, 111, 120, 88, 110] →
    formatLongInternal v f exact = docInt v f

theorem intFormatDoc_proven : IntFormatDoc := by
  intro v f exact hf ht
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
  unfold formatLongInternal docInt
  by_cases hp : f.precision = -1
  · simp only [hp, bne_self_eq_false, Bool.false_eq_true, if_false, ne_eq, not_true_eq_false]
    by_cases hz : f.noNeg0 = true
    · simp [hz]
    simp only [hz, Bool.false_eq_true, if_false]
    by_cases hc : f.type = 99
    · simp only [hc, beq_self_eq_true, if_true]
      by_cases hs : f.sign = 0
      · simp only [hs, bne_self_eq_false, Bool.false_eq_true, if_false, ne_eq, not_true_eq_false]
        by_cases ha : f.alternate = true
        · simp [ha]
        simp only [ha, Bool.false_eq_true, if_false]
        by_cases ho : v > 2 ^ 63 - 1 ∨ v < -(2 ^ 63)
        · rw [if_pos ho, if_pos ho]
        rw [if_neg ho, if_neg ho]
        by_cases hr : v < 0 ∨ v > 0x10ffff
        · rw [if_pos hr, if_pos hr]
        rw [if_neg hr, if_neg hr]
        -- the character, padded: no digits, one remainder character
        simp only [bind, Except.bind]
        generalize localeInfo f.thousands = loc
        obtain ⟨sep, gr⟩ := loc
        simp only []
        rw [calc_c sep gr f hs]
        simp only []
        exact congrArg Except.ok (fill_c v f hf.align)
      · have hs' : (f.sign != 0) = true := by simpa using hs
        simp [hs', hs]
    · have hc' : (f.type == 99) = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, if_false, hc]
      generalize hbs : (if f.type == 98 then ((2 : Nat), (2 : Nat)) else if f.type == 111 then (8, 2)
        else if f.type == 120 || f.type == 88 then (16, 2) else (10, 0)) = bs
      obtain ⟨base, skip⟩ := bs
      have hbt : (f.type = 98 ∧ base = 2 ∧ skip = 2) ∨ (f.type = 111 ∧ base = 8 ∧ skip = 2) ∨
          ((f.type = 120 ∨ f.type = 88) ∧ base = 16 ∧ skip = 2) ∨
          ((f.type = 100 ∨ f.type = 110) ∧ base = 10 ∧ skip = 0) := by
        rcases ht with h | h | h | h | h | h | h <;> simp [h] at hbs <;> omega
      have hbase : (if f.type = 98 then 2 else if f.type = 111 then 8
          else if f.type = 120 ∨ f.type = 88 then 16 else 10) = base := by
        rcases hbt with ⟨h, rfl, -⟩ | ⟨h, rfl, -⟩ | ⟨h | h, rfl, -⟩ | ⟨h | h, rfl, -⟩ <;> simp [h]
      simp only []
      rw [hbase, ← longSlow_doc v f base skip hf hbt]
      split
      · rename_i hfast
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hfast
        exact intFastSlow_proven v f base skip
          (by rcases hbt with ⟨_, h1, h2⟩ | ⟨_, h1, h2⟩ | ⟨_, h1, h2⟩ | ⟨_, h1, h2⟩ <;> simp [h1, h2])
          hfast.1.1.1.1.1.1 hfast.1.1.1.1.1.2 hfast.1.1.1.1.2 hfast.1.1.1.2 hfast.1.1.2 hfast.1.2
      · rfl
  · have hp' : (f.precision != -1) = true := by simpa using hp
    simp [hp', hp]

end PyLean.UnicodeObj
