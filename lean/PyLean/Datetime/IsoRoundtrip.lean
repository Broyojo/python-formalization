import PyLean.Datetime.CalendarProps

/-!
`fromisoformat(d.isoformat()) == d` for dates, in both parsers.
-/

namespace PyLean.Datetime

open PyLean

/-- The ASCII digit `k`. -/
def dc (k : Nat) : Char := Char.ofNat (48 + k)

theorem dc_facts_fin : ∀ k : Fin 10,
    isAsciiDigit (dc k) = true ∧ (dc k).toNat = 48 + (k : Nat) ∧ digitVal (dc k) = (k : Nat) ∧
    intTransform (dc k) = some (dc k) ∧ isAsciiSpace (dc k) = false ∧ isDigitOrUnderscore (dc k) = true ∧
    dc k ≠ '+' ∧ dc k ≠ '-' ∧ dc k ≠ 'W' ∧ dc k ≠ '_' ∧ utf8Char (dc k) = [48 + (k : Nat)] := by
  decide

theorem dc_facts (k : Nat) (hk : k < 10) :
    isAsciiDigit (dc k) = true ∧ (dc k).toNat = 48 + k ∧ digitVal (dc k) = k ∧
    intTransform (dc k) = some (dc k) ∧ isAsciiSpace (dc k) = false ∧ isDigitOrUnderscore (dc k) = true ∧
    dc k ≠ '+' ∧ dc k ≠ '-' ∧ dc k ≠ 'W' ∧ dc k ≠ '_' ∧ utf8Char (dc k) = [48 + k] :=
  dc_facts_fin ⟨k, hk⟩

theorem dc_zero : dc 0 = '0' := by decide

/-! ### Formatting -/

theorem natDigitsAux_small (f n : Nat) (h : n < 10) : natDigitsAux (f + 1) n = [dc n] := by
  simp [natDigitsAux, h, dc, Nat.mod_eq_of_lt h]

theorem natDigitsAux_big (f n : Nat) (h : ¬ n < 10) :
    natDigitsAux (f + 1) n = natDigitsAux f (n / 10) ++ [dc (n % 10)] := by
  simp [natDigitsAux, h, dc]

theorem padNat2 (n : Nat) (h : n < 100) : padNat 2 n = [dc (n / 10), dc (n % 10)] := by
  unfold padNat natDigits
  by_cases h1 : n < 10
  · rw [natDigitsAux_small _ _ h1]
    simp [Nat.div_eq_of_lt h1, Nat.mod_eq_of_lt h1, dc_zero]
  · rw [natDigitsAux_big _ _ h1]
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [hk, natDigitsAux_small _ _ (by omega)]
    simp [← hk, Nat.mod_eq_of_lt (show n / 10 < 10 by omega)]

theorem padNat4 (n : Nat) (h : n < 10000) :
    padNat 4 n = [dc (n / 1000), dc (n / 100 % 10), dc (n / 10 % 10), dc (n % 10)] := by
  unfold padNat natDigits
  by_cases h1 : n < 10
  · rw [natDigitsAux_small _ _ h1]
    simp [show n / 1000 = 0 by omega, show n / 100 % 10 = 0 by omega, show n / 10 % 10 = 0 by omega,
      Nat.mod_eq_of_lt h1, dc_zero]
  · rw [natDigitsAux_big _ _ h1]
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    by_cases h2 : n / 10 < 10
    · rw [hk, natDigitsAux_small _ _ (by omega)]
      simp [← hk, show n / 1000 = 0 by omega, show n / 100 % 10 = 0 by omega,
        show n / 10 % 10 = n / 10 by omega, dc_zero]
    · rw [hk, natDigitsAux_big _ _ (by omega)]
      obtain ⟨k2, hk2⟩ : ∃ k2, k = k2 + 1 := ⟨k - 1, by omega⟩
      by_cases h3 : (k + 1) / 10 / 10 < 10
      · rw [hk2, natDigitsAux_small _ _ (by omega)]
        simp [← hk2, ← hk, show n / 1000 = 0 by omega, show n / 10 / 10 = n / 100 by omega,
          show n / 100 % 10 = n / 100 by omega, dc_zero]
      · rw [hk2, natDigitsAux_big _ _ (by omega)]
        obtain ⟨k3, hk3⟩ : ∃ k3, k2 = k3 + 1 := ⟨k2 - 1, by omega⟩
        rw [hk3, natDigitsAux_small _ _ (by omega)]
        simp [← hk3, ← hk2, ← hk, show n / 10 / 10 / 10 = n / 1000 by omega,
          show n / 10 / 10 % 10 = n / 100 % 10 by omega]

theorem natDigitsAux_fuel (f g n : Nat) (hf : n < f) (hg : n < g) :
    natDigitsAux f n = natDigitsAux g n := by
  induction f generalizing g n with
  | zero => omega
  | succ f ih =>
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    by_cases h10 : n < 10
    · rw [natDigitsAux_small _ _ h10, natDigitsAux_small _ _ h10]
    · rw [natDigitsAux_big _ _ h10, natDigitsAux_big _ _ h10, ih g (n / 10) (by omega) (by omega)]

theorem natDigits_big (n : Nat) (h : ¬ n < 10) : natDigits n = natDigits (n / 10) ++ [dc (n % 10)] := by
  unfold natDigits
  rw [natDigitsAux_big _ _ h, natDigitsAux_fuel n (n / 10 + 1) (n / 10) (by omega) (by omega)]

theorem padNat_step (w n : Nat) (hw : 2 ≤ w) : padNat w n = padNat (w - 1) (n / 10) ++ [dc (n % 10)] := by
  unfold padNat
  by_cases h10 : n < 10
  · have e : natDigits n = [dc n] := by unfold natDigits; exact natDigitsAux_small _ _ h10
    have e0 : natDigits 0 = ['0'] := by decide
    rw [e, Nat.div_eq_of_lt h10, e0, Nat.mod_eq_of_lt h10]
    simp only [List.length_cons, List.length_nil]
    obtain ⟨k, rfl⟩ : ∃ k, w = k + 2 := ⟨w - 2, by omega⟩
    simp [List.replicate_succ']
  · rw [natDigits_big n h10]
    simp only [List.length_append, List.length_cons, List.length_nil, List.append_assoc]
    congr 2
    omega

theorem padNat_one (n : Nat) (h : n < 10) : padNat 1 n = [dc n] := by
  unfold padNat natDigits
  rw [natDigitsAux_small _ _ h]
  rfl

theorem padNat6 (n : Nat) (h : n < 1000000) :
    padNat 6 n = [dc (n / 100000), dc (n / 10000 % 10), dc (n / 1000 % 10), dc (n / 100 % 10),
      dc (n / 10 % 10), dc (n % 10)] := by
  rw [padNat_step 6 n (by omega), padNat_step 5 _ (by omega), padNat_step 4 _ (by omega),
    padNat_step 3 _ (by omega), padNat_step 2 _ (by omega), padNat_one _ (by omega)]
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  rw [show n / 10 / 10 / 10 / 10 / 10 = n / 100000 by omega, show n / 10 / 10 / 10 / 10 = n / 10000 by omega,
    show n / 10 / 10 / 10 = n / 1000 by omega, show n / 10 / 10 = n / 100 by omega]

/-- `date.isoformat()` of a valid date, character by character. -/
theorem dateIsoformat_eq (y m d : Int) (h : ValidDate y m d) :
    dateIsoformat y m d =
      [dc (y.toNat / 1000), dc (y.toNat / 100 % 10), dc (y.toNat / 10 % 10), dc (y.toNat % 10), '-',
       dc (m.toNat / 10), dc (m.toNat % 10), '-', dc (d.toNat / 10), dc (d.toNat % 10)] := by
  have hv := h
  rw [validDate_iff] at h
  unfold MINYEAR MAXYEAR at h
  have hd := dimL_bounds (isLeap y) m ⟨h.2.2.1, h.2.2.2.1⟩
  unfold dateIsoformat padInt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), padNat4 _ (by omega),
    padNat2 _ (by omega), padNat2 _ (by omega)]
  rfl

/-! ### Parsing digit runs -/

/-- The value of a list of decimal digits. -/
def digitsNat (l : List Nat) : Nat := l.foldl (fun acc k => acc * 10 + k) 0

theorem mapM_intTransform_dc (l : List Nat) (h : ∀ k ∈ l, k < 10) :
    (l.map dc).mapM intTransform = some (l.map dc) := by
  induction l with
  | nil => rfl
  | cons k t ih =>
    simp only [List.map_cons, List.mapM_cons, (dc_facts k (h k (by simp))).2.2.2.1,
      ih (fun j hj => h j (by simp [hj]))]
    rfl

theorem underscoreDigits_dc (l : List Nat) (acc : Nat) (h : ∀ k ∈ l, k < 10) :
    underscoreDigits (l.map dc) acc false = some (l.foldl (fun acc k => acc * 10 + k) acc) := by
  induction l generalizing acc with
  | nil => rfl
  | cons k t ih =>
    have hk := dc_facts k (h k (by simp))
    simp only [List.map_cons, underscoreDigits, hk.1, ite_true, List.foldl_cons, hk.2.2.1]
    exact ih _ (fun j hj => h j (by simp [hj]))

theorem splitSign_dc (k : Nat) (hk : k < 10) (r : List Char) : splitSign (dc k :: r) = (false, dc k :: r) := by
  have f := dc_facts k hk
  unfold splitSign
  split
  · rename_i heq; exact absurd (List.cons.inj heq).1 f.2.2.2.2.2.2.1
  · rename_i heq; exact absurd (List.cons.inj heq).1 f.2.2.2.2.2.2.2.1
  · rfl

theorem takeWhile_dc (l : List Nat) (h : ∀ k ∈ l, k < 10) :
    (l.map dc).takeWhile isDigitOrUnderscore = l.map dc := by
  induction l with
  | nil => rfl
  | cons k t ih =>
    simp only [List.map_cons, List.takeWhile_cons, (dc_facts k (h k (by simp))).2.2.2.2.2.1, ite_true,
      ih (fun j hj => h j (by simp [hj]))]

theorem dropWhile_dc (l : List Nat) (h : ∀ k ∈ l, k < 10) :
    (l.map dc).dropWhile isDigitOrUnderscore = [] := by
  induction l with
  | nil => rfl
  | cons k t ih =>
    simp only [List.map_cons, List.dropWhile_cons, (dc_facts k (h k (by simp))).2.2.2.2.2.1, ite_true,
      ih (fun j hj => h j (by simp [hj]))]

theorem pyInt_dc (l : List Nat) (hne : l ≠ []) (h : ∀ k ∈ l, k < 10) :
    pyInt (l.map dc) = .ok (digitsNat l) := by
  obtain ⟨k, t, rfl⟩ : ∃ k t, l = k :: t := by
    cases l with
    | nil => exact absurd rfl hne
    | cons k t => exact ⟨k, t, rfl⟩
  have hk := dc_facts k (h k (by simp))
  have hall : ∀ x ∈ (k :: t).map dc, isDigitOrUnderscore x = true := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    exact (dc_facts j (h j hj)).2.2.2.2.2.1
  unfold pyInt
  rw [mapM_intTransform_dc _ h]
  simp only [Option.bind_some]
  unfold intAscii
  rw [List.map_cons, List.dropWhile_cons, if_neg (by simp [hk.2.2.2.2.1])]
  dsimp only
  rw [splitSign_dc k (h k (by simp))]
  dsimp only
  rw [← List.map_cons, takeWhile_dc _ h, dropWhile_dc _ h, List.map_cons]
  simp only [List.all_nil, Bool.not_true, Bool.false_eq_true, ite_false, hk.1, ite_true]
  rw [← List.map_cons, underscoreDigits_dc _ _ h]
  rfl

/-! ### The date parsers on `YYYY-MM-DD` -/

theorem parseIsoDatePy_ext (a b c e f g i j : Nat) (ha : a < 10) (hb : b < 10) (hc : c < 10) (he : e < 10)
    (hf : f < 10) (hg : g < 10) (hi : i < 10) (hj : j < 10) :
    parseIsoDatePy [dc a, dc b, dc c, dc e, '-', dc f, dc g, '-', dc i, dc j] =
      .ok (((a * 1000 + b * 100 + c * 10 + e : Nat) : Int), ((f * 10 + g : Nat) : Int), ((i * 10 + j : Nat) : Int)) := by
  have p4 := pyInt_dc [a, b, c, e] (by simp) (by simp; omega)
  have p2m := pyInt_dc [f, g] (by simp) (by simp; omega)
  have p2d := pyInt_dc [i, j] (by simp) (by simp; omega)
  simp only [List.map_cons, List.map_nil, digitsNat, List.foldl_cons, List.foldl_nil] at p4 p2m p2d
  have hW : dc f ≠ 'W' := (dc_facts f hf).2.2.2.2.2.2.2.2.1
  unfold parseIsoDatePy
  simp only [List.length_cons, List.length_nil, slice, charAt]
  simp [p4, p2m, p2d, hW, bind, Except.bind, pure, Except.pure]
  omega

theorem byte_dc (k : Nat) (hk : k < 10) : isDigitC (48 + k) = true := by
  unfold isDigitC; simp; omega

set_option maxRecDepth 20000 in
theorem parseIsoDateC_ext (a b c e f g i j : Nat) (ha : a < 10) (hb : b < 10) (hc : c < 10) (he : e < 10)
    (hf : f < 10) (hg : g < 10) (hi : i < 10) (hj : j < 10) :
    parseIsoDateC [48 + a, 48 + b, 48 + c, 48 + e, 45, 48 + f, 48 + g, 45, 48 + i, 48 + j] 10 =
      .ok (((a * 1000 + b * 100 + c * 10 + e : Nat) : Int), ((f * 10 + g : Nat) : Int), ((i * 10 + j : Nat) : Int)) := by
  unfold parseIsoDateC
  simp [parseDigitsC, byteAt, byte_dc a ha, byte_dc b hb, byte_dc c hc, byte_dc e he, byte_dc f hf,
    byte_dc g hg, byte_dc i hi, byte_dc j hj, show 48 + f ≠ 87 by omega]
  omega

/-- `date.fromisoformat(d.isoformat()) == d` and
`datetime.fromisoformat(d.isoformat()) == datetime(d.year, d.month, d.day)` for
every date, in both twins. -/
def DateIsoformatRoundtrip : Prop :=
  ∀ y m d : Int, ValidDate y m d →
    dateFromIsoPy (dateIsoformat y m d) = .ok (y, m, d) ∧
    dateFromIsoC (dateIsoformat y m d) = .ok (y, m, d) ∧
    datetimeFromIsoPy (dateIsoformat y m d) = .ok ⟨y, m, d, ⟨0, 0, 0, 0, none⟩⟩ ∧
    datetimeFromIsoC (dateIsoformat y m d) = .ok ⟨y, m, d, ⟨0, 0, 0, 0, none⟩⟩

theorem dateIsoformatRoundtrip_proven : DateIsoformatRoundtrip := by
  intro y m d h
  have hv := h
  rw [validDate_iff] at h
  unfold MINYEAR MAXYEAR at h
  have hd := dimL_bounds (isLeap y) m ⟨h.2.2.1, h.2.2.2.1⟩
  rw [dateIsoformat_eq y m d hv]
  have ey : (((y.toNat / 1000 * 1000 + y.toNat / 100 % 10 * 100 + y.toNat / 10 % 10 * 10 + y.toNat % 10 : Nat)) : Int) = y := by
    omega
  have em : (((m.toNat / 10 * 10 + m.toNat % 10 : Nat)) : Int) = m := by omega
  have ed : (((d.toNat / 10 * 10 + d.toNat % 10 : Nat)) : Int) = d := by omega
  have pPy := parseIsoDatePy_ext (y.toNat / 1000) (y.toNat / 100 % 10) (y.toNat / 10 % 10) (y.toNat % 10)
    (m.toNat / 10) (m.toNat % 10) (d.toNat / 10) (d.toNat % 10)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have pC := parseIsoDateC_ext (y.toNat / 1000) (y.toNat / 100 % 10) (y.toNat / 10 % 10) (y.toNat % 10)
    (m.toNat / 10) (m.toNat % 10) (d.toNat / 10) (d.toNat % 10)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [ey, em, ed] at pPy pC
  have hascii : ∀ k, k < 10 → (dc k).toNat < 128 := fun k hk => by
    rw [(dc_facts k hk).2.1]; omega
  have hutf : ∀ k, k < 10 → utf8Char (dc k) = [48 + k] := fun k hk => (dc_facts k hk).2.2.2.2.2.2.2.2.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold dateFromIsoPy
    simp [hascii _ (show y.toNat / 1000 < 10 by omega), hascii _ (show y.toNat / 100 % 10 < 10 by omega),
      hascii _ (show y.toNat / 10 % 10 < 10 by omega), hascii _ (show y.toNat % 10 < 10 by omega),
      hascii _ (show m.toNat / 10 < 10 by omega), hascii _ (show m.toNat % 10 < 10 by omega),
      hascii _ (show d.toNat / 10 < 10 by omega), hascii _ (show d.toNat % 10 < 10 by omega),
      pPy, bind, Except.bind, checkDate_ok y m d hv]
  · unfold dateFromIsoC utf8
    simp [hutf _ (show y.toNat / 1000 < 10 by omega), hutf _ (show y.toNat / 100 % 10 < 10 by omega),
      hutf _ (show y.toNat / 10 % 10 < 10 by omega), hutf _ (show y.toNat % 10 < 10 by omega),
      hutf _ (show m.toNat / 10 < 10 by omega), hutf _ (show m.toNat % 10 < 10 by omega),
      hutf _ (show d.toNat / 10 < 10 by omega), hutf _ (show d.toNat % 10 < 10 by omega),
      show utf8Char '-' = [45] by decide, pC, checkDate_ok y m d hv]
  · have hW : dc (m.toNat / 10) ≠ 'W' := (dc_facts _ (show m.toNat / 10 < 10 by omega)).2.2.2.2.2.2.2.2.1
    unfold datetimeFromIsoPy findSepPy
    simp [charAt, hW, pPy, bind, Except.bind, pure, Except.pure, checkDate_ok y m d hv, checkTime]
  · unfold datetimeFromIsoC utf8
    simp [hutf _ (show y.toNat / 1000 < 10 by omega), hutf _ (show y.toNat / 100 % 10 < 10 by omega),
      hutf _ (show y.toNat / 10 % 10 < 10 by omega), hutf _ (show y.toNat % 10 < 10 by omega),
      hutf _ (show m.toNat / 10 < 10 by omega), hutf _ (show m.toNat % 10 < 10 by omega),
      hutf _ (show d.toNat / 10 < 10 by omega), hutf _ (show d.toNat % 10 < 10 by omega),
      show utf8Char '-' = [45] by decide, findSepC, byteAt, show 48 + m.toNat / 10 ≠ 87 by omega, pC,
      bind, Except.bind, pure, Except.pure, tzinfoFromIsoResults, checkDate_ok y m d hv, checkTime]

end PyLean.Datetime
