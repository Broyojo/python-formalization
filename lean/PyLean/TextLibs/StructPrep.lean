import PyLean.TextLibs.StructStd

/-!
`whichtable`, `prepare_s` and `set_format` (`Modules/_struct.c:1558-1830`), and the object life of
`Struct` (`Struct_impl`, `s_new`, `same_format`, `Struct___init___impl`, `s_init`, 1843-2004), stated by
what each does rather than through one another.
-/

namespace PyLean.TextLibs.Struct

open PyLean PyLean.TextLibs

set_option linter.unusedSimpArgs false

/-! ### `prepare_s` refusals -/

/-- The value of a run of decimal digits, read on from `acc`. -/
def digVal (acc : Nat) (ds : List Char) : Nat := ds.foldl (fun a d => a * 10 + digit d) acc

theorem digVal_ge : ∀ (ds : List Char) (acc : Nat), acc ≤ digVal acc ds
  | [], _ => Nat.le_refl _
  | d :: ds, acc => by
    have := digVal_ge ds (acc * 10 + digit d)
    simp only [digVal, List.foldl_cons] at this ⊢
    omega

theorem digit_range (d : Char) (h : isDigit d = true) : 48 ≤ d.toNat ∧ d.toNat ≤ 57 := by
  simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le] at h
  have e1 : ('0' : Char).val.toNat = 48 := rfl
  have e2 : ('9' : Char).val.toNat = 57 := rfl
  simp only [Char.toNat]
  omega

theorem digit_le (d : Char) (h : isDigit d = true) : digit d ≤ 9 := by
  have := digit_range d h
  simp only [digit]
  have e1 : ('0' : Char).toNat = 48 := rfl
  omega

theorem digit_not_space (d : Char) (h : isDigit d = true) : isSpace d = false := by
  have hr := digit_range d h
  cases hs : isSpace d
  · rfl
  · simp only [isSpace, Bool.or_eq_true, decide_eq_true_eq] at hs
    rcases hs with ((((h1 | h1) | h1) | h1) | h1) | h1 <;> subst h1 <;> simp at hr

/-- The overflow test of the digit loop (1679-1682) is exactly `acc * 10 + d > PY_SSIZE_T_MAX`. -/
theorem ovf_test (acc d : Nat) (hd : d ≤ 9) :
    (acc ≥ maxN / 10 ∧ (acc > maxN / 10 ∨ d > maxN % 10)) ↔ acc * 10 + d > maxN := by
  simp only [maxN, Nat.reducePow, Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod]
  omega

theorem scan_ok : ∀ (ds : List Char) (acc : Nat) (rest : List Char) (c : Option Char),
    (∀ d ∈ ds, isDigit d = true) → digVal acc ds ≤ maxN →
    (match rest with | [] => c = none | x :: _ => isDigit x = false ∧ c = some x) →
    scanDigits1 acc (ds ++ rest) = some (digVal acc ds, c, rest.drop 1)
  | [], acc, rest, c, _, _, hr => by
    match rest, hr with
    | [], hr => subst hr; rfl
    | x :: xs, ⟨hx, hc⟩ => subst hc; simp [scanDigits1, hx, digVal]
  | d :: ds, acc, rest, c, hd, hv, hr => by
    have hdd : isDigit d = true := hd d (by simp)
    have hle := digVal_ge ds (acc * 10 + digit d)
    simp only [digVal, List.foldl_cons] at hv hle
    have hno : ¬ (acc ≥ maxN / 10 ∧ (acc > maxN / 10 ∨ digit d > maxN % 10)) := by
      rw [ovf_test _ _ (digit_le d hdd)]; omega
    simp only [List.cons_append, scanDigits1, hdd, if_true, if_neg hno]
    exact scan_ok ds _ rest c (fun x hx => hd x (by simp [hx])) hv hr

theorem scan_ovf : ∀ (ds : List Char) (acc : Nat) (rest : List Char),
    (∀ d ∈ ds, isDigit d = true) → digVal acc ds > maxN → acc ≤ maxN →
    scanDigits1 acc (ds ++ rest) = none
  | [], acc, rest, _, hv, ha => by simp [digVal] at hv; omega
  | d :: ds, acc, rest, hd, hv, ha => by
    have hdd : isDigit d = true := hd d (by simp)
    simp only [digVal, List.foldl_cons] at hv
    simp only [List.cons_append, scanDigits1, hdd, if_true]
    by_cases hc : acc * 10 + digit d > maxN
    · rw [if_pos ((ovf_test _ _ (digit_le d hdd)).2 hc)]
    · rw [if_neg (fun h => hc ((ovf_test _ _ (digit_le d hdd)).1 h))]
      exact scan_ovf ds _ rest (fun x hx => hd x (by simp [hx])) hv (by omega)

/-- The refusals of `prepare_s`, each with its message, from any state of the first pass:
- a non-ASCII format is `ValueError` (1655-1658), and an ASCII one with a NUL is `struct.error`
  (1660-1664);
- a run of digits at the end is "repeat count given without format specifier" (1686-1690) as long as
  it fits in `Py_ssize_t`, and one that does not is "total struct size too long", wherever it is
  (1679-1683);
- a character that no entry of the table starts is "bad char in struct format" (`getentry`, 1609-1612);
- an item whose count, aligned offset or size passes `PY_SSIZE_T_MAX` is "total struct size too long"
  (1700-1726). -/
def PrepareRefusals : Prop :=
  (∀ fmt : List Nat, (∃ c ∈ fmt, 128 ≤ c) →
    prepareS fmt = .error (.valueError "non-ASCII character in struct format")) ∧
  (∀ fmt : List Nat, (∀ c ∈ fmt, c < 128) → 0 ∈ fmt →
    prepareS fmt = .error (structErr "embedded null character")) ∧
  (∀ (tbl : List FormatDef) (fuel : Nat) (st : Pass1) (ds : List Char), ds ≠ [] →
    (∀ d ∈ ds, isDigit d = true) → digVal 0 ds ≤ maxN →
    pass1 tbl (fuel + 1) ds st = .error (structErr "repeat count given without format specifier")) ∧
  (∀ (tbl : List FormatDef) (fuel : Nat) (st : Pass1) (ds rest : List Char), ds ≠ [] →
    (∀ d ∈ ds, isDigit d = true) → digVal 0 ds > maxN →
    pass1 tbl (fuel + 1) (ds ++ rest) st = .error overflowErr) ∧
  (∀ (tbl : List FormatDef) (fuel : Nat) (st : Pass1) (c : Char) (r : List Char),
    isSpace c = false → isDigit c = false → (∀ e ∈ tbl, ∃ x xs, e.format = x :: xs ∧ x ≠ c) →
    pass1 tbl (fuel + 1) (c :: r) st = .error (structErr "bad char in struct format")) ∧
  (∀ (tbl : List FormatDef) (st : Pass1) (num : Nat) (c : Char) (r : List Char) (e : FormatDef),
    getentry (c :: r) tbl = .ok e →
    (((c = 's' ∨ c = 'p') ∧ st.len = maxN) ∨
     (c ≠ 's' ∧ c ≠ 'p' ∧ c ≠ 'x' ∧ num > maxN - st.len) ∨
     align st.size e = none ∨
     (∃ size, align st.size e = some size ∧ num > (maxN - size) / e.size)) →
    pass1Item tbl st num c r = .error overflowErr)

theorem getentry_none (c : Char) (r : List Char) :
    ∀ tbl : List FormatDef, (∀ e ∈ tbl, ∃ x xs, e.format = x :: xs ∧ x ≠ c) →
      getentry (c :: r) tbl = .error (structErr "bad char in struct format")
  | [], _ => rfl
  | e :: es, h => by
    obtain ⟨x, xs, hfm, hx⟩ := h e (by simp)
    have hf : formatEqual e (c :: r) = false := by
      unfold formatEqual
      rw [hfm]
      simp [List.isPrefixOf, hx]
    simp only [getentry, hf, Bool.false_eq_true, if_false]
    exact getentry_none c r es (fun y hy => h y (by simp [hy]))

theorem prepareRefusals_proven : PrepareRefusals := by
  refine ⟨fun fmt h => ?_, fun fmt h h0 => ?_, fun tbl fuel st ds hne hd hv => ?_,
    fun tbl fuel st ds rest hne hd hv => ?_, fun tbl fuel st c r hsp hdg hno => ?_,
    fun tbl st num c r e hg hc => ?_⟩
  · obtain ⟨c, hc, hc2⟩ := h
    have : (!fmt.all (· < 128)) = true := by
      simp only [Bool.not_eq_true', List.all_eq_false]
      exact ⟨c, hc, by simp; omega⟩
    simp [prepareS, this]
  · have : (!fmt.all (· < 128)) = false := by simp; exact h
    simp [prepareS, this, h0]
  · match ds, hne with
    | d :: ds', _ =>
      have hdd : isDigit d = true := hd d (by simp)
      have hs := scan_ok ds' (digit d) [] none (fun x hx => hd x (by simp [hx]))
        (by simpa [digVal] using hv) rfl
      rw [List.append_nil] at hs
      simp only [pass1, hdd, if_true, hs]
      have : isSpace d = false := digit_not_space d hdd
      simp [this]
  · match ds, hne with
    | d :: ds', _ =>
      have hdd : isDigit d = true := hd d (by simp)
      have hs := scan_ovf ds' (digit d) rest (fun x hx => hd x (by simp [hx]))
        (by simpa [digVal] using hv) (by have := digit_le d hdd; simp only [maxN]; omega)
      have hsp : isSpace d = false := digit_not_space d hdd
      simp only [List.cons_append, pass1, hsp, hdd, if_true, Bool.false_eq_true, if_false, hs]
  · have hg := getentry_none c r tbl hno
    simp [pass1, hsp, hdg, pass1Item, hg, bind, Except.bind]
  · unfold pass1Item
    simp only [hg, bind, Except.bind]
    rcases hc with ⟨hsp, hl⟩ | ⟨h1, h2, h3, h4⟩ | ha | ⟨size, ha, hs⟩
    · simp [hsp, hl]
    · simp only [h1, h2, h3, or_self, if_false, false_or]
      rw [if_pos h4]
    · by_cases hsp : c = 's' ∨ c = 'p'
      · by_cases hl : st.len = maxN
        · simp [hsp, hl]
        · simp [hsp, hl, pure, Except.pure, ha]
      · by_cases hx : c = 'x'
        · simp [hsp, hx, pure, Except.pure, ha]
        · by_cases h4 : num > maxN - st.len
          · simp [hsp, hx, h4]
          · simp [hsp, hx, h4, pure, Except.pure, ha]
    · by_cases hsp : c = 's' ∨ c = 'p'
      · by_cases hl : st.len = maxN
        · simp [hsp, hl]
        · simp [hsp, hl, pure, Except.pure, ha, hs]
      · by_cases hx : c = 'x'
        · simp [hsp, hx, pure, Except.pure, ha, hs]
        · by_cases h4 : num > maxN - st.len
          · simp [hsp, hx, h4]
          · simp [hsp, hx, h4, pure, Except.pure, ha, hs]

/-! ### `prepare_s` success: one item in every table -/

/-- `calcsize` of a one-digit count and any code of the table a prefix selects is the count times the
code's size, for every prefix (`<`, `>`, `!`, `=`, `@`, none) and every entry, `x`, `s` and `p` included.
A `prepare_s` that refused good formats, or computed sizes another way, fails this. -/
def OneItemSize : Prop :=
  ∀ p ∈ [[], ['<'], ['>'], ['!'], ['='], ['@']], ∀ e ∈ (whichtable p).1.table, ∀ d < 10,
    calcsize (.str ((p ++ Char.ofNat ('0'.toNat + d) :: e.format).map Char.toNat)) = .ok (d * e.size)

def okEq (r : Py Nat) (n : Nat) : Bool :=
  match r with
  | .ok m => m == n
  | .error _ => false

theorem okEq_sound (r : Py Nat) (n : Nat) (h : okEq r n = true) : r = .ok n := by
  cases r with
  | ok m => simp only [okEq, beq_iff_eq] at h; rw [h]
  | error _ => simp [okEq] at h

theorem oneItem_check : ∀ p ∈ [[], ['<'], ['>'], ['!'], ['='], ['@']], ∀ e ∈ (whichtable p).1.table, ∀ d < 10,
    okEq (calcsize (.str ((p ++ Char.ofNat ('0'.toNat + d) :: e.format).map Char.toNat))) (d * e.size) = true := by
  decide +kernel

theorem oneItemSize_proven : OneItemSize :=
  fun p hp e he d hd => okEq_sound _ _ (oneItem_check p hp e he d hd)

/-! ### `whichtable` -/

theorem pass2_mem (tbl : List FormatDef) : ∀ (fuel : Nat) (s : List Char) (acc : List Code × Nat),
    (∀ c ∈ acc.1, c.fmtdef ∈ tbl) → ∀ c ∈ (pass2 tbl fuel s acc).1, c.fmtdef ∈ tbl := by
  intro fuel
  induction fuel with
  | zero => intro s acc h; exact h
  | succ fuel ih =>
    intro s acc h
    have hitem : ∀ acc num c r, (∀ x ∈ acc.1, x.fmtdef ∈ tbl) →
        ∀ x ∈ (pass2Item tbl acc num c r).1, x.fmtdef ∈ tbl := by
      intro acc num c r ha x hx
      obtain ⟨codes, size⟩ := acc
      unfold pass2Item at hx
      cases hg : getentry (c :: r) tbl with
      | error _ => rw [hg] at hx; exact ha x hx
      | ok e =>
        have he := (getentry_mem hg).1
        rw [hg] at hx
        simp only at hx
        split at hx
        · simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | hx
          · exact ha x hx
          · subst hx; exact he
        · split at hx
          · exact ha x hx
          · split at hx
            · simp only [List.mem_append, List.mem_singleton] at hx
              rcases hx with hx | hx
              · exact ha x hx
              · subst hx; exact he
            · exact ha x hx
    match s with
    | [] => exact h
    | c :: s =>
      unfold pass2
      split
      · exact ih _ _ h
      · split
        · split
          · exact h
          · exact ih _ _ (hitem _ _ _ _ h)
        · exact ih _ _ (hitem _ _ _ _ h)

/-- The byte-order character picks the table every code comes from: `<` and `=` the little-endian
table, `>` and `!` the big-endian one, `@` and no prefix the native one (`whichtable`, 1558-1582); and
without a prefix character the format is read from its first character, as with `@` (the back-out at
1577). A `whichtable` that sent `>` to the little-endian table, or swallowed a first code, fails this. -/
def PrefixTables : Prop :=
  (∀ (pc : Char) (body : List Nat) (s : SObj), pc ∈ ['<', '=', '>', '!', '@'] →
    prepareS (pc.toNat :: body) = .ok s →
    ∀ c ∈ s.codes, c.fmtdef ∈ (if pc = '<' ∨ pc = '=' then lilendianTable
      else if pc = '>' ∨ pc = '!' then bigendianTable else nativeTable)) ∧
  (∀ (x : Char) (body : List Nat), x ∉ ['<', '=', '>', '!', '@'] →
    (prepareS (x.toNat :: body)).map (fun s => (s.codes, s.sSize, s.sLen))
      = (prepareS ('@'.toNat :: x.toNat :: body)).map (fun s => (s.codes, s.sSize, s.sLen)))

theorem prepareS_codes (fmt : List Nat) (s : SObj) (h : prepareS fmt = .ok s) :
    ∀ c ∈ s.codes, c.fmtdef ∈ (whichtable (asciiChars fmt)).1.table := by
  unfold prepareS at h
  split at h
  · cases h
  split at h
  · cases h
  cases hw : whichtable (asciiChars fmt) with
  | mk t f =>
    rw [hw] at h
    simp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases hp : pass2 t.table (f.length + 1) f ([], 0) with
        | mk codes size =>
          rw [hp] at h
          cases h
          intro c hc
          have := pass2_mem t.table (f.length + 1) f ([], 0) (by simp) c (by rw [hp]; exact hc)
          simpa using this

theorem prefixTables_proven : PrefixTables := by
  refine ⟨fun pc body s hpc h c hc => ?_, fun x body hx => ?_⟩
  · have := prepareS_codes _ s h c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with rfl | rfl | rfl | rfl | rfl <;> simpa [asciiChars, whichtable, Tab.table] using this
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    have hw1 : whichtable (asciiChars (x.toNat :: body)) = (.native, asciiChars (x.toNat :: body)) := by
      simp only [asciiChars, List.map_cons, Char.ofNat_toNat]
      unfold whichtable
      split <;> simp_all
    have hw2 : whichtable (asciiChars ('@'.toNat :: x.toNat :: body)) =
        (.native, asciiChars (x.toNat :: body)) := by
      simp [asciiChars, whichtable]
    unfold prepareS
    rw [hw1, hw2]
    cases hp : pass1 Tab.native.table ((asciiChars (x.toNat :: body)).length + 1) (asciiChars (x.toNat :: body)) {} with
    | error e =>
      by_cases hA : (128 ≤ x.toNat ∨ ∃ y ∈ body, 128 ≤ y) <;> by_cases hB : (0 = x.toNat ∨ 0 ∈ body) <;>
        simp [hA, hB, hp, Except.map]
    | ok st =>
      by_cases hA : (128 ≤ x.toNat ∨ ∃ y ∈ body, 128 ≤ y) <;> by_cases hB : (0 = x.toNat ∨ 0 ∈ body) <;>
        by_cases hM : maxN / 32 < st.ncodes + 1 <;> simp [hA, hB, hp, hM, Except.map]

/-! ### `set_format` -/

theorem decodeSurrogate_ascii (b : List Nat) (h : ∀ x ∈ b, x < 128) : decodeSurrogate b = b := by
  unfold decodeSurrogate
  conv => rhs; rw [← List.map_id b]
  apply List.map_congr_left
  intro x hx
  simp [h x hx]

/-- `set_format` (1805-1830): an object that is neither `str` nor `bytes` is `TypeError` naming its type
(1814-1818); `bytes` are decoded with `surrogateescape`, so a non-ASCII byte becomes a non-ASCII
character and the refusal of `prepare_s`, and ASCII bytes give the same struct as the equal `str`. -/
def SetFormatLaw : Prop :=
  (∀ (t : String) (h : Bool), setFormat (.other t h) =
    .error (.typeError s!"Struct() argument 1 must be a str or bytes object, not {t}")) ∧
  (∀ (t : String) (e : PyExc), setFormat (.hashRaises t e) =
    .error (.typeError s!"Struct() argument 1 must be a str or bytes object, not {t}")) ∧
  (∀ b : List Nat, (∃ x ∈ b, 128 ≤ x) →
    setFormat (.bytes b) = .error (.valueError "non-ASCII character in struct format")) ∧
  (∀ b : List Nat, (∀ x ∈ b, x < 128) → setFormat (.bytes b) = setFormat (.str b))

theorem setFormatLaw_proven : SetFormatLaw := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun b ⟨x, hx, hx2⟩ => ?_, fun b h => ?_⟩
  · simp only [setFormat]
    apply prepareRefusals_proven.1
    refine ⟨if x < 128 then x else 0xDC00 + x, ?_, ?_⟩
    · simp only [decodeSurrogate, List.mem_map]; exact ⟨x, hx, rfl⟩
    · simp only [if_neg (show ¬ x < 128 by omega)]; omega
  · simp only [setFormat, decodeSurrogate_ascii b h]

/-! ### The life of a `Struct`, by its branches -/

def reinitMsg : String :=
  "Re-initialization of Struct by calling the __init__() method will not work in future Python versions"
def diffMsg : String := "Different format arguments for __new__() and __init__() methods of Struct"

/-- The branches of `s_new` (1868-1934), `Struct_impl` (1843-1863), `same_format` (1937-1950),
`Struct___init___impl` (1964-1987) and `s_init` (1990-2004), each by its outcome:
- a subclass `__new__` that calls `Struct.__new__` goes through the clinic parser of `Struct_impl`, so a
  missing or extra argument is `TypeError` and a bad format raises (1870-1873);
- for the default `__new__`, `format=` as a keyword is the format (1879-1883); with a custom `__init__` a
  missing or an extra argument is only a `DeprecationWarning` and the object has no format yet
  (1884-1902);
- `__init__` with the struct's own format, as `str` or as `bytes`, warns of nothing and keeps the
  struct; with another format it warns, "Different format ..." the first time and "Re-initialization ..."
  once `__init__` has run, and installs the new one; an object that is not a format warns and then
  raises `TypeError`;
- `s_init` on a struct `__init__` has already run on is explicit, so re-initialises: a guard without
  `!init_called` would make `s.__init__(fmt)` a silent no-op. -/
def LifeBranches : Prop :=
  (∀ (b : Bool) (f g : FmtArg),
    sNewL { newIsS := false, initIsS := b } ⟨[], []⟩ =
      (.error (.typeError "Struct() missing required argument 'format' (pos 1)"), []) ∧
    sNewL { newIsS := false, initIsS := b } ⟨[f, g], []⟩ =
      (.error (.typeError "Struct() takes at most 1 argument (2 given)"), []) ∧
    (∀ s, setFormat f = .ok s → sNewL { newIsS := false, initIsS := b } ⟨[f], []⟩ = (.ok { obj := some s }, [])) ∧
    (∀ e, setFormat f = .error e → sNewL { newIsS := false, initIsS := b } ⟨[f], []⟩ = (.error e, []))) ∧
  (∀ (f g : FmtArg) (s : SObj), setFormat f = .ok s →
    typeCallL {} ⟨[], [("format", f)]⟩ = (.ok { obj := some s, initCalled := true }, []) ∧
    sNewL { initIsS := false } ⟨[], []⟩ =
      (.ok {}, [("DeprecationWarning", "Struct() missing required argument 'format' (pos 1)")]) ∧
    sNewL { initIsS := false } ⟨[f, g], []⟩ =
      (.ok {}, [("DeprecationWarning", "Struct() takes at most 1 argument (2 given)")])) ∧
  (∀ (s : SObj) (b : Bool), (∀ c ∈ s.format, c < 128) →
    structInitImpl ⟨some s, b⟩ (.str s.format) = (.ok ⟨some s, true⟩, []) ∧
    structInitImpl ⟨some s, b⟩ (.bytes s.format) = (.ok ⟨some s, true⟩, [])) ∧
  (∀ (s s' : SObj) (b : Bool) (cps : List Nat), cps ≠ s.format → setFormat (.str cps) = .ok s' →
    structInitImpl ⟨some s, b⟩ (.str cps) =
      (.ok ⟨some s', true⟩, [("FutureWarning", if b then reinitMsg else diffMsg)])) ∧
  (∀ (s : SObj) (b : Bool) (t : String) (h : Bool),
    structInitImpl ⟨some s, b⟩ (.other t h) =
      (.error (.typeError s!"Struct() argument 1 must be a str or bytes object, not {t}"),
       [("FutureWarning", if b then reinitMsg else diffMsg)])) ∧
  (∀ (ty : SType) (s s' : SObj) (cps : List Nat), cps ≠ s.format → setFormat (.str cps) = .ok s' →
    sInitL ty ⟨some s, true⟩ ⟨[.str cps], []⟩ = (.ok ⟨some s', true⟩, [("FutureWarning", reinitMsg)]))

theorem lifeBranches_proven : LifeBranches := by
  refine ⟨fun b f g => ⟨by simp [sNewL, structImpl, parseFormat, bind, Except.bind],
      by simp [sNewL, structImpl, parseFormat, bind, Except.bind]; rfl, fun s h => ?_, fun e h => ?_⟩, fun f g s h => ⟨?_, by simp [sNewL], by simp [sNewL]; rfl⟩,
    fun s b h => ⟨?_, ?_⟩, fun s s' b cps hne h => ?_, fun s b t hh => ?_, fun ty s s' cps hne h => ?_⟩
  · simp [sNewL, structImpl, parseFormat, h, bind, Except.bind, pure, Except.pure]
  · simp [sNewL, structImpl, parseFormat, h, bind, Except.bind]
  · simp [typeCallL, sNewL, sInitL, h]
  · have : sameFormat s (.str s.format) = true := by simp [sameFormat]; exact h
    simp [structInitImpl, this]
  · have : sameFormat s (.bytes s.format) = true := by simp [sameFormat]
    simp [structInitImpl, this]
  · have : sameFormat s (.str cps) = false := by simp [sameFormat, hne]
    cases b <;> simp [structInitImpl, this, h, reinitMsg, diffMsg]
  · cases b <;> simp [structInitImpl, sameFormat, setFormat, reinitMsg, diffMsg]
  · have : sameFormat s (.str cps) = false := by simp [sameFormat, hne]
    simp [sInitL, parseFormat, structInitImpl, this, h, reinitMsg]

end PyLean.TextLibs.Struct
