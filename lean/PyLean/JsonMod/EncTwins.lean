import PyLean.JsonMod.Enc

/-!
The C encoder (`c_make_encoder`, `c_encode_basestring(_ascii)`) and the
pure-Python encoder (`_make_iterencode`, `py_encode_basestring(_ascii)`)
produce the same text or raise the same exception.
-/

namespace PyLean.JsonMod

open PyLean

/-- A code point of a Python `str` (`chr` accepts `0..0x10FFFF`). -/
def cpOk (c : Nat) : Bool := c ≤ 0x10FFFF

def strOk (s : PStr) : Bool := s.all cpOk

/-- The text of `float.__repr__` is ASCII. -/
def fltOk (r : PStr) : Bool := r.all (· < 128)

def EKey.ok : EKey → Bool
  | .str s => strOk s
  | .flt _ r => fltOk r
  | _ => true

mutual
/-- Every string in the value (keys included) is a Python `str`: its code
points are at most `0x10FFFF`. A type invariant of `EVal`. -/
def EVal.ok : EVal → Bool
  | .str s => strOk s
  | .flt _ r => fltOk r
  | .list xs => EVal.okList xs
  | .dict kvs => EVal.okItems kvs
  | _ => true
def EVal.okList : List EVal → Bool
  | [] => true
  | x :: xs => EVal.ok x && EVal.okList xs
def EVal.okItems : List (EKey × EVal) → Bool
  | [] => true
  | (k, x) :: xs => k.ok && EVal.ok x && EVal.okItems xs
end

/-- What the encoder options promise: no custom `encoder`, and `default()`
returns Python values. -/
structure ECfg.Ok (cfg : ECfg) : Prop where
  cst : cfg.customEnc = none
  dfl : ∀ n t v', cfg.dflt n t = .ok v' → v'.ok = true

theorem cEncStr_std {cfg : ECfg} (h : cfg.customEnc = none) (s : PStr) : cEncStr cfg s = .ok (cStrEnc cfg s) := by
  simp [cEncStr, h]

theorem and_0xf (x : Nat) : x &&& 0xf = x % 16 := Nat.and_two_pow_sub_one_eq_mod x 4

theorem uEsc_eq_cU (n : Nat) : uEsc n = 92 :: cU n := by
  simp only [uEsc, cU, Nat.shiftRight_eq_div_pow, and_0xf]

theorem or_d800 {x : Nat} (h : x < 1024) : 0xd800 ||| x = 0xd800 + x := by
  have := (Nat.two_pow_add_eq_or_of_lt (i := 10) h 54).symm
  simpa using this

theorem or_dc00 {x : Nat} (h : x < 1024) : 0xdc00 ||| x = 0xdc00 + x := by
  have := (Nat.two_pow_add_eq_or_of_lt (i := 10) h 55).symm
  simpa using this

theorem and_3ff (x : Nat) : x &&& 0x3ff = x % 1024 := Nat.and_two_pow_sub_one_eq_mod x 10

/-- Per-character agreement of the two ASCII escapers. -/
theorem asciiChar_twins (c : Nat) (hc : c ≤ 0x10FFFF) :
    (if c = 92 ∨ c = 34 ∨ ¬(32 ≤ c ∧ c ≤ 126) then pyAsciiReplace c else [c]) =
      (if sChar c then [c] else cAsciiEscapeChar c) := by
  by_cases h1 : c = 92
  · subst h1; decide
  by_cases h2 : c = 34
  · subst h2; decide
  by_cases h3 : 32 ≤ c ∧ c ≤ 126
  · have : sChar c = true := by simp [sChar]; omega
    simp [h1, h2, h3, this]
  · have hs : sChar c = false := by simp [sChar]; omega
    simp only [h3, not_false_eq_true, or_true, ↓reduceIte, hs, Bool.false_eq_true]
    simp only [pyAsciiReplace, escDct, cAsciiEscapeChar, h1, h2, ↓reduceIte]
    by_cases h4 : c = 8
    · subst h4; decide
    by_cases h5 : c = 12
    · subst h5; decide
    by_cases h6 : c = 10
    · subst h6; decide
    by_cases h7 : c = 13
    · subst h7; decide
    by_cases h8 : c = 9
    · subst h8; decide
    simp only [h4, h5, h6, h7, h8, ↓reduceIte]
    by_cases h9 : c < 32
    · have : ¬ c ≥ 0x10000 := by omega
      simp [h9, this, uEsc_eq_cU]
    · have hc32 : ¬ c < 32 := h9
      simp only [hc32, ↓reduceIte]
      by_cases h10 : c < 0x10000
      · have : ¬ c ≥ 0x10000 := by omega
        simp [h10, this, uEsc_eq_cU]
      · have : c ≥ 0x10000 := by omega
        simp only [h10, ↓reduceIte, this, uEsc_eq_cU, Nat.shiftRight_eq_div_pow, and_3ff]
        have e1 : (c - 0x10000) / 2 ^ 10 % 1024 < 1024 := Nat.mod_lt _ (by decide)
        have e2 : (c - 0x10000) % 1024 < 1024 := Nat.mod_lt _ (by decide)
        rw [or_d800 e1, or_dc00 e2]
        have e3 : 0xd800 + (c - 0x10000) / 2 ^ 10 % 1024 = 0xd800 - 0x10000 / 2 ^ 10 + c / 2 ^ 10 := by
          simp only [Nat.reducePow]; omega
        have e4 : 0xdc00 + (c - 0x10000) % 1024 = 0xdc00 + c % 1024 := by omega
        rw [e3, e4]
        simp

theorem asciiEscape_twins (s : PStr) (hs : strOk s = true) :
    pyEncodeBasestringAscii s = cAsciiEscape s := by
  simp only [pyEncodeBasestringAscii, cAsciiEscape]
  simp only [List.flatMap_def]
  congr 3
  apply List.map_congr_left
  intro c hc
  have : cpOk c = true := List.all_eq_true.mp hs c hc
  exact asciiChar_twins c (by simpa [cpOk] using this)

theorem escapeChar_twins (c : Nat) :
    (if c < 32 ∨ c = 92 ∨ c = 34 then (escDct c).getD [] else [c]) = cEscapeChar c := by
  simp only [escDct, cEscapeChar]
  by_cases h1 : c = 92
  · subst h1; decide
  by_cases h2 : c = 34
  · subst h2; decide
  by_cases h4 : c = 8
  · subst h4; decide
  by_cases h5 : c = 12
  · subst h5; decide
  by_cases h6 : c = 10
  · subst h6; decide
  by_cases h7 : c = 13
  · subst h7; decide
  by_cases h8 : c = 9
  · subst h8; decide
  simp only [h1, h2, h4, h5, h6, h7, h8, ↓reduceIte, or_false]
  by_cases h9 : c < 32
  · have : c ≤ 0x1f := by omega
    simp only [h9, ↓reduceIte, this, Option.getD_some, uEsc, Nat.shiftRight_eq_div_pow, and_0xf]
    have a : c / 4096 % 16 = 0 := by omega
    have b : c / 256 % 16 = 0 := by omega
    have d : c / 2 ^ 4 % 16 = c / 16 % 16 := by simp
    rw [a, b, d]
    rfl
  · have : ¬ c ≤ 0x1f := by omega
    simp [h9, this]

theorem escape_twins (s : PStr) : pyEncodeBasestring s = cEscape s := by
  simp only [pyEncodeBasestring, cEscape]
  simp only [List.flatMap_def]
  congr 3
  apply List.map_congr_left
  intro c _
  exact escapeChar_twins c

theorem strEnc_twins (cfg : ECfg) (s : PStr) (hs : strOk s = true) : pyStrEnc cfg s = cStrEnc cfg s := by
  simp only [pyStrEnc, cStrEnc]
  split
  · exact asciiEscape_twins s hs
  · exact escape_twins s

/-- `floatstr` and `encoder_encode_float` agree on every float. -/
theorem floatStr_twins (cfg : ECfg) (b : Nat) (r : PStr) : pyFloatStr cfg b r = cEncodeFloat cfg b r := by
  by_cases h1 : fltExp b = 2047
  · by_cases h2 : fltMant b = 0
    · cases h3 : fltNeg b <;> cases h4 : cfg.allowNan <;>
        simp [pyFloatStr, cEncodeFloat, fltIsNan, fltIsFinite, fltIsPosInf, fltIsNegInf, h1, h2, h3, h4]
    · cases h4 : cfg.allowNan <;>
        simp [pyFloatStr, cEncodeFloat, fltIsNan, fltIsFinite, fltIsPosInf, fltIsNegInf, h1, h2, h4]
  · simp [pyFloatStr, cEncodeFloat, fltIsNan, fltIsFinite, fltIsPosInf, fltIsNegInf, h1]

theorem keyStr_twins (cfg : ECfg) (k : EKey) : pyKeyStr cfg k = cKeyStr cfg k := by
  cases k with
  | bool b => cases b <;> rfl
  | flt b r => simp only [pyKeyStr, cKeyStr, floatStr_twins]
  | _ => rfl

theorem fltOk_str {r : PStr} (h : fltOk r = true) : strOk r = true := by
  apply List.all_eq_true.mpr
  intro c hc
  have := List.all_eq_true.mp h c hc
  simp only [decide_eq_true_eq] at this
  simp only [cpOk, decide_eq_true_eq]
  omega

theorem cEncodeFloat_ok {cfg : ECfg} {b : Nat} {r t : PStr} (hr : fltOk r = true)
    (h : cEncodeFloat cfg b r = .ok t) : fltOk t = true := by
  unfold cEncodeFloat at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h; decide
      · split at h
        · cases h; decide
        · cases h; decide
  · cases h; exact hr

theorem keyStr_ok {cfg : ECfg} {k : EKey} {ks : PStr} (hk : k.ok = true)
    (h : cKeyStr cfg k = .ok (some ks)) : strOk ks = true := by
  cases k with
  | str s => simp [cKeyStr] at h; subst h; exact hk
  | flt b r =>
    simp only [cKeyStr] at h
    cases hr : cEncodeFloat cfg b r with
    | error e => rw [hr] at h; cases h
    | ok t =>
      rw [hr] at h
      simp only [Except.map, Except.ok.injEq, Option.some.injEq] at h
      subst h
      exact fltOk_str (cEncodeFloat_ok hk hr)
  | int n =>
    simp only [cKeyStr] at h
    cases hr : intRepr n with
    | error e => rw [hr] at h; cases h
    | ok t =>
      rw [hr] at h
      simp only [Except.map, Except.ok.injEq, Option.some.injEq] at h
      subst h
      simp only [intRepr] at hr
      split at hr
      · cases hr
      · simp only [Except.ok.injEq] at hr
        subst hr
        apply List.all_eq_true.mpr
        intro c hc
        simp only [cpOk, decide_eq_true_eq]
        have hd : ∀ f n, ∀ c ∈ decDigitsF f n, c ≤ 57 := by
          intro f
          induction f with
          | zero => intro n c hc; simp [decDigitsF] at hc
          | succ f ih =>
            intro n c hc
            simp only [decDigitsF] at hc
            split at hc
            · simp at hc; omega
            · simp at hc
              rcases hc with hc | hc
              · exact ih _ c hc
              · have := Nat.mod_lt n (show 10 > 0 by decide); omega
        split at hc
        · simp at hc
          rcases hc with hc | hc
          · omega
          · have := hd _ _ c hc; omega
        · have := hd _ _ c hc; omega
  | bool b => cases b <;> simp [cKeyStr, encodedConst] at h <;> subst h <;> decide
  | none => simp [cKeyStr, encodedConst] at h; subst h; decide
  | tup n => simp only [cKeyStr] at h; split at h <;> cases h

theorem okItems_insert (p : EKey × EVal) (items : List (EKey × EVal)) :
    EVal.okItems (insertItem p items) = (p.1.ok && EVal.ok p.2 && EVal.okItems items) := by
  induction items with
  | nil => simp [insertItem, EVal.okItems]
  | cons q t ih =>
    simp only [insertItem]
    split
    · simp [EVal.okItems]
    · simp only [EVal.okItems, ih]
      cases p.1.ok <;> cases EVal.ok p.2 <;> cases q.1.ok <;> cases EVal.ok q.2 <;> simp

theorem okItems_foldr (kvs : List (EKey × EVal)) :
    EVal.okItems (kvs.foldr insertItem []) = EVal.okItems kvs := by
  induction kvs with
  | nil => rfl
  | cons p t ih => simp only [List.foldr_cons, okItems_insert, ih, EVal.okItems]

theorem sortItems_ok {kvs items : List (EKey × EVal)} (h : sortItems kvs = .ok items) :
    EVal.okItems items = EVal.okItems kvs := by
  unfold sortItems at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · split at h
    · cases h; exact okItems_foldr _
    · cases h

theorem encList_twins (cfg : ECfg) (f : Nat)
    (ih : ∀ lvl seen v, v.ok = true → pyEnc cfg f lvl seen v = cEnc cfg f lvl seen v)
    (lvl : Nat) (seen : List Nat) (sep : PStr) :
    ∀ (xs : List EVal) (i : Nat), EVal.okList xs = true →
    pyEncList cfg f lvl seen sep (decide (i = 0)) xs = cEncList cfg f lvl seen sep i xs := by
  intro xs
  induction xs with
  | nil => intro i _; simp [pyEncList, cEncList]
  | cons x xs ihx =>
    intro i h
    simp only [EVal.okList, Bool.and_eq_true] at h
    simp only [pyEncList, cEncList]
    rw [ih lvl seen x h.1]
    have := ihx (i + 1) h.2
    simp only [Nat.add_one_ne_zero, decide_false] at this
    rw [this]
    by_cases hi : i = 0 <;> simp [hi]

theorem encItems_twins (cfg : ECfg) (hc : cfg.customEnc = none) (f : Nat)
    (ih : ∀ lvl seen v, v.ok = true → pyEnc cfg f lvl seen v = cEnc cfg f lvl seen v)
    (lvl : Nat) (seen : List Nat) (sep : PStr) :
    ∀ (items : List (EKey × EVal)) (first : Bool), EVal.okItems items = true →
    pyEncItems cfg f lvl seen (cfg.indent.map fun ind => [10] ++ rep ind lvl) sep first items =
      cEncItems cfg f lvl seen sep first items := by
  intro items
  induction items with
  | nil => intro _ _; simp [pyEncItems, cEncItems]
  | cons p xs ihx =>
    obtain ⟨k, x⟩ := p
    intro first h
    simp only [EVal.okItems, Bool.and_eq_true] at h
    simp only [pyEncItems, cEncItems, keyStr_twins, cEncStr_std hc]
    cases hk : cKeyStr cfg k with
    | error e => rfl
    | ok o =>
      cases o with
      | none => exact ihx first h.2
      | some ks =>
        simp only
        rw [ih lvl seen x h.1.2, ihx false h.2, strEnc_twins cfg ks (keyStr_ok h.1.1 hk)]
        cases cfg.indent <;> rfl

theorem enc_twins (cfg : ECfg) (hO : cfg.Ok) : ∀ (f lvl : Nat) (seen : List Nat) (v : EVal), v.ok = true →
    pyEnc cfg f lvl seen v = cEnc cfg f lvl seen v := by
  intro f
  induction f with
  | zero => intro lvl seen v _; simp [pyEnc, cEnc]
  | succ f ih =>
    intro lvl seen v hv
    cases v with
    | none => simp [pyEnc, cEnc]
    | bool b => cases b <;> simp [pyEnc, cEnc]
    | int n => simp [pyEnc, cEnc]
    | flt b r => simp only [pyEnc, cEnc, floatStr_twins]
    | str s => simp only [pyEnc, cEnc, cEncStr_std hO.cst]; rw [strEnc_twins cfg s hv]
    | back k => simp [pyEnc, cEnc]
    | other n t =>
      simp only [pyEnc, cEnc]
      split
      · rfl
      · cases hd : cfg.dflt n t with
        | error e => rfl
        | ok v' => exact ih lvl (n :: seen) v' (hO.dfl n t v' hd)
    | list xs =>
      have hl : ∀ sep lvl', pyEncList cfg f lvl' seen sep true xs = cEncList cfg f lvl' seen sep 0 xs := by
        intro sep lvl'
        have := encList_twins cfg f ih lvl' seen sep xs 0 hv
        simpa using this
      simp only [pyEnc, cEnc, List.length_eq_zero_iff]
      split
      · rfl
      · cases hi : cfg.indent with
        | none => simp only [hl]; rfl
        | some ind => simp only [hl, cNewlineIndent, cSepIndent, List.append_assoc, Option.getD_some]
    | dict kvs =>
      simp only [pyEnc, cEnc, List.length_eq_zero_iff]
      split
      · rfl
      · cases hs : (if cfg.sortKeys then sortItems kvs else Except.ok kvs) with
        | error e => simp only
        | ok items =>
          have hok : EVal.okItems items = true := by
            rw [← (show EVal.okItems kvs = true from hv)]
            by_cases hsk : cfg.sortKeys
            · simp only [hsk, ↓reduceIte] at hs; exact sortItems_ok hs
            · simp only [hsk, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hs; rw [hs]
          simp only
          cases hi : cfg.indent with
          | none =>
            have := encItems_twins cfg hO.cst f ih lvl seen cfg.itemSep items true hok
            simp only [hi, Option.map_none] at this
            simp only [this]
          | some ind =>
            have := encItems_twins cfg hO.cst f ih (lvl + 1) seen (cfg.itemSep ++ [10] ++ rep ind (lvl + 1)) items true hok
            simp only [hi, Option.map_some, List.append_assoc] at this
            simp only [cSepIndent, cNewlineIndent, List.append_assoc]
            rw [this]
            cases cEncItems cfg f (lvl + 1) seen (cfg.itemSep ++ ([10] ++ rep ind (lvl + 1))) true items with
            | error e => rfl
            | ok r => obtain ⟨body, first⟩ := r; cases first <;> rfl

/-- On the same value (a type-correct Python object: code points at most
`0x10FFFF`, ASCII `float.__repr__`), for every `default()` returning such values,
every `allow_nan` and the other options, `json.dumps` with the C encoder and
with the pure-Python encoder return the same text or raise the same exception
(class and message; `TypeError` from mixed-type `sort_keys` excepted, whose
message both take from the same `list.sort`). -/
def DumpsTwins : Prop := ∀ (cfg : ECfg) (v : EVal), cfg.Ok → v.ok = true → dumpsPy cfg v = dumpsC cfg v

theorem dumpsTwins_proven : DumpsTwins := by
  intro cfg v hO hv
  cases v with
  | str s =>
    simp only [dumpsPy, dumpsC]
    rw [strEnc_twins cfg s hv]
    rfl
  | _ => simp only [dumpsPy, dumpsC]; exact enc_twins cfg hO _ 0 [] _ hv

end PyLean.JsonMod
