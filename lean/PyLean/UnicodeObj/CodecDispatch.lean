import PyLean.UnicodeObj.CodecCharmap
import PyLean.UnicodeObj.CodecEscapeProps

/-!
The fast dispatch by encoding name, `_Py_normalize_encoding` (unicodeobject.c:3523-3567) with
the shortcuts of `PyUnicode_Decode` (:3570-3657) and `PyUnicode_AsEncodedString` (:3828-3925),
`_Py_GetErrorHandler` (:469-493), and properties of the charmap codec.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- The loop of `_Py_normalize_encoding`, unicodeobject.c:3537-3563. `room` is what is left
of the buffer, `l` the output so far, reversed. `none` is the `return 0` of a full buffer.
A NUL ends the C string. -/
def normalizeLoop : List Nat → Bool → Nat → List Nat → Option (List Nat)
  | [], _, _, l => some l.reverse
  | c :: cs, punct, room, l =>
    if c == 0 then some l.reverse
    else if pyIsAlnum c || c == 46 then
      if punct && !l.isEmpty then
        if room == 0 then none
        else if room == 1 then none
        else normalizeLoop cs false (room - 2) (pyToLower c :: 95 :: l)
      else if room == 0 then none
      else normalizeLoop cs false (room - 1) (pyToLower c :: l)
    else normalizeLoop cs true room l

/-- `_Py_normalize_encoding(encoding, buflower, 11)`: ten characters and the NUL. -/
def normalizeEncoding (name : List Nat) : Option (List Nat) := normalizeLoop name false 10 []

/-- Which codec a name reaches without the registry. -/
inductive Shortcut where
  | utf8 | utf16 | utf32 | ascii | latin1 | registry
  deriving Repr, DecidableEq

/-- The shortcuts of `PyUnicode_Decode` and `PyUnicode_AsEncodedString`. -/
def shortcutOf (name : List Nat) : Shortcut :=
  match normalizeEncoding name with
  | none => .registry
  | some l =>
    if l == lit "utf8" || l == lit "utf_8" then .utf8
    else if l == lit "utf16" || l == lit "utf_16" then .utf16
    else if l == lit "utf32" || l == lit "utf_32" then .utf32
    else if l == lit "ascii" || l == lit "us_ascii" then .ascii
    else if l == lit "latin1" || l == lit "latin_1" || l == lit "iso_8859_1" ||
        l == lit "iso8859_1" then .latin1
    else .registry

/-- `_Py_GetErrorHandler`, unicodeobject.c:469-493, on the names it recognises: `namereplace`
is `_Py_ERROR_OTHER` there and goes through the registry to the same handler. -/
def getErrorHandler (errors : String) : Option ErrHandler :=
  if errors == "strict" then some .strict
  else if errors == "surrogateescape" then some .surrogateescape
  else if errors == "replace" then some .replace
  else if errors == "ignore" then some .ignore
  else if errors == "backslashreplace" then some .backslashreplace
  else if errors == "surrogatepass" then some .surrogatepass
  else if errors == "xmlcharrefreplace" then some .xmlcharrefreplace
  else none

/-- Encoding names are case-insensitive for the fast dispatch: the upper-cased name
normalises to the same thing, for every name of bytes. -/
def NormalizeCase : Prop :=
  ∀ name : List Nat, (∀ c ∈ name, c < 256) →
    normalizeEncoding (name.map pyToUpper) = normalizeEncoding name

theorem upper_facts : ∀ c, c < 256 →
    (pyToUpper c == 0) = (c == 0) ∧
    (pyIsAlnum (pyToUpper c) || pyToUpper c == 46) = (pyIsAlnum c || c == 46) ∧
    pyToLower (pyToUpper c) = pyToLower c := by
  decide +kernel

theorem normalizeLoop_upper (name : List Nat) (h : ∀ c ∈ name, c < 256) (p r l) :
    normalizeLoop (name.map pyToUpper) p r l = normalizeLoop name p r l := by
  induction name generalizing p r l with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨h1, h2, h3⟩ := upper_facts c (h c List.mem_cons_self)
    have ih' := fun p r l => ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) p r l
    simp only [List.map_cons, normalizeLoop, h1, h2, h3, ih']

theorem normalizeCase_proven : NormalizeCase :=
  fun name h => normalizeLoop_upper name h false 10 []

/-! ## Charmap -/

theorem decodeDriver_map (step : List Nat → DStep) (f : Nat → Nat) (h e code input)
    (b : List Nat) (hstop : step [] = .stop)
    (hstep : ∀ x ∈ b, ∀ r, step (x :: r) = .char (f x) 1)
    (fuel pos : Nat) (out : Str) (hf : b.length < fuel) :
    decodeDriver step h e code input fuel pos b out = .ok (out ++ b.map f, pos + b.length) := by
  induction b generalizing fuel pos out with
  | nil =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [decodeDriver, hstop]
  | cons x xs ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [List.length_cons] at hf
      simp only [decodeDriver, hstep x List.mem_cons_self, List.drop_succ_cons, List.drop_zero]
      rw [ih (fun y hy => hstep y (List.mem_cons_of_mem _ hy)) fuel _ _ (by omega)]
      simp [Nat.add_assoc, Nat.add_comm 1]

/-- Charmap decoding by a `str` table maps each byte through the table, when no byte is
undefined, for every table and every input. -/
def CharmapDecodeString : Prop :=
  ∀ (table : Str) (b : Bytes) (h : ErrHandler),
    (∀ x ∈ b, x < table.length ∧ table.getD x 0 ≠ 0xfffe) →
    charmapDecode b (.str table) h = .ok (b.map (table.getD · 0))

theorem charmapDecodeString_proven : CharmapDecodeString := by
  intro table b h hb
  unfold charmapDecode
  cases b with
  | nil => rfl
  | cons x xs =>
    have := decodeDriver_map (stepCharmapString table) (table.getD · 0) h "charmap" .unknown
      (x :: xs) (x :: xs) rfl (fun y hy r => by
        obtain ⟨h1, h2⟩ := hb y hy
        have h3 : (table.getD y 0 == 0xfffe) = false := by simpa using h2
        simp only [stepCharmapString, if_pos h1, h3, Bool.false_eq_true, if_false])
      ((x :: xs).length + 1) 0 [] (by omega)
    have e : (x :: xs).isEmpty = false := rfl
    simp only [e, Bool.false_eq_true, if_false, bind, Except.bind]
    rw [this]
    simp [pure, Except.pure]

/-- Charmap decoding by a mapping, for every mapping that gives each byte an int in range. -/
def CharmapDecodeMapping : Prop :=
  ∀ (m : Mapping) (f : Nat → Nat) (b : Bytes) (h : ErrHandler),
    (∀ x ∈ b, m x = .int (f x) ∧ f x ≤ maxUnicode ∧ f x ≠ 0xFFFE) →
    charmapDecode b (.map m) h = .ok (b.map f)

theorem charmapDecodeMapping_proven : CharmapDecodeMapping := by
  intro m f b h hb
  unfold charmapDecode
  cases b with
  | nil => rfl
  | cons x xs =>
    have := decodeDriver_map (stepCharmapMapping m) f h "charmap" .unknown
      (x :: xs) (x :: xs) rfl (fun y hy r => by
        obtain ⟨h1, h2, h3⟩ := hb y hy
        have h4 : ¬ ((f y : Int) = 0xFFFE) := by omega
        have h5 : ¬ ((f y : Int) < 0 ∨ (f y : Int) > maxUnicode) := by omega
        simp only [stepCharmapMapping, h1]
        rw [if_neg h4, if_neg h5]
        simp)
      ((x :: xs).length + 1) 0 [] (by omega)
    have e : (x :: xs).isEmpty = false := rfl
    simp only [e, Bool.false_eq_true, if_false, bind, Except.bind]
    rw [this]
    simp [pure, Except.pure]

/-- Charmap encoding by a mapping, for every mapping that gives each character a byte. -/
def CharmapEncodeMapping : Prop :=
  ∀ (m : Nat → EncItem) (f : Nat → Nat) (s : Str) (h nameOf),
    (∀ c ∈ s, m c = .int (f c) ∧ f c ≤ 255) →
    charmapEncode s (.map m) h nameOf = .ok (s.map f)

theorem charmapEncodeLoop_map (input : Str) (m : Nat → EncItem) (f : Nat → Nat) (h nameOf)
    (s : Str) (hs : ∀ c ∈ s, m c = .int (f c) ∧ f c ≤ 255) (fuel pos : Nat) (out : Bytes)
    (hf : s.length < fuel) :
    charmapEncodeLoop input (.map m) h nameOf fuel pos s out = .ok (out ++ s.map f) := by
  induction s generalizing fuel pos out with
  | nil =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [charmapEncodeLoop]
  | cons c cs ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [List.length_cons] at hf
      obtain ⟨h1, h2⟩ := hs c List.mem_cons_self
      have hn : ¬ ((f c : Int) < 0 ∨ (f c : Int) > 255) := by omega
      simp only [charmapEncodeLoop, charmapencodeOutput, charmapencodeLookup, h1, hn, if_false]
      rw [ih (fun x hx => hs x (List.mem_cons_of_mem _ hx)) fuel _ _ (by omega)]
      simp

theorem charmapEncodeMapping_proven : CharmapEncodeMapping := by
  intro m f s h nameOf hs
  simpa [charmapEncode] using charmapEncodeLoop_map s m f h nameOf s hs (s.length + 1) 0 [] (by omega)

/-- U+FFFE means "unmapped" in a decoding table, so `PyUnicode_BuildEncodingMap` never gives
it a byte, in either of its two results. -/
def BuildMapsNoFFFE : Prop :=
  ∀ table : Str, table ≠ [] →
    match buildEncodingMap table with
    | .trie t => encodingMapLookup 0xFFFE t = none
    | .dict d => d.lookup 0xFFFE = none

/-- A table with a non-BMP character takes the dict branch, which has no such check. -/
theorem buildMapsNoFFFE_refuted : ¬ BuildMapsNoFFFE := by
  intro h
  have h2 : List.lookup 0xFFFE [(0, 0), (0xFFFE, 1), (0x10000, 2)] = none :=
    h [0, 0xFFFE, 0x10000] (by simp)
  revert h2
  decide

/-! ## Replacements -/

theorem decChars_ascii (fuel n : Nat) (acc : List Nat) (h : ∀ x ∈ acc, x < 128) :
    ∀ x ∈ decChars fuel n acc, x < 128 := by
  induction fuel generalizing n acc with
  | zero => simpa [decChars] using h
  | succ fuel ih =>
    have ha : ∀ x ∈ (48 + n % 10) :: acc, x < 128 := by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · exact h x hx
    simp only [decChars]
    split
    · exact ha
    · exact ih _ _ ha

theorem hexDigits_ascii (w n : Nat) : ∀ x ∈ hexDigits w n, x < 128 := by
  intro x hx
  simp only [hexDigits, List.mem_map] at hx
  obtain ⟨i, -, rfl⟩ := hx
  have : (n >>> (4 * i)) &&& 15 ≤ 15 := Nat.and_le_right
  simp only [hexLower]
  split <;> omega

/-- The replacements of `backslashreplace` and `xmlcharrefreplace` are ASCII for every
character, so the ASCII encoder can write them straight to its output. -/
def ReplacementsAscii : Prop :=
  ∀ c : Nat, (∀ x ∈ escapeEncodeChar c, x < 128) ∧ (∀ x ∈ xmlRef c, x < 128)

theorem replacementsAscii_proven : ReplacementsAscii := by
  intro c
  constructor
  · intro x hx
    have hh := fun w => hexDigits_ascii w c x
    simp only [escapeEncodeChar] at hx
    repeat' split at hx
    all_goals
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (hx | hx) | hx
      · omega
      · omega
      · exact hh _ hx
  · intro x hx
    simp only [xmlRef, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with ((hx | hx) | hx) | hx
    · omega
    · omega
    · exact decChars_ascii _ _ _ (by simp) x hx
    · omega

/-- `_Py_GetErrorHandler` classifies each of the seven names to its handler, and sends every
other name, `namereplace` among them, to the registry. -/
def ErrorHandlerNames : Prop :=
  getErrorHandler "strict" = some .strict ∧ getErrorHandler "ignore" = some .ignore ∧
  getErrorHandler "replace" = some .replace ∧
  getErrorHandler "surrogateescape" = some .surrogateescape ∧
  getErrorHandler "surrogatepass" = some .surrogatepass ∧
  getErrorHandler "backslashreplace" = some .backslashreplace ∧
  getErrorHandler "xmlcharrefreplace" = some .xmlcharrefreplace ∧
  getErrorHandler "namereplace" = none

theorem errorHandlerNames_proven : ErrorHandlerNames := by
  unfold ErrorHandlerNames
  decide +kernel

end PyLean.UnicodeObj
