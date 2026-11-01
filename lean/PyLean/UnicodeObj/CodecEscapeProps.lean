import PyLean.UnicodeObj.CodecEscape
import PyLean.UnicodeObj.CodecUtf7

/-!
Properties of ASCII, Latin-1, UTF-7, `unicode_escape` and `raw_unicode_escape`.
-/

namespace PyLean.UnicodeObj

open PyLean

/-! ## Hex escapes -/

theorem hexValue_hexLower : ∀ d, d < 16 → hexValue (hexLower d) = some d := by decide

theorem hexEscape_cons (count c : Nat) (cs : List Nat) (n acc v : Nat) (h : hexValue c = some v) :
    hexEscape (count + 1) (c :: cs) n acc = hexEscape count cs (n + 1) (acc * 16 + v) := by
  simp [hexEscape, h]

theorem hexEscape_hex2 (c n : Nat) (r : List Nat) (hc : c < 256) :
    hexEscape 2 (hex2 c ++ r) n 0 = .ok c := by
  simp only [hex2, List.cons_append, List.nil_append]
  rw [hexEscape_cons _ _ _ _ _ _ (hexValue_hexLower _ (by omega)),
    hexEscape_cons _ _ _ _ _ _ (hexValue_hexLower _ (by omega))]
  simp only [hexEscape]
  congr 1
  omega

theorem hexEscape_hex4 (c n : Nat) (r : List Nat) (hc : c < 65536) :
    hexEscape 4 (hex4 c ++ r) n 0 = .ok c := by
  simp only [hex4, hex2, List.cons_append, List.nil_append]
  rw [hexEscape_cons _ _ _ _ _ _ (hexValue_hexLower _ (by omega)),
    hexEscape_cons _ _ _ _ _ _ (hexValue_hexLower _ (by omega)),
    hexEscape_cons _ _ _ _ _ _ (hexValue_hexLower _ (by omega)),
    hexEscape_cons _ _ _ _ _ _ (hexValue_hexLower _ (by omega))]
  simp only [hexEscape]
  congr 1
  omega

theorem hexEscape_hex8 (c n : Nat) (r : List Nat) (hc : c ≤ maxUnicode) :
    hexEscape 8 (hex8 c ++ r) n 0 = .ok c := by
  have hm : maxUnicode = 0x10FFFF := rfl
  simp only [hex8, hex4, hex2, List.cons_append, List.nil_append]
  rw [hexEscape_cons _ _ _ _ _ _ (rfl : hexValue 48 = some 0),
    hexEscape_cons _ _ _ _ _ _ (rfl : hexValue 48 = some 0),
    hexEscape_cons _ _ _ _ _ _ (hexValue_hexLower _ (by omega)),
    hexEscape_cons _ _ _ _ _ _ (hexValue_hexLower _ (by omega)),
    hexEscape_cons _ _ _ _ _ _ (hexValue_hexLower _ (by omega)),
    hexEscape_cons _ _ _ _ _ _ (hexValue_hexLower _ (by omega)),
    hexEscape_cons _ _ _ _ _ _ (hexValue_hexLower _ (by omega)),
    hexEscape_cons _ _ _ _ _ _ (hexValue_hexLower _ (by omega))]
  simp only [hexEscape]
  congr 1
  omega

/-! ## `unicode_escape` -/

theorem hexLower_length2 (c : Nat) : (hex2 c).length = 2 := rfl
theorem hexLower_length4 (c : Nat) : (hex4 c).length = 4 := rfl
theorem hexLower_length8 (c : Nat) : (hex8 c).length = 8 := rfl

theorem stepUE_x (names cons r) (c : Nat) (hc : c < 256) :
    stepUnicodeEscape names cons (92 :: 120 :: (hex2 c ++ r)) = .char c 4 := by
  have hm : maxUnicode = 0x10FFFF := rfl
  show stepHex cons 2 "truncated \\xXX escape" (hex2 c ++ r) = _
  simp only [stepHex, hexEscape_hex2 c 0 r hc]
  rw [if_neg (by omega)]

theorem stepUE_u (names cons r) (c : Nat) (hc : c < 65536) :
    stepUnicodeEscape names cons (92 :: 117 :: (hex4 c ++ r)) = .char c 6 := by
  have hm : maxUnicode = 0x10FFFF := rfl
  show stepHex cons 4 "truncated \\uXXXX escape" (hex4 c ++ r) = _
  simp only [stepHex, hexEscape_hex4 c 0 r hc]
  rw [if_neg (by omega)]

theorem stepUE_U (names cons r) (c : Nat) (hc : c ≤ maxUnicode) :
    stepUnicodeEscape names cons (92 :: 85 :: (hex8 c ++ r)) = .char c 10 := by
  show stepHex cons 8 "truncated \\UXXXXXXXX escape" (hex8 c ++ r) = _
  simp only [stepHex, hexEscape_hex8 c 0 r hc]
  rw [if_neg (by omega)]

theorem stepUE_char (names cons) (c : Nat) (r : List Nat) (hc : c ≤ maxUnicode) :
    stepUnicodeEscape names cons (unicodeEscapeChar c ++ r) =
      .char c (unicodeEscapeChar c).length := by
  unfold unicodeEscapeChar
  by_cases h1 : c < 0x100
  · rw [if_pos h1]
    by_cases h2 : c ≥ 32 ∧ c < 127
    · rw [if_pos h2]
      by_cases h3 : c = 92
      · subst h3
        rfl
      · have h3' : (c != 92) = true := by simpa using h3
        simp only [h3', if_true, List.cons_append, List.nil_append, List.length_cons,
          List.length_nil, stepUnicodeEscape]
    · rw [if_neg h2]
      by_cases h3 : c = 9
      · subst h3; rfl
      · rw [if_neg h3]
        by_cases h4 : c = 10
        · subst h4; rfl
        · rw [if_neg h4]
          by_cases h5 : c = 13
          · subst h5; rfl
          · rw [if_neg h5]
            exact stepUE_x names cons r c h1
  · rw [if_neg h1]
    by_cases h2 : c < 0x10000
    · rw [if_pos h2]
      exact stepUE_u names cons r c h2
    · rw [if_neg h2]
      exact stepUE_U names cons r c hc

theorem unicodeEscapeChar_pos (c : Nat) : 1 ≤ (unicodeEscapeChar c).length := by
  unfold unicodeEscapeChar
  repeat' split
  all_goals simp

theorem length_flat_pos (enc : Nat → List Nat) (hl : ∀ c, 1 ≤ (enc c).length) (c : Nat)
    (cs : List Nat) : ((c :: cs).flatMap enc).isEmpty = false := by
  have h1 := hl c
  cases hk : (c :: cs).flatMap enc with
  | nil =>
    rw [List.flatMap_cons] at hk
    have := (List.append_eq_nil_iff.1 hk).1
    simp [this] at h1
  | cons _ _ => rfl

/-- `s.encode('unicode_escape')` decodes back to `s` for every string, lone surrogates
included, one-shot or stateful, and all of it is consumed. -/
def UnicodeEscapeRoundTrip : Prop :=
  ∀ (s : Str) (names : List Nat → Option Nat) (final : Bool), Str.Valid s →
    unicodeEscapeDecode (unicodeEscapeEncode s) .strict names final =
      .ok (s, (unicodeEscapeEncode s).length)

theorem unicodeEscapeRoundTrip_proven : UnicodeEscapeRoundTrip := by
  intro s names final hv
  unfold unicodeEscapeDecode unicodeEscapeEncode
  have hlen := length_le_flat unicodeEscapeChar unicodeEscapeChar_pos s
  cases hs : s with
  | nil => simp
  | cons c cs =>
    subst hs
    simp only [length_flat_pos unicodeEscapeChar unicodeEscapeChar_pos, Bool.false_eq_true, if_false]
    have := decodeDriver_flatMap (stepUnicodeEscape names !final) unicodeEscapeChar .strict
      "unicodeescape" .unknown ((c :: cs).flatMap unicodeEscapeChar) (c :: cs) rfl
      (fun x hx r => stepUE_char names (!final) x r (hv x hx))
      (((c :: cs).flatMap unicodeEscapeChar).length + 1) 0 [] (by omega)
    simpa using this

/-! ## `raw_unicode_escape` -/

theorem stepRaw_u (cons r) (c : Nat) (hc : c < 65536) :
    stepRawEscape cons (92 :: 117 :: (hex4 c ++ r)) = .char c 6 := by
  have hm : maxUnicode = 0x10FFFF := rfl
  show rawHex cons 4 "truncated \\uXXXX escape" (hex4 c ++ r) = _
  simp only [rawHex, hexEscape_hex4 c 0 r hc]
  rw [if_neg (by omega)]

theorem stepRaw_U (cons r) (c : Nat) (hc : c ≤ maxUnicode) :
    stepRawEscape cons (92 :: 85 :: (hex8 c ++ r)) = .char c 10 := by
  show rawHex cons 8 "truncated \\UXXXXXXXX escape" (hex8 c ++ r) = _
  simp only [rawHex, hexEscape_hex8 c 0 r hc]
  rw [if_neg (by omega)]

theorem stepRaw_char (cons) (c : Nat) (r : List Nat) (hc : c ≤ maxUnicode) (h92 : c ≠ 92) :
    stepRawEscape cons (rawEscapeChar c ++ r) = .char c (rawEscapeChar c).length := by
  unfold rawEscapeChar
  by_cases h1 : c < 0x100
  · rw [if_pos h1]
    have h' : (c != 92) = true := by simpa using h92
    simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil, stepRawEscape,
      h', if_true]
  · rw [if_neg h1]
    by_cases h2 : c < 0x10000
    · rw [if_pos h2]
      exact stepRaw_u cons r c h2
    · rw [if_neg h2]
      exact stepRaw_U cons r c hc

theorem rawEscapeChar_pos (c : Nat) : 1 ≤ (rawEscapeChar c).length := by
  unfold rawEscapeChar
  repeat' split
  all_goals simp

/-- `s.encode('raw_unicode_escape')` decodes back to `s` for every string with no
backslash. A backslash is the documented exception: the docs say existing backslashes are
not escaped, so `'\\u0041'` does not round-trip. -/
def RawEscapeRoundTrip : Prop :=
  ∀ (s : Str) (final : Bool), Str.Valid s → (∀ c ∈ s, c ≠ 92) →
    rawEscapeDecode (rawEscapeEncode s) .strict final = .ok (s, (rawEscapeEncode s).length)

theorem rawEscapeRoundTrip_proven : RawEscapeRoundTrip := by
  intro s final hv h92
  unfold rawEscapeDecode rawEscapeEncode
  have hlen := length_le_flat rawEscapeChar rawEscapeChar_pos s
  cases hs : s with
  | nil => simp
  | cons c cs =>
    subst hs
    simp only [length_flat_pos rawEscapeChar rawEscapeChar_pos, Bool.false_eq_true, if_false]
    have := decodeDriver_flatMap (stepRawEscape !final) rawEscapeChar .strict
      "rawunicodeescape" .unknown ((c :: cs).flatMap rawEscapeChar) (c :: cs) rfl
      (fun x hx r => stepRaw_char (!final) x r (hv x hx) (h92 x hx))
      (((c :: cs).flatMap rawEscapeChar).length + 1) 0 [] (by omega)
    simpa using this

/-! ## Chunks -/

/-- Decoding in two chunks with `final=False` on the first gives what decoding at once gives,
wherever the input is cut: the contract of a stateful decoder, which `\x`, `\u`, `\U` and `\N`
honour by holding the escape back. -/
def UnicodeEscapeChunks : Prop :=
  ∀ (b : Bytes) (k : Nat) (names : List Nat → Option Nat) (h : ErrHandler) (t u : Str) (n m : Nat),
    unicodeEscapeDecode (b.take k) h names false = .ok (t, n) →
    unicodeEscapeDecode (b.drop n) h names true = .ok (u, m) →
    unicodeEscapeDecode b h names true = .ok (t ++ u, b.length)

/-- `\107` cut after `\10`: the octal branch does not wait for its third digit. -/
theorem unicodeEscapeChunks_refuted : ¬ UnicodeEscapeChunks := by
  intro hc
  have := hc [92, 49, 48, 55] 3 (fun _ => none) .strict [8] [55] 3 1 (by decide) (by decide)
  revert this
  decide

/-! ## Latin-1 and ASCII -/

theorem ucs1Loop_plain (input : Str) (limit : Nat) (h nameOf) (s : Str) (hs : ∀ c ∈ s, c < limit)
    (fuel pos : Nat) (out : Bytes) (hf : s.length < fuel) :
    ucs1EncodeLoop input limit h nameOf fuel pos s out = .ok (out ++ s) := by
  induction s generalizing fuel pos out with
  | nil =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [ucs1EncodeLoop]
  | cons c cs ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [List.length_cons] at hf
      have hc := hs c List.mem_cons_self
      simp only [ucs1EncodeLoop, hc, if_true]
      rw [ih (fun x hx => hs x (List.mem_cons_of_mem _ hx)) fuel _ _ (by omega)]
      simp

/-- Latin-1 is a bijection: decoding any bytes and encoding gives them back. -/
def Latin1RoundTrip : Prop :=
  ∀ (b : Bytes) (h : ErrHandler) (nameOf : Nat → Option Str), Bytes.Valid b →
    ucs1Encode (latin1Decode b) 256 h nameOf = .ok b

theorem latin1RoundTrip_proven : Latin1RoundTrip := by
  intro b h nameOf hb
  simpa [ucs1Encode, latin1Decode] using
    ucs1Loop_plain b 256 h nameOf b hb (b.length + 1) 0 [] (by omega)

/-- The strict encoder reports the exact span: for a string whose first unencodable character
is at `pre.length`, the error runs from there to the end of the unencodable run. For both
limits and every string. -/
def Ucs1StrictError : Prop :=
  ∀ (pre : Str) (c : Nat) (cs : Str) (limit : Nat) (nameOf : Nat → Option Str),
    (∀ x ∈ pre, x < limit) → c ≥ limit → (limit = 128 ∨ limit = 256) →
    ucs1Encode (pre ++ c :: cs) limit .strict nameOf =
      .error (encodeError (if limit == 256 then "latin-1" else "ascii") (pre ++ c :: cs) pre.length
        (pre.length + (unencodableRun limit (c :: cs)).length)
        (if limit == 256 then "ordinal not in range(256)" else "ordinal not in range(128)"))

theorem ucs1Strict_loop (input : Str) (limit : Nat) (nameOf) (pre : Str) (c : Nat) (cs : Str)
    (hp : ∀ x ∈ pre, x < limit) (hc : c ≥ limit) (fuel pos : Nat) (out : Bytes)
    (hf : pre.length < fuel) :
    ucs1EncodeLoop input limit .strict nameOf fuel pos (pre ++ c :: cs) out =
      .error (encodeError (if limit == 256 then "latin-1" else "ascii") input (pos + pre.length)
        (pos + pre.length + (unencodableRun limit (c :: cs)).length)
        (if limit == 256 then "ordinal not in range(256)" else "ordinal not in range(128)")) := by
  induction pre generalizing fuel pos out with
  | nil =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hn : ¬ c < limit := by omega
      simp [ucs1EncodeLoop, hn]
  | cons x xs ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [List.length_cons] at hf
      have hx := hp x List.mem_cons_self
      simp only [List.cons_append, ucs1EncodeLoop, hx, if_true]
      rw [ih (fun y hy => hp y (List.mem_cons_of_mem _ hy)) fuel _ _ (by omega)]
      simp only [List.length_cons]
      congr 2 <;> omega

theorem ucs1StrictError_proven : Ucs1StrictError := by
  intro pre c cs limit nameOf hp hc _
  have := ucs1Strict_loop (pre ++ c :: cs) limit nameOf pre c cs hp hc
    ((pre ++ c :: cs).length + 1) 0 [] (by simp; omega)
  simpa [ucs1Encode] using this

theorem driver_ascii (input : Bytes) (h) (pre : Str) (hp : ∀ x ∈ pre, x < 128) (r : List Nat)
    (fuel pos : Nat) (out : Str) (hf : pre.length < fuel) :
    ∃ fuel', fuel = fuel' + pre.length ∧
      decodeDriver stepAscii h "ascii" .unknown input fuel pos (pre ++ r) out =
        decodeDriver stepAscii h "ascii" .unknown input fuel' (pos + pre.length) r (out ++ pre) := by
  induction pre generalizing fuel pos out with
  | nil => exact ⟨fuel, by simp, by simp⟩
  | cons x xs ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [List.length_cons] at hf
      have hx := hp x List.mem_cons_self
      obtain ⟨f, e, he⟩ := ih (fun y hy => hp y (List.mem_cons_of_mem _ hy)) fuel (pos + 1) (out ++ [x])
        (by omega)
      refine ⟨f, by simp only [List.length_cons]; omega, ?_⟩
      simp only [List.cons_append, decodeDriver, stepAscii, hx, if_true, List.drop_succ_cons,
        List.drop_zero]
      rw [he]
      simp [Nat.add_assoc, Nat.add_comm 1]

/-- ASCII decoding reports the first byte at or above 128, and accepts exactly the rest. -/
def AsciiStrict : Prop :=
  ∀ (pre : Bytes) (x : Nat) (post : Bytes), (∀ c ∈ pre, c < 128) → x ≥ 128 →
    (asciiDecode pre .strict = .ok pre) ∧
    asciiDecode (pre ++ x :: post) .strict =
      .error (decodeError "ascii" (pre ++ x :: post) pre.length (pre.length + 1)
        "ordinal not in range(128)")

theorem asciiStrict_proven : AsciiStrict := by
  intro pre x post hp hx
  constructor
  · obtain ⟨f, e, he⟩ := driver_ascii pre .strict pre hp [] (pre.length + 1) 0 [] (by omega)
    have hf : f = 1 := by omega
    subst hf
    have h2 : pre ++ [] = pre := by simp
    rw [h2] at he
    simp only [asciiDecode, he, bind, Except.bind]
    simp [decodeDriver, stepAscii, pure, Except.pure]
  · obtain ⟨f, e, he⟩ := driver_ascii (pre ++ x :: post) .strict pre hp (x :: post)
      ((pre ++ x :: post).length + 1) 0 [] (by simp; omega)
    have hf : f = post.length + 2 := by simp at e; omega
    subst hf
    have hn : ¬ x < 128 := by omega
    simp only [asciiDecode, he, bind, Except.bind]
    simp [decodeDriver, stepAscii, hn, decodeHandlerCall]

/-! ## UTF-7 -/

theorem toBase64_lt (n : Nat) : toBase64 n < 128 := by
  simp only [toBase64]
  have : n % 64 < 64 := Nat.mod_lt _ (by omega)
  repeat' split
  all_goals omega

/-- A string of characters the encoder leaves direct passes through UTF-7 unchanged in both
directions. These are set D, set O and whitespace: ASCII above NUL, minus `+`, `\`, `~` and
the other control characters. -/
def Utf7Direct : Prop :=
  ∀ s : Str, (∀ c ∈ s, encodeDirect c = true ∧ c ≠ 43) →
    utf7Encode s = s ∧ utf7Decode s .strict true = .ok (s, s.length)

theorem u7foldl_direct (s : Str) (out : Bytes) (hs : ∀ c ∈ s, encodeDirect c = true ∧ c ≠ 43) :
    s.foldl (fun p ch => u7EncodeStep p.1 ch p.2) (({} : U7Enc), out) = ({}, out ++ s) := by
  induction s generalizing out with
  | nil => simp
  | cons c cs ih =>
    obtain ⟨h1, h2⟩ := hs c List.mem_cons_self
    have h3 : (c == 43) = false := by simpa using h2
    have e : u7EncodeStep {} c out = ({}, out ++ [c]) := by simp [u7EncodeStep, h3, h1]
    rw [List.foldl_cons]
    show List.foldl _ (u7EncodeStep {} c out) cs = _
    rw [e, ih _ (fun x hx => hs x (List.mem_cons_of_mem _ hx))]
    simp

theorem u7loop_direct (input : Bytes) (h) (consumed : Bool) (s : Str)
    (hs : ∀ c ∈ s, encodeDirect c = true ∧ c ≠ 43) (fuel pos : Nat) (out : Str)
    (hf : s.length < fuel) :
    utf7Loop input h consumed fuel pos s {} out = .ok (out ++ s, {}, pos + s.length) := by
  induction s generalizing fuel pos out with
  | nil =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [utf7Loop]
  | cons c cs ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [List.length_cons] at hf
      obtain ⟨h1, h2⟩ := hs c List.mem_cons_self
      have h3 : (c == 43) = false := by simpa using h2
      have h4 : decodeDirect c = true := by
        simp only [encodeDirect, Bool.and_eq_true, decide_eq_true_eq] at h1
        simp only [decodeDirect, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
        exact ⟨by omega, h2⟩
      simp only [utf7Loop, u7Step, h3, h4, Bool.false_eq_true, if_false, if_true]
      simp only [List.drop_succ_cons, List.drop_zero]
      rw [ih (fun x hx => hs x (List.mem_cons_of_mem _ hx)) fuel _ _ (by omega)]
      simp [Nat.add_assoc, Nat.add_comm 1]

theorem utf7Direct_proven : Utf7Direct := by
  intro s hs
  constructor
  · have := u7foldl_direct s [] hs
    simp only [List.nil_append] at this
    simp [utf7Encode, this]
  · unfold utf7Decode
    cases hn : s with
    | nil => simp
    | cons c cs =>
      subst hn
      have := u7loop_direct (c :: cs) .strict false (c :: cs) hs
        (3 * (c :: cs).length + 3) 0 [] (by omega)
      have e1 : (c :: cs).isEmpty = false := rfl
      simp only [e1, Bool.false_eq_true, if_false, Bool.not_true]
      rw [this]
      simp

/-- Every string encodes to UTF-7, and the result decodes back, for strings of scalar values. -/
def Utf7RoundTrip : Prop :=
  ∀ s : Str, Str.Valid s → (∀ c ∈ s, isSurrogate c = false) →
    utf7Decode (utf7Encode s) .strict true = .ok (s, (utf7Encode s).length)

end PyLean.UnicodeObj
