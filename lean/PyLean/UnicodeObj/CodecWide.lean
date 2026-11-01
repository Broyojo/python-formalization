import PyLean.UnicodeObj.CodecHandlers

/-!
UTF-16 and UTF-32: `PyUnicode_DecodeUTF16Stateful` (unicodeobject.c:6285-6437),
`_PyUnicode_EncodeUTF16` (:6440-6601), `PyUnicode_DecodeUTF32Stateful` (:5978-6120),
`_PyUnicode_EncodeUTF32` (:6123-6265), with `STRINGLIB(utf16_decode)`, `utf16_encode`
and `utf32_encode` (stringlib/codecs.h:500-828).

Abstractions, each checked by the difftest:
* The aligned long reads and the unrolled loops only move runs of characters that the
  scalar path would move the same way, so one scalar model covers them.
* Byte fields use `/` and `%`, and joined fields `+`, where C uses `>>`, `&` and `|`
  on the same disjoint bits.
* The model is for a little-endian build: `utf-16` and `utf-32` without a BOM are LE.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- One round of a decoder at the head of the remaining input. -/
inductive DStep where
  /-- A character and the bytes it took. -/
  | char (c n : Nat)
  /-- Any number of characters and the bytes they took. -/
  | multi (w : Str) (n : Nat)
  /-- Stop here. -/
  | stop
  /-- An error: `reason`, and `start`, `end` relative to the head. -/
  | fail (reason : String) (start stop : Nat)
  /-- An exception that does not go through the error handler. -/
  | raise (e : PyExc)
  deriving Repr, DecidableEq

/-- The `while (1)` of the UTF-16 and UTF-32 decoders, with the error handler call. -/
def decodeDriver (step : List Nat → DStep) (h : ErrHandler) (enc : String) (code : EncCode)
    (input : Bytes) : Nat → Nat → List Nat → Str → Py (Str × Nat)
  | 0, _, _, _ => .error .modelFuel
  | fuel + 1, pos, rest, out =>
    match step rest with
    | .char c n => decodeDriver step h enc code input fuel (pos + n) (rest.drop n) (out ++ [c])
    | .multi w n => decodeDriver step h enc code input fuel (pos + n) (rest.drop n) (out ++ w)
    | .stop => .ok (out, pos)
    | .raise e => .error e
    | .fail reason s e =>
      match decodeHandlerCall h enc code input (pos + s) (pos + e) reason with
      | .error x => .error x
      | .ok (rep, newpos) =>
        decodeDriver step h enc code input fuel newpos (input.drop newpos) (out ++ rep)

/-- `(q[ihi] << 8) | q[ilo]`. -/
def unit16 (le : Bool) (a b : Nat) : Nat := if le then b * 256 + a else a * 256 + b

def isHighSurrogate (c : Nat) : Bool := decide (0xD800 ≤ c) && decide (c ≤ 0xDBFF)
def isLowSurrogate (c : Nat) : Bool := decide (0xDC00 ≤ c) && decide (c ≤ 0xDFFF)

/-- `Py_UNICODE_JOIN_SURROGATES`. -/
def joinSurrogates (hi lo : Nat) : Nat := 0x10000 + (hi % 1024) * 1024 + lo % 1024

/-- One round of `STRINGLIB(utf16_decode)` and the `switch (ch)` after it,
codecs.h:500-612 and unicodeobject.c:6364-6407. -/
def step16 (le consumed : Bool) : List Nat → DStep
  | [] => .stop
  | [_] => if consumed then .stop else .fail "truncated data" 0 1
  | a :: b :: t =>
    let ch := unit16 le a b
    if !isSurrogate ch then .char ch 2
    else if !isHighSurrogate ch then .fail "illegal encoding" 0 2
    else
      match t with
      | c :: d :: _ =>
        let ch2 := unit16 le c d
        if !isLowSurrogate ch2 then .fail "illegal UTF-16 surrogate" 0 2
        else .char (joinSurrogates ch ch2) 4
      | _ =>
        if consumed then .stop else .fail "unexpected end of data" 0 (2 + t.length)

/-- The body of the UTF-32 decoder's loop, unicodeobject.c:6049-6104. -/
def step32 (le consumed : Bool) : List Nat → DStep
  | a :: b :: c :: d :: _ =>
    let ch := if le then d * 16777216 + c * 65536 + b * 256 + a
      else a * 16777216 + b * 65536 + c * 256 + d
    if isSurrogate ch then
      .fail "code point in surrogate code point range(0xd800, 0xe000)" 0 4
    else if ch < 0x110000 then .char ch 4
    else .fail "code point not in range(0x110000)" 0 4
  | [] => .stop
  | rest => if consumed then .stop else .fail "truncated data" 0 rest.length

/-- The BOM check of the UTF-16 decoder, unicodeobject.c:6308-6321. -/
def bom16 (bo : Int) (b : Bytes) : Int × Nat :=
  match b with
  | a :: c :: _ =>
    if bo = 0 then
      let bom := c * 256 + a
      if bom = 0xFEFF then (-1, 2) else if bom = 0xFFFE then (1, 2) else (bo, 0)
    else (bo, 0)
  | _ => (bo, 0)

/-- The BOM check of the UTF-32 decoder, unicodeobject.c:6002-6016. -/
def bom32 (bo : Int) (b : Bytes) : Int × Nat :=
  match b with
  | a :: c :: d :: e :: _ =>
    if bo = 0 then
      let bom := e * 16777216 + d * 65536 + c * 256 + a
      if bom = 0x0000FEFF then (-1, 4) else if bom = 0xFFFE0000 then (1, 4) else (bo, 0)
    else (bo, 0)
  | _ => (bo, 0)

/-- `PyUnicode_DecodeUTF16Stateful`, unicodeobject.c:6285-6437. `final = false` is
`consumed != NULL`. Returns the text and the bytes consumed. -/
def utf16DecodeFull (input : Bytes) (bo : Int) (h : ErrHandler) (final : Bool) : Py (Str × Nat) :=
  let (bo, q) := bom16 bo input
  let rest := input.drop q
  if rest.isEmpty then .ok ([], input.length)
  else
    let le := decide (bo ≤ 0)
    decodeDriver (step16 le !final) h (if le then "utf-16-le" else "utf-16-be")
      (if le then .utf16le else .utf16be) input (input.length + 1) q rest []

/-- `PyUnicode_DecodeUTF32Stateful`, unicodeobject.c:5978-6120. -/
def utf32DecodeFull (input : Bytes) (bo : Int) (h : ErrHandler) (final : Bool) : Py (Str × Nat) :=
  let (bo, q) := bom32 bo input
  let rest := input.drop q
  if rest.isEmpty then .ok ([], input.length)
  else
    let le := decide (bo ≤ 0)
    decodeDriver (step32 le !final) h (if le then "utf-32-le" else "utf-32-be")
      (if le then .utf32le else .utf32be) input (input.length + 1) q rest []

/-- Two bytes of a code unit, in the output's byte order. -/
def unitBytes (le : Bool) (u : Nat) : List Nat :=
  if le then [u % 256, u / 256 % 256] else [u / 256 % 256, u % 256]

/-- `Py_UNICODE_HIGH_SURROGATE` and `Py_UNICODE_LOW_SURROGATE`. -/
def highSurrogate (c : Nat) : Nat := 0xD800 - (0x10000 / 1024) + c / 1024
def lowSurrogate (c : Nat) : Nat := 0xDC00 + c % 1024

/-- The bytes `STRINGLIB(utf16_encode)` writes for one character, codecs.h:620-740. -/
def utf16Char (le : Bool) (c : Nat) : List Nat :=
  if c < 0x10000 then unitBytes le c
  else unitBytes le (highSurrogate c) ++ unitBytes le (lowSurrogate c)

/-- The bytes `STRINGLIB(utf32_encode)` writes for one character, codecs.h:757-828. -/
def utf32Char (le : Bool) (c : Nat) : List Nat :=
  if le then [c % 256, c / 256 % 256, c / 65536 % 256, c / 16777216 % 256]
  else [c / 16777216 % 256, c / 65536 % 256, c / 256 % 256, c % 256]

/-- The `while (pos < len)` of `_PyUnicode_EncodeUTF16` and `_PyUnicode_EncodeUTF32`,
unicodeobject.c:6524-6585 and :6174-6248. `unitSize` is 2 or 4. A `bytes` replacement must
be a whole number of units and a `str` one must be ASCII, and each str character is
written as a character. -/
def encodeWideLoop (charBytes : Nat → List Nat) (unitSize : Nat) (h : ErrHandler)
    (nameOf : Nat → Option Str) (enc : String) (code : EncCode) (input : Str) :
    Nat → Nat → List Nat → Bytes → Py Bytes
  | 0, _, _, _ => .error .modelFuel
  | _ + 1, _, [], out => .ok out
  | fuel + 1, pos, c :: cs, out =>
    if !isSurrogate c then
      encodeWideLoop charBytes unitSize h nameOf enc code input fuel (pos + 1) cs (out ++ charBytes c)
    else
      let reason := "surrogates not allowed"
      match encodeHandlerCall h nameOf enc code input pos (pos + 1) reason with
      | .error e => .error e
      | .ok (rep, newpos) =>
        let bad := encodeError enc input pos (pos + 1) reason
        let next := fun (w : Bytes) =>
          encodeWideLoop charBytes unitSize h nameOf enc code input fuel newpos
            (input.drop newpos) (out ++ w)
        match rep with
        | .bytes b => if b.length % unitSize != 0 then .error bad else next b
        | .str r =>
          if !(r.all (· < 128)) then .error bad else next (r.flatMap charBytes)

/-- `_PyUnicode_EncodeUTF16`, unicodeobject.c:6440-6601. `byteorder` is -1, 0 or 1. -/
def utf16EncodeFull (s : Str) (byteorder : Int) (h : ErrHandler) (nameOf : Nat → Option Str) :
    Py Bytes :=
  let le := decide (byteorder ≤ 0)
  let enc := if byteorder < 0 then "utf-16-le" else if byteorder > 0 then "utf-16-be" else "utf-16"
  let bom := if byteorder = 0 then unitBytes le 0xFEFF else []
  encodeWideLoop (utf16Char le) 2 h nameOf enc (if le then .utf16le else .utf16be) s
    (s.length + 1) 0 s bom

/-- `_PyUnicode_EncodeUTF32`, unicodeobject.c:6123-6265. -/
def utf32EncodeFull (s : Str) (byteorder : Int) (h : ErrHandler) (nameOf : Nat → Option Str) :
    Py Bytes :=
  let le := decide (byteorder ≤ 0)
  let enc := if byteorder = -1 then "utf-32-le" else if byteorder = 1 then "utf-32-be" else "utf-32"
  let bom := if byteorder = 0 then utf32Char le 0xFEFF else []
  encodeWideLoop (utf32Char le) 4 h nameOf enc (if le then .utf32le else .utf32be) s
    (s.length + 1) 0 s bom

/-! ## Round trips -/

/-- A general fact about the driver: when `step` decodes each encoded character and stops
on empty input, the driver returns the characters. -/
theorem decodeDriver_flatMap (step : List Nat → DStep) (enc : Nat → List Nat) (h e code input)
    (s : Str) (hstop : step [] = .stop)
    (hstep : ∀ c ∈ s, ∀ r, step (enc c ++ r) = .char c (enc c).length)
    (fuel pos : Nat) (out : Str) (hf : s.length < fuel) :
    decodeDriver step h e code input fuel pos (s.flatMap enc) out =
      .ok (out ++ s, pos + (s.flatMap enc).length) := by
  induction s generalizing fuel pos out with
  | nil =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [decodeDriver, hstop]
  | cons c cs ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [List.length_cons] at hf
      simp only [List.flatMap_cons, decodeDriver, hstep c List.mem_cons_self]
      rw [List.drop_left]
      rw [ih (fun x hx => hstep x (List.mem_cons_of_mem _ hx)) fuel _ _ (by omega)]
      simp [Nat.add_assoc]

/-- A scalar value: a valid code point that is not a surrogate. -/
def Scalar (s : Str) : Prop := Str.Valid s ∧ ∀ c ∈ s, isSurrogate c = false

theorem encodeWide_plain (charBytes : Nat → List Nat) (u h nameOf e code input) (s : Str)
    (hs : ∀ c ∈ s, isSurrogate c = false) (fuel pos : Nat) (out : Bytes) (hf : s.length < fuel) :
    encodeWideLoop charBytes u h nameOf e code input fuel pos s out =
      .ok (out ++ s.flatMap charBytes) := by
  induction s generalizing fuel pos out with
  | nil =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [encodeWideLoop]
  | cons c cs ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [List.length_cons] at hf
      have hc := hs c List.mem_cons_self
      simp only [encodeWideLoop, hc, Bool.not_false, if_true]
      rw [ih (fun x hx => hs x (List.mem_cons_of_mem _ hx)) fuel _ _ (by omega)]
      simp

theorem step32_char (le : Bool) (cons : Bool) (c : Nat) (r : List Nat) (hv : c ≤ maxUnicode)
    (hs : isSurrogate c = false) : step32 le cons (utf32Char le c ++ r) = .char c 4 := by
  have hm : maxUnicode = 0x10FFFF := rfl
  simp only [isSurrogate, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hs
  cases le
  · simp only [utf32Char, Bool.false_eq_true, if_false, List.cons_append, List.nil_append, step32]
    have e : c / 16777216 % 256 * 16777216 + c / 65536 % 256 * 65536 + c / 256 % 256 * 256 +
        c % 256 = c := by omega
    rw [e]
    simp only [isSurrogate]
    have h1 : (decide (0xD800 ≤ c) && decide (c ≤ 0xDFFF)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; exact hs
    simp [h1]
    omega
  · simp only [utf32Char, if_true, List.cons_append, List.nil_append, step32]
    have e : c / 16777216 % 256 * 16777216 + c / 65536 % 256 * 65536 + c / 256 % 256 * 256 +
        c % 256 = c := by omega
    rw [e]
    simp only [isSurrogate]
    have h1 : (decide (0xD800 ≤ c) && decide (c ≤ 0xDFFF)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; exact hs
    simp [h1]
    omega

/-- Encoding to UTF-32 and decoding with the same `byteorder` gives the string back, for
every string of scalar values, in all three byte orders (the BOM form included), and
consumes everything. -/
def Utf32RoundTrip : Prop :=
  ∀ (s : Str) (bo : Int) (nameOf : Nat → Option Str), Scalar s → (bo = -1 ∨ bo = 0 ∨ bo = 1) →
    ∃ b, utf32EncodeFull s bo .strict nameOf = .ok b ∧
      utf32DecodeFull b bo .strict true = .ok (s, b.length)

theorem utf32Char_length (le : Bool) (c : Nat) : (utf32Char le c).length = 4 := by
  cases le <;> simp [utf32Char]

theorem length_le_flat (enc : Nat → List Nat) (hl : ∀ c, 1 ≤ (enc c).length) (s : Str) :
    s.length ≤ (s.flatMap enc).length := by
  induction s with
  | nil => simp
  | cons c cs ih =>
    have := hl c
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem utf32RoundTrip_proven : Utf32RoundTrip := by
  intro s bo nameOf hsc hbo
  obtain ⟨hv, hs⟩ := hsc
  generalize hle : decide (bo ≤ 0) = le
  have hlen := length_le_flat (utf32Char le) (fun c => by rw [utf32Char_length]; omega) s
  have henc := fun bom e code =>
    encodeWide_plain (utf32Char le) 4 .strict nameOf e code s s hs (s.length + 1) 0 bom (by omega)
  have hstop : step32 le false [] = .stop := rfl
  have hstep : ∀ c ∈ s, ∀ r, step32 le false (utf32Char le c ++ r) =
      .char c (utf32Char le c).length := by
    intro c hc r
    rw [utf32Char_length]
    exact step32_char le false c r (hv c hc) (hs c hc)
  have hdrv := fun e code input fuel pos hf =>
    decodeDriver_flatMap (step32 le false) (utf32Char le) .strict e code input s hstop hstep
      fuel pos [] hf
  simp only [List.nil_append] at hdrv
  refine ⟨(if bo = 0 then utf32Char le 0xFEFF else []) ++ s.flatMap (utf32Char le), ?_, ?_⟩
  · simp only [utf32EncodeFull, hle]
    exact henc _ _ _
  · have hb : bom32 bo ((if bo = 0 then utf32Char le 0xFEFF else []) ++ s.flatMap (utf32Char le)) =
        (if bo = 0 then -1 else bo, if bo = 0 then 4 else 0) := by
      rcases hbo with rfl | rfl | rfl
      · cases s.flatMap (utf32Char le) with
        | nil => rfl
        | cons _ t => simp [bom32]; split <;> rfl
      · have : le = true := by simpa using hle.symm
        subst this
        simp [bom32, utf32Char]
      · cases s.flatMap (utf32Char le) with
        | nil => rfl
        | cons _ t => simp [bom32]; split <;> rfl
    have hle2 : decide ((if bo = 0 then (-1 : Int) else bo) ≤ 0) = le := by
      rw [← hle]; rcases hbo with rfl | rfl | rfl <;> rfl
    have hdrop : ((if bo = 0 then utf32Char le 0xFEFF else []) ++ s.flatMap (utf32Char le)).drop
        (if bo = 0 then 4 else 0) = s.flatMap (utf32Char le) := by
      by_cases h : bo = 0
      · simp only [h, if_true]
        exact List.drop_left' (utf32Char_length le 0xFEFF)
      · simp [h]
    simp only [utf32DecodeFull, hb, hdrop, hle2]
    cases hsl : s with
    | nil => simp
    | cons c cs =>
      have hne : ((c :: cs).flatMap (utf32Char le)).isEmpty = false := by
        cases le <;> simp [utf32Char]
      subst hsl
      simp only [hne, Bool.false_eq_true, if_false, Bool.not_true]
      have hl : (c :: cs).length ≤ ((c :: cs).flatMap (utf32Char le)).length := hlen
      rw [hdrv _ _ _ _ _ (by simp only [List.length_append]; omega)]
      congr 2
      · by_cases h : bo = 0
        · simp only [h, if_true, List.length_append, utf32Char_length]
        · simp [h]

/-! ## UTF-16 -/

theorem unit_bytes (le : Bool) (u : Nat) (hu : u < 65536) :
    ∃ a b, unitBytes le u = [a, b] ∧ unit16 le a b = u := by
  cases le
  · refine ⟨_, _, rfl, ?_⟩
    simp only [unit16, Bool.false_eq_true, if_false]
    omega
  · refine ⟨_, _, rfl, ?_⟩
    simp only [unit16, if_true]
    omega

theorem step16_char (le cons : Bool) (c : Nat) (r : List Nat) (hv : c ≤ maxUnicode)
    (hs : isSurrogate c = false) :
    step16 le cons (utf16Char le c ++ r) = .char c (utf16Char le c).length := by
  have hm : maxUnicode = 0x10FFFF := rfl
  by_cases h : c < 0x10000
  · obtain ⟨a, b, h1, h2⟩ := unit_bytes le c h
    simp only [utf16Char, h, if_true, h1, List.cons_append, List.nil_append, List.length_cons,
      List.length_nil, step16, h2, hs, Bool.not_false]
  · have hh : highSurrogate c < 65536 := by simp only [highSurrogate]; omega
    have hl : lowSurrogate c < 65536 := by simp only [lowSurrogate]; omega
    obtain ⟨a, b, h1, h2⟩ := unit_bytes le _ hh
    obtain ⟨x, y, h3, h4⟩ := unit_bytes le _ hl
    have a1 : 0xD800 ≤ highSurrogate c := by simp only [highSurrogate]; omega
    have a2 : highSurrogate c ≤ 0xDBFF := by simp only [highSurrogate]; omega
    have a3 : 0xDC00 ≤ lowSurrogate c := by simp only [lowSurrogate]; omega
    have a4 : lowSurrogate c ≤ 0xDFFF := by simp only [lowSurrogate]; omega
    have s1 : isSurrogate (highSurrogate c) = true := by
      have a5 : highSurrogate c ≤ 0xDFFF := by omega
      simp [isSurrogate, a1, a5]
    have s2 : isHighSurrogate (highSurrogate c) = true := by simp [isHighSurrogate, a1, a2]
    have s3 : isLowSurrogate (lowSurrogate c) = true := by simp [isLowSurrogate, a3, a4]
    have s4 : joinSurrogates (highSurrogate c) (lowSurrogate c) = c := by
      simp only [joinSurrogates, highSurrogate, lowSurrogate]; omega
    simp only [utf16Char, h, if_false, h1, h3, List.cons_append, List.nil_append, List.length_cons,
      List.length_nil, step16, h2, h4, s1, s2, s3, s4, Bool.not_true, Bool.false_eq_true]

theorem utf16Char_pos (le : Bool) (c : Nat) : 1 ≤ (utf16Char le c).length := by
  cases le <;> simp only [utf16Char, unitBytes] <;> split <;> simp

/-- Encoding to UTF-16 and decoding with the same `byteorder` gives the string back, for
every string of scalar values, surrogate pairs included, in all three byte orders (the BOM
form included), and consumes everything. -/
def Utf16RoundTrip : Prop :=
  ∀ (s : Str) (bo : Int) (nameOf : Nat → Option Str), Scalar s → (bo = -1 ∨ bo = 0 ∨ bo = 1) →
    ∃ b, utf16EncodeFull s bo .strict nameOf = .ok b ∧
      utf16DecodeFull b bo .strict true = .ok (s, b.length)

theorem utf16RoundTrip_proven : Utf16RoundTrip := by
  intro s bo nameOf hsc hbo
  obtain ⟨hv, hs⟩ := hsc
  generalize hle : decide (bo ≤ 0) = le
  have hlen := length_le_flat (utf16Char le) (utf16Char_pos le) s
  have henc := fun bom e code =>
    encodeWide_plain (utf16Char le) 2 .strict nameOf e code s s hs (s.length + 1) 0 bom (by omega)
  have hstop : step16 le false [] = .stop := rfl
  have hstep : ∀ c ∈ s, ∀ r, step16 le false (utf16Char le c ++ r) =
      .char c (utf16Char le c).length :=
    fun c hc r => step16_char le false c r (hv c hc) (hs c hc)
  have hdrv := fun e code input fuel pos hf =>
    decodeDriver_flatMap (step16 le false) (utf16Char le) .strict e code input s hstop hstep
      fuel pos [] hf
  simp only [List.nil_append] at hdrv
  have hbl : (unitBytes le 0xFEFF).length = 2 := by cases le <;> simp [unitBytes]
  refine ⟨(if bo = 0 then unitBytes le 0xFEFF else []) ++ s.flatMap (utf16Char le), ?_, ?_⟩
  · simp only [utf16EncodeFull, hle]
    exact henc _ _ _
  · have hb : bom16 bo ((if bo = 0 then unitBytes le 0xFEFF else []) ++ s.flatMap (utf16Char le)) =
        (if bo = 0 then -1 else bo, if bo = 0 then 2 else 0) := by
      rcases hbo with rfl | rfl | rfl
      · cases s.flatMap (utf16Char le) with
        | nil => rfl
        | cons _ t => simp [bom16]; split <;> rfl
      · have : le = true := by simpa using hle.symm
        subst this
        simp [bom16, unitBytes]
      · cases s.flatMap (utf16Char le) with
        | nil => rfl
        | cons _ t => simp [bom16]; split <;> rfl
    have hle2 : decide ((if bo = 0 then (-1 : Int) else bo) ≤ 0) = le := by
      rw [← hle]; rcases hbo with rfl | rfl | rfl <;> rfl
    have hdrop : ((if bo = 0 then unitBytes le 0xFEFF else []) ++ s.flatMap (utf16Char le)).drop
        (if bo = 0 then 2 else 0) = s.flatMap (utf16Char le) := by
      by_cases h : bo = 0
      · simp only [h, if_true]
        exact List.drop_left' hbl
      · simp [h]
    simp only [utf16DecodeFull, hb, hdrop, hle2]
    cases hsl : s with
    | nil => simp
    | cons c cs =>
      have hne : ((c :: cs).flatMap (utf16Char le)).isEmpty = false := by
        have h1 : 1 ≤ ((c :: cs).flatMap (utf16Char le)).length := by
          simp only [List.flatMap_cons, List.length_append]
          have := utf16Char_pos le c
          omega
        cases hl : (c :: cs).flatMap (utf16Char le) with
        | nil =>
          rw [hl] at h1
          simp at h1
        | cons _ _ => rfl
      subst hsl
      simp only [hne, Bool.false_eq_true, if_false, Bool.not_true]
      have hl : (c :: cs).length ≤ ((c :: cs).flatMap (utf16Char le)).length := hlen
      rw [hdrv _ _ _ _ _ (by simp only [List.length_append]; omega)]
      congr 2
      · by_cases h : bo = 0
        · simp only [h, if_true, List.length_append, hbl]
        · simp [h]

/-! ## The handlers advance -/

/-- Every standard handler, on a decode error with `start < end`, returns a position past
`start`, so no decoder loop can repeat forever. For all inputs and all encodings. -/
def DecodeHandlerAdvances : Prop :=
  ∀ h enc code input start stop reason rep newpos, start < stop →
    decodeHandlerCall h enc code input start stop reason = .ok (rep, newpos) → start < newpos

theorem bytelength_pos {code : EncCode} (h : code ≠ .unknown) : 0 < code.bytelength := by
  cases code <;> first | decide | exact absurd rfl h

theorem decodeHandlerAdvances_proven : DecodeHandlerAdvances := by
  intro h enc code input start stop reason rep newpos hlt he
  cases h <;> simp only [decodeHandlerCall] at he
  case strict | xmlcharrefreplace | namereplace => cases he
  case ignore | replace | backslashreplace =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at he
    omega
  case surrogateescape =>
    split at he
    · cases he
    · rename_i hne
      simp only [Except.ok.injEq, Prod.mk.injEq] at he
      have : 0 < (escapeRun 4 ((input.drop start).take (stop - start))).length := by
        cases hr : escapeRun 4 ((input.drop start).take (stop - start)) with
        | nil => simp [hr] at hne
        | cons _ _ => simp
      omega
  case surrogatepass =>
    split at he
    · cases he
    · rename_i hc
      have hu : code ≠ .unknown := by
        intro e; subst e; simp at hc
      have hb := bytelength_pos hu
      repeat' split at he
      all_goals first | (cases he; omega) | cases he

/-- The same for encode errors: `newpos` is `end`, past `start`. -/
def EncodeHandlerAdvances : Prop :=
  ∀ h nameOf enc code input start stop reason rep newpos, start < stop →
    encodeHandlerCall h nameOf enc code input start stop reason = .ok (rep, newpos) →
    start < newpos

theorem encodeHandlerAdvances_proven : EncodeHandlerAdvances := by
  intro h nameOf enc code input start stop reason rep newpos hlt he
  cases h <;> simp only [encodeHandlerCall] at he
  case strict => cases he
  case ignore | replace | backslashreplace | xmlcharrefreplace | namereplace =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at he
    omega
  case surrogatepass | surrogateescape =>
    split at he <;> cases he <;> exact hlt

end PyLean.UnicodeObj
