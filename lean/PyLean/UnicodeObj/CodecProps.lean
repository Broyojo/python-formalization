import PyLean.UnicodeObj.CodecUtf8

/-!
The UTF-8 encoder's error paths, codecs.h:300-395, and properties of the UTF-8 codec.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- `\xHH`, `\uHHHH` or `\UHHHHHHHH`, the character of a `UnicodeEncodeError` message. -/
def escapeEncodeChar (c : Nat) : Str :=
  if c ≤ 0xff then [92, 120] ++ hexDigits 2 c
  else if c ≤ 0xffff then [92, 117] ++ hexDigits 4 c
  else [92, 85] ++ hexDigits 8 c

/-- `UnicodeEncodeError.__str__`, Objects/exceptions.c. -/
def encodeError (encoding : String) (input : Str) (start stop : Nat) (reason : String) : PyExc :=
  if stop = start + 1 then
    .named "UnicodeEncodeError"
      s!"'{encoding}' codec can't encode character '{toLeanString (escapeEncodeChar (input.getD start 0))}' in position {start}: {reason}"
  else
    .named "UnicodeEncodeError"
      s!"'{encoding}' codec can't encode characters in position {start}-{stop - 1}: {reason}"

/-- The longest prefix of surrogates: the run `startpos`..`endpos` of codecs.h:309-312. -/
def surrogateRun : List Nat → List Nat × List Nat
  | [] => ([], [])
  | c :: cs =>
    if isSurrogate c then
      let (a, b) := surrogateRun cs
      (c :: a, b)
    else ([], c :: cs)

/-- `xmlcharrefreplace`, unicodeobject.c:917-971: `&#NNN;`. -/
def xmlRef (c : Nat) : List Nat := [38, 35] ++ digitsDec c ++ [59]
where
  digitsDec (n : Nat) : List Nat := (Nat.toDigits 10 n).map Char.toNat

/-- `STRINGLIB(utf8_encoder)`, codecs.h:260-470. `pos` is the index of `rest` in `input`. -/
def utf8EncodeLoop (input : Str) (h : ErrHandler) : Nat → Nat → List Nat → List Nat → Py (List Nat)
  | 0, _, _, _ => .error .modelFuel
  | _ + 1, _, [], out => .ok out
  | fuel + 1, pos, c :: cs, out =>
    if !isSurrogate c then
      utf8EncodeLoop input h fuel (pos + 1) cs (out ++ utf8EncodeChar c)
    else
      let (run, after) := surrogateRun (c :: cs)
      let stopAt := pos + run.length
      let go (w : List Nat) := utf8EncodeLoop input h fuel stopAt after (out ++ w)
      let fail (start : Nat) : Py (List Nat) :=
        .error (encodeError "utf-8" input start stopAt "surrogates not allowed")
      match h with
      | .replace => go (List.replicate run.length 63)
      | .ignore => go []
      | .surrogatepass => go (run.flatMap utf8EncodeChar)
      | .backslashreplace => go (run.flatMap escapeEncodeChar)
      | .xmlcharrefreplace => go (run.flatMap xmlRef)
      | .surrogateescape =>
        -- `k` stops at the first character outside DC80..DCFF
        match run.findIdx? (fun x => !(decide (0xDC80 ≤ x) && decide (x ≤ 0xDCFF))) with
        | none => go (run.map (· - 0xdc00))
        | some k => fail (pos + k)
      | _ => fail pos

/-- `unicode_encode_utf8` for `s.encode('utf-8', errors)`. -/
def utf8Encode (s : Str) (h : ErrHandler) : Py (List Nat) :=
  utf8EncodeLoop s h (s.length + 1) 0 s []

/-! ## Rejection of overlong forms and surrogates -/

/-- The decoder rejects what Table 3-7 and RFC 3629 forbid, whatever follows: `C0`, `C1`
and `F5..FF` as lead bytes, overlong three- and four-byte forms, encoded surrogates, and
sequences above U+10FFFF. For all bytes `b2`, `b3`, `b4`. -/
def Utf8RejectsForbidden : Prop :=
  (∀ a rest, (a = 0xC0 ∨ a = 0xC1 ∨ (0xF5 ≤ a)) → utf8Step (a :: rest) = .err 1) ∧
  (∀ b2 b3 rest, b2 < 0xA0 → utf8Step (0xE0 :: b2 :: b3 :: rest) = .err 2) ∧
  (∀ b2 b3 rest, 0xA0 ≤ b2 → utf8Step (0xED :: b2 :: b3 :: rest) = .err 2) ∧
  (∀ b2 b3 b4 rest, b2 < 0x90 → utf8Step (0xF0 :: b2 :: b3 :: b4 :: rest) = .err 2) ∧
  (∀ b2 b3 b4 rest, 0x90 ≤ b2 → utf8Step (0xF4 :: b2 :: b3 :: b4 :: rest) = .err 2)

theorem utf8RejectsForbidden_proven : Utf8RejectsForbidden := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a rest h
    rcases h with rfl | rfl | h
    · rfl
    · rfl
    · simp only [utf8Step]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · intro b2 b3 rest h
    simp only [utf8Step]
    rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)]
    simp [step3, isCont, h]
  · intro b2 b3 rest h
    simp only [utf8Step]
    rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)]
    simp [step3, isCont, h]
  · intro b2 b3 b4 rest h
    simp only [utf8Step]
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]
    simp [step4, isCont, h]
  · intro b2 b3 b4 rest h
    simp only [utf8Step]
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]
    simp [step4, isCont, h]

/-- The strict decoder accepts exactly the well-formed sequences of Table 3-7. -/
def Utf8StrictIffWellFormed : Prop :=
  ∀ b : Bytes, Bytes.Valid b →
    ((∃ s, utf8Decode b .strict = .ok s) ↔ utf8Wf (b.length + 1) b = true)

/-- `surrogateescape` round-trips every byte string through decode and encode. -/
def SurrogateEscapeRoundTrip : Prop :=
  ∀ b : Bytes, Bytes.Valid b → ∃ s, utf8Decode b .surrogateescape = .ok s ∧
    utf8Encode s .surrogateescape = .ok b

/-- Encoding then decoding gives the string back, for every string with no surrogate. -/
def Utf8RoundTrip : Prop :=
  ∀ s : Str, Str.Valid s → (∀ c ∈ s, isSurrogate c = false) →
    utf8Decode (s.flatMap utf8EncodeChar) .strict = .ok s

end PyLean.UnicodeObj
