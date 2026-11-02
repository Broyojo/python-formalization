import PyLean.UnicodeObj.ObjectEscape

/-!
The failure paths of the two escape decoders and what the two encoders write.

`UnicodeEscapeRoundTrip` and `RawEscapeRoundTrip` run the decoders over text with no error in it. A
decoder that accepted everything, or an encoder that copied bytes, would pass them. So the failing
escapes get their own statements, and the encoders theirs.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- Text an encoder wrote is walked over one character at a time, for any handler. -/
theorem driverX_prefix (step : List Nat → DStep) (enc : Nat → List Nat) (H : DH) (e : String)
    (code : EncCode) (atEnd : Option Nat) (input : Bytes) (hist : List DecView) (s : Str)
    (hstep : ∀ c ∈ s, ∀ r, step (enc c ++ r) = .char c (enc c).length) (tail : List Nat) :
    ∀ (fuel pos : Nat) (out : Str),
      decodeDriverX step H e code atEnd (s.length + fuel) input hist pos (s.flatMap enc ++ tail) out =
        decodeDriverX step H e code atEnd fuel input hist (pos + (s.flatMap enc).length) tail (out ++ s) := by
  induction s with
  | nil => intro fuel pos out; simp
  | cons c cs ih =>
    intro fuel pos out
    have el : (c :: cs).length + fuel = (cs.length + fuel) + 1 := by simp; omega
    rw [el, List.flatMap_cons, List.append_assoc]
    simp only [decodeDriverX]
    rw [hstep c List.mem_cons_self]
    dsimp only
    rw [List.drop_left, ih (fun x hx r => hstep x (List.mem_cons_of_mem _ hx) r)]
    simp [Nat.add_assoc]

/-- A `strict` decode stops at the first escape that fails, with the span and the reason of that
escape, measured in the whole input, after any text the encoder could have written. -/
def UnicodeEscapeFailsAt : Prop :=
  ∀ (s : Str) (tail : List Nat) (names : List Nat → Option Nat) (final : Bool) (why : String)
    (a b fuel : Nat), Str.Valid s → s.length < fuel →
    stepUnicodeEscape names (!final) tail = .fail why a b →
    let bs := unicodeEscapeEncode s ++ tail
    let n := (unicodeEscapeEncode s).length
    unicodeEscapeDecodeX bs (.std .strict) names final fuel =
      .error (decodeError "unicodeescape" bs (n + a) (n + b) why)

theorem unicodeEscapeFailsAt_proven : UnicodeEscapeFailsAt := by
  intro s tail names final why a b fuel hv hf hs
  obtain ⟨k, rfl⟩ : ∃ k, fuel = s.length + (k + 1) := ⟨fuel - s.length - 1, by omega⟩
  have hne : (unicodeEscapeEncode s ++ tail).isEmpty = false := by
    cases ht : unicodeEscapeEncode s ++ tail with
    | nil =>
      have h0 := (List.append_eq_nil_iff.1 ht).2
      rw [h0] at hs
      cases hs
    | cons _ _ => rfl
  dsimp only
  simp only [unicodeEscapeDecodeX, hne, Bool.false_eq_true, if_false]
  have hp := driverX_prefix (stepUnicodeEscape names !final) unicodeEscapeChar (.std .strict) "unicodeescape"
    .unknown (some (unicodeEscapeEncode s ++ tail).length) (unicodeEscapeEncode s ++ tail) [] s
    (fun c hc r => stepUE_char names (!final) c r (hv c hc)) tail (k + 1) 0 []
  rw [show unicodeEscapeEncode s ++ tail = s.flatMap unicodeEscapeChar ++ tail from rfl] at *
  rw [hp]
  simp only [decodeDriverX, hs, handlerStep, decodeHandlerCall, Nat.zero_add, unicodeEscapeEncode]

/-- What each escape does when it cannot be read: the spans and reasons of
unicodeobject.c:6696-6831. The span of a failed hex escape stops at the first byte that is not a hex
digit, so a handler that resumes there reads that byte again. `hexValue d = none` is what makes it
fail. In the `consumed` form an incomplete escape stops instead, which `Chunked` covers. -/
def UnicodeEscapeFailures : Prop :=
  ∀ (names : List Nat → Option Nat) (c : Bool) (r : List Nat) (d : Nat),
    (hexValue d = none →
      stepUnicodeEscape names c (92 :: 120 :: d :: r) = .fail "truncated \\xXX escape" 0 2 ∧
      stepUnicodeEscape names c (92 :: 117 :: d :: r) = .fail "truncated \\uXXXX escape" 0 2 ∧
      stepUnicodeEscape names c (92 :: 85 :: d :: r) = .fail "truncated \\UXXXXXXXX escape" 0 2) ∧
    stepUnicodeEscape names false [92] = .fail "\\ at end of string" 0 1 ∧
    stepUnicodeEscape names false [92, 120] = .fail "truncated \\xXX escape" 0 2 ∧
    stepUnicodeEscape names false [92, 78] = .fail "malformed \\N character escape" 0 2 ∧
    (d ≠ 123 → stepUnicodeEscape names c (92 :: 78 :: d :: r) =
      .fail "malformed \\N character escape" 0 2) ∧
    stepUnicodeEscape names c (92 :: 78 :: 123 :: 125 :: r) =
      .fail "malformed \\N character escape" 0 3 ∧
    (d ≠ 125 → names [d] = none → stepUnicodeEscape names c (92 :: 78 :: 123 :: d :: 125 :: r) =
      .fail "unknown Unicode character name" 0 5) ∧
    stepUnicodeEscape names c (92 :: 85 :: 48 :: 48 :: 49 :: 49 :: 48 :: 48 :: 48 :: 48 :: r) =
      .fail "illegal Unicode character" 0 10

theorem unicodeEscapeFailures_proven : UnicodeEscapeFailures := by
  intro names c r d
  refine ⟨?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro hd
    refine ⟨?_, ?_, ?_⟩
    all_goals
      simp only [stepUnicodeEscape]
      show stepHex _ _ _ _ = _
      simp [stepHex, hexEscape, hd]
  · intro hd
    exact stepName_other names c r hd
  · rfl
  · intro hd hn
    have h1 : nameBytes [d, 125] = some [d] := by
      rw [name_cons hd]
      rfl
    have hb : nameBytes (d :: 125 :: r) = some [d] := by
      have := (nameBytes_app [d, 125] r [d] h1).1
      simpa using this
    show stepName names c (123 :: d :: 125 :: r) = _
    simp [stepName, hb, hn]
  · show stepHex c 8 "truncated \\UXXXXXXXX escape" (48 :: 48 :: 49 :: 49 :: 48 :: 48 :: 48 :: 48 :: r) = _
    rfl

/-- The same walk for `raw_unicode_escape`, whose text has no backslash. -/
def RawEscapeFailsAt : Prop :=
  ∀ (s : Str) (tail : List Nat) (final : Bool) (why : String) (a b fuel : Nat),
    Str.Valid s → (∀ c ∈ s, c ≠ 92) → s.length < fuel →
    stepRawEscape (!final) tail = .fail why a b →
    let bs := rawEscapeEncode s ++ tail
    let n := (rawEscapeEncode s).length
    rawEscapeDecodeX bs (.std .strict) final fuel =
      .error (decodeError "rawunicodeescape" bs (n + a) (n + b) why)

theorem rawEscapeFailsAt_proven : RawEscapeFailsAt := by
  intro s tail final why a b fuel hv h92 hf hs
  obtain ⟨k, rfl⟩ : ∃ k, fuel = s.length + (k + 1) := ⟨fuel - s.length - 1, by omega⟩
  have hne : (rawEscapeEncode s ++ tail).isEmpty = false := by
    cases ht : rawEscapeEncode s ++ tail with
    | nil =>
      have h0 := (List.append_eq_nil_iff.1 ht).2
      rw [h0] at hs
      cases hs
    | cons _ _ => rfl
  dsimp only
  simp only [rawEscapeDecodeX, hne, Bool.false_eq_true, if_false]
  have hp := driverX_prefix (stepRawEscape !final) rawEscapeChar (.std .strict) "rawunicodeescape"
    .unknown (some (rawEscapeEncode s ++ tail).length) (rawEscapeEncode s ++ tail) [] s
    (fun c hc r => stepRaw_char (!final) c r (hv c hc) (h92 c hc)) tail (k + 1) 0 []
  rw [show rawEscapeEncode s ++ tail = s.flatMap rawEscapeChar ++ tail from rfl] at *
  rw [hp]
  simp only [decodeDriverX, hs, handlerStep, decodeHandlerCall, Nat.zero_add, rawEscapeEncode]

/-- What the raw decoder does with a backslash, unicodeobject.c:6971-7025: at the very end of the
input it is itself, before anything but `u` or `U` it is itself and the next byte, and the two escapes
fail like their twins, except that a value above U+10FFFF has its own message. -/
def RawEscapeFailures : Prop :=
  ∀ (c : Bool) (r : List Nat) (d e : Nat),
    stepRawEscape false [92] = .char 92 1 ∧
    (e ≠ 117 → e ≠ 85 → stepRawEscape c (92 :: e :: r) = .multi [92, e] 2) ∧
    (hexValue d = none →
      stepRawEscape c (92 :: 117 :: d :: r) = .fail "truncated \\uXXXX escape" 0 2 ∧
      stepRawEscape c (92 :: 85 :: d :: r) = .fail "truncated \\UXXXXXXXX escape" 0 2) ∧
    stepRawEscape c (92 :: 85 :: 48 :: 48 :: 49 :: 49 :: 48 :: 48 :: 48 :: 48 :: r) =
      .fail "\\Uxxxxxxxx out of range" 0 10

theorem rawEscapeFailures_proven : RawEscapeFailures := by
  intro c r d e
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro h1 h2
    have b1 : (e == 117) = false := by simpa using h1
    have b2 : (e == 85) = false := by simpa using h2
    simp [stepRawEscape, b1, b2]
  · intro hd
    constructor
    all_goals
      simp only [stepRawEscape]
      show rawHex _ _ _ _ = _
      simp [rawHex, hexEscape, hd]
  · show rawHex c 8 "truncated \\UXXXXXXXX escape" (48 :: 48 :: 49 :: 49 :: 48 :: 48 :: 48 :: 48 :: r) = _
    rfl

theorem hexLower_print (d : Nat) (h : d < 16) : 32 ≤ hexLower d ∧ hexLower d < 127 := by
  simp only [hexLower]
  split <;> omega

theorem hex2_print (c x : Nat) (h : x ∈ hex2 c) : 32 ≤ x ∧ x < 127 := by
  simp only [hex2, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact hexLower_print _ (Nat.mod_lt _ (by omega))
  · exact hexLower_print _ (Nat.mod_lt _ (by omega))

theorem hex4_print (c x : Nat) (h : x ∈ hex4 c) : 32 ≤ x ∧ x < 127 := by
  simp only [hex4, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with (rfl | rfl) | h
  · exact hexLower_print _ (Nat.mod_lt _ (by omega))
  · exact hexLower_print _ (Nat.mod_lt _ (by omega))
  · exact hex2_print c x h

theorem hex8_print (c x : Nat) (h : x ∈ hex8 c) : 32 ≤ x ∧ x < 127 := by
  simp only [hex8, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with (rfl | rfl | rfl | rfl) | h
  · decide
  · decide
  · exact hexLower_print _ (Nat.mod_lt _ (by omega))
  · exact hexLower_print _ (Nat.mod_lt _ (by omega))
  · exact hex4_print c x h

/-- Every byte `PyUnicode_AsUnicodeEscapeString` writes is printable ASCII, for every string. That is
what the round trip does not say: a decoder takes a raw `é` as U+00E9, so an encoder that copied it
would still round-trip. -/
def UnicodeEscapePrintable : Prop :=
  ∀ s : Str, ∀ b ∈ unicodeEscapeEncode s, 32 ≤ b ∧ b < 127

theorem unicodeEscapePrintable_proven : UnicodeEscapePrintable := by
  intro s b hb
  simp only [unicodeEscapeEncode, List.mem_flatMap] at hb
  obtain ⟨c, _, hc⟩ := hb
  unfold unicodeEscapeChar at hc
  split at hc
  · split at hc
    · split at hc
      · simp only [List.mem_singleton] at hc
        omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        omega
    · split at hc
      · simp at hc
        omega
      · split at hc
        · simp at hc
          omega
        · split at hc
          · simp at hc
            omega
          · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with (rfl | rfl) | hc
            · decide
            · decide
            · exact hex2_print c b hc
  · split at hc
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with (rfl | rfl) | hc
      · decide
      · decide
      · exact hex4_print c b hc
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with (rfl | rfl) | hc
      · decide
      · decide
      · exact hex8_print c b hc

/-- `PyUnicode_AsRawUnicodeEscapeString`: Latin-1 text is copied, which is its one-byte branch, and any
other text gets the Latin-1 characters copied and the rest written as printable ASCII. So every byte
above 126 in the output is a character of the input, unchanged. `Str.Valid` is the type invariant. -/
def RawEscapeEncodeSpec : Prop :=
  ∀ s : Str,
    ((∀ c ∈ s, c < 256) → rawEscapeEncode s = s) ∧
    ∀ c ∈ s, 256 ≤ c → ∀ b ∈ rawEscapeChar c, 32 ≤ b ∧ b < 127

theorem rawEscapeEncodeSpec_proven : RawEscapeEncodeSpec := by
  intro s
  constructor
  · intro h
    induction s with
    | nil => rfl
    | cons c cs ih =>
      have hc := h c List.mem_cons_self
      have e : rawEscapeChar c = [c] := if_pos hc
      simp only [rawEscapeEncode, List.flatMap_cons, e, List.singleton_append]
      exact congrArg (c :: ·) (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))
  · intro c _ hc b hb
    unfold rawEscapeChar at hb
    rw [if_neg (by omega)] at hb
    split at hb
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with (rfl | rfl) | hb
      · decide
      · decide
      · exact hex4_print c b hb
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with (rfl | rfl) | hb
      · decide
      · decide
      · exact hex8_print c b hb

end PyLean.UnicodeObj
