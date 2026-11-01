import PyLean.UnicodeObj.CodecUtf8
import PyLean.UnicodeObj.CodecWide

/-!
The UTF-8 encoder's error paths, codecs.h:300-395, and properties of the UTF-8 codec.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- The longest prefix of surrogates: the run `startpos`..`endpos` of codecs.h:309-312. -/
def surrogateRun : List Nat → List Nat × List Nat
  | [] => ([], [])
  | c :: cs =>
    if isSurrogate c then
      let (a, b) := surrogateRun cs
      (c :: a, b)
    else ([], c :: cs)

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
      | .backslashreplace | .namereplace => go (run.flatMap escapeEncodeChar)
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

theorem isCont_of {b : Nat} (h1 : 0x80 ≤ b) (h2 : b < 0xC0) : isCont b = true := by
  simp [isCont, h1, h2]

/-- The decoder reads back what the encoder wrote for one scalar value, whatever follows. -/
theorem utf8Step_char (c : Nat) (r : List Nat) (hv : c ≤ maxUnicode)
    (hs : isSurrogate c = false) :
    utf8Step (utf8EncodeChar c ++ r) = .char c (utf8EncodeChar c).length := by
  have hm : maxUnicode = 0x10FFFF := rfl
  simp only [isSurrogate, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hs
  unfold utf8EncodeChar
  by_cases h1 : c < 0x80
  · rw [if_pos h1]
    simp [utf8Step, h1]
  rw [if_neg h1]
  by_cases h2 : c < 0x0800
  · rw [if_pos h2]
    simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
    simp only [utf8Step]
    rw [if_neg (by omega), if_pos (by omega), if_neg (by omega)]
    simp only [step2, isCont_of (b := 0x80 + c % 64) (by omega) (by omega), Bool.not_true,
      Bool.false_eq_true, if_false]
    exact congrArg (fun x => U8.char x 2) (by omega)
  rw [if_neg h2]
  by_cases h3 : c < 0x10000
  · rw [if_pos h3]
    simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
    simp only [utf8Step]
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    simp only [step3, isCont_of (b := 0x80 + c / 64 % 64) (by omega) (by omega),
      isCont_of (b := 0x80 + c % 64) (by omega) (by omega), Bool.not_true, Bool.false_eq_true,
      if_false]
    rw [if_neg (by simp; omega), if_neg (by simp; omega)]
    exact congrArg (fun x => U8.char x 3) (by omega)
  rw [if_neg h3]
  simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
  simp only [utf8Step]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  simp only [step4, isCont_of (b := 0x80 + c / 4096 % 64) (by omega) (by omega),
    isCont_of (b := 0x80 + c / 64 % 64) (by omega) (by omega),
    isCont_of (b := 0x80 + c % 64) (by omega) (by omega), Bool.not_true, Bool.false_eq_true,
    if_false]
  rw [if_neg (by simp; omega), if_neg (by simp; omega)]
  exact congrArg (fun x => U8.char x 4) (by omega)

theorem utf8EncodeChar_ne (c : Nat) : utf8EncodeChar c ≠ [] := by
  unfold utf8EncodeChar
  repeat' split
  all_goals simp

theorem utf8Loop_flatMap (input : Bytes) (h : ErrHandler) (consumed : Bool) (s : Str)
    (hs : ∀ c ∈ s, c ≤ maxUnicode ∧ isSurrogate c = false) (fuel pos : Nat) (out : Str)
    (hf : s.length < fuel) :
    utf8DecodeLoop input h consumed fuel pos (s.flatMap utf8EncodeChar) out =
      .ok (out ++ s, pos + (s.flatMap utf8EncodeChar).length) := by
  induction s generalizing fuel pos out with
  | nil =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [utf8DecodeLoop]
  | cons c cs ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [List.length_cons] at hf
      obtain ⟨h1, h2⟩ := hs c List.mem_cons_self
      have hstep := utf8Step_char c (cs.flatMap utf8EncodeChar) h1 h2
      have hne := utf8EncodeChar_ne c
      simp only [List.flatMap_cons]
      generalize hrest : utf8EncodeChar c ++ cs.flatMap utf8EncodeChar = rest at *
      cases rest with
      | nil =>
        have := List.append_eq_nil_iff.1 hrest
        exact absurd this.1 hne
      | cons b0 tl =>
        simp only [utf8DecodeLoop, hstep]
        rw [← hrest, List.drop_left]
        rw [ih (fun x hx => hs x (List.mem_cons_of_mem _ hx)) fuel _ _ (by omega)]
        simp [Nat.add_assoc]

theorem length_le_flatMap (s : Str) : s.length ≤ (s.flatMap utf8EncodeChar).length := by
  induction s with
  | nil => simp
  | cons c cs ih =>
    have hne := utf8EncodeChar_ne c
    have : 1 ≤ (utf8EncodeChar c).length := List.length_pos_iff.2 hne
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

/-- Encoding then decoding gives the string back, for every string of scalar values, and the
strict encoder succeeds on them. -/
def Utf8RoundTrip : Prop :=
  ∀ s : Str, (∀ c ∈ s, c ≤ maxUnicode ∧ isSurrogate c = false) →
    utf8Encode s .strict = .ok (s.flatMap utf8EncodeChar) ∧
    utf8Decode (s.flatMap utf8EncodeChar) .strict = .ok s

theorem utf8EncodeLoop_plain (input : Str) (h : ErrHandler) (s : Str)
    (hs : ∀ c ∈ s, isSurrogate c = false) (fuel pos : Nat) (out : List Nat) (hf : s.length < fuel) :
    utf8EncodeLoop input h fuel pos s out = .ok (out ++ s.flatMap utf8EncodeChar) := by
  induction s generalizing fuel pos out with
  | nil =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [utf8EncodeLoop]
  | cons c cs ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [List.length_cons] at hf
      have hc := hs c List.mem_cons_self
      simp only [utf8EncodeLoop, hc, Bool.not_false, if_true]
      rw [ih (fun x hx => hs x (List.mem_cons_of_mem _ hx)) fuel _ _ (by omega)]
      simp

theorem utf8RoundTrip_proven : Utf8RoundTrip := by
  intro s hs
  constructor
  · simpa [utf8Encode] using
      utf8EncodeLoop_plain s .strict s (fun c hc => (hs c hc).2) (s.length + 1) 0 [] (by omega)
  · have := utf8Loop_flatMap (s.flatMap utf8EncodeChar) .strict false s hs
      ((s.flatMap utf8EncodeChar).length + 1) 0 [] (by have := length_le_flatMap s; omega)
    simp only [utf8Decode, this, bind, Except.bind, pure, Except.pure]
    simp

end PyLean.UnicodeObj
