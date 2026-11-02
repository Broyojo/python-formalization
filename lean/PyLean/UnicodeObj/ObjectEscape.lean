import PyLean.UnicodeObj.ObjectChunksCodecs

/-!
The part of `_PyUnicode_DecodeUnicodeEscapeInternal2`, unicodeobject.c:6522-6769, that `decodeDriverX`
leaves out, and what its callers do with it: the first invalid escape, which
`_PyUnicode_DecodeUnicodeEscapeStateful`, :6772-6808, turns into a `DeprecationWarning` once the text
is decoded. That warning is an exception when warnings are errors, so it is a failure path of the
decoder, after a decode that worked.

`*first_invalid_escape_ptr` is set only while `starts == initial_starts`. Every call of a handler
moves `starts`, since `*input` then points into the exception's own copy of the bytes, so the
position is lost after the first handler call even if the handler did nothing to the object.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- `*first_invalid_escape_char` and `*first_invalid_escape_ptr` as an offset. -/
structure EscInfo where
  char : Int := -1
  pos : Option Nat := none
  deriving Repr, DecidableEq

/-- What one round of the loop records: an octal escape above `0377`, :6733-6741, or an escape with
no meaning, the `default:` at :6833-6840. -/
def escInvalid : List Nat → Option Nat
  | 92 :: e :: r =>
    if e == 10 || e == 92 || e == 39 || e == 34 || e == 98 || e == 102 || e == 116 || e == 110 ||
        e == 114 || e == 118 || e == 97 then none
    else if 48 ≤ e ∧ e ≤ 55 then
      let ch := (octalEscape (e - 48) r).1
      if ch > 255 then some ch else none
    else if e == 120 || e == 117 || e == 85 || e == 78 then none
    else some e
  | _ => none

/-- The first one stays. `s - 3` after three digits and `s - 1` after one character are both the byte
after the backslash. -/
def noteInvalid (w : EscInfo) (rest : List Nat) (pos : Nat) (clean : Bool) : EscInfo :=
  match escInvalid rest with
  | some ch =>
    if w.char = -1 then { char := ch, pos := if clean then some (pos + 1) else none } else w
  | none => w

/-- The loop of `_PyUnicode_DecodeUnicodeEscapeInternal2`. `clean` is `starts == initial_starts`. -/
def escLoopW (names : List Nat → Option Nat) (consumed : Bool) (H : DH) (size : Nat) :
    Nat → Bytes → List DecView → Nat → List Nat → Str → EscInfo → Bool → Py (Str × Nat × EscInfo)
  | 0, _, _, _, _, _, _, _ => .error .modelFuel
  | fuel + 1, input, hist, pos, rest, out, w, clean =>
    let w' := noteInvalid w rest pos clean
    match stepUnicodeEscape names consumed rest with
    | .char c n => escLoopW names consumed H size fuel input hist (pos + n) (rest.drop n) (out ++ [c]) w' clean
    | .multi x n => escLoopW names consumed H size fuel input hist (pos + n) (rest.drop n) (out ++ x) w' clean
    | .stop => .ok (out, stopPos (some size) rest pos, w')
    | .raise e => .error e
    | .fail reason s e =>
      match handlerStep H "unicodeescape" .unknown reason input hist (pos + s) (pos + e) with
      | .error x => .error x
      | .ok (hist', input', rep, newpos) =>
        escLoopW names consumed H size fuel input' hist' newpos (input'.drop newpos) (out ++ rep) w' false

/-- `_PyUnicode_DecodeUnicodeEscapeInternal2`. -/
def escInternal (input : Bytes) (H : DH) (names : List Nat → Option Nat) (final : Bool) (fuel : Nat) :
    Py (Str × Nat × EscInfo) :=
  if input.isEmpty then .ok ([], 0, {})
  else escLoopW names (!final) H input.length fuel input [] 0 input [] {} true

/-- The digits of `%o`. -/
def octalText (c : Nat) : String := String.ofList (Nat.toDigits 8 c)

/-- The two warnings of :6892-6913. -/
def escWarning (ch : Int) : PyExc :=
  if ch > 0xff then
    .named "DeprecationWarning" (s!"\"\\{octalText ch.toNat}\" is an invalid octal escape sequence. " ++
      "Such sequences will not work in the future. ")
  else
    .named "DeprecationWarning" (s!"\"\\{Char.ofNat ch.toNat}\" is an invalid escape sequence. " ++
      "Such sequences will not work in the future. ")

/-- `_PyUnicode_DecodeUnicodeEscapeStateful`, unicodeobject.c:6772-6808, and with `final` true
`PyUnicode_DecodeUnicodeEscape`, :6811-6816. `warnRaises` is whether `PyErr_WarnFormat` fails, which
it does when warnings are errors. -/
def unicodeEscapeStateful (input : Bytes) (H : DH) (names : List Nat → Option Nat) (final warnRaises : Bool)
    (fuel : Nat) : Py (Str × Nat) :=
  match escInternal input H names final fuel with
  | .error e => .error e
  | .ok (s, n, w) =>
    if w.char ≠ -1 ∧ warnRaises = true then .error (escWarning w.char) else .ok (s, n)

theorem escLoopW_tie (names : List Nat → Option Nat) (consumed : Bool) (H : DH) (size : Nat) :
    ∀ (fuel : Nat) (input : Bytes) (hist : List DecView) (pos : Nat) (rest : List Nat) (out : Str)
      (w : EscInfo) (clean : Bool),
      (escLoopW names consumed H size fuel input hist pos rest out w clean).map (fun r => (r.1, r.2.1)) =
        decodeDriverX (stepUnicodeEscape names consumed) H "unicodeescape" .unknown (some size) fuel input
          hist pos rest out := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro input hist pos rest out w clean
    simp only [escLoopW, decodeDriverX]
    cases stepUnicodeEscape names consumed rest with
    | char c n => exact ih ..
    | multi x n => exact ih ..
    | stop => rfl
    | raise e => rfl
    | fail why s e =>
      dsimp only
      cases handlerStep H "unicodeescape" .unknown why input hist (pos + s) (pos + e) with
      | error x => rfl
      | ok r =>
        obtain ⟨hist', input', rep, newpos⟩ := r
        exact ih ..

/-- The internal function is the decoder the rest of the model uses. -/
theorem escInternal_tie (input : Bytes) (H : DH) (names : List Nat → Option Nat) (final : Bool) (fuel : Nat) :
    (escInternal input H names final fuel).map (fun r => (r.1, r.2.1)) =
      unicodeEscapeDecodeX input H names final fuel := by
  unfold escInternal unicodeEscapeDecodeX
  split
  · rfl
  · exact escLoopW_tie ..

theorem note_keep {w : EscInfo} (h : w.char ≠ -1) (rest : List Nat) (pos : Nat) (clean : Bool) :
    noteInvalid w rest pos clean = w := by
  unfold noteInvalid
  cases escInvalid rest with
  | none => rfl
  | some ch => exact if_neg h

/-- Once recorded, the first invalid escape stays, whatever follows and whatever a handler does. -/
theorem esc_keeps (names : List Nat → Option Nat) (consumed : Bool) (H : DH) (size : Nat) :
    ∀ (fuel : Nat) (input : Bytes) (hist : List DecView) (pos : Nat) (rest : List Nat) (out : Str)
      (w : EscInfo) (clean : Bool), w.char ≠ -1 → ∀ r,
      escLoopW names consumed H size fuel input hist pos rest out w clean = .ok r → r.2.2 = w := by
  intro fuel
  induction fuel with
  | zero => intro input hist pos rest out w clean _ r h; cases h
  | succ fuel ih =>
    intro input hist pos rest out w clean hw r h
    simp only [escLoopW, note_keep hw] at h
    cases hs : stepUnicodeEscape names consumed rest with
    | char c n =>
      rw [hs] at h
      exact ih _ _ _ _ _ _ _ hw r h
    | multi x n =>
      rw [hs] at h
      exact ih _ _ _ _ _ _ _ hw r h
    | stop =>
      rw [hs] at h
      cases h
      rfl
    | raise e =>
      rw [hs] at h
      cases h
    | fail why s e =>
      rw [hs] at h
      dsimp only at h
      cases hh : handlerStep H "unicodeescape" .unknown why input hist (pos + s) (pos + e) with
      | error x =>
        rw [hh] at h
        cases h
      | ok q =>
        obtain ⟨hist', input', rep, newpos⟩ := q
        rw [hh] at h
        exact ih _ _ _ _ _ _ _ hw r h

theorem escInvalid_ne {c : Nat} (r : List Nat) (h : c ≠ 92) : escInvalid (c :: r) = none := by
  unfold escInvalid
  split <;> simp_all

/-- `PyUnicode_AsUnicodeEscapeString` writes no invalid escape. -/
theorem escInvalid_char (c : Nat) (r : List Nat) : escInvalid (unicodeEscapeChar c ++ r) = none := by
  unfold unicodeEscapeChar
  by_cases h1 : c < 0x100
  · rw [if_pos h1]
    by_cases h2 : c ≥ 32 ∧ c < 127
    · rw [if_pos h2]
      by_cases h3 : c = 92
      · subst h3
        rfl
      · have h3' : (c != 92) = true := by simpa using h3
        simp only [h3', if_true, List.cons_append, List.nil_append]
        exact escInvalid_ne r h3
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
            rfl
  · rw [if_neg h1]
    by_cases h2 : c < 0x10000
    · rw [if_pos h2]
      rfl
    · rw [if_neg h2]
      rfl

/-- The text of `PyUnicode_AsUnicodeEscapeString` at the head of the input is walked over one
character at a time, with nothing recorded. -/
theorem esc_prefix (names : List Nat → Option Nat) (consumed : Bool) (H : DH) (size : Nat) (input : Bytes)
    (hist : List DecView) (s : Str) (hv : Str.Valid s) (tail : List Nat) :
    ∀ (fuel pos : Nat) (out : Str) (w : EscInfo) (clean : Bool),
      escLoopW names consumed H size (s.length + fuel) input hist pos
          (s.flatMap unicodeEscapeChar ++ tail) out w clean =
        escLoopW names consumed H size fuel input hist (pos + (s.flatMap unicodeEscapeChar).length) tail
          (out ++ s) w clean := by
  induction s with
  | nil => intro fuel pos out w clean; simp
  | cons c cs ih =>
    intro fuel pos out w clean
    have hc : c ≤ maxUnicode := hv c List.mem_cons_self
    have hs : Str.Valid cs := fun x hx => hv x (List.mem_cons_of_mem _ hx)
    have e : (c :: cs).length + fuel = (cs.length + fuel) + 1 := by simp; omega
    rw [e, List.flatMap_cons, List.append_assoc]
    simp only [escLoopW]
    have hn : noteInvalid w (unicodeEscapeChar c ++ (cs.flatMap unicodeEscapeChar ++ tail)) pos clean = w := by
      unfold noteInvalid
      rw [escInvalid_char]
    rw [hn, stepUE_char names consumed c _ hc]
    dsimp only
    rw [List.drop_left, ih hs]
    simp [Nat.add_assoc]

/-- Text from `s.encode('unicode_escape')` has no invalid escape, so it decodes without a warning
even when warnings are errors, for any handler. -/
def UnicodeEscapeClean : Prop :=
  ∀ (s : Str) (H : DH) (names : List Nat → Option Nat) (final : Bool) (fuel : Nat),
    Str.Valid s → s.length < fuel →
    unicodeEscapeStateful (unicodeEscapeEncode s) H names final true fuel =
      .ok (s, (unicodeEscapeEncode s).length)

theorem unicodeEscapeClean_proven : UnicodeEscapeClean := by
  intro s H names final fuel hv hf
  obtain ⟨k, rfl⟩ : ∃ k, fuel = s.length + (k + 1) := ⟨fuel - s.length - 1, by omega⟩
  unfold unicodeEscapeStateful escInternal unicodeEscapeEncode
  by_cases he : (s.flatMap unicodeEscapeChar).isEmpty = true
  · have hn := List.isEmpty_iff.1 he
    rw [if_pos he, hn]
    cases s with
    | nil => simp
    | cons c cs =>
      have := length_flat_pos unicodeEscapeChar unicodeEscapeChar_pos c cs
      rw [hn] at this
      simp at this
  · rw [if_neg he]
    have h := esc_prefix names (!final) H (s.flatMap unicodeEscapeChar).length (s.flatMap unicodeEscapeChar)
      [] s hv [] (k + 1) 0 [] {} true
    simp only [List.append_nil] at h
    rw [h]
    simp [escLoopW, stepUnicodeEscape, stopPos, noteInvalid, escInvalid]

/-- The first invalid escape is the one reported. After any text the encoder could have written, an
escape that records something, octal above `0377` or one with no meaning, is what comes out of the
internal function, with its position, whatever follows it and whatever a handler then does, and it is
the warning of the stateful decoder. That warning is an exception only if warnings are errors, and
it never replaces a failure of the decode, and it changes nothing about a decode when it is not an
exception. `s.length < fuel` is the budget of the model. -/
def UnicodeEscapeWarns : Prop :=
  ∀ (s : Str) (tail : List Nat) (ch : Nat) (H : DH) (names : List Nat → Option Nat) (final : Bool)
    (fuel : Nat), Str.Valid s → s.length < fuel → escInvalid tail = some ch →
    let b := unicodeEscapeEncode s ++ tail
    (∀ r, escInternal b H names final fuel = .ok r →
      r.2.2 = { char := ch, pos := some ((unicodeEscapeEncode s).length + 1) }) ∧
    match unicodeEscapeDecodeX b H names final fuel with
    | .ok r =>
      unicodeEscapeStateful b H names final true fuel = .error (escWarning ch) ∧
        unicodeEscapeStateful b H names final false fuel = .ok r
    | .error e =>
      unicodeEscapeStateful b H names final true fuel = .error e ∧
        unicodeEscapeStateful b H names final false fuel = .error e

theorem esc_tail_ne {tail : List Nat} {ch : Nat} (h : escInvalid tail = some ch) :
    tail ≠ [] := by
  intro e
  rw [e] at h
  cases h

theorem unicodeEscapeWarns_proven : UnicodeEscapeWarns := by
  intro s tail ch H names final fuel hv hf hi
  obtain ⟨k, rfl⟩ : ∃ k, fuel = s.length + (k + 1) := ⟨fuel - s.length - 1, by omega⟩
  have hne : (unicodeEscapeEncode s ++ tail).isEmpty = false := by
    cases ht : unicodeEscapeEncode s ++ tail with
    | nil =>
      have := (List.append_eq_nil_iff.1 ht).2
      exact absurd this (esc_tail_ne hi)
    | cons _ _ => rfl
  have key : ∀ r, escInternal (unicodeEscapeEncode s ++ tail) H names final (s.length + (k + 1)) = .ok r →
      r.2.2 = { char := ch, pos := some ((unicodeEscapeEncode s).length + 1) } := by
    intro r hr
    unfold escInternal at hr
    rw [hne] at hr
    simp only [Bool.false_eq_true, if_false] at hr
    rw [show (unicodeEscapeEncode s ++ tail) = s.flatMap unicodeEscapeChar ++ tail from rfl] at hr
    rw [esc_prefix names (!final) H _ _ [] s hv tail (k + 1) 0 [] {} true] at hr
    simp only [escLoopW] at hr
    have hn : noteInvalid {} tail (0 + (s.flatMap unicodeEscapeChar).length) true =
        { char := ch, pos := some ((unicodeEscapeEncode s).length + 1) } := by
      unfold noteInvalid
      rw [hi]
      simp [unicodeEscapeEncode]
    rw [hn] at hr
    have hw : ({ char := ch, pos := some ((unicodeEscapeEncode s).length + 1) } : EscInfo).char ≠ -1 := by
      show ((ch : Int)) ≠ -1
      omega
    cases hs : stepUnicodeEscape names (!final) tail with
    | char c n =>
      rw [hs] at hr
      exact esc_keeps _ _ _ _ _ _ _ _ _ _ _ _ hw r hr
    | multi x n =>
      rw [hs] at hr
      exact esc_keeps _ _ _ _ _ _ _ _ _ _ _ _ hw r hr
    | stop =>
      rw [hs] at hr
      cases hr
      rfl
    | raise e =>
      rw [hs] at hr
      cases hr
    | fail why a b =>
      rw [hs] at hr
      dsimp only at hr
      cases hh : handlerStep H "unicodeescape" .unknown why (s.flatMap unicodeEscapeChar ++ tail) []
          (0 + (s.flatMap unicodeEscapeChar).length + a) (0 + (s.flatMap unicodeEscapeChar).length + b) with
      | error x =>
        rw [hh] at hr
        cases hr
      | ok q =>
        obtain ⟨hist', input', rep, newpos⟩ := q
        rw [hh] at hr
        exact esc_keeps _ _ _ _ _ _ _ _ _ _ _ _ hw r hr
  refine ⟨key, ?_⟩
  have htie := escInternal_tie (unicodeEscapeEncode s ++ tail) H names final (s.length + (k + 1))
  rw [← htie]
  cases hd : escInternal (unicodeEscapeEncode s ++ tail) H names final (s.length + (k + 1)) with
  | error e => simp [Except.map, unicodeEscapeStateful, hd]
  | ok r =>
    obtain ⟨t, n, w⟩ := r
    have hw := key (t, n, w) hd
    dsimp only at hw
    subst hw
    have hc : (ch : Int) ≠ -1 := by omega
    simp [Except.map, unicodeEscapeStateful, hd]

end PyLean.UnicodeObj
