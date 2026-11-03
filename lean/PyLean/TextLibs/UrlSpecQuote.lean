import PyLean.TextLibs.UrlLegacy

/-!
`quote`, `quote_plus` and `quote_from_bytes` against the escape written out in full: a byte that
is neither in `_ALWAYS_SAFE` (spelled out as its 66 characters) nor in `safe` becomes `%` and two
upper-case hex digits. And their error paths: a character the codec cannot write, and `encoding`
or `errors` given with `bytes`.
-/

namespace PyLean.TextLibs.Url

open PyLean
open PyLean.UnicodeObj (ErrHandler isSurrogate)

set_option linter.unusedSimpArgs false

/-- `_ALWAYS_SAFE`, :992-995, as the literal it is built from. -/
def alwaysSafeSet : Str := cs "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_.-~"

/-- The digits `'%{:02X}'.format(b)` writes. -/
def hexUpper : Str := cs "0123456789ABCDEF"

/-- What `quote` writes for one byte, per its docstring: the byte itself when it is always safe
or in `safe`, and otherwise `%` with two upper-case hex digits. -/
def quoteSpec (sb : Str) (b : Nat) : Str :=
  if b ∈ alwaysSafeSet ∨ b ∈ sb then [b] else [37, hexUpper.getD (b / 16) 0, hexUpper.getD (b % 16) 0]

set_option maxRecDepth 20000 in
theorem alwaysSafeSet_lt : ∀ c ∈ alwaysSafeSet, c < 128 := by decide

set_option maxRecDepth 20000 in
theorem alwaysSafe_iff (c : Nat) : alwaysSafe c = true ↔ c ∈ alwaysSafeSet := by
  by_cases hc : c < 128
  · have key : ∀ c < 128, (alwaysSafe c = true ↔ c ∈ alwaysSafeSet) := by decide
    exact key c hc
  · constructor
    · intro h; exact absurd (alwaysSafe_lt c h) hc
    · intro h; exact absurd (alwaysSafeSet_lt c h) hc

set_option maxRecDepth 20000 in
theorem hexU_upper (d : Nat) (h : d < 16) : hexU d = hexUpper.getD d 0 := by
  have key : ∀ d < 16, hexU d = hexUpper.getD d 0 := by decide
  exact key d h

theorem quoteByte_spec (sb : Str) (b : Nat) (hb : b < 256) : quoteByte sb b = quoteSpec sb b := by
  unfold quoteByte quoteSpec
  by_cases h1 : b ∈ alwaysSafeSet ∨ b ∈ sb
  · rw [if_pos h1, if_pos]
    rcases h1 with h | h
    · simp [(alwaysSafe_iff b).2 h]
    · simp [h]
  · rw [if_neg h1, if_neg, hexU_upper _ (by omega), hexU_upper _ (by omega)]
    intro h
    rcases Bool.or_eq_true _ _ ▸ h with h | h
    · exact h1 (Or.inl ((alwaysSafe_iff b).1 h))
    · exact h1 (Or.inr (List.contains_iff_mem.1 h))

theorem flatMap_quoteSpec (sb x : Str) (hx : ∀ b ∈ x, b < 256) :
    x.flatMap (quoteByte sb) = x.flatMap (quoteSpec sb) := by
  induction x with
  | nil => rfl
  | cons b r ih =>
    simp only [List.flatMap_cons, quoteByte_spec sb b (hx b List.mem_cons_self),
      ih (fun c hc => hx c (List.mem_cons_of_mem _ hc))]

/-! ## Strict encoders raise on the first character they cannot write -/

theorem encodeError_class (e : String) (s : Str) (a b : Nat) (r : String) :
    (UnicodeObj.encodeError e s a b r).className = "UnicodeEncodeError" := by
  unfold UnicodeObj.encodeError; split <;> rfl

theorem ucs1_strict_raises (input : Str) (limit : Nat) (nameOf : Nat → Option Str) :
    ∀ (cs : Str) (fuel pos : Nat) (out : Str), cs.length < fuel → (∃ c ∈ cs, limit ≤ c) →
      (UnicodeObj.ucs1EncodeLoop input limit .strict nameOf fuel pos cs out).raises "UnicodeEncodeError"
  | [], _, _, _, _, ⟨c, hc, _⟩ => by simp at hc
  | c :: cs, fuel + 1, pos, out, hl, hex => by
    unfold UnicodeObj.ucs1EncodeLoop
    by_cases hc : c < limit
    · rw [if_pos hc]
      apply ucs1_strict_raises input limit nameOf cs fuel _ _ (by simp at hl; omega)
      obtain ⟨d, hd, hld⟩ := hex
      rcases List.mem_cons.1 hd with rfl | hd
      · omega
      · exact ⟨d, hd, hld⟩
    · rw [if_neg hc]
      exact ⟨_, rfl, encodeError_class _ _ _ _ _⟩
  | _ :: _, 0, _, _, hl, _ => by simp at hl

theorem utf8_strict_raises (input : Str) :
    ∀ (cs : Str) (fuel pos : Nat) (out : Str), cs.length < fuel → (∃ c ∈ cs, isSurrogate c = true) →
      (UnicodeObj.utf8EncodeLoop input .strict fuel pos cs out).raises "UnicodeEncodeError"
  | [], _, _, _, _, ⟨c, hc, _⟩ => by simp at hc
  | c :: cs, fuel + 1, pos, out, hl, hex => by
    unfold UnicodeObj.utf8EncodeLoop
    by_cases hc : isSurrogate c = true
    · rw [if_neg (by simp [hc])]
      exact ⟨_, rfl, encodeError_class _ _ _ _ _⟩
    · rw [if_pos (by simpa using hc)]
      apply utf8_strict_raises input cs fuel _ _ (by simp at hl; omega)
      obtain ⟨d, hd, hld⟩ := hex
      rcases List.mem_cons.1 hd with rfl | hd
      · exact absurd hld hc
      · exact ⟨d, hd, hld⟩
  | _ :: _, 0, _, _, hl, _ => by simp at hl

/-- A character `encoding` cannot write: a surrogate for UTF-8, a code point from 128 for ASCII,
from 256 for Latin-1. -/
def Enc.unfit : Enc → Nat → Bool
  | .utf8, c => isSurrogate c
  | .ascii, c => decide (128 ≤ c)
  | .latin1, c => decide (256 ≤ c)

theorem encodeWith_strict_raises (e : Enc) (s : Str) (hs : ∃ c ∈ s, e.unfit c = true) :
    (encodeWith e .strict s).raises "UnicodeEncodeError" := by
  cases e with
  | utf8 => exact utf8_strict_raises s s _ 0 [] (by omega) hs
  | ascii =>
    obtain ⟨c, hc, h⟩ := hs
    exact ucs1_strict_raises s 128 noNames s _ 0 [] (by omega) ⟨c, hc, by simpa [Enc.unfit] using h⟩
  | latin1 =>
    obtain ⟨c, hc, h⟩ := hs
    exact ucs1_strict_raises s 256 noNames s _ 0 [] (by omega) ⟨c, hc, by simpa [Enc.unfit] using h⟩

theorem raises_bind {α β : Type} (x : Py α) (f : α → Py β) (cls : String) (h : x.raises cls) :
    (x >>= f).raises cls := by
  obtain ⟨e, he, hc⟩ := h
  exact ⟨e, by rw [he]; rfl, hc⟩

/-! ## The property -/

/-- For every `bytes` or `bytearray` and every `str` or `bytes` `safe`, `quote_from_bytes` (on
each of its three paths), `quote` and `quote_plus` write each byte as itself when it is one of
the 66 always-safe characters or in `safe`'s ASCII part, and otherwise as `%` followed by two
upper-case hex digits; `quote_plus` on `bytes` with a space first adds `b' '` to `safe` and then
turns spaces into `+`. `quote` on a `bytes` refuses `encoding` and then `errors` with their
`TypeError`s. On a non-empty `str` (with a `str` or `bytes` `safe`), `quote` and `quote_plus` raise `UnicodeEncodeError` when the
encoding (UTF-8 when `None`) cannot write a character and `errors` is `None` or `'strict'`; with
`errors='ignore'` the ASCII and Latin-1 codecs drop those characters. `bytes` values are below
256 (a type invariant). Source: the docstrings of `quote` ("%-escapes all characters that are
neither in the unreserved chars ... nor the additional chars set via the safe arg"; "errors='strict'
(unsupported characters raise a UnicodeEncodeError)"; "encoding and errors must not be specified if
string is a bytes object"), of `quote_plus` and of `quote_from_bytes`; RFC 3986 section 2.1
("should use uppercase hexadecimal digits"). -/
def QuoteSpec : Prop :=
  (∀ (x : Str) (ba : Bool) (safe : Arg) (sb : Str), safeBytes safe = some sb → (∀ b ∈ x, b < 256) →
    quoteFromBytes (.bytes x ba) safe = .ok (x.flatMap (quoteSpec sb)) ∧
    quote (.bytes x ba) safe none none = .ok (x.flatMap (quoteSpec sb))) ∧
  (∀ (x : Str) (safe : Arg) (sb : Str), safeBytes safe = some sb → (∀ b ∈ x, b < 256) →
    quotePlus (.bytes x false) safe none none =
      .ok (if 32 ∈ x then spToPlus (x.flatMap (quoteSpec (sb ++ [32]))) else x.flatMap (quoteSpec sb))) ∧
  (∀ (x : Str) (ba : Bool) (safe : Arg) (e : Enc) (h : Option ErrHandler),
    quote (.bytes x ba) safe (some e) h = .error (.typeError "quote() doesn't support 'encoding' for bytes")) ∧
  (∀ (x : Str) (ba : Bool) (safe : Arg) (h : ErrHandler),
    quote (.bytes x ba) safe none (some h) = .error (.typeError "quote() doesn't support 'errors' for bytes")) ∧
  (∀ (s : Str) (safe : Arg) (sb : Str) (e : Option Enc) (h : Option ErrHandler), safeBytes safe = some sb →
    s ≠ [] → (∃ c ∈ s, (e.getD .utf8).unfit c = true) → (h = none ∨ h = some .strict) →
    (quote (.str s) safe e h).raises "UnicodeEncodeError" ∧
    (quotePlus (.str s) safe e h).raises "UnicodeEncodeError") ∧
  (∀ (s : Str) (safe : Arg) (sb : Str), safeBytes safe = some sb →
    quote (.str s) safe (some .ascii) (some .ignore) = .ok ((s.filter (· < 128)).flatMap (quoteSpec sb)) ∧
    quote (.str s) safe (some .latin1) (some .ignore) = .ok ((s.filter (· < 256)).flatMap (quoteSpec sb)))

theorem quote_str_raises (s : Str) (safe : Arg) (e : Option Enc) (h : Option ErrHandler) (hne : s ≠ [])
    (hu : ∃ c ∈ s, (e.getD .utf8).unfit c = true) (hh : h = none ∨ h = some .strict) :
    (quote (.str s) safe e h).raises "UnicodeEncodeError" := by
  have hs : s.isEmpty = false := by cases s <;> simp_all
  have hg : h.getD .strict = .strict := by rcases hh with rfl | rfl <;> rfl
  simp only [quote, hs, Bool.false_eq_true, ite_false, hg]
  exact raises_bind _ _ _ (encodeWith_strict_raises _ s hu)

theorem filter_lt (s : Str) (n : Nat) (hn : n ≤ 256) : ∀ b ∈ s.filter (fun c => decide (c < n)), b < 256 := by
  intro b hb; simp at hb; omega

theorem quoteSpec_proven : QuoteSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x ba safe sb hs hx
    have h1 := quoteFromBytes_eq x ba safe sb hs
    rw [flatMap_quoteSpec sb x hx] at h1
    exact ⟨h1, by simp only [quote]; exact h1⟩
  · intro x safe sb hs hx
    unfold quotePlus
    by_cases h32 : 32 ∈ x
    · obtain ⟨safe2, e2, hs2⟩ := safeBytes_space safe sb hs
      have hq : quote (.bytes x false) safe2 none none = .ok (x.flatMap (quoteSpec (sb ++ [32]))) := by
        simp only [quote, Option.isSome_none, Bool.false_eq_true, ite_false]
        rw [quoteFromBytes_eq x false safe2 _ hs2, flatMap_quoteSpec _ x hx]
      simp only [show x.contains 32 = true by simpa using h32, Bool.not_true, Bool.false_eq_true,
        ite_false, bind, Except.bind, e2, hq, pure, Except.pure, if_pos h32]
      rfl
    · have hq : quote (.bytes x false) safe none none = .ok (x.flatMap (quoteSpec sb)) := by
        simp only [quote, Option.isSome_none, Bool.false_eq_true, ite_false]
        rw [quoteFromBytes_eq x false safe _ hs, flatMap_quoteSpec _ x hx]
      simp only [show x.contains 32 = false by simpa using h32, Bool.not_false, ite_true, if_neg h32]
      exact hq
  · intro x ba safe e h; rfl
  · intro x ba safe h; rfl
  · intro s safe sb e h hs hne hu hh
    refine ⟨quote_str_raises s safe e h hne hu hh, ?_⟩
    unfold quotePlus
    by_cases h32 : s.contains 32 = true
    · obtain ⟨safe2, e2, _⟩ := safeBytes_space safe sb hs
      simp only [h32, Bool.not_true, Bool.false_eq_true, ite_false, e2, bind, Except.bind]
      exact raises_bind _ _ _ (quote_str_raises s _ e h hne hu hh)
    · simp only [Bool.not_eq_true] at h32
      simp only [h32, Bool.not_false, ite_true]
      exact quote_str_raises s safe e h hne hu hh
  · intro s safe sb hs
    have hsa := safeBytes_ascii safe sb hs
    constructor
    · by_cases he : s.isEmpty = true
      · have : s = [] := List.isEmpty_iff.1 he
        subst this; rfl
      · simp only [quote, he, Bool.false_eq_true, ite_false, Option.getD_some, encodeWith,
          ucs1Encode_ignore, bind, Except.bind]
        rw [quoteFromBytes_eq _ false safe sb hs, flatMap_quoteSpec _ _ (filter_lt s 128 (by omega))]
    · by_cases he : s.isEmpty = true
      · have : s = [] := List.isEmpty_iff.1 he
        subst this; rfl
      · simp only [quote, he, Bool.false_eq_true, ite_false, Option.getD_some, encodeWith,
          ucs1Encode_ignore, bind, Except.bind]
        rw [quoteFromBytes_eq _ false safe sb hs, flatMap_quoteSpec _ _ (filter_lt s 256 (by omega))]

end PyLean.TextLibs.Url
