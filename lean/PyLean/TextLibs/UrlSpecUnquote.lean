import PyLean.TextLibs.UrlSpecQuote

/-!
`unquote`, `unquote_to_bytes` and `_unquote_impl` on every input: the left-to-right reading
`scan` (a `%` followed by two hex digits is that byte, every other character, including a `%`
that does not start such an escape, is kept), non-ASCII characters of a `str` kept as they are
between the decoded ASCII runs, and the error paths.
-/

namespace PyLean.TextLibs.Url

open PyLean
open PyLean.UnicodeObj (ErrHandler isSurrogate)

set_option linter.unusedSimpArgs false

/-! ## `_generate_unquoted_parts` -/

theorem dropWhile_length_le (p : Nat → Bool) (l : Str) : (l.dropWhile p).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons c r ih => simp only [List.dropWhile_cons]; split <;> simp <;> omega

theorem dropWhile_lt_of_head (p : Nat → Bool) (c : Nat) (r : Str) (hc : p c = true) :
    ((c :: r).dropWhile p).length < (c :: r).length := by
  simp only [List.dropWhile_cons, hc, ite_true]
  have := dropWhile_length_le p r
  simp; omega

theorem dropWhile_cons_head {p : Nat → Bool} : ∀ {s : Str} {c : Nat} {r : Str}, s.dropWhile p = c :: r → p c = false
  | [], c, r, h => by simp at h
  | x :: s, c, r, h => by
    rw [List.dropWhile_cons] at h
    split at h
    · exact dropWhile_cons_head h
    · next hx => cases h; simpa using hx

/-- The fuel of `genParts` does not matter once it exceeds the length. -/
theorem genParts_fuel (e : Enc) (h : ErrHandler) :
    ∀ (n : Nat) (s : Str) (f1 f2 : Nat), s.length < n → s.length < f1 → s.length < f2 →
      genParts e h f1 s = genParts e h f2 s := by
  intro n
  induction n with
  | zero => intro s _ _ h; omega
  | succ n ih =>
    intro s f1 f2 hn h1 h2
    obtain ⟨f1, rfl⟩ : ∃ k, f1 = k + 1 := ⟨f1 - 1, by omega⟩
    obtain ⟨f2, rfl⟩ : ∃ k, f2 = k + 1 := ⟨f2 - 1, by omega⟩
    simp only [genParts]
    split
    · rfl
    · next hr =>
      have hlen : ((s.dropWhile (· ≥ 128)).dropWhile (· < 128)).length < s.length := by
        generalize hd : s.dropWhile (· ≥ 128) = rest at hr
        obtain ⟨c, r, rfl⟩ : ∃ c r, rest = c :: r := by
          cases rest with
          | nil => simp at hr
          | cons c r => exact ⟨c, r, rfl⟩
        have h1 := dropWhile_length_le (· ≥ 128) s
        rw [hd] at h1
        have hc : decide (c < 128) = true := by
          have := dropWhile_cons_head hd
          simp at this ⊢; omega
        have := dropWhile_lt_of_head (· < 128) c r hc
        omega
      rw [ih _ f1 f2 (by omega) (by omega) (by omega)]

/-- `G s`: `''.join(_generate_unquoted_parts(s, ...))` with enough fuel. -/
def G (e : Enc) (h : ErrHandler) (s : Str) : Py Str := genParts e h (s.length + 1) s

theorem G_eq (e : Enc) (h : ErrHandler) (s : Str) (f : Nat) (hf : s.length < f) :
    genParts e h f s = G e h s :=
  genParts_fuel e h (s.length + 1) s f _ (by omega) hf (by omega)

theorem G_nil (e : Enc) (h : ErrHandler) : G e h [] = .ok [] := rfl

theorem takeWhile_ge_cons (c : Nat) (s : Str) (hc : 128 ≤ c) :
    (c :: s).takeWhile (· ≥ 128) = c :: s.takeWhile (· ≥ 128) := by
  simp [List.takeWhile_cons, hc]

theorem dropWhile_ge_cons (c : Nat) (s : Str) (hc : 128 ≤ c) :
    (c :: s).dropWhile (· ≥ 128) = s.dropWhile (· ≥ 128) := by
  simp [List.dropWhile_cons, hc]

theorem genParts_high (e : Enc) (h : ErrHandler) (f c : Nat) (s : Str) (hc : 128 ≤ c) :
    genParts e h (f + 1) (c :: s) = (genParts e h (f + 1) s).map (c :: ·) := by
  simp only [genParts, takeWhile_ge_cons c s hc, dropWhile_ge_cons c s hc]
  by_cases hr : (s.dropWhile (· ≥ 128)).isEmpty = true
  · simp [hr, Except.map]
  · simp only [hr, Bool.false_eq_true, ite_false]
    cases unquoteImpl _ with
    | error z => rfl
    | ok u =>
      simp only [bind, Except.bind]
      cases decodeWith e h u with
      | error z => rfl
      | ok d =>
        simp only
        cases genParts e h f _ with
        | error z => rfl
        | ok t => simp [pure, Except.pure, Except.map]

/-- A non-ASCII character is yielded as it is, :830. -/
theorem G_high (e : Enc) (h : ErrHandler) (c : Nat) (s : Str) (hc : 128 ≤ c) :
    G e h (c :: s) = (G e h s).map (c :: ·) := by
  show genParts e h (s.length + 1 + 1) (c :: s) = _
  rw [genParts_high e h _ c s hc, G_eq e h s _ (by omega)]

theorem takeWhile_lt_app (a b : Str) (c : Nat) (hc : 128 ≤ c) :
    (a ++ c :: b).takeWhile (· < 128) = a.takeWhile (· < 128) := by
  induction a with
  | nil => simp [List.takeWhile_cons]; omega
  | cons x r ih =>
    simp only [List.cons_append, List.takeWhile_cons]
    split
    · rw [ih]
    · rfl

theorem dropWhile_lt_app (a b : Str) (c : Nat) (hc : 128 ≤ c) :
    (a ++ c :: b).dropWhile (· < 128) = a.dropWhile (· < 128) ++ c :: b := by
  induction a with
  | nil => simp [List.dropWhile_cons]; omega
  | cons x r ih =>
    simp only [List.cons_append, List.dropWhile_cons]
    split
    · rw [ih]
    · rfl

theorem genParts_low (e : Enc) (h : ErrHandler) (f x : Nat) (s : Str) (hx : x < 128) :
    genParts e h (f + 1) (x :: s) = (do
      let u ← unquoteImpl (.str ((x :: s).takeWhile (· < 128)))
      let d ← decodeWith e h u
      let t ← genParts e h f ((x :: s).dropWhile (· < 128))
      pure (d ++ t)) := by
  have hg : (x :: s).takeWhile (· ≥ 128) = [] := by simp [List.takeWhile_cons]; omega
  have hd : (x :: s).dropWhile (· ≥ 128) = x :: s := by simp [List.dropWhile_cons]; omega
  simp only [genParts, hg, hd, List.isEmpty_cons, Bool.false_eq_true, ite_false, List.nil_append]

/-- An ASCII character starts a run that is decoded, :831-833. -/
theorem G_low (e : Enc) (h : ErrHandler) (x : Nat) (s : Str) (hx : x < 128) :
    G e h (x :: s) = (do
      let u ← unquoteImpl (.str ((x :: s).takeWhile (· < 128)))
      let d ← decodeWith e h u
      let t ← G e h ((x :: s).dropWhile (· < 128))
      pure (d ++ t)) := by
  have hlt := dropWhile_lt_of_head (· < 128) x s (by simpa using hx)
  show genParts e h (s.length + 1 + 1) (x :: s) = _
  rw [genParts_low e h _ x s hx, G_eq e h _ _ (by simp at hlt ⊢; omega)]

/-- `G` is a homomorphism over a non-ASCII character. -/
theorem G_split (e : Enc) (h : ErrHandler) (c : Nat) (hc : 128 ≤ c) :
    ∀ (n : Nat) (a b : Str), a.length < n →
      G e h (a ++ c :: b) = (do let x ← G e h a; let y ← G e h b; pure (x ++ c :: y)) := by
  intro n
  induction n with
  | zero => intro a b h; omega
  | succ n ih =>
    intro a b hn
    cases a with
    | nil =>
      simp only [List.nil_append, G_nil, G_high e h c b hc]
      cases G e h b <;> rfl
    | cons x a =>
      by_cases hx : 128 ≤ x
      · rw [List.cons_append, G_high e h x _ hx, G_high e h x _ hx, ih a b (by simp at hn; omega)]
        cases G e h a <;> simp [bind, Except.bind, Except.map, pure, Except.pure]
        cases G e h b <;> rfl
      · have hx' : x < 128 := by omega
        rw [List.cons_append, G_low e h x _ hx', G_low e h x _ hx']
        rw [← List.cons_append, takeWhile_lt_app (x :: a) b c hc, dropWhile_lt_app (x :: a) b c hc]
        have hlt := dropWhile_lt_of_head (· < 128) x a (by simpa using hx')
        rw [ih _ b (by simp at hn hlt ⊢; omega)]
        cases unquoteImpl (.str ((x :: a).takeWhile (· < 128))) with
        | error z => rfl
        | ok u =>
          simp only [bind, Except.bind]
          cases decodeWith e h u with
          | error z => rfl
          | ok d =>
            simp only
            cases G e h ((x :: a).dropWhile (· < 128)) with
            | error z => rfl
            | ok t =>
              simp only
              cases G e h b with
              | error z => rfl
              | ok y => simp [pure, Except.pure]

theorem decodeWith_ascii (e : Enc) (h : ErrHandler) (s : Str) (hs : ∀ c ∈ s, c < 128) :
    decodeWith e h s = .ok s := by
  cases e with
  | utf8 => exact utf8Decode_ascii s h hs
  | ascii => exact asciiDecode_ascii s h hs
  | latin1 => rfl

theorem mem_takeWhile_lt {x : Nat} {l : Str} (h : x ∈ l.takeWhile (· < 128)) : x < 128 := by
  have := mem_takeWhile_p h
  simpa using this

theorem mem_takeWhile_sub {x : Nat} {p : Nat → Bool} {l : Str} (h : x ∈ l.takeWhile p) : x ∈ l := by
  rw [← List.takeWhile_append_dropWhile (p := p) (l := l)]; exact List.mem_append_left _ h

theorem mem_dropWhile_sub {x : Nat} {p : Nat → Bool} {l : Str} (h : x ∈ l.dropWhile p) : x ∈ l := by
  rw [← List.takeWhile_append_dropWhile (p := p) (l := l)]; exact List.mem_append_right _ h

/-- Without a `%`, `G` gives the string back. -/
theorem G_noPct (e : Enc) (h : ErrHandler) :
    ∀ (n : Nat) (s : Str), s.length < n → 37 ∉ s → G e h s = .ok s := by
  intro n
  induction n with
  | zero => intro s h; omega
  | succ n ih =>
    intro s hn hp
    cases s with
    | nil => rfl
    | cons x s =>
      by_cases hx : 128 ≤ x
      · rw [G_high e h x s hx, ih s (by simp at hn; omega) (fun m => hp (List.mem_cons_of_mem _ m))]
        rfl
      · have hx' : x < 128 := by omega
        rw [G_low e h x s hx']
        have hrun : ∀ y ∈ (x :: s).takeWhile (· < 128), y < 128 := fun y hy => mem_takeWhile_lt hy
        have hrp : 37 ∉ (x :: s).takeWhile (· < 128) := fun m => hp (mem_takeWhile_sub m)
        have hlt := dropWhile_lt_of_head (· < 128) x s (by simpa using hx')
        rw [unquoteImpl_str_ascii _ hrun, scan_no_pct _ hrp]
        simp only [bind, Except.bind, decodeWith_ascii e h _ hrun]
        rw [ih _ (by simp at hn hlt ⊢; omega) (fun m => hp (mem_dropWhile_sub m))]
        simp only [pure, Except.pure]
        rw [List.takeWhile_append_dropWhile]

theorem unquote_str_eq (s : Str) (enc : Option Enc) (h : Option ErrHandler) :
    unquote (.str s) enc h = if 37 ∈ s then G (enc.getD .utf8) (h.getD .replace) s else .ok s := by
  by_cases hp : 37 ∈ s
  · simp [unquote, hp, G]
  · simp [unquote, hp]

/-! ## The property -/

/-- For every input, `unquote`, `unquote_to_bytes` and `_unquote_impl` read `%XX` escapes left to
right (`scan`): a `%` followed by two hex digits (either case) is that byte, and any other
character is kept, including a `%` with fewer than two hex digits after it. On a `str`:
an ASCII string without `%` is returned as it is, one with a `%` is decoded from its scanned
bytes with `encoding` and `errors` (UTF-8 and `'replace'` when `None`); and a non-ASCII character
is kept as it is between the unquoted text on its two sides, the left side's errors first.
On `bytes`, `unquote` decodes the scanned bytes, and refuses `encoding=None` with its
`TypeError`. `unquote_to_bytes` scans `bytes`; scans the UTF-8 bytes of a `str` without
surrogates and raises `UnicodeEncodeError` on a lone surrogate; returns `b''` for an empty
argument; raises `AttributeError` for `None`; and on a `bytearray` with a `%` raises the
`TypeError` of the `bytearray` dictionary key at :817. Source: the docstrings of `unquote`
("Replace %xx escapes by their single-character equivalent ... invalid sequences are replaced by a
placeholder character") and `unquote_to_bytes`, the docs ("unquote() ... string may be either a str
or a bytes object"), and the comment at :796-797 ("strings are encoded as UTF-8"). -/
def UnquoteSpec : Prop :=
  (∀ (s : Str) (enc : Option Enc) (h : Option ErrHandler), (∀ c ∈ s, c < 128) →
    unquote (.str s) enc h = if 37 ∈ s then decodeWith (enc.getD .utf8) (h.getD .replace) (scan s) else .ok s) ∧
  (∀ (a b : Str) (c : Nat) (enc : Option Enc) (h : Option ErrHandler), 128 ≤ c →
    unquote (.str (a ++ c :: b)) enc h =
      (do let x ← unquote (.str a) enc h; let y ← unquote (.str b) enc h; pure (x ++ c :: y))) ∧
  (∀ (x : Str) (e : Enc) (h : ErrHandler), unquote (.bytes x false) (some e) (some h) = decodeWith e h (scan x)) ∧
  (∀ (x : Str) (h : Option ErrHandler),
    unquote (.bytes x false) none h = .error (.typeError "decode() argument 'encoding' must be str, not None")) ∧
  (∀ x : Str, unquoteToBytes (.bytes x false) = .ok (scan x)) ∧
  (∀ x : Str, 37 ∉ x → unquoteToBytes (.bytes x true) = .ok x) ∧
  (∀ x : Str, 37 ∈ x →
    unquoteToBytes (.bytes x true) = .error (.typeError "cannot use 'bytearray' as a dict key (unhashable type: 'bytearray')")) ∧
  (∀ s : Str, (∀ c ∈ s, isSurrogate c = false) →
    unquoteToBytes (.str s) = .ok (scan (s.flatMap UnicodeObj.utf8EncodeChar))) ∧
  (∀ s : Str, (∃ c ∈ s, isSurrogate c = true) → (unquoteToBytes (.str s)).raises "UnicodeEncodeError") ∧
  unquoteToBytes (.str []) = .ok [] ∧ unquoteToBytes (.bytes [] false) = .ok [] ∧
  unquoteToBytes .none = .error (.named "AttributeError" "'NoneType' object has no attribute 'split'")

theorem unquoteImpl_str_plain (s : Str) (hs : ∀ c ∈ s, isSurrogate c = false) :
    unquoteImpl (.str s) = .ok (scan (s.flatMap UnicodeObj.utf8EncodeChar)) := by
  rw [← joinBits_split]
  cases s with
  | nil => simp [unquoteImpl, Arg.truthy, splitOn_nil, joinBits, unquoteItems]; rfl
  | cons c r =>
    unfold unquoteImpl
    simp only [Arg.truthy, List.isEmpty_cons, Bool.not_false, Bool.false_eq_true, ite_false,
      utf8Encode_plain _ _ hs, bind, Except.bind, pure, Except.pure]
    rcases hsp : splitOn [37] ((c :: r).flatMap UnicodeObj.utf8EncodeChar) with _ | ⟨x, _ | ⟨y, u⟩⟩
    · exact absurd hsp (splitOn_ne_nil _ _)
    · have := splitOn_single hsp
      rw [← this]
      simp [joinBits, unquoteItems]
    · simp [joinBits]

theorem unquoteSpec_proven : UnquoteSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s enc h hs
    rw [unquote_str_eq]
    by_cases hp : 37 ∈ s
    · rw [if_pos hp, if_pos hp]
      obtain ⟨c, r, rfl⟩ : ∃ c r, s = c :: r := by
        cases s with
        | nil => simp at hp
        | cons c r => exact ⟨c, r, rfl⟩
      unfold G
      rw [show (c :: r).length + 1 = r.length + 2 by simp]
      exact genParts_ascii _ _ _ hs (by simp) r.length
    · rw [if_neg hp, if_neg hp]
  · intro a b c enc h hc
    rw [unquote_str_eq, unquote_str_eq, unquote_str_eq]
    by_cases hw : 37 ∈ a ++ c :: b
    · rw [if_pos hw, G_split _ _ c hc (a.length + 1) a b (by omega)]
      have ha : (if 37 ∈ a then G (enc.getD .utf8) (h.getD .replace) a else .ok a) =
          G (enc.getD .utf8) (h.getD .replace) a := by
        split
        · rfl
        · next hn => exact (G_noPct _ _ (a.length + 1) a (by omega) hn).symm
      have hb : (if 37 ∈ b then G (enc.getD .utf8) (h.getD .replace) b else .ok b) =
          G (enc.getD .utf8) (h.getD .replace) b := by
        split
        · rfl
        · next hn => exact (G_noPct _ _ (b.length + 1) b (by omega) hn).symm
      rw [ha, hb]
    · rw [if_neg hw]
      have ha : 37 ∉ a := fun m => hw (List.mem_append_left _ m)
      have hb : 37 ∉ b := fun m => hw (List.mem_append_right _ (List.mem_cons_of_mem _ m))
      have hc37 : c ≠ 37 := by omega
      rw [if_neg ha, if_neg hb]
      rfl
  · intro x e h
    simp only [unquote, unquoteImpl_bytes, bind, Except.bind]
  · intro x h
    simp only [unquote, unquoteImpl_bytes, bind, Except.bind]; rfl
  · intro x; exact unquoteImpl_bytes x
  · intro x hx
    simp only [unquoteToBytes, unquoteImpl]
    cases x with
    | nil => rfl
    | cons c r =>
      simp [Arg.truthy, bind, Except.bind, pure, Except.pure, splitOn_one_none 37 (c :: r) hx]
  · intro x hx
    simp only [unquoteToBytes, unquoteImpl]
    cases x with
    | nil => simp at hx
    | cons c r =>
      simp only [Arg.truthy, List.isEmpty_cons, Bool.not_false, Bool.false_eq_true, ite_false,
        bind, Except.bind, pure, Except.pure]
      rcases hsp : splitOn [37] (c :: r) with _ | ⟨y, _ | ⟨z, u⟩⟩
      · exact absurd hsp (splitOn_ne_nil _ _)
      · have := splitOn_single hsp
        rw [← this] at hx
        exact absurd hx (splitOn_parts 37 _ y (by rw [hsp]; simp))
      · rfl
  · intro s hs; exact unquoteImpl_str_plain s hs
  · intro s hs
    obtain ⟨c, hc, hsur⟩ := hs
    obtain ⟨d, r, rfl⟩ : ∃ d r, s = d :: r := by
      cases s with
      | nil => simp at hc
      | cons d r => exact ⟨d, r, rfl⟩
    simp only [unquoteToBytes, unquoteImpl, Arg.truthy, List.isEmpty_cons, Bool.not_false,
      Bool.false_eq_true, ite_false]
    exact raises_bind _ _ _ (utf8_strict_raises _ _ _ 0 [] (by omega) ⟨c, hc, hsur⟩)
  · rfl
  · rfl
  · rfl

end PyLean.TextLibs.Url
