import PyLean.TextLibs.UrlQuoteProps

/-!
Round trips of `Lib/urllib/parse.py`'s quoting functions: `unquote(quote(s))`,
`unquote_plus(quote_plus(s))` and `unquote_to_bytes(quote_from_bytes(b))`.
-/

namespace PyLean.TextLibs.Url

open PyLean
open PyLean.UnicodeObj (ErrHandler utf8EncodeChar isSurrogate maxUnicode)

set_option linter.unusedSimpArgs false

theorem scan_no_pct (q : Str) (h : 37 ∉ q) : scan q = q := by
  induction q with
  | nil => exact scan_nil
  | cons c r ih =>
    have hc : c ≠ 37 := fun e => h (e ▸ List.mem_cons_self)
    rw [scan_other c r hc, ih (fun m => h (List.mem_cons_of_mem _ m))]

/-- `_unquote_impl` on an ASCII `str`. -/
theorem unquoteImpl_str_ascii (q : Str) (hq : ∀ c ∈ q, c < 128) :
    unquoteImpl (.str q) = .ok (scan q) := by
  rw [← joinBits_split]
  cases q with
  | nil => simp [unquoteImpl, Arg.truthy, splitOn_nil, joinBits, unquoteItems]; rfl
  | cons c r =>
    unfold unquoteImpl
    simp only [Arg.truthy, List.isEmpty_cons, Bool.not_false, Bool.false_eq_true, ite_false,
      utf8Encode_ascii _ _ hq, bind, Except.bind, pure, Except.pure]
    rcases hsp : splitOn [37] (c :: r) with _ | ⟨x, _ | ⟨y, u⟩⟩
    · exact absurd hsp (splitOn_ne_nil _ _)
    · have := splitOn_single hsp
      subst this
      simp [joinBits, unquoteItems]
    · simp [joinBits]

theorem takeWhile_all (p : Nat → Bool) (l : Str) (h : ∀ c ∈ l, p c = true) : l.takeWhile p = l := by
  induction l with
  | nil => rfl
  | cons c r ih => simp [List.takeWhile_cons, h c List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem genParts_nil (e : Enc) (h : ErrHandler) (f : Nat) : genParts e h (f + 1) [] = .ok [] := by
  simp [genParts]

/-- `''.join(_generate_unquoted_parts(q, ...))` on an ASCII string: one run. -/
theorem genParts_ascii (e : Enc) (h : ErrHandler) (q : Str) (hq : ∀ c ∈ q, c < 128) (hne : q ≠ [])
    (f : Nat) : genParts e h (f + 2) q = decodeWith e h (scan q) := by
  obtain ⟨c, r, rfl⟩ : ∃ c r, q = c :: r := by cases q with
    | nil => exact absurd rfl hne
    | cons c r => exact ⟨c, r, rfl⟩
  have hc := hq c List.mem_cons_self
  have hgap : (c :: r).takeWhile (fun x => decide (x ≥ 128)) = [] := by
    simp [List.takeWhile_cons]; omega
  have hrest : (c :: r).dropWhile (fun x => decide (x ≥ 128)) = c :: r := by
    simp [List.dropWhile_cons]; omega
  have hrun : (c :: r).takeWhile (fun x => decide (x < 128)) = c :: r :=
    takeWhile_all _ _ (fun x hx => by simp; exact hq x hx)
  have hdrop : (c :: r).dropWhile (fun x => decide (x < 128)) = [] :=
    (dropWhile_nil_iff _ _).2 (fun x hx => by simp; exact hq x hx)
  rw [genParts]
  simp only [hgap, hrest, List.isEmpty_cons, Bool.false_eq_true, ite_false, hrun, hdrop,
    unquoteImpl_str_ascii _ hq, bind, Except.bind, genParts_nil, List.nil_append]
  cases decodeWith e h (scan (c :: r)) <;> simp [pure, Except.pure]

theorem hexU_ge (x : Nat) : 48 ≤ hexU x := by
  simp only [hexU]; split <;> omega

theorem quoteByte_ne (safe : Str) (b d : Nat) (hd : alwaysSafe d = false) (hds : d ∉ safe)
    (hd37 : d ≠ 37) (hd48 : d < 48) : d ∉ quoteByte safe b := by
  unfold quoteByte
  split
  · next hk =>
    simp
    intro e; subst e
    simp [hd] at hk; exact hds hk
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨hd37, ?_, ?_⟩
    · have := hexU_ge (b / 16); omega
    · have := hexU_ge (b % 16); omega

theorem not_mem_flatMap_quote (safe : Str) (x : Str) (d : Nat) (hd : alwaysSafe d = false)
    (hds : d ∉ safe) (hd37 : d ≠ 37) (hd48 : d < 48) : d ∉ x.flatMap (quoteByte safe) := by
  simp only [List.mem_flatMap, not_exists, not_and]
  intro b _
  exact quoteByte_ne safe b d hd hds hd37 hd48

/-- `unquote(quote(s))` for the bytes a codec wrote. -/
theorem unquote_quoted (e : Enc) (h : ErrHandler) (s : Str) (hs : ∀ c ∈ s, e.fits c) (sb : Str)
    (hsb : ∀ c ∈ sb, c < 128) (hp : 37 ∉ sb) :
    unquote (.str ((e.bytesOf s).flatMap (quoteByte sb))) (some e) (some h) = .ok s := by
  have hb := bytesOf_lt e s hs
  have hasc := flatMap_quote_ascii sb hsb _ hb
  have hscan := scan_quote sb hp _ hb
  generalize hq : (e.bytesOf s).flatMap (quoteByte sb) = q at hasc hscan
  simp only [unquote]
  by_cases h37 : q.contains 37 = true
  · rw [if_neg (by rw [h37]; decide)]
    have hne : q ≠ [] := by intro e; subst e; simp at h37
    have : q.length + 1 = (q.length - 1) + 2 := by
      cases q with
      | nil => exact absurd rfl hne
      | cons _ _ => simp
    simp only [Option.getD_some]
    rw [this, genParts_ascii e h q hasc hne, hscan, decodeWith_fits e h s hs]
  · rw [if_pos (by simpa using h37)]
    have hn : 37 ∉ q := by simpa using h37
    rw [scan_no_pct q hn] at hscan
    -- `q` is the codec's bytes for `s`, and an ASCII string the codec writes as itself
    have hqf : ∀ c ∈ q, e.fits c := by
      intro c hc
      have := hasc c hc
      cases e with
      | utf8 => exact ascii_scalar q hasc c hc
      | ascii => exact this
      | latin1 => show c < 256; omega
    have hqb : e.bytesOf q = q := by
      cases e with
      | utf8 => exact flatMap_utf8_ascii q hasc
      | ascii => rfl
      | latin1 => rfl
    have d1 := decodeWith_fits e h s hs
    have d2 := decodeWith_fits e h q hqf
    rw [hqb] at d2
    rw [← hscan, d2] at d1
    cases d1
    rfl

/-- For every `str` that `encoding` can write (for UTF-8: every string without surrogates),
every `safe` (`str` or `bytes`) and all error handlers, `quote(s, safe, encoding, errors)`
%-escapes every byte of `s.encode(encoding)` that is neither always safe nor in `safe`, and when
`safe` has no `%`, `unquote(quote(s, ...), encoding, errors2) == s`. `encoding=None` is UTF-8 on
both sides. Source: (a), a round trip; the docstrings of `quote` and `unquote`. -/
def QuoteStrRoundTrip : Prop :=
  ∀ (enc : Option Enc) (s : Str) (safe : Arg) (sb : Str) (h1 h2 : Option ErrHandler),
    (∀ c ∈ s, (enc.getD .utf8).fits c) → safeBytes safe = some sb →
    quote (.str s) safe enc h1 = .ok (((enc.getD .utf8).bytesOf s).flatMap (quoteByte sb)) ∧
    (37 ∉ sb → ∃ q, quote (.str s) safe enc h1 = .ok q ∧ unquote (.str q) enc h2 = .ok s)

theorem unquote_getD (q : Str) (enc : Option Enc) (h : Option ErrHandler) :
    unquote (.str q) enc h = unquote (.str q) (some (enc.getD .utf8)) (some (h.getD .replace)) := by
  simp [unquote]

theorem quote_str_eq (enc : Option Enc) (s : Str) (safe : Arg) (sb : Str) (h1 : Option ErrHandler)
    (hs : ∀ c ∈ s, (enc.getD .utf8).fits c) (hsb : safeBytes safe = some sb) :
    quote (.str s) safe enc h1 = .ok (((enc.getD .utf8).bytesOf s).flatMap (quoteByte sb)) := by
  simp only [quote]
  by_cases he : s.isEmpty = true
  · rw [if_pos he]
    have : s = [] := List.isEmpty_iff.1 he
    subst this
    cases enc with
    | none => rfl
    | some e => cases e <;> rfl
  · rw [if_neg he]
    simp only [bind, Except.bind, encodeWith_fits _ _ s hs]
    exact quoteFromBytes_eq _ false safe sb hsb

theorem quoteStrRoundTrip_proven : QuoteStrRoundTrip := by
  intro enc s safe sb h1 h2 hs hsb
  refine ⟨quote_str_eq enc s safe sb h1 hs hsb, fun hp => ⟨_, quote_str_eq enc s safe sb h1 hs hsb, ?_⟩⟩
  rw [unquote_getD]
  exact unquote_quoted _ _ s hs sb (safeBytes_ascii safe sb hsb) hp

/-- `' '` to `'+'`, as `quote_plus` ends. -/
def spToPlus (q : Str) : Str := q.map (fun c => if c == 32 then 43 else c)

/-- For every `str` that `encoding` can write, every `safe` and all error handlers,
`quote_plus(s, safe, encoding, errors)` is `quote(s, safe)` when `s` has no space, and otherwise
`quote(s, safe + ' ')` with spaces turned into `+`; when `safe` has neither `%` nor `+`,
`unquote_plus(quote_plus(s, ...), encoding, errors2) == s`.
Source: (a), a round trip; the docstrings of `quote_plus` and `unquote_plus`. -/
def QuotePlusRoundTrip : Prop :=
  ∀ (enc : Option Enc) (s : Str) (safe : Arg) (sb : Str) (h1 h2 : Option ErrHandler),
    (∀ c ∈ s, (enc.getD .utf8).fits c) → safeBytes safe = some sb →
    quotePlus (.str s) safe enc h1 = .ok (if s.contains 32 then
        spToPlus (((enc.getD .utf8).bytesOf s).flatMap (quoteByte (sb ++ [32])))
      else ((enc.getD .utf8).bytesOf s).flatMap (quoteByte sb)) ∧
    (37 ∉ sb → 43 ∉ sb → ∃ q, quotePlus (.str s) safe enc h1 = .ok q ∧ unquotePlus (.str q) enc h2 = .ok s)

theorem map_plus_id (q : Str) (h : 43 ∉ q) : q.map (fun c => if c == 43 then 32 else c) = q := by
  induction q with
  | nil => rfl
  | cons c r ih =>
    have hc : c ≠ 43 := fun e => h (e ▸ List.mem_cons_self)
    rw [List.map_cons, ih (fun m => h (List.mem_cons_of_mem _ m))]
    simp [hc]

theorem map_space_plus (q : Str) (h : 43 ∉ q) :
    (q.map (fun c => if c == 32 then 43 else c)).map (fun c => if c == 43 then 32 else c) = q := by
  induction q with
  | nil => rfl
  | cons c r ih =>
    have hc : c ≠ 43 := fun e => h (e ▸ List.mem_cons_self)
    simp only [List.map_cons, ih (fun m => h (List.mem_cons_of_mem _ m))]
    by_cases h32 : c = 32
    · subst h32; simp
    · simp [h32, hc]

theorem plus_not_quoted (sb x : Str) (h : 43 ∉ sb) : 43 ∉ x.flatMap (quoteByte sb) :=
  not_mem_flatMap_quote sb x 43 (by decide) h (by decide) (by decide)

theorem safeBytes_space (safe : Arg) (sb : Str) (hs : safeBytes safe = some sb) :
    ∃ safe2, addSpace safe = .ok safe2 ∧ safeBytes safe2 = some (sb ++ [32]) := by
  cases safe with
  | str s => simp [safeBytes] at hs; subst hs; exact ⟨_, rfl, by simp [safeBytes]⟩
  | bytes b ba => simp [safeBytes] at hs; subst hs; exact ⟨_, rfl, by simp [safeBytes]⟩
  | none => simp [safeBytes] at hs

theorem quotePlus_eq (enc : Option Enc) (s : Str) (safe : Arg) (sb : Str) (h1 : Option ErrHandler)
    (hs : ∀ c ∈ s, (enc.getD .utf8).fits c) (hsb : safeBytes safe = some sb) :
    quotePlus (.str s) safe enc h1 = .ok (if s.contains 32 then
        spToPlus (((enc.getD .utf8).bytesOf s).flatMap (quoteByte (sb ++ [32])))
      else ((enc.getD .utf8).bytesOf s).flatMap (quoteByte sb)) := by
  unfold quotePlus
  by_cases hsp : s.contains 32 = true
  · obtain ⟨safe2, e2, hs2⟩ := safeBytes_space safe sb hsb
    simp only [hsp, Bool.not_true, Bool.false_eq_true, ite_false, ite_true, bind, Except.bind, e2,
      quote_str_eq enc s safe2 _ h1 hs hs2, pure, Except.pure]
    rfl
  · simp only [Bool.not_eq_true] at hsp
    simp only [hsp, Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
    exact quote_str_eq enc s safe sb h1 hs hsb

theorem quotePlusRoundTrip_proven : QuotePlusRoundTrip := by
  intro enc s safe sb h1 h2 hs hsb
  refine ⟨quotePlus_eq enc s safe sb h1 hs hsb, fun hp h43 => ?_⟩
  have hsa := safeBytes_ascii safe sb hsb
  have hb := bytesOf_lt _ s hs
  unfold quotePlus
  by_cases hsp : s.contains 32 = true
  · obtain ⟨safe2, e2, hs2⟩ := safeBytes_space safe sb hsb
    simp only [hsp, Bool.not_true, Bool.false_eq_true, ite_false, bind, Except.bind, e2,
      quote_str_eq enc s safe2 _ h1 hs hs2, pure, Except.pure]
    refine ⟨_, rfl, ?_⟩
    simp only [unquotePlus]
    have n43 : 43 ∉ sb ++ [32] := by simp; exact h43
    have n37 : 37 ∉ sb ++ [32] := by simp; exact hp
    rw [map_space_plus _ (plus_not_quoted _ _ n43), unquote_getD]
    exact unquote_quoted _ _ s hs _ (by intro c hc; simp at hc; rcases hc with h | h; exact hsa c h; omega) n37
  · simp only [Bool.not_eq_true] at hsp
    simp only [hsp, Bool.not_false, ite_true]
    rw [quote_str_eq enc s safe sb h1 hs hsb]
    refine ⟨_, rfl, ?_⟩
    simp only [unquotePlus]
    rw [map_plus_id _ (plus_not_quoted _ _ h43), unquote_getD]
    exact unquote_quoted _ _ s hs sb hsa hp

/-- `unquote_to_bytes(quote_from_bytes(b, safe)) == b` for every `bytes` and every `safe` without
`%`. Source: (a), a round trip; the docstrings of both functions. -/
def QuoteBytesRoundTrip : Prop :=
  ∀ (x : Str) (ba : Bool) (safe : Arg) (sb : Str), (∀ b ∈ x, b < 256) → safeBytes safe = some sb →
    37 ∉ sb → ∃ q, quoteFromBytes (.bytes x ba) safe = .ok q ∧ unquoteToBytes (.str q) = .ok x

theorem quoteBytesRoundTrip_proven : QuoteBytesRoundTrip := by
  intro x ba safe sb hx hsb hp
  refine ⟨_, quoteFromBytes_eq x ba safe sb hsb, ?_⟩
  simp only [unquoteToBytes]
  rw [unquoteImpl_str_ascii _ (flatMap_quote_ascii sb (safeBytes_ascii safe sb hsb) x hx),
    scan_quote sb hp x hx]

end PyLean.TextLibs.Url
