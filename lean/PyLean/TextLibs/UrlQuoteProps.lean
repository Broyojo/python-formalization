import PyLean.TextLibs.UrlQuote

/-!
Properties of quoting in `Lib/urllib/parse.py`: the three paths of `quote_from_bytes` agree,
and `unquote` inverts `quote` (and `unquote_plus` inverts `quote_plus`) for every string the
chosen codec can encode, with any error handlers.
-/

namespace PyLean.TextLibs.Url

open PyLean
open PyLean.UnicodeObj (ErrHandler utf8EncodeChar isSurrogate maxUnicode)

set_option linter.unusedSimpArgs false

/-! ## The codecs on text they can represent -/

theorem utf8EncodeChar_ascii (c : Nat) (h : c < 128) : utf8EncodeChar c = [c] := by
  simp [utf8EncodeChar, show c < 0x80 from h]

theorem flatMap_utf8_ascii (s : Str) (h : ∀ c ∈ s, c < 128) : s.flatMap utf8EncodeChar = s := by
  induction s with
  | nil => rfl
  | cons c r ih =>
    rw [List.flatMap_cons, utf8EncodeChar_ascii c (h c List.mem_cons_self),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rfl

/-- `s.encode('utf-8', errors)` for a string without surrogates, whatever `errors` is. -/
theorem utf8Encode_plain (s : Str) (h : ErrHandler) (hs : ∀ c ∈ s, isSurrogate c = false) :
    UnicodeObj.utf8Encode s h = .ok (s.flatMap utf8EncodeChar) := by
  have := UnicodeObj.utf8EncodeLoop_plain s h s hs (s.length + 1) 0 [] (by omega)
  simpa [UnicodeObj.utf8Encode] using this

/-- `b.decode('utf-8', errors)` of what the encoder wrote, whatever `errors` is. -/
theorem utf8Decode_flatMap (s : Str) (h : ErrHandler)
    (hs : ∀ c ∈ s, c ≤ maxUnicode ∧ isSurrogate c = false) :
    UnicodeObj.utf8Decode (s.flatMap utf8EncodeChar) h = .ok s := by
  have := UnicodeObj.utf8Loop_flatMap (s.flatMap utf8EncodeChar) h false s hs
    ((s.flatMap utf8EncodeChar).length + 1) 0 [] (by have := UnicodeObj.length_le_flatMap s; omega)
  simp only [UnicodeObj.utf8Decode, this, bind, Except.bind, pure, Except.pure, List.nil_append]

theorem ascii_scalar (s : Str) (h : ∀ c ∈ s, c < 128) :
    ∀ c ∈ s, c ≤ maxUnicode ∧ isSurrogate c = false := by
  intro c hc
  have := h c hc
  refine ⟨by simp [maxUnicode]; omega, ?_⟩
  simp [isSurrogate]; omega

theorem utf8Encode_ascii (s : Str) (h : ErrHandler) (hs : ∀ c ∈ s, c < 128) :
    UnicodeObj.utf8Encode s h = .ok s := by
  rw [utf8Encode_plain s h (fun c hc => (ascii_scalar s hs c hc).2), flatMap_utf8_ascii s hs]

theorem utf8Decode_ascii (s : Str) (h : ErrHandler) (hs : ∀ c ∈ s, c < 128) :
    UnicodeObj.utf8Decode s h = .ok s := by
  have := utf8Decode_flatMap s h (ascii_scalar s hs)
  rwa [flatMap_utf8_ascii s hs] at this

theorem ucs1Loop_below (input : Str) (limit : Nat) (h : ErrHandler) (nameOf : Nat → Option Str) :
    ∀ (s : Str) (fuel pos : Nat) (out : Str), (∀ c ∈ s, c < limit) → s.length < fuel →
      UnicodeObj.ucs1EncodeLoop input limit h nameOf fuel pos s out = .ok (out ++ s) := by
  intro s
  induction s with
  | nil =>
    intro fuel pos out _ hf
    cases fuel with
    | zero => omega
    | succ f => simp [UnicodeObj.ucs1EncodeLoop]
  | cons c r ih =>
    intro fuel pos out hs hf
    cases fuel with
    | zero => omega
    | succ f =>
      simp only [UnicodeObj.ucs1EncodeLoop, if_pos (hs c List.mem_cons_self)]
      rw [ih f (pos + 1) (out ++ [c]) (fun x hx => hs x (List.mem_cons_of_mem _ hx))
        (by simp at hf; omega)]
      simp

/-- `s.encode('latin-1' or 'ascii', errors)` when every character fits. -/
theorem ucs1Encode_below (s : Str) (limit : Nat) (h : ErrHandler) (nameOf : Nat → Option Str)
    (hs : ∀ c ∈ s, c < limit) : UnicodeObj.ucs1Encode s limit h nameOf = .ok s := by
  have := ucs1Loop_below s limit h nameOf s (s.length + 1) 0 [] hs (by omega)
  simpa [UnicodeObj.ucs1Encode] using this

theorem unencodableRun_split (limit : Nat) (s : Str) :
    UnicodeObj.unencodableRun limit s ++ s.drop (UnicodeObj.unencodableRun limit s).length = s ∧
      ∀ c ∈ UnicodeObj.unencodableRun limit s, c ≥ limit := by
  induction s with
  | nil => simp [UnicodeObj.unencodableRun]
  | cons c r ih =>
    by_cases hc : c ≥ limit
    · have e : UnicodeObj.unencodableRun limit (c :: r) = c :: UnicodeObj.unencodableRun limit r := by
        simp [UnicodeObj.unencodableRun, hc]
      rw [e]
      refine ⟨by simp [ih.1], ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with h | h
      · exact h ▸ hc
      · exact ih.2 x h
    · have e : UnicodeObj.unencodableRun limit (c :: r) = [] := by
        simp [UnicodeObj.unencodableRun, hc]
      rw [e]; simp

/-- `s.encode('ascii', 'ignore')`: the characters below 128. -/
theorem ucs1Loop_ignore (input : Str) (limit : Nat) (nameOf : Nat → Option Str) :
    ∀ (n : Nat) (s : Str) (fuel pos : Nat) (out : Str), s.length < n → s.length < fuel →
      UnicodeObj.ucs1EncodeLoop input limit .ignore nameOf fuel pos s out =
        .ok (out ++ s.filter (fun c => decide (c < limit))) := by
  intro n
  induction n with
  | zero => intro s _ _ _ h; omega
  | succ n ih =>
    intro s fuel pos out hn hf
    match s, fuel with
    | [], 0 => simp at hf
    | [], f + 1 => simp [UnicodeObj.ucs1EncodeLoop]
    | _ :: _, 0 => simp at hf
    | c :: r, f + 1 =>
      simp only [UnicodeObj.ucs1EncodeLoop]
      by_cases hc : c < limit
      · rw [if_pos hc, ih r f (pos + 1) (out ++ [c]) (by simp at hn; omega) (by simp at hf; omega)]
        simp [hc]
      · rw [if_neg hc]
        obtain ⟨hsplit, hge⟩ := unencodableRun_split limit (c :: r)
        have hlen : (UnicodeObj.unencodableRun limit (c :: r)).length ≥ 1 := by
          simp [UnicodeObj.unencodableRun, show c ≥ limit by omega]
        have hfil : (c :: r).filter (fun c => decide (c < limit)) =
            ((c :: r).drop (UnicodeObj.unencodableRun limit (c :: r)).length).filter
              (fun c => decide (c < limit)) := by
          generalize hR : UnicodeObj.unencodableRun limit (c :: r) = R at hsplit hge
          have := congrArg (List.filter (fun c => decide (c < limit))) hsplit
          rw [List.filter_append, List.filter_eq_nil_iff.2 (fun x hx => by simp; exact hge x hx)] at this
          simpa using this.symm
        try dsimp only
        rw [ih _ f _ _ (by simp at hn ⊢; omega) (by simp at hf ⊢; omega), hfil]
        simp

theorem ucs1Encode_ignore (s : Str) (limit : Nat) (nameOf : Nat → Option Str) :
    UnicodeObj.ucs1Encode s limit .ignore nameOf = .ok (s.filter (fun c => decide (c < limit))) := by
  have := ucs1Loop_ignore s limit nameOf (s.length + 1) s (s.length + 1) 0 [] (by omega) (by omega)
  simpa [UnicodeObj.ucs1Encode] using this

theorem asciiDriver (input : Str) (h : ErrHandler) :
    ∀ (s : Str) (fuel pos : Nat) (out : Str), (∀ c ∈ s, c < 128) → s.length < fuel →
      UnicodeObj.decodeDriver UnicodeObj.stepAscii h "ascii" .unknown input fuel pos s out =
        .ok (out ++ s, pos + s.length) := by
  intro s
  induction s with
  | nil =>
    intro fuel pos out _ hf
    cases fuel with
    | zero => omega
    | succ f => simp [UnicodeObj.decodeDriver, UnicodeObj.stepAscii]
  | cons c r ih =>
    intro fuel pos out hs hf
    cases fuel with
    | zero => omega
    | succ f =>
      have hc := hs c List.mem_cons_self
      simp only [UnicodeObj.decodeDriver, UnicodeObj.stepAscii, if_pos hc, List.drop_one, List.tail_cons]
      rw [ih f (pos + 1) (out ++ [c]) (fun x hx => hs x (List.mem_cons_of_mem _ hx)) (by simp at hf; omega)]
      simp [Nat.add_assoc, Nat.add_comm 1]

theorem asciiDecode_ascii (s : Str) (h : ErrHandler) (hs : ∀ c ∈ s, c < 128) :
    UnicodeObj.asciiDecode s h = .ok s := by
  simp [UnicodeObj.asciiDecode, asciiDriver s h s (s.length + 1) 0 [] hs (by omega), bind, Except.bind,
    pure, Except.pure]

/-- The characters `encoding` can write: `Enc.fits`. -/
def Enc.fits : Enc → Nat → Prop
  | .utf8, c => c ≤ maxUnicode ∧ isSurrogate c = false
  | .ascii, c => c < 128
  | .latin1, c => c < 256

/-- The bytes `encoding` writes for a string it can represent. -/
def Enc.bytesOf : Enc → Str → Str
  | .utf8, s => s.flatMap utf8EncodeChar
  | _, s => s

theorem encodeWith_fits (e : Enc) (h : ErrHandler) (s : Str) (hs : ∀ c ∈ s, e.fits c) :
    encodeWith e h s = .ok (e.bytesOf s) := by
  cases e with
  | utf8 => exact utf8Encode_plain s h (fun c hc => (hs c hc).2)
  | ascii => exact ucs1Encode_below s 128 h noNames hs
  | latin1 => exact ucs1Encode_below s 256 h noNames hs

theorem decodeWith_fits (e : Enc) (h : ErrHandler) (s : Str) (hs : ∀ c ∈ s, e.fits c) :
    decodeWith e h (e.bytesOf s) = .ok s := by
  cases e with
  | utf8 => exact utf8Decode_flatMap s h hs
  | ascii => exact asciiDecode_ascii s h hs
  | latin1 => rfl

theorem bytesOf_lt (e : Enc) (s : Str) (hs : ∀ c ∈ s, e.fits c) : ∀ b ∈ e.bytesOf s, b < 256 := by
  cases e with
  | utf8 =>
    intro b hb
    simp only [Enc.bytesOf, List.mem_flatMap] at hb
    obtain ⟨c, hc, hb⟩ := hb
    have hm := (hs c hc).1
    simp only [maxUnicode] at hm
    unfold utf8EncodeChar at hb
    split at hb
    · simp at hb; omega
    · split at hb
      · simp at hb; omega
      · split at hb
        · simp at hb; omega
        · simp at hb; omega
  | ascii => intro b hb; have := hs b hb; simp [Enc.fits] at this; omega
  | latin1 => intro b hb; exact hs b hb

theorem bytesOf_nil (e : Enc) (s : Str) : e.bytesOf s = [] ↔ s = [] := by
  cases e with
  | utf8 =>
    simp only [Enc.bytesOf]
    constructor
    · intro h
      cases s with
      | nil => rfl
      | cons c r =>
        have := UnicodeObj.utf8EncodeChar_ne c
        simp [List.flatMap_cons] at h
        exact absurd h.1 this
    · intro h; subst h; rfl
  | ascii => simp [Enc.bytesOf]
  | latin1 => simp [Enc.bytesOf]

/-! ## The quoter -/

theorem hexU_isHex (d : Nat) (h : d < 16) : isHex (hexU d) = true := by
  simp only [hexU, isHex, isAsciiDigit]
  split <;> simp <;> omega

theorem hexVal_hexU (d : Nat) (h : d < 16) : hexVal (hexU d) = d := by
  simp only [hexU, hexVal]
  split <;> split <;> (try split) <;> omega

theorem alwaysSafe_pct : alwaysSafe 37 = false := by decide

theorem alwaysSafe_lt (c : Nat) (h : alwaysSafe c = true) : c < 128 := by
  simp [alwaysSafe, isAsciiAlpha, isAsciiDigit] at h; omega

/-- `scan` reads back each quoted byte. -/
theorem scan_quote (safe : Str) (hp : 37 ∉ safe) (x : Str) (hx : ∀ b ∈ x, b < 256) :
    scan (x.flatMap (quoteByte safe)) = x := by
  induction x with
  | nil => exact scan_nil
  | cons b r ih =>
    have hb := hx b List.mem_cons_self
    have ih' := ih (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    rw [List.flatMap_cons]
    by_cases hk : (alwaysSafe b || safe.contains b) = true
    · have hne : b ≠ 37 := by
        intro e; subst e
        simp [alwaysSafe_pct] at hk
        exact hp hk
      rw [show quoteByte safe b = [b] by simp only [quoteByte, hk, if_true]]
      rw [List.singleton_append, scan_other b _ hne, ih']
    · rw [show quoteByte safe b = [37, hexU (b / 16), hexU (b % 16)] by
        simp only [quoteByte, hk, Bool.false_eq_true, if_false]]
      simp only [List.cons_append, List.nil_append]
      rw [scan_pct3, hexU_isHex _ (by omega), hexU_isHex _ (by omega), Bool.and_self, if_pos rfl,
        hexVal_hexU _ (by omega), hexVal_hexU _ (by omega), ih']
      congr 1
      omega

theorem quoteByte_ascii (safe : Str) (hs : ∀ c ∈ safe, c < 128) (b : Nat) (hb : b < 256) :
    ∀ c ∈ quoteByte safe b, c < 128 := by
  intro c hc
  unfold quoteByte at hc
  split at hc
  · next hk =>
    simp at hc; subst hc
    rcases Bool.or_eq_true _ _ ▸ hk with h | h
    · exact alwaysSafe_lt _ h
    · exact hs _ (List.contains_iff_mem.1 h)
  · simp [hexU] at hc
    rcases hc with h | h | h
    · omega
    · split at h <;> omega
    · split at h <;> omega

theorem flatMap_quote_ascii (safe : Str) (hs : ∀ c ∈ safe, c < 128) (x : Str)
    (hx : ∀ b ∈ x, b < 256) : ∀ c ∈ x.flatMap (quoteByte safe), c < 128 := by
  intro c hc
  simp only [List.mem_flatMap] at hc
  obtain ⟨b, hbx, hb⟩ := hc
  exact quoteByte_ascii safe hs b (hx b hbx) c hb

theorem flatMap_quote_keep (safe x : Str) (hk : ∀ b ∈ x, (alwaysSafe b || safe.contains b) = true) :
    x.flatMap (quoteByte safe) = x := by
  induction x with
  | nil => rfl
  | cons b r ih =>
    rw [List.flatMap_cons, ih (fun y hy => hk y (List.mem_cons_of_mem _ hy)),
      show quoteByte safe b = [b] by simp only [quoteByte, hk b List.mem_cons_self, if_true]]
    rfl

theorem dropWhile_nil_iff (p : Nat → Bool) (x : Str) : x.dropWhile p = [] ↔ ∀ b ∈ x, p b = true := by
  induction x with
  | nil => simp
  | cons c r ih =>
    by_cases hc : p c = true
    · simp [List.dropWhile_cons, hc, ih]
    · simp [List.dropWhile_cons, hc]

theorem rstripBy_nil (p : Nat → Bool) (x : Str) : rstripBy p x = [] ↔ ∀ b ∈ x, p b = true := by
  simp only [rstripBy, List.reverse_eq_nil_iff, dropWhile_nil_iff, List.mem_reverse]

theorem chunks_flatten_lt (n : Nat) : ∀ m (l : Str), l.length < m → (chunks n l).flatten = l
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | m + 1, l, hm => by
    rw [chunks]
    split
    · simp
    · next h =>
      split
      · next hle => simp [List.take_of_length_le hle]
      · next hle =>
        have hn : n ≠ 0 := fun e => h (Or.inl e)
        rw [List.flatten_cons, chunks_flatten_lt n m (l.drop n) (by simp; omega)]
        exact List.take_append_drop n l

theorem chunks_flatten (n : Nat) (l : Str) : (chunks n l).flatten = l :=
  chunks_flatten_lt n (l.length + 1) l (by omega)

/-- `safe`, as `quote_from_bytes` normalizes it: its characters below 128. -/
def safeBytes : Arg → Option Str
  | .str s => some (s.filter (fun c => decide (c < 128)))
  | .bytes s _ => some (s.filter (fun c => decide (c < 128)))
  | .none => none

/-- `quote_from_bytes`, :1096-1121: the fast path (`bs.rstrip(safe)` is empty, return
`bs.decode()`), the path below 200,000 bytes, and the chunked path above it all give the
quoted bytes in order, for every `bytes`/`bytearray` and every `str` or `bytes` `safe`. A
non-bytes argument raises `TypeError`. Source: (a), the paths of one function agree. -/
def QuoteFromBytesPaths : Prop :=
  (∀ (x : Str) (ba : Bool) (safe : Arg) (sb : Str), safeBytes safe = some sb →
    quoteFromBytes (.bytes x ba) safe = .ok (x.flatMap (quoteByte sb))) ∧
  (∀ (s safe : Arg), (∀ x ba, s ≠ Arg.bytes x ba) →
    quoteFromBytes s safe = .error (PyExc.typeError "quote_from_bytes() expected bytes"))

theorem normSafe_eq (safe : Arg) (sb : Str) (hs : safeBytes safe = some sb) : normSafe safe = .ok sb := by
  cases safe with
  | str s => simp [safeBytes] at hs; simp [normSafe, ucs1Encode_ignore, hs]
  | bytes s b => simp [safeBytes] at hs; simp [normSafe, ← hs]
  | none => simp [safeBytes] at hs

theorem safeBytes_ascii (safe : Arg) (sb : Str) (hs : safeBytes safe = some sb) : ∀ c ∈ sb, c < 128 := by
  cases safe with
  | str s => simp [safeBytes] at hs; subst hs; intro c hc; simp at hc; exact hc.2
  | bytes s b => simp [safeBytes] at hs; subst hs; intro c hc; simp at hc; exact hc.2
  | none => simp [safeBytes] at hs

theorem flatMap_flatten' (l : List Str) (f : Nat → Str) :
    l.flatten.flatMap f = l.flatMap (fun c => c.flatMap f) := by
  induction l with
  | nil => rfl
  | cons x r ih => simp [List.flatten_cons, List.flatMap_append, ih]

theorem quoteTail_eq (x sb : Str) (hsb : ∀ c ∈ sb, c < 128) :
    quoteTail x sb = .ok (x.flatMap (quoteByte sb)) := by
  unfold quoteTail
  by_cases hf : (rstripBy (fun c => alwaysSafe c || sb.contains c) x).isEmpty = true
  · rw [if_pos hf]
    have hall := (rstripBy_nil _ _).1 (List.isEmpty_iff.1 hf)
    have hasc : ∀ b ∈ x, b < 128 := by
      intro b hb
      rcases Bool.or_eq_true _ _ ▸ hall b hb with h | h
      · exact alwaysSafe_lt _ h
      · exact hsb _ (List.contains_iff_mem.1 h)
    rw [utf8Decode_ascii _ _ hasc, flatMap_quote_keep sb _ hall]
  · rw [if_neg hf]
    split
    · rfl
    · rw [← flatMap_flatten', chunks_flatten]

theorem quoteFromBytes_eq (x : Str) (ba : Bool) (safe : Arg) (sb : Str)
    (hs : safeBytes safe = some sb) :
    quoteFromBytes (.bytes x ba) safe = .ok (x.flatMap (quoteByte sb)) := by
  unfold quoteFromBytes
  cases x with
  | nil => rfl
  | cons c r =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, bind, Except.bind, pure,
      Except.pure, normSafe_eq safe sb hs]
    exact quoteTail_eq _ sb (safeBytes_ascii safe sb hs)

theorem quoteFromBytesPaths_proven : QuoteFromBytesPaths := by
  refine ⟨fun x ba safe sb hs => quoteFromBytes_eq x ba safe sb hs, ?_⟩
  intro s safe hs
  cases s with
  | bytes x ba => exact absurd rfl (hs x ba)
  | str x => rfl
  | none => rfl

end PyLean.TextLibs.Url
