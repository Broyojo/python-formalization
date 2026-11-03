import PyLean.UnicodeObj.CodecsRegProps

/-!
The generic and the text encode/decode paths, the error handler registry, `_normalize_encoding`
and the escape codec.
-/

namespace PyLean.UnicodeObj.Codecs

open PyLean PyLean.UnicodeObj

/-! ## Encoding and decoding -/

/-- What a coder's answer becomes (codecs.c:411-429, :456-473): the first item of a 2-tuple;
a `TypeError` for anything else; the coder's exception with a note naming the encoding. -/
def coderResult (r : Py Val) (what tupleMsg encoding : String) : NPy Val :=
  match r with
  | .error e => .error ⟨e, [s!"{what} with '{encoding}' codec failed"]⟩
  | .ok (.tuple _ [out, _] _) => .ok out
  | .ok _ => .error ⟨.typeError tupleMsg, []⟩

/-- The two paths, with the text test and the argument tuple as the model computes them. -/
def EncodePaths0 : Prop :=
  ∀ (W : World) (st : Reg) (obj : Val) (enc : List Nat) (errors : Option Str),
    match pyCodecLookup W st enc with
    | (st1, .error e) =>
      pyCodecEncode W st obj enc errors = (st1, .error ⟨e, []⟩) ∧
      encodeText W st obj enc errors = (st1, .error ⟨e, []⟩)
    | (st1, .ok codec) =>
      let gen := (runOps W st1 (W.call (tupleItem codec 0) (argsTuple obj errors)).1,
        coderResult (W.call (tupleItem codec 0) (argsTuple obj errors)).2 "encoding"
          "encoder must return a tuple (object, integer)" (cstr enc))
      pyCodecEncode W st obj enc errors = gen ∧
      (isTextCodec W codec = .ok true → encodeText W st obj enc errors = gen) ∧
      (isTextCodec W codec = .ok false → encodeText W st obj enc errors =
        (st1, .error ⟨lookupErr s!"'{toLeanString (trunc400 ((utf8Decode enc .strict).toOption.getD []))}' is not a text encoding; use {("codecs.encode()" : String)} to handle arbitrary codecs", []⟩)) ∧
      (∀ e, isTextCodec W codec = .error e → encodeText W st obj enc errors = (st1, .error ⟨e, []⟩))

/-- The same for decoding. -/
def DecodePaths0 : Prop :=
  ∀ (W : World) (st : Reg) (obj : Val) (enc : List Nat) (errors : Option Str),
    match pyCodecLookup W st enc with
    | (st1, .error e) =>
      pyCodecDecode W st obj enc errors = (st1, .error ⟨e, []⟩) ∧
      decodeText W st obj enc errors = (st1, .error ⟨e, []⟩)
    | (st1, .ok codec) =>
      let gen := (runOps W st1 (W.call (tupleItem codec 1) (argsTuple obj errors)).1,
        coderResult (W.call (tupleItem codec 1) (argsTuple obj errors)).2 "decoding"
          "decoder must return a tuple (object,integer)" (cstr enc))
      pyCodecDecode W st obj enc errors = gen ∧
      (isTextCodec W codec = .ok true → decodeText W st obj enc errors = gen) ∧
      (isTextCodec W codec = .ok false → decodeText W st obj enc errors =
        (st1, .error ⟨lookupErr s!"'{toLeanString (trunc400 ((utf8Decode enc .strict).toOption.getD []))}' is not a text encoding; use {("codecs.decode()" : String)} to handle arbitrary codecs", []⟩)) ∧
      (∀ e, isTextCodec W codec = .error e → decodeText W st obj enc errors = (st1, .error ⟨e, []⟩))

theorem coderResult_eq (W : World) (st : Reg) (obj coder : Val) (encoding : String)
    (errors : Option Str) (what tupleMsg : String) :
    codecInternal W st obj coder encoding errors what tupleMsg =
      (runOps W st (W.call coder (argsTuple obj errors)).1,
        coderResult (W.call coder (argsTuple obj errors)).2 what tupleMsg encoding) := by
  unfold codecInternal callVal coderResult
  rcases W.call coder (argsTuple obj errors) with ⟨ops, r⟩
  simp only
  cases r with
  | error e => rfl
  | ok res =>
    cases res with
    | tuple id items exact =>
      simp only
      match items with
      | [] => rfl
      | [_] => rfl
      | [_, _] => rfl
      | _ :: _ :: _ :: _ => simp
    | _ => rfl

theorem lookupText_cases (W : World) (st : Reg) (enc : List Nat) (alt : Option String) :
    lookupTextEncoding W st enc alt =
      match pyCodecLookup W st enc with
      | (st1, .error e) => (st1, .error e)
      | (st1, .ok codec) =>
        match isTextCodec W codec with
        | .error e => (st1, .error e)
        | .ok true => (st1, .ok codec)
        | .ok false =>
          let name := toLeanString (trunc400 ((utf8Decode enc .strict).toOption.getD []))
          match alt with
          | some cmd => (st1, .error (lookupErr
              s!"'{name}' is not a text encoding; use {cmd} to handle arbitrary codecs"))
          | none => (st1, .error (lookupErr s!"'{name}' is not a text encoding")) := rfl

theorem encodePaths0 : EncodePaths0 := by
  intro W st obj enc errors
  have hlt := lookupText_cases W st enc (some "codecs.encode()")
  unfold pyCodecEncode encodeText pyCodecEncoder codecGetitem getitemChecked encodeInternal
  rw [hlt]
  rcases hl : pyCodecLookup W st enc with ⟨st1, r⟩
  cases r with
  | error e => simp
  | ok codec =>
    simp only [coderResult_eq]
    refine ⟨?_, fun h => ?_, fun h => ?_, fun e h => ?_⟩
    · trivial
    all_goals (simp only [h]; try rfl)

theorem decodePaths0 : DecodePaths0 := by
  intro W st obj enc errors
  have hlt := lookupText_cases W st enc (some "codecs.decode()")
  unfold pyCodecDecode decodeText pyCodecDecoder codecGetitem getitemChecked decodeInternal
  rw [hlt]
  rcases hl : pyCodecLookup W st enc with ⟨st1, r⟩
  cases r with
  | error e => simp
  | ok codec =>
    simp only [coderResult_eq]
    refine ⟨?_, fun h => ?_, fun h => ?_, fun e h => ?_⟩
    · trivial
    all_goals (simp only [h]; try rfl)


/-- A plain `tuple`, `PyTuple_CheckExact`. -/
def isExactTuple : Val → Bool
  | .tuple _ _ true => true
  | _ => false

theorem argsTuple_eq (obj : Val) (errors : Option Str) :
    argsTuple obj errors = obj :: (errors.map Val.str).toList := by
  cases errors <;> rfl

theorem isTextCodec_exact (W : World) (codec : Val) (h : isExactTuple codec = true) :
    isTextCodec W codec = .ok true := by
  cases codec with
  | tuple id items exact => cases exact <;> simp_all [isExactTuple, isTextCodec]
  | _ => simp [isExactTuple] at h

theorem isTextCodec_other (W : World) (codec : Val) (h : isExactTuple codec = false) :
    isTextCodec W codec =
      match W.getattr codec "_is_text_encoding" with
      | .error e => .error e
      | .ok none => .ok true
      | .ok (some a) => W.truth a := by
  cases codec with
  | tuple id items exact => cases exact <;> first | rfl | simp_all [isExactTuple, isTextCodec]
  | _ => rfl

/-- **codecs.encode and str.encode use one encoder the same way.** For every registry, object,
encoding name and `errors`: if the lookup fails, both fail with its error. Otherwise
`codecs.encode` calls the codec's first item with `(obj,)`, or `(obj, errors)` when `errors` is
given (`args_tuple`), and returns the first item of the 2-tuple it answers (codecs.rst: the
encoder "returns a tuple (output object, length consumed)"), a `TypeError` for any other answer,
and the encoder's exception with the note "encoding with '<encoding>' codec failed". The text
path (`str.encode`, `_PyCodec_LookupTextEncoding`) does exactly the same for a plain tuple, for a
codec without `_is_text_encoding`, and for one whose `_is_text_encoding` is true; it raises the
`LookupError` that points to `codecs.encode()` when that attribute is false, and the error of
reading it or of testing its truth. -/
def EncodePaths : Prop :=
  ∀ (W : World) (st : Reg) (obj : Val) (enc : List Nat) (errors : Option Str),
    match pyCodecLookup W st enc with
    | (st1, .error e) =>
      pyCodecEncode W st obj enc errors = (st1, .error ⟨e, []⟩) ∧
      encodeText W st obj enc errors = (st1, .error ⟨e, []⟩)
    | (st1, .ok codec) =>
      let args := obj :: (errors.map Val.str).toList
      let gen := (runOps W st1 (W.call (tupleItem codec 0) args).1,
        coderResult (W.call (tupleItem codec 0) args).2 "encoding"
          "encoder must return a tuple (object, integer)" (cstr enc))
      let refuse : Reg × NPy Val := (st1, .error ⟨lookupErr s!"'{toLeanString (trunc400 ((utf8Decode enc .strict).toOption.getD []))}' is not a text encoding; use {("codecs.encode()" : String)} to handle arbitrary codecs", []⟩)
      pyCodecEncode W st obj enc errors = gen ∧
      (isExactTuple codec = true → encodeText W st obj enc errors = gen) ∧
      (isExactTuple codec = false →
        match W.getattr codec "_is_text_encoding" with
        | .error e => encodeText W st obj enc errors = (st1, .error ⟨e, []⟩)
        | .ok none => encodeText W st obj enc errors = gen
        | .ok (some a) =>
          match W.truth a with
          | .ok true => encodeText W st obj enc errors = gen
          | .ok false => encodeText W st obj enc errors = refuse
          | .error e => encodeText W st obj enc errors = (st1, .error ⟨e, []⟩))

/-- **The same for codecs.decode and the text decode path** (`bytes.decode`). -/
def DecodePaths : Prop :=
  ∀ (W : World) (st : Reg) (obj : Val) (enc : List Nat) (errors : Option Str),
    match pyCodecLookup W st enc with
    | (st1, .error e) =>
      pyCodecDecode W st obj enc errors = (st1, .error ⟨e, []⟩) ∧
      decodeText W st obj enc errors = (st1, .error ⟨e, []⟩)
    | (st1, .ok codec) =>
      let args := obj :: (errors.map Val.str).toList
      let gen := (runOps W st1 (W.call (tupleItem codec 1) args).1,
        coderResult (W.call (tupleItem codec 1) args).2 "decoding"
          "decoder must return a tuple (object,integer)" (cstr enc))
      let refuse : Reg × NPy Val := (st1, .error ⟨lookupErr s!"'{toLeanString (trunc400 ((utf8Decode enc .strict).toOption.getD []))}' is not a text encoding; use {("codecs.decode()" : String)} to handle arbitrary codecs", []⟩)
      pyCodecDecode W st obj enc errors = gen ∧
      (isExactTuple codec = true → decodeText W st obj enc errors = gen) ∧
      (isExactTuple codec = false →
        match W.getattr codec "_is_text_encoding" with
        | .error e => decodeText W st obj enc errors = (st1, .error ⟨e, []⟩)
        | .ok none => decodeText W st obj enc errors = gen
        | .ok (some a) =>
          match W.truth a with
          | .ok true => decodeText W st obj enc errors = gen
          | .ok false => decodeText W st obj enc errors = refuse
          | .error e => decodeText W st obj enc errors = (st1, .error ⟨e, []⟩))

def CodecPaths : Prop := EncodePaths ∧ DecodePaths

theorem encodePaths_proven : EncodePaths := by
  intro W st obj enc errors
  have h0 := encodePaths0 W st obj enc errors
  rcases hl : pyCodecLookup W st enc with ⟨st1, r⟩
  rw [hl] at h0
  cases r with
  | error e => exact h0
  | ok codec =>
    simp only [argsTuple_eq] at h0
    obtain ⟨g1, g2, g3, g4⟩ := h0
    refine ⟨g1, fun hx => g2 (isTextCodec_exact W codec hx), fun hx => ?_⟩
    have ht := isTextCodec_other W codec hx
    rcases hg : W.getattr codec "_is_text_encoding" with e | _ | a
    · rw [hg] at ht; exact g4 e ht
    · rw [hg] at ht; exact g2 ht
    · rw [hg] at ht; simp only at ht
      simp only
      rcases htr : W.truth a with e | b
      · rw [htr] at ht; exact g4 e ht
      · rw [htr] at ht; cases b
        · exact g3 ht
        · exact g2 ht

theorem decodePaths_proven : DecodePaths := by
  intro W st obj enc errors
  have h0 := decodePaths0 W st obj enc errors
  rcases hl : pyCodecLookup W st enc with ⟨st1, r⟩
  rw [hl] at h0
  cases r with
  | error e => exact h0
  | ok codec =>
    simp only [argsTuple_eq] at h0
    obtain ⟨g1, g2, g3, g4⟩ := h0
    refine ⟨g1, fun hx => g2 (isTextCodec_exact W codec hx), fun hx => ?_⟩
    have ht := isTextCodec_other W codec hx
    rcases hg : W.getattr codec "_is_text_encoding" with e | _ | a
    · rw [hg] at ht; exact g4 e ht
    · rw [hg] at ht; exact g2 ht
    · rw [hg] at ht; simp only at ht
      simp only
      rcases htr : W.truth a with e | b
      · rw [htr] at ht; exact g4 e ht
      · rw [htr] at ht; cases b
        · exact g3 ht
        · exact g2 ht

theorem codecPaths_proven : CodecPaths := ⟨encodePaths_proven, decodePaths_proven⟩

/-! ## The error handler registry -/

theorem dictSet_lookupS (d : List (String × Val)) (k : String) (v : Val) :
    (dictSet d k v).lookup k = some v := by
  unfold dictSet
  split
  · rename_i h
    induction d with
    | nil => simp at h
    | cons e es ih =>
      simp only [List.map_cons, List.lookup]
      cases hb : e.1 == k
      · have hk : (k == e.1) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq] at hb ⊢; exact fun x => hb x.symm
        simp only [Bool.false_eq_true, if_false, hk]
        apply ih
        simpa [List.any_cons, hb] using h
      · simp
  · rename_i h
    induction d with
    | nil => simp [List.lookup]
    | cons e es ih =>
      have hb : (e.1 == k) = false := by
        cases hx : e.1 == k
        · rfl
        · exact absurd (by simp [List.any_cons, hx]) h
      have hk : (k == e.1) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq] at hb ⊢; exact fun x => hb x.symm
      simp only [List.cons_append, List.lookup, hk]
      apply ih
      intro x; apply h; simp [List.any_cons, x]

theorem lookup_filter_ne (d : List (String × Val)) (k : String) :
    (d.filter (·.1 != k)).lookup k = none := by
  induction d with
  | nil => rfl
  | cons e es ih =>
    by_cases he : e.1 = k
    · simp [List.filter, he, ih]
    · have hk : (k == e.1) = false := by simp; exact fun x => he x.symm
      have hne : (e.1 != k) = true := by simp [he]
      simp only [List.filter, hne, List.lookup, hk]
      exact ih

theorem any_lookup (d : List (String × Val)) (k : String) :
    d.any (·.1 == k) = (d.lookup k).isSome := by
  induction d with
  | nil => rfl
  | cons e es ih =>
    by_cases he : e.1 = k
    · simp [List.lookup, he]
    · have hk : (k == e.1) = false := by simp; exact fun x => he x.symm
      simp [List.lookup, he, hk, ih]

/-- **The error handler registry does what codecs.rst and `_unregister_error`'s docstring say.**
`register_error(name, h)` refuses a non-callable `h` and otherwise makes `lookup_error(name)`
return `h`, builtin names included; `lookup_error` of an unregistered name raises `LookupError`
naming it (cut to 400 bytes), and a NULL name means "strict"; `_unregister_error` refuses the
eight builtin names, and otherwise answers whether a custom handler was registered, after which
`lookup_error` of that name raises. -/
def ErrorRegistryDoc : Prop :=
  ∀ (W : World) (st : Reg) (name : String) (h : Val),
    (W.callable h = true → (codecsRegisterError W st name h).2 = .ok .none ∧
      codecsLookupError (codecsRegisterError W st name h).1 name = .ok h) ∧
    (W.callable h = false →
      codecsRegisterError W st name h = (st, .error (.typeError "handler must be callable"))) ∧
    lookupError st none = lookupError st (some "strict") ∧
    (st.errors.lookup name = none → codecsLookupError st name =
      .error (lookupErr s!"unknown error handler name '{toLeanString (trunc400 (lit name))}'")) ∧
    (name ∈ builtinNames → codecsUnregisterError st name =
      (st, .error (.valueError s!"cannot un-register built-in error handler '{name}'"))) ∧
    (name ∉ builtinNames → (codecsUnregisterError st name).2 = .ok (st.errors.lookup name).isSome ∧
      (codecsUnregisterError st name).1.errors.lookup name = none)

theorem errorRegistryDoc_proven : ErrorRegistryDoc := by
  intro W st name h
  refine ⟨fun hc => ?_, fun hc => ?_, rfl, fun hn => ?_, fun hb => ?_, fun hb => ?_⟩
  · simp [codecsRegisterError, codecsLookupError, registerError, hc, lookupError, dictSet_lookupS]
  · simp [codecsRegisterError, registerError, hc]
  · simp [codecsLookupError, lookupError, hn]
  · simp [codecsUnregisterError, unregisterError, List.contains_iff_mem, hb]
  · have hb' : builtinNames.contains name = false := by simpa [List.contains_iff_mem] using hb
    unfold codecsUnregisterError unregisterError
    simp only [hb', Bool.false_eq_true, if_false]
    rw [any_lookup]
    cases hl : st.errors.lookup name
    · simp [hl]
    · simp [lookup_filter_ne]

/-! ## _normalize_encoding -/

/-- The pieces of a name between separators (anything but an ASCII letter, digit or `.`), the
empty ones dropped. -/
def namePieces (s : List Nat) : List (List Nat) :=
  (s.splitBy (fun a b => (pyIsAlnum a || a == 46) == (pyIsAlnum b || b == 46))).filter
    (fun p => p.all fun c => pyIsAlnum c || c == 46)

/-- `encodings.normalize_encoding` as codecs.rst describes it: "all non-alphanumeric characters
except the dot used for Python package names are collapsed and replaced with a single
underscore, leading and trailing underscores are removed." -/
def docNormalize (s : List Nat) : List Nat := [95].intercalate (namePieces s)

/-- **_normalize_encoding follows its documentation on ASCII names** (codecs.rst,
`encodings.normalize_encoding`, which is `_codecs._normalize_encoding` since 3.15; "encoding
should be ASCII only" is its documented precondition). -/
def NormalizeEncodingDoc : Prop :=
  ∀ s : Str, (∀ c ∈ s, c < 128) → normalizeEncodingC s = .ok (docNormalize s)

theorem normalizeEncodingDoc_refuted : ¬ NormalizeEncodingDoc := by
  intro h
  have := h [97, 0, 98] (by decide)
  revert this
  decide

/-! ## escape_encode and escape_decode -/

set_option maxRecDepth 100000 in
theorem escapeByte_form : BytesObj.Bytes.EncForm escapeByte := by
  have hx : ∀ c, c < 256 → (c &&& 0xf0) >>> 4 = c / 16 ∧ c &&& 0xf = c % 16 := by decide
  intro c hc
  unfold escapeByte
  by_cases h1 : c = 39 ∨ c = 92
  · rw [if_pos h1]; right; left; exact ⟨rfl, by omega⟩
  · rw [if_neg h1]
    by_cases h2 : c = 9
    · subst h2; simp
    · rw [if_neg h2]
      by_cases h3 : c = 10
      · subst h3; simp
      · rw [if_neg h3]
        by_cases h4 : c = 13
        · subst h4; simp
        · rw [if_neg h4]
          by_cases h5 : c < 32 ∨ c ≥ 0x7f
          · rw [if_pos h5]
            right; right; right; right; right
            rw [(hx c hc).1, (hx c hc).2]
            rfl
          · rw [if_neg h5]
            left; exact ⟨rfl, by omega⟩

/-- **escape_decode undoes escape_encode.** For every bytes object, `codecs.escape_encode`
either raises `OverflowError` (only past `PY_SSIZE_T_MAX / 4` bytes) or returns escapes, with the
length of its input, that `codecs.escape_decode` decodes back to the input, with their own
length. -/
def EscapeRoundTrip : Prop :=
  ∀ b : Bytes, Bytes.Valid b →
    (b.length > ssizeMaxN / 4 ∧ escapeEncode b = .error (.overflowError "string is too large to encode")) ∨
    ∃ e, escapeEncode b = .ok (e, b.length) ∧ escapeDecode e none = .ok (b, e.length)

theorem escapeRoundTrip_proven : EscapeRoundTrip := by
  intro b hb
  by_cases hl : b.length > ssizeMaxN / 4
  · left; exact ⟨hl, by simp [escapeEncode, hl]⟩
  · right
    refine ⟨b.flatMap escapeByte, by simp [escapeEncode, hl, codecTuple], ?_⟩
    have hf := BytesObj.Bytes.flat_length _ escapeByte_form b hb
    have := BytesObj.Bytes.decode_flat escapeByte escapeByte_form b hb
      (2 * (b.flatMap escapeByte).length + 2) 0 [] (by omega)
    simp only [escapeDecode, codecTuple, BytesObj.Bytes.bytesDecodeEscape, BytesObj.Bytes.decodeEscape2]
    rw [this]
    simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

end PyLean.UnicodeObj.Codecs

namespace PyLean.UnicodeObj.Codecs

open PyLean PyLean.UnicodeObj

/-! ## register and unregister -/

theorem removeFirst_spec (f : Val) : ∀ (l : List Val),
    (removeFirst f l = none ∧ ∀ x ∈ l, x.is f = false) ∨
    ∃ pre g post, l = pre ++ g :: post ∧ (∀ x ∈ pre, x.is f = false) ∧ g.is f = true ∧
      removeFirst f l = some (pre ++ post)
  | [] => Or.inl ⟨rfl, by simp⟩
  | x :: xs => by
    simp only [removeFirst]
    by_cases hx : x.is f = true
    · right; exact ⟨[], x, xs, rfl, by simp, hx, by simp [hx]⟩
    · have hx' : x.is f = false := by simpa using hx
      rcases removeFirst_spec f xs with ⟨h1, h2⟩ | ⟨pre, g, post, h1, h2, h3, h4⟩
      · left; simp only [hx', Bool.false_eq_true, if_false, h1, Option.map_none, true_and]
        intro y hy; simp at hy; rcases hy with rfl | hy; exact hx'; exact h2 y hy
      · right
        refine ⟨x :: pre, g, post, by simp [h1], ?_, h3, by simp [hx', h4]⟩
        intro y hy; simp at hy; rcases hy with rfl | hy; exact hx'; exact h2 y hy

/-- **codecs.register and codecs.unregister do what their docstrings say.** `register`
refuses a non-callable with "argument must be callable" and otherwise appends the function to
the search path, cache untouched; `unregister` ("Unregister a codec search function and clear
the registry's cache. If the search function is not registered, do nothing.") removes the first
registration of that very object and empties the cache, or changes nothing. Both return
`None`. -/
def RegisterDoc : Prop :=
  ∀ (W : World) (st : Reg) (f : Val),
    (W.callable f = false → codecsRegister W st f = (st, .error (.typeError "argument must be callable"))) ∧
    (W.callable f = true → codecsRegister W st f = ({ st with path := st.path ++ [f] }, .ok .none)) ∧
    (codecsUnregister st f).2 = .ok .none ∧
    (((∀ x ∈ st.path, x.is f = false) ∧ (codecsUnregister st f).1 = st) ∨
     ∃ pre g post, st.path = pre ++ g :: post ∧ (∀ x ∈ pre, x.is f = false) ∧ g.is f = true ∧
       (codecsUnregister st f).1 = { st with path := pre ++ post, cache := [] })

theorem registerDoc_proven : RegisterDoc := by
  intro W st f
  refine ⟨fun h => by simp [codecsRegister, register, h], fun h => by simp [codecsRegister, register, h],
    rfl, ?_⟩
  rcases removeFirst_spec f st.path with ⟨h1, h2⟩ | ⟨pre, g, post, h1, h2, h3, h4⟩
  · left; exact ⟨h2, by simp [codecsUnregister, unregister, h1]⟩
  · right; exact ⟨pre, g, post, h1, h2, h3, by simp [codecsUnregister, unregister, h4]⟩

end PyLean.UnicodeObj.Codecs

namespace PyLean.UnicodeObj.Codecs

open PyLean PyLean.UnicodeObj

/-! ## The C API getters against Lib/codecs.py -/

/-- What `CodecInfo.__new__` sets up (Lib/codecs.py:94-107): the attributes `encode`, `decode`,
`streamreader` and `streamwriter` are the four items of the tuple. -/
def ItemsMatchAttrs (W : World) (info : Val) : Prop :=
  W.getattr info "encode" = .ok (some (tupleItem info 0)) ∧
  W.getattr info "decode" = .ok (some (tupleItem info 1)) ∧
  W.getattr info "streamreader" = .ok (some (tupleItem info 2)) ∧
  W.getattr info "streamwriter" = .ok (some (tupleItem info 3))

/-- **The C API getters and their twins in Lib/codecs.py agree.** For every registry, search
functions and name (that the `str` argument converter accepts): `PyCodec_KnownEncoding` is
whether `codecs.lookup` succeeds, and never raises; whenever the codec object's attributes are
its items, as `CodecInfo.__new__` makes them, `PyCodec_Encoder`/`Decoder` give what
`codecs.getencoder`/`getdecoder` give, and `PyCodec_StreamReader`/`StreamWriter(name, stream,
errors)` what `codecs.getreader`/`getwriter(name)(stream[, errors])` give;
`PyCodec_IncrementalEncoder`/`Decoder(name, errors)` give what
`codecs.getincrementalencoder`/`getincrementaldecoder(name)([errors])` give, except when that
attribute is `None`, where Python raises `LookupError(name)` and C tries to call `None`. -/
def CApiMatchesLib : Prop :=
  ∀ (W : World) (st : Reg) (name : Str) (enc : List Nat) (errors : Option Str) (stream : Val),
    strArg name = .ok enc →
    knownEncoding W st enc = ((codecsLookup W st name).1, (codecsLookup W st name).2.isOk) ∧
    (∀ st1 info, codecsLookup W st name = (st1, .ok info) → ItemsMatchAttrs W info →
      pyCodecEncoder W st enc = libGetAttr W st name "encode" ∧
      pyCodecDecoder W st enc = libGetAttr W st name "decode" ∧
      pyCodecStreamReader W st enc stream errors =
        libCall W (libGetAttr W st name "streamreader") (stream :: (errors.map Val.str).toList) ∧
      pyCodecStreamWriter W st enc stream errors =
        libCall W (libGetAttr W st name "streamwriter") (stream :: (errors.map Val.str).toList)) ∧
    (∀ attr, attr = "incrementalencoder" ∨ attr = "incrementaldecoder" →
      ∀ st1 info, codecsLookup W st name = (st1, .ok info) →
      (W.getattr info attr = .ok (some .none) →
        libCall W (libGetIncremental W st name attr) ((errors.map Val.str).toList) =
          (st1, .error (lookupErr (toLeanString name)))) ∧
      (W.getattr info attr ≠ .ok (some .none) →
        getIncremental W st enc errors attr =
          libCall W (libGetIncremental W st name attr) ((errors.map Val.str).toList))) ∧
    (∀ st1 e, codecsLookup W st name = (st1, .error e) →
      pyCodecEncoder W st enc = (st1, .error e) ∧ libGetAttr W st name "encode" = (st1, .error e))

theorem cApiMatchesLib_proven : CApiMatchesLib := by
  intro W st name enc errors stream harg
  have hl : codecsLookup W st name = pyCodecLookup W st enc := by simp [codecsLookup, harg]
  refine ⟨?_, fun st1 info h hm => ?_, fun attr _ st1 info h => ⟨fun hn => ?_, fun hn => ?_⟩,
    fun st1 e h => ?_⟩
  · rw [hl]; unfold knownEncoding
    rcases pyCodecLookup W st enc with ⟨s, r⟩
    cases r <;> rfl
  · rw [hl] at h
    obtain ⟨h0, h1, h2, h3⟩ := hm
    simp only [pyCodecEncoder, pyCodecDecoder, pyCodecStreamReader, pyCodecStreamWriter, codecGetitem,
      getStream, libGetAttr, libCall, hl, h, pyAttr, h0, h1, h2, h3]
    refine ⟨by first | trivial | rfl, by first | trivial | rfl, ?_, ?_⟩ <;> cases errors <;>
      first | trivial | rfl
  · rw [hl] at h
    simp only [libCall, libGetIncremental, libGetAttr, hl, h, pyAttr, hn]
  · rw [hl] at h
    simp only [getIncremental, makeIncremental, libCall, libGetIncremental, libGetAttr, hl, h, pyAttr]
    rcases hg : W.getattr info attr with e | _ | a
    · rfl
    · rfl
    · cases a <;> (try exact absurd hg hn) <;> cases errors <;> rfl
  · rw [hl] at h
    simp [pyCodecEncoder, codecGetitem, libGetAttr, hl, h]

end PyLean.UnicodeObj.Codecs

namespace PyLean.UnicodeObj.Codecs

open PyLean PyLean.UnicodeObj

/-! ## normalizestring -/

/-- What `normalizestring` does to one character: a space becomes `-`, an ASCII capital its
lower case, anything else stays. -/
def normChar (c : Nat) : Nat := if c = 32 then 45 else if 65 ≤ c ∧ c ≤ 90 then c + 32 else c

theorem map_eq_self {f : Nat → Nat} : ∀ (l : List Nat), (∀ x ∈ l, f x = x) → l.map f = l
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.map_cons, h x (by simp), map_eq_self xs (fun y hy => h y (by simp [hy]))]

theorem norm_char_bytes (c : Nat) :
    (utf8EncodeChar c).map (fun ch => if ch = 32 then 45 else cLower ch) = utf8EncodeChar (normChar c) := by
  by_cases h : c < 0x80
  · have hn : normChar c < 0x80 := by unfold normChar; split <;> (try split) <;> omega
    simp only [utf8EncodeChar, h, if_true, hn, List.map_cons, List.map_nil, normChar, cLower]
    split <;> (try split) <;> (try split) <;> simp_all <;> omega
  · have hn : normChar c = c := by unfold normChar; split <;> (try split) <;> omega
    rw [hn]
    apply map_eq_self
    intro x hx
    have : 128 ≤ x := by
      unfold utf8EncodeChar at hx
      simp only [h, if_false] at hx
      split at hx <;> (try split at hx) <;> simp at hx <;> omega
    have h1 : x ≠ 32 := by omega
    have h2 : ¬ (65 ≤ x ∧ x ≤ 90) := by omega
    simp only [h1, if_false, cLower, h2]

/-- **normalizestring lower-cases ASCII letters and turns spaces into hyphens**
(codecs.c:84-115; codecs.rst, `lookup`: "all ASCII letters are converted to lower case, spaces
are replaced with hyphens"). For the C string of every name that has no lone surrogate (the
`str` converter refuses those): an `OverflowError` past `PY_SSIZE_T_MAX` bytes, otherwise the
name with those two changes and every other character, non-ASCII ones included, unchanged. -/
def NormalizeStringSpec : Prop :=
  ∀ s : Str, (∀ c ∈ s, c ≤ maxUnicode ∧ isSurrogate c = false) →
    normalizestring (s.flatMap utf8EncodeChar) =
      if (s.flatMap utf8EncodeChar).length > ssizeMaxN then .error (.overflowError "string is too large")
      else .ok (s.map normChar)

theorem normalizeStringSpec_proven : NormalizeStringSpec := by
  intro s hs
  unfold normalizestring
  split
  · rfl
  · have hm : (s.flatMap utf8EncodeChar).map (fun ch => if ch = 32 then 45 else cLower ch) =
        (s.map normChar).flatMap utf8EncodeChar := by
      rw [List.flatMap_map, List.map_flatMap]
      congr 1; funext c; exact norm_char_bytes c
    rw [hm]
    have hs' : ∀ c ∈ s.map normChar, c ≤ maxUnicode ∧ isSurrogate c = false := by
      intro c hc
      simp only [List.mem_map] at hc
      obtain ⟨x, hx, rfl⟩ := hc
      have := hs x hx
      have hm : maxUnicode = 0x10FFFF := rfl
      unfold normChar
      split <;> (try split) <;> simp_all [isSurrogate] <;> omega
    exact (utf8RoundTrip_proven _ hs').2

end PyLean.UnicodeObj.Codecs

namespace PyLean.UnicodeObj.Codecs

open PyLean PyLean.UnicodeObj

/-! ## The getters on a raw 4-tuple -/

/-- **`PyCodec_Encoder` and `codecs.getencoder` agree on every codec**, without the
`CodecInfo` invariant of `CApiMatchesLib`. False: `_codecs.register`'s docstring lets a search
function return "a tuple of functions (encoder, decoder, stream_reader, stream_writer)", and
`codecs.lookup` hands that tuple back as is; C takes its item 0, Python asks for an `encode`
attribute a tuple does not have. -/
def CApiMatchesLibAll : Prop :=
  ∀ (W : World) (st : Reg) (name : Str) (enc : List Nat), strArg name = .ok enc →
    pyCodecEncoder W st enc = libGetAttr W st name "encode"

/-- One search function, which answers with a plain 4-tuple. -/
def rawTupleWorld : World where
  call f _ :=
    match f with
    | .obj 1 _ => ([], .ok (.tuple 100 [.obj 200 "function", .obj 201 "function",
        .obj 202 "function", .obj 203 "function"] true))
    | _ => ([], .ok .none)
  getattr _ _ := .ok none
  truth _ := .ok true
  callable _ := true

def rawTupleReg : Reg := { path := [.obj 1 "function"], cache := [], errors := [] }

def isOkVal : Py Val → Bool
  | .ok _ => true
  | .error _ => false

theorem rawTuple_c : isOkVal (pyCodecEncoder rawTupleWorld rawTupleReg (lit "x")).2 = true := by rfl
theorem rawTuple_py : isOkVal (libGetAttr rawTupleWorld rawTupleReg (lit "x") "encode").2 = false := by rfl

theorem cApiMatchesLibAll_refuted : ¬ CApiMatchesLibAll := by
  intro h
  have := congrArg (fun r => isOkVal r.2) (h rawTupleWorld rawTupleReg (lit "x") (lit "x") rfl)
  simp only [rawTuple_c, rawTuple_py] at this
  cases this

end PyLean.UnicodeObj.Codecs
