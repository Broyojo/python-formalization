import PyLean.BytesObj.Bytes.FromListLemmas

/-!
Properties of the `bytes` methods, fourth part.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## strip, removeprefix, removesuffix -/

/-- `bytes.strip` and `bytearray.strip` (`do_strip` tests `Py_ISSPACE`, the bytearray helper
searches the six-byte string) strip the same bytes, for every byte string and every direction,
and the same goes for an explicit set. Stripping twice changes nothing more. -/
def StripTwins : Prop :=
  ∀ (s : Seq) (t : StripType),
    bytesStrip s none t = bytearrayStrip s none t ∧
    (∀ cs : Seq, bytesStrip s (some cs) t = bytearrayStrip s (some cs) t)

theorem stripTwins_proven : StripTwins := by
  intro s t
  refine ⟨?_, fun cs => rfl⟩
  have e : byteSpace = (fun c => [9, 10, 13, 12, 11, 32].contains c) := by
    funext c
    apply Bool.eq_iff_iff.mpr
    simp [byteSpace]
    omega
  simp only [bytesStrip, bytearrayStrip, Option.getD_none, e]

/-- `removeprefix`/`removesuffix`: with a non-empty matching affix, the affix and the result
rebuild the original; otherwise the original comes back, for `bytes` and `bytearray`. -/
def RemoveAffix : Prop :=
  ∀ s p : Seq,
    (p ≠ [] → p.isPrefixOf s = true → p ++ bytesRemoveprefix s p = s) ∧
    (p.isPrefixOf s = false → bytesRemoveprefix s p = s) ∧
    (p ≠ [] → p.isSuffixOf s = true → bytesRemovesuffix s p ++ p = s) ∧
    bytesRemoveprefix s [] = s ∧ bytesRemovesuffix s [] = s

theorem removeAffix_proven : RemoveAffix := by
  intro s p
  have hsuf : p.isSuffixOf s = true → p.length ≤ s.length ∧
      p.isPrefixOf (s.drop (s.length - p.length)) = true := by
    intro h
    have h2 : p <:+ s := List.isSuffixOf_iff_suffix.mp h
    have hle := h2.length_le
    refine ⟨hle, ?_⟩
    obtain ⟨t, rfl⟩ := h2
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hne hp
    have h2 := isPrefixOf_eq_true_iff.mp hp
    have hl : p.length > 0 := List.length_pos_iff.mpr hne
    unfold bytesRemoveprefix
    rw [if_pos ⟨h2.1, hl, hp⟩]
    conv => rhs; rw [← List.take_append_drop p.length s, h2.2]
  · intro hp
    have : ¬ (s.length ≥ p.length ∧ p.length > 0 ∧ p.isPrefixOf s = true) := by
      intro h; simp [hp] at h
    unfold bytesRemoveprefix
    rw [if_neg this]
  · intro hne hp
    obtain ⟨h1, h2⟩ := hsuf hp
    have hl : p.length > 0 := List.length_pos_iff.mpr hne
    unfold bytesRemovesuffix
    rw [if_pos ⟨h1, hl, h2⟩]
    have e := isPrefixOf_eq_true_iff.mp h2
    have e2 : s.drop (s.length - p.length) = p := by
      have hlen : (s.drop (s.length - p.length)).length = p.length := by simp; omega
      have e3 := e.2
      rwa [List.take_of_length_le (by omega)] at e3
    conv => rhs; rw [← List.take_append_drop (s.length - p.length) s, e2]
  · simp [bytesRemoveprefix]
  · simp [bytesRemovesuffix]

/-! ## Encoders -/

theorem findIdx_none_lt (s : Seq) (k : Nat) (h : ∀ c ∈ s, c < k) : s.findIdx? (· ≥ k) = none := by
  rw [List.findIdx?_eq_none_iff]
  intro x hx
  have := h x hx
  simp
  omega

/-- `bytes.decode` and `bytes(str, encoding, errors)` through the shortcut codecs:
`s.decode('latin-1')` is the code points of the bytes whatever `errors` is, and
`bytes(text, 'latin-1')` inverts it; `ascii` accepts a string below 128 and reports the first byte at
or above it with its position; utf-8, the default (`encoding=NULL`, unicodeobject.c:3587-3589), and any
spelling `_Py_normalize_encoding` folds to it, decodes what `bytes(text, 'utf-8')` wrote for every
text without surrogates; and an empty input decodes to `''` before the encoding or the handler is
looked at (:3480-3485), so even an unknown codec gives `''`. -/
def DecodeRoundTrip : Prop :=
  (∀ (s : Seq) (err : Option String), (∀ c ∈ s, c < 256) → bytesDecode s (some "latin-1") err = .ok s) ∧
  (∀ s : Seq, (∀ c ∈ s, c < 256) → bytesNew (some (.str s)) (some "latin-1") none = .ok s) ∧
  (∀ (pre : Seq) (x : Nat) (post : Seq), (∀ c ∈ pre, c < 128) → x ≥ 128 →
    bytesDecode pre (some "ascii") none = .ok pre ∧
    bytesDecode (pre ++ x :: post) (some "ascii") none =
      .error (UnicodeObj.decodeError "ascii" (pre ++ x :: post) pre.length (pre.length + 1)
        "ordinal not in range(128)")) ∧
  (∀ s : Seq, (∀ c ∈ s, c ≤ UnicodeObj.maxUnicode ∧ UnicodeObj.isSurrogate c = false) →
    bytesNew (some (.str s)) (some "utf-8") none = .ok (s.flatMap UnicodeObj.utf8EncodeChar) ∧
    bytesDecode (s.flatMap UnicodeObj.utf8EncodeChar) none none = .ok s ∧
    bytesDecode (s.flatMap UnicodeObj.utf8EncodeChar) (some "UTF8") (some "strict") = .ok s) ∧
  (∀ enc err : Option String, bytesDecode [] enc err = .ok [])

theorem sc_latin1 : shortcutOfName (some "latin-1") = .latin1 := by decide
theorem sc_ascii : shortcutOfName (some "ascii") = .ascii := by decide
theorem sc_utf8 : shortcutOfName (some "utf-8") = .utf8 := by decide
theorem sc_UTF8 : shortcutOfName (some "UTF8") = .utf8 := by decide
theorem eh_strict : errHandlerOf (some "strict") = some .strict := by decide

theorem flatMap_utf8_nil (s : Seq) (h : (s.flatMap UnicodeObj.utf8EncodeChar).length = 0) : s = [] := by
  cases s with
  | nil => rfl
  | cons c cs =>
    exfalso
    simp only [List.flatMap_cons, List.length_append] at h
    have : (UnicodeObj.utf8EncodeChar c).length ≠ 0 := by
      unfold UnicodeObj.utf8EncodeChar; split <;> (try split) <;> (try split) <;> simp
    omega

theorem decodeRoundTrip_proven : DecodeRoundTrip := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s err hs
    unfold bytesDecode unicodeDecode
    rw [sc_latin1]
    by_cases h0 : s.length = 0
    · simp [h0, List.eq_nil_of_length_eq_zero h0]
    · simp [h0, UnicodeObj.latin1Decode]
  · intro s hs
    have := UnicodeObj.latin1RoundTrip_proven s .strict (fun _ => none) hs
    simp only [UnicodeObj.latin1Decode] at this
    simp [bytesNew, unicodeEncode, sc_latin1, errHandlerOf, this]
  · intro pre x post hp hx
    obtain ⟨h1, h2⟩ := UnicodeObj.asciiStrict_proven pre x post hp hx
    constructor
    · unfold bytesDecode unicodeDecode
      rw [sc_ascii]
      by_cases h0 : pre.length = 0
      · simp [h0, List.eq_nil_of_length_eq_zero h0]
      · simp [h0, errHandlerOf, h1]
    · unfold bytesDecode unicodeDecode
      rw [sc_ascii]
      simp [errHandlerOf, h2]
  · intro s hs
    obtain ⟨h1, h2⟩ := UnicodeObj.utf8RoundTrip_proven s hs
    refine ⟨?_, ?_, ?_⟩
    · simp [bytesNew, unicodeEncode, sc_utf8, errHandlerOf, h1]
    · unfold bytesDecode unicodeDecode
      by_cases h0 : (s.flatMap UnicodeObj.utf8EncodeChar).length = 0
      · simp [h0, flatMap_utf8_nil s h0]
      · rw [if_neg h0]; simp [shortcutOfName, errHandlerOf, h2]
    · unfold bytesDecode unicodeDecode
      rw [sc_UTF8, eh_strict]
      by_cases h0 : (s.flatMap UnicodeObj.utf8EncodeChar).length = 0
      · simp [h0, flatMap_utf8_nil s h0]
      · rw [if_neg h0]; simp [h2]
  · intro enc err
    simp [bytesDecode, unicodeDecode]

/-! ## The constructor -/

theorem byteItem_ok (c : Nat) (hc : c < 256) : byteItem (.int c) = .ok c := by
  have h : ¬ ((c : Int) < 0 ∨ (c : Int) ≥ 256) := by omega
  simp [byteItem, asSsizeClamp, Obj.index?, clamp_byte c hc, h, bind, Except.bind, pure, Except.pure]

theorem items_ok (vals : Seq) (h : ∀ c ∈ vals, c < 256) :
    bytesFromItems (vals.map (fun (c : Nat) => Obj.int (c : Int))) = .ok vals := by
  induction vals with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, bytesFromItems, bind, Except.bind, pure, Except.pure]
    rw [byteItem_ok c (h c (by simp)), ih (fun x hx => h x (by simp [hx]))]

/-- `bytes(x)`: a list, a tuple and a generator of ints in `range(256)` give those bytes
(three separate C loops); an int `n ≥ 0` gives `n` zero bytes and a negative one
`ValueError`; a `str` without an encoding is a `TypeError`; a buffer gives its contents;
a bad item stops the loop with `ValueError`. Hypothesis of the list cases: a list that can exist
(fewer than `2^46` items), since `_PyBytes_FromList` allocates its writer for the list's size first. -/
def BytesNewSpec : Prop :=
  (∀ vals : Seq, (∀ c ∈ vals, c < 256) → (vals.length : Int) + 33 < 2 ^ 46 →
    let items := vals.map (fun (c : Nat) => Obj.int (c : Int))
    bytesNew (some (.list items)) none none = .ok vals ∧
    bytesNew (some (.tuple items)) none none = .ok vals ∧
    bytesNew (some (.iter items)) none none = .ok vals) ∧
  (∀ n : Nat, (n : Int) ≠ 0 → (n : Int) + 33 < 2 ^ 47 →
    bytesNew (some (.int n)) none none = .ok (List.replicate n 0)) ∧
  (∀ v : Int, ssizeMin ≤ v → v < 0 →
    bytesNew (some (.int v)) none none = .error (.valueError "negative count")) ∧
  (∀ cs : Seq, bytesNew (some (.str cs)) none none =
    .error (.typeError "string argument without an encoding")) ∧
  (∀ (s a : Seq), bytesNew (some (.memview s a)) none none = .ok s ∧
    bytesNew (some (.bytearray s)) none none = .ok s) ∧
  bytesNew none none none = .ok [] ∧
  (∀ (rest : List Obj), (rest.length : Int) + 34 < 2 ^ 46 →
    bytesNew (some (.list (.int 256 :: rest))) none none =
    .error (.valueError "bytes must be in range(0, 256)"))

theorem bytesNewSpec_proven : BytesNewSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro vals h hl
    have := items_ok vals h
    have hw : writerCreate 64 false = .ok { overallocate := true, size := 64 } := by decide
    have hfl := bytesFromList_plain (vals.map (fun (c : Nat) => Obj.int (c : Int))) (by simpa using hl)
    rw [this, List.map_map] at hfl
    simp only
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [bytesNew, Obj.index?, bytesFromObject, Obj.buffer?, iterItems?, this, getIterOr, lengthHint,
        iterFinish, hw, hfl, bind, Except.bind, pure, Except.pure]
  · intro n h0 hs
    have h1 : ssizeMin ≤ (n : Int) ∧ (n : Int) ≤ ssizeMax := by
      rw [ssizeMax_val, show ssizeMin = -9223372036854775808 by decide]; omega
    have h2 : ¬ ((n : Int) < 0) := by omega
    simp [bytesNew, Obj.index?, countOf, h1, h2, bytesFromSize_ok n hs]
  · intro v h1 h2
    have h3 : ssizeMin ≤ v ∧ v ≤ ssizeMax := by
      rw [ssizeMax_val]; omega
    simp [bytesNew, Obj.index?, countOf, h3, h2]
  · intro cs
    simp [bytesNew]
  · intro s a
    simp [bytesNew, Obj.index?, bytesFromObject, Obj.buffer?]
  · simp [bytesNew, bytesFromStringAndSize]
  · intro rest hr
    have hfl := bytesFromList_plain (.int 256 :: rest) (by simp; omega)
    have c256 : clampSsize (256 : Int) = 256 := clamp_id 256 (by decide) (by decide)
    have h : byteItem (.int 256) = .error (.valueError "bytes must be in range(0, 256)") := by
      simp [byteItem, asSsizeClamp, Obj.index?, c256, bind, Except.bind]
      rfl
    simp only [bytesNew, Obj.index?, bytesFromObject, Obj.buffer?, List.map_cons] at hfl ⊢
    rw [hfl]
    simp [bytesFromItems, h, bind, Except.bind]

/-! ## The iterator -/

/-- `n` calls of `next`, collecting the values until the first stop. -/
def striterDrain : Nat → StrIter → List Nat
  | 0, _ => []
  | n + 1, it =>
    match striterNext it with
    | (some v, it') => v :: striterDrain n it'
    | (none, _) => []

/-- `iter(b)` yields the bytes in order and then stops for good; `__length_hint__` counts
what is left; `__setstate__` clamps into `[0, len]`; and rebuilding from `__reduce__`
restores the iterator (which is what pickling a partly used iterator needs). -/
def BytesIterSpec : Prop :=
  (∀ s : Seq, striterDrain (s.length + 1) (bytesIter s) = s) ∧
  (∀ (s : Seq) (i : Int), striterLen { seq := some s, index := i } = (s.length : Int) - i) ∧
  (∀ (it : StrIter), it.seq = none → (striterNext it).1 = none ∧ striterLen it = 0) ∧
  (∀ (s : Seq) (i : Int), 0 ≤ i → i ≤ s.length → i ≤ ssizeMax →
    striterSetstate (bytesIter s) i = .ok { seq := some s, index := i }) ∧
  (∀ (s : Seq) (i : Int), i < 0 → ssizeMin ≤ i →
    striterSetstate (bytesIter s) i = .ok (bytesIter s))

theorem drain_from (s : Seq) (k : Nat) (hk : k ≤ s.length) (n : Nat) (hn : s.length - k + 1 ≤ n) :
    striterDrain n { seq := some s, index := (k : Int) } = s.drop k := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    simp only [striterDrain, striterNext]
    by_cases h : k < s.length
    · have hi : (k : Int) < s.length := by omega
      simp only [hi, if_true]
      have e : ((k : Int) + 1) = ((k + 1 : Nat) : Int) := by omega
      simp only [e]
      rw [ih (k + 1) (by omega) (by omega)]
      have hd : s.getD (k : Int).toNat 0 = s[k] := by simp [List.getD, h]
      rw [hd, ← List.drop_eq_getElem_cons h]
    · have e : k = s.length := by omega
      subst e
      simp

theorem bytesIterSpec_proven : BytesIterSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s
    have := drain_from s 0 (by omega) (s.length + 1) (by omega)
    simpa [bytesIter] using this
  · intro s i
    rfl
  · intro it h
    simp [striterNext, striterLen, h]
  · intro s i h0 h1 h2
    have h3 : ssizeMin ≤ i := by rw [show ssizeMin = -9223372036854775808 by decide]; omega
    have h4 : ¬ (i < 0) := by omega
    have h5 : ¬ (i > s.length) := by omega
    simp [striterSetstate, Sequences.asSsize, h2, h3, bytesIter, h4, h5, bind, Except.bind, pure,
      Except.pure]
  · intro s i h0 h1
    have h3 : i ≤ ssizeMax := by rw [show ssizeMax = 9223372036854775807 by decide]; omega
    simp [striterSetstate, Sequences.asSsize, h1, h3, bytesIter, h0, bind, Except.bind, pure,
      Except.pure]

/-! ## The hash cache -/

/-- The cached hash, for any `Py_HashBuffer` that never returns the marker `-1` (its
documented contract): `hash(b)` is the hash of the contents, whether or not the cache was
filled, the second call hits the cache, a subclass copy keeps the cache, and a resize that
changes the size invalidates it. -/
def BytesHashCache : Prop :=
  ∀ (hb : Seq → Int) (o : BytesSt), (∀ s, hb s ≠ -1) → (o.shash = -1 ∨ o.shash = hb o.data) →
    (bytesHash hb o).1 = hb o.data ∧
    (bytesHash hb (bytesHash hb o).2).1 = hb o.data ∧
    (bytesHash hb o).2.data = o.data ∧
    (bytesHash hb (bytesSubtypeNew o)).1 = hb o.data ∧
    ∀ (n : Nat) (o' : BytesSt), (n : Int) ≠ o.data.length → bytesResize o n = .ok o' →
      o'.shash = -1

theorem bytesHashCache_proven : BytesHashCache := by
  intro hb o hne hc
  have h1 : (bytesHash hb o).1 = hb o.data ∧ (bytesHash hb o).2.data = o.data ∧
      (bytesHash hb o).2.shash = hb o.data := by
    rcases hc with h | h
    · simp [bytesHash, h]
    · simp [bytesHash, h, hne]
  refine ⟨h1.1, ?_, h1.2.1, ?_, ?_⟩
  · have hC : ∀ o' : BytesSt, o'.shash ≠ -1 → (bytesHash hb o').1 = o'.shash := by
      intro o' h
      simp [bytesHash, h]
    rw [hC _ (by rw [h1.2.2]; exact hne _), h1.2.2]
  · rcases hc with h | h
    · simp [bytesHash, bytesSubtypeNew, h]
    · simp [bytesHash, bytesSubtypeNew, h, hne]
  · intro n o' hn h
    unfold bytesResize at h
    simp only [bind, Except.bind] at h
    split at h
    · simp at h
    · simp only [hn, if_false, pure, Except.pure, Except.ok.injEq] at h
      subst h
      rfl

end PyLean.BytesObj.Bytes
