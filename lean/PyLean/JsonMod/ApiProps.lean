import PyLean.JsonMod.CApi
import PyLean.JsonMod.ChunkProps
import PyLean.JsonMod.DecProps
import PyLean.JsonMod.RoundTripTop

/-!
Properties of the public API and of the C wrappers.
-/

namespace PyLean.JsonMod

open PyLean

/-! ### `JSONDecodeError` -/

theorem rfindNl_bounds (doc : PStr) (pos : Int) (h0 : 0 ≤ pos) :
    -1 ≤ rfindNl doc pos ∧ rfindNl doc pos < pos := by
  unfold rfindNl
  simp only
  cases hl : ((pySlice doc 0 pos).zipIdx.filter (·.1 == 10)).getLast? with
  | none => simp only; omega
  | some p =>
    obtain ⟨c, i⟩ := p
    simp only
    have hm := List.mem_of_getLast? hl
    have hm2 := (List.mem_filter.mp hm).1
    have hlt : i < (pySlice doc 0 pos).length := by
      have := (List.mem_zipIdx hm2).2.1
      simpa using this
    have hb : (pySlice doc 0 pos).length ≤ pos.toNat := by
      simp only [pySlice, sliceBound, List.length_take]
      have : ¬ ((0 : Int) < 0) := by omega
      simp only [this, ↓reduceIte, Int.toNat_zero, Nat.sub_zero]
      split <;> omega
    omega

/-- `JSONDecodeError(*e.__reduce__()[1])` has the same attributes and text as
`e`, for every message, document and position; `str(e)` is what the decoders'
errors print; and for `pos >= 0`, `lineno >= 1` and `1 <= colno <= pos + 1`. -/
def JdeReduce : Prop :=
  ∀ (msg : String) (doc : PStr) (pos : Int),
    (let e := jdeInit msg doc pos
     let r := jdeReduce e
     jdeInit r.1 r.2.1 r.2.2 = e) ∧
    (DErr.jde msg pos).toPy doc = .named "JSONDecodeError" (jdeInit msg doc pos).errmsg ∧
    (0 ≤ pos → 1 ≤ (jdeInit msg doc pos).lineno ∧ 1 ≤ (jdeInit msg doc pos).colno ∧
      (jdeInit msg doc pos).colno ≤ pos + 1)

theorem jdeReduce_proven : JdeReduce := by
  intro msg doc pos
  refine ⟨rfl, rfl, ?_⟩
  intro h0
  have := rfindNl_bounds doc pos h0
  simp only [jdeInit]
  omega

/-! ### `detect_encoding` -/

theorem startsWith_cons (a : Nat) (b p : List Nat) :
    startsWith (a :: b) (a :: p) = startsWith b p := by
  simp [startsWith]

/-- A `str` whose first two characters are ASCII and not NUL (what RFC 4627
section 3 relies on, and any JSON text without a leading NUL), encoded in one
of the five encodings without a BOM, is detected as that encoding. -/
def DetectEncoding : Prop :=
  ∀ (e : TextEnc) (a b : Nat) (t : PStr), 0 < a → a < 128 → 0 < b → b < 128 →
    detectEncoding (e.encode (a :: b :: t)) = e.name

/-- The same for a text of one character. -/
def DetectEncoding1 : Prop :=
  ∀ (e : TextEnc) (a : Nat), 0 < a → a < 128 → detectEncoding (e.encode [a]) = e.name

/-- With a BOM, `detect_encoding` names the codec that consumes it. -/
def DetectBom : Prop :=
  ∀ b : List Nat,
    detectEncoding (bomUtf8 ++ b) = "utf-8-sig" ∧
    detectEncoding (bomU32Le ++ b) = "utf-32" ∧ detectEncoding (bomU32Be ++ b) = "utf-32" ∧
    (b.take 2 ≠ [0, 0] → detectEncoding (bomU16Le ++ b) = "utf-16") ∧
    detectEncoding (bomU16Be ++ b) = "utf-16"

theorem detectBom_proven : DetectBom := by
  intro b
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [detectEncoding, startsWith, bomUtf8, bomU32Be, bomU32Le, bomU16Be, bomU16Le]
  · simp [detectEncoding, startsWith, bomU32Be, bomU32Le]
  · simp [detectEncoding, startsWith, bomU32Be, bomU32Le]
  · intro h
    have : ¬ (b.take 2 = [0, 0]) := h
    simp [detectEncoding, startsWith, bomU32Be, bomU32Le, bomU16Be, bomU16Le, this]
  · simp [detectEncoding, startsWith, bomU32Be, bomU32Le, bomU16Be, bomU16Le]

/-- `detect_encoding` on four leading bytes with no BOM. -/
theorem detect_ge4 (a b c d : Nat) (t : List Nat)
    (h1 : startsWith (a :: b :: c :: d :: t) bomU32Be = false)
    (h2 : startsWith (a :: b :: c :: d :: t) bomU32Le = false)
    (h3 : startsWith (a :: b :: c :: d :: t) bomU16Be = false)
    (h4 : startsWith (a :: b :: c :: d :: t) bomU16Le = false)
    (h5 : startsWith (a :: b :: c :: d :: t) bomUtf8 = false) :
    detectEncoding (a :: b :: c :: d :: t) =
      if a = 0 then (if b ≠ 0 then "utf-16-be" else "utf-32-be")
      else if b = 0 then (if c ≠ 0 ∨ d ≠ 0 then "utf-16-le" else "utf-32-le")
      else "utf-8" := by
  have hl : 4 ≤ (a :: b :: c :: d :: t).length := by simp
  simp only [detectEncoding, h1, h2, h3, h4, h5, Bool.false_or, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
    List.getD_cons_zero, List.getD_cons_succ, hl, ge_iff_le]

theorem startsWith_false_head {a c : Nat} {t p : List Nat} (h : a ≠ c) : startsWith (a :: t) (c :: p) = false := by
  simp [startsWith, h]

theorem detectEncoding_proven : DetectEncoding := by
  intro e a b t ha ha' hb hb'
  have u8 : ∀ c, c < 128 → utf8Enc1 c = [c] := by intro c h; simp [utf8Enc1, h]
  have u16 : ∀ le c, c < 128 → utf16Enc1 le c = if le then [c, 0] else [0, c] := by
    intro le c h
    have e1 : c % 256 = c := Nat.mod_eq_of_lt (by omega)
    have e2 : c / 256 = 0 := Nat.div_eq_of_lt (by omega)
    have e3 : c < 0x10000 := by omega
    simp [utf16Enc1, e1, e2, e3]
  have u32 : ∀ le c, c < 128 → utf32Enc1 le c = if le then [c, 0, 0, 0] else [0, 0, 0, c] := by
    intro le c h
    have e1 : c % 256 = c := Nat.mod_eq_of_lt (by omega)
    have e2 : c / 256 = 0 := Nat.div_eq_of_lt (by omega)
    have e3 : c / 65536 = 0 := Nat.div_eq_of_lt (by omega)
    have e4 : c / 16777216 = 0 := Nat.div_eq_of_lt (by omega)
    cases le <;> simp [utf32Enc1, e1, e2, e3, e4]
  have a0 : a ≠ 0 := by omega
  have b0 : b ≠ 0 := by omega
  cases e with
  | utf8 =>
    simp only [TextEnc.encode, List.flatMap_cons, u8 a ha', u8 b hb', TextEnc.name, List.cons_append, List.nil_append]
    cases h : t.flatMap utf8Enc1 with
    | nil =>
      -- two bytes
      have hn : detectEncoding [a, b] = "utf-8" := by
        have n1 : a ≠ 0xfe := by omega
        have n2 : a ≠ 0xff := by omega
        have n3 : a ≠ 0xef := by omega
        simp [detectEncoding, startsWith, bomU32Be, bomU32Le, bomU16Be, bomU16Le, bomUtf8, a0, b0, n1, n2, n3]
      exact hn
    | cons c r =>
      cases r with
      | nil =>
        have n1 : a ≠ 0xfe := by omega
        have n2 : a ≠ 0xff := by omega
        have n3 : a ≠ 0xef := by omega
        simp [detectEncoding, startsWith, bomU32Be, bomU32Le, bomU16Be, bomU16Le, bomUtf8, a0, n1, n2, n3]
      | cons d r =>
        rw [detect_ge4 a b c d r (startsWith_false_head a0) (startsWith_false_head (by omega))
          (startsWith_false_head (by omega)) (startsWith_false_head (by omega)) (startsWith_false_head (by omega))]
        simp [a0, b0]
  | utf16 le =>
    simp only [TextEnc.encode, List.flatMap_cons, u16 le a ha', u16 le b hb']
    cases le with
    | true =>
      simp only [↓reduceIte, List.cons_append, List.nil_append, TextEnc.name]
      rw [detect_ge4 a 0 b 0 _ (startsWith_false_head a0) (startsWith_false_head (by omega))
        (startsWith_false_head (by omega)) (startsWith_false_head (by omega)) (startsWith_false_head (by omega))]
      simp [a0, b0]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append, TextEnc.name]
      have h1 : startsWith (0 :: a :: 0 :: b :: t.flatMap (utf16Enc1 false)) bomU32Be = false := by
        simp [startsWith, bomU32Be, a0]
      rw [detect_ge4 0 a 0 b _ h1 (startsWith_false_head (by omega))
        (startsWith_false_head (by omega)) (startsWith_false_head (by omega)) (startsWith_false_head (by omega))]
      simp [a0]
  | utf32 le =>
    simp only [TextEnc.encode, List.flatMap_cons, u32 le a ha']
    cases le with
    | true =>
      simp only [↓reduceIte, List.cons_append, TextEnc.name]
      rw [detect_ge4 a 0 0 0 _ (startsWith_false_head a0) (startsWith_false_head (by omega))
        (startsWith_false_head (by omega)) (startsWith_false_head (by omega)) (startsWith_false_head (by omega))]
      simp [a0]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, List.cons_append, TextEnc.name]
      generalize ([] : List Nat) ++ (utf32Enc1 false b ++ List.flatMap (utf32Enc1 false) t) = R
      have h1 : startsWith (0 :: 0 :: 0 :: a :: R) bomU32Be = false := by
        simp [startsWith, bomU32Be]
      rw [detect_ge4 0 0 0 a _ h1 (startsWith_false_head (by omega))
        (startsWith_false_head (by omega)) (startsWith_false_head (by omega)) (startsWith_false_head (by omega))]
      simp

theorem detectEncoding1_proven : DetectEncoding1 := by
  intro e a ha ha'
  have a0 : a ≠ 0 := by omega
  have n1 : a ≠ 0xfe := by omega
  have n2 : a ≠ 0xff := by omega
  have n3 : a ≠ 0xef := by omega
  have e1 : a % 256 = a := Nat.mod_eq_of_lt (by omega)
  have e2 : a / 256 = 0 := Nat.div_eq_of_lt (by omega)
  have e3 : a / 65536 = 0 := Nat.div_eq_of_lt (by omega)
  have e4 : a / 16777216 = 0 := Nat.div_eq_of_lt (by omega)
  have e5 : a < 0x10000 := by omega
  have e6 : a < 0x80 := by omega
  cases e with
  | utf8 =>
    simp [TextEnc.encode, TextEnc.name, utf8Enc1, e6, detectEncoding, startsWith, bomU32Be, bomU32Le, bomU16Be,
      bomU16Le, bomUtf8, n1, n2, n3]
  | utf16 le =>
    cases le <;>
      simp [TextEnc.encode, TextEnc.name, utf16Enc1, e1, e2, e5, detectEncoding, startsWith, bomU32Be, bomU32Le,
        bomU16Be, bomU16Le, bomUtf8, a0, n1, n2, n3]
  | utf32 le =>
    cases le <;>
      simp [TextEnc.encode, TextEnc.name, utf32Enc1, e1, e2, e3, e4, detectEncoding, startsWith, bomU32Be, bomU32Le,
        bomU16Be, bomU16Le, bomUtf8, a0, n1, n2, n3]

/-! ### `json.loads`, `json.load` -/

/-- `json.loads`: a `str` with a leading BOM and an argument of any other type
are rejected, whatever the options, before anything is decoded. -/
def LoadsRejects : Prop :=
  ∀ (decode : DCfg → PStr → DR JVal) (a : DecArgs),
    (∀ t, jsonLoads decode a (.other t) =
      .error (.typeError s!"the JSON object must be str, bytes or bytearray, not {t}")) ∧
    (∀ s : PStr, jsonLoads decode a (.str (0xfeff :: s)) =
      .error (.named "JSONDecodeError"
        (jdeInit "Unexpected UTF-8 BOM (decode using utf-8-sig)" (0xfeff :: s) 0).errmsg))

theorem loadsRejects_proven : LoadsRejects := by
  intro decode a
  refine ⟨fun _ => rfl, fun s => ?_⟩
  simp only [jsonLoads, List.head?_cons, ↓reduceIte]
  rfl

/-- The fast path of `json.loads` agrees with an explicit `JSONDecoder`: passing
every option at its default value, for a `str`, `bytes` or any other argument. -/
def LoadsFastPath : Prop :=
  ∀ (decode : DCfg → PStr → DR JVal) (x : LoadArg),
    jsonLoads decode {} x = jsonLoads decode { strict := some true } x

theorem loadsFastPath_proven : LoadsFastPath := by
  intro decode x
  have h : ∀ s, loadsDecode decode {} s = loadsDecode decode { strict := some true } s := by
    intro s
    rfl
  cases x with
  | str s => simp only [jsonLoads, h]
  | bytes b =>
    simp only [jsonLoads]
    cases decodeBytes (detectEncoding b) b with
    | error e => rfl
    | ok s => exact h s
  | other t => rfl

/-- `json.load(fp)` is `json.loads(fp.read())`, and an exception of `read()`
propagates. -/
def LoadRead : Prop :=
  ∀ (decode : DCfg → PStr → DR JVal) (a : DecArgs),
    (∀ x, jsonLoad decode a (.ok x) = jsonLoads decode a x) ∧
    (∀ e, jsonLoad decode a (.error e) = .error e)

theorem loadRead_proven : LoadRead := fun _ _ => ⟨fun _ => rfl, fun _ => rfl⟩

/-- The document `json.loads` hands to the decoder. -/
def loadDoc : LoadArg → Option PStr
  | .str s => some s
  | .bytes b =>
    match decodeBytes (detectEncoding b) b with
    | .ok s => some s
    | .error _ => none
  | .other _ => none

/-- The same value, or exceptions of the same class. -/
def ApiRel {α : Type} (p c : Except PyExc α) : Prop :=
  (∀ v, p = .ok v ↔ c = .ok v) ∧ (∀ e, p = .error e → ∃ e', c = .error e' ∧ e.className = e'.className)

theorem ApiRel.refl {α : Type} (p : Except PyExc α) : ApiRel p p :=
  ⟨fun _ => Iff.rfl, fun e h => ⟨e, h, rfl⟩⟩

theorem loadsDecode_rel (a : DecArgs) (s : PStr) (hs : (s.length : Int) ≤ ssizeMax) :
    ApiRel (loadsDecode loadsPy a s) (loadsDecode loadsC a s) := by
  unfold loadsDecode
  simp only
  cases hc : (if loadsFast a = true then (Except.ok {} : Except PyExc DCfg) else decoderInit a) with
  | error e => exact ApiRel.refl _
  | ok cfg =>
    simp only
    rcases loadsTwinsScan_proven cfg s hs with h | ⟨_, _, _, _, h1, h2⟩ | ⟨_, _, _, _, h1, h2⟩
    · rw [h]; exact ApiRel.refl _
    · rw [h1, h2]
      refine ⟨fun v => by simp, fun e he => ⟨_, rfl, ?_⟩⟩
      simp only [Except.error.injEq] at he
      subst he
      rfl
    · rw [h1, h2]
      refine ⟨fun v => by simp, fun e he => ⟨_, rfl, ?_⟩⟩
      simp only [Except.error.injEq] at he
      subst he
      rfl

/-- Public `json.loads` on either implementation, for every option and every
argument (type invariant: the document, a `str`, has at most `sys.maxsize`
characters): the same value, or exceptions of the same class. Decoded `bytes`
are covered too; the messages differ only as in `json-loads-twins-scan`. -/
def LoadsApiTwins : Prop :=
  ∀ (a : DecArgs) (x : LoadArg), (∀ s, loadDoc x = some s → (s.length : Int) ≤ ssizeMax) →
    ApiRel (jsonLoads loadsPy a x) (jsonLoads loadsC a x)

theorem loadsApiTwins_proven : LoadsApiTwins := by
  intro a x h
  cases x with
  | str s =>
    simp only [jsonLoads]
    split
    · exact ApiRel.refl _
    · exact loadsDecode_rel a s (h s rfl)
  | bytes b =>
    simp only [jsonLoads]
    cases hd : decodeBytes (detectEncoding b) b with
    | error e => exact ApiRel.refl _
    | ok s => exact loadsDecode_rel a s (h s (by simp [loadDoc, hd]))
  | other t => exact ApiRel.refl _

/-! ### `json.dumps`, `json.dump` -/

/-- With every option at its default, the cached encoder of `dumps` and `dump`
is the one `JSONEncoder(...)` would build. -/
def DumpsFastPath : Prop := ∀ a : EncArgs, dumpsFast a = true → encoderInit a = .ok {}

theorem dumpsFastPath_proven : DumpsFastPath := by
  intro a h
  rcases a with ⟨sk, ea, cc, an, so, ind, sep, df, dd, kw⟩
  cases sk <;> cases ea <;> cases cc <;> cases an <;> cases so <;> cases sep <;> cases df <;>
    cases kw <;> cases ind <;> simp [dumpsFast] at h <;> rfl

/-- The default separators, JSONEncoder.__init__ docstring: `(', ', ': ')` if
`indent` is `None`, `(',', ': ')` otherwise. -/
def DefaultSeparators : Prop :=
  ∀ (a : EncArgs) (cfg : ECfg), a.separators = none → encoderInit a = .ok cfg →
    cfg.keySep = cs ": " ∧
    cfg.itemSep = (match a.indent with
      | .none => cs ", "
      | _ => cs ",")

theorem defaultSeparators_proven : DefaultSeparators := by
  intro a cfg hs h
  rcases a with ⟨sk, ea, cc, an, so, ind, sep, df, dd, kw⟩
  simp only at hs
  subst hs
  cases kw with
  | cons k kw => simp [encoderInit] at h
  | nil =>
    cases ind <;> simp only [encoderInit, Except.ok.injEq] at h <;> subst h <;> exact ⟨rfl, rfl⟩

/-- `json.dump` writes what `json.dumps` returns, chunk by chunk: with a
`write` that does not fail, the chunks join to the text of `dumps`, or the
generator raises what `dumps` raises. For every option, and every value and
`default` the twin theorem covers (type invariants of `ECfg.Ok`, `EVal.ok`). -/
def DumpIsDumps : Prop :=
  ∀ (a : EncArgs) (cfg : ECfg) (v : EVal), encoderOf a = .ok cfg → cfg.Ok → v.ok = true →
    yRes (jsonDump a (fun _ _ => none) v) = jsonDumps dumpsC a v

theorem dumpIsDumps_proven : DumpIsDumps := by
  intro a cfg v h hO hv
  simp only [jsonDump, jsonDumps, h, dumpTo_none]
  rw [iterencodeJoin_proven cfg v]
  exact dumpsTwins_proven cfg v hO hv

/-- `json.dump` on an `fp` whose `write` fails has written a prefix of the
generator's chunks and raises the first exception that occurred. -/
def DumpPrefix : Prop :=
  ∀ (wr : Nat → PStr → Option PyExc) (y : Yield), (dumpTo wr y).1 <+: y.1

theorem dumpPrefix_proven : DumpPrefix := by
  intro wr y
  unfold dumpTo
  simp only
  cases (writeAll wr 0 y.1).2 <;> exact writeAll_prefix wr 0 y.1

/-! ### `allow_nan` and floats -/

/-- `allow_nan`, for every float and in both encoders: a finite float gives its
`repr`; a non-finite one gives `NaN`, `Infinity` or `-Infinity`, or with
`allow_nan=False` raises `ValueError` naming its `repr`. (Exact statements about
the IEEE-754 bit pattern; `repr` itself is a parameter.) -/
def AllowNan : Prop :=
  ∀ (cfg : ECfg) (b : Nat) (r : PStr),
    pyFloatStr cfg b r = cEncodeFloat cfg b r ∧
    (fltIsFinite b = true → cEncodeFloat cfg b r = .ok r) ∧
    (fltIsFinite b = false → cfg.allowNan = false → cEncodeFloat cfg b r = .error (outOfRange r)) ∧
    (fltIsFinite b = false → cfg.allowNan = true →
      cEncodeFloat cfg b r =
        .ok (if fltIsNan b then cs "NaN" else if fltNeg b then cs "-Infinity" else cs "Infinity"))

theorem allowNan_proven : AllowNan := by
  intro cfg b r
  refine ⟨floatStr_twins cfg b r, ?_, ?_, ?_⟩
  · intro h; simp [cEncodeFloat, h]
  · intro h h2; simp [cEncodeFloat, h, h2]
  · intro h h2
    have h1 : fltExp b = 2047 := by simpa [fltIsFinite] using h
    by_cases hm : fltMant b = 0
    · cases hn : fltNeg b <;>
        simp [cEncodeFloat, h, h2, fltIsPosInf, fltIsNegInf, fltIsNan, h1, hm, hn]
    · simp [cEncodeFloat, h, h2, fltIsPosInf, fltIsNegInf, fltIsNan, h1, hm]

/-- An object nothing is known about, under `JSONEncoder.default`: `TypeError`
naming its type, in both encoders. -/
def DefaultTypeError : Prop :=
  ∀ (cfg : ECfg) (n : Nat) (t : String), (∀ m u, cfg.dflt m u = .error (defaultErr u)) →
    dumpsPy cfg (.other n t) = .error (defaultErr t) ∧
    dumpsC cfg (.other n t) = .error (defaultErr t)

theorem defaultTypeError_proven : DefaultTypeError := by
  intro cfg n t h
  have e : encFuel cfg (.other n t) = cfg.dfltDepth + 1 := by simp [encFuel, EVal.depth]; omega
  simp [dumpsPy, dumpsC, e, pyEnc, cEnc, h]

/-! ### The C wrappers -/

/-- `c_encode_basestring(_ascii)` and their Python twins, on every `str`; a
non-`str` gets `TypeError` from the C functions. -/
def EncodeBasestringTwins : Prop :=
  (∀ s : PStr, strOk s = true →
    cPyEncodeBasestringAscii (.str s) = .ok (pyEncodeBasestringAscii s) ∧
    cPyEncodeBasestring (.str s) = .ok (pyEncodeBasestring s)) ∧
  (∀ t, cPyEncodeBasestringAscii (.other t) = .error (badArgErr "encode_basestring_ascii" "argument" t) ∧
    cPyEncodeBasestring (.other t) = .error (badArgErr "encode_basestring" "argument" t))

theorem encodeBasestringTwins_proven : EncodeBasestringTwins := by
  refine ⟨fun s h => ⟨?_, ?_⟩, fun _ => ⟨rfl, rfl⟩⟩
  · have := strEnc_twins { ensureAscii := true } s h
    simp only [pyStrEnc, cStrEnc, ↓reduceIte] at this
    simp [cPyEncodeBasestringAscii, this]
  · have := strEnc_twins { ensureAscii := false } s h
    simp only [pyStrEnc, cStrEnc, Bool.false_eq_true, ↓reduceIte] at this
    simp [cPyEncodeBasestring, this]

theorem outOfSsize_false {i : Int} (h0 : 0 ≤ i) (h1 : i ≤ ssizeMax) : outOfSsize i = false := by
  have h2 : ¬ (i < ssizeMin) := by simp only [ssizeMin]; omega
  have h3 : ¬ (i > ssizeMax) := by omega
  simp [outOfSsize, h2, h3]

theorem cScanLoop_no_stop (s : PStr) (strict : Bool) (b : Int) :
    ∀ (g e : Nat) (acc : Option PStr) (i : Int), cScanLoop s strict b g e acc ≠ .error (.stop i) := by
  intro g
  induction g with
  | zero => intro e acc i; simp [cScanLoop, fuelOut]
  | succ g ih =>
    intro e acc i h
    simp only [cScanLoop] at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | exact ih _ _ _ h

theorem cScanstring_no_stop (s : PStr) (e : Nat) (strict : Bool) (i : Int) :
    cScanstring s e strict ≠ .error (.stop i) := by
  unfold cScanstring
  split
  · simp
  · exact cScanLoop_no_stop _ _ _ _ _ _ _

/-- `scanstring(s, end, strict)`: the C function and `py_scanstring` agree up to
`ScanTwin` for every `end`. -/
def ScanstringTwins : Prop :=
  ∀ (s : PStr) (e : Int) (strict : Bool),
    ScanTwin s (pyScanstringCall s e strict) (cPyScanstring (.str s) e strict)

/-- `scanstring('ab', 5)`: C raises `ValueError: end is out of bounds`, and
`py_scanstring` a `JSONDecodeError` naming a position past the end. -/
theorem scanstringTwins_refuted : ¬ScanstringTwins := by
  intro h
  have h1 := h (cs "ab") 5 true
  have e1 : pyScanstringCall (cs "ab") 5 true = .error (.jde "Unterminated string starting at" 4) := by decide
  have e2 : cPyScanstring (.str (cs "ab")) 5 true = .error (.exc (.valueError "end is out of bounds")) := by decide
  rw [e1, e2] at h1
  rcases h1 with h1 | ⟨_, _, _, _, h1, _⟩ | ⟨_, _, _, _, h1, _⟩ <;> cases h1

/-- For `0 <= end <= len(s)`, `scanstring` agrees between the twins up to
`ScanTwin`. The bounds are exactly the refuted cases. -/
def ScanstringTwinsInRange : Prop :=
  ∀ (s : PStr) (e : Nat) (strict : Bool), e ≤ s.length → (s.length : Int) ≤ ssizeMax →
    ScanTwin s (pyScanstringCall s (e : Int) strict) (cPyScanstring (.str s) (e : Int) strict)

theorem scanstringTwinsInRange_proven : ScanstringTwinsInRange := by
  intro s e strict h1 hs
  have ho := outOfSsize_false (i := (e : Int)) (by omega) (by omega)
  have hn : ¬ ((e : Int) < 0) := by omega
  simp only [pyScanstringCall, cPyScanstring, ho, Bool.false_eq_true, ↓reduceIte, hn, Int.toNat_natCast]
  rcases scanstring_rel s strict e h1 with ⟨v, k, _, h1, h2⟩ | ⟨pe, ce, h1, h2, he⟩
  · rw [h1, h2]; exact Or.inl rfl
  · rw [h1, h2]
    rcases he with rfl | ⟨i, rfl, rfl⟩ | ⟨q, ch, hq, hch, rfl, rfl⟩ | ⟨q, ch, hq, hq1, rfl, rfl⟩
    · left; cases pe <;> rfl
    · exact absurd h2 (cScanstring_no_stop s e strict i)
    · right; left; exact ⟨q, ch, hq, hch, rfl, rfl⟩
    · right; right; exact ⟨q, ch, hq, hq1, rfl, rfl⟩

/-- `JSONDecoder.raw_decode` with the C scanner is `scanner_call` with
`StopIteration` turned into `JSONDecodeError`, on every `str` and index. -/
def ScannerCallRaw : Prop :=
  ∀ (cfg : DCfg) (s : PStr) (idx : Int), rawDecodeC cfg s idx = stopToJde (cScannerCall cfg (.str s) idx)

theorem scannerCallRaw_proven : ScannerCallRaw := by
  intro cfg s idx
  by_cases h : idx < ssizeMin ∨ idx > ssizeMax
  · have ho : outOfSsize idx = true := by simpa [outOfSsize] using h
    simp [rawDecodeC, cScannerCall, h, ho, stopToJde, ssizeErr]
  · have ho : outOfSsize idx = false := by simpa [outOfSsize] using h
    by_cases h2 : idx < 0
    · simp [rawDecodeC, cScannerCall, h, ho, h2, stopToJde]
    · simp only [rawDecodeC, cScannerCall, h, ho, h2, ↓reduceIte, Bool.false_eq_true]
      cases hc : cScanOnce cfg s (docFuel s) idx.toNat with
      | error e => cases e <;> simp [stopToJde]
      | ok r => obtain ⟨v, n⟩ := r; simp [stopToJde]

theorem foldlM_getattr_ok (g : String → Except PyExc Unit) :
    ∀ (l : List String), (∀ a ∈ l, g a = .ok ()) → l.foldlM (fun _ a => g a) () = .ok ()
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.foldlM_cons, h a (by simp)]
    exact foldlM_getattr_ok g l (fun b hb => h b (by simp [hb]))

theorem foldlM_getattr_err (g : String → Except PyExc Unit) (e : PyExc) :
    ∀ (pre : List String) (a : String) (post : List String), (∀ b ∈ pre, g b = .ok ()) → g a = .error e →
    (pre ++ a :: post).foldlM (fun _ a => g a) () = .error e
  | [], a, post, _, ha => by simp [List.foldlM_cons, ha]; rfl
  | b :: pre, a, post, h, ha => by
    simp only [List.cons_append, List.foldlM_cons, h b (by simp)]
    exact foldlM_getattr_err g e pre a post (fun c hc => h c (by simp [hc])) ha

/-- `make_scanner(ctx)` for every context object: when `strict` and the six other attributes can
be read and `bool(ctx.strict)` returns, the scanner has every hook with `strict` by truth value;
otherwise the first failure in the order of `scanner_new` (`strict`, its truth value,
`object_hook`, `object_pairs_hook`, `array_hook`, `parse_float`, `parse_int`, `parse_constant`)
is what it raises, whatever exception that is. -/
def ScannerNew : Prop :=
  ∀ (ctx : ScanCtx) (cfg : DCfg),
    ((∀ a ∈ "strict" :: scannerAttrs, ctx.getattr a = .ok ()) → ∀ st, ctx.strict = .ok st →
      scannerNew ctx cfg = .ok { cfg with strict := st }) ∧
    (∀ e, ctx.getattr "strict" = .error e → scannerNew ctx cfg = .error e) ∧
    (ctx.getattr "strict" = .ok () → ∀ e, ctx.strict = .error e → scannerNew ctx cfg = .error e) ∧
    (∀ (pre : List String) (a : String) (post : List String) (e : PyExc), scannerAttrs = pre ++ a :: post →
      ctx.getattr "strict" = .ok () → (∃ st, ctx.strict = .ok st) → (∀ b ∈ pre, ctx.getattr b = .ok ()) →
      ctx.getattr a = .error e → scannerNew ctx cfg = .error e)

theorem scannerNew_proven : ScannerNew := by
  intro ctx cfg
  refine ⟨fun h st hs => ?_, fun e he => ?_, fun h1 e he => ?_, fun pre a post e hl h1 hs hpre ha => ?_⟩
  · have h1 := h "strict" (by simp)
    simp only [scannerNew, h1, hs]
    rw [foldlM_getattr_ok _ _ (fun b hb => h b (by simp [hb]))]
  · simp [scannerNew, he]
  · simp [scannerNew, h1, he]
  · obtain ⟨st, hs⟩ := hs
    simp only [scannerNew, h1, hs]
    rw [hl, foldlM_getattr_err _ e pre a post hpre ha]

/-- `c_make_encoder(markers, default, encoder, indent, key_sep, item_sep, sort_keys, skipkeys,
allow_nan)`: as `JSONEncoder.iterencode` calls it (encoder.py:254-257) it keeps every option,
`check_circular` being `markers is not None`; and with `str` separators, a `markers` that is
neither a dict nor `None` is refused with `make_encoder() argument 1 must be dict or None, not
<type>` (`%.200s` of `tp_name`, :1327-1331), whatever the other arguments. -/
def EncoderNew : Prop :=
  (∀ cfg : ECfg, cfg.customEnc = none →
    encoderNew (if cfg.checkCircular then .dict else .none) cfg.dflt cfg.dfltDepth
      (if cfg.ensureAscii then .cAscii else .cPlain) cfg.indent (.str cfg.keySep) (.str cfg.itemSep)
      cfg.sortKeys cfg.skipKeys cfg.allowNan = .ok cfg) ∧
  (∀ (t : String) dflt dfltDepth encoder indent (ks is : PStr) sortKeys skipKeys allowNan,
    encoderNew (.other t) dflt dfltDepth encoder indent (.str ks) (.str is) sortKeys skipKeys allowNan =
      .error (.typeError s!"make_encoder() argument 1 must be dict or None, not {truncName 200 t}"))

theorem encoderNew_proven : EncoderNew := by
  refine ⟨fun cfg h => ?_, fun t _ _ _ _ _ _ _ _ _ => rfl⟩
  rcases cfg with ⟨ea, cc, an, so, sk, ind, it, ks, df, dd, ce⟩
  simp only at h
  subst h
  cases ea <;> cases cc <;> rfl

/-- `c_make_encoder` refuses a `key_separator` that is not a `str` with `TypeError`, whatever the
other arguments and whatever the separator's type: `PyArg_ParseTupleAndKeywords` raises
`TypeError` for an argument of the wrong type (`"must be str, not <type>"`, the `U` unit of
`"OOOOUUppp:make_encoder"`, Modules/_json.c:1320). -/
def EncoderNewSepTypeError : Prop :=
  ∀ (markers : MarkersArg) (dflt : Nat → String → Except PyExc EVal) (dfltDepth : Nat)
    (encoder : EncoderArg) (indent : Option PStr) (t : String) (itemSep : StrArg)
    (sortKeys skipKeys allowNan : Bool),
    ∃ m, encoderNew markers dflt dfltDepth encoder indent (.other t) itemSep sortKeys skipKeys allowNan
      = .error (.typeError m)

/-- The type `'a' + 'é' * 30` is 61 bytes; `converterr`'s `snprintf("%.50s")` keeps 50, which ends
with the first byte of the 25th 'é', and `PyErr_SetString` cannot decode the message:
`UnicodeDecodeError` at byte 92. -/
theorem encoderNew_longSep :
    uArgErr 5 ("a" ++ String.ofList (List.replicate 30 'é')) =
      .named "UnicodeDecodeError"
        "'utf-8' codec can't decode byte 0xc3 in position 92: unexpected end of data" := by
  decide

theorem encoderNewSepTypeError_refuted : ¬EncoderNewSepTypeError := by
  intro h
  obtain ⟨m, hm⟩ := h .none (fun _ _ => .error (.valueError "")) 0 .cAscii none
    ("a" ++ String.ofList (List.replicate 30 'é')) (.str []) false false false
  simp only [encoderNew, encoderNew_longSep] at hm
  cases hm

/-- `c_make_encoder(...)(o, 0)`, the 1-tuple `JSONEncoder.encode` joins. With the
two C `encoder`s it is the text of `dumps`. -/
def EncoderCallDumps : Prop :=
  ∀ (alloc : Alloc) (cfg : ECfg) (v : EVal), cfg.customEnc = none →
    encoderCall alloc cfg v 0 = (dumpsC cfg v).map (fun t => [t])

theorem encoderCallDumps_proven : EncoderCallDumps := by
  intro alloc cfg v hc
  have ho : outOfSsize (0 : Int) = false := outOfSsize_false (by omega) (by decide)
  have hcc : cacheCopies 0 = 0 := rfl
  unfold encoderCall
  rw [if_neg (by simp [ho])]
  split
  · rename_i e he
    cases hi : cfg.indent <;> simp [hi, createIndentCache, Except.map] at he
  simp only [hcc]
  cases v with
  | str s =>
    have e : encFuel cfg (.str s) = cfg.dfltDepth + 1 := by simp [encFuel, EVal.depth]; omega
    simp [e, cEnc, cEncStr_std hc, dumpsC, cStrEnc, Except.map]
  | _ =>
    simp only [dumpsC]
    cases cEnc cfg _ 0 [] _ <;> rfl

/-! ### The indent cache -/

theorem rep_snoc (t : PStr) (n : Nat) : rep t n ++ t = rep t (n + 1) := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp only [rep, List.append_assoc, ih]

/-- The comment above `create_indent_cache`, :1362-1371, for levels up to `n`. -/
structure Cached (cfg : ECfg) (ind : PStr) (i : Nat) (c : IndentCache) (n : Nat) : Prop where
  len : c.length = 2 * n + 1
  nl : ∀ k, k ≤ n → c[2 * k]? = some (cNewlineIndent ind (k + i))
  sep : ∀ k, 1 ≤ k → k ≤ n → c[2 * k - 1]? = some (cSepIndent cfg ind (k + i))

theorem create_cached (cfg : ECfg) (ind : PStr) (i : Nat) :
    Cached cfg ind i [cNewlineIndent ind i] 0 := by
  constructor
  · simp
  · intro k hk
    obtain rfl : k = 0 := by omega
    simp
  · intro k h1 h2; omega

theorem rep_length (t : PStr) (n : Nat) : (rep t n).length = n * t.length := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp only [rep, List.length_append, ih]; rw [Nat.succ_mul]; omega

theorem rep_one (t : PStr) : rep t 1 = t := by simp [rep]

/-- `PyUnicode_New` succeeds when its size check passes for every kind and `malloc` grants every
request up to the largest it could make. -/
theorem unicodeNewOk_small {alloc : Alloc} {size m : Nat} (h1 : ((56 + 4 * (size + 1) : Nat) : Int) ≤ ssizeMax)
    (h2 : ∀ n, n ≤ 56 + 4 * (size + 1) → alloc n = true) : unicodeNewOk alloc size m = true := by
  unfold unicodeNewOk
  have hb : ucsStruct m + (size + 1) * ucsWidth m ≤ 56 + 4 * (size + 1) := by
    unfold ucsStruct ucsWidth
    by_cases a : m < 128 <;> by_cases b : m < 256 <;> by_cases c : m < 65536 <;> simp [a, b, c] <;> omega
  rw [h2 _ hb]
  unfold ucsStruct ucsWidth
  simp only [ssizeMax] at h1
  by_cases a : m < 128 <;> by_cases b : m < 256 <;> by_cases c : m < 65536 <;> simp [a, b, c, ssizeMax] <;> omega

/-- `PyUnicode_New`'s size check refuses more than `PY_SSIZE_T_MAX - 41` characters, whatever
`malloc` would do. -/
theorem unicodeNewOk_big {alloc : Alloc} {size m : Nat} (h : (size : Int) > ssizeMax - 41) :
    unicodeNewOk alloc size m = false := by
  unfold unicodeNewOk ucsStruct ucsWidth
  simp only [ssizeMax] at h
  by_cases a : m < 128 <;> by_cases b : m < 256 <;> by_cases c : m < 65536 <;> simp [a, b, c, ssizeMax] <;> omega

/-- A refused `malloc` is `MemoryError`. -/
theorem unicodeNewOk_refused {alloc : Alloc} {size m : Nat}
    (h : alloc (ucsStruct m + (size + 1) * ucsWidth m) = false) : unicodeNewOk alloc size m = false := by
  simp [unicodeNewOk, h]

/-- What `PyUnicode_New` allows is below `PY_SSIZE_T_MAX - 40`. -/
theorem unicodeNewOk_le {alloc : Alloc} {size m : Nat} (h : unicodeNewOk alloc size m = true) :
    (size : Int) ≤ ssizeMax - 41 := by
  unfold unicodeNewOk ucsStruct ucsWidth at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h, _⟩ := h
  by_cases a : m < 128 <;> by_cases b : m < 256 <;> by_cases c : m < 65536 <;>
    simp [a, b, c, ssizeMax] at h ⊢ <;> omega

theorem update_cached {cfg : ECfg} {ind : PStr} {i : Nat} {c : IndentCache} {n : Nat}
    (h : Cached cfg ind i c n) : Cached cfg ind i (updateIndentCache cfg ind (n + 1) c) (n + 1) := by
  have hn := h.nl n (Nat.le_refl n)
  have hnl : c.getD ((n + 1 - 1) * 2) [] ++ ind = cNewlineIndent ind (n + 1 + i) := by
    have e : (n + 1 - 1) * 2 = 2 * n := by omega
    have e2 : n + 1 + i = (n + i) + 1 := by omega
    rw [e, List.getD_eq_getElem?_getD, hn, e2]
    simp [cNewlineIndent, rep_snoc]
  have hlen := h.len
  constructor
  · simp [updateIndentCache]; omega
  · intro k hk
    by_cases hk2 : k ≤ n
    · simp only [updateIndentCache]
      rw [List.getElem?_append_left (by omega)]
      exact h.nl k hk2
    · obtain rfl : k = n + 1 := by omega
      simp only [updateIndentCache, hnl]
      rw [List.getElem?_append_right (by omega)]
      have e : 2 * (n + 1) - c.length = 1 := by omega
      simp [e]
  · intro k h1 hk
    by_cases hk2 : k ≤ n
    · simp only [updateIndentCache]
      rw [List.getElem?_append_left (by omega)]
      exact h.sep k h1 hk2
    · obtain rfl : k = n + 1 := by omega
      simp only [updateIndentCache, hnl]
      rw [List.getElem?_append_right (by omega)]
      have e : 2 * (n + 1) - 1 - c.length = 0 := by omega
      simp [e, cSepIndent]

/-- `malloc` grants every request of at most `n` bytes, and `n` passes every size check. -/
def Grants (alloc : Alloc) (n : Nat) : Prop := (n : Int) ≤ ssizeMax ∧ ∀ m, m ≤ n → alloc m = true

/-- The indent cache, for every `indent` (a `str`, so shorter than `PY_SSIZE_T_MAX`, a type
invariant), every level in `Py_ssize_t` and every behaviour `alloc` of `malloc`:
1. `create_indent_cache` (:1373-1390): below level 1 the cache is `['\n']` (`PySequence_Repeat`
   gives `''`, or the repeat is skipped at 0); from level 2, `OverflowError('repeated string is
   too long')` when `len(indent) > PY_SSIZE_T_MAX / level`; otherwise `['\n' + indent * level]`
   or `MemoryError`: the cache when `malloc` grants the two strings' requests (up to
   `56 + 4 * (len(indent) * level + 2)` bytes), `MemoryError` when `PyUnicode_New`'s size check
   refuses the repeat (more than `PY_SSIZE_T_MAX - 41` characters) or `malloc` refuses its request;
2. from a cache `['\n' + indent * i]`, at every level `k` reached one at a time (the assertion of
   `update_indent_cache`), `get_item_separator` returns `item_separator + '\n' + indent * (k + i)`,
   `write_newline_indent` returns `'\n' + indent * (k + i)`, and the invariant of the comment at
   :1362-1371 holds afterwards. This is why the encoder models, which write those strings
   directly at level `cacheCopies level + k`, are faithful to the C code. -/
def IndentCacheSpec : Prop :=
  (∀ (alloc : Alloc) (ind : PStr) (level : Int), (ind.length : Int) < ssizeMax → ¬ outOfSsize level →
    (level < 1 → createIndentCache alloc ind level = .ok [[10]] ∧ cacheCopies level = 0) ∧
    (2 ≤ level → (ind.length : Int) > ssizeMax / level →
      createIndentCache alloc ind level = .error (.overflowError "repeated string is too long")) ∧
    (1 ≤ level → ¬ (2 ≤ level ∧ (ind.length : Int) > ssizeMax / level) →
      (createIndentCache alloc ind level = .ok [cNewlineIndent ind (cacheCopies level)] ∨
        createIndentCache alloc ind level = .error memoryError) ∧
      (Grants alloc (56 + 4 * (level.toNat * ind.length + 2)) →
        createIndentCache alloc ind level = .ok [cNewlineIndent ind (cacheCopies level)]) ∧
      (2 ≤ level → ((level.toNat * ind.length : Nat) : Int) > ssizeMax - 41 →
        createIndentCache alloc ind level = .error memoryError) ∧
      (2 ≤ level → level.toNat * ind.length ≠ 0 →
        alloc (ucsStruct (strMax ind) + (level.toNat * ind.length + 1) * ucsWidth (strMax ind)) = false →
        createIndentCache alloc ind level = .error memoryError))) ∧
  ∀ (cfg : ECfg) (ind : PStr) (i : Nat), Cached cfg ind i [cNewlineIndent ind i] 0 ∧
    ∀ (c : IndentCache) (n k : Nat), Cached cfg ind i c n → 1 ≤ k → k ≤ n + 1 →
      let r := getItemSeparator cfg ind k c
      r.1 = cSepIndent cfg ind (k + i) ∧ Cached cfg ind i r.2 (max n k) ∧
      writeNewlineIndent k r.2 = cNewlineIndent ind (k + i)

theorem createIndentCache_one (alloc : Alloc) (ind : PStr) (hl : (ind.length : Int) < ssizeMax) :
    (createIndentCache alloc ind 1 = .ok [[10] ++ ind] ∨ createIndentCache alloc ind 1 = .error memoryError) ∧
    (Grants alloc (56 + 4 * (ind.length + 2)) → createIndentCache alloc ind 1 = .ok [[10] ++ ind]) := by
  have hr : unicodeRepeat alloc ind 1 = .ok ind := by simp [unicodeRepeat]
  have hca : createIndentCache alloc ind 1 = (unicodeAppend alloc [10] ind).map (fun nl => [nl]) := by
    simp only [createIndentCache, ne_eq, show (1 : Int) ≠ 0 by decide, not_false_eq_true, ↓reduceIte, hr]
    cases unicodeAppend alloc [10] ind <;> rfl
  rw [hca]
  by_cases he : ind = []
  · subst he; simp [unicodeAppend, Except.map]
  have hov : ¬ ((([10] : PStr).length : Int) > ssizeMax - ind.length) := by simp; omega
  have hov' : ¬ (ssizeMax - (ind.length : Int) < 1) := by omega
  refine ⟨?_, fun ⟨g1, g2⟩ => ?_⟩
  · simp only [unicodeAppend, he, List.cons_ne_nil, ↓reduceIte, hov]
    split <;> simp [Except.map]
  · have hk := unicodeNewOk_small (alloc := alloc) (m := max (strMax [10]) (strMax ind))
      (size := 1 + ind.length) (by push_cast at g1 ⊢; omega) (fun n hn => g2 n (by omega))
    simp [unicodeAppend, he, hov', hk, Except.map]

theorem createIndentCache_two (alloc : Alloc) (ind : PStr) (level : Int) (h2 : 2 ≤ level)
    (hno : ¬ ((ind.length : Int) > ssizeMax / level)) :
    createIndentCache alloc ind level =
      if level.toNat * ind.length = 0 then .ok [[10]]
      else if unicodeNewOk alloc (level.toNat * ind.length) (strMax ind) then
        (if unicodeNewOk alloc (1 + level.toNat * ind.length) (max (strMax [10]) (strMax (rep ind level.toNat)))
         then .ok [[10] ++ rep ind level.toNat] else .error memoryError)
      else .error memoryError := by
  have h0 : level ≠ 0 := by omega
  have hrl : (rep ind level.toNat).length = level.toNat * ind.length := rep_length _ _
  generalize hN : level.toNat * ind.length = N at hrl ⊢
  have hrep : unicodeRepeat alloc ind level =
      if N = 0 then .ok [] else if unicodeNewOk alloc N (strMax ind) then .ok (rep ind level.toNat)
      else .error memoryError := by
    simp [unicodeRepeat, show ¬ level < 1 by omega, show level ≠ 1 by omega, hno, hN]
  simp only [createIndentCache, ne_eq, h0, not_false_eq_true, ↓reduceIte, hrep]
  by_cases hN0 : N = 0
  · simp [hN0, unicodeAppend]
  simp only [hN0, ↓reduceIte]
  by_cases hk : unicodeNewOk alloc N (strMax ind) = true
  · have hle := unicodeNewOk_le hk
    have hne : rep ind level.toNat ≠ [] := by
      intro h; rw [h] at hrl; simp at hrl; omega
    have hov : ¬ ((([10] : PStr).length : Int) > ssizeMax - ((rep ind level.toNat).length : Int)) := by
      rw [hrl]; simp; omega
    have hlen : ([10] : PStr).length + (rep ind level.toNat).length = 1 + N := by simp [hrl]
    simp only [hk, ↓reduceIte, unicodeAppend, List.cons_ne_nil, hne, hov, hlen]
    by_cases hk2 : unicodeNewOk alloc (1 + N) (max (strMax [10]) (strMax (rep ind level.toNat))) = true
    · simp [hk2]
    · simp [hk2]
  · simp [hk]

theorem createIndentCache_spec (alloc : Alloc) (ind : PStr) (level : Int) (hl : (ind.length : Int) < ssizeMax) :
    (level < 1 → createIndentCache alloc ind level = .ok [[10]] ∧ cacheCopies level = 0) ∧
    (2 ≤ level → (ind.length : Int) > ssizeMax / level →
      createIndentCache alloc ind level = .error (.overflowError "repeated string is too long")) ∧
    (1 ≤ level → ¬ (2 ≤ level ∧ (ind.length : Int) > ssizeMax / level) →
      (createIndentCache alloc ind level = .ok [cNewlineIndent ind (cacheCopies level)] ∨
        createIndentCache alloc ind level = .error memoryError) ∧
      (Grants alloc (56 + 4 * (level.toNat * ind.length + 2)) →
        createIndentCache alloc ind level = .ok [cNewlineIndent ind (cacheCopies level)]) ∧
      (2 ≤ level → ((level.toNat * ind.length : Nat) : Int) > ssizeMax - 41 →
        createIndentCache alloc ind level = .error memoryError) ∧
      (2 ≤ level → level.toNat * ind.length ≠ 0 →
        alloc (ucsStruct (strMax ind) + (level.toNat * ind.length + 1) * ucsWidth (strMax ind)) = false →
        createIndentCache alloc ind level = .error memoryError)) := by
  refine ⟨fun h => ?_, fun h2 hov => ?_, fun h1 hno => ?_⟩
  · exact ⟨createIndentCache_lt1 alloc ind h, by simp [cacheCopies, h]⟩
  · exact createIndentCache_ovf alloc ind h2 hov
  · have hc : cacheCopies level = level.toNat := by simp [cacheCopies, show ¬ level < 1 by omega]
    rw [hc]
    by_cases hone : level = 1
    · subst hone
      obtain ⟨a, b⟩ := createIndentCache_one alloc ind hl
      have e : (1 : Int).toNat = 1 := rfl
      simp only [e, cNewlineIndent, rep_one, Nat.one_mul]
      exact ⟨a, b, fun h => by omega, fun h => by omega⟩
    have h2 : 2 ≤ level := by omega
    have hno' : ¬ ((ind.length : Int) > ssizeMax / level) := fun h => hno ⟨h2, h⟩
    rw [createIndentCache_two alloc ind level h2 hno']
    have hrl : (rep ind level.toNat).length = level.toNat * ind.length := rep_length _ _
    generalize level.toNat * ind.length = N at hrl ⊢
    have hnl : N = 0 → cNewlineIndent ind level.toNat = [10] := by
      intro h; rw [h] at hrl; simp [cNewlineIndent, List.length_eq_zero_iff.mp hrl]
    refine ⟨?_, fun ⟨g1, g2⟩ => ?_, fun _ hbig => ?_, fun _ hN0 hrf => ?_⟩
    · by_cases hN0 : N = 0
      · left; simp [hN0, hnl hN0]
      simp only [hN0, ↓reduceIte]
      split
      · split
        · left; rfl
        · right; rfl
      · right; rfl
    · by_cases hN0 : N = 0
      · simp [hN0, hnl hN0]
      have hk1 := unicodeNewOk_small (alloc := alloc) (size := N) (m := strMax ind)
        (by push_cast at g1 ⊢; omega) (fun n hn => g2 n (by omega))
      have hk2 := unicodeNewOk_small (alloc := alloc) (size := 1 + N)
        (m := max (strMax [10]) (strMax (rep ind level.toNat))) (by push_cast at g1 ⊢; omega)
        (fun n hn => g2 n (by omega))
      simp [hN0, hk1, hk2, cNewlineIndent]
    · have hN0 : N ≠ 0 := by intro h; subst h; simp [ssizeMax] at hbig
      simp [hN0, unicodeNewOk_big (alloc := alloc) (m := strMax ind) hbig]
    · simp [hN0, unicodeNewOk_refused (alloc := alloc) hrf]

theorem indentCacheSpec_proven : IndentCacheSpec := by
  refine ⟨fun alloc ind level hl _ => createIndentCache_spec alloc ind level hl, ?_⟩
  intro cfg ind i
  refine ⟨create_cached cfg ind i, ?_⟩
  intro c n k h h1 h2
  have hlen := h.len
  by_cases hk : k ≤ n
  · have hc : ¬ (k * 2 > c.length) := by omega
    have e1 : k * 2 - 1 = 2 * k - 1 := by omega
    have e2 : k * 2 = 2 * k := by omega
    have hm : max n k = n := by omega
    simp only [getItemSeparator, hc, ↓reduceIte, writeNewlineIndent, hm]
    refine ⟨?_, h, ?_⟩
    · rw [List.getD_eq_getElem?_getD, e1, h.sep k h1 hk]; rfl
    · rw [List.getD_eq_getElem?_getD, e2, h.nl k hk]; rfl
  · obtain rfl : k = n + 1 := by omega
    have hu := update_cached h
    have hc : (n + 1) * 2 > c.length := by omega
    have e1 : (n + 1) * 2 - 1 = 2 * (n + 1) - 1 := by omega
    have e2 : (n + 1) * 2 = 2 * (n + 1) := by omega
    have hm : max n (n + 1) = n + 1 := by omega
    simp only [getItemSeparator, hc, ↓reduceIte, writeNewlineIndent, hm]
    refine ⟨?_, hu, ?_⟩
    · rw [List.getD_eq_getElem?_getD, e1, hu.sep (n + 1) (by omega) (Nat.le_refl _)]; rfl
    · rw [List.getD_eq_getElem?_getD, e2, hu.nl (n + 1) (Nat.le_refl _)]; rfl

end PyLean.JsonMod
