import PyLean.UnicodeObj.CodecsErrRound

/-!
Round trips through the standard handlers, called directly on exception objects, and the names
`namereplace` writes.
-/

namespace PyLean.UnicodeObj.Codecs

open PyLean PyLean.UnicodeObj

/-! ## surrogateescape -/

theorem escapeRun_prefix : ∀ (k : Nat) (l : List Nat), escapeRun k l = l.take (escapeRun k l).length
  | 0, _ => by simp [escapeRun]
  | _ + 1, [] => by simp [escapeRun]
  | k + 1, b :: bs => by
    simp only [escapeRun]
    split
    · simp
    · simp only [List.length_cons, List.take_succ_cons]
      rw [← escapeRun_prefix k bs]

theorem escapeRun_mem : ∀ (k : Nat) (l : List Nat) (x : Nat), x ∈ escapeRun k l → x ∈ l ∧ 128 ≤ x
  | 0, _, _, h => by simp [escapeRun] at h
  | _ + 1, [], _, h => by simp [escapeRun] at h
  | k + 1, b :: bs, x, h => by
    simp only [escapeRun] at h
    split at h
    · simp at h
    · rename_i hb
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨by simp, by omega⟩
      · have := escapeRun_mem k bs x h
        exact ⟨by simp [this.1], this.2⟩

theorem map_sub_add : ∀ l : List Nat,
    List.map (fun x => x - 0xdc00) (List.map (fun x => x + 0xdc00) l) = l
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, map_sub_add xs, Nat.add_sub_cancel]

theorem stOf_zero (e : ExcObj) (n : Nat) (h : e.start ≤ 0) : stOf e n = 0 := by
  unfold stOf adjustStart; simp only; split <;> split <;> (try split) <;> omega

theorem enOf_full (e : ExcObj) (n : Nat) (h : (n : Int) ≤ e.stop) : enOf e n = n := by
  unfold enOf adjustEnd; simp only; split <;> split <;> omega

/-- **surrogateescape round-trips through its two handlers.** Whatever `surrogateescape`
returns for a decode error (any bytes, any `start` and `end`), handing that string to it again
as the `object` of an encode error covering the whole string gives back the bytes it replaced.
PEP 383; codecs.rst: "This code will then be turned back into the same byte when the
'surrogateescape' error handler is used when encoding the data." -/
def SurrogateEscapeHandlersRoundTrip : Prop :=
  ∀ (H : Hier) (capi : Except PyExc (Nat → Option Str)) (d e : ExcObj) (b : Bytes) (s : Str) (pos : Nat),
    HierOk H → Bytes.Valid b → H.isDec d.cls = true → d.object = .bytes b →
    callBuiltin H capi .surrogateescape d = .ok (.str s, pos) →
    H.isEnc e.cls = true → e.object = .str s → e.start ≤ 0 → (s.length : Int) ≤ e.stop →
    callBuiltin H capi .surrogateescape e = .ok (.bytes (slice b (stOf d b.length) pos), s.length)

theorem surrogateEscapeHandlersRoundTrip_proven : SurrogateEscapeHandlersRoundTrip := by
  intro H capi d e b s pos hH hv hD hdo hd hE heo hst hen
  have hDE := hH.dec_not_enc hD
  simp only [callBuiltin, surrogateEscapeErrors, hDE, Bool.false_eq_true, if_false, hD, if_true,
    surrogateEscapeDecode, getParams_bytes d b hdo, ok_bind] at hd
  rw [escConsume_eq] at hd
  split at hd
  · obtain ⟨x, hx⟩ := bail_isError (α := Body) H d
    rw [hx] at hd; cases hd
  · simp only [pure, Except.pure, Functor.map, Except.map, Body.result, Except.ok.injEq,
      Prod.mk.injEq, Rep.str.injEq] at hd
    obtain ⟨hs, hpos⟩ := hd
    have hlen : s.length = (escapeRun (min 4 (enOf d b.length - stOf d b.length))
        (b.drop (stOf d b.length))).length := by rw [← hs]; simp
    have hst0 := stOf_zero e s.length hst
    have hen0 := enOf_full e s.length hen
    simp only [callBuiltin, surrogateEscapeErrors, hE, if_true, surrogateEscapeEncode,
      getParams_str e s heo, ok_bind, hst0, hen0]
    rw [escWrite_eq]
    have hall : (slice s 0 s.length).all (fun c => decide (0xdc80 ≤ c) && decide (c ≤ 0xdcff)) = true := by
      rw [List.all_eq_true]
      intro x hx
      have hx' : x ∈ s := mem_slice hx
      rw [← hs] at hx'
      simp only [List.mem_map] at hx'
      obtain ⟨y, hy, rfl⟩ := hx'
      have h1 := escapeRun_mem _ _ y hy
      have h2 := hv y (List.mem_of_mem_drop h1.1)
      simp; omega
    rw [if_pos hall]
    simp only [bailOn_ok, ok_bind, pure, Except.pure, Functor.map, Except.map, Body.result,
      Except.ok.injEq, Prod.mk.injEq, and_true]
    have hsl : slice s 0 s.length = s := by simp [slice]
    rw [hsl, ← hs, ← hpos]
    rw [map_sub_add]
    unfold slice
    simp only [List.length_map, Nat.add_sub_cancel_left]
    exact congrArg Rep.bytes (escapeRun_prefix _ _)

/-! ## surrogatepass -/

theorem passRead_passBytes (code : EncCode) (c : Nat) (post : List Nat) (hu : code ≠ .unknown)
    (hs : isSurrogate c = true) (hp : ∀ x ∈ post, x < 256) :
    passRead code (passBytes code c ++ post) = c := by
  have hc := surrogate_lt hs
  have hb : ∀ x ∈ passBytes code c ++ post, x < 256 := by
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · cases code <;> simp [passBytes] at hx <;> rcases hx with rfl | rfl | rfl | rfl <;>
        first | omega | exact Nat.mod_lt _ (by decide)
    · exact hp x hx
  rw [passRead_eq code _ (by rw [List.length_append, passBytes_length]; omega) hb,
    passBytes_eq code c hs]
  cases code
  · -- the three bytes of a surrogate in UTF-8
    have h12 : c >>> 12 = 13 := by rw [Nat.shiftRight_eq_div_pow]; omega
    have hy1 : (c >>> 6) &&& 0x3f = c / 64 % 64 := by
      rw [Nat.shiftRight_eq_div_pow, show (0x3f : Nat) = 2 ^ 6 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
    have hy2 : c &&& 0x3f = c % 64 := by
      rw [show (0x3f : Nat) = 2 ^ 6 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
    have k : ∀ y, y < 64 → (0x80 ||| y) &&& 0xc0 = 0x80 ∧ (0x80 ||| y) &&& 0x3f = y := by decide
    simp only [surrogatePassBytes, h12, hy1, hy2, surrogatePassRead, List.cons_append]
    have k1 := k (c / 64 % 64) (Nat.mod_lt _ (by decide))
    have k2 := k (c % 64) (Nat.mod_lt _ (by decide))
    simp only [k1.1, k2.1, k1.2, k2.2]
    simp only [show ((0xe0 : Nat) ||| 13) &&& 0xf0 = 0xe0 by decide,
      show ((0xe0 : Nat) ||| 13) &&& 0x0f = 13 by decide, beq_self_eq_true, Bool.and_self, if_true,
      Nat.shiftLeft_eq]
    omega
  all_goals first
    | exact absurd rfl hu
    | (simp [surrogatePassBytes, surrogatePassRead]; omega)

theorem encCodeOf_same (H : Hier) (hH : HierOk H) (d e : ExcObj) (x y : String)
    (hd : H.sub d.cls "UnicodeError" = true) (he : H.sub e.cls "UnicodeError" = true)
    (henc : d.encoding = e.encoding) : encCodeOf H d x = encCodeOf H e y := by
  simp [encCodeOf, getEncoding, checkType, hd, he, henc, ok_bind]

/-- **surrogatepass round-trips through its two handlers, in each of its five encodings.**
The bytes `surrogatepass` writes for a lone surrogate under an exception naming any encoding,
placed at `start` of the `object` of a decode error naming the same encoding, decode back to that
surrogate. codecs.rst: surrogatepass "allow[s] encoding and decoding surrogate code point
(U+D800 - U+DFFF) as normal code point" for utf-8, utf-16, utf-32 and their big- and little-endian forms.
Scope: the decode error's MRO keeps `UnicodeError` (a custom `mro()` that drops it makes
`PyUnicodeDecodeError_GetEncoding` refuse the object, `OddClasses`). -/
def SurrogatePassHandlersRoundTrip : Prop :=
  ∀ (H : Hier) (capi : Except PyExc (Nat → Option Str)) (e d : ExcObj) (c : Nat) (pre post out : Bytes)
    (pos : Nat),
    HierOk H → isSurrogate c = true → H.isEnc e.cls = true → e.object = .str [c] → e.start ≤ 0 →
    1 ≤ e.stop →
    callBuiltin H capi .surrogatepass e = .ok (.bytes out, pos) →
    H.isDec d.cls = true → H.sub d.cls "UnicodeError" = true → d.encoding = e.encoding →
    d.object = .bytes (pre ++ out ++ post) →
    d.start = pre.length → Bytes.Valid post →
    callBuiltin H capi .surrogatepass d = .ok (.str [c], pre.length + out.length)

theorem surrogatePassHandlersRoundTrip_proven : SurrogatePassHandlersRoundTrip := by
  intro H capi e d c pre post out pos hH hs hE heo hst hen he hD hdU henc hdo hds hpv
  have hDE := hH.dec_not_enc hD
  simp only [callBuiltin, surrogatePassErrors, hE, if_true, surrogatePassEncode] at he
  cases hc : encCodeOf H e "UnicodeEncodeError" with
  | error x => rw [hc] at he; cases he
  | ok code =>
    have heU : H.sub e.cls "UnicodeError" = true := by
      cases hn : H.sub e.cls "UnicodeError"
      · simp [encCodeOf, getEncoding, checkType, hn, raiseT, bind, Except.bind] at hc
      · rfl
    have hcode := encCodeOf_same H hH d e "UnicodeDecodeError" "UnicodeEncodeError" hdU heU henc
    rw [hc, ok_bind] at he
    split at he
    · obtain ⟨x, hx⟩ := bail_isError (α := Body) H e
      rw [hx] at he; cases he
    · rename_i hu
      have hst0 := stOf_zero e 1 hst
      have hen0 := enOf_full e 1 (by simpa using hen)
      simp only [getParams_str e [c] heo, ok_bind, List.length_singleton, hst0, hen0] at he
      have hg : guardRange code.bytelength ⟨[c], 1, 0, 1, 1 - 0⟩ = (1, 1) := by
        have := bytelength_pos code hu
        unfold guardRange ssizeMaxN
        rw [if_neg]; simp only [Nat.sub_zero]
        simp only [Nat.sub_zero, gt_iff_lt, Nat.not_lt]
        exact (Nat.le_div_iff_mul_le this.1).2 (by omega)
      simp only [hg, slice, List.drop_zero, Nat.sub_zero, List.take_one, List.head?_cons,
        Option.toList_some] at he
      rw [passWrite_eq] at he
      simp only [List.all_cons, hs, List.all_nil, Bool.and_self, if_true, bailOn_ok, ok_bind,
        List.flatMap_cons,
        List.flatMap_nil, List.append_nil, pure, Except.pure, Functor.map, Except.map, Body.result,
        Except.ok.injEq, Prod.mk.injEq, Rep.bytes.injEq] at he
      obtain ⟨hout, _⟩ := he
      subst hout
      simp only [callBuiltin, surrogatePassErrors, hDE, Bool.false_eq_true, if_false, hD, if_true,
        surrogatePassDecode, hcode, hc, ok_bind, hu]
      have hlen : (pre ++ passBytes code c ++ post).length =
          pre.length + code.bytelength + post.length := by
        rw [List.length_append, List.length_append, passBytes_length]
      have hb := bytelength_pos code hu
      have hst1 : stOf d (pre ++ passBytes code c ++ post).length = pre.length := by
        unfold stOf adjustStart; rw [hds, hlen]; simp only; split <;> split <;> (try split) <;> omega
      rw [getParams_bytes d _ hdo, ok_bind]
      simp only [hst1]
      have hcond : (pre ++ passBytes code c ++ post).length - pre.length ≥ code.bytelength := by
        rw [hlen]; omega
      rw [if_pos hcond]
      have hdrop : (pre ++ passBytes code c ++ post).drop pre.length = passBytes code c ++ post := by
        simp [List.append_assoc]
      rw [hdrop, passRead_passBytes code c post hu hs hpv]
      simp [hs, pure, Except.pure, Functor.map, Except.map, Body.result, passBytes_length]

/-! ## backslashreplace and unicode_escape -/

theorem shift_and15 (c k : Nat) : (c >>> k) &&& 15 = c / 2 ^ k % 16 := by
  rw [Nat.shiftRight_eq_div_pow, show (15 : Nat) = 2 ^ 4 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem hexDigits2 (c : Nat) : hexDigits 2 c = hex2 c := by
  simp [hexDigits, hex2, List.range, List.range.loop, shift_and15]

theorem hexDigits4 (c : Nat) : hexDigits 4 c = hex4 c := by
  simp [hexDigits, hex4, hex2, List.range, List.range.loop, shift_and15]

theorem hexDigits8 (c : Nat) (h : c ≤ maxUnicode) : hexDigits 8 c = hex8 c := by
  have hm : maxUnicode = 0x10FFFF := rfl
  have h28 : c / 2 ^ 28 % 16 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have h24 : c / 2 ^ 24 % 16 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  simp [hexDigits, hex8, hex4, hex2, List.range, List.range.loop, shift_and15, h28, h24, hexLower]

theorem stepUE_escape (names cons) (c : Nat) (r : List Nat) (hc : c ≤ maxUnicode) :
    stepUnicodeEscape names cons (escapeEncodeChar c ++ r) = .char c (escapeEncodeChar c).length := by
  unfold escapeEncodeChar
  split
  · rw [hexDigits2]; simp only [List.cons_append, List.nil_append]
    exact stepUE_x names cons r c (by omega)
  · split
    · rw [hexDigits4]; simp only [List.cons_append, List.nil_append]
      exact stepUE_u names cons r c (by omega)
    · rw [hexDigits8 c hc]; simp only [List.cons_append, List.nil_append]
      exact stepUE_U names cons r c hc

theorem escapeEncodeChar_pos (c : Nat) : 1 ≤ (escapeEncodeChar c).length := by
  unfold escapeEncodeChar; split <;> (try split) <;> simp

/-- Decoding `flatMap enc` with `unicode_escape` gives the characters back, for a per-character
escape that the decoder reads back. -/
theorem ue_flat (enc : Nat → List Nat) (hpos : ∀ c, 1 ≤ (enc c).length) (s : Str)
    (names : List Nat → Option Nat) (final : Bool)
    (hstep : ∀ c ∈ s, ∀ r, stepUnicodeEscape names (!final) (enc c ++ r) = .char c (enc c).length) :
    unicodeEscapeDecode (s.flatMap enc) .strict names final = .ok (s, (s.flatMap enc).length) := by
  unfold unicodeEscapeDecode
  have hlen := length_le_flat enc hpos s
  cases hs : s with
  | nil => simp
  | cons c cs =>
    subst hs
    simp only [length_flat_pos enc hpos, Bool.false_eq_true, if_false]
    have := decodeDriver_flatMap (stepUnicodeEscape names !final) enc .strict
      "unicodeescape" .unknown ((c :: cs).flatMap enc) (c :: cs) rfl hstep
      (((c :: cs).flatMap enc).length + 1) 0 [] (by omega)
    simpa using this

/-- **backslashreplace writes escapes that unicode_escape reads back.** For every encode or
translate error with a `str` object and any `start` and `end`, decoding the replacement with
`unicode_escape` gives the characters it replaced; for every decode error, it gives the code
points of the bytes it replaced. codecs.rst: backslashreplace uses `\xhh`, `\uxxxx`,
`\Uxxxxxxxx` on encoding and `\xhh` on decoding. -/
def BackslashReplaceUnicodeEscape : Prop :=
  ∀ (H : Hier) (capi : Except PyExc (Nat → Option Str)) (e : ExcObj) (r : Str) (pos : Nat)
    (names : List Nat → Option Nat) (final : Bool),
    HierOk H → callBuiltin H capi .backslashreplace e = .ok (.str r, pos) →
    ∀ l, (e.object = .str l ∧ Str.Valid l ∨ e.object = .bytes l ∧ Bytes.Valid l) →
      unicodeEscapeDecode r .strict names final = .ok (slice l (stOf e l.length) pos, r.length)

theorem backslashReplaceUnicodeEscape_proven : BackslashReplaceUnicodeEscape := by
  intro H capi e r pos names final hH hr l hl
  simp only [callBuiltin, backslashReplaceErrors] at hr
  have enc : ∀ s, e.object = .str s → Str.Valid s →
      Body.result <$> backslashEncode e = .ok (.str r, pos) →
      unicodeEscapeDecode r .strict names final = .ok (slice s (stOf e s.length) pos, r.length) := by
    intro s hs hv h
    simp only [backslashEncode, getParams_str e s hs, ok_bind, pure, Except.pure, Functor.map,
      Except.map, Body.result, Except.ok.injEq, Prod.mk.injEq, Rep.str.injEq] at h
    obtain ⟨hr', hp⟩ := h
    subst hr'; subst hp
    rw [flatMap_congr _ (fun x _ => writeUnicodeHex_eq x)]
    exact ue_flat escapeEncodeChar escapeEncodeChar_pos _ names final
      (fun c hc r => stepUE_escape names _ c r (hv c (mem_slice hc)))
  split at hr
  · rcases hl with ⟨hs, hv⟩ | ⟨hb, _⟩
    · exact enc l hs hv hr
    · simp [backslashEncode, getParams, asAttr, hb, raiseT, bind, Except.bind, Functor.map,
        Except.map] at hr
  · split at hr
    · rcases hl with ⟨hs, _⟩ | ⟨hb, hv⟩
      · simp [backslashDecode, getParams, asAttr, hs, raiseT, bind, Except.bind, Functor.map,
          Except.map] at hr
      · simp only [backslashDecode, getParams_bytes e l hb, ok_bind, pure, Except.pure, Functor.map,
          Except.map, Body.result, Except.ok.injEq, Prod.mk.injEq, Rep.str.injEq] at hr
        obtain ⟨hr', hp⟩ := hr
        subst hr'; subst hp
        rw [flatMap_congr _ (fun x _ => byteHex_eq x)]
        refine ue_flat (fun b => [92, 120] ++ hexDigits 2 b) (fun _ => by simp) _ names final ?_
        intro c hc r
        rw [hexDigits2]; simp only [List.cons_append, List.nil_append, List.length_cons, hex2,
          List.length_nil]
        exact stepUE_x names _ r c (hv c (mem_slice hc))
    · split at hr
      · rcases hl with ⟨hs, hv⟩ | ⟨hb, _⟩
        · exact enc l hs hv hr
        · simp [backslashEncode, getParams, asAttr, hb, raiseT, bind, Except.bind, Functor.map,
            Except.map] at hr
      · simp [wrongType, raiseT, Functor.map, Except.map] at hr

end PyLean.UnicodeObj.Codecs
