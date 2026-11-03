import PyLean.UnicodeObj.CodecsErrLoops

/-!
The handlers of `Python/codecs.c`, called on an exception object directly, against the model of
the same handlers as the codec loops see them (`encodeHandlerCall`, `decodeHandlerCall` in
`CodecHandlers.lean`, difftested through real `encode` and `decode` calls).
-/

namespace PyLean.UnicodeObj.Codecs

open PyLean PyLean.UnicodeObj

/-- A direct call's result in the codec-loop model's terms: raising the argument itself is
raising the exception the codec built, `bad`. -/
def lowerEnc (bad : PyExc) : HPy (Rep × Nat) → Py (EncRep × Nat)
  | .ok (.str s, p) => .ok (.str s, p)
  | .ok (.bytes b, p) => .ok (.bytes b, p)
  | .error .reraise => .error bad
  | .error (.exc x) => .error x

/-- The same for a decode handler, whose replacement must be a `str`. -/
def lowerDec (bad : PyExc) : HPy (Rep × Nat) → Py (Str × Nat)
  | .ok (.str s, p) => .ok (s, p)
  | .ok (.bytes _, _) => .error .modelFuel
  | .error .reraise => .error bad
  | .error (.exc x) => .error x

/-- Where a handler stops on a `str` object whose clipped range is `st`..`en`: `en`, unless a
guard against an oversized replacement cuts the range first (codecs.c:915-919, :982-986,
:1104-1106, :1249-1253). `cutStop_fits` shows it is `en` whenever the replacement fits in a
`Py_ssize_t`. -/
def cutStop (h : ErrHandler) (getname : Nat → Option Str) (code : EncCode) (s : Str) (st en : Nat) :
    Nat :=
  let p : Params := ⟨s, s.length, st, en, en - st⟩
  match h with
  | .xmlcharrefreplace | .backslashreplace => (guardRange 10 p).1
  | .surrogatepass => (guardRange code.bytelength p).1
  | .namereplace => (nameSizeLoop getname (slice s st en) st 0).1
  | _ => en

/-- **Encode errors.** On every object below `UnicodeEncodeError` whose `object` is a `str`,
with any `start` and `end`, each standard handler gives what the codec-loop model gives for the
clipped range: `start` clipped to `[0, max(0, len-1)]`, `end` to `[min(1, len), len]`, then cut
by `cutStop`. The `encoding` attribute matters only to `surrogatepass`. -/
def EncodeAgree : Prop :=
  ∀ (H : Hier) (getname : Nat → Option Str) (h : ErrHandler) (e : ExcObj) (s : Str) (code : EncCode),
    HierOk H → H.isEnc e.cls = true → e.object = .str s → Str.Valid s →
    (h = .surrogatepass → encCodeOf H e "UnicodeEncodeError" = .ok code) →
    let st := stOf e s.length
    let stop := cutStop h getname code s st (enOf e s.length)
    lowerEnc (encodeError "" s st stop "") (callBuiltin H (.ok getname) h e) =
      encodeHandlerCall h getname "" code s st stop ""

/-- **Decode errors.** The same below `UnicodeDecodeError` with a `bytes` object. The class
must print as `UnicodeDecodeError` because the model of the codec loop names it so in the
`TypeError` of `xmlcharrefreplace` and `namereplace`. -/
def DecodeAgree : Prop :=
  ∀ (H : Hier) (getname : Nat → Option Str) (h : ErrHandler) (e : ExcObj) (b : Bytes) (code : EncCode),
    HierOk H → H.isDec e.cls = true → e.tpName = "UnicodeDecodeError" → e.object = .bytes b →
    Bytes.Valid b →
    (h = .surrogatepass → encCodeOf H e "UnicodeDecodeError" = .ok code) →
    let st := stOf e b.length
    let en := enOf e b.length
    lowerDec (decodeError "" b st en "") (callBuiltin H (.ok getname) h e) =
      decodeHandlerCall h "" code b st en ""

/-- **Translate errors.** `ignore`, `replace` (U+FFFD per character) and `backslashreplace`
(the encode escapes) handle them; the other handlers refuse them. -/
def TranslateSpec : Prop :=
  ∀ (H : Hier) (getname : Nat → Option Str) (h : ErrHandler) (e : ExcObj) (s : Str),
    HierOk H → H.isTr e.cls = true → e.object = .str s →
    let st := stOf e s.length
    let en := enOf e s.length
    callBuiltin H (.ok getname) h e =
      match h with
      | .strict => .error .reraise
      | .ignore => .ok (.str [], en)
      | .replace => .ok (.str (List.replicate (en - st) 0xfffd), en)
      | .backslashreplace =>
        let stop := cutStop .backslashreplace getname .unknown s st en
        .ok (.str ((slice s st stop).flatMap escapeEncodeChar), stop)
      | _ => wrongType e

def HandlersAgree : Prop := EncodeAgree ∧ DecodeAgree ∧ TranslateSpec

theorem guardRange_fst (w : Nat) (s : List Nat) (st en : Nat) (sl : Nat) (hsl : sl = en - st) :
    (guardRange w ⟨s, s.length, st, en, sl⟩).1 = (guardRange w ⟨s, s.length, st, en, en - st⟩).1 := by
  subst hsl; rfl

theorem guardRange_snd (w : Nat) (s : List Nat) (st en : Nat) (hen : en ≤ s.length) (hst : st ≤ s.length) :
    (guardRange w ⟨s, s.length, st, en, en - st⟩).2 =
      (guardRange w ⟨s, s.length, st, en, en - st⟩).1 - st := by
  unfold guardRange
  split <;> simp

theorem guardRange_le (w : Nat) (s : List Nat) (st en : Nat) (hen : en ≤ s.length) :
    (guardRange w ⟨s, s.length, st, en, en - st⟩).1 ≤ s.length := by
  unfold guardRange
  split <;> simp <;> omega

theorem flatMap_congr {f g : Nat → List Nat} : ∀ (l : List Nat), (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.flatMap_cons]
    rw [h x (by simp), flatMap_congr xs (fun y hy => h y (by simp [hy]))]

theorem drop_take_slice (l : List Nat) (a b : Nat) : (l.drop a).take (b - a) = slice l a b := rfl

theorem mem_slice {l : List Nat} {a b x : Nat} (h : x ∈ slice l a b) : x ∈ l :=
  List.mem_of_mem_drop (List.mem_of_mem_take h)

theorem encodeAgree_proven : EncodeAgree := by
  intro H getname h e s code hH hE hobj hv hcode
  have hD := hH.enc_not_dec hE
  have hT := hH.enc_not_tr hE
  have hp := getParams_str e s hobj
  have hle := enOf_le e s.length
  have hsle := stOf_le e s.length
  simp only
  cases h with
  | strict =>
    simp [callBuiltin, strictErrors, hH.uerr_base (hH.enc_uerr hE), lowerEnc, encodeHandlerCall]
  | ignore =>
    simp [callBuiltin, ignoreErrors, hE, ignoreError, hp, bind, Except.bind, pure, Except.pure,
      Functor.map, Except.map, Body.result, lowerEnc, encodeHandlerCall, cutStop]
  | replace =>
    simp [callBuiltin, replaceErrors, hE, replaceEncode, hp, bind, Except.bind, pure, Except.pure,
      Functor.map, Except.map, Body.result, lowerEnc, encodeHandlerCall, cutStop]
    omega
  | xmlcharrefreplace =>
    simp only [callBuiltin, xmlCharRefReplaceErrors, hE, Bool.not_true, Bool.false_eq_true, if_false,
      hp, bind, Except.bind, pure, Except.pure, Functor.map, Except.map, Body.result, lowerEnc,
      encodeHandlerCall, cutStop]
    congr 3
    refine flatMap_congr _ (fun x hx => xmlBlock_eq x (hv x (mem_slice hx)))
  | backslashreplace =>
    simp only [callBuiltin, backslashReplaceErrors, hE, if_true, backslashEncode, hp, bind, Except.bind, pure,
      Except.pure, Functor.map, Except.map, Body.result, lowerEnc, encodeHandlerCall, cutStop]
    congr 3
    exact flatMap_congr _ (fun x _ => writeUnicodeHex_eq x)
  | namereplace =>
    simp only [callBuiltin, nameReplaceErrors, hE, Bool.not_true, Bool.false_eq_true, if_false,
      hp, bind, Except.bind, pure, Except.pure, Functor.map, Except.map, Body.result, lowerEnc,
      encodeHandlerCall, cutStop]
    congr 3
    refine flatMap_congr _ (fun x _ => ?_)
    unfold nameBlock
    cases getname x <;> simp [writeUnicodeHex_eq]
  | surrogatepass =>
    have hc := hcode rfl
    simp only [callBuiltin, surrogatePassErrors, hE, if_true, surrogatePassEncode]
    · simp only [bind, Except.bind, hc]
      by_cases hu : code = .unknown
      · subst hu
        simp [lowerEnc, encodeHandlerCall, Functor.map, Except.map]
      · simp only [hu, if_false, hp, pure, Except.pure]
        rw [passWrite_eq]
        simp only [encodeHandlerCall, cutStop, drop_take_slice]
        have hu' : (code == .unknown) = false := by simp [hu]
        by_cases hall : (slice s (stOf e s.length)
            (guardRange code.bytelength ⟨s, s.length, stOf e s.length, enOf e s.length,
              enOf e s.length - stOf e s.length⟩).1).all isSurrogate = true
        · rw [if_pos hall]
          simp only [hu', hall, Bool.false_or, Bool.not_true, Bool.false_eq_true,
            if_false, Functor.map, Except.map, Body.result, lowerEnc]
          congr 3
          refine flatMap_congr _ (fun x hx => passBytes_eq code x ?_)
          exact List.all_eq_true.1 hall x hx
        · have hall' : (slice s (stOf e s.length)
            (guardRange code.bytelength ⟨s, s.length, stOf e s.length, enOf e s.length,
              enOf e s.length - stOf e s.length⟩).1).all isSurrogate = false := by simpa using hall
          rw [if_neg hall]
          simp [hu', hall', lowerEnc, Functor.map, Except.map]
  | surrogateescape =>
    simp only [callBuiltin, surrogateEscapeErrors, hE, if_true, surrogateEscapeEncode, hp, bind,
      Except.bind]
    rw [escWrite_eq]
    simp only [encodeHandlerCall, cutStop, drop_take_slice]
    by_cases hall : (slice s (stOf e s.length) (enOf e s.length)).all
        (fun c => decide (0xdc80 ≤ c) && decide (c ≤ 0xdcff)) = true
    · simp [hall, lowerEnc, Functor.map, Except.map, Body.result, pure, Except.pure]
    · simp [hall, lowerEnc, Functor.map, Except.map, Body.result, pure, Except.pure]

theorem decodeAgree_proven : DecodeAgree := by
  intro H getname h e b code hH hD htp hobj hv hcode
  have hE := hH.dec_not_enc hD
  have hT := hH.dec_not_tr hD
  have hp := getParams_bytes e b hobj
  have hle := enOf_le e b.length
  have hsle := stOf_le e b.length
  have hU := hH.dec_uerr hD
  simp only
  cases h with
  | strict =>
    simp [callBuiltin, strictErrors, hH.uerr_base hU, lowerDec, decodeHandlerCall]
  | ignore =>
    simp [callBuiltin, ignoreErrors, hE, hT, hD, ignoreError, hp, bind, Except.bind, pure,
      Except.pure, Functor.map, Except.map, Body.result, lowerDec, decodeHandlerCall]
  | replace =>
    simp [callBuiltin, replaceErrors, hE, hD, replaceDecode, decodeGetEnd, checkType, hU, hp, bind,
      Except.bind, pure, Except.pure, Functor.map, Except.map, Body.result, lowerDec,
      decodeHandlerCall, replacementChars]
  | xmlcharrefreplace =>
    simp [callBuiltin, xmlCharRefReplaceErrors, hE, wrongType, raiseT, htp, Functor.map,
      Except.map, lowerDec, decodeHandlerCall, wrongExceptionType]
  | backslashreplace =>
    simp only [callBuiltin, backslashReplaceErrors, hE, hD, Bool.false_eq_true, if_false, if_true,
      backslashDecode, hp, bind, Except.bind, pure, Except.pure, Functor.map, Except.map,
      Body.result, lowerDec, decodeHandlerCall, drop_take_slice]
    rw [flatMap_congr _ (fun x _ => byteHex_eq x)]
  | namereplace =>
    simp [callBuiltin, nameReplaceErrors, hE, wrongType, raiseT, htp, Functor.map, Except.map,
      lowerDec, decodeHandlerCall, wrongExceptionType, bind, Except.bind]
  | surrogatepass =>
    have hc := hcode rfl
    simp only [callBuiltin, surrogatePassErrors, hE, hD, Bool.false_eq_true, if_false, if_true,
      surrogatePassDecode]
    · simp only [bind, Except.bind, hc]
      by_cases hu : code = .unknown
      · subst hu
        simp [lowerDec, decodeHandlerCall, Functor.map, Except.map]
      · have hu' : (code == .unknown) = false := by simp [hu]
        simp only [hu, if_false, hp, decodeHandlerCall, hu', Bool.false_eq_true]
        have hrd : (if b.length - stOf e b.length ≥ code.bytelength
            then passRead code (b.drop (stOf e b.length)) else 0) =
            (if b.length - stOf e b.length ≥ code.bytelength
            then surrogatePassRead code (b.drop (stOf e b.length)) else 0) := by
          split
          · rw [passRead_eq code _ (by simp; omega) (fun x hx => hv x (List.mem_of_mem_drop hx))]
          · rfl
        rw [hrd]
        by_cases hs : isSurrogate (if b.length - stOf e b.length ≥ code.bytelength
            then surrogatePassRead code (b.drop (stOf e b.length)) else 0) = true
        · simp [hs, Functor.map, Except.map, Body.result, lowerDec, pure, Except.pure]
        · simp [hs, Functor.map, Except.map, Body.result, lowerDec, pure, Except.pure]
  | surrogateescape =>
    simp only [callBuiltin, surrogateEscapeErrors, hE, hD, Bool.false_eq_true, if_false, if_true,
      surrogateEscapeDecode, hp, bind, Except.bind, decodeHandlerCall]
    rw [escConsume_eq]
    have hrun : escapeRun 4 ((b.drop (stOf e b.length)).take (enOf e b.length - stOf e b.length)) =
        escapeRun (min 4 (enOf e b.length - stOf e b.length)) (b.drop (stOf e b.length)) :=
      escapeRun_take _ _ _
    simp only [hrun]
    by_cases hz : escapeRun (min 4 (enOf e b.length - stOf e b.length)) (b.drop (stOf e b.length)) = []
    · simp [hz, lowerDec, Functor.map, Except.map]
    · have hne : (escapeRun (min 4 (enOf e b.length - stOf e b.length))
          (b.drop (stOf e b.length))).isEmpty = false := by
        cases hx : escapeRun (min 4 (enOf e b.length - stOf e b.length)) (b.drop (stOf e b.length))
        · exact absurd hx hz
        · rfl
      have hlen : (escapeRun (min 4 (enOf e b.length - stOf e b.length))
          (b.drop (stOf e b.length))).length ≠ 0 := by
        intro h0; exact hz (List.eq_nil_of_length_eq_zero h0)
      simp [hne, hlen, lowerDec, Functor.map, Except.map, Body.result, pure, Except.pure]

theorem translateSpec_proven : TranslateSpec := by
  intro H getname h e s hH hT hobj
  have hE := hH.tr_not_enc hT
  have hD := hH.tr_not_dec hT
  have hp := getParams_str e s hobj
  have hU := hH.tr_uerr hT
  simp only
  cases h with
  | strict => simp [callBuiltin, strictErrors, hH.uerr_base hU]
  | ignore =>
    simp [callBuiltin, ignoreErrors, hE, hT, ignoreError, hp, bind, Except.bind, pure, Except.pure,
      Functor.map, Except.map, Body.result]
  | replace =>
    simp [callBuiltin, replaceErrors, hE, hD, hT, replaceTranslate, hp, bind, Except.bind, pure,
      Except.pure, Functor.map, Except.map, Body.result, replacementChars]
  | xmlcharrefreplace =>
    simp [callBuiltin, xmlCharRefReplaceErrors, hE, Functor.map, Except.map, wrongType, raiseT]
  | backslashreplace =>
    simp only [callBuiltin, backslashReplaceErrors, hE, hD, hT, Bool.false_eq_true, if_false,
      if_true, backslashEncode, hp, bind, Except.bind, pure, Except.pure, Functor.map, Except.map,
      Body.result, cutStop]
    congr 3
    exact flatMap_congr _ (fun x _ => writeUnicodeHex_eq x)
  | namereplace =>
    simp [callBuiltin, nameReplaceErrors, hE, Functor.map, Except.map, wrongType, raiseT, bind,
      Except.bind]
  | surrogatepass =>
    simp [callBuiltin, surrogatePassErrors, hE, hD, Functor.map, Except.map, wrongType, raiseT]
  | surrogateescape =>
    simp [callBuiltin, surrogateEscapeErrors, hE, hD, Functor.map, Except.map, wrongType, raiseT]

theorem handlersAgree_proven : HandlersAgree :=
  ⟨encodeAgree_proven, decodeAgree_proven, translateSpec_proven⟩

end PyLean.UnicodeObj.Codecs
