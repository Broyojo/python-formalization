import PyLean.UnicodeObj.CodecCallback

/-!
Properties of the error handler callback paths.
-/

namespace PyLean.UnicodeObj

open PyLean

/-! ## The loops over `EH` are the loops over `ErrHandler` on `.std` -/

theorem ucs1EncodeLoopX_std (input : Str) (limit : Nat) (h : ErrHandler)
    (nameOf : Nat → Option Str) :
    ∀ (fuel : Nat) (hist : List EncView) (pos : Nat) (rest : List Nat) (out : Bytes),
      ucs1EncodeLoopX input limit (.std h) nameOf fuel hist pos rest out =
        ucs1EncodeLoop input limit h nameOf fuel pos rest out := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro hist pos rest out
    cases rest with
    | nil => rfl
    | cons c cs =>
      by_cases hc : c < limit
      · simp only [ucs1EncodeLoopX, ucs1EncodeLoop, if_pos hc]
        exact ih ..
      · simp only [ucs1EncodeLoopX, ucs1EncodeLoop, if_neg hc]
        have via : ∀ (reason : String) (collstart collend : Nat) (o : Bytes),
            ((match encHandlerStep (.std h) nameOf (if limit == 256 then "latin-1" else "ascii") .unknown
                reason input hist collstart collend with
             | .error e => .error e
             | .ok (hist', rep, newpos) =>
               match rep with
               | .bytes b => ucs1EncodeLoopX input limit (.std h) nameOf fuel hist' newpos (input.drop newpos) (o ++ b)
               | .str r =>
                 if r.all (· < limit) then
                   ucs1EncodeLoopX input limit (.std h) nameOf fuel hist' newpos (input.drop newpos) (o ++ r)
                 else .error (encodeError (if limit == 256 then "latin-1" else "ascii") input collstart collend reason)) : Py Bytes) =
            (match encodeHandlerCall h nameOf (if limit == 256 then "latin-1" else "ascii") .unknown input
                collstart collend reason with
             | .error e => .error e
             | .ok (rep, newpos) =>
               match rep with
               | .bytes b => ucs1EncodeLoop input limit h nameOf fuel newpos (input.drop newpos) (o ++ b)
               | .str r =>
                 if r.all (· < limit) then
                   ucs1EncodeLoop input limit h nameOf fuel newpos (input.drop newpos) (o ++ r)
                 else .error (encodeError (if limit == 256 then "latin-1" else "ascii") input collstart collend reason)) := by
          intro reason collstart collend o
          simp only [encHandlerStep]
          generalize encodeHandlerCall _ _ _ _ _ _ _ _ = d
          cases d with
          | error x => rfl
          | ok p =>
            obtain ⟨rep, newpos⟩ := p
            cases rep with
            | bytes b => exact ih ..
            | str r =>
              simp only
              split
              · exact ih ..
              · rfl
        cases h
        all_goals first
          | rfl
          | exact ih ..
          | exact via ..
          | (dsimp only
             split
             · exact ih ..
             · exact via ..)

theorem encodeWideLoopX_std (charBytes : Nat → List Nat) (unitSize : Nat) (h : ErrHandler)
    (nameOf : Nat → Option Str) (enc : String) (code : EncCode) (input : Str) :
    ∀ (fuel : Nat) (hist : List EncView) (pos : Nat) (rest : List Nat) (out : Bytes),
      encodeWideLoopX charBytes unitSize (.std h) nameOf enc code input fuel hist pos rest out =
        encodeWideLoop charBytes unitSize h nameOf enc code input fuel pos rest out := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro hist pos rest out
    cases rest with
    | nil => rfl
    | cons c cs =>
      by_cases hc : (!isSurrogate c) = true
      · simp only [encodeWideLoopX, encodeWideLoop, if_pos hc]
        exact ih ..
      · simp only [encodeWideLoopX, encodeWideLoop, if_neg hc, encHandlerStep]
        generalize encodeHandlerCall _ _ _ _ _ _ _ _ = d
        cases d with
        | error x => rfl
        | ok p =>
          obtain ⟨rep, newpos⟩ := p
          cases rep with
          | bytes b =>
            simp only
            split
            · rfl
            · exact ih ..
          | str r =>
            simp only
            split
            · rfl
            · exact ih ..

theorem utf8EncodeLoopX_std (input : Str) (h : ErrHandler) (nameOf : Nat → Option Str) :
    ∀ (fuel : Nat) (hist : List EncView) (pos : Nat) (rest : List Nat) (out : List Nat),
      utf8EncodeLoopX input (.std h) nameOf fuel hist pos rest out =
        utf8EncodeLoop input h fuel pos rest out := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro hist pos rest out
    cases rest with
    | nil => rfl
    | cons c cs =>
      by_cases hc : (!isSurrogate c) = true
      · simp only [utf8EncodeLoopX, utf8EncodeLoop, if_pos hc]
        exact ih ..
      · simp only [utf8EncodeLoopX, utf8EncodeLoop, if_neg hc]
        generalize surrogateRun (c :: cs) = ra
        obtain ⟨run, after⟩ := ra
        simp only
        cases h
        all_goals first
          | rfl
          | exact ih ..
          | (dsimp only
             cases List.findIdx? (fun x => !(decide (0xDC80 ≤ x) && decide (x ≤ 0xDCFF))) run with
             | none => exact ih ..
             | some k => rfl)

/-! ## Where a callback's position lands -/

/-- A handler can return any position. What reaches the decoder is inside the object as the
handler left it, and a negative position counts from that object's end, not the original's.
The view the handler saw is the error's own. -/
def DecodeCallbackPosition : Prop :=
  ∀ (cb : DecCB) (hist : List DecView) (enc reason : String) (input : Bytes) (start stop : Nat)
    (hist' : List DecView) (obj : Bytes) (rep : Str) (newpos : Nat),
    decodeCallback cb hist enc reason input start stop = .ok (hist', obj, rep, newpos) →
    newpos ≤ obj.length ∧
    hist' = hist ++ [{ object := input, encoding := enc, start, stop, reason }] ∧
    ∃ p e, cb hist' = .ret rep p e ∧ decObject input e = .ok obj ∧
      ssizeMin ≤ p ∧ p ≤ ssizeMax ∧ (newpos : Int) = if p < 0 then (obj.length : Int) + p else p

theorem ssizeOfIndex_ok {n m : Int} (h : ssizeOfIndex n = .ok m) :
    n = m ∧ ssizeMin ≤ n ∧ n ≤ ssizeMax := by
  unfold ssizeOfIndex at h
  split at h
  · cases h
  · rename_i hn
    simp only [Except.ok.injEq] at h
    subst h
    omega

theorem decodeCallbackPosition_proven : DecodeCallbackPosition := by
  intro cb hist enc reason input start stop hist' obj rep newpos h
  simp only [decodeCallback, bind, Except.bind] at h
  split at h
  · cases h
  · cases h
  · rename_i rep0 p0 e0 hcb
    split at h
    · cases h
    · rename_i p hp
      obtain ⟨rfl, h1, h2⟩ := ssizeOfIndex_ok hp
      split at h
      · cases h
      · rename_i o hobj
        by_cases hneg : p0 < 0
        · simp only [if_pos hneg] at h ⊢
          split at h
          · cases h
          · rename_i hin
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            exact ⟨by omega, rfl, p0, e0, hcb, hobj, h1, h2, by simp only [if_pos hneg]; omega⟩
        · simp only [if_neg hneg] at h ⊢
          split at h
          · cases h
          · rename_i hin
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            exact ⟨by omega, rfl, p0, e0, hcb, hobj, h1, h2, by simp only [if_neg hneg]; omega⟩

/-- The same for an encoder, where the object cannot change. -/
def EncodeCallbackPosition : Prop :=
  ∀ (cb : EncCB) (hist : List EncView) (enc reason : String) (input : Str) (start stop : Nat)
    (hist' : List EncView) (rep : EncRep) (newpos : Nat),
    encodeCallback cb hist enc reason input start stop = .ok (hist', rep, newpos) →
    newpos ≤ input.length ∧
    hist' = hist ++ [{ object := input, encoding := enc, start, stop, reason }] ∧
    ∃ p, cb hist' = .ret rep p ∧ ssizeMin ≤ p ∧ p ≤ ssizeMax ∧
      (newpos : Int) = if p < 0 then (input.length : Int) + p else p

theorem encodeCallbackPosition_proven : EncodeCallbackPosition := by
  intro cb hist enc reason input start stop hist' rep newpos h
  simp only [encodeCallback, bind, Except.bind] at h
  split at h
  · cases h
  · cases h
  · split at h <;> cases h
  · rename_i rep0 p0 hcb
    split at h
    · cases h
    · rename_i p hp
      obtain ⟨rfl, h1, h2⟩ := ssizeOfIndex_ok hp
      by_cases hneg : p0 < 0
      · simp only [if_pos hneg] at h ⊢
        split at h
        · cases h
        · rename_i hin
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨by omega, rfl, p0, hcb, h1, h2, by simp only [if_pos hneg]; omega⟩
      · simp only [if_neg hneg] at h ⊢
        split at h
        · cases h
        · rename_i hin
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨by omega, rfl, p0, hcb, h1, h2, by simp only [if_neg hneg]; omega⟩

/-! ## The standard handlers through the callback path -/

/-- `get_standard_encoding_impl`, Python/codecs.c:1148-1198, on the names the decoders pass. -/
def codeOf (enc : String) : EncCode :=
  if enc == "utf-8" then .utf8
  else if enc == "utf-16-le" then .utf16le
  else if enc == "utf-16-be" then .utf16be
  else if enc == "utf-32-le" then .utf32le
  else if enc == "utf-32-be" then .utf32be
  else .unknown

/-- A callback that does what a standard handler does: `PyCodec_*Errors` as `register_error` gets
them. It reads the encoding from the exception, as `PyCodec_SurrogatePassErrors` does. -/
def mimicDec (h : ErrHandler) : DecCB := fun hist =>
  match hist.getLast? with
  | none => .bad
  | some v =>
    match decodeHandlerCall h v.encoding (codeOf v.encoding) v.object v.start v.stop v.reason with
    | .error e => .raises e
    | .ok (rep, newpos) => .ret rep newpos .keep

theorem ssizeOfIndex_nat {n : Nat} (h : (n : Int) ≤ ssizeMax) : ssizeOfIndex n = .ok n := by
  unfold ssizeOfIndex
  rw [if_neg]
  unfold ssizeMin
  omega

theorem decodeCallback_ok {cb : DecCB} {hist : List DecView} {enc reason : String} {input : Bytes}
    {start stop newpos : Nat} {rep : Str} (hs : (input.length : Int) ≤ ssizeMax)
    (hb : newpos ≤ input.length)
    (hc : cb (hist ++ [{ object := input, encoding := enc, start, stop, reason }]) =
      .ret rep newpos .keep) :
    decodeCallback cb hist enc reason input start stop =
      .ok (hist ++ [{ object := input, encoding := enc, start, stop, reason }], input, rep, newpos) := by
  have hn : ((newpos : Nat) : Int) ≤ ssizeMax := by omega
  simp only [decodeCallback, hc, ssizeOfIndex_nat hn, bind, Except.bind, decObject]
  rw [if_neg (by omega), if_neg (by omega)]
  simp

theorem escapeRun_len (n : Nat) (l : List Nat) : (escapeRun n l).length ≤ l.length := by
  induction n generalizing l with
  | zero => simp [escapeRun]
  | succ n ih =>
    cases l with
    | nil => simp [escapeRun]
    | cons b bs =>
      simp only [escapeRun]
      split
      · simp
      · simp only [List.length_cons]
        have := ih bs
        omega

/-- Past `start`, a standard handler stays inside the input. -/
theorem decodeHandler_bound {h : ErrHandler} {enc : String} {code : EncCode} {input : Bytes}
    {start stop : Nat} {reason : String} {rep : Str} {newpos : Nat} (hs : stop ≤ input.length)
    (he : decodeHandlerCall h enc code input start stop reason = .ok (rep, newpos)) :
    newpos ≤ input.length := by
  cases h <;> simp only [decodeHandlerCall] at he
  case strict | xmlcharrefreplace | namereplace => cases he
  case ignore | replace | backslashreplace =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at he
    omega
  case surrogateescape =>
    split at he
    · cases he
    · rename_i hne
      simp only [Except.ok.injEq, Prod.mk.injEq] at he
      have h1 := escapeRun_len 4 ((input.drop start).take (stop - start))
      have h2 : 0 < (escapeRun 4 ((input.drop start).take (stop - start))).length := by
        cases hr : escapeRun 4 ((input.drop start).take (stop - start)) with
        | nil => simp [hr] at hne
        | cons _ _ => simp
      simp only [List.length_take, List.length_drop] at h1
      have := he.2
      omega
  case surrogatepass =>
    split at he
    · cases he
    · rename_i hc
      have hu : code ≠ .unknown := by
        intro e; subst e; simp at hc
      have hb := bytelength_pos hu
      have h0 : isSurrogate 0 = false := by decide
      repeat' split at he
      all_goals first
        | (cases he; done)
        | (cases he; omega)
        | (exfalso; simp_all)

/-- A decoder step stays inside the bytes it was given. -/
structure StepBound (step : List Nat → DStep) : Prop where
  fail : ∀ rest r s e, step rest = .fail r s e → e ≤ rest.length
  char : ∀ rest c n, step rest = .char c n → n ≤ rest.length
  multi : ∀ rest w n, step rest = .multi w n → n ≤ rest.length

theorem mimic_last (h : ErrHandler) (hist : List DecView) (v : DecView) :
    mimicDec h (hist ++ [v]) =
      match decodeHandlerCall h v.encoding (codeOf v.encoding) v.object v.start v.stop v.reason with
      | .error e => .raises e
      | .ok (rep, newpos) => .ret rep newpos .keep := by
  simp [mimicDec]

/-- Going through `unicode_decode_call_errorhandler_writer` changes nothing for a standard handler.
For most decoders C has no other way to reach one, and `ErrHandler` is the shortcut around it. -/
theorem driver_mimic (step : List Nat → DStep) (hb : StepBound step) (h : ErrHandler) (enc : String)
    (input : Bytes) (hs : (input.length : Int) ≤ ssizeMax) :
    ∀ (fuel : Nat) (hist1 hist2 : List DecView) (pos : Nat) (rest : List Nat) (out : Str),
      rest = input.drop pos → pos ≤ input.length →
      decodeDriverX step (.custom (mimicDec h)) enc (codeOf enc) none fuel input hist1 pos rest out =
        decodeDriverX step (.std h) enc (codeOf enc) none fuel input hist2 pos rest out := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro hist1 hist2 pos rest out hr hp
    have hl : rest.length = input.length - pos := by rw [hr, List.length_drop]
    simp only [decodeDriverX]
    cases hst : step rest with
    | char c n =>
      have := hb.char _ _ _ hst
      exact ih _ _ _ _ _ (by rw [hr, List.drop_drop]) (by omega)
    | multi w n =>
      have := hb.multi _ _ _ hst
      exact ih _ _ _ _ _ (by rw [hr, List.drop_drop]) (by omega)
    | stop => rfl
    | raise e => rfl
    | fail r s e =>
      have he := hb.fail _ _ _ _ hst
      dsimp only
      simp only [handlerStep]
      cases hd : decodeHandlerCall h enc (codeOf enc) input (pos + s) (pos + e) r with
      | error x =>
        have hc : mimicDec h (hist1 ++ [⟨input, enc, pos + s, pos + e, r⟩]) = .raises x := by
          rw [mimic_last]
          simp only [hd]
        simp [decodeCallback, hc, bind, Except.bind]
      | ok p =>
        obtain ⟨w, newpos⟩ := p
        have hbd := decodeHandler_bound (by omega) hd
        have hc : mimicDec h (hist1 ++ [⟨input, enc, pos + s, pos + e, r⟩]) = .ret w newpos .keep := by
          rw [mimic_last]
          simp only [hd]
        simp only [decodeCallback_ok hs hbd hc]
        exact ih _ _ _ _ _ rfl hbd

theorem stepAscii_bound : StepBound stepAscii := by
  constructor
  · intro rest r s e h
    unfold stepAscii at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (cases h; simp)
  · intro rest c n h
    unfold stepAscii at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (cases h; simp)
  · intro rest w n h
    unfold stepAscii at h
    repeat' split at h
    all_goals first
      | (cases h; done)

theorem step16_bound (le consumed : Bool) : StepBound (step16 le consumed) := by
  constructor
  · intro rest r s e h
    unfold step16 at h
    repeat' (first | (split at h) | (dsimp only at h; split at h))
    all_goals first
      | (cases h; done)
      | (cases h; simp; try omega)
  · intro rest c n h
    unfold step16 at h
    repeat' (first | (split at h) | (dsimp only at h; split at h))
    all_goals first
      | (cases h; done)
      | (cases h; simp; try omega)
  · intro rest w n h
    unfold step16 at h
    repeat' (first | (split at h) | (dsimp only at h; split at h))
    all_goals first
      | (cases h; done)

theorem step32_bound (le consumed : Bool) : StepBound (step32 le consumed) := by
  constructor
  · intro rest r s e h
    unfold step32 at h
    repeat' (first | (split at h) | (dsimp only at h; split at h))
    all_goals first
      | (cases h; done)
      | (cases h; simp; try omega)
  · intro rest c n h
    unfold step32 at h
    repeat' (first | (split at h) | (dsimp only at h; split at h))
    all_goals first
      | (cases h; done)
      | (cases h; simp; try omega)
  · intro rest w n h
    unfold step32 at h
    repeat' (first | (split at h) | (dsimp only at h; split at h))
    all_goals first
      | (cases h; done)

/-- A standard handler registered under another name gives what its own name gives, for every
UTF-16 and UTF-32 input, byte order and handler. C calls these handlers through
`unicode_decode_call_errorhandler_writer`; the `ErrHandler` that the round trips are proved over
goes straight to them, so this is what ties those theorems to the C path. -/
def WideStdIsCallback : Prop :=
  ∀ (input : Bytes) (bo : Int) (h : ErrHandler) (final : Bool) (fuel : Nat),
    (input.length : Int) ≤ ssizeMax →
    utf16DecodeX input bo (.custom (mimicDec h)) final fuel =
      utf16DecodeX input bo (.std h) final fuel ∧
    utf32DecodeX input bo (.custom (mimicDec h)) final fuel =
      utf32DecodeX input bo (.std h) final fuel ∧
    utf16DecodeX input bo (.std h) final (input.length + 1) = utf16DecodeFull input bo h final ∧
    utf32DecodeX input bo (.std h) final (input.length + 1) = utf32DecodeFull input bo h final

theorem wideStdIsCallback_proven : WideStdIsCallback := by
  intro input bo h final fuel hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [utf16DecodeX]
    generalize hb : bom16 bo input = bq
    obtain ⟨bo', q⟩ := bq
    simp only
    split
    · rfl
    · rename_i hne
      have hq : q ≤ input.length := by
        have : (input.drop q) ≠ [] := by
          intro e
          simp [e] at hne
        have := List.length_pos_iff.2 this
        rw [List.length_drop] at this
        omega
      by_cases hle : bo' ≤ 0
      · simpa [hle, codeOf] using driver_mimic (step16 true !final) (step16_bound _ _) h "utf-16-le"
          input hs fuel [] [] q _ [] rfl hq
      · simpa [hle, codeOf] using driver_mimic (step16 false !final) (step16_bound _ _) h "utf-16-be"
          input hs fuel [] [] q _ [] rfl hq
  · simp only [utf32DecodeX]
    generalize hb : bom32 bo input = bq
    obtain ⟨bo', q⟩ := bq
    simp only
    split
    · rfl
    · rename_i hne
      have hq : q ≤ input.length := by
        have : (input.drop q) ≠ [] := by
          intro e
          simp [e] at hne
        have := List.length_pos_iff.2 this
        rw [List.length_drop] at this
        omega
      by_cases hle : bo' ≤ 0
      · simpa [hle, codeOf] using driver_mimic (step32 true !final) (step32_bound _ _) h "utf-32-le"
          input hs fuel [] [] q _ [] rfl hq
      · simpa [hle, codeOf] using driver_mimic (step32 false !final) (step32_bound _ _) h "utf-32-be"
          input hs fuel [] [] q _ [] rfl hq
  · simp only [utf16DecodeX, utf16DecodeFull]
    generalize bom16 bo input = bq
    obtain ⟨bo', q⟩ := bq
    simp only
    split
    · rfl
    · exact decodeDriverX_std ..
  · simp only [utf32DecodeX, utf32DecodeFull]
    generalize bom32 bo input = bq
    obtain ⟨bo', q⟩ := bq
    simp only
    split
    · rfl
    · exact decodeDriverX_std ..

/-- A handler that writes `rep` for each bad byte and carries on. -/
def constDec (rep : Str) : DecCB := fun hist =>
  match hist.getLast? with
  | none => .bad
  | some v => .ret rep v.stop .keep

/-- `bytes.decode('ascii', handler)`: every byte under 128 stands for itself and every other byte
for one call of the handler, at its own position. The bytes above 127 are not grouped into runs,
unlike the encoder's characters. -/
def AsciiConstantHandler : Prop :=
  ∀ (input : Bytes) (rep : Str) (fuel : Nat), input.length < fuel → (input.length : Int) ≤ ssizeMax →
    asciiDecodeX input (.custom (constDec rep)) fuel =
      .ok (input.flatMap fun b => if b < 128 then [b] else rep)

theorem ascii_const_loop (input : Bytes) (rep : Str) (hs : (input.length : Int) ≤ ssizeMax) :
    ∀ (fuel : Nat) (hist : List DecView) (pos : Nat) (rest : List Nat) (out : Str),
      rest = input.drop pos → pos ≤ input.length → rest.length < fuel →
      decodeDriverX stepAscii (.custom (constDec rep)) "ascii" .unknown none fuel input hist pos rest out =
        .ok (out ++ rest.flatMap (fun b => if b < 128 then [b] else rep), input.length) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ h; omega
  | succ fuel ih =>
    intro hist pos rest out hr hp hf
    have hl : rest.length = input.length - pos := by rw [hr, List.length_drop]
    cases hrest : rest with
    | nil =>
      subst hrest
      have : pos = input.length := by simp at hl; omega
      simp [decodeDriverX, stepAscii, stopPos, this]
    | cons c cs =>
      subst hrest
      simp only [List.length_cons] at hl hf
      have hd : (c :: cs).drop 1 = cs := rfl
      have hcs : cs = input.drop (pos + 1) := by
        rw [← List.drop_drop, ← hr]
        rfl
      by_cases hc : c < 128
      · simp only [decodeDriverX, stepAscii, if_pos hc, hd]
        rw [ih _ (pos + 1) cs _ hcs (by omega) (by omega)]
        simp [hc]
      · simp only [decodeDriverX, stepAscii, if_neg hc, handlerStep]
        have hk : constDec rep (hist ++ [⟨input, "ascii", pos + 0, pos + 1, "ordinal not in range(128)"⟩]) =
            .ret rep ((pos + 1 : Nat) : Int) .keep := by
          simp [constDec]
        rw [decodeCallback_ok hs (by omega) hk]
        simp only
        rw [ih _ (pos + 1) _ _ rfl (by omega) (by rw [← hcs]; omega), ← hcs]
        simp [hc]

theorem asciiConstantHandler_proven : AsciiConstantHandler := by
  intro input rep fuel hf hs
  have := ascii_const_loop input rep hs fuel [] 0 input [] (by simp) (by omega) hf
  simp [asciiDecodeX, this, bind, Except.bind]

/-! ## Inline against callback in `unicode_encode_ucs1` -/

/-- `PyCodec_*Errors` as a callback, for an encoder. -/
def mimicEnc (h : ErrHandler) (nameOf : Nat → Option Str) : EncCB := fun hist =>
  match hist.getLast? with
  | none => .bad
  | some v =>
    match encodeHandlerCall h nameOf v.encoding .unknown v.object v.start v.stop v.reason with
    | .error e => .raises e
    | .ok (rep, newpos) => .ret rep newpos

theorem mimicEnc_last (h : ErrHandler) (nameOf : Nat → Option Str) (hist : List EncView) (v : EncView) :
    mimicEnc h nameOf (hist ++ [v]) =
      match encodeHandlerCall h nameOf v.encoding .unknown v.object v.start v.stop v.reason with
      | .error e => .raises e
      | .ok (rep, newpos) => .ret rep newpos := by
  simp [mimicEnc]

theorem encodeCallback_ok {cb : EncCB} {hist : List EncView} {enc reason : String} {input : Str}
    {start stop newpos : Nat} {rep : EncRep} (hs : (input.length : Int) ≤ ssizeMax)
    (hb : newpos ≤ input.length)
    (hc : cb (hist ++ [{ object := input, encoding := enc, start, stop, reason }]) = .ret rep newpos) :
    encodeCallback cb hist enc reason input start stop =
      .ok (hist ++ [{ object := input, encoding := enc, start, stop, reason }], rep, newpos) := by
  have hn : ((newpos : Nat) : Int) ≤ ssizeMax := by omega
  simp only [encodeCallback, hc, ssizeOfIndex_nat hn, bind, Except.bind]
  rw [if_neg (by omega), if_neg (by omega)]
  simp

theorem unencodable_take (limit : Nat) (l : List Nat) :
    l.take (unencodableRun limit l).length = unencodableRun limit l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [unencodableRun]
    split
    · simp [ih]
    · rfl

theorem unencodable_len (limit : Nat) (l : List Nat) : (unencodableRun limit l).length ≤ l.length := by
  induction l with
  | nil => simp [unencodableRun]
  | cons a t ih =>
    simp only [unencodableRun]
    split
    · simp; omega
    · simp

/-- `unicode_encode_ucs1` writes `replace`, `ignore`, `backslashreplace` and `xmlcharrefreplace`
inline. The same handlers registered under another name take the generic path, with its
position checks and its test that the replacement fits. The two give the same result, success or
failure, for every string. The characters themselves come from one definition in the model, so
this compares the control paths, not the two C routines that write them. -/
def Ucs1InlineMatchesCallback : Prop :=
  ∀ (s : Str) (limit : Nat) (nameOf : Nat → Option Str) (h : ErrHandler) (fuel : Nat),
    (limit = 128 ∨ limit = 256) →
    (h = .replace ∨ h = .ignore ∨ h = .backslashreplace ∨ h = .xmlcharrefreplace) →
    (s.length : Int) ≤ ssizeMax →
    ucs1EncodeLoopX s limit (.std h) nameOf fuel [] 0 s [] =
      ucs1EncodeLoopX s limit (.custom (mimicEnc h nameOf)) nameOf fuel [] 0 s []

theorem ucs1_inline_loop (s : Str) (limit : Nat) (nameOf : Nat → Option Str) (h : ErrHandler)
    (hl : limit = 128 ∨ limit = 256)
    (hh : h = .replace ∨ h = .ignore ∨ h = .backslashreplace ∨ h = .xmlcharrefreplace)
    (hs : (s.length : Int) ≤ ssizeMax) :
    ∀ (fuel : Nat) (hist1 hist2 : List EncView) (pos : Nat) (rest : List Nat) (out : Bytes),
      rest = s.drop pos →
      ucs1EncodeLoopX s limit (.std h) nameOf fuel hist1 pos rest out =
        ucs1EncodeLoopX s limit (.custom (mimicEnc h nameOf)) nameOf fuel hist2 pos rest out := by
  have hlim : 128 ≤ limit := by omega
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro hist1 hist2 pos rest out hr
    cases rest with
    | nil => rfl
    | cons c cs =>
      have hcs : cs = s.drop (pos + 1) := by
        rw [← List.drop_drop, ← hr]
        rfl
      by_cases hc : c < limit
      · simp only [ucs1EncodeLoopX, if_pos hc]
        exact ih _ _ _ _ _ hcs
      · simp only [ucs1EncodeLoopX, if_neg hc]
        generalize hrun : unencodableRun limit (c :: cs) = run
        have ht := unencodable_take limit (c :: cs)
        have hle := unencodable_len limit (c :: cs)
        rw [hrun] at ht hle
        have hlen : (c :: cs).length = s.length - pos := by rw [hr, List.length_drop]
        have hpos : pos + run.length ≤ s.length := by
          simp only [List.length_cons] at hlen hle
          omega
        have hdrop : (c :: cs).drop run.length = s.drop (pos + run.length) := by
          rw [hr, List.drop_drop]
        have hslice : (s.drop pos).take (pos + run.length - pos) = run := by
          rw [← hr, show pos + run.length - pos = run.length by omega, ht]
        generalize henc : (if limit == 256 then "latin-1" else "ascii") = enc
        generalize hreason : (if limit == 256 then "ordinal not in range(256)"
          else "ordinal not in range(128)") = reason
        have step : ∀ w : Str, (∀ x ∈ w, x < limit) →
            mimicEnc h nameOf (hist2 ++ [⟨s, enc, pos, pos + run.length, reason⟩]) =
              .ret (.str w) ((pos + run.length : Nat) : Int) →
            ucs1EncodeLoopX s limit (.std h) nameOf fuel hist1 (pos + run.length)
                (s.drop (pos + run.length)) (out ++ w) =
              (match encHandlerStep (.custom (mimicEnc h nameOf)) nameOf enc .unknown reason s hist2 pos
                  (pos + run.length) with
               | .error e => .error e
               | .ok (hist', rep, newpos) =>
                 match rep with
                 | .bytes b => ucs1EncodeLoopX s limit (.custom (mimicEnc h nameOf)) nameOf fuel hist' newpos
                     (s.drop newpos) (out ++ b)
                 | .str r =>
                   if r.all (· < limit) then
                     ucs1EncodeLoopX s limit (.custom (mimicEnc h nameOf)) nameOf fuel hist' newpos
                       (s.drop newpos) (out ++ r)
                   else .error (encodeError enc s pos (pos + run.length) reason)) := by
          intro w hw hm
          simp only [encHandlerStep]
          rw [encodeCallback_ok hs hpos hm]
          have hall : (w.all fun x => decide (x < limit)) = true := by
            simp only [List.all_eq_true, decide_eq_true_eq]
            exact hw
          simp only [hall, if_true]
          exact ih _ _ _ _ _ rfl
        rcases hh with rfl | rfl | rfl | rfl
        · have hw : ∀ x ∈ List.replicate run.length 63, x < limit := by
            intro x hx
            rw [List.eq_of_mem_replicate hx]
            omega
          have hm := step _ hw (by rw [mimicEnc_last]; simp only [encodeHandlerCall, hslice])
          change ucs1EncodeLoopX s limit (.std .replace) nameOf fuel hist1 (pos + run.length)
            ((c :: cs).drop run.length) (out ++ List.replicate run.length 63) = _
          rw [hdrop]
          exact hm
        · have hm := step [] (by simp) (by rw [mimicEnc_last]; simp only [encodeHandlerCall])
          change ucs1EncodeLoopX s limit (.std .ignore) nameOf fuel hist1 (pos + run.length)
            ((c :: cs).drop run.length) (out ++ []) = _
          rw [hdrop]
          exact hm
        · have hw : ∀ x ∈ run.flatMap escapeEncodeChar, x < limit := by
            intro x hx
            obtain ⟨a, -, hax⟩ := List.mem_flatMap.1 hx
            have := (replacementsAscii_proven a).1 x hax
            omega
          have hm := step _ hw (by rw [mimicEnc_last]; simp only [encodeHandlerCall, hslice])
          change ucs1EncodeLoopX s limit (.std .backslashreplace) nameOf fuel hist1 (pos + run.length)
            ((c :: cs).drop run.length) (out ++ run.flatMap escapeEncodeChar) = _
          rw [hdrop]
          exact hm
        · have hw : ∀ x ∈ run.flatMap xmlRef, x < limit := by
            intro x hx
            obtain ⟨a, -, hax⟩ := List.mem_flatMap.1 hx
            have := (replacementsAscii_proven a).2 x hax
            omega
          have hm := step _ hw (by rw [mimicEnc_last]; simp only [encodeHandlerCall, hslice])
          change ucs1EncodeLoopX s limit (.std .xmlcharrefreplace) nameOf fuel hist1 (pos + run.length)
            ((c :: cs).drop run.length) (out ++ run.flatMap xmlRef) = _
          rw [hdrop]
          exact hm

theorem ucs1InlineMatchesCallback_proven : Ucs1InlineMatchesCallback := by
  intro s limit nameOf h fuel hl hh hs
  exact ucs1_inline_loop s limit nameOf h hl hh hs fuel [] [] 0 s [] (by simp)

/-- The exception of a result, for a comparison that `decide` can make. -/
def errOf : Py Bytes → Option PyExc
  | .error e => some e
  | .ok _ => none

/-- `surrogateescape` too: inline it writes what it can and hands the rest of the run to the
callback path, while the callback alone rejects the whole run. -/
def Ucs1SurrogateEscapeMatchesCallback : Prop :=
  ∀ (s : Str) (limit : Nat) (nameOf : Nat → Option Str) (fuel : Nat),
    (limit = 128 ∨ limit = 256) → (s.length : Int) ≤ ssizeMax →
    ucs1EncodeLoopX s limit (.std .surrogateescape) nameOf fuel [] 0 s [] =
      ucs1EncodeLoopX s limit (.custom (mimicEnc .surrogateescape nameOf)) nameOf fuel [] 0 s []

/-- `'\udcff\udfff'.encode('ascii', 'surrogateescape')` reports position 1, and the same handler
under another name reports positions 0-1. -/
theorem ucs1SurrogateEscapeMatchesCallback_refuted : ¬ Ucs1SurrogateEscapeMatchesCallback := by
  intro h
  have e := h [0xdcff, 0xdfff] 128 (fun _ => none) 3 (Or.inl rfl) (by unfold ssizeMax; decide)
  have d := congrArg errOf e
  revert d
  decide +kernel

end PyLean.UnicodeObj
