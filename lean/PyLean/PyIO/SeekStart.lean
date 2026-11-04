import PyLean.PyIO.StringPy

/-!
`_pyio.TextIOWrapper.seek` to the start and to the end (`Lib/_pyio.py:2522-2595`), over the
`_pyio.StringIO` model.
-/

namespace PyLean.PyIO

open PyLean

theorem dec_reset_reset (d : Dec) : d.reset.reset = d.reset := by
  unfold Dec.reset; split <;> simp_all

/-- `seek(0)` then `read()` returns `getvalue()` on every open `_pyio.StringIO` state, and
`seek(0)` returns 0: the cookie-0 branch (_pyio.py:2562-2576) rewinds the `BytesIO`, drops
the decoded characters and the snapshot and resets the decoder, so `read()` decodes the
whole buffer from a clean decoder, as `getvalue()` does. `seek(0, 2)` returns the length of
the buffer and the following `read()` returns `''` (:2547-2557). `seek` refuses a closed
stream with `ValueError('tell on closed file')` (:2536-2537), a nonzero offset with
`whence` 1 or 2 with `UnsupportedOperation` (:2541-2542, :2548-2549), another `whence` with
`ValueError('unsupported whence (w)')` (:2558-2559), and a negative cookie with
`ValueError('negative seek position c')` (:2560-2561), each changing nothing. -/
def StringIOSeekStartEnd : Prop := ∀ (t : TState),
  (t.b.closed = true → ∀ c w, TP.seek t c w = (t, .error (.valueError "tell on closed file"))) ∧
  (t.b.closed = false →
    (TP.seek t 0 0).2 = .ok (.int 0) ∧
    (TP.step (TP.seek t 0 0).1 (.read none)).2 = (TP.getvalue t).2 ∧
    (TP.seek t 0 2).2 = .ok (.int t.b.buf.length) ∧
    (TP.step (TP.seek t 0 2).1 (.read none)).2 = .ok (.str []) ∧
    (∀ c, c ≠ 0 → TP.seek t c 1 = (t, .error (unsupportedOp "can't do nonzero cur-relative seeks")) ∧
      TP.seek t c 2 = (t, .error (unsupportedOp "can't do nonzero end-relative seeks"))) ∧
    (∀ c w, w ≠ 0 → w ≠ 1 → w ≠ 2 → TP.seek t c w = (t, .error (.valueError s!"unsupported whence ({w})"))) ∧
    (∀ c, c < 0 → TP.seek t c 0 = (t, .error (.valueError s!"negative seek position {c}"))))

theorem reset_decode_nil (d : Dec) : ∃ d', d.reset.decode [] true = .ok (d', []) := by
  unfold Dec.reset
  cases hn : d.nl <;>
    simp [Dec.decode, utf8Dec, utf8DecF, bind, Except.bind, pure, Except.pure, hn, translateNl, nlKinds]

/-- The state `seek(0)` leaves. -/
def seek0St (t : TState) : TState :=
  { t with b := { t.b with pos := 0 }, telling := true, decoded := [], used := 0, snapshot := none,
           decoder := t.decoder.map Dec.reset }

/-- The state `seek(0, 2)` leaves. -/
def seekEndSt (t : TState) : TState :=
  { t with b := { t.b with pos := t.b.buf.length }, telling := true, decoded := [], used := 0,
           snapshot := none, decoder := t.decoder.map Dec.reset }

theorem stringIOSeekStartEnd_proven : StringIOSeekStartEnd := by
  intro t
  refine ⟨?_, ?_⟩
  · intro hc c w; simp [TP.seek, hc]
  · intro hc
    have hseek0 : TP.seek t 0 0 = (seek0St t, .ok (.int 0)) := by
      cases hd : t.decoder <;>
        simp [TP.seek, TP.seekCookie, TP.flush, hc, TP.unpack, hd, TP.setDecoded, P.seek, seek0St]
    refine ⟨by rw [hseek0], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hseek0]
      cases hd : t.decoder with
      | none =>
        simp only [Option.map_none]
        simp [TP.step, TP.read, TP.getvalue, TP.flush, hc, hd, TP.getDecoder, seek0St,
          P.readRaw, TP.getDecodedChars]
        have hr : Dec.reset ⟨[], t.readuniversal, t.readtranslate, false, Dec.none0⟩ =
            ⟨[], t.readuniversal, t.readtranslate, false, Dec.none0⟩ := by
          unfold Dec.reset; split <;> rfl
        rw [hr]
        by_cases hb : t.b.buf = []
        · simp only [hb, ite_true]
          cases Dec.decode _ [] true <;> rfl
        · simp only [hb, ite_false, slice, List.drop_zero, List.take_length]
          cases Dec.decode _ t.b.buf true <;> rfl
      | some d =>
        simp [TP.step, TP.read, TP.getvalue, TP.flush, hc, hd, TP.getDecoder, seek0St,
          P.readRaw, TP.getDecodedChars]
        by_cases hb : t.b.buf = []
        · simp only [hb, ite_true]
          cases Dec.decode _ [] true <;> rfl
        · simp only [hb, ite_false, slice, List.drop_zero, List.take_length]
          cases Dec.decode _ t.b.buf true <;> rfl
    · simp [TP.seek, TP.flush, hc, P.seek]
    · have hs2 : TP.seek t 0 2 = (seekEndSt t, .ok (.int t.b.buf.length)) := by
        simp [TP.seek, TP.flush, hc, P.seek, TP.setDecoded, seekEndSt]
      rw [hs2]
      cases hd : t.decoder with
      | none =>
        simp [TP.step, TP.read, hc, TP.getDecoder, P.readRaw, TP.getDecodedChars, Dec.decode, utf8Dec,
          utf8DecF, bind, Except.bind, pure, Except.pure, hd, seekEndSt]
        cases t.readuniversal <;> cases t.readtranslate <;> simp [translateNl, nlKinds]
      | some d =>
        simp [TP.step, TP.read, hc, TP.getDecoder, P.readRaw, TP.getDecodedChars, hd, seekEndSt]
        obtain ⟨d', h⟩ := reset_decode_nil d
        simp [h]
    · intro c hcz
      constructor <;> simp [TP.seek, hc, hcz]
    · intro c w h0 h1 h2; simp [TP.seek, hc, h0, h1, h2]
    · intro c hneg
      have : c ≠ 1 := by omega
      simp [TP.seek, hc, hneg]

end PyLean.PyIO
