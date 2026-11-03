import PyLean.TextLibs.PlistWriteOk

/-! The writer's refusals, value by value, and `dump`'s format check. -/

namespace PyLean.TextLibs.Plist

open PyLean PyLean.TextLibs

theorem utf16_surrogate (nameOf : Nat → Option UnicodeObj.Str) (input : UnicodeObj.Str) :
    ∀ (cs : List Nat) fuel pos out, cs.length < fuel → (∃ c ∈ cs, UnicodeObj.isSurrogate c = true) →
      ∃ e, UnicodeObj.encodeWideLoop (UnicodeObj.utf16Char false) 2 .strict nameOf "utf-16-be" .utf16be input
        fuel pos cs out = .error e ∧ isInst e "UnicodeEncodeError" = true
  | [], _, _, _, _, h => by simp at h
  | c :: cs, fuel, pos, out, hf, h => by
    obtain ⟨f, rfl⟩ : ∃ j, fuel = j + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    by_cases hc : UnicodeObj.isSurrogate c = true
    · refine ⟨UnicodeObj.encodeError "utf-16-be" input pos (pos + 1) "surrogates not allowed",
        by simp [UnicodeObj.encodeWideLoop, hc, UnicodeObj.encodeHandlerCall], ?_⟩
      simp only [UnicodeObj.encodeError]; split <;> rfl
    · simp only [UnicodeObj.encodeWideLoop, hc, Bool.not_false, ↓reduceIte]
      exact utf16_surrogate nameOf input cs f _ _ (by simp at hf; omega)
        (by obtain ⟨x, hx, hs⟩ := h; simp at hx; rcases hx with rfl | hx
            · exact absurd hs hc
            · exact ⟨x, hx, hs⟩)

/-- The documented and the other refusals of `dumps(fmt=FMT_BINARY)`, for a value `w` alone:
`OverflowError(value)` for an int outside -2**63..2**64-1 (:788-791, :803), `ValueError('UIDs must
be positive')` and `OverflowError(value)` for a UID's data (:832-833, :843), `TypeError(value)` for an
unsupported type (:869), `UnicodeEncodeError` for a `str` with a lone surrogate (:826),
`TypeError` for an aware datetime without `aware_datetime` (:814) and `OverflowError` when its UTC
time leaves the datetime range (:810); and `dump`'s `ValueError('Unsupported format: %r')`
(:934-935) for any value. -/
def WriteErrors : Prop :=
  ∀ (xmlw : XmlWrite) (cfg : WCfg) (k : Nat),
    (∀ v : Int, (v < -2 ^ 63 ∨ 2 ^ 64 ≤ v) →
      dumpsR xmlw (k + 8) [.int v] 0 .binary cfg = .error (.overflowError (toString v))) ∧
    (∀ d : Int, d < 0 →
      dumpsR xmlw (k + 8) [.uid d] 0 .binary cfg = .error (.valueError "UIDs must be positive")) ∧
    (∀ d : Int, 2 ^ 64 ≤ d →
      dumpsR xmlw (k + 8) [.uid d] 0 .binary cfg = .error (.overflowError s!"UID({d})")) ∧
    (∀ s ty, dumpsR xmlw (k + 8) [.other s ty] 0 .binary cfg = .error (.typeError s)) ∧
    (∀ s : List Nat, (∃ c ∈ s, UnicodeObj.isSurrogate c = true) →
      ∃ e, dumpsR xmlw (k + 8) [.str s] 0 .binary cfg = .error e ∧ isInst e "UnicodeEncodeError" = true) ∧
    (∀ us o, cfg.awareDatetime = false → dumpsR xmlw (k + 8) [.date us (some o)] 0 .binary cfg =
      .error (.typeError "can't subtract offset-naive and offset-aware datetimes")) ∧
    (∀ us o, cfg.awareDatetime = true → o ≠ 0 → (us - o < dtMinUs ∨ us - o > dtMaxUs) →
      dumpsR xmlw (k + 8) [.date us (some o)] 0 .binary cfg = .error (.overflowError "date value out of range")) ∧
    (∀ H root, dumpsR xmlw (k + 2) H root .none cfg = .error (.valueError "Unsupported format: None")) ∧
    (∀ H root rp, dumpsR xmlw (k + 2) H root (.other rp) cfg =
      .error (.valueError s!"Unsupported format: {rp}"))

theorem writeErrors_proven : WriteErrors := by
  intro xmlw cfg k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have h0 : ∀ h : -2 ^ 63 ≤ v, v < 2 ^ 64 → False := fun h1 h2 => by omega
    simp [dumpsR, dumpR, binaryWriteR, flattenR, WState.init, tableLookup, idLookup, scalarType,
      call, countToSizeR, countToSize, writeAll, writeObjectR, getrefnumR, scalarMatch, writeInt,
      bind, Except.bind]
    rcases hv with hv | hv
    · rw [if_pos (by omega), if_neg (by omega)]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
  · intro d hd
    simp [dumpsR, dumpR, binaryWriteR, flattenR, WState.init, tableLookup, idLookup, scalarType, objId,
      call, countToSizeR, countToSize, writeAll, writeObjectR, getrefnumR, bind, Except.bind, hd]
  · intro d hd
    have h1 : ¬ d < 0 := by omega
    simp [dumpsR, dumpR, binaryWriteR, flattenR, WState.init, tableLookup, idLookup, scalarType, objId,
      call, countToSizeR, countToSize, writeAll, writeObjectR, getrefnumR, bind, Except.bind, h1]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · intro s ty
    simp [dumpsR, dumpR, binaryWriteR, flattenR, WState.init, tableLookup, idLookup, scalarType, objId,
      call, countToSizeR, countToSize, writeAll, writeObjectR, getrefnumR, bind, Except.bind]
  · intro s hs
    have hu := utf16_surrogate (fun _ => none) s s (s.length + 1) 0 [] (by omega) hs
    obtain ⟨e, he, hc⟩ := hu
    have ha := ascii_encode_spec s
    cases hae : UnicodeObj.ucs1Encode s 128 .strict (fun _ => none) with
    | ok t =>
      rw [hae] at ha
      obtain ⟨c, hcs, hsc⟩ := hs
      have := ha.2 c hcs
      simp [UnicodeObj.isSurrogate] at hsc; omega
    | error e' =>
      rw [hae] at ha
      refine ⟨e, ?_, hc⟩
      simp [dumpsR, dumpR, binaryWriteR, flattenR, WState.init, tableLookup, idLookup, scalarType,
        call, countToSizeR, countToSize, writeAll, writeObjectR, getrefnumR, scalarMatch, bind,
        Except.bind, hae, ha, UnicodeObj.utf16EncodeFull, he]
  · intro us o ha
    simp [dumpsR, dumpR, binaryWriteR, flattenR, WState.init, tableLookup, idLookup, scalarType,
      call, countToSizeR, countToSize, writeAll, writeObjectR, getrefnumR, scalarMatch, bind,
      Except.bind, dateSeconds, ha]
  · intro us o ha ho hr
    have hr' : us - o < dtMinUs ∨ us - o > dtMaxUs := hr
    simp [dumpsR, dumpR, binaryWriteR, flattenR, WState.init, tableLookup, idLookup, scalarType,
      call, countToSizeR, countToSize, writeAll, writeObjectR, getrefnumR, scalarMatch, bind,
      Except.bind, dateSeconds, ha, ho, hr']
  · intro H root; simp [dumpsR, dumpR, call, bind, Except.bind]
  · intro H root rp; simp [dumpsR, dumpR, call, bind, Except.bind]

end PyLean.TextLibs.Plist
