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

theorem keptItems_nonstr (H : WHeap) : ∀ items : List (Nat × Nat), (∃ q ∈ items, keyStr H q.1 = none) →
    keptItems H false items = .error (.typeError "keys must be strings")
  | [], h => by simp at h
  | (k, v) :: rest, h => by
    simp only [keptItems]
    by_cases hk : keyStr H k = none
    · simp [hk]
    · have hn : (keyStr H k).isNone = false := by cases h' : keyStr H k <;> simp_all
      rw [if_neg (by simp [hn])]
      obtain ⟨q, hq, hq'⟩ := h
      simp at hq
      rcases hq with rfl | hq
      · exact absurd hq' hk
      · rw [keptItems_nonstr H rest ⟨q, hq, hq'⟩]; rfl

theorem dumps_dict_nonstr (xmlw : XmlWrite) (cfg : WCfg) (k : Nat) (H : WHeap) (items : List (Nat × Nat))
    (hd : H.getD 0 .none = .dict items) (hs : cfg.skipkeys = false) (hq : ∃ q ∈ items, keyStr H q.1 = none) :
    dumpsR xmlw (k + 8) H 0 .binary cfg = .error (.typeError "keys must be strings") := by
  have hdi : (dictItems H cfg items >>= keptItems H cfg.skipkeys) = .error (.typeError "keys must be strings") := by
    unfold dictItems
    rw [hs]
    by_cases hsk : cfg.sortKeys = true
    · have hany : items.any (fun (k, _) => (keyStr H k).isNone) = true := by
        obtain ⟨q, hq1, hq2⟩ := hq
        exact List.any_eq_true.mpr ⟨q, hq1, by rcases q with ⟨a, b⟩; simp [hq2]⟩
      simp [hsk, hany, bind, Except.bind]
    · simp [hsk, bind, Except.bind, keptItems_nonstr H items hq]
  have hflat : flattenR H cfg (k + 5) 0 WState.init = .error (.typeError "keys must be strings") := by
    simp only [flattenR, WState.init, tableLookup, idLookup, List.find?_nil, Option.map_none,
      Option.isSome_none, hd]
    simp only [scalarType, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    simp only [dictItemsR, call, bind, Except.bind] at hdi ⊢
    revert hdi
    cases dictItems H cfg items with
    | error e => intro h; simpa using h
    | ok its =>
      intro h
      simp only at h ⊢
      rw [h]
  simp [dumpsR, dumpR, binaryWriteR, call, bind, Except.bind, hflat]

/-- The documented and the other refusals of `dumps(fmt=FMT_BINARY)`, for a value `w` alone:
`OverflowError(value)` for an int outside -2**63..2**64-1 (:788-791, :803), `ValueError('UIDs must
be positive')` and `OverflowError(value)` for a UID's data (:832-833, :843), `TypeError(value)` for an
unsupported type (:869), `UnicodeEncodeError` for a `str` with a lone surrogate (:826),
`TypeError` for an aware datetime without `aware_datetime` (:814) and `OverflowError` when its UTC
time leaves the datetime range (:810); and `dump`'s `ValueError('Unsupported format: %r')`
(:934-935) for any value and any hashable `fmt` not equal to a format. Scope limit: `.other` is a hashable object that is not equal to `FMT_XML` or `FMT_BINARY`; `_FORMATS` finds a key by hash and equality, so an object whose own `__hash__`/`__eq__` makes it equal to a format would select that format, and is not represented. -/
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
      .error (.valueError s!"Unsupported format: {rp}")) ∧
    (∀ H root ty e, dumpsR xmlw (k + 2) H root (.badHash ty e) cfg =
      .error (if e.className = "TypeError" then
        .typeError s!"cannot use '{ty}' as a frozendict key ({e.message})" else e)) ∧
    (∀ (H : WHeap) items, H.getD 0 .none = .dict items → cfg.skipkeys = false →
      (∃ q ∈ items, keyStr H q.1 = none) →
      dumpsR xmlw (k + 8) H 0 .binary cfg = .error (.typeError "keys must be strings")) ∧
    (∀ us o, cfg.awareDatetime = true → (o = 0 ∨ (dtMinUs ≤ us - o ∧ us - o ≤ dtMaxUs)) →
      dumpsR xmlw (k + 8) [.date us (some o)] 0 .binary cfg =
      .ok (asciiBytes "bplist00" ++ 0x33 :: beBytes (Binary64.F64.ofRat (mkRat (us - o) 1000000)).bits 8 ++
        [8, 0, 0, 0, 0, 0, 0, 1, 1] ++ beBytes 1 8 ++ beBytes 0 8 ++ beBytes 17 8)) ∧
    (∀ (H : WHeap) root, dumpsR xmlw (k + 3) H root .xml cfg = xmlw (k + 1) H cfg root) ∧
    (∀ us, cfg.awareDatetime = false → dumpsR xmlw (k + 8) [.date us none] 0 .binary cfg =
      .ok (asciiBytes "bplist00" ++ 0x33 :: beBytes (Binary64.F64.ofRat (mkRat us 1000000)).bits 8 ++
        [8, 0, 0, 0, 0, 0, 0, 1, 1] ++ beBytes 1 8 ++ beBytes 0 8 ++ beBytes 17 8))

theorem writeErrors_proven : WriteErrors := by
  intro xmlw cfg k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro H root ty e; simp [dumpsR, dumpR, call, bind, Except.bind, frozendictKeyErr]
  · intro H items hd hs hq
    exact dumps_dict_nonstr xmlw cfg k H items hd hs hq
  · intro us o ha ho
    have hd : dateSeconds cfg us (some o) = .ok (Binary64.F64.ofRat (mkRat (us - o) 1000000)).bits := by
      by_cases h0 : o = 0
      · subst h0; simp [dateSeconds, ha, pure, Except.pure, bind, Except.bind]
      · have hr : ¬ (us - o < dtMinUs ∨ us - o > dtMaxUs) := by omega
        simp [dateSeconds, ha, h0, hr, pure, Except.pure, bind, Except.bind]
    simp [dumpsR, dumpR, binaryWriteR, flattenR, WState.init, tableLookup, idLookup, scalarType,
      call, countToSizeR, countToSize, writeAll, writeObjectR, getrefnumR, scalarMatch, bind,
      Except.bind, hd, pure, Except.pure, beBytes_length, packRefs, beBytes, asciiBytes, bplistHeader]
  · intro H root
    simp [dumpsR, dumpR, call, bind, Except.bind]
  · intro us ha
    simp [dumpsR, dumpR, binaryWriteR, flattenR, WState.init, tableLookup, idLookup, scalarType,
      call, countToSizeR, countToSize, writeAll, writeObjectR, getrefnumR, scalarMatch, bind,
      Except.bind, dateSeconds, ha, pure, Except.pure, beBytes_length, packRefs, beBytes, asciiBytes, bplistHeader]

end PyLean.TextLibs.Plist
