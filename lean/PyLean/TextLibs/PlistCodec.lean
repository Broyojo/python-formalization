import PyLean.TextLibs.PlistBytes

/-! The `str` codecs the binary writer and reader use, with the strict handler: `ascii`
encoding succeeds exactly on ASCII text and returns it, otherwise raises `UnicodeEncodeError`;
`utf-16-be` encoding succeeds only without surrogates, in whole code units; `ascii` decoding of
ASCII bytes returns them. -/

namespace PyLean.TextLibs.Plist

open PyLean PyLean.TextLibs PyLean.UnicodeObj

theorem ucs1Loop_ascii (input : Str) (nameOf : Nat → Option Str) :
    ∀ (cs : List Nat) fuel pos out, cs.length < fuel → (∀ c ∈ cs, c < 128) →
      ucs1EncodeLoop input 128 .strict nameOf fuel pos cs out = .ok (out ++ cs)
  | [], fuel, _, out, hf, _ => by
    obtain ⟨f, rfl⟩ : ∃ j, fuel = j + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simp [ucs1EncodeLoop]
  | c :: cs, fuel, pos, out, hf, h => by
    obtain ⟨f, rfl⟩ : ∃ j, fuel = j + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simp only [ucs1EncodeLoop, if_pos (h c (by simp))]
    rw [ucs1Loop_ascii input nameOf cs f (pos + 1) (out ++ [c]) (by simp at hf; omega)
      (fun x hx => h x (by simp [hx]))]
    simp

theorem ucs1Loop_strict (input : Str) (nameOf : Nat → Option Str) :
    ∀ (cs : List Nat) fuel pos out, cs.length < fuel →
      match ucs1EncodeLoop input 128 .strict nameOf fuel pos cs out with
      | .ok t => t = out ++ cs ∧ ∀ c ∈ cs, c < 128
      | .error e => isInst e "UnicodeEncodeError" = true
  | [], fuel, _, out, hf => by
    obtain ⟨f, rfl⟩ : ∃ j, fuel = j + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simp [ucs1EncodeLoop]
  | c :: cs, fuel, pos, out, hf => by
    obtain ⟨f, rfl⟩ : ∃ j, fuel = j + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    by_cases hc : c < 128
    · simp only [ucs1EncodeLoop, if_pos hc]
      have ih := ucs1Loop_strict input nameOf cs f (pos + 1) (out ++ [c]) (by simp at hf; omega)
      revert ih
      cases ucs1EncodeLoop input 128 .strict nameOf f (pos + 1) cs (out ++ [c]) with
      | error e => exact id
      | ok t =>
        intro ⟨h1, h2⟩
        refine ⟨by simp [h1], ?_⟩
        intro x hx
        simp at hx
        rcases hx with rfl | hx
        · exact hc
        · exact h2 x hx
    · simp only [ucs1EncodeLoop, if_neg hc]
      simp only [encodeError]
      split <;> rfl

theorem ascii_encode_spec (s : Str) :
    match ucs1Encode s 128 .strict (fun _ => none) with
    | .ok t => t = s ∧ ∀ c ∈ s, c < 128
    | .error e => isInst e "UnicodeEncodeError" = true := by
  have h := ucs1Loop_strict s (fun _ => none) s (s.length + 1) 0 [] (by omega)
  unfold ucs1Encode
  revert h
  cases ucs1EncodeLoop s 128 .strict (fun _ => none) (s.length + 1) 0 s [] with
  | error e => exact id
  | ok t => intro ⟨h1, h2⟩; exact ⟨by simpa using h1, h2⟩

theorem ascii_decode_ascii (input : List Nat) :
    ∀ (rest : List Nat) fuel pos out, rest.length < fuel → (∀ c ∈ rest, c < 128) →
      decodeDriver stepAscii .strict "ascii" .unknown input fuel pos rest out = .ok (out ++ rest, pos + rest.length)
  | [], fuel, pos, out, hf, _ => by
    obtain ⟨f, rfl⟩ : ∃ j, fuel = j + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simp [decodeDriver, stepAscii]
  | c :: cs, fuel, pos, out, hf, h => by
    obtain ⟨f, rfl⟩ : ∃ j, fuel = j + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simp only [decodeDriver, stepAscii, if_pos (h c (by simp)), List.drop_succ_cons, List.drop_zero]
    rw [ascii_decode_ascii input cs f (pos + 1) (out ++ [c]) (by simp at hf; omega)
      (fun x hx => h x (by simp [hx]))]
    simp [Nat.add_assoc, Nat.add_comm 1]

theorem asciiDecode_ascii (s : List Nat) (h : ∀ c ∈ s, c < 128) : asciiDecode s .strict = .ok s := by
  unfold asciiDecode
  rw [ascii_decode_ascii s s (s.length + 1) 0 [] (by omega) h]
  rfl

theorem encodeWide_strict_noSurr (charBytes : Nat → List Nat) (u : Nat) (nameOf : Nat → Option Str)
    (e : String) (code : EncCode) (input : Str) :
    ∀ (cs : List Nat) fuel pos out t, encodeWideLoop charBytes u .strict nameOf e code input fuel pos cs out = .ok t →
      ∀ c ∈ cs, isSurrogate c = false
  | [], _, _, _, _, _ => by simp
  | c :: cs, fuel, pos, out, t, h => by
    obtain ⟨f, rfl⟩ : ∃ j, fuel = j + 1 := by
      cases fuel with
      | zero => simp [encodeWideLoop] at h
      | succ j => exact ⟨j, rfl⟩
    by_cases hc : isSurrogate c = true
    · simp [encodeWideLoop, hc, encodeHandlerCall] at h
    · simp only [encodeWideLoop, hc, Bool.not_false, ↓reduceIte] at h
      intro x hx
      simp at hx
      rcases hx with rfl | hx
      · simpa using hc
      · exact encodeWide_strict_noSurr charBytes u nameOf e code input cs f _ _ t h x hx

theorem utf16Char_even (c : Nat) : (utf16Char false c).length % 2 = 0 := by
  simp only [utf16Char, unitBytes]
  split <;> simp

theorem flatMap_even (s : Str) : (s.flatMap (utf16Char false)).length % 2 = 0 := by
  induction s with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append]
    have := utf16Char_even c
    omega

/-- A successful strict `utf-16-be` encoding: no surrogate in the text, the bytes are a whole
number of code units, and decoding gives the text back. -/
theorem utf16be_spec (s : Str) (hv : Str.Valid s) (t : List Nat)
    (h : utf16EncodeFull s 1 .strict (fun _ => none) = .ok t) :
    t.length % 2 = 0 ∧ utf16DecodeFull t 1 .strict true = .ok (s, t.length) := by
  have hns : ∀ c ∈ s, isSurrogate c = false := by
    unfold utf16EncodeFull at h
    exact encodeWide_strict_noSurr _ _ _ _ _ s s _ _ _ t h
  obtain ⟨b, hb1, hb2⟩ := utf16RoundTrip_proven s 1 (fun _ => none) ⟨hv, hns⟩ (by simp)
  rw [hb1] at h
  cases h
  refine ⟨?_, hb2⟩
  unfold utf16EncodeFull at hb1
  rw [encodeWide_plain _ _ _ _ _ _ s s hns _ _ _ (by omega)] at hb1
  have hbe : t = s.flatMap (utf16Char false) := by
    have := Except.ok.inj hb1
    simpa using this.symm
  rw [hbe]
  exact flatMap_even s

end PyLean.TextLibs.Plist
