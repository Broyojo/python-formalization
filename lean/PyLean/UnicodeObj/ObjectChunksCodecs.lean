import PyLean.UnicodeObj.ObjectChunks

/-!
The chunk property for the decoders built on `decodeDriver`: `raw_unicode_escape`, UTF-16, UTF-32 and
`unicode_escape`. In `unicode_escape` it is false at an octal escape, which is
`unicodeEscapeChunks_refuted`, and true everywhere else.
-/

namespace PyLean.UnicodeObj

open PyLean

theorem agree_le {d d' : DStep} {L L' : Nat} (h : Agree d d' L) (hl : L ≤ L') : Agree d d' L' := by
  cases d with
  | char c n => exact ⟨h.1, Nat.le_trans h.2 hl⟩
  | multi w n => exact ⟨h.1, Nat.le_trans h.2 hl⟩
  | fail why s e => exact ⟨h.1, Nat.le_trans h.2 hl⟩
  | stop => trivial
  | raise e => exact h

/-! ## Hex digits -/

theorem hex_ok : ∀ (count : Nat) (r t : List Nat) (n acc ch : Nat),
    hexEscape count r n acc = .ok ch →
    hexEscape count (r ++ t) n acc = .ok ch ∧ count ≤ r.length := by
  intro count
  induction count with
  | zero =>
    intro r t n acc ch h
    simp only [hexEscape] at h ⊢
    exact ⟨h, Nat.zero_le _⟩
  | succ count ih =>
    intro r t n acc ch h
    cases r with
    | nil => simp [hexEscape] at h
    | cons c cs =>
      simp only [hexEscape] at h
      cases hv : hexValue c with
      | none =>
        rw [hv] at h
        cases h
      | some v =>
        rw [hv] at h
        obtain ⟨h1, h2⟩ := ih cs t (n + 1) (acc * 16 + v) ch h
        simp only [List.cons_append, hexEscape, hv, List.length_cons]
        exact ⟨h1, by omega⟩

theorem hex_bad : ∀ (count : Nat) (r t : List Nat) (n acc m : Nat),
    hexEscape count r n acc = .error (m, false) →
    hexEscape count (r ++ t) n acc = .error (m, false) ∧ m < n + r.length := by
  intro count
  induction count with
  | zero =>
    intro r t n acc m h
    simp [hexEscape] at h
  | succ count ih =>
    intro r t n acc m h
    cases r with
    | nil => simp [hexEscape] at h
    | cons c cs =>
      simp only [hexEscape] at h
      cases hv : hexValue c with
      | none =>
        rw [hv] at h
        simp only [Except.error.injEq, Prod.mk.injEq, and_true] at h
        simp only [List.cons_append, hexEscape, hv, List.length_cons]
        exact ⟨by rw [h], by omega⟩
      | some v =>
        rw [hv] at h
        obtain ⟨h1, h2⟩ := ih cs t (n + 1) (acc * 16 + v) m h
        simp only [List.cons_append, hexEscape, hv, List.length_cons]
        exact ⟨h1, by omega⟩

theorem stepHex_agree (count : Nat) (msg : String) (r t : List Nat) :
    Agree (stepHex true count msg r) (stepHex false count msg (r ++ t)) (2 + r.length) := by
  unfold stepHex
  cases h : hexEscape count r 0 0 with
  | ok ch =>
    obtain ⟨h1, h2⟩ := hex_ok count r t 0 0 ch h
    rw [h1]
    exact agree_ite (fun _ => ⟨rfl, by omega⟩) (fun _ => ⟨rfl, by omega⟩)
  | error p =>
    obtain ⟨n, b⟩ := p
    cases b
    · obtain ⟨h1, h2⟩ := hex_bad count r t 0 0 n h
      rw [h1]
      exact ⟨rfl, by omega⟩
    · simp [Agree]

theorem rawHex_agree (count : Nat) (msg : String) (r t : List Nat) :
    Agree (rawHex true count msg r) (rawHex false count msg (r ++ t)) (2 + r.length) := by
  unfold rawHex
  cases h : hexEscape count r 0 0 with
  | ok ch =>
    obtain ⟨h1, h2⟩ := hex_ok count r t 0 0 ch h
    rw [h1]
    exact agree_ite (fun _ => ⟨rfl, by omega⟩) (fun _ => ⟨rfl, by omega⟩)
  | error p =>
    obtain ⟨n, b⟩ := p
    cases b
    · obtain ⟨h1, h2⟩ := hex_bad count r t 0 0 n h
      rw [h1]
      exact ⟨rfl, by omega⟩
    · simp [Agree]

theorem stepHex_ok (c : Bool) (count : Nat) (msg : String) (r : List Nat) :
    okStep (stepHex c count msg r) := by
  unfold stepHex
  cases hexEscape count r 0 0 with
  | ok ch =>
    exact okStep_ite (show 0 < 2 + count by omega) (show 0 < 2 + count by omega)
  | error p =>
    obtain ⟨n, b⟩ := p
    cases b
    · show 0 < 2 + n
      omega
    · exact okStep_ite trivial (show 0 < 2 + n by omega)

theorem rawHex_ok (c : Bool) (count : Nat) (msg : String) (r : List Nat) :
    okStep (rawHex c count msg r) := by
  unfold rawHex
  cases hexEscape count r 0 0 with
  | ok ch =>
    exact okStep_ite (show 0 < 2 + count by omega) (show 0 < 2 + count by omega)
  | error p =>
    obtain ⟨n, b⟩ := p
    cases b
    · show 0 < 2 + n
      omega
    · exact okStep_ite trivial (show 0 < 2 + n by omega)

/-! ## `raw_unicode_escape` -/

theorem raw_moves (c : Bool) : Moves (stepRawEscape c) := by
  refine ⟨rfl, ?_⟩
  intro r
  cases r with
  | nil => trivial
  | cons x r =>
    simp only [stepRawEscape]
    refine okStep_ite (show 0 < 1 by omega) ?_
    cases r with
    | nil => exact okStep_ite trivial (show 0 < 1 by omega)
    | cons e r =>
      refine okStep_ite (rawHex_ok ..) (okStep_ite (rawHex_ok ..) (show 0 < 2 by omega))

theorem raw_agree (r t : List Nat) :
    Agree (stepRawEscape true r) (stepRawEscape false (r ++ t)) r.length := by
  cases r with
  | nil => trivial
  | cons x r =>
    simp only [stepRawEscape, List.cons_append]
    refine agree_ite (fun _ => ⟨rfl, by simp⟩) (fun _ => ?_)
    cases r with
    | nil => simp [Agree]
    | cons e r =>
      simp only [List.cons_append]
      refine agree_ite (fun _ => agree_le (rawHex_agree ..) (by simp; omega))
        (fun _ => agree_ite (fun _ => agree_le (rawHex_agree ..) (by simp; omega))
          (fun _ => ⟨rfl, by simp⟩))

theorem raw_is_driver (h : ErrHandler) (b : Bytes) (final : Bool) :
    rawEscapeDecode b h final =
      decodeDriver (stepRawEscape !final) h "rawunicodeescape" .unknown b (b.length + 1) 0 b [] := by
  unfold rawEscapeDecode
  split
  · next he =>
    have : b = [] := List.isEmpty_iff.1 he
    subst this
    rfl
  · rfl

/-- `raw_unicode_escape` in two chunks, wherever the input is cut, for every handler. -/
def RawEscapeChunks : Prop :=
  ∀ (b : Bytes) (k : Nat) (h : ErrHandler), Chunked (fun x final => rawEscapeDecode x h final) b k

theorem rawEscapeChunks_proven : RawEscapeChunks := by
  intro b k h
  refine chunked_driver (raw_moves true) (raw_moves false) h "rawunicodeescape" .unknown b k
    (fun i => raw_agree _ _) ?_ _ (fun x => raw_is_driver h x false) (fun x => raw_is_driver h x true)
  intro i why s e hs
  have hag := raw_agree ((b.take k).drop i) (b.drop k)
  rw [hs] at hag
  have hok := (raw_moves true).ok ((b.take k).drop i)
  rw [hs] at hok
  have hle := hag.2
  have hne : (b.take k).drop i ≠ [] := by
    intro he
    rw [he] at hs
    cases hs
  have hl := List.length_pos_iff.2 hne
  simp only [List.length_drop] at hle hl
  simp only [okStep] at hok
  exact handler_loc h _ _ _ _ _ _ _ (by omega) (by omega) (fun _ => .inl rfl)

/-! ## UTF-16 and UTF-32 -/

theorem step16_moves (le c : Bool) : Moves (step16 le c) := by
  refine ⟨rfl, ?_⟩
  intro r
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨x, _ | ⟨y, r⟩⟩⟩⟩
  · trivial
  · exact okStep_ite trivial (show 0 < 1 by omega)
  · simp only [step16]
    refine okStep_ite (show 0 < 2 by omega) (okStep_ite (show 0 < 2 by omega) ?_)
    exact okStep_ite trivial (show 0 < 2 + 0 by omega)
  · simp only [step16]
    refine okStep_ite (show 0 < 2 by omega) (okStep_ite (show 0 < 2 by omega) ?_)
    exact okStep_ite trivial (show 0 < 2 + 1 by omega)
  · simp only [step16]
    refine okStep_ite (show 0 < 2 by omega) (okStep_ite (show 0 < 2 by omega) ?_)
    exact okStep_ite (show 0 < 2 by omega) (show 0 < 4 by omega)

theorem step16_agree (le : Bool) (r t : List Nat) :
    Agree (step16 le true r) (step16 le false (r ++ t)) r.length := by
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨x, _ | ⟨y, r⟩⟩⟩⟩
  · trivial
  · simp [step16, Agree]
  · simp only [step16, List.cons_append, List.nil_append]
    refine agree_ite (fun _ => ⟨rfl, by simp⟩) (fun _ => agree_ite (fun _ => ⟨rfl, by simp⟩) (fun _ => ?_))
    simp [Agree]
  · simp only [step16, List.cons_append, List.nil_append]
    refine agree_ite (fun _ => ⟨rfl, by simp⟩) (fun _ => agree_ite (fun _ => ⟨rfl, by simp⟩) (fun _ => ?_))
    simp [Agree]
  · simp only [step16, List.cons_append]
    refine agree_ite (fun _ => ⟨rfl, by simp⟩) (fun _ => agree_ite (fun _ => ⟨rfl, by simp⟩) (fun _ => ?_))
    exact agree_ite (fun _ => ⟨rfl, by simp⟩) (fun _ => ⟨rfl, by simp <;> omega⟩)

theorem step16_fail {le : Bool} {r : List Nat} {why : String} {s e : Nat}
    (h : step16 le true r = .fail why s e) : s = 0 ∧ e = 2 ∧ 2 ≤ r.length := by
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨x, _ | ⟨y, r⟩⟩⟩⟩
  · cases h
  · simp [step16] at h
  all_goals
    simp only [step16] at h
    split at h
    · cases h
    · split at h
      · cases h
        simp
      · first
          | (simp at h; done)
          | (split at h
             · cases h
               simp
             · cases h)

theorem step32_moves (le c : Bool) : Moves (step32 le c) := by
  refine ⟨rfl, ?_⟩
  intro r
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨x, _ | ⟨y, r⟩⟩⟩⟩
  · trivial
  · exact okStep_ite trivial (show 0 < 1 by omega)
  · exact okStep_ite trivial (show 0 < 2 by omega)
  · exact okStep_ite trivial (show 0 < 3 by omega)
  · simp only [step32]
    exact okStep_ite (show 0 < 4 by omega) (okStep_ite (show 0 < 4 by omega) (show 0 < 4 by omega))

theorem step32_agree (le : Bool) (r t : List Nat) :
    Agree (step32 le true r) (step32 le false (r ++ t)) r.length := by
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨x, _ | ⟨y, r⟩⟩⟩⟩
  · trivial
  · simp [step32, Agree]
  · simp [step32, Agree]
  · simp [step32, Agree]
  · simp only [step32, List.cons_append]
    exact agree_ite (fun _ => ⟨rfl, by simp <;> omega⟩)
      (fun _ => agree_ite (fun _ => ⟨rfl, by simp <;> omega⟩) (fun _ => ⟨rfl, by simp <;> omega⟩))

theorem step32_fail {le : Bool} {r : List Nat} {why : String} {s e : Nat}
    (h : step32 le true r = .fail why s e) : s = 0 ∧ e = 4 ∧ 4 ≤ r.length := by
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨x, _ | ⟨y, r⟩⟩⟩⟩
  · cases h
  · simp [step32] at h
  · simp [step32] at h
  · simp [step32] at h
  · simp only [step32] at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (cases h; simp <;> omega)

theorem utf16_is_driver (bo : Int) (hbo : bo ≠ 0) (h : ErrHandler) (b : Bytes) (final : Bool) :
    utf16DecodeFull b bo h final =
      decodeDriver (step16 (decide (bo ≤ 0)) !final) h (if decide (bo ≤ 0) then "utf-16-le" else "utf-16-be")
        (if decide (bo ≤ 0) then .utf16le else .utf16be) b (b.length + 1) 0 b [] := by
  have hb : bom16 bo b = (bo, 0) := by
    unfold bom16
    split
    · rw [if_neg hbo]
    · rfl
  simp only [utf16DecodeFull, hb, List.drop_zero]
  split
  · next he =>
    have : b = [] := List.isEmpty_iff.1 he
    subst this
    rfl
  · rfl

theorem utf32_is_driver (bo : Int) (hbo : bo ≠ 0) (h : ErrHandler) (b : Bytes) (final : Bool) :
    utf32DecodeFull b bo h final =
      decodeDriver (step32 (decide (bo ≤ 0)) !final) h (if decide (bo ≤ 0) then "utf-32-le" else "utf-32-be")
        (if decide (bo ≤ 0) then .utf32le else .utf32be) b (b.length + 1) 0 b [] := by
  have hb : bom32 bo b = (bo, 0) := by
    unfold bom32
    split
    · rw [if_neg hbo]
    · rfl
  simp only [utf32DecodeFull, hb, List.drop_zero]
  split
  · next he =>
    have : b = [] := List.isEmpty_iff.1 he
    subst this
    rfl
  · rfl

/-- UTF-16 with a fixed byte order, `utf-16-le` and `utf-16-be`, in two chunks, wherever the input
is cut, a surrogate pair included, for every standard handler. `bo ≠ 0` keeps the BOM out: with one,
the incremental decoder is a Python class, `Lib/encodings/utf_16.py`. -/
def Utf16Chunks : Prop :=
  ∀ (b : Bytes) (k : Nat) (bo : Int) (h : ErrHandler), bo ≠ 0 →
    Chunked (fun x final => utf16DecodeFull x bo h final) b k

theorem utf16Chunks_proven : Utf16Chunks := by
  intro b k bo h hbo
  refine chunked_driver (step16_moves _ true) (step16_moves _ false) h _ _ b k
    (fun i => step16_agree _ _ _) ?_ _ (fun x => utf16_is_driver bo hbo h x false)
    (fun x => utf16_is_driver bo hbo h x true)
  intro i why s e hs
  obtain ⟨h0, h2, hl⟩ := step16_fail hs
  subst h0 h2
  simp only [List.length_drop] at hl
  refine handler_loc h _ _ _ _ _ _ _ (by omega) (by omega) (fun _ => .inr ?_)
  have : (if decide (bo ≤ 0) = true then EncCode.utf16le else .utf16be).bytelength = 2 := by
    split <;> rfl
  rw [this]
  omega

/-- The same for UTF-32. -/
def Utf32Chunks : Prop :=
  ∀ (b : Bytes) (k : Nat) (bo : Int) (h : ErrHandler), bo ≠ 0 →
    Chunked (fun x final => utf32DecodeFull x bo h final) b k

theorem utf32Chunks_proven : Utf32Chunks := by
  intro b k bo h hbo
  refine chunked_driver (step32_moves _ true) (step32_moves _ false) h _ _ b k
    (fun i => step32_agree _ _ _) ?_ _ (fun x => utf32_is_driver bo hbo h x false)
    (fun x => utf32_is_driver bo hbo h x true)
  intro i why s e hs
  obtain ⟨h0, h2, hl⟩ := step32_fail hs
  subst h0 h2
  simp only [List.length_drop] at hl
  refine handler_loc h _ _ _ _ _ _ _ (by omega) (by omega) (fun _ => .inr ?_)
  have : (if decide (bo ≤ 0) = true then EncCode.utf32le else .utf32be).bytelength = 4 := by
    split <;> rfl
  rw [this]
  omega

/-! ## `unicode_escape` -/

theorem name_cons {c : Nat} {cs : List Nat} (hc : c ≠ 125) :
    nameBytes (c :: cs) = (nameBytes cs).map (c :: ·) := by
  rw [nameBytes.eq_def]
  split <;> simp_all

theorem nameBytes_app : ∀ (r t name : List Nat), nameBytes r = some name →
    nameBytes (r ++ t) = some name ∧ name.length < r.length := by
  intro r
  induction r with
  | nil =>
    intro t name h
    simp [nameBytes] at h
  | cons c cs ih =>
    intro t name h
    by_cases hc : c = 125
    · subst hc
      simp only [nameBytes, Option.some.injEq] at h
      subst h
      simp [nameBytes]
    · rw [name_cons hc] at h
      cases hn : nameBytes cs with
      | none =>
        rw [hn] at h
        cases h
      | some m =>
        rw [hn] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨h1, h2⟩ := ih t m hn
        rw [List.cons_append, name_cons hc, h1]
        simp [h2]

theorem stepName_other (names : List Nat → Option Nat) (c : Bool) {x : Nat} (r : List Nat)
    (hx : x ≠ 123) : stepName names c (x :: r) = .fail "malformed \\N character escape" 0 2 := by
  unfold stepName
  split <;> simp_all

theorem stepName_agree (names : List Nat → Option Nat) (r t : List Nat) :
    Agree (stepName names true r) (stepName names false (r ++ t)) (2 + r.length) := by
  cases r with
  | nil => simp [stepName, Agree]
  | cons x r =>
    by_cases hx : x = 123
    · subst hx
      simp only [stepName, List.cons_append]
      cases hn : nameBytes r with
      | none => simp [Agree]
      | some name =>
        obtain ⟨h1, h2⟩ := nameBytes_app r t name hn
        rw [h1]
        cases name with
        | nil => exact ⟨rfl, by simp <;> omega⟩
        | cons n ns =>
          dsimp only
          simp only [List.length_cons] at h2
          cases hc : names (n :: ns) with
          | some ch => exact ⟨rfl, by simp <;> omega⟩
          | none => exact ⟨rfl, by simp <;> omega⟩
    · rw [List.cons_append, stepName_other names true r hx, stepName_other names false _ hx]
      exact ⟨rfl, by simp <;> omega⟩

theorem stepName_ok (names : List Nat → Option Nat) (c : Bool) (r : List Nat) :
    okStep (stepName names c r) := by
  cases r with
  | nil => exact okStep_ite trivial (show 0 < 2 by omega)
  | cons x r =>
    by_cases hx : x = 123
    · subst hx
      simp only [stepName]
      cases hn : nameBytes r with
      | none => exact okStep_ite trivial (show 0 < 3 + r.length by omega)
      | some name =>
        cases name with
        | nil => show 0 < 3; omega
        | cons n ns =>
          dsimp only
          cases hc : names (n :: ns) with
          | some ch => show 0 < 4 + _; omega
          | none => show 0 < 4 + _; omega
    · rw [stepName_other names c r hx]
      show 0 < 2
      omega

theorem esc_moves (names : List Nat → Option Nat) (c : Bool) : Moves (stepUnicodeEscape names c) := by
  refine ⟨rfl, ?_⟩
  intro r
  have two : okStep (DStep.char 0 2) := by show 0 < 2; omega
  cases r with
  | nil => trivial
  | cons x r =>
    simp only [stepUnicodeEscape]
    refine okStep_ite (show 0 < 1 by omega) ?_
    cases r with
    | nil => exact okStep_ite trivial (show 0 < 1 by omega)
    | cons e r =>
      refine okStep_ite (show 0 < 2 by omega) ?_
      repeat refine okStep_ite (show 0 < 2 by omega) ?_
      refine okStep_ite ?_ (okStep_ite (stepHex_ok ..) (okStep_ite (stepHex_ok ..)
        (okStep_ite (stepHex_ok ..) (okStep_ite (stepName_ok ..) (show 0 < 2 by omega)))))
      show okStep (match octalEscape (e - 48) r with | (ch, n) => DStep.char ch (2 + n))
      cases octalEscape (e - 48) r
      show 0 < 2 + _
      omega

/-- An octal digit. -/
def isOctal (c : Nat) : Prop := 48 ≤ c ∧ c ≤ 55

instance (c : Nat) : Decidable (isOctal c) := by unfold isOctal; exact inferInstance

/-- What is left of the input may hold an octal escape with fewer than three digits. -/
def Pending (r : List Nat) : Prop := r = [] ∨ ∃ a, r = [a] ∧ isOctal a

theorem octal_app (d : Nat) (r t : List Nat)
    (hp : Pending r → ∀ x, t.head? = some x → ¬isOctal x) :
    octalEscape d (r ++ t) = octalEscape d r ∧ (octalEscape d r).2 ≤ r.length := by
  rcases r with _ | ⟨a, _ | ⟨b, r⟩⟩
  · have ht : ∀ x, t.head? = some x → ¬isOctal x := hp (.inl rfl)
    refine ⟨?_, by simp [octalEscape]⟩
    rcases t with _ | ⟨x, _ | ⟨y, u⟩⟩
    · rfl
    · have := ht x rfl
      simp only [isOctal] at this
      simp [octalEscape, this]
    · have := ht x rfl
      simp only [isOctal] at this
      simp [octalEscape, this]
  · by_cases ha : isOctal a
    · have ht : ∀ x, t.head? = some x → ¬isOctal x := hp (.inr ⟨a, rfl, ha⟩)
      have ha' : 48 ≤ a ∧ a ≤ 55 := ha
      refine ⟨?_, by simp [octalEscape, ha']⟩
      rcases t with _ | ⟨x, u⟩
      · rfl
      · have := ht x rfl
        simp only [isOctal] at this
        simp [octalEscape, ha', this]
    · have ha' : ¬(48 ≤ a ∧ a ≤ 55) := ha
      refine ⟨?_, by simp [octalEscape, ha']⟩
      rcases t with _ | ⟨x, u⟩
      · rfl
      · simp [octalEscape, ha']
  · refine ⟨by simp [octalEscape], ?_⟩
    simp only [octalEscape]
    split
    · split <;> simp <;> omega
    · simp

theorem esc_agree (names : List Nat → Option Nat) (r t : List Nat)
    (hO : ∀ e r', r = 92 :: e :: r' → isOctal e → Pending r' → ∀ x, t.head? = some x → ¬isOctal x) :
    Agree (stepUnicodeEscape names true r) (stepUnicodeEscape names false (r ++ t)) r.length := by
  cases r with
  | nil => trivial
  | cons c r =>
    simp only [stepUnicodeEscape, List.cons_append]
    refine agree_ite (fun _ => ⟨rfl, by simp⟩) (fun hc => ?_)
    cases r with
    | nil => simp [Agree]
    | cons e r =>
      have hc92 : c = 92 := by simpa using hc
      subst hc92
      simp only [List.cons_append]
      have two : 2 ≤ (92 :: e :: r).length := by simp
      repeat refine agree_ite (fun _ => ⟨rfl, two⟩) (fun _ => ?_)
      refine agree_ite (fun ho => ?_) (fun _ => ?_)
      · obtain ⟨h1, h2⟩ := octal_app (e - 48) r t (hO e r rfl ho)
        rw [h1]
        show Agree (match octalEscape (e - 48) r with | (ch, n) => DStep.char ch (2 + n))
          (match octalEscape (e - 48) r with | (ch, n) => DStep.char ch (2 + n)) _
        cases he : octalEscape (e - 48) r with
        | mk ch n =>
          rw [he] at h2
          exact ⟨rfl, by simp at h2 ⊢; omega⟩
      · refine agree_ite (fun _ => agree_le (stepHex_agree ..) (by simp; omega)) (fun _ => ?_)
        refine agree_ite (fun _ => agree_le (stepHex_agree ..) (by simp; omega)) (fun _ => ?_)
        refine agree_ite (fun _ => agree_le (stepHex_agree ..) (by simp; omega)) (fun _ => ?_)
        exact agree_ite (fun _ => agree_le (stepName_agree ..) (by simp; omega)) (fun _ => ⟨rfl, two⟩)

theorem esc_is_driver (names : List Nat → Option Nat) (h : ErrHandler) (b : Bytes) (final : Bool) :
    unicodeEscapeDecode b h names final =
      decodeDriver (stepUnicodeEscape names !final) h "unicodeescape" .unknown b (b.length + 1) 0 b [] := by
  unfold unicodeEscapeDecode
  split
  · next he =>
    have : b = [] := List.isEmpty_iff.1 he
    subst this
    rfl
  · rfl

/-- The cut falls inside an octal escape and the next chunk starts with one more digit for it. That
is the one place the decoder does not wait: `\10` then `7`. `unicodeEscapeChunks_refuted` is this
case. A `\` before the backslash is not looked at, so this also covers `\\10`, which is not an
octal escape. -/
def OctalCut (a t : Bytes) : Prop :=
  (∃ x, t.head? = some x ∧ isOctal x) ∧
    ∃ u, (∃ e, a = u ++ [92, e] ∧ isOctal e) ∨ (∃ e x, a = u ++ [92, e, x] ∧ isOctal e ∧ isOctal x)

/-- `unicode_escape` in two chunks, for every handler and name table, wherever the input is cut, in
the middle of `\x`, `\u`, `\U` and `\N{...}` included, unless the cut is an `OctalCut`. -/
def UnicodeEscapeChunksNarrow : Prop :=
  ∀ (b : Bytes) (k : Nat) (names : List Nat → Option Nat) (h : ErrHandler),
    ¬OctalCut (b.take k) (b.drop k) →
    Chunked (fun x final => unicodeEscapeDecode x h names final) b k

theorem unicodeEscapeChunksNarrow_proven : UnicodeEscapeChunksNarrow := by
  intro b k names h hcut
  have hag : ∀ i, Agree (stepUnicodeEscape names true ((b.take k).drop i))
      (stepUnicodeEscape names false ((b.take k).drop i ++ b.drop k)) ((b.take k).drop i).length := by
    intro i
    refine esc_agree names _ _ ?_
    intro e r' hr he hp x hx ho
    apply hcut
    refine ⟨⟨x, hx, ho⟩, (b.take k).take i, ?_⟩
    have hs := List.take_append_drop i (b.take k)
    rw [hr] at hs
    rcases hp with rfl | ⟨a, rfl, ha⟩
    · exact .inl ⟨e, hs.symm, he⟩
    · exact .inr ⟨e, a, hs.symm, he, ha⟩
  refine chunked_driver (esc_moves names true) (esc_moves names false) h "unicodeescape" .unknown b k
    hag ?_ _ (fun x => esc_is_driver names h x false) (fun x => esc_is_driver names h x true)
  intro i why s e hs
  have hg := hag i
  rw [hs] at hg
  have hok := (esc_moves names true).ok ((b.take k).drop i)
  rw [hs] at hok
  have hle := hg.2
  have hne : (b.take k).drop i ≠ [] := by
    intro he
    rw [he] at hs
    cases hs
  have hl := List.length_pos_iff.2 hne
  simp only [List.length_drop] at hle hl
  simp only [okStep] at hok
  exact handler_loc h _ _ _ _ _ _ _ (by omega) (by omega) (fun _ => .inl rfl)

end PyLean.UnicodeObj
