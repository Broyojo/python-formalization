import PyLean.TextLibs.BinasciiModel

/-!
Properties of the base64 and hex models. Each statement was smoke-tested on
CPython 3.14.7 over 400000 random inputs before being proved.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

set_option linter.unusedSimpArgs false

/-- `v` survives `table_b2a_base64` then `table_a2b_base64`, and is never `'='`. -/
theorem tables_inverse : ∀ v, v < 64 → a2bChar (b2aChar v) = v ∧ b2aChar v ≠ 61 := by decide

/-- One data character: the decoder advances by `decStep`. -/
theorem a2bLoop_data (strict : Bool) (v : Nat) (hv : v < 64) (cs : List Nat) (i : Nat) (st : Dec)
    (hp : st.pads = 0) :
    a2bLoop strict (b2aChar v :: cs) i st = a2bLoop strict cs (i + 1) (decStep st v) := by
  obtain ⟨h1, h2⟩ := tables_inverse v hv
  have hst : { st with pads := 0 } = st := by cases st; simp_all
  rw [a2bLoop, if_neg h2]
  simp only [h1, hst]
  rw [if_neg (by omega), if_neg (by simp [hp])]

/-- `a2bLoop` on a pad byte, when the position allows it. -/
theorem a2bLoop_pad (strict : Bool) (cs : List Nat) (i : Nat) (st : Dec)
    (h : st.quad ≥ 2 ∧ st.quad + (st.pads + 1) ≤ 4) :
    a2bLoop strict (61 :: cs) i st = a2bLoop strict cs (i + 1) { st with pads := st.pads + 1 } := by
  rw [a2bLoop, if_pos rfl]
  simp only [if_pos h]

/-- The encoder's output for `d`, with the tail, from a clean state. -/
def enc (d : List Nat) (left : Nat) : List Nat :=
  let (out, l, bits) := b2aLoop d left 0
  out ++ (if bits = 2 then [b2aChar (l % 4 * 16), 61, 61]
          else if bits = 4 then [b2aChar (l % 16 * 4), 61] else [])

theorem b2aBase64_eq_enc (d : List Nat) : b2aBase64 d false = enc d 0 := by
  simp [b2aBase64, enc]

/-- `leftchar = (leftchar << 8) | byte` in 32 bits. -/
def L (y x : Nat) : Nat := (x * 256 + y) % 2 ^ 32

/-- The wrap at 32 bits never reaches the low bytes, which are all the encoder reads. -/
theorem L_low1 (x y : Nat) (hy : y < 256) : L y x % 256 = y := by unfold L; omega
theorem L_low2 (x y r : Nat) (hx : x % 256 = r) (hy : y < 256) : L y x % 65536 = r * 256 + y := by
  unfold L; omega
theorem L_low3 (x y r : Nat) (hx : x % 65536 = r) (hy : y < 256) :
    L y x % 16777216 = r * 256 + y := by
  unfold L; omega

theorem step0 (a : Nat) (r : List Nat) (left : Nat) : b2aLoop (a :: r) left 0 =
    (b2aChar (L a left / 4 % 64) :: (b2aLoop r (L a left) 2).1, (b2aLoop r (L a left) 2).2) := rfl
theorem step2 (b : Nat) (r : List Nat) (l : Nat) : b2aLoop (b :: r) l 2 =
    (b2aChar (L b l / 16 % 64) :: (b2aLoop r (L b l) 4).1, (b2aLoop r (L b l) 4).2) := rfl
theorem step4 (c : Nat) (r : List Nat) (l : Nat) : b2aLoop (c :: r) l 4 =
    (b2aChar (L c l / 64 % 64) :: b2aChar (L c l / 1 % 64) :: (b2aLoop r (L c l) 0).1,
      (b2aLoop r (L c l) 0).2) := rfl

/-- `enc` in terms of the loop's components. -/
theorem enc_eq (d : List Nat) (left : Nat) : enc d left =
    (b2aLoop d left 0).1 ++
      (if (b2aLoop d left 0).2.2 = 2 then [b2aChar ((b2aLoop d left 0).2.1 % 4 * 16), 61, 61]
       else if (b2aLoop d left 0).2.2 = 4 then [b2aChar ((b2aLoop d left 0).2.1 % 16 * 4), 61]
       else []) := rfl

/-- Three input bytes become exactly four characters, whatever `leftchar` held. -/
theorem enc_three (a b c : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256)
    (left : Nat) (r : List Nat) :
    enc (a :: b :: c :: r) left =
      b2aChar (a / 4) :: b2aChar (a % 4 * 16 + b / 16) :: b2aChar (b % 16 * 4 + c / 64) ::
      b2aChar (c % 64) :: enc r (L c (L b (L a left))) := by
  have h1 := L_low1 left a ha
  have h2 := L_low2 _ b a h1 hb
  have h3 := L_low3 _ c _ h2 hc
  have e1 : L a left / 4 % 64 = a / 4 := by omega
  have e2 : L b (L a left) / 16 % 64 = a % 4 * 16 + b / 16 := by omega
  have e3 : L c (L b (L a left)) / 64 % 64 = b % 16 * 4 + c / 64 := by omega
  have e4 : L c (L b (L a left)) / 1 % 64 = c % 64 := by omega
  have hp : b2aLoop (a :: b :: c :: r) left 0 =
      (b2aChar (L a left / 4 % 64) :: b2aChar (L b (L a left) / 16 % 64) ::
        b2aChar (L c (L b (L a left)) / 64 % 64) :: b2aChar (L c (L b (L a left)) / 1 % 64) ::
        (b2aLoop r (L c (L b (L a left))) 0).1, (b2aLoop r (L c (L b (L a left))) 0).2) := rfl
  rw [e1, e2, e3, e4] at hp
  unfold enc
  rw [hp]
  rfl

/-- Decoding one group ends in a clean state with the three bytes appended. -/
theorem decStep_group (v1 v2 v3 v4 l0 : Nat) (o : List Nat) :
    decStep (decStep (decStep (decStep ⟨0, 0, l0, o⟩ v1) v2) v3) v4 =
      ⟨0, 0, 0, o ++ [(v1 * 4 + v2 / 16) % 256, (v2 % 16 * 16 + v3 / 4) % 256,
        (v3 % 4 * 64 + v4) % 256]⟩ := by
  simp only [decStep, List.append_assoc, List.cons_append, List.nil_append]

/-- The decoder undoes one four-character group. -/
theorem a2bLoop_group (strict : Bool) (a b c : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256)
    (cs : List Nat) (i l0 : Nat) (o : List Nat) :
    a2bLoop strict (b2aChar (a / 4) :: b2aChar (a % 4 * 16 + b / 16) ::
        b2aChar (b % 16 * 4 + c / 64) :: b2aChar (c % 64) :: cs) i ⟨0, 0, l0, o⟩
      = a2bLoop strict cs (i + 1 + 1 + 1 + 1) ⟨0, 0, 0, o ++ [a, b, c]⟩ := by
  rw [a2bLoop_data strict _ (by omega) _ _ _ rfl, a2bLoop_data strict _ (by omega) _ _ _ rfl,
    a2bLoop_data strict _ (by omega) _ _ _ rfl, a2bLoop_data strict _ (by omega) _ _ _ rfl,
    decStep_group]
  have e1 : (a / 4 * 4 + (a % 4 * 16 + b / 16) / 16) % 256 = a := by omega
  have e2 : ((a % 4 * 16 + b / 16) % 16 * 16 + (b % 16 * 4 + c / 64) / 4) % 256 = b := by omega
  have e3 : ((b % 16 * 4 + c / 64) % 4 * 64 + c % 64) % 256 = c := by omega
  rw [e1, e2, e3]

/-- What a completed decode needs: every encoder output ends on a valid position. -/
def Finished (st : Dec) (want : List Nat) : Prop :=
  st.out = want ∧ st.quad ≠ 1 ∧ ¬(st.quad ≠ 0 ∧ st.quad + st.pads < 4)

theorem roundtrip_go (strict : Bool) : ∀ (n : Nat) (d : List Nat), d.length ≤ n →
    (∀ x ∈ d, x < 256) → ∀ (left i l0 : Nat) (o : List Nat),
    ∃ st, a2bLoop strict (enc d left) i ⟨0, 0, l0, o⟩ = .ok st ∧ Finished st (o ++ d) := by
  intro n
  induction n with
  | zero =>
    intro d hl _ left i l0 o
    have : d = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨_, rfl, by simp [Finished]⟩
  | succ n ih =>
    intro d hl hb left i l0 o
    match d, hl, hb with
    | [], _, _ => exact ⟨_, rfl, by simp [Finished]⟩
    | [a], _, hb =>
      have ha : a < 256 := hb a (by simp)
      have h1 := L_low1 left a ha
      have he : enc [a] left =
          [b2aChar (L a left / 4 % 64), b2aChar (L a left % 4 * 16), 61, 61] := rfl
      generalize L a left = l1 at he h1
      have e1 : l1 / 4 % 64 = a / 4 := by omega
      have e2 : l1 % 4 * 16 = a % 4 * 16 := by omega
      rw [he, e1, e2, a2bLoop_data strict _ (by omega) _ _ _ rfl,
        a2bLoop_data strict _ (by omega) _ _ _ rfl,
        a2bLoop_pad strict _ _ _ (by simp [decStep]), a2bLoop_pad strict _ _ _ (by simp [decStep])]
      refine ⟨_, rfl, ?_, ?_, ?_⟩
      · show o ++ [(a / 4 * 4 + a % 4 * 16 / 16) % 256] = o ++ [a]
        rw [show (a / 4 * 4 + a % 4 * 16 / 16) % 256 = a by omega]
      · simp [decStep]
      · simp [decStep]
    | [a, b], _, hb =>
      have ha : a < 256 := hb a (by simp)
      have hb' : b < 256 := hb b (by simp)
      have h1 := L_low1 left a ha
      have h2 := L_low2 _ b a h1 hb'
      have he : enc [a, b] left =
          [b2aChar (L a left / 4 % 64), b2aChar (L b (L a left) / 16 % 64),
           b2aChar (L b (L a left) % 16 * 4), 61] := rfl
      generalize hl2 : L b (L a left) = l2 at he h2
      generalize L a left = l1 at he h1
      have e1 : l1 / 4 % 64 = a / 4 := by omega
      have e2 : l2 / 16 % 64 = a % 4 * 16 + b / 16 := by omega
      have e3 : l2 % 16 * 4 = b % 16 * 4 := by omega
      rw [he, e1, e2, e3, a2bLoop_data strict _ (by omega) _ _ _ rfl,
        a2bLoop_data strict _ (by omega) _ _ _ rfl,
        a2bLoop_data strict _ (by omega) _ _ _ rfl,
        a2bLoop_pad strict _ _ _ (by simp [decStep])]
      refine ⟨_, rfl, ?_, ?_, ?_⟩
      · show o ++ [(a / 4 * 4 + (a % 4 * 16 + b / 16) / 16) % 256] ++
            [((a % 4 * 16 + b / 16) % 16 * 16 + b % 16 * 4 / 4) % 256] = o ++ [a, b]
        rw [show (a / 4 * 4 + (a % 4 * 16 + b / 16) / 16) % 256 = a by omega,
          show ((a % 4 * 16 + b / 16) % 16 * 16 + b % 16 * 4 / 4) % 256 = b by omega]
        simp
      · simp [decStep]
      · simp [decStep]
    | a :: b :: c :: r, hl, hb =>
      have ha : a < 256 := hb a (by simp)
      have hb' : b < 256 := hb b (by simp)
      have hc : c < 256 := hb c (by simp)
      rw [enc_three a b c ha hb' hc, a2bLoop_group strict a b c ha hb' hc]
      obtain ⟨st, h1, h2⟩ := ih r (by simp at hl; omega)
        (fun x hx => hb x (by simp [hx])) (L c (L b (L a left)))
        (i + 1 + 1 + 1 + 1) 0 (o ++ [a, b, c])
      refine ⟨st, h1, ?_⟩
      simpa [Finished] using h2

/-- `a2b_base64(b2a_base64(d, newline=False), strict_mode=s) == d` for every `bytes` value
`d` and both modes. The only hypothesis is the type invariant that `d` holds bytes. -/
def Base64RoundTrip : Prop :=
  ∀ (strict : Bool) (d : List Nat), (∀ x ∈ d, x < 256) →
    a2bBase64Bytes strict (b2aBase64 d false) = .ok d

theorem base64RoundTrip_proven : Base64RoundTrip := by
  intro strict d hd
  obtain ⟨st, h1, h2, h3, h4⟩ := roundtrip_go strict d.length d (Nat.le_refl _) hd 0 0 0 []
  rw [b2aBase64_eq_enc]
  unfold a2bBase64Bytes
  show (a2bLoop strict (enc d 0) 0 {} >>= _) = _
  have hempty : ({} : Dec) = ⟨0, 0, 0, []⟩ := rfl
  rw [hempty, h1]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [if_neg h3, if_neg h4, h2]
  simp

/-! ### Decoder laws -/

/-- The lenient loop never reads its index: `i` only selects a strict-mode message. -/
theorem lenient_index (s : List Nat) : ∀ (i j : Nat) (st : Dec),
    a2bLoop false s i st = a2bLoop false s j st := by
  induction s with
  | nil => intro _ _ _; rfl
  | cons c cs ih =>
    intro i j st
    unfold a2bLoop
    by_cases h61 : c = 61
    · simp only [if_pos h61]
      split
      · exact ih _ _ _
      · simp only [Bool.not_false, if_true]
        exact ih _ _ _
    · simp only [if_neg h61]
      split
      · simp only [Bool.false_eq_true, if_false]
        exact ih _ _ _
      · simp only [Bool.false_eq_true, and_false, if_false]
        exact ih _ _ _

def keepByte (c : Nat) : Bool := c == 61 || decide (a2bChar c < 64)

theorem lenient_filter (s : List Nat) : ∀ (i : Nat) (st : Dec),
    a2bLoop false (s.filter keepByte) i st = a2bLoop false s i st := by
  induction s with
  | nil => intro _ _; rfl
  | cons c cs ih =>
    intro i st
    by_cases hk : keepByte c = true
    · rw [List.filter_cons_of_pos hk]
      conv => lhs; unfold a2bLoop
      conv => rhs; unfold a2bLoop
      by_cases h61 : c = 61
      · simp only [if_pos h61]
        split
        · exact ih _ _
        · simp only [Bool.not_false, if_true]
          exact ih _ _
      · simp only [if_neg h61]
        split
        · simp only [Bool.false_eq_true, if_false]
          exact ih _ _
        · simp only [Bool.false_eq_true, and_false, if_false]
          exact ih _ _
    · rw [List.filter_cons_of_neg hk, ih]
      have h61 : c ≠ 61 := by
        intro h
        apply hk
        simp [keepByte, h]
      have hv : a2bChar c ≥ 64 := by
        have : ¬ (a2bChar c < 64) := by
          intro h
          apply hk
          simp [keepByte, h]
        omega
      conv => rhs; unfold a2bLoop
      simp only [if_neg h61, if_pos hv, Bool.false_eq_true, if_false]
      exact lenient_index _ _ _ _

/-- Non-alphabet bytes do not affect lenient decoding, including its errors and their
messages: they are "discarded prior to the padding check". -/
def LenientIgnoresNonAlphabet : Prop :=
  ∀ s : List Nat, a2bBase64Bytes false (s.filter keepByte) = a2bBase64Bytes false s

theorem lenientIgnoresNonAlphabet_proven : LenientIgnoresNonAlphabet := by
  intro s
  unfold a2bBase64Bytes
  rw [lenient_filter]

theorem strict_lenient_loop (s : List Nat) : ∀ (i j : Nat) (st st' : Dec),
    a2bLoop true s i st = .ok st' → st'.quad ≠ 1 → a2bLoop false s j st = .ok st' := by
  induction s with
  | nil =>
    intro _ _ _ _ h _
    exact h
  | cons c cs ih =>
    intro i j st st' h hq
    unfold a2bLoop at h ⊢
    by_cases h61 : c = 61
    · simp only [if_pos h61] at h ⊢
      split at h
      · rename_i hc
        rw [if_pos hc]
        exact ih _ _ _ _ h hq
      · rename_i hc
        rw [if_neg hc]
        simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
        split at h
        · rename_i h1
          cases h
          exact absurd h1 hq
        · cases h
    · simp only [if_neg h61] at h ⊢
      split at h
      · simp only [if_true] at h
        cases h
      · rename_i hv
        rw [if_neg hv]
        simp only [and_true] at h
        split at h
        · cases h
        · rename_i hp
          simp only [Bool.false_eq_true, and_false, if_false]
          have hp0 : st.pads = 0 := by omega
          exact ih _ _ _ _ h hq

/-- `strict_mode=True` only rejects: whatever it accepts, the default mode accepts with the
same result. -/
def StrictImpliesLenient : Prop :=
  ∀ (s r : List Nat), a2bBase64Bytes true s = .ok r → a2bBase64Bytes false s = .ok r

theorem strictImpliesLenient_proven : StrictImpliesLenient := by
  intro s r h
  unfold a2bBase64Bytes at h ⊢
  cases hl : a2bLoop true s 0 {} with
  | error e =>
    rw [hl] at h
    cases h
  | ok st =>
    rw [hl] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    by_cases h1 : st.quad = 1
    · rw [if_pos h1] at h
      cases h
    · rw [if_neg h1] at h
      rw [strict_lenient_loop s 0 0 {} st hl h1]
      simp only [bind, Except.bind, pure, Except.pure]
      rw [if_neg h1]
      exact h

/-! ### Length and hex -/

theorem enc_length : ∀ (n : Nat) (d : List Nat), d.length ≤ n → (∀ x ∈ d, x < 256) → ∀ left,
    (enc d left).length = (d.length + 2) / 3 * 4 := by
  intro n
  induction n with
  | zero =>
    intro d hl _ left
    have : d = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rfl
  | succ n ih =>
    intro d hl hb left
    match d, hl, hb with
    | [], _, _ => rfl
    | [a], _, _ =>
      have he : enc [a] left =
          [b2aChar (L a left / 4 % 64), b2aChar (L a left % 4 * 16), 61, 61] := rfl
      rw [he]
      simp only [List.length_cons, List.length_nil]
    | [a, b], _, _ =>
      have he : enc [a, b] left =
          [b2aChar (L a left / 4 % 64), b2aChar (L b (L a left) / 16 % 64),
           b2aChar (L b (L a left) % 16 * 4), 61] := rfl
      rw [he]
      simp only [List.length_cons, List.length_nil]
    | a :: b :: c :: r, hl, hb =>
      rw [enc_three a b c (hb a (by simp)) (hb b (by simp)) (hb c (by simp)),
        List.length_cons, List.length_cons, List.length_cons, List.length_cons,
        ih r (by simp at hl; omega) (fun x hx => hb x (by simp [hx]))]
      simp only [List.length_cons]
      omega

/-- `len(b2a_base64(d, newline=False))` is `4 * ceil(len(d) / 3)`. -/
def B2aLength : Prop :=
  ∀ d : List Nat, (∀ x ∈ d, x < 256) → (b2aBase64 d false).length = (d.length + 2) / 3 * 4

theorem b2aLength_proven : B2aLength := by
  intro d hd
  rw [b2aBase64_eq_enc, enc_length d.length d (Nat.le_refl _) hd]

theorem hexDigit_inverse : ∀ v, v < 16 → digitValue (hexDigit v) = v := by decide

theorem b2aHex_length (d : List Nat) : (b2aHex d).length = 2 * d.length := by
  induction d with
  | nil => rfl
  | cons _ _ ih =>
    simp only [b2aHex, List.length_cons, ih]
    omega

/-- `unhexlify(hexlify(d)) == d` for every `bytes` value. -/
def HexRoundTrip : Prop :=
  ∀ d : List Nat, (∀ x ∈ d, x < 256) → a2bHexBytes (b2aHex d) = .ok d

theorem hexRoundTrip_proven : HexRoundTrip := by
  intro d hd
  have hloop : ∀ d : List Nat, (∀ x ∈ d, x < 256) → a2bHexLoop (b2aHex d) = .ok d := by
    intro d
    induction d with
    | nil => intro _; rfl
    | cons b r ih =>
      intro hb
      have h : b < 256 := hb b (by simp)
      have ht := hexDigit_inverse (b / 16) (by omega)
      have hu := hexDigit_inverse (b % 16) (by omega)
      simp only [b2aHex, a2bHexLoop, ht, hu]
      rw [if_neg (by omega), ih (fun x hx => hb x (by simp [hx]))]
      simp only [bind, Except.bind, pure, Except.pure]
      rw [show b / 16 * 16 + b % 16 = b by omega]
  unfold a2bHexBytes
  rw [b2aHex_length, if_neg (by omega)]
  exact hloop d hd

/-! ### `Lib/base64.py` over the C functions -/

/-- `b64decode(b64encode(d), validate=v) == d` for every `bytes` value and both modes. -/
def B64ModuleRoundTrip : Prop :=
  ∀ (validate : Bool) (d out : List Nat), (∀ x ∈ d, x < 256) →
    b64encode d none = .ok out → b64decode (.bytes out) none validate = .ok d

theorem b64ModuleRoundTrip_proven : B64ModuleRoundTrip := by
  intro validate d out hd h
  simp only [b64encode] at h
  cases h
  exact base64RoundTrip_proven validate d hd

end PyLean.TextLibs.Binascii
