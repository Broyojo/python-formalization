import PyLean.TextLibs.BinasciiC
import PyLean.TextLibs.BinasciiProps3
import PyLean.TextLibs.BinasciiProps7

/-!
The base64 codec of 3.15.2, with its fast paths, against the one-loop decoder and the bit-at-a-time
encoder the earlier proofs were written on. `a2bBase64Bytes` and `b2aBase64` are specifications now:
these theorems say the C functions compute them at the default options, and the statements in this
file are about the C functions.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

set_option linter.unusedSimpArgs false

/-! ### Tables -/

theorem revT64_lt : ∀ c, c < 256 → revT b64Alpha (some 61) c = if c = 61 then 64 else a2bChar c := by
  decide +kernel

theorem revT_large (a : List Nat) (p : Option Nat) (c : Nat) (hp : p ≠ some c) (h : ∀ x ∈ a, x ≠ c) : revT a p c = 255 := by
  have h1 : (p == some c) = false := by simpa using hp
  have h2 : (a.zipIdx.reverse.find? (·.1 == c)) = none := by
    apply List.find?_eq_none.mpr
    intro x hx
    have hm : x ∈ a.zipIdx := List.mem_reverse.mp hx
    have : x.1 ∈ a := List.fst_mem_of_mem_zipIdx hm
    simpa using h x.1 this
  simp [revT, h1, h2]

theorem b64Alpha_lt : ∀ x ∈ b64Alpha, x < 128 := by decide +kernel

/-- The default table is the one of the earlier model, for every byte value and beyond. -/
theorem revT64 (c : Nat) : revT b64Alpha (some 61) c = if c = 61 then 64 else a2bChar c := by
  by_cases h : c < 256
  · exact revT64_lt c h
  · have h1 : revT b64Alpha (some 61) c = 255 := by
      apply revT_large
      · intro e
        have : c = 61 := by simpa using e.symm
        omega
      · intro x hx
        have := b64Alpha_lt x hx
        omega
    have h2 : a2bChar c = 255 := by
      simp only [a2bChar]
      repeat (rw [if_neg (by omega)])
    rw [h1, if_neg (by omega), h2]

/-- The options of the default decoder. -/
def cfg64 (strict : Bool) : B64 := ⟨strict, true, revT b64Alpha (some 61), none⟩

/-! ### The fast path changes nothing -/

theorem a2bLoop_i (strict : Bool) : ∀ (s : List Nat) (i j : Nat) (st : Dec), a2bLoop strict s i st = a2bLoop strict s j st := by
  intro s
  induction s with
  | nil => intro i j st; rfl
  | cons c r ih =>
    intro i j st
    simp only [a2bLoop]
    split
    · split
      · exact ih _ _ _
      · split
        · exact ih _ _ _
        · rfl
    · split
      · split
        · rfl
        · exact ih _ _ _
      · split
        · rfl
        · exact ih _ _ _

theorem step_data (strict : Bool) (a : Nat) (r : List Nat) (i : Nat) (st : Dec) (h61 : a ≠ 61) (hv : a2bChar a < 64)
    (hp : st.pads = 0) : a2bLoop strict (a :: r) i st = a2bLoop strict r (i + 1) (decStep st (a2bChar a)) := by
  have hst : { st with pads := 0 } = st := by cases st; simp_all
  rw [a2bLoop, if_neg h61]
  simp only [hst]
  rw [if_neg (by omega), if_neg (by simp [hp])]

/-- `base64_decode_quad` does what four turns of the slow loop do. -/
theorem quad_steps (strict : Bool) (a b c d : Nat) (o r out : List Nat) (i : Nat)
    (hq : quad64 (revT b64Alpha (some 61)) a b c d = some o) :
    a2bLoop strict (a :: b :: c :: d :: r) i ⟨0, 0, 0, out⟩ = a2bLoop strict r i ⟨0, 0, 0, out ++ o⟩ := by
  simp only [quad64] at hq
  by_cases hn : revT b64Alpha (some 61) a ≥ 64 ∨ revT b64Alpha (some 61) b ≥ 64 ∨ revT b64Alpha (some 61) c ≥ 64 ∨
      revT b64Alpha (some 61) d ≥ 64
  · rw [if_pos hn] at hq
    cases hq
  · rw [if_neg hn] at hq
    have key : ∀ x, ¬ revT b64Alpha (some 61) x ≥ 64 → x ≠ 61 ∧ a2bChar x < 64 := by
      intro x hx
      rw [revT64] at hx
      by_cases h : x = 61
      · simp [h] at hx
      · simp only [if_neg h] at hx
        exact ⟨h, by omega⟩
    simp only [not_or] at hn
    obtain ⟨n1, n2, n3, n4⟩ := hn
    obtain ⟨a1, a2⟩ := key a n1
    obtain ⟨b1, b2⟩ := key b n2
    obtain ⟨c1, c2⟩ := key c n3
    obtain ⟨d1, d2⟩ := key d n4
    simp only [revT64, if_neg a1, if_neg b1, if_neg c1, if_neg d1, Option.some.injEq] at hq
    rw [step_data strict a _ _ _ a1 a2 rfl, step_data strict b _ _ _ b1 b2 rfl, step_data strict c _ _ _ c1 c2 rfl,
      step_data strict d _ _ _ d1 d2 rfl, decStep_group, a2bLoop_i strict r _ i]
    subst hq
    have e2 : (a2bChar b % 16 * 16 + a2bChar c / 4) % 256 = (a2bChar b * 16 + a2bChar c / 4) % 256 := by omega
    have e3 : (a2bChar c % 4 * 64 + a2bChar d) % 256 = (a2bChar c * 64 + a2bChar d) % 256 := by omega
    rw [e2, e3]

/-- `base64_decode_fast` can be taken out of a run from a clean position. -/
theorem fast_loop (strict : Bool) : ∀ (n : Nat) (s out : List Nat), s.length ≤ n → ∀ (i : Nat),
    a2bLoop strict s i ⟨0, 0, 0, out⟩ =
      a2bLoop strict (fast64 (revT b64Alpha (some 61)) s out).1 i ⟨0, 0, 0, (fast64 (revT b64Alpha (some 61)) s out).2⟩ := by
  intro n
  induction n with
  | zero =>
    intro s out h i
    have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [fast64]
  | succ n ih =>
    intro s out h i
    match s, h with
    | a :: b :: c :: d :: r, h =>
      rw [fast64]
      cases hq : quad64 (revT b64Alpha (some 61)) a b c d with
      | none => rfl
      | some o =>
        simp only
        rw [quad_steps strict a b c d o r out i hq]
        exact ih r (out ++ o) (by simp at h; omega) i
    | [], _ => simp [fast64]
    | [_], _ => simp [fast64]
    | [_, _], _ => simp [fast64]
    | [_, _, _], _ => simp [fast64]

theorem fast_len (t : Nat → Nat) : ∀ (n : Nat) (s out : List Nat), s.length ≤ n → (fast64 t s out).1.length ≤ s.length := by
  intro n
  induction n with
  | zero =>
    intro s out h
    have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [fast64]
  | succ n ih =>
    intro s out h
    match s, h with
    | a :: b :: c :: d :: r, h =>
      rw [fast64]
      cases hq : quad64 t a b c d with
      | none => simp
      | some o =>
        simp only
        have := ih r (out ++ o) (by simp at h; omega)
        simp only [List.length_cons]
        omega
    | [], _ => simp [fast64]
    | [_], _ => simp [fast64]
    | [_, _], _ => simp [fast64]
    | [_, _, _], _ => simp [fast64]

theorem cfg_padded (s : Bool) : (cfg64 s).padded = true := rfl
theorem cfg_strict (s : Bool) : (cfg64 s).strict = s := rfl
theorem cfg_tbl (s : Bool) : (cfg64 s).tbl = revT b64Alpha (some 61) := rfl
theorem cfg_ig (s : Bool) : (cfg64 s).ig = none := rfl

/-- The loop of `binascii_a2b_base64_impl` with default options is the slow loop alone. -/
theorem run_eq (strict : Bool) : ∀ (f : Nat) (s : List Nat) (st : Dec), s.length < f →
    a2b64Run (cfg64 strict) f s st = a2bLoop strict s 0 st := by
  intro f
  induction f with
  | zero => intro _ _ h; omega
  | succ f ih =>
    intro s st h
    cases s with
    | nil => rfl
    | cons x xs =>
      have hl : xs.length < f := by simpa using h
      by_cases hx : x = 61
      · subst hx
        simp only [a2b64Run, a2bLoop, cfg_padded, cfg_strict, cfg_ig, ign, beq_self_eq_true, Bool.and_true,
          Bool.true_and, if_true, Bool.or_false, ite_true, decide_true]
        split
        · rw [ih _ _ hl]; exact a2bLoop_i strict _ _ _ _
        · split
          · rw [ih _ _ hl]; exact a2bLoop_i strict _ _ _ _
          · rfl
      · have hne : (x == 61) = false := by simpa using hx
        simp only [a2b64Run, a2bLoop, cfg_padded, cfg_strict, cfg_ig, cfg_tbl, ign, hne, Bool.and_false, Bool.true_and,
          Bool.false_eq_true, if_false, revT64, if_neg hx, Bool.not_false, Bool.and_true]
        split
        · split
          · rfl
          · rw [ih _ _ hl]; exact a2bLoop_i _ _ _ _ _
        · by_cases hp : st.pads ≠ 0 ∧ strict = true
          · rw [if_pos (by simpa using hp), if_pos hp]
          · rw [if_neg (by simpa using hp), if_neg hp]
            split
            · rename_i hq
              obtain ⟨q, p, l, o⟩ := st
              simp only at hq
              subst hq
              simp only [decStep]
              have hf := fast_len (revT b64Alpha (some 61)) xs.length xs (o ++ [(l * 64 + a2bChar x) % 256]) (Nat.le_refl _)
              rw [ih _ _ (by omega), a2bLoop_i strict xs _ 0,
                fast_loop strict xs.length xs _ (Nat.le_refl _) 0]
            · rw [ih _ _ hl]; exact a2bLoop_i _ _ _ _ _

/-- `a2b_base64` with default options is the specification. -/
theorem a2b64Core_eq (strict : Bool) (s : List Nat) : a2b64Core (cfg64 strict) false s = a2bBase64Bytes strict s := by
  have hf := fast_len (revT b64Alpha (some 61)) s.length s [] (Nat.le_refl _)
  have h1 : a2b64Run (cfg64 strict) (s.length + 1) (fast64 (revT b64Alpha (some 61)) s []).1
      { out := (fast64 (revT b64Alpha (some 61)) s []).2 } = a2bLoop strict s 0 {} := by
    rw [run_eq strict _ _ _ (by omega)]
    exact (fast_loop strict s.length s [] (Nat.le_refl _) 0).symm
  simp only [a2b64Core, a2bBase64Bytes, cfg_tbl, cfg_padded]
  rw [h1]
  cases a2bLoop strict s 0 {} with
  | error e => rfl
  | ok st => simp [bind, Except.bind, pure, Except.pure]

/-- `binascii.a2b_base64(d, strict_mode=s)` is the specification, for any argument. -/
theorem a2bB64_eq (strict : Bool) (d : Data) :
    a2bB64 d (some strict) true .absent none false = a2bBase64 strict d := by
  simp only [a2bB64, a2bBase64, alphaDec, bufOpt, decTable, bind, Except.bind, pure, Except.pure]
  cases asciiBuffer d with
  | error e => rfl
  | ok s =>
    simp only [Option.getD_some, Option.isNone_none, Bool.not_eq_true', Bool.or_true, if_true]
    have := a2b64Core_eq strict s
    simp only [cfg64] at this
    simpa using this

/-! ### The encoder -/

theorem chars64 : ∀ v, v < 64 → b64Alpha.getD v 0 = b2aChar v := by decide +kernel

/-- `pads` of `binascii_b2a_base64_impl`. -/
def pads64 (n : Nat) : Nat := (3 - n % 3) % 3 * 4 / 3

theorem pads64_step (n : Nat) : pads64 (n + 3) = pads64 n := by
  have : (n + 3) % 3 = n % 3 := by omega
  simp only [pads64, this]

/-- The fast path and the tail write what the bit loop writes. -/
theorem enc_c : ∀ (n : Nat) (d : List Nat), d.length ≤ n → (∀ x ∈ d, x < 256) → ∀ left,
    (fastEnc64 b64Alpha d).1 ++ tail64 b64Alpha (fastEnc64 b64Alpha d).2 ++ List.replicate (pads64 d.length) 61 = enc d left := by
  intro n
  induction n with
  | zero =>
    intro d h _ left
    have : d = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rfl
  | succ n ih =>
    intro d h hb left
    match d, h, hb with
    | [], _, _ => rfl
    | [a], _, hb =>
      have ha : a < 256 := hb a (by simp)
      have h1 := L_low1 left a ha
      have he : enc [a] left = [b2aChar (L a left / 4 % 64), b2aChar (L a left % 4 * 16), 61, 61] := rfl
      rw [he]
      generalize L a left = l1 at h1
      have e1 : l1 / 4 % 64 = a / 4 % 64 := by omega
      have e2 : l1 % 4 * 16 = a * 16 % 64 := by omega
      rw [e1, e2]
      have q1 : a / 4 % 64 < 64 := by omega
      have q2 : a * 16 % 64 < 64 := by omega
      simp [fastEnc64, tail64, pads64]
      exact ⟨chars64 _ q1, chars64 _ q2⟩
    | [a, b], _, hb =>
      have ha : a < 256 := hb a (by simp)
      have hb' : b < 256 := hb b (by simp)
      have h1 := L_low1 left a ha
      have h2 := L_low2 _ b a h1 hb'
      have he : enc [a, b] left = [b2aChar (L a left / 4 % 64), b2aChar (L b (L a left) / 16 % 64),
           b2aChar (L b (L a left) % 16 * 4), 61] := rfl
      rw [he]
      generalize L b (L a left) = l2 at h2
      generalize L a left = l1 at h1
      have e1 : l1 / 4 % 64 = (a * 256 + b) / 2 ^ 10 % 64 := by omega
      have e2 : l2 / 16 % 64 = (a * 256 + b) / 2 ^ 4 % 64 := by omega
      have e3 : l2 % 16 * 4 = (a * 256 + b) * 4 % 64 := by omega
      rw [e1, e2, e3]
      have q1 : (a * 256 + b) / 2 ^ 10 % 64 < 64 := by omega
      have q2 : (a * 256 + b) / 2 ^ 4 % 64 < 64 := by omega
      have q3 : (a * 256 + b) * 4 % 64 < 64 := by omega
      simp [fastEnc64, tail64, pads64]
      exact ⟨chars64 _ q1, chars64 _ q2, chars64 _ q3⟩
    | a :: b :: c :: r, h, hb =>
      have ha : a < 256 := hb a (by simp)
      have hb' : b < 256 := hb b (by simp)
      have hc : c < 256 := hb c (by simp)
      rw [enc_three a b c ha hb' hc]
      have hr := ih r (by simp at h; omega) (fun x hx => hb x (by simp [hx])) (L c (L b (L a left)))
      generalize hv : a * 65536 + b * 256 + c = v
      have e1 : v / 2 ^ 18 % 64 = a / 4 := by omega
      have e2 : v / 2 ^ 12 % 64 = a % 4 * 16 + b / 16 := by omega
      have e3 : v / 2 ^ 6 % 64 = b % 16 * 4 + c / 64 := by omega
      have e4 : v % 64 = c % 64 := by omega
      have hstep : fastEnc64 b64Alpha (a :: b :: c :: r) =
          ([b64Alpha.getD (v / 2 ^ 18 % 64) 0, b64Alpha.getD (v / 2 ^ 12 % 64) 0, b64Alpha.getD (v / 2 ^ 6 % 64) 0,
            b64Alpha.getD (v % 64) 0] ++ (fastEnc64 b64Alpha r).1, (fastEnc64 b64Alpha r).2) := by
        rw [fastEnc64, hv]
      rw [hstep, e1, e2, e3, e4, chars64 _ (by omega), chars64 _ (by omega), chars64 _ (by omega), chars64 _ (by omega)]
      have hl : (a :: b :: c :: r).length = r.length + 3 := by simp
      rw [hl, pads64_step, ← hr]
      simp [List.append_assoc]

/-- `b2a_base64` with default options is the specification, on bytes. -/
theorem b2a64Core_eq (d : List Nat) (hd : ∀ x ∈ d, x < 256) (nl : Bool) :
    b2a64Core b64Alpha d true 0 nl = b2aBase64 d nl := by
  have h := enc_c d.length d (Nat.le_refl _) hd 0
  have e : b2aBase64 d nl = enc d 0 ++ (if nl then [10] else []) := by
    simp [b2aBase64, enc]
  rw [e, ← h]
  cases nl <;> simp [b2a64Core, pads64, List.append_assoc]

theorem b2aB64_eq (d : List Nat) (hd : ∀ x ∈ d, x < 256) (nl : Bool) :
    b2aB64 (.bytes d) true 0 nl none = .ok (b2aBase64 d nl) := by
  simp only [b2aB64, bufData, sizeT, bufOpt, encTable, bind, Except.bind, pure, Except.pure]
  simp [b2a64Core_eq d hd nl]

/-! ### The statements, on the C functions -/

/-- `a2b_base64(b2a_base64(d, newline=False), strict_mode=s) == d`, for every `bytes` value `d` and both
modes, through the fast paths. The only hypothesis is that `d` holds bytes. -/
def Base64RoundTripC : Prop :=
  ∀ (strict : Bool) (d out : List Nat), (∀ x ∈ d, x < 256) → b2aB64 (.bytes d) true 0 false none = .ok out →
    a2bB64 (.bytes out) (some strict) true .absent none false = .ok d

theorem base64RoundTripC_proven : Base64RoundTripC := by
  intro strict d out hd h
  rw [b2aB64_eq d hd] at h
  cases h
  rw [a2bB64_eq]
  simpa [a2bBase64, asciiBuffer, bind, Except.bind] using base64RoundTrip_proven strict d hd

/-- Non-alphabet bytes do not affect the default decoding, including its errors and their messages:
they are "discarded prior to the padding check". -/
def LenientIgnoresC : Prop :=
  ∀ s : List Nat, a2bB64 (.bytes (s.filter keepByte)) (some false) true .absent none false =
    a2bB64 (.bytes s) (some false) true .absent none false

theorem lenientIgnoresC_proven : LenientIgnoresC := by
  intro s
  rw [a2bB64_eq, a2bB64_eq]
  simpa [a2bBase64, asciiBuffer, bind, Except.bind] using lenientIgnoresNonAlphabet_proven s

/-- `strict_mode=True` only rejects: whatever it accepts, the default mode accepts with the same result. -/
def StrictImpliesLenientC : Prop :=
  ∀ (s r : List Nat), a2bB64 (.bytes s) (some true) true .absent none false = .ok r →
    a2bB64 (.bytes s) (some false) true .absent none false = .ok r

theorem strictImpliesLenientC_proven : StrictImpliesLenientC := by
  intro s r h
  rw [a2bB64_eq] at h ⊢
  simp only [a2bBase64, asciiBuffer, bind, Except.bind] at h ⊢
  exact strictImpliesLenient_proven s r h

/-- `len(b2a_base64(d, newline=False))` is `4 * ceil(len(d) / 3)`. -/
def B2aLengthC : Prop :=
  ∀ d out : List Nat, (∀ x ∈ d, x < 256) → b2aB64 (.bytes d) true 0 false none = .ok out →
    out.length = (d.length + 2) / 3 * 4

theorem b2aLengthC_proven : B2aLengthC := by
  intro d out hd h
  rw [b2aB64_eq d hd] at h
  cases h
  exact b2aLength_proven d hd

/-- `unhexlify(hexlify(d)) == d` for every `bytes` value, whatever `ignorechars` holds, since every
digit is read as a digit before `ignorechars` is looked at. -/
def HexRoundTripC : Prop :=
  ∀ (d ig : List Nat), (∀ x ∈ d, x < 256) → a2bHexI (.bytes (b2aHex d)) (.bytes ig) = .ok d

theorem hex_digits : ∀ v, v < 256 → digitValue (hexDigit (v / 16)) = v / 16 ∧ digitValue (hexDigit (v % 16)) = v % 16 := by
  decide +kernel

theorem hexIg_loop (ig : Option (List Nat)) : ∀ (d out : List Nat), (∀ x ∈ d, x < 256) →
    a2bHexIg ig (b2aHex d) none out = .ok (out ++ d) := by
  intro d
  induction d with
  | nil => intro out _; simp [b2aHex, a2bHexIg]
  | cons x r ih =>
    intro out h
    have hx : x < 256 := h x (by simp)
    obtain ⟨h1, h2⟩ := hex_digits x hx
    have e : (x / 16) * 16 + x % 16 = x := by omega
    simp only [b2aHex, a2bHexIg, h1, h2]
    rw [if_neg (by omega), if_neg (by omega), e, ih _ (fun y hy => h y (by simp [hy]))]
    simp

theorem hexRoundTripC_proven : HexRoundTripC := by
  intro d ig hd
  simp only [a2bHexI, asciiBuffer, bufData, bind, Except.bind]
  simpa using hexIg_loop _ d [] hd

/-- `b64decode(b64encode(d), validate=v) == d` for every `bytes` value and both modes. -/
def B64ModuleRoundTripC : Prop :=
  ∀ (validate : Bool) (d out : List Nat), (∀ x ∈ d, x < 256) → pyB64encode (.bytes d) none true 0 = .ok out →
    pyB64decode (.bytes out) none (some validate) true none false = .ok d

theorem b64ModuleRoundTripC_proven : B64ModuleRoundTripC := by
  intro validate d out hd h
  have h' : b2aB64 (.bytes d) true 0 false none = .ok out := h
  have e : pyB64decode (.bytes out) none (some validate) true none false =
      a2bB64 (.bytes out) (some validate) true .absent none false := by
    simp [pyB64decode, bytesFromDecodeData, a2bB64, bind, Except.bind, bufOpt, bufData, pure, Except.pure]
  rw [e]
  exact base64RoundTripC_proven validate d out hd h'

end PyLean.TextLibs.Binascii
