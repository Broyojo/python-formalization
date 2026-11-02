import PyLean.Pickle.TextRoundtrip
import PyLean.Pickle.LongShortest

/-!
The text-line and `save_long` agreements with hypotheses that exclude exactly
the refuted inputs: a line or int both twins reject stays inside the statement.
-/

namespace PyLean.Pickle

open PyLean

theorem takeWhile_len_eq {l : Bytes} (h : (l.takeWhile (· ≠ 0)).length = l.length) :
    (0 : UInt8) ∉ l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases ha : a = 0
    · subst ha
      rw [List.takeWhile_cons_of_neg (by simp)] at h
      simp at h
    · rw [List.takeWhile_cons_of_pos (by simpa using ha)] at h
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      intro m
      rcases List.mem_cons.mp m with e | e
      · exact ha e.symm
      · exact ih h e

/-- `int(b)` raises for every bytes object containing NUL. -/
theorem pyIntOfBytes_nul (b : Bytes) (h : (0 : UInt8) ∈ b) : isErr (pyIntOfBytes b) = true := by
  unfold pyIntOfBytes
  dsimp only
  split
  · have : ¬ (b.takeWhile (· ≠ 0)).length = b.length := fun e => takeWhile_len_eq e h
    rw [if_neg this]
    rfl
  · rfl
  · rfl

/-- The lines where only C accepts past the digit limit: its strtol path takes
the line, which has more than 4300 digits. -/
def FastOverLimit (body : Bytes) : Prop :=
  ∃ x c, strtol (body ++ [nl]) = (x, c, false) ∧
    ((body ++ [nl]).getD c 0 = nl ∨ (body ++ [nl]).getD c 0 = 0) ∧
    (body.filter isDigit).length > maxStrDigits

/-- Every complete `INT` line outside the two refuted sets: lines with NUL that
C accepts, and lines past the digit limit that C's strtol path accepts. Lines
both twins reject stay in. -/
def IntLineTwinsPrecise : Prop :=
  ∀ body : Bytes, nl ∉ body →
    ((0 : UInt8) ∈ body → isErr (cLoadIntLine (body ++ [nl])) = true) → ¬ FastOverLimit body →
    SameOutcome (cLoadIntLine (body ++ [nl])) (pyLoadIntLine (body ++ [nl]))

theorem intLineTwinsPrecise_proven : IntLineTwinsPrecise := by
  intro body hnl hc hf
  by_cases hz : (0 : UInt8) ∈ body
  · have h1 := hc hz
    have hm : (0 : UInt8) ∈ body ++ [nl] := List.mem_append_left _ hz
    have h2 := pyIntOfBytes_nul _ hm
    have h3 : ¬ body ++ [nl] = [0x30, 0x30, nl] := by
      intro e; rw [e] at hm; revert hm; decide
    have h4 : ¬ body ++ [nl] = [0x30, 0x31, nl] := by
      intro e; rw [e] at hm; revert hm; decide
    unfold pyLoadIntLine
    rw [if_neg h3, if_neg h4]
    cases hp : pyIntOfBytes (body ++ [nl]) with
    | ok v => rw [hp] at h2; simp [isErr] at h2
    | error e =>
      cases hq : cLoadIntLine (body ++ [nl]) with
      | ok v => rw [hq] at h1; simp [isErr] at h1
      | error e' => exact trivial
  · exact intLineTwinsNarrow_proven body hnl hz (fun x c h1 h2 => by
      apply Nat.le_of_not_gt
      intro h3
      exact hf ⟨x, c, h1, h2, h3⟩)

/-- Every complete `LONG` line, except lines with NUL that C accepts. -/
def LongLineTwinsPrecise : Prop :=
  ∀ body : Bytes, nl ∉ body → ((0 : UInt8) ∈ body → isErr (cLoadLongLine (body ++ [nl])) = true) →
    SameOutcome (cLoadLongLine (body ++ [nl])) (pyLoadLongLine (body ++ [nl]))

theorem longLineTwinsPrecise_proven : LongLineTwinsPrecise := by
  intro body hnl hc
  by_cases hz : (0 : UInt8) ∈ body
  · have h1 := hc hz
    have hval : (0 : UInt8) ∈ (let val := (body ++ [nl]).dropLast
        if val ≠ [] ∧ val.getLast? = some 0x4c then val.dropLast else val) := by
      have e : (body ++ [nl]).dropLast = body := by simp
      simp only [e]
      split
      · rename_i hl
        have hne := hl.1
        obtain ⟨b, d, hb⟩ : ∃ b d, body = b ++ [d] := ⟨_, _, (List.dropLast_concat_getLast hne).symm⟩
        subst hb
        have hd : d = 0x4c := by simpa using hl.2
        subst hd
        simp only [List.dropLast_concat]
        rcases List.mem_append.mp hz with m | m
        · exact m
        · simp at m
      · exact hz
    have h2 := pyIntOfBytes_nul _ hval
    have h3 : isErr (pyLoadLongLine (body ++ [nl])) = true := h2
    cases hp : pyLoadLongLine (body ++ [nl]) with
    | ok v => rw [hp] at h3; simp [isErr] at h3
    | error e =>
      cases hq : cLoadLongLine (body ++ [nl]) with
      | ok v => rw [hq] at h1; simp [isErr] at h1
      | error e' => exact trivial
  · exact longLineTwinsNoNul_proven body hnl hz

/-- The exponent of the one int where C refuses and Python encodes:
`8 * (2**31 - 1) - 1`. -/
def long4Exp : Nat := 17179869175

/-- `-(2**long4Exp)`, the int of the refuted `SaveLongTwinsAgree`. Noncomputable
because a compiled closed term would run when the module initializes, and the
power panics every program that links it (`pydiff`). Only statements use it. -/
noncomputable def long4Edge : Int := -((2 : Int) ^ long4Exp)

theorem k_le_log (K b l : Nat) (hK : K + 1 = 17179869176) (h : b ≥ 8 * 2147483647) (h2 : b = l + 1) :
    K ≤ l := by omega
theorem k_mono (K n : Nat) (hK : K + 1 = 17179869176) (h : n ≤ 2147483647) : 8 * n - 1 ≤ K := by omega
theorem k_32 (K : Nat) (hK : K + 1 = 17179869176) : 32 ≤ K := by omega

theorem sameOutcome_refl {α : Type} (r : Py α) : SameOutcome r r := by
  cases r <;> simp [SameOutcome]

theorem saveLong_aux (K : Nat) (hK : K + 1 = 17179869176) (p : Nat) (x : Int) (hp : p ≤ 5)
    (hx : x ≠ -((2 : Int) ^ K)) : SameOutcome (cSaveLong p x) (pySaveLong p x) := by
  have hA := fun b l h h2 => k_le_log K b l hK h h2
  have hB := fun n h => k_mono K n hK h
  have h32 := k_32 K hK
  clear hK
  by_cases hs : bitLength x.natAbs / 8 + 1 ≤ 0x7fffffff
  · rw [saveLongTwinsAgreeSized_proven p x hp hs]
    exact sameOutcome_refl _
  have hbl : bitLength x.natAbs ≥ 8 * 2147483647 := by omega
  have hne : x.natAbs ≠ 0 := by
    intro h; rw [h] at hbl; simp [bitLength] at hbl
  have hge : 2 ^ K ≤ x.natAbs := by
    have h1 := Nat.log2_self_le hne
    have h2 : bitLength x.natAbs = Nat.log2 x.natAbs + 1 := by simp [bitLength, hne]
    exact Nat.le_trans (Nat.pow_le_pow_right (by omega) (hA _ _ hbl h2)) h1
  have hcast : (2 : Int) ^ K = ((2 ^ K : Nat) : Int) := by simp
  have hpos : (2 ^ 32 : Nat) ≤ 2 ^ K := Nat.pow_le_pow_right (by omega) h32
  have hnf : ¬ (-0x80000000 ≤ x ∧ x ≤ 0x7fffffff) := by omega
  have hpy1 : ¬ (p ≥ 1 ∧ x ≥ 0 ∧ x ≤ 255) := by omega
  have hpy2 : ¬ (p ≥ 1 ∧ x ≥ 0 ∧ x ≤ 65535) := by omega
  have hpy3 : ¬ (p ≥ 1 ∧ -0x80000000 ≤ x ∧ x ≤ 0x7fffffff) := by omega
  unfold cSaveLong pySaveLong
  dsimp only
  rw [if_neg hnf, if_neg hpy1, if_neg hpy2, if_neg hpy3]
  by_cases hp2 : p ≥ 2
  · rw [if_pos hp2, if_pos hp2]
    have hc : cLongBytes x = .error (.overflowError "int too large to pickle") := by
      unfold cLongBytes; dsimp only; rw [if_pos (by omega)]
    rw [hc]
    -- Python: the encoding has at least 2**31 bytes
    have henc : (encodeLong x).length > 2147483647 := by
      apply Nat.lt_of_not_le
      intro hle
      have hrt := decodeEncodeLong_proven x
      generalize hE : encodeLong x = E at hrt hle
      have hnil : E ≠ [] := by
        intro h; subst h
        have : x = 0 := by rw [← hrt]; simp [decodeLong, leInt, leNat]
        subst this; simp at hne
      have hbd := leInt_bounds E hnil
      rw [show leInt E = x from hrt] at hbd
      have hmono : ((2 : Int) ^ (8 * E.length - 1)) ≤ (2 : Int) ^ K := int_two_pow_le (hB _ hle)
      apply hx
      rw [hcast] at hmono ⊢
      omega
    show SameOutcome (Except.error _) (if (encodeLong x).length < 256 then _ else _)
    rw [if_neg (by omega)]
    unfold packI32
    rw [if_neg (by omega)]
    exact trivial
  · rw [if_neg hp2, if_neg hp2, if_neg hnf]
    exact sameOutcome_refl _

/-- Whole-outcome agreement of `save_long` for every int except that one:
beyond the LONG4 limit both twins raise. -/
def SaveLongSameOutcome : Prop :=
  ∀ (p : Nat) (x : Int), p ≤ 5 → x ≠ long4Edge → SameOutcome (cSaveLong p x) (pySaveLong p x)

theorem saveLongSameOutcome_proven : SaveLongSameOutcome :=
  fun p x hp hx => saveLong_aux long4Exp rfl p x hp hx

end PyLean.Pickle
