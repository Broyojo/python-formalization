import PyLean.Pickle.ParseLemmas

/-! The narrowed `LONG` line property. -/

namespace PyLean.Pickle

open PyLean

theorem sameOutcome_parse (L v : Bytes) (hL : L.takeWhile (· ≠ 0) = v) (hv : (0 : UInt8) ∉ v) :
    SameOutcome (cLongFromLine L) (pyIntOfBytes v) := by
  unfold cLongFromLine pyIntOfBytes
  rw [hL, takeWhile_ne_zero_of_not_mem hv]
  cases h : pyLongFromString v <;> simp [SameOutcome, h]

theorem sameOutcome_parse' (L v : Bytes) (hL : pyLongFromString (L.takeWhile (· ≠ 0)) = pyLongFromString v)
    (hv : (0 : UInt8) ∉ v) :
    SameOutcome (cLongFromLine L) (pyIntOfBytes v) := by
  unfold cLongFromLine pyIntOfBytes
  dsimp only
  rw [hL, takeWhile_ne_zero_of_not_mem hv]
  cases h : pyLongFromString v <;> simp [SameOutcome, h]

/-- `LongLineTwins` for lines without NUL bytes: the C and Python `LONG`
parsers accept the same lines (with or without the trailing `L`) and return
the same value. -/
def LongLineTwinsNoNul : Prop :=
  ∀ body : Bytes, nl ∉ body → (0 : UInt8) ∉ body →
    SameOutcome (cLoadLongLine (body ++ [nl])) (pyLoadLongLine (body ++ [nl]))

theorem longLineTwinsNoNul_proven : LongLineTwinsNoNul := by
  intro body _ hz
  by_cases hnil : body = []
  · subst hnil
    simp [cLoadLongLine, pyLoadLongLine, pyIntOfBytes, pyLongFromString, lfsBase, scanDigits, skipSpace,
      SameOutcome]
  · obtain ⟨b, d, rfl⟩ : ∃ b d, body = b ++ [d] := ⟨_, _, (List.dropLast_concat_getLast hnil).symm⟩
    have hb : (0 : UInt8) ∉ b := fun m => hz (List.mem_append_left _ m)
    have hd : d ≠ 0 := fun e => hz (List.mem_append_right _ (by simp [e]))
    have hlen : ¬ (b ++ [d] ++ [nl]).length < 2 := by simp
    have hget : (b ++ [d] ++ [nl]).getD ((b ++ [d] ++ [nl]).length - 2) 0 = d := by simp
    unfold cLoadLongLine pyLoadLongLine
    rw [if_neg hlen, hget]
    have hdrop : (b ++ [d] ++ [nl]).dropLast = b ++ [d] := by simp
    rw [hdrop]
    by_cases hL : d = 0x4c
    · subst hL
      have hset : (b ++ [(0x4c : UInt8)] ++ [nl]).set ((b ++ [(0x4c : UInt8)] ++ [nl]).length - 2) 0 =
          b ++ 0 :: [nl] := by
        simp [List.set_append]
      rw [if_pos rfl, hset]
      dsimp only
      rw [if_pos ⟨by simp, by simp⟩]
      simp only [List.dropLast_concat]
      exact sameOutcome_parse _ _ (takeWhile_ne_zero_append_zero _ hb) hb
    · rw [if_neg hL]
      dsimp only
      rw [if_neg (by simp [hL])]
      apply sameOutcome_parse' _ _ _ hz
      rw [takeWhile_ne_zero_of_not_mem (by simpa [nl] using And.intro hz (by decide : (0:UInt8) ≠ 0x0a))]
      exact pyLongFromString_append_space _ (by decide)

end PyLean.Pickle
