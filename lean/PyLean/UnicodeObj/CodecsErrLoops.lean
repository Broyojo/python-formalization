import PyLean.UnicodeObj.CodecsErrBase

/-!
The loops of `surrogatepass` and `surrogateescape` against the codec-loop model of
`CodecHandlers.lean`.
-/

namespace PyLean.UnicodeObj.Codecs

open PyLean PyLean.UnicodeObj

theorem lt256_or {x y : Nat} (hx : x < 256) (hy : y < 256) : x ||| y < 256 :=
  Nat.or_lt_two_pow (n := 8) hx hy

theorem surrogate_lt {ch : Nat} (hs : isSurrogate ch = true) : 0xD800 ≤ ch ∧ ch ≤ 0xDFFF := by
  simp [isSurrogate] at hs; omega

/-- The bytes the handler writes for one surrogate are those of the codec-loop model. -/
theorem passBytes_eq (code : EncCode) (ch : Nat) (hs : isSurrogate ch = true) :
    passBytes code ch = surrogatePassBytes code ch := by
  have hlt := surrogate_lt hs
  cases code
  · simp only [passBytes, surrogatePassBytes]
    have a1 : (0xe0 ||| (ch >>> 12)) < 256 :=
      lt256_or (by decide) (by rw [Nat.shiftRight_eq_div_pow]; omega)
    have a2 : (0x80 ||| ((ch >>> 6) &&& 0x3f)) < 256 :=
      lt256_or (by decide) (by have := Nat.and_le_right (n := ch >>> 6) (m := 0x3f); omega)
    have a3 : (0x80 ||| (ch &&& 0x3f)) < 256 :=
      lt256_or (by decide) (by have := Nat.and_le_right (n := ch) (m := 0x3f); omega)
    rw [Nat.mod_eq_of_lt a1, Nat.mod_eq_of_lt a2, Nat.mod_eq_of_lt a3]
  all_goals simp [passBytes, surrogatePassBytes, Nat.shiftRight_eq_div_pow]

theorem or_shift (x y k : Nat) (hy : y < 2 ^ k) : x <<< k ||| y = x * 2 ^ k + y := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt hy, Nat.shiftLeft_eq]

/-- The code unit the handler reads is that of the codec-loop model, when enough bytes are
left. -/
theorem passRead_eq (code : EncCode) (p : List Nat) (hl : code.bytelength ≤ p.length)
    (hb : ∀ x ∈ p, x < 256) : passRead code p = surrogatePassRead code p := by
  cases code
  · rcases p with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
    all_goals simp [EncCode.bytelength] at hl
    simp [passRead, surrogatePassRead, and_assoc]
  · rcases p with _ | ⟨a, _ | ⟨b, r⟩⟩
    all_goals simp [EncCode.bytelength] at hl
    have ha := hb a (by simp)
    simp only [passRead, surrogatePassRead, List.getD_cons_zero, List.getD_cons_succ]
    rw [or_shift b a 8 (by omega)]
  · rcases p with _ | ⟨a, _ | ⟨b, r⟩⟩
    all_goals simp [EncCode.bytelength] at hl
    have hb' := hb b (by simp)
    simp only [passRead, surrogatePassRead, List.getD_cons_zero, List.getD_cons_succ]
    rw [or_shift a b 8 (by omega)]
  · rcases p with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, r⟩⟩⟩⟩
    all_goals simp [EncCode.bytelength] at hl
    have ha := hb a (by simp)
    have hb' := hb b (by simp)
    have hc := hb c (by simp)
    simp only [passRead, surrogatePassRead, List.getD_cons_zero, List.getD_cons_succ]
    rw [Nat.or_assoc, Nat.or_assoc, or_shift b a 8 (by omega),
      or_shift c (b * 2 ^ 8 + a) 16 (by omega), or_shift d (c * 2 ^ 16 + (b * 2 ^ 8 + a)) 24 (by omega)]
    omega
  · rcases p with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, r⟩⟩⟩⟩
    all_goals simp [EncCode.bytelength] at hl
    have hb' := hb b (by simp)
    have hc := hb c (by simp)
    have hd := hb d (by simp)
    simp only [passRead, surrogatePassRead, List.getD_cons_zero, List.getD_cons_succ]
    rw [Nat.or_assoc, Nat.or_assoc, or_shift c d 8 (by omega),
      or_shift b (c * 2 ^ 8 + d) 16 (by omega), or_shift a (b * 2 ^ 16 + (c * 2 ^ 8 + d)) 24 (by omega)]
    omega
  · rfl

/-- The write loop of `surrogatepass` (codecs.c:1262-1302) fails exactly when a character of
the range is not a surrogate. -/
theorem passWrite_eq (code : EncCode) : ∀ l : List Nat,
    passWrite code l = if l.all isSurrogate then .ok (l.flatMap (passBytes code)) else .error .reraise
  | [] => rfl
  | ch :: cs => by
    simp only [passWrite, List.all_cons]
    by_cases hs : isSurrogate ch = true
    · simp only [hs, Bool.not_true, Bool.true_and, Bool.false_eq_true, if_false]
      rw [passWrite_eq code cs]
      cases cs.all isSurrogate <;> simp [bind, Except.bind, pure, Except.pure, List.flatMap_cons]
    · have : isSurrogate ch = false := by simpa using hs
      simp [this]

/-- The write loop of `surrogateescape` (codecs.c:1434-1444). -/
theorem escWrite_eq : ∀ l : List Nat,
    escWrite l = if l.all (fun c => decide (0xdc80 ≤ c) && decide (c ≤ 0xdcff))
      then .ok (l.map (· - 0xdc00)) else .error .reraise
  | [] => rfl
  | ch :: cs => by
    simp only [escWrite, List.all_cons]
    by_cases h : ch < 0xdc80 ∨ ch > 0xdcff
    · have : (decide (0xdc80 ≤ ch) && decide (ch ≤ 0xdcff)) = false := by
        simp; omega
      simp [h, this]
    · have : (decide (0xdc80 ≤ ch) && decide (ch ≤ 0xdcff)) = true := by
        simp; omega
      simp only [h, if_false, this, Bool.true_and]
      rw [escWrite_eq cs]
      split <;> simp [bind, Except.bind, pure, Except.pure]

/-- The consume loop of `surrogateescape` (codecs.c:1466-1473) is `escapeRun` shifted. -/
theorem escConsume_eq : ∀ (k : Nat) (l : List Nat), escConsume k l = (escapeRun k l).map (· + 0xdc00)
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, b :: bs => by
    simp only [escConsume, escapeRun]
    split
    · rfl
    · rw [escConsume_eq k bs]; simp [Nat.add_comm]

theorem escapeRun_take : ∀ (k m : Nat) (l : List Nat), escapeRun k (l.take m) = escapeRun (min k m) l
  | 0, _, _ => by simp [escapeRun]
  | _ + 1, 0, l => by simp [escapeRun]
  | k + 1, m + 1, [] => by simp [escapeRun]
  | k + 1, m + 1, b :: bs => by
    have : min (k + 1) (m + 1) = min k m + 1 := by omega
    rw [this, List.take_succ_cons]
    simp only [escapeRun]
    split
    · rfl
    · rw [escapeRun_take k m bs]

end PyLean.UnicodeObj.Codecs
