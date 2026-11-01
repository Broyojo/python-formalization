import PyLean.TextLibs.ReApiProps

/-! Laws of the small helpers of `re`, each set against another helper or stated bit by bit. -/

namespace PyLean.TextLibs.Re

open PyLean

set_option linter.unusedSimpArgs false

theorem complement_bit (x i : Nat) (h : x < 2 ^ 16) :
    (2 ^ 16 - 1 - x).testBit i = (decide (i < 16) && !x.testBit i) := by
  have e : 2 ^ 16 - 1 - x = 2 ^ 16 - (x + 1) := by omega
  rw [e, Nat.testBit_two_pow_sub_succ h]

/-- `_combine_flags`, every bit of it: `del_flags` clears, `add_flags` sets, and an `add_flags` that
holds a type flag first clears the old type flags, so `(?a:...)` inside `(?u:...)` does not leave
both. The hypotheses are the size of the flag words, which the parser keeps below `2^16`. -/
def CombineFlagsLaw : Prop :=
  ∀ (f a d i : Nat), f < 2 ^ 16 → a < 2 ^ 16 → d < 2 ^ 16 → i < 16 →
    (combineFlags f a d).testBit i =
      (!d.testBit i && (a.testBit i ||
        (f.testBit i && (decide ((a &&& TYPE_FLAGS) = 0) || !TYPE_FLAGS.testBit i))))

theorem combineFlagsLaw_proven : CombineFlagsLaw := by
  intro f a d i hf ha hd hi
  have ht : TYPE_FLAGS < 2 ^ 16 := by decide
  unfold combineFlags
  simp only [Nat.testBit_and, Nat.testBit_or, complement_bit _ i hd, decide_eq_true hi, Bool.true_and]
  by_cases h : (a &&& TYPE_FLAGS) = 0
  · simp [h]
    cases d.testBit i <;> simp [Bool.and_comm, Bool.or_comm]
  · have h2 : ((a &&& TYPE_FLAGS) ≠ 0) := h
    rw [if_pos h2]
    simp only [Nat.testBit_and, complement_bit _ i ht, decide_eq_true hi, Bool.true_and]
    simp [h]
    cases d.testBit i <;> simp [Bool.and_comm, Bool.or_comm]

/-- `_sre.ascii_iscased` is what its name says, by the two case mappings: a character is cased when
one of them moves it. And the two mappings undo each other on letters, for every code point. -/
def AsciiCaseLaw : Prop :=
  ∀ c : Nat,
    asciiIscased c = (lowerAscii c != c || upperLocale c != c) ∧
    lowerAscii (upperLocale c) = lowerAscii c ∧
    upperLocale (lowerAscii c) = upperLocale c ∧
    lowerAscii (lowerAscii c) = lowerAscii c

theorem asciiCaseLaw_proven : AsciiCaseLaw := by
  intro c
  unfold asciiIscased isLetter lowerAscii upperLocale
  by_cases h1 : 65 ≤ c ∧ c ≤ 90
  · have h3 : ¬(97 ≤ c ∧ c ≤ 122) := by omega
    have h4 : c < 128 := by omega
    have h5 : ¬(c + 32 = c) := by omega
    have h6 : (97 ≤ c + 32 ∧ c + 32 ≤ 122) := by omega
    have h7 : ¬(65 ≤ c + 32 ∧ c + 32 ≤ 90) := by omega
    simp only [h1, h3, h6, h7, if_true, if_false, and_self]
    simp [h4, h1.1, h1.2, h5] <;> omega
  · by_cases h2 : 97 ≤ c ∧ c ≤ 122
    · have h4 : c < 128 := by omega
      have h5 : ¬(c - 32 = c) := by omega
      have h6 : (65 ≤ c - 32 ∧ c - 32 ≤ 90) := by omega
      have h7 : ¬(97 ≤ c - 32 ∧ c - 32 ≤ 122) := by omega
      simp only [h1, h2, h6, h7, if_true, if_false, and_self]
      simp [h4, h2.1, h2.2, h5] <;> omega
    · simp only [h1, h2, if_false, bne_self_eq_false, Bool.or_false, and_self]
      have h3 : (decide (c < 128) && ((decide (97 ≤ c) && decide (c ≤ 122)) ||
          (decide (65 ≤ c) && decide (c ≤ 90)))) = false := by
        simp only [Bool.and_eq_false_iff, Bool.or_eq_false_iff, decide_eq_false_iff_not]
        omega
      simpa using h3

/-- `char_loc_ignore` in the C locale: a letter of either case matches itself and its other case, and
nothing else, which is why `LITERAL_LOC_IGNORE` keeps the pattern's character as written. -/
def CharLocIgnoreLaw : Prop :=
  ∀ (p c : Nat),
    (97 ≤ p → p ≤ 122 → (charLocIgnore p c = true ↔ c = p ∨ c = p - 32)) ∧
    (65 ≤ p → p ≤ 90 → (charLocIgnore p c = true ↔ c = p ∨ c = p + 32))

theorem charLocIgnoreLaw_proven : CharLocIgnoreLaw := by
  intro p c
  constructor
  · intro h1 h2
    simp only [charLocIgnore, lowerLocale, lowerAscii, upperLocale, Bool.or_eq_true, beq_iff_eq]
    split <;> split <;> omega
  · intro h1 h2
    simp only [charLocIgnore, lowerLocale, lowerAscii, upperLocale, Bool.or_eq_true, beq_iff_eq]
    split <;> split <;> omega

/-- `sre_category`: under any flags, a category and its negation answer opposite ways for every
character, which is what `CH_NEGATE` and the `[\s\S]` shortcut of `_optimize_charset` rely on. -/
def CategoryNegation : Prop :=
  ∀ (flags c : Nat) (k : Cat),
    sreCategory (catCode flags k) c = !sreCategory (catCode flags (chNegate k)) c

theorem categoryNegation_proven : CategoryNegation := by
  intro flags c k
  unfold catCode
  cases hl : hasFlag flags FLAG_LOCALE <;> cases hu : hasFlag flags FLAG_UNICODE <;> cases k <;>
    simp [chNegate, sreCategory]

/-- `_compile`, on what it is given: a compiled pattern with flags is `ValueError`, whatever the flags;
a compiled pattern without them goes through; anything but a string or a pattern is `TypeError`, for
any flags; and a string compiles under its own kind. The caches only return an earlier result. -/
def ReCompileLaw : Prop :=
  ∀ (p : Pat) (s : List Nat) (flags : Nat),
    (flags ≠ 0 → reCompile (.compiled p) flags =
      .error (.valueError "cannot process flags argument with a compiled pattern")) ∧
    reCompile (.compiled p) 0 = .ok p ∧
    reCompile .other flags = .error (.typeError "first argument must be string or compiled pattern") ∧
    reCompile (.text s) flags = compilePat true s flags ∧
    reCompile (.bytes s) flags = compilePat false s flags

theorem reCompileLaw_proven : ReCompileLaw := by
  intro p s flags
  refine ⟨fun h => ?_, ?_, rfl, rfl, rfl⟩
  · simp [reCompile, h]
  · simp [reCompile]

/-- The string `re.escape(s)` compiles to matches `s` and nothing else, with or without `VERBOSE`. -/
def EscapeRoundTrip : Prop :=
  ∀ (s : List Nat) (flags : Nat), (flags = 0 ∨ flags = FLAG_VERBOSE) →
    (∀ c ∈ s, c < 0x110000) → ∃ p, parse true (escape s) flags = .ok p ∧ p.p = s.map .literal

end PyLean.TextLibs.Re
