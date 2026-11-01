import PyLean.UnicodeObj.Repr
import PyLean.UnicodeObj.TextTranslate
import PyLean.UnicodeObj.TextDedent

/-!
Properties of the text slice: case mapping, the `is*` predicates, identifiers,
`repr`/`isprintable`, the ASCII `bytes` twins.
-/

namespace PyLean.UnicodeObj

open PyLean

/-! ## Facts for ASCII, from the tables -/

theorem ascii_facts : ∀ c, c < 128 →
    (toUpperFull c = [pyToUpper c] ∧ toLowerFull c = [pyToLower c] ∧
     toTitleFull c = [pyToUpper c] ∧ toFoldedFull c = [pyToLower c] ∧
     isLowercase c = pyIsLower c ∧ isUppercase c = pyIsUpper c ∧ isTitlecase c = false ∧
     isCased c = pyIsAlpha c ∧ isAlpha c = pyIsAlpha c ∧ isDigit c = pyIsDigit c ∧
     isAlnum c = pyIsAlnum c ∧ isPrintable c = (decide (32 ≤ c) && decide (c < 127))) := by
  decide +kernel

theorem mem_ascii {s : Str} (h : isAscii s = true) {c} (hc : c ∈ s) : c < 128 := by
  simp only [isAscii, List.all_eq_true, decide_eq_true_eq] at h
  exact h c hc

/-! ## Fast path vs. general path of the case methods -/

/-- For ASCII input, `ascii_upper_or_lower` computes what the general
`do_upper`, `do_lower` and `do_casefold` compute. Quantified over every ASCII
string. -/
def CaseAsciiFastPath : Prop :=
  ∀ s : Str, isAscii s = true →
    asciiUpperOrLower false s = (doUpper s).res ∧
    asciiUpperOrLower true s = (doLower s).res ∧
    asciiUpperOrLower true s = (doCasefold s).res

theorem mapLoop_map (f : List Nat → Nat → List Nat → List Nat) (g : Nat → Nat) (s : Str)
    (hf : ∀ c, c ∈ s → ∀ b a, f b c a = [g c]) (before : List Nat) (o : CaseOut) :
    (mapLoop f before s o).res = o.res ++ s.map g := by
  induction s generalizing before o with
  | nil => simp [mapLoop]
  | cons c cs ih =>
    simp only [mapLoop, List.map_cons]
    rw [ih (fun x hx => hf x (List.mem_cons_of_mem _ hx))]
    simp [emit, hf c List.mem_cons_self]

theorem caseAsciiFastPath_proven : CaseAsciiFastPath := by
  intro s hs
  have hlow : ∀ c, c ∈ s → ∀ b a, lowerUcs4 b c a = [pyToLower c] := by
    intro c hc b a
    have h := mem_ascii hs hc
    have := (ascii_facts c h).2.1
    unfold lowerUcs4
    rw [if_neg (by omega), this]
  refine ⟨?_, ?_, ?_⟩
  · have := mapLoop_map (fun b c a => if false then lowerUcs4 b c a else toUpperFull c)
      pyToUpper s (fun c hc b a => by
        simpa using (ascii_facts c (mem_ascii hs hc)).1) [] startOut
    simpa [doUpper, doUpperOrLower, asciiUpperOrLower, startOut] using this.symm
  · have := mapLoop_map (fun b c a => if true then lowerUcs4 b c a else toUpperFull c)
      pyToLower s (fun c hc b a => by simpa using hlow c hc b a) [] startOut
    simpa [doLower, doUpperOrLower, asciiUpperOrLower, startOut] using this.symm
  · have := mapLoop_map (fun _ c _ => toFoldedFull c) pyToLower s (fun c hc b a =>
      (ascii_facts c (mem_ascii hs hc)).2.2.2.1) [] startOut
    simpa [doCasefold, asciiUpperOrLower, startOut] using this.symm

/-! ## Expansion bound and the kind of the result -/

/-- What every `do_*` keeps true. -/
def Good (o : CaseOut) (n : Nat) : Prop :=
  o.res.length ≤ 3 * n ∧ Str.Valid o.res ∧ o.maxchar = maxCharOf o.res

theorem good_mapping_spec {m : List Nat} (h : goodMapping m = true) :
    m.length ≤ 3 ∧ ∀ x ∈ m, x ≤ maxUnicode := by
  simp only [goodMapping, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.2, h.2⟩

theorem emit_good {o n} {m : List Nat} (h : Good o n) (h1 : m.length ≤ 3)
    (h2 : ∀ x ∈ m, x ≤ maxUnicode) : Good (emit o m) (n + 1) := by
  obtain ⟨a, b, c⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp only [emit, List.length_append]; omega
  · intro x hx
    simp only [emit, List.mem_append] at hx
    rcases hx with hx | hx
    · exact b x hx
    · exact h2 x hx
  · simp [emit, maxCharOf, List.foldl_append] at c ⊢
    rw [c]

/-- The condition on a per-character map. -/
def MapOk (f : List Nat → Nat → List Nat → List Nat) : Prop :=
  ∀ b c a, c ≤ maxUnicode → (f b c a).length ≤ 3 ∧ ∀ x ∈ f b c a, x ≤ maxUnicode

theorem mapLoop_good {f} (hf : MapOk f) (s : Str) (hs : Str.Valid s) (before o n)
    (h : Good o n) : Good (mapLoop f before s o) (n + s.length) := by
  induction s generalizing before o n with
  | nil => simpa [mapLoop] using h
  | cons c cs ih =>
    have hc : c ≤ maxUnicode := hs c List.mem_cons_self
    have hcs : Str.Valid cs := fun x hx => hs x (List.mem_cons_of_mem _ hx)
    simp only [mapLoop, List.length_cons]
    have := ih hcs (c :: before) _ (n + 1)
      (emit_good h (hf before c cs hc).1 (hf before c cs hc).2)
    have e : n + (cs.length + 1) = n + 1 + cs.length := by omega
    rw [e]; exact this

theorem lowerUcs4_ok : MapOk lowerUcs4 := by
  intro b c a hc
  unfold lowerUcs4
  by_cases h : c = 0x3A3
  · rw [if_pos h]
    simp only [List.length_cons, List.length_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq]
    refine ⟨by omega, ?_⟩
    unfold handleCapitalSigma
    split <;> decide
  · rw [if_neg h]
    exact good_mapping_spec (charFact_case hc).1

theorem toUpper_ok : MapOk (fun _ c _ => toUpperFull c) :=
  fun _ _ _ hc => good_mapping_spec (charFact_case hc).2.1

theorem toFolded_ok : MapOk (fun _ c _ => toFoldedFull c) :=
  fun _ _ _ hc => good_mapping_spec (charFact_case hc).2.2.2

theorem swapcase_ok : MapOk swapcaseMap := by
  intro b c a hc
  unfold swapcaseMap
  split
  · exact lowerUcs4_ok b c a hc
  · split
    · exact good_mapping_spec (charFact_case hc).2.1
    · simp only [List.length_cons, List.length_nil, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq]
      exact ⟨by omega, hc⟩

theorem start_good : Good startOut 0 := by
  refine ⟨by simp [startOut], ?_, ?_⟩
  · intro x hx; simp [startOut] at hx
  · simp [startOut, maxCharOf]

theorem titleLoop_good (s : Str) (hs : Str.Valid s) (p before o n) (h : Good o n) :
    Good (titleLoop p before s o) (n + s.length) := by
  induction s generalizing p before o n with
  | nil => simpa [titleLoop] using h
  | cons c cs ih =>
    have hc : c ≤ maxUnicode := hs c List.mem_cons_self
    have hcs : Str.Valid cs := fun x hx => hs x (List.mem_cons_of_mem _ hx)
    simp only [titleLoop, List.length_cons]
    have hm : (if p = true then lowerUcs4 before c cs else toTitleFull c).length ≤ 3 ∧
        ∀ x ∈ (if p = true then lowerUcs4 before c cs else toTitleFull c), x ≤ maxUnicode := by
      split
      · exact lowerUcs4_ok _ _ _ hc
      · exact good_mapping_spec (charFact_case hc).2.2.1
    have := ih hcs (isCased c) (c :: before) _ (n + 1) (emit_good h hm.1 hm.2)
    have e : n + (cs.length + 1) = n + 1 + cs.length := by omega
    rw [e]; exact this

/-- For every string, each `do_*` writes at most `3 * length` code points, all
valid, and reports their maximum in `*maxchar`. So `case_operation`'s buffer of
`3 * length` `Py_UCS4` cannot overflow, the `mapped[3]` arrays cannot either, and
`PyUnicode_New(newlength, maxchar)` picks the canonical kind. -/
def CaseOutputBound : Prop :=
  ∀ s : Str, Str.Valid s →
    Good (doUpper s) s.length ∧ Good (doLower s) s.length ∧ Good (doCasefold s) s.length ∧
    Good (doSwapcase s) s.length ∧ Good (doTitle s) s.length ∧ Good (doCapitalize s) s.length

theorem caseOutputBound_proven : CaseOutputBound := by
  intro s hs
  have h0 := start_good
  have lift : ∀ {o}, Good o (0 + s.length) → Good o s.length := by
    intro o h; simpa using h
  refine ⟨lift (mapLoop_good ?_ s hs [] _ 0 h0), lift (mapLoop_good ?_ s hs [] _ 0 h0),
    lift (mapLoop_good toFolded_ok s hs [] _ 0 h0), lift (mapLoop_good swapcase_ok s hs [] _ 0 h0),
    lift (titleLoop_good s hs _ _ _ 0 h0), ?_⟩
  · simpa using toUpper_ok
  · simpa using lowerUcs4_ok
  · cases s with
    | nil => exact h0
    | cons c cs =>
      have hc : c ≤ maxUnicode := hs c List.mem_cons_self
      have hcs : Str.Valid cs := fun x hx => hs x (List.mem_cons_of_mem _ hx)
      have ht := good_mapping_spec (charFact_case hc).2.2.1
      have := mapLoop_good lowerUcs4_ok cs hcs [c] _ 1 (emit_good h0 ht.1 ht.2)
      simpa [doCapitalize, Nat.add_comm] using this

/-! ## Final sigma -/

/-- `l` (nearest character first) starts with `\p{case-ignorable}*\p{cased}`. -/
def SigmaSeq (l : List Nat) : Prop :=
  ∃ ign c rest, l = ign ++ c :: rest ∧ (∀ x ∈ ign, isCaseIgnorable x = true) ∧ isCased c = true

/-- The rule in the comment of `handle_capital_sigma` (unicodeobject.c:10047-10051)
and in Table 3-17 of the Unicode Standard: the sigma is final exactly when
`\p{cased}\p{case-ignorable}*` precedes it and `\p{case-ignorable}*\p{cased}` does not
follow it. -/
def FinalSigmaRegex : Prop :=
  ∀ before after, handleCapitalSigma before after = 0x3C2 ↔ SigmaSeq before ∧ ¬ SigmaSeq after

/-- `'ʰΣ'.lower()` keeps the medial sigma: U+02B0 is both cased and
case-ignorable, and the scan stops only at characters that are not case-ignorable. -/
theorem finalSigmaRegex_refuted : ¬ FinalSigmaRegex := by
  intro h
  have hs : SigmaSeq [0x2B0] := ⟨[], 0x2B0, [], rfl, by simp, by decide⟩
  have hn : ¬ SigmaSeq [] := by
    rintro ⟨ign, c, rest, h, -, -⟩
    simp at h
  have := (h [0x2B0] []).2 ⟨hs, hn⟩
  revert this
  decide

theorem sigmaSeq_iff (l : List Nat) (h : ∀ c ∈ l, ¬ (isCased c = true ∧ isCaseIgnorable c = true)) :
    SigmaSeq l ↔ ∃ c, firstNotIgnorable l = some c ∧ isCased c = true := by
  induction l with
  | nil =>
    constructor
    · rintro ⟨ign, c, rest, h, -, -⟩; simp at h
    · rintro ⟨c, h, -⟩; simp [firstNotIgnorable] at h
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have hxs : ∀ c ∈ xs, ¬ (isCased c = true ∧ isCaseIgnorable c = true) :=
      fun c hc => h c (List.mem_cons_of_mem _ hc)
    by_cases hi : isCaseIgnorable x = true
    · have hc : isCased x ≠ true := fun e => hx ⟨e, hi⟩
      have e : firstNotIgnorable (x :: xs) = firstNotIgnorable xs := by
        simp [firstNotIgnorable, hi]
      rw [e, ← ih hxs]
      constructor
      · rintro ⟨ign, c, rest, he, hign, hcas⟩
        cases ign with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at he
          rw [he.1] at hc
          exact absurd hcas hc
        | cons y ys =>
          simp only [List.cons_append, List.cons.injEq] at he
          exact ⟨ys, c, rest, he.2, fun z hz => hign z (List.mem_cons_of_mem _ hz), hcas⟩
      · rintro ⟨ign, c, rest, he, hign, hcas⟩
        refine ⟨x :: ign, c, rest, by simp [he], ?_, hcas⟩
        intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hi
        · exact hign z hz
    · have e : firstNotIgnorable (x :: xs) = some x := by simp [firstNotIgnorable, hi]
      rw [e]
      constructor
      · rintro ⟨ign, c, rest, he, hign, hcas⟩
        cases ign with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at he
          exact ⟨x, rfl, he.1 ▸ hcas⟩
        | cons y ys =>
          simp only [List.cons_append, List.cons.injEq] at he
          exact absurd (he.1 ▸ hign y List.mem_cons_self) hi
      · rintro ⟨c, he, hcas⟩
        simp only [Option.some.injEq] at he
        subst he
        exact ⟨[], x, xs, rfl, by simp, hcas⟩

/-- The narrowed rule: with no character that is both cased and case-ignorable
around the sigma, `handle_capital_sigma` implements the regex exactly. -/
def FinalSigmaNoOverlap : Prop :=
  ∀ before after,
    (∀ c ∈ before ++ after, ¬ (isCased c = true ∧ isCaseIgnorable c = true)) →
    (handleCapitalSigma before after = 0x3C2 ↔ SigmaSeq before ∧ ¬ SigmaSeq after)

theorem finalSigmaNoOverlap_proven : FinalSigmaNoOverlap := by
  intro before after h
  rw [sigmaSeq_iff before (fun c hc => h c (List.mem_append_left _ hc)),
    sigmaSeq_iff after (fun c hc => h c (List.mem_append_right _ hc))]
  unfold handleCapitalSigma finalSigma
  cases hb : firstNotIgnorable before with
  | none => simp
  | some c =>
    cases ha : firstNotIgnorable after with
    | none => by_cases hc : isCased c = true <;> simp [hc]
    | some d =>
      by_cases hc : isCased c = true <;> by_cases hd : isCased d = true <;> simp [hc, hd]

/-! ## The `is*` predicates -/

theorem allShape_eq (p : Nat → Bool) (s : Str) :
    allShape p s = (s != [] && s.all p) := by
  match s with
  | [] => rfl
  | [c] => simp [allShape]
  | a :: b :: t => simp [allShape]

/-- The six `allShape` predicates: the one-character shortcut and the loop agree,
so each is "non-empty and every character satisfies the per-character test", and
decimal, digit and numeric strings nest, for every string. `isalnum` is the
documented disjunction of the four per-character tests. -/
def IsPredicates : Prop :=
  (∀ p s, allShape p s = true ↔ s ≠ [] ∧ ∀ c ∈ s, p c = true) ∧
  (∀ c, isAlnum c = (isAlpha c || isDecimalDigit c || isDigit c || isNumeric c)) ∧
  (∀ s : Str, Str.Valid s →
    (unicodeIsDecimal s = true → unicodeIsDigit s = true) ∧
    (unicodeIsDigit s = true → unicodeIsNumeric s = true))

theorem digit_facts {c} (h : c ≤ maxUnicode) :
    (isDecimalDigit c = true → isDigit c = true) ∧ (isDigit c = true → isNumeric c = true) := by
  have := flagFact_spec _ _ _ _ _ _ _ _ _ (flags_ok h)
  exact ⟨this.1, this.2.1⟩

theorem isPredicates_proven : IsPredicates := by
  refine ⟨?_, ?_, ?_⟩
  · intro p s
    rw [allShape_eq]
    simp [List.all_eq_true]
  · intro c; rfl
  · intro s hs
    simp only [unicodeIsDecimal, unicodeIsDigit, unicodeIsNumeric, allShape_eq, Bool.and_eq_true,
      List.all_eq_true]
    refine ⟨fun h => ⟨h.1, fun c hc => (digit_facts (hs c hc)).1 (h.2 c hc)⟩,
      fun h => ⟨h.1, fun c hc => (digit_facts (hs c hc)).2 (h.2 c hc)⟩⟩

theorem case_facts {c} (h : c ≤ maxUnicode) :
    ¬ (isLowercase c = true ∧ isUppercase c = true) ∧
    ¬ (isLowercase c = true ∧ isTitlecase c = true) ∧
    ¬ (isUppercase c = true ∧ isTitlecase c = true) ∧
    (isCased c = true ↔ isLowercase c = true ∨ isUppercase c = true ∨ isTitlecase c = true) :=
  (flagFact_spec _ _ _ _ _ _ _ _ _ (flags_ok h)).2.2.1

theorem isLowerLoop_iff (s : Str) (cased : Bool) :
    isLowerLoop s cased = true ↔
      (∀ c ∈ s, isUppercase c = false ∧ isTitlecase c = false) ∧
      (cased = true ∨ ∃ c ∈ s, isLowercase c = true) := by
  induction s generalizing cased with
  | nil => simp [isLowerLoop]
  | cons x xs ih =>
    simp only [isLowerLoop, List.mem_cons, forall_eq_or_imp, exists_eq_or_imp]
    by_cases h : (isUppercase x || isTitlecase x) = true
    · have : ¬ (isUppercase x = false ∧ isTitlecase x = false) := by
        rintro ⟨h1, h2⟩; simp [h1, h2] at h
      simp [h, this]
    · have h' : isUppercase x = false ∧ isTitlecase x = false := by
        simpa using h
      simp only [h, if_false, Bool.false_eq_true, ih]
      have e : (if (!cased && isLowercase x) = true then true else cased) =
          (cased || isLowercase x) := by cases cased <;> cases isLowercase x <;> rfl
      rw [e]
      constructor
      · rintro ⟨a, b⟩
        exact ⟨⟨h', a⟩, by simpa [or_assoc] using b⟩
      · rintro ⟨⟨-, a⟩, b⟩
        exact ⟨a, by simpa [or_assoc] using b⟩

theorem isUpperLoop_iff (s : Str) (cased : Bool) :
    isUpperLoop s cased = true ↔
      (∀ c ∈ s, isLowercase c = false ∧ isTitlecase c = false) ∧
      (cased = true ∨ ∃ c ∈ s, isUppercase c = true) := by
  induction s generalizing cased with
  | nil => simp [isUpperLoop]
  | cons x xs ih =>
    simp only [isUpperLoop, List.mem_cons, forall_eq_or_imp, exists_eq_or_imp]
    by_cases h : (isLowercase x || isTitlecase x) = true
    · have : ¬ (isLowercase x = false ∧ isTitlecase x = false) := by
        rintro ⟨h1, h2⟩; simp [h1, h2] at h
      simp [h, this]
    · have h' : isLowercase x = false ∧ isTitlecase x = false := by
        simpa using h
      simp only [h, if_false, Bool.false_eq_true, ih]
      have e : (if (!cased && isUppercase x) = true then true else cased) =
          (cased || isUppercase x) := by cases cased <;> cases isUppercase x <;> rfl
      rw [e]
      constructor
      · rintro ⟨a, b⟩
        exact ⟨⟨h', a⟩, by simpa [or_assoc] using b⟩
      · rintro ⟨⟨-, a⟩, b⟩
        exact ⟨a, by simpa [or_assoc] using b⟩

/-- The docstrings of `islower` and `isupper` for every string ("all cased
characters ... and there is at least one cased character"), which also says their
one-character shortcuts agree with their loops; and `istitle`'s shortcut agrees
with its loop. -/
def IsCaseDoc : Prop :=
  ∀ s : Str, Str.Valid s →
    (unicodeIsLower s = true ↔
      (∀ c ∈ s, isCased c = true → isLowercase c = true) ∧ ∃ c ∈ s, isCased c = true) ∧
    (unicodeIsUpper s = true ↔
      (∀ c ∈ s, isCased c = true → isUppercase c = true) ∧ ∃ c ∈ s, isCased c = true) ∧
    unicodeIsTitle s = isTitleLoop s false false

theorem isCaseDoc_proven : IsCaseDoc := by
  intro s hs
  have hf : ∀ c, c ∈ s → _ := fun c hc => case_facts (hs c hc)
  have lowerDoc : isLowerLoop s false = true ↔
      (∀ c ∈ s, isCased c = true → isLowercase c = true) ∧ ∃ c ∈ s, isCased c = true := by
    rw [isLowerLoop_iff]
    constructor
    · rintro ⟨h1, h2 | ⟨c, hc, hl⟩⟩
      · simp at h2
      · refine ⟨fun x hx hcx => ?_, c, hc, ((hf c hc).2.2.2).2 (Or.inl hl)⟩
        rcases ((hf x hx).2.2.2).1 hcx with h | h | h
        · exact h
        · simp [(h1 x hx).1] at h
        · simp [(h1 x hx).2] at h
    · rintro ⟨h1, c, hc, hcas⟩
      refine ⟨fun x hx => ?_, Or.inr ⟨c, hc, h1 c hc hcas⟩⟩
      obtain ⟨n1, n2, -, n4⟩ := hf x hx
      constructor
      · cases hu : isUppercase x with
        | false => rfl
        | true => exact absurd ⟨h1 x hx (n4.2 (Or.inr (Or.inl hu))), hu⟩ n1
      · cases ht : isTitlecase x with
        | false => rfl
        | true => exact absurd ⟨h1 x hx (n4.2 (Or.inr (Or.inr ht))), ht⟩ n2
  have upperDoc : isUpperLoop s false = true ↔
      (∀ c ∈ s, isCased c = true → isUppercase c = true) ∧ ∃ c ∈ s, isCased c = true := by
    rw [isUpperLoop_iff]
    constructor
    · rintro ⟨h1, h2 | ⟨c, hc, hl⟩⟩
      · simp at h2
      · refine ⟨fun x hx hcx => ?_, c, hc, ((hf c hc).2.2.2).2 (Or.inr (Or.inl hl))⟩
        rcases ((hf x hx).2.2.2).1 hcx with h | h | h
        · simp [(h1 x hx).1] at h
        · exact h
        · simp [(h1 x hx).2] at h
    · rintro ⟨h1, c, hc, hcas⟩
      refine ⟨fun x hx => ?_, Or.inr ⟨c, hc, h1 c hc hcas⟩⟩
      obtain ⟨n1, -, n3, n4⟩ := hf x hx
      constructor
      · cases hu : isLowercase x with
        | false => rfl
        | true => exact absurd ⟨hu, h1 x hx (n4.2 (Or.inl hu))⟩ n1
      · cases ht : isTitlecase x with
        | false => rfl
        | true => exact absurd ⟨h1 x hx (n4.2 (Or.inr (Or.inr ht))), ht⟩ n3
  refine ⟨?_, ?_, ?_⟩
  · match s, hf, lowerDoc with
    | [], _, _ => simp [unicodeIsLower]
    | [c], hf, lowerDoc =>
      rw [← lowerDoc]
      have := hf c List.mem_cons_self
      simp only [unicodeIsLower, isLowerLoop]
      by_cases hl : isLowercase c = true
      · have hu : isUppercase c = false := by
          cases hu : isUppercase c with
          | false => rfl
          | true => exact absurd ⟨hl, hu⟩ this.1
        have ht : isTitlecase c = false := by
          cases ht : isTitlecase c with
          | false => rfl
          | true => exact absurd ⟨hl, ht⟩ this.2.1
        simp [hl, hu, ht, isLowerLoop]
      · simp only [Bool.not_eq_true] at hl
        simp [hl, isLowerLoop]
    | a :: b :: t, _, lowerDoc => exact lowerDoc
  · match s, hf, upperDoc with
    | [], _, _ => simp [unicodeIsUpper]
    | [c], hf, upperDoc =>
      rw [← upperDoc]
      have := hf c List.mem_cons_self
      simp only [unicodeIsUpper, isUpperLoop]
      by_cases hl : isUppercase c = true
      · have hu : isLowercase c = false := by
          cases hu : isLowercase c with
          | false => rfl
          | true => exact absurd ⟨hu, hl⟩ this.1
        have ht : isTitlecase c = false := by
          cases ht : isTitlecase c with
          | false => rfl
          | true => exact absurd ⟨hl, ht⟩ this.2.2.1
        simp [hl, hu, ht, isUpperLoop]
      · simp only [Bool.not_eq_true] at hl
        simp [hl, isUpperLoop]
    | a :: b :: t, _, upperDoc => exact upperDoc
  · match s with
    | [] => rfl
    | [c] =>
      simp only [unicodeIsTitle, isTitleLoop]
      by_cases h1 : isTitlecase c = true <;> by_cases h2 : isUppercase c = true <;>
        by_cases h3 : isLowercase c = true <;> simp [h1, h2, h3, isTitleLoop]
    | a :: b :: t => rfl

/-! ## Identifiers -/

theorem scanContinue_eq (cs : List Nat) (i : Nat) :
    scanContinue i cs = i + cs.length ↔ ∀ d ∈ cs, isXidContinue d = true := by
  have hle : ∀ (cs : List Nat) i, scanContinue i cs ≤ i + cs.length := by
    intro cs
    induction cs with
    | nil => intro i; simp [scanContinue]
    | cons x xs ih =>
      intro i
      simp only [scanContinue, List.length_cons]
      split
      · omega
      · have := ih (i + 1); omega
  induction cs generalizing i with
  | nil => simp [scanContinue]
  | cons x xs ih =>
    simp only [scanContinue, List.length_cons, List.mem_cons, forall_eq_or_imp]
    by_cases hx : isXidContinue x = true
    · simp only [hx, Bool.not_true, Bool.false_eq_true, if_false, true_and]
      exact ⟨fun h => (ih (i + 1)).1 (by omega), fun h => by have := (ih (i + 1)).2 h; omega⟩
    · simp only [Bool.not_eq_true] at hx
      simp [hx]

/-- `s.isidentifier()` holds exactly for a non-empty string that starts with an
XID_Start character or `_` and continues with XID_Continue characters (PEP 3131).
Quantified over every string. -/
def IsIdentifierSpec : Prop :=
  ∀ s : Str, pyUnicodeIsIdentifier s = true ↔
    ∃ c cs, s = c :: cs ∧ (isXidStart c = true ∨ c = 0x5F) ∧ ∀ d ∈ cs, isXidContinue d = true

theorem isIdentifierSpec_proven : IsIdentifierSpec := by
  intro s
  cases s with
  | nil => simp [pyUnicodeIsIdentifier]
  | cons c cs =>
    have hl := scanContinue_eq cs 1
    have hcond : ((!isXidStart c) = true ∧ c ≠ 0x5F) ↔
        ¬ (isXidStart c = true ∨ c = 0x5F) := by
      cases isXidStart c <;> simp
    simp only [pyUnicodeIsIdentifier, scanIdentifier, List.length_cons, Bool.and_eq_true,
      bne_iff_ne, beq_iff_eq]
    by_cases hst : isXidStart c = true ∨ c = 0x5F
    · rw [if_neg (fun h => hcond.1 h hst)]
      constructor
      · rintro ⟨-, h⟩
        exact ⟨c, cs, rfl, hst, hl.1 (by omega)⟩
      · rintro ⟨c', cs', he, -, h2⟩
        simp only [List.cons.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        have h3 := hl.2 h2
        exact ⟨by simp, by omega⟩
    · rw [if_pos (hcond.2 hst)]
      constructor
      · rintro ⟨-, h⟩
        omega
      · rintro ⟨c', cs', he, h1, -⟩
        simp only [List.cons.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact absurd h1 hst

/-! ## `repr` -/

theorem hexDigits_length (w n : Nat) : (hexDigits w n).length = w := by simp [hexDigits]

theorem hexDigits_le (w n : Nat) : ∀ x ∈ hexDigits w n, x ≤ 127 := by
  intro x hx
  simp only [hexDigits, List.mem_map] at hx
  obtain ⟨i, -, rfl⟩ := hx
  have : (n >>> (4 * i)) &&& 15 ≤ 15 := Nat.and_le_right
  simp only [hexLower]
  split <;> omega

/-- The increment the first pass of `unicode_repr` adds for `ch`. -/
def reprIncr (ch : Nat) : Nat := (reprScanStep {} ch).osize

theorem reprStep_fields (a : ReprScan) (c : Nat) :
    (reprScanStep a c).osize = a.osize + reprIncr c ∧
    (reprScanStep a c).squote = a.squote + (if c = 39 then 1 else 0) ∧
    (reprScanStep a c).dquote = a.dquote + (if c = 34 then 1 else 0) := by
  simp only [reprIncr, reprScanStep]
  repeat' split
  all_goals simp_all <;> omega

theorem reprChar_length (q c : Nat) (hq : q = 39 ∨ q = 34) :
    (reprChar q c).length = reprIncr c + (if c = q then 1 else 0) := by
  simp only [reprIncr, reprChar, reprScanStep]
  repeat' split
  all_goals simp_all [hexDigits_length] <;> omega

theorem reprScan_fields (s : Str) (a : ReprScan) :
    (s.foldl reprScanStep a).osize = a.osize + (s.map reprIncr).sum ∧
    (s.foldl reprScanStep a).squote = a.squote + s.count 39 ∧
    (s.foldl reprScanStep a).dquote = a.dquote + s.count 34 := by
  induction s generalizing a with
  | nil => simp
  | cons c cs ih =>
    obtain ⟨h1, h2, h3⟩ := reprStep_fields a c
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, List.count_cons]
    obtain ⟨i1, i2, i3⟩ := ih (reprScanStep a c)
    rw [i1, i2, i3, h1, h2, h3]
    refine ⟨by omega, ?_, ?_⟩ <;> simp <;> split <;> omega

theorem repr_flat_length (q : Nat) (hq : q = 39 ∨ q = 34) (s : Str) :
    (s.flatMap (reprChar q)).length = (s.map reprIncr).sum + s.count q := by
  induction s with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons,
      List.count_cons, ih, reprChar_length q c hq]
    simp only [beq_iff_eq]
    omega

theorem maxch_mono (s : Str) (a : ReprScan) : a.maxch ≤ (s.foldl reprScanStep a).maxch := by
  induction s generalizing a with
  | nil => exact Nat.le_refl _
  | cons c cs ih =>
    refine Nat.le_trans ?_ (ih _)
    simp only [reprScanStep]
    repeat' split
    all_goals simp <;> omega

/-- Every non-ASCII character that `repr` copies is at most the `maxch` of the
first pass. -/
theorem maxch_ge (s : Str) (a : ReprScan) :
    ∀ c ∈ s, 127 ≤ c → isPrintable c = true → c ≤ (s.foldl reprScanStep a).maxch := by
  induction s generalizing a with
  | nil => intro c hc; simp at hc
  | cons x xs ih =>
    intro c hc h127 hp
    rcases List.mem_cons.1 hc with rfl | hc
    · refine Nat.le_trans ?_ (maxch_mono xs _)
      have h7 : c ≠ 0x7f := by
        rintro rfl
        revert hp
        decide
      simp only [reprScanStep]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_pos hp]
      exact Nat.le_max_left _ _
    · exact ih _ c hc h127 hp

theorem reprIncr_pos (c : Nat) : 1 ≤ reprIncr c := by
  simp only [reprIncr, reprScanStep]
  repeat' split
  all_goals simp

theorem reprIncr_one (c : Nat) (h : reprIncr c = 1) (h127 : 127 ≤ c) : isPrintable c = true := by
  simp only [reprIncr, reprScanStep] at h
  repeat' split at h
  all_goals first | omega | simp_all | assumption

theorem sum_one (s : Str) (h : (s.map reprIncr).sum = s.length) : ∀ c ∈ s, reprIncr c = 1 := by
  induction s with
  | nil => intro c hc; simp at hc
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons] at h
    have hx := reprIncr_pos x
    have hle : xs.length ≤ (xs.map reprIncr).sum := by
      clear ih h hx
      induction xs with
      | nil => simp
      | cons y ys ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have := reprIncr_pos y
        omega
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · omega
    · exact ih (by omega) c hc

/-- The two passes of `unicode_repr` agree, for every string: the size computed
by the first pass is the length written by the second, and no written character
exceeds `maxch`, so `PyUnicode_New(osize, maxch)` allocates exactly enough and the
writes cannot truncate a character. -/
def ReprTwoPasses : Prop :=
  ∀ s : Str,
    (unicodeReprFull s).1.length = (unicodeReprFull s).2.1 ∧
    ∀ x ∈ (unicodeReprFull s).1, x ≤ (unicodeReprFull s).2.2

theorem reprChar_le (q c m : Nat) (hq : q ≤ 127) (hm : 127 ≤ m)
    (hc : 127 ≤ c → isPrintable c = true → c ≤ m) :
    ∀ x ∈ reprChar q c, x ≤ m := by
  intro x hx
  have hh := fun w => hexDigits_le w c
  simp only [reprChar] at hx
  repeat' split at hx
  all_goals
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or] at hx
  all_goals first
    | omega
    | (rcases hx with hx | hx
       · omega
       · have := hh _ x hx
         omega)
    | (subst hx
       have h1 : isPrintable x = true := by simp_all
       exact hc (by omega) h1)

theorem reprFinish_spec (s : Str) (a : ReprScan) (e1 : a.osize = (s.map reprIncr).sum)
    (e2 : a.squote = s.count 39) (e3 : a.dquote = s.count 34)
    (hm : ∀ c ∈ s, 127 ≤ c → isPrintable c = true → c ≤ a.maxch) (hm0 : 127 ≤ a.maxch) :
    (reprFinish s a).1.length = (reprFinish s a).2.1 ∧
    ∀ x ∈ (reprFinish s a).1, x ≤ (reprFinish s a).2.2 := by
  simp only [reprFinish]
  have hq : reprQuote a.squote a.dquote = 39 ∨ reprQuote a.squote a.dquote = 34 := by
    unfold reprQuote; split <;> simp
  have hq7 : reprQuote a.squote a.dquote ≤ 127 := by rcases hq with h | h <;> omega
  have hcount : s.count (reprQuote a.squote a.dquote) =
      if a.squote ≠ 0 ∧ a.dquote ≠ 0 then a.squote else 0 := by
    unfold reprQuote
    by_cases h4 : a.squote = 0 <;> by_cases h5 : a.dquote = 0 <;> simp [h4, h5] <;> omega
  generalize reprQuote a.squote a.dquote = q at *
  have hlen := repr_flat_length q hq s
  by_cases hc : (a.osize != s.length || a.squote != 0) = true
  · simp only [hc, Bool.not_true, cond_false, stringlibRepr]
    constructor
    · simp only [if_false, Bool.false_eq_true, List.length_append, List.length_cons,
        List.length_nil, hlen, hcount, ← e1]
      split <;> omega
    · intro x hx
      simp only [if_false, Bool.false_eq_true, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false, List.mem_flatMap] at hx
      rcases hx with (rfl | ⟨c, hcs, hx⟩) | rfl
      · omega
      · exact reprChar_le q c _ hq7 hm0 (fun a b => hm c hcs a b) x hx
      · omega
  · simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hc
    obtain ⟨c1, c2⟩ := hc
    have : (!(a.osize != s.length || a.squote != 0)) = true := by simp [c1, c2]
    simp only [this, if_true]
    constructor
    · simp [c1, c2]
    · intro x hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (rfl | hx) | rfl
      · omega
      · have h11 := sum_one s (by rw [← e1]; exact c1) x hx
        by_cases h127 : 127 ≤ x
        · exact hm x hx h127 (reprIncr_one x h11 h127)
        · omega
      · omega

theorem reprTwoPasses_proven : ReprTwoPasses := by
  intro s
  have hf := reprScan_fields s ({} : ReprScan)
  exact reprFinish_spec s (reprScan s) (by simpa [reprScan] using hf.1) (by simpa [reprScan] using hf.2.1)
    (by simpa [reprScan] using hf.2.2) (maxch_ge s {}) (maxch_mono s {})

end PyLean.UnicodeObj
