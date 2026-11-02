import PyLean.JsonMod.RoundTripStr
import PyLean.JsonMod.DecFuel

/-!
`int.__repr__` text and the number scanner: an int written by `dumps` is read
back by `_match_number_unicode`.
-/

namespace PyLean.JsonMod

open PyLean

/-- A delimiter (or the end of the document) after a value. -/
def Delim (rest : PStr) : Prop :=
  rest = [] ∨ ∃ c r, rest = c :: r ∧ (isWs c = true ∨ c = 44 ∨ c = 93 ∨ c = 125)

theorem decVal_snoc (l : PStr) (d : Nat) : decVal (l ++ [d]) = 10 * decVal l + (d - 48) := by
  simp [decVal, List.foldl_append]

/-- What `decDigits` produces. -/
structure DigSpec (n : Nat) (l : PStr) : Prop where
  dig : ∀ c ∈ l, isDigit c = true
  val : decVal l = n
  head : (n = 0 ∧ l = [48]) ∨ (∃ d r, l = d :: r ∧ 49 ≤ d ∧ d ≤ 57)

theorem decDigitsF_spec : ∀ (f n : Nat), n < f → DigSpec n (decDigitsF f n) := by
  intro f
  induction f with
  | zero => intro n h; omega
  | succ f ih =>
    intro n hn
    simp only [decDigitsF]
    split
    · rename_i h10
      refine ⟨?_, ?_, ?_⟩
      · intro c hc
        simp only [List.mem_singleton] at hc
        subst hc
        simp [isDigit]; omega
      · simp only [decVal, List.foldl_cons, List.foldl_nil]; omega
      · by_cases h0 : n = 0
        · subst h0; exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨48 + n, [], rfl, by omega, by omega⟩
    · rename_i h10
      have q := ih (n / 10) (by omega)
      refine ⟨?_, ?_, ?_⟩
      · intro c hc
        simp only [List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | hc
        · exact q.dig c hc
        · subst hc
          simp [isDigit]; omega
      · rw [decVal_snoc, q.val]; omega
      · rcases q.head with ⟨h0, _⟩ | ⟨d, r, h1, h2, h3⟩
        · omega
        · exact Or.inr ⟨d, r ++ [48 + n % 10], by rw [h1]; rfl, h2, h3⟩

theorem decDigits_spec (n : Nat) : DigSpec n (decDigits n) := decDigitsF_spec (n + 1) n (by omega)

theorem digitsLen_append : ∀ (l r : PStr), (∀ c ∈ l, isDigit c = true) →
    digitsLen (l ++ r) = l.length + digitsLen r
  | [], r, _ => by simp
  | c :: l, r, h => by
    have h1 := h c (by simp)
    simp only [List.cons_append, digitsLen_cons, h1, ↓reduceIte, List.length_cons]
    rw [digitsLen_append l r (fun d hd => h d (by simp [hd]))]
    omega

theorem Delim.stop {rest : PStr} (h : Delim rest) :
    digitsLen rest = 0 ∧ reFrac rest = [] ∧ reExp rest = [] := by
  rcases h with rfl | ⟨c, r, rfl, hc⟩
  · exact ⟨rfl, rfl, rfl⟩
  · have hn : ∀ x : Nat, (x = 9 ∨ x = 10 ∨ x = 13 ∨ x = 32 ∨ x = 44 ∨ x = 93 ∨ x = 125) →
        digitsLen (x :: r) = 0 ∧ reFrac (x :: r) = [] ∧ reExp (x :: r) = [] := by
      intro x hx
      have h1 : isDigit x = false := by
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      have h2 : x ≠ 46 := by omega
      have h3 : ¬ (x = 101 ∨ x = 69) := by omega
      refine ⟨by simp [digitsLen_cons, h1], ?_, reExp_not x r h3⟩
      rw [reFrac_cons]; simp [h2]
    apply hn
    rcases hc with hc | hc
    · simp only [isWs, Bool.or_eq_true, beq_iff_eq] at hc; omega
    · omega

/-- The digits of an int, without sign. -/
theorem reInt_digits {n : Nat} {ds rest : PStr} (hd : DigSpec n ds) (h0 : digitsLen rest = 0) :
    reInt (ds ++ rest) = some ds := by
  rcases hd.head with ⟨_, rfl⟩ | ⟨d, r, rfl, h1, h2⟩
  · simp [reInt_cons]
  · have h3 : d ≠ 48 := by omega
    have hr : ∀ c ∈ r, isDigit c = true := fun c hc => hd.dig c (by simp [hc])
    simp only [List.cons_append, reInt_cons, h3, ↓reduceIte, h1, h2, and_self]
    rw [digitsLen_append r rest hr, h0, Nat.add_zero, List.take_left]

theorem numberRe_digits {n : Nat} {ds rest : PStr} (hd : DigSpec n ds) (hrest : Delim rest)
    (h45 : ∀ r, ds ≠ 45 :: r) : numberRe (ds ++ rest) = some (ds, [], []) := by
  obtain ⟨h1, h2, h3⟩ := hrest.stop
  have hs : reSign (ds ++ rest) = ([], ds ++ rest) := by
    cases ds with
    | nil =>
      rcases hd.head with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
    | cons c l =>
      have : c ≠ 45 := fun e => h45 l (by rw [e])
      simp [reSign_cons, this]
  unfold numberRe
  simp only [hs, reInt_digits hd h1, List.drop_left, h2, List.length_nil, List.drop_zero, h3, List.nil_append]

theorem numberRe_signed {n : Nat} {ds rest : PStr} (hd : DigSpec n ds) (hrest : Delim rest) :
    numberRe (45 :: ds ++ rest) = some (45 :: ds, [], []) := by
  obtain ⟨h1, h2, h3⟩ := hrest.stop
  have hs : reSign (45 :: ds ++ rest) = ([45], ds ++ rest) := rfl
  unfold numberRe
  simp only [hs, reInt_digits hd h1, List.drop_left, h2, List.length_nil,
    List.drop_zero, h3, List.singleton_append]

/-- The form of `int.__repr__`. -/
theorem intRepr_view {n : Int} {t : PStr} (h : intRepr n = .ok t) :
    ∃ ds, DigSpec n.natAbs ds ∧ t = (if n < 0 then 45 :: ds else ds) ∧ ds.length ≤ maxStrDigits := by
  unfold intRepr at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hl
    simp only [Except.ok.injEq] at h
    exact ⟨_, decDigits_spec _, h.symm, by omega⟩

/-- What `loads` makes of the text of an int. -/
def decInt (dcfg : DCfg) (n : Int) : JVal :=
  match intRepr n with
  | .ok t =>
    match parseInt dcfg t with
    | .ok j => j
    | .error _ => .null
  | .error _ => .null

/-- Callbacks that leave the JSON structure alone: objects come back as their
items (no `object_hook`, `object_pairs_hook` absent or keeping the pairs, and
`array_hook` absent or keeping the list), `parse_int` does not raise, and the other callbacks are Python callables. -/
structure DCfg.Rec (dcfg : DCfg) : Prop where
  fin : ∀ acc, cFinish dcfg acc = .ok (.obj acc)
  arr : ∀ xs, mkArr dcfg xs = .ok (.arr xs)
  int : ∀ h, dcfg.parseIntFn = some h → ∀ t, ∃ j, h t = .ok j
  flt : ∀ t, dcfg.parseFloat t ≠ fuelOut
  con : ∀ t, dcfg.parseConstant t ≠ fuelOut

theorem pyInt_repr {n : Int} {t : PStr} (h : intRepr n = .ok t) : pyIntOfText t = .ok n := by
  obtain ⟨ds, hd, rfl, hl⟩ := intRepr_view h
  · have hint : pyIntOfText (if n < 0 then 45 :: ds else ds) = .ok n := by
      by_cases hn : n < 0
      · simp only [hn, ↓reduceIte, pyIntOfText]
        have : ¬ ds.length > maxStrDigits := by omega
        simp only [this, ↓reduceIte, hd.val]
        congr 1
        omega
      · have h45 : ∀ r, ds ≠ 45 :: r := by
          intro r e
          rcases hd.head with ⟨_, h⟩ | ⟨d, r', h', h1, h2⟩
          · rw [e] at h; simp at h
          · rw [e] at h'; simp at h'; omega
        simp only [hn, ↓reduceIte]
        have h1 : pyIntOfText ds = (if ds.length > maxStrDigits then
            .error (.valueError s!"Exceeds the limit (4300 digits) for integer string conversion: value has {ds.length} digits; use sys.set_int_max_str_digits() to increase the limit")
            else .ok (decVal ds : Int)) := by
          cases ds with
          | nil => rfl
          | cons c l =>
            have : c ≠ 45 := fun e => h45 l (by rw [e])
            simp [pyIntOfText, this]
        rw [h1]
        have : ¬ ds.length > maxStrDigits := by omega
        simp only [this, ↓reduceIte, hd.val]
        congr 1
        omega
    exact hint

theorem parseInt_repr (dcfg : DCfg) (hR : dcfg.Rec) {n : Int} {t : PStr} (h : intRepr n = .ok t) :
    parseInt dcfg t = .ok (decInt dcfg n) := by
  simp only [decInt, h]
  cases hi : dcfg.parseIntFn with
  | some f =>
    obtain ⟨j, hj⟩ := hR.int f hi t
    simp [parseInt, hi, hj]
  | none => simp [parseInt, hi, pyInt_repr h]

theorem numberRe_repr {n : Int} {t rest : PStr} (h : intRepr n = .ok t) (hr : Delim rest) :
    numberRe (t ++ rest) = some (t, [], []) := by
  obtain ⟨ds, hd, rfl, _⟩ := intRepr_view h
  by_cases hn : n < 0
  · simp only [hn, ↓reduceIte, List.cons_append]
    exact numberRe_signed hd hr
  · simp only [hn, ↓reduceIte]
    refine numberRe_digits hd hr ?_
    intro r e
    rcases hd.head with ⟨_, h'⟩ | ⟨d, r', h', h1, h2⟩
    · rw [e] at h'; simp at h'
    · rw [e] at h'; simp at h'; omega

/-- `_match_number_unicode` on the text of an int. -/
theorem matchNumber_repr (dcfg : DCfg) (hR : dcfg.Rec) (s : PStr) (p : Nat) {n : Int} {t rest : PStr}
    (h : intRepr n = .ok t) (hs : s.drop p = t ++ rest) (hr : Delim rest) (hp : p < s.length) :
    cMatchNumber dcfg s p = .ok (decInt dcfg n, p + t.length) := by
  have hre := numberRe_repr h hr
  rw [← hs] at hre
  rcases matchNumber_twin dcfg s p hp with ⟨h1, _⟩ | ⟨i, fr, ex, h1, h2⟩
  · rw [hre] at h1; cases h1
  · rw [hre] at h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl, rfl⟩ := h1
    rw [h2]
    simp [parseInt_repr dcfg hR h, Except.map]

end PyLean.JsonMod
