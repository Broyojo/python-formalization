import PyLean.LongObj.ComplexDbl
import PyLean.LongObj.ComplexParseTwin

/-!
The concrete `strtod`, the one the difftest runs, satisfies `StrtodSpec`. So the
parser theorems proved over an abstract `strtod` hold at exact binary64 with no
assumption left, and `StrtodSpec` is not vacuous.
-/

namespace PyLean.LongObj.Cplx

open CDouble

namespace Dbl

/-- What a stop character is not. -/
theorem stop_facts (c : Nat) (h : isStop c = true) :
    isDigit c = false ∧ c ≠ 46 ∧ c ≠ 45 ∧ c ≠ 43 ∧ c ≠ 101 ∧ c ≠ 69 ∧
      lower c ≠ 105 ∧ lower c ≠ 110 ∧ lower c ≠ 102 ∧ lower c ≠ 116 ∧ lower c ≠ 121 ∧
      lower c ≠ 97 := by
  simp only [isStop, isSpaceC, chLParen, chRParen, Bool.or_eq_true, beq_iff_eq] at h
  repeat' (rcases h with h | h)
  all_goals decide

theorem scanDigits_cut (c : Nat) (q : List Nat) (hc : isDigit c = false) :
    ∀ (s : List Nat) (acc n : Nat), scanDigits (s ++ c :: q) acc n = scanDigits s acc n := by
  intro s
  induction s with
  | nil => intro acc n; simp [scanDigits, hc]
  | cons x t ih =>
    intro acc n
    simp only [List.cons_append, scanDigits]
    split
    · exact ih _ _
    · rfl

theorem scanDigits_le : ∀ (s : List Nat) (acc n : Nat), (scanDigits s acc n).2 ≤ n + s.length := by
  intro s
  induction s with
  | nil => intro acc n; simp [scanDigits]
  | cons x t ih =>
    intro acc n
    simp only [scanDigits, List.length_cons]
    split
    · have := ih (acc * 10 + (x - 48)) (n + 1)
      omega
    · simp

theorem drop_cut (s : List Nat) (k : Nat) (hk : k ≤ s.length) (c : Nat) (q : List Nat) :
    (s ++ c :: q).drop k = s.drop k ++ c :: q :=
  List.drop_append_of_le_length hk

theorem dgFrac_cut (c : Nat) (q : List Nat) (hc : isStop c = true) (r : List Nat) :
    dgFrac (r ++ c :: q) = dgFrac r := by
  obtain ⟨h1, h2, _⟩ := stop_facts c hc
  cases r with
  | nil =>
    simp only [List.nil_append]
    cases q <;> simp [dgFrac, h2]
  | cons x t =>
    by_cases hx : x = 46
    · subst hx
      simp only [List.cons_append, dgFrac]
      rw [scanDigits_cut c q h1]
    · simp [dgFrac, hx]

theorem dgFrac_len (r : List Nat) (h : (dgFrac r).2.2 = true) : 1 + (dgFrac r).2.1 ≤ r.length := by
  cases r with
  | nil => simp [dgFrac] at h
  | cons x t =>
    by_cases hx : x = 46
    · subst hx
      simp only [dgFrac, List.length_cons]
      have := scanDigits_le t 0 0
      omega
    · simp [dgFrac, hx] at h

theorem dgExpDigits_cut (c : Nat) (q : List Nat) (hc : isStop c = true) (e : Bool) (t : List Nat)
    (sl : Nat) : dgExpDigits e (t ++ c :: q) sl = dgExpDigits e t sl := by
  have h1 := (stop_facts c hc).1
  simp only [dgExpDigits]
  rw [scanDigits_cut c q h1]

theorem dgExp_cut (c : Nat) (q : List Nat) (hc : isStop c = true) (a : List Nat) :
    dgExp (a ++ c :: q) = dgExp a := by
  obtain ⟨h1, _, h3, h4, h5, h6, _⟩ := stop_facts c hc
  cases a with
  | nil =>
    have hb : (c == 101 || c == 69) = false := by simp [h5, h6]
    simp only [List.nil_append, dgExp, hb, Bool.false_eq_true, ite_false]
  | cons x t =>
    simp only [List.cons_append, dgExp]
    split
    · cases t with
      | nil =>
        simp only [List.nil_append]
        have e1 : dgExpDigits false (c :: q) 0 = (0, 0) := by
          simp [dgExpDigits, scanDigits, h1]
        have e2 : dgExpDigits false ([] : List Nat) 0 = (0, 0) := by
          simp [dgExpDigits, scanDigits]
        split
        · next u heq => simp only [List.cons.injEq] at heq; omega
        · next u heq => simp only [List.cons.injEq] at heq; omega
        · rw [e1]
          exact e2.symm
      | cons y u =>
        simp only [List.cons_append]
        by_cases hy1 : y = 45
        · subst hy1
          simp only
          rw [dgExpDigits_cut c q hc]
        · by_cases hy2 : y = 43
          · subst hy2
            simp only
            rw [dgExpDigits_cut c q hc]
          · have l : dgExpDigits false (y :: (u ++ c :: q)) 0 = dgExpDigits false (y :: u) 0 := by
              have := dgExpDigits_cut c q hc false (y :: u) 0
              simpa using this
            split
            · next v heq => simp only [List.cons.injEq] at heq; omega
            · next v heq => simp only [List.cons.injEq] at heq; omega
            · split
              · next v heq => simp only [List.cons.injEq] at heq; omega
              · next v heq => simp only [List.cons.injEq] at heq; omega
              · exact l
    · rfl

theorem dgExpDigits_len (e : Bool) (t : List Nat) (sl : Nat) :
    (dgExpDigits e t sl).2 ≤ 1 + sl + t.length := by
  simp only [dgExpDigits]
  split
  · simp
  · have := scanDigits_le t 0 0
    simp only
    omega

theorem dgExp_len (a : List Nat) : (dgExp a).2 ≤ a.length := by
  cases a with
  | nil => simp [dgExp]
  | cons x t =>
    simp only [dgExp, List.length_cons]
    split
    · split
      · next u =>
        have := dgExpDigits_len true u 1
        simp only [List.length_cons] at this ⊢
        omega
      · next u =>
        have := dgExpDigits_len false u 1
        simp only [List.length_cons] at this ⊢
        omega
      · have := dgExpDigits_len false t 0
        omega
    · simp

theorem dgMant_cut (c : Nat) (q : List Nat) (hc : isStop c = true) (neg : Bool) (s : List Nat)
    (off : Nat) : dgMant neg (s ++ c :: q) off = dgMant neg s off := by
  have h1 := (stop_facts c hc).1
  simp only [dgMant]
  rw [scanDigits_cut c q h1]
  have hni : (scanDigits s 0 0).2 ≤ s.length := by
    have := scanDigits_le s 0 0
    omega
  rw [drop_cut s _ hni, dgFrac_cut c q hc]
  generalize hfr : dgFrac (s.drop (scanDigits s 0 0).2) = fr
  have hdl : (scanDigits s 0 0).2 + (if fr.2.2 = true then 1 + fr.2.1 else 0) ≤ s.length := by
    split
    · next h =>
      have h3 := dgFrac_len (s.drop (scanDigits s 0 0).2) (by rw [hfr]; exact h)
      rw [hfr] at h3
      simp only [List.length_drop] at h3
      omega
    · simpa using hni
  rw [drop_cut s _ hdl, dgExp_cut c q hc]

theorem dgMant_le (neg : Bool) (s : List Nat) (off : Nat) :
    (dgMant neg s off).2 ≤ off + s.length := by
  simp only [dgMant]
  split
  · simp
  · have hni : (scanDigits s 0 0).2 ≤ s.length := by
      have := scanDigits_le s 0 0
      omega
    generalize hfr : dgFrac (s.drop (scanDigits s 0 0).2) = fr
    have hdl : (scanDigits s 0 0).2 + (if fr.2.2 = true then 1 + fr.2.1 else 0) ≤ s.length := by
      split
      · next h =>
        have h3 := dgFrac_len (s.drop (scanDigits s 0 0).2) (by rw [hfr]; exact h)
        rw [hfr] at h3
        simp only [List.length_drop] at h3
        omega
      · simpa using hni
    have hex := dgExp_len (s.drop ((scanDigits s 0 0).2 + (if fr.2.2 = true then 1 + fr.2.1 else 0)))
    simp only [List.length_drop] at hex
    simp only
    omega

theorem dgStrtod_cut (c : Nat) (q : List Nat) (hc : isStop c = true) (p : List Nat) :
    dgStrtod (p ++ c :: q) = dgStrtod p := by
  obtain ⟨_, _, h3, h4, _⟩ := stop_facts c hc
  cases p with
  | nil =>
    have := dgMant_cut c q hc false [] 0
    simp only [List.nil_append] at this ⊢
    have e1 : dgStrtod (c :: q) = dgMant false (c :: q) 0 := by
      unfold dgStrtod
      split
      · next t heq => simp only [List.cons.injEq] at heq; omega
      · next t heq => simp only [List.cons.injEq] at heq; omega
      · rfl
    rw [e1, this]
    rfl
  | cons x t =>
    by_cases h45 : x = 45
    · subst h45
      simp only [List.cons_append, dgStrtod]
      exact dgMant_cut c q hc true t 1
    · by_cases h43 : x = 43
      · subst h43
        simp only [List.cons_append, dgStrtod]
        exact dgMant_cut c q hc false t 1
      · have e : ∀ r : List Nat, dgStrtod (x :: r) = dgMant false (x :: r) 0 := by
          intro r
          unfold dgStrtod
          split
          · next u heq => simp only [List.cons.injEq] at heq; omega
          · next u heq => simp only [List.cons.injEq] at heq; omega
          · rfl
        rw [List.cons_append, e, e]
        have := dgMant_cut c q hc false (x :: t) 0
        simpa using this

theorem dgStrtod_le (p : List Nat) : (dgStrtod p).2 ≤ p.length := by
  cases p with
  | nil => exact dgMant_le false [] 0
  | cons x t =>
    by_cases h45 : x = 45
    · subst h45
      have := dgMant_le true t 1
      simp only [dgStrtod, List.length_cons]
      omega
    · by_cases h43 : x = 43
      · subst h43
        have := dgMant_le false t 1
        simp only [dgStrtod, List.length_cons]
        omega
      · have e : dgStrtod (x :: t) = dgMant false (x :: t) 0 := by
          unfold dgStrtod
          split
          · next u heq => simp only [List.cons.injEq] at heq; omega
          · next u heq => simp only [List.cons.injEq] at heq; omega
          · rfl
        rw [e]
        simpa using dgMant_le false (x :: t) 0

theorem ciPrefix_cut (c : Nat) (q : List Nat) : ∀ (s w : List Nat), (∀ x ∈ w, lower c ≠ x) →
    ciPrefix (s ++ c :: q) w = ciPrefix s w := by
  intro s
  induction s with
  | nil =>
    intro w hw
    cases w with
    | nil => rfl
    | cons x ws =>
      have : (lower c == x) = false := by simpa using hw x (by simp)
      simp [ciPrefix, this]
  | cons a s ih =>
    intro w hw
    cases w with
    | nil => rfl
    | cons x ws =>
      simp only [List.cons_append, ciPrefix]
      rw [ih ws (fun y hy => hw y (by simp [hy]))]

theorem ciPrefix_len : ∀ (s w : List Nat), ciPrefix s w = true → w.length ≤ s.length := by
  intro s
  induction s with
  | nil =>
    intro w h
    cases w with
    | nil => simp
    | cons x ws => simp [ciPrefix] at h
  | cons a s ih =>
    intro w h
    cases w with
    | nil => simp
    | cons x ws =>
      simp only [ciPrefix, Bool.and_eq_true] at h
      have := ih ws h.2
      simp only [List.length_cons]
      omega

theorem infNanBody_cut (c : Nat) (q : List Nat) (hc : isStop c = true) (neg : Bool) (s : List Nat)
    (off z : Nat) : infNanBody neg (s ++ c :: q) off z = infNanBody neg s off z := by
  obtain ⟨_, _, _, _, _, _, a1, a2, a3, a4, a5, a6⟩ := stop_facts c hc
  have wI : ∀ x ∈ wInf, lower c ≠ x := by
    intro x hx
    simp only [wInf, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have wN : ∀ x ∈ wNan, lower c ≠ x := by
    intro x hx
    simp only [wNan, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have wT : ∀ x ∈ wInity, lower c ≠ x := by
    intro x hx
    simp only [wInity, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  simp only [infNanBody]
  rw [ciPrefix_cut c q s wInf wI, ciPrefix_cut c q s wNan wN]
  split
  · next h =>
    have hl := ciPrefix_len s wInf h
    have hl' : 3 ≤ s.length := by simpa [wInf] using hl
    rw [drop_cut s 3 hl', ciPrefix_cut c q _ wInity wT]
  · rfl

theorem infNanBody_le (neg : Bool) (s : List Nat) (off : Nat) :
    (infNanBody neg s off 0).2 ≤ off + s.length := by
  simp only [infNanBody]
  split
  · next h =>
    have hl := ciPrefix_len s wInf h
    have hl' : 3 ≤ s.length := by simpa [wInf] using hl
    split
    · next h2 =>
      have hl2 := ciPrefix_len (s.drop 3) wInity h2
      simp only [wInity, List.length_drop, List.length_cons, List.length_nil] at hl2
      simp only
      omega
    · simp only
      omega
  · split
    · next h =>
      have hl := ciPrefix_len s wNan h
      have hl' : 3 ≤ s.length := by simpa [wNan] using hl
      simp only
      omega
    · simp

theorem parseInfNan_cut (c : Nat) (q : List Nat) (hc : isStop c = true) (p : List Nat) :
    parseInfNan (p ++ c :: q) = parseInfNan p := by
  obtain ⟨_, _, h3, h4, _⟩ := stop_facts c hc
  cases p with
  | nil =>
    have := infNanBody_cut c q hc false [] 0 0
    simp only [List.nil_append] at this ⊢
    have e1 : parseInfNan (c :: q) = infNanBody false (c :: q) 0 0 := by
      unfold parseInfNan
      split
      · next t heq => simp only [List.cons.injEq] at heq; omega
      · next t heq => simp only [List.cons.injEq] at heq; omega
      · rfl
    rw [e1, this]
    rfl
  | cons x t =>
    by_cases h45 : x = 45
    · subst h45
      simp only [List.cons_append, parseInfNan]
      exact infNanBody_cut c q hc true t 1 0
    · by_cases h43 : x = 43
      · subst h43
        simp only [List.cons_append, parseInfNan]
        exact infNanBody_cut c q hc false t 1 0
      · have e : ∀ r : List Nat, parseInfNan (x :: r) = infNanBody false (x :: r) 0 0 := by
          intro r
          unfold parseInfNan
          split
          · next u heq => simp only [List.cons.injEq] at heq; omega
          · next u heq => simp only [List.cons.injEq] at heq; omega
          · rfl
        rw [List.cons_append, e, e]
        have := infNanBody_cut c q hc false (x :: t) 0 0
        simpa using this

theorem parseInfNan_le (p : List Nat) : (parseInfNan p).2 ≤ p.length := by
  cases p with
  | nil => exact infNanBody_le false [] 0
  | cons x t =>
    by_cases h45 : x = 45
    · subst h45
      have := infNanBody_le true t 1
      simp only [parseInfNan, List.length_cons]
      omega
    · by_cases h43 : x = 43
      · subst h43
        have := infNanBody_le false t 1
        simp only [parseInfNan, List.length_cons]
        omega
      · have e : parseInfNan (x :: t) = infNanBody false (x :: t) 0 0 := by
          unfold parseInfNan
          split
          · next u heq => simp only [List.cons.injEq] at heq; omega
          · next u heq => simp only [List.cons.injEq] at heq; omega
          · rfl
        rw [e]
        simpa using infNanBody_le false (x :: t) 0

/-- The concrete conversion consumes only what is there, and stops at a stop
character. -/
theorem asciiStrtod_spec : StrtodSpec asciiStrtod where
  le_length p := by
    simp only [asciiStrtod]
    split
    · exact parseInfNan_le p
    · exact dgStrtod_le p
  cut p c q hc := by
    simp only [asciiStrtod]
    rw [dgStrtod_cut c q hc, parseInfNan_cut c q hc]

end Dbl

/-- `ParseRejectsNul` and `FloatStringsAreComplexStrings` at exact binary64, with the
concrete conversion and no hypothesis on it. -/
def ParserAtBinary64 : Prop :=
  ∀ (db : UniDB) (v : List Nat) (r r' : String),
    (0 ∈ v → ∃ m, complex_from_str db Dbl.asciiStrtod v r = .error (.valueError m)) ∧
    (∀ x : Dbl, float_from_str db Dbl.asciiStrtod v r = .ok x →
      complex_from_str db Dbl.asciiStrtod v r' = .ok ⟨x, CDouble.zero⟩)

theorem parserAtBinary64_proven : ParserAtBinary64 := by
  intro db v r r'
  exact ⟨parseRejectsNul_proven Dbl Dbl.asciiStrtod Dbl.asciiStrtod_spec db v r,
    fun x h => floatStringsAreComplexStrings_proven Dbl Dbl.asciiStrtod Dbl.asciiStrtod_spec db v
      r r' x h⟩

end PyLean.LongObj.Cplx
