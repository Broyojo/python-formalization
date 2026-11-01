import PyLean.JsonMod.DecLemmas

/-!
`py_scanstring` and `scanstring_unicode` agree, except for the messages (and,
for invalid escapes, the position) of two errors.
-/

namespace PyLean.JsonMod

open PyLean

/-- How a pure-Python error relates to the C one at the same point: equal; the
C `StopIteration(i)` that the Python array and object loops have already turned
into `JSONDecodeError("Expecting value", s, i)`; or one of the two errors whose
text differs: a control character (same position, Python's message names the
character), or an invalid escape `\c` (C reports the backslash's position with
`"Invalid \\escape"`, Python the position of `c` with `"Invalid \\escape: 'c'"`). -/
def ErrRel (s : PStr) (pe ce : DErr) : Prop :=
  pe = ce ∨
  (∃ i, pe = .jde "Expecting value" i ∧ ce = .stop i) ∨
  (∃ (q : Nat) (ch : Nat), s[q]? = some ch ∧ ch < 32 ∧
    ce = .jde "Invalid control character at" q ∧ pe = .jde (ctrlMsgPy ch) q) ∨
  (∃ (q : Nat) (ch : Nat), s[q]? = some 92 ∧ s[q + 1]? = some ch ∧
    ce = .jde "Invalid \\escape" q ∧ pe = .jde (escMsgPy ch) ((q : Int) + 1))

/-- Related outcomes with a result position. -/
def ResRel {α : Type} (s : PStr) (py : DR (α × Int)) (c : DR (α × Nat)) : Prop :=
  (∃ (v : α) (k : Nat), k ≤ s.length ∧ py = .ok (v, (k : Int)) ∧ c = .ok (v, k)) ∨
  (∃ pe ce, py = .error pe ∧ c = .error ce ∧ ErrRel s pe ce)

theorem ResRel.err_eq {α : Type} {s : PStr} (e : DErr) : ResRel (α := α) s (.error e) (.error e) :=
  Or.inr ⟨e, e, rfl, rfl, Or.inl rfl⟩

theorem findTerm_spec : ∀ (t : PStr) (k : Nat), findTerm t = some k →
    k < t.length ∧ isTerm (t.getD k 0) = true ∧ ∀ j < k, isTerm (t.getD j 0) = false
  | [], k, h => by simp [findTerm] at h
  | c :: t, k, h => by
    simp only [findTerm] at h
    split at h
    · cases h; simp_all
    · cases hf : findTerm t with
      | none => rw [hf] at h; cases h
      | some k' =>
        rw [hf] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
        obtain ⟨h1, h2, h3⟩ := findTerm_spec t k' hf
        refine ⟨by simp; omega, by simpa using h2, ?_⟩
        intro j hj
        cases j with
        | zero => simpa using ‹¬isTerm c = true›
        | succ j => simpa using h3 j (by omega)

theorem findTerm_none : ∀ (t : PStr), findTerm t = none → ∀ c ∈ t, isTerm c = false
  | [], _ => by simp
  | c :: t, h => by
    simp only [findTerm] at h
    by_cases hc : isTerm c = true
    · simp [hc] at h
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, Option.map_eq_none_iff] at h
      intro x hx
      simp at hx
      rcases hx with hx | hx
      · subst hx; simpa using hc
      · exact findTerm_none t h x hx

theorem cFind_found_of (strict : Bool) : ∀ (t : PStr) (k : Nat),
    k < t.length → (t.getD k 0 = 34 ∨ t.getD k 0 = 92) →
    (∀ j < k, t.getD j 0 ≠ 34 ∧ t.getD j 0 ≠ 92 ∧ ¬(t.getD j 0 ≤ 31 ∧ strict = true)) →
    cFind strict t = .found k
  | [], _, h, _, _ => by simp at h
  | c :: t, 0, _, hc, _ => by simp at hc; simp [cFind, hc]
  | c :: t, k + 1, hk, hc, hj => by
    obtain ⟨h1, h2, h3⟩ := hj 0 (by omega)
    simp only [List.getD_cons_zero] at h1 h2 h3
    simp only [cFind, h1, h2, or_self, ↓reduceIte, h3]
    rw [cFind_found_of strict t k (by simp at hk; omega) (by simpa using hc)
      (fun j hj' => by simpa using hj (j + 1) (by omega))]

theorem cFind_ctrl_of : ∀ (t : PStr) (k : Nat),
    k < t.length → t.getD k 0 ≤ 31 → t.getD k 0 ≠ 34 → t.getD k 0 ≠ 92 →
    (∀ j < k, isTerm (t.getD j 0) = false) →
    cFind true t = .ctrl k
  | [], _, h, _, _, _, _ => by simp at h
  | c :: t, 0, _, h1, h2, h3, _ => by
    simp at h1 h2 h3; simp [cFind, h2, h3, h1]
  | c :: t, k + 1, hk, h1, h2, h3, hj => by
    have h0 := hj 0 (by omega)
    simp only [List.getD_cons_zero, isTerm, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
      decide_eq_false_iff_not, Nat.not_lt] at h0
    have : ¬ c ≤ 31 := by omega
    simp only [cFind, h0.1.1, h0.1.2, or_self, ↓reduceIte, this, false_and]
    rw [cFind_ctrl_of t k (by simp at hk; omega) (by simpa using h1) (by simpa using h2) (by simpa using h3)
      (fun j hj' => by simpa using hj (j + 1) (by omega))]

theorem cFind_eof_of (strict : Bool) : ∀ (t : PStr),
    (∀ c ∈ t, c ≠ 34 ∧ c ≠ 92 ∧ ¬(c ≤ 31 ∧ strict = true)) → cFind strict t = .eof
  | [], _ => rfl
  | c :: t, h => by
    have h0 := h c (by simp)
    simp only [cFind, h0.1, h0.2.1, or_self, ↓reduceIte, h0.2.2]
    rw [cFind_eof_of strict t (fun x hx => h x (by simp [hx]))]

theorem cFind_false_ne_ctrl : ∀ (t : PStr) (k : Nat), cFind false t ≠ .ctrl k
  | [], _ => by simp [cFind]
  | c :: t, k => by
    simp only [cFind]
    split
    · simp
    · simp only [Bool.false_eq_true, and_false, ↓reduceIte]
      cases h : cFind false t with
      | found _ => simp
      | ctrl k' => exact absurd h (cFind_false_ne_ctrl t k')
      | eof => simp

/-- `cFind` from a later start, shifted back, when nothing before it stops the scan. -/
theorem cFind_drop (strict : Bool) : ∀ (t : PStr) (j : Nat),
    (∀ i < j, t.getD i 0 ≠ 34 ∧ t.getD i 0 ≠ 92 ∧ ¬(t.getD i 0 ≤ 31 ∧ strict = true)) →
    cFind strict t = (match cFind strict (t.drop j) with
      | .found k => .found (k + j) | .ctrl k => .ctrl (k + j) | .eof => .eof)
  | t, 0, _ => by cases h : cFind strict t <;> simp [h]
  | [], j + 1, _ => by simp [cFind]
  | c :: t, j + 1, h => by
    obtain ⟨h1, h2, h3⟩ := h 0 (by omega)
    simp only [List.getD_cons_zero] at h1 h2 h3
    simp only [cFind, h1, h2, or_self, ↓reduceIte, h3, List.drop_succ_cons]
    rw [cFind_drop strict t j (fun i hi => by simpa using h (i + 1) (by omega))]
    cases cFind strict (t.drop j) <;> simp [Nat.add_assoc]

theorem getD_drop (s : PStr) (e k : Nat) : (s.drop e).getD k 0 = s.getD (e + k) 0 := by
  simp [List.getD_eq_getElem?_getD]

theorem decodeU_ok {s : PStr} {p v : Nat} (h : hex4 s (p + 1) = some v) : decodeUXXXX s p = .ok v := by
  simp [decodeUXXXX, h]

theorem decodeU_bad {s : PStr} {p : Nat} (h : hex4 s (p + 1) = none) :
    decodeUXXXX s p = .error (.jde "Invalid \\uXXXX escape" (p : Int)) := by
  simp [decodeUXXXX, h]

theorem hex4_le {s : PStr} {p v : Nat} (h : hex4 s p = some v) : p + 4 ≤ s.length := by
  unfold hex4 at h
  split at h
  · rename_i a b c d heq
    have := congrArg List.length heq
    simp only [List.length_take, List.length_drop, List.length_cons, List.length_nil] at this
    omega
  · cases h

/-- The C loop's result depends on the writer's contents only. -/
theorem cScanLoop_none (s : PStr) (strict : Bool) (b : Int) (g e : Nat) :
    cScanLoop s strict b g e none = cScanLoop s strict b g e (some []) := by
  cases g with
  | zero => rfl
  | succ g =>
    simp only [cScanLoop]
    cases cFind strict (s.drop e) with
    | ctrl k => rfl
    | eof => rfl
    | found k =>
      simp only [Option.getD_none, Option.getD_some, List.nil_append]
      by_cases hc : s.getD (e + k) 0 = 34
      · simp only [hc, and_self, ↓reduceIte, reduceCtorEq, and_false]
      · simp only [hc, false_and, ↓reduceIte]

/-- The C loop restarted later in the same chunk. -/
theorem cScanLoop_skip (s : PStr) (strict : Bool) (b : Int) (g e j : Nat) (a : PStr)
    (h : ∀ i < j, (s.drop e).getD i 0 ≠ 34 ∧ (s.drop e).getD i 0 ≠ 92 ∧
      ¬((s.drop e).getD i 0 ≤ 31 ∧ strict = true)) :
    cScanLoop s strict b (g + 1) e (some a) =
      cScanLoop s strict b (g + 1) (e + j) (some (a ++ (s.drop e).take j)) := by
  simp only [cScanLoop]
  rw [cFind_drop strict (s.drop e) j h, List.drop_drop]
  cases hf : cFind strict (s.drop (e + j)) with
  | ctrl k =>
    simp only
    congr 3
    omega
  | eof => rfl
  | found k =>
    simp only [reduceCtorEq, and_false, ↓reduceIte, Option.getD_some]
    have e1 : e + (k + j) = e + j + k := by omega
    have e2 : (s.drop e).take (k + j) = (s.drop e).take j ++ (s.drop (e + j)).take k := by
      rw [Nat.add_comm k j, List.take_add, List.drop_drop]
    rw [e1, e2, List.append_assoc]

theorem getD_of_getElem? {s : PStr} {i c : Nat} (h : s[i]? = some c) : s.getD i 0 = c := by
  simp [List.getD_eq_getElem?_getD, h]

theorem take2_eq {s : PStr} {e : Nat} (h : (s.drop e).take 2 = [92, 117]) :
    s.getD e 0 = 92 ∧ s.getD (e + 1) 0 = 117 ∧ e + 2 ≤ s.length := by
  have hl := congrArg List.length h
  simp only [List.length_take, List.length_drop, List.length_cons, List.length_nil] at hl
  have h0 := congrArg (fun l => l.getD 0 0) h
  have h1 := congrArg (fun l => l.getD 1 0) h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop] at h0 h1
  simp at h0 h1
  refine ⟨?_, ?_, by omega⟩
  · simpa [List.getD_eq_getElem?_getD] using h0
  · simpa [List.getD_eq_getElem?_getD] using h1

theorem getElem?_of_lt (s : PStr) {i : Nat} (h : i < s.length) : s[i]? = some (s.getD i 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- C after reading `\u` at `p` (backslash) and `p+1` (`u`) when the four
hex digits are missing or invalid: the error at `p + 1`. -/
theorem c_bad_u (s : PStr) (strict : Bool) (b : Int) (g p : Nat) (a : PStr)
    (h92 : s[p]? = some 92) (h117 : s[p + 1]? = some 117) (hx : hex4 s (p + 2) = none) :
    cScanLoop s strict b (g + 1) p (some a) = .error (.jde "Invalid \\uXXXX escape" ((p + 1 : Nat) : Int)) := by
  have hlt : p + 1 < s.length := (List.getElem?_eq_some_iff.mp h117).1
  have hcf : cFind strict (s.drop p) = .found 0 := by
    apply cFind_found_of strict _ 0 (by simp; omega) (by simp [List.getD_eq_getElem?_getD, h92])
    intro j hj; omega
  simp only [cScanLoop, hcf, Nat.add_zero, List.getD_eq_getElem?_getD, h92, h117, Option.getD_some]
  simp only [reduceCtorEq, and_false, ↓reduceIte, Option.getD_some, Nat.reduceEqDiff]
  have hne : p + 1 ≠ s.length := by omega
  simp only [hne, ↓reduceIte, Nat.add_assoc, Nat.reduceAdd]
  have e1 : p + 2 - 1 = p + 1 := by omega
  have e2 : p + 6 - 5 = p + 1 := by omega
  by_cases hend : p + 6 > s.length
  · simp only [hend, ↓reduceIte, ne_eq, not_true_eq_false, e1]
  · simp only [hend, ↓reduceIte, hx, ne_eq, not_true_eq_false, e2]

/-- C after reading a valid `\uXXXX` at `p` that ends the input. -/
theorem c_last_u (s : PStr) (strict : Bool) (b : Int) (g p u : Nat) (a : PStr)
    (h92 : s[p]? = some 92) (h117 : s[p + 1]? = some 117) (hx : hex4 s (p + 2) = some u)
    (hend : p + 6 = s.length) :
    cScanLoop s strict b (g + 2) p (some a) = .error (.jde "Unterminated string starting at" b) := by
  have hlt : p + 1 < s.length := (List.getElem?_eq_some_iff.mp h117).1
  have hcf : cFind strict (s.drop p) = .found 0 := by
    apply cFind_found_of strict _ 0 (by simp; omega) (by simp [List.getD_eq_getElem?_getD, h92])
    intro j hj; omega
  simp only [cScanLoop, hcf, Nat.add_zero, List.getD_eq_getElem?_getD, h92, h117, Option.getD_some]
  simp only [reduceCtorEq, and_false, ↓reduceIte, Option.getD_some, Nat.reduceEqDiff]
  have hne : p + 1 ≠ s.length := by omega
  have hend' : ¬ (p + 6 > s.length) := by omega
  simp only [hne, ↓reduceIte, Nat.add_assoc, Nat.reduceAdd, hend', hx]
  have h6 : ¬ (p + 6 + 6 < s.length) := by omega
  simp only [h6, false_and, and_false, ↓reduceIte]
  rw [hend, List.drop_length]
  rfl

/-- Python on the same input (a valid `\uXXXX` at `p` that ends the input). -/
theorem py_last_u (s : PStr) (strict : Bool) (b : Int) (f p u : Nat) (a : PStr)
    (h92 : s[p]? = some 92) (h117 : s[p + 1]? = some 117) (hx : hex4 s (p + 2) = some u)
    (hend : p + 6 = s.length) :
    pyScanLoop s strict b (f + 2) p a = .error (.jde "Unterminated string starting at" b) := by
  have hft : findTerm (s.drop p) = some 0 := by
    rw [List.drop_eq_getElem_cons (by have := (List.getElem?_eq_some_iff.mp h92).1; omega)]
    simp [findTerm, (List.getElem?_eq_some_iff.mp h92).2, isTerm]
  simp only [pyScanLoop, hft, Nat.add_zero, List.getD_eq_getElem?_getD, h92, Option.getD_some]
  simp only [Nat.reduceEqDiff, ↓reduceIte, ne_eq, not_true_eq_false, h117, not_false_eq_true]
  have h2 : decodeUXXXX s (p + 1) = .ok u := decodeU_ok hx
  simp only [h2]
  have hd : (s.drop (p + 1 + 5)).take 2 = [] := by
    rw [List.drop_eq_nil_of_le (by omega)]; rfl
  simp only [hd, reduceCtorEq, and_false, ↓reduceIte]
  have hd2 : s.drop (p + 1 + 5) = [] := List.drop_eq_nil_of_le (by omega)
  simp [pyScanLoop, hd2, findTerm]

theorem take2_of {s : PStr} {e : Nat} (h1 : s[e]? = some 92) (h2 : s[e + 1]? = some 117) :
    (s.drop e).take 2 = [92, 117] := by
  have hl := (List.getElem?_eq_some_iff.mp h2).1
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]
  simp [(List.getElem?_eq_some_iff.mp h1).2, (List.getElem?_eq_some_iff.mp h2).2]

theorem take2_eq' {s : PStr} {e : Nat} (h : (s.drop e).take 2 = [92, 117]) :
    s[e]? = some 92 ∧ s[e + 1]? = some 117 := by
  have h0 := congrArg (fun l => l[0]?) h
  have h1 := congrArg (fun l => l[1]?) h
  simp only [List.getElem?_take, List.getElem?_drop] at h0 h1
  simp at h0 h1
  exact ⟨h0, h1⟩

theorem pyScanLoop_end (s : PStr) (strict : Bool) (b : Int) (f : Nat) (a : PStr) :
    pyScanLoop s strict b (f + 1) s.length a = .error (.jde "Unterminated string starting at" b) := by
  simp [pyScanLoop, findTerm]

/-- The main string lemma: the Python loop against the C loop, both with enough fuel. -/
theorem scanLoop_rel (s : PStr) (strict : Bool) (b : Int) :
    ∀ (f g e : Nat) (a : PStr), s.length + 1 - e ≤ f → s.length + 1 - e ≤ g → e ≤ s.length →
    ResRel s (pyScanLoop s strict (b : Int) f e a) (cScanLoop s strict b g e (some a)) := by
  intro f
  induction f with
  | zero => intro g e a hf; omega
  | succ f ih =>
    intro g e a hf hg he
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    cases hft : findTerm (s.drop e) with
    | none =>
      have hc : cFind strict (s.drop e) = .eof := by
        apply cFind_eof_of
        intro c hc
        have := findTerm_none _ hft c hc
        simp [isTerm] at this; omega
      simp only [pyScanLoop, cScanLoop, hft, hc]
      exact ResRel.err_eq _
    | some k =>
      obtain ⟨hk, hterm, hbefore⟩ := findTerm_spec _ k hft
      simp only [List.length_drop] at hk
      rw [getD_drop] at hterm
      have hbefore' : ∀ j < k, (s.drop e).getD j 0 ≠ 34 ∧ (s.drop e).getD j 0 ≠ 92 ∧
          ¬((s.drop e).getD j 0 ≤ 31 ∧ strict = true) := by
        intro j hj
        have := hbefore j hj
        simp [isTerm] at this ⊢; omega
      have hs0 := getElem?_of_lt s (show e + k < s.length by omega)
      generalize hc0 : s.getD (e + k) 0 = c0 at hs0 hterm
      by_cases hq : c0 = 34 ∨ c0 = 92
      · rw [cScanLoop_skip s strict b g e k a hbefore']
        have hcf0 : cFind strict (s.drop (e + k)) = .found 0 := by
          apply cFind_found_of strict _ 0 (by simp; omega)
          · simp [List.getD_eq_getElem?_getD, hs0]; exact hq
          · intro j hj; omega
        rcases hq with hq | hq
        · -- closing quote
          subst hq
          left
          refine ⟨a ++ (s.drop e).take k, e + k + 1, by omega, ?_, ?_⟩
          · simp [pyScanLoop, hft, List.getD_eq_getElem?_getD, hs0]
          · simp [cScanLoop, hcf0, List.getD_eq_getElem?_getD, hs0]
        · -- backslash
          subst hq
          simp only [pyScanLoop, decodeUXXXX, cScanLoop, hft, hcf0, List.getD_eq_getElem?_getD, hs0, Option.getD_some,
            Nat.add_zero, List.take_zero, List.append_nil, Nat.reduceEqDiff, ↓reduceIte, ne_eq,
            not_true_eq_false, not_false_eq_true, reduceCtorEq, and_false]
          cases hesc : s[e + k + 1]? with
          | none =>
            have hlen : e + k + 1 = s.length := by
              have := List.getElem?_eq_none_iff.mp hesc; omega
            simp [hlen]
            exact ResRel.err_eq _
          | some esc =>
            have hlt : e + k + 1 < s.length := (List.getElem?_eq_some_iff.mp hesc).1
            have hne : e + k + 1 ≠ s.length := by omega
            simp only [hne, ↓reduceIte, Option.getD_some]
            have q1 : e + k + 1 + 1 + 4 = e + k + 1 + 5 := by omega
            have q2 : e + k + 1 + 1 + 4 + 6 - 5 = e + k + 1 + 5 + 1 := by omega
            have q3 : e + k + 1 + 1 + 4 - 5 = e + k + 1 := by omega
            have q4 : e + k + 1 + 1 - 1 = e + k + 1 := by omega
            have q5 : e + k + 1 + 1 + 4 + 1 = e + k + 1 + 5 + 1 := by omega
            have q6 : e + k + 1 + 1 + 4 + 2 = e + k + 1 + 5 + 2 := by omega
            have q7 : e + k + 1 + 5 + 1 + 1 = e + k + 1 + 5 + 2 := rfl
            simp only [q1, q2, q3, q4, q5, q6, q7]
            by_cases hu : esc = 117
            · subst hu
              simp only [not_true_eq_false, ↓reduceIte]
              by_cases hend : e + k + 1 + 5 > s.length
              · have hx : hex4 s (e + k + 1 + 1) = none := by
                  cases h4 : hex4 s (e + k + 1 + 1) with
                  | none => rfl
                  | some _ => have := hex4_le h4; omega
                simp only [hx, hend, ↓reduceIte]
                exact ResRel.err_eq _
              · simp only [hend, ↓reduceIte]
                cases hx : hex4 s (e + k + 1 + 1) with
                | none => exact ResRel.err_eq _
                | some uni =>
                  have he2 : e + k + 1 + 5 ≤ s.length := by have := hex4_le hx; omega
                  simp only
                  by_cases hhi : 55296 ≤ uni ∧ uni ≤ 56319
                  · by_cases ht : (s.drop (e + k + 1 + 5)).take 2 = [92, 117]
                    · obtain ⟨h92, h117⟩ := take2_eq' ht
                      have hlt2 : e + k + 1 + 5 + 1 < s.length := (List.getElem?_eq_some_iff.mp h117).1
                      by_cases h6 : e + k + 1 + 5 + 6 < s.length
                      · simp only [hhi, ht, h6, h92, h117, Option.getD_some, and_self, ↓reduceIte]
                        cases hx2 : hex4 s (e + k + 1 + 5 + 2) with
                        | none => exact ResRel.err_eq _
                        | some uni2 =>
                          simp only
                          have := hex4_le hx2
                          split
                          · exact ih g _ _ (by omega) (by omega) (by omega)
                          · exact ih g _ _ (by omega) (by omega) (by omega)
                      · simp only [hhi, ht, h6, and_self, ↓reduceIte, false_and, and_false]
                        obtain ⟨g', rfl⟩ : ∃ g', g = g' + 2 := ⟨g - 2, by omega⟩
                        obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
                        cases hx2 : hex4 s (e + k + 1 + 5 + 2) with
                        | none =>
                          rw [c_bad_u s strict b (g' + 1) (e + k + 1 + 5) _ h92 h117 hx2]
                          right; refine ⟨_, _, rfl, rfl, Or.inl ?_⟩
                          simp
                        | some uni2 =>
                          have := hex4_le hx2
                          have hend6 : e + k + 1 + 5 + 6 = s.length := by omega
                          rw [c_last_u s strict b g' (e + k + 1 + 5) uni2 _ h92 h117 hx2 hend6]
                          simp only
                          split
                          · rw [hend6, show f' + 2 = (f' + 1) + 1 by omega, pyScanLoop_end]
                            exact ResRel.err_eq _
                          · rw [py_last_u s strict (b : Int) f' (e + k + 1 + 5) uni2 _ h92 h117 hx2 hend6]
                            exact ResRel.err_eq _
                    · have hc : ¬ (e + k + 1 + 5 + 6 < s.length ∧ s[e + k + 1 + 5]?.getD 0 = 92 ∧
                          s[e + k + 1 + 5 + 1]?.getD 0 = 117) := by
                        rintro ⟨h6, h1, h2⟩
                        apply ht
                        apply take2_of
                        · rw [List.getElem?_eq_getElem (by omega)] at h1 ⊢; simpa using h1
                        · rw [List.getElem?_eq_getElem (by omega)] at h2 ⊢; simpa using h2
                      simp only [hhi, ht, and_false, ↓reduceIte, true_and, hc]
                      exact ih g _ _ (by omega) (by omega) (by omega)
                  · have n1 : ¬ (55296 ≤ uni ∧ uni ≤ 56319 ∧ (s.drop (e + k + 1 + 5)).take 2 = [92, 117]) :=
                      fun h => hhi ⟨h.1, h.2.1⟩
                    have n2 : ¬ (55296 ≤ uni ∧ uni ≤ 56319 ∧ e + k + 1 + 5 + 6 < s.length ∧
                        s[e + k + 1 + 5]?.getD 0 = 92 ∧ s[e + k + 1 + 5 + 1]?.getD 0 = 117) :=
                      fun h => hhi ⟨h.1, h.2.1⟩
                    simp only [n1, n2, ↓reduceIte]
                    exact ih g _ _ (by omega) (by omega) (by omega)
            · simp only [hu, not_false_eq_true, ↓reduceIte]
              cases hb : backslash esc with
              | none =>
                right
                refine ⟨_, _, rfl, rfl, Or.inr (Or.inr (Or.inr ⟨e + k, esc, hs0, hesc, ?_, ?_⟩))⟩
                · congr 2
                · congr 1
              | some ch =>
                exact ih g (e + k + 1 + 1) _ (by omega) (by omega) (by omega)
      · -- a control character
        have hlt32 : c0 < 32 := by simp [isTerm] at hterm; omega
        have h34 : c0 ≠ 34 := fun h => hq (Or.inl h)
        have h92 : c0 ≠ 92 := fun h => hq (Or.inr h)
        simp only [pyScanLoop, hft, List.getD_eq_getElem?_getD, hs0, Option.getD_some, h34, h92,
          ↓reduceIte, ne_eq, not_false_eq_true]
        cases strict with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          have hskip : ∀ i < k + 1, (s.drop e).getD i 0 ≠ 34 ∧ (s.drop e).getD i 0 ≠ 92 ∧
              ¬((s.drop e).getD i 0 ≤ 31 ∧ false = true) := by
            intro i hi
            by_cases hik : i < k
            · exact hbefore' i hik
            · have : i = k := by omega
              subst this
              rw [getD_drop, hc0]
              simp [h34, h92]
          rw [cScanLoop_skip s false b g e (k + 1) a hskip]
          have htk : (s.drop e).take (k + 1) = (s.drop e).take k ++ [c0] := by
            rw [List.take_add_one, List.getElem?_drop, hs0]; rfl
          rw [htk, ← List.append_assoc]
          exact ih (g + 1) (e + k + 1) _ (by omega) (by omega) (by omega)
        | true =>
          have hcf : cFind true (s.drop e) = .ctrl k := by
            apply cFind_ctrl_of _ k (by simp; omega)
            · rw [getD_drop, hc0]; omega
            · rw [getD_drop, hc0]; exact h34
            · rw [getD_drop, hc0]; exact h92
            · exact hbefore
          simp only [cScanLoop, hcf, ↓reduceIte]
          right
          refine ⟨_, _, rfl, rfl, Or.inr (Or.inr (Or.inl ⟨e + k, c0, hs0, hlt32, rfl, ?_⟩))⟩
          congr 1
          omega

end PyLean.JsonMod
