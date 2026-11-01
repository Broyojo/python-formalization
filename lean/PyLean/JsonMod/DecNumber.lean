import PyLean.JsonMod.DecLemmas

/-!
`NUMBER_RE` (scanner.py) and `_match_number_unicode` (Modules/_json.c) match
the same text.
-/

namespace PyLean.JsonMod

open PyLean

theorem drop_cons {s : PStr} {i : Nat} (h : i < s.length) : s.drop i = s.getD i 0 :: s.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons h]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem drop_nil {s : PStr} {i : Nat} (h : s.length ≤ i) : s.drop i = [] := List.drop_eq_nil_of_le h

theorem digitsLen_le (t : PStr) : digitsLen t ≤ t.length := by
  induction t with
  | nil => simp [digitsLen]
  | cons c t ih => simp only [digitsLen]; split <;> simp <;> omega

theorem digitsLen_cons (c : Nat) (t : PStr) :
    digitsLen (c :: t) = if isDigit c then digitsLen t + 1 else 0 := rfl

theorem length_take_digits (t : PStr) : (t.take (digitsLen t)).length = digitsLen t := by
  simp [Nat.min_eq_left (digitsLen_le t)]

theorem reInt_cons (c : Nat) (r : PStr) :
    reInt (c :: r) = if c = 48 then some [48] else if 49 ≤ c ∧ c ≤ 57 then some (c :: r.take (digitsLen r)) else none := by
  by_cases h : c = 48
  · subst h; rfl
  · simp [reInt, h]

theorem reFrac_cons (c : Nat) (r : PStr) :
    reFrac (c :: r) = if c = 46 then (if digitsLen r = 0 then [] else 46 :: r.take (digitsLen r)) else [] := by
  by_cases h : c = 46
  · subst h; rfl
  · simp [reFrac, h]

theorem reSign_cons (c : Nat) (r : PStr) :
    reSign (c :: r) = if c = 45 then ([45], r) else ([], c :: r) := by
  by_cases h : c = 45
  · subst h; rfl
  · simp [reSign, h]

theorem reExp_sign (e c : Nat) (r : PStr) (he : e = 101 ∨ e = 69) (hc : c = 45 ∨ c = 43) :
    reExp (e :: c :: r) = if digitsLen r = 0 then [] else e :: c :: r.take (digitsLen r) := by
  rcases hc with rfl | rfl <;> simp [reExp, he]

theorem reExp_nosign (e : Nat) (r : PStr) (he : e = 101 ∨ e = 69) (hc : ∀ c r', r = c :: r' → c ≠ 45 ∧ c ≠ 43) :
    reExp (e :: r) = if digitsLen r = 0 then [] else e :: r.take (digitsLen r) := by
  cases r with
  | nil => simp [reExp, he, digitsLen]
  | cons c r' =>
    have := hc c r' rfl
    simp [reExp, he, this.1, this.2]

theorem reExp_not (e : Nat) (r : PStr) (he : ¬(e = 101 ∨ e = 69)) : reExp (e :: r) = [] := by
  simp [reExp, he]

/-- `(?:0|[1-9][0-9]*)` and the integer branch of `_match_number_unicode`. -/
theorem reInt_twin (s : PStr) (a : Nat) (h : a < s.length) :
    (reInt (s.drop a) = none ∧ cNumInt s a = none) ∨
    (∃ ip, reInt (s.drop a) = some ip ∧ cNumInt s a = some (a + ip.length) ∧
      ip = (s.drop a).take ip.length) := by
  rw [drop_cons h, reInt_cons]
  simp only [cNumInt]
  generalize s.getD a 0 = c
  by_cases h48 : c = 48
  · subst h48
    right
    exact ⟨[48], by simp, by simp, by simp⟩
  · by_cases h19 : 49 ≤ c ∧ c ≤ 57
    · right
      refine ⟨c :: (s.drop (a + 1)).take (digitsLen (s.drop (a + 1))), by simp [h48, h19], ?_, ?_⟩
      · simp only [h19, and_self, ↓reduceIte, List.length_cons, length_take_digits]
        congr 1; omega
      · simp [length_take_digits]
    · left
      simp [h19, h48]

theorem digitsLen_digit (s : PStr) (i : Nat) : ∀ j < digitsLen (s.drop i), isDigit (s.getD (i + j) 0) = true := by
  induction h : s.length - i generalizing i with
  | zero =>
    intro j hj
    rw [drop_nil (s := s) (i := i) (by omega)] at hj
    simp [digitsLen] at hj
  | succ n ih =>
    intro j hj
    rw [drop_cons (s := s) (i := i) (by omega), digitsLen_cons] at hj
    split at hj
    · rename_i hd
      cases j with
      | zero => simpa using hd
      | succ j =>
        have := ih (i + 1) (by omega) j (by omega)
        rwa [show i + 1 + j = i + (j + 1) by omega] at this
    · simp at hj

theorem digit_last (s : PStr) (i : Nat) (h : 0 < digitsLen (s.drop i)) :
    isDigit (s.getD (i + digitsLen (s.drop i) - 1) 0) = true := by
  have := digitsLen_digit s i (digitsLen (s.drop i) - 1) (by omega)
  rwa [show i + (digitsLen (s.drop i) - 1) = i + digitsLen (s.drop i) - 1 by omega] at this

/-- `(\.[0-9]+)?` and the fraction branch. -/
theorem reFrac_twin (s : PStr) (b : Nat) :
    cNumFrac s b = (b + (reFrac (s.drop b)).length, decide (reFrac (s.drop b) ≠ [])) ∧
    reFrac (s.drop b) = (s.drop b).take (reFrac (s.drop b)).length := by
  by_cases hb : b < s.length
  · rw [drop_cons hb, reFrac_cons]
    simp only [cNumFrac]
    generalize hc : s.getD b 0 = c
    by_cases h46 : c = 46
    · subst h46
      by_cases hb1 : b + 1 < s.length
      · rw [drop_cons hb1, digitsLen_cons, show b + 1 + 1 = b + 2 from rfl]
        generalize hd : s.getD (b + 1) 0 = d
        by_cases hdig : isDigit d = true
        · simp only [hdig, ↓reduceIte, Nat.add_one_ne_zero, List.length_cons, ne_eq, reduceCtorEq,
            not_false_eq_true, decide_true, hb1, and_self, List.take_succ_cons, length_take_digits]
          refine ⟨?_, trivial⟩
          simp only [Prod.mk.injEq, and_true]
          omega
        · simp [hdig]
      · rw [drop_nil (s := s) (i := b + 1) (by omega)]
        simp [digitsLen, hb1]
    · simp [h46]
  · rw [drop_nil (s := s) (i := b) (by omega)]
    simp [reFrac, cNumFrac]
    omega

/-- `([eE][-+]?[0-9]+)?` and the exponent branch (with its backtracking). -/
theorem reExp_twin (s : PStr) (c : Nat) (fl : Bool) :
    cNumExp s c fl = (c + (reExp (s.drop c)).length, fl || decide (reExp (s.drop c) ≠ [])) ∧
    reExp (s.drop c) = (s.drop c).take (reExp (s.drop c)).length := by
  by_cases hc : c < s.length
  · rw [drop_cons hc]
    generalize he : s.getD c 0 = e
    have he' : s[c]? = some e := by
      rw [← he]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]
    have heNotDigit : (e = 101 ∨ e = 69) → isDigit e = false := by
      rintro (rfl | rfl) <;> rfl
    by_cases hee : e = 101 ∨ e = 69
    · by_cases hc1 : c + 1 < s.length
      · rw [drop_cons hc1, show c + 1 + 1 = c + 2 from rfl]
        generalize hg : s.getD (c + 1) 0 = g
        have hg' : s[c + 1]? = some g := by
          rw [← hg]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc1]
        by_cases hsg : g = 45 ∨ g = 43
        · have hgNotDigit : isDigit g = false := by rcases hsg with rfl | rfl <;> rfl
          rw [reExp_sign e g _ hee hsg]
          by_cases hc2 : c + 2 < s.length
          · by_cases hD0 : digitsLen (s.drop (c + 2)) = 0
            · simp only [hD0, ↓reduceIte, List.length_nil, Nat.add_zero, ne_eq, not_true_eq_false,
                decide_false, Bool.or_false, List.take_zero, and_true]
              simp only [cNumExp, hc1, he, hee, and_self, ↓reduceIte, hg, hsg, show c + 1 + 1 = c + 2 from rfl,
                hc2, hD0, Nat.add_zero, Nat.add_sub_cancel]
              simp [hg', hgNotDigit]
            · simp only [hD0, ↓reduceIte, List.length_cons, length_take_digits, ne_eq, reduceCtorEq,
                not_false_eq_true, decide_true, Bool.or_true, List.take_succ_cons, and_true]
              simp only [cNumExp, hc1, he, hee, and_self, ↓reduceIte, hg, hsg, show c + 1 + 1 = c + 2 from rfl,
                hc2]
              have hl := digit_last s (c + 2) (by omega)
              simp only [hl, ↓reduceIte, Prod.mk.injEq, and_true]
              omega
          · have hD0 : digitsLen (s.drop (c + 2)) = 0 := by
              rw [drop_nil (s := s) (i := c + 2) (by omega)]; rfl
            simp only [hD0, ↓reduceIte, List.length_nil, Nat.add_zero, ne_eq, not_true_eq_false,
              decide_false, Bool.or_false, List.take_zero, and_true]
            simp only [cNumExp, hc1, he, hee, and_self, ↓reduceIte, show c + 1 + 1 = c + 2 from rfl, hc2,
              false_and]
            rw [drop_cons hc1, digitsLen_cons, hg, hgNotDigit]
            simp [he', heNotDigit hee]
        · have hns : ∀ c' r', g :: s.drop (c + 2) = c' :: r' → c' ≠ 45 ∧ c' ≠ 43 := by
            intro c' r' h; simp at h; omega
          rw [reExp_nosign e _ hee hns]
          have hr : g :: s.drop (c + 2) = s.drop (c + 1) := by rw [drop_cons hc1, hg]
          rw [hr]
          by_cases hD0 : digitsLen (s.drop (c + 1)) = 0
          · simp only [hD0, ↓reduceIte, List.length_nil, Nat.add_zero, ne_eq, not_true_eq_false,
              decide_false, Bool.or_false, List.take_zero, and_true]
            simp only [cNumExp, hc1, he, hee, and_self, ↓reduceIte, hg, hsg, and_false, hD0,
              Nat.add_zero, Nat.add_sub_cancel]
            simp [he', heNotDigit hee]
          · simp only [hD0, ↓reduceIte, List.length_cons, length_take_digits, ne_eq, reduceCtorEq,
              not_false_eq_true, decide_true, Bool.or_true, List.take_succ_cons, and_true]
            simp only [cNumExp, hc1, he, hee, and_self, ↓reduceIte, hg, hsg, and_false]
            have hl := digit_last s (c + 1) (by omega)
            simp only [hl, ↓reduceIte, Prod.mk.injEq, and_true]
            omega
      · rw [drop_nil (s := s) (i := c + 1) (by omega)]
        rw [reExp_nosign e [] hee (by simp)]
        simp [digitsLen, cNumExp, hc1]
    · rw [reExp_not e _ hee]
      have : ¬ (c + 1 < s.length ∧ (s.getD c 0 = 101 ∨ s.getD c 0 = 69)) := by
        rw [he]; exact fun h => hee h.2
      simp only [cNumExp, this, ↓reduceIte, List.length_nil, Nat.add_zero, ne_eq, not_true_eq_false,
        decide_false, Bool.or_false, List.take_zero, and_self]
  · rw [drop_nil (s := s) (i := c) (by omega)]
    simp [reExp, cNumExp]
    omega

theorem take_split (s : PStr) (a m n : Nat) :
    (s.drop a).take (m + n) = (s.drop a).take m ++ (s.drop (a + m)).take n := by
  rw [List.take_add, List.drop_drop]

/-- After the sign: the integer, fraction and exponent at `a`. -/
theorem numberRest_twin (cfg : DCfg) (s : PStr) (start a : Nat) (sign : PStr) (ha : a < s.length)
    (hsign : sign = (s.drop start).take sign.length) (hsa : a = start + sign.length)
    (hsg : cNumSign s start = some a) :
    (reInt (s.drop a) = none ∧ cMatchNumber cfg s start = .error (.stop start)) ∨
    (∃ ip, reInt (s.drop a) = some ip ∧
      cMatchNumber cfg s start =
      (if reFrac ((s.drop a).drop ip.length) ≠ [] ∨
          reExp (((s.drop a).drop ip.length).drop (reFrac ((s.drop a).drop ip.length)).length) ≠ [] then
        .ok (.hook .float (sign ++ ip ++ reFrac ((s.drop a).drop ip.length) ++
          reExp (((s.drop a).drop ip.length).drop (reFrac ((s.drop a).drop ip.length)).length)),
          start + ((sign ++ ip).length + (reFrac ((s.drop a).drop ip.length)).length +
            (reExp (((s.drop a).drop ip.length).drop (reFrac ((s.drop a).drop ip.length)).length)).length))
       else (parseInt cfg (sign ++ ip)).map (·, start + ((sign ++ ip).length +
          (reFrac ((s.drop a).drop ip.length)).length +
          (reExp (((s.drop a).drop ip.length).drop (reFrac ((s.drop a).drop ip.length)).length)).length)))) := by
  rcases reInt_twin s a ha with ⟨h1, h2⟩ | ⟨ip, h1, h2, h3⟩
  · left
    refine ⟨h1, ?_⟩
    unfold cMatchNumber
    rw [hsg]
    simp only [h2]
  · right
    refine ⟨ip, h1, ?_⟩
    unfold cMatchNumber
    rw [hsg]
    simp only [List.drop_drop, h2]
    obtain ⟨hf1, hf2⟩ := reFrac_twin s (a + ip.length)
    rw [hf1]
    generalize hfr : reFrac (s.drop (a + ip.length)) = fr at hf2
    obtain ⟨he1, he2⟩ := reExp_twin s (a + ip.length + fr.length) (decide (fr ≠ []))
    rw [he1]
    generalize hex : reExp (s.drop (a + ip.length + fr.length)) = ex at he2
    simp only [List.length_append]
    have hnum : (s.drop start).take (a + ip.length + fr.length + ex.length - start) = sign ++ ip ++ fr ++ ex := by
      rw [show a + ip.length + fr.length + ex.length - start =
        sign.length + ip.length + fr.length + ex.length by omega]
      have p1 : (s.drop start).take sign.length = sign := hsign.symm
      have p2 : (s.drop (start + sign.length)).take ip.length = ip := by rw [← hsa]; exact h3.symm
      have p3 : (s.drop (start + (sign.length + ip.length))).take fr.length = fr := by
        rw [← Nat.add_assoc, ← hsa]; exact hf2.symm
      have p4 : (s.drop (start + (sign.length + ip.length + fr.length))).take ex.length = ex := by
        rw [show start + (sign.length + ip.length + fr.length) = a + ip.length + fr.length by omega]
        exact he2.symm
      rw [take_split, take_split, take_split, p1, p2, p3, p4]
    rw [hnum]
    by_cases hfl : fr ≠ [] ∨ ex ≠ []
    · have : (decide (fr ≠ []) || decide (ex ≠ [])) = true := by
        rcases hfl with h | h <;> simp [h]
      simp only [this, ↓reduceIte, hfl]
      rw [show a + ip.length + fr.length + ex.length =
        start + (sign.length + ip.length + fr.length + ex.length) by omega]
    · have h1 : fr = [] := by simp at hfl; exact hfl.1
      have h2 : ex = [] := by simp at hfl; exact hfl.2
      subst h1; subst h2
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.or_self, Bool.false_eq_true,
        ↓reduceIte, or_self, List.append_nil, List.length_nil, Nat.add_zero]
      rw [show a + ip.length = start + (sign.length + ip.length) by omega]

/-- `NUMBER_RE.match(s, idx)` and `_match_number_unicode(s, idx)` match the same
text and produce the same value. -/
theorem matchNumber_twin (cfg : DCfg) (s : PStr) (idx : Nat) (h : idx < s.length) :
    (numberRe (s.drop idx) = none ∧ cMatchNumber cfg s idx = .error (.stop idx)) ∨
    (∃ i fr ex, numberRe (s.drop idx) = some (i, fr, ex) ∧
      cMatchNumber cfg s idx =
        (if fr ≠ [] ∨ ex ≠ [] then .ok (.hook .float (i ++ fr ++ ex), idx + (i.length + fr.length + ex.length))
         else (parseInt cfg i).map (·, idx + (i.length + fr.length + ex.length)))) := by
  have hd := drop_cons h
  rw [List.getD_eq_getElem?_getD] at hd
  by_cases hs : s[idx]?.getD 0 = 45
  · by_cases h1 : idx + 1 ≥ s.length
    · left
      refine ⟨?_, by simp [cMatchNumber, cNumSign, List.getD_eq_getElem?_getD, hs, h1]⟩
      simp only [numberRe, hd, reSign_cons, hs, ↓reduceIte]
      rw [drop_nil (s := s) (i := idx + 1) (by omega)]
      rfl
    · have hsign : [45] = (s.drop idx).take [45].length := by rw [hd, hs]; rfl
      have hsg : cNumSign s idx = some (idx + 1) := by
        simp [cNumSign, List.getD_eq_getElem?_getD, hs, h1]
      rcases numberRest_twin cfg s idx (idx + 1) [45] (by omega) hsign rfl hsg with ⟨n1, n2⟩ | ⟨ip, n1, n2⟩
      · left
        refine ⟨?_, n2⟩
        simp [numberRe, hd, reSign_cons, hs, n1]
      · right
        refine ⟨[45] ++ ip, reFrac ((s.drop (idx + 1)).drop ip.length),
          reExp (((s.drop (idx + 1)).drop ip.length).drop (reFrac ((s.drop (idx + 1)).drop ip.length)).length),
          by simp [numberRe, hd, reSign_cons, hs, n1], ?_⟩
        rw [n2]
  · have hsign : ([] : PStr) = (s.drop idx).take ([] : PStr).length := by simp
    have hsg : cNumSign s idx = some idx := by
      simp [cNumSign, List.getD_eq_getElem?_getD, hs]
    rcases numberRest_twin cfg s idx idx [] h hsign rfl hsg with ⟨n1, n2⟩ | ⟨ip, n1, n2⟩
    · left
      refine ⟨?_, n2⟩
      simp only [numberRe, hd, reSign_cons, hs, ↓reduceIte]
      rw [← hd, n1]
    · right
      refine ⟨[] ++ ip, reFrac ((s.drop idx).drop ip.length),
        reExp (((s.drop idx).drop ip.length).drop (reFrac ((s.drop idx).drop ip.length)).length), ?_, ?_⟩
      · simp only [numberRe, hd, reSign_cons, hs, ↓reduceIte]
        rw [← hd, n1]
      · rw [n2]

end PyLean.JsonMod
