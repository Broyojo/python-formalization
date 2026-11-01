import PyLean.JsonMod.RoundTrip

/-!
`py_scanstring` reads the text written by `py_encode_basestring(_ascii)` back:
exactly with `ensure_ascii=False`, and up to joined surrogate pairs (`mergeSurr`)
with `ensure_ascii=True`.
-/

namespace PyLean.JsonMod

open PyLean

/-- An escaped high surrogate followed by an escape that is not a low surrogate. -/
theorem loop_u_nolow (s : PStr) (strict : Bool) (b : Int) (f e n m : Nat) (a R : PStr)
    (hs : s.drop e = uEsc n ++ uEsc m ++ R) (hn : n < 0x10000) (hm : m < 0x10000)
    (hl : isLow m = false) :
    pyScanLoop s strict b (f + 1) e a = pyScanLoop s strict b f (e + 6) (a ++ [n]) := by
  have hs' : s.drop e = uEsc n ++ (uEsc m ++ R) := by rw [hs, List.append_assoc]
  by_cases hh : isHigh n = true
  · have hf : findTerm (s.drop e) = some 0 := by rw [hs']; simp [findTerm, isTerm, uEsc]
    obtain ⟨h0, h1⟩ := uEsc_nth n _ s e hs'
    have hx := hex4_uEsc s e n _ hs' hn
    have hd := drop_six hs'
    have hx2 := hex4_uEsc s (e + 6) m R hd hm
    have ht : (s.drop (e + 6)).take 2 = [92, 117] := by rw [hd]; simp [uEsc]
    simp only [isHigh, isLow, Bool.and_eq_true, decide_eq_true_eq, Bool.and_eq_false_iff,
      decide_eq_false_iff_not] at hh hl
    have hnl : ¬ (0xdc00 ≤ m ∧ m ≤ 0xdfff) := by omega
    have e6 : e + 0 + 1 + 5 = e + 6 := by omega
    have e2 : e + 0 + 1 + 1 = e + 2 := by omega
    simp only [pyScanLoop, hf, List.getD_eq_getElem?_getD]
    simp [h0, h1, e2, hx, e6, ht, hh, hx2, hnl]
  · exact loop_u s strict b f e n a _ hs' hn (Or.inl (by simpa using hh))

theorem mergeSurr_notHigh (c : Nat) (t : PStr) (h : isHigh c = false) :
    mergeSurr (c :: t) = c :: mergeSurr t := by
  cases t with
  | nil => rfl
  | cons d t => simp [mergeSurr, h]

theorem escA_low {c : Nat} (h : isLow c = true) : escA c = uEsc c := by
  simp only [isLow, Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 : ¬ (32 ≤ c ∧ c ≤ 126) := by omega
  have h2 : pyAsciiReplace c = uEsc c := by
    have n1 : c ≠ 92 := by omega
    have n2 : c ≠ 34 := by omega
    have n3 : c ≠ 8 := by omega
    have n4 : c ≠ 12 := by omega
    have n5 : c ≠ 10 := by omega
    have n6 : c ≠ 13 := by omega
    have n7 : c ≠ 9 := by omega
    have n8 : ¬ c < 32 := by omega
    have n9 : c < 0x10000 := by omega
    simp [pyAsciiReplace, escDct, n1, n2, n3, n4, n5, n6, n7, n8, n9]
  simp [escA, h1, h2]

theorem backslash_le {x y : Nat} (hb : backslash x = some y) : y ≤ 92 := by
  unfold backslash at hb
  repeat' (first | (split at hb) | (cases hb; omega) | cases hb)

/-- `ensure_ascii=True`: `py_scanstring` reads the escaped text back as
`mergeSurr t`. -/
theorem loopA (s : PStr) (strict : Bool) (b : Int) : ∀ (n : Nat) (t : PStr) (f e : Nat) (a rest : PStr),
    t.length ≤ n → t.length + 1 ≤ f → (∀ c ∈ t, c ≤ 0x10FFFF) →
    s.drop e = t.flatMap escA ++ 34 :: rest →
    pyScanLoop s strict b f e a =
      .ok (a ++ mergeSurr t, ((e + (t.flatMap escA).length + 1 : Nat) : Int)) := by
  intro n
  induction n with
  | zero =>
    intro t f e a rest hn hf _ hs
    obtain rfl : t = [] := List.length_eq_zero_iff.mp (by omega)
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    simp only [List.flatMap_nil, List.nil_append] at hs
    have h0 : s[e]? = some 34 := by
      have := congrArg (fun l => l[0]?) hs; simpa [List.getElem?_drop] using this
    have hft : findTerm (s.drop e) = some 0 := by rw [hs]; simp [findTerm, isTerm]
    simp [pyScanLoop, hft, List.getD_eq_getElem?_getD, h0, mergeSurr]
  | succ n ih =>
    intro t f e a rest hn hf hok hs
    cases t with
    | nil => exact ih [] f e a rest (by simp) hf hok hs
    | cons c t' =>
      obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
      have hc : c ≤ 0x10FFFF := hok c (by simp)
      have hok' : ∀ d ∈ t', d ≤ 0x10FFFF := fun d hd => hok d (by simp [hd])
      have hlen : t'.length ≤ n := by simpa using hn
      have hf' : t'.length + 1 ≤ f := by simpa using hf
      simp only [List.flatMap_cons, List.append_assoc] at hs ⊢
      cases escA_form c hc with
      | plain h ht hp =>
        rw [h] at hs ⊢
        have hnh : isHigh c = false := by
          simp [isHigh]; omega
        have h0 : s[e]? = some c := by
          have := congrArg (fun l => l[0]?) hs; simpa [List.getElem?_drop] using this
        have hd : s.drop (e + 1) = t'.flatMap escA ++ 34 :: rest := by
          rw [← List.drop_drop, hs]; simp
        rw [pyScanLoop_absorb s strict b f e c a h0 ht, ih t' (f + 1) (e + 1) _ rest hlen (by omega) hok' hd,
          mergeSurr_notHigh c t' hnh]
        exact ok_congr (by simp) (by simp only [List.singleton_append, List.length_cons]; omega)
      | short x y h hx hb hy =>
        subst hy
        rw [h] at hs ⊢
        have hnh : isHigh y = false := by
          have := backslash_le hb
          simp [isHigh]; omega
        have hs' : s.drop e = [92, x] ++ (t'.flatMap escA ++ 34 :: rest) := by rw [hs]
        have hd : s.drop (e + 2) = t'.flatMap escA ++ 34 :: rest := by
          rw [← List.drop_drop, hs]; simp
        rw [loop_short s strict b f e x y a _ hs' hx hb, ih t' f (e + 2) _ rest hlen hf' hok' hd,
          mergeSurr_notHigh y t' hnh]
        exact ok_congr (by simp) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      | u h hb =>
        rw [h] at hs ⊢
        have fin : ∀ (f' : Nat), t'.length + 1 ≤ f' → mergeSurr (c :: t') = c :: mergeSurr t' →
            pyScanLoop s strict b f' (e + 6) (a ++ [c]) =
              .ok (a ++ mergeSurr (c :: t'), ((e + ((uEsc c).length + (t'.flatMap escA).length) + 1 : Nat) : Int)) := by
          intro f' hf2 hm
          have hd := drop_six hs
          rw [ih t' f' (e + 6) _ rest hlen hf2 hok' hd, hm]
          exact ok_congr (by simp) (by rw [uEsc_length]; omega)
        simp only [List.length_append]
        by_cases hh : isHigh c = true
        · cases t' with
          | nil =>
            rw [loop_u s strict b f e c a _ hs hb (Or.inr (by simp))]
            exact fin f hf' rfl
          | cons c2 t'' =>
            have hc2 : c2 ≤ 0x10FFFF := hok' c2 (by simp)
            simp only [List.flatMap_cons, List.append_assoc] at hs ⊢
            by_cases hl : isLow c2 = true
            · rw [escA_low hl] at hs ⊢
              have hl2 := hl
              simp only [isLow, Bool.and_eq_true, decide_eq_true_eq] at hl2
              have hs2 : s.drop e = uEsc c ++ uEsc c2 ++ (t''.flatMap escA ++ 34 :: rest) := by
                rw [hs, List.append_assoc]
              have hd : s.drop (e + 12) = t''.flatMap escA ++ 34 :: rest := by
                rw [← List.drop_drop, hs2]; simp [uEsc]
              have hok2 : ∀ d ∈ t'', d ≤ 0x10FFFF := fun d hd => hok' d (by simp [hd])
              rw [loop_pair s strict b f e c c2 a _ hs2 hb (by omega) hh hl,
                ih t'' f (e + 12) _ rest (by simp at hlen; omega) (by simp at hf'; omega) hok2 hd]
              simp only [mergeSurr, hh, hl, and_self, ↓reduceIte]
              exact ok_congr (by simp) (by simp only [List.length_append, uEsc_length]; omega)
            · have hm : mergeSurr (c :: c2 :: t'') = c :: mergeSurr (c2 :: t'') := by
                simp [mergeSurr, hl]
              have hf3 := fin f hf' hm
              simp only [List.flatMap_cons] at hf3
              rw [← hf3]
              cases escA_form c2 hc2 with
              | plain h2 ht2 =>
                rw [h2] at hs
                have h92 : c2 ≠ 92 := by simp [isTerm] at ht2; omega
                exact loop_u s strict b f e c a _ hs hb (Or.inr (by simp [h92]))
              | short x y h2 hx2 _ _ =>
                rw [h2] at hs
                exact loop_u s strict b f e c a _ hs hb (Or.inr (by simp [hx2]))
              | u h2 hb2 =>
                rw [h2] at hs
                have hs2 : s.drop e = uEsc c ++ uEsc c2 ++ (t''.flatMap escA ++ 34 :: rest) := by
                  rw [hs, List.append_assoc]
                exact loop_u_nolow s strict b f e c c2 a _ hs2 hb hb2 (by simpa using hl)
              | pair n2 m2 h2 hn2 _ hh2 _ _ =>
                rw [h2] at hs
                have hs2 : s.drop e = uEsc c ++ uEsc n2 ++ (uEsc m2 ++ t''.flatMap escA ++ 34 :: rest) := by
                  rw [hs]; simp [List.append_assoc]
                have hnl : isLow n2 = false := by
                  simp only [isHigh, Bool.and_eq_true, decide_eq_true_eq] at hh2
                  simp [isLow]; omega
                exact loop_u_nolow s strict b f e c n2 a _ hs2 hb hn2 hnl
        · have hnh : isHigh c = false := by simpa using hh
          rw [loop_u s strict b f e c a _ hs hb (Or.inl hnh)]
          exact fin f hf' (mergeSurr_notHigh c t' hnh)
      | pair n2 m2 h hn2 hm2 hh hl hj =>
        rw [h] at hs ⊢
        have hnh : isHigh c = false := by
          have := join_ge n2 m2
          rw [hj] at this
          simp [isHigh]; omega
        have hs2 : s.drop e = uEsc n2 ++ uEsc m2 ++ (t'.flatMap escA ++ 34 :: rest) := by
          rw [hs, List.append_assoc]
        have hd : s.drop (e + 12) = t'.flatMap escA ++ 34 :: rest := by
          rw [← List.drop_drop, hs2]; simp [uEsc]
        rw [loop_pair s strict b f e n2 m2 a _ hs2 hn2 hm2 hh hl, hj,
          ih t' f (e + 12) _ rest hlen hf' hok' hd, mergeSurr_notHigh c t' hnh]
        exact ok_congr (by simp) (by simp only [List.length_append, uEsc_length]; omega)

end PyLean.JsonMod
