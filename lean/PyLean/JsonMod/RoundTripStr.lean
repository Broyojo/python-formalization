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

/-- The ways one `ensure_ascii=False` escape starts. -/
inductive EscNForm (c : Nat) : Prop where
  | plain (h : escN c = [c]) (ht : isTerm c = false)
  | short (x y : Nat) (h : escN c = [92, x]) (hx : x ≠ 117) (hb : backslash x = some y) (hy : y = c)
  | u (h : escN c = uEsc c) (hn : c < 32)

theorem escN_form (c : Nat) : EscNForm c := by
  by_cases h92 : c = 92
  · subst h92; exact .short 92 92 (by decide) (by decide) (by decide) rfl
  by_cases h34 : c = 34
  · subst h34; exact .short 34 34 (by decide) (by decide) (by decide) rfl
  by_cases h8 : c = 8
  · subst h8; exact .short 98 8 (by decide) (by decide) (by decide) rfl
  by_cases h12 : c = 12
  · subst h12; exact .short 102 12 (by decide) (by decide) (by decide) rfl
  by_cases h10 : c = 10
  · subst h10; exact .short 110 10 (by decide) (by decide) (by decide) rfl
  by_cases h13 : c = 13
  · subst h13; exact .short 114 13 (by decide) (by decide) (by decide) rfl
  by_cases h9 : c = 9
  · subst h9; exact .short 116 9 (by decide) (by decide) (by decide) rfl
  by_cases h32 : c < 32
  · exact .u (by simp [escN, escDct, h92, h34, h8, h12, h10, h13, h9, h32]) h32
  · refine .plain (by simp [escN, h92, h34, h32]) ?_
    simp [isTerm, h92, h34, h32]

/-- `ensure_ascii=False`: `py_scanstring` reads the escaped text back exactly. -/
theorem loopN (s : PStr) (strict : Bool) (b : Int) : ∀ (t : PStr) (f e : Nat) (a rest : PStr),
    t.length + 1 ≤ f → s.drop e = t.flatMap escN ++ 34 :: rest →
    pyScanLoop s strict b f e a = .ok (a ++ t, ((e + (t.flatMap escN).length + 1 : Nat) : Int)) := by
  intro t
  induction t with
  | nil =>
    intro f e a rest hf hs
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    simp only [List.flatMap_nil, List.nil_append] at hs
    have h0 : s[e]? = some 34 := by
      have := congrArg (fun l => l[0]?) hs; simpa [List.getElem?_drop] using this
    have hft : findTerm (s.drop e) = some 0 := by rw [hs]; simp [findTerm, isTerm]
    simp [pyScanLoop, hft, List.getD_eq_getElem?_getD, h0]
  | cons c t' ih =>
    intro f e a rest hf hs
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    have hf' : t'.length + 1 ≤ f := by simpa using hf
    simp only [List.flatMap_cons, List.append_assoc] at hs ⊢
    cases escN_form c with
    | plain h ht =>
      rw [h] at hs ⊢
      have h0 : s[e]? = some c := by
        have := congrArg (fun l => l[0]?) hs; simpa [List.getElem?_drop] using this
      have hd : s.drop (e + 1) = t'.flatMap escN ++ 34 :: rest := by
        rw [← List.drop_drop, hs]; simp
      rw [pyScanLoop_absorb s strict b f e c a h0 ht, ih (f + 1) (e + 1) _ rest (by omega) hd]
      exact ok_congr (by simp) (by simp only [List.singleton_append, List.length_cons]; omega)
    | short x y h hx hb hy =>
      subst hy
      rw [h] at hs ⊢
      have hs' : s.drop e = [92, x] ++ (t'.flatMap escN ++ 34 :: rest) := by rw [hs]
      have hd : s.drop (e + 2) = t'.flatMap escN ++ 34 :: rest := by
        rw [← List.drop_drop, hs]; simp
      rw [loop_short s strict b f e x y a _ hs' hx hb, ih f (e + 2) _ rest hf' hd]
      exact ok_congr (by simp) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    | u h hn =>
      rw [h] at hs ⊢
      have hd := drop_six hs
      have hnh : isHigh c = false := by simp [isHigh]; omega
      rw [loop_u s strict b f e c a _ hs (by omega) (Or.inl hnh), ih f (e + 6) _ rest hf' hd]
      exact ok_congr (by simp) (by simp only [List.length_append, uEsc_length]; omega)

theorem escA_ne (c : Nat) (hc : c ≤ 0x10FFFF) : 1 ≤ (escA c).length := by
  cases escA_form c hc with
  | plain h _ _ => simp [h]
  | short x y h => simp [h]
  | u h _ => rw [h, uEsc_length]; omega
  | pair n m h => rw [h]; simp [uEsc_length]

theorem escN_ne (c : Nat) : 1 ≤ (escN c).length := by
  cases escN_form c with
  | plain h _ => simp [h]
  | short x y h => simp [h]
  | u h _ => rw [h, uEsc_length]; omega

theorem flatMap_ge (esc : Nat → PStr) (t : PStr) (h : ∀ c ∈ t, 1 ≤ (esc c).length) :
    t.length ≤ (t.flatMap esc).length := by
  induction t with
  | nil => simp
  | cons c t ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h c (by simp)
    have h2 := ih (fun d hd => h d (by simp [hd]))
    omega

/-- What `loads` makes of a string written by `dumps`. -/
def decS (ascii : Bool) (t : PStr) : PStr := if ascii then mergeSurr t else t

theorem cps_of_strOk {t : PStr} (h : strOk t = true) : ∀ c ∈ t, c ≤ 0x10FFFF := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa [cpOk] using this

theorem pyEncA (t : PStr) : pyEncodeBasestringAscii t = 34 :: t.flatMap escA ++ [34] := rfl
theorem pyEncN (t : PStr) : pyEncodeBasestring t = 34 :: t.flatMap escN ++ [34] := rfl

/-- `py_scanstring` on a string written by `py_encode_basestring(_ascii)`. -/
theorem scan_enc_py (cfg : ECfg) (s : PStr) (t rest : PStr) (p : Nat) (strict : Bool)
    (hok : strOk t = true) (hs : s.drop p = pyStrEnc cfg t ++ rest) :
    pyScanstring s ((p + 1 : Nat) : Int) strict =
      .ok (decS cfg.ensureAscii t, ((p + (pyStrEnc cfg t).length : Nat) : Int)) := by
  have hl : p + (pyStrEnc cfg t).length ≤ s.length := by
    have h1 := congrArg List.length hs
    simp only [List.length_drop, List.length_append] at h1
    have h2 : 1 ≤ (pyStrEnc cfg t).length := by
      unfold pyStrEnc; split <;> simp [pyEncA, pyEncN]
    omega
  unfold pyScanstring
  have hc1 : clampPos s ((p + 1 : Nat) : Int) = p + 1 := by
    apply clampPos_nat
    have h2 : 1 ≤ (pyStrEnc cfg t).length := by
      unfold pyStrEnc; split <;> simp [pyEncA, pyEncN]
    omega
  rw [hc1]
  by_cases ha : cfg.ensureAscii = true
  · have he : pyStrEnc cfg t = 34 :: t.flatMap escA ++ [34] := by simp [pyStrEnc, ha, pyEncA]
    rw [he] at hs hl ⊢
    have hd : s.drop (p + 1) = t.flatMap escA ++ 34 :: rest := by
      rw [← List.drop_drop, hs]; simp
    have hge := flatMap_ge escA t (fun c hc => escA_ne c (cps_of_strOk hok c hc))
    simp only [List.cons_append, List.length_cons, List.length_append, List.length_nil] at hl ⊢
    rw [loopA s strict _ t.length t _ (p + 1) [] rest (by omega) (by omega) (cps_of_strOk hok) hd]
    exact ok_congr (by simp [decS, ha]) (by omega)
  · have he : pyStrEnc cfg t = 34 :: t.flatMap escN ++ [34] := by simp [pyStrEnc, ha, pyEncN]
    rw [he] at hs hl ⊢
    have hd : s.drop (p + 1) = t.flatMap escN ++ 34 :: rest := by
      rw [← List.drop_drop, hs]; simp
    have hge := flatMap_ge escN t (fun c _ => escN_ne c)
    simp only [List.cons_append, List.length_cons, List.length_append, List.length_nil] at hl ⊢
    rw [loopN s strict _ t _ (p + 1) [] rest (by omega) hd]
    exact ok_congr (by simp [decS, ha]) (by omega)

/-- `scanstring_unicode` on a string written by `encoder_encode_string`. -/
theorem scan_enc_c (cfg : ECfg) (s : PStr) (t rest : PStr) (p : Nat) (strict : Bool)
    (hok : strOk t = true) (hs : s.drop p = cStrEnc cfg t ++ rest) :
    cScanstring s (p + 1) strict = .ok (decS cfg.ensureAscii t, p + (cStrEnc cfg t).length) := by
  have heq := strEnc_twins cfg t hok
  rw [← heq] at hs ⊢
  have hpy := scan_enc_py cfg s t rest p strict hok hs
  have h1 : 1 ≤ (pyStrEnc cfg t).length := by
    unfold pyStrEnc; split <;> simp [pyEncA, pyEncN]
  have hl : p + 1 ≤ s.length := by
    have h2 := congrArg List.length hs
    simp only [List.length_drop, List.length_append] at h2
    omega
  rcases scanstring_rel s strict (p + 1) (by omega) hl with ⟨v, k, _, h3, h4⟩ | ⟨pe, ce, h3, _, _⟩
  · rw [hpy] at h3
    simp only [Except.ok.injEq, Prod.mk.injEq] at h3
    obtain ⟨rfl, h5⟩ := h3
    have : k = p + (pyStrEnc cfg t).length := by omega
    rw [h4, this]
  · rw [hpy] at h3; cases h3

end PyLean.JsonMod
