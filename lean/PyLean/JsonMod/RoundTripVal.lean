import PyLean.JsonMod.RoundTripInt

/-!
Reading back the text written by `dumps`: the C scanner decodes the encoding of
any value when `indent` is white space and the separators are `,` and `:` with
white space around them. The statement is by induction on the decoder's fuel;
running out of fuel is ruled out separately (`DecFuel`).
-/

namespace PyLean.JsonMod

open PyLean

mutual
/-- `EVal.ok`, without float values: their text is `float.__repr__`, which is
abstract here (see `json-dumps-accepted-float`). -/
def EVal.okJ : EVal → Bool
  | .flt _ _ => false
  | .str s => strOk s
  | .list xs => EVal.okJList xs
  | .dict kvs => EVal.okJItems kvs
  | _ => true
def EVal.okJList : List EVal → Bool
  | [] => true
  | x :: xs => EVal.okJ x && EVal.okJList xs
def EVal.okJItems : List (EKey × EVal) → Bool
  | [] => true
  | (k, x) :: xs => k.ok && EVal.okJ x && EVal.okJItems xs
end

mutual
theorem EVal.ok_of_okJ : ∀ v : EVal, v.okJ = true → v.ok = true
  | .none, _ => rfl
  | .bool _, _ => rfl
  | .int _, _ => rfl
  | .str _, h => h
  | .flt _ _, h => by simp [EVal.okJ] at h
  | .list xs, h => EVal.okList_of_okJ xs h
  | .dict kvs, h => EVal.okItems_of_okJ kvs h
  | .back _, _ => rfl
  | .other _ _, _ => rfl
theorem EVal.okList_of_okJ : ∀ xs : List EVal, EVal.okJList xs = true → EVal.okList xs = true
  | [], _ => rfl
  | x :: xs, h => by
    simp only [EVal.okJList, Bool.and_eq_true] at h
    simp only [EVal.okList, Bool.and_eq_true]
    exact ⟨EVal.ok_of_okJ x h.1, EVal.okList_of_okJ xs h.2⟩
theorem EVal.okItems_of_okJ : ∀ xs : List (EKey × EVal), EVal.okJItems xs = true → EVal.okItems xs = true
  | [], _ => rfl
  | (k, x) :: xs, h => by
    simp only [EVal.okJItems, Bool.and_eq_true] at h
    simp only [EVal.okItems, Bool.and_eq_true]
    exact ⟨⟨h.1.1, EVal.ok_of_okJ x h.1.2⟩, EVal.okItems_of_okJ xs h.2⟩
end

/-- Only JSON white space. -/
def wsOnly (t : PStr) : Bool := t.all isWs

/-- A separator: the character `m` with JSON white space around it. -/
def SepOk (sep : PStr) (m : Nat) : Prop :=
  ∃ a b, sep = a ++ m :: b ∧ wsOnly a = true ∧ wsOnly b = true

/-- The options under which `dumps` writes JSON: `item_separator` is a comma and
`key_separator` a colon, possibly padded with white space, and `indent` is white
space. -/
structure Layout (cfg : ECfg) : Prop where
  item : SepOk cfg.itemSep 44
  key : SepOk cfg.keySep 58
  ind : ∀ i, cfg.indent = some i → wsOnly i = true
  cst : cfg.customEnc = none
  dfl : ∀ n t v', cfg.dflt n t = .ok v' → EVal.okJ v' = true

theorem wsOnly_nil : wsOnly [] = true := rfl

theorem wsOnly_append {a b : PStr} (ha : wsOnly a = true) (hb : wsOnly b = true) : wsOnly (a ++ b) = true := by
  simp only [wsOnly, List.all_append, Bool.and_eq_true] at *
  exact ⟨ha, hb⟩

theorem wsOnly_rep {t : PStr} (h : wsOnly t = true) : ∀ k, wsOnly (rep t k) = true
  | 0 => rfl
  | k + 1 => wsOnly_append h (wsOnly_rep h k)

theorem wsOnly_nl {t : PStr} (h : wsOnly t = true) (k : Nat) : wsOnly (cNewlineIndent t k) = true :=
  wsOnly_append (by decide) (wsOnly_rep h k)

theorem wsLen_append : ∀ (a R : PStr), wsOnly a = true → wsLen (a ++ R) = a.length + wsLen R
  | [], R, _ => by simp
  | c :: a, R, h => by
    simp only [wsOnly, List.all_cons, Bool.and_eq_true] at h
    simp only [List.cons_append, wsLen, h.1, ↓reduceIte, List.length_cons]
    rw [wsLen_append a R h.2]
    omega

theorem drop_after {s : PStr} {p : Nat} {a R : PStr} (hs : s.drop p = a ++ R) : s.drop (p + a.length) = R := by
  rw [← List.drop_drop, hs]; simp

theorem char_at {s : PStr} {p c : Nat} {R : PStr} (hs : s.drop p = c :: R) :
    p < s.length ∧ s[p]? = some c ∧ s.getD p 0 = c := by
  have h0 : s[p]? = some c := by
    have := congrArg (fun l => l[0]?) hs; simpa [List.getElem?_drop] using this
  exact ⟨(List.getElem?_eq_some_iff.mp h0).1, h0, by simp [List.getD_eq_getElem?_getD, h0]⟩

theorem wsEnd_text {s : PStr} {p : Nat} {a R : PStr} (hs : s.drop p = a ++ R) (ha : wsOnly a = true)
    (hR : wsLen R = 0) : wsEnd s p = p + a.length := by
  simp only [wsEnd, hs, wsLen_append a R ha, hR, Nat.add_zero]

theorem cArrAfter_close_eval {s : PStr} {k : Nat} {post rest : PStr}
    (hs : s.drop k = post ++ 93 :: rest) (hp : wsOnly post = true) :
    cArrAfter s k = .close ((k + post.length + 1 : Nat) : Int) := by
  have hw := wsEnd_text hs hp (by simp [wsLen, isWs])
  obtain ⟨h1, _, h3⟩ := char_at (drop_after hs)
  unfold cArrAfter
  dsimp only
  rw [hw, ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, h3⟩)]

theorem cArrAfter_next_eval {s : PStr} {k : Nat} {a b R : PStr}
    (hs : s.drop k = a ++ 44 :: (b ++ R)) (ha : wsOnly a = true) (hb : wsOnly b = true)
    (hR0 : wsLen R = 0) (hR : ∀ r, R ≠ 93 :: r) :
    cArrAfter s k = .next ((k + a.length + 1 + b.length : Nat) : Int) := by
  have hw := wsEnd_text hs ha (by simp [wsLen, isWs])
  have hd := drop_after hs
  obtain ⟨h1, _, h3⟩ := char_at hd
  have hd1 : s.drop (k + a.length + 1) = b ++ R := by
    rw [← List.drop_drop, hd]; simp
  have hw2 := wsEnd_text hd1 hb hR0
  have hdR := drop_after hd1
  have n1 : ¬ (k + a.length < s.length ∧ s.getD (k + a.length) 0 = 93) := by rw [h3]; simp
  have n2 : ¬ (k + a.length ≥ s.length ∨ s.getD (k + a.length) 0 ≠ 44) := by rw [h3]; simp; omega
  have n3 : ¬ (k + a.length + 1 + b.length < s.length ∧ s.getD (k + a.length + 1 + b.length) 0 = 93) := by
    rintro ⟨h4, h5⟩
    rw [drop_cons h4, h5] at hdR
    exact hR _ hdR.symm
  unfold cArrAfter
  dsimp only
  rw [hw, hw2]
  simp only [n1, n2, n3, ↓reduceIte]

theorem cObjAfter_close_eval {s : PStr} {k : Nat} {post rest : PStr}
    (hs : s.drop k = post ++ 125 :: rest) (hp : wsOnly post = true) :
    cObjAfter s k = .close ((k + post.length + 1 : Nat) : Int) := by
  have hw := wsEnd_text hs hp (by simp [wsLen, isWs])
  obtain ⟨h1, _, h3⟩ := char_at (drop_after hs)
  unfold cObjAfter
  dsimp only
  rw [hw, ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, h3⟩)]

theorem cObjAfter_next_eval {s : PStr} {k : Nat} {a b R : PStr}
    (hs : s.drop k = a ++ 44 :: (b ++ R)) (ha : wsOnly a = true) (hb : wsOnly b = true)
    (hR0 : wsLen R = 0) (hR : ∀ r, R ≠ 125 :: r) :
    cObjAfter s k = .next ((k + a.length + 1 + b.length : Nat) : Int) := by
  have hw := wsEnd_text hs ha (by simp [wsLen, isWs])
  have hd := drop_after hs
  obtain ⟨h1, _, h3⟩ := char_at hd
  have hd1 : s.drop (k + a.length + 1) = b ++ R := by
    rw [← List.drop_drop, hd]; simp
  have hw2 := wsEnd_text hd1 hb hR0
  have hdR := drop_after hd1
  have n1 : ¬ (k + a.length < s.length ∧ s.getD (k + a.length) 0 = 125) := by rw [h3]; simp
  have n2 : ¬ (k + a.length ≥ s.length ∨ s.getD (k + a.length) 0 ≠ 44) := by rw [h3]; simp; omega
  have n3 : ¬ (k + a.length + 1 + b.length < s.length ∧ s.getD (k + a.length + 1 + b.length) 0 = 125) := by
    rintro ⟨h4, h5⟩
    rw [drop_cons h4, h5] at hdR
    exact hR _ hdR.symm
  unfold cObjAfter
  dsimp only
  rw [hw, hw2]
  simp only [n1, n2, n3, ↓reduceIte]

/-! ### One step of `scan_once_unicode` -/

theorem litAt_of {s : PStr} {p : Nat} {lit : String} {R : PStr} (hs : s.drop p = cs lit ++ R)
    (hk : 1 ≤ (cs lit).length) : litAt s p lit = true := by
  have h := congrArg List.length hs
  simp only [List.length_drop, List.length_append] at h
  unfold litAt
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨by omega, ?_⟩
  rw [hs]
  simp

theorem scanOnce_arr (cfg : DCfg) (n : Nat) {s : PStr} {p : Nat} {R : PStr} (hs : s.drop p = 91 :: R) :
    cScanOnce cfg s (n + 1) p =
      if wsEnd s (p + 1) ≥ s.length ∨ s.getD (wsEnd s (p + 1)) 0 ≠ 93 then
        cArrLoop cfg s n (wsEnd s (p + 1)) []
      else .ok (.arr [], wsEnd s (p + 1) + 1) := by
  obtain ⟨h1, _, h3⟩ := char_at hs
  have hl : ¬ p ≥ s.length := by omega
  simp only [cScanOnce, hl, ↓reduceIte, h3, Nat.reduceEqDiff]

theorem scanOnce_obj (cfg : DCfg) (n : Nat) {s : PStr} {p : Nat} {R : PStr} (hs : s.drop p = 123 :: R) :
    cScanOnce cfg s (n + 1) p =
      if wsEnd s (p + 1) ≥ s.length ∨ s.getD (wsEnd s (p + 1)) 0 ≠ 125 then
        (if wsEnd s (p + 1) ≥ s.length ∨ s.getD (wsEnd s (p + 1)) 0 ≠ 34 then
          .error (.jde "Expecting property name enclosed in double quotes" (wsEnd s (p + 1)))
         else cObjBody cfg s n (wsEnd s (p + 1)) [])
      else (cFinish cfg []).map (·, wsEnd s (p + 1) + 1) := by
  obtain ⟨h1, _, h3⟩ := char_at hs
  have hl : ¬ p ≥ s.length := by omega
  simp only [cScanOnce, hl, ↓reduceIte, h3, Nat.reduceEqDiff]

theorem scanOnce_str (cfg : DCfg) (n : Nat) {s : PStr} {p e : Nat} {R v : PStr} (hs : s.drop p = 34 :: R)
    (h : cScanstring s (p + 1) cfg.strict = .ok (v, e)) :
    cScanOnce cfg s (n + 1) p = .ok (.str v, e) := by
  obtain ⟨h1, _, h3⟩ := char_at hs
  have hl : ¬ p ≥ s.length := by omega
  simp only [cScanOnce, hl, ↓reduceIte, h3, h]

theorem scanOnce_lit (cfg : DCfg) (n : Nat) {s : PStr} {p : Nat} (lit : String) (c : Nat) (R tl : PStr)
    (hc : cs lit = c :: tl) (hs : s.drop p = cs lit ++ R)
    (hn1 : c ≠ 34) (hn2 : c ≠ 123) (hn3 : c ≠ 91) :
    litAt s p lit = true ∧ cScanOnce cfg s (n + 1) p =
      (if c = 110 ∧ litAt s p "null" = true then .ok (.null, p + 4)
       else if c = 116 ∧ litAt s p "true" = true then .ok (.bool true, p + 4)
       else if c = 102 ∧ litAt s p "false" = true then .ok (.bool false, p + 5)
       else if c = 78 ∧ litAt s p "NaN" = true then cConst cfg "NaN" p
       else if c = 73 ∧ litAt s p "Infinity" = true then cConst cfg "Infinity" p
       else if c = 45 ∧ litAt s p "-Infinity" = true then cConst cfg "-Infinity" p
       else cMatchNumber cfg s p) := by
  have hs' : s.drop p = c :: (tl ++ R) := by rw [hs, hc]; rfl
  obtain ⟨h1, _, h3⟩ := char_at hs'
  have hl : ¬ p ≥ s.length := by omega
  refine ⟨litAt_of hs (by rw [hc]; simp), ?_⟩
  simp only [cScanOnce, hl, ↓reduceIte, h3, hn1, hn2, hn3]

/-! ### Views of the encoder -/

/-- A value's text starts like this. -/
def ValHead (c : Nat) : Prop :=
  c = 34 ∨ c = 91 ∨ c = 123 ∨ c = 110 ∨ c = 116 ∨ c = 102 ∨ c = 45 ∨ isDigit c = true

theorem ValHead.not {c : Nat} (h : ValHead c) : isWs c = false ∧ c ≠ 93 ∧ c ≠ 125 := by
  have hd : isDigit c = true → 48 ≤ c ∧ c ≤ 57 := by simp [isDigit]
  have key : c ≠ 32 ∧ c ≠ 9 ∧ c ≠ 10 ∧ c ≠ 13 ∧ c ≠ 93 ∧ c ≠ 125 := by
    rcases h with h | h | h | h | h | h | h | h
    all_goals first
      | (subst h; decide)
      | (have := hd h; omega)
  simp [isWs, key.1, key.2.1, key.2.2.1, key.2.2.2.1, key.2.2.2.2]

theorem cStrEnc_head (cfg : ECfg) (t : PStr) : ∃ r, cStrEnc cfg t = 34 :: r := by
  unfold cStrEnc
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem intRepr_head {n : Int} {t : PStr} (h : intRepr n = .ok t) :
    ∃ c r, t = c :: r ∧ ValHead c ∧
      (c = 45 → ∃ d r', r = d :: r' ∧ isDigit d = true) ∧ (c ≠ 45 → isDigit c = true) := by
  obtain ⟨ds, hd, rfl, _⟩ := intRepr_view h
  have hds : ∃ d r, ds = d :: r ∧ isDigit d = true := by
    rcases hd.head with ⟨_, rfl⟩ | ⟨d, r, rfl, _, _⟩
    · exact ⟨48, [], rfl, rfl⟩
    · exact ⟨d, r, rfl, hd.dig d (by simp)⟩
  obtain ⟨d, r, rfl, h2⟩ := hds
  by_cases hn : n < 0
  · simp only [hn, ↓reduceIte]
    exact ⟨45, d :: r, rfl, by simp [ValHead], fun _ => ⟨d, r, rfl, h2⟩, fun e => absurd rfl e⟩
  · simp only [hn, ↓reduceIte]
    have h3 : d ≠ 45 := by
      intro e
      subst e
      revert h2
      decide
    exact ⟨d, r, rfl, by simp [ValHead, h2], fun e => absurd e h3, fun _ => h2⟩

theorem cEnc_head {cfg : ECfg} (hL : Layout cfg) : ∀ {f lvl : Nat} {seen : List Nat} {v : EVal} {t : PStr},
    v.okJ = true → cEnc cfg f lvl seen v = .ok t → ∃ c r, t = c :: r ∧ ValHead c := by
  intro f
  induction f with
  | zero => intro lvl seen v t _ h; simp [cEnc] at h
  | succ f ih =>
    intro lvl seen v t hok h
    cases v with
    | none =>
      simp only [cEnc, Except.ok.injEq] at h
      exact ⟨110, _, by rw [← h]; rfl, by simp [ValHead]⟩
    | bool b =>
      cases b
      · simp only [cEnc, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
        exact ⟨102, _, by rw [← h]; rfl, by simp [ValHead]⟩
      · simp only [cEnc, ↓reduceIte, Except.ok.injEq] at h
        exact ⟨116, _, by rw [← h]; rfl, by simp [ValHead]⟩
    | int n =>
      simp only [cEnc] at h
      obtain ⟨c, r, h1, h2, _⟩ := intRepr_head h
      exact ⟨c, r, h1, h2⟩
    | flt b r => simp [EVal.okJ] at hok
    | str x =>
      simp only [cEnc, cEncStr, hL.cst, Except.ok.injEq] at h
      obtain ⟨r, hr⟩ := cStrEnc_head cfg x
      exact ⟨34, r, by rw [← h, hr], by simp [ValHead]⟩
    | list xs =>
      simp only [cEnc] at h
      split at h
      · simp only [Except.ok.injEq] at h
        exact ⟨91, _, by rw [← h]; rfl, by simp [ValHead]⟩
      · split at h
        · cases h
        · simp only [Except.ok.injEq] at h
          exact ⟨91, _, by rw [← h]; rfl, by simp [ValHead]⟩
    | dict kvs =>
      simp only [cEnc] at h
      split at h
      · simp only [Except.ok.injEq] at h
        exact ⟨123, _, by rw [← h]; rfl, by simp [ValHead]⟩
      · split at h
        · cases h
        · split at h
          · cases h
          · simp only [Except.ok.injEq] at h
            exact ⟨123, _, by rw [← h]; rfl, by simp [ValHead]⟩
    | back k =>
      simp only [cEnc] at h
      cases h
    | other n t' =>
      simp only [cEnc] at h
      split at h
      · cases h
      · cases hd : cfg.dflt n t' with
        | error e => rw [hd] at h; cases h
        | ok v' =>
          rw [hd] at h
          exact ih (hL.dfl n t' v' hd) h

end PyLean.JsonMod
