import PyLean.JsonMod.RoundTripVal

/-!
The C scanner reads back the text written by the C encoder.
-/

namespace PyLean.JsonMod

open PyLean

/-- `D r j k`: out of fuel, or the value `j` ending at `k`. -/
def D {α : Type} (r : DR (α × Nat)) (j : α) (k : Nat) : Prop := r = fuelOut ∨ r = .ok (j, k)

theorem D.ok {α : Type} {j : α} {k : Nat} : D (.ok (j, k)) j k := Or.inr rfl

/-- The accumulator of `_parse_object_unicode` after the pairs `ps`. -/
def addAll (dcfg : DCfg) (acc : List (PStr × JVal)) (ps : List (PStr × JVal)) : List (PStr × JVal) :=
  ps.foldl (fun a p => cAddPair dcfg a p.1 p.2) acc

/-- The pairs `loads` reads from the items written by `dumps`: skipped keys are
gone, non-str keys are strings. -/
def decI (cfg : ECfg) (g : EVal → JVal) : List (EKey × EVal) → List (PStr × JVal)
  | [] => []
  | (k, x) :: r =>
    match cKeyStr cfg k with
    | .ok (some ks) => (decS cfg.ensureAscii ks, g x) :: decI cfg g r
    | _ => decI cfg g r

/-- The items in the order `dumps` writes them. -/
def sortedItems (cfg : ECfg) (kvs : List (EKey × EVal)) : List (EKey × EVal) :=
  match (if cfg.sortKeys then sortItems kvs else .ok kvs) with
  | .ok i => i
  | .error _ => []

/-- The value `loads` reads from the text `dumps` wrote. -/
def decV (cfg : ECfg) (dcfg : DCfg) : Nat → EVal → JVal
  | 0, _ => .null
  | f + 1, v =>
    match v with
    | .bool b => .bool b
    | .int n => decInt dcfg n
    | .str t => .str (decS cfg.ensureAscii t)
    | .list xs => .arr (xs.map (decV cfg dcfg f))
    | .dict kvs => .obj (addAll dcfg [] (decI cfg (decV cfg dcfg f) (sortedItems cfg kvs)))
    | _ => .null

/-! ### Views of the encoder -/

theorem cEncList_cons {cfg : ECfg} {f lvl i : Nat} {sep : PStr} {x : EVal} {xs : List EVal} {body : PStr}
    (h : cEncList cfg f lvl sep i (x :: xs) = .ok body) :
    ∃ t b, cEnc cfg f lvl x = .ok t ∧ cEncList cfg f lvl sep (i + 1) xs = .ok b ∧
      body = (if i ≠ 0 then sep else []) ++ t ++ b := by
  simp only [cEncList] at h
  cases h1 : cEnc cfg f lvl x with
  | error e => rw [h1] at h; cases h
  | ok t =>
    rw [h1] at h
    simp only at h
    cases h2 : cEncList cfg f lvl sep (i + 1) xs with
    | error e => rw [h2] at h; cases h
    | ok b =>
      rw [h2] at h
      simp only [Except.ok.injEq] at h
      exact ⟨t, b, rfl, rfl, h.symm⟩

theorem cEncList_shift (cfg : ECfg) (f lvl : Nat) (sep : PStr) :
    ∀ (xs : List EVal) (i j : Nat), i ≠ 0 → j ≠ 0 →
      cEncList cfg f lvl sep i xs = cEncList cfg f lvl sep j xs := by
  intro xs
  induction xs with
  | nil => intro i j _ _; simp [cEncList]
  | cons x xs ih =>
    intro i j hi hj
    simp only [cEncList, hi, hj, ne_eq, not_false_eq_true, ↓reduceIte]
    rw [ih (i + 1) (j + 1) (by omega) (by omega)]

theorem cEncList_one {cfg : ECfg} {f lvl : Nat} {sep : PStr} {y : EVal} {ys : List EVal} {b : PStr}
    (h : cEncList cfg f lvl sep 1 (y :: ys) = .ok b) :
    ∃ b0, cEncList cfg f lvl sep 0 (y :: ys) = .ok b0 ∧ b = sep ++ b0 := by
  obtain ⟨t, b1, h1, h2, h3⟩ := cEncList_cons h
  refine ⟨t ++ b1, ?_, by rw [h3]; simp⟩
  simp only [cEncList, h1]
  rw [cEncList_shift cfg f lvl sep ys (0 + 1) (1 + 1) (by omega) (by omega), h2]
  simp

theorem cEncList_head {cfg : ECfg} {f lvl : Nat} {sep : PStr} {xs : List EVal} {b : PStr}
    (hne : xs ≠ []) (h : cEncList cfg f lvl sep 0 xs = .ok b) : ∃ c r, b = c :: r ∧ ValHead c := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons x xs =>
    obtain ⟨t, b1, h1, _, h3⟩ := cEncList_cons h
    obtain ⟨c, r, rfl, hc⟩ := cEnc_head h1
    exact ⟨c, r ++ b1, by rw [h3]; simp, hc⟩

theorem cEnc_list_view {cfg : ECfg} {f lvl : Nat} {xs : List EVal} {t : PStr} (hL : Layout cfg)
    (hne : xs ≠ []) (h : cEnc cfg (f + 1) lvl (.list xs) = .ok t) :
    ∃ lvl' pre sep post body, wsOnly pre = true ∧ wsOnly post = true ∧ SepOk sep 44 ∧
      cEncList cfg f lvl' sep 0 xs = .ok body ∧ t = [91] ++ pre ++ body ++ post ++ [93] := by
  have hl : ¬ xs.length = 0 := by simpa using hne
  simp only [cEnc, hl, ↓reduceIte] at h
  cases hi : cfg.indent with
  | none =>
    simp only [hi] at h
    cases hb : cEncList cfg f lvl cfg.itemSep 0 xs with
    | error e => rw [hb] at h; cases h
    | ok body =>
      rw [hb] at h
      simp only [Except.ok.injEq] at h
      exact ⟨lvl, [], cfg.itemSep, [], body, rfl, rfl, hL.item, hb, by rw [← h]⟩
  | some ind =>
    have hw := hL.ind ind hi
    simp only [hi] at h
    cases hb : cEncList cfg f (lvl + 1) (cSepIndent cfg ind (lvl + 1)) 0 xs with
    | error e => rw [hb] at h; cases h
    | ok body =>
      rw [hb] at h
      simp only [Except.ok.injEq] at h
      obtain ⟨a, b, h1, h2, h3⟩ := hL.item
      refine ⟨lvl + 1, cNewlineIndent ind (lvl + 1), cSepIndent cfg ind (lvl + 1),
        cNewlineIndent ind (lvl + 1 - 1), body, wsOnly_nl hw _, wsOnly_nl hw _,
        ⟨a, b ++ cNewlineIndent ind (lvl + 1), ?_, h2, wsOnly_append h3 (wsOnly_nl hw _)⟩, hb, by rw [← h]⟩
      simp [cSepIndent, h1]

theorem cEnc_dict_view {cfg : ECfg} {f lvl : Nat} {kvs : List (EKey × EVal)} {t : PStr} (hL : Layout cfg)
    (hne : kvs ≠ []) (h : cEnc cfg (f + 1) lvl (.dict kvs) = .ok t) :
    ∃ lvl' sep body first post, SepOk sep 44 ∧ wsOnly post = true ∧
      (first = true → post = []) ∧
      (if cfg.sortKeys then sortItems kvs else .ok kvs) = .ok (sortedItems cfg kvs) ∧
      cEncItems cfg f lvl' sep true (sortedItems cfg kvs) = .ok (body, first) ∧
      t = [123] ++ body ++ post ++ [125] := by
  have hl : ¬ kvs.length = 0 := by simpa using hne
  simp only [cEnc, hl, ↓reduceIte] at h
  cases hs : (if cfg.sortKeys then sortItems kvs else Except.ok kvs) with
  | error e =>
    cases hi : cfg.indent <;> simp only [hi, hs] at h <;> cases h
  | ok items =>
    have hsort : sortedItems cfg kvs = items := by simp [sortedItems, hs]
    rw [hsort]
    cases hi : cfg.indent with
    | none =>
      simp only [hi, hs] at h
      cases hb : cEncItems cfg f lvl cfg.itemSep true items with
      | error e => rw [hb] at h; cases h
      | ok r =>
        obtain ⟨body, first⟩ := r
        rw [hb] at h
        simp only [Except.ok.injEq] at h
        exact ⟨lvl, cfg.itemSep, body, first, [], hL.item, rfl, fun _ => rfl, rfl, hb, by rw [← h]⟩
    | some ind =>
      have hw := hL.ind ind hi
      simp only [hi, hs] at h
      cases hb : cEncItems cfg f (lvl + 1) (cSepIndent cfg ind (lvl + 1)) true items with
      | error e => rw [hb] at h; cases h
      | ok r =>
        obtain ⟨body, first⟩ := r
        rw [hb] at h
        simp only [Except.ok.injEq] at h
        obtain ⟨a, b, h1, h2, h3⟩ := hL.item
        refine ⟨lvl + 1, cSepIndent cfg ind (lvl + 1), body, first,
          (if (!first) = true then cNewlineIndent ind (lvl + 1 - 1) else []),
          ⟨a, b ++ cNewlineIndent ind (lvl + 1), ?_, h2, wsOnly_append h3 (wsOnly_nl hw _)⟩, ?_, ?_, rfl, hb,
          by rw [← h]⟩
        · simp [cSepIndent, h1]
        · split
          · exact wsOnly_nl hw _
          · rfl
        · intro hf; simp [hf]

/-- The separator before an item when it is the first one written. -/
def firstPre (cfg : ECfg) (lvl : Nat) : PStr :=
  match cfg.indent with
  | some ind => cNewlineIndent ind lvl
  | none => []

theorem firstPre_ws {cfg : ECfg} (hL : Layout cfg) (lvl : Nat) : wsOnly (firstPre cfg lvl) = true := by
  unfold firstPre
  split
  · rename_i ind hi; exact wsOnly_nl (hL.ind ind hi) _
  · rfl

theorem items_view (cfg : ECfg) (f lvl : Nat) (sep : PStr) (g : EVal → JVal) :
    ∀ (items : List (EKey × EVal)) (first : Bool) (b : PStr) (fst : Bool), EVal.okItems items = true →
    cEncItems cfg f lvl sep first items = .ok (b, fst) →
    (b = [] ∧ fst = first ∧ decI cfg g items = []) ∨
    (∃ ks x t items' b', strOk ks = true ∧ x.ok = true ∧ EVal.okItems items' = true ∧
      cEnc cfg f lvl x = .ok t ∧ cEncItems cfg f lvl sep false items' = .ok (b', fst) ∧
      b = (if first then firstPre cfg lvl else sep) ++ cStrEnc cfg ks ++ cfg.keySep ++ t ++ b' ∧
      decI cfg g items = (decS cfg.ensureAscii ks, g x) :: decI cfg g items') := by
  intro items
  induction items with
  | nil =>
    intro first b fst _ h
    simp only [cEncItems, Except.ok.injEq, Prod.mk.injEq] at h
    exact Or.inl ⟨h.1.symm, h.2.symm, rfl⟩
  | cons p items ih =>
    obtain ⟨k, x⟩ := p
    intro first b fst hok h
    simp only [EVal.okItems, Bool.and_eq_true] at hok
    simp only [cEncItems] at h
    cases hk : cKeyStr cfg k with
    | error e => rw [hk] at h; cases h
    | ok o =>
      rw [hk] at h
      cases o with
      | none =>
        simp only at h
        have hd : decI cfg g ((k, x) :: items) = decI cfg g items := by simp [decI, hk]
        rw [hd]
        exact ih first b fst hok.2 h
      | some ks =>
        simp only at h
        cases h1 : cEnc cfg f lvl x with
        | error e => rw [h1] at h; cases h
        | ok t =>
          rw [h1] at h
          simp only at h
          cases h2 : cEncItems cfg f lvl sep false items with
          | error e => rw [h2] at h; cases h
          | ok r =>
            obtain ⟨b', fst'⟩ := r
            rw [h2] at h
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine Or.inr ⟨ks, x, t, items, b', keyStr_ok hok.1.1 hk, hok.1.2, hok.2, h1, h2, ?_, ?_⟩
            · simp only [firstPre, List.append_assoc]
              cases cfg.indent <;> rfl
            · simp [decI, hk]

theorem items_fst (cfg : ECfg) (f lvl : Nat) (sep : PStr) :
    ∀ (items : List (EKey × EVal)) (b : PStr) (fst : Bool),
    cEncItems cfg f lvl sep false items = .ok (b, fst) → fst = false := by
  intro items
  induction items with
  | nil =>
    intro b fst h
    simp only [cEncItems, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  | cons p items ih =>
    obtain ⟨k, x⟩ := p
    intro b fst h
    simp only [cEncItems] at h
    cases hk : cKeyStr cfg k with
    | error e => rw [hk] at h; cases h
    | ok o =>
      rw [hk] at h
      cases o with
      | none => exact ih b fst h
      | some ks =>
        simp only at h
        cases h1 : cEnc cfg f lvl x with
        | error e => rw [h1] at h; cases h
        | ok t =>
          rw [h1] at h
          simp only at h
          cases h2 : cEncItems cfg f lvl sep false items with
          | error e => rw [h2] at h; cases h
          | ok r =>
            obtain ⟨b', fst'⟩ := r
            rw [h2] at h
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl⟩ := h
            exact ih b' fst' h2

theorem Delim_of_ws {R rest : PStr} {m : Nat} (hR : wsOnly R = true) (hm : m = 93 ∨ m = 125) :
    Delim (R ++ m :: rest) := by
  cases R with
  | nil =>
    right
    exact ⟨m, rest, rfl, by omega⟩
  | cons c r =>
    right
    simp only [wsOnly, List.all_cons, Bool.and_eq_true] at hR
    exact ⟨c, r ++ m :: rest, rfl, Or.inl hR.1⟩

theorem Delim_of_sep {sep R : PStr} (hs : SepOk sep 44) : Delim (sep ++ R) := by
  obtain ⟨a, b, rfl, ha, _⟩ := hs
  cases a with
  | nil => exact Or.inr ⟨44, b ++ R, by simp, Or.inr (Or.inl rfl)⟩
  | cons c r =>
    simp only [wsOnly, List.all_cons, Bool.and_eq_true] at ha
    exact Or.inr ⟨c, r ++ 44 :: (b ++ R), by simp, Or.inl ha.1⟩

theorem sortedItems_ok {cfg : ECfg} {kvs : List (EKey × EVal)}
    (h : (if cfg.sortKeys then sortItems kvs else .ok kvs) = .ok (sortedItems cfg kvs))
    (hok : EVal.okItems kvs = true) : EVal.okItems (sortedItems cfg kvs) = true := by
  by_cases hs : cfg.sortKeys = true
  · simp only [hs, ↓reduceIte] at h
    rw [sortItems_ok h, hok]
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
    rw [← h, hok]

theorem addAll_cons (dcfg : DCfg) (acc : List (PStr × JVal)) (k : PStr) (v : JVal) (ps : List (PStr × JVal)) :
    addAll dcfg (cAddPair dcfg acc k v) ps = addAll dcfg acc ((k, v) :: ps) := rfl

/-- The text after a value in an array, ahead of the next element. -/
theorem dec_enc (cfg : ECfg) (dcfg : DCfg) (s : PStr) (hL : Layout cfg) : ∀ n : Nat,
    (∀ (f lvl : Nat) (v : EVal) (t : PStr) (p : Nat) (rest : PStr), v.ok = true →
      cEnc cfg f lvl v = .ok t → s.drop p = t ++ rest → Delim rest →
      D (cScanOnce dcfg s n p) (decV cfg dcfg f v) (p + t.length)) ∧
    (∀ (f lvl : Nat) (sep : PStr) (xs : List EVal) (e : Nat) (acc : List JVal) (body post rest : PStr),
      SepOk sep 44 → EVal.okList xs = true → xs ≠ [] → cEncList cfg f lvl sep 0 xs = .ok body →
      s.drop e = body ++ post ++ 93 :: rest → wsOnly post = true →
      D (cArrLoop dcfg s n e acc) (.arr (acc ++ xs.map (decV cfg dcfg f)))
        (e + body.length + post.length + 1)) ∧
    (∀ (f lvl : Nat) (sep ks : PStr) (x : EVal) (items : List (EKey × EVal)) (q : Nat)
      (acc : List (PStr × JVal)) (t body : PStr) (fst : Bool) (post rest : PStr),
      SepOk sep 44 → strOk ks = true → x.ok = true → EVal.okItems items = true →
      cEnc cfg f lvl x = .ok t → cEncItems cfg f lvl sep false items = .ok (body, fst) →
      s.drop q = cStrEnc cfg ks ++ cfg.keySep ++ t ++ body ++ post ++ 125 :: rest → wsOnly post = true →
      D (cObjBody dcfg s n q acc)
        (.obj (addAll dcfg acc ((decS cfg.ensureAscii ks, decV cfg dcfg f x) ::
          decI cfg (decV cfg dcfg f) items)))
        (q + (cStrEnc cfg ks).length + cfg.keySep.length + t.length + body.length + post.length + 1)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intros; exact Or.inl (by simp [cScanOnce])
    · intros; exact Or.inl (by simp [cArrLoop])
    · intros; exact Or.inl (by simp [cObjBody])
  | succ n ih =>
    obtain ⟨ihS, ihA, ihO⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro f lvl v t p rest hok he hs hd
      cases f with
      | zero => simp [cEnc] at he
      | succ f =>
        cases v with
        | none =>
          simp only [cEnc, Except.ok.injEq] at he
          subst he
          obtain ⟨hl, h2⟩ := scanOnce_lit dcfg n "null" 110 rest [117, 108, 108] (by decide) hs
            (by decide) (by decide) (by decide)
          rw [h2]
          simp only [hl, and_self, ↓reduceIte]
          exact D.ok
        | bool b =>
          cases b with
          | false =>
            simp only [cEnc, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at he
            subst he
            obtain ⟨hl, h2⟩ := scanOnce_lit dcfg n "false" 102 rest [97, 108, 115, 101] (by decide) hs
              (by decide) (by decide) (by decide)
            rw [h2]
            simp only [hl, Nat.reduceEqDiff, false_and, and_self, ↓reduceIte]
            exact D.ok
          | true =>
            simp only [cEnc, ↓reduceIte, Except.ok.injEq] at he
            subst he
            obtain ⟨hl, h2⟩ := scanOnce_lit dcfg n "true" 116 rest [114, 117, 101] (by decide) hs
              (by decide) (by decide) (by decide)
            rw [h2]
            simp only [hl, Nat.reduceEqDiff, false_and, and_self, ↓reduceIte]
            exact D.ok
        | int m =>
          simp only [cEnc] at he
          obtain ⟨c, r, rfl, hc, hsg, hdg⟩ := intRepr_head he
          have hs' : s.drop p = c :: (r ++ rest) := by rw [hs]; rfl
          obtain ⟨hlt, _, hg⟩ := char_at hs'
          have hc0 := hc
          have hnot : c ≠ 34 ∧ c ≠ 123 ∧ c ≠ 91 ∧ c ≠ 110 ∧ c ≠ 116 ∧ c ≠ 102 ∧ c ≠ 78 ∧ c ≠ 73 := by
            by_cases h45 : c = 45
            · subst h45; decide
            · have := hdg h45
              simp [isDigit] at this
              omega
          have hm : ¬ (c = 45 ∧ litAt s p "-Infinity" = true) := by
            rintro ⟨rfl, hl⟩
            obtain ⟨d, r', rfl, hdig⟩ := hsg rfl
            have h9 := (lit_twin' s p "-Infinity" 9 (by decide) (by decide)).mpr hl
            rw [pySlice_nat, hs] at h9
            simp [cs] at h9
            simp [h9.1, isDigit] at hdig
          have hl : ¬ p ≥ s.length := by omega
          have hstep : cScanOnce dcfg s (n + 1) p = cMatchNumber dcfg s p := by
            simp only [cScanOnce, hl, ↓reduceIte, hg, hnot.1, hnot.2.1, hnot.2.2.1, hnot.2.2.2.1,
              hnot.2.2.2.2.1, hnot.2.2.2.2.2.1, hnot.2.2.2.2.2.2.1, hnot.2.2.2.2.2.2.2, false_and, hm]
          rw [hstep, matchNumber_repr dcfg s p he hs hd hlt]
          exact D.ok
        | str x =>
          simp only [cEnc, Except.ok.injEq] at he
          subst he
          obtain ⟨r, hr⟩ := cStrEnc_head cfg x
          have hs' : s.drop p = 34 :: (r ++ rest) := by rw [hs, hr, List.cons_append]
          have hscan := scan_enc_c cfg s x rest p dcfg.strict hok hs
          rw [scanOnce_str dcfg n hs' hscan]
          exact D.ok
        | back k => simp only [cEnc] at he; cases he
        | other => simp [cEnc] at he
        | list xs =>
          have hxs : EVal.okList xs = true := hok
          by_cases hx : xs = []
          · subst hx
            simp only [cEnc, List.length_nil, ↓reduceIte, Except.ok.injEq] at he
            subst he
            have hs' : s.drop p = 91 :: 93 :: rest := by rw [hs]; rfl
            rw [scanOnce_arr dcfg n hs']
            have hd1 : s.drop (p + 1) = 93 :: rest := by rw [← List.drop_drop, hs']; rfl
            have hw : wsEnd s (p + 1) = p + 1 := by
              simpa using wsEnd_text (a := []) (by simpa using hd1) rfl (by simp [wsLen, isWs])
            obtain ⟨h1, _, h3⟩ := char_at hd1
            rw [hw]
            have n1 : ¬ (p + 1 ≥ s.length ∨ s.getD (p + 1) 0 ≠ 93) := by rw [h3]; simp; omega
            simp only [n1, ↓reduceIte, decV, List.map_nil]
            exact D.ok
          · obtain ⟨lvl', pre, sep, post, body, hpre, hpost, hsep, hb, rfl⟩ := cEnc_list_view hL hx he
            obtain ⟨c, r, hbody, hc⟩ := cEncList_head hx hb
            have hs' : s.drop p = 91 :: (pre ++ body ++ post ++ [93] ++ rest) := by
              rw [hs]; simp [List.append_assoc]
            rw [scanOnce_arr dcfg n hs']
            have hd1 : s.drop (p + 1) = pre ++ (body ++ post ++ 93 :: rest) := by
              rw [← List.drop_drop, hs']; simp [List.append_assoc]
            have hnot := hc.not
            have hw : wsEnd s (p + 1) = p + 1 + pre.length :=
              wsEnd_text hd1 hpre (by rw [hbody]; simp [wsLen, hnot.1])
            have hd2 := drop_after hd1
            have hd3 : s.drop (p + 1 + pre.length) = c :: (r ++ post ++ 93 :: rest) := by
              rw [hd2, hbody]; simp
            obtain ⟨_, _, h3⟩ := char_at hd3
            rw [hw]
            have n1 : (p + 1 + pre.length ≥ s.length ∨ s.getD (p + 1 + pre.length) 0 ≠ 93) := by
              rw [h3]; exact Or.inr hnot.2.1
            simp only [n1, ↓reduceIte, decV]
            have := ihA f lvl' sep xs (p + 1 + pre.length) [] body post rest hsep hxs hx hb
              (by rw [hd2]) hpost
            simp only [List.nil_append] at this
            have e : p + ([91] ++ pre ++ body ++ post ++ [93]).length =
                p + 1 + pre.length + body.length + post.length + 1 := by
              simp only [List.length_append, List.length_cons, List.length_nil]; omega
            rw [e]
            exact this
        | dict kvs =>
          have hkvs : EVal.okItems kvs = true := hok
          by_cases hx : kvs = []
          · subst hx
            simp only [cEnc, List.length_nil, ↓reduceIte, Except.ok.injEq] at he
            subst he
            have hs' : s.drop p = 123 :: 125 :: rest := by rw [hs]; rfl
            rw [scanOnce_obj dcfg n hs']
            have hd1 : s.drop (p + 1) = 125 :: rest := by rw [← List.drop_drop, hs']; rfl
            have hw : wsEnd s (p + 1) = p + 1 := by
              simpa using wsEnd_text (a := []) (by simpa using hd1) rfl (by simp [wsLen, isWs])
            obtain ⟨h1, _, h3⟩ := char_at hd1
            rw [hw]
            have n1 : ¬ (p + 1 ≥ s.length ∨ s.getD (p + 1) 0 ≠ 125) := by rw [h3]; simp; omega
            have hse : sortedItems cfg [] = [] := by
              unfold sortedItems
              by_cases h : cfg.sortKeys = true <;> simp [h, sortItems]
            simp only [n1, ↓reduceIte, decV, hse, decI]
            exact D.ok
          · obtain ⟨lvl', sep, body, first, post, hsep, hpost, hfirst, hsort, hb, rfl⟩ :=
              cEnc_dict_view hL hx he
            have hok2 := sortedItems_ok hsort hkvs
            rcases items_view cfg f lvl' sep (decV cfg dcfg f) _ true body first hok2 hb with
              ⟨rfl, rfl, hdec⟩ | ⟨ks, x, t, items', b', hks, hxok, hok', hx1, hb', hbody, hdec⟩
            · obtain rfl := hfirst rfl
              have hs' : s.drop p = 123 :: 125 :: rest := by rw [hs]; rfl
              rw [scanOnce_obj dcfg n hs']
              have hd1 : s.drop (p + 1) = 125 :: rest := by rw [← List.drop_drop, hs']; rfl
              have hw : wsEnd s (p + 1) = p + 1 := by
                simpa using wsEnd_text (a := []) (by simpa using hd1) rfl (by simp [wsLen, isWs])
              obtain ⟨h1, _, h3⟩ := char_at hd1
              rw [hw]
              have n1 : ¬ (p + 1 ≥ s.length ∨ s.getD (p + 1) 0 ≠ 125) := by rw [h3]; simp; omega
              simp only [n1, ↓reduceIte, decV, hdec]
              exact D.ok
            · simp only [↓reduceIte] at hbody
              obtain ⟨kr, hkr⟩ := cStrEnc_head cfg ks
              have hpre := firstPre_ws hL lvl'
              have hd0 : s.drop p = 123 :: (firstPre cfg lvl' ++ (cStrEnc cfg ks ++ cfg.keySep ++ t ++ b' ++ post ++ 125 :: rest)) := by
                rw [hs, hbody]; simp [List.append_assoc]
              rw [scanOnce_obj dcfg n hd0]
              have hd1 : s.drop (p + 1) = firstPre cfg lvl' ++ (cStrEnc cfg ks ++ cfg.keySep ++ t ++ b' ++ post ++ 125 :: rest) := by
                rw [← List.drop_drop, hd0]; rfl
              have hw : wsEnd s (p + 1) = p + 1 + (firstPre cfg lvl').length :=
                wsEnd_text hd1 hpre (by rw [hkr]; simp [wsLen, isWs])
              have hd2 := drop_after hd1
              have hd3 : s.drop (p + 1 + (firstPre cfg lvl').length) = 34 :: (kr ++ cfg.keySep ++ t ++ b' ++ post ++ 125 :: rest) := by
                rw [hd2, hkr]; simp [List.append_assoc]
              obtain ⟨hlt, _, h3⟩ := char_at hd3
              rw [hw]
              have n1 : (p + 1 + (firstPre cfg lvl').length ≥ s.length ∨
                  s.getD (p + 1 + (firstPre cfg lvl').length) 0 ≠ 125) := by rw [h3]; simp
              have n2 : ¬ (p + 1 + (firstPre cfg lvl').length ≥ s.length ∨
                  s.getD (p + 1 + (firstPre cfg lvl').length) 0 ≠ 34) := by rw [h3]; simp; omega
              have hfalse := items_fst cfg f lvl' sep _ _ _ hb'
              subst hfalse
              have hpost' : wsOnly post = true := hpost
              simp only [n1, n2, ↓reduceIte, decV, hdec]
              have := ihO f lvl' sep ks x items' (p + 1 + (firstPre cfg lvl').length) [] t b' false post rest
                hsep hks hxok hok' hx1 hb' (by rw [hd2]) hpost'
              have e : p + ([123] ++ body ++ post ++ [125]).length =
                  p + 1 + (firstPre cfg lvl').length + (cStrEnc cfg ks).length + cfg.keySep.length + t.length +
                    b'.length + post.length + 1 := by
                rw [hbody]
                simp only [List.length_append, List.length_cons, List.length_nil]; omega
              rw [e]
              exact this
    · intro f lvl sep xs e acc body post rest hsep hok hne hb hs hpost
      cases xs with
      | nil => exact absurd rfl hne
      | cons x ys =>
        obtain ⟨t, b1, h1, h2, h3⟩ := cEncList_cons hb
        simp only [ne_eq, not_true_eq_false, ↓reduceIte, List.nil_append] at h3
        simp only [EVal.okList, Bool.and_eq_true] at hok
        subst h3
        simp only [cArrLoop]
        cases ys with
        | nil =>
          simp only [cEncList, Except.ok.injEq] at h2
          subst h2
          have hs' : s.drop e = t ++ (post ++ 93 :: rest) := by simpa [List.append_assoc] using hs
          rcases ihS f lvl x t e (post ++ 93 :: rest) hok.1 h1 hs' (Delim_of_ws hpost (Or.inl rfl)) with h | h
          · left; rw [h]; rfl
          · right
            rw [h]
            simp only
            rw [cArrAfter_close_eval (drop_after hs') hpost]
            simp only [Int.toNat_natCast, List.map_cons, List.map_nil, List.length_append, List.length_nil]
            rfl
        | cons y ys' =>
          obtain ⟨b0, hb0, rfl⟩ := cEncList_one (b := b1) (by simpa using h2)
          obtain ⟨a, c, hsp, ha, hc⟩ := hsep
          obtain ⟨ch, r, hb0', hch⟩ := cEncList_head (by simp) hb0
          have hR : wsLen (b0 ++ post ++ 93 :: rest) = 0 ∧ ∀ r', (b0 ++ post ++ 93 :: rest) ≠ 93 :: r' := by
            rw [hb0']
            have hn := hch.not
            refine ⟨by simp [wsLen, hn.1], ?_⟩
            intro r' e'
            simp only [List.cons_append, List.cons.injEq] at e'
            exact hn.2.1 e'.1
          have hs1 : s.drop e = t ++ (sep ++ (b0 ++ post ++ 93 :: rest)) := by
            rw [hs]; simp [List.append_assoc]
          rcases ihS f lvl x t e _ hok.1 h1 hs1 (Delim_of_sep ⟨a, c, hsp, ha, hc⟩) with h | h
          · left; rw [h]; rfl
          · have hd := drop_after hs1
            have hd2 : s.drop (e + t.length) = a ++ 44 :: (c ++ (b0 ++ post ++ 93 :: rest)) := by
              rw [hd, hsp]; simp [List.append_assoc]
            rw [h]
            simp only
            rw [cArrAfter_next_eval hd2 ha hc hR.1 hR.2]
            simp only [Int.toNat_natCast]
            have hd3 : s.drop (e + t.length + a.length + 1 + c.length) = b0 ++ post ++ 93 :: rest := by
              have h3 := drop_after hd2
              have h4 : s.drop (e + t.length + a.length + 1) = c ++ (b0 ++ post ++ 93 :: rest) := by
                rw [← List.drop_drop, h3]; simp
              exact drop_after h4
            have := ihA f lvl sep (y :: ys') _ (acc ++ [decV cfg dcfg f x]) b0 post rest ⟨a, c, hsp, ha, hc⟩ hok.2
              (by simp) hb0 hd3 hpost
            have e1 : e + (t ++ (sep ++ b0)).length + post.length + 1 =
                e + t.length + a.length + 1 + c.length + b0.length + post.length + 1 := by
              rw [hsp]
              simp only [List.length_append, List.length_cons]; omega
            have e2 : acc ++ decV cfg dcfg f x :: decV cfg dcfg f y :: List.map (decV cfg dcfg f) ys' =
                acc ++ [decV cfg dcfg f x] ++ decV cfg dcfg f y :: List.map (decV cfg dcfg f) ys' := by simp
            simp only [List.map_cons] at this ⊢
            rw [e1, e2]
            exact this
    · intro f lvl sep ks x items q acc t body fst post rest hsep hks hx hitems h1 hb hs hpost
      simp only [cObjBody]
      have hs2 : s.drop q = cStrEnc cfg ks ++ (cfg.keySep ++ (t ++ (body ++ (post ++ 125 :: rest)))) := by
        simpa [List.append_assoc] using hs
      rw [scan_enc_c cfg s ks _ q dcfg.strict hks hs2]
      simp only
      have hd1 := drop_after hs2
      obtain ⟨a, c, hsp, ha, hc⟩ := hL.key
      generalize hR : t ++ (body ++ (post ++ 125 :: rest)) = RR at hd1
      have hd2 : s.drop (q + (cStrEnc cfg ks).length) = a ++ 58 :: (c ++ RR) := by
        rw [hd1, hsp]; simp [List.append_assoc]
      have hw : wsEnd s (q + (cStrEnc cfg ks).length) = q + (cStrEnc cfg ks).length + a.length :=
        wsEnd_text hd2 ha (by simp [wsLen, isWs])
      have hd3 := drop_after hd2
      obtain ⟨hlt, _, h3⟩ := char_at hd3
      have hd4 : s.drop (q + (cStrEnc cfg ks).length + a.length + 1) = c ++ RR := by
        rw [← List.drop_drop, hd3]; simp
      obtain ⟨c0, r0, ht, hhead⟩ := cEnc_head h1
      have hRR : RR = c0 :: (r0 ++ (body ++ (post ++ 125 :: rest))) := by rw [← hR, ht]; simp
      have hw2 : wsEnd s (q + (cStrEnc cfg ks).length + a.length + 1) =
          q + (cStrEnc cfg ks).length + a.length + 1 + c.length :=
        wsEnd_text hd4 hc (by rw [hRR]; simp [wsLen, hhead.not.1])
      have n1 : ¬ (q + (cStrEnc cfg ks).length + a.length ≥ s.length ∨
          s.getD (q + (cStrEnc cfg ks).length + a.length) 0 ≠ 58) := by rw [h3]; simp; omega
      rw [hw]
      simp only [n1, ↓reduceIte]
      rw [hw2]
      have hd5 := drop_after hd4
      rw [← hR] at hd5
      have hkl : cfg.keySep.length = a.length + 1 + c.length := by
        rw [hsp]; simp only [List.length_append, List.length_cons]; omega
      rcases items_view cfg f lvl sep (decV cfg dcfg f) items false body fst hitems hb with
        ⟨rfl, rfl, hdec⟩ | ⟨ks', x', t', items', b', hks', hx', hok', hx1, hb', hbody, hdec⟩
      · simp only [List.nil_append] at hd5
        rcases ihS f lvl x t _ (post ++ 125 :: rest) hx h1 hd5 (Delim_of_ws hpost (Or.inr rfl)) with h | h
        · left; rw [h]; rfl
        · right
          rw [h]
          simp only
          rw [cObjAfter_close_eval (drop_after hd5) hpost]
          simp only [Int.toNat_natCast, hdec]
          have e1 : q + (cStrEnc cfg ks).length + a.length + 1 + c.length + t.length + post.length + 1 =
              q + (cStrEnc cfg ks).length + cfg.keySep.length + t.length + ([] : PStr).length + post.length + 1 := by
            simp only [List.length_nil]; omega
          rw [e1]
          rfl
      · simp only [Bool.false_eq_true, ↓reduceIte] at hbody
        subst hbody
        obtain ⟨a2, c2, hsp2, ha2, hc2⟩ := hsep
        obtain ⟨kr, hkr⟩ := cStrEnc_head cfg ks'
        generalize hR2 : cStrEnc cfg ks' ++ cfg.keySep ++ t' ++ b' ++ post ++ 125 :: rest = R2
        have hR2' : R2 = 34 :: (kr ++ cfg.keySep ++ t' ++ b' ++ post ++ 125 :: rest) := by
          rw [← hR2, hkr]; simp
        have hd6 : s.drop (q + (cStrEnc cfg ks).length + a.length + 1 + c.length) = t ++ (sep ++ R2) := by
          rw [hd5, ← hR2]; simp [List.append_assoc]
        rcases ihS f lvl x t _ _ hx h1 hd6 (Delim_of_sep ⟨a2, c2, hsp2, ha2, hc2⟩) with h | h
        · left; rw [h]; rfl
        · have hd7 := drop_after hd6
          have hd8 : s.drop (q + (cStrEnc cfg ks).length + a.length + 1 + c.length + t.length) =
              a2 ++ 44 :: (c2 ++ R2) := by
            rw [hd7, hsp2]; simp [List.append_assoc]
          rw [h]
          simp only
          rw [cObjAfter_next_eval hd8 ha2 hc2 (by rw [hR2']; simp [wsLen, isWs])
            (by rw [hR2']; intro r' e'; simp at e')]
          simp only [Int.toNat_natCast]
          have hd9 := drop_after hd8
          have hd10 : s.drop (q + (cStrEnc cfg ks).length + a.length + 1 + c.length + t.length + a2.length + 1) =
              c2 ++ R2 := by
            rw [← List.drop_drop, hd9]; simp
          have hd11 := drop_after hd10
          generalize hi : q + (cStrEnc cfg ks).length + a.length + 1 + c.length + t.length + a2.length + 1 + c2.length = idx at hd11 ⊢
          have hd12 : s.drop idx = 34 :: (kr ++ cfg.keySep ++ t' ++ b' ++ post ++ 125 :: rest) := by
            rw [hd11, hR2']
          obtain ⟨hlt2, _, h5⟩ := char_at hd12
          have n2 : ¬ (idx ≥ s.length ∨ s.getD idx 0 ≠ 34) := by rw [h5]; simp; omega
          simp only [n2, ↓reduceIte]
          have hd13 : s.drop idx = cStrEnc cfg ks' ++ cfg.keySep ++ t' ++ b' ++ post ++ 125 :: rest := by
            rw [hd11, ← hR2]
          have := ihO f lvl sep ks' x' items' idx (cAddPair dcfg acc (decS cfg.ensureAscii ks) (decV cfg dcfg f x))
            t' b' fst post rest ⟨a2, c2, hsp2, ha2, hc2⟩ hks' hx' hok' hx1 hb' hd13 hpost
          rw [addAll_cons] at this
          simp only [hdec]
          have e1 : q + (cStrEnc cfg ks).length + cfg.keySep.length + t.length +
              (sep ++ cStrEnc cfg ks' ++ cfg.keySep ++ t' ++ b').length + post.length + 1 =
              idx + (cStrEnc cfg ks').length + cfg.keySep.length + t'.length + b'.length + post.length + 1 := by
            rw [← hi, hsp2]
            simp only [List.length_append, List.length_cons]; omega
          rw [e1]
          exact this

end PyLean.JsonMod
