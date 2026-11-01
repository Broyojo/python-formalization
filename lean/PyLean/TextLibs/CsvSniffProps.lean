import PyLean.TextLibs.CsvSniff

/-! Properties of `csv.Sniffer.sniff`. -/

namespace PyLean.TextLibs.Csv

open PyLean PyLean.TextLibs

set_option linter.unusedSimpArgs false

/-- `reader` rejects a dialect whose delimiter is its quote character, as `bad delimiter or quotechar
value`, so what `sniff` returns must have them differ to be usable at all. -/
def SniffUsable : Prop :=
  ∀ (s : List Nat) (ds : Option (List Nat)) (r : Sniffed),
    sniff s ds = .ok r → r.delimiter ≠ r.quotechar

/-- Whether `sniff` of `s` gives a dialect with the two the same. -/
def sniffClash (s : List Nat) : Bool :=
  match sniff s none with
  | .ok r => r.delimiter == r.quotechar
  | .error _ => false

theorem sniffClash_true : sniffClash [34] = true := by decide +kernel

theorem sniffUsable_refuted : ¬SniffUsable := by
  intro h
  have h1 := sniffClash_true
  unfold sniffClash at h1
  cases hs : sniff [34] none with
  | error e =>
    rw [hs] at h1
    cases h1
  | ok r =>
    rw [hs] at h1
    exact h [34] none r hs (by simpa using h1)

/-! ### `delimiters` -/

theorem bump_keys (d : List (List Nat × Nat)) (key k : List Nat) (hk : k ∈ (bump d key).map (·.1)) :
    k ∈ d.map (·.1) ∨ k = key := by
  induction d with
  | nil =>
    simp only [bump, List.map_cons, List.map_nil, List.mem_singleton] at hk
    exact .inr hk
  | cons x r ih =>
    obtain ⟨a, n⟩ := x
    simp only [bump] at hk
    split at hk
    · simp only [List.map_cons, List.mem_cons] at hk ⊢
      rcases hk with hk | hk
      · exact .inl (.inl hk)
      · exact .inl (.inr hk)
    · simp only [List.map_cons, List.mem_cons] at hk ⊢
      rcases hk with hk | hk
      · exact .inl (.inl hk)
      · rcases ih hk with h | h
        · exact .inl (.inr h)
        · exact .inr h

theorem tally_keys (dl : Option (List Nat)) (qi : Nat) (di si : Option Nat) :
    ∀ (ms : List Re.FindItem) (g : GQ), (∀ k ∈ g.delims.map (·.1), inDelims dl k = true) →
    ∀ k ∈ (tally dl qi di si ms g).delims.map (·.1), inDelims dl k = true := by
  intro ms
  induction ms with
  | nil => intro g h; exact h
  | cons m r ih =>
    intro g h
    have hstep : ∃ g', tally dl qi di si (m :: r) g = tally dl qi di si r g' ∧
        ∀ k ∈ g'.delims.map (·.1), inDelims dl k = true := by
      generalize h1 : (if (!(itemAt m qi).isEmpty) = true then
        { g with quotes := bump g.quotes (itemAt m qi) } else g) = g1
      have hg1 : g1.delims = g.delims := by
        rw [← h1]
        split <;> rfl
      cases di with
      | none =>
        refine ⟨g1, by rw [← h1]; rfl, ?_⟩
        rw [hg1]
        exact h
      | some d =>
        generalize h2 : (if (!(itemAt m d).isEmpty && inDelims dl (itemAt m d)) = true then
          { g1 with delims := bump g1.delims (itemAt m d) } else g1) = g2
        have hg2 : ∀ k ∈ g2.delims.map (·.1), inDelims dl k = true := by
          intro k hk
          rw [← h2] at hk
          split at hk
          · rename_i hc
            rcases bump_keys _ _ _ hk with h3 | h3
            · rw [hg1] at h3
              exact h k h3
            · subst h3
              simp only [Bool.and_eq_true] at hc
              exact hc.2
          · rw [hg1] at hk
            exact h k hk
        cases si with
        | none =>
          refine ⟨g2, by rw [← h2, ← h1]; rfl, hg2⟩
        | some sp =>
          refine ⟨if (!(itemAt m sp).isEmpty) = true then { g2 with spaces := g2.spaces + 1 } else g2,
            by rw [← h2, ← h1]; rfl, ?_⟩
          split
          · exact hg2
          · exact hg2
    obtain ⟨g', h1, h2⟩ := hstep
    rw [h1]
    exact ih g' h2

theorem maxKey_mem : ∀ d : List (List Nat × Nat), d ≠ [] → maxKey d ∈ d.map (·.1) := by
  intro d hd
  match d, hd with
  | x :: r, _ =>
    have : ∀ (l : List (List Nat × Nat)) (b : List Nat × Nat),
        (l.foldl (fun b y => if y.2 > b.2 then y else b) b) = b ∨
        (l.foldl (fun b y => if y.2 > b.2 then y else b) b) ∈ l := by
      intro l
      induction l with
      | nil => intro b; exact .inl rfl
      | cons y t ih =>
        intro b
        simp only [List.foldl_cons]
        split
        · rcases ih y with h | h
          · exact .inr (by rw [h]; simp)
          · exact .inr (List.mem_cons_of_mem _ h)
        · rcases ih b with h | h
          · exact .inl h
          · exact .inr (List.mem_cons_of_mem _ h)
    simp only [maxKey, List.map_cons, List.mem_cons, List.mem_map]
    rcases this r x with h | h
    · exact .inl (by rw [h])
    · exact .inr ⟨_, h, rfl⟩

theorem gqFinish_delim (dl : Option (List Nat)) (data : List Nat) (g : GQ)
    (h : ∀ k ∈ g.delims.map (·.1), inDelims dl k = true) (q d : List Nat) (dq skip : Bool)
    (hr : gqFinish data g = .ok (q, dq, d, skip)) : d = [] ∨ inDelims dl d = true := by
  unfold gqFinish at hr
  simp only [bind, Except.bind, pure, Except.pure] at hr
  by_cases he : g.delims.isEmpty = true
  · simp only [he, Bool.not_true, Bool.false_eq_true, if_false, List.isEmpty_nil] at hr
    cases hr
    exact .inl rfl
  · have hne : g.delims ≠ [] := by
      intro h0
      simp [h0] at he
    have hm := h _ (maxKey_mem _ hne)
    have hd : (if (!g.delims.isEmpty) = true then
        (if maxKey g.delims == [10] then [] else maxKey g.delims,
          (g.delims.lookup (maxKey g.delims)).getD 0 == g.spaces)
        else (([] : List Nat), false)).1 = [] ∨
        inDelims dl (if (!g.delims.isEmpty) = true then
          (if maxKey g.delims == [10] then [] else maxKey g.delims,
            (g.delims.lookup (maxKey g.delims)).getD 0 == g.spaces)
          else (([] : List Nat), false)).1 = true := by
      have he' : (!g.delims.isEmpty) = true := by simpa using he
      simp only [he', if_true]
      split
      · exact .inl rfl
      · exact .inr hm
    generalize hc : (if (!g.delims.isEmpty) = true then
        (if maxKey g.delims == [10] then [] else maxKey g.delims,
          (g.delims.lookup (maxKey g.delims)).getD 0 == g.spaces)
        else (([] : List Nat), false)) = c at hr hd
    obtain ⟨d1, s1⟩ := c
    simp only at hd hr
    split at hr
    · revert hr
      generalize Re.compilePat true (dqPattern d1 (maxKey g.quotes)) 8 = x
      cases x with
      | error e => intro hr; cases hr
      | ok p =>
        simp only
        generalize Re.scanAll p data 0 data.length true = y
        cases y with
        | error e => intro hr; cases hr
        | ok ms =>
          intro hr
          cases hr
          exact hd
    · cases hr
      exact hd

theorem guessQuote_delim (dl : Option (List Nat)) (data q d : List Nat) (dq skip : Bool)
    (hr : guessQuote data dl = .ok (q, dq, d, skip)) : d = [] ∨ inDelims dl d = true := by
  have key : ∀ l : List (List Nat × Nat × Option Nat × Option Nat),
      guessQuote.go data dl l = .ok (q, dq, d, skip) → d = [] ∨ inDelims dl d = true := by
    intro l
    induction l with
    | nil =>
      intro h
      cases h
      exact .inl rfl
    | cons x t ih =>
      obtain ⟨r, qi, di, si⟩ := x
      intro h
      simp only [guessQuote.go, bind, Except.bind] at h
      revert h
      generalize Re.compilePat true r (16 ||| 8) = a
      cases a with
      | error e => intro h; cases h
      | ok p =>
        simp only
        generalize Re.findall p data 0 data.length = b
        cases b with
        | error e => intro h; cases h
        | ok ms =>
          simp only
          split
          · exact ih
          · intro h
            exact gqFinish_delim dl data _ (tally_keys dl qi di si ms {} (by simp)) q d dq skip h
  exact key _ hr

theorem setKey_keys {β : Type} (d : List (Nat × β)) (x : Nat) (v : β) (k : Nat)
    (hk : k ∈ (setKey d x v).map (·.1)) : k ∈ d.map (·.1) ∨ k = x := by
  induction d with
  | nil =>
    simp only [setKey, List.map_cons, List.map_nil, List.mem_singleton] at hk
    exact .inr hk
  | cons y r ih =>
    obtain ⟨a, w⟩ := y
    simp only [setKey] at hk
    split at hk
    · simp only [List.map_cons, List.mem_cons] at hk ⊢
      rcases hk with hk | hk
      · exact .inl (.inl hk)
      · exact .inl (.inr hk)
    · simp only [List.map_cons, List.mem_cons] at hk ⊢
      rcases hk with hk | hk
      · exact .inl (.inl hk)
      · rcases ih hk with h | h
        · exact .inl (.inr h)
        · exact .inr h

/-- The candidates all pass `delimiters`. -/
def KeysOk (dl : Option (List Nat)) (d : List (Nat × (Nat × Int))) : Prop :=
  ∀ k ∈ d.map (·.1), allowed dl k = true

theorem scanModes_ok (dl : Option (List Nat)) (t C : Nat) : ∀ (m d : List (Nat × (Nat × Int))),
    KeysOk dl d → KeysOk dl (scanModes dl t C m d) := by
  intro m
  induction m with
  | nil => intro d h; exact h
  | cons x r ih =>
    obtain ⟨k, v⟩ := x
    intro d h
    simp only [scanModes]
    apply ih
    split
    · rename_i hk
      intro y hy
      rcases setKey_keys _ _ _ _ hy with h1 | h1
      · exact h y h1
      · subst h1
        simp only [Bool.and_eq_true] at hk
        exact hk.2
    · exact h

theorem consistency_ok (dl : Option (List Nat)) (t : Nat) (m : List (Nat × (Nat × Int))) :
    ∀ (cs : List Nat) (d : List (Nat × (Nat × Int))), KeysOk dl d →
    KeysOk dl (consistencyLoop dl t m cs d) := by
  intro cs
  induction cs with
  | nil => intro d h; exact h
  | cons c r ih =>
    intro d h
    simp only [consistencyLoop]
    split
    · exact ih _ (scanModes_ok dl t c m d h)
    · exact h

theorem gdLoop_ok (dl : Option (List Nat)) (data : List (List Nat)) (chunk : Nat) :
    ∀ (fuel it start stop : Nat) (cf : List (Nat × List (Nat × Nat))) (modes d : List (Nat × (Nat × Int))),
    KeysOk dl d →
    match gdLoop dl data chunk fuel it start stop cf modes d with
    | .inl x => allowed dl x.1 = true
    | .inr d => KeysOk dl d := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ d h; exact h
  | succ fuel ih =>
    intro it start stop cf modes d h
    by_cases hs : start < data.length
    · rw [gdLoop, if_pos hs]
      dsimp only
      have h2 := consistency_ok dl (min (chunk * (it + 1)) data.length)
        (updateModes modes (((data.drop start).take (stop - start)).foldl addLine cf)) consistencySteps d h
      generalize consistencyLoop dl (min (chunk * (it + 1)) data.length)
        (updateModes modes (((data.drop start).take (stop - start)).foldl addLine cf)) consistencySteps d = d2 at h2 ⊢
      match d2, h2 with
      | [(k, v)], h2 =>
        exact h2 k (by simp)
      | [], h2 =>
        exact ih _ _ _ _ _ _ h2
      | a :: b :: t, h2 =>
        exact ih _ _ _ _ _ _ h2
    · rw [gdLoop, if_neg hs]
      exact h

theorem lastItem_mem : ∀ d : List (Nat × (Nat × Int)), d ≠ [] → lastItem d ∈ d.map (·.1) := by
  intro d hd
  match d, hd with
  | x :: r, _ =>
    have : ∀ (l : List (Nat × (Nat × Int))) (b : Nat × (Nat × Int)) (f : Nat × (Nat × Int) → Nat × (Nat × Int) → Bool),
        (l.foldl (fun b y => if f b y then y else b) b) = b ∨
        (l.foldl (fun b y => if f b y then y else b) b) ∈ l := by
      intro l
      induction l with
      | nil => intro b _; exact .inl rfl
      | cons y t ih =>
        intro b f
        simp only [List.foldl_cons]
        split
        · rcases ih y f with h | h
          · exact .inr (by rw [h]; simp)
          · exact .inr (List.mem_cons_of_mem _ h)
        · rcases ih b f with h | h
          · exact .inl h
          · exact .inr (List.mem_cons_of_mem _ h)
    simp only [lastItem, List.map_cons, List.mem_cons, List.mem_map]
    rcases this r x (fun b y => decide (y.2.1 > b.2.1) || (decide (y.2.1 == b.2.1) && (decide (y.2.2 > b.2.2) ||
          (decide (y.2.2 == b.2.2) && decide (y.1 > b.1))))) with h | h
    · exact .inl (by rw [h])
    · exact .inr ⟨_, h, rfl⟩

theorem guessDelimiter_ok (dl : Option (List Nat)) (s d : List Nat) (skip : Bool)
    (h : guessDelimiter s dl = (d, skip)) : d = [] ∨ ∃ c, d = [c] ∧ allowed dl c = true := by
  unfold guessDelimiter at h
  simp only at h
  generalize hd : (splitNL s).filter (!·.isEmpty) = data at h
  have h0 := gdLoop_ok dl data (min 10 data.length) (data.length + 1) 0 0 (min 10 data.length)
    ((List.range 127).map fun c => (c, ([] : List (Nat × Nat)))) [] [] (by simp [KeysOk])
  generalize hr : gdLoop dl data (min 10 data.length) (data.length + 1) 0 0 (min 10 data.length)
    ((List.range 127).map fun c => (c, ([] : List (Nat × Nat)))) [] [] = r at h h0
  cases r with
  | inl x =>
    obtain ⟨k, sk⟩ := x
    simp only [Prod.mk.injEq] at h
    exact .inr ⟨k, h.1.symm, h0⟩
  | inr d2 =>
    by_cases he : d2.isEmpty = true
    · simp only [he, if_true, Prod.mk.injEq] at h
      exact .inl h.1.symm
    · simp only [he, Bool.false_eq_true, if_false] at h
      have hne : d2 ≠ [] := by
        intro h1
        simp [h1] at he
      generalize hh : (if d2.length > 1 then preferred.find? (fun p => d2.any (·.1 == p)) else none) = x at h
      cases x with
      | some p =>
        simp only [Prod.mk.injEq] at h
        refine .inr ⟨p, h.1.symm, h0 p ?_⟩
        split at hh
        · have := List.find?_some hh
          simp only [List.any_eq_true, beq_iff_eq] at this
          obtain ⟨y, h1, h2⟩ := this
          exact List.mem_map.2 ⟨y, h1, h2⟩
        · cases hh
      | none =>
        simp only [Prod.mk.injEq] at h
        exact .inr ⟨_, h.1.symm, h0 _ (lastItem_mem d2 hne)⟩

/-- `sniff(sample, delimiters)` returns a delimiter from `delimiters`: the docs' "it is interpreted as
a string containing possible valid delimiter characters". -/
def SniffRespectsDelimiters : Prop :=
  ∀ (s ds : List Nat) (r : Sniffed), sniff s (some ds) = .ok r →
    ∃ c, r.delimiter.head? = some c ∧ c ∈ ds

theorem sniffRespectsDelimiters_proven : SniffRespectsDelimiters := by
  intro s ds r h
  unfold sniff at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  generalize hs : (crlf s).map (fun c => if c == 13 then 10 else c) = t at h
  cases hq : guessQuote t (some ds) with
  | error e =>
    rw [hq] at h
    cases h
  | ok x =>
    rw [hq] at h
    obtain ⟨q, dq, d, skip⟩ := x
    simp only at h
    have h1 := guessQuote_delim (some ds) t q d dq skip hq
    by_cases he : d.isEmpty = true
    · simp only [he, if_true] at h
      generalize hg : guessDelimiter t (some ds) = g at h
      obtain ⟨d2, s2⟩ := g
      simp only at h
      rcases guessDelimiter_ok (some ds) t d2 s2 hg with h2 | ⟨c, h2, h3⟩
      · subst h2
        simp [throw, throwThe, MonadExceptOf.throw] at h
      · subst h2
        simp only [List.isEmpty_cons, Bool.false_eq_true, if_false] at h
        cases h
        exact ⟨c, rfl, by simpa [allowed] using h3⟩
    · simp only [he, Bool.false_eq_true, if_false] at h
      have hne : d ≠ [] := by
        intro h0
        simp [h0] at he
      rcases h1 with h1 | h1
      · exact absurd h1 hne
      · cases h
        unfold inDelims at h1
        simp only at h1
        cases hc : d.head? with
        | none =>
          rw [hc] at h1
          cases h1
        | some c =>
          rw [hc] at h1
          exact ⟨c, rfl, by simpa using h1⟩

end PyLean.TextLibs.Csv
