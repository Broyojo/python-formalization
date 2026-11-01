import PyLean.TextLibs.ShlexModel

/-! Properties of `shlex`. The round trip walks the state machine over what `quote` writes. -/

namespace PyLean.TextLibs.Shlex

open PyLean

set_option linter.unusedSimpArgs false

/-- The lexer of `split(s)`, with `wordchars` left free: the walk does not depend on it. -/
def scOf (W : List Nat) : Cfg :=
  { posix := true, commenters := [], wordchars := W, whitespace := [32, 9, 13, 10], whitespaceSplit := true,
    quotes := [39, 34], escape := [92], escapedquotes := [34], punct := [] }

theorem split_is_scOf : splitCfg false true = scOf (wordcharsOf true) := rfl

/-- A lexer in a plain state. -/
def M (d : List Nat) (st : Option Nat) (t : List Nat) (n : Nat) : Lx :=
  { src := { data := d }, state := st, token := t, lineno := n }

def nl (c n : Nat) : Nat := if c == 10 then n + 1 else n

section
variable (W : List Nat) (f : Nat) (q : Bool) (e : Nat) (d t : List Nat) (n : Nat)

theorem rt_read (c : Nat) (st : Option Nat) : readToken (scOf W) (f + 1) q e (M (c :: d) st t n) =
    step (scOf W) f q e (M d st t n) (some c) := by
  simp only [readToken, scOf, List.isEmpty_nil, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false]
  rfl

theorem rt_eof (st : Option Nat) : readToken (scOf W) (f + 1) q e (M [] st t n) =
    step (scOf W) f q e (M [] st t n) none := by
  simp only [readToken, scOf, List.isEmpty_nil, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false]
  rfl

theorem safe_plain (c : Nat) (h : safeChar c = true) :
    c ≠ 32 ∧ c ≠ 9 ∧ c ≠ 13 ∧ c ≠ 10 ∧ c ≠ 39 ∧ c ≠ 34 ∧ c ≠ 92 := by
  simp only [safeChar, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  omega

theorem word_step (c : Nat) (h : safeChar c = true) :
    readToken (scOf W) (f + 1) q e (M (c :: d) (some 97) t n) =
      readToken (scOf W) f q e (M d (some 97) (t ++ [c]) n) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := safe_plain c h
  rw [rt_read, step]
  simp [scOf, M, h1, h2, h3, h4, h5, h6, h7]

theorem word_start (c : Nat) (h : safeChar c = true) :
    readToken (scOf W) (f + 1) q e (M (c :: d) (some 32) [] n) =
      readToken (scOf W) f q e (M d (some 97) [c] n) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := safe_plain c h
  rw [rt_read, step]
  by_cases hw : W.contains c = true <;> simp [scOf, M, h1, h2, h3, h4, h5, h6, h7, hw]

theorem open_quote (hW : W.contains 39 = false) : readToken (scOf W) (f + 1) q e (M (39 :: d) (some 32) [] n) =
    readToken (scOf W) f q e (M d (some 39) [] n) := by
  have hw' : 39 ∉ W := by simpa using hW
  rw [rt_read, step]
  simp [scOf, M, hw']

theorem body_step (c : Nat) (h : c ≠ 39) :
    readToken (scOf W) (f + 1) q e (M (c :: d) (some 39) t n) =
      readToken (scOf W) f true e (M d (some 39) (t ++ [c]) (nl c n)) := by
  rw [rt_read, step]
  by_cases h10 : c = 10
  · subst h10
    simp [scOf, M, nl]
  · simp [scOf, M, nl, h, h10]

theorem close_quote : readToken (scOf W) (f + 1) q e (M (39 :: d) (some 39) t n) =
    readToken (scOf W) f true e (M d (some 97) t n) := by
  rw [rt_read, step]
  simp [scOf, M]

/-- `'"'"'` inside a quoted string is one `'`. -/
theorem five_step : readToken (scOf W) (f + 5) q e (M (39 :: 34 :: 39 :: 34 :: 39 :: d) (some 39) t n) =
    readToken (scOf W) f true e (M d (some 39) (t ++ [39]) n) := by
  rw [show f + 5 = (f + 4) + 1 from rfl, close_quote]
  have a : readToken (scOf W) (f + 3 + 1) true e (M (34 :: 39 :: 34 :: 39 :: d) (some 97) t n) =
      readToken (scOf W) (f + 3) true e (M (39 :: 34 :: 39 :: d) (some 34) t n) := by
    rw [rt_read, step]
    simp [scOf, M]
  have b : readToken (scOf W) (f + 2 + 1) true e (M (39 :: 34 :: 39 :: d) (some 34) t n) =
      readToken (scOf W) (f + 2) true e (M (34 :: 39 :: d) (some 34) (t ++ [39]) n) := by
    rw [rt_read, step]
    simp [scOf, M]
  have c : readToken (scOf W) (f + 1 + 1) true e (M (34 :: 39 :: d) (some 34) (t ++ [39]) n) =
      readToken (scOf W) (f + 1) true e (M (39 :: d) (some 97) (t ++ [39]) n) := by
    rw [rt_read, step]
    simp [scOf, M]
  have g : readToken (scOf W) (f + 1) true e (M (39 :: d) (some 97) (t ++ [39]) n) =
      readToken (scOf W) f true e (M d (some 39) (t ++ [39]) n) := by
    rw [rt_read, step]
    simp [scOf, M]
  rw [a, b, c, g]

/-- The end of a token, at a space. -/
theorem end_space (hq : !t.isEmpty || q = true) :
    readToken (scOf W) (f + 1) q e (M (32 :: d) (some 97) t n) =
      .ok (M d (some 32) [] n, if !q && t.isEmpty then none else some t) := by
  rw [rt_read, step]
  have h1 : (!t.isEmpty || q) = true := hq
  simp [scOf, M, finish, h1]

/-- The end of a token, at the end of the text. -/
theorem end_eof : readToken (scOf W) (f + 1) q e (M [] (some 97) t n) =
    .ok (M [] none [] n, if !q && t.isEmpty then none else some t) := by
  rw [rt_eof, step]
  simp [scOf, M, finish]

/-- After the end of the text, `read_token` gives `None`, the `eof` of POSIX mode. -/
theorem past_end : readToken (scOf W) (f + 1) false e (M [] none [] n) = .ok (M [] none [] n, none) := by
  rw [rt_eof, step]
  simp [scOf, M, finish]

theorem blank_end : readToken (scOf W) (f + 1) false e (M [] (some 32) [] n) = .ok (M [] none [] n, none) := by
  rw [rt_eof, step]
  simp [scOf, M, finish]

end

/-- The safe run: to the end of the characters. -/
theorem safe_run (W : List Nat) (e : Nat) : ∀ (s t d : List Nat) (f n : Nat) (q : Bool), s.all safeChar = true →
    readToken (scOf W) (f + s.length) q e (M (s ++ d) (some 97) t n) =
      readToken (scOf W) f q e (M d (some 97) (t ++ s) n) := by
  intro s
  induction s with
  | nil => intro t d f n q _; simp
  | cons c r ih =>
    intro t d f n q h
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.length_cons, show f + (r.length + 1) = (f + r.length) + 1 by omega, List.cons_append,
      word_step W _ q e _ t n c h.1, ih _ _ _ _ _ h.2]
    simp

/-- The quoted body, by `quoteBody`: the lexer stays in the quote and ends with `s` added. -/
theorem body_run (W : List Nat) (e : Nat) : ∀ (s t d : List Nat) (f n : Nat) (q : Bool),
    ∃ n', ∃ q', (s = [] ∨ q' = true) ∧ (q = true → q' = true) ∧
      readToken (scOf W) (f + (quoteBody s).length) q e (M (quoteBody s ++ d) (some 39) t n) =
        readToken (scOf W) f q' e (M d (some 39) (t ++ s) n') := by
  intro s
  induction s with
  | nil =>
    intro t d f n q
    exact ⟨n, q, .inl rfl, id, by simp [quoteBody]⟩
  | cons c r ih =>
    intro t d f n q
    have hb : quoteBody (c :: r) = (if c == 39 then [39, 34, 39, 34, 39] else [c]) ++ quoteBody r := by
      simp [quoteBody]
    by_cases h : c = 39
    · subst h
      obtain ⟨n', q', _, h2, h3⟩ := ih (t ++ [39]) d f n true
      refine ⟨n', q', .inr (h2 rfl), fun _ => h2 rfl, ?_⟩
      rw [hb]
      simp only [beq_self_eq_true, if_true, List.cons_append, List.nil_append, List.length_cons]
      rw [show f + ((quoteBody r).length + 1 + 1 + 1 + 1 + 1) = (f + (quoteBody r).length) + 5 by omega,
        five_step, h3]
      simp
    · have hne : (c == 39) = false := by simpa using h
      obtain ⟨n', q', _, h2, h3⟩ := ih (t ++ [c]) d f (nl c n) true
      refine ⟨n', q', .inr (h2 rfl), fun _ => h2 rfl, ?_⟩
      rw [hb]
      simp only [hne, Bool.false_eq_true, if_false, List.cons_append, List.nil_append, List.length_cons]
      rw [show f + ((quoteBody r).length + 1) = (f + (quoteBody r).length) + 1 by omega,
        body_step W _ q e _ t n c h, h3]
      simp

/-- One token of `quote`'s output, from the start of a token to just past it. `end_` is what follows:
a space, or the end of the text. -/
theorem token_go (W : List Nat) (hW : W.contains 39 = false) (a : List Nat) (e n f : Nat)
    (hf : (quoteS a).length + 2 ≤ f) :
    (∀ d, ∃ n', readToken (scOf W) f false e (M (quoteS a ++ 32 :: d) (some 32) [] n) =
      .ok (M d (some 32) [] n', some a)) ∧
    (∃ n', readToken (scOf W) f false e (M (quoteS a) (some 32) [] n) = .ok (M [] none [] n', some a)) := by
  by_cases h0 : a.isEmpty = true
  · have ha : a = [] := by simpa using h0
    subst ha
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 3 + 1 := ⟨f - 4, by simp [quoteS] at hf; omega⟩
    have hq : quoteS [] = [39, 39] := rfl
    rw [hq]
    constructor
    · intro d
      refine ⟨n, ?_⟩
      show readToken (scOf W) (g + 3 + 1) false e (M (39 :: 39 :: 32 :: d) (some 32) [] n) = _
      rw [open_quote W _ _ _ _ _ hW, show g + 3 = (g + 2) + 1 from rfl, close_quote,
        show g + 2 = (g + 1) + 1 from rfl, end_space W _ _ _ _ _ _ (by simp)]
      simp
    · refine ⟨n, ?_⟩
      show readToken (scOf W) (g + 3 + 1) false e (M (39 :: 39 :: []) (some 32) [] n) = _
      rw [open_quote W _ _ _ _ _ hW, show g + 3 = (g + 2) + 1 from rfl, close_quote,
        show g + 2 = (g + 1) + 1 from rfl, end_eof]
      simp
  · have hne : a.isEmpty = false := by simpa using h0
    by_cases hs : a.all safeChar = true
    · have hq : quoteS a = a := by simp [quoteS, hne, hs]
      rw [hq] at hf ⊢
      match a, hs, hne, hf with
      | c :: r, hs, _, hf =>
        simp only [List.all_cons, Bool.and_eq_true] at hs
        simp only [List.length_cons] at hf
        obtain ⟨g, rfl⟩ : ∃ g, f = (g + 1) + r.length + 1 := ⟨f - r.length - 2, by omega⟩
        constructor
        · intro d
          refine ⟨n, ?_⟩
          rw [List.cons_append, word_start W _ _ e _ n c hs.1, safe_run W e r _ _ _ _ _ hs.2,
            end_space W _ _ _ _ _ _ (by simp)]
          simp
        · refine ⟨n, ?_⟩
          have := word_start W ((g + 1) + r.length) false e r n c hs.1
          rw [this]
          have h2 := safe_run W e r [c] [] (g + 1) n false hs.2
          rw [List.append_nil] at h2
          rw [h2, end_eof]
          simp
    · have hq : quoteS a = 39 :: quoteBody a ++ [39] := by simp [quoteS, hne, hs]
      rw [hq] at hf ⊢
      simp only [List.cons_append, List.length_cons, List.length_append, List.length_nil] at hf ⊢
      obtain ⟨g, rfl⟩ : ∃ g, f = (g + 1 + 1 + 1 - 1 + 0) + (quoteBody a).length + 1 := ⟨f - (quoteBody a).length - 3, by omega⟩
      have hr : ∀ d : List Nat, ∃ n' , ∃ q', q' = true ∧
          readToken (scOf W) ((g + 2) + (quoteBody a).length + 1) false e (M (39 :: (quoteBody a ++ 39 :: d)) (some 32) [] n) =
            readToken (scOf W) (g + 1) true e (M d (some 97) a n') := by
        intro d
        obtain ⟨n', q', h1, _, h3⟩ := body_run W e a [] (39 :: d) (g + 2) n false
        have hq' : q' = true := by
          rcases h1 with h1 | h1
          · subst h1
            simp at hne
          · exact h1
        subst hq'
        refine ⟨n', true, rfl, ?_⟩
        rw [open_quote W _ _ _ _ _ hW, h3, show g + 2 = (g + 1) + 1 from rfl, close_quote]
        simp
      constructor
      · intro d
        obtain ⟨n', _, _, h⟩ := hr (32 :: d)
        refine ⟨n', ?_⟩
        rw [List.append_assoc]
        simp only [List.cons_append, List.nil_append]
        rw [show g + 1 + 1 + 1 - 1 + 0 = g + 2 by omega, h, end_space W _ _ _ _ _ _ (by simp)]
        simp [hne]
      · obtain ⟨n', _, _, h⟩ := hr []
        refine ⟨n', ?_⟩
        rw [show g + 1 + 1 + 1 - 1 + 0 = g + 2 by omega, h, end_eof]
        simp [hne]

theorem lexAll_succ (c : Cfg) (F calls : Nat) (l : Lx) : lexAll c F (calls + 1) l =
    match getToken c F l with
    | .error e => .error e
    | .ok (l, t) =>
      if t == eofOf c then .ok []
      else
        match lexAll c F calls l with
        | .error e => .error e
        | .ok r => .ok (t.getD [] :: r) := by
  rw [lexAll]
  rfl

theorem eof_sc (W : List Nat) : eofOf (scOf W) = none := rfl

/-- `lexAll` walks the tokens of `join`. -/
theorem lex_go (W : List Nat) (hW : W.contains 39 = false) (F : Nat) : ∀ (args : List (List Nat))
    (calls n : Nat) (hd : List Nat),
    (∀ a ∈ hd :: args, (quoteS a).length + 2 ≤ F) → args.length + 2 ≤ calls → 2 ≤ F →
    lexAll (scOf W) F calls (M (List.intercalate [32] ((hd :: args).map quoteS)) (some 32) [] n) = .ok (hd :: args) := by
  intro args
  induction args with
  | nil =>
    intro calls n hd hf hc h2
    obtain ⟨c2, rfl⟩ : ∃ c, calls = c + 1 + 1 := ⟨calls - 2, by simp at hc; omega⟩
    obtain ⟨n', h⟩ := (token_go W hW hd 32 n F (hf hd (by simp))).2
    obtain ⟨g, rfl⟩ : ∃ g, F = g + 1 := ⟨F - 1, by omega⟩
    have h1 : getToken (scOf W) (g + 1) (M (quoteS hd) (some 32) [] n) = .ok (M [] none [] n', some hd) := h
    have h3 : getToken (scOf W) (g + 1) (M [] none [] n') = .ok (M [] none [] n', none) := past_end W g 32 n'
    simp only [List.map_cons, List.map_nil, List.intercalate_singleton]
    have hne : (some hd == eofOf (scOf W)) = false := by
      rw [eof_sc]
      rfl
    rw [lexAll_succ, h1]
    simp only [hne, Bool.false_eq_true, if_false]
    rw [lexAll_succ, h3]
    simp [eof_sc]
  | cons b rest ih =>
    intro calls n hd hf hc h2
    obtain ⟨c2, rfl⟩ : ∃ c, calls = c + 1 := ⟨calls - 1, by simp at hc; omega⟩
    have hj : List.intercalate [32] ((hd :: b :: rest).map quoteS) =
        quoteS hd ++ 32 :: List.intercalate [32] ((b :: rest).map quoteS) := by
      simp [List.intercalate_cons_cons]
    obtain ⟨n', h⟩ := (token_go W hW hd 32 n F (hf hd (by simp))).1 (List.intercalate [32] ((b :: rest).map quoteS))
    have h1 : getToken (scOf W) F (M (quoteS hd ++ 32 :: List.intercalate [32] ((b :: rest).map quoteS)) (some 32) [] n) =
        .ok (M (List.intercalate [32] ((b :: rest).map quoteS)) (some 32) [] n', some hd) := h
    have hne : (some hd == eofOf (scOf W)) = false := by
      rw [eof_sc]
      rfl
    rw [hj, lexAll_succ, h1]
    have hr := ih c2 n' b (fun a ha => hf a (List.mem_cons_of_mem _ ha)) (by simp at hc ⊢; omega) h2
    simp only [hne, Bool.false_eq_true, if_false]
    rw [hr]
    rfl

theorem quote_ne (a : List Nat) : 1 ≤ (quoteS a).length := by
  unfold quoteS
  split
  · simp
  · split
    · cases a with
      | nil => simp_all
      | cons x t => simp
    · simp

/-- The sizes of what `join` writes. -/
theorem join_len : ∀ (args : List (List Nat)) (hd : List Nat),
    (hd :: args).length ≤ (List.intercalate [32] ((hd :: args).map quoteS)).length ∧
    ∀ a ∈ hd :: args, (quoteS a).length ≤ (List.intercalate [32] ((hd :: args).map quoteS)).length := by
  intro args
  induction args with
  | nil =>
    intro hd
    simp only [List.map_cons, List.map_nil, List.intercalate_singleton, List.length_cons, List.length_nil]
    exact ⟨by have := quote_ne hd; omega, fun a ha => by simp at ha; rw [ha]; exact Nat.le_refl _⟩
  | cons b rest ih =>
    intro hd
    have hj : List.intercalate [32] ((hd :: b :: rest).map quoteS) =
        quoteS hd ++ 32 :: List.intercalate [32] ((b :: rest).map quoteS) := by
      simp [List.intercalate_cons_cons]
    obtain ⟨h1, h2⟩ := ih b
    have hq := quote_ne hd
    rw [hj]
    simp only [List.length_append, List.length_cons] at h1 ⊢
    refine ⟨by omega, fun a ha => ?_⟩
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · omega
    · have := h2 a (List.mem_cons.2 ha)
      omega

/-- `shlex.split(shlex.join(args)) == args`, the round trip the docs give `join` for, for every list
of strings: spaces, quotes, newlines, backslashes, empty strings and non-ASCII text included. -/
def JoinRoundTrip : Prop :=
  ∀ args : List (List Nat), split (joinS args) false true = .ok args

/-- The words of POSIX mode hold no `'`. -/
theorem word_no_quote : (wordcharsOf true).contains 39 = false := by
  decide +kernel

theorem joinRoundTrip_proven : JoinRoundTrip := by
  intro args
  unfold split joinS
  rw [split_is_scOf]
  match args with
  | [] =>
    show lexAll (scOf _) (0 * 2 + 8) (0 + 2) (M [] (some 32) [] 1) = _
    rw [lexAll_succ]
    have h : getToken (scOf (wordcharsOf true)) (0 * 2 + 8) (M [] (some 32) [] 1) = .ok (M [] none [] 1, none) :=
      blank_end _ _ _ _
    rw [h]
    simp [eof_sc]
  | hd :: rest =>
    obtain ⟨h1, h2⟩ := join_len rest hd
    generalize hT : List.intercalate [32] ((hd :: rest).map quoteS) = T at *
    have := lex_go (wordcharsOf true) word_no_quote (T.length * 2 + 8) rest (T.length + 2) 1 hd
      (fun a ha => by have := h2 a ha; omega) (by simp at h1; omega) (by omega)
    rw [hT] at this
    exact this

/-- `quote` is for strings, and raises `TypeError` for anything else. A false object gets past that
check, because `if not s` comes first. -/
def QuoteRejectsNonStr : Prop :=
  ∀ (cls : String) (b : Bool), ∃ m, quote (.other cls (.ok b)) = .error (.typeError m)

theorem quoteRejectsNonStr_refuted : ¬QuoteRejectsNonStr := by
  intro h
  obtain ⟨m, hm⟩ := h "NoneType" false
  cases hm

/-- A stream that raises stops the lexer with that exception, on the first read it reaches. -/
def StreamFailurePasses : Prop :=
  ∀ (c : Cfg) (f : Nat) (q : Bool) (e0 : Nat) (d : List Nat) (e : PyExc) (l : Lx),
    l.src = { data := d, failAt := some (0, e) } → l.chars = [] →
    readToken c (f + 1) q e0 l = .error e

theorem streamFailurePasses_proven : StreamFailurePasses := by
  intro c f q e0 d e l h1 h2
  rw [readToken]
  simp [h1, h2, Src.read1]

/-- A closing quote is required in either mode, and its absence is the `ValueError` the docs of
`split` imply: an open quote at the end of the text raises, whatever was read. -/
def OpenQuoteRaises : Prop :=
  ∀ (W t : List Nat) (f n : Nat) (q : Bool) (e : Nat),
    readToken (scOf W) (f + 1) q e (M [] (some 39) t n) = .error (.valueError "No closing quotation")

theorem openQuoteRaises_proven : OpenQuoteRaises := by
  intro W t f n q e
  rw [rt_eof, step]
  simp [scOf, M]

end PyLean.TextLibs.Shlex
