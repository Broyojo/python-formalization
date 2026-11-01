import PyLean.PyGrammar.Peg.Facts

/-!
The failure paths of `Parser/pegen_errors.c` and `_PyPegen_run_parser`. The aim is one invariant,
`ParserNeverSilent`: `_PyPegen_run_parser` never returns `NULL` without an exception set, for any
source and any parser state. Everything else here is what that needs: each raising function
sets an exception on every path and leaves the parser where it was.

"No exception yet" is `Fresh`, the guard at the top of the raising functions, whose other side is
`FirstErrorWins`.
-/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- The parser's position and token storage survive `f`, whatever state it starts from. -/
def Keeps {α : Type} (f : PM α) : Prop :=
  ∀ p : PS, (f p).2.mark = p.mark ∧ (f p).2.tokens = p.tokens ∧ (f p).2.memo = p.memo

/-- No exception to protect, the guard of `_PyPegen_raise_error_known_location`. -/
abbrev Fresh (p : PS) : Prop := ¬(p.errorIndicator = true ∧ p.errOccurred = true)

theorem fresh_guard {p : PS} (h : Fresh p) : (p.errorIndicator && p.errOccurred) = false := by
  cases h1 : p.errorIndicator <;> cases h2 : p.errOccurred <;> simp_all

theorem keeps_setErr (e : PyError) : Keeps (setErr e) := fun _ => ⟨rfl, rfl, rfl⟩

/-- `_PyPegen_raise_error_known_location`: with no exception yet, it sets the given class, message
and line, turns the `CURRENT_POS` end line into the tokenizer's, and marks the error. -/
theorem raiseKnownLocation_err (p : PS) (cls msg : String) (a b c d : Int) (h : Fresh p) :
    ∃ e : PyError, (raiseKnownLocation cls a b c d msg p).2.tok.err = some e ∧
      e.cls = cls ∧ e.msg = msg ∧ e.lineno = some a ∧
      e.endLineno = some (if c == -5 then p.tok.lineno else c) ∧
      (raiseKnownLocation cls a b c d msg p).2.errorIndicator = true := by
  have g := fresh_guard h
  simp only [raiseKnownLocation, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, g,
    pure, Bool.false_eq_true, ↓reduceIte, set, StateT.set, setErr, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, MonadState.modifyGet, MonadStateOf.set]
  refine ⟨_, rfl, ?_⟩
  simp

theorem keeps_raiseKnownLocation (cls msg : String) (a b c d : Int) :
    Keeps (raiseKnownLocation cls a b c d msg) := by
  intro p
  by_cases g : (p.errorIndicator && p.errOccurred) = true
  · simp only [raiseKnownLocation, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, g,
      pure, StateT.pure, ↓reduceIte]
    simp
  · simp only [raiseKnownLocation, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, g,
      pure, ↓reduceIte, set, StateT.set, setErr, modify, modifyGet,
      MonadStateOf.modifyGet, StateT.modifyGet, MonadState.modifyGet, MonadStateOf.set]
    refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl

/-- `_PyPegen_raise_error_known_location` as a registry statement: the contract above, and it never
moves the parser. -/
def RaiseKnownLocation : Prop := ∀ (cls msg : String) (a b c d : Int),
  Keeps (raiseKnownLocation cls a b c d msg) ∧
  ∀ p : PS, Fresh p →
    ∃ e : PyError, (raiseKnownLocation cls a b c d msg p).2.tok.err = some e ∧
      e.cls = cls ∧ e.msg = msg ∧ e.lineno = some a ∧
      e.endLineno = some (if c == -5 then p.tok.lineno else c) ∧
      (raiseKnownLocation cls a b c d msg p).2.errorIndicator = true

theorem raiseKnownLocation_proven : RaiseKnownLocation := fun cls msg a b c d =>
  ⟨keeps_raiseKnownLocation cls msg a b c d, fun p h => raiseKnownLocation_err p cls msg a b c d h⟩

/-- `f` always leaves an exception set, and does not move the parser: what every path of the
error functions owes `_PyPegen_run_parser`. -/
def Raises (f : PM Unit) : Prop := Keeps f ∧ ∀ p : PS, (f p).2.errOccurred = true

theorem Raises.ite {c : Prop} [Decidable c] {a b : PM Unit} (ha : Raises a) (hb : Raises b) :
    Raises (if c then a else b) := by
  by_cases h : c <;> simp [h, ha, hb]

theorem raises_setErr (e : PyError) : Raises (setErr e) :=
  ⟨keeps_setErr e, fun _ => rfl⟩

theorem raises_raiseKnownLocation (cls msg : String) (a b c d : Int) :
    Raises (raiseKnownLocation cls a b c d msg) := by
  refine ⟨keeps_raiseKnownLocation _ _ _ _ _ _, fun p => ?_⟩
  by_cases h : Fresh p
  · obtain ⟨e, h1, _⟩ := raiseKnownLocation_err p cls msg a b c d h
    simp [PS.errOccurred, h1]
  · have h' : p.errorIndicator = true ∧ p.errOccurred = true := by simpa [Fresh] using h
    rw [(firstErrorWins_proven p h'.1 h'.2).1 cls msg a b c d]
    exact h'.2

theorem raises_raiseErrorKnownLocation (cls msg : String) (a b c d : Int) :
    Raises (raiseErrorKnownLocation cls a b c d msg) :=
  raises_raiseKnownLocation _ _ _ _ _ _

theorem raises_raiseUnclosed : Raises raiseUnclosed :=
  ⟨fun p => (raises_raiseErrorKnownLocation _ _ _ _ _ _).1 p,
   fun p => (raises_raiseErrorKnownLocation _ _ _ _ _ _).2 p⟩

theorem raises_raiseAtToken (cls : String) (t : Token) (msg : String) :
    Raises (raiseAtToken cls t msg) :=
  ⟨fun p => (raises_raiseKnownLocation _ _ _ _ _ _).1 p,
   fun p => (raises_raiseKnownLocation _ _ _ _ _ _).2 p⟩

theorem raises_raiseError0 (cls msg : String) : Raises (raiseError0 cls msg) := by
  constructor
  · intro p
    unfold raiseError0
    simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure]
    split
    · exact ⟨rfl, rfl, rfl⟩
    · split
      · exact keeps_raiseKnownLocation _ _ _ _ _ _ p
      · exact (raises_raiseAtToken _ _ _).1 p
  · intro p
    unfold raiseError0
    simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure]
    split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      exact h.2
    · split
      · exact (raises_raiseKnownLocation _ _ _ _ _ _).2 p
      · exact (raises_raiseAtToken _ _ _).2 p

/-- `RAISE_ERROR`, `use_mark == 0`. -/
theorem raises_raiseError (cls msg : String) : Raises (raiseError cls false msg) := by
  constructor
  · intro p
    unfold raiseError
    simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    split
    · exact ⟨rfl, rfl, rfl⟩
    · split
      · exact keeps_raiseKnownLocation _ _ _ _ _ _ p
      · exact (raises_raiseAtToken _ _ _).1 p
  · intro p
    unfold raiseError
    simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      exact h.2
    · split
      · exact (raises_raiseKnownLocation _ _ _ _ _ _).2 p
      · exact (raises_raiseAtToken _ _ _).2 p

/-- `RAISE_ERROR` keeps to its contract: with no exception yet, it sets the given class and
message at the error token, and marks the error. -/
def RaiseErrorContract : Prop := ∀ (p : PS) (cls msg : String) (t : Token), Fresh p →
  ∃ e : PyError, (raiseError0 cls msg p).2.tok.err = some e ∧ e.cls = cls ∧ e.msg = msg ∧
    (raiseError0 cls msg p).2.errorIndicator = true ∧
    (p.fill = 0 → e.lineno = some 0) ∧
    (p.fill ≠ 0 → p.knownErrToken = some t → e.lineno = some t.lineno)

theorem raiseErrorContract_proven : RaiseErrorContract := by
  intro p cls msg t h
  have g := fresh_guard h
  by_cases hf : p.fill = 0
  · have hf' : (p.fill == 0) = true := by simpa using hf
    simp only [raiseError0, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
      StateT.pure, g, Bool.false_eq_true, ↓reduceIte, hf']
    obtain ⟨e, h1, h2, h3, h4, _, h6⟩ := raiseKnownLocation_err p cls msg 0 0 0 (-1) h
    exact ⟨e, h1, h2, h3, h6, fun _ => h4, fun h' => absurd hf h'⟩
  · have hf' : (p.fill == 0) = false := by simpa using hf
    simp only [raiseError0, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
      StateT.pure, g, Bool.false_eq_true, ↓reduceIte, hf']
    let u := p.knownErrToken.getD (p.tokenAt (p.fill - 1))
    obtain ⟨e, h1, h2, h3, h4, _, h6⟩ := raiseKnownLocation_err p cls msg u.lineno
      (if u.colOffset == -1 then
        if p.tok.cur == p.tok.buf then 0 else (p.tok.cur : Int) - p.tok.lineStart
       else u.colOffset + 1)
      u.endLineno (if u.endColOffset != -1 then u.endColOffset + 1 else -1) h
    refine ⟨e, h1, h2, h3, h6, fun h' => absurd h' hf, fun _ hk => ?_⟩
    rw [h4]
    simp [u, hk]

/-- `raise_unclosed_parentheses_error`: "'x' was never closed", at the innermost open bracket. -/
def RaiseUnclosed : Prop := ∀ (p : PS) (c : Nat) (line col : Int) (rest : List (Nat × Int × Int)),
  Fresh p → p.tok.parenstack = (c, line, col) :: rest →
    ∃ e : PyError, (raiseUnclosed p).2.tok.err = some e ∧ e.cls = "SyntaxError" ∧
      e.msg = s!"'{chStr c}' was never closed" ∧ e.lineno = some line

theorem raiseUnclosed_eq (p : PS) (c : Nat) (line col : Int) (rest : List (Nat × Int × Int))
    (hs : p.tok.parenstack = (c, line, col) :: rest) :
    raiseUnclosed p =
      raiseErrorKnownLocation "SyntaxError" line col line (-1)
        s!"'{chStr c}' was never closed" p := by
  have : raiseUnclosed p = (match p.tok.parenstack.headD (0, 0, 0) with
    | (c, line, col) => raiseErrorKnownLocation "SyntaxError" line col line (-1)
        s!"'{chStr c}' was never closed") p := rfl
  rw [this, hs]
  rfl

theorem raiseUnclosed_proven : RaiseUnclosed := by
  intro p c line col rest h hs
  rw [raiseUnclosed_eq p c line col rest hs]
  obtain ⟨e, h1, h2, h3, h4, _, _⟩ := raiseKnownLocation_err p "SyntaxError"
    s!"'{chStr c}' was never closed" line (if col == -5 then -5 else col + 1) line
    (if (-1 : Int) == -5 then -5 else -1 + 1) h
  exact ⟨e, h1, h2, h3, h4⟩

theorem raises_tokenizerErrorSwitch (s : TokState) : Raises (tokenizerErrorSwitch s) := by
  unfold tokenizerErrorSwitch
  dsimp only
  repeat' apply Raises.ite
  all_goals first
    | exact raises_raiseErrorKnownLocation _ _ _ _ _ _
    | exact raises_raiseUnclosed
    | exact raises_raiseError0 _ _
    | exact raises_setErr _

/-- `_Pypegen_tokenizer_error` returns `-1` from every arm of its switch, and on every arm an
exception is set, so the `-1` that `_PyPegen_fill_token` passes up is never a failure without an
exception. It reads no token and does not move the parser. -/
def TokenizerErrorSets : Prop := ∀ p : PS,
  (tokenizerError p).1 = -1 ∧ (tokenizerError p).2.errOccurred = true ∧
    (tokenizerError p).2.mark = p.mark ∧ (tokenizerError p).2.tokens = p.tokens ∧
    (tokenizerError p).2.memo = p.memo

theorem tokenizerErrorSets_proven : TokenizerErrorSets := by
  intro p
  by_cases h : p.errOccurred = true
  · simp only [tokenizerError, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, h,
      ↓reduceIte, pure, StateT.pure]
    simp [h]
  · have e : tokenizerError p = (-1, (tokenizerErrorSwitch p.tok
        { p with errorIndicator := true }).2) := by
      simp only [tokenizerError, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, h,
        ↓reduceIte, pure, StateT.pure, Bool.false_eq_true]
      rfl
    rw [e]
    have k := (raises_tokenizerErrorSwitch p.tok).1 { p with errorIndicator := true }
    exact ⟨rfl, (raises_tokenizerErrorSwitch p.tok).2 _, k.1, k.2.1, k.2.2⟩

theorem tokenizerError_proven : TokenizerErrorIsFailure := fun p =>
  (tokenizerErrorSets_proven p).1

/-- `tokenizeFullSource`, spelled out: the prompt check, then the walk, then the restore. -/
theorem tokenizeFullSource_eq (p : PS) (h : p.tok.prompt = false) :
    tokenizeFullSource p =
      let q := (tokenizeRest (p.knownErrToken.getD (p.tokenAt (p.fill - 1))).lineno
        (p.tok.src.size + 2) { p with tok := { p.tok with err := none } }).2
      ((), if !(q.tok.err.isSome && q.tok.modeIndex == 0) then
        { q with tok := { q.tok with err := p.tok.err } } else q) := by
  simp only [tokenizeFullSource, h, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure, set, StateT.set, MonadStateOf.set, Bool.false_eq_true, ↓reduceIte]
  generalize tokenizeRest _ _ _ = r
  obtain ⟨a, q⟩ := r
  cases c : (q.tok.err.isSome && q.tok.modeIndex == 0) <;> simp [c, StateT.set] <;> rfl

theorem restore_err (q : PS) (e : Option PyError) :
    (if !(q.tok.err.isSome && q.tok.modeIndex == 0) then
      { q with tok := { q.tok with err := e } } else q).tok.err =
      if q.tok.err.isSome && q.tok.modeIndex == 0 then q.tok.err else e := by
  cases c : (q.tok.err.isSome && q.tok.modeIndex == 0) <;> simp

/-- `_PyPegen_tokenize_full_source_to_check_for_errors`: "We don't want to tokenize to the end
for interactive input". Otherwise the rest of the source is tokenized, a tokenizer error in
regular mode replaces the current exception, and any other outcome puts it back. -/
def TokenizeFullSource : Prop := ∀ p : PS,
  (p.tok.prompt = true → (tokenizeFullSource p).2 = p) ∧
  (p.tok.prompt = false →
    let q := (tokenizeRest (p.knownErrToken.getD (p.tokenAt (p.fill - 1))).lineno
      (p.tok.src.size + 2) { p with tok := { p.tok with err := none } }).2
    (tokenizeFullSource p).2.tok.err =
      if q.tok.err.isSome && q.tok.modeIndex == 0 then q.tok.err else p.tok.err)

theorem tokenizeFullSource_proven : TokenizeFullSource := by
  intro p
  constructor
  · intro h
    simp [tokenizeFullSource, h, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure]
  · intro h
    rw [tokenizeFullSource_eq p h]
    exact restore_err _ _

/-- An exception set before `_PyPegen_tokenize_full_source_to_check_for_errors` is still set, or
has been replaced, after it: the function never clears the error it was called to refine. -/
theorem tokenizeFullSource_keeps_err (p : PS) (h : p.errOccurred = true) :
    (tokenizeFullSource p).2.errOccurred = true := by
  cases hp : p.tok.prompt with
  | true => rw [(tokenizeFullSource_proven p).1 hp]; exact h
  | false =>
    have := (tokenizeFullSource_proven p).2 hp
    dsimp only at this
    simp only [PS.errOccurred, this]
    split
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      exact hc.1
    · exact h

theorem tail_err (p : PS) (last : Token) (q : PS) :
    (setSyntaxErrorTail p last q).2.errOccurred = true := by
  unfold setSyntaxErrorTail
  split
  · split
    · exact raises_raiseUnclosed.2 q
    · exact (raises_raiseError0 _ _).2 q
  · split
    · exact (raises_raiseError0 _ _).2 q
    · exact tokenizeFullSource_keeps_err _ ((raises_raiseErrorKnownLocation _ _ _ _ _ _).2 q)

/-- `_Pypegen_set_syntax_error`: whatever state the second pass left, an exception is set when it
returns. With no exception yet, an `INDENT` or `DEDENT` as the last token is the indentation
error the C names. -/
def SetSyntaxError : Prop := ∀ (last : Token) (p : PS),
  (setSyntaxError last p).2.errOccurred = true ∧
  (p.errOccurred = false → p.fill ≠ 0 → last.type = TokKind.INDENT.num →
    ∃ e : PyError, (setSyntaxError last p).2.tok.err = some e ∧ e.cls = "IndentationError" ∧
      e.msg = "unexpected indent") ∧
  (p.errOccurred = false → p.fill ≠ 0 → last.type = TokKind.DEDENT.num →
    ∃ e : PyError, (setSyntaxError last p).2.tok.err = some e ∧ e.cls = "IndentationError" ∧
      e.msg = "unexpected unindent")

theorem setSyntaxError_eq (last : Token) (p : PS) (h : p.errOccurred = false) (hf : p.fill ≠ 0) :
    setSyntaxError last p = setSyntaxErrorTail p last p := by
  have hf' : (p.fill == 0) = false := by simpa using hf
  simp only [setSyntaxError, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, h, hf',
    Bool.false_eq_true, ↓reduceIte, pure, StateT.pure]

theorem setSyntaxError_proven : SetSyntaxError := by
  intro last p
  refine ⟨?_, ?_, ?_⟩
  · by_cases h : p.errOccurred = true
    · simp only [setSyntaxError, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, h,
        ↓reduceIte, pure, StateT.pure]
      split
      · exact tokenizeFullSource_keeps_err _ h
      · exact h
    · have h' : p.errOccurred = false := by simpa using h
      by_cases hf : p.fill = 0
      · have hf' : (p.fill == 0) = true := by simpa using hf
        simp only [setSyntaxError, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
          h', hf', Bool.false_eq_true, ↓reduceIte, pure, StateT.pure]
        exact tail_err _ _ _
      · rw [setSyntaxError_eq last p h' hf]
        exact tail_err _ _ _
  · intro h hf ht
    rw [setSyntaxError_eq last p h hf]
    have hg : Fresh p := by simp [Fresh, h]
    have d : (TokKind.INDENT.num == TokKind.ERRORTOKEN.num) = false := by decide
    have h1 : (last.type == TokKind.ERRORTOKEN.num && p.tok.done == E_EOF) = false := by
      simp only [ht, d, Bool.false_and]
    have h3 : (last.type == TokKind.INDENT.num) = true := by simp [ht]
    simp only [setSyntaxErrorTail, h1, h3, Bool.true_or, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨e, a, b, c, _⟩ := raiseErrorContract_proven p "IndentationError" "unexpected indent"
      last hg
    exact ⟨e, a, b, c⟩
  · intro h hf ht
    rw [setSyntaxError_eq last p h hf]
    have hg : Fresh p := by simp [Fresh, h]
    have d : (TokKind.DEDENT.num == TokKind.ERRORTOKEN.num) = false := by decide
    have d2 : (TokKind.DEDENT.num == TokKind.INDENT.num) = false := by decide
    have h1 : (last.type == TokKind.ERRORTOKEN.num && p.tok.done == E_EOF) = false := by
      simp only [ht, d, Bool.false_and]
    have h3 : (last.type == TokKind.INDENT.num) = false := by simp only [ht, d2]
    have h4 : (last.type == TokKind.DEDENT.num) = true := by simp [ht]
    simp only [setSyntaxErrorTail, h1, h3, h4, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨e, a, b, c, _⟩ := raiseErrorContract_proven p "IndentationError" "unexpected unindent"
      last hg
    exact ⟨e, a, b, c⟩

/-- `_PyPegen_run_parser` never returns `NULL` with no exception set, whatever the grammar did:
every `return NULL` in its body, on the discarded-result path, the incomplete-input path, the
non-`SyntaxError` path, after the second pass, and on a bad single statement, has an exception
behind it. So `SystemError: parser returned NULL without error` is out of reach. -/
def ParserNeverSilent : Prop := ∀ (fuel : Nat) (p : PS),
  (runParser fuel p).1 = .null → (runParser fuel p).2.errOccurred = true

theorem parserNeverSilent_proven : ParserNeverSilent := by
  intro fuel p
  rw [runParser.eq_def]
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure]
  generalize parseStart fuel p = r
  obtain ⟨res, q⟩ := r
  dsimp only
  by_cases h1 : (nonNull res && q.errOccurred) = true
  · simp only [h1, ↓reduceIte]
    simp only [Bool.and_eq_true] at h1
    exact fun _ => h1.2
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases hr : nonNull res with
    | false =>
      simp only [Bool.not_false, ↓reduceIte]
      split
      · intro _
        exact (raises_raiseError _ _).2 _
      · split
        · rename_i hc
          simp only [Bool.and_eq_true] at hc
          exact fun _ => hc.1
        · intro _
          exact (setSyntaxError_proven _ _).1
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      split
      · split
        · intro _
          exact (raises_raiseError _ _).2 _
        · intro h
          have h' : res = .null := h
          rw [h'] at hr
          simp [nonNull] at hr
      · intro h
        have h' : res = .null := h
        rw [h'] at hr
        simp [nonNull] at hr

end PyLean.PyGrammar.Peg
