import PyLean.PyGrammar.Peg.Frame

/-!
The arms of the error functions of `Parser/pegen_errors.c` and the frontier of
`_PyPegen_is_memoized`, each with the class, message and line it raises.
-/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- `f` run on `q` sets an exception of class `cls` with message `msg` (and line `line`, when
given). -/
def SetsErr (r : PS) (cls msg : String) (line : Option Int) : Prop :=
  ∃ e : PyError, r.tok.err = some e ∧ e.cls = cls ∧ e.msg = msg ∧
    (line.isSome → e.lineno = line)

theorem known_sets (q : PS) (h : Fresh q) (cls msg : String) (line col : Int) :
    SetsErr (raiseErrorKnownLocation cls line col line (-1) msg q).2 cls msg (some line) := by
  obtain ⟨e, a, b, c, d, _⟩ := raiseKnownLocation_err q cls msg line
    (if col == -5 then -5 else col + 1) line (if (-1 : Int) == -5 then -5 else -1 + 1) h
  exact ⟨e, a, b, c, fun _ => d⟩

theorem error0_sets (q : PS) (h : Fresh q) (cls msg : String) :
    SetsErr (raiseError0 cls msg q).2 cls msg none := by
  obtain ⟨e, a, b, c, _⟩ := raiseErrorContract_proven q cls msg default h
  exact ⟨e, a, b, c, fun h => by simp at h⟩

/-- The `OverflowError` of `E_COLUMNOVERFLOW`, `Parser/pegen_errors.c:70-72`. -/
def columnOverflowErr : PyError :=
  { cls := "OverflowError", msg := "Parser column offset overflow - source line is too big" }

theorem tokErr_eq (p : PS) (h : p.errOccurred = false) :
    tokenizerError p = (-1, (tokenizerErrorSwitch p.tok { p with errorIndicator := true }).2) := by
  simp only [tokenizerError, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, h,
    ↓reduceIte, pure, StateT.pure, Bool.false_eq_true]
  rfl

/-- `_Pypegen_tokenizer_error`, `Parser/pegen_errors.c:23-81`, arm by arm. With an exception
already set it returns -1 and changes nothing (`:25-27`). Otherwise it sets `error_indicator` and
raises, by `tok->done`: `E_TOKEN` "invalid token"; `E_EOF` "'c' was never closed" at the innermost
open bracket when one is open, else "unexpected EOF while parsing"; `E_DEDENT` `IndentationError`
"unindent does not match any outer indentation level"; `E_INTR` `KeyboardInterrupt`; `E_NOMEM`
`MemoryError`; `E_TABSPACE` `TabError` "inconsistent use of tabs and spaces in indentation";
`E_TOODEEP` `IndentationError` "too many levels of indentation"; `E_LINECONT` "unexpected
character after line continuation character"; `E_COLUMNOVERFLOW` `OverflowError` "Parser column
offset overflow - source line is too big"; anything else "unknown parsing error". The arms that
fall through to `RAISE_ERROR_KNOWN_LOCATION` (`:77-79`) raise on the tokenizer's line. -/
def TokenizerErrorArms : Prop := ∀ p : PS,
  (p.errOccurred = true → tokenizerError p = (-1, p)) ∧
  (p.errOccurred = false →
    let s := p.tok
    let r := (tokenizerError p).2
    (tokenizerError p).1 = -1 ∧ r.errorIndicator = true ∧
    (s.done = E_TOKEN → SetsErr r "SyntaxError" "invalid token" (some s.lineno)) ∧
    (s.done = E_EOF → ∀ c line col rest, s.level ≠ 0 → s.parenstack = (c, line, col) :: rest →
      SetsErr r "SyntaxError" s!"'{chStr c}' was never closed" (some line)) ∧
    (s.done = E_EOF → s.level = 0 → SetsErr r "SyntaxError" "unexpected EOF while parsing" none) ∧
    (s.done = E_DEDENT →
      SetsErr r "IndentationError" "unindent does not match any outer indentation level" none) ∧
    (s.done = E_INTR → r.tok.err = some { cls := "KeyboardInterrupt", msg := "" }) ∧
    (s.done = E_NOMEM → r.tok.err = some { cls := "MemoryError", msg := "" }) ∧
    (s.done = E_TABSPACE →
      SetsErr r "TabError" "inconsistent use of tabs and spaces in indentation" (some s.lineno)) ∧
    (s.done = E_TOODEEP →
      SetsErr r "IndentationError" "too many levels of indentation" (some s.lineno)) ∧
    (s.done = E_LINECONT → SetsErr r "SyntaxError"
      "unexpected character after line continuation character" (some s.lineno)) ∧
    (s.done = E_COLUMNOVERFLOW → r.tok.err = some columnOverflowErr) ∧
    (s.done ∉ [E_TOKEN, E_EOF, E_DEDENT, E_INTR, E_NOMEM, E_TABSPACE, E_TOODEEP, E_LINECONT,
      E_COLUMNOVERFLOW] → SetsErr r "SyntaxError" "unknown parsing error" (some s.lineno)))

theorem tokenizerErrorArms_proven : TokenizerErrorArms := by
  intro p
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp [tokenizerError, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, h,
      pure, StateT.pure]
  · simp only []
    rw [tokErr_eq p h]
    generalize hq : ({ p with errorIndicator := true } : PS) = q
    have fresh : Fresh q := by
      subst hq
      simp [Fresh, PS.errOccurred] at h ⊢
      exact h
    have hqt : q.tok = p.tok := by rw [← hq]
    have hqi : q.errorIndicator = true := by rw [← hq]
    refine ⟨rfl, (frame_tokenizerErrorSwitch p.tok q).grows.err hqi, fun hd => ?_,
      fun hd c line col rest hl hs => ?_, fun hd hl => ?_, fun hd => ?_, fun hd => ?_,
      fun hd => ?_, fun hd => ?_, fun hd => ?_, fun hd => ?_, fun hd => ?_, fun hd => ?_⟩
    · have e : tokenizerErrorSwitch p.tok = raiseErrorKnownLocation "SyntaxError" p.tok.lineno 0
          p.tok.lineno (-1) "invalid token" := by
        unfold tokenizerErrorSwitch
        simp [hd, E_TOKEN]
      rw [e]
      exact known_sets q fresh _ _ _ _
    · have e : tokenizerErrorSwitch p.tok = raiseUnclosed := by
        unfold tokenizerErrorSwitch
        simp [hd, E_TOKEN, E_EOF, hl]
      rw [e]
      obtain ⟨x, a, b, c', d⟩ := raiseUnclosed_proven q c line col rest fresh (by rw [hqt]; exact hs)
      exact ⟨x, a, b, c', fun _ => d⟩
    · have e : tokenizerErrorSwitch p.tok = raiseError0 "SyntaxError" "unexpected EOF while parsing" := by
        unfold tokenizerErrorSwitch
        simp [hd, E_TOKEN, E_EOF, hl]
      rw [e]
      exact error0_sets q fresh _ _
    · have e : tokenizerErrorSwitch p.tok = raiseError0 "IndentationError"
          "unindent does not match any outer indentation level" := by
        unfold tokenizerErrorSwitch
        simp [hd, E_TOKEN, E_EOF, E_DEDENT]
      rw [e]
      exact error0_sets q fresh _ _
    · have e : tokenizerErrorSwitch p.tok = setErr { cls := "KeyboardInterrupt", msg := "" } := by
        unfold tokenizerErrorSwitch
        simp [hd, E_TOKEN, E_EOF, E_DEDENT, E_INTR]
      rw [e]
      rfl
    · have e : tokenizerErrorSwitch p.tok = setErr { cls := "MemoryError", msg := "" } := by
        unfold tokenizerErrorSwitch
        simp [hd, E_TOKEN, E_EOF, E_DEDENT, E_INTR, E_NOMEM]
      rw [e]
      rfl
    · have e : tokenizerErrorSwitch p.tok = raiseErrorKnownLocation "TabError" p.tok.lineno 0
          p.tok.lineno (-1) "inconsistent use of tabs and spaces in indentation" := by
        unfold tokenizerErrorSwitch
        simp [hd, E_TOKEN, E_EOF, E_DEDENT, E_INTR, E_NOMEM, E_TABSPACE]
      rw [e]
      exact known_sets q fresh _ _ _ _
    · have e : tokenizerErrorSwitch p.tok = raiseErrorKnownLocation "IndentationError"
          p.tok.lineno 0 p.tok.lineno (-1) "too many levels of indentation" := by
        unfold tokenizerErrorSwitch
        simp [hd, E_TOKEN, E_EOF, E_DEDENT, E_INTR, E_NOMEM, E_TABSPACE, E_TOODEEP]
      rw [e]
      exact known_sets q fresh _ _ _ _
    · have e : tokenizerErrorSwitch p.tok = raiseErrorKnownLocation "SyntaxError" p.tok.lineno
          (if (p.tok.cur : Int) - p.tok.buf - 1 ≥ 0 then (p.tok.cur : Int) - p.tok.buf - 1 else 0)
          p.tok.lineno (-1) "unexpected character after line continuation character" := by
        unfold tokenizerErrorSwitch
        simp [hd, E_TOKEN, E_EOF, E_DEDENT, E_INTR, E_NOMEM, E_TABSPACE, E_TOODEEP, E_LINECONT]
      rw [e]
      exact known_sets q fresh _ _ _ _
    · have e : tokenizerErrorSwitch p.tok = setErr columnOverflowErr := by
        unfold tokenizerErrorSwitch
        simp [hd, E_TOKEN, E_EOF, E_DEDENT, E_INTR, E_NOMEM, E_TABSPACE, E_TOODEEP, E_LINECONT,
          E_COLUMNOVERFLOW, columnOverflowErr]
      rw [e]
      rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hd
      have e : tokenizerErrorSwitch p.tok = raiseErrorKnownLocation "SyntaxError" p.tok.lineno 0
          p.tok.lineno (-1) "unknown parsing error" := by
        unfold tokenizerErrorSwitch
        simp [h1, h2, h3, h4, h5, h6, h7, h8, h9]
      rw [e]
      exact known_sets q fresh _ _ _ _

/-- `_Pypegen_set_syntax_error`, `Parser/pegen_errors.c:383-424`, case by case. An exception
already set is kept, and refined by `_PyPegen_tokenize_full_source_to_check_for_errors` only when
the tokenizer is fine and the exception is a `SyntaxError` (`:386-394`). Otherwise, with a token
read: an `ERRORTOKEN` at `E_EOF` is "'c' was never closed" at the innermost open bracket, or
"unexpected EOF while parsing" with none open (`:400-407`); an `INDENT` or `DEDENT` is
`IndentationError` "unexpected indent" or "unexpected unindent" (`:409-412`); and anything else is
"invalid syntax" at the first pass's last token, then the full-source check, which may replace it
(`:414-423`). `p->fill == 0` is not stated: the second pass runs only after the first read a token,
since `_PyPegen_fill_token` counts a token on every path (`FillToken`). -/
def SetSyntaxErrorArms : Prop := ∀ (last : Token) (p : PS),
  (p.errOccurred = true → (p.tok.done = 16 ∨ p.tok.done = E_OK) →
    (∃ e, p.tok.err = some e ∧ isSyntaxErrorClass e.cls = true) →
    setSyntaxError last p = tokenizeFullSource p) ∧
  (p.errOccurred = true → ¬((p.tok.done = 16 ∨ p.tok.done = E_OK) ∧
    ∃ e, p.tok.err = some e ∧ isSyntaxErrorClass e.cls = true) →
    setSyntaxError last p = ((), p)) ∧
  (p.errOccurred = false → p.fill ≠ 0 →
    let r := (setSyntaxError last p).2
    (last.type = TokKind.ERRORTOKEN.num → p.tok.done = E_EOF → ∀ c line col rest,
      p.tok.level ≠ 0 → p.tok.parenstack = (c, line, col) :: rest →
      SetsErr r "SyntaxError" s!"'{chStr c}' was never closed" (some line)) ∧
    (last.type = TokKind.ERRORTOKEN.num → p.tok.done = E_EOF → p.tok.level = 0 →
      SetsErr r "SyntaxError" "unexpected EOF while parsing" none) ∧
    (last.type = TokKind.INDENT.num → SetsErr r "IndentationError" "unexpected indent" none) ∧
    (last.type = TokKind.DEDENT.num → SetsErr r "IndentationError" "unexpected unindent" none) ∧
    (¬(last.type = TokKind.ERRORTOKEN.num ∧ p.tok.done = E_EOF) → last.type ≠ TokKind.INDENT.num →
      last.type ≠ TokKind.DEDENT.num →
      let q := (raiseErrorKnownLocation "SyntaxError" last.lineno last.colOffset last.endLineno
        last.endColOffset "invalid syntax" p).2
      SetsErr q "SyntaxError" "invalid syntax" (some last.lineno) ∧
      setSyntaxError last p = tokenizeFullSource q))

theorem setSyntaxErrorArms_proven : SetSyntaxErrorArms := by
  intro last p
  have base : ∀ h : p.errOccurred = true, setSyntaxError last p =
      if (p.tok.done == 16 || p.tok.done == E_OK) &&
        ((p.tok.err.map (·.cls)).map isSyntaxErrorClass).getD false then tokenizeFullSource p
      else ((), p) := by
    intro h
    simp only [setSyntaxError, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, h,
      ↓reduceIte, pure, StateT.pure]
    split <;> rfl
  refine ⟨fun h hd he => ?_, fun h hn => ?_, fun h hf => ?_⟩
  · rw [base h]
    obtain ⟨e, he, hc⟩ := he
    have : ((p.tok.done == 16 || p.tok.done == E_OK) &&
        ((p.tok.err.map (·.cls)).map isSyntaxErrorClass).getD false) = true := by
      rcases hd with hd | hd <;> simp [hd, he, hc]
    rw [if_pos this]
  · rw [base h]
    have : ¬ ((p.tok.done == 16 || p.tok.done == E_OK) &&
        ((p.tok.err.map (·.cls)).map isSyntaxErrorClass).getD false) = true := by
      intro hc
      apply hn
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
      obtain ⟨hd, hs⟩ := hc
      refine ⟨hd, ?_⟩
      cases he : p.tok.err with
      | none => rw [he] at hs; simp at hs
      | some e => rw [he] at hs; exact ⟨e, rfl, by simpa using hs⟩
    rw [if_neg this]
  · simp only []
    have hg : Fresh p := by simp [Fresh, h]
    refine ⟨fun ht hd c line col rest hl hs => ?_, fun ht hd hl => ?_, fun ht => ?_, fun ht => ?_,
      fun h1 h2 h3 => ?_⟩
    · rw [setSyntaxError_eq last p h hf]
      have e1 : (last.type == TokKind.ERRORTOKEN.num && p.tok.done == E_EOF) = true := by
        simp [ht, hd]
      have e2 : (p.tok.level != 0) = true := by simpa using hl
      simp only [setSyntaxErrorTail, e1, e2, ↓reduceIte]
      obtain ⟨x, a, b, c', d⟩ := raiseUnclosed_proven p c line col rest hg hs
      exact ⟨x, a, b, c', fun _ => d⟩
    · rw [setSyntaxError_eq last p h hf]
      have e1 : (last.type == TokKind.ERRORTOKEN.num && p.tok.done == E_EOF) = true := by
        simp [ht, hd]
      have e2 : (p.tok.level != 0) = false := by simpa using hl
      simp only [setSyntaxErrorTail, e1, e2, Bool.false_eq_true, ↓reduceIte]
      exact error0_sets p hg _ _
    · obtain ⟨x, a, b, c'⟩ := (setSyntaxError_proven last p).2.1 h hf ht
      exact ⟨x, a, b, c', fun h => by simp at h⟩
    · obtain ⟨x, a, b, c'⟩ := (setSyntaxError_proven last p).2.2 h hf ht
      exact ⟨x, a, b, c', fun h => by simp at h⟩
    · have e1 : (last.type == TokKind.ERRORTOKEN.num && p.tok.done == E_EOF) = false := by
        simpa using h1
      have e3 : (last.type == TokKind.INDENT.num || last.type == TokKind.DEDENT.num) = false := by
        simpa using And.intro h2 h3
      refine ⟨?_, ?_⟩
      · obtain ⟨x, a, b, c', d, _⟩ := raiseKnownLocation_err p "SyntaxError" "invalid syntax"
          last.lineno (if last.colOffset == -5 then -5 else last.colOffset + 1) last.endLineno
          (if last.endColOffset == -5 then -5 else last.endColOffset + 1) hg
        exact ⟨x, a, b, c', fun _ => d⟩
      · rw [setSyntaxError_eq last p h hf]
        simp only [setSyntaxErrorTail, e1, e3, Bool.false_eq_true, ↓reduceIte, bind, StateT.bind]
        rfl

/-- `_PyPegen_is_memoized`, `Parser/pegen.c:341-373`, at the frontier and on a miss. At
`p->mark == p->fill` it first fills a token (`:344-349`): if that fails it sets `error_indicator`
and returns -1 (here `some NULL`); if it succeeds the new token's memo is empty, so it is a miss
(0, `none`) on the filled state. With the token read and no entry of the type, it is a miss and the
parser is untouched. `memo.size = fill` is the invariant `FillToken` keeps. Hits are
`pygrammar-peg-memo-cache`. -/
def MemoFrontier : Prop := ∀ (p : PS) (ty : Nat),
  (p.mark = p.fill → (fillToken p).1 < 0 →
    isMemoized ty p = (some .null, { (fillToken p).2 with errorIndicator := true })) ∧
  (p.mark = p.fill → ¬ (fillToken p).1 < 0 → p.memo.size = p.fill →
    isMemoized ty p = (none, (fillToken p).2)) ∧
  (p.mark < p.fill → (p.memo.getD p.mark []).all (fun m => m.1 != ty) = true →
    isMemoized ty p = (none, p))

theorem find_none_of_all (l : List (Nat × Ast × Nat)) (ty : Nat)
    (h : l.all (fun m => m.1 != ty) = true) : l.find? (fun m => m.1 == ty) = none := by
  rw [List.find?_eq_none]
  intro x hx
  have := List.all_eq_true.1 h x hx
  simpa using this

theorem memoFrontier_proven : MemoFrontier := by
  intro p ty
  have e : isMemoized ty p = (if (ensureToken p).1 then memoLookup ty (ensureToken p).2
      else (some .null, (ensureToken p).2)) := rfl
  refine ⟨fun hm hf => ?_, fun hm hf hs => ?_, fun hm ha => ?_⟩
  · have he : ensureToken p = (false, { (fillToken p).2 with errorIndicator := true }) := by
      simp [ensureToken, hm, hf]
    rw [e, he]
    rfl
  · have he : ensureToken p = (true, (fillToken p).2) := by
      simp [ensureToken, hm, hf]
    rw [e, he]
    obtain ⟨h1, _, _, h4⟩ := fillToken_proven p
    have hslot : ((fillToken p).2.memo.getD (fillToken p).2.mark []) = [] := by
      rw [h4, h1, hm, ← hs]
      simp [Array.getD_eq_getD_getElem?]
    show (match ((fillToken p).2.memo.getD (fillToken p).2.mark []).find? (fun m => m.1 == ty) with
      | some (_, node, mark) => (some node, { (fillToken p).2 with mark := mark })
      | none => (none, (fillToken p).2)) = _
    rw [hslot]
    rfl
  · have hn : (p.mark == p.fill) = false := by simp; omega
    have he : ensureToken p = (true, p) := by simp [ensureToken, hn]
    rw [e, he]
    show (match (p.memo.getD p.mark []).find? (fun m => m.1 == ty) with
      | some (_, node, mark) => (some node, { p with mark := mark })
      | none => (none, p)) = _
    rw [find_none_of_all _ _ ha]

/-- The column `_PyPegen_raise_error` gives `_PyPegen_raise_error_known_location` for token `t`,
`Parser/pegen_errors.c:219-228`: one-based, or for a token with no column the tokenizer's position
in the line (0 at the start of the buffer). -/
def raiseCol (p : PS) (t : Token) : Int :=
  if t.colOffset = -1 then (if p.tok.cur = p.tok.buf then 0 else (p.tok.cur : Int) - p.tok.lineStart)
  else t.colOffset + 1

/-- The end column, `:229-231`: one-based, or -1. -/
def raiseEndCol (t : Token) : Int := if t.endColOffset ≠ -1 then t.endColOffset + 1 else -1

/-- `_PyPegen_raise_error`, `Parser/pegen_errors.c:197-241`. It bails out on an earlier error
(`:201-203`); with no token read it raises at line 0 (`:204-210`); otherwise it raises at
`known_err_token` if set, else at `tokens[mark]` with `use_mark` and `tokens[fill - 1]` without
(`:216-218`), with `raiseCol` and `raiseEndCol`, on that token's line. With `use_mark` at the
frontier it first fills a token, and if that fails sets `error_indicator` and raises nothing more
(`:211-215`). -/
def RaiseErrorExact : Prop := ∀ (p : PS) (cls msg : String) (m : Bool),
  (p.errorIndicator = true → p.errOccurred = true → raiseError cls m msg p = ((), p)) ∧
  (Fresh p → p.fill = 0 → raiseError cls m msg p = raiseKnownLocation cls 0 0 0 (-1) msg p) ∧
  (Fresh p → p.fill ≠ 0 → ¬(m = true ∧ p.mark = p.fill) →
    let t := p.knownErrToken.getD (p.tokenAt (if m then p.mark else p.fill - 1))
    raiseError cls m msg p =
      raiseKnownLocation cls t.lineno (raiseCol p t) t.endLineno (raiseEndCol t) msg p ∧
    SetsErr (raiseError cls m msg p).2 cls msg (some t.lineno)) ∧
  (Fresh p → p.fill ≠ 0 → m = true → p.mark = p.fill → (fillToken p).1 < 0 →
    raiseError cls m msg p = ((), { (fillToken p).2 with errorIndicator := true })) ∧
  (Fresh p → p.fill ≠ 0 → m = true → p.mark = p.fill → ¬ (fillToken p).1 < 0 →
    let q := (fillToken p).2
    let t := q.knownErrToken.getD (q.tokenAt q.mark)
    raiseError cls m msg p = raiseKnownLocation cls t.lineno (raiseCol q t) t.endLineno
      (raiseEndCol t) msg q)

theorem raiseAtToken_eq (cls : String) (t : Token) (msg : String) (p : PS) :
    raiseAtToken cls t msg p =
      raiseKnownLocation cls t.lineno (raiseCol p t) t.endLineno (raiseEndCol t) msg p := by
  have e : raiseAtToken cls t msg p = raiseKnownLocation cls t.lineno
      (if t.colOffset == -1 then (if p.tok.cur == p.tok.buf then 0 else (p.tok.cur : Int) - p.tok.lineStart)
       else t.colOffset + 1) t.endLineno (if t.endColOffset != -1 then t.endColOffset + 1 else -1)
      msg p := rfl
  rw [e]
  unfold raiseCol raiseEndCol
  congr 1
  · simp only [beq_iff_eq]
  · simp

theorem raiseErrorExact_proven : RaiseErrorExact := by
  intro p cls msg m
  refine ⟨fun h1 h2 => ?_, fun hg hf => ?_, fun hg hf hn => ?_, fun hg hf hm hmf hfl => ?_,
    fun hg hf hm hmf hfl => ?_⟩
  · simp [raiseError, h1, h2, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure]
  · have g := fresh_guard hg
    have hf' : (p.fill == 0) = true := by simpa using hf
    simp only [raiseError, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, g, hf',
      Bool.false_eq_true, ↓reduceIte, pure, StateT.pure]
    cases raiseKnownLocation cls 0 0 0 (-1) msg p
    rfl
  · have g := fresh_guard hg
    have hf' : (p.fill == 0) = false := by simpa using hf
    have hn' : (m && p.mark == p.fill) = false := by
      cases m <;> simp_all
    have e : raiseError cls m msg p = raiseAtToken cls
        (p.knownErrToken.getD (p.tokenAt (if m then p.mark else p.fill - 1))) msg p := by
      simp only [raiseError, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, g, hf',
        hn', Bool.false_eq_true, ↓reduceIte, pure, StateT.pure]
    simp only []
    rw [e, raiseAtToken_eq]
    refine ⟨rfl, ?_⟩
    obtain ⟨x, a, b, c, d, _⟩ := raiseKnownLocation_err p cls msg _ _ _ _ hg
    exact ⟨x, a, b, c, fun _ => d⟩
  · have g := fresh_guard hg
    have hf' : (p.fill == 0) = false := by simpa using hf
    have hm' : (m && p.mark == p.fill) = true := by simp [hm, hmf]
    simp only [raiseError, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, g, hf',
      hm', Bool.false_eq_true, ↓reduceIte, pure, StateT.pure]
    rcases hq : fillToken p with ⟨a, s⟩
    rw [hq] at hfl
    simp only [] at hfl
    simp only [hfl, ↓reduceIte]
    rfl
  · have g := fresh_guard hg
    have hf' : (p.fill == 0) = false := by simpa using hf
    have hm' : (m && p.mark == p.fill) = true := by simp [hm, hmf]
    subst hm
    simp only [raiseError, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, g, hf',
      hm', Bool.false_eq_true, ↓reduceIte, pure, StateT.pure]
    rcases hq : fillToken p with ⟨a, s⟩
    rw [hq] at hfl
    simp only [] at hfl
    simp only [hfl, Bool.false_eq_true, ↓reduceIte, ↓reduceIte]
    exact raiseAtToken_eq cls _ msg s

end PyLean.PyGrammar.Peg
