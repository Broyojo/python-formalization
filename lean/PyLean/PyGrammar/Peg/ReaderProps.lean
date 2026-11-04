import PyLean.PyGrammar.Peg.TokenProps

/-!
What the token readers of `Parser/pegen.c` return, token by token: `_PyPegen_expect_forced_token`,
`_PyPegen_expect_soft_keyword`, `_PyPegen_name_token` and `_PyPegen_soft_keyword_token`. Each is
stated twice: with the token at the mark already read, where the result and the new mark are given
exactly, and at the frontier, where the reader first calls `_PyPegen_fill_token` and fails with
`error_indicator` set if that fails, or else behaves as on the state with the token read.
-/

namespace PyLean.PyGrammar.Peg

open Lexer

theorem ensure_ready (p : PS) (h : p.mark < p.fill) : ensureToken p = (true, p) := by
  have : (p.mark == p.fill) = false := by simp; omega
  simp [ensureToken, this]

theorem ensure_fail (p : PS) (h : p.mark = p.fill) (hf : (fillToken p).1 < 0) :
    ensureToken p = (false, { (fillToken p).2 with errorIndicator := true }) := by
  simp [ensureToken, h, hf]

theorem ensure_ok (p : PS) (h : p.mark = p.fill) (hf : ¬ (fillToken p).1 < 0) :
    ensureToken p = (true, (fillToken p).2) := by
  simp [ensureToken, h, hf]

theorem expect_ready (ty : Nat) (p : PS) (h : p.mark < p.fill) :
    expectToken ty p = takeToken ty p := by
  simp only [expectToken, bind, StateT.bind, ensure_ready p h, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]

theorem expect_ensure (ty : Nat) (p : PS) :
    expectToken ty p = (if (ensureToken p).1 then takeToken ty (ensureToken p).2
      else (.null, (ensureToken p).2)) := by
  simp only [expectToken, bind, StateT.bind]
  cases ensureToken p with
  | mk b q => cases b <;> rfl

/-- `_PyPegen_name_from_token`, `Parser/pegen.c:565-582`: a `Name` with the identifier
`_PyPegen_new_identifier` makes of the token's bytes, `Load`, at the token's location; `NULL` with
`error_indicator` set if the identifier is refused. -/
def NameFromToken : Prop := ∀ (t : Token) (q : PS),
  (∀ id, (newIdentifier t.bytes q).1 = .ident id →
    nameFromToken (.tok t) q = (.node .Name [.ident id, .node .Load [] none] (some (tokLoc t)),
      (newIdentifier t.bytes q).2)) ∧
  ((newIdentifier t.bytes q).1 = .null →
    nameFromToken (.tok t) q = (.null, { (newIdentifier t.bytes q).2 with errorIndicator := true }))

theorem nameFromToken_proven : NameFromToken := by
  intro t q
  refine ⟨fun id h => ?_, fun h => ?_⟩
  · simp only [nameFromToken]
    split
    · rename_i hn
      rw [h] at hn
      cases hn
    · rw [h]
  · simp only [nameFromToken, h]

/-- The token readers with the token at the mark already read (`p->mark < p->fill`, so no
`_PyPegen_fill_token`). `_PyPegen_expect_forced_token` (`Parser/pegen.c:435-454`) bails out on an
earlier error, takes a token of the type and moves the mark, and otherwise raises
`SyntaxError: expected '<x>'` at that token, the mark unmoved. `_PyPegen_expect_soft_keyword`
(`:457-478`) takes a `NAME` spelled `kw` as a `Name` and moves the mark, and returns `NULL` with
the parser untouched on any other token. `_PyPegen_name_token` (`:585-589`) takes a `NAME` as a
`Name`, and leaves the parser untouched on any other type. `_PyPegen_soft_keyword_token`
(`:597-612`) takes a `NAME` that is one of the grammar's soft keywords, and on any other `NAME`
returns `NULL` with the mark moved past it. -/
def TokenReadersExact : Prop := ∀ (p : PS), p.mark < p.fill →
  let t := p.tokenAt p.mark
  let next : PS := { p with mark := p.mark + 1 }
  (∀ (ty : Nat) (x : String),
    (p.errorIndicator = true → forcedToken ty x p = (.null, p)) ∧
    (p.errorIndicator = false → t.type = ty → forcedToken ty x p = (.tok t, next)) ∧
    (p.errorIndicator = false → t.type ≠ ty →
      (forcedToken ty x p).1 = .null ∧ (forcedToken ty x p).2.mark = p.mark ∧
      (forcedToken ty x p).2.tokens = p.tokens ∧ (forcedToken ty x p).2.errorIndicator = true ∧
      ∃ e : PyError, (forcedToken ty x p).2.tok.err = some e ∧ e.cls = "SyntaxError" ∧
        e.msg = s!"expected '{x}'" ∧ e.lineno = some t.lineno)) ∧
  (∀ kw : List Nat,
    (t.type = TokKind.NAME.num → t.bytes = kw → expectSoftKeyword kw p = nameFromToken (.tok t) next) ∧
    (¬(t.type = TokKind.NAME.num ∧ t.bytes = kw) → expectSoftKeyword kw p = (.null, p))) ∧
  (t.type = TokKind.NAME.num → nameToken p = nameFromToken (.tok t) next) ∧
  (t.type ≠ TokKind.NAME.num → nameToken p = (.null, p)) ∧
  (t.type = TokKind.NAME.num → softKeywords.contains t.bytes = true →
    softKeywordToken p = nameFromToken (.tok t) next) ∧
  (t.type = TokKind.NAME.num → softKeywords.contains t.bytes = false →
    softKeywordToken p = (.null, next)) ∧
  (t.type ≠ TokKind.NAME.num → softKeywordToken p = (.null, p))

theorem take_eq (ty : Nat) (p : PS) (h : (p.tokenAt p.mark).type = ty) :
    takeToken ty p = (.tok (p.tokenAt p.mark), { p with mark := p.mark + 1 }) := by
  simp [takeToken, h]

theorem take_ne (ty : Nat) (p : PS) (h : (p.tokenAt p.mark).type ≠ ty) :
    takeToken ty p = (.null, p) := by
  simp [takeToken, h]

theorem nameToken_ready (p : PS) (h : p.mark < p.fill) :
    nameToken p = (match takeToken TokKind.NAME.num p with
      | (a, q) => nameFromToken a q) := by
  simp only [nameToken, bind, StateT.bind, expect_ready _ p h]
  cases takeToken TokKind.NAME.num p
  rfl

theorem tokenReadersExact_proven : TokenReadersExact := by
  intro p hm
  simp only []
  have he := ensure_ready p hm
  refine ⟨fun ty x => ⟨fun h => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩, fun kw => ⟨fun h1 h2 => ?_,
    fun h => ?_⟩, fun h => ?_, fun h => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h => ?_⟩
  · simp [forcedToken, h]
  · simp [forcedToken, h1, he, h2]
  · have hne : ((p.tokenAt p.mark).type != ty) = true := by simpa using h2
    have e1 : forcedToken ty x p = (.null, (raiseRange "SyntaxError" (.tok (p.tokenAt p.mark))
        (.tok (p.tokenAt p.mark)) s!"expected '{x}'" p).2) := by
      simp [forcedToken, h1, he, hne]
    rw [e1]
    have fresh : Fresh p := by simp [Fresh, h1]
    have hk := keeps_raiseKnownLocation "SyntaxError" s!"expected '{x}'"
      (locOf (.tok (p.tokenAt p.mark))).lineno
      (if (locOf (.tok (p.tokenAt p.mark))).colOffset == -5 then -5
        else (locOf (.tok (p.tokenAt p.mark))).colOffset + 1)
      (locOf (.tok (p.tokenAt p.mark))).endLineno
      (if (locOf (.tok (p.tokenAt p.mark))).endColOffset == -5 then -5
        else (locOf (.tok (p.tokenAt p.mark))).endColOffset + 1) p
    obtain ⟨e, q1, q2, q3, q4, _, q6⟩ := raiseKnownLocation_err p "SyntaxError" s!"expected '{x}'"
      (locOf (.tok (p.tokenAt p.mark))).lineno
      (if (locOf (.tok (p.tokenAt p.mark))).colOffset == -5 then -5
        else (locOf (.tok (p.tokenAt p.mark))).colOffset + 1)
      (locOf (.tok (p.tokenAt p.mark))).endLineno
      (if (locOf (.tok (p.tokenAt p.mark))).endColOffset == -5 then -5
        else (locOf (.tok (p.tokenAt p.mark))).endColOffset + 1) fresh
    exact ⟨rfl, hk.1, hk.2.1, q6, e, q1, q2, q3, by rw [q4]; rfl⟩
  · have e2 : nameToken p = nameFromToken (.tok (p.tokenAt p.mark)) { p with mark := p.mark + 1 } := by
      rw [nameToken_ready p hm, take_eq _ p h1]
    simp only [expectSoftKeyword, he, h1, h2, bne_self_eq_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, e2]
  · by_cases h1 : (p.tokenAt p.mark).type = TokKind.NAME.num
    · have h2 : (p.tokenAt p.mark).bytes ≠ kw := fun h2 => h ⟨h1, h2⟩
      simp [expectSoftKeyword, he, h1, h2]
    · simp [expectSoftKeyword, he, h1]
  · rw [nameToken_ready p hm, take_eq _ p h]
  · rw [nameToken_ready p hm, take_ne _ p h]
    rfl
  · simp only [softKeywordToken, expect_ready _ p hm, take_eq _ p h1, h2, ↓reduceIte]
  · simp only [softKeywordToken, expect_ready _ p hm, take_eq _ p h1, h2, Bool.false_eq_true,
      ↓reduceIte]
  · simp only [softKeywordToken, expect_ready _ p hm, take_ne _ p h]

/-- At the frontier (`p->mark == p->fill`) each reader first calls `_PyPegen_fill_token`
(`Parser/pegen.c:437-441`, `459-463`, `407-411` through `_PyPegen_expect_token`): if that fails, the
result is `NULL` with `error_indicator` set on the state the failed fill left; if it succeeds, the
reader behaves as on the state with the token read. -/
def TokenReadersFrontier : Prop := ∀ (p : PS), p.mark = p.fill →
  ((fillToken p).1 < 0 →
    let q : PS := { (fillToken p).2 with errorIndicator := true }
    (∀ ty x, p.errorIndicator = false → forcedToken ty x p = (.null, q)) ∧
    (∀ kw, expectSoftKeyword kw p = (.null, q)) ∧ nameToken p = (.null, q) ∧
    softKeywordToken p = (.null, q)) ∧
  (¬ (fillToken p).1 < 0 →
    let q := (fillToken p).2
    (∀ ty x, p.errorIndicator = false → q.errorIndicator = false →
      forcedToken ty x p = forcedToken ty x q) ∧
    (∀ kw, expectSoftKeyword kw p = (if (q.tokenAt q.mark).type != TokKind.NAME.num then (.null, q)
      else if (q.tokenAt q.mark).bytes != kw then (.null, q) else nameToken q)) ∧
    nameToken p = (match takeToken TokKind.NAME.num q with | (a, r) => nameFromToken a r) ∧
    softKeywordToken p = (match (takeToken TokKind.NAME.num q).1 with
      | .tok t => if softKeywords.contains t.bytes then nameFromToken (.tok t)
          (takeToken TokKind.NAME.num q).2 else (.null, (takeToken TokKind.NAME.num q).2)
      | _ => (.null, (takeToken TokKind.NAME.num q).2)))

theorem tokenReadersFrontier_proven : TokenReadersFrontier := by
  intro p hm
  constructor
  · intro hf
    have he := ensure_fail p hm hf
    refine ⟨fun ty x h => ?_, fun kw => ?_, ?_, ?_⟩
    · simp [forcedToken, h, he]
    · simp [expectSoftKeyword, he]
    · simp only [nameToken, bind, StateT.bind, expect_ensure, he, Bool.false_eq_true, ↓reduceIte]
      rfl
    · simp only [softKeywordToken, expect_ensure, he, Bool.false_eq_true, ↓reduceIte]
  · intro hf
    have he := ensure_ok p hm hf
    refine ⟨fun ty x h hq => ?_, fun kw => ?_, ?_, ?_⟩
    · have hr : (fillToken p).2.mark < (fillToken p).2.fill := by
        obtain ⟨a, b, _⟩ := fillToken_proven p
        omega
      simp [forcedToken, h, hq, he, ensure_ready _ hr]
    · simp [expectSoftKeyword, he]
    · simp only [nameToken, bind, StateT.bind, expect_ensure, he, ↓reduceIte]
      cases takeToken TokKind.NAME.num (fillToken p).2
      rfl
    · simp only [softKeywordToken, expect_ensure, he, ↓reduceIte]
      cases (takeToken TokKind.NAME.num (fillToken p).2).1 <;> rfl

end PyLean.PyGrammar.Peg
