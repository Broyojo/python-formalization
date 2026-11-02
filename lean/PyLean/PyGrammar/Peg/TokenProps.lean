import PyLean.PyGrammar.Peg.ErrorProps

/-!
The token and memo machinery of `Parser/pegen.c` that every generated rule goes through: reading a
token, including the path where the tokenizer fails, taking a token, and the memo as a cache.

The type invariant used is `memo.size = fill`: `_PyPegen_fill_token` is the only place either
grows, and it grows both (`FillToken`).
-/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### `_Pypegen_raise_decode_error` -/

/-- `_Pypegen_raise_decode_error`: returns `-1` and leaves the parser where it was. A decoding
error becomes a `SyntaxError` naming its kind, and any other exception is left alone. -/
def RaiseDecodeError : Prop := ∀ (p : PS) (e : PyError), p.tok.err = some e →
  (raiseDecodeError p).1 = -1 ∧
  (∀ t, decodeErrType e.cls = some t →
    ∃ x : PyError, (raiseDecodeError p).2.tok.err = some x ∧ x.cls = "SyntaxError" ∧
      x.msg = s!"({t}) {e.msg}") ∧
  (decodeErrType e.cls = none → (raiseDecodeError p).2 = p)

theorem raiseDecode_eq (p : PS) : raiseDecodeError p = (-1, (raiseDecodeBody none p.tok.err p).2) := rfl

theorem raiseDecode_some (p : PS) (e : PyError) (h : p.tok.err = some e) (t : String)
    (ht : decodeErrType e.cls = some t) :
    raiseDecodeError p = (-1, (raiseError0 "SyntaxError" s!"({t}) {e.msg}"
      { p with tok := { p.tok with err := none } }).2) := by
  rw [raiseDecode_eq, h]
  simp only [raiseDecodeBody, ht]
  rfl

theorem raiseDecode_none (p : PS) (e : PyError) (h : p.tok.err = some e)
    (ht : decodeErrType e.cls = none) : raiseDecodeError p = (-1, p) := by
  rw [raiseDecode_eq, h]
  simp only [raiseDecodeBody, ht]
  rfl

theorem raiseDecodeError_proven : RaiseDecodeError := by
  intro p e h
  cases ht : decodeErrType e.cls with
  | none =>
    rw [raiseDecode_none p e h ht]
    exact ⟨rfl, fun t ht' => by simp at ht', fun _ => rfl⟩
  | some t =>
    rw [raiseDecode_some p e h t ht]
    refine ⟨rfl, fun t' ht' => ?_, fun ht' => by simp at ht'⟩
    cases ht'
    have fresh : Fresh { p with tok := { p.tok with err := none } } := by
      simp [Fresh, PS.errOccurred]
    obtain ⟨x, h1, h2, h3, _⟩ := raiseErrorContract_proven _ "SyntaxError"
      s!"({t}) {e.msg}" default fresh
    exact ⟨x, h1, h2, h3⟩

theorem keeps_raiseDecodeError : Keeps raiseDecodeError := by
  intro p
  cases h : p.tok.err with
  | none =>
    rw [raiseDecode_eq, h]
    exact ⟨rfl, rfl, rfl⟩
  | some e =>
    cases ht : decodeErrType e.cls with
    | none =>
      rw [raiseDecode_none p e h ht]
      exact ⟨rfl, rfl, rfl⟩
    | some t =>
      rw [raiseDecode_some p e h t ht]
      exact (raises_raiseError0 _ _).1 _

/-! ### `_PyPegen_fill_token` -/

theorem pushToken_fields (p : PS) :
    (pushToken p).1.mark = p.mark ∧ (pushToken p).1.tokens.size = p.tokens.size + 1 ∧
    (∀ i, i < p.tokens.size → (pushToken p).1.tokenAt i = p.tokenAt i) ∧
    (pushToken p).1.memo = p.memo.push [] := by
  unfold pushToken
  dsimp only
  generalize getTokSkippingIgnores (p.tok.src.size + 2) p.tok p.typeIgnores = r
  obtain ⟨s, ty, t, ig⟩ := r
  dsimp only
  repeat' split
  all_goals
    refine ⟨rfl, by simp, fun i hi => ?_, rfl⟩
    simp only [PS.tokenAt, Array.getD_eq_getD_getElem?]
    simp [Array.getElem?_push, hi, Nat.ne_of_lt hi]

theorem fillToken_step (p : PS) :
    fillToken p =
      let q := (pushToken p).1
      if (pushToken p).2 == TokKind.ERRORTOKEN.num then
        (if q.tok.done == E_DECODE then raiseDecodeError else tokenizerError) q
      else (0, q) := by
  have e : fillToken p = (if (pushToken p).2 == TokKind.ERRORTOKEN.num then
      (if (pushToken p).1.tok.done == E_DECODE then raiseDecodeError else tokenizerError)
      else pure 0) (pushToken p).1 := rfl
  rw [e]
  dsimp only
  split <;> rfl

theorem fillToken_keeps (p : PS) :
    (fillToken p).2.mark = (pushToken p).1.mark ∧ (fillToken p).2.tokens = (pushToken p).1.tokens ∧
    (fillToken p).2.memo = (pushToken p).1.memo := by
  rw [fillToken_step]
  dsimp only
  split
  · split
    · exact keeps_raiseDecodeError _
    · exact (tokenizerErrorSets_proven _).2.2
  · exact ⟨rfl, rfl, rfl⟩

/-- `_PyPegen_fill_token`, on success and on both failure paths (a decoding error and
`_Pypegen_tokenizer_error`): it appends exactly one token and one empty memo slot, leaves the
earlier tokens and `p->mark` alone. So `memo.size = fill` holds, and marks stay valid. -/
def FillToken : Prop := ∀ p : PS,
  (fillToken p).2.mark = p.mark ∧
  (fillToken p).2.fill = p.fill + 1 ∧
  (∀ i, i < p.fill → (fillToken p).2.tokenAt i = p.tokenAt i) ∧
  (fillToken p).2.memo = p.memo.push []

theorem fillToken_proven : FillToken := by
  intro p
  obtain ⟨h1, h2, h3⟩ := fillToken_keeps p
  obtain ⟨a, b, c, d⟩ := pushToken_fields p
  refine ⟨h1.trans a, ?_, fun i hi => ?_, h3.trans d⟩
  · show (fillToken p).2.tokens.size = p.tokens.size + 1
    rw [h2, b]
  · have : (fillToken p).2.tokenAt i = (pushToken p).1.tokenAt i := by
      simp only [PS.tokenAt, h2]
    rw [this]
    exact c i hi

/-! ### `_PyPegen_expect_token` -/

/-- The fill at the head of every token-reading function. -/
theorem ensureToken_eq (p : PS) :
    ensureToken p =
      if p.mark == p.fill then
        if (fillToken p).1 < 0 then (false, { (fillToken p).2 with errorIndicator := true })
        else (true, (fillToken p).2)
      else (true, p) := rfl

theorem expectToken_eq (ty : Nat) (p : PS) :
    expectToken ty p =
      if (ensureToken p).1 then takeToken ty (ensureToken p).2 else (.null, (ensureToken p).2) := by
  have e : expectToken ty p = (if !(ensureToken p).1 then pure .null else takeToken ty)
      (ensureToken p).2 := rfl
  rw [e]
  cases (ensureToken p).1 <;> rfl

/-- `_PyPegen_expect_token`: at a token already read, take it if its type matches, and otherwise
change nothing. At the end of the tokens read so far, read one first: if that fails, the rule
gets `NULL` with `error_indicator` set and `p->mark` where it was. -/
def ExpectToken : Prop := ∀ (p : PS) (ty : Nat),
  (p.mark ≠ p.fill →
    expectToken ty p =
      if (p.tokenAt p.mark).type != ty then (.null, p)
      else (.tok (p.tokenAt p.mark), { p with mark := p.mark + 1 })) ∧
  (p.mark = p.fill → (fillToken p).1 < 0 →
    expectToken ty p = (.null, { (fillToken p).2 with errorIndicator := true }) ∧
      (fillToken p).2.mark = p.mark) ∧
  (p.mark = p.fill → ¬(fillToken p).1 < 0 →
    expectToken ty p =
      if ((fillToken p).2.tokenAt p.mark).type != ty then (.null, (fillToken p).2)
      else (.tok ((fillToken p).2.tokenAt p.mark),
        { (fillToken p).2 with mark := p.mark + 1 }))

theorem expectToken_proven : ExpectToken := by
  intro p ty
  refine ⟨fun h => ?_, fun h hf => ?_, fun h hf => ?_⟩
  · have h' : (p.mark == p.fill) = false := by simpa using h
    rw [expectToken_eq, ensureToken_eq]
    simp only [h', Bool.false_eq_true, ↓reduceIte]
    rfl
  · have h' : (p.mark == p.fill) = true := by simpa using h
    rw [expectToken_eq, ensureToken_eq]
    simp only [h', hf, ↓reduceIte, Bool.false_eq_true]
    exact ⟨trivial, (fillToken_proven p).1⟩
  · have h' : (p.mark == p.fill) = true := by simpa using h
    rw [expectToken_eq, ensureToken_eq]
    simp only [h', hf, ↓reduceIte]
    have hm : (fillToken p).2.mark = p.mark := (fillToken_proven p).1
    simp only [takeToken, hm]

/-! ### The memo -/

theorem modify_getD_self (a : Array (List (Nat × Ast × Nat))) (i : Nat) (h : i < a.size)
    (f : List (Nat × Ast × Nat) → List (Nat × Ast × Nat)) :
    (a.modify i f).getD i [] = f (a.getD i []) := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem_modify, h]

theorem find_replaced (l : List (Nat × Ast × Nat)) (ty : Nat) (x : Nat × Ast × Nat) (hx : x.1 = ty)
    (h : l.any (fun m => m.1 == ty) = true) :
    (l.map fun m => if m.1 == ty then x else m).find? (fun m => m.1 == ty) = some x := by
  induction l with
  | nil => simp at h
  | cons m ms ih =>
    by_cases hm : (m.1 == ty) = true
    · have hx' : (x.1 == ty) = true := by simp [hx]
      simp only [List.map_cons, hm, ↓reduceIte, List.find?_cons, hx']
    · have hf : (m.1 == ty) = false := by simpa using hm
      have : ms.any (fun m => m.1 == ty) = true := by
        simp only [List.any_cons, hf, Bool.false_or] at h
        exact h
      simp only [List.map_cons, hf, Bool.false_eq_true, ↓reduceIte, List.find?_cons]
      exact ih this

/-- The memo is a cache. What `_PyPegen_insert_memo` or `_PyPegen_update_memo` stores for rule
`ty` at token `m` is what `_PyPegen_is_memoized` finds when the parser is back at `m`, and the
parser resumes at the mark the rule ended on, even if `ty` was stored there before. Hypotheses:
token `m` is read, and `memo.size = fill`, the invariant of `FillToken`. -/
def MemoReturnsStored : Prop := ∀ (p : PS) (m ty : Nat) (node : Ast), m < p.fill →
  p.memo.size = p.fill →
    (let q := (insertMemo m ty node p).2
     isMemoized ty { q with mark := m } = (some node, { q with mark := p.mark })) ∧
    (let q := (updateMemo m ty node p).2
     isMemoized ty { q with mark := m } = (some node, { q with mark := p.mark }))

theorem isMemoized_hit (q : PS) (m ty : Nat) (node : Ast) (e : Nat) (h : m < q.fill)
    (hf : (q.memo.getD m []).find? (fun x => x.1 == ty) = some (ty, node, e)) :
    isMemoized ty { q with mark := m } = (some node, { q with mark := e }) := by
  have h' : ensureToken { q with mark := m } = (true, { q with mark := m }) := by
    have hn : (m == q.fill) = false := by simpa using Nat.ne_of_lt h
    rw [ensureToken_eq]
    simp only [PS.fill] at hn ⊢
    simp only [hn, Bool.false_eq_true, ↓reduceIte]
  have e1 : isMemoized ty { q with mark := m } =
      (if (ensureToken { q with mark := m }).1 then memoLookup ty (ensureToken { q with mark := m }).2
       else (some .null, (ensureToken { q with mark := m }).2)) := rfl
  rw [e1, h']
  show (match (q.memo.getD m []).find? (fun x => x.1 == ty) with
    | some (_, node, mark) => (some node, { q with mark := mark })
    | none => (none, { q with mark := m })) = _
  rw [hf]

theorem memoReturnsStored_proven : MemoReturnsStored := by
  intro p m ty node hm hs
  have hm' : m < p.memo.size := by omega
  constructor
  · intro q
    refine isMemoized_hit q m ty node p.mark hm ?_
    show ((p.memo.modify m _).getD m []).find? _ = _
    rw [modify_getD_self _ _ hm']
    simp
  · intro q
    refine isMemoized_hit q m ty node p.mark hm ?_
    show ((p.memo.modify m _).getD m []).find? _ = _
    rw [modify_getD_self _ _ hm']
    by_cases ha : (p.memo.getD m []).any (fun x => x.1 == ty) = true
    · simp only [ha, ↓reduceIte]
      exact find_replaced _ ty (ty, node, p.mark) rfl ha
    · have hf : ((p.memo.getD m []).any fun x => x.1 == ty) = false := Bool.eq_false_iff.mpr ha
      simp only [hf, Bool.false_eq_true, ↓reduceIte, List.find?_cons]
      simp

/-! ### `_PyPegen_get_last_nonnwhitespace_token` -/

/-- `NEWLINE`, `INDENT`, `DEDENT` and `ENDMARKER`: what `_PyPegen_get_last_nonnwhitespace_token`
walks past. -/
def isWhitespaceToken (t : Token) : Bool :=
  !(t.type != TokKind.ENDMARKER.num
    && (t.type < TokKind.NEWLINE.num || t.type > TokKind.DEDENT.num))

/-- `_PyPegen_get_last_nonnwhitespace_token`: with at least one token behind the mark, the result
is a token behind it, every token after it is whitespace, and it is whitespace itself only if it
is the very first token. This is where each node's `end_lineno` and `end_col_offset` come from. -/
def LastNonWhitespace : Prop := ∀ (p : PS), 0 < p.mark →
  ∃ i, i < p.mark ∧ lastNonWhitespaceToken p = p.tokenAt i ∧
    (isWhitespaceToken (p.tokenAt i) = true → i = 0) ∧
    ∀ j, i < j → j < p.mark → isWhitespaceToken (p.tokenAt j) = true

theorem go_spec (p : PS) (m : Nat) (t : Token) :
    ∃ i, i ≤ m ∧ lastNonWhitespaceToken.go p (m + 1) t = p.tokenAt i ∧
      (isWhitespaceToken (p.tokenAt i) = true → i = 0) ∧
      ∀ j, i < j → j ≤ m → isWhitespaceToken (p.tokenAt j) = true := by
  induction m generalizing t with
  | zero =>
    refine ⟨0, Nat.le_refl _, ?_, fun _ => rfl, fun j h1 h2 => by omega⟩
    simp only [lastNonWhitespaceToken.go]
    split <;> rfl
  | succ m ih =>
    by_cases hw : isWhitespaceToken (p.tokenAt (m + 1)) = true
    · have hg : lastNonWhitespaceToken.go p (m + 1 + 1) t =
          lastNonWhitespaceToken.go p (m + 1) (p.tokenAt (m + 1)) := by
        have hn : ((p.tokenAt (m + 1)).type != TokKind.ENDMARKER.num
            && ((p.tokenAt (m + 1)).type < TokKind.NEWLINE.num
              || (p.tokenAt (m + 1)).type > TokKind.DEDENT.num)) = false := by
          cases hX : ((p.tokenAt (m + 1)).type != TokKind.ENDMARKER.num
              && ((p.tokenAt (m + 1)).type < TokKind.NEWLINE.num
                || (p.tokenAt (m + 1)).type > TokKind.DEDENT.num)) with
          | false => rfl
          | true =>
            simp only [isWhitespaceToken, hX, Bool.not_true] at hw
            exact absurd hw (by decide)
        simp only [lastNonWhitespaceToken.go, hn, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨i, h1, h2, h3, h4⟩ := ih (p.tokenAt (m + 1))
      refine ⟨i, by omega, hg.trans h2, h3, fun j hj hj2 => ?_⟩
      by_cases e : j = m + 1
      · rw [e]; exact hw
      · exact h4 j hj (by omega)
    · have hn : ((p.tokenAt (m + 1)).type != TokKind.ENDMARKER.num
          && ((p.tokenAt (m + 1)).type < TokKind.NEWLINE.num
            || (p.tokenAt (m + 1)).type > TokKind.DEDENT.num)) = true := by
        cases hX : ((p.tokenAt (m + 1)).type != TokKind.ENDMARKER.num
            && ((p.tokenAt (m + 1)).type < TokKind.NEWLINE.num
              || (p.tokenAt (m + 1)).type > TokKind.DEDENT.num)) with
        | true => rfl
        | false => exact absurd (by simp only [isWhitespaceToken, hX, Bool.not_false]) hw
      refine ⟨m + 1, Nat.le_refl _, ?_, fun h => absurd h hw, fun j h1 h2 => by omega⟩
      simp only [lastNonWhitespaceToken.go, hn, ↓reduceIte]

theorem lastNonWhitespace_proven : LastNonWhitespace := by
  intro p h
  obtain ⟨m, hm⟩ : ∃ m, p.mark = m + 1 := ⟨p.mark - 1, by omega⟩
  obtain ⟨i, h1, h2, h3, h4⟩ := go_spec p m default
  refine ⟨i, by omega, ?_, h3, fun j h5 h6 => h4 j h5 (by omega)⟩
  unfold lastNonWhitespaceToken
  rw [hm]
  exact h2

end PyLean.PyGrammar.Peg
