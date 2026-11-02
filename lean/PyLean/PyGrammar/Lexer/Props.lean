import PyLean.PyGrammar.Lexer.Tokenize
import PyLean.PyGrammar.Peg.Interp

/-!
Properties of the tokenizer. The twins here are the parser's string tokenizer and the readline
tokenizer behind `Lib/tokenize.py`, which share `Parser/lexer/lexer.c` but feed it differently.
-/

namespace PyLean.PyGrammar.Lexer

open Peg

/-- A source that `compile` accepts tokenizes without an exception: the two front ends of
`Parser/lexer/lexer.c` agree on what is valid. -/
def tokenizesIfParses (text : List Nat) : Bool :=
  match parseStr {} (utf8Encode text) .file with
  | .error _ => true
  | .ok _ => (tokenizeText text true).2.isNone

/-- `tokenize` accepts every program the compiler accepts: the module documents itself as a
lexical scanner for Python source, and `generate_tokens` raises only on invalid input. -/
def TokenizeAcceptsValid : Prop := ∀ text : List Nat, tokenizesIfParses text = true

/-- `f"""{x=!r\n}aaa"""\n`, the input that raised `MemoryError` on 3.14.7, where the size of
the expression came from two buffers. On 3.15.2 the expression is a span of `tok->buf`. -/
def staleExprSize : List Nat :=
  [102, 34, 34, 34, 123, 120, 61, 33, 114, 10, 125, 97, 97, 97, 34, 34, 34, 10]

set_option maxRecDepth 100000 in
/-- That input now tokenizes. One input, so it credits no row. -/
theorem staleExprSize_tokenizes : tokenizesIfParses staleExprSize = true := by decide +kernel

/-- The debug text of `f'{expr=}'` ends with `=` and optional whitespace, as the docs of
f-strings describe: "the text of the expression, an equal sign" then the value. -/
def debugTextOk (src : List Nat) : Bool :=
  match parseStr {} src .file with
  | .ok (.node .Module (.seq [.node .Expr [.node .JoinedStr
      [.seq [.node .Constant (.const (.str text) :: _) _, .node .FormattedValue _ _]] _] _] :: _) _) =>
    ((text.reverse.dropWhile fun c => c == 10 || c == 32).head?) == some 61
  | _ => true

/-- Every debug text of an f-string keeps the `=`. -/
def DebugTextKeepsEquals : Prop := ∀ src : List Nat, debugTextOk src = true

/-- `f'''{"\"#x"=#c\n}'''`, whose `=` was lost on 3.14.7, where the comment-stripping loop of
`set_ftstring_expr` did not skip escapes and took the `#` inside the string for a comment. -/
def escapedHash : List Nat :=
  [102, 39, 39, 39, 123, 34, 92, 34, 35, 120, 34, 61, 35, 99, 10, 125, 39, 39, 39]

set_option maxRecDepth 100000 in
/-- That input now keeps it. One input, so it credits no row. -/
theorem escapedHash_keeps : debugTextOk escapedHash = true := by decide +kernel

theorem len_dropWhile (p : Nat → Bool) (l : List Nat) : (l.dropWhile p).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.dropWhile]
    split
    · simp only [List.length_cons]
      omega
    · simp

/-- One step of the first loop on anything but a backslash, whatever follows. -/
theorem scan_plain {ch : Nat} {rest : List Nat} {inStr : Bool} {q : Nat} (h : ch ≠ 92) :
    setFtstringExpr.scan (ch :: rest) inStr q =
      if ch = 34 ∨ ch = 39 then
        if inStr = false then setFtstringExpr.scan rest true ch
        else if ch = q then setFtstringExpr.scan rest false q
        else setFtstringExpr.scan rest inStr q
      else if ch = 35 ∧ inStr = false then true
      else setFtstringExpr.scan rest inStr q := by
  cases rest <;> simp [setFtstringExpr.scan, h]

theorem scan_comment_free {f : Nat} {bs : List Nat} {inStr : Bool} {q : Nat} :
    bs.length < f → setFtstringExpr.scan (setFtstringExpr.strip f bs inStr q) inStr q = false := by
  induction f generalizing bs inStr q with
  | zero => exact fun h => by omega
  | succ f ih =>
    intro h
    cases bs with
    | nil => simp [setFtstringExpr.strip, setFtstringExpr.scan]
    | cons ch rest =>
      have hr : rest.length < f := by simpa using h
      by_cases h1 : ch = 92
      · subst h1
        cases rest with
        | nil => simp [setFtstringExpr.strip, setFtstringExpr.scan]
        | cons e t =>
          have ht : t.length < f := by
            simp at hr
            omega
          simpa [setFtstringExpr.strip, setFtstringExpr.scan] using ih (inStr := inStr) (q := q) ht
      · by_cases h2 : ch = 34 ∨ ch = 39
        · cases inStr with
          | false =>
            simpa [setFtstringExpr.strip, scan_plain, h1, h2]
              using ih (inStr := true) (q := ch) hr
          | true =>
            by_cases h3 : ch = q
            · subst h3
              simpa [setFtstringExpr.strip, scan_plain, h1, h2]
                using ih (inStr := false) (q := ch) hr
            · simpa [setFtstringExpr.strip, scan_plain, h1, h2, h3]
                using ih (inStr := true) (q := q) hr
        · by_cases h4 : ch = 35
          · subst h4
            cases inStr with
            | false =>
              cases hd : rest.dropWhile (fun x => x != 10) with
              | nil => simp [setFtstringExpr.strip, setFtstringExpr.scan, hd]
              | cons x t =>
                have ht : t.length < f := by
                  have := len_dropWhile (fun x => x != 10) rest
                  rw [hd] at this
                  simp at this
                  omega
                simpa [setFtstringExpr.strip, scan_plain, hd]
                  using ih (inStr := false) (q := q) ht
            | true =>
              simpa [setFtstringExpr.strip, scan_plain]
                using ih (inStr := true) (q := q) hr
          · simpa [setFtstringExpr.strip, scan_plain, h1, h2, h4]
              using ih (inStr := inStr) (q := q) hr

theorem strip_no_comment {f : Nat} {bs : List Nat} {inStr : Bool} {q : Nat} :
    bs.length < f → setFtstringExpr.scan bs inStr q = false →
      setFtstringExpr.strip f bs inStr q = bs := by
  induction f generalizing bs inStr q with
  | zero => exact fun h => by omega
  | succ f ih =>
    intro h hs
    cases bs with
    | nil => simp [setFtstringExpr.strip]
    | cons ch rest =>
      have hr : rest.length < f := by simpa using h
      by_cases h1 : ch = 92
      · subst h1
        cases rest with
        | nil => simp [setFtstringExpr.strip]
        | cons e t =>
          have ht : t.length < f := by
            simp at hr
            omega
          simp [setFtstringExpr.scan] at hs
          simp [setFtstringExpr.strip, ih ht hs]
      · by_cases h2 : ch = 34 ∨ ch = 39
        · cases inStr with
          | false =>
            simp [scan_plain, h1, h2] at hs
            simp [setFtstringExpr.strip, h1, h2, ih hr hs]
          | true =>
            by_cases h3 : ch = q
            · subst h3
              simp [scan_plain, h1, h2] at hs
              simp [setFtstringExpr.strip, h1, h2, ih hr hs]
            · simp [scan_plain, h1, h2, h3] at hs
              simp [setFtstringExpr.strip, h1, h2, h3, ih hr hs]
        · by_cases h4 : ch = 35
          · subst h4
            cases inStr with
            | false => simp [scan_plain] at hs
            | true =>
              simp [scan_plain] at hs
              simp [setFtstringExpr.strip, ih hr hs]
          · simp [scan_plain, h1, h2, h4] at hs
            simp [setFtstringExpr.strip, h1, h2, h4, ih hr hs]

/-- `byte_col_to_char_col`, `Parser/tokenizer/helpers.c:15-24`: column 1 is column 1, and each
byte adds a column unless it continues a UTF-8 character. These two facts determine the function,
and they are what makes a tokenizer error's column count characters and not bytes. -/
def ByteColCounts : Prop := ∀ (s : TokState),
  byteColToCharCol s 1 = 1 ∧
  ∀ k : Nat, byteColToCharCol s ((k : Int) + 2) = byteColToCharCol s ((k : Int) + 1) +
    (if (s.at (s.lineStart + k)) &&& 0xC0 != 0x80 then 1 else 0)

theorem byteColCounts_proven : ByteColCounts := by
  intro s
  refine ⟨by simp [byteColToCharCol], fun k => ?_⟩
  unfold byteColToCharCol
  have e1 : ((k : Int) + 2 - 1).toNat = k + 1 := by omega
  have e2 : ((k : Int) + 1 - 1).toNat = k := by omega
  rw [e1, e2, List.range_succ, List.filter_append]
  simp only [List.filter_cons, List.filter_nil, List.length_append]
  split <;> simp <;> omega

/-- The two loops of `set_ftstring_expr`, `Parser/lexer/lexer.c:133-219`, agree. The first looks for
a comment, the second removes comments. What the second leaves has none the first would find, and
when the first finds none the second changes nothing. On 3.14.7 the second loop did not skip
escapes, so they disagreed. `f` is the loop's bound, the length of the expression and one over. -/
def CommentLoopsAgree : Prop := ∀ (f : Nat) (bs : List Nat), bs.length < f →
  setFtstringExpr.scan (setFtstringExpr.strip f bs false 0) false 0 = false ∧
  (setFtstringExpr.scan bs false 0 = false → setFtstringExpr.strip f bs false 0 = bs)

theorem commentLoopsAgree_proven : CommentLoopsAgree :=
  fun _ _ h => ⟨scan_comment_free h, strip_no_comment h⟩

/-- Every spelling in `Grammar/Tokens` is found by `_PyToken_OneChar`, `_PyToken_TwoChars`
and `_PyToken_ThreeChars` as the token it spells, as `Parser/token.c` is generated to do. -/
def ExactTokensResolve : Prop :=
  TokKind.all.all (fun k =>
    match k.exact? with
    | some e => exactLookup (e.toList.map Char.toNat) == k.num
    | none => true) = true

set_option maxRecDepth 100000 in
theorem exactTokensResolve_proven : ExactTokensResolve := by
  unfold ExactTokensResolve; decide +kernel

/-- `findEnd` of `underflow` answers past where it started. -/
theorem findEnd_gt (s : TokState) (n : Nat) (f i e : Nat)
    (h : underflow.findEnd s n f i = some e) : i < e := by
  induction f generalizing i with
  | zero => simp [underflow.findEnd] at h
  | succ f ih =>
    unfold underflow.findEnd at h
    split at h
    · simp at h
    · split at h
      · simp at h
        omega
      · have := ih (i + 1) h
        omega

/-- `buf <= cur <= inp` (the invariant in the comment on `struct tok_state`,
`Parser/lexer/state.h:79`) survives one `tok_nextc`: the tokenizer never reads past the end
of the data it holds. -/
def NextcStaysInBuffer : Prop :=
  ∀ s : TokState, s.cur ≤ s.inp → (nextcS s).2.cur ≤ (nextcS s).2.inp

theorem nextcFast_le (s : TokState) (h : s.cur < s.inp) :
    (nextcFast s).2.cur ≤ (nextcFast s).2.inp := by
  unfold nextcFast
  split
  · simpa using Nat.le_of_lt h
  · simp only
    omega

theorem syntaxErrorRange_inp (m : String) (a b : Int) (s : TokState) :
    (syntaxErrorRange m a b s).inp = s.inp := by
  unfold syntaxErrorRange
  split <;> rfl

@[simp] theorem setMode_cur (s : TokState) (f : Mode → Mode) : (s.setMode f).cur = s.cur := rfl
@[simp] theorem setMode_inp (s : TokState) (f : Mode → Mode) : (s.setMode f).inp = s.inp := rfl

theorem underflow_keeps_cur (s : TokState) (h : s.cur = s.inp)
    (hr : (underflow s).1 = true) :
    (underflow s).2.cur = s.cur ∧ s.cur < (underflow s).2.inp := by
  unfold underflow at hr ⊢
  dsimp only at hr ⊢
  cases hf : underflow.findEnd s s.src.size (s.src.size - s.inp + 1) s.inp with
  | none =>
    simp only [hf] at hr ⊢
    by_cases hge : s.inp ≥ s.src.size
    · simp only [hge, if_true] at hr
      split at hr <;> simp at hr
    · simp only [hge, if_false] at hr ⊢
      split <;> simp <;> omega
  | some e =>
    have he := findEnd_gt s _ _ _ _ hf
    simp only [hf] at hr ⊢
    split
    · repeat' split
      all_goals simp
      all_goals omega
    · split <;> simp <;> omega

theorem nextcStaysInBuffer_proven : NextcStaysInBuffer := by
  intro s h
  by_cases hc : s.cur = s.inp
  · by_cases hd : s.done = E_OK
    · have hu : nextcS s = (let (rc, s') := underflow s
        if !rc then (EOF, { s' with cur := s'.inp })
        else
          let s2 := { s' with lineStart := s'.cur }
          if (s2.slice s2.lineStart s2.inp).contains 0 then
            (EOF, { syntaxErrorRange "source code cannot contain null bytes" (-1) (-1) s2 with
                    cur := s2.inp })
          else nextcFast s2) := by
        simp [nextcS, hc, hd]
      rw [hu]
      generalize hun : underflow s = u
      obtain ⟨rc, s'⟩ := u
      cases rc with
      | false => simp
      | true =>
        have hk := underflow_keeps_cur s hc (by rw [hun])
        rw [hun] at hk
        simp only at hk
        simp only [Bool.not_true, Bool.false_eq_true, if_false]
        split
        · simp [syntaxErrorRange_inp]
        · exact nextcFast_le _ (by simpa using (by omega : s'.cur < s'.inp))
    · simp [nextcS, hc, hd]
  · have hne : (s.cur != s.inp) = true := by simpa using hc
    simp only [nextcS, hne, if_true]
    exact nextcFast_le s (by omega)

/-- With no CRLF preserved, `translate_newlines` leaves no carriage return: the tokenizer's
carriage-return branches never fire on the parser path. -/
def TranslateRemovesCr : Prop :=
  ∀ (s : List Nat) (execInput : Bool), 13 ∉ translateNewlines s execInput false

theorem translate_go_noCr (n : Nat) : ∀ (l : List Nat) (skip : Bool) (c : Nat) (acc : List Nat),
    l.length ≤ n → 13 ∉ acc → 13 ∉ (translateNewlines.go false l skip c acc).1 := by
  induction n with
  | zero =>
    intro l skip c acc hl h
    cases l with
    | nil => simpa [translateNewlines.go] using h
    | cons _ _ => simp at hl
  | succ n ih =>
    intro l skip c acc hl h
    cases l with
    | nil => simpa [translateNewlines.go] using h
    | cons c0 rest =>
      simp only [List.length_cons] at hl
      rw [translateNewlines.go.eq_def]
      dsimp only
      split
      · cases rest with
        | nil => simpa using h
        | cons c1 rest' =>
          simp only [List.length_cons] at hl
          dsimp only
          split
          · exact ih _ _ _ _ (by omega) (by simp_all)
          · rename_i hc
            exact ih _ _ _ _ (by omega) (by
              simp only [List.mem_cons, not_or]
              refine ⟨?_, h⟩
              intro hc1
              subst hc1
              simp at hc)
      · split
        · exact ih _ _ _ _ (by omega) (by simp_all)
        · rename_i hc
          exact ih _ _ _ _ (by omega) (by
            simp only [List.mem_cons, not_or]
            refine ⟨?_, h⟩
            intro hc1
            subst hc1
            simp at hc)

theorem translateRemovesCr_proven : TranslateRemovesCr := by
  intro s e
  unfold translateNewlines
  dsimp only
  generalize hg : translateNewlines.go false (s.takeWhile (· != 0)) false 0 [] = r
  obtain ⟨acc, c⟩ := r
  have := translate_go_noCr _ (s.takeWhile (· != 0)) false 0 [] (Nat.le_refl _) (by simp)
  rw [hg] at this
  simp only at this ⊢
  split <;> simp_all

/-- Type and string of each token: what the guarantee of `untokenize` covers. -/
def tokKey (l : List TokInfo) : List (Nat × List Nat) := l.map fun t => (t.type, t.str)

/-- `untokenize` on the tokens of a valid source gives text that tokenizes to the same types and
strings. -/
def untokenizeRoundTrips (text : List Nat) : Bool :=
  match parseStr {} (utf8Encode text) .file with
  | .error _ => true
  | .ok _ =>
    let ts : List TokInfo := (tokenizeText text true).1
    match untokenize ts with
    | none => false
    | some out => tokKey (tokenizeText out true).1 == tokKey ts

/-- The docstring of `untokenize`: "The result is guaranteed to tokenize back to match the
input so that the conversion is lossless and round-trips are assured. The guarantee applies
only to the token type and token string". Stated for sources the compiler accepts. -/
def UntokenizeLossless : Prop := ∀ text : List Nat, untokenizeRoundTrips text = true

/-- `if x:\n    \\\ny\n`: a body indented with a backslash continuation. The `INDENT` token's
string is empty, since `tok->buf` moved to the next line, so nothing writes the indentation. -/
def indentByContinuation : List Nat :=
  lit "if x:\n    \\\ny\n"

set_option maxRecDepth 100000 in
theorem untokenizeLossless_refuted : ¬ UntokenizeLossless := fun h =>
  absurd (h indentByContinuation) (by decide +kernel)

end PyLean.PyGrammar.Lexer
