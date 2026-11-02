import PyLean.PyGrammar.Peg.Interp

/-!
Universally quantified facts about the parser's runtime helpers: errors, the memo, and the
actions that build `arguments` and concatenate strings. Hypotheses, where any, are the type
invariants of the C structures and are named in the docstrings.
-/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### First error wins -/

/-- `// Bail out if we already have an error set.`: with `error_indicator` and an exception
set, no raise replaces the exception or changes the parser, whichever entry point is
used. -/
def FirstErrorWins : Prop :=
  ∀ (p : PS), p.errorIndicator = true → p.errOccurred = true →
    (∀ (cls msg : String) (a b c d : Int), (raiseKnownLocation cls a b c d msg p).2 = p) ∧
    (∀ (cls msg : String), (raiseError0 cls msg p).2 = p) ∧
    (∀ (cls msg : String) (m : Bool), (raiseError cls m msg p).2 = p)

theorem firstErrorWins_proven : FirstErrorWins := by
  intro p h1 h2
  refine ⟨?_, ?_, ?_⟩
  · intro cls msg a b c d
    simp [raiseKnownLocation, h1, h2, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure]
  · intro cls msg
    simp [raiseError0, h1, h2, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure]
  · intro cls msg m
    simp [raiseError, h1, h2, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure]

/-- `_Pypegen_tokenizer_error` returns `-1` from every branch of its switch. -/
def TokenizerErrorIsFailure : Prop := ∀ p : PS, (tokenizerError p).1 = -1

/-! ### `arguments` -/

theorem seqOf_getNames (s : Ast) : (seqOf (getNames s)).length = (seqOf s).length := by
  simp [getNames, seqOf]

theorem seqOf_getDefaults (s : Ast) : (seqOf (getDefaults s)).length = (seqOf s).length := by
  simp [getDefaults, seqOf]

theorem seqOf_join (a b : Ast) :
    (seqOf (joinSeq a b)).length = (seqOf a).length + (seqOf b).length := by
  simp [joinSeq, seqOf]

/-- `_PyAST_arguments` as `_PyPegen_make_arguments` calls it never has more positional
defaults than positional parameters, which is `validate_arguments`'s check: the parser cannot
build what the validator refuses. Precondition, from the grammar's calls: at most one of
`slash_without_default` and `slash_with_default` is given. -/
def MakeArgumentsDefaultsFit : Prop :=
  ∀ (a b c d : Ast), (isNullA a = true ∨ isNullA b = true) →
    (seqOf (posdefaultsOf b d)).length ≤
      (seqOf (posonlyOf a b)).length + (seqOf (posargsOf c d)).length

theorem seqOf_seq (xs : List Ast) : seqOf (.seq xs) = xs := rfl

theorem makeArgumentsDefaultsFit_proven : MakeArgumentsDefaultsFit := by
  intro a b c d h
  unfold posdefaultsOf posonlyOf posargsOf
  cases ha : isNullA a <;> cases hb : isNullA b <;> cases hc : isNullA c <;>
    cases hd : isNullA d <;>
    simp [ha, hb, hc, hd, seqOf_getNames, seqOf_getDefaults, seqOf_join, seqOf_seq] <;>
    first
    | omega
    | (simp [ha, hb] at h)

/-! ### String concatenation -/

theorem foldConsts_len (xs : List Ast) (acc : List Nat) (last : Ast) :
    (foldConsts xs acc last).2.2.length ≤ xs.length := by
  induction xs generalizing acc last with
  | nil => simp [foldConsts]
  | cons x xs ih =>
    unfold foldConsts
    split
    · have := ih (acc ++ constStr x) x
      simp only [List.length_cons]
      omega
    · simp

/-- `_build_concatenated_str`: "Drop all empty contanst strings". What the folding loop
returns holds no constant empty string, for any input list. -/
def ConcatNormalForm : Prop :=
  ∀ (f : Nat) (xs : List Ast), xs.length < f →
    (foldLoop f xs).all (fun e => !isEmptyStrConst e) = true

theorem isEmptyStrConst_mkAt (s : List Nat) (k : Ast) (l : Loc) (h : s.isEmpty = false) :
    isEmptyStrConst (mkAt .Constant [.const (.str s), k] l) = false := by
  cases s with
  | nil => simp at h
  | cons x xs => rfl

theorem concatNormalForm_proven : ConcatNormalForm := by
  intro f
  induction f with
  | zero => intro xs h; simp at h
  | succ f ih =>
    intro xs h
    cases xs with
    | nil => simp [foldLoop]
    | cons e rest =>
      simp only [List.length_cons] at h
      have hlen := foldConsts_len rest (constStr e) e
      rw [foldLoop]
      split
      · dsimp only
        split
        · exact ih _ (by omega)
        · rename_i hs
          simp only [List.all_cons, Bool.and_eq_true]
          refine ⟨?_, ih _ (by omega)⟩
          have hs' : (foldConsts rest (constStr e) e).1.isEmpty = false := by simpa using hs
          simp [isEmptyStrConst_mkAt _ _ _ hs']
      · split
        · exact ih _ (by omega)
        · rename_i hemp
          simp only [List.all_cons, Bool.and_eq_true]
          exact ⟨by simpa using hemp, ih _ (by omega)⟩

/-! ### Identifiers -/

/-- `_PyPegen_new_identifier` refuses exactly the spellings the keyword table cannot have
made names, after NFKC: no `Name` in a tree is called `None`, `True` or `False`. -/
def IdentifierNeverConstant : Prop :=
  ∀ (bytes : List Nat) (p : PS),
    match (newIdentifier bytes p).1 with
    | .ident s => s ≠ [78, 111, 110, 101] ∧ s ≠ [84, 114, 117, 101]
        ∧ s ≠ [70, 97, 108, 115, 101]
    | _ => True

/-! ### Numbers -/

/-- Integer literals: decimal digits read as their value, whatever the digit-group
underscores, for literals not starting with `0`. -/
def DecimalValue : Prop :=
  ∀ ds : List Nat, ds ≠ [] → (∀ d ∈ ds, 49 ≤ d ∧ d ≤ 57) → ds.length ≤ 19 →
    match parseNumber ds with
    | .ok (.int v) => v = (ds.foldl (fun a d => a * 10 + (d - 48)) 0 : Nat)
    | _ => False

/-! ### Other action helpers -/

theorem dropSpace_tail (r : List Nat) (nl : Bool) :
    ∃ pre, r = pre ++ (dropTrailingSpace r nl).1 ∧ ∀ c ∈ pre, isUnicodeSpace c = true := by
  induction r generalizing nl with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons c t ih =>
    unfold dropTrailingSpace
    split
    · rename_i hc
      obtain ⟨pre, e, hp⟩ := ih (nl || c == 13 || c == 10)
      refine ⟨c :: pre, by simpa using e, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with q | q
      · exact q ▸ hc
      · exact hp x q
    · exact ⟨[], rfl, by simp⟩

theorem stripTail_tail (f : Nat) (r : List Nat) :
    ∃ pre, r = pre ++ stripDebugTail f r ∧
      ∀ c ∈ pre, isUnicodeSpace c = true ∨ c = 92 := by
  induction f generalizing r with
  | zero => exact ⟨[], rfl, by simp⟩
  | succ f ih =>
    unfold stripDebugTail
    split
    · exact ⟨[], rfl, by simp⟩
    · obtain ⟨pre, e, hp⟩ := dropSpace_tail r false
      have hsp : ∀ c ∈ pre, isUnicodeSpace c = true ∨ c = 92 := fun c hc => Or.inl (hp c hc)
      split
      · rename_i t hq
        rw [hq] at e
        simp only at e
        obtain ⟨pre2, e2, hp2⟩ := ih t
        refine ⟨pre ++ 92 :: pre2, ?_, fun c hc => ?_⟩
        · rw [e]
          simp only [List.append_assoc, List.cons_append]
          rw [← e2]
        · rcases List.mem_append.1 hc with q | q
          · exact hsp c q
          · rcases List.mem_cons.1 q with q | q
            · exact Or.inr q
            · exact hp2 c q
      · rw [‹dropTrailingSpace r false = _›] at e
        exact ⟨pre, e, hsp⟩

theorem dropSpace_all (pre r : List Nat) (nl : Bool) (hp : ∀ c ∈ pre, isUnicodeSpace c = true)
    (hr : isUnicodeSpace 61 = false) :
    (dropTrailingSpace (pre ++ 61 :: r) nl).1 = 61 :: r := by
  induction pre generalizing nl with
  | nil =>
    simp only [List.nil_append, dropTrailingSpace, hr]
    rfl
  | cons c t ih =>
    simp only [List.cons_append, dropTrailingSpace]
    rw [if_pos (hp c (List.mem_cons_self ..))]
    exact ih _ fun x hx => hp x (List.mem_cons_of_mem _ hx)

/-- `_strip_interpolation_debug_expr`, from its comments: "Discard whitespace ... after the debug
'=' but preserve whitespace before it", and "Preserve unexpected metadata instead of dropping
source text". Whitespace after the `=` goes, whatever comes before it, and in no case is anything
removed but a final `=` and what follows it, which is whitespace and continuation backslashes. -/
def StripInterpolation : Prop :=
  (∀ r tail : List Nat, (∀ c ∈ tail, isUnicodeSpace c = true) →
    stripInterpolationDebugExpr (r ++ 61 :: tail) = r) ∧
  (∀ s : List Nat, stripInterpolationDebugExpr s = s ∨
    ∃ tail, s = stripInterpolationDebugExpr s ++ 61 :: tail ∧
      ∀ c ∈ tail, isUnicodeSpace c = true ∨ c = 92)

theorem strip_step (f : Nat) (r t : List Nat) (nl : Bool) (hne : r ≠ [])
    (h : dropTrailingSpace r false = (61 :: t, nl)) : stripDebugTail (f + 1) r = 61 :: t := by
  cases r with
  | nil => exact (hne rfl).elim
  | cons c cs =>
    show (match dropTrailingSpace (c :: cs) false with
      | (92 :: t, true) => stripDebugTail f t
      | (r', _) => r') = _
    rw [h]
    rfl

theorem stripInterpolation_proven : StripInterpolation := by
  have h61 : isUnicodeSpace 61 = false := by decide
  constructor
  · intro r tail ht
    unfold stripInterpolationDebugExpr
    have er : (r ++ 61 :: tail).reverse = tail.reverse ++ 61 :: r.reverse := by simp
    have hd := dropSpace_all tail.reverse r.reverse false (fun c hc => ht c (by simpa using hc)) h61
    have hne : tail.reverse ++ 61 :: r.reverse ≠ [] := by simp
    have hn : (r ++ 61 :: tail).length = (r.length + tail.length) + 1 := by
      simp
      omega
    generalize hq : dropTrailingSpace (tail.reverse ++ 61 :: r.reverse) false = q at hd
    obtain ⟨r', nl⟩ := q
    simp only at hd
    subst hd
    rw [hn, er, strip_step _ _ _ nl hne hq]
    simp
  · intro s
    unfold stripInterpolationDebugExpr
    obtain ⟨pre, e, hp⟩ := stripTail_tail s.length s.reverse
    generalize hs : stripDebugTail s.length s.reverse = out at e
    match out, e with
    | 61 :: t, e =>
      refine Or.inr ⟨pre.reverse, ?_, fun c hc => hp c (by simpa using hc)⟩
      have : s = (pre ++ 61 :: t).reverse := by rw [← e]; simp
      rw [this]
      simp
    | [], _ => exact Or.inl rfl
    | c :: t, _ =>
      by_cases hc : c = 61
      · subst hc
        rename_i e
        refine Or.inr ⟨pre.reverse, ?_, fun c hc => hp c (by simpa using hc)⟩
        have : s = (pre ++ 61 :: t).reverse := by rw [← e]; simp
        rw [this]
        simp
      · left
        split
        · rename_i h
          cases h
          exact (hc rfl).elim
        · rfl

/-- `_PyPegen_register_stmts`: nothing in the first pass; in the second it records the last
statement unless a later one is already recorded. -/
def RegisterStmts : Prop := ∀ (a : Ast) (xs : List Ast) (c : Ctor) (fs : List Ast) (loc : Loc) (p : PS),
  (p.callInvalidRules = false → registerStmts a p = (a, p)) ∧
  (p.callInvalidRules = true → p.lastStmt.1 ≤ loc.lineno →
    (registerStmts (.seq (xs ++ [.node c fs (some loc)])) p).2.lastStmt
      = (loc.lineno, loc.colOffset))

theorem registerStmts_proven : RegisterStmts := by
  intro a xs c fs loc p
  constructor
  · intro h
    simp [registerStmts, h, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure]
  · intro h1 h2
    have : ¬ p.lastStmt.1 > loc.lineno := by omega
    simp [registerStmts, h1, this, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      MonadState.modifyGet, seqOf, locOf]

end PyLean.PyGrammar.Peg
