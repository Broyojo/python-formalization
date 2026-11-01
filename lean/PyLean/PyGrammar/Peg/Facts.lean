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

/-! ### Memo -/

/-- The memo is a cache: what `_PyPegen_update_memo` stored at the current token is what
`_PyPegen_is_memoized` finds, with the mark restored. Hypothesis: the token at `p.mark` is
already filled, as `_PyPegen_is_memoized` guarantees before any memo is written there. -/
def MemoReturnsStored : Prop :=
  ∀ (p : PS) (ty : Nat) (node : Ast), p.mark < p.memo.size → p.mark < p.fill →
    let (_, q) := updateMemo p.mark ty node p
    (isMemoized ty q).1 = some node ∧ (isMemoized ty q).2.mark = p.mark

/-! ### `arguments` -/

/-- `_PyAST_arguments` as `_PyPegen_make_arguments` calls it never has more positional
defaults than positional parameters, which is `validate_arguments`'s first check: the
parser cannot produce what the validator refuses. Names and defaults come from the same
`NameDefaultPair` lists. -/
def MakeArgumentsDefaultsFit : Prop :=
  ∀ (a b c d e : Ast),
    match makeArguments a b c d e with
    | .node .arguments_ [posonly, args, _, _, _, _, defaults] _ =>
      (seqOf defaults).length ≤ (seqOf posonly).length + (seqOf args).length
    | _ => False

theorem makeArgumentsDefaultsFit_proven : MakeArgumentsDefaultsFit := by
  intro a b c d e
  simp only [makeArguments, mkAst, Ctor.fields, normFields]
  cases a <;> cases b <;> cases d <;> simp [getNames, getDefaults, joinSeq, seqOf] <;>
    (try split) <;> (try split) <;> simp_all <;> omega

/-! ### String concatenation -/

/-- A `Constant` of an empty `str`. -/
def isEmptyConst (e : Ast) : Bool := isEmptyStrConst e

/-- `foldConsts` stops at the first thing that is not a constant. -/
theorem foldConsts_tail (xs : List Ast) (acc : List Nat) (last : Ast) :
    match (foldConsts xs acc last).2.2 with
    | [] => True
    | e :: _ => isConstant e = false := by
  induction xs generalizing acc last with
  | nil => simp [foldConsts]
  | cons x xs ih =>
    unfold foldConsts
    split
    · exact ih _ _
    · rename_i h
      simpa using h

/-- Pairs of neighbours in a list. -/
def noAdjacentConstants : List Ast → Bool
  | a :: b :: rest => !(isConstant a && isConstant b) && noAdjacentConstants (b :: rest)
  | _ => true

/-- `_build_concatenated_str`'s comment: "if the current elem and the following are
constants, fold them and all consequent constants". What comes out has no two neighbouring
constants, so `f'a' 'b'` is one `Constant`, not two, and each constant is non-empty. -/
def ConcatNormalForm : Prop :=
  ∀ (f : Nat) (xs : List Ast), xs.length < f →
    (foldLoop f xs).all (fun e => !isEmptyStrConst e) = true

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

theorem isEmptyStrConst_mkAt (s : List Nat) (k : Ast) (l : Loc) (h : s ≠ []) :
    isEmptyStrConst (mkAt .Constant [.const (.str s), k] l) = false := by
  cases s with
  | nil => exact absurd rfl h
  | cons x xs => simp [mkAt, mkAst, Ctor.fields, normFields, locArgs, isEmptyStrConst]

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
      unfold foldLoop
      split
      · split
        · dsimp only
          generalize hf : foldConsts rest (constStr e) e = r
          obtain ⟨s, last, tail⟩ := r
          have hl : tail.length ≤ rest.length := by
            have := foldConsts_len rest (constStr e) e
            rw [hf] at this
            simpa using this
          simp only
          split
          · exact ih _ (by omega)
          · rename_i hs
            have hne : s ≠ [] := by simpa using hs
            simp only [List.all_cons, Bool.and_eq_true]
            refine ⟨?_, ih _ (by omega)⟩
            simp [isEmptyStrConst_mkAt _ _ _ hne]
        · split
          · exact ih _ (by omega)
          · rename_i hemp
            simp only [List.all_cons, Bool.and_eq_true]
            exact ⟨by simpa using hemp, ih _ (by omega)⟩
      · rename_i hc
        simp only [List.all_cons, Bool.and_eq_true]
        refine ⟨?_, ih _ (by omega)⟩
        have : isEmptyStrConst e = false := by
          cases e <;> simp_all [isEmptyStrConst, isConstant]
          split <;> simp_all
        simp [this]

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

end PyLean.PyGrammar.Peg
