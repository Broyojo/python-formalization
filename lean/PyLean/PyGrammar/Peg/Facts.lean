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

end PyLean.PyGrammar.Peg
