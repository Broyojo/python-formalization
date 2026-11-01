import PyLean.PyGrammar.Check.Preprocess

/-!
Properties of `Python/ast.c` and `Python/ast_preprocess.c`.
-/

namespace PyLean.PyGrammar.Check

open PyLean

/-- The one-node tree `Try(body=[Pass], handlers=[h], ...)`, or `TryStar`, in a module. -/
def tryTree (c : Ctor) (h : Ast) : Ast :=
  let pass := Ast.node .Pass [] (some ⟨1, 0, 1, 4⟩)
  .node .Module
    [.seq [.node c [.seq [pass], .seq [h], .seq [], .seq []] (some ⟨1, 0, 1, 4⟩)], .seq []] none

/-- `validate` treats the handlers of `Try` and of `TryStar` the same: the C code has two
copies of the case, and they ought to accept the same handlers. -/
def TryHandlersTwin : Prop :=
  ∀ h : Ast, (validate (tryTree .Try h)).toBool = (validate (tryTree .TryStar h)).toBool

/-- A handler whose `lineno` is past its `end_lineno`, with a type so that only the position
check can object. -/
def badHandler : Ast :=
  .node .ExceptHandler
    [.node .Name [.ident [120], .node .Load [] none] (some ⟨1, 0, 1, 1⟩), .null,
     .seq [.node .Pass [] (some ⟨1, 0, 1, 4⟩)]]
    (some ⟨5, 0, 1, 0⟩)

theorem tryHandlersTwin_refuted : ¬ TryHandlersTwin := fun h =>
  absurd (h badHandler) (by decide +kernel)

/-- Every `Name` a validated tree holds went through `validate_name`: no tree `_PyAST_Validate`
accepts has a `Name` called `None`, `True` or `False`, which `codegen_nameop` asserts. -/
def validAccepts (m : Ast) : Bool := (validate m).toBool

/-- `ast.NamedExpr(target=Name("None", Store()), value=...)`. -/
def namedNone : Ast :=
  let l : Option Loc := some ⟨1, 0, 1, 1⟩
  .node .Expression
    [.node .NamedExpr
      [.node .Name [.ident [78, 111, 110, 101], .node .Store [] none] l,
       .node .Constant [.const (.int 1), .null] l] l] none

/-- The same name in plain expression position is refused. -/
def plainNone : Ast :=
  .node .Expression
    [.node .Name [.ident [78, 111, 110, 101], .node .Load [] none] (some ⟨1, 0, 1, 1⟩)] none

/-- A statement of the check above: rejecting `None` as a name does not depend on where the
name sits in the expression. -/
def NamesAlwaysChecked : Prop :=
  ∀ (name : Ast) (l : Option Loc) (v : Ast),
    (validate (.node .Expression [.node .Name [name, .node .Load [] none] l] none)).toBool = false →
    (validate (.node .Expression
      [.node .NamedExpr [.node .Name [name, .node .Store [] none] l, v] l] none)).toBool = false

theorem namesAlwaysChecked_refuted : ¬ NamesAlwaysChecked := fun h => by
  have := h (.ident [78, 111, 110, 101]) (some ⟨1, 0, 1, 1⟩)
    (.node .Constant [.const (.int 1), .null] (some ⟨1, 0, 1, 1⟩)) (by decide +kernel)
  revert this
  decide +kernel

/-- `validate_name` refuses exactly the three constants. -/
def ValidateNameExact : Prop :=
  ∀ cps : List Nat,
    (validateName (.ident cps)).toBool = false ↔
      cps = [78, 111, 110, 101] ∨ cps = [84, 114, 117, 101] ∨ cps = [70, 97, 108, 115, 101]

theorem validateNameExact_proven : ValidateNameExact := by
  intro cps
  unfold validateName
  split <;> simp_all [Except.toBool, ok1, verr]

/-- `VALIDATE_POSITIONS` accepts exactly well-ordered ranges, for ordinary positive lines. -/
def ValidatePositionsOrdered : Prop :=
  ∀ l : Loc, 0 ≤ l.lineno → 0 ≤ l.colOffset →
    ((validatePositions (some l)).toBool = true ↔
      (l.lineno < l.endLineno ∨ (l.lineno = l.endLineno ∧ l.colOffset ≤ l.endColOffset)))

theorem validatePositionsOrdered_proven : ValidatePositionsOrdered := by
  intro l h1 h2
  unfold validatePositions
  simp only
  split
  · rename_i h
    simp [Except.toBool, verr]
    omega
  · split
    · rename_i h3 h4
      simp at h4
      omega
    · split
      · rename_i h3 h4 h5
        simp at h5
        simp [Except.toBool, verr]
        omega
      · rename_i h3 h4 h5
        simp at h5
        simp [Except.toBool, ok1]
        omega

/-- `_validate_nonempty_seq` accepts exactly non-empty sequences. -/
def NonemptySeqExact : Prop :=
  ∀ (xs : List Ast) (what owner : String),
    (validateNonemptySeq (.seq xs) what owner).toBool = true ↔ xs ≠ []

theorem nonemptySeqExact_proven : NonemptySeqExact := by
  intro xs what owner
  unfold validateNonemptySeq seqLen seqL
  cases xs <;> simp [Except.toBool, ok1, verr]

/-- `remove_docstring`: "In case there's just the docstring in the body, replace it with
`pass` keyword, so body won't be empty." With a located first statement, as every statement
out of the parser is, the body stays non-empty when it has anything else or a single
statement. -/
def DocstringRemovalKeepsBody : Prop :=
  ∀ (c : Ctor) (fs : List Ast) (l : Loc) (rest : List Ast),
    removeDocstring (.node c fs (some l) :: rest) ≠ []

theorem docstringRemovalKeepsBody_proven : DocstringRemovalKeepsBody := by
  intro c fs l rest
  cases rest with
  | nil => simp [removeDocstring]
  | cons x xs =>
    simp [removeDocstring]

/-- Constant folding of `match` values preserves value: `-c` folds to the constant
`PyNumber_Negative(c)`, and `a + bj`/`a - bj` to `PyNumber_Add`/`PyNumber_Subtract` of the
two constants, keeping the node's location. Hypothesis: the tree is being optimized
(`syntax_check_only` is false). -/
def FoldPreservesValue : Prop :=
  ∀ (st : PState), st.syntaxCheckOnly = false →
    (∀ (u : Ast) (fs1 : List Ast) (v c : PyConst) (rest : List Ast) (l1 l2 l3 : Option Loc),
      u = .node .USub fs1 l1 → negConst v = some c →
      foldMatchValue st 2 (.node .UnaryOp [u, .node .Constant (.const v :: rest) l2] l3)
        = .node .Constant [.const c, .null] l3) ∧
    (∀ (a b c : PyConst) (r1 r2 fs : List Ast) (l1 l2 l3 l4 : Option Loc) (add : Bool),
      complexArith add a b = some c →
      foldMatchValue st 3 (.node .BinOp
        [.node .Constant (.const a :: r1) l1,
         .node (if add then .Add else .Sub) fs l2,
         .node .Constant (.const b :: r2) l3] l4)
        = .node .Constant [.const c, .null] l4)

theorem foldPreservesValue_proven : FoldPreservesValue := by
  intro st hs
  constructor
  · intro u fs1 v c rest l1 l2 l3 hu hc
    subst hu
    simp [foldMatchValue, hs, hc]
  · intro a b c r1 r2 fs l1 l2 l3 l4 add hc
    cases add <;> simp_all [foldMatchValue]

/-- The result of a `%`-format fold holds one `FormattedValue` per tuple item: folding
`'...' % (a, b)` uses every argument exactly once. -/
def isFormatted : Ast → Bool
  | .node .FormattedValue _ _ => true
  | _ => false

theorem parseFormat_formatted (s : List Nat) (arg x : Ast) (r : List Nat)
    (h : parseFormat s arg = some (x, r)) : isFormatted x = true := by
  unfold parseFormat at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨spec, lj, w, p, rest⟩, _, h⟩ := h
  simp only at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    rfl
  · simp at h

/-- `formatLoop` consumes the tuple: `FormattedValue`s out = in + tuple length. -/
def FormatUsesEveryArg : Prop :=
  ∀ (f : Nat) (fmt : List Nat) (elts acc out : List Ast),
    formatLoop f fmt elts acc = some out →
      (out.filter isFormatted).length = (acc.filter isFormatted).length + elts.length

theorem formatUsesEveryArg_proven : FormatUsesEveryArg := by
  intro f
  induction f with
  | zero => intro fmt elts acc out h; simp [formatLoop] at h
  | succ f ih =>
    intro fmt elts acc out h
    unfold formatLoop at h
    generalize hp : parseLiteral fmt = pr at h
    obtain ⟨lit, rest⟩ := pr
    simp only at h
    have hacc : ∀ acc' : List Ast, acc' = (if lit.isEmpty then acc else constAtM1 lit :: acc) →
        (acc'.filter isFormatted).length = (acc.filter isFormatted).length := by
      intro acc' e
      subst e
      split <;> simp [List.filter, isFormatted, constAtM1]
    cases rest with
    | nil =>
      simp only at h
      split at h
      · rename_i he
        simp only [Option.some.injEq] at h
        subst h
        cases elts with
        | nil =>
          have := hacc _ rfl
          simp only [List.filter_reverse, List.length_reverse]
          simpa using this
        | cons _ _ => simp at he
      · simp at h
    | cons _ after =>
      simp only at h
      cases elts with
      | nil => simp at h
      | cons e es =>
        simp only at h
        split at h
        · rename_i x r hf
          have := ih _ _ _ _ h
          have hx := parseFormat_formatted _ _ _ _ hf
          simp only [List.filter, hx, List.length_cons] at this
          have := hacc _ rfl
          simp only [List.length_cons]
          omega
        · simp at h

/-! ### The syntax-check pass changes nothing -/

/-- What an identity proof needs of the state: it never leaves syntax-check mode, and the
optimization level stays below 2. -/
def Quiet (st : PState) : Prop := st.syntaxCheckOnly = true ∧ st.optimize < 2

theorem foldMatchValue_quiet (st : PState) (h : Quiet st) (f : Nat) (e : Ast) :
    foldMatchValue st f e = e := by
  cases f with
  | zero => rfl
  | succ f =>
    rw [foldMatchValue]
    simp [h.1]

theorem foldBinop_quiet (st : PState) (h : Quiet st) (e : Ast) : foldBinop st e = e := by
  simp [foldBinop, h.1]

theorem set_getD_self (fs : List Ast) (i : Nat) : fs.set i (fs.getD i .null) = fs := by
  induction fs generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i => simpa using ih i

/-- `Quiet` survives the state changes of the walk. -/
theorem quiet_push (st : PState) (h : Quiet st) (x : Bool × Bool × Bool) :
    Quiet { st with cf := x :: st.cf } := h

theorem quiet_pop (st : PState) (h : Quiet st) : Quiet { st with cf := st.cf.drop 1 } := h

/-- The statement proved together for the four mutually recursive functions. -/
def FoldId (f : Nat) : Prop :=
  (∀ (e : Ast) (st : PState), Quiet st →
      (fold f e st).1 = e ∧ Quiet (fold f e st).2) ∧
  (∀ (xs : List Ast) (st : PState), Quiet st →
      (foldList f xs st).1 = xs ∧ Quiet (foldList f xs st).2) ∧
  (∀ (xs : List Ast) (st : PState), Quiet st →
      (foldBody f xs st).1 = xs ∧ Quiet (foldBody f xs st).2) ∧
  (∀ (ss : List Step) (fs : List Ast) (st : PState), Quiet st →
      (runSteps f ss fs st).1 = fs ∧ Quiet (runSteps f ss fs st).2)

/-- With `syntax_check_only` set and `optimize < 2`, as `Py_CompileStringObject` runs it for
`PyCF_ONLY_AST`, `astfold_*` leaves every tree as it found it. -/
def SyntaxOnlyIdentity : Prop := ∀ f, FoldId f

theorem preVisit_quiet (c : Ctor) (l : Option Loc) (st : PState) (h : Quiet st) :
    Quiet (preVisit c l st).2 := by
  unfold preVisit
  split
  · unfold beforeReturn
    dsimp only
    split
    · split
      · exact h
      · exact h
    · exact h
  · unfold beforeLoopExit
    dsimp only
    split
    · split
      · exact h
      · exact h
    · exact h
  · unfold beforeLoopExit
    dsimp only
    split
    · split
      · exact h
      · exact h
    · exact h
  · exact h

theorem mappingKeys_quiet (st : PState) (h : Quiet st) (f : Nat) (c : Ctor) (fs : List Ast) :
    mappingKeys st f c fs = fs := by
  unfold mappingKeys
  split
  · simp [foldMatchValue_quiet st h]
  · rfl

theorem postFold_quiet (st : PState) (h : Quiet st) (c : Ctor) (fs : List Ast) (l : Option Loc) :
    postFold st c fs l = .node c fs l := by
  unfold postFold
  split
  · exact foldBinop_quiet st h _
  · simp [h.1]
  · rfl

theorem removeDoc_guard (st : PState) (h : Quiet st) (b : Bool) :
    (b && decide (st.optimize ≥ 2)) = false := by
  have : ¬ st.optimize ≥ 2 := by
    have := h.2
    omega
  simp [this]

theorem syntaxOnlyIdentity_proven : SyntaxOnlyIdentity := by
  intro f
  induction f with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro e st h
      exact ⟨rfl, h⟩
    · intro xs st h
      exact ⟨rfl, h⟩
    · intro xs st h
      exact ⟨rfl, h⟩
    · intro ss fs st h
      exact ⟨rfl, h⟩
  | succ f ih =>
    obtain ⟨hF, hL, hB, hS⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro e st h
      cases e with
      | node c fs l =>
        by_cases hm : ∃ v, c = .MatchValue ∧ fs = [v]
        · obtain ⟨v, rfl, rfl⟩ := hm
          have : fold (f + 1) (.node .MatchValue [v] l) st =
              (.node .MatchValue [foldMatchValue st (f + 1) v] l, st) := rfl
          rw [this]
          simp [foldMatchValue_quiet st h, h]
        · have heq : fold (f + 1) (.node c fs l) st =
              (let (_, s1) := preVisit c l st
               let (fs', s2) := runSteps f (visits c) fs s1
               (postFold s2 c (mappingKeys s2 f c fs') l, s2)) := by
            rw [fold]
            split
            · rename_i v l' he
              exact absurd ⟨v, (Ast.node.inj he).1, (Ast.node.inj he).2.1⟩ hm
            · rename_i c' fs' l' he
              simp only [Ast.node.injEq] at he
              obtain ⟨rfl, rfl, rfl⟩ := he
              rfl
            · simp at *
            · simp at *
          rw [heq]
          have hp := preVisit_quiet c l st h
          generalize preVisit c l st = r1 at hp ⊢
          obtain ⟨_, s1⟩ := r1
          have ⟨hr, hq⟩ := hS (visits c) fs s1 hp
          generalize hrs : runSteps f (visits c) fs s1 = r2 at hr hq ⊢
          obtain ⟨fs', s2⟩ := r2
          simp only at hr hq ⊢
          subst hr
          rw [mappingKeys_quiet s2 hq, postFold_quiet s2 hq]
          exact ⟨rfl, hq⟩
      | seq xs =>
        have heq : fold (f + 1) (.seq xs) st =
            (let (ys, s1) := foldList f xs st; (.seq ys, s1)) := by
          rw [fold]
        rw [heq]
        have ⟨h1, h2⟩ := hL xs st h
        generalize foldList f xs st = r at h1 h2 ⊢
        obtain ⟨ys, s1⟩ := r
        simp only at h1 h2 ⊢
        subst h1
        exact ⟨rfl, h2⟩
      | _ =>
        rw [fold]
        exact ⟨rfl, h⟩
    · intro xs st h
      cases xs with
      | nil => exact ⟨rfl, h⟩
      | cons x xs =>
        have heq : foldList (f + 1) (x :: xs) st =
            (let (x', s1) := fold f x st
             let (xs', s2) := foldList f xs s1
             (x' :: xs', s2)) := by
          rw [foldList]
        rw [heq]
        have ⟨h1, h2⟩ := hF x st h
        generalize fold f x st = r at h1 h2 ⊢
        obtain ⟨x', s1⟩ := r
        simp only at h1 h2 ⊢
        subst h1
        have ⟨h3, h4⟩ := hL xs s1 h2
        generalize foldList f xs s1 = r at h3 h4 ⊢
        obtain ⟨xs', s2⟩ := r
        simp only at h3 h4 ⊢
        subst h3
        exact ⟨rfl, h4⟩
    · intro xs st h
      rw [foldBody]
      dsimp only
      rw [removeDoc_guard st h]
      simp only [Bool.false_eq_true, if_false]
      have ⟨h1, h2⟩ := hL xs st h
      generalize foldList f xs st = r at h1 h2 ⊢
      obtain ⟨ys, s1⟩ := r
      simp only at h1 h2 ⊢
      subst h1
      cases hd : (getDocString ys).isSome <;> simp [hd, h2]
    · intro ss fs st h
      cases ss with
      | nil => exact ⟨rfl, h⟩
      | cons s rest =>
        rw [runSteps]
        cases s with
        | fld i =>
          dsimp only
          have ⟨h1, h2⟩ := hF (fs.getD i .null) st h
          generalize fold f (fs.getD i .null) st = r at h1 h2 ⊢
          obtain ⟨v, s1⟩ := r
          simp only at h1 h2 ⊢
          subst h1
          rw [set_getD_self]
          exact hS rest fs s1 h2
        | body i =>
          dsimp only
          split
          · rename_i xs he
            have ⟨h1, h2⟩ := hB xs st h
            generalize foldBody f xs st = r at h1 h2 ⊢
            obtain ⟨b, s1⟩ := r
            simp only at h1 h2 ⊢
            subst h1
            have hset : fs.set i (.seq b) = fs := by
              rw [← he]
              exact set_getD_self fs i
            rw [hset]
            exact hS rest fs s1 h2
          · exact hS rest fs st h
        | ann i =>
          dsimp only
          split
          · exact hS rest fs st h
          · have ⟨h1, h2⟩ := hF (fs.getD i .null) st h
            generalize fold f (fs.getD i .null) st = r at h1 h2 ⊢
            obtain ⟨v, s1⟩ := r
            simp only at h1 h2 ⊢
            subst h1
            rw [set_getD_self]
            exact hS rest fs s1 h2
        | push a b c => exact hS rest fs _ (quiet_push st h _)
        | pop => exact hS rest fs _ (quiet_pop st h)

end PyLean.PyGrammar.Check
