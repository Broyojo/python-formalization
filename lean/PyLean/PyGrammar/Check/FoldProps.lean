import PyLean.PyGrammar.Check.Props

/-!
What the `astfold_*` walkers do when they really fold, with `syntax_check_only` off.

`FoldReachesWalked` is the walkers' property: `astfold_expr` replaces every `Name('__debug__', Load)`
it sees, so if a tree still holds one, some walker skipped a field. `Clean` asks this of every field
that `Parser/Python.asdl` types as a node, so the statement does not lean on `visits`; `coverOK`
checks each row of `visits` against the ASDL. Fuel appears only as `fuelOut`, set when the model
ran out, which is never a Python outcome.

The broad statement is false: `astfold_pattern` sends `MatchValue` values and `MatchMapping` keys to
`fold_const_match_patterns`, which does not walk them. That is `FoldReachesAll` and the bug
`pygrammar-check-debug-in-pattern`.

`FoldReachesNames`, the rest, is false too: the `NamedExpr_kind` case of `astfold_expr` folds the
value and not the target (`Python/ast_preprocess.c:632-634`), and `validate_expr` accepts a target
that is a `Name` in `Load` context (`Python/ast.c:392-399`), so a hand-built tree keeps a
`__debug__` load there. The grammar only builds `Store` targets. That is the scope record
`pygrammar-check-fold-namedexpr-target`. `FoldReachesWalked` sets that field aside as well and
holds.
-/

namespace PyLean.PyGrammar.Check

open PyLean

/-- `Name('__debug__', Load)`, what the `Name_kind` case of `astfold_expr` replaces. -/
def isDebugLoad : Ast → Bool
  | .node .Name [.ident id, .node .Load _ _] _ => id == "__debug__".toList.map Char.toNat
  | _ => false

/-- Field types of `Parser/Python.asdl` that can hold an expression somewhere below. -/
def nodeTyped : FieldBase → Bool
  | .identifier | .int | .string | .constant | .expr_context_ | .boolop_ | .operator_ | .unaryop_
  | .cmpop_ | .alias_ | .type_ignore_ => false
  | _ => true

/-- Indices of the node-typed fields of a constructor. -/
def astFields (c : Ctor) : List Nat :=
  (c.fields.zipIdx.filter fun x => nodeTyped x.1.2.1).map (·.2)

/-- No `__debug__` load in any node-typed field, except where `skip` says. -/
inductive Clean (skip : Ctor → Nat → Bool) : Ast → Prop
  | node {c : Ctor} {fs : List Ast} {l : Option Loc} : isDebugLoad (.node c fs l) = false →
      (∀ i, i ∈ astFields c → skip c i = false → Clean skip (fs.getD i .null)) →
      Clean skip (.node c fs l)
  | seq {xs : List Ast} : (∀ x, x ∈ xs → Clean skip x) → Clean skip (.seq xs)
  | leaf {a : Ast} : (∀ c fs l, a ≠ .node c fs l) → (∀ xs, a ≠ .seq xs) → Clean skip a

theorem Clean.field {sk : Ctor → Nat → Bool} {c : Ctor} {fs : List Ast} {l : Option Loc}
    (h : Clean sk (.node c fs l)) {i : Nat} (hi : i ∈ astFields c) (hs : sk c i = false) :
    Clean sk (fs.getD i .null) := by
  cases h with
  | node _ k => exact k i hi hs
  | leaf h1 _ => exact absurd rfl (h1 c fs l)

theorem Clean.elem {sk : Ctor → Nat → Bool} {xs : List Ast} (h : Clean sk (.seq xs)) {x : Ast}
    (hx : x ∈ xs) : Clean sk x := by
  cases h with
  | seq k => exact k x hx
  | leaf _ h2 => exact absurd rfl (h2 xs)

theorem clean_null (sk : Ctor → Nat → Bool) : Clean sk .null :=
  Clean.leaf (fun _ _ _ h => by cases h) (fun _ h => by cases h)

/-- Handled by `astfold_mod`, not `astfold_expr`/`astfold_stmt`. -/
def modSkip (c : Ctor) : Bool :=
  c == .Module || c == .Interactive || c == .Expression || c == .FunctionType

/-- `MatchValue.value` and `MatchMapping.keys`, which `astfold_pattern` does not walk. -/
def patSkip (c : Ctor) (i : Nat) : Bool :=
  (c == .MatchValue && i == 0) || (c == .MatchMapping && i == 0)

/-- Annotations: `from __future__ import annotations` keeps them unevaluated, unfolded. -/
def annSkip (c : Ctor) (i : Nat) : Bool :=
  (c == .arg_ && i == 1) || (c == .AnnAssign && i == 1)
    || ((c == .FunctionDef || c == .AsyncFunctionDef) && i == 4)

def skipBroad (fut : Bool) (c : Ctor) (i : Nat) : Bool := modSkip c || (fut && annSkip c i)

def skipNarrow (fut : Bool) (c : Ctor) (i : Nat) : Bool := skipBroad fut c i || patSkip c i

/-- `NamedExpr.target`, which the `NamedExpr_kind` case of `astfold_expr` does not walk:
`Python/ast_preprocess.c:632-634` calls `astfold_expr` on the value only. -/
def walrusSkip (c : Ctor) (i : Nat) : Bool := c == .NamedExpr && i == 0

def skipWalked (fut : Bool) (c : Ctor) (i : Nat) : Bool := skipNarrow fut c i || walrusSkip c i

/-- The body a module's `astfold_mod` case folds. -/
def modBody : Ast → Ast
  | .node .Module (b :: _) _ => b
  | .node .Interactive [b] _ => b
  | .node .Expression [b] _ => b
  | _ => .null

/-- Every `__debug__` load in a module is folded, unconditionally on the source. Hypothesis:
folding is on, the documented meaning of `syntax_check_only` being off. -/
def FoldReachesAll : Prop := ∀ (fuel : Nat) (st : PState) (m : Ast), st.syntaxCheckOnly = false →
  (foldMod fuel m st).2.fuelOut = false →
    Clean (skipBroad st.futureAnnotations) (modBody (foldMod fuel m st).1)

/-- The same, setting aside the two fields of `patSkip`. False: the target of a `NamedExpr` is
not walked either, and a hand-built tree can hold a `__debug__` load there. -/
def FoldReachesNames : Prop := ∀ (fuel : Nat) (st : PState) (m : Ast), st.syntaxCheckOnly = false →
  (foldMod fuel m st).2.fuelOut = false →
    Clean (skipNarrow st.futureAnnotations) (modBody (foldMod fuel m st).1)

/-- The same, setting aside `NamedExpr.target` too: every other node-typed field of
`Parser/Python.asdl` is reached. Hypothesis: folding is on, as in `FoldReachesAll`. Like the two
statements above it speaks of the nodes the folded tree holds: `Clean` does not say that the walk
kept every node it was given. -/
def FoldReachesWalked : Prop := ∀ (fuel : Nat) (st : PState) (m : Ast), st.syntaxCheckOnly = false →
  (foldMod fuel m st).2.fuelOut = false →
    Clean (skipWalked st.futureAnnotations) (modBody (foldMod fuel m st).1)

/-! ### The refutation -/

/-- A path through a tree, along fields `Clean` looks at, ending on a `__debug__` load. -/
def debugAt (sk : Ctor → Nat → Bool) : List Nat → Ast → Bool
  | [], e => isDebugLoad e
  | i :: p, .node c fs _ =>
    (astFields c).contains i && !sk c i && debugAt sk p (fs.getD i .null)
  | i :: p, .seq xs => decide (i < xs.length) && debugAt sk p (xs.getD i .null)
  | _ :: _, _ => false

theorem not_clean_of_debugAt (sk : Ctor → Nat → Bool) (p : List Nat) (e : Ast)
    (h : debugAt sk p e = true) : ¬ Clean sk e := by
  induction p generalizing e with
  | nil =>
    intro hc
    cases hc with
    | node h1 _ =>
      rw [debugAt, h1] at h
      cases h
    | seq _ => cases h
    | leaf h1 _ =>
      cases e with
      | node c fs l => exact h1 c fs l rfl
      | _ => cases h
  | cons i p ih =>
    intro hc
    cases e with
    | node c fs l =>
      simp only [debugAt, Bool.and_eq_true, Bool.not_eq_true'] at h
      have hi : i ∈ astFields c := by simpa using h.1.1
      exact ih _ h.2 (hc.field hi h.1.2)
    | seq xs =>
      simp only [debugAt, Bool.and_eq_true, decide_eq_true_eq] at h
      have hm : xs.getD i .null ∈ xs := by
        have e : xs.getD i .null = xs[i]'h.1 := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h.1]
        rw [e]
        exact List.getElem_mem h.1
      exact ih _ h.2 (hc.elem hm)
    | _ => cases h

/-- `match x:\n    case __debug__.real: pass\n`. -/
def debugInPattern : Ast :=
  let load := Ast.node .Load [] none
  let dbg := Ast.node .Name [.ident ("__debug__".toList.map Char.toNat), load] none
  let attr := Ast.node .Attribute [dbg, .ident ("real".toList.map Char.toNat), load] none
  let case_ := Ast.node .match_case_
    [.node .MatchValue [attr] none, .null, .seq [.node .Pass [] none]] none
  .node .Module [.seq [.node .Match [.node .Name [.ident [120], load] none, .seq [case_]] none],
    .seq []] none

set_option maxRecDepth 100000 in
theorem foldReachesAll_refuted : ¬ FoldReachesAll := fun h =>
  not_clean_of_debugAt (skipBroad false) [0, 1, 0, 0, 0, 0] _ (by decide +kernel)
    (h 64 {} debugInPattern rfl (by decide +kernel))

/-- `ast.Module([ast.Expr(ast.NamedExpr(d, d))], [])` with `d = ast.Name('__debug__', ast.Load())`
as both target and value. Only a hand-built tree has it: the grammar gives a walrus target the
`Store` context, and compiling `(__debug__ := 1)` is rejected in symbol-table analysis
(`Python/symtable.c:1624-1627`), while `validate_expr` checks no more than that the target is a
`Name`. -/
def debugInWalrus : Ast :=
  let load := Ast.node .Load [] none
  let dbg := Ast.node .Name [.ident ("__debug__".toList.map Char.toNat), load] none
  .node .Module [.seq [.node .Expr [.node .NamedExpr [dbg, dbg] none] none], .seq []] none

set_option maxRecDepth 100000 in
/-- What the folder makes of it at optimize level 0: the value becomes `Constant(True)` and the
target stays. This is the tree `compile(..., flags=ast.PyCF_OPTIMIZED_AST)` returns on 3.15.2, the
output of the reproducer in `bugs/pygrammar-check-fold-namedexpr-target.yaml`. One input, so it
credits no row. -/
theorem debugInWalrus_folded :
    modBody (foldMod 64 debugInWalrus {}).1 =
      .seq [.node .Expr [.node .NamedExpr
        [.node .Name [.ident ("__debug__".toList.map Char.toNat), .node .Load [] none] none,
         .node .Constant [.const .true_, .null] none] none] none] := by
  rfl

set_option maxRecDepth 100000 in
theorem foldReachesNames_refuted : ¬ FoldReachesNames := fun h =>
  not_clean_of_debugAt (skipNarrow false) [0, 0, 0] _ (by decide +kernel)
    (h 64 {} debugInWalrus rfl (by decide +kernel))

/-! ### Coverage of `visits` against `Parser/Python.asdl` -/

/-- The fields a row of `visits` folds. -/
def stepIdx (fut : Bool) : List Step → List Nat
  | [] => []
  | .fld i :: r => i :: stepIdx fut r
  | .body i :: r => i :: stepIdx fut r
  | .ann i :: r => if fut then stepIdx fut r else i :: stepIdx fut r
  | .push _ _ _ :: r => stepIdx fut r
  | .pop :: r => stepIdx fut r

/-- A row of `visits` covers every node-typed field that `skipWalked` does not set aside. -/
def coverOK (fut : Bool) (c : Ctor) : Bool :=
  (astFields c).all fun i => skipWalked fut c i || (stepIdx fut (visits c)).contains i

set_option maxHeartbeats 4000000 in
theorem coverOK_all (fut : Bool) (c : Ctor) : coverOK fut c = true := by
  cases fut <;> cases c <;> rfl

theorem visits_cover (fut : Bool) (c : Ctor) (i : Nat) (hi : i ∈ astFields c)
    (hs : skipWalked fut c i = false) : i ∈ stepIdx fut (visits c) := by
  have h := coverOK_all fut c
  unfold coverOK at h
  have := List.all_eq_true.mp h i hi
  rw [hs] at this
  simpa using this

/-! ### The walk -/

structure Keep (st r : PState) : Prop where
  sc : r.syntaxCheckOnly = st.syntaxCheckOnly
  fa : r.futureAnnotations = st.futureAnnotations
  fu : st.fuelOut = true → r.fuelOut = true

theorem Keep.refl (st : PState) : Keep st st := ⟨rfl, rfl, id⟩

theorem Keep.trans {a b c : PState} (x : Keep a b) (y : Keep b c) : Keep a c :=
  ⟨y.sc.trans x.sc, y.fa.trans x.fa, fun h => y.fu (x.fu h)⟩

theorem Keep.false_of {a b : PState} (x : Keep a b) (h : b.fuelOut = false) : a.fuelOut = false := by
  cases ha : a.fuelOut with
  | false => rfl
  | true => rw [x.fu ha] at h; exact h

theorem keep_preVisit (c : Ctor) (l : Option Loc) (st : PState) : Keep st (preVisit c l st).2 := by
  unfold preVisit
  split
  · unfold beforeReturn
    split
    · split
      · exact ⟨rfl, rfl, id⟩
      · exact Keep.refl st
    · exact Keep.refl st
  · unfold beforeLoopExit
    split
    · split
      · exact ⟨rfl, rfl, id⟩
      · exact Keep.refl st
    · exact Keep.refl st
  · unfold beforeLoopExit
    split
    · split
      · exact ⟨rfl, rfl, id⟩
      · exact Keep.refl st
    · exact Keep.refl st
  · exact Keep.refl st

theorem getD_set_ne (fs : List Ast) (i j : Nat) (v : Ast) (h : j ≠ i) :
    (fs.set i v).getD j .null = fs.getD j .null := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, Ne.symm h]

theorem clean_getD_set {sk : Ctor → Nat → Bool} (fs : List Ast) (i : Nat) (v : Ast)
    (h : Clean sk v) : Clean sk ((fs.set i v).getD i .null) := by
  by_cases hi : i < fs.length
  · have : (fs.set i v).getD i .null = v := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_set, hi]
    rw [this]
    exact h
  · have : (fs.set i v).getD i .null = .null := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_set, hi]
    rw [this]
    exact clean_null sk

/-- After a step on field `i`: `i` joins the fields known clean. -/
theorem steps_cons {sk : Ctor → Nat → Bool} {R fs : List Ast} {S : List Nat} {i : Nat} {v : Ast}
    (hv : Clean sk v) (h1 : ∀ j, j ∈ S → Clean sk (R.getD j .null))
    (h2 : ∀ j, j ∉ S → R.getD j .null = (fs.set i v).getD j .null) :
    (∀ j, j ∈ i :: S → Clean sk (R.getD j .null)) ∧
    (∀ j, j ∉ i :: S → R.getD j .null = fs.getD j .null) := by
  constructor
  · intro j hj
    by_cases hs : j ∈ S
    · exact h1 j hs
    · have : j = i := by simpa [hs] using hj
      subst this
      rw [h2 j hs]
      exact clean_getD_set fs j v hv
  · intro j hj
    have h3 : j ≠ i := fun e => hj (by simp [e])
    have h4 : j ∉ S := fun e => hj (List.mem_cons_of_mem _ e)
    rw [h2 j h4, getD_set_ne fs i j v h3]

theorem clean_constAtM1 (sk : Ctor → Nat → Bool) (s : List Nat) : Clean sk (constAtM1 s) :=
  Clean.node rfl fun i hi _ => by
    have : astFields .Constant = [] := by decide +kernel
    rw [this] at hi
    cases hi

theorem clean_ite {sk : Ctor → Nat → Bool} {c : Prop} [Decidable c] {a b : Ast} (ha : Clean sk a)
    (hb : Clean sk b) : Clean sk (if c then a else b) := by
  by_cases h : c
  · rw [if_pos h]
    exact ha
  · rw [if_neg h]
    exact hb

theorem parseFormat_clean {sk : Ctor → Nat → Bool} (s : List Nat) (arg x : Ast) (r : List Nat)
    (h : parseFormat s arg = some (x, r)) (ha : Clean sk arg) : Clean sk x := by
  unfold parseFormat at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨spec, lj, w, p, rest⟩, _, h⟩ := h
  simp only at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    refine Clean.node rfl fun i hi _ => ?_
    have e : astFields .FormattedValue = [0, 2] := by decide +kernel
    rw [e] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ha
    · show Clean sk (ite _ _ _)
      exact clean_ite (clean_null sk) (clean_constAtM1 sk _)
  · simp at h

theorem formatLoop_clean {sk : Ctor → Nat → Bool} (f : Nat) (fmt : List Nat) (elts acc out : List Ast)
    (h : formatLoop f fmt elts acc = some out) (ha : ∀ x, x ∈ acc → Clean sk x)
    (he : ∀ x, x ∈ elts → Clean sk x) : ∀ x, x ∈ out → Clean sk x := by
  induction f generalizing fmt elts acc with
  | zero => simp [formatLoop] at h
  | succ f ih =>
    unfold formatLoop at h
    generalize hp : parseLiteral fmt = pr at h
    obtain ⟨lit, rest⟩ := pr
    simp only at h
    have hacc : ∀ x, x ∈ (if lit.isEmpty then acc else constAtM1 lit :: acc) → Clean sk x := by
      intro x hx
      split at hx
      · exact ha x hx
      · rcases List.mem_cons.mp hx with h1 | h1
        · rw [h1]
          exact clean_constAtM1 sk _
        · exact ha x h1
    cases rest with
    | nil =>
      simp only at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        intro x hx
        exact hacc x (by simpa using hx)
      · simp at h
    | cons _ after =>
      simp only at h
      cases elts with
      | nil => simp at h
      | cons e es =>
        simp only at h
        split at h
        · rename_i x r hf
          refine ih r es _ h ?_ (fun y hy => he y (List.mem_cons_of_mem _ hy))
          intro y hy
          rcases List.mem_cons.mp hy with h1 | h1
          · rw [h1]
            exact parseFormat_clean after e x r hf (he e (List.mem_cons_self ..))
          · exact hacc y h1
        · simp at h

theorem foldBinop_clean {sk : Ctor → Nat → Bool} (st : PState) (hs : st.syntaxCheckOnly = false)
    (fs : List Ast) (l : Option Loc) (h : Clean sk (.node .BinOp fs l))
    (hf : sk .BinOp 2 = false) (ht : sk .Tuple 0 = false) :
    Clean sk (foldBinop st (.node .BinOp fs l)) := by
  unfold foldBinop
  simp only [hs, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i elts h3 h4 l' he
    cases he
    split
    · exact h
    · split
      · rename_i out hl
        refine Clean.node rfl fun i hi _ => ?_
        have he : astFields .JoinedStr = [0] := by decide +kernel
        rw [he] at hi
        simp only [List.mem_singleton] at hi
        subst hi
        have h2 : Clean sk (Ast.node .Tuple (.seq elts :: h3) h4) :=
          h.field (i := 2) (by decide +kernel) hf
        have h1 : Clean sk (.seq elts) := h2.field (i := 0) (by decide +kernel) ht
        exact Clean.seq (formatLoop_clean _ _ _ [] _ hl (fun _ hx => by cases hx)
          (fun _ hx => h1.elem hx))
      · exact h
  · exact h

theorem mappingKeys_getD (fut : Bool) (st : PState) (f : Nat) (c : Ctor) (fs : List Ast) (i : Nat)
    (h : skipWalked fut c i = false) :
    (mappingKeys st f c fs).getD i .null = fs.getD i .null := by
  unfold mappingKeys
  split
  · cases i with
    | zero => simp [skipWalked, skipNarrow, patSkip] at h
    | succ i => simp [List.getD_eq_getElem?_getD]
  · cases i with
    | zero => simp [skipWalked, skipNarrow, patSkip] at h
    | succ i => simp [List.getD_eq_getElem?_getD]
  · rfl

theorem skip_binop (fut : Bool) : skipWalked fut .BinOp 2 = false := by cases fut <;> rfl

theorem skip_tuple (fut : Bool) : skipWalked fut .Tuple 0 = false := by cases fut <;> rfl

theorem postFold_clean (fut : Bool) (st : PState) (f : Nat) (c : Ctor) (fs : List Ast)
    (l : Option Loc) (hs : st.syntaxCheckOnly = false)
    (h : ∀ i, i ∈ astFields c → skipWalked fut c i = false →
      Clean (skipWalked fut) (fs.getD i .null)) :
    Clean (skipWalked fut) (postFold st c (mappingKeys st f c fs) l) := by
  have h' : ∀ i, i ∈ astFields c → skipWalked fut c i = false →
      Clean (skipWalked fut) ((mappingKeys st f c fs).getD i .null) := by
    intro i hi hk
    rw [mappingKeys_getD fut st f c fs i hk]
    exact h i hi hk
  generalize mappingKeys st f c fs = fs' at h' ⊢
  unfold postFold
  split
  · exact foldBinop_clean st hs fs' l (Clean.node rfl h') (skip_binop fut) (skip_tuple fut)
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i id x y
      split
      · refine Clean.node rfl fun i hi _ => ?_
        have : astFields .Constant = [] := by decide +kernel
        rw [this] at hi
        cases hi
      · rename_i hne
        refine Clean.node ?_ h'
        unfold isDebugLoad
        simpa using hne
    · rename_i hn
      refine Clean.node ?_ h'
      unfold isDebugLoad
      split
      · rename_i hx
        cases hx
        exact (hn _ _ _ rfl).elim
      · rfl
  · rename_i h1 h2
    refine Clean.node ?_ h'
    unfold isDebugLoad
    split
    · rename_i hx
      cases hx
      exact (h2 rfl).elim
    · rfl

/-- The four mutually recursive functions, together. -/
def SFold (fut : Bool) (f : Nat) : Prop := ∀ (e : Ast) (st : PState),
  st.syntaxCheckOnly = false → st.futureAnnotations = fut →
  Keep st (fold f e st).2 ∧
    ((fold f e st).2.fuelOut = false → Clean (skipWalked fut) (fold f e st).1)

def SList (fut : Bool) (f : Nat) : Prop := ∀ (xs : List Ast) (st : PState),
  st.syntaxCheckOnly = false → st.futureAnnotations = fut →
  Keep st (foldList f xs st).2 ∧
    ((foldList f xs st).2.fuelOut = false → ∀ x, x ∈ (foldList f xs st).1 → Clean (skipWalked fut) x)

def SBody (fut : Bool) (f : Nat) : Prop := ∀ (xs : List Ast) (st : PState),
  st.syntaxCheckOnly = false → st.futureAnnotations = fut →
  Keep st (foldBody f xs st).2 ∧
    ((foldBody f xs st).2.fuelOut = false → ∀ x, x ∈ (foldBody f xs st).1 → Clean (skipWalked fut) x)

def SSteps (fut : Bool) (f : Nat) : Prop := ∀ (ss : List Step) (fs : List Ast) (st : PState),
  st.syntaxCheckOnly = false → st.futureAnnotations = fut →
  Keep st (runSteps f ss fs st).2 ∧
    ((runSteps f ss fs st).2.fuelOut = false →
      (∀ i, i ∈ stepIdx fut ss → Clean (skipWalked fut) ((runSteps f ss fs st).1.getD i .null)) ∧
      (∀ i, i ∉ stepIdx fut ss → (runSteps f ss fs st).1.getD i .null = fs.getD i .null))

theorem walk_zero (fut : Bool) : SFold fut 0 ∧ SList fut 0 ∧ SBody fut 0 ∧ SSteps fut 0 := by
  have k : ∀ st : PState, Keep st { st with fuelOut := true } := fun _ => ⟨rfl, rfl, fun _ => rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e st _ _
    simp only [fold]
    exact ⟨k st, fun h => by cases h⟩
  · intro xs st _ _
    simp only [foldList]
    exact ⟨k st, fun h => by cases h⟩
  · intro xs st _ _
    simp only [foldBody]
    exact ⟨k st, fun h => by cases h⟩
  · intro ss fs st _ _
    simp only [runSteps]
    exact ⟨k st, fun h => by cases h⟩

theorem hide_clean {sk : Ctor → Nat → Bool} (he : sk .Expr 0 = false) (xs : List Ast)
    (h : ∀ x, x ∈ xs → Clean sk x) : ∀ x, x ∈ hideDocstring xs → Clean sk x := by
  unfold hideDocstring
  split
  · rename_i v l rest
    intro x hx
    rcases List.mem_cons.mp hx with h1 | h1
    · subst h1
      have hv : Clean sk v := (h _ (List.mem_cons_self ..)).field (i := 0) (by decide +kernel) he
      refine Clean.node rfl fun i hi _ => ?_
      have e1 : astFields .Expr = [0] := by decide +kernel
      rw [e1] at hi
      simp only [List.mem_singleton] at hi
      subst hi
      refine Clean.node rfl fun i hi _ => ?_
      have e2 : astFields .JoinedStr = [0] := by decide +kernel
      rw [e2] at hi
      simp only [List.mem_singleton] at hi
      subst hi
      exact Clean.seq fun y hy => by
        have : y = v := by simpa using hy
        rw [this]
        exact hv
    · exact h x (List.mem_cons_of_mem _ h1)
  · exact h

theorem skip_expr (fut : Bool) : skipWalked fut .Expr 0 = false := by cases fut <;> rfl

theorem walk_succ {fut : Bool} {f : Nat} (hF : SFold fut f) (hL : SList fut f) (hB : SBody fut f)
    (hS : SSteps fut f) :
    SFold fut (f + 1) ∧ SList fut (f + 1) ∧ SBody fut (f + 1) ∧ SSteps fut (f + 1) := by
  have hL' : SList fut (f + 1) := by
    intro xs st h1 h2
    cases xs with
    | nil => exact ⟨by simp only [foldList]; exact Keep.refl st, by simp [foldList]⟩
    | cons x xs =>
      obtain ⟨k1, p1⟩ := hF x st h1 h2
      obtain ⟨k2, p2⟩ := hL xs (fold f x st).2 (k1.sc.trans h1) (k1.fa.trans h2)
      simp only [foldList]
      refine ⟨k1.trans k2, fun hf y hy => ?_⟩
      rcases List.mem_cons.mp hy with h3 | h3
      · rw [h3]
        exact p1 (k2.false_of hf)
      · exact p2 hf y h3
  refine ⟨?_, hL', ?_, ?_⟩
  · intro e st h1 h2
    cases e with
    | node c fs l =>
      rw [fold_node_eq]
      have k0 := keep_preVisit c l st
      obtain ⟨k1, post⟩ := hS (visits c) fs (preVisit c l st).2 (k0.sc.trans h1) (k0.fa.trans h2)
      generalize runSteps f (visits c) fs (preVisit c l st).2 = r at k1 post ⊢
      refine ⟨k0.trans k1, fun hf => ?_⟩
      obtain ⟨c1, _⟩ := post hf
      exact postFold_clean fut r.2 f c r.1 l (k1.sc.trans (k0.sc.trans h1))
        fun i hi hs => c1 i (visits_cover fut c i hi hs)
    | seq xs =>
      obtain ⟨k, p⟩ := hL xs st h1 h2
      have e : fold (f + 1) (.seq xs) st = (.seq (foldList f xs st).1, (foldList f xs st).2) := rfl
      rw [e]
      exact ⟨k, fun hf => Clean.seq (p hf)⟩
    | null => exact ⟨Keep.refl st, fun _ => clean_null _⟩
    | ident a => exact ⟨Keep.refl st, fun _ => Clean.leaf (fun _ _ _ h => by cases h) (fun _ h => by cases h)⟩
    | str a => exact ⟨Keep.refl st, fun _ => Clean.leaf (fun _ _ _ h => by cases h) (fun _ h => by cases h)⟩
    | int a => exact ⟨Keep.refl st, fun _ => Clean.leaf (fun _ _ _ h => by cases h) (fun _ h => by cases h)⟩
    | const a => exact ⟨Keep.refl st, fun _ => Clean.leaf (fun _ _ _ h => by cases h) (fun _ h => by cases h)⟩
    | tok a => exact ⟨Keep.refl st, fun _ => Clean.leaf (fun _ _ _ h => by cases h) (fun _ h => by cases h)⟩
  · intro xs st h1 h2
    obtain ⟨k, p⟩ := hL (if ((getDocString xs).isSome && decide (st.optimize ≥ 2)) = true
      then removeDocstring xs else xs) st h1 h2
    simp only [foldBody]
    generalize foldList f (if ((getDocString xs).isSome && decide (st.optimize ≥ 2)) = true
      then removeDocstring xs else xs) st = r at k p ⊢
    by_cases hc : ((!if ((getDocString xs).isSome && decide (st.optimize ≥ 2)) = true then false
        else (getDocString xs).isSome) && (getDocString r.1).isSome) = true
    · simp only [hc, ↓reduceIte]
      exact ⟨k, fun hf => hide_clean (skip_expr fut) r.1 (p hf)⟩
    · simp only [hc, ↓reduceIte]
      exact ⟨k, p⟩
  · intro ss fs st h1 h2
    cases ss with
    | nil =>
      simp only [runSteps]
      exact ⟨Keep.refl st, fun _ => ⟨fun _ h => (by cases h), fun _ _ => trivial⟩⟩
    | cons s rest =>
      rw [runSteps]
      cases s with
      | fld i =>
        dsimp only
        obtain ⟨k1, p1⟩ := hF (fs.getD i .null) st h1 h2
        obtain ⟨k2, p2⟩ := hS rest (fs.set i (fold f (fs.getD i .null) st).1)
          (fold f (fs.getD i .null) st).2 (k1.sc.trans h1) (k1.fa.trans h2)
        refine ⟨k1.trans k2, fun hf => ?_⟩
        obtain ⟨a, b⟩ := p2 hf
        exact steps_cons (p1 (k2.false_of hf)) a b
      | body i =>
        dsimp only
        split
        · rename_i xs _
          obtain ⟨k1, p1⟩ := hB xs st h1 h2
          obtain ⟨k2, p2⟩ := hS rest (fs.set i (.seq (foldBody f xs st).1)) (foldBody f xs st).2
            (k1.sc.trans h1) (k1.fa.trans h2)
          refine ⟨k1.trans k2, fun hf => ?_⟩
          obtain ⟨a, b⟩ := p2 hf
          exact steps_cons (Clean.seq (p1 (k2.false_of hf))) a b
        · obtain ⟨k1, p1⟩ := hF (fs.getD i .null) st h1 h2
          obtain ⟨k2, p2⟩ := hS rest (fs.set i (fold f (fs.getD i .null) st).1)
            (fold f (fs.getD i .null) st).2 (k1.sc.trans h1) (k1.fa.trans h2)
          refine ⟨k1.trans k2, fun hf => ?_⟩
          obtain ⟨a, b⟩ := p2 hf
          exact steps_cons (p1 (k2.false_of hf)) a b
      | ann i =>
        dsimp only
        split
        · rename_i h
          have hfut : fut = true := h2.symm.trans h
          have e : stepIdx fut (.ann i :: rest) = stepIdx fut rest := by simp [stepIdx, hfut]
          rw [e]
          exact hS rest fs st h1 h2
        · rename_i h
          have hfut : fut = false := by
            rw [← h2]
            simpa using h
          have e : stepIdx fut (.ann i :: rest) = i :: stepIdx fut rest := by simp [stepIdx, hfut]
          rw [e]
          obtain ⟨k1, p1⟩ := hF (fs.getD i .null) st h1 h2
          obtain ⟨k2, p2⟩ := hS rest (fs.set i (fold f (fs.getD i .null) st).1)
            (fold f (fs.getD i .null) st).2 (k1.sc.trans h1) (k1.fa.trans h2)
          refine ⟨k1.trans k2, fun hf => ?_⟩
          obtain ⟨a, b⟩ := p2 hf
          exact steps_cons (p1 (k2.false_of hf)) a b
      | push a b c =>
        obtain ⟨k, p⟩ := hS rest fs { st with cf := (a, b, c) :: st.cf } h1 h2
        exact ⟨⟨k.sc, k.fa, fun h => k.fu h⟩, p⟩
      | pop =>
        obtain ⟨k, p⟩ := hS rest fs { st with cf := st.cf.drop 1 } h1 h2
        exact ⟨⟨k.sc, k.fa, fun h => k.fu h⟩, p⟩

theorem walk_all (fut : Bool) (f : Nat) : SFold fut f ∧ SList fut f ∧ SBody fut f ∧ SSteps fut f := by
  induction f with
  | zero => exact walk_zero fut
  | succ f ih => exact walk_succ ih.1 ih.2.1 ih.2.2.1 ih.2.2.2

theorem foldReachesWalked_proven : FoldReachesWalked := by
  intro fuel st m h1
  obtain ⟨hF, hL, hB, _⟩ := walk_all st.futureAnnotations fuel
  unfold foldMod
  split
  · rename_i b rest l
    intro hf
    exact Clean.seq ((hB (seqL b) st h1 rfl).2 hf)
  · rename_i b l
    intro hf
    exact Clean.seq ((hL (seqL b) st h1 rfl).2 hf)
  · rename_i b l
    intro hf
    exact (hF b st h1 rfl).2 hf
  · rename_i h2 h3 h4
    intro _
    have e : modBody m = .null := by
      unfold modBody
      split
      · exact (h2 _ _ _ rfl).elim
      · exact (h3 _ _ rfl).elim
      · exact (h4 _ _ rfl).elim
      · rfl
    show Clean _ (modBody m)
    rw [e]
    exact clean_null _

/-! ### Docstrings -/

theorem runSteps_nil_val (f : Nat) (fs : List Ast) (s : PState) : (runSteps f [] fs s).1 = fs := by
  cases f <;> simp only [runSteps]

theorem fold_constant (f : Nat) (fs : List Ast) (l : Option Loc) (st : PState) :
    (fold f (.node .Constant fs l) st).1 = .node .Constant fs l := by
  cases f with
  | zero => simp only [fold]
  | succ f =>
    rw [fold_node_eq, show visits .Constant = [] from rfl]
    have hr := runSteps_nil_val f fs (preVisit .Constant l st).2
    generalize runSteps f [] fs (preVisit .Constant l st).2 = R at hr ⊢
    obtain ⟨x, s2⟩ := R
    dsimp only at hr ⊢
    subst hr
    rfl

theorem fold_doc_stmt (f : Nat) (s : List Nat) (k : List Ast) (l l2 : Option Loc) (st : PState) :
    (fold f (.node .Expr [.node .Constant (.const (.str s) :: k) l] l2) st).1 =
      .node .Expr [.node .Constant (.const (.str s) :: k) l] l2 := by
  cases f with
  | zero => simp only [fold]
  | succ f =>
    rw [fold_node_eq, show visits .Expr = [.fld 0] from rfl]
    have e : (runSteps f [.fld 0] [.node .Constant (.const (.str s) :: k) l] (preVisit .Expr l2 st).2).1
        = [.node .Constant (.const (.str s) :: k) l] := by
      cases f with
      | zero => simp only [runSteps]
      | succ f =>
        rw [runSteps]
        dsimp only
        rw [runSteps_nil_val, List.getD_cons_zero, fold_constant]
        rfl
    generalize runSteps f [.fld 0] [.node .Constant (.const (.str s) :: k) l]
      (preVisit .Expr l2 st).2 = R at e ⊢
    obtain ⟨x, s2⟩ := R
    dsimp only at e ⊢
    subst e
    rfl

theorem docString_shape {xs : List Ast} {s : List Nat} (h : getDocString xs = some s) :
    ∃ k l l2 rest, xs = .node .Expr [.node .Constant (.const (.str s) :: k) l] l2 :: rest := by
  unfold getDocString at h
  split at h
  · cases h
    exact ⟨_, _, _, _, rfl⟩
  · cases h

theorem hide_none {xs : List Ast} (h : (getDocString xs).isSome = true) :
    getDocString (hideDocstring xs) = none := by
  cases hd : getDocString xs with
  | none =>
    rw [hd] at h
    cases h
  | some s =>
    obtain ⟨k, l, l2, rest, rfl⟩ := docString_shape hd
    rfl

theorem foldBody_succ (f : Nat) (xs : List Ast) (st : PState) :
    foldBody (f + 1) xs st =
      if (!(if ((getDocString xs).isSome && decide (st.optimize ≥ 2)) = true then false
            else (getDocString xs).isSome)
          && (getDocString (foldList f (if ((getDocString xs).isSome && decide (st.optimize ≥ 2)) = true
              then removeDocstring xs else xs) st).1).isSome) = true
      then (hideDocstring (foldList f (if ((getDocString xs).isSome && decide (st.optimize ≥ 2)) = true
              then removeDocstring xs else xs) st).1,
            (foldList f (if ((getDocString xs).isSome && decide (st.optimize ≥ 2)) = true
              then removeDocstring xs else xs) st).2)
      else foldList f (if ((getDocString xs).isSome && decide (st.optimize ≥ 2)) = true
              then removeDocstring xs else xs) st := by
  simp only [foldBody]

theorem doc_hidden (r : List Ast × PState) :
    getDocString (if (!false && (getDocString r.1).isSome) = true
      then (hideDocstring r.1, r.2) else r).1 = none := by
  by_cases h : (getDocString r.1).isSome = true
  · simp only [Bool.not_false, Bool.true_and, h, ↓reduceIte]
    exact hide_none h
  · simp only [Bool.not_false, Bool.true_and, h, ↓reduceIte]
    simpa using h

/-- "Turn a constant folded string expression statement into a JoinedStr so that it is not
mistaken for a docstring": folding keeps a body's docstring and never makes one. With `optimize`
below 2 the docstring afterwards is the one before; at 2 and above there is none. -/
def FoldKeepsDocstring : Prop := ∀ (f : Nat) (st : PState) (xs : List Ast),
  (st.optimize < 2 → getDocString (foldBody (f + 1) xs st).1 = getDocString xs) ∧
  (st.optimize ≥ 2 → getDocString (foldBody (f + 1) xs st).1 = none)

theorem foldKeepsDocstring_proven : FoldKeepsDocstring := by
  intro f st xs
  constructor
  · intro hlt
    have hn : decide (st.optimize ≥ 2) = false := by
      simp only [decide_eq_false_iff_not]
      omega
    rw [foldBody_succ]
    simp only [hn, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    cases hd : getDocString xs with
    | none =>
      simp only [Option.isSome_none]
      exact doc_hidden (foldList f xs st)
    | some s =>
      simp only [Option.isSome_some, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨k, l, l2, rest, rfl⟩ := docString_shape hd
      cases f with
      | zero =>
        simp only [foldList]
        exact hd
      | succ f =>
        simp only [foldList, fold_doc_stmt]
        exact hd
  · intro hge
    have hn : decide (st.optimize ≥ 2) = true := by simpa using hge
    rw [foldBody_succ]
    simp only [hn, Bool.and_true]
    cases hd : (getDocString xs).isSome with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact doc_hidden (foldList f xs st)
    | true =>
      simp only [↓reduceIte]
      exact doc_hidden (foldList f (removeDocstring xs) st)

end PyLean.PyGrammar.Check
