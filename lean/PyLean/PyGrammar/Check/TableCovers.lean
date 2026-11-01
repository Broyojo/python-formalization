import PyLean.PyGrammar.Check.Rejects

/-!
`ValidateRejects` is only as strong as the child lists of its table: a child missing from a row is a
child nothing is claimed about. `TableCovers` checks those lists against `Ctor.fields`, which is
generated from `Parser/Python.asdl` and not written with the table in mind: every present field of a
tree-valued ASDL type is listed, with exactly one exception, `NamedExpr.target`, which `validate_expr`
does not visit (`pygrammar-check-namedexpr-target`).

`alias` is left out of `treeBase` because it holds only identifiers. The positions a row gives its
children are not compared with the ASDL here, only that the child is listed; `exprHead` and the
`Pos` of each row are what the review of the table reads.
-/

namespace PyLean.PyGrammar.Check

open PyLean

/-- ASDL types whose values a validator could visit. -/
def treeBase : FieldBase → Bool
  | .stmt_ | .expr_ | .comprehension_ | .excepthandler_ | .arguments_ | .arg_ | .keyword_
  | .withitem_ | .match_case_ | .pattern_ | .type_param_ => true
  | _ => false

/-- The children of a node, read from the ASDL alone. -/
def fieldKids (c : Ctor) (fs : List Ast) : List Ast :=
  (c.fields.zip fs).flatMap fun p =>
    if treeBase p.1.2.1 then
      match p.1.2.2 with
      | .seq | .optSeq => seqL p.2
      | _ => [p.2]
    else []

/-- The position a node of an ASDL type stands in. -/
def posOf : FieldBase → Option Pos
  | .mod_ => some .module
  | .stmt_ => some .stmt
  | .expr_ => some E
  | .pattern_ => some (.pat true)
  | .comprehension_ => some .comp
  | .excepthandler_ => some (.handler true)
  | .arguments_ => some .arguments
  | .arg_ => some .arg
  | .keyword_ => some .kw
  | .withitem_ => some .item
  | .match_case_ => some .case_
  | .type_param_ => some .tparam
  | _ => none

/-- For a node of the right arity, each present child the ASDL gives it is in its row of `spec`,
except the target of a `NamedExpr`. The arity is a type invariant: `obj2ast` builds no other node. -/
def TableCovers : Prop :=
  ∀ (c : Ctor) (fs : List Ast) (l : Option Loc) (b : FieldBase) (p : Pos),
    c.asdlType? = some b → posOf b = some p → fs.length = c.fields.length →
    ∀ x ∈ fieldKids c fs, x ≠ .null →
      x ∈ (spec p c fs l).2.map Prod.snd ∨ (c = .NamedExpr ∧ fs.head? = some x)

theorem map_snd_elts (p : Pos) (v : Ast) : (elts p v).map Prod.snd = seqL v := by
  simp [elts, Function.comp_def]

theorem len_succ {fs : List Ast} {n : Nat} (h : fs.length = n + 1) :
    ∃ a r, fs = a :: r ∧ r.length = n := by
  cases fs with
  | nil => simp at h
  | cons a r => exact ⟨a, r, rfl, by simpa using h⟩

/-- One constructor's row covers its ASDL children. -/
class Cov (c : Ctor) (p : Pos) : Prop where
  cov : ∀ (fs : List Ast) (l : Option Loc), fs.length = c.fields.length →
    ∀ x ∈ fieldKids c fs, x ≠ .null →
      x ∈ (spec p c fs l).2.map Prod.snd ∨ (c = .NamedExpr ∧ fs.head? = some x)

macro "cov" : tactic => `(tactic| (
  intro fs l hlen x hx hn
  have hnull : isNull x = false := by
    cases x <;> simp_all [isNull]
  unfold Ctor.fields at hlen
  dsimp only at hlen
  simp only [List.length_cons, List.length_nil] at hlen
  repeat
    (obtain ⟨a, r, e, h'⟩ := len_succ hlen
     subst e
     clear hlen
     have hlen := h'
     clear h')
  have e := List.eq_nil_of_length_eq_zero hlen
  subst e
  unfold fieldKids Ctor.fields at hx
  dsimp only at hx
  simp [treeBase] at hx
  all_goals unfold spec
  all_goals dsimp only
  all_goals try unfold modSpec
  all_goals try unfold exprBody
  all_goals try unfold stmtSpec
  all_goals try unfold patSpec
  all_goals try unfold tparamSpec
  all_goals try dsimp only
  all_goals simp [compSpec, kwSpec, argSpec, optArgSpec, argumentsSpec, itemSpec, caseSpec,
    handlerSpec, trySpec, map_snd_elts, List.map_append]
  all_goals repeat' (refine Or.elim hx (fun hx => ?_) (fun hx => ?_))
  all_goals first
    | (subst hx
       simp [hnull])
    | simp [hx]))

instance : Cov .Module .module := ⟨by cov⟩
instance : Cov .Interactive .module := ⟨by cov⟩
instance : Cov .Expression .module := ⟨by cov⟩
instance : Cov .FunctionType .module := ⟨by cov⟩
instance : Cov .FunctionDef .stmt := ⟨by cov⟩
instance : Cov .AsyncFunctionDef .stmt := ⟨by cov⟩
instance : Cov .ClassDef .stmt := ⟨by cov⟩
instance : Cov .Return .stmt := ⟨by cov⟩
instance : Cov .Delete .stmt := ⟨by cov⟩
instance : Cov .Assign .stmt := ⟨by cov⟩
instance : Cov .TypeAlias .stmt := ⟨by cov⟩
instance : Cov .AugAssign .stmt := ⟨by cov⟩
instance : Cov .AnnAssign .stmt := ⟨by cov⟩
instance : Cov .For .stmt := ⟨by cov⟩
instance : Cov .AsyncFor .stmt := ⟨by cov⟩
instance : Cov .While .stmt := ⟨by cov⟩
instance : Cov .If .stmt := ⟨by cov⟩
instance : Cov .With .stmt := ⟨by cov⟩
instance : Cov .AsyncWith .stmt := ⟨by cov⟩
instance : Cov .Match .stmt := ⟨by cov⟩
instance : Cov .Raise .stmt := ⟨by cov⟩
instance : Cov .Try .stmt := ⟨by cov⟩
instance : Cov .TryStar .stmt := ⟨by cov⟩
instance : Cov .Assert .stmt := ⟨by cov⟩
instance : Cov .Import .stmt := ⟨by cov⟩
instance : Cov .ImportFrom .stmt := ⟨by cov⟩
instance : Cov .Global .stmt := ⟨by cov⟩
instance : Cov .Nonlocal .stmt := ⟨by cov⟩
instance : Cov .Expr .stmt := ⟨by cov⟩
instance : Cov .Pass .stmt := ⟨by cov⟩
instance : Cov .Break .stmt := ⟨by cov⟩
instance : Cov .Continue .stmt := ⟨by cov⟩
instance : Cov .BoolOp E := ⟨by cov⟩
instance : Cov .NamedExpr E := ⟨by cov⟩
instance : Cov .BinOp E := ⟨by cov⟩
instance : Cov .UnaryOp E := ⟨by cov⟩
instance : Cov .Lambda E := ⟨by cov⟩
instance : Cov .IfExp E := ⟨by cov⟩
instance : Cov .Dict E := ⟨by cov⟩
instance : Cov .Set E := ⟨by cov⟩
instance : Cov .ListComp E := ⟨by cov⟩
instance : Cov .SetComp E := ⟨by cov⟩
instance : Cov .DictComp E := ⟨by cov⟩
instance : Cov .GeneratorExp E := ⟨by cov⟩
instance : Cov .Await E := ⟨by cov⟩
instance : Cov .Yield E := ⟨by cov⟩
instance : Cov .YieldFrom E := ⟨by cov⟩
instance : Cov .Compare E := ⟨by cov⟩
instance : Cov .Call E := ⟨by cov⟩
instance : Cov .FormattedValue E := ⟨by cov⟩
instance : Cov .Interpolation E := ⟨by cov⟩
instance : Cov .JoinedStr E := ⟨by cov⟩
instance : Cov .TemplateStr E := ⟨by cov⟩
instance : Cov .Constant E := ⟨by cov⟩
instance : Cov .Attribute E := ⟨by cov⟩
instance : Cov .Subscript E := ⟨by cov⟩
instance : Cov .Starred E := ⟨by cov⟩
instance : Cov .Name E := ⟨by cov⟩
instance : Cov .List E := ⟨by cov⟩
instance : Cov .Tuple E := ⟨by cov⟩
instance : Cov .Slice E := ⟨by cov⟩
instance : Cov .MatchValue (.pat true) := ⟨by cov⟩
instance : Cov .MatchSingleton (.pat true) := ⟨by cov⟩
instance : Cov .MatchSequence (.pat true) := ⟨by cov⟩
instance : Cov .MatchMapping (.pat true) := ⟨by cov⟩
instance : Cov .MatchClass (.pat true) := ⟨by cov⟩
instance : Cov .MatchStar (.pat true) := ⟨by cov⟩
instance : Cov .MatchAs (.pat true) := ⟨by cov⟩
instance : Cov .MatchOr (.pat true) := ⟨by cov⟩
instance : Cov .TypeVar .tparam := ⟨by cov⟩
instance : Cov .ParamSpec .tparam := ⟨by cov⟩
instance : Cov .TypeVarTuple .tparam := ⟨by cov⟩
instance : Cov .comprehension_ .comp := ⟨by cov⟩
instance : Cov .ExceptHandler (.handler true) := ⟨by cov⟩
instance : Cov .arguments_ .arguments := ⟨by cov⟩
instance : Cov .arg_ .arg := ⟨by cov⟩
instance : Cov .keyword_ .kw := ⟨by cov⟩
instance : Cov .withitem_ .item := ⟨by cov⟩
instance : Cov .match_case_ .case_ := ⟨by cov⟩

theorem tableCovers_proven : TableCovers := by
  intro c fs l b p hb hp
  have k : Cov c p := by
    unfold Ctor.asdlType? at hb
    cases c <;> dsimp only at hb <;> cases hb <;> unfold posOf at hp <;> dsimp only at hp <;>
      cases hp <;> exact inferInstance
  exact k.cov fs l

end PyLean.PyGrammar.Check
