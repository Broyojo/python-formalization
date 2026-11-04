import PyLean.PyGrammar.Check.Rejects
import PyLean.PyGrammar.Peg.Actions

/-!
Three pieces of CPython decide what an assignment target is, and they are written separately.
`_PyPegen_get_invalid_target` picks the subexpression an error message blames.
`_PyPegen_set_expr_context` rewrites a target parsed as a load. `validate_expr` checks the result.

`TargetValidates` says they agree: what the first finds nothing wrong with, the second turns into a
tree that passes the context switch of the third, at every position of the target. Alone that would
hold for a first function that blames everything, so `LegalTargetAccepted` says it does not: a
target built only from names, attributes, subscripts, stars, tuples and lists gets `NULL`.
`SetContextLast` and `SetContextRestores` say what the rewrite computes: the comment on it promises
"an `expr_ty` equivalent to `expr` but with `ctx` as context", so only the last context counts, and
a tree that already has a context comes back unchanged from a change and a change back.

Only `LegalTargetAccepted` has a fuel hypothesis, and it is the tree's height, which the parser's
`MAXSTACK` keeps far below the 100000 of the call sites. `invalidTarget` at fuel 0 returns its
argument, so a `NULL` answer means the fuel sufficed, and `setExprContext` at fuel 0 returns its
argument unchanged.
-/

namespace PyLean.PyGrammar.Check

open PyLean PyLean.PyGrammar.Peg

/-- The shape `obj2ast` and the parser give the six nodes with a `ctx` field: the right arity, an
actual sequence of elements, and no `NULL` element. A `Name` holds no keyword, since `None`, `True`
and `False` are keyword tokens and never `NAME`, which is a type invariant of parser output. Any
other node is unconstrained. -/
inductive TShape : Ast → Prop
  | name {i x : Ast} {l : Option Loc} : validateName i = ok1 → TShape (.node .Name [i, x] l)
  | attr {v a x : Ast} {l : Option Loc} : TShape (.node .Attribute [v, a, x] l)
  | sub {v s x : Ast} {l : Option Loc} : TShape (.node .Subscript [v, s, x] l)
  | star {v x : Ast} {l : Option Loc} : TShape v → TShape (.node .Starred [v, x] l)
  | tuple {xs : List Ast} {x : Ast} {l : Option Loc} : (∀ y ∈ xs, TShape y) →
      TShape (.node .Tuple [.seq xs, x] l)
  | list {xs : List Ast} {x : Ast} {l : Option Loc} : (∀ y ∈ xs, TShape y) →
      TShape (.node .List [.seq xs, x] l)
  | other {c : Ctor} {fs : List Ast} {l : Option Loc} : c ≠ .Name → c ≠ .Attribute →
      c ≠ .Subscript → c ≠ .Starred → c ≠ .Tuple → c ≠ .List → TShape (.node c fs l)

/-- The first switch of `validate_expr` gives this node the context `ctx`, and so does it for every
position below it that the switch recurses through. -/
inductive Heads (ctx : Ctor) : Ast → Prop
  | name {i x : Ast} {l : Option Loc} : exprCtx .Name [i, x] ctx = .ok (some ctx) →
      Heads ctx (.node .Name [i, x] l)
  | attr {v a x : Ast} {l : Option Loc} : exprCtx .Attribute [v, a, x] ctx = .ok (some ctx) →
      Heads ctx (.node .Attribute [v, a, x] l)
  | sub {v s x : Ast} {l : Option Loc} : exprCtx .Subscript [v, s, x] ctx = .ok (some ctx) →
      Heads ctx (.node .Subscript [v, s, x] l)
  | star {v x : Ast} {l : Option Loc} : exprCtx .Starred [v, x] ctx = .ok (some ctx) →
      Heads ctx v → Heads ctx (.node .Starred [v, x] l)
  | tuple {xs : List Ast} {x : Ast} {l : Option Loc} :
      exprCtx .Tuple [.seq xs, x] ctx = .ok (some ctx) → (∀ y ∈ xs, Heads ctx y) →
      Heads ctx (.node .Tuple [.seq xs, x] l)
  | list {xs : List Ast} {x : Ast} {l : Option Loc} :
      exprCtx .List [.seq xs, x] ctx = .ok (some ctx) → (∀ y ∈ xs, Heads ctx y) →
      Heads ctx (.node .List [.seq xs, x] l)

theorem visit_null {g : Ast → Ast} {p : Ast → Bool} {xs : List Ast}
    (hp : ∀ x, x ≠ .null → p x = true) (hq : p .null = false)
    (h : ((xs.map g).find? p).getD .null = .null) : ∀ y ∈ xs, g y = .null := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.find?_cons] at h
    by_cases hg : g a = .null
    · rw [hg, hq] at h
      intro y hy
      rcases List.mem_cons.1 hy with e | e
      · exact e ▸ hg
      · exact ih h y e
    · rw [hp _ hg] at h
      exact (hg h).elim

/-- A node with no `ctx` field is never a good target, whatever its fields, unless the caller is
parsing a `for`. -/
theorem invalid_other {k f : Nat} {c : Ctor} {fs : List Ast} {l : Option Loc} (hk : k ≠ 2)
    (h1 : c ≠ .Name) (h2 : c ≠ .Attribute) (h3 : c ≠ .Subscript) (h4 : c ≠ .Starred)
    (h5 : c ≠ .Tuple) (h6 : c ≠ .List) : invalidTarget k (f + 1) (.node c fs l) ≠ .null := by
  intro h
  generalize he : Ast.node c fs l = e at h
  rw [invalidTarget.eq_def] at h
  simp only [] at h
  split at h
  all_goals first
    | (cases he
       done)
    | (subst h
       cases he
       done)
    | (cases he
       first
         | exact h1 rfl
         | exact h2 rfl
         | exact h3 rfl
         | exact h4 rfl
         | exact h5 rfl
         | exact h6 rfl)
    | (cases he
       simp [hk] at h)

theorem target_heads {k : Nat} (hk : k ≠ 2) (cx : Ast) :
    ∀ (f : Nat) (e : Ast), TShape e → invalidTarget k f e = .null →
      Heads (ctxOfAst cx) (setExprContext cx f e) := by
  intro f
  induction f with
  | zero =>
    intro e hs h
    rw [invalidTarget.eq_def] at h
    simp only [] at h
    subst h
    cases hs
  | succ f ih =>
    intro e hs h
    cases hs with
    | name hv =>
      rw [setExprContext.eq_def]
      simp only []
      refine Heads.name ?_
      unfold exprCtx
      simp only [show validateName _ = ok1 from hv, ok1]
    | attr =>
      rw [setExprContext.eq_def]
      simp only []
      exact Heads.attr rfl
    | sub =>
      rw [setExprContext.eq_def]
      simp only []
      exact Heads.sub rfl
    | star hv =>
      rw [invalidTarget.eq_def] at h
      simp only [] at h
      split at h
      · cases h
      · rw [setExprContext.eq_def]
        simp only []
        exact Heads.star rfl (ih _ hv h)
    | tuple hy =>
      rw [invalidTarget.eq_def] at h
      simp only [seqOf] at h
      have hn := visit_null (fun x hx => by cases x <;> first | rfl | exact absurd rfl hx) rfl h
      rw [setExprContext.eq_def]
      simp only [seqOf]
      refine Heads.tuple rfl fun y hm => ?_
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hm
      exact ih w (hy w hw) (hn w hw)
    | list hy =>
      rw [invalidTarget.eq_def] at h
      simp only [seqOf] at h
      have hn := visit_null (fun x hx => by cases x <;> first | rfl | exact absurd rfl hx) rfl h
      rw [setExprContext.eq_def]
      simp only [seqOf]
      refine Heads.list rfl fun y hm => ?_
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hm
      exact ih w (hy w hw) (hn w hw)
    | other h1 h2 h3 h4 h5 h6 => exact (invalid_other hk h1 h2 h3 h4 h5 h6 h).elim

/-- A target `_PyPegen_get_invalid_target` accepts as `STAR_TARGETS` or `DEL_TARGETS` becomes, under
`_PyPegen_set_expr_context`, a tree whose every target position passes the context check of
`validate_expr`. `FOR_TARGETS` is excluded because it looks through `in`, which the rewrite does not.
`TShape` is the documented type invariant. -/
def TargetValidates : Prop := ∀ (k f : Nat) (cx e : Ast), k ≠ 2 → TShape e →
  invalidTarget k f e = .null → Heads (ctxOfAst cx) (setExprContext cx f e)

theorem targetValidates_proven : TargetValidates :=
  fun k f cx e hk hs h => target_heads hk cx f e hs h

/-- Only the last context counts. -/
def SetContextLast : Prop := ∀ (c d : Ast) (f : Nat) (e : Ast),
  setExprContext c f (setExprContext d f e) = setExprContext c f e

theorem setContextLast_proven : SetContextLast := by
  intro c d f
  induction f with
  | zero =>
    intro e
    rfl
  | succ f ih =>
    intro e
    have hd := setExprContext.eq_def d (f + 1) e
    simp only [] at hd
    split at hd
    all_goals rw [hd]
    all_goals first
      | rfl
      | simp only [setExprContext, seqOf, List.map_map, Function.comp_def, ih]

/-- A tree whose target spine already has the context `cx`. -/
inductive Spine (cx : Ast) : Ast → Prop
  | name {i : Ast} {l : Option Loc} : Spine cx (.node .Name [i, cx] l)
  | attr {v a : Ast} {l : Option Loc} : Spine cx (.node .Attribute [v, a, cx] l)
  | sub {v s : Ast} {l : Option Loc} : Spine cx (.node .Subscript [v, s, cx] l)
  | star {v : Ast} {l : Option Loc} : Spine cx v → Spine cx (.node .Starred [v, cx] l)
  | tuple {xs : List Ast} {l : Option Loc} : (∀ y ∈ xs, Spine cx y) →
      Spine cx (.node .Tuple [.seq xs, cx] l)
  | list {xs : List Ast} {l : Option Loc} : (∀ y ∈ xs, Spine cx y) →
      Spine cx (.node .List [.seq xs, cx] l)
  | other {c : Ctor} {fs : List Ast} {l : Option Loc} : c ≠ .Name → c ≠ .Attribute →
      c ≠ .Subscript → c ≠ .Starred → c ≠ .Tuple → c ≠ .List → Spine cx (.node c fs l)

theorem set_other {cx : Ast} {f : Nat} {c : Ctor} {fs : List Ast} {l : Option Loc}
    (h1 : c ≠ .Name) (h2 : c ≠ .Attribute) (h3 : c ≠ .Subscript) (h4 : c ≠ .Starred)
    (h5 : c ≠ .Tuple) (h6 : c ≠ .List) :
    setExprContext cx (f + 1) (.node c fs l) = .node c fs l := by
  generalize he : Ast.node c fs l = e
  rw [setExprContext.eq_def]
  simp only []
  split
  all_goals first
    | rfl
    | (cases he
       first
         | exact (h1 rfl).elim
         | exact (h2 rfl).elim
         | exact (h3 rfl).elim
         | exact (h4 rfl).elim
         | exact (h5 rfl).elim
         | exact (h6 rfl).elim)

theorem map_self {g : Ast → Ast} {xs : List Ast} (h : ∀ y ∈ xs, g y = y) : xs.map g = xs := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons]
    rw [h a (List.mem_cons_self ..), ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem set_spine {cx : Ast} : ∀ (f : Nat) (e : Ast), Spine cx e → setExprContext cx f e = e := by
  intro f
  induction f with
  | zero =>
    intro e _
    rfl
  | succ f ih =>
    intro e hs
    cases hs with
    | name => rfl
    | attr => rfl
    | sub => rfl
    | star hv => simp only [setExprContext, ih _ hv]
    | tuple hy => simp only [setExprContext, seqOf, map_self fun y hm => ih y (hy y hm)]
    | list hy => simp only [setExprContext, seqOf, map_self fun y hm => ih y (hy y hm)]
    | other h1 h2 h3 h4 h5 h6 => exact set_other h1 h2 h3 h4 h5 h6

/-- Changing the context of a tree that has `cx` on its target spine, and changing it back, gives
the tree: nothing but the context moved. `Spine` is a statement about the input, not a restriction
of it: any tree has some context there, or holds no `ctx` field. -/
def SetContextRestores : Prop := ∀ (c cx e : Ast) (f : Nat), Spine cx e →
  setExprContext cx f (setExprContext c f e) = e

theorem setContextRestores_proven : SetContextRestores := by
  intro c cx e f hs
  rw [setContextLast_proven]
  exact set_spine f e hs

/-- A target of height `n` built only from the forms that hold one. -/
inductive Legal : Nat → Ast → Prop
  | name {n : Nat} {fs : List Ast} {l : Option Loc} : Legal n (.node .Name fs l)
  | attr {n : Nat} {fs : List Ast} {l : Option Loc} : Legal n (.node .Attribute fs l)
  | sub {n : Nat} {fs : List Ast} {l : Option Loc} : Legal n (.node .Subscript fs l)
  | star {n : Nat} {v : Ast} {fs : List Ast} {l : Option Loc} : Legal n v →
      Legal (n + 1) (.node .Starred (v :: fs) l)
  | tuple {n : Nat} {xs : List Ast} {fs : List Ast} {l : Option Loc} : (∀ y ∈ xs, Legal n y) →
      Legal (n + 1) (.node .Tuple (.seq xs :: fs) l)
  | list {n : Nat} {xs : List Ast} {fs : List Ast} {l : Option Loc} : (∀ y ∈ xs, Legal n y) →
      Legal (n + 1) (.node .List (.seq xs :: fs) l)

theorem visit_all_null {g : Ast → Ast} {p : Ast → Bool} {xs : List Ast}
    (hq : p .null = false) (h : ∀ y ∈ xs, g y = .null) :
    ((xs.map g).find? p).getD .null = .null := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, List.find?_cons]
    rw [h a (List.mem_cons_self ..), hq]
    exact ih fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem legal_null : ∀ (f n : Nat) (e : Ast), n < f → Legal n e → invalidTarget 0 f e = .null := by
  intro f
  induction f with
  | zero =>
    intro n e hn _
    omega
  | succ f ih =>
    intro n e hn hl
    cases hl with
    | name => rfl
    | attr => rfl
    | sub => rfl
    | star hv =>
      rw [invalidTarget.eq_def]
      simp only []
      exact ih _ _ (by omega) hv
    | tuple hy =>
      rw [invalidTarget.eq_def]
      simp only [seqOf]
      exact visit_all_null rfl fun y hm => ih _ _ (by omega) (hy y hm)
    | list hy =>
      rw [invalidTarget.eq_def]
      simp only [seqOf]
      exact visit_all_null rfl fun y hm => ih _ _ (by omega) (hy y hm)

/-- `_PyPegen_get_invalid_target` blames nothing in a legal `STAR_TARGETS` target, given fuel above
its height. -/
def LegalTargetAccepted : Prop := ∀ (f n : Nat) (e : Ast), n < f → Legal n e →
  invalidTarget 0 f e = .null

theorem legalTargetAccepted_proven : LegalTargetAccepted := legal_null

/-! ### What the rewrite computes, and what the blame picks -/

/-- The six node shapes `_PyPegen_set_expr_context` rewrites, `Parser/action_helpers.c:325-345`;
every other expression is returned as is (`default: new = expr;`). -/
def ctxShape : Ast → Bool
  | .node .Name [_, _] _ | .node .Tuple [_, _] _ | .node .List [_, _] _
  | .node .Subscript [_, _, _] _ | .node .Attribute [_, _, _] _ | .node .Starred [_, _] _ => true
  | _ => false

/-- `e'` is "an `expr_ty` equivalent to `expr` but with `ctx` as context" (the comment on
`_PyPegen_set_expr_context`, `Parser/action_helpers.c:318`): every position of the target spine gets
the context `cx`, and nothing else changes. A `Name` keeps its id (`_set_name_context`, `:269-272`),
a `Subscript` its value and slice (`:295-299`), an `Attribute` its value and attr (`:302-306`), and
every node its location (`EXTRA_EXPR(e, e)`); a `Starred` has its value rewritten (`:309-316`), and a
`Tuple` or `List` its elements, each in place and in order (`_set_seq_context`, `:246-266`). The
value of a `Subscript` or `Attribute` is not on the spine and keeps its own context. `n` bounds the
nesting of stars, tuples and lists. -/
inductive Recontext (cx : Ast) : Nat → Ast → Ast → Prop
  | name {n : Nat} {i x : Ast} {l : Option Loc} :
      Recontext cx n (.node .Name [i, x] l) (.node .Name [i, cx] l)
  | attr {n : Nat} {v a x : Ast} {l : Option Loc} :
      Recontext cx n (.node .Attribute [v, a, x] l) (.node .Attribute [v, a, cx] l)
  | sub {n : Nat} {v s x : Ast} {l : Option Loc} :
      Recontext cx n (.node .Subscript [v, s, x] l) (.node .Subscript [v, s, cx] l)
  | star {n : Nat} {v v' x : Ast} {l : Option Loc} : Recontext cx n v v' →
      Recontext cx (n + 1) (.node .Starred [v, x] l) (.node .Starred [v', cx] l)
  | tuple {n : Nat} {elts x : Ast} {ys : List Ast} {l : Option Loc} :
      (seqOf elts).length = ys.length → (∀ q ∈ (seqOf elts).zip ys, Recontext cx n q.1 q.2) →
      Recontext cx (n + 1) (.node .Tuple [elts, x] l) (.node .Tuple [.seq ys, cx] l)
  | list {n : Nat} {elts x : Ast} {ys : List Ast} {l : Option Loc} :
      (seqOf elts).length = ys.length → (∀ q ∈ (seqOf elts).zip ys, Recontext cx n q.1 q.2) →
      Recontext cx (n + 1) (.node .List [elts, x] l) (.node .List [.seq ys, cx] l)
  | other {n : Nat} {e : Ast} : ctxShape e = false → Recontext cx n e e

theorem map_zip_eq {g : Ast → Ast} : ∀ {xs ys : List Ast}, xs.length = ys.length →
    (∀ q ∈ xs.zip ys, g q.1 = q.2) → xs.map g = ys
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: xs, y :: ys, h, hq => by
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons, forall_eq_or_imp] at hq ⊢
    rw [hq.1, map_zip_eq (by simpa using h) hq.2]

theorem set_noShape {cx : Ast} {f : Nat} {e : Ast} (h : ctxShape e = false) :
    setExprContext cx (f + 1) e = e := by
  rw [setExprContext.eq_def]
  simp only []
  split <;> simp_all [ctxShape]

/-- `_PyPegen_set_expr_context` computes exactly `Recontext`: the result is the input with `cx` on
the target spine and every id, attr, value, slice, element and location kept. The fuel is above the
nesting, as the parser's `MAXSTACK` keeps it below the 100000 of the call site. -/
def SetContextExact : Prop := ∀ (cx : Ast) (n f : Nat) (e e' : Ast), n < f →
  Recontext cx n e e' → setExprContext cx f e = e'

theorem setContextExact_proven : SetContextExact := by
  intro cx n f
  induction f generalizing n with
  | zero => intro e e' h; omega
  | succ f ih =>
    intro e e' hn hr
    cases hr with
    | name => rfl
    | attr => rfl
    | sub => rfl
    | star hv => simp only [setExprContext, ih _ _ _ (by omega) hv]
    | tuple hl hq =>
      simp only [setExprContext]
      rw [map_zip_eq hl fun q hm => ih _ _ _ (by omega) (hq q hm)]
    | list hl hq =>
      simp only [setExprContext]
      rw [map_zip_eq hl fun q hm => ih _ _ _ (by omega) (hq q hm)]
    | other h => exact set_noShape h

/-- The forms `_PyPegen_get_invalid_target` looks into or accepts, `Parser/action_helpers.c:1238-1264`;
any other expression is its own answer (`default: return e;`). -/
def blameForm : Ast → Bool
  | .null | .node .List (_ :: _) _ | .node .Tuple (_ :: _) _ | .node .Starred (_ :: _) _
  | .node .Compare (_ :: _ :: _) _ | .node .Name _ _ | .node .Subscript _ _
  | .node .Attribute _ _ => true
  | _ => false

/-- The first comparison operator is `in`. -/
def firstOpIn (ops : Ast) : Prop := ∃ fs l rest, seqOf ops = .node .In fs l :: rest

/-- Every subexpression of a target that cannot be assigned to (`k` 0, `STAR_TARGETS`), deleted
(1, `DEL_TARGETS`) or bound by `for` (2, `FOR_TARGETS`), left to right. Names, attributes and
subscripts are good; a tuple or list is as good as its elements, "the only ones that can contain valid
names in targets when they are parsed as expressions" (`:1232-1236`); a star is bad under `del` and
otherwise as good as its value; a comparison is bad, except that for `for` "the `a in b` in
`for a in b` gets parsed as a comparison" (`:1250-1252`), so a comparison whose first operator is
`in` is as good as its left side, and any other comparison is not blamed at all; every other
expression is bad. `n` bounds the nesting. -/
inductive Offenders (k : Nat) : Nat → Ast → List Ast → Prop
  | null {n : Nat} : Offenders k n .null []
  | name {n : Nat} {fs : List Ast} {l : Option Loc} : Offenders k n (.node .Name fs l) []
  | attr {n : Nat} {fs : List Ast} {l : Option Loc} : Offenders k n (.node .Attribute fs l) []
  | sub {n : Nat} {fs : List Ast} {l : Option Loc} : Offenders k n (.node .Subscript fs l) []
  | tuple {n : Nat} {elts : Ast} {fs : List Ast} {l : Option Loc} {oss : List (List Ast)} :
      (seqOf elts).length = oss.length → (∀ q ∈ (seqOf elts).zip oss, Offenders k n q.1 q.2) →
      Offenders k (n + 1) (.node .Tuple (elts :: fs) l) oss.flatten
  | list {n : Nat} {elts : Ast} {fs : List Ast} {l : Option Loc} {oss : List (List Ast)} :
      (seqOf elts).length = oss.length → (∀ q ∈ (seqOf elts).zip oss, Offenders k n q.1 q.2) →
      Offenders k (n + 1) (.node .List (elts :: fs) l) oss.flatten
  | starDel {n : Nat} {v : Ast} {fs : List Ast} {l : Option Loc} : k = 1 →
      Offenders k n (.node .Starred (v :: fs) l) [.node .Starred (v :: fs) l]
  | star {n : Nat} {v : Ast} {fs : List Ast} {l : Option Loc} {os : List Ast} : k ≠ 1 →
      Offenders k n v os → Offenders k (n + 1) (.node .Starred (v :: fs) l) os
  | cmp {n : Nat} {left ops : Ast} {fs : List Ast} {l : Option Loc} : k ≠ 2 →
      Offenders k n (.node .Compare (left :: ops :: fs) l) [.node .Compare (left :: ops :: fs) l]
  | cmpIn {n : Nat} {left ops : Ast} {fs : List Ast} {l : Option Loc} {os : List Ast} : k = 2 →
      firstOpIn ops → Offenders k n left os →
      Offenders k (n + 1) (.node .Compare (left :: ops :: fs) l) os
  | cmpOther {n : Nat} {left ops : Ast} {fs : List Ast} {l : Option Loc} : k = 2 →
      ¬ firstOpIn ops → Offenders k n (.node .Compare (left :: ops :: fs) l) []
  | other {n : Nat} {e : Ast} : blameForm e = false → Offenders k n e [e]

theorem offenders_nonnull {k n : Nat} {e : Ast} {os : List Ast} (h : Offenders k n e os) :
    ∀ o ∈ os, o ≠ .null := by
  induction h with
  | null | name | attr | sub | cmpOther => simp
  | @tuple _ elts _ _ oss hl _ ih | @list _ elts _ _ oss hl _ ih =>
    intro o ho
    obtain ⟨xs, hx, ho⟩ := List.mem_flatten.1 ho
    have hm : xs ∈ ((seqOf elts).zip oss).map Prod.snd := by
      rw [List.map_snd_zip (by omega)]
      exact hx
    obtain ⟨q, hq, hqe⟩ := List.mem_map.1 hm
    exact ih q hq o (hqe ▸ ho)
  | starDel => simp
  | star _ _ ih => exact ih
  | cmp => simp
  | cmpIn _ _ _ ih => exact ih
  | other h =>
    intro o ho
    simp only [List.mem_singleton] at ho
    subst ho
    intro hn
    subst hn
    simp [blameForm] at h

theorem visit_first {g : Ast → Ast} : ∀ {xs : List Ast} {oss : List (List Ast)},
    xs.length = oss.length → (∀ q ∈ xs.zip oss, g q.1 = q.2.headD .null ∧ ∀ o ∈ q.2, o ≠ .null) →
    ((xs.map g).find? (fun x => match x with | .null => false | _ => true)).getD .null =
      oss.flatten.headD .null
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: xs, os :: oss, h, hq => by
    simp only [List.zip_cons_cons, List.mem_cons, forall_eq_or_imp] at hq
    obtain ⟨⟨hg, hnn⟩, hr⟩ := hq
    simp only [List.map_cons, List.find?_cons, List.flatten_cons]
    cases os with
    | nil =>
      rw [hg]
      exact visit_first (by simpa using h) hr
    | cons o os =>
      have ho : o ≠ .null := hnn o (List.mem_cons_self ..)
      rw [hg]
      simp only [List.headD_cons, List.cons_append]
      cases o with
      | null => exact (ho rfl).elim
      | _ => rfl

/-- `_PyPegen_get_invalid_target` returns the first subexpression `Offenders` lists, and `NULL`
when there is none: the leftmost offender of a tuple or list wins (`VISIT_CONTAINER`, `:1220-1229`),
a star is looked through except under `del`, and a `for` target looks through the `in` of a
comparison and nowhere else. The fuel is above the nesting, as the parser's `MAXSTACK` keeps it
below the 100000 of the call sites. -/
def InvalidTargetFirst : Prop := ∀ (k n f : Nat) (e : Ast) (os : List Ast), n < f →
  Offenders k n e os → invalidTarget k f e = os.headD .null

theorem invalidTargetFirst_proven : InvalidTargetFirst := by
  intro k n f
  induction f generalizing n with
  | zero => intro e os h; omega
  | succ f ih =>
    intro e os hn ho
    cases ho with
    | null => rfl
    | name => rfl
    | attr => rfl
    | sub => rfl
    | tuple hl hq =>
      rw [invalidTarget.eq_def]
      simp only []
      exact visit_first hl fun q hm => ⟨ih _ _ _ (by omega) (hq q hm), offenders_nonnull (hq q hm)⟩
    | list hl hq =>
      rw [invalidTarget.eq_def]
      simp only []
      exact visit_first hl fun q hm => ⟨ih _ _ _ (by omega) (hq q hm), offenders_nonnull (hq q hm)⟩
    | starDel hk =>
      rw [invalidTarget.eq_def]
      simp [hk]
    | star hk hv =>
      rw [invalidTarget.eq_def]
      simp only [beq_iff_eq, hk, ↓reduceIte]
      exact ih _ _ _ (by omega) hv
    | cmp hk =>
      rw [invalidTarget.eq_def]
      simp [hk]
    | cmpIn hk hin hv =>
      obtain ⟨fs, l, rest, hs⟩ := hin
      subst hk
      rw [invalidTarget.eq_def]
      simp only [beq_self_eq_true, ↓reduceIte, hs]
      exact ih _ _ _ (by omega) hv
    | cmpOther hk hin =>
      subst hk
      rw [invalidTarget.eq_def]
      simp only [beq_self_eq_true, ↓reduceIte]
      split
      · next _ _ _ hs => exact (hin ⟨_, _, _, hs⟩).elim
      · rfl
    | other h =>
      rw [invalidTarget.eq_def]
      simp only []
      split <;> simp_all [blameForm]

end PyLean.PyGrammar.Check
