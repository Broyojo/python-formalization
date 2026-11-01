import PyLean.PyGrammar.Check.Props

/-!
Where `_PyAST_Validate` can dereference `NULL`. `obj2ast_*` turns `None` into `NULL` for sum types,
`Python/Python-ast.c`, so a `None` in a list of expressions, statements, patterns, handlers or
identifiers reaches the validator. `validate_exprs` and `validate_stmts` check for it. The others do
not, which is the bug `pygrammar-check-none-in-list-segfault`.

`NullSites` is the exact statement: a tree on which `validate` dereferences `NULL` has a `None` at one
of the fields of `nullField`, and nowhere else can cause it. It is proved over all the validators, so
it also says that every other path is safe. Product types (`keyword`, `comprehension`, `arg`,
`withitem`, `match_case`) look unguarded in the C, but `obj2ast` refuses `None` for them; the model
accepts such a tree and moves on, so they are not sites here.
-/

namespace PyLean.PyGrammar.Check

open PyLean

/-- The fields where `validate` meets a `NULL` it does not check for. The first nine are lists; the
rest are required fields, which `obj2ast` fills, so a `None` there does not reach the C. -/
def nullField : Ctor → Nat → Bool
  | .Try, 1 | .TryStar, 1 => true
  | .MatchSequence, 0 | .MatchOr, 0 => true
  | .MatchMapping, 0 | .MatchMapping, 1 => true
  | .MatchClass, 1 | .MatchClass, 2 | .MatchClass, 3 => true
  | .match_case_, 0 => true
  | .Name, 0 | .TypeVar, 0 | .ParamSpec, 0 | .TypeVarTuple, 0 => true
  | _, _ => false

/-- A field that is `NULL`, or a list holding one. -/
def NullIn (v : Ast) : Prop := v = .null ∨ .null ∈ seqL v

/-- Somewhere in the tree, a `nullField` holds a `NULL`. -/
inductive HasNull : Ast → Prop
  | site {c : Ctor} {fs : List Ast} {l : Option Loc} (i : Nat) : nullField c i = true →
      NullIn (fs.getD i .null) → HasNull (.node c fs l)
  | field {c : Ctor} {fs : List Ast} {l : Option Loc} {x : Ast} : x ∈ fs → HasNull x →
      HasNull (.node c fs l)
  | elem {xs : List Ast} {x : Ast} : x ∈ xs → HasNull x → HasNull (.seq xs)

/-- Some element has one. -/
def LN (xs : List Ast) : Prop := ∃ x, x ∈ xs ∧ HasNull x

theorem LN.tail {x : Ast} {xs : List Ast} (h : LN xs) : LN (x :: xs) := by
  obtain ⟨y, hy, hn⟩ := h
  exact ⟨y, List.mem_cons_of_mem _ hy, hn⟩

theorem hasNull_seqL {v : Ast} (h : LN (seqL v)) : HasNull v := by
  obtain ⟨y, hy, hn⟩ := h
  cases v with
  | seq xs => exact HasNull.elem hy hn
  | _ => cases hy

/-- `r` is the `NULL` dereference only if `G`. -/
def Nn (r : V) (G : Prop) : Prop := r = nullDeref → G

theorem Nn.mono {r : V} {G G' : Prop} (h : Nn r G) (k : G → G') : Nn r G' := fun e => k (h e)

theorem Nn.and {a : V} {b : Unit → V} {G : Prop} (ha : Nn a G) (hb : Nn (b ()) G) :
    Nn (a.and b) G := by
  intro h
  cases a with
  | ok u => exact hb h
  | error e => exact ha h

theorem Nn.ok' {G : Prop} : Nn ok1 G := fun h => by cases h

theorem Nn.verr {G : Prop} (m : String) : Nn (verr m) G := fun h => by cases h

theorem Nn.terr {G : Prop} (m : String) : Nn (terr m) G := fun h => by cases h

theorem Nn.ite {c : Prop} [Decidable c] {x y : V} {G : Prop} (hx : Nn x G) (hy : Nn y G) :
    Nn (if c then x else y) G := by
  by_cases h : c
  · rw [if_pos h]
    exact hx
  · rw [if_neg h]
    exact hy

theorem positions_safe {G : Prop} (l : Option Loc) : Nn (validatePositions l) G := by
  intro h
  unfold validatePositions at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h

theorem validateName_null {n : Ast} (h : validateName n = nullDeref) : n = .null := by
  unfold validateName at h
  split at h
  · rfl
  all_goals cases h

theorem nonempty_safe {G : Prop} (s : Ast) (a b : String) : Nn (validateNonemptySeq s a b) G := by
  intro h
  unfold validateNonemptySeq at h
  split at h <;> cases h

theorem capture_null {n : Ast} (h : validateCapture n = nullDeref) : n = .null := by
  unfold validateCapture at h
  split at h
  · cases h
  · exact validateName_null h

theorem names_null (xs : List Ast) (acc : V)
    (h : (xs.foldl (fun acc n => acc.and fun _ => validateName n) acc) = nullDeref) :
    acc = nullDeref ∨ .null ∈ xs := by
  induction xs generalizing acc with
  | nil => exact Or.inl h
  | cons x xs ih =>
    simp only [List.foldl_cons] at h
    rcases ih _ h with e | e
    · have k : Nn (acc.and fun _ => validateName x) (acc = nullDeref ∨ .null ∈ x :: xs) :=
        Nn.and (fun e => Or.inl e) (fun e => Or.inr (by
          rw [validateName_null e]
          exact List.mem_cons_self ..))
      exact k e
    · exact Or.inr (List.mem_cons_of_mem _ e)

theorem exprCtx_err {c : Ctor} {fs : List Ast} {ctx : Ctor} {e : V} {l : Option Loc}
    (h : exprCtx c fs ctx = .error e) : Nn e (HasNull (.node c fs l)) := by
  intro he
  subst he
  unfold exprCtx at h
  split at h
  any_goals cases h
  · rename_i id x
    have hv : validateName id = nullDeref := by
      cases hv : validateName id with
      | ok u =>
        rw [hv] at h
        cases u
        cases h
      | error e =>
        rw [hv] at h
        simpa using h
    exact HasNull.site 0 rfl (Or.inl (validateName_null hv))
  · split at h
    · cases h
    · cases h

/-- All the validators together. -/
structure NS (f : Nat) : Prop where
  comprehension : ∀ g, Nn (validateComprehension f g) (LN (seqL g))
  comps : ∀ xs, Nn (validateComps f xs) (LN xs)
  keywords : ∀ xs, Nn (validateKeywords f xs) (LN xs)
  args : ∀ xs, Nn (validateArgs f xs) (LN xs)
  optArg : ∀ a, Nn (validateOptArgAnnotation f a) (HasNull a)
  arguments : ∀ a, Nn (validateArguments f a) (HasNull a)
  expr : ∀ e c, Nn (validateExpr f e c) (HasNull e)
  body : ∀ c fs ctx, Nn (validateExprBody f c fs ctx) (LN fs)
  exprs : ∀ xs c b, Nn (validateExprs f xs c b) (LN xs)
  matchValue : ∀ e, Nn (validateMatchValue f e) (HasNull e)
  keys : ∀ xs, Nn (validateMappingKeys f xs) (LN xs ∨ .null ∈ xs)
  pattern : ∀ p b, Nn (validatePattern f p b) (HasNull p ∨ p = .null)
  classRoot : ∀ c, Nn (classRoot f c) False
  patterns : ∀ xs b, Nn (validatePatterns f xs b) (LN xs ∨ .null ∈ xs)
  assign : ∀ t c, Nn (validateAssignlist f t c) (LN (seqL t))
  bodyS : ∀ b n, Nn (validateBody f b n) (LN (seqL b))
  withItems : ∀ xs, Nn (validateWithItems f xs) (LN xs)
  cases : ∀ xs, Nn (validateCases f xs) (LN xs)
  handlers : ∀ xs p, Nn (validateHandlers f xs p) (LN xs ∨ .null ∈ xs)
  try_ : ∀ n b h o fb p, Nn (validateTry f n b h o fb p) (LN [b, h, o, fb] ∨ .null ∈ seqL h)
  typeParam : ∀ t, Nn (validateTypeParam f t) (HasNull t)
  typeParams : ∀ xs, Nn (validateTypeParams f xs) (LN xs)
  stmt : ∀ s, Nn (validateStmt f s) (HasNull s)
  stmts : ∀ xs, Nn (validateStmts f xs) (LN xs)

theorem ns_zero : NS 0 := by
  constructor
  all_goals (intros; simp only [validateComprehension, validateComps, validateKeywords, validateArgs,
    validateOptArgAnnotation, validateArguments, validateExpr, validateExprBody, validateExprs,
    validateMatchValue, validateMappingKeys, validatePattern, classRoot, validatePatterns,
    validateAssignlist, validateBody, validateWithItems, validateCases, validateHandlers,
    validateTry, validateTypeParam, validateTypeParams, validateStmt, validateStmts]; intro h; cases h)

macro "mem0" : tactic => `(tactic| exact List.mem_cons_self ..)
macro "mem1" : tactic => `(tactic| first | mem0 | (refine List.mem_cons_of_mem _ ?_; mem0))
macro "mem2" : tactic => `(tactic| first | mem0 | (refine List.mem_cons_of_mem _ ?_; mem1))
macro "mem3" : tactic => `(tactic| first | mem0 | (refine List.mem_cons_of_mem _ ?_; mem2))
macro "mem4" : tactic => `(tactic| first | mem0 | (refine List.mem_cons_of_mem _ ?_; mem3))
macro "mem5" : tactic => `(tactic| first | mem0 | (refine List.mem_cons_of_mem _ ?_; mem4))
macro "mem6" : tactic => `(tactic| first | mem0 | (refine List.mem_cons_of_mem _ ?_; mem5))

set_option hygiene false in
/-- From what a call says about its argument to what the caller needs. -/
macro "nn_up" : tactic => `(tactic| first
  | exact fun h => h
  | exact LN.tail
  | (refine fun h => ⟨_, ?_, h⟩; mem6)
  | (refine fun h => ⟨_, ?_, hasNull_seqL h⟩; mem6)
  | (refine fun h => ⟨_, List.mem_cons_self .., HasNull.field ?_ h⟩; mem6)
  | (refine fun h => ⟨_, List.mem_cons_self .., HasNull.field ?_ (hasNull_seqL h)⟩; mem6)
  | (refine fun h => HasNull.field ?_ h; mem6)
  | (refine fun h => HasNull.field ?_ (hasNull_seqL h); mem6)
  | (refine fun h => Or.inl (HasNull.field ?_ h); mem6)
  | (refine fun h => Or.inl (HasNull.field ?_ (hasNull_seqL h)); mem6)
  | (refine fun h => Or.inl ⟨_, List.mem_cons_self .., HasNull.field ?_ h⟩; mem6)
  | (refine fun h => Or.inl ⟨_, List.mem_cons_self .., HasNull.field ?_ (hasNull_seqL h)⟩; mem6)
  | exact fun h => Or.inl h
  | exact fun h => Or.inl (hasNull_seqL h))

set_option hygiene false in
macro "nn" : tactic => `(tactic| repeat' (first
  | with_reducible exact Nn.ok'
  | with_reducible exact Nn.verr _
  | with_reducible exact Nn.terr _
  | with_reducible exact positions_safe _
  | with_reducible exact nonempty_safe _ _ _
  | ((with_reducible refine (h.expr _ _).mono ?_); nn_up)
  | ((with_reducible refine (h.exprs _ _ _).mono ?_); nn_up)
  | ((with_reducible refine (h.comprehension _).mono ?_); nn_up)
  | ((with_reducible refine (h.comps _).mono ?_); nn_up)
  | ((with_reducible refine (h.keywords _).mono ?_); nn_up)
  | ((with_reducible refine (h.args _).mono ?_); nn_up)
  | ((with_reducible refine (h.optArg _).mono ?_); nn_up)
  | ((with_reducible refine (h.arguments _).mono ?_); nn_up)
  | ((with_reducible refine (h.body _ _ _).mono ?_); nn_up)
  | ((with_reducible refine (h.matchValue _).mono ?_); nn_up)
  | ((with_reducible refine (h.assign _ _).mono ?_); nn_up)
  | ((with_reducible refine (h.bodyS _ _).mono ?_); nn_up)
  | ((with_reducible refine (h.withItems _).mono ?_); nn_up)
  | ((with_reducible refine (h.cases _).mono ?_); nn_up)
  | ((with_reducible refine (h.typeParam _).mono ?_); nn_up)
  | ((with_reducible refine (h.typeParams _).mono ?_); nn_up)
  | ((with_reducible refine (h.stmt _).mono ?_); nn_up)
  | ((with_reducible refine (h.stmts _).mono ?_); nn_up)
  | ((with_reducible refine (h.handlers _ _).mono ?_);
      exact fun e => e.elim (fun a => Or.inl a.tail) (fun a => Or.inr (List.mem_cons_of_mem _ a)))
  | ((with_reducible refine (h.try_ _ _ _ _ _ _).mono ?_);
      exact fun e => e.elim (fun ⟨_, hx, hn⟩ => HasNull.field hx hn)
        (fun a => HasNull.site 1 rfl (Or.inr a)))
  | exact h.classRoot _
  | exact fun e => HasNull.site 0 rfl (Or.inl (validateName_null e))
  | with_reducible refine Nn.and ?_ ?_
  | with_reducible refine Nn.ite ?_ ?_
  | dsimp only
  | split))

theorem ls_up {c : Ctor} {fs : List Ast} {l : Option Loc} {i : Nat} {v : Ast} {r : V}
    (e1 : fs.getD i .null = v) (e2 : nullField c i = true) (e3 : v ∈ fs)
    (hr : Nn r (LN (seqL v) ∨ .null ∈ seqL v)) :
    Nn r (HasNull (.node c fs l) ∨ Ast.node c fs l = .null) := by
  refine hr.mono fun e => Or.inl ?_
  rcases e with a | a
  · exact HasNull.field e3 (hasNull_seqL a)
  · exact HasNull.site i e2 (by rw [e1]; exact Or.inr a)

theorem capt_safe {G : Prop} (r : Ast) : Nn (if isNull r then ok1 else validateCapture r) G := by
  by_cases h : isNull r = true
  · rw [if_pos h]
    exact Nn.ok'
  · rw [if_neg h]
    intro e
    have := capture_null e
    subst this
    exact (h rfl).elim

theorem ns_succ {f : Nat} (h : NS f) : NS (f + 1) := by
  constructor
  · intro g
    rw [validateComprehension.eq_def]
    simp only []
    nn
  · intro xs
    rw [validateComps.eq_def]
    simp only []
    nn
  · intro xs
    rw [validateKeywords.eq_def]
    simp only []
    nn
  · intro xs
    rw [validateArgs.eq_def]
    simp only []
    nn
  · intro a
    rw [validateOptArgAnnotation.eq_def]
    simp only []
    nn
  · intro a
    rw [validateArguments.eq_def]
    simp only []
    nn
  · intro e c
    rw [validateExpr.eq_def]
    simp only []
    split
    · refine Nn.and (positions_safe _) ?_
      try dsimp only
      split
      · rename_i hc
        exact exprCtx_err hc
      · split
        · refine Nn.ite (Nn.verr _) ?_
          exact (h.body _ _ _).mono fun ⟨x, hx, hn⟩ => HasNull.field hx hn
        · exact (h.body _ _ _).mono fun ⟨x, hx, hn⟩ => HasNull.field hx hn
    · exact Nn.ok'
  · intro c fs ctx
    rw [validateExprBody.eq_def]
    simp only []
    nn
  · intro xs c b
    rw [validateExprs.eq_def]
    simp only []
    nn
  · intro e
    rw [validateMatchValue.eq_def]
    simp only []
    refine Nn.and ((h.expr _ _).mono fun x => x) ?_
    nn
  · -- `validateMappingKeys`: the unchecked `key->kind`
    intro xs
    rw [validateMappingKeys.eq_def]
    simp only []
    split
    · exact Nn.ok'
    · exact fun _ => Or.inr (List.mem_cons_self ..)
    · rename_i key rest hn
      have hrest := h.keys rest
      have up : (LN rest ∨ .null ∈ rest) → (LN (key :: rest) ∨ .null ∈ key :: rest) :=
        fun e => e.elim (fun a => Or.inl a.tail) (fun a => Or.inr (List.mem_cons_of_mem _ a))
      split
      · exact hrest.mono up
      · exact hrest.mono up
      · exact hrest.mono up
      · exact Nn.and ((h.matchValue _).mono fun a => Or.inl ⟨_, List.mem_cons_self .., a⟩)
          (hrest.mono up)
  · -- `validatePattern`: the unchecked `p->kind` and the lists below it
    intro p b
    rw [validatePattern.eq_def]
    simp only []
    split
    · exact fun _ => Or.inr rfl
    · rename_i c fs l
      refine Nn.and (positions_safe _) ?_
      try dsimp only
      split
      · exact (h.matchValue _).mono fun a => Or.inl (HasNull.field (by simp) a)
      · split
        · exact Nn.ok'
        · exact Nn.ok'
        · exact Nn.ok'
        · exact Nn.verr _
      · exact ls_up (i := 0) rfl rfl (by simp) (h.patterns _ _)
      · refine Nn.ite (Nn.verr _) (Nn.and (capt_safe _) (Nn.and ?_ ?_))
        · exact ls_up (i := 0) rfl rfl (by simp) (h.keys _)
        · exact ls_up (i := 1) rfl rfl (by simp) (h.patterns _ _)
      · refine Nn.ite (Nn.verr _) (Nn.and ?_ (Nn.and ?_ (Nn.and ?_ (Nn.and ?_ ?_))))
        · exact (h.expr _ _).mono fun a => Or.inl (HasNull.field (by simp) a)
        · exact (h.classRoot _).mono False.elim
        · intro e
          refine Or.inl (HasNull.site 2 rfl (Or.inr ?_))
          exact (names_null _ _ e).resolve_left fun x => Nn.ok' x
        · exact ls_up (i := 1) rfl rfl (by simp) (h.patterns _ _)
        · exact ls_up (i := 3) rfl rfl (by simp) (h.patterns _ _)
      · exact Nn.ite (Nn.verr _) (capt_safe _)
      · rename_i pat name
        refine Nn.and (capt_safe _) ?_
        by_cases hp : isNull pat = true
        · rw [if_pos hp]
          exact Nn.ok'
        · rw [if_neg hp]
          refine Nn.ite (Nn.verr _) ?_
          refine (h.pattern pat false).mono fun e => ?_
          rcases e with a | a
          · exact Or.inl (HasNull.field (by simp) a)
          · subst a
            exact (hp rfl).elim
      · exact Nn.ite (Nn.verr _) (ls_up (i := 0) rfl rfl (by simp) (h.patterns _ _))
      · exact Nn.ok'
    · exact Nn.ok'
  · intro c
    rw [classRoot.eq_def]
    simp only []
    nn
  · intro xs b
    rw [validatePatterns.eq_def]
    simp only []
    split
    · exact Nn.ok'
    · rename_i p rest
      refine Nn.and ((h.pattern p b).mono fun e => ?_) ((h.patterns rest b).mono fun e => ?_)
      · rcases e with a | a
        · exact Or.inl ⟨p, List.mem_cons_self .., a⟩
        · subst a
          exact Or.inr (List.mem_cons_self ..)
      · exact e.elim (fun a => Or.inl a.tail) (fun a => Or.inr (List.mem_cons_of_mem _ a))
  · intro t c
    rw [validateAssignlist.eq_def]
    simp only []
    nn
  · intro b n
    rw [validateBody.eq_def]
    simp only []
    nn
  · intro xs
    rw [validateWithItems.eq_def]
    simp only []
    nn
  · intro xs
    rw [validateCases.eq_def]
    simp only []
    split
    · exact Nn.ok'
    · rename_i c' pat guard body l rest
      refine Nn.and ((h.pattern pat false).mono fun e => ?_) ?_
      · rcases e with a | a
        · exact ⟨_, List.mem_cons_self .., HasNull.field (by simp) a⟩
        · subst a
          exact ⟨_, List.mem_cons_self .., HasNull.site 0 rfl (Or.inl rfl)⟩
      · nn
    · nn
  · intro xs p
    rw [validateHandlers.eq_def]
    simp only []
    split
    · exact Nn.ok'
    · exact fun _ => Or.inr (List.mem_cons_self ..)
    · nn
    · nn
  · intro n b hd o fb p
    rw [validateTry.eq_def]
    simp only []
    refine Nn.and ((h.bodyS _ _).mono fun a => Or.inl ⟨b, by simp, hasNull_seqL a⟩) ?_
    refine Nn.ite (Nn.verr _) (Nn.ite (Nn.verr _) (Nn.and ?_ (Nn.and ?_ ?_)))
    · exact (h.handlers _ _).mono fun e =>
        e.elim (fun a => Or.inl ⟨hd, by simp, hasNull_seqL a⟩) Or.inr
    · exact (h.stmts _).mono fun a => Or.inl ⟨fb, by simp, hasNull_seqL a⟩
    · exact (h.stmts _).mono fun a => Or.inl ⟨o, by simp, hasNull_seqL a⟩
  · intro t
    rw [validateTypeParam.eq_def]
    simp only []
    nn
  · intro xs
    rw [validateTypeParams.eq_def]
    simp only []
    nn
  · intro s
    rw [validateStmt.eq_def]
    simp only []
    nn
  · intro xs
    rw [validateStmts.eq_def]
    simp only []
    nn

theorem ns_all (f : Nat) : NS f := by
  induction f with
  | zero => exact ns_zero
  | succ f ih => exact ns_succ ih

/-- `_PyAST_Validate` dereferences `NULL` on a tree only if that tree has a `None` at a `nullField`:
`Try.handlers`, `TryStar.handlers`, the `patterns` of `MatchSequence`, `MatchOr`, `MatchMapping` and
`MatchClass`, `MatchMapping.keys`, `MatchClass.kwd_attrs` or `kwd_patterns`, or a required field
`obj2ast` fills. Every other list is safe, for every tree: `validate_exprs` and `validate_stmts`
check, and the rest are product types. -/
def NullSites : Prop := ∀ m : Ast, validate m = nullDeref → HasNull m

theorem nullSites_proven : NullSites := by
  intro m
  unfold validate
  dsimp only
  split
  · exact fun e => HasNull.field (by simp) (hasNull_seqL ((ns_all _).stmts _ e))
  · exact fun e => HasNull.field (by simp) (hasNull_seqL ((ns_all _).stmts _ e))
  · exact fun e => HasNull.field (by simp) ((ns_all _).expr _ _ e)
  · refine Nn.and ((ns_all _).exprs _ _ _ |>.mono fun a => HasNull.field (by simp) (hasNull_seqL a)) ?_
    exact (ns_all _).expr _ _ |>.mono fun a => HasNull.field (by simp) a
  · intro e
    simp [nullDeref] at e

end PyLean.PyGrammar.Check
