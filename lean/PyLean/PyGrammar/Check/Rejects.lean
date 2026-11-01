import PyLean.PyGrammar.Check.Props

/-!
What `Python/ast.c` refuses, stated as a table and not as a run of the validators.

`spec` gives, for each kind of position in a tree (an expression in some context, a statement, a
pattern, a `comprehension`, ...) and each constructor, the rule the node must satisfy and the
children that must satisfy theirs. `W` is the closure of that table over a tree. `ValidateRejects`
says `_PyAST_Validate` accepts only trees in `W`: every validator refuses what its row refuses, at
any depth, for every tree. A `None` in a list that does not allow one is a refused tree, whether the
C code says so or crashes, which is the other half of `NullSites`.

The table says what is checked, and it says nothing about which check fails first or with what
message: the difftest covers those. Children that are absent from a row are not checked, and that is
deliberate where the C does not check them: `NamedExpr.target` is the case on record, see
`pygrammar-check-namedexpr-target`, and `TableCovers` shows it is the only one. Source positions are
checked on expressions, statements, patterns, `arg` and type parameters, but not on `vararg`, `kwarg`
or `keyword`, `withitem`, `comprehension` and `match_case` nodes, nor on `TryStar` handlers, see
`pygrammar-check-trystar-handlers`, which is why `handler` carries a flag.

Rows for a constructor at the wrong arity are `(True, [])`: `obj2ast` does not produce those trees,
and the validators accept them unread.
-/

namespace PyLean.PyGrammar.Check

open PyLean

/-- What kind of thing a child is, from its ASDL type and the context it is checked in. -/
inductive Pos where
  | module
  | expr (ctx : Ctor)
  | stmt
  | pat (star : Bool)
  | comp
  | kw
  | arg
  /-- `arguments.vararg` and `kwarg`: only the annotation is read. -/
  | optArg
  | arguments
  | item
  | case_
  | handler (positions : Bool)
  | tparam
  /-- The value of `MatchValue`. -/
  | value
  /-- A key of `MatchMapping`. -/
  | key
  /-- `MatchClass.cls`, which must be a dotted name. -/
  | cls

/-- `VALIDATE_POSITIONS`, as a condition. -/
def posOk : Option Loc → Prop
  | none => True
  | some l => l.lineno ≤ l.endLineno ∧ (l.lineno < 0 → l.endLineno = l.lineno)
      ∧ (l.colOffset < 0 → l.colOffset = l.endColOffset)
      ∧ (l.lineno = l.endLineno → l.colOffset ≤ l.endColOffset)

/-- `validate_name`: present, and not `None`, `True` or `False`. -/
def NameOk (n : Ast) : Prop :=
  n ≠ .null ∧ n ≠ .ident [78, 111, 110, 101] ∧ n ≠ .ident [84, 114, 117, 101]
    ∧ n ≠ .ident [70, 97, 108, 115, 101]

/-- An optional capture target: absent, or a name other than `_`. -/
def CaptureOk (n : Ast) : Prop := n = .null ∨ (n ≠ .ident [95] ∧ NameOk n)

/-- The list holds no `None`. -/
def NoNull (xs : List Ast) : Prop := Ast.null ∉ xs

/-- Is this a `Name` node? -/
def isNameNode : Ast → Bool
  | .node .Name _ _ => true
  | _ => false

/-- `ImportFrom.level` is not negative. -/
def LevelOk : Ast → Prop
  | .int v => 0 ≤ v
  | _ => True

/-- `MatchSingleton.value`. -/
def IsSingleton : Ast → Prop
  | .const .none | .const .true_ | .const .false_ => True
  | _ => False

/-- A constant allowed in a value pattern. -/
def ConstLit : PyConst → Prop
  | .int _ | .float _ | .bytes _ | .complex _ _ | .str _ => True
  | _ => False

/-- A real or imaginary number constant, as allowed. -/
def NumLit (real imag : Bool) : Ast → Prop
  | .node .Constant (.const (.int _) :: _) _ | .node .Constant (.const (.float _) :: _) _ =>
    real = true
  | .node .Constant (.const (.complex _ _) :: _) _ => imag = true
  | _ => False

/-- The negation of one, by unary minus and no other operator. -/
def NegLit (real imag : Bool) : Ast → Prop
  | .node .UnaryOp [.node .USub _ _, o] _ => NumLit real imag o
  | _ => False

/-- `a + bj` or `a - bj`: a possibly negated real on the left, and an unsigned imaginary on the
right. -/
def ComplexLit : Ast → Prop
  | .node .BinOp [l, .node .Add _ _, r] _ | .node .BinOp [l, .node .Sub _ _, r] _ =>
    (NumLit true false l ∨ NegLit true false l) ∧ NumLit false true r
  | _ => False

/-- The shapes of `validate_pattern_match_value`. -/
def LiteralOk : Ast → Prop
  | .node .Constant (.const v :: _) _ => ConstLit v
  | .node .Attribute _ _ => True
  | e@(.node .UnaryOp _ _) => NegLit true true e
  | e@(.node .BinOp _ _) => ComplexLit e
  | .node .JoinedStr _ _ | .node .TemplateStr _ _ => True
  | _ => False

/-- `None`, `True` and `False` are allowed as mapping keys without further checks. -/
def SingletonKey : Ast → Prop
  | .node .Constant (.const .none :: _) _ | .node .Constant (.const .true_ :: _) _
  | .node .Constant (.const .false_ :: _) _ => True
  | _ => False

/-- A row: the node's own rule, and the children that must satisfy theirs. -/
abbrev Spec := Prop × List (Pos × Ast)

/-- Each element of a sequence field, at position `p`. -/
def elts (p : Pos) (v : Ast) : List (Pos × Ast) := (seqL v).map fun x => (p, x)

/-- Load position. -/
abbrev E : Pos := .expr .Load

/-- Store position. -/
abbrev St : Pos := .expr .Store

/-- The first switch of `validate_expr`: a node with a `ctx` field has the context of its position,
and any other node is only legal in `Load` position. -/
def exprHead (ctx : Ctor) : Ctor → List Ast → Prop
  | .Attribute, [_, _, x] | .Subscript, [_, _, x] => ctxOfAst x = ctx
  | .Starred, [_, x] | .List, [_, x] | .Tuple, [_, x] => ctxOfAst x = ctx
  | .Name, [id, x] => NameOk id ∧ ctxOfAst x = ctx
  | _, _ => ctx = .Load

/-- The second switch of `validate_expr`. `Dict.keys` may hold `None`, for `**d`. -/
def exprBody (ctx : Ctor) : Ctor → List Ast → Spec
  | .BoolOp, [_, vs] => (2 ≤ seqLen vs ∧ NoNull (seqL vs), elts E vs)
  | .BinOp, [l, _, r] => (True, [(E, l), (E, r)])
  | .UnaryOp, [_, o] => (True, [(E, o)])
  | .Lambda, [a, b] => (True, [(.arguments, a), (E, b)])
  | .IfExp, [t, b, o] => (True, [(E, t), (E, b), (E, o)])
  | .Dict, [ks, vs] => (seqLen ks = seqLen vs ∧ NoNull (seqL vs), elts E ks ++ elts E vs)
  | .Set, [es] => (NoNull (seqL es), elts E es)
  | .ListComp, [e, g] | .SetComp, [e, g] | .GeneratorExp, [e, g] =>
    (seqLen g ≠ 0, elts .comp g ++ [(E, e)])
  | .DictComp, [k, v, g] => (seqLen g ≠ 0, elts .comp g ++ [(E, k), (E, v)])
  | .Yield, [v] | .YieldFrom, [v] | .Await, [v] => (True, [(E, v)])
  | .Compare, [l, ops, cs] =>
    (seqLen cs ≠ 0 ∧ seqLen cs = seqLen ops ∧ NoNull (seqL cs), elts E cs ++ [(E, l)])
  | .Call, [fn, args, kws] => (NoNull (seqL args), (E, fn) :: elts E args ++ elts .kw kws)
  | .JoinedStr, [v] | .TemplateStr, [v] => (NoNull (seqL v), elts E v)
  | .FormattedValue, [v, _, s] => (True, [(E, v), (E, s)])
  | .Interpolation, [v, _, _, s] => (True, [(E, v), (E, s)])
  | .Attribute, [v, _, _] => (True, [(E, v)])
  | .Subscript, [v, s, _] => (True, [(E, s), (E, v)])
  | .Starred, [v, _] => (True, [(.expr ctx, v)])
  | .Slice, [a, b, s] => (True, [(E, a), (E, b), (E, s)])
  | .List, [e, _] | .Tuple, [e, _] => (NoNull (seqL e), elts (.expr ctx) e)
  | .NamedExpr, [t, v] => (isNameNode t = true, [(E, v)])
  | _, _ => (True, [])

/-- A body: present, with no `None` in it. -/
def BodyOk (b : Ast) : Prop := seqLen b ≠ 0 ∧ NoNull (seqL b)

/-- `Try` and `TryStar`. -/
def trySpec (b hs o fb : Ast) (positions : Bool) : Spec :=
  (BodyOk b ∧ NoNull (seqL fb) ∧ NoNull (seqL o) ∧ (seqLen hs ≠ 0 ∨ seqLen fb ≠ 0)
      ∧ (seqLen hs = 0 → seqLen o = 0),
    elts .stmt b ++ elts (.handler positions) hs ++ elts .stmt fb ++ elts .stmt o)

/-- `validate_stmt`. -/
def stmtSpec : Ctor → List Ast → Spec
  | .FunctionDef, [_, a, b, d, r, _, t] | .AsyncFunctionDef, [_, a, b, d, r, _, t] =>
    (BodyOk b ∧ NoNull (seqL d),
      elts .stmt b ++ elts .tparam t ++ (.arguments, a) :: elts E d ++ [(E, r)])
  | .ClassDef, [_, bs, ks, b, d, t] =>
    (BodyOk b ∧ NoNull (seqL bs) ∧ NoNull (seqL d),
      elts .stmt b ++ elts .tparam t ++ elts E bs ++ elts .kw ks ++ elts E d)
  | .Return, [v] => (True, [(E, v)])
  | .Delete, [t] => (seqLen t ≠ 0 ∧ NoNull (seqL t), elts (.expr .Del) t)
  | .Assign, [t, v, _] => (seqLen t ≠ 0 ∧ NoNull (seqL t), elts St t ++ [(E, v)])
  | .AugAssign, [t, _, v] => (True, [(St, t), (E, v)])
  | .AnnAssign, [t, a, v, s] => (isNameNode t = true ∨ s = .int 0, [(St, t), (E, v), (E, a)])
  | .TypeAlias, [n, t, v] => (isNameNode n = true, (St, n) :: elts .tparam t ++ [(E, v)])
  | .For, [t, i, b, o, _] | .AsyncFor, [t, i, b, o, _] =>
    (BodyOk b ∧ NoNull (seqL o), (St, t) :: (E, i) :: elts .stmt b ++ elts .stmt o)
  | .While, [t, b, o] | .If, [t, b, o] =>
    (BodyOk b ∧ NoNull (seqL o), (E, t) :: elts .stmt b ++ elts .stmt o)
  | .With, [is, b, _] | .AsyncWith, [is, b, _] =>
    (seqLen is ≠ 0 ∧ BodyOk b, elts .item is ++ elts .stmt b)
  | .Match, [s, cs] => (seqLen cs ≠ 0, (E, s) :: elts .case_ cs)
  | .Raise, [e, c] => (e = .null → c = .null, [(E, e), (E, c)])
  | .Try, [b, h, o, fb] => trySpec b h o fb true
  | .TryStar, [b, h, o, fb] => trySpec b h o fb false
  | .Assert, [t, m] => (True, [(E, t), (E, m)])
  | .Import, [n] | .Global, [n] | .Nonlocal, [n] => (seqLen n ≠ 0, [])
  | .ImportFrom, [_, n, lv] => (LevelOk lv ∧ seqLen n ≠ 0, [])
  | .Expr, [v] => (True, [(E, v)])
  | _, _ => (True, [])

/-- `validate_pattern`. A `None` pattern is refused by `leafOk`. -/
def patSpec (star : Bool) : Ctor → List Ast → Spec
  | .MatchValue, [v] => (True, [(.value, v)])
  | .MatchSingleton, [v] => (IsSingleton v, [])
  | .MatchSequence, [ps] => (True, elts (.pat true) ps)
  | .MatchMapping, [ks, ps, r] =>
    (seqLen ks = seqLen ps ∧ CaptureOk r, elts .key ks ++ elts (.pat false) ps)
  | .MatchClass, [c, ps, as, kps] =>
    (seqLen as = seqLen kps ∧ ∀ n ∈ seqL as, NameOk n,
      (E, c) :: (.cls, c) :: elts (.pat false) ps ++ elts (.pat false) kps)
  | .MatchStar, [n] => (star = true ∧ CaptureOk n, [])
  | .MatchAs, [p, n] =>
    (CaptureOk n ∧ (p ≠ .null → n ≠ .null), if isNull p then [] else [(.pat false, p)])
  | .MatchOr, [ps] => (2 ≤ seqLen ps, elts (.pat false) ps)
  | _, _ => (True, [])

/-- `validate_typeparam`. -/
def tparamSpec : Ctor → List Ast → Spec
  | .TypeVar, [n, b, d] => (NameOk n, [(E, b), (E, d)])
  | .ParamSpec, [n, d] | .TypeVarTuple, [n, d] => (NameOk n, [(E, d)])
  | _, _ => (True, [])

/-- The module node of `_PyAST_Validate`. -/
def modSpec : Ctor → List Ast → Spec
  | .Module, b :: _ | .Interactive, b :: _ => (NoNull (seqL b), elts .stmt b)
  | .Expression, [b] => (True, [(E, b)])
  | .FunctionType, [a, r] => (NoNull (seqL a), elts E a ++ [(E, r)])
  | _, _ => (False, [])

def compSpec : List Ast → Spec
  | [t, i, ifs, _] => (NoNull (seqL ifs), (St, t) :: (E, i) :: elts E ifs)
  | _ => (True, [])

def kwSpec : List Ast → Spec
  | [_, v] => (True, [(E, v)])
  | _ => (True, [])

def argSpec (l : Option Loc) : List Ast → Spec
  | [_, a, _] => (posOk l, [(E, a)])
  | _ => (True, [])

def optArgSpec : List Ast → Spec
  | [_, a, _] => (True, [(E, a)])
  | _ => (True, [])

def argumentsSpec : List Ast → Spec
  | [po, a, va, ko, kd, ka, d] =>
    (seqLen d ≤ seqLen po + seqLen a ∧ seqLen kd = seqLen ko ∧ NoNull (seqL d),
      elts .arg po ++ elts .arg a ++ (.optArg, va) :: elts .arg ko ++ (.optArg, ka) ::
        elts E d ++ elts E kd)
  | _ => (True, [])

def itemSpec : List Ast → Spec
  | [e, v] => (True, [(E, e), (St, v)])
  | _ => (True, [])

def caseSpec : Ctor → List Ast → Spec
  | .match_case_, [p, g, b] => (BodyOk b, (.pat false, p) :: (E, g) :: elts .stmt b)
  | _, _ => (True, [])

def handlerSpec (positions : Bool) (l : Option Loc) : List Ast → Spec
  | [ty, _, b] => ((positions = true → posOk l) ∧ BodyOk b, (E, ty) :: elts .stmt b)
  | _ => (True, [])

/-- The whole table. -/
def spec (p : Pos) (c : Ctor) (fs : List Ast) (l : Option Loc) : Spec :=
  match p with
  | .module => modSpec c fs
  | .expr ctx =>
    (posOk l ∧ exprHead ctx c fs ∧ (exprBody ctx c fs).1, (exprBody ctx c fs).2)
  | .stmt => (posOk l ∧ (stmtSpec c fs).1, (stmtSpec c fs).2)
  | .pat star => (posOk l ∧ (patSpec star c fs).1, (patSpec star c fs).2)
  | .comp => compSpec fs
  | .kw => kwSpec fs
  | .arg => argSpec l fs
  | .optArg => optArgSpec fs
  | .arguments => argumentsSpec fs
  | .item => itemSpec fs
  | .case_ => caseSpec c fs
  | .handler positions => handlerSpec positions l fs
  | .tparam => (posOk l ∧ (tparamSpec c fs).1, (tparamSpec c fs).2)
  | .value | .key | .cls => (False, [])

/-- What may stand where no node is. The patterns and handlers are the `NULL` the C dereferences. -/
def leafOk : Pos → Ast → Prop
  | .pat _, a | .handler _, a => a ≠ .null
  | .module, _ | .value, _ | .key, _ | .cls, _ => False
  | _, _ => True

/-- The tree satisfies the table from this position down. -/
inductive W : Pos → Ast → Prop
  | node {p : Pos} {c : Ctor} {fs : List Ast} {l : Option Loc} : (spec p c fs l).1 →
      (∀ k ∈ (spec p c fs l).2, W k.1 k.2) → W p (.node c fs l)
  | leaf {p : Pos} {a : Ast} : leafOk p a → (∀ c fs l, a ≠ .node c fs l) → W p a
  | value {a : Ast} : LiteralOk a → W E a → W .value a
  | singleton {a : Ast} : SingletonKey a → W .key a
  | keyValue {a : Ast} : W .value a → W .key a
  | clsName {fs : List Ast} {l : Option Loc} : W .cls (.node .Name fs l)
  | clsAttr {v : Ast} {vs : List Ast} {l : Option Loc} : W .cls v →
      W .cls (.node .Attribute (v :: vs) l)

/-- Every element is good at `p`. -/
def All (p : Pos) (xs : List Ast) : Prop := ∀ y ∈ xs, W p y

/-- The children of a row are good. -/
def Kids (ks : List (Pos × Ast)) : Prop := ∀ k ∈ ks, W k.1 k.2

/-- A row holds. -/
def OK (s : Spec) : Prop := s.1 ∧ Kids s.2

theorem W.mk {p : Pos} {c : Ctor} {fs : List Ast} {l : Option Loc} (h : OK (spec p c fs l)) :
    W p (.node c fs l) := W.node h.1 h.2

theorem kids_nil : Kids [] ↔ True := by simp [Kids]

theorem kids_cons {k : Pos × Ast} {ks : List (Pos × Ast)} :
    Kids (k :: ks) ↔ W k.1 k.2 ∧ Kids ks := by simp [Kids]

theorem kids_append {a b : List (Pos × Ast)} : Kids (a ++ b) ↔ Kids a ∧ Kids b := by
  simp only [Kids, List.mem_append]
  constructor
  · exact fun h => ⟨fun k hk => h k (Or.inl hk), fun k hk => h k (Or.inr hk)⟩
  · exact fun ⟨a, b⟩ k hk => hk.elim (a k) (b k)

theorem kids_elts {p : Pos} {v : Ast} : Kids (elts p v) ↔ All p (seqL v) := by
  simp [Kids, elts, All]

theorem all_nil {p : Pos} : All p [] := by simp [All]

theorem all_cons {p : Pos} {x : Ast} {xs : List Ast} (a : W p x) (b : All p xs) :
    All p (x :: xs) := by
  intro y hy
  rcases List.mem_cons.1 hy with e | e
  · exact e ▸ a
  · exact b y e

theorem noNull_nil : NoNull [] := by simp [NoNull]

theorem noNull_cons {x : Ast} {xs : List Ast} (a : x ≠ .null) (b : NoNull xs) :
    NoNull (x :: xs) := by
  intro h
  rcases List.mem_cons.1 h with e | e
  · exact a e.symm
  · exact b e

theorem isNull_eq {a : Ast} : isNull a = true ↔ a = .null := by
  cases a <;> simp [isNull]

/-- A `None` in an expression position is a leaf: whether it may be there is the parent's rule. -/
theorem w_null_expr (c : Ctor) : W (.expr c) .null := W.leaf trivial (by simp)

/-- `r` is accepted only if `G`. -/
def Ac (r : V) (G : Prop) : Prop := r = ok1 → G

theorem Ac.seq {a : V} {b : Unit → V} {A G : Prop} (ha : Ac a A) (k : A → Ac (b ()) G) :
    Ac (a.and b) G := by
  intro e
  cases a with
  | ok u =>
    cases u
    exact k (ha rfl) e
  | error x => cases e

theorem Ac.last {a : V} {A G : Prop} (ha : Ac a A) (k : A → G) : Ac a G := fun e => k (ha e)

theorem Ac.ok' {G : Prop} (g : G) : Ac ok1 G := fun _ => g

theorem Ac.always {r : V} {G : Prop} (g : G) : Ac r G := fun _ => g

theorem Ac.verr {G : Prop} (m : String) : Ac (verr m) G := fun h => by cases h

theorem Ac.terr {G : Prop} (m : String) : Ac (terr m) G := fun h => by cases h

theorem Ac.fuel {G : Prop} : Ac (.error .modelFuel) G := fun h => by cases h

theorem Ac.ite {c : Prop} [Decidable c] {x y : V} {G : Prop} (hx : c → Ac x G) (hy : ¬c → Ac y G) :
    Ac (if c then x else y) G := by
  by_cases h : c
  · rw [if_pos h]
    exact hx h
  · rw [if_neg h]
    exact hy h

theorem positions_ok (l : Option Loc) : Ac (validatePositions l) (posOk l) := by
  intro e
  cases l with
  | none => trivial
  | some l =>
    unfold validatePositions at e
    simp only at e
    split at e
    · cases e
    · split at e
      · cases e
      · split at e
        · cases e
        · rename_i h1 h2 h3
          simp only [posOk]
          simp at h1 h2 h3
          refine ⟨h1, ?_, ?_, ?_⟩
          · intro hn
            exact h2.1 hn
          · intro hn
            exact h2.2 hn
          · intro he
            exact h3 he

theorem name_ok (n : Ast) : Ac (validateName n) (NameOk n) := by
  intro e
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rintro rfl
      simp [validateName, nullDeref, verr, ok1] at e

theorem capture_ok (n : Ast) : Ac (if isNull n then ok1 else validateCapture n) (CaptureOk n) := by
  refine Ac.ite (fun h _ => Or.inl (isNull_eq.1 h)) (fun _ => ?_)
  intro e
  unfold validateCapture at e
  split at e
  · cases e
  · rename_i hn
    exact Or.inr ⟨hn, name_ok n e⟩

theorem nonempty_ok (s : Ast) (a b : String) : Ac (validateNonemptySeq s a b) (seqLen s ≠ 0) := by
  intro e
  unfold validateNonemptySeq at e
  split at e
  · rename_i h
    simpa using h
  · cases e

theorem names_ok_aux (xs : List Ast) (acc : V)
    (h : (xs.foldl (fun acc n => acc.and fun _ => validateName n) acc) = ok1) :
    acc = ok1 ∧ ∀ n ∈ xs, NameOk n := by
  induction xs generalizing acc with
  | nil => exact ⟨h, by simp⟩
  | cons x xs ih =>
    simp only [List.foldl_cons] at h
    obtain ⟨e, hr⟩ := ih _ h
    have k : Ac (acc.and fun _ => validateName x) (acc = ok1 ∧ NameOk x) := by
      refine Ac.seq (A := acc = ok1) (fun e => e) (fun ha => ?_)
      exact fun e => ⟨ha, name_ok x e⟩
    obtain ⟨a, b⟩ := k e
    refine ⟨a, fun n hn => ?_⟩
    rcases List.mem_cons.1 hn with q | q
    · exact q ▸ b
    · exact hr n q

theorem names_ok (xs : List Ast) :
    Ac (xs.foldl (fun acc n => acc.and fun _ => validateName n) ok1) (∀ n ∈ xs, NameOk n) :=
  fun e => (names_ok_aux xs ok1 e).2

theorem exprCtx_error_ne {c : Ctor} {fs : List Ast} {ctx : Ctor} {e : V}
    (h : exprCtx c fs ctx = .error e) : e ≠ ok1 := by
  unfold exprCtx at h
  split at h
  any_goals cases h
  · split at h
    · cases h
    · rename_i e' he
      cases h
      exact he
  · split at h
    · cases h
      intro q
      cases q
    · cases h

theorem exprHead_default {ctx : Ctor} {c : Ctor} {fs : List Ast}
    (h1 : ∀ a b x, c = .Attribute → fs = [a, b, x] → False)
    (h2 : ∀ a b x, c = .Subscript → fs = [a, b, x] → False)
    (h3 : ∀ a x, c = .Starred → fs = [a, x] → False)
    (h4 : ∀ a x, c = .Name → fs = [a, x] → False)
    (h5 : ∀ a x, c = .List → fs = [a, x] → False)
    (h6 : ∀ a x, c = .Tuple → fs = [a, x] → False) (hl : ctx = .Load) : exprHead ctx c fs := by
  unfold exprHead
  split
  · exact (h1 _ _ _ rfl rfl).elim
  · exact (h2 _ _ _ rfl rfl).elim
  · exact (h3 _ _ rfl rfl).elim
  · exact (h5 _ _ rfl rfl).elim
  · exact (h6 _ _ rfl rfl).elim
  · exact (h4 _ _ rfl rfl).elim
  · exact hl

/-- What the first switch established. -/
theorem exprCtx_ok {c : Ctor} {fs : List Ast} {ctx : Ctor} {a : Option Ctor}
    (h : exprCtx c fs ctx = .ok a) :
    (∀ x, a = some x → x = ctx → exprHead ctx c fs) ∧ (a = none → exprHead ctx c fs) := by
  unfold exprCtx at h
  split at h
  · cases h
    exact ⟨fun _ e q => by cases e; simpa [exprHead] using q, by simp⟩
  · cases h
    exact ⟨fun _ e q => by cases e; simpa [exprHead] using q, by simp⟩
  · cases h
    exact ⟨fun _ e q => by cases e; simpa [exprHead] using q, by simp⟩
  · rename_i id x
    split at h
    · rename_i hv
      cases h
      exact ⟨fun _ e q => by
        cases e
        simp only [exprHead]
        exact ⟨name_ok id hv, q⟩, by simp⟩
    · cases h
  · cases h
    exact ⟨fun _ e q => by cases e; simpa [exprHead] using q, by simp⟩
  · cases h
    exact ⟨fun _ e q => by cases e; simpa [exprHead] using q, by simp⟩
  · rename_i h1 h2 h3 h4 h5 h6
    split at h
    · cases h
    · rename_i hl
      cases h
      have hl' : ctx = .Load := by simpa using hl
      exact ⟨by simp, fun _ => exprHead_default h1 h2 h3 h4 h5 h6 hl'⟩

theorem number_lit {e : Ast} {r i : Bool} (h : ensureLiteralNumber e r i = true) :
    NumLit r i e := by
  unfold ensureLiteralNumber at h
  split at h
  · split at h <;> first
      | (exfalso
         cases h
         done)
      | simp [NumLit, h]
  · cases h

theorem negative_lit {e : Ast} {r i : Bool} (h : ensureLiteralNegative e r i = true) :
    NegLit r i e := by
  unfold ensureLiteralNegative at h
  split at h
  · split at h
    · exact number_lit h
    · cases h
  · cases h

theorem complex_lit {e : Ast} (h : ensureLiteralComplex e = true) : ComplexLit e := by
  unfold ensureLiteralComplex at h
  split at h
  · rename_i left op right l
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hop, hl⟩, hr⟩ := h
    have hl' : NumLit true false left ∨ NegLit true false left := by
      revert hl
      split
      · exact fun q => Or.inl (number_lit q)
      · exact fun q => Or.inr (negative_lit q)
      · exact fun q => by cases q
    have hr' : NumLit false true right := by
      revert hr
      split
      · exact fun q => number_lit q
      · exact fun q => by cases q
    revert hop
    split
    · exact fun _ => ⟨hl', hr'⟩
    · exact fun _ => ⟨hl', hr'⟩
    · exact fun q => by cases q
  · cases h

theorem ok_triv : OK ((True : Prop), ([] : List (Pos × Ast))) := ⟨trivial, by simp [Kids]⟩

/-- All the validators together. -/
structure AC (f : Nat) : Prop where
  comprehension : ∀ g, Ac (validateComprehension f g) (seqLen g ≠ 0 ∧ All .comp (seqL g))
  comps : ∀ xs, Ac (validateComps f xs) (All .comp xs)
  keywords : ∀ xs, Ac (validateKeywords f xs) (All .kw xs)
  args : ∀ xs, Ac (validateArgs f xs) (All .arg xs)
  optArg : ∀ a, Ac (validateOptArgAnnotation f a) (W .optArg a)
  arguments : ∀ a, Ac (validateArguments f a) (W .arguments a)
  expr : ∀ e c, Ac (validateExpr f e c) (W (.expr c) e)
  body : ∀ c fs ctx, Ac (validateExprBody f c fs ctx) (OK (exprBody ctx c fs))
  exprs : ∀ xs c b, Ac (validateExprs f xs c b) (All (.expr c) xs ∧ (b = false → NoNull xs))
  matchValue : ∀ e, Ac (validateMatchValue f e) (W .value e)
  keys : ∀ xs, Ac (validateMappingKeys f xs) (All .key xs)
  pattern : ∀ p b, Ac (validatePattern f p b) (W (.pat b) p)
  classRoot : ∀ c, Ac (classRoot f c) (W .cls c)
  patterns : ∀ xs b, Ac (validatePatterns f xs b) (All (.pat b) xs)
  assign : ∀ t c, Ac (validateAssignlist f t c)
    (seqLen t ≠ 0 ∧ NoNull (seqL t) ∧ All (.expr c) (seqL t))
  bodyS : ∀ b n, Ac (validateBody f b n) (BodyOk b ∧ All .stmt (seqL b))
  withItems : ∀ xs, Ac (validateWithItems f xs) (All .item xs)
  cases : ∀ xs, Ac (validateCases f xs) (All .case_ xs)
  handlers : ∀ xs p, Ac (validateHandlers f xs p) (All (.handler p) xs)
  try_ : ∀ n b hs o fb p, Ac (validateTry f n b hs o fb p) (OK (trySpec b hs o fb p))
  typeParam : ∀ t, Ac (validateTypeParam f t) (W .tparam t)
  typeParams : ∀ xs, Ac (validateTypeParams f xs) (All .tparam xs)
  stmt : ∀ s, Ac (validateStmt f s) (W .stmt s)
  stmts : ∀ xs, Ac (validateStmts f xs) (All .stmt xs ∧ NoNull xs)

theorem ac_zero : AC 0 := by
  constructor
  all_goals (intros; simp only [validateComprehension, validateComps, validateKeywords, validateArgs,
    validateOptArgAnnotation, validateArguments, validateExpr, validateExprBody, validateExprs,
    validateMatchValue, validateMappingKeys, validatePattern, classRoot, validatePatterns,
    validateAssignlist, validateBody, validateWithItems, validateCases, validateHandlers,
    validateTry, validateTypeParam, validateTypeParams, validateStmt, validateStmts]; exact Ac.fuel)

theorem AC.exprsF {f : Nat} (h : AC f) (xs : List Ast) (c : Ctor) :
    Ac (validateExprs f xs c false) (All (.expr c) xs ∧ NoNull xs) :=
  fun e => have a := h.exprs xs c false e; ⟨a.1, a.2 rfl⟩

theorem AC.exprsT {f : Nat} (h : AC f) (xs : List Ast) (c : Ctor) :
    Ac (validateExprs f xs c true) (All (.expr c) xs) :=
  fun e => (h.exprs xs c true e).1

theorem AC.opt {f : Nat} (h : AC f) (v : Ast) (c : Ctor) :
    Ac (if isNull v then ok1 else validateExpr f v c) (W (.expr c) v) := by
  refine Ac.ite (fun e _ => ?_) (fun _ => h.expr v c)
  rw [isNull_eq.1 e]
  exact w_null_expr c

theorem AC.optTp {f : Nat} (h : AC f) (t : Ast) :
    Ac (if isNull t then ok1 else validateTypeParam f t) (W .tparam t) := by
  refine Ac.ite (fun e _ => ?_) (fun _ => h.typeParam t)
  rw [isNull_eq.1 e]
  exact W.leaf trivial (by simp)

theorem pos_if (p : Bool) (l : Option Loc) :
    Ac (if p then validatePositions l else ok1) (p = true → posOk l) :=
  Ac.ite (fun _ e _ => positions_ok l e) (fun hp _ q => (hp q).elim)

set_option hygiene false in
/-- The calls a validator makes. -/
macro "ac_call" : tactic => `(tactic| first
  | with_reducible exact positions_ok _
  | with_reducible exact pos_if _ _
  | with_reducible exact nonempty_ok _ _ _
  | with_reducible exact name_ok _
  | with_reducible exact capture_ok _
  | with_reducible exact names_ok _
  | with_reducible exact h.expr _ _
  | with_reducible exact h.opt _ _
  | with_reducible exact h.optTp _
  | with_reducible exact h.exprsF _ _
  | with_reducible exact h.exprsT _ _
  | with_reducible exact h.comprehension _
  | with_reducible exact h.keywords _
  | with_reducible exact h.arguments _
  | with_reducible exact h.assign _ _
  | with_reducible exact h.bodyS _ _
  | with_reducible exact h.withItems _
  | with_reducible exact h.cases _
  | with_reducible exact h.typeParams _
  | with_reducible exact h.try_ _ _ _ _ _ _
  | with_reducible exact h.matchValue _
  | with_reducible exact h.classRoot _
  | with_reducible exact h.patterns _ _
  | with_reducible exact h.pattern _ _
  | with_reducible exact h.keys _
  | with_reducible exact h.stmts _)

/-- Discharge what an accepted branch owes, from what the calls established. -/
macro "ac_close" : tactic => `(tactic| first
  | assumption
  | (simp only [OK, BodyOk, kids_nil, kids_cons, kids_append, kids_elts, and_true, true_and]
     simp_all [isNull_eq, isNameNode, w_null_expr, kids_nil, kids_cons, kids_append, kids_elts, OK,
       BodyOk, IsSingleton]))

set_option hygiene false in
/-- Run a validator's body forward. -/
macro "ac" : tactic => `(tactic| repeat' (first
  | with_reducible exact Ac.verr _
  | with_reducible exact Ac.terr _
  | ((with_reducible apply Ac.seq); ac_call; intro _)
  | ((with_reducible apply Ac.last); ac_call; intro _)
  | with_reducible refine Ac.ok' ?_
  | (with_reducible refine Ac.ite ?_ ?_; all_goals intro _)
  | dsimp only
  | split
  | ac_close))

theorem Ac.null {G : Prop} : Ac nullDeref G := fun e => by simp [nullDeref, ok1] at e

/-- The `neg` of `ImportFrom`. -/
theorem level_ok {lv : Ast} (h : (match lv with
      | .int v => decide (v < 0)
      | _ => false) = false) : LevelOk lv := by
  cases lv <;> simp_all [LevelOk]

/-- What `ac` leaves in `validate_stmt`: `AnnAssign`, `Raise` and `ImportFrom`. -/
macro "ac_rest" : tactic => `(tactic| first
  | exact level_ok (by assumption)
  | (intro q
     subst q
     simp_all [isNull])
  | (rename_i a3 _ _ _ _ _
     have q := a3 (by split <;> simp_all)
     refine Or.inr ?_
     revert q
     split
     · exact fun _ => rfl
     · exact fun e => by cases e))

theorem w_triv {p : Pos} {c : Ctor} {fs : List Ast} {l : Option Loc}
    (e : spec p c fs l = ((True : Prop), [])) : W p (.node c fs l) :=
  W.mk (by rw [e]; exact ok_triv)

theorem w_comp_other {x : Ast} (hx : ∀ c t i ifs y l, x = .node c [t, i, ifs, y] l → False) :
    W .comp x := by
  cases x with
  | node c fs l =>
    refine w_triv ?_
    show compSpec fs = _
    unfold compSpec
    split
    · exact (hx c _ _ _ _ l rfl).elim
    · rfl
  | _ => exact W.leaf trivial (by simp)

theorem w_kw_other {x : Ast} (hx : ∀ c n v l, x = .node c [n, v] l → False) : W .kw x := by
  cases x with
  | node c fs l =>
    refine w_triv ?_
    show kwSpec fs = _
    unfold kwSpec
    split
    · exact (hx c _ _ l rfl).elim
    · rfl
  | _ => exact W.leaf trivial (by simp)

theorem w_arg_other {x : Ast} (hx : ∀ c n a y l, x = .node c [n, a, y] l → False) : W .arg x := by
  cases x with
  | node c fs l =>
    refine w_triv ?_
    show argSpec l fs = _
    unfold argSpec
    split
    · exact (hx c _ _ _ l rfl).elim
    · rfl
  | _ => exact W.leaf trivial (by simp)

theorem w_optArg_other {x : Ast} (hx : ∀ c n a y l, x = .node c [n, a, y] l → False) :
    W .optArg x := by
  cases x with
  | node c fs l =>
    refine w_triv ?_
    show optArgSpec fs = _
    unfold optArgSpec
    split
    · exact (hx c _ _ _ l rfl).elim
    · rfl
  | _ => exact W.leaf trivial (by simp)

theorem w_arguments_other {x : Ast}
    (hx : ∀ c a b d e g i j l, x = .node c [a, b, d, e, g, i, j] l → False) : W .arguments x := by
  cases x with
  | node c fs l =>
    refine w_triv ?_
    show argumentsSpec fs = _
    unfold argumentsSpec
    split
    · exact (hx c _ _ _ _ _ _ _ l rfl).elim
    · rfl
  | _ => exact W.leaf trivial (by simp)

theorem w_item_other {x : Ast} (hx : ∀ c e v l, x = .node c [e, v] l → False) : W .item x := by
  cases x with
  | node c fs l =>
    refine w_triv ?_
    show itemSpec fs = _
    unfold itemSpec
    split
    · exact (hx c _ _ l rfl).elim
    · rfl
  | _ => exact W.leaf trivial (by simp)

theorem w_case_other {x : Ast} (hx : ∀ p g b l, x = .node .match_case_ [p, g, b] l → False) :
    W .case_ x := by
  cases x with
  | node c fs l =>
    refine w_triv ?_
    show caseSpec c fs = _
    unfold caseSpec
    split
    · exact (hx _ _ _ l rfl).elim
    · rfl
  | _ => exact W.leaf trivial (by simp)

theorem w_handler_other {p : Bool} {x : Ast} (hn : x ≠ .null)
    (hx : ∀ c ty n b l, x = .node c [ty, n, b] l → False) : W (.handler p) x := by
  cases x with
  | node c fs l =>
    refine w_triv ?_
    show handlerSpec p l fs = _
    unfold handlerSpec
    split
    · exact (hx c _ _ _ l rfl).elim
    · rfl
  | _ => exact W.leaf (by first | exact absurd rfl hn | simp [leafOk]) (by simp)

theorem ac_succ {f : Nat} (h : AC f) : AC (f + 1) := by
  constructor
  · intro g
    rw [validateComprehension.eq_def]
    simp only []
    exact Ac.ite (fun _ => Ac.verr _)
      (fun hn => Ac.last (h.comps _) fun a => ⟨by simpa using hn, a⟩)
  · intro xs
    rw [validateComps.eq_def]
    simp only []
    split
    · exact Ac.ok' all_nil
    · refine Ac.seq (h.expr _ _) fun a1 => Ac.seq (h.expr _ _) fun a2 =>
        Ac.seq (h.exprsF _ _) fun a3 => Ac.last (h.comps _) fun a4 => all_cons (W.mk ?_) a4
      simp only [OK, spec, compSpec, kids_cons, kids_elts]
      exact ⟨a3.2, a1, a2, a3.1⟩
    · rename_i x rest hn
      exact Ac.last (h.comps rest) fun a => all_cons
        (w_comp_other fun _ _ _ _ _ _ e => by subst e; exact hn _ _ _ _ _ _ rfl) a
  · intro xs
    rw [validateKeywords.eq_def]
    simp only []
    split
    · exact Ac.ok' all_nil
    · refine Ac.seq (h.expr _ _) fun a1 => Ac.last (h.keywords _) fun a2 =>
        all_cons (W.mk ?_) a2
      simp only [OK, spec, kwSpec, kids_cons, kids_nil]
      exact ⟨trivial, a1, trivial⟩
    · rename_i x rest hn
      exact Ac.last (h.keywords rest) fun a => all_cons
        (w_kw_other fun _ _ _ _ e => by subst e; exact hn _ _ _ _ rfl) a
  · intro xs
    rw [validateArgs.eq_def]
    simp only []
    split
    · exact Ac.ok' all_nil
    · refine Ac.seq (positions_ok _) fun a0 => Ac.seq (h.opt _ _) fun a1 =>
        Ac.last (h.args _) fun a2 => all_cons (W.mk ?_) a2
      simp only [OK, spec, argSpec, kids_cons, kids_nil]
      exact ⟨a0, a1, trivial⟩
    · rename_i x rest hn
      exact Ac.last (h.args rest) fun a => all_cons
        (w_arg_other fun _ _ _ _ _ e => by subst e; exact hn _ _ _ _ _ rfl) a
  · intro a
    rw [validateOptArgAnnotation.eq_def]
    simp only []
    split
    · refine Ac.last (h.opt _ _) fun a1 => W.mk ?_
      simp only [OK, spec, optArgSpec, kids_cons, kids_nil]
      exact ⟨trivial, a1, trivial⟩
    · rename_i hn
      exact Ac.always (w_optArg_other fun _ _ _ _ _ e => hn _ _ _ _ _ e)
  · intro a
    rw [validateArguments.eq_def]
    simp only []
    split
    · refine Ac.seq (h.args _) fun a1 => Ac.seq (h.args _) fun a2 => Ac.seq (h.optArg _) fun a3 =>
        Ac.seq (h.args _) fun a4 => Ac.seq (h.optArg _) fun a5 => ?_
      refine Ac.ite (fun _ => Ac.verr _) fun n1 => Ac.ite (fun _ => Ac.verr _) fun n2 =>
        Ac.seq (h.exprsF _ _) fun a6 => Ac.last (h.exprsT _ _) fun a7 => W.mk ?_
      simp only [OK, spec, argumentsSpec, kids_cons, kids_append, kids_elts]
      exact ⟨⟨by simpa using n1, by simpa using n2, a6.2⟩,
        ⟨⟨⟨⟨a1, a2⟩, a3, a4⟩, a5, a6.1⟩, a7⟩⟩
    · rename_i hn
      exact Ac.always (w_arguments_other fun _ _ _ _ _ _ _ _ _ e => hn _ _ _ _ _ _ _ _ _ e)
  · intro e ctx
    cases e with
    | node c fs l =>
      rw [validateExpr.eq_def]
      simp only []
      refine Ac.seq (positions_ok l) fun hp => ?_
      try dsimp only
      split
      · rename_i e' he
        exact fun q => (exprCtx_error_ne he q).elim
      · rename_i a ha
        obtain ⟨k1, k2⟩ := exprCtx_ok ha
        split
        · rename_i x
          refine Ac.ite (fun _ => Ac.verr _) fun hn => Ac.last (h.body _ _ _) fun b => W.mk ?_
          exact ⟨⟨hp, k1 x rfl (by simpa using hn), b.1⟩, b.2⟩
        · exact Ac.last (h.body _ _ _) fun b => W.mk ⟨⟨hp, k2 rfl, b.1⟩, b.2⟩
    | _ => exact Ac.always (W.leaf trivial (by simp))
  · intro c fs ctx
    unfold exprBody
    split
    all_goals first
      | exact Ac.always ok_triv
      | (rw [validateExprBody.eq_def]
         simp only []
         ac)
  · intro xs c b
    rw [validateExprs.eq_def]
    simp only []
    split
    · exact Ac.ok' ⟨all_nil, fun _ => noNull_nil⟩
    · rename_i e rest
      refine Ac.ite (fun hn => ?_) (fun hn => ?_)
      · refine Ac.ite (fun hb => ?_) (fun _ => Ac.verr _)
        refine Ac.last (h.exprs _ _ _) fun a => ⟨?_, fun q => ?_⟩
        · rw [isNull_eq.1 hn]
          exact all_cons (w_null_expr c) a.1
        · simp [q] at hb
      · exact Ac.seq (h.expr _ _) fun a1 => Ac.last (h.exprs _ _ _) fun a2 =>
          ⟨all_cons a1 a2.1, fun q => noNull_cons (fun en => hn (isNull_eq.2 en)) (a2.2 q)⟩
  · intro e
    rw [validateMatchValue.eq_def]
    simp only []
    refine Ac.seq (h.expr _ _) fun a => ?_
    try dsimp only
    split <;> try split
    all_goals first
      | exact Ac.verr _
      | (refine Ac.ok' (W.value ?_ a)
         first
           | (rename_i hq
              exact negative_lit hq)
           | (rename_i hq
              exact complex_lit hq)
           | simp_all [LiteralOk, ConstLit])
  · intro xs
    rw [validateMappingKeys.eq_def]
    simp only []
    split
    · exact Ac.ok' all_nil
    · exact Ac.null
    · rename_i key rest hn
      have hr := h.keys rest
      split
      · exact Ac.last hr fun a => all_cons (W.singleton (by simp [SingletonKey])) a
      · exact Ac.last hr fun a => all_cons (W.singleton (by simp [SingletonKey])) a
      · exact Ac.last hr fun a => all_cons (W.singleton (by simp [SingletonKey])) a
      · exact Ac.seq (h.matchValue _) fun a1 => Ac.last hr fun a2 =>
          all_cons (W.keyValue a1) a2
  · intro p b
    cases p with
    | null =>
      rw [validatePattern.eq_def]
      simp only []
      exact Ac.null
    | node c fs l =>
      refine Ac.last (A := posOk l ∧ OK (patSpec b c fs)) ?_
        (fun a => W.mk ⟨⟨a.1, a.2.1⟩, a.2.2⟩)
      unfold patSpec
      split
      all_goals
        rw [validatePattern.eq_def]
        simp only []
        refine Ac.seq (positions_ok l) fun hp => ?_
        try dsimp only
        first
          | exact Ac.always ⟨hp, ok_triv⟩
          | ac
    | _ => exact Ac.always (W.leaf (by simp [leafOk]) (by simp))
  · intro c
    rw [classRoot.eq_def]
    simp only []
    split
    · exact Ac.ok' W.clsName
    · exact Ac.last (h.classRoot _) fun a => W.clsAttr a
    · exact Ac.verr _
  · intro xs b
    rw [validatePatterns.eq_def]
    simp only []
    split
    · exact Ac.ok' all_nil
    · exact Ac.seq (h.pattern _ _) fun a1 => Ac.last (h.patterns _ _) fun a2 => all_cons a1 a2
  · intro t c
    rw [validateAssignlist.eq_def]
    simp only []
    exact Ac.seq (nonempty_ok _ _ _) fun a => Ac.last (h.exprsF _ _) fun b => ⟨a, b.2, b.1⟩
  · intro b n
    rw [validateBody.eq_def]
    simp only []
    exact Ac.seq (nonempty_ok _ _ _) fun a => Ac.last (h.stmts _) fun b => ⟨⟨a, b.2⟩, b.1⟩
  · intro xs
    rw [validateWithItems.eq_def]
    simp only []
    split
    · exact Ac.ok' all_nil
    · refine Ac.seq (h.expr _ _) fun a1 => Ac.seq (h.opt _ _) fun a2 =>
        Ac.last (h.withItems _) fun a3 => all_cons (W.mk ?_) a3
      simp only [OK, spec, itemSpec, kids_cons, kids_nil]
      exact ⟨trivial, a1, a2, trivial⟩
    · rename_i x rest hn
      exact Ac.last (h.withItems rest) fun a => all_cons
        (w_item_other fun _ _ _ _ e => by subst e; exact hn _ _ _ _ rfl) a
  · intro xs
    rw [validateCases.eq_def]
    simp only []
    split
    · exact Ac.ok' all_nil
    · refine Ac.seq (h.pattern _ _) fun a1 => Ac.seq (h.opt _ _) fun a2 =>
        Ac.seq (h.bodyS _ _) fun a3 => Ac.last (h.cases _) fun a4 => all_cons (W.mk ?_) a4
      simp only [OK, spec, caseSpec, kids_cons, kids_elts]
      exact ⟨a3.1, a1, a2, a3.2⟩
    · rename_i x rest hn
      exact Ac.last (h.cases rest) fun a => all_cons
        (w_case_other fun _ _ _ _ e => by subst e; exact hn _ _ _ _ rfl) a
  · intro xs p
    rw [validateHandlers.eq_def]
    simp only []
    split
    · exact Ac.ok' all_nil
    · exact Ac.null
    · refine Ac.seq (pos_if _ _) fun a0 => Ac.seq (h.opt _ _) fun a1 =>
        Ac.seq (h.bodyS _ _) fun a2 => Ac.last (h.handlers _ _) fun a3 => all_cons (W.mk ?_) a3
      simp only [OK, spec, handlerSpec, kids_cons, kids_elts]
      exact ⟨⟨a0, a2.1⟩, a1, a2.2⟩
    · rename_i x rest hn1 hn2
      exact Ac.last (h.handlers rest p) fun a => all_cons
        (w_handler_other (fun e => by subst e; exact hn1 rfl)
          fun _ _ _ _ _ e => by subst e; exact hn2 _ _ _ _ _ rfl) a
  · intro n b hd o fb p
    rw [validateTry.eq_def]
    simp only []
    refine Ac.seq (h.bodyS _ _) fun a1 => ?_
    refine Ac.ite (fun _ => Ac.verr _) fun n1 => Ac.ite (fun _ => Ac.verr _) fun n2 => ?_
    refine Ac.seq (h.handlers _ _) fun a2 => Ac.seq (h.stmts _) fun a3 =>
      Ac.last (h.stmts _) fun a4 => ?_
    simp only [OK, trySpec, kids_append, kids_elts]
    refine ⟨⟨a1.1, a3.2, a4.2, ?_, ?_⟩, ⟨⟨a1.2, a2⟩, a3.1⟩, a4.1⟩
    · simp at n1
      omega
    · simp at n2
      omega
  · intro t
    cases t with
    | node c fs l =>
      refine Ac.last (A := posOk l ∧ OK (tparamSpec c fs)) ?_
        (fun a => W.mk ⟨⟨a.1, a.2.1⟩, a.2.2⟩)
      unfold tparamSpec
      split
      all_goals
        rw [validateTypeParam.eq_def]
        simp only []
        refine Ac.seq (positions_ok l) fun hp => ?_
        try dsimp only
        first
          | exact Ac.always ⟨hp, ok_triv⟩
          | ac
    | _ => exact Ac.always (W.leaf trivial (by simp))
  · intro xs
    rw [validateTypeParams.eq_def]
    simp only []
    split
    · exact Ac.ok' all_nil
    · exact Ac.seq (h.optTp _) fun a1 => Ac.last (h.typeParams _) fun a2 => all_cons a1 a2
  · intro s
    cases s with
    | node c fs l =>
      refine Ac.last (A := posOk l ∧ OK (stmtSpec c fs)) ?_
        (fun a => W.mk ⟨⟨a.1, a.2.1⟩, a.2.2⟩)
      unfold stmtSpec
      split
      all_goals
        rw [validateStmt.eq_def]
        simp only []
        refine Ac.seq (positions_ok l) fun hp => ?_
        try dsimp only
        first
          | exact Ac.always ⟨hp, ok_triv⟩
          | (ac
             all_goals ac_rest)
    | _ => exact Ac.always (W.leaf trivial (by simp))
  · intro xs
    rw [validateStmts.eq_def]
    simp only []
    split
    · exact Ac.ok' ⟨all_nil, noNull_nil⟩
    · rename_i s rest
      exact Ac.ite (fun _ => Ac.verr _) fun hn => Ac.seq (h.stmt _) fun a =>
        Ac.last (h.stmts _) fun b =>
          ⟨all_cons a b.1, noNull_cons (fun en => hn (isNull_eq.2 en)) b.2⟩

theorem ac_all (f : Nat) : AC f := by
  induction f with
  | zero => exact ac_zero
  | succ f ih => exact ac_succ ih

/-- `_PyAST_Validate` accepts only trees that satisfy `spec` at every position: every validator
refuses what its row refuses, at any depth, for every tree. There is no hypothesis on the tree. -/
def ValidateRejects : Prop := ∀ m : Ast, validate m = ok1 → W .module m

theorem validateRejects_proven : ValidateRejects := by
  intro m
  unfold validate
  dsimp only
  split
  · refine Ac.last ((ac_all _).stmts _) fun a => W.mk ?_
    simp only [OK, spec, modSpec, kids_elts]
    exact ⟨a.2, a.1⟩
  · refine Ac.last ((ac_all _).stmts _) fun a => W.mk ?_
    simp only [OK, spec, modSpec, kids_elts]
    exact ⟨a.2, a.1⟩
  · refine Ac.last ((ac_all _).expr _ _) fun a => W.mk ?_
    simp only [OK, spec, modSpec, kids_cons, kids_nil]
    exact ⟨trivial, a, trivial⟩
  · refine Ac.seq ((ac_all _).exprsF _ _) fun a => Ac.last ((ac_all _).expr _ _) fun b => W.mk ?_
    simp only [OK, spec, modSpec, kids_append, kids_elts, kids_cons, kids_nil]
    exact ⟨a.2, a.1, b, trivial⟩
  · intro e
    simp [ok1] at e

end PyLean.PyGrammar.Check
