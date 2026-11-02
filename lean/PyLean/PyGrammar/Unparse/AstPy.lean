import PyLean.PyGrammar.Check.Preprocess
import PyLean.PyGrammar.Unparse.Python

/-!
The tree utilities of `Lib/ast.py`, over the shared `Ast`. Every located node of an `Ast` has
all four attributes, so the `hasattr` branches of the source take their "present" side.
-/

namespace PyLean.PyGrammar.Unparse

open PyLean Lexer

/-! ### `increment_lineno` -/

/-- `TypeIgnore` keeps its line in a field: `child.lineno = getattr(child, 'lineno', 0) + n`. -/
def bumpHead (n : Int) : List Ast → List Ast
  | .int v :: r => .int (v + n) :: r
  | fs => fs

/-- Move a location by `n` lines. -/
def moveLoc (n : Int) (x : Loc) : Loc :=
  { x with lineno := x.lineno + n, endLineno := x.endLineno + n }

mutual
  /-- `increment_lineno`, `Lib/ast.py:281-301`: every located node, and the `lineno` field of
  `TypeIgnore`, moves by `n`. -/
  def incrementLineno (n : Int) : Ast → Ast
    | .node c fs l =>
      if c == .TypeIgnore then .node c (bumpHead n fs) (l.map (moveLoc n))
      else .node c (incrementList n fs) (l.map (moveLoc n))
    | .seq xs => .seq (incrementList n xs)
    | a => a

  /-- `incrementLineno` over a list of fields. -/
  def incrementList (n : Int) : List Ast → List Ast
    | [] => []
    | x :: xs => incrementLineno n x :: incrementList n xs
end

theorem bumpHead_inv (n : Int) (fs : List Ast) : bumpHead (-n) (bumpHead n fs) = fs := by
  cases fs with
  | nil => rfl
  | cons x xs =>
    cases x <;> simp [bumpHead] <;> omega

theorem moveLoc_inv (n : Int) (l : Option Loc) :
    (l.map (moveLoc n)).map (moveLoc (-n)) = l := by
  cases l with
  | none => rfl
  | some x =>
    simp only [Option.map, moveLoc]
    cases x
    simp
    omega

theorem incr_true (n : Int) (c : Ctor) (fs : List Ast) (l : Option Loc)
    (h : (c == .TypeIgnore) = true) :
    incrementLineno n (.node c fs l) = .node c (bumpHead n fs) (l.map (moveLoc n)) := by
  simp [incrementLineno, h]

theorem incr_false (n : Int) (c : Ctor) (fs : List Ast) (l : Option Loc)
    (h : ¬ (c == .TypeIgnore) = true) :
    incrementLineno n (.node c fs l) = .node c (incrementList n fs) (l.map (moveLoc n)) := by
  simp [incrementLineno, h]

mutual
  theorem incrementLineno_inv (n : Int) : ∀ t : Ast, incrementLineno (-n) (incrementLineno n t) = t
    | .node c fs l => by
      by_cases h : (c == .TypeIgnore) = true
      · rw [incr_true _ _ _ _ h, incr_true _ _ _ _ h, bumpHead_inv, moveLoc_inv]
      · rw [incr_false _ _ _ _ h, incr_false _ _ _ _ h, incrementList_inv n fs, moveLoc_inv]
    | .seq xs => by simp [incrementLineno, incrementList_inv n xs]
    | .null | .ident _ | .str _ | .int _ | .const _ | .tok _ => by simp [incrementLineno]

  theorem incrementList_inv (n : Int) : ∀ l : List Ast, incrementList (-n) (incrementList n l) = l
    | [] => rfl
    | x :: xs => by simp [incrementList, incrementLineno_inv n x, incrementList_inv n xs]
end

/-- `increment_lineno(increment_lineno(t, n), -n)` is `t`: "move code" is reversible, for every
tree and every `n`. -/
def IncrementLinenoReversible : Prop :=
  ∀ (n : Int) (t : Ast), incrementLineno (-n) (incrementLineno n t) = t

theorem incrementLinenoReversible_proven : IncrementLinenoReversible :=
  fun n t => incrementLineno_inv n t

/-! ### `_splitlines_no_ff`, `_pad_whitespace` -/

/-- One match of `(.*?(?:\r\n|\n|\r|$))`. -/
def lineMatch : List Nat → List Nat × List Nat
  | [] => ([], [])
  | 13 :: 10 :: r => ([13, 10], r)
  | 10 :: r => ([10], r)
  | 13 :: r => ([13], r)
  | c :: r => (c :: (lineMatch r).1, (lineMatch r).2)

theorem lineMatch_append (s : List Nat) : (lineMatch s).1 ++ (lineMatch s).2 = s := by
  fun_induction lineMatch s <;> simp_all

theorem lineMatch_ne (s : List Nat) (h : s ≠ []) : (lineMatch s).1 ≠ [] := by
  fun_induction lineMatch s <;> simp_all

/-- `_splitlines_no_ff`, `Lib/ast.py:355-371`, by `finditer`. -/
def splitNoFF : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | _ + 1, [] => [[]]
  | f + 1, c :: r => (lineMatch (c :: r)).1 :: splitNoFF f (lineMatch (c :: r)).2

/-- The lines are the source, cut: joining them loses nothing. -/
def SplitLinesLossless : Prop :=
  ∀ (s : List Nat) (f : Nat), s.length < f → (splitNoFF f s).flatten = s

theorem splitLinesLossless_proven : SplitLinesLossless := by
  intro s f
  induction f generalizing s with
  | zero => intro h; simp at h
  | succ f ih =>
    intro h
    cases s with
    | nil => simp [splitNoFF]
    | cons c r =>
      have ha := lineMatch_append (c :: r)
      have hn := lineMatch_ne (c :: r) (by simp)
      have hl : (lineMatch (c :: r)).1.length + (lineMatch (c :: r)).2.length = (c :: r).length := by
        rw [← List.length_append, ha]
      have hpos : 0 < (lineMatch (c :: r)).1.length := List.length_pos_iff.mpr hn
      simp only [splitNoFF, List.flatten_cons]
      rw [ih _ (by omega), ha]

/-- `_pad_whitespace`, `Lib/ast.py:374-382`. -/
def padWhitespace (s : List Nat) : List Nat :=
  s.map fun c => if c == 12 || c == 9 then c else 32

/-- The padding keeps the column of whatever follows it, tab stops included: it has the
length of the text it replaces and agrees on `\f` and `\t`. -/
def PadKeepsColumns : Prop :=
  ∀ s : List Nat, (padWhitespace s).length = s.length ∧
    ∀ c ∈ padWhitespace s, c = 12 ∨ c = 9 ∨ c = 32

theorem padKeepsColumns_proven : PadKeepsColumns := by
  intro s
  constructor
  · simp [padWhitespace]
  · intro c h
    simp only [padWhitespace, List.mem_map] at h
    obtain ⟨x, _, rfl⟩ := h
    split
    · rename_i hx
      simp only [Bool.or_eq_true, beq_iff_eq] at hx
      omega
    · simp

/-! ### Docstrings: three copies of one rule -/

/-- `get_docstring(node, clean=False)`, `Lib/ast.py:330-351`, on a body. -/
def pyGetDocstring (body : List Ast) : Option (List Nat) :=
  match body with
  | .node .Expr (v :: _) _ :: _ =>
    match v with
    | .node .Constant (.const (.str s) :: _) _ => some s
    | _ => none
  | _ => none

/-- `Unparser.get_raw_docstring`'s docstring: "Logic mirrored from `_PyAST_GetDocString`". The
C function and the two Python functions find the same string in every body whose `Expr`
statements have their one field, as an ASDL `Expr` does. -/
def DocstringTwins : Prop :=
  ∀ body : List Ast,
    (∀ c fs l rest, body = .node c fs l :: rest → c = .Expr → fs.length = 1) →
    pyGetDocstring body = Check.getDocString body ∧
    (rawDocstring body).isSome = (Check.getDocString body).isSome

theorem docstringTwins_proven : DocstringTwins := by
  intro body h
  match body with
  | [] => simp [pyGetDocstring, Check.getDocString, rawDocstring]
  | .node c fs l :: rest =>
    by_cases hc : c = .Expr
    · subst hc
      have hl := h _ _ _ _ rfl rfl
      match fs, hl with
      | [v], _ =>
        match v with
        | .node .Constant (.const (.str s) :: _) _ =>
          simp [pyGetDocstring, Check.getDocString, rawDocstring]
        | .node c' fs' l' =>
          simp only [pyGetDocstring, Check.getDocString, rawDocstring]
          split <;> simp_all
        | .seq _ | .null | .ident _ | .str _ | .int _ | .const _ | .tok _ =>
          simp [pyGetDocstring, Check.getDocString, rawDocstring]
    · simp [pyGetDocstring, Check.getDocString, rawDocstring, hc]
  | .seq _ :: _ | .null :: _ | .ident _ :: _ | .str _ :: _ | .int _ :: _ | .const _ :: _
  | .tok _ :: _ => simp [pyGetDocstring, Check.getDocString, rawDocstring]

/-! ### `literal_eval` -/

/-- What `literal_eval` evaluates to. -/
inductive LVal where
  | c (v : PyConst)
  | tuple (xs : List LVal)
  | list (xs : List LVal)
  | set (xs : List LVal)
  | dict (ks vs : List LVal)
  deriving Inhabited

/-- The `raise` at the end of `_convert_literal`, the message's node repr not rendered. -/
def malformed : Except PyExc LVal := .error (.valueError "~malformed node or string")

/-- `type(x) in (int, float, complex)`: an exact test, so a `bool` is refused. -/
def isNumber : PyConst → Bool
  | .int _ | .float _ | .complex _ _ => true
  | _ => false

/-- `type(x) in (int, float)` -/
def isRealConst : PyConst → Bool
  | .int _ | .float _ => true
  | _ => false

/-- `type(x) is complex` -/
def isComplexConst : PyConst → Bool
  | .complex _ _ => true
  | _ => false

/-- `isinstance(node.left, (Constant, UnaryOp))` -/
def isConstOrUnary : Ast → Bool
  | .node .Constant _ _ | .node .UnaryOp _ _ => true
  | _ => false

/-- `isinstance(node.right, Constant)` -/
def isConstantNode : Ast → Bool
  | .node .Constant _ _ => true
  | _ => false

mutual
  /-- `_convert_literal`, `Lib/ast.py:67-114`. -/
  def convert : Nat → Ast → Except PyExc LVal
    | 0, _ => .error .modelFuel
    | f + 1, node =>
      match node with
      | .node .Constant (.const v :: _) _ => .ok (.c v)
      | .node .Dict [keys, values] _ =>
        if (seqU keys).length == (seqU values).length then do
          return .dict (← convertList f (seqU keys)) (← convertList f (seqU values))
        else malformed
      | .node .Tuple (elts :: _) _ => do return .tuple (← convertList f (seqU elts))
      | .node .List (elts :: _) _ => do return .list (← convertList f (seqU elts))
      | .node .Set (elts :: _) _ => do return .set (← convertList f (seqU elts))
      | .node .Call [.node .Name (.ident [115, 101, 116] :: _) _, .seq [], .seq []] _ =>
        .ok (.set [])
      | .node .UnaryOp [.node o _ _, .node .Constant (.const v :: _) _] _ =>
        if (o == .UAdd || o == .USub) && isNumber v then
          if o == .UAdd then .ok (.c v)
          else
            match Check.negConst v with
            | some r => .ok (.c r)
            | none => malformed
        else malformed
      | .node .BinOp [left, .node o _ _, right] _ =>
        if (o == .Add || o == .Sub) && isConstOrUnary left && isConstantNode right then
          match convert f left with
          | .error e => .error e
          | .ok (.c l) =>
            if isRealConst l then
              match convert f right with
              | .error e => .error e
              | .ok (.c r) =>
                if isComplexConst r then
                  match Check.complexArith (o == .Add) l r with
                  | some v => .ok (.c v)
                  | none => .error (.overflowError "int too large to convert to float")
                else malformed
              | .ok _ => malformed
            else malformed
          | .ok _ => malformed
        else malformed
      | _ => malformed

  /-- `map(_convert_literal, seq)` -/
  def convertList : Nat → List Ast → Except PyExc (List LVal)
    | 0, _ => .error .modelFuel
    | _ + 1, [] => .ok []
    | f + 1, x :: xs => do
      let v ← convert f x
      return v :: (← convertList f xs)

end

/-- `literal_eval` "may only consist of" literal structures: a call with arguments is refused,
whatever the callee. -/
def LiteralRefusesCalls : Prop :=
  ∀ (f : Nat) (g a : Ast) (as : List Ast) (kw : Ast) (l : Option Loc),
    ∃ e, convert (f + 1) (.node .Call [g, .seq (a :: as), kw] l) = .error e

theorem literalRefusesCalls_proven : LiteralRefusesCalls := by
  intro f g a as kw l
  simp [convert, malformed]

end PyLean.PyGrammar.Unparse
