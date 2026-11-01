import Lean.Data.Json
import PyLean.PyGrammar.AstGen

/-!
The AST shared by every part of `PyGrammar`.

`Parser/Python.asdl` is read mechanically into `Ctor` (see `gen/gen_ast.py`). A
node is one generic shape, `Ast.node ctor fields loc`, whose `fields` are in ASDL
order, so all consumers (parser actions, `ast_preprocess`, the validator, both
unparsers) share one type and one JSON encoding.

Strings are lists of code points rather than `String`, because a Python `str` may
contain lone surrogates and Lean's `Char` cannot. Floats are IEEE-754 binary64
bit patterns held as `Nat`, so equality is exact and proofs never meet `Float`.
-/

namespace PyLean.PyGrammar

open Lean

/-- A Python object as it can occur in `Constant.value`. -/
inductive PyConst where
  | none | true_ | false_ | ellipsis
  | int (v : Int)
  /-- binary64 bit pattern. -/
  | float (bits : Nat)
  /-- binary64 bit patterns of the real and imaginary parts. -/
  | complex (re im : Nat)
  /-- Code points; may contain surrogates. -/
  | str (cps : List Nat)
  | bytes (bs : List Nat)
  | tuple (xs : List PyConst)
  | frozenset (xs : List PyConst)
  deriving Repr, Inhabited

/-- The four location attributes. An ASDL attribute that is `None` in Python never
arises from the parser; `-1` stands for it in hand-built trees. -/
structure Loc where
  lineno : Int
  colOffset : Int
  endLineno : Int
  endColOffset : Int
  deriving DecidableEq, Repr, Inhabited

/-- A token as the parser stores it (`Token` in `Parser/pegen.h`, without the memo
list, which lives in the parser state). `bytes` is the UTF-8 text of the token. -/
structure Token where
  type : Nat
  bytes : List Nat
  level : Nat
  lineno : Int
  colOffset : Int
  endLineno : Int
  endColOffset : Int
  /-- `Token.metadata`: for f/t-string middle and debug tokens, a Python str. -/
  metadata : Option (List Nat) := none
  deriving DecidableEq, Repr, Inhabited

/-- Generic ASDL tree. Absent optional fields, and C `NULL`, are `.null`. -/
inductive Ast where
  /-- `Ctor(fields…)`, fields in ASDL order. `loc` is `none` exactly when the
  constructor has no location attributes. -/
  | node (c : Ctor) (fields : List Ast) (loc : Option Loc)
  /-- An `asdl_seq`. -/
  | seq (xs : List Ast)
  /-- `NULL` in C, `None` in Python. -/
  | null
  /-- ASDL `identifier`. -/
  | ident (cps : List Nat)
  /-- ASDL `string`. -/
  | str (cps : List Nat)
  /-- ASDL `int`. -/
  | int (v : Int)
  /-- ASDL `constant`. -/
  | const (v : PyConst)
  /-- Parser-internal: a token (never in a finished tree). -/
  | tok (t : Token)
  deriving Repr, Inhabited

namespace PyConst

/-- Structural equality on constants. -/
def beq : PyConst → PyConst → Bool
  | .none, .none | .true_, .true_ | .false_, .false_ | .ellipsis, .ellipsis => true
  | .int a, .int b => a == b
  | .float a, .float b => a == b
  | .complex a b, .complex c d => a == c && b == d
  | .str a, .str b => a == b
  | .bytes a, .bytes b => a == b
  | .tuple a, .tuple b => beqList a b
  | .frozenset a, .frozenset b => beqList a b
  | _, _ => false
where
  beqList : List PyConst → List PyConst → Bool
    | [], [] => true
    | a :: as, b :: bs => beq a b && beqList as bs
    | _, _ => false

instance : BEq PyConst := ⟨beq⟩

end PyConst

namespace Ast

/-- Structural equality, location included. -/
def beq : Ast → Ast → Bool
  | .node c f l, .node c' f' l' => c == c' && beqList f f' && l == l'
  | .seq a, .seq b => beqList a b
  | .null, .null => true
  | .ident a, .ident b => a == b
  | .str a, .str b => a == b
  | .int a, .int b => a == b
  | .const a, .const b => a == b
  | .tok a, .tok b => a == b
  | _, _ => false
where
  beqList : List Ast → List Ast → Bool
    | [], [] => true
    | a :: as, b :: bs => beq a b && beqList as bs
    | _, _ => false

instance : BEq Ast := ⟨beq⟩

/-- Replace every location by `(0,0,0,0)`, keeping which nodes have one: what
`ast.compare(a, b)` looks at with its default `compare_attributes=False`. -/
def stripLoc : Ast → Ast
  | .node c f l => .node c (stripList f) (l.map fun _ => ⟨0, 0, 0, 0⟩)
  | .seq xs => .seq (stripList xs)
  | a => a
where
  stripList : List Ast → List Ast
    | [] => []
    | a :: as => stripLoc a :: stripList as

/-- `ctor` applied to fields, with no location. -/
def mk (c : Ctor) (fields : List Ast := []) : Ast := .node c fields none

/-- Constructor tag, when this is a node. -/
def ctor? : Ast → Option Ctor
  | .node c _ _ => some c
  | _ => none

/-- The field called `name`, by ASDL position. -/
def field? (a : Ast) (name : String) : Option Ast :=
  match a with
  | .node c fs _ =>
    let rec go : List (String × FieldBase × FieldQuant) → List Ast → Option Ast
      | (n, _) :: ns, f :: rest => if n == name then some f else go ns rest
      | _, _ => none
    go c.fields fs
  | _ => none

end Ast

/-! ### JSON encoding

The canonical exchange format with `difftest/pygrammar_ast.py`:

* node: `{"c": name, "l": [lineno, col, end_lineno, end_col] | null, "f": [fields]}`
* seq: a JSON array;  null: `null`
* identifier: `{"id": [cps]}`;  string: `{"s": [cps]}`;  int: `{"n": i}`
* constant: `{"k": kind, "v": value}` with kinds `None True False Ellipsis`,
  `int` (decimal string), `float` (bits as decimal string), `complex` (two such
  strings), `str`/`bytes` (arrays), `tuple`/`frozenset` (arrays of constants).
-/

namespace PyConst

/-- Encode a constant. -/
partial def toJ : PyConst → Json
  | .none => Json.mkObj [("k", "None")]
  | .true_ => Json.mkObj [("k", "True")]
  | .false_ => Json.mkObj [("k", "False")]
  | .ellipsis => Json.mkObj [("k", "Ellipsis")]
  | .int v => Json.mkObj [("k", "int"), ("v", toString v)]
  | .float b => Json.mkObj [("k", "float"), ("v", toString b)]
  | .complex r i => Json.mkObj [("k", "complex"), ("v", toJson [toString r, toString i])]
  | .str s => Json.mkObj [("k", "str"), ("v", toJson s)]
  | .bytes s => Json.mkObj [("k", "bytes"), ("v", toJson s)]
  | .tuple xs => Json.mkObj [("k", "tuple"), ("v", Json.arr (xs.map toJ).toArray)]
  | .frozenset xs => Json.mkObj [("k", "frozenset"), ("v", Json.arr (xs.map toJ).toArray)]

private def natOfDec (s : String) : Except String Nat :=
  match s.toNat? with
  | .some n => .ok n
  | .none => .error s!"bad nat {s}"

private def intOfDec (s : String) : Except String Int :=
  match s.toInt? with
  | .some n => .ok n
  | .none => .error s!"bad int {s}"

/-- Decode a constant. -/
partial def ofJ (j : Json) : Except String PyConst := do
  let k ← (← j.getObjVal? "k").getStr?
  match k with
  | "None" => return .none
  | "True" => return .true_
  | "False" => return .false_
  | "Ellipsis" => return .ellipsis
  | "int" => return .int (← intOfDec (← (← j.getObjVal? "v").getStr?))
  | "float" => return .float (← natOfDec (← (← j.getObjVal? "v").getStr?))
  | "complex" =>
    let v ← (← j.getObjVal? "v").getArr?
    if h : v.size = 2 then
      return .complex (← natOfDec (← v[0].getStr?)) (← natOfDec (← v[1].getStr?))
    else throw "bad complex"
  | "str" => return .str (← fromJson? (← j.getObjVal? "v"))
  | "bytes" => return .bytes (← fromJson? (← j.getObjVal? "v"))
  | "tuple" => return .tuple (← (← (← j.getObjVal? "v").getArr?).toList.mapM ofJ)
  | "frozenset" => return .frozenset (← (← (← j.getObjVal? "v").getArr?).toList.mapM ofJ)
  | _ => throw s!"bad constant kind {k}"

end PyConst

namespace Ast

/-- Encode a tree. -/
partial def toJ : Ast → Json
  | .node c fs l =>
    Json.mkObj [("c", c.name),
      ("l", match l with
        | some l => toJson [l.lineno, l.colOffset, l.endLineno, l.endColOffset]
        | none => Json.null),
      ("f", Json.arr (fs.map toJ).toArray)]
  | .seq xs => Json.arr (xs.map toJ).toArray
  | .null => Json.null
  | .ident s => Json.mkObj [("id", toJson s)]
  | .str s => Json.mkObj [("s", toJson s)]
  | .int v => Json.mkObj [("n", toJson v)]
  | .const v => v.toJ
  | .tok t => Json.mkObj [("tok", toJson t.type)]

/-- Decode a tree. -/
partial def ofJ (j : Json) : Except String Ast :=
  match j with
  | .null => .ok .null
  | .arr xs => do return .seq (← xs.toList.mapM ofJ)
  | .obj _ =>
    match j.getObjVal? "c" with
    | .ok c => do
      let name ← c.getStr?
      let some ctor := Ctor.ofName? name | throw s!"unknown ctor {name}"
      let fs ← (← (← j.getObjVal? "f").getArr?).toList.mapM ofJ
      let l ← j.getObjVal? "l"
      let loc : Option Loc ← match l with
        | .null => pure none
        | .arr a =>
          match a.toList.mapM (fun x => x.getInt?) with
          | .ok [p, q, r, s] => pure (some ⟨p, q, r, s⟩)
          | _ => throw "bad loc"
        | _ => throw "bad loc"
      return .node ctor fs loc
    | .error _ =>
      match j.getObjVal? "id", j.getObjVal? "s", j.getObjVal? "n" with
      | .ok v, _, _ => do return .ident (← fromJson? v)
      | _, .ok v, _ => do return .str (← fromJson? v)
      | _, _, .ok v => do return .int (← v.getInt?)
      | _, _, _ => do return .const (← PyConst.ofJ j)
  | _ => .error "bad ast json"

end Ast

end PyLean.PyGrammar
