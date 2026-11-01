import PyLean.PyGrammar.Ast
import PyLean.PyGrammar.Peg.Helpers

/-!
The grammar as data. `GrammarData.lean` is generated from `Grammar/python.gram`
through pegen's own `CParserGenerator` (see `gen/gen_grammar.py`), so these types
describe what `Parser/parser.c` is made of: rules, alternatives, and for each item
the C call the generator emits for it, plus each action as a small C expression tree.
-/

namespace PyLean.PyGrammar.Peg

/-- A rule action: the C expression between `{ }` in `python.gram`, parsed. -/
inductive AE where
  /-- The `i`-th variable bound in the alternative. -/
  | var (i : Nat)
  | null
  /-- The four parts of `EXTRA`. -/
  | extra0 | extra1 | extra2 | extra3
  /-- `p->tokens[p->mark-1]` -/
  | lastTok
  /-- `p->tok` -/
  | tokState
  | pyNone | pyTrue | pyFalse | pyEllipsis
  | int (n : Int)
  | str (s : String)
  /-- An enum constant or `X_kind`. -/
  | ctor (c : Ctor)
  /-- `_PyAST_c(args)`; a located constructor takes the location as its last four. -/
  | mk (c : Ctor) (args : List AE)
  | call (h : Helper) (args : List AE)
  /-- `CHECK(type, e)` -/
  | check (e : AE)
  /-- `CHECK_NULL_ALLOWED(type, e)` -/
  | checkNull (e : AE)
  /-- `CHECK_VERSION(type, v, msg, node)` -/
  | checkVersion (v msg node : AE)
  | ite (c a b : AE)
  | and_ (a b : AE)
  | or_ (a b : AE)
  | eq (a b : AE)
  | not_ (a : AE)
  | sub (a b : AE)
  | add (a b : AE)
  /-- `e->v.Ctor.name` -/
  | field (e : AE) (name : String)
  /-- `e->kind` -/
  | kind (e : AE)
  /-- `e->name`, a location attribute or a member of a parser record. -/
  | attr (e : AE) (name : String)
  deriving Repr, Inhabited

/-- The function an item calls, as `CCallMakerVisitor` chooses it. -/
inductive Call where
  /-- `_PyPegen_expect_token(p, t)` -/
  | tok (t : Nat)
  /-- `_PyPegen_name_token(p)` -/
  | name
  /-- `_PyPegen_number_token(p)` -/
  | number
  /-- `_PyPegen_string_token(p)` -/
  | string
  /-- `_PyPegen_soft_keyword_token(p)` -/
  | softKeywordToken
  /-- `_PyPegen_expect_soft_keyword(p, s)` -/
  | softKw (s : List Nat)
  /-- `_PyPegen_expect_forced_token(p, t, s)` -/
  | forcedTok (t : Nat) (s : String)
  /-- `_PyPegen_expect_forced_result(p, r_rule(p), s)` -/
  | forcedRule (r : Nat) (s : String)
  /-- `r_rule(p)` -/
  | rule (r : Nat)
  deriving Repr, Inhabited

/-- One conjunct of an alternative. -/
inductive Item where
  /-- `(v = c(p))` -/
  | call (c : Call)
  /-- `(_opt_var = c(p), !p->error_indicator)` -/
  | opt (c : Call)
  /-- `_PyPegen_lookahead…(positive, c, p)` -/
  | look (positive : Bool) (c : Call)
  /-- `(_cut_var = 1)` -/
  | cut
  deriving Repr, Inhabited

/-- An alternative: `nvars` counts the variables the C code binds, so the default
action of `emit_default_action` can be chosen. -/
structure Alt where
  items : List Item
  action : Option AE
  nvars : Nat
  /-- `if (p->call_invalid_rules)` around the alternative. -/
  guardInvalid : Bool
  /-- The action uses `EXTRA`. -/
  extra : Bool
  deriving Repr, Inhabited

/-- Kinds of generated rule function. -/
inductive RuleKind where
  | normal | gather | loop0 | loop1
  deriving DecidableEq, Repr, Inhabited

/-- A generated rule function of `Parser/parser.c`. -/
structure Rule where
  name : String
  kind : RuleKind
  memo : Bool
  leftRec : Bool
  leader : Bool
  /-- Some alternative uses `EXTRA`, so entry reads the start location. -/
  extra : Bool
  /-- Name ends in `without_invalid`. -/
  withoutInvalid : Bool
  alts : List Alt
  deriving Repr, Inhabited

end PyLean.PyGrammar.Peg
