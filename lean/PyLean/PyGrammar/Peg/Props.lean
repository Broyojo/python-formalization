import PyLean.PyGrammar.Peg.Interp
import PyLean.PyGrammar.Unparse.CUnparse
import PyLean.PyGrammar.Check.Validate

/-!
Properties of the grammar and the parser.

The static ones quantify over every rule of `Grammar/python.gram`, artificial rules
included, and are checked by the kernel over the generated data. Together they discharge
what makes a PEG interpreter safe: references resolve, `invalid_` rules cannot run in the
first pass, loops consume input, and left recursion goes through a seed-growing leader.

The refutations run the whole pipeline (lexer, PEG interpreter, actions, unparser) in the
kernel on concrete source text.
-/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### Static analysis of the grammar data -/

/-- Every rule number. -/
def allRules : List Nat := List.range ruleCount

/-- The rule a call refers to. -/
def Call.ruleRef? : Call → Option Nat
  | .rule r | .forcedRule r _ => some r
  | _ => none

/-- The call of an item. -/
def Item.call? : Item → Option Call
  | .call c | .opt c | .look _ c => some c
  | .cut => none

/-- Rules an alternative calls. -/
def Alt.refs (a : Alt) : List Nat :=
  a.items.filterMap fun i => i.call?.bind Call.ruleRef?

/-- Rules a rule calls. -/
def Rule.refs (r : Rule) : List Nat := r.alts.flatMap Alt.refs

/-- Every rule reference resolves. -/
def GrammarRefsResolve : Prop :=
  allRules.all (fun id => (ruleOf id).refs.all (· < ruleCount)) = true

/-- Is this `invalid_…`? -/
def isInvalidName (s : String) : Bool := s.toList.take 8 == "invalid_".toList

/-- The first pass cannot reach an `invalid_` rule: every alternative that calls one is
guarded by `p->call_invalid_rules`, or belongs to an `invalid_` rule itself. -/
def InvalidRulesGuarded : Prop :=
  allRules.all (fun id =>
    let r := ruleOf id
    isInvalidName r.name ||
      r.alts.all fun a =>
        a.guardInvalid || a.refs.all (fun t => !isInvalidName (ruleOf t).name)) = true

/-- One step of the least fixed point of "can match without consuming a token". `ns` is
the current set. -/
def itemNullable (ns : List Nat) : Item → Bool
  | .cut | .opt _ | .look _ _ => true
  | .call c =>
    match c.ruleRef? with
    | some r => ns.contains r
    | none => false

/-- Nullability of an alternative. -/
def altNullable (ns : List Nat) (a : Alt) : Bool := a.items.all (itemNullable ns)

/-- Nullability of a rule given the current set. -/
def ruleNullable (ns : List Nat) (id : Nat) : Bool :=
  let r := ruleOf id
  match r.kind with
  | .loop0 => true
  | _ => r.alts.any (altNullable ns)

/-- Iterate to the least fixed point. -/
def nullableStep (ns : List Nat) : List Nat := allRules.filter (ruleNullable ns)

/-- The set of rules that can match empty input. Rules are few and the chain is short. -/
def nullableSet : List Nat :=
  (List.range 12).foldl (fun ns _ => nullableStep ns) []

/-- `nullableSet` is a fixed point, so the analysis above is complete. -/
def NullableIsFixedPoint : Prop := nullableStep nullableSet = nullableSet

/-- The body of a repeat must consume input, or `while (items)` would spin forever on
`p->mark` unchanged. -/
def LoopsConsume : Prop :=
  allRules.all (fun id =>
    let r := ruleOf id
    match r.kind with
    | .loop0 | .loop1 => !r.alts.any (altNullable nullableSet)
    | _ => true) = true

/-- Rules called at the alternative's starting position: up to and including the first
item that must consume input. -/
def altLeftRefs (a : Alt) : List Nat :=
  let rec go : List Item → List Nat
    | [] => []
    | i :: rest =>
      let here := (i.call?.bind Call.ruleRef?).toList
      if itemNullable nullableSet i then here ++ go rest else here
  go a.items

/-- Left-call edges of a rule, with the back edges through a leader cut: a leader's call
at the same position finds its seed in the memo and returns at once. -/
def leftEdges (id : Nat) : List Nat :=
  let r := ruleOf id
  if r.leftRec && r.leader then [] else r.alts.flatMap altLeftRefs

/-- Remove the rules whose left calls are all to removed rules; `rest` is what remains. -/
def peelStep (rest : List Nat) : List Nat :=
  rest.filter fun id => (leftEdges id).any rest.contains

/-- Every rule's left calls bottom out once leader back edges are cut: the graph is acyclic,
since peeling leaves empties it. So at any fixed position a call chain can only repeat a rule
through a leader's memo entry. This is the static half of "left recursion terminates". -/
def LeftRecursionGuarded : Prop :=
  (List.range 40).foldl (fun rest _ => peelStep rest) allRules = []

/-- Reserved and soft keywords are disjoint, and keyword token numbers lie above
`Grammar/Tokens`, so a keyword can never be taken for an operator or for `NAME`. -/
def KeywordsDistinct : Prop :=
  ((keywords.all fun k => !softKeywords.contains k.1 && decide (k.2 ≥ TokKind.count))
    && (keywords.map (·.2)).eraseDups.length == keywords.length) = true

/-- `Rule` names are unique, so memo keys `1000 + id` identify a rule. -/
def RuleNamesDistinct : Prop :=
  (allRules.map fun id => (ruleOf id).name).eraseDups.length = ruleCount

/-- The four start symbols the trailer of `Grammar/python.gram` dispatches on are the rules
named so. -/
def StartRulesNamed : Prop :=
  (ruleOf rule_file).name = "file" ∧ (ruleOf rule_interactive).name = "interactive" ∧
  (ruleOf rule_eval).name = "eval" ∧ (ruleOf rule_func_type).name = "func_type"

set_option maxRecDepth 100000 in
theorem grammarRefsResolve_proven : GrammarRefsResolve := by unfold GrammarRefsResolve; decide +kernel

set_option maxRecDepth 100000 in
/-- `dict` calls `invalid_double_starred_kvpairs` in a three-item alternative, which
`visit_Alt` does not guard, so the comment at the top of `Grammar/python.gram` overstates it. -/
theorem invalidRulesGuarded_refuted : ¬ InvalidRulesGuarded := by
  unfold InvalidRulesGuarded; decide +kernel

/-- The narrowed statement: `dict` is the only exception. -/
def InvalidRulesGuardedButDict : Prop :=
  allRules.all (fun id =>
    let r := ruleOf id
    isInvalidName r.name || r.name == "dict" ||
      r.alts.all fun a =>
        a.guardInvalid || a.refs.all (fun t => !isInvalidName (ruleOf t).name)) = true

set_option maxRecDepth 100000 in
theorem invalidRulesGuardedButDict_proven : InvalidRulesGuardedButDict := by
  unfold InvalidRulesGuardedButDict; decide +kernel

set_option maxRecDepth 100000 in
theorem nullableIsFixedPoint_proven : NullableIsFixedPoint := by unfold NullableIsFixedPoint; decide +kernel

set_option maxRecDepth 100000 in
theorem loopsConsume_proven : LoopsConsume := by unfold LoopsConsume; decide +kernel

set_option maxRecDepth 100000 in
theorem leftRecursionGuarded_proven : LeftRecursionGuarded := by unfold LeftRecursionGuarded; decide +kernel

set_option maxRecDepth 100000 in
theorem keywordsDistinct_proven : KeywordsDistinct := by unfold KeywordsDistinct; decide +kernel

set_option maxRecDepth 100000 in
theorem ruleNamesDistinct_proven : RuleNamesDistinct := by unfold RuleNamesDistinct; decide +kernel

set_option maxRecDepth 100000 in
theorem startRulesNamed_proven : StartRulesNamed := by unfold StartRulesNamed; decide +kernel

/-! ### Round trip: `ast.parse(ast.unparse(t))` -/

/-- `ast.compare(parse src, parse (unparse (parse src)))`, with the default arguments:
locations are ignored. A source that does not parse is vacuous; an `unparse` or second
parse that fails is a failure of the round trip. -/
def roundTrips (src : List Nat) : Bool :=
  match parseStr {} src .file with
  | .error _ => true
  | .ok t =>
    match Unparse.unparseN (Check.astSize t) t with
    | .error _ => false
    | .ok u =>
      match parseStr {} (utf8Encode u) .file with
      | .error _ => false
      | .ok t2 => t.stripLoc == t2.stripLoc

/-- The docstring of `ast.unparse`'s `Unparser.visit`: output that, "if converted back to an
ast (using ast.parse) will generate an AST equivalent to *node*". -/
def UnparseRoundTrip : Prop := ∀ src : List Nat, roundTrips src = true

/-- `f"{x:\x7d}"`: a `}` in a format spec. `Unparser` writes it as `}}`, which ends the
replacement field in a format spec instead of being a literal. -/
def bracketSpec : List Nat :=
  [102, 34, 123, 120, 58, 92, 120, 55, 100, 125, 34]

set_option maxRecDepth 100000 in
theorem unparseRoundTrip_refuted : ¬ UnparseRoundTrip := fun h =>
  absurd (h bracketSpec) (by decide +kernel)

/-! ### The C unparser -/

/-- `_PyAST_ExprAsUnicode` of a parsed expression parses back to it, ignoring locations: the
string `from __future__ import annotations` stores for an annotation is that annotation's
source. A source that is not an expression is vacuous. -/
def cRoundTrips (src : List Nat) : Bool :=
  match parseStr {} src .eval with
  | .ok (.node .Expression [e] _) =>
    match Unparse.exprAsUnicode (Check.astSize e) e with
    | .error _ => false
    | .ok u =>
      match parseStr {} (utf8Encode u) .eval with
      | .ok (.node .Expression [e2] _) => e.stripLoc == e2.stripLoc
      | _ => false
  | _ => true

/-- For every expression source, the annotation string reads back as the same expression. -/
def CUnparseRoundTrip : Prop := ∀ src : List Nat, cRoundTrips src = true

/-- `f"{'\\n'}"`: `append_joinedstr` applies `repr` to a body that already holds the inner
string's `repr`, so the backslash is doubled and the inner string changes. -/
def nestedEscape : List Nat :=
  [102, 34, 123, 39, 92, 110, 39, 125, 34]

set_option maxRecDepth 100000 in
theorem cUnparseRoundTrip_refuted : ¬ CUnparseRoundTrip := fun h =>
  absurd (h nestedEscape) (by decide +kernel)

/-! ### Statements left open -/

/-- The parser never runs out of model fuel. -/
def ParserTerminates : Prop :=
  ∀ (cfg : Cfg) (src : List Nat) (start : StartRule) (e : PyError),
    parseStr cfg src start = .error e → e.cls ≠ "<model fuel exhausted>"

/-- What the parser returns passes the validator. -/
def ParserOutputValidates : Prop :=
  ∀ (src : List Nat) (t : Ast), parseStr {} src .file = .ok t → (Check.validate t).toBool = true

end PyLean.PyGrammar.Peg
