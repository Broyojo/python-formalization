import PyLean.PyGrammar.Peg.GrammarData
import PyLean.PyGrammar.Lexer.Get

/-!
FIRST sets over the grammar data, for any table `F` of what each rule can start with. A pair
`(n, ts)` says: can match nothing when `n`, and otherwise starts with a token whose type is in
`ts`. `Closed` is the condition that makes a table right, checked rule by rule.
-/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- What a call can start with. -/
def callFirst (F : Nat → Bool × List Nat) : Call → Bool × List Nat
  | .tok t => (false, [t])
  | .name => (false, [TokKind.NAME.num])
  | .number => (false, [TokKind.NUMBER.num])
  | .string => (false, [TokKind.STRING.num])
  | .softKeywordToken => (false, [TokKind.NAME.num])
  | .softKw _ => (false, [TokKind.NAME.num])
  | .forcedTok t _ => (false, [t])
  | .forcedRule r _ => F r
  | .rule r => F r

/-- What a sequence of items can start with. An optional item, a lookahead and a cut can all be
passed without consuming a token. -/
def itemsFirst (F : Nat → Bool × List Nat) : List Item → Bool × List Nat
  | [] => (true, [])
  | .call c :: rest =>
    if (callFirst F c).1 then
      ((itemsFirst F rest).1, (callFirst F c).2 ++ (itemsFirst F rest).2)
    else (false, (callFirst F c).2)
  | .opt c :: rest => ((itemsFirst F rest).1, (callFirst F c).2 ++ (itemsFirst F rest).2)
  | .look _ _ :: rest => itemsFirst F rest
  | .cut :: rest => itemsFirst F rest

/-- `xs ⊆ ys` -/
def subsetB (xs ys : List Nat) : Bool := xs.all ys.contains

/-- `f` covers an alternative. -/
def covers (x f : Bool × List Nat) : Bool := subsetB x.2 f.2 && (!x.1 || f.1)

/-- `f` is right for rule `r`, given `F` for the rules it calls. -/
def Closed (F : Nat → Bool × List Nat) (r : Rule) (f : Bool × List Nat) : Bool :=
  match r.kind with
  | .normal | .gather => r.alts.all fun a => covers (itemsFirst F a.items) f
  | .loop0 => f.1 && subsetB (itemsFirst F (r.alts.headD default).items).2 f.2
  | .loop1 => covers (itemsFirst F (r.alts.headD default).items) f

end PyLean.PyGrammar.Peg
