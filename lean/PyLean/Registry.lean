import Lean

/-!
Every property gets one registry entry. `Audit.lean` checks that each `thm`
has type exactly `prop` (proven) or `¬ prop` (refuted), and that it depends on
no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace PyLean.Registry

inductive Status where
  /-- The property holds for every input; `thm : prop`. -/
  | proven
  /-- A counterexample exists; `thm : ¬ prop`. A refutation must also have a
  plain-Python reproducer under `bugs/`. -/
  | refuted
  /-- Stated but neither proven nor refuted yet. The audit counts these, and they
  do not count towards coverage. -/
  | open
  deriving Repr, DecidableEq, Inhabited

structure Entry where
  id : String
  /-- Path relative to CPython's `Lib/` (or `Objects/`, `Modules/` for C). -/
  pyFile : String
  pyFns : List String
  /-- The property in plain English, quantified over all inputs. -/
  statement : String
  /-- Where the promise comes from: docstring, docs page, or "invariant". -/
  source : String
  status : Status
  prop : Lean.Name
  thm : Option Lean.Name := none
  /-- For refutations: the `bugs/*.yaml` id. -/
  bug : Option String := none
  notes : String := ""
  deriving Inhabited

end PyLean.Registry
