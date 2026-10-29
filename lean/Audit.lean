import PyLean

/-!
Registry audit, run with `lake env lean Audit.lean`. Fails unless every entry
is proven or refuted by a theorem whose type is exactly the registered
property (or its negation) and which uses only the standard axioms. A `sorry`
anywhere in a proof shows up here as the axiom `sorryAx`.
-/

open Lean Elab Command PyLean.Registry

def allEntries : List Entry := PyLean.Ipaddress.entries

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut failures : Array String := #[]
  let mut proven : Nat := 0
  let mut refuted : Nat := 0
  for e in allEntries do
    if e.status == .open then
      failures := failures.push s!"{e.id}: still open"
      continue
    let some thm := e.thm | failures := failures.push s!"{e.id}: no theorem"; continue
    let some info := env.find? thm | failures := failures.push s!"{e.id}: unknown {thm}"; continue
    if env.find? e.prop |>.isNone then
      failures := failures.push s!"{e.id}: unknown property {e.prop}"; continue
    let expected := match e.status with
      | .refuted => mkApp (mkConst ``Not) (mkConst e.prop)
      | _ => mkConst e.prop
    if info.type != expected then
      failures := failures.push s!"{e.id}: {thm} does not state {if e.status == .refuted then "¬ " else ""}{e.prop}"
      continue
    let axs ← liftCoreM (collectAxioms thm)
    let bad := axs.filter (· ∉ allowedAxioms)
    if !bad.isEmpty then
      failures := failures.push s!"{e.id}: {thm} uses {bad.toList}"
      continue
    if e.status == .refuted then
      if e.bug.isNone then failures := failures.push s!"{e.id}: refuted without a bug id"; continue
      refuted := refuted + 1
    else
      proven := proven + 1
  logInfo m!"{allEntries.length} properties: {proven} proven, {refuted} refuted, {failures.size} failing"
  for f in failures do logInfo m!"FAIL {f}"
  unless failures.isEmpty do throwError "audit failed"
