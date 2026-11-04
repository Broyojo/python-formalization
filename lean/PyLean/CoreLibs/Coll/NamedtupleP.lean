import PyLean.CoreLibs.Coll.NamedtupleProps
import PyLean.CoreLibs.Coll.CounterProps2

/-!
`namedtuple` with its fallible conversions, Lib/collections/__init__.py:387-427 (CPython 3.15.2):
`list(map(str, field_names))` over any iterable (:389, `iter()`, `next()` and `str()` may raise)
and `tuple(defaults)` (:423), evaluated where the source evaluates them; and `__getnewargs__`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PyLean.CoreLibs.Coll

open PyLean

/-- `field_names` as passed: a `str`, or an iterable of objects with their `str()`. -/
inductive FieldSrc (α : Type) where
  | str (s : String)
  | objs (it : Py (FIt α)) (toStr : α → Py String)

/-- :387-389: split a `str`; then `list(map(str, field_names))`, each `str()` called as its item
is pulled. -/
def fieldListP {α : Type} : FieldSrc α → Py (List String)
  | .str s => .ok (splitNames s)
  | .objs it toStr => do
    let it ← it
    let l ← it.xs.mapM toStr
    match it.stop with
    | none => pure l
    | some e => .error e

/-- `namedtuple(typename, field_names, rename=..., defaults=...)` with `field_names` converted by
`fieldListP` first and `defaults` (`none` for `None`, else `tuple(defaults)`, which may raise)
evaluated after the name checks (:421-423); the rest is `namedtuple`. -/
def namedtupleP {α ν : Type} (U : UniId) (tn : String) (src : FieldSrc α) (rename : Bool)
    (defaults : Option (Py (List ν))) : Py (NT ν) := do
  let names ← fieldListP src
  let names' := if rename then renameLoop U [] 0 names else names
  checkNames U (tn :: names')
  checkSeen rename [] names'
  let d ← match defaults with
    | none => pure none
    | some p => some <$> p
  namedtuple U tn (.list names) rename d

/-- **`namedtuple` converts its arguments where the source does.** For every Unicode database:
with a `str` for `field_names` and a defaults sequence that converts, it is `namedtuple` on the
string, whose fields are the string's comma- or whitespace-separated words; an iterable of
field names whose `str()` raises (or whose `next()` raises) raises that before any name is
checked; and a defaults iterable whose `tuple()` raises does so only after the names passed
their checks, a bad name's `ValueError` coming first.

Source: Lib/collections/__init__.py:387-389, :421-423; Doc/library/collections.rst
('field_names ... can be a single string with each fieldname separated by whitespace and/or
commas'). -/
def NamedtupleConversions : Prop :=
  ∀ (α : Type) (U : UniId) (tn s : String) (r : Bool) (d : Option (List Nat)) (e : PyExc),
    namedtupleP (α := α) U tn (.str s) r (d.map .ok) = namedtuple U tn (.str s) r d ∧
    (∀ (x : α) (xs : List α) (toStr : α → Py String) (d' : Option (Py (List Nat))), toStr x = .error e →
      namedtupleP U tn (.objs (.ok ⟨x :: xs, none⟩) toStr) r d' = .error e) ∧
    (∀ (names : List String) (toStr : α → Py String) (xs : List α), xs.mapM toStr = .ok names →
      namedtupleP U tn (.objs (.ok ⟨xs, some e⟩) toStr) r (d.map (Except.ok (ε := PyExc))) = .error e) ∧
    (∀ x : PyExc, checkNames U (tn :: (if r then renameLoop U [] 0 (splitNames s) else splitNames s)) = .error x →
      namedtupleP (α := α) (ν := Nat) U tn (.str s) r (some (.error e)) = .error x) ∧
    (checkNames U (tn :: (if r then renameLoop U [] 0 (splitNames s) else splitNames s)) = .ok () →
      checkSeen r [] (if r then renameLoop U [] 0 (splitNames s) else splitNames s) = .ok () →
      namedtupleP (α := α) (ν := Nat) U tn (.str s) r (some (.error e)) = .error e)

theorem namedtupleConversions_proven : NamedtupleConversions := by
  intro α U tn s r d e
  refine ⟨?_, fun x xs toStr d' hx => ?_, fun names toStr xs hm => ?_, fun x hx => ?_, fun h1 h2 => ?_⟩
  · simp only [namedtupleP, fieldListP, ok_bind]
    cases hc : checkNames U (tn :: (if r then renameLoop U [] 0 (splitNames s) else splitNames s)) with
    | error x =>
      simp only [error_bind]
      simp [namedtuple, fieldList, hc, bind, Except.bind]
    | ok u =>
      simp only [ok_bind]
      cases hs : checkSeen r [] (if r then renameLoop U [] 0 (splitNames s) else splitNames s) with
      | error x =>
        simp only [error_bind]
        simp [namedtuple, fieldList, hc, hs, bind, Except.bind]
      | ok u' =>
        cases d <;> rfl
  · simp [namedtupleP, fieldListP, List.mapM_cons, hx]
  · simp [namedtupleP, fieldListP, hm]
  · simp only [namedtupleP, fieldListP, ok_bind, hx, error_bind]
  · simp only [namedtupleP, fieldListP, ok_bind, h1, h2]
    rfl

/-- **`__getnewargs__` rebuilds the instance.** For every generated class and every tuple of the
right length, `T(*p.__getnewargs__())` gives back the same values (the copy and pickle
protocol).

Source: docstring, Lib/collections/__init__.py:481 ('Return self as a plain tuple.  Used by copy
and pickle.'). -/
def NamedtupleGetnewargs : Prop :=
  ∀ (U : UniId) (tn : String) (fn : FieldNames) (r : Bool) (d : Option (List Nat)) (T : NT Nat)
    (vals : List Nat), namedtuple U tn fn r d = .ok T → vals.length = T.fields.length →
    ntCall T (ntGetnewargs vals) [] = .ok vals

theorem namedtupleGetnewargs_proven : NamedtupleGetnewargs := by
  intro U tn fn r d T vals hT hl
  obtain ⟨_, _, ha, _⟩ := namedtuple_inv hT
  have hlen : T.args.length = vals.length := by rw [ha, List.length_map, hl]
  simp only [ntCall, ntGetnewargs, hlen, Nat.lt_irrefl, gt_iff_lt, if_false, checkKw, ok_bind,
    List.drop_length, fillRest, List.append_nil]
  rw [List.drop_eq_nil_of_le (by omega)]
  simp [fillRest]

end PyLean.CoreLibs.Coll
