import PyLean.DictSet.DictOps

/-!
The loop of `BaseException___setstate___impl` (`Objects/exceptions.c:246-255`, CPython 3.15.2)
over the real dict table.

`setstateLoop` in `ExcCore.lean` walks the interpreter's dict, a list without dummy entries, by
index. `PyDict_Next` walks `dk_entries`, where a deleted key leaves a `NULL` slot until a resize
compacts the table (`Objects/dictobject.c`). The two agree as long as the state dict is not
changed during the loop, and when it only grows from a table without dummies. Here the loop runs
over `PyLean.DictSet`'s mirror of the table (`dictNext`, `dictSetItem`, `dictDelItem`,
`insertion_resize`), so the cases where they differ are exact.

## Scope

* Keys and values are numbers standing for exact `str` keys and their values; `intProto`
  hashes a key to itself. The layout that `PyDict_Next` sees depends only on the order of
  insertions and deletions, not on hash values, and an all-str dict never changes kind.
* What a `__setattr__` does to the state dict is a script, run for the attribute name being set:
  `st[k] = v` and `del st[k]` (a missing key is the `KeyError` of `PyDict_DelItem`). It may
  do anything else to `self`; the model records only the attribute assignment.
-/

namespace PyLean.TypeObj.SetstateC

open PyLean PyLean.DictSet

/-- Exact `str` keys, standing as numbers; `hash(k)` is `k`. -/
def keyProto : Proto Nat (PyDict Nat Nat) :=
  { hash := fun k => .ok k
    isStr := fun _ => false
    isStrLike := fun _ => false
    strEq := fun a b => a == b
    reprStr := fun _ => ""
    repr := fun _ => .ok ""
    typeName := fun _ => ""
    eq := fun a b s => (.ok (a == b), s) }

abbrev SD := PyDict Nat Nat

/-- What a `__setattr__` does to the state dict. -/
inductive DAct where
  | set (k v : Nat)
  | del (k : Nat)
  deriving DecidableEq, Repr

def runActs : List DAct → SD → Py Unit × SD
  | [], d => (.ok (), d)
  | .set k v :: as, d =>
    match dictSetItem keyProto k v d with
    | (.ok (), d') => runActs as d'
    | (.error e, d') => (.error e, d')
  | .del k :: as, d =>
    match dictDelItem keyProto k d with
    | (.ok (), d') => runActs as d'
    | (.error e, d') => (.error e, d')

/-- The state dict, and the attributes set on `self` so far, in order. -/
structure St where
  d : SD
  log : List (Nat × Nat) := []

/-- `PyObject_SetAttr(self, k, v)` with a user `__setattr__` that runs `script k` on the dict and
then sets the attribute; a raise from the script is the result. -/
def setAttr (script : Nat → List DAct) (k v : Nat) (s : St) : Py Unit × St :=
  match runActs (script k) s.d with
  | (.ok (), d') => (.ok (), { d := d', log := s.log ++ [(k, v)] })
  | (.error e, d') => (.error e, { s with d := d' })

/-- `while (PyDict_Next(state, &i, &d_key, &d_value)) { ... PyObject_SetAttr(...) ... }`,
`Objects/exceptions.c:246-255`. `fuel` is a model bound. -/
def setstateLoop (script : Nat → List DAct) : Nat → Int → St → Py Unit × St
  | 0, _, s => (.error .modelFuel, s)
  | f + 1, pos, s =>
    match dictNext s.d pos with
    | none => (.ok (), s)
    | some (pos', k, v, _) =>
      match setAttr script k v s with
      | (.ok (), s') => setstateLoop script f pos' s'
      | (.error e, s') => (.error e, s')

/-- `st = {}` then `st[k] = v` for each pair, in order. -/
def build (items : List (Nat × Nat)) : SD :=
  items.foldl (fun d p => (dictSetItem keyProto p.1 p.2 d).2) {}

/-- `del st[k]` for each key, in order. -/
def delAll (ks : List Nat) (d : SD) : SD := ks.foldl (fun d k => (dictDelItem keyProto k d).2) d

end PyLean.TypeObj.SetstateC
