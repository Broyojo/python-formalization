import PyLean.CoreLibs.Misc.Weakref.Model

/-!
`copy.deepcopy` over a small object graph, to run `WeakValueDictionary.__deepcopy__` and
`WeakKeyDictionary.__deepcopy__` (Lib/weakref.py:151-158, :347-354) with the `memo` of
Lib/copy.py:118-160.

A cell is an atom (copied as itself, `_deepcopy_atomic`), an object whose copy raises (a lock), an
instance with one attribute (copied by `_reconstruct`, Lib/copy.py:230-260, which records the new
object in `memo` before it copies the state), or one of the two dictionaries. `copy.deepcopy`
records `memo[id(x)] = y` only after `x.__deepcopy__(memo)` returns (Lib/copy.py:142-160), and the
two `__deepcopy__` methods never record their `new` themselves. Scope: `_keep_alive`'s entry, which
maps `id(memo)` to a list, is left out; it maps no object of the graph.
-/

namespace PyLean.CoreLibs.Misc.Weakref

open PyLean

inductive Cell where
  | atom
  | bad (e : PyExc)
  | box (fld : Nat)
  | wvd (d : WVD Nat)
  | wkd (d : WKD Nat)
  deriving DecidableEq

/-- The heap, the next fresh id, and `memo`. -/
structure DS where
  heap : List (Nat × Cell)
  next : Nat
  memo : List (Nat × Nat)

def DS.get (s : DS) (x : Nat) : Option Cell := dGet s.heap x

def DS.put (s : DS) (x : Nat) (c : Cell) : DS := { s with heap := dSet s.heap x c }

def DS.alloc (s : DS) (c : Cell) : DS × Nat :=
  ({ s with heap := s.heap ++ [(s.next, c)], next := s.next + 1 }, s.next)

/-- `copy.deepcopy(x, memo)`, Lib/copy.py:118-160, with `ops` the keys' `__hash__`/`__eq__` of a
`WeakValueDictionary` and `q` the referents' of a `WeakKeyDictionary`. -/
def deep (ops : KOps Nat) (q : ROps) (w : World) : Nat → DS → Nat → Py (DS × Nat)
  | 0, _, _ => .error .modelFuel
  | f + 1, s, x =>
    match dGet s.memo x with
    | some y => .ok (s, y)
    | none =>
      match s.get x with
      | none => .ok (s, x)
      | some .atom => .ok (s, x)
      | some (.bad e) => .error e
      | some (.box fld) =>
        let a := s.alloc (.box fld)
        let s := { a.1 with memo := dSet a.1.memo x a.2 }
        match deep ops q w f s fld with
        | .error e => .error e
        | .ok (s, fld') => .ok ({ (s.put a.2 (.box fld')) with memo := dSet s.memo x a.2 }, a.2)
      | some (.wvd d) =>
        let a := s.alloc (.wvd WVD.empty)
        match WVD.deepcopy ops (fun s k => deep ops q w f s k) (.ok WVD.empty) w d a.1 with
        | .error e => .error e
        | .ok (s, n) => .ok ({ (s.put a.2 (.wvd n)) with memo := dSet s.memo x a.2 }, a.2)
      | some (.wkd d) =>
        let a := s.alloc (.wkd WKD.empty)
        match WKD.deepcopy q (fun s v => deep ops q w f s v) (.ok WKD.empty) w d a.1 with
        | .error e => .error e
        | .ok (s, n) => .ok ({ (s.put a.2 (.wkd n)) with memo := dSet s.memo x a.2 }, a.2)

/-- Where a reference to `x` points in the copy: its copy when `memo` has one, else `x` itself. -/
def img (m : List (Nat × Nat)) (x : Nat) : Nat := (dGet m x).getD x

end PyLean.CoreLibs.Misc.Weakref
