import PyLean.Itertools.Model

/-!
`itertools.groupby` (Modules/itertoolsmodule.c:426-720) and `itertools.tee`
(:722-1205) with their doc equivalents (rst:426-456, :687-718), driven by
interleaved operations on the returned iterators.

groupby operations: `outer` is `next(groupby_obj)` (result: the key, the group
is remembered by creation order); `group j` is `next()` on the `j`-th group
created so far (an op naming a group that does not exist yet is skipped).

tee operations, on the list of tee iterators created so far: `next k`,
`tee k m` (`tee(t_k, m)` appends `m` iterators) and `copy k` (`t_k.__copy__()`;
the doc's `_tee` has no `__copy__`, the doc side uses `_tee(t_k)`, which the
doc text calls the same flattening).
-/

namespace PyLean.Itertools

open PyLean

/-! ## groupby -/

inductive GbOp where
  | outer
  | group (j : Nat)
  deriving Repr, DecidableEq

/-- `groupbyobject` (:428-437); groupers are numbered by creation, and
`currgrouper` is the number of the current one. -/
structure CGroupby where
  it : List Int
  tgtkey : Option Int
  currkey : Option Int
  currvalue : Option Int
  currgrouper : Option Nat
  groupers : List Int   -- `tgtkey` of each `_grouper`, by number
  deriving Repr

/-- `groupby_step` (:508-531): `none` is the `-1` (exhausted) return. -/
def cGroupbyStep (key : Int → Int) (g : CGroupby) : Option CGroupby :=
  match g.it with
  | [] => none
  | v :: rest => some { g with it := rest, currvalue := some v, currkey := some (key v) }

/-- The tests at the head of that loop: `true` means "call `groupby_step`". -/
def gbAdvance : Option Int → Option Int → Bool
  | none, _ => true
  | some _, none => false
  | some ck, some tk => tk == ck

/-- The `for (;;)` loop of `groupby_next` (:541-567). The flag is `true` for
the `break` out of the loop and `false` when `groupby_step` failed; the steps
already taken stay in the state either way. Each iteration but the last
consumes an item, so `it.length + 1` iterations are enough. -/
def cGroupbySkip (key : Int → Int) : Nat → CGroupby → Bool × CGroupby
  | 0, g => (false, g)
  | fuel + 1, g =>
    if !gbAdvance g.currkey g.tgtkey then (true, g)
    else match cGroupbyStep key g with
      | none => (false, g)
      | some g => cGroupbySkip key fuel g

/-- `groupby_next` (:534-579). -/
def cGroupbyNext (key : Int → Int) (g : CGroupby) : Option Int × CGroupby :=
  let g := { g with currgrouper := none }
  match cGroupbySkip key (g.it.length + 1) g with
  | (false, g) => (none, g)
  | (true, g) =>
    let ck := g.currkey.getD 0
    let id := g.groupers.length
    (some ck, { g with tgtkey := some ck, groupers := g.groupers ++ [ck], currgrouper := some id })

/-- `_grouper_next` (:666-700). -/
def cGrouperNext (key : Int → Int) (g : CGroupby) (j : Nat) : Option Int × CGroupby :=
  if g.currgrouper != some j then (none, g)
  else
    let g' := if g.currvalue.isNone then cGroupbyStep key g else some g
    match g' with
    | none => (none, g)
    | some g =>
      if g.groupers.getD j 0 == g.currkey.getD 0 then
        (g.currvalue, { g with currvalue := none, currkey := none })
      else (none, g)

def cGroupbyOps (key : Int → Int) : CGroupby → List GbOp → List (Option Int)
  | _, [] => []
  | g, .outer :: ops => let (r, g) := cGroupbyNext key g; r :: cGroupbyOps key g ops
  | g, .group j :: ops =>
    if j < g.groupers.length then
      let (r, g) := cGrouperNext key g j; r :: cGroupbyOps key g ops
    else cGroupbyOps key g ops

def cGroupby (key : Int → Int) (l : List Int) (ops : List GbOp) : List (Option Int) :=
  cGroupbyOps key { it := l, tgtkey := none, currkey := none, currvalue := none,
                    currgrouper := none, groupers := [] } ops

/-! ### Doc groupby: two kinds of generator frames sharing `nonlocal` state -/

inductive GenPc where
  | fresh      -- created, not started
  | suspended  -- suspended at a `yield`
  | done
  deriving Repr, DecidableEq

structure DocGroupby where
  it : List Int
  currValue : Int
  currKey : Int
  targetKey : Int
  exhausted : Bool
  outer : GenPc
  groups : List (Int × GenPc)   -- `(target_key, frame state)` of each `_grouper`
  deriving Repr

/-- `next()` on the `j`-th `_grouper(target_key)` generator (rst:431-439). -/
def docGrouperNext (key : Int → Int) (d : DocGroupby) (j : Nat) : Option Int × DocGroupby :=
  let (tk, pc) := d.groups.getD j (0, .done)
  let setPc (d : DocGroupby) (pc : GenPc) := { d with groups := d.groups.set j (tk, pc) }
  match pc with
  | .done => (none, d)
  | .fresh => (some d.currValue, setPc d .suspended)
  | .suspended =>
    match d.it with
    | [] => (none, setPc { d with exhausted := true } .done)
    | v :: rest =>
      let d := { d with it := rest, currValue := v, currKey := key v }
      if d.currKey != tk then (none, setPc d .done)
      else (some d.currValue, d)

/-- `for _ in curr_group: pass` (rst:455-456). -/
def docExhaustGroup (key : Int → Int) (d : DocGroupby) (j : Nat) : Nat → DocGroupby
  | 0 => d
  | fuel + 1 =>
    match docGrouperNext key d j with
    | (none, d) => d
    | (some _, d) => docExhaustGroup key d j fuel

/-- The `while not exhausted:` body up to its `yield` (rst:451-454). -/
def docGroupbyLoopHead (d : DocGroupby) : Option Int × DocGroupby :=
  if d.exhausted then (none, { d with outer := .done })
  else
    let d := { d with targetKey := d.currKey, groups := d.groups ++ [(d.currKey, GenPc.fresh)] }
    (some d.currKey, { d with outer := .suspended })

/-- `next()` on the doc's `groupby` generator (rst:426-456). -/
def docGroupbyNext (key : Int → Int) (d : DocGroupby) : Option Int × DocGroupby :=
  match d.outer with
  | .done => (none, d)
  | .fresh =>
    match d.it with
    | [] => (none, { d with outer := .done })
    | v :: rest => docGroupbyLoopHead { d with it := rest, currValue := v, currKey := key v }
  | .suspended =>
    let d := if d.currKey == d.targetKey then
        docExhaustGroup key d (d.groups.length - 1) (d.it.length + 2)
      else d
    docGroupbyLoopHead d

def docGroupbyOps (key : Int → Int) : DocGroupby → List GbOp → List (Option Int)
  | _, [] => []
  | d, .outer :: ops => let (r, d) := docGroupbyNext key d; r :: docGroupbyOps key d ops
  | d, .group j :: ops =>
    if j < d.groups.length then
      let (r, d) := docGrouperNext key d j; r :: docGroupbyOps key d ops
    else docGroupbyOps key d ops

def docGroupby (key : Int → Int) (l : List Int) (ops : List GbOp) : List (Option Int) :=
  docGroupbyOps key { it := l, currValue := 0, currKey := 0, targetKey := 0, exhausted := false,
                      outer := .fresh, groups := [] } ops

/-! ## tee -/

inductive TeeOp where
  | next (k : Nat)
  | tee (k m : Nat)
  | copy (k : Nat)
  deriving Repr, DecidableEq

/-- `#define LINKCELLS 57` (:732). -/
def LINKCELLS : Nat := 57

/-- The shared chain of `teedataobject`s (:734-741): block `b` holds
`blocks[b]` (`numread` values); `nextlink` of block `b` exists iff
`b + 1 < blocks.length`. Each tee is `(dataobj, index)`. -/
structure CTee where
  it : List Int
  blocks : List (List Int)
  tees : List (Nat × Nat)
  deriving Repr

/-- `teedataobject_jumplink` (:773-782) as used by `tee_next` (:961-968): at
`index >= LINKCELLS` move to the next block, creating it if needed. -/
def teeJump (t : CTee) (b i : Nat) : CTee × Nat × Nat :=
  if i ≥ LINKCELLS then
    let t := if b + 1 < t.blocks.length then t else { t with blocks := t.blocks ++ [[]] }
    (t, b + 1, 0)
  else (t, b, i)

/-- `teedataobject_getitem_lock_held` (:785-809) and the `to->index++` of
`tee_next` (:969-973): a stored value, or (lead iterator) pull one more item. -/
def teeGetitem (t : CTee) (k b i : Nat) : Option Int × CTee :=
  let blk := t.blocks.getD b []
  if i < blk.length then
    (some (blk.getD i 0), { t with tees := t.tees.set k (b, i + 1) })
  else
    match t.it with
    | [] => (none, t)
    | v :: rest =>
      (some v, { t with it := rest, blocks := t.blocks.set b (blk ++ [v]),
                        tees := t.tees.set k (b, i + 1) })

/-- `tee_next` (:953-975, GIL build). -/
def cTeeNext (t : CTee) (k : Nat) : Option Int × CTee :=
  let (b, i) := t.tees.getD k (0, 0)
  let (t, b, i) := teeJump t b i
  teeGetitem { t with tees := t.tees.set k (b, i) } k b i

def cTeeOps : CTee → List TeeOp → List (Option Int) × CTee
  | t, [] => ([], t)
  | t, .next k :: ops =>
    if k < t.tees.length then
      let (r, t) := cTeeNext t k
      let (rs, t) := cTeeOps t ops
      (r :: rs, t)
    else cTeeOps t ops
  | t, .tee k m :: ops =>
    if k < t.tees.length then
      cTeeOps { t with tees := t.tees ++ List.replicate m (t.tees.getD k (0, 0)) } ops
    else cTeeOps t ops
  | t, .copy k :: ops =>
    if k < t.tees.length then cTeeOps { t with tees := t.tees ++ [t.tees.getD k (0, 0)] } ops
    else cTeeOps t ops

/-- `itertools_tee_impl` (:1165-1204): `n` through the `Py_ssize_t` converter;
`n == 0` returns `()`. Results of the ops, then the number of items pulled from
the input. -/
def cTee (l : List Int) (n : Int) (ops : List TeeOp) : Py (List (Option Int) × Nat) := do
  let n ← asSsize n
  if n < 0 then throw (.valueError "n must be >= 0")
  if !tupleNewOk n then throw memoryError
  let t : CTee := { it := l, blocks := [[]], tees := List.replicate n.toNat (0, 0) }
  let (rs, t) := cTeeOps t ops
  return (rs, l.length - t.it.length)

/-- The doc's `_tee` objects (rst:698-718) sharing one chain of
`[value, next]` links: link `c` is filled iff `c < values.length`; each tee
holds its current link number. -/
structure DocTee where
  it : List Int
  values : List Int
  tees : List Nat
  deriving Repr

/-- `_tee.__next__` (rst:712-718). -/
def docTeeNext (t : DocTee) (k : Nat) : Option Int × DocTee :=
  let c := t.tees.getD k 0
  let t' : Option DocTee :=
    if c < t.values.length then some t
    else match t.it with
      | [] => none
      | v :: rest => some { t with it := rest, values := t.values ++ [v] }
  match t' with
  | none => (none, t)
  | some t => (some (t.values.getD c 0), { t with tees := t.tees.set k (c + 1) })

def docTeeOps : DocTee → List TeeOp → List (Option Int) × DocTee
  | t, [] => ([], t)
  | t, .next k :: ops =>
    if k < t.tees.length then
      let (r, t) := docTeeNext t k
      let (rs, t) := docTeeOps t ops
      (r :: rs, t)
    else docTeeOps t ops
  | t, .tee k m :: ops =>
    if k < t.tees.length then
      docTeeOps { t with tees := t.tees ++ List.replicate m (t.tees.getD k 0) } ops
    else docTeeOps t ops
  | t, .copy k :: ops =>
    if k < t.tees.length then docTeeOps { t with tees := t.tees ++ [t.tees.getD k 0] } ops
    else docTeeOps t ops

/-- rst:687-696: bare `ValueError` for `n < 0`. -/
def docTee (l : List Int) (n : Int) (ops : List TeeOp) : Py (List (Option Int) × Nat) := do
  if n < 0 then throw (.valueError "")
  let t : DocTee := { it := l, values := [], tees := List.replicate n.toNat 0 }
  let (rs, t) := docTeeOps t ops
  return (rs, l.length - t.it.length)

end PyLean.Itertools
