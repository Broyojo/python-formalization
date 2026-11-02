import PyLean.Itertools.Model

/-!
`itertools.groupby` (Modules/itertoolsmodule.c:423-716) and `itertools.tee`
(:718-1197) with their doc equivalents (rst:431-461, :692-723), driven by
interleaved operations on the returned iterators.

groupby operations: `outer` is `next(groupby_obj)` (result: the key, the group
is remembered by creation order); `group j` is `next()` on the `j`-th group
created so far (an op naming a group that does not exist yet is skipped).

groupby is generic in the element type and in the key type `κ`, whose `__eq__`
is assumed to be an equivalence with decidable equality (`PyObject_RichCompareBool`
on keys is `==`). Key functions are pure and the input iterator does not raise
in this file, which is the layer the doc comparison runs on; `GroupbyRaising.lean`
is the full mirror with the failing calls, and shows it reduces to this one.
`direct k` is `itertools._grouper(groupby_obj, k)`.

tee operations, on the list of tee iterators created so far: `next k`,
`tee k m` (`tee(t_k, m)` appends `m` iterators), `copy k` (`t_k.__copy__()`;
the doc's `_tee` has no `__copy__`, the doc side uses `_tee(t_k)`, which the
doc text calls the same flattening) and `ctor k` (`itertools._tee(t_k)`). The
input may be non-iterable or raise after its items.
-/

namespace PyLean.Itertools

open PyLean

variable {α κ : Type} [Inhabited α] [Inhabited κ] [DecidableEq κ]

/-! ## groupby -/

inductive GbOp (κ : Type) where
  | outer
  | group (j : Nat)
  | direct (k : κ)

/-- `groupbyobject` (:425-434); groupers are numbered by creation, and
`currgrouper` is the number of the current one. -/
structure CGroupby (α κ : Type) where
  it : List α
  tgtkey : Option κ
  currkey : Option κ
  currvalue : Option α
  currgrouper : Option Nat
  groupers : List κ   -- `tgtkey` of each `_grouper`, by number

/-- `_grouper_create` (:625-637): a new grouper becomes the current one. -/
def cGrouperCreate (g : CGroupby α κ) (tgtkey : κ) : CGroupby α κ :=
  { g with groupers := g.groupers ++ [tgtkey], currgrouper := some g.groupers.length }

/-- `itertools_groupby_impl` (:456-475). The input's exception is not modelled. -/
def cGroupbyNew (iterable : Obj α) : Py (CGroupby α κ) :=
  match getIter iterable with
  | .error e => .error e
  | .ok ⟨l, _⟩ => .ok { it := l, tgtkey := none, currkey := none, currvalue := none,
                        currgrouper := none, groupers := [] }

/-- `groupby_step` (:505-529): `none` is the `-1` (exhausted) return. -/
def cGroupbyStep (key : α → κ) (g : CGroupby α κ) : Option (CGroupby α κ) :=
  match g.it with
  | [] => none
  | v :: rest => some { g with it := rest, currvalue := some v, currkey := some (key v) }

/-- The tests at the head of that loop: `true` means "call `groupby_step`". -/
def gbAdvance : Option κ → Option κ → Bool
  | none, _ => true
  | some _, none => false
  | some ck, some tk => tk == ck

/-- The `for (;;)` loop of `groupby_next` (:539-566). The flag is `true` for
the `break` out of the loop and `false` when `groupby_step` failed; the steps
already taken stay in the state either way. Each iteration but the last
consumes an item, so `it.length + 1` iterations are enough. -/
def cGroupbySkip (key : α → κ) : Nat → CGroupby α κ → Bool × CGroupby α κ
  | 0, g => (false, g)
  | fuel + 1, g =>
    if !gbAdvance g.currkey g.tgtkey then (true, g)
    else match cGroupbyStep key g with
      | none => (false, g)
      | some g => cGroupbySkip key fuel g

/-- `groupby_next` (:532-575). -/
def cGroupbyNext (key : α → κ) (g : CGroupby α κ) : Option κ × CGroupby α κ :=
  let g := { g with currgrouper := none }
  match cGroupbySkip key (g.it.length + 1) g with
  | (false, g) => (none, g)
  | (true, g) =>
    let ck := g.currkey.getD default
    (some ck, cGrouperCreate { g with tgtkey := some ck } ck)

/-- `_grouper_next` (:662-696). -/
def cGrouperNext (key : α → κ) (g : CGroupby α κ) (j : Nat) : Option α × CGroupby α κ :=
  if g.currgrouper != some j then (none, g)
  else
    let g' := if g.currvalue.isNone then cGroupbyStep key g else some g
    match g' with
    | none => (none, g)
    | some g =>
      if g.groupers.getD j default == g.currkey.getD default then
        (g.currvalue, { g with currvalue := none, currkey := none })
      else (none, g)

/-- `itertools__grouper_impl` (:617-622) on an existing groupby object. -/
def cGrouperDirect (g : CGroupby α κ) (k : κ) : CGroupby α κ := cGrouperCreate g k

def cGroupbyOps (key : α → κ) : CGroupby α κ → List (GbOp κ) → List (Option κ ⊕ Option α)
  | _, [] => []
  | g, .outer :: ops => let (r, g) := cGroupbyNext key g; .inl r :: cGroupbyOps key g ops
  | g, .group j :: ops =>
    if j < g.groupers.length then
      let (r, g) := cGrouperNext key g j; .inr r :: cGroupbyOps key g ops
    else cGroupbyOps key g ops
  | g, .direct k :: ops => cGroupbyOps key (cGrouperDirect g k) ops

def cGroupby (key : α → κ) (iterable : Obj α) (ops : List (GbOp κ)) : Py (List (Option κ ⊕ Option α)) :=
  match cGroupbyNew iterable with
  | .error e => .error e
  | .ok g => .ok (cGroupbyOps key g ops)

/-! ### Doc groupby: two kinds of generator frames sharing `nonlocal` state -/

inductive GenPc where
  | fresh      -- created, not started
  | suspended  -- suspended at a `yield`
  | done
  deriving Repr, DecidableEq

structure DocGroupby (α κ : Type) where
  it : List α
  currValue : α
  currKey : κ
  targetKey : κ
  exhausted : Bool
  outer : GenPc
  groups : List (κ × GenPc)   -- `(target_key, frame state)` of each `_grouper`

/-- `next()` on the `j`-th `_grouper(target_key)` generator (rst:436-444). -/
def docGrouperNext (key : α → κ) (d : DocGroupby α κ) (j : Nat) : Option α × DocGroupby α κ :=
  let (tk, pc) := d.groups.getD j (default, .done)
  let setPc (d : DocGroupby α κ) (pc : GenPc) := { d with groups := d.groups.set j (tk, pc) }
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

/-- `for _ in curr_group: pass` (rst:460-461). -/
def docExhaustGroup (key : α → κ) (d : DocGroupby α κ) (j : Nat) : Nat → DocGroupby α κ
  | 0 => d
  | fuel + 1 =>
    match docGrouperNext key d j with
    | (none, d) => d
    | (some _, d) => docExhaustGroup key d j fuel

/-- The `while not exhausted:` body up to its `yield` (rst:456-459). -/
def docGroupbyLoopHead (d : DocGroupby α κ) : Option κ × DocGroupby α κ :=
  if d.exhausted then (none, { d with outer := .done })
  else
    let d := { d with targetKey := d.currKey, groups := d.groups ++ [(d.currKey, GenPc.fresh)] }
    (some d.currKey, { d with outer := .suspended })

/-- `next()` on the doc's `groupby` generator (rst:431-461). -/
def docGroupbyNext (key : α → κ) (d : DocGroupby α κ) : Option κ × DocGroupby α κ :=
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

def docGroupbyOps (key : α → κ) : DocGroupby α κ → List (GbOp κ) → List (Option κ ⊕ Option α)
  | _, [] => []
  | d, .outer :: ops => let (r, d) := docGroupbyNext key d; .inl r :: docGroupbyOps key d ops
  | d, .group j :: ops =>
    if j < d.groups.length then
      let (r, d) := docGrouperNext key d j; .inr r :: docGroupbyOps key d ops
    else docGroupbyOps key d ops
  | d, .direct _ :: ops => docGroupbyOps key d ops

def docGroupbyInit (l : List α) : DocGroupby α κ :=
  { it := l, currValue := default, currKey := default, targetKey := default, exhausted := false,
    outer := .fresh, groups := [] }

def docGroupby (key : α → κ) (iterable : Obj α) (ops : List (GbOp κ)) : Py (List (Option κ ⊕ Option α)) :=
  match getIter iterable with
  | .error e => .error e
  | .ok ⟨l, _⟩ => .ok (docGroupbyOps key (docGroupbyInit l) ops)

/-! ## tee -/

inductive TeeOp where
  | next (k : Nat)
  | tee (k m : Nat)
  | copy (k : Nat)
  | ctor (k : Nat)
  deriving Repr, DecidableEq

/-- Result of one `next()`. -/
inductive NextRes (α : Type) where
  | val (a : α)
  | stop
  | exc (e : PyExc)

/-- `#define LINKCELLS 57` (:728). -/
def LINKCELLS : Nat := 57

/-- The shared chain of `teedataobject`s (:730-737): block `b` holds
`blocks[b]` (`numread` values); `nextlink` of block `b` exists iff
`b + 1 < blocks.length`. Each tee is `(dataobj, index)`. -/
structure CTee (α : Type) where
  it : Src α
  blocks : List (List α)
  tees : List (Nat × Nat)

/-- `teedataobject_jumplink` (:769-778) as used by `tee_next` (:957-964): at
`index >= LINKCELLS` move to the next block, creating it if needed
(`teedataobject_newinternal`, :752-766). -/
def teeJump (t : CTee α) (b i : Nat) : CTee α × Nat × Nat :=
  if i ≥ LINKCELLS then
    let t := if b + 1 < t.blocks.length then t else { t with blocks := t.blocks ++ [[]] }
    (t, b + 1, 0)
  else (t, b, i)

/-- `teedataobject_getitem_lock_held` (:781-805), its wrapper
`teedataobject_getitem` (:808-815) and the `to->index++` of `tee_next`
(:965-969): a stored value, or (lead iterator) pull one more item. -/
def teeGetitem (t : CTee α) (k b i : Nat) : NextRes α × CTee α :=
  let blk := t.blocks.getD b []
  if i < blk.length then
    (.val (blk.getD i default), { t with tees := t.tees.set k (b, i + 1) })
  else
    match t.it.next with
    | .done => (.stop, t)
    | .fail e rest => (.exc e, { t with it := rest })
    | .item v rest =>
      (.val v, { t with it := rest, blocks := t.blocks.set b (blk ++ [v]),
                        tees := t.tees.set k (b, i + 1) })

/-- `tee_next` (:949-971, GIL build). -/
def cTeeNext (t : CTee α) (k : Nat) : NextRes α × CTee α :=
  let (b, i) := t.tees.getD k (0, 0)
  let (t, b, i) := teeJump t b i
  teeGetitem { t with tees := t.tees.set k (b, i) } k b i

def cTeeOps : CTee α → List TeeOp → List (NextRes α) × CTee α
  | t, [] => ([], t)
  | t, .next k :: ops =>
    if k < t.tees.length then
      let (r, t) := cTeeNext t k
      let (rs, t) := cTeeOps t ops
      (r :: rs, t)
    else cTeeOps t ops
  | t, .tee k m :: ops =>
    -- `itertools_tee_impl` on a tee: `tee_fromiterable` then `tee_copy`
    if k < t.tees.length then
      cTeeOps { t with tees := t.tees ++ List.replicate m (t.tees.getD k (0, 0)) } ops
    else cTeeOps t ops
  | t, .copy k :: ops =>
    if k < t.tees.length then cTeeOps { t with tees := t.tees ++ [t.tees.getD k (0, 0)] } ops
    else cTeeOps t ops
  | t, .ctor k :: ops =>
    -- `itertools__tee_impl` (:1093-1098) → `tee_fromiterable` (:1051-1082): a tee is copied
    if k < t.tees.length then cTeeOps { t with tees := t.tees ++ [t.tees.getD k (0, 0)] } ops
    else cTeeOps t ops

/-- `itertools_tee_impl` (:1161-1196) on a non-tee input: `n` through the
`Py_ssize_t(allow_negative=False)` converter (Modules/clinic/itertoolsmodule.c.h:338-352);
`n == 0` returns `()` without touching the iterable;
otherwise `PyObject_GetIter` and `tee_fromiterable` (:1051-1082). Results of the
ops, then the number of items pulled from the input. -/
def cTee (iterable : Obj α) (n : Int) (ops : List TeeOp) : Py (List (NextRes α) × Nat) :=
  match asSsize n with
  | .error e => .error e
  | .ok n =>
    if n < 0 then .error (.valueError "n cannot be negative")
    else if !tupleNewOk n then .error memoryError
    else if n = 0 then .ok ([], 0)
    else match getIter iterable with
      | .error e => .error e
      | .ok it =>
        let t : CTee α := { it := it, blocks := [[]], tees := List.replicate n.toNat (0, 0) }
        let (rs, t') := cTeeOps t ops
        .ok (rs, it.items.length - t'.it.items.length)

/-- What the `next` argument of `_tee_dataobject` is. -/
inductive TeeNextArg where
  | none
  | dataobject
  | other
  deriving Repr, DecidableEq

/-- `itertools_teedataobject_impl` (:885-926): the constructor's validation; on
success the block's `values` and whether `nextlink` is set. -/
def cTeeDataNew (values : List α) (next : TeeNextArg) : Py (List α × Bool) :=
  let invalid : Py (List α × Bool) := .error (.valueError "Invalid arguments")
  if values.length > LINKCELLS then invalid
  else if values.length = LINKCELLS then
    match next with
    | .none => .ok (values, false)
    | .dataobject => .ok (values, true)
    | .other => invalid
  else
    match next with
    | .none => .ok (values, false)
    | _ => invalid

/-- The doc's `_tee` objects (rst:703-723) sharing one chain of
`[value, next]` links: link `c` is filled iff `c < values.length`; each tee
holds its current link number. -/
structure DocTee (α : Type) where
  it : Src α
  values : List α
  tees : List Nat

/-- `_tee.__next__` (rst:717-723). -/
def docTeeNext (t : DocTee α) (k : Nat) : NextRes α × DocTee α :=
  let c := t.tees.getD k 0
  if c < t.values.length then
    (.val (t.values.getD c default), { t with tees := t.tees.set k (c + 1) })
  else
    match t.it.next with
    | .done => (.stop, t)
    | .fail e rest => (.exc e, { t with it := rest })
    | .item v rest =>
      (.val v, { t with it := rest, values := t.values ++ [v], tees := t.tees.set k (c + 1) })

def docTeeOps : DocTee α → List TeeOp → List (NextRes α) × DocTee α
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
  | t, .ctor k :: ops =>
    if k < t.tees.length then docTeeOps { t with tees := t.tees ++ [t.tees.getD k 0] } ops
    else docTeeOps t ops

/-- rst:692-701: bare `ValueError` for `n < 0`, `()` for `n == 0`. -/
def docTee (iterable : Obj α) (n : Int) (ops : List TeeOp) : Py (List (NextRes α) × Nat) :=
  if n < 0 then .error (.valueError "")
  else if n = 0 then .ok ([], 0)
  else match getIter iterable with
    | .error e => .error e
    | .ok it =>
      let t : DocTee α := { it := it, values := [], tees := List.replicate n.toNat 0 }
      let (rs, t') := docTeeOps t ops
      .ok (rs, it.items.length - t'.it.items.length)

end PyLean.Itertools
