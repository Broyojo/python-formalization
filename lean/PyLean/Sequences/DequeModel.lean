import PyLean.Sequences.ListModel

/-!
Model of `collections.deque` (`Modules/_collectionsmodule.c`, CPython 3.15.2).

## Representation of the block structure

A deque is a doubly-linked chain of blocks of `BLOCKLEN = 64` slots. Its items
occupy `leftblock[leftindex..]`, then whole middle blocks, then
`rightblock[..rightindex]`; the chain never has an empty block at either end
(`deque_pop_impl`/`deque_popleft_impl` free a block as soon as it empties,
`deque_append_lock_held` adds one only to store an item). So the chain is
determined by `leftindex` and the number of items, and we number blocks
`0, 1, ...` from `leftblock`: slot `j` of block `b` holds item number
`b * 64 + j - leftindex` (or is unused). `rightblock` is block
`(leftindex + len - 1) / 64` (`rbNum`), and a walk past it is a NULL
pointer.

The record keeps `leftindex`, `rightindex`, the items, `state` (the mutation
counter; `size_t` in C, whose wrap after 2**64 mutations is not modelled) and
`maxlen` as the C struct does (`maxlen = -1` when unbounded), plus the type's
name (`"deque"` or a subclass that does not override `__new__`/`__init__`).
`Deque.WF` is the layout invariant documented at
_collectionsmodule.c:103-125, which every operation preserves. The free-block
list only matters for allocation (`newblock`, `freeblock`), which never fails
in this model.

## Elements

Elements are of an abstract type `α`. `PyObject_RichCompareBool(a, b, Py_EQ)`
is a parameter `cmp : Cmp α`: it may raise and may mutate the deque being
searched, which is what the `state` checks of `deque_count_impl`,
`deque_index_impl`, `deque_remove_impl` and `deque_contains_lock_held` are for.
`pureCmp f` is the comparison of an element type whose `__eq__` is a pure
function `f` returning a truth value.
-/

namespace PyLean.Sequences

open PyLean

def BLOCKLEN : Int := 64
/-- `CENTER = (BLOCKLEN - 1) / 2`. -/
def CENTER : Int := 31

structure Deque (α : Type) where
  left : Int
  right : Int
  items : List α
  maxlen : Int
  state : Nat
  tname : String
  deriving Repr, DecidableEq

instance {α : Type} : Inhabited (Deque α) := ⟨⟨CENTER + 1, CENTER, [], -1, 0, "deque"⟩⟩

/-- `finalize_iterator` (_collectionsmodule.c:438-450), called once `tp_iternext` has
returned NULL: `e` is the exception then set (`PyErr_Occurred()`, `none` for plain
exhaustion). `StopIteration` is cleared, any other exception propagates. -/
def finalizeIterator (e : Option PyExc) : Py Unit :=
  match e with
  | none => .ok ()
  | some .stopIteration => .ok ()
  | some e => .error e

/-- One `tp_iternext` call made from inside a method of deque `d`: the iterator runs
arbitrary Python code, which sees `d` as it stands and may change it (append, clear,
re-initialise it with `d.__init__(maxlen=...)`, ...), then yields an item or raises
(`StopIteration` included). -/
abbrev NextFn (α : Type) := Deque α → Py α × Deque α

/-- An iterable as `deque_extend_impl` / `deque_extendleft_impl` / `deque_init_impl`
see it (other than the deque itself): `PyObject_GetIter(iterable)` (`getIter`: `__iter__`
runs, may change the deque, and may raise; a non-iterable raises `TypeError`), then the
`tp_iternext` calls in order. After the last one `tp_iternext` returns NULL with no
exception set; a call that raises ends the iteration. A finite iterator is a list of
calls (the scope: an endless iterator never returns from `extend`). -/
structure ReIter (α : Type) where
  getIter : Deque α → Py Unit × Deque α
  nexts : List (NextFn α)

/-- An iterator that does not touch the deque: it yields `xs`, then ends with `e`
(`none`: plain exhaustion). -/
def ReIter.ofList {α : Type} (xs : List α) (e : Option PyExc) : ReIter α :=
  ⟨fun d => (.ok (), d), xs.map (fun x d => (.ok x, d)) ++
    (match e with | none => [] | some e => [fun d => (.error e, d)])⟩

/-- A `PyIterable` as a `ReIter`: a non-iterable fails in `PyObject_GetIter`. -/
def ReIter.ofIterable {α : Type} : PyIterable α → ReIter α
  | .notIterable t => ⟨fun d => (.error (notIterableErr t), d), []⟩
  | .iter xs e => ReIter.ofList xs e

/-- The `maxlen` argument of `deque_init_impl`. -/
inductive MaxlenArg where
  | absent
  | int (n : Int)
  /-- An object that is neither `None` nor an `int`. -/
  | other
  deriving Repr, DecidableEq

/-- `PyObject_RichCompareBool(a, b, Py_EQ)` run on behalf of a method of deque
`d`: a truth value or an exception, and `d` as the comparison left it. -/
abbrev Cmp (α : Type) := Deque α → α → α → Py Bool × Deque α

/-- A pure `__eq__` that returns a truth value. -/
def pureCmp {α : Type} (f : α → α → Bool) : Cmp α := fun d a b => (.ok (f a b), d)

namespace Deque

variable {α : Type} [Inhabited α]

def size (d : Deque α) : Int := d.items.length

/-- The layout invariant, _collectionsmodule.c:103-125: both indices in
`[0, BLOCKLEN)`, `(leftindex + len - 1) % BLOCKLEN == rightindex`, an empty
deque has `leftindex == rightindex + 1` (in one block). -/
def Layout (d : Deque α) : Prop :=
  0 ≤ d.left ∧ d.left < 64 ∧ 0 ≤ d.right ∧ d.right < 64 ∧
  (d.left + d.size - 1) % 64 = d.right ∧ (d.size = 0 → d.left = d.right + 1)

/-- `maxlen` is `-1` or bounds the length. -/
def MaxOk (d : Deque α) : Prop := d.maxlen = -1 ∨ (0 ≤ d.maxlen ∧ d.size ≤ d.maxlen)

def WF (d : Deque α) : Prop := d.Layout ∧ d.MaxOk

/-- Number of the right block. -/
def rbNum (d : Deque α) : Int := (d.left + d.size - 1) / 64

/-- Read slot `j` of block `b` (`b->data[j]`). Block numbers outside
`[0, rbNum]` are a NULL dereference; an unused slot holds garbage. -/
def read (d : Deque α) (b j : Int) : Py α :=
  if b < 0 ∨ b > d.rbNum then .error (cUB "NULL block")
  else
    let k := b * 64 + j - d.left
    if 0 ≤ j ∧ j < 64 ∧ 0 ≤ k ∧ k < d.size then .ok (ix d.items k)
    else .error (cUB "unused slot")

/-- Write slot `j` of block `b`. -/
def write (d : Deque α) (b j : Int) (v : α) : Py (Deque α) :=
  if b < 0 ∨ b > d.rbNum then .error (cUB "NULL block")
  else
    let k := b * 64 + j - d.left
    if 0 ≤ j ∧ j < 64 ∧ 0 ≤ k ∧ k < d.size then .ok { d with items := d.items.set k.toNat v }
    else .error (cUB "unused slot")

/-- `deque_new` (_collectionsmodule.c:203-233): one block, empty and centred
(`leftindex = CENTER + 1`, `rightindex = CENTER`, :225-226), `state = 0`, and
`maxlen = -1` (:228), so `deque.__new__(deque).maxlen is None` before any `__init__`. -/
def new (tname : String := "deque") : Deque α := ⟨CENTER + 1, CENTER, [], -1, 0, tname⟩

/-- `deque_pop_impl` (_collectionsmodule.c:245-278). -/
def pop (d : Deque α) : Py (α × Deque α) :=
  if d.size = 0 then .error (.indexError "pop from an empty deque")
  else
    let item := ix d.items (d.size - 1)
    let items := d.items.dropLast
    let right := d.right - 1
    let state := d.state + 1
    if right < 0 then
      if items.length ≠ 0 then .ok (item, { d with items, state, right := 64 - 1 })
      else .ok (item, { d with items, state, left := CENTER + 1, right := CENTER })
    else .ok (item, { d with items, state, right })

/-- `deque_popleft_impl` (_collectionsmodule.c:290-324). -/
def popleft (d : Deque α) : Py (α × Deque α) :=
  if d.size = 0 then .error (.indexError "pop from an empty deque")
  else
    let item := ix d.items 0
    let items := d.items.drop 1
    let left := d.left + 1
    let state := d.state + 1
    if left = 64 then
      if items.length ≠ 0 then .ok (item, { d with items, state, left := 0 })
      else .ok (item, { d with items, state, left := CENTER + 1, right := CENTER })
    else .ok (item, { d with items, state, left })

/-- `NEEDS_TRIM(deque, maxlen)`: `(size_t)maxlen < (size_t)len`, i.e.
`0 <= maxlen < len` (_collectionsmodule.c:338). -/
def needsTrim (d : Deque α) (maxlen : Int) : Bool := decide (0 ≤ maxlen ∧ maxlen < d.size)

/-- Drop the popped item of a trim (the C code `Py_DECREF`s it). The trims
only run on non-empty deques, so the error branch is unreachable. -/
def snd' (r : Py (α × Deque α)) (d : Deque α) : Deque α :=
  match r with
  | .ok (_, d') => d'
  | .error _ => d

/-- `deque_append_lock_held` (_collectionsmodule.c:341-366): a new right
block when `rightindex == BLOCKLEN - 1`, store, then trim from the left. -/
def appendM (d : Deque α) (x : α) (maxlen : Int) : Deque α :=
  let right := if d.right = 64 - 1 then -1 else d.right
  let d := { d with items := d.items ++ [x], right := right + 1 }
  if d.needsTrim maxlen then snd' d.popleft d else { d with state := d.state + 1 }

/-- `deque_appendleft_lock_held` (_collectionsmodule.c:389-415). -/
def appendleftM (d : Deque α) (x : α) (maxlen : Int) : Deque α :=
  let left := if d.left = 0 then 64 else d.left
  let d := { d with items := x :: d.items, left := left - 1 }
  if d.needsTrim maxlen then snd' d.pop d else { d with state := d.state + 1 }

/-- `d.append(x)` / `d.appendleft(x)` (_collectionsmodule.c:380-386, 429-435). -/
def append (d : Deque α) (x : α) : Deque α := d.appendM x d.maxlen
def appendleft (d : Deque α) (x : α) : Deque α := d.appendleftM x d.maxlen

/-- The loop `while ((item = iternext(it)) != NULL) push(deque, item, maxlen)` of
`deque_extend_impl` (_collectionsmodule.c:512-518, `push` = `deque_append_lock_held`)
and `deque_extendleft_impl` (:567-573, `deque_appendleft_lock_held`), then
`finalize_iterator` (:519, :574). `maxlen` is the local read once at entry
(:484, :539), not `deque->maxlen`: an iterator that re-initialises the deque does not
change the bound the loop applies. Every call sees the deque the previous push left. -/
def pushLoop (push : Deque α → α → Int → Deque α) (maxlen : Int) :
    List (NextFn α) → Deque α → Py Unit × Deque α
  | [], d => (finalizeIterator none, d)
  | nx :: rest, d =>
    match nx d with
    | (.error e, d) => (finalizeIterator (some e), d)
    | (.ok x, d) => pushLoop push maxlen rest (push d x maxlen)

/-- `consume_iterator` (_collectionsmodule.c:455-465): call `tp_iternext` until it
returns NULL, dropping the items, then `finalize_iterator`. -/
def consumeLoop : List (NextFn α) → Deque α → Py Unit × Deque α
  | [], d => (finalizeIterator none, d)
  | nx :: rest, d =>
    match nx d with
    | (.error e, d) => (finalizeIterator (some e), d)
    | (.ok _, d) => consumeLoop rest d

/-- `deque_extend_impl` (_collectionsmodule.c:479-520) for an iterable other than the
deque: `maxlen` read at :484, `PyObject_GetIter` (:497-499), `consume_iterator` when that
`maxlen` is 0 (:501-502), the "start filling from the left" heuristic on a deque that is
empty *now* (:505-510), then the loop. -/
def extendRe (d : Deque α) (it : ReIter α) : Py Unit × Deque α :=
  let maxlen := d.maxlen
  match it.getIter d with
  | (.error e, d) => (.error e, d)
  | (.ok (), d) =>
    if maxlen = 0 then consumeLoop it.nexts d
    else
      let d := if d.size = 0 then { d with left := 1, right := 0 } else d
      pushLoop appendM maxlen it.nexts d

/-- `deque_extendleft_impl` (_collectionsmodule.c:534-575): `maxlen` at :539,
`PyObject_GetIter` :552-554, `consume_iterator` :556-557, heuristic :560-565, loop. -/
def extendleftRe (d : Deque α) (it : ReIter α) : Py Unit × Deque α :=
  let maxlen := d.maxlen
  match it.getIter d with
  | (.error e, d) => (.error e, d)
  | (.ok (), d) =>
    if maxlen = 0 then consumeLoop it.nexts d
    else
      let d := if d.size = 0 then { d with left := 64 - 1, right := 64 - 2 } else d
      pushLoop appendleftM maxlen it.nexts d

/-- `d += iterable` (`deque_inplace_concat`, _collectionsmodule.c:578-590): `deque_extend`,
then `d` itself on success. -/
def iaddRe (d : Deque α) (it : ReIter α) : Py Unit × Deque α := d.extendRe it

/-- What `extendRe` does with an iterator yielding `xs` that does not touch the deque
(`extendRe_ofList` in `DequeOps` proves it): nothing when `maxlen == 0`, otherwise
the heuristic and one `deque_append_lock_held` per item. -/
def extend (d : Deque α) (xs : List α) : Deque α :=
  if d.maxlen = 0 then d
  else
    let d := if d.size = 0 then { d with left := 1, right := 0 } else d
    xs.foldl (fun d x => d.appendM x d.maxlen) d

/-- The same for `extendleftRe`. -/
def extendleft (d : Deque α) (xs : List α) : Deque α :=
  if d.maxlen = 0 then d
  else
    let d := if d.size = 0 then { d with left := 64 - 1, right := 64 - 2 } else d
    xs.foldl (fun d x => d.appendleftM x d.maxlen) d

/-- `d.extend(iterable)` / `d.extendleft(iterable)` / `d += iterable` for an iterable
that does not touch the deque. -/
def extendIter (d : Deque α) (src : PyIterable α) : Py Unit × Deque α := d.extendRe (.ofIterable src)
def extendleftIter (d : Deque α) (src : PyIterable α) : Py Unit × Deque α :=
  d.extendleftRe (.ofIterable src)
def iadd (d : Deque α) (src : PyIterable α) : Py Unit × Deque α := d.iaddRe (.ofIterable src)

/-- `d.extend(d)` / `d += d` (_collectionsmodule.c:487-495): `PySequence_List(d)`, then
`deque_extend` over that private list, which no Python code can reach; `d.extendleft(d)`
(:542-550) the same with `deque_extendleft_impl`. -/
def extendSelf (d : Deque α) : Deque α := d.extend d.items
def extendleftSelf (d : Deque α) : Deque α := d.extendleft d.items

/-- `deque_clear` (_collectionsmodule.c:721-803): a fresh centred block. The
`alternate_method` needs a failed `newblock`. `d.clear()`
(`deque_clearmethod_impl`, :815-820) calls it. -/
def clear (d : Deque α) : Deque α :=
  if d.size = 0 then d
  else { d with items := [], left := CENTER + 1, right := CENTER, state := d.state + 1 }

/-- The fill of `deque_copy_impl` (_collectionsmodule.c:608-646), exact `deque`
type: a new deque with the same `maxlen`, filled from the left by walking the
blocks of the old one. -/
def copyExact (d : Deque α) : Deque α :=
  let nd : Deque α := { (new : Deque α) with maxlen := d.maxlen }
  if d.size > 0 then
    (d.items.foldl (fun nd x => nd.appendM x nd.maxlen) { nd with left := 1, right := 0 })
  else nd

/-- `deque_init_impl` (_collectionsmodule.c:1755-1778): `maxlen` parsed (:1758-1767,
`None` and an absent argument both mean -1), stored (:1768), the deque cleared if it is
not empty (:1769-1770: a re-initialisation), then `deque_extend_impl` only when an
iterable was given (:1771-1776; `none` is `iterable == NULL`, which leaves the indices
where they are). An iterable equal to `d` is the self case of `deque_extend_impl`: the
cleared deque as a list, i.e. `some (.ofList [] none)`. -/
def initRe (d : Deque α) (iterable : Option (ReIter α)) (maxlenobj : MaxlenArg) : Py Unit × Deque α :=
  let parsed : Py Int := match maxlenobj with
    | .absent => .ok (-1)
    | .other => .error (.typeError "an integer is required")
    | .int m =>
      match asSsize m with
      | .error e => .error e
      | .ok m => if m < 0 then .error (.valueError "maxlen must be non-negative") else .ok m
  match parsed with
  | .error e => (.error e, d)
  | .ok maxlen =>
    let d : Deque α := { d with maxlen }
    let d : Deque α := if d.size > (0 : Int) then d.clear else d
    match iterable with
    | none => (.ok (), d)
    | some it => d.extendRe it

/-- `d.__init__(iterable, maxlen)` for an iterable that does not touch the deque. -/
def init (d : Deque α) (src : PyIterable α) (maxlenobj : MaxlenArg) : Py Unit × Deque α :=
  d.initRe (some (.ofIterable src)) maxlenobj

/-- `type(tname)(xs, maxlen)`: `deque_new` then `deque_init`. -/
def makeOf (tname : String) (xs : List α) (maxlen : MaxlenArg) : Py (Deque α) :=
  let (r, d) := (new tname).init (.iter xs none) maxlen
  match r with
  | .ok () => .ok d
  | .error e => .error e

/-- `type(tname)()` / `type(tname)(maxlen=m)`: `deque_new`, then `deque_init` with
`iterable == NULL`. -/
def makeEmpty (tname : String) (maxlen : MaxlenArg) : Py (Deque α) :=
  let (r, d) := (new tname).initRe none maxlen
  match r with
  | .ok () => .ok d
  | .error e => .error e

/-- `deque(xs, maxlen)`. -/
def make (xs : List α) (maxlen : MaxlenArg) : Py (Deque α) := makeOf "deque" xs maxlen

/-- `deque_copy_impl` (_collectionsmodule.c:602-661): the exact type fills a new
deque; a subclass calls `type(d)(d)` or `PyObject_CallFunction(type(d), "On", d,
d.maxlen)` (:648-652), which reads the whole `Py_ssize_t`. `d.__copy__()`
(`deque___copy___impl`, :671-675) is the same. The "must return a deque" check (:653-659)
needs a subclass with its own `__new__`. -/
def copy (d : Deque α) : Py (Deque α) :=
  if d.tname = "deque" then .ok d.copyExact
  else if d.maxlen < 0 then makeOf d.tname d.items .absent
  else makeOf d.tname d.items (.int d.maxlen)

/-- The right operand of `d + other`, as `PyObject_IsInstance(other, deque)`
(Objects/abstract.c `object_isinstance`) classifies it: a deque instance, or an object
whose `__class__` claims to be one, iterated by `deque_extend_impl` (`src`: what that
iteration yields; it runs on the new deque, which no Python code can reach, so it is a
`PyIterable`); anything else (`tname`: its type's name); or `__class__` raising (an
exception other than `AttributeError`). -/
inductive ConcatArg (α : Type) where
  | inst (src : PyIterable α)
  | notInst (tname : String)
  | raises (e : PyExc)

/-- A deque operand: iterating it yields its items. -/
def ConcatArg.ofDeque {α : Type} (o : Deque α) : ConcatArg α := .inst (.iter o.items none)

/-- `d + other` (`deque_concat_lock_held`, _collectionsmodule.c:678-707): the
instance check (:684-691: `rv < 0` propagates, `rv == 0` is the `TypeError`), `copy`
(:693-695), then `deque_extend_impl` on the copy (:699-703), whose failure discards it.
`deque_concat` (:710-718) adds only the lock. -/
def concat (d : Deque α) (other : ConcatArg α) : Py (Deque α) :=
  match other with
  | .raises e => .error e
  | .notInst t => .error (.typeError s!"can only concatenate deque (not \"{t}\") to deque")
  | .inst src =>
    match d.copy with
    | .error e => .error e
    | .ok nd =>
      match nd.extendIter src with
      | (.error e, _) => .error e
      | (.ok (), nd) => .ok nd

/-! ### Rotation -/

/-- The `n > 0` loop of `_deque_rotate` (_collectionsmodule.c:978-1021): a
new left block when `leftindex == 0`, then move the last
`m = min(n, rightindex + 1, leftindex)` items from the right block to the
left block, freeing the right block once it empties. -/
def rotRight : Nat → Int → Int → List α → Int → Py (Int × Int × List α)
  | 0, _, _, _, _ => .error .modelFuel
  | fuel + 1, li, ri, items, n =>
    if n > 0 then
      let li := if li = 0 then 64 else li
      let m := min (min n (ri + 1)) li
      let ri := ri - m
      let li := li - m
      let k := items.length - m.toNat
      let items := items.drop k ++ items.take k
      let n := n - m
      let ri := if ri < 0 then 64 - 1 else ri
      rotRight fuel li ri items n
    else .ok (li, ri, items)

/-- The `n < 0` loop of `_deque_rotate` (_collectionsmodule.c:1022-1065). -/
def rotLeft : Nat → Int → Int → List α → Int → Py (Int × Int × List α)
  | 0, _, _, _, _ => .error .modelFuel
  | fuel + 1, li, ri, items, n =>
    if n < 0 then
      let ri := if ri = 64 - 1 then -1 else ri
      let m := min (min (-n) (64 - li)) (64 - 1 - ri)
      let items := items.drop m.toNat ++ items.take m.toNat
      let li := li + m
      let ri := ri + m
      let n := n + m
      let li := if li = 64 then 0 else li
      rotLeft fuel li ri items n
    else .ok (li, ri, items)

/-- The normalisation at the top of `_deque_rotate` (_collectionsmodule.c:965-973);
C `%` truncates. -/
def rotNorm (len n : Int) : Int :=
  let halflen := len / 2
  if n > halflen ∨ n < -halflen then
    let n := n.tmod len
    if n > halflen then n - len else if n < -halflen then n + len else n
  else n

/-- `_deque_rotate(deque, n)` (_collectionsmodule.c:954-1076). -/
def rotateC (d : Deque α) (n : Int) : Py (Deque α) :=
  if d.size ≤ 1 then .ok d
  else
    let n := rotNorm d.size n
    let fuel := n.natAbs + 1
    let r := if n > 0 then rotRight fuel d.left d.right d.items n
      else rotLeft fuel d.left d.right d.items n
    match r with
    | .ok (li, ri, items) => .ok { d with left := li, right := ri, items, state := d.state + 1 }
    | .error e => .error e

/-- `d.rotate(n)`: Argument Clinic `Py_ssize_t` (default 1), then
`deque_rotate_impl` (_collectionsmodule.c:1090-1097). -/
def rotate (d : Deque α) (n : Int) : Py (Deque α) := do
  let n ← asSsize n
  d.rotateC n

/-! ### Searching -/

/-- Advance a `(block, index)` cursor by one slot (`index++; if (index ==
BLOCKLEN) { b = b->rightlink; index = 0; }`). -/
def step1 (b j : Int) : Int × Int := if j + 1 = 64 then (b + 1, 0) else (b, j + 1)

/-- The loop of `deque_count_impl` (_collectionsmodule.c:1169-1191): `count`
matches so far, `n` items left. -/
def countLoop (cmp : Cmp α) (v : α) (st : Nat) : Nat → Int → Int → Int → Deque α → Py Int × Deque α
  | 0, _, _, count, d => (.ok count, d)
  | n + 1, b, j, count, d =>
    match d.read b j with
    | .error e => (.error e, d)
    | .ok item =>
      match cmp d item v with
      | (.error e, d) => (.error e, d)
      | (.ok c, d) =>
        let count := count + (if c then 1 else 0)
        if st ≠ d.state then (.error (.named "RuntimeError" "deque mutated during iteration"), d)
        else
          let (b', j') := step1 b j
          countLoop cmp v st n b' j' count d

/-- `d.count(v)`, `deque_count_impl` (_collectionsmodule.c:1159-1193). -/
def count (d : Deque α) (cmp : Cmp α) (v : α) : Py Int × Deque α :=
  countLoop cmp v d.state d.items.length 0 d.left 0 d

/-- The search loops of `deque_index_impl` (_collectionsmodule.c:1301-1321),
`deque_contains_lock_held` (:1204-1223) and `deque_remove_impl` (:1472-1492):
walk `n` items comparing with `v`, starting at position `i`. A match wins over
the mutation check unless `checkFirst` (only `remove` tests the state before the
match), and mutation raises `mutExc`. -/
def scanLoop (cmp : Cmp α) (v : α) (st : Nat) (checkFirst : Bool) (mutExc : PyExc) :
    Nat → Int → Int → Int → Deque α → Py (Option Int) × Deque α
  | 0, _, _, _, d => (.ok none, d)
  | n + 1, i, b, j, d =>
    match d.read b j with
    | .error e => (.error e, d)
    | .ok item =>
      match cmp d item v with
      | (.error e, d) => (.error e, d)
      | (.ok c, d) =>
        if !checkFirst && c then (.ok (some i), d)
        else if st ≠ d.state then (.error mutExc, d)
        else if c then (.ok (some i), d)
        else
          let (b', j') := step1 b j
          scanLoop cmp v st checkFirst mutExc n (i + 1) b' j' d

def mutatedErr : PyExc := .named "RuntimeError" "deque mutated during iteration"

/-- `v in d`: `deque_contains_lock_held` and `deque_contains`
(_collectionsmodule.c:1196-1236). -/
def contains (d : Deque α) (cmp : Cmp α) (v : α) : Py Bool × Deque α :=
  match scanLoop cmp v d.state false mutatedErr d.items.length 0 0 d.left d with
  | (.ok r, d) => (.ok r.isSome, d)
  | (.error e, d) => (.error e, d)

/-- `deque_index_impl` (_collectionsmodule.c:1262-1324) after argument
conversion: clip, skip whole blocks, skip single slots, then search. The C code
returns `stop - n - 1`, which is the position `i` kept by `scanLoop`. -/
def indexC (d : Deque α) (cmp : Cmp α) (v : α) (start stop : Int) : Py Int × Deque α :=
  let size := d.size
  let start := if start < 0 then (if start + size < 0 then 0 else start + size) else start
  let stop := if stop < 0 then (if stop + size < 0 then 0 else stop + size) else stop
  let stop := if stop > size then size else stop
  let start := if start > stop then stop else start
  -- for (i=0 ; i < start - BLOCKLEN ; i += BLOCKLEN) b = b->rightlink;
  let nb := if start - 64 > 0 then (start - 64 + 63) / 64 else 0
  let i := nb * 64
  -- for ( ; i < start ; i++) { index++; ... }
  let (b, j) := (List.range (start - i).toNat).foldl (fun (bj : Int × Int) _ => step1 bj.1 bj.2) (nb, d.left)
  -- a walk from a NULL block would be undefined
  if b > d.rbNum + 1 ∨ nb - 1 > d.rbNum then (.error (cUB "walk past NULL"), d)
  else
    match scanLoop cmp v d.state false mutatedErr (stop - start).toNat start b j d with
    | (.ok (some k), d) => (.ok k, d)
    | (.ok none, d) => (.error (.valueError "deque.index(x): x not in deque"), d)
    | (.error e, d) => (.error e, d)

/-- `d.index(v[, start[, stop]])`: `_PyEval_SliceIndexNotNone` arguments. -/
def index (d : Deque α) (cmp : Cmp α) (v : α) (start stop : Option Int) : Py Int × Deque α :=
  d.indexC cmp v (sliceIndex (start.getD 0)) (sliceIndex (stop.getD ssizeMax))

/-! ### Item access -/

/-- `deque_item_lock_held` (_collectionsmodule.c:1384-1420) for `i` already
made non-negative by `PySequence_GetItem`; `deque_item` (:1423-1431) adds only
the lock. -/
def itemC (d : Deque α) (i : Int) : Py α :=
  if !validIndex i d.size then .error (.indexError "deque index out of range")
  else if i = 0 then d.read 0 d.left
  else if i = d.size - 1 then d.read d.rbNum d.right
  else
    let index := i
    let i := i + d.left
    let n := i / 64
    let i := i % 64
    if index < d.size / 2 then d.read n i
    else
      let n := (d.left + d.size - 1) / 64 - n
      d.read (d.rbNum - n) i

/-- `d[i]`: `PyObject_GetItem` → `PyNumber_AsSsize_t(key, IndexError)` →
`PySequence_GetItem` (adds `len` to a negative index), Objects/abstract.c:155-180, 1832-1853. -/
def getitem (d : Deque α) (i : Int) : Py α := do
  let i ← subIndex i
  d.itemC (if i < 0 then i + d.size else i)

/-- `deque_del_item` (_collectionsmodule.c:1434-1447): rotate, popleft, rotate back. -/
def delItem (d : Deque α) (i : Int) : Py (Deque α) := do
  let d ← d.rotateC (-i)
  let (_, d) ← d.popleft
  d.rotateC i

/-- `deque_ass_item_lock_held` (_collectionsmodule.c:1503-1532); `deque_ass_item`
(:1535-1543) adds only the lock. -/
def assItemC (d : Deque α) (i : Int) (v : Option α) : Py (Deque α) :=
  let len := d.size
  let halflen := (len + 1) / 2
  if !validIndex i len then .error (.indexError "deque index out of range")
  else match v with
  | none => d.delItem i
  | some v =>
    let index := i
    let i := i + d.left
    let n := i / 64
    let i := i % 64
    if index ≤ halflen then d.write n i v
    else
      let n := (d.left + d.size - 1) / 64 - n
      d.write (d.rbNum - n) i v

/-- `d[i] = v` / `del d[i]` (`PySequence_SetItem`/`PySequence_DelItem`). -/
def setitem (d : Deque α) (i : Int) (v : Option α) : Py (Deque α) := do
  let i ← subIndex i
  d.assItemC (if i < 0 then i + d.size else i) v

/-- `deque_remove_impl` (_collectionsmodule.c:1461-1500). The mutation check
raises `IndexError` here, unlike the other searches. -/
def remove (d : Deque α) (cmp : Cmp α) (v : α) : Py Unit × Deque α :=
  match scanLoop cmp v d.state true (.indexError "deque mutated during iteration")
      d.items.length 0 0 d.left d with
  | (.error e, d) => (.error e, d)
  | (.ok none, d) => (.error (.valueError "deque.remove(x): x not in deque"), d)
  | (.ok (some i), d) =>
    match d.delItem i with
    | .ok d => (.ok (), d)
    | .error e => (.error e, d)

/-- `deque_insert_impl` (_collectionsmodule.c:1347-1373) after the clinic
`Py_ssize_t` conversion. -/
def insertC (d : Deque α) (index : Int) (v : α) : Py (Deque α) := do
  let n := d.size
  if d.maxlen = n then throw (.indexError "deque already at its maximum size")
  if index ≥ n then return d.append v
  if index ≤ -n ∨ index = 0 then return d.appendleft v
  let d ← d.rotateC (-index)
  let d := if index < 0 then d.append v else d.appendleft v
  d.rotateC index

def insert (d : Deque α) (index : Int) (v : α) : Py (Deque α) := do
  let i ← asSsize index
  d.insertC i v

/-- `deque_reverse_impl` (_collectionsmodule.c:1109-1145): swap the items
under a left cursor and a right cursor `len / 2` times. -/
def reverseLoop (d : Deque α) : Nat → Int → Int → Int → Int → Py (Deque α)
  | 0, _, _, _, _ => .ok d
  | n + 1, lb, li, rb, ri => do
    let x ← d.read lb li
    let y ← d.read rb ri
    let d ← d.write lb li y
    let d ← d.write rb ri x
    let (lb, li) := step1 lb li
    let (rb, ri) := if ri - 1 < 0 then (rb - 1, 64 - 1) else (rb, ri - 1)
    reverseLoop d n lb li rb ri

def reverse (d : Deque α) : Py (Deque α) :=
  d.reverseLoop (d.items.length / 2) 0 d.left d.rbNum d.right

/-! ### Repetition -/

/-- `deque_inplace_repeat_lock_held` (_collectionsmodule.c:823-897) for a
`Py_ssize_t` count; `deque_inplace_repeat` (:900-908) adds only the lock. The
single-item case fills blocks directly. -/
def irepeatC (d : Deque α) (n : Int) : Py (Deque α) := do
  let size := d.size
  if size = 0 ∨ n = 1 then return d
  if n ≤ 0 then return d.clear
  if size = 1 then
    let item := ix d.items 0
    let n := if d.maxlen ≥ 0 ∧ n > d.maxlen then d.maxlen else n
    -- the block-filling loop: n - 1 more copies appended on the right
    let k := (n - 1).toNat
    let right := (d.right + (n - 1)) % 64
    return { d with items := d.items ++ List.replicate k item, right, state := d.state + 1 }
  if size > ssizeMax / n then throw memoryError
  let seq := d.items
  let n := if d.maxlen ≥ 0 ∧ n * size > d.maxlen then (d.maxlen + size - 1) / size else n
  return (List.range (n - 1).toNat).foldl (fun d _ => d.extend seq) d

/-- `d *= n` (`sequence_repeat` conversion, `deque_inplace_repeat`). -/
def irepeat (d : Deque α) (n : Int) : Py (Deque α) := do
  let n ← repeatCount n
  d.irepeatC n

/-- `d * n` (`deque_repeat`, _collectionsmodule.c:911-927): copy, then
repeat the copy in place. -/
def mul (d : Deque α) (n : Int) : Py (Deque α) := do
  let n ← repeatCount n
  let nd ← d.copy
  nd.irepeatC n

/-! ### Small slots -/

/-- `len(d)` (`deque_len`, _collectionsmodule.c:1239-1243). -/
def len (d : Deque α) : Int := d.size

/-- `d.maxlen` (`deque_get_maxlen`, _collectionsmodule.c:1803-1809). -/
def getMaxlen (d : Deque α) : Option Int := if d.maxlen < 0 then none else some d.maxlen

/-- Blocks in use, as `deque___sizeof___impl` counts them
(_collectionsmodule.c:1790-1800). -/
def blocks (d : Deque α) : Int := (d.left + d.size + 64 - 1) / 64

/-- `d.__sizeof__()`: `_PyObject_SIZE(type)` plus the blocks; a block is 528
bytes on LP64 (`sizeof(block)`: two links and 64 pointers). -/
def sizeof (d : Deque α) (basicsize : Int) : Int := basicsize + d.blocks * 528

/-! ### Iterators -/

/-- `dequeiterobject` (_collectionsmodule.c:1908-1914). `b` is numbered from the
`leftblock` of the deque at the time of the call; every operation that moves
blocks also changes `state`, so a stale `b` is never dereferenced. -/
structure Iter where
  b : Int
  index : Int
  state : Nat
  counter : Int
  deriving Repr, DecidableEq

/-- `deque_iter` (_collectionsmodule.c:1920-1938). -/
def iter (d : Deque α) : Iter := ⟨0, d.left, d.state, d.size⟩

/-- `deque_reviter` (_collectionsmodule.c:2100-2117). -/
def reviter (d : Deque α) : Iter := ⟨d.rbNum, d.right, d.state, d.size⟩

/-- `dequeiter_next_lock_held` (_collectionsmodule.c:1969-1993) and
`dequeiter_next` (:1996-2008): `.ok none` is `NULL` without an exception. -/
def iterNext (d : Deque α) (it : Iter) : Py (Option α) × Iter :=
  if d.state ≠ it.state then (.error mutatedErr, { it with counter := 0 })
  else if it.counter = 0 then (.ok none, it)
  else
    match d.read it.b it.index with
    | .error e => (.error e, it)
    | .ok item =>
      let index := it.index + 1
      let counter := it.counter - 1
      let it' : Iter := if index = 64 ∧ counter > 0 then { it with b := it.b + 1, index := 0, counter }
        else { it with index, counter }
      (.ok (some item), it')

/-- `dequereviter_next_lock_held` (_collectionsmodule.c:2120-2144) and
`dequereviter_next` (:2147-2158). The exhausted test comes first here, the state
test first in `iterNext`. -/
def reviterNext (d : Deque α) (it : Iter) : Py (Option α) × Iter :=
  if it.counter = 0 then (.ok none, it)
  else if d.state ≠ it.state then (.error mutatedErr, { it with counter := 0 })
  else
    match d.read it.b it.index with
    | .error e => (.error e, it)
    | .ok item =>
      let index := it.index - 1
      let counter := it.counter - 1
      let it' : Iter := if index < 0 ∧ counter > 0 then { it with b := it.b - 1, index := 64 - 1, counter }
        else { it with index, counter }
      (.ok (some item), it')

/-- The consuming loop of `dequeiter_new` (_collectionsmodule.c:2011-2043) and
`dequereviter_new` (:2161-2193): `for (i = 0; i < index; i++)`. -/
def iterAdvance (next : Deque α → Iter → Py (Option α) × Iter) (d : Deque α) : Nat → Iter → Py Iter
  | 0, it => .ok it
  | n + 1, it =>
    match next d it with
    | (.ok (some _), it') => iterAdvance next d n it'
    | (r, it') =>
      if it'.counter ≠ 0 then
        (match r with
         | .error e => .error e
         | .ok _ => .error (cUB "NULL without an exception"))
      else .ok it'

/-- `type(iter(d))(d, index)`: `index` is a `Py_ssize_t` (`"O!|n"`, default 0). A
negative `index` consumes nothing. The loop stops at exhaustion, so it runs at
most `len(d) + 1` times. -/
def iterNew (d : Deque α) (index : Int) : Py Iter := do
  let index ← asSsize index
  iterAdvance iterNext d (min index.toNat (d.items.length + 1)) d.iter

def reviterNew (d : Deque α) (index : Int) : Py Iter := do
  let index ← asSsize index
  iterAdvance reviterNext d (min index.toNat (d.items.length + 1)) d.reviter

/-- `it.__length_hint__()` (`dequeiter_len`, _collectionsmodule.c:2046-2051). -/
def iterLen (it : Iter) : Int := it.counter

/-- The second argument of `it.__reduce__()` (`dequeiter_reduce`,
_collectionsmodule.c:2056-2069): `(type(it), (d, len(d) - it.counter))`. -/
def iterReduce (d : Deque α) (it : Iter) : Int := d.size - it.counter

/-! ### Comparison, repr, pickling -/

/-- `PyList` repr of the items (`%R` of `PySequence_List(d)`), with the element
repr `r`, which may raise. -/
def listRepr (r : α → Py String) (xs : List α) : Py String := do
  let ss ← xs.mapM r
  return "[" ++ ", ".intercalate ss ++ "]"

/-- `deque_repr` (_collectionsmodule.c:1633-1661). `entered` is `Py_ReprEnter`
having found this deque already being printed. -/
def repr (d : Deque α) (r : α → Py String) (entered : Bool) : Py String := do
  if entered then return "[...]"
  let s ← listRepr r d.items
  if d.maxlen ≥ 0 then return s!"{d.tname}({s}, maxlen={d.maxlen})"
  else return s!"{d.tname}({s})"

/-- `deque___reduce___impl` (_collectionsmodule.c:1604-1628):
`(type(d), (), state, iter(d))` or `(type(d), ((), maxlen), state, iter(d))`;
the part that depends on the deque is the optional `maxlen` and the iterator. -/
def reduce (d : Deque α) : Option Int × Iter :=
  (if d.maxlen < 0 then none else some d.maxlen, d.iter)

/-- The search loop of `deque_richcompare` (_collectionsmodule.c:1696-1721) over two
iterators; `eq` and `rich` are `PyObject_RichCompareBool` for `Py_EQ` and for
`op`, assumed not to mutate the deques. The result for exhausted iterators
is the `switch` at :1724-1731. -/
def richLoop (eq : α → α → Py Bool) (rich : α → α → Py Bool) (op : CmpOp) (v w : Deque α) :
    Nat → Iter → Iter → Py Bool
  | 0, _, _ => .error .modelFuel
  | fuel + 1, it1, it2 =>
    match iterNext v it1 with
    | (.error e, _) => .error e
    | (.ok x, it1) =>
      match iterNext w it2 with
      | (.error e, _) => .error e
      | (.ok y, it2) =>
        match x, y with
        | some x, some y =>
          match eq x y with
          | .error e => .error e
          | .ok false => rich x y
          | .ok true => richLoop eq rich op v w fuel it1 it2
        | _, _ =>
          match op with
          | .lt => .ok y.isSome
          | .le => .ok x.isNone
          | .eq => .ok (x.isNone && y.isNone)
          | .ne => .ok (x.isSome || y.isSome)
          | .gt => .ok x.isSome
          | .ge => .ok y.isNone

/-- `deque_richcompare` (_collectionsmodule.c:1664-1740) for two deques: `same`
says `v is w`. A non-deque operand gives `NotImplemented` (:1672-1675), which
the difftest checks separately. -/
def richcompare (eq rich : α → α → Py Bool) (op : CmpOp) (same : Bool) (v w : Deque α) : Py Bool :=
  let vs := v.size
  let ws := w.size
  if op = .eq ∧ same then .ok true
  else if op = .eq ∧ vs ≠ ws then .ok false
  else if op = .ne ∧ same then .ok false
  else if op = .ne ∧ vs ≠ ws then .ok true
  else richLoop eq rich op v w (v.items.length + 1) v.iter w.iter

end Deque

end PyLean.Sequences
