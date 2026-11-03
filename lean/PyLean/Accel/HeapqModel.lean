import PyLean.Accel.Heap

/-!
# `heapq` with fallible, re-entrant comparisons

Model of the heap primitives of the C accelerator `Modules/_heapqmodule.c` and of its
pure-Python twin `Lib/heapq.py` (CPython 3.15.2) in which every comparison is Python code:
`PyObject_RichCompareBool(a, b, Py_LT)` in C, `a < b` followed by its truth test in Python.
Such a comparison can raise (in `__lt__` or in the `__bool__` of what `__lt__` returned),
keep state of its own, read the heap list, and mutate it (append, pop, clear, replace items).

* The world `HW σ α` is the heap list's contents `heap` together with everything else Python
  code can see or change, `st : σ`. Elements `α` are objects by identity: the model only moves
  them and never compares them with `=`.
* A comparison `lt : Cmp σ α` maps the two operands to Python code over the world. It is the
  same function in both twins: C's `PyObject_RichCompareBool` and Python's `<` plus truth test
  run the same `do_richcompare` and `PyObject_IsTrue`, and for `Py_LT` there is no identity
  shortcut. The C code holds a strong reference to both operands across the call
  (`Py_INCREF`/`Py_DECREF`, e.g. `_heapqmodule.c:46-50`), so the callback cannot free them;
  the `Py_DECREF`s after the call, which may run `__del__`, happen before the size re-check, so
  their effects are part of the comparison's world change. (`__del__` itself is out of scope:
  there is no finalization model.)
* C runs in `CM σ α`, whose errors are a Python exception or `crash`: reading or writing
  `arr[i]` (`_PyList_ITEMS`, `PyList_GET_ITEM`) at an index outside the list's current size.
  Every C read goes to the current contents: the C code re-reads `arr = _PyList_ITEMS(heap)`
  after every comparison before using it (`:60`, `:102`, `:442`, `:484`), so it never reads
  through a stale items pointer.
* Python runs over an arbitrary sequence object `S : Seq W α`: `Lib/heapq.py` is duck-typed and
  calls `len(heap)`, `heap[i]`, `heap[i] = v`, `heap.append`, `heap.pop()` and `bool(heap)`,
  each of which is Python code (for a list subclass they dispatch to overrides). `listSeq` is
  an exact `list` (or a subclass overriding none of them). C instead checks `PyList_Check`
  (a list or any subclass) in the Argument Clinic wrapper and then uses the raw list storage,
  ignoring overrides.
* The `*_max` variants take `mx = true`: each definition has both branches, with their own
  source lines, because the operand order of the comparison (and in Python the order of the
  two `heap[...]` reads) differs.

Not modelled: `Py_BEGIN_CRITICAL_SECTION` in the clinic wrappers (free-threaded builds only, not
observable single-threaded), `MemoryError` from `_PyList_AppendTakeRef` / `PyList_SetSlice`,
and the arity checks of `_PyArg_CheckPositional` (the models start from a call with the right
number of arguments). The unreachable `item == NULL` check of `heappush` (`:135-138`,
`:517-520`: clinic never passes NULL) is omitted.

Loops use fuel; fuel exhaustion raises `PyExc.modelFuel`, which the theorems show never
happens for the fuel the callers pass.
-/

namespace PyLean.Accel.Heapq

open PyLean

/-! ### Python code over a world -/

/-- Python code run against a world `W`: a value or an exception, and in both cases the world
it leaves. -/
structure Eff (W ε β : Type) where
  run : W → Except ε β × W

namespace Eff

variable {W ε β γ : Type}

@[inline] def pure' (b : β) : Eff W ε β := ⟨fun w => (.ok b, w)⟩

@[inline] def bind' (x : Eff W ε β) (f : β → Eff W ε γ) : Eff W ε γ :=
  ⟨fun w => match x.run w with
    | (.ok b, w') => (f b).run w'
    | (.error e, w') => (.error e, w')⟩

instance : Monad (Eff W ε) where
  pure := pure'
  bind := bind'

def raise (e : ε) : Eff W ε β := ⟨fun w => (.error e, w)⟩

@[simp] theorem run_pure (b : β) (w : W) : (pure b : Eff W ε β).run w = (.ok b, w) := rfl

@[simp] theorem run_bind (x : Eff W ε β) (f : β → Eff W ε γ) (w : W) :
    (x >>= f).run w = match x.run w with
      | (.ok b, w') => (f b).run w'
      | (.error e, w') => (.error e, w') := rfl

@[simp] theorem run_raise (e : ε) (w : W) : (raise e : Eff W ε β).run w = (.error e, w) := rfl

end Eff

/-- The world: the heap list's contents and everything else Python code can see. -/
structure HW (σ α : Type) where
  st : σ
  heap : List α

/-- One comparison `a < b` with its truth test, as Python code over the world. -/
abbrev Cmp (σ α : Type) := α → α → Eff (HW σ α) PyExc Bool

/-- A comparison that neither reads nor writes the heap list: its outcome and its effect on
the rest of the world depend only on the operands and `st`. -/
def ofSt {σ α : Type} (f : α → α → σ → Except PyExc Bool × σ) : Cmp σ α :=
  fun a b => ⟨fun w => ((f a b w.st).1, { w with st := (f a b w.st).2 })⟩

/-- An honest comparison: the pure Boolean `r a b`, no effect. -/
def pureCmp {σ α : Type} (r : α → α → Bool) : Cmp σ α := ofSt fun a b s => (.ok (r a b), s)

variable {σ α : Type} [Inhabited α]

/-! ### C accelerator -/

/-- What can go wrong in C: a Python exception, or a memory-unsafe access. -/
inductive CErr where
  | py (e : PyExc)
  /-- `arr[i]` read or written with `i` outside the list's current size. -/
  | crash (what : String)
  deriving DecidableEq, Repr

abbrev CM (σ α β : Type) := Eff (HW σ α) CErr β

def cRaise {β : Type} (e : PyExc) : CM σ α β := Eff.raise (.py e)

/-- `PyList_GET_SIZE(heap)`. -/
def cSize : CM σ α Nat := ⟨fun w => (.ok w.heap.length, w)⟩

/-- `arr[i]` / `PyList_GET_ITEM(heap, i)`: no bounds check. -/
def cItem (i : Nat) : CM σ α α :=
  ⟨fun w => if i < w.heap.length then (.ok (at! w.heap i), w) else (.error (.crash "read"), w)⟩

/-- `arr[i] = v` (`FT_ATOMIC_STORE_PTR_RELAXED`, a plain store in the default build): no
bounds check. -/
def cStore (i : Nat) (v : α) : CM σ α Unit :=
  ⟨fun w => if i < w.heap.length then (.ok (), { w with heap := w.heap.set i v })
    else (.error (.crash "write"), w)⟩

/-- `_PyList_AppendTakeRef(heap, item)`. -/
def cAppend (v : α) : CM σ α Unit := ⟨fun w => (.ok (), { w with heap := w.heap ++ [v] })⟩

/-- `PyList_SetSlice(heap, lo, hi, NULL)` for `lo ≤ hi = size`: delete `heap[lo:]`. -/
def cDelTail (lo : Nat) : CM σ α Unit := ⟨fun w => (.ok (), { w with heap := w.heap.take lo })⟩

/-- `PyObject_RichCompareBool(a, b, Py_LT)`: the comparison, with a raised exception
returned as `-1`. -/
def cLt (lt : Cmp σ α) (a b : α) : CM σ α Bool :=
  ⟨fun w => match (lt a b).run w with
    | (.ok c, w') => (.ok c, w')
    | (.error e, w') => (.error (.py e), w')⟩

def sizeChanged : PyExc := .named "RuntimeError" "list changed size during iteration"

def idxErr : PyExc := .indexError "index out of range"

/-- `x < y` (`mx = false`) or `y < x` (`mx = true`): `siftdown` compares `newitem < parent`
(Modules/_heapqmodule.c:46-50), `siftdown_max` `parent < newitem` (:428-432); `heappushpop`
compares `top < item` (:276-278), `heappushpop_max` `item < top` (:613-615). -/
def cLtOrd (mx : Bool) (lt : Cmp σ α) (x y : α) : CM σ α Bool :=
  if mx then cLt lt y x else cLt lt x y

/-- The choice of the smaller (larger, for `siftup_max`) child in `siftup`,
Modules/_heapqmodule.c:91-108 (`siftup_max` :473-490): with a right child, compare
`arr[childpos] < arr[childpos + 1]` (:92-98; `siftup_max` `arr[childpos + 1] < arr[childpos]`,
:474-480), add `cmp ^ 1` (:101 / :483), re-read the items and re-check the size (:102-107 /
:484-489). -/
def cChild (mx : Bool) (lt : Cmp σ α) (endpos childpos : Nat) : CM σ α Nat :=
  if childpos + 1 < endpos then do
    let a ← cItem (if mx then childpos + 1 else childpos)
    let b ← cItem (if mx then childpos else childpos + 1)
    let cmp ← cLt lt a b
    -- :99-100 / :481-482: `cmp < 0` returns -1 (the bind above)
    let childpos := childpos + (if cmp then 0 else 1)
    let size' ← cSize
    if endpos ≠ size' then cRaise sizeChanged
    else pure childpos
  else pure childpos

/-- The `while (pos > startpos)` loop of `siftdown`, Modules/_heapqmodule.c:43-66, and of
`siftdown_max`, :426-448. `newitem` is `arr[pos]` (read at :42, re-read at :62 / :444). -/
def cSiftdownLoop (mx : Bool) (lt : Cmp σ α) (startpos size : Nat) :
    Nat → α → Nat → CM σ α Unit
  | 0, _, _ => cRaise .modelFuel
  | fuel + 1, newitem, pos =>
    if pos > startpos then do
      let parentpos := (pos - 1) >>> 1                          -- :44 / :427
      let parent ← cItem parentpos                              -- :45 / :428
      let cmp ← cLtOrd mx lt newitem parent                     -- :46-50 / :429-432
      -- :51-52 / :433-434: `cmp < 0` returns -1 (the bind above)
      let size' ← cSize
      if size ≠ size' then cRaise sizeChanged                    -- :53-57 / :435-439
      else if !cmp then pure ()                                  -- :58-59 / :440-441
      else do
        let parent ← cItem parentpos                            -- :60-61 / :442-443
        let newitem ← cItem pos                                 -- :62 / :444
        cStore parentpos newitem                                -- :63 / :445
        cStore pos parent                                       -- :64 / :446
        cSiftdownLoop mx lt startpos size fuel newitem parentpos -- :65 / :447
    else pure ()

/-- `siftdown(heap, startpos, pos)`, Modules/_heapqmodule.c:25-68 (`mx = false`), and
`siftdown_max`, :408-450 (`mx = true`). -/
def cSiftdown (mx : Bool) (lt : Cmp σ α) (startpos pos : Nat) : CM σ α Unit := do
  let size ← cSize                                              -- :33 / :416
  if pos ≥ size then cRaise idxErr                               -- :34-37 / :417-420
  else do
    let newitem ← cItem pos                                     -- :41-42 / :424-425
    cSiftdownLoop mx lt startpos size (pos + 1) newitem pos

/-- The `while (pos < limit)` loop of `siftup`, Modules/_heapqmodule.c:88-115, and of
`siftup_max`, :470-497. Returns the final `pos`. -/
def cSiftupLoop (mx : Bool) (lt : Cmp σ α) (endpos limit : Nat) : Nat → Nat → CM σ α Nat
  | 0, _ => cRaise .modelFuel
  | fuel + 1, pos =>
    if pos < limit then do
      let childpos ← cChild mx lt endpos (2 * pos + 1)          -- :90-108 / :472-490
      let tmp1 ← cItem childpos                                 -- :110 / :492
      let tmp2 ← cItem pos                                      -- :111 / :493
      cStore childpos tmp2                                      -- :112 / :494
      cStore pos tmp1                                           -- :113 / :495
      cSiftupLoop mx lt endpos limit fuel childpos              -- :114 / :496
    else pure pos

/-- `siftup(heap, pos)`, Modules/_heapqmodule.c:70-118 (`mx = false`), and `siftup_max`,
:452-500 (`mx = true`). -/
def cSiftup (mx : Bool) (lt : Cmp σ α) (pos : Nat) : CM σ α Unit := do
  let endpos ← cSize                                            -- :78 / :460
  let startpos := pos                                           -- :79 / :461
  if pos ≥ endpos then cRaise idxErr                             -- :80-83 / :462-465
  else do
    let limit := endpos >>> 1                                   -- :87 / :469
    let pos ← cSiftupLoop mx lt endpos limit (endpos + 1) pos
    cSiftdown mx lt startpos pos                                -- :117 / :499

/-- The argument the C function receives: whether it passes `PyList_Check` (an exact list or a
subclass; its contents are the world's `heap`), and otherwise the name `_PyArg_BadArgument`
prints (`tp_name`, or `None` for None). -/
structure CArg where
  isList : Bool
  tpName : String

/-- `_PyArg_BadArgument(fname, displayname, "list", arg)`, Python/getargs.c:663-670:
`"%.200s() %.200s must be %.50s, not %.50s"` (the `%.50s` cut is by bytes; the model cuts
characters, which is the same for ASCII names). -/
def badArg (fname which tp : String) : PyExc :=
  .typeError s!"{fname}() {which} must be list, not {tp.take 50}"

def fnName (base : String) (mx : Bool) : String := if mx then base ++ "_max" else base

/-- The clinic wrapper's `PyList_Check`, Modules/clinic/_heapqmodule.c.h:30-33 (`heappush`),
:62-65 (`heappop`), :105-108, :144-147, :176-179, :211-214, :243-246, :278-281, :310-313,
:348-351. `which` is `"argument 1"` for the two-argument functions, `"argument"` for the
one-argument ones. -/
def cChecked {β : Type} (base which : String) (mx : Bool) (arg : CArg) (body : CM σ α β) :
    CM σ α β :=
  if arg.isList then body else cRaise (badArg (fnName base mx) which arg.tpName)

/-- `_heapq.heappush`, Modules/_heapqmodule.c:131-150; `heappush_max` :513-533. -/
def cHeappush (mx : Bool) (lt : Cmp σ α) (arg : CArg) (item : α) : CM σ α Unit :=
  cChecked "heappush" "argument 1" mx arg do
    cAppend item                                                -- :142-144 / :524-526
    let n ← cSize
    cSiftdown mx lt 0 (n - 1)                                   -- :146-148 / :528-530

/-- `heappop_internal`, Modules/_heapqmodule.c:152-183, called by `heappop` :195-200
(`siftup`) and `heappop_max` :545-550 (`siftup_max`). -/
def cHeappopInternal (mx : Bool) (lt : Cmp σ α) : CM σ α α := do
  let n ← cSize                                                 -- :159
  if n = 0 then cRaise idxErr                                    -- :160-163
  else do
    let lastelt ← cItem (n - 1)                                 -- :165-166
    cDelTail (n - 1)                                            -- :167-170
    let n := n - 1                                              -- :171
    if n = 0 then pure lastelt                                  -- :173-174
    else do
      let returnitem ← cItem 0                                  -- :175
      cStore 0 lastelt                                          -- :176-177
      cSiftup mx lt 0                                           -- :178-181
      pure returnitem                                           -- :182

def cHeappop (mx : Bool) (lt : Cmp σ α) (arg : CArg) : CM σ α α :=
  cChecked "heappop" "argument" mx arg (cHeappopInternal mx lt)

/-- `heapreplace_internal`, Modules/_heapqmodule.c:202-220, called by `heapreplace`
:242-247 and `heapreplace_max` :563-568. -/
def cHeapreplaceInternal (mx : Bool) (lt : Cmp σ α) (item : α) : CM σ α α := do
  let n ← cSize
  if n = 0 then cRaise idxErr                                    -- :207-210
  else do
    let returnitem ← cItem 0                                    -- :212
    cStore 0 item                                               -- :213-214
    cSiftup mx lt 0                                             -- :215-218
    pure returnitem                                             -- :219

def cHeapreplace (mx : Bool) (lt : Cmp σ α) (arg : CArg) (item : α) : CM σ α α :=
  cChecked "heapreplace" "argument 1" mx arg (cHeapreplaceInternal mx lt item)

/-- `_heapq.heappushpop`, Modules/_heapqmodule.c:264-298 (`top < item`), and
`heappushpop_max`, :601-636 (`item < top`). -/
def cHeappushpopImpl (mx : Bool) (lt : Cmp σ α) (item : α) : CM σ α α := do
  let n ← cSize
  if n = 0 then pure item                                       -- :271-273 / :608-610
  else do
    let top ← cItem 0                                           -- :275-276 / :612-613
    let cmp ← cLtOrd mx lt top item                             -- :277-278 / :614-615
    -- :279-280 / :616-618: `cmp < 0` returns NULL (the bind above)
    if !cmp then pure item                                      -- :281-283 / :619-621
    else do
      let n ← cSize
      if n = 0 then cRaise idxErr                                -- :285-288 / :623-626
      else do
        let returnitem ← cItem 0                                -- :290 / :628
        cStore 0 item                                           -- :291-292 / :629-630
        cSiftup mx lt 0                                         -- :293-296 / :631-634
        pure returnitem                                         -- :297 / :635

def cHeappushpop (mx : Bool) (lt : Cmp σ α) (arg : CArg) (item : α) : CM σ α α :=
  cChecked "heappushpop" "argument 1" mx arg (cHeappushpopImpl mx lt item)

/-- Run `body i` for `i` in order, stopping at the first error. -/
def effFor {W ε : Type} (body : Nat → Eff W ε Unit) : List Nat → Eff W ε Unit
  | [] => pure ()
  | i :: is => do body i; effFor body is

/-- The inner `while (1)` of `cache_friendly_heapify`, Modules/_heapqmodule.c:342-349 and
:353-360: sift `j`, stop at an even `j`, else go on with `j >>= 1`. -/
def cClimb (mx : Bool) (lt : Cmp σ α) : Nat → Nat → CM σ α Unit
  | 0, _ => cRaise .modelFuel
  | fuel + 1, j => do
    cSiftup mx lt j                                             -- :344-345 / :355-356
    if j % 2 = 0 then pure ()                                   -- :346-347 / :357-358
    else cClimb mx lt fuel (j >>> 1)                            -- :348 / :359

/-- `cache_friendly_heapify`, Modules/_heapqmodule.c:332-363. -/
def cCacheFriendly (mx : Bool) (lt : Cmp σ α) : CM σ α Unit := do
  let size ← cSize
  let m := size >>> 1                                           -- :337
  let leftmost := keepTopBit (m + 1) - 1                        -- :338 (keep_top_bit :300-310)
  let mhalf := m >>> 1                                          -- :339
  effFor (fun i => cClimb mx lt (i + 1) i) (downFrom mhalf leftmost)   -- :341-350
  effFor (fun i => cClimb mx lt (i + 1) i) (downFrom leftmost m)       -- :352-361

/-- `heapify_internal`, Modules/_heapqmodule.c:365-389, called by `heapify` :401-406 and
`heapify_max` :580-585. -/
def cHeapifyInternal (mx : Bool) (lt : Cmp σ α) : CM σ α Unit := do
  let n ← cSize                                                 -- :374
  if n > 2500 then cCacheFriendly mx lt                         -- :375-376
  else effFor (fun i => cSiftup mx lt i) (downFrom 0 (n >>> 1)) -- :385-388

def cHeapify (mx : Bool) (lt : Cmp σ α) (arg : CArg) : CM σ α Unit :=
  cChecked "heapify" "argument" mx arg (cHeapifyInternal mx lt)

/-! ### Pure-Python twin, over any sequence object -/

/-- The operations `Lib/heapq.py` performs on its `heap` argument, each Python code over the
world `W`. Python indices are ints (`Int`); `len()` is a non-negative int. -/
structure Seq (W α : Type) where
  /-- `len(heap)` -/
  len : Eff W PyExc Nat
  /-- `heap[i]` -/
  get : Int → Eff W PyExc α
  /-- `heap[i] = v` -/
  set : Int → α → Eff W PyExc Unit
  /-- `heap.append(v)` -/
  append : α → Eff W PyExc Unit
  /-- `heap.pop()` -/
  pop : Eff W PyExc α
  /-- `bool(heap)`, as in `if heap:` -/
  truth : Eff W PyExc Bool

variable {W : Type}

/-- `x < y` (`mx = false`) or `y < x` (`mx = true`), with its truth test: `_siftdown`'s
`newitem < parent` (Lib/heapq.py:228) and `_siftdown_max`'s `parent < newitem` (:302);
`heappushpop`'s `heap[0] < item` (:166) and `heappushpop_max`'s `item < heap[0]` (:206). -/
def pyLtOrd (lt : α → α → Eff W PyExc Bool) (mx : Bool) (x y : α) : Eff W PyExc Bool :=
  if mx then lt y x else lt x y

/-- `heap[childpos] < heap[rightpos]` (Lib/heapq.py:283) or, in `_siftup_max`,
`heap[rightpos] < heap[childpos]` (:319): the two reads in that order, then the comparison. -/
def pyChildLt (S : Seq W α) (lt : α → α → Eff W PyExc Bool) (mx : Bool) (childpos rightpos : Int) :
    Eff W PyExc Bool :=
  if mx then do
    let x ← S.get rightpos
    let y ← S.get childpos
    lt x y
  else do
    let x ← S.get childpos
    let y ← S.get rightpos
    lt x y

/-- `rightpos < endpos and not heap[childpos] < heap[rightpos]` (Lib/heapq.py:283; `_siftup_max`
:319), short-circuiting. -/
def pyTakeRight (S : Seq W α) (lt : α → α → Eff W PyExc Bool) (mx : Bool) (endpos : Nat)
    (childpos rightpos : Int) : Eff W PyExc Bool :=
  if rightpos < endpos then do
    let r ← pyChildLt S lt mx childpos rightpos
    pure (!r)
  else pure false

/-- The `while pos > startpos` loop of `_siftdown`, Lib/heapq.py:225-232, and of
`_siftdown_max`, :299-306. Returns the final `pos`. -/
def pySiftdownLoop (S : Seq W α) (lt : α → α → Eff W PyExc Bool) (mx : Bool) (startpos : Int)
    (newitem : α) : Nat → Int → Eff W PyExc Int
  | 0, _ => Eff.raise .modelFuel
  | fuel + 1, pos =>
    if pos > startpos then do
      let parentpos := (pos - 1) / 2                            -- :226 / :300 (`>> 1`)
      let parent ← S.get parentpos                              -- :227 / :301
      let c ← pyLtOrd lt mx newitem parent                      -- :228 / :302
      if c then do
        S.set pos parent                                        -- :229 / :303
        pySiftdownLoop S lt mx startpos newitem fuel parentpos  -- :230-231 / :304-305
      else pure pos                                             -- :232 / :306
    else pure pos

/-- `_siftdown(heap, startpos, pos)`, Lib/heapq.py:221-233 (`mx = false`), and
`_siftdown_max`, :294-307 (`mx = true`). -/
def pySiftdown (S : Seq W α) (lt : α → α → Eff W PyExc Bool) (mx : Bool) (startpos pos : Int) :
    Eff W PyExc Unit := do
  let newitem ← S.get pos                                       -- :222 / :296
  let pos ← pySiftdownLoop S lt mx startpos newitem (pos.toNat + 1) pos
  S.set pos newitem                                             -- :233 / :307

/-- The `while childpos < endpos` loop of `_siftup`, Lib/heapq.py:279-288, and of
`_siftup_max`, :315-324. Returns the final `pos`. -/
def pySiftupLoop (S : Seq W α) (lt : α → α → Eff W PyExc Bool) (mx : Bool) (endpos : Nat) :
    Nat → Int → Eff W PyExc Int
  | 0, _ => Eff.raise .modelFuel
  | fuel + 1, pos =>
    let childpos := 2 * pos + 1                                 -- :279, :288 / :315, :324
    if childpos < endpos then do                                -- :280 / :316
      let rightpos := childpos + 1                              -- :282 / :318
      let c ← pyTakeRight S lt mx endpos childpos rightpos      -- :283 / :319
      let childpos := if c then rightpos else childpos          -- :284 / :320
      let v ← S.get childpos                                    -- :286 / :322
      S.set pos v
      pySiftupLoop S lt mx endpos fuel childpos                 -- :287 / :323
    else pure pos

/-- `_siftup(heap, pos)`, Lib/heapq.py:274-292 (`mx = false`), and `_siftup_max`,
:309-328 (`mx = true`). -/
def pySiftup (S : Seq W α) (lt : α → α → Eff W PyExc Bool) (mx : Bool) (pos : Int) :
    Eff W PyExc Unit := do
  let endpos ← S.len                                            -- :275 / :311
  let startpos := pos                                           -- :276 / :312
  let newitem ← S.get pos                                       -- :277 / :313
  let pos ← pySiftupLoop S lt mx endpos (endpos + 1) pos
  S.set pos newitem                                             -- :291 / :327
  pySiftdown S lt mx startpos pos                               -- :292 / :328

/-- `heappush(heap, item)`, Lib/heapq.py:133-136; `heappush_max` :199-202. -/
def pyHeappush (S : Seq W α) (lt : α → α → Eff W PyExc Bool) (mx : Bool) (item : α) :
    Eff W PyExc Unit := do
  S.append item                                                 -- :135 / :201
  let n ← S.len
  pySiftdown S lt mx 0 ((n : Int) - 1)                          -- :136 / :202

/-- `heappop(heap)`, Lib/heapq.py:138-146; `heappop_max` :182-190. -/
def pyHeappop (S : Seq W α) (lt : α → α → Eff W PyExc Bool) (mx : Bool) : Eff W PyExc α := do
  let lastelt ← S.pop                                           -- :140 / :184
  let b ← S.truth                                               -- :141 / :185
  if b then do
    let returnitem ← S.get 0                                    -- :142 / :186
    S.set 0 lastelt                                             -- :143 / :187
    pySiftup S lt mx 0                                          -- :144 / :188
    pure returnitem                                             -- :145 / :189
  else pure lastelt                                             -- :146 / :190

/-- `heapreplace(heap, item)`, Lib/heapq.py:148-162; `heapreplace_max` :192-197. -/
def pyHeapreplace (S : Seq W α) (lt : α → α → Eff W PyExc Bool) (mx : Bool) (item : α) :
    Eff W PyExc α := do
  let returnitem ← S.get 0                                      -- :159 / :194
  S.set 0 item                                                  -- :160 / :195
  pySiftup S lt mx 0                                            -- :161 / :196
  pure returnitem                                               -- :162 / :197

/-- `heap and heap[0] < item` (Lib/heapq.py:166) / `heap and item < heap[0]` (:206):
`bool(heap)`, then, if true, `heap[0]` and the comparison. -/
def pyTopLt (S : Seq W α) (lt : α → α → Eff W PyExc Bool) (mx : Bool) (item : α) :
    Eff W PyExc Bool := do
  let b ← S.truth
  if b then do
    let h0 ← S.get 0
    pyLtOrd lt mx h0 item
  else pure false

/-- `heappushpop(heap, item)`, Lib/heapq.py:164-169 (`heap[0] < item`); `heappushpop_max`
:204-209 (`item < heap[0]`). `item, heap[0] = heap[0], item` reads `heap[0]` again, then
stores. -/
def pyHeappushpop (S : Seq W α) (lt : α → α → Eff W PyExc Bool) (mx : Bool) (item : α) :
    Eff W PyExc α := do
  let c ← pyTopLt S lt mx item                                  -- :166 / :206
  if c then do
    let v ← S.get 0                                             -- :167 / :207
    S.set 0 item
    pySiftup S lt mx 0                                          -- :168 / :208
    pure v                                                      -- :169 / :209
  else pure item

/-- `heapify(x)`, Lib/heapq.py:171-180; `heapify_max` :211-215:
`n = len(x); for i in reversed(range(n//2)): _siftup(x, i)`. -/
def pyHeapify (S : Seq W α) (lt : α → α → Eff W PyExc Bool) (mx : Bool) : Eff W PyExc Unit := do
  let n ← S.len                                                 -- :173 / :213
  effFor (fun i => pySiftup S lt mx (i : Int)) (List.range (n / 2)).reverse  -- :179-180 / :214-215

/-! ### Lists -/

/-- Python's index normalisation for a list of length `n`: a negative index counts from the
end; `none` is out of range. -/
def listIndex (i : Int) (n : Nat) : Option Nat :=
  let j := if i < 0 then i + n else i
  if 0 ≤ j ∧ j < n then some j.toNat else none

/-- An exact `list` (or a subclass overriding none of `__len__`, `__getitem__`, `__setitem__`,
`append`, `pop`): `list_length`, `list_subscript`, `list_ass_subscript`, `list.append`,
`list.pop()` (Objects/listobject.c) and truth by length. -/
def listSeq : Seq (HW σ α) α where
  len := ⟨fun w => (.ok w.heap.length, w)⟩
  get i := ⟨fun w => match listIndex i w.heap.length with
    | some j => (.ok (at! w.heap j), w)
    | none => (.error (.indexError "list index out of range"), w)⟩
  set i v := ⟨fun w => match listIndex i w.heap.length with
    | some j => (.ok (), { w with heap := w.heap.set j v })
    | none => (.error (.indexError "list assignment index out of range"), w)⟩
  append v := ⟨fun w => (.ok (), { w with heap := w.heap ++ [v] })⟩
  pop := ⟨fun w => match w.heap.getLast? with
    | some x => (.ok x, { w with heap := w.heap.dropLast })
    | none => (.error (.indexError "pop from empty list"), w)⟩
  truth := ⟨fun w => (.ok (!w.heap.isEmpty), w)⟩

end PyLean.Accel.Heapq
