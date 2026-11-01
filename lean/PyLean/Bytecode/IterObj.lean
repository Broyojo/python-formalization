import Lean.Data.Json
import PyLean.DiffCore
import PyLean.Registry

/-!
`Objects/iterobject.c`, `Objects/enumobject.c`, `Objects/cellobject.c`, CPython 3.14.7.

Generic over the element type `α` and over what the sequence does: `__getitem__`,
the callable and the comparison are plain function arguments that may raise, so
every statement covers all user-defined behaviour with no reentrancy. `Py (Option α)`
is a C return value: `ok (some v)` a result, `ok none` is `NULL` with no exception,
`error e` is `NULL` with an exception set.
-/

namespace PyLean.Bytecode.IterObj

open PyLean

/-- `PyErr_ExceptionMatches(PyExc_IndexError)`. -/
def isIndexError : PyExc → Bool
  | .indexError _ => true
  | _ => false

/-- `PyErr_ExceptionMatches(PyExc_StopIteration)`. -/
def isStopIteration : PyExc → Bool
  | .stopIteration => true
  | _ => false

def stopsSeq (e : PyExc) : Bool := isIndexError e || isStopIteration e

/-! ## `iter(sequence)`: lines 11-182 -/

/-- `seqiterobject`: `held` is `it_seq != NULL`. -/
structure SeqIter where
  held : Bool
  index : Int
  deriving DecidableEq, Repr

/-- `PySeqIter_New`, lines 17-33, after the `PySequence_Check`. -/
def seqIterNew : SeqIter := ⟨true, 0⟩

/-- `iter_iternext`, lines 52-83. -/
def iterIternext {α : Type} (getitem : Int → Py α) (it : SeqIter) : SeqIter × Py (Option α) :=
  if !it.held then (it, .ok none)
  else if it.index = ssizeMax then (it, .error (.overflowError "iter index too large"))
  else
    match getitem it.index with
    | .ok v => ({ it with index := it.index + 1 }, .ok (some v))
    | .error e =>
      if stopsSeq e then ({ it with held := false }, .ok none)
      else (it, .error e)

/-- `iter_len`, lines 85-105. `size` is `none` when `_PyObject_HasLen` is false,
`Py (some n)` is `PySequence_Size`. The result is `none` for `NotImplemented`. -/
def iterLen (size : Option (Py Int)) (it : SeqIter) : Py (Option Int) :=
  if it.held then
    match size with
    | some (.ok n) =>
      let len := n - it.index
      if 0 ≤ len then .ok (some len) else .ok (some 0)
    | some (.error e) => .error e
    | none => .ok none
  else .ok (some 0)

/-- `iter_reduce`, lines 109-123: the index for `iter(seq)`, or `none` for `iter(())`. -/
def iterReduce (it : SeqIter) : Option Int := if it.held then some it.index else none

/-- `iter_setstate`, lines 127-140, with `index` already narrowed by
`PyLong_AsSsize_t`. -/
def iterSetstate (it : SeqIter) (index : Int) : SeqIter :=
  if it.held then { it with index := if index < 0 then 0 else index } else it

/-- `getitem` of a Python list. -/
def listGet {α : Type} (l : List α) (i : Int) : Py α :=
  if 0 ≤ i then
    match l[i.toNat]? with
    | some v => .ok v
    | none => .error (.indexError "list index out of range")
  else .error (.indexError "list index out of range")

/-- Drain an iterator: `n` calls of `next`. -/
def drain {α : Type} (getitem : Int → Py α) : Nat → SeqIter → List α
  | 0, _ => []
  | n + 1, it =>
    match iterIternext getitem it with
    | (it', .ok (some v)) => v :: drain getitem n it'
    | _ => []

/-! ## `iter(callable, sentinel)`: lines 186-307 -/

/-- `calliterobject`: `live` is `it_callable != NULL`. -/
structure CallIter where
  live : Bool
  deriving DecidableEq, Repr

/-- `calliter_iternext`, lines 223-254. `eq r` is
`PyObject_RichCompareBool(sentinel, r, Py_EQ)`. -/
def calliterIternext {α : Type} (call : Py α) (eq : α → Py Bool) (it : CallIter) :
    CallIter × Py (Option α) :=
  if !it.live then (it, .ok none)
  else
    match call with
    | .ok r =>
      match eq r with
      | .ok false => (it, .ok (some r))
      | .ok true => (⟨false⟩, .ok none)
      | .error e => (it, .error e)
    | .error e =>
      if isStopIteration e then (⟨false⟩, .ok none) else (it, .error e)

/-- `calliter_reduce`, lines 256-270: does the pickle keep the pair? -/
def calliterReduce (it : CallIter) : Bool := it.live

/-! ## `anext(it, default)`: lines 312-436 -/

/-- One suspension of an awaitable's iterator. -/
inductive Step (α : Type) where
  | yield (v : α)
  | ret (v : α)
  | stopAsync
  | raise (e : PyExc)
  deriving Repr

/-- An object with `__await__`: `begin` is what the method does, a new iterator
state of type `σ`; `resume` runs that iterator one step. A coroutine has
`begin s = s`: its state lives in the object. -/
structure Awaitable (σ α : Type) where
  begin : σ → σ
  resume : σ → σ × Step α

/-- `anextawaitable_getiter` then `tp_iternext`, lines 339-367 and 369-407. `obj`
is the object's own state. The iterator made from it is discarded after the step,
except that an object that keeps its state in itself (a coroutine) keeps it. -/
def anextIternext {σ α : Type} (A : Awaitable σ α) (keep : Bool) (dflt : α) (obj : σ) :
    σ × Step α :=
  let it := A.begin obj
  let (it', r) := A.resume it
  let obj' := if keep then it' else obj
  match r with
  | .stopAsync => (obj', .ret dflt)
  | r => (obj', r)

/-- Drive `await x` through `anext(x, default)`: every value and the result. -/
def runAnext {σ α : Type} (A : Awaitable σ α) (keep : Bool) (dflt : α) : Nat → σ → List (Step α)
  | 0, _ => []
  | n + 1, s =>
    let (s', r) := anextIternext A keep dflt s
    match r with
    | .yield _ => r :: runAnext A keep dflt n s'
    | _ => [r]

/-- Drive plain `await x`: `__await__` once, then the iterator. -/
def runAwait {σ α : Type} (A : Awaitable σ α) (n : Nat) (s : σ) : List (Step α) :=
  let rec go : Nat → σ → List (Step α)
    | 0, _ => []
    | k + 1, it =>
      let (it', r) := A.resume it
      match r with
      | .yield _ => r :: go k it'
      | _ => [r]
  go n (A.begin s)

/-! ## `enumerate`: `Objects/enumobject.c` lines 30-357 -/

/-- `enumobject`: `en_index` and `en_longindex`. -/
structure Enum where
  index : Int
  longindex : Option Int
  deriving DecidableEq, Repr

/-- `enum_new_impl`, lines 47-88: `PyLong_AsSsize_t` overflow switches to
`en_longindex`. -/
def enumNew (start : Int) : Enum :=
  if ssizeMin ≤ start ∧ start ≤ ssizeMax then ⟨start, none⟩ else ⟨ssizeMax, some start⟩

/-- `increment_longindex_lock_held` and `enum_next_long`, lines 176-236. -/
def enumNextLong (en : Enum) : Enum × Int :=
  let nx := en.longindex.getD ssizeMax
  ({ en with longindex := some (nx + 1) }, nx)

/-- `enum_next`, lines 238-286, past the `tp_iternext` of the wrapped iterator:
the state and the index of the pair. -/
def enumNext (en : Enum) : Enum × Int :=
  if en.index = ssizeMax then enumNextLong en
  else ({ en with index := en.index + 1 }, en.index)

/-- `enum_reduce`, lines 288-303: the `start` of the pickled call. -/
def enumReduce (en : Enum) : Int :=
  match en.longindex with
  | some l => l
  | none => en.index

/-- `n` steps of `enum_next`: the indices produced. -/
def enumIndices : Nat → Enum → List Int
  | 0, _ => []
  | n + 1, en => (enumNext en).2 :: enumIndices n (enumNext en).1

/-- What a Python-level counter gives: `start, start+1, ...`. -/
def counter : Nat → Int → List Int
  | 0, _ => []
  | n + 1, s => s :: counter n (s + 1)

/-- `check_keyword`, `enumerate_vectorcall`, lines 90-153: `(iterable position, start
position)` into the arguments, or the `TypeError`. Arguments are `pos` positional
then `kw` names. -/
def enumArgs (npos : Nat) (kw : List String) : Except String (Nat × Option Nat) :=
  let total := npos + kw.length
  let bad (k : String) : Except String (Nat × Option Nat) :=
    .error s!"'{k}' is an invalid keyword argument for enumerate()"
  if total == 2 then
    match kw with
    | [] => .ok (0, some 1)
    | [k] => if k == "start" then .ok (0, some 1) else bad k
    | [k0, k1] =>
      if k0 == "start" then
        if k1 == "iterable" then .ok (1, some 0) else bad k1
      else if k0 == "iterable" then
        if k1 == "start" then .ok (0, some 1) else bad k1
      else bad k0
    | _ => .ok (0, some 1)
  else if total == 1 then
    match kw with
    | [k] => if k == "iterable" then .ok (0, none) else bad k
    | _ => .ok (0, none)
  else if npos == 0 then .error "enumerate() missing required argument 'iterable'"
  else .error s!"enumerate() takes at most 2 arguments ({total} given)"

/-! ## `reversed`: lines 361-543 -/

/-- `reversedobject`: `held` is `seq != NULL`. -/
structure Rev where
  index : Int
  held : Bool
  deriving DecidableEq, Repr

/-- `reversed_new_impl`, lines 379-421, for a sequence of length `n` with no
`__reversed__`. -/
def revNew (n : Int) : Rev := ⟨n - 1, true⟩

/-- `reversed_next`, lines 456-478. -/
def revNext {α : Type} (getitem : Int → Py α) (ro : Rev) : Rev × Py (Option α) :=
  if 0 ≤ ro.index then
    match getitem ro.index with
    | .ok v => ({ ro with index := ro.index - 1 }, .ok (some v))
    | .error e =>
      if stopsSeq e then (⟨-1, false⟩, .ok none) else (⟨-1, false⟩, .error e)
  else (⟨-1, false⟩, .ok none)

/-- `reversed_len`, lines 480-495. -/
def revLen (size : Py Int) (ro : Rev) : Py Int :=
  if ro.index = -1 then .ok 0
  else
    match size with
    | .error e => .error e
    | .ok n =>
      let position := ro.index + 1
      .ok (if n < position then 0 else position)

/-- `reversed_reduce`, lines 499-510: the index, or `none` for `reversed(())`. -/
def revReduce (ro : Rev) : Option Int := if ro.index != -1 then some ro.index else none

/-- `reversed_setstate`, lines 512-534. -/
def revSetstate (size : Py Int) (ro : Rev) (index : Int) : Py Rev :=
  if ro.index != -1 then
    match size with
    | .error e => .error e
    | .ok n =>
      let i := if index < -1 then -1 else if index > n - 1 then n - 1 else index
      .ok { ro with index := i }
  else .ok ro

def revDrain {α : Type} (getitem : Int → Py α) : Nat → Rev → List α
  | 0, _ => []
  | n + 1, ro =>
    match revNext getitem ro with
    | (ro', .ok (some v)) => v :: revDrain getitem n ro'
    | _ => []

/-! ## `cell`: `Objects/cellobject.c` -/

/-- `PyCellObject`: `none` is an empty cell. -/
abbrev Cell (α : Type) := Option α

/-- `cell_compare_impl`, lines 85-94: `Py_RETURN_RICHCOMPARE(b == NULL, a == NULL, op)`
when one side is empty. `op` is `Py_LT`...`Py_GE`; `cmp` is `PyObject_RichCompare`. -/
def cellCompare {α β : Type} (cmp : α → α → Nat → Py β) (ofBool : Bool → β) (a b : Cell α)
    (op : Nat) : Py β :=
  match a, b with
  | some x, some y => cmp x y op
  | _, _ =>
    let l := b.isNone
    let r := a.isNone
    .ok (ofBool (match op with
      | 0 => !l && r
      | 1 => !l || r
      | 2 => l == r
      | 3 => l != r
      | 4 => l && !r
      | _ => l || !r))

/-- `cell_get_contents`, lines 146-156. -/
def cellGet {α : Type} (c : Cell α) : Py α :=
  match c with
  | some v => .ok v
  | none => .error (.valueError "Cell is empty")

/-- `cell_set_contents`, lines 158-165; `del cell.cell_contents` is `obj = NULL`. -/
def cellSet {α : Type} (_ : Cell α) (obj : Option α) : Cell α := obj

/-- `cell_new`, lines 36-53: `none` for the `TypeError` paths, handled by the
argument parser. -/
def cellNew {α : Type} (args : List α) (nkw : Nat) : Except String (Cell α) :=
  if nkw != 0 then .error "cell() takes no keyword arguments"
  else
    match args with
    | [] => .ok none
    | [x] => .ok (some x)
    | _ => .error s!"cell expected at most 1 argument, got {args.length}"

/-- `cell_repr`, lines 117-128, without the addresses. -/
def cellReprKind {α : Type} (c : Cell α) (tpName : α → String) : String :=
  match c with
  | none => "empty"
  | some v => String.ofList ((tpName v).toList.take 80)

/-! ## Properties -/

/-- An exhausted iterator never calls `__getitem__` again. -/
def IterExhaustedSticky : Prop :=
  ∀ (α : Type) (getitem : Int → Py α) (it : SeqIter), it.held = false →
    iterIternext getitem it = (it, .ok none)

theorem iterExhaustedSticky_proven : IterExhaustedSticky := by
  intro α g it h
  simp [iterIternext, h]

/-- A success advances the index by one; an error other than `IndexError` and
`StopIteration` leaves the iterator as it was, so it can be retried. -/
def IterStep : Prop :=
  ∀ (α : Type) (getitem : Int → Py α) (it : SeqIter), it.held = true → it.index ≠ ssizeMax →
    match iterIternext getitem it with
    | (it', .ok (some _)) => it'.index = it.index + 1 ∧ it'.held = true
    | (it', .ok none) => it'.held = false
    | (it', .error _) => it' = it

theorem iterStep_proven : IterStep := by
  intro α g it h hm
  simp only [iterIternext, h, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hm]
  cases hg : g it.index with
  | ok v => simp
  | error e =>
    by_cases hs : stopsSeq e
    · simp [hs]
    · simp [hs]

/-- `__setstate__` never leaves a negative index and never revives an exhausted
iterator. -/
def IterSetstate : Prop :=
  ∀ (it : SeqIter) (i : Int), 0 ≤ it.index → 0 ≤ (iterSetstate it i).index ∧
    (iterSetstate it i).held = it.held

/-- A sentinel match ends a callable iterator for good, and so does `StopIteration`;
any other exception keeps it alive. -/
def CalliterEnds : Prop :=
  ∀ (α : Type) (call : Py α) (eq : α → Py Bool),
    (∀ c e, calliterIternext (.error e : Py α) eq c = if c.live then
      (if isStopIteration e then (⟨false⟩, .ok none) else (c, .error e)) else (c, .ok none)) ∧
    (∀ r, eq r = .ok true → (calliterIternext (.ok r) eq ⟨true⟩).1 = ⟨false⟩) ∧
    (calliterIternext call eq ⟨false⟩ = (⟨false⟩, .ok none))

theorem calliterEnds_proven : CalliterEnds := by
  intro α call eq
  refine ⟨?_, ?_, ?_⟩
  · intro c e
    simp only [calliterIternext]
    cases c.live <;> simp
  · intro r h
    simp [calliterIternext, h]
  · simp [calliterIternext]

/-- `await anext(x, default)` is `await x` when `x` does not raise `StopAsyncIteration`:
what the C comment at lines 426-431 and `Doc/library/functions.rst` promise.
False for an awaitable whose `__await__` makes a new iterator. -/
def AnextAwaitsOnce : Prop :=
  ∀ (σ α : Type) (A : Awaitable σ α) (dflt : α) (s : σ) (n : Nat),
    (runAnext A false dflt n s).length = (runAwait A n s).length

/-- An awaitable that yields twice, with its state in a fresh iterator. -/
def twice : Awaitable Nat Nat where
  begin := fun _ => 0
  resume := fun
    | 0 => (1, .yield 1)
    | 1 => (2, .yield 2)
    | _ => (3, .ret 3)

theorem anextAwaitsOnce_refuted : ¬AnextAwaitsOnce := by
  intro h
  have := h Nat Nat twice 0 0 4
  simp [runAnext, anextIternext, twice, runAwait, runAwait.go] at this

/-- For a coroutine, whose state lives in the object, `anext(x, default)` is `await x`. -/
def AnextCoroutine : Prop :=
  ∀ (σ α : Type) (resume : σ → σ × Step α) (dflt : α) (n : Nat) (s : σ),
    (∀ t, ¬∃ t', resume t = (t', .stopAsync)) →
    runAnext ⟨id, resume⟩ true dflt n s = runAwait ⟨id, resume⟩ n s

/-- The fast `Py_ssize_t` counter and the slow `PyLong` counter of `enumerate` are
one counter: for every start and every length the indices are
`start, start+1, ...`, across `PY_SSIZE_T_MAX`. -/
def EnumCounts : Prop :=
  ∀ (start : Int) (n : Nat), enumIndices n (enumNew start) = counter n start

theorem counter_succ (n : Nat) (start : Int) :
    counter (n + 1) start = start :: counter n (start + 1) := rfl

theorem enumIndices_long (n : Nat) (x : Int) :
    enumIndices n ⟨ssizeMax, some x⟩ = counter n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [counter_succ]
    simp only [enumIndices, enumNext, enumNextLong, ↓reduceIte, Option.getD_some, ih]

theorem enumIndices_fast (n : Nat) (i : Int) (h : i ≤ ssizeMax) :
    enumIndices n ⟨i, none⟩ = counter n i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    rw [counter_succ]
    by_cases hi : i = ssizeMax
    · subst hi
      simp only [enumIndices, enumNext, enumNextLong, ↓reduceIte, Option.getD_none]
      rw [enumIndices_long]
    · simp only [enumIndices, enumNext, hi, ↓reduceIte]
      rw [ih (i + 1) (by omega)]

theorem enumCounts_proven : EnumCounts := by
  intro start n
  unfold enumNew
  split
  · rename_i h; exact enumIndices_fast n start h.2
  · exact enumIndices_long n start

/-- Pickling `enumerate` keeps the count: rebuilding from `__reduce__` continues with
the same indices, in both the fast and the slow state. -/
def EnumReduce : Prop :=
  ∀ (start : Int) (k n : Nat),
    enumIndices n (enumNew (enumReduce ((List.range k).foldl (fun e _ => (enumNext e).1) (enumNew start)))) =
      counter n (start + k)

/-- `reversed(list)` yields the list backwards, for all lists. -/
def RevYieldsReversed : Prop :=
  ∀ (α : Type) (l : List α), revDrain (listGet l) l.length (revNew l.length) = l.reverse

/-- `reversed.__setstate__` keeps the index in `[-1, n-1]` and leaves an exhausted
iterator alone; `__length_hint__` is then in `[0, n]`. -/
def RevSetstate : Prop :=
  ∀ (ro : Rev) (n i : Int) (r : Rev), 0 ≤ n → revSetstate (.ok n) ro i = .ok r →
    (ro.index = -1 → r = ro) ∧ (ro.index ≠ -1 → -1 ≤ r.index ∧ r.index ≤ n - 1 ∧
      ∀ h, revLen (.ok n) r = .ok h → 0 ≤ h ∧ h ≤ n)

/-- `cell` order: an empty cell sorts before every full cell, two empty cells are
equal, and two full cells compare as their contents. -/
def CellOrder : Prop :=
  ∀ (α β : Type) (cmp : α → α → Nat → Py β) (ofBool : Bool → β) (x y : α) (op : Nat),
    cellCompare cmp ofBool (some x) (some y) op = cmp x y op ∧
    cellCompare cmp ofBool none (some x) 0 = .ok (ofBool true) ∧
    cellCompare cmp ofBool (some x) none 0 = .ok (ofBool false) ∧
    cellCompare cmp ofBool (none : Cell α) none 2 = .ok (ofBool true) ∧
    cellCompare cmp ofBool (none : Cell α) none 0 = .ok (ofBool false)

theorem cellOrder_proven : CellOrder := by
  intro α β cmp ofBool x y op
  simp [cellCompare]

/-- `cell_contents` reads what was stored; an empty cell raises `ValueError`, and
`del` empties the cell. -/
def CellContents : Prop :=
  ∀ (α : Type) (c : Cell α) (v : α),
    cellGet (cellSet c (some v)) = .ok v ∧
    cellGet (cellSet c none) = .error (.valueError "Cell is empty")

theorem cellContents_proven : CellContents := by
  intro α c v
  exact ⟨rfl, rfl⟩

/-- `cell()` takes at most one positional argument and no keywords. -/
def CellNew : Prop :=
  ∀ (α : Type) (x : α), cellNew [x] 0 = .ok (some x) ∧ cellNew ([] : List α) 0 = .ok none ∧
    (∀ a b rest, (cellNew (a :: b :: rest : List α) 0).toOption = none) ∧
    (∀ (l : List α) n, n ≠ 0 → (cellNew l n).toOption = none)

theorem cellNew_proven : CellNew := by
  intro α x
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro a b rest; simp [cellNew, Except.toOption]
  · intro l n hn
    have : (n != 0) = true := by simp [hn]
    simp [cellNew, this, Except.toOption]

/-- `enumerate(iterable, start)` binds its two arguments the same way however they
are spelled. -/
def EnumArgs : Prop :=
  enumArgs 2 [] = .ok (0, some 1) ∧ enumArgs 1 ["start"] = .ok (0, some 1) ∧
  enumArgs 0 ["iterable", "start"] = .ok (0, some 1) ∧
  enumArgs 0 ["start", "iterable"] = .ok (1, some 0) ∧
  enumArgs 1 [] = .ok (0, none) ∧ enumArgs 0 ["iterable"] = .ok (0, none)

end PyLean.Bytecode.IterObj
