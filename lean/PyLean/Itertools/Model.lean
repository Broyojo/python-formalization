import PyLean.Core

/-!
Shared vocabulary for the `itertools` models: `Modules/itertoolsmodule.c`
(CPython 3.14.7) and the "Roughly equivalent to" code in
`Doc/library/itertools.rst` (3.14.7), over iterables of Python ints.

Conventions:

* An input iterable is a finite `List Int` (a list iterator: once exhausted it
  stays exhausted). Its length is a `Py_ssize_t`, so `l.length ≤ ssizeMax` is a
  type invariant wherever C counts items.
* Predicates, key functions and binary functions are pure (`Int → Bool`,
  `Int → Int`, `Int → Int → Int`); raising callbacks and re-entrancy are out of
  scope.
* A C iterator is a state `σ` and a `tp_iternext` function `σ → Step σ α`
  (`NULL` without an exception is `stop`, `NULL` with one is `raise`). The doc
  generators are written as direct recursive functions over the input list,
  which is what their `for` loops do.
* Draining an iterator (`list(it)`) gives an `Run α`: the items produced, then
  `none` (normal end) or `some e` (the exception that ended it). Construction
  errors are a `Run` with no items. The doc's generator functions raise their
  argument errors lazily at the first `next()`, while C raises in the
  constructor; draining identifies the two (an intended difference).
* C allocation: `PyMem_New(type, n)` and `PyTuple_New(n)` fail with
  `MemoryError` by their own overflow checks (Include/pymem.h:63-65,
  Objects/tupleobject.c:53-56). Beyond that, `malloc` of `mallocLimit = 2^47`
  bytes or more fails (no 64-bit macOS/Linux process has that much address
  space); smaller requests are assumed to succeed. The difftest never asks for
  allocations between available RAM and `2^47` bytes, where real behaviour is
  machine dependent.
-/

namespace PyLean.Itertools

open PyLean

/-! ## Iterator protocol -/

/-- One `tp_iternext` call. -/
inductive Step (σ α : Type) where
  | yield (a : α) (s : σ)
  | stop (s : σ)
  | raise (e : PyExc) (s : σ)

/-- Result of draining an iterator: the items, then how it ended. -/
abbrev Run (α : Type) := List α × Option PyExc

/-- `list(it)` with fuel; `modelFuel` never is a Python outcome. -/
def drain {σ α : Type} (next : σ → Step σ α) : Nat → σ → Run α
  | 0, _ => ([], some .modelFuel)
  | fuel + 1, s =>
    match next s with
    | .yield a s' => let r := drain next fuel s'; (a :: r.1, r.2)
    | .stop _ => ([], none)
    | .raise e _ => ([], some e)

/-- `list(islice(it, k))` for an infinite (or any) iterator: at most `k` items. -/
def takeN {σ α : Type} (next : σ → Step σ α) : Nat → σ → Run α
  | 0, _ => ([], none)
  | k + 1, s =>
    match next s with
    | .yield a s' => let r := takeN next k s'; (a :: r.1, r.2)
    | .stop _ => ([], none)
    | .raise e _ => ([], some e)

theorem drain_succ {σ α : Type} (next : σ → Step σ α) (fuel : Nat) (s : σ) :
    drain next (fuel + 1) s = match next s with
      | .yield a s' => let r := drain next fuel s'; (a :: r.1, r.2)
      | .stop _ => ([], none)
      | .raise e _ => ([], some e) := rfl

/-- `drain` that also returns the final state (to observe how much of the
input was consumed). -/
def drainSt {σ α : Type} (next : σ → Step σ α) : Nat → σ → Run α × σ
  | 0, s => (([], some .modelFuel), s)
  | fuel + 1, s =>
    match next s with
    | .yield a s' => let r := drainSt next fuel s'; ((a :: r.1.1, r.1.2), r.2)
    | .stop s' => (([], none), s')
    | .raise e s' => (([], some e), s')

/-- A run that raised before producing anything. -/
def Run.err {α : Type} (e : PyExc) : Run α := ([], some e)

/-- A run that produced `l` and stopped normally. -/
def Run.ok {α : Type} (l : List α) : Run α := (l, none)

/-- Prepend one item (a generator that yields `a` and then continues as `r`). -/
def Run.cons {α : Type} (a : α) (r : Run α) : Run α := (a :: r.1, r.2)

/-- Prepend several items. -/
def Run.prepend {α : Type} (l : List α) (r : Run α) : Run α := (l ++ r.1, r.2)

/-! ## Input objects -/

/-- A Python object passed where an iterable is expected: something iterable,
yielding `items` and then ending (`err = none`) or raising `err`; or an object
of a non-iterable type. -/
inductive Obj (α : Type) where
  | iter (items : List α) (err : Option PyExc)
  | notIterable (tyName : String)

/-- An iterator: the items left and how it ends. After raising, a generator
is finished, so `fail` leaves an exhausted source. -/
structure Src (α : Type) where
  items : List α
  err : Option PyExc

/-- `PyObject_GetIter`, Objects/abstract.c. -/
def getIter {α : Type} : Obj α → Py (Src α)
  | .iter l e => .ok ⟨l, e⟩
  | .notIterable ty => .error (.typeError s!"'{ty}' object is not iterable")

/-- Result of `tp_iternext` on an input iterator. -/
inductive Pull (α : Type) where
  | item (x : α) (rest : Src α)
  | done
  | fail (e : PyExc) (rest : Src α)

/-- `(*Py_TYPE(it)->tp_iternext)(it)` / `PyIter_Next(it)`. -/
def Src.next {α : Type} : Src α → Pull α
  | ⟨x :: xs, e⟩ => .item x ⟨xs, e⟩
  | ⟨[], none⟩ => .done
  | ⟨[], some e⟩ => .fail e ⟨[], none⟩

/-- `PySequence_Tuple(obj)`: drains the iterable, or raises. -/
def tupleOf {α : Type} : Obj α → Py (List α)
  | .iter l none => .ok l
  | .iter _ (some e) => .error e
  | .notIterable ty => .error (.typeError s!"'{ty}' object is not iterable")

/-- `mapM` in `Except` keeps the length. -/
theorem mapM_length {α β ε : Type} (f : α → Except ε β) (os : List α) (its : List β)
    (h : os.mapM f = .ok its) : its.length = os.length := by
  induction os generalizing its with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | cons o os ih =>
    simp only [List.mapM_cons, bind, Except.bind] at h
    cases h1 : f o with
    | error e => simp [h1] at h
    | ok s =>
      simp only [h1] at h
      cases h2 : os.mapM f with
      | error e => simp [h2] at h
      | ok t =>
        simp only [h2, pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp [ih t h2]

/-- Number of items an input object provides. -/
def Obj.len {α : Type} : Obj α → Nat
  | .iter l _ => l.length
  | .notIterable _ => 0

/-! ## C integer conversions -/

/-- `PyLong_AsSsize_t` overflow message, Objects/longobject.c:668. -/
def ssizeOverflowMsg : String := "Python int too large to convert to C ssize_t"

/-- `PyLong_AsSsize_t` / `PyNumber_AsSsize_t(o, PyExc_OverflowError)` / the
Argument Clinic `Py_ssize_t` converter / `PyArg_Parse` format `n`, on an int:
the value, or `OverflowError` outside `[-2^63, 2^63-1]`. -/
def asSsize (x : Int) : Py Int :=
  if ssizeMin ≤ x ∧ x ≤ ssizeMax then .ok x else .error (.overflowError ssizeOverflowMsg)

/-- `x` is a `Py_ssize_t` value. -/
def InSsize (x : Int) : Prop := ssizeMin ≤ x ∧ x ≤ ssizeMax

instance (x : Int) : Decidable (InSsize x) := inferInstanceAs (Decidable (_ ∧ _))

def two64 : Int := 18446744073709551616

/-- `(Py_ssize_t)(size_t)x`: two's complement wraparound to 64 bits. CPython is
built with `-fno-strict-overflow`, and itertoolsmodule.c:1730-1732 adds via
`size_t` precisely to get this. -/
def wrapSsize (x : Int) : Int :=
  if x % two64 > ssizeMax then x % two64 - two64 else x % two64

/-! ## Allocation -/

/-- See the module docstring. -/
def mallocLimit : Nat := 2 ^ 47

/-- `PyMem_New(Py_ssize_t, n)` succeeds (Include/pymem.h:63-65): the overflow
check `n > PY_SSIZE_T_MAX / sizeof(Py_ssize_t)`, then `malloc(8n)`. -/
def memNewOk (n : Int) : Bool :=
  decide (n ≤ ssizeMax / 8) && decide (8 * n < mallocLimit)

/-- `PyTuple_New(n)` succeeds for `n ≥ 1` (Objects/tupleobject.c:53-57,
`sizeof(PyTupleObject) = 40` on 3.14): the overflow check, then the GC
allocation of `16 + 40 + 8(n-1)` bytes. `PyTuple_New(0)` returns the
empty-tuple singleton. -/
def tupleNewOk (n : Int) : Bool :=
  n == 0 || (decide (n ≤ (ssizeMax - 32) / 8) && decide (48 + 8 * n < mallocLimit))

def memoryError : PyExc := .named "MemoryError" ""

/-- Python `lst * n` for a list of `size` items (`sequence_repeat` narrows `n`
with `PyNumber_AsSsize_t(n, PyExc_OverflowError)`, Objects/abstract.c; then
`list_repeat_lock_held`, Objects/listobject.c:790-801, and `list_new_prealloc`
→ `PyMem_New`). `ok` means the repeat succeeds. -/
def listRepeatCheck (size : Nat) (n : Int) : Py Unit :=
  if n < ssizeMin ∨ n > ssizeMax then .error (.overflowError "cannot fit 'int' into an index-sized integer")
  else if size = 0 ∨ n ≤ 0 then .ok ()
  else if (size : Int) > ssizeMax / n then .error memoryError
  else if !memNewOk (size * n) then .error memoryError
  else .ok ()

/-! ## Callbacks used by the difftest -/

/-- `operator.truth` on an int. -/
def truthy (x : Int) : Bool := x != 0

end PyLean.Itertools
