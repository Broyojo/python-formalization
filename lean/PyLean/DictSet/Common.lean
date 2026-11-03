import PyLean.Core

/-!
Shared vocabulary for the `dict`, `set` and `OrderedDict` models.

Everything is generic over the key type `K` and the value type `V`. Lean
equality on `K` is object identity (`is`); Python-level equality and hashing are
supplied by a `Proto`, so the tables are modelled over an abstract hashable type
rather than over `int`. `__eq__` may raise and may mutate the table being probed
(`DKIX_KEY_CHANGED`, the `table != so->table` restart), so model functions run in
the state monad `M`, which keeps state changes made before an exception, exactly
as C does. A key type whose comparison is pure is `Honest`; the table theorems
quantify over all such protocols.
-/

namespace PyLean.DictSet

open PyLean

/-- State monad with exceptions in which the state survives the exception:
what C does when a callback mutates the object and then raises. -/
def M (σ α : Type) : Type := σ → Py α × σ

namespace M
variable {σ α β : Type}

instance : Monad (M σ) where
  pure a := fun s => (.ok a, s)
  bind m f := fun s =>
    match m s with
    | (.ok a, s') => f a s'
    | (.error e, s') => (.error e, s')

def get : M σ σ := fun s => (.ok s, s)
def put (s : σ) : M σ Unit := fun _ => (.ok (), s)
def modify (f : σ → σ) : M σ Unit := fun s => (.ok (), f s)
def throw (e : PyExc) : M σ α := fun s => (.error e, s)
def lift (r : Py α) : M σ α := fun s => (r, s)

/-- `try m except e: h e` -/
def tryCatch (m : M σ α) (h : PyExc → M σ α) : M σ α := fun s =>
  match m s with
  | (.ok a, s') => (.ok a, s')
  | (.error e, s') => h e s'

/-- A branch the source asserts is unreachable; never a Python outcome. -/
def unreachable : M σ α := throw .modelFuel

@[simp] theorem pure_run (a : α) (s : σ) : (pure a : M σ α) s = (.ok a, s) := rfl
@[simp] theorem get_run (s : σ) : (get : M σ σ) s = (.ok s, s) := rfl
@[simp] theorem put_run (s s' : σ) : (put s' : M σ Unit) s = (.ok (), s') := rfl
@[simp] theorem modify_run (f : σ → σ) (s : σ) : (modify f : M σ Unit) s = (.ok (), f s) := rfl
@[simp] theorem throw_run (e : PyExc) (s : σ) : (throw e : M σ α) s = (.error e, s) := rfl
@[simp] theorem lift_run (r : Py α) (s : σ) : (lift r : M σ α) s = (r, s) := rfl

theorem bind_run (m : M σ α) (f : α → M σ β) (s : σ) :
    (m >>= f) s = match m s with
      | (.ok a, s') => f a s'
      | (.error e, s') => (.error e, s') := rfl

theorem bind_ok {m : M σ α} {f : α → M σ β} {s s' : σ} {a : α}
    (h : m s = (.ok a, s')) : (m >>= f) s = f a s' := by
  rw [bind_run, h]

theorem bind_err {m : M σ α} {f : α → M σ β} {s s' : σ} {e : PyExc}
    (h : m s = (.error e, s')) : (m >>= f) s = (.error e, s') := by
  rw [bind_run, h]

end M

/-- `RuntimeError(msg)`; `PyExc` has no dedicated constructor. -/
def runtimeError (msg : String) : PyExc := .named "RuntimeError" msg
def memoryError : PyExc := .named "MemoryError" ""
def attributeError (msg : String) : PyExc := .named "AttributeError" msg
def systemError (msg : String) : PyExc := .named "SystemError" msg

/-- Not a Python exception: the interpreter would dereference NULL here
(`Py_NewRef(NULL)`) and die with SIGSEGV. A property "never crashes" says that
this value is never produced. -/
def crash (_where : String) : PyExc := .named "<crash>" ""

/-- The object protocol keys are used through. -/
structure KeyOps (K : Type) where
  /-- `PyObject_Hash`; never returns `-1` successfully. -/
  hash : K → Py Int
  /-- `PyUnicode_CheckExact`. -/
  isStr : K → Bool
  /-- `PyUnicode_Check`. -/
  isStrLike : K → Bool
  /-- `unicode_eq` on two exact strings. -/
  strEq : K → K → Bool
  /-- `repr(key)`, used in `KeyError` messages (total: a failing repr there
  would replace the error, which the models do not need). -/
  reprStr : K → String
  /-- `PyObject_Repr`. -/
  repr : K → Py String
  /-- `%T`. -/
  typeName : K → String

/-- `PyObject_RichCompareBool(a, b, Py_EQ)` in state `σ`. It has the identity
shortcut built in and may raise or mutate the state. -/
structure Proto (K σ : Type) extends KeyOps K where
  eq : K → K → M σ Bool
  /-- What a call of `__hash__` does to the state, whatever it then answers: `hash` gives the
  answer (or the exception), this the effect, which comes first. -/
  hashEff : K → σ → σ := fun _ s => s

/-- `_PyErr_SetKeyError(key)`: `str(e)` is `repr(key)`. -/
def keyErr {K σ : Type} (P : Proto K σ) (k : K) : PyExc := .keyError (P.reprStr k)

/-- `(size_t)hash`. -/
def toU64 (h : Int) : Nat := (h % (2 ^ 64 : Int)).toNat

/-- `(Py_hash_t)u` for `u : size_t`. -/
def toI64 (u : Nat) : Int :=
  let v : Nat := u % 2 ^ 64
  if v < 2 ^ 63 then (v : Int) else (v : Int) - (2 ^ 64 : Int)

def PERTURB_SHIFT : Nat := 5

/-- One step of the probe recurrence, shared by `do_lookup`, `lookdict_index`,
`find_empty_slot` and `build_indices_*` (`dictobject.c:1075-1076`):
`perturb >>= PERTURB_SHIFT; i = mask & (i*5 + perturb + 1)`. -/
def probeStep (mask i perturb : Nat) : Nat × Nat :=
  let p := perturb >>> PERTURB_SHIFT
  (mask &&& (i * 5 + p + 1), p)

/-- The `n`-th probe position: `(hash & mask)` stepped `n` times. -/
def probeState (mask u : Nat) : Nat → Nat × Nat
  | 0 => (u &&& mask, u)
  | n + 1 =>
    let s := probeState mask u n
    probeStep mask s.1 s.2

/-- An iterable as the C code consumes it: `PyObject_GetIter` may fail, each
`PyIter_Next` yields an item, and the iterator may end with an exception rather
than `StopIteration`. -/
structure Iterable (α : Type) where
  getIter : Option PyExc := none
  items : List α
  stop : Option PyExc := none
  deriving Inhabited

/-- An iterator driven from C, as a script of calls: `getIter` is `PyObject_GetIter`, and each
step is one `PyIter_Next`, which may raise, may change whatever the state holds, and returns
`none` on exhaustion. A step can depend on the state, so an iterator whose length depends on
what the loop did fits, up to the length of the script. -/
structure ReIter (σ α : Type) where
  getIter : M σ Unit := pure ()
  steps : List (M σ (Option α))

/-- An `Iterable` as such a script: no re-entry, and failures only where `Iterable` has them. -/
def ReIter.ofIterable {σ α : Type} (it : Iterable α) : ReIter σ α :=
  { getIter := match it.getIter with
      | some e => M.throw e
      | none => pure ()
    steps := it.items.map (fun x => pure (some x)) ++
      match it.stop with
      | some e => [M.throw e]
      | none => [] }

end PyLean.DictSet
