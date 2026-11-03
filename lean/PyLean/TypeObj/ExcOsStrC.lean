import PyLean.TypeObj.ExcOs

/-!
`OSError_str` at the level of C pointers and reference counts, `Objects/exceptions.c:2346-2390`
(CPython 3.15.2).

`osErrorStr` in `ExcOs.lean` is the version the interpreter and the difftest run: it reads the
four members once and hands the values to `rt.str` and `rt.repr`, and the model's heap never
frees anything. That is what CPython does after gh-160822 (main, and the 3.15 branch after
3.15.2), which takes strong references first. 3.15.2 passes the borrowed members straight to
`PyUnicode_FromFormat` (`:2372-2388`). Its `%S` and `%R` conversions run Python code one after
the other, so a conversion that assigns a member drops the member's reference, and a later
conversion reads the pointer it was given at the start. This file models that with an explicit
heap of reference counts.

## Scope

* Objects are numbered; `0` is `None`, which is immortal. A live object has a reference count
  and the two methods `str()` and `repr()` run on it.
* What Python code in a `__str__` or `__repr__` may do to the exception is `e.m = None` or
  `del e.m` on the four `_Py_T_OBJECT` members (`:2464-2472`): `Py_XSETREF`, so the new value
  is stored and the old one decref'd (`Python/structmember.c`). Any other effect of the method
  is outside the scope: the statement quantifies over the methods that do only these.
* Freeing an object runs nothing (no `__del__`, and the model's objects hold no references).
* A conversion holds a reference to the object it converts while its method runs: the method's
  frame holds `self`. Reading a freed object is undefined behaviour, the `ub` outcome.
* `BaseException_str` (`:162-182`) is the fallback; its tuple branch formats the items of the
  args tuple, which holds references to them and which `Py_ReprEnter` keeps alive
  (`Objects/tupleobject.c:298`).
-/

namespace PyLean.TypeObj.OsStrC

/-- The four `PyObject *` members `OSError_str` reads. -/
inductive Mem where
  | errno | strerror | filename | filename2
  deriving DecidableEq, Repr

/-- What Python code does to the exception while it is formatted: `e.m = None`, or `del e.m`. -/
inductive Act where
  | setNone (m : Mem)
  | del (m : Mem)
  deriving DecidableEq, Repr

/-- A `__str__` or `__repr__`: its assignments in order, then its result, `none` when it raises. -/
structure Meth where
  acts : List Act := []
  result : Option String
  deriving DecidableEq, Repr

/-- A live object other than `None`. -/
structure CObj where
  rc : Nat
  str : Meth
  repr : Meth
  deriving DecidableEq, Repr

/-- The C heap and the fields of the `PyOSErrorObject` being formatted. `NULL` is `none`. -/
structure St where
  objs : List (Nat × CObj)
  errno : Option Nat := none
  strerror : Option Nat := none
  filename : Option Nat := none
  filename2 : Option Nat := none
  /-- The items of `self->args`. -/
  args : List Nat := []
  deriving DecidableEq, Repr

/-- Outcome of a C function: a value, a raised exception, or undefined behaviour. -/
inductive CR (α : Type) where
  | ok (a : α) (s : St)
  | raise (s : St)
  | ub (what : String) (s : St)
  deriving DecidableEq, Repr

def CR.bind {α β : Type} (r : CR α) (f : α → St → CR β) : CR β :=
  match r with
  | .ok a s => f a s
  | .raise s => .raise s
  | .ub w s => .ub w s

/-- Did this run read freed memory? -/
def CR.isUb {α : Type} : CR α → Bool
  | .ub _ _ => true
  | _ => false

def find (s : St) (a : Nat) : Option CObj := (s.objs.find? (·.1 == a)).map (·.2)

/-- Apply `f` to the object at `a`; `none` frees it. -/
def stepAt (a : Nat) (f : CObj → Option CObj) (p : Nat × CObj) : Option (Nat × CObj) :=
  if p.1 == a then (f p.2).map (p.1, ·) else some p

def mapObj (s : St) (a : Nat) (f : CObj → Option CObj) : St :=
  { s with objs := s.objs.filterMap (stepAt a f) }

def incO (o : CObj) : Option CObj := some { o with rc := o.rc + 1 }

def decO (o : CObj) : Option CObj := if o.rc ≤ 1 then none else some { o with rc := o.rc - 1 }

/-- `Py_INCREF`; `None` is immortal. -/
def incref (a : Nat) (s : St) : St := if a == 0 then s else mapObj s a incO

/-- `Py_DECREF`: the object is freed when the count reaches zero. -/
def decref (a : Nat) (s : St) : St := if a == 0 then s else mapObj s a decO

def getMem (s : St) : Mem → Option Nat
  | .errno => s.errno
  | .strerror => s.strerror
  | .filename => s.filename
  | .filename2 => s.filename2

def putMem (s : St) (v : Option Nat) : Mem → St
  | .errno => { s with errno := v }
  | .strerror => { s with strerror := v }
  | .filename => { s with filename := v }
  | .filename2 => { s with filename2 := v }

/-- `Py_XSETREF(self->m, v)`: store, then drop the old reference. -/
def setMem (s : St) (m : Mem) (v : Option Nat) : St :=
  let old := getMem s m
  let s := putMem s v m
  match old with
  | some o => decref o s
  | none => s

def runAct (s : St) : Act → St
  | .setNone m => setMem s m (some 0)
  | .del m => setMem s m none

/-- `PyObject_Str(a)` (`str := true`) or `PyObject_Repr(a)`: undefined behaviour on a freed
object; otherwise the method runs with `self` held by its frame. -/
def conv (str : Bool) (a : Nat) (s : St) : CR String :=
  if a == 0 then .ok "None" s
  else
    match find s a with
    | none => .ub s!"{if str then "%S" else "%R"} of freed object {a}" s
    | some o =>
      let m := if str then o.str else o.repr
      let s := decref a (m.acts.foldl runAct (incref a s))
      match m.result with
      | some r => .ok r s
      | none => .raise s

/-- `OR_NONE`, `Objects/exceptions.c:2350`. -/
def orNoneC (v : Option Nat) : Nat := v.getD 0

/-- The repr of the args tuple: `"(" + ", ".join(map(repr, items)) + ")"` for two or more
items, `Objects/tupleobject.c:286-345`. -/
def reprItems : List Nat → St → CR (List String)
  | [], s => .ok [] s
  | a :: rest, s => (conv false a s).bind fun r s => (reprItems rest s).bind fun rs s => .ok (r :: rs) s

/-- `BaseException_str`, `Objects/exceptions.c:162-182`. -/
def baseStr (s : St) : CR String :=
  match s.args with
  | [] => .ok "" s
  | [x] => conv true x s
  | xs => (reprItems xs s).bind fun rs s => .ok ("(" ++ ", ".intercalate rs ++ ")") s

/-- `OSError_str`, `Objects/exceptions.c:2346-2390`, outside Windows. Every pointer is read when
the call to `PyUnicode_FromFormat` is made; the conversions then run in order. -/
def osErrorStrC (s : St) : CR String :=
  match s.filename with
  | some fn =>
    let eno := orNoneC s.errno
    let se := orNoneC s.strerror
    match s.filename2 with
    | some f2 =>
      (conv true eno s).bind fun a s => (conv true se s).bind fun b s =>
        (conv false fn s).bind fun c s => (conv false f2 s).bind fun d s =>
          .ok s!"[Errno {a}] {b}: {c} -> {d}" s
    | none =>
      (conv true eno s).bind fun a s => (conv true se s).bind fun b s =>
        (conv false fn s).bind fun c s => .ok s!"[Errno {a}] {b}: {c}" s
  | none =>
    match s.errno, s.strerror with
    | some x, some y =>
      (conv true x s).bind fun a s => (conv true y s).bind fun b s => .ok s!"[Errno {a}] {b}" s
    | _, _ => baseStr s

/-- `OSError_str` after gh-160822 (main, `Objects/exceptions.c:2325-2385` there): the same,
with `Py_XNewRef` of the four members first and `Py_XDECREF` at `done:`. -/
def osErrorStrFixed (s : St) : CR String :=
  let held := [s.errno, s.strerror, s.filename, s.filename2].filterMap id
  let r := osErrorStrC (held.foldl (fun s a => incref a s) s)
  match r with
  | .ok v s => .ok v (held.foldl (fun s a => decref a s) s)
  | .raise s => .raise (held.foldl (fun s a => decref a s) s)
  | .ub w s => .ub w s

/-! ## Reachable states -/

/-- The references the exception holds: its members and its args tuple's items. -/
def holders (s : St) : List Nat :=
  [s.errno, s.strerror, s.filename, s.filename2].filterMap id ++ s.args

/-- A state Python code can reach: addresses are distinct and not `0`, a live object has a
count of at least one, and every held pointer is `None` or a live object whose count covers its
holders. -/
def wf (s : St) : Bool :=
  decide (s.objs.map (·.1)).Nodup && s.objs.all (fun p => p.1 != 0 && 1 ≤ p.2.rc) &&
  (holders s).all fun a =>
    a == 0 || match find s a with
      | some o => decide ((holders s).count a ≤ o.rc)
      | none => false

end PyLean.TypeObj.OsStrC
