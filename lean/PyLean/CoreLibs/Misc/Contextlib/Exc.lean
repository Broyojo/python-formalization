import PyLean.Core

/-!
Exceptions as objects, for `Lib/contextlib.py`.

`contextlib` compares exceptions by identity and writes `__traceback__` and `__context__`, so an
exception is a slot in a heap, not a value. `Cls` is the concrete class hierarchy of a class, own
name first; `isinstance` is membership. `Res α` is a Python result whose exception is an object of
the heap. `Heap.raiseCtx` is the implicit chaining of `_PyErr_SetObject`, Python/errors.c:199-232.
-/

namespace PyLean.CoreLibs.Misc.Contextlib

/-- The class of an exception: its `__mro__` as names, own name first. -/
abbrev Cls := List String

/-- An exception instance. `tb` is the identity of `__traceback__`; `children` is `.exceptions` of
an exception group. -/
structure ExcObj where
  cls : Cls
  msg : String := ""
  context : Option Nat := none
  cause : Option Nat := none
  tb : Option Nat := none
  children : Option (List Nat) := none
  deriving Repr, DecidableEq, Inhabited

abbrev Heap := List ExcObj

/-- An exception object is referred to by its index in the heap. -/
abbrev ExcId := Nat

/-- A Python result: a value, or the exception object that was raised. -/
abbrev Res (α : Type) := Except ExcId α

namespace Heap

def get (h : Heap) (e : ExcId) : ExcObj := h.getD e default

def alloc (h : Heap) (o : ExcObj) : Heap × ExcId := (h ++ [o], h.length)

def modify (h : Heap) (e : ExcId) (f : ExcObj → ExcObj) : Heap := h.set e (f (h.get e))

def setContext (h : Heap) (e : ExcId) (c : Option ExcId) : Heap :=
  h.modify e (fun o => { o with context := c })

def setTb (h : Heap) (e : ExcId) (t : Option Nat) : Heap := h.modify e (fun o => { o with tb := t })

/-- `isinstance(e, <class named n>)`. -/
def isInst (h : Heap) (e : ExcId) (n : String) : Bool := (h.get e).cls.contains n

/-- `isinstance(e, tuple_of_classes)`. -/
def isInstAny (h : Heap) (e : ExcId) (ns : List String) : Bool := ns.any (h.isInst e)

/-- The walk of `_PyErr_SetObject` that breaks a cycle `value` would close: starting at `o`, cut
the link that reaches `value`. `slow` is Floyd's slow pointer: a pre-existing cycle ends the walk. -/
def breakCycle (value : ExcId) : Nat → Heap → ExcId → ExcId → Bool → Heap
  | 0, h, _, _, _ => h
  | fuel + 1, h, o, slow, toggle =>
    match (h.get o).context with
    | none => h
    | some c =>
      if c = value then h.setContext o none
      else if c = slow then h
      else
        let slow := if toggle then ((h.get slow).context.getD slow) else slow
        breakCycle value fuel h c slow (!toggle)

/-- `raise value` with `handled` being handled: Python/errors.c:199-232. -/
def raiseCtx (h : Heap) (value : ExcId) (handled : Option ExcId) : Heap :=
  match handled with
  | none => h
  | some x =>
    if x = value then h
    else (breakCycle value (2 * h.length + 2) h x x false).setContext value (some x)

end Heap

/-- The classes the model creates itself. -/
def clsBase : Cls := ["BaseException"]
def clsExc : Cls := ["Exception", "BaseException"]
def clsRuntime : Cls := ["RuntimeError", "Exception", "BaseException"]
def clsAttr : Cls := ["AttributeError", "Exception", "BaseException"]
def clsType : Cls := ["TypeError", "Exception", "BaseException"]
def clsStop : Cls := ["StopIteration", "Exception", "BaseException"]
def clsStopAsync : Cls := ["StopAsyncIteration", "Exception", "BaseException"]
def clsGenExit : Cls := ["GeneratorExit", "BaseException"]
def clsBEG : Cls := ["BaseExceptionGroup", "BaseException"]
def clsEG : Cls := ["ExceptionGroup", "BaseExceptionGroup", "Exception", "BaseException"]

/-- The state a context manager runs in: the exception heap and whatever else `σ` holds. -/
structure St (σ : Type) where
  h : Heap
  g : σ
  deriving Repr

variable {σ : Type}

/-- `raise cls(msg)`, with `handled` being handled at that moment. -/
def St.raiseNew (s : St σ) (cls : Cls) (msg : String) (handled : Option ExcId := none) :
    St σ × ExcId :=
  let (h, e) := s.h.alloc { cls, msg }
  ({ s with h := h.raiseCtx e handled }, e)

end PyLean.CoreLibs.Misc.Contextlib
