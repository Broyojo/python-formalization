import PyLean.Core

/-!
# The Python object model (CPython 3.14.7)

This file is the shared vocabulary of the data model: values, the heap, type
objects, descriptors, exceptions, and the monad every interpreter-level function
runs in. Everything that mirrors C code lives in the files that import this one
(`Attr`, `Dispatch`, `Number`, `Call`, `TypeNew`, ...). The `Bytecode` module builds
on this file; see *API* below.

## Design

* `Val` is a Python reference. `None`, booleans, exact `int`/`str`/`float`/`tuple`
  are immediate; everything else (`.obj a`) is an address into `World.heap`.
  Identity (`Val.is`) is structural on immediates and by address on heap objects.
  That is exact for `None`/`True`/`False`, small ints and interned strings, and an
  approximation for big ints and tuples, which CPython may or may not share.
* `Obj` is one heap object: `ob_type`, its instance dict, its `__slots__` values and
  a type-specific `Payload`. A type object is the `Cell.ty` variant of a heap cell.
* `TypeData` is a `PyTypeObject`: `tp_name`, `tp_base`, `tp_bases`, `tp_mro`, `tp_dict`,
  the flags the semantics depends on, and the slot table. A slot holds a `SlotFn`:
  the generic `slot_*` dispatcher of that slot, or a named C implementation. Slot
  equality is therefore C function-pointer equality, which is what `binary_op1` and
  `update_one_slot` compare.
* `M` threads the `World` through both results and exceptions: side effects before a
  raise survive, as they do in Python.
* `Rt` closes the recursion. Interpreter functions never call each other through the
  dynamic graph (`getattr` -> `__get__` -> user code -> `getattr`). They call the
  hooks of an `Rt`, and `Interp.lean` ties the knot by fuel. A theorem quantified over
  `rt : Rt` holds for *every* behaviour of user-defined methods, which is how the
  properties are stated "for all class structures".

## API

* Reading: `World.get`, `typeOf`, `tdata`, `tpName`, `slotOf`, `isSubtype`, `findInMro`.
* Writing: `alloc`, `setObj`, `setTypeData`, `logEvent`.
* Exceptions: `raiseC`, `typeErr`, `attrErr`, `excMatches`, `catchMatch`.
* Calling and the other re-entrant operations: the fields of `Rt`.
* User code is opaque here: a `function` object holds `FuncData.code : Nat`, and
  `Rt.exec` runs it. `Bytecode` supplies an `exec` that interprets code objects.
-/

namespace PyLean.TypeObj

/-- Heap address. -/
abbrev Addr := Nat
abbrev Name := String

/-- The six rich comparison operators, in `Py_LT..Py_GE` order. -/
inductive CmpOp where
  | lt | le | eq | ne | gt | ge
  deriving DecidableEq, Repr, Inhabited

/-- `_Py_SwappedOp`, `Objects/object.c:1039`. -/
def CmpOp.swapped : CmpOp → CmpOp
  | .lt => .gt | .le => .ge | .eq => .eq | .ne => .ne | .gt => .lt | .ge => .le

/-- `opstrings`, `Objects/object.c:1041`. -/
def CmpOp.str : CmpOp → String
  | .lt => "<" | .le => "<=" | .eq => "==" | .ne => "!=" | .gt => ">" | .ge => ">="

/-- `name_op`, `Objects/typeobject.c:10461`. -/
def CmpOp.dunder : CmpOp → Name
  | .lt => "__lt__" | .le => "__le__" | .eq => "__eq__"
  | .ne => "__ne__" | .gt => "__gt__" | .ge => "__ge__"

/-- Every slot `slotdefs` knows about, in `slotdefs` offset order
(`Objects/typeobject.c:10969`). -/
inductive Slot where
  | tp_repr | tp_hash | tp_call | tp_str | tp_getattro | tp_setattro | tp_richcompare
  | tp_iter | tp_iternext | tp_descr_get | tp_descr_set | tp_init | tp_new | tp_finalize
  | bf_getbuffer | bf_releasebuffer | am_await | am_aiter | am_anext
  | nb_add | nb_subtract | nb_multiply | nb_remainder | nb_divmod | nb_power
  | nb_negative | nb_positive | nb_absolute | nb_bool | nb_invert
  | nb_lshift | nb_rshift | nb_and | nb_xor | nb_or | nb_int | nb_float
  | nb_inplace_add | nb_inplace_subtract | nb_inplace_multiply | nb_inplace_remainder
  | nb_inplace_power | nb_inplace_lshift | nb_inplace_rshift | nb_inplace_and
  | nb_inplace_xor | nb_inplace_or | nb_floor_divide | nb_true_divide
  | nb_inplace_floor_divide | nb_inplace_true_divide | nb_index
  | nb_matrix_multiply | nb_inplace_matrix_multiply
  | mp_length | mp_subscript | mp_ass_subscript
  | sq_length | sq_concat | sq_repeat | sq_item | sq_ass_item | sq_contains
  | sq_inplace_concat | sq_inplace_repeat
  deriving DecidableEq, Repr, Inhabited

/-- The struct a slot lives in. Static types may have NULL `tp_as_*` pointers, and
several `abstract.c` branches depend on that. -/
inductive SlotGroup where
  | tp | buffer | async | number | mapping | sequence
  deriving DecidableEq, Repr

def Slot.group : Slot → SlotGroup
  | .tp_repr | .tp_hash | .tp_call | .tp_str | .tp_getattro | .tp_setattro
  | .tp_richcompare | .tp_iter | .tp_iternext | .tp_descr_get | .tp_descr_set
  | .tp_init | .tp_new | .tp_finalize => .tp
  | .bf_getbuffer | .bf_releasebuffer => .buffer
  | .am_await | .am_aiter | .am_anext => .async
  | .mp_length | .mp_subscript | .mp_ass_subscript => .mapping
  | .sq_length | .sq_concat | .sq_repeat | .sq_item | .sq_ass_item | .sq_contains
  | .sq_inplace_concat | .sq_inplace_repeat => .sequence
  | _ => .number

/-- A family of C implementations. `SlotFn.c f` in slot `s` is the C function family
`f` installs in `s` (`.c .object` in `tp_repr` is `object_repr`, in `tp_getattro` it is
`PyObject_GenericGetAttr`, in `tp_new` it is `object_new`). Two types share a slot
pointer exactly when they hold the same `SlotFn`, because a static subclass inherits
the pointer. -/
inductive CFn where
  | object | type | none | notImpl | ellipsis | int | bool | float | str | tuple | list
  | dict | dictKeys | function | method | builtinFn | wrapperDescr | methodWrapper | methodDescr
  | classmethodDescr | memberDescr | getsetDescr | property | classmethod | staticmethod
  | super | mappingproxy | seqIter | listIter | tupleIter | strIter | cell | exception
  | exceptionGroup | stopIteration | systemExit | importError | osError | nameError
  | attributeError | syntaxError | keyError | memoryError | unicodeEncodeError
  | unicodeDecodeError | unicodeTranslateError
  | classStaticGetattro
  /-- Stand-in for a C slot this model does not implement. Reaching it is a model
  gap, reported like `PyExc.modelFuel`, and never a Python outcome. -/
  | unmodelled
  deriving DecidableEq, Repr, Inhabited

/-- The value of a slot. -/
inductive SlotFn where
  /-- `slot_tp_repr`, `slot_nb_add`, ...: the dispatcher `slotdefs` names for this slot. -/
  | generic
  | c (f : CFn)
  /-- `PyObject_HashNotImplemented`, `Objects/object.c:1145`. -/
  | hashNotImpl
  /-- `_PyObject_NextNotImplemented`, `Objects/object.c:1559`. -/
  | nextNotImpl
  deriving DecidableEq, Repr, Inhabited

/-- A Python reference. -/
inductive Val where
  | none | notImpl | ellipsis
  | bool (b : Bool)
  | int (i : Int)
  /-- An exact float as raw IEEE bits. Floats are opaque here: this model needs their
  identity and type, not their arithmetic. -/
  | float (bits : Nat)
  | str (s : String)
  | tuple (xs : List Val)
  | obj (a : Addr)
  deriving Repr, Inhabited

mutual
  /-- Reference identity, `v == w` on `PyObject *`. -/
  def Val.is : Val → Val → Bool
    | .none, .none | .notImpl, .notImpl | .ellipsis, .ellipsis => true
    | .bool a, .bool b => a == b
    | .int a, .int b => a == b
    | .float a, .float b => a == b
    | .str a, .str b => a == b
    | .tuple a, .tuple b => Val.isList a b
    | .obj a, .obj b => a == b
    | _, _ => false
  def Val.isList : List Val → List Val → Bool
    | [], [] => true
    | x :: xs, y :: ys => Val.is x y && Val.isList xs ys
    | _, _ => false
end

/-- The `self` of a C method or a bound builtin. -/
abbrev Kw := List (Name × Val)

/-- A dict with string keys, for `tp_dict` and namespaces. -/
abbrev NameDict := List (Name × Val)

def NameDict.get? (d : NameDict) (n : Name) : Option Val :=
  match d with
  | [] => none
  | (k, v) :: rest => if k == n then some v else NameDict.get? rest n

def NameDict.contains (d : NameDict) (n : Name) : Bool := (NameDict.get? d n).isSome

/-- `PyDict_SetItem`: overwrite in place, or append, preserving insertion order. -/
def NameDict.set (d : NameDict) (n : Name) (v : Val) : NameDict :=
  match d with
  | [] => [(n, v)]
  | (k, x) :: rest => if k == n then (k, v) :: rest else (k, x) :: NameDict.set rest n v

def NameDict.erase (d : NameDict) (n : Name) : NameDict :=
  match d with
  | [] => []
  | (k, x) :: rest => if k == n then rest else (k, x) :: NameDict.erase rest n

/-- Parameters and defaults of a Python function (`PyCodeObject` + `PyFunctionObject`).
`varnames` lists positional parameters, then keyword-only parameters, then the `*args`
and `**kwargs` names, in that order, as `co_varnames` does. -/
structure FuncData where
  name : String := ""
  qualname : String := ""
  module : Val := .none
  doc : Val := .none
  argcount : Nat := 0
  posonly : Nat := 0
  kwonly : Nat := 0
  varnames : List Name := []
  hasVarargs : Bool := false
  hasVarkw : Bool := false
  defaults : List Val := []
  kwdefaults : NameDict := []
  /-- `func_defaults` and `func_kwdefaults` are not NULL (an empty tuple or dict differs from
  NULL for `__defaults__` and `__kwdefaults__`). -/
  defaultsSet : Bool := false
  kwdefaultsSet : Bool := false
  /-- The code object, opaque here; `Rt.exec` interprets it. -/
  code : Nat := 0
  /-- `__class__` cell for zero-argument `super()`. -/
  classCell : Option Addr := none
  deriving Repr, Inhabited

/-- C-implemented callables: entries of `PyMethodDef` tables and of `builtins`. -/
inductive Builtin where
  /-- A method that exists in CPython but has no implementation in this model. -/
  | stub (name : String)
  | tpNewWrapper (ty : Addr)
  -- object
  | objectInitSubclass | objectSubclasshook | objectFormat | objectDir | objectSizeof
  | objectGetstate | objectReduce | objectReduceEx | classGetitem
  -- type
  | typeMro | typeSubclasses | typePrepare | typeInstancecheck | typeSubclasscheck | typeDir
  | typeSizeof
  -- builtins module
  | isinstance | issubclass | getattr | setattr | delattr | hasattr | len | iter | next
  | repr | hash | callable | dir | abs | divmod | pow | format | ascii | vars
  -- property
  | propertyGetter | propertySetter | propertyDeleter | propertySetName
  -- sequences
  | tupleCount | tupleIndex | listAppend | strFormat | dunderGetitem | dunderContains
  /-- `dict.keys`, and the `__length_hint__` of the C iterators. -/
  | dictKeysMethod | iterLengthHint
  /-- A `PyMethodDef` of an exception class, by name (`Exceptions.lean`). -/
  | excMethod (name : String)
  /-- Harness: `hash(x)` as the difftest can compare it. -/
  | hashProbe
  deriving Repr, Inhabited, DecidableEq

/-- Which C wrapper function a `wrapper_descriptor` uses (`slotdefs`'s `wrapper` column).
`update_one_slot` compares these. -/
inductive WrapKind where
  | unary | hash | call | binary | binaryL | binaryR | ternary | ternaryR | setattr | delattr
  | richcmp (op : CmpOp) | next | descrGet | descrSet | descrDelete | init | del | buffer
  | releaseBuffer | inquiry | len | indexArg | sqItem | sqSetitem | sqDelitem | objobj
  | objobjarg | delitem
  deriving DecidableEq, Repr, Inhabited

/-- An entry of `slotdefs`. -/
structure SlotDef where
  name : Name
  slot : Slot
  /-- `.generic` when `slotdefs` gives a dispatcher, `none` when the entry has `NULL`
  (`sq_concat`, `sq_repeat`, the `tp_getattr` lines, ...). -/
  generic : Option SlotFn
  wrapper : Option WrapKind
  deriving Repr, Inhabited

/-- `PyBaseExceptionObject` and the extra C fields of its subclasses that are visible
from Python. -/
structure ExcData where
  args : List Val := []
  traceback : Val := .none
  context : Option Val := none
  cause : Option Val := none
  suppressContext : Bool := false
  notes : Option Val := none
  /-- `value`/`code`/`name`/`obj`/`path`/... C members, by Python attribute name. -/
  members : NameDict := []
  /-- `BaseExceptionGroup.message` and `.exceptions`. -/
  egMessage : Option Val := none
  egExceptions : List Val := []
  /-- `PyBaseExceptionGroupObject.excs_str`: the repr saved for custom sequences. -/
  egExcsStr : Option String := none
  /-- `PyOSErrorObject.written`; `-1` means unset. -/
  written : Int := -1
  deriving Repr, Inhabited

/-- Type-specific part of a heap object. -/
inductive Payload where
  /-- `object()` and instances of classes with no builtin base. -/
  | plain
  /-- An instance of a subclass of `int`/`str`/`tuple`/`float`: the builtin value. -/
  | boxed (v : Val)
  | list (xs : List Val)
  /-- Dict entries in insertion order. Keys are compared with `Val.is` (exact `str`,
  `int`), so this is a dict for attribute namespaces, not `Objects/dictobject.c`. -/
  | dict (entries : List (Val × Val))
  | func (f : FuncData)
  /-- `PyCFunctionObject`: a builtin function, with `__self__` if bound. -/
  | builtin (b : Builtin) (self : Option Val)
  /-- `PyMethodObject`, `Objects/classobject.c`. -/
  | bound (func : Val) (self : Val)
  /-- `PyWrapperDescrObject`: `d_type`, `d_base` (an index into `slotdefs`) and
  `d_wrapped`. -/
  | wrapperDescr (owner : Addr) (base : SlotDef) (wrapped : SlotFn)
  /-- `wrapperobject` (`method-wrapper`): `descr` bound to `self`. -/
  | methodWrapper (descr : Val) (self : Val)
  /-- `PyMethodDescrObject`: `d_type`, `ml_name`. -/
  | methodDescr (owner : Addr) (name : Name) (b : Builtin)
  | classmethodDescr (owner : Addr) (name : Name) (b : Builtin)
  /-- `PyMemberDescrObject`. `readonly` mirrors `Py_READONLY`. -/
  | memberDescr (owner : Addr) (name : Name) (readonly : Bool)
  /-- `PyGetSetDescrObject`. `canSet` says whether the `PyGetSetDef` has a setter. -/
  | getsetDescr (owner : Addr) (name : Name) (canSet : Bool)
  /-- `propertyobject`, `Objects/descrobject.c`. `name` is `prop_name`. -/
  | property (fget fset fdel doc : Val) (name : Option Val) (getterDoc : Bool)
  | classmethod (f : Val)
  | staticmethod (f : Val)
  /-- `superobject`: `type`, `obj`, `obj_type`. -/
  | super (ty : Option Addr) (obj : Option Val) (objType : Option Addr)
  /-- `seqiterobject` (`iterator`): `it_seq` (cleared on exhaustion) and `it_index`. -/
  | seqIter (seq : Option Val) (index : Int)
  /-- `C.__dict__`: a `mappingproxy` over the `tp_dict` of `ty`. -/
  | typeDictProxy (ty : Addr)
  | mappingproxy (mapping : Val)
  | cell (v : Option Val)
  | exc (e : ExcData)
  /-- The contents of a `bytes` or `bytearray`, which the exception code reads. -/
  | bytes (b : List Nat)

/-- A `PyTypeObject`. -/
structure TypeData where
  /-- `tp_name`. For a heap type this equals `__name__`. -/
  name : String := ""
  qualname : String := ""
  base : Option Addr := none
  bases : List Addr := []
  /-- `tp_mro`; `none` while the class is under construction. -/
  mro : Option (List Addr) := none
  dict : NameDict := []
  slots : List (Slot × SlotFn) := []
  /-- `tp_as_number`, `tp_as_sequence`, ... are non-NULL. Always true on heap types. -/
  asNumber : Bool := false
  asSequence : Bool := false
  asMapping : Bool := false
  asAsync : Bool := false
  asBuffer : Bool := false
  /-- `Py_TPFLAGS_HEAPTYPE`, `_BASETYPE`, `_IMMUTABLETYPE`, `_METHOD_DESCRIPTOR`,
  `_IS_ABSTRACT`. -/
  heap : Bool := false
  baseType : Bool := false
  immutable : Bool := false
  methodDescriptor : Bool := false
  isAbstract : Bool := false
  /-- `tp_basicsize`, `tp_itemsize`, `tp_dictoffset`, `tp_weaklistoffset`, as integers
  because their exact values drive `solid_base` and `__class__` assignment. -/
  basicsize : Nat := 0
  itemsize : Nat := 0
  dictoffset : Int := 0
  weaklistoffset : Int := 0
  /-- Member names added by `__slots__`: `ht_slots`. -/
  htSlots : Option (List Name) := none
  subclasses : List Addr := []
  deriving Repr, Inhabited

/-- One heap object. -/
structure Obj where
  /-- `ob_type`. -/
  cls : Addr := 0
  /-- Address of the instance dict once it exists. -/
  dict : Option Addr := none
  /-- `__slots__` member values; an absent name is an unset slot. -/
  slotVals : NameDict := []
  body : Payload := .plain

/-- A heap cell: an ordinary object or a type object. -/
inductive Cell where
  | val (o : Obj)
  | ty (cls : Addr) (t : TypeData)

instance : Inhabited Obj := ⟨{}⟩
instance : Inhabited Cell := ⟨.val {}⟩

/-- The interpreter state. -/
structure World where
  heap : Array Cell := #[]
  /-- Observable events in reverse order: the difftest's call log. -/
  trace : List String := []
  /-- `globals()['__name__']` of the running frame, read by `type_new_set_module`. -/
  curModule : Option Val := none
  deriving Inhabited

/-- A raised exception. `val` is the exception object when one exists; a C-level
`PyErr_SetString` stays unmaterialised (class and message) until something catches it
as an object, as `PyErr_Occurred` state does. `fuel` is not a Python outcome. -/
inductive PyErr where
  | exc (cls : Addr) (msg : String) (val : Option Val)
  | fuel
  deriving Repr, Inhabited

/-- Result of a computation: the world survives a raise. -/
inductive R (α : Type) where
  | ok (a : α) (w : World)
  | err (e : PyErr) (w : World)
  deriving Inhabited

/-- The interpreter monad. -/
def M (α : Type) := World → R α

instance {α : Type} : Inhabited (M α) := ⟨fun w => .err .fuel w⟩

namespace M

@[inline] protected def pure {α : Type} (a : α) : M α := fun w => .ok a w

@[inline] protected def bind {α β : Type} (x : M α) (f : α → M β) : M β := fun w =>
  match x w with
  | .ok a w' => f a w'
  | .err e w' => .err e w'

instance : Monad M where
  pure := M.pure
  bind := M.bind

@[simp] theorem pure_app {α : Type} (a : α) (w : World) : (pure a : M α) w = .ok a w := rfl

@[simp] theorem bind_app {α β : Type} (x : M α) (f : α → M β) (w : World) :
    (x >>= f) w = match x w with
      | .ok a w' => f a w'
      | .err e w' => .err e w' := rfl

end M

/-- Current world. -/
@[inline] def getW : M World := fun w => .ok w w
/-- Update the world. -/
@[inline] def modW (f : World → World) : M Unit := fun w => .ok () (f w)
/-- Raise an exception. -/
@[inline] def raise {α : Type} (e : PyErr) : M α := fun w => .err e w

@[simp] theorem getW_app (w : World) : getW w = .ok w w := rfl
@[simp] theorem modW_app (f : World → World) (w : World) : modW f w = .ok () (f w) := rfl
@[simp] theorem raise_app {α : Type} (e : PyErr) (w : World) : (raise e : M α) w = .err e w := rfl

/-- `try x except: h`, with the world of the failure passed on. -/
@[inline] def tryM {α : Type} (x : M α) (h : PyErr → M α) : M α := fun w =>
  match x w with
  | .ok a w' => .ok a w'
  | .err e w' => h e w'

@[simp] theorem tryM_app {α : Type} (x : M α) (h : PyErr → M α) (w : World) :
    tryM x h w = match x w with
      | .ok a w' => .ok a w'
      | .err e w' => h e w' := rfl

/-! ## Builtin type addresses

Builtin types occupy the first heap cells, in this order; `Builtins.lean` fills them. -/

namespace B
def object : Addr := 0
def type : Addr := 1
def int : Addr := 2
def bool : Addr := 3
def float : Addr := 4
def str : Addr := 5
def tuple : Addr := 6
def list : Addr := 7
def dict : Addr := 8
def noneType : Addr := 9
def notImplType : Addr := 10
def ellipsis : Addr := 11
def function : Addr := 12
def method : Addr := 13
def builtinFn : Addr := 14
def wrapperDescr : Addr := 15
def methodWrapper : Addr := 16
def methodDescr : Addr := 17
def classmethodDescr : Addr := 18
def memberDescr : Addr := 19
def getsetDescr : Addr := 20
def property : Addr := 21
def classmethod : Addr := 22
def staticmethod : Addr := 23
def super : Addr := 24
def mappingproxy : Addr := 25
def seqIter : Addr := 26
def listIter : Addr := 27
def tupleIter : Addr := 28
def strIter : Addr := 29
def cell : Addr := 30
/-- `types.GenericAlias` and `types.UnionType`, then the types the exception code needs. -/
def genericAlias : Addr := 100
def unionType : Addr := 101
def bytes : Addr := 102
def bytearray : Addr := 103
def traceback : Addr := 104
def dictKeyIter : Addr := 105
def dictKeys : Addr := 106
-- Exception classes used by C code.
def BaseException : Addr := 31
def Exception : Addr := 32
def TypeError : Addr := 33
def AttributeError : Addr := 34
def ValueError : Addr := 35
def IndexError : Addr := 36
def KeyError : Addr := 37
def OverflowError : Addr := 38
def StopIteration : Addr := 39
def RuntimeError : Addr := 40
def SystemError : Addr := 41
def ZeroDivisionError : Addr := 42
def NameError : Addr := 43
def NotImplementedError : Addr := 44
def RecursionError : Addr := 45
def ArithmeticError : Addr := 46
def LookupError : Addr := 47
def UnboundLocalError : Addr := 48
def BaseExceptionGroup : Addr := 49
def ExceptionGroup : Addr := 50
def DeprecationWarning : Addr := 51
def RuntimeWarning : Addr := 52
def MemoryError : Addr := 53
/-- First address not reserved above; the remaining exception classes follow. -/
def firstFree : Addr := 54
end B

/-! ## Reading the world -/

/-- Heap cell at `a`. A dangling address reads as a default object; a well-formed world
has none, and using a total read keeps every model function total. -/
@[inline] def World.get (w : World) (a : Addr) : Cell := w.heap.getD a default

/-- The heap object at `a`, when it is not a type. -/
def World.objAt (w : World) (a : Addr) : Obj :=
  match w.get a with
  | .val o => o
  | .ty cls _ => { cls := cls }

/-- `Py_TYPE(v)`. -/
def typeOf (w : World) : Val → Addr
  | .none => B.noneType
  | .notImpl => B.notImplType
  | .ellipsis => B.ellipsis
  | .bool _ => B.bool
  | .int _ => B.int
  | .float _ => B.float
  | .str _ => B.str
  | .tuple _ => B.tuple
  | .obj a =>
    match w.get a with
    | .val o => o.cls
    | .ty cls _ => cls

/-- The `PyTypeObject` at `t`. -/
def tdata (w : World) (t : Addr) : TypeData :=
  match w.get t with
  | .ty _ d => d
  | .val _ => default

/-- `tp_name`. -/
def tpName (w : World) (t : Addr) : String := (tdata w t).name

/-- `Py_TYPE(v)->tp_name`. -/
def typeName (w : World) (v : Val) : String := tpName w (typeOf w v)

/-- `is_subtype_with_mro`, `Objects/typeobject.c:2804`, with the `tp_base` walk of
`type_is_subtype_base_chain` (`:2792`) bounded by the heap size. -/
def baseChain (w : World) (fuel : Nat) (a b : Addr) : Bool :=
  if a == b then true else
  match fuel, (tdata w a).base with
  | fuel + 1, some p => baseChain w fuel p b
  | _, _ => b == B.object

/-- `PyType_IsSubtype(a, b)`, `Objects/typeobject.c:2829`. -/
def isSubtype (w : World) (a b : Addr) : Bool :=
  match (tdata w a).mro with
  | some mro => mro.contains b
  | none => baseChain w w.heap.size a b

/-- `PyType_Check(v)`: is `v` a class? (`Py_TPFLAGS_TYPE_SUBCLASS` is set exactly on
subclasses of `type`, by `inherit_special`.) -/
def typeCheck (w : World) (v : Val) : Bool := isSubtype w (typeOf w v) B.type

/-- The address of a class value. -/
def asType (w : World) (v : Val) : Option Addr :=
  match v with
  | .obj a => if typeCheck w v then some a else none
  | _ => none

/-- `slot` of type `t`, `NULL` as `none`. A slot in a `tp_as_*` struct that is NULL reads
as NULL. -/
def slotOf (w : World) (t : Addr) (s : Slot) : Option SlotFn :=
  (tdata w t).slots.lookup s

/-- Is `tp_as_number` (etc.) non-NULL? -/
def hasGroup (w : World) (t : Addr) : SlotGroup → Bool
  | .tp => true
  | .buffer => (tdata w t).asBuffer
  | .async => (tdata w t).asAsync
  | .number => (tdata w t).asNumber
  | .mapping => (tdata w t).asMapping
  | .sequence => (tdata w t).asSequence

/-- `find_name_in_mro` over an explicit MRO, `Objects/typeobject.c:5748`. -/
def findInMroList (w : World) (mro : List Addr) (n : Name) : Option Val :=
  match mro with
  | [] => none
  | t :: rest =>
    match NameDict.get? (tdata w t).dict n with
    | some v => some v
    | none => findInMroList w rest n

/-- `_PyType_Lookup(t, n)`, `Objects/typeobject.c:5717`, ignoring the method cache
(`_PyType_LookupStackRefAndVersion` is a transparent cache in front of this). -/
def findInMro (w : World) (t : Addr) (n : Name) : Option Val :=
  findInMroList w ((tdata w t).mro.getD []) n

/-- `PyDescr_IsData(descr)`: the type of `descr` has `tp_descr_set`. -/
def isDataDescr (w : World) (d : Val) : Bool := (slotOf w (typeOf w d) .tp_descr_set).isSome

/-! ## Writing the world -/

def World.setCell (w : World) (a : Addr) (c : Cell) : World :=
  { w with heap := w.heap.setIfInBounds a c }

/-- Replace the object at `a`. -/
def setObj (a : Addr) (o : Obj) : M Unit := modW fun w => w.setCell a (.val o)

/-- Update the object at `a`. -/
def modObj (a : Addr) (f : Obj → Obj) : M Unit := modW fun w =>
  match w.get a with
  | .val o => w.setCell a (.val (f o))
  | .ty _ _ => w

/-- Update the type at `t`. -/
def modType (t : Addr) (f : TypeData → TypeData) : M Unit := modW fun w =>
  match w.get t with
  | .ty c d => w.setCell t (.ty c (f d))
  | .val _ => w

/-- Allocate a heap cell. -/
def allocCell (c : Cell) : M Addr := fun w =>
  .ok w.heap.size { w with heap := w.heap.push c }

/-- Allocate an object of class `cls` and return a reference. -/
def alloc (cls : Addr) (body : Payload := .plain) : M Val := do
  let a ← allocCell (.val { cls := cls, body := body })
  pure (.obj a)

/-- Append an event to the trace. -/
def logEvent (s : String) : M Unit := modW fun w => { w with trace := s :: w.trace }

/-- The payload of a heap value. -/
def payloadOf (w : World) : Val → Option Payload
  | .obj a =>
    match w.get a with
    | .val o => some o.body
    | .ty _ _ => none
  | _ => none

/-! ## Exceptions -/

/-- `PyErr_SetString(cls, msg)`. -/
def raiseC {α : Type} (cls : Addr) (msg : String) : M α := raise (.exc cls msg none)
def typeErr {α : Type} (msg : String) : M α := raiseC B.TypeError msg
def attrErr {α : Type} (msg : String) : M α := raiseC B.AttributeError msg
def valueErr {α : Type} (msg : String) : M α := raiseC B.ValueError msg
def runtimeErr {α : Type} (msg : String) : M α := raiseC B.RuntimeError msg
def systemErr {α : Type} (msg : String) : M α := raiseC B.SystemError msg
def indexErr {α : Type} (msg : String) : M α := raiseC B.IndexError msg
def keyErr {α : Type} (msg : String) : M α := raiseC B.KeyError msg
def overflowErr {α : Type} (msg : String) : M α := raiseC B.OverflowError msg
/-- A code path this model leaves out; not a Python outcome. -/
def unmodelled {α : Type} : M α := raise .fuel

/-- `PyErr_ExceptionMatches(cls)` for a pending error. -/
def excMatches (w : World) (e : PyErr) (cls : Addr) : Bool :=
  match e with
  | .exc c _ _ => isSubtype w c cls
  | .fuel => false

/-- `if (x == NULL && PyErr_ExceptionMatches(cls)) { PyErr_Clear(); h }`. -/
def catchMatch {α : Type} (cls : Addr) (x : M α) (h : M α) : M α :=
  tryM x fun e => do
    let w ← getW
    if excMatches w e cls then h else raise e

/-! ## Open recursion -/

/-- The re-entrant operations of the interpreter. Every model function calls these
instead of each other, so nothing here is recursive; `Interp.lean` ties the knot. A
property over `rt` holds whatever user-defined methods do. -/
structure Rt where
  /-- Run the code object `code` for the function `func` with these bound locals. This
  is the hook the bytecode interpreter fills in. -/
  exec (code : Nat) (func : Val) (locals : NameDict) : M Val
  /-- `PyObject_Call(f, args, kw)`. -/
  call (f : Val) (args : List Val) (kw : Kw) : M Val
  /-- `PyObject_GetAttr(v, name)`. -/
  getAttr (v : Val) (n : Name) : M Val
  /-- `PyObject_GetOptionalAttr`: `none` when the attribute is missing. -/
  getOptionalAttr (v : Val) (n : Name) : M (Option Val)
  /-- `PyObject_SetAttr(v, name, value)`; `none` deletes. -/
  setAttr (v : Val) (n : Name) (value : Option Val) : M Unit
  /-- `PyObject_IsTrue(v)`. -/
  isTrue (v : Val) : M Bool
  /-- `PyObject_RichCompare(v, w, op)`. -/
  richCompare (v w : Val) (op : CmpOp) : M Val
  /-- `PyObject_Repr(v)`. -/
  repr (v : Val) : M String
  /-- `PyObject_Str(v)`. -/
  str (v : Val) : M String
  /-- `PyObject_Hash(v)`. -/
  hash (v : Val) : M Int
  /-- `PyObject_GetIter(v)`. -/
  getIter (v : Val) : M Val
  /-- `PyIter_Next(it)`: `none` on exhaustion. -/
  iterNext (it : Val) : M (Option Val)
  /-- `PySequence_List(v)`: the items of an iterable. -/
  listItems (v : Val) : M (List Val)
  /-- `PyObject_GetItem(o, k)`. -/
  getItem (o k : Val) : M Val
  /-- The getter of the `PyGetSetDef` (or C member) `n` of the static type `owner`. -/
  getsetGet (owner : Addr) (n : Name) (obj : Val) : M Val
  /-- The setter of the same; `none` deletes. -/
  getsetSet (owner : Addr) (n : Name) (obj : Val) (value : Option Val) : M Unit
  /-- Call the `tp_new` function `f` on type `t`. -/
  tpNew (f : SlotFn) (t : Addr) (args : List Val) (kw : Kw) : M Val
  /-- Call the `tp_call` function `f` on `self`, for `wrap_call`. -/
  tpCall (f : SlotFn) (self : Val) (args : List Val) (kw : Kw) : M Val
  deriving Inhabited

/-- `Py_ssize_t` range check. -/
def inSsize (i : Int) : Bool := decide (PyLean.ssizeMin ≤ i) && decide (i ≤ PyLean.ssizeMax)

end PyLean.TypeObj
