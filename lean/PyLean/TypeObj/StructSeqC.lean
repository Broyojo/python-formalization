import PyLean.TypeObj.StructSeq
import PyLean.UnicodeObj.ObjectWriterProps

/-!
# Struct sequences in memory: Objects/structseq.c, CPython 3.15.2

`StructSeq.lean` models what the constructor, `__reduce__` and `__replace__` compute when the
type's three size attributes tell the truth. This file models the C underneath: the type's
layout (`tp_name`, `tp_members`, `tp_basicsize`), the three size attributes as they sit in the
type's own dict, the item array of an object as allocated, and the functions that read them.

What is modelled, and the scope limits:

* The size attributes `n_sequence_fields`, `n_fields`, `n_unnamed_fields` are read from the
  type's own dict (`_PyType_GetDict(tp)`, no MRO walk) by `get_type_attr_as_size` (:27-42). The
  heap types that `PyStructSequence_NewType` builds (`os.stat_result`, `os.terminal_size`,
  `time.struct_time`, ...) are not `Py_TPFLAGS_IMMUTABLETYPE`, so Python code can rebind or
  delete these attributes (checked on 3.15.2); none of them is an acceptable base type, so no
  subclass can override them. A dict lookup is an arbitrary outcome (`TDict`): it can raise if a
  non-str key was planted in the dict through `gc.get_referents`; what such a key's `__eq__` does
  to other state is not modelled.
* Memory is the item array as allocated, `CObj.slots`: a slot holds an object, `NULL`, or junk
  (`PyObject_GC_NewVar` does not clear the block). Reading or writing outside it, dereferencing
  junk or `NULL`, or reading `tp_members` past its sentinel is `CRes.ub`: undefined behaviour, which
  on 3.15.2 shows up as a segfault or a silent heap overwrite.
* Allocation failure is an arbitrary predicate `malloc` on the byte count. `PyUnicodeWriter` is the
  model of `UnicodeObj/ObjectWriter.lean`; its creation can fail (`writerCreateC`, with its own
  predicate `walloc`), its later growth cannot (that model has no allocation failure).
* Python code run by a callback is an arbitrary outcome, and so is each lookup in the
  constructor's `dict` argument and each pop from `__replace__`'s keywords: a key's `__eq__` can
  raise or change the dict between them.
* Python code run by a callback is an arbitrary outcome: `__repr__` of an item (`rep`), the
  conversion of the constructor's argument (`FastArg`, which may also rebind the size
  attributes), the lookups in the constructor's `dict` argument (`CDictArg`). Reference counts
  and GC tracking are not modelled.
* C strings (`tp_name`, member names) are their bytes before the terminating NUL.
-/

namespace PyLean.TypeObj.StructSeq

open PyLean PyLean.UnicodeObj

/-- What a C function returns: a value, `NULL` (or `-1`) with an exception set, `NULL` with no
exception set (the interpreter then raises `SystemError: ... returned NULL without setting an
exception`), or undefined behaviour, with a tag saying which access it was. -/
inductive CRes (α : Type) where
  | ok (a : α)
  | exc (e : PyExc)
  | nullNoExc
  | ub (what : String)

namespace CRes

def bind {α β : Type} : CRes α → (α → CRes β) → CRes β
  | .ok a, f => f a
  | .exc e, _ => .exc e
  | .nullNoExc, _ => .nullNoExc
  | .ub w, _ => .ub w

instance : Monad CRes where
  pure := .ok
  bind := CRes.bind

@[simp] theorem bind_ok {α β : Type} (a : α) (f : α → CRes β) : (CRes.ok a >>= f) = f a := rfl
@[simp] theorem bind_exc {α β : Type} (e : PyExc) (f : α → CRes β) : (CRes.exc e >>= f) = .exc e := rfl
@[simp] theorem bind_null {α β : Type} (f : α → CRes β) : (CRes.nullNoExc >>= f) = .nullNoExc := rfl
@[simp] theorem bind_ub {α β : Type} (w : String) (f : α → CRes β) : (CRes.ub w >>= f) = .ub w := rfl
@[simp] theorem pure_eq {α : Type} (a : α) : (pure a : CRes α) = .ok a := rfl

/-- A Python exception becomes `NULL` with that exception set. -/
def ofPy {α : Type} : Py α → CRes α
  | .ok a => .ok a
  | .error e => .exc e

def isUB {α : Type} : CRes α → Bool
  | .ub _ => true
  | _ => false

end CRes

def systemError (m : String) : PyExc := .named "SystemError" m
def memoryError : PyExc := .named "MemoryError" ""

/-! ## The size attributes -/

/-- A value stored under a size key. `PyLong_AsSsize_t` accepts exactly the objects that pass
`PyLong_Check`: ints and int subclasses, `bool` included, with their integer value. Anything else
(a float, a str, an object with `__index__`) is `other`. -/
inductive SizeVal where
  | int (n : Int)
  | other
  deriving DecidableEq, Repr

/-- `PyLong_AsSsize_t`, Objects/longobject.c:708-751: `TypeError` for a non-int (:717-719, no
`__index__` call), `OverflowError` outside `Py_ssize_t` (:747-750). -/
def asSsize : SizeVal → Py Int
  | .other => .error (.typeError "an integer is required")
  | .int n =>
    if ssizeMin ≤ n ∧ n ≤ ssizeMax then .ok n
    else .error (.overflowError "Python int too large to convert to C ssize_t")

/-- The type's own dict, as `PyDict_GetItemWithError` reads it: what is stored under a key, if
anything, or the exception the lookup raised. -/
abbrev TDict := String → Py (Option SizeVal)

/-- `get_type_attr_as_size(tp, name)`, Objects/structseq.c:27-42. -/
def getTypeAttrAsSize (tpName : String) (d : TDict) (key : String) : Py Int :=
  match d key with
  | .error e => .error e
  | .ok none => .error (.typeError s!"~Missed attribute '{key}' of type {tpName}")
  | .ok (some v) => asSsize v

/-- What every caller does with it: `n = ...; if (n < 0) return NULL;` (:69, :73, :174, :178,
:182, :357, :404). A negative value with no exception set, which `get_type_attr_as_size` returns
for a stored negative int, makes the caller return `NULL` with nothing set. -/
def sizeOrNull (r : Py Int) : CRes Nat :=
  match r with
  | .error e => .exc e
  | .ok n => if n < 0 then .nullNoExc else .ok n.toNat

/-! ## Types and objects -/

/-- One `PyMemberDef` of `tp_members`: its name, and the item slot its offset points at,
`(offset - offsetof(PyStructSequence, ob_item)) / sizeof(PyObject *)`. -/
structure Member where
  name : Bytes
  slot : Nat
  deriving DecidableEq, Repr

/-- A struct sequence type: `tp_name`, `tp_members` up to its `NULL`-name sentinel,
`tp_basicsize`, and its own dict. -/
structure CType where
  name : Bytes
  members : List Member
  basicsize : Nat
  dict : TDict

/-- `tp_name` as `%s` prints it in a message (the bytes, for ASCII names). -/
def CType.nameStr (t : CType) : String := String.ofList (t.name.map Char.ofNat)

/-- `offsetof(PyStructSequence, ob_item)` on a 64-bit build: the `PyVarObject` header and the
cached hash. -/
def obItemOff : Nat := 32

/-- `get_real_size(op)`, :55-62: `Py_SIZE(op)` plus the hidden slots counted in `tp_basicsize`. -/
def realSize (t : CType) (size : Nat) : Nat := size + (t.basicsize - obItemOff) / 8

inductive Slot (α : Type) where
  | null
  | val (a : α)
  | junk
  deriving DecidableEq, Repr

/-- A struct sequence object: `Py_SIZE` and its item array as allocated. -/
structure CObj (α : Type) where
  size : Nat
  slots : List (Slot α)
  deriving DecidableEq, Repr

/-- Read slot `i` of the block. -/
def readSlot {α : Type} (slots : List (Slot α)) (i : Nat) (what : String) : CRes (Slot α) :=
  if h : i < slots.length then .ok slots[i] else .ub what

/-- Write slot `i` of the block. -/
def writeSlot {α : Type} (slots : List (Slot α)) (i : Nat) (v : Slot α) (what : String) :
    CRes (List (Slot α)) :=
  if i < slots.length then .ok (slots.set i v) else .ub what

/-- A slot used as an object (`Py_NewRef`, `PyDict_SetItem`, ...): `NULL` and junk crash. -/
def deref {α : Type} (s : Slot α) (what : String) : CRes α :=
  match s with
  | .val a => .ok a
  | _ => .ub what

/-- `tp_members[idx].name` as a C string: the sentinel's name is `NULL`, and reading past the
sentinel (or before the array) is out of bounds. -/
inductive MName where
  | name (b : Bytes)
  | null

def memberName (ms : List Member) (idx : Int) (what : String) : CRes MName :=
  if idx < 0 then .ub what
  else if h : idx.toNat < ms.length then .ok (.name ms[idx.toNat].name)
  else if idx.toNat = ms.length then .ok .null
  else .ub what

/-- `PyUnicode_FromString(name)`: strict UTF-8; a `NULL` name crashes in `strlen`. -/
def fromCString (n : MName) (what : String) : CRes Str :=
  match n with
  | .name b => CRes.ofPy (utf8Decode b .strict)
  | .null => .ub what

/-! ## `PyStructSequence_New`, `PyStructSequence_SetItem`, `PyStructSequence_GetItem` -/

/-- `_PyType_PreHeaderSize` of a GC type without managed dict: one `PyGC_Head`. -/
def preSize : Nat := 16

/-- `PyObject_GC_NewVar(PyStructSequence, type, n)` for `n ≥ 0`: the byte size of the block.
`_PyObject_VAR_SIZE` (Include/cpython/objimpl.h:22-26) computes `basicsize + n * itemsize` in
`size_t` and rounds up to 8, both modulo 2^64 with no overflow check; `gc_alloc`
(Python/gc.c:2012-2028) refuses a size above `PY_SSIZE_T_MAX - presize`, and the allocator may
fail. `n < 0` (Python/gc.c:2055-2058) cannot happen: every caller checks it first. -/
def gcNewVar (basicsize n : Nat) (malloc : Nat → Bool) : CRes Nat :=
  let raw := (basicsize + n * 8) % 2 ^ 64
  let size := ((raw + 7) / 8 * 8) % 2 ^ 64
  if size > ssizeMax.toNat - preSize then .exc memoryError
  else if !malloc (preSize + size) then .exc memoryError
  else .ok size

/-- `PyStructSequence_New(type)`, :64-88: `n_fields` then `n_sequence_fields` from the dict, a
block for `n_fields` items (on top of `tp_basicsize`, which already holds the hidden ones),
the hash cache reset (:80, the last word of the header), `Py_SIZE = n_sequence_fields`, and the
first `n_fields` slots set to `NULL`. The rest of the block is junk. -/
def pssNew {α : Type} (t : CType) (malloc : Nat → Bool) : CRes (CObj α) := do
  let size ← sizeOrNull (getTypeAttrAsSize t.nameStr t.dict "n_fields")
  let vsize ← sizeOrNull (getTypeAttrAsSize t.nameStr t.dict "n_sequence_fields")
  let bytes ← gcNewVar t.basicsize size malloc
  if bytes < obItemOff then .ub "PyStructSequence_New: hash cache past the block"
  else
    let cap := (bytes - obItemOff) / 8
    if size > cap then .ub "PyStructSequence_New: NULL stores past the block"
    else .ok { size := vsize, slots := List.replicate size .null ++ List.replicate (cap - size) .junk }

/-- `PyStructSequence_SetItem(op, index, value)`, :90-101, in a release build: the asserts
(:94-99) are compiled out, so any index is written. -/
def pssSetItem {α : Type} (o : CObj α) (index : Int) (v : α) : CRes (CObj α) :=
  if index < 0 then .ub "PyStructSequence_SetItem: negative index"
  else do
    let s ← writeSlot o.slots index.toNat (.val v) "PyStructSequence_SetItem: past the block"
    .ok { o with slots := s }

/-- `PyStructSequence_GetItem(op, index)`, :103-113, in a release build: the borrowed pointer
in slot `index`, unchecked. -/
def pssGetItem {α : Type} (o : CObj α) (index : Int) : CRes (Slot α) :=
  if index < 0 then .ub "PyStructSequence_GetItem: negative index"
  else readSlot o.slots index.toNat "PyStructSequence_GetItem: past the block"

/-! ## `structseq_repr`, :273-339 -/

/-- `PyUnicodeWriter_WriteRepr(writer, value)`, Objects/unicode_writer.c:336-354: `NULL` writes
`<NULL>`; otherwise the text of `repr(value)` (`rep`), or its exception, is written with
`_PyUnicodeWriter_WriteStr`. For an exact int the writer formats it itself
(`_PyLong_FormatWriter`), which writes the same text as `int.__repr__` and raises the same
`ValueError` past the digit limit; `rep` stands for both. Junk is dereferenced. -/
def writeReprSlot {α : Type} (rep : α → Py Str) (w : UWriter) : Slot α → CRes UWriter
  | .null => .ok (writeReprOp w none).1
  | .val a =>
    match rep a with
    | .ok s => .ok (writeText w s)
    | .error e => .exc e
  | .junk => .ub "structseq_repr: junk item"

/-- One writer call: `if (PyUnicodeWriter_Write...(writer, ...) < 0) goto error;`. -/
def wop (w : UWriter) (op : WOp) : CRes UWriter :=
  match applyOp w op with
  | (w', .ok _) => .ok w'
  | (_, .error e) => .exc e

def chComma : Nat := 44
def chSpace : Nat := 32
def chEq : Nat := 61
def chLParen : Nat := 40
def chRParen : Nat := 41

/-- Write `", "` before every field but the first, :297-305. -/
def reprSep (i : Nat) (w : UWriter) : CRes UWriter :=
  if i > 0 then do
    let w ← wop w (.char chComma)
    wop w (.char chSpace)
  else .ok w

/-- Write the name, `=`, and `repr(value)`, :315-327. -/
def reprNameValue {α : Type} (o : CObj α) (rep : α → Py Str) (i : Nat) (b : Bytes) (w : UWriter) :
    CRes UWriter := do
  let w ← wop w (.utf8 b (-1))
  let w ← wop w (.char chEq)
  let v ← pssGetItem o i
  writeReprSlot rep w v

/-- The body of the field loop, :297-327, for field `i`: `tp_members[i].name` (:308), refused
with `SystemError` when it is the sentinel's `NULL` (:309-314). -/
def reprField {α : Type} (t : CType) (o : CObj α) (rep : α → Py Str) (i : Nat) (w : UWriter) :
    CRes UWriter := do
  let w ← reprSep i w
  let n ← memberName t.members i "structseq_repr: tp_members past the sentinel"
  match n with
  | .null =>
    .exc (systemError s!"~In structseq_repr(), member {i} name is NULL for type {t.nameStr}")
  | .name b => reprNameValue o rep i b w

/-- `for (i = 0; i < VISIBLE_SIZE(obj); i++)`, :296: fields `i, i+1, ...` while `fuel` lasts. -/
def reprLoop {α : Type} (t : CType) (o : CObj α) (rep : α → Py Str) :
    Nat → Nat → UWriter → CRes UWriter
  | 0, _, w => .ok w
  | fuel + 1, i, w => do
    let w ← reprField t o rep i w
    reprLoop t o rep fuel (i + 1) w

/-- A `Py_ssize_t` result of `+` and `*`: CPython is built with `-fno-strict-overflow`, so signed
arithmetic wraps modulo 2^64. -/
def toSsize (x : Int) : Int :=
  let m := x % 2 ^ 64
  if m ≥ 2 ^ 63 then m - 2 ^ 64 else m

/-- `PyUnicodeWriter_Create(length)`, Objects/unicode_writer.c:104-132: a negative length is
`ValueError` (:107-111); otherwise the writer and, for `length > 0`, a buffer of `length`
characters are allocated (`_PyUnicodeWriter_Prepare`, then `PyUnicode_New`, which refuses or
fails to allocate with `MemoryError`). `walloc length` says whether that allocation succeeds.
Later growth of the buffer is the writer model of `UnicodeObj/ObjectWriter.lean`, which has no
allocation failure. -/
def writerCreateC (length : Int) (walloc : Int → Bool) : CRes UWriter :=
  if length < 0 then .exc (.valueError "length must be positive")
  else if length > 0 ∧ walloc length = false then .exc memoryError
  else CRes.ofPy (writerCreate length)

/-- `structseq_repr(op)`, :273-339. The writer is created with room for
`strlen(tp_name) + 1 + Py_SIZE * 5 + 1` characters (:280-286), computed in `Py_ssize_t`, so a
huge `Py_SIZE` wraps it negative; `tp_name` is written whole with
`PyUnicodeWriter_WriteUTF8(writer, tp_name, strlen(tp_name))` (:289): there is no truncation in
3.15. -/
def structseqRepr {α : Type} (walloc : Int → Bool) (t : CType) (o : CObj α) (rep : α → Py Str) :
    CRes Str := do
  let w ← writerCreateC (toSsize (t.name.length + 1 + o.size * 5 + 1)) walloc
  let w ← wop w (.utf8 t.name t.name.length)
  let w ← wop w (.char chLParen)
  let w ← reprLoop t o rep o.size 0 w
  let w ← wop w (.char chRParen)
  .ok w.finish.1

/-! ## `structseq_reduce`, :342-385 -/

/-- `PyTuple_FromArray(self->ob_item, n)`: a new reference to each of the first `n` slots. -/
def fromArray {α : Type} (slots : List (Slot α)) : Nat → CRes (List α)
  | 0 => .ok []
  | n + 1 => do
    let xs ← fromArray slots n
    let s ← readSlot slots n "structseq_reduce: visible item past the block"
    let v ← deref s "structseq_reduce: NULL or junk visible item"
    .ok (xs ++ [v])

/-- The hidden-field loop of `structseq_reduce`, :368-372, from field `i` while `fuel` lasts:
`tp_members[i - n_unnamed_fields].name` and slot `i` go into the dict. -/
def reduceLoop {α : Type} (t : CType) (o : CObj α) (nUnnamed : Nat) :
    Nat → Nat → CRes (List (Str × α))
  | 0, _ => .ok []
  | fuel + 1, i => do
    let n ← memberName t.members ((i : Int) - nUnnamed) "structseq_reduce: tp_members out of range"
    let key ← fromCString n "structseq_reduce: NULL member name"
    let s ← readSlot o.slots i "structseq_reduce: hidden item past the block"
    let v ← deref s "structseq_reduce: NULL or junk hidden item"
    let rest ← reduceLoop t o nUnnamed fuel (i + 1)
    .ok ((key, v) :: rest)

/-- `structseq_reduce(self)`, :342-385: the visible items and the (name, value) pairs of the
hidden fields, in insertion order. `n_fields` comes from `tp_basicsize` (never negative), the
unnamed count from the dict. -/
def reduceC {α : Type} (t : CType) (o : CObj α) : CRes (List α × List (Str × α)) := do
  let nFields := realSize t o.size
  let nVis := o.size
  let nUnnamed ← sizeOrNull (getTypeAttrAsSize t.nameStr t.dict "n_unnamed_fields")
  let tup ← fromArray o.slots nVis
  let d ← reduceLoop t o nUnnamed (nFields - nVis) nVis
  .ok (tup, d)

/-! ## `structseq_replace`, :388-458 -/

/-- `kwargs`. `pop i name` is `PyDict_PopString(kwargs, name, &ob)` for field `i`, after the name
is decoded (Objects/dictobject.c:3326-3339): the value removed, if a key compared equal, or what
a key's `__eq__` raised. Keyword names can be str subclasses whose `__hash__` and `__eq__` are
Python code, so each pop is its own outcome. `sizeAfter` is `PyDict_GET_SIZE(kwargs)` after the
loop (:435). -/
structure KwArg (α : Type) where
  pop : Nat → Str → Py (Option α)
  sizeAfter : Nat

/-- The keyword loop, :423-433, from field `i` while `fuel` lasts. -/
def replaceKwLoop {α : Type} (t : CType) (self : CObj α) (pop : Nat → Str → Py (Option α)) :
    Nat → Nat → List (Slot α) → CRes (List (Slot α))
  | 0, _, res => .ok res
  | fuel + 1, i, res => do
    let n ← memberName t.members i "structseq_replace: tp_members past the sentinel"
    let key ← fromCString n "structseq_replace: NULL member name"
    let got ← CRes.ofPy (pop i key)
    let v ← match got with
      | some v => pure v
      | none => do
        let s ← readSlot self.slots i "structseq_replace: self item past the block"
        deref s "structseq_replace: NULL or junk self item"
    let res ← writeSlot res i (.val v) "structseq_replace: write past the new block"
    replaceKwLoop t self pop fuel (i + 1) res

/-- The copy loop, :447-449, from field `i` while `fuel` lasts. -/
def replaceCopyLoop {α : Type} (self : CObj α) : Nat → Nat → List (Slot α) → CRes (List (Slot α))
  | 0, _, res => .ok res
  | fuel + 1, i, res => do
    let s ← readSlot self.slots i "structseq_replace: self item past the block"
    let v ← deref s "structseq_replace: NULL or junk self item"
    let res ← writeSlot res i (.val v) "structseq_replace: write past the new block"
    replaceCopyLoop self fuel (i + 1) res

/-- `structseq_replace(self, *args, **kwargs)`, :388-458. `kws` is `kwargs`, `none` for `NULL`.
The new object comes from `PyStructSequence_New(Py_TYPE(self))`, which reads the dict again; the
loops run over `n_fields` of `self`, from `tp_basicsize`. -/
def replaceC {α : Type} (t : CType) (self : CObj α) (nargs : Nat) (kws : Option (KwArg α))
    (malloc : Nat → Bool) : CRes (CObj α) := do
  if nargs ≠ 0 then .exc (.typeError "__replace__() takes no positional arguments")
  else
    let nFields := realSize t self.size
    let nUnnamed ← sizeOrNull (getTypeAttrAsSize t.nameStr t.dict "n_unnamed_fields")
    if nUnnamed > 0 then
      .exc (.typeError s!"~__replace__() is not supported for {t.nameStr} because it has unnamed field(s)")
    else
      let res ← pssNew (α := α) t malloc
      match kws with
      | some kws => do
        let slots ← replaceKwLoop t self kws.pop nFields 0 res.slots
        if kws.sizeAfter > 0 then .exc (.typeError "~Got unexpected field name(s): %R")
        else .ok { res with slots := slots }
      | none => do
        let slots ← replaceCopyLoop self nFields 0 res.slots
        .ok { res with slots := slots }

/-! ## `structseq_new_impl`, :166-270 -/

/-- `PySequence_Fast(arg, "constructor requires a sequence")`: the items, or the exception; a
list or tuple is used as is, anything else is iterated, which runs Python code, so the type's
dict is whatever that code left (`dictAfter`). -/
structure FastArg (α : Type) where
  res : Py (List α)
  dictAfter : TDict

/-- The `dict` argument. `look i name` is `PyDict_GetItemStringRef(dict, name)` for field `i`,
after the name is decoded: what it finds, or what a key's `__eq__` raised. Such an `__eq__` is
Python code that can change the dict, so each lookup is its own outcome, and the two reads of
`PyDict_GET_SIZE(dict)` are separate: `size0` before the loop (:238), `size1` after it (:255). -/
inductive CDictArg (α : Type) where
  | dict (look : Nat → Str → Py (Option α)) (size0 size1 : Nat)
  | notDict

/-- The `dict` loop, :240-254, from field `i` while `fuel` lasts: the value found under
`tp_members[i - n_unnamed_fields].name`, or `None`. Returns the block and the count found. -/
def newDictLoop {α : Type} (t : CType) (none_ : α) (look : Nat → Str → Py (Option α)) (nUnnamed : Nat) :
    Nat → Nat → List (Slot α) → Nat → CRes (List (Slot α) × Nat)
  | 0, _, res, found => .ok (res, found)
  | fuel + 1, i, res, found => do
    let n ← memberName t.members ((i : Int) - nUnnamed) "structseq_new: tp_members out of range"
    let key ← fromCString n "structseq_new: NULL member name"
    let got ← CRes.ofPy (look i key)
    let (v, found) := match got with
      | some v => (v, found + 1)
      | none => (none_, found)
    let res ← writeSlot res i (.val v) "structseq_new: dict field past the block"
    newDictLoop t none_ look nUnnamed fuel (i + 1) res found

/-- The `None` loop, :263-265. -/
def newNoneLoop {α : Type} (none_ : α) : Nat → Nat → List (Slot α) → CRes (List (Slot α))
  | 0, _, res => .ok res
  | fuel + 1, i, res => do
    let res ← writeSlot res i (.val none_) "structseq_new: None field past the block"
    newNoneLoop none_ fuel (i + 1) res

/-- The copy loop, :233-236. -/
def newCopyLoop {α : Type} : List α → Nat → List (Slot α) → CRes (List (Slot α))
  | [], _, res => .ok res
  | x :: xs, i, res => do
    let res ← writeSlot res i (.val x) "structseq_new: item past the block"
    newCopyLoop xs (i + 1) res

/-- `structseq_new_impl(type, arg, dict)`, :166-270. The three sizes are read first (:173-184),
then the argument is converted, which may run Python code; `PyStructSequence_New` (:228) then
reads `n_fields` and `n_sequence_fields` again from the dict as that code left it. -/
def newImplC {α : Type} (t : CType) (arg : FastArg α) (dict : Option (CDictArg α)) (none_ : α)
    (malloc : Nat → Bool) : CRes (CObj α) := do
  let minLen ← sizeOrNull (getTypeAttrAsSize t.nameStr t.dict "n_sequence_fields")
  let maxLen ← sizeOrNull (getTypeAttrAsSize t.nameStr t.dict "n_fields")
  let nUnnamed ← sizeOrNull (getTypeAttrAsSize t.nameStr t.dict "n_unnamed_fields")
  let xs ← CRes.ofPy arg.res
  let t := { t with dict := arg.dictAfter }
  match dict with
  | some .notDict => .exc (.typeError s!"~{t.nameStr}() takes a dict as second arg, if any")
  | _ =>
    let len := xs.length
    let lenErr : Option PyExc :=
      if minLen ≠ maxLen then
        if len < minLen then some (.typeError s!"~{t.nameStr}() takes an at least {minLen}-sequence ({len}-sequence given)")
        else if len > maxLen then some (.typeError s!"~{t.nameStr}() takes an at most {maxLen}-sequence ({len}-sequence given)")
        else none
      else if len ≠ minLen then some (.typeError s!"~{t.nameStr}() takes a {minLen}-sequence ({len}-sequence given)")
      else none
    match lenErr with
    | some e => .exc e
    | none =>
      let res ← pssNew (α := α) t malloc
      let slots ← newCopyLoop xs 0 res.slots
      match dict with
      | some (.dict look size0 size1) =>
        if size0 > 0 then do
          let (slots, found) ← newDictLoop t none_ look nUnnamed (maxLen - len) len slots 0
          if size1 > found then .exc (.typeError s!"~{t.nameStr}() got duplicate or unexpected field name(s)")
          else .ok { res with slots := slots }
        else do
          let slots ← newNoneLoop none_ (maxLen - len) len slots
          .ok { res with slots := slots }
      | _ => do
        let slots ← newNoneLoop none_ (maxLen - len) len slots
        .ok { res with slots := slots }

/-! ## Type creation: `count_members`, `initialize_members`, `_PyStructSequence_NewType` -/

/-- A `PyStructSequence_Field.name` before the `NULL` terminator: a C string, or the pointer
`PyStructSequence_UnnamedField`. The test at :474 and :553 compares pointers, so a field whose
name is the text `"unnamed field"` at another address is named. -/
inductive FName where
  | named (b : Bytes)
  | unnamed
  deriving DecidableEq, Repr

/-- `PyStructSequence_Desc`: the type name, the fields before the terminator, and the C `int`
`n_in_sequence`. -/
structure Desc where
  name : Bytes
  fields : List FName
  nInSeq : Int

/-- `count_members(desc, &n_unnamed)`, :468-479: walk to the terminator, counting the unnamed. -/
def countMembers (fs : List FName) : Nat × Nat :=
  fs.foldl (fun (i, u) f => (i + 1, if f = .unnamed then u + 1 else u)) (0, 0)

/-- The loop of `initialize_members`, :552-566: field `i` (with `k` members so far) becomes
member `k`, at the offset of slot `i`, unless it is unnamed. -/
def initMembersLoop : List FName → Nat → List Member → List Member
  | [], _, acc => acc
  | .unnamed :: fs, i, acc => initMembersLoop fs (i + 1) acc
  | .named b :: fs, i, acc => initMembersLoop fs (i + 1) (acc ++ [{ name := b, slot := i }])

/-- `initialize_members(desc, n_members, n_unnamed)`, :539-570: `PyMem_NEW` of
`n_members - n_unnamed + 1` entries (`MemoryError` if it fails), then the loop over the
`n_members` fields. -/
def initializeMembers (fs : List FName) (nMembers nUnnamed : Nat) (malloc : Nat → Bool) :
    CRes (List Member) :=
  if !malloc ((nMembers - nUnnamed + 1) * 40) then .exc memoryError
  else .ok (initMembersLoop (fs.take nMembers) 0 [])

/-- C's `(int)` conversion of a `size_t` value on the two's-complement targets CPython supports. -/
def toCInt (x : Int) : Int :=
  let m := x % 2 ^ 32
  if m ≥ 2 ^ 31 then m - 2 ^ 32 else m

/-- The member names `PyType_FromMetaclass` treats as special offsets (typeobject.c:5443-5451),
in the order it checks them (:5651-5665). -/
def specialNames : List String := ["__weaklistoffset__", "__dictoffset__", "__vectorcalloffset__"]

/-- `special_offset_from_member` (Objects/typeobject.c:5272-5297) for the members of a struct
sequence: they are `_Py_T_OBJECT`, so a member under one of the special names is refused with
`SystemError`. The first special name (in check order) that some member has decides. -/
def specialCheck (ms : List Member) : Option PyExc :=
  match specialNames.find? (fun s => ms.any (·.name == lit s)) with
  | some s => some (systemError s!"type of {s} must be Py_T_PYSSIZET")
  | none => none

/-- What `PyType_FromSpecWithBases(&spec, &PyTuple_Type)` does with `spec.basicsize` and the
members: `> 0` is used (Objects/typeobject.c:5339-5341); `< 0` asks for that much room on top of
tuple (:5342-5344), which tuple, a variable-size base without `Py_TPFLAGS_ITEMS_AT_END`, refuses
(:5629-5643); `0` inherits tuple's 32 (:5645-5648); then the special offsets are computed from
the members named `__weaklistoffset__`, `__dictoffset__`, `__vectorcalloffset__` (:5649-5665,
`specialCheck`); and `check_basicsize_includes_size_and_offsets` refuses a basicsize below the
base's (:5207-5212, called at :5781). Every other check and allocation it does before is `rest`,
an arbitrary outcome. Returns `tp_basicsize`. -/
def fromSpecBasicsize (name : Bytes) (ms : List Member) (basicsize : Int) (rest : Py Unit) : CRes Nat :=
  match rest with
  | .error e => .exc e
  | .ok () =>
    if basicsize < 0 then
      .exc (systemError "Cannot extend variable-size class without Py_TPFLAGS_ITEMS_AT_END.")
    else
      let bs := if basicsize = 0 then 32 else basicsize.toNat
      match specialCheck ms with
      | some e => .exc e
      | none =>
        if bs < 32 then
          .exc (.typeError s!"~tp_basicsize for type '{String.ofList (name.map Char.ofNat)}' ({bs}) is too small for base 'tuple' (32)")
        else .ok bs

/-- The `__match_args__` loop of `initialize_structseq_dict`, :510-520: for `i < n_in_sequence`,
the decoded names of the named fields. The terminator (index `fields.length`) has a `NULL`
name, which is not `PyStructSequence_UnnamedField`, so `PyUnicode_FromString(NULL)` crashes;
past it is out of bounds. -/
def matchArgsLoop (fs : List FName) : Nat → Nat → CRes (List Str)
  | 0, _ => .ok []
  | fuel + 1, i => do
    let here ← if h : i < fs.length then
        match fs[i] with
        | .unnamed => pure none
        | .named b => do
          let s ← CRes.ofPy (utf8Decode b .strict)
          pure (some s)
      else .ub "initialize_structseq_dict: field past the terminator"
    let rest ← matchArgsLoop fs fuel (i + 1)
    .ok (match here with | some s => s :: rest | none => rest)

/-- The dict holding three honest sizes. -/
def honestDict (nSeq nFields nUnnamed : Int) : TDict := fun key =>
  if key = "n_sequence_fields" then .ok (some (.int nSeq))
  else if key = "n_fields" then .ok (some (.int nFields))
  else if key = "n_unnamed_fields" then .ok (some (.int nUnnamed))
  else .ok none

/-- `initialize_structseq_dict(desc, dict, n_members, n_unnamed)`, :481-537: the three sizes
(:499-501), then `__match_args__` from `PyTuple_New(n_in_sequence)` (:505-508), whose negative
size is `SystemError` (`PyTuple_New`, Objects/tupleobject.c:75-81, then `tuple_alloc`, :39-42). Returns the size dict and
`__match_args__`. -/
def initDict (d : Desc) (nMembers nUnnamed : Nat) : CRes (TDict × List Str) := do
  if d.nInSeq < 0 then .exc (systemError "~Objects/tupleobject.c:40: bad argument to internal function")
  else
    let ma ← matchArgsLoop d.fields d.nInSeq.toNat 0
    .ok (honestDict d.nInSeq nMembers nUnnamed, ma)

/-- A type built from a `Desc`, and its `__match_args__`. -/
structure Built where
  type : CType
  matchArgs : List Str

/-- `_PyStructSequence_NewType(desc, tp_flags)`, :744-793 (and `PyStructSequence_NewType`,
:796-800, which passes no flags): count the fields, build `tp_members`, compute
`spec.basicsize = (int)(sizeof(PyStructSequence) + (hidden - 1) * sizeof(PyObject *))` with
`hidden = n_members - n_in_sequence` (:774-775), build the type, then its dict. -/
def newType (d : Desc) (malloc : Nat → Bool) (rest : Py Unit) : CRes Built := do
  let (n, u) := countMembers d.fields
  let ms ← initializeMembers d.fields n u malloc
  let hidden : Int := (n : Int) - d.nInSeq
  let bs ← fromSpecBasicsize d.name ms (toCInt (40 + (hidden - 1) * 8)) rest
  let (dict, ma) ← initDict d n u
  .ok { type := { name := d.name, members := ms, basicsize := bs, dict := dict }, matchArgs := ma }

end PyLean.TypeObj.StructSeq
