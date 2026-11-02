import PyLean.Pickle.Basic

/-!
Python values that the picklers see, with object identity.

Pickling memoizes by `id(obj)`, so the model's values carry an object id
(`Oid`) on every node the picklers memoize (str, bytes, bytearray, tuple,
list, dict, set, frozenset). Ints, bools and None are never memoized.

Ids of objects the picklers create themselves (`save_reduce` argument tuples,
the Latin-1 `str` for a protocol 0-2 `bytes`, the `bytes` copy of a
`bytearray`, the list of a `set`) are `Oid.tmp`, except where CPython returns
a cached singleton: `str(b, 'latin1')` of a one-byte `bytes` is the cached
one-character str (`Oid.str1`). User objects that are cached one-byte bytes
are `Oid.bytes1`. The differential test labels user objects the same way, from
their real `id()`.

Type invariant (not enforced by the type): equal ids label identical nodes.
Recursive (cyclic) structures cannot be represented.
-/

namespace PyLean.Pickle

/-- The callables the picklers reference for protocol < 3 `bytes`, protocol < 5
`bytearray` and protocol < 4 `set`/`frozenset`. -/
inductive Glob where
  | codecsEncode
  | bytes
  | bytearray
  | set
  | frozenset
  deriving Repr, DecidableEq, Inhabited

/-- `obj.__module__` as `whichmodule` reports it. -/
def Glob.module : Glob → String
  | .codecsEncode => "_codecs"
  | _ => "builtins"

/-- `obj.__qualname__`. -/
def Glob.name : Glob → String
  | .codecsEncode => "encode"
  | .bytes => "bytes"
  | .bytearray => "bytearray"
  | .set => "set"
  | .frozenset => "frozenset"

inductive Oid where
  /-- A user object, numbered by the harness from `id()`. -/
  | u (n : Nat)
  /-- CPython's cached one-character Latin-1 `str`. -/
  | str1 (c : Nat)
  /-- CPython's cached one-byte `bytes`. -/
  | bytes1 (b : Nat)
  /-- The `'latin1'` argument of `codecs.encode`. -/
  | latin1
  | glob (g : Glob)
  /-- The `k`-th temporary created while pickling `base`. -/
  | tmp (base : Oid) (k : Nat)
  deriving Repr, DecidableEq, Inhabited

inductive PV where
  | none
  | bool (b : Bool)
  | int (i : Int)
  | str (o : Oid) (s : List Nat)
  | bytes (o : Oid) (b : Bytes)
  | bytearray (o : Oid) (b : Bytes)
  | tuple (o : Oid) (xs : List PV)
  | list (o : Oid) (xs : List PV)
  | dict (o : Oid) (kvs : List (PV × PV))
  | set (o : Oid) (xs : List PV)
  | frozenset (o : Oid) (xs : List PV)
  deriving Repr, Inhabited

/-- The id of the `str` CPython returns for `str(b, 'latin1')` of a `bytes`
object `o` (one byte: the cached character). -/
def latin1StrOid (o : Oid) (b : Bytes) : Oid :=
  match b with
  | [c] => .str1 c.toNat
  | _ => .tmp o 1

/-- The id of `bytes(ba)` for a `bytearray` `o`: a new object, except that one
byte is the cached `bytes`. `_PyBytes_FromBuffer`
(`Objects/bytesobject.c:2958-2979`) copies into a `PyBytesWriter`, whose
`PyBytesWriter_FinishWithSize` (:3865-3923) ends a short result in
`PyBytes_FromStringAndSize(small_buffer, size)`, which returns the cached
object for size 1. -/
def bytesCopyOid (o : Oid) (b : Bytes) : Oid :=
  match b with
  | [c] => .bytes1 c.toNat
  | _ => .tmp o 1

end PyLean.Pickle
