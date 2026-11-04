import PyLean.Core

/-!
Shared vocabulary for the in-memory I/O models (`Modules/_io/bytesio.c`,
`Modules/_io/stringio.c`, `Lib/_pyio.py`), CPython 3.15.2.

Conventions:

* Bytes are `List Nat` (each in `[0, 256)`), text is `List Nat` of code
  points (each in `[0, 0x110000)`, surrogates included), so that NUL and lone
  surrogates are ordinary elements.
* A test case is a constructor plus a list of operations; every operation
  returns a `Py Val`. Arguments are Python ints or `None` (`Option Int`).
* LP64: `Py_ssize_t` and `long` are 64-bit, `int` is 32-bit.
* Allocation: a request for `memLimit` (`2 ** 47`) or more bytes fails with
  `MemoryError`, as it must on x86-64, and smaller requests succeed. Real limits
  below it depend on the machine (the pod grants about `1.02e14`); the difftests
  only exercise sizes far below it or at least it.
-/

namespace PyLean.PyIO

open PyLean

/-- A scalar Python value. -/
inductive Atom where
  | none
  | int (i : Int)
  | bool (b : Bool)
  | bytes (b : List Nat)
  | str (s : List Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Values returned by operations: a scalar or a list (or tuple) of scalars. -/
inductive Val where
  | atom (a : Atom)
  | list (l : List Atom)
  deriving Repr, DecidableEq, Inhabited

@[match_pattern] def Val.none : Val := .atom .none
@[match_pattern] def Val.int (i : Int) : Val := .atom (.int i)
@[match_pattern] def Val.bool (b : Bool) : Val := .atom (.bool b)
@[match_pattern] def Val.bytes (b : List Nat) : Val := .atom (.bytes b)
@[match_pattern] def Val.str (s : List Nat) : Val := .atom (.str s)

/-- The contents of a `bytes` value (`[]` for anything else). -/
def Val.bytesOf : Val → List Nat
  | .bytes b => b
  | _ => []

/-- The text of a `str` value (`[]` for anything else). -/
def Val.strOf : Val → List Nat
  | .str l => l
  | _ => []

/-! ## Exceptions that are not in `PyExc` -/

def bufferError : PyExc := .named "BufferError" "Existing exports of data: object cannot be re-sized"
def memoryError : PyExc := .named "MemoryError" ""
def osError (m : String) : PyExc := .named "OSError" m
def unsupportedOp (m : String) : PyExc := .named "UnsupportedOperation" m
/-- `IOBase._unsupported(name)` on an instance of class `cls`, _pyio.py:341-344:
`"%s.%s() not supported" % (self.__class__.__name__, name)`. -/
def pyUnsupported (cls name : String) : PyExc := unsupportedOp s!"{cls}.{name}() not supported"
/-- `UnicodeDecodeError`; the message embeds byte values and positions. -/
def unicodeDecodeError : PyExc := .named "UnicodeDecodeError" "~utf-8 decode error"
/-- `UnicodeEncodeError` (a lone surrogate in a `newline` argument). -/
def unicodeEncodeError : PyExc := .named "UnicodeEncodeError" "~utf-8 encode error"

/-- Allocation bound (bytes), see the module docstring: `2 ** 47`, which no x86-64
Linux process can allocate (its user address space is 47 bits, part of it mapped). -/
def memLimit : Nat := 2 ^ 47

/-- `_PyBytes_FromSize`, Objects/bytesobject.c:101-105 and its allocation on LP64
(`PyBytesObject_SIZE` is 33): every path that makes a `bytes` of `n` bytes ends here. -/
def allocBytes (n : Int) : Py Unit :=
  if n > ssizeMax - 33 then .error (.overflowError "byte string is too large")
  else if n ≥ memLimit then .error memoryError
  else .ok ()

/-! ## C argument conversion (Argument Clinic), LP64 -/

def intMin : Int := -(2 ^ 31)
def intMax : Int := 2 ^ 31 - 1

def InSsize (v : Int) : Prop := ssizeMin ≤ v ∧ v ≤ ssizeMax
instance (v : Int) : Decidable (InSsize v) := inferInstanceAs (Decidable (_ ∧ _))

def InCInt (v : Int) : Prop := intMin ≤ v ∧ v ≤ intMax
instance (v : Int) : Decidable (InCInt v) := inferInstanceAs (Decidable (_ ∧ _))

/-- `Py_ssize_t(accept={int, NoneType})`: `_Py_convert_optional_to_ssize_t`
(Python/modsupport.c:15-35) calls `PyNumber_AsSsize_t(obj, PyExc_OverflowError)`
(Objects/abstract.c), whose message names the type. `None` keeps the default. -/
def optSsize (dflt : Int) : Option Int → Py Int
  | none => .ok dflt
  | some v => if InSsize v then .ok v
      else .error (.overflowError "cannot fit 'int' into an index-sized integer")

/-- Plain `Py_ssize_t` converter: `PyLong_AsSsize_t`. -/
def argSsize (v : Int) : Py Int :=
  if InSsize v then .ok v else .error (.overflowError "Python int too large to convert to C ssize_t")

/-- `int` converter: `PyLong_AsInt`. -/
def argCInt (v : Int) : Py Int :=
  if InCInt v then .ok v else .error (.overflowError "Python int too large to convert to C int")

/-- `PyLong_AsLong` (LP64: same range as `Py_ssize_t`). -/
def asLong (v : Int) : Py Int :=
  if InSsize v then .ok v else .error (.overflowError "Python int too large to convert to C long")

/-! ## The argument of `truncate` as an arbitrary object -/

/-- One action of the `__index__` of an object passed to `truncate`, on the stream
being truncated. `__index__` swallows every `Exception` such an action raises. -/
inductive Hook where
  | close
  | getbuffer
  | tell
  /-- `seek(p)`. -/
  | seekAbs (p : Nat)
  /-- `seek(0, 1)`. -/
  | seekCur
  | write (b : List Nat)
  deriving Repr, DecidableEq, Inhabited

/-- The argument of `truncate` when it is not `None` or an `int`. -/
inductive TArg where
  /-- `__index__` runs `hook`, then returns `some v` or raises `ValueError('boom')`. -/
  | index (hook : List Hook) (v : Option Int)
  /-- An object with no `__index__`: its type name and `repr`. -/
  | noIndex (typeName repr : String)
  deriving Repr, DecidableEq, Inhabited

def boomErr : PyExc := .valueError "boom"

/-- `type(a).__name__` of a `TArg.index` object: the harness's class `Idx`
(difftest/pyio_diff.py), which `PyNumber_AsSsize_t` names when the result overflows. -/
def indexTypeName : String := "Idx"

/-- The argument of a binary `write` when it is not a bytes-like object: a `str`, or an
object of the named type without the buffer interface. -/
inductive WArg where
  | str (s : List Nat)
  | obj (typeName : String)
  deriving Repr, DecidableEq, Inhabited

def WArg.typeName : WArg → String
  | .str _ => "str"
  | .obj t => t

/-- `_PyNumber_Index` on an object with no `__index__`, Objects/abstract.c:1410-1424. -/
def notIndexable (typeName : String) : PyExc :=
  .typeError s!"'{typeName}' object cannot be interpreted as an integer"

/-! ## List helpers -/

/-- `buf[a:a+n]` for `a, n >= 0`. -/
def slice (buf : List Nat) (a n : Nat) : List Nat := (buf.drop a).take n

/-- Index of the first element equal to `c`, if any. -/
def findIdx? (l : List Nat) (c : Nat) : Option Nat :=
  match l with
  | [] => none
  | x :: xs => if x = c then some 0 else (findIdx? xs c).map (· + 1)

/-- `buf` with `b` written at position `pos`, zero-filling any gap:
the semantics both BytesIO twins and the C StringIO implement. -/
def writeAt (buf : List Nat) (pos : Nat) (b : List Nat) : List Nat :=
  (buf ++ List.replicate (pos - buf.length) 0).take pos ++ b ++ buf.drop (pos + b.length)

end PyLean.PyIO
