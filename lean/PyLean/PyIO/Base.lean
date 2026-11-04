import PyLean.PyIO.Basic

/-!
The abstract bases over a scripted subclass: `_io._IOBase`, `_io._RawIOBase`
(`Modules/_io/iobase.c`), `_io._BufferedIOBase` (`Modules/_io/bufferedio.c:51-220`),
`_io._TextIOBase` (`Modules/_io/textio.c:49-185`) and `IOBase`, `RawIOBase`,
`BufferedIOBase`, `TextIOBase` in `Lib/_pyio.py`.

The stream is a user subclass whose overridden methods replay a script
(`UObj`): each call of `read`, `peek`, `readinto`, `write` or `flush` takes
the next `Ret`, and every call is logged, so the argument the base class passes
is observable. An exhausted script answers `b''`, `b''`, `0`, `None`, and
`flush` falls through to the base class. `InterruptedError` is raised with
`errno == EINTR`. The class may also override `seek` (a script of `Ret`), the
inquiries `seekable`/`readable`/`writable` (one shared script of `IRet`, any object or
an exception, `False` when exhausted) and the `closed` property (one fixed `IRet`).
-/

namespace PyLean.PyIO

open PyLean

/-- What a scripted user method does. -/
inductive Ret where
  | bytes (b : List Nat)
  | none
  | int (n : Int)
  | raise (cls msg : String)
  deriving Repr, DecidableEq, Inhabited

def Ret.typeName : Ret → String
  | .bytes _ => "bytes"
  | .none => "NoneType"
  | .int _ => "int"
  | .raise _ _ => ""

/-- What an overridden `seekable()`, `readable()`, `writable()` or `closed` answers: a
bool, an int, `None`, or an exception. -/
inductive IRet where
  | bool (b : Bool)
  | int (n : Int)
  | none
  | raise (cls msg : String)
  deriving Repr, DecidableEq, Inhabited

/-- `PyObject_IsTrue` (C) and `bool()` (Python) of an answer that did not raise. -/
def IRet.truthy : IRet → Bool
  | .bool b => b
  | .int n => n != 0
  | .none => false
  | .raise _ _ => false

/-- The answer as a returned value. -/
def IRet.val : IRet → Val
  | .bool b => .bool b
  | .int n => .int n
  | .none => .none
  | .raise _ _ => .none

/-- A logged call of a user method. -/
inductive Call where
  | read (n : Int) | peek (n : Int) | readinto (n : Int) | write (b : List Nat) | flush | read1 (n : Int)
  | seek (pos whence : Int) | inquiry (name : String)
  deriving Repr, DecidableEq, Inhabited

structure UObj where
  /-- `type(self).__name__`, used by `_pyio._unsupported`. -/
  name : String
  reads : List Ret
  /-- `none`: the class has no `peek` attribute. -/
  peeks : Option (List Ret)
  /-- `readinto(b)`: bytes copied into `b` and the return value. -/
  intos : List (List Nat × Ret)
  writes : List Ret
  flushes : List Ret
  /-- `read` is not overridden: `RawIOBase.read` runs over `readinto`. -/
  rawRead : Bool
  isClosed : Bool
  log : List Call
  /-- `readinto` keeps a `memoryview` of the buffer it was given. -/
  keepView : Bool
  /-- `none`: `seek` is not overridden. -/
  seeks : Option (List Ret) := none
  /-- `none`: `seekable`, `readable` and `writable` are not overridden. -/
  inqs : Option (List IRet) := none
  /-- `none`: `closed` is the base class's property. -/
  closedProp : Option IRet := none
  deriving Repr, DecidableEq, Inhabited

def excOf (cls msg : String) : PyExc := .named cls msg

def unsup (m : String) : PyExc := unsupportedOp m

def UObj.callRead (u : UObj) (n : Int) : UObj × Ret :=
  let u := { u with log := u.log ++ [Call.read n] }
  match u.reads with
  | [] => (u, .bytes [])
  | r :: rs => ({ u with reads := rs }, r)

def UObj.callRead1 (u : UObj) (n : Int) : UObj × Ret :=
  let u := { u with log := u.log ++ [Call.read1 n] }
  match u.reads with
  | [] => (u, .bytes [])
  | r :: rs => ({ u with reads := rs }, r)

def UObj.callPeek (u : UObj) (n : Int) : UObj × Ret :=
  let u := { u with log := u.log ++ [Call.peek n] }
  match u.peeks with
  | some (r :: rs) => ({ u with peeks := some rs }, r)
  | _ => (u, .bytes [])

def UObj.callInto (u : UObj) (n : Int) : UObj × (List Nat × Ret) :=
  let u := { u with log := u.log ++ [Call.readinto n] }
  match u.intos with
  | [] => (u, ([], .int 0))
  | r :: rs => ({ u with intos := rs }, r)

/-- `self.seek(p, w)` of an overriding class; an exhausted script answers `0`. -/
def UObj.callSeek (u : UObj) (p w : Int) (rs : List Ret) : UObj × Ret :=
  let u := { u with log := u.log ++ [Call.seek p w] }
  match rs with
  | [] => (u, .int 0)
  | r :: rs => ({ u with seeks := some rs }, r)

/-- `self.seekable()`, `self.readable()` or `self.writable()`: the base methods return
`False` (iobase.c:410, :442, :475; _pyio.py:428, :442, :456); an overriding
class answers from its script. -/
def UObj.callInq (u : UObj) (name : String) : UObj × IRet :=
  match u.inqs with
  | none => (u, .bool false)
  | some rs =>
    let u := { u with log := u.log ++ [Call.inquiry name] }
    match rs with
    | [] => (u, .bool false)
    | r :: rs => ({ u with inqs := some rs }, r)

/-- Reading `self.closed`: the base property reports the flag (`iobase_closed_get`,
iobase.c:188-195; `IOBase.closed`, _pyio.py:466-471), or the class's property answers. -/
def UObj.readClosed (u : UObj) : IRet :=
  match u.closedProp with
  | none => .bool u.isClosed
  | some r => r

def UObj.callWrite (u : UObj) (b : List Nat) : UObj × Ret :=
  let u := { u with log := u.log ++ [Call.write b] }
  match u.writes with
  | [] => (u, .none)
  | r :: rs => ({ u with writes := rs }, r)

/-- Index of the first `\n`, `(readahead.find(b"\n") + 1) or len(readahead)`. -/
def nlPrefix (b : List Nat) : Nat :=
  match findIdx? b 10 with
  | some i => i + 1
  | none => b.length

/-- The scripted operations. `checkClosed msg` etc. call `_checkClosed()` or, with
`some m`, `_checkClosed(m)`; `writelines ls stop` iterates over `ls`, and then the
iterator raises `stop` if it is `some (cls, msg)`. -/
inductive UOp where
  | seek | tell | truncate | flush | close | closed | seekable | readable | writable
  | checkClosed (msg : Option String) | checkSeekable (msg : Option String)
  | checkReadable (msg : Option String) | checkWritable (msg : Option String)
  | enter | exit | fileno | isatty
  | readline (n : Option Int) | iter | next | readlines (h : Option Int)
  | writelines (ls : List (List Nat)) (stop : Option (String × String)) | del
  | rawRead (n : Option Int) | rawReadall | rawReadinto | rawWrite
  | bRead | bRead1 | bReadinto (n : Nat) | bReadinto1 (n : Nat) | bWrite | bDetach
  | tRead | tReadline | tWrite | tTruncate | tDetach | tEncoding | tNewlines | tErrors
  deriving Repr, DecidableEq, Inhabited

def closedDotE : PyExc := .valueError "I/O operation on closed file."
def bufSize : Nat := 131072

namespace BC

/-- `_PyIO_trap_eintr`, bufferedio.c:878-901, for a scripted exception of this model's
harness, where `InterruptedError` is always raised as `InterruptedError(EINTR, ...)` and no
other scripted class has an `errno`. The real test is "an `OSError` instance whose `errno`
is `EINTR`", whatever the class (see `BC2.trapEintr` for the buffered layer); this table
is exact only for the classes this harness raises, and no property here relies on it. -/
def trapEintr (cls : String) : Bool := cls == "InterruptedError"

/-- `_io__IOBase_flush_impl`, iobase.c:172-185, after the script. -/
def flush (u : UObj) : UObj × Py Val :=
  let u' := { u with log := u.log ++ [Call.flush] }
  match u.flushes with
  | r :: rs =>
    let u' := { u' with flushes := rs }
    match r with
    | .raise c m => (u', .error (excOf c m))
    | _ => (u', .ok .none)
  | [] => if u.isClosed then (u', .error closedDotE) else (u', .ok .none)

/-- `_io__IOBase_close_impl`, iobase.c:270-291. -/
def close (u : UObj) : UObj × Py Val :=
  if u.isClosed then (u, .ok .none) else
  let (u', r) := flush u
  ({ u' with isClosed := true }, r.map (fun _ => .none))

/-- `iobase_check_closed`, iobase.c:197-214: the derived `closed` attribute, looked up
with `PyObject_GetOptionalAttr` (so an `AttributeError` means open), then
`PyObject_IsTrue`. -/
def checkClosed (u : UObj) : Py Unit :=
  match u.readClosed with
  | .raise "AttributeError" _ => .ok ()
  | .raise c m => .error (excOf c m)
  | r => if r.truthy then .error closedDotE else .ok ()

/-- `METH_NOARGS` (iobase.c:845-848) refuses an argument before the function runs. -/
def noArgs (name : String) : PyExc := .typeError s!"_IOBase.{name}() takes no arguments (1 given)"

/-- `_PyIOBase_check_seekable` / `_readable` / `_writable`, iobase.c:414-428, :457-471,
:480-494: call the method, propagate its exception, and accept only the object `True`
(`res != Py_True`), which is returned. -/
def checkInq (u : UObj) (name msg : String) : UObj × Py Val :=
  match u.callInq name with
  | (u, .raise c m) => (u, .error (excOf c m))
  | (u, .bool true) => (u, .ok (.bool true))
  | (u, _) => (u, .error (unsup msg))

/-- `_io__RawIOBase_read_impl`, iobase.c:923-961, for `n >= 0`: `PyByteArray_Resize`
(:953) and `take_bytes` (:956) each refuse while a view of the bytearray is alive. -/
def rawReadN (u : UObj) (n : Nat) : UObj × Py Val :=
  match u.callInto n with
  | (u, (_, .raise c m)) => (u, .error (excOf c m))
  | (u, (_, .none)) => (u, .ok .none)
  | (u, (d, .int k)) =>
    if !InSsize k then (u, .error (.valueError "cannot fit 'int' into an index-sized integer"))
    else if k < 0 ∨ k > n then
      (u, .error (.valueError s!"readinto returned {k} outside buffer size {n}"))
    else if u.keepView then (u, .error bufferError)
    else (u, .ok (.bytes ((d.take n ++ List.replicate (n - (d.take n).length) 0).take k.toNat)))
  | (u, (_, .bytes _)) =>
    (u, .error (.typeError "'bytes' object cannot be interpreted as an integer"))

def readCall (u : UObj) (n : Nat) : UObj × Ret :=
  if u.rawRead then
    match rawReadN u n with
    | (u, .error (.named c m)) => (u, .raise c m)
    | (u, .error (.valueError m)) => (u, .raise "ValueError" m)
    | (u, .error (.typeError m)) => (u, .raise "TypeError" m)
    | (u, .error _) => (u, .raise "ValueError" "")
    | (u, .ok .none) => (u, .none)
    | (u, .ok v) => (u, .bytes v.bytesOf)
  else u.callRead n

/-- The `do` loop of `_io__IOBase_readline_impl`, iobase.c:613-618. -/
def scanNl (remaining : Int) (n : Nat) : List Nat → Nat
  | [] => n
  | x :: xs => if (n : Int) ≥ remaining then n else if x = 10 then n + 1 else scanNl remaining (n + 1) xs

/-- The peek step of `_io__IOBase_readline_impl`, iobase.c:582-630, with `len` bytes
already in `buffer`: `remaining = limit - len`, iobase.c:612. -/
def readahead (limit : Int) (len : Nat) (r : List Nat) : Nat :=
  if r.length > 0 then
    if limit ≥ 0 then scanNl (limit - len) 0 r
    else nlPrefix r
  else 1

/-- The loop of `_io__IOBase_readline_impl`, iobase.c:577-645. -/
def readlineLoop (limit : Int) : UObj → List Nat → Nat → UObj × Py (List Nat)
  | u, _, 0 => (u, .error .modelFuel)
  | u, res, fuel + 1 =>
    if limit < 0 ∨ (res.length : Int) < limit then
      let pk : UObj × Py (Option Nat) :=
        if u.peeks.isSome then
          match u.callPeek 1 with
          | (u, .bytes r) => (u, .ok (some (readahead limit res.length r)))
          | (u, .raise c m) =>
            if trapEintr c then (u, .ok none) else (u, .error (excOf c m))
          | (u, r) => (u, .error (osError s!"peek() should have returned a bytes object, not '{r.typeName}'"))
        else (u, .ok (some 1))
      match pk with
      | (u, .error e) => (u, .error e)
      | (u, .ok none) => readlineLoop limit u res fuel
      | (u, .ok (some nread)) =>
        match readCall u nread with
        | (u, .raise c m) =>
          if trapEintr c then readlineLoop limit u res fuel else (u, .error (excOf c m))
        | (u, .bytes b) =>
          if b = [] then (u, .ok res) else
          let res := res ++ b
          if res.getLast? = some 10 then (u, .ok res) else readlineLoop limit u res fuel
        | (u, r) => (u, .error (osError s!"read() should have returned a bytes object, not '{r.typeName}'"))
    else (u, .ok res)

def fuelOf (u : UObj) : Nat := u.reads.length + u.intos.length + (u.peeks.getD []).length + 2

/-- `_io__IOBase_readline_impl`, iobase.c:569-677. -/
def readline (u : UObj) (limit : Option Int) : UObj × Py Val :=
  match optSsize (-1) limit with
  | .error e => (u, .error e)
  | .ok limit =>
    match readlineLoop limit u [] (fuelOf u) with
    | (u, .error e) => (u, .error e)
    | (u, .ok r) => (u, .ok (.bytes r))

/-- `iobase_iternext`, iobase.c:689-703. -/
def next (u : UObj) : UObj × Py Val :=
  match readline u none with
  | (u, .error e) => (u, .error e)
  | (u, .ok v) => if v.bytesOf = [] then (u, .error .stopIteration) else (u, .ok v)

/-- The loop of `_io__IOBase_readlines_impl`, iobase.c:746-769. -/
def readlinesLoop (hint : Int) : UObj → Int → List Atom → Nat → UObj × Py Val
  | u, _, _, 0 => (u, .error .modelFuel)
  | u, length, acc, fuel + 1 =>
    match next u with
    | (u, .error .stopIteration) => (u, .ok (.list acc.reverse))
    | (u, .error e) => (u, .error e)
    | (u, .ok v) =>
      let l := v.bytesOf
      let acc := Atom.bytes l :: acc
      if hint > 0 ∧ (l.length : Int) > hint - length then (u, .ok (.list acc.reverse))
      else readlinesLoop hint u (length + l.length) acc fuel

/-- `_io__IOBase_readlines_impl`, iobase.c:718-778, with `iobase_iter`
(:680-686). -/
def readlines (u : UObj) (hint : Option Int) : UObj × Py Val :=
  match optSsize (-1) hint with
  | .error e => (u, .error e)
  | .ok hint =>
    match checkClosed u with
    | .error e => (u, .error e)
    | .ok () => readlinesLoop hint u 0 [] (fuelOf u)

/-- The loop of `_io__IOBase_writelines`, iobase.c:804-824: `PyIter_Next` raising
`stop` at the end of the lines returns `NULL` (:806-811). -/
def writelinesLoop (stop : Option (String × String)) : UObj → List (List Nat) → Nat → UObj × Py Val
  | u, _, 0 => (u, .error .modelFuel)
  | u, [], _ =>
    match stop with
    | some (c, m) => (u, .error (excOf c m))
    | none => (u, .ok .none)
  | u, l :: ls, fuel + 1 =>
    match u.callWrite l with
    | (u, .raise c m) =>
      if trapEintr c then writelinesLoop stop u (l :: ls) fuel else (u, .error (excOf c m))
    | (u, _) => writelinesLoop stop u ls fuel

/-- The loop of `_io__RawIOBase_readall_impl`, iobase.c:971-1020. -/
def readallLoop : UObj → List Nat → Bool → Nat → UObj × Py Val
  | u, _, _, 0 => (u, .error .modelFuel)
  | u, acc, any, fuel + 1 =>
    match readCall u bufSize with
    | (u, .raise c m) =>
      if trapEintr c then readallLoop u acc any fuel else (u, .error (excOf c m))
    | (u, .none) => if !any then (u, .ok .none) else (u, .ok (.bytes acc))
    | (u, .int _) => (u, .error (.typeError "read() should return bytes"))
    | (u, .bytes d) =>
      if d = [] then (u, .ok (.bytes acc)) else readallLoop u (acc ++ d) true fuel

/-- `_bufferediobase_readinto_generic`, bufferedio.c:51-83, with a buffer of
`n` bytes `0xff`; returns `[count, buffer]`. -/
def bReadinto (u : UObj) (n : Nat) (one : Bool) : UObj × Py Val :=
  match if one then u.callRead1 n else u.callRead n with
  | (u, .raise c m) => (u, .error (excOf c m))
  | (u, .bytes d) =>
    if d.length > n then
      (u, .error (.valueError s!"read() returned too much data: {n} bytes requested, {d.length} returned"))
    else (u, .ok (.list [.int d.length, .bytes (d ++ List.replicate (n - d.length) 255)]))
  | (u, _) => (u, .error (.typeError "read() should return bytes"))

/-- `self.closed`, `self.seekable()` and the like, as a returned value. -/
def answer (u : UObj) (r : IRet) : UObj × Py Val :=
  match r with
  | .raise c m => (u, .error (excOf c m))
  | r => (u, .ok r.val)

/-- What an overriding `seek` returned, as a value. -/
def seekAnswer (p : UObj × Ret) : UObj × Py Val :=
  match p with
  | (u, .raise c m) => (u, .error (excOf c m))
  | (u, .bytes b) => (u, .ok (.bytes b))
  | (u, .none) => (u, .ok .none)
  | (u, .int n) => (u, .ok (.int n))

/-- `_io__IOBase_tell_impl`, iobase.c:134-138: `self.seek(0, 1)` through the method
table; the base `seek` raises (iobase.c:119-125), an overriding one answers. -/
def tell (u : UObj) : UObj × Py Val :=
  match u.seeks with
  | none => (u, .error (unsup "seek"))
  | some rs => seekAnswer (u.callSeek 0 1 rs)

def step (u : UObj) : UOp → UObj × Py Val
  | .seek => (u, .error (unsup "seek"))
  | .tell => tell u
  | .truncate => (u, .error (unsup "truncate"))
  | .flush => flush u
  | .close => close u
  | .closed => answer u u.readClosed
  | .seekable => let (u, r) := u.callInq "seekable"; answer u r
  | .readable => let (u, r) := u.callInq "readable"; answer u r
  | .writable => let (u, r) := u.callInq "writable"; answer u r
  -- `_PyIOBase_check_closed`, iobase.c:217-226
  | .checkClosed (some _) => (u, .error (noArgs "_checkClosed"))
  | .checkClosed none =>
    match checkClosed u with
    | .error e => (u, .error e)
    | .ok () => (u, .ok .none)
  | .checkSeekable (some _) => (u, .error (noArgs "_checkSeekable"))
  | .checkSeekable none => checkInq u "seekable" "File or stream is not seekable."
  | .checkReadable (some _) => (u, .error (noArgs "_checkReadable"))
  | .checkReadable none => checkInq u "readable" "File or stream is not readable."
  | .checkWritable (some _) => (u, .error (noArgs "_checkWritable"))
  | .checkWritable none => checkInq u "writable" "File or stream is not writable."
  -- `iobase_enter`, iobase.c:499-505, returns `self`, encoded as `None`
  | .enter =>
    match checkClosed u with
    | .error e => (u, .error e)
    | .ok () => (u, .ok .none)
  | .exit => close u
  | .fileno => (u, .error (unsup "fileno"))
  -- `_io__IOBase_isatty_impl`, iobase.c:544-550
  | .isatty =>
    match checkClosed u with
    | .error e => (u, .error e)
    | .ok () => (u, .ok (.bool false))
  | .readline n => readline u n
  -- `iobase_iter`, iobase.c:680-686, returns `self`, encoded as `None`
  | .iter =>
    match checkClosed u with
    | .error e => (u, .error e)
    | .ok () => (u, .ok .none)
  | .next => next u
  | .readlines h => readlines u h
  | .writelines ls stop =>
    match checkClosed u with
    | .error e => (u, .error e)
    | .ok () => writelinesLoop stop u ls (ls.length + u.writes.length + 1)
  | .del =>
    -- iobase_finalize, iobase.c:296-333: a `closed` that is missing or raises means
    -- "do nothing", and errors of close() are unraisable
    match u.readClosed with
    | .raise _ _ => (u, .ok .none)
    | r => if r.truthy then (u, .ok .none) else let (u, _) := close u; (u, .ok .none)
  | .rawRead n =>
    let n := n.getD (-1)
    if !InSsize n then (u, .error (.overflowError "Python int too large to convert to C ssize_t"))
    else if n < 0 then readallLoop u [] false (u.intos.length + u.reads.length + 2)
    else
      -- `PyByteArray_FromStringAndSize` makes a `bytes`, Objects/bytearrayobject.c:195
      match allocBytes n with
      | .error e => (u, .error e)
      | .ok () => rawReadN u n.toNat
  | .rawReadall => readallLoop u [] false (u.intos.length + u.reads.length + 2)
  | .rawReadinto => (u, .error (.named "NotImplementedError" ""))
  | .rawWrite => (u, .error (.named "NotImplementedError" ""))
  | .bRead => (u, .error (unsup "read"))
  | .bRead1 => (u, .error (unsup "read1"))
  | .bReadinto n => bReadinto u n false
  | .bReadinto1 n => bReadinto u n true
  | .bWrite => (u, .error (unsup "write"))
  | .bDetach => (u, .error (unsup "detach"))
  | .tRead => (u, .error (unsup "read"))
  | .tReadline => (u, .error (unsup "readline"))
  | .tWrite => (u, .error (unsup "write"))
  | .tTruncate => (u, .error (unsup "truncate"))
  | .tDetach => (u, .error (unsup "detach"))
  | .tEncoding | .tNewlines | .tErrors => (u, .ok .none)

end BC

namespace BP

/-- `_unsupported`, _pyio.py:341-344. -/
def unsupported (u : UObj) (name : String) : PyExc := pyUnsupported u.name name

/-- `IOBase._checkClosed(msg)`, _pyio.py:473-478: `if self.closed:` reads the property
(which may raise, `AttributeError` included) and tests its truth. -/
def checkClosed (u : UObj) (msg : Option String) : Py Unit :=
  match u.readClosed with
  | .raise c m => .error (excOf c m)
  | r => if r.truthy then .error (.valueError (msg.getD "I/O operation on closed file.")) else .ok ()

/-- `IOBase._checkSeekable` / `_checkReadable` / `_checkWritable`, _pyio.py:430-435,
:444-449, :458-463: `if not self.seekable():`, the default message or `msg`; `None` on
success. -/
def checkInq (u : UObj) (name dflt : String) (msg : Option String) : UObj × Py Val :=
  match u.callInq name with
  | (u, .raise c m) => (u, .error (excOf c m))
  | (u, r) => if r.truthy then (u, .ok .none) else (u, .error (unsup (msg.getD dflt)))

/-- `IOBase.flush`, _pyio.py:380-385 (`self._checkClosed()`), after the script. -/
def flush (u : UObj) : UObj × Py Val :=
  let u' := { u with log := u.log ++ [Call.flush] }
  match u.flushes with
  | r :: rs =>
    let u' := { u' with flushes := rs }
    match r with
    | .raise c m => (u', .error (excOf c m))
    | _ => (u', .ok .none)
  | [] =>
    match checkClosed u none with
    | .error e => (u', .error e)
    | .ok () => (u', .ok .none)

/-- `IOBase.close`, _pyio.py:390-399. -/
def close (u : UObj) : UObj × Py Val :=
  if u.isClosed then (u, .ok .none) else
  let (u', r) := flush u
  ({ u' with isClosed := true }, r.map (fun _ => .none))

/-- `RawIOBase.read`, _pyio.py:610-627, for `size >= 0`: `del b[n:]` and
`b.take_bytes()` each refuse while a view of `b` is alive. -/
def rawReadN (u : UObj) (n : Nat) : UObj × Py Val :=
  match u.callInto n with
  | (u, (_, .raise c m)) => (u, .error (excOf c m))
  | (u, (_, .none)) => (u, .ok .none)
  | (u, (d, .int k)) =>
    if k < 0 ∨ k > n then
      (u, .error (.valueError s!"readinto returned {k} outside buffer size {n}"))
    else if u.keepView then (u, .error bufferError)
    else (u, .ok (.bytes ((d.take n ++ List.replicate (n - (d.take n).length) 0).take k.toNat)))
  | (u, (_, .bytes _)) =>
    (u, .error (.typeError "'<' not supported between instances of 'bytes' and 'int'"))

def readCall (u : UObj) (n : Nat) : UObj × Ret :=
  if u.rawRead then
    match rawReadN u n with
    | (u, .error (.named c m)) => (u, .raise c m)
    | (u, .error (.valueError m)) => (u, .raise "ValueError" m)
    | (u, .error (.typeError m)) => (u, .raise "TypeError" m)
    | (u, .error _) => (u, .raise "ValueError" "")
    | (u, .ok .none) => (u, .none)
    | (u, .ok v) => (u, .bytes v.bytesOf)
  else u.callRead n

/-- `nreadahead` with `peek`, _pyio.py:525-532, with `len` bytes already in `res`. -/
def nreadahead (size : Int) (len : Nat) (r : Ret) : Py Nat :=
  match r with
  | .bytes [] | .none | .int 0 => .ok 1
  | .bytes b =>
    let n := nlPrefix b
    .ok (if size ≥ 0 then min n (size - len).toNat else n)
  | .int _ => .error (.named "AttributeError" "'int' object has no attribute 'find'")
  | .raise c m => .error (excOf c m)

/-- The loop of `IOBase.readline`, _pyio.py:546-553. -/
def readlineLoop (size : Int) : UObj → List Nat → Nat → UObj × Py (List Nat)
  | u, _, 0 => (u, .error .modelFuel)
  | u, res, fuel + 1 =>
    if size < 0 ∨ (res.length : Int) < size then
      let pk : UObj × Py Nat :=
        if u.peeks.isSome then
          let (u, r) := u.callPeek 1
          (u, nreadahead size res.length r)
        else (u, .ok 1)
      match pk with
      | (u, .error e) => (u, .error e)
      | (u, .ok nread) =>
        match readCall u nread with
        | (u, .raise c m) => (u, .error (excOf c m))
        | (u, .none) | (u, .int 0) | (u, .bytes []) => (u, .ok res)
        | (u, .int _) => (u, .error (.typeError "can't concat int to bytearray"))
        | (u, .bytes b) =>
          let res := res ++ b
          if res.getLast? = some 10 then (u, .ok res) else readlineLoop size u res fuel
    else (u, .ok res)

/-- `IOBase.readline`, _pyio.py:513-553. -/
def readline (u : UObj) (size : Option Int) : UObj × Py Val :=
  match readlineLoop (size.getD (-1)) u [] (BC.fuelOf u) with
  | (u, .error e) => (u, .error e)
  | (u, .ok r) => (u, .ok (.bytes r))

/-- `IOBase.__next__`, _pyio.py:559-563. -/
def next (u : UObj) : UObj × Py Val :=
  match readline u none with
  | (u, .error e) => (u, .error e)
  | (u, .ok v) => if v.bytesOf = [] then (u, .error .stopIteration) else (u, .ok v)

/-- `for line in self` of `IOBase.readlines`, _pyio.py:565-581. -/
def readlinesLoop (hint : Option Int) : UObj → Int → List Atom → Nat → UObj × Py Val
  | u, _, _, 0 => (u, .error .modelFuel)
  | u, n, acc, fuel + 1 =>
    match next u with
    | (u, .error .stopIteration) => (u, .ok (.list acc.reverse))
    | (u, .error e) => (u, .error e)
    | (u, .ok v) =>
      let l := v.bytesOf
      let acc := Atom.bytes l :: acc
      let n := n + l.length
      match hint with
      | some h => if n ≥ h then (u, .ok (.list acc.reverse)) else readlinesLoop hint u n acc fuel
      | none => readlinesLoop hint u n acc fuel

/-- `IOBase.readlines`, _pyio.py:565-581: `list(self)` and `for line in self` both start
with `__iter__` (:555-557), whose `_checkClosed()` reads `closed`. -/
def readlines (u : UObj) (hint : Option Int) : UObj × Py Val :=
  match checkClosed u none with
  | .error e => (u, .error e)
  | .ok () =>
  let hint := match hint with
    | some h => if h ≤ 0 then none else some h
    | none => none
  readlinesLoop hint u 0 [] (BC.fuelOf u)

/-- `for line in lines: self.write(line)`, _pyio.py:590-591: the first exception, from a
`write` or from the iterator (`stop`, raised after the lines), propagates. -/
def writelinesLoop (stop : Option (String × String)) : UObj → List (List Nat) → UObj × Py Val
  | u, [] =>
    match stop with
    | some (c, m) => (u, .error (excOf c m))
    | none => (u, .ok .none)
  | u, l :: ls =>
    match u.callWrite l with
    | (u, .raise c m) => (u, .error (excOf c m))
    | (u, _) => writelinesLoop stop u ls

/-- `RawIOBase.readall`, _pyio.py:629-638; `last` is the falsy `data`. -/
def readallLoop : UObj → List Nat → Nat → UObj × Py Val
  | u, _, 0 => (u, .error .modelFuel)
  | u, res, fuel + 1 =>
    match readCall u bufSize with
    | (u, .raise c m) => (u, .error (excOf c m))
    | (u, .none) => if res ≠ [] then (u, .ok (.bytes res)) else (u, .ok .none)
    | (u, .int 0) => if res ≠ [] then (u, .ok (.bytes res)) else (u, .ok (.int 0))
    | (u, .int _) => (u, .error (.typeError "can't concat int to bytearray"))
    | (u, .bytes d) =>
      if d = [] then (u, .ok (.bytes res)) else readallLoop u (res ++ d) fuel

/-- `BufferedIOBase._readinto`, _pyio.py:727-740, with a buffer of `n` bytes
`0xff`. A longer result does not fit the slice assignment. -/
def bReadinto (u : UObj) (n : Nat) (one : Bool) : UObj × Py Val :=
  match if one then u.callRead1 n else u.callRead n with
  | (u, .raise c m) => (u, .error (excOf c m))
  | (u, .bytes d) =>
    if d.length > n then
      (u, .error (.valueError "memoryview assignment: lvalue and rvalue have different structures"))
    else (u, .ok (.list [.int d.length, .bytes (d ++ List.replicate (n - d.length) 255)]))
  | (u, .none) => (u, .error (.typeError "object of type 'NoneType' has no len()"))
  | (u, .int _) => (u, .error (.typeError "object of type 'int' has no len()"))

/-- `IOBase.tell`, _pyio.py:366-368: `return self.seek(0, 1)`, through the object's own
`seek`: the base one is `self._unsupported("seek")` (:364). -/
def tell (u : UObj) : UObj × Py Val :=
  match u.seeks with
  | none => (u, .error (unsupported u "seek"))
  | some rs => BC.seekAnswer (u.callSeek 0 1 rs)

def step (u : UObj) : UOp → UObj × Py Val
  | .seek => (u, .error (unsupported u "seek"))
  | .tell => tell u
  | .truncate => (u, .error (unsupported u "truncate"))
  | .flush => flush u
  | .close => close u
  | .closed => BC.answer u u.readClosed
  | .seekable => let (u, r) := u.callInq "seekable"; BC.answer u r
  | .readable => let (u, r) := u.callInq "readable"; BC.answer u r
  | .writable => let (u, r) := u.callInq "writable"; BC.answer u r
  | .checkClosed msg =>
    match checkClosed u msg with
    | .error e => (u, .error e)
    | .ok () => (u, .ok .none)
  | .checkSeekable msg => checkInq u "seekable" "File or stream is not seekable." msg
  | .checkReadable msg => checkInq u "readable" "File or stream is not readable." msg
  | .checkWritable msg => checkInq u "writable" "File or stream is not writable." msg
  -- `IOBase.__enter__`, _pyio.py:482-485: `self._checkClosed(); return self`, and `self`
  -- is encoded as `None` (the difftest maps `f.__enter__() is f` to `None`)
  | .enter =>
    match checkClosed u none with
    | .error e => (u, .error e)
    | .ok () => (u, .ok .none)
  | .exit => close u
  | .fileno => (u, .error (unsupported u "fileno"))
  -- `IOBase.isatty`, _pyio.py:503-509
  | .isatty =>
    match checkClosed u none with
    | .error e => (u, .error e)
    | .ok () => (u, .ok (.bool false))
  | .readline n => readline u n
  -- `IOBase.__iter__`, _pyio.py:555-557: `return self`, encoded as `None` as for `__enter__`
  | .iter =>
    match checkClosed u none with
    | .error e => (u, .error e)
    | .ok () => (u, .ok .none)
  | .next => next u
  | .readlines h => readlines u h
  -- `IOBase.writelines`, _pyio.py:583-591
  | .writelines ls stop =>
    match checkClosed u none with
    | .error e => (u, .error e)
    | .ok () => writelinesLoop stop u ls
  | .del =>
    -- IOBase.__del__, _pyio.py:401-418: only an `AttributeError` from `closed` means
    -- "do nothing"; close() errors propagate from an explicit call
    match u.readClosed with
    | .raise "AttributeError" _ => (u, .ok .none)
    | .raise c m => (u, .error (excOf c m))
    | r => if r.truthy then (u, .ok .none) else close u
  | .rawRead n =>
    let n := n.getD (-1)
    if n < 0 then readallLoop u [] (u.intos.length + u.reads.length + 2)
    else if !InSsize n then (u, .error (.overflowError "cannot fit 'int' into an index-sized integer"))
    else if n ≥ memLimit then (u, .error memoryError)
    else rawReadN u n.toNat
  | .rawReadall => readallLoop u [] (u.intos.length + u.reads.length + 2)
  | .rawReadinto => (u, .error (unsupported u "readinto"))
  | .rawWrite => (u, .error (unsupported u "write"))
  | .bRead => (u, .error (unsupported u "read"))
  | .bRead1 => (u, .error (unsupported u "read1"))
  | .bReadinto n => bReadinto u n false
  | .bReadinto1 n => bReadinto u n true
  | .bWrite => (u, .error (unsupported u "write"))
  | .bDetach => (u, .error (unsupported u "detach"))
  | .tRead => (u, .error (unsupported u "read"))
  | .tReadline => (u, .error (unsupported u "readline"))
  | .tWrite => (u, .error (unsupported u "write"))
  | .tTruncate => (u, .error (unsupported u "truncate"))
  | .tDetach => (u, .error (unsupported u "detach"))
  | .tEncoding | .tNewlines | .tErrors => (u, .ok .none)

end BP

end PyLean.PyIO
