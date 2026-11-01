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
`errno == EINTR`.
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

/-- A logged call of a user method. -/
inductive Call where
  | read (n : Int) | peek (n : Int) | readinto (n : Int) | write (b : List Nat) | flush | read1 (n : Int)
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

/-- The scripted operations. -/
inductive UOp where
  | seek | tell | truncate | flush | close | closed | seekable | readable | writable
  | checkClosed | checkSeekable | checkReadable | checkWritable
  | enter | exit | fileno | isatty
  | readline (n : Option Int) | iter | next | readlines (h : Option Int)
  | writelines (ls : List (List Nat)) | del
  | rawRead (n : Option Int) | rawReadall | rawReadinto | rawWrite
  | bRead | bRead1 | bReadinto (n : Nat) | bReadinto1 (n : Nat) | bWrite | bDetach
  | tRead | tReadline | tWrite | tTruncate | tDetach | tEncoding | tNewlines | tErrors
  deriving Repr, DecidableEq, Inhabited

def closedDotE : PyExc := .valueError "I/O operation on closed file."
def bufSize : Nat := 131072

namespace BC

/-- `_PyIO_trap_eintr`, bufferedio.c:879-901, for a scripted exception. -/
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

/-- `_io__RawIOBase_read_impl`, iobase.c:923-961, for `n >= 0`. -/
def rawReadN (u : UObj) (n : Nat) : UObj × Py Val :=
  match u.callInto n with
  | (u, (_, .raise c m)) => (u, .error (excOf c m))
  | (u, (_, .none)) => (u, .ok .none)
  | (u, (d, .int k)) =>
    if !InSsize k then (u, .error (.valueError "cannot fit 'int' into an index-sized integer"))
    else if k < 0 ∨ k > n then
      (u, .error (.valueError s!"readinto returned {k} outside buffer size {n}"))
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

/-- The peek step of `_io__IOBase_readline_impl`, iobase.c:582-615. -/
def readahead (limit : Int) (r : List Nat) : Nat :=
  if r.length > 0 then
    if limit ≥ 0 then
      let rec go (n : Nat) (l : List Nat) : Nat :=
        match l with
        | [] => n
        | x :: xs => if (n : Int) ≥ limit then n else if x = 10 then n + 1 else go (n + 1) xs
      go 0 r
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
          | (u, .bytes r) => (u, .ok (some (readahead limit r)))
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
    if u.isClosed then (u, .error closedDotE) else
    readlinesLoop hint u 0 [] (fuelOf u)

/-- The loop of `_io__IOBase_writelines`, iobase.c:804-824. -/
def writelinesLoop : UObj → List (List Nat) → Nat → UObj × Py Val
  | u, _, 0 => (u, .error .modelFuel)
  | u, [], _ => (u, .ok .none)
  | u, l :: ls, fuel + 1 =>
    match u.callWrite l with
    | (u, .raise c m) =>
      if trapEintr c then writelinesLoop u (l :: ls) fuel else (u, .error (excOf c m))
    | (u, _) => writelinesLoop u ls fuel

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

def step (u : UObj) : UOp → UObj × Py Val
  | .seek => (u, .error (unsup "seek"))
  | .tell => (u, .error (unsup "seek"))
  | .truncate => (u, .error (unsup "truncate"))
  | .flush => flush u
  | .close => close u
  | .closed => (u, .ok (.bool u.isClosed))
  | .seekable | .readable | .writable => (u, .ok (.bool false))
  | .checkClosed => if u.isClosed then (u, .error closedDotE) else (u, .ok .none)
  | .checkSeekable => (u, .error (unsup "File or stream is not seekable."))
  | .checkReadable => (u, .error (unsup "File or stream is not readable."))
  | .checkWritable => (u, .error (unsup "File or stream is not writable."))
  | .enter => if u.isClosed then (u, .error closedDotE) else (u, .ok .none)
  | .exit => close u
  | .fileno => (u, .error (unsup "fileno"))
  | .isatty => if u.isClosed then (u, .error closedDotE) else (u, .ok (.bool false))
  | .readline n => readline u n
  | .iter => if u.isClosed then (u, .error closedDotE) else (u, .ok .none)
  | .next => next u
  | .readlines h => readlines u h
  | .writelines ls =>
    if u.isClosed then (u, .error closedDotE)
    else writelinesLoop u ls (ls.length + u.writes.length + 1)
  | .del =>
    -- iobase_finalize, iobase.c:296-333: errors of close() are unraisable
    if u.isClosed then (u, .ok .none) else let (u, _) := close u; (u, .ok .none)
  | .rawRead n =>
    let n := n.getD (-1)
    if !InSsize n then (u, .error (.overflowError "Python int too large to convert to C ssize_t"))
    else if n < 0 then readallLoop u [] false (u.intos.length + u.reads.length + 2)
    else if n ≥ memLimit then (u, .error memoryError)
    else rawReadN u n.toNat
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
def unsupported (u : UObj) (name : String) : PyExc := unsup s!"{u.name}.{name}() not supported"

/-- `IOBase.flush`, _pyio.py:380-385, after the script. -/
def flush (u : UObj) : UObj × Py Val :=
  let u' := { u with log := u.log ++ [Call.flush] }
  match u.flushes with
  | r :: rs =>
    let u' := { u' with flushes := rs }
    match r with
    | .raise c m => (u', .error (excOf c m))
    | _ => (u', .ok .none)
  | [] => if u.isClosed then (u', .error closedDotE) else (u', .ok .none)

/-- `IOBase.close`, _pyio.py:390-399. -/
def close (u : UObj) : UObj × Py Val :=
  if u.isClosed then (u, .ok .none) else
  let (u', r) := flush u
  ({ u' with isClosed := true }, r.map (fun _ => .none))

/-- `RawIOBase.read`, _pyio.py@3.14.7:610-627, for `size >= 0`. -/
def rawReadN (u : UObj) (n : Nat) : UObj × Py Val :=
  match u.callInto n with
  | (u, (_, .raise c m)) => (u, .error (excOf c m))
  | (u, (_, .none)) => (u, .ok .none)
  | (u, (d, .int k)) =>
    if k < 0 ∨ k > n then
      (u, .error (.valueError s!"readinto returned {k} outside buffer size {n}"))
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

/-- `nreadahead` with `peek`, _pyio.py:525-532. -/
def nreadahead (size : Int) (r : Ret) : Py Nat :=
  match r with
  | .bytes [] | .none | .int 0 => .ok 1
  | .bytes b =>
    let n := nlPrefix b
    .ok (if size ≥ 0 then min n size.toNat else n)
  | .int _ => .error (.named "AttributeError" "'int' object has no attribute 'find'")
  | .raise c m => .error (excOf c m)

/-- The loop of `IOBase.readline`, _pyio.py@3.14.7:546-553. -/
def readlineLoop (size : Int) : UObj → List Nat → Nat → UObj × Py (List Nat)
  | u, _, 0 => (u, .error .modelFuel)
  | u, res, fuel + 1 =>
    if size < 0 ∨ (res.length : Int) < size then
      let pk : UObj × Py Nat :=
        if u.peeks.isSome then
          let (u, r) := u.callPeek 1
          (u, nreadahead size r)
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

/-- `IOBase.readline`, _pyio.py@3.14.7:513-553. -/
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

def readlines (u : UObj) (hint : Option Int) : UObj × Py Val :=
  if u.isClosed then (u, .error closedDotE) else
  let hint := match hint with
    | some h => if h ≤ 0 then none else some h
    | none => none
  readlinesLoop hint u 0 [] (BC.fuelOf u)

/-- `IOBase.writelines`, _pyio.py:583-591. -/
def writelinesLoop : UObj → List (List Nat) → UObj × Py Val
  | u, [] => (u, .ok .none)
  | u, l :: ls =>
    match u.callWrite l with
    | (u, .raise c m) => (u, .error (excOf c m))
    | (u, _) => writelinesLoop u ls

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

def step (u : UObj) : UOp → UObj × Py Val
  | .seek => (u, .error (unsupported u "seek"))
  | .tell => (u, .error (unsupported u "seek"))
  | .truncate => (u, .error (unsupported u "truncate"))
  | .flush => flush u
  | .close => close u
  | .closed => (u, .ok (.bool u.isClosed))
  | .seekable | .readable | .writable => (u, .ok (.bool false))
  | .checkClosed => if u.isClosed then (u, .error closedDotE) else (u, .ok .none)
  | .checkSeekable => (u, .error (unsup "File or stream is not seekable."))
  | .checkReadable => (u, .error (unsup "File or stream is not readable."))
  | .checkWritable => (u, .error (unsup "File or stream is not writable."))
  | .enter => if u.isClosed then (u, .error closedDotE) else (u, .ok .none)
  | .exit => close u
  | .fileno => (u, .error (unsupported u "fileno"))
  | .isatty => if u.isClosed then (u, .error closedDotE) else (u, .ok (.bool false))
  | .readline n => readline u n
  | .iter => if u.isClosed then (u, .error closedDotE) else (u, .ok .none)
  | .next => next u
  | .readlines h => readlines u h
  | .writelines ls => if u.isClosed then (u, .error closedDotE) else writelinesLoop u ls
  | .del =>
    -- IOBase.__del__, _pyio.py:401-418: close() errors propagate from an explicit call
    if u.isClosed then (u, .ok .none) else close u
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
