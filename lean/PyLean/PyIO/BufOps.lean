import PyLean.PyIO.BufC
import PyLean.PyIO.BufPy
import PyLean.PyIO.BytesIO

/-! The operations on a buffered object and their dispatch in both twins, with
re-entry: a hook in the raw runs an operation through `stepC`/`stepP` at one
less fuel. -/

namespace PyLean.PyIO

open PyLean

def BP2.className (s : BufP) : String :=
  if s.kind = 0 then "BufferedReader" else if s.kind = 1 then "BufferedWriter" else "BufferedRandom"

def noRawAttr (a : String) : PyExc := .named "AttributeError" s!"'Raw' object has no attribute '{a}'"

namespace BC2

def wrapArg {α : Type} (a : Py α) (f : α → BM Val) : BM Val :=
  match a with
  | .error e => thr e
  | .ok v => f v

/-- `bufferediobase_unsupported`, bufferedio.c:113-118. -/
def bufferediobaseUnsupported (msg : String) : BM Val := thr (unsupportedOp msg)

/-- `_bufferediobase_readinto_generic` (bufferedio.c:50-83) of a `BufferedWriter`,
through `_io__BufferedIOBase_readinto_impl`/`readinto1_impl` (:92-111): it calls
`self.read(len)` or `self.read1(len)`, which a writer inherits from
`_BufferedIOBase` (:165-195), so the call raises before any type or length check. -/
def bufferediobaseReadinto (len : Nat) (one : Bool) : BM Val := do
  let _ ← wrapArg (argCInt len) (fun _ => bufferediobaseUnsupported (if one then "read1" else "read"))
  pure (Val.int 0)

/-- `buffered_iternext`, bufferedio.c:1497-1538 (exact types only). -/
def iternext : BM Val := do
  checkInit
  let l ← readlineRaw (-1)
  if l = [] then thr .stopIteration else pure (Val.bytes l)

/-- The methods and properties of the three types (bufferedio.c:2550-2749). -/
def stepOp (op : BfOp) : BM Val := do
  let s ← get
  match op with
  | .read n =>
    -- a writer inherits `_io__BufferedIOBase_read_impl`, bufferedio.c:165-172, whose
    -- unused `int` argument is still converted (clinic/bufferedio.c.h:162-165)
    if !s.readable then
      match n with
      | none => thr (.typeError "'NoneType' object cannot be interpreted as an integer")
      | some v => wrapArg (argCInt v) (fun _ => bufferediobaseUnsupported "read")
    else
    wrapArg (optSsize (-1) n) read
  | .read1 n =>
    -- a writer inherits `_io__BufferedIOBase_read1_impl`, bufferedio.c:188-195
    -- (clinic/bufferedio.c.h:217-220)
    if !s.readable then wrapArg (argCInt n) (fun _ => bufferediobaseUnsupported "read1") else
    wrapArg (argSsize n) read1
  | .peek n =>
    if !s.readable then
      thr (.named "AttributeError" "'_io.BufferedWriter' object has no attribute 'peek'") else
    wrapArg (argSsize n) (fun _ => peek)
  -- a writer inherits `_io__BufferedIOBase_readinto_impl` (:92-97, :106-111), whose
  -- `_bufferediobase_readinto_generic` (:50-83) calls `self.read`/`self.read1`
  | .readinto n => if !s.readable then bufferediobaseReadinto n false else readinto n false
  | .readinto1 n => if !s.readable then bufferediobaseReadinto n true else readinto n true
  | .readline n =>
    -- a writer inherits `_io__IOBase_readline_impl` (Modules/_io/iobase.c:568-677):
    -- with no `peek`, it calls `self.read(1)` unless the limit is 0
    if !s.readable then wrapArg (optSsize (-1) n) (fun l =>
      if l = 0 then pure (Val.bytes []) else bufferediobaseUnsupported "read") else
    -- `_io__Buffered_readline_impl`, bufferedio.c:1320-1326
    wrapArg (optSsize (-1) n) (fun l => do
      checkInit
      let r ← readlineRaw l
      pure (Val.bytes r))
  | .next => iternext
  | .write b =>
    if !s.writable then thr (unsupportedOp "write") else
    write b
  | .seek p w => wrapArg (argCInt w) (seek p)
  | .tell => tell
  | .truncate n => truncate n
  | .flush => flushMethod
  | .close => close
  | .detach => do
    detach
  | .closed => do
    -- `_io__Buffered_closed_get_impl`, bufferedio.c:540-546
    checkInit
    let r ← onRaw .closed Raw.closedAttr
    let b ← ofPy r
    pure (Val.bool b)
  -- bufferedio.c:652-670 forwards to the raw, but only the types that list the
  -- method do: a reader has no `writable` and a writer no `readable`, so those
  -- are `_IOBase`'s False. The harness raw answers from flags init checked.
  | .readable => if !s.readable then pure (Val.bool false) else do checkInit; pure (Val.bool true)
  | .writable => if !s.writable then pure (Val.bool false) else do checkInit; pure (Val.bool true)
  | .seekable => do checkInit; let b ← rawFlag Raw.canSeek; pure (Val.bool b)
  | .isatty => do
    -- `_io__Buffered_isatty_impl`, bufferedio.c:722-728
    checkInit
    let r ← onRaw .isatty Raw.isatty
    let b ← ofPy r
    pure (Val.bool b)
  | .fileno => do checkInit; thr (unsupportedOp "fileno")
  | .name => do checkInit; thr (noRawAttr "name")
  | .mode => do checkInit; thr (noRawAttr "mode")
  | .getstate => thr (.typeError s!"cannot pickle '{className s}' instances")

end BC2

/-- An operation of the C object with `fuel` levels of re-entry. -/
def stepC : Nat → BfOp → SM BufS Val
  | 0 => fun _ s => (s, .error .modelFuel)
  | fuel + 1 => fun op s => BC2.stepOp op (stepC fuel) s

namespace BP2

/-- `IOBase.__next__` over the buffered `readline`, _pyio.py:559-563. -/
def next : PM Val := do
  let l ← readlineRaw none
  if l = [] then thr .stopIteration else pure (Val.bytes l)

def stepOp (op : BfOp) : PM Val := do
  let s ← get
  match op with
  -- `BufferedIOBase.read`/`write` raise through `_unsupported` where the kind has
  -- no override, and only `BufferedReader` defines `peek`
  | .read n =>
    if s.kind = 1 then thr (unsupportedOp "BufferedWriter.read() not supported") else
    read n
  | .read1 n =>
    if s.kind = 1 then thr (unsupportedOp "BufferedWriter.read1() not supported") else
    read1 n
  | .peek n =>
    if s.kind = 1 then
      thr (.named "AttributeError" "'BufferedWriter' object has no attribute 'peek'") else
    peek n
  -- a writer inherits `BufferedIOBase.readinto(1)` (:702-740), which calls
  -- `self.read`/`self.read1`, and `IOBase.readline` (:513-553), which has no `peek`
  -- and calls `self.read(1)` unless `size` is 0
  | .readinto n =>
    if s.kind = 1 then thr (unsupportedOp "BufferedWriter.read() not supported") else readinto n false
  | .readinto1 n =>
    if s.kind = 1 then thr (unsupportedOp "BufferedWriter.read1() not supported") else readinto n true
  | .readline n =>
    if s.kind = 1 then
      if n = some 0 then pure (Val.bytes []) else thr (unsupportedOp "BufferedWriter.read() not supported")
    else do let r ← readlineRaw n; pure (Val.bytes r)
  | .next => next
  | .write b =>
    if s.kind = 0 then thr (unsupportedOp "BufferedReader.write() not supported") else
    write b
  | .seek p w => seek p w
  | .tell => tell
  | .truncate n => truncate n
  | .flush => flush
  | .close => close
  | .detach => detach
  | .closed => do let b ← closed; pure (Val.bool b)
  -- `BufferedWriter` has no `readable`, `BufferedReader` no `writable`: IOBase's False
  | .readable =>
    if s.kind = 1 then pure (Val.bool false) else do
    let b ← rawFlag "readable" Raw.canRead; pure (Val.bool b)
  | .writable =>
    if s.kind = 0 then pure (Val.bool false) else do
    let b ← rawFlag "writable" Raw.canWrite; pure (Val.bool b)
  | .seekable => do let b ← rawFlag "seekable" Raw.canSeek; pure (Val.bool b)
  | .isatty => do
    let r ← onRaw "isatty" .isatty Raw.isatty
    let b ← ofPy r
    pure (Val.bool b)
  | .fileno =>
    if s.detached then thr (noneAttr "fileno") else thr (unsupportedOp "Raw.fileno() not supported")
  | .name => if s.detached then thr (noneAttr "name") else thr (noRawAttr "name")
  | .mode => if s.detached then thr (noneAttr "mode") else thr (noRawAttr "mode")
  | .getstate => thr (.typeError s!"cannot pickle '{className s}' object")

end BP2

/-- An operation of the Python object with `fuel` levels of re-entry. -/
def stepP : Nat → BfOp → SM BufP Val
  | 0 => fun _ s => (s, .error .modelFuel)
  | fuel + 1 => fun op s => BP2.stepOp op (stepP fuel) s

/-! ## A whole test case -/

/-- How a case ends: the results so far, or a crash or hang that stopped it. -/
inductive Outcome (σ : Type) where
  | done (s : σ) (rs : List (Py Val))
  | crashed
  | hung
  | initErr (e : PyExc)

/-- Run the operations in turn, stopping when the process dies or hangs. -/
def runSeq {σ : Type} (step : BfOp → SM σ Val) (stop : σ → Bool) : σ → List BfOp → Option (σ × List (Py Val))
  | s, [] => some (s, [])
  | s, o :: os =>
    let (s', r) := step o s
    if stop s' then none else
    match runSeq step stop s' os with
    | none => none
    | some (s'', rs) => some (s'', r :: rs)

def reFuel (r : Raw) : Nat := r.hooks.length + 2

/-- `io.Buffered*(raw, size)` then the operations. -/
def runC (kind : Nat) (raw : Raw) (size : Int) (ops : List BfOp) : Outcome BufS :=
  let s0 : BufS := default
  match BC2.init kind raw size (stepC (reFuel raw)) s0 with
  | (s, .error e) => if s.crashed then .crashed else .initErr e
  | (s, .ok _) =>
    match runSeq (stepC (reFuel raw + 1)) (·.crashed) s ops with
    | none => .crashed
    | some (s, rs) => .done s rs

/-- `_pyio.Buffered*(raw, size)` then the operations. -/
def runP (kind : Nat) (raw : Raw) (size : Int) (ops : List BfOp) : Outcome BufP :=
  match BP2.init kind raw size with
  | .error e => .initErr e
  | .ok s =>
    match runSeq (stepP (reFuel raw + 1)) (·.hung) s ops with
    | none => .hung
    | some (s, rs) => .done s rs

end PyLean.PyIO
