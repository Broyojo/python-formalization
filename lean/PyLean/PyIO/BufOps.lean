import PyLean.PyIO.BufC
import PyLean.PyIO.BufPy
import PyLean.PyIO.BytesIO

/-! The operations on a buffered object and their dispatch in both twins. -/

namespace PyLean.PyIO

open PyLean SM

inductive BfOp where
  | read (n : Option Int) | read1 (n : Int) | peek (n : Int)
  | readinto (n : Nat) | readinto1 (n : Nat)
  | readline (n : Option Int) | next
  | write (b : List Nat)
  | seek (p w : Int) | tell | truncate (n : Option Int)
  | flush | close | detach | closed
  | readable | writable | seekable | isatty | fileno | name | mode | getstate
  deriving Repr, DecidableEq, Inhabited

def BC2.className (s : BufS) : String :=
  if !s.readable then "BufferedWriter" else if !s.writable then "BufferedReader" else "BufferedRandom"

def BP2.className (s : BufP) : String :=
  if s.kind = 0 then "BufferedReader" else if s.kind = 1 then "BufferedWriter" else "BufferedRandom"

def noRawAttr (a : String) : PyExc := .named "AttributeError" s!"'Raw' object has no attribute '{a}'"

namespace BC2

/-- Run `m` and return its value or exception, keeping the state. -/
def lift (m : BM Val) : BufS → BufS × Py Val := m

def wrapArg {α : Type} (a : Py α) (f : α → BM Val) : BM Val :=
  match a with
  | .error e => thr e
  | .ok v => f v

/-- `buffered_iternext`, bufferedio.c:1486-1526 (exact types only). -/
def iternext : BM Val := do
  checkInit
  let l ← readlineRaw (-1)
  if l = [] then thr .stopIteration else pure (.bytes l)

/-- The forwarding properties and methods, bufferedio.c:631-719, :532-537. -/
def stepOp (s : BufS) : BfOp → BufS × Py Val
  | .read n => (wrapArg (optSsize (-1) n) read) s
  | .read1 n => (wrapArg (argSsize n) read1) s
  | .peek n => (wrapArg (argSsize n) (fun _ => peek)) s
  | .readinto n => (readinto n false) s
  | .readinto1 n => (readinto n true) s
  | .readline n =>
    (wrapArg (optSsize (-1) n) (fun l => do
      checkInit
      let r ← readlineRaw l
      pure (.bytes r))) s
  | .next => iternext s
  | .write b => (write b) s
  | .seek p w => (wrapArg (argCInt w) (seek p)) s
  | .tell => tell s
  | .truncate n => (truncate n) s
  | .flush => flush s
  | .close => close s
  | .detach => detach s
  | .closed => (do checkInit; let s ← SM.get; pure (.bool s.raw.closed)) s
  | .readable => (do checkInit; let s ← SM.get; pure (.bool s.raw.canRead)) s
  | .writable => (do checkInit; let s ← SM.get; pure (.bool s.raw.canWrite)) s
  | .seekable => (do checkInit; let s ← SM.get; pure (.bool s.raw.canSeek)) s
  | .isatty => (do
      checkInit
      let s ← SM.get
      if s.raw.closed then thr closedRaw else pure (.bool false)) s
  | .fileno => (do checkInit; thr (unsupportedOp "fileno")) s
  | .name => (do checkInit; thr (noRawAttr "name")) s
  | .mode => (do checkInit; thr (noRawAttr "mode")) s
  | .getstate => (.error (.typeError s!"cannot pickle '{className s}' instances") : Py Val) |> fun r => (s, r)
where
  closedRaw : PyExc := .valueError "I/O operation on closed file."

end BC2

namespace BP2

def opt (r : Option (List Nat)) : Val := match r with
  | some d => .bytes d
  | none => .none

/-- `IOBase.__next__` over the buffered `readline`. -/
def next : PM Val := do
  let l ← readlineRaw none
  if l = [] then thr .stopIteration else pure (.bytes l)

def stepOp (s : BufP) : BfOp → BufP × Py Val
  | .read n => (read n) s
  | .read1 n => (read1 n) s
  | .peek n => (peek n) s
  | .readinto n => (readinto n false) s
  | .readinto1 n => (readinto n true) s
  | .readline n => (do let r ← readlineRaw n; pure (.bytes r)) s
  | .next => next s
  | .write b => (write b) s
  | .seek p w => (seek p w) s
  | .tell => tell s
  | .truncate n => (truncate n) s
  | .flush => flush s
  | .close => close s
  | .detach => detach s
  | .closed => (s, .ok (.bool s.raw.closed))
  -- `BufferedWriter` has no `readable`, `BufferedReader` no `writable`: IOBase's False
  | .readable => (s, .ok (.bool (s.kind ≠ 1 && s.raw.canRead)))
  | .writable => (s, .ok (.bool (s.kind ≠ 0 && s.raw.canWrite)))
  | .seekable => (s, .ok (.bool s.raw.canSeek))
  | .isatty =>
    if s.raw.closed then (s, .error (.valueError "I/O operation on closed file.")) else (s, .ok (.bool false))
  | .fileno => (s, .error (unsupportedOp "Raw.fileno() not supported"))
  | .name => (s, .error (noRawAttr "name"))
  | .mode => (s, .error (noRawAttr "mode"))
  | .getstate => (s, .error (.typeError s!"cannot pickle '{className s}' object"))

end BP2

end PyLean.PyIO
