import PyLean.PyIO.Basic

/-!
A raw stream with scripted behaviour for the buffered classes: a subclass of
`RawIOBase` holding contents and a position. It is a fallible, re-entrant Python
object:

* `readinto`, `write`, `seek`, `tell` follow scripts that force short counts,
  `None` (would block), arbitrary int answers (out of range, or in range without
  touching the buffer), a `str` answer, and exceptions;
* the `closed` attribute is a property with its own script (honest, a lie, or an
  exception);
* `hooks` re-enter the buffered object: at the start of the raw callback number
  `n` (counting `readinto`, `write`, `seek`, `tell`, `truncate`, `flush`,
  `close`, `isatty` and reads of `closed`) the raw calls the buffered object's
  operation `op` and logs its outcome, then goes on with its own behaviour.

With exhausted scripts the stream behaves like a file. Both twins share this
model; the buffered layer (`BufC.lean`, `BufPy.lean`) performs the logging and
the re-entry, since only it can run an operation of the buffered object.
-/

namespace PyLean.PyIO

open PyLean

/-- A state-and-exception computation: the shape of a C or Python method body. -/
def SM (σ α : Type) := σ → σ × Py α

instance {σ : Type} : Monad (SM σ) where
  pure a := fun s => (s, .ok a)
  bind m f := fun s =>
    match m s with
    | (s', .ok a) => f a s'
    | (s', .error e) => (s', .error e)

namespace SM
variable {σ α : Type}
def thr (e : PyExc) : SM σ α := fun s => (s, .error e)
def get : SM σ σ := fun s => (s, .ok s)
def put (s : σ) : SM σ Unit := fun _ => (s, .ok ())
def mod (f : σ → σ) : SM σ Unit := fun s => (f s, .ok ())
/-- Run `m`, handing its outcome to the caller even when it raised. -/
def attempt (m : SM σ α) : SM σ (Py α) := fun s => let (s', r) := m s; (s', .ok r)
end SM

/-- The operations on a buffered object (both twins). -/
inductive BfOp where
  | read (n : Option Int) | read1 (n : Int) | peek (n : Int)
  | readinto (n : Nat) | readinto1 (n : Nat)
  | readline (n : Option Int) | next
  | write (b : List Nat)
  | seek (p w : Int) | tell | truncate (n : Option Int)
  | flush | close | detach | closed
  | readable | writable | seekable | isatty | fileno | name | mode | getstate
  /-- `obj.__init__(raw, size)` again, with the same raw stream. -/
  | reinit (size : Int)
  deriving Repr, DecidableEq, Inhabited

/-- One answer of `readinto` or `write`. -/
inductive RStep where
  /-- Behave honestly, moving at most `k` bytes. -/
  | short (k : Nat)
  /-- Return `None` (would block). -/
  | block
  /-- Return the int `v` without touching the buffer. -/
  | bad (v : Int)
  /-- Return the `str` `'x'`. -/
  | wrong
  /-- Raise `c(m)`, or `c(errno, m)` when `eno` is set (then `str(e)` is `[Errno eno] m`).
  `mro` names the classes of `type(e).__mro__`: the class carries its place in the
  hierarchy, so a statement over every `mro` holds for every class hierarchy. -/
  | raise (c m : String) (eno : Option Nat) (mro : List String)
  deriving Repr, DecidableEq, Inhabited

/-- One answer of `readable()`, `writable()` or `seekable()`. -/
inductive QStep where
  /-- The raw's own flag, as a `bool`. -/
  | ok
  /-- The `int` `v` (truthy unless 0, never `is True`). -/
  | int (v : Int)
  | raise (c m : String)
  deriving Repr, DecidableEq, Inhabited

/-- What an inquiry answers. -/
inductive QAns where
  | bool (b : Bool)
  | int (v : Int)
  deriving Repr, DecidableEq, Inhabited

def QAns.truthy : QAns → Bool
  | .bool b => b
  | .int v => v != 0

def QAns.val : QAns → Val
  | .bool b => .bool b
  | .int v => .int v

/-- One answer of `seek` or `tell`. -/
inductive SStep where
  | ok
  | bad (v : Int)
  | wrong
  /-- Raise `c(m)`; `mro` names the classes of `type(e).__mro__`. -/
  | raise (c m : String) (mro : List String)
  deriving Repr, DecidableEq, Inhabited

/-- One read of the `closed` property. -/
inductive CStep where
  /-- The raw's own flag. -/
  | ok
  | lie (b : Bool)
  | raise (c m : String)
  deriving Repr, DecidableEq, Inhabited

/-- An entry of the raw's call log. `re r` is the outcome of a re-entered call. -/
inductive RCall where
  | readinto (n : Int)
  | write (b : List Nat)
  | seek (p w : Int)
  | tell
  | truncate (p : Option Int)
  | flush
  | close
  | closed
  | isatty
  | readable
  | writable
  | seekable
  | re (r : Py Val)
  deriving Repr, DecidableEq, Inhabited

structure Raw where
  data : List Nat
  pos : Nat
  rs : List RStep
  ws : List RStep
  ss : List SStep
  /-- The MRO of the exception the last `seek` or `tell` raised. -/
  excMro : List String
  cs : List CStep
  /-- Answers of `readable()`, `writable()`, `seekable()`, in call order. -/
  qs : List QStep
  /-- What `flush()` returns (`None` when absent). -/
  flushRet : Option Int
  canRead : Bool
  canWrite : Bool
  canSeek : Bool
  closed : Bool
  /-- `close()` raises this once, before closing. -/
  closeFail : Option (String × String)
  /-- `(n, op)`: callback number `n` first re-enters the buffered object with `op`. -/
  hooks : List (Nat × BfOp)
  /-- Callbacks so far. -/
  tick : Nat
  log : List RCall
  deriving Repr, DecidableEq, Inhabited

/-- What `readinto` or `write` answers. -/
inductive RRes where
  /-- `readinto` stored these bytes and returned their count. -/
  | data (b : List Nat)
  /-- `write` returned this count. -/
  | count (n : Nat)
  | none
  /-- An int answer that did not move any byte. -/
  | bad (v : Int)
  /-- The `str` `'x'`. -/
  | wrong
  /-- An exception, its `errno` (`None` when it has none) and the names of its MRO. -/
  | exc (e : PyExc) (eno : Option Nat) (mro : List String)
  deriving Repr, DecidableEq, Inhabited

/-- `str(c(errno, m))` is `[Errno errno] m`; `str(c(m))` is `m`. -/
def errMsg (m : String) : Option Nat → String
  | some n => s!"[Errno {n}] {m}"
  | none => m

/-- What `seek` or `tell` answers. -/
inductive IRes where
  | int (v : Int)
  | wrong
  deriving Repr, DecidableEq, Inhabited

def rawClosedErr : PyExc := .valueError "raw closed"
def valueErrorMro : List String := ["ValueError", "Exception", "BaseException", "object"]
def closedFileErr : PyExc := .valueError "I/O operation on closed file."
/-- `'x' < 0` in Python. -/
def strLtErr (op : String) : PyExc := .typeError s!"'{op}' not supported between instances of 'str' and 'int'"
/-- `PyNumber_AsSsize_t`/`PyNumber_AsOff_t` on `'x'`. -/
def strIndexErr : PyExc := .typeError "'str' object cannot be interpreted as an integer"

namespace Raw

/-- The start of a callback: log `c`, count it, and find the hook it fires. -/
def enter (r : Raw) (c : RCall) : Raw × Option BfOp :=
  let t := r.tick + 1
  ({ r with tick := t, log := r.log ++ [c] }, (r.hooks.find? (·.1 = t)).map (·.2))

def note (r : Raw) (v : Py Val) : Raw := { r with log := r.log ++ [RCall.re v] }

/-- `readinto(b)` with `len(b) = len`. -/
def readinto (r : Raw) (len : Nat) : Raw × RRes :=
  if r.closed then (r, .exc rawClosedErr none valueErrorMro) else
  let take (r : Raw) (k : Nat) : Raw × RRes :=
    let d := (r.data.drop r.pos).take (min k len)
    ({ r with pos := r.pos + d.length }, .data d)
  match r.rs with
  | [] => take r len
  | .short k :: t => take { r with rs := t } k
  | .block :: t => ({ r with rs := t }, .none)
  | .bad v :: t => ({ r with rs := t }, .bad v)
  | .wrong :: t => ({ r with rs := t }, .wrong)
  | .raise c m e mro :: t => ({ r with rs := t }, .exc (.named c (errMsg m e)) e mro)

/-- `write(b)`. -/
def write (r : Raw) (b : List Nat) : Raw × RRes :=
  if r.closed then (r, .exc rawClosedErr none valueErrorMro) else
  let put (r : Raw) (k : Nat) : Raw × RRes :=
    let d := b.take k
    -- as the harness raw: a zero-length write does not pad up to a position past the end
    ({ r with data := if d = [] then r.data else writeAt r.data r.pos d, pos := r.pos + d.length },
     .count d.length)
  match r.ws with
  | [] => put r b.length
  | .short k :: t => put { r with ws := t } k
  | .block :: t => ({ r with ws := t }, .none)
  | .bad v :: t => ({ r with ws := t }, .bad v)
  | .wrong :: t => ({ r with ws := t }, .wrong)
  | .raise c m e mro :: t => ({ r with ws := t }, .exc (.named c (errMsg m e)) e mro)

def popS (r : Raw) : Raw × SStep :=
  match r.ss with
  | [] => (r, .ok)
  | s :: t => ({ r with ss := t }, s)

/-- `seek(p, w)`. -/
def seek (r : Raw) (p w : Int) : Raw × Py IRes :=
  if r.closed then (r, .error rawClosedErr) else
  let (r, st) := r.popS
  match st with
  | .raise c m mro => ({ r with excMro := mro }, .error (.named c m))
  | .bad v => (r, .ok (.int v))
  | .wrong => (r, .ok .wrong)
  | .ok =>
    if !r.canSeek then (r, .error (osError "unseekable")) else
    let n : Int :=
      if w = 0 then p else if w = 1 then r.pos + p else if w = 2 then r.data.length + p else -1
    if n < 0 then (r, .error (.valueError "bad seek")) else
    ({ r with pos := n.toNat }, .ok (.int n))

/-- `tell()`. -/
def tell (r : Raw) : Raw × Py IRes :=
  if r.closed then (r, .error rawClosedErr) else
  let (r, st) := r.popS
  match st with
  | .raise c m mro => ({ r with excMro := mro }, .error (.named c m))
  | .bad v => (r, .ok (.int v))
  | .wrong => (r, .ok .wrong)
  | .ok => if !r.canSeek then (r, .error (osError "unseekable")) else (r, .ok (.int r.pos))

/-- `truncate(p)` (`None` is the current position). -/
def truncate (r : Raw) (p : Option Int) : Raw × Py Int :=
  if r.closed then (r, .error rawClosedErr) else
  let n : Int := p.getD r.pos
  if n < 0 then (r, .error (.valueError "bad truncate")) else
  -- the bound of the harness raw: never build the zeros of a huge scripted position
  if n > 2 ^ 24 then (r, .error (.overflowError "too big")) else
  let d := (r.data ++ List.replicate (n.toNat - r.data.length) 0).take n.toNat
  ({ r with data := d }, .ok n)

/-- `flush()`: what it returns is scripted. -/
def flush (r : Raw) : Raw × Py Val :=
  if r.closed then (r, .error closedFileErr) else
  (r, .ok (match r.flushRet with | some v => .int v | none => .none))

/-- `readable()`, `writable()` or `seekable()`, whose flag is `flag`. -/
def inquire (r : Raw) (flag : Bool) : Raw × Py QAns :=
  match r.qs with
  | [] => (r, .ok (.bool flag))
  | .ok :: t => ({ r with qs := t }, .ok (.bool flag))
  | .int v :: t => ({ r with qs := t }, .ok (.int v))
  | .raise c m :: t => ({ r with qs := t }, .error (.named c m))

/-- `close()`. -/
def close (r : Raw) : Raw × Py Unit :=
  match r.closeFail with
  | some (c, m) => ({ r with closeFail := none }, .error (.named c m))
  | none => ({ r with closed := true }, .ok ())

/-- `isatty()`. -/
def isatty (r : Raw) : Raw × Py Bool :=
  if r.closed then (r, .error closedFileErr) else (r, .ok false)

/-- A read of the `closed` property. -/
def closedAttr (r : Raw) : Raw × Py Bool :=
  match r.cs with
  | [] => (r, .ok r.closed)
  | .ok :: t => ({ r with cs := t }, .ok r.closed)
  | .lie b :: t => ({ r with cs := t }, .ok b)
  | .raise c m :: t => ({ r with cs := t }, .error (.named c m))

end Raw

/-- Outcome of the whole test case: the process died, or hung. -/
def crashErr : PyExc := .named "SIGSEGV" ""
def hangErr : PyExc := .named "Deadlock" ""
/-- Outcome of the whole test case: C undefined behaviour. Not `crashErr`: the
process may die or go on with corrupted memory, so no result is claimed. -/
def ubErr : PyExc := .named "UndefinedBehaviour" ""

end PyLean.PyIO
