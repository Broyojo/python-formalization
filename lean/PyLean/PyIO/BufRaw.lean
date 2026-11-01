import PyLean.PyIO.Basic

/-!
A raw stream with scripted behaviour for the buffered classes: a subclass of
`RawIOBase` holding contents and a position, where the `readinto`, `write`,
`seek` and `tell` scripts force short counts, `None` (would block), invalid
counts and exceptions. Every call is logged. With an exhausted script the
stream behaves like a file. Both twins share this model; only the inherited
`RawIOBase.read`/`readall` differ (`rawRead`, `rawReadall`).
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

inductive RStep where
  | short (k : Nat)
  | block
  | bad (v : Int)
  | raise (c m : String)
  deriving Repr, DecidableEq, Inhabited

inductive SStep where
  | ok
  | bad (v : Int)
  | raise (c m : String)
  deriving Repr, DecidableEq, Inhabited

inductive RCall where
  | readinto (n : Int)
  | write (b : List Nat)
  | seek (p w : Int)
  | tell
  | truncate (p : Option Int)
  | flush
  | close
  deriving Repr, DecidableEq, Inhabited

structure Raw where
  data : List Nat
  pos : Nat
  rs : List RStep
  ws : List RStep
  ss : List SStep
  canRead : Bool
  canWrite : Bool
  canSeek : Bool
  closed : Bool
  /-- `close()` raises this once, before closing. -/
  closeFail : Option (String × String)
  log : List RCall
  deriving Repr, DecidableEq, Inhabited

/-- What `readinto` or `write` answers. -/
inductive RRes where
  | data (b : List Nat)
  | count (n : Nat)
  | none
  | bad (v : Int)
  | exc (e : PyExc)
  deriving Repr, DecidableEq, Inhabited

def rawClosedErr : PyExc := .valueError "raw closed"

namespace Raw

/-- `readinto(b)` with `len(b) = len`. -/
def readinto (r : Raw) (len : Nat) : Raw × RRes :=
  let r := { r with log := r.log ++ [RCall.readinto len] }
  if r.closed then (r, .exc rawClosedErr) else
  let take (r : Raw) (k : Nat) : Raw × RRes :=
    let d := (r.data.drop r.pos).take (min k len)
    ({ r with pos := r.pos + d.length }, .data d)
  match r.rs with
  | [] => take r len
  | .short k :: t => take { r with rs := t } k
  | .block :: t => ({ r with rs := t }, .none)
  | .bad v :: t => ({ r with rs := t }, .bad v)
  | .raise c m :: t => ({ r with rs := t }, .exc (.named c m))

/-- `write(b)`. -/
def write (r : Raw) (b : List Nat) : Raw × RRes :=
  let r := { r with log := r.log ++ [RCall.write b] }
  if r.closed then (r, .exc rawClosedErr) else
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
  | .raise c m :: t => ({ r with ws := t }, .exc (.named c m))

def popS (r : Raw) : Raw × SStep :=
  match r.ss with
  | [] => (r, .ok)
  | s :: t => ({ r with ss := t }, s)

/-- `seek(p, w)`. -/
def seek (r : Raw) (p w : Int) : Raw × Py Int :=
  let r := { r with log := r.log ++ [RCall.seek p w] }
  if r.closed then (r, .error rawClosedErr) else
  let (r, st) := r.popS
  match st with
  | .raise c m => (r, .error (.named c m))
  | .bad v => (r, .ok v)
  | .ok =>
    if !r.canSeek then (r, .error (osError "unseekable")) else
    let n : Int :=
      if w = 0 then p else if w = 1 then r.pos + p else if w = 2 then r.data.length + p else -1
    if n < 0 then (r, .error (.valueError "bad seek")) else
    ({ r with pos := n.toNat }, .ok n)

/-- `tell()`. -/
def tell (r : Raw) : Raw × Py Int :=
  let r := { r with log := r.log ++ [RCall.tell] }
  if r.closed then (r, .error rawClosedErr) else
  let (r, st) := r.popS
  match st with
  | .raise c m => (r, .error (.named c m))
  | .bad v => (r, .ok v)
  | .ok => if !r.canSeek then (r, .error (osError "unseekable")) else (r, .ok r.pos)

/-- `truncate(p)` (`None` is the current position). -/
def truncate (r : Raw) (p : Option Int) : Raw × Py Int :=
  let r := { r with log := r.log ++ [RCall.truncate p] }
  if r.closed then (r, .error rawClosedErr) else
  let n : Int := p.getD r.pos
  if n < 0 then (r, .error (.valueError "bad truncate")) else
  -- the bound of the harness raw: never build the zeros of a huge scripted position
  if n > 2 ^ 24 then (r, .error (.overflowError "too big")) else
  let d := (r.data ++ List.replicate (n.toNat - r.data.length) 0).take n.toNat
  ({ r with data := d }, .ok n)

/-- `flush()`, the harness logging around `IOBase.flush`. -/
def flush (r : Raw) : Raw × Py Unit :=
  let r := { r with log := r.log ++ [RCall.flush] }
  if r.closed then (r, .error (.valueError "I/O operation on closed file.")) else (r, .ok ())

/-- `close()`, the harness logging around `IOBase.close`. -/
def close (r : Raw) : Raw × Py Unit :=
  let r := { r with log := r.log ++ [RCall.close] }
  match r.closeFail with
  | some (c, m) => ({ r with closeFail := none }, .error (.named c m))
  | none =>
    if r.closed then (r, .ok ()) else
    let (r, _) := r.flush
    ({ r with closed := true }, .ok ())

end Raw

end PyLean.PyIO
