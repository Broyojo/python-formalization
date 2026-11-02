import PyLean.PyIO.TextC
import PyLean.PyIO.StringExtra

/-! Operations on a `TextIOWrapper` over a `BytesIO`, for both twins. -/

namespace PyLean.PyIO

open PyLean SM

inductive TXOp where
  | read (n : Option Int) | readline (n : Option Int) | next | readlines (h : Option Int)
  | write (s : List Nat) | seek (p w : Int) | tell | seekTell | truncate (n : Option Int)
  | flush | close | detach | closed | encoding | errors | newlines
  | lineBuffering | writeThrough | seekable | readable | writable | isatty | fileno | name
  | chunkGet | chunkSet (v : Int) | chunkDel
  /-- `f.buffer is b`. -/
  | buffer
  /-- `reconfigure(line_buffering=lb, write_through=wt)`, with `newline=nl` when `some`. -/
  | reconfigure (nl : Option (Option (List Nat))) (lb wt : Option Bool)
  | bufvalue
  deriving Repr, DecidableEq, Inhabited

namespace TCm

/-- `textiowrapper` readlines: `_io__IOBase_readlines_impl` over `iternext`. -/
def readlinesLoop (hint : Int) : Nat → Int → List Atom → TM Val
  | 0, _, _ => thr .modelFuel
  | fuel + 1, length, acc => do
    let r ← SM.attempt next
    match r with
    | .error .stopIteration => pure (.list acc.reverse)
    | .error e => thr e
    | .ok v =>
      let l := v.strOf
      let acc := Atom.str l :: acc
      if hint > 0 ∧ (l.length : Int) > hint - length then pure (.list acc.reverse)
      else readlinesLoop hint fuel (length + l.length) acc

/-- `_io_TextIOWrapper_reconfigure_impl`, textio.c:1438-1513, with `set_newline`
(:926-959). Encoding and errors stay. -/
def reconfigure (nl : Option (Option (List Nat))) (lb wt : Option Bool) : TM Val := do
  let t ← SM.get
  if t.decodedNN ∧ nl.isSome then
    thr (unsupportedOp "It is not possible to set the encoding or newline of stream after the first read")
  match nl with
  | some (some n) =>
    if !(n = [] ∨ n = [10] ∨ n = [13] ∨ n = [13, 10]) then
      thr (.valueError "~illegal newline value")
  | _ => pure ()
  let _ ← flush
  SM.mod fun t => { t with b2c := (0, 1) }
  match nl with
  | some n =>
    SM.mod fun t =>
      let ru := n.isNone || n = some []
      { t with readnl := n, readuniversal := ru, readtranslate := n.isNone
               writetranslate := n ≠ some []
               writenl := if !ru && n ≠ some [10] then n else none
               dec := NDec.fresh (some []) n.isNone }
  | none => pure ()
  SM.mod fun t => { t with lineBuffering := lb.getD t.lineBuffering, writeThrough := wt.getD t.writeThrough }
  pure Val.none

def stepOp (t : TC) : TXOp → TC × Py Val
  | .read n =>
    match optSsize (-1) n with
    | .error e => (t, .error e)
    | .ok n => (read n) t
  | .readline none => (t, .error (.typeError "'NoneType' object cannot be interpreted as an integer"))
  | .readline (some n) =>
    -- textio.c:2451: `size: Py_ssize_t = -1`, so unlike `read` no `None`
    if !InSsize n then (t, .error (.overflowError "Python int too large to convert to C ssize_t"))
    else (do checkAttached; let r ← readlineRaw n; pure (Val.str r)) t
  | .next => next t
  | .readlines h =>
    match optSsize (-1) h with
    | .error e => (t, .error e)
    | .ok h =>
      (do checkAttached; checkClosed
          let t ← SM.get
          readlinesLoop h (t.b.buf.length - t.b.pos + t.decoded.length + 3) 0 []) t
  | .write s => (write s) t
  | .seek p w =>
    match argCInt w with
    | .error e => (t, .error e)
    | .ok w => (seek p w) t
  | .tell => (do let r ← tell; pure (Val.int r)) t
  | .seekTell => (do let r ← tell; seek r 0) t
  | .truncate n => (truncate n) t
  | .flush => flush t
  | .close => close t
  | .detach => detach t
  -- textio.c:3351-3365: an uninitialized object reports closed
  | .closed =>
    if !t.ok then (t, .ok (.bool true)) else
    (do checkAttached; let t ← SM.get; pure (Val.bool t.b.closed)) t
  | .encoding => (do checkAttached; let t ← SM.get; pure (Val.str t.encName)) t
  | .errors => (do checkAttached; let t ← SM.get; pure (Val.str t.errName)) t
  | .newlines =>
    (do checkAttached
        let t ← SM.get
        if t.readuniversal then pure (newlinesVal t.dec.seennl) else pure Val.none) t
  | .lineBuffering => (do checkAttached; let t ← SM.get; pure (Val.bool t.lineBuffering)) t
  | .writeThrough => (do checkAttached; let t ← SM.get; pure (Val.bool t.writeThrough)) t
  | .seekable | .readable | .writable =>
    (do checkAttached
        let t ← SM.get
        if t.b.closed then thr (.valueError "I/O operation on closed file.")
        pure (Val.bool true)) t
  | .isatty =>
    (do checkAttached
        let t ← SM.get
        if t.b.closed then thr (.valueError "I/O operation on closed file.")
        pure (Val.bool false)) t
  | .fileno => (do checkAttached; thr (unsupportedOp "fileno")) t
  | .name =>
    (do checkAttached
        thr (.named "AttributeError" "'_io.BytesIO' object has no attribute 'name'")) t
  | .chunkGet => (do checkAttached; let t ← SM.get; pure (Val.int t.chunk)) t
  | .chunkSet v =>
    (do checkAttached
        if !InSsize v then thr (.valueError "cannot fit 'int' into an index-sized integer")
        if v ≤ 0 then thr (.valueError "a strictly positive integer is required")
        SM.mod fun t => { t with chunk := v.toNat }
        pure Val.none) t
  -- the setter generated in clinic/textio.c.h:1324-1333, before any attachment check
  | .chunkDel =>
    (t, .error (.named "AttributeError" "attribute '_CHUNK_SIZE' of '_io.TextIOWrapper' objects cannot be deleted"))
  -- `_io_TextIOWrapper_buffer_get_impl`, textio.c:3446-3450
  | .buffer => (do checkAttached; pure (Val.bool true)) t
  | .reconfigure nl lb wt => (do checkAttached; reconfigure nl lb wt) t
  | .bufvalue =>
    if t.b.closed then (t, .error (.valueError "I/O operation on closed file.")) else (t, .ok (.bytes t.b.buf))

end TCm

namespace TP

/-- `TextIOWrapper(BytesIO(data), 'utf-8', 'surrogatepass', newline)`,
_pyio.py:2090-2120 and `_configure`, :2128-2143 (`os.linesep` is `\n`). -/
def initW (data : List Nat) (newline : Option (List Nat)) : Py TState :=
  match newline with
  | some nl =>
    if !(nl = [] ∨ nl = [10] ∨ nl = [13] ∨ nl = [13, 10]) then .error (illegalNewline nl) else .ok (mk data)
  | none => .ok (mk data)
where
  mk (data : List Nat) : TState :=
    { b := bInit data, decoded := [], used := 0, snapshot := none, telling := true, decoder := none
      b2c := (0, 1)
      readuniversal := newline.isNone || newline = some []
      readtranslate := newline.isNone
      readnl := newline
      writetranslate := newline ≠ some []
      writenl := match newline with
        | some [] | none => [10]
        | some nl => nl }

/-- `TextIOWrapper.detach`, _pyio.py:2514-2520. -/
def stepW (t : TState) : TXOp → TState × Py Val
  | .read n => step t (.read n)
  | .readline n => step t (.readline n)
  | .next => step t .next
  | .readlines h => step t (.readlines h)
  | .write s => step t (.write s)
  | .seek p w => step t (.seek p w)
  | .tell => step t .tell
  | .seekTell => step t .seekTell
  | .truncate n => step t (.truncate n)
  | .flush => xstep t .flush
  | .close => close t
  | .detach => xstep t .flush |> fun (t, r) => (t, r.map (fun _ => .none))
  | .closed => (t, .ok (.bool t.b.closed))
  | .encoding => (t, .ok (.str [117, 116, 102, 45, 56]))
  | .errors => (t, .ok (.str ("surrogatepass".toList.map Char.toNat)))
  | .newlines => (t, newlines t)
  | .lineBuffering | .writeThrough => (t, .ok (.bool false))
  | .seekable => xstep t .seekable
  | .readable => xstep t .readable
  | .writable => xstep t .writable
  | .isatty => xstep t .isatty
  | .fileno => xstep t .fileno
  | .name => xstep t .name
  | .chunkGet => (t, .ok (.int 2048))
  | .chunkSet _ => (t, .ok .none)
  -- `_CHUNK_SIZE` is a class attribute, _pyio.py:2081
  | .chunkDel => (t, .error (.named "AttributeError" "'TextIOWrapper' object has no attribute '_CHUNK_SIZE'"))
  | .buffer => (t, .ok (.bool true))
  | .reconfigure _ _ _ => (t, .ok .none)
  | .bufvalue =>
    if t.b.closed then (t, .error (.valueError "getvalue on closed file")) else (t, .ok (.bytes t.b.buf))

end TP

end PyLean.PyIO
