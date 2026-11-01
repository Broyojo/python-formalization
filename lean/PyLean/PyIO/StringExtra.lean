import PyLean.PyIO.StringC
import PyLean.PyIO.StringPy

/-!
The remaining `StringIO` attributes of both twins: inquiries, `flush`, `isatty`,
`fileno`, `detach`, `encoding`, `errors`, `line_buffering`, `name`, and the C
pickling state (`Modules/_io/stringio.c:804-999`, `Modules/_io/iobase.c`,
`Modules/_io/textio.c:67-185`, `Lib/_pyio.py:2244-2277`, :2773-2788).
-/

namespace PyLean.PyIO

open PyLean

/-- `setstate v nl p` is `__setstate__((v, nl, p, None))`. -/
inductive SXOp where
  | readable | writable | seekable | flush | isatty | fileno | detach
  | encoding | errors | lineBuffering | name
  | getstate
  | setstate (v : Option (List Nat)) (nl : Option (List Nat)) (pos : Int)
  deriving Repr, DecidableEq, Inhabited

namespace SC

/-- `_io_StringIO___setstate___impl`, stringio.c:899-999: `__init__` runs on the
state, then the buffer is replaced verbatim and the position range-checked. -/
def setstate (s : SCState) (v nl : Option (List Nat)) (pos : Int) : SCState × Py Val :=
  if s.closed then (s, .error closedErr) else
  match init v nl with
  | .error e => (s, .error e)
  | .ok t =>
    let t := { t with buf := v.getD [] }
    match argSsize pos with
    | .error e => (t, .error e)
    | .ok p =>
      if p < 0 then (t, .error (.valueError "position value cannot be negative"))
      else ({ t with pos := p.toNat }, .ok .none)

/-- stringio.c:804-842 (`readable`..), :1022-1028 (`line_buffering`), :863-888
(`__getstate__`); `flush` and `isatty` are `_IOBase`'s (iobase.c:172-185,
:544-550): `flush` only sees `__IOBase_closed`, which `StringIO.close` does not set. -/
def xstep (s : SCState) : SXOp → SCState × Py Val
  | .readable | .writable | .seekable =>
    if s.closed then (s, .error closedErr) else (s, .ok (.bool true))
  | .flush => (s, .ok .none)
  | .isatty =>
    if s.closed then (s, .error (.valueError "I/O operation on closed file.")) else (s, .ok (.bool false))
  | .fileno => (s, .error (unsupportedOp "fileno"))
  | .detach => (s, .error (unsupportedOp "detach"))
  | .encoding | .errors => (s, .ok .none)
  | .lineBuffering => if s.closed then (s, .error closedErr) else (s, .ok (.bool false))
  | .name => (s, .error (.named "AttributeError" "'_io.StringIO' object has no attribute 'name'"))
  | .getstate =>
    if s.closed then (s, .error closedErr)
    else (s, .ok (.list [.str s.buf, (match s.readnl with
      | some n => .str n
      | none => .none), .int s.pos, .none]))
  | .setstate v nl p => setstate s v nl p

end SC

namespace TP

/-- `TextIOWrapper.readable/writable` (_pyio.py:2249-2253) and `seekable`
(:2244-2247), `flush` (:2255-2257), `isatty` (:2277-2278), `fileno` (:2274-2275,
`IOBase.fileno`), `name` (:2270-2272), `StringIO.encoding/errors/detach`
(:2778-2788), `line_buffering` (:2189-2191). -/
def xstep (t : TState) : SXOp → TState × Py Val
  | .readable | .writable | .seekable =>
    if t.b.closed then (t, .error closedDot) else (t, .ok (.bool true))
  | .flush =>
    match flush t with
    | .error e => (t, .error e)
    | .ok t => (t, .ok .none)
  | .isatty => if t.b.closed then (t, .error closedDot) else (t, .ok (.bool false))
  | .fileno => (t, .error (unsupportedOp "BytesIO.fileno() not supported"))
  | .detach => (t, .error (unsupportedOp "StringIO.detach() not supported"))
  | .encoding | .errors => (t, .ok .none)
  | .lineBuffering => (t, .ok (.bool false))
  | .name => (t, .error (.named "AttributeError" "'BytesIO' object has no attribute 'name'"))
  | .getstate | .setstate _ _ _ => (t, .ok .none)

end TP

def stepSAnyC (s : SCState) : SOp ⊕ SXOp → SCState × Py Val
  | .inl o => SC.step s o
  | .inr o => SC.xstep s o

def stepSAnyP (t : TState) : SOp ⊕ SXOp → TState × Py Val
  | .inl o => TP.step t o
  | .inr o => TP.xstep t o

/-- On an open StringIO `readable`, `writable`, `seekable` are true and `isatty`
false; on a closed one each raises `ValueError` (both twins, every state). -/
def StringIOInquiries : Prop := ∀ (s : SCState) (t : TState) (o : SXOp),
  (o = .readable ∨ o = .writable ∨ o = .seekable ∨ o = .isatty) →
  (s.closed = false → (SC.xstep s o).2 = .ok (.bool (o ≠ .isatty))) ∧
  (s.closed = true → ∃ m, (SC.xstep s o).2 = .error (.valueError m)) ∧
  (t.b.closed = false → (TP.xstep t o).2 = .ok (.bool (o ≠ .isatty))) ∧
  (t.b.closed = true → (TP.xstep t o).2 = .error (.valueError "I/O operation on closed file."))

theorem stringIOInquiries_proven : StringIOInquiries := by
  intro s t o ho
  rcases ho with rfl | rfl | rfl | rfl <;>
    simp +contextual [SC.xstep, TP.xstep, SC.closedErr, TP.closedDot]

/-- `detach`, `fileno` raise `UnsupportedOperation`, and `encoding`, `errors` are
`None`, in both twins on every state (`TextIOBase`: "not supported by an
in-memory text buffer"). -/
def StringIOUnsupported : Prop := ∀ (s : SCState) (t : TState),
  (∀ o, (o = SXOp.detach ∨ o = .fileno) →
    (((SC.xstep s o).2.toBool = false) ∧ ((TP.xstep t o).2.toBool = false) ∧
     ∃ m₁ m₂, (SC.xstep s o).2 = .error (unsupportedOp m₁) ∧ (TP.xstep t o).2 = .error (unsupportedOp m₂))) ∧
  (∀ o, (o = SXOp.encoding ∨ o = .errors) → (SC.xstep s o).2 = .ok .none ∧ (TP.xstep t o).2 = .ok .none)

theorem stringIOUnsupported_proven : StringIOUnsupported := by
  intro s t
  constructor
  · intro o ho
    rcases ho with rfl | rfl <;> exact ⟨rfl, rfl, _, _, rfl, rfl⟩
  · intro o ho
    rcases ho with rfl | rfl <;> simp [SC.xstep, TP.xstep]

/-- Pickling round trip (C): whenever `__init__` accepts the saved value and
newline, `__setstate__(__getstate__())` restores contents and position verbatim
(no newline translation is applied twice). The position fits `Py_ssize_t`. -/
def StringIOPickleRoundTrip : Prop := ∀ (s t i : SCState),
  s.closed = false → t.closed = false → (s.pos : Int) ≤ ssizeMax →
  SC.init (some s.buf) s.readnl = .ok i →
  (SC.setstate t (some s.buf) s.readnl s.pos).2 = .ok .none ∧
  (SC.setstate t (some s.buf) s.readnl s.pos).1.buf = s.buf ∧
  (SC.setstate t (some s.buf) s.readnl s.pos).1.pos = s.pos

theorem stringIOPickleRoundTrip_proven : StringIOPickleRoundTrip := by
  intro s t i hs ht hp hi
  have hz : ssizeMin ≤ 0 := by decide
  have hsz : InSsize (s.pos : Int) := ⟨by omega, hp⟩
  have hn : ¬ (s.pos : Int) < 0 := by omega
  simp [SC.setstate, ht, hi, argSsize, hsz, hn]

end PyLean.PyIO
