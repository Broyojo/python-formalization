import PyLean.PyIO.BytesDocs

/-!
The remaining `BytesIO` methods of both twins: the inquiries, `flush`,
`isatty`, `writelines`, and pickling (`bytesio.c`, `Lib/_pyio.py`).
-/

namespace PyLean.PyIO

open PyLean

/-- `readable`..`isatty` take no argument; `writelines ls` passes a list of
bytes; `getstate` is `__getstate__()` (the dict slot is `None`);
`setstate b p` is `__setstate__((b, p, None))`. -/
inductive XOp where
  | readable | writable | seekable | flush | isatty
  | writelines (ls : List (List Nat))
  | getstate
  | setstate (b : List Nat) (pos : Int)
  deriving Repr, DecidableEq, Inhabited

namespace C

/-- `_io_BytesIO_writelines_impl`, bytesio.c:850-876: `CHECK_CLOSED`, then
`write_bytes_lock_held` per item, stopping at the first failure. -/
def writelinesLoop : BState → List (List Nat) → BState × Py Val
  | s, [] => (s, .ok .none)
  | s, l :: ls =>
    match write s l with
    | (s', .error e) => (s', .error e)
    | (s', .ok _) => writelinesLoop s' ls

/-- `bytesio_setstate_lock_held`, bytesio.c:948-1023, for a 3-tuple: exports
are checked, the buffer is reset and `state[0]` is written, then the position
is converted and range-checked. -/
def setstate (s : BState) (b : List Nat) (pos : Int) : BState × Py Val :=
  if s.exports > 0 then (s, .error bufferError) else
  match write { s with buf := [], pos := 0 } b with
  | (s', .error e) => (s', .error e)
  | (s', .ok _) =>
    match argSsize pos with
    | .error e => (s', .error e)
    | .ok p =>
      if p < 0 then (s', .error (.valueError "position value cannot be negative"))
      else ({ s' with pos := p.toNat }, .ok .none)

/-- bytesio.c:323-328, :338-343, :353-358, :368-373, :445-450, :850-876,
:938-945, :948-1023. -/
def xstep (s : BState) : XOp → BState × Py Val
  | .readable | .writable | .seekable =>
    if s.closed then (s, .error closedErr) else (s, .ok (.bool true))
  | .flush => if s.closed then (s, .error closedErr) else (s, .ok .none)
  | .isatty => if s.closed then (s, .error closedErr) else (s, .ok (.bool false))
  | .writelines ls => if s.closed then (s, .error closedErr) else writelinesLoop s ls
  | .getstate =>
    if s.closed then (s, .error closedErr)
    else (s, .ok (.list [.bytes s.buf, .int s.pos, .none]))
  | .setstate b p => setstate s b p

end C

namespace P

def closedDot : PyExc := .valueError "I/O operation on closed file."

/-- `for line in lines: self.write(line)`, _pyio.py:589-590. -/
def writelinesLoop : BState → List (List Nat) → BState × Py Val
  | s, [] => (s, .ok .none)
  | s, l :: ls =>
    match write s l with
    | (s', .error e) => (s', .error e)
    | (s', .ok _) => writelinesLoop s' ls

/-- `BytesIO.readable/writable/seekable` (_pyio.py:1022-1035), `IOBase.flush`
(:380-386), `IOBase.isatty` (:503-509), `IOBase.writelines` (:583-590),
`BytesIO.__getstate__` (@3.14.7:891-894, the instance dict as `[buffer, pos]`).
`__setstate__` does not exist in `_pyio`. -/
def xstep (s : BState) : XOp → BState × Py Val
  | .readable | .writable | .seekable =>
    if s.closed then (s, .error closedDot) else (s, .ok (.bool true))
  | .flush => if s.closed then (s, .error closedDot) else (s, .ok .none)
  | .isatty => if s.closed then (s, .error closedDot) else (s, .ok (.bool false))
  | .writelines ls => if s.closed then (s, .error closedDot) else writelinesLoop s ls
  | .getstate =>
    if s.closed then (s, .error (.valueError "__getstate__ on closed file"))
    else (s, .ok (.list [.bytes s.buf, .int s.pos]))
  | .setstate _ _ => (s, .ok .none)

end P

def stepAnyC (s : BState) : BOp ⊕ XOp → BState × Py Val
  | .inl o => C.step s o
  | .inr o => C.xstep s o

def stepAnyP (s : BState) : BOp ⊕ XOp → BState × Py Val
  | .inl o => P.step s o
  | .inr o => P.xstep s o

/-- On an open BytesIO `readable`, `writable`, `seekable` are true, `flush`
returns `None` and `isatty` false; on a closed one each raises `ValueError`
with the message of `IOBase._checkClosed` (both twins, every state). -/
def BytesIOInquiries : Prop := ∀ (s : BState) (o : XOp),
  (o = .readable ∨ o = .writable ∨ o = .seekable ∨ o = .flush ∨ o = .isatty) →
  (if s.closed then (C.xstep s o).2 = .error (.valueError "I/O operation on closed file.") ∧
      (P.xstep s o).2 = .error (.valueError "I/O operation on closed file.")
    else (C.xstep s o).2 = (P.xstep s o).2 ∧
      (C.xstep s o).2 = (if o = .flush then .ok .none else .ok (.bool (o ≠ .isatty)))) ∧
  (C.xstep s o).1 = s ∧ (P.xstep s o).1 = s

theorem bytesIOInquiries_proven : BytesIOInquiries := by
  intro s o ho
  rcases ho with rfl | rfl | rfl | rfl | rfl <;> cases hc : s.closed <;>
    simp [C.xstep, P.xstep, hc, C.closedErr, P.closedDot]

/-- `writelines(ls)` on an open BytesIO is `write(l)` for each `l` in turn,
stopping at the first failure ("equivalent to calling write() for each
element", bytesio.c:846-847): same final state and outcome as the run of
`write` operations (both twins). -/
def BytesIOWritelines : Prop := ∀ (s : BState) (ls : List (List Nat)), s.closed = false →
  ∃ (rs : List (Py Val)),
    (runOps C.step s (ls.map .write)).2 = rs ∧
    ((∀ r ∈ rs, r.toBool = true) →
      (C.xstep s (.writelines ls)).1 = (runOps C.step s (ls.map .write)).1 ∧
      (C.xstep s (.writelines ls)).2 = .ok .none) ∧
  ((∀ r ∈ (runOps P.step s (ls.map .write)).2, r.toBool = true) →
    (P.xstep s (.writelines ls)).1 = (runOps P.step s (ls.map .write)).1 ∧
    (P.xstep s (.writelines ls)).2 = .ok .none)

theorem C_writelines_ok : ∀ (ls : List (List Nat)) (s : BState),
    (∀ r ∈ (runOps C.step s (ls.map .write)).2, r.toBool = true) →
    C.writelinesLoop s ls = ((runOps C.step s (ls.map .write)).1, .ok .none) := by
  intro ls
  induction ls with
  | nil => intro s _; simp [C.writelinesLoop, runOps]
  | cons l ls ih =>
    intro s h
    simp only [List.map_cons, runOps, C.step] at h ⊢
    simp only [C.writelinesLoop]
    rcases hw : C.write s l with ⟨s', r⟩
    rw [hw] at h
    cases r with
    | error e => simp [Except.toBool] at h
    | ok v =>
      simp only at h ⊢
      exact ih s' (fun r hr => h r (List.mem_cons_of_mem _ hr))

theorem P_writelines_ok : ∀ (ls : List (List Nat)) (s : BState),
    (∀ r ∈ (runOps P.step s (ls.map .write)).2, r.toBool = true) →
    P.writelinesLoop s ls = ((runOps P.step s (ls.map .write)).1, .ok .none) := by
  intro ls
  induction ls with
  | nil => intro s _; simp [P.writelinesLoop, runOps]
  | cons l ls ih =>
    intro s h
    simp only [List.map_cons, runOps, P.step] at h ⊢
    simp only [P.writelinesLoop]
    rcases hw : P.write s l with ⟨s', r⟩
    rw [hw] at h
    cases r with
    | error e => simp [Except.toBool] at h
    | ok v =>
      simp only at h ⊢
      exact ih s' (fun r hr => h r (List.mem_cons_of_mem _ hr))

theorem bytesIOWritelines_proven : BytesIOWritelines := by
  intro s ls hc
  refine ⟨_, rfl, ?_, ?_⟩
  · intro h; simp only [C.xstep, hc, Bool.false_eq_true, ite_false]; rw [C_writelines_ok ls s h]; simp
  · intro h; simp only [P.xstep, hc, Bool.false_eq_true, ite_false]; rw [P_writelines_ok ls s h]; simp

/-- Pickling round trip (C): the state of an open BytesIO, restored into any
open BytesIO without exports, reproduces contents and position. Hypotheses:
the position fits `Py_ssize_t` (a type invariant of the C object) and the
contents are below the allocation bound. -/
def BytesIOPickleRoundTrip : Prop := ∀ (s t : BState),
  s.closed = false → t.closed = false → t.exports = 0 → (s.pos : Int) ≤ ssizeMax → s.buf.length < memLimit →
  (C.xstep s .getstate).2 = .ok (.list [.bytes s.buf, .int s.pos, .none]) ∧
  (C.xstep t (.setstate s.buf s.pos)).2 = .ok .none ∧
  (C.xstep t (.setstate s.buf s.pos)).1.buf = s.buf ∧ (C.xstep t (.setstate s.buf s.pos)).1.pos = s.pos

theorem bytesIOPickleRoundTrip_proven : BytesIOPickleRoundTrip := by
  intro s t hs ht he hp hm
  have hmax : memLimit ≤ ssizeMax := by decide
  have hz : ssizeMin ≤ 0 := by decide
  have hsz : InSsize (s.pos : Int) := ⟨by omega, hp⟩
  have hw : C.write { t with buf := [], pos := 0 } s.buf =
      (if s.buf = [] then { t with buf := [], pos := 0 }
       else { t with buf := s.buf, pos := s.buf.length, shared := false }, .ok (.int s.buf.length)) := by
    obtain ⟨tb, tp, tc, te, ts⟩ := t
    simp only at ht he; subst ht he
    by_cases hb : s.buf = []
    · simp [C.write, hb]
    · have hl : s.buf.length ≠ 0 := fun e => hb (List.eq_nil_of_length_eq_zero e)
      have c1 : ¬ ((0 + s.buf.length : Nat) > 0 ∧ (((0 + s.buf.length : Nat)) : Int) > ssizeMax) := by omega
      have c2 : ¬ ((0 + s.buf.length : Nat) > 0 ∧ (((0 + s.buf.length : Nat)) : Int) = ssizeMax) := by omega
      have c3 : ¬ ((0 + s.buf.length : Nat) > 0 ∧ (0 + s.buf.length : Nat) ≥ memLimit) := by omega
      simp only [C.write, Bool.false_eq_true, ite_false, Nat.lt_irrefl, gt_iff_lt, hl, List.length_nil]
      simp only [gt_iff_lt] at c1 c2 c3
      simp only [c1, c2, c3, ite_false, hb]
      simp [writeAt]
  have hpn : ¬ (s.pos : Int) < 0 := by omega
  rw [he] at hw
  refine ⟨by simp [C.xstep, hs], ?_⟩
  simp only [C.xstep, C.setstate, he, Nat.lt_irrefl, gt_iff_lt, Nat.not_lt_zero, ite_false, hw, argSsize, hsz, ite_true, hpn]
  by_cases hb : s.buf = [] <;> simp [hb] at hw ⊢ <;> simp [hw]

/-- `getbuffer()` followed by releasing the view restores the export count, so
a resize is possible again (C `bytesiobuf_getbuffer`/`releasebuffer`, Python
`memoryview` over the `bytearray`); position and contents do not change. -/
def BytesIOReleaseExports : Prop := ∀ (s : BState), s.closed = false →
  (C.step (C.step s .getbuffer).1 .release).1.exports = s.exports ∧
  (C.step (C.step s .getbuffer).1 .release).1.buf = s.buf ∧
  (C.step (C.step s .getbuffer).1 .release).1.pos = s.pos ∧
  (C.step s .getbuffer).1.exports > 0 ∧
  (P.step (P.step s .getbuffer).1 .release).1 = s

theorem bytesIOReleaseExports_proven : BytesIOReleaseExports := by
  intro s hc
  obtain ⟨buf, pos, cl, ex, sh⟩ := s
  simp only at hc; subst hc
  simp [C.step, P.step, bRelease]

end PyLean.PyIO
