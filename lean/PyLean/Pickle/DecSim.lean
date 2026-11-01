import PyLean.Pickle.DecProps
import PyLean.Pickle.IntNarrow
import PyLean.Pickle.Narrow

/-!
A simulation between the two unpicklers, step by step. The states are related
by `DR`. Python's reads never fail when data runs short, they return what is
left, so where C raises `truncated` Python goes on, but at the end of the input
with nothing left to reach `STOP`: `Doom`. `DOut` allows exactly that.

The reader relation `RR` has three shapes. No frame on either side; a frame on
both; and a frame Python has used up and still holds while C has left it,
which a read of 0 bytes at the end of a frame does in `_Unpickler_ReadInto`.
-/

namespace PyLean.Pickle

open PyLean

/-- `marks` as the C stack sizes at each Python metastack level. -/
def marksOf : List (List DV) → List Nat
  | [] => []
  | m :: r => (m ++ r.flatten).length :: marksOf r

/-- Python's frame is used up, or absent. -/
def FrameDone (p : PySt) : Prop :=
  match p.frame with
  | none => True
  | some (f, fp) => f.length ≤ fp

/-- Every read Python makes from now on returns nothing. -/
def Doom (p : PySt) : Prop := p.inp.length ≤ p.pos ∧ FrameDone p

/-- The readers are at the same place in the same input. -/
def RR (p : PySt) (c : CSt) : Prop :=
  match p.frame with
  | none => c.frameEnd = none ∧ c.idx = p.pos ∧ c.inputLen = p.inp.length ∧ p.pos ≤ p.inp.length
  | some (f, fp) =>
    fp ≤ f.length ∧ p.pos ≤ p.inp.length ∧
    ((c.frameEnd = some p.pos ∧ f.length ≤ p.pos ∧ c.idx + (f.length - fp) = p.pos ∧
        c.inputLen = p.pos ∧ c.savedInputLen = p.inp.length ∧
        f = (p.inp.drop (p.pos - f.length)).take f.length) ∨
     (fp = f.length ∧ c.frameEnd = none ∧ c.idx = p.pos ∧ c.inputLen = p.inp.length))

/-- The two unpicklers hold the same objects in the same places. -/
structure DR (p : PySt) (c : CSt) : Prop where
  inp : c.inp = p.inp
  rr : RR p c
  stack : c.stack = p.stack ++ p.metastack.flatten
  marks : c.marks = marksOf p.metastack
  memo : p.memo = c.memo.map (fun kv => ((kv.1 : Int), kv.2))
  heap : c.heap = p.heap
  proto : c.proto = p.proto
  /-- Type invariant: a `bytes` object has at most `sys.maxsize` bytes. -/
  size : p.inp.length ≤ ssizeMaxN

/-- What a step of each may do from related states, for values related by `R`. -/
def DOut {α β : Type} (R : α → β → Prop) :
    Except PyExc (β × CSt) → Except PyExc (α × PySt) → Prop
  | .ok (b, c'), .ok (a, p') => R a b ∧ DR p' c'
  | .error _, .error _ => True
  | .error _, .ok (_, p') => Doom p'
  | .ok _, .error _ => False

/-- `mp` and `mc` run in step from all related states. -/
def MSim {α β : Type} (R : α → β → Prop) (mp : PyM α) (mc : CM β) : Prop :=
  ∀ p c, DR p c → DOut R (mc.run c) (mp.run p)

/-- `m` leaves a doomed state doomed. -/
def Keeps {α : Type} (m : PyM α) : Prop :=
  ∀ p a p', Doom p → m.run p = .ok (a, p') → Doom p'

theorem pyRun_bind {α β : Type} (m : PyM α) (f : α → PyM β) (p : PySt) :
    (m >>= f).run p = (match m.run p with
      | .ok (a, s) => (f a).run s
      | .error e => .error e) := by
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind]
  cases m p <;> rfl

theorem cRun_bind {α β : Type} (m : CM α) (f : α → CM β) (c : CSt) :
    (m >>= f).run c = (match m.run c with
      | .ok (a, s) => (f a).run s
      | .error e => .error e) := by
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind]
  cases m c <;> rfl

/-- Sequencing. In the third case C has failed and Python goes on doomed. -/
theorem MSim.bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {mp : PyM α} {mc : CM β} {fp : α → PyM γ} {fc : β → CM δ}
    (h : MSim R mp mc) (hk : ∀ a b, R a b → MSim S (fp a) (fc b)) (hd : ∀ a, Keeps (fp a)) :
    MSim S (mp >>= fp) (mc >>= fc) := by
  intro p c hdr
  have hb := h p c hdr
  rw [pyRun_bind, cRun_bind]
  cases hc : mc.run c with
  | ok rc =>
    obtain ⟨b, c'⟩ := rc
    cases hq : mp.run p with
    | ok rp =>
      obtain ⟨a, p'⟩ := rp
      rw [hc, hq] at hb
      exact hk a b hb.1 p' c' hb.2
    | error e => rw [hc, hq] at hb; exact hb.elim
  | error e =>
    cases hq : mp.run p with
    | ok rp =>
      obtain ⟨a, p'⟩ := rp
      rw [hc, hq] at hb
      show DOut S (Except.error e) ((fp a).run p')
      cases hr : (fp a).run p' with
      | ok r2 =>
        obtain ⟨x, p2⟩ := r2
        exact hd a p' x p2 hb hr
      | error e2 => exact trivial
    | error e2 => exact trivial

theorem keeps_pure {α : Type} (a : α) : Keeps (pure a : PyM α) := by
  intro p x p' hd h
  cases h
  exact hd

theorem keeps_bind {α β : Type} {m : PyM α} {f : α → PyM β} (hm : Keeps m) (hf : ∀ a, Keeps (f a)) :
    Keeps (m >>= f) := by
  intro p x p' hd h
  rw [pyRun_bind] at h
  cases hq : m.run p with
  | error e => rw [hq] at h; cases h
  | ok r =>
    obtain ⟨a, s⟩ := r
    rw [hq] at h
    exact hf a s x p' (hm p a s hd hq) h

theorem keeps_throw {α : Type} (e : PyExc) : Keeps (pyThrow e : PyM α) := by
  intro p x p' _ h
  cases h

theorem keeps_lift {α : Type} (r : Py α) : Keeps (pyLift r) := by
  intro p x p' hd h
  cases r with
  | ok a => cases h; exact hd
  | error e => cases h

theorem keeps_push (v : DV) : Keeps (push v) := by
  intro p x p' hd h
  cases h
  exact hd

theorem keeps_setHeap (h' : Heap) : Keeps (setHeap h') := by
  intro p x p' hd h
  cases h
  exact hd

theorem keeps_alloc (o : HObj) : Keeps (pyAlloc o) := by
  intro p x p' hd h
  cases h
  exact hd

/-! ## How Python's readers compute -/

theorem fileRead_run (n : Nat) (p : PySt) :
    (fileRead n).run p =
      .ok ((p.inp.drop p.pos).take n,
        { p with pos := p.pos + ((p.inp.drop p.pos).take n).length }) := rfl

theorem read_none (p : PySt) (h : p.frame = none) (n : Nat) :
    (pyRead n).run p = (fileRead n).run p := by
  obtain ⟨inp, pos, frame, stack, mt, memo, heap, proto⟩ := p
  simp only at h
  subst h
  rfl

theorem read_frame_ok (p : PySt) (f : Bytes) (fp n : Nat) (h : p.frame = some (f, fp))
    (hl : ((f.drop fp).take n).length = n) :
    (pyRead n).run p = .ok ((f.drop fp).take n, { p with frame := some (f, fp + n) }) := by
  obtain ⟨inp, pos, frame, stack, mt, memo, heap, proto⟩ := p
  simp only at h
  subst h
  have h1 : ¬ ((f.drop fp).take n = [] ∧ n ≠ 0) := by
    intro hc
    have := hc.2
    rw [hc.1] at hl
    simp at hl
    omega
  have h2 : ¬ ((f.drop fp).take n).length < n := by omega
  simp only [StateT.run, pyRead, Bind.bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get,
    StateT.get, set, MonadStateOf.set, StateT.set, pure, Except.pure, StateT.pure]
  simp only [if_neg h1, if_neg h2, hl, Nat.lt_irrefl, if_false]
  rfl

theorem read_frame_empty (p : PySt) (f : Bytes) (fp n : Nat) (h : p.frame = some (f, fp))
    (hd : (f.drop fp).take n = []) (hn : n ≠ 0) :
    (pyRead n).run p = (fileRead n).run { p with frame := none } := by
  obtain ⟨inp, pos, frame, stack, mt, memo, heap, proto⟩ := p
  simp only at h
  subst h
  simp only [StateT.run, pyRead, Bind.bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get,
    StateT.get, set, MonadStateOf.set, StateT.set, pure, Except.pure, StateT.pure]
  simp only [hd, List.length_nil, Nat.add_zero, true_and, if_pos hn]
  rfl

theorem read_frame_short (p : PySt) (f : Bytes) (fp n : Nat) (h : p.frame = some (f, fp))
    (hd : (f.drop fp).take n ≠ []) (hl : ((f.drop fp).take n).length < n) :
    ∃ e, (pyRead n).run p = .error e := by
  obtain ⟨inp, pos, frame, stack, mt, memo, heap, proto⟩ := p
  simp only at h
  subst h
  refine ⟨unpicklingError "pickle exhausted before end of frame", ?_⟩
  simp only [StateT.run, pyRead, Bind.bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get,
    StateT.get, set, MonadStateOf.set, StateT.set, pure, Except.pure, StateT.pure]
  simp only [hd, false_and, if_false, if_pos hl]
  rfl

/-! ## How C's reader computes -/

theorem cRead_fast (c : CSt) (n : Nat) (h : c.idx + n ≤ c.inputLen) :
    (cRead n).run c = .ok ((c.inp.drop c.idx).take n, { c with idx := c.idx + n }) := by
  simp only [StateT.run, cRead, Bind.bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get,
    StateT.get, set, MonadStateOf.set, StateT.set, pure, Except.pure, StateT.pure]
  simp only [if_pos h]
  rfl

theorem cRead_noframe (c : CSt) (n : Nat) (h : ¬ c.idx + n ≤ c.inputLen) (hf : c.frameEnd = none) :
    ∃ e, (cRead n).run c = .error e := by
  by_cases ho : c.idx > ssizeMaxN - n
  · exact ⟨unpicklingError "read would overflow (invalid bytecode)", by
      simp only [StateT.run, cRead, Bind.bind, StateT.bind, Except.bind, get, getThe,
        MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set, pure, Except.pure, StateT.pure]
      simp only [if_neg h, if_pos ho]
      rfl⟩
  · exact ⟨truncated, by
      simp only [StateT.run, cRead, Bind.bind, StateT.bind, Except.bind, get, getThe,
        MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set, pure, Except.pure, StateT.pure]
      simp only [if_neg h, if_neg ho, hf]
      rfl⟩

theorem cRead_straddle (c : CSt) (n fe : Nat) (h : ¬ c.idx + n ≤ c.inputLen)
    (hf : c.frameEnd = some fe) (hlt : c.idx < fe) : ∃ e, (cRead n).run c = .error e := by
  by_cases ho : c.idx > ssizeMaxN - n
  · exact ⟨unpicklingError "read would overflow (invalid bytecode)", by
      simp only [StateT.run, cRead, Bind.bind, StateT.bind, Except.bind, get, getThe,
        MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set, pure, Except.pure, StateT.pure]
      simp only [if_neg h, if_pos ho]
      rfl⟩
  · exact ⟨unpicklingError "pickle exhausted before end of frame", by
      simp only [StateT.run, cRead, Bind.bind, StateT.bind, Except.bind, get, getThe,
        MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set, pure, Except.pure, StateT.pure]
      simp only [if_neg h, if_neg ho, hf, cLeaveFrame, decide_eq_true hlt]
      rfl⟩

/-! ## The statement -/

/-- The line Python's next `readline` returns. -/
def peekLine (p : PySt) : Option Bytes :=
  match pyReadline.run p with
  | .ok (l, _) => some l
  | .error _ => none

/-- The divergences on record, for opcode `op` about to run from `p`. Each is one
refuted entry: an `INT` line as in `pickle-int-line-twins` and its two narrowings,
a line with NUL C accepts (`pickle-long-line-twins`), a `PUT` index above
`sys.maxsize` (`pickle-put-twins`), an empty `APPENDS` or `ADDITEMS` batch on a
target without the method (`pickle-loads-twins-accept`), a `FRAME` longer than the
data (`pickle-frame-twins`). -/
def Hazard (op : UInt8) (p : PySt) : Prop :=
  (op = oINT ∧ ∃ body, peekLine p = some (body ++ [nl]) ∧
    (BoolSpelling body ∨ ((0 : UInt8) ∈ body ∧ isErr (cLoadIntLine (body ++ [nl])) = false) ∨
      FastOverLimit body)) ∨
  (op = oLONG ∧ ∃ body, peekLine p = some (body ++ [nl]) ∧ (0 : UInt8) ∈ body ∧
    isErr (cLoadLongLine (body ++ [nl])) = false) ∨
  ((op = oGET ∨ op = oPUT) ∧ ∃ body, peekLine p = some (body ++ [nl]) ∧ (0 : UInt8) ∈ body ∧
    isErr (cLongFromLine (body ++ [nl])) = false) ∨
  (op = oPUT ∧ ∃ body v, peekLine p = some (body ++ [nl]) ∧ pyIntOfBytes body = .ok v ∧ v > ssizeMax) ∨
  (op = oAPPENDS ∧ p.stack = [] ∧ ∃ t r m, p.metastack = (t :: r) :: m ∧ hasExtend p.heap t = false) ∨
  (op = oADDITEMS ∧ p.stack = [] ∧ ∃ t r m, p.metastack = (t :: r) :: m ∧ isSetRef p.heap t = false) ∨
  (op = oFRAME ∧ ∃ b p', (pyUnpack 8).run p = .ok (b, p') ∧ leNat b ≤ ssizeMaxN ∧
    p'.inp.length < p'.pos + leNat b)

/-- No opcode of Python's run from `p` meets a `Hazard`. -/
def HazFree : Nat → PySt → Prop
  | 0, _ => True
  | f + 1, p =>
    match (pyRead 1).run p with
    | .ok (op :: _, p1) =>
      ¬ Hazard op p1 ∧
        match (pyStep op).run p1 with
        | .ok (Option.none, p2) => HazFree f p2
        | _ => True
    | _ => True

/-- On every data-only stream whose run meets none of the divergences on record,
`pickle.loads` and `pickle._loads` both raise or return equal objects. The
hypotheses are the type invariant on `bytes`, the model's scope, and exactly the
refuted cases. -/
def LoadsTwinsNarrow : Prop :=
  ∀ data : Bytes, data.length ≤ ssizeMaxN → DataOnly data →
    HazFree (data.length + 1) { inp := data } →
    SameOutcome (resolved (cLoads data)) (resolved (pyLoads data))

end PyLean.Pickle
