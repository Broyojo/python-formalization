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
  /-- No key has gone to `memo_dict`, so `memo_len` is `len(memo)`. -/
  memoDict : c.memoDict = []
  memoLen : c.memoLen = p.memo.length
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

theorem fileRead_append (inp : Bytes) (pos a b : Nat) :
    (inp.drop pos).take a ++ (inp.drop (pos + ((inp.drop pos).take a).length)).take b =
      (inp.drop pos).take (a + b) := by
  rw [List.take_add]
  congr 2
  by_cases h : a ≤ (inp.drop pos).length
  · rw [List.length_take_of_le h, List.drop_drop]
  · have h' : (inp.drop pos).length ≤ a := by omega
    rw [List.length_take, Nat.min_eq_right h', List.drop_of_length_le h', List.length_drop]
    exact List.drop_of_length_le (by omega)

theorem with_pos (p : PySt) (n : Nat) (h : p.pos = n) : { p with pos := n } = p := by
  subst h; rfl

/-- On the `BytesIO`, reading in chunks is reading once: the loop stops early only
after a short read, and then nothing is left. -/
theorem chunkedLoop_run (size : Nat) (fuel cursize : Nat) (p : PySt) (start : Nat) (b : Bytes)
    (hb : b = (p.inp.drop start).take cursize) (hp : p.pos = start + b.length)
    (hle : cursize ≤ size) (hfuel : size - cursize ≤ fuel) (hc : cursize = 0 → size = 0) :
    (chunkedLoop fuel size cursize b).run p =
      .ok ((p.inp.drop start).take size,
        { p with pos := start + ((p.inp.drop start).take size).length }) := by
  induction fuel generalizing cursize p b with
  | zero =>
    have e : cursize = size := by omega
    subst e
    subst hb
    show Except.ok _ = _
    rw [with_pos p _ hp]
  | succ fuel ih =>
    by_cases hcond : cursize < size ∧ b.length = cursize
    · have hd : min cursize (size - cursize) ≠ 0 := by
        have := hc
        omega
      generalize hdelta : min cursize (size - cursize) = delta at hd
      have hstep : (chunkedLoop (fuel + 1) size cursize b).run p =
          (do let d ← fileRead delta
              chunkedLoop fuel size (cursize + delta) (b ++ d)).run p := by
        simp only [chunkedLoop]
        rw [if_pos hcond, hdelta]
      rw [hstep, pyRun_bind, fileRead_run]
      dsimp only
      subst hb
      have hkey := fileRead_append p.inp start cursize delta
      rw [← hp] at hkey
      exact ih (cursize + delta) { p with pos := p.pos + ((p.inp.drop p.pos).take delta).length } _
        hkey (by show p.pos + _ = _; rw [List.length_append]; omega) (by omega) (by omega) (by omega)
    · have hstep : (chunkedLoop (fuel + 1) size cursize b).run p = .ok (b, p) := by
        simp only [chunkedLoop]
        rw [if_neg hcond]
        rfl
      rw [hstep]
      have hb2 : b = (p.inp.drop start).take size := by
        by_cases hlt : cursize < size
        · have hshort : b.length ≠ cursize := fun e => hcond ⟨hlt, e⟩
          subst hb
          have h1 : ((p.inp.drop start).take cursize).length < cursize := by
            have := List.length_take_le cursize (p.inp.drop start)
            omega
          rw [List.length_take] at h1
          rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
        · have e : cursize = size := by omega
          subst e
          exact hb
      rw [← hb2, with_pos p _ hp]

theorem chunkedFileRead_run (n : Nat) (p : PySt) : (chunkedFileRead n).run p = (fileRead n).run p := by
  have hstep : (chunkedFileRead n).run p =
      (do let b ← fileRead (min n minReadBufSize)
          chunkedLoop n n (min n minReadBufSize) b).run p := rfl
  rw [hstep, pyRun_bind, fileRead_run, fileRead_run]
  dsimp only
  exact chunkedLoop_run n n _ { p with pos := p.pos + ((p.inp.drop p.pos).take (min n minReadBufSize)).length }
    p.pos _ rfl rfl (by omega) (by omega) (by simp [minReadBufSize])

theorem read_none (p : PySt) (h : p.frame = none) (n : Nat) :
    (pyRead n).run p = (fileRead n).run p := by
  obtain ⟨inp, pos, frame, stack, mt, memo, heap, proto⟩ := p
  simp only at h
  subst h
  exact chunkedFileRead_run n _

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

/-- The `PUT` family stores at `idx`: the index `pyStep op` would use. -/
def putIndex (op : UInt8) (p : PySt) : Option Nat :=
  if op = oBINPUT then
    match (pyRead 1).run p with
    | .ok ([b], _) => some b.toNat
    | _ => none
  else if op = oLONG_BINPUT then
    match (pyUnpack 4).run p with
    | .ok (b, _) => some (leNat b)
    | _ => none
  else if op = oPUT then
    match peekLine p with
    | some l =>
      match pyIntOfBytes l.dropLast with
      | .ok v => if v ≥ 0 then some v.toNat else none
      | .error _ => none
    | none => none
  else none

/-- The bytes a `BINBYTES`, `BINBYTES8` or `BYTEARRAY8` opcode declares. -/
def countedSize (op : UInt8) (p : PySt) : Option Nat :=
  if op = oBINBYTES then
    match (pyUnpack 4).run p with
    | .ok (b, _) => some (leNat b)
    | _ => none
  else if op = oBINBYTES8 ∨ op = oBYTEARRAY8 then
    match (pyUnpack 8).run p with
    | .ok (b, _) => some (leNat b)
    | _ => none
  else none

/-- The divergences on record, for opcode `op` about to run from `p`. Each is one
refuted entry: an `INT` line as in `pickle-int-line-twins` and its narrowing,
a line with NUL C accepts (`pickle-long-line-twins`), a `PUT` index above
`sys.maxsize` (`pickle-put-twins`), a sparse `PUT` (`pickle-memoize-twins`), a
counted payload that crosses the end of a frame after a whole 1 MiB chunk
(`pickle-frame-chunk-straddle`).

The last two are stated from Python's state, which is wider than the refuted
cases: every `PUT` at or past 32 above twice `len(memo)`, which is every key C could
send to `memo_dict`, and every payload of at least 1 MiB that does not fit in the
frame. -/
def Hazard (op : UInt8) (p : PySt) : Prop :=
  (op = oINT ∧ ∃ body, peekLine p = some (body ++ [nl]) ∧
    (((0 : UInt8) ∈ body ∧ isErr (cLoadIntLine (body ++ [nl])) = false) ∨
      FastOverLimit body)) ∨
  (op = oLONG ∧ ∃ body, peekLine p = some (body ++ [nl]) ∧ (0 : UInt8) ∈ body ∧
    isErr (cLoadLongLine (body ++ [nl])) = false) ∨
  ((op = oGET ∨ op = oPUT) ∧ ∃ body, peekLine p = some (body ++ [nl]) ∧ (0 : UInt8) ∈ body ∧
    isErr (cLongFromLine (body ++ [nl])) = false) ∨
  (op = oPUT ∧ ∃ body v, peekLine p = some (body ++ [nl]) ∧ pyIntOfBytes body = .ok v ∧ v > ssizeMax) ∨
  (∃ idx, putIndex op p = some idx ∧ idx ≥ 32 ∧ idx > p.memo.length * 2) ∨
  (∃ size f fp, countedSize op p = some size ∧ p.frame = some (f, fp) ∧
    minReadBufSize ≤ size ∧ fp < f.length ∧ f.length < fp + size + 8)

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

/-- `FRAME n` at the start of a stream. With fewer than `n` bytes left, both
unpicklers raise: `EOFError` from `_Unframer.load_frame`, and C's read of the whole
frame fails. Otherwise both hold exactly the next `n` bytes as the frame and go on
from its first byte. -/
def FrameRead : Prop :=
  ∀ (n : Nat) (body : Bytes), n ≤ ssizeMaxN →
    let data := oFRAME :: leBytes n 8 ++ body
    let p : PySt := { inp := data, pos := 1 }
    let c : CSt := { inp := data, idx := 1, inputLen := data.length }
    (body.length < n → pyLoadFrame.run p = .error (eofError "") ∧ ∃ e, cLoadFrame.run c = .error e) ∧
    (n ≤ body.length →
      pyLoadFrame.run p = .ok ((), { p with pos := 9 + n, frame := some (body.take n, 0) }) ∧
      cLoadFrame.run c = .ok ((), { c with idx := 9, inputLen := 9 + n, frameEnd := some (9 + n),
                                           savedInputLen := data.length }))

/-- On every data-only stream whose run meets none of the divergences on record,
`pickle.loads` and `pickle._loads` both raise or return equal objects. The
hypotheses are the type invariant on `bytes`, the model's scope, and exactly the
refuted cases. The hazards say which refuted cases those are. -/
def LoadsTwinsNarrow : Prop :=
  ∀ data : Bytes, data.length ≤ ssizeMaxN → DataOnly data →
    HazFree (data.length + 1) { inp := data } →
    SameOutcome (resolved (cLoads data)) (resolved (pyLoads data))

theorem cDiscard_run {α : Type} (m : CM α) (c : CSt) :
    (discard m).run c = (m >>= fun _ => pure ()).run c := rfl

theorem cLoadFrame_none (c : CSt) (h : c.frameEnd = none) (hf : c.idx + 8 ≤ c.inputLen) :
    cLoadFrame.run c = (cOpenFrame ((c.inp.drop c.idx).take 8)).run { c with idx := c.idx + 8 } := by
  have h2 : cLoadFrame = (cRead 8 >>= fun b => do
      let s ← get
      match s.frameEnd with
      | some fe =>
        if s.idx < fe then cThrow (unpicklingError "beginning of a new frame before end of current frame")
        else
          set { s with inputLen := s.savedInputLen, frameEnd := none }
          cOpenFrame b
      | none => cOpenFrame b) := rfl
  rw [h2, cRun_bind, cRead_fast c 8 hf]
  dsimp only
  generalize (c.inp.drop c.idx).take 8 = b
  cases c
  simp only at h
  subst h
  rfl

/-- The body of `cOpenFrame` after the size check. -/
theorem cOpenFrame_some {b : Bytes} {n : Nat} (hb : calcBinsize b = some n) (c : CSt) :
    (cOpenFrame b).run c = (discard (cRead n) >>= fun _ =>
      modify fun (s : CSt) =>
        let start := s.idx - n
        { s with idx := start, frameEnd := some (start + n), savedInputLen := s.inputLen,
                 inputLen := start + n }).run c := by
  unfold cOpenFrame
  rw [hb]

theorem cOpenFrame_err {b : Bytes} {n : Nat} {c : CSt} {e : PyExc} (hb : calcBinsize b = some n)
    (he : (cRead n).run c = .error e) : (cOpenFrame b).run c = .error e := by
  rw [cOpenFrame_some hb, cRun_bind, cDiscard_run, cRun_bind, he]

theorem cOpenFrame_ok {b : Bytes} {n : Nat} {c : CSt} (hb : calcBinsize b = some n)
    (hf : c.idx + n ≤ c.inputLen) :
    (cOpenFrame b).run c = .ok ((), { c with
      idx := c.idx + n - n, frameEnd := some (c.idx + n - n + n), savedInputLen := c.inputLen,
      inputLen := c.idx + n - n + n }) := by
  rw [cOpenFrame_some hb, cRun_bind, cDiscard_run, cRun_bind, cRead_fast c n hf]
  rfl

theorem frameRead_proven : FrameRead := by
  intro n body hn
  dsimp only
  generalize hdata : oFRAME :: leBytes n 8 ++ body = data
  have hl8 : (leBytes n 8).length = 8 := leBytes_length n 8
  have hlen : data.length = 9 + body.length := by
    rw [← hdata]
    simp only [List.length_cons, List.length_append, hl8]
  have hhdr : (data.drop 1).take 8 = leBytes n 8 := by
    rw [← hdata]
    exact List.take_left' hl8
  have hrest : data.drop 9 = body := by
    rw [← hdata]
    exact List.drop_left' (l₁ := oFRAME :: leBytes n 8) (by simp [hl8])
  have hsz : leNat (leBytes n 8) = n := by
    rw [leNat_leBytes]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hn (by decide))
  have hmax : ¬ n > ssizeMaxN := by omega
  -- Python, up to the read of the frame
  have hunpack : (pyUnpack 8).run ({ inp := data, pos := 1 } : PySt) =
      .ok (leBytes n 8, { inp := data, pos := 9 }) := by
    have h1 : (pyRead 8).run ({ inp := data, pos := 1 } : PySt) =
        .ok (leBytes n 8, { inp := data, pos := 9 }) := by
      rw [read_none _ rfl, fileRead_run]
      simp only [hhdr, hl8]
    have h2 : (pyUnpack 8).run ({ inp := data, pos := 1 } : PySt) =
        (do let d ← pyRead 8
            if d.length = 8 then return d
            else pyThrow (structError s!"unpack requires a buffer of {8} bytes")).run
          ({ inp := data, pos := 1 } : PySt) := rfl
    rw [h2, pyRun_bind, h1]
    dsimp only
    rw [if_pos hl8]
    rfl
  have hframe : pyLoadFrame.run ({ inp := data, pos := 1 } : PySt) =
      (pyReadFrame n).run ({ inp := data, pos := 9 } : PySt) := by
    have h2 : pyLoadFrame.run ({ inp := data, pos := 1 } : PySt) =
        (pyUnpack 8 >>= fun d =>
          if leNat d > ssizeMaxN then
            pyThrow (.valueError s!"frame size > sys.maxsize: {leNat d}")
          else pyStartFrame (leNat d)).run ({ inp := data, pos := 1 } : PySt) := rfl
    rw [h2, pyRun_bind, hunpack]
    dsimp only
    rw [hsz, if_neg hmax]
    rfl
  have hread : (chunkedFileRead n).run ({ inp := data, pos := 9 } : PySt) =
      .ok (body.take n, { inp := data, pos := 9 + (body.take n).length }) := by
    rw [chunkedFileRead_run, fileRead_run]
    simp only [hrest]
  have hpy : (pyReadFrame n).run ({ inp := data, pos := 9 } : PySt) =
      if (body.take n).length < n then .error (eofError "")
      else .ok ((), { inp := data, pos := 9 + (body.take n).length,
                      frame := some (body.take n, 0) }) := by
    have h2 : (pyReadFrame n).run ({ inp := data, pos := 9 } : PySt) =
        (do let d ← chunkedFileRead n
            if d.length < n then pyThrow (eofError "")
            else modify fun (s : PySt) => { s with frame := some (d, 0) }).run
          ({ inp := data, pos := 9 } : PySt) := rfl
    rw [h2, pyRun_bind, hread]
    dsimp only
    split <;> rfl
  -- C, up to the read of the frame
  have hc8 : 1 + 8 ≤ data.length := by omega
  have h3 : calcBinsize (leBytes n 8) = some n := by
    unfold calcBinsize
    dsimp only
    rw [hsz, if_neg hmax]
  have hopen : cLoadFrame.run ({ inp := data, idx := 1, inputLen := data.length } : CSt) =
      (cOpenFrame (leBytes n 8)).run ({ inp := data, idx := 9, inputLen := data.length } : CSt) := by
    rw [cLoadFrame_none _ rfl hc8]
    dsimp only
    rw [hhdr]
  constructor
  · intro hshort
    have hlt : (body.take n).length < n := by
      rw [List.length_take]; omega
    refine ⟨by rw [hframe, hpy, if_pos hlt], ?_⟩
    obtain ⟨e, he⟩ := cRead_noframe ({ inp := data, idx := 9, inputLen := data.length } : CSt) n
      (by dsimp only; omega) rfl
    exact ⟨e, by rw [hopen, cOpenFrame_err h3 he]⟩
  · intro hfull
    have hl : (body.take n).length = n := by
      rw [List.length_take]; omega
    refine ⟨by rw [hframe, hpy, if_neg (by omega), hl], ?_⟩
    rw [hopen, cOpenFrame_ok h3 (by dsimp only; omega)]
    have e9 : 9 + n - n = 9 := by omega
    simp only [e9]

end PyLean.Pickle
