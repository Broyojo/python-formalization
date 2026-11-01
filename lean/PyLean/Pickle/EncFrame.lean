import PyLean.Pickle.EncSim

/-!
The two framers agree, and with that the two picklers: `_Framer` keeps the
current frame apart, C writes it into the output buffer behind a 9-byte
placeholder that `_Pickler_CommitFrame` fills in or removes.
-/

namespace PyLean.Pickle

open PyLean

def ph : Bytes := List.replicate frameHeaderSize 0xfe

/-- The framer states correspond. -/
def FR (py : PyFramer) (c : CFramer) : Prop :=
  match py.cur with
  | none => c.framing = false ∧ c.frameStart = none ∧ c.buf = py.out
  | some f => c.framing = true ∧
      ((c.frameStart = none ∧ f = [] ∧ c.buf = py.out) ∨
       (c.frameStart = some py.out.length ∧ c.buf = py.out ++ ph ++ f))

theorem ph_length : ph.length = 9 := by simp [ph, frameHeaderSize]

theorem commit_frame (c : CFramer) (out f : Bytes) (h1 : c.framing = true)
    (h2 : c.frameStart = some out.length) (h3 : c.buf = out ++ ph ++ f) :
    c.commit = { c with buf := pyCommit out f, frameStart := none } := by
  obtain ⟨buf, fs, fr⟩ := c
  simp only at h1 h2 h3
  subst h1 h2 h3
  have hlen : (out ++ ph ++ f).length - out.length - frameHeaderSize = f.length := by
    simp [ph_length, frameHeaderSize]
  have ht : (out ++ ph ++ f).take out.length = out := by
    rw [List.append_assoc]; simp
  have hd : (out ++ ph ++ f).drop (out.length + frameHeaderSize) = f := by
    apply List.drop_left'
    simp [ph_length, frameHeaderSize]
  simp only [CFramer.commit, hlen, ht, hd, pyCommit]
  split <;> simp [List.append_assoc]

theorem FR_step (py : PyFramer) (c : CFramer) (h : FR py c) (e : Event) (he : Clean e) :
    FR (PyFramer.step py e) (CFramer.step c e) := by
  obtain ⟨out, cur⟩ := py
  obtain ⟨buf, fs, fr⟩ := c
  cases e with
  | start => exact he.elim
  | finish => exact he.elim
  | w d =>
    cases cur with
    | none =>
      obtain ⟨h1, h2, h3⟩ := h
      simp only at h1 h2 h3
      subst h1 h2 h3
      simp [FR, PyFramer.step, CFramer.step, CFramer.write]
    | some f =>
      obtain ⟨h1, h2⟩ := h
      simp only at h1 h2
      subst h1
      rcases h2 with ⟨h2, h3, h4⟩ | ⟨h2, h3⟩
      · subst h2 h3 h4
        simp [FR, PyFramer.step, CFramer.step, CFramer.write, ph]
      · subst h2 h3
        simp [FR, PyFramer.step, CFramer.step, CFramer.write]
  | boundary =>
    cases cur with
    | none =>
      obtain ⟨h1, h2, h3⟩ := h
      simp only at h1 h2 h3
      subst h1 h2 h3
      simp [FR, PyFramer.step, CFramer.step]
    | some f =>
      obtain ⟨h1, h2⟩ := h
      simp only at h1 h2
      subst h1
      rcases h2 with ⟨h2, h3, h4⟩ | ⟨h2, h3⟩
      · subst h2 h3 h4
        simp [FR, PyFramer.step, CFramer.step, frameSizeTarget]
      · subst h2 h3
        have hlen : (out ++ ph ++ f).length - out.length - frameHeaderSize = f.length := by
          simp [ph_length, frameHeaderSize]
        simp only [CFramer.step, PyFramer.step, hlen]
        by_cases ht : f.length ≥ frameSizeTarget
        · have hc := commit_frame ⟨out ++ ph ++ f, some out.length, true⟩ out f rfl rfl rfl
          rw [if_pos ht, if_pos ht, hc]
          simp [FR]
        · rw [if_neg ht, if_neg ht]
          exact ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩
  | large hdr pay =>
    cases cur with
    | none =>
      obtain ⟨h1, h2, h3⟩ := h
      simp only at h1 h2 h3
      subst h1 h2 h3
      simp [FR, PyFramer.step, CFramer.step, CFramer.write, CFramer.commit]
    | some f =>
      obtain ⟨h1, h2⟩ := h
      simp only at h1 h2
      subst h1
      rcases h2 with ⟨h2, h3, h4⟩ | ⟨h2, h3⟩
      · subst h2 h3 h4
        simp [FR, PyFramer.step, CFramer.step, CFramer.write, CFramer.commit, pyCommit, frameSizeMin]
      · subst h2 h3
        have hc := commit_frame ⟨out ++ ph ++ f, some out.length, true⟩ out f rfl rfl rfl
        simp only [CFramer.step, PyFramer.step]
        rw [hc]
        simp [FR, CFramer.write]

theorem FR_fold (l : List Event) (hl : ∀ e ∈ l, Clean e) (py : PyFramer) (c : CFramer) (h : FR py c) :
    FR (l.foldl PyFramer.step py) (l.foldl CFramer.step c) := by
  induction l generalizing py c with
  | nil => exact h
  | cons e r ih =>
    exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) _ _
      (FR_step py c h e (hl e List.mem_cons_self))

theorem FR_finish (py : PyFramer) (c : CFramer) (h : FR py c) :
    (PyFramer.step py .finish).out = (CFramer.step c .finish).buf := by
  obtain ⟨out, cur⟩ := py
  obtain ⟨buf, fs, fr⟩ := c
  cases cur with
  | none =>
    obtain ⟨h1, h2, h3⟩ := h
    simp only at h1 h2 h3
    subst h1 h2 h3
    simp [PyFramer.step, CFramer.step, CFramer.commit]
  | some f =>
    obtain ⟨h1, h2⟩ := h
    simp only at h1 h2
    subst h1
    rcases h2 with ⟨h2, h3, h4⟩ | ⟨h2, h3⟩
    · subst h2 h3 h4
      simp [PyFramer.step, CFramer.step, CFramer.commit]
    · subst h2 h3
      have hc := commit_frame ⟨out ++ ph ++ f, some out.length, true⟩ out f rfl rfl rfl
      simp only [CFramer.step, PyFramer.step]
      rw [hc]
      by_cases hf : f.length > 0
      · rw [if_pos hf]
      · have hf0 : f = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hf0
        simp [pyCommit, frameSizeMin]

/-- Python's framer only sees the token stream. -/
def pyT (st : PyFramer) : Tok → PyFramer
  | .b x => PyFramer.step st (.w [x])
  | .bnd => PyFramer.step st .boundary
  | .lg h p => PyFramer.step st (.large h p)

theorem pyT_w (d : Bytes) (st : PyFramer) :
    (d.map Tok.b).foldl pyT st = PyFramer.step st (.w d) := by
  obtain ⟨out, cur⟩ := st
  induction d generalizing out cur with
  | nil => cases cur <;> simp [PyFramer.step]
  | cons x d ih =>
    simp only [List.map_cons, List.foldl_cons]
    cases cur with
    | none =>
      simp only [pyT, PyFramer.step]
      rw [ih]
      simp [PyFramer.step]
    | some f =>
      simp only [pyT, PyFramer.step]
      rw [ih]
      simp [PyFramer.step]

theorem pyFold_flat (a : List Event) (ha : ∀ e ∈ a, Clean e) (st : PyFramer) :
    a.reverse.foldl PyFramer.step st = (flat a).foldl pyT st := by
  induction a generalizing st with
  | nil => rfl
  | cons e r ih =>
    have hr := ih (fun x hx => ha x (List.mem_cons_of_mem _ hx)) st
    have he := ha e List.mem_cons_self
    simp only [List.reverse_cons, List.foldl_append, flat, hr, List.foldl_cons, List.foldl_nil]
    cases e with
    | w d => simp only [tok]; rw [pyT_w]
    | boundary => rfl
    | large h p => rfl
    | start => exact he.elim
    | finish => exact he.elim

def pyFrameFrom (st : PyFramer) (ev : List Event) : Bytes := (ev.reverse.foldl PyFramer.step st).out
def cFrameFrom (st : CFramer) (ev : List Event) : Bytes := (ev.reverse.foldl CFramer.step st).buf

/-- From corresponding states, related call sequences end in the same bytes. -/
theorem frames_agree (a b : List Event) (ha : ∀ e ∈ a, Clean e) (hb : ∀ e ∈ b, Clean e)
    (hf : flat a = flat b) (py0 : PyFramer) (c0 : CFramer) (h0 : FR py0 c0) :
    pyFrameFrom py0 (.finish :: .w [oSTOP] :: a) = cFrameFrom c0 (.finish :: .w [oSTOP] :: b) := by
  unfold pyFrameFrom cFrameFrom
  simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
  apply FR_finish
  have e1 : a.reverse.foldl PyFramer.step py0 = b.reverse.foldl PyFramer.step py0 := by
    rw [pyFold_flat a ha, pyFold_flat b hb, hf]
  rw [e1]
  refine FR_step _ _ ?_ (.w [oSTOP]) trivial
  exact FR_fold _ (fun x hx => hb x (List.mem_reverse.mp hx)) _ _ h0

/-- What `dump` writes before `save`. -/
def preEv (p : Nat) : List Event :=
  (if p ≥ 4 then [.start] else []) ++ (if p ≥ 2 then [.w [oPROTO, p.toUInt8]] else [])

def tailM : EncM Unit := do
  wr [oSTOP]
  emit .finish

theorem pyBody_eq (p : Nat) (x : PV) :
    pyBody p x {} = (pySave p x >>= fun _ => tailM) { memo := [], ev := preEv p } := by
  by_cases h2 : p ≥ 2 <;> by_cases h4 : p ≥ 4 <;>
    simp only [pyBody, preEv, h2, h4, ↓reduceIte, List.nil_append, List.append_nil] <;> rfl

theorem cBody_eq (p : Nat) (x : PV) :
    cBody p x {} = (cSave p x >>= fun _ => tailM) { memo := [], ev := preEv p } := by
  by_cases h2 : p ≥ 2 <;> by_cases h4 : p ≥ 4 <;>
    simp only [cBody, preEv, h2, h4, ↓reduceIte, List.nil_append, List.append_nil] <;> rfl

theorem bind_err {m : EncM Unit} {k : Unit → EncM Unit} {s : EncSt} {e : PyExc} (h : m s = .error e) :
    (m >>= k) s = .error e := by
  show (StateT.bind m k) s = _
  simp only [StateT.bind, bind, Except.bind, h]

theorem pyDumps_ok {x : PV} {protocol : Int} {p : Nat} {st : EncSt} (hp : pyProtocol protocol = .ok p)
    (h : pyBody p x {} = .ok ((), st)) : pyDumps x protocol = .ok (pyFrame st.ev.reverse) := by
  unfold pyDumps
  simp only [hp, bind, Except.bind, StateT.run, h, pure, Except.pure]

theorem cDumps_ok {x : PV} {protocol : Int} {p : Nat} {st : EncSt} (hp : cProtocol protocol = .ok p)
    (h : cBody p x {} = .ok ((), st)) : cDumps x protocol = .ok (cFrame st.ev.reverse) := by
  unfold cDumps
  simp only [hp, bind, Except.bind, StateT.run, h, pure, Except.pure]

theorem pyDumps_err {x : PV} {protocol : Int} {p : Nat} {e : PyExc} (hp : pyProtocol protocol = .ok p)
    (h : pyBody p x {} = .error e) : pyDumps x protocol = .error e := by
  unfold pyDumps
  simp only [hp, bind, Except.bind, StateT.run, h]

theorem cDumps_err {x : PV} {protocol : Int} {p : Nat} {e : PyExc} (hp : cProtocol protocol = .ok p)
    (h : cBody p x {} = .error e) : cDumps x protocol = .error e := by
  unfold cDumps
  simp only [hp, bind, Except.bind, StateT.run, h]

theorem preEv_FR (p : Nat) :
    FR ((preEv p).reverse.foldl PyFramer.step {}) ((preEv p).reverse.foldl CFramer.step {}) := by
  by_cases h2 : p ≥ 2 <;> by_cases h4 : p ≥ 4 <;>
    simp [preEv, h2, h4, FR, PyFramer.step, CFramer.step, CFramer.write]

/-- The picklers agree, exception class aside, on every plain value without the
batch shapes of `BatchOk`, whose ints pass C's size check, for every protocol
within C `long`. Each hypothesis is one of the refutations above. Both raise
for oversized objects, with different classes. -/
def DumpsTwinsNarrow : Prop :=
  ∀ (x : PV) (protocol : Int), longMin ≤ protocol → protocol ≤ longMax →
    BatchOk (effProto protocol) x → IntsOk x →
    SameOutcome (cDumps x protocol) (pyDumps x protocol)

theorem dumpsTwinsNarrow_proven : DumpsTwinsNarrow := by
  intro x protocol hlo hhi hb hi
  by_cases h5 : protocol > 5
  · have hc : cProtocol protocol = .error (.valueError "pickle protocol must be <= 5") := by
      unfold cProtocol
      rw [if_neg (by omega), if_neg (by omega), if_pos h5]
    have hp : pyProtocol protocol = .error (.valueError "pickle protocol must be <= 5") := by
      unfold pyProtocol
      rw [if_neg (by omega), if_neg (by omega)]
    unfold cDumps pyDumps
    simp only [hc, hp, bind, Except.bind]
    trivial
  have hp5 : effProto protocol ≤ 5 := by unfold effProto; split <;> omega
  have hc : cProtocol protocol = .ok (effProto protocol) := by
    unfold cProtocol effProto
    rw [if_neg (by omega)]
    by_cases hn : protocol < 0
    · rw [if_pos hn, if_pos hn]
    · rw [if_neg hn, if_neg h5, if_neg hn]
  have hp : pyProtocol protocol = .ok (effProto protocol) := by
    unfold pyProtocol effProto
    by_cases hn : protocol < 0
    · rw [if_pos hn, if_pos hn]
    · rw [if_neg hn, if_pos (by omega), if_neg hn]
  generalize effProto protocol = p at *
  let s0 : EncSt := { memo := [], ev := preEv p }
  have hrel : Rel (preEv p) s0 s0 :=
    ⟨rfl, [], [], rfl, rfl, rfl, by simp, by simp⟩
  have hsim := simSave (preEv p) p hp5 x hb hi s0 s0 hrel
  have e1 := pyBody_eq p x
  have e2 := cBody_eq p x
  cases hm : pySave p x s0 with
  | error e =>
    rw [hm] at hsim
    cases hn : cSave p x s0 with
    | ok r => rw [hn] at hsim; exact hsim.elim
    | error e' =>
      rw [cDumps_err hc (e2.trans (bind_err hn)), pyDumps_err hp (e1.trans (bind_err hm))]
      trivial
  | ok r =>
    rw [hm] at hsim
    cases hn : cSave p x s0 with
    | error e' => rw [hn] at hsim; exact hsim.elim
    | ok r' =>
      rw [hn] at hsim
      obtain ⟨u, st⟩ := r
      obtain ⟨u', st'⟩ := r'
      obtain ⟨_, a, b, ha, hb', hf, hca, hcb⟩ := hsim
      simp only at ha hb'
      have r1 : pyBody p x {} = .ok ((), { memo := st.memo, ev := .finish :: .w [oSTOP] :: st.ev }) :=
        e1.trans ((bind_run hm).trans rfl)
      have r2 : cBody p x {} = .ok ((), { memo := st'.memo, ev := .finish :: .w [oSTOP] :: st'.ev }) :=
        e2.trans ((bind_run hn).trans rfl)
      rw [cDumps_ok hc r2, pyDumps_ok hp r1]
      show cFrame _ = pyFrame _
      rw [ha, hb']
      have ef : ∀ l : List Event, (Event.finish :: .w [oSTOP] :: l ++ preEv p).reverse =
          (preEv p).reverse ++ (Event.finish :: .w [oSTOP] :: l).reverse := by
        intro l; simp
      simp only [List.cons_append] at ef
      unfold cFrame pyFrame
      rw [ef, ef, List.foldl_append, List.foldl_append]
      exact (frames_agree a b hca hcb hf _ _ (preEv_FR p)).symm

end PyLean.Pickle
