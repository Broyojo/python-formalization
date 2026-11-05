import PyLean.Pickle.ToolsSteps

/-!
The sanity checks of `dis` (`Lib/pickletools.py:2448-2459`, `:2491-2592`), each
with its exact message, at any position of any stream and from any emulated state,
and the text of a clean `STOP`.
-/

namespace PyLean.Pickle

open PyLean

/-- The argument of an opcode has a `repr`: true of every argument except floats
and characters outside Latin-1, which the model does not render, and ints past the
4300-digit limit, whose `repr` raises. -/
def ReprOk (arg : Option TV) : Prop := ∀ a, arg = some a → ∃ r, tvRepr a = .ok r

theorem strReprCP_true_ok (q c : Nat) : ∃ r, strReprCP true q c = .ok r := by
  unfold strReprCP
  repeat' split
  all_goals first | exact ⟨_, rfl⟩ | simp_all

theorem mapM_ok {α β : Type} (f : α → Py β) (hf : ∀ a, ∃ b, f a = .ok b) :
    ∀ l : List α, ∃ r, l.mapM f = .ok r
  | [] => ⟨[], rfl⟩
  | a :: l => by
    obtain ⟨b, hb⟩ := hf a
    obtain ⟨r, hr⟩ := mapM_ok f hf l
    refine ⟨b :: r, ?_⟩
    simp only [List.mapM_cons, hb, hr]
    rfl

theorem mapM_strReprCP_ne (q : Nat) (s : List Nat) (e : PyExc) :
    s.mapM (strReprCP true q) ≠ .error e := by
  obtain ⟨r, hr⟩ := mapM_ok (strReprCP true q) (strReprCP_true_ok q) s
  rw [hr]
  intro h
  cases h

theorem strRepr_true_ok (s : List Nat) : ∃ r, strRepr true s = .ok r := by
  cases hres : strRepr true s with
  | ok r => exact ⟨r, rfl⟩
  | error e =>
    exfalso
    unfold strRepr at hres
    simp only [bind, Except.bind] at hres
    split at hres
    · rename_i err h
      exact mapM_strReprCP_ne _ s err h
    · cases hres

theorem strRepr_true_ne (s : List Nat) (e : PyExc) : strRepr true s ≠ .error e := by
  obtain ⟨r, hr⟩ := strRepr_true_ok s
  rw [hr]
  intro h
  cases h

theorem argText_ok (info : OpInfo) (arg : Option TV) (mm : Option String) (line : String)
    (h : ReprOk arg) : ∃ l, argText info arg mm line = .ok l := by
  cases hres : argText info arg mm line with
  | ok l => exact ⟨l, rfl⟩
  | error e =>
    exfalso
    unfold argText at hres
    split at hres
    · cases hres
    · cases harg : arg with
      | none =>
        simp only [harg, bind, Except.bind, pure, Except.pure] at hres
        cases mm <;> cases hres
      | some a =>
        obtain ⟨r, hr⟩ := h a harg
        simp only [harg, bind, Except.bind, pure, Except.pure] at hres
        split at hres
        all_goals
          split at hres
          · rename_i err herr
            first
              | exact strRepr_true_ne _ _ herr
              | (rw [hr] at herr; cases herr)
          · cases mm <;> cases hres

/-- `name in ("PUT", "BINPUT", "LONG_BINPUT", "MEMOIZE")`, `:2522`. -/
def putName (name : String) : Bool :=
  name == "PUT" || name == "BINPUT" || name == "LONG_BINPUT" || name == "MEMOIZE"

/-- `name in ("GET", "BINGET", "LONG_BINGET")`, `:2535`. -/
def getName (name : String) : Bool := name == "GET" || name == "BINGET" || name == "LONG_BINGET"

/-- The first part of each line, `:2482-2486`, without colours. -/
def disLine (i : Nat) (s : DisSt) (op : GenOp) : String :=
  pad4 (codeRepr op.info.code) ++ " " ++ spaces (i * s.markstack.length) ++ op.info.name

/-- What has been printed once the position is, `:2476-2477`. -/
def posText : Option Nat → String
  | some p => fmt5 p ++ ": "
  | none => ""

theorem disStep_err (i a : Nat) (s : DisSt) (op : GenOp) (m : MarkRes) (k : MemoRes) (l msg : String)
    (hm : markPhase op.info s.stack s.markstack = .ok m)
    (hk : memoPhase op.info op.arg m.stack s.memo m.markmsg m.errormsg = .ok k)
    (hl : argText op.info op.arg k.markmsg (disLine i s op) = .ok l) (he : k.errormsg = some msg) :
    ∃ out, disStep i a s op = .error (.valueError msg, out) := by
  unfold disStep
  simp only [bind, Except.bind, dmLift, hm, hk]
  simp only [disLine] at hl
  rw [hl]
  dsimp only
  rw [he]
  exact ⟨_, rfl⟩

theorem disStep_pop (i a : Nat) (s : DisSt) (op : GenOp) (m : MarkRes) (k : MemoRes) (l : String)
    (hm : markPhase op.info s.stack s.markstack = .ok m)
    (hk : memoPhase op.info op.arg m.stack s.memo m.markmsg m.errormsg = .ok k)
    (hl : argText op.info op.arg k.markmsg (disLine i s op) = .ok l) (he : k.errormsg = none)
    (hlt : m.stack.length < m.numtopop) :
    ∃ out, disStep i a s op = .error (.valueError
      s!"tries to pop {m.numtopop} items from stack with only {m.stack.length} items", out) := by
  unfold disStep
  simp only [bind, Except.bind, dmLift, hm, hk]
  simp only [disLine] at hl
  rw [hl]
  dsimp only
  rw [he]
  dsimp only
  simp only [stackPhase, if_pos hlt]
  exact ⟨_, rfl⟩

theorem disStep_ok (i a : Nat) (s : DisSt) (op : GenOp) (m : MarkRes) (k : MemoRes) (l : String)
    (hm : markPhase op.info s.stack s.markstack = .ok m)
    (hk : memoPhase op.info op.arg m.stack s.memo m.markmsg m.errormsg = .ok k)
    (hl : argText op.info op.arg k.markmsg (disLine i s op) = .ok l) (he : k.errormsg = none)
    (hge : ¬ m.stack.length < m.numtopop) :
    disStep i a s op = .ok
      { stack := k.after.reverse ++ m.stack.drop m.numtopop, memo := k.memo,
        maxproto := max s.maxproto op.info.proto,
        markstack := if k.after.contains markObj then op.pos :: m.markstack else m.markstack,
        annocol := (annotateLine op.info a s.annocol l).2,
        out := s.out ++ posText op.pos ++ (annotateLine op.info a s.annocol l).1 ++ "\n" } := by
  unfold disStep
  simp only [bind, Except.bind, dmLift, hm, hk]
  simp only [disLine] at hl
  rw [hl]
  dsimp only
  rw [he]
  dsimp only
  simp only [stackPhase, if_neg hge]
  cases op.pos <;> simp only [posText, String.append_assoc, String.empty_append, String.append_empty] <;> rfl

theorem disLoop_step (t : Bool) (i a : Nat) (d : Bytes) (f pos : Nat) (s : DisSt) (op : GenOp)
    (pos' : Nat) (hg : genopStep t pos d = .ok (op, pos')) :
    disLoop t i a d (f + 1) pos s =
      match disStep i a s op with
      | .error (e, out) => (out, some e)
      | .ok s' =>
        if op.info.code == oSTOP then disEnd s'
        else disLoop t i a d f pos' s' := by
  rw [disLoop, hg]
  rfl

/-- The step fails with the check's message. -/
theorem disLoop_check (t : Bool) (i a : Nat) (d : Bytes) (f pos : Nat) (s : DisSt) (op : GenOp)
    (pos' : Nat) (hg : genopStep t pos d = .ok (op, pos')) (m : MarkRes) (k : MemoRes) (msg : String)
    (hm : markPhase op.info s.stack s.markstack = .ok m)
    (hk : memoPhase op.info op.arg m.stack s.memo m.markmsg m.errormsg = .ok k)
    (hr : ReprOk op.arg) (he : k.errormsg = some msg) :
    (disLoop t i a d (f + 1) pos s).2 = some (.valueError msg) := by
  obtain ⟨l, hl⟩ := argText_ok op.info op.arg k.markmsg (disLine i s op) hr
  obtain ⟨out, ho⟩ := disStep_err i a s op m k l msg hm hk hl he
  rw [disLoop_step t i a d f pos s op pos' hg, ho]

theorem markPhase_pass (info : OpInfo) (stack : List String) (ms : List (Option Nat))
    (h1 : markObj ∉ info.before) (h2 : ¬(info.name = "POP" ∧ stack.head? = some markObj)) :
    markPhase info stack ms = .ok ⟨stack, ms, info.before.length, none, none⟩ := by
  unfold markPhase
  rw [if_neg]
  intro hc
  simp only [Bool.or_eq_true, List.contains_iff_mem, Bool.and_eq_true, beq_iff_eq] at hc
  rcases hc with hc | hc
  · exact h1 hc
  · exact h2 hc

theorem markPhase_nomark (info : OpInfo) (stack : List String) (h : markObj ∈ info.before) :
    markPhase info stack [] =
      .ok ⟨stack, [], info.before.length, none, some "no MARK exists on stack"⟩ := by
  unfold markPhase
  rw [if_pos (by simp [List.contains_iff_mem, h])]

theorem memoPhase_other (info : OpInfo) (arg : Option TV) (st : List String) (memo : List (Int × String))
    (mm em : Option String) (h1 : putName info.name = false) (h2 : getName info.name = false) :
    memoPhase info arg st memo mm em = .ok ⟨memo, info.after, mm, em⟩ := by
  unfold memoPhase
  unfold putName at h1
  unfold getName at h2
  simp only [h1, h2, Bool.false_eq_true, if_false]

theorem memoPhase_put_empty (info : OpInfo) (arg : Option TV) (memo : List (Int × String))
    (mm em : Option String) (h : putName info.name = true) :
    ∃ mm', memoPhase info arg [] memo mm em =
      .ok ⟨memo, info.after, mm', some "stack is empty -- can't store into memo"⟩ := by
  unfold memoPhase
  unfold putName at h
  simp only [h, if_true]
  exact ⟨_, rfl⟩

theorem memoPhase_put_mark (info : OpInfo) (arg : Option TV) (r : List String)
    (memo : List (Int × String)) (mm em : Option String) (h : putName info.name = true) :
    ∃ mm', memoPhase info arg (markObj :: r) memo mm em =
      .ok ⟨memo, info.after, mm', some "can't store markobject in the memo"⟩ := by
  unfold memoPhase
  unfold putName at h
  simp only [h, if_true, beq_self_eq_true]
  exact ⟨_, rfl⟩

theorem memoPhase_get_missing (info : OpInfo) (arg : Option TV) (a : TV) (r : String) (st : List String)
    (memo : List (Int × String)) (mm em : Option String) (h1 : putName info.name = false)
    (h2 : getName info.name = true) (ha : arg = some a) (hr : tvRepr a = .ok r)
    (hl : memo.lookup (memoKey arg) = none) :
    memoPhase info arg st memo mm em =
      .ok ⟨memo, info.after, mm, some s!"memo key {r} has never been stored into"⟩ := by
  unfold memoPhase
  unfold putName at h1
  unfold getName at h2
  simp only [h1, h2, Bool.false_eq_true, if_false, if_true, hl]
  subst ha
  simp only [hr]

/-! ## Facts of the opcode table -/

theorem table_mark_not_memo :
    ∀ info ∈ opTable, markObj ∈ info.before → putName info.name = false ∧ getName info.name = false := by
  decide +kernel

theorem table_memo_no_mark :
    ∀ info ∈ opTable, (putName info.name = true ∨ getName info.name = true) →
      markObj ∉ info.before ∧ info.name ≠ "POP" ∧ ¬(putName info.name = true ∧ getName info.name = true) := by
  decide +kernel

theorem table_pop : ∀ info ∈ opTable, info.name = "POP" → info.before.length = 1 := by
  decide +kernel

/-- The `STOP` opcode, `:2137-2147`. -/
def stopInfo : OpInfo :=
  { code := 0x2e, name := "STOP", arg := "", proto := 0, before := ["any"], after := [],
    doc := "Stop the unpickling machine." }

theorem table_stop : ∀ info ∈ opTable, info.code = oSTOP → info = stopInfo := by
  decide +kernel

/-! ## The checks -/

/-- `dis` (`Lib/pickletools.py:2423-2592`), every outcome of one opcode, at any
position of any stream and from any emulated stack, memo and mark stack:

* `genops`: when `genops` raises, `dis` raises the same, after what it printed;
* `nomark`: an opcode that needs a MARK with none on the mark stack raises
  `"no MARK exists on stack"` (`:2518-2519`);
* `putempty`, `putmark`: a PUT, BINPUT, LONG_BINPUT or MEMOIZE on an empty stack, or
  with the markobject on top, raises `"stack is empty -- can't store into memo"` or
  `"can't store markobject in the memo"` (`:2529-2532`);
* `getmissing`: a GET, BINGET or LONG_BINGET of a key the memo lacks raises
  `"memo key %r has never been stored into"` (`:2535-2540`);
* `pop`: any other opcode that pops more items than the stack holds raises
  `"tries to pop %d items from stack with only %d items"` (`:2575-2577`);
* `notempty`: a `STOP` that leaves items on the stack raises
  `"stack not empty after STOP: %r"` naming them bottom first (`:2591-2592`);
* `clean`: a `STOP` on a one-item stack prints its line and the highest protocol,
  and raises nothing.

Every check is stated with the text of the source, so a `dis` that drops one of
them, or that always raises, fails. -/
def DisChecks : Prop :=
  (∀ (t : Bool) (i a : Nat) (d : Bytes) (f pos : Nat) (s : DisSt) (e : PyExc),
    genopStep t pos d = .error e → disLoop t i a d (f + 1) pos s = (s.out, some e)) ∧
  (∀ (t : Bool) (i a : Nat) (d : Bytes) (f pos : Nat) (s : DisSt) (op : GenOp) (pos' : Nat),
    genopStep t pos d = .ok (op, pos') → ReprOk op.arg →
    markObj ∈ op.info.before → s.markstack = [] →
    (disLoop t i a d (f + 1) pos s).2 = some (.valueError "no MARK exists on stack")) ∧
  (∀ (t : Bool) (i a : Nat) (d : Bytes) (f pos : Nat) (s : DisSt) (op : GenOp) (pos' : Nat),
    genopStep t pos d = .ok (op, pos') → ReprOk op.arg →
    putName op.info.name = true → s.stack = [] →
    (disLoop t i a d (f + 1) pos s).2 =
      some (.valueError "stack is empty -- can't store into memo")) ∧
  (∀ (t : Bool) (i a : Nat) (d : Bytes) (f pos : Nat) (s : DisSt) (op : GenOp) (pos' : Nat),
    genopStep t pos d = .ok (op, pos') → ReprOk op.arg →
    putName op.info.name = true → s.stack.head? = some markObj →
    (disLoop t i a d (f + 1) pos s).2 = some (.valueError "can't store markobject in the memo")) ∧
  (∀ (t : Bool) (i a : Nat) (d : Bytes) (f pos : Nat) (s : DisSt) (op : GenOp) (pos' : Nat)
      (x : TV) (r : String),
    genopStep t pos d = .ok (op, pos') → getName op.info.name = true → op.arg = some x →
    tvRepr x = .ok r → s.memo.lookup (memoKey op.arg) = none →
    (disLoop t i a d (f + 1) pos s).2 =
      some (.valueError s!"memo key {r} has never been stored into")) ∧
  (∀ (t : Bool) (i a : Nat) (d : Bytes) (f pos : Nat) (s : DisSt) (op : GenOp) (pos' : Nat),
    genopStep t pos d = .ok (op, pos') → ReprOk op.arg →
    markObj ∉ op.info.before → putName op.info.name = false → getName op.info.name = false →
    s.stack.length < op.info.before.length →
    (disLoop t i a d (f + 1) pos s).2 = some (.valueError
      s!"tries to pop {op.info.before.length} items from stack with only {s.stack.length} items")) ∧
  (∀ (t : Bool) (i a : Nat) (d : Bytes) (f pos : Nat) (s : DisSt) (op : GenOp) (pos' : Nat)
      (x y : String) (r : List String),
    genopStep t pos d = .ok (op, pos') → op.info.code = oSTOP → s.stack = x :: y :: r →
    (disLoop t i a d (f + 1) pos s).2 = some (.valueError
      s!"stack not empty after STOP: [{", ".intercalate (y :: r).reverse}]")) ∧
  (∀ (t : Bool) (i : Nat) (d : Bytes) (f pos : Nat) (s : DisSt) (op : GenOp) (pos' : Nat) (x : String),
    genopStep t pos d = .ok (op, pos') → op.info.code = oSTOP → s.stack = [x] →
    disLoop t i 0 d (f + 1) pos s =
      (s.out ++ posText op.pos ++ ".    " ++ spaces (i * s.markstack.length) ++ "STOP\n" ++
        s!"highest protocol among opcodes = {max s.maxproto 0}\n", none))

theorem stop_facts {t : Bool} {pos : Nat} {d : Bytes} {op : GenOp} {pos' : Nat}
    (hg : genopStep t pos d = .ok (op, pos')) (hc : op.info.code = oSTOP) :
    op.info = stopInfo ∧ op.arg = none := by
  obtain ⟨hm, harg, _, _⟩ := genopStep_ok_info hg
  have hi := table_stop op.info hm hc
  exact ⟨hi, harg (by rw [hi]; rfl)⟩

theorem stop_step (i a : Nat) (s : DisSt) (op : GenOp) (hi : op.info = stopInfo) (ha : op.arg = none)
    (x : String) (r : List String) (hs : s.stack = x :: r) :
    disStep i a s op =
      .ok { stack := r, memo := s.memo, maxproto := max s.maxproto 0, markstack := s.markstack,
            annocol := (annotateLine stopInfo a s.annocol (disLine i s op)).2,
            out := s.out ++ posText op.pos ++ (annotateLine stopInfo a s.annocol (disLine i s op)).1 ++ "\n" } := by
  have hm : markPhase op.info s.stack s.markstack = .ok ⟨s.stack, s.markstack, 1, none, none⟩ := by
    rw [hi, markPhase_pass stopInfo s.stack s.markstack (by decide) (by simp [stopInfo])]
    rfl
  have hk : memoPhase op.info op.arg s.stack s.memo none none = .ok ⟨s.memo, [], none, none⟩ := by
    rw [hi, memoPhase_other stopInfo op.arg s.stack s.memo none none (by decide +kernel)
      (by decide +kernel)]
    rfl
  have hl : argText op.info op.arg none (disLine i s op) = .ok (disLine i s op) := by
    unfold argText; rw [ha]; rfl
  rw [disStep_ok i a s op _ _ _ hm hk hl rfl (by rw [hs]; simp)]
  rw [hi, hs]
  rfl

theorem disChecks_proven : DisChecks := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t i a d f pos s e hg
    rw [disLoop, hg]
  · intro t i a d f pos s op pos' hg hr hb hms
    obtain ⟨hmem, _, _, _⟩ := genopStep_ok_info hg
    obtain ⟨h1, h2⟩ := table_mark_not_memo op.info hmem hb
    have hm := markPhase_nomark op.info s.stack hb
    rw [← hms] at hm
    exact disLoop_check t i a d f pos s op pos' hg _ _ _ hm
      (memoPhase_other op.info op.arg _ s.memo _ _ h1 h2) hr rfl
  · intro t i a d f pos s op pos' hg hr hp hs
    obtain ⟨hmem, _, _, _⟩ := genopStep_ok_info hg
    obtain ⟨h1, h2, _⟩ := table_memo_no_mark op.info hmem (Or.inl hp)
    have hm := markPhase_pass op.info s.stack s.markstack h1 (fun c => h2 c.1)
    rw [hs] at hm
    obtain ⟨mm', hk⟩ := memoPhase_put_empty op.info op.arg s.memo none none hp
    exact disLoop_check t i a d f pos s op pos' hg ⟨[], s.markstack, op.info.before.length, none, none⟩
      _ _ (by rw [hs]; exact hm) hk hr rfl
  · intro t i a d f pos s op pos' hg hr hp hs
    obtain ⟨hmem, _, _, _⟩ := genopStep_ok_info hg
    obtain ⟨h1, h2, _⟩ := table_memo_no_mark op.info hmem (Or.inl hp)
    have hm := markPhase_pass op.info s.stack s.markstack h1 (fun c => h2 c.1)
    cases hst : s.stack with
    | nil => rw [hst] at hs; cases hs
    | cons x rest =>
      rw [hst] at hs
      injection hs with hx
      subst hx
      rw [hst] at hm
      obtain ⟨mm', hk⟩ := memoPhase_put_mark op.info op.arg rest s.memo none none hp
      exact disLoop_check t i a d f pos s op pos' hg
        ⟨markObj :: rest, s.markstack, op.info.before.length, none, none⟩
        _ _ (by rw [hst]; exact hm) hk hr rfl
  · intro t i a d f pos s op pos' x r hg hgn hx hrx hl
    obtain ⟨hmem, _, _, _⟩ := genopStep_ok_info hg
    obtain ⟨h1, h2, h3⟩ := table_memo_no_mark op.info hmem (Or.inr hgn)
    have hp : putName op.info.name = false := by
      cases hpn : putName op.info.name
      · rfl
      · exact absurd ⟨hpn, hgn⟩ h3
    have hm := markPhase_pass op.info s.stack s.markstack h1 (fun c => h2 c.1)
    have hk := memoPhase_get_missing op.info op.arg x r s.stack s.memo none none hp hgn hx hrx hl
    have hr : ReprOk op.arg := by
      intro b hb; rw [hx] at hb; injection hb with hb; subst hb; exact ⟨r, hrx⟩
    exact disLoop_check t i a d f pos s op pos' hg _ _ _ hm hk hr rfl
  · intro t i a d f pos s op pos' hg hr hb hp hgn hlt
    obtain ⟨hmem, _, _, _⟩ := genopStep_ok_info hg
    have hpop : ¬(op.info.name = "POP" ∧ s.stack.head? = some markObj) := by
      intro ⟨hn, hh⟩
      have := table_pop op.info hmem hn
      rw [this] at hlt
      have : s.stack = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [this] at hh
      cases hh
    have hm := markPhase_pass op.info s.stack s.markstack hb hpop
    have hk := memoPhase_other op.info op.arg s.stack s.memo none none hp hgn
    obtain ⟨l, hl⟩ := argText_ok op.info op.arg none (disLine i s op) hr
    obtain ⟨out, ho⟩ := disStep_pop i a s op _ _ l hm hk hl rfl hlt
    rw [disLoop_step t i a d f pos s op pos' hg, ho]
  · intro t i a d f pos s op pos' x y r hg hc hs
    obtain ⟨hi, ha⟩ := stop_facts hg hc
    rw [disLoop_step t i a d f pos s op pos' hg, stop_step i a s op hi ha x (y :: r) hs]
    dsimp only
    rw [hc]
    simp only [beq_self_eq_true, if_true, disEnd]
    rfl
  · intro t i d f pos s op pos' x hg hc hs
    obtain ⟨hi, ha⟩ := stop_facts hg hc
    rw [disLoop_step t i 0 d f pos s op pos' hg, stop_step i 0 s op hi ha x [] hs]
    dsimp only
    rw [hc]
    simp only [beq_self_eq_true, if_true, disEnd, annotateLine, if_true]
    have hline : disLine i s op = ".    " ++ spaces (i * s.markstack.length) ++ "STOP" := by
      unfold disLine
      rw [hi]
      rfl
    rw [hline]
    simp only [List.isEmpty_nil, if_true, String.append_assoc]
    rfl

end PyLean.Pickle
