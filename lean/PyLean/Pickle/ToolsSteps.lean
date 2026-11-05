import PyLean.Pickle.ToolsExact

/-!
Every outcome of one round of `_genops` and of `dis`: the exhausted and
unknown-opcode errors, the opcode and positions returned (with and without
`tell`), and each sanity check of `dis` with its exact message.
-/

namespace PyLean.Pickle

open PyLean

/-! ## `_genops` -/

/-- `getpos()`: `data.tell()`, or `None` for a file without `tell` (`:2300-2303`). -/
def posOf (t : Bool) (p : Nat) : Option Nat := if t then some p else none

theorem getPos_eq (t : Bool) (p : Nat) (d : Bytes) : getPos t p d = .ok (posOf t p, p) := by
  cases t <;> rfl

theorem findOp_mem {c : UInt8} {info : OpInfo} (h : findOp c = some info) : info ∈ opTable :=
  List.mem_of_find?_eq_some h

theorem findOp_code {c : UInt8} {info : OpInfo} (h : findOp c = some info) : info.code = c := by
  have := List.find?_some h
  simpa using this

/-- One round of `_genops` at any position of any data, `:2305-2323`. -/
theorem genopStep_eq (t : Bool) (pos : Nat) (d : Bytes) :
    genopStep t pos d =
      match (d.drop pos).take 1 with
      | [] => .error (.valueError "pickle exhausted before seeing STOP")
      | c :: _ =>
        match findOp c with
        | none => .error (.valueError (unknownOpMsg (posOf t pos) c))
        | some info =>
          match readArg info (pos + 1) d with
          | .ok (a, s) => .ok (⟨info, a, posOf t pos, posOf t s⟩, s)
          | .error e => .error e := by
  unfold genopStep
  rw [tBind, getPos_eq]
  dsimp only
  rw [tBind]
  simp only [tRead]
  generalize hr : (d.drop pos).take 1 = r
  cases r with
  | nil => rfl
  | cons c t' =>
    have hl := congrArg List.length hr
    simp only [List.length_take, List.length_drop, List.length_cons] at hl
    have hone : t'.length = 0 := by omega
    have hpos : pos + (c :: t').length = pos + 1 := by simp [hone]
    dsimp only
    rw [hpos]
    cases findOp c with
    | none => rfl
    | some info =>
      dsimp only
      rw [tBind]
      cases readArg info (pos + 1) d with
      | error e => rfl
      | ok ra =>
        obtain ⟨a, s⟩ := ra
        dsimp only
        rw [tBind, getPos_eq]
        rfl

theorem take1_at (pre rest : Bytes) (c : UInt8) : ((pre ++ c :: rest).drop pre.length).take 1 = [c] := by
  rw [List.drop_left]; rfl

theorem readArg_noarg (info : OpInfo) (h : info.arg = "") (pos : Nat) (d : Bytes) :
    readArg info pos d = .ok (none, pos) := by
  unfold readArg
  rw [h]
  rfl

theorem genopStep_ok_info {t : Bool} {pos : Nat} {d : Bytes} {op : GenOp} {s : Nat}
    (h : genopStep t pos d = .ok (op, s)) :
    op.info ∈ opTable ∧ (op.info.arg = "" → op.arg = none) ∧ op.pos = posOf t pos ∧
      ∃ c, (d.drop pos).take 1 = [c] ∧ findOp c = some op.info := by
  rw [genopStep_eq] at h
  generalize hr : (d.drop pos).take 1 = r at h
  cases r with
  | nil => cases h
  | cons c t' =>
    have hl := congrArg List.length hr
    simp only [List.length_take, List.length_drop, List.length_cons] at hl
    have hone : t' = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hone
    dsimp only at h
    cases hf : findOp c with
    | none => rw [hf] at h; cases h
    | some info =>
      rw [hf] at h
      dsimp only at h
      cases ha : readArg info (pos + 1) d with
      | error e => rw [ha] at h; cases h
      | ok ra =>
        obtain ⟨a, s'⟩ := ra
        rw [ha] at h
        cases h
        refine ⟨findOp_mem hf, fun harg => ?_, rfl, c, rfl, hf⟩
        rw [readArg_noarg info harg] at ha
        injection ha with ha
        injection ha with ha
        exact ha.symm

/-- The opcodes `_genops` returns for argument-free opcodes from position `p` on. -/
def noArgOps (t : Bool) : Nat → List (UInt8 × OpInfo) → List GenOp
  | _, [] => []
  | p, (_, info) :: r => ⟨info, none, posOf t p, posOf t (p + 1)⟩ :: noArgOps t (p + 1) r

/-- `c` is an opcode without argument, other than `STOP`. -/
def NoArg (x : UInt8 × OpInfo) : Prop := findOp x.1 = some x.2 ∧ x.2.arg = "" ∧ x.1 ≠ oSTOP

theorem genopsLoop_noarg (t : Bool) (rest : Bytes) :
    ∀ (cs : List (UInt8 × OpInfo)) (pre : Bytes) (f : Nat), (∀ x ∈ cs, NoArg x) → cs.length < f →
      genopsLoop t f pre.length (pre ++ cs.map Prod.fst ++ rest) =
        match genopsLoop t (f - cs.length) (pre.length + cs.length) (pre ++ cs.map Prod.fst ++ rest) with
        | .ok (ops, s) => .ok (noArgOps t pre.length cs ++ ops, s)
        | .error e => .error e := by
  intro cs
  induction cs with
  | nil =>
    intro pre f _ _
    simp only [List.length_nil, Nat.sub_zero, Nat.add_zero]
    cases genopsLoop t f pre.length (pre ++ List.map Prod.fst [] ++ rest) with
    | ok r => obtain ⟨ops, s⟩ := r; rfl
    | error e => rfl
  | cons x cs ih =>
    intro pre f hall hf
    obtain ⟨c, info⟩ := x
    obtain ⟨h1, h2, h3⟩ := hall (c, info) List.mem_cons_self
    have hrest : ∀ y ∈ cs, NoArg y := fun y hy => hall y (List.mem_cons_of_mem _ hy)
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at hf; omega⟩
    have hd : pre ++ List.map Prod.fst ((c, info) :: cs) ++ rest =
        pre ++ c :: (cs.map Prod.fst ++ rest) := by simp
    have hd2 : pre ++ c :: (cs.map Prod.fst ++ rest) = (pre ++ [c]) ++ cs.map Prod.fst ++ rest := by simp
    have hstep : genopStep t pre.length (pre ++ c :: (cs.map Prod.fst ++ rest)) =
        .ok (⟨info, none, posOf t pre.length, posOf t (pre.length + 1)⟩, pre.length + 1) := by
      rw [genopStep_eq, take1_at]
      dsimp only
      rw [h1]
      dsimp only
      rw [readArg_noarg info h2]
    have hcode : (info.code == oSTOP) = false := by
      rw [findOp_code h1]; simpa using h3
    rw [hd, genopsLoop, tBind, hstep]
    dsimp only
    rw [hcode]
    simp only [Bool.false_eq_true, if_false]
    rw [tBind, hd2]
    have hl : (pre ++ [c]).length = pre.length + 1 := by simp
    have := ih (pre ++ [c]) g hrest (by simp at hf; omega)
    rw [hl] at this
    rw [this]
    have e1 : g - cs.length = g + 1 - ((c, info) :: cs).length := by simp
    have e2 : pre.length + 1 + cs.length = pre.length + ((c, info) :: cs).length := by simp; omega
    rw [e1, e2]
    cases genopsLoop t (g + 1 - ((c, info) :: cs).length) (pre.length + ((c, info) :: cs).length)
        (pre ++ [c] ++ List.map Prod.fst cs ++ rest) with
    | ok r => obtain ⟨ops, s⟩ := r; rfl
    | error e => rfl

theorem genops_noarg (t : Bool) (cs : List (UInt8 × OpInfo)) (rest : Bytes) (hall : ∀ x ∈ cs, NoArg x) :
    genops t (cs.map Prod.fst ++ rest) =
      match genopsLoop t ((cs.map Prod.fst ++ rest).length + 1 - cs.length) cs.length
          (cs.map Prod.fst ++ rest) with
      | .ok (ops, _) => .ok (noArgOps t 0 cs ++ ops)
      | .error e => .error e := by
  unfold genops
  have := genopsLoop_noarg t rest cs [] ((cs.map Prod.fst ++ rest).length + 1) hall (by simp; omega)
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at this
  rw [this]
  cases genopsLoop t ((cs.map Prod.fst ++ rest).length + 1 - cs.length) cs.length
      (cs.map Prod.fst ++ rest) with
  | ok r => obtain ⟨ops, s⟩ := r; rfl
  | error e => rfl

/-- `_genops` without `tell` returns the same opcodes and arguments with `pos`
(and the end position) `None`, and raises exactly when `_genops` with `tell`
raises. -/
def noPos (op : GenOp) : GenOp := { op with pos := none, endPos := none }

theorem genopStep_twin (pos : Nat) (d : Bytes) :
    (∀ op s, genopStep true pos d = .ok (op, s) → genopStep false pos d = .ok (noPos op, s)) ∧
    (∀ e, genopStep true pos d = .error e → ∃ e', genopStep false pos d = .error e') := by
  rw [genopStep_eq, genopStep_eq]
  generalize (d.drop pos).take 1 = r
  cases r with
  | nil => exact ⟨fun _ _ h => (by cases h), fun _ _ => ⟨_, rfl⟩⟩
  | cons c _ =>
    dsimp only
    cases findOp c with
    | none => exact ⟨fun _ _ h => (by cases h), fun _ _ => ⟨_, rfl⟩⟩
    | some info =>
      dsimp only
      cases readArg info (pos + 1) d with
      | error e => exact ⟨fun _ _ h => (by cases h), fun _ _ => ⟨_, rfl⟩⟩
      | ok ra =>
        obtain ⟨a, s'⟩ := ra
        exact ⟨fun op s h => (by cases h; rfl), fun _ h => (by cases h)⟩

theorem genopsLoop_twin (d : Bytes) :
    ∀ (f pos : Nat),
      (∀ ops s, genopsLoop true f pos d = .ok (ops, s) →
        genopsLoop false f pos d = .ok (ops.map noPos, s)) ∧
      (∀ e, genopsLoop true f pos d = .error e → ∃ e', genopsLoop false f pos d = .error e') := by
  intro f
  induction f with
  | zero =>
    intro pos
    refine ⟨fun ops s h => ?_, fun e _ => ⟨.modelFuel, rfl⟩⟩
    rw [genopsLoop] at h
    cases h
  | succ f ih =>
    intro pos
    obtain ⟨s1, s2⟩ := genopStep_twin pos d
    constructor
    · intro ops s h
      rw [genopsLoop, tBind] at h ⊢
      cases hs : genopStep true pos d with
      | error e => rw [hs] at h; cases h
      | ok r =>
        obtain ⟨op, p'⟩ := r
        rw [hs] at h
        rw [s1 op p' hs]
        dsimp only at h ⊢
        have hc : (noPos op).info.code = op.info.code := rfl
        rw [hc]
        by_cases hst : (op.info.code == oSTOP) = true
        · rw [if_pos hst] at h ⊢
          cases h
          rfl
        · rw [if_neg hst] at h ⊢
          rw [tBind] at h ⊢
          cases hl : genopsLoop true f p' d with
          | error e => rw [hl] at h; cases h
          | ok q =>
            obtain ⟨rest, e'⟩ := q
            rw [hl] at h
            rw [(ih p').1 rest e' hl]
            cases h
            rfl
    · intro e h
      rw [genopsLoop, tBind] at h ⊢
      cases hs : genopStep true pos d with
      | error x =>
        obtain ⟨e', he'⟩ := s2 x hs
        rw [he']
        exact ⟨e', rfl⟩
      | ok r =>
        obtain ⟨op, p'⟩ := r
        rw [hs] at h
        rw [s1 op p' hs]
        dsimp only at h ⊢
        have hc : (noPos op).info.code = op.info.code := rfl
        rw [hc]
        by_cases hst : (op.info.code == oSTOP) = true
        · rw [if_pos hst] at h; cases h
        · rw [if_neg hst] at h ⊢
          rw [tBind] at h ⊢
          cases hl : genopsLoop true f p' d with
          | ok q => rw [hl] at h; cases h
          | error x =>
            obtain ⟨e', he'⟩ := (ih p').2 x hl
            rw [he']
            exact ⟨e', rfl⟩

/-- `_genops` and `genops` (`Lib/pickletools.py:2296-2351`), every outcome:

* `step`: one round at any position of any stream: no byte left raises
  `"pickle exhausted before seeing STOP"`; an unknown byte raises
  `"at position %s, opcode %r unknown"` with `<unknown>` for a file without `tell`;
  a known opcode is returned with the argument its reader gave (or the reader's
  exception) and `tell()` before and after it, or `None` and `None` without `tell`;
* `run`: on argument-free opcodes followed by `STOP`, `genops` returns each of them
  at its position and stops after the `STOP`, ignoring what follows; without the
  `STOP` it raises the exhausted error, and on an unknown byte the unknown-opcode
  error at that byte's position;
* `notell`: the `pos is None` case (`:2345-2349`): a file without `tell` gets the same
  opcodes and arguments with no positions, and fails exactly when the bytes do.

A `genopStep` that always raises, or that skips the argument or misreports a
position, fails `step` and `run`. -/
def GenopsExact : Prop :=
  (∀ (t : Bool) (pre : Bytes),
    genopStep t pre.length pre = .error (.valueError "pickle exhausted before seeing STOP")) ∧
  (∀ (t : Bool) (pre rest : Bytes) (c : UInt8), findOp c = none →
    genopStep t pre.length (pre ++ c :: rest) =
      .error (.valueError (unknownOpMsg (posOf t pre.length) c))) ∧
  (∀ (t : Bool) (pre rest : Bytes) (c : UInt8) (info : OpInfo), findOp c = some info →
    genopStep t pre.length (pre ++ c :: rest) =
      match readArg info (pre.length + 1) (pre ++ c :: rest) with
      | .ok (a, s) => .ok (⟨info, a, posOf t pre.length, posOf t s⟩, s)
      | .error e => .error e) ∧
  (∀ (t : Bool) (cs : List (UInt8 × OpInfo)) (stop : OpInfo) (rest : Bytes),
    (∀ x ∈ cs, NoArg x) → findOp oSTOP = some stop →
    genops t (cs.map Prod.fst ++ oSTOP :: rest) =
      .ok (noArgOps t 0 cs ++ [⟨stop, none, posOf t cs.length, posOf t (cs.length + 1)⟩])) ∧
  (∀ (t : Bool) (cs : List (UInt8 × OpInfo)), (∀ x ∈ cs, NoArg x) →
    genops t (cs.map Prod.fst) = .error (.valueError "pickle exhausted before seeing STOP")) ∧
  (∀ (t : Bool) (cs : List (UInt8 × OpInfo)) (c : UInt8) (rest : Bytes), (∀ x ∈ cs, NoArg x) →
    findOp c = none →
    genops t (cs.map Prod.fst ++ c :: rest) =
      .error (.valueError (unknownOpMsg (posOf t cs.length) c))) ∧
  (∀ (d : Bytes) (ops : List GenOp), genops true d = .ok ops → genops false d = .ok (ops.map noPos)) ∧
  (∀ (d : Bytes) (e : PyExc), genops true d = .error e → ∃ e', genops false d = .error e')

theorem genopStep_exhausted (t : Bool) (pre : Bytes) :
    genopStep t pre.length pre = .error (.valueError "pickle exhausted before seeing STOP") := by
  rw [genopStep_eq, List.drop_length]
  rfl

theorem genopStep_unknown (t : Bool) (pre rest : Bytes) (c : UInt8) (h : findOp c = none) :
    genopStep t pre.length (pre ++ c :: rest) =
      .error (.valueError (unknownOpMsg (posOf t pre.length) c)) := by
  rw [genopStep_eq, take1_at]
  dsimp only
  rw [h]

theorem genopStep_known (t : Bool) (pre rest : Bytes) (c : UInt8) (info : OpInfo)
    (h : findOp c = some info) :
    genopStep t pre.length (pre ++ c :: rest) =
      match readArg info (pre.length + 1) (pre ++ c :: rest) with
      | .ok (a, s) => .ok (⟨info, a, posOf t pre.length, posOf t s⟩, s)
      | .error e => .error e := by
  rw [genopStep_eq, take1_at]
  dsimp only
  rw [h]

theorem genopsExact_proven : GenopsExact := by
  refine ⟨genopStep_exhausted, genopStep_unknown, genopStep_known, ?_, ?_, ?_, ?_, ?_⟩
  · intro t cs stop rest hall hs
    rw [genops_noarg t cs (oSTOP :: rest) hall]
    have hf : (cs.map Prod.fst ++ oSTOP :: rest).length + 1 - cs.length = rest.length + 2 := by
      simp; omega
    rw [hf, genopsLoop, tBind]
    have hstep := genopStep_known t (cs.map Prod.fst) rest oSTOP stop hs
    simp only [List.length_map] at hstep
    rw [hstep, readArg_noarg stop (by
      have := findOp_mem hs
      have hc := findOp_code hs
      revert this hc
      generalize stop = st
      intro hm hc
      have key : ∀ i ∈ opTable, i.code = oSTOP → i.arg = "" := by decide +kernel
      exact key st hm hc)]
    dsimp only
    rw [findOp_code hs]
    simp only [beq_self_eq_true, if_true]
    rfl
  · intro t cs hall
    have hg := genops_noarg t cs [] hall
    have hf : (cs.map Prod.fst ++ []).length + 1 - cs.length = 1 := by simp
    rw [hf, genopsLoop, tBind] at hg
    have := genopStep_exhausted t (cs.map Prod.fst)
    simp only [List.length_map] at this
    simp only [List.append_nil] at hg
    rw [hg, this]
  · intro t cs c rest hall hc
    rw [genops_noarg t cs (c :: rest) hall]
    have hf : (cs.map Prod.fst ++ c :: rest).length + 1 - cs.length = rest.length + 2 := by
      simp; omega
    rw [hf, genopsLoop, tBind]
    have := genopStep_unknown t (cs.map Prod.fst) rest c hc
    simp only [List.length_map] at this
    rw [this]
  · intro d ops h
    unfold genops at h ⊢
    cases hq : genopsLoop true (d.length + 1) 0 d with
    | error e => rw [hq] at h; cases h
    | ok r =>
      obtain ⟨o, x⟩ := r
      rw [hq] at h
      rw [(genopsLoop_twin d _ 0).1 o x hq]
      cases h
      rfl
  · intro d e h
    unfold genops at h ⊢
    cases hq : genopsLoop true (d.length + 1) 0 d with
    | ok r => rw [hq] at h; cases h
    | error x =>
      obtain ⟨e', he'⟩ := (genopsLoop_twin d _ 0).2 x hq
      rw [he']
      exact ⟨e', rfl⟩

end PyLean.Pickle
