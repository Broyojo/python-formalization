import PyLean.Pickle.ToolsProps
import PyLean.Pickle.DecProps

/-!
Properties of `_genops`, `genops` and `dis` over every byte string.
-/

namespace PyLean.Pickle

open PyLean

/-! ## Readers stay inside the data and move forward -/

/-- `m` moves the file position forward and stays inside the data. -/
def Mono {α : Type} (m : TM α) : Prop :=
  ∀ (pos : Nat) (d : Bytes) (a : α) (s : Nat), pos ≤ d.length → m pos d = .ok (a, s) →
    pos ≤ s ∧ s ≤ d.length

theorem mono_bind {α β : Type} {m : TM α} {f : α → TM β} (hm : Mono m) (hf : ∀ a, Mono (f a)) :
    Mono (m >>= f) := by
  intro pos d b s hp h
  rw [tBind] at h
  cases hq : m pos d with
  | error e => rw [hq] at h; cases h
  | ok r =>
    obtain ⟨a, s1⟩ := r
    rw [hq] at h
    obtain ⟨h1, h2⟩ := hm pos d a s1 hp hq
    obtain ⟨h3, h4⟩ := hf a s1 d b s h2 h
    exact ⟨Nat.le_trans h1 h3, h4⟩

theorem mono_pure {α : Type} (a : α) : Mono (pure a : TM α) := by
  intro pos d b s hp h
  cases h
  exact ⟨Nat.le_refl _, hp⟩

theorem mono_throw {α : Type} (e : PyExc) : Mono (tThrow e : TM α) := by
  intro pos d b s hp h
  cases h

theorem mono_lift {α : Type} (r : Py α) : Mono (tLift r) := by
  intro pos d b s hp h
  cases r with
  | ok a => cases h; exact ⟨Nat.le_refl _, hp⟩
  | error e => cases h

theorem mono_read (n : Nat) : Mono (tRead n) := by
  intro pos d b s hp h
  simp only [tRead] at h
  cases h
  simp only [List.length_take, List.length_drop]
  omega

theorem mono_readline : Mono tReadline := by
  intro pos d b s hp h
  simp only [tReadline] at h
  cases h
  split <;> simp only [List.length_take, List.length_drop] <;> omega

theorem mono_tell : Mono tTell := by
  intro pos d b s hp h
  cases h
  exact ⟨Nat.le_refl _, hp⟩

theorem mono_ite {α : Type} {c : Prop} [Decidable c] {a b : TM α} (ha : Mono a) (hb : Mono b) :
    Mono (if c then a else b) := by
  split <;> assumption

/-- Prove `Mono` of a reader body from those of its parts. -/
macro "mono_tac" extra:term : tactic =>
  `(tactic| repeat' first
    | exact mono_read _ | exact mono_readline | exact mono_tell | exact mono_lift _
    | exact mono_throw _ | exact mono_pure _ | exact $extra
    | refine mono_bind ?_ (fun _ => ?_)
    | refine mono_ite ?_ ?_
    | split)

theorem mono_readUintN (k : Nat) (name : String) : Mono (readUintN k name) := by
  unfold readUintN; mono_tac mono_tell

theorem mono_readInt4 : Mono readInt4 := by
  unfold readInt4; mono_tac mono_tell

theorem mono_readRawnl : Mono readRawnl := by
  unfold readRawnl; mono_tac mono_tell

theorem mono_needBytes (n : Nat) (name : String) (d : Bytes) : Mono (needBytes n name d) := by
  unfold needBytes; mono_tac mono_tell

theorem mono_readCounted (n : Nat) (name : String) : Mono (readCounted n name) := by
  unfold readCounted
  refine mono_ite (mono_throw _) ?_
  exact mono_bind (mono_read _) (fun _ => mono_needBytes _ _ _)

/-- `Mono` of a reader built from the ones above. -/
macro "mono2" : tactic =>
  `(tactic| repeat' first
    | exact mono_read _ | exact mono_readline | exact mono_tell | exact mono_lift _
    | exact mono_throw _ | exact mono_pure _ | exact mono_readUintN _ _ | exact mono_readInt4
    | exact mono_readRawnl | exact mono_needBytes _ _ _ | exact mono_readCounted _ _
    | refine mono_bind ?_ (fun _ => ?_)
    | refine mono_ite ?_ ?_
    | split)

theorem mono_readStringnlNoescape : Mono readStringnlNoescape := by
  unfold readStringnlNoescape; mono2

/-- `Mono` of every value `argReader` returns. -/
theorem argReader_mono (name : String) (r : TM TV) (h : argReader name = some r) : Mono r := by
  have nat (m : TM Nat) (hm : Mono m) : Mono (asNat m) :=
    mono_bind hm (fun _ => mono_pure _)
  have int (m : TM Int) (hm : Mono m) : Mono (asInt m) :=
    mono_bind hm (fun _ => mono_pure _)
  have str (m : TM (List Nat)) (hm : Mono m) : Mono (asStr m) :=
    mono_bind hm (fun _ => mono_pure _)
  have byt (m : TM Bytes) (hm : Mono m) : Mono (asBytes m) :=
    mono_bind hm (fun _ => mono_pure _)
  have n1 := mono_readStringnlNoescape
  unfold argReader at h
  split at h <;> first
    | (cases h; done)
    | (cases h
       first
         | exact nat _ (by first | unfold readUint1 | unfold readUint2 | unfold readUint4 | unfold readUint8
                           exact mono_readUintN _ _)
         | exact int _ mono_readInt4
         | exact str _ n1
         | exact str _ (by unfold readStringnl; mono2)
         | exact str _ (by unfold readStringnlNoescapePair; mono2; all_goals exact n1)
         | exact str _ (by unfold readString1 readUint1; mono2)
         | exact str _ (by unfold readString4; mono2)
         | exact str _ (by unfold readUnicodestringnl; mono2)
         | exact str _ (by unfold readUnicodestring1 readUint1; mono2)
         | exact str _ (by unfold readUnicodestring4 readUint4; mono2)
         | exact str _ (by unfold readUnicodestring8 readUint8; mono2)
         | exact byt _ (by unfold readBytes1 readUint1; mono2)
         | exact byt _ (by unfold readBytes4 readUint4; mono2)
         | exact byt _ (by unfold readBytes8 readUint8; mono2)
         | exact int _ (by unfold readDecimalnlLong; mono2)
         | exact int _ (by unfold readLong1 readUint1; mono2)
         | exact int _ (by unfold readLong4; mono2)
         | exact mono_bind (by unfold readBytearray8 readUint8; mono2) (fun _ => mono_pure _)
         | exact mono_bind (by unfold readFloat8; mono2) (fun _ => mono_pure _)
         | (unfold readDecimalnlShort; mono2)
         | (unfold readFloatnl; mono2))

theorem readArg_mono (info : OpInfo) : Mono (readArg info) := by
  unfold readArg
  split
  · next r h => exact mono_bind (argReader_mono _ _ h) (fun _ => mono_pure _)
  · exact mono_pure _

/-! ## `_genops` -/

/-- Each opcode moves forward, stays inside the data, and reports where it began
and ended. -/
theorem genopStep_spec (t : Bool) (pos : Nat) (d : Bytes) (op : GenOp) (s : Nat)
    (hp : pos ≤ d.length) (h : genopStep t pos d = .ok (op, s)) :
    pos < s ∧ s ≤ d.length ∧ (t = true → op.pos = some pos ∧ op.endPos = some s) := by
  have hg (p : Nat) : getPos t p d = .ok ((if t = true then some p else none), p) := by
    cases t <;> rfl
  unfold genopStep at h
  rw [tBind, hg] at h
  dsimp only at h
  rw [tBind] at h
  simp only [tRead] at h
  generalize hr : (d.drop pos).take 1 = r at h
  cases r with
  | nil => cases h
  | cons c t' =>
    have hl := congrArg List.length hr
    simp only [List.length_take, List.length_drop, List.length_cons] at hl
    have hone : t'.length = 0 := by omega
    have hpos : pos + (c :: t').length = pos + 1 := by simp [hone]
    dsimp only at h
    rw [hpos] at h
    cases hf : findOp c with
    | none => rw [hf] at h; cases h
    | some info =>
      rw [hf] at h
      dsimp only at h
      rw [tBind] at h
      cases ha : readArg info (pos + 1) d with
      | error e => rw [ha] at h; cases h
      | ok ra =>
        obtain ⟨arg, s1⟩ := ra
        rw [ha] at h
        dsimp only at h
        rw [tBind, hg] at h
        have hm := readArg_mono info (pos + 1) d arg s1 (by omega) ha
        cases h
        refine ⟨by omega, hm.2, fun ht => ?_⟩
        simp [ht]

/-- `_genops` terminates on every byte string: `len(data) + 1` rounds are enough,
and more rounds change nothing. Source: undisputed invariant (no hang). -/
def GenopsFuelEnough : Prop :=
  ∀ (t : Bool) (d : Bytes) (f : Nat), d.length + 1 ≤ f →
    genopsLoop t f 0 d = genopsLoop t (d.length + 1) 0 d

theorem genopsLoop_fuel (t : Bool) (d : Bytes) :
    ∀ (f f' pos : Nat), pos ≤ d.length → d.length + 1 ≤ f + pos → f ≤ f' →
      genopsLoop t f pos d = genopsLoop t f' pos d := by
  intro f
  induction f with
  | zero => intro f' pos h1 h2 _; omega
  | succ f ih =>
    intro f' pos hp h1 h2
    cases f' with
    | zero => omega
    | succ g =>
      rw [genopsLoop, genopsLoop, tBind, tBind]
      cases hs : genopStep t pos d with
      | error e => rfl
      | ok r =>
        obtain ⟨op, s⟩ := r
        dsimp only
        by_cases hc : (op.info.code == oSTOP) = true
        · rw [if_pos hc, if_pos hc]
        · rw [if_neg hc, if_neg hc]
          obtain ⟨h3, h4, _⟩ := genopStep_spec t pos d op s hp hs
          rw [tBind, tBind, ih g s h4 (by omega) (by omega)]

theorem genopsFuelEnough_proven : GenopsFuelEnough := by
  intro t d f h
  exact (genopsLoop_fuel t d (d.length + 1) f 0 (by omega) (by omega) h).symm

/-- The opcodes of a successful parse cover positions `p` to `e` without gaps,
each moves forward, and `STOP` comes last and nowhere else. -/
def OpsChain : Nat → List GenOp → Nat → Prop
  | _, [], _ => False
  | p, [op], e => op.pos = some p ∧ op.endPos = some e ∧ op.info.code = oSTOP ∧ p < e
  | p, op :: o :: r, e => ∃ m, op.pos = some p ∧ op.endPos = some m ∧ op.info.code ≠ oSTOP ∧
      p < m ∧ OpsChain m (o :: r) e

/-- On every byte string `genops` accepts, the opcodes start at 0, are contiguous,
stay inside the data and end at the first `STOP`. -/
def GenopsWellFormed : Prop :=
  ∀ (d : Bytes) (ops : List GenOp), genops true d = .ok ops →
    ∃ e, OpsChain 0 ops e ∧ e ≤ d.length

theorem genopsLoop_chain (d : Bytes) :
    ∀ (f pos : Nat) (ops : List GenOp) (e : Nat), pos ≤ d.length →
      genopsLoop true f pos d = .ok (ops, e) → OpsChain pos ops e ∧ e ≤ d.length := by
  intro f
  induction f with
  | zero => intro pos ops e _ h; cases h
  | succ f ih =>
    intro pos ops e hp h
    rw [genopsLoop, tBind] at h
    cases hs : genopStep true pos d with
    | error x => rw [hs] at h; cases h
    | ok r =>
      obtain ⟨op, s⟩ := r
      rw [hs] at h
      dsimp only at h
      obtain ⟨h1, h2, h3⟩ := genopStep_spec true pos d op s hp hs
      obtain ⟨h4, h5⟩ := h3 rfl
      by_cases hc : (op.info.code == oSTOP) = true
      · rw [if_pos hc] at h
        cases h
        exact ⟨⟨h4, h5, by simpa using hc, h1⟩, h2⟩
      · rw [if_neg hc, tBind] at h
        cases hr : genopsLoop true f s d with
        | error x => rw [hr] at h; cases h
        | ok q =>
          obtain ⟨rest, e'⟩ := q
          rw [hr] at h
          cases h
          obtain ⟨h6, h7⟩ := ih s rest _ h2 hr
          cases rest with
          | nil => exact h6.elim
          | cons o r' =>
            exact ⟨⟨s, h4, h5, fun ec => hc (by simp [ec]), h1, h6⟩, h7⟩

theorem genopsWellFormed_proven : GenopsWellFormed := by
  intro d ops h
  unfold genops at h
  split at h
  · next r x hq =>
    cases h
    exact ⟨_, genopsLoop_chain d _ 0 _ _ (Nat.zero_le _) hq⟩
  · cases h

/-! ## `dis` -/

/-- `dis` reports bad streams with `ValueError` (its docstring lists the sanity
checks, and every check it makes raises that). -/
def DisNoIndexError : Prop :=
  ∀ (t : Bool) (d : Bytes) (memo : List (Int × String)) (i a : Nat),
    (dis t d memo i a).2 ≠ some (.indexError "list index out of range")

theorem disNoIndexError_refuted : ¬DisNoIndexError := by
  intro h
  exact h true [0x28, 0x85, 0x74, 0x2e] [] 4 0 (by decide +kernel)

theorem disStep_maxproto (i a : Nat) (s : DisSt) (op : GenOp) (s' : DisSt)
    (h : disStep i a s op = .ok s') : s'.maxproto = max s.maxproto op.info.proto := by
  unfold disStep at h
  simp only [Bind.bind, Except.bind] at h
  repeat' (split at h)
  all_goals first | (cases h; rfl) | cases h

/-- The value of `maxproto` after `ops`. -/
def maxProto (ops : List GenOp) : Int := ops.foldl (fun m o => max m (o.info.proto : Int)) (-1)

/-- When `dis` raises nothing, `genops` accepts the stream and the last line
printed is the maximum protocol over its opcodes. -/
def DisFollowsGenops : Prop :=
  ∀ (t : Bool) (d : Bytes) (memo : List (Int × String)) (i a : Nat) (out : String),
    dis t d memo i a = (out, none) →
    ∃ ops, genops t d = .ok ops ∧
      ∃ txt, out = txt ++ s!"highest protocol among opcodes = {maxProto ops}\n"

theorem disLoop_genops (t : Bool) (i a : Nat) (d : Bytes) :
    ∀ (f pos : Nat) (s : DisSt) (out : String), disLoop t i a d f pos s = (out, none) →
      ∃ ops e, genopsLoop t f pos d = .ok (ops, e) ∧
        ∃ txt, out = txt ++ s!"highest protocol among opcodes = {
          ops.foldl (fun m o => max m (o.info.proto : Int)) s.maxproto}\n" := by
  intro f
  induction f with
  | zero => intro pos s out h; simp [disLoop] at h
  | succ f ih =>
    intro pos s out h
    rw [disLoop] at h
    cases hs : genopStep t pos d with
    | error e => rw [hs] at h; simp at h
    | ok r =>
      obtain ⟨op, p'⟩ := r
      rw [hs] at h
      dsimp only at h
      cases hd : disStep i a s op with
      | error x => rw [hd] at h; simp at h
      | ok s' =>
        rw [hd] at h
        dsimp only at h
        have hm := disStep_maxproto i a s op s' hd
        by_cases hc : (op.info.code == oSTOP) = true
        · rw [if_pos hc] at h
          unfold disEnd at h
          dsimp only at h
          split at h
          · injection h with h1 _
            refine ⟨[op], p', ?_, s'.out, ?_⟩
            · rw [genopsLoop, tBind, hs]
              dsimp only
              rw [if_pos hc]
              rfl
            · rw [← h1]
              simp only [List.foldl_cons, List.foldl_nil]
              rw [hm]
          · simp at h
        · rw [if_neg hc] at h
          obtain ⟨ops, e, h1, txt, h2⟩ := ih p' s' out h
          refine ⟨op :: ops, e, ?_, txt, ?_⟩
          · rw [genopsLoop, tBind, hs]
            dsimp only
            rw [if_neg hc, tBind, h1]
            rfl
          · rw [h2]
            simp only [List.foldl_cons]
            rw [hm]

theorem disFollowsGenops_proven : DisFollowsGenops := by
  intro t d memo i a out h
  obtain ⟨ops, e, h1, txt, h2⟩ := disLoop_genops t i a d _ 0 _ out h
  refine ⟨ops, ?_, txt, h2⟩
  unfold genops
  rw [h1]

/-! ## `read_unicodestringnl` -/

/-- `read_unicodestringnl` is `raw-unicode-escape` on the line, as in `load_unicode`,
and raises when the newline is missing. -/
def ReadUnicodeNl : Prop :=
  (∀ pre line rest : Bytes, nl ∉ line →
    valOf (readUnicodestringnl pre.length (pre ++ line ++ nl :: rest)) = decodeRUE line) ∧
  (∀ pre short : Bytes, nl ∉ short →
    readUnicodestringnl pre.length (pre ++ short) =
      .error (.valueError "no newline found when trying to read unicodestringnl"))

theorem findIdx_none (l : Bytes) (h : nl ∉ l) : l.findIdx? (· == nl) = none := by
  induction l with
  | nil => rfl
  | cons a r ih =>
    have ha : a ≠ nl := fun e => h (e ▸ List.mem_cons_self)
    have hr : nl ∉ r := fun m => h (List.mem_cons_of_mem _ m)
    simp [List.findIdx?_cons, ha, ih hr]

theorem readUnicodeNl_proven : ReadUnicodeNl := by
  constructor
  · intro pre line rest h
    have h1 : (line ++ [nl]).getLast? = some nl := by simp
    have h2 : (line ++ [nl]).dropLast = line := by simp
    unfold readUnicodestringnl
    rw [tBind, tReadline_at pre line rest h]
    dsimp only
    rw [if_pos (by rw [h1]; rfl), h2]
    simp only [tLift, valOf]
    cases decodeRUE line <;> rfl
  · intro pre short h
    have hd : (pre ++ short).drop pre.length = short := List.drop_left
    have hl : (short.getLast? == some nl) ≠ true := by
      intro hb
      exact h (List.mem_of_getLast? (beq_iff_eq.mp hb))
    unfold readUnicodestringnl
    rw [tBind]
    simp only [tReadline, hd, findIdx_none short h]
    rw [if_neg hl]
    rfl

/-! ## `optimize` -/

/-- `p[a:b]`. -/
def slice (p : Bytes) (a b : Nat) : Bytes := (p.drop a).take (b - a)

theorem take_slice (p : Bytes) (a b : Nat) (h : a ≤ b) : p.take a ++ slice p a b = p.take b := by
  have e : b = a + (b - a) := by omega
  unfold slice
  conv => rhs; rw [e, List.take_add]

/-- The bytes the second loop of `optimize` copies. -/
def rawBytes (p : Bytes) : List OptOp → Bytes
  | [] => []
  | .raw a b :: r => slice p a b ++ rawBytes p r
  | _ :: r => rawBytes p r

theorem rawBytes_append (p : Bytes) (l r : List OptOp) :
    rawBytes p (l ++ r) = rawBytes p l ++ rawBytes p r := by
  induction l with
  | nil => rfl
  | cons o l ih => cases o <;> simp [rawBytes, ih, List.append_assoc]

def AllRaw (l : List OptOp) : Prop := ∀ o ∈ l, ∃ a b, o = OptOp.raw a b

/-- An opcode `optimize` only copies: no memo or frame opcode, and a protocol
below the framing protocols. -/
def RawOp (op : GenOp) : Prop :=
  hasSub op.info.name "PUT" = false ∧ op.info.name ≠ "MEMOIZE" ∧
  hasSub op.info.name "FRAME" = false ∧ hasSub op.info.name "GET" = false ∧
  (op.info.name = "PROTO" → memoKey op.arg < 4)

/-- `optimize` returns a stream without memo or frame opcodes, of protocol below
4, unchanged up to its `STOP`. The hypothesis selects the opcodes `optimize`
copies: what it does with memo opcodes is the open `pickle-optimize-sound`. -/
def OptimizeRawCopy : Prop :=
  ∀ (p : Bytes) (ops : List GenOp), genops true p = .ok ops → (∀ op ∈ ops, RawOp op) →
    ∃ e, optimize p = .ok (p.take e) ∧ OpsChain 0 ops e

/-- What the first loop of `optimize` keeps on these opcodes. -/
structure OptInv (p : Bytes) (s : OptSt) (pos : Nat) : Prop where
  bytes : s.header ++ rawBytes p s.ops.reverse = p.take pos
  raw : AllRaw s.ops
  lo : 0 ≤ s.proto
  hi : s.proto < 4

theorem optStep_raw (p : Bytes) (s : OptSt) (op : GenOp) (pos m : Nat) (hr : RawOp op)
    (h1 : op.pos = some pos) (h2 : op.endPos = some m) (hlt : pos < m) (hi : OptInv p s pos) :
    OptInv p (optStep p s op) m := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := hr
  have hraw : OptInv p { s with ops := OptOp.raw pos m :: s.ops } m := by
    refine ⟨?_, ?_, hi.lo, hi.hi⟩
    · simp only [List.reverse_cons]
      rw [rawBytes_append, ← List.append_assoc, hi.bytes]
      simp only [rawBytes, List.append_nil]
      exact take_slice p pos m (by omega)
    · intro o ho
      rcases List.mem_cons.mp ho with e | e
      · exact ⟨_, _, e⟩
      · exact hi.raw o e
  unfold optStep
  simp only [a1, a2, a3, a4, h1, h2, Option.getD_some, Bool.false_eq_true, if_false]
  by_cases hP : op.info.name = "PROTO"
  · have hk := a5 hP
    rw [if_pos hP]
    by_cases hz : pos = 0
    · subst hz
      rw [if_pos rfl]
      refine ⟨?_, hi.raw, ?_, ?_⟩
      · have hb := hi.bytes
        have hn : rawBytes p s.ops.reverse = [] := by
          have : s.header ++ rawBytes p s.ops.reverse = [] := by rw [hb]; simp
          exact (List.append_eq_nil_iff.mp this).2
        rw [hn]
        simp
      · have := hi.lo
        simp only
        omega
      · have := hi.hi
        simp only
        omega
    · rw [if_neg hz]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.reverse_cons]
        rw [rawBytes_append, ← List.append_assoc, hi.bytes]
        simp only [rawBytes, List.append_nil]
        exact take_slice p pos m (by omega)
      · intro o ho
        rcases List.mem_cons.mp ho with e | e
        · exact ⟨_, _, e⟩
        · exact hi.raw o e
      · have := hi.lo
        simp only
        omega
      · have := hi.hi
        simp only
        omega
  · rw [if_neg hP]
    exact hraw

theorem optFold (p : Bytes) :
    ∀ (ops : List GenOp) (pos e : Nat) (s : OptSt), OpsChain pos ops e →
      (∀ op ∈ ops, RawOp op) → OptInv p s pos → OptInv p (ops.foldl (optStep p) s) e := by
  intro ops
  induction ops with
  | nil => intro pos e s h; exact h.elim
  | cons op r ih =>
    intro pos e s hc hall hi
    cases r with
    | nil =>
      obtain ⟨h1, h2, _, h3⟩ := hc
      exact optStep_raw p s op pos e (hall op List.mem_cons_self) h1 h2 h3 hi
    | cons o r' =>
      obtain ⟨m, h1, h2, _, h3, h4⟩ := hc
      exact ih m e _ h4 (fun x hx => hall x (List.mem_cons_of_mem _ hx))
        (optStep_raw p s op pos m (hall op List.mem_cons_self) h1 h2 h3 hi)

/-- The framer state after the calls of `s`. -/
def framed (s : OptOut) : PyFramer := s.ev.reverse.foldl PyFramer.step {}

theorem step_write (st : PyFramer) (hc : st.cur = none) (d : Bytes) :
    (st.step .boundary).step (.w d) = { st with out := st.out ++ d } := by
  obtain ⟨o, c⟩ := st
  simp only at hc
  subst hc
  rfl

theorem step_large (st : PyFramer) (hc : st.cur = none) (d : Bytes) :
    st.step (.large [] d) = { st with out := st.out ++ ([] ++ d) } := by
  obtain ⟨o, c⟩ := st
  simp only at hc
  subst hc
  rfl

theorem framed_write (s : OptOut) (d : Bytes) :
    framed (optWrite s d) = ((framed s).step .boundary).step (.w d) := by
  simp only [framed, optWrite, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem framed_large (s : OptOut) (d : Bytes) :
    framed { s with ev := .large [] d :: s.ev } = (framed s).step (.large [] d) := by
  simp only [framed, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem emitRaw (proto : Nat) (p : Bytes) :
    ∀ (l : List OptOp) (s : OptOut), AllRaw l → (framed s).cur = none →
      ∃ out, l.foldlM (optEmit proto p) s = .ok out ∧ (framed out).cur = none ∧
        (framed out).out = (framed s).out ++ rawBytes p l := by
  intro l
  induction l with
  | nil => intro s _ hc; exact ⟨s, rfl, hc, by simp [rawBytes]⟩
  | cons o r ih =>
    intro s hall hc
    obtain ⟨a, b, rfl⟩ := hall o List.mem_cons_self
    have hr : AllRaw r := fun x hx => hall x (List.mem_cons_of_mem _ hx)
    let data := (p.drop a).take (b - a)
    have hstep : ∃ s1, optEmit proto p s (.raw a b) = .ok s1 ∧ (framed s1).cur = none ∧
        (framed s1).out = (framed s).out ++ data := by
      by_cases hl : data.length > frameSizeTarget
      · refine ⟨{ s with ev := .large [] data :: s.ev }, ?_, ?_, ?_⟩
        · simp only [optEmit, data]
          rw [if_pos hl]
        · rw [framed_large, step_large _ hc]
          exact hc
        · rw [framed_large, step_large _ hc]
          simp
      · refine ⟨optWrite s data, ?_, ?_, ?_⟩
        · simp only [optEmit, data]
          rw [if_neg hl]
        · rw [framed_write, step_write _ hc]
          exact hc
        · rw [framed_write, step_write _ hc]
    obtain ⟨s1, h1, h2, h3⟩ := hstep
    obtain ⟨out, h4, h5, h6⟩ := ih s1 hr h2
    refine ⟨out, ?_, h5, ?_⟩
    · rw [List.foldlM_cons, h1]
      exact h4
    · rw [h6, h3]
      simp [rawBytes, slice, data, List.append_assoc]

theorem optimizeRawCopy_proven : OptimizeRawCopy := by
  intro p ops h hraw
  obtain ⟨e, hc, _⟩ := genopsWellFormed_proven p ops h
  refine ⟨e, ?_, hc⟩
  have hinit : OptInv p {} 0 :=
    ⟨by simp [rawBytes], (fun o ho => (List.not_mem_nil ho).elim), by decide, by decide⟩
  have inv := optFold p ops 0 e {} hc hraw hinit
  generalize hs : ops.foldl (optStep p) {} = s at inv
  have hp : pyProtocol s.proto = .ok s.proto.toNat := by
    unfold pyProtocol
    rw [if_neg (by have := inv.lo; omega), if_pos (by have := inv.hi; omega)]
  have hlt : ¬ s.proto.toNat ≥ 4 := by have := inv.hi; omega
  have hrev : AllRaw s.ops.reverse := fun o ho => inv.raw o (List.mem_reverse.mp ho)
  obtain ⟨out, h1, h2, h3⟩ := emitRaw s.proto.toNat p s.ops.reverse { newids := s.newids } hrev rfl
  have hf : pyFrame (([] : List Event) ++ out.ev.reverse ++ [Event.finish]) = (framed out).out := by
    unfold pyFrame
    simp only [List.nil_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have e2 : out.ev.reverse.foldl PyFramer.step {} = framed out := rfl
    rw [e2]
    simp [PyFramer.step, h2]
  unfold optimize
  simp only [Bind.bind, Except.bind, h, hs, hp, h1, Pure.pure, Except.pure]
  rw [if_neg hlt, hf, h3]
  have hb := inv.bytes
  simp only [framed, List.foldl_nil, List.reverse_nil]
  simp only [List.nil_append]
  rw [← hb]

/-- `optimize` keeps what a stream loads to: on a stream an unpickler accepts,
that same unpickler returns an equal object from the optimized stream. Each
unpickler is compared with itself, because `optimize` drops frames and a stream
the twins disagree on can stop being one. -/
def OptimizeSound : Prop :=
  ∀ p q : Bytes, optimize p = .ok q →
    (isErr (pyLoads p) = false → resolved (pyLoads q) = resolved (pyLoads p)) ∧
    (isErr (cLoads p) = false → resolved (cLoads q) = resolved (cLoads p))

/-- `stack not empty after STOP: %r` names what is left, bottom first: the
list repr with `StackObject.__repr__`. -/
def DisStackRepr : Prop :=
  ∀ s : DisSt, s.stack ≠ [] →
    (disEnd s).2 = some (.valueError
      s!"stack not empty after STOP: [{", ".intercalate s.stack.reverse}]")

theorem disStackRepr_proven : DisStackRepr := by
  intro s h
  unfold disEnd
  cases hs : s.stack with
  | nil => exact absurd hs h
  | cons x r => rfl

end PyLean.Pickle
