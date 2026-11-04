import PyLean.Bytecode.SpecCompareFloat
import PyLean.Bytecode.SpecForIter

/-!
The fast paths of the `COMPARE_OP` and `FOR_ITER` specializations, as in `SpecFast.lean`: the
exact operands on which each macro answers by itself, what it answers, and that it exits on every
other stack.
-/

namespace PyLean.Bytecode

open Uop

/-- The mirror's answer of `_COMPARE_OP_INT` on two ints. -/
def cmpIntBit (n : Nat) : Val → Val → Val
  | .int a, .int b => .bool (comparisonBit (decide (a ≥ b)) (decide (a ≤ b)) &&& n != 0)
  | _, _ => .null

/-- The mirror's answer of `_COMPARE_OP_FLOAT` on two floats. -/
def cmpFloatBit (n : Nat) : Val → Val → Val
  | .float a, .float b =>
    .bool (comparisonBit (Binary64.F64.ge (toF a) (toF b)) (Binary64.F64.le (toF a) (toF b)) &&& n != 0)
  | _, _ => .null

/-- The mirror's answer of `_COMPARE_OP_STR` on two strs. -/
def cmpStrBit (n : Nat) : Val → Val → Val
  | .str a, .str b => .bool ((7 + (if a == b then 1 else 0)) &&& n != 0)
  | _, _ => .null

theorem cmpInt_arith (e : Env) : KindArith (COMPARE_OP_INT e) CompactInt (cmpIntBit e.oparg) := by
  refine kindArith_of intKind CompactInt notCompactInt_iff (_COMPARE_OP_INT e) _ ?_
  rintro regs rest _ _ ⟨a, rfl, ha⟩ ⟨b, rfl, hb⟩
  have ha' := (isCompact_iff a).2 ha
  have hb' := (isCompact_iff b).2 hb
  bc_simp [_COMPARE_OP_INT, ha', hb', cmpIntBit]

theorem cmpFloat_arith (e : Env) : KindArith (COMPARE_OP_FLOAT e) IsFloat (cmpFloatBit e.oparg) := by
  refine kindArith_of floatKind IsFloat notFloat_iff (_COMPARE_OP_FLOAT e) _ ?_
  rintro regs rest _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
  bc_simp [_COMPARE_OP_FLOAT, cmpFloatBit]

theorem cmpStr_arith (e : Env) : KindArith (COMPARE_OP_STR e) IsStr (cmpStrBit e.oparg) := by
  refine kindArith_of strKind IsStr notStr_iff (_COMPARE_OP_STR e) _ ?_
  rintro regs rest _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
  bc_simp [_COMPARE_OP_STR, cmpStrBit]

/-- `COMPARE_OP_INT` (`Python/bytecodes.c:3256`, `:3280-3300`), `COMPARE_OP_FLOAT` (`:3253`,
`:3262-3278`) and `COMPARE_OP_STR` (`:3259`, `:3302-3318`): on two compact ints, two floats, or
two strs they answer the comparison `oparg >> 5` of `left` (the second value) with `right`, as a
bool: the order of `int`, the IEEE-754 relations of `float` (every comparison with a NaN false,
except `!=`), and equality of `str` for `==` and `!=`, the only two the specializer picks; on
any other operands each exits with the stack unchanged. The oparg is the one the compiler emits
(`CmpArg`, `Python/flowgraph.c`), whose low four bits these forms read. -/
def CompareFast : Prop := ∀ (e : Env) (regs : Regs) (rest : List Val) (l r : Val),
  (CmpArg e.oparg → ∀ a b, l = .int a → r = .int b → Compact a → Compact b →
    COMPARE_OP_INT e ⟨regs, r :: l :: rest⟩ = .ok () ⟨regs, .bool (cmpInt (e.oparg >>> 5) a b) :: rest⟩) ∧
  (¬ (CompactInt l ∧ CompactInt r) →
    COMPARE_OP_INT e ⟨regs, r :: l :: rest⟩ = .error .deopt ⟨regs, r :: l :: rest⟩) ∧
  (CmpArg e.oparg → ∀ a b, l = .float a → r = .float b →
    COMPARE_OP_FLOAT e ⟨regs, r :: l :: rest⟩ =
      .ok () ⟨regs, .bool (floatTable (e.oparg >>> 5) (toF a) (toF b)) :: rest⟩) ∧
  (¬ (IsFloat l ∧ IsFloat r) →
    COMPARE_OP_FLOAT e ⟨regs, r :: l :: rest⟩ = .error .deopt ⟨regs, r :: l :: rest⟩) ∧
  (e.oparg >>> 5 = 2 → e.oparg &&& 15 = 8 → ∀ a b, l = .str a → r = .str b →
    COMPARE_OP_STR e ⟨regs, r :: l :: rest⟩ = .ok () ⟨regs, .bool (a == b) :: rest⟩) ∧
  (e.oparg >>> 5 = 3 → e.oparg &&& 15 = 7 → ∀ a b, l = .str a → r = .str b →
    COMPARE_OP_STR e ⟨regs, r :: l :: rest⟩ = .ok () ⟨regs, .bool (a != b) :: rest⟩) ∧
  (¬ (IsStr l ∧ IsStr r) →
    COMPARE_OP_STR e ⟨regs, r :: l :: rest⟩ = .error .deopt ⟨regs, r :: l :: rest⟩)

theorem compareFast_proven : CompareFast := by
  intro e regs rest l r
  refine ⟨fun harg a b hl hr ha hb => ?_, (cmpInt_arith e regs rest l r).2,
    fun harg a b hl hr => ?_, (cmpFloat_arith e regs rest l r).2, fun hop hm a b hl hr => ?_,
    fun hop hm a b hl hr => ?_, (cmpStr_arith e regs rest l r).2⟩
  · subst hl hr
    rw [(cmpInt_arith e regs rest _ _).1 ⟨a, rfl, ha⟩ ⟨b, rfl, hb⟩, cmpIntBit, cmpBit_int a b e.oparg harg]
  · subst hl hr
    rw [(cmpFloat_arith e regs rest _ _).1 ⟨a, rfl⟩ ⟨b, rfl⟩, cmpFloatBit,
      cmpBit_float (toF a) (toF b) e.oparg harg]
  · subst hl hr
    rw [(cmpStr_arith e regs rest _ _).1 ⟨a, rfl⟩ ⟨b, rfl⟩, cmpStrBit]
    by_cases hab : a = b
    · simp [hab, and_low 8 e.oparg (by decide), hm]
    · simp [hab, and_low 7 e.oparg (by decide), hm]
  · subst hl hr
    rw [(cmpStr_arith e regs rest _ _).1 ⟨a, rfl⟩ ⟨b, rfl⟩, cmpStrBit]
    by_cases hab : a = b
    · simp [hab, and_low 8 e.oparg (by decide), hm]
    · simp [hab, and_low 7 e.oparg (by decide), hm]

/-! ## `FOR_ITER` over a list, a tuple, a range -/

/-- After `JUMPBY(oparg + 1)`. -/
abbrev jumpedOver (regs : Regs) (oparg : Nat) : Regs := { regs with next := regs.next + oparg + 1 }

theorem jumpBy_succ (regs : Regs) (n : Nat) :
    jumpBy ((n : Int) + 1) regs = .ok () (jumpedOver regs n) := by
  simp only [jumpBy, jumpedOver]
  congr 2 <;> omega

/-- A list or tuple form of `FOR_ITER`, given the guard and the sequence it accepts. -/
def SeqIterFast (m : M Unit) (P : Rt → Val → Prop) (ctor : Array Val → Obj) (oparg : Nat) : Prop :=
  ∀ (regs : Regs) (rest : List Val) (it idx : Val), Live regs.rt it →
    (∀ a items i, it = .ref a → regs.rt.heap[a]? = some (ctor items) → idx = .tagged i →
      (∀ v, items[i]? = some v →
        m ⟨regs, idx :: it :: rest⟩ = .ok () ⟨regs, v :: .tagged (i + 1) :: it :: rest⟩) ∧
      (items.size ≤ i →
        m ⟨regs, idx :: it :: rest⟩ = .error .dispatch ⟨jumpedOver regs oparg, idx :: it :: rest⟩)) ∧
    (¬ P regs.rt it → m ⟨regs, idx :: it :: rest⟩ = .error .deopt ⟨regs, idx :: it :: rest⟩)

theorem seq_jump_next (e : Env) (regs : Regs) (rest : List Val) (a : Addr) (o : Obj)
    (items : Array Val) (i : Nat) (h : regs.rt.heap[a]? = some o) (ho : o = .list items ∨ o = .tuple items) :
    (∀ v, items[i]? = some v → (do iterJumpSeq e; iterNextSeq) ⟨regs, .tagged i :: .ref a :: rest⟩ =
        .ok () ⟨regs, v :: .tagged (i + 1) :: .ref a :: rest⟩) ∧
    (items.size ≤ i → (do iterJumpSeq e; iterNextSeq) ⟨regs, .tagged i :: .ref a :: rest⟩ =
        .error .dispatch ⟨jumpedOver regs e.oparg, .tagged i :: .ref a :: rest⟩) := by
  have hsi := seqItems_ok (regs := regs) h ho
  constructor
  · intro v hv
    have hlt : i < items.size := (Array.getElem?_eq_some_iff.1 hv).1
    have hend : ¬ items.size ≤ i := by omega
    have hgd : items.getD i .null = v := by simp [Array.getD_eq_getD_getElem?, hv]
    bc_simp [iterJumpSeq, iterNextSeq, hsi, taggedIndex, hend, hgd]
  · intro hend
    have hj := jumpBy_succ regs e.oparg
    bc_simp [iterJumpSeq, hsi, taggedIndex, hend, hj]

theorem seqIterFast_of (e : Env) (m : M Unit) (g : M Unit) (P : Rt → Val → Prop) (ctor : Array Val → Obj)
    (hm : m = (do g; iterJumpSeq e; iterNextSeq))
    (hg : GuardNos g P) (hP : ∀ rt a items, rt.heap[a]? = some (ctor items) → P rt (.ref a))
    (hc : ∀ items, ctor items = .list items ∨ ctor items = .tuple items) :
    SeqIterFast m P ctor e.oparg := by
  intro regs rest it idx hl
  subst hm
  constructor
  · rintro a items i rfl ho rfl
    have g1 := (hg regs rest (.ref a) (.tagged i) hl).1 (hP _ a items ho)
    obtain ⟨h1, h2⟩ := seq_jump_next e regs rest a _ items i ho (hc items)
    refine ⟨fun v hv => ?_, fun hend => ?_⟩
    · have := h1 v hv
      simp only [bind, EStateM.bind, g1] at this ⊢
      exact this
    · have := h2 hend
      simp only [bind, EStateM.bind, g1] at this ⊢
      exact this
  · intro hn
    simp only [bind, EStateM.bind, (hg regs rest it idx hl).2 hn]

/-- `FOR_ITER_RANGE`'s fast path. -/
def RangeIterFast (e : Env) : Prop :=
  ∀ (regs : Regs) (rest : List Val) (it idx : Val), Live regs.rt it →
    (∀ a start step len, it = .ref a → regs.rt.heap[a]? = some (.rangeIter start step len) →
      (0 < len → FOR_ITER_RANGE e ⟨regs, idx :: it :: rest⟩ = .ok ()
        ⟨{ regs with rt := { regs.rt with heap := (regs.rt.heap.setIfInBounds a
            (.rangeIter (start + step) step (len - 1))) } }, .int start :: idx :: it :: rest⟩) ∧
      (len ≤ 0 → FOR_ITER_RANGE e ⟨regs, idx :: it :: rest⟩ =
        .error .dispatch ⟨jumpedOver regs e.oparg, idx :: it :: rest⟩)) ∧
    (¬ (∃ a start step len, it = .ref a ∧ regs.rt.heap[a]? = some (.rangeIter start step len)) →
      FOR_ITER_RANGE e ⟨regs, idx :: it :: rest⟩ = .error .deopt ⟨regs, idx :: it :: rest⟩)

/-- `FOR_ITER_LIST` (`Python/bytecodes.c:4006-4010`: `_ITER_CHECK_LIST` `:3927-3933`,
`_ITER_JUMP_LIST` `:3936-3952`, `_ITER_NEXT_LIST` `:3964-3985`) and `FOR_ITER_TUPLE` (`:4047-4051`,
`:4012-4045`): on an exact list or tuple with the tagged index `GET_ITER` left above it, they
push item `i` and bump the tag when `i` is in range, and otherwise jump over `END_FOR` with both
slots left for `POP_ITER`; on anything else the type guard exits. `FOR_ITER_RANGE` (`:4097-4101`,
`:4053-4095`) on a range iterator with `len > 0` pushes `start` and advances the iterator by one
`step`, with `len ≤ 0` jumps over `END_FOR`, and exits on anything else. -/
def ForIterFast : Prop := ∀ (e : Env),
  SeqIterFast (FOR_ITER_LIST e) IsList .list e.oparg ∧
  SeqIterFast (FOR_ITER_TUPLE e) IsTuple .tuple e.oparg ∧
  RangeIterFast e

theorem forIterFast_proven : ForIterFast := by
  intro e
  refine ⟨?_, ?_, ?_⟩
  · exact seqIterFast_of e _ _ITER_CHECK_LIST IsList .list rfl
      (guardNos_of _ _ fun regs x _ hx => notList_spec regs x hx)
      (fun rt a items h => ⟨a, items, rfl, h⟩) (fun items => Or.inl rfl)
  · exact seqIterFast_of e _ _ITER_CHECK_TUPLE IsTuple .tuple rfl
      (guardNos_of _ _ fun regs x _ hx => notTuple_spec regs x hx)
      (fun rt a items h => ⟨a, items, rfl, h⟩) (fun items => Or.inr rfl)
  · intro regs rest it idx hl
    constructor
    · rintro a start step len rfl ho
      have g1 : _ITER_CHECK_RANGE ⟨regs, idx :: .ref a :: rest⟩ = .ok () ⟨regs, idx :: .ref a :: rest⟩ := by
        bc_simp [_ITER_CHECK_RANGE, ho]
      constructor
      · intro hlen
        have hle : ¬ len ≤ 0 := by omega
        show (do _ITER_CHECK_RANGE; _ITER_JUMP_RANGE e; _ITER_NEXT_RANGE) _ = _
        simp only [bind, EStateM.bind, g1]
        bc_simp [_ITER_JUMP_RANGE, _ITER_NEXT_RANGE, ho, hle, setObj]
      · intro hlen
        show (do _ITER_CHECK_RANGE; _ITER_JUMP_RANGE e; _ITER_NEXT_RANGE) _ = _
        simp only [bind, EStateM.bind, g1]
        bc_simp [_ITER_JUMP_RANGE, ho, hlen, jumpBy_succ regs e.oparg]
    · intro hn
      cases it with
      | ref a =>
        obtain ⟨o, ho⟩ := live_obj hl
        cases o with
        | rangeIter st sp ln => exact absurd ⟨a, st, sp, ln, rfl, ho⟩ hn
        | _ => bc_simp [FOR_ITER_RANGE, _ITER_CHECK_RANGE, ho]
      | _ => bc_simp [FOR_ITER_RANGE, _ITER_CHECK_RANGE]

end PyLean.Bytecode
