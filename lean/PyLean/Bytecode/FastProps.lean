import PyLean.Bytecode.SpecFastCmpIter
import PyLean.Bytecode.Props

/-!
Registry forms of the specialized instructions: each is the adaptive interpreter's contract
(the specialized form steps as its generic form on every stack, `withDeopt` included) together
with the fast path's own behaviour from `SpecFast*.lean`, so a fast path that always exits, or a
guard that rejects or accepts the wrong values, fails the statement.
-/

namespace PyLean.Bytecode

open Uop

def ToBoolRules : Prop := ToBoolSpecialized ∧ ToBoolFast
theorem toBoolRules_proven : ToBoolRules := ⟨toBoolSpecialized_proven, toBoolFast_proven⟩

def BinaryMulIntRules : Prop :=
  BinaryMulInt ∧ IntUop _BINARY_OP_MULTIPLY_INT (· * ·) ∧ IntArith BINARY_OP_MULTIPLY_INT (· * ·)
theorem binaryMulIntRules_proven : BinaryMulIntRules :=
  ⟨binaryMulInt_proven, binaryIntFast_proven.1, binaryIntFast_proven.2.1⟩

def BinaryAddIntRules : Prop :=
  BinaryAddInt ∧ IntUop _BINARY_OP_ADD_INT (· + ·) ∧ IntArith BINARY_OP_ADD_INT (· + ·)
theorem binaryAddIntRules_proven : BinaryAddIntRules :=
  ⟨binaryAddInt_proven, binaryIntFast_proven.2.2.1, binaryIntFast_proven.2.2.2.1⟩

def BinarySubIntRules : Prop :=
  BinarySubInt ∧ IntUop _BINARY_OP_SUBTRACT_INT (· - ·) ∧ IntArith BINARY_OP_SUBTRACT_INT (· - ·)
theorem binarySubIntRules_proven : BinarySubIntRules :=
  ⟨binarySubInt_proven, binaryIntFast_proven.2.2.2.2.1, binaryIntFast_proven.2.2.2.2.2⟩

def BinaryMulFloatRules : Prop := BinaryMulFloat ∧
  KindUop _BINARY_OP_MULTIPLY_FLOAT IsFloat (fop fmul) ∧ KindArith BINARY_OP_MULTIPLY_FLOAT IsFloat (fop fmul)
theorem binaryMulFloatRules_proven : BinaryMulFloatRules :=
  ⟨binaryMulFloat_proven, binaryKindFast_proven.1, binaryKindFast_proven.2.1⟩

def BinaryAddFloatRules : Prop := BinaryAddFloat ∧
  KindUop _BINARY_OP_ADD_FLOAT IsFloat (fop fadd) ∧ KindArith BINARY_OP_ADD_FLOAT IsFloat (fop fadd)
theorem binaryAddFloatRules_proven : BinaryAddFloatRules :=
  ⟨binaryAddFloat_proven, binaryKindFast_proven.2.2.1, binaryKindFast_proven.2.2.2.1⟩

def BinarySubFloatRules : Prop := BinarySubFloat ∧
  KindUop _BINARY_OP_SUBTRACT_FLOAT IsFloat (fop fsub) ∧ KindArith BINARY_OP_SUBTRACT_FLOAT IsFloat (fop fsub)
theorem binarySubFloatRules_proven : BinarySubFloatRules :=
  ⟨binarySubFloat_proven, binaryKindFast_proven.2.2.2.2.1, binaryKindFast_proven.2.2.2.2.2.1⟩

def BinaryAddUnicodeRules : Prop := BinaryAddUnicode ∧
  KindUop _BINARY_OP_ADD_UNICODE IsStr sconcat ∧ KindArith BINARY_OP_ADD_UNICODE IsStr sconcat
theorem binaryAddUnicodeRules_proven : BinaryAddUnicodeRules :=
  ⟨binaryAddUnicode_proven, binaryKindFast_proven.2.2.2.2.2.2.1, binaryKindFast_proven.2.2.2.2.2.2.2⟩

def SubscrListIntRules : Prop := SubscrListInt ∧ SubscrListFast
theorem subscrListIntRules_proven : SubscrListIntRules := ⟨subscrListInt_proven, subscrListFast_proven⟩

def SubscrStrIntRules : Prop := SubscrStrInt ∧ SubscrStrFast
theorem subscrStrIntRules_proven : SubscrStrIntRules := ⟨subscrStrInt_proven, subscrStrFast_proven⟩

def SubscrTupleIntRules : Prop := SubscrTupleInt ∧ SubscrTupleFast
theorem subscrTupleIntRules_proven : SubscrTupleIntRules :=
  ⟨subscrTupleInt_proven, subscrTupleFast_proven⟩

def StoreSubscrListIntRules : Prop := StoreSubscrListInt ∧ StoreSubscrListFast
theorem storeSubscrListIntRules_proven : StoreSubscrListIntRules :=
  ⟨storeSubscrListInt_proven, storeSubscrListFast_proven⟩

/-- `COMPARE_OP_INT` is `COMPARE_OP`, and on two compact ints answers their order. -/
def CompareIntRules : Prop := CompareInt ∧ ∀ (e : Env) (regs : Regs) (rest : List Val) (l r : Val),
  (CmpArg e.oparg → ∀ a b, l = .int a → r = .int b → Compact a → Compact b →
    COMPARE_OP_INT e ⟨regs, r :: l :: rest⟩ = .ok () ⟨regs, .bool (cmpInt (e.oparg >>> 5) a b) :: rest⟩) ∧
  (¬ (CompactInt l ∧ CompactInt r) →
    COMPARE_OP_INT e ⟨regs, r :: l :: rest⟩ = .error .deopt ⟨regs, r :: l :: rest⟩)
theorem compareIntRules_proven : CompareIntRules :=
  ⟨compareInt_proven, fun e regs rest l r =>
    ⟨(compareFast_proven e regs rest l r).1, (compareFast_proven e regs rest l r).2.1⟩⟩

/-- `COMPARE_OP_FLOAT` is `COMPARE_OP`, and on two floats answers the IEEE-754 relation. -/
def CompareFloatRules : Prop := CompareFloat ∧ ∀ (e : Env) (regs : Regs) (rest : List Val) (l r : Val),
  (CmpArg e.oparg → ∀ a b, l = .float a → r = .float b →
    COMPARE_OP_FLOAT e ⟨regs, r :: l :: rest⟩ =
      .ok () ⟨regs, .bool (floatTable (e.oparg >>> 5) (toF a) (toF b)) :: rest⟩) ∧
  (¬ (IsFloat l ∧ IsFloat r) →
    COMPARE_OP_FLOAT e ⟨regs, r :: l :: rest⟩ = .error .deopt ⟨regs, r :: l :: rest⟩)
theorem compareFloatRules_proven : CompareFloatRules :=
  ⟨compareFloat_proven, fun e regs rest l r =>
    ⟨(compareFast_proven e regs rest l r).2.2.1, (compareFast_proven e regs rest l r).2.2.2.1⟩⟩

/-- `COMPARE_OP_STR` is `COMPARE_OP` for `==` and `!=`, and on two strs answers (in)equality. -/
def CompareStrRules : Prop := CompareStr ∧ ∀ (e : Env) (regs : Regs) (rest : List Val) (l r : Val),
  (e.oparg >>> 5 = 2 → e.oparg &&& 15 = 8 → ∀ a b, l = .str a → r = .str b →
    COMPARE_OP_STR e ⟨regs, r :: l :: rest⟩ = .ok () ⟨regs, .bool (a == b) :: rest⟩) ∧
  (e.oparg >>> 5 = 3 → e.oparg &&& 15 = 7 → ∀ a b, l = .str a → r = .str b →
    COMPARE_OP_STR e ⟨regs, r :: l :: rest⟩ = .ok () ⟨regs, .bool (a != b) :: rest⟩) ∧
  (¬ (IsStr l ∧ IsStr r) →
    COMPARE_OP_STR e ⟨regs, r :: l :: rest⟩ = .error .deopt ⟨regs, r :: l :: rest⟩)
theorem compareStrRules_proven : CompareStrRules :=
  ⟨compareStr_proven, fun e regs rest l r =>
    ⟨(compareFast_proven e regs rest l r).2.2.2.2.1, (compareFast_proven e regs rest l r).2.2.2.2.2.1,
     (compareFast_proven e regs rest l r).2.2.2.2.2.2⟩⟩

def ForIterSeqRules : Prop := ForIterSeq ∧ ∀ (e : Env),
  SeqIterFast (FOR_ITER_LIST e) IsList .list e.oparg ∧ SeqIterFast (FOR_ITER_TUPLE e) IsTuple .tuple e.oparg
theorem forIterSeqRules_proven : ForIterSeqRules :=
  ⟨forIterSeq_proven, fun e => ⟨(forIterFast_proven e).1, (forIterFast_proven e).2.1⟩⟩

def ForIterRangeRules : Prop := ForIterRange ∧ ∀ (e : Env), RangeIterFast e
theorem forIterRangeRules_proven : ForIterRangeRules :=
  ⟨forIterRange_proven, fun e => (forIterFast_proven e).2.2⟩

end PyLean.Bytecode
