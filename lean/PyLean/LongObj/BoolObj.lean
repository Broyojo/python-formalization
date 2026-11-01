import PyLean.LongObj.Conv

/-!
`Objects/boolobject.c`. `bool` is an `int` whose only values are `False` and `True`.
`PyObject_IsTrue` is generic: the constructors are modelled over an arbitrary argument
type with a truth oracle, which may raise.
-/

namespace PyLean.LongObj

open PyLean

/-- An operand of the `bool` number slots: a `bool`, or a plain `int`. -/
inductive BoolOperand where
  | b (x : Bool)
  | i (x : Int)
  deriving Repr, DecidableEq

/-- The value an operand has as an `int`. -/
def BoolOperand.toInt : BoolOperand → Int
  | .b true => 1
  | .b false => 0
  | .i x => x

/-- `bool_repr(self)`, boolobject.c:14-17. -/
def boolRepr (self : Bool) : String := if self then "True" else "False"

/-- `PyBool_FromLong(ok)`, boolobject.c:21-24. -/
def boolFromLong (ok : Int) : Bool := ok ≠ 0

def noKeywordsMsg : String := "bool() takes no keyword arguments"
def tooManyArgsMsg (n : Nat) : String := s!"bool expected at most 1 argument, got {n}"

/-- `bool_new(type, args, kwds)`, boolobject.c:29-42. -/
def boolNew {α : Type} (isTrue : α → Py Bool) (false_ : α) (args : List α) (kwds : Bool) :
    Py Bool :=
  if kwds then .error (.typeError noKeywordsMsg)
  else
    match args with
    | [] => match isTrue false_ with
      | .ok t => .ok (boolFromLong (if t then 1 else 0))
      | .error e => .error e
    | [x] => match isTrue x with
      | .ok t => .ok (boolFromLong (if t then 1 else 0))
      | .error e => .error e
    | _ => .error (.typeError (tooManyArgsMsg args.length))

/-- `bool_vectorcall(type, args, nargsf, kwnames)`, boolobject.c:45-66. -/
def boolVectorcall {α : Type} (isTrue : α → Py Bool) (args : List α) (kwnames : Bool) : Py Bool :=
  if kwnames then .error (.typeError noKeywordsMsg)
  else if args.length > 1 then .error (.typeError (tooManyArgsMsg args.length))
  else
    match args with
    | x :: _ => match isTrue x with
      | .ok t => .ok (boolFromLong (if t then 1 else 0))
      | .error e => .error e
    | [] => .ok (boolFromLong 0)

/-- The message of the `DeprecationWarning`, boolobject.c:73-79. -/
def boolInvertMsg : String :=
  "Bitwise inversion '~' on bool is deprecated and will be removed in " ++
  "Python 3.16. This returns the bitwise inversion of the underlying int " ++
  "object and is usually not what you expect from negating " ++
  "a bool. Use the 'not' operator for boolean negation or " ++
  "~int(x) if you really want the bitwise inversion of the " ++
  "underlying int."

/-- `bool_invert(v)`, boolobject.c:71-84. `warnRaises` is whether the warning filters
turn the `DeprecationWarning` into an exception. -/
def boolInvert (warnRaises : Bool) (v : Bool) : Py Int :=
  if warnRaises then .error (.named "DeprecationWarning" boolInvertMsg)
  else
    match longInvert (Long.ofInt (BoolOperand.b v).toInt) with
    | .ok x => .ok x.toInt
    | .error e => .error e

/-- `bool_and`, `bool_or`, `bool_xor`, boolobject.c:87-108: both `bool` gives a `bool`,
anything else goes to the `int` slot. -/
def boolOp (op : BitOp) (a b : BoolOperand) : Py BoolOperand :=
  match a, b with
  | .b x, .b y => .ok (.b (op.bool x y))
  | _, _ =>
    match longBit op (Long.ofInt a.toInt) (Long.ofInt b.toInt) with
    | .ok r => .ok (.i r.toInt)
    | .error e => .error e

/-- `bool(x)` through `tp_new` and through vectorcall agree on every argument list, for
every truth oracle, given that `False` is false. -/
theorem boolNew_eq_vectorcall {α : Type} (isTrue : α → Py Bool) (false_ : α)
    (hf : isTrue false_ = .ok false) (args : List α) (kw : Bool) :
    boolNew isTrue false_ args kw = boolVectorcall isTrue args kw := by
  simp only [boolNew, boolVectorcall]
  cases kw with
  | true => simp
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    match args with
    | [] => simp [hf]
    | [x] => simp
    | x :: y :: t =>
      have : (x :: y :: t).length > 1 := by simp
      simp [this]

theorem boolRepr_values : boolRepr true = "True" ∧ boolRepr false = "False" := ⟨rfl, rfl⟩

/-- `~True == -2` and `~False == -1`, the bitwise inversion of the underlying `int`, with
the deprecation raised instead when warnings are errors. -/
theorem boolInvert_spec (v : Bool) :
    boolInvert false v = .ok (-(BoolOperand.b v).toInt - 1) ∧
    boolInvert true v = .error (.named "DeprecationWarning" boolInvertMsg) := by
  constructor
  · have h := longInvert_spec (BoolOperand.b v).toInt (by cases v <;> decide)
    simp only [boolInvert, Bool.false_eq_true, ite_false, h, Long.toInt_ofInt]
  · rfl

/-- `bool & bool` and friends agree with the `int` operators on the values `0` and `1`,
and return a `bool`. -/
theorem boolOp_bool (op : BitOp) (x y : Bool) :
    boolOp op (.b x) (.b y) = .ok (.b (op.bool x y)) := rfl

/-- The `bool` result has the value the `int` operator gives on `0`/`1`, bit by bit. -/
theorem boolOp_agrees (op : BitOp) (x y : Bool) (i : Nat) :
    bitZ (BoolOperand.b (op.bool x y)).toInt i =
      op.bool (bitZ (BoolOperand.b x).toInt i) (bitZ (BoolOperand.b y).toInt i) := by
  have one : ∀ j : Nat, bitZ 1 j = decide (j = 0) := by
    intro j
    cases j with
    | zero => decide
    | succ n =>
      have h : bitZ ((1 : Nat) : Int) (n + 1) = if n + 1 < 1 then (1 : Nat).testBit (n + 1) else false :=
        bitZ_tc (s := false) (k := 1) (m := 1) (by decide) |>.symm ▸ (by simp [bitZ_tc])
      simpa using h
  have zero : ∀ j : Nat, bitZ 0 j = false := by
    intro j
    simp [bitZ]
  cases op <;> cases x <;> cases y <;>
    simp [BitOp.bool, BoolOperand.toInt, one, zero]

/-- A `bool` operand beside an `int` is the `int` `0` or `1`: the result is an `int` with
the two's complement bits of the operation. -/
theorem boolOp_mixed (op : BitOp) (x : Bool) (y : Int)
    (hy : MathInt.digitCount y.natAbs + 1 ≤ maxLongDigits) :
    ∃ r, boolOp op (.b x) (.i y) = .ok (.i r) ∧
      ∀ i, bitZ r i = op.bool (bitZ (BoolOperand.b x).toInt i) (bitZ y i) := by
  obtain ⟨r, h1, h2⟩ := longBit_spec op (BoolOperand.b x).toInt y (by cases x <;> decide) hy
  refine ⟨r, ?_, h2⟩
  have e : (BoolOperand.i y).toInt = y := rfl
  simp only [boolOp, e, h1, Long.toInt_ofInt]

end PyLean.LongObj
