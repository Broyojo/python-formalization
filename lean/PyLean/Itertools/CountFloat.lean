import PyLean.Itertools.CountRepeatProps
import PyLean.Binary64.Float
import PyLean.Binary64.Dtoa

/-!
`count` on real Python numbers: the number types of `CountRepeat.lean` instantiated
with `float` (exact, by `Binary64`), `bool`, `Raising`, a class that passes
`PyNumber_Check` through `__float__` and whose `__add__` and `__radd__` raise, and
`RaisingInt`, an int subclass with those same methods, which is `.intSub i .raising`.
This is what the difftest runs, and what refutes the two doc comparisons.
-/

namespace PyLean.Itertools

open PyLean

/-- The rest of an object, for the numbers the difftest uses. -/
inductive PyNum where
  | float (x : Binary64.F64)
  | bool (b : Bool)
  | raising
  | str

/-- `PyFloat_AsDouble` of the operand of `float_add`, for an int or a float. -/
def numToDouble : CVal PyNum → Py Binary64.F64
  | .int i | .intSub i _ => Binary64.PyLong_AsDouble i
  | .num (.float x) => .ok x
  | _ => .error (.typeError "~unsupported operand")

def isFloatVal : CVal PyNum → Bool
  | .num (.float _) => true
  | _ => false

/-- Whether `a + b` reaches a raising `__add__` or `__radd__`. `Raising` wins over
everything: `float_add` and `long_add` answer `NotImplemented` for it. `RaisingInt` is
an int, so they accept it: its `__add__` runs when it is on the left, and its `__radd__`
goes first only against a type it subclasses, the exact int, not `bool` or `float`. -/
def addRaises : CVal PyNum → CVal PyNum → Bool
  | .num .raising, _ | _, .num .raising => true
  | .intSub _ .raising, _ => true
  | .int _, .intSub _ .raising => true
  | _, _ => false

/-- A raising method first. With a float operand, `float_add`
(Objects/floatobject.c), whose conversion of a huge int raises `OverflowError`;
otherwise two int-likes, whose sum is an exact int. -/
def numAdd (a b : CVal PyNum) : Py (CVal PyNum) :=
  if addRaises a b then .error (.valueError "add")
  else if isFloatVal a || isFloatVal b then
    match numToDouble a with
    | .error e => .error e
    | .ok x =>
      match numToDouble b with
      | .error e => .error e
      | .ok y => .ok (.num (.float (Binary64.F64.add x y)))
  else .ok (.int (a.longVal + b.longVal))

/-- `repr` of the non-int numbers. -/
def numRepr : CVal PyNum → Py String
  | .num (.float x) =>
    match Binary64.float_repr x with
    | some r => .ok (String.ofList (r.map Char.ofNat))
    | none => .error (.valueError "~float_repr")
  | .intSub _ (.bool b) => .ok (if b then "True" else "False")
  | .intSub i .raising => .ok (toString i)
  | .num .raising => .ok "Raising()"
  | _ => .ok "?"

def numOps : NumOps PyNum := ⟨numAdd, numRepr⟩

/-- `x, x + y, x + y + y, ...`, in floating point. -/
def floatSeq (y : Binary64.F64) : Nat → Binary64.F64 → List Binary64.F64
  | 0, _ => []
  | k + 1, x => x :: floatSeq y k (Binary64.F64.add x y)

theorem doc_floatSeq (y : Binary64.F64) : ∀ (k : Nat) (x : Binary64.F64),
    docCountRun numOps (.num (.float y)) k (.num (.float x)) =
      ((floatSeq y k x).map (fun v => CVal.num (PyNum.float v)), none)
  | 0, _ => rfl
  | 1, _ => rfl
  | k + 2, x => by
    have := doc_floatSeq y (k + 1) (Binary64.F64.add x y)
    simp only [docCountRun, floatSeq, pyAdd, numOps, numAdd, addRaises, isFloatVal, numToDouble]
    simp only [Bool.false_or, Bool.or_false, Bool.false_eq_true, if_false, Bool.true_or, if_true]
    simp only [numOps] at this
    rw [this]
    simp [floatSeq]

/-- `count(x, y)` on two floats, for all floats (infinities and NaNs included, whose
payloads are not modelled) and every `k`: the values are `x`, `x + y`, `x + y + y`,
... by repeated IEEE-754 addition, as the doc's generator computes them, and not
`x + k * y`, which is why the docs suggest `(start + step * i for i in count())` for
accuracy (rst:333-335). No exception is possible. -/
def CountFloatDocAgree : Prop :=
  ∀ (x y : Binary64.F64) (k : Nat),
    opVals (cCount numOps (some (.num (.float x))) (some (.num (.float y))) (List.replicate k .next)) =
      ((floatSeq y k x).map (fun v => CVal.num (PyNum.float v)), none)

theorem countFloatDocAgree_proven : CountFloatDocAgree := by
  intro x y k
  rw [← doc_floatSeq]
  exact countDocAgreeClosed_proven PyNum numOps _ _ (fun a => isFloatVal a = true) k rfl rfl
    (by simp [NoIntSub]) (by simp [NoIntSub])
    (fun a ha => by
      cases a with
      | num v =>
        cases v with
        | float u => exact ⟨.num (.float (Binary64.F64.add u y)), by simp [pyAdd, numOps, numAdd, addRaises, isFloatVal, numToDouble], rfl⟩
        | bool b => simp [isFloatVal] at ha
        | raising => simp [isFloatVal] at ha
        | str => simp [isFloatVal] at ha
      | int i => simp [isFloatVal] at ha
      | intSub i v => simp [isFloatVal] at ha
      | nonNum v => simp [isFloatVal] at ha)
    rfl

/-- The add fails on the first value: C raises at once, where the doc's generator
yields it first. A `Raising` start is the simplest such number; the same happens
with `count(10**400, 1.0)`, whose add is `OverflowError`. -/
theorem countDocAgreeAll_refuted : ¬CountDocAgreeAll := by
  intro h
  have := congrArg (fun r => r.1.length)
    (h PyNum numOps (.num .raising) (.num (.float Binary64.F64.one)) 1 rfl rfl)
  simp [cCount, cCountNew, argBad, argLong, CVal.isNumber, CVal.isLong, cCountOps, cCountNext, pyAdd,
    numOps, numAdd, addRaises, opVals, docCountRun, List.replicate, CVal.longVal] at this

/-- `count(True)`: the add never fails, yet C gives the int 1 where the doc's
generator gives `True`. -/
theorem countDocAgreeTotalAdd_refuted : ¬CountDocAgreeTotalAdd := by
  intro h
  have := congrArg (fun r => r.1.map (fun v => match v with | CVal.intSub _ _ => true | _ => false))
    (h PyNum numOps (.intSub 1 (.bool true)) (.int 1)
      (fun a => a.isLong = true ∧ addRaises a (.int 1) = false) 1 rfl rfl
      (fun a ha => by
        cases a with
        | int i => exact ⟨_, rfl, rfl, rfl⟩
        | intSub i v =>
          cases v with
          | raising => simp [addRaises] at ha
          | _ => exact ⟨.int (i + 1), by simp [pyAdd, numOps, numAdd, addRaises, isFloatVal, CVal.longVal],
              rfl, rfl⟩
        | num v => simp [CVal.isLong] at ha
        | nonNum v => simp [CVal.isLong] at ha)
      ⟨rfl, rfl⟩)
  simp [cCount, cCountNew, argBad, argLong, CVal.isNumber, CVal.isLong, cCountOps, cCountNext, CVal.longVal,
    asSsize, asLongOrMinus1, ssizeMin_eq, ssizeMax_eq, opVals, docCountRun, List.replicate] at this

end PyLean.Itertools
