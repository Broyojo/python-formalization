import PyLean.CoreLibs.Rand.Mt

/-!
The interface between `Lib/random.py` and its core generator.

`Lib/random.py:277-282` promises that everything below the core "only access
randomness through the methods: random(), getrandbits(), or _randbelow()". The
model takes that literally: the Python layer is written against a `Gen`, a record
of those methods over an arbitrary state `σ`. `Random` itself is one `Gen` (over
`Mt.State`), `SystemRandom` is another, and a user subclass is any other. A
property of the Python layer is stated for every `Gen` that meets its documented
contract, and then applies to each of them.

Floats: the type `F` is a parameter with the raw IEEE operations in `Flt`. Lean's
`Float` is one instance (used by the difftest, see `FloatInst.lean`). Lean cannot
reduce `Float` operations, so properties never look inside `F`: what they say is
either about the integers around the floats, or about every `Flt` satisfying the
IEEE NaN rules (`Dist.lean`).
-/

namespace PyLean.CoreLibs.Rand

open PyLean

/-! ### The state-and-exception monad -/

/-- A method call on the generator: the state changes even when an exception
comes out (`Random.choices([], k=1)` draws, then raises). -/
def RM (σ α : Type) : Type := σ → Py α × σ

namespace RM

variable {σ α β : Type}

@[inline] protected def pure (a : α) : RM σ α := fun s => (.ok a, s)

@[inline] protected def bind (x : RM σ α) (f : α → RM σ β) : RM σ β := fun s =>
  match x s with
  | (.ok a, s') => f a s'
  | (.error e, s') => (.error e, s')

instance : Monad (RM σ) where
  pure := RM.pure
  bind := RM.bind

/-- `raise e`. -/
@[inline] def raise (e : PyExc) : RM σ α := fun s => (.error e, s)

/-- A pure computation that can raise. -/
@[inline] def lift (x : Py α) : RM σ α := fun s => (x, s)

@[simp] theorem pure_apply (a : α) (s : σ) : (Pure.pure a : RM σ α) s = (.ok a, s) := rfl

@[simp] theorem bind_apply (x : RM σ α) (f : α → RM σ β) (s : σ) :
    (x >>= f) s = match x s with
      | (.ok a, s') => f a s'
      | (.error e, s') => (.error e, s') := rfl

@[simp] theorem raise_apply (e : PyExc) (s : σ) : (raise e : RM σ α) s = (.error e, s) := rfl
@[simp] theorem lift_apply (x : Py α) (s : σ) : (lift x : RM σ α) s = (x, s) := rfl

end RM

/-! ### The core generator -/

/-- What the Python layer calls on `self`. -/
structure Gen (σ F : Type) where
  /-- `self.random()`. -/
  random : σ → F × σ
  /-- `self.getrandbits(k)`. -/
  getrandbits : IntArg → RM σ Nat

/-- The contract of `getrandbits`: "Generates an int with k random bits"
(`Modules/_randommodule.c:503`, `Lib/random.py:911`). -/
def Gen.Valid {σ F : Type} (g : Gen σ F) : Prop :=
  ∀ (k : Nat) (r : Nat) (s s' : σ), g.getrandbits (.int k) s = (.ok r, s') → r < 2 ^ k

/-- The raw IEEE 754 operations on a float type. `lt`, `le`, `beq` are IEEE
comparisons, `pow`, `log`, ... the C library's. Python's exceptions are added in
the wrappers below, as in `Modules/mathmodule.c` and `Objects/floatobject.c`. -/
class Flt (F : Type) extends Inhabited F, OfScientific F, Add F, Sub F, Mul F, Div F, Neg F where
  lt : F → F → Bool
  le : F → F → Bool
  beq : F → F → Bool
  isNan : F → Bool
  isInf : F → Bool
  sqrt : F → F
  log : F → F
  log2 : F → F
  exp : F → F
  sin : F → F
  cos : F → F
  acos : F → F
  pow : F → F → F
  fabs : F → F
  /-- `fmod`, always exact. -/
  fmod : F → F → F
  /-- `math.lgamma` on finite arguments: `m_lgamma`, Modules/mathmodule.c:483-524. -/
  lgamma : F → F
  /-- `math.floor` of a finite float, exactly. -/
  floorInt : F → Int
  /-- `float(n)`: correctly rounded, `none` on overflow. -/
  ofInt : Int → Option F
  /-- `x < n` compared exactly. -/
  ltInt : F → Int → Bool
  /-- `x == floor(x)`. -/
  isInteger : F → Bool
  /-- `DOUBLE_IS_ODD_INTEGER(x)`. -/
  isOddInteger : F → Bool
  /-- `copysign(0.0, x)`. -/
  zeroLike : F → F

namespace Flt

variable {F : Type} [Flt F]

instance : LT F := ⟨fun a b => Flt.lt a b = true⟩
instance : LE F := ⟨fun a b => Flt.le a b = true⟩
instance (a b : F) : Decidable (a < b) := inferInstanceAs (Decidable (Flt.lt a b = true))
instance (a b : F) : Decidable (a ≤ b) := inferInstanceAs (Decidable (Flt.le a b = true))

/-- Python's truthiness of a float. -/
def truthy (x : F) : Bool := !Flt.beq x 0.0

def isFinite (x : F) : Bool := !(isNan x || isInf x)

/-- `float(n)` for an `int`, as binary operators do it (`convert_to_double`,
Objects/floatobject.c). -/
def pyFloat (n : Int) : Py F :=
  match ofInt n with
  | some x => .ok x
  | none => .error (.overflowError "int too large to convert to float")

/-- `a / b` on floats: `float_div`, Objects/floatobject.c. -/
def pyDiv (a b : F) : Py F :=
  if Flt.beq b 0.0 then .error (.zeroDivisionError "division by zero") else .ok (a / b)

/-- `a % b` on floats: `float_rem`, Objects/floatobject.c:587-611. -/
def pyMod (v w : F) : Py F :=
  if Flt.beq w 0.0 then .error (.zeroDivisionError "division by zero")
  else
    let m := fmod v w
    if truthy m then
      if Flt.lt w 0.0 != Flt.lt m 0.0 then .ok (m + w) else .ok m
    else .ok (zeroLike w)

/-- `a ** b` on floats: `float_pow`, Objects/floatobject.c:687-803. The complex-result
branch at :759 is not modelled: `Lib/random.py` cannot reach it, because every base
there is `>= 0`, so it gets a marker exception that the difftest would expose. -/
def pyPow (iv iw : F) : Py F :=
  if Flt.beq iw 0.0 then .ok 1.0
  else if isNan iv then .ok iv
  else if isNan iw then .ok (if Flt.beq iv 1.0 then 1.0 else iw)
  else if isInf iw then
    let av := fabs iv
    if Flt.beq av 1.0 then .ok 1.0
    else if Flt.lt 0.0 iw == Flt.lt 1.0 av then .ok (fabs iw)
    else .ok 0.0
  else if isInf iv then
    let odd := isOddInteger iw
    if Flt.lt 0.0 iw then .ok (if odd then iv else fabs iv)
    else .ok (if odd then zeroLike iv else 0.0)
  else if Flt.beq iv 0.0 then
    let odd := isOddInteger iw
    if Flt.lt iw 0.0 then .error (.zeroDivisionError "zero to a negative power")
    else .ok (if odd then iv else 0.0)
  else
    if Flt.lt iv 0.0 && !isInteger iw then
      .error (.named "ModelUnreached" "negative base to a fractional power")
    else
      let neg := Flt.lt iv 0.0 && isOddInteger iw
      let av := if Flt.lt iv 0.0 then -iv else iv
      if Flt.beq av 1.0 then .ok (if neg then -1.0 else 1.0)
      else
        let ix := pow av iw
        if isInf ix then
          .error (.overflowError "(34, 'Numerical result out of range')")
        else .ok (if neg then -ix else ix)

/-- `math_1` with `can_overflow = 1`, Modules/mathmodule.c:788-825. -/
def math1Over (f : F → F) (x : F) : Py F :=
  let r := f x
  if isNan r && !isNan x then .error (.valueError "~math domain error")
  else if isInf r && isFinite x then .error (.overflowError "math range error")
  else .ok r

/-- `math_1` with `can_overflow = 0` and an `err_msg`, Modules/mathmodule.c:788-825.
Every such message embeds the argument. -/
def math1Dom (f : F → F) (x : F) : Py F :=
  let r := f x
  if isNan r && !isNan x then .error (.valueError "~domain")
  else if isInf r && isFinite x then .error (.valueError "~domain")
  else .ok r

def mathSqrt (x : F) : Py F := math1Dom sqrt x
def mathExp (x : F) : Py F := math1Over exp x
def mathSin (x : F) : Py F := math1Dom sin x
def mathCos (x : F) : Py F := math1Dom cos x
def mathAcos (x : F) : Py F := math1Dom acos x

/-- `math.log(x)`, `m_log`, Modules/mathmodule.c: `x <= 0` is a domain error, nan
and inf pass through. -/
def mathLog (x : F) : Py F :=
  if isNan x then .ok x
  else if Flt.le x 0.0 then .error (.valueError "~domain")
  else .ok (log x)

/-- `math.log2(x)`, same shape as `mathLog`. -/
def mathLog2 (x : F) : Py F :=
  if isNan x then .ok x
  else if Flt.le x 0.0 then .error (.valueError "~domain")
  else .ok (log2 x)

/-- `math.lgamma(x)`, through `math_1a`: `m_lgamma` sets `ERANGE` for an infinite
result from a finite argument. -/
def mathLgamma (x : F) : Py F :=
  if isNan x then .ok x
  else if isInf x then .ok (fabs x)
  else
    let r := lgamma x
    if isInf r then .error (.overflowError "math range error") else .ok r

/-- `math.floor(x)` on a float: `float.__floor__`, Objects/floatobject.c. -/
def mathFloor (x : F) : Py Int :=
  if isNan x then .error (.valueError "cannot convert float NaN to integer")
  else if isInf x then .error (.overflowError "cannot convert float infinity to integer")
  else .ok (floorInt x)

/-- `NV_MAGICCONST = 4 * _exp(-0.5) / _sqrt(2.0)`, Lib/random.py:94. -/
def NV_MAGICCONST : F := 4.0 * exp (-0.5) / sqrt 2.0
/-- `LOG4 = _log(4.0)`, Lib/random.py:95. -/
def LOG4 : F := log 4.0
/-- `SG_MAGICCONST = 1.0 + _log(4.5)`, Lib/random.py:96. -/
def SG_MAGICCONST : F := 1.0 + log 4.5
/-- `math.tau`, imported as `TWOPI`, Lib/random.py:55. -/
def TWOPI : F := 6.283185307179586
/-- `math.pi`. -/
def PI : F := 3.141592653589793
/-- `math.e`. -/
def E : F := 2.718281828459045

end Flt

end PyLean.CoreLibs.Rand
