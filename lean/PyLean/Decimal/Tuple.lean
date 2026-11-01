import PyLean.Decimal.Parse

/-!
`Decimal((sign, digits, exp))` and `Decimal.as_tuple()` in both twins, plus
`_pydecimal`'s `__str__` on its raw attributes.

Tuple items are Python objects; `PyVal` keeps the distinctions the two
constructors make: ints, bools (an `int` subclass: `isinstance(True, int)`
and `PyLong_Check(True)` both hold, `str(True) == 'True'`,
`PyLong_AsLong(True) == 1`), strings, and anything else.
-/

namespace PyLean.Decimal

open PyLean

inductive PyVal where
  | int (v : Int)
  | bool (b : Bool)
  | str (s : String)
  | other
  deriving Repr, DecidableEq, Inhabited

/-- Value of an `int` or `bool` (`PyLong_Check` holds). -/
def PyVal.asInt? : PyVal → Option Int
  | .int v => some v
  | .bool b => some (if b then 1 else 0)
  | _ => none

/-- `str(x)` of a digit accepted by `_pydecimal`'s check `0 <= digit <= 9`. -/
def PyVal.pyStr : PyVal → List Char
  | .int v => Nat.toDigits 10 v.toNat
  | .bool b => (if b then "True" else "False").toList
  | _ => []

/-- A `_pydecimal.Decimal` object's raw attributes: `_sign`, `_int` (a string)
and `_exp` (`int`, or a code `'F'`, `'n'`, `'N'`). -/
inductive PExp where
  | num (e : Int)
  | inf
  | qnan
  | snan
  deriving Repr, DecidableEq

structure PyObj where
  sign : Bool
  int : List Char
  exp : PExp
  deriving Repr, DecidableEq

/-- `_pydecimal.Decimal.__str__()`, _pydecimal.py:1076-1126, on raw attributes.
`"%+d" % n` formats an int, so a more than 4300-digit exponent raises. -/
def pyStrObj (o : PyObj) (caps : Bool := true) : Py (List Char) :=
  let sign := if o.sign then ['-'] else []
  match o.exp with
  | .inf => .ok (sign ++ "Infinity".toList)
  | .qnan => .ok (sign ++ "NaN".toList ++ o.int)
  | .snan => .ok (sign ++ "sNaN".toList ++ o.int)
  | .num e => do
    let leftdigits : Int := e + o.int.length
    let dotplace : Int := if e ≤ 0 ∧ leftdigits > -6 then leftdigits else 1
    if leftdigits ≠ dotplace then strLimit (leftdigits - dotplace).natAbs
    return sciFinite o.sign o.int e caps

/-- The attributes `_pydecimal` builds for a value. -/
def Dec.toPyObj : Dec → PyObj
  | .fin n c e => ⟨n, Nat.toDigits 10 c, .num e⟩
  | .inf n => ⟨n, ['0'], .inf⟩
  | .nan n s p => ⟨n, if p = 0 then [] else Nat.toDigits 10 p, if s then .snan else .qnan⟩

/-- `str(d)` in `_pydecimal`. -/
def pyStr (d : Dec) (caps : Bool := true) : Py (List Char) := pyStrObj d.toPyObj caps

/-- `isinstance(value[0], int) and value[0] in (0, 1)`, _pydecimal.py:648-652. -/
def pySign (s : PyVal) : Py Bool :=
  match s.asInt? with
  | some 0 => pure false
  | some 1 => pure true
  | _ => throw (.valueError "Invalid sign.  The first value in the tuple should be an integer; either 0 for a positive number or 1 for a negative number.")

/-- `_pydecimal.Decimal(value)` for a tuple `value = (s, digits, e)`,
_pydecimal.py:642-685 (the length check at :644 is the shape of the
argument here). `digits = none` is an object that is not iterable. -/
def pyFromTuple (s : PyVal) (digits : Option (List PyVal)) (e : PyVal) : Py PyObj := do
  let sign ← pySign s
  if e = .str "F" then
    -- infinity: value[1] is ignored
    return ⟨sign, ['0'], .inf⟩
  let some ds := digits | throw (.typeError "~not iterable")
  -- digits = [...] skipping leading zeros
  let rec collect : List PyVal → List PyVal → Py (List PyVal)
    | [], acc => .ok acc
    | d :: rest, acc =>
      match d.asInt? with
      | some v =>
        if 0 ≤ v ∧ v ≤ 9 then collect rest (if acc ≠ [] ∨ v ≠ 0 then acc ++ [d] else acc)
        else .error (.valueError "The second value in the tuple must be composed of integers in the range 0 through 9.")
      | none => .error (.valueError "The second value in the tuple must be composed of integers in the range 0 through 9.")
  let kept ← collect ds []
  let joined := kept.flatMap PyVal.pyStr
  match e with
  | .str "n" => return ⟨sign, joined, .qnan⟩
  | .str "N" => return ⟨sign, joined, .snan⟩
  | _ =>
    match e.asInt? with
    | some x => return ⟨sign, if kept = [] then ['0'] else joined, .num x⟩
    | none => throw (.valueError "The third value in the tuple must be an integer, or one of the strings 'F', 'n', 'N'.")

/-- One coefficient digit in `dectuple_as_str` (_decimal.c:2881-2903). -/
def cDigit (d : PyVal) : Py Nat :=
  match d.asInt? with
  | none => .error (.valueError "coefficient must be a tuple of digits")
  | some v =>
    if v < -(2 ^ 63) ∨ v ≥ 2 ^ 63 then .error (.overflowError "~Python int too large to convert to C long")
    else if v < 0 ∨ v > 9 then .error (.valueError "coefficient must be a tuple of digits")
    else .ok v.toNat

/-- `_decimal.Decimal(value)` for a tuple: `dectuple_as_str`
(_decimal.c:2779-2926) builds a numeric string which
`PyDecType_FromCStringExact` (:2351-2377) converts under the max context. -/
def cFromTuple (s : PyVal) (digits : Option (List PyVal)) (e : PyVal) : Py Dec := do
  -- sign
  let some sv := s.asInt? | throw (.valueError "sign must be an integer with the value 0 or 1")
  if sv < -(2 ^ 63) ∨ sv ≥ 2 ^ 63 then throw (.overflowError "~Python int too large to convert to C long")
  if sv ≠ 0 ∧ sv ≠ 1 then throw (.valueError "sign must be an integer with the value 0 or 1")
  let neg := sv = 1
  -- exponent or special code
  let kind : Option PExp ← match e with
    | .str "F" => pure (some .inf)
    | .str "n" => pure (some .qnan)
    | .str "N" => pure (some .snan)
    | .str _ => throw (.valueError "string argument in the third position must be 'F', 'n' or 'N'")
    | v => match v.asInt? with
      | none => throw (.valueError "exponent must be an integer")
      | some x =>
        if x < mpdSsizeMin ∨ x > mpdSsizeMax then throw (.overflowError "~Python int too large to convert to C ssize_t")
        else pure none
  -- coefficient: a tuple or a list of digits
  let some ds := digits | throw (.valueError "coefficient must be a tuple of digits")
  let vals ← ds.mapM cDigit
  let str := vals.map (fun v => Char.ofNat (48 + v))
  let p := digitsValue str
  let sigDigits := numDigits p
  match kind with
  | some .inf => return .inf neg
  | some .qnan | some .snan =>
    -- "NaN<digits>" through mpd_qset_string: the payload may have at most
    -- MPD_MAX_PREC significant digits
    if p ≠ 0 ∧ (sigDigits : Int) > mpdMaxPrec then throw invalidOp
    return .nan neg (kind = some .snan) p
  | _ =>
    let x := (e.asInt?).getD 0
    let d := Dec.fin neg p x
    if InCLimits d then return d else throw invalidOp

/-- `Decimal.as_tuple()` of `_pydecimal` (_pydecimal.py:1014-1019) and of
`_decimal` (`PyDec_AsTuple`, _decimal.c@3.14.7:4038-4129): sign, coefficient
digits (`(0,)` for an infinity, `()` for a NaN without payload) and the
exponent or code. -/
def asTuple (d : Dec) : PyVal × List PyVal × PyVal :=
  match d with
  | .fin n c e => (.int (if n then 1 else 0), (Nat.toDigits 10 c).map (fun ch => .int (ch.toNat - 48)), .int e)
  | .inf n => (.int (if n then 1 else 0), [.int 0], .str "F")
  | .nan n s p => (.int (if n then 1 else 0),
      (if p = 0 then [] else (Nat.toDigits 10 p).map (fun ch => .int (ch.toNat - 48))),
      .str (if s then "N" else "n"))

end PyLean.Decimal
