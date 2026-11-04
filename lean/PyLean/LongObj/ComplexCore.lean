import PyLean.Core

/-!
The arithmetic of `Objects/complexobject.c` (CPython 3.15.2), lines 27-397,
mirrored over an abstract C `double`.

`CDouble R` lists exactly the C operations on `double` that the file uses.
Nothing about them is assumed here: every property states its assumptions on
the instance as an explicit hypothesis. Two kinds of instance exist:

* a commutative ring or ordered field (`RingCompat`, `FieldCompat` in
  `ComplexAlgebra.lean`), where `isnan` and `isinf` are always false, so a
  theorem is a statement about the branch structure over exact arithmetic;
* `Dbl` (`ComplexDbl.lean`), exact IEEE-754 binary64, which is what the
  differential test runs and what refutations evaluate.

`errno` is a C global, and two findings hinge on it, so it is threaded
explicitly: each function takes the incoming value and returns the outgoing one.
-/

namespace PyLean.LongObj.Cplx

/-- The values of C `errno` that `complexobject.c` looks at. -/
inductive Errno where
  /-- `errno == 0`. -/
  | ok
  | edom
  | erange
  deriving DecidableEq, Repr, Inhabited

/-- The C `double` operations used by `Objects/complexobject.c`. -/
class CDouble (R : Type) where
  zero : R
  one : R
  /-- The literal `100.0` of line 754. -/
  hundred : R
  /-- `Py_INFINITY`. -/
  inf : R
  /-- `Py_NAN`. -/
  nan : R
  add : R → R → R
  sub : R → R → R
  mul : R → R → R
  div : R → R → R
  neg : R → R
  /-- C `==`. -/
  eq : R → R → Bool
  /-- C `<`. -/
  lt : R → R → Bool
  isnan : R → Bool
  isinf : R → Bool
  /-- `copysign(x, y)`. -/
  copysign : R → R → R
  fabs : R → R
  floor : R → R
  /-- The cast `(long)x` of line 755, used only on integral `|x| <= 100`. -/
  toLong : R → Int
  /-- `PyLong_AsDouble` on an exact integer; `none` is the overflow case. -/
  ofInt : Int → Option R
  /-- `float == int` as `float_richcompare` decides it: exactly, without
  converting the int to a double. -/
  eqInt : R → Int → Bool

namespace CDouble

variable {R : Type} [CDouble R]

scoped infixl:65 " +. " => CDouble.add
scoped infixl:65 " -. " => CDouble.sub
scoped infixl:70 " *. " => CDouble.mul
scoped infixl:70 " /. " => CDouble.div
scoped prefix:max "⊖" => CDouble.neg
scoped infix:50 " ==. " => CDouble.eq
scoped infix:50 " <. " => CDouble.lt

/-- C `isfinite`. -/
def isfinite (x : R) : Bool := !isnan x && !isinf x

/-- C `x >= y`: false when either side is a NaN. -/
def ge (x y : R) : Bool := lt y x || CDouble.eq x y

/-- C `x <= y`: false when either side is a NaN. -/
def le (x y : R) : Bool := lt x y || CDouble.eq x y

/-- C `x != y`: true when either side is a NaN. -/
def ne (x y : R) : Bool := !CDouble.eq x y

/-- The `b.real < 0 ? -b.real : b.real` of lines 195, 196, 268 and 269. -/
def absLt (x : R) : R := if lt x zero then neg x else x

end CDouble

open CDouble

/-- `Py_complex`. -/
structure Cx (R : Type) where
  real : R
  imag : R
  deriving DecidableEq, Repr, Inhabited

section arith

variable {R : Type} [CDouble R]

/-- `static Py_complex c_1 = {1., 0.};`, line 29. -/
def c_1 : Cx R := ⟨one, zero⟩

/-- `_Py_c_sum`, lines 31-38. -/
def c_sum (a b : Cx R) : Cx R := ⟨a.real +. b.real, a.imag +. b.imag⟩

/-- `_Py_cr_sum`, lines 40-46: only the real part changes. -/
def cr_sum (a : Cx R) (b : R) : Cx R := { a with real := a.real +. b }

/-- `_Py_rc_sum`, lines 48-52. -/
def rc_sum (a : R) (b : Cx R) : Cx R := cr_sum b a

/-- `_Py_c_diff`, lines 54-61. -/
def c_diff (a b : Cx R) : Cx R := ⟨a.real -. b.real, a.imag -. b.imag⟩

/-- `_Py_cr_diff`, lines 63-69. -/
def cr_diff (a : Cx R) (b : R) : Cx R := { a with real := a.real -. b }

/-- `_Py_rc_diff`, lines 71-78. -/
def rc_diff (a : R) (b : Cx R) : Cx R := ⟨a -. b.real, ⊖b.imag⟩

/-- `_Py_c_neg`, lines 80-87. -/
def c_neg (a : Cx R) : Cx R := ⟨⊖a.real, ⊖a.imag⟩

/-- The four mutable locals of `_Py_c_prod`, plus `recalc`. -/
structure ProdSt (R : Type) where
  a : R
  b : R
  c : R
  d : R
  recalc : Bool

/-- Lines 101-112: `z` is infinite. -/
def prodBoxZ (s : ProdSt R) : ProdSt R :=
  if isinf s.a || isinf s.b then
    { a := copysign (if isinf s.a then one else zero) s.a
      b := copysign (if isinf s.b then one else zero) s.b
      c := if isnan s.c then copysign zero s.c else s.c
      d := if isnan s.d then copysign zero s.d else s.d
      recalc := true }
  else s

/-- Lines 113-124: `w` is infinite. -/
def prodBoxW (s : ProdSt R) : ProdSt R :=
  if isinf s.c || isinf s.d then
    { c := copysign (if isinf s.c then one else zero) s.c
      d := copysign (if isinf s.d then one else zero) s.d
      a := if isnan s.a then copysign zero s.a else s.a
      b := if isnan s.b then copysign zero s.b else s.b
      recalc := true }
  else s

/-- Lines 125-140: recover infinities from overflow. -/
def prodOverflow (ac bd ad bc : R) (s : ProdSt R) : ProdSt R :=
  if !s.recalc && (isinf ac || isinf bd || isinf ad || isinf bc) then
    { a := if isnan s.a then copysign zero s.a else s.a
      b := if isnan s.b then copysign zero s.b else s.b
      c := if isnan s.c then copysign zero s.c else s.c
      d := if isnan s.d then copysign zero s.d else s.d
      recalc := true }
  else s

/-- `_Py_c_prod`, lines 89-148. -/
def c_prod (z w : Cx R) : Cx R :=
  let a := z.real
  let b := z.imag
  let c := w.real
  let d := w.imag
  let ac := a *. c
  let bd := b *. d
  let ad := a *. d
  let bc := b *. c
  let r : Cx R := ⟨ac -. bd, ad +. bc⟩
  if isnan r.real && isnan r.imag then
    let s := prodOverflow ac bd ad bc (prodBoxW (prodBoxZ ⟨a, b, c, d, false⟩))
    if s.recalc then
      ⟨inf *. (s.a *. s.c -. s.b *. s.d), inf *. (s.a *. s.d +. s.b *. s.c)⟩
    else r
  else r

/-- `_Py_cr_prod`, lines 150-157. -/
def cr_prod (a : Cx R) (b : R) : Cx R := ⟨a.real *. b, a.imag *. b⟩

/-- `_Py_rc_prod`, lines 159-163. -/
def rc_prod (a : R) (b : Cx R) : Cx R := cr_prod b a

/-- `_Py_c_quot`, lines 169-246. -/
def c_quot (a b : Cx R) (errno : Errno) : Cx R × Errno :=
  let abs_breal := absLt b.real
  let abs_bimag := absLt b.imag
  let (r, errno) : Cx R × Errno :=
    if ge abs_breal abs_bimag then
      if abs_breal ==. zero then
        (⟨zero, zero⟩, Errno.edom)
      else
        let ratio := b.imag /. b.real
        let denom := b.real +. b.imag *. ratio
        (⟨(a.real +. a.imag *. ratio) /. denom,
          (a.imag -. a.real *. ratio) /. denom⟩, errno)
    else if ge abs_bimag abs_breal then
      let ratio := b.real /. b.imag
      let denom := b.real *. ratio +. b.imag
      (⟨(a.real *. ratio +. a.imag) /. denom,
        (a.imag *. ratio -. a.real) /. denom⟩, errno)
    else
      (⟨nan, nan⟩, errno)
  let r : Cx R :=
    if isnan r.real && isnan r.imag then
      if (isinf a.real || isinf a.imag) && isfinite b.real && isfinite b.imag then
        let x := copysign (if isinf a.real then one else zero) a.real
        let y := copysign (if isinf a.imag then one else zero) a.imag
        ⟨inf *. (x *. b.real +. y *. b.imag), inf *. (y *. b.real -. x *. b.imag)⟩
      else if (isinf abs_breal || isinf abs_bimag) && isfinite a.real && isfinite a.imag then
        let x := copysign (if isinf b.real then one else zero) b.real
        let y := copysign (if isinf b.imag then one else zero) b.imag
        ⟨zero *. (a.real *. x +. a.imag *. y), zero *. (a.imag *. x -. a.real *. y)⟩
      else r
    else r
  (r, errno)

/-- `_Py_cr_quot`, lines 248-261. `if (b)` is `b != 0`, so a NaN `b` divides. -/
def cr_quot (a : Cx R) (b : R) (errno : Errno) : Cx R × Errno :=
  if ne b zero then (⟨a.real /. b, a.imag /. b⟩, errno)
  else (⟨zero, zero⟩, Errno.edom)

/-- `_Py_rc_quot`, lines 263-304. -/
def rc_quot (a : R) (b : Cx R) (errno : Errno) : Cx R × Errno :=
  let abs_breal := absLt b.real
  let abs_bimag := absLt b.imag
  let (r, errno) : Cx R × Errno :=
    if ge abs_breal abs_bimag then
      if abs_breal ==. zero then
        (⟨zero, zero⟩, Errno.edom)
      else
        let ratio := b.imag /. b.real
        let denom := b.real +. b.imag *. ratio
        (⟨a /. denom, ((⊖a) *. ratio) /. denom⟩, errno)
    else if ge abs_bimag abs_breal then
      let ratio := b.real /. b.imag
      let denom := b.real *. ratio +. b.imag
      (⟨(a *. ratio) /. denom, (⊖a) /. denom⟩, errno)
    else
      (⟨nan, nan⟩, errno)
  let r : Cx R :=
    if isnan r.real && isnan r.imag && isfinite a && (isinf abs_breal || isinf abs_bimag) then
      let x := copysign (if isinf b.real then one else zero) b.real
      let y := copysign (if isinf b.imag then one else zero) b.imag
      ⟨zero *. (a *. x), zero *. ((⊖a) *. y)⟩
    else r
  (r, errno)

/-- The libm functions the file calls. A call returns its value and `some e`
when it writes `errno`; `none` leaves `errno` alone, because a successful libm
call never clears it. Which values and which writes occur depends on the libm,
so a property that needs either says so in a hypothesis. `cos` and `sin` are the two
calls of lines 333-334; a compiler may merge them into one `sincos`, which is why
the libm is a parameter and not `cos` as a fixed function. -/
structure Libm (R : Type) where
  hypot : R → R → R × Option Errno
  pow : R → R → R × Option Errno
  atan2 : R → R → R × Option Errno
  exp : R → R × Option Errno
  log : R → R × Option Errno
  cos : R → R × Option Errno
  sin : R → R × Option Errno

/-- Apply a libm call's `errno` write. -/
def Errno.after (errno : Errno) : Option Errno → Errno
  | some e => e
  | none => errno

/-- `_Py_ADJUST_ERANGE2`, `Include/internal/pycore_pymath.h:45-57`. -/
def adjustERange2 (x y : R) (errno : Errno) : Errno :=
  if x ==. inf || x ==. ⊖inf || y ==. inf || y ==. ⊖inf then
    if errno = Errno.ok then Errno.erange else errno
  else if errno = Errno.erange then Errno.ok
  else errno

/-- `_Py_c_pow`, lines 309-339. -/
def c_pow (L : Libm R) (a b : Cx R) (errno : Errno) : Cx R × Errno :=
  if b.real ==. zero && b.imag ==. zero then
    (⟨one, zero⟩, errno)
  else if a.real ==. zero && a.imag ==. zero then
    let errno := if ne b.imag zero || b.real <. zero then Errno.edom else errno
    (⟨zero, zero⟩, errno)
  else
    let (vabs, e₁) := L.hypot a.real a.imag
    let errno := errno.after e₁
    let (len, e₂) := L.pow vabs b.real
    let errno := errno.after e₂
    let (at_, e₃) := L.atan2 a.imag a.real
    let errno := errno.after e₃
    let phase := at_ *. b.real
    let (len, phase, errno) : R × R × Errno :=
      if ne b.imag zero then
        let (ex, e₄) := L.exp ((⊖at_) *. b.imag)
        let errno := errno.after e₄
        let len := len *. ex
        let (lg, e₅) := L.log vabs
        let errno := errno.after e₅
        (len, phase +. b.imag *. lg, errno)
      else (len, phase, errno)
    let (co, e₆) := L.cos phase
    let errno := errno.after e₆
    let (si, e₇) := L.sin phase
    let errno := errno.after e₇
    let r : Cx R := ⟨len *. co, len *. si⟩
    (r, adjustERange2 r.real r.imag errno)

/-- A C `long` is 64-bit here; `mask <<= 1` wraps to `LONG_MIN` at `1 << 63`
(signed overflow, which is what the guard `mask > 0` relies on). -/
def wrapLong (v : Int) : Int :=
  let m := v % (2 ^ 64 : Int)
  if m ≥ 2 ^ 63 then m - 2 ^ 64 else m

/-- `n & mask` for the loop of `c_powu`, whose guard gives `n >= mask > 0`. -/
def longAndNonzero (n mask : Int) : Bool := (n.toNat &&& mask.toNat) != 0

/-- The `while` of `c_powu`, lines 348-353. The guard is true at most 63 times,
because `mask` leaves the positive range on the 63rd shift. -/
def powuLoop : Nat → Int → Cx R → Cx R → Int → Cx R
  | 0, _, r, _, _ => r
  | fuel + 1, mask, r, p, n =>
    if mask > 0 ∧ n ≥ mask then
      let r := if longAndNonzero n mask then c_prod r p else r
      powuLoop fuel (wrapLong (mask * 2)) r (c_prod p p) n
    else r

/-- `c_powu`, lines 341-355. -/
def c_powu (x : Cx R) (n : Int) : Cx R := powuLoop 64 1 c_1 x n

/-- `c_powi`, lines 357-365. -/
def c_powi (x : Cx R) (n : Int) (errno : Errno) : Cx R × Errno :=
  if n > 0 then (c_powu x n, errno)
  else c_quot c_1 (c_powu x (-n)) errno

/-- `_Py_c_abs`, lines 367-397. The third branch is the only one that leaves
`errno` as it found it, despite the comment on line 370. -/
def c_abs (L : Libm R) (z : Cx R) (errno : Errno) : R × Errno :=
  if !isfinite z.real || !isfinite z.imag then
    if isinf z.real then (fabs z.real, Errno.ok)
    else if isinf z.imag then (fabs z.imag, Errno.ok)
    else (nan, errno)
  else
    let (result, _) := L.hypot z.real z.imag
    if !isfinite result then (result, Errno.erange) else (result, Errno.ok)

end arith

end PyLean.LongObj.Cplx
