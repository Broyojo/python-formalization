import PyLean.Binary64.Dtoa

/-!
`Objects/complexobject.c`, CPython 3.14.7, the float paths. The transcendental C library
functions are parameters (`Libm`): the body of each function is mirrored and every
property holds for any C library. The `__format__` machinery lives in
`Python/formatter_unicode.c` and is not modelled here.
-/

namespace PyLean.Binary64

open PyLean

/-- `Py_complex`. -/
structure C where
  re : F64
  im : F64
  deriving DecidableEq, Repr, Inhabited

/-- The C library functions `complexobject.c` calls. -/
structure Libm where
  hypot : F64 → F64 → F64
  pow : F64 → F64 → F64
  atan2 : F64 → F64 → F64
  exp : F64 → F64
  log : F64 → F64
  cos : F64 → F64
  sin : F64 → F64
  /-- Whether `cos` and `sin` of this argument set `errno` to `EDOM`. POSIX asks for that on
  an infinity, and glibc does it. -/
  trigEdom : F64 → Bool

/-- `c_1`, complexobject.c:29. -/
def c_1 : C := ⟨d1, d0⟩

abbrev fadd := F64.add
abbrev fsub := F64.sub
abbrev fmul := F64.mul
abbrev fdiv := F64.div

/-- `_Py_c_sum`, complexobject.c:31-38. -/
def _Py_c_sum (a b : C) : C := ⟨fadd a.re b.re, fadd a.im b.im⟩

/-- `_Py_cr_sum`, complexobject.c:40-46. -/
def _Py_cr_sum (a : C) (b : F64) : C := ⟨fadd a.re b, a.im⟩

/-- `_Py_rc_sum`, complexobject.c:48-52. -/
def _Py_rc_sum (a : F64) (b : C) : C := _Py_cr_sum b a

/-- `_Py_c_diff`, complexobject.c:54-61. -/
def _Py_c_diff (a b : C) : C := ⟨fsub a.re b.re, fsub a.im b.im⟩

/-- `_Py_cr_diff`, complexobject.c:63-69. -/
def _Py_cr_diff (a : C) (b : F64) : C := ⟨fsub a.re b, a.im⟩

/-- `_Py_rc_diff`, complexobject.c:71-78. -/
def _Py_rc_diff (a : F64) (b : C) : C := ⟨fsub a b.re, b.im.neg⟩

/-- `_Py_c_neg`, complexobject.c:80-87. -/
def _Py_c_neg (a : C) : C := ⟨a.re.neg, a.im.neg⟩

/-- `copysign(isinf(x) ? 1.0 : 0.0, x)`. -/
def boxInf (x : F64) : F64 := F64.copysign (if x.isInf then d1 else d0) x

/-- `if (isnan(x)) x = copysign(0.0, x)`. -/
def nanToZero (x : F64) : F64 := if x.isNaN then F64.copysign d0 x else x

/-- `_Py_c_prod`, complexobject.c:89-148. -/
def _Py_c_prod (z w : C) : C :=
  let a0 := z.re; let b0 := z.im; let c0 := w.re; let d0' := w.im
  let ac := fmul a0 c0; let bd := fmul b0 d0'; let ad := fmul a0 d0'; let bc := fmul b0 c0
  let r : C := ⟨fsub ac bd, fadd ad bc⟩
  if r.re.isNaN && r.im.isNaN then
    let zInf := a0.isInf || b0.isInf
    let (a1, b1, c1, d1') : F64 × F64 × F64 × F64 :=
      if zInf then (boxInf a0, boxInf b0, nanToZero c0, nanToZero d0') else (a0, b0, c0, d0')
    let wInf := c1.isInf || d1'.isInf
    let (a2, b2, c2, d2') : F64 × F64 × F64 × F64 :=
      if wInf then (nanToZero a1, nanToZero b1, boxInf c1, boxInf d1') else (a1, b1, c1, d1')
    let recalc0 := zInf || wInf
    let ovf := !recalc0 && (ac.isInf || bd.isInf || ad.isInf || bc.isInf)
    let (a3, b3, c3, d3) : F64 × F64 × F64 × F64 :=
      if ovf then (nanToZero a2, nanToZero b2, nanToZero c2, nanToZero d2') else (a2, b2, c2, d2')
    if recalc0 || ovf then
      ⟨fmul (F64.inf false) (fsub (fmul a3 c3) (fmul b3 d3)),
       fmul (F64.inf false) (fadd (fmul a3 d3) (fmul b3 c3))⟩
    else r
  else r

/-- `_Py_cr_prod`, complexobject.c:150-157. -/
def _Py_cr_prod (a : C) (b : F64) : C := ⟨fmul a.re b, fmul a.im b⟩

/-- `_Py_rc_prod`, complexobject.c:159-163. -/
def _Py_rc_prod (a : F64) (b : C) : C := _Py_cr_prod b a

/-- `b < 0 ? -b : b`. -/
def absLt (b : F64) : F64 := if F64.lt b d0 then b.neg else b

/-- `_Py_c_quot`, complexobject.c:169-246: the quotient and `errno == EDOM`. -/
def _Py_c_quot (a b : C) : C × Bool :=
  let abs_breal := absLt b.re
  let abs_bimag := absLt b.im
  let (r, edom) : C × Bool :=
    if F64.ge abs_breal abs_bimag then
      if F64.eq abs_breal d0 then (⟨d0, d0⟩, true)
      else
        let ratio := fdiv b.im b.re
        let denom := fadd b.re (fmul b.im ratio)
        (⟨fdiv (fadd a.re (fmul a.im ratio)) denom, fdiv (fsub a.im (fmul a.re ratio)) denom⟩, false)
    else if F64.ge abs_bimag abs_breal then
      let ratio := fdiv b.re b.im
      let denom := fadd (fmul b.re ratio) b.im
      (⟨fdiv (fadd (fmul a.re ratio) a.im) denom, fdiv (fsub (fmul a.im ratio) a.re) denom⟩, false)
    else (⟨F64.qnan, F64.qnan⟩, false)
  if r.re.isNaN && r.im.isNaN then
    if (a.re.isInf || a.im.isInf) && b.re.isFinite && b.im.isFinite then
      let x := boxInf a.re
      let y := boxInf a.im
      (⟨fmul (F64.inf false) (fadd (fmul x b.re) (fmul y b.im)),
        fmul (F64.inf false) (fsub (fmul y b.re) (fmul x b.im))⟩, edom)
    else if (abs_breal.isInf || abs_bimag.isInf) && a.re.isFinite && a.im.isFinite then
      let x := boxInf b.re
      let y := boxInf b.im
      (⟨fmul d0 (fadd (fmul a.re x) (fmul a.im y)),
        fmul d0 (fsub (fmul a.im x) (fmul a.re y))⟩, edom)
    else (r, edom)
  else (r, edom)

/-- `_Py_cr_quot`, complexobject.c:248-261. -/
def _Py_cr_quot (a : C) (b : F64) : C × Bool :=
  if !b.isZero then (⟨fdiv a.re b, fdiv a.im b⟩, false) else (⟨d0, d0⟩, true)

/-- `_Py_rc_quot`, complexobject.c:264-304. -/
def _Py_rc_quot (a : F64) (b : C) : C × Bool :=
  let abs_breal := absLt b.re
  let abs_bimag := absLt b.im
  let (r, edom) : C × Bool :=
    if F64.ge abs_breal abs_bimag then
      if F64.eq abs_breal d0 then (⟨d0, d0⟩, true)
      else
        let ratio := fdiv b.im b.re
        let denom := fadd b.re (fmul b.im ratio)
        (⟨fdiv a denom, fdiv (fmul a.neg ratio) denom⟩, false)
    else if F64.ge abs_bimag abs_breal then
      let ratio := fdiv b.re b.im
      let denom := fadd (fmul b.re ratio) b.im
      (⟨fdiv (fmul a ratio) denom, fdiv a.neg denom⟩, false)
    else (⟨F64.qnan, F64.qnan⟩, false)
  if r.re.isNaN && r.im.isNaN && a.isFinite && (abs_breal.isInf || abs_bimag.isInf) then
    let x := boxInf b.re
    let y := boxInf b.im
    (⟨fmul d0 (fmul a x), fmul d0 (fmul a.neg y)⟩, edom)
  else (r, edom)

/-- `errno` after a complex power. -/
inductive PowErrno where
  | none | edom | erange
  deriving DecidableEq, Repr

/-- `_Py_ADJUST_ERANGE2`, pyport.h: an infinite part means `ERANGE`. -/
def adjustErange2 (r : C) (e : PowErrno) : PowErrno :=
  if e == .none && (r.re.isInf || r.im.isInf) then .erange else e

/-- `_Py_c_pow`, complexobject.c:309-339. -/
def _Py_c_pow (m : Libm) (a b : C) : C × PowErrno :=
  if F64.eq b.re d0 && F64.eq b.im d0 then (⟨d1, d0⟩, .none)
  else if F64.eq a.re d0 && F64.eq a.im d0 then
    (⟨d0, d0⟩, if F64.ne b.im d0 || F64.lt b.re d0 then .edom else .none)
  else
    let vabs := m.hypot a.re a.im
    let len0 := m.pow vabs b.re
    let at' := m.atan2 a.im a.re
    let phase0 := fmul at' b.re
    let (len, phase) : F64 × F64 :=
      if F64.ne b.im d0 then
        (fmul len0 (m.exp (fmul at'.neg b.im)), fadd phase0 (fmul b.im (m.log vabs)))
      else (len0, phase0)
    let r : C := ⟨fmul len (m.cos phase), fmul len (m.sin phase)⟩
    (r, adjustErange2 r (if m.trigEdom phase then .edom else .none))

/-- `c_powu`, complexobject.c:341-355: `mask` walks the bits of `n ≤ 100`. -/
def c_powuLoop : Nat → Nat → Nat → C → C → C
  | 0, _, _, r, _ => r
  | fuel + 1, n, mask, r, p =>
    if mask ≤ n then
      let r' := if n &&& mask != 0 then _Py_c_prod r p else r
      c_powuLoop fuel n (mask * 2) r' (_Py_c_prod p p)
    else r

def c_powu (x : C) (n : Nat) : C := c_powuLoop 64 n 1 c_1 x

/-- `c_powi`, complexobject.c:357-365. -/
def c_powi (x : C) (n : Int) : C × Bool :=
  if 0 < n then (c_powu x n.toNat, false)
  else _Py_c_quot c_1 (c_powu x (-n).toNat)

/-- `_Py_c_abs`, complexobject.c:367-397: the value and `errno == ERANGE`. `stale` is that
same test on entry: the NaN path at :389 returns without touching `errno`, and in 3.14.7
nothing clears it first. -/
def _Py_c_abs (m : Libm) (stale : Bool) (z : C) : F64 × Bool :=
  if !z.re.isFinite || !z.im.isFinite then
    if z.re.isInf then (z.re.abs, false)
    else if z.im.isInf then (z.im.abs, false)
    else (F64.qnan, stale)
  else
    let result := m.hypot z.re z.im
    (result, !result.isFinite)

/-! ## Object level -/

/-- `real_to_double`, complexobject.c:644-656. -/
def real_to_double (o : Obj) : Py (Option F64) := convertToDouble o

/-- `real_to_complex`, complexobject.c:658-663. -/
def real_to_complex (o : Obj) : Py (Option C) := do
  let some r ← real_to_double o | return none
  return some ⟨r, d0⟩

/-- What a complex operand can be. -/
inductive CObj where
  | complex (z : C)
  | real (o : Obj)
  deriving Repr

/-- `COMPLEX_BINOP`, complexobject.c:680-716. -/
def complexBinop (cc : C → C → C × Bool) (rc : F64 → C → C × Bool) (cr : C → F64 → C × Bool)
    (v w : CObj) : Py (Option C) :=
  let finish (r : C × Bool) : Py (Option C) :=
    if r.2 then .error (.zeroDivisionError "division by zero") else .ok (some r.1)
  match w, v with
  | .complex b, .complex a => finish (cc a b)
  | .complex b, .real o => do
    let some a ← real_to_double o | return none
    finish (rc a b)
  | .real _, .real _ => .ok none
  | .real o, .complex a => do
    let some b ← real_to_double o | return none
    finish (cr a b)

/-- `complex_add`, complexobject.c:718. -/
def complex_add : CObj → CObj → Py (Option C) :=
  complexBinop (fun a b => (_Py_c_sum a b, false)) (fun a b => (_Py_rc_sum a b, false))
    (fun a b => (_Py_cr_sum a b, false))

/-- `complex_sub`, complexobject.c:720. -/
def complex_sub : CObj → CObj → Py (Option C) :=
  complexBinop (fun a b => (_Py_c_diff a b, false)) (fun a b => (_Py_rc_diff a b, false))
    (fun a b => (_Py_cr_diff a b, false))

/-- `complex_mul`, complexobject.c:719. -/
def complex_mul : CObj → CObj → Py (Option C) :=
  complexBinop (fun a b => (_Py_c_prod a b, false)) (fun a b => (_Py_rc_prod a b, false))
    (fun a b => (_Py_cr_prod a b, false))

/-- `complex_div`, complexobject.c:721. -/
def complex_div : CObj → CObj → Py (Option C) :=
  complexBinop _Py_c_quot _Py_rc_quot _Py_cr_quot

/-- `TO_COMPLEX`, complexobject.c:638-642. -/
def toComplex : CObj → Py (Option C)
  | .complex z => .ok (some z)
  | .real o => real_to_complex o

/-- `complex_pow`, complexobject.c:723-757, after the `z != None` check. -/
def complex_pow (m : Libm) (v w : CObj) : Py (Option C) := do
  let some a ← toComplex v | return none
  let some b ← toComplex w | return none
  let (p, e) : C × PowErrno :=
    if F64.eq b.im d0 && F64.eq b.re (F64.floor b.re) && F64.le b.re.abs (F64.ofInt 100) then
      let (r, edom) := c_powi a b.re.truncInt
      (r, adjustErange2 r (if edom then .edom else .none))
    else _Py_c_pow m a b
  match e with
  | .edom => .error (.zeroDivisionError "zero to a negative or complex power")
  | .erange => .error (.overflowError "complex exponentiation")
  | .none => .ok (some p)

/-- `complex_neg`, complexobject.c:759-767. -/
def complex_neg (z : C) : C := ⟨z.re.neg, z.im.neg⟩

/-- `complex_pos`, complexobject.c:769-777. -/
def complex_pos (z : C) : C := z

/-- `complex_abs`, complexobject.c:779-790. -/
def complex_abs (m : Libm) (stale : Bool) (z : C) : Py F64 :=
  let (r, erange) := _Py_c_abs m stale z
  if erange then .error (.overflowError "absolute value too large") else .ok r

/-- `complex_bool`, complexobject.c:792-797. -/
def complex_bool (z : C) : Bool := F64.ne z.re d0 || F64.ne z.im d0

/-- `complex_conjugate_impl`, complexobject.c:861-868. -/
def complex_conjugate (z : C) : C := ⟨z.re, z.im.neg⟩

/-- `complex___getnewargs___impl`, complexobject.c:875-881. -/
def complex_getnewargs (z : C) : F64 × F64 := (z.re, z.im)

/-- `complex___complex___impl`, complexobject.c:917-927. -/
def complex_complex (z : C) : C := z

/-- `complex_richcompare`, complexobject.c:799-853. `none` is `NotImplemented`. `ne` picks
`Py_NE` over `Py_EQ`; other operators are `NotImplemented`. -/
def complex_richcompare (v : C) (w : CObj) (op : CmpOp) : Option Bool :=
  if op != .eq && op != .ne then none
  else
    let result (equal : Bool) : Bool := equal == (op == .eq)
    match w with
    | .real (.int n) =>
      if F64.eq v.im d0 then float_richcompare v.re (.int n) op
      else some (result false)
    | .real (.float x) | .real (.floatSub _ x) => some (result (F64.eq v.re x && F64.eq v.im d0))
    | .complex j => some (result (F64.eq v.re j.re && F64.eq v.im j.im))
    | .real (.other ..) => none

/-- `complex_hash`, complexobject.c:614-635, for real and imaginary parts that are not
NaNs. `_PyHASH_IMAG` is `1000003`. -/
def complex_hash (z : C) : Option Int :=
  match _Py_HashDouble z.re, _Py_HashDouble z.im with
  | some hr, some hi =>
    let hashreal := hr.toNat + (if hr < 0 then (hr + 2 ^ 64).toNat else 0)
    let hashimag := hi.toNat + (if hi < 0 then (hi + 2 ^ 64).toNat else 0)
    let combined := (hashreal + 1000003 * hashimag) % 2 ^ 64
    some (toSigned64 (if combined = 2 ^ 64 - 1 then 2 ^ 64 - 2 else combined))
  | _, _ => none

/-- `complex_repr`, complexobject.c:557-612. -/
def complex_repr (z : C) : Option (List Nat) :=
  if F64.eq z.re d0 && !z.re.sign then
    (PyOS_double_to_string z.im 114 0 {}).map fun r => render r.1 ++ [106]
  else
    match PyOS_double_to_string z.re 114 0 {}, PyOS_double_to_string z.im 114 0 { sign := true } with
    | some pre, some im => some (40 :: render pre.1 ++ render im.1 ++ [106, 41])
    | _, _ => none

/-- `complex_from_string_inner`, complexobject.c:930-1051: `s` with its length. `none` is
the model's fuel running out. -/
def complex_from_string_inner (s : List Nat) (len : Nat) : Py C :=
  let bad {α} : Py α := .error (.valueError "complex() arg is a malformed string")
  let isJ (c : Nat) : Bool := c == 106 || c == 74
  let sign1 (c : Nat) : Bool := c == 43 || c == 45
  let s0 := scanFrom s isSpace 0
  let (got_bracket, s1) : Bool × Nat :=
    if at_ s s0 == 40 then (true, scanFrom s isSpace (s0 + 1)) else (false, s0)
  match PyOS_string_to_double s s1 true none with
  | none => .error .modelFuel
  | some (zr, end1) =>
    let z : F64 := match zr with | .ok v => v | .error _ => dm1
    let parsed : Py (F64 × F64 × Nat) :=
      if end1 != s1 then
        let s2 := end1
        let c := at_ s s2
        if sign1 c then
          match PyOS_string_to_double s s2 true none with
          | none => .error .modelFuel
          | some (yr, end2) =>
            let (y, s3) : F64 × Nat :=
              if end2 != s2 then ((match yr with | .ok v => v | .error _ => dm1), end2)
              else (if c == 43 then d1 else dm1, s2 + 1)
            if !isJ (at_ s s3) then bad else .ok (z, y, s3 + 1)
        else if isJ c then .ok (d0, z, s2 + 1)
        else .ok (z, d0, s2)
      else
        let c := at_ s s1
        let (y, s2) : F64 × Nat :=
          if sign1 c then (if c == 43 then d1 else dm1, s1 + 1) else (d1, s1)
        if !isJ (at_ s s2) then bad else .ok (d0, y, s2 + 1)
    match parsed with
    | .error e => .error e
    | .ok (x, y, s3) =>
      let s4 := scanFrom s isSpace s3
      let s5 : Option Nat :=
        if got_bracket then
          if at_ s s4 != 41 then none else some (scanFrom s isSpace (s4 + 1))
        else some s4
      match s5 with
      | none => bad
      | some e => if e != len then bad else .ok ⟨x, y⟩

/-- `complex_subtype_from_string`, complexobject.c:1053-1081, for a `str`. -/
def complex_subtype_from_string (cps : List Nat) : Py C :=
  _Py_string_to_number_with_underscores (transformDecimalAndSpace cps) "complex"
    complex_from_string_inner

end PyLean.Binary64
