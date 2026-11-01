import PyLean.Binary64.Bigint
import PyLean.Binary64.Float

/-!
`_Py_dg_strtod` and `bigcomp` from `Python/dtoa.c`, CPython 3.14.7. Every line
that touches a `double` goes through the exact `F64` operations, so the fast path,
the scaled starting approximation and the correction loop all run as written.
The `goto`s become a small exit type.
-/

namespace PyLean.Binary64

/-- `tens[i]`, dtoa.c:1103-1108: exact for `i ≤ 22`. -/
def tens (i : Nat) : F64 := F64.ofInt (10 ^ i)

/-- `bigtens`, dtoa.c:1110-1111. -/
def bigtens (j : Nat) : F64 := F64.ofInt (10 ^ (16 * 2 ^ j))

/-- `tinytens`, dtoa.c:1112-1115. -/
def tinytens (j : Nat) : F64 :=
  if j < 4 then F64.ofRat (mkRat 1 (10 ^ (16 * 2 ^ j)))
  else F64.mul (F64.ofInt (2 ^ 53)) (F64.ofRat (mkRat (2 ^ 53) (10 ^ 256)))

def STRTOD_DIGLIM : Nat := 40
def MAX_ABS_EXP : Nat := 1100000000
def MAX_DIGITS : Nat := 1000000000
def Big0 : Nat := Frac_mask ||| Exp_msk1 * (1024 + Bias - 1)
def Big1 : Nat := 0xffffffff

/-- How `_Py_dg_strtod` leaves the parser. `se` is `*se`. -/
structure Parsed where
  sign : Bool
  /-- `s0`: index of the first significant digit. -/
  s0 : Nat
  nd : Nat
  nd0 : Int
  e : Int
  se : Nat
  deriving DecidableEq, Repr

/-- The exponent digits, with `abs_exp` wrapping in 32 bits, dtoa.c:1492-1496. -/
def expDigits (s : List Nat) (i stop : Nat) : Nat :=
  (List.range (stop - i)).foldl (fun acc k => (10 * acc + (at_ s (i + k) - 48)) % 2 ^ 32) 0

/-- The parsing half of `_Py_dg_strtod`, dtoa.c:1402-1520. `none` is `parse_error`,
which also sets `*se = s00`. -/
def strtodParse (s : List Nat) (s00 : Nat) : Option Parsed := do
  let c0 := at_ s s00
  let (sign, p0) : Bool × Nat :=
    if c0 == 45 then (true, s00 + 1) else if c0 == 43 then (false, s00 + 1) else (false, s00)
  let isZ : Nat → Bool := (· == 48)
  let p1 := scanFrom s isZ p0
  let lz0 : Bool := p1 != p0
  let s0a := p1
  let p2 := scanFrom s isDigit p1
  let ndigits0 := p2 - p1
  let (p3, s0, lz, ndigits, fraclen) : Nat × Nat × Bool × Nat × Nat :=
    if at_ s p2 == 46 then
      let q0 := p2 + 1
      let (q1, s0b, lz1, fl0) : Nat × Nat × Bool × Nat :=
        if ndigits0 == 0 then
          let t := scanFrom s isZ q0
          (t, t, lz0 || t != q0, t - q0)
        else (q0, s0a, lz0, 0)
      let q2 := scanFrom s isDigit q1
      (q2, s0b, lz1, ndigits0 + (q2 - q1), fl0 + (q2 - q1))
    else (p2, s0a, lz0, ndigits0, 0)
  if ndigits == 0 && !lz then none
  else if MAX_DIGITS < ndigits || MAX_DIGITS < fraclen then none
  else
    let nd := ndigits
    let nd0 : Int := (ndigits : Int) - fraclen
    let c := at_ s p3
    let (e0, se) : Int × Nat :=
      if c == 101 || c == 69 then
        let s00' := p3
        let c1 := at_ s (p3 + 1)
        let (esign, q0) : Bool × Nat :=
          if c1 == 45 then (true, p3 + 2) else if c1 == 43 then (false, p3 + 2) else (false, p3 + 1)
        let q1 := scanFrom s isZ q0
        let lz' : Bool := q1 != q0
        let q2 := scanFrom s isDigit q1
        let abs_exp := expDigits s q1 q2
        let e1 : Int := if 9 < q2 - q1 || MAX_ABS_EXP < abs_exp then MAX_ABS_EXP else abs_exp
        let e2 := if esign then -e1 else e1
        (e2, if q2 == q1 && !lz' then s00' else q2)
      else (0, p3)
    let e1 := e0 - ((nd : Int) - nd0)
    let nd0' : Int := if nd0 ≤ 0 then nd else nd0
    some { sign, s0, nd, nd0 := nd0', e := e1, se }

/-- Significant digit `i` as a character: `s0[i < nd0 ? i : i+1]`. -/
def sigChar (s : List Nat) (s0 : Nat) (nd0 : Int) (i : Nat) : Nat :=
  at_ s (s0 + if (i : Int) < nd0 then i else i + 1)

/-- Significant digit `i` as a number. -/
def sigDig (s : List Nat) (s0 : Nat) (nd0 : Int) (i : Nat) : Nat :=
  sigChar s s0 nd0 i - 48

/-- `for (i = n; i > 0; ) { --i; if (dig != '0') { ++i; break; } }`, dtoa.c:1526-1532
and :1704-1712. -/
def stripZeros (s : List Nat) (s0 : Nat) (nd0 : Int) : Nat → Nat
  | 0 => 0
  | i + 1 => if sigChar s s0 nd0 i != 48 then i + 1 else stripZeros s s0 nd0 i

/-- The exits of `_Py_dg_strtod` other than a normal return. -/
inductive StrtodExit where
  | ret (rv : F64)
  | undfl
  | ovfl
  deriving DecidableEq, Repr

/-- `rv * 10 ** e1` for `e1 > 0`, dtoa.c:1622-1647. -/
def scaleUp (rv0 : F64) (e1 : Nat) : Except StrtodExit F64 := do
  let i := e1 &&& 15
  let rv1 := if i != 0 then F64.mul rv0 (tens i) else rv0
  let e2 := e1 - i
  if e2 == 0 then return rv1
  if 308 < e2 then throw .ovfl
  let go (e j : Nat) (rv : F64) : Nat × Nat × F64 :=
    (List.range 8).foldl (fun (st : Nat × Nat × F64) _ =>
      let (e, j, rv) := st
      if 1 < e then (e / 2, j + 1, if e &&& 1 != 0 then F64.mul rv (bigtens j) else rv)
      else st) (e, j, rv)
  let (_, j, rv2) := go (e2 / 16) 0 rv1
  let rv3 := setWord0 rv2 (word0 rv2 + 2 ^ 32 - P * Exp_msk1)
  let rv4 := F64.mul rv3 (bigtens j)
  let z := word0 rv4 &&& Exp_mask
  if Exp_msk1 * (1024 + Bias - P) < z then throw .ovfl
  if Exp_msk1 * (1024 + Bias - 1 - P) < z then return mkWords Big0 Big1
  return setWord0 rv4 (word0 rv4 + P * Exp_msk1)

/-- `rv * 10 ** -e1` for `e1 > 0`, dtoa.c:1659-1685: the result and `bc.scale`. -/
def scaleDown (rv0 : F64) (e0 : Nat) : Except StrtodExit (F64 × Nat) := do
  let i := e0 &&& 15
  let rv1 := if i != 0 then F64.div rv0 (tens i) else rv0
  let e1 := e0 / 16
  if e1 == 0 then return (rv1, 0)
  if 32 ≤ e1 then throw .undfl
  let scale := if e1 &&& 16 != 0 then 2 * P else 0
  let rv2 := (List.range 5).foldl
    (fun rv j => if (e1 / 2 ^ j) &&& 1 != 0 then F64.mul rv (tinytens j) else rv) rv1
  let exf := (word0 rv2 &&& Exp_mask) / 2 ^ Exp_shift
  let rv3 :=
    if scale != 0 && decide (exf < 2 * P + 1) then
      let j := 2 * P + 1 - exf
      if 32 ≤ j then
        let r := setWord1 rv2 0
        if 53 ≤ j then setWord0 r ((P + 2) * Exp_msk1)
        else setWord0 r (word0 r &&& ((0xffffffff * 2 ^ (j - 32)) % 2 ^ 32))
      else setWord1 rv2 (word1 rv2 &&& ((0xffffffff * 2 ^ j) % 2 ^ 32))
    else rv2
  if rv3.isZero then throw .undfl
  return (rv3, scale)

/-- One pass of the digit comparison in `bigcomp`, dtoa.c:1354-1375. -/
def bigcompLoop (dig : Nat → Nat) (nd : Nat) (d : Bigint) : Nat → Nat → Bigint → Int
  | 0, _, _ => -1
  | fuel + 1, i, b0 =>
    let b := multadd b0 10 0
    let (q, b1) := quorem b d
    let dd : Int := (dig i : Int) - q
    let i' := i + 1
    if dd != 0 then dd
    else if b1.isZero then (if i' < nd then 1 else 0)
    else if !(decide (i' < nd)) then -1
    else bigcompLoop dig nd d fuel i' b1

/-- The last step of `bigcomp`, dtoa.c:1379-1380. -/
def bigcompRound (rv : F64) (scale : Nat) (dd : Int) (odd : Bool) : F64 :=
  if 0 < dd || (dd == 0 && odd) then F64.add rv (sulp rv scale) else rv

/-- `bigcomp`, dtoa.c:1274-1382. -/
def bigcomp (rv : F64) (dig : Nat → Nat) (bc : BCinfo) : F64 :=
  let nd := bc.nd
  let p5 : Int := (nd : Int) + bc.e0
  let (b0, p20) := sd2b rv bc.scale
  let odd := b0.x0 % 2 == 1
  let b1 := lshift b0 1
  let b2 : Bigint := { b1 with x := match b1.x with | [] => [1] | d :: ds => (d ||| 1) :: ds }
  let p2 := p20 - 1 - p5
  let d0' := i2b 1
  let (d1, b3) : Bigint × Bigint :=
    if 0 < p5 then (pow5mult d0' p5.toNat, b2)
    else if p5 < 0 then (d0', pow5mult b2 (-p5).toNat)
    else (d0', b2)
  let (bb2, dd2) : Int × Int := if 0 < p2 then (p2, 0) else (0, -p2)
  let i := dshift d1 dd2
  let bb2' := bb2 + i
  let dd2' := dd2 + i
  let b4 := if 0 < bb2' then lshift b3 bb2'.toNat else b3
  let d2' := if 0 < dd2' then lshift d1 dd2'.toNat else d1
  let dd : Int :=
    if 0 ≤ cmp b4 d2' then -1
    else bigcompLoop dig nd d2' (nd + 2) 0 b4
  bigcompRound rv bc.scale dd odd

/-- What one pass of the correction loop decides. -/
inductive Step where
  | cont (rv : F64) (bcnd : Nat)
  | brk (rv : F64) (bcnd : Nat)
  | exit (e : StrtodExit)
  deriving DecidableEq, Repr

/-- `y` in `bc.scale && y <= 2*P*Exp_msk1 ? ... : 0xffffffff`, dtoa.c:1926-1930. -/
def word1Top (rv : F64) (scale : Nat) : Nat :=
  let y := word0 rv &&& Exp_mask
  if scale != 0 && decide (y ≤ 2 * P * Exp_msk1) then
    0xffffffff &&& ((0xffffffff * 2 ^ (2 * P + 1 - y / 2 ^ Exp_shift)) % 2 ^ 32)
  else 0xffffffff

/-- `drop_down:`, dtoa.c:1941-1959. -/
def dropDown (rv : F64) (scale nd bcnd : Nat) : Step :=
  let L := word0 rv &&& Exp_mask
  if scale != 0 && decide (L ≤ (2 * P + 1) * Exp_msk1) then
    if (P + 2) * Exp_msk1 < L then .brk rv bcnd
    else if nd < bcnd then .brk rv bcnd
    else .exit .undfl
  else
    let L' := L + 2 ^ 32 - Exp_msk1
    .brk (mkWords ((L' % 2 ^ 32) ||| Bndry_mask) 0xffffffff) bcnd

/-- The adjustment after `ratio`, dtoa.c:1976-2061. -/
def adjustStep (rv : F64) (scale nd bcnd : Nat) (dsign : Bool) (delta bs : Bigint) : Step :=
  let aadj0 := ratio delta bs
  let adjust (aadj aadj1 : F64) : Step :=
    let y := word0 rv &&& Exp_mask
    let finishUp (rv' : F64) (y : Nat) (aadj : F64) : Step :=
      let z := word0 rv' &&& Exp_mask
      if bcnd == nd && scale == 0 && y == z then
        let L := aadj.truncInt
        let a := F64.sub aadj (F64.ofInt L)
        if dsign || word1 rv' != 0 || (word0 rv' &&& Bndry_mask) != 0 then
          if F64.lt a (F64.ofRat (mkRat 4999999 10000000)) ||
              F64.gt a (F64.ofRat (mkRat 5000001 10000000)) then .brk rv' bcnd
          else .cont rv' bcnd
        else if F64.lt a (F64.div (F64.ofRat (mkRat 4999999 10000000)) d2) then .brk rv' bcnd
        else .cont rv' bcnd
      else .cont rv' bcnd
    if y == Exp_msk1 * (1024 + Bias - 1) then
      let rv0 := rv
      let rv1 := setWord0 rv (word0 rv + 2 ^ 32 - P * Exp_msk1)
      let adj := F64.mul aadj1 (ulpD rv1)
      let rv2 := F64.add rv1 adj
      if Exp_msk1 * (1024 + Bias - P) ≤ (word0 rv2 &&& Exp_mask) then
        if word0 rv0 == Big0 && word1 rv0 == Big1 then .exit .ovfl
        else .cont (mkWords Big0 Big1) bcnd
      else finishUp (setWord0 rv2 (word0 rv2 + P * Exp_msk1)) y aadj
    else
      let (aadj', aadj1') : F64 × F64 :=
        if scale != 0 && decide (y ≤ 2 * P * Exp_msk1) then
          let (a2, a12) : F64 × F64 :=
            if F64.le aadj (F64.ofInt 0x7fffffff) then
              let z0 := (aadj.truncInt).toNat
              let z := if z0 ≤ 0 then 1 else z0
              let a := F64.ofInt z
              (a, if dsign then a else a.neg)
            else (aadj, aadj1)
          let a3 := setWord0 a12 (word0 a12 + (2 * P + 1) * Exp_msk1 + 2 ^ 32 - y)
          (a2, a3)
        else (aadj, aadj1)
      let adj := F64.mul aadj1' (ulpD rv)
      finishUp (F64.add rv adj) y aadj'
  if F64.le aadj0 d2 then
    if dsign then adjust d1 d1
    else if word1 rv != 0 || (word0 rv &&& Bndry_mask) != 0 then
      if word1 rv == 1 && word0 rv == 0 then
        if nd < bcnd then .brk rv bcnd else .exit .undfl
      else adjust d1 dm1
    else
      let a := if F64.lt aadj0 d1 then dHalf else F64.mul aadj0 dHalf
      adjust a a.neg
  else
    let a := F64.mul aadj0 dHalf
    adjust a (if dsign then a else a.neg)

/-- One pass of the correction loop, dtoa.c:1742-2061. -/
def strtodStep (bd0 : Bigint) (e : Int) (nd scale bcnd : Nat) (rv : F64) : Step :=
  let (bb0, bbe) := sd2b rv scale
  let odd := bb0.x0 % 2 == 1
  let (bb2a, bb5, bd2a, bd5) : Int × Nat × Int × Nat :=
    if 0 ≤ e then (0, 0, e, e.toNat) else (-e, (-e).toNat, 0, 0)
  let (bb2b, bd2b) : Int × Int := if 0 ≤ bbe then (bb2a + bbe, bd2a) else (bb2a, bd2a - bbe)
  let bs2a := bb2b
  let bb2c := bb2b + 1
  let bd2c := bd2b + 1
  let i0 := min (min bb2c bd2c) bs2a
  let (bb2, bd2, bs2) : Int × Int × Int :=
    if 0 < i0 then (bb2c - i0, bd2c - i0, bs2a - i0) else (bb2c, bd2c, bs2a)
  let bs1 := if 0 < bb5 then pow5mult (i2b 1) bb5 else i2b 1
  let bb1 := if 0 < bb5 then mult bs1 bb0 else bb0
  let bb := if 0 < bb2 then lshift bb1 bb2.toNat else bb1
  let bd1 := if 0 < bd5 then pow5mult bd0 bd5 else bd0
  let bd := if 0 < bd2 then lshift bd1 bd2.toNat else bd1
  let bs := if 0 < bs2 then lshift bs1 bs2.toNat else bs1
  let delta0 := diff bb bd
  let dsign := delta0.sign
  let delta : Bigint := { delta0 with sign := false }
  let i1 := cmp delta bs
  -- dtoa.c:1868-1899
  let early : Step ⊕ (Int × Nat) :=
    if nd < bcnd && i1 ≤ 0 then
      if dsign then .inl (.brk rv bcnd)
      else if word1 rv == 0 && (word0 rv &&& Bndry_mask) == 0 then
        let j := (word0 rv &&& Exp_mask) / 2 ^ Exp_shift
        if 2 ≤ (j : Int) - scale then
          .inl (.brk (F64.sub rv (F64.mul dHalf (sulp rv scale))) bcnd)
        else .inr (-1, nd)
      else .inr (-1, nd)
    else .inr (i1, bcnd)
  match early with
  | .inl st => st
  | .inr (i, bcnd) =>
    if i < 0 then
      if dsign || word1 rv != 0 || (word0 rv &&& Bndry_mask) != 0
          || decide ((word0 rv &&& Exp_mask) ≤ (2 * P + 1) * Exp_msk1) then .brk rv bcnd
      else if delta.x0 == 0 && delta.wds ≤ 1 then .brk rv bcnd
      else
        let delta' := lshift delta 1
        if 0 < cmp delta' bs then dropDown rv scale nd bcnd else .brk rv bcnd
    else if i == 0 then
      let afterBoundary : Step :=
        if !odd then .brk rv bcnd
        else if dsign then .brk (F64.add rv (sulp rv scale)) bcnd
        else
          let r := F64.sub rv (sulp rv scale)
          if r.isZero then
            if nd < bcnd then .brk r bcnd else .exit .undfl
          else .brk r bcnd
      if dsign then
        if (word0 rv &&& Bndry_mask) == Bndry_mask && word1 rv == word1Top rv scale then
          .brk (mkWords ((word0 rv &&& Exp_mask) + Exp_msk1) 0) bcnd
        else afterBoundary
      else if (word0 rv &&& Bndry_mask) == 0 && word1 rv == 0 then
        dropDown rv scale nd bcnd
      else afterBoundary
    else adjustStep rv scale nd bcnd dsign delta bs

/-- The `for(;;)`. -/
def strtodLoop (bd0 : Bigint) (e : Int) (nd scale : Nat) : Nat → Nat → F64 → Step
  | 0, bcnd, rv => .cont rv bcnd
  | fuel + 1, bcnd, rv =>
    match strtodStep bd0 e nd scale bcnd rv with
    | .cont rv' bcnd' => strtodLoop bd0 e nd scale fuel bcnd' rv'
    | st => st

/-- The first 16 digits, dtoa.c:1576-1583: `y` from digits below 9, `z` from the
next seven. -/
def firstDigits (dig : Nat → Nat) (nd : Nat) : Nat × Nat :=
  let n := min nd 16
  (List.range n).foldl (fun (st : Nat × Nat) i =>
    if i < 9 then (10 * st.1 + dig i, st.2) else (st.1, 10 * st.2 + dig i)) (0, 0)

/-- The Clinger fast path, dtoa.c:1590-1615: `some rv` when it applies. -/
def strtodFast (rv : F64) (nd : Nat) (e : Int) : Option F64 :=
  if nd ≤ 15 then
    if e == 0 then some rv
    else if 0 < e then
      if e ≤ 22 then some (F64.mul rv (tens e.toNat))
      else
        let i := 15 - nd
        if e ≤ 22 + (i : Int) then
          some (F64.mul (F64.mul rv (tens i)) (tens (e - i).toNat))
        else none
    else if -22 ≤ e then some (F64.div rv (tens (-e).toNat))
    else none
  else none

/-- `_Py_dg_strtod`, the numeric half, dtoa.c:1522-2074, before the sign goes on at
`ret:`, `undfl:` and `ovfl:`: `(|value|, errno == ERANGE)`. `none` means the model's
loop fuel ran out. -/
def strtodAbs (s : List Nat) (p : Parsed) : Option (F64 × Bool) :=
  if p.nd == 0 then some (d0, false)
  else
    let i0 := stripZeros s p.s0 p.nd0 p.nd
    let e := p.e + ((p.nd : Int) - i0)
    let nd := i0
    let nd0 : Int := if (nd : Int) < p.nd0 then nd else p.nd0
    let dig := sigDig s p.s0 nd0
    let (y, z) := firstDigits dig nd
    let k := min nd 16
    let rv0 := F64.ofInt y
    let rv1 := if 9 < k then F64.add (F64.mul (tens (k - 9)) rv0) (F64.ofInt z) else rv0
    match strtodFast rv1 nd e with
    | some r => some (r, false)
    | none =>
      let e1 : Int := e + ((nd : Int) - k)
      let scaled : Except StrtodExit (F64 × Nat) :=
        if 0 < e1 then do return (← scaleUp rv1 e1.toNat, 0)
        else if e1 < 0 then scaleDown rv1 (-e1).toNat
        else .ok (rv1, 0)
      match scaled with
      | .error .ovfl => some (F64.inf false, true)
      | .error .undfl => some (d0, false)
      | .error (.ret r) => some (r, false)
      | .ok (rv2, scale) =>
        let bcnd0 := nd
        -- truncate to 18 digits for very long inputs, dtoa.c:1696-1724
        let (ndT, nd0T, eT, yT) : Nat × Int × Int × Nat :=
          if STRTOD_DIGLIM < nd then
            let it := stripZeros s p.s0 nd0 18
            let ndT := it
            let nd0T : Int := if (ndT : Int) < nd0 then ndT else nd0
            let eT := e + ((nd : Int) - it)
            let yT := if ndT < 9 then
                (List.range ndT).foldl (fun acc i => 10 * acc + sigDig s p.s0 nd0T i) 0
              else y
            (ndT, nd0T, eT, yT)
          else (nd, nd0, e, y)
        let digT := sigDig s p.s0 nd0T
        let bd0 := s2b digT ndT yT
        match strtodLoop bd0 eT ndT scale 64 bcnd0 rv2 with
        | .cont .. => none
        | .exit .ovfl => some (F64.inf false, true)
        | .exit .undfl => some (d0, false)
        | .exit (.ret r) => some (r, false)
        | .brk rv3 bcnd =>
          let rv4 :=
            if ndT < bcnd then
              bigcomp rv3 dig { e0 := e, nd := bcnd, nd0 := nd0.toNat, scale }
            else rv3
          let rv5 :=
            if scale != 0 then F64.mul rv4 (mkWords (Exp_1 - 2 * P * Exp_msk1) 0) else rv4
          some (rv5, false)

/-- The sign goes on last, dtoa.c:2076, :2089 and :2097. -/
def strtodValue (s : List Nat) (p : Parsed) : Option (F64 × Bool) :=
  (strtodAbs s p).map fun r => (if p.sign then r.1.neg else r.1, r.2)

/-- `_Py_dg_strtod`, dtoa.c:1385-2108: value, `*se`, and whether `errno` is
`ERANGE`. `none` means the model's fuel ran out. -/
def _Py_dg_strtod (s : List Nat) (s00 : Nat) : Option (F64 × Nat × Bool) :=
  match strtodParse s s00 with
  | none => some (d0, s00, false)
  | some p =>
    match strtodValue s p with
    | none => none
    | some (v, er) => some (v, p.se, er)

end PyLean.Binary64
