import PyLean.Binary64.Strtod

/-!
`_Py_dg_dtoa` from `Python/dtoa.c`, and on top of it everything in
`Python/pystrtod.c` and `Objects/floatobject.c` that goes through decimal strings:
`format_float_short`, `PyOS_double_to_string`, `repr`, `round(x, n)`, and the
`float(str)` path.

CPython only ever calls `_Py_dg_dtoa` with mode 0, 2 or 3 (`format_float_short` and
`double_round`), so `leftright` is true exactly in mode 0, where `ilim == -1` keeps
the floating-point quick path out. Its `leftright` branch at dtoa.c:2441-2459 and
the bookkeeping for modes 1, 4, 5 and above are therefore not modelled.

Precisions stay `int`-sized `Int`s, and C `int` overflow is modelled with `wrap32`,
which is what the x86-64 build does at the two places below that overflow.
-/

namespace PyLean.Binary64

open PyLean

/-- Two's complement `int` arithmetic. -/
def wrap32 (n : Int) : Int := ((n + 2 ^ 31) % 2 ^ 32) - 2 ^ 31

def Ten_pmax : Int := 22
def Quick_max : Int := 14
def Int_max : Int := 14
def Bletch : Nat := 0x10

/-- What `_Py_dg_dtoa` hands back. `digits` are ASCII codes. -/
structure DtoaOut where
  digits : List Nat
  decpt : Int
  sign : Bool
  deriving DecidableEq, Repr

/-- `bump_up` (dtoa.c:2508-2516) and `roundoff` (:2763-2770) on the reversed buffer:
pop nines, increment the digit below them, and when every digit was a nine, leave
a `1` and raise `k`. -/
def bumpUp : List Nat → Int → List Nat × Int
  | [], k => ([49], k + 1)
  | d :: ds, k =>
    if d == 57 then
      match ds with
      | [] => ([49], k + 1)
      | _ => bumpUp ds k
    else ((d + 1) :: ds, k)

/-- `while(*--s == '0'); s++;` on the reversed buffer. -/
def stripTrailingZeros (s : List Nat) : List Nat := s.dropWhile (· == 48)

/-- The scaling of `u` in the quick path, dtoa.c:2398-2421: `(u, ieps)`. -/
def quickScale (u : F64) (k : Int) : F64 × Nat :=
  if 0 < k then
    let k' := k.toNat
    let ds0 := tens (k' &&& 0xf)
    let j0 := k' / 16
    let (u1, j1, ieps0) : F64 × Nat × Nat :=
      if j0 &&& Bletch != 0 then (F64.div u (bigtens 4), j0 &&& (Bletch - 1), 3) else (u, j0, 2)
    let (ds, ieps) := (List.range 5).foldl (fun (st : F64 × Nat) i =>
      if (j1 / 2 ^ i) &&& 1 != 0 then (F64.mul st.1 (bigtens i), st.2 + 1) else st) (ds0, ieps0)
    (F64.div u1 ds, ieps)
  else if k != 0 then
    let j1 := (-k).toNat
    let u1 := F64.mul u (tens (j1 &&& 0xf))
    (List.range 5).foldl (fun (st : F64 × Nat) i =>
      if ((j1 / 16) / 2 ^ i) &&& 1 != 0 then (F64.mul st.1 (bigtens i), st.2 + 1) else st) (u1, 2)
  else (u, 2)

/-- The "generate `ilim` digits, then fix them up" loop, dtoa.c:2462-2478. -/
def quickDigits (eps : F64) : Nat → Int → Nat → F64 → List Nat → Int → Option (List Nat × Int)
  | 0, _, _, _, _, _ => none
  | fuel + 1, ilim0, i, u, s, k =>
    let L := u.truncInt
    let u1 := F64.sub u (F64.ofInt L)
    let ilim := if u1.isZero then (i : Int) else ilim0
    let s' := (48 + L.toNat) :: s
    if (i : Int) == ilim then
      if F64.gt u1 (F64.add dHalf eps) then some (bumpUp s' k)
      else if F64.lt u1 (F64.sub dHalf eps) then some (stripTrailingZeros s', k)
      else none
    else quickDigits eps fuel ilim (i + 1) (F64.mul u1 (F64.ofInt 10)) s' k

/-- The floating-point quick path, dtoa.c:2389-2485, for `leftright == 0`. `none`
is `fast_failed`. Otherwise the reversed digits and `k`, as at `ret1`, `ret` after
`no_digits`, or `ret` after `one_digit`. -/
def dtoaQuick (u0 : F64) (k0 ilim0 ilim1 ndigits : Int) (k_check : Bool) :
    Option (List Nat × Int) :=
  let (u1, ieps1) := quickScale u0 k0
  let adj : Option (F64 × Nat × Int × Int) :=
    if k_check && F64.lt u1 d1 && decide (0 < ilim0) then
      if ilim1 ≤ 0 then none
      else some (F64.mul u1 (F64.ofInt 10), ieps1 + 1, ilim1, k0 - 1)
    else some (u1, ieps1, ilim0, k0)
  match adj with
  | none => none
  | some (u2, ieps, ilim, k) =>
    let eps0 := F64.add (F64.mul (F64.ofInt ieps) u2) (F64.ofInt 7)
    let eps1 := setWord0 eps0 (word0 eps0 + 2 ^ 32 - (P - 1) * Exp_msk1)
    if ilim == 0 then
      let u3 := F64.sub u2 (F64.ofInt 5)
      if F64.gt u3 eps1 then some ([49], k + 1)
      else if F64.lt u3 eps1.neg then some ([], -1 - ndigits)
      else none
    else
      let eps2 := F64.mul eps1 (tens (ilim - 1).toNat)
      quickDigits eps2 (ilim.toNat + 1) ilim 1 u2 [] k

/-- The "small integer" digit loop, dtoa.c:2498-2527. -/
def smallIntDigits (ds : F64) (ilim : Int) : Nat → Nat → F64 → List Nat → Int → List Nat × Int
  | 0, _, _, s, k => (s, k)
  | fuel + 1, i, u, s, k =>
    let L := (F64.div u ds).truncInt
    let u1 := F64.sub u (F64.mul (F64.ofInt L) ds)
    let s' := (48 + L.toNat) :: s
    if u1.isZero then (s', k)
    else if (i : Int) == ilim then
      let u2 := F64.add u1 u1
      if F64.gt u2 ds || (F64.eq u2 ds && L % 2 == 1) then bumpUp s' k
      else (s'.dropWhile (· == 48), k)
    else smallIntDigits ds ilim fuel (i + 1) (F64.mul u1 (F64.ofInt 10)) s' k

/-- The non-`leftright` digit loop and the final round-off, dtoa.c:2744-2775. -/
def fixedDigits (S : Bigint) (ilim : Int) : Nat → Nat → Bigint → List Nat → Int → Option (List Nat × Int)
  | 0, _, _, _, _ => none
  | fuel + 1, i, b, s, k =>
    let (q, b1) := quorem b S
    let dig := q + 48
    let s' := dig :: s
    if b1.isZero then some (s', k)
    else if ilim ≤ (i : Int) then
      let b2 := lshift b1 1
      let j := cmp b2 S
      if 0 < j || (j == 0 && dig % 2 == 1) then some (bumpUp s' k)
      else some (stripTrailingZeros s', k)
    else fixedDigits S ilim fuel (i + 1) (multadd b1 10 0) s' k

/-- The shortest-digits loop, dtoa.c:2674-2741, for mode 0. `even` is
`!(word1(&u) & 1)`. -/
def shortestDigits (S : Bigint) (even : Bool) :
    Nat → Bigint → Bigint → Bigint → List Nat → Int → Option (List Nat × Int)
  | 0, _, _, _, _, _ => none
  | fuel + 1, b0, mlo, mhi, s, k =>
    let (q, b) := quorem b0 S
    let dig := q + 48
    let j := cmp b mlo
    let delta := diff S mhi
    let j1 := if delta.sign then 1 else cmp b delta
    let round9 (s : List Nat) : Option (List Nat × Int) := some (bumpUp (57 :: s) k)
    if j1 == 0 && even then
      if dig == 57 then round9 s
      else some ((if 0 < j then dig + 1 else dig) :: s, k)
    else if j < 0 || (j == 0 && even) then
      if b.isZero then some (dig :: s, k)
      else if 0 < j1 then
        let b' := lshift b 1
        let j2 := cmp b' S
        if 0 < j2 || (j2 == 0 && dig % 2 == 1) then
          if dig == 57 then round9 s else some ((dig + 1) :: s, k)
        else some (dig :: s, k)
      else some (dig :: s, k)
    else if 0 < j1 then
      if dig == 57 then round9 s else some ((dig + 1) :: s, k)
    else
      shortestDigits S even fuel (multadd b 10 0) (multadd mlo 10 0) (multadd mhi 10 0)
        (dig :: s) k

/-- The multiple-precision path, dtoa.c:2531-2775. -/
def dtoaBig (u : F64) (mode : Nat) (b0 : Bigint) (be : Int) (bbits : Nat) (denorm k_check : Bool)
    (b20 s20 : Int) (b5 s5 : Nat) (k0 ilim0 ilim1 ndigits : Int) : Option (List Nat × Int) :=
  let leftright := mode == 0
  let m20 := b20
  let m5 := b5
  let i0 : Int := if denorm then be + ((Bias : Int) + (P - 1) - 1 + 1) else 1 + (P : Int) - bbits
  let (b21, s21, mhi0) : Int × Int × Bigint :=
    if leftright then (b20 + i0, s20 + i0, i2b 1) else (b20, s20, i2b 1)
  let (b22, m21, s22) : Int × Int × Int :=
    if 0 < m20 && 0 < s21 then
      let i := min m20 s21
      (b21 - i, m20 - i, s21 - i)
    else (b21, m20, s21)
  let (b1, mhi1) : Bigint × Bigint :=
    if 0 < b5 then
      if leftright then
        let (b', mhi') : Bigint × Bigint :=
          if 0 < m5 then
            let mhi' := pow5mult mhi0 m5
            (mult mhi' b0, mhi')
          else (b0, mhi0)
        let j := b5 - m5
        (if j != 0 then pow5mult b' j else b', mhi')
      else (pow5mult b0 b5, mhi0)
    else (b0, mhi0)
  let S0 := if 0 < s5 then pow5mult (i2b 1) s5 else i2b 1
  let spec_case : Bool :=
    leftright && word1 u == 0 && (word0 u &&& Bndry_mask) == 0
      && (word0 u &&& (Exp_mask &&& 0xffefffff)) != 0
  let (b23, s23) : Int × Int := if spec_case then (b22 + 1, s22 + 1) else (b22, s22)
  let i := dshift S0 s23
  let b24 := b23 + i
  let m22 := m21 + i
  let s24 := s23 + i
  let b2 := if 0 < b24 then lshift b1 b24.toNat else b1
  let S1 := if 0 < s24 then lshift S0 s24.toNat else S0
  let (b3, mhi2, k, ilim) : Bigint × Bigint × Int × Int :=
    if k_check && decide (cmp b2 S1 < 0) then
      (multadd b2 10 0, (if leftright then multadd mhi1 10 0 else mhi1), k0 - 1, ilim1)
    else (b2, mhi1, k0, ilim0)
  let fcvtZero : Option (Option (List Nat × Int)) :=
    if ilim ≤ 0 && mode == 3 then
      if ilim < 0 then some (some ([], -1 - ndigits))
      else
        let S2 := multadd S1 5 0
        if cmp b3 S2 ≤ 0 then some (some ([], -1 - ndigits))
        else some (some ([49], k + 1))
    else none
  match fcvtZero with
  | some r => r
  | none =>
    if leftright then
      let mhi3 := if 0 < m22 then lshift mhi2 m22.toNat else mhi2
      let mlo := mhi3
      let mhi4 := if spec_case then lshift mhi3 1 else mhi3
      shortestDigits S1 (word1 u % 2 == 0) 40 b3 mlo mhi4 [] k
    else fixedDigits S1 ilim 1300 1 b3 [] k

/-- `_Py_dg_dtoa`, dtoa.c:2194-2802, for modes 0, 2 and 3. `none` means the model's
fuel ran out. -/
def _Py_dg_dtoa (dd : F64) (mode : Nat) (ndigits0 : Int) : Option DtoaOut :=
  let sign := word0 dd &&& Sign_bit != 0
  let u := if sign then setWord0 dd (word0 dd - Sign_bit) else dd
  if (word0 u &&& Exp_mask) == Exp_mask then
    let isInfBits := word1 u == 0 && (word0 u &&& 0xfffff) == 0
    some { digits := if isInfBits then [73, 110, 102, 105, 110, 105, 116, 121] else [78, 97, 78]
           decpt := 9999, sign }
  else if u.isZero then some { digits := [48], decpt := 1, sign }
  else
    let (b, be, bbits) := d2b u
    let i0 : Nat := (word0 u / 2 ^ 20) &&& (Exp_mask / 2 ^ 20)
    let (d2', i1, denorm) : F64 × Int × Bool :=
      if i0 != 0 then
        (mkWords ((word0 u &&& Frac_mask) ||| Exp_1) (word1 u), (i0 : Int) - Bias, false)
      else
        let i : Int := bbits + be + ((Bias : Int) + (P - 1) - 1)
        let x : Nat :=
          if 32 < i then shl32 (word0 u) (64 - i).toNat ||| (word1 u / 2 ^ (i - 32).toNat)
          else shl32 (word1 u) (32 - i).toNat
        let d := F64.ofInt x
        (setWord0 d (word0 d + 2 ^ 32 - 31 * Exp_msk1), i - ((Bias : Int) + (P - 1) - 1 + 1), true)
    let ds := F64.add
      (F64.add (F64.mul (F64.sub d2' (F64.ofBits 0x3ff8000000000000))
          (F64.ofRat (mkRat 289529654602168 (10 ^ 15))))
        (F64.ofRat (mkRat 1760912590558 (10 ^ 13))))
      (F64.mul (F64.ofInt i1) (F64.ofRat (mkRat 301029995663981 (10 ^ 15))))
    let k0 := ds.truncInt
    let k1 := if F64.lt ds d0 && F64.ne ds (F64.ofInt k0) then k0 - 1 else k0
    let (k, k_check) : Int × Bool :=
      if 0 ≤ k1 && k1 ≤ Ten_pmax then
        (if F64.lt u (tens k1.toNat) then k1 - 1 else k1, false)
      else (k1, true)
    let j : Int := (bbits : Int) - i1 - 1
    let (b2a, s2a) : Int × Int := if 0 ≤ j then (0, j) else (-j, 0)
    let (b2, s2, b5, s5) : Int × Int × Nat × Nat :=
      if 0 ≤ k then (b2a, s2a + k, 0, k.toNat) else (b2a - k, s2a, (-k).toNat, 0)
    let (ilim, ilim1, ndigits) : Int × Int × Int :=
      if mode == 2 then
        let n := if ndigits0 ≤ 0 then 1 else ndigits0
        (n, n, n)
      else if mode == 3 then
        let i := wrap32 (ndigits0 + wrap32 (k + 1))
        (i, wrap32 (i - 1), ndigits0)
      else (-1, -1, 0)
    let finish (r : List Nat × Int) : Option DtoaOut :=
      some { digits := r.1.reverse, decpt := r.2 + 1, sign }
    let bigPath (u' : F64) : Option DtoaOut :=
      -- "Do we have a small integer?", dtoa.c:2489-2529
      if 0 ≤ be && k ≤ Int_max then
        let ds' := tens k.toNat
        if ndigits < 0 && ilim ≤ 0 then
          if ilim < 0 || F64.le u' (F64.mul (F64.ofInt 5) ds') then
            finish ([], -1 - ndigits)
          else finish ([49], k + 1)
        else finish (smallIntDigits ds' ilim 40 1 u' [] k)
      else
        match dtoaBig u' mode b be bbits denorm k_check b2 s2 b5 s5 k ilim ilim1 ndigits with
        | none => none
        | some r => finish r
    if 0 ≤ ilim && ilim ≤ Quick_max then
      match dtoaQuick u k ilim ilim1 ndigits k_check with
      | some r => finish r
      | none => bigPath u
    else bigPath u

/-! ## `format_float_short` -/

/-- A run of output. Zero padding is run-length encoded, so that a precision of
`INT_MAX` stays a small value and `decide` can look at it. -/
inductive Piece where
  | chars (c : List Nat)
  | zeros (n : Nat)
  deriving DecidableEq, Repr

def Piece.render : Piece → List Nat
  | .chars c => c
  | .zeros n => List.replicate n 48

def render (ps : List Piece) : List Nat := (ps.map Piece.render).flatten

/-- `sprintf("%+.02d", exp)`. -/
def fmtExp (exp : Int) : List Nat :=
  let digs := (toString exp.natAbs).toList.map Char.toNat
  let padded := if digs.length < 2 then 48 :: digs else digs
  (if exp < 0 then 45 else 43) :: padded

structure DtsFlags where
  sign : Bool := false
  add_dot_0 : Bool := false
  alt : Bool := false
  no_neg_0 : Bool := false
  deriving DecidableEq, Repr

/-- `Py_DTST_*`. -/
inductive DtsType where
  | finite | infinite | nan
  deriving DecidableEq, Repr

/-- `format_float_short`, pystrtod.c:968-1218. `code` is `'e'`, `'f'`, `'g'` or `'r'`
and `upper` selects `uc_float_strings`. -/
def format_float_short (d : F64) (code : Nat) (mode : Nat) (precision : Int) (fl : DtsFlags)
    (upper : Bool) : Option (List Piece × DtsType) :=
  match _Py_dg_dtoa d mode precision with
  | none => none
  | some out =>
    let digits := out.digits
    let digits_len : Int := digits.length
    let sign0 := out.sign
    let sign1 :=
      if fl.no_neg_0 && sign0 && (digits_len == 0 || (digits_len == 1 && digits.head? == some 48))
      then false else sign0
    let d0c := digits.headD 0
    if digits_len != 0 && !isDigit d0c then
      let sign2 := if d0c == 78 || d0c == 110 then false else sign1
      let pre : List Nat := if sign2 then [45] else if fl.sign then [43] else []
      if d0c == 73 || d0c == 105 then
        some ([.chars (pre ++ (if upper then [73, 78, 70] else [105, 110, 102]))], .infinite)
      else
        some ([.chars (pre ++ (if upper then [78, 65, 78] else [110, 97, 110]))], .nan)
    else
      let decpt0 := out.decpt
      let vend0 : Int := digits_len
      let (use_exp, vend1) : Bool × Int :=
        if code == 101 then (true, precision)
        else if code == 102 then (false, decpt0 + precision)
        else if code == 103 then
          (decide (decpt0 ≤ -4) ||
            decide ((if fl.add_dot_0 then precision - 1 else precision) < decpt0),
            if fl.alt then precision else vend0)
        else (decide (decpt0 ≤ -4) || decide (16 < decpt0), vend0)
      let (exp, decpt) : Int × Int := if use_exp then (decpt0 - 1, 1) else (0, decpt0)
      let vstart : Int := if decpt ≤ 0 then decpt - 1 else 0
      let vend : Int :=
        if !use_exp && fl.add_dot_0 then (if decpt < vend1 then vend1 else decpt + 1)
        else (if decpt < vend1 then vend1 else decpt)
      let signP : List Piece :=
        if sign1 then [.chars [45]] else if fl.sign then [.chars [43]] else []
      let leftP : List Piece :=
        if decpt ≤ 0 then
          [.zeros (decpt - vstart).toNat, .chars [46], .zeros (0 - decpt).toNat]
        else [.zeros (0 - vstart).toNat]
      let midP : List Piece :=
        if 0 < decpt && decpt ≤ digits_len then
          [.chars (digits.take decpt.toNat), .chars [46], .chars (digits.drop decpt.toNat)]
        else [.chars digits]
      let rightP : List Piece :=
        if digits_len < decpt then
          [.zeros (decpt - digits_len).toNat, .chars [46], .zeros (vend - decpt).toNat]
        else [.zeros (vend - digits_len).toNat]
      let body := signP ++ leftP ++ midP ++ rightP
      let body' := if fl.alt then body else dropDot body
      let expP : List Piece :=
        if use_exp then [.chars ((if upper then 69 else 101) :: fmtExp exp)] else []
      some (body' ++ expP, .finite)
where
  /-- The last character of the body, looked for through empty pieces. -/
  dropDot (ps : List Piece) : List Piece :=
    let rec go : List Piece → List Piece
      | [] => []
      | .zeros 0 :: rest => go rest
      | .chars [] :: rest => go rest
      | .chars c :: rest =>
        if c.getLast? == some 46 then .chars c.dropLast :: rest else .chars c :: rest
      | p :: rest => p :: rest
    (go ps.reverse).reverse

/-- `PyOS_double_to_string`, pystrtod.c:1221-1285, for the codes CPython uses. The
`precision++` at :1240 is `int` arithmetic. -/
def PyOS_double_to_string (val : F64) (format_code : Nat) (precision : Int) (fl : DtsFlags) :
    Option (List Piece × DtsType) :=
  let go (code mode : Nat) (prec : Int) (upper : Bool) :=
    format_float_short val code mode prec fl upper
  if format_code == 69 then go 101 2 (wrap32 (precision + 1)) true
  else if format_code == 101 then go 101 2 (wrap32 (precision + 1)) false
  else if format_code == 70 then go 102 3 precision true
  else if format_code == 102 then go 102 3 precision false
  else if format_code == 71 then go 103 2 (if precision == 0 then 1 else precision) true
  else if format_code == 103 then go 103 2 (if precision == 0 then 1 else precision) false
  else if format_code == 114 && precision == 0 then go 114 0 precision false
  else none

/-- `float_repr`, floatobject.c:348-364. -/
def float_repr (x : F64) : Option (List Nat) :=
  (PyOS_double_to_string x 114 0 { add_dot_0 := true }).map fun r => render r.1

/-! ## `round(x, n)` -/

def asciiOfInt (n : Int) : List Nat := (toString n).toList.map Char.toNat

/-- `double_round`, floatobject.c:915-966. -/
def double_round (x : F64) (ndigits : Int) : Py F64 :=
  match _Py_dg_dtoa x 3 ndigits with
  | none => .error .modelFuel
  | some out =>
    let buflen : Int := out.digits.length
    let mybuf := (if out.sign then [45] else []) ++ 48 :: out.digits ++ 101 :: asciiOfInt (out.decpt - buflen)
    match _Py_dg_strtod mybuf 0 with
    | none => .error .modelFuel
    | some (rounded, _, erange) =>
      if erange && F64.ge rounded.abs d1 then
        .error (.overflowError "rounded value too large to represent")
      else .ok rounded

/-- `PyNumber_AsSsize_t(o, NULL)`: clips. -/
def clipSsize (n : Int) : Int := max (min n ssizeMax) ssizeMin

/-- `float___round___impl` with an `ndigits`, floatobject.c:1051-1075. -/
def float_round_ndigits (x : F64) (o_ndigits : Int) : Py F64 :=
  let ndigits := clipSsize o_ndigits
  if !x.isFinite then .ok x
  else if 323 < ndigits then .ok x
  else if ndigits < -308 then .ok (F64.mul d0 x)
  else double_round x ndigits

/-! ## `float(str)` -/

/-- `_PyOS_ascii_strtod`, pystrtod.c:92-113: value, end, `ERANGE`. -/
def _PyOS_ascii_strtod (s : List Nat) (nptr : Nat) : Option (F64 × Nat × Bool) :=
  match _Py_dg_strtod s nptr with
  | none => none
  | some (r, e, er) =>
    if e == nptr then
      let (r', e') := _Py_parse_inf_or_nan s nptr
      some (r', e', er)
    else some (r, e, er)

/-- `PyOS_string_to_double`, pystrtod.c:298-331. `wantEnd` is `endptr != NULL` and
`overflow` is the exception class name passed as `overflow_exception`. The result
pairs the outcome with `*endptr`. -/
def PyOS_string_to_double (s : List Nat) (start : Nat) (wantEnd : Bool)
    (overflow : Option String) : Option (Py F64 × Nat) :=
  match _PyOS_ascii_strtod s start with
  | none => none
  | some (x, fail_pos, er) =>
    let bad : Py F64 := .error (.valueError "~could not convert string to float: ...")
    if !wantEnd && (fail_pos == start || at_ s fail_pos != 0) then some (bad, fail_pos)
    else if fail_pos == start then some (bad, fail_pos)
    else if er && F64.ge x.abs d1 && overflow.isSome then
      some (.error (.named (overflow.getD "") "~value too large to convert to float: ..."), fail_pos)
    else some (.ok x, fail_pos)

def strToFloatError {α} : Py α := .error (.valueError "~could not convert string to float: ")

/-- `float_from_string_inner`, floatobject.c:149-187: `s` is the whole buffer, with
`len` meaningful bytes. -/
def float_from_string_inner (s : List Nat) (len : Nat) : Py F64 :=
  let i0 := scanLimit s isSpace len 0
  if i0 == len then strToFloatError
  else
    let last := trimEnd s i0 (len - i0) len
    match PyOS_string_to_double s i0 true none with
    | none => .error .modelFuel
    | some (r, e) =>
      if e != last then strToFloatError
      else r
where
  /-- `while (s < last && Py_ISSPACE(*s)) s++`. -/
  scanLimit (s : List Nat) (p : Nat → Bool) (len : Nat) (i : Nat) : Nat :=
    let rec go : Nat → Nat → Nat
      | 0, i => i
      | f + 1, i => if decide (i < len) && p (at_ s i) then go f (i + 1) else i
    go (len + 1) i
  /-- `while (s < last - 1 && Py_ISSPACE(last[-1])) last--`. -/
  trimEnd (s : List Nat) (i0 : Nat) : Nat → Nat → Nat
    | 0, last => last
    | f + 1, last =>
      if decide (i0 + 1 < last) && isSpace (at_ s (last - 1)) then trimEnd s i0 f (last - 1)
      else last

/-- The underscore scan of `_Py_string_to_number_with_underscores`,
pystrtod.c:367-382: stop at the first NUL. The result is the copy, the stop
position, and the last character, or `none` on a misplaced underscore. -/
def underscoreScan : List Nat → Nat → Nat → List Nat → Option (List Nat × Nat × Nat)
  | [], prev, i, acc => some (acc.reverse, i, prev)
  | c :: cs, prev, i, acc =>
    if c == 0 then some (acc.reverse, i, prev)
    else if c == 95 then
      if !isDigit prev then none else underscoreScan cs c (i + 1) acc
    else if prev == 95 && !isDigit c then none
    else underscoreScan cs c (i + 1) (c :: acc)

/-- `_Py_string_to_number_with_underscores`, pystrtod.c:344-402, for any inner
conversion. `s` is the NUL-terminated buffer without the terminator. -/
def _Py_string_to_number_with_underscores {α} (s : List Nat) (what : String)
    (inner : List Nat → Nat → Py α) : Py α :=
  let err : Py α := .error (.valueError s!"~could not convert string to {what}: ")
  if !(s.takeWhile (· != 0)).contains 95 then inner s s.length
  else
    match underscoreScan s 0 0 [] with
    | none => err
    | some (dup, stop, prev) =>
      if prev == 95 then err
      else if stop != s.length then err
      else inner dup dup.length

/-- The first code point of each run of ten Unicode decimal digits (`Nd`). -/
def ndZeros : List Nat :=
  [0x30, 0x660, 0x6f0, 0x7c0, 0x966, 0x9e6, 0xa66, 0xae6, 0xb66, 0xbe6, 0xc66, 0xce6,
   0xd66, 0xde6, 0xe50, 0xed0, 0xf20, 0x1040, 0x1090, 0x17e0, 0x1810, 0x1946, 0x19d0,
   0x1a80, 0x1a90, 0x1b50, 0x1bb0, 0x1c40, 0x1c50, 0xa620, 0xa8d0, 0xa900, 0xa9d0,
   0xa9f0, 0xaa50, 0xabf0, 0xff10, 0x104a0, 0x10d30, 0x11066, 0x110f0, 0x11136, 0x111d0,
   0x112f0, 0x11450, 0x114d0, 0x11650, 0x116c0, 0x116d0, 0x11730, 0x118e0, 0x11950,
   0x11bf0, 0x11c50, 0x11d50, 0x11da0, 0x11f50, 0x16130, 0x16a60, 0x16ac0, 0x16b50,
   0x16d70, 0x1ccf0, 0x1d7ce, 0x1d7d8, 0x1d7e2, 0x1d7ec, 0x1d7f6, 0x1e140, 0x1e2f0,
   0x1e4f0, 0x1e5f1, 0x1e950, 0x1fbf0]

/-- `Py_UNICODE_TODECIMAL`. -/
def toDecimal (ch : Nat) : Option Nat :=
  (ndZeros.find? fun z => decide (z ≤ ch) && decide (ch < z + 10)).map fun z => ch - z

/-- `Py_UNICODE_ISSPACE` above ASCII. -/
def isUnicodeSpace (ch : Nat) : Bool :=
  ch == 0x85 || ch == 0xa0 || ch == 0x1680 || (0x2000 ≤ ch && ch ≤ 0x200a) ||
    ch == 0x2028 || ch == 0x2029 || ch == 0x202f || ch == 0x205f || ch == 0x3000

/-- `_PyUnicode_TransformDecimalAndSpaceToASCII`, unicodeobject.c. A non-ASCII string
maps character by character, and the first character it cannot map becomes a `?`
that ends the string. -/
def transformDecimalAndSpace (cps : List Nat) : List Nat :=
  if cps.all (· < 128) then cps else go cps
where
  go : List Nat → List Nat
    | [] => []
    | ch :: rest =>
      if ch < 127 then ch :: go rest
      else if isUnicodeSpace ch then 32 :: go rest
      else
        match toDecimal ch with
        | some d => (48 + d) :: go rest
        | none => [63]

/-- The string-like arguments of `PyFloat_FromString`. -/
inductive StrArg where
  /-- A `str`, by code points. -/
  | str (cps : List Nat)
  /-- `bytes`, `bytearray`, or any other buffer. -/
  | bytes (b : List Nat)
  deriving DecidableEq, Repr

/-- `PyFloat_FromString`, floatobject.c:189-237. -/
def PyFloat_FromString (v : StrArg) : Py F64 :=
  let s := match v with
    | .str cps => transformDecimalAndSpace cps
    | .bytes b => b
  _Py_string_to_number_with_underscores s "float" float_from_string_inner

/-- `float_new_impl`, floatobject.c:1574-1593, for no argument and for numbers. -/
def float_new_number (x : Option Obj) : Py F64 :=
  match x with
  | none => .ok d0
  | some o => PyFloat_AsDouble o

/-- `float_subtype_new`, floatobject.c:1600-1618: the value of `float(x)`, stored in
a new instance of the subclass. -/
def float_subtype_new (x : Option Obj) : Py F64 :=
  float_new_number (some (x.getD (.int 0)))

/-- `float_vectorcall`, floatobject.c:1620-1635: the argument count check. -/
def float_vectorcall (args : List Obj) : Py F64 :=
  match args with
  | [] => float_new_number none
  | [x] => float_new_number (some x)
  | _ => .error (.typeError s!"float expected at most 1 argument, got {args.length}")

/-- `float_from_number_impl`, floatobject.c:1648-1665. -/
def float_from_number (x : Obj) : Py F64 := PyFloat_AsDouble x

end PyLean.Binary64
