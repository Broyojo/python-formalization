import PyLean.Binary64.Model

/-!
The multiple-precision kernel of `Python/dtoa.c`, CPython 3.14.7, limb by limb:
base `2 ^ 32` digits, least significant first, in the order the C loops touch them.
Each helper keeps the loop structure of its source so that `Bigint.val` can be
related to it in `BigintLemmas.lean`.

`Balloc`, `Bfree` and `Bcopy` are memory management: a `Bigint` value here owns its
limbs, and growing a limb list needs no pool.
-/

namespace PyLean.Binary64

/-- `struct Bigint`. `x` is `b->x[0 : b->wds]`; `sign` only matters on the result
of `diff`. -/
structure Bigint where
  sign : Bool := false
  x : List Nat
  deriving DecidableEq, Repr, Inhabited

namespace Bigint

/-- Value of a limb list. -/
def limbsVal : List Nat → Nat
  | [] => 0
  | d :: ds => d + 2 ^ 32 * limbsVal ds

def val (b : Bigint) : Nat := limbsVal b.x

/-- `b->wds`. -/
def wds (b : Bigint) : Nat := b.x.length

/-- `b->x[0]`. -/
def x0 (b : Bigint) : Nat := b.x.headD 0

/-- `!b->x[0] && b->wds <= 1`. -/
def isZero (b : Bigint) : Bool := b.x0 == 0 && decide (b.wds ≤ 1)

/-- `b->x[b->wds-1]`. -/
def top (b : Bigint) : Nat := b.x.getLastD 0

end Bigint

/-- `(ULong)(x << n)` for `n < 32`. -/
def shl32 (x n : Nat) : Nat := (x * 2 ^ n) % 2 ^ 32

/-- The `do ... while(++i < wds)` loop of `multadd`, dtoa.c:454-459, and the store
of a final carry at :460-473. -/
def multaddLoop (m : Nat) : List Nat → Nat → List Nat
  | [], carry => if carry != 0 then [carry] else []
  | d :: ds, carry =>
    let y := d * m + carry
    (y % 2 ^ 32) :: multaddLoop m ds (y / 2 ^ 32)

/-- `multadd`, dtoa.c:442-475. -/
def multadd (b : Bigint) (m a : Nat) : Bigint := { b with x := multaddLoop m b.x a }

/-- `s2b`'s two loops, dtoa.c:502-512: `dig i` is the `i`th significant digit. -/
def s2bLoop (dig : Nat → Nat) : Nat → Nat → Bigint → Bigint
  | 0, _, b => b
  | n + 1, i, b => s2bLoop dig n (i + 1) (multadd b 10 (dig i))

/-- `s2b`, dtoa.c:483-514. The caller passes the digit accessor, which skips the
decimal point exactly as the `s++` at :507 does. -/
def s2b (dig : Nat → Nat) (nd y9 : Nat) : Bigint :=
  let b : Bigint := { x := [y9] }
  if nd ≤ 9 then b else s2bLoop dig (nd - 9) 9 b

/-- `hi0bits`, dtoa.c:518-545. -/
def hi0bits (x0 : Nat) : Nat :=
  let (k1, x1) := if x0 &&& 0xffff0000 == 0 then (16, shl32 x0 16) else (0, x0)
  let (k2, x2) := if x1 &&& 0xff000000 == 0 then (k1 + 8, shl32 x1 8) else (k1, x1)
  let (k3, x3) := if x2 &&& 0xf0000000 == 0 then (k2 + 4, shl32 x2 4) else (k2, x2)
  let (k4, x4) := if x3 &&& 0xc0000000 == 0 then (k3 + 2, shl32 x3 2) else (k3, x3)
  if x4 &&& 0x80000000 == 0 then
    if x4 &&& 0x40000000 == 0 then 32 else k4 + 1
  else k4

/-- `lo0bits`, dtoa.c:550-591: the count, and `*y` afterwards. -/
def lo0bits (y : Nat) : Nat × Nat :=
  let x := y
  if x &&& 7 != 0 then
    if x &&& 1 != 0 then (0, y)
    else if x &&& 2 != 0 then (1, x / 2)
    else (2, x / 4)
  else
    let (k1, x1) := if x &&& 0xffff == 0 then (16, x / 2 ^ 16) else (0, x)
    let (k2, x2) := if x1 &&& 0xff == 0 then (k1 + 8, x1 / 2 ^ 8) else (k1, x1)
    let (k3, x3) := if x2 &&& 0xf == 0 then (k2 + 4, x2 / 2 ^ 4) else (k2, x2)
    let (k4, x4) := if x3 &&& 0x3 == 0 then (k3 + 2, x3 / 2 ^ 2) else (k3, x3)
    if x4 &&& 1 == 0 then
      let x5 := x4 / 2
      if x5 == 0 then (32, y) else (k4 + 1, x5)
    else (k4, x4)

/-- `i2b`, dtoa.c:595-606. -/
def i2b (i : Nat) : Bigint := { x := [i] }

/-- Drop high zero limbs. -/
def trimHigh (x : List Nat) : List Nat := (x.reverse.dropWhile (· == 0)).reverse

/-- The inner `do` loop of `mult`, dtoa.c:655-661: add `a * y` into `xc`. -/
def multInner (y : Nat) : List Nat → List Nat → Nat → List Nat
  | [], [], _ => []
  | [], _ :: cs, carry => carry :: cs
  | _ :: _, [], _ => []
  | a :: as, c :: cs, carry =>
    let z := a * y + c + carry
    (z % 2 ^ 32) :: multInner y as cs (z / 2 ^ 32)

/-- The outer loop of `mult`, dtoa.c:650-663: `xc0` walks up `c`. -/
def multOuter (xa : List Nat) : List Nat → List Nat → List Nat
  | [], xc => xc
  | y :: ys, xc =>
    match (if y != 0 then multInner y xa xc 0 else xc) with
    | [] => []
    | c :: cs => c :: multOuter xa ys cs

/-- `mult`, dtoa.c:611-667. -/
def mult (a0 b0 : Bigint) : Bigint :=
  if a0.isZero || b0.isZero then { x := [0] }
  else
    let (a, b) := if a0.wds < b0.wds then (b0, a0) else (a0, b0)
    let wc := a.wds + b.wds
    { x := trimHigh (multOuter a.x b.x (List.replicate wc 0)) }

/-- `interp->dtoa.p5s`, built by `_PyDtoa_Init`, dtoa.c:2807-2830: `5 ** (2 ** (i + 2))`. -/
def p5s : Array Bigint :=
  (List.range 7).foldl (fun acc _ => let p := acc.back!; acc.push (mult p p)) #[i2b 625]

/-- The `for(;;)` loop of `pow5mult`, dtoa.c:699-712. -/
def pow5Loop : Nat → Nat → Nat → Bigint → Bigint
  | 0, _, _, b => b
  | fuel + 1, i, k, b =>
    let b1 := if k &&& 1 != 0 then mult b (p5s[i]!) else b
    if k / 2 == 0 then b1 else pow5Loop fuel (i + 1) (k / 2) b1

/-- `pow5mult`, dtoa.c:675-714 (and the uncached twin at :721-764). -/
def pow5mult (b0 : Bigint) (k : Nat) : Bigint :=
  let i := k &&& 3
  let b := if i != 0 then multadd b0 ([5, 25, 125].getD (i - 1) 0) 0 else b0
  if k / 4 == 0 then b else pow5Loop 8 0 (k / 4) b

/-- The shifting `do` loop of `lshift`, dtoa.c:800-805: the limbs, then the last `z`. -/
def lshiftLoop (k : Nat) : List Nat → Nat → List Nat
  | [], z => if z != 0 then [z] else []
  | d :: ds, z => (shl32 d k ||| z) :: lshiftLoop k ds (d / 2 ^ (32 - k))

/-- `lshift`, dtoa.c:772-814. -/
def lshift (b : Bigint) (k : Nat) : Bigint :=
  if k == 0 || b.isZero then b
  else
    let n := k / 32
    let k' := k % 32
    let low := List.replicate n 0
    if k' != 0 then { x := low ++ lshiftLoop k' b.x 0 }
    else { x := low ++ b.x }

/-- The limb loop of `cmp`, dtoa.c:839-845, from the top limb down. -/
def cmpLoop : List Nat → List Nat → Int
  | a :: as, b :: bs => if a != b then (if a < b then -1 else 1) else cmpLoop as bs
  | _, _ => 0

/-- `cmp`, dtoa.c:819-846. -/
def cmp (a b : Bigint) : Int :=
  let i := (a.wds : Int) - b.wds
  if i != 0 then i else cmpLoop a.x.reverse b.x.reverse

/-- The subtraction loops of `diff`, dtoa.c:889-899, with `y` a wrapping `ULLong`. -/
def diffLoop : List Nat → List Nat → Nat → List Nat
  | [], _, _ => []
  | a :: as, [], borrow =>
    let y := (a + 2 ^ 64 - borrow) % 2 ^ 64
    (y % 2 ^ 32) :: diffLoop as [] (y / 2 ^ 32 % 2)
  | a :: as, b :: bs, borrow =>
    let y := (a + 2 ^ 64 - b - borrow) % 2 ^ 64
    (y % 2 ^ 32) :: diffLoop as bs (y / 2 ^ 32 % 2)

/-- `diff`, dtoa.c:852-904. -/
def diff (a0 b0 : Bigint) : Bigint :=
  let i := cmp a0 b0
  if i == 0 then { x := [0] }
  else
    let (a, b, s) := if i < 0 then (b0, a0, true) else (a0, b0, false)
    { sign := s, x := trimHigh (diffLoop a.x b.x 0) }

/-- `word0(x)`, the high 32 bits. -/
def word0 (x : F64) : Nat := x.bits / 2 ^ 32

/-- `word1(x)`, the low 32 bits. -/
def word1 (x : F64) : Nat := x.bits % 2 ^ 32

def mkWords (w0 w1 : Nat) : F64 := F64.ofBits (w0 * 2 ^ 32 + w1)

/-- `word0(x) = w`, leaving `word1`. -/
def setWord0 (x : F64) (w : Nat) : F64 := mkWords (w % 2 ^ 32) (word1 x)

/-- `word1(x) = w`, leaving `word0`. -/
def setWord1 (x : F64) (w : Nat) : F64 := mkWords (word0 x) (w % 2 ^ 32)

def Exp_shift : Nat := 20
def Exp_msk1 : Nat := 0x100000
def Exp_mask : Nat := 0x7ff00000
def P : Nat := 53
def Bias : Nat := 1023
def Etiny : Int := -1074
def Exp_1 : Nat := 0x3ff00000
def Ebits : Nat := 11
def Frac_mask : Nat := 0xfffff
def Bndry_mask : Nat := 0xfffff
def Sign_bit : Nat := 0x80000000

/-- `ulp`, dtoa.c:909-919. `L` wraps in 32 bits if `x` is too small for the "normal
result" the comment asks for; the callers do not go there. -/
def ulpD (x : F64) : F64 :=
  mkWords (((word0 x &&& Exp_mask) + 2 ^ 32 - (P - 1) * Exp_msk1) % 2 ^ 32) 0

/-- `b2d`, dtoa.c:923-956: the double in `[1, 2)` holding the top bits of `a`, and
the exponent. Reading below `x[0]` gives `0`. -/
def b2d (a : Bigint) : F64 × Nat :=
  let rev := a.x.reverse
  let y := rev.headD 0
  let k := hi0bits y
  let e := 32 - k
  let next1 := rev.getD 1 0
  let next2 := rev.getD 2 0
  if k < Ebits then
    let w0 := Exp_1 ||| (y / 2 ^ (Ebits - k))
    let w := next1
    let w1 := shl32 y ((32 - Ebits) + k) ||| (w / 2 ^ (Ebits - k))
    (mkWords w0 w1, e)
  else
    let z := next1
    let k' := k - Ebits
    if k' != 0 then
      let w0 := Exp_1 ||| shl32 y k' ||| (z / 2 ^ (32 - k'))
      let y' := next2
      let w1 := shl32 z k' ||| (y' / 2 ^ (32 - k'))
      (mkWords w0 w1, e)
    else (mkWords (Exp_1 ||| y) z, e)

/-- `sd2b`, dtoa.c:979-1026. -/
def sd2b (d : F64) (scale0 : Nat) : Bigint × Int :=
  let x0 := word1 d
  let x1 := word0 d &&& Frac_mask
  let e0 : Int := Etiny - 1 + (((word0 d &&& Exp_mask) / 2 ^ Exp_shift : Nat) : Int)
  let (e1, x1) : Int × Nat := if e0 < Etiny then (Etiny, x1) else (e0, x1 ||| Exp_msk1)
  let (e2, x0', x1') : Int × Nat × Nat :=
    if scale0 != 0 && (x0 != 0 || x1 != 0) then
      let e2 := e1 - scale0
      if e2 < Etiny then
        let scale := (Etiny - e2).toNat
        let (x0a, x1a, scale') : Nat × Nat × Nat :=
          if 32 ≤ scale then (x1, 0, scale - 32) else (x0, x1, scale)
        if scale' != 0 then
          ((Etiny, (x0a / 2 ^ scale') ||| shl32 x1a (32 - scale'), x1a / 2 ^ scale'))
        else (Etiny, x0a, x1a)
      else (e2, x0, x1)
    else (e1, x0, x1)
  ({ x := if x1' == 0 then [x0'] else [x0', x1'] }, e2)

/-- `d2b`, dtoa.c:1037-1080: `(b, *e, *bits)`. -/
def d2b (d : F64) : Bigint × Int × Nat :=
  let z0 := word0 d &&& Frac_mask
  let w0 := word0 d &&& 0x7fffffff
  let de := w0 / 2 ^ Exp_shift
  let z := if de != 0 then z0 ||| Exp_msk1 else z0
  let y := word1 d
  let (limbs, k) : List Nat × Nat :=
    if y != 0 then
      let (k, y') := lo0bits y
      if k != 0 then
        let x0 := y' ||| shl32 z (32 - k)
        let z' := z / 2 ^ k
        (if z' != 0 then [x0, z'] else [x0], k)
      else (if z != 0 then [y', z] else [y'], 0)
    else
      let (k, z') := lo0bits z
      ([z'], k + 32)
  let b : Bigint := { x := limbs }
  if de != 0 then
    (b, (de : Int) - Bias - (P - 1) + k, P - k)
  else
    (b, (de : Int) - Bias - (P - 1) + 1 + k, 32 * limbs.length - hi0bits (limbs.getLastD 0))

/-- `ratio`, dtoa.c:1085-1101. -/
def ratio (a b : Bigint) : F64 :=
  let (da, ka) := b2d a
  let (db, kb) := b2d b
  let k : Int := (ka : Int) - kb + 32 * ((a.wds : Int) - b.wds)
  if 0 < k then
    F64.div (setWord0 da (word0 da + k.toNat * Exp_msk1)) db
  else
    F64.div da (setWord0 db (word0 db + (-k).toNat * Exp_msk1))

/-- `dshift`, dtoa.c:1126-1133. -/
def dshift (b : Bigint) (p2 : Int) : Nat :=
  let rv0 : Int := (hi0bits b.top : Int) - 4
  let rv := if 0 < p2 then rv0 - p2 else rv0
  (rv % 32).toNat

/-- The subtraction loops of `quorem`, dtoa.c:1165-1172 and :1186-1193: walk `S`
and `b` together, with `y` and `ys` wrapping `ULLong`s. -/
def quoremSub (q : Nat) : List Nat → List Nat → Nat → Nat → List Nat
  | [], bs, _, _ => bs
  | _ :: _, [], _, _ => []
  | s :: ss, b :: bs, carry, borrow =>
    let ys := s * q + carry
    let carry' := ys / 2 ^ 32
    let y := (b + 2 ^ 64 - (ys % 2 ^ 32) - borrow) % 2 ^ 64
    let borrow' := y / 2 ^ 32 % 2
    (y % 2 ^ 32) :: quoremSub q ss bs carry' borrow'

/-- `while(--bxe > bx && !*bxe) --n`: drop high zero limbs, keeping one. -/
def trimKeep1 (x : List Nat) : List Nat :=
  match trimHigh x with
  | [] => x.take 1
  | l => l

/-- `quorem`, dtoa.c:1139-1203: the quotient digit and the updated `b`. -/
def quorem (b : Bigint) (S : Bigint) : Nat × Bigint :=
  if b.wds < S.wds then (0, b)
  else
    let q0 := b.top / (S.top + 1)
    let b1 : Bigint :=
      if q0 != 0 then
        let x := quoremSub q0 S.x b.x 0 0
        { b with x := if x.getLastD 0 == 0 then trimKeep1 x else x }
      else b
    if 0 ≤ cmp b1 S then
      let x := quoremSub 1 S.x b1.x 0 0
      (q0 + 1, { b1 with x := if x.getLastD 0 == 0 then trimKeep1 x else x })
    else (q0, b1)

structure BCinfo where
  e0 : Int
  nd : Nat
  nd0 : Nat
  scale : Nat

/-- `sulp`, dtoa.c:1211-1226. -/
def sulp (x : F64) (scale : Nat) : F64 :=
  if scale != 0 && decide ((word0 x &&& Exp_mask) / 2 ^ Exp_shift < 2 * P + 1) then
    mkWords ((P + 2) * Exp_msk1) 0
  else ulpD x

end PyLean.Binary64
