import PyLean.CoreLibs.Rand.Exact

/-!
The real-valued and binomial distributions of `Lib/random.py:500-890`, over a float
type `F`. Each one is a program over `self.random()`, so each is mirrored statement
by statement. Arguments are floats unless the source needs an `int`.

Rejection loops use fuel. `modelFuel` is not a Python outcome: it means that the
draws supplied so far were all rejected.
-/

namespace PyLean.CoreLibs.Rand

open PyLean RM Flt

variable {σ F : Type} [Flt F]

/-- `Random.uniform`, Lib/random.py:500-509. -/
def uniform (g : Gen σ F) (a b : F) : RM σ F := do
  let r ← rnd g
  return a + (b - a) * r

/-- `Random.triangular`, Lib/random.py:511-534. `mode = none` is `None`. The
`try` around `(mode - low) / (high - low)` (:526-529) returns `low` on
`ZeroDivisionError`, after the draw. -/
def triangular (g : Gen σ F) (low high : F) (mode : Option F) : RM σ F := do
  let u ← rnd g
  let c? : Option F := match mode with
    | none => some 0.5
    | some m =>
      match pyDiv (m - low) (high - low) with
      | .ok c => some c
      | .error _ => none
  match c? with
  | none => return low
  | some c =>
    let (u, c, low, high) := if Flt.lt c u then (1.0 - u, 1.0 - c, high, low) else (u, c, low, high)
    let s ← lift (mathSqrt (u * c))
    return low + (high - low) * s

/-- The `while True` of `normalvariate`, Lib/random.py:548-554. -/
def normalLoop (g : Gen σ F) : Nat → RM σ F
  | 0 => raise .modelFuel
  | fuel + 1 => do
    let u1 ← rnd g
    let r2 ← rnd g
    let u2 := 1.0 - r2
    let z ← lift (pyDiv (NV_MAGICCONST * (u1 - 0.5)) u2)
    let zz := z * z / 4.0
    let l ← lift (mathLog u2)
    if Flt.le zz (-l) then pure z else normalLoop g fuel

/-- `Random.normalvariate`, Lib/random.py:536-555. -/
def normalvariate (g : Gen σ F) (fuel : Nat) (mu sigma : F) : RM σ F := do
  let z ← normalLoop g fuel
  return mu + z * sigma

/-- `Random.gauss`, Lib/random.py:557-593. `gn` is `self.gauss_next`; the result
carries its new value. -/
def gauss (g : Gen σ F) (mu sigma : F) (gn : Option F) : RM σ (F × Option F) := do
  match gn with
  | some z => return (mu + z * sigma, none)
  | none =>
    let r1 ← rnd g
    let x2pi := r1 * TWOPI
    let r2 ← rnd g
    let l ← lift (mathLog (1.0 - r2))
    let g2rad ← lift (mathSqrt (-2.0 * l))
    let c ← lift (mathCos x2pi)
    let s ← lift (mathSin x2pi)
    return (mu + (c * g2rad) * sigma, some (s * g2rad))

/-- `Random.lognormvariate`, Lib/random.py:595-603. -/
def lognormvariate (g : Gen σ F) (fuel : Nat) (mu sigma : F) : RM σ F := do
  let x ← normalvariate g fuel mu sigma
  lift (mathExp x)

/-- `Random.expovariate`, Lib/random.py:605-623. -/
def expovariate (g : Gen σ F) (lambd : F) : RM σ F := do
  let r ← rnd g
  let l ← lift (mathLog (1.0 - r))
  lift (pyDiv (-l) lambd)

/-- The acceptance test `u2 < 1.0 - d * d or u2 <= (1.0 - d) * _exp(d)`,
Lib/random.py:654, with `or`'s short circuit. -/
def vonmisesAccept (u2 d : F) : Py Bool :=
  if Flt.lt u2 (1.0 - d * d) then .ok true
  else do
    let e ← mathExp d
    return Flt.le u2 ((1.0 - d) * e)

/-- The `while True` of `vonmisesvariate`, Lib/random.py:648-655. The result is `z`. -/
def vonmisesLoop (g : Gen σ F) (r : F) : Nat → RM σ F
  | 0 => raise .modelFuel
  | fuel + 1 => do
    let u1 ← rnd g
    let z ← lift (mathCos (PI * u1))
    let d ← lift (pyDiv z (r + z))
    let u2 ← rnd g
    let accept ← lift (vonmisesAccept u2 d)
    if accept then pure z else vonmisesLoop g r fuel

/-- `Random.vonmisesvariate`, Lib/random.py:625-665. -/
def vonmisesvariate (g : Gen σ F) (fuel : Nat) (mu kappa : F) : RM σ F := do
  if Flt.le kappa 1e-6 then
    let u ← rnd g
    return TWOPI * u
  else
    let s ← lift (pyDiv 0.5 kappa)
    let root ← lift (mathSqrt (1.0 + s * s))
    let r := s + root
    let z ← vonmisesLoop g r fuel
    let q ← lift (pyDiv 1.0 r)
    let f ← lift (pyDiv (q + z) (1.0 + q * z))
    let u3 ← rnd g
    let a ← lift (mathAcos f)
    if Flt.lt 0.5 u3 then lift (pyMod (mu + a) TWOPI)
    else lift (pyMod (mu - a) TWOPI)

/-- The `alpha > 1.0` loop of `gammavariate`, Lib/random.py:701-711. The result is
`x`; the caller multiplies by `beta`. -/
def gammaCheng (g : Gen σ F) (alpha ainv bbb ccc : F) : Nat → RM σ F
  | 0 => raise .modelFuel
  | fuel + 1 => do
    let u1 ← rnd g
    if !(Flt.lt 1e-7 u1 && Flt.lt u1 0.9999999) then gammaCheng g alpha ainv bbb ccc fuel
    else
      let r2 ← rnd g
      let u2 := 1.0 - r2
      let q ← lift (pyDiv u1 (1.0 - u1))
      let l ← lift (mathLog q)
      let v ← lift (pyDiv l ainv)
      let ev ← lift (mathExp v)
      let x := alpha * ev
      let z := u1 * u1 * u2
      let r := bbb + ccc * v - x
      if Flt.le 0.0 (r + SG_MAGICCONST - 4.5 * z) then pure x
      else
        let lz ← lift (mathLog z)
        if Flt.le lz r then pure x else gammaCheng g alpha ainv bbb ccc fuel

/-- `x` in the `alpha < 1.0` loop of `gammavariate`, Lib/random.py:724-727. -/
def gammaGSx (alpha b p : F) : Py F :=
  if Flt.le p 1.0 then do
    let e ← pyDiv 1.0 alpha
    pyPow p e
  else do
    let q ← pyDiv (b - p) alpha
    let l ← mathLog q
    return -l

/-- The `alpha < 1.0` loop of `gammavariate` (ALGORITHM GS), Lib/random.py:720-733. -/
def gammaGS (g : Gen σ F) (alpha : F) : Nat → RM σ F
  | 0 => raise .modelFuel
  | fuel + 1 => do
    let u ← rnd g
    let b := (E + alpha) / E
    let p := b * u
    let x ← lift (gammaGSx alpha b p)
    let u1 ← rnd g
    if Flt.lt 1.0 p then
      let w ← lift (pyPow x (alpha - 1.0))
      if Flt.le u1 w then pure x else gammaGS g alpha fuel
    else
      let w ← lift (mathExp (-x))
      if Flt.le u1 w then pure x else gammaGS g alpha fuel

/-- `Random.gammavariate`, Lib/random.py:667-734. -/
def gammavariate (g : Gen σ F) (fuel : Nat) (alpha beta : F) : RM σ F := do
  if Flt.le alpha 0.0 || Flt.le beta 0.0 then
    raise (.valueError "gammavariate: alpha and beta must be > 0.0")
  else if Flt.lt 1.0 alpha then
    let ainv ← lift (mathSqrt (2.0 * alpha - 1.0))
    let bbb := alpha - LOG4
    let ccc := alpha + ainv
    let x ← gammaCheng g alpha ainv bbb ccc fuel
    return x * beta
  else if Flt.beq alpha 1.0 then
    let r ← rnd g
    let l ← lift (mathLog (1.0 - r))
    return (-l) * beta
  else
    let x ← gammaGS g alpha fuel
    return x * beta

/-- `Random.betavariate`, Lib/random.py:736-766. -/
def betavariate (g : Gen σ F) (fuel : Nat) (alpha beta : F) : RM σ F := do
  let y ← gammavariate g fuel alpha 1.0
  if truthy y then
    let w ← gammavariate g fuel beta 1.0
    lift (pyDiv y (y + w))
  else return 0.0

/-- `Random.paretovariate`, Lib/random.py:768-773. -/
def paretovariate (g : Gen σ F) (alpha : F) : RM σ F := do
  let r ← rnd g
  let u := 1.0 - r
  let e ← lift (pyDiv (-1.0) alpha)
  lift (pyPow u e)

/-- `Random.weibullvariate`, Lib/random.py:775-784. -/
def weibullvariate (g : Gen σ F) (alpha beta : F) : RM σ F := do
  let r ← rnd g
  let u := 1.0 - r
  let l ← lift (mathLog u)
  let e ← lift (pyDiv 1.0 beta)
  let w ← lift (pyPow (-l) e)
  return alpha * w

/-- The BG loop of `binomialvariate`, Lib/random.py:838-846, with its
`except ValueError: continue`. -/
def binomBG (g : Gen σ F) (n : Int) (c : F) : Nat → Int → Int → RM σ Int
  | 0, _, _ => raise .modelFuel
  | fuel + 1, x, y => do
    let r ← rnd g
    let step : Py Int := do
      let l ← mathLog2 r
      let q ← pyDiv l c
      mathFloor q
    match step with
    | .error (.valueError _) => binomBG g n c fuel x y
    | .error e => raise e
    | .ok v =>
      let y := y + v + 1
      if y > n then pure x else binomBG g n c fuel (x + 1) y

/-- The values `setup_complete` guards, Lib/random.py:878-883. -/
structure BtrsSetup (F : Type) where
  alpha : F
  lpq : F
  m : Int
  h : F

/-- The setup block, Lib/random.py:879-882. -/
def btrsSetup (n : Int) (p spq b : F) : Py (BtrsSetup F) := do
  let t ← pyDiv 5.1 b
  let alpha := (2.83 + t) * spq
  let q ← pyDiv p (1.0 - p)
  let lpq ← mathLog q
  let n1 : F ← pyFloat (n + 1)
  let m ← mathFloor (n1 * p)
  let a1 ← pyFloat (m + 1)
  let a2 ← pyFloat (n - m + 1)
  let l1 ← mathLgamma a1
  let l2 ← mathLgamma a2
  return { alpha, lpq, m, h := l1 + l2 }

/-- `if not setup_complete: ...`, Lib/random.py:878-883. -/
def btrsEnsure (n : Int) (p spq b : F) : Option (BtrsSetup F) → Py (BtrsSetup F)
  | some st => .ok st
  | none => btrsSetup n p spq b

/-- The BTRS loop, Lib/random.py:859-890, with its
`except ZeroDivisionError: continue`. -/
def btrsLoop (g : Gen σ F) (n : Int) (p spq a b c vr : F) :
    Nat → Option (BtrsSetup F) → RM σ Int
  | 0, _ => raise .modelFuel
  | fuel + 1, setup => do
    let u0 ← rnd g
    let u := u0 - 0.5
    let us := 0.5 - fabs u
    let kk : Py Int := do
      let d ← pyDiv (2.0 * a) us
      mathFloor ((d + b) * u + c)
    match kk with
    | .error (.zeroDivisionError _) => btrsLoop g n p spq a b c vr fuel setup
    | .error e => raise e
    | .ok k =>
      if k < 0 ∨ k > n then btrsLoop g n p spq a b c vr fuel setup
      else
        let v ← rnd g
        if Flt.le 0.07 us && Flt.le v vr then pure k
        else
          let st ← lift (btrsEnsure n p spq b setup)
          let d1 ← lift (pyDiv a (us * us))
          let d2 ← lift (pyDiv st.alpha (d1 + b))
          let v := v * d2
          let lv ← lift (mathLog v)
          let a1 ← lift (pyFloat (k + 1))
          let a2 ← lift (pyFloat (n - k + 1))
          let l1 ← lift (mathLgamma a1)
          let l2 ← lift (mathLgamma a2)
          let km ← lift (pyFloat (k - st.m))
          if Flt.le lv (st.h - l1 - l2 + km * st.lpq) then pure k
          else btrsLoop g n p spq a b c vr fuel (some st)

/-- `Random.binomialvariate`, Lib/random.py:789-890. `n` is an `int`. `depth` is
fuel for the recursion at :829, which never goes deeper than one call. -/
def binomialvariate (g : Gen σ F) (fuel : Nat) : Nat → Int → F → RM σ Int
  | 0, _, _ => raise .modelFuel
  | depth + 1, n, p => do
    if n < 0 then raise (.valueError "n must be non-negative")
    else if Flt.le p 0.0 || Flt.le 1.0 p then
      if Flt.beq p 0.0 then return 0
      else if Flt.beq p 1.0 then return n
      else raise (.valueError "p must be in the range 0.0 <= p <= 1.0")
    else if n = 1 then
      let r ← rnd g
      return if Flt.lt r p then 1 else 0
    else if Flt.lt 0.5 p then
      let x ← binomialvariate g fuel depth n (1.0 - p)
      return n - x
    else
      let nf : F ← lift (pyFloat n)
      if Flt.lt (nf * p) 10.0 then
        let c ← lift (mathLog2 (1.0 - p))
        if !truthy c then return 0
        else binomBG g n c fuel 0 0
      else if !(Flt.le 10.0 (nf * p) && Flt.le p 0.5) then
        raise (.assertionError "")
      else
        let spq ← lift (mathSqrt (nf * p * (1.0 - p)))
        let b := 1.15 + 2.53 * spq
        let a := -0.0873 + 0.0248 * b + 0.01 * p
        let c := nf * p + 0.5
        let t ← lift (pyDiv 4.2 b)
        let vr := 0.92 - t
        btrsLoop g n p spq a b c vr fuel none

end PyLean.CoreLibs.Rand
