import PyLean.MathInt.FltFns

/-!
# `Modules/mathmodule.c`: `fsum`, `hypot`, `dist`, `prod`

CPython 3.15.2. An iterable is its items followed by how iteration ends (`It`): either
cleanly, or with an exception from `PyIter_Next`, so a failing iterator is part of every
loop.
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64

/-- An iterable: the items `PyIter_Next` yields, then `none` (exhausted) or the exception
it raises. -/
structure It where
  items : List Arg
  err : Option PyExc := none
  deriving Inhabited

/-- How a loop over `It` ends after the items. -/
def It.finish {α : Type} (it : It) (a : α) : Py α :=
  match it.err with
  | some e => .error e
  | none => .ok a

/-! ## Compensated arithmetic, mathmodule.c:93-187 -/

structure DoubleLength where
  hi : F64
  lo : F64

/-- `dl_fast_sum`, mathmodule.c:95-103 (for `fabs(a) >= fabs(b)`). -/
def dl_fast_sum (a b : F64) : DoubleLength :=
  let x := F64.add a b
  let y := F64.add (F64.sub a x) b
  ⟨x, y⟩

/-- `dl_sum`, mathmodule.c:105-113. -/
def dl_sum (a b : F64) : DoubleLength :=
  let x := F64.add a b
  let z := F64.sub x a
  let y := F64.add (F64.sub a (F64.sub x z)) (F64.sub b z)
  ⟨x, y⟩

/-- `dl_mul`, mathmodule.c:117-124, the version compiled without `UNRELIABLE_FMA`. -/
def dl_mul (x y : F64) : DoubleLength :=
  let z := F64.mul x y
  let zz := F64.fma x y (F64.neg z)
  ⟨z, zz⟩

/-! ## `fsum`, mathmodule.c:1173-1396 -/

/-- `NUM_PARTIALS`, mathmodule.c:1209. -/
def NUM_PARTIALS : Nat := 32

/-- `_fsum_realloc`, mathmodule.c:1212-1237, as a capacity: the doubled size, or `none` for
`MemoryError("math.fsum partials")` when the size check fails. A failing allocator is not
modelled. -/
def _fsum_realloc (n m : Nat) : Option Nat :=
  let m := m + m
  if n < m && m < (2 ^ 63 - 1) / 8 then some m else none

/-- The inner loop of mathmodule.c:1309-1320 over the partials `p[0..n)`: the final `x` and
the kept `lo` values `p[0..i)`. -/
def fsumInner : F64 → List F64 → List F64 → F64 × List F64
  | x, [], acc => (x, acc.reverse)
  | x, y :: ys, acc =>
    let (x, y) := if F64.lt (F64.abs x) (F64.abs y) then (y, x) else (x, y)
    let hi := F64.add x y
    let yr := F64.sub hi x
    let lo := F64.sub y yr
    fsumInner hi ys (if !F64.eq lo c0 then lo :: acc else acc)

/-- The state of `math_fsum` between items. -/
structure FsumSt where
  p : List F64 := []
  m : Nat := NUM_PARTIALS
  special_sum : F64 := c0
  inf_sum : F64 := c0

/-- One item, mathmodule.c:1308-1344. -/
def fsumStep (st : FsumSt) (xsave : F64) : Py FsumSt :=
  let (x, ps) := fsumInner xsave st.p []
  if !isZeroC x then
    if !x.isFinite then
      if xsave.isFinite then .error (.overflowError "intermediate overflow in fsum")
      else
        let inf_sum := if xsave.isInf then F64.add st.inf_sum xsave else st.inf_sum
        .ok { st with p := [], special_sum := F64.add st.special_sum xsave, inf_sum }
    else if st.m ≤ ps.length then
      match _fsum_realloc ps.length st.m with
      | some m => .ok { st with p := ps ++ [x], m }
      | none => .error (.named "MemoryError" "math.fsum partials")
    else .ok { st with p := ps ++ [x] }
  else .ok { st with p := ps }

/-- `sum_exact` from the top, mathmodule.c:1361-1370: the partials below `hi` (top first),
the running `hi`, the last `lo`; returns `hi`, `lo` and what is left below. -/
def fsumTop : List F64 → F64 → F64 → F64 × F64 × List F64
  | [], hi, lo => (hi, lo, [])
  | y :: ys, x, _ =>
    let hi := F64.add x y
    let yr := F64.sub hi x
    let lo := F64.sub y yr
    if !F64.eq lo c0 then (hi, lo, ys) else fsumTop ys hi lo

/-- The end of `math_fsum`, mathmodule.c:1347-1385. -/
def fsumEnd (st : FsumSt) : Py F64 :=
  if !isZeroC st.special_sum then
    if st.inf_sum.isNaN then .error (.valueError "-inf + inf in fsum")
    else .ok st.special_sum
  else
    match st.p.reverse with
    | [] => .ok c0
    | top :: rest =>
      let (hi, lo, below) := fsumTop rest top c0
      match below with
      | [] => .ok hi
      | pn1 :: _ =>
        if (F64.lt lo c0 && F64.lt pn1 c0) || (F64.lt c0 lo && F64.lt c0 pn1) then
          let y := F64.mul lo c2
          let x := F64.add hi y
          let yr := F64.sub x hi
          if F64.eq y yr then .ok x else .ok hi
        else .ok hi

/-- `math_fsum`, mathmodule.c:1280-1396. -/
def math_fsum (it : It) : Py F64 := do
  let st ← it.items.foldlM (fun st item => do fsumStep st (← assignDouble item)) {}
  let st ← it.finish st
  fsumEnd st

/-! ## `vector_norm`, `hypot`, `dist` -/

/-- `DBL_MIN`. -/
def DBL_MIN : F64 := F64.ofBits 0x0010000000000000

/-- The loop and correction of `vector_norm`, mathmodule.c:1921-1944. -/
def vectorNormCore (vec : List F64) (max_e : Int) : F64 :=
  let scale := F64.ldexp c1 (-max_e)
  let (csum, frac1, frac2) := vec.foldl (fun (s : F64 × F64 × F64) x =>
    let (csum, frac1, frac2) := s
    let x := F64.mul x scale
    let pr := dl_mul x x
    let sm := dl_fast_sum csum pr.hi
    (sm.hi, F64.add frac1 pr.lo, F64.add frac2 sm.lo)) (c1, c0, c0)
  let h := F64.sqrt (F64.add (F64.sub csum c1) (F64.add frac1 frac2))
  let pr := dl_mul (F64.neg h) h
  let sm := dl_fast_sum csum pr.hi
  let csum := sm.hi
  let frac1 := F64.add frac1 pr.lo
  let frac2 := F64.add frac2 sm.lo
  let x := F64.add (F64.sub csum c1) (F64.add frac1 frac2)
  let h := F64.add h (F64.div x (F64.mul c2 h))
  F64.div h scale

/-- `vector_norm`, mathmodule.c:1896-1945. `fuel` bounds the subnormal recursion (:1914-1920),
which happens at most once. -/
def vector_norm : Nat → List F64 → F64 → Bool → F64
  | fuel, vec, max, found_nan =>
    if max.isInf then max
    else if found_nan then cNaN
    else if isZeroC max || vec.length ≤ 1 then max
    else
      let max_e := (F64.frexp max).2
      if max_e < -1023 then
        match fuel with
        | 0 => cNaN
        | k + 1 =>
          F64.mul DBL_MIN (vector_norm k (vec.map (fun v => F64.div v DBL_MIN))
            (F64.div max DBL_MIN) found_nan)
      else vectorNormCore vec max_e

/-- One coordinate of the loop of `math_hypot_impl`, mathmodule.c:2084-2093. -/
def hypotStep (s : List F64 × F64 × Bool) (item : Arg) : Py (List F64 × F64 × Bool) := do
  let (coords, max, found_nan) := s
  let x := F64.abs (← assignDouble item)
  return (coords ++ [x], if F64.lt max x then x else max, found_nan || x.isNaN)

/-- `math_hypot_impl`, mathmodule.c:2065-2105. -/
def math_hypot (args : List Arg) : Py F64 := do
  let (coords, max, found_nan) ← args.foldlM hypotStep ([], c0, false)
  return vector_norm 1 coords max found_nan

/-- One coordinate of the loop of `math_dist_impl`, mathmodule.c:2009-2020. -/
def distStep (s : List F64 × F64 × Bool) (pq : Arg × Arg) : Py (List F64 × F64 × Bool) := do
  let (diffs, max, found_nan) := s
  let px ← assignDouble pq.1
  let qx ← assignDouble pq.2
  let x := F64.abs (F64.sub px qx)
  return (diffs ++ [x], if F64.lt max x then x else max, found_nan || x.isNaN)

/-- `math_dist_impl`, mathmodule.c:1965-2044. `PySequence_Tuple` iterates `p`, then `q`
(:1977-1993); a tuple is an `It` that cannot fail. -/
def math_dist (pit qit : It) : Py F64 := do
  let p ← pit.finish pit.items
  let q ← qit.finish qit.items
  if p.length != q.length then
    .error (.valueError "both points must have the same number of dimensions")
  else
    let (diffs, max, found_nan) ← (p.zip q).foldlM distStep ([], c0, false)
    return vector_norm 1 diffs max found_nan

/-! ## `prod`, mathmodule.c:2630-2832 -/

/-- `(long)((unsigned long)a * b)`: the product modulo `2 ** 64`, as a signed value. -/
def wrapLong (v : Int) : Int :=
  let r := v % (2 ^ 64)
  if r < 2 ^ 63 then r else r - 2 ^ 64

/-- `_check_long_mult_overflow`, mathmodule.c:2630-2678. -/
def _check_long_mult_overflow (a b : Int) : Bool :=
  let longprod := wrapLong (a * b)
  let doubleprod := F64.mul (F64.ofInt a) (F64.ofInt b)
  let doubled_longprod := F64.ofInt longprod
  if F64.eq doubled_longprod doubleprod then false
  else
    let diff := F64.sub doubled_longprod doubleprod
    let absdiff := if F64.ge diff c0 then diff else F64.neg diff
    let absprod := if F64.ge doubleprod c0 then doubleprod else F64.neg doubleprod
    if F64.le (F64.mul (F64.ofInt 32) absdiff) absprod then false else true

/-- `PyNumber_Multiply` on the values `prod` handles: `int`, `bool` (an `int`), `float`
(`float_mul`, converting an int with `PyLong_AsDouble`). Other operands raise the
`TypeError` of `binary_op1`; types with their own `__mul__` are out of scope. -/
def pyMul (a b : Ret) : Py Ret :=
  let num : Ret → Option (Sum Int F64)
    | .int n => some (.inl n)
    | .intSub "bool" n => some (.inl n)
    | .float x => some (.inr x)
    | .floatSub _ x => some (.inr x)
    | _ => none
  match num a, num b with
  | some (.inl m), some (.inl n) => .ok (.int (m * n))
  | some (.inr x), some (.inr y) => .ok (.float (F64.mul x y))
  | some (.inr x), some (.inl n) => do return .float (F64.mul x (← PyLong_AsDouble n))
  | some (.inl m), some (.inr y) => do return .float (F64.mul (← PyLong_AsDouble m) y)
  | _, _ => .error (.typeError s!"unsupported operand type(s) for *: '{a.fq}' and '{b.fq}'")

/-- An argument as the object `prod` multiplies. -/
def Arg.toRet : Arg → Ret
  | .float x => .float x
  | .floatSub t x .. => .floatSub t x
  | .int n => .int n
  | .bool b => .intSub "bool" (if b then 1 else 0)
  | .other ty .. => .other ty

/-- The generic loop, mathmodule.c:2814-2829. -/
def prodGeneric (result : Ret) (it : It) (items : List Arg) : Py Ret := do
  let r ← items.foldlM (fun r item => pyMul r item.toRet) result
  it.finish r

/-- The float fast path, mathmodule.c:2768-2810, from item list `items`. -/
def prodFloat (f : F64) (it : It) : List Arg → Py Ret
  | [] => it.finish (.float f)
  | .float x :: rest => prodFloat (F64.mul f x) it rest
  | .int n :: rest =>
    if LONG_MIN ≤ n && n ≤ LONG_MAX then prodFloat (F64.mul f (F64.ofInt n)) it rest
    else do
      let r ← pyMul (.float f) (.int n)
      prodGeneric r it rest
  | item :: rest => do
    let r ← pyMul (.float f) item.toRet
    prodGeneric r it rest

/-- The int fast path, mathmodule.c:2718-2762. -/
def prodInt (i : Int) (it : It) : List Arg → Py Ret
  | [] => it.finish (.int i)
  | item :: rest =>
    let fast : Option Int :=
      match item with
      | .int b =>
        if LONG_MIN ≤ b && b ≤ LONG_MAX && !_check_long_mult_overflow i b then some (i * b)
        else none
      | _ => none
    match fast with
    | some x => prodInt (wrapLong x) it rest
    | none => do
      let r ← pyMul (.int i) item.toRet
      match r with
      | .float f => prodFloat f it rest
      | r => prodGeneric r it rest

/-- `math_prod_impl`, mathmodule.c:2697-2832. `start = none` is the default `1`. -/
def math_prod (it : It) (start : Option Arg) : Py Ret :=
  let result : Ret := match start with | some s => s.toRet | none => .int 1
  match result with
  | .int i => if LONG_MIN ≤ i && i ≤ LONG_MAX then prodInt i it it.items
              else prodGeneric result it it.items
  | .float f => prodFloat f it it.items
  | r => prodGeneric r it it.items

end PyLean.MathInt
