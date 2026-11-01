import PyLean.LongObj.Pow

/-!
Conversions between `int` and C types, and the value functions that read digits
directly: `PyLong_From*`, `PyLong_As*`, the sign predicates, `_PyLong_NumBits`,
`long_hash`, `bit_length` and `bit_count`, longobject.c.

The accumulation loops are mirrored with `uint64_t` wraparound, so that the
`(x >> SHIFT) != prev` test is what detects overflow, as in the C.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt

/-! ## From C integers -/

/-- `PYLONG_FROM_INT(UINT_TYPE, INT_TYPE, ival)`, longobject.c:336-367, for a 32 or
64 bit type. -/
def fromCInt (ival : Int) : Long :=
  if isSmallInt ival then fromSingle ival
  else if -(MASK : Int) ≤ ival ∧ ival ≤ MASK then fromSingle ival
  else ⟨decide (ival < 0), digitLoop 3 ival.natAbs⟩

/-- `PYLONG_FROM_UINT(INT_TYPE, ival)`, longobject.c:378-406. -/
def fromCUInt (ival : Nat) : Long :=
  if (ival : Int) < nSmallPos then fromSingle ival
  else if ival ≤ MASK then fromSingle ival
  else ⟨false, digitLoop 3 ival⟩

theorem fromCInt_spec {x : Int} (h : x.natAbs ≤ 2 ^ 64) : fromCInt x = Long.ofInt x := by
  unfold fromCInt
  by_cases hs : isSmallInt x = true
  · simp only [hs, ite_true]
    apply fromSingle_eq
    simp only [isSmallInt, nSmallNeg, nSmallPos, Bool.and_eq_true] at hs
    have h3 := of_decide_eq_true hs.1
    have h4 := of_decide_eq_true hs.2
    omega
  · simp only [hs, Bool.false_eq_true, ite_false]
    by_cases hm : -(MASK : Int) ≤ x ∧ x ≤ MASK
    · rw [if_pos hm]
      apply fromSingle_eq
      simp only [MASK] at hm
      omega
    · rw [if_neg hm]
      simp only [Long.ofInt, Long.mk.injEq, true_and]
      exact digitLoop_eq 3 _ (by omega)

theorem fromCUInt_spec {x : Nat} (h : x ≤ 2 ^ 64) : fromCUInt x = Long.ofInt x := by
  unfold fromCUInt
  have hs := fromSingle_eq (x := (x : Int))
  rw [Int.natAbs_natCast] at hs
  by_cases h1 : (x : Int) < nSmallPos
  · rw [if_pos h1]
    exact hs (by simp only [nSmallPos] at h1; omega)
  · rw [if_neg h1]
    by_cases h2 : x ≤ MASK
    · rw [if_pos h2]
      exact hs (by simp only [MASK] at h2; omega)
    · rw [if_neg h2, Long.ofInt_natCast, digitLoop_eq 3 _ (by omega)]

/-! ## Accumulating digits, top first -/

/-- `x = (x << SHIFT) | digit; if ((x >> SHIFT) != prev) overflow;`, longobject.c:560-567
and its copies, on `uint64_t`. `ds` runs from the top digit down. -/
def accumLoop : List Nat → Nat → Option Nat
  | [], x => some x
  | d :: ds, x =>
    let x' := u64 ((x <<< 30) ||| d)
    if x' >>> 30 ≠ x then none else accumLoop ds x'

/-- The same loop with no check, longobject.c:794-796 and :1619-1621. -/
def maskLoop : List Nat → Nat → Nat
  | [], x => x
  | d :: ds, x => maskLoop ds (u64 ((x <<< 30) ||| d))

/-- The exact value of the digits accumulated so far. -/
def foldB (ds : List Nat) (x : Nat) : Nat := ds.foldl (fun x d => x * 2 ^ 30 + d) x

theorem foldB_cons (d : Nat) (ds : List Nat) (x : Nat) :
    foldB (d :: ds) x = foldB ds (x * 2 ^ 30 + d) := Eq.trans rfl rfl

theorem foldB_ge : ∀ (ds : List Nat) (x : Nat), x ≤ foldB ds x
  | [], _ => Nat.le_refl _
  | d :: ds, x => by
    rw [foldB_cons]
    have := foldB_ge ds (x * 2 ^ 30 + d)
    omega

theorem foldB_mod {M : Nat} : ∀ (ds : List Nat) (x : Nat), foldB ds (x % M) % M = foldB ds x % M
  | [], _ => Nat.mod_mod _ _
  | d :: ds, x => by
    rw [foldB_cons, foldB_cons, ← foldB_mod ds ((x % M) * 2 ^ 30 + d),
      ← foldB_mod ds (x * 2 ^ 30 + d)]
    have : ((x % M) * 2 ^ 30 + d) % M = (x * 2 ^ 30 + d) % M := by
      simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
    rw [this]

theorem accumLoop_spec : ∀ (ds : List Nat) (x : Nat), IsDigits ds → x < 2 ^ 64 →
    accumLoop ds x = if foldB ds x < 2 ^ 64 then some (foldB ds x) else none
  | [], x, _, hx => by simp [accumLoop, foldB, hx]
  | d :: ds, x, hd, hx => by
    have ⟨h1, h2⟩ := isDigits_cons.1 hd
    have hor : (x <<< 30) ||| d = x * 2 ^ 30 + d := shl_or x d 30 h1
    simp only [accumLoop, hor, u64, foldB_cons]
    by_cases hfit : x * 2 ^ 30 + d < 2 ^ 64
    · rw [Nat.mod_eq_of_lt hfit]
      have hs : (x * 2 ^ 30 + d) >>> 30 = x := by rw [shr30]; omega
      simp only [hs, ne_eq, not_true_eq_false, ite_false]
      exact accumLoop_spec ds _ h2 hfit
    · have hge := foldB_ge ds (x * 2 ^ 30 + d)
      have hne : ((x * 2 ^ 30 + d) % 2 ^ 64) >>> 30 ≠ x := by rw [shr30]; omega
      have hnf : ¬ foldB ds (x * 2 ^ 30 + d) < 2 ^ 64 := by omega
      rw [if_pos hne, if_neg hnf]

theorem maskLoop_spec : ∀ (ds : List Nat) (x : Nat), IsDigits ds → x < 2 ^ 64 →
    maskLoop ds x = foldB ds x % 2 ^ 64
  | [], x, _, hx => by simp [maskLoop, foldB, Nat.mod_eq_of_lt hx]
  | d :: ds, x, hd, _ => by
    have ⟨h1, h2⟩ := isDigits_cons.1 hd
    have hor : (x <<< 30) ||| d = x * 2 ^ 30 + d := shl_or x d 30 h1
    simp only [maskLoop, hor, u64, foldB_cons]
    rw [maskLoop_spec ds _ h2 (Nat.mod_lt _ (by decide)), foldB_mod]

/-- The digits of a magnitude, top first, accumulate to its value. -/
theorem foldB_rev (V : Nat) : foldB (digitsOf V).reverse 0 = V := by
  unfold foldB
  rw [fold_val, val_digitsOf]

/-- `accumLoop` on the digits of `V`. -/
theorem accum_digits (V : Nat) :
    accumLoop (digitsOf V).reverse 0 = if V < 2 ^ 64 then some V else none := by
  have hd : IsDigits (digitsOf V).reverse := by
    intro x hx
    exact digitsOf_digits V x (List.mem_reverse.1 hx)
  rw [accumLoop_spec _ _ hd (by decide), foldB_rev]

/-! ## `long`, `Py_ssize_t` -/

/-- `PyLong_AsLongAndOverflow(vv, &overflow)`, longobject.c:512-587, for an exact int. -/
def asLongAndOverflow (v : Long) : Int × Int :=
  if v.isCompact = true then (v.medium, 0)
  else
    let sign : Int := if v.neg then -1 else 1
    match accumLoop v.ds.reverse 0 with
    | none => (-1, sign)
    | some x =>
      if x ≤ 2 ^ 63 - 1 then ((x : Int) * sign, 0)
      else if sign < 0 ∧ x = 2 ^ 63 then (-(2 ^ 63), 0)
      else (-1, sign)

/-- `PyLong_AsLong(obj)`, longobject.c:593-604. -/
def asLong (v : Long) : Py Int :=
  let (r, o) := asLongAndOverflow v
  if o ≠ 0 then .error (.overflowError "Python int too large to convert to C long") else .ok r

/-- `PyLong_AsInt(obj)`, longobject.c:610-622. -/
def asCInt (v : Long) : Py Int :=
  let (r, o) := asLongAndOverflow v
  if o ≠ 0 ∨ r > 2 ^ 31 - 1 ∨ r < -(2 ^ 31) then
    .error (.overflowError "Python int too large to convert to C int")
  else .ok r

/-- `PyLong_AsSsize_t(vv)`, longobject.c:628-671. -/
def asSsize (v : Long) : Py Int :=
  let overflow : Py Int := .error (.overflowError "Python int too large to convert to C ssize_t")
  if v.isCompact = true then .ok v.medium
  else
    let sign : Int := if v.neg then -1 else 1
    match accumLoop v.ds.reverse 0 with
    | none => overflow
    | some x =>
      if x ≤ 2 ^ 63 - 1 then .ok ((x : Int) * sign)
      else if sign < 0 ∧ x = 2 ^ 63 then .ok (-(2 ^ 63))
      else overflow

/-- `PyLong_AsUnsignedLong(vv)`, longobject.c:677-725, for an exact int. -/
def asUnsignedLong (v : Long) : Py Nat :=
  if !v.neg && v.isCompact then .ok v.medium.toNat
  else if v.neg then .error (.overflowError "can't convert negative value to unsigned int")
  else
    match accumLoop v.ds.reverse 0 with
    | none => .error (.overflowError "Python int too large to convert to C unsigned long")
    | some x => .ok x

/-- `PyLong_AsSize_t(vv)`, longobject.c:731-767, for an exact int. -/
def asSizeT (v : Long) : Py Nat :=
  if !v.neg && v.isCompact then .ok v.medium.toNat
  else if v.neg then .error (.overflowError "can't convert negative value to size_t")
  else
    match accumLoop v.ds.reverse 0 with
    | none => .error (.overflowError "Python int too large to convert to C size_t")
    | some x => .ok x

/-- `_PyLong_AsUnsignedLongMask(vv)`, longobject.c:773-798, and its `long long` twin,
:1597-1623, identical on a 64-bit build: `x * sign` on `unsigned long`. -/
def asUnsignedMask (v : Long) : Nat :=
  if v.isCompact = true then (v.medium % 2 ^ 64).toNat
  else
    let sign : Int := if v.neg then -1 else 1
    (((maskLoop v.ds.reverse 0 : Nat) * sign) % 2 ^ 64).toNat

/-- `PyLong_AsLongLongAndOverflow(vv, &overflow)`, longobject.c:1660-1735. It adds the
digit where `PyLong_AsLongAndOverflow` ors it; `x << SHIFT` has zero low bits, so
this is the same `accumLoop`. -/
def asLongLongAndOverflow (v : Long) : Int × Int := asLongAndOverflow v

theorem compact_iff (a : Int) : (Long.ofInt a).isCompact = true ↔ a.natAbs < 2 ^ 30 := by
  rw [Long.isCompact_ofInt]; simp

theorem asLongAndOverflow_spec (a : Int) :
    asLongAndOverflow (Long.ofInt a) =
      if -(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 63 then (a, 0) else (-1, if a < 0 then -1 else 1) := by
  unfold asLongAndOverflow
  by_cases hc : (Long.ofInt a).isCompact = true
  · simp only [hc, ite_true]
    have h1 := (compact_iff a).1 hc
    rw [Long.medium_ofInt h1, if_pos (by omega)]
  · simp only [hc, Bool.false_eq_true, ite_false]
    have hds : (Long.ofInt a).ds = digitsOf a.natAbs := rfl
    have hneg : (Long.ofInt a).neg = decide (a < 0) := rfl
    simp only [hds, hneg, accum_digits, decide_eq_true_eq]
    by_cases hn : a < 0
    · simp only [hn, ite_true]
      by_cases h1 : a.natAbs < 2 ^ 64
      · simp only [h1, ite_true]
        by_cases h2 : a.natAbs ≤ 2 ^ 63 - 1
        · simp only [h2, ite_true]
          rw [if_pos (by omega)]
          congr 1
          omega
        · simp only [h2, ite_false]
          by_cases h3 : a.natAbs = 2 ^ 63
          · rw [if_pos ⟨by omega, h3⟩, if_pos (by omega)]
            congr 1
            omega
          · rw [if_neg (by omega), if_neg (by omega)]
      · rw [if_neg h1, if_neg (by omega)]
    · simp only [hn, ite_false]
      by_cases h1 : a.natAbs < 2 ^ 64
      · simp only [h1, ite_true]
        by_cases h2 : a.natAbs ≤ 2 ^ 63 - 1
        · simp only [h2, ite_true]
          rw [if_pos (by omega)]
          congr 1
          omega
        · simp only [h2, ite_false]
          rw [if_neg (by omega), if_neg (by omega)]
      · rw [if_neg h1, if_neg (by omega)]

/-- `PyLong_AsLong`: exact on `long`, `OverflowError` outside it. -/
theorem overflow_sign_ne (a : Int) : (if a < 0 then (-1 : Int) else 1) ≠ 0 := by
  split <;> omega

theorem asLong_spec (a : Int) :
    asLong (Long.ofInt a) = if -(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 63 then .ok a
      else .error (.overflowError "Python int too large to convert to C long") := by
  by_cases h : -(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 63
  · have e : asLongAndOverflow (Long.ofInt a) = (a, 0) := by
      rw [asLongAndOverflow_spec, if_pos h]
    simp only [asLong, e]
    rw [if_pos h, if_neg (by omega)]
  · have e : asLongAndOverflow (Long.ofInt a) = (-1, if a < 0 then -1 else 1) := by
      rw [asLongAndOverflow_spec, if_neg h]
    simp only [asLong, e]
    rw [if_neg h, if_pos (overflow_sign_ne a)]

/-- `PyLong_AsInt`: exact on `int`, `OverflowError` outside it. -/
theorem asCInt_spec (a : Int) :
    asCInt (Long.ofInt a) = if -(2 ^ 31 : Int) ≤ a ∧ a < 2 ^ 31 then .ok a
      else .error (.overflowError "Python int too large to convert to C int") := by
  by_cases h : -(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 63
  · have e : asLongAndOverflow (Long.ofInt a) = (a, 0) := by
      rw [asLongAndOverflow_spec, if_pos h]
    simp only [asCInt, e]
    by_cases h2 : -(2 ^ 31 : Int) ≤ a ∧ a < 2 ^ 31
    · rw [if_pos h2, if_neg (by omega)]
    · rw [if_neg h2, if_pos (by omega)]
  · have e : asLongAndOverflow (Long.ofInt a) = (-1, if a < 0 then -1 else 1) := by
      rw [asLongAndOverflow_spec, if_neg h]
    simp only [asCInt, e]
    rw [if_neg (by omega : ¬ (-(2 ^ 31 : Int) ≤ a ∧ a < 2 ^ 31)),
      if_pos (Or.inl (overflow_sign_ne a))]

theorem asSsize_spec (a : Int) :
    asSsize (Long.ofInt a) = if -(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 63 then .ok a
      else .error (.overflowError "Python int too large to convert to C ssize_t") := by
  unfold asSsize
  by_cases hc : (Long.ofInt a).isCompact = true
  · simp only [hc, ite_true]
    have h1 := (compact_iff a).1 hc
    rw [Long.medium_ofInt h1, if_pos (by omega)]
  · simp only [hc, Bool.false_eq_true, ite_false]
    have hds : (Long.ofInt a).ds = digitsOf a.natAbs := rfl
    have hneg : (Long.ofInt a).neg = decide (a < 0) := rfl
    simp only [hds, hneg, accum_digits, decide_eq_true_eq]
    by_cases hn : a < 0
    · simp only [hn, ite_true]
      by_cases h1 : a.natAbs < 2 ^ 64
      · simp only [h1, ite_true]
        by_cases h2 : a.natAbs ≤ 2 ^ 63 - 1
        · simp only [h2, ite_true]
          rw [if_pos (by omega)]
          congr 1
          omega
        · simp only [h2, ite_false]
          by_cases h3 : a.natAbs = 2 ^ 63
          · rw [if_pos ⟨by omega, h3⟩, if_pos (by omega)]
            congr 1
            omega
          · rw [if_neg (by omega), if_neg (by omega)]
      · rw [if_neg h1, if_neg (by omega)]
    · simp only [hn, ite_false]
      by_cases h1 : a.natAbs < 2 ^ 64
      · simp only [h1, ite_true]
        by_cases h2 : a.natAbs ≤ 2 ^ 63 - 1
        · simp only [h2, ite_true]
          rw [if_pos (by omega)]
          congr 1
          omega
        · simp only [h2, ite_false]
          rw [if_neg (by omega), if_neg (by omega)]
      · rw [if_neg h1, if_neg (by omega)]

theorem asUnsigned_common (a : Int) (e1 e2 : PyExc) (f : Long → Py Nat)
    (hf : ∀ v, f v = if (!v.neg && v.isCompact) = true then .ok v.medium.toNat
      else if v.neg = true then .error e1
      else match accumLoop v.ds.reverse 0 with
        | none => .error e2
        | some x => .ok x) :
    f (Long.ofInt a) = if a < 0 then .error e1
      else if a < 2 ^ 64 then .ok a.toNat else .error e2 := by
  rw [hf]
  have hneg : (Long.ofInt a).neg = decide (a < 0) := rfl
  have hds : (Long.ofInt a).ds = digitsOf a.natAbs := rfl
  by_cases hn : a < 0
  · have h0 : (Long.ofInt a).neg = true := by rw [hneg]; exact decide_eq_true hn
    rw [h0]
    simp [hn]
  · have h0 : (Long.ofInt a).neg = false := by rw [hneg]; exact decide_eq_false hn
    rw [h0, if_neg hn]
    by_cases hc : (Long.ofInt a).isCompact = true
    · have h1 := (compact_iff a).1 hc
      simp only [Bool.not_false, Bool.true_and, hc, ite_true]
      rw [Long.medium_ofInt h1, if_pos (by omega)]
    · simp only [Bool.not_false, Bool.true_and, hc, Bool.false_eq_true, ite_false]
      rw [hds, accum_digits]
      have e : a.natAbs = a.toNat := by omega
      by_cases h1 : a.natAbs < 2 ^ 64
      · rw [if_pos h1, if_pos (by omega), e]
      · rw [if_neg h1, if_neg (by omega)]

/-- `PyLong_AsUnsignedLong`: `OverflowError` on negative or too large, exact otherwise. -/
theorem asUnsignedLong_spec (a : Int) :
    asUnsignedLong (Long.ofInt a) =
      if a < 0 then .error (.overflowError "can't convert negative value to unsigned int")
      else if a < 2 ^ 64 then .ok a.toNat
      else .error (.overflowError "Python int too large to convert to C unsigned long") :=
  asUnsigned_common a _ _ asUnsignedLong (fun _ => rfl)

theorem asSizeT_spec (a : Int) :
    asSizeT (Long.ofInt a) =
      if a < 0 then .error (.overflowError "can't convert negative value to size_t")
      else if a < 2 ^ 64 then .ok a.toNat
      else .error (.overflowError "Python int too large to convert to C size_t") :=
  asUnsigned_common a _ _ asSizeT (fun _ => rfl)

/-- The mask conversions are reduction modulo `2**64`, for all ints. -/
theorem asUnsignedMask_spec (a : Int) : asUnsignedMask (Long.ofInt a) = (a % 2 ^ 64).toNat := by
  unfold asUnsignedMask
  by_cases hc : (Long.ofInt a).isCompact = true
  · simp only [hc, ite_true]
    rw [Long.medium_ofInt ((compact_iff a).1 hc)]
  · simp only [hc, Bool.false_eq_true, ite_false]
    have hneg : (Long.ofInt a).neg = decide (a < 0) := rfl
    have hds : (Long.ofInt a).ds = digitsOf a.natAbs := rfl
    have hd : IsDigits (digitsOf a.natAbs).reverse := by
      intro x hx
      exact digitsOf_digits _ x (List.mem_reverse.1 hx)
    rw [hds, hneg, maskLoop_spec _ _ hd (by decide), foldB_rev]
    simp only [decide_eq_true_eq]
    generalize hA : a.natAbs = A at *
    by_cases hn : a < 0
    · simp only [hn, ite_true]
      have : a = -(A : Int) := by omega
      subst this
      congr 1
      omega
    · simp only [hn, ite_false]
      have : a = (A : Int) := by omega
      subst this
      congr 1
      omega

/-! ## Sign predicates and `_PyLong_NumBits` -/

/-- `long_sign(vv)`, longobject.c:858-868, and `_PyLong_Sign`, `PyLong_GetSign`,
:871-886: compact and non-compact branches read the same tag. -/
def longSign (v : Long) : Int :=
  if v.ds = [] then 0 else if v.neg then -1 else 1

/-- `_PyLong_NumBits(vv)`, longobject.c:899-920. -/
def numBits (v : Long) : Nat :=
  let n := v.ds.length
  if n > 0 then (n - 1) * 30 + bitLength (v.ds.getD (n - 1) 0) else 0

theorem longSign_spec (a : Int) :
    longSign (Long.ofInt a) = if a < 0 then -1 else if a = 0 then 0 else 1 := by
  simp only [longSign, Long.ofInt]
  by_cases h : a = 0
  · subst h; simp
  · have hne : digitsOf a.natAbs ≠ [] := by rw [Ne, digitsOf_eq_nil]; omega
    simp only [hne, ite_false, h, decide_eq_true_eq]

theorem numBits_list (neg : Bool) (l : List Nat) (top : Nat) :
    numBits ⟨neg, l ++ [top]⟩ = l.length * 30 + bitLength top := by
  simp [numBits, List.getD]

/-- `int.bit_length()` of an int is the bit length of its magnitude, on the top digit. -/
theorem numBits_spec (a : Int) : numBits (Long.ofInt a) = bitLength a.natAbs := by
  by_cases h : a = 0
  · subst h
    simp [numBits, Long.ofInt, bitLength]
  · have hne : digitsOf a.natAbs ≠ [] := by rw [Ne, digitsOf_eq_nil]; omega
    have hN := normal_digitsOf a.natAbs
    have hd := digitsOf_digits a.natAbs
    have hv := val_digitsOf a.natAbs
    obtain ⟨l, top, hl⟩ : ∃ l t, digitsOf a.natAbs = l ++ [t] :=
      ⟨(digitsOf a.natAbs).dropLast, (digitsOf a.natAbs).getLast hne,
        (List.dropLast_concat_getLast hne).symm⟩
    have h0 : top ≠ 0 := by
      have := hN hne
      simpa [hl] using this
    rw [hl] at hd hv
    have hdl : IsDigits l := (isDigits_append.1 hd).1
    rw [val_append] at hv
    simp only [val_cons, val_nil, Nat.mul_zero, Nat.add_zero] at hv
    have hb := bitLength_add_shift (val l) top (30 * l.length) (val_lt hdl) (by omega)
    have hlong : Long.ofInt a = ⟨decide (a < 0), l ++ [top]⟩ := by
      simp only [Long.ofInt, hl]
    rw [hlong, numBits_list, ← hv, hb]
    omega

/-! ## `long_hash` -/

/-- `_PyHASH_MODULUS`, pyhash.h. -/
def hashModulus : Nat := 2 ^ 61 - 1

/-- One iteration of the loop of `long_hash`, longobject.c:3634-3638. -/
def hashStep (x d : Nat) : Nat :=
  let x := (u64 (x <<< 30) &&& hashModulus) ||| (x >>> (61 - 30))
  let x := x + d
  if x ≥ hashModulus then x - hashModulus else x

/-- `(Py_uhash_t)-1` becomes `-2`, and the result is read as `Py_hash_t`. -/
def hashResult (x : Nat) : Int := s64of (if x = 2 ^ 64 - 1 then 2 ^ 64 - 2 else x)

/-- `long_hash(obj)`, longobject.c:3591-3644. -/
def longHash (v : Long) : Int :=
  if v.isCompact = true then hashResult (v.medium % 2 ^ 64).toNat
  else
    let sign : Int := if v.neg then -1 else 1
    let x := v.ds.reverse.foldl hashStep 0
    hashResult (((x : Int) * sign) % 2 ^ 64).toNat

/-- The specification of `hash(int)`: the magnitude modulo `2**61 - 1`, with the sign,
and `-1` replaced by `-2`. -/
def pyHash (a : Int) : Int :=
  let r : Int := (a.natAbs % hashModulus : Nat)
  let h := if a < 0 then -r else r
  if h = -1 then -2 else h

/-- Rotating by `SHIFT` is multiplication by `2**SHIFT` modulo `2**61 - 1`, the argument
of the comment at longobject.c:3609-3633. -/
theorem hashStep_spec {x d : Nat} (hx : x < hashModulus) (hd : d < 2 ^ 30) :
    hashStep x d = (x * 2 ^ 30 + d) % hashModulus := by
  have hM : hashModulus = 2 ^ 61 - 1 := rfl
  simp only [hashStep]
  have hlo : u64 (x <<< 30) &&& hashModulus = (x % 2 ^ 31) * 2 ^ 30 := by
    rw [hM, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq]
    simp only [u64]
    omega
  have hhi : x >>> (61 - 30) = x / 2 ^ 31 := by
    simp [Nat.shiftRight_eq_div_pow]
  have hlt : x / 2 ^ 31 < 2 ^ 30 := by simp only [hM] at hx; omega
  have hor : ((x % 2 ^ 31) * 2 ^ 30) ||| (x / 2 ^ 31) = (x % 2 ^ 31) * 2 ^ 30 + x / 2 ^ 31 := by
    have := shl_or (x % 2 ^ 31) (x / 2 ^ 31) 30 hlt
    rwa [Nat.shiftLeft_eq] at this
  rw [hlo, hhi, hor, hM]
  simp only [hM] at hx
  split <;> omega

theorem hashFold : ∀ (ds : List Nat) (x : Nat), IsDigits ds → x < hashModulus →
    ds.foldl hashStep x = foldB ds x % hashModulus
  | [], x, _, hx => by simp [foldB, Nat.mod_eq_of_lt hx]
  | d :: ds, x, hd, hx => by
    have ⟨h1, h2⟩ := isDigits_cons.1 hd
    simp only [List.foldl_cons]
    rw [hashStep_spec hx h1, hashFold ds _ h2 (Nat.mod_lt _ (by decide)), foldB_cons, foldB_mod]

/-- `hash(a)` follows the numeric hash rule for every int, on both paths of `long_hash`. -/
theorem longHash_spec (a : Int) : longHash (Long.ofInt a) = pyHash a := by
  have hrange : ∀ h : Int, -(2 ^ 62 : Int) ≤ h → h < 2 ^ 62 →
      hashResult (h % 2 ^ 64).toNat = if h = -1 then -2 else h := by
    intro h h1 h2
    by_cases hm : h = -1
    · subst hm
      decide
    · have hne : (h % 2 ^ 64).toNat ≠ 2 ^ 64 - 1 := by omega
      simp only [hashResult, s64of]
      rw [if_neg hne, if_neg hm]
      split <;> omega
  have hM : hashModulus = 2 ^ 61 - 1 := rfl
  have hlt := Nat.mod_lt a.natAbs (show 0 < hashModulus by decide)
  simp only [pyHash]
  generalize hR : a.natAbs % hashModulus = R at *
  rw [hM] at hlt
  unfold longHash
  by_cases hc : (Long.ofInt a).isCompact = true
  · simp only [hc, ite_true]
    have h1 := (compact_iff a).1 hc
    have hRe : R = a.natAbs := by
      rw [← hR, hM]; exact Nat.mod_eq_of_lt (by omega)
    rw [Long.medium_ofInt h1, hrange a (by omega) (by omega)]
    have e : (if a < 0 then -(R : Int) else R) = a := by
      rw [hRe]; split <;> omega
    rw [e]
  · simp only [hc, Bool.false_eq_true, ite_false]
    have hneg : (Long.ofInt a).neg = decide (a < 0) := rfl
    have hds : (Long.ofInt a).ds = digitsOf a.natAbs := rfl
    have hd : IsDigits (digitsOf a.natAbs).reverse := by
      intro x hx
      exact digitsOf_digits _ x (List.mem_reverse.1 hx)
    rw [hds, hneg, hashFold _ _ hd (by decide), foldB_rev, hR]
    simp only [decide_eq_true_eq]
    by_cases hn : a < 0
    · simp only [hn, ite_true]
      rw [show (R : Int) * -1 = -(R : Int) by omega]
      exact hrange _ (by omega) (by omega)
    · simp only [hn, ite_false]
      rw [show (R : Int) * 1 = (R : Int) by omega]
      exact hrange _ (by omega) (by omega)

/-! ## `int.bit_count` -/

/-- The number of set bits among the low `k` bits of `n`. -/
def popK : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => popK k n + (n.testBit k).toNat

/-- `popcount_digit(d)`, longobject.c:208-214: `_Py_popcount32` on a digit. -/
def popcountDigit (d : Nat) : Nat := popK 30 d

/-- `int.bit_count()`, longobject.c:6230-6245: the sum over the digits. -/
def bitCount (v : Long) : Nat := v.ds.foldl (fun s d => s + popcountDigit d) 0

theorem popK_succ (k n : Nat) : popK (k + 1) n = popK k n + (n.testBit k).toNat :=
  Eq.trans rfl rfl

theorem popK_shift {d m : Nat} (hd : d < 2 ^ 30) : ∀ k, popK (30 + k) (d + 2 ^ 30 * m) =
    popK 30 d + popK k m
  | 0 => by
    have : ∀ j, j ≤ 30 → popK j (d + 2 ^ 30 * m) = popK j d := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
        intro hj
        simp only [popK]
        rw [ih (by omega), testBit_cons hd, if_pos (by omega)]
    simpa [popK] using this 30 (Nat.le_refl _)
  | k + 1 => by
    have := popK_shift (m := m) hd k
    rw [show 30 + (k + 1) = (30 + k) + 1 by omega, popK_succ, popK_succ k m, this, testBit_cons hd,
      if_neg (by omega), show 30 + k - 30 = k by omega, Nat.add_assoc]

theorem bitCount_go : ∀ (ds : List Nat) (s : Nat), IsDigits ds →
    ds.foldl (fun s d => s + popcountDigit d) s = s + popK (30 * ds.length) (val ds)
  | [], s, _ => by simp [popK]
  | d :: ds, s, hd => by
    have ⟨h1, h2⟩ := isDigits_cons.1 hd
    simp only [List.foldl_cons]
    rw [bitCount_go ds _ h2, val_cons, List.length_cons,
      show 30 * (ds.length + 1) = 30 + 30 * ds.length by omega, popK_shift h1, popcountDigit,
      Nat.add_assoc]

/-- `popK` past the top bit changes nothing. -/
theorem popK_full {n : Nat} (j k : Nat) (h : n < 2 ^ k) (hk : k ≤ j) : popK j n = popK k n := by
  induction j with
  | zero => have : k = 0 := by omega
            subst this; rfl
  | succ j ih =>
    by_cases he : k = j + 1
    · subst he; rfl
    · have h2 : n < 2 ^ j := Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega))
      have hb : n.testBit j = false := by
        rw [Nat.testBit_eq_decide_div_mod_eq, Nat.div_eq_of_lt h2]
        decide
      simp only [popK, hb]
      exact ih (by omega)

/-- `int.bit_count()` is the population count of the magnitude, whatever the sign. -/
theorem bitCount_spec (a : Int) : bitCount (Long.ofInt a) = popK (bitLength a.natAbs) a.natAbs := by
  have hd := digitsOf_digits a.natAbs
  simp only [bitCount, Long.ofInt]
  rw [bitCount_go _ _ hd, val_digitsOf, Nat.zero_add, length_digitsOf]
  apply popK_full
  · exact lt_two_pow_bitLength' _
  · simp only [digitCount]; omega

end PyLean.LongObj
