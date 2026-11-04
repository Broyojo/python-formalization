import PyLean.LongObj.Pow

/-!
The registry statements for the arithmetic kernels of `Objects/longobject.c`.

Hypotheses are of two kinds, each stated in the docstring: `IsDigits`/`Normal`, which
are type invariants of a `PyLongObject`, and bounds against `MAX_LONG_DIGITS`
(`Sized`, `DivSized`), which say the allocation `long_alloc` is asked for exists. No
statement assumes the absence of carries: `chk32`, `chk64` and `chkS64` are in the
models, and `= .ok` proves none of them fired.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt

/-- `long_alloc` refuses exactly the sizes above `MAX_LONG_DIGITS`. -/
def LongAllocLimit : Prop :=
  ∀ n, (n ≤ maxLongDigits → longAlloc n = .ok ()) ∧
    (maxLongDigits < n → longAlloc n = .error (.overflowError "too many digits in integer"))

theorem longAllocLimit_proven : LongAllocLimit := fun n =>
  ⟨longAlloc_ok, fun h => by simp [longAlloc, h]⟩

/-- `long_normalize` keeps the value and leaves a non-zero top digit, by cutting the
vector to a prefix (it only lowers the size, longobject.c:131-136), so digits stay
digits. Type invariant: none; it holds of any list. -/
def NormalizeSpec : Prop :=
  ∀ l, val (normalize l) = val l ∧ Normal (normalize l) ∧ (normalize l).length ≤ l.length ∧
    normalize l <+: l ∧ (IsDigits l → IsDigits (normalize l))

theorem normalizeSpec_proven : NormalizeSpec := fun l =>
  ⟨val_normalize l, normal_normalize l, length_normalize_le l, List.take_prefix _ _,
    isDigits_normalize⟩

/-- The constructors of a small object build the canonical object for all of
`stwodigits`: small, medium and three-digit values; and `is_medium_int`'s unsigned
wraparound test (longobject.c:53-58) holds exactly when `|x| < 2**30`, i.e. when the
value fits one digit. The range is the type `int64_t`. -/
def FromSTwoDigitsCanonical : Prop :=
  ∀ x : Int, -(2 ^ 63 : Int) ≤ x → x < 2 ^ 63 →
    fromSTwoDigits x = Long.ofInt x ∧ isMediumInt x = decide (x.natAbs < 2 ^ 30)

theorem fromSTwoDigitsCanonical_proven : FromSTwoDigitsCanonical := fun _ h1 h2 =>
  ⟨fromSTwoDigits_eq h1 h2, by
    rw [isMediumInt_iff h1 h2]
    apply decide_eq_decide.2
    simp only [MASK]
    omega⟩

/-- `x_add` is exact on all digit vectors and its `digit` carry never wraps.
Hypotheses: digit vectors (type invariant) and room for one more digit. -/
def XAddExact : Prop :=
  ∀ a b, IsDigits a → IsDigits b → max a.length b.length + 1 ≤ maxLongDigits →
    xAdd a b = .ok (digitsOf (val a + val b))

theorem xAddExact_proven : XAddExact := fun _ _ h1 h2 h3 => xAdd_spec h1 h2 h3

/-- `x_sub` on normalized magnitudes gives the canonical signed difference, including
the digit scan on equal sizes. Hypotheses: `IsDigits`, `Normal` (type invariants of its
operands) and the allocation bound on existing objects. -/
def XSubExact : Prop :=
  ∀ a b, IsDigits a → IsDigits b → Normal a → Normal b → a.length ≤ maxLongDigits →
    b.length ≤ maxLongDigits → xSub a b = .ok (Long.ofInt ((val a : Int) - val b))

theorem xSubExact_proven : XSubExact := fun _ _ h1 h2 h3 h4 h5 h6 => xSub_spec h1 h2 h3 h4 h5 h6

/-- `a + b` and `a - b` return the canonical object, on the compact path and through
`x_add`/`x_sub`, for all operands with room for one more digit. -/
def LongAddSubExact : Prop :=
  ∀ a b : Int, Sized a → Sized b →
    longAdd (.ofInt a) (.ofInt b) = .ok (.ofInt (a + b)) ∧
    longSub (.ofInt a) (.ofInt b) = .ok (.ofInt (a - b))

theorem longAddSubExact_proven : LongAddSubExact := fun a b h1 h2 =>
  ⟨longAdd_spec a b h1 h2, longSub_spec a b h1 h2⟩

/-- The functions behind the specialized `BINARY_OP_{ADD,SUBTRACT,MULTIPLY}_INT`. On compact
ints they give the canonical object of the exact result when that result is medium, and
otherwise decline (`none`, `PyStackRef_NULL`, never an exception) so the generic path
takes over. Compact operands are their only precondition (`assert`ed in the C). -/
def CompactOpsExact : Prop :=
  ∀ a b : Int, a.natAbs < 2 ^ 30 → b.natAbs < 2 ^ 30 →
    compactAdd (.ofInt a) (.ofInt b) =
      (if (a + b).natAbs < 2 ^ 30 then some (.ofInt (a + b)) else none) ∧
    compactSub (.ofInt a) (.ofInt b) =
      (if (a - b).natAbs < 2 ^ 30 then some (.ofInt (a - b)) else none) ∧
    compactMul (.ofInt a) (.ofInt b) =
      (if (a * b).natAbs < 2 ^ 30 then some (.ofInt (a * b)) else none)

theorem compactOpsExact_proven : CompactOpsExact := by
  intro a b ha hb
  have ea := Long.medium_ofInt ha
  have eb := Long.medium_ofInt hb
  refine ⟨?_, ?_, ?_⟩
  · simp only [compactAdd, ea, eb]
    exact mediumFromSTwoDigits_eq (by omega) (by omega)
  · simp only [compactSub, ea, eb]
    exact mediumFromSTwoDigits_eq (by omega) (by omega)
  · simp only [compactMul, ea, eb]
    have h := Int.natAbs_mul a b
    have hlt : a.natAbs * b.natAbs < 2 ^ 30 * 2 ^ 30 := Nat.mul_lt_mul'' ha hb
    exact mediumFromSTwoDigits_eq (by omega) (by omega)

/-- `v_iadd` and `v_isub`: for `len y <= len x`, carries and borrows propagate as far as
the top of `x`, and the value is exact modulo the width of `x`. -/
def VectorAddSub : Prop :=
  ∀ x y : List Nat, IsDigits x → IsDigits y → y.length ≤ x.length →
    (∃ r c, vIAdd x y = .ok (r, c) ∧ IsDigits r ∧ r.length = x.length ∧ c ≤ 1 ∧
      val r + 2 ^ (30 * x.length) * c = val x + val y) ∧
    (IsDigits (vISub x y).1 ∧ (vISub x y).2 ≤ 1 ∧ (vISub x y).1.length = x.length ∧
      val (vISub x y).1 + val y = val x + 2 ^ (30 * x.length) * (vISub x y).2)

theorem vectorAddSub_proven : VectorAddSub := fun x y h1 h2 h3 => by
  obtain ⟨r, c, a1, a2, a3, a4, a5⟩ := vIAddGo_spec x y 0 h1 h2 h3 (by omega)
  obtain ⟨b1, b2, b3, b4⟩ := vISubGo_spec x y 0 h1 h2 h3 (by omega)
  exact ⟨⟨r, c, a1, a2, a3, a4, by simpa using a5⟩, b1, b2, b3, by simpa [vISub] using b4⟩

/-- `x_mul` is exact for all digit vectors, on the gradeschool path and on the squaring
path taken when both operands are one object, with no `twodigits` overflow and no store
outside `z`. Hypotheses: digit vectors, `same` only for equal operands, the allocation. -/
def XMulExact : Prop :=
  ∀ (same : Bool) (a b : List Nat), IsDigits a → IsDigits b → (same = true → a = b) →
    a.length + b.length ≤ maxLongDigits → xMul same a b = .ok (digitsOf (val a * val b))

theorem xMulExact_proven : XMulExact := fun _ _ _ h1 h2 h3 h4 => xMul_spec h1 h2 h3 h4

/-- `k_mul`, with `k_lopsided_mul` and `kmul_split`, is exact for all digit vectors
including non-normalized slices, with every store inside `ret`: this is the claim of
the "(*)" comment at longobject.c:4233-4276. -/
def KMulExact : Prop :=
  ∀ (same : Bool) (a b : List Nat), IsDigits a → IsDigits b → (same = true → a = b) →
    a.length + b.length + 2 ≤ maxLongDigits → kMul same a b = .ok (digitsOf (val a * val b))

theorem kMulExact_proven : KMulExact := fun _ _ _ h1 h2 h3 h4 => kMul_spec h1 h2 h3 h4

/-- `a * b` returns the canonical object on the compact path and through `k_mul`, for
`x * y` and for `x * x` on one object. -/
def LongMulExact : Prop :=
  ∀ (same : Bool) (a b : Int), (same = true → a = b) →
    digitCount a.natAbs + digitCount b.natAbs + 2 ≤ maxLongDigits →
    longMul same (.ofInt a) (.ofInt b) = .ok (.ofInt (a * b))

theorem longMulExact_proven : LongMulExact := fun s a b h1 h2 => longMul_spec s a b h1 h2

/-- `v_lshift` and `v_rshift` by `d < PyLong_SHIFT` are exact and return the bits
shifted out. -/
def VectorShifts : Prop :=
  ∀ (d : Nat) (a : List Nat), d < 30 → IsDigits a →
    (IsDigits (vLshiftGo d a 0).1 ∧ (vLshiftGo d a 0).2 < 2 ^ d ∧
      val (vLshiftGo d a 0).1 + 2 ^ (30 * a.length) * (vLshiftGo d a 0).2 = val a * 2 ^ d) ∧
    (IsDigits (vRshiftGo d a).1 ∧ (vRshiftGo d a).2 < 2 ^ d ∧
      val (vRshiftGo d a).1 * 2 ^ d + (vRshiftGo d a).2 = val a)

theorem vectorShifts_proven : VectorShifts := fun d a hd ha => by
  obtain ⟨h1, _, h3, h4⟩ := vLshiftGo_spec hd a 0 ha (Nat.two_pow_pos d)
  obtain ⟨g1, _, g3, g4⟩ := vRshiftGo_spec hd a ha
  exact ⟨⟨h1, h3, by simpa using h4⟩, g1, g3, g4⟩

/-- `inplace_divrem1`, `divrem1`, `inplace_rem1`: division by a non-zero digit. -/
def DivremOneDigit : Prop :=
  ∀ (a : List Nat) (n : Nat), IsDigits a → 0 < n → n < 2 ^ 30 → a.length ≤ maxLongDigits →
    divrem1 a n = .ok (digitsOf (val a / n), val a % n) ∧ inplaceRem1 n a = val a % n

theorem divremOneDigit_proven : DivremOneDigit := fun a n h1 h2 h3 h4 => by
  refine ⟨divrem1_exact h1 h2 h3 h4, ?_⟩
  rw [inplaceRem1_eq h2 h3 a h1]
  obtain ⟨_, _, g3, g4⟩ := inplaceDivrem1_spec h2 h3 a h1
  generalize inplaceDivrem1 n a = p at *
  obtain ⟨q, r⟩ := p
  simp only at g3 g4 ⊢
  exact ((Nat.div_mod_unique h2 (a := val a) (c := r) (d := val q)).2 ⟨by omega, g3⟩).2.symm

/-- One digit of Algorithm D: for a normalized divisor and `V < BASE * W`, `q`, `r` are
the true quotient digit and remainder, whatever the estimate did. -/
def KnuthDigit : Prop :=
  ∀ (wl vk : List Nat) (wm1 wm2 : Nat), IsDigits (wl ++ [wm2, wm1]) → 2 ^ 29 ≤ wm1 →
    IsDigits vk → vk.length = wl.length + 3 → val vk < 2 ^ 30 * val (wl ++ [wm2, wm1]) →
    ∃ q r, divStep (wl ++ [wm2, wm1]) wm1 wm2 vk = .ok (q, r) ∧ q < 2 ^ 30 ∧ IsDigits r ∧
      val r < val (wl ++ [wm2, wm1]) ∧ val vk = q * val (wl ++ [wm2, wm1]) + val r

theorem knuthDigit_proven : KnuthDigit := fun _ _ _ _ h1 h2 h3 h4 h5 => by
  obtain ⟨q, r, a1, a2, a3, _, a5, a6⟩ := divStep_spec h1 h2 h3 h4 h5
  exact ⟨q, r, a1, a2, a3, a5, a6⟩

/-- `x_divrem` returns `v // w` and `v % w`. Hypotheses: the function's own stated
precondition `2 <= size(w) <= size(v)` (longobject.c:3320-3321), digit vectors, a
normalized divisor, and room for the work copy. -/
def XDivremExact : Prop :=
  ∀ v w : List Nat, IsDigits v → IsDigits w → Normal w → 2 ≤ w.length → w.length ≤ v.length →
    v.length + 1 ≤ maxLongDigits →
    xDivrem v w = .ok (digitsOf (val v / val w), digitsOf (val v % val w))

theorem xDivremExact_proven : XDivremExact := fun _ _ h1 h2 h3 h4 h5 h6 =>
  xDivrem_spec h1 h2 h3 h4 h5 h6

/-- `long_divrem` and `long_rem` truncate, and raise `ZeroDivisionError` on zero. -/
def LongDivremExact : Prop :=
  ∀ a b : Int, digitCount a.natAbs + 1 ≤ maxLongDigits →
    (b = 0 → longDivrem (.ofInt a) (.ofInt b) = .error (.zeroDivisionError "division by zero") ∧
      longRem (.ofInt a) (.ofInt b) = .error (.zeroDivisionError "division by zero")) ∧
    (b ≠ 0 → longDivrem (.ofInt a) (.ofInt b) = .ok (.ofInt (a.tdiv b), .ofInt (a.tmod b)) ∧
      longRem (.ofInt a) (.ofInt b) = .ok (.ofInt (a.tmod b)))

theorem longDivremExact_proven : LongDivremExact := fun a b hs =>
  ⟨fun h => by subst h; simp [longDivrem, longRem, Long.ofInt],
   fun h => ⟨longDivrem_spec a b h hs, longRem_spec a b h hs⟩⟩

/-- The digit-level `l_divmod` returns the objects of `MathInt.divmod`, which took
`long_divrem` as exact; so that assumption of `mathint-divmod-floor` is discharged. -/
def LDivmodRefines : Prop :=
  ∀ v w : Int, DivSized v w → lDivmod (.ofInt v) (.ofInt w) = ofPair (divmod v w)

theorem lDivmodRefines_proven : LDivmodRefines := lDivmod_eq

/-- `divmod`, `//` and `%` satisfy Python's defining relation on the digit model, and
`%` through `l_mod` (which never uses `_pylong`) agrees with it. -/
def DivisionFloor : Prop :=
  ∀ v w : Int, DivSized v w → w ≠ 0 →
    (∃ q r, longDivmod (.ofInt v) (.ofInt w) = .ok (.ofInt q, .ofInt r) ∧ IsFloorDivmod v w q r) ∧
    (∃ q r, longDiv (.ofInt v) (.ofInt w) = .ok (.ofInt q) ∧ IsFloorDivmod v w q r) ∧
    (∃ q r, longMod (.ofInt v) (.ofInt w) = .ok (.ofInt r) ∧ IsFloorDivmod v w q r)

theorem divisionFloor_proven : DivisionFloor := fun v w hs hw =>
  ⟨lDivmod_floor v w hs hw, longDiv_floor v w hs hw, lMod_floor v w hs hw⟩

/-- `a >> b` is the floor shift for every `b >= 0`, including `b >= 2**63`, and raises
`ValueError` for `b < 0`. Hypothesis: `a` is an object (its digit count is at most
`MAX_LONG_DIGITS`). -/
def RshiftExact : Prop :=
  ∀ a b : Int, digitCount a.natAbs ≤ maxLongDigits →
    longRshift (.ofInt a) (.ofInt b) =
      if b < 0 then .error (.valueError "negative shift count")
      else .ok (.ofInt (a / 2 ^ b.toNat))

theorem rshiftExact_proven : RshiftExact := fun a b h => longRshift_spec a b h

/-- `a << b` raises `ValueError` for `b < 0`, is `0` for `a == 0`, raises
`OverflowError` for `a != 0` when `b` does not fit `int64_t`; below `2**63` it is
`a * 2**b` exactly when `long_alloc` accepts the size `long_lshift1` asks for, and
`OverflowError('too many digits in integer')` otherwise (for example `1 << (2**63 - 1)`).
The same holds of `long_lshift_int64` and `_PyLong_Lshift` for every count. A
MemoryError where the size is accepted but the memory is not available is outside the
model. -/
def LshiftExact : Prop :=
  ∀ a b : Int,
    (b < 0 → longLshift (.ofInt a) (.ofInt b) = .error (.valueError "negative shift count")) ∧
    (0 ≤ b → a = 0 → longLshift (.ofInt a) (.ofInt b) = .ok (.ofInt 0)) ∧
    (a ≠ 0 → (2 : Int) ^ 63 ≤ b → longLshift (.ofInt a) (.ofInt b) =
      .error (.overflowError "too many digits in integer")) ∧
    (0 ≤ b → b < 2 ^ 63 → a ≠ 0 → longLshift (.ofInt a) (.ofInt b) =
      if lshiftNeed a b.toNat ≤ maxLongDigits then .ok (.ofInt (a * 2 ^ b.toNat))
      else .error (.overflowError "too many digits in integer")) ∧
    (∀ s : Nat, longLshiftInt64 (.ofInt a) s =
      if a = 0 then .ok (.ofInt 0)
      else if lshiftNeed a s ≤ maxLongDigits then .ok (.ofInt (a * 2 ^ s))
      else .error (.overflowError "too many digits in integer"))

theorem lshiftExact_proven : LshiftExact := fun a b =>
  ⟨(longLshift_spec a b).1, (longLshift_spec a b).2.1, (longLshift_spec a b).2.2.1,
    fun hb hb2 ha => by rw [longLshift_int64 a b hb hb2, longLshiftInt64_spec, if_neg ha],
    longLshiftInt64_spec a⟩

/-- `v_complement` on a non-zero vector is the two's complement, with no carry out. -/
def VComplementExact : Prop :=
  ∀ a : List Nat, IsDigits a → val a ≠ 0 →
    ∃ z, vComplGo a 1 = .ok (z, 0) ∧ IsDigits z ∧ z.length = a.length ∧
      val z + val a = 2 ^ (30 * a.length)

theorem vComplementExact_proven : VComplementExact := fun _ h1 h2 => vCompl_nonzero h1 h2

/-- `&`, `|`, `^` act bit by bit on the infinite two's complement expansions, for all
ints, on the compact path and on `long_bitwise`; the result is canonical. -/
def BitwiseBits : Prop :=
  ∀ (op : BitOp) (a b : Int), digitCount a.natAbs + 1 ≤ maxLongDigits →
    digitCount b.natAbs + 1 ≤ maxLongDigits →
    ∃ r, longBit op (.ofInt a) (.ofInt b) = .ok (.ofInt r) ∧
      ∀ i, bitZ r i = op.bool (bitZ a i) (bitZ b i)

theorem bitwiseBits_proven : BitwiseBits := fun op a b h1 h2 => longBit_spec op a b h1 h2

/-- `~a == -a - 1`, `-a`, `abs(a)` and `bool(a)` return the canonical results. -/
def UnaryExact : Prop :=
  ∀ a : Int, digitCount a.natAbs + 1 ≤ maxLongDigits →
    longInvert (.ofInt a) = .ok (.ofInt (-a - 1)) ∧ longNeg (.ofInt a) = .ofInt (-a) ∧
    longAbs (.ofInt a) = .ofInt (a.natAbs : Int) ∧ longBool (.ofInt a) = decide (a ≠ 0)

theorem unaryExact_proven : UnaryExact := fun a h =>
  ⟨longInvert_spec a h, longNeg_spec a, longAbs_spec a, longBool_spec a⟩

/-- `a ** e` for `e >= 0` is exact on the small-exponent, binary and window paths. -/
def PowExact : Prop :=
  ∀ a e : Int, 0 ≤ e → longPowNone a e = some (a ^ e.toNat)

theorem powExact_proven : PowExact := fun a e h => longPowNone_spec a e h

/-- The mirrored loops agree with `MathInt.powMod` for all arguments, so the assumption
of `mathint-pow-neg-exp-inverse` that they compute `a**e % c` is discharged. -/
def PowModRefines : Prop := ∀ v w x : Int, longPowMod v w x = powMod v w x

theorem powModRefines_proven : PowModRefines := longPowMod_eq

/-- `pow(v, w, x)` for `w >= 0`, `x != 0` is the Python remainder of `v**w` by `x`, with
`x`'s sign, on all three paths. -/
def PowModFloor : Prop :=
  ∀ v w x : Int, 0 ≤ w → x ≠ 0 → ∃ q r, longPowMod v w x = .ok r ∧ IsFloorDivmod (v ^ w.toNat) x q r

theorem powModFloor_proven : PowModFloor := fun v w x h1 h2 => longPowMod_floor v w x h1 h2

end PyLean.LongObj
