import PyLean.LongObj.AddSub

/-!
`long_compare` and `long_richcompare`, `Objects/longobject.c:3600-3635`, and
`_PyLong_Negate`, :353-368 (CPython 3.15.2), on the `Long` objects of `Digits.lean`.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt

/-! ## `long_compare` -/

/-- `_PyLong_SignedDigitCount(op)`, pycore_long.h:258-264: `(1 - sign bits) * ndigits`. Zero
has no digits, so its count is 0 whatever the flag. -/
def Long.signedDigitCount (x : Long) : Int :=
  if x.neg then -(x.ds.length : Int) else x.ds.length

/-- `while (--i >= 0) { diff = (sdigit) a[i] - (sdigit) b[i]; if (diff) break; }`,
longobject.c:3613-3619, from digit `i - 1` down; `diff` stays 0 when the loop runs
out. Digits are below `2**30`, so the `sdigit` (int32) difference cannot wrap. -/
def cmpDigits (a b : List Nat) : Nat → Int
  | 0 => 0
  | i + 1 =>
    let diff : Int := (a.getD i 0 : Int) - (b.getD i 0 : Int)
    if diff ≠ 0 then diff else cmpDigits a b i

/-- `long_compare(a, b)`, longobject.c:3604-3623: the difference of the compact values
(:3607-3609), otherwise the difference of the signed digit counts (:3610), and on equal
counts the first differing digit from the top, negated for a negative `a`
(:3611-3621). `Py_ssize_t` cannot overflow: compact values are below `2**30` and digit
counts below `MAX_LONG_DIGITS`. -/
def longCompare (a b : Long) : Int :=
  if bothCompact a b then a.medium - b.medium
  else
    let sign := a.signedDigitCount - b.signedDigitCount
    if sign = 0 then
      let diff := cmpDigits a.ds b.ds a.ds.length
      if a.neg then -diff else diff
    else sign

theorem val_take_succ' {a : List Nat} {i : Nat} (hi : i < a.length) :
    val (a.take (i + 1)) = val (a.take i) + 2 ^ (30 * i) * a.getD i 0 := by
  have ea : a.take (i + 1) = a.take i ++ [a[i]] := by simp
  have ga : a.getD i 0 = a[i] := by simp [List.getD, hi]
  rw [ea, val_append, ga, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  simp

theorem cmpDigits_spec {a b : List Nat} (ha : IsDigits a) (hb : IsDigits b) :
    ∀ i, i ≤ a.length → i ≤ b.length →
      (cmpDigits a b i < 0 ↔ val (a.take i) < val (b.take i)) ∧
      (0 < cmpDigits a b i ↔ val (b.take i) < val (a.take i))
  | 0, _, _ => by simp [cmpDigits]
  | i + 1, h1, h2 => by
    have ih := cmpDigits_spec ha hb i (by omega) (by omega)
    rw [val_take_succ' (by omega : i < a.length), val_take_succ' (by omega : i < b.length)]
    have hVa := val_le_of_len (isDigits_take ha i) (n := i) (List.length_take_le i a)
    have hVb := val_le_of_len (isDigits_take hb i) (n := i) (List.length_take_le i b)
    simp only [cmpDigits]
    generalize a.getD i 0 = x
    generalize b.getD i 0 = y
    generalize val (a.take i) = Va at *
    generalize val (b.take i) = Vb at *
    generalize 2 ^ (30 * i) = P at *
    rcases Nat.lt_trichotomy x y with h | h | h
    · have hne : ((x : Int) - (y : Int)) ≠ 0 := by omega
      simp only [hne, ne_eq, not_false_eq_true, ↓reduceIte]
      have := Nat.mul_le_mul_left P (show x + 1 ≤ y by omega)
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
    · subst h
      have hne : ¬ ((x : Int) - (x : Int)) ≠ 0 := by omega
      simp only [hne, ↓reduceIte]
      omega
    · have hne : ((x : Int) - (y : Int)) ≠ 0 := by omega
      simp only [hne, ne_eq, not_false_eq_true, ↓reduceIte]
      have := Nat.mul_le_mul_left P (show y + 1 ≤ x by omega)
      rw [Nat.mul_add, Nat.mul_one] at this
      omega

/-- The sign and digit-count step of `long_compare`, as arithmetic. -/
theorem cmp_arith (x y : Int) (lx ly : Nat) (D : Int)
    (hlt : lx < ly → x.natAbs < y.natAbs) (hgt : ly < lx → y.natAbs < x.natAbs)
    (heq : lx = ly → (D < 0 ↔ x.natAbs < y.natAbs) ∧ (0 < D ↔ y.natAbs < x.natAbs))
    (hx0 : x = 0 ↔ lx = 0) (hy0 : y = 0 ↔ ly = 0) :
    ((if (if x < 0 then -(lx : Int) else lx) - (if y < 0 then -(ly : Int) else ly) = 0 then
        (if x < 0 then -D else D)
      else (if x < 0 then -(lx : Int) else lx) - (if y < 0 then -(ly : Int) else ly)) < 0 ↔ x < y) ∧
    (0 < (if (if x < 0 then -(lx : Int) else lx) - (if y < 0 then -(ly : Int) else ly) = 0 then
        (if x < 0 then -D else D)
      else (if x < 0 then -(lx : Int) else lx) - (if y < 0 then -(ly : Int) else ly)) ↔ y < x) := by
  by_cases hx : x < 0 <;> by_cases hy : y < 0 <;> simp only [hx, hy, ↓reduceIte] <;>
    (repeat' split) <;> omega

/-- The three outcomes of `long_compare` on canonical objects. -/
theorem longCompare_ofInt (x y : Int) :
    (longCompare (.ofInt x) (.ofInt y) < 0 ↔ x < y) ∧
    (0 < longCompare (.ofInt x) (.ofInt y) ↔ y < x) := by
  unfold longCompare
  by_cases hc : bothCompact (.ofInt x) (.ofInt y) = true
  · rw [if_pos hc]
    simp only [bothCompact, Bool.and_eq_true, Long.isCompact_ofInt, decide_eq_true_eq] at hc
    rw [Long.medium_ofInt hc.1, Long.medium_ofInt hc.2]
    omega
  · rw [if_neg hc]
    have dA := digitsOf_digits x.natAbs
    have dB := digitsOf_digits y.natAbs
    have nA := normal_digitsOf x.natAbs
    have nB := normal_digitsOf y.natAbs
    have key := cmp_arith x y (digitsOf x.natAbs).length (digitsOf y.natAbs).length
      (cmpDigits (digitsOf x.natAbs) (digitsOf y.natAbs) (digitsOf x.natAbs).length)
      (fun h => by
        have := val_lt_of_length dA dB nB h
        rwa [val_digitsOf, val_digitsOf] at this)
      (fun h => by
        have := val_lt_of_length dB dA nA h
        rwa [val_digitsOf, val_digitsOf] at this)
      (fun h => by
        have := cmpDigits_spec dA dB (digitsOf x.natAbs).length (Nat.le_refl _) (Nat.le_of_eq h)
        rwa [List.take_of_length_le (Nat.le_refl _), List.take_of_length_le (Nat.le_of_eq h.symm),
          val_digitsOf, val_digitsOf] at this)
      (by rw [List.length_eq_zero_iff, digitsOf_eq_nil]; exact Int.natAbs_eq_zero.symm)
      (by rw [List.length_eq_zero_iff, digitsOf_eq_nil]; exact Int.natAbs_eq_zero.symm)
    have ex : (Long.ofInt x).signedDigitCount =
        if x < 0 then -((digitsOf x.natAbs).length : Int) else (digitsOf x.natAbs).length := by
      simp [Long.signedDigitCount, Long.ofInt]
    have ey : (Long.ofInt y).signedDigitCount =
        if y < 0 then -((digitsOf y.natAbs).length : Int) else (digitsOf y.natAbs).length := by
      simp [Long.signedDigitCount, Long.ofInt]
    have en : ((Long.ofInt x).neg = true) = (x < 0) := by simp [Long.ofInt]
    simp only [ex, ey, en]
    exact key

/-- `long_compare` meets its contract, longobject.c:3600-3602 ("if a < b, return a
negative number; if a == b, return 0; if a > b, return a positive number"), for every
pair of ints of every size, on the compact path and on the digit path. Canonical
objects (`Long.ofInt`: normalized digits below `2**30`) are the type invariant. -/
def LongCompareExact : Prop :=
  ∀ x y : Int,
    (longCompare (.ofInt x) (.ofInt y) < 0 ↔ x < y) ∧
    (longCompare (.ofInt x) (.ofInt y) = 0 ↔ x = y) ∧
    (0 < longCompare (.ofInt x) (.ofInt y) ↔ y < x)

theorem longCompareExact_proven : LongCompareExact := by
  intro x y
  have ⟨h1, h2⟩ := longCompare_ofInt x y
  exact ⟨h1, by omega, h2⟩

/-! ## `long_richcompare` -/

/-- The `op` of `tp_richcompare`: `Py_LT`, `Py_LE`, `Py_EQ`, `Py_NE`, `Py_GT`, `Py_GE`
(Include/object.h). -/
inductive RichOp where
  | lt | le | eq | ne | gt | ge
  deriving DecidableEq, Repr

/-- An operand: an object passing `PyLong_Check` (an `int`, `bool` or other subclass),
with its identity `id`, or any other object. -/
inductive RichArg where
  | int (id : Nat) (x : Long)
  | other (id : Nat)

/-- What `long_richcompare` returns: `NotImplemented`, or `True`/`False`. -/
inductive RichOut where
  | notImplemented
  | bool (b : Bool)
  deriving DecidableEq, Repr

/-- `Py_RETURN_RICHCOMPARE(val1, val2, op)`, Include/object.h:673-685, in its case
order. -/
def returnRichcompare (val1 val2 : Int) : RichOp → Bool
  | .eq => decide (val1 = val2)
  | .ne => decide (val1 ≠ val2)
  | .lt => decide (val1 < val2)
  | .gt => decide (val1 > val2)
  | .le => decide (val1 ≤ val2)
  | .ge => decide (val1 ≥ val2)

/-- `long_richcompare(self, other, op)`, longobject.c:3625-3635: `CHECK_BINOP`
(:1843-1847) returns `NotImplemented` unless both are ints; the same object compares
equal without reading a digit (:3630-3631); otherwise `long_compare` (:3633), then
`Py_RETURN_RICHCOMPARE(result, 0, op)` (:3634). -/
def longRichcompare (self other : RichArg) (op : RichOp) : RichOut :=
  match self, other with
  | .int i a, .int j b =>
    let result : Int := if i = j then 0 else longCompare a b
    .bool (returnRichcompare result 0 op)
  | _, _ => .notImplemented

/-- The six comparisons on integers. -/
def intCmp (op : RichOp) (x y : Int) : Bool :=
  match op with
  | .lt => decide (x < y)
  | .le => decide (x ≤ y)
  | .eq => decide (x = y)
  | .ne => decide (x ≠ y)
  | .gt => decide (y < x)
  | .ge => decide (y ≤ x)

/-- All six rich comparisons of two ints give the comparison of their values, through the
identity shortcut or `long_compare`; any non-int operand on either side gives
`NotImplemented`. The hypothesis `i = j → x = y` says one object has one value (a type
invariant of identity). The shortcut changes no result, so it is mirrored but cannot be
told apart from `long_compare` by any property of results. -/
def LongRichcompareExact : Prop :=
  (∀ (i j : Nat) (x y : Int) (op : RichOp), (i = j → x = y) →
    longRichcompare (.int i (.ofInt x)) (.int j (.ofInt y)) op = .bool (intCmp op x y)) ∧
  (∀ (k : Nat) (b : RichArg) (op : RichOp), longRichcompare (.other k) b op = .notImplemented) ∧
  (∀ (k : Nat) (a : RichArg) (op : RichOp), longRichcompare a (.other k) op = .notImplemented)

theorem longRichcompareExact_proven : LongRichcompareExact := by
  refine ⟨fun i j x y op hid => ?_, fun k b op => by cases b <;> rfl,
    fun k a op => by cases a <;> rfl⟩
  have ⟨c1, c2, c3⟩ := longCompareExact_proven x y
  simp only [longRichcompare]
  by_cases h : i = j
  · have hxy := hid h
    subst hxy
    rw [if_pos h]
    cases op <;> simp [returnRichcompare, intCmp]
  · rw [if_neg h]
    congr 1
    cases op <;> simp only [returnRichcompare, intCmp] <;> apply decide_eq_decide.2 <;> omega

/-! ## `_PyLong_Negate` -/

/-- `_PyLong_Negate(&x)`, longobject.c:355-368. `unique` is
`_PyObject_IsUniquelyReferenced(x)` (:361). A uniquely referenced object has its sign
flipped in place (`_PyLong_FlipSign`, :362); a shared one is left alone and replaced by
`_PyLong_FromSTwoDigits(-medium_value(x))` (:366). The result is the object `*x_p`
points to afterwards, and the old object as it is afterwards (the same object when it was
flipped). -/
def longNegate (unique : Bool) (x : Long) : Long × Long :=
  if unique then (x.flip, x.flip) else (fromSTwoDigits (-x.medium), x)

/-- `_PyLong_Negate` gives the canonical object of `-v`, and never modifies a shared
object: so a cached small int, which is always shared, keeps its value. The precondition
"a shared object is compact" is the comment at :353-354 (a freshly allocated int that is
already shared is a small int); every caller passes a fresh result. -/
def LongNegateExact : Prop :=
  ∀ (unique : Bool) (v : Int), (unique = false → v.natAbs < 2 ^ 30) →
    (longNegate unique (.ofInt v)).1 = .ofInt (-v) ∧
    (unique = false → (longNegate unique (.ofInt v)).2 = .ofInt v)

theorem longNegateExact_proven : LongNegateExact := by
  intro unique v hc
  cases unique with
  | true => exact ⟨by simp [longNegate, Long.ofInt_neg], fun h => by cases h⟩
  | false =>
    have h := hc rfl
    refine ⟨?_, fun _ => rfl⟩
    simp only [longNegate, Bool.false_eq_true, ↓reduceIte, Long.medium_ofInt h]
    exact fromSTwoDigits_eq (by omega) (by omega)

/-- What the callers rely on: on a fresh object, and on a shared compact one, the
result is `Long.flip`, which is how the models of `long_mul`, `long_divrem` and
`long_rem` write the call. -/
theorem longNegate_fst (unique : Bool) (v : Int) (hc : unique = false → v.natAbs < 2 ^ 30) :
    (longNegate unique (.ofInt v)).1 = (Long.ofInt v).flip := by
  rw [(longNegateExact_proven unique v hc).1, Long.ofInt_neg]

end PyLean.LongObj
