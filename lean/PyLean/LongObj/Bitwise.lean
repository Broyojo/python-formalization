import PyLean.LongObj.Shift

/-!
Two's complement on sign-magnitude digits: `v_complement`, `long_bitwise`, `long_and`,
`long_or`, `long_xor`, `long_invert`, `long_neg`, `long_abs`, `long_bool`, longobject.c.

Python's specification treats an `int` as an infinite two's complement bit string.
`bitZ x i` is bit `i` of that string, and `longBit_spec` proves each operator acts bit
by bit, for every pair of ints and on both the compact and the digit paths.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt

/-- Bit `i` of the infinite two's complement expansion of `x`. -/
def bitZ (x : Int) (i : Nat) : Bool := decide ((x / 2 ^ i) % 2 = 1)

/-- A value given by `k` low bits `m` and a sign bit `s` extending upward. -/
theorem bitZ_tc {k m i : Nat} {s : Bool} (hm : m < 2 ^ k) :
    bitZ ((m : Int) - (if s = true then 2 ^ k else 0)) i =
      if i < k then m.testBit i else s := by
  have hpi : (0 : Int) < 2 ^ i := Int.pow_pos (by decide)
  have hdiv : ((m / 2 ^ i : Nat) : Int) = (m : Int) / 2 ^ i := by
    rw [Int.natCast_ediv, cast_two_pow]
  cases s with
  | false =>
    simp only [Bool.false_eq_true, ite_false, Int.sub_zero, bitZ, ← hdiv]
    by_cases h : i < k
    · rw [if_pos h, Nat.testBit_eq_decide_div_mod_eq]
      apply decide_eq_decide.2
      omega
    · rw [if_neg h]
      have h2 : m < 2 ^ i := Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by omega))
      rw [Nat.div_eq_of_lt h2]
      decide
  | true =>
    simp only [ite_true, bitZ]
    by_cases h : i < k
    · rw [if_pos h, Nat.testBit_eq_decide_div_mod_eq]
      apply decide_eq_decide.2
      obtain ⟨j, rfl⟩ : ∃ j, k = i + (j + 1) := ⟨k - i - 1, by omega⟩
      have e : (2 : Int) ^ (i + (j + 1)) = 2 ^ i * (2 * 2 ^ j) := by
        rw [Int.pow_add, Int.pow_succ]
        grind
      rw [e, Int.sub_eq_add_neg, ← Int.mul_neg, Int.add_mul_ediv_left _ _ (Int.ne_of_gt hpi), ← hdiv]
      omega
    · rw [if_neg h]
      have hp : (2 : Nat) ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
      have hq : (m : Int) - 2 ^ k = (2 ^ i - 2 ^ k + m) + 2 ^ i * (-1) := by grind
      have hle : (2 : Int) ^ k ≤ 2 ^ i := by
        rw [← cast_two_pow, ← cast_two_pow]
        exact Int.ofNat_le.2 hp
      have hmc : (m : Int) < 2 ^ k := by
        rw [← cast_two_pow]; exact Int.ofNat_lt.2 hm
      rw [hq, Int.add_mul_ediv_left _ _ (Int.ne_of_gt hpi),
        Int.ediv_eq_zero_of_lt (by omega) (by omega)]
      decide

/-- `a ^ PyLong_MASK` on a digit. -/
theorem xor_mask {d : Nat} (hd : d < 2 ^ 30) : d ^^^ MASK = MASK - d := by
  apply Nat.eq_of_testBit_eq
  intro i
  have e : MASK - d = 2 ^ 30 - (d + 1) := by simp only [MASK]; omega
  rw [e, Nat.testBit_two_pow_sub_succ hd, Nat.testBit_xor]
  simp only [MASK, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 30
  · cases d.testBit i <;> simp [hi]
  · have h2 : d < 2 ^ i := Nat.lt_of_lt_of_le hd (Nat.pow_le_pow_right (by decide) (by omega))
    have h3 : d.testBit i = false := by
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.div_eq_of_lt h2]
      decide
    simp [h3, hi]

/-! ## `v_complement` -/

/-- `v_complement(z, a, m)`, longobject.c:5558-5568, returning `z` and the final carry. -/
def vComplGo : List Nat → Nat → Py (List Nat × Nat)
  | [], carry => .ok ([], carry)
  | a :: as, carry => do
    let c ← chk32 (carry + (a ^^^ MASK))
    let (r, c') ← vComplGo as (c >>> 30)
    return ((c &&& MASK) :: r, c')

theorem vComplGo_spec : ∀ (as : List Nat) (carry : Nat), IsDigits as → carry ≤ 1 →
    ∃ z c, vComplGo as carry = .ok (z, c) ∧ IsDigits z ∧ z.length = as.length ∧ c ≤ 1 ∧
      val z + 2 ^ (30 * as.length) * c + val as + 1 = 2 ^ (30 * as.length) + carry
  | [], carry, _, hc => ⟨[], carry, rfl, isDigits_nil, rfl, hc, by simp; omega⟩
  | a :: as, carry, h, hc => by
    have ⟨ha, has⟩ := isDigits_cons.1 h
    have hx := xor_mask ha
    simp only [MASK] at hx
    have hlt : carry + (a ^^^ MASK) < 2 ^ 32 := by simp only [MASK]; omega
    have ⟨c1, c2⟩ := carry_step (x := carry + (a ^^^ MASK))
    have hhi : (carry + (a ^^^ MASK)) >>> 30 ≤ 1 := by
      rw [shr30]; simp only [MASK] at hx ⊢; omega
    obtain ⟨z, c, hr, h1, h2, h3, h4⟩ := vComplGo_spec as _ has hhi
    refine ⟨((carry + (a ^^^ MASK)) &&& MASK) :: z, c, ?_, isDigits_cons.2 ⟨c1, h1⟩,
      by simp [h2], h3, ?_⟩
    · simp only [vComplGo, chk32_ok hlt, bind_ok, hr, pure_ok]
    · have e0 : 2 ^ (30 * (a :: as).length) = 2 ^ 30 * 2 ^ (30 * as.length) := by
        rw [List.length_cons, show 30 * (as.length + 1) = 30 + 30 * as.length by omega, Nat.pow_add]
      rw [e0, val_cons, val_cons]
      generalize hP : 2 ^ (30 * as.length) = P at *
      generalize ((carry + (a ^^^ MASK)) &&& MASK) = low at *
      generalize hH : (carry + (a ^^^ MASK)) >>> 30 = hi at *
      have hd : (a ^^^ MASK) + a + 1 = 2 ^ 30 := by
        have : a ^^^ MASK = 2 ^ 30 - 1 - a := hx
        omega
      generalize a ^^^ MASK = d at *
      have e1 : 2 ^ 30 * val z + 2 ^ 30 * P * c = 2 ^ 30 * (val z + P * c) := by grind
      have e2 : 2 ^ 30 * (val z + P * c + val as + 1) = 2 ^ 30 * (P + hi) := by rw [h4]
      have e3 : 2 ^ 30 * (val z + P * c + val as + 1) =
          2 ^ 30 * (val z + P * c) + 2 ^ 30 * val as + 2 ^ 30 := by grind
      have e4 : 2 ^ 30 * (P + hi) = 2 ^ 30 * P + 2 ^ 30 * hi := by grind
      omega

/-- `v_complement` on a non-zero vector is `2**(30*m) - val a`, with no carry out. -/
theorem vCompl_nonzero {a : List Nat} (ha : IsDigits a) (h0 : val a ≠ 0) :
    ∃ z, vComplGo a 1 = .ok (z, 0) ∧ IsDigits z ∧ z.length = a.length ∧
      val z + val a = 2 ^ (30 * a.length) := by
  obtain ⟨z, c, hr, h1, h2, h3, h4⟩ := vComplGo_spec a 1 ha (by omega)
  have hlt := val_lt ha
  have hc : c = 0 := by
    rcases Nat.eq_zero_or_pos c with h | h
    · exact h
    · have := Nat.mul_le_mul_left (2 ^ (30 * a.length)) h
      omega
  subst hc
  simp only [Nat.mul_zero, Nat.add_zero] at h4
  exact ⟨z, hr, h1, h2, by omega⟩

/-! ## `long_bitwise` -/

/-- The three operators of `long_bitwise`. -/
inductive BitOp where
  | and | or | xor
  deriving Repr, DecidableEq

/-- The operator on digits. -/
def BitOp.nat : BitOp → Nat → Nat → Nat
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b

/-- The operator on bits. -/
def BitOp.bool : BitOp → Bool → Bool → Bool
  | .and, a, b => a && b
  | .or, a, b => a || b
  | .xor, a, b => a != b

theorem BitOp.testBit (op : BitOp) (a b i : Nat) :
    (op.nat a b).testBit i = op.bool (a.testBit i) (b.testBit i) := by
  cases op <;> simp [BitOp.nat, BitOp.bool, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]

theorem BitOp.lt (op : BitOp) {a b k : Nat} (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    op.nat a b < 2 ^ k := by
  cases op
  · exact Nat.and_lt_two_pow _ hb
  · exact Nat.or_lt_two_pow ha hb
  · exact Nat.xor_lt_two_pow ha hb

theorem BitOp.comm (op : BitOp) (a b : Bool) : op.bool a b = op.bool b a := by
  cases op <;> cases a <;> cases b <;> rfl

/-- Compute digits for the overlap of `a` and `b`, longobject.c:5661-5676. -/
def bwOverlap (op : BitOp) : List Nat → List Nat → List Nat
  | _, [] => []
  | [], _ :: _ => []
  | a :: as, b :: bs => op.nat a b :: bwOverlap op as bs

/-- `size_z`, longobject.c:5628-5643. -/
def bwSize (op : BitOp) (x y : List Nat) (ny : Bool) : Nat :=
  match op with
  | .xor => x.length
  | .and => if ny = true then x.length else y.length
  | .or => if ny = true then y.length else x.length

/-- The digits of `z` before the final complement, longobject.c:5660-5684. -/
def zOf (op : BitOp) (x y : List Nat) (ny : Bool) : List Nat :=
  let sizeZ := bwSize op x y ny
  bwOverlap op x y ++
    (if op = .xor ∧ ny = true then (x.drop y.length).map (· ^^^ MASK)
     else (x.drop y.length).take (sizeZ - y.length))

/-- Complement the result if negative, and normalize, longobject.c:5687-5695. -/
def bwFinish (negz : Bool) (z : List Nat) : Py Long :=
  if negz = true then
    match vComplGo (z ++ [MASK]) 1 with
    | .ok (u, _) =>
      let m := normalize u
      .ok ⟨!m.isEmpty, m⟩
    | .error e => .error e
  else .ok ⟨false, normalize z⟩

/-- Lines 5621-5696 of `long_bitwise`, once both operands are in two's complement and
`x` is the longer: choose the size and sign of `z`, return 0 when `z` would have no
digits and no sign digit (:5645-5649), else combine and complement back. -/
def bwCore (op : BitOp) (x y : List Nat) (nx ny : Bool) : Py Long :=
  let sizeZ := bwSize op x y ny + (if op.bool nx ny = true then 1 else 0)
  if sizeZ = 0 then .ok ⟨false, []⟩
  else do
    longAlloc sizeZ
    bwFinish (op.bool nx ny) (zOf op x y ny)

/-- If negative, replace by the two's complement, longobject.c:5597-5619. -/
def twosOf (neg : Bool) (ds : List Nat) : Py (List Nat) :=
  if neg then
    match longAlloc ds.length, vComplGo ds 1 with
    | .ok _, .ok (z, _) => .ok z
    | .error e, _ => .error e
    | _, .error e => .error e
  else .ok ds

/-- The body of `long_bitwise` after the swap: `a` is the longer operand. -/
def bwOrdered (a : Long) (op : BitOp) (b : Long) : Py Long :=
  match twosOf a.neg a.ds, twosOf b.neg b.ds with
  | .ok x, .ok y => bwCore op x y a.neg b.neg
  | .error e, _ => .error e
  | _, .error e => .error e

/-- `long_bitwise(a, op, b)`, longobject.c:5573-5696. 3.15 swaps the operands first, on
their digit counts (:5591-5595), and only then takes the two's complements. -/
def longBitwise (a : Long) (op : BitOp) (b : Long) : Py Long :=
  if a.ds.length < b.ds.length then bwOrdered b op a else bwOrdered a op b

/-- The `int64_t` two's complement bit pattern of a `stwodigits`. -/
def u64of (x : Int) : Nat := (x % 2 ^ 64).toNat

/-- A `uint64_t` bit pattern read back as `stwodigits`. -/
def s64of (m : Nat) : Int := if m < 2 ^ 63 then m else (m : Int) - 2 ^ 64

/-- `long_and`, `long_or`, `long_xor`, longobject.c:5699-5732. -/
def longBit (op : BitOp) (a b : Long) : Py Long :=
  if a.isCompact = true ∧ b.isCompact = true then
    .ok (fromSTwoDigits (s64of (op.nat (u64of a.medium) (u64of b.medium))))
  else longBitwise a op b

/-- `x` split into its 64 bit pattern and sign. -/
theorem u64of_tc {x : Int} (h1 : -(2 ^ 63 : Int) ≤ x) (h2 : x < 2 ^ 63) :
    u64of x < 2 ^ 64 ∧ x = (u64of x : Int) - (if decide (x < 0) = true then 2 ^ 64 else 0) := by
  simp only [u64of]
  by_cases h : x < 0
  · simp only [h, decide_true, ite_true]; omega
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]; omega

theorem testBit63 {m : Nat} (h : m < 2 ^ 64) : m.testBit 63 = decide (2 ^ 63 ≤ m) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  apply decide_eq_decide.2
  omega

theorem s64of_tc {m : Nat} (h : m < 2 ^ 64) :
    s64of m = (m : Int) - (if m.testBit 63 = true then 2 ^ 64 else 0) := by
  rw [testBit63 h]
  simp only [s64of]
  by_cases h2 : m < 2 ^ 63
  · have : ¬ 2 ^ 63 ≤ m := by omega
    simp [h2, this]
  · have : 2 ^ 63 ≤ m := by omega
    simp [h2, this]

theorem s64of_range {m : Nat} (h : m < 2 ^ 64) :
    -(2 ^ 63 : Int) ≤ s64of m ∧ s64of m < 2 ^ 63 := by
  simp only [s64of]
  split <;> omega

/-- The compact path acts bit by bit. -/
theorem compactBit_spec (op : BitOp) {a b : Int} (ha : a.natAbs < 2 ^ 30) (hb : b.natAbs < 2 ^ 30)
    (i : Nat) :
    bitZ (s64of (op.nat (u64of a) (u64of b))) i = op.bool (bitZ a i) (bitZ b i) := by
  obtain ⟨m1, e1⟩ := u64of_tc (x := a) (by omega) (by omega)
  obtain ⟨m2, e2⟩ := u64of_tc (x := b) (by omega) (by omega)
  have ea : bitZ a i = if i < 64 then (u64of a).testBit i else decide (a < 0) := by
    conv => lhs; rw [e1]
    exact bitZ_tc m1
  have eb : bitZ b i = if i < 64 then (u64of b).testBit i else decide (b < 0) := by
    conv => lhs; rw [e2]
    exact bitZ_tc m2
  have hm := BitOp.lt op m1 m2
  rw [s64of_tc hm, bitZ_tc hm, ea, eb]
  by_cases h : i < 64
  · simp only [h, ite_true, BitOp.testBit]
  · simp only [h, ite_false]
    rw [BitOp.testBit]
    have s1 : (u64of a).testBit 63 = decide (a < 0) := by
      rw [testBit63 m1]
      apply decide_eq_decide.2
      simp only [u64of]
      omega
    have s2 : (u64of b).testBit 63 = decide (b < 0) := by
      rw [testBit63 m2]
      apply decide_eq_decide.2
      simp only [u64of]
      omega
    rw [s1, s2]

theorem testBit_cons {d m i : Nat} (hd : d < 2 ^ 30) :
    (d + 2 ^ 30 * m).testBit i = if i < 30 then d.testBit i else m.testBit (i - 30) := by
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ hd]

theorem val_testBit_append {a b : List Nat} (ha : IsDigits a) (i : Nat) :
    (val (a ++ b)).testBit i =
      if i < 30 * a.length then (val a).testBit i else (val b).testBit (i - 30 * a.length) := by
  rw [val_append, Nat.add_comm, Nat.testBit_two_pow_mul_add _ (val_lt ha)]

/-- Digits of `val x` above the first `n` are those of `x.drop n`. -/
theorem val_testBit_drop {x : List Nat} {n : Nat} (hx : IsDigits x) (hn : n ≤ x.length) (j : Nat) :
    (val (x.drop n)).testBit j = (val x).testBit (j + 30 * n) := by
  have := val_testBit_append (a := x.take n) (b := x.drop n) (isDigits_take hx n) (j + 30 * n)
  rw [List.take_append_drop, List.length_take, Nat.min_eq_left hn, if_neg (by omega),
    Nat.add_sub_cancel] at this
  exact this.symm

theorem bwOverlap_spec (op : BitOp) : ∀ (x y : List Nat), IsDigits x → IsDigits y →
    y.length ≤ x.length →
    IsDigits (bwOverlap op x y) ∧ (bwOverlap op x y).length = y.length ∧
      ∀ i, i < 30 * y.length → (val (bwOverlap op x y)).testBit i =
        op.bool ((val x).testBit i) ((val y).testBit i)
  | _, [], _, _, _ => by
    simp [bwOverlap, isDigits_nil]
  | a :: as, b :: bs, hx, hy, hl => by
    have ⟨ha, has⟩ := isDigits_cons.1 hx
    have ⟨hb, hbs⟩ := isDigits_cons.1 hy
    obtain ⟨h1, h2, h3⟩ := bwOverlap_spec op as bs has hbs (by simpa using hl)
    have hd := BitOp.lt op ha hb
    refine ⟨isDigits_cons.2 ⟨hd, h1⟩, by simp [bwOverlap, h2], ?_⟩
    intro i hi
    simp only [bwOverlap, val_cons]
    rw [testBit_cons hd, testBit_cons ha, testBit_cons hb]
    by_cases h : i < 30
    · simp only [h, ite_true, BitOp.testBit]
    · simp only [h, ite_false]
      exact h3 _ (by simp only [List.length_cons] at hi; omega)
  | [], _ :: _, _, _, hl => by simp at hl

/-- Inverted digits have inverted bits. -/
theorem map_xor_spec : ∀ (l : List Nat), IsDigits l →
    IsDigits (l.map (· ^^^ MASK)) ∧ (l.map (· ^^^ MASK)).length = l.length ∧
      ∀ i, i < 30 * l.length → (val (l.map (· ^^^ MASK))).testBit i = !(val l).testBit i
  | [], _ => by simp [isDigits_nil]
  | a :: as, h => by
    have ⟨ha, has⟩ := isDigits_cons.1 h
    obtain ⟨h1, h2, h3⟩ := map_xor_spec as has
    have hd : a ^^^ MASK < 2 ^ 30 := by
      rw [xor_mask ha]; simp only [MASK]; omega
    refine ⟨isDigits_cons.2 ⟨hd, h1⟩, by simp, ?_⟩
    intro i hi
    simp only [List.map_cons, val_cons]
    rw [testBit_cons hd, testBit_cons ha]
    by_cases hlt : i < 30
    · simp only [hlt, ite_true, Nat.testBit_xor, MASK, Nat.testBit_two_pow_sub_one,
        decide_true, Bool.bne_true]
    · simp only [hlt, ite_false]
      exact h3 _ (by simp only [List.length_cons] at hi; omega)

/-- `val x - sign * 2**(30*len x)`: what a two's complement vector and sign stand for. -/
def tcVal (x : List Nat) (s : Bool) : Int :=
  (val x : Int) - (if s = true then 2 ^ (30 * x.length) else 0)

theorem bitZ_tcVal {x : List Nat} (hx : IsDigits x) (s : Bool) (i : Nat) :
    bitZ (tcVal x s) i = if i < 30 * x.length then (val x).testBit i else s :=
  bitZ_tc (val_lt hx)

/-- Complementing back (longobject.c:5687-5691) yields the canonical object of the
two's complement value, and the extra digit makes that complement exact. -/
theorem complBack {z : List Nat} (hz : IsDigits z) :
    ∃ u c, vComplGo (z ++ [MASK]) 1 = .ok (u, c) ∧
      (⟨!(normalize u).isEmpty, normalize u⟩ : Long) = Long.ofInt (tcVal z true) := by
  have hd : IsDigits (z ++ [MASK]) := isDigits_append.2 ⟨hz, isDigits_cons.2 ⟨by decide, isDigits_nil⟩⟩
  have hv : val (z ++ [MASK]) = val z + 2 ^ (30 * z.length) * MASK := by
    rw [val_append]; simp
  have hP : 0 < 2 ^ (30 * z.length) := Nat.two_pow_pos _
  have hm : 2 ^ (30 * z.length) * MASK ≠ 0 := Nat.mul_ne_zero (by omega) (by decide)
  obtain ⟨u, hu, u1, u2, u3⟩ := vCompl_nonzero hd (by omega)
  refine ⟨u, 0, hu, ?_⟩
  have hl : (z ++ [MASK]).length = z.length + 1 := by simp
  rw [hl, show 30 * (z.length + 1) = 30 * z.length + 30 by omega, Nat.pow_add, hv] at u3
  have hzlt := val_lt hz
  have hval : val u + val z = 2 ^ (30 * z.length) := by
    generalize 2 ^ (30 * z.length) = P at *
    have hMASK : P * MASK + P = P * 2 ^ 30 := by
      simp only [MASK]
      rw [show (2 : Nat) ^ 30 = 2 ^ 30 - 1 + 1 by decide, Nat.mul_add, Nat.mul_one]
    omega
  have hupos : 0 < val u := by omega
  rw [digitsOf_normalize u1]
  have htc : tcVal z true = -((val u : Nat) : Int) := by
    simp only [tcVal, ite_true]
    rw [← cast_two_pow]
    omega
  rw [htc, Long.ofInt_neg_natCast hupos]
  have hne : digitsOf (val u) ≠ [] := by rw [Ne, digitsOf_eq_nil]; omega
  have hemp : (digitsOf (val u)).isEmpty = false := by
    cases hh : digitsOf (val u) with
    | nil => exact absurd hh hne
    | cons _ _ => rfl
  simp [hemp]

theorem take_drop_all (x : List Nat) (n : Nat) : (x.drop n).take (x.length - n) = x.drop n :=
  List.take_of_length_le (by simp)

theorem zOf_spec (op : BitOp) {x y : List Nat} (hx : IsDigits x) (hy : IsDigits y)
    (hl : y.length ≤ x.length) (nx ny : Bool) (i : Nat) :
    IsDigits (zOf op x y ny) ∧
    bitZ (tcVal (zOf op x y ny) (op.bool nx ny)) i =
      op.bool (bitZ (tcVal x nx) i) (bitZ (tcVal y ny) i) := by
  obtain ⟨o1, o2, o3⟩ := bwOverlap_spec op x y hx hy hl
  have ddrop := isDigits_drop hx y.length
  have bitsDrop : ∀ i, 30 * y.length ≤ i → (val (x.drop y.length)).testBit (i - 30 * y.length)
      = (val x).testBit i := by
    intro i hi
    rw [val_testBit_drop hx hl, Nat.sub_add_cancel hi]
  rw [bitZ_tcVal hx, bitZ_tcVal hy]
  have hlow : ∀ i, x.length ≤ i / 30 → True := fun _ _ => trivial
  have hdropl : (x.drop y.length).length = x.length - y.length := by simp
  cases op with
  | and =>
    cases ny with
    | false =>
      have hz : zOf .and x y false = bwOverlap .and x y := by simp [zOf, bwSize]
      rw [hz]
      refine ⟨o1, ?_⟩
      rw [bitZ_tcVal o1, o2]
      by_cases h1 : i < 30 * y.length
      · simp only [h1, ite_true, BitOp.bool, Bool.and_false]
        have h2 : i < 30 * x.length := by omega
        simp only [h2, ite_true]
        exact o3 i h1
      · simp [h1, BitOp.bool]
    | true =>
      have hz : zOf .and x y true = bwOverlap .and x y ++ x.drop y.length := by
        simp [zOf, bwSize, take_drop_all]
      rw [hz]
      have dz := isDigits_append.2 ⟨o1, ddrop⟩
      refine ⟨dz, ?_⟩
      rw [bitZ_tcVal dz]
      have lz : (bwOverlap .and x y ++ x.drop y.length).length = x.length := by
        simp only [List.length_append, o2, hdropl]; omega
      rw [lz, val_testBit_append o1, o2]
      by_cases h1 : i < 30 * y.length
      · have h2 : i < 30 * x.length := by omega
        simp only [h1, h2, ite_true]
        exact o3 i h1
      · by_cases h2 : i < 30 * x.length
        · simp only [h1, h2, ite_true, ite_false, bitsDrop i (by omega), BitOp.bool, Bool.and_true]
        · simp only [h1, h2, ite_false, BitOp.bool, Bool.and_true]
  | or =>
    cases ny with
    | true =>
      have hz : zOf .or x y true = bwOverlap .or x y := by simp [zOf, bwSize]
      rw [hz]
      refine ⟨o1, ?_⟩
      rw [bitZ_tcVal o1, o2]
      by_cases h1 : i < 30 * y.length
      · have h2 : i < 30 * x.length := by omega
        simp only [h1, h2, ite_true]
        exact o3 i h1
      · simp [h1, BitOp.bool]
    | false =>
      have hz : zOf .or x y false = bwOverlap .or x y ++ x.drop y.length := by
        simp [zOf, bwSize, take_drop_all]
      rw [hz]
      have dz := isDigits_append.2 ⟨o1, ddrop⟩
      refine ⟨dz, ?_⟩
      rw [bitZ_tcVal dz]
      have lz : (bwOverlap .or x y ++ x.drop y.length).length = x.length := by
        simp only [List.length_append, o2, hdropl]; omega
      rw [lz, val_testBit_append o1, o2]
      by_cases h1 : i < 30 * y.length
      · have h2 : i < 30 * x.length := by omega
        simp only [h1, h2, ite_true]
        exact o3 i h1
      · by_cases h2 : i < 30 * x.length
        · simp only [h1, h2, ite_true, ite_false, bitsDrop i (by omega), BitOp.bool, Bool.or_false]
        · simp only [h1, h2, ite_false, BitOp.bool, Bool.or_false]
  | xor =>
    cases ny with
    | false =>
      have hz : zOf .xor x y false = bwOverlap .xor x y ++ x.drop y.length := by
        simp [zOf, bwSize, take_drop_all]
      rw [hz]
      have dz := isDigits_append.2 ⟨o1, ddrop⟩
      refine ⟨dz, ?_⟩
      rw [bitZ_tcVal dz]
      have lz : (bwOverlap .xor x y ++ x.drop y.length).length = x.length := by
        simp only [List.length_append, o2, hdropl]; omega
      rw [lz, val_testBit_append o1, o2]
      by_cases h1 : i < 30 * y.length
      · have h2 : i < 30 * x.length := by omega
        simp only [h1, h2, ite_true]
        exact o3 i h1
      · by_cases h2 : i < 30 * x.length
        · simp [h1, h2, bitsDrop i (by omega), BitOp.bool]
        · simp [h1, h2, BitOp.bool]
    | true =>
      obtain ⟨m1, m2, m3⟩ := map_xor_spec (x.drop y.length) ddrop
      have hz : zOf .xor x y true =
          bwOverlap .xor x y ++ (x.drop y.length).map (· ^^^ MASK) := by simp [zOf]
      rw [hz]
      have dz := isDigits_append.2 ⟨o1, m1⟩
      refine ⟨dz, ?_⟩
      rw [bitZ_tcVal dz]
      have lz : (bwOverlap .xor x y ++ (x.drop y.length).map (· ^^^ MASK)).length = x.length := by
        simp only [List.length_append, o2, m2, hdropl]; omega
      rw [lz, val_testBit_append o1, o2]
      by_cases h1 : i < 30 * y.length
      · have h2 : i < 30 * x.length := by omega
        simp only [h1, h2, ite_true]
        exact o3 i h1
      · by_cases h2 : i < 30 * x.length
        · have h3 : i - 30 * y.length < 30 * (x.drop y.length).length := by
            rw [hdropl]; omega
          simp only [h1, h2, ite_true, ite_false]
          rw [m3 _ h3, bitsDrop i (by omega)]
          simp [BitOp.bool]
        · simp [h1, h2, BitOp.bool]

/-- With `size_z == 0` there is nothing in `z`. -/
theorem zOf_nil (op : BitOp) {x y : List Nat} (hl : y.length ≤ x.length) (ny : Bool)
    (h : bwSize op x y ny = 0) : zOf op x y ny = [] := by
  have hy : y = [] := by
    apply List.eq_nil_of_length_eq_zero
    cases op <;> cases ny <;>
      simp only [bwSize, Bool.false_eq_true, ite_false, ite_true] at h <;> omega
  subst hy
  cases op <;> cases ny <;>
    simp only [bwSize, Bool.false_eq_true, ite_false, ite_true] at h <;>
    simp [zOf, bwSize, bwOverlap, h, List.eq_nil_of_length_eq_zero h]

theorem bwCore_spec (op : BitOp) {x y : List Nat} (hx : IsDigits x) (hy : IsDigits y)
    (hl : y.length ≤ x.length) (hs : x.length + 1 ≤ maxLongDigits) (nx ny : Bool) :
    bwCore op x y nx ny = .ok (Long.ofInt (tcVal (zOf op x y ny) (op.bool nx ny))) := by
  have dz := (zOf_spec op hx hy hl nx ny 0).1
  have hsz : bwSize op x y ny + (if op.bool nx ny = true then 1 else 0) ≤ maxLongDigits := by
    have h1 : bwSize op x y ny ≤ x.length := by
      cases op <;> simp only [bwSize] <;> (try split) <;> omega
    split <;> omega
  simp only [bwCore]
  by_cases h0 : bwSize op x y ny + (if op.bool nx ny = true then 1 else 0) = 0
  · have h1 : op.bool nx ny = false := by
      cases hn : op.bool nx ny
      · rfl
      · rw [hn] at h0; simp at h0
    have h2 : bwSize op x y ny = 0 := by
      rw [h1] at h0; simpa using h0
    rw [if_pos h0, h1, zOf_nil op hl ny h2]
    rfl
  rw [if_neg h0, longAlloc_ok hsz]
  simp only [bind_ok]
  unfold bwFinish
  by_cases hneg : op.bool nx ny = true
  · rw [if_pos hneg, hneg]
    obtain ⟨u, c, h1, h2⟩ := complBack dz
    simp only [h1]
    exact congrArg Except.ok h2
  · rw [if_neg hneg]
    have hf : op.bool nx ny = false := by simpa using hneg
    rw [hf, digitsOf_normalize dz]
    simp only [tcVal, Bool.false_eq_true, ite_false, Int.sub_zero]
    rw [Long.ofInt_natCast]

theorem twosOf_spec (v : Int) (hs : digitCount v.natAbs ≤ maxLongDigits) :
    ∃ x, twosOf (decide (v < 0)) (digitsOf v.natAbs) = .ok x ∧ IsDigits x ∧
      x.length = digitCount v.natAbs ∧ tcVal x (decide (v < 0)) = v := by
  have d0 := digitsOf_digits v.natAbs
  have l0 := length_digitsOf v.natAbs
  have v0 := val_digitsOf v.natAbs
  by_cases h : v < 0
  · obtain ⟨z, hz, z1, z2, z3⟩ := vCompl_nonzero d0 (by rw [v0]; omega)
    rw [v0, l0] at z3
    refine ⟨z, ?_, z1, by omega, ?_⟩
    · simp only [twosOf, h, decide_true, ite_true, longAlloc_ok (show (digitsOf v.natAbs).length ≤ _ by omega), hz]
    · simp only [tcVal, h, decide_true, ite_true]
      rw [show z.length = digitCount v.natAbs by omega, ← cast_two_pow]
      omega
  · refine ⟨digitsOf v.natAbs, ?_, d0, l0, ?_⟩
    · simp [twosOf, h]
    · simp only [tcVal, h, decide_false, Bool.false_eq_true, ite_false, Int.sub_zero, v0]
      omega

/-- `long_bitwise` acts bit by bit on the infinite two's complement expansions. -/
theorem longBitwise_spec (op : BitOp) (a b : Int)
    (ha : digitCount a.natAbs + 1 ≤ maxLongDigits) (hb : digitCount b.natAbs + 1 ≤ maxLongDigits) :
    ∃ r, longBitwise (Long.ofInt a) op (Long.ofInt b) = .ok (Long.ofInt r) ∧
      ∀ i, bitZ r i = op.bool (bitZ a i) (bitZ b i) := by
  obtain ⟨x, hx, x1, x2, x3⟩ := twosOf_spec a (by omega)
  obtain ⟨y, hy, y1, y2, y3⟩ := twosOf_spec b (by omega)
  have ea : (Long.ofInt a).neg = decide (a < 0) := rfl
  have eb : (Long.ofInt b).neg = decide (b < 0) := rfl
  have da : (Long.ofInt a).ds = digitsOf a.natAbs := rfl
  have db : (Long.ofInt b).ds = digitsOf b.natAbs := rfl
  have l1 := length_digitsOf a.natAbs
  have l2 := length_digitsOf b.natAbs
  by_cases hl : x.length < y.length
  · have : (digitsOf a.natAbs).length < (digitsOf b.natAbs).length := by omega
    simp only [longBitwise, bwOrdered, ea, eb, da, db, hx, hy, this, ite_true]
    rw [bwCore_spec op y1 x1 (by omega) (by omega)]
    refine ⟨_, rfl, fun i => ?_⟩
    rw [(zOf_spec op y1 x1 (by omega) _ _ i).2, y3, x3, BitOp.comm]
  · have : ¬ (digitsOf a.natAbs).length < (digitsOf b.natAbs).length := by omega
    simp only [longBitwise, bwOrdered, ea, eb, da, db, hx, hy, this, ite_false]
    rw [bwCore_spec op x1 y1 (by omega) (by omega)]
    refine ⟨_, rfl, fun i => ?_⟩
    rw [(zOf_spec op x1 y1 (by omega) _ _ i).2, y3, x3]

/-- `x & y`, `x | y`, `x ^ y` act bit by bit, on the compact path and on `long_bitwise`. -/
theorem longBit_spec (op : BitOp) (a b : Int)
    (ha : digitCount a.natAbs + 1 ≤ maxLongDigits) (hb : digitCount b.natAbs + 1 ≤ maxLongDigits) :
    ∃ r, longBit op (Long.ofInt a) (Long.ofInt b) = .ok (Long.ofInt r) ∧
      ∀ i, bitZ r i = op.bool (bitZ a i) (bitZ b i) := by
  unfold longBit
  by_cases hc : (Long.ofInt a).isCompact = true ∧ (Long.ofInt b).isCompact = true
  · rw [if_pos hc]
    have h1 : a.natAbs < 2 ^ 30 := by
      have := hc.1; rw [Long.isCompact_ofInt] at this; exact of_decide_eq_true this
    have h2 : b.natAbs < 2 ^ 30 := by
      have := hc.2; rw [Long.isCompact_ofInt] at this; exact of_decide_eq_true this
    have hlt := BitOp.lt op (u64of_tc (x := a) (by omega) (by omega)).1
      (u64of_tc (x := b) (by omega) (by omega)).1
    obtain ⟨r1, r2⟩ := s64of_range hlt
    rw [Long.medium_ofInt h1, Long.medium_ofInt h2, fromSTwoDigits_eq r1 r2]
    exact ⟨_, rfl, compactBit_spec op h1 h2⟩
  · rw [if_neg hc]
    exact longBitwise_spec op a b ha hb

/-! ## `~x`, `-x`, `abs(x)`, `bool(x)` -/

/-- `long_invert(v)`, longobject.c:5251-5266. `~m` on `stwodigits` is `-m - 1`. -/
def longInvert (v : Long) : Py Long :=
  if v.isCompact = true then .ok (fromSTwoDigits (-v.medium - 1))
  else
    match longAdd v longOne with
    | .ok x => .ok x.flip
    | .error e => .error e

/-- `long_neg(v)`, longobject.c:5269-5280. -/
def longNeg (v : Long) : Long :=
  if v.isCompact = true then fromSTwoDigits (-v.medium) else v.flip

/-- `long_abs(v)`, longobject.c:5289-5295. -/
def longAbs (v : Long) : Long := if v.neg then longNeg v else v

/-- `long_bool(v)`, longobject.c:5304-5307. -/
def longBool (v : Long) : Bool := !v.ds.isEmpty

theorem longInvert_spec (a : Int) (ha : digitCount a.natAbs + 1 ≤ maxLongDigits) :
    longInvert (Long.ofInt a) = .ok (Long.ofInt (-a - 1)) := by
  unfold longInvert
  by_cases hc : (Long.ofInt a).isCompact = true
  · rw [if_pos hc]
    have h1 : a.natAbs < 2 ^ 30 := by
      rw [Long.isCompact_ofInt] at hc; exact of_decide_eq_true hc
    rw [Long.medium_ofInt h1, fromSTwoDigits_eq (by omega) (by omega)]
  · rw [if_neg hc, longOne_eq, longAdd_spec a 1 ha (by unfold Sized; decide)]
    simp only
    rw [← Long.ofInt_neg]
    congr 2
    omega

theorem longNeg_spec (a : Int) : longNeg (Long.ofInt a) = Long.ofInt (-a) := by
  unfold longNeg
  by_cases hc : (Long.ofInt a).isCompact = true
  · rw [if_pos hc]
    have h1 : a.natAbs < 2 ^ 30 := by
      rw [Long.isCompact_ofInt] at hc; exact of_decide_eq_true hc
    rw [Long.medium_ofInt h1, fromSTwoDigits_eq (by omega) (by omega)]
  · rw [if_neg hc, Long.ofInt_neg]

theorem longAbs_spec (a : Int) : longAbs (Long.ofInt a) = Long.ofInt (a.natAbs : Int) := by
  unfold longAbs
  by_cases h : a < 0
  · have hn : (Long.ofInt a).neg = true := decide_eq_true h
    rw [if_pos hn, longNeg_spec]
    congr 1
    omega
  · have hn : (Long.ofInt a).neg = false := decide_eq_false h
    rw [if_neg (by simp [hn])]
    congr 1
    omega

theorem longBool_spec (a : Int) : longBool (Long.ofInt a) = decide (a ≠ 0) := by
  simp only [longBool, Long.ofInt]
  by_cases h : a = 0
  · subst h; simp
  · have hne : digitsOf a.natAbs ≠ [] := by rw [Ne, digitsOf_eq_nil]; omega
    have hemp : (digitsOf a.natAbs).isEmpty = false := by
      cases hh : digitsOf a.natAbs with
      | nil => exact absurd hh hne
      | cons _ _ => rfl
    simp [hemp, h]

end PyLean.LongObj
