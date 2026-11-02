import PyLean.Core

/-!
# The pre-sort compare selection for int keys

For a list whose keys are all exact `int`s, `list_sort_impl` picks
`unsafe_long_compare` when every key is compact (at most one 30-bit digit), and
`unsafe_object_compare` over `long_richcompare` otherwise
(`listobject.c:3029-3124`). `unsafeObjectCompare` mirrors that function for keys of
any type; `difftest/listsort_diff.py` fn `"objcmp"` checks its branches on two-item
lists. The model represents an int as in
`Include/cpython/longintrepr.h`: a sign and little-endian base `2^30` digits with
a non-zero top digit. `longCompare` mirrors `long_compare`
(`Objects/longobject.c:3605-3623`) digit by digit, so the theorems here say the
fast path and the digit loop both agree with `<` on `Int`.
-/

namespace PyLean.ListSort

open PyLean

/-- What `tp_richcompare(v, w, Py_LT)` returns when it does not raise: `NotImplemented`,
a `bool`, or any other object `o`. -/
inductive RichRes (ρ : Type) where
  | notImplemented
  | bool (b : Bool)
  | other (o : ρ)

/-- `unsafe_object_compare(v, w, ms)` (`listobject.c:2799-2832`): `-1` with an exception
set is `.error`. `sameSlot` is `Py_TYPE(v)->tp_richcompare == ms->key_richcompare`
(:2804, re-checked because a comparison can reassign `__class__`), `rich` the slot's
result, `isTrue` is `PyObject_IsTrue`, which can raise, and `fallback` is
`PyObject_RichCompareBool(v, w, Py_LT)`. -/
def unsafeObjectCompare {ρ : Type} (sameSlot : Bool) (rich : Py (RichRes ρ)) (isTrue : ρ → Py Bool)
    (fallback : Py Bool) : Py Bool :=
  if !sameSlot then fallback
  else
    match rich with
    | .ok .notImplemented => fallback
    | .error e => .error e
    | .ok (.bool b) => .ok b
    | .ok (.other o) => isTrue o

/-- `1 << PyLong_SHIFT` (`longintrepr.h:47`). -/
def digitBase : Nat := 2 ^ 30

/-- `ob_digit`: little-endian digits, top digit non-zero, `[]` for 0. -/
def toDigits : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, n => if n = 0 then [] else (n % digitBase) :: toDigits fuel (n / digitBase)

/-- An exact `int`: `sign` is `1 - (lv_tag & _PyLong_SIGN_MASK)`, in `{1, 0, -1}`. -/
structure PyLong where
  sign : Int
  digits : List Nat

def PyLong.ofInt (x : Int) : PyLong := ⟨x.sign, toDigits x.natAbs x.natAbs⟩

/-- `_PyLong_IsCompact`: `lv_tag < (2 << _PyLong_NON_SIZE_BITS)`, at most one digit. -/
def PyLong.isCompact (v : PyLong) : Bool := decide (v.digits.length ≤ 1)

/-- `_PyLong_CompactValue`: `sign * ob_digit[0]` (`ob_digit[0]` is 0 for zero). -/
def PyLong.compactValue (v : PyLong) : Int := v.sign * (v.digits.getD 0 0 : Nat)

/-- `_PyLong_SignedDigitCount`. -/
def PyLong.signedDigitCount (v : PyLong) : Int := v.sign * (v.digits.length : Int)

/-- `while (--i >= 0) { diff = a[i] - b[i]; if (diff) break; }` from digit `i`. -/
def digitLoop (a b : List Nat) : Nat → Int
  | 0 => 0
  | i + 1 =>
    let diff : Int := (a.getD i 0 : Int) - (b.getD i 0 : Int)
    if diff ≠ 0 then diff else digitLoop a b i

/-- `long_compare(a, b)` (`Objects/longobject.c:3605-3623`). -/
def longCompare (a b : PyLong) : Int :=
  if a.isCompact && b.isCompact then a.compactValue - b.compactValue
  else
    let sign := a.signedDigitCount - b.signedDigitCount
    if sign = 0 then
      let diff := digitLoop a.digits b.digits a.digits.length
      if a.sign < 0 then -diff else diff
    else sign

/-- `unsafe_long_compare` (`listobject.c:2860-2882`): `v0 < w0`. -/
def unsafeLongCompare (v w : PyLong) : Bool := decide (v.compactValue < w.compactValue)

/-- `long_richcompare(v, w, Py_LT)` (`Objects/longobject.c:3626-3635`). The `self ==
other` shortcut gives 0, as `long_compare` does for equal values. -/
def longRichLt (v w : PyLong) : Bool := decide (longCompare v w < 0)

/-- `ints_are_bounded` over the keys (`listobject.c:3073-3078`, `:3094`). -/
def allCompact (keys : List Int) : Bool := keys.all (fun k => (PyLong.ofInt k).isCompact)

/-- `unsafe_object_compare` on exact ints: every key has `long_richcompare` as its
slot, which answers with a `bool` and never raises. -/
def longObjectCompare (v w : PyLong) : Bool :=
  match unsafeObjectCompare (ρ := PUnit) true (.ok (.bool (longRichLt v w))) (fun _ => .ok false)
      (.ok false) with
  | .ok b => b
  | .error _ => false

/-- The compare chosen by the pre-sort check for all-int keys. -/
def selectCompare (bounded : Bool) (x y : Int) : Bool :=
  if bounded then unsafeLongCompare (.ofInt x) (.ofInt y)
  else longObjectCompare (.ofInt x) (.ofInt y)

/-! ## Digits -/

/-- The value of little-endian digits. -/
def val : List Nat → Nat
  | [] => 0
  | d :: ds => d + digitBase * val ds

theorem toDigits_spec : ∀ (fuel n : Nat), n ≤ fuel →
    val (toDigits fuel n) = n ∧ (∀ d ∈ toDigits fuel n, d < digitBase) ∧
      ((n = 0 ∧ toDigits fuel n = []) ∨
        ∃ j, (toDigits fuel n).length = j + 1 ∧ digitBase ^ j ≤ n ∧ n < digitBase ^ (j + 1))
  | 0, n, h => by
    have : n = 0 := by omega
    subst this; simp [toDigits, val]
  | fuel + 1, n, h => by
    simp only [toDigits]
    by_cases h0 : n = 0
    · subst h0; simp [val]
    simp only [h0, ↓reduceIte]
    have hB : digitBase = 1073741824 := rfl
    have hq : n / digitBase ≤ fuel := by rw [hB]; omega
    obtain ⟨h1, h2, h3⟩ := toDigits_spec fuel (n / digitBase) hq
    have hr : n % digitBase + digitBase * (n / digitBase) = n := Nat.mod_add_div n digitBase
    have hlt : n % digitBase < digitBase := Nat.mod_lt _ (by rw [hB]; omega)
    refine ⟨by simp only [val]; rw [h1]; exact hr, ?_, .inr ?_⟩
    · intro d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact hlt
      · exact h2 d hd
    · rcases h3 with ⟨hq0, hd⟩ | ⟨j, hl, ha, hb⟩
      · refine ⟨0, by simp [hd], ?_, ?_⟩
        · rw [Nat.pow_zero]; omega
        · rw [hq0, Nat.mul_zero, Nat.add_zero] at hr
          rw [Nat.zero_add, Nat.pow_one]; omega
      · refine ⟨j + 1, by simp [hl], ?_, ?_⟩
        · have := Nat.mul_le_mul_left digitBase ha
          rw [Nat.pow_succ, Nat.mul_comm]
          omega
        · have h1 : n / digitBase + 1 ≤ digitBase ^ (j + 1) := hb
          have h2 := Nat.mul_le_mul_left digitBase h1
          rw [Nat.mul_add, Nat.mul_one] at h2
          rw [Nat.pow_succ _ (j + 1), Nat.mul_comm (digitBase ^ (j + 1))]
          omega

theorem val_take_succ : ∀ (a : List Nat) (i : Nat), i < a.length →
    val (a.take (i + 1)) = val (a.take i) + digitBase ^ i * a.getD i 0
  | [], _, h => by simp at h
  | a0 :: as, 0, _ => by simp [val]
  | a0 :: as, i + 1, h => by
    have ih := val_take_succ as i (by simpa using h)
    simp only [List.take_succ_cons, val, List.getD_cons_succ]
    rw [ih, Nat.mul_add, Nat.pow_succ, Nat.mul_comm (digitBase ^ i) digitBase, Nat.mul_assoc]
    omega

theorem val_take_lt : ∀ (a : List Nat), (∀ d ∈ a, d < digitBase) → ∀ i, val (a.take i) < digitBase ^ i
  | [], _, i => by simp [val]; exact Nat.pow_pos (by decide)
  | a0 :: as, _, 0 => by simp [val]
  | a0 :: as, h, i + 1 => by
    have ih := val_take_lt as (fun d hd => h d (by simp [hd])) i
    have h0 := h a0 (by simp)
    simp only [List.take_succ_cons, val]
    have h1 : val (as.take i) + 1 ≤ digitBase ^ i := ih
    have h2 := Nat.mul_le_mul_left digitBase h1
    rw [Nat.mul_add, Nat.mul_one] at h2
    rw [Nat.pow_succ, Nat.mul_comm (digitBase ^ i)]
    omega

/-- `digitLoop` compares the low `i` digits numerically. -/
theorem digitLoop_spec (a b : List Nat) (ha : ∀ d ∈ a, d < digitBase) (hb : ∀ d ∈ b, d < digitBase) :
    ∀ i, i ≤ a.length → i ≤ b.length →
      (digitLoop a b i < 0 ↔ val (a.take i) < val (b.take i)) ∧
      (0 < digitLoop a b i ↔ val (b.take i) < val (a.take i))
  | 0, _, _ => by simp [digitLoop, val]
  | i + 1, h1, h2 => by
    have ih := digitLoop_spec a b ha hb i (by omega) (by omega)
    rw [val_take_succ a i (by omega), val_take_succ b i (by omega)]
    have hVa := val_take_lt a ha i
    have hVb := val_take_lt b hb i
    simp only [digitLoop]
    generalize a.getD i 0 = x
    generalize b.getD i 0 = y
    generalize val (a.take i) = Va at *
    generalize val (b.take i) = Vb at *
    generalize digitBase ^ i = P at *
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

theorem len_lt_val {m k : Nat} (h : (toDigits m m).length < (toDigits k k).length) : m < k := by
  obtain ⟨_, _, h3⟩ := toDigits_spec m m (Nat.le_refl _)
  obtain ⟨_, _, h3'⟩ := toDigits_spec k k (Nat.le_refl _)
  rcases h3' with ⟨_, hd⟩ | ⟨j', hl', ha', _⟩
  · rw [hd] at h; simp at h
  rcases h3 with ⟨hm, _⟩ | ⟨j, hl, _, hb⟩
  · have : 0 < digitBase ^ j' := Nat.pow_pos (by decide)
    omega
  · have : digitBase ^ (j + 1) ≤ digitBase ^ j' := Nat.pow_le_pow_right (by decide) (by omega)
    omega

theorem eq_len_cmp {m k : Nat} (h : (toDigits m m).length = (toDigits k k).length) :
    (digitLoop (toDigits m m) (toDigits k k) (toDigits m m).length < 0 ↔ m < k) ∧
    (0 < digitLoop (toDigits m m) (toDigits k k) (toDigits m m).length ↔ k < m) := by
  obtain ⟨h1, h2, _⟩ := toDigits_spec m m (Nat.le_refl _)
  obtain ⟨h1', h2', _⟩ := toDigits_spec k k (Nat.le_refl _)
  have := digitLoop_spec _ _ h2 h2' (toDigits m m).length (Nat.le_refl _) (Nat.le_of_eq h)
  have e1 : (toDigits m m).take (toDigits m m).length = toDigits m m :=
    List.take_of_length_le (Nat.le_refl _)
  have e2 : (toDigits k k).take (toDigits m m).length = toDigits k k :=
    List.take_of_length_le (Nat.le_of_eq h.symm)
  rw [e1, e2, h1, h1'] at this
  exact this

theorem isCompact_iff (x : Int) : (PyLong.ofInt x).isCompact = decide (x.natAbs < digitBase) := by
  obtain ⟨_, _, h3⟩ := toDigits_spec x.natAbs x.natAbs (Nat.le_refl _)
  unfold PyLong.isCompact
  apply decide_eq_decide.2
  show (toDigits x.natAbs x.natAbs).length ≤ 1 ↔ _
  have hB : (1 : Nat) ≤ digitBase := by decide
  rcases h3 with ⟨h0, hd⟩ | ⟨j, hl, ha, hb⟩
  · rw [hd, h0]; simp; omega
  · rw [hl]
    cases j with
    | zero => simp at ha hb ⊢; omega
    | succ j =>
      constructor
      · intro h; omega
      · intro h
        have : digitBase ^ 1 ≤ digitBase ^ (j + 1) := Nat.pow_le_pow_right (by decide) (by omega)
        simp at this; omega

theorem compactValue_eq (x : Int) (h : (PyLong.ofInt x).isCompact = true) :
    (PyLong.ofInt x).compactValue = x := by
  obtain ⟨h1, _, h3⟩ := toDigits_spec x.natAbs x.natAbs (Nat.le_refl _)
  simp only [PyLong.compactValue, PyLong.ofInt]
  have hlen : (toDigits x.natAbs x.natAbs).length ≤ 1 := of_decide_eq_true h
  have hd : (toDigits x.natAbs x.natAbs).getD 0 0 = x.natAbs := by
    rcases hds : toDigits x.natAbs x.natAbs with _ | ⟨d, ds⟩
    · rw [hds] at h1; simpa [val] using h1
    · have : ds = [] := by
        rw [hds] at hlen
        simp only [List.length_cons] at hlen
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst this
      rw [hds] at h1
      simpa [val] using h1
  rw [hd]
  exact Int.sign_mul_natAbs x

/-- The length/size relation of `toDigits_spec`, for `z`'s magnitude. -/
def toDigits_prop (z : Int) : Prop :=
  (z.natAbs = 0 ∧ toDigits z.natAbs z.natAbs = []) ∨
    ∃ j, (toDigits z.natAbs z.natAbs).length = j + 1 ∧ digitBase ^ j ≤ z.natAbs ∧
      z.natAbs < digitBase ^ (j + 1)

theorem cmp_arith (x y : Int) (lx ly : Nat) (D : Int)
    (hlt : lx < ly → x.natAbs < y.natAbs) (hgt : ly < lx → y.natAbs < x.natAbs)
    (heq : lx = ly → (D < 0 ↔ x.natAbs < y.natAbs) ∧ (0 < D ↔ y.natAbs < x.natAbs))
    (hxl : x ≠ 0 → 1 ≤ lx) (hyl : y ≠ 0 → 1 ≤ ly) (hx0 : x = 0 → lx = 0) (hy0 : y = 0 → ly = 0) :
    (if x.sign * (lx : Int) - y.sign * (ly : Int) = 0 then (if x.sign < 0 then -D else D)
      else x.sign * (lx : Int) - y.sign * (ly : Int)) < 0 ↔ x < y := by
  have sx : (x < 0 ∧ x.sign = -1) ∨ (x = 0 ∧ x.sign = 0) ∨ (0 < x ∧ x.sign = 1) := by
    rcases Int.lt_trichotomy x 0 with h | h | h
    · exact .inl ⟨h, Int.sign_eq_neg_one_of_neg h⟩
    · exact .inr (.inl ⟨h, by simp [h]⟩)
    · exact .inr (.inr ⟨h, Int.sign_eq_one_of_pos h⟩)
  have sy : (y < 0 ∧ y.sign = -1) ∨ (y = 0 ∧ y.sign = 0) ∨ (0 < y ∧ y.sign = 1) := by
    rcases Int.lt_trichotomy y 0 with h | h | h
    · exact .inl ⟨h, Int.sign_eq_neg_one_of_neg h⟩
    · exact .inr (.inl ⟨h, by simp [h]⟩)
    · exact .inr (.inr ⟨h, Int.sign_eq_one_of_pos h⟩)
  rcases sx with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases sy with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rw [h2, h4] <;> split <;> (try split) <;> omega

/-- `long_compare(x, y) < 0` exactly when `x < y`, for all ints of every size. -/
theorem longCompare_lt (x y : Int) : longCompare (.ofInt x) (.ofInt y) < 0 ↔ x < y := by
  unfold longCompare
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    rw [compactValue_eq x h.1, compactValue_eq y h.2]
    omega
  · have hx := toDigits_spec x.natAbs x.natAbs (Nat.le_refl _)
    have hy := toDigits_spec y.natAbs y.natAbs (Nat.le_refl _)
    have len_of_ne : ∀ (z : Int), toDigits_prop z → z ≠ 0 → 1 ≤ (toDigits z.natAbs z.natAbs).length := by
      intro z hz h0
      rcases hz with ⟨h, _⟩ | ⟨j, hj, _⟩
      · omega
      · omega
    have len_of_zero : ∀ z : Int, z = 0 → (toDigits z.natAbs z.natAbs).length = 0 := by
      intro z h0; subst h0; simp [toDigits]
    exact cmp_arith x y (toDigits x.natAbs x.natAbs).length (toDigits y.natAbs y.natAbs).length _
      len_lt_val len_lt_val eq_len_cmp (len_of_ne x hx.2.2) (len_of_ne y hy.2.2)
      (len_of_zero x) (len_of_zero y)

/-- The chosen compare agrees with `<` on the keys of the list. -/
theorem selectCompare_eq (keys : List Int) (x y : Int) (hx : x ∈ keys) (hy : y ∈ keys) :
    selectCompare (allCompact keys) x y = decide (x < y) := by
  unfold selectCompare
  split
  · rename_i h
    have hall := List.all_eq_true.1 h
    unfold unsafeLongCompare
    rw [compactValue_eq x (hall x hx), compactValue_eq y (hall y hy)]
  · show longRichLt (.ofInt x) (.ofInt y) = decide (x < y)
    unfold longRichLt
    exact decide_eq_decide.2 (longCompare_lt x y)

end PyLean.ListSort
