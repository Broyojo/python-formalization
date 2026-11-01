import PyLean.LongObj.Digits

/-!
`x_add`, `x_sub`, `long_add`, `long_sub` and the in-place vector operations
`v_iadd` and `v_isub`, longobject.c. The `digit` carry and borrow are checked to
fit `uint32_t`; subtraction wraps as the C does.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt

/-! ## `x_add` -/

/-- Second loop of `x_add` and the store of the final carry, longobject.c:3672-3677. -/
def xAddTail : List Nat → Nat → Py (List Nat)
  | [], carry => .ok [carry]
  | a :: as, carry => do
    let c ← chk32 (carry + a)
    let r ← xAddTail as (c >>> 30)
    return (c &&& MASK) :: r

/-- First loop of `x_add`, longobject.c:3667-3671. -/
def xAddLoop : List Nat → List Nat → Nat → Py (List Nat)
  | as, [], carry => xAddTail as carry
  | a :: as, b :: bs, carry => do
    let s ← chk32 (a + b)
    let c ← chk32 (carry + s)
    let r ← xAddLoop as bs (c >>> 30)
    return (c &&& MASK) :: r
  | [], _ :: _, _ => .error cOverflow

/-- `x_add(a, b)`, longobject.c:3650-3679. -/
def xAdd (a b : List Nat) : Py (List Nat) :=
  let (a, b) := if a.length < b.length then (b, a) else (a, b)
  do
    longAlloc (a.length + 1)
    let z ← xAddLoop a b 0
    return normalize z

/-- One carry step: for `x < 2^31`, the digit and next carry split `x`. -/
theorem carry_step {x : Nat} : (x &&& MASK) < 2 ^ 30 ∧ (x &&& MASK) + 2 ^ 30 * (x >>> 30) = x := by
  rw [and30, shr30]
  exact ⟨Nat.mod_lt _ (by decide), Nat.mod_add_div _ _⟩

theorem xAddTail_spec : ∀ (as : List Nat) (carry : Nat), IsDigits as → carry ≤ 1 →
    ∃ z, xAddTail as carry = .ok z ∧ IsDigits z ∧ z.length = as.length + 1 ∧
      val z = val as + carry
  | [], carry, _, hc => ⟨[carry], rfl, isDigits_cons.2 ⟨by omega, isDigits_nil⟩, rfl, by simp⟩
  | a :: as, carry, h, hc => by
    have ⟨ha, has⟩ := isDigits_cons.1 h
    have hlt : carry + a < 2 ^ 32 := by omega
    have ⟨c1, c2⟩ := carry_step (x := carry + a)
    have hc' : (carry + a) >>> 30 ≤ 1 := by rw [shr30]; omega
    obtain ⟨z, hz, h1, h2, h3⟩ := xAddTail_spec as _ has hc'
    refine ⟨((carry + a) &&& MASK) :: z, ?_, isDigits_cons.2 ⟨c1, h1⟩, by simp [h2], ?_⟩
    · simp only [xAddTail, chk32_ok hlt, bind_ok, hz, pure_ok]
    · simp only [val_cons, h3]
      rw [Nat.mul_add]
      omega

theorem xAddLoop_spec : ∀ (as bs : List Nat) (carry : Nat), IsDigits as → IsDigits bs →
    bs.length ≤ as.length → carry ≤ 1 →
    ∃ z, xAddLoop as bs carry = .ok z ∧ IsDigits z ∧ z.length = as.length + 1 ∧
      val z = val as + val bs + carry
  | as, [], carry, h, _, _, hc => by
    obtain ⟨z, hz, h1, h2, h3⟩ := xAddTail_spec as carry h hc
    exact ⟨z, by simp [xAddLoop, hz], h1, h2, by simp [h3]⟩
  | a :: as, b :: bs, carry, h, hb, hl, hc => by
    have ⟨ha, has⟩ := isDigits_cons.1 h
    have ⟨hb0, hbs⟩ := isDigits_cons.1 hb
    have hlt1 : a + b < 2 ^ 32 := by omega
    have hlt : carry + (a + b) < 2 ^ 32 := by omega
    have ⟨c1, c2⟩ := carry_step (x := carry + (a + b))
    have hc' : (carry + (a + b)) >>> 30 ≤ 1 := by rw [shr30]; omega
    obtain ⟨z, hz, h1, h2, h3⟩ := xAddLoop_spec as bs _ has hbs (by simpa using hl) hc'
    refine ⟨((carry + (a + b)) &&& MASK) :: z, ?_, isDigits_cons.2 ⟨c1, h1⟩, by simp [h2], ?_⟩
    · simp only [xAddLoop, chk32_ok hlt1, chk32_ok hlt, bind_ok, hz, pure_ok]
    · simp only [val_cons, h3]
      simp only [Nat.mul_add]
      omega
  | [], _ :: _, _, _, _, hl, _ => by simp at hl

/-- `x_add` is exact, normalized, and its `digit` carry never wraps. -/
theorem xAdd_spec {a b : List Nat} (ha : IsDigits a) (hb : IsDigits b)
    (hs : max a.length b.length + 1 ≤ maxLongDigits) :
    xAdd a b = .ok (digitsOf (val a + val b)) := by
  unfold xAdd
  by_cases h : a.length < b.length
  · simp only [h, ite_true]
    obtain ⟨z, hz, h1, _, h3⟩ := xAddLoop_spec b a 0 hb ha (Nat.le_of_lt h) (by omega)
    rw [show b.length + 1 ≤ maxLongDigits by omega |> longAlloc_ok]
    simp only [bind_ok, hz, pure_ok, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [digitsOf_normalize h1, h3]
    simp [Nat.add_comm]
  · simp only [h, ite_false]
    obtain ⟨z, hz, h1, _, h3⟩ := xAddLoop_spec a b 0 ha hb (by omega) (by omega)
    rw [show a.length + 1 ≤ maxLongDigits by omega |> longAlloc_ok]
    simp only [bind_ok, hz, pure_ok, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [digitsOf_normalize h1, h3]
    simp

/-! ## `x_sub` -/

/-- Second loop of `x_sub`, longobject.c:3724-3729, returning the digits and the
final borrow (asserted to be zero at :3730). -/
def xSubTail : List Nat → Nat → List Nat × Nat
  | [], borrow => ([], borrow)
  | a :: as, borrow =>
    let t := subU32 a 0 borrow
    let (r, b) := xSubTail as ((t >>> 30) &&& 1)
    ((t &&& MASK) :: r, b)

/-- First loop of `x_sub`, longobject.c:3716-3723. -/
def xSubLoop : List Nat → List Nat → Nat → List Nat × Nat
  | as, [], borrow => xSubTail as borrow
  | a :: as, b :: bs, borrow =>
    let t := subU32 a b borrow
    let (r, c) := xSubLoop as bs ((t >>> 30) &&& 1)
    ((t &&& MASK) :: r, c)
  | [], _ :: _, borrow => ([], borrow)

/-- The scan `while (--i >= 0 && a[i] == b[i]);`, longobject.c:3702-3704. -/
def scanDiff (a b : List Nat) : Nat → Option Nat
  | 0 => none
  | i + 1 => if a.getD i 0 = b.getD i 0 then scanDiff a b i else some i

/-- Lines 3713-3734 of `x_sub`: subtract `b` from `a`, both already arranged. -/
def xSubGo (neg : Bool) (a b : List Nat) : Py Long := do
  longAlloc a.length
  let (z, _) := xSubLoop a b 0
  return (if neg then Long.flip else id) ⟨false, normalize z⟩

/-- `x_sub(a, b)`, longobject.c:3684-3735. -/
def xSub (a b : List Nat) : Py Long :=
  if a.length < b.length then xSubGo true b a
  else if a.length = b.length then
    match scanDiff a b a.length with
    | none => .ok ⟨false, []⟩
    | some i =>
      if a.getD i 0 < b.getD i 0 then xSubGo true (b.take (i + 1)) (a.take (i + 1))
      else xSubGo false (a.take (i + 1)) (b.take (i + 1))
  else xSubGo false a b

theorem subU32_step {a b c : Nat} (ha : a < 2 ^ 30) (hb : b < 2 ^ 30) (hc : c ≤ 1) :
    (subU32 a b c &&& MASK) < 2 ^ 30 ∧ ((subU32 a b c >>> 30) &&& 1) ≤ 1 ∧
    (subU32 a b c &&& MASK) + b + c = a + 2 ^ 30 * ((subU32 a b c >>> 30) &&& 1) := by
  have h1 : ∀ x : Nat, x &&& 1 = x % 2 := fun x => Nat.and_two_pow_sub_one_eq_mod x 1
  rw [and30, shr30, h1]
  simp only [subU32]
  omega

theorem xSubTail_spec : ∀ (as : List Nat) (borrow : Nat), IsDigits as → borrow ≤ 1 →
    IsDigits (xSubTail as borrow).1 ∧ (xSubTail as borrow).2 ≤ 1 ∧
      (xSubTail as borrow).1.length = as.length ∧
      val (xSubTail as borrow).1 + borrow =
        val as + 2 ^ (30 * as.length) * (xSubTail as borrow).2
  | [], borrow, _, hb => by simp [xSubTail, isDigits_nil, hb]
  | a :: as, borrow, h, hb => by
    have ⟨ha, has⟩ := isDigits_cons.1 h
    have ⟨s1, s2, s3⟩ := subU32_step (b := 0) ha (by decide) hb
    obtain ⟨h1, h2, h3, h4⟩ := xSubTail_spec as _ has s2
    simp only [xSubTail]
    generalize subU32 a 0 borrow = t at *
    generalize hr : xSubTail as ((t >>> 30) &&& 1) = r at *
    obtain ⟨z, cc⟩ := r
    simp only at h1 h2 h3 h4 ⊢
    refine ⟨isDigits_cons.2 ⟨s1, h1⟩, h2, by simp [h3], ?_⟩
    simp only [val_cons, List.length_cons]
    rw [show 30 * (as.length + 1) = 30 + 30 * as.length by omega, Nat.pow_add, Nat.mul_assoc
      ]
    grind

theorem xSubLoop_spec : ∀ (as bs : List Nat) (borrow : Nat), IsDigits as → IsDigits bs →
    bs.length ≤ as.length → borrow ≤ 1 →
    IsDigits (xSubLoop as bs borrow).1 ∧ (xSubLoop as bs borrow).2 ≤ 1 ∧
      (xSubLoop as bs borrow).1.length = as.length ∧
      val (xSubLoop as bs borrow).1 + val bs + borrow =
        val as + 2 ^ (30 * as.length) * (xSubLoop as bs borrow).2
  | as, [], borrow, h, _, _, hb => by
    obtain ⟨h1, h2, h3, h4⟩ := xSubTail_spec as borrow h hb
    simp only [xSubLoop, val_nil, Nat.add_zero]
    exact ⟨h1, h2, h3, h4⟩
  | a :: as, b :: bs, borrow, h, hb0, hl, hb => by
    have ⟨ha, has⟩ := isDigits_cons.1 h
    have ⟨hb1, hbs⟩ := isDigits_cons.1 hb0
    have ⟨s1, s2, s3⟩ := subU32_step ha hb1 hb
    obtain ⟨h1, h2, h3, h4⟩ := xSubLoop_spec as bs _ has hbs (by simpa using hl) s2
    simp only [xSubLoop]
    generalize subU32 a b borrow = t at *
    generalize hr : xSubLoop as bs ((t >>> 30) &&& 1) = r at *
    obtain ⟨z, cc⟩ := r
    simp only at h1 h2 h3 h4 ⊢
    refine ⟨isDigits_cons.2 ⟨s1, h1⟩, h2, by simp [h3], ?_⟩
    simp only [val_cons, List.length_cons]
    rw [show 30 * (as.length + 1) = 30 + 30 * as.length by omega, Nat.pow_add, Nat.mul_assoc]
    grind
  | [], _ :: _, _, _, _, hl, _ => by simp at hl

/-- `xSubGo` on `val b ≤ val a` is exact. -/
theorem xSubGo_spec {neg : Bool} {a b : List Nat} (ha : IsDigits a) (hb : IsDigits b)
    (hl : b.length ≤ a.length) (hs : a.length ≤ maxLongDigits) (hle : val b ≤ val a) :
    xSubGo neg a b = .ok ((if neg then Long.flip else id) ⟨false, digitsOf (val a - val b)⟩) := by
  obtain ⟨h1, h2, h3, h4⟩ := xSubLoop_spec a b 0 ha hb hl (by omega)
  unfold xSubGo
  rw [longAlloc_ok hs]
  generalize hr : xSubLoop a b 0 = r at *
  obtain ⟨z, cc⟩ := r
  simp only at h1 h2 h3 h4
  simp only [bind_ok, pure_ok, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have hz := val_lt h1
  rw [h3] at hz
  have hc : cc = 0 := by
    rcases Nat.eq_zero_or_pos cc with h0 | h0
    · exact h0
    · have := Nat.mul_le_mul_left (2 ^ (30 * a.length)) h0
      omega
  rw [hc] at h4
  have hv : val z = val a - val b := by omega
  rw [digitsOf_normalize h1, hv]

theorem scanDiff_none : ∀ {a b : List Nat} {n : Nat}, scanDiff a b n = none →
    ∀ k < n, a.getD k 0 = b.getD k 0
  | _, _, 0, _, _, hk => absurd hk (by omega)
  | a, b, n + 1, h, k, hk => by
    simp only [scanDiff] at h
    split at h
    · rename_i he
      by_cases hk' : k = n
      · subst hk'; exact he
      · exact scanDiff_none h k (by omega)
    · simp at h

theorem scanDiff_some : ∀ {a b : List Nat} {n i : Nat}, scanDiff a b n = some i →
    i < n ∧ a.getD i 0 ≠ b.getD i 0 ∧ ∀ k, i < k → k < n → a.getD k 0 = b.getD k 0
  | _, _, 0, _, h => by simp [scanDiff] at h
  | a, b, n + 1, i, h => by
    simp only [scanDiff] at h
    split at h
    · rename_i he
      obtain ⟨h1, h2, h3⟩ := scanDiff_some h
      refine ⟨by omega, h2, fun k hk hk2 => ?_⟩
      by_cases hk' : k = n
      · subst hk'; exact he
      · exact h3 k hk (by omega)
    · rename_i he
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨by omega, he, fun k hk hk2 => by omega⟩

theorem eq_of_getD_eq : ∀ {a b : List Nat}, a.length = b.length →
    (∀ k < a.length, a.getD k 0 = b.getD k 0) → a = b
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hl, h => by
    have h0 := h 0 (by simp)
    simp only [List.getD_cons_zero] at h0
    have ih := eq_of_getD_eq (a := xs) (b := ys) (by simpa using hl) (fun k hk => by
      have := h (k + 1) (by simp; omega)
      simpa using this)
    rw [h0, ih]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- If two equal-length vectors agree above position `i`, their difference is
that of their prefixes up to `i` inclusive. -/
theorem val_split_at {a : List Nat} {i : Nat} (hi : i < a.length) :
    val a = val (a.take (i + 1)) + 2 ^ (30 * (i + 1)) * val (a.drop (i + 1)) := by
  have := val_take_add_drop a (i + 1)
  rwa [List.length_take, Nat.min_eq_left (by omega)] at this

theorem drop_eq_of_getD {a b : List Nat} {i : Nat} (hl : a.length = b.length)
    (h : ∀ k, i < k → k < a.length → a.getD k 0 = b.getD k 0) :
    a.drop (i + 1) = b.drop (i + 1) := by
  apply eq_of_getD_eq (by simp [hl])
  intro k hk
  simp only [List.length_drop] at hk
  have := h (i + 1 + k) (by omega) (by omega)
  simpa [List.getD, List.getElem?_drop] using this

/-- Comparing prefixes up to `i` by their top digit. -/
theorem val_take_lt {a b : List Nat} {i : Nat} (ha : IsDigits a) (hb : IsDigits b)
    (hi : i < a.length) (hib : i < b.length) (hlt : a.getD i 0 < b.getD i 0) :
    val (a.take (i + 1)) < val (b.take (i + 1)) := by
  have ea : a.take (i + 1) = a.take i ++ [a[i]] := by simp
  have eb : b.take (i + 1) = b.take i ++ [b[i]'hib] := by simp
  have ga : a.getD i 0 = a[i] := by simp [List.getD, hi]
  have gb : b.getD i 0 = b[i]'hib := by simp [List.getD, hib]
  rw [ga, gb] at hlt
  rw [ea, eb, val_append, val_append]
  simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi), Nat.min_eq_left (Nat.le_of_lt hib),
    val_cons, val_nil, Nat.mul_zero, Nat.add_zero]
  have hA := val_le_of_len (isDigits_take ha i) (n := i) (by simp; omega)
  have hm := Nat.mul_le_mul_left (2 ^ (30 * i)) (show a[i] + 1 ≤ b[i]'hib from hlt)
  rw [Nat.mul_add, Nat.mul_one] at hm
  omega

/-- For normalized magnitudes with fewer digits, the value is smaller. -/
theorem val_lt_of_length {a b : List Nat} (ha : IsDigits a) (hb : IsDigits b) (hn : Normal b)
    (hl : a.length < b.length) : val a < val b := by
  have hne : b ≠ [] := by intro h; simp [h] at hl
  obtain ⟨l, d, hb'⟩ : ∃ l d, b = l ++ [d] :=
    ⟨b.dropLast, b.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
  have hd : d ≠ 0 := by
    have := hn hne
    simpa [hb'] using this
  subst hb'
  rw [val_append]
  simp only [val_cons, val_nil, Nat.mul_zero, Nat.add_zero]
  simp only [List.length_append, List.length_cons, List.length_nil] at hl
  have h1 : val a < 2 ^ (30 * l.length) := val_le_of_len ha (by omega)
  have h2 := Nat.mul_le_mul_left (2 ^ (30 * l.length)) (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hd))
  omega

/-- `x_sub` on normalized magnitudes is exact: it returns the canonical object
of `val a - val b` (with the sign of that difference). -/
theorem xSub_spec {a b : List Nat} (ha : IsDigits a) (hb : IsDigits b) (na : Normal a)
    (nb : Normal b) (hsa : a.length ≤ maxLongDigits) (hsb : b.length ≤ maxLongDigits) :
    xSub a b = .ok (Long.ofInt ((val a : Int) - val b)) := by
  unfold xSub
  by_cases h1 : a.length < b.length
  · simp only [h1, ite_true]
    have hlt := val_lt_of_length ha hb nb h1
    rw [xSubGo_spec hb ha (by omega) hsb (by omega)]
    have : (val a : Int) - val b = -((val b - val a : Nat) : Int) := by omega
    rw [this, Long.ofInt_neg, Long.ofInt_natCast]
    rfl
  · simp only [h1, ite_false]
    by_cases h2 : a.length = b.length
    · simp only [h2, ite_true]
      rw [← h2]
      generalize hs : scanDiff a b a.length = sc
      cases sc with
      | none =>
        have := eq_of_getD_eq h2 (scanDiff_none hs)
        subst this
        simp [Long.ofInt]
      | some i =>
        obtain ⟨hi, hne, hgt⟩ := scanDiff_some hs
        have hib : i < b.length := by omega
        have hdrop := drop_eq_of_getD h2 hgt
        have va := val_split_at hi
        have vb := val_split_at hib
        rw [← hdrop] at vb
        generalize val (a.drop (i + 1)) = S at va vb
        generalize 2 ^ (30 * (i + 1)) * S = T at va vb
        simp only
        have lena : (a.take (i + 1)).length = i + 1 := by simp; omega
        have lenb : (b.take (i + 1)).length = i + 1 := by simp; omega
        have hsz : i + 1 ≤ maxLongDigits := by omega
        by_cases hlt : a.getD i 0 < b.getD i 0
        · simp only [hlt, ite_true]
          have hv := val_take_lt ha hb hi hib hlt
          rw [xSubGo_spec (isDigits_take hb _) (isDigits_take ha _) (by omega) (by omega) (by omega)]
          have : (val a : Int) - val b
              = -((val (b.take (i + 1)) - val (a.take (i + 1)) : Nat) : Int) := by omega
          rw [this, Long.ofInt_neg, Long.ofInt_natCast]
          rfl
        · simp only [hlt, ite_false]
          have hgt' : b.getD i 0 < a.getD i 0 := by omega
          have hv := val_take_lt hb ha hib hi hgt'
          rw [xSubGo_spec (isDigits_take ha _) (isDigits_take hb _) (by omega) (by omega) (by omega)]
          have : (val a : Int) - val b
              = ((val (a.take (i + 1)) - val (b.take (i + 1)) : Nat) : Int) := by omega
          rw [this, Long.ofInt_natCast]
          rfl
    · simp only [h2, ite_false]
      have hlt := val_lt_of_length hb ha na (by omega)
      rw [xSubGo_spec ha hb (by omega) hsa (by omega)]
      have : (val a : Int) - val b = ((val a - val b : Nat) : Int) := by omega
      rw [this, Long.ofInt_natCast]
      rfl

/-! ## `long_add`, `long_sub` -/

/-- `x_add` with a sign, as `_PyLong_FlipSign(z)` leaves it (longobject.c:3755, :3800). -/
def xAddSigned (neg : Bool) (a b : List Nat) : Py Long := do
  let z ← xAdd a b
  return (if neg then Long.flip else id) ⟨false, z⟩

/-- `long_add(a, b)`, longobject.c:3738-3768. -/
def longAdd (a b : Long) : Py Long :=
  if bothCompact a b then do
    let z ← chkS64 (a.medium + b.medium)
    return fromSTwoDigits z
  else if a.neg then
    if b.neg then xAddSigned true a.ds b.ds
    else xSub b.ds a.ds
  else if b.neg then xSub a.ds b.ds
  else xAddSigned false a.ds b.ds

/-- `long_sub(a, b)`, longobject.c:3785-3811. -/
def longSub (a b : Long) : Py Long :=
  if bothCompact a b then do
    let z ← chkS64 (a.medium - b.medium)
    return fromSTwoDigits z
  else if a.neg then
    if b.neg then xSub b.ds a.ds
    else xAddSigned true a.ds b.ds
  else if b.neg then xAddSigned false a.ds b.ds
  else xSub a.ds b.ds

/-- An `int` operand of a binary operation whose digit count leaves room for one
more digit: allocation cannot fail (`long_alloc`'s limit is a type invariant of
every object, and these are the only sizes the arithmetic can request). -/
def Sized (v : Int) : Prop := digitCount v.natAbs + 1 ≤ maxLongDigits

theorem xAddSigned_spec {neg : Bool} {a b : List Nat} (ha : IsDigits a) (hb : IsDigits b)
    (hs : max a.length b.length + 1 ≤ maxLongDigits) :
    xAddSigned neg a b = .ok ((if neg then Long.flip else id) ⟨false, digitsOf (val a + val b)⟩) := by
  simp only [xAddSigned, xAdd_spec ha hb hs, bind_ok, pure_ok]

theorem longAdd_spec (a b : Int) (ha : Sized a) (hb : Sized b) :
    longAdd (Long.ofInt a) (Long.ofInt b) = .ok (Long.ofInt (a + b)) := by
  unfold longAdd
  by_cases hc : bothCompact (Long.ofInt a) (Long.ofInt b) = true
  · simp only [hc, ite_true]
    simp only [bothCompact, Long.isCompact_ofInt, Bool.and_eq_true] at hc
    have h1 := of_decide_eq_true hc.1
    have h2 := of_decide_eq_true hc.2
    rw [Long.medium_ofInt h1, Long.medium_ofInt h2, chkS64_ok (by omega)]
    simp only [bind_ok, pure_ok]
    rw [fromSTwoDigits_eq (by omega) (by omega)]
  · simp only [hc, Bool.false_eq_true, ite_false]
    have dsa := digitsOf_digits a.natAbs
    have dsb := digitsOf_digits b.natAbs
    have na := normal_digitsOf a.natAbs
    have nb := normal_digitsOf b.natAbs
    have la := length_digitsOf a.natAbs
    have lb := length_digitsOf b.natAbs
    unfold Sized at ha hb
    have hmax : max (digitsOf a.natAbs).length (digitsOf b.natAbs).length + 1 ≤ maxLongDigits := by
      omega
    simp only [Long.ofInt, decide_eq_true_eq]
    by_cases hna : a < 0
    · simp only [hna, ite_true, decide_true]
      by_cases hnb : b < 0
      · simp only [hnb, ite_true, decide_true]
        rw [xAddSigned_spec dsa dsb hmax]
        simp only [val_digitsOf, ite_true]
        have e : a + b = -((a.natAbs + b.natAbs : Nat) : Int) := by omega
        have := Long.ofInt_neg_natCast (n := a.natAbs + b.natAbs) (by omega)
        rw [e]
        have h2 : (Long.ofInt (-((a.natAbs + b.natAbs : Nat) : Int))) =
          ⟨decide (-((a.natAbs + b.natAbs : Nat) : Int) < 0),
            digitsOf (-((a.natAbs + b.natAbs : Nat) : Int)).natAbs⟩ := rfl
        rw [← h2, this]
        simp only [Long.flip]
        have hne : digitsOf (a.natAbs + b.natAbs) ≠ [] := by
          rw [Ne, digitsOf_eq_nil]; omega
        simp [hne]
      · simp only [hnb, ite_false, decide_false]
        rw [xSub_spec dsb dsa nb na (by omega) (by omega)]
        simp only [val_digitsOf]
        have e : (b.natAbs : Int) - a.natAbs = a + b := by omega
        rw [e]; rfl
    · simp only [hna, ite_false, decide_false]
      by_cases hnb : b < 0
      · simp only [hnb, ite_true, decide_true]
        rw [xSub_spec dsa dsb na nb (by omega) (by omega)]
        simp only [val_digitsOf]
        have e : (a.natAbs : Int) - b.natAbs = a + b := by omega
        rw [e]; rfl
      · simp only [hnb, ite_false, decide_false]
        rw [xAddSigned_spec dsa dsb hmax]
        simp only [val_digitsOf, Bool.false_eq_true, ite_false, id]
        have e : a + b = ((a.natAbs + b.natAbs : Nat) : Int) := by omega
        rw [e]
        exact congrArg Except.ok (Long.ofInt_natCast _).symm

theorem longSub_spec (a b : Int) (ha : Sized a) (hb : Sized b) :
    longSub (Long.ofInt a) (Long.ofInt b) = .ok (Long.ofInt (a - b)) := by
  unfold longSub
  by_cases hc : bothCompact (Long.ofInt a) (Long.ofInt b) = true
  · simp only [hc, ite_true]
    simp only [bothCompact, Long.isCompact_ofInt, Bool.and_eq_true] at hc
    have h1 := of_decide_eq_true hc.1
    have h2 := of_decide_eq_true hc.2
    rw [Long.medium_ofInt h1, Long.medium_ofInt h2, chkS64_ok (by omega)]
    simp only [bind_ok, pure_ok]
    rw [fromSTwoDigits_eq (by omega) (by omega)]
  · simp only [hc, Bool.false_eq_true, ite_false]
    have dsa := digitsOf_digits a.natAbs
    have dsb := digitsOf_digits b.natAbs
    have na := normal_digitsOf a.natAbs
    have nb := normal_digitsOf b.natAbs
    have la := length_digitsOf a.natAbs
    have lb := length_digitsOf b.natAbs
    unfold Sized at ha hb
    have hmax : max (digitsOf a.natAbs).length (digitsOf b.natAbs).length + 1 ≤ maxLongDigits := by
      omega
    simp only [Long.ofInt, decide_eq_true_eq]
    by_cases hna : a < 0
    · simp only [hna, ite_true, decide_true]
      by_cases hnb : b < 0
      · simp only [hnb, ite_true, decide_true]
        rw [xSub_spec dsb dsa nb na (by omega) (by omega)]
        simp only [val_digitsOf]
        have e : (b.natAbs : Int) - a.natAbs = a - b := by omega
        rw [e]; rfl
      · simp only [hnb, ite_false, decide_false]
        rw [xAddSigned_spec dsa dsb hmax]
        simp only [val_digitsOf, ite_true]
        have e : a - b = -((a.natAbs + b.natAbs : Nat) : Int) := by omega
        have := Long.ofInt_neg_natCast (n := a.natAbs + b.natAbs) (by omega)
        rw [e]
        have h2 : (Long.ofInt (-((a.natAbs + b.natAbs : Nat) : Int))) =
          ⟨decide (-((a.natAbs + b.natAbs : Nat) : Int) < 0),
            digitsOf (-((a.natAbs + b.natAbs : Nat) : Int)).natAbs⟩ := rfl
        rw [← h2, this]
        simp only [Long.flip]
        have hne : digitsOf (a.natAbs + b.natAbs) ≠ [] := by
          rw [Ne, digitsOf_eq_nil]; omega
        simp [hne]
    · simp only [hna, ite_false, decide_false]
      by_cases hnb : b < 0
      · simp only [hnb, ite_true, decide_true]
        rw [xAddSigned_spec dsa dsb hmax]
        simp only [val_digitsOf, Bool.false_eq_true, ite_false, id]
        have e : a - b = ((a.natAbs + b.natAbs : Nat) : Int) := by omega
        rw [e]
        exact congrArg Except.ok (Long.ofInt_natCast _).symm
      · simp only [hnb, ite_false, decide_false]
        rw [xSub_spec dsa dsb na nb (by omega) (by omega)]
        simp only [val_digitsOf]
        have e : (a.natAbs : Int) - b.natAbs = a - b := by omega
        rw [e]; rfl

/-! ## `v_iadd`, `v_isub` -/

/-- Second loop of `v_iadd`, longobject.c:1791-1796: stops when the carry dies. -/
def vIAddTail : List Nat → Nat → Py (List Nat × Nat)
  | [], carry => .ok ([], carry)
  | x :: xs, carry =>
    if carry = 0 then .ok (x :: xs, 0)
    else do
      let c ← chk32 (carry + x)
      let (r, c') ← vIAddTail xs (c >>> 30)
      return ((c &&& MASK) :: r, c')

/-- `v_iadd(x, m, y, n)`, longobject.c:1779-1798, with `m = x.length` and
`n = y.length`; returns the updated `x` and the final carry. -/
def vIAddGo : List Nat → List Nat → Nat → Py (List Nat × Nat)
  | xs, [], carry => vIAddTail xs carry
  | x :: xs, y :: ys, carry => do
    let s ← chk32 (x + y)
    let c ← chk32 (carry + s)
    let (r, c') ← vIAddGo xs ys (c >>> 30)
    return ((c &&& MASK) :: r, c')
  | [], _ :: _, _ => .error cOverflow

def vIAdd (x y : List Nat) : Py (List Nat × Nat) := vIAddGo x y 0

theorem vIAddTail_spec : ∀ (xs : List Nat) (carry : Nat), IsDigits xs → carry ≤ 1 →
    ∃ r c, vIAddTail xs carry = .ok (r, c) ∧ IsDigits r ∧ r.length = xs.length ∧ c ≤ 1 ∧
      val r + 2 ^ (30 * xs.length) * c = val xs + carry
  | [], carry, _, hc => ⟨[], carry, rfl, isDigits_nil, rfl, hc, by simp⟩
  | x :: xs, carry, h, hc => by
    have ⟨hx, hxs⟩ := isDigits_cons.1 h
    by_cases h0 : carry = 0
    · subst h0
      refine ⟨x :: xs, 0, by simp [vIAddTail], h, rfl, by omega, by simp⟩
    · have hlt : carry + x < 2 ^ 32 := by omega
      have ⟨c1, c2⟩ := carry_step (x := carry + x)
      obtain ⟨r, c, hr, h1, h2, h3, h4⟩ := vIAddTail_spec xs ((carry + x) >>> 30) hxs
        (by rw [shr30]; omega)
      refine ⟨((carry + x) &&& MASK) :: r, c, ?_, isDigits_cons.2 ⟨c1, h1⟩, by simp [h2], h3, ?_⟩
      · simp only [vIAddTail, h0, ite_false, chk32_ok hlt, bind_ok, hr, pure_ok]
      · simp only [val_cons, List.length_cons]
        rw [show 30 * (xs.length + 1) = 30 + 30 * xs.length by omega, Nat.pow_add, Nat.mul_assoc]
        grind

theorem vIAddGo_spec : ∀ (xs ys : List Nat) (carry : Nat), IsDigits xs → IsDigits ys →
    ys.length ≤ xs.length → carry ≤ 1 →
    ∃ r c, vIAddGo xs ys carry = .ok (r, c) ∧ IsDigits r ∧ r.length = xs.length ∧ c ≤ 1 ∧
      val r + 2 ^ (30 * xs.length) * c = val xs + val ys + carry
  | xs, [], carry, h, _, _, hc => by
    obtain ⟨r, c, hr, h1, h2, h3, h4⟩ := vIAddTail_spec xs carry h hc
    exact ⟨r, c, by simp [vIAddGo, hr], h1, h2, h3, by simpa using h4⟩
  | x :: xs, y :: ys, carry, h, hy, hl, hc => by
    have ⟨hx, hxs⟩ := isDigits_cons.1 h
    have ⟨hy0, hys⟩ := isDigits_cons.1 hy
    have hlt1 : x + y < 2 ^ 32 := by omega
    have hlt : carry + (x + y) < 2 ^ 32 := by omega
    have ⟨c1, c2⟩ := carry_step (x := carry + (x + y))
    obtain ⟨r, c, hr, h1, h2, h3, h4⟩ := vIAddGo_spec xs ys ((carry + (x + y)) >>> 30) hxs hys
      (by simpa using hl) (by rw [shr30]; omega)
    refine ⟨((carry + (x + y)) &&& MASK) :: r, c, ?_, isDigits_cons.2 ⟨c1, h1⟩, by simp [h2], h3, ?_⟩
    · simp only [vIAddGo, chk32_ok hlt1, chk32_ok hlt, bind_ok, hr, pure_ok]
    · simp only [val_cons, List.length_cons]
      rw [show 30 * (xs.length + 1) = 30 + 30 * xs.length by omega, Nat.pow_add, Nat.mul_assoc]
      grind
  | [], _ :: _, _, _, _, hl, _ => by simp at hl

/-- Second loop of `v_isub`, longobject.c:1817-1822. -/
def vISubTail : List Nat → Nat → List Nat × Nat
  | [], borrow => ([], borrow)
  | x :: xs, borrow =>
    if borrow = 0 then (x :: xs, 0)
    else
      let t := subU32 x borrow 0
      let (r, b) := vISubTail xs ((t >>> 30) &&& 1)
      ((t &&& MASK) :: r, b)

/-- `v_isub(x, m, y, n)`, longobject.c:1805-1824. -/
def vISubGo : List Nat → List Nat → Nat → List Nat × Nat
  | xs, [], borrow => vISubTail xs borrow
  | x :: xs, y :: ys, borrow =>
    let t := subU32 x y borrow
    let (r, b) := vISubGo xs ys ((t >>> 30) &&& 1)
    ((t &&& MASK) :: r, b)
  | [], _ :: _, borrow => ([], borrow)

def vISub (x y : List Nat) : List Nat × Nat := vISubGo x y 0

theorem vISubTail_spec : ∀ (xs : List Nat) (borrow : Nat), IsDigits xs → borrow ≤ 1 →
    IsDigits (vISubTail xs borrow).1 ∧ (vISubTail xs borrow).2 ≤ 1 ∧
      (vISubTail xs borrow).1.length = xs.length ∧
      val (vISubTail xs borrow).1 + borrow =
        val xs + 2 ^ (30 * xs.length) * (vISubTail xs borrow).2
  | [], borrow, _, hb => by simp [vISubTail, isDigits_nil, hb]
  | x :: xs, borrow, h, hb => by
    have ⟨hx, hxs⟩ := isDigits_cons.1 h
    by_cases h0 : borrow = 0
    · subst h0
      simp [vISubTail, h]
    · have hb1 : borrow < 2 ^ 30 := by omega
      have ⟨s1, s2, s3⟩ := subU32_step (c := 0) hx hb1 (by omega)
      obtain ⟨h1, h2, h3, h4⟩ := vISubTail_spec xs _ hxs s2
      simp only [vISubTail, h0, ite_false]
      generalize subU32 x borrow 0 = t at *
      generalize hr : vISubTail xs ((t >>> 30) &&& 1) = r at *
      obtain ⟨z, cc⟩ := r
      simp only at h1 h2 h3 h4 ⊢
      refine ⟨isDigits_cons.2 ⟨s1, h1⟩, h2, by simp [h3], ?_⟩
      simp only [val_cons, List.length_cons]
      rw [show 30 * (xs.length + 1) = 30 + 30 * xs.length by omega, Nat.pow_add, Nat.mul_assoc]
      grind

theorem vISubGo_spec : ∀ (xs ys : List Nat) (borrow : Nat), IsDigits xs → IsDigits ys →
    ys.length ≤ xs.length → borrow ≤ 1 →
    IsDigits (vISubGo xs ys borrow).1 ∧ (vISubGo xs ys borrow).2 ≤ 1 ∧
      (vISubGo xs ys borrow).1.length = xs.length ∧
      val (vISubGo xs ys borrow).1 + val ys + borrow =
        val xs + 2 ^ (30 * xs.length) * (vISubGo xs ys borrow).2
  | xs, [], borrow, h, _, _, hb => by
    obtain ⟨h1, h2, h3, h4⟩ := vISubTail_spec xs borrow h hb
    simp only [vISubGo, val_nil, Nat.add_zero]
    exact ⟨h1, h2, h3, h4⟩
  | x :: xs, y :: ys, borrow, h, hy, hl, hb => by
    have ⟨hx, hxs⟩ := isDigits_cons.1 h
    have ⟨hy0, hys⟩ := isDigits_cons.1 hy
    have ⟨s1, s2, s3⟩ := subU32_step hx hy0 hb
    obtain ⟨h1, h2, h3, h4⟩ := vISubGo_spec xs ys _ hxs hys (by simpa using hl) s2
    simp only [vISubGo]
    generalize subU32 x y borrow = t at *
    generalize hr : vISubGo xs ys ((t >>> 30) &&& 1) = r at *
    obtain ⟨z, cc⟩ := r
    simp only at h1 h2 h3 h4 ⊢
    refine ⟨isDigits_cons.2 ⟨s1, h1⟩, h2, by simp [h3], ?_⟩
    simp only [val_cons, List.length_cons]
    rw [show 30 * (xs.length + 1) = 30 + 30 * xs.length by omega, Nat.pow_add, Nat.mul_assoc]
    grind
  | [], _ :: _, _, _, _, hl, _ => by simp at hl

end PyLean.LongObj
