import PyLean.LongObj.DivOps

/-!
Shifts on the digit model: `long_rshift1`, `long_rshift`, `_PyLong_Rshift`,
`long_lshift1`, `long_lshift_method`, `long_lshift_int64`, `_PyLong_Lshift`,
longobject.c:5314-5550.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt

/-- `PyLong_AsInt64(b, &shiftby)` for `b >= 0`, as the shift code uses it: `none`
on overflow (the `PyErr_ExceptionMatches(PyExc_OverflowError)` branches). -/
def asInt64 (b : Int) : Option Nat :=
  if b < 2 ^ 63 then some b.toNat else none

/-! ## Right shift -/

/-- The loop of `long_rshift1`, longobject.c:5387-5391, and the store of the final
`accum` at :5393. -/
def rshiftLoop (hishift : Nat) : List Nat → Nat → Py (List Nat)
  | [], accum => .ok [u32 accum]
  | d :: ds, accum => do
    let acc ← chk64 (accum + (d <<< hishift))
    let r ← rshiftLoop hishift ds (acc >>> 30)
    return (acc &&& MASK) :: r

/-- `sticky |= ob_digit[j]`, longobject.c:5379-5382. -/
def stickyOf : List Nat → Nat → Nat
  | [], s => s
  | d :: ds, s => stickyOf ds (s ||| d)

/-- The compact path of `long_rshift1`, longobject.c:5326-5333: `~(~m >> shift)` for
negative `m`, on `stwodigits`. -/
def compactRshift (m : Int) (shift : Nat) : Int :=
  if m < 0 then -(((-m - 1) / 2 ^ shift)) - 1 else m / 2 ^ shift

/-- The general path of `long_rshift1`, longobject.c:5335-5396, after the
adjustment of `remshift` for a negative `a`. -/
def rshiftBig (neg : Bool) (ds : List Nat) (wordshift remshift : Nat) : Py Long :=
  let sizeA := ds.length
  if sizeA ≤ wordshift then .ok (if neg then ⟨true, [1]⟩ else ⟨false, []⟩)
  else do
    longAlloc (sizeA - wordshift)
    let hishift := 30 - remshift
    let accum := ds.getD wordshift 0
    let accum :=
      if neg then
        accum + ((MASK >>> hishift) + (if stickyOf (ds.take wordshift) 0 ≠ 0 then 1 else 0))
      else accum
    let accum := accum >>> remshift
    let z ← rshiftLoop hishift (ds.drop (wordshift + 1)) accum
    let n := normalize z
    return ⟨neg && !n.isEmpty, n⟩

/-- `long_rshift1(a, wordshift, remshift)`, longobject.c:5314-5397. -/
def longRshift1 (a : Long) (wordshift remshift : Nat) : Py Long :=
  if a.isCompact then
    .ok (fromSTwoDigits (compactRshift a.medium (if wordshift = 0 then remshift else 30)))
  else if a.neg then
    if remshift = 0 then
      if wordshift = 0 then .ok a
      else rshiftBig true a.ds (wordshift - 1) 30
    else rshiftBig true a.ds wordshift remshift
  else rshiftBig false a.ds wordshift remshift

/-- `_PyLong_Rshift(a, shiftby)`, longobject.c:5430-5453. The range check at
:5440-5449 is compiled out on a 64-bit build. -/
def pyLongRshift (a : Long) (shiftby : Nat) : Py Long :=
  if a.ds = [] then .ok ⟨false, []⟩
  else longRshift1 a (shiftby / 30) (shiftby % 30)

/-- `long_rshift(a, b)`, longobject.c:5400-5426. -/
def longRshift (a b : Long) : Py Long :=
  if b.neg then .error (.valueError "negative shift count")
  else if a.ds = [] then .ok ⟨false, []⟩
  else
    match asInt64 b.toInt with
    | none => .ok (if a.neg then ⟨true, [1]⟩ else ⟨false, []⟩)
    | some s => pyLongRshift a s

theorem ofInt_minus_one : Long.ofInt (-1) = ⟨true, [1]⟩ := by decide
theorem ofInt_zero : Long.ofInt 0 = ⟨false, []⟩ := by decide

theorem rshift_step_alg (acc low hi accum d h ds z B : Nat) (h1 : acc = accum + d * h)
    (h2 : low + B * hi = acc) (h3 : z = hi + h * ds) :
    low + B * z = accum + h * (d + B * ds) := by
  subst_vars
  grind

theorem rshiftLoop_spec {h : Nat} (hh : h ≤ 30) :
    ∀ (ds : List Nat) (accum : Nat), IsDigits ds → accum ≤ 2 ^ h → accum < 2 ^ 30 →
      ∃ z, rshiftLoop h ds accum = .ok z ∧ IsDigits z ∧ z.length = ds.length + 1 ∧
        val z = accum + 2 ^ h * val ds
  | [], accum, _, _, h2 => by
    have hu : u32 accum = accum := Nat.mod_eq_of_lt (by omega)
    refine ⟨[accum], by simp [rshiftLoop, hu], isDigits_cons.2 ⟨h2, isDigits_nil⟩, rfl, by simp⟩
  | d :: ds, accum, hd, h1, h2 => by
    have ⟨hd0, hds⟩ := isDigits_cons.1 hd
    have hshl : d <<< h = d * 2 ^ h := Nat.shiftLeft_eq d h
    have hm : (d + 1) * 2 ^ h ≤ 2 ^ 30 * 2 ^ h := Nat.mul_le_mul_right _ hd0
    have hm2 : (d + 1) * 2 ^ h = d * 2 ^ h + 2 ^ h := by grind
    have hp : 2 ^ 30 * 2 ^ h ≤ 2 ^ 30 * 2 ^ 30 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hh)
    have hacc : accum + d * 2 ^ h ≤ 2 ^ 30 * 2 ^ h := by omega
    have h64 : accum + d * 2 ^ h < 2 ^ 64 := by omega
    have ⟨c1, c2⟩ := carry_step (x := accum + d * 2 ^ h)
    have hhi1 : (accum + d * 2 ^ h) >>> 30 ≤ 2 ^ h := by
      rw [shr30]
      exact Nat.div_le_of_le_mul (by omega)
    have hhi2 : (accum + d * 2 ^ h) >>> 30 < 2 ^ 30 := by
      by_cases h30 : h = 30
      · subst h30
        rw [shr30]
        apply Nat.div_lt_of_lt_mul
        have : 2 ^ 30 * (d + 1) ≤ 2 ^ 30 * 2 ^ 30 := Nat.mul_le_mul_left _ hd0
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm d] at *
        omega
      · have : 2 ^ h ≤ 2 ^ 29 := Nat.pow_le_pow_right (by decide) (by omega)
        omega
    obtain ⟨z, hz, z1, z2, z3⟩ := rshiftLoop_spec hh ds _ hds hhi1 hhi2
    refine ⟨((accum + d * 2 ^ h) &&& MASK) :: z, ?_, isDigits_cons.2 ⟨c1, z1⟩, by simp [z2], ?_⟩
    · simp only [rshiftLoop, hshl, chk64_ok h64, bind_ok, hz, pure_ok]
    · rw [val_cons, val_cons]
      exact rshift_step_alg _ _ _ _ _ _ _ _ _ rfl c2 z3

theorem floor_neg_div (m : Int) (k : Nat) (hm : m < 0) :
    m / 2 ^ k = -(((-m - 1) / 2 ^ k)) - 1 := by
  obtain ⟨n, hn⟩ : ∃ n : Nat, m = -((n : Int) + 1) := ⟨(-m - 1).toNat, by omega⟩
  subst hn
  have hD : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
  have e1 : -(-((n : Int) + 1)) - 1 = (n : Int) := by omega
  rw [e1]
  have hmod := Int.emod_add_mul_ediv (n : Int) (2 ^ k)
  have hlt := Int.emod_lt_of_pos (n : Int) hD
  have hge := Int.emod_nonneg (n : Int) (Int.ne_of_gt hD)
  generalize hq : (n : Int) / 2 ^ k = q at *
  generalize hr : (n : Int) % 2 ^ k = r at *
  generalize hDD : (2 : Int) ^ k = D at *
  have : -((n : Int) + 1) = (D - 1 - r) + D * (-q - 1) := by
    rw [← hmod]; grind
  rw [this, Int.add_mul_ediv_left _ _ (by omega), Int.ediv_eq_zero_of_lt (by omega) (by omega)]
  omega

/-- The compact path of `long_rshift1` is floor division. -/
theorem compactRshift_eq (m : Int) (k : Nat) : compactRshift m k = m / 2 ^ k := by
  unfold compactRshift
  split
  · rename_i h; exact (floor_neg_div m k h).symm
  · rfl

/-- `wordshift`/`remshift` split of a shift: `B^w * 2^r`. -/
theorem shift_pow (w r : Nat) : 2 ^ (30 * w + r) = 2 ^ (30 * w) * 2 ^ r := Nat.pow_add _ _ _

theorem div_two_steps (A P Q : Nat) : A / (P * Q) = A / P / Q := (Nat.div_div_eq_div_mul A P Q).symm

/-- The non-negative general path of `long_rshift1` is the floor shift. -/
theorem rshiftBig_pos {ds : List Nat} {w r : Nat} (hd : IsDigits ds) (hr : r < 30)
    (hs : ds.length ≤ maxLongDigits) :
    rshiftBig false ds w r = .ok ⟨false, digitsOf (val ds / 2 ^ (30 * w + r))⟩ := by
  unfold rshiftBig
  by_cases hsz : ds.length ≤ w
  · simp only [hsz, ite_true]
    have hlt : val ds < 2 ^ (30 * w) := val_le_of_len hd hsz
    have : val ds < 2 ^ (30 * w + r) :=
      Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.div_eq_of_lt this]
    simp
  · simp only [hsz, ite_false]
    rw [longAlloc_ok (by omega)]
    simp only [bind_ok, Bool.false_eq_true, ite_false]
    have hdrop : ds.drop w = ds.getD w 0 :: ds.drop (w + 1) := by
      have hl : w < ds.length := by omega
      have e : ds.getD w 0 = ds[w] := by simp [List.getD, hl]
      rw [e]
      exact (List.drop_eq_getElem_cons hl)
    have hsplit := val_split (n := ds) (size := w) (by omega)
    rw [hdrop] at hsplit
    have dtail := isDigits_drop hd w
    rw [hdrop] at dtail
    obtain ⟨ht0, hts⟩ := isDigits_cons.1 dtail
    generalize ds.getD w 0 = t0 at *
    generalize hT : ds.drop (w + 1) = ts at *
    have hh : 30 - r ≤ 30 := by omega
    have hshr : t0 >>> r = t0 / 2 ^ r := by simp [Nat.shiftRight_eq_div_pow]
    have ht1 : t0 / 2 ^ r ≤ 2 ^ (30 - r) := by
      apply Nat.le_of_lt
      apply Nat.div_lt_of_lt_mul
      rw [← Nat.pow_add, show r + (30 - r) = 30 by omega]
      exact ht0
    have ht2 : t0 / 2 ^ r < 2 ^ 30 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ht0
    obtain ⟨z, hz, z1, _, z3⟩ := rshiftLoop_spec hh ts (t0 / 2 ^ r) hts ht1 ht2
    simp only [hshr, hz, bind_ok, pure_ok]
    rw [digitsOf_normalize z1, z3]
    have hval : val ds / 2 ^ (30 * w + r) = t0 / 2 ^ r + 2 ^ (30 - r) * val ts := by
      have hL : val (ds.take w) < 2 ^ (30 * w) :=
        val_le_of_len (isDigits_take hd w) (by simp; omega)
      rw [shift_pow, div_two_steps, hsplit]
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hL, Nat.zero_add]
      simp only [val_cons]
      have e : (2 : Nat) ^ 30 = 2 ^ r * 2 ^ (30 - r) := by
        rw [← Nat.pow_add, show r + (30 - r) = 30 by omega]
      rw [e, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]
    rw [hval]
    simp

theorem stickyOf_mono : ∀ (l : List Nat) (s : Nat), s ≠ 0 → stickyOf l s ≠ 0
  | [], _, h => h
  | d :: ds, s, h => stickyOf_mono ds _ (by
      intro h0
      exact h (Nat.or_eq_zero_iff.1 h0).1)

/-- The sticky bit is set exactly when a low digit is non-zero. -/
theorem stickyOf_zero_iff : ∀ (l : List Nat), stickyOf l 0 = 0 ↔ val l = 0
  | [] => by simp [stickyOf]
  | d :: ds => by
    simp only [stickyOf, Nat.zero_or, val_cons]
    have ih := stickyOf_zero_iff ds
    constructor
    · intro h
      have hd : d = 0 := by
        rcases Nat.eq_zero_or_pos d with h0 | h0
        · exact h0
        · exact absurd h (stickyOf_mono ds d (by omega))
      subst hd
      have := ih.1 h
      simp [this]
    · intro h
      have hd : d = 0 := by omega
      have hv : val ds = 0 := by
        have : 2 ^ 30 * val ds = 0 := by omega
        exact (Nat.mul_eq_zero.1 this).resolve_left (by decide)
      subst hd
      exact ih.2 hv

theorem mask_shr {h : Nat} (hh : h ≤ 30) : MASK >>> h = 2 ^ (30 - h) - 1 := by
  have e : MASK = 2 ^ (30 - h) * 2 ^ h - 1 := by
    rw [← Nat.pow_add, show 30 - h + h = 30 by omega]; rfl
  have hp : 0 < 2 ^ h := Nat.two_pow_pos h
  have hq : 0 < 2 ^ (30 - h) := Nat.two_pow_pos _
  rw [Nat.shiftRight_eq_div_pow, e]
  generalize 2 ^ (30 - h) = P at *
  generalize 2 ^ h = Q at *
  have e2 : P * Q - 1 = (P - 1) * Q + (Q - 1) := by
    obtain ⟨P', rfl⟩ : ∃ k, P = k + 1 := ⟨P - 1, by omega⟩
    have : (P' + 1) * Q = P' * Q + Q := by grind
    simp only [Nat.add_sub_cancel]
    omega
  rw [e2, Nat.mul_comm (P - 1), Nat.mul_add_div hp, Nat.div_eq_of_lt (by omega), Nat.add_zero]

/-- `(A - 1) / X` in terms of the top part and the sticky digit. -/
theorem ceil_split {X L T A e : Nat} (hX : 0 < X) (hL : L < X) (hA : A = L + X * T) (hA1 : 1 ≤ A)
    (he : e = if L ≠ 0 then 1 else 0) : (A - 1) / X + 1 = T + e := by
  by_cases h0 : L = 0
  · subst h0
    simp only [ne_eq, not_true_eq_false, ite_false] at he
    subst he
    have hT : 1 ≤ T := by
      rcases Nat.eq_zero_or_pos T with h | h
      · subst h; simp at hA; omega
      · exact h
    obtain ⟨S, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
    have e1 : A - 1 = (X - 1) + X * S := by
      have : X * (S + 1) = X * S + X := by grind
      omega
    rw [e1, Nat.add_mul_div_left _ _ hX, Nat.div_eq_of_lt (by omega)]
    omega
  · simp only [ne_eq, h0, not_false_eq_true, ite_true] at he
    subst he
    have e1 : A - 1 = (L - 1) + X * T := by omega
    rw [e1, Nat.add_mul_div_left _ _ hX, Nat.div_eq_of_lt (by omega)]
    omega

theorem floor_neg_nat (A k : Nat) (hA : 1 ≤ A) :
    (-(A : Int)) / 2 ^ k = -(((A - 1) / 2 ^ k + 1 : Nat) : Int) := by
  rw [floor_neg_div _ _ (by omega)]
  have e : -(-(A : Int)) - 1 = ((A - 1 : Nat) : Int) := by omega
  have e2 : ((((A - 1) / 2 ^ k : Nat)) : Int) = ((A - 1 : Nat) : Int) / (2 : Int) ^ k := by
    rw [Int.natCast_ediv, cast_two_pow]
  rw [e, ← e2]
  omega

/-- The negative general path of `long_rshift1`: `0 < remshift <= SHIFT`. -/
theorem rshiftBig_neg {ds : List Nat} {w r : Nat} (hd : IsDigits ds) (hn : Normal ds)
    (hne : ds ≠ []) (hr1 : 1 ≤ r) (hr : r ≤ 30) (hs : ds.length ≤ maxLongDigits) :
    rshiftBig true ds w r = .ok (Long.ofInt (-(val ds : Int) / 2 ^ (30 * w + r))) := by
  have hA1 : 1 ≤ val ds := by
    rcases Nat.eq_zero_or_pos (val ds) with h | h
    · exact absurd (eq_nil_of_val_zero hn h) hne
    · exact h
  rw [floor_neg_nat _ _ hA1, Long.ofInt_neg_natCast (Nat.succ_pos _)]
  unfold rshiftBig
  by_cases hsz : ds.length ≤ w
  · simp only [hsz, ite_true]
    have hlt : val ds < 2 ^ (30 * w) := val_le_of_len hd hsz
    have hpw : 2 ^ (30 * w) ≤ 2 ^ (30 * w + r) := Nat.pow_le_pow_right (by decide) (by omega)
    have : val ds - 1 < 2 ^ (30 * w + r) := by omega
    rw [Nat.div_eq_of_lt this]
    have h1 : digitsOf 1 = [1] := by decide
    simp [h1]
  · simp only [hsz, ite_false]
    rw [longAlloc_ok (by omega)]
    simp only [bind_ok, ite_true]
    have hl : w < ds.length := by omega
    have hdrop : ds.drop w = ds.getD w 0 :: ds.drop (w + 1) := by
      have e : ds.getD w 0 = ds[w] := by simp [List.getD, hl]
      rw [e]
      exact (List.drop_eq_getElem_cons hl)
    have hsplit := val_split (n := ds) (size := w) (by omega)
    rw [hdrop] at hsplit
    have dtail := isDigits_drop hd w
    rw [hdrop] at dtail
    obtain ⟨ht0, hts⟩ := isDigits_cons.1 dtail
    have hL : val (ds.take w) < 2 ^ (30 * w) :=
      val_le_of_len (isDigits_take hd w) (by simp; omega)
    have hst : (if stickyOf (ds.take w) 0 ≠ 0 then 1 else 0) =
        (if val (ds.take w) ≠ 0 then 1 else 0) := by
      by_cases h : val (ds.take w) = 0
      · simp [h, (stickyOf_zero_iff _).2 h]
      · have : stickyOf (ds.take w) 0 ≠ 0 := fun h2 => h ((stickyOf_zero_iff _).1 h2)
        simp [h, this]
    rw [hst]
    generalize he : (if val (ds.take w) ≠ 0 then 1 else 0) = e at *
    have he1 : e ≤ 1 := by rw [← he]; split <;> omega
    generalize ds.getD w 0 = t0 at *
    generalize ds.drop (w + 1) = ts at *
    rw [mask_shr (by omega)]
    have hh : 30 - r ≤ 30 := by omega
    have hrr : 30 - (30 - r) = r := by omega
    rw [hrr]
    have hpr : 1 ≤ 2 ^ r := Nat.two_pow_pos r
    have hshr : (t0 + (2 ^ r - 1 + e)) >>> r = (t0 + (2 ^ r - 1 + e)) / 2 ^ r := by
      simp [Nat.shiftRight_eq_div_pow]
    have hph : 2 ^ r * 2 ^ (30 - r) = 2 ^ 30 := by
      rw [← Nat.pow_add, show r + (30 - r) = 30 by omega]
    have ht1 : (t0 + (2 ^ r - 1 + e)) / 2 ^ r ≤ 2 ^ (30 - r) := by
      have : (t0 + (2 ^ r - 1 + e)) / 2 ^ r < 2 ^ (30 - r) + 1 := by
        apply Nat.div_lt_of_lt_mul
        rw [Nat.mul_add, Nat.mul_one, hph]
        omega
      omega
    have ht2 : (t0 + (2 ^ r - 1 + e)) / 2 ^ r < 2 ^ 30 := by
      have : 2 ^ (30 - r) ≤ 2 ^ 29 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    obtain ⟨z, hz, z1, _, z3⟩ := rshiftLoop_spec hh ts _ hts ht1 ht2
    simp only [hshr, hz, bind_ok, pure_ok]
    have hval : val z = (val ds - 1) / 2 ^ (30 * w + r) + 1 := by
      rw [z3, shift_pow, div_two_steps]
      have hc := ceil_split (Nat.two_pow_pos (30 * w)) hL hsplit hA1 he.symm
      generalize hQ : (val ds - 1) / 2 ^ (30 * w) = Q at *
      simp only [val_cons] at hc
      have e2 : Q + 2 ^ r = (t0 + (2 ^ r - 1 + e)) + 2 ^ r * (2 ^ (30 - r) * val ts) := by
        rw [← Nat.mul_assoc, hph]
        omega
      have e3 : (Q + 2 ^ r) / 2 ^ r = Q / 2 ^ r + 1 := Nat.add_div_right _ (Nat.two_pow_pos r)
      rw [e2, Nat.add_mul_div_left _ _ (Nat.two_pow_pos r)] at e3
      exact e3
    rw [digitsOf_normalize z1, hval]
    have hne2 : digitsOf ((val ds - 1) / 2 ^ (30 * w + r) + 1) ≠ [] := by
      rw [Ne, digitsOf_eq_nil]; exact Nat.succ_ne_zero _
    have hemp : (digitsOf ((val ds - 1) / 2 ^ (30 * w + r) + 1)).isEmpty = false := by
      cases hh2 : digitsOf ((val ds - 1) / 2 ^ (30 * w + r) + 1) with
      | nil => exact absurd hh2 hne2
      | cons _ _ => rfl
    simp [hemp]

theorem compact_shift_range {m : Int} (hm : m.natAbs < 2 ^ 30) (k : Nat) :
    -(2 ^ 63 : Int) ≤ m / 2 ^ k ∧ m / 2 ^ k < 2 ^ 63 := by
  have hp0 : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
  by_cases h : m < 0
  · rw [floor_neg_div m k h]
    have h1 : 0 ≤ (-m - 1) / (2 : Int) ^ k := Int.ediv_nonneg (by omega) (Int.le_of_lt hp0)
    have h2 : (-m - 1) / (2 : Int) ^ k ≤ -m - 1 := Int.ediv_le_self _ (by omega)
    omega
  · have h1 : 0 ≤ m / (2 : Int) ^ k := Int.ediv_nonneg (by omega) (Int.le_of_lt hp0)
    have h2 : m / (2 : Int) ^ k ≤ m := Int.ediv_le_self _ (by omega)
    omega

/-- Above the digit width of a compact value, the floor shift no longer depends on `k`. -/
theorem compact_shift_saturates {m : Int} (hm : m.natAbs < 2 ^ 30) {k : Nat} (hk : 30 ≤ k) :
    m / 2 ^ k = m / 2 ^ 30 := by
  have sat : ∀ j : Nat, 30 ≤ j → m / (2 : Int) ^ j = if m < 0 then -1 else 0 := by
    intro j hj
    have hn : (2 : Nat) ^ 30 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hj
    have hp : (2 : Int) ^ 30 ≤ 2 ^ j := by
      rw [← cast_two_pow, ← cast_two_pow]
      exact Int.ofNat_le.2 hn
    by_cases h : m < 0
    · rw [if_pos h, floor_neg_div m j h, Int.ediv_eq_zero_of_lt (by omega) (by omega)]
      omega
    · rw [if_neg h, Int.ediv_eq_zero_of_lt (by omega) (by omega)]
  rw [sat k hk, sat 30 (by omega)]

/-- `long_rshift1(a, s / SHIFT, s % SHIFT)` is the canonical object of the floor shift. -/
theorem longRshift1_spec (a : Int) (s : Nat) (hs : digitCount a.natAbs ≤ maxLongDigits) :
    longRshift1 (Long.ofInt a) (s / 30) (s % 30) = .ok (Long.ofInt (a / 2 ^ s)) := by
  unfold longRshift1
  by_cases hc : (Long.ofInt a).isCompact = true
  · simp only [hc, ite_true]
    have hm : a.natAbs < 2 ^ 30 := by
      rw [Long.isCompact_ofInt] at hc
      exact of_decide_eq_true hc
    rw [Long.medium_ofInt hm, compactRshift_eq]
    by_cases h0 : s / 30 = 0
    · have : s % 30 = s := by omega
      simp only [h0, ite_true, this]
      obtain ⟨r1, r2⟩ := compact_shift_range hm s
      rw [fromSTwoDigits_eq r1 r2]
    · simp only [h0, ite_false]
      obtain ⟨r1, r2⟩ := compact_shift_range hm 30
      rw [fromSTwoDigits_eq r1 r2, compact_shift_saturates hm (k := s) (by omega)]
  · simp only [hc, Bool.false_eq_true, ite_false]
    have hne : digitsOf a.natAbs ≠ [] := by
      intro h
      have h0 := digitsOf_eq_nil.1 h
      apply hc
      rw [Long.isCompact_ofInt]
      simp [h0]
    have dA := digitsOf_digits a.natAbs
    have nA := normal_digitsOf a.natAbs
    have lA : (digitsOf a.natAbs).length ≤ maxLongDigits := by rw [length_digitsOf]; exact hs
    have hsplit : 30 * (s / 30) + s % 30 = s := by omega
    by_cases hn : a < 0
    · have hneg : (Long.ofInt a).neg = true := decide_eq_true hn
      simp only [hneg, ite_true]
      have ha : a = -(val (digitsOf a.natAbs) : Int) := by rw [val_digitsOf]; omega
      by_cases hr : s % 30 = 0
      · simp only [hr, ite_true]
        by_cases hw : s / 30 = 0
        · have hs0 : s = 0 := by omega
          simp only [hw, ite_true]
          subst hs0
          simp
        · simp only [hw, ite_false]
          have e : 30 * (s / 30 - 1) + 30 = s := by omega
          have := rshiftBig_neg (w := s / 30 - 1) (r := 30) dA nA hne (by omega) (by omega) lA
          rw [e, ← ha] at this
          exact this
      · simp only [hr, ite_false]
        have := rshiftBig_neg (w := s / 30) (r := s % 30) dA nA hne (by omega) (by omega) lA
        rw [hsplit, ← ha] at this
        exact this
    · have hneg : (Long.ofInt a).neg = false := decide_eq_false hn
      simp only [hneg, Bool.false_eq_true, ite_false]
      have := rshiftBig_pos (w := s / 30) (r := s % 30) dA (by omega) lA
      rw [hsplit, val_digitsOf] at this
      have e : ((a.natAbs : Nat) : Int) = a := by omega
      have e2 : Long.ofInt (a / 2 ^ s) = ⟨false, digitsOf (a.natAbs / 2 ^ s)⟩ := by
        have : a / 2 ^ s = ((a.natAbs / 2 ^ s : Nat) : Int) := by
          rw [Int.natCast_ediv, cast_two_pow, e]
        rw [this, Long.ofInt_natCast]
      rw [e2]
      exact this

/-- A shift of at least `2^63` bits passes every digit a real object can have. -/
theorem huge_shift (a b : Int) (hs : digitCount a.natAbs ≤ maxLongDigits) (hb : (2 : Int) ^ 63 ≤ b) :
    a / 2 ^ b.toNat = if a < 0 then -1 else 0 := by
  have h1 : a.natAbs < 2 ^ (30 * digitCount a.natAbs) := (digitCount_spec _).1
  have h2 : 2 ^ (30 * digitCount a.natAbs) ≤ 2 ^ b.toNat :=
    Nat.pow_le_pow_right (by decide) (by simp only [maxLongDigits] at hs; omega)
  have hb2 : (a.natAbs : Int) < 2 ^ b.toNat := by
    rw [← cast_two_pow]; omega
  by_cases h : a < 0
  · rw [if_pos h, floor_neg_div a _ h, Int.ediv_eq_zero_of_lt (by omega) (by omega)]
    omega
  · rw [if_neg h, Int.ediv_eq_zero_of_lt (by omega) (by omega)]

/-- `a >> b` is the floor shift for every `b >= 0`, on all three of the compact path,
the general path and the overflow-of-`int64_t` path; a negative `b` raises `ValueError`. -/
theorem longRshift_spec (a b : Int) (hs : digitCount a.natAbs ≤ maxLongDigits) :
    longRshift (Long.ofInt a) (Long.ofInt b) =
      if b < 0 then .error (.valueError "negative shift count")
      else .ok (Long.ofInt (a / 2 ^ b.toNat)) := by
  unfold longRshift
  by_cases hb : b < 0
  · have : (Long.ofInt b).neg = true := decide_eq_true hb
    simp [this, hb]
  · have hneg : (Long.ofInt b).neg = false := decide_eq_false hb
    simp only [hneg, Bool.false_eq_true, ite_false, hb, Long.toInt_ofInt]
    by_cases ha : a = 0
    · subst ha
      simp [Long.ofInt]
    · have hne : (Long.ofInt a).ds ≠ [] := by
        simp only [Long.ofInt, Ne, digitsOf_eq_nil]; omega
      simp only [hne, ite_false, asInt64]
      by_cases hbig : b < 2 ^ 63
      · simp only [hbig, ite_true, pyLongRshift, hne]
        exact longRshift1_spec a b.toNat hs
      · simp only [hbig, ite_false]
        rw [huge_shift a b hs (by omega)]
        by_cases hn : a < 0
        · have : (Long.ofInt a).neg = true := decide_eq_true hn
          simp only [this, ite_true, hn, ofInt_minus_one]
        · have : (Long.ofInt a).neg = false := decide_eq_false hn
          simp only [this, Bool.false_eq_true, ite_false, hn, ofInt_zero]

/-! ## Left shift -/

/-- The compact path of `long_lshift1`, longobject.c:5462-5467: `-(-m << remshift)`. -/
def compactLshift (m : Int) (r : Nat) : Int :=
  if m < 0 then -((-m) * 2 ^ r) else m * 2 ^ r

/-- `long_lshift1(a, wordshift, remshift)`, longobject.c:5456-5494. The digit loop at
:5483-5487 is the loop of `v_lshift`, carry going through `accum`. -/
def longLshift1 (a : Long) (wordshift remshift : Nat) : Py Long :=
  if wordshift = 0 ∧ a.isCompact = true then do
    let x ← chkS64 (compactLshift a.medium remshift)
    return fromSTwoDigits x
  else do
    longAlloc (a.ds.length + wordshift + (if remshift ≠ 0 then 1 else 0))
    let p := vLshiftGo remshift a.ds 0
    let z := List.replicate wordshift 0 ++ p.1 ++ (if remshift ≠ 0 then [p.2] else [])
    let n := normalize z
    return ⟨a.neg && !n.isEmpty, n⟩

/-- `long_lshift_int64(a, shiftby)` and `_PyLong_Lshift`, longobject.c:5525-5550. The test
3.15 changed, :5532-5540, is under `#if PY_SSIZE_T_MAX <= INT64_MAX / PyLong_SHIFT`, which
is false on a 64-bit build, so it is not compiled here. -/
def longLshiftInt64 (a : Long) (shiftby : Nat) : Py Long :=
  if a.ds = [] then .ok ⟨false, []⟩
  else longLshift1 a (shiftby / 30) (shiftby % 30)

/-- `long_lshift_method(aa, bb)`, longobject.c:5498-5521. -/
def longLshift (a b : Long) : Py Long :=
  if b.neg then .error (.valueError "negative shift count")
  else if a.ds = [] then .ok ⟨false, []⟩
  else
    match asInt64 b.toInt with
    | none => .error (.overflowError "too many digits in integer")
    | some s => longLshiftInt64 a s

theorem lshift_value {ds : List Nat} {w r : Nat} (hd : IsDigits ds) (hr : r < 30) :
    let p := vLshiftGo r ds 0
    let z := List.replicate w 0 ++ p.1 ++ (if r ≠ 0 then [p.2] else [])
    IsDigits z ∧ val z = val ds * 2 ^ (30 * w + r) := by
  obtain ⟨h1, h2, h3, h4⟩ := vLshiftGo_spec hr ds 0 hd (Nat.two_pow_pos r)
  simp only [Nat.add_zero] at h4
  generalize vLshiftGo r ds 0 = p at *
  obtain ⟨y, c⟩ := p
  simp only at h1 h2 h3 h4 ⊢
  have hr0 : val y + 2 ^ (30 * ds.length) * c = val (y ++ (if r ≠ 0 then [c] else [])) := by
    by_cases h : r = 0
    · subst h
      have hc : c = 0 := by simpa using h3
      subst hc
      simp
    · simp only [ne_eq, h, not_false_eq_true, ite_true]
      rw [val_append, h2]
      simp
  constructor
  · refine isDigits_append.2 ⟨isDigits_append.2 ⟨isDigits_replicate_zero _, h1⟩, ?_⟩
    split
    · exact isDigits_cons.2 ⟨by
        have : 2 ^ r ≤ 2 ^ 29 := Nat.pow_le_pow_right (by decide) (by omega)
        omega, isDigits_nil⟩
    · exact isDigits_nil
  · rw [List.append_assoc, val_append, val_replicate_zero, Nat.zero_add, List.length_replicate,
      ← hr0, h4, Nat.pow_add]
    grind

/-- The size `long_lshift1` asks `long_alloc` for, longobject.c:5469-5473:
`oldsize + wordshift`, plus one when `remshift` is non-zero. -/
def lshiftNeed (a : Int) (s : Nat) : Nat :=
  digitCount a.natAbs + s / 30 + (if s % 30 ≠ 0 then 1 else 0)

/-- `long_lshift1` on `s / SHIFT`, `s % SHIFT` is the canonical `a * 2**s`. The
hypothesis is exactly the room `long_alloc` needs. -/
theorem longLshift1_spec (a : Int) (s : Nat)
    (hs : lshiftNeed a s ≤ maxLongDigits) :
    longLshift1 (Long.ofInt a) (s / 30) (s % 30) = .ok (Long.ofInt (a * 2 ^ s)) := by
  unfold longLshift1
  by_cases hfast : s / 30 = 0 ∧ (Long.ofInt a).isCompact = true
  · simp only [hfast, and_self, ite_true]
    have hm : a.natAbs < 2 ^ 30 := by
      have := hfast.2
      rw [Long.isCompact_ofInt] at this
      exact of_decide_eq_true this
    have hs30 : s < 30 := by omega
    have hmod : s % 30 = s := by omega
    have hp : 2 ^ s ≤ 2 ^ 29 := Nat.pow_le_pow_right (by decide) (by omega)
    have hbound : (a * 2 ^ s).natAbs < 2 ^ 60 := by
      rw [Int.natAbs_mul, Int.natAbs_pow]
      have e : Int.natAbs 2 = 2 := rfl
      rw [e]
      have := Nat.mul_lt_mul_of_lt_of_le hm hp (Nat.two_pow_pos 29)
      omega
    have hc : compactLshift a s = a * 2 ^ s := by
      unfold compactLshift
      split
      · rw [Int.neg_mul, Int.neg_neg]
      · rfl
    rw [Long.medium_ofInt hm, hmod, hc, chkS64_ok (by omega)]
    simp only [bind_ok, pure_ok]
    rw [fromSTwoDigits_eq (by omega) (by omega)]
  · rw [if_neg hfast]
    have dA := digitsOf_digits a.natAbs
    have lA := length_digitsOf a.natAbs
    have hlen : (Long.ofInt a).ds.length + s / 30 + (if s % 30 ≠ 0 then 1 else 0) ≤ maxLongDigits := by
      simp only [Long.ofInt, lA]
      exact hs
    rw [longAlloc_ok hlen]
    simp only [bind_ok, pure_ok]
    have hv := lshift_value (w := s / 30) (r := s % 30) dA (by omega)
    simp only at hv
    have hds : (Long.ofInt a).ds = digitsOf a.natAbs := rfl
    rw [hds, digitsOf_normalize hv.1, hv.2, val_digitsOf,
      show 30 * (s / 30) + s % 30 = s by omega]
    by_cases hn : a < 0
    · have hpos : 0 < a.natAbs * 2 ^ s := Nat.mul_pos (by omega) (Nat.two_pow_pos s)
      have e : a * 2 ^ s = -((a.natAbs * 2 ^ s : Nat) : Int) := by
        have h1 : ((a.natAbs * 2 ^ s : Nat) : Int) = (a.natAbs : Int) * 2 ^ s := by
          rw [Int.natCast_mul, cast_two_pow]
        have h2 : (a.natAbs : Int) = -a := by omega
        rw [h1, h2, Int.neg_mul, Int.neg_neg]
      rw [e, Long.ofInt_neg_natCast hpos]
      have hne : digitsOf (a.natAbs * 2 ^ s) ≠ [] := by rw [Ne, digitsOf_eq_nil]; omega
      have hemp : (digitsOf (a.natAbs * 2 ^ s)).isEmpty = false := by
        cases hh2 : digitsOf (a.natAbs * 2 ^ s) with
        | nil => exact absurd hh2 hne
        | cons _ _ => rfl
      have hneg : (Long.ofInt a).neg = true := decide_eq_true hn
      simp [hneg, hemp]
    · have e : a * 2 ^ s = ((a.natAbs * 2 ^ s : Nat) : Int) := by
        have h1 : ((a.natAbs * 2 ^ s : Nat) : Int) = (a.natAbs : Int) * 2 ^ s := by
          rw [Int.natCast_mul, cast_two_pow]
        have h2 : (a.natAbs : Int) = a := by omega
        rw [h1, h2]
      rw [e, Long.ofInt_natCast]
      have hneg : (Long.ofInt a).neg = false := decide_eq_false hn
      simp [hneg]

/-- `a << b`: `ValueError` for `b < 0`, `0` for `a == 0`, the exact product while the
result can be allocated, and `OverflowError` when `b` does not fit `int64_t`. -/
theorem longLshift_spec (a b : Int) :
    (b < 0 → longLshift (Long.ofInt a) (Long.ofInt b) =
      .error (.valueError "negative shift count")) ∧
    (0 ≤ b → a = 0 → longLshift (Long.ofInt a) (Long.ofInt b) = .ok (Long.ofInt 0)) ∧
    (a ≠ 0 → (2 : Int) ^ 63 ≤ b → longLshift (Long.ofInt a) (Long.ofInt b) =
      .error (.overflowError "too many digits in integer")) ∧
    (0 ≤ b → b < 2 ^ 63 → digitCount a.natAbs + b.toNat / 30 + 1 ≤ maxLongDigits →
      longLshift (Long.ofInt a) (Long.ofInt b) = .ok (Long.ofInt (a * 2 ^ b.toNat))) := by
  refine ⟨fun hb => ?_, fun hb ha => ?_, fun ha hb => ?_, fun hb hb2 hs => ?_⟩
  · have : (Long.ofInt b).neg = true := decide_eq_true hb
    simp [longLshift, this]
  · subst ha
    have : (Long.ofInt b).neg = false := decide_eq_false (by omega)
    simp [longLshift, this, Long.ofInt]
    exact hb
  · have hneg : (Long.ofInt b).neg = false := decide_eq_false (by omega)
    have hne : (Long.ofInt a).ds ≠ [] := by
      simp only [Long.ofInt, Ne, digitsOf_eq_nil]; omega
    have hc : ¬ b < 2 ^ 63 := by omega
    simp only [longLshift, hneg, Bool.false_eq_true, ite_false, hne, asInt64, Long.toInt_ofInt, hc]
  · have hneg : (Long.ofInt b).neg = false := decide_eq_false (by omega)
    by_cases ha : a = 0
    · subst ha
      simp [longLshift, hneg, Long.ofInt]
      exact hb
    · have hne : (Long.ofInt a).ds ≠ [] := by
        simp only [Long.ofInt, Ne, digitsOf_eq_nil]; omega
      simp only [longLshift, hneg, Bool.false_eq_true, ite_false, hne, asInt64, Long.toInt_ofInt,
        hb2, ite_true, longLshiftInt64]
      exact longLshift1_spec a b.toNat (by unfold lshiftNeed; split <;> omega)

/-- When `long_alloc` refuses the size, `long_lshift1` raises its OverflowError
(longobject.c:163-166 through :5473-5475). The compact shortcut (:5462-5467) cannot
be taken: it needs `wordshift == 0`, and then the size is at most 2. -/
theorem longLshift1_overflow (a : Int) (s : Nat) (hs : maxLongDigits < lshiftNeed a s) :
    longLshift1 (Long.ofInt a) (s / 30) (s % 30) =
      .error (.overflowError "too many digits in integer") := by
  have hm : maxLongDigits = 307445734561825860 := by decide
  unfold lshiftNeed at hs
  have hfast : ¬ (s / 30 = 0 ∧ (Long.ofInt a).isCompact = true) := by
    rintro ⟨h1, h2⟩
    rw [Long.isCompact_ofInt] at h2
    have := (digitCount_le_one_iff a.natAbs).2 (of_decide_eq_true h2)
    split at hs <;> omega
  unfold longLshift1
  rw [if_neg hfast]
  have hl : (Long.ofInt a).ds.length = digitCount a.natAbs := length_digitsOf _
  have hal : longAlloc ((Long.ofInt a).ds.length + s / 30 + (if s % 30 ≠ 0 then 1 else 0)) =
      .error (.overflowError "too many digits in integer") := by
    unfold longAlloc
    rw [if_pos (by rw [hl]; exact hs)]
  rw [hal]
  rfl

/-- `long_lshift_int64(a, shiftby)` and `_PyLong_Lshift`, for every `shiftby >= 0`: `0`
for `a == 0`, the canonical `a * 2**shiftby` when `long_alloc` accepts the size, and its
OverflowError otherwise. CPython can still raise MemoryError where the size is accepted
but the memory is not there; allocation failure is outside the model. -/
theorem longLshiftInt64_spec (a : Int) (s : Nat) :
    longLshiftInt64 (Long.ofInt a) s =
      if a = 0 then .ok (Long.ofInt 0)
      else if lshiftNeed a s ≤ maxLongDigits then .ok (Long.ofInt (a * 2 ^ s))
      else .error (.overflowError "too many digits in integer") := by
  by_cases ha : a = 0
  · subst ha
    simp [longLshiftInt64, Long.ofInt]
  · have hne : (Long.ofInt a).ds ≠ [] := by
      simp only [Long.ofInt, Ne, digitsOf_eq_nil]; omega
    rw [if_neg ha]
    unfold longLshiftInt64
    rw [if_neg hne]
    by_cases hs : lshiftNeed a s ≤ maxLongDigits
    · rw [if_pos hs, longLshift1_spec a s hs]
    · rw [if_neg hs, longLshift1_overflow a s (by omega)]

/-- `long_lshift_method` on two ints with `0 <= b < 2**63` is `long_lshift_int64`. -/
theorem longLshift_int64 (a b : Int) (hb : 0 ≤ b) (hb2 : b < 2 ^ 63) :
    longLshift (Long.ofInt a) (Long.ofInt b) = longLshiftInt64 (Long.ofInt a) b.toNat := by
  have hneg : (Long.ofInt b).neg = false := decide_eq_false (by omega)
  by_cases ha : a = 0
  · subst ha
    simp [longLshift, longLshiftInt64, hneg, Long.ofInt]
    exact hb
  · have hne : (Long.ofInt a).ds ≠ [] := by
      simp only [Long.ofInt, Ne, digitsOf_eq_nil]; omega
    simp only [longLshift, hneg, Bool.false_eq_true, ite_false, hne, asInt64, Long.toInt_ofInt,
      hb2, ite_true]

end PyLean.LongObj
