import PyLean.LongObj.Knuth
import PyLean.MathInt.Divmod

/-!
Digit-level division: `v_lshift`, `v_rshift`, `inplace_divrem1`, `divrem1`,
`inplace_rem1`, `rem1`, `x_divrem`, `long_divrem`, `long_rem`, `l_divmod`, `l_mod`,
`long_div`, `long_mod` and `long_divmod`, longobject.c.

`MathInt.divmod` treated `long_divrem` as exact truncated division.
`lDivmod_eq` discharges that assumption: the digit-level `l_divmod` here returns
the canonical objects of `MathInt.divmod`, so `MathInt.DivmodFloor` holds of it too.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt

/-! ## Vector shifts -/

/-- `v_lshift(z, a, m, d)`, longobject.c:1830-1842, returning `z` and the final carry. -/
def vLshiftGo (d : Nat) : List Nat → Nat → List Nat × Nat
  | [], carry => ([], carry)
  | a :: as, carry =>
    let acc := (a <<< d) ||| carry
    let (r, c) := vLshiftGo d as (u32 (acc >>> 30))
    ((u32 acc &&& MASK) :: r, c)

/-- `v_rshift(z, a, m, d)`, longobject.c:1848-1861: the C loop runs from the top
digit down, which is this recursion's return order. Returns `z` and the final carry. -/
def vRshiftGo (d : Nat) : List Nat → List Nat × Nat
  | [] => ([], 0)
  | a :: as =>
    let (zs, carry) := vRshiftGo d as
    let acc := (carry <<< 30) ||| a
    (u32 (acc >>> d) :: zs, u32 acc &&& (2 ^ d - 1))

theorem lshift_alg (low B r P c hi a d carry as : Nat)
    (h1 : low + B * hi = a * d + carry) (h2 : r + P * c = as * d + hi) :
    (low + B * r) + (B * P) * c = (a + B * as) * d + carry := by
  subst_vars
  grind

theorem vLshiftGo_spec {d : Nat} (hd : d < 30) : ∀ (as : List Nat) (carry : Nat), IsDigits as →
    carry < 2 ^ d →
    IsDigits (vLshiftGo d as carry).1 ∧ (vLshiftGo d as carry).1.length = as.length ∧
      (vLshiftGo d as carry).2 < 2 ^ d ∧
      val (vLshiftGo d as carry).1 + 2 ^ (30 * as.length) * (vLshiftGo d as carry).2
        = val as * 2 ^ d + carry
  | [], carry, _, hc => by simp [vLshiftGo, isDigits_nil, hc]
  | a :: as, carry, h, hc => by
    have ⟨ha, has⟩ := isDigits_cons.1 h
    have hpd : 2 ^ d ≤ 2 ^ 29 := Nat.pow_le_pow_right (by decide) (by omega)
    have hacc : (a <<< d) ||| carry = a * 2 ^ d + carry := shl_or a carry d hc
    have hm : (a + 1) * 2 ^ d ≤ 2 ^ 30 * 2 ^ d := Nat.mul_le_mul_right _ ha
    have hm2 : (a + 1) * 2 ^ d = a * 2 ^ d + 2 ^ d := by grind
    have hlt : a * 2 ^ d + carry < 2 ^ 30 * 2 ^ d := by omega
    have hlt32 : 2 ^ 30 * 2 ^ d ≤ 2 ^ 30 * 2 ^ 29 := Nat.mul_le_mul_left _ hpd
    simp only [vLshiftGo, hacc]
    generalize hA : a * 2 ^ d + carry = A at *
    have hhi : A / 2 ^ 30 < 2 ^ d := Nat.div_lt_of_lt_mul hlt
    have hu : u32 (A >>> 30) = A / 2 ^ 30 := by
      rw [shr30]; exact Nat.mod_eq_of_lt (by omega)
    have hlo : u32 A &&& MASK = A % 2 ^ 30 := by
      rw [and30]
      exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))
    rw [hu, hlo]
    obtain ⟨h1, h2, h3, h4⟩ := vLshiftGo_spec hd as (A / 2 ^ 30) has hhi
    generalize vLshiftGo d as (A / 2 ^ 30) = p at *
    obtain ⟨r, c⟩ := p
    simp only at h1 h2 h3 h4 ⊢
    refine ⟨isDigits_cons.2 ⟨Nat.mod_lt _ (by decide), h1⟩, by simp [h2], h3, ?_⟩
    have e0 : 2 ^ (30 * (a :: as).length) = 2 ^ 30 * 2 ^ (30 * as.length) := by
      rw [List.length_cons, show 30 * (as.length + 1) = 30 + 30 * as.length by omega, Nat.pow_add]
    rw [val_cons, val_cons, e0]
    exact lshift_alg _ _ _ _ _ _ _ _ _ _ (by rw [Nat.mod_add_div]; exact hA.symm) h4

theorem rshift_alg (q m B zs d carry a as acc : Nat)
    (h1 : m + d * q = acc) (h2 : acc = carry * B + a) (h3 : zs * d + carry = as) :
    (q + B * zs) * d + m = a + B * as := by
  subst_vars
  grind

theorem vRshiftGo_spec {d : Nat} (hd : d < 30) : ∀ (as : List Nat), IsDigits as →
    IsDigits (vRshiftGo d as).1 ∧ (vRshiftGo d as).1.length = as.length ∧
      (vRshiftGo d as).2 < 2 ^ d ∧
      val (vRshiftGo d as).1 * 2 ^ d + (vRshiftGo d as).2 = val as
  | [], _ => by
    simp only [vRshiftGo, List.length_nil, val_nil, Nat.zero_mul, Nat.add_zero, true_and]
    exact ⟨isDigits_nil, Nat.two_pow_pos d, trivial⟩
  | a :: as, h => by
    have ⟨ha, has⟩ := isDigits_cons.1 h
    obtain ⟨h1, h2, h3, h4⟩ := vRshiftGo_spec hd as has
    simp only [vRshiftGo]
    generalize vRshiftGo d as = p at *
    obtain ⟨zs, carry⟩ := p
    simp only at h1 h2 h3 h4 ⊢
    have hacc : (carry <<< 30) ||| a = carry * 2 ^ 30 + a := shl_or carry a 30 ha
    rw [hacc]
    have hpd : 2 ^ d ≤ 2 ^ 29 := Nat.pow_le_pow_right (by decide) (by omega)
    have hm : (carry + 1) * 2 ^ 30 ≤ 2 ^ d * 2 ^ 30 := Nat.mul_le_mul_right _ h3
    have hm2 : (carry + 1) * 2 ^ 30 = carry * 2 ^ 30 + 2 ^ 30 := by grind
    have hlt : carry * 2 ^ 30 + a < 2 ^ d * 2 ^ 30 := by omega
    generalize hA : carry * 2 ^ 30 + a = A at *
    have hq : A / 2 ^ d < 2 ^ 30 := Nat.div_lt_of_lt_mul hlt
    have hu : u32 (A >>> d) = A / 2 ^ d := by
      rw [Nat.shiftRight_eq_div_pow]; exact Nat.mod_eq_of_lt (by omega)
    have hlo : u32 A &&& (2 ^ d - 1) = A % 2 ^ d := by
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))
    rw [hu, hlo]
    refine ⟨isDigits_cons.2 ⟨hq, h1⟩, by simp [h2], Nat.mod_lt _ (Nat.pow_pos (by decide)), ?_⟩
    rw [val_cons, val_cons]
    exact rshift_alg _ _ _ _ _ _ _ _ _ (Nat.mod_add_div A (2 ^ d)) hA.symm h4

/-! ## Division by one digit -/

/-- `inplace_divrem1(pout, pin, size, n)`, longobject.c:1885-1899. The loop runs
from the top digit down, which is this recursion's return order. -/
def inplaceDivrem1 (n : Nat) : List Nat → List Nat × Nat
  | [] => ([], 0)
  | a :: as =>
    let (qs, remainder) := inplaceDivrem1 n as
    let dividend := (remainder <<< 30) ||| a
    (u32 (dividend / n) :: qs, dividend % n)

/-- `inplace_rem1(pin, size, n)`, longobject.c:1924-1932. -/
def inplaceRem1 (n : Nat) : List Nat → Nat
  | [] => 0
  | a :: as => ((inplaceRem1 n as <<< 30) ||| a) % n

/-- `divrem1(a, n, &rem)`, longobject.c:1907-1918. -/
def divrem1 (a : List Nat) (n : Nat) : Py (List Nat × Nat) := do
  longAlloc a.length
  let (q, r) := inplaceDivrem1 n a
  return (normalize q, r)

theorem rem_step (n q r R a : Nat) (h1 : R = n * q + r) :
    R * 2 ^ 30 + a = n * (q * 2 ^ 30) + (r * 2 ^ 30 + a) := by
  subst h1
  grind

theorem inplaceDivrem1_spec {n : Nat} (hn : 0 < n) (hn2 : n < 2 ^ 30) :
    ∀ (as : List Nat), IsDigits as →
    IsDigits (inplaceDivrem1 n as).1 ∧ (inplaceDivrem1 n as).1.length = as.length ∧
      (inplaceDivrem1 n as).2 < n ∧
      val as = n * val (inplaceDivrem1 n as).1 + (inplaceDivrem1 n as).2
  | [], _ => by simp [inplaceDivrem1, isDigits_nil, hn]
  | a :: as, h => by
    have ⟨ha, has⟩ := isDigits_cons.1 h
    obtain ⟨h1, h2, h3, h4⟩ := inplaceDivrem1_spec hn hn2 as has
    simp only [inplaceDivrem1]
    generalize inplaceDivrem1 n as = p at *
    obtain ⟨qs, rem⟩ := p
    simp only at h1 h2 h3 h4 ⊢
    have hor : (rem <<< 30) ||| a = rem * 2 ^ 30 + a := shl_or rem a 30 ha
    rw [hor]
    generalize hD : rem * 2 ^ 30 + a = D at *
    have hm : (rem + 1) * 2 ^ 30 ≤ n * 2 ^ 30 := Nat.mul_le_mul_right _ h3
    have hm2 : (rem + 1) * 2 ^ 30 = rem * 2 ^ 30 + 2 ^ 30 := by grind
    have hq : D / n < 2 ^ 30 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm] at hm; omega)
    have hu : u32 (D / n) = D / n := Nat.mod_eq_of_lt (by omega)
    rw [hu]
    refine ⟨isDigits_cons.2 ⟨hq, h1⟩, by simp [h2], Nat.mod_lt _ hn, ?_⟩
    have hdm := Nat.div_add_mod D n
    rw [val_cons, val_cons, h4]
    generalize D / n = Q at *
    generalize D % n = M at *
    subst hD
    generalize (2 : Nat) ^ 30 = B at *
    grind

theorem inplaceRem1_eq {n : Nat} (hn : 0 < n) (hn2 : n < 2 ^ 30) :
    ∀ (as : List Nat), IsDigits as → inplaceRem1 n as = (inplaceDivrem1 n as).2
  | [], _ => rfl
  | a :: as, h => by
    have ⟨_, has⟩ := isDigits_cons.1 h
    simp only [inplaceRem1, inplaceDivrem1]
    rw [inplaceRem1_eq hn hn2 as has]

/-! ## `x_divrem` -/

/-- The outer loop of `x_divrem`, longobject.c:3300-3361. `rem` is `vk[1:size_w+1]`
at the start of an iteration and `low` the digits still to bring down, the next
one first. Quotient digits go in front of `acc`, as `*--ak = q` stores them. -/
def divLoop (w : List Nat) (wm1 wm2 : Nat) : List Nat → List Nat → List Nat →
    Py (List Nat × List Nat)
  | [], rem, acc => .ok (acc, rem)
  | d :: low, rem, acc => do
    let (q, rem') ← divStep w wm1 wm2 (d :: rem)
    divLoop w wm1 wm2 low rem' (q :: acc)

/-- `x_divrem(v1, w1, &prem)`, longobject.c:3242-3370; returns quotient and remainder digits. -/
def xDivrem (v1 w1 : List Nat) : Py (List Nat × List Nat) := do
  longAlloc (v1.length + 1)
  longAlloc w1.length
  let d := 30 - bitLength (w1.getD (w1.length - 1) 0)
  let w := (vLshiftGo d w1 0).1
  let v := (vLshiftGo d v1 0).1
  let carry := (vLshiftGo d v1 0).2
  let v := if carry ≠ 0 ∨ v.getD (v1.length - 1) 0 ≥ w.getD (w1.length - 1) 0
    then v ++ [carry] else v
  let k := v.length - w1.length
  longAlloc k
  let wm1 := w.getD (w1.length - 1) 0
  let wm2 := w.getD (w1.length - 2) 0
  let (a, rem) ← divLoop w wm1 wm2 (v.take k).reverse (v.drop k) []
  return (normalize a, normalize (vRshiftGo d rem).1)

theorem divLoop_spec {wl : List Nat} {wm1 wm2 : Nat} (hw : IsDigits (wl ++ [wm2, wm1]))
    (h1 : 2 ^ 29 ≤ wm1) : ∀ (low rem acc : List Nat), IsDigits low → IsDigits rem →
    rem.length = wl.length + 2 → val rem < val (wl ++ [wm2, wm1]) →
    ∃ qs r, divLoop (wl ++ [wm2, wm1]) wm1 wm2 low rem acc = .ok (qs ++ acc, r) ∧ IsDigits qs ∧
      qs.length = low.length ∧ IsDigits r ∧ r.length = wl.length + 2 ∧
      val r < val (wl ++ [wm2, wm1]) ∧
      val low.reverse + 2 ^ (30 * low.length) * val rem =
        val qs * val (wl ++ [wm2, wm1]) + val r
  | [], rem, acc, _, h3, h4, h5 => ⟨[], rem, by simp [divLoop], isDigits_nil, rfl, h3, h4, h5,
      by simp⟩
  | d :: low, rem, acc, h2, h3, h4, h5 => by
    have ⟨hd, hlow⟩ := isDigits_cons.1 h2
    have hvk : IsDigits (d :: rem) := isDigits_cons.2 ⟨hd, h3⟩
    have hlt : val (d :: rem) < 2 ^ 30 * val (wl ++ [wm2, wm1]) := by
      rw [val_cons]
      have : 2 ^ 30 * (val rem + 1) ≤ 2 ^ 30 * val (wl ++ [wm2, wm1]) :=
        Nat.mul_le_mul_left _ h5
      rw [Nat.mul_add] at this
      omega
    obtain ⟨q, r1, hs, q1, d1, l1, v1, e1⟩ := divStep_spec hw h1 hvk (by simp [h4]) hlt
    obtain ⟨qs, r, hr, s1, s2, s3, s4, s5, s6⟩ := divLoop_spec hw h1 low r1 (q :: acc) hlow d1 l1 v1
    refine ⟨qs ++ [q], r, ?_, isDigits_append.2 ⟨s1, isDigits_cons.2 ⟨q1, isDigits_nil⟩⟩,
      by simp [s2], s3, s4, s5, ?_⟩
    · simp only [divLoop, hs, bind_ok, hr, List.append_assoc, List.singleton_append]
    · rw [List.reverse_cons, val_append, val_append, List.length_reverse, s2]
      rw [val_cons] at e1
      simp only [val_cons, val_nil, Nat.mul_zero, Nat.add_zero, List.length_cons]
      rw [show 30 * (low.length + 1) = 30 * low.length + 30 by omega, Nat.pow_add]
      generalize 2 ^ (30 * low.length) = P at *
      generalize val (wl ++ [wm2, wm1]) = W at *
      generalize (2 : Nat) ^ 30 = B at *
      have e2 : val low.reverse + P * d + P * B * val rem =
          val low.reverse + P * (d + B * val rem) := by grind
      rw [e2, e1]
      have e3 : val low.reverse + P * (q * W + val r1) =
          (val low.reverse + P * val r1) + P * (q * W) := by grind
      rw [e3, s6]
      grind

theorem split2 {w : List Nat} {m : Nat} (h : w.length = m + 2) :
    ∃ wl a b, w = wl ++ [a, b] ∧ wl.length = m := by
  have hd : (w.drop m).length = 2 := by simp; omega
  match hr : w.drop m, hd with
  | [a, b], _ =>
    refine ⟨w.take m, a, b, ?_, by simp; omega⟩
    rw [← hr, List.take_append_drop]

theorem drop_concat {u : List Nat} {t k : Nat} (h : k ≤ u.length) :
    (u ++ [t]).drop k = u.drop k ++ [t] :=
  List.drop_append_of_le_length h

/-- A window whose top digit is below `wm1` is below the divisor. -/
theorem val_lt_of_top {x w : List Nat} {t wm1 Pn : Nat} (hx : IsDigits x)
    (hlx : Pn = 2 ^ (30 * x.length)) (ht : t < wm1) (hw : Pn * wm1 ≤ val w) :
    val (x ++ [t]) < val w := by
  rw [val_append, ← hlx]
  simp only [val_cons, val_nil, Nat.mul_zero, Nat.add_zero]
  have h1 : val x < Pn := by rw [hlx]; exact val_lt hx
  have h2 : Pn * (t + 1) ≤ Pn * wm1 := Nat.mul_le_mul_left _ ht
  rw [Nat.mul_add, Nat.mul_one] at h2
  omega

/-- The final unshift and the division relation, longobject.c:3364-3369. -/
theorem unshift_alg {V W Q R c p M : Nat} (hp : 0 < p) (hc : c < p)
    (h1 : V * p = Q * (W * p) + M) (h2 : R * p + c = M) (hM : M < W * p) :
    V / W = Q ∧ V % W = R := by
  have hRW : R < W := by
    have : R * p < W * p := by omega
    exact Nat.lt_of_mul_lt_mul_right this
  have e : p * V = p * (Q * W + R) + c := by
    subst h2
    rw [Nat.mul_comm p V, h1]
    grind
  have hc0 : c = 0 := by
    have := congrArg (· % p) e
    simp only [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hc] at this
    simpa using this.symm
  subst hc0
  have e2 : V = Q * W + R := Nat.eq_of_mul_eq_mul_left hp (by simpa using e)
  have hW : 0 < W := by omega
  have := (Nat.div_mod_unique hW (a := V) (c := R) (d := Q)).2
    ⟨by rw [e2]; grind, hRW⟩
  exact this

/-- `x_divrem` is Algorithm D: for a normalized divisor of at least two digits and
a dividend at least as long, it returns `v // w` and `v % w`, with no intermediate
leaving its C type. -/
theorem xDivrem_spec {v1 w1 : List Nat} (hv : IsDigits v1) (hw : IsDigits w1) (nw : Normal w1)
    (h2 : 2 ≤ w1.length) (hle : w1.length ≤ v1.length) (hs : v1.length + 1 ≤ maxLongDigits) :
    xDivrem v1 w1 = .ok (digitsOf (val v1 / val w1), digitsOf (val v1 % val w1)) := by
  have hne : w1 ≠ [] := by intro h; simp [h] at h2
  obtain ⟨l, top, hl⟩ : ∃ l t, w1 = l ++ [t] :=
    ⟨w1.dropLast, w1.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
  have htop0 : top ≠ 0 := by
    have := nw hne
    simpa [hl] using this
  have hdl : IsDigits l := (isDigits_append.1 (hl ▸ hw)).1
  have htop : top < 2 ^ 30 := (isDigits_cons.1 (isDigits_append.1 (hl ▸ hw)).2).1
  have hgetTop : w1.getD (w1.length - 1) 0 = top := by
    subst hl; simp [List.getD]
  have hlenl : w1.length = l.length + 1 := by subst hl; simp
  obtain ⟨b1, b2⟩ := bitLength_bounds top (by omega)
  have hbl : bitLength top ≤ 30 := bitLength_le_of_lt' htop
  have hbl1 : 1 ≤ bitLength top := by
    have := (bitLength_facts top).2.1 (by omega)
    exact this.2
  generalize hdd : 30 - bitLength top = d at *
  have hd : d < 30 := by omega
  have hdp : bitLength top + d = 30 := by omega
  have hp : 0 < 2 ^ d := Nat.pow_pos (by decide)
  -- normalized divisor
  obtain ⟨wd, wlen, wc, wv⟩ := vLshiftGo_spec hd w1 0 hw hp
  obtain ⟨vd, vlen, vc, vv⟩ := vLshiftGo_spec hd v1 0 hv hp
  simp only [Nat.add_zero] at wv vv
  generalize hwp : vLshiftGo d w1 0 = pw at *
  generalize hvp : vLshiftGo d v1 0 = pv at *
  obtain ⟨w, c0⟩ := pw
  obtain ⟨v, carry⟩ := pv
  simp only at wd wlen wc wv vd vlen vc vv
  generalize hX1 : 2 ^ (30 * l.length) = X1 at *
  have hW : val w1 = val l + X1 * top := by
    rw [hl, val_append, hX1]; simp
  have hlX : val l < X1 := by rw [← hX1]; exact val_lt hdl
  have hPn : 2 ^ (30 * w1.length) = X1 * 2 ^ 30 := by
    rw [hlenl, show 30 * (l.length + 1) = 30 * l.length + 30 by omega, Nat.pow_add, hX1]
  have hshift : val w1 * 2 ^ d < X1 * 2 ^ 30 := by
    have a1 : (top + 1) * 2 ^ d ≤ 2 ^ bitLength top * 2 ^ d := Nat.mul_le_mul_right _ b2
    rw [← Nat.pow_add, hdp] at a1
    have a2 : val w1 < X1 * (top + 1) := by
      rw [hW, Nat.mul_add, Nat.mul_one]; omega
    calc val w1 * 2 ^ d < X1 * (top + 1) * 2 ^ d := Nat.mul_lt_mul_of_pos_right a2 hp
      _ = X1 * ((top + 1) * 2 ^ d) := Nat.mul_assoc _ _ _
      _ ≤ X1 * 2 ^ 30 := Nat.mul_le_mul_left _ a1
  have hc0 : c0 = 0 := by
    rcases Nat.eq_zero_or_pos c0 with h | h
    · exact h
    · rw [hPn] at wv
      have := Nat.mul_le_mul_left (X1 * 2 ^ 30) h
      omega
  subst hc0
  simp only [Nat.mul_zero, Nat.add_zero] at wv
  have hlow : X1 * 2 ^ 29 ≤ val w := by
    have a1 : 2 ^ (bitLength top - 1) * 2 ^ d ≤ top * 2 ^ d := Nat.mul_le_mul_right _ b1
    rw [← Nat.pow_add, show bitLength top - 1 + d = 29 by omega] at a1
    have a2 : X1 * 2 ^ 29 ≤ X1 * (top * 2 ^ d) := Nat.mul_le_mul_left _ a1
    rw [wv, hW, Nat.add_mul, Nat.mul_assoc]
    omega
  -- split the normalized divisor
  obtain ⟨wl, wm2, wm1, hws, hlwl⟩ := split2 (w := w) (m := w1.length - 2) (by omega)
  have hwlen : wl.length + 1 = l.length := by omega
  have hgw1 : w.getD (w1.length - 1) 0 = wm1 := by
    subst hws
    have : w1.length - 1 = wl.length + 1 := by omega
    rw [this]; simp [List.getD]
  have hgw2 : w.getD (w1.length - 2) 0 = wm2 := by
    subst hws
    have : w1.length - 2 = wl.length := by omega
    rw [this]; simp [List.getD]
  have hwd : IsDigits (wl ++ [wm2, wm1]) := hws ▸ wd
  have hwv := val2 wl wm2 wm1
  have hXw : X1 = 2 ^ (30 * wl.length) * 2 ^ 30 := by
    rw [← hX1, ← hwlen, show 30 * (wl.length + 1) = 30 * wl.length + 30 by omega, Nat.pow_add]
  have hwm1 : 2 ^ 29 ≤ wm1 := by
    refine Nat.le_of_not_lt fun hlt => ?_
    have a0 : val wl < 2 ^ (30 * wl.length) := (val_lt (isDigits_append.1 hwd).1)
    have a1 : wm2 < 2 ^ 30 :=
      (isDigits_cons.1 (isDigits_append.1 hwd).2).1
    have a2 : X1 * (wm1 + 1) ≤ X1 * 2 ^ 29 := Nat.mul_le_mul_left _ hlt
    have a3 : 2 ^ (30 * wl.length) * (wm2 + 1) ≤ 2 ^ (30 * wl.length) * 2 ^ 30 :=
      Nat.mul_le_mul_left _ a1
    rw [hws, hwv] at hlow
    rw [hXw] at hlow a2
    rw [Nat.mul_add, Nat.mul_one] at a2 a3
    omega
  have hgetv : (w1.getD (w1.length - 1) 0) = top := hgetTop
  have hdivisor : X1 * wm1 ≤ val w := by
    rw [hws, hwv, hXw]; omega
  -- the top window is below the divisor
  obtain ⟨v', hv'⟩ : ∃ x, x = if carry ≠ 0 ∨ v.getD (v1.length - 1) 0 ≥ wm1 then v ++ [carry] else v :=
    ⟨_, rfl⟩
  have hv'd : IsDigits v' := by
    rw [hv']
    split
    · exact isDigits_append.2 ⟨vd, isDigits_cons.2 ⟨by
        have : 2 ^ d ≤ 2 ^ 29 := Nat.pow_le_pow_right (by decide) (by omega)
        omega, isDigits_nil⟩⟩
    · exact vd
  have hv'v : val v' = val v1 * 2 ^ d := by
    rw [hv']
    split
    · rw [val_append, vlen, ← vv]
      simp
    · rename_i hn
      have hc : carry = 0 := by
        rcases Nat.eq_zero_or_pos carry with h | h
        · exact h
        · exact absurd (Or.inl (by omega)) hn
      rw [← vv, hc]
      simp
  have hv'len : w1.length ≤ v'.length := by
    rw [hv']
    split
    · simp [vlen]; omega
    · omega
  have hk : v'.length - w1.length + w1.length = v'.length := by omega
  have hrem : val (v'.drop (v'.length - w1.length)) < val w := by
    rw [hv']
    split
    · rename_i hc
      have hk1 : (v ++ [carry]).length - w1.length ≤ v.length := by simp [vlen]; omega
      rw [drop_concat hk1]
      have hlx : X1 = 2 ^ (30 * (v.drop ((v ++ [carry]).length - w1.length)).length) := by
        rw [← hX1]; congr 2; simp [vlen]; omega
      refine val_lt_of_top (isDigits_drop vd _) hlx ?_ hdivisor
      have : 2 ^ d ≤ 2 ^ 29 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · rename_i hn
      have hnot : ¬ (v.getD (v1.length - 1) 0 ≥ wm1) := fun h => hn (Or.inr h)
      have hvne : v ≠ [] := by intro h; simp [h] at vlen; omega
      obtain ⟨u, t, hu⟩ : ∃ u t, v = u ++ [t] :=
        ⟨v.dropLast, v.getLast hvne, (List.dropLast_concat_getLast hvne).symm⟩
      have hgt : v.getD (v1.length - 1) 0 = t := by
        have : v1.length - 1 = u.length := by
          have := congrArg List.length hu
          simp at this
          omega
        rw [this, hu]; simp [List.getD]
      have hud : IsDigits u := (isDigits_append.1 (hu ▸ vd)).1
      have hul : u.length + 1 = v.length := by rw [hu]; simp
      have hk1 : v.length - w1.length ≤ u.length := by
        rw [hu]; simp; omega
      rw [hu, show (u ++ [t]).length - w1.length = u.length + 1 - w1.length by simp]
      have hk2 : u.length + 1 - w1.length ≤ u.length := by omega
      rw [drop_concat hk2]
      have hlx : X1 = 2 ^ (30 * (u.drop (u.length + 1 - w1.length)).length) := by
        rw [← hX1]; congr 2; simp; omega
      exact val_lt_of_top (isDigits_drop hud _) hlx (by omega) hdivisor
  have hv'le : v'.length ≤ v1.length + 1 := by
    rw [hv']
    split
    · simp [vlen]
    · omega
  generalize hkk : v'.length - w1.length = k at *
  have hlow2 : IsDigits (v'.take k).reverse := by
    intro x hx
    exact isDigits_take hv'd k x (List.mem_reverse.1 hx)
  have hremlen : (v'.drop k).length = wl.length + 2 := by simp; omega
  have hremd := isDigits_drop hv'd k
  rw [hws] at hrem
  obtain ⟨qs, r, hr, q1, q2, r1, r2, r3, r4⟩ := divLoop_spec hwd hwm1 (v'.take k).reverse
    (v'.drop k) [] hlow2 hremd hremlen hrem
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse, List.length_take] at hr r4
  have hsplit := val_split (n := v') (size := k) (by omega)
  rw [Nat.min_eq_left (by omega), ← hsplit, hv'v] at r4
  rw [← hws, wv] at r3 r4
  obtain ⟨sd, sl, sc, sv⟩ := vRshiftGo_spec hd r r1
  have hfin := unshift_alg hp sc r4 sv r3
  -- assemble
  have hsplitfin : xDivrem v1 w1 = .ok (normalize qs, normalize (vRshiftGo d r).1) := by
    unfold xDivrem
    rw [longAlloc_ok hs, longAlloc_ok (by omega)]
    simp only [bind_ok]
    rw [hgetTop, hdd, hwp, hvp]
    simp only [hgw1, hgw2]
    rw [← hv', hkk, longAlloc_ok (by omega)]
    simp only [bind_ok]
    rw [hws, hr]
    simp only [bind_ok, pure_ok]
  rw [hsplitfin, digitsOf_normalize q1, digitsOf_normalize sd, hfin.1, hfin.2]

/-! ## `long_divrem` and `long_rem` -/

/-- The digit work of `long_divrem`, longobject.c:3156-3172: both magnitudes. -/
def divMag (a b : List Nat) : Py (List Nat × Long) :=
  if b.length = 1 then
    match divrem1 a (b.getD 0 0) with
    | .ok (q, r) => .ok (q, fromSingle r)
    | .error e => .error e
  else
    match xDivrem a b with
    | .ok (q, r) => .ok (q, ⟨false, r⟩)
    | .error e => .error e

/-- The test `|a| < |b|`, longobject.c:3145-3147 and :3208-3210. -/
def magLess (a b : List Nat) : Bool :=
  decide (a.length < b.length ∨
    (a.length = b.length ∧ a.getD (a.length - 1) 0 < b.getD (b.length - 1) 0))

/-- `long_divrem(a, b, &div, &rem)`, longobject.c:3135-3194. -/
def longDivrem (a b : Long) : Py (Long × Long) :=
  if b.ds.length = 0 then .error (.zeroDivisionError "division by zero")
  else if magLess a.ds b.ds then .ok (⟨false, []⟩, a)
  else
    match divMag a.ds b.ds with
    | .error e => .error e
    | .ok (z, rem) =>
      let z : Long := ⟨false, z⟩
      let z := if a.neg != b.neg then z.flip else z
      let rem := if a.neg && !rem.ds.isEmpty then rem.flip else rem
      .ok (z, rem)

/-- `rem1(a, n)`, longobject.c:1939-1947, through `PyLong_FromLong`. -/
def rem1 (a : List Nat) (n : Nat) : Long := fromSingle (inplaceRem1 n a)

/-- `long_rem(a, b, &rem)`, longobject.c:3199-3236. -/
def longRem (a b : Long) : Py Long :=
  if b.ds.length = 0 then .error (.zeroDivisionError "division by zero")
  else if magLess a.ds b.ds then .ok a
  else
    let finish (rem : Long) : Py Long :=
      .ok (if a.neg && !rem.ds.isEmpty then rem.flip else rem)
    if b.ds.length = 1 then finish (rem1 a.ds (b.ds.getD 0 0))
    else
      match xDivrem a.ds b.ds with
      | .ok (_, r) => finish ⟨false, r⟩
      | .error e => .error e

/-- The shortcut test only ever fires when `|a| < |b|`. It can miss: equal top
digits fall through to the general path, which handles that case too. -/
theorem magLess_lt {a b : List Nat} (ha : IsDigits a) (hb : IsDigits b) (nb : Normal b)
    (h : magLess a b = true) : val a < val b := by
  simp only [magLess, decide_eq_true_eq] at h
  rcases h with h | ⟨h1, h2⟩
  · exact val_lt_of_length ha hb nb h
  · have hpos : 0 < a.length := by
      rcases Nat.eq_zero_or_pos a.length with h0 | h0
      · have e1 : a = [] := List.eq_nil_of_length_eq_zero h0
        have e2 : b = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst e1; subst e2
        simp at h2
      · exact h0
    have := val_take_lt ha hb (i := a.length - 1) (by omega) (by omega)
      (by rw [← h1] at h2; exact h2)
    rw [show a.length - 1 + 1 = a.length by omega, List.take_length] at this
    rwa [h1, List.take_length] at this

theorem divrem1_exact {a : List Nat} {n : Nat} (ha : IsDigits a) (hn : 0 < n) (hn2 : n < 2 ^ 30)
    (hs : a.length ≤ maxLongDigits) :
    divrem1 a n = .ok (digitsOf (val a / n), val a % n) := by
  obtain ⟨h1, _, h3, h4⟩ := inplaceDivrem1_spec hn hn2 a ha
  simp only [divrem1, longAlloc_ok hs, bind_ok]
  generalize hp : inplaceDivrem1 n a = p at *
  obtain ⟨q, r⟩ := p
  simp only at h1 h3 h4
  have hu := (Nat.div_mod_unique hn (a := val a) (c := r) (d := val q)).2 ⟨by omega, h3⟩
  simp only [pure_ok]
  rw [digitsOf_normalize h1, hu.1, hu.2]

/-- The digit work of `long_divrem` on normalized magnitudes. -/
theorem divMag_spec {a b : List Nat} (ha : IsDigits a) (hb : IsDigits b) (nb : Normal b)
    (h0 : b ≠ []) (hle : b.length ≤ a.length) (hs : a.length + 1 ≤ maxLongDigits) :
    divMag a b = .ok (digitsOf (val a / val b), ⟨false, digitsOf (val a % val b)⟩) := by
  unfold divMag
  by_cases h1 : b.length = 1
  · rw [if_pos h1]
    match b, h1, hb, nb with
    | [n], _, hb, nb =>
      have hn : n < 2 ^ 30 := (isDigits_cons.1 hb).1
      have hn0 : 0 < n := by
        have := nb (by simp)
        simp at this
        omega
      have hv : val [n] = n := by simp
      simp only [List.getD_cons_zero, hv]
      rw [divrem1_exact ha hn0 hn (by omega)]
      simp only
      have hr : val a % n < 2 ^ 30 := by
        have := Nat.mod_lt (val a) hn0
        omega
      generalize val a % n = m at *
      have := fromSingle_eq (x := (m : Int)) (by rw [Int.natAbs_natCast]; exact hr)
      rw [this, Long.ofInt_natCast]
  · rw [if_neg h1]
    have h2 : 2 ≤ b.length := by
      cases b with
      | nil => exact absurd rfl h0
      | cons x t =>
        cases t with
        | nil => simp at h1
        | cons y u => simp
    rw [xDivrem_spec ha hb nb h2 hle hs]

/-- Truncated quotient in terms of magnitudes. -/
theorem tdiv_natAbs (a b : Int) : a.tdiv b =
    if (decide (a < 0) != decide (b < 0)) = true then -((a.natAbs / b.natAbs : Nat) : Int)
    else ((a.natAbs / b.natAbs : Nat) : Int) := by
  rcases (by omega : (a = (a.natAbs : Int) ∧ 0 ≤ a) ∨ (a = -(a.natAbs : Int) ∧ a < 0)) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases (by omega : (b = (b.natAbs : Int) ∧ 0 ≤ b) ∨ (b = -(b.natAbs : Int) ∧ b < 0)) with
    ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
  generalize a.natAbs = A at * <;> generalize b.natAbs = B at * <;> subst h1 <;> subst h3
  · have d1 : decide ((A : Int) < 0) = false := decide_eq_false (by omega)
    have d2 : decide ((B : Int) < 0) = false := decide_eq_false (by omega)
    simp only [d1, d2, bne_self_eq_false, Bool.false_eq_true, ite_false, ← Int.ofNat_tdiv]
  · have d1 : decide ((A : Int) < 0) = false := decide_eq_false (by omega)
    have d2 : decide (-(B : Int) < 0) = true := decide_eq_true h4
    simp only [d1, d2, Int.tdiv_neg, ← Int.ofNat_tdiv]
    rfl
  · have d1 : decide (-(A : Int) < 0) = true := decide_eq_true h2
    have d2 : decide ((B : Int) < 0) = false := decide_eq_false (by omega)
    simp only [d1, d2, Int.neg_tdiv, ← Int.ofNat_tdiv]
    rfl
  · have d1 : decide (-(A : Int) < 0) = true := decide_eq_true h2
    have d2 : decide (-(B : Int) < 0) = true := decide_eq_true h4
    simp only [d1, d2, Int.neg_tdiv, Int.tdiv_neg, Int.neg_neg, ← Int.ofNat_tdiv]
    rfl

/-- Truncated remainder in terms of magnitudes. -/
theorem tmod_natAbs (a b : Int) : a.tmod b =
    if a < 0 then -((a.natAbs % b.natAbs : Nat) : Int)
    else ((a.natAbs % b.natAbs : Nat) : Int) := by
  rcases (by omega : (a = (a.natAbs : Int) ∧ 0 ≤ a) ∨ (a = -(a.natAbs : Int) ∧ a < 0)) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases (by omega : (b = (b.natAbs : Int) ∧ 0 ≤ b) ∨ (b = -(b.natAbs : Int) ∧ b < 0)) with
    ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
  generalize a.natAbs = A at * <;> generalize b.natAbs = B at * <;> subst h1 <;> subst h3
  · rw [if_neg (by omega)]; simp only [← Int.ofNat_tmod]
  · rw [if_neg (by omega), Int.tmod_neg]; simp only [← Int.ofNat_tmod]
  · rw [if_pos h2, Int.neg_tmod]; simp only [← Int.ofNat_tmod]
  · rw [if_pos h2, Int.neg_tmod, Int.tmod_neg]; simp only [← Int.ofNat_tmod]

/-- The sign fix-ups give the canonical object of the signed value. -/
theorem signed_ofInt (s : Bool) (n : Nat) :
    (if s = true then (⟨false, digitsOf n⟩ : Long).flip else ⟨false, digitsOf n⟩) =
      Long.ofInt (if s = true then -(n : Int) else n) := by
  cases s with
  | true =>
    simp only [ite_true]
    rw [Long.ofInt_neg, Long.ofInt_natCast]
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    rw [Long.ofInt_natCast]

/-- `long_divrem` returns the canonical truncated quotient and remainder for every
nonzero divisor; the hypothesis is the room `x_divrem` needs for its work copy. -/
theorem longDivrem_spec (a b : Int) (hb : b ≠ 0) (hs : digitCount a.natAbs + 1 ≤ maxLongDigits) :
    longDivrem (Long.ofInt a) (Long.ofInt b) =
      .ok (Long.ofInt (a.tdiv b), Long.ofInt (a.tmod b)) := by
  have dA := digitsOf_digits a.natAbs
  have dB := digitsOf_digits b.natAbs
  have nB := normal_digitsOf b.natAbs
  have lA := length_digitsOf a.natAbs
  have hB0 : 0 < b.natAbs := by omega
  have hne : digitsOf b.natAbs ≠ [] := by rw [Ne, digitsOf_eq_nil]; omega
  have hlen : ¬ (digitsOf b.natAbs).length = 0 := by
    intro h; exact hne (List.eq_nil_of_length_eq_zero h)
  unfold longDivrem
  simp only [Long.ofInt, hlen, ite_false]
  by_cases hm : magLess (digitsOf a.natAbs) (digitsOf b.natAbs) = true
  · have hlt := magLess_lt dA dB nB hm
    rw [val_digitsOf, val_digitsOf] at hlt
    simp only [hm, ite_true]
    have e1 : a.tdiv b = 0 := by
      rw [tdiv_natAbs, Nat.div_eq_of_lt hlt]; simp
    have e2 : a.tmod b = a := by
      rw [tmod_natAbs, Nat.mod_eq_of_lt hlt]
      split <;> omega
    rw [e1, e2]
    simp
  · simp only [hm, Bool.false_eq_true, ite_false]
    have hle : (digitsOf b.natAbs).length ≤ (digitsOf a.natAbs).length := by
      simp only [magLess, decide_eq_true_eq] at hm
      omega
    rw [divMag_spec dA dB nB hne hle (by omega), val_digitsOf, val_digitsOf]
    simp only
    have s1 := signed_ofInt (decide (a < 0) != decide (b < 0)) (a.natAbs / b.natAbs)
    rw [← tdiv_natAbs] at s1
    have s2 := signed_ofInt (decide (a < 0)) (a.natAbs % b.natAbs)
    have e2 : (if decide (a < 0) = true then -((a.natAbs % b.natAbs : Nat) : Int)
        else ((a.natAbs % b.natAbs : Nat) : Int)) = a.tmod b := by
      rw [tmod_natAbs]; simp only [decide_eq_true_eq]
    rw [e2] at s2
    have hrem : (if (decide (a < 0) && !(digitsOf (a.natAbs % b.natAbs)).isEmpty) = true then
          (⟨false, digitsOf (a.natAbs % b.natAbs)⟩ : Long).flip
        else ⟨false, digitsOf (a.natAbs % b.natAbs)⟩) = Long.ofInt (a.tmod b) := by
      rw [← s2]
      by_cases hz : digitsOf (a.natAbs % b.natAbs) = []
      · simp [hz, Long.flip]
      · have : (digitsOf (a.natAbs % b.natAbs)).isEmpty = false := by
          cases hh : digitsOf (a.natAbs % b.natAbs) with
          | nil => exact absurd hh hz
          | cons _ _ => rfl
        simp [this]
    exact congrArg Except.ok (Prod.ext s1 hrem)

end PyLean.LongObj
