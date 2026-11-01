import PyLean.LongObj.Karatsuba

/-!
Algorithm D as used by `x_divrem`, longobject.c:3242-3370: one quotient digit.

The first half is pure `Nat` arithmetic on the top digits of the window, written
for an arbitrary base `B`. With

  `V = vl + X*v2 + X*B*vv`  and  `W = wl + X*wm2 + X*B*wm1`,  `vl, wl < X`,

the estimate from `vv / wm1`, corrected by the `wm2` test, never undershoots the
true quotient digit and overshoots by at most one.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt

/-! ## Quotient estimate: arithmetic -/

/-- `q + 1` is above the true digit when `vv < wm1 * (q + 1)`. -/
theorem est_upper {vl v2 X B vv wl wm2 wm1 V W q : Nat}
    (hV : V = vl + X * v2 + X * B * vv) (hW : W = wl + X * wm2 + X * B * wm1)
    (hvl : vl < X) (hv2 : v2 < B) (hq : vv < wm1 * (q + 1)) : V < (q + 1) * W := by
  have h1 : X * (v2 + 1) ≤ X * B := Nat.mul_le_mul_left _ hv2
  have h2 : X * B * (vv + 1) ≤ X * B * (wm1 * (q + 1)) := Nat.mul_le_mul_left _ hq
  have e1 : (q + 1) * W = (q + 1) * wl + (q + 1) * (X * wm2) + X * B * (wm1 * (q + 1)) := by
    subst hW; grind
  have e2 : X * B * (vv + 1) = X * B * vv + X * B := by grind
  have e3 : X * (v2 + 1) = X * v2 + X := by grind
  omega

/-- The test at longobject.c:3325-3326 succeeding means `q` is too large. -/
theorem est_dec {vl v2 X B vv wl wm2 wm1 V W q r : Nat}
    (hV : V = vl + X * v2 + X * B * vv) (hW : W = wl + X * wm2 + X * B * wm1)
    (hvl : vl < X) (hvv : vv = wm1 * q + r) (hgt : r * B + v2 < wm2 * q) : V < q * W := by
  have h1 : X * (r * B + v2 + 1) ≤ X * (wm2 * q) := Nat.mul_le_mul_left _ hgt
  have e1 : q * W = q * wl + X * (wm2 * q) + X * B * (wm1 * q) := by subst hW; grind
  have e2 : X * (r * B + v2 + 1) = X * B * r + X * v2 + X := by grind
  have e3 : X * B * vv = X * B * (wm1 * q) + X * B * r := by subst hvv; grind
  omega

/-- The test failing bounds the overshoot. -/
theorem est_exit {vl v2 X B vv wl wm2 wm1 V W q r : Nat}
    (hV : V = vl + X * v2 + X * B * vv) (hW : W = wl + X * wm2 + X * B * wm1)
    (hwl : wl < X) (hvv : vv = wm1 * q + r) (hle : wm2 * q ≤ r * B + v2) :
    q * W ≤ V + q * X := by
  have h1 : X * (wm2 * q) ≤ X * (r * B + v2) := Nat.mul_le_mul_left _ hle
  have h2 : q * wl ≤ q * X := Nat.mul_le_mul_left _ (Nat.le_of_lt hwl)
  have e1 : q * W = q * wl + X * (wm2 * q) + X * B * (wm1 * q) := by subst hW; grind
  have e2 : X * (r * B + v2) = X * B * r + X * v2 := by grind
  have e3 : X * B * vv = X * B * (wm1 * q) + X * B * r := by subst hvv; grind
  omega

/-- With a normalized divisor the overshoot is at most one. -/
theorem est_overshoot {X B wl wm2 wm1 W V q : Nat}
    (hW : W = wl + X * wm2 + X * B * wm1) (hq : q ≤ B + 1) (hB : B + 1 ≤ B * wm1)
    (h : q * W ≤ V + q * X) : (q - 1) * W ≤ V := by
  have h1 : q * X ≤ (B * wm1) * X := Nat.mul_le_mul_right _ (Nat.le_trans hq hB)
  have e1 : (B * wm1) * X = X * B * wm1 := by grind
  have h2 : q * X ≤ W := by omega
  cases q with
  | zero => simp
  | succ p =>
    have e2 : (p + 1) * W = p * W + W := by grind
    simp only [Nat.add_sub_cancel]
    omega

/-! ## Quotient estimate: the loop -/

theorem shl_or (a b i : Nat) (h : b < 2 ^ i) : (a <<< i) ||| b = a * 2 ^ i + b := by
  rw [Nat.shiftLeft_eq, Nat.mul_comm, Nat.two_pow_add_eq_or_of_lt h]

/-- `while (wm2 * q > (r << SHIFT | vk[size_w-2])) { --q; r += wm1; if (r >= BASE) break; }`,
longobject.c:3325-3331. Fuel 2 is enough (`qLoop_spec`). -/
def qLoop (wm1 wm2 v2 : Nat) : Nat → Nat → Nat → Py (Nat × Nat)
  | 0, q, r => .ok (q, r)
  | f + 1, q, r => do
    let lhs ← chk64 (wm2 * q)
    let rhs ← chk64 ((r <<< 30) ||| v2)
    if lhs > rhs then
      let r' ← chk32 (r + wm1)
      if r' ≥ 2 ^ 30 then .ok (q - 1, r') else qLoop wm1 wm2 v2 f (q - 1) r'
    else .ok (q, r)

theorem qLoop_spec {wm1 wm2 v2 vl wl X vv V W : Nat}
    (hV : V = vl + X * v2 + X * 2 ^ 30 * vv) (hW : W = wl + X * wm2 + X * 2 ^ 30 * wm1)
    (hvl : vl < X) (h1 : 2 ^ 29 ≤ wm1) (h2 : wm1 < 2 ^ 30) (hw2 : wm2 < 2 ^ 30)
    (hv2 : v2 < 2 ^ 30) :
    ∀ (f q r : Nat), 1 ≤ f → vv = wm1 * q + r → r < 2 ^ 30 → V < (q + 1) * W →
      2 ^ 30 ≤ r + f * wm1 → q ≤ 2 ^ 30 + 1 →
      ∃ q' r', qLoop wm1 wm2 v2 f q r = .ok (q', r') ∧ vv = wm1 * q' + r' ∧
        V < (q' + 1) * W ∧ wm2 * q' ≤ r' * 2 ^ 30 + v2 ∧ q' ≤ 2 ^ 30 + 1 := by
  intro f
  induction f with
  | zero => intro q r h; omega
  | succ f ih =>
    intro q r _ hvv hr hup hfuel hq
    have hl : wm2 * q ≤ (2 ^ 30 - 1) * (2 ^ 30 + 1) := Nat.mul_le_mul (by omega) hq
    have hl64 : wm2 * q < 2 ^ 64 := by omega
    have hor : (r <<< 30) ||| v2 = r * 2 ^ 30 + v2 := shl_or r v2 30 hv2
    have hr64 : r * 2 ^ 30 + v2 < 2 ^ 64 := by omega
    simp only [qLoop, hor, chk64_ok hl64, chk64_ok hr64, bind_ok]
    by_cases hgt : wm2 * q > r * 2 ^ 30 + v2
    · simp only [hgt, ite_true]
      have hq1 : 1 ≤ q := by
        rcases Nat.eq_zero_or_pos q with h0 | h0
        · subst h0; simp at hgt
        · exact h0
      obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have hdec := est_dec hV hW hvl hvv hgt
      have hvv' : vv = wm1 * p + (r + wm1) := by rw [hvv]; grind
      rw [chk32_ok (by omega)]
      simp only [bind_ok]
      by_cases hbig : r + wm1 ≥ 2 ^ 30
      · simp only [hbig, ite_true]
        refine ⟨p, r + wm1, rfl, hvv', hdec, ?_, by omega⟩
        have a1 : wm2 * p ≤ (2 ^ 30 - 1) * (2 ^ 30) := Nat.mul_le_mul (by omega) (by omega)
        have a2 : 2 ^ 30 * 2 ^ 30 ≤ (r + wm1) * 2 ^ 30 := Nat.mul_le_mul_right _ hbig
        omega
      · simp only [hbig, ite_false]
        have hf1 : 1 ≤ f := by
          rcases Nat.eq_zero_or_pos f with h0 | h0
          · subst h0
            simp only [Nat.zero_add, Nat.one_mul] at hfuel
            omega
          · exact h0
        refine ih p (r + wm1) hf1 hvv' (by omega) hdec ?_ (by omega)
        have e : (f + 1) * wm1 = f * wm1 + wm1 := by grind
        omega
    · simp only [hgt, ite_false]
      exact ⟨q, r, rfl, hvv, hup, by omega, hq⟩

/-! ## Multiply and subtract -/

/-- `(digit)z & PyLong_MASK`, longobject.c:3341: the low 30 bits of a signed value. -/
def loDigit (z : Int) : Nat := (z % 2 ^ 30).toNat

/-- `Py_ARITHMETIC_RIGHT_SHIFT(stwodigits, z, PyLong_SHIFT)`, longobject.c:3342-3343. -/
def arsh30 (z : Int) : Int := z / 2 ^ 30

/-- `(sdigit)x`: the value fits `int32_t`. -/
def chkS32 (x : Int) : Py Int :=
  if -(2 ^ 31 : Int) ≤ x ∧ x < 2 ^ 31 then .ok x else .error cOverflow

theorem chkS32_ok {x : Int} (h : -(2 ^ 31 : Int) ≤ x ∧ x < 2 ^ 31) : chkS32 x = .ok x := if_pos h

/-- The loop subtracting `q * w0[0:size_w]` from `vk[0:size_w]`, longobject.c:3335-3344,
carrying `zhi`. -/
def subLoop (q : Nat) : List Nat → List Nat → Int → Py (List Nat × Int)
  | [], _, zhi => .ok ([], zhi)
  | _ :: _, [], _ => .error cOverflow
  | v :: vs, w :: ws, zhi => do
    let z ← chkS64 ((v : Int) + zhi - (q : Int) * (w : Int))
    let hi ← chkS32 (arsh30 z)
    let (r, zhi') ← subLoop q vs ws hi
    return (loDigit z :: r, zhi')

theorem sub_step_alg (d r Pn z vs h q w ws v zhi z0 B : Int)
    (h1 : z0 = v + zhi - q * w) (h2 : z0 = d + B * h) (h3 : r + Pn * z = vs + h - q * ws) :
    (d + B * r) + (B * Pn) * z = (v + B * vs) + zhi - q * (w + B * ws) := by
  subst h1
  grind

theorem cast_two_pow (k : Nat) : ((2 ^ k : Nat) : Int) = 2 ^ k := Int.natCast_pow 2 k

theorem subLoop_spec {q : Nat} (hq : q ≤ 2 ^ 30) :
    ∀ (vs ws : List Nat) (zhi : Int), IsDigits vs → IsDigits ws → vs.length = ws.length →
      -(q : Int) ≤ zhi → zhi ≤ 0 →
      ∃ r z, subLoop q vs ws zhi = .ok (r, z) ∧ IsDigits r ∧ r.length = vs.length ∧
        -(q : Int) ≤ z ∧ z ≤ 0 ∧
        (val r : Int) + (2 ^ (30 * vs.length) : Nat) * z = val vs + zhi - (q : Int) * val ws
  | [], [], zhi, _, _, _, h1, h2 => ⟨[], zhi, rfl, isDigits_nil, rfl, h1, h2, by simp⟩
  | v :: vs, w :: ws, zhi, hv, hw, hl, h1, h2 => by
    have ⟨hv0, hvs⟩ := isDigits_cons.1 hv
    have ⟨hw0, hws⟩ := isDigits_cons.1 hw
    have hP : q * w ≤ q * (2 ^ 30 - 1) := Nat.mul_le_mul_left _ (by omega)
    have hcast : (q : Int) * (w : Int) = ((q * w : Nat) : Int) := by simp
    obtain ⟨z0, hz⟩ : ∃ z : Int, z = (v : Int) + zhi - (q : Int) * (w : Int) := ⟨_, rfl⟩
    have hzn : z0 = (v : Int) + zhi - ((q * w : Nat) : Int) := by rw [hz, hcast]
    have hz1 : -(2 ^ 63 : Int) ≤ z0 ∧ z0 < 2 ^ 63 := by omega
    have hsplit : z0 = (loDigit z0 : Int) + 2 ^ 30 * arsh30 z0 := by
      simp only [loDigit, arsh30]; omega
    have hd : loDigit z0 < 2 ^ 30 := by simp only [loDigit]; omega
    have hh1 : -(q : Int) ≤ arsh30 z0 := by simp only [arsh30]; omega
    have hh2 : arsh30 z0 ≤ 0 := by simp only [arsh30]; omega
    have hs32 : -(2 ^ 31 : Int) ≤ arsh30 z0 ∧ arsh30 z0 < 2 ^ 31 := by omega
    obtain ⟨r, z, hr, r1, r2, r3, r4, r5⟩ := subLoop_spec hq vs ws (arsh30 z0) hvs hws
      (by simpa using hl) hh1 hh2
    refine ⟨loDigit z0 :: r, z, ?_, isDigits_cons.2 ⟨hd, r1⟩, by simp [r2], r3, r4, ?_⟩
    · simp only [subLoop, ← hz, chkS64_ok hz1, bind_ok, chkS32_ok hs32, hr, pure_ok]
    · have e0 : (2 ^ (30 * (v :: vs).length) : Nat) = 2 ^ 30 * 2 ^ (30 * vs.length) := by
        rw [List.length_cons, show 30 * (vs.length + 1) = 30 + 30 * vs.length by omega, Nat.pow_add]
      have r5' : (val r : Int) + (2 : Int) ^ (30 * vs.length) * z =
          (val vs : Int) + arsh30 z0 - (q : Int) * (val ws : Int) := by
        simpa using r5
      rw [e0, val_cons (loDigit z0) r, val_cons v vs, val_cons w ws]
      have c1 : ((loDigit z0 + 2 ^ 30 * val r : Nat) : Int) = (loDigit z0 : Int) + 2 ^ 30 * val r := by
        rw [Int.natCast_add, Int.natCast_mul, cast_two_pow]
      have c2 : ((2 ^ 30 * 2 ^ (30 * vs.length) : Nat) : Int) = 2 ^ 30 * 2 ^ (30 * vs.length) := by
        rw [Int.natCast_mul, cast_two_pow, cast_two_pow]
      have c3 : ((v + 2 ^ 30 * val vs : Nat) : Int) = (v : Int) + 2 ^ 30 * val vs := by
        rw [Int.natCast_add, Int.natCast_mul, cast_two_pow]
      have c4 : ((w + 2 ^ 30 * val ws : Nat) : Int) = (w : Int) + 2 ^ 30 * val ws := by
        rw [Int.natCast_add, Int.natCast_mul, cast_two_pow]
      rw [c1, c2, c3, c4]
      exact sub_step_alg _ _ _ _ _ _ _ _ _ _ _ z0 _ hz hsplit r5'

/-! ## One quotient digit -/

/-- The body of the outer loop of `x_divrem`, longobject.c:3304-3361: divide
`vk[0:size_w+1]` by `w`, giving the digit and the remainder `vk[0:size_w]`. -/
def divStep (w : List Nat) (wm1 wm2 : Nat) (vk : List Nat) : Py (Nat × List Nat) := do
  let n := w.length
  let vtop := vk.getD n 0
  let vv := (vtop <<< 30) ||| vk.getD (n - 1) 0
  let q0 ← chk32 (vv / wm1)
  let (q, _) ← qLoop wm1 wm2 (vk.getD (n - 2) 0) 2 q0 (vv % wm1)
  let (r, zhi) ← subLoop q (vk.take n) w 0
  if (vtop : Int) + zhi < 0 then
    let (r', _) ← vIAddGo r w 0
    return (q - 1, r')
  else return (q, r)

/-- What the sign of `vtop + zhi` says, longobject.c:3347-3348: `t` is 0 or -1. -/
theorem divStep_value {V W Pn r q : Nat} {t : Int}
    (hPn : W ≤ Pn) (hr : r < Pn)
    (e : (r : Int) + (Pn : Int) * t = (V : Int) - ((q * W : Nat) : Int))
    (h1 : V < (q + 1) * W) (h2 : (q - 1) * W ≤ V) :
    (0 ≤ t → V = q * W + r) ∧ (t < 0 → 1 ≤ q ∧ V + Pn = q * W + r) := by
  have hqw : (q + 1) * W = q * W + W := by grind
  constructor
  · intro h0
    obtain ⟨T, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    have e' : (r : Int) + ((Pn * T : Nat) : Int) = (V : Int) - ((q * W : Nat) : Int) := by
      rw [e.symm]; simp
    have hT : T = 0 := by
      rcases Nat.eq_zero_or_pos T with h | h
      · exact h
      · have : Pn ≤ Pn * T := Nat.le_mul_of_pos_right _ h
        omega
    subst hT
    simp only [Nat.mul_zero] at e'
    omega
  · intro h0
    obtain ⟨T, hT⟩ : ∃ T : Nat, t = -((T + 1 : Nat) : Int) := ⟨(-t - 1).toNat, by omega⟩
    subst hT
    have e' : ((Pn * (T + 1) : Nat) : Int) = (r : Int) - (V : Int) + ((q * W : Nat) : Int) := by
      have h3 := e
      rw [Int.mul_neg] at h3
      have : ((Pn * (T + 1) : Nat) : Int) = (Pn : Int) * ((T + 1 : Nat) : Int) := by simp
      omega
    have hq : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h
        have : Pn ≤ Pn * (T + 1) := Nat.le_mul_of_pos_right _ (by omega)
        simp only [Nat.zero_mul] at e'
        omega
      · exact h
    obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at h2
    have hpw : (p + 1) * W = p * W + W := by grind
    have hT : T = 0 := by
      rcases Nat.eq_zero_or_pos T with h | h
      · exact h
      · have : Pn * 2 ≤ Pn * (T + 1) := Nat.mul_le_mul_left _ (by omega)
        omega
    subst hT
    simp only [Nat.zero_add, Nat.mul_one] at e'
    exact ⟨by omega, by omega⟩

theorem getD3 (l : List Nat) (a b c : Nat) :
    (l ++ [a, b, c]).getD l.length 0 = a ∧ (l ++ [a, b, c]).getD (l.length + 1) 0 = b ∧
      (l ++ [a, b, c]).getD (l.length + 2) 0 = c := by
  simp [List.getD, List.getElem?_append_right]

theorem split3 {vk : List Nat} {m : Nat} (h : vk.length = m + 3) :
    ∃ vl a b c, vk = vl ++ [a, b, c] ∧ vl.length = m := by
  have hd : (vk.drop m).length = 3 := by simp; omega
  match hr : vk.drop m, hd with
  | [a, b, c], _ =>
    refine ⟨vk.take m, a, b, c, ?_, by simp; omega⟩
    rw [← hr, List.take_append_drop]

/-- `vtop <= wm1`, the assert at longobject.c:3314. -/
theorem vtop_le {X B vl vm vtop wl wm2 wm1 : Nat} (hB : 0 < B) (hX : 0 < X) (hwl : wl < X)
    (hw2 : wm2 < B)
    (h : vl + X * B * vm + X * B * B * vtop < B * (wl + X * wm2 + X * B * wm1)) :
    vtop ≤ wm1 := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have a1 : X * B * B * (wm1 + 1) ≤ X * B * B * vtop := Nat.mul_le_mul_left _ hlt
  have a2 : B * (wl + 1) ≤ B * X := Nat.mul_le_mul_left _ hwl
  have a3 : X * B * (wm2 + 1) ≤ X * B * B := Nat.mul_le_mul_left _ hw2
  have e1 : B * (wl + X * wm2 + X * B * wm1) = B * wl + X * B * wm2 + X * B * B * wm1 := by grind
  have e2 : X * B * B * (wm1 + 1) = X * B * B * wm1 + X * B * B := by grind
  have e3 : B * (wl + 1) = B * wl + B := by grind
  have e4 : X * B * (wm2 + 1) = X * B * wm2 + X * B := by grind
  have e5 : B * X = X * B := Nat.mul_comm _ _
  omega

theorem val3 (l : List Nat) (a b c : Nat) :
    val (l ++ [a, b, c]) = val l + 2 ^ (30 * l.length) * a +
      2 ^ (30 * l.length) * 2 ^ 30 * b + 2 ^ (30 * l.length) * 2 ^ 30 * 2 ^ 30 * c := by
  rw [val_append]
  simp only [val_cons, val_nil, Nat.mul_zero, Nat.add_zero]
  generalize 2 ^ (30 * l.length) = X
  generalize (2 : Nat) ^ 30 = B
  grind

theorem val2 (l : List Nat) (a b : Nat) :
    val (l ++ [a, b]) = val l + 2 ^ (30 * l.length) * a + 2 ^ (30 * l.length) * 2 ^ 30 * b := by
  rw [val_append]
  simp only [val_cons, val_nil, Nat.mul_zero, Nat.add_zero]
  generalize 2 ^ (30 * l.length) = X
  generalize (2 : Nat) ^ 30 = B
  grind

/-- One quotient digit of Algorithm D is exact: with a normalized divisor and
`V < BASE * W`, the digit is `V // W`, the remainder `V % W`, and no intermediate
leaves its C type. -/
theorem divStep_spec {wl vk : List Nat} {wm1 wm2 : Nat} (hw : IsDigits (wl ++ [wm2, wm1]))
    (h1 : 2 ^ 29 ≤ wm1) (hvk : IsDigits vk) (hlen : vk.length = wl.length + 3)
    (hlt : val vk < 2 ^ 30 * val (wl ++ [wm2, wm1])) :
    ∃ q r, divStep (wl ++ [wm2, wm1]) wm1 wm2 vk = .ok (q, r) ∧ q < 2 ^ 30 ∧ IsDigits r ∧
      r.length = wl.length + 2 ∧ val r < val (wl ++ [wm2, wm1]) ∧
      val vk = q * val (wl ++ [wm2, wm1]) + val r := by
  obtain ⟨vl, v2, v1, vtop, rfl, hvl⟩ := split3 hlen
  obtain ⟨dwl, dw2⟩ := isDigits_append.1 hw
  obtain ⟨hw2, dw3⟩ := isDigits_cons.1 dw2
  obtain ⟨hw1, _⟩ := isDigits_cons.1 dw3
  obtain ⟨dvl, dv3⟩ := isDigits_append.1 hvk
  obtain ⟨hv2, dv4⟩ := isDigits_cons.1 dv3
  obtain ⟨hv1, dv5⟩ := isDigits_cons.1 dv4
  obtain ⟨hvt, _⟩ := isDigits_cons.1 dv5
  have hlvl : val vl < 2 ^ (30 * wl.length) := by
    have := val_lt dvl; rwa [hvl] at this
  have hlwl : val wl < 2 ^ (30 * wl.length) := val_lt dwl
  have hX : 0 < 2 ^ (30 * wl.length) := Nat.pow_pos (by decide)
  have eV := val3 vl v2 v1 vtop
  have eW := val2 wl wm2 wm1
  rw [hvl] at eV
  generalize hXd : 2 ^ (30 * wl.length) = X at *
  generalize hVd : val (vl ++ [v2, v1, vtop]) = V at *
  generalize hWd : val (wl ++ [wm2, wm1]) = W at *
  have hle : vtop ≤ wm1 := by
    refine vtop_le (B := 2 ^ 30) (X := X) (vl := val vl + X * v2) (vm := v1) (wl := val wl)
      (wm2 := wm2) (by decide) hX hlwl hw2 ?_
    rw [← eW]
    omega
  -- the estimate
  have hor : (vtop <<< 30) ||| v1 = vtop * 2 ^ 30 + v1 := shl_or vtop v1 30 hv1
  generalize hvv : vtop * 2 ^ 30 + v1 = vv at *
  have hVv : V = val vl + X * v2 + X * 2 ^ 30 * vv := by
    rw [eV, ← hvv]
    generalize (2 : Nat) ^ 30 = B
    grind
  have hw0 : 0 < wm1 := by omega
  have hvvle : vv ≤ wm1 * 2 ^ 30 + (2 ^ 30 - 1) := by
    have : vtop * 2 ^ 30 ≤ wm1 * 2 ^ 30 := Nat.mul_le_mul_right _ hle
    omega
  have hq0 : vv / wm1 ≤ 2 ^ 30 + 1 := by
    have : vv / wm1 < 2 ^ 30 + 2 := by
      apply Nat.div_lt_of_lt_mul
      have e : wm1 * (2 ^ 30 + 2) = wm1 * 2 ^ 30 + 2 * wm1 := by grind
      omega
    omega
  have hup0 : vv < wm1 * (vv / wm1 + 1) := Nat.lt_mul_div_succ _ hw0
  have hdm : vv = wm1 * (vv / wm1) + vv % wm1 := (Nat.div_add_mod vv wm1).symm
  have hrlt : vv % wm1 < wm1 := Nat.mod_lt _ hw0
  obtain ⟨q, r, hq, q1, q2, q3, q4⟩ := qLoop_spec (vv := vv) (V := V) (W := W) (vl := val vl)
    (wl := val wl) (X := X) (v2 := v2) hVv eW hlvl h1 hw1 hw2 hv2 2 (vv / wm1) (vv % wm1)
    (by omega) hdm (by omega) (est_upper hVv eW hlvl hv2 hup0) (by omega) hq0
  have hover : (q - 1) * W ≤ V := by
    refine est_overshoot eW q4 ?_ (est_exit hVv eW hlwl q1 q3)
    have : 2 ^ 30 * 2 ^ 29 ≤ 2 ^ 30 * wm1 := Nat.mul_le_mul_left _ h1
    omega
  have hWpos : 0 < W := by
    have : X * 2 ^ 30 * 1 ≤ X * 2 ^ 30 * wm1 := Nat.mul_le_mul_left _ hw0
    have : 0 < X * 2 ^ 30 := Nat.mul_pos hX (by decide)
    omega
  have hqB : q ≤ 2 ^ 30 := by
    have : (q - 1) * W < 2 ^ 30 * W := by
      have e := Nat.mul_comm (2 ^ 30) W
      omega
    have := Nat.lt_of_mul_lt_mul_right this
    omega
  -- multiply and subtract
  have htake : (vl ++ [v2, v1, vtop]).take (wl ++ [wm2, wm1]).length = vl ++ [v2, v1] := by
    have e : vl ++ [v2, v1, vtop] = (vl ++ [v2, v1]) ++ [vtop] := by simp
    have hlen2 : (wl ++ [wm2, wm1]).length = (vl ++ [v2, v1]).length := by simp [hvl]
    rw [e, hlen2, List.take_left]
  have dlow : IsDigits (vl ++ [v2, v1]) :=
    isDigits_append.2 ⟨dvl, isDigits_cons.2 ⟨hv2, isDigits_cons.2 ⟨hv1, isDigits_nil⟩⟩⟩
  obtain ⟨r1, z, hr1, d1, l1, _, _, v1'⟩ := subLoop_spec hqB (vl ++ [v2, v1]) (wl ++ [wm2, wm1]) 0
    dlow hw (by simp [hvl]) (by omega) (by omega)
  have hlenlow : (vl ++ [v2, v1]).length = wl.length + 2 := by simp [hvl]
  rw [hlenlow] at l1 v1'
  rw [hWd] at v1'
  generalize hPn : 2 ^ (30 * (wl.length + 2)) = Pn at *
  have hWPn : W ≤ Pn := by
    have := val_lt hw
    rw [hWd] at this
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    rw [hPn] at this
    omega
  have hr1lt : val r1 < Pn := by
    have := val_lt d1
    rw [l1, hPn] at this
    exact this
  have hVsplit : V = val (vl ++ [v2, v1]) + Pn * vtop := by
    have e2 := val2 vl v2 v1
    rw [hvl, hXd] at e2
    have e3 : Pn = X * 2 ^ 30 * 2 ^ 30 := by
      rw [← hPn, show 30 * (wl.length + 2) = 30 * wl.length + 30 + 30 by omega, Nat.pow_add,
        Nat.pow_add, hXd]
    rw [e2, e3, eV]
  have ee : (val r1 : Int) + (Pn : Int) * ((vtop : Int) + z) = (V : Int) - ((q * W : Nat) : Int) := by
    subst hVsplit
    push_cast
    rw [Int.mul_add]
    have := v1'
    grind
  obtain ⟨c1, c2⟩ := divStep_value hWPn hr1lt ee q2 hover
  have ht := getD3 vl v2 v1 vtop
  rw [hvl] at ht
  have hlw : (wl ++ [wm2, wm1]).length = wl.length + 2 := by simp
  have hg1 : (vl ++ [v2, v1, vtop]).getD (wl ++ [wm2, wm1]).length 0 = vtop := by
    rw [hlw]; exact ht.2.2
  have hg2 : (vl ++ [v2, v1, vtop]).getD ((wl ++ [wm2, wm1]).length - 1) 0 = v1 := by
    rw [hlw]; exact ht.2.1
  have hg3 : (vl ++ [v2, v1, vtop]).getD ((wl ++ [wm2, wm1]).length - 2) 0 = v2 := by
    rw [hlw]; exact ht.1
  have hq32 : vv / wm1 < 2 ^ 32 := by omega
  by_cases hneg : (vtop : Int) + z < 0
  · obtain ⟨hq1, hbig⟩ := c2 hneg
    have dwhole := hw
    obtain ⟨r', c, hr', d2, l2, _, v2'⟩ := vIAddGo_spec r1 (wl ++ [wm2, wm1]) 0 d1 hw
      (by simp [l1]) (by omega)
    rw [hWd, l1, hPn] at v2'
    simp only [Nat.add_zero] at v2'
    have hrw : q * W = (q - 1) * W + W := by
      obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      grind
    have hlt2 : V - (q - 1) * W < W := by omega
    have hr'lt : val r' < Pn := by
      have := val_lt d2
      rw [l2, l1, hPn] at this
      exact this
    have hval : val r' = V - (q - 1) * W := by
      refine eq_of_add_mul_eq (M := Pn) (c := c) (d := 1) hr'lt (by omega) ?_
      omega
    refine ⟨q - 1, r', ?_, by omega, d2, by omega, by omega, by omega⟩
    simp only [divStep, hg1, hg2, hg3, htake, hor, chk32_ok hq32, bind_ok, hq, hr1]
    rw [if_pos hneg]
    simp only [hr', bind_ok, pure_ok]
  · have hval := c1 (by omega)
    have hqlt : q < 2 ^ 30 := by
      have h3 : q * W < 2 ^ 30 * W := by omega
      exact Nat.lt_of_mul_lt_mul_right h3
    refine ⟨q, r1, ?_, hqlt, d1, by omega, ?_, hval⟩
    · simp only [divStep, hg1, hg2, hg3, htake, hor, chk32_ok hq32, bind_ok, hq, hr1]
      rw [if_neg hneg]
      simp only [pure_ok]
    · have e := (Nat.add_mul q 1 W)
      simp only [Nat.one_mul] at e
      omega

end PyLean.LongObj
