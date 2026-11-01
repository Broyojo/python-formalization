import PyLean.LongObj.AddSub

/-!
`x_mul`, longobject.c:3831-3926, both the gradeschool path and the squaring path
(HAC 14.16) taken when the two operands are the same object. Every `twodigits`
carry is checked to fit `uint64_t`, every pointer store to stay in the buffer.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt

/-! ## Gradeschool -/

/-- One outer iteration of the gradeschool path, longobject.c:3914-3922: add
`f * b[0:]` into `z` starting at the row's offset. -/
def mulRow (f : Nat) : List Nat → List Nat → Nat → Py (List Nat)
  | zs, [], carry =>
    if carry ≠ 0 then
      match zs with
      | z :: t => do
        let s ← chk32 (z + (carry &&& MASK))
        return s :: t
      | [] => .error cOverflow
    else .ok zs
  | z :: zs, b :: bs, carry => do
    let c ← chk64 (carry + (z + b * f))
    let r ← mulRow f zs bs (c >>> 30)
    return (c &&& MASK) :: r
  | [], _ :: _, _ => .error cOverflow

/-- The outer loop `for (i = 0; i < size_a; ++i)`, longobject.c:3902-3923. The
argument `zs` is `z + i`; the digit below it is finished. -/
def schoolLoop (bs : List Nat) : List Nat → List Nat → Py (List Nat)
  | [], zs => .ok zs
  | f :: as, zs => do
    let zs' ← mulRow f zs bs 0
    match zs' with
    | z0 :: t => do
      let r ← schoolLoop bs as t
      return z0 :: r
    | [] => .error cOverflow

theorem digit_mul_le {b f : Nat} (hb : b < 2 ^ 30) (hf : f < 2 ^ 30) :
    b * f ≤ (2 ^ 30 - 1) * (2 ^ 30 - 1) :=
  Nat.mul_le_mul (by omega) (by omega)

theorem mulRow_spec {f : Nat} (hf : f < 2 ^ 30) : ∀ (bs mid tail : List Nat) (carry : Nat),
    IsDigits bs → IsDigits mid → mid.length = bs.length → carry ≤ MASK →
    ∃ mid', mulRow f (mid ++ 0 :: tail) bs carry = .ok (mid' ++ tail) ∧ IsDigits mid' ∧
      mid'.length = bs.length + 1 ∧ val mid' = val mid + f * val bs + carry
  | [], [], tail, carry, _, _, _, hc => by
    have hc' : carry < 2 ^ 30 := by simp only [MASK] at hc; omega
    have hm : carry &&& MASK = carry := by rw [and30]; exact Nat.mod_eq_of_lt hc'
    by_cases h0 : carry = 0
    · subst h0
      exact ⟨[0], by simp [mulRow], isDigits_cons.2 ⟨by decide, isDigits_nil⟩, rfl, by simp⟩
    · refine ⟨[carry], ?_, isDigits_cons.2 ⟨hc', isDigits_nil⟩, rfl, by simp⟩
      simp only [List.nil_append, mulRow, ne_eq, h0, not_false_eq_true, ite_true, hm, Nat.zero_add]
      rw [chk32_ok (by omega)]
      rfl
  | b :: bs, z :: mid, tail, carry, hb, hm, hl, hc => by
    have ⟨hb0, hbs⟩ := isDigits_cons.1 hb
    have ⟨hz, hmid⟩ := isDigits_cons.1 hm
    have hbf := digit_mul_le hb0 hf
    simp only [MASK] at hc
    have hc64 : carry + (z + b * f) < 2 ^ 64 := by omega
    have ⟨c1, c2⟩ := carry_step (x := carry + (z + b * f))
    have hc' : (carry + (z + b * f)) >>> 30 ≤ MASK := by
      rw [shr30]; simp only [MASK]; omega
    obtain ⟨m, hr, h1, h2, h3⟩ := mulRow_spec hf bs mid tail _ hbs hmid (by simpa using hl) hc'
    refine ⟨((carry + (z + b * f)) &&& MASK) :: m, ?_, isDigits_cons.2 ⟨c1, h1⟩, by simp [h2], ?_⟩
    · simp only [List.cons_append, mulRow, chk64_ok hc64, bind_ok, hr, pure_ok]
    · simp only [val_cons, h3]
      generalize ((carry + (z + b * f)) &&& MASK) = d at *
      generalize ((carry + (z + b * f)) >>> 30) = e at *
      grind
  | [], _ :: _, _, _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, _, _, hl, _ => by simp at hl

theorem schoolLoop_spec {bs : List Nat} (hb : IsDigits bs) : ∀ (as mid : List Nat),
    IsDigits as → IsDigits mid → mid.length = bs.length →
    ∃ r, schoolLoop bs as (mid ++ List.replicate as.length 0) = .ok r ∧ IsDigits r ∧
      r.length = bs.length + as.length ∧ val r = val mid + val as * val bs
  | [], mid, _, hm, hl => ⟨mid, by simp [schoolLoop], hm, by simp [hl], by simp⟩
  | f :: as, mid, ha, hm, hl => by
    have ⟨hf, has⟩ := isDigits_cons.1 ha
    obtain ⟨m', hr, h1, h2, h3⟩ := mulRow_spec hf bs mid (List.replicate as.length 0) 0 hb hm hl
      (by simp [MASK])
    match m', h1, h2, h3, hr with
    | z0 :: m, h1, h2, h3, hr =>
      have ⟨hz0, hmm⟩ := isDigits_cons.1 h1
      have hlm : m.length = bs.length := by simpa using h2
      obtain ⟨r, hr', r1, r2, r3⟩ := schoolLoop_spec hb as m has hmm hlm
      refine ⟨z0 :: r, ?_, isDigits_cons.2 ⟨hz0, r1⟩, by simp [r2]; omega, ?_⟩
      · simp only [schoolLoop, List.length_cons, List.replicate_succ, hr, bind_ok,
          List.cons_append, hr', pure_ok]
      · simp only [val_cons, r3] at h3 ⊢
        grind

/-! ## Squaring -/

/-- `if (carry) { ... }`, longobject.c:3877-3898. -/
def sqEnd (zs : List Nat) (carry : Nat) : Py (List Nat) :=
  if carry ≠ 0 then
    match zs with
    | [] => .error cOverflow
    | e :: t => do
      let c ← chk64 (carry + e)
      let d := c &&& MASK
      let c' := c >>> 30
      if c' ≠ 0 then
        match t with
        | [] => .error cOverflow
        | _ :: t' => return d :: c' :: t'
      else return d :: t
  else .ok zs

/-- `while (pa < paend)`, longobject.c:3871-3876. -/
def sqInner (f : Nat) : List Nat → List Nat → Nat → Py (List Nat)
  | [], zs, carry => sqEnd zs carry
  | p :: pa, z :: zs, carry => do
    let c ← chk64 (carry + (z + p * f))
    let r ← sqInner f pa zs (c >>> 30)
    return (c &&& MASK) :: r
  | _ :: _, [], _ => .error cOverflow

/-- One outer iteration of the squaring path, longobject.c:3853-3898. `pa` is
`a + i + 1`, `zs` is `z + 2*i`. -/
def sqRow (f : Nat) (pa : List Nat) (zs : List Nat) : Py (List Nat) :=
  match zs with
  | [] => .error cOverflow
  | z :: zs => do
    let c ← chk64 (z + f * f)
    let r ← sqInner (f <<< 1) pa zs (c >>> 30)
    return (c &&& MASK) :: r

/-- The outer loop of the squaring path, longobject.c:3851-3899. -/
def sqLoop : List Nat → List Nat → Py (List Nat)
  | [], zs => .ok zs
  | f :: as, zs => do
    let r ← sqRow f as zs
    match r with
    | z0 :: z1 :: t => do
      let s ← sqLoop as t
      return z0 :: z1 :: s
    | _ => .error cOverflow

/-- Shape of the digits at and above the carry position after a row: one digit,
then a digit at most 1 (the only store above the pyramid), then zeros. -/
def EndShape (k : Nat) (t : List Nat) : Prop :=
  t.length = k + 1 ∧ IsDigits t ∧ ∀ j, k = j + 1 → ∃ d e, t = d :: e :: List.replicate j 0 ∧ e ≤ 1

theorem sqEnd_spec {k e carry : Nat} (he : e ≤ 1) (hc : carry ≤ 2 * 2 ^ 30 - 2)
    (hv : val (e :: List.replicate k 0) + carry < 2 ^ (30 * (k + 1))) :
    ∃ r, sqEnd (e :: List.replicate k 0) carry = .ok r ∧ EndShape k r ∧
      val r = e + carry := by
  have hrep : IsDigits (List.replicate k 0) := isDigits_replicate_zero k
  simp only [val_cons, val_replicate_zero, Nat.mul_zero, Nat.add_zero] at hv
  by_cases h0 : carry = 0
  · subst h0
    refine ⟨e :: List.replicate k 0, by simp [sqEnd], ⟨by simp, isDigits_cons.2 ⟨by omega, hrep⟩, ?_⟩,
      by simp [val_replicate_zero]⟩
    intro j hj
    subst hj
    exact ⟨e, 0, by simp [List.replicate_succ], by omega⟩
  · have hlt : carry + e < 2 ^ 64 := by omega
    have ⟨c1, c2⟩ := carry_step (x := carry + e)
    have hc1 : (carry + e) >>> 30 ≤ 1 := by rw [shr30]; omega
    by_cases hc0 : (carry + e) >>> 30 = 0
    · refine ⟨((carry + e) &&& MASK) :: List.replicate k 0, ?_,
        ⟨by simp, isDigits_cons.2 ⟨c1, hrep⟩, ?_⟩, ?_⟩
      · simp only [sqEnd, ne_eq, h0, not_false_eq_true, ite_true, chk64_ok hlt, bind_ok, hc0,
          not_true_eq_false, ite_false, pure_ok]
      · intro j hj
        subst hj
        exact ⟨(carry + e) &&& MASK, 0, by simp [List.replicate_succ], by omega⟩
      · simp only [val_cons, val_replicate_zero, Nat.mul_zero, Nat.add_zero]
        omega
    · have hc2 : (carry + e) >>> 30 = 1 := by omega
      cases k with
      | zero =>
        exfalso
        rw [hc2] at c2
        rw [show 30 * (0 + 1) = 30 from rfl] at hv
        omega
      | succ j =>
        refine ⟨((carry + e) &&& MASK) :: 1 :: List.replicate j 0, ?_,
          ⟨by simp, isDigits_cons.2 ⟨c1, isDigits_cons.2 ⟨by decide,
            isDigits_replicate_zero j⟩⟩, ?_⟩, ?_⟩
        · simp only [sqEnd, ne_eq, h0, not_false_eq_true, ite_true, chk64_ok hlt, bind_ok, hc2,
            Nat.one_ne_zero, List.replicate_succ, pure_ok]
        · intro i hi
          have : i = j := by omega
          subst this
          exact ⟨_, 1, rfl, by omega⟩
        · simp only [val_cons, val_replicate_zero, Nat.mul_zero, Nat.add_zero]
          omega

theorem sqInner_spec {f e k : Nat} (hf : f ≤ 2 * 2 ^ 30 - 2) (he : e ≤ 1) :
    ∀ (pa mid : List Nat) (carry : Nat), IsDigits pa → IsDigits mid → mid.length = pa.length →
    carry ≤ 2 * 2 ^ 30 - 2 →
    val (mid ++ e :: List.replicate k 0) + f * val pa + carry < 2 ^ (30 * (pa.length + k + 1)) →
    ∃ m t, sqInner f pa (mid ++ e :: List.replicate k 0) carry = .ok (m ++ t) ∧
      m.length = pa.length ∧ IsDigits m ∧ EndShape k t ∧
      val (m ++ t) = val (mid ++ e :: List.replicate k 0) + f * val pa + carry
  | [], [], carry, _, _, _, hc, hv => by
    have hv' : val (e :: List.replicate k 0) + carry < 2 ^ (30 * (k + 1)) := by
      simpa using hv
    obtain ⟨r, hr, h1, h2⟩ := sqEnd_spec he hc hv'
    refine ⟨[], r, by simpa [sqInner] using hr, rfl, isDigits_nil, h1, ?_⟩
    simp [h2, val_replicate_zero]
  | p :: pa, z :: mid, carry, hp, hm, hl, hc, hv => by
    have ⟨hp0, hpa⟩ := isDigits_cons.1 hp
    have ⟨hz, hmid⟩ := isDigits_cons.1 hm
    have hpf : p * f ≤ (2 ^ 30 - 1) * (2 * 2 ^ 30 - 2) := Nat.mul_le_mul (by omega) hf
    have hc64 : carry + (z + p * f) < 2 ^ 64 := by omega
    have ⟨c1, c2⟩ := carry_step (x := carry + (z + p * f))
    have hc' : (carry + (z + p * f)) >>> 30 ≤ 2 * 2 ^ 30 - 2 := by rw [shr30]; omega
    have hlen : mid.length = pa.length := by simpa using hl
    have hv' : val (mid ++ e :: List.replicate k 0) + f * val pa +
        (carry + (z + p * f)) >>> 30 < 2 ^ (30 * (pa.length + k + 1)) := by
      simp only [List.cons_append, val_cons, List.length_cons] at hv
      rw [show 30 * (pa.length + 1 + k + 1) = 30 + 30 * (pa.length + k + 1) by omega,
        Nat.pow_add] at hv
      generalize hM : 2 ^ (30 * (pa.length + k + 1)) = M at *
      generalize val (mid ++ e :: List.replicate k 0) = V at *
      generalize ((carry + (z + p * f)) >>> 30) = C at *
      generalize ((carry + (z + p * f)) &&& MASK) = D at *
      have : 2 ^ 30 * (V + f * val pa + C) < 2 ^ 30 * M := by
        have e1 : 2 ^ 30 * (V + f * val pa + C) = 2 ^ 30 * V + f * (2 ^ 30 * val pa) + 2 ^ 30 * C := by
          grind
        have e2 : f * (p + 2 ^ 30 * val pa) = f * p + f * (2 ^ 30 * val pa) := by grind
        rw [e2, Nat.mul_comm f p] at hv
        rw [e1]
        omega
      exact Nat.lt_of_mul_lt_mul_left this
    obtain ⟨m, t, hr, h1, h2, h3, h4⟩ := sqInner_spec hf he pa mid _ hpa hmid hlen hc' hv'
    refine ⟨((carry + (z + p * f)) &&& MASK) :: m, t, ?_, by simp [h1],
      isDigits_cons.2 ⟨c1, h2⟩, h3, ?_⟩
    · simp only [List.cons_append, sqInner, chk64_ok hc64, bind_ok, hr, pure_ok]
    · simp only [List.cons_append, val_cons] at h4 ⊢
      rw [h4]
      generalize ((carry + (z + p * f)) >>> 30) = C at *
      generalize ((carry + (z + p * f)) &&& MASK) = D at *
      grind
  | [], _ :: _, _, _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, _, _, hl, _, _ => by simp at hl

theorem sqRow_spec {f e k z : Nat} {mid pa : List Nat} (hf : f < 2 ^ 30) (he : e ≤ 1)
    (hz : z < 2 ^ 30) (hpa : IsDigits pa) (hm : IsDigits mid) (hl : mid.length = pa.length)
    (hv : val (z :: mid ++ e :: List.replicate k 0) + f * f + 2 * f * 2 ^ 30 * val pa
      < 2 ^ (30 * (pa.length + k + 2))) :
    ∃ d m t, sqRow f pa (z :: mid ++ e :: List.replicate k 0) = .ok (d :: (m ++ t)) ∧
      d < 2 ^ 30 ∧ m.length = pa.length ∧ IsDigits m ∧ EndShape k t ∧
      val (d :: (m ++ t)) = val (z :: mid ++ e :: List.replicate k 0) + f * f
        + 2 * f * 2 ^ 30 * val pa := by
  have hff := digit_mul_le hf hf
  have hc64 : z + f * f < 2 ^ 64 := by omega
  have ⟨c1, c2⟩ := carry_step (x := z + f * f)
  have hc' : (z + f * f) >>> 30 ≤ 2 * 2 ^ 30 - 2 := by rw [shr30]; omega
  have hf2 : f <<< 1 = 2 * f := by simp [Nat.shiftLeft_eq, Nat.mul_comm]
  have hv' : val (mid ++ e :: List.replicate k 0) + f <<< 1 * val pa + (z + f * f) >>> 30
      < 2 ^ (30 * (pa.length + k + 1)) := by
    simp only [List.cons_append, val_cons] at hv
    rw [show 30 * (pa.length + k + 2) = 30 + 30 * (pa.length + k + 1) by omega, Nat.pow_add] at hv
    rw [hf2]
    generalize 2 ^ (30 * (pa.length + k + 1)) = M at *
    generalize val (mid ++ e :: List.replicate k 0) = V at *
    generalize ((z + f * f) >>> 30) = C at *
    generalize ((z + f * f) &&& MASK) = D at *
    have : 2 ^ 30 * (V + 2 * f * val pa + C) < 2 ^ 30 * M := by
      have e1 : 2 ^ 30 * (V + 2 * f * val pa + C) = 2 ^ 30 * V + 2 * f * 2 ^ 30 * val pa + 2 ^ 30 * C := by
        grind
      rw [e1]
      omega
    exact Nat.lt_of_mul_lt_mul_left this
  obtain ⟨m, t, hr, h1, h2, h3, h4⟩ := sqInner_spec (e := e) (k := k) (f := f <<< 1)
    (by rw [hf2]; omega) he pa mid _ hpa hm hl hc' hv'
  refine ⟨_, m, t, ?_, c1, h1, h2, h3, ?_⟩
  · simp only [List.cons_append, sqRow, chk64_ok hc64, bind_ok, hr, pure_ok]
  · simp only [List.cons_append, val_cons] at h4 ⊢
    rw [h4, hf2]
    generalize ((z + f * f) >>> 30) = C at *
    generalize ((z + f * f) &&& MASK) = D at *
    generalize val (mid ++ e :: List.replicate k 0) = V at *
    have e1 : 2 ^ 30 * (V + 2 * f * val pa + C) = 2 ^ 30 * V + 2 ^ 30 * C + 2 * f * 2 ^ 30 * val pa := by
      grind
    rw [e1]
    omega

theorem sq_expand (f R : Nat) :
    (f + 2 ^ 30 * R) * (f + 2 ^ 30 * R) = f * f + 2 * f * 2 ^ 30 * R + 2 ^ 30 * (2 ^ 30 * (R * R)) := by
  grind

theorem sq_nest (d z1 V RR : Nat) : d + 2 ^ 30 * (z1 + 2 ^ 30 * (V + RR)) =
    d + 2 ^ 30 * z1 + 2 ^ 30 * (2 ^ 30 * V) + 2 ^ 30 * (2 ^ 30 * RR) := by
  simp only [Nat.mul_add, Nat.add_assoc]

theorem sq_next_bound {d z1 V RR W F G M : Nat}
    (h4 : d + 2 ^ 30 * (z1 + 2 ^ 30 * V) = W + F + G)
    (hv : W + (F + G + 2 ^ 30 * (2 ^ 30 * RR)) < 2 ^ 30 * 2 ^ 30 * M) : V + RR < M := by
  have e0 := sq_nest d z1 V RR
  have e1 := sq_nest d z1 V 0
  simp only [Nat.mul_zero, Nat.add_zero] at e1
  have e2 : (2 : Nat) ^ 30 * 2 ^ 30 * M = 2 ^ 30 * (2 ^ 30 * M) := Nat.mul_assoc _ _ _
  have e3 : 2 ^ 30 * (2 ^ 30 * (V + RR)) = 2 ^ 30 * (2 ^ 30 * V) + 2 ^ 30 * (2 ^ 30 * RR) := by
    simp only [Nat.mul_add]
  have : 2 ^ 30 * (2 ^ 30 * (V + RR)) < 2 ^ 30 * (2 ^ 30 * M) := by omega
  exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_mul_lt_mul_left this)

theorem sq_final {d z1 V RR W F G : Nat}
    (h4 : d + 2 ^ 30 * (z1 + 2 ^ 30 * V) = W + F + G) :
    d + 2 ^ 30 * (z1 + 2 ^ 30 * (V + RR)) = W + (F + G + 2 ^ 30 * (2 ^ 30 * RR)) := by
  have e0 := sq_nest d z1 V RR
  have e1 := sq_nest d z1 V 0
  simp only [Nat.mul_zero, Nat.add_zero] at e1
  omega

theorem sqLoop_nil (f : Nat) (m : List Nat) (e : Nat)
    (hd : IsDigits (f :: ([] : List Nat))) (hl : m.length = ([] : List Nat).length + 1) (hm : IsDigits m) (he : e ≤ 1)
    (hv : val (m ++ e :: List.replicate ([] : List Nat).length 0) + val (f :: ([] : List Nat)) * val (f :: ([] : List Nat))
      < 2 ^ (30 * (2 * ([] : List Nat).length + 2))) :
    ∃ r, sqLoop (f :: ([] : List Nat)) (m ++ e :: List.replicate ([] : List Nat).length 0) = .ok r ∧ IsDigits r ∧
      r.length = 2 * ([] : List Nat).length + 2 ∧
      val r = val (m ++ e :: List.replicate ([] : List Nat).length 0) + val (f :: ([] : List Nat)) * val (f :: ([] : List Nat)) := by
    match m, hl, hm with
    | [z], _, hm =>
      have ⟨hf, hrest⟩ := isDigits_cons.1 hd
      have ⟨hz, _⟩ := isDigits_cons.1 hm
      have hff := digit_mul_le hf hf
      have hv' : val (z :: ([] : List Nat) ++ e :: List.replicate 0 0) + f * f +
          2 * f * 2 ^ 30 * val ([] : List Nat)
          < 2 ^ (30 * (([] : List Nat).length + 0 + 2)) := by
        simp only [val_cons, val_nil, Nat.mul_zero, Nat.add_zero] at hv ⊢
        simpa using hv
      obtain ⟨d, m2, t, hr, d1, h1, h2, h3, h4⟩ := sqRow_spec (k := 0) hf he hz isDigits_nil
        isDigits_nil rfl hv'
      obtain ⟨tl, tdig, _⟩ := h3
      match m2, t, tl with
      | [], [d1'], _ =>
        have hr' : sqRow f [] [z, e] = .ok [d, d1'] := by simpa using hr
        refine ⟨[d, d1'], ?_, isDigits_cons.2 ⟨d1, tdig⟩, rfl, ?_⟩
        · simp only [List.cons_append, List.nil_append, sqLoop, List.length_nil,
            List.replicate_zero, hr', bind_ok, pure_ok]
        · simp only [val_cons, val_nil, List.cons_append, List.nil_append, List.replicate_zero,
            List.length_nil, Nat.mul_zero, Nat.add_zero] at h4 ⊢
          omega
      | _ :: _, _, _ => simp at h1
    | [], hl, _ => simp at hl
    | _ :: _ :: _, hl, _ => simp at hl

theorem sqLoop_cons (f2 : Nat) (rest2 : List Nat)
    (ih : ∀ (f : Nat) (m : List Nat) (e : Nat),
      IsDigits (f :: rest2) → m.length = rest2.length + 1 → IsDigits m → e ≤ 1 →
      val (m ++ e :: List.replicate rest2.length 0) + val (f :: rest2) * val (f :: rest2)
        < 2 ^ (30 * (2 * rest2.length + 2)) →
      ∃ r, sqLoop (f :: rest2) (m ++ e :: List.replicate rest2.length 0) = .ok r ∧ IsDigits r ∧
        r.length = 2 * rest2.length + 2 ∧
        val r = val (m ++ e :: List.replicate rest2.length 0) + val (f :: rest2) * val (f :: rest2))
    (f : Nat) (m : List Nat) (e : Nat)
    (hd : IsDigits (f :: (f2 :: rest2))) (hl : m.length = (f2 :: rest2).length + 1) (hm : IsDigits m) (he : e ≤ 1)
    (hv : val (m ++ e :: List.replicate (f2 :: rest2).length 0) + val (f :: (f2 :: rest2)) * val (f :: (f2 :: rest2))
      < 2 ^ (30 * (2 * (f2 :: rest2).length + 2))) :
    ∃ r, sqLoop (f :: (f2 :: rest2)) (m ++ e :: List.replicate (f2 :: rest2).length 0) = .ok r ∧ IsDigits r ∧
      r.length = 2 * (f2 :: rest2).length + 2 ∧
      val r = val (m ++ e :: List.replicate (f2 :: rest2).length 0) + val (f :: (f2 :: rest2)) * val (f :: (f2 :: rest2)) := by
    have ⟨hf, hrest⟩ := isDigits_cons.1 hd
    match m, hl, hm with
    | z :: mid, hl, hm =>
      have ⟨hz, hmid⟩ := isDigits_cons.1 hm
      have hlm : mid.length = (f2 :: rest2).length := by simpa using hl
      have hexp := sq_expand f (val (f2 :: rest2))
      have hvexp : val (f :: f2 :: rest2) = f + 2 ^ 30 * val (f2 :: rest2) := rfl
      rw [hvexp, hexp] at hv ⊢
      have hv' : val (z :: mid ++ e :: List.replicate (f2 :: rest2).length 0) + f * f +
          2 * f * 2 ^ 30 * val (f2 :: rest2) <
            2 ^ (30 * ((f2 :: rest2).length + (f2 :: rest2).length + 2)) := by
        rw [show 30 * ((f2 :: rest2).length + (f2 :: rest2).length + 2)
          = 30 * (2 * (f2 :: rest2).length + 2) by omega]
        omega
      obtain ⟨d, m2, t, hr, d1, h1, h2, h3, h4⟩ := sqRow_spec hf he hz hrest hmid hlm hv'
      obtain ⟨tl, tdig, tshape⟩ := h3
      match m2, h1, h2 with
      | z1 :: m3, h1, h2 =>
        have hl3 : m3.length = rest2.length := by simpa using h1
        obtain ⟨d2, e2, ht, he2⟩ := tshape rest2.length (by simp)
        subst ht
        have ⟨hz1, hm3⟩ := isDigits_cons.1 h2
        have ⟨hd2, htail⟩ := isDigits_cons.1 tdig
        have hnext : m3 ++ d2 :: e2 :: List.replicate rest2.length 0 =
            (m3 ++ [d2]) ++ e2 :: List.replicate rest2.length 0 := by simp
        have hl4 : (m3 ++ [d2]).length = rest2.length + 1 := by simp [hl3]
        have hd4 : IsDigits (m3 ++ [d2]) :=
          isDigits_append.2 ⟨hm3, isDigits_cons.2 ⟨hd2, isDigits_nil⟩⟩
        have hexpr : val (d :: ((z1 :: m3) ++ d2 :: e2 :: List.replicate rest2.length 0)) =
            d + 2 ^ 30 * (z1 + 2 ^ 30 * val (m3 ++ d2 :: e2 :: List.replicate rest2.length 0)) := by
          simp
        rw [hexpr] at h4
        generalize hW : val (z :: mid ++ e :: List.replicate (f2 :: rest2).length 0) = W at *
        have hvnext : val ((m3 ++ [d2]) ++ e2 :: List.replicate rest2.length 0) +
            val (f2 :: rest2) * val (f2 :: rest2) < 2 ^ (30 * (2 * rest2.length + 2)) := by
          rw [← hnext]
          simp only [List.length_cons] at hv
          rw [show 30 * (2 * (rest2.length + 1) + 2) = 30 + 30 + 30 * (2 * rest2.length + 2) by omega,
            Nat.pow_add, Nat.pow_add] at hv
          exact sq_next_bound h4 hv
        obtain ⟨s, hs, s1, s2, s3⟩ := ih f2 (m3 ++ [d2]) e2 hrest hl4 hd4 he2 hvnext
        refine ⟨d :: z1 :: s, ?_, isDigits_cons.2 ⟨d1, isDigits_cons.2 ⟨hz1, s1⟩⟩, ?_, ?_⟩
        · have hr' : sqRow f (f2 :: rest2) (z :: mid ++ e :: List.replicate (f2 :: rest2).length 0)
              = .ok (d :: z1 :: ((m3 ++ [d2]) ++ e2 :: List.replicate rest2.length 0)) := by
            rw [hr]
            simp
          rw [sqLoop, hr']
          simp only [bind_ok, hs, pure_ok]
        · simp [s2]; omega
        · rw [← hnext] at s3
          rw [val_cons, val_cons, s3]
          exact sq_final h4
      | [], h1, _ => simp at h1
    | [], hl, _ => simp at hl


theorem sqLoop_spec (rest : List Nat) : ∀ (f : Nat) (m : List Nat) (e : Nat),
    IsDigits (f :: rest) → m.length = rest.length + 1 → IsDigits m → e ≤ 1 →
    val (m ++ e :: List.replicate rest.length 0) + val (f :: rest) * val (f :: rest)
      < 2 ^ (30 * (2 * rest.length + 2)) →
    ∃ r, sqLoop (f :: rest) (m ++ e :: List.replicate rest.length 0) = .ok r ∧ IsDigits r ∧
      r.length = 2 * rest.length + 2 ∧
      val r = val (m ++ e :: List.replicate rest.length 0) + val (f :: rest) * val (f :: rest) := by
  induction rest with
  | nil => exact sqLoop_nil
  | cons f2 rest2 ih => exact sqLoop_cons f2 rest2 ih

/-! ## `x_mul` -/

/-- `x_mul(a, b)`, longobject.c:3831-3926. `same` is the pointer test `a == b` at :3843. -/
def xMul (same : Bool) (a b : List Nat) : Py (List Nat) := do
  longAlloc (a.length + b.length)
  let z := List.replicate (a.length + b.length) 0
  let r ← if same then sqLoop a z else schoolLoop b a z
  return normalize r

theorem mul_lt_pow {a b : List Nat} (ha : IsDigits a) (hb : IsDigits b) :
    val a * val b < 2 ^ (30 * (a.length + b.length)) := by
  have h1 := val_lt ha
  have h2 := val_lt hb
  rw [Nat.mul_add, Nat.pow_add]
  exact Nat.mul_lt_mul'' h1 h2

/-- `x_mul` is exact for all digit vectors on both paths, and no `twodigits` or
`digit` intermediate wraps. -/
theorem xMul_spec {same : Bool} {a b : List Nat} (ha : IsDigits a) (hb : IsDigits b)
    (hsame : same = true → a = b) (hs : a.length + b.length ≤ maxLongDigits) :
    xMul same a b = .ok (digitsOf (val a * val b)) := by
  unfold xMul
  rw [longAlloc_ok hs]
  simp only [bind_ok]
  cases same with
  | true =>
    have hab := hsame rfl
    subst hab
    match a, ha with
    | [], _ =>
      simp [sqLoop, normalize, topNonzero, bind_ok, pure_ok]
    | f :: rest, ha =>
      have hz : List.replicate ((f :: rest).length + (f :: rest).length) 0 =
          List.replicate (rest.length + 1) 0 ++ 0 :: List.replicate rest.length 0 := by
        rw [← List.replicate_succ, List.replicate_append_replicate]
        congr 1
      have hzv : val (List.replicate (rest.length + 1) 0 ++ 0 :: List.replicate rest.length 0) = 0 := by
        rw [← hz, val_replicate_zero]
      have hb' := mul_lt_pow ha ha
      obtain ⟨r, hr, h1, _, h3⟩ := sqLoop_spec rest f (List.replicate (rest.length + 1) 0) 0 ha
        (by simp) (isDigits_replicate_zero _) (by omega)
        (by rw [hzv, Nat.zero_add]
            simp only [List.length_cons] at hb'
            rw [show 30 * (2 * rest.length + 2) = 30 * (rest.length + 1 + (rest.length + 1)) by omega]
            exact hb')
      simp only [ite_true, hz, hr, bind_ok, pure_ok]
      rw [digitsOf_normalize h1, h3, hzv, Nat.zero_add]
  | false =>
    have := schoolLoop_spec hb a (List.replicate b.length 0) ha (isDigits_replicate_zero _) (by simp)
    obtain ⟨r, hr, h1, _, h3⟩ := this
    rw [List.replicate_append_replicate, Nat.add_comm b.length] at hr
    simp only [Bool.false_eq_true, ite_false, hr, bind_ok, pure_ok]
    rw [digitsOf_normalize h1, h3, val_replicate_zero, Nat.zero_add]

end PyLean.LongObj
