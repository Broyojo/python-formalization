import PyLean.LongObj.Mul

/-!
`kmul_split`, `k_mul`, `k_lopsided_mul` and `long_mul`, longobject.c:4039-4357.

`same` models the pointer test `a == b`. The recursion carries explicit fuel, and
each store into `ret` is checked to stay inside the allocation: a `memcpy` or
`v_iadd` past the end is reported as `cOverflow`. `kMulF_spec` therefore also
proves the "(*) Why adding t3 can't run out of room" comment at :4233-4276.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt

/-- `KARATSUBA_CUTOFF`, longobject.c:84. -/
def karatsubaCutoff : Nat := 70
/-- `KARATSUBA_SQUARE_CUTOFF`, longobject.c:85. -/
def karatsubaSquareCutoff : Nat := 2 * karatsubaCutoff

/-- `kmul_split(n, size, &high, &low)`, longobject.c:4039-4064; returns `(high, low)`. -/
def kmulSplit (n : List Nat) (size : Nat) : Py (List Nat × List Nat) :=
  let sizeLo := min n.length size
  let sizeHi := n.length - sizeLo
  do
    longAlloc sizeHi
    longAlloc sizeLo
    return (normalize (n.drop sizeLo), normalize (n.take sizeLo))

/-- The loop of `k_lopsided_mul`, longobject.c:4310-4330. `b` is what remains of
the input (`b + nbdone`), `ret` is `ret + nbdone`, `mul` is `k_mul(a, -)`. -/
def lopLoop (mul : List Nat → Py (List Nat)) (asize : Nat) :
    Nat → List Nat → List Nat → Py (List Nat)
  | 0, _, _ => .error .modelFuel
  | f + 1, b, ret =>
    if 0 < b.length then
      let n := min b.length asize
      do
        let product ← mul (b.take n)
        if ret.length < product.length then .error cOverflow
        else
          let (ret', _) ← vIAdd ret product
          let rest ← lopLoop mul asize f (b.drop n) (ret'.drop n)
          return ret'.take n ++ rest
    else .ok ret

/-- Steps 2 to 6 of `k_mul`, longobject.c:4152-4222, once the operands are split. -/
def kMulCombine (mul : Bool → List Nat → List Nat → Py (List Nat)) (same : Bool)
    (rsize shift : Nat) (ah al bh bl : List Nat) : Py (List Nat) := do
  longAlloc rsize
  let t1 ← mul same ah bh
  if rsize < 2 * shift + t1.length then .error cOverflow
  else
    let high := t1 ++ List.replicate (rsize - 2 * shift - t1.length) 0
    let t2 ← mul same al bl
    if 2 * shift < t2.length then .error cOverflow
    else
      let ret := t2 ++ List.replicate (2 * shift - t2.length) 0 ++ high
      let lo := ret.take shift
      let up := ret.drop shift
      if up.length < t2.length ∨ up.length < t1.length then .error cOverflow
      else
        let up := (vISub up t2).1
        let up := (vISub up t1).1
        let s1 ← xAdd ah al
        let s2 ← if same = true then pure s1 else xAdd bh bl
        let t3 ← mul same s1 s2
        if up.length < t3.length then .error cOverflow
        else
          let (up, _) ← vIAdd up t3
          return normalize (lo ++ up)

/-- The part of `k_mul`, longobject.c:4107-4222, after the swap at :4097-4105 has
made `a` the shorter operand. `k_lopsided_mul` (:4287-4339) is inlined; its
recursive calls are never on one object, so `same` is false there. -/
def kMulBody (mul : Bool → List Nat → List Nat → Py (List Nat)) (same : Bool)
    (a b : List Nat) : Py (List Nat) :=
  let asize := a.length
  let bsize := b.length
  let i := if same = true then karatsubaSquareCutoff else karatsubaCutoff
  if asize ≤ i then
    if asize = 0 then .ok [] else xMul same a b
  else if 2 * asize ≤ bsize then do
    longAlloc (asize + bsize)
    longAlloc asize
    let ret ← lopLoop (mul false a) asize (bsize + 1) b (List.replicate (asize + bsize) 0)
    return normalize ret
  else
    let shift := bsize >>> 1
    do
      let (ah, al) ← kmulSplit a shift
      let (bh, bl) ← if same = true then pure (ah, al) else kmulSplit b shift
      kMulCombine mul same (asize + bsize) shift ah al bh bl

/-- `k_mul(a, b)`, longobject.c:4073-4231. -/
def kMulF : Nat → Bool → List Nat → List Nat → Py (List Nat)
  | 0, _, _, _ => .error .modelFuel
  | fuel + 1, same, a, b =>
    if a.length > b.length then kMulBody (kMulF fuel) same b a
    else kMulBody (kMulF fuel) same a b

/-- Fuel that `k_mul` never exhausts: the digit count of the operands bounds the
recursion depth. -/
def kMul (same : Bool) (a b : List Nat) : Py (List Nat) :=
  kMulF (a.length + b.length + 1) same a b

theorem digitCount_le_of_lt {V k : Nat} (h : V < 2 ^ (30 * k)) : digitCount V ≤ k := by
  have := bitLength_le_of_lt' h
  unfold digitCount
  omega

theorem length_digitsOf_le {V k : Nat} (h : V < 2 ^ (30 * k)) : (digitsOf V).length ≤ k := by
  rw [length_digitsOf]
  exact digitCount_le_of_lt h

/-- Uniqueness modulo `M`: the only step that lets the borrows and carries out of
the high digit be ignored. -/
theorem eq_of_add_mul_eq {x w M c d : Nat} (hx : x < M) (hw : w < M)
    (h : x + M * c = w + M * d) : x = w := by
  have := congrArg (· % M) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hw] at this
  exact this

/-- `kmul_split` on a split point inside the vector. -/
theorem kmulSplit_le {n : List Nat} {size : Nat} (hn : IsDigits n)
    (hs : n.length ≤ maxLongDigits) (hle : size ≤ n.length) :
    kmulSplit n size = .ok (digitsOf (val (n.drop size)), digitsOf (val (n.take size))) := by
  have hmin : min n.length size = size := by omega
  simp only [kmulSplit, hmin]
  rw [longAlloc_ok (by omega), longAlloc_ok (by omega)]
  simp only [bind_ok, pure_ok]
  rw [digitsOf_normalize (isDigits_drop hn _), digitsOf_normalize (isDigits_take hn _)]

theorem val_split {n : List Nat} {size : Nat} (hle : size ≤ n.length) :
    val n = val (n.take size) + 2 ^ (30 * size) * val (n.drop size) := by
  have := val_take_add_drop n size
  rwa [List.length_take, Nat.min_eq_left hle] at this

theorem lopLoop_spec {mul : List Nat → Py (List Nat)} {asize A : Nat} (ha : 0 < asize)
    (hA : A < 2 ^ (30 * asize))
    (hmul : ∀ s, IsDigits s → s.length ≤ asize → mul s = .ok (digitsOf (A * val s))) :
    ∀ (f : Nat) (b ret : List Nat), b.length < f → IsDigits b → IsDigits ret →
      b.length + asize ≤ ret.length → val ret + A * val b < 2 ^ (30 * ret.length) →
      ∃ r, lopLoop mul asize f b ret = .ok r ∧ IsDigits r ∧ r.length = ret.length ∧
        val r = val ret + A * val b := by
  intro f
  induction f with
  | zero => intro b ret h; exact absurd h (Nat.not_lt_zero _)
  | succ f ih =>
    intro b ret hf hb hret hlen hv
    by_cases hb0 : 0 < b.length
    · have hn : min b.length asize ≤ asize := by omega
      have hn1 : 0 < min b.length asize := by omega
      generalize hnn : min b.length asize = n at *
      have hnb : n ≤ b.length := by omega
      have hb1 := isDigits_take hb n
      have hsplit := val_split hnb
      have hprod := hmul (b.take n) hb1 (by simp; omega)
      have hPlt : A * val (b.take n) < 2 ^ (30 * (asize + n)) := by
        rw [Nat.mul_add, Nat.pow_add]
        exact Nat.mul_lt_mul'' hA (val_le_of_len hb1 (by simp; omega))
      have hplen : (digitsOf (A * val (b.take n))).length ≤ asize + n := length_digitsOf_le hPlt
      have hplen' : (digitsOf (A * val (b.take n))).length ≤ ret.length := by omega
      obtain ⟨r', c, hr', d1, l1, c1, v1⟩ := vIAddGo_spec ret (digitsOf (A * val (b.take n))) 0
        hret (digitsOf_digits _) hplen' (by omega)
      simp only [val_digitsOf, Nat.add_zero] at v1
      -- the carry out of the high digit is zero
      have hP2 : A * val b = A * val (b.take n) + 2 ^ (30 * n) * (A * val (b.drop n)) := by
        rw [hsplit, Nat.mul_add]
        generalize 2 ^ (30 * n) = P
        generalize val (b.take n) = X
        generalize val (b.drop n) = Y
        rw [Nat.mul_left_comm]
      generalize hPP : 2 ^ (30 * ret.length) = M at *
      have hc : c = 0 := by
        rcases Nat.eq_zero_or_pos c with h0 | h0
        · exact h0
        · have := Nat.mul_le_mul_left M h0
          omega
      subst hc
      simp only [Nat.mul_zero, Nat.add_zero] at v1
      have hnr : n ≤ r'.length := by omega
      have hsplitr := val_split (n := r') hnr
      have hlen' : (b.drop n).length + asize ≤ (r'.drop n).length := by
        simp only [List.length_drop]; omega
      have hdrop : (r'.drop n).length = r'.length - n := by simp
      have hM : M = 2 ^ (30 * n) * 2 ^ (30 * (r'.drop n).length) := by
        rw [← hPP, ← Nat.pow_add, hdrop, l1]
        congr 1
        omega
      have hv' : val (r'.drop n) + A * val (b.drop n) < 2 ^ (30 * (r'.drop n).length) := by
        generalize 2 ^ (30 * (r'.drop n).length) = Q at *
        generalize hPn : 2 ^ (30 * n) = Pn at *
        apply Nat.lt_of_mul_lt_mul_left (a := Pn)
        rw [Nat.mul_add]
        have e : val r' + Pn * (A * val (b.drop n)) < M := by omega
        rw [hsplitr] at e
        rw [← hM]
        omega
      obtain ⟨r, hr, r1, r2, r3⟩ := ih (b.drop n) (r'.drop n) (by simp; omega)
        (isDigits_drop hb _) (isDigits_drop d1 _) hlen' hv'
      refine ⟨r'.take n ++ r, ?_, isDigits_append.2 ⟨isDigits_take d1 _, r1⟩, ?_, ?_⟩
      · have hvia : vIAdd ret (digitsOf (A * val (b.take n))) = .ok (r', 0) := hr'
        simp only [lopLoop, hb0, ite_true, hnn, hprod, bind_ok]
        rw [if_neg (by omega), hvia]
        simp only [bind_ok, hr, pure_ok]
      · simp only [List.length_append, List.length_take, r2, List.length_drop]
        omega
      · rw [val_append, r3]
        simp only [List.length_take, Nat.min_eq_left hnr]
        generalize hPn : 2 ^ (30 * n) = Pn at *
        generalize val (r'.drop n) = U at *
        generalize A * val (b.drop n) = T at *
        generalize val (r'.take n) = L at *
        rw [Nat.mul_add]
        omega
    · have hb' : b = [] := by
        cases b with
        | nil => rfl
        | cons _ _ => simp at hb0
      subst hb'
      refine ⟨ret, by simp [lopLoop], hret, rfl, by simp⟩

/-- Algebra of steps 4 to 6: if the digits below `shift` plus the digits above it
hold `T2 + X*X*T1`, then subtracting `T2` and `T1` and adding `T3` at `shift`,
ignoring carries out of the top, leaves the true product. -/
theorem karatsuba_algebra {X M L U U1 U2 U3 T1 T2 T3 P W b1 b2 c : Nat}
    (hX : 0 < X) (hP : P < X * M) (hU3 : U3 < M)
    (hW : L + X * W = P)
    (hWU : W + T1 + T2 = U + T3)
    (h1 : U1 + T2 = U + M * b1)
    (h2 : U2 + T1 = U1 + M * b2)
    (h3 : U3 + M * c = U2 + T3) :
    L + X * U3 = P := by
  have hWM : W < M := by
    have : X * W < X * M := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  have e : U3 + M * c = W + M * (b1 + b2) := by
    rw [Nat.mul_add]
    omega
  rw [eq_of_add_mul_eq hU3 hWM e, hW]

theorem kar_ring (X Ah Al Bh Bl : Nat) :
    (Al + X * Ah) * (Bl + X * Bh) =
      Al * Bl + X * (X * (Ah * Bh)) + X * (Ah * Bl + Al * Bh) := by
  grind

theorem kar_ring2 (Ah Al Bh Bl U : Nat) :
    (U + (Ah * Bl + Al * Bh)) + Ah * Bh + Al * Bl = U + (Ah + Al) * (Bh + Bl) := by
  grind

theorem val_pad {l h : List Nat} {k n : Nat} (hl : l.length + k = n) :
    val (l ++ List.replicate k 0 ++ h) = val l + 2 ^ (30 * n) * val h := by
  rw [val_append, val_append, val_replicate_zero, Nat.mul_zero, Nat.add_zero, List.length_append,
    List.length_replicate, hl]

theorem val_pad_end {l : List Nat} (k : Nat) : val (l ++ List.replicate k 0) = val l := by
  rw [val_append, val_replicate_zero, Nat.mul_zero, Nat.add_zero]

theorem sum_lt_two {x y p p1 p2 : Nat} (hx : x < 2 ^ (30 * p1)) (hy : y < 2 ^ (30 * p2))
    (h1 : p1 ≤ p) (h2 : p2 ≤ p) : x + y < 2 * 2 ^ (30 * p) := by
  have e1 : 2 ^ (30 * p1) ≤ 2 ^ (30 * p) := Nat.pow_le_pow_right (by decide) (by omega)
  have e2 : 2 ^ (30 * p2) ≤ 2 ^ (30 * p) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem two_mul_pow_le {p : Nat} : 2 * 2 ^ (30 * p) ≤ 2 ^ (30 * (p + 1)) := by
  rw [show 30 * (p + 1) = 30 + 30 * p by omega, Nat.pow_add]
  exact Nat.mul_le_mul_right _ (by decide)

/-- Steps 2 to 6 of `k_mul` compute the product, stay inside `ret`, and overflow
nothing. The bound on `t3` is the "(*)" comment at longobject.c:4233-4276. -/
theorem kMulCombine_spec {mul : Bool → List Nat → List Nat → Py (List Nat)} {same : Bool}
    {sa sb shift Ah Al Bh Bl V : Nat}
    (hmul : ∀ x y, IsDigits x → IsDigits y → (same = true → x = y) →
      x.length + y.length < sa + sb → mul same x y = .ok (digitsOf (val x * val y)))
    (hs : sa + sb + 2 ≤ maxLongDigits) (hbig : 70 < sa) (hle : sa ≤ sb)
    (hsh : sb / 2 = shift) (hnl : ¬ 2 * sa ≤ sb)
    (dAh : Ah < 2 ^ (30 * (sa - shift))) (dAl : Al < 2 ^ (30 * shift))
    (dBh : Bh < 2 ^ (30 * (sb - shift))) (dBl : Bl < 2 ^ (30 * shift))
    (hsame : same = true → Ah = Bh ∧ Al = Bl)
    (hV : V = (Al + 2 ^ (30 * shift) * Ah) * (Bl + 2 ^ (30 * shift) * Bh))
    (hVlt : V < 2 ^ (30 * (sa + sb))) :
    kMulCombine mul same (sa + sb) shift (digitsOf Ah) (digitsOf Al) (digitsOf Bh) (digitsOf Bl)
      = .ok (digitsOf V) := by
  have hsa : shift + 1 ≤ sa := by omega
  have hsb1 : 2 * shift ≤ sb := by omega
  have hsb2 : sb ≤ 2 * shift + 1 := by omega
  have hshp : 1 ≤ shift := by omega
  have lAh : (digitsOf Ah).length ≤ sa - shift := length_digitsOf_le dAh
  have lAl : (digitsOf Al).length ≤ shift := length_digitsOf_le dAl
  have lBh : (digitsOf Bh).length ≤ sb - shift := length_digitsOf_le dBh
  have lBl : (digitsOf Bl).length ≤ shift := length_digitsOf_le dBl
  have ht1 : mul same (digitsOf Ah) (digitsOf Bh) = .ok (digitsOf (Ah * Bh)) := by
    have := hmul _ _ (digitsOf_digits Ah) (digitsOf_digits Bh)
      (fun h => by rw [(hsame h).1]) (by omega)
    rwa [val_digitsOf, val_digitsOf] at this
  have ht2 : mul same (digitsOf Al) (digitsOf Bl) = .ok (digitsOf (Al * Bl)) := by
    have := hmul _ _ (digitsOf_digits Al) (digitsOf_digits Bl)
      (fun h => by rw [(hsame h).2]) (by omega)
    rwa [val_digitsOf, val_digitsOf] at this
  have lt1 : (digitsOf (Ah * Bh)).length ≤ (sa - shift) + (sb - shift) :=
    length_digitsOf_le (by rw [Nat.mul_add, Nat.pow_add]; exact Nat.mul_lt_mul'' dAh dBh)
  have lt2 : (digitsOf (Al * Bl)).length ≤ shift + shift :=
    length_digitsOf_le (by rw [Nat.mul_add, Nat.pow_add]; exact Nat.mul_lt_mul'' dAl dBl)
  have vt1 := val_digitsOf (Ah * Bh)
  have vt2 := val_digitsOf (Al * Bl)
  have dt1 := digitsOf_digits (Ah * Bh)
  have dt2 := digitsOf_digits (Al * Bl)
  generalize digitsOf (Ah * Bh) = t1 at *
  generalize digitsOf (Al * Bl) = t2 at *
  have c1 : ¬ (sa + sb < 2 * shift + t1.length) := by omega
  have c2 : ¬ (2 * shift < t2.length) := by omega
  obtain ⟨ret, hret⟩ : ∃ r, r = t2 ++ List.replicate (2 * shift - t2.length) 0 ++
      (t1 ++ List.replicate (sa + sb - 2 * shift - t1.length) 0) := ⟨_, rfl⟩
  have lret : ret.length = sa + sb := by
    rw [hret]; simp only [List.length_append, List.length_replicate]; omega
  have dret : IsDigits ret := by
    rw [hret]
    exact isDigits_append.2 ⟨isDigits_append.2 ⟨dt2, isDigits_replicate_zero _⟩,
      isDigits_append.2 ⟨dt1, isDigits_replicate_zero _⟩⟩
  have vret : val ret = val t2 + 2 ^ (30 * (2 * shift)) * val t1 := by
    rw [hret, val_pad (n := 2 * shift) (by omega), val_pad_end]
  have hsplit := val_split (n := ret) (size := shift) (by omega)
  obtain ⟨lo, hlo⟩ : ∃ l, l = ret.take shift := ⟨_, rfl⟩
  obtain ⟨up, hup⟩ : ∃ l, l = ret.drop shift := ⟨_, rfl⟩
  rw [← hlo, ← hup] at hsplit
  have llo : lo.length = shift := by rw [hlo]; simp; omega
  have lup : up.length = sa + sb - shift := by rw [hup]; simp; omega
  have dlo : IsDigits lo := by rw [hlo]; exact isDigits_take dret _
  have dup : IsDigits up := by rw [hup]; exact isDigits_drop dret _
  have c3 : ¬ (up.length < t2.length ∨ up.length < t1.length) := by omega
  have s1 := vISubGo_spec up t2 0 dup dt2 (by omega) (by omega)
  generalize hp1 : vISubGo up t2 0 = p1 at s1
  obtain ⟨U1, b1⟩ := p1
  simp only at s1
  obtain ⟨d1, _, l1, v1⟩ := s1
  have s2 := vISubGo_spec U1 t1 0 d1 dt1 (by omega) (by omega)
  generalize hp2 : vISubGo U1 t1 0 = p2 at s2
  obtain ⟨U2, b2⟩ := p2
  simp only at s2
  obtain ⟨d2, _, l2, v2⟩ := s2
  have hs1 : xAdd (digitsOf Ah) (digitsOf Al) = .ok (digitsOf (Ah + Al)) := by
    rw [xAdd_spec (digitsOf_digits _) (digitsOf_digits _) (by omega), val_digitsOf, val_digitsOf]
  have hs2 : xAdd (digitsOf Bh) (digitsOf Bl) = .ok (digitsOf (Bh + Bl)) := by
    rw [xAdd_spec (digitsOf_digits _) (digitsOf_digits _) (by omega), val_digitsOf, val_digitsOf]
  have ha1 : Ah + Al < 2 * 2 ^ (30 * (sa - 1)) := sum_lt_two dAh dAl (by omega) (by omega)
  have hb1 : Bh + Bl < 2 * 2 ^ (30 * (sb - shift)) := sum_lt_two dBh dBl (by omega) (by omega)
  have la1 : (digitsOf (Ah + Al)).length ≤ sb - shift + 1 := by
    apply length_digitsOf_le
    have h1 := sum_lt_two (p := sb - shift) dAh dAl (by omega) (by omega)
    exact Nat.lt_of_lt_of_le h1 two_mul_pow_le
  have lb1 : (digitsOf (Bh + Bl)).length ≤ sb - shift + 1 :=
    length_digitsOf_le (Nat.lt_of_lt_of_le hb1 two_mul_pow_le)
  have ht3 : mul same (digitsOf (Ah + Al)) (digitsOf (Bh + Bl))
      = .ok (digitsOf ((Ah + Al) * (Bh + Bl))) := by
    have := hmul _ _ (digitsOf_digits (Ah + Al)) (digitsOf_digits (Bh + Bl))
      (fun h => by rw [(hsame h).1, (hsame h).2]) (by omega)
    rwa [val_digitsOf, val_digitsOf] at this
  have lt3 : (digitsOf ((Ah + Al) * (Bh + Bl))).length ≤ sa + sb - shift := by
    apply length_digitsOf_le
    have h1 := Nat.mul_lt_mul'' ha1 hb1
    have e : (2 * 2 ^ (30 * (sa - 1))) * (2 * 2 ^ (30 * (sb - shift))) ≤
        2 ^ (30 * (sa + sb - shift)) := by
      have e2 : (2 * 2 ^ (30 * (sa - 1))) * (2 * 2 ^ (30 * (sb - shift))) =
          4 * 2 ^ (30 * (sa - 1 + (sb - shift))) := by
        rw [Nat.mul_add 30, Nat.pow_add]
        generalize 2 ^ (30 * (sa - 1)) = P
        generalize 2 ^ (30 * (sb - shift)) = Q
        grind
      rw [e2, show 30 * (sa + sb - shift) = 30 + 30 * (sa - 1 + (sb - shift)) by omega, Nat.pow_add]
      exact Nat.mul_le_mul_right _ (by decide)
    omega
  have vt3 := val_digitsOf ((Ah + Al) * (Bh + Bl))
  have dt3 := digitsOf_digits ((Ah + Al) * (Bh + Bl))
  generalize digitsOf ((Ah + Al) * (Bh + Bl)) = t3 at *
  have c4 : ¬ (U2.length < t3.length) := by omega
  obtain ⟨U3, c, h3, d3, l3, _, v3⟩ := vIAddGo_spec U2 t3 0 d2 dt3 (by omega) (by omega)
  simp only [Nat.add_zero] at v1 v2 v3
  have hfinal : val (lo ++ U3) = V := by
    rw [val_append, llo]
    have hX : 0 < 2 ^ (30 * shift) := Nat.pow_pos (by decide)
    have hXM : V < 2 ^ (30 * shift) * 2 ^ (30 * U2.length) := by
      rw [← Nat.pow_add, show 30 * shift + 30 * U2.length = 30 * (sa + sb) by omega]
      exact hVlt
    have hU3 : val U3 < 2 ^ (30 * U2.length) := by
      have := val_lt d3
      rwa [l3] at this
    have h2s : 2 ^ (30 * (2 * shift)) = 2 ^ (30 * shift) * 2 ^ (30 * shift) := by
      rw [← Nat.pow_add]; congr 1; omega
    have hL : val lo + 2 ^ (30 * shift) * val up =
        Al * Bl + 2 ^ (30 * shift) * (2 ^ (30 * shift) * (Ah * Bh)) := by
      rw [← hsplit, vret, h2s, vt1, vt2, Nat.mul_assoc]
    have hWdef := kar_ring (2 ^ (30 * shift)) Ah Al Bh Bl
    have hW2 := kar_ring2 Ah Al Bh Bl (val up)
    refine karatsuba_algebra (W := val up + (Ah * Bl + Al * Bh)) (M := 2 ^ (30 * U2.length))
      (U := val up) (U1 := val U1) (U2 := val U2) (T1 := Ah * Bh) (T2 := Al * Bl)
      (T3 := (Ah + Al) * (Bh + Bl)) (b1 := b1) (b2 := b2) (c := c)
      hX hXM hU3 ?_ hW2 ?_ ?_ ?_
    · rw [Nat.mul_add, ← Nat.add_assoc, hL, hV, hWdef]
    · rw [← vt2, l2, l1]
      exact v1
    · rw [← vt1, l2]
      exact v2
    · rw [← vt3]
      exact v3
  have hfin : normalize (lo ++ U3) = digitsOf V := by
    rw [digitsOf_normalize (isDigits_append.2 ⟨dlo, d3⟩), hfinal]
  have hp1' : (vISub up t2).1 = U1 := by simp only [vISub, hp1]
  have hp2' : (vISub U1 t1).1 = U2 := by simp only [vISub, hp2]
  have h3' : vIAdd U2 t3 = .ok (U3, c) := h3
  unfold kMulCombine
  rw [longAlloc_ok (by omega)]
  simp only [bind_ok, ht1, c1, ite_false, ht2, c2]
  rw [← hret, ← hlo, ← hup]
  simp only [c3, ite_false, hp1', hp2', hs1, bind_ok]
  by_cases h : same = true
  · obtain ⟨e1, e2⟩ := hsame h
    subst e1; subst e2
    rw [if_pos h]
    simp only [pure_ok, bind_ok, ht3, c4, ite_false, h3', hfin]
  · rw [if_neg h]
    simp only [hs2, bind_ok, ht3, c4, ite_false, h3', pure_ok, hfin]

theorem kMulBody_spec {mul : Bool → List Nat → List Nat → Py (List Nat)} {same : Bool}
    {a b : List Nat} (hda : IsDigits a) (hdb : IsDigits b) (hsm : same = true → a = b)
    (hs : a.length + b.length + 2 ≤ maxLongDigits) (hle : a.length ≤ b.length)
    (hmul : ∀ s x y, IsDigits x → IsDigits y → (s = true → x = y) →
      x.length + y.length < a.length + b.length → mul s x y = .ok (digitsOf (val x * val y))) :
    kMulBody mul same a b = .ok (digitsOf (val a * val b)) := by
  simp only [kMulBody]
  by_cases hsmall : a.length ≤ (if same = true then karatsubaSquareCutoff else karatsubaCutoff)
  · rw [if_pos hsmall]
    by_cases hz : a.length = 0
    · rw [if_pos hz]
      have : a = [] := List.eq_nil_of_length_eq_zero hz
      subst this
      simp
    · rw [if_neg hz]
      exact xMul_spec hda hdb hsm (by omega)
  · rw [if_neg hsmall]
    have hbig : 70 < a.length := by
      simp only [karatsubaSquareCutoff, karatsubaCutoff] at hsmall
      split at hsmall <;> omega
    by_cases hlop : 2 * a.length ≤ b.length
    · rw [if_pos hlop, longAlloc_ok (by omega), longAlloc_ok (by omega)]
      simp only [bind_ok]
      have hmul' : ∀ s, IsDigits s → s.length ≤ a.length →
          mul false a s = .ok (digitsOf (val a * val s)) :=
        fun s hsd hsl => hmul false a s hda hsd (by simp) (by omega)
      have hbound : val (List.replicate (a.length + b.length) 0) + val a * val b
          < 2 ^ (30 * (List.replicate (a.length + b.length) 0).length) := by
        rw [val_replicate_zero, Nat.zero_add, List.length_replicate]
        exact mul_lt_pow hda hdb
      obtain ⟨r, hr, r1, _, r3⟩ := lopLoop_spec (by omega) (val_lt hda) hmul' (b.length + 1) b
        (List.replicate (a.length + b.length) 0) (by omega) hdb (isDigits_replicate_zero _)
        (by simp; omega) hbound
      simp only [hr, bind_ok, pure_ok]
      rw [digitsOf_normalize r1, r3, val_replicate_zero, Nat.zero_add]
    · rw [if_neg hlop]
      have hshift : b.length >>> 1 = b.length / 2 := by simp [Nat.shiftRight_eq_div_pow]
      rw [hshift]
      generalize hsh : b.length / 2 = shift at *
      have hsha : shift ≤ a.length := by omega
      have hshb : shift ≤ b.length := by omega
      have hsplitA := kmulSplit_le (size := shift) hda (by omega) hsha
      have hsplitB := kmulSplit_le (size := shift) hdb (by omega) hshb
      have vA := val_split (n := a) hsha
      have vB := val_split (n := b) hshb
      have dAh := val_lt (isDigits_drop hda shift)
      have dBh := val_lt (isDigits_drop hdb shift)
      rw [List.length_drop] at dAh dBh
      have dAl := val_le_of_len (isDigits_take hda shift) (n := shift) (by simp; omega)
      have dBl := val_le_of_len (isDigits_take hdb shift) (n := shift) (by simp; omega)
      have hcomb := kMulCombine_spec (fun x y h1 h2 h3 h4 => hmul same x y h1 h2 h3 h4) hs hbig hle
        hsh hlop dAh dAl dBh dBl
        (fun h => by have := hsm h; subst this; exact ⟨rfl, rfl⟩)
        (by rw [← vA, ← vB]) (mul_lt_pow hda hdb)
      rw [hsplitA]
      simp only [bind_ok]
      by_cases h : same = true
      · rw [if_pos h]
        have := hsm h
        subst this
        simp only [pure_ok, bind_ok]
        exact hcomb
      · rw [if_neg h, hsplitB]
        simp only [bind_ok]
        exact hcomb

/-- `k_mul` is exact for all digit vectors, including the non-normalized `bslice`
of `k_lopsided_mul`. -/
theorem kMulF_spec : ∀ (fuel : Nat) (same : Bool) (a b : List Nat),
    a.length + b.length < fuel → IsDigits a → IsDigits b → (same = true → a = b) →
    a.length + b.length + 2 ≤ maxLongDigits →
    kMulF fuel same a b = .ok (digitsOf (val a * val b)) := by
  intro fuel
  induction fuel with
  | zero => intro same a b h; exact absurd h (Nat.not_lt_zero _)
  | succ fuel ih =>
    intro same a b hf ha hb hsame hs
    simp only [kMulF]
    by_cases hsw : a.length > b.length
    · rw [if_pos hsw, Nat.mul_comm]
      exact kMulBody_spec hb ha (fun h => (hsame h).symm) (by omega) (by omega)
        (fun s x y h1 h2 h3 h4 => ih s x y (by omega) h1 h2 h3 (by omega))
    · rw [if_neg hsw]
      exact kMulBody_spec ha hb hsame (by omega) (by omega)
        (fun s x y h1 h2 h3 h4 => ih s x y (by omega) h1 h2 h3 (by omega))

theorem kMul_spec {same : Bool} {a b : List Nat} (ha : IsDigits a) (hb : IsDigits b)
    (hsame : same = true → a = b) (hs : a.length + b.length + 2 ≤ maxLongDigits) :
    kMul same a b = .ok (digitsOf (val a * val b)) :=
  kMulF_spec _ same a b (by omega) ha hb hsame hs

/-! ## `long_mul` -/

/-- `_PyLong_SameSign(a, b)`, pycore_long.h:283-287: the sign tags agree, so zero
differs from both signs. -/
def sameSign (a b : Long) : Bool :=
  (a.ds.isEmpty == b.ds.isEmpty) && (a.neg == b.neg)

/-- `long_mul(a, b)`, longobject.c:4343-4357. `same` is `a == b` on the two objects.
`_PyLong_Negate(&z)` (:355-368) is `Long.flip`: on the shared zero object it
rebuilds zero through `_PyLong_FromSTwoDigits`, which `flip` leaves unchanged. -/
def longMul (same : Bool) (a b : Long) : Py Long :=
  if bothCompact a b then do
    let v ← chkS64 (a.medium * b.medium)
    return fromSTwoDigits v
  else do
    let z ← kMul same a.ds b.ds
    let z : Long := ⟨false, z⟩
    return if !sameSign a b then z.flip else z

/-- The sign fix-up of `long_mul` gives the canonical object of the product. -/
theorem signed_product (a b : Int) :
    (if !sameSign (Long.ofInt a) (Long.ofInt b) then
        (⟨false, digitsOf (a.natAbs * b.natAbs)⟩ : Long).flip
      else ⟨false, digitsOf (a.natAbs * b.natAbs)⟩) = Long.ofInt (a * b) := by
  by_cases ha0 : a = 0
  · subst ha0
    simp [Long.flip, Long.ofInt]
  by_cases hb0 : b = 0
  · subst hb0
    simp [Long.flip, Long.ofInt]
  have na : digitsOf a.natAbs ≠ [] := by rw [Ne, digitsOf_eq_nil]; omega
  have nb : digitsOf b.natAbs ≠ [] := by rw [Ne, digitsOf_eq_nil]; omega
  have hpos : 0 < a.natAbs * b.natAbs := Nat.mul_pos (by omega) (by omega)
  have hne : digitsOf (a.natAbs * b.natAbs) ≠ [] := by rw [Ne, digitsOf_eq_nil]; omega
  have hab : (a * b).natAbs = a.natAbs * b.natAbs := Int.natAbs_mul a b
  have hss : sameSign (Long.ofInt a) (Long.ofInt b) = (decide (a < 0) == decide (b < 0)) := by
    have h1 : (digitsOf a.natAbs).isEmpty = false := by
      cases hh : digitsOf a.natAbs with
      | nil => exact absurd hh na
      | cons _ _ => rfl
    have h2 : (digitsOf b.natAbs).isEmpty = false := by
      cases hh : digitsOf b.natAbs with
      | nil => exact absurd hh nb
      | cons _ _ => rfl
    simp only [sameSign, Long.ofInt, h1, h2, beq_self_eq_true, Bool.true_and]
  rw [hss]
  rcases Int.lt_or_gt_of_ne ha0 with ha | ha <;> rcases Int.lt_or_gt_of_ne hb0 with hb | hb
  · have hc : 0 < a * b := Int.mul_pos_of_neg_of_neg ha hb
    have e : a * b = ((a.natAbs * b.natAbs : Nat) : Int) := by omega
    rw [e, Long.ofInt_natCast]
    simp [ha, hb]
  · have hc : a * b < 0 := Int.mul_neg_of_neg_of_pos ha hb
    have e : a * b = -((a.natAbs * b.natAbs : Nat) : Int) := by omega
    rw [e, Long.ofInt_neg_natCast hpos]
    have h1 : ¬ b < 0 := by omega
    simp [ha, h1, Long.flip, hne]
  · have hc : a * b < 0 := Int.mul_neg_of_pos_of_neg ha hb
    have e : a * b = -((a.natAbs * b.natAbs : Nat) : Int) := by omega
    rw [e, Long.ofInt_neg_natCast hpos]
    have h1 : ¬ a < 0 := by omega
    simp [hb, h1, Long.flip, hne]
  · have hc : 0 < a * b := Int.mul_pos ha hb
    have e : a * b = ((a.natAbs * b.natAbs : Nat) : Int) := by omega
    rw [e, Long.ofInt_natCast]
    have h1 : ¬ a < 0 := by omega
    have h2 : ¬ b < 0 := by omega
    simp [h1, h2]

/-- `int * int` returns the canonical object of the product, on the compact path
and the `k_mul` path, for `x * y` and for `x * x` on one object. The hypothesis
bounds the digit counts so that `long_alloc` cannot refuse a request. -/
theorem longMul_spec (same : Bool) (a b : Int) (hsame : same = true → a = b)
    (hs : digitCount a.natAbs + digitCount b.natAbs + 2 ≤ maxLongDigits) :
    longMul same (Long.ofInt a) (Long.ofInt b) = .ok (Long.ofInt (a * b)) := by
  unfold longMul
  by_cases hc : bothCompact (Long.ofInt a) (Long.ofInt b) = true
  · simp only [hc, ite_true]
    simp only [bothCompact, Long.isCompact_ofInt, Bool.and_eq_true] at hc
    have h1 := of_decide_eq_true hc.1
    have h2 := of_decide_eq_true hc.2
    have hm : (a * b).natAbs < 2 ^ 60 := by
      rw [Int.natAbs_mul]
      exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' h1 h2) (by decide)
    rw [Long.medium_ofInt h1, Long.medium_ofInt h2, chkS64_ok (by omega)]
    simp only [bind_ok, pure_ok]
    rw [fromSTwoDigits_eq (by omega) (by omega)]
  · simp only [hc, Bool.false_eq_true, ite_false]
    have hsm : same = true → (Long.ofInt a).ds = (Long.ofInt b).ds := by
      intro h
      rw [hsame h]
    have hk : kMul same (Long.ofInt a).ds (Long.ofInt b).ds =
        .ok (digitsOf (val (Long.ofInt a).ds * val (Long.ofInt b).ds)) :=
      kMul_spec (digitsOf_digits _) (digitsOf_digits _) hsm (by
        simp only [Long.ofInt, length_digitsOf]; omega)
    rw [hk]
    simp only [bind_ok, pure_ok]
    have e : val (Long.ofInt a).ds * val (Long.ofInt b).ds = a.natAbs * b.natAbs := by
      simp only [Long.ofInt, val_digitsOf]
    rw [e, signed_product]

end PyLean.LongObj
