import PyLean.MathInt.FromBytes

/-!
The digit loop of `_PyLong_AsByteArray` (longobject.c:1155-1191) in closed
form: it emits the low bytes of the (two's-complemented) digit value, and
fails exactly when more than `n` whole bytes are produced.
-/

namespace PyLean.MathInt

open PyLean

/-- The `k` low bytes of `x`, least significant first. -/
def lowBytes (x : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => x % 256 :: lowBytes (x / 256) k

theorem lowBytes_length (x k : Nat) : (lowBytes x k).length = k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp [lowBytes, ih]

theorem lowBytes_all (x k : Nat) : AllBytes (lowBytes x k) := by
  induction k generalizing x with
  | zero => intro b hb; simp [lowBytes] at hb
  | succ k ih =>
    intro b hb
    simp only [lowBytes, List.mem_cons] at hb
    rcases hb with h | h
    · subst h; exact Nat.mod_lt _ (by decide)
    · exact ih _ b h

theorem bytesVal_lowBytes (x k : Nat) : bytesVal (lowBytes x k) = x % 256 ^ k := by
  induction k generalizing x with
  | zero => simp [lowBytes, bytesVal, Nat.mod_one]
  | succ k ih =>
    simp only [lowBytes, bytesVal, ih, Nat.pow_succ]
    rw [Nat.mul_comm (256 ^ k) 256, Nat.mod_mul, Nat.add_comm]

theorem lowBytes_add (x a b : Nat) :
    lowBytes x (a + b) = lowBytes x a ++ lowBytes (x / 256 ^ a) b := by
  induction a generalizing x with
  | zero => simp [lowBytes]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [lowBytes, ih, List.cons_append, Nat.pow_succ, Nat.div_div_eq_div_mul,
      Nat.mul_comm (256 ^ a) 256]

theorem lowBytes_mod (x y k : Nat) (h : x % 256 ^ k = y % 256 ^ k) : lowBytes x k = lowBytes y k := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih =>
    simp only [lowBytes]
    have h1 : x % 256 = y % 256 := by
      have := congrArg (· % 256) h
      simp only [Nat.pow_succ, Nat.mod_mod_of_dvd _ (Nat.dvd_mul_left 256 _)] at this
      exact this
    have h2 : (x / 256) % 256 ^ k = (y / 256) % 256 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm] at h
      rw [Nat.mod_mul] at h; rw [Nat.mod_mul] at h
      have : 256 * ((x / 256) % 256 ^ k) = 256 * ((y / 256) % 256 ^ k) := by omega
      exact Nat.eq_of_mul_eq_mul_left (by decide) this
    rw [h1, ih _ _ h2]

/-- `storeBytes`, longobject.c:1181-1190: emit `accumbits / 8` low bytes unless
that would exceed `n` bytes. -/
theorem storeBytes_spec (n : Nat) : ∀ fuel (st : ABState), st.accumbits < 8 * fuel + 8 →
    st.out.length ≤ n →
    storeBytes n fuel st =
      if st.out.length + st.accumbits / 8 > n then none
      else some ⟨st.out ++ lowBytes st.accum (st.accumbits / 8),
        st.accum / 256 ^ (st.accumbits / 8), st.accumbits % 8, st.carry⟩ := by
  intro fuel
  induction fuel with
  | zero =>
    intro st h hn
    have : st.accumbits / 8 = 0 := by omega
    simp only [storeBytes, this, Nat.add_zero, show ¬ (st.out.length > n) by omega, ite_false,
      lowBytes, List.append_nil, Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt (show st.accumbits < 8 by omega)]
  | succ f ih =>
    intro st h hn
    unfold storeBytes
    by_cases h8 : st.accumbits ≥ 8
    · simp only [h8, ite_true]
      by_cases hfull : st.out.length ≥ n
      · simp only [hfull, ite_true]
        rw [if_pos (by omega)]
      · simp only [hfull, ite_false]
        rw [ih _ (by simp; omega) (by simp; omega)]
        simp only [List.length_append, List.length_singleton]
        have hk : (st.accumbits - 8) / 8 = st.accumbits / 8 - 1 := by omega
        rw [hk]
        by_cases hc : st.out.length + 1 + (st.accumbits / 8 - 1) > n
        · rw [if_pos hc, if_pos (by omega)]
        · rw [if_neg hc, if_neg (by omega)]
          have e1 : st.accumbits / 8 = 1 + (st.accumbits / 8 - 1) := by omega
          congr 1
          congr 1
          · rw [List.append_assoc, e1, lowBytes_add]
            simp [lowBytes, Nat.pow_one]
          · rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']
            rw [Nat.succ_eq_add_one, show st.accumbits / 8 - 1 + 1 = st.accumbits / 8 by omega]
          · omega
    · simp only [h8, ite_false]
      have : st.accumbits / 8 = 0 := by omega
      rw [this, if_neg (by omega)]
      simp [lowBytes, Nat.mod_eq_of_lt (show st.accumbits < 8 by omega)]

/-! ### The effective digits -/

/-- The per-digit two's-complement transform of longobject.c:1158-1162. -/
def effStep (twos : Bool) (d c : Nat) : Nat × Nat :=
  if twos then (((d ^^^ digitMask) + c) &&& digitMask, ((d ^^^ digitMask) + c) >>> 30) else (d, c)

/-- Value of the effective digits. -/
def effVal (twos : Bool) : List Nat → Nat → Nat
  | [], _ => 0
  | d :: ds, c => (effStep twos d c).1 + 2 ^ 30 * effVal twos ds (effStep twos d c).2

/-- Final carry. -/
def effCarry (twos : Bool) : List Nat → Nat → Nat
  | [], c => c
  | d :: ds, c => effCarry twos ds (effStep twos d c).2

/-- Bits counted: 30 per digit, and the significant bits of the last
(complemented, for negative numbers) digit, longobject.c:1168-1180. -/
def effBits (twos : Bool) : List Nat → Nat → Nat
  | [], _ => 0
  | [d], c => bitLength (if twos then (effStep twos d c).1 ^^^ digitMask else (effStep twos d c).1)
  | d :: ds, c => 30 + effBits twos ds (effStep twos d c).2

theorem effStep_lt (twos : Bool) (d c : Nat) (hd : d < 2 ^ 30) (hc : c ≤ 1) :
    (effStep twos d c).1 < 2 ^ 30 ∧ (effStep twos d c).2 ≤ 1 := by
  unfold effStep
  cases twos with
  | false => simp [hd, hc]
  | true =>
    simp only [ite_true]
    unfold digitMask
    rw [and_mask_eq_mod, Nat.shiftRight_eq_div_pow, Nat.xor_comm, xor_mask 30 d hd]
    refine ⟨Nat.mod_lt _ (by decide), ?_⟩
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul (by decide)).mpr; omega

/-- The digit loop in closed form. -/
theorem asByteArrayLoop_spec (n : Nat) (twos : Bool) : ∀ (ds : List Nat) (st : ABState),
    (∀ d ∈ ds, d < 2 ^ 30) → st.carry ≤ 1 → st.accum < 2 ^ st.accumbits → st.accumbits < 8 →
    st.out.length ≤ n →
    let tot := st.accum + 2 ^ st.accumbits * effVal twos ds st.carry
    let L := st.accumbits + effBits twos ds st.carry
    asByteArrayLoop n twos ds st =
      if st.out.length + L / 8 > n then none
      else some ⟨st.out ++ lowBytes tot (L / 8), tot / 256 ^ (L / 8), L % 8,
        effCarry twos ds st.carry⟩ := by
  intro ds
  induction ds with
  | nil =>
    intro st _ _ ha hb hn
    simp only [asByteArrayLoop, effVal, effBits, effCarry, Nat.mul_zero, Nat.add_zero]
    have h0 : st.accumbits / 8 = 0 := by omega
    obtain ⟨o, a, ab, c⟩ := st
    simp only at h0 hb hn ⊢
    simp [h0, lowBytes, Nat.mod_eq_of_lt hb, show ¬ (o.length > n) by omega]
  | cons d ds ih =>
    intro st hall hc ha hb hn
    have hd := hall d (by simp)
    have hrest : ∀ x ∈ ds, x < 2 ^ 30 := fun x hx => hall x (by simp [hx])
    obtain ⟨he, hc'⟩ := effStep_lt twos d st.carry hd hc
    generalize hE : effStep twos d st.carry = E at he hc'
    obtain ⟨e, c'⟩ := E
    simp only at he hc'
    have hstep : (if twos then
        (((d ^^^ digitMask) + st.carry) &&& digitMask, ((d ^^^ digitMask) + st.carry) >>> 30)
        else (d, st.carry)) = (e, c') := by rw [← hE]; rfl
    simp only [asByteArrayLoop, hstep]
    have hor : st.accum ||| (e <<< st.accumbits) = st.accum + e * 2 ^ st.accumbits :=
      or_shift_eq_add _ _ _ ha
    rw [hor]
    have hval : effVal twos (d :: ds) st.carry = e + 2 ^ 30 * effVal twos ds c' := by
      simp only [effVal, hE]
    have hcar : effCarry twos (d :: ds) st.carry = effCarry twos ds c' := by
      simp only [effCarry, hE]
    rw [hval, hcar]
    have hacc : st.accum + e * 2 ^ st.accumbits < 2 ^ (st.accumbits + 30) := by
      rw [Nat.pow_add, Nat.mul_comm (2 ^ st.accumbits)]
      have : e * 2 ^ st.accumbits + 2 ^ st.accumbits ≤ 2 ^ 30 * 2 ^ st.accumbits := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ he
      omega
    cases ds with
    | nil =>
      have hbits : effBits twos [d] st.carry =
          bitLength (if twos = true then e ^^^ digitMask else e) := by
        simp only [effBits, hE]
      rw [hbits]
      simp only [ite_true, effVal, effCarry, Nat.mul_zero, Nat.add_zero]
      generalize bitLength (if twos = true then e ^^^ digitMask else e) = bl
      rw [storeBytes_spec n _ ⟨st.out, st.accum + e * 2 ^ st.accumbits, st.accumbits + bl, c'⟩
        (by first | omega | (simp; omega) | simp) hn]
      simp only
      by_cases hov : st.out.length + (st.accumbits + bl) / 8 > n
      · simp only [hov, ite_true]
      · simp only [hov, ite_false, asByteArrayLoop, Nat.mul_comm e]
    | cons d2 ds2 =>
      have hbits : effBits twos (d :: d2 :: ds2) st.carry = 30 + effBits twos (d2 :: ds2) c' := by
        simp only [effBits, hE]
      rw [hbits]
      simp only [reduceCtorEq, ite_false]
      rw [storeBytes_spec n _ ⟨st.out, st.accum + e * 2 ^ st.accumbits, st.accumbits + 30, c'⟩
        (by first | omega | (simp; omega) | simp) hn]
      simp only
      generalize hk : (st.accumbits + 30) / 8 = k
      generalize hab2 : (st.accumbits + 30) % 8 = ab2
      have hsplit : st.accumbits + 30 = 8 * k + ab2 := by omega
      generalize hR : effVal twos (d2 :: ds2) c' = R
      generalize hB : effBits twos (d2 :: ds2) c' = B
      generalize hacc' : st.accum + e * 2 ^ st.accumbits = acc at hacc
      have hpk : 2 ^ (st.accumbits + 30) = 256 ^ k * 2 ^ ab2 := by
        rw [hsplit, Nat.pow_add, Nat.pow_mul]
      have htot : st.accum + 2 ^ st.accumbits * (e + 2 ^ 30 * R) = acc + 256 ^ k * (2 ^ ab2 * R) := by
        rw [← hacc', ← Nat.mul_assoc, ← hpk, Nat.pow_add]
        grind
      rw [htot]
      by_cases hov : st.out.length + k > n
      · rw [if_pos hov, if_pos (by omega)]
      · rw [if_neg hov]
        simp only
        have hlt2 : acc / 256 ^ k < 2 ^ ab2 := by
          apply (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).mpr
          rw [Nat.mul_comm, ← hpk]; exact hacc
        have ih' := ih ⟨st.out ++ lowBytes acc k, acc / 256 ^ k, ab2, c'⟩ hrest hc' hlt2
          (by show ab2 < 8; omega) (by simp [lowBytes_length]; omega)
        simp only [hR, hB] at ih'
        rw [ih']
        simp only [List.length_append, lowBytes_length]
        have hL : (st.accumbits + (30 + B)) / 8 = k + (ab2 + B) / 8 := by omega
        rw [hL]
        by_cases hov2 : st.out.length + k + (ab2 + B) / 8 > n
        · rw [if_pos hov2, if_pos (by omega)]
        · rw [if_neg hov2, if_neg (by omega)]
          have hdiv : (acc + 256 ^ k * (2 ^ ab2 * R)) / 256 ^ k = acc / 256 ^ k + 2 ^ ab2 * R :=
            Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide))
          have hmod : (acc + 256 ^ k * (2 ^ ab2 * R)) % 256 ^ k = acc % 256 ^ k := by
            rw [Nat.add_mul_mod_self_left]
          have f1 : st.out ++ lowBytes acc k ++ lowBytes (acc / 256 ^ k + 2 ^ ab2 * R) ((ab2 + B) / 8) =
              st.out ++ lowBytes (acc + 256 ^ k * (2 ^ ab2 * R)) (k + (ab2 + B) / 8) := by
            rw [lowBytes_add, lowBytes_mod _ acc k hmod, hdiv, List.append_assoc]
          have f2 : (acc / 256 ^ k + 2 ^ ab2 * R) / 256 ^ ((ab2 + B) / 8) =
              (acc + 256 ^ k * (2 ^ ab2 * R)) / 256 ^ (k + (ab2 + B) / 8) := by
            rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, hdiv]
          have f3 : (ab2 + B) % 8 = (st.accumbits + (30 + B)) % 8 := by omega
          rw [f1, f2, f3]

end PyLean.MathInt
