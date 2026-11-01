import PyLean.LongObj.Bitwise
import PyLean.MathInt.Pow

/-!
`long_pow`, longobject.c:4994-5133: the small-exponent cases, left-to-right binary
exponentiation, and the sliding window. `MULT` is `mult`, on values, because
`long_mul` and `l_mod` are proven exact in `Karatsuba.lean` and `DivOps.lean`.

`MathInt.modPow` stood in for these loops. `longPowMod_eq` discharges that: the
mirrored loops give the same result as `MathInt.powMod` for all arguments.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt

/-- `EXP_TABLE_LEN`, longobject.c:92. -/
def expTableLen : Nat := 16
/-- `HUGE_EXP_CUTOFF / PyLong_SHIFT`, longobject.c:112, :5045. -/
def hugeDigits : Nat := 60 / 30

/-- `MULT(x, y, result)`, longobject.c:5014-5023: `x*y`, reduced when `c` is given. -/
def mult (c : Option Int) (x y : Int) : Int :=
  match c with
  | some m => (x * y) % m
  | none => x * y

/-- `MULT(z, z, z)` repeated `n` times. -/
def sqN (c : Option Int) : Nat → Int → Int
  | 0, z => z
  | n + 1, z => sqN c n (mult c z z)

/-! ## Binary -/

/-- The search for the first significant bit, longobject.c:5054-5061, on the bit
index: stops at the `k` with `2^(k+1) > bi`. -/
def firstBit (bi : Nat) : Nat → Nat → Nat
  | 0, k => k
  | f + 1, k => if 2 ^ (k + 1) > bi then k else firstBit bi f (k + 1)

/-- The loop `for (; bit != 0; bit >>= 1)`, longobject.c:5063-5068. `k` indexes
`bit = 1 << (k-1)`. -/
def binDigit (c : Option Int) (a : Int) (bi : Nat) : Nat → Int → Int
  | 0, z => z
  | k + 1, z =>
    let z := mult c z z
    let z := if bi &&& (1 <<< k) ≠ 0 then mult c z a else z
    binDigit c a bi k z

/-- The outer loop over the lower digits, longobject.c:5062-5074. -/
def binDigits (c : Option Int) (a : Int) : List Nat → Int → Int
  | [], z => z
  | d :: ds, z => binDigits c a ds (binDigit c a d 30 z)

/-! ## Sliding window -/

structure WinState where
  z : Int
  pending : Nat
  blen : Nat

/-- `while ((pending & 1) == 0) { ++ntz; pending >>= 1; }`, longobject.c:5101-5104. -/
def ntzLoop : Nat → Nat → Nat → Nat × Nat
  | 0, p, n => (p, n)
  | f + 1, p, n => if p &&& 1 = 0 then ntzLoop f (p >>> 1) (n + 1) else (p, n)

/-- `ABSORB_PENDING`, longobject.c:5096-5115. -/
def absorb (c : Option Int) (table : List Int) (st : WinState) : WinState :=
  let (p, ntz) := ntzLoop 6 st.pending 0
  let z := sqN c (st.blen - ntz) st.z
  let z := mult c z (table.getD (p >>> 1) 0)
  ⟨sqN c ntz z, 0, 0⟩

/-- One exponent bit, longobject.c:5120-5128. -/
def winBit (c : Option Int) (table : List Int) (st : WinState) (bit : Nat) : WinState :=
  let pending := (st.pending <<< 1) ||| bit
  if pending ≠ 0 then
    let blen := st.blen + 1
    if blen = 5 then absorb c table ⟨st.z, pending, blen⟩ else ⟨st.z, pending, blen⟩
  else ⟨mult c st.z st.z, pending, st.blen⟩

/-- `for (j = PyLong_SHIFT - 1; j >= 0; --j)`, longobject.c:5119-5129. -/
def winDigit (c : Option Int) (table : List Int) (bi : Nat) : Nat → WinState → WinState
  | 0, st => st
  | j + 1, st => winDigit c table bi j (winBit c table st ((bi >>> j) &&& 1))

/-- The digit loop of the window path, longobject.c:5117-5130. -/
def winDigits (c : Option Int) (table : List Int) : List Nat → WinState → WinState
  | [], st => st
  | d :: ds, st => winDigits c table ds (winDigit c table d 30 st)

/-- The table `table[i] == a**(2*i+1) % c`, longobject.c:5080-5088. -/
def tableGo (c : Option Int) (a2 : Int) : Nat → Int → List Int
  | 0, _ => []
  | n + 1, t => t :: tableGo c a2 n (mult c t a2)

/-- Lines 5024-5133 of `long_pow`; `e` holds the digits of the exponent. -/
def powLoop (a : Int) (e : List Nat) (c : Option Int) : Int :=
  let i := e.length
  let bi := e.getD (i - 1) 0
  if i ≤ 1 ∧ bi ≤ 3 then
    if bi ≥ 2 then
      let z := mult c a a
      if bi = 3 then mult c z a else z
    else if bi = 1 then mult c a 1
    else 1
  else if i ≤ hugeDigits then
    let k := firstBit bi 31 0
    binDigits c a (e.reverse.drop 1) (binDigit c a bi k a)
  else
    let table := tableGo c (mult c a a) expTableLen a
    let st := winDigits c table e.reverse ⟨1, 0, 0⟩
    if st.pending ≠ 0 then (absorb c table st).z else st.z

/-! ## Congruence bookkeeping -/

/-- `x` stands for `y`: equal, or equal modulo `c`. -/
def Cong (c : Option Int) (x y : Int) : Prop :=
  match c with
  | some m => x % m = y % m
  | none => x = y

/-- `x` is what a final result should look like for this modulus. -/
def Reduced (c : Option Int) (x : Int) : Prop :=
  match c with
  | some m => 0 ≤ x ∧ x < m
  | none => True

variable {c : Option Int} {a : Int}

theorem mult_cong {x y : Int} {E F : Nat} (h1 : Cong c x (a ^ E)) (h2 : Cong c y (a ^ F)) :
    Cong c (mult c x y) (a ^ (E + F)) := by
  cases c with
  | none =>
    simp only [Cong, mult] at *
    rw [h1, h2, Int.pow_add]
  | some m =>
    simp only [Cong, mult] at *
    rw [Int.emod_emod_of_dvd _ (Int.dvd_refl m), Int.mul_emod, h1, h2, ← Int.mul_emod, Int.pow_add]

theorem mult_reduced (hc : ∀ m, c = some m → 0 < m) (x y : Int) : Reduced c (mult c x y) := by
  cases c with
  | none => trivial
  | some m =>
    have hm := hc m rfl
    simp only [Reduced, mult]
    exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hm⟩

theorem sqN_cong : ∀ (n : Nat) (z : Int) (E : Nat), Cong c z (a ^ E) →
    Cong c (sqN c n z) (a ^ (E * 2 ^ n))
  | 0, z, E, h => by simpa [sqN] using h
  | n + 1, z, E, h => by
    have h1 : Cong c (mult c z z) (a ^ (E + E)) := mult_cong h h
    have := sqN_cong n _ _ h1
    simp only [sqN]
    rwa [show (E + E) * 2 ^ n = E * 2 ^ (n + 1) by rw [Nat.pow_succ]; grind] at this

theorem and_shift_ne (bi k : Nat) : bi &&& (1 <<< k) ≠ 0 ↔ bi.testBit k = true := by
  rw [Nat.one_shiftLeft]
  constructor
  · intro h
    rw [Nat.testBit_eq_decide_div_mod_eq]
    simp only [decide_eq_true_eq]
    refine Decidable.byContradiction fun hn => h ?_
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and, Nat.testBit_two_pow]
    by_cases hj : k = j
    · subst hj
      rw [Nat.testBit_eq_decide_div_mod_eq]
      simp [hn]
    · simp [hj]
  · intro h h0
    have h2 := congrArg (fun x => Nat.testBit x k) h0
    simp only [Nat.testBit_and, Nat.testBit_two_pow] at h2
    simp [h] at h2

/-- Splitting the low `k+1` bits. -/
theorem mod_two_pow_succ (bi k : Nat) :
    bi % 2 ^ (k + 1) = (if bi.testBit k = true then 2 ^ k else 0) + bi % 2 ^ k := by
  rw [Nat.mod_pow_succ, Nat.add_comm]
  congr 1
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : bi / 2 ^ k % 2 = 1
  · simp [h]
  · have : bi / 2 ^ k % 2 = 0 := by omega
    simp [this]

theorem binDigit_cong : ∀ (k : Nat) (z : Int) (E : Nat), Cong c z (a ^ E) →
    Cong c a (a ^ 1) → ∀ bi : Nat,
    Cong c (binDigit c a bi k z) (a ^ (E * 2 ^ k + bi % 2 ^ k))
  | 0, z, E, h, _, bi => by simpa [binDigit, Nat.mod_one] using h
  | k + 1, z, E, h, ha, bi => by
    have h1 : Cong c (mult c z z) (a ^ (E + E)) := mult_cong h h
    simp only [binDigit]
    by_cases ht : bi.testBit k = true
    · have hne : bi &&& (1 <<< k) ≠ 0 := (and_shift_ne bi k).2 ht
      simp only [hne, not_false_eq_true, ne_eq, ite_true]
      have h2 := mult_cong h1 ha
      have := binDigit_cong k _ _ h2 ha bi
      rw [show (E + E + 1) * 2 ^ k + bi % 2 ^ k = E * 2 ^ (k + 1) + bi % 2 ^ (k + 1) by
        rw [mod_two_pow_succ, if_pos ht, Nat.pow_succ]; grind] at this
      exact this
    · have hne : ¬ (bi &&& (1 <<< k) ≠ 0) := fun h => ht ((and_shift_ne bi k).1 h)
      simp only [hne, ite_false]
      have := binDigit_cong k _ _ h1 ha bi
      rw [show (E + E) * 2 ^ k + bi % 2 ^ k = E * 2 ^ (k + 1) + bi % 2 ^ (k + 1) by
        rw [mod_two_pow_succ, if_neg ht, Nat.pow_succ]; grind] at this
      exact this

theorem binDigit_reduced (hc : ∀ m, c = some m → 0 < m) (bi : Nat) :
    ∀ (k : Nat) (z : Int), 1 ≤ k → Reduced c (binDigit c a bi k z)
  | 0, _, h => by omega
  | 1, z, _ => by
    simp only [binDigit]
    split
    · exact mult_reduced hc _ _
    · exact mult_reduced hc _ _
  | k + 2, z, _ => by
    simp only [binDigit]
    exact binDigit_reduced hc bi (k + 1) _ (by omega)

/-- High-to-low digit folding: the exponent of a digit vector. -/
theorem fold_rev : ∀ (ds : List Nat) (E : Nat),
    ds.reverse.foldl (fun x d => x * 2 ^ 30 + d) E = E * 2 ^ (30 * ds.length) + val ds
  | [], E => by simp
  | d :: ds, E => by
    rw [List.reverse_cons, List.foldl_append, fold_rev ds E]
    simp only [List.foldl_cons, List.foldl_nil, val_cons, List.length_cons]
    rw [show 30 * (ds.length + 1) = 30 + 30 * ds.length by omega, Nat.pow_add]
    generalize 2 ^ (30 * ds.length) = P
    generalize (2 : Nat) ^ 30 = B
    grind

theorem binDigits_cong (ha : Cong c a (a ^ 1)) : ∀ (ds : List Nat) (z : Int) (E : Nat),
    IsDigits ds → Cong c z (a ^ E) →
    Cong c (binDigits c a ds z) (a ^ ds.foldl (fun x d => x * 2 ^ 30 + d) E)
  | [], _, _, _, h => h
  | d :: ds, z, E, hd, h => by
    have ⟨h1, h2⟩ := isDigits_cons.1 hd
    have := binDigit_cong 30 z E h ha d
    rw [Nat.mod_eq_of_lt h1] at this
    exact binDigits_cong ha ds _ _ h2 this

theorem binDigits_reduced (hc : ∀ m, c = some m → 0 < m) (ds : List Nat) (hne : ds ≠ []) (z : Int) :
    Reduced c (binDigits c a ds z) := by
  induction ds generalizing z with
  | nil => exact absurd rfl hne
  | cons d t ih =>
    cases t with
    | nil => exact binDigit_reduced hc d 30 z (by omega)
    | cons x y => exact ih (by simp) _

theorem firstBit_spec {bi : Nat} (h1 : 1 ≤ bi) :
    ∀ (f k : Nat), 2 ^ k ≤ bi → bi < 2 ^ (k + f) →
      2 ^ firstBit bi f k ≤ bi ∧ bi < 2 ^ (firstBit bi f k + 1)
  | 0, k, h2, h3 => by
    have : bi < 2 ^ k := by simpa using h3
    omega
  | 0 + 1, k, h2, h3 => by
    have : 2 ^ (k + 1) > bi := by simpa using h3
    simp only [firstBit, this, ite_true]
    exact ⟨h2, trivial⟩
  | f + 2, k, h2, h3 => by
    simp only [firstBit]
    split
    · rename_i hn
      exact ⟨h2, hn⟩
    · rename_i hn
      refine firstBit_spec h1 (f + 1) (k + 1) (by omega) ?_
      rw [show k + 1 + (f + 1) = k + (f + 2) by omega]
      exact h3

/-! ## Window invariants -/

theorem ntzLoop_spec : ∀ (f p n : Nat), 0 < p → p < 2 ^ f →
    (ntzLoop f p n).1 % 2 = 1 ∧ (ntzLoop f p n).1 * 2 ^ ((ntzLoop f p n).2 - n) = p ∧
      n ≤ (ntzLoop f p n).2 ∧ (ntzLoop f p n).1 ≤ p
  | 0, p, n, h1, h2 => by simp at h2; omega
  | f + 1, p, n, h1, h2 => by
    have h3 : p &&& 1 = p % 2 := Nat.and_two_pow_sub_one_eq_mod p 1
    simp only [ntzLoop, h3]
    by_cases hp : p % 2 = 0
    · simp only [hp, ite_true]
      have hs : p >>> 1 = p / 2 := by simp [Nat.shiftRight_eq_div_pow]
      rw [hs]
      obtain ⟨g1, g2, g3, g4⟩ := ntzLoop_spec f (p / 2) (n + 1) (by omega)
        (by rw [Nat.pow_succ] at h2; omega)
      generalize ntzLoop f (p / 2) (n + 1) = r at *
      obtain ⟨p', m⟩ := r
      simp only at g1 g2 g3 g4 ⊢
      refine ⟨g1, ?_, by omega, by omega⟩
      rw [show m - n = (m - (n + 1)) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc, g2]
      omega
    · simp only [hp, ite_false]
      exact ⟨by omega, by simp, Nat.le_refl _, Nat.le_refl _⟩

theorem tableGo_cong {a2 : Int} (ha2 : Cong c a2 (a ^ 2)) :
    ∀ (n : Nat) (t : Int) (E i : Nat), Cong c t (a ^ E) → i < n →
      Cong c ((tableGo c a2 n t).getD i 0) (a ^ (E + 2 * i))
  | 0, _, _, _, _, h => by omega
  | n + 1, t, E, 0, h1, _ => by simpa [tableGo] using h1
  | n + 1, t, E, i + 1, h1, h2 => by
    have h3 := tableGo_cong ha2 n (mult c t a2) (E + 2) i (mult_cong h1 ha2) (by omega)
    simp only [tableGo, List.getD_cons_succ]
    rwa [show E + 2 + 2 * i = E + 2 * (i + 1) by omega] at h3

/-- The window invariant: `z` holds `a**E` and the consumed exponent is `E`
followed by the `blen` pending bits. -/
def WinInv (c : Option Int) (a : Int) (st : WinState) (F : Nat) : Prop :=
  ∃ E, Cong c st.z (a ^ E) ∧ F = E * 2 ^ st.blen + st.pending ∧
    st.pending < 2 ^ st.blen ∧ st.blen ≤ 4 ∧ Reduced c st.z ∧ (st.pending = 0 → st.blen = 0)

theorem absorb_spec {table : List Int} {z : Int} {p b E : Nat} (hc : ∀ m, c = some m → 0 < m)
    (htab : ∀ i, i < 16 → Cong c (table.getD i 0) (a ^ (1 + 2 * i)))
    (hz : Cong c z (a ^ E)) (hzr : Reduced c z) (hb : b ≤ 5) (hp : p < 2 ^ b) (hp0 : 0 < p) :
    let st := absorb c table ⟨z, p, b⟩
    Cong c st.z (a ^ (E * 2 ^ b + p)) ∧ st.pending = 0 ∧ st.blen = 0 ∧ Reduced c st.z := by
  have hp32 : p < 2 ^ 6 := Nat.lt_of_lt_of_le hp (Nat.pow_le_pow_right (by decide) (by omega))
  obtain ⟨g1, g2, _, g4⟩ := ntzLoop_spec 6 p 0 hp0 hp32
  simp only [absorb]
  generalize ntzLoop 6 p 0 = r at *
  obtain ⟨q, ntz⟩ := r
  simp only [Nat.sub_zero] at g1 g2 g4 ⊢
  have hnb : ntz < b := by
    refine Nat.lt_of_not_le fun hle => ?_
    have h1 : 2 ^ b ≤ 2 ^ ntz := Nat.pow_le_pow_right (by decide) hle
    have h2 : 1 * 2 ^ ntz ≤ q * 2 ^ ntz := Nat.mul_le_mul_right _ (by omega)
    omega
  have hq : q >>> 1 = q / 2 := by simp [Nat.shiftRight_eq_div_pow]
  have hidx : q / 2 < 16 := by
    have : 2 ^ b ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) hb
    omega
  have ht := htab _ hidx
  have h1 := sqN_cong (b - ntz) z E hz
  have h2 := mult_cong h1 ht
  have h3 := sqN_cong ntz _ _ h2
  have hexp : (E * 2 ^ (b - ntz) + (1 + 2 * (q / 2))) * 2 ^ ntz = E * 2 ^ b + p := by
    rw [show 1 + 2 * (q / 2) = q by omega, Nat.add_mul, g2, Nat.mul_assoc, ← Nat.pow_add,
      show b - ntz + ntz = b by omega]
  rw [hexp] at h3
  rw [hq]
  refine ⟨h3, trivial, trivial, ?_⟩
  cases ntz with
  | zero => exact mult_reduced hc _ _
  | succ n =>
    have : ∀ (n : Nat) (w : Int), Reduced c (sqN c (n + 1) w) := by
      intro n
      induction n with
      | zero => intro w; exact mult_reduced hc _ _
      | succ n ih => intro w; exact ih _
    exact this n _

theorem winBit_inv {table : List Int} {st : WinState} {F bit : Nat}
    (hc : ∀ m, c = some m → 0 < m)
    (htab : ∀ i, i < 16 → Cong c (table.getD i 0) (a ^ (1 + 2 * i)))
    (h : WinInv c a st F) (hb : bit ≤ 1) :
    WinInv c a (winBit c table st bit) (F * 2 + bit) := by
  obtain ⟨E, hz, hF, hp, hl, hr, hzero⟩ := h
  have hb2 : bit < 2 ^ 1 := by omega
  have hor : (st.pending <<< 1) ||| bit = st.pending * 2 + bit := shl_or _ _ 1 hb2
  simp only [winBit, hor]
  by_cases h0 : st.pending * 2 + bit ≠ 0
  · simp only [h0, ne_eq, not_false_eq_true, ite_true]
    have hP : st.pending * 2 + bit < 2 ^ (st.blen + 1) := by
      rw [Nat.pow_succ]; omega
    by_cases h5 : st.blen + 1 = 5
    · simp only [h5, ite_true]
      rw [h5] at hP
      have hpos : 0 < st.pending * 2 + bit := by omega
      obtain ⟨a1, a2, a3, a4⟩ := absorb_spec (b := 5) hc htab hz hr (by omega) hP hpos
      refine ⟨E * 2 ^ 5 + (st.pending * 2 + bit), a1, ?_, ?_, ?_, a4, ?_⟩
      · have hb4 : st.blen = 4 := by omega
        rw [hb4] at hF
        rw [a2, a3]
        simp only [Nat.pow_zero, Nat.mul_one, Nat.add_zero]
        omega
      · rw [a2, a3]; decide
      · rw [a3]; omega
      · intro _; exact a3
    · simp only [h5, ite_false]
      refine ⟨E, hz, ?_, hP, by simp only; omega, hr, fun h => ?_⟩
      · show F * 2 + bit = E * 2 ^ (st.blen + 1) + (st.pending * 2 + bit)
        rw [hF, Nat.pow_succ]
        grind
      · simp only at h; omega
  · simp only [h0, ite_false]
    have hz0 : st.pending = 0 ∧ bit = 0 := by omega
    have hbl := hzero hz0.1
    refine ⟨E + E, mult_cong hz hz, ?_, ?_, hl, mult_reduced hc _ _, fun _ => hbl⟩
    · show F * 2 + bit = (E + E) * 2 ^ st.blen + (st.pending * 2 + bit)
      rw [hF, hz0.1, hz0.2, hbl]
      simp only [Nat.pow_zero, Nat.mul_one, Nat.add_zero]
      omega
    · show st.pending * 2 + bit < 2 ^ st.blen
      have := Nat.two_pow_pos st.blen
      omega

theorem shift_and_one (bi j : Nat) : (bi >>> j) &&& 1 = if bi.testBit j = true then 1 else 0 := by
  rw [Nat.and_two_pow_sub_one_eq_mod (bi >>> j) 1, Nat.shiftRight_eq_div_pow,
    Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : bi / 2 ^ j % 2 = 1
  · simp [h]
  · have : bi / 2 ^ j % 2 = 0 := by omega
    simp [this]

theorem winDigit_inv {table : List Int} (hc : ∀ m, c = some m → 0 < m)
    (htab : ∀ i, i < 16 → Cong c (table.getD i 0) (a ^ (1 + 2 * i))) (bi : Nat) :
    ∀ (j : Nat) (st : WinState) (F : Nat), WinInv c a st F →
      WinInv c a (winDigit c table bi j st) (F * 2 ^ j + bi % 2 ^ j)
  | 0, st, F, h => by simpa [winDigit, Nat.mod_one] using h
  | j + 1, st, F, h => by
    simp only [winDigit]
    rw [shift_and_one]
    have hbit : (if bi.testBit j = true then 1 else 0) ≤ 1 := by split <;> omega
    have h1 := winBit_inv (table := table) hc htab h hbit
    have := winDigit_inv hc htab bi j _ _ h1
    have e : (F * 2 + if bi.testBit j = true then 1 else 0) * 2 ^ j + bi % 2 ^ j =
        F * 2 ^ (j + 1) + bi % 2 ^ (j + 1) := by
      rw [mod_two_pow_succ, Nat.pow_succ]
      split <;> grind
    rw [e] at this
    exact this

theorem winDigits_inv {table : List Int} (hc : ∀ m, c = some m → 0 < m)
    (htab : ∀ i, i < 16 → Cong c (table.getD i 0) (a ^ (1 + 2 * i))) :
    ∀ (ds : List Nat) (st : WinState) (F : Nat), IsDigits ds → WinInv c a st F →
      WinInv c a (winDigits c table ds st) (ds.foldl (fun x d => x * 2 ^ 30 + d) F)
  | [], _, _, _, h => h
  | d :: ds, st, F, hd, h => by
    have ⟨h1, h2⟩ := isDigits_cons.1 hd
    have := winDigit_inv hc htab d 30 st F h
    rw [Nat.mod_eq_of_lt h1] at this
    exact winDigits_inv hc htab ds _ _ h2 this

/-! ## `powLoop` -/

theorem fold_val (ds : List Nat) : ds.reverse.foldl (fun x d => x * 2 ^ 30 + d) 0 = val ds := by
  rw [fold_rev]; simp

theorem cong_self (a : Int) : Cong c a (a ^ 1) := by
  have h : a ^ 1 = a := by rw [Int.pow_succ, Int.pow_zero, Int.one_mul]
  cases c with
  | none => simp only [Cong, h]
  | some m => simp only [Cong, h]

theorem cong_one (a : Int) : Cong c 1 (a ^ 0) := by
  cases c with
  | none => simp [Cong]
  | some m => simp [Cong]

theorem reduced_one (hc : ∀ m, c = some m → 2 ≤ m) : Reduced c 1 := by
  cases c with
  | none => trivial
  | some m =>
    have := hc m rfl
    simp only [Reduced]
    omega

/-- All three paths of `long_pow` compute `a**e`, reduced when a modulus is given. -/
theorem powLoop_spec (a : Int) (e : Nat) (hc : ∀ m, c = some m → 2 ≤ m) :
    Cong c (powLoop a (digitsOf e) c) (a ^ e) ∧ Reduced c (powLoop a (digitsOf e) c) := by
  have hc0 : ∀ m, c = some m → 0 < m := fun m h => by have := hc m h; omega
  have dd := digitsOf_digits e
  have vv := val_digitsOf e
  generalize hds : digitsOf e = ds at *
  unfold powLoop
  simp only
  by_cases hs : ds.length ≤ 1 ∧ ds.getD (ds.length - 1) 0 ≤ 3
  · rw [if_pos hs]
    have hbi : ds.getD (ds.length - 1) 0 = e := by
      match ds, hs, vv with
      | [], _, hv => simpa using hv
      | [d], _, hv => simpa using hv
      | _ :: _ :: _, hs, _ => simp at hs
    rw [hbi]
    rw [hbi] at hs
    have hca := cong_self (c := c) a
    by_cases h2 : e ≥ 2
    · rw [if_pos h2]
      have h1 := mult_cong hca hca
      by_cases h3 : e = 3
      · subst h3
        simp only [ite_true]
        exact ⟨mult_cong h1 hca, mult_reduced hc0 _ _⟩
      · rw [if_neg h3]
        have : e = 2 := by omega
        subst this
        exact ⟨h1, mult_reduced hc0 _ _⟩
    · rw [if_neg h2]
      by_cases h1 : e = 1
      · subst h1
        simp only [ite_true]
        exact ⟨mult_cong hca (cong_one a), mult_reduced hc0 _ _⟩
      · rw [if_neg h1]
        have : e = 0 := by omega
        subst this
        exact ⟨cong_one a, reduced_one hc⟩
  · rw [if_neg hs]
    have hne : ds ≠ [] := by
      intro h
      subst h
      simp at hs
    obtain ⟨l, top, hl⟩ : ∃ l t, ds = l ++ [t] :=
      ⟨ds.dropLast, ds.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    have htop : ds.getD (ds.length - 1) 0 = top := by subst hl; simp [List.getD]
    have hrev : ds.reverse = top :: l.reverse := by subst hl; simp
    have hs' : ¬ (ds.length ≤ 1 ∧ top ≤ 3) := by rw [htop] at hs; exact hs
    have htopd : top < 2 ^ 30 := (isDigits_cons.1 (isDigits_append.1 (hl ▸ dd)).2).1
    have htop0 : top ≠ 0 := by
      have hN := normal_digitsOf e
      rw [hds] at hN
      have := hN hne
      simpa [hl] using this
    by_cases hb : ds.length ≤ hugeDigits
    · rw [if_pos hb, htop, hrev]
      simp only [List.drop_succ_cons, List.drop_zero]
      obtain ⟨f1, f2⟩ := firstBit_spec (bi := top) (by omega) 31 0 (by simpa using (by omega : 1 ≤ top))
        (by simp only [Nat.zero_add]; omega)
      generalize firstBit top 31 0 = k at *
      have hmod : 1 * 2 ^ k + top % 2 ^ k = top := by
        have hd := Nat.div_add_mod top (2 ^ k)
        have hq : top / 2 ^ k = 1 := by
          apply Nat.div_eq_of_lt_le
          · simpa using f1
          · rw [Nat.pow_succ] at f2; omega
        rw [hq] at hd
        omega
      have hz0 := binDigit_cong (c := c) k a 1 (by simpa using cong_self (c := c) a) (cong_self a) top
      rw [hmod] at hz0
      have hdl : IsDigits l.reverse := by
        intro x hx
        exact (isDigits_append.1 (hl ▸ dd)).1 x (List.mem_reverse.1 hx)
      have hfin := binDigits_cong (cong_self (a := a) (c := c)) l.reverse _ _ hdl hz0
      have hexp : l.reverse.foldl (fun x d => x * 2 ^ 30 + d) top = e := by
        have h1 := fold_rev l top
        have h2 : ds.reverse.foldl (fun x d => x * 2 ^ 30 + d) 0 = val ds := fold_val ds
        rw [hrev] at h2
        simp only [List.foldl_cons, Nat.zero_mul, Nat.zero_add] at h2
        rw [h2, vv]
      rw [hexp] at hfin
      refine ⟨hfin, ?_⟩
      by_cases hl0 : l.reverse = []
      · rw [hl0]
        simp only [binDigits]
        have hl1 : l = [] := by simpa using hl0
        subst hl1
        have hk : 1 ≤ k := by
          rcases Nat.eq_zero_or_pos k with h | h
          · subst h
            have hlen : ds.length = 1 := by rw [hl]; simp
            have h3 : top < 2 := by simpa using f2
            exact absurd ⟨by omega, by omega⟩ hs'
          · exact h
        exact binDigit_reduced hc0 top k a hk
      · exact binDigits_reduced hc0 _ hl0 _
    · rw [if_neg hb]
      have ha2 := mult_cong (cong_self (c := c) a) (cong_self a)
      have htab : ∀ i, i < 16 → Cong c ((tableGo c (mult c a a) expTableLen a).getD i 0)
          (a ^ (1 + 2 * i)) := fun i hi =>
        tableGo_cong ha2 _ _ _ _ (cong_self a) hi
      have hinit : WinInv c a ⟨1, 0, 0⟩ 0 :=
        ⟨0, cong_one a, by simp, by simp, by simp, reduced_one hc, fun _ => rfl⟩
      have hdr : IsDigits ds.reverse := by
        intro x hx
        exact dd x (List.mem_reverse.1 hx)
      obtain ⟨E, h1, h2, h3, h4, h5, h6⟩ := winDigits_inv hc0 htab ds.reverse _ _ hdr hinit
      rw [fold_val, vv] at h2
      generalize winDigits c (tableGo c (mult c a a) expTableLen a) ds.reverse ⟨1, 0, 0⟩ = st at *
      by_cases hp : st.pending ≠ 0
      · rw [if_pos hp]
        obtain ⟨a1, _, _, a4⟩ := absorb_spec (b := st.blen) hc0 htab h1 h5 (by omega) h3 (by omega)
        rw [← h2] at a1
        exact ⟨a1, a4⟩
      · rw [if_neg hp]
        have hp0 : st.pending = 0 := by omega
        have hb0 := h6 hp0
        rw [hb0, hp0] at h2
        simp only [Nat.pow_zero, Nat.mul_one, Nat.add_zero] at h2
        rw [h2]
        exact ⟨h1, h5⟩

/-- `long_pow` with no modulus computes the exact power. -/
theorem powLoop_none (a : Int) (e : Nat) : powLoop a (digitsOf e) none = a ^ e :=
  (powLoop_spec (c := none) a e (by simp)).1

/-- `long_pow` with a modulus `m >= 2` computes `a**e % m` for every `a`. -/
theorem powLoop_some (a : Int) (e : Nat) {m : Int} (hm : 2 ≤ m) :
    powLoop a (digitsOf e) (some m) = a ^ e % m := by
  obtain ⟨h1, h2, h3⟩ := powLoop_spec (c := some m) a e (by
    intro k hk
    simp only [Option.some.injEq] at hk
    omega)
  simp only [Cong] at h1
  rw [← h1, Int.emod_eq_of_lt h2 h3]

/-! ## `long_pow` -/

/-- `pow(v, w, x)` for ints with `x` given, longobject.c:4878-5157, with the result
of the exponentiation loops supplied by `k`. -/
def powModWith (k : Int → Int → Int → Int) (v w x : Int) : Py Int := do
  if x = 0 then throw (.valueError "pow() 3rd argument cannot be 0")
  let negativeOutput := x < 0
  let c : Int := x.natAbs
  if c = 1 then return 0
  let mut a := v
  let mut b := w
  if b < 0 then
    b := -b
    a ← invmod a c
  if a < 0 ∨ digitCount a.natAbs > digitCount c.natAbs then
    a := floorMod a c
  let z : Int := k a b c
  if negativeOutput ∧ z ≠ 0 then return z - c
  return z

/-- The mirrored `long_pow`. -/
def longPowMod (v w x : Int) : Py Int :=
  powModWith (fun a b c => powLoop a (digitsOf b.toNat) (some c)) v w x

/-- `v ** w` with no modulus, longobject.c:4914-4922, :5024-5133. A negative exponent
leaves `long_pow` for `float_pow`, outside the integer model. -/
def longPowNone (v w : Int) : Option Int :=
  if w < 0 then none else some (powLoop v (digitsOf w.toNat) none)

theorem floorMod_nonneg (a c : Int) (hc : 2 ≤ c) : 0 ≤ floorMod a c := by
  simp only [floorMod]
  rw [Int.fmod_eq_emod_of_nonneg _ (by omega)]
  exact Int.emod_nonneg _ (by omega)

/-- The base after the reduction at longobject.c:4983-4988 is non-negative. -/
theorem reduced_base_nonneg (a c : Int) (hc : 2 ≤ c) :
    0 ≤ (if a < 0 ∨ digitCount a.natAbs > digitCount c.natAbs then floorMod a c else a) := by
  by_cases h1 : a < 0 ∨ digitCount a.natAbs > digitCount c.natAbs
  · rw [if_pos h1]; exact floorMod_nonneg a c hc
  · rw [if_neg h1]; omega

theorem powModWith_congr {k1 k2 : Int → Int → Int → Int}
    (h : ∀ a b c, 0 ≤ a → 2 ≤ c → k1 a b c = k2 a b c) (v w x : Int) :
    powModWith k1 v w x = powModWith k2 v w x := by
  unfold powModWith
  by_cases hx : x = 0
  · subst hx; rfl
  by_cases h1 : (x.natAbs : Int) = 1
  · simp only [hx, h1, ite_false, ite_true]
  have hc2 : 2 ≤ (x.natAbs : Int) := by omega
  simp only [hx, h1, ite_false]
  by_cases hw : w < 0
  · rw [if_pos hw, if_pos hw]
    cases hi : invmod v x.natAbs with
    | error e => rfl
    | ok b =>
      simp only [bind_ok]
      by_cases hr : b < 0 ∨ digitCount b.natAbs > digitCount (x.natAbs : Int).natAbs
      · rw [if_pos hr, if_pos hr, h _ _ _ (floorMod_nonneg b _ hc2) hc2]
      · rw [if_neg hr, if_neg hr, h _ _ _ (by omega) hc2]
  · rw [if_neg hw, if_neg hw]
    by_cases hr : v < 0 ∨ digitCount v.natAbs > digitCount (x.natAbs : Int).natAbs
    · rw [if_pos hr, if_pos hr, h _ _ _ (floorMod_nonneg v _ hc2) hc2]
    · rw [if_neg hr, if_neg hr, h _ _ _ (by omega) hc2]

/-- The mirrored loops of `long_pow` agree with `MathInt.powMod` for all arguments,
which discharges its assumption that they compute `a**e % c`. -/
theorem longPowMod_eq (v w x : Int) : longPowMod v w x = powMod v w x := by
  have hrfl : powMod v w x =
      powModWith (fun a b c => ((modPow a.toNat b.toNat c.toNat : Nat) : Int)) v w x := rfl
  rw [hrfl]
  unfold longPowMod
  apply powModWith_congr
  intro a b c ha hc
  show powLoop a (digitsOf b.toNat) (some c) = ((modPow a.toNat b.toNat c.toNat : Nat) : Int)
  rw [powLoop_some _ _ hc, modPow_eq _ _ _ (by omega), Int.natCast_emod, Int.natCast_pow,
    Int.toNat_of_nonneg ha, Int.toNat_of_nonneg (by omega)]

/-- `a ** b` for `b >= 0` is the exact power on all three paths of `long_pow`. -/
theorem longPowNone_spec (v w : Int) (hw : 0 ≤ w) : longPowNone v w = some (v ^ w.toNat) := by
  simp only [longPowNone]
  rw [if_neg (by omega), powLoop_none]

/-- `pow(v, w, x)` for `w >= 0`, `x != 0` is the Python remainder of `v**w` by `x`. -/
theorem longPowMod_floor (v w x : Int) (hw : 0 ≤ w) (hx : x ≠ 0) :
    ∃ q r, longPowMod v w x = .ok r ∧ IsFloorDivmod (v ^ w.toNat) x q r := by
  have hw' : ¬ w < 0 := by omega
  by_cases h1 : (x.natAbs : Int) = 1
  · refine ⟨v ^ w.toNat * x, 0, ?_, ?_⟩
    · simp only [longPowMod, powModWith, hx, h1, ite_false, ite_true]
      rfl
    · have hsq : x * x = 1 := by
        have : x = 1 ∨ x = -1 := by omega
        rcases this with h | h <;> subst h <;> rfl
      refine ⟨?_, fun h => ?_, fun h => ?_⟩
      · rw [Int.add_zero, Int.mul_assoc, hsq, Int.mul_one]
      · omega
      · omega
  · have hc2 : 2 ≤ (x.natAbs : Int) := by omega
    generalize hc : (x.natAbs : Int) = c at *
    have hbase : ∀ a : Int, a % c = v % c → powLoop a (digitsOf w.toNat) (some c) = v ^ w.toNat % c := by
      intro a ha
      rw [powLoop_some _ _ hc2]
      have hpow : ∀ n : Nat, a ^ n % c = v ^ n % c := by
        intro n
        induction n with
        | zero => rw [Int.pow_zero, Int.pow_zero]
        | succ n ih =>
          rw [Int.pow_succ, Int.pow_succ, Int.mul_emod, ih, ha, ← Int.mul_emod]
      exact hpow _
    obtain ⟨Z, hZ⟩ : ∃ z, z = v ^ w.toNat % c := ⟨_, rfl⟩
    have hz1 : 0 ≤ Z := by rw [hZ]; exact Int.emod_nonneg _ (by omega)
    have hz2 : Z < c := by rw [hZ]; exact Int.emod_lt_of_pos _ (by omega)
    have hzq : v ^ w.toNat = c * (v ^ w.toNat / c) + Z := by
      rw [hZ]; exact (Int.mul_ediv_add_emod _ _).symm
    generalize hQ : v ^ w.toNat / c = Q at hzq
    generalize hV : v ^ w.toNat = V at *
    have hres : longPowMod v w x = .ok (if x < 0 ∧ Z ≠ 0 then Z - c else Z) := by
      simp only [longPowMod, powModWith, hx, hc, ite_false]
      have hc1 : ¬ c = 1 := by omega
      rw [if_neg hc1, if_neg hw']
      by_cases hr : v < 0 ∨ digitCount v.natAbs > digitCount c.natAbs
      · rw [if_pos hr, hbase _ (by
          simp only [floorMod]
          rw [Int.fmod_eq_emod_of_nonneg _ (by omega), Int.emod_emod_of_dvd _ (Int.dvd_refl c)]),
          ← hZ]
        split <;> rfl
      · rw [if_neg hr, hbase _ rfl, ← hZ]
        split <;> rfl
    by_cases hneg : x < 0
    · have hxc : c = -x := by omega
      by_cases hz0 : Z = 0
      · refine ⟨-Q, 0, by simpa [hneg, hz0] using hres, ?_⟩
        refine ⟨?_, fun h => by omega, fun h => ⟨by omega, by omega⟩⟩
        rw [hzq, hz0, hxc]
        grind
      · refine ⟨-(Q + 1), Z - c, by simpa [hneg, hz0] using hres, ?_⟩
        refine ⟨?_, fun h => by omega, fun h => ⟨by omega, by omega⟩⟩
        rw [hzq, hxc]
        grind
    · have hxc : c = x := by omega
      refine ⟨Q, Z, by simpa [hneg] using hres, ?_⟩
      refine ⟨?_, fun h => ⟨hz1, by omega⟩, fun h => by omega⟩
      rw [hzq, hxc]
      grind

end PyLean.LongObj
