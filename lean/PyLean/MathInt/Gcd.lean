import PyLean.MathInt.Model
import PyLean.MathInt.Factorial

/-!
`math.gcd` / `math.lcm` on arguments below `2**60`, where `_PyLong_GCD`
takes its `simple:` path (Euclid on C `long`s, longobject.c:5911-5942).
The general statements `GcdGeneral` / `LcmGeneral`, which go through Lehmer's
step, are proven in `Lehmer.lean`.
-/

namespace PyLean.MathInt

open PyLean

theorem euclid_eq : ∀ fuel x y, y < fuel → euclid fuel x y = Nat.gcd x y := by
  intro fuel
  induction fuel with
  | zero => intro x y h; omega
  | succ f ih =>
    intro x y h
    unfold euclid
    by_cases hy : y = 0
    · subst hy; simp
    · simp only [hy, ne_eq, not_false_eq_true, ite_true]
      rw [ih y (x % y) (Nat.lt_of_lt_of_le (Nat.mod_lt x (by omega)) (by omega))]
      rw [Nat.gcd_comm y (x % y), ← Nat.gcd_rec, Nat.gcd_comm]

theorem gcdSimple_eq (a b : Int) : gcdSimple a b = Int.gcd a b := by
  unfold gcdSimple; rw [euclid_eq _ _ _ (by omega)]; rfl

theorem digitCount_le_two (n : Nat) (h : n < 2 ^ 60) : digitCount n ≤ 2 := by
  unfold digitCount
  have := bitLength_le_of_lt' h
  omega

/-- `_PyLong_GCD(a, b)` when both fit in two digits. -/
theorem pyLongGCD_small (a b : Int) (ha : a.natAbs < 2 ^ 60) (hb : b.natAbs < 2 ^ 60) :
    pyLongGCD a b = .ok (Int.gcd a b) := by
  unfold pyLongGCD
  rw [if_pos ⟨digitCount_le_two _ ha, digitCount_le_two _ hb⟩, gcdSimple_eq]

/-- `gcd` of a list of ints, as the docs define it: `gcd()` is 0. -/
def listGcd (xs : List Int) : Nat := xs.foldl (fun g a => Nat.gcd g a.natAbs) 0

theorem foldl_gcd_one : ∀ xs : List Int, xs.foldl (fun g a => Nat.gcd g a.natAbs) 1 = 1
  | [] => rfl
  | x :: xs => by simp only [List.foldl, Nat.gcd_one_left]; exact foldl_gcd_one xs

theorem foldl_gcd_le : ∀ (xs : List Int) (g : Nat), 0 < g →
    xs.foldl (fun g a => Nat.gcd g a.natAbs) g ≤ g
  | [], _, _ => Nat.le_refl _
  | x :: xs, g, hg => by
    simp only [List.foldl]
    have h1 := Nat.gcd_le_left x.natAbs hg
    have h2 := foldl_gcd_le xs (Nat.gcd g x.natAbs) (Nat.gcd_pos_of_pos_left _ hg)
    omega

theorem gcd_lt_of (r x M : Nat) (hr : r < M) (hx : x < M) : Nat.gcd r x < M := by
  rcases Nat.eq_zero_or_pos x with h | h
  · rw [h, Nat.gcd_zero_right]; exact hr
  · exact Nat.lt_of_le_of_lt (Nat.gcd_le_right _ h) hx

/-- The loop of `math_gcd_impl` (mathmodule.c@3.14.7:742-758) from a nonnegative
running value `res`. -/
theorem gcdLoop_spec : ∀ (xs : List Int) (res : Nat), res < 2 ^ 60 →
    (∀ x ∈ xs, x.natAbs < 2 ^ 60) →
    gcdLoop (res : Int) xs = .ok (xs.foldl (fun g a => Nat.gcd g a.natAbs) res : Nat)
  | [], _, _, _ => rfl
  | x :: xs, res, hr, hall => by
    unfold gcdLoop
    by_cases h1 : (res : Int) = 1
    · have : res = 1 := by omega
      subst this
      rw [if_pos h1]
      rw [gcdLoop_spec xs 1 (by decide) (fun y hy => hall y (by simp [hy]))]
      simp only [List.foldl_cons, Nat.gcd_one_left, foldl_gcd_one]
    · simp only [h1, ite_false]
      rw [pyLongGCD_small _ _ (by simpa using hr) (hall x (by simp))]
      simp only [bind, Except.bind]
      have hg : Int.gcd (res : Int) x = Nat.gcd res x.natAbs := rfl
      rw [hg]
      exact gcdLoop_spec xs _ (gcd_lt_of _ _ _ hr (hall x (by simp)))
        (fun y hy => hall y (by simp [hy]))

/-- `math.gcd` docs: "Return the greatest common divisor of the specified
integer arguments ... gcd() without arguments returns 0", with the result
nonnegative. Stated for arguments below `2**60`, where every `_PyLong_GCD`
call takes the `simple:` path; see `GcdGeneral` for the rest. -/
def GcdSmall : Prop :=
  ∀ args : List Int, (∀ a ∈ args, a.natAbs < 2 ^ 60) → gcd args = .ok (listGcd args : Int)

theorem gcdSmall_proven : GcdSmall := by
  intro args hall
  unfold gcd listGcd
  match args, hall with
  | [a, b], hall =>
    simp only
    rw [pyLongGCD_small _ _ (hall a (by simp)) (hall b (by simp))]
    simp [List.foldl, Int.gcd]; rfl
  | [], _ => rfl
  | [a], _ => simp [List.foldl]
  | a :: b :: c :: rest, hall =>
    simp only
    unfold gcdLoop
    by_cases h1 : a = 1
    · subst h1
      simp only [ite_true]
      have := gcdLoop_spec (c :: rest) 1 (by decide) (fun y hy => hall y (by simp [hy]))
      rw [show ((1 : Nat) : Int) = 1 from rfl] at this
      rw [this]
      simp only [List.foldl, Nat.gcd_one_left, Nat.gcd_zero_left, Int.natAbs_one, foldl_gcd_one]
    · simp only [h1, ite_false]
      rw [pyLongGCD_small _ _ (hall a (by simp)) (hall b (by simp))]
      simp only [bind, Except.bind]
      have hb := hall b (by simp)
      refine (gcdLoop_spec (c :: rest) (Int.gcd a b) (gcd_lt_of _ _ _ (hall a (by simp)) hb)
        (fun y hy => hall y (by simp [hy]))).trans ?_
      simp [List.foldl, Int.gcd]

/-- `math.lcm` docs: "lcm() without arguments returns 1", `lcm(a)` is
`abs(a)`, and `lcm(a, b)` is the least common multiple. Stated for two
arguments below `2**60` (one `_PyLong_GCD` call on its `simple:` path); see
`LcmGeneral`. -/
def LcmSmall : Prop :=
  lcm [] = .ok 1 ∧ (∀ a, lcm [a] = .ok (a.natAbs : Int)) ∧
  ∀ a b : Int, a.natAbs < 2 ^ 60 → b.natAbs < 2 ^ 60 →
    lcm [a, b] = .ok (Nat.lcm a.natAbs b.natAbs : Int)

theorem lcmSmall_proven : LcmSmall := by
  refine ⟨rfl, fun a => rfl, fun a b ha hb => ?_⟩
  unfold lcm lcmLoop
  by_cases h0 : a = 0
  · subst h0; simp [lcmLoop, Nat.lcm]
  simp only [h0, ite_false]
  by_cases hb0 : b = 0
  · subst hb0
    have : longLcm a 0 = .ok 0 := by simp [longLcm]
    simp [this, lcmLoop, bind, Except.bind, Nat.lcm]
  have hl : longLcm a b = .ok ((floorDiv a (Int.gcd a b) * b).natAbs : Int) := by
    unfold longLcm
    simp only [h0, hb0, or_self, ite_false]
    rw [pyLongGCD_small _ _ ha hb]
    rfl
  rw [hl]
  simp only [bind, Except.bind, lcmLoop]
  congr 1
  have hdvd : (Int.gcd a b : Int) ∣ a := Int.gcd_dvd_left a b
  have hgpos : 0 < Int.gcd a b := Int.gcd_pos_of_ne_zero_left b h0
  have hgn : Nat.gcd a.natAbs b.natAbs = Int.gcd a b := rfl
  generalize Int.gcd a b = g at *
  obtain ⟨t, ht⟩ := hdvd
  have hq : floorDiv a g = t := by
    unfold floorDiv
    rw [Int.fdiv_eq_ediv_of_dvd ⟨t, ht⟩, ht, Int.mul_ediv_cancel_left _ (by omega)]
  rw [hq]
  unfold Nat.lcm
  have e1 : a.natAbs = g * t.natAbs := by
    have := congrArg Int.natAbs ht; rw [Int.natAbs_mul] at this; simpa using this
  rw [hgn, e1, Nat.mul_assoc, Nat.mul_div_cancel_left _ hgpos, Int.natAbs_mul]

/-- `math.gcd` returns the mathematical gcd for all arguments, including
those that go through Lehmer's loop in `_PyLong_GCD`. -/
def GcdGeneral : Prop := ∀ args : List Int, gcd args = .ok (listGcd args : Int)

/-- `math.lcm` returns the mathematical lcm for all arguments. -/
def LcmGeneral : Prop :=
  ∀ args : List Int,
    lcm args = .ok ((args.foldl (fun (l : Nat) (a : Int) => Nat.lcm l a.natAbs) (1 : Nat) : Nat) : Int)

end PyLean.MathInt
