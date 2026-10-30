import PyLean.Sequences.DequeBasic

/-!
List rotation, and `_deque_rotate`: the chunked block loop rotates the items
by `n` (modulo the length) and keeps the layout invariant.
-/

namespace PyLean.Sequences

open PyLean

/-- Rotate left by `k` items (`k <= len`). -/
def rotL (k : Nat) (l : List Int) : List Int := l.drop k ++ l.take k

/-- Rotate left by `k` modulo the length, for any int `k`; a right rotation
by `n` is `rotLi (-n)`. -/
def rotLi (k : Int) (l : List Int) : List Int := rotL (k % (l.length : Int)).toNat l

theorem length_rotL (k : Nat) (l : List Int) : (rotL k l).length = l.length := by
  unfold rotL; simp only [List.length_append, List.length_drop, List.length_take]; omega

theorem rotL_zero (l : List Int) : rotL 0 l = l := by simp [rotL]

theorem rotL_len (l : List Int) : rotL l.length l = l := by
  simp [rotL, List.drop_length, List.take_length]

theorem rotL_rotL_le (a b : Nat) (l : List Int) (h : a + b ≤ l.length) :
    rotL a (rotL b l) = rotL (a + b) l := by
  unfold rotL
  have hb : a ≤ (l.drop b).length := by simp only [List.length_drop]; omega
  rw [List.drop_append_of_le_length hb, List.take_append_of_le_length hb, List.drop_drop,
    Nat.add_comm b a, List.append_assoc]
  congr 1
  rw [Nat.add_comm a b, List.take_add]

theorem rotL_rotL_ge (a b : Nat) (l : List Int) (ha : a ≤ l.length) (hb : b ≤ l.length)
    (h : l.length ≤ a + b) : rotL a (rotL b l) = rotL (a + b - l.length) l := by
  have h1 : (a + b - l.length) + (l.length - b) ≤ (rotL b l).length := by rw [length_rotL]; omega
  calc rotL a (rotL b l) = rotL (a + b - l.length) (rotL (l.length - b) (rotL b l)) := by
        rw [rotL_rotL_le _ _ _ h1, show a + b - l.length + (l.length - b) = a by omega]
    _ = rotL (a + b - l.length) l := by
        rw [rotL_rotL_le (l.length - b) b l (by omega), show l.length - b + b = l.length by omega, rotL_len]

theorem toNat_emod_lt (k : Int) (l : List Int) (h : l ≠ []) : (k % (l.length : Int)).toNat < l.length := by
  have hl : 0 < (l.length : Int) := by have := List.length_pos_iff.mpr h; omega
  have h1 := Int.emod_lt_of_pos k hl
  have h0 := Int.emod_nonneg k (show (l.length : Int) ≠ 0 by omega)
  omega

theorem length_rotLi (k : Int) (l : List Int) : (rotLi k l).length = l.length := length_rotL _ _

/-- `x % len = y` from `x = y + len * q` and `0 <= y < len`. -/
theorem emod_char (x y len q : Int) (hy0 : 0 ≤ y) (hy1 : y < len) (hx : x = y + len * q) :
    x % len = y := by
  rw [hx, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hy0 hy1]

theorem rotLi_rotLi (a b : Int) (l : List Int) : rotLi a (rotLi b l) = rotLi (a + b) l := by
  by_cases hl : l = []
  · subst hl; simp [rotLi, rotL]
  unfold rotLi
  rw [length_rotL]
  have hpos : 0 < (l.length : Int) := by have := List.length_pos_iff.mpr hl; omega
  have hne : (l.length : Int) ≠ 0 := by omega
  have ha0 := Int.emod_nonneg a hne
  have ha1 := Int.emod_lt_of_pos a hpos
  have hb0 := Int.emod_nonneg b hne
  have hb1 := Int.emod_lt_of_pos b hpos
  have hab : (a + b) % (l.length : Int) = (a % l.length + b % l.length) % l.length := Int.add_emod a b _
  by_cases hlt : a % (l.length : Int) + b % l.length < l.length
  · rw [rotL_rotL_le _ _ _ (by omega)]
    rw [hab, Int.emod_eq_of_lt (by omega) hlt]
    congr 1; omega
  · rw [rotL_rotL_ge _ _ _ (by omega) (by omega) (by omega)]
    have : (a % l.length + b % l.length) % (l.length : Int) = a % l.length + b % l.length - l.length :=
      emod_char _ _ _ 1 (by omega) (by omega) (by omega)
    rw [hab, this]
    congr 1; omega

theorem rotLi_zero (l : List Int) : rotLi 0 l = l := by simp [rotLi, rotL_zero]

theorem rotLi_nat (k : Nat) (l : List Int) (h : k < l.length) : rotLi k l = rotL k l := by
  unfold rotLi
  rw [Int.emod_eq_of_lt (by omega) (by omega)]; rfl

theorem rotLi_add_mul (k q : Int) (l : List Int) : rotLi (k + (l.length : Int) * q) l = rotLi k l := by
  unfold rotLi; rw [Int.add_mul_emod_self_left]

/-! ### The block loops -/

/-- The loop invariant of `_deque_rotate`: both cursors in a block and
`(leftindex + len - 1) % BLOCKLEN == rightindex`. -/
def RotInv (li ri : Int) (len : Nat) : Prop :=
  0 ≤ li ∧ li < 64 ∧ 0 ≤ ri ∧ ri < 64 ∧ (li + (len : Int) - 1) % 64 = ri

theorem rotRight_spec : ∀ (fuel : Nat) (li ri n : Int) (items : List Int),
    RotInv li ri items.length → 0 ≤ n → n ≤ items.length → n < fuel →
    ∃ li' ri', Deque.rotRight fuel li ri items n = .ok (li', ri', rotL (items.length - n.toNat) items) ∧
      RotInv li' ri' items.length
  | 0, _, _, _, _, _, _, _, h => by omega
  | fuel + 1, li, ri, n, items, hinv, hn0, hnl, hf => by
    unfold Deque.rotRight
    by_cases hpos : n > 0
    · rw [iteT hpos]
      simp only
      obtain ⟨h1, h2, h3, h4, h5⟩ := hinv
      generalize hli1 : (if li = 0 then (64 : Int) else li) = li1
      have hli1b : 1 ≤ li1 ∧ li1 ≤ 64 ∧ li1 % 64 = li % 64 := by
        rw [← hli1]; split <;> omega
      generalize hm : min (min n (ri + 1)) li1 = m
      have hm1 : 1 ≤ m ∧ m ≤ n ∧ m ≤ ri + 1 ∧ m ≤ li1 := by
        rw [← hm]; simp only [Int.min_def]; split <;> split <;> omega
      have hlen : (items.length : Int) - m.toNat = (items.length - m.toNat : Nat) := by omega
      have hstep := rotRight_spec fuel (li1 - m) (if ri - m < 0 then 64 - 1 else ri - m) (n - m)
        (items.drop (items.length - m.toNat) ++ items.take (items.length - m.toNat))
      have hlr : (items.drop (items.length - m.toNat) ++ items.take (items.length - m.toNat)).length
          = items.length := length_rotL _ _
      rw [hlr] at hstep
      obtain ⟨li', ri', hres, hinv'⟩ := hstep
        ⟨by omega, by omega, by split <;> omega, by split <;> omega, by split <;> omega⟩
        (by omega) (by omega) (by omega)
      refine ⟨li', ri', ?_, hinv'⟩
      rw [hres]
      congr 3
      show rotL (items.length - (n - m).toNat) (rotL (items.length - m.toNat) items) = _
      rw [rotL_rotL_ge _ _ _ (by omega) (by omega) (by omega)]
      congr 1; omega
    · rw [iteF hpos]
      have : n = 0 := by omega
      subst this
      exact ⟨li, ri, by simp [rotL_len], hinv⟩

theorem rotLeft_spec : ∀ (fuel : Nat) (li ri n : Int) (items : List Int),
    RotInv li ri items.length → n ≤ 0 → -n ≤ items.length → -n < fuel →
    ∃ li' ri', Deque.rotLeft fuel li ri items n = .ok (li', ri', rotL (-n).toNat items) ∧
      RotInv li' ri' items.length
  | 0, _, _, _, _, _, _, _, h => by omega
  | fuel + 1, li, ri, n, items, hinv, hn0, hnl, hf => by
    unfold Deque.rotLeft
    by_cases hneg : n < 0
    · rw [iteT hneg]
      simp only
      obtain ⟨h1, h2, h3, h4, h5⟩ := hinv
      generalize hri1 : (if ri = 64 - 1 then (-1 : Int) else ri) = ri1
      have hri1b : -1 ≤ ri1 ∧ ri1 ≤ 62 ∧ (ri1 + 64) % 64 = ri % 64 := by
        rw [← hri1]; split <;> omega
      generalize hm : min (min (-n) (64 - li)) (64 - 1 - ri1) = m
      have hm1 : 1 ≤ m ∧ m ≤ -n ∧ m ≤ 64 - li ∧ m ≤ 64 - 1 - ri1 := by
        rw [← hm]; simp only [Int.min_def]; split <;> split <;> omega
      have hstep := rotLeft_spec fuel (if li + m = 64 then 0 else li + m) (ri1 + m) (n + m)
        (items.drop m.toNat ++ items.take m.toNat)
      have hlr : (items.drop m.toNat ++ items.take m.toNat).length = items.length := length_rotL _ _
      rw [hlr] at hstep
      obtain ⟨li', ri', hres, hinv'⟩ := hstep
        ⟨by split <;> omega, by split <;> omega, by omega, by omega, by split <;> omega⟩
        (by omega) (by omega) (by omega)
      refine ⟨li', ri', ?_, hinv'⟩
      rw [hres]
      congr 3
      show rotL (-(n + m)).toNat (rotL m.toNat items) = _
      rw [rotL_rotL_le _ _ _ (by omega)]
      congr 1; omega
    · rw [iteF hneg]
      have : n = 0 := by omega
      subst this
      exact ⟨li, ri, by simp [rotL_zero], hinv⟩

/-- The normalisation keeps `n` modulo `len` and lands in `[-len/2, len/2]`. -/
theorem rotNorm_spec (len n : Int) (hlen : 2 ≤ len) :
    ∃ q, Deque.rotNorm len n = n - len * q ∧ -(len / 2) ≤ Deque.rotNorm len n ∧
      Deque.rotNorm len n ≤ len / 2 := by
  unfold Deque.rotNorm
  simp only
  by_cases hbig : n > len / 2 ∨ n < -(len / 2)
  · rw [iteT hbig]
    -- C `%` is `Int.tmod`: `n - len * tdiv n len`, strictly inside `(-len, len)`.
    have ht : n.tmod len = n - len * n.tdiv len := Int.tmod_def n len
    have hlt := Int.tmod_lt_of_pos n (show 0 < len by omega)
    have hgt : -len < n.tmod len := by
      rw [Int.tmod_eq_emod]
      have h0 := Int.emod_nonneg n (show len ≠ 0 by omega)
      have h1 := Int.emod_lt_of_pos n (show 0 < len by omega)
      split
      · simp only [Int.cast_ofNat_Int]; omega
      · rename_i hnd
        have : n % len ≠ 0 := fun hz => hnd (Or.inr (Int.dvd_iff_emod_eq_zero.mpr hz))
        have : (len.natAbs : Int) = len := by omega
        omega
    generalize n.tmod len = t at ht hlt hgt
    generalize n.tdiv len = q at ht
    by_cases h1 : t > len / 2
    · rw [iteT h1]
      refine ⟨q + 1, ?_, by omega, by omega⟩
      rw [Int.mul_add, Int.mul_one]; omega
    · rw [iteF h1]
      by_cases h2 : t < -(len / 2)
      · rw [iteT h2]
        refine ⟨q - 1, ?_, by omega, by omega⟩
        rw [Int.mul_sub, Int.mul_one]; omega
      · rw [iteF h2]
        exact ⟨q, by omega, by omega, by omega⟩
  · rw [iteF hbig]
    exact ⟨0, by simp, by omega, by omega⟩

/-- `_deque_rotate`: for every deque with the layout invariant and every
`Py_ssize_t` `n`, the result keeps the layout, `maxlen` and the length, and
its items are the items rotated right by `n` (left by `-n`) modulo the length. -/
theorem rotateC_spec (d : Deque) (n : Int) (h : d.Layout) :
    ∃ d', d.rotateC n = .ok d' ∧ d'.Layout ∧ d'.items = rotLi (-n) d.items ∧ d'.maxlen = d.maxlen := by
  unfold Deque.rotateC
  by_cases hsmall : d.size ≤ 1
  · rw [iteT hsmall]
    refine ⟨d, rfl, h, ?_, rfl⟩
    rw [Deque.size_eq] at hsmall
    unfold rotLi
    match hl : d.items, hsmall with
    | [], _ => simp [rotL]
    | [x], _ => simp [rotL]
    | _ :: _ :: _, hs => simp at hs; omega
  rw [iteF hsmall]
  rw [Deque.size_eq] at hsmall
  have hlen2 : 2 ≤ (d.items.length : Int) := by omega
  obtain ⟨q, hq, hlo, hhi⟩ := rotNorm_spec _ n hlen2
  rw [← Deque.size_eq] at hq hlo hhi
  generalize Deque.rotNorm d.size n = n' at hq hlo hhi ⊢
  rw [Deque.size_eq] at hq hlo hhi
  dsimp only
  have hinv : RotInv d.left d.right d.items.length := by
    obtain ⟨a, b, c, e, f, _⟩ := h; exact ⟨a, b, c, e, f⟩
  have hne : d.items ≠ [] := by intro he; rw [he] at hlen2; simp at hlen2
  have hdiv : (d.items.length : Int) / 2 < d.items.length := by omega
  -- the target rotation, `rotLi (-n)`, written with `n'`
  have htarget : rotLi (-n) d.items = rotLi (-n') d.items := by
    rw [hq, show -(n - (d.items.length : Int) * q) = -n + (d.items.length : Int) * q by
      rw [Int.neg_sub]; omega, rotLi_add_mul]
  by_cases hp : n' > 0
  · rw [iteT hp]
    obtain ⟨li', ri', hres, hinv'⟩ := rotRight_spec (n'.natAbs + 1) d.left d.right n' d.items hinv
      (by omega) (by omega) (by omega)
    rw [hres]
    refine ⟨_, rfl, ?_, ?_, rfl⟩
    · obtain ⟨a, b, c, e, f⟩ := hinv'
      rw [Deque.layout_iff]; simp only [length_rotL]; exact ⟨a, b, c, e, f, by omega⟩
    · show rotL (d.items.length - n'.toNat) d.items = _
      rw [htarget, show -n' = ((d.items.length - n'.toNat : Nat) : Int) + (d.items.length : Int) * (-1) by omega,
        rotLi_add_mul, rotLi_nat _ _ (by omega)]
  · rw [iteF hp]
    obtain ⟨li', ri', hres, hinv'⟩ := rotLeft_spec (n'.natAbs + 1) d.left d.right n' d.items hinv
      (by omega) (by omega) (by omega)
    rw [hres]
    refine ⟨_, rfl, ?_, ?_, rfl⟩
    · obtain ⟨a, b, c, e, f⟩ := hinv'
      rw [Deque.layout_iff]; simp only [length_rotL]; exact ⟨a, b, c, e, f, by omega⟩
    · show rotL (-n').toNat d.items = _
      rw [htarget, show -n' = (((-n').toNat : Nat) : Int) by omega]
      by_cases hz : (-n').toNat = 0
      · rw [hz]; simp [rotLi_zero, rotL_zero]
      · rw [rotLi_nat _ _ (by omega)]; congr 1

end PyLean.Sequences
