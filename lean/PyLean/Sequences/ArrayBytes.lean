import PyLean.Sequences.ArrayItems

/-!
`array.array` as bytes: `tobytes`, `frombytes`, `byteswap`, `tofile`, `fromfile`,
`__reduce_ex__`, `_array_reconstructor`.
-/

namespace PyLean.Sequences

open PyLean

set_option linter.unusedSectionVars false

/-- The `n` little-endian bytes of `u`. -/
def digits (n : Nat) (u : Nat) : List Nat := (List.range n).map (fun i => (u >>> (8 * i)) % 256)

theorem digits_succ (n u : Nat) : digits (n + 1) u = u % 256 :: digits n (u / 256) := by
  unfold digits
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.mul_zero, Nat.shiftRight_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, Nat.shiftRight_eq_div_pow]
  rw [show 8 * (i + 1) = 8 + 8 * i by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul]

theorem leValue_digits (n u : Nat) : leValue (digits n u) = u % 2 ^ (8 * n) := by
  induction n generalizing u with
  | zero => simp [digits, leValue, Nat.mod_one]
  | succ n ih =>
    rw [digits_succ]
    simp only [leValue]
    rw [ih, show 8 * (n + 1) = 8 + 8 * n by omega, Nat.pow_add, Nat.mod_mul]

theorem digits_leValue (bs : List Nat) (h : ∀ b ∈ bs, b < 256) : digits bs.length (leValue bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hb := h b (by simp)
    simp only [List.length_cons, leValue]
    rw [digits_succ]
    have h1 : (b + 256 * leValue bs) % 256 = b := by omega
    have h2 : (b + 256 * leValue bs) / 256 = leValue bs := by omega
    rw [h1, h2, ih (fun x hx => h x (by simp [hx]))]

theorem leValue_lt (bs : List Nat) (h : ∀ b ∈ bs, b < 256) : leValue bs < 2 ^ (8 * bs.length) := by
  induction bs with
  | nil => simp [leValue]
  | cons b bs ih =>
    have hb := h b (by simp)
    have := ih (fun x hx => h x (by simp [hx]))
    simp only [List.length_cons, leValue]
    rw [show 8 * (bs.length + 1) = 8 + 8 * bs.length by omega, Nat.pow_add]
    generalize 2 ^ (8 * bs.length) = p at this
    have h3 : 256 * (leValue bs + 1) ≤ 256 * p := Nat.mul_le_mul_left _ this
    simp only [show (2 : Nat) ^ 8 = 256 by decide]
    omega

theorem itemBytes_eq (tc : TC) (x : Int) :
    itemBytes tc x = digits tc.itemsize.toNat (x % 2 ^ (8 * tc.itemsize.toNat)).toNat := rfl

theorem length_itemBytes (tc : TC) (x : Int) : (itemBytes tc x).length = tc.itemsize.toNat := by
  simp [itemBytes]

theorem itemBytes_lt (tc : TC) (x : Int) : ∀ b ∈ itemBytes tc x, b < 256 := by
  intro b hb
  simp only [itemBytes, List.mem_map] at hb
  obtain ⟨i, _, e⟩ := hb
  omega

/-- The unsigned or two's complement range of each element, from its size. -/
theorem tc_range (tc : TC) :
    let k := 8 * tc.itemsize.toNat
    ((tc.isSigned || tc == .u) = true → tc.lo = -(2 : Int) ^ (k - 1) ∧ tc.hi = (2 : Int) ^ (k - 1) - 1) ∧
    ((tc.isSigned || tc == .u) = false → tc.lo = 0 ∧ tc.hi = (2 : Int) ^ k - 1) ∧ 1 ≤ k := by
  cases tc <;> decide

theorem natMod_int (x : Int) (k : Nat) :
    (((x % (2 : Int) ^ k).toNat % 2 ^ k : Nat) : Int) = x % (2 : Int) ^ k := by
  have hP : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
  have h0 := Int.emod_nonneg x (show (2 : Int) ^ k ≠ 0 by omega)
  have h1 := Int.emod_lt_of_pos x hP
  have hc : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by simp
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- Storing a value and reading its bytes back gives the value. -/
theorem itemOfBytes_itemBytes (tc : TC) (x : Int) (h : tc.lo ≤ x ∧ x ≤ tc.hi) :
    itemOfBytes tc (itemBytes tc x) = x := by
  unfold itemOfBytes
  rw [itemBytes_eq, leValue_digits]
  obtain ⟨hs, hu, hk⟩ := tc_range tc
  generalize hkd : 8 * tc.itemsize.toNat = k at hs hu hk ⊢
  rw [natMod_int]
  have hP : (2 : Int) ^ k = 2 * 2 ^ (k - 1) := by
    conv => lhs; rw [show k = (k - 1) + 1 by omega, Int.pow_succ]
    rw [Int.mul_comm]
  have hQ : (0 : Int) < 2 ^ (k - 1) := Int.pow_pos (by decide)
  cases hsg : (tc.isSigned || tc == .u)
  · simp only [Bool.false_eq_true, ite_false]
    obtain ⟨h0, h1⟩ := hu hsg
    rw [h0, h1] at h
    exact Int.emod_eq_of_lt (by omega) (by omega)
  · simp only [ite_true]
    obtain ⟨h0, h1⟩ := hs hsg
    rw [h0, h1] at h
    by_cases hneg : x < 0
    · rw [emod_char x (x + 2 ^ k) _ (-1) (by omega) (by omega) (by rw [Int.mul_neg, Int.mul_one]; omega)]
      rw [iteT (by omega)]
      omega
    · rw [Int.emod_eq_of_lt (by omega) (by omega), iteF (by omega)]

/-- Reading a value from `itemsize` bytes and storing it gives the bytes. -/
theorem itemBytes_itemOfBytes (tc : TC) (bs : List Nat) (hl : bs.length = tc.itemsize.toNat)
    (hb : ∀ b ∈ bs, b < 256) : itemBytes tc (itemOfBytes tc bs) = bs := by
  have hlt := leValue_lt bs hb
  rw [hl] at hlt
  obtain ⟨_, _, hk⟩ := tc_range tc
  have hdig : digits tc.itemsize.toNat (leValue bs) = bs := by
    rw [← hl]; exact digits_leValue bs hb
  have key : (itemOfBytes tc bs % 2 ^ (8 * tc.itemsize.toNat)).toNat = leValue bs := by
    generalize hkd : 8 * tc.itemsize.toNat = k at hlt hk
    have hP : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
    have hc : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by simp
    have hv : ((leValue bs : Nat) : Int) % 2 ^ k = leValue bs := Int.emod_eq_of_lt (by omega) (by omega)
    have e : itemOfBytes tc bs = (leValue bs : Int) ∨ itemOfBytes tc bs = (leValue bs : Int) - 2 ^ k := by
      unfold itemOfBytes
      dsimp only
      rw [hkd]
      split
      · split
        · exact Or.inr rfl
        · exact Or.inl rfl
      · exact Or.inl rfl
    rcases e with e | e
    · rw [e, hv]; simp
    · rw [e, emod_char _ (leValue bs : Int) _ (-1) (by omega) (by omega) (by rw [Int.mul_neg, Int.mul_one]; omega)]; simp
  rw [itemBytes_eq, key, hdig]

theorem itemOfBytes_range (tc : TC) (bs : List Nat) (hl : bs.length = tc.itemsize.toNat)
    (hb : ∀ b ∈ bs, b < 256) : tc.lo ≤ itemOfBytes tc bs ∧ itemOfBytes tc bs ≤ tc.hi := by
  have hlt := leValue_lt bs hb
  rw [hl] at hlt
  obtain ⟨hs, hu, hk⟩ := tc_range tc
  generalize hkd : 8 * tc.itemsize.toNat = k at hs hu hk hlt
  have hP : (2 : Int) ^ k = 2 * 2 ^ (k - 1) := by
    conv => lhs; rw [show k = (k - 1) + 1 by omega, Int.pow_succ]
    rw [Int.mul_comm]
  have hc : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by simp
  unfold itemOfBytes
  rw [hkd]
  cases hsg : (tc.isSigned || tc == .u)
  · simp only [Bool.false_eq_true, ite_false]
    obtain ⟨h0, h1⟩ := hu hsg
    rw [h0, h1]
    omega
  · simp only [ite_true]
    obtain ⟨h0, h1⟩ := hs hsg
    rw [h0, h1]
    split <;> omega

/-- Splitting the bytes of a list of items gives the items' bytes. -/
theorem chunks_flatMap (tc : TC) (xs : List Int) (fuel : Nat) (hf : xs.length ≤ fuel) :
    chunks tc.itemsize.toNat (xs.flatMap (itemBytes tc)) fuel = xs.map (itemBytes tc) := by
  have hn : 0 < tc.itemsize.toNat := by rcases itemsize_cases tc with h | h | h | h <;> rw [h] <;> decide
  induction xs generalizing fuel with
  | nil =>
    cases fuel <;> rfl
  | cons x xs ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      simp only [chunks, List.flatMap_cons, List.map_cons]
      have hl := length_itemBytes tc x
      have hne : (itemBytes tc x ++ xs.flatMap (itemBytes tc)).isEmpty = false := by
        apply List.isEmpty_eq_false_iff.mpr
        intro he
        have := congrArg List.length he
        simp only [List.length_append, List.length_nil] at this
        omega
      rw [hne]
      simp only [Bool.false_eq_true, ite_false]
      rw [← hl, List.take_left', List.drop_left', hl, ih _ (by simp at hf; omega)]
      all_goals rfl

theorem length_arrToBytes (a : Arr) : (arrToBytes a).length = a.items.length * a.tc.itemsize.toNat := by
  unfold arrToBytes
  generalize a.items = l
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, length_itemBytes, ih, List.length_cons]
    rw [Nat.add_mul]; omega

theorem map_itemOf (tc : TC) (xs : List Int) (h : ∀ x ∈ xs, tc.lo ≤ x ∧ x ≤ tc.hi) :
    ((xs.map (itemBytes tc)).map (itemOfBytes tc)) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons]
    rw [itemOfBytes_itemBytes tc x (h x (by simp)), ih (fun y hy => h y (by simp [hy]))]

theorem memcpy_end (l src : List Int) : memcpy (l ++ List.replicate src.length 0) l.length src = l ++ src := by
  unfold memcpy
  rw [show ((l.length : Int)).toNat = l.length by omega,
    show ((l.length : Int) + src.length).toNat = l.length + src.length by omega, List.take_left',
    List.drop_eq_nil_of_le (by simp)]
  · simp
  · rfl

theorem resized_grow (l : List Int) (k : Nat) (hk : 0 < k) :
    resized l ((l.length : Int) + k) = l ++ List.replicate k 0 := by
  rw [resized_gt _ _ (by omega)]
  congr 2
  omega

/-- `a.tobytes()` is the concatenated bytes of the items, `a.frombytes(b)` appends
items decoded from `b`, and the two are inverse: for every array `b` (type invariant
`WF`) and every array `a` of the same typecode (no buffer exported, the result
fits): `a.frombytes(b.tobytes())` gives `a + b`; `len(b.tobytes())` is
`len(b) * itemsize`; `frombytes` of a length that is not a multiple of `itemsize`
raises `ValueError` and of a buffer whose `itemsize` is not 1 `TypeError`. -/
def ArrayBytesRoundTrip : Prop :=
  ∀ (a b : Arr), a.tc = b.tc → b.WF → a.exports = 0 → a.Fits (a.items.length + b.items.length) →
    (∃ a', arrFromBytes a (arrToBytes b) 1 = .ok a' ∧ a'.items = a.items ++ b.items) ∧
    ((arrToBytes b).length = b.items.length * b.tc.itemsize.toNat) ∧
    (∀ bs : List Nat, (bs.length : Int) % a.tc.itemsize ≠ 0 →
      arrFromBytes a bs 1 = .error (.valueError "bytes length not a multiple of item size")) ∧
    (∀ (bs : List Nat) (w : Int), w ≠ 1 → arrFromBytes a bs w = .error (.typeError "a bytes-like object is required"))

theorem arrayBytesRoundTrip_proven : ArrayBytesRoundTrip := by
  intro a b htc hw hx hf
  refine ⟨?_, length_arrToBytes b, fun bs hm => ?_, fun bs w hw' => ?_⟩
  · have hsz := itemsize_cases a.tc
    have hlen := length_arrToBytes b
    rw [← htc] at hlen
    have hbs : ((arrToBytes b).length : Int) = (b.items.length : Int) * a.tc.itemsize := by
      rw [hlen, Int.natCast_mul, show ((a.tc.itemsize.toNat : Nat) : Int) = a.tc.itemsize by
        rcases hsz with h | h | h | h <;> rw [h] <;> rfl]
    by_cases hb0 : b.items.length = 0
    · have he : b.items = [] := List.eq_nil_of_length_eq_zero hb0
      unfold arrFromBytes
      simp only [bind, Except.bind, pure, Except.pure, throwE]
      have h0 : arrToBytes b = [] := by simp [arrToBytes, he]
      rw [h0]
      simp [he]
    have hdiv : ((arrToBytes b).length : Int) % a.tc.itemsize = 0 := by
      rw [hbs]; exact Int.mul_emod_left _ _
    have hq : ((arrToBytes b).length : Int) / a.tc.itemsize = b.items.length := by
      rw [hbs]; exact Int.mul_ediv_cancel _ (by rcases hsz with h | h | h | h <;> rw [h] <;> decide)
    obtain ⟨a1, hr, hi, ht, _⟩ := arrResize_ok a (a.items.length + b.items.length) hx (by omega) hf
    have hres : a1.items = a.items ++ List.replicate b.items.length 0 := by
      rw [hi, show ((a.items.length : Int) + b.items.length) = (a.items.length : Int) + (b.items.length : Nat) by rfl]
      exact resized_grow _ _ (by omega)
    have hps : (b.items.length : Int) > 0 := by omega
    unfold arrFromBytes
    simp only [bind, Except.bind, pure, Except.pure, throwE]
    simp only [show ¬ ((1 : Int) ≠ 1) by decide, ite_false, hdiv, show ¬ ((0 : Int) ≠ 0) by decide, hq]
    rw [iteT hps]
    have hsm : ¬ ((b.items.length : Int) > ssizeMax - a.items.length ∨
        (a.items.length : Int) + b.items.length > ssizeMax / a.tc.itemsize) := by
      unfold Arr.Fits at hf
      have : ssizeMax / a.tc.itemsize ≤ ssizeMax := Int.ediv_le_self _ (by unfold ssizeMax; omega)
      omega
    rw [iteF hsm]
    simp only [hr]
    refine ⟨_, rfl, ?_⟩
    show memcpy a1.items _ _ = _
    have hch : (chunks a.tc.itemsize.toNat (arrToBytes b) (arrToBytes b).length).map (itemOfBytes a1.tc) = b.items := by
      rw [ht, htc]
      unfold arrToBytes
      rw [chunks_flatMap b.tc b.items _ (by
        have := length_arrToBytes b
        unfold arrToBytes at this
        rw [this]
        rcases itemsize_cases b.tc with h | h | h | h <;> rw [h] <;> simp <;> omega)]
      exact map_itemOf b.tc b.items hw
    rw [ht] at hch
    rw [hch, hres]
    exact memcpy_end _ _
  · unfold arrFromBytes
    simp only [bind, Except.bind, pure, Except.pure, throwE, show ¬ ((1 : Int) ≠ 1) by decide, ite_false]
    rw [iteT hm]
  · unfold arrFromBytes
    simp only [bind, Except.bind, pure, Except.pure, throwE]
    rw [iteT hw']

theorem swapped_item (tc : TC) (x : Int) :
    itemBytes tc (itemOfBytes tc (itemBytes tc x).reverse) = (itemBytes tc x).reverse :=
  itemBytes_itemOfBytes tc _ (by rw [List.length_reverse, length_itemBytes])
    (fun b hb => itemBytes_lt tc x b (List.mem_reverse.mp hb))

theorem itemOfBytes_inj (tc : TC) (x y : Int) (hx : tc.lo ≤ x ∧ x ≤ tc.hi) (hy : tc.lo ≤ y ∧ y ≤ tc.hi)
    (h : itemBytes tc x = itemBytes tc y) : x = y := by
  rw [← itemOfBytes_itemBytes tc x hx, ← itemOfBytes_itemBytes tc y hy, h]

/-- `a.byteswap()` reverses the bytes of every item, in place, and is its own
inverse on any array (type invariant `WF`, for every typecode): `tobytes` then
gives each item's bytes reversed, the result is `WF` again, and a second
`byteswap` restores the array. -/
def ArrayByteswap : Prop :=
  ∀ (a : Arr), a.WF →
    (arrByteswap a).WF ∧ arrToBytes (arrByteswap a) = a.items.flatMap (fun x => (itemBytes a.tc x).reverse) ∧
    arrByteswap (arrByteswap a) = a

theorem arrayByteswap_proven : ArrayByteswap := by
  intro a hw
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    simp only [arrByteswap, List.mem_map] at hy
    obtain ⟨x, _, rfl⟩ := hy
    exact itemOfBytes_range a.tc _ (by rw [List.length_reverse, length_itemBytes])
      (fun b hb => itemBytes_lt a.tc x b (List.mem_reverse.mp hb))
  · simp only [arrToBytes, arrByteswap]
    generalize a.items = l
    induction l with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons, List.flatMap_cons, swapped_item, ih]
  · have h : ∀ l : List Int, (∀ x ∈ l, a.tc.lo ≤ x ∧ x ≤ a.tc.hi) →
        (l.map (fun x => itemOfBytes a.tc (itemBytes a.tc x).reverse)).map
          (fun x => itemOfBytes a.tc (itemBytes a.tc x).reverse) = l := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons x xs ih =>
        intro hl
        simp only [List.map_cons]
        rw [swapped_item, List.reverse_reverse, itemOfBytes_itemBytes a.tc x (hl x (by simp)),
          ih (fun y hy => hl y (by simp [hy]))]
    obtain ⟨tc, items, al, hb, ex, tn⟩ := a
    simp only [arrByteswap]
    congr 1
    exact h _ hw

end PyLean.Sequences
