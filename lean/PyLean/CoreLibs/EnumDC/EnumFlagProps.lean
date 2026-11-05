import PyLean.CoreLibs.EnumDC.EnumObj

/-!
Properties of the bit helpers, of iterating a `Flag` value, of `Flag._generate_next_value_`, of `verify(CONTINUOUS)` and
of `Flag._missing_` under `CONFORM`.
-/

namespace PyLean.CoreLibs.EnumDC

open PyLean

/-! ### `_iter_bits_lsb` and `bit_count` -/

theorem bitLength_half (n : Nat) (h : 0 < n) : bitLength n = bitLength (n / 2) + 1 := by
  unfold bitLength
  have hn : n ≠ 0 := by omega
  simp only [hn, ↓reduceIte]
  rw [Nat.log2_def n]
  by_cases h2 : 2 ≤ n
  · have : n / 2 ≠ 0 := by omega
    simp [h2, this]
  · have : n = 1 := by omega
    subst this
    decide

theorem lowBit_odd (n : Nat) (h : n % 2 = 1) : lowBit n = 1 := by
  unfold lowBit
  rw [bitLength_half n (by omega)]
  simp [lowBitAux, h]

theorem lowBit_double (m : Nat) (h : 0 < m) : lowBit (2 * m) = 2 * lowBit m := by
  unfold lowBit
  rw [bitLength_half (2 * m) (by omega)]
  have h1 : 2 * m / 2 = m := by omega
  have h2 : ¬ (2 * m % 2 = 1) := by omega
  simp only [lowBitAux, h1, h2, ↓reduceIte]

theorem xor_double (a b : Nat) : (2 * a) ^^^ (2 * b) = 2 * (a ^^^ b) := by
  have h : ∀ x : Nat, 2 * x = x <<< 1 := fun x => by rw [Nat.shiftLeft_eq]; omega
  rw [h a, h b, h (a ^^^ b), Nat.shiftLeft_xor_distrib]

theorem xor_odd_one (a : Nat) : (2 * a + 1) ^^^ 1 = 2 * a := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero =>
    have e1 : (2 * a + 1) % 2 = 1 := by omega
    have e2 : (2 * a) % 2 = 0 := by omega
    simp [Nat.testBit_xor, Nat.testBit_zero, e1, e2]
  | succ j =>
    rw [Nat.testBit_xor, Nat.testBit_add_one, Nat.testBit_add_one, Nat.testBit_add_one]
    have e1 : (2 * a + 1) / 2 = a := by omega
    have e2 : (2 * a) / 2 = a := by omega
    rw [e1, e2]
    simp

theorem iterBits_zero (f : Nat) : iterBits f 0 = [] := by
  cases f <;> rfl

theorem iterBits_double : ∀ (f m : Nat), iterBits f (2 * m) = (iterBits f m).map (2 * ·)
  | 0, _ => rfl
  | f + 1, m => by
    by_cases hm : m = 0
    · subst hm
      simp [iterBits]
    · have h2 : 2 * m ≠ 0 := by omega
      simp only [iterBits, h2, hm, ↓reduceIte, List.map_cons]
      rw [lowBit_double m (by omega), xor_double, iterBits_double f]

theorem iterBits_odd (f a : Nat) : iterBits (f + 1) (2 * a + 1) = 1 :: (iterBits f a).map (2 * ·) := by
  have h1 : 2 * a + 1 ≠ 0 := by omega
  simp only [iterBits, h1, ↓reduceIte]
  rw [lowBit_odd _ (by omega), xor_odd_one, iterBits_double]

/-- The set bits of `n` as powers of two, lowest first: bit 0, then the bits of `n // 2` doubled. -/
def bitsSpec (n : Nat) : List Nat :=
  if n = 0 then [] else (if n % 2 = 1 then [1] else []) ++ (bitsSpec (n / 2)).map (2 * ·)
termination_by n
decreasing_by omega

theorem iterBits_spec (n : Nat) : ∀ f, bitLength n < f → iterBits f n = bitsSpec n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro f hf
    by_cases h0 : n = 0
    · subst h0
      rw [iterBits_zero, bitsSpec]
      simp
    · have hl := bitLength_half n (by omega)
      by_cases hodd : n % 2 = 1
      · have hn : n = 2 * (n / 2) + 1 := by omega
        obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
        conv => lhs; rw [hn]
        rw [iterBits_odd, ih (n / 2) (by omega) f' (by omega)]
        conv => rhs; rw [bitsSpec]
        simp [h0, hodd]
      · have hn : n = 2 * (n / 2) := by omega
        conv => lhs; rw [hn]
        rw [iterBits_double, ih (n / 2) (by omega) f (by omega)]
        conv => rhs; rw [bitsSpec]
        simp [h0, hodd]

theorem bitsOf_spec (n : Nat) : bitsOf n = bitsSpec n := iterBits_spec n _ (by omega)

theorem mem_bitsSpec (n : Nat) : ∀ b, b ∈ bitsSpec n ↔ ∃ i, b = 2 ^ i ∧ n.testBit i = true := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro b
    rw [bitsSpec]
    by_cases h0 : n = 0
    · subst h0
      simp
    · simp only [h0, ↓reduceIte, List.mem_append, List.mem_map]
      constructor
      · rintro (hb | ⟨b', hb', rfl⟩)
        · split at hb
          · rename_i hodd
            simp only [List.mem_singleton] at hb
            subst hb
            exact ⟨0, rfl, by simp [Nat.testBit_zero, hodd]⟩
          · simp at hb
        · obtain ⟨i, rfl, hi⟩ := (ih (n / 2) (by omega) b').1 hb'
          exact ⟨i + 1, by rw [Nat.pow_succ, Nat.mul_comm], by rw [Nat.testBit_add_one]; exact hi⟩
      · rintro ⟨i, rfl, hi⟩
        cases i with
        | zero =>
          left
          have : n % 2 = 1 := by simpa [Nat.testBit_zero] using hi
          simp [this]
        | succ j =>
          right
          refine ⟨2 ^ j, (ih (n / 2) (by omega) _).2 ⟨j, rfl, by rwa [Nat.testBit_add_one] at hi⟩, ?_⟩
          rw [Nat.pow_succ, Nat.mul_comm]

theorem bitsSpec_sorted (n : Nat) : (bitsSpec n).Pairwise (· < ·) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [bitsSpec]
    by_cases h0 : n = 0
    · simp [h0]
    · simp only [h0, ↓reduceIte]
      rw [List.pairwise_append]
      refine ⟨?_, ?_, ?_⟩
      · split <;> simp
      · rw [List.pairwise_map]
        exact List.Pairwise.imp (fun h => by omega) (ih (n / 2) (by omega))
      · intro a ha b hb
        split at ha
        · simp only [List.mem_singleton] at ha
          subst ha
          obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
          obtain ⟨i, rfl, _⟩ := (mem_bitsSpec _ _).1 hb'
          have := Nat.one_le_two_pow (n := i)
          omega
        · simp at ha

/-- `_iter_bits_lsb`, run to the end: a negative value, given or the value of the member given, is the `ValueError`
with the `repr` of what was given; otherwise the generator yields exactly the powers of two of the set bits, each once,
from the lowest. So the unwrap of a member, the error, and the order are all pinned. -/
def IterBitsLsb : Prop :=
  (∀ n : Int, n < 0 → iterBitsLsb (.int n) = .error (.valueError s!"{n} is not a positive integer")) ∧
  (∀ (v : Int) (s : String), v < 0 →
    iterBitsLsb (.member v (.ok s)) = .error (.valueError s!"{s} is not a positive integer") ∧
    iterBitsLsb (.intSub v (.ok s)) = .error (.valueError s!"{s} is not a positive integer")) ∧
  (∀ (v : Int) (e : PyExc), v < 0 → iterBitsLsb (.member v (.error e)) = .error e ∧
    iterBitsLsb (.intSub v (.error e)) = .error e) ∧
  (∀ (n : Nat) (r : Py String), iterBitsLsb (.int n) = .ok (bitsOf n) ∧ iterBitsLsb (.member n r) = .ok (bitsOf n) ∧
    iterBitsLsb (.intSub n r) = .ok (bitsOf n)) ∧
  (∀ n b, b ∈ bitsOf n ↔ ∃ i, b = 2 ^ i ∧ n.testBit i = true) ∧
  (∀ n, (bitsOf n).Pairwise (· < ·))

theorem iterBitsLsb_proven : IterBitsLsb := by
  refine ⟨fun n h => ?_, fun v s h => ⟨?_, ?_⟩, fun v e h => ⟨?_, ?_⟩, fun n r => ?_, fun n b => ?_, fun n => ?_⟩
  · unfold iterBitsLsb
    simp only [h, ↓reduceIte, BitsArg.repr]
    rfl
  · unfold iterBitsLsb
    simp only [h, ↓reduceIte, BitsArg.repr]
  · unfold iterBitsLsb
    simp only [h, ↓reduceIte, BitsArg.repr]
  · unfold iterBitsLsb
    simp only [h, ↓reduceIte, BitsArg.repr]
  · unfold iterBitsLsb
    simp only [h, ↓reduceIte, BitsArg.repr]
  · have hn : ¬ ((n : Int) < 0) := by omega
    refine ⟨?_, ?_, ?_⟩ <;> simp [iterBitsLsb, hn]
  · rw [bitsOf_spec]; exact mem_bitsSpec n b
  · rw [bitsOf_spec]; exact bitsSpec_sorted n

/-- `Flag.__len__` is `int.bit_count()`: zero for 0, the same for `2n`, one more for `2n + 1`, which fixes it on every
value; and on a class whose members are in value order, for a value with no bit outside `_flag_mask_`, it is the number of
items `iter` yields. -/
def FlagLen : Prop :=
  bitCount 0 = 0 ∧ (∀ n, bitCount (2 * n) = bitCount n ∧ bitCount (2 * n + 1) = bitCount n + 1) ∧
  ∀ (c : FlagCls) (cache : List (Nat × Option String)) (v : Nat) (l : List (Option MapEntry)),
    c.valueOrdered = true → v &&& c.flagMask = v → c.iterC cache v = .ok l → l.length = bitCount v

theorem flagLen_proven : FlagLen := by
  refine ⟨rfl, fun n => ⟨?_, ?_⟩, ?_⟩
  · simp only [bitCount, bitsOf_spec]
    by_cases h : n = 0
    · subst h; rfl
    · conv => lhs; rw [bitsSpec]
      have h1 : 2 * n ≠ 0 := by omega
      have h2 : ¬ (2 * n % 2 = 1) := by omega
      have h3 : 2 * n / 2 = n := by omega
      simp [h1, h2, h3]
  · simp only [bitCount, bitsOf_spec]
    conv => lhs; rw [bitsSpec]
    have h1 : 2 * n + 1 ≠ 0 := by omega
    have h2 : (2 * n + 1) % 2 = 1 := by omega
    have h3 : (2 * n + 1) / 2 = n := by omega
    simp [h2, h3]
  · intro c cache v l ho hv h
    simp only [FlagCls.iterC, ho, ↓reduceIte, FlagCls.byValue, hv, Except.ok.injEq] at h
    subst h
    simp [bitCount]

/-- `len(x)` is the number of members `iter(x)` yields, the docs' "Returns number of members in flag". False: under
`KEEP`, bits outside the class are counted by `bit_count` and skipped by `__iter__`, which masks with `_flag_mask_`, so
`F(8)` of a three-bit class has `len` 1 and no members. -/
def LenMatchesIter : Prop :=
  ∀ (c : FlagCls) (v : Int) (n : Nat) (name : Option String) (l : List (Option MapEntry)),
    c.call v = .ok (.flag n name) → c.iterC [] n = .ok l → bitCount n = l.length

theorem lenMatchesIter_refuted : ¬LenMatchesIter := by
  intro h
  have := h ⟨"F", [("A", 1), ("B", 2), ("C", 4)], .keep⟩ 8 8 none [] (by decide +kernel) (by decide +kernel)
  revert this
  decide

/-! ### Iterating a `Flag` value -/

/-- `Flag.__iter__`, every path: in a class whose members are in value order, `_value2member_map_.get` of each bit of
`value & _flag_mask_` from the lowest, which is the member with that value, else a pseudo-member stored since, else
`None`; in any other class the first bit with no member raises `AttributeError` for its `_sort_order_` (on `None`, or on a
pseudo-member), and otherwise the members come in definition order. `F(w)` stores the pseudo-member it makes, so a later
iteration yields it. -/
def FlagIterPaths : Prop :=
  ∀ (c : FlagCls) (cache : List (Nat × Option String)) (v : Nat),
    (c.valueOrdered = true → c.iterC cache v = .ok ((bitsOf (v &&& c.flagMask)).map (c.mapGet cache))) ∧
    (c.valueOrdered = false → ∀ e, (c.byValue cache v).findSome? c.sortKey = some e → c.iterC cache v = .error e) ∧
    (c.valueOrdered = false → (c.byValue cache v).findSome? c.sortKey = none →
      c.iterC cache v = .ok ((c.canonical.filter (fun p => isSingleBit p.2 &&
        (c.byValue cache v).contains (some (.member p.1 p.2)))).map (fun p => some (.member p.1 p.2)))) ∧
    (∀ b n, c.memberOf b = some n → c.mapGet cache b = some (.member n b)) ∧
    (∀ b, c.memberOf b = none → c.mapGet cache b = (cache.lookup b).map (.pseudo b)) ∧
    c.sortKey none = some (.named "AttributeError" "'NoneType' object has no attribute '_sort_order_'") ∧
    (∀ w n, c.sortKey (some (.pseudo w n)) =
      some (.named "AttributeError" s!"'{c.name}' object has no attribute '_sort_order_'")) ∧
    (∀ n w, c.sortKey (some (.member n w)) = none) ∧
    (∀ w n name, c.call w = .ok (.flag n name) → c.mapGet cache n = none →
      c.callC cache w = .ok (.flag n name, cache ++ [(n, name)]) ∧
      c.mapGet (cache ++ [(n, name)]) n = some (.pseudo n name))

theorem flagIterPaths_proven : FlagIterPaths := by
  intro c cache v
  refine ⟨fun h => by simp [FlagCls.iterC, h, FlagCls.byValue], fun h e he => by simp [FlagCls.iterC, h,
    FlagCls.byDef, he], fun h he => by simp [FlagCls.iterC, h, FlagCls.byDef, he], fun b n h => by
    simp [FlagCls.mapGet, h], fun b h => by simp [FlagCls.mapGet, h], rfl, fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  intro w n name hc hg
  refine ⟨by simp [FlagCls.callC, hc, hg], ?_⟩
  have hm : c.memberOf n = none := by
    unfold FlagCls.mapGet at hg
    cases h : c.memberOf n with
    | none => rfl
    | some x => simp [h] at hg
  have hl : cache.lookup n = none := by
    simp only [FlagCls.mapGet, hm, Option.map_eq_none_iff] at hg
    exact hg
  simp [FlagCls.mapGet, hm, List.lookup_append, hl]

/-- Every item `iter(x)` yields is a member of the class: Doc/library/enum.rst:632-634, "Returns all contained
non-alias members". False: an alias such as `X = 6` with no member for its bits makes
`list(F.X)` yield `None` twice, since `_iter_member_by_value_` uses `_value2member_map_.get`. -/
def FlagIterMembers : Prop :=
  ∀ (c : FlagCls) (cache : List (Nat × Option String)) (v : Nat) (l : List (Option MapEntry)),
    c.iterC cache v = .ok l → ∀ x ∈ l, ∃ n w, x = some (.member n w)

theorem flagIterMembers_refuted : ¬FlagIterMembers := by
  intro h
  have h1 : (FlagCls.iterC ⟨"H", [("A", 1), ("X", 6)], .strict⟩ [] 6) = .ok [none, none] := by decide +kernel
  obtain ⟨n, w, hx⟩ := h _ _ _ _ h1 none (by simp)
  cases hx

/-! ### Values that are `int`s -/

/-- The operations behave on `int` objects as on Python `int`s: what the theorems on `int` values assume. -/
structure IntOps {α : Type} (o : Ops α) : Prop where
  same_int : ∀ a b, o.same (o.ofInt a) (o.ofInt b) = true → a = b
  hash_int : ∀ a, ∃ h, o.hash (o.ofInt a) = .ok h
  eq_int : ∀ a b, o.eq (o.ofInt a) (o.ofInt b) = .ok (decide (a = b))
  lt_int : ∀ a b, o.lt (o.ofInt a) (o.ofInt b) = .ok (decide (a < b))
  gt_int : ∀ a b, o.gt (o.ofInt a) (o.ofInt b) = .ok (decide (a > b))
  succ_int : ∀ a, o.succ (o.ofInt a) = .ok (o.ofInt (a + 1))
  index_int : ∀ a, o.index (o.ofInt a) = .ok a
  bitLength_int : ∀ a, o.bitLength (o.ofInt a) = .ok (intBitLength a)
  asInt_int : ∀ a, o.asInt (o.ofInt a) = some a

theorem evOps_intOps : IntOps evOps where
  same_int a b h := by simp [evOps] at h
  hash_int a := ⟨0, rfl⟩
  eq_int a b := by simp [evOps]
  lt_int a b := rfl
  gt_int a b := rfl
  succ_int a := rfl
  index_int a := rfl
  bitLength_int a := rfl
  asInt_int a := rfl

theorem pvOps_intOps : IntOps pvOps where
  same_int a b h := by simpa [pvOps] using h
  hash_int a := ⟨intHash a, rfl⟩
  eq_int a b := by
    simp only [pvOps, pvEq, PV.norm, pvEq0, Except.ok.injEq]
    cases h : (a == b) <;> simp_all
  lt_int a b := by simp [pvOps, pvCmp, PV.norm]
  gt_int a b := by simp [pvOps, pvCmp, PV.norm]
  succ_int a := rfl
  index_int a := rfl
  bitLength_int a := rfl
  asInt_int a := rfl

section Ints

variable {α : Type} {o : Ops α}

theorem ofInt_inj (h : IntOps o) {a b : Int} (e : o.ofInt a = o.ofInt b) : a = b := by
  have h1 := h.eq_int a b
  rw [e, h.eq_int b b] at h1
  simp only [decide_true, Except.ok.injEq] at h1
  exact of_decide_eq_true h1.symm

theorem dictFind_ints (h : IntOps o) (a : Int) (H : Int) (hh : o.hash (o.ofInt a) = .ok H) :
    ∀ xs : List Int, o.dictFind (o.ofInt a) H (xs.map fun x => (o.ofInt x, ())) =
      .ok (if a ∈ xs then some () else none)
  | [] => rfl
  | x :: xs => by
    have ih := dictFind_ints h a H hh xs
    simp only [List.map_cons, Ops.dictFind]
    by_cases hs : o.same (o.ofInt x) (o.ofInt a) = true
    · have := h.same_int x a hs
      subst this
      simp [hs]
    · simp only [hs, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨Hx, hx⟩ := h.hash_int x
      rw [hx]
      by_cases hxa : x = a
      · subst hxa
        rw [hh] at hx
        cases hx
        simp [h.eq_int]
      · simp only [h.eq_int, hxa, decide_false]
        by_cases hH : Hx = H
        · simp only [hH, ↓reduceIte, ih]
          simp [List.mem_cons, Ne.symm hxa]
        · simp only [hH, ↓reduceIte, ih]
          simp [List.mem_cons, Ne.symm hxa]

theorem lookupIn_ints (h : IntOps o) (w : String) (a : Int) (xs : List Int) :
    o.lookupIn w (xs.map fun x => (o.ofInt x, ())) (o.ofInt a) = .ok (if a ∈ xs then some () else none) := by
  obtain ⟨H, hh⟩ := h.hash_int a
  simp only [Ops.lookupIn, hh]
  exact dictFind_ints h a H hh xs

/-- The insertion order of `set(l)`. -/
def dedupInto : List Int → List Int → List Int
  | acc, [] => acc
  | acc, x :: r => if x ∈ acc then dedupInto acc r else dedupInto (acc ++ [x]) r

theorem mem_dedupInto : ∀ (l acc : List Int) (z : Int), z ∈ dedupInto acc l ↔ z ∈ acc ∨ z ∈ l
  | [], acc, z => by simp [dedupInto]
  | x :: r, acc, z => by
    simp only [dedupInto]
    split
    · rename_i hx
      rw [mem_dedupInto r acc z]
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr (List.mem_cons_of_mem _ h)
      · rintro (h | h)
        · exact .inl h
        · rcases List.mem_cons.1 h with rfl | h
          · exact .inl hx
          · exact .inr h
    · rw [mem_dedupInto r (acc ++ [x]) z, List.mem_append, List.mem_singleton, List.mem_cons]
      constructor
      · rintro ((h | h) | h)
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr h)
      · rintro (h | h | h)
        · exact .inl (.inl h)
        · exact .inl (.inr h)
        · exact .inr h

theorem setOf_ints (h : IntOps o) : ∀ (l acc : List Int),
    o.setOf (l.map o.ofInt) (acc.map fun x => (o.ofInt x, ())) = .ok ((dedupInto acc l).map fun x => (o.ofInt x, ()))
  | [], acc => rfl
  | x :: r, acc => by
    simp only [List.map_cons, Ops.setOf, lookupIn_ints h, dedupInto]
    by_cases hx : x ∈ acc
    · simp only [hx, ↓reduceIte]
      exact setOf_ints h r acc
    · simp only [hx, ↓reduceIte]
      have := setOf_ints h r (acc ++ [x])
      rw [List.map_append] at this
      exact this

theorem setIn_ints (h : IntOps o) (dd : List Int) (a : Int) :
    o.setIn (dd.map fun x => (o.ofInt x, ())) (o.ofInt a) = .ok (decide (a ∈ dd)) := by
  simp only [Ops.setIn, lookupIn_ints h]
  by_cases ha : a ∈ dd <;> simp [ha]

theorem missingFrom_ints (h : IntOps o) (dd : List Int) : ∀ ps : List Int,
    o.missingFrom (dd.map fun x => (o.ofInt x, ())) ps = .ok (ps.filter fun k => !decide (k ∈ dd))
  | [] => rfl
  | k :: r => by
    simp only [Ops.missingFrom, setIn_ints h, missingFrom_ints h dd r, List.filter_cons]
    by_cases hk : k ∈ dd <;> simp [hk]

/-- `min`/`max` of `int` objects is the least/greatest of the values, which is one of them. -/
theorem extremum_lt_ints (h : IntOps o) : ∀ (r : List Int) (x : Int),
    ∃ m, extremum o.lt (o.ofInt x) (r.map o.ofInt) = .ok (o.ofInt m) ∧ m ∈ x :: r ∧ ∀ y ∈ x :: r, m ≤ y
  | [], x => ⟨x, rfl, by simp, by simp⟩
  | y :: r, x => by
    simp only [List.map_cons, extremum, h.lt_int]
    by_cases hyx : y < x
    · obtain ⟨m, hm, h1, h2⟩ := extremum_lt_ints h r y
      refine ⟨m, by simp [hyx, hm], List.mem_cons_of_mem _ h1, ?_⟩
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | rfl | hz
      · have := h2 y (by simp); omega
      · exact h2 z (by simp)
      · exact h2 z (by simp [hz])
    · obtain ⟨m, hm, h1, h2⟩ := extremum_lt_ints h r x
      refine ⟨m, by simp [hyx, hm], by rcases List.mem_cons.1 h1 with h' | h' <;> simp [h'], ?_⟩
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | rfl | hz
      · exact h2 z (by simp)
      · have := h2 x (by simp); omega
      · exact h2 z (by simp [hz])

theorem extremum_gt_ints (h : IntOps o) : ∀ (r : List Int) (x : Int),
    ∃ m, extremum o.gt (o.ofInt x) (r.map o.ofInt) = .ok (o.ofInt m) ∧ m ∈ x :: r ∧ ∀ y ∈ x :: r, y ≤ m
  | [], x => ⟨x, rfl, by simp, by simp⟩
  | y :: r, x => by
    simp only [List.map_cons, extremum, h.gt_int]
    by_cases hyx : y > x
    · obtain ⟨m, hm, h1, h2⟩ := extremum_gt_ints h r y
      refine ⟨m, by simp [hyx, hm], List.mem_cons_of_mem _ h1, ?_⟩
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | rfl | hz
      · have := h2 y (by simp); omega
      · exact h2 z (by simp)
      · exact h2 z (by simp [hz])
    · obtain ⟨m, hm, h1, h2⟩ := extremum_gt_ints h r x
      refine ⟨m, by simp [hyx, hm], by rcases List.mem_cons.1 h1 with h' | h' <;> simp [h'], ?_⟩
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | rfl | hz
      · exact h2 z (by simp)
      · have := h2 x (by simp); omega
      · exact h2 z (by simp [hz])

theorem map_of_ints (L : List α) (hL : ∀ x ∈ L, ∃ y, x = o.ofInt y) : ∃ l : List Int, L = l.map o.ofInt := by
  induction L with
  | nil => exact ⟨[], rfl⟩
  | cons x r ih =>
    obtain ⟨y, rfl⟩ := hL x (by simp)
    obtain ⟨l, hl⟩ := ih (fun z hz => hL z (by simp [hz]))
    exact ⟨y :: l, by simp [hl]⟩

end Ints

theorem mem_intRange (a b k : Int) : k ∈ intRange a b ↔ a ≤ k ∧ k < b := by
  simp only [intRange, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    omega
  · intro h
    exact ⟨(k - a).toNat, by omega, by omega⟩

/-! ### `verify(CONTINUOUS)` -/

/-- `verify(CONTINUOUS)` on `int` values, for every iteration order of the set and every class of `int`-like values:
on an `Enum` it passes exactly when every integer strictly between the lowest and the highest value is a value; on a
`Flag` exactly when every power of two `2**j` with `_high_bit(low) < j < _high_bit(high)` is a value, the docs' "no missing
values between the lowest-valued member and the highest-valued member". The check runs over every value, not only the
`int` ones: with values `1, 2, 'x'`, `min` compares `'x'` with an `int` and raises `TypeError`. -/
def VerifyContinuousInts : Prop :=
  ∀ (α : Type) (o : Ops α), IntOps o → ∀ (order : List α → List α), (∀ l x, x ∈ order l ↔ x ∈ l) →
    ∀ (s : String) (l : List Int) (lo hi : Int), lo ∈ l → hi ∈ l → (∀ z ∈ l, lo ≤ z ∧ z ≤ hi) →
      (verifyContinuousG o order false s (l.map o.ofInt) = .ok () ↔ ∀ k, lo < k → k < hi → k ∈ l) ∧
      (verifyContinuousG o order true s (l.map o.ofInt) = .ok () ↔
        ∀ j : Nat, intBitLength lo ≤ j → j + 1 < intBitLength hi → (2 : Int) ^ j ∈ l)

theorem verifyContinuousInts_proven : VerifyContinuousInts := by
  intro α o h order hp s l lo hi hlo hhi hb
  have hset : o.setOf (l.map o.ofInt) [] = .ok ((dedupInto [] l).map fun x => (o.ofInt x, ())) := setOf_ints h l []
  have hmem : ∀ z, z ∈ dedupInto [] l ↔ z ∈ l := fun z => by rw [mem_dedupInto]; simp
  generalize dedupInto [] l = dd at hset hmem
  have hfst : (dd.map fun x => (o.ofInt x, ())).map Prod.fst = dd.map o.ofInt := by simp
  have hL : ∀ x ∈ order (dd.map o.ofInt), ∃ y, x = o.ofInt y := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.1 ((hp _ x).1 hx)
    exact ⟨y, rfl⟩
  obtain ⟨l', hl'⟩ := map_of_ints _ hL
  have hl'mem : ∀ z, z ∈ l' ↔ z ∈ l := by
    intro z
    constructor
    · intro hz
      have : o.ofInt z ∈ order (dd.map o.ofInt) := by rw [hl']; exact List.mem_map_of_mem hz
      obtain ⟨w, hw, he⟩ := List.mem_map.1 ((hp _ _).1 this)
      rw [← ofInt_inj h he]
      exact (hmem w).1 hw
    · intro hz
      have : o.ofInt z ∈ order (dd.map o.ofInt) := (hp _ _).2 (List.mem_map_of_mem ((hmem z).2 hz))
      rw [hl'] at this
      obtain ⟨w, hw, he⟩ := List.mem_map.1 this
      rw [← ofInt_inj h he]
      exact hw
  have hfilt : ∀ ps : List Int, (ps.filter fun k => !decide (k ∈ dd)) = [] ↔ ∀ k ∈ ps, k ∈ l := by
    intro ps
    rw [List.filter_eq_nil_iff]
    constructor
    · intro h1 k hk
      have := h1 k hk
      simp only [Bool.not_eq_true', decide_eq_false_iff_not, Classical.not_not] at this
      exact (hmem k).1 this
    · intro h1 k hk
      simp only [Bool.not_eq_true', decide_eq_false_iff_not, Classical.not_not]
      exact (hmem k).2 (h1 k hk)
  by_cases hlen : dd.length < 2
  · have heq : lo = hi := by
      match dd, hmem, hlen with
      | [], hmem, _ => exact absurd ((hmem lo).2 hlo) (by simp)
      | [d], hmem, _ =>
        have h1 := (hmem lo).2 hlo
        have h2 := (hmem hi).2 hhi
        simp only [List.mem_singleton] at h1 h2
        rw [h1, h2]
      | _ :: _ :: _, _, hlen => exact absurd hlen (by simp)
    have hok : ∀ flag, verifyContinuousG o order flag s (l.map o.ofInt) = .ok () := by
      intro flag
      simp only [verifyContinuousG, hset, List.length_map, hlen, ↓reduceIte]
    refine ⟨⟨fun _ k h1 h2 => by omega, fun _ => hok false⟩, ⟨fun _ j h1 h2 => by rw [heq] at h1; omega,
      fun _ => hok true⟩⟩
  · cases l' with
    | nil =>
      exfalso
      have := (hl'mem lo).2 hlo
      simp at this
    | cons y r' =>
      obtain ⟨m, hm, hm1, hm2⟩ := extremum_lt_ints h r' y
      obtain ⟨M, hM, hM1, hM2⟩ := extremum_gt_ints h r' y
      have hmlo : m = lo := by
        have a1 := (hb m ((hl'mem m).1 hm1)).1
        have a2 := hm2 lo ((hl'mem lo).2 hlo)
        omega
      have hMhi : M = hi := by
        have a1 := (hb M ((hl'mem M).1 hM1)).2
        have a2 := hM2 hi ((hl'mem hi).2 hhi)
        omega
      rw [hmlo] at hm
      rw [hMhi] at hM
      have hord : order ((dd.map fun x => (o.ofInt x, ())).map Prod.fst) = o.ofInt y :: r'.map o.ofInt := by
        rw [hfst, hl']
        rfl
      constructor
      · simp only [verifyContinuousG, hset, List.length_map, hlen, ↓reduceIte, hord, hm, hM, Bool.false_eq_true,
          h.succ_int, h.index_int, missingFrom_ints h dd]
        cases hF : (intRange (lo + 1) hi).filter (fun k => !decide (k ∈ dd)) with
        | nil =>
          simp only [true_iff]
          intro k h1 h2
          exact ((hfilt _).1 hF) k ((mem_intRange _ _ _).2 ⟨by omega, h2⟩)
        | cons k ks =>
          simp only [reduceCtorEq, false_iff]
          intro hall
          have hk : k ∈ (intRange (lo + 1) hi).filter (fun k => !decide (k ∈ dd)) := by rw [hF]; simp
          rw [List.mem_filter] at hk
          have hr := (mem_intRange _ _ _).1 hk.1
          have := hall k (by omega) hr.2
          simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hk
          exact hk.2 ((hmem k).2 this)
      · simp only [verifyContinuousG, hset, List.length_map, hlen, ↓reduceIte, hord, hm, hM,
          h.bitLength_int, missingFrom_ints h dd]
        cases hF : ((intRange (intBitLength lo : Int) ((intBitLength hi : Int) - 1)).map
            (fun i => (2 : Int) ^ i.toNat)).filter (fun k => !decide (k ∈ dd)) with
        | nil =>
          simp only [true_iff]
          intro j h1 h2
          apply (hfilt _).1 hF
          rw [List.mem_map]
          exact ⟨(j : Int), (mem_intRange _ _ _).2 ⟨by omega, by omega⟩, by simp⟩
        | cons k ks =>
          simp only [reduceCtorEq, false_iff]
          intro hall
          have hk : k ∈ ((intRange (intBitLength lo : Int) ((intBitLength hi : Int) - 1)).map
              (fun i => (2 : Int) ^ i.toNat)).filter (fun k => !decide (k ∈ dd)) := by rw [hF]; simp
          rw [List.mem_filter, List.mem_map] at hk
          obtain ⟨⟨i, hi', rfl⟩, hk2⟩ := hk
          have hr := (mem_intRange _ _ _).1 hi'
          have := hall i.toNat (by omega) (by omega)
          simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hk2
          exact hk2 ((hmem _).2 this)

/-! ### `Flag._generate_next_value_` -/

private theorem lt_two_pow_bitLength' (n : Nat) : n < 2 ^ bitLength n := by
  unfold bitLength
  split
  · rename_i h; subst h; decide
  · exact Nat.lt_log2_self

/-- `Flag._generate_next_value_`, every path, for every value type: the first value is `start`, or `1` for `None`; then an
empty `last_values` is the `ValueError` of `max`, an exception from a `>` of `max` goes out, an exception from
`bit_length` becomes the `TypeError` of :1450-1451, and otherwise the value is `2 ** bit_length(max)`. On `int`s that is
the least power of two above every value so far, the docs' "the next power of two". The `TypeError` is
`'invalid flag value %r' % last_value` (:1452): an exception of the value's `repr` goes out instead (for `R` with `__gt__`,
no `bit_length` and a `__repr__` raising `ValueError`, `Flag._generate_next_value_('n', 1, 1, [R()])` raises that
`ValueError`), and a tuple value is unpacked (`[(1, R())]` is the `TypeError` "not all arguments converted"). -/
def FlagGenerateG : Prop :=
  ∀ (α : Type) (o : Ops α) (start : Option α) (count : Nat) (last : List α),
    flagGenerateG o start 0 last = .ok (start.getD (o.ofInt 1)) ∧
    (count ≠ 0 → flagGenerateG o start count [] = .error (.valueError "max() iterable argument is empty")) ∧
    (∀ x r, count ≠ 0 →
      (∀ e, extremum o.gt x r = .error e → flagGenerateG o start count (x :: r) = .error e) ∧
      (∀ m, extremum o.gt x r = .ok m →
        (∀ e, o.bitLength m = .error e → o.isInst e "Exception" = true → pyFormat 1 (o.fmtOne m) = .ok () →
          (flagGenerateG o start count (x :: r)).raises "TypeError") ∧
        (∀ e e', o.bitLength m = .error e → o.isInst e "Exception" = true → pyFormat 1 (o.fmtOne m) = .error e' →
          flagGenerateG o start count (x :: r) = .error e') ∧
        (∀ e, o.bitLength m = .error e → o.isInst e "Exception" = false →
          flagGenerateG o start count (x :: r) = .error e) ∧
        (∀ b, o.bitLength m = .ok b → flagGenerateG o start count (x :: r) = .ok (o.ofInt ((2 : Int) ^ b))))) ∧
    (IntOps o → ∀ (i : Nat) (r : List Nat), count ≠ 0 →
      ∃ k : Nat, flagGenerateG o start count ((i :: r).map fun (x : Nat) => o.ofInt (x : Int)) =
          .ok (o.ofInt ((2 ^ k : Nat) : Int)) ∧
        (∀ x ∈ i :: r, x < 2 ^ k) ∧ ∀ j, k = j + 1 → ∃ x ∈ i :: r, 2 ^ j ≤ x)

theorem flagGenerateG_proven : FlagGenerateG := by
  intro α o start count last
  refine ⟨rfl, fun hc => by simp [flagGenerateG, hc], fun x r hc => ⟨fun e he => by simp [flagGenerateG, hc, he],
    fun m hm => ⟨fun e he hx hs => ⟨_, by simp [flagGenerateG, hc, hm, he, hx, hs, withRepr]; rfl, rfl⟩,
      fun e e' he hx hr => by simp [flagGenerateG, hc, hm, he, hx, hr, withRepr],
      fun e he hx => by simp [flagGenerateG, hc, hm, he, hx],
      fun b hb => by simp [flagGenerateG, hc, hm, hb]⟩⟩, ?_⟩
  intro h i r hc
  have hmap : ((i :: r).map fun (x : Nat) => o.ofInt (x : Int)) =
      ((i : Int) :: r.map (fun x : Nat => (x : Int))).map o.ofInt := by simp
  obtain ⟨M, hM, hM1, hM2⟩ := extremum_gt_ints h (r.map (fun x : Nat => (x : Int))) (i : Int)
  have hMn : ∃ Mn : Nat, M = Mn ∧ Mn ∈ i :: r := by
    simp only [List.mem_cons, List.mem_map] at hM1
    rcases hM1 with rfl | ⟨Mn, hMn, rfl⟩
    · exact ⟨i, rfl, by simp⟩
    · exact ⟨Mn, rfl, by simp [hMn]⟩
  obtain ⟨Mn, rfl, hMn⟩ := hMn
  have hle : ∀ x ∈ i :: r, x ≤ Mn := by
    intro x hx
    have : ((x : Nat) : Int) ∈ (i : Int) :: r.map (fun x : Nat => (x : Int)) := by
      simp only [List.mem_cons, List.mem_map] at hx ⊢
      rcases hx with rfl | hx
      · exact .inl rfl
      · exact .inr ⟨x, hx, rfl⟩
    have := hM2 _ this
    omega
  refine ⟨bitLength Mn, ?_, ?_, ?_⟩
  · rw [hmap]
    simp only [List.map_cons, flagGenerateG, hc, ↓reduceIte]
    simp only [hM, h.bitLength_int, intBitLength, Int.natAbs_natCast, Except.ok.injEq]
    congr 1
  · intro x hx
    have := lt_two_pow_bitLength' Mn
    have := hle x hx
    omega
  · intro j hj
    refine ⟨Mn, hMn, ?_⟩
    unfold bitLength at hj
    split at hj
    · omega
    · rename_i hn
      have : j = Mn.log2 := by omega
      rw [this]
      exact Nat.log2_self_le hn

/-! ### `Flag._missing_` under `CONFORM` -/

theorem and_sub_or_left (a b : Nat) : a &&& (a ||| b) = a := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_or]
  cases a.testBit i <;> simp

theorem and_sub_or_right (a b : Nat) : b &&& (a ||| b) = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_or]
  cases b.testBit i <;> simp

theorem and_sub_trans {a b c : Nat} (h1 : a &&& b = a) (h2 : b &&& c = b) : a &&& c = a :=
  calc a &&& c = (a &&& b) &&& c := by rw [h1]
    _ = a &&& (b &&& c) := Nat.and_assoc a b c
    _ = a &&& b := by rw [h2]
    _ = a := h1

theorem foldl_or_sub : ∀ (l : List (String × Nat)) (init : Nat),
    init &&& l.foldl (fun m p => m ||| p.2) init = init ∧
      ∀ p ∈ l, p.2 &&& l.foldl (fun m p => m ||| p.2) init = p.2
  | [], init => ⟨Nat.and_self init, by simp⟩
  | p :: r, init => by
    obtain ⟨h1, h2⟩ := foldl_or_sub r (init ||| p.2)
    simp only [List.foldl_cons]
    refine ⟨and_sub_trans (and_sub_or_left init p.2) h1, ?_⟩
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact and_sub_trans (and_sub_or_right init q.2) h1
    · exact h2 q hq

theorem memberOf_sub (c : FlagCls) {x : Nat} {n : String} (h : c.memberOf x = some n) : x &&& c.flagMask = x := by
  simp only [FlagCls.memberOf, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, _⟩ := h
  have h1 := List.find?_some hp
  have h2 := List.mem_of_find?_eq_some hp
  have : p.2 = x := by simpa using h1
  rw [← this]
  exact (foldl_or_sub c.members 0).2 p h2

theorem lt_of_testBit {n i : Nat} (h : n.testBit i = true) : i < bitLength n := by
  apply Classical.byContradiction
  intro hi
  have : n < 2 ^ i := Nat.lt_of_lt_of_le (lt_two_pow_bitLength' n) (Nat.pow_le_pow_right (by decide) (by omega))
  rw [Nat.testBit_lt_two_pow this] at h
  cases h

theorem andMask_nonneg (v : Int) (m : Nat) (hv : 0 ≤ v) : andMask v m = v.toNat &&& m := by
  unfold andMask
  rw [Int.toNat_emod hv (Int.natCast_nonneg _), Int.toNat_natCast]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow]
  cases hm : m.testBit i
  · simp
  · have := lt_of_testBit hm
    simp [this]

theorem notAnd_sub {fm x : Nat} (h : x &&& fm = x) : notAnd fm x = 0 := by
  unfold notAnd
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.zero_testBit]
  cases hx : x.testBit i
  · simp
  · have hi := lt_of_testBit hx
    have hf : fm.testBit i = true := by
      have := congrArg (fun n => n.testBit i) h
      simp only [Nat.testBit_and, hx, Bool.true_and] at this
      exact this
    simp [hi, hf]

theorem inRange_sub (fm x : Nat) (hle : x ≤ 2 ^ bitLength fm - 1)
    (h0 : x &&& ((2 ^ bitLength fm - 1) ^^^ fm) = 0) : x &&& fm = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and]
  cases hx : x.testBit i
  · simp
  · have hi : i < bitLength fm := by
      apply Classical.byContradiction
      intro hi
      have : x < 2 ^ i := by
        have := Nat.pow_le_pow_right (n := 2) (by decide) (show bitLength fm ≤ i by omega)
        have := Nat.one_le_two_pow (n := bitLength fm)
        omega
      rw [Nat.testBit_lt_two_pow this] at hx
      cases hx
    have := congrArg (fun n => n.testBit i) h0
    simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, hx, Nat.zero_testBit, hi,
      decide_true, Bool.true_and] at this
    cases hf : fm.testBit i
    · rw [hf] at this; simp at this
    · rfl

theorem nameOf_ok (c : FlagCls) (hb : c.boundary ≠ .strict) (value mv al : Nat) :
    ∃ r, c.nameOf value mv al = pure r := by
  have hs : (c.boundary == Boundary.strict) = false := by simpa using hb
  simp only [FlagCls.nameOf, hs, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  repeat' split
  all_goals exact ⟨_, rfl⟩

theorem conform_missing (c : FlagCls) (hb : c.boundary = .conform) (v : Int) (hv : 0 ≤ v) :
    ∃ name, c.missing v = .ok (.flag (v.toNat &&& c.flagMask) name) := by
  have hns : c.boundary ≠ .strict := by rw [hb]; decide
  simp only [FlagCls.missing, FlagCls.missingR, hb]
  split
  · have hx : andMask v c.flagMask &&& c.flagMask = andMask v c.flagMask := by
      simp only [andMask, Nat.and_assoc, Nat.and_self]
    have hun := notAnd_sub hx
    have hnn : ¬ ((andMask v c.flagMask : Int) < 0) := by omega
    obtain ⟨nm, hnm⟩ := nameOf_ok c hns (andMask v c.flagMask) (andMask v c.flagMask &&& c.singlesMask)
      (notAnd c.singlesMask (andMask v c.flagMask))
    simp only [pure_bind, hnn, ↓reduceIte, Int.toNat_natCast, hun, bne_self_eq_false, Bool.false_and,
      Bool.false_eq_true, hnm]
    rw [← andMask_nonneg v _ hv]
    exact ⟨_, rfl⟩
  · rename_i hoob
    have h1 : v ≤ (c.allBits : Int) := by
      apply Classical.byContradiction
      intro hc
      apply hoob
      simp [hc]
    have h2 : andMask v (c.allBits ^^^ c.flagMask) = 0 := by
      apply Classical.byContradiction
      intro hc
      apply hoob
      simp [hc]
    have hsub : v.toNat &&& c.flagMask = v.toNat := by
      rw [andMask_nonneg v _ hv] at h2
      unfold FlagCls.allBits at h1 h2
      exact inRange_sub c.flagMask v.toNat (by omega) h2
    have hnn : ¬ (v < 0) := by omega
    obtain ⟨nm, hnm⟩ := nameOf_ok c hns v.toNat (v.toNat &&& c.singlesMask) (notAnd c.singlesMask v.toNat)
    simp only [pure_bind, hnn, ↓reduceIte, notAnd_sub hsub, bne_self_eq_false, Bool.false_and, Bool.false_eq_true,
      hnm]
    rw [hsub]
    exact ⟨_, rfl⟩

/-- Under `CONFORM`, `F(v)` for an `int` `v ≥ 0` succeeds, and its value is `v & _flag_mask_`: the extra bits are
discarded, whether `v` is out of range or only has a bit no member has. Docs of `FlagBoundary.CONFORM`: "extra bits are
discarded". -/
def ConformKeepsMask : Prop :=
  ∀ (c : FlagCls) (v : Int), c.boundary = .conform → 0 ≤ v →
    ∃ name, c.call v = .ok (.flag (v.toNat &&& c.flagMask) name)

theorem conformKeepsMask_proven : ConformKeepsMask := by
  intro c v hb hv
  unfold FlagCls.call
  simp only [ge_iff_le, hv, ↓reduceIte]
  cases hm : c.memberOf v.toNat with
  | some n =>
    refine ⟨some n, ?_⟩
    simp only [memberOf_sub c hm]
  | none =>
    exact conform_missing c hb v hv

/-! ### `verify(NAMED_FLAGS)` -/

section Named

variable {α : Type} {o : Ops α}

theorem listIn_ints (h : IntOps o) (b : Int) : ∀ l : List Int, o.listIn (o.ofInt b) (l.map o.ofInt) = .ok (decide (b ∈ l))
  | [] => rfl
  | y :: r => by
    have ih := listIn_ints h b r
    simp only [List.map_cons, Ops.listIn, Ops.req]
    by_cases hs : o.same (o.ofInt y) (o.ofInt b) = true
    · have := h.same_int y b hs
      subst this
      simp [hs]
    · simp only [hs, Bool.false_eq_true, ↓reduceIte, h.eq_int]
      by_cases hy : y = b
      · subst hy; simp
      · simp only [hy, decide_false, ih]
        simp [List.mem_cons, Ne.symm hy]

theorem notIn_ints (h : IntOps o) (iv : List Int) : ∀ bs : List Nat,
    o.notIn (iv.map o.ofInt) bs = .ok (bs.filter fun b => !decide ((b : Int) ∈ iv))
  | [] => rfl
  | b :: r => by
    simp only [Ops.notIn, listIn_ints h, notIn_ints h iv r, List.filter_cons]
    by_cases hb : ((b : Int) ∈ iv) <;> simp [hb]

/-- What `NAMED_FLAGS` asks of one entry of `_member_map_` on `int` values. -/
def namedOk (c : EClassG α) (o : Ops α) (iv : List Int) (p : Name × Name) : Prop :=
  c.memberNames.contains p.1 = false → ∀ i, c.values.lookup p.2 = some (o.ofInt i) → 0 ≤ i →
    ∀ b ∈ bitsOf i.toNat, (b : Int) ∈ iv

theorem missedBits_ints (h : IntOps o) (c : EClassG α) (iv : List Int) (hm : c.memberValues = iv.map o.ofInt)
    (hv : ∀ n v, c.values.lookup n = some v → ∃ i, v = o.ofInt i) (p : Name × Name) :
    ∃ L, c.missedBits o p = .ok L ∧ (L = [] ↔ namedOk c o iv p) := by
  unfold EClassG.missedBits namedOk
  by_cases hc : c.memberNames.contains p.1 = true
  · refine ⟨[], by simp only [hc, ↓reduceIte], ?_⟩
    have hc2 := hc
    simp at hc2
    simp [hc2]
  · have hc' : c.memberNames.contains p.1 = false := Bool.eq_false_iff.2 hc
    simp only [hc', Bool.false_eq_true, ↓reduceIte, forall_const]
    cases hl : c.values.lookup p.2 with
    | none => simp
    | some v =>
      obtain ⟨i, rfl⟩ := hv _ _ hl
      simp only [h.lt_int, h.asInt_int, Ops.bitsOfValue, hm, notIn_ints h]
      by_cases hi : i < 0
      · refine ⟨[], by simp [hi], ?_⟩
        simp only [true_iff]
        intro j hj; have := ofInt_inj h (Option.some.inj hj); omega
      · refine ⟨(bitsOf i.toNat).filter fun b => !decide ((b : Int) ∈ iv), by simp [hi], ?_⟩
        rw [List.filter_eq_nil_iff]
        constructor
        · intro hall j hj _ b hb
          rw [← ofInt_inj h (Option.some.inj hj)] at hb
          have := hall b hb
          simpa using this
        · intro hall b hb
          have := hall i rfl (by omega) b hb
          simpa using this

theorem namedLoop_ints (h : IntOps o) (c : EClassG α) (iv : List Int) (hm : c.memberValues = iv.map o.ofInt)
    (hv : ∀ n v, c.values.lookup n = some v → ∃ i, v = o.ofInt i) :
    ∀ l : List (Name × Name), ∃ b, c.namedLoop o l = .ok b ∧ (b = false ↔ ∀ p ∈ l, namedOk c o iv p)
  | [] => ⟨false, rfl, by simp⟩
  | p :: r => by
    obtain ⟨L, hL, hL'⟩ := missedBits_ints h c iv hm hv p
    obtain ⟨b, hb, hb'⟩ := namedLoop_ints h c iv hm hv r
    refine ⟨!L.isEmpty || b, by simp [EClassG.namedLoop, hL, hb], ?_⟩
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff, List.mem_cons, forall_eq_or_imp, hL', hb']

end Named

/-- `verify(NAMED_FLAGS)` on `int` values: it passes exactly when no entry of `_member_map_` that is not in
`_member_names_` and has a value `>= 0` has a bit that no member value equals, the docs' "multi-flag aliases may not
contain unnamed flags". The member values are compared by `==`, so a value equal to an `int` counts (`A = 1, B = 2.0,
C = D = 3` passes); and a value that is not an `int` is compared with `0` first, so `A = 'x'; B = 'x'` raises the
`TypeError` of `'x' < 0` (see `verifyNamed_strAlias`). -/
def VerifyNamedInts : Prop :=
  ∀ (α : Type) (o : Ops α), IntOps o → ∀ (c : EClassG α) (iv : List Int), c.memberValues = iv.map o.ofInt →
    (∀ n v, c.values.lookup n = some v → ∃ i, v = o.ofInt i) →
    (c.verifyNamed o = .ok () ↔ ∀ p ∈ c.memberMap, namedOk c o iv p) ∧
    (c.verifyNamed o = .ok () ∨ (c.verifyNamed o).raises "ValueError")

theorem verifyNamedInts_proven : VerifyNamedInts := by
  intro α o h c iv hm hv
  obtain ⟨b, hb, hb'⟩ := namedLoop_ints h c iv hm hv c.memberMap
  unfold EClassG.verifyNamed
  rw [hb]
  cases b with
  | false => exact ⟨by simp only [true_iff]; exact hb'.1 rfl, .inl rfl⟩
  | true =>
    refine ⟨?_, .inr ⟨_, rfl, rfl⟩⟩
    simp only [reduceCtorEq, false_iff]
    intro hall
    exact Bool.noConfusion (hb'.2 hall)

/-- The earlier rule, which skipped an entry whose value is not an `int`: false, `A = 'x'; B = 'x'` raises the `TypeError`
of `'x' < 0` at :2022, as on 3.15.2. -/
private theorem verifyNamed_strAlias :
    ¬ (∀ c : EClassG EV, c.verifyNamed evOps = .ok () ↔ ∀ p ∈ c.memberMap, c.memberNames.contains p.1 = false →
        ∀ i, c.values.lookup p.2 = some (.atom (.int i)) → ∀ b ∈ bitsOf i.toNat, (b : Int) ∈ c.memberValues.filterMap
          evOps.asInt) := by
  intro h
  have := (h { memberNames := [['A']], memberMap := [(['A'], ['A']), (['B'], ['A'])],
               values := [(['A'], .atom (.str "x"))] }).2 (by
    intro p hp hc i hi
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp at hi)
  revert this
  decide +kernel

/-- A member value equal to an `int` counts for `NAMED_FLAGS`: with `A = 1, B = K(2), C = D = 3`, the bit `2` of the alias
`D` is found by `K(2) == 2`, as `2.0 == 2` is on 3.15.2. -/
private theorem verifyNamed_equalValue :
    ({ memberNames := [['A'], ['B'], ['C']],
       memberMap := [(['A'], ['A']), (['B'], ['B']), (['C'], ['C']), (['D'], ['C'])],
       values := [(['A'], .int 1), (['B'], .key 2 none none 0), (['C'], .int 3)] } : EClassG PV).verifyNamed pvOps =
      .ok () := by
  decide +kernel

/-! ### `Flag._missing_` outside the range -/

/-- The out-of-range test of :1494-1497: outside `~all_bits .. all_bits`, or a bit of `all_bits` no member has. -/
def FlagCls.outOfRange (c : FlagCls) (v : Int) : Bool :=
  !decide (-(c.allBits : Int) - 1 ≤ v ∧ v ≤ (c.allBits : Int)) || andMask v (c.allBits ^^^ c.flagMask) != 0

/-- `Flag._missing_` on an out-of-range `int`, each boundary, :1494-1523: `STRICT` is the `ValueError` "invalid value",
`EJECT` gives back the `int` itself, and `KEEP` never raises: a value `>= 0` keeps every bit, and a negative one becomes
`max(all_bits + 1, 2 ** v.bit_length()) + v`; in range, a negative value under `KEEP` is `all_bits + 1 + v`. So for a
two-bit class `F(8)` is the `ValueError` under `STRICT` and `8` under `EJECT`. -/
def MissingBoundaries : Prop :=
  ∀ (c : FlagCls) (v : Int),
    (c.boundary = .strict → c.outOfRange v = true → (c.missing v).raises "ValueError") ∧
    (c.boundary = .eject → c.outOfRange v = true → c.missing v = .ok (.plain v)) ∧
    (c.boundary = .keep → ∃ name, c.missing v = .ok (.flag (if 0 ≤ v then v.toNat
        else if c.outOfRange v then ((max (c.allBits + 1) (2 ^ bitLength v.natAbs) : Nat) + v).toNat
        else ((c.allBits : Int) + 1 + v).toNat) name))

theorem missingBoundaries_proven : MissingBoundaries := by
  intro c v
  refine ⟨fun hb ho => ?_, fun hb ho => ?_, fun hb => ?_⟩
  · unfold FlagCls.outOfRange at ho
    simp only [FlagCls.missing, FlagCls.missingR, hb, ho, ↓reduceIte]
    exact ⟨_, rfl, rfl⟩
  · unfold FlagCls.outOfRange at ho
    simp only [FlagCls.missing, FlagCls.missingR, hb, ho, ↓reduceIte]
    rfl
  · have hns : c.boundary ≠ .strict := by rw [hb]; decide
    simp only [FlagCls.missing, FlagCls.missingR, hb]
    by_cases ho : c.outOfRange v = true
    · have ho' := ho
      unfold FlagCls.outOfRange at ho'
      simp only [ho', ↓reduceIte]
      by_cases hv : v < 0
      · have hpos : 0 ≤ ((max (c.allBits + 1) (2 ^ bitLength v.natAbs) : Nat) : Int) + v := by
          have h1 := lt_two_pow_bitLength' v.natAbs
          have h2 : 2 ^ bitLength v.natAbs ≤ max (c.allBits + 1) (2 ^ bitLength v.natAbs) := Nat.le_max_right _ _
          omega
        have hnn : ¬ (((max (c.allBits + 1) (2 ^ bitLength v.natAbs) : Nat) : Int) + v < 0) := by omega
        obtain ⟨nm, hnm⟩ := nameOf_ok c hns
          (((max (c.allBits + 1) (2 ^ bitLength v.natAbs) : Nat) : Int) + v).toNat
          ((((max (c.allBits + 1) (2 ^ bitLength v.natAbs) : Nat) : Int) + v).toNat &&& c.singlesMask)
          (notAnd c.singlesMask (((max (c.allBits + 1) (2 ^ bitLength v.natAbs) : Nat) : Int) + v).toNat)
        simp only [hv, ↓reduceIte, pure_bind, hnn, ne_eq, reduceCtorEq, not_false_eq_true, bne_self_eq_false,
          Bool.and_false, Bool.false_eq_true, hnm, Bool.and_true, decide_true]
        simp only [show ¬ (0 ≤ v) by omega, ↓reduceIte, ho]
        exact ⟨_, rfl⟩
      · have hnn : ¬ (v < 0) := hv
        obtain ⟨nm, hnm⟩ := nameOf_ok c hns v.toNat (v.toNat &&& c.singlesMask) (notAnd c.singlesMask v.toNat)
        simp only [hv, ↓reduceIte, pure_bind, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, false_or, or_true, hnm]
        simp only [show 0 ≤ v by omega, ↓reduceIte]
        exact ⟨_, rfl⟩
    · have ho' : (!decide (-(c.allBits : Int) - 1 ≤ v ∧ v ≤ (c.allBits : Int)) ||
          andMask v (c.allBits ^^^ c.flagMask) != 0) = false := by
        unfold FlagCls.outOfRange at ho; simpa using ho
      simp only [ho', Bool.false_eq_true, ↓reduceIte, pure_bind]
      by_cases hv : v < 0
      · have hk : Boundary.keep = Boundary.eject ∨ Boundary.keep = Boundary.keep := .inr rfl
        obtain ⟨nm, hnm⟩ := nameOf_ok c hns ((c.allBits : Int) + 1 + v).toNat
          (((c.allBits : Int) + 1 + v).toNat &&& c.singlesMask) (notAnd c.singlesMask ((c.allBits : Int) + 1 + v).toNat)
        simp only [hv, ↓reduceIte, pure_bind, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, false_or, or_true, hnm]
        simp only [show ¬ (0 ≤ v) by omega, ↓reduceIte, ho]
        exact ⟨_, rfl⟩
      · obtain ⟨nm, hnm⟩ := nameOf_ok c hns v.toNat (v.toNat &&& c.singlesMask) (notAnd c.singlesMask v.toNat)
        simp only [hv, ↓reduceIte, pure_bind, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, false_or, or_true, hnm]
        simp only [show 0 ≤ v by omega, ↓reduceIte]
        exact ⟨_, rfl⟩

/-! ### `Flag._missing_` in range, and the names of pseudo-members -/

/-- The only exception of the name loop, :1541-1560, is the `STRICT` one of :1557, "no members with value". -/
theorem nameOf_error (c : FlagCls) (value mv al : Nat) (e : PyExc) (h : c.nameOf value mv al = .error e) :
    c.boundary = .strict ∧ ∃ u : Nat, e = .valueError s!"~no members with value {u}" := by
  by_cases hb : c.boundary = .strict
  · refine ⟨hb, ?_⟩
    simp only [FlagCls.nameOf] at h
    repeat' split at h
    all_goals first | exact ⟨_, (Except.error.inj h).symm⟩ | cases h
  · obtain ⟨r, hr⟩ := nameOf_ok c hb value mv al
    rw [hr] at h
    cases h

/-- `Flag._missing_` on an `int` `>= 0` in range, any boundary: the value is kept exactly and the name is the name loop's,
:1541-1560 (a member of that value wins, :1566); the loop's only exception is the `STRICT` "no members with value" of
:1557, and with no member bit and no alias bit the name is `None`. So `F(3)` of `A = 1, B = 2` under `STRICT` is the
pseudo-member `(3, 'A|B')`, `F(9)` under `KEEP` is `(9, 'A|8')`, and `F(3)` of `A = 1, X = 6` under `STRICT` is the
`ValueError` "no members with value 2", all as on 3.15.2. -/
def MissingInRange : Prop :=
  (∀ (c : FlagCls) (v : Int), c.outOfRange v = false → 0 ≤ v →
    c.missing v = (c.nameOf v.toNat (v.toNat &&& c.singlesMask) (notAnd c.singlesMask v.toNat)).map
      (fun nm => .flag v.toNat (match c.memberOf v.toNat with
        | some n => some n
        | none => nm))) ∧
  (∀ (c : FlagCls) (value : Nat), c.nameOf value 0 0 = .ok none) ∧
  (∀ (c : FlagCls) (value mv al : Nat), c.boundary ≠ .strict → ∃ r, c.nameOf value mv al = .ok r) ∧
  (∀ (c : FlagCls) (value mv al : Nat) (e : PyExc), c.nameOf value mv al = .error e →
    c.boundary = .strict ∧ ∃ u : Nat, e = .valueError s!"~no members with value {u}") ∧
  FlagCls.call ⟨"F", [("A", 1), ("B", 2)], .strict⟩ 3 = .ok (.flag 3 (some "A|B")) ∧
  FlagCls.call ⟨"F", [("A", 1), ("B", 2)], .keep⟩ 9 = .ok (.flag 9 (some "A|8")) ∧
  FlagCls.call ⟨"F", [("A", 1), ("X", 6)], .strict⟩ 3 = .error (.valueError "~no members with value 2")

theorem missingInRange_proven : MissingInRange := by
  refine ⟨?_, fun c value => by simp [FlagCls.nameOf], fun c value mv al hb => nameOf_ok c hb value mv al,
    nameOf_error, by decide +kernel, by decide +kernel, by decide +kernel⟩
  intro c v ho hv
  have ho' : (!decide (-(c.allBits : Int) - 1 ≤ v ∧ v ≤ (c.allBits : Int)) ||
      andMask v (c.allBits ^^^ c.flagMask) != 0) = false := by
    unfold FlagCls.outOfRange at ho; simpa using ho
  have h1 : v ≤ (c.allBits : Int) := by
    apply Classical.byContradiction
    intro hc
    simp [hc] at ho'
  have h2 : andMask v (c.allBits ^^^ c.flagMask) = 0 := by
    apply Classical.byContradiction
    intro hc
    simp [hc] at ho'
  have hsub : v.toNat &&& c.flagMask = v.toNat := by
    rw [andMask_nonneg v _ hv] at h2
    unfold FlagCls.allBits at h1 h2
    exact inRange_sub c.flagMask v.toNat (by omega) h2
  have hnn : ¬ (v < 0) := by omega
  simp only [FlagCls.missing, FlagCls.missingR, ho', Bool.false_eq_true, ↓reduceIte, pure_bind, hnn, notAnd_sub hsub,
    bne_self_eq_false, Bool.false_and]
  generalize c.nameOf _ _ _ = x
  cases x <;> rfl

/-! ### `verify(CONTINUOUS)` on values that do not compare -/

/-- `verify(CONTINUOUS)` raises what building the set raises, and what `min` raises: with values `1, 2, 'x'` that is the
`TypeError` of `<`, whose operands are in the order the set is iterated, which depends on the hash seed: iterated as
`1, 2, 'x'` it is "'<' not supported between instances of 'str' and 'int'" (PYTHONHASHSEED=0 on 3.15.2), iterated as
`'x', 2, 1` it is "... 'int' and 'str'" (PYTHONHASHSEED=1). -/
def ContinuousErrors : Prop :=
  (∀ (α : Type) (o : Ops α) (order : List α → List α) (flag : Bool) (s : String) (vals : List α) (e : PyExc),
    o.setOf vals [] = .error e → verifyContinuousG o order flag s vals = .error e) ∧
  (∀ (α : Type) (o : Ops α) (order : List α → List α) (flag : Bool) (s : String) (vals : List α)
    (st : List (α × Unit)) (x : α) (r : List α) (e : PyExc), o.setOf vals [] = .ok st → ¬ st.length < 2 →
    order (st.map Prod.fst) = x :: r → extremum o.lt x r = .error e → verifyContinuousG o order flag s vals = .error e) ∧
  verifyContinuousG evOps id false "C" [.atom (.int 1), .atom (.int 2), .atom (.str "x")] =
    .error (.typeError "'<' not supported between instances of 'str' and 'int'") ∧
  verifyContinuousG evOps (fun l => l.rotateRight 1) false "C" [.atom (.int 1), .atom (.int 2), .atom (.str "x")] =
    .error (.typeError "'<' not supported between instances of 'int' and 'str'")

theorem continuousErrors_proven : ContinuousErrors := by
  refine ⟨fun α o order flag s vals e h => by simp [verifyContinuousG, h],
    fun α o order flag s vals st x r e h hl ho he => by simp [verifyContinuousG, h, hl, ho, he], by decide +kernel,
    by decide +kernel⟩

/-- The earlier `FlagGenerateG` clause, an `Exception` from `bit_length` gives the `TypeError`: false when the value's
`__repr__` raises, as `%r` runs it (:1452). -/
private theorem flagGenerate_reprRaises :
    ¬ (∀ (α : Type) (o : Ops α) (start : Option α) (count : Nat) (x : α) (r : List α) (m : α) (e : PyExc),
        count ≠ 0 → extremum o.gt x r = .ok m → o.bitLength m = .error e → o.isInst e "Exception" = true →
        (flagGenerateG o start count (x :: r)).raises "TypeError") := by
  intro h
  obtain ⟨e, he, hc⟩ := h PV pvOps (some (.int 1)) 1 (.robj "ValueError" 0) [] (.robj "ValueError" 0)
    (.named "AttributeError" "'RObj' object has no attribute 'bit_length'") (by decide) rfl rfl (by decide +kernel)
  have : flagGenerateG pvOps (some (.int 1)) 1 [.robj "ValueError" 0] = .error (.valueError "repr") := by decide +kernel
  rw [this] at he
  cases he
  simp [PyExc.className] at hc

/-- `[(1, R())]`: the tuple is unpacked by the `%` of :1452, so the `TypeError` "not all arguments converted", not the
`KeyError` of `R.__repr__`, as on 3.15.2. -/
private theorem flagGenerate_tuple :
    flagGenerateG pvOps (some (.int 1)) 1 [.pair 1 "KeyError"] =
      .error (.typeError "not all arguments converted during string formatting (required 1, got 2)") := by
  decide +kernel

/-! ### `Flag._missing_`: the repr of an out-of-range value, the name loop, negative values -/

/-- `Flag._missing_` under `STRICT` on an out-of-range value formats it with `%r` (:1501), so the `repr` of an `int`
subclass that raises goes out instead of the `ValueError`. -/
def MissingStrictRepr : Prop :=
  ∀ (c : FlagCls) (v : Int) (e : PyExc) (s : String), c.boundary = .strict → c.outOfRange v = true →
    c.missingR (.error e) v = .error e ∧ (c.missingR (.ok s) v).raises "ValueError"

theorem missingStrictRepr_proven : MissingStrictRepr := by
  intro c v e s hb ho
  unfold FlagCls.outOfRange at ho
  refine ⟨?_, ?_⟩
  · simp only [FlagCls.missingR, hb, ho, ↓reduceIte]
    rfl
  · simp only [FlagCls.missingR, hb, ho, ↓reduceIte]
    exact ⟨_, rfl, rfl⟩

/-- The members the name loop collects, :1541-1552: with no alias bit, exactly those of `_iter_member_(member_value)`;
with alias bits, those and every canonical member with a nonzero value inside `member_value | aliases` (the loop of
:1547-1552), and nothing else. The name is theirs joined with `|`, plus `|unknown` for bits none of them has, except that
no bit at all is `None` and unknown bits under `STRICT` are the :1557 error. So `A = 1, X = 6` under `STRICT` gives
`F(7) = (7, 'A|X')`: the alias loop finds `X`. -/
def NameLoop : Prop :=
  (∀ (c : FlagCls) (mv : Nat), c.nameMembers mv 0 = (c.iterMembers mv).filterMap id) ∧
  (∀ (c : FlagCls) (mv al : Nat), al ≠ 0 → ∀ p ∈ c.canonical, p.2 ≠ 0 → p.2 &&& (mv ||| al) = p.2 →
    p ∈ c.nameMembers mv al) ∧
  (∀ (c : FlagCls) (mv al : Nat), al ≠ 0 → ∀ p ∈ c.nameMembers mv al,
    p ∈ (c.iterMembers mv).filterMap id ∨ (p ∈ c.canonical ∧ p.2 ≠ 0 ∧ p.2 &&& (mv ||| al) = p.2)) ∧
  (∀ (c : FlagCls) (value mv al : Nat), (mv != 0 || al != 0) = true →
    c.nameOf value mv al =
      let all := c.nameMembers mv al
      let combined := all.foldl (fun m p => m ||| p.2) 0
      let unknown := (if al != 0 then mv ||| al else value) ^^^ combined
      if combined == 0 then .ok none
      else if unknown != 0 && c.boundary == .strict then .error (.valueError s!"~no members with value {unknown}")
      else if unknown != 0 then .ok (some s!"{"|".intercalate (all.map Prod.fst)}|{unknown}")
      else .ok (some ("|".intercalate (all.map Prod.fst)))) ∧
  FlagCls.call ⟨"F", [("A", 1), ("X", 6)], .strict⟩ 7 = .ok (.flag 7 (some "A|X"))

theorem nameLoop_proven : NameLoop := by
  refine ⟨fun c mv => by simp [FlagCls.nameMembers], fun c mv al hal p hp h0 hs => ?_, fun c mv al hal p hp => ?_,
    fun c value mv al h => by simp only [FlagCls.nameOf, h, ↓reduceIte], by decide +kernel⟩
  · have hal' : (al != 0) = true := by simpa using hal
    simp only [FlagCls.nameMembers, hal', ↓reduceIte, List.mem_append, List.mem_filter]
    by_cases hf : p ∈ (c.iterMembers mv).filterMap id
    · exact .inl hf
    · refine .inr ⟨hp, ?_⟩
      simp [hf, h0, hs]
  · have hal' : (al != 0) = true := by simpa using hal
    simp only [FlagCls.nameMembers, hal', ↓reduceIte, List.mem_append, List.mem_filter] at hp
    rcases hp with hp | ⟨hp, hq⟩
    · exact .inl hp
    · refine .inr ⟨hp, ?_, ?_⟩ <;> simp at hq <;> simp [hq]

/-- `Flag._missing_` on a negative `int` in range, :1518-1524: under `EJECT` and `KEEP` it becomes `all_bits + 1 + value`,
and under `STRICT` and `CONFORM` `singles_mask & value`; then the unknown-bits test (skipped under `KEEP`) and the name
loop. So `F(-1)` of `A = 1, B = 2` is `(3, 'A|B')` under `STRICT` and under `EJECT`, and `G(-2)` of `A = 1, X = 6` under
`STRICT` is `(0, None)`. -/
def MissingNegative : Prop :=
  (∀ (c : FlagCls) (v : Int), c.outOfRange v = false → v < 0 →
    let v2 : Nat := (if c.boundary = .eject ∨ c.boundary = .keep then (c.allBits : Int) + 1 + v
      else (andMask v c.singlesMask : Int)).toNat
    c.missing v =
      if (notAnd c.flagMask v2 != 0 && c.boundary != .keep) = true then .error (.valueError "~unknown values")
      else (c.nameOf v2 (v2 &&& c.singlesMask) (notAnd c.singlesMask v2)).map
        (fun nm => .flag v2 (match c.memberOf v2 with
          | some n => some n
          | none => nm))) ∧
  FlagCls.call ⟨"F", [("A", 1), ("B", 2)], .strict⟩ (-1) = .ok (.flag 3 (some "A|B")) ∧
  FlagCls.call ⟨"F", [("A", 1), ("B", 2)], .eject⟩ (-1) = .ok (.flag 3 (some "A|B")) ∧
  FlagCls.call ⟨"G", [("A", 1), ("X", 6)], .strict⟩ (-2) = .ok (.flag 0 none)

theorem missingNegative_proven : MissingNegative := by
  refine ⟨?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
  intro c v ho hv
  have ho' : (!decide (-(c.allBits : Int) - 1 ≤ v ∧ v ≤ (c.allBits : Int)) ||
      andMask v (c.allBits ^^^ c.flagMask) != 0) = false := by
    unfold FlagCls.outOfRange at ho; simpa using ho
  simp only [FlagCls.missing, FlagCls.missingR, ho', Bool.false_eq_true, ↓reduceIte, pure_bind, hv]
  split
  · rfl
  · generalize c.nameOf _ _ _ = x
    cases x <;> rfl

end PyLean.CoreLibs.EnumDC
