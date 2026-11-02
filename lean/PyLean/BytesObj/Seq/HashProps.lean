import PyLean.BytesObj.Seq.TupleModel

/-!
Properties of `tuple_hash`, in exact 64-bit arithmetic: the value of `hash(())`,
that `-1` is never returned, that the cache is stable, and that each round is a
bijection, so two tuples of equal length that differ in exactly one element's
hash have different raw accumulators.
-/

namespace PyLean.BytesObj.Seq

open PyLean

/-- `XXP1 * 614540362697595703 ≡ 1 (mod 2^64)`. -/
private def XXP1inv : Nat := 614540362697595703
/-- `XXP2 * 839798700976720815 ≡ 1 (mod 2^64)`. -/
private def XXP2inv : Nat := 839798700976720815

private theorem U64_pos : 0 < U64 := by decide

/-- Multiplication by a unit modulo `2^64` can be undone. -/
private theorem mul_cancel (P Q x : Nat) (h : P * Q % U64 = 1) (hx : x < U64) :
    ((x * P) % U64 * Q) % U64 = x := by
  have h1 : ((x * P) % U64 * Q) % U64 = (x * (P * Q)) % U64 := by
    rw [Nat.mul_mod ((x * P) % U64) Q, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  rw [h1, Nat.mul_mod, h, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hx]

private theorem mulP1_inj {x y : Nat} (hx : x < U64) (hy : y < U64)
    (h : (x * XXP1) % U64 = (y * XXP1) % U64) : x = y := by
  have hc : XXP1 * XXP1inv % U64 = 1 := by decide
  rw [← mul_cancel XXP1 XXP1inv x hc hx, ← mul_cancel XXP1 XXP1inv y hc hy, h]

private theorem mulP2_inj {x y : Nat} (hx : x < U64) (hy : y < U64)
    (h : (x * XXP2) % U64 = (y * XXP2) % U64) : x = y := by
  have hc : XXP2 * XXP2inv % U64 = 1 := by decide
  rw [← mul_cancel XXP2 XXP2inv x hc hx, ← mul_cancel XXP2 XXP2inv y hc hy, h]

/-- The rotation written with `+`: the two fields do not overlap. -/
theorem xxRotate_eq (x : Nat) (hx : x < U64) :
    xxRotate x = 2 ^ 31 * (x % 2 ^ 33) + x / 2 ^ 33 := by
  have hb : x / 2 ^ 33 < 2 ^ 31 := by
    have : x < 2 ^ 64 := hx
    omega
  have hor := Nat.two_pow_add_eq_or_of_lt (i := 31) hb (x % 2 ^ 33)
  have hshl : (x <<< 31) % U64 = 2 ^ 31 * (x % 2 ^ 33) := by
    rw [Nat.shiftLeft_eq]
    show (x * 2 ^ 31) % 2 ^ 64 = _
    omega
  unfold xxRotate
  rw [hshl, Nat.shiftRight_eq_div_pow, hor]

theorem xxRotate_lt (x : Nat) (hx : x < U64) : xxRotate x < U64 := by
  rw [xxRotate_eq x hx]
  have : x < 2 ^ 64 := hx
  show _ < 2 ^ 64
  omega

theorem xxRotate_inj {x y : Nat} (hx : x < U64) (hy : y < U64) (h : xxRotate x = xxRotate y) :
    x = y := by
  rw [xxRotate_eq x hx, xxRotate_eq y hy] at h
  have h1 : x < 2 ^ 64 := hx
  have h2 : y < 2 ^ 64 := hy
  omega

theorem hashRound_lt (acc lane : Nat) : hashRound acc lane < U64 :=
  Nat.mod_lt _ U64_pos

/-- A round is injective in the accumulator. -/
theorem hashRound_inj_acc {a b lane : Nat} (ha : a < U64) (hb : b < U64)
    (h : hashRound a lane = hashRound b lane) : a = b := by
  unfold hashRound at h
  simp only at h
  have h1 := mulP1_inj (xxRotate_lt _ (Nat.mod_lt _ U64_pos)) (xxRotate_lt _ (Nat.mod_lt _ U64_pos)) h
  have h2 := xxRotate_inj (Nat.mod_lt _ U64_pos) (Nat.mod_lt _ U64_pos) h1
  have k := lane * XXP2
  generalize lane * XXP2 = c at h2
  have ha' : a < 2 ^ 64 := ha
  have hb' : b < 2 ^ 64 := hb
  have h3 : (a + c) % 2 ^ 64 = (b + c) % 2 ^ 64 := h2
  omega

/-- A round is injective in the lane, for lanes that are `Py_uhash_t`s. -/
theorem hashRound_inj_lane {acc x y : Nat} (hx : x < U64) (hy : y < U64)
    (h : hashRound acc x = hashRound acc y) : x = y := by
  unfold hashRound at h
  simp only at h
  have h1 := mulP1_inj (xxRotate_lt _ (Nat.mod_lt _ U64_pos)) (xxRotate_lt _ (Nat.mod_lt _ U64_pos)) h
  have h2 := xxRotate_inj (Nat.mod_lt _ U64_pos) (Nat.mod_lt _ U64_pos) h1
  apply mulP2_inj hx hy
  generalize x * XXP2 = c at h2 ⊢
  generalize y * XXP2 = d at h2 ⊢
  have h3 : (acc + c) % 2 ^ 64 = (acc + d) % 2 ^ 64 := h2
  show c % 2 ^ 64 = d % 2 ^ 64
  omega

/-- The rounds over a list of lanes. -/
def hashRounds (lanes : List Nat) (acc : Nat) : Nat := lanes.foldl hashRound acc

theorem hashRounds_nil (acc : Nat) : hashRounds [] acc = acc := by
  simp [hashRounds]

theorem hashRounds_cons (x : Nat) (xs : List Nat) (acc : Nat) :
    hashRounds (x :: xs) acc = hashRounds xs (hashRound acc x) := by
  simp [hashRounds]

theorem hashRounds_lt (lanes : List Nat) (acc : Nat) (h : acc < U64) : hashRounds lanes acc < U64 := by
  induction lanes generalizing acc with
  | nil => rw [hashRounds_nil]; exact h
  | cons x xs ih => rw [hashRounds_cons]; exact ih _ (hashRound_lt _ _)

theorem hashRounds_inj (lanes : List Nat) {a b : Nat} (ha : a < U64) (hb : b < U64)
    (h : hashRounds lanes a = hashRounds lanes b) : a = b := by
  induction lanes generalizing a b with
  | nil => rw [hashRounds_nil, hashRounds_nil] at h; exact h
  | cons x xs ih =>
    rw [hashRounds_cons, hashRounds_cons] at h
    exact hashRound_inj_acc ha hb (ih (hashRound_lt _ _) (hashRound_lt _ _) h)

theorem hashLoop_ok_map {α : Type} (hashE : α → Py Int) (lanes : α → Int) (xs : List α) (acc : Nat)
    (h : ∀ x ∈ xs, hashE x = .ok (lanes x)) :
    hashLoop hashE xs acc = .ok (hashRounds (xs.map (fun x => toUhash (lanes x))) acc) := by
  induction xs generalizing acc with
  | nil => simp [hashLoop, hashRounds_nil]
  | cons x xs ih =>
    have hx := h x (by simp)
    simp only [hashLoop, hx, List.map_cons, hashRounds_cons]
    exact ih _ (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem toUhash_lt (x : Int) : toUhash x < U64 := by
  unfold toUhash
  have h1 : (0 : Int) ≤ x % (U64 : Int) := Int.emod_nonneg _ (by decide)
  have h2 : x % (U64 : Int) < (U64 : Int) := Int.emod_lt_of_pos _ (by decide)
  omega

theorem toUhash_minus_one : toUhash (-1) = U64 - 1 := by decide

/-- `hashFinish` is below `2^64` and is never `(Py_uhash_t)-1`. -/
theorem hashFinish_spec (acc len : Nat) : hashFinish acc len < U64 ∧ hashFinish acc len ≠ U64 - 1 := by
  unfold hashFinish
  simp only
  have h : (acc + (len ^^^ (XXP5 ^^^ 3527539))) % U64 < U64 := Nat.mod_lt _ U64_pos
  generalize (acc + (len ^^^ (XXP5 ^^^ 3527539))) % U64 = y at h
  have hU : U64 = 18446744073709551616 := by decide
  split
  · rw [hU]; omega
  · rename_i hy; rw [hU] at hy h ⊢; omega

theorem toHash_ne_minus_one {x : Nat} (h : x < U64) (h' : x ≠ U64 - 1) : toHash x ≠ -1 := by
  unfold toHash
  have hU : U64 = 18446744073709551616 := by decide
  rw [hU] at h h' ⊢
  split <;> omega

/-! ## The properties -/

/-- `hash(())` for every element type: the value of `_PyTuple_HASH_EMPTY`
(pycore_tuple.h:76), `5740354900026072187`, the historical hash of the empty
tuple that line 346 of tupleobject.c mangles the length to keep. -/
def TupleHashEmpty : Prop :=
  ∀ (α : Type) (hashE : α → Py Int) (t : Tup α), t.items = [] → t.hash = -1 →
    (tupleHash hashE t).map (·.1) = .ok 5740354900026072187

theorem tupleHashEmpty_proven : TupleHashEmpty := by
  intro α hashE t h1 h2
  have hm1 : toUhash t.hash = U64 - 1 := by rw [h2]; exact toUhash_minus_one
  have hval : toHash (hashFinish XXP5 0) = 5740354900026072187 := by decide
  unfold tupleHash
  rw [if_neg (by rw [hm1]; simp), h1]
  simp only [hashLoop, List.length_nil, hval]
  rfl

/-- For every element type and every tuple whose hash is not cached yet: a
successful `hash(t)` returns a value other than `-1` (the C error marker and the
"not computed" cache marker), stores it in `ob_hash`, and leaves the items alone.
`-1` in `ob_hash` being "no cached hash" is the type invariant of a fresh tuple. -/
def TupleHashNotMinusOne : Prop :=
  ∀ (α : Type) (hashE : α → Py Int) (t t' : Tup α) (h : Int),
    t.hash = -1 → tupleHash hashE t = .ok (h, t') →
      h ≠ -1 ∧ t'.hash = h ∧ t'.items = t.items

theorem tupleHashNotMinusOne_proven : TupleHashNotMinusOne := by
  intro α hashE t t' h h1 hr
  have hm1 : toUhash t.hash = U64 - 1 := by rw [h1]; exact toUhash_minus_one
  unfold tupleHash at hr
  rw [if_neg (by rw [hm1]; simp)] at hr
  cases hl : hashLoop hashE t.items XXP5 with
  | error e => rw [hl] at hr; simp at hr
  | ok acc =>
    rw [hl] at hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨h2, h3⟩ := hr
    obtain ⟨hlt, hne⟩ := hashFinish_spec acc t.items.length
    subst h2
    subst h3
    exact ⟨toHash_ne_minus_one hlt hne, rfl, rfl⟩

/-- The cache: after a successful `hash(t)`, every later `hash(t)` returns the same
value without asking the elements at all, so it cannot fail and cannot change,
even if an element's `__hash__` has since changed or would raise. A failed
`hash(t)` caches nothing (the model has no result object to carry a cache). -/
def TupleHashCached : Prop :=
  ∀ (α : Type) (hashE hashE' : α → Py Int) (t t' : Tup α) (h : Int),
    t.hash = -1 → tupleHash hashE t = .ok (h, t') → tupleHash hashE' t' = .ok (h, t')

theorem tupleHashCached_proven : TupleHashCached := by
  intro α hashE hashE' t t' h h1 hr
  obtain ⟨hne, hc, _⟩ := tupleHashNotMinusOne_proven α hashE t t' h h1 hr
  have hbound : (-(2 : Int) ^ 63) ≤ h ∧ h < 2 ^ 63 := by
    unfold tupleHash at hr
    have hm1 : toUhash t.hash = U64 - 1 := by rw [h1]; exact toUhash_minus_one
    rw [if_neg (by rw [hm1]; simp)] at hr
    cases hl : hashLoop hashE t.items XXP5 with
    | error e => rw [hl] at hr; simp at hr
    | ok acc =>
      rw [hl] at hr
      simp only [Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨h2, _⟩ := hr
      have hlt := (hashFinish_spec acc t.items.length).1
      subst h2
      generalize hashFinish acc t.items.length = y at hlt
      have hU : U64 = 18446744073709551616 := by decide
      unfold toHash
      rw [hU] at hlt ⊢
      split <;> omega
  have hne' : toUhash t'.hash ≠ U64 - 1 := by
    rw [hc]
    unfold toUhash
    have hU : U64 = 18446744073709551616 := by decide
    rw [hU]
    omega
  unfold tupleHash
  rw [if_pos hne', hc]

/-- Each round of the hash is a bijection. For two lists of lanes that differ in
one position, with all `Py_uhash_t` values, the accumulators after the loop
differ, whichever position it is and whatever the rest holds: tuples of the same
length that differ in exactly one element's hash never collide in the loop.
The last step keeps that, except for the single remap of `-1` to `1546275796`
(tupleobject.c:407-409), which `hash` needs for the error marker: equal hashes
mean that one accumulator hit `-1` and the other `1546275796`. -/
def TupleHashOneLane : Prop :=
  ∀ (pre post : List Nat) (x y acc n : Nat), x < U64 → y < U64 → acc < U64 → x ≠ y →
    let a := hashRounds (pre ++ x :: post) acc
    let b := hashRounds (pre ++ y :: post) acc
    a ≠ b ∧
      (hashFinish a n = hashFinish b n →
        hashFinish a n = 1546275796 ∧
          ((a + (n ^^^ (XXP5 ^^^ 3527539))) % U64 = U64 - 1 ∨
            (b + (n ^^^ (XXP5 ^^^ 3527539))) % U64 = U64 - 1))

theorem hashRounds_append (l r : List Nat) (acc : Nat) :
    hashRounds (l ++ r) acc = hashRounds r (hashRounds l acc) := by
  simp [hashRounds, List.foldl_append]

theorem tupleHashOneLane_proven : TupleHashOneLane := by
  intro pre post x y acc n hx hy hacc hxy
  have hp := hashRounds_lt pre acc hacc
  have hne : hashRounds (pre ++ x :: post) acc ≠ hashRounds (pre ++ y :: post) acc := by
    intro h
    rw [hashRounds_append, hashRounds_append, hashRounds_cons, hashRounds_cons] at h
    have h1 : hashRound (hashRounds pre acc) x = hashRound (hashRounds pre acc) y :=
      hashRounds_inj post (hashRound_lt _ _) (hashRound_lt _ _) h
    exact hxy (hashRound_inj_lane hx hy h1)
  have ha : hashRounds (pre ++ x :: post) acc < U64 := hashRounds_lt _ _ hacc
  have hb : hashRounds (pre ++ y :: post) acc < U64 := hashRounds_lt _ _ hacc
  intro a b
  refine ⟨hne, ?_⟩
  intro h
  have ha' : a < U64 := ha
  have hb' : b < U64 := hb
  have hne' : a ≠ b := hne
  clear_value a b
  unfold hashFinish at h ⊢
  simp only at h ⊢
  generalize n ^^^ (XXP5 ^^^ 3527539) = k at h ⊢
  have hU : U64 = 18446744073709551616 := by decide
  have hr : (a + k) % U64 ≠ (b + k) % U64 := by rw [hU] at ha' hb' ⊢; omega
  generalize hra : (a + k) % U64 = ra at h hr ⊢
  generalize hrb : (b + k) % U64 = rb at h hr ⊢
  by_cases h1 : ra = U64 - 1
  · by_cases h2 : rb = U64 - 1
    · exact absurd (h1.trans h2.symm) hr
    · simp only [if_pos h1, if_neg h2] at h
      exact ⟨by rw [if_pos h1], Or.inl h1⟩
  · by_cases h2 : rb = U64 - 1
    · simp only [if_neg h1, if_pos h2] at h
      exact ⟨by rw [if_neg h1]; exact h, Or.inr h2⟩
    · simp only [if_neg h1, if_neg h2] at h
      exact absurd h hr

/-- The stack test of `tuple_hash`: it comes after the cache, and a tuple that passes it hashes as
`tupleHash` does; otherwise the `RecursionError` leaves the cache alone, so a later call can succeed. -/
def TupleHashGuard : Prop :=
  ∀ (α : Type) (hashE : α → Py Int) (t : Tup α),
    tupleHashGuarded hashE t false = tupleHash hashE t ∧
    (toUhash t.hash ≠ U64 - 1 → tupleHashGuarded hashE t true = .ok (t.hash, t)) ∧
    (toUhash t.hash = U64 - 1 → tupleHashGuarded hashE t true =
      .error (.named "RecursionError" "~Stack overflow while hashing a tuple"))

theorem tupleHashGuard_proven : TupleHashGuard := by
  intro α hashE t
  refine ⟨?_, fun h => ?_, fun h => ?_⟩
  · unfold tupleHashGuarded tupleHash
    split <;> simp
  · simp [tupleHashGuarded, h]
  · simp [tupleHashGuarded, h]

end PyLean.BytesObj.Seq
