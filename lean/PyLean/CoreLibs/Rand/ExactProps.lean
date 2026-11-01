import PyLean.CoreLibs.Rand.MtProps
import PyLean.CoreLibs.Rand.Exact
import PyLean.RangeSlice.Length

/-!
Properties of the integer and sequence layer of `Lib/random.py`, for every core
generator. `Post x P` is partial correctness: if `x` returns, the value satisfies
`P`. A loop that keeps being rejected ends in `modelFuel`, which is not a Python
outcome, so `Post` says nothing about it; that is the honest statement, because
termination of a rejection loop depends on what the generator produces.
-/

namespace PyLean.CoreLibs.Rand

open PyLean PyLean.RangeSlice RM Flt

variable {σ F α β : Type}

/-- If `x` returns, its value satisfies `P`. -/
def Post (x : RM σ α) (P : α → Prop) : Prop := ∀ s a s', x s = (.ok a, s') → P a

theorem Post.bind {x : RM σ α} {f : α → RM σ β} {Q : α → Prop} {P : β → Prop}
    (hx : Post x Q) (hf : ∀ a, Q a → Post (f a) P) : Post (x >>= f) P := by
  intro s b s' h
  simp only [RM.bind_apply] at h
  cases hxs : x s with
  | mk r t =>
    rw [hxs] at h
    cases r with
    | error e => cases h
    | ok a => exact hf a (hx s a t hxs) t b s' h

theorem Post.pure {a : α} {P : α → Prop} (h : P a) : Post (Pure.pure a : RM σ α) P := by
  intro s b s' e
  simp only [RM.pure_apply, Prod.mk.injEq, Except.ok.injEq] at e
  exact e.1 ▸ h

theorem Post.raise {e : PyExc} {P : α → Prop} : Post (RM.raise e : RM σ α) P := by
  intro s b s' h
  simp at h

theorem Post.lift (x : Py α) : Post (RM.lift x : RM σ α) (fun a => x = .ok a) := by
  intro s b s' h
  simp only [RM.lift_apply, Prod.mk.injEq] at h
  exact h.1

theorem Post.mono {x : RM σ α} {P Q : α → Prop} (h : Post x P) (hq : ∀ a, P a → Q a) : Post x Q :=
  fun s a s' e => hq a (h s a s' e)

theorem Post.any (x : RM σ α) : Post x (fun _ => True) := fun _ _ _ _ => trivial

/-- The contract of `self._randbelow`: "Return a random int in the range [0,n)",
Lib/random.py:246. -/
def BelowValid (below : Nat → RM σ Nat) : Prop := ∀ n, 0 < n → Post (below n) (· < n)

/-! ### `_randbelow` -/

theorem belowLoop_lt (g : Gen σ F) (n k : Nat) : ∀ fuel r, Post (belowLoop g n k fuel r) (· < n)
  | 0, r => by
    simp only [belowLoop]
    split
    · exact Post.raise
    · exact Post.pure (by omega)
  | fuel + 1, r => by
    simp only [belowLoop]
    split
    · exact Post.bind (Post.any _) (fun r _ => belowLoop_lt g n k fuel r)
    · exact Post.pure (by omega)

/-- `_randbelow_with_getrandbits(n)` returns a value in `[0, n)` for every `n > 0`,
whatever `getrandbits` returns, because the loop only leaves on `r < n`. Each draw
fits `k = n.bit_length()` bits and `2 ** k ≤ 2 * n`, so with a uniform source each
draw is accepted with probability above 1/2 (the loop terminates with probability 1;
the fuel of the model is not part of the claim). -/
def RandbelowInRange : Prop :=
  (∀ (g : Gen σ F) (fuel : Nat), BelowValid (randbelowWith g fuel)) ∧
  (∀ n : Nat, 0 < n → n < 2 ^ bitLength n ∧ 2 ^ bitLength n ≤ 2 * n)

theorem randbelowInRange_proven : RandbelowInRange (σ := σ) (F := F) := by
  refine ⟨fun g fuel n _ => Post.bind (Post.any _) (fun r _ => belowLoop_lt g n _ fuel r), ?_⟩
  intro n hn
  refine ⟨lt_pow_bitLength n, ?_⟩
  unfold bitLength
  rw [if_neg (by omega), Nat.pow_succ]
  have := Nat.log2_self_le (n := n) (by omega)
  omega

/-- `_randbelow_without_getrandbits(n)` returns a value in `[0, n)` when
`n < maxsize`: the result is an `int % n`. (`n >= maxsize` is `floor(random() * n)`,
a float bound, entry `rand-randbelow-without-huge`.) -/
def RandbelowWithoutInRange : Prop :=
  ∀ [Flt F] (g : Gen σ F) (fuel n : Nat), 0 < n → n < 2 ^ 53 → Post (randbelowWithout g fuel n) (· < n)

theorem randbelowWithoutInRange_proven : RandbelowWithoutInRange (σ := σ) (F := F) := by
  intro _ g fuel n h0 h1
  simp only [randbelowWithout]
  rw [if_neg (by omega)]
  refine Post.bind (Post.any _) fun _ _ => Post.bind (Post.any _) fun _ _ =>
    Post.bind (Post.any _) fun _ _ => Post.bind (Post.any _) fun _ _ =>
    Post.bind (Post.any _) fun v _ => Post.pure ?_
  have h2 : v % (n : Int) < n := Int.emod_lt_of_pos _ (by omega)
  have h3 : 0 ≤ v % (n : Int) := Int.emod_nonneg _ (by omega)
  show (v % (n : Int)).toNat < n
  omega

/-! ### `randbytes` -/

theorem toBytesLE_spec (r n : Nat) (h : r < 2 ^ (8 * n)) :
    toBytesLE r n = .ok ((List.range n).map fun i => (r >>> (8 * i)) % 256) := by
  simp [toBytesLE, h]

/-- The bytes, read back little-endian. -/
def fromBytesLE : List Nat → Nat
  | [] => 0
  | b :: bs => b + 256 * fromBytesLE bs

theorem fromBytesLE_range : ∀ (m n : Nat),
    fromBytesLE ((List.range m).map fun i => (n >>> (8 * i)) % 256) = n % 2 ^ (8 * m)
  | 0, n => by simp [fromBytesLE, Nat.mod_one]
  | m + 1, n => by
    have hmap : ((List.range (m + 1)).map fun i => (n >>> (8 * i)) % 256)
        = n % 256 :: (List.range m).map (fun i => ((n >>> 8) >>> (8 * i)) % 256) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.mul_zero, Nat.shiftRight_zero]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp, Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one]
      rw [← Nat.shiftRight_add, Nat.add_comm]
    rw [hmap]
    simp only [fromBytesLE]
    rw [fromBytesLE_range m (n >>> 8)]
    have h : 8 * (m + 1) = 8 + 8 * m := by omega
    rw [h, Nat.pow_add, Nat.mod_mul, Nat.shiftRight_eq_div_pow]

/-- `randbytes(n)` for an `int` `n ≥ 0`, on a generator meeting the `getrandbits`
contract: exactly `n` bytes, each below 256, which are the bytes of
`getrandbits(8 * n)`, little-endian, from the same draw. `to_bytes` cannot overflow. -/
def RandbytesSpec : Prop :=
  ∀ (g : Gen σ F) (n : Nat) (s : σ), g.Valid →
    let k := 8 * n
    match g.getrandbits (.int (k : Int)) s with
    | (.error e, s') => randbytes g (.int (n : Int)) s = (.error e, s')
    | (.ok r, s') =>
      ∃ b, randbytes g (.int (n : Int)) s = (.ok b, s') ∧
        b.length = n ∧ (∀ x ∈ b, x < 256) ∧ fromBytesLE b = r

theorem randbytesSpec_proven : RandbytesSpec (σ := σ) (F := F) := by
  intro g n s hg
  have hdef : randbytes g (.int (n : Int)) s =
      (match g.getrandbits (.int ((8 * n : Nat) : Int)) s with
       | (.ok r, s') => (toBytesLE r n, s')
       | (.error e, s') => (.error e, s')) := by
    simp only [randbytes, RM.bind_apply, RM.lift_apply, mul8, IntArg.index]
    have : (n : Int) * 8 = ((8 * n : Nat) : Int) := by omega
    rw [this]
    cases g.getrandbits (.int ((8 * n : Nat) : Int)) s with
    | mk r t => cases r <;> simp [Int.toNat_natCast]
  simp only
  rw [hdef]
  cases hx : g.getrandbits (.int ((8 * n : Nat) : Int)) s with
  | mk r t =>
    cases r with
    | error e => rfl
    | ok r =>
      have hb : r < 2 ^ (8 * n) := hg _ r s t hx
      simp only
      refine ⟨_, by rw [toBytesLE_spec r n hb], by simp, ?_, ?_⟩
      · intro x hx'
        simp only [List.mem_map] at hx'
        obtain ⟨i, _, rfl⟩ := hx'
        exact Nat.mod_lt _ (by decide)
      · rw [fromBytesLE_range, Nat.mod_eq_of_lt hb]

/-! ### `randrange`, `randint` -/

theorem floorDiv_pos (x c : Int) (h : c > 0) : floorDiv x c = x / c := by simp [floorDiv, h]

theorem floorDiv_neg (x c : Int) (h : ¬ c > 0) : floorDiv x c = (-x) / (-c) := by simp [floorDiv, h]

/-- For `c > 0`, `k < (w + c - 1) // c ↔ k * c < w`. -/
theorem lt_floorDiv_pos (w c k : Int) (hc : 0 < c) (hk : 0 ≤ k) :
    k < (w + c - 1) / c ↔ k * c < w := by
  have h := Int.le_ediv_iff_mul_le (a := k + 1) (b := w + c - 1) hc
  have e : (k + 1) * c = k * c + c := by rw [Int.add_mul, Int.one_mul]
  rw [e] at h
  constructor
  · intro hl
    have := h.mp (by omega)
    omega
  · intro hl
    have := h.mpr (by omega)
    omega

/-- The length formula of `randrange`, Lib/random.py:325-328, for `c ≠ 0`, is the
length of `range`. -/
def rrLen (w c : Int) : Int :=
  if c > 0 then floorDiv (w + c - 1) c else floorDiv (w + c + 1) c

theorem rrLen_lt (a b c k : Int) (h0 : c ≠ 0) (hk : 0 ≤ k) :
    k < rrLen (b - a) c ↔ InSeq a b c k := by
  unfold rrLen InSeq
  by_cases hc : c > 0
  · rw [if_pos hc, if_pos (by omega), floorDiv_pos _ _ hc, lt_floorDiv_pos _ _ _ hc hk]
    have : k * c = c * k := Int.mul_comm _ _
    constructor <;> intro h <;> omega
  · rw [if_neg hc, if_neg (by omega), floorDiv_neg _ _ hc]
    have hc' : 0 < -c := by omega
    have e : -(b - a + c + 1) = (a - b) + (-c) - 1 := by omega
    rw [e, lt_floorDiv_pos _ _ _ hc' hk]
    have : k * -c = -(k * c) := by rw [Int.mul_neg]
    constructor <;> intro h <;> omega

theorem computeRangeLength_eq (a b c : Int) (h0 : c ≠ 0) :
    computeRangeLength a b c = max (rrLen (b - a) c) 0 := by
  have h1 := computeRangeLength_isLen a b c h0
  have h2 : IsLen a b c (max (rrLen (b - a) c) 0) := by
    refine ⟨by omega, fun k hk => ?_⟩
    rw [← rrLen_lt a b c k h0 hk]
    omega
  exact isLen_unique h1 h2

/-- "Roughly equivalent to `choice(range(start, stop, step))`" (Lib/random.py:297),
for `int` arguments: with `L = len(range(start, stop, step))`, if `L > 0` then
`randrange` is exactly one call `below(L)` and `range(...)[that]`, and if `L = 0` or
`step == 0` it raises `ValueError` without drawing. Python's `range` is the model
`computeRangeLength`, `computeItem` of `RangeSlice`. -/
def RandrangeIsRangeChoice : Prop :=
  ∀ (below : Nat → RM σ Nat) (a b c : Int) (s : σ), c ≠ 0 →
    let L := computeRangeLength a b c
    let r := makeRangeObject a b c
    (0 < L → randrange below (.int a) (some (.int b)) (some (.int c)) s =
      (do let j ← below L.toNat; return computeItem r j) s) ∧
    (L = 0 → ∃ e, randrange below (.int a) (some (.int b)) (some (.int c)) s = (.error e, s) ∧
      e.className = "ValueError")

theorem intStr_error {n : Int} {e : PyExc} (h : intStr n = .error e) : e.className = "ValueError" := by
  unfold intStr at h
  split at h
  · cases h; rfl
  · cases h

theorem argStr_error {x : IntArg} {e : PyExc} (h : argStr x = .error e) :
    e.className = "ValueError" := by
  cases x with
  | int n => exact intStr_error h
  | bool b => cases h
  | other ty => cases h

theorem emptyRange2_error {x y : IntArg} {e : PyExc} (h : emptyRange2 x y = .error e) :
    e.className = "ValueError" := by
  simp only [emptyRange2, bind, Except.bind] at h
  cases hx : argStr x with
  | error e' => rw [hx] at h; cases h; exact argStr_error hx
  | ok a =>
    rw [hx] at h
    cases hy : argStr y with
    | error e' => simp only [hy] at h; cases h; exact argStr_error hy
    | ok b => simp only [hy] at h; cases h

theorem emptyRange3_error {x y z : IntArg} {e : PyExc} (h : emptyRange3 x y z = .error e) :
    e.className = "ValueError" := by
  simp only [emptyRange3, bind, Except.bind] at h
  cases hx : argStr x with
  | error e' => rw [hx] at h; cases h; exact argStr_error hx
  | ok a =>
    rw [hx] at h
    cases hy : argStr y with
    | error e' => simp only [hy] at h; cases h; exact argStr_error hy
    | ok b =>
      simp only [hy] at h
      cases hz : argStr z with
      | error e' => simp only [hz] at h; cases h; exact argStr_error hz
      | ok c => simp only [hz] at h; cases h

theorem raiseValue_shape {m : Py String} (s : σ) (hm : ∀ e, m = .error e → e.className = "ValueError") :
    ∃ e, (raiseValue m : RM σ α) s = (.error e, s) ∧ e.className = "ValueError" := by
  cases m with
  | ok x => exact ⟨.valueError x, rfl, rfl⟩
  | error e => exact ⟨e, rfl, hm e rfl⟩

theorem randrange_int (below : Nat → RM σ Nat) (a b c : Int) :
    randrange below (.int a) (some (.int b)) (some (.int c)) =
      (if c = 1 then
        if b - a > 0 then (do let r ← below (b - a).toNat; return a + (r : Int))
        else raiseValue (emptyRange2 (.int a) (.int b))
      else if c = 0 then (RM.raise (.valueError "zero step for randrange()") : RM σ Int)
      else if rrLen (b - a) c ≤ 0 then raiseValue (emptyRange3 (.int a) (.int b) (.int c))
      else (do let r ← below (rrLen (b - a) c).toNat; return a + c * (r : Int))) := rfl

theorem randrange_one (below : Nat → RM σ Nat) (a : Int) :
    randrange below (.int a) none none =
      (if a > 0 then (do let r ← below a.toNat; return (r : Int))
       else (RM.raise (.valueError "empty range for randrange()") : RM σ Int)) := rfl

theorem post_bind_pure (below : Nat → RM σ Nat) (hv : BelowValid below) {n : Nat} (hn : 0 < n)
    (f : Nat → Int) (P : Int → Prop) (h : ∀ j, j < n → P (f j)) :
    Post (do let r ← below n; return f r) P :=
  Post.bind (hv n hn) (fun j hj => Post.pure (h j hj))

theorem rrLen_one (w : Int) : rrLen w 1 = w := by
  simp [rrLen, floorDiv]

theorem bind_congr_result {x : RM σ Nat} {f g : Nat → RM σ Int} {s : σ}
    (h : ∀ r t, x s = (.ok r, t) → f r t = g r t) : (x >>= f) s = (x >>= g) s := by
  simp only [RM.bind_apply]
  cases hx : x s with
  | mk r t =>
    cases r with
    | ok a => exact h a t hx
    | error e => rfl

theorem randrangeIsRangeChoice_proven : RandrangeIsRangeChoice (σ := σ) := by
  intro below a b c s hc
  have hlen := computeRangeLength_eq a b c hc
  simp only
  rw [randrange_int]
  constructor
  · intro hL
    by_cases h1 : c = 1
    · subst h1
      rw [rrLen_one] at hlen
      have hpos : b - a > 0 := by omega
      have hto : (computeRangeLength a b 1).toNat = (b - a).toNat := by
        rw [hlen]
        omega
      rw [if_pos rfl, if_pos hpos, hto]
      apply bind_congr_result
      intro r t _
      simp [computeItem, makeRangeObject]
    · have hpos : ¬ rrLen (b - a) c ≤ 0 := by omega
      have hto : (computeRangeLength a b c).toNat = (rrLen (b - a) c).toNat := by
        rw [hlen]
        omega
      rw [if_neg h1, if_neg hc, if_neg hpos, hto]
      apply bind_congr_result
      intro r t _
      simp [computeItem, makeRangeObject, h1, Int.mul_comm]
  · intro hL
    by_cases h1 : c = 1
    · subst h1
      rw [rrLen_one] at hlen
      rw [if_pos rfl, if_neg (by omega)]
      exact raiseValue_shape s (fun e h => emptyRange2_error h)
    · rw [if_neg h1, if_neg hc, if_pos (by omega)]
      exact raiseValue_shape s (fun e h => emptyRange3_error h)

/-- `randrange` stays in range: one-argument `randrange(a)` in `[0, a)`; with `stop`
and `step`, the result is `a + k * c` for a `k ≥ 0` that is strictly before `b` in the
direction of `c`. -/
def RandrangeBounds : Prop :=
  ∀ below : Nat → RM σ Nat, BelowValid below →
    (∀ a : Int, Post (randrange below (.int a) none none) (fun r => 0 ≤ r ∧ r < a)) ∧
    (∀ a b c : Int, Post (randrange below (.int a) (some (.int b)) (some (.int c)))
      (fun r => c ≠ 0 ∧ ∃ k : Int, 0 ≤ k ∧ r = a + k * c ∧ InSeq a b c k))

theorem randrangeBounds_proven : RandrangeBounds (σ := σ) := by
  intro below hv
  refine ⟨fun a => ?_, fun a b c => ?_⟩
  · rw [randrange_one]
    by_cases hpos : a > 0
    · rw [if_pos hpos]
      exact post_bind_pure below hv (n := a.toNat) (by omega) (fun j => (j : Int)) _
        (fun j hj => ⟨by omega, by omega⟩)
    · rw [if_neg hpos]
      exact Post.raise
  · rw [randrange_int]
    by_cases hc : c = 0
    · subst hc
      rw [if_neg (by omega), if_pos rfl]
      exact Post.raise
    by_cases h1 : c = 1
    · subst h1
      rw [if_pos rfl]
      by_cases hpos : b - a > 0
      · rw [if_pos hpos]
        exact post_bind_pure below hv (n := (b - a).toNat) (by omega) (fun j => a + (j : Int)) _
          (fun j hj => ⟨by omega, (j : Int), by omega, by simp, by
            simp only [InSeq]
            rw [if_pos (by omega)]
            omega⟩)
      · rw [if_neg hpos]
        intro s r s' h
        obtain ⟨e, he, _⟩ := raiseValue_shape (m := emptyRange2 (.int a) (.int b)) (α := Int) s
          (fun e h => emptyRange2_error h)
        rw [he] at h
        cases h
    · rw [if_neg h1, if_neg hc]
      by_cases hle : rrLen (b - a) c ≤ 0
      · rw [if_pos hle]
        intro s r s' h
        obtain ⟨e, he, _⟩ := raiseValue_shape (m := emptyRange3 (.int a) (.int b) (.int c)) (α := Int) s
          (fun e h => emptyRange3_error h)
        rw [he] at h
        cases h
      · rw [if_neg hle]
        exact post_bind_pure below hv (n := (rrLen (b - a) c).toNat) (by omega)
          (fun j => a + c * (j : Int)) _
          (fun j hj => ⟨hc, (j : Int), by omega, by rw [Int.mul_comm],
            (rrLen_lt a b c j hc (by omega)).mp (by omega)⟩)

/-- Every way `randrange` rejects its arguments: a non-integer argument, `step` given
without `stop`, and an empty one-argument range, each before any draw. -/
def RandrangeArgErrors : Prop :=
  ∀ (below : Nat → RM σ Nat) (s : σ),
    (∀ (ty : String) (stop step : Option IntArg),
      randrange below (.other ty) stop step s =
        (.error (.typeError s!"'{ty}' object cannot be interpreted as an integer"), s)) ∧
    (∀ (a : Int) (step : IntArg), stepIsOne (some step) = false →
      randrange below (.int a) none (some step) s =
        (.error (.typeError "Missing a non-None stop argument"), s)) ∧
    (∀ a : Int, a ≤ 0 →
      randrange below (.int a) none none s =
        (.error (.valueError "empty range for randrange()"), s))

theorem randrangeArgErrors_proven : RandrangeArgErrors (σ := σ) := by
  intro below s
  refine ⟨fun ty stop step => rfl, fun a step h => ?_, fun a h => ?_⟩
  · have hdef : randrange below (.int a) none (some step) =
        (if !stepIsOne (some step) then
          (RM.raise (.typeError "Missing a non-None stop argument") : RM σ Int)
         else if a > 0 then (do let r ← below a.toNat; return (r : Int))
         else (RM.raise (.valueError "empty range for randrange()") : RM σ Int)) := rfl
    rw [hdef, h]
    rfl
  · rw [randrange_one, if_neg (by omega)]
    rfl

/-- `randint(a, b)` "Alias for `randrange(a, b+1)`" (Doc/library/random.rst): same
call and same result for `a ≤ b`; for `b < a` a `ValueError` without a draw. Its
result lies in `[a, b]`. -/
def RandintSpec : Prop :=
  ∀ (below : Nat → RM σ Nat) (a b : Int) (s : σ),
    (a ≤ b → randint below (.int a) (.int b) s =
      randrange below (.int a) (some (.int (b + 1))) none s) ∧
    (b < a → ∃ e, randint below (.int a) (.int b) s = (.error e, s) ∧ e.className = "ValueError") ∧
    (BelowValid below → Post (randint below (.int a) (.int b)) (fun r => a ≤ r ∧ r ≤ b))

theorem randint_int (below : Nat → RM σ Nat) (a b : Int) :
    randint below (.int a) (.int b) =
      (if b < a then raiseValue (do
          let sa ← intStr a
          let sb ← intStr b
          return s!"empty range in randint({sa}, {sb})")
       else (do let r ← below (b - a + 1).toNat; return a + (r : Int))) := rfl

theorem randintSpec_proven : RandintSpec (σ := σ) := by
  intro below a b s
  refine ⟨fun h => ?_, fun h => ?_, fun hv => ?_⟩
  · have hdef : randrange below (.int a) (some (.int (b + 1))) none =
        (if (1 : Int) = 1 then
          if (b + 1) - a > 0 then (do let r ← below ((b + 1) - a).toNat; return a + (r : Int))
          else raiseValue (emptyRange2 (.int a) (.int (b + 1)))
        else if (1 : Int) = 0 then (RM.raise (.valueError "zero step for randrange()") : RM σ Int)
        else if rrLen ((b + 1) - a) 1 ≤ 0 then
          raiseValue (emptyRange3 (.int a) (.int (b + 1)) (.int 1))
        else (do let r ← below (rrLen ((b + 1) - a) 1).toNat; return a + 1 * (r : Int))) := rfl
    rw [randint_int, hdef, if_neg (by omega), if_pos rfl, if_pos (by omega)]
    have : (b + 1 - a) = b - a + 1 := by omega
    rw [this]
  · rw [randint_int, if_pos h]
    apply raiseValue_shape
    intro e he
    simp only [bind, Except.bind] at he
    cases hx : intStr a with
    | error e' => rw [hx] at he; cases he; exact intStr_error hx
    | ok x =>
      rw [hx] at he
      cases hy : intStr b with
      | error e' => simp only [hy] at he; cases he; exact intStr_error hy
      | ok y => simp only [hy] at he; cases he
  · rw [randint_int]
    by_cases hba : b < a
    · rw [if_pos hba]
      intro s r s' h
      have := raiseValue_shape (α := Int) (m := do
          let sa ← intStr a
          let sb ← intStr b
          return s!"empty range in randint({sa}, {sb})") s (fun e he => by
        simp only [bind, Except.bind] at he
        cases hx : intStr a with
        | error e' => rw [hx] at he; cases he; exact intStr_error hx
        | ok x =>
          rw [hx] at he
          cases hy : intStr b with
          | error e' => simp only [hy] at he; cases he; exact intStr_error hy
          | ok y => simp only [hy] at he; cases he)
      obtain ⟨e, he, _⟩ := this
      rw [he] at h
      cases h
    · rw [if_neg hba]
      exact post_bind_pure below hv (n := (b - a + 1).toNat) (by omega) (fun j => a + (j : Int)) _
        (fun j hj => ⟨by omega, by omega⟩)

/-! ### `choice` -/

/-- `choice(seq)`: an empty sequence raises `IndexError` before any draw, and
otherwise the result is `seq[j]` for some `j` in range, for any object with `__len__`
and `__getitem__`. For a list that means the result is an element of it. -/
def ChoiceSpec : Prop :=
  ∀ below : Nat → RM σ Nat, BelowValid below →
    (∀ seq : SeqObj α, seq.len = .ok 0 → ∀ s,
      choice below seq s = (.error (.indexError "Cannot choose from an empty sequence"), s)) ∧
    (∀ seq : SeqObj α, Post (choice below seq)
      (fun x => ∃ n j, seq.len = .ok n ∧ j < n ∧ seq.getItem j = .ok x)) ∧
    (∀ l : List α, Post (choice below (listSeq l)) (· ∈ l))

theorem listGet_ok {l : List α} {i : Nat} {x : α} (h : listGet l i = .ok x) : ∃ hi : i < l.length, l[i] = x := by
  unfold listGet at h
  cases hg : l[i]? with
  | none => rw [hg] at h; cases h
  | some a =>
    rw [hg] at h
    cases h
    have := List.getElem?_eq_some_iff.mp hg
    exact this

theorem choice_post (below : Nat → RM σ Nat) (hv : BelowValid below) (seq : SeqObj α) :
    Post (choice below seq) (fun x => ∃ n j, seq.len = .ok n ∧ j < n ∧ seq.getItem j = .ok x) := by
  unfold choice
  refine Post.bind (Post.lift seq.len) (fun n hn => ?_)
  split
  · exact Post.raise
  · rename_i h0
    refine Post.bind (Post.lift seq.len) (fun n' hn' => ?_)
    have : n' = n := by
      rw [hn] at hn'
      cases hn'
      rfl
    subst this
    refine Post.bind (hv n' (by omega)) (fun j hj => ?_)
    refine Post.mono (Post.lift _) (fun a ha => ?_)
    exact ⟨n', j, hn, hj, ha⟩

theorem choiceSpec_proven : ChoiceSpec (σ := σ) (α := α) := by
  intro below hv
  refine ⟨fun seq h s => ?_, choice_post below hv, fun l => ?_⟩
  · simp only [choice, RM.bind_apply, RM.lift_apply, h]
    rfl
  · refine Post.mono (choice_post below hv (listSeq l)) ?_
    rintro x ⟨n, j, _, _, h⟩
    obtain ⟨hi, rfl⟩ := listGet_ok h
    exact List.getElem_mem hi

/-! ### `shuffle` -/

theorem set_perm : ∀ (x : List α) (i : Nat) (hi : i < x.length) (v : α),
    (x.set i v ++ [x[i]]).Perm (v :: x)
  | [], _, hi, _ => by simp at hi
  | a :: t, 0, _, v => by
    simp only [List.set_cons_zero, List.getElem_cons_zero, List.cons_append]
    exact (List.perm_append_singleton a t).cons v
  | a :: t, i + 1, hi, v => by
    simp only [List.set_cons_succ, List.getElem_cons_succ, List.cons_append]
    exact ((set_perm t i (by simpa using hi) v).cons a).trans (List.Perm.swap v a t)

/-- `x[i], x[j] = x[j], x[i]` permutes `x`. -/
theorem swap_perm (x : List α) (i j : Nat) (hi : i < x.length) (hj : j < x.length) :
    ((x.set i x[j]).set j x[i]).Perm x := by
  by_cases hij : i = j
  · subst hij
    simp
  · let y := x.set i x[j]
    have hjy : j < y.length := by simpa [y] using hj
    have h1 : (y.set j x[i] ++ [y[j]]).Perm (x[i] :: y) := set_perm y j hjy _
    have hyj : y[j] = x[j] := by simp [y, List.getElem_set, Ne.symm hij]
    rw [hyj] at h1
    have h2 : (y ++ [x[i]]).Perm (x[j] :: x) := set_perm x i hi _
    have h3 : (x[i] :: y).Perm (y ++ [x[i]]) := (List.perm_append_singleton _ _).symm
    have h4 : (y.set j x[i] ++ [x[j]]).Perm (x[j] :: x) := h1.trans (h3.trans h2)
    have h5 : (x[j] :: y.set j x[i]).Perm (x[j] :: x) :=
      (List.perm_append_singleton _ _).symm.trans h4
    exact h5.cons_inv

theorem swapAssign_perm {x y : List α} {i j : Nat} (h : swapAssign x i j = .ok y) : y.Perm x := by
  simp only [swapAssign, bind, Except.bind] at h
  cases hj : listGet x j with
  | error e => rw [hj] at h; cases h
  | ok xj =>
    rw [hj] at h
    cases hi : listGet x i with
    | error e => simp only [hi] at h; cases h
    | ok xi =>
      simp only [hi] at h
      cases h
      obtain ⟨hjl, rfl⟩ := listGet_ok hj
      obtain ⟨hil, rfl⟩ := listGet_ok hi
      exact swap_perm x i j hil hjl

theorem shuffleLoop_perm (below : Nat → RM σ Nat) : ∀ (i : Nat) (x : List α),
    Post (shuffleLoop below i x) (·.Perm x)
  | 0, x => Post.pure (List.Perm.refl x)
  | i + 1, x => by
    simp only [shuffleLoop]
    refine Post.bind (Post.any _) (fun j _ => ?_)
    refine Post.bind (Post.lift _) (fun y hy => ?_)
    exact Post.mono (shuffleLoop_perm below i y) (fun a ha => ha.trans (swapAssign_perm hy))

/-- `shuffle(x)` permutes the list, whatever `_randbelow` does. If `_randbelow` meets
its contract and never raises, `shuffle` cannot raise either: the indices are always
in range. -/
def ShuffleSpec : Prop :=
  ∀ (below : Nat → RM σ Nat) (x : List α),
    Post (shuffle below x) (·.Perm x) ∧
    (BelowValid below → (∀ n s, ∃ r s', below n s = (.ok r, s')) →
      ∀ s, ∃ y s', shuffle below x none s = (.ok y, s'))

theorem shuffle_none (below : Nat → RM σ Nat) (x : List α) :
    shuffle below x = shuffleLoop below (x.length - 1) x := by
  unfold shuffle
  split <;> simp_all

theorem shuffleLoop_total (below : Nat → RM σ Nat) (hv : BelowValid below)
    (ht : ∀ n s, ∃ r s', below n s = (.ok r, s')) :
    ∀ (i : Nat) (x : List α), i < x.length ∨ i = 0 →
      ∀ s, ∃ y s', shuffleLoop below i x s = (.ok y, s')
  | 0, x, _, s => ⟨x, s, rfl⟩
  | i + 1, x, h, s => by
    obtain ⟨j, s1, hj⟩ := ht (i + 2) s
    have hjlt : j < i + 2 := hv (i + 2) (by omega) s j s1 hj
    have hi : i + 1 < x.length := by omega
    have hjl : j < x.length := by omega
    have hget : ∀ (k : Nat) (hk : k < x.length), listGet x k = .ok x[k] := by
      intro k hk
      simp [listGet, hk]
    let y := (x.set (i + 1) x[j]).set j x[i + 1]
    have hsw : swapAssign x (i + 1) j = .ok y := by
      simp only [swapAssign, hget j hjl, hget (i + 1) hi]
      rfl
    have hlen : y.length = x.length := by simp [y]
    obtain ⟨z, s2, hz⟩ := shuffleLoop_total below hv ht i y (by omega) s1
    refine ⟨z, s2, ?_⟩
    simp only [shuffleLoop, RM.bind_apply, RM.lift_apply, hj, hsw]
    exact hz

theorem shuffleSpec_proven : ShuffleSpec (σ := σ) (α := α) := by
  intro below x
  rw [shuffle_none]
  refine ⟨shuffleLoop_perm below _ x, fun hv ht s => ?_⟩
  exact shuffleLoop_total below hv ht _ x (by omega) s

/-- `shuffle` on an immutable sequence of at least two items raises `TypeError` at
the first assignment, after one draw; shorter ones are left alone. -/
def ShuffleImmutable : Prop :=
  ∀ (below : Nat → RM σ Nat) (x : List α) (ty : String) (s : σ),
    (x.length ≤ 1 → shuffle below x (some ty) s = (.ok x, s)) ∧
    (2 ≤ x.length → (∀ r t, below x.length s = (.ok r, t) →
      shuffle below x (some ty) s = (.error (.typeError s!"'{ty}' object does not support item assignment"), t)))

theorem shuffleImmutable_proven : ShuffleImmutable (σ := σ) (α := α) := by
  intro below x ty s
  constructor
  · intro h
    match x, h with
    | [], _ => rfl
    | [a], _ => rfl
  · intro h r t hb
    match x, h with
    | a :: b :: rest, _ =>
      simp only [List.length_cons] at hb
      simp only [shuffle, List.length_cons, RM.bind_apply, hb]
      rfl

/-! ### `sample` -/

theorem take_set_lt (l : List α) (m j : Nat) (v : α) (h : j < m) :
    (l.set j v).take m = (l.take m).set j v := by
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_take, List.getElem?_set]
  by_cases h1 : j = i
  · subst h1
    simp only [if_true, h]
    by_cases h2 : j < l.length
    · simp [h, h2]
      omega
    · simp [h, h2]
      omega
  · simp [h1]

/-- One step of the pool loop on the live part. -/
theorem pool_step (pool : List α) (m j : Nat) (hm : m < pool.length) (hj : j ≤ m) :
    (((pool.set j pool[m]).take m) ++ [pool[j]]).Perm (pool.take (m + 1)) := by
  have hsucc : pool.take (m + 1) = pool.take m ++ [pool[m]] := by
    rw [List.take_succ, List.getElem?_eq_getElem hm]
    rfl
  rw [hsucc]
  by_cases hjm : j = m
  · subst hjm
    simp
  · have hlt : j < m := by omega
    have hT : (pool.take m).length = m := by
      rw [List.length_take]
      omega
    have h1 := set_perm (pool.take m) j (by omega) pool[m]
    have hTj : (pool.take m)[j]'(by omega) = pool[j] := List.getElem_take ..
    rw [hTj] at h1
    rw [take_set_lt _ _ _ _ hlt]
    exact h1.trans (List.perm_append_singleton _ _).symm

/-- The pool branch: run on the list `pool` next to a list of positions `ipool`
with the same contents. `look` maps a position to the population element. -/
theorem poolLoop_spec (below : Nat → RM σ Nat) (hv : BelowValid below) (n : Nat) (look : Nat → Option α) :
    ∀ (c i : Nat) (pool : List α) (ipool : List Nat), i + c ≤ n → pool.length = n →
      ipool.length = n → ipool.map look = pool.map some →
      Post (poolLoop below n c i pool) (fun l => l.length = c ∧ ∃ pos rest : List Nat,
        (pos ++ rest).Perm (ipool.take (n - i)) ∧ pos.length = c ∧ pos.map look = l.map some)
  | 0, i, pool, ipool, _, _, _, _ => by
    exact Post.pure ⟨rfl, [], ipool.take (n - i), List.Perm.refl _, rfl, rfl⟩
  | c + 1, i, pool, ipool, hb, hp, hi, hr => by
    simp only [poolLoop]
    refine Post.bind (hv (n - i) (by omega)) (fun j hj => ?_)
    refine Post.bind (Post.lift _) (fun x hx => ?_)
    refine Post.bind (Post.lift _) (fun v hvv => ?_)
    obtain ⟨hjl, rfl⟩ := listGet_ok hx
    obtain ⟨hml, rfl⟩ := listGet_ok hvv
    have hmn : n - i - 1 < ipool.length := by omega
    have hji : j < ipool.length := by omega
    let ipool' := ipool.set j ipool[n - i - 1]
    have hr' : ipool'.map look = (pool.set j pool[n - i - 1]).map some := by
      simp only [ipool', List.map_set]
      rw [hr]
      have := congrArg (fun l => l[n - i - 1]?) hr
      simp only [List.getElem?_map, List.getElem?_eq_getElem hmn,
        List.getElem?_eq_getElem hml, Option.map_some] at this
      have h2 : look ipool[n - i - 1] = some pool[n - i - 1] := Option.some.inj this
      rw [h2]
    refine Post.bind (poolLoop_spec below hv n look c (i + 1) (pool.set j pool[n - i - 1]) ipool'
      (by omega) (by simp [hp]) (by simp [ipool', hi]) hr') (fun l hl => ?_)
    obtain ⟨hlen, pos, rest, hperm, hpl, hpm⟩ := hl
    refine Post.pure ?_
    refine ⟨by simp [hlen], ipool[j] :: pos, rest, ?_, by simp [hpl], ?_⟩
    · have hstep := pool_step ipool (n - i - 1) j hmn (by omega)
      have e : n - (i + 1) = n - i - 1 := by omega
      have e2 : n - i = n - i - 1 + 1 := by omega
      rw [e] at hperm
      rw [e2]
      have hcons : (ipool[j] :: (pos ++ rest)).Perm
          ((ipool.set j ipool[n - i - 1]).take (n - i - 1) ++ [ipool[j]]) :=
        (hperm.cons _).trans (List.perm_append_singleton _ _).symm
      exact hcons.trans hstep
    · have := congrArg (fun l => l[j]?) hr
      simp only [List.getElem?_map, List.getElem?_eq_getElem hji,
        List.getElem?_eq_getElem hjl, Option.map_some] at this
      have h2 : look ipool[j] = some pool[j] := Option.some.inj this
      simp only [List.map_cons, hpm, h2]

theorem pickLoop_spec (below : Nat → RM σ Nat) (hv : BelowValid below) (n : Nat) (hn : 0 < n)
    (selected : List Nat) : ∀ (fuel j : Nat), j < n →
      Post (pickLoop below n selected fuel j) (fun r => r < n ∧ r ∉ selected)
  | 0, j, hj => by
    simp only [pickLoop]
    split
    · exact Post.raise
    · exact Post.pure ⟨hj, by assumption⟩
  | fuel + 1, j, hj => by
    simp only [pickLoop]
    split
    · exact Post.bind (hv n hn) (fun j' hj' => pickLoop_spec below hv n hn selected fuel j' hj')
    · exact Post.pure ⟨hj, by assumption⟩

/-- The set branch. -/
theorem setLoop_spec (below : Nat → RM σ Nat) (hv : BelowValid below) (pop : SeqObj α) (n fuel : Nat)
    (hn : 0 < n) (look : Nat → Option α) (hpop : ∀ j x, pop.getItem j = .ok x → look j = some x) :
    ∀ (c : Nat) (selected : List Nat), Post (setLoop below pop n fuel c selected)
      (fun l => l.length = c ∧ ∃ pos : List Nat, pos.Nodup ∧ pos.length = c ∧
        (∀ j ∈ pos, j < n ∧ j ∉ selected) ∧ pos.map look = l.map some)
  | 0, selected => by
    exact Post.pure ⟨rfl, [], List.nodup_nil, rfl, by simp, rfl⟩
  | c + 1, selected => by
    simp only [setLoop]
    refine Post.bind (hv n hn) (fun j hj => ?_)
    refine Post.bind (pickLoop_spec below hv n hn selected fuel j hj) (fun j' hj2 => ?_)
    obtain ⟨hj', hns⟩ := hj2
    refine Post.bind (Post.lift _) (fun x hx => ?_)
    refine Post.bind (setLoop_spec below hv pop n fuel hn look hpop c (j' :: selected)) (fun l hl => ?_)
    obtain ⟨hlen, pos, hnd, hpl, hall, hm⟩ := hl
    refine Post.pure ?_
    refine ⟨by simp [hlen], j' :: pos, ?_, by simp [hpl], ?_, ?_⟩
    · apply List.nodup_cons.mpr
      refine ⟨fun hmem => (hall _ hmem).2 (by simp), hnd⟩
    · intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact ⟨hj', hns⟩
      · have := hall a ha
        exact ⟨this.1, fun h => this.2 (List.mem_cons_of_mem _ h)⟩
    · simp [hm, hpop _ _ hx]

/-- `sample(population, k)` on a list, with `0 ≤ k ≤ len(population)` (other `k` raise):
the result has `k` items, read from `k` distinct positions of the population, in both
the pool branch and the set branch. Elements need not be distinct ("each occurrence
is a possible selection"), so positions are the right notion. Holds for every `fuel`
and `_randbelow` that meets its contract. -/
def SampleDistinctPositions : Prop :=
  ∀ (below : Nat → RM σ Nat) (fuel : Nat) (p : List α) (k : Int), BelowValid below →
    Post (sample below fuel (listSeq p) k)
      (fun l => (l.length : Int) = k ∧ ∃ pos : List Nat, pos.Nodup ∧ pos.length = l.length ∧
        (∀ j ∈ pos, j < p.length) ∧ pos.map (fun j => p[j]?) = l.map some)

theorem sampleCore_list (below : Nat → RM σ Nat) (hv : BelowValid below) (fuel : Nat) (p : List α) (k : Int) :
    Post (sampleCore below fuel (listSeq p) p.length k)
      (fun l => (l.length : Int) = k ∧ ∃ pos : List Nat, pos.Nodup ∧ pos.length = l.length ∧
        (∀ j ∈ pos, j < p.length) ∧ pos.map (fun j => p[j]?) = l.map some) := by
  unfold sampleCore
  split
  · exact Post.raise
  rename_i hk
  have hk0 : 0 ≤ k := by omega
  have hkn : k ≤ p.length := by omega
  simp only
  have hmapr : (List.range p.length).map (fun j => p[j]?) = p.map some := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp
  split
  · have hspec := poolLoop_spec below hv p.length (fun j => p[j]?) k.toNat 0 p (List.range p.length)
      (by omega) rfl (by simp) hmapr
    show Post (poolLoop below p.length k.toNat 0 p) _
    refine Post.mono hspec ?_
    rintro l ⟨hlen, pos, rest, hperm, hpl, hm⟩
    have hrn : (List.take (p.length - 0) (List.range p.length)) = List.range p.length := by simp
    rw [hrn] at hperm
    have hnd : (pos ++ rest).Nodup := (hperm.nodup_iff).mpr List.nodup_range
    refine ⟨by omega, pos, ?_, by omega, ?_, hm⟩
    · exact (List.nodup_append.mp hnd).1
    · intro j hj
      have : j ∈ pos ++ rest := List.mem_append_left _ hj
      have := hperm.mem_iff.mp this
      simpa using this
  · rename_i hset
    have hn0 : 0 < p.length := by
      have : 21 ≤ setsize k.toNat := by simp only [setsize]; omega
      omega
    have hspec := setLoop_spec below hv (listSeq p) p.length fuel hn0 (fun j => p[j]?)
      (by
        intro j x hx
        obtain ⟨hj, rfl⟩ := listGet_ok hx
        simp [hj]) k.toNat []
    refine Post.mono hspec ?_
    rintro l ⟨hlen, pos, hnd, hpl, hall, hm⟩
    exact ⟨by omega, pos, hnd, by omega, fun j hj => (hall j hj).1, hm⟩

theorem sampleDistinctPositions_proven : SampleDistinctPositions (σ := σ) (α := α) := by
  intro below fuel p k hv
  have hdef : sample below fuel (listSeq p) k =
      (RM.lift (listSeq p).len >>= fun n => sampleCore below fuel (listSeq p) n k) := rfl
  rw [hdef]
  refine Post.bind (Post.lift _) (fun n hn => ?_)
  have : n = p.length := by
    simp only [listSeq] at hn
    cases hn
    rfl
  subst this
  exact sampleCore_list below hv fuel p k

/-- The argument checks of `sample`, each before any draw. -/
def SampleArgErrors : Prop :=
  ∀ (below : Nat → RM σ Nat) (fuel : Nat) (pop : SeqObj α) (k : Int) (counts : Option CountsArg) (s : σ),
    (pop.isSequence = false → sample below fuel pop k counts s =
      (.error (.typeError "Population must be a sequence.  For dicts or sets, use sorted(d)."), s)) ∧
    (∀ n, pop.isSequence = true → pop.len = .ok n → counts = none → (k < 0 ∨ k > n) →
      sample below fuel pop k counts s =
        (.error (.valueError "Sample larger than population or is negative"), s)) ∧
    (∀ n cs, pop.isSequence = true → pop.len = .ok n → counts = some (.seq cs) → cs.length ≠ n →
      sample below fuel pop k counts s =
        (.error (.valueError "The number of counts does not match the population"), s))

theorem accumulateCounts_length (cs : List CountV) : (accumulateCounts cs).length = cs.length := by
  have go : ∀ (l : List CountV) (acc : CountV), (accumulateCounts.go acc l).length = l.length := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons x xs ih =>
      intro acc
      simp only [accumulateCounts.go, List.length_cons, ih]
  cases cs with
  | nil => rfl
  | cons c cs => simp [accumulateCounts, go]

theorem sampleArgErrors_proven : SampleArgErrors (σ := σ) (α := α) := by
  intro below fuel pop k counts s
  refine ⟨fun h => ?_, fun n h1 h2 h3 h4 => ?_, fun n cs h1 h2 h3 h4 => ?_⟩
  · simp only [sample, h]
    rfl
  · subst h3
    have hdef : sample below fuel pop k none =
        (RM.lift pop.len >>= fun n => sampleCore below fuel pop n k) := by
      simp only [sample, h1]
      rfl
    simp only [hdef, RM.bind_apply, RM.lift_apply, h2, sampleCore]
    rw [if_pos (by omega)]
    rfl
  · subst h3
    have hdef : sample below fuel pop k (some (.seq cs)) =
        (RM.lift pop.len >>= fun n =>
          if (accumulateCounts cs).length ≠ n then
            RM.raise (.valueError "The number of counts does not match the population")
          else
            let cum := accumulateCounts cs
            let total : CountV := cum.getLast?.getD (some 0)
            match total with
            | none => RM.raise (.typeError "Counts must be integers")
            | some total =>
              if total < 0 then RM.raise (.valueError "Counts must be non-negative")
              else do
                let selections ← sampleRange below fuel total.toNat k
                RM.lift (mapSelections pop (cum.dropLast.filterMap id) selections)) := by
      simp only [sample, h1]
      rfl
    simp only [hdef, RM.bind_apply, RM.lift_apply, h2]
    rw [if_pos (by rw [accumulateCounts_length]; exact h4)]
    rfl

/-- `sample` rejects a negative count. It does not: only the running total is
checked (Lib/random.py:429), so `sample(['a', 'b'], counts=[3, -1], k=2)` succeeds,
while `counts=[-1, -1]` raises `ValueError: Counts must be non-negative`. -/
def SampleRejectsNegativeCounts : Prop :=
  ∀ (below : Nat → RM Unit Nat) (cs : List Int) (p : List Nat) (k : Int),
    cs.length = p.length → (∃ c ∈ cs, c < 0) →
    ∃ e, sample below 0 (listSeq p) k (some (.seq (cs.map some))) () = (.error e, ()) ∧
      e.className = "ValueError"

theorem sampleRejectsNegativeCounts_refuted : ¬ SampleRejectsNegativeCounts := by
  intro h
  obtain ⟨e, he⟩ := h (fun _ s => (.ok 0, s)) [3, -1] [10, 20] 2 rfl ⟨-1, by simp, by decide⟩
  have key : sample (fun _ s => (.ok 0, s) : Nat → RM Unit Nat) 0 (listSeq [10, 20]) 2
      (some (.seq (([3, -1] : List Int).map some))) () = (.ok [10, 10], ()) := by
    rfl
  rw [key] at he
  cases he.1

end PyLean.CoreLibs.Rand
