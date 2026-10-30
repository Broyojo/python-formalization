import PyLean.Itertools.CountRepeat
import PyLean.Itertools.IsliceProps

/-!
`count` and `repeat`: the C-long fast path and the PyLong slow path of `count`
are indistinguishable (values and `repr`), and `repeat`'s `__length_hint__`
and `repr` track the remaining count.
-/

namespace PyLean.Itertools

open PyLean

/-! ## count -/

/-- What `count(start, step)` should answer: after `k` calls of `next()` the
current value is `V = start + k*step`; `repr` shows `V`, and `step` unless it
is the int 1. -/
def countSpec (step : Int) : Int → List Op → List OpRes
  | _, [] => []
  | v, .next :: ops => .int v :: countSpec step (v + step) ops
  | v, .repr :: ops =>
    .str (if step = 1 then s!"count({v})" else s!"count({v}, {step})") :: countSpec step v ops
  | v, .hint :: ops => .exc (.typeError "~no __length_hint__") :: countSpec step v ops

/-- The state invariant: fast mode holds `V` in `cnt` (only with step 1),
slow mode holds it in `long_cnt` with `cnt == PY_SSIZE_T_MAX`. -/
def CountInv (s : CountState) (v step : Int) : Prop :=
  s.longStep = step ∧
  ((s.longCnt = none ∧ s.cnt = v ∧ step = 1 ∧ v ≤ ssizeMax) ∨ (s.longCnt = some v ∧ s.cnt = ssizeMax))

theorem asLongOrMinus1_eq_one (x : Int) : asLongOrMinus1 x = 1 ↔ x = 1 := by
  simp only [asLongOrMinus1, ssizeMin_eq, ssizeMax_eq]
  split <;> omega

theorem countOps_spec (step : Int) : ∀ (ops : List Op) (s : CountState) (v : Int), CountInv s v step →
    cCountOps s ops = countSpec step v ops
  | [], _, _, _ => rfl
  | .next :: ops, s, v, ⟨hst, h⟩ => by
    simp only [cCountOps, countSpec, cCountNext]
    rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
    · by_cases hv : v = ssizeMax
      · simp only [h2, hv, ↓reduceIte, h1, Option.getD]
        rw [countOps_spec step ops _ (ssizeMax + step) ⟨by simp [hst], Or.inr ⟨by simp [hst], by simp⟩⟩]
      · simp only [h2, hv, ↓reduceIte]
        rw [countOps_spec step ops _ (v + step) ⟨by simp [hst], Or.inl ⟨by simp [h1], by simp [h2, h3], h3,
          by rw [h3]; omega⟩⟩]
    · simp only [h2, ↓reduceIte, h1, Option.getD]
      rw [countOps_spec step ops _ (v + step) ⟨by simp [hst], Or.inr ⟨by simp [hst], by simp⟩⟩]
  | .repr :: ops, s, v, ⟨hst, h⟩ => by
    simp only [cCountOps, countSpec, cCountRepr]
    rw [countOps_spec step ops s v ⟨hst, h⟩]
    rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
    · simp [h1, h2, h3]
    · simp only [h1, hst]
      by_cases h1' : step = 1
      · simp [h1', asLongOrMinus1, ssizeMin_eq, ssizeMax_eq]
      · have : ¬ asLongOrMinus1 step = 1 := fun h => h1' ((asLongOrMinus1_eq_one step).1 h)
        simp [h1', this]
  | .hint :: ops, s, v, hinv => by
    simp only [cCountOps, countSpec]
    rw [countOps_spec step ops s v hinv]

theorem countNew_inv (start step : Option Int) :
    CountInv (cCountNew start step) (start.getD 0) (step.getD 1) := by
  have hmax : (0 : Int) ≤ ssizeMax := by decide
  have h11 : asLongOrMinus1 1 = 1 := by simp [asLongOrMinus1, ssizeMin_eq, ssizeMax_eq]
  by_cases h1 : asLongOrMinus1 (step.getD 1) = 1
  · have h1' := (asLongOrMinus1_eq_one _).1 h1
    cases start with
    | none => simp [cCountNew, h1, CountInv, h1', hmax, h11]
    | some s =>
      cases hs : asSsize s with
      | error e => simp [cCountNew, hs, CountInv]
      | ok v =>
        have hv : v = s ∧ s ≤ ssizeMax := by
          simp only [asSsize] at hs; split at hs <;> simp_all
        simp [cCountNew, hs, h1, CountInv, h1', hv.1, hv.2, h11]
  · cases start with
    | none => simp [cCountNew, h1, CountInv]
    | some s =>
      cases hs : asSsize s with
      | error e => simp [cCountNew, hs, CountInv]
      | ok v =>
        have hv : v = s ∧ s ≤ ssizeMax := by
          simp only [asSsize] at hs; split at hs <;> simp_all
        simp [cCountNew, hs, h1, CountInv]

/-- For every int `start` and `step` and every sequence of `next()`/`repr()`
calls, `count` answers as the spec: the C-long fast path and the PyLong slow
path (and the switch at `sys.maxsize`) are invisible. -/
def CountFastSlowConsistent : Prop :=
  ∀ (start step : Option Int) (ops : List Op),
    cCount start step ops = countSpec (step.getD 1) (start.getD 0) ops

theorem countFastSlowConsistent_proven : CountFastSlowConsistent := by
  intro start step ops
  exact countOps_spec _ ops _ _ (countNew_inv start step)

theorem countSpec_values (step : Int) : ∀ (k : Nat) (v : Int),
    countSpec step v (List.replicate k .next) = ((List.range k).map (fun (i : Nat) => v + i * step)).map .int
  | 0, _ => rfl
  | k + 1, v => by
    simp only [List.replicate_succ, countSpec, countSpec_values step k (v + step), List.range_succ_eq_map,
      List.map_cons, List.map_map]
    congr 1
    · simp
    · apply List.map_congr_left; intro i _; simp [Function.comp]; rw [Int.add_mul, Int.one_mul]; omega

/-- `count`'s values are the doc generator's `start, start+step, ...`. -/
def CountDocAgree : Prop :=
  ∀ (start step : Option Int) (k : Nat),
    cCount start step (List.replicate k .next) = (docCountValues start step k).map .int

theorem countDocAgree_proven : CountDocAgree := by
  intro start step k
  rw [countFastSlowConsistent_proven, countSpec_values]
  simp [docCountValues]

/-! ## repeat -/

/-- What `repeat(elem[, times])` should answer, with `rem` the number of items
left (`none`: endless). -/
def repeatSpec (elem : Int) : Option Nat → List Op → List OpRes
  | _, [] => []
  | none, .next :: ops => .int elem :: repeatSpec elem none ops
  | some 0, .next :: ops => .stop :: repeatSpec elem (some 0) ops
  | some (k + 1), .next :: ops => .int elem :: repeatSpec elem (some k) ops
  | none, .repr :: ops => .str s!"repeat({elem})" :: repeatSpec elem none ops
  | some k, .repr :: ops => .str s!"repeat({elem}, {k})" :: repeatSpec elem (some k) ops
  | none, .hint :: ops => .exc (.typeError "len() of unsized object") :: repeatSpec elem none ops
  | some k, .hint :: ops => .int k :: repeatSpec elem (some k) ops

theorem repeatOps_none (elem : Int) : ∀ ops : List Op,
    cRepeatOps { elem := elem, cnt := -1 } ops = repeatSpec elem none ops
  | [] => rfl
  | .next :: ops => by simp [cRepeatOps, cRepeatNext, repeatSpec, repeatOps_none elem ops]
  | .repr :: ops => by simp [cRepeatOps, cRepeatRepr, repeatSpec, repeatOps_none elem ops]
  | .hint :: ops => by simp [cRepeatOps, cRepeatHint, repeatSpec, repeatOps_none elem ops]

theorem repeatOps_some (elem : Int) : ∀ (ops : List Op) (k : Nat),
    cRepeatOps { elem := elem, cnt := k } ops = repeatSpec elem (some k) ops
  | [], _ => rfl
  | .next :: ops, 0 => by
    have := repeatOps_some elem ops 0
    simp only [cRepeatOps, cRepeatNext, repeatSpec]
    simpa using this
  | .next :: ops, k + 1 => by
    have := repeatOps_some elem ops k
    simp only [cRepeatOps, cRepeatNext, repeatSpec]
    simp only [show ((k + 1 : Nat) : Int) ≠ 0 by omega, ↓reduceIte, show ((k + 1 : Nat) : Int) > 0 by omega,
      show ((k + 1 : Nat) : Int) - 1 = (k : Int) by omega, this]
  | .repr :: ops, k => by
    have h : ((k : Nat) : Int) ≠ -1 := by omega
    simp [cRepeatOps, cRepeatRepr, repeatSpec, repeatOps_some elem ops k, h]
    rfl
  | .hint :: ops, k => by
    have h : ((k : Nat) : Int) ≠ -1 := by omega
    simp [cRepeatOps, cRepeatHint, repeatSpec, repeatOps_some elem ops k, h]

/-- For `times` omitted or a `Py_ssize_t` (negative meaning 0), every
sequence of `next()`, `repr()` and `__length_hint__()` calls answers as the
spec: `__length_hint__` is exactly the number of items left. -/
def RepeatConsistent : Prop :=
  ∀ (elem : Int) (times : Option Int) (ops : List Op), (∀ t, times = some t → InSsize t) →
    cRepeat elem times ops = repeatSpec elem (times.map Int.toNat) ops

theorem repeatConsistent_proven : RepeatConsistent := by
  intro elem times ops h
  cases times with
  | none => exact repeatOps_none elem ops
  | some t =>
    have ht := h t rfl
    simp only [InSsize] at ht
    simp only [cRepeat, cRepeatNew, asSsize, ht, and_self, ↓reduceIte, bind, Except.bind, pure,
      Except.pure, Option.map]
    by_cases h0 : t < 0
    · simp only [h0, ↓reduceIte]
      rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, repeatOps_some, Int.toNat_of_nonpos (by omega)]
    · simp only [h0, ↓reduceIte]
      obtain ⟨n, rfl⟩ : ∃ n : Nat, t = n := ⟨t.toNat, by omega⟩
      rw [repeatOps_some]
      simp

/-- The ints produced by a sequence of `next()` calls. -/
def opInts (rs : List OpRes) : List Int :=
  rs.filterMap (fun r => match r with | .int v => some v | _ => none)

/-- Broad: `repeat` produces the doc generator's items for every int `times`. -/
def RepeatDocAgree : Prop :=
  ∀ (elem : Int) (times : Option Int) (k : Nat),
    opInts (cRepeat elem times (List.replicate k .next)) = docRepeatValues elem times k

theorem repeatDocAgree_refuted : ¬RepeatDocAgree := by
  intro h
  have := h 0 (some (2 ^ 63)) 1
  revert this
  decide

theorem repeatSpec_values (elem : Int) : ∀ (k : Nat) (rem : Option Nat),
    opInts (repeatSpec elem rem (List.replicate k .next)) =
      List.replicate (match rem with | none => k | some r => min k r) elem
  | 0, rem => by cases rem <;> rfl
  | k + 1, none => by
    simp only [List.replicate_succ, repeatSpec, opInts, List.filterMap_cons]
    have := repeatSpec_values elem k none
    simp only [opInts] at this
    rw [this]
  | k + 1, some 0 => by
    simp only [List.replicate_succ, repeatSpec, opInts, List.filterMap_cons]
    have := repeatSpec_values elem k (some 0)
    simp only [opInts] at this
    rw [this]; simp
  | k + 1, some (r + 1) => by
    simp only [List.replicate_succ, repeatSpec, opInts, List.filterMap_cons]
    have := repeatSpec_values elem k (some r)
    simp only [opInts] at this
    rw [this, show min (k + 1) (r + 1) = min k r + 1 by omega, List.replicate_succ]

/-- Narrowed to `Py_ssize_t` `times`: the items are the doc generator's. -/
def RepeatDocAgreeSsize : Prop :=
  ∀ (elem : Int) (times : Option Int) (k : Nat), (∀ t, times = some t → InSsize t) →
    opInts (cRepeat elem times (List.replicate k .next)) = docRepeatValues elem times k

theorem repeatDocAgreeSsize_proven : RepeatDocAgreeSsize := by
  intro elem times k h
  rw [repeatConsistent_proven elem times _ h, repeatSpec_values]
  cases times <;> simp [docRepeatValues]

end PyLean.Itertools
