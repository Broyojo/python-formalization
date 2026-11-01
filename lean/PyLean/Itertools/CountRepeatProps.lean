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

variable {ν : Type}

/-- What `count(start, step)` should answer, for every kind of number: `next()`
adds first, so a failed add raises in place of `v` and changes nothing; `repr`
shows the current value, and the step unless it is an int equal to 1. -/
def countSpec (N : NumOps ν) (ty : String) (step : CVal ν) : CVal ν → List Op → List (OpRes (CVal ν))
  | _, [] => []
  | v, .next :: ops =>
    match pyAdd N v step with
    | .error e => .exc e :: countSpec N ty step v ops
    | .ok u => .val v :: countSpec N ty step u ops
  | v, .repr :: ops =>
    reprRes (cCountRepr N ty { cnt := ssizeMax, longCnt := some v, longStep := step }) ::
      countSpec N ty step v ops
  | v, .hint :: ops => .exc (.typeError "~no __length_hint__") :: countSpec N ty step v ops

/-- The state invariant: fast mode holds `V` in `cnt` (only with the exact int 1 as
step), slow mode holds it in `long_cnt` with `cnt == PY_SSIZE_T_MAX`. -/
def CountInv (s : CountState ν) (v step : CVal ν) : Prop :=
  s.longStep = step ∧
  ((∃ i : Int, s.longCnt = none ∧ s.cnt = i ∧ v = .int i ∧ step = .int 1 ∧ i ≤ ssizeMax) ∨
    (s.longCnt = some v ∧ s.cnt = ssizeMax))

theorem asLongOrMinus1_eq_one (x : Int) : asLongOrMinus1 x = 1 ↔ x = 1 := by
  simp only [asLongOrMinus1, ssizeMin_eq, ssizeMax_eq]
  split <;> omega

theorem stepIsOne_one : stepIsOne (.int 1 : CVal ν) = true := by
  simp [stepIsOne, CVal.isLong, CVal.longVal, asLongOrMinus1, ssizeMin_eq, ssizeMax_eq]

theorem countOps_spec (N : NumOps ν) (ty : String) (step : CVal ν) : ∀ (ops : List Op) (s : CountState ν)
    (v : CVal ν), CountInv s v step → cCountOps N ty s ops = countSpec N ty step v ops
  | [], _, _, _ => rfl
  | .next :: ops, s, v, ⟨hst, h⟩ => by
    simp only [cCountOps, countSpec, cCountNext]
    rcases h with ⟨i, h1, h2, rfl, rfl, h4⟩ | ⟨h1, h2⟩
    · by_cases hv : i = ssizeMax
      · subst hv
        simp only [h2, ↓reduceIte, h1, Option.getD, hst, pyAdd]
        rw [countOps_spec N ty _ ops _ (.int (ssizeMax + 1)) ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩]
      · simp only [h2, hv, ↓reduceIte, pyAdd]
        rw [countOps_spec N ty _ ops { s with cnt := i + 1 } (.int (i + 1))
          ⟨hst, Or.inl ⟨i + 1, h1, rfl, rfl, rfl, by omega⟩⟩]
    · simp only [h2, ↓reduceIte, h1, Option.getD, hst]
      cases ha : pyAdd N v step with
      | error e =>
        simp only
        rw [countOps_spec N ty step ops s v ⟨hst, Or.inr ⟨h1, h2⟩⟩]
      | ok u =>
        simp only
        rw [countOps_spec N ty step ops { cnt := ssizeMax, longCnt := some u, longStep := step } u
          ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩]
  | .repr :: ops, s, v, ⟨hst, h⟩ => by
    simp only [cCountOps, countSpec]
    rw [countOps_spec N ty step ops s v ⟨hst, h⟩]
    rcases h with ⟨i, h1, h2, rfl, rfl, h4⟩ | ⟨h1, h2⟩
    · simp [cCountRepr, h1, h2, stepIsOne_one, pyRepr] <;> rfl
    · simp [cCountRepr, h1, hst]
  | .hint :: ops, s, v, hinv => by
    simp only [cCountOps, countSpec]
    rw [countOps_spec N ty step ops s v hinv]

/-- An argument that is not an int subclass. -/
def NoIntSub (a : Option (CVal ν)) : Prop := ∀ i x, a ≠ some (.intSub i x)

theorem countNew_inv (start step : Option (CVal ν)) (hs : NoIntSub start) (ht : NoIntSub step)
    (h1 : argBad start = false) (h2 : argBad step = false) :
    ∃ s, cCountNew start step = .ok s ∧ CountInv s (start.getD (.int 0)) (step.getD (.int 1)) := by
  have hone : asLongOrMinus1 1 = 1 := by simp [asLongOrMinus1, ssizeMin_eq, ssizeMax_eq]
  have hmax : (0 : Int) ≤ ssizeMax := by decide
  have hslow : ∀ (lc : CVal ν), CountInv { cnt := ssizeMax, longCnt := some lc, longStep := step.getD (.int 1) }
      lc (step.getD (.int 1)) := fun lc => ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩
  cases start with
  | none =>
    cases step with
    | none =>
      exact ⟨_, by simp [cCountNew, argBad, argLong, CVal.longVal, hone] <;> rfl,
        ⟨rfl, Or.inl ⟨0, rfl, rfl, rfl, rfl, hmax⟩⟩⟩
    | some t =>
      cases t with
      | int j =>
        by_cases hj : j = 1
        · subst hj
          exact ⟨_, by simp [cCountNew, argBad, argLong, CVal.isNumber, CVal.isLong, CVal.longVal, hone] <;> rfl,
            ⟨rfl, Or.inl ⟨0, rfl, rfl, rfl, rfl, hmax⟩⟩⟩
        · have hne : asLongOrMinus1 j ≠ 1 := fun h => hj ((asLongOrMinus1_eq_one j).1 h)
          exact ⟨_, by simp [cCountNew, argBad, argLong, CVal.isNumber, CVal.isLong, CVal.longVal, hne] <;> rfl,
            hslow _⟩
      | intSub i x => exact absurd rfl (ht i x)
      | num x =>
        exact ⟨_, by simp [cCountNew, argBad, argLong, CVal.isNumber, CVal.isLong, CVal.longVal, hone] <;> rfl,
          hslow _⟩
      | nonNum x => simp [argBad, CVal.isNumber] at h2
  | some a =>
    cases a with
    | int i =>
      cases hi : asSsize i with
      | error e =>
        exact ⟨_, by
          cases step with
          | none => simp [cCountNew, argBad, argLong, CVal.isNumber, CVal.isLong, CVal.longVal, hi] <;> rfl
          | some t =>
            cases t <;> simp_all [cCountNew, argBad, argLong, CVal.isNumber, CVal.isLong, CVal.longVal, hi] <;> rfl,
          hslow _⟩
      | ok v =>
        have hv : v = i ∧ i ≤ ssizeMax := by
          simp only [asSsize] at hi; split at hi <;> simp_all
        obtain ⟨rfl, hle⟩ := hv
        cases step with
        | none =>
          exact ⟨_, by simp [cCountNew, argBad, argLong, CVal.isNumber, CVal.isLong, CVal.longVal, hi, hone] <;> rfl,
            ⟨rfl, Or.inl ⟨v, rfl, rfl, rfl, rfl, hle⟩⟩⟩
        | some t =>
          cases t with
          | int j =>
            by_cases hj : j = 1
            · subst hj
              exact ⟨_, by simp [cCountNew, argBad, argLong, CVal.isNumber, CVal.isLong, CVal.longVal, hi, hone] <;> rfl,
                ⟨rfl, Or.inl ⟨v, rfl, rfl, rfl, rfl, hle⟩⟩⟩
            · have hne : asLongOrMinus1 j ≠ 1 := fun h => hj ((asLongOrMinus1_eq_one j).1 h)
              exact ⟨_, by simp [cCountNew, argBad, argLong, CVal.isNumber, CVal.isLong, CVal.longVal, hi, hne] <;> rfl,
                hslow _⟩
          | intSub i x => exact absurd rfl (ht i x)
          | num x =>
            exact ⟨_, by simp [cCountNew, argBad, argLong, CVal.isNumber, CVal.isLong, CVal.longVal] <;> rfl,
              hslow _⟩
          | nonNum x => simp [argBad, CVal.isNumber] at h2
    | intSub i x => exact absurd rfl (hs i x)
    | num x =>
      have hf : argLong (some (CVal.num x)) = false := rfl
      exact ⟨_, by
        simp only [cCountNew, h1, h2, Bool.or_self, Bool.false_eq_true, if_false, hf, Bool.false_and]
        rfl, hslow _⟩
    | nonNum x => simp [argBad, CVal.isNumber] at h1

/-- For all number types, every start and step that are numbers but not int
subclasses, and every sequence of `next()`/`repr()` calls, `count` answers as the
spec: the C-long fast path and the object slow path, and the switch at
`sys.maxsize`, are invisible, including a failed add and a failed `repr`. The
hypothesis on int subclasses is real: see `CountDocAgreeTotalAdd`. -/
def CountConsistent : Prop :=
  ∀ (ν : Type) (N : NumOps ν) (ty : String) (start step : Option (CVal ν)) (ops : List Op),
    NoIntSub start → NoIntSub step → argBad start = false → argBad step = false →
    cCount N start step ops ty = countSpec N ty (step.getD (.int 1)) (start.getD (.int 0)) ops

theorem countConsistent_proven : CountConsistent := by
  intro ν N ty start step ops h1 h2 h3 h4
  obtain ⟨s, hs, hinv⟩ := countNew_inv start step h1 h2 h3 h4
  simp only [cCount, hs]
  exact countOps_spec N ty _ ops s _ hinv

/-- For every int `start` and `step` and every sequence of `next()`/`repr()`
calls, `count` gives `start + k*step` and its `repr` is `count(V)` or
`count(V, step)`: the fast path and the slow path are invisible, for ints with no
hypothesis at all. -/
def intSpec (ty : String) (step : Int) : Int → List Op → List (OpRes (CVal ν))
  | _, [] => []
  | v, .next :: ops => .val (.int v) :: intSpec ty step (v + step) ops
  | v, .repr :: ops =>
    .str (if step = 1 then s!"{ty}({v})" else s!"{ty}({v}, {step})") :: intSpec ty step v ops
  | v, .hint :: ops => .exc (.typeError "~no __length_hint__") :: intSpec ty step v ops

theorem countSpec_int (N : NumOps ν) (ty : String) (step : Int) : ∀ (ops : List Op) (v : Int),
    countSpec N ty (.int step) (.int v) ops = intSpec ty step v ops
  | [], _ => rfl
  | .next :: ops, v => by
    simp only [countSpec, intSpec, pyAdd]
    rw [countSpec_int N ty step ops]
  | .repr :: ops, v => by
    simp only [countSpec, intSpec]
    rw [countSpec_int N ty step ops]
    by_cases h : step = 1
    · subst h
      simp [cCountRepr, stepIsOne_one, pyRepr, reprRes] <;> rfl
    · have hne : ¬ asLongOrMinus1 step = 1 := fun h' => h ((asLongOrMinus1_eq_one step).1 h')
      simp [cCountRepr, stepIsOne, CVal.isLong, CVal.longVal, hne, pyRepr, reprRes, h] <;> rfl
  | .hint :: ops, v => by
    simp only [countSpec, intSpec]
    rw [countSpec_int N ty step ops]

def CountFastSlowConsistent : Prop :=
  ∀ (ν : Type) (N : NumOps ν) (ty : String) (start step : Option Int) (ops : List Op),
    cCount N (start.map .int) (step.map .int) ops ty = intSpec ty (step.getD 1) (start.getD 0) ops

theorem countFastSlowConsistent_proven : CountFastSlowConsistent := by
  intro ν N ty start step ops
  have h := countConsistent_proven ν N ty (start.map .int) (step.map .int) ops
    (by cases start <;> simp [NoIntSub]) (by cases step <;> simp [NoIntSub])
    (by cases start <;> simp [argBad, CVal.isNumber]) (by cases step <;> simp [argBad, CVal.isNumber])
  rw [h]
  have e1 : (step.map (CVal.int (ν := ν))).getD (.int 1) = .int (step.getD 1) := by cases step <;> rfl
  have e2 : (start.map (CVal.int (ν := ν))).getD (.int 0) = .int (start.getD 0) := by cases start <;> rfl
  rw [e1, e2, countSpec_int]

/-- `count(a, b)` raises exactly for non-numbers (:3538-3542), and the fast path is
taken exactly when both are ints, the start fits a `Py_ssize_t` and the step is 1
(:3544-3585). Otherwise `cnt` is `PY_SSIZE_T_MAX`, as the asserts at :3587-3590
say. For every number type. -/
def CountNewModes : Prop :=
  ∀ (ν : Type) (a b : Option (CVal ν)),
    ((argBad a || argBad b) = true → cCountNew a b = .error (.typeError "a number is required")) ∧
    ∀ s, cCountNew a b = .ok s →
      (s.longCnt = none ∨ s.cnt = ssizeMax) ∧
      (s.longCnt = none ↔ (argLong a = true ∧ argLong b = true ∧
        (∀ x, a = some x → InSsize x.longVal) ∧ asLongOrMinus1 (b.getD (.int 1)).longVal = 1))

theorem asSsize_of_not_in (x : Int) (h : ¬ InSsize x) : ∃ e, asSsize x = .error e := by
  simp only [InSsize] at h
  simp only [asSsize, h, if_false]
  exact ⟨_, rfl⟩

theorem countNewModes_proven : CountNewModes := by
  intro ν a b
  refine ⟨fun h => by simp [cCountNew, h], ?_⟩
  intro s h
  simp only [cCountNew] at h
  by_cases hbad : (argBad a || argBad b) = true
  · simp [hbad] at h
  · simp only [hbad, Bool.false_eq_true, if_false] at h
    cases hsa : argLong a && argLong b with
    | false =>
      -- not both ints: slow
      have hnot : ¬ (argLong a = true ∧ argLong b = true) := by
        intro ⟨p, q⟩
        simp [p, q] at hsa
      have hs : s.longCnt ≠ none ∧ s.cnt = ssizeMax := by
        cases a with
        | none => simp [hsa] at h; simp [← h]
        | some x => simp [hsa] at h; simp [← h]
      exact ⟨Or.inr hs.2, ⟨fun e => absurd e hs.1, fun ⟨p, q, _⟩ => absurd ⟨p, q⟩ hnot⟩⟩
    | true =>
      have hab : argLong a = true ∧ argLong b = true := by simpa using hsa
      cases a with
      | none =>
        by_cases ho : asLongOrMinus1 (b.getD (.int 1)).longVal = 1
        · simp [hsa, ho] at h
          simp [← h, hab.2, ho, show argLong (none : Option (CVal ν)) = true from rfl]
        · simp [hsa, ho] at h
          simp [← h, ho]
      | some x =>
        by_cases hx : InSsize x.longVal
        · have hok : asSsize x.longVal = .ok x.longVal := by
            simp only [InSsize] at hx
            simp only [asSsize, hx, if_true]
            simp
          by_cases ho : asLongOrMinus1 (b.getD (.int 1)).longVal = 1
          · simp [hsa, hok, ho] at h
            simp [← h, hab.1, hab.2, ho, hx]
          · simp [hsa, hok, ho] at h
            simp [← h, ho]
        · obtain ⟨e, he⟩ := asSsize_of_not_in _ hx
          simp [hsa, he] at h
          simp [← h, hx]

/-- The items and end seen by `k` calls of `next()`, stopping at an exception. -/
def opVals {β : Type} : List (OpRes β) → Run β
  | [] => ([], none)
  | .val v :: l => let r := opVals l; (v :: r.1, r.2)
  | .exc e :: _ => ([], some e)
  | _ :: l => opVals l

/-- Broad: `count` gives the doc generator's values and end, for all numbers. -/
def CountDocAgreeAll : Prop :=
  ∀ (ν : Type) (N : NumOps ν) (start step : CVal ν) (k : Nat),
    start.isNumber = true → step.isNumber = true →
    opVals (cCount N (some start) (some step) (List.replicate k .next)) = docCountRun N step k start

/-- A set of values that adding the step never leaves and never fails on: for
example all floats with a float step. -/
def AddClosed (N : NumOps ν) (step : CVal ν) (P : CVal ν → Prop) : Prop :=
  ∀ a, P a → ∃ b, pyAdd N a step = .ok b ∧ P b

/-- Narrowed to adds that cannot fail. The doc generator and C then differ only
through int subclasses: `count(True)` gives the int 1 where the doc gives `True`. -/
def CountDocAgreeTotalAdd : Prop :=
  ∀ (ν : Type) (N : NumOps ν) (start step : CVal ν) (P : CVal ν → Prop) (k : Nat),
    start.isNumber = true → step.isNumber = true → AddClosed N step P → P start →
    opVals (cCount N (some start) (some step) (List.replicate k .next)) = docCountRun N step k start

/-- With no int subclass either, for every number type: `count` gives the doc
generator's values, for every `k`. Hypotheses, both documented or type-level: adding
the step never fails on the values reached (`CountFailedAddRaisesFirst` says what
happens otherwise), and neither argument is an int subclass. -/
def CountDocAgreeClosed : Prop :=
  ∀ (ν : Type) (N : NumOps ν) (start step : CVal ν) (P : CVal ν → Prop) (k : Nat),
    start.isNumber = true → step.isNumber = true →
    NoIntSub (some start) → NoIntSub (some step) → AddClosed N step P → P start →
    opVals (cCount N (some start) (some step) (List.replicate k .next)) = docCountRun N step k start

theorem countSpec_closed (N : NumOps ν) (ty : String) (step : CVal ν) (P : CVal ν → Prop)
    (hc : AddClosed N step P) : ∀ (k : Nat) (v : CVal ν), P v →
    opVals (countSpec N ty step v (List.replicate k .next)) = docCountRun N step k v
  | 0, _, _ => rfl
  | 1, v, hv => by
    obtain ⟨u, hu, _⟩ := hc v hv
    simp [List.replicate, countSpec, hu, opVals, docCountRun]
  | k + 2, v, hv => by
    obtain ⟨u, hu, hp⟩ := hc v hv
    have := countSpec_closed N ty step P hc (k + 1) u hp
    rw [List.replicate_succ]
    simp only [countSpec, hu, opVals, docCountRun, this]

theorem countDocAgreeClosed_proven : CountDocAgreeClosed := by
  intro ν N start step P k h1 h2 h3 h4 hc hp
  have hb1 : argBad (some start) = false := by simp [argBad, h1]
  have hb2 : argBad (some step) = false := by simp [argBad, h2]
  have h := countConsistent_proven ν N "count" (some start) (some step) (List.replicate k .next) h3 h4 hb1 hb2
  simp only [Option.getD_some] at h
  rw [h]
  exact countSpec_closed N "count" step P hc k start hp

/-- For every number type and state in slow mode, when adding the step to the
current value `v` fails: `next()` raises that exception, not returning `v`, and
leaves the state as it was, so `v` is still there for `repr` and the next attempt
(:3643-3647). -/
def CountFailedAddRaisesFirst : Prop :=
  ∀ (ν : Type) (N : NumOps ν) (s : CountState ν) (v : CVal ν) (e : PyExc),
    s.cnt = ssizeMax → s.longCnt = some v → pyAdd N v s.longStep = .error e →
    cCountNext N s = (.exc e, s)

theorem countFailedAddRaisesFirst_proven : CountFailedAddRaisesFirst := by
  intro ν N s v e h1 h2 h3
  simp [cCountNext, h1, h2, h3]

/-! ## repeat -/

variable {α : Type}

/-- What `repeat(elem[, times])` should answer, with `rem` the number of items
left (`none`: endless). -/
def repeatSpec (rp : α → String) (elem : α) : Option Nat → List Op → List (OpRes α ⊕ OpRes Int)
  | _, [] => []
  | none, .next :: ops => .inl (.val elem) :: repeatSpec rp elem none ops
  | some 0, .next :: ops => .inl .stop :: repeatSpec rp elem (some 0) ops
  | some (k + 1), .next :: ops => .inl (.val elem) :: repeatSpec rp elem (some k) ops
  | none, .repr :: ops => .inr (.str s!"repeat({rp elem})") :: repeatSpec rp elem none ops
  | some k, .repr :: ops => .inr (.str s!"repeat({rp elem}, {k})") :: repeatSpec rp elem (some k) ops
  | none, .hint :: ops =>
    .inr (.exc (.typeError "len() of unsized object")) :: repeatSpec rp elem none ops
  | some k, .hint :: ops => .inr (.val k) :: repeatSpec rp elem (some k) ops

theorem repeatOps_none (rp : α → String) (elem : α) : ∀ ops : List Op,
    cRepeatOps rp { elem := elem, cnt := -1 } ops = repeatSpec rp elem none ops
  | [] => rfl
  | .next :: ops => by simp [cRepeatOps, cRepeatNext, repeatSpec, repeatOps_none rp elem ops]
  | .repr :: ops => by simp [cRepeatOps, cRepeatRepr, repeatSpec, repeatOps_none rp elem ops]
  | .hint :: ops => by simp [cRepeatOps, cRepeatHint, repeatSpec, repeatOps_none rp elem ops]

theorem repeatOps_some (rp : α → String) (elem : α) : ∀ (ops : List Op) (k : Nat),
    cRepeatOps rp { elem := elem, cnt := k } ops = repeatSpec rp elem (some k) ops
  | [], _ => rfl
  | .next :: ops, 0 => by
    have := repeatOps_some rp elem ops 0
    simp only [cRepeatOps, cRepeatNext, repeatSpec]
    simpa using this
  | .next :: ops, k + 1 => by
    have := repeatOps_some rp elem ops k
    simp only [cRepeatOps, cRepeatNext, repeatSpec]
    simp only [show ((k + 1 : Nat) : Int) ≠ 0 by omega, ↓reduceIte, show ((k + 1 : Nat) : Int) > 0 by omega,
      show ((k + 1 : Nat) : Int) - 1 = (k : Int) by omega, this]
  | .repr :: ops, k => by
    have h : ((k : Nat) : Int) ≠ -1 := by omega
    simp [cRepeatOps, cRepeatRepr, repeatSpec, repeatOps_some rp elem ops k, h]
    rfl
  | .hint :: ops, k => by
    have h : ((k : Nat) : Int) ≠ -1 := by omega
    simp [cRepeatOps, cRepeatHint, repeatSpec, repeatOps_some rp elem ops k, h]

/-- For `times` omitted or a `Py_ssize_t` (negative meaning 0), every
sequence of `next()`, `repr()` and `__length_hint__()` calls answers as the
spec: `__length_hint__` is exactly the number of items left. Over any element
type, for any `repr` of it. -/
def RepeatConsistent : Prop :=
  ∀ (α : Type) (rp : α → String) (elem : α) (times : Option Int) (ops : List Op),
    (∀ t, times = some t → InSsize t) →
    cRepeat rp elem times ops = repeatSpec rp elem (times.map Int.toNat) ops

theorem repeatConsistent_proven : RepeatConsistent := by
  intro α rp elem times ops h
  cases times with
  | none => exact repeatOps_none rp elem ops
  | some t =>
    have ht := h t rfl
    simp only [InSsize] at ht
    simp only [cRepeat, cRepeatNew, asSsize, ht, and_self, ↓reduceIte, Option.map]
    by_cases h0 : t < 0
    · simp only [h0, ↓reduceIte]
      rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, repeatOps_some, Int.toNat_of_nonpos (by omega)]
    · simp only [h0, ↓reduceIte]
      obtain ⟨n, rfl⟩ : ∃ n : Nat, t = n := ⟨t.toNat, by omega⟩
      rw [repeatOps_some]
      simp

/-- The items produced by a sequence of `next()` calls. -/
def opItems (rs : List (OpRes α ⊕ OpRes Int)) : List α :=
  rs.filterMap (fun r => match r with | .inl (.val v) => some v | _ => none)

/-- Broad: `repeat` produces the doc generator's items for every int `times`. -/
def RepeatDocAgree : Prop :=
  ∀ (α : Type) (rp : α → String) (elem : α) (times : Option Int) (k : Nat),
    opItems (cRepeat rp elem times (List.replicate k .next)) = docRepeatValues elem times k

theorem repeatDocAgree_refuted : ¬RepeatDocAgree := by
  intro h
  have := h Int (fun _ => "") 0 (some (2 ^ 63)) 1
  revert this
  decide

theorem repeatSpec_values (rp : α → String) (elem : α) : ∀ (k : Nat) (rem : Option Nat),
    opItems (repeatSpec rp elem rem (List.replicate k .next)) =
      List.replicate (match rem with | none => k | some r => min k r) elem
  | 0, rem => by cases rem <;> rfl
  | k + 1, none => by
    simp only [List.replicate_succ, repeatSpec, opItems, List.filterMap_cons]
    have := repeatSpec_values rp elem k none
    simp only [opItems] at this
    rw [this]
  | k + 1, some 0 => by
    simp only [List.replicate_succ, repeatSpec, opItems, List.filterMap_cons]
    have := repeatSpec_values rp elem k (some 0)
    simp only [opItems] at this
    rw [this]; simp
  | k + 1, some (r + 1) => by
    simp only [List.replicate_succ, repeatSpec, opItems, List.filterMap_cons]
    have := repeatSpec_values rp elem k (some r)
    simp only [opItems] at this
    rw [this, show min (k + 1) (r + 1) = min k r + 1 by omega, List.replicate_succ]

/-- Narrowed to `Py_ssize_t` `times`: the items are the doc generator's. -/
def RepeatDocAgreeSsize : Prop :=
  ∀ (α : Type) (rp : α → String) (elem : α) (times : Option Int) (k : Nat),
    (∀ t, times = some t → InSsize t) →
    opItems (cRepeat rp elem times (List.replicate k .next)) = docRepeatValues elem times k

theorem repeatDocAgreeSsize_proven : RepeatDocAgreeSsize := by
  intro α rp elem times k h
  rw [repeatConsistent_proven α rp elem times _ h, repeatSpec_values]
  cases times <;> simp [docRepeatValues]

end PyLean.Itertools
