import PyLean.Itertools.Islice

/-!
Properties of `islice`: the C object against the doc equivalent, layered as in
`Accel` (broad statement refuted, narrowed statements proven), plus the doc
sentence about how much input is consumed.
-/

namespace PyLean.Itertools

open PyLean

/-! ## Arithmetic helpers -/

theorem ssizeMax_eq : ssizeMax = 9223372036854775807 := by decide
theorem ssizeMin_eq : ssizeMin = -9223372036854775808 := by decide

theorem wrapSsize_id (x : Int) (h1 : ssizeMin ≤ x) (h2 : x ≤ ssizeMax) : wrapSsize x = x := by
  rw [ssizeMin_eq] at h1
  rw [ssizeMax_eq] at h2
  simp only [wrapSsize, two64, ssizeMax_eq]
  by_cases h : x % 18446744073709551616 > 9223372036854775807
  · simp only [h, ↓reduceIte]; omega
  · simp only [h, ↓reduceIte]; omega

theorem wrapSsize_over (x : Int) (h1 : ssizeMax < x) (h2 : x ≤ 2 * ssizeMax) : wrapSsize x = x - two64 := by
  rw [ssizeMax_eq] at h1 h2
  simp only [wrapSsize, two64, ssizeMax_eq]
  by_cases h : x % 18446744073709551616 > 9223372036854775807
  · simp only [h, ↓reduceIte]; omega
  · simp only [h, ↓reduceIte]; omega

/-! ## The skip loop -/

theorem cIsliceSkip_ge (p : Int) : ∀ (xs : List Int) (i : Int), p ≤ i → cIsliceSkip p xs i = (some xs, i)
  | [], i, h => by simp [cIsliceSkip]; omega
  | x :: xs, i, h => by simp [cIsliceSkip]; omega

theorem cIsliceSkip_lt (p : Int) : ∀ (xs : List Int) (k : Nat) (i : Int), i + k = p →
    cIsliceSkip p xs i = if k ≤ xs.length then (some (xs.drop k), p) else (none, i + xs.length)
  | [], k, i, h => by
    cases k with
    | zero =>
      obtain rfl : p = i := by omega
      simp [cIsliceSkip]
    | succ k =>
      have : i < p := by omega
      simp [cIsliceSkip, this]
  | x :: xs, k, i, h => by
    cases k with
    | zero =>
      obtain rfl : p = i := by omega
      simp [cIsliceSkip]
    | succ k =>
      have ih := cIsliceSkip_lt p xs k (i + 1) (by omega)
      have hip : i < p := by omega
      simp only [cIsliceSkip, hip, ↓reduceIte, ih, List.length_cons, List.drop_succ_cons]
      by_cases hk : k ≤ xs.length
      · simp [hk]
      · simp [hk]; omega

/-! ## The doc loop -/

/-- Abbreviation for the doc loop. -/
local notation "D" => docIsliceLoop

/-- The bound does not stop the loop at position `j`. -/
def BoundAbove (bound : Option Int) (j : Int) : Prop :=
  match bound with
  | none => True
  | some m => j < m

theorem boundCheck_false {bound : Option Int} {j : Int} (h : BoundAbove bound j) :
    pastBound bound j = false := by
  cases bound with
  | none => rfl
  | some m => simp only [BoundAbove] at h; simp [pastBound]; omega

theorem D_nil (bound : Option Int) (st i q : Int) : D bound st i q [] = ([], 0) := by
  simp [docIsliceLoop]

theorem D_stop (B st i q : Int) (xs : List Int) (h : B ≤ i) : D (some B) st i q xs = ([], 0) := by
  cases xs with
  | nil => simp [docIsliceLoop]
  | cons x xs => simp [docIsliceLoop, pastBound]; omega

theorem D_yield (bound : Option Int) (st i : Int) (x : Int) (xs : List Int) (h : BoundAbove bound i) :
    D bound st i i (x :: xs) = (x :: (D bound st (i + 1) (i + st) xs).1, (D bound st (i + 1) (i + st) xs).2 + 1) := by
  simp only [docIsliceLoop, boundCheck_false h]
  simp

/-- Skipping `k` items that are before `nextI` and below the bound. -/
theorem D_skip (bound : Option Int) (st : Int) : ∀ (k : Nat) (xs : List Int) (i q : Int),
    i + k ≤ q → (∀ j, i ≤ j → j < i + k → BoundAbove bound j) → k ≤ xs.length →
    D bound st i q xs = ((D bound st (i + k) q (xs.drop k)).1, (D bound st (i + k) q (xs.drop k)).2 + k)
  | 0, xs, i, q, _, _, _ => by simp
  | k + 1, [], _, _, _, _, hl => by simp at hl
  | k + 1, x :: xs, i, q, hq, hb, hl => by
    have hbi : BoundAbove bound i := hb i (by omega) (by omega)
    have hne : ¬ i = q := by omega
    have ih := D_skip bound st k xs (i + 1) q (by omega) (fun j h1 h2 => hb j (by omega) (by omega))
      (by simp at hl; omega)
    simp only [docIsliceLoop, boundCheck_false hbi, hne, Bool.false_eq_true, ↓reduceIte, ih,
      List.drop_succ_cons]
    simp only [Prod.mk.injEq]
    constructor
    · congr 2; push_cast; omega
    · have : i + 1 + (k : Int) = i + ((k + 1 : Nat) : Int) := by push_cast; omega
      rw [this]; omega

/-- Consumption of the doc loop: everything below the bound. -/
theorem D_consumed_some (B st : Int) : ∀ (xs : List Int) (i q : Int),
    ((D (some B) st i q xs).2 : Int) = min (xs.length : Int) (max 0 (B - i))
  | [], i, q => by simp [docIsliceLoop]; omega
  | x :: xs, i, q => by
    by_cases h : B ≤ i
    · rw [D_stop B st i q _ h]; simp; omega
    · have hb : BoundAbove (some B) i := by simp [BoundAbove]; omega
      simp only [docIsliceLoop, boundCheck_false hb]
      by_cases hiq : i = q
      · simp only [hiq, ↓reduceIte, Bool.false_eq_true]
        have := D_consumed_some B st xs (q + 1) (q + st)
        simp only [List.length_cons]; push_cast; omega
      · simp only [hiq, ↓reduceIte, Bool.false_eq_true]
        have := D_consumed_some B st xs (i + 1) q
        simp only [List.length_cons]; push_cast; omega

theorem D_consumed_none (st : Int) : ∀ (xs : List Int) (i q : Int), (D none st i q xs).2 = xs.length
  | [], i, q => by simp [docIsliceLoop]
  | x :: xs, i, q => by
    simp only [docIsliceLoop, boundCheck_false (show BoundAbove none i from trivial)]
    by_cases hiq : i = q
    · simp only [hiq, ↓reduceIte, Bool.false_eq_true, D_consumed_none st xs, List.length_cons]
    · simp only [hiq, ↓reduceIte, Bool.false_eq_true, D_consumed_none st xs, List.length_cons]

/-- Nothing is yielded once `nextI` is at or above the bound. -/
theorem D_noyield (B st : Int) : ∀ (xs : List Int) (i q : Int), B ≤ q → (D (some B) st i q xs).1 = []
  | [], i, q, _ => by simp [docIsliceLoop]
  | x :: xs, i, q, h => by
    by_cases hb : B ≤ i
    · rw [D_stop B st i q _ hb]
    · have hb' : BoundAbove (some B) i := by simp [BoundAbove]; omega
      have hiq : ¬ i = q := by omega
      simp only [docIsliceLoop, boundCheck_false hb', hiq, Bool.false_eq_true, ↓reduceIte]
      exact D_noyield B st xs (i + 1) q h

/-! ## The C object -/

/-- The C run with `stop=None`, as long as `lz->next += step` cannot wrap. -/
theorem cRun_none : ∀ (fuel : Nat) (xs : List Int) (i p st : Int),
    xs.length < fuel → 0 ≤ i → i ≤ p → 1 ≤ st → i + xs.length + st ≤ ssizeMax + 1 →
    (drainSt cIsliceNext fuel { it := some xs, next := p, stop := -1, step := st, cnt := i }).1
        = Run.ok (D none st i p xs).1 ∧
    (drainSt cIsliceNext fuel { it := some xs, next := p, stop := -1, step := st, cnt := i }).2.cnt
        = i + (D none st i p xs).2
  | 0, xs, _, _, _, h, _, _, _, _ => by simp at h
  | fuel + 1, xs, i, p, st, hf, hi, hip, hst, hw => by
    obtain ⟨k, hk⟩ : ∃ k : Nat, i + k = p := ⟨(p - i).toNat, by omega⟩
    have hsk := cIsliceSkip_lt p xs k i hk
    by_cases hkl : k ≤ xs.length
    · rw [if_pos hkl] at hsk
      have hD := D_skip none st k xs i p (by omega) (fun _ _ _ => trivial) hkl
      rw [show i + (k : Int) = p from hk] at hD
      cases hdrop : xs.drop k with
      | nil =>
        rw [hdrop, D_nil] at hD
        simp only [drainSt, cIsliceNext, hsk, hdrop, hD]
        simp [Run.ok]; omega
      | cons item rest =>
        have hlen : rest.length + k + 1 = xs.length := by
          have := congrArg List.length hdrop; simp at this; omega
        rw [hdrop, D_yield none st p item rest trivial] at hD
        have hwrap : wrapSsize (p + st) = p + st := wrapSsize_id _ (by rw [ssizeMin_eq]; omega)
          (by rw [ssizeMax_eq] at hw ⊢; omega)
        have ih := cRun_none fuel rest (p + 1) (p + st) st (by omega) (by omega) (by omega) hst
          (by omega)
        have hnlt : ¬ (p + st < p) := by omega
        simp only [drainSt, cIsliceNext, hsk, hdrop, hwrap, hD]
        simp only [bne_self_eq_false, Bool.false_and, Bool.or_false, decide_eq_true_eq, hnlt,
          ↓reduceIte, Bool.false_eq_true]
        refine ⟨?_, ?_⟩
        · rw [ih.1]; rfl
        · rw [ih.2]; push_cast; omega
    · rw [if_neg hkl] at hsk
      have hD := D_skip none st xs.length xs i p (by omega) (fun _ _ _ => trivial) (Nat.le_refl _)
      rw [List.drop_length, D_nil] at hD
      simp only [drainSt, cIsliceNext, hsk, hD]
      simp [Run.ok]

/-- The C run with an int `stop`: the doc loop with bound `max(next, stop)`;
`q` is the doc's `next_i`, which C clamps to `stop`. -/
theorem cRun_some : ∀ (fuel : Nat) (xs : List Int) (i p q S st : Int),
    xs.length < fuel → 0 ≤ i → i ≤ p → p ≤ ssizeMax → 0 ≤ S → S ≤ ssizeMax → 1 ≤ st → st ≤ ssizeMax →
    (q = p ∨ (p = S ∧ S ≤ q)) →
    (drainSt cIsliceNext fuel { it := some xs, next := p, stop := S, step := st, cnt := i }).1
        = Run.ok (D (some (max p S)) st i q xs).1 ∧
    (drainSt cIsliceNext fuel { it := some xs, next := p, stop := S, step := st, cnt := i }).2.cnt
        = i + (D (some (max p S)) st i q xs).2
  | 0, xs, _, _, _, _, _, h, _, _, _, _, _, _, _, _ => by simp at h
  | fuel + 1, xs, i, p, q, S, st, hf, hi, hip, hp, hS, hS', hst, hst', hq => by
    obtain ⟨k, hk⟩ : ∃ k : Nat, i + k = p := ⟨(p - i).toNat, by omega⟩
    have hsk := cIsliceSkip_lt p xs k i hk
    have hSne : (S != -1) = true := by simp; omega
    by_cases hkl : k ≤ xs.length
    · rw [if_pos hkl] at hsk
      have hD := D_skip (some (max p S)) st k xs i q (by omega)
        (fun j _ hj => by simp [BoundAbove]; omega) hkl
      rw [show i + (k : Int) = p from hk] at hD
      by_cases hpS : p ≥ S
      · rw [D_stop _ st p q _ (by omega)] at hD
        simp only [drainSt, cIsliceNext, hsk, hSne, hD]
        simp only [Bool.true_and, ge_iff_le, decide_eq_true_eq, show S ≤ p from hpS, ↓reduceIte]
        simp [Run.ok]; omega
      · have hqp : q = p := by omega
        subst hqp
        have hmax : max q S = S := by omega
        rw [hmax] at hD ⊢
        cases hdrop : xs.drop k with
        | nil =>
          rw [hdrop, D_nil] at hD
          simp only [drainSt, cIsliceNext, hsk, hdrop, hSne, hD]
          simp only [Bool.true_and, ge_iff_le, decide_eq_true_eq, show ¬ S ≤ q by omega, ↓reduceIte]
          simp [Run.ok]; omega
        | cons item rest =>
          have hlen : rest.length + k + 1 = xs.length := by
            have := congrArg List.length hdrop; simp at this; omega
          rw [hdrop, D_yield (some S) st q item rest (by simp [BoundAbove]; omega)] at hD
          -- the next `next`: `min(p + step, stop)`, whether or not `p + step` wraps
          have hnext : (if (decide (wrapSsize (q + st) < q) || decide (wrapSsize (q + st) > S)) = true
              then S else wrapSsize (q + st)) = if q + st > S then S else q + st := by
            by_cases hw : q + st ≤ ssizeMax
            · rw [wrapSsize_id _ (by rw [ssizeMin_eq]; omega) hw]
              by_cases h2 : q + st > S
              · simp [h2]
              · simp [h2]; omega
            · rw [wrapSsize_over _ (by omega) (by omega)]
              have : q + st - two64 < q := by simp [two64]; rw [ssizeMax_eq] at hst'; omega
              simp [this]; omega
          have ih := cRun_some fuel rest (q + 1) (if q + st > S then S else q + st) (q + st) S st
            (by omega) (by omega) (by split <;> omega) (by split <;> omega) hS hS' hst hst'
            (by split <;> omega)
          have hmax2 : max (if q + st > S then S else q + st) S = S := by split <;> omega
          rw [hmax2] at ih
          simp only [drainSt, cIsliceNext, hsk, hdrop, hSne, hD]
          simp only [Bool.true_and, ge_iff_le, decide_eq_true_eq, show ¬ S ≤ q by omega, ↓reduceIte]
          rw [hnext]
          refine ⟨?_, ?_⟩
          · rw [ih.1]; rfl
          · rw [ih.2]; push_cast; omega
    · rw [if_neg hkl] at hsk
      have hD := D_skip (some (max p S)) st xs.length xs i q (by omega)
        (fun j _ hj => by simp [BoundAbove]; omega) (Nat.le_refl _)
      rw [List.drop_length, D_nil] at hD
      simp only [drainSt, cIsliceNext, hsk, hD]
      simp [Run.ok]

/-! ## Argument parsing -/

/-- `islice(it, stop)` or `islice(it, start, stop[, step])`. -/
def IsliceArgsOk (args : List (Option Int)) : Prop := 1 ≤ args.length ∧ args.length ≤ 3

/-- Every argument is `None` or a `Py_ssize_t`. -/
def IsliceArgsSsize (args : List (Option Int)) : Prop := ∀ a ∈ args, ∀ v, a = some v → InSsize v

theorem asSsizeOrMinus1_of {v : Int} (h : InSsize v) : asSsizeOrMinus1 v = v := by
  simp [asSsizeOrMinus1, asSsize, InSsize] at *; simp [h]

/-- The doc's validated `(start, stop, step)` of an argument list. -/
def isliceRef (args : List (Option Int)) : Int × Option Int × Int :=
  match args with
  | [s] => (0, s, 1)
  | [a, b] => (a.getD 0, b, 1)
  | a :: b :: c :: _ => (a.getD 0, b, c.getD 1)
  | [] => (0, none, 1)

def StopOk : Option Int → Prop
  | some v => 0 ≤ v
  | none => True

/-- The doc's argument check passes. -/
def IsliceRefOk (args : List (Option Int)) : Prop :=
  0 ≤ (isliceRef args).1 ∧ StopOk (isliceRef args).2.1 ∧ 1 ≤ (isliceRef args).2.2

theorem eq_neg1_false {x : Int} (h : 0 ≤ x) : (x = -1) = False := by simp; omega
theorem lt_neg1_false {x : Int} (h : 0 ≤ x) : (x < -1) = False := by simp; omega
theorem lt_zero_false {x : Int} (h : 0 ≤ x) : (x < 0) = False := by simp; omega
theorem lt_one_false {x : Int} (h : 1 ≤ x) : (x < 1) = False := by simp; omega
theorem le_zero_false {x : Int} (h : 1 ≤ x) : (x ≤ 0) = False := by simp; omega

theorem doc_args_ok (args : List (Option Int)) (hok : IsliceArgsOk args) (h : IsliceRefOk args) :
    docIsliceArgs args = .ok (isliceRef args) := by
  rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, rest⟩⟩⟩⟩ <;> simp [IsliceArgsOk] at hok
  all_goals
    rcases a1 with _ | u <;> (try rcases a2 with _ | v) <;> (try rcases a3 with _ | w) <;>
      simp [IsliceRefOk, isliceRef, StopOk] at h <;> simp [docIsliceArgs, isliceRef] <;> omega

theorem doc_args_err (args : List (Option Int)) (hok : IsliceArgsOk args) (h : ¬ IsliceRefOk args) :
    ∃ e, docIsliceArgs args = .error e := by
  rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, rest⟩⟩⟩⟩ <;> simp [IsliceArgsOk] at hok
  all_goals
    rcases a1 with _ | u <;> (try rcases a2 with _ | v) <;> (try rcases a3 with _ | w) <;>
      simp [IsliceRefOk, isliceRef, StopOk] at h <;>
      simp only [docIsliceArgs] <;> split <;> (first | exact ⟨_, rfl⟩ | (exfalso; simp_all <;> omega))

theorem c_args_ok (args : List (Option Int)) (hok : IsliceArgsOk args) (hs : IsliceArgsSsize args)
    (h : IsliceRefOk args) :
    cIsliceArgs args = .ok ((isliceRef args).1, (isliceRef args).2.1.getD (-1), (isliceRef args).2.2) := by
  rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, rest⟩⟩⟩⟩ <;> simp [IsliceArgsOk] at hok
  all_goals
    rcases a1 with _ | u <;> (try rcases a2 with _ | v) <;> (try rcases a3 with _ | w) <;>
      simp [IsliceArgsSsize] at hs <;>
      simp [IsliceRefOk, isliceRef, StopOk] at h <;>
      simp [cIsliceArgs, isliceRef, asSsizeOrMinus1_of, hs, eq_neg1_false, lt_neg1_false,
        lt_zero_false, lt_one_false, h]

theorem c_args_err (args : List (Option Int)) (hok : IsliceArgsOk args) (hs : IsliceArgsSsize args)
    (h : ¬ IsliceRefOk args) : ∃ e, cIsliceArgs args = .error e := by
  rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, rest⟩⟩⟩⟩ <;> simp [IsliceArgsOk] at hok
  all_goals
    rcases a1 with _ | u <;> (try rcases a2 with _ | v) <;> (try rcases a3 with _ | w) <;>
      simp [IsliceArgsSsize] at hs <;>
      simp [IsliceRefOk, isliceRef, StopOk] at h <;>
      simp only [cIsliceArgs, asSsizeOrMinus1_of, hs] <;>
      split <;> (first | exact ⟨_, rfl⟩ | skip) <;>
      (rename_i heq; (repeat' split at heq) <;>
        simp only [reduceCtorEq, Except.ok.injEq, Prod.mk.injEq] at heq) <;>
      (try obtain ⟨rfl, rfl⟩ := heq) <;>
      (repeat' split) <;> (first | exact ⟨_, rfl⟩ | (exfalso; first | omega | (simp_all <;> omega)))

theorem isliceRef_bounds (args : List (Option Int)) (hok : IsliceArgsOk args) (hs : IsliceArgsSsize args) :
    (isliceRef args).1 ≤ ssizeMax ∧ (∀ v, (isliceRef args).2.1 = some v → v ≤ ssizeMax) ∧
    (isliceRef args).2.2 ≤ ssizeMax := by
  have : (0 : Int) ≤ ssizeMax := by decide
  have h1 : (1 : Int) ≤ ssizeMax := by decide
  rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, rest⟩⟩⟩⟩ <;> simp [IsliceArgsOk] at hok
  all_goals
    rcases a1 with _ | u <;> (try rcases a2 with _ | v) <;> (try rcases a3 with _ | w) <;>
      simp [IsliceArgsSsize, InSsize] at hs <;> simp [isliceRef] <;> omega

/-! ## Properties -/

/-- C and doc drain to the same items, consume the same number of input
items, and raise in the same cases (the doc raises a bare `ValueError`, C a
`ValueError` with a message; messages are not compared). -/
def isliceAgree (l : List Int) (args : List (Option Int)) : Prop :=
  (cIslice l args).1.1 = (docIslice l args).1.1 ∧ (cIslice l args).2 = (docIslice l args).2 ∧
  (cIslice l args).1.2.isSome = (docIslice l args).1.2.isSome

/-- Broad: C `islice` behaves like the doc equivalent for every int argument. -/
def IsliceDocAgree : Prop :=
  ∀ (l : List Int) (args : List (Option Int)), IsliceArgsOk args → (l.length : Int) ≤ ssizeMax →
    isliceAgree l args

theorem isliceDocAgree_refuted : ¬IsliceDocAgree := by
  intro h
  have := (h [0, 1, 2] [some (2 ^ 63)] (by simp [IsliceArgsOk]) (by decide)).1
  revert this
  decide

/-- Narrowed to `Py_ssize_t` arguments, the range C accepts. -/
def IsliceDocAgreeSsize : Prop :=
  ∀ (l : List Int) (args : List (Option Int)), IsliceArgsOk args → (l.length : Int) ≤ ssizeMax →
    IsliceArgsSsize args → isliceAgree l args

theorem isliceDocAgreeSsize_refuted : ¬IsliceDocAgreeSsize := by
  intro h
  have := (h [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] [some 1, none, some (2 ^ 63 - 1)] (by simp [IsliceArgsOk]) (by decide)
    (by simp [IsliceArgsSsize, InSsize, ssizeMin, ssizeMax])).1
  revert this
  decide

/-- Narrowed further: with `stop=None`, the C `next += step` must not wrap for
any item the input can still provide (`len + step <= sys.maxsize + 1`). -/
def IsliceDocAgreeNoWrap : Prop :=
  ∀ (l : List Int) (args : List (Option Int)), IsliceArgsOk args → (l.length : Int) ≤ ssizeMax →
    IsliceArgsSsize args →
    ((isliceRef args).2.1 = none → (l.length : Int) + (isliceRef args).2.2 ≤ ssizeMax + 1) →
    isliceAgree l args

theorem isliceDocAgreeNoWrap_proven : IsliceDocAgreeNoWrap := by
  intro l args hok hlen hs hw
  obtain ⟨hb1, hb2, hb3⟩ := isliceRef_bounds args hok hs
  by_cases hr : IsliceRefOk args
  · have hc := c_args_ok args hok hs hr
    have hd := doc_args_ok args hok hr
    obtain ⟨hr1, hr2, hr3⟩ := hr
    simp only [isliceAgree, cIslice, docIslice, hc, hd]
    generalize hR : isliceRef args = R at *
    obtain ⟨start, stop, st⟩ := R
    simp only at hr1 hr2 hr3 hb1 hb2 hb3 hw ⊢
    cases stop with
    | none =>
      have := cRun_none (l.length + 1) l 0 start st (by omega) (by omega) hr1 hr3 (by simpa using hw rfl)
      simp only [Option.getD, Option.map] at this ⊢
      rw [this.1, this.2]
      simp [Run.ok]
    | some S =>
      simp only [StopOk] at hr2
      have := cRun_some (l.length + 1) l 0 start start S st (by omega) (by omega) hr1 hb1 hr2
        (hb2 S rfl) hr3 hb3 (Or.inl rfl)
      simp only [Option.getD, Option.map] at this ⊢
      rw [this.1, this.2]
      simp [Run.ok]
  · obtain ⟨e1, he1⟩ := c_args_err args hok hs hr
    obtain ⟨e2, he2⟩ := doc_args_err args hok hr
    simp [isliceAgree, cIslice, docIslice, he1, he2, Run.err]

/-- rst:485-487: "fully consuming the islice advances the input iterator by
max(start, stop) steps regardless of the step value" (at most `len` for a
finite input). For the C object, for every `Py_ssize_t` `start` and `stop`. -/
def IsliceConsumesMaxStartStop : Prop :=
  ∀ (l : List Int) (args : List (Option Int)) (S : Int), IsliceArgsOk args →
    (l.length : Int) ≤ ssizeMax → IsliceArgsSsize args → IsliceRefOk args →
    (isliceRef args).2.1 = some S →
    (cIslice l args).2 = min (l.length : Int) (max (isliceRef args).1 S)

theorem isliceConsumesMaxStartStop_proven : IsliceConsumesMaxStartStop := by
  intro l args S hok hlen hs hr hS
  have hag := isliceDocAgreeNoWrap_proven l args hok hlen hs (by simp [hS])
  rw [hag.2.1]
  have hd := doc_args_ok args hok hr
  obtain ⟨hr1, hr2, hr3⟩ := hr
  simp only [docIslice, hd]
  generalize hR : isliceRef args = R at *
  obtain ⟨start, stop, st⟩ := R
  simp only at hS hr1 ⊢
  subst hS
  simp only [Option.map]
  rw [D_consumed_some]
  simp only [StopOk] at hr2
  omega

/-- The `ValueError` that names the step ("must be a positive integer or
None") is raised only for steps that are not positive integers. -/
def IsliceStepMessageAccurate : Prop :=
  ∀ (l : List Int) (a b : Option Int) (v : Int),
    (cIslice l [a, b, some v]).1.2 = some (.valueError isliceStepMsg) → v < 1

theorem isliceStepMessageAccurate_refuted : ¬IsliceStepMessageAccurate := by
  intro h
  have := h [] none none (2 ^ 63) (by decide)
  revert this
  decide

end PyLean.Itertools
