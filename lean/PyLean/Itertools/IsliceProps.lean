import PyLean.Itertools.Islice

/-!
Properties of `islice`: the C object against the doc equivalent, layered as in
`Accel` (broad statement refuted, narrowed statements proven), plus the doc
sentence about how much input is consumed.
-/

namespace PyLean.Itertools

open PyLean

variable {α : Type}

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

theorem cIsliceSkip_ge (p : Int) : ∀ (xs : List α) (i : Int), p ≤ i → cIsliceSkip p xs i = (some xs, i)
  | [], i, h => by simp [cIsliceSkip]; omega
  | x :: xs, i, h => by simp [cIsliceSkip]; omega

theorem cIsliceSkip_lt (p : Int) : ∀ (xs : List α) (k : Nat) (i : Int), i + k = p →
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

theorem D_nil (bound : Option Int) (st : Int) (err : Option PyExc) (i q : Int) (h : BoundAbove bound i) :
    D bound st err i q ([] : List α) = ([], 0, err) := by
  simp [docIsliceLoop, boundCheck_false h]

theorem D_stop (B st : Int) (err : Option PyExc) (i q : Int) (xs : List α) (h : B ≤ i) :
    D (some B) st err i q xs = ([], 0, none) := by
  cases xs with
  | nil => simp [docIsliceLoop, pastBound]; omega
  | cons x xs => simp [docIsliceLoop, pastBound]; omega

theorem D_yield (bound : Option Int) (st : Int) (err : Option PyExc) (i : Int) (x : α) (xs : List α)
    (h : BoundAbove bound i) :
    D bound st err i i (x :: xs) =
      (x :: (D bound st err (i + 1) (i + st) xs).1, (D bound st err (i + 1) (i + st) xs).2.1 + 1,
        (D bound st err (i + 1) (i + st) xs).2.2) := by
  simp only [docIsliceLoop, boundCheck_false h]
  simp

/-- Skipping `k` items that are before `nextI` and below the bound. -/
theorem D_skip (bound : Option Int) (st : Int) (err : Option PyExc) : ∀ (k : Nat) (xs : List α) (i q : Int),
    i + k ≤ q → (∀ j, i ≤ j → j < i + k → BoundAbove bound j) → k ≤ xs.length →
    D bound st err i q xs =
      ((D bound st err (i + k) q (xs.drop k)).1, (D bound st err (i + k) q (xs.drop k)).2.1 + k,
        (D bound st err (i + k) q (xs.drop k)).2.2)
  | 0, xs, i, q, _, _, _ => by simp
  | k + 1, [], _, _, _, _, hl => by simp at hl
  | k + 1, x :: xs, i, q, hq, hb, hl => by
    have hbi : BoundAbove bound i := hb i (by omega) (by omega)
    have hne : ¬ i = q := by omega
    have ih := D_skip bound st err k xs (i + 1) q (by omega) (fun j h1 h2 => hb j (by omega) (by omega))
      (by simp at hl; omega)
    simp only [docIsliceLoop, boundCheck_false hbi, hne, Bool.false_eq_true, ↓reduceIte, ih,
      List.drop_succ_cons]
    have e : i + 1 + (k : Int) = i + ((k + 1 : Nat) : Int) := by push_cast; omega
    rw [e]
    simp only [Prod.mk.injEq, true_and, and_true]
    omega

/-- Consumption of the doc loop: everything below the bound. -/
theorem D_consumed_some (B st : Int) (err : Option PyExc) : ∀ (xs : List α) (i q : Int),
    ((D (some B) st err i q xs).2.1 : Int) = min (xs.length : Int) (max 0 (B - i))
  | [], i, q => by
    simp only [docIsliceLoop]
    split <;> simp <;> omega
  | x :: xs, i, q => by
    by_cases h : B ≤ i
    · rw [D_stop B st err i q _ h]; simp; omega
    · have hb : BoundAbove (some B) i := by simp [BoundAbove]; omega
      simp only [docIsliceLoop, boundCheck_false hb]
      by_cases hiq : i = q
      · simp only [hiq, ↓reduceIte, Bool.false_eq_true]
        have := D_consumed_some B st err xs (q + 1) (q + st)
        simp only [List.length_cons]; push_cast; omega
      · simp only [hiq, ↓reduceIte, Bool.false_eq_true]
        have := D_consumed_some B st err xs (i + 1) q
        simp only [List.length_cons]; push_cast; omega

/-! ## The C object -/

/-- The run of `cIsliceNext` as a pair: run and final `cnt`. -/
def islRes (s : IsliceState α) (fuel : Nat) : Run α × Int :=
  ((drainSt cIsliceNext fuel s).1, (drainSt cIsliceNext fuel s).2.cnt)

theorem drain_ended (s : IsliceState α) (err : Option PyExc) (cnt : Int) (fuel : Nat)
    (h : cIsliceNext s = cIsliceEnded s err cnt) :
    (drainSt cIsliceNext (fuel + 1) s).1 = ([], err) ∧ (drainSt cIsliceNext (fuel + 1) s).2.cnt = cnt := by
  cases err <;> simp [drainSt, h, cIsliceEnded]

/-- The C run with `stop=None`, as long as `lz->next += step` cannot wrap. -/
theorem cRun_none (err : Option PyExc) : ∀ (fuel : Nat) (xs : List α) (i p st : Int),
    xs.length < fuel → 0 ≤ i → i ≤ p → 1 ≤ st → i + xs.length + st ≤ ssizeMax + 1 →
    (drainSt cIsliceNext fuel { it := some ⟨xs, err⟩, next := p, stop := -1, step := st, cnt := i }).1
        = ((D none st err i p xs).1, (D none st err i p xs).2.2) ∧
    (drainSt cIsliceNext fuel { it := some ⟨xs, err⟩, next := p, stop := -1, step := st, cnt := i }).2.cnt
        = i + (D none st err i p xs).2.1
  | 0, xs, _, _, _, h, _, _, _, _ => by simp at h
  | fuel + 1, xs, i, p, st, hf, hi, hip, hst, hw => by
    obtain ⟨k, hk⟩ : ∃ k : Nat, i + k = p := ⟨(p - i).toNat, by omega⟩
    have hsk := cIsliceSkip_lt p xs k i hk
    by_cases hkl : k ≤ xs.length
    · rw [if_pos hkl] at hsk
      have hD := D_skip none st err k xs i p (by omega) (fun _ _ _ => trivial) hkl
      rw [show i + (k : Int) = p from hk] at hD
      cases hdrop : xs.drop k with
      | nil =>
        rw [hdrop, D_nil none st err p p trivial] at hD
        have := drain_ended { it := some ⟨xs, err⟩, next := p, stop := -1, step := st, cnt := i } err p fuel
          (by simp [cIsliceNext, hsk, hdrop])
        simp only [hD]
        rw [this.1, this.2]
        simp <;> omega
      | cons item rest =>
        have hlen : rest.length + k + 1 = xs.length := by
          have := congrArg List.length hdrop; simp at this; omega
        rw [hdrop, D_yield none st err p item rest trivial] at hD
        have hwrap : wrapSsize (p + st) = p + st := wrapSsize_id _ (by rw [ssizeMin_eq]; omega)
          (by rw [ssizeMax_eq] at hw ⊢; omega)
        have ih := cRun_none err fuel rest (p + 1) (p + st) st (by omega) (by omega) (by omega) hst
          (by omega)
        have hnlt : ¬ (p + st < p) := by omega
        simp only [drainSt, cIsliceNext, hsk, hdrop, hwrap, hD]
        simp only [bne_self_eq_false, Bool.false_and, Bool.or_false, decide_eq_true_eq, hnlt,
          ↓reduceIte, Bool.false_eq_true]
        refine ⟨?_, ?_⟩
        · rw [ih.1]
        · rw [ih.2]; push_cast; try omega
    · rw [if_neg hkl] at hsk
      have hD := D_skip none st err xs.length xs i p (by omega) (fun _ _ _ => trivial) (Nat.le_refl _)
      rw [List.drop_length, D_nil none st err _ p trivial] at hD
      have := drain_ended { it := some ⟨xs, err⟩, next := p, stop := -1, step := st, cnt := i } err
        (i + xs.length) fuel (by simp [cIsliceNext, hsk])
      simp only [hD]
      rw [this.1, this.2]
      simp

/-- The C run with an int `stop`: the doc loop with bound `max(next, stop)`;
`q` is the doc's `next_i`, which C clamps to `stop`. -/
theorem cRun_some (err : Option PyExc) : ∀ (fuel : Nat) (xs : List α) (i p q S st : Int),
    xs.length < fuel → 0 ≤ i → i ≤ p → p ≤ ssizeMax → 0 ≤ S → S ≤ ssizeMax → 1 ≤ st → st ≤ ssizeMax →
    (q = p ∨ (p = S ∧ S ≤ q)) →
    (drainSt cIsliceNext fuel { it := some ⟨xs, err⟩, next := p, stop := S, step := st, cnt := i }).1
        = ((D (some (max p S)) st err i q xs).1, (D (some (max p S)) st err i q xs).2.2) ∧
    (drainSt cIsliceNext fuel { it := some ⟨xs, err⟩, next := p, stop := S, step := st, cnt := i }).2.cnt
        = i + (D (some (max p S)) st err i q xs).2.1
  | 0, xs, _, _, _, _, _, h, _, _, _, _, _, _, _, _ => by simp at h
  | fuel + 1, xs, i, p, q, S, st, hf, hi, hip, hp, hS, hS', hst, hst', hq => by
    obtain ⟨k, hk⟩ : ∃ k : Nat, i + k = p := ⟨(p - i).toNat, by omega⟩
    have hsk := cIsliceSkip_lt p xs k i hk
    have hSne : (S != -1) = true := by simp; omega
    by_cases hkl : k ≤ xs.length
    · rw [if_pos hkl] at hsk
      have hD := D_skip (some (max p S)) st err k xs i q (by omega)
        (fun j _ hj => by simp [BoundAbove]; omega) hkl
      rw [show i + (k : Int) = p from hk] at hD
      by_cases hpS : p ≥ S
      · rw [D_stop _ st err p q _ (by omega)] at hD
        simp only [drainSt, cIsliceNext, hsk, hSne, hD]
        simp only [Bool.true_and, ge_iff_le, decide_eq_true_eq, show S ≤ p from hpS, ↓reduceIte]
        simp; omega
      · have hqp : q = p := by omega
        subst hqp
        have hmax : max q S = S := by omega
        rw [hmax] at hD ⊢
        cases hdrop : xs.drop k with
        | nil =>
          rw [hdrop, D_nil (some S) st err q q (by simp [BoundAbove]; omega)] at hD
          have := drain_ended { it := some ⟨xs, err⟩, next := q, stop := S, step := st, cnt := i } err q fuel
            (by simp [cIsliceNext, hsk, hdrop, hSne, show ¬ S ≤ q by omega])
          simp only [hD]
          rw [this.1, this.2]
          simp <;> omega
        | cons item rest =>
          have hlen : rest.length + k + 1 = xs.length := by
            have := congrArg List.length hdrop; simp at this; omega
          rw [hdrop, D_yield (some S) st err q item rest (by simp [BoundAbove]; omega)] at hD
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
          have ih := cRun_some err fuel rest (q + 1) (if q + st > S then S else q + st) (q + st) S st
            (by omega) (by omega) (by split <;> omega) (by split <;> omega) hS hS' hst hst'
            (by split <;> omega)
          have hmax2 : max (if q + st > S then S else q + st) S = S := by split <;> omega
          rw [hmax2] at ih
          simp only [drainSt, cIsliceNext, hsk, hdrop, hSne, hD]
          simp only [Bool.true_and, ge_iff_le, decide_eq_true_eq, show ¬ S ≤ q by omega, ↓reduceIte]
          rw [hnext]
          refine ⟨?_, ?_⟩
          · rw [ih.1]
          · rw [ih.2]; push_cast; try omega
    · rw [if_neg hkl] at hsk
      have hD := D_skip (some (max p S)) st err xs.length xs i q (by omega)
        (fun j _ hj => by simp [BoundAbove]; omega) (Nat.le_refl _)
      rw [List.drop_length, D_nil _ st err _ q (by simp [BoundAbove]; omega)] at hD
      have := drain_ended { it := some ⟨xs, err⟩, next := p, stop := S, step := st, cnt := i } err
        (i + xs.length) fuel (by simp [cIsliceNext, hsk])
      simp only [hD]
      rw [this.1, this.2]
      simp

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
    ∃ e, docIsliceArgs args = .error e ∧ e.className = "ValueError" := by
  rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, rest⟩⟩⟩⟩ <;> simp [IsliceArgsOk] at hok
  all_goals
    rcases a1 with _ | u <;> (try rcases a2 with _ | v) <;> (try rcases a3 with _ | w) <;>
      simp [IsliceRefOk, isliceRef, StopOk] at h <;>
      simp only [docIsliceArgs] <;> split <;> (first | exact ⟨_, rfl, rfl⟩ | (exfalso; simp_all <;> omega))

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

/-- All of `islice_new`'s own errors are `ValueError`s. -/
theorem cIsliceArgs_class (args : List (Option Int)) (e : PyExc) (h : cIsliceArgs args = .error e) :
    e.className = "ValueError" := by
  simp only [cIsliceArgs] at h
  repeat' split at h
  all_goals first
    | (cases h; rfl)
    | skip
  all_goals (rename_i heq; (repeat' split at heq) <;> cases h <;> cases heq <;> rfl)

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
items, and end the same way: the same exception class, or none. (The doc
raises a bare `ValueError` for bad arguments where C has a message.) -/
def isliceAgree (seq : Obj α) (args : List (Option Int)) : Prop :=
  (cIslice seq args).1.1 = (docIslice seq args).1.1 ∧ (cIslice seq args).2 = (docIslice seq args).2 ∧
  (cIslice seq args).1.2.map PyExc.className = (docIslice seq args).1.2.map PyExc.className

/-- Broad: C `islice` behaves like the doc equivalent for every int argument,
over any element type. Type invariant: the input has at most `sys.maxsize` items. -/
def IsliceDocAgree : Prop :=
  ∀ (α : Type) (seq : Obj α) (args : List (Option Int)), IsliceArgsOk args →
    (seq.len : Int) ≤ ssizeMax → isliceAgree seq args

theorem isliceDocAgree_refuted : ¬IsliceDocAgree := by
  intro h
  have := (h Int (.iter [0, 1, 2] none) [some (2 ^ 63)] (by simp [IsliceArgsOk]) (by decide)).1
  revert this
  decide

/-- Narrowed to `Py_ssize_t` arguments, the range C accepts. -/
def IsliceDocAgreeSsize : Prop :=
  ∀ (α : Type) (seq : Obj α) (args : List (Option Int)), IsliceArgsOk args →
    (seq.len : Int) ≤ ssizeMax → IsliceArgsSsize args → isliceAgree seq args

theorem isliceDocAgreeSsize_refuted : ¬IsliceDocAgreeSsize := by
  intro h
  have := (h Int (.iter [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] none) [some 1, none, some (2 ^ 63 - 1)]
    (by simp [IsliceArgsOk]) (by decide) (by simp [IsliceArgsSsize, InSsize, ssizeMin, ssizeMax])).1
  revert this
  decide

/-- Narrowed further: with `stop=None`, the C `next += step` must not wrap for
any item the input can still provide (`len + step <= sys.maxsize + 1`). -/
def IsliceDocAgreeNoWrap : Prop :=
  ∀ (α : Type) (seq : Obj α) (args : List (Option Int)), IsliceArgsOk args →
    (seq.len : Int) ≤ ssizeMax → IsliceArgsSsize args →
    ((isliceRef args).2.1 = none → (seq.len : Int) + (isliceRef args).2.2 ≤ ssizeMax + 1) →
    isliceAgree seq args

theorem isliceDocAgreeNoWrap_proven : IsliceDocAgreeNoWrap := by
  intro α seq args hok hlen hs hw
  obtain ⟨hb1, hb2, hb3⟩ := isliceRef_bounds args hok hs
  by_cases hr : IsliceRefOk args
  · have hc := c_args_ok args hok hs hr
    have hd := doc_args_ok args hok hr
    obtain ⟨hr1, hr2, hr3⟩ := hr
    cases seq with
    | notIterable ty =>
      simp [isliceAgree, cIslice, cIsliceNew, docIslice, hc, hd, getIter, Run.err]
    | iter l err =>
      simp only [Obj.len] at hlen hw
      simp only [isliceAgree, cIslice, cIsliceNew, docIslice, hc, hd, getIter, Obj.len]
      generalize hR : isliceRef args = R at *
      obtain ⟨start, stop, st⟩ := R
      simp only at hr1 hr2 hr3 hb1 hb2 hb3 hw ⊢
      cases stop with
      | none =>
        have := cRun_none err (l.length + 1) l 0 start st (by omega) (by omega) hr1 hr3
          (by simpa using hw rfl)
        simp only [Option.getD, Option.map] at this ⊢
        rw [this.1, this.2]
        simp
      | some S =>
        simp only [StopOk] at hr2
        have := cRun_some err (l.length + 1) l 0 start start S st (by omega) (by omega) hr1 hb1 hr2
          (hb2 S rfl) hr3 hb3 (Or.inl rfl)
        simp only [Option.getD, Option.map] at this ⊢
        rw [this.1, this.2]
        simp
  · obtain ⟨e1, he1⟩ := c_args_err args hok hs hr
    have hc1 := cIsliceArgs_class args e1 he1
    obtain ⟨e2, he2, hc2⟩ := doc_args_err args hok hr
    simp [isliceAgree, cIslice, cIsliceNew, docIslice, he1, he2, Run.err, hc1, hc2]

/-- rst:498-500: "fully consuming the islice advances the input iterator by
max(start, stop) steps regardless of the step value" (at most `len` for a
finite input). For the C object, for every `Py_ssize_t` `start` and `stop`. -/
def IsliceConsumesMaxStartStop : Prop :=
  ∀ (α : Type) (l : List α) (err : Option PyExc) (args : List (Option Int)) (S : Int), IsliceArgsOk args →
    (l.length : Int) ≤ ssizeMax → IsliceArgsSsize args → IsliceRefOk args →
    (isliceRef args).2.1 = some S →
    (cIslice (.iter l err) args).2 = min (l.length : Int) (max (isliceRef args).1 S)

theorem isliceConsumesMaxStartStop_proven : IsliceConsumesMaxStartStop := by
  intro α l err args S hok hlen hs hr hS
  have hag := isliceDocAgreeNoWrap_proven α (.iter l err) args hok hlen hs (by simp [hS])
  rw [hag.2.1]
  have hd := doc_args_ok args hok hr
  obtain ⟨hr1, hr2, hr3⟩ := hr
  simp only [docIslice, hd, getIter]
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
  ∀ (α : Type) (seq : Obj α) (a b : Option Int) (v : Int),
    (cIslice seq [a, b, some v]).1.2 = some (.valueError isliceStepMsg) → v < 1

theorem isliceStepMessageAccurate_refuted : ¬IsliceStepMessageAccurate := by
  intro h
  have := h Int (.iter [] none) none none (2 ^ 63) (by decide)
  revert this
  decide

end PyLean.Itertools
