import PyLean.CoreLibs.Rand.CountsProps
import PyLean.CoreLibs.Rand.DistFormula

/-!
The integer and sequence methods of `Lib/random.py:245-495` as functions of the values
their generator produces.

`GbRun g k s rs s'` says that, from state `s`, successive calls `self.getrandbits(k)`
return the values `rs` and end in `s'`; `RndRun g s us s'` says the same for
`self.random()`. The `_randbelow` loops are pinned in closed form: the result is the first
accepted draw, after exactly that many calls with that argument. The sequence methods
take `_randbelow` itself as a parameter `below` (`__init_subclass__` picks it), and are
pinned one step at a time: which bound each step passes to `below`, and what it does
with the answer.
-/

namespace PyLean.CoreLibs.Rand

open PyLean PyLean.Binary64 PyLean.Binary64.F64 RM Flt

variable {σ F α : Type}

/-- From `s`, the calls `self.getrandbits(k)` return `rs`, in order, and end in `s'`. -/
inductive GbRun (g : Gen σ F) (k : Nat) : σ → List Nat → σ → Prop
  | nil (s : σ) : GbRun g k s [] s
  | cons {s s1 s2 : σ} {r : Nat} {rs : List Nat} :
      g.getrandbits (.int k) s = (.ok r, s1) → GbRun g k s1 rs s2 → GbRun g k s (r :: rs) s2

/-- From `s`, the calls `self.random()` return `us`, in order, and end in `s'`. -/
inductive RndRun (g : Gen σ F) : σ → List F → σ → Prop
  | nil (s : σ) : RndRun g s [] s
  | cons {s s1 s2 : σ} {u : F} {us : List F} :
      g.random s = (u, s1) → RndRun g s1 us s2 → RndRun g s (u :: us) s2

/-! ### `_randbelow_with_getrandbits`, Lib/random.py:245-252 -/

theorem belowLoop_accept (g : Gen σ F) (n k : Nat) (r : Nat) (hr : r < n) :
    ∀ fuel (s : σ), belowLoop g n k fuel r s = (.ok r, s)
  | 0, s => by simp [belowLoop, show ¬ r ≥ n by omega]
  | _ + 1, s => by simp [belowLoop, show ¬ r ≥ n by omega]

theorem belowLoop_run (g : Gen σ F) (n k r : Nat) (s' : σ) (hr : r < n) :
    ∀ (rest : List Nat) (fuel r0 : Nat) (s1 : σ), n ≤ r0 → GbRun g k s1 (rest ++ [r]) s' →
      (∀ x ∈ rest, n ≤ x) → rest.length + 1 ≤ fuel → belowLoop g n k fuel r0 s1 = (.ok r, s')
  | [], fuel, r0, s1, h0, hrun, _, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    cases hrun with
    | cons h1 h2 =>
      cases h2 with
      | nil =>
        simp only [belowLoop, show r0 ≥ n from h0, if_true, RM.bind_apply, gb, h1]
        exact belowLoop_accept g n k r hr f _
  | x :: rest, fuel, r0, s1, h0, hrun, hx, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    cases hrun with
    | cons h1 h2 =>
      simp only [belowLoop, show r0 ≥ n from h0, if_true, RM.bind_apply, gb, h1]
      exact belowLoop_run g n k r s' hr rest f x _ (hx x (by simp)) h2
        (fun y hy => hx y (by simp [hy])) (by simp at hf; omega)

theorem belowLoop_run_err (g : Gen σ F) (n k : Nat) (e : PyExc) (s2 : σ) :
    ∀ (rest : List Nat) (fuel r0 : Nat) (s1 s3 : σ), n ≤ r0 → GbRun g k s1 rest s3 →
      (∀ x ∈ rest, n ≤ x) → g.getrandbits (.int k) s3 = (.error e, s2) → rest.length + 1 ≤ fuel →
      belowLoop g n k fuel r0 s1 = (.error e, s2)
  | [], fuel, r0, s1, s3, h0, hrun, _, he, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    cases hrun with
    | nil => simp only [belowLoop, show r0 ≥ n from h0, if_true, RM.bind_apply, gb, he]
  | x :: rest, fuel, r0, s1, s3, h0, hrun, hx, he, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    cases hrun with
    | cons h1 h2 =>
      simp only [belowLoop, show r0 ≥ n from h0, if_true, RM.bind_apply, gb, h1]
      exact belowLoop_run_err g n k e s2 rest f x _ s3 (hx x (by simp)) h2
        (fun y hy => hx y (by simp [hy])) he (by simp at hf; omega)

/-- `_randbelow_with_getrandbits(n)` returns the first value below `n` among the calls
`self.getrandbits(n.bit_length())`, after exactly the calls up to it, and propagates the
first exception. (`fuel` only bounds the model's loop: any `fuel` at least the number of
rejections gives this result.) -/
def RandbelowWithExact : Prop :=
  ∀ (σ F : Type) (g : Gen σ F) (n fuel : Nat) (rs : List Nat) (s : σ), 0 < n →
    (∀ x ∈ rs, n ≤ x) → rs.length ≤ fuel →
    (∀ r s', r < n → GbRun g (bitLength n) s (rs ++ [r]) s' → randbelowWith g fuel n s = (.ok r, s')) ∧
    (∀ e s1 s2, GbRun g (bitLength n) s rs s1 → g.getrandbits (.int (bitLength n)) s1 = (.error e, s2) →
      randbelowWith g fuel n s = (.error e, s2))

theorem randbelowWithExact_proven : RandbelowWithExact := by
  intro σ F g n fuel rs s hn hrs hf
  refine ⟨fun r s' hr hrun => ?_, fun e s1 s2 hrun he => ?_⟩
  · cases rs with
    | nil =>
      cases hrun with
      | cons h1 h2 =>
        cases h2 with
        | nil =>
          simp only [randbelowWith, RM.bind_apply, gb, h1]
          exact belowLoop_accept g n _ r hr fuel _
    | cons x rest =>
      cases hrun with
      | cons h1 h2 =>
        simp only [randbelowWith, RM.bind_apply, gb, h1]
        exact belowLoop_run g n _ r s' hr rest fuel x _ (hrs x (by simp)) h2
          (fun y hy => hrs y (by simp [hy])) (by simp at hf; omega)
  · cases rs with
    | nil =>
      cases hrun with
      | nil => simp only [randbelowWith, RM.bind_apply, gb, he]
    | cons x rest =>
      cases hrun with
      | cons h1 h2 =>
        simp only [randbelowWith, RM.bind_apply, gb, h1]
        exact belowLoop_run_err g n _ e s2 rest fuel x _ s1 (hrs x (by simp)) h2
          (fun y hy => hrs y (by simp [hy])) he (by simp at hf; omega)

/-! ### `_randbelow_without_getrandbits`, Lib/random.py:254-272 -/

theorem drawBelow_accept [Flt F] (g : Gen σ F) (lim r : F) (hr : Flt.le lim r = false) :
    ∀ fuel (s : σ), drawBelow g lim fuel r s = (.ok r, s)
  | 0, s => by simp [drawBelow, hr]
  | _ + 1, s => by simp [drawBelow, hr]

theorem drawBelow_run [Flt F] (g : Gen σ F) (lim u : F) (s' : σ) (hu : Flt.le lim u = false) :
    ∀ (rest : List F) (fuel : Nat) (r0 : F) (s1 : σ), Flt.le lim r0 = true →
      RndRun g s1 (rest ++ [u]) s' → (∀ x ∈ rest, Flt.le lim x = true) → rest.length + 1 ≤ fuel →
      drawBelow g lim fuel r0 s1 = (.ok u, s')
  | [], fuel, r0, s1, h0, hrun, _, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    cases hrun with
    | cons h1 h2 =>
      cases h2 with
      | nil =>
        simp only [drawBelow, h0, if_true, rnd_bind_apply h1]
        exact drawBelow_accept g lim u hu f _
  | x :: rest, fuel, r0, s1, h0, hrun, hx, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    cases hrun with
    | cons h1 h2 =>
      simp only [drawBelow, h0, if_true, rnd_bind_apply h1]
      exact drawBelow_run g lim u s' hu rest f x _ (hx x (by simp)) h2
        (fun y hy => hx y (by simp [hy])) (by simp at hf; omega)

theorem ofInt_le_2_53 {m : Nat} (hm : m ≤ 2 ^ 53) : (F64.ofInt m).isInf = false := by
  by_cases h : m < 2 ^ 53
  · exact isInf_false_of_finite (ofInt_small (n := (m : Int)) (by simpa using h)).1
  · have : m = 2 ^ 53 := by omega
    subst this
    decide +kernel

theorem pyFloat_le_2_53 [RandLibm] {m : Nat} (hm : m ≤ 2 ^ 53) :
    (pyFloat (m : Int) : Py F64) = .ok (F64.ofInt m) := by
  have : (Flt.ofInt (m : Int) : Option F64) = some (F64.ofInt m) := by
    show F64R.ofIntOpt _ = _
    simp [F64R.ofIntOpt, ofInt_le_2_53 hm]
  simp [pyFloat, this]

/-- `_randbelow_without_getrandbits(n)` over binary64. For `0 < n < 2 ** 53`:
`limit = (2 ** 53 - 2 ** 53 % n) / 2 ** 53`, the result is `floor(u * 2 ** 53) % n` for the
first `random()` value `u` below `limit`, after exactly the calls up to it. For
`n >= 2 ** 53`: first `warnings.warn(msg)` (:262-265) with the exact message; when the
warning filters turn it into an exception, that exception before any draw; otherwise one
draw `u` and `floor(u * float(n))`, with the `OverflowError` of `float(n)` after the draw.
`warn` is any warning hook: the small branch never calls it. -/
def RandbelowWithoutExact : Prop :=
  ∀ [RandLibm] (σ : Type) (g : Gen σ F64) (warn : String → Py Unit),
    (∀ (n fuel : Nat) (us : List F64) (u : F64) (s s' : σ), 0 < n → n < 2 ^ 53 →
      RndRun g s (us ++ [u]) s' →
      (∀ x ∈ us, Flt.le (F64.ofInt (2 ^ 53 - 2 ^ 53 % n : Nat) / F64.ofInt (2 ^ 53 : Nat)) x = true) →
      Flt.le (F64.ofInt (2 ^ 53 - 2 ^ 53 % n : Nat) / F64.ofInt (2 ^ 53 : Nat)) u = false →
      us.length ≤ fuel →
      randbelowWithout g fuel n (2 ^ 53) warn s =
        (match mathFloor (u * F64.ofInt (2 ^ 53 : Nat)) with
         | .ok v => .ok (v % (n : Int)).toNat
         | .error e => .error e, s')) ∧
    (∀ (n fuel : Nat) (e : PyExc) (s : σ), 2 ^ 53 ≤ n → warn withoutWarnMsg = .error e →
      randbelowWithout g fuel n (2 ^ 53) warn s = (.error e, s)) ∧
    (∀ (n fuel : Nat) (u : F64) (s s1 : σ), 2 ^ 53 ≤ n → warn withoutWarnMsg = .ok () →
      g.random s = (u, s1) →
      randbelowWithout g fuel n (2 ^ 53) warn s =
        (match (do let nf ← pyFloat (n : Int); mathFloor (u * nf) : Py Int) with
         | .ok v => .ok v.toNat
         | .error e => .error e, s1))

theorem randbelowWithoutExact_proven : RandbelowWithoutExact := by
  intro _ σ g warn
  refine ⟨fun n fuel us u s s' hn hlt hrun hus hu hf => ?_, fun n fuel e s hn hw => ?_,
    fun n fuel u s s1 hn hw h => ?_⟩
  · have hrem : 2 ^ 53 % n ≤ 2 ^ 53 := Nat.mod_le _ _
    have ha := pyFloat_le_2_53 (m := 2 ^ 53 - 2 ^ 53 % n) (by omega)
    have hb := pyFloat_le_2_53 (m := 2 ^ 53) (Nat.le_refl _)
    simp only [randbelowWithout]
    rw [if_neg (by omega)]
    have hcast : (((2 ^ 53 - 2 ^ 53 % n : Nat) : Int)) = ((2 ^ 53 - 2 ^ 53 % n : Nat) : Int) := rfl
    simp only [lift_bind_apply, ha, hb]
    have key : ∀ r1 (s1 : σ), g.random s = (r1, s1) →
        (rnd g >>= fun r => drawBelow g (F64.ofInt (2 ^ 53 - 2 ^ 53 % n : Nat) / F64.ofInt (2 ^ 53 : Nat))
          fuel r >>= fun r => RM.lift (mathFloor (r * F64.ofInt (2 ^ 53 : Nat))) >>= fun v =>
            Pure.pure (v % (n : Int)).toNat) s =
        (drawBelow g (F64.ofInt (2 ^ 53 - 2 ^ 53 % n : Nat) / F64.ofInt (2 ^ 53 : Nat)) fuel r1 >>=
          fun r => RM.lift (mathFloor (r * F64.ofInt (2 ^ 53 : Nat))) >>= fun v =>
            Pure.pure (v % (n : Int)).toNat) s1 := by
      intro r1 s1 h1
      rw [rnd_bind_apply h1]
    cases us with
    | nil =>
      cases hrun with
      | cons h1 h2 =>
        cases h2 with
        | nil =>
          rw [key _ _ h1, RM.bind_apply, drawBelow_accept g _ u hu fuel]
          simp only [lift_bind_apply]
          cases mathFloor (u * F64.ofInt (2 ^ 53 : Nat)) <;> rfl
    | cons x rest =>
      cases hrun with
      | cons h1 h2 =>
        rw [key _ _ h1, RM.bind_apply, drawBelow_run g _ u s' hu rest fuel x _ (hus x (by simp)) h2
          (fun y hy => hus y (by simp [hy])) (by simp at hf; omega)]
        simp only [lift_bind_apply]
        cases mathFloor (u * F64.ofInt (2 ^ 53 : Nat)) <;> rfl
  · simp only [randbelowWithout, if_pos hn, lift_bind_apply, hw]
  · simp only [randbelowWithout, if_pos hn, lift_bind_apply, hw, rnd_bind_apply h]
    cases (pyFloat (n : Int) : Py F64) with
    | error e => rfl
    | ok nf =>
      pysimp
      cases mathFloor (u * nf) <;> rfl

/-! ### `choice`, Lib/random.py:347-354 -/

/-- `choice(seq)` is `seq[_randbelow(len(seq))]`: `IndexError` before any draw for an
empty sequence, otherwise exactly one `_randbelow(len(seq))` and the item at the index it
returns (with that item's own `__getitem__` exception), and `len` failures propagate. -/
def ChoiceExact : Prop :=
  ∀ (σ α : Type) (below : Nat → RM σ Nat) (seq : SeqObj α) (s : σ),
    (seq.len = .ok 0 → choice below seq s = (.error (.indexError "Cannot choose from an empty sequence"), s)) ∧
    (∀ e, seq.len = .error e → choice below seq s = (.error e, s)) ∧
    (∀ n, seq.len = .ok n → 0 < n →
      choice below seq s =
        match below n s with
        | (.ok j, s1) => (seq.getItem j, s1)
        | (.error e, s1) => (.error e, s1))

theorem choiceExact_proven : ChoiceExact := by
  intro σ α below seq s
  refine ⟨fun h => ?_, fun e h => ?_, fun n h hn => ?_⟩
  · simp only [choice, lift_bind_apply, h]; rfl
  · simp only [choice, lift_bind_apply, h]
  · simp only [choice, lift_bind_apply, h, if_neg (show n ≠ 0 by omega)]
    rw [RM.bind_apply]
    cases below n s with
    | mk r t => cases r <;> rfl

/-! ### `shuffle`, Lib/random.py:356-363 -/

/-- `shuffle(x)` is Fisher-Yates from the end: for `i` from `len(x) - 1` down to `1` it
calls `_randbelow(i + 1)` once and swaps `x[i]` with `x[j]`; nothing else. A sequence of
fewer than two items draws nothing. -/
def ShuffleExact : Prop :=
  ∀ (σ α : Type) (below : Nat → RM σ Nat),
    (∀ x : List α, shuffle below x none = shuffleLoop below (x.length - 1) x) ∧
    (∀ (x : List α) (s : σ), shuffleLoop below 0 x s = (.ok x, s)) ∧
    (∀ (i : Nat) (x : List α) (s s1 : σ) (j : Nat) (hi : i + 1 < x.length) (hj : j < x.length),
      below (i + 2) s = (.ok j, s1) →
      shuffleLoop below (i + 1) x s = shuffleLoop below i ((x.set (i + 1) x[j]).set j x[i + 1]) s1) ∧
    (∀ (i : Nat) (x : List α) (s s1 : σ) (e : PyExc), below (i + 2) s = (.error e, s1) →
      shuffleLoop below (i + 1) x s = (.error e, s1))

theorem shuffleExact_proven : ShuffleExact := by
  intro σ α below
  refine ⟨fun x => shuffle_none below x, fun x s => rfl, fun i x s s1 j hi hj h => ?_,
    fun i x s s1 e h => ?_⟩
  · simp only [shuffleLoop, RM.bind_apply, h, lift_bind_apply, swapAssign, RM.lift_apply]
    have g1 : listGet x j = .ok x[j] := by simp [listGet, List.getElem?_eq_getElem hj]
    have g2 : listGet x (i + 1) = .ok x[i + 1] := by simp [listGet, List.getElem?_eq_getElem hi]
    simp only [g1, g2, ex_ok_bind, ex_pure]
  · simp only [shuffleLoop, RM.bind_apply, h]

/-! ### `sample`, Lib/random.py:365-458 -/

/-- `sample(population, k)` once its arguments passed: the pool branch when
`n <= setsize`, else the set branch (:438-441). In the pool branch step `i` calls
`_randbelow(n - i)` once, takes `pool[j]`, and moves `pool[n - i - 1]` into slot `j`
(:444-448). In the set branch each step calls `_randbelow(n)` until the index is not yet
selected, then takes `population[j]` (:450-457). With counts, the result is
`[population[bisect(cum_counts, s)] for s in sample(range(total), k)]` (:431-433). -/
def SampleExact : Prop :=
  ∀ (σ α : Type) (below : Nat → RM σ Nat) (fuel : Nat),
    (∀ (pop : SeqObj α) (n : Nat) (k : Int), 0 ≤ k → k ≤ n →
      sampleCore below fuel pop n k =
        if n ≤ setsize k.toNat then poolLoop below n k.toNat 0 (pop.toList ())
        else setLoop below pop n fuel k.toNat []) ∧
    (∀ (n c i : Nat) (pool : List α) (s s1 : σ) (j : Nat) (hj : j < pool.length)
        (hm : n - i - 1 < pool.length), below (n - i) s = (.ok j, s1) →
      poolLoop below n (c + 1) i pool s =
        match poolLoop below n c (i + 1) (pool.set j pool[n - i - 1]) s1 with
        | (.ok rest, t) => (.ok (pool[j] :: rest), t)
        | (.error e, t) => (.error e, t)) ∧
    (∀ (pop : SeqObj α) (n c : Nat) (selected : List Nat) (s s1 : σ) (j : Nat),
      below n s = (.ok j, s1) →
      setLoop below pop n fuel (c + 1) selected s =
        match pickLoop below n selected fuel j s1 with
        | (.error e, t) => (.error e, t)
        | (.ok j', t) =>
          match pop.getItem j' with
          | .error e => (.error e, t)
          | .ok x =>
            match setLoop below pop n fuel c (j' :: selected) t with
            | (.ok rest, t') => (.ok (x :: rest), t')
            | (.error e, t') => (.error e, t')) ∧
    (∀ (n : Nat) (selected : List Nat) (f j : Nat) (s : σ), j ∉ selected →
      pickLoop below n selected f j s = (.ok j, s)) ∧
    (∀ (n : Nat) (selected : List Nat) (f j : Nat) (s : σ), j ∈ selected →
      pickLoop below n selected (f + 1) j s =
        match below n s with
        | (.ok j', s1) => pickLoop below n selected f j' s1
        | (.error e, s1) => (.error e, s1))

theorem sampleExact_proven : SampleExact := by
  intro σ α below fuel
  refine ⟨fun pop n k h0 h1 => ?_, fun n c i pool s s1 j hj hm h => ?_,
    fun pop n c selected s s1 j h => ?_, fun n selected f j s h => ?_, fun n selected f j s h => ?_⟩
  · simp only [sampleCore, if_neg (show ¬ ¬ (0 ≤ k ∧ k ≤ (n : Int)) from fun c => c ⟨h0, h1⟩)]
  · simp only [poolLoop, RM.bind_apply, h, lift_bind_apply, RM.lift_apply]
    have g1 : listGet pool j = .ok pool[j] := by simp [listGet, List.getElem?_eq_getElem hj]
    have g2 : listGet pool (n - i - 1) = .ok pool[n - i - 1] := by
      simp [listGet, List.getElem?_eq_getElem hm]
    simp only [g1, g2]
    cases poolLoop below n c (i + 1) (pool.set j pool[n - i - 1]) s1 with
    | mk r t => cases r <;> rfl
  · simp only [setLoop, RM.bind_apply, h]
    cases pickLoop below n selected fuel j s1 with
    | mk r t =>
      cases r with
      | error e => rfl
      | ok j' =>
        simp only [RM.lift_apply]
        cases pop.getItem j' with
        | error e => rfl
        | ok x =>
          simp only
          cases setLoop below pop n fuel c (j' :: selected) t with
          | mk r' t' => cases r' <;> rfl
  · cases f <;> simp [pickLoop, h] <;> rfl
  · simp only [pickLoop, h, if_true, RM.bind_apply]
    cases below n s with
    | mk r t => cases r <;> rfl

/-! ### `choices`, Lib/random.py:460-495 -/

/-- `choices` over binary64. Without weights each item is `population[floor(random() * n)]`
with `n = float(len(population)) + 0.0` (:470-473); with `cum_weights` (given, or the
running sums of `weights`), each item is `population[bisect(cum_weights, random() * total,
0, n - 1)]` with `total = cum_weights[-1] + 0.0`, after the checks `total > 0.0` and
`isfinite(total)` (:485-495). One `random()` per item, in order. -/
def ChoicesExact : Prop :=
  ∀ [RandLibm] (σ α : Type) (g : Gen σ F64),
    (∀ (pop : SeqObj α) (nf : F64) (k : Nat) (u : F64) (s s1 : σ), g.random s = (u, s1) →
      choicesPlain g pop nf (k + 1) s =
        match (do let j ← mathFloor (u * nf); pop.getItem j.toNat : Py α) with
        | .error e => (.error e, s1)
        | .ok x =>
          match choicesPlain g pop nf k s1 with
          | (.ok rest, t) => (.ok (x :: rest), t)
          | (.error e, t) => (.error e, t)) ∧
    (∀ (pop : SeqObj α) (cum : List (Num F64)) (total : F64) (hi k : Nat) (u : F64) (s s1 : σ),
      g.random s = (u, s1) →
      choicesWeighted g pop cum total hi (k + 1) s =
        match pop.getItem (bisectNum cum (u * total) (hi + 1) 0 hi) with
        | .error e => (.error e, s1)
        | .ok x =>
          match choicesWeighted g pop cum total hi k s1 with
          | (.ok rest, t) => (.ok (x :: rest), t)
          | (.error e, t) => (.error e, t)) ∧
    (∀ (pop : SeqObj α) (n : Nat) (k : Int) (s : σ), pop.len = .ok n →
      choices g pop none none k s =
        match (pyFloat (n : Int) : Py F64) with
        | .ok nf => choicesPlain g pop (nf + 0.0) k.toNat s
        | .error e => (.error e, s)) ∧
    (∀ (pop : SeqObj α) (n : Nat) (xs : List (Num F64)) (k : Int) (s : σ), pop.len = .ok n →
      choices g pop (some (.seq xs)) none k s =
        match accumulateNums xs with
        | .ok cum => choicesCum g pop n cum k s
        | .error e => (.error e, s)) ∧
    (∀ (pop : SeqObj α) (n : Nat) (cum : List (Num F64)) (k : Int) (s : σ), pop.len = .ok n →
      choices g pop none (some cum) k s = choicesCum g pop n cum k s) ∧
    (∀ (pop : SeqObj α) (n : Nat) (cum : List (Num F64)) (k : Int) (s : σ),
      choicesCum g pop n cum k s =
        if cum.length ≠ n then (.error (.valueError "The number of weights does not match the population"), s)
        else match cum.getLast? with
          | none => (.error (.indexError "list index out of range"), s)
          | some last =>
            match (match last with
                   | .int a => (do let x ← pyFloat a; pure (x + 0.0) : Py F64)
                   | .flt x => .ok (x + 0.0)) with
            | .error e => (.error e, s)
            | .ok total =>
              if Flt.le total 0.0 then (.error (.valueError "Total of weights must be greater than zero"), s)
              else if !Flt.isFinite total then (.error (.valueError "Total of weights must be finite"), s)
              else choicesWeighted g pop cum total (n - 1) k.toNat s)

theorem choicesExact_proven : ChoicesExact := by
  intro _ σ α g
  refine ⟨fun pop nf k u s s1 h => ?_, fun pop cum total hi k u s s1 h => ?_,
    fun pop n k s hn => ?_, fun pop n xs k s hn => ?_, fun pop n cum k s hn => ?_,
    fun pop n cum k s => ?_⟩
  · simp only [choicesPlain, rnd_bind_apply h, lift_bind_apply]
    cases mathFloor (u * nf) with
    | error e => rfl
    | ok j =>
      pysimp
      cases pop.getItem j.toNat with
      | error e => rfl
      | ok x =>
        pysimp
        rw [RM.bind_apply]
        cases choicesPlain g pop nf k s1 with
        | mk r t => cases r <;> rfl
  · simp only [choicesWeighted, rnd_bind_apply h, lift_bind_apply]
    cases pop.getItem (bisectNum cum (u * total) (hi + 1) 0 hi) with
    | error e => rfl
    | ok x =>
      pysimp
      rw [RM.bind_apply]
      cases choicesWeighted g pop cum total hi k s1 with
      | mk r t => cases r <;> rfl
  · simp only [choices, lift_bind_apply, hn]
    cases (pyFloat (n : Int) : Py F64) <;> rfl
  · simp only [choices, lift_bind_apply, hn]
    cases accumulateNums xs <;> rfl
  · simp only [choices, lift_bind_apply, hn]
  · unfold choicesCum
    by_cases hl : cum.length ≠ n
    · rw [if_pos hl, if_pos hl]; rfl
    · rw [if_neg hl, if_neg hl]
      cases cum.getLast? with
      | none => rfl
      | some last =>
        simp only [lift_bind_apply]
        cases last with
        | int a =>
          dsimp only
          cases (pyFloat a : Py F64) with
          | error e => rfl
          | ok x =>
            simp only [ex_ok_bind, ex_pure]
            by_cases h1 : Flt.le (x + 0.0) 0.0 = true
            · simp only [h1, if_true, RM.raise_apply]
            · simp only [h1, Bool.false_eq_true, if_false]
              by_cases h2 : (!Flt.isFinite (x + 0.0)) = true
              · simp only [h2, if_true, RM.raise_apply]
              · simp only [h2, Bool.false_eq_true, if_false]
        | flt x =>
          dsimp only
          by_cases h1 : Flt.le (x + 0.0) 0.0 = true
          · simp only [h1, if_true, RM.raise_apply]
          · simp only [h1, Bool.false_eq_true, if_false]
            by_cases h2 : (!Flt.isFinite (x + 0.0)) = true
            · simp only [h2, if_true, RM.raise_apply]
            · simp only [h2, Bool.false_eq_true, if_false]

end PyLean.CoreLibs.Rand
