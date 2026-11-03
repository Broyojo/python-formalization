import PyLean.CoreLibs.CalStat.StatND

/-!
`geometric_mean` (Lib/statistics.py:225-262): the scan `count_positive` inside
`fsum(map(log, ...))`. The theorems pin what the scan feeds to `fsum`, the logarithms of the
positive items in order, and what it records, the count and whether a zero was met, against
`math.fsum(map(math.log, positives))` written independently of the generator.
-/

namespace PyLean.CoreLibs.CalStat

open PyLean

/-- `x > 0.0` holds (and does not raise). -/
def posB (x : Val) : Bool := decide (vltPy (.flt Flt.pz) x = .ok true)

/-- `x` is a zero the scan accepts: `x > 0.0` is false, `math.isnan(x)` is false, `x == 0.0`. -/
def ZeroV (x : Val) : Prop :=
  vltPy (.flt Flt.pz) x = .ok false ∧ (Flt.isNan <$> asDouble x) = .ok false ∧ veq x (.flt Flt.pz) = true

/-- `x` is negative for the scan: `x > 0.0` is false, `math.isnan(x)` is false, `x == 0.0` is false. -/
def NegV (x : Val) : Prop :=
  vltPy (.flt Flt.pz) x = .ok false ∧ (Flt.isNan <$> asDouble x) = .ok false ∧ veq x (.flt Flt.pz) = false

/-- The partials loop of `math.fsum(map(math.log, xs))`: each `log` is taken, then added, before
the next item is looked at. -/
def fsumLogs (L : Libm) (xs : List Val) (st : FsumState) : Py FsumState :=
  xs.foldlM (fun fs v => do fsumStep fs (← mathLog L v)) st

theorem gm_pos (L : Libm) (st : GmSt) (x : Val) (h : vltPy (.flt Flt.pz) x = .ok true) :
    gmStep L st x = (do
      let l ← mathLog L x
      let fs ← fsumStep st.fs l
      return { n := st.n + 1, foundZero := st.foundZero, fs := fs }) := by
  simp only [gmStep, h, ok_bind', ite_true, Bool.true_or]
  cases mathLog L x with
  | error e => rfl
  | ok l =>
    simp only [ok_bind']
    cases fsumStep st.fs l <;> rfl

theorem gm_zero' (L : Libm) (st : GmSt) (x : Val) (h : ZeroV x) :
    gmStep L st x = .ok { n := st.n + 1, foundZero := true, fs := st.fs } := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [gmStep, h1, ok_bind', Bool.false_eq_true, ite_false, h2, Bool.false_or, h3, ite_true]
  rfl

theorem gm_neg (L : Libm) (st : GmSt) (x : Val) (h : NegV x) :
    gmStep L st x = .error (statErr "~No negative inputs allowed: x") := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [gmStep, h1, ok_bind', Bool.false_eq_true, ite_false, h2, Bool.false_or, h3]
  rfl

theorem posB_of_pos {x : Val} (h : vltPy (.flt Flt.pz) x = .ok true) : posB x = true := by
  simp [posB, h]

theorem posB_of_zero {x : Val} (h : ZeroV x) : posB x = false := by
  simp [posB, h.1]

/-- The scan over items that are positive or zero: the logarithms of the positive ones go to `fsum`
in order, `n` counts every item, `found_zero` records a zero. -/
theorem gm_fold (L : Libm) (xs : List Val) :
    ∀ st : GmSt, (∀ x ∈ xs, vltPy (.flt Flt.pz) x = .ok true ∨ ZeroV x) →
    xs.foldlM (gmStep L) st = (fsumLogs L (xs.filter posB) st.fs).map
      (fun fs => { n := st.n + xs.length, foundZero := st.foundZero || xs.any (fun x => !posB x), fs := fs }) := by
  induction xs with
  | nil =>
    intro st _
    cases st; simp [fsumLogs, Functor.map, Except.map]; rfl
  | cons x xs ih =>
    intro st h
    have hx := h x (by simp)
    have hr : ∀ y ∈ xs, vltPy (.flt Flt.pz) y = .ok true ∨ ZeroV y := fun y hy => h y (by simp [hy])
    rcases hx with hp | hz
    · rw [List.foldlM_cons, gm_pos L st x hp]
      simp only [List.filter_cons, posB_of_pos hp, ite_true, fsumLogs, List.foldlM_cons]
      cases hl : mathLog L x with
      | error e => rfl
      | ok l =>
        simp only [ok_bind']
        cases hf : fsumStep st.fs l with
        | error e => rfl
        | ok fs1 =>
          simp only [ok_bind', pure, Except.pure]
          rw [ih _ hr]
          simp only [fsumLogs, List.any_cons, posB_of_pos hp, Bool.not_true, Bool.false_or, List.length_cons]
          cases (xs.filter posB).foldlM (fun fs v => do fsumStep fs (← mathLog L v)) fs1 with
          | error e => rfl
          | ok fs2 =>
            simp only [Functor.map, Except.map, Except.ok.injEq, GmSt.mk.injEq]
            refine ⟨by omega, ?_⟩; simp
    · rw [List.foldlM_cons, gm_zero' L st x hz, ok_bind', ih _ hr]
      simp only [List.filter_cons, posB_of_zero hz, Bool.false_eq_true, ite_false, List.any_cons, Bool.not_false,
        Bool.true_or, Bool.or_true, List.length_cons]
      cases fsumLogs L (xs.filter posB) st.fs with
      | error e => rfl
      | ok fs2 =>
        simp only [Functor.map, Except.map, Except.ok.injEq, GmSt.mk.injEq]
        refine ⟨by omega, ?_⟩; simp

/-- `geometric_mean`, statistics.py:225-262, through its scan `count_positive` (:243-251):

* all items positive: the result is `exp(fsum(map(log, data)) / n)`, NaN when that sum is NaN;
* items positive or zero with at least one zero: `0.0`, or NaN when the sum of the logarithms of the
  positive items is NaN or `+inf` (:259-260);
* the first item that is neither positive, NaN nor zero raises `StatisticsError` (its `repr` in the
  message, `~`), after the logarithms of the positive items before it, whose own errors come first;
* no data raises.

Every item is a number (`Val`); a user object whose `>` raises `StopIteration` inside the generator
(PEP 479) is out of scope. -/
def GeometricScan : Prop :=
  ∀ (L : Libm) (xs : List Val),
    ((∀ x ∈ xs, vltPy (.flt Flt.pz) x = .ok true) → xs ≠ [] →
      geometricMean L (xs.map Val.toN) =
        (do
          let fs ← fsumLogs L xs {}
          let total ← fsumEnd fs
          if total.isNan then return .nan
          mathExp L (← fltDiv total (Flt.ofInt xs.length)))) ∧
    ((∀ x ∈ xs, vltPy (.flt Flt.pz) x = .ok true ∨ ZeroV x) → (∃ x ∈ xs, ZeroV x) →
      geometricMean L (xs.map Val.toN) =
        (do
          let fs ← fsumLogs L (xs.filter posB) {}
          let total ← fsumEnd fs
          return (if total.isNan then .nan else if Flt.eq total (.inf false) then .nan else Flt.pz))) ∧
    (∀ (pre rest : List Val) (x : Val), (∀ y ∈ pre, vltPy (.flt Flt.pz) y = .ok true ∨ ZeroV y) → NegV x →
      xs = pre ++ x :: rest →
      geometricMean L (xs.map Val.toN) =
        (do
          let _ ← fsumLogs L (pre.filter posB) {}
          .error (.named "StatisticsError" "~No negative inputs allowed: x"))) ∧
    geometricMean L [] = .error (.named "StatisticsError" "Must have a non-empty dataset")

theorem map_v (xs : List Val) : (xs.map Val.toN).map (·.v) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, ih]; rfl

theorem geometricScan_proven : GeometricScan := by
  intro L xs
  refine ⟨?_, ?_, ?_, by simp [geometricMean, statErr, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]; rfl⟩
  · intro hp hne
    have hfold := gm_fold L xs {} (fun x hx => Or.inl (hp x hx))
    have hf : xs.filter posB = xs := List.filter_eq_self.mpr (fun x hx => posB_of_pos (hp x hx))
    have ha : xs.any (fun x => !posB x) = false := by
      simp only [List.any_eq_false]; intro x hx; simp [posB_of_pos (hp x hx)]
    have hl : xs.length ≠ 0 := by simpa using hne
    simp only [geometricMean, map_v, hfold, hf, ha]
    cases fsumLogs L xs {} with
    | error e => rfl
    | ok fs =>
      simp only [Functor.map, Except.map, ok_bind', Bool.or_false]
      cases fsumEnd fs with
      | error e => rfl
      | ok total =>
        simp only [ok_bind', Nat.zero_add, hl, ite_false]
        cases total.isNan <;> simp [Bool.false_eq_true, pure, Except.pure]
  · intro hn hz
    have hfold := gm_fold L xs {} hn
    have ha : xs.any (fun x => !posB x) = true := by
      obtain ⟨x, hx, hzx⟩ := hz
      exact List.any_eq_true.mpr ⟨x, hx, by simp [posB_of_zero hzx]⟩
    have hl : xs.length ≠ 0 := by
      obtain ⟨x, hx, -⟩ := hz
      exact List.length_pos_of_mem hx |> Nat.pos_iff_ne_zero.mp
    simp only [geometricMean, map_v, hfold, ha]
    cases fsumLogs L (xs.filter posB) {} with
    | error e => rfl
    | ok fs =>
      simp only [Functor.map, Except.map, ok_bind', Bool.false_or]
      cases fsumEnd fs with
      | error e => rfl
      | ok total =>
        simp only [ok_bind', Nat.zero_add, hl, ite_false, ite_true]
        cases total.isNan <;> simp [Bool.false_eq_true, pure, Except.pure]
  · intro pre rest x hpre hneg hxs
    subst hxs
    simp only [geometricMean, map_v, List.foldlM_append, gm_fold L pre {} hpre, List.foldlM_cons]
    cases fsumLogs L (pre.filter posB) {} with
    | error e => rfl
    | ok fs =>
      simp only [Functor.map, Except.map, ok_bind', gm_neg L _ x hneg]
      rfl

end PyLean.CoreLibs.CalStat
