import PyLean.CoreLibs.CalStat.DistProps

/-!
The value of `fmean`, `geometric_mean` and `NormalDist.pdf`, where FmeanChecks, GeometricChecks and NormalDistUndefined state only
when they raise. What the C library computes stays abstract, in `Libm`.
-/

namespace PyLean.CoreLibs.CalStat

open PyLean

/-- `fmean`: the exact sum of `fsum` over the count, and with weights `sumprod` over the sum of the weights. Each step's
exception comes out, and only `sumprod`'s `ValueError` becomes the length message. -/
def FmeanExact : Prop :=
  ∀ (data w : List PyN) (total den : Flt) (num : Val) (e : PyExc) (m : String),
    (data ≠ [] → fsumV (data.map (·.v)) = .ok total → fmean data none = vdiv (.flt total) (.int data.length)) ∧
    (fsumV (data.map (·.v)) = .error e → fmean data none = .error e) ∧
    (sumprod data w = .ok num → fsumV (w.map (·.v)) = .ok den → den.truthy = true →
      fmean data (some w) = vdiv num (.flt den)) ∧
    (sumprod data w = .ok num → fsumV (w.map (·.v)) = .ok den → den.truthy = false →
      fmean data (some w) = .error (.named "StatisticsError" "sum of weights must be non-zero")) ∧
    (sumprod data w = .error (.valueError m) →
      fmean data (some w) = .error (.named "StatisticsError" "data and weights must be the same length"))

theorem fmeanExact_proven : FmeanExact := by
  intro data w total den num e m
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h1 h2
    have h0 : data.length ≠ 0 := by simpa using h1
    simp [fmean, h2, h0, bind, Except.bind, pure, Except.pure]
  · intro h
    simp [fmean, h, bind, Except.bind]
  · intro h1 h2 h3
    simp [fmean, h1, h2, h3, bind, Except.bind, pure, Except.pure]
  · intro h1 h2 h3
    simp [fmean, h1, h2, h3, bind, Except.bind, pure, Except.pure, statErr, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw]
  · intro h
    simp [fmean, h, bind, Except.bind, statErr]

/-- `geometric_mean` after its scan: `exp` of the mean of the logarithms, read from the state the scan leaves; a NaN total is
NaN; a zero in the data gives `0.0`, or NaN when an infinity was there too. A failure of the scan or of `fsum` comes out. -/
def GeometricExact : Prop :=
  ∀ (L : Libm) (data : List PyN) (st : GmSt) (total : Flt) (e : PyExc),
    ((data.map (·.v)).foldlM (gmStep L) ({} : GmSt) = .error e → geometricMean L data = .error e) ∧
    ((data.map (·.v)).foldlM (gmStep L) ({} : GmSt) = .ok st → fsumEnd st.fs = .error e → geometricMean L data = .error e) ∧
    ((data.map (·.v)).foldlM (gmStep L) ({} : GmSt) = .ok st → fsumEnd st.fs = .ok total → st.n ≠ 0 →
      (total.isNan = true → geometricMean L data = .ok .nan) ∧
      (total.isNan = false → st.foundZero = true →
        geometricMean L data = .ok (if Flt.eq total (.inf false) then .nan else Flt.pz)) ∧
      (total.isNan = false → st.foundZero = false →
        geometricMean L data = (fltDiv total (Flt.ofInt st.n)).bind (mathExp L)))

theorem geometricExact_proven : GeometricExact := by
  intro L data st total e
  refine ⟨?_, ?_, ?_⟩
  · intro h
    simp [geometricMean, h, bind, Except.bind]
  · intro h1 h2
    simp [geometricMean, h1, h2, bind, Except.bind]
  · intro h1 h2 h3
    refine ⟨?_, ?_, ?_⟩
    · intro h
      simp [geometricMean, h1, h2, h3, h, bind, Except.bind, pure, Except.pure]
    · intro h4 h5
      simp [geometricMean, h1, h2, h3, h4, h5, bind, Except.bind, pure, Except.pure]
    · intro h4 h5
      simp [geometricMean, h1, h2, h3, h4, h5, bind, Except.bind, pure, Except.pure]

/-- `NormalDist.pdf` of a float, Lib/statistics.py:1259-1265: `z` from `x`, `mu` and `sigma`, then `exp(-0.5 * z * z)` over
`sqrt(tau) * sigma`, for every `sigma` that is not zero, including one whose square underflows, which raised before 3.15. A
range error of `exp` comes out. `sigma` is not zero, so its quotients do not raise. -/
def PdfExact : Prop :=
  ∀ (L : Libm) (X : ND) (x : Flt), X.sigma.truthy = true → (∃ q, X.sigma = .fin q) →
    let z := Flt.div (Flt.sub x X.mu) X.sigma
    ND.pdf L X (.flt x) =
      match mathExp L (Flt.mul (Flt.mul (Flt.neg Flt.half) z) z) with
      | .error e => .error e
      | .ok r => (fltDiv r (Flt.mul sqrt2pi X.sigma)).map .flt

theorem pdfExact_proven : PdfExact := by
  intro L X x h ⟨q, hq⟩
  rw [hq] at h
  simp only [ND.pdf, hq, h, Bool.not_true, Bool.false_eq_true, ite_false, bind, Except.bind, vsub, vdiv, vmul, arith, subOp,
    divOp, mulOp, fltDiv, pure, Except.pure, Functor.map, Except.map, asDouble, toFloat]
  cases mathExp L _ with
  | error e => rfl
  | ok r =>
    simp only [Except.map]

end PyLean.CoreLibs.CalStat
