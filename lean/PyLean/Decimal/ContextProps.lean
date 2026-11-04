import PyLean.Decimal.CContext
import PyLean.Decimal.OpsProps

/-!
Properties of the conversion layer, `_raise_error`, the `Context` wrappers and
the `Context` objects of both twins.
-/

namespace PyLean.Decimal

open PyLean

/-! ## `_raise_error` -/

/-- For every condition: an ignored signal sets no flag and raises nothing; otherwise
the flag is set, and the condition's handler gives the result unless the signal is
trapped, when its exception is raised. The handlers return what the docs of each signal
say: NaN, or a signed infinity for DivisionByZero, or the rounding mode's overflow value. -/
def RaiseErrorCorrect : Prop :=
  ∀ (c : Ctx) (ignored : List Signal) (cnd : Cond) (fl : List Signal),
    (cnd.signal ∈ ignored → (raiseError c ignored cnd).run fl = .ok (handle c cnd, fl)) ∧
    (cnd.signal ∉ ignored → cnd.signal ∉ c.traps →
      (raiseError c ignored cnd).run fl =
        .ok (handle c cnd, if cnd.signal ∈ fl then fl else fl ++ [cnd.signal])) ∧
    (cnd.signal ∉ ignored → cnd.signal ∈ c.traps →
      (raiseError c ignored cnd).run fl = .error (.named cnd.signal.name "~")) ∧
    (raiseError c [] cnd).run fl = (do raiseSig c cnd.signal; pure (handle c cnd)).run fl ∧
    (∀ s, handle c (.divisionByZero s) = some (.inf s)) ∧
    (∀ s, handle c (.overflow s) = some (overflowResult c s)) ∧
    (∀ a, handle c (.invalidOperation (some a)) = some (quietOf c a)) ∧
    handle c (.invalidOperation none) = some nanD ∧
    handle c .conversionSyntax = some nanD ∧ handle c .divisionImpossible = some nanD ∧
    handle c .divisionUndefined = some nanD ∧ handle c .invalidContext = some nanD ∧
    (∀ s, handle c (.plain s) = none)

theorem raiseErrorCorrect_proven : RaiseErrorCorrect := by
  intro c ignored cnd fl
  refine ⟨?_, ?_, ?_, ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  · intro h
    simp [raiseError, h, StateT.run, pure, StateT.pure, Except.pure, bind, StateT.bind, Except.bind]
  · intro h1 h2
    simp [raiseError, h1, h2, StateT.run, pure, StateT.pure, Except.pure, bind, StateT.bind, Except.bind,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
  · intro h1 h2
    simp [raiseError, h1, h2, StateT.run, bind, StateT.bind, Except.bind,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw, StateT.lift, liftM, monadLift, MonadLift.monadLift, Except.pure, pure]
  · by_cases h : cnd.signal ∈ c.traps <;>
    simp [raiseError, raiseSig, h, StateT.run, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw, StateT.lift, liftM, monadLift, MonadLift.monadLift]

/-! ## Conversions and the wrappers -/

theorem liftPy_ok_run {α β : Type} {x : Py α} {v : α} (g : α → DM β) (fl : List Signal)
    (h : x = .ok v) : (liftPy x >>= g).run fl = (g v).run fl := by
  subst h; rfl

theorem liftPy_err_run {α β : Type} {x : Py α} {e : PyExc} (g : α → DM β) (fl : List Signal)
    (h : x = .error e) : (liftPy x >>= g).run fl = .error e := by
  subst h; rfl

/-- `convertRaise` is `convertOther true`, with the same error when conversion fails. -/
theorem convertOther_false (b : Arg) (y : Dec) (h : convertRaise b = .ok y) :
    convertOther false b = .ok (some y) := by
  cases b with
  | dec d => simpa [convertRaise, convertOther, bind, Except.bind, pure, Except.pure] using h
  | int n =>
    simp only [convertRaise, convertOther, bind, Except.bind, pure, Except.pure] at h ⊢
    cases hp : pyFromInt n with
    | error e => simp [hp] at h
    | ok d => simpa [hp] using h
  | tuple t => simp [convertRaise, convertOther, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw, pure, Except.pure] at h
  | other s => simp [convertRaise, convertOther, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw, pure, Except.pure] at h

theorem convertOther_false_err (b : Arg) (e : PyExc) (h : convertRaise b = .error e) :
    convertOther false b = .error e ∨ (convertOther false b = .ok none ∧ e = unableExc b) := by
  cases b with
  | dec d => simp [convertRaise, convertOther, bind, Except.bind, pure, Except.pure] at h
  | int n =>
    left
    simp only [convertRaise, convertOther, bind, Except.bind, pure, Except.pure] at h ⊢
    cases hp : pyFromInt n with
    | error e' => simp_all
    | ok d => simp [hp] at h
  | tuple t =>
    right
    simp [convertRaise, convertOther, bind, Except.bind, pure, Except.pure] at h
    exact ⟨rfl, h.symm⟩
  | other s =>
    right
    simp [convertRaise, convertOther, bind, Except.bind, pure, Except.pure] at h
    exact ⟨rfl, h.symm⟩

/-- What `C.m(a, b)` should do: `x.m(y, context=C)` for the operands converted in
order, an error from the first conversion that fails. -/
def Equiv2 {α : Type} (w : Ctx → Arg → Arg → DM α) (f : Ctx → Dec → Dec → DM α) : Prop :=
  ∀ (c : Ctx) (a b : Arg) (fl : List Signal),
    match convertRaise a, convertRaise b with
    | .ok x, .ok y => (w c a b).run fl = (f c x y).run fl
    | .ok _, .error e => (w c a b).run fl = .error e
    | .error e, _ => (w c a b).run fl = .error e

/-- The one-operand form of `Equiv2`. -/
def Equiv1 {α : Type} (w : Ctx → Arg → DM α) (f : Ctx → Dec → DM α) : Prop :=
  ∀ (c : Ctx) (a : Arg) (fl : List Signal),
    match convertRaise a with
    | .ok x => (w c a).run fl = (f c x).run fl
    | .error e => (w c a).run fl = .error e

theorem ctxUn_equiv {α : Type} (f : Ctx → Dec → DM α) : Equiv1 (ctxUn f) f := by
  intro c a fl
  cases ha : convertRaise a with
  | ok x => exact liftPy_ok_run (f c) fl ha
  | error e => exact liftPy_err_run (f c) fl ha

theorem ctxBin_equiv {α : Type} (f : Ctx → Dec → Dec → DM α) : Equiv2 (ctxBin f) f := by
  intro c a b fl
  cases ha : convertRaise a with
  | error e => exact liftPy_err_run _ fl ha
  | ok x =>
    cases hb : convertRaise b with
    | ok y =>
      simp only [ctxBin]
      rw [liftPy_ok_run _ fl ha, liftPy_ok_run _ fl hb]
    | error e =>
      simp only [ctxBin]
      rw [liftPy_ok_run _ fl ha, liftPy_err_run _ fl hb]

/-- `DM`'s bind, one step. -/
theorem bind_run {α β : Type} (x : DM α) (g : α → DM β) (fl : List Signal) :
    (x >>= g).run fl = (match x.run fl with
      | .ok p => (g p.1).run p.2
      | .error e => .error e) := by
  simp only [StateT.run, bind, StateT.bind, Except.bind]
  cases x fl with
  | error e => rfl
  | ok v => rfl

theorem opArg_run {α : Type} (f : Ctx → Dec → Dec → DM α) (c : Ctx) (x y : Dec) (b : Arg)
    (fl : List Signal) (hb : convertRaise b = .ok y) :
    (opArg f c x b).run fl = (match (f c x y).run fl with
      | .ok p => .ok (some p.1, p.2)
      | .error e => .error e) := by
  simp only [opArg]
  rw [liftPy_ok_run _ fl (convertOther_false b y hb)]
  simp only [StateT.run, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure]
  try (cases f c x y fl <;> rfl)

theorem ctxOp_equiv {α : Type} (f : Ctx → Dec → Dec → DM α) : Equiv2 (ctxOp f) f := by
  intro c a b fl
  cases ha : convertRaise a with
  | error e => exact liftPy_err_run _ fl ha
  | ok x =>
    cases hb : convertRaise b with
    | ok y =>
      simp only [ctxOp]
      rw [liftPy_ok_run _ fl ha, bind_run, opArg_run f c x y b fl hb]
      cases f c x y |>.run fl with
      | error e => rfl
      | ok v => rfl
    | error e =>
      simp only [ctxOp]
      rw [liftPy_ok_run _ fl ha, bind_run]
      rcases convertOther_false_err b e hb with h | ⟨h, rfl⟩
      · simp only [opArg]
        rw [liftPy_err_run _ fl h]
      · simp only [opArg]
        rw [liftPy_ok_run _ fl h]
        rfl

/-- `Context.fma` under the same reading as `Equiv2`, for three operands. -/
theorem contextFma_equiv (c : Ctx) (a b t : Arg) (x y z : Dec) (fl : List Signal)
    (ha : convertRaise a = .ok x) (hb : convertRaise b = .ok y) (ht : convertRaise t = .ok z) :
    (contextFma c a b t).run fl = (fma c x y z).run fl := by
  simp only [contextFma]
  rw [liftPy_ok_run _ fl ha, liftPy_ok_run _ fl hb, liftPy_ok_run _ fl ht]

/-- "For a Context instance C and Decimal instance x, C.exp(x) is equivalent to
x.exp(context=C). Each Context method accepts a Python integer anywhere that a Decimal
instance is accepted." (Doc/library/decimal.rst:1164-1168.) Every `Context` method taking
one or two operands behaves as the `Decimal` method on the operands converted by
`_convert_other`, and an operand that is neither raises the conversion's error. The
exceptions the docs do not mention, `canonical` and `is_canonical`, take only a Decimal. -/
def ContextMethodsMatchDecimal : Prop :=
  Equiv2 contextAdd add ∧ Equiv2 contextSubtract sub ∧ Equiv2 contextMultiply mul ∧
  Equiv2 contextDivide truediv ∧ Equiv2 contextDivideInt floordivD ∧
  Equiv2 contextDivmod divmodD ∧ Equiv2 contextRemainder modD ∧
  Equiv2 contextCompare compareD ∧ Equiv2 contextCompareSignal compareSignal ∧
  Equiv2 contextMax maxD ∧ Equiv2 contextMaxMag maxMag ∧ Equiv2 contextMin minD ∧
  Equiv2 contextMinMag minMag ∧ Equiv2 contextLogicalAnd logicalAnd ∧
  Equiv2 contextLogicalOr logicalOr ∧ Equiv2 contextLogicalXor logicalXor ∧
  Equiv2 contextNextToward nextToward ∧ Equiv2 contextQuantize (fun c a b => quantize c a b) ∧
  Equiv2 contextRemainderNear remainderNear ∧ Equiv2 contextRotate rotate ∧
  Equiv2 contextScaleb scaleb ∧ Equiv2 contextShift shift ∧
  Equiv2 contextCompareTotal (fun _ a b => pure (decOfInt (compareTotal a b))) ∧
  Equiv2 contextCompareTotalMag (fun _ a b => pure (decOfInt (compareTotalMag a b))) ∧
  Equiv2 contextCopySign (fun _ a b => pure (copySign a b)) ∧
  Equiv2 contextSameQuantum (fun _ a b => pure (sameQuantum a b)) ∧
  Equiv1 contextAbs (fun c a => dunderAbs c a) ∧ Equiv1 contextLogb logb ∧
  Equiv1 contextLogicalInvert logicalInvert ∧ Equiv1 contextMinus dunderNeg ∧
  Equiv1 contextPlus dunderPos ∧ Equiv1 contextNextMinus nextMinus ∧
  Equiv1 contextNextPlus nextPlus ∧ Equiv1 contextNormalize normalize ∧
  Equiv1 contextToIntegralExact (fun c a => toIntegralExact c a) ∧
  Equiv1 contextToIntegralValue (fun c a => toIntegralValue c a) ∧
  Equiv1 contextNumberClass (fun c a => pure (numberClass c a)) ∧
  Equiv1 contextIsNormal (fun c a => pure (isNormal c a)) ∧
  Equiv1 contextIsSubnormal (fun c a => pure (isSubnormal c a)) ∧
  Equiv1 contextToEngString (fun c a => pure (toEng a c.capitals)) ∧
  Equiv1 contextToSciString (fun c a => liftPy (pyStr a c.capitals)) ∧
  Equiv1 contextCopyAbs (fun _ a => pure (copyAbs a)) ∧
  Equiv1 contextCopyNegate (fun _ a => pure (copyNegate a)) ∧
  Equiv1 contextCopyDecimal (fun _ a => pure a) ∧
  Equiv1 contextIsFinite (fun _ a => pure (isFinite a)) ∧
  Equiv1 contextIsInfinite (fun _ a => pure (isInfinite a)) ∧
  Equiv1 contextIsNan (fun _ a => pure (isNanP a)) ∧
  Equiv1 contextIsQnan (fun _ a => pure (isQnan a)) ∧
  Equiv1 contextIsSigned (fun _ a => pure (isSigned a)) ∧
  Equiv1 contextIsSnan (fun _ a => pure (isSnan a)) ∧
  Equiv1 contextIsZero (fun _ a => pure (isZero a)) ∧
  (∀ d, contextCanonical (.dec d) = .ok d ∧ contextIsCanonical (.dec d) = .ok true) ∧
  (∀ n, contextCanonical (.int n) = .error (.typeError "canonical requires a Decimal as an argument.") ∧
    contextIsCanonical (.int n) = .error (.typeError "is_canonical requires a Decimal as an argument.")) ∧
  contextRadix = .fin false 10 0 ∧
  (∀ (c : Ctx) (a b t : Arg) (x y z : Dec) (fl : List Signal),
    convertRaise a = .ok x → convertRaise b = .ok y → convertRaise t = .ok z →
    (contextFma c a b t).run fl = (fma c x y z).run fl)

theorem contextMethodsMatchDecimal_proven : ContextMethodsMatchDecimal := by
  refine ⟨ctxOp_equiv _, ctxOp_equiv _, ctxOp_equiv _, ctxOp_equiv _, ctxOp_equiv _, ctxOp_equiv _,
    ctxOp_equiv _, ctxBin_equiv _, ctxBin_equiv _, ctxBin_equiv _, ctxBin_equiv _, ctxBin_equiv _,
    ctxBin_equiv _, ctxBin_equiv _, ctxBin_equiv _, ctxBin_equiv _, ctxBin_equiv _, ctxBin_equiv _,
    ctxBin_equiv _, ctxBin_equiv _, ctxBin_equiv _, ctxBin_equiv _, ctxBin_equiv _, ctxBin_equiv _,
    ctxBin_equiv _, ctxBin_equiv _, ctxUn_equiv _, ctxUn_equiv _, ctxUn_equiv _, ctxUn_equiv _,
    ctxUn_equiv _, ctxUn_equiv _, ctxUn_equiv _, ctxUn_equiv _, ctxUn_equiv _, ctxUn_equiv _,
    ctxUn_equiv _, ctxUn_equiv _, ctxUn_equiv _, ctxUn_equiv _, ctxUn_equiv _, ctxUn_equiv _,
    ctxUn_equiv _, ctxUn_equiv _, ctxUn_equiv _, ctxUn_equiv _, ctxUn_equiv _, ctxUn_equiv _,
    ctxUn_equiv _, ctxUn_equiv _, ctxUn_equiv _, ?_, ?_, rfl, ?_⟩
  · intro d; exact ⟨rfl, rfl⟩
  · intro n; exact ⟨rfl, rfl⟩
  · intro c a b t x y z fl ha hb ht
    exact contextFma_equiv c a b t x y z fl ha hb ht

/-- `a.__rop__(b)`: for a Decimal or int `b`, the operator with the operands
swapped; for anything else `NotImplemented`. Without this, `3 - Decimal(1)` would not
reach `__sub__` with 3 converted first. -/
def ReflectedOperators : Prop :=
  ∀ (c : Ctx) (a y : Dec) (b : Arg) (fl : List Signal),
    (convertRaise b = .ok y →
      (rsub c a b).run fl = ((sub c y a).run fl).map (fun p => (some p.1, p.2)) ∧
      (rtruediv c a b).run fl = ((truediv c y a).run fl).map (fun p => (some p.1, p.2)) ∧
      (rdivmod c a b).run fl = ((divmodD c y a).run fl).map (fun p => (some p.1, p.2)) ∧
      (rmod c a b).run fl = ((modD c y a).run fl).map (fun p => (some p.1, p.2)) ∧
      (rfloordiv c a b).run fl = ((floordivD c y a).run fl).map (fun p => (some p.1, p.2))) ∧
    (∀ s, (rsub c a (.other s)).run fl = .ok (none, fl) ∧ (rtruediv c a (.other s)).run fl = .ok (none, fl) ∧
      (rdivmod c a (.other s)).run fl = .ok (none, fl) ∧ (rmod c a (.other s)).run fl = .ok (none, fl) ∧
      (rfloordiv c a (.other s)).run fl = .ok (none, fl))

theorem ropArg_run {α : Type} (f : Ctx → Dec → Dec → DM α) (c : Ctx) (a y : Dec) (b : Arg)
    (fl : List Signal) (hb : convertRaise b = .ok y) :
    (ropArg f c a b).run fl = ((f c y a).run fl).map (fun p => (some p.1, p.2)) := by
  simp only [ropArg]
  rw [liftPy_ok_run _ fl (convertOther_false b y hb)]
  simp only [StateT.run, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, Except.map]
  try (cases f c y a fl <;> rfl)

theorem reflectedOperators_proven : ReflectedOperators := by
  intro c a y b fl
  refine ⟨fun hb => ⟨ropArg_run _ c a y b fl hb, ropArg_run _ c a y b fl hb, ropArg_run _ c a y b fl hb,
    ropArg_run _ c a y b fl hb, ropArg_run _ c a y b fl hb⟩, fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-! ## New contexts -/

theorem ebind_ok {α β : Type} {x : Py α} {f : α → Py β} {r : β} (h : (x >>= f) = .ok r) :
    ∃ a, x = .ok a ∧ f a = .ok r := by
  cases hx : x with
  | error e => simp [hx, bind, Except.bind] at h
  | ok v => exact ⟨v, rfl, by simpa [hx, bind, Except.bind] using h⟩

/-- A template with `flags` set, as after `DefaultContext.divide(...)`. -/
def dirtyTemplate : CContext := { dfltCtx with status := [.inexact, .rounded] }

/-- "If the flags field is not specified or is None, all flags are cleared."
(Doc/library/decimal.rst:1110-1111), for `_decimal`, for any state of `DefaultContext`. -/
def ContextNewClearsFlagsC : Prop :=
  ∀ (t c : CContext), cContextCall t {} = .ok c → c.status = []

/-- `DefaultContext.divide(Decimal(1), Decimal(3))` then `Context()`: `context_new` copies
the template's status word and `flags=None` leaves it. -/
theorem contextNewClearsFlagsC_refuted : ¬ContextNewClearsFlagsC := by
  intro h
  have := h dirtyTemplate { dirtyTemplate with capitals := 1 } rfl
  simp [dirtyTemplate] at this

/-- "If a field is not specified or is None, the default values are copied from the
DefaultContext." (Doc/library/decimal.rst:1109-1110), for `capitals` in `_decimal`. -/
def ContextNewCopiesCapitalsC : Prop :=
  ∀ (t c : CContext), cContextCall t {} = .ok c → c.capitals = t.capitals

theorem contextNewCopiesCapitalsC_refuted : ¬ContextNewCopiesCapitalsC := by
  intro h
  have := h { dfltCtx with capitals := 0 } { dfltCtx with capitals := 1 } rfl
  simp at this

/-- A `PyContext` and a `CContext` hold the same values. -/
def Corresponds (p : PyContext) (c : CContext) : Prop :=
  p.prec = c.prec ∧ p.rounding = c.round ∧ p.emin = c.emin ∧ p.emax = c.emax ∧
  p.capitals = c.capitals ∧ p.clamp = c.clamp ∧
  (∀ s, (p.flags.lookup s).getD false = hasSignal c.status s) ∧
  (∀ s, (p.traps.lookup s).getD false = hasSignal c.traps s)

theorem sigEntries_keyed (d : SigDict) : sigEntries (keyed d) = d := by
  induction d with
  | nil => rfl
  | cons x xs ih => simpa [sigEntries, keyed] using ih

theorem pySignals_mem (s : Signal) : s ∈ pySignals := by cases s <;> decide

theorem hasOther_keyed (d : SigDict) : hasOther (keyed d) = false := by
  induction d with
  | nil => rfl
  | cons x xs ih => simpa [hasOther, keyed, SigKey.isSig] using ih

theorem hasKey_keyed_sig (d : SigDict) (s : Signal) (h : (d.lookup s).isSome) :
    hasKey (keyed d) (.sig s) = true := by
  induction d with
  | nil => simp at h
  | cons x xs ih =>
    obtain ⟨k, v⟩ := x
    by_cases hx : s = k
    · subst hx; simp [hasKey, keyed]
    · have hne : (s == k) = false := by simpa using hx
      simp only [List.lookup, hne] at h
      have := ih h
      simp only [hasKey, keyed] at this
      simp [hasKey, keyed, this]

/-- A signal is found in `_signals`: by identity, at its own position. -/
theorem ansIn_sig (s : Signal) : ansIn (pySignals.map (SigKey.sig s).eqSig) = .ok true := by
  cases s <;> rfl

/-- `checkKeys` passes a dict whose keys all compare equal to some signal before any comparison
raises. -/
theorem checkKeys_ok (fmt : PyExc) : ∀ d : List (SigKey × SigVal),
    (∀ p ∈ d, ansIn (pySignals.map p.1.eqSig) = .ok true) → checkKeys fmt d = .ok ()
  | [], _ => rfl
  | (k, v) :: rest, h => by
    have hk := h (k, v) (by simp)
    simp only [checkKeys, hk, bind, Except.bind, Bool.not_true]
    exact checkKeys_ok fmt rest (fun p hp => h p (by simp [hp]))

theorem extrasOf_keyed (d : SigDict) : extrasOf (keyed d) = [] := by
  induction d with
  | nil => rfl
  | cons x xs ih => simpa [extrasOf, keyed, SigKey.isSig] using ih

theorem sigEntries_append (a b : List (SigKey × SigVal)) :
    sigEntries (a ++ b) = sigEntries a ++ sigEntries b := by
  simp [sigEntries, List.filterMap_append]

theorem extrasOf_append (a b : List (SigKey × SigVal)) :
    extrasOf (a ++ b) = extrasOf a ++ extrasOf b := by
  simp [extrasOf, List.filter_append]

theorem sigEntries_nonsig : ∀ x : List (SigKey × SigVal), (∀ p ∈ x, p.1.isSig = false) → sigEntries x = []
  | [], _ => rfl
  | (k, v) :: rest, h => by
    have hk := h (k, v) (by simp)
    cases k with
    | sig s => simp [SigKey.isSig] at hk
    | other r hh eq hv pv =>
      simp only [sigEntries, List.filterMap_cons]
      exact sigEntries_nonsig rest (fun p hp => h p (by simp [hp]))

theorem extrasOf_nonsig : ∀ x : List (SigKey × SigVal), (∀ p ∈ x, p.1.isSig = false) → extrasOf x = x
  | [], _ => rfl
  | (k, v) :: rest, h => by
    have hk := h (k, v) (by simp)
    simp only [extrasOf, List.filter_cons, hk, Bool.not_false, if_true]
    exact congrArg _ (extrasOf_nonsig rest (fun p hp => h p (by simp [hp])))

/-- Extra keys a dict was stored with. -/
def ExtrasOk (x : List (SigKey × SigVal)) : Prop :=
  ∀ p ∈ x, p.1.isSig = false ∧ ansIn (pySignals.map p.1.eqSig) = .ok true

theorem hasKey_append_left (a b : List (SigKey × SigVal)) (k : SigKey) (h : hasKey a k = true) :
    hasKey (a ++ b) k = true := by
  simp only [hasKey, List.any_append, Bool.or_eq_true] at h ⊢
  exact Or.inl h

/-- A dict with an entry for every signal, plus extra keys `__eq__` lets through, is what
`_set_signal_dict` keeps. -/
theorem setSignalDict_keyed_extra (d : SigDict) (x : List (SigKey × SigVal))
    (h : ∀ s, (d.lookup s).isSome) (hx : ExtrasOk x) :
    setSignalDict (.dict (keyed d ++ x)) = .ok (d, x) := by
  have h1 : pySignals.all (fun s => hasKey (keyed d ++ x) (.sig s)) = true := by
    rw [List.all_eq_true]
    intro s _
    exact hasKey_append_left _ _ _ (hasKey_keyed_sig d s (h s))
  have hc : checkKeys (CtxArg.pct (.dict (keyed d ++ x)) (.keyError "~is not a valid signal dict"))
      (keyed d ++ x) = .ok () := by
    apply checkKeys_ok
    intro p hp
    simp only [List.mem_append] at hp
    rcases hp with hp | hp
    · simp only [keyed, List.mem_map] at hp
      obtain ⟨q, _, rfl⟩ := hp
      exact ansIn_sig q.1
    · exact (hx p hp).2
  simp only [setSignalDict, hc, h1, bind, Except.bind, Bool.not_true, pure, Except.pure]
  rw [sigEntries_append, extrasOf_append, sigEntries_keyed, extrasOf_keyed,
    sigEntries_nonsig x (fun p hp => (hx p hp).1), extrasOf_nonsig x (fun p hp => (hx p hp).1)]
  simp

/-- A dict with an entry for every signal is what `_set_signal_dict` keeps. -/
theorem setSignalDict_keyed (d : SigDict) (h : ∀ s, (d.lookup s).isSome) :
    setSignalDict (.dict (keyed d)) = .ok (d, []) := by
  have := setSignalDict_keyed_extra d [] h (fun p hp => by simp at hp)
  simpa using this

theorem pySetattr_flags (c : PyContext) (v : CtxArg) :
    pySetattr c "flags" v =
      (do let d ← setSignalDict v; pure { c with flags := d.1, flagsExtra := d.2 }) := by
  simp [pySetattr]

theorem pySetattr_traps (c : PyContext) (v : CtxArg) :
    pySetattr c "traps" v =
      (do let d ← setSignalDict v; pure { c with traps := d.1, trapsExtra := d.2 }) := by
  simp [pySetattr]

/-- All-false dict for every signal. -/
def clearDict0 : SigDict := pySignals.map (fun s => (s, false))

theorem clearDict0_total (s : Signal) : (clearDict0.lookup s).isSome := by cases s <;> rfl

theorem clearDict0_false (s : Signal) : (clearDict0.lookup s).getD false = false := by
  cases s <;> rfl

/-- `_pydecimal`'s `Context()` keeps the promise: all flags clear, for every
`DefaultContext`. -/
def ContextNewClearsFlagsPy : Prop :=
  ∀ (dc c : PyContext), pyContextNew dc {} = .ok c → ∀ s, (c.flags.lookup s).getD false = false

theorem contextNewClearsFlagsPy_proven : ContextNewClearsFlagsPy := by
  intro dc c h s
  simp only [pyContextNew, orElseArg] at h
  obtain ⟨c1, _, h⟩ := ebind_ok h
  obtain ⟨c2, _, h⟩ := ebind_ok h
  obtain ⟨c3, _, h⟩ := ebind_ok h
  obtain ⟨c4, _, h⟩ := ebind_ok h
  obtain ⟨c5, _, h⟩ := ebind_ok h
  obtain ⟨c6, _, h⟩ := ebind_ok h
  obtain ⟨c6', _, h⟩ := ebind_ok h
  obtain ⟨t, _, h⟩ := ebind_ok h
  obtain ⟨c7, _, h⟩ := ebind_ok h
  obtain ⟨f, hf, h⟩ := ebind_ok h
  simp only [signalArg] at hf
  cases hf
  rw [pySetattr_flags] at h
  have hk := setSignalDict_keyed clearDict0 clearDict0_total
  have hk' : setSignalDict (.dict (keyed (pySignals.map (fun s => (s, false))))) = .ok (clearDict0, []) := hk
  simp only [hk', bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact clearDict0_false s

/-- For a template whose flags are clear and whose `capitals` is 1, which is the state
`DefaultContext` starts in, `Context()` copies every field in `_decimal` and agrees with
`_pydecimal` built from the same `DefaultContext`. The excluded templates are
decimal-c-context-inherits-flags and decimal-c-context-ignores-default-capitals. -/
def ContextNewCleanTemplate : Prop :=
  ∀ (t c : CContext), t.status = [] → t.capitals = 1 → cContextCall t {} = .ok c →
    c = t

theorem contextNewCleanTemplate_proven : ContextNewCleanTemplate := by
  intro t c hs hc h
  have h' : cContextCall t {} = .ok { t with capitals := 1 } := rfl
  rw [h'] at h
  cases h
  cases t
  simp_all

/-! ## `_pydecimal`'s integer attributes, case by case -/

/-- The exception `raise ValueError("..." % (..., value))` raises for an int `value`: the message,
or the int/str-limit `ValueError` when `str(value)` has more than 4300 digits. -/
def limitOr (n : Int) (e : PyExc) : PyExc :=
  if maxStrDigits < numDigits n.natAbs then .valueError limitToStrMsg else e

theorem limitOr_valueError (n : Int) (m : String) : ∃ m', limitOr n (.valueError m) = .valueError m' := by
  unfold limitOr; split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem sic_hi (name : String) (n hi : Int) :
    setIntegerCheck name (.int n) none (some hi) =
      (if n > hi then .error (limitOr n (.valueError s!"{name} must be in [-inf, {hi}]. got: {n}"))
       else .ok n) := by
  by_cases h : n > hi <;> by_cases hl : maxStrDigits < numDigits n.natAbs <;>
    simp [setIntegerCheck, intValue, intText, strLimit, limitOr, h, hl, bind, Except.bind, pure,
      Except.pure]
  all_goals rfl

theorem sic_lo (name : String) (n lo : Int) :
    setIntegerCheck name (.int n) (some lo) none =
      (if n < lo then .error (limitOr n (.valueError s!"{name} must be in [{lo}, inf]. got: {n}"))
       else .ok n) := by
  by_cases h : n < lo <;> by_cases hl : maxStrDigits < numDigits n.natAbs <;>
    simp [setIntegerCheck, intValue, intText, strLimit, limitOr, h, hl, bind, Except.bind, pure,
      Except.pure]
  all_goals rfl

theorem sic_lohi (name : String) (n lo hi : Int) :
    setIntegerCheck name (.int n) (some lo) (some hi) =
      (if n < lo ∨ n > hi then .error (limitOr n (.valueError s!"{name} must be in [{lo}, {hi}]. got {n}"))
       else .ok n) := by
  by_cases h : n < lo ∨ n > hi <;> by_cases hl : maxStrDigits < numDigits n.natAbs <;>
    simp only [setIntegerCheck, intValue, intText, strLimit, limitOr, h, hl, ite_true, ite_false,
      gt_iff_lt, bind, Except.bind, pure, Except.pure] <;> rfl

theorem pySetattr_prec (c : PyContext) (n : Int) :
    pySetattr c "prec" (.int n) =
      (if n < 1 then .error (limitOr n (.valueError s!"prec must be in [1, inf]. got: {n}"))
       else .ok { c with prec := n }) := by
  have := sic_lo "prec" n 1
  by_cases h : n < 1 <;> simp_all [pySetattr, bind, Except.bind, pure, Except.pure]
  all_goals rfl

theorem pySetattr_emin (c : PyContext) (n : Int) :
    pySetattr c "Emin" (.int n) =
      (if n > 0 then .error (limitOr n (.valueError s!"Emin must be in [-inf, 0]. got: {n}"))
       else .ok { c with emin := n }) := by
  have := sic_hi "Emin" n 0
  by_cases h : n > 0 <;> simp_all [pySetattr, bind, Except.bind, pure, Except.pure]
  all_goals rfl

theorem pySetattr_emax (c : PyContext) (n : Int) :
    pySetattr c "Emax" (.int n) =
      (if n < 0 then .error (limitOr n (.valueError s!"Emax must be in [0, inf]. got: {n}"))
       else .ok { c with emax := n }) := by
  have := sic_lo "Emax" n 0
  by_cases h : n < 0 <;> simp_all [pySetattr, bind, Except.bind, pure, Except.pure]
  all_goals rfl

theorem pySetattr_capitals (c : PyContext) (n : Int) :
    pySetattr c "capitals" (.int n) =
      (if n < 0 ∨ n > 1 then .error (limitOr n (.valueError s!"capitals must be in [0, 1]. got {n}"))
       else .ok { c with capitals := n }) := by
  have := sic_lohi "capitals" n 0 1
  by_cases h : n < 0 ∨ n > 1
  · rw [if_pos h] at this ⊢
    simp [pySetattr, this, bind, Except.bind]
    all_goals rfl
  · rw [if_neg h] at this ⊢
    simp [pySetattr, this, bind, Except.bind, pure, Except.pure]

theorem pySetattr_clamp (c : PyContext) (n : Int) :
    pySetattr c "clamp" (.int n) =
      (if n < 0 ∨ n > 1 then .error (limitOr n (.valueError s!"clamp must be in [0, 1]. got {n}"))
       else .ok { c with clamp := n }) := by
  have := sic_lohi "clamp" n 0 1
  by_cases h : n < 0 ∨ n > 1
  · rw [if_pos h] at this ⊢
    simp [pySetattr, this, bind, Except.bind]
    all_goals rfl
  · rw [if_neg h] at this ⊢
    simp [pySetattr, this, bind, Except.bind, pure, Except.pure]

/-! ## Attributes: the two twins agree inside the documented ranges -/

/-- An integer attribute set in range is stored by both twins, and one below the range
is refused by both with `ValueError` (`_decimal`: `OverflowError` past `ssize_t`). `prec`
above `MAX_PREC` and `Emin`, `Emax` past their limits are outside the documented ranges,
which `_pydecimal` does not enforce (Doc/library/decimal.rst, `Context.prec`, `Emin`, `Emax`). -/
def ContextAttrTwins : Prop :=
  ∀ (p : PyContext) (c : CContext) (n : Int),
    (1 ≤ n → n ≤ mpdMaxPrec →
      pySetattr p "prec" (.int n) = .ok { p with prec := n } ∧
      cSetattr c "prec" (.int n) = .ok { c with prec := n }) ∧
    (n ≤ 0 → mpdSsizeMin ≤ n →
      (∃ m, pySetattr p "prec" (.int n) = .error (.valueError m)) ∧
      (∃ m, cSetattr c "prec" (.int n) = .error (.valueError m))) ∧
    (mpdMinEmin ≤ n → n ≤ 0 →
      pySetattr p "Emin" (.int n) = .ok { p with emin := n } ∧
      cSetattr c "Emin" (.int n) = .ok { c with emin := n }) ∧
    (0 < n → n ≤ mpdSsizeMax →
      (∃ m, pySetattr p "Emin" (.int n) = .error (.valueError m)) ∧
      (∃ m, cSetattr c "Emin" (.int n) = .error (.valueError m))) ∧
    (0 ≤ n → n ≤ mpdMaxEmax →
      pySetattr p "Emax" (.int n) = .ok { p with emax := n } ∧
      cSetattr c "Emax" (.int n) = .ok { c with emax := n }) ∧
    (n < 0 → mpdSsizeMin ≤ n →
      (∃ m, pySetattr p "Emax" (.int n) = .error (.valueError m)) ∧
      (∃ m, cSetattr c "Emax" (.int n) = .error (.valueError m))) ∧
    (n = 0 ∨ n = 1 →
      pySetattr p "capitals" (.int n) = .ok { p with capitals := n } ∧
      cSetattr c "capitals" (.int n) = .ok { c with capitals := n } ∧
      pySetattr p "clamp" (.int n) = .ok { p with clamp := n } ∧
      cSetattr c "clamp" (.int n) = .ok { c with clamp := n }) ∧
    (n ≠ 0 → n ≠ 1 → mpdSsizeMin ≤ n → n ≤ mpdSsizeMax →
      (∃ m, pySetattr p "capitals" (.int n) = .error (.valueError m)) ∧
      (∃ m, cSetattr c "capitals" (.int n) = .error (.valueError m)) ∧
      (∃ m, pySetattr p "clamp" (.int n) = .error (.valueError m)) ∧
      (∃ m, cSetattr c "clamp" (.int n) = .error (.valueError m)))

theorem longAsSsize_ok (n : Int) (h1 : mpdSsizeMin ≤ n) (h2 : n ≤ mpdSsizeMax) :
    longAsSsize (.int n) = .ok n := by
  simp only [longAsSsize]
  exact if_neg (by simp only [mpdSsizeMin, mpdSsizeMax] at *; omega)

theorem setprec_ok (c : CContext) (n : Int) (h1 : 1 ≤ n) (h2 : n ≤ mpdMaxPrec) :
    contextSetprec c (.int n) = .ok { c with prec := n } := by
  have hs := longAsSsize_ok n (by simp only [mpdSsizeMin]; omega)
    (by simp only [mpdSsizeMax]; simp only [mpdMaxPrec] at h2; omega)
  have g : ¬(n ≤ 0 ∨ n > mpdMaxPrec) := by omega
  simp only [contextSetprec, hs, bind, Except.bind, if_neg g]
  rfl

theorem setprec_err (c : CContext) (n : Int) (h1 : n ≤ 0) (h2 : mpdSsizeMin ≤ n) :
    ∃ m, contextSetprec c (.int n) = .error (.valueError m) := by
  have hs := longAsSsize_ok n h2 (by simp only [mpdSsizeMax]; omega)
  have g : n ≤ 0 ∨ n > mpdMaxPrec := Or.inl h1
  refine ⟨"valid range for prec is [1, MAX_PREC]", ?_⟩
  simp only [contextSetprec, hs, bind, Except.bind, if_pos g]
  rfl

theorem setemin_ok (c : CContext) (n : Int) (h1 : mpdMinEmin ≤ n) (h2 : n ≤ 0) :
    contextSetemin c (.int n) = .ok { c with emin := n } := by
  have hs := longAsSsize_ok n (by simp only [mpdSsizeMin]; simp only [mpdMinEmin] at h1; omega)
    (by simp only [mpdSsizeMax]; omega)
  have g : ¬(n > 0 ∨ n < mpdMinEmin) := by omega
  simp only [contextSetemin, hs, bind, Except.bind, if_neg g]
  rfl

theorem setemin_err (c : CContext) (n : Int) (h1 : 0 < n) (h2 : n ≤ mpdSsizeMax) :
    ∃ m, contextSetemin c (.int n) = .error (.valueError m) := by
  have hs := longAsSsize_ok n (by simp only [mpdSsizeMin]; omega) h2
  have g : n > 0 ∨ n < mpdMinEmin := Or.inl h1
  refine ⟨"valid range for Emin is [MIN_EMIN, 0]", ?_⟩
  simp only [contextSetemin, hs, bind, Except.bind, if_pos g]
  rfl

theorem setemax_ok (c : CContext) (n : Int) (h1 : 0 ≤ n) (h2 : n ≤ mpdMaxEmax) :
    contextSetemax c (.int n) = .ok { c with emax := n } := by
  have hs := longAsSsize_ok n (by simp only [mpdSsizeMin]; omega)
    (by simp only [mpdSsizeMax]; simp only [mpdMaxEmax] at h2; omega)
  have g : ¬(n < 0 ∨ n > mpdMaxEmax) := by omega
  simp only [contextSetemax, hs, bind, Except.bind, if_neg g]
  rfl

theorem setemax_err (c : CContext) (n : Int) (h1 : n < 0) (h2 : mpdSsizeMin ≤ n) :
    ∃ m, contextSetemax c (.int n) = .error (.valueError m) := by
  have hs := longAsSsize_ok n h2 (by simp only [mpdSsizeMax]; omega)
  have g : n < 0 ∨ n > mpdMaxEmax := Or.inl h1
  refine ⟨"valid range for Emax is [0, MAX_EMAX]", ?_⟩
  simp only [contextSetemax, hs, bind, Except.bind, if_pos g]
  rfl

theorem setcapitals_ok (c : CContext) (n : Int) (h : n = 0 ∨ n = 1) :
    contextSetcapitals c (.int n) = .ok { c with capitals := n } := by
  have hs := longAsSsize_ok n (by simp only [mpdSsizeMin]; omega) (by simp only [mpdSsizeMax]; omega)
  have g : ¬(n ≠ 0 ∧ n ≠ 1) := by omega
  simp only [contextSetcapitals, hs, bind, Except.bind, if_neg g]
  rfl

theorem setcapitals_err (c : CContext) (n : Int) (h1 : n ≠ 0) (h2 : n ≠ 1)
    (h3 : mpdSsizeMin ≤ n) (h4 : n ≤ mpdSsizeMax) :
    ∃ m, contextSetcapitals c (.int n) = .error (.valueError m) := by
  have g : n ≠ 0 ∧ n ≠ 1 := ⟨h1, h2⟩
  refine ⟨"valid values for capitals are 0 or 1", ?_⟩
  simp only [contextSetcapitals, longAsSsize_ok n h3 h4, bind, Except.bind, if_pos g]
  rfl

theorem setclamp_ok (c : CContext) (n : Int) (h : n = 0 ∨ n = 1) :
    contextSetclamp c (.int n) = .ok { c with clamp := n } := by
  have hs := longAsSsize_ok n (by simp only [mpdSsizeMin]; omega) (by simp only [mpdSsizeMax]; omega)
  have hb : ¬(n < -(2 ^ 31) ∨ 2 ^ 31 - 1 < n) := by omega
  have g : ¬(n ≠ 0 ∧ n ≠ 1) := by omega
  simp only [contextSetclamp, hs, bind, Except.bind, if_neg hb, if_neg g]
  rfl

theorem setclamp_err (c : CContext) (n : Int) (h1 : n ≠ 0) (h2 : n ≠ 1)
    (h3 : mpdSsizeMin ≤ n) (h4 : n ≤ mpdSsizeMax) :
    ∃ m, contextSetclamp c (.int n) = .error (.valueError m) := by
  refine ⟨"valid values for clamp are 0 or 1", ?_⟩
  by_cases hb : n < -(2 ^ 31) ∨ 2 ^ 31 - 1 < n
  · have g : ((2 : Int) ^ 31 - 1 ≠ 0 ∧ (2 : Int) ^ 31 - 1 ≠ 1) := by omega
    simp only [contextSetclamp, longAsSsize_ok n h3 h4, bind, Except.bind, if_pos hb, if_pos g]
    rfl
  · have g : n ≠ 0 ∧ n ≠ 1 := ⟨h1, h2⟩
    simp only [contextSetclamp, longAsSsize_ok n h3 h4, bind, Except.bind, if_neg hb, if_pos g]
    rfl

theorem contextAttrTwins_proven : ContextAttrTwins := by
  intro p c n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h1 h2
    have g : ¬n < 1 := by omega
    exact ⟨by rw [pySetattr_prec, if_neg g], by simpa [cSetattr] using setprec_ok c n h1 h2⟩
  · intro h1 h2
    have g : n < 1 := by omega
    obtain ⟨m, hm⟩ := limitOr_valueError n s!"prec must be in [1, inf]. got: {n}"
    exact ⟨⟨m, by rw [pySetattr_prec, if_pos g, hm]⟩, by simpa [cSetattr] using setprec_err c n h1 h2⟩
  · intro h1 h2
    have g : ¬n > 0 := by omega
    exact ⟨by rw [pySetattr_emin, if_neg g], by simpa [cSetattr] using setemin_ok c n h1 h2⟩
  · intro h1 h2
    obtain ⟨m, hm⟩ := limitOr_valueError n s!"Emin must be in [-inf, 0]. got: {n}"
    exact ⟨⟨m, by rw [pySetattr_emin, if_pos h1, hm]⟩, by simpa [cSetattr] using setemin_err c n h1 h2⟩
  · intro h1 h2
    have g : ¬n < 0 := by omega
    exact ⟨by rw [pySetattr_emax, if_neg g], by simpa [cSetattr] using setemax_ok c n h1 h2⟩
  · intro h1 h2
    obtain ⟨m, hm⟩ := limitOr_valueError n s!"Emax must be in [0, inf]. got: {n}"
    exact ⟨⟨m, by rw [pySetattr_emax, if_pos h1, hm]⟩, by simpa [cSetattr] using setemax_err c n h1 h2⟩
  · intro h
    have g : ¬(n < 0 ∨ n > 1) := by omega
    exact ⟨by rw [pySetattr_capitals, if_neg g], by simpa [cSetattr] using setcapitals_ok c n h,
      by rw [pySetattr_clamp, if_neg g], by simpa [cSetattr] using setclamp_ok c n h⟩
  · intro h1 h2 h3 h4
    have g : n < 0 ∨ n > 1 := by omega
    obtain ⟨m1, hm1⟩ := limitOr_valueError n s!"capitals must be in [0, 1]. got {n}"
    obtain ⟨m2, hm2⟩ := limitOr_valueError n s!"clamp must be in [0, 1]. got {n}"
    exact ⟨⟨m1, by rw [pySetattr_capitals, if_pos g, hm1]⟩,
      by simpa [cSetattr] using setcapitals_err c n h1 h2 h3 h4,
      ⟨m2, by rw [pySetattr_clamp, if_pos g, hm2]⟩,
      by simpa [cSetattr] using setclamp_err c n h1 h2 h3 h4⟩

/-! ## `SignalDict` -/

theorem bit_mem (x : Bit) : x ∈ allBits := by cases x <;> decide

theorem mem_or (a b : Status) (x : Bit) : x ∈ orBits a b ↔ x ∈ a ∨ x ∈ b := by
  simp [orBits, bit_mem]

theorem mem_clear (a b : Status) (x : Bit) : x ∈ clearBits a b ↔ x ∈ a ∧ x ∉ b := by
  simp [clearBits, bit_mem]

/-- Two status words with the same signals compare equal as mappings: a `SignalDict`
is a `MutableMapping` (_decimal.c:7796-7797), whose `__eq__` compares items
(Lib/_collections_abc.py:822), and `ctx.flags.copy()` is that same mapping. -/
def SignalDictEqualityByItems : Prop :=
  ∀ (a b : Status), (∀ s, hasSignal a s = hasSignal b s) →
    signaldictRichcompare (some a) (.sd (some b)) false = .ok (some true)

/-- `ctx.divide(0, 0)` sets `MPD_Division_undefined` and `create_decimal('xyz')` sets
`MPD_Conversion_syntax`: both show `flags[InvalidOperation]` true, but
`signaldict_richcompare` compares the raw words. -/
theorem signalDictEqualityByItems_refuted : ¬SignalDictEqualityByItems := by
  intro h
  have := h [.divisionUndefined] [.conversionSyntax] (by intro s; cases s <;> decide)
  revert this
  decide

/-- `ctx.flags == ctx.flags.copy()`, for every status word. -/
def SignalDictEqualsCopy : Prop :=
  ∀ a : Status, signaldictRichcompare (some a) (.dict (keyed (flagsAsDict a))) false = .ok (some true)

/-- After `ctx.divide(0, 0)`: `dict_as_flags` turns `InvalidOperation: True` into all
seven bits of `MPD_IEEE_Invalid_operation`, and the status word has one. -/
theorem signalDictEqualsCopy_refuted : ¬SignalDictEqualsCopy := by
  intro h
  have := h [.divisionUndefined]
  revert this
  decide

/-- The case the source handles: words in which the bits of InvalidOperation are all set
or all clear, as `ctx.flags[InvalidOperation] = v`, `Context(flags=[...])` and
`dict_as_flags` leave them. Then equality is by items. The excluded words, with some of
those bits set, are what an operation leaves. -/
def SignalDictEqualityCanonical : Prop :=
  ∀ (a b : Status),
    (∀ x y, x ∈ ieeeInvalid → y ∈ ieeeInvalid → a.contains x = a.contains y) →
    (∀ x y, x ∈ ieeeInvalid → y ∈ ieeeInvalid → b.contains x = b.contains y) →
    (∀ s, hasSignal a s = hasSignal b s) →
    signaldictRichcompare (some a) (.sd (some b)) false = .ok (some true)

theorem contains_of_hasSignal (a b : Status)
    (ha : ∀ x y, x ∈ ieeeInvalid → y ∈ ieeeInvalid → a.contains x = a.contains y)
    (hb : ∀ x y, x ∈ ieeeInvalid → y ∈ ieeeInvalid → b.contains x = b.contains y)
    (h : ∀ s, hasSignal a s = hasSignal b s) (x : Bit) : a.contains x = b.contains x := by
  have key : ∀ (st : Status) (hs : ∀ x y, x ∈ ieeeInvalid → y ∈ ieeeInvalid → st.contains x = st.contains y)
      (x : Bit), x ∈ ieeeInvalid → hasSignal st .invalidOperation = st.contains x := by
    intro st hs x hx
    have hc : hasSignal st .invalidOperation = ieeeInvalid.any st.contains := rfl
    rw [hc]
    cases hv : st.contains x with
    | true =>
      rw [List.any_eq_true]
      exact ⟨x, hx, hv⟩
    | false =>
      rw [← Bool.not_eq_true, List.any_eq_true]
      rintro ⟨y, hy, hy2⟩
      rw [hs y x hy hx, hv] at hy2
      cases hy2
  by_cases hx : x ∈ ieeeInvalid
  · rw [← key a ha x hx, ← key b hb x hx]
    exact h _
  · have one : ∀ s : Signal, s.flagBits = [x] → a.contains x = b.contains x := by
      intro s hs
      have := h s
      simpa [hasSignal, hs] using this
    cases x with
    | clamped => exact one .clamped rfl
    | divisionByZero => exact one .divisionByZero rfl
    | inexact => exact one .inexact rfl
    | notImplemented => exact one .floatOperation rfl
    | overflow => exact one .overflow rfl
    | rounded => exact one .rounded rfl
    | subnormal => exact one .subnormal rfl
    | underflow => exact one .underflow rfl
    | _ => exact absurd (by decide) hx

theorem signalDictEqualityCanonical_proven : SignalDictEqualityCanonical := by
  intro a b ha hb h
  have hc := contains_of_hasSignal a b ha hb h
  have heq : andBits a allBits = andBits b allBits := by
    simp only [andBits]
    apply List.filter_congr
    intro x _
    rw [hc x]
  simp [signaldictRichcompare, heq]

/-- `ctx.flags[s] = v` then `ctx.flags[s]` gives `v`, whichever bits were set, and no other
signal changes: signals own disjoint sets of bits. Deleting a key raises. -/
def SignalDictSetGet : Prop :=
  ∀ (st st' : Status) (s t : Signal) (b : Bool),
    signaldictSetitem (some st) (.sig s) (some b) = .ok st' →
    signaldictGetitem (some st') (.sig s) = .ok b ∧
    (t ≠ s → signaldictGetitem (some st') (.sig t) = signaldictGetitem (some st) (.sig t))

theorem flagBits_disjoint (s t : Signal) (h : t ≠ s) (x : Bit) (hx : x ∈ t.flagBits) :
    s.flagBits.contains x = false := by
  cases s <;> cases t <;> first
    | exact absurd rfl h
    | (cases x <;> first | rfl | (exact absurd hx (by decide)))

theorem any_congr' {l : List Bit} {f g : Bit → Bool} (h : ∀ x ∈ l, f x = g x) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.any_cons]
    rw [h y (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem flagBits_nonempty (s : Signal) : ∃ x, x ∈ s.flagBits := by
  cases s
  all_goals first
    | exact ⟨.invalidOperation, by decide⟩ | exact ⟨.notImplemented, by decide⟩
    | exact ⟨.divisionByZero, by decide⟩ | exact ⟨.overflow, by decide⟩
    | exact ⟨.underflow, by decide⟩ | exact ⟨.subnormal, by decide⟩
    | exact ⟨.inexact, by decide⟩ | exact ⟨.rounded, by decide⟩ | exact ⟨.clamped, by decide⟩

theorem signalDictSetGet_proven : SignalDictSetGet := by
  intro st st' s t b h
  simp only [signaldictSetitem, exceptionAsFlag, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
  subst h
  constructor
  · simp only [signaldictGetitem, exceptionAsFlag, bind, Except.bind, pure, Except.pure, Except.ok.injEq]
    cases b with
    | true =>
      obtain ⟨x, hx⟩ := flagBits_nonempty s
      simp only [↓reduceIte]
      rw [List.any_eq_true]
      exact ⟨x, hx, by simp [mem_or, hx]⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← Bool.not_eq_true, List.any_eq_true]
      rintro ⟨x, hx, h2⟩
      have h3 : x ∈ clearBits st s.flagBits := by simpa using h2
      exact ((mem_clear _ _ _).mp h3).2 hx
  · intro hts
    simp only [signaldictGetitem, exceptionAsFlag, bind, Except.bind, pure, Except.pure, Except.ok.injEq]
    apply any_congr'
    intro x hx
    have hd : x ∉ s.flagBits := by simpa using flagBits_disjoint s t hts x hx
    cases b with
    | true => simp [mem_or, hd]
    | false => simp [mem_clear, hd]

end PyLean.Decimal
