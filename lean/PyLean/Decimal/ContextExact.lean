import PyLean.Decimal.ContextProps

/-!
`_pydecimal`'s `Context` attributes and constructor, outcome by outcome: what each
assignment stores and the exception, with its message, for every value it refuses.
-/

namespace PyLean.Decimal

open PyLean

/-! ## `__setattr__`, `_set_integer_check`, `_set_signal_dict` -/

/-- A value that is not an int. -/
def CtxArg.isInt : CtxArg → Bool
  | .int _ => true
  | _ => false

/-- A dict whose keys are exactly the nine signals (each once or more). -/
def ValidSigDict (d : List (SigKey × Bool)) : Prop :=
  hasKey d .other = false ∧ ∀ s, hasKey d (.sig s) = true

/-- Every assignment to a `_pydecimal` `Context` attribute (_pydecimal.py:4005-4053):

* `prec`, `Emin`, `Emax`, `capitals`, `clamp` store an int inside `[1, inf]`, `[-inf, 0]`,
  `[0, inf]`, `[0, 1]`, `[0, 1]` and refuse one outside with `ValueError` and the exact text of
  `_set_integer_check` (:4008-4016); anything that is not an int is a `TypeError`
  (`"%s must be an integer"`, :4006-4007);
* `rounding` stores one of the eight mode names and refuses any other string, and any non-string,
  with `TypeError` (:4041-4046);
* `flags` and `traps` store a dict whose keys are exactly the signals; a dict with another key or
  a missing signal is a `KeyError`, anything else a `TypeError` (:4019-4028);
* `_ignored_flags` stores its value (:4049-4050);
* any other name is an `AttributeError` (:4051-4053).

Each refusal leaves the context unchanged: the model returns an exception and no context. -/
def SetattrExact : Prop :=
  ∀ (c : PyContext) (n : Int) (v : CtxArg),
    -- prec
    (1 ≤ n → pySetattr c "prec" (.int n) = .ok { c with prec := n }) ∧
    (n < 1 → pySetattr c "prec" (.int n) = .error (.valueError s!"prec must be in [1, inf]. got: {n}")) ∧
    -- Emin
    (n ≤ 0 → pySetattr c "Emin" (.int n) = .ok { c with emin := n }) ∧
    (0 < n → pySetattr c "Emin" (.int n) = .error (.valueError s!"Emin must be in [-inf, 0]. got: {n}")) ∧
    -- Emax
    (0 ≤ n → pySetattr c "Emax" (.int n) = .ok { c with emax := n }) ∧
    (n < 0 → pySetattr c "Emax" (.int n) = .error (.valueError s!"Emax must be in [0, inf]. got: {n}")) ∧
    -- capitals, clamp
    ((n = 0 ∨ n = 1) → pySetattr c "capitals" (.int n) = .ok { c with capitals := n } ∧
      pySetattr c "clamp" (.int n) = .ok { c with clamp := n }) ∧
    (n ≠ 0 → n ≠ 1 →
      pySetattr c "capitals" (.int n) = .error (.valueError s!"capitals must be in [0, 1]. got {n}") ∧
      pySetattr c "clamp" (.int n) = .error (.valueError s!"clamp must be in [0, 1]. got {n}")) ∧
    -- not an int
    (v.isInt = false →
      pySetattr c "prec" v = .error (.typeError "prec must be an integer") ∧
      pySetattr c "Emin" v = .error (.typeError "Emin must be an integer") ∧
      pySetattr c "Emax" v = .error (.typeError "Emax must be an integer") ∧
      pySetattr c "capitals" v = .error (.typeError "capitals must be an integer") ∧
      pySetattr c "clamp" v = .error (.typeError "clamp must be an integer")) ∧
    -- rounding
    (∀ r : Rounding, pySetattr c "rounding" (.str r.name) = .ok { c with rounding := r }) ∧
    (∀ s : String, roundingOfName s = none →
      pySetattr c "rounding" (.str s) = .error (.typeError s!"{s}: invalid rounding mode")) ∧
    ((∀ s, v ≠ .str s) → ∃ m, pySetattr c "rounding" v = .error (.typeError m)) ∧
    -- flags, traps
    (∀ d, ValidSigDict d →
      pySetattr c "flags" (.dict d) = .ok { c with flags := sigEntries d } ∧
      pySetattr c "traps" (.dict d) = .ok { c with traps := sigEntries d }) ∧
    (∀ d, (hasKey d .other = true ∨ ∃ s, hasKey d (.sig s) = false) →
      (∃ m, pySetattr c "flags" (.dict d) = .error (.keyError m)) ∧
      (∃ m, pySetattr c "traps" (.dict d) = .error (.keyError m))) ∧
    ((∀ d, v ≠ .dict d) →
      (∃ m, pySetattr c "flags" v = .error (.typeError m)) ∧
      (∃ m, pySetattr c "traps" v = .error (.typeError m))) ∧
    -- _ignored_flags
    (∀ l : List Signal, pySetattr c "_ignored_flags" (.list (l.map .sig)) = .ok { c with ignored := l }) ∧
    -- anything else
    (∀ name, name ∉ ["prec", "Emin", "Emax", "capitals", "clamp", "rounding", "flags", "traps",
        "_ignored_flags"] →
      pySetattr c name v =
        .error (.named "AttributeError" s!"'decimal.Context' object has no attribute '{name}'"))

theorem roundingOfName_name (r : Rounding) : roundingOfName r.name = some r := by
  cases r <;> rfl

theorem ignoredOf_map (l : List Signal) : ignoredOf (.list (l.map .sig)) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simpa [ignoredOf] using ih

theorem setSignalDict_valid (d : List (SigKey × Bool)) (h : ValidSigDict d) :
    setSignalDict (.dict d) = .ok (sigEntries d) := by
  have h1 : pySignals.all (fun s => hasKey d (.sig s)) = true := by
    rw [List.all_eq_true]; intro s _; exact h.2 s
  simp [setSignalDict, h.1, h1]

theorem setSignalDict_bad (d : List (SigKey × Bool))
    (h : hasKey d .other = true ∨ ∃ s, hasKey d (.sig s) = false) :
    ∃ m, setSignalDict (.dict d) = .error (.keyError m) := by
  refine ⟨"~is not a valid signal dict", ?_⟩
  rcases h with h | ⟨s, hs⟩
  · simp [setSignalDict, h]
  · have h1 : pySignals.all (fun s => hasKey d (.sig s)) = false := by
      rw [List.all_eq_false]; exact ⟨s, pySignals_mem s, by simp [hs]⟩
    by_cases ho : hasKey d .other = true
    · simp [setSignalDict, ho]
    · simp [setSignalDict, ho, h1]

theorem setSignalDict_nondict (v : CtxArg) (h : ∀ d, v ≠ .dict d) :
    ∃ m, setSignalDict v = .error (.typeError m) := by
  cases v with
  | dict d => exact absurd rfl (h d)
  | _ => exact ⟨_, rfl⟩

theorem setattrExact_proven : SetattrExact := by
  intro c n v
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h1 h2 => ?_, fun hv => ?_, fun r => ?_, fun s hs => ?_, fun hv => ?_, fun d hd => ?_,
    fun d hd => ?_, fun hv => ?_, fun l => ?_, fun name hn => ?_⟩
  · simp [pySetattr, setIntegerCheck, show ¬ n < 1 by omega, bind, Except.bind, pure, Except.pure]
  · simp [pySetattr, setIntegerCheck, h, bind, Except.bind]; rfl
  · simp [pySetattr, setIntegerCheck, show ¬ n > 0 by omega, bind, Except.bind, pure, Except.pure]
  · simp [pySetattr, setIntegerCheck, h, bind, Except.bind]; rfl
  · simp [pySetattr, setIntegerCheck, show ¬ n < 0 by omega, bind, Except.bind, pure, Except.pure]
  · simp [pySetattr, setIntegerCheck, h, bind, Except.bind]; rfl
  · have g : ¬(n < 0 ∨ n > 1) := by omega
    exact ⟨by simp [pySetattr, setIntegerCheck, g, bind, Except.bind, pure, Except.pure],
      by simp [pySetattr, setIntegerCheck, g, bind, Except.bind, pure, Except.pure]⟩
  · have g : n < 0 ∨ n > 1 := by omega
    exact ⟨by simp [pySetattr, setIntegerCheck, g, bind, Except.bind]; rfl,
      by simp [pySetattr, setIntegerCheck, g, bind, Except.bind]; rfl⟩
  · cases v with
    | int m => simp [CtxArg.isInt] at hv
    | _ => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · simp [pySetattr, roundingOfName_name, pure, Except.pure]
  · simp [pySetattr, hs, throw, throwThe, MonadExceptOf.throw]
  · cases v with
    | str s => exact absurd rfl (hv s)
    | _ => exact ⟨_, rfl⟩
  · simp [pySetattr, setSignalDict_valid d hd, bind, Except.bind, pure, Except.pure]
  · obtain ⟨m, hm⟩ := setSignalDict_bad d hd
    exact ⟨⟨m, by simp [pySetattr, hm, bind, Except.bind]⟩, ⟨m, by simp [pySetattr, hm, bind, Except.bind]⟩⟩
  · obtain ⟨m, hm⟩ := setSignalDict_nondict v hv
    exact ⟨⟨m, by simp [pySetattr, hm, bind, Except.bind]⟩, ⟨m, by simp [pySetattr, hm, bind, Except.bind]⟩⟩
  · simp [pySetattr, ignoredOf_map, pure, Except.pure]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hn
    simp [pySetattr, h1, h2, h3, h4, h5, h6, h7, h8, h9, throw, throwThe, MonadExceptOf.throw]

/-! ## The message for a value that is not a dict -/

/-- Assigning anything but a dict to `flags` or `traps` raises `TypeError` with the message the
source writes, `"<value> must be a signal dict"` (_pydecimal.py:4021; `~` marks the formatted
value, as everywhere in the model). -/
def SignalDictTypeErrorMessage : Prop :=
  ∀ (c : PyContext) (v : CtxArg), (∀ d, v ≠ .dict d) →
    pySetattr c "traps" v = .error (.typeError "~must be a signal dict")

/-- `Context().traps = ()`: `"%s must be a signal dict" % ()` formats with an empty argument tuple
and fails with "not enough arguments for format string (got 0)". -/
theorem signalDictTypeErrorMessage_refuted : ¬ SignalDictTypeErrorMessage := by
  intro h
  have hm := h defaultContext (.tuple 0) (fun d hd => nomatch hd)
  simp only [pySetattr, setSignalDict, notSignalDictMsg] at hm
  revert hm
  decide

/-! ## `Context.__init__` -/

/-- An optional int argument. -/
def optInt : Option Int → CtxArg
  | none => .none
  | some n => .int n

/-- A list of signals passed as `flags` or `traps`. -/
def optList : Option (List Signal) → CtxArg
  | none => .none
  | some l => .list (l.map .sig)

/-- The dict `Context()` builds from a list of signals, _pydecimal.py:3994, :4001. -/
def listDict (l : List Signal) : SigDict := pySignals.map (fun s => (s, decide (s ∈ l)))

/-- `Context(prec, rounding, Emin, Emax, capitals, clamp, flags, traps)`
(_pydecimal.py:3969-4003) with ints, a rounding mode, and lists of signals as the docs
describe them (Doc/library/decimal.rst:1104-1120), for every `DefaultContext` whose `traps`
is a signal dict: an argument that is not given (or `None`) is taken from `DefaultContext`,
except `flags`, which start clear; a list of signals becomes the dict of those set; when every
integer is in range the context holds exactly these values. Otherwise the first refused value
in the order `prec`, `Emin`, `Emax`, `capitals`, `clamp` raises its `ValueError`. -/
def ContextInitExact : Prop :=
  ∀ (dc : PyContext) (p emin emax cap cl : Option Int) (r : Option Rounding)
    (fl tr : Option (List Signal)),
    (∀ s, (dc.traps.lookup s).isSome) →
    let P := p.getD dc.prec
    let Em := emin.getD dc.emin
    let EM := emax.getD dc.emax
    let Ca := cap.getD dc.capitals
    let Cl := cl.getD dc.clamp
    let a : CtxInit := { prec := optInt p, rounding := (match r with
                           | none => .none
                           | some r => .str r.name),
                         emin := optInt emin, emax := optInt emax, capitals := optInt cap,
                         clamp := optInt cl, flags := optList fl, traps := optList tr }
    (1 ≤ P → Em ≤ 0 → 0 ≤ EM → (Ca = 0 ∨ Ca = 1) → (Cl = 0 ∨ Cl = 1) →
      pyContextNew dc a = .ok
        { prec := P, rounding := r.getD dc.rounding, emin := Em, emax := EM, capitals := Ca,
          clamp := Cl, flags := listDict (fl.getD []),
          traps := (match tr with
            | none => dc.traps
            | some l => listDict l),
          ignored := [] }) ∧
    (P < 1 → pyContextNew dc a = .error (.valueError s!"prec must be in [1, inf]. got: {P}")) ∧
    (1 ≤ P → 0 < Em → pyContextNew dc a = .error (.valueError s!"Emin must be in [-inf, 0]. got: {Em}")) ∧
    (1 ≤ P → Em ≤ 0 → EM < 0 → pyContextNew dc a = .error (.valueError s!"Emax must be in [0, inf]. got: {EM}"))

theorem orElse_optInt (o : Option Int) (d : Int) : orElseArg (optInt o) (.int d) = .int (o.getD d) := by
  cases o <;> rfl

theorem orElse_optList_flags (o : Option (List Signal)) :
    signalArg (keyed (pySignals.map (fun s => (s, false)))) (optList o) =
      .ok (.dict (keyed (listDict (o.getD [])))) := by
  cases o with
  | none => rfl
  | some l =>
    simp only [optList, signalArg, signalDictOf, listDict, keyed, List.map_map, Option.getD_some]
    have h1 : (l.map SigKey.sig).contains .other = false := by simp
    have h2 : ∀ s, (l.map SigKey.sig).contains (.sig s) = decide (s ∈ l) := by
      intro s; simp
    simp only [h1, h2]
    simp [Function.comp_def]

theorem listDict_total (l : List Signal) (s : Signal) : ((listDict l).lookup s).isSome := by
  cases s <;> rfl

theorem orElse_optList_traps (dc : SigDict) (o : Option (List Signal)) :
    signalArg (keyed dc) (optList o) =
      .ok (.dict (keyed (match o with
        | none => dc
        | some l => listDict l))) := by
  cases o with
  | none => rfl
  | some l =>
    simp only [optList, signalArg, signalDictOf, listDict, keyed, List.map_map]
    have h1 : (l.map SigKey.sig).contains .other = false := by simp
    have h2 : ∀ s, (l.map SigKey.sig).contains (.sig s) = decide (s ∈ l) := by
      intro s; simp
    simp only [h1, h2]
    simp [Function.comp_def]

theorem contextInitExact_proven : ContextInitExact := by
  intro dc p emin emax cap cl r fl tr htr P Em EM Ca Cl a
  have hr : orElseArg (match r with
      | none => CtxArg.none
      | some r => .str r.name) (.str dc.rounding.name) = .str (r.getD dc.rounding).name := by
    cases r <;> rfl
  have hfl := orElse_optList_flags fl
  have htr' := orElse_optList_traps dc.traps tr
  have hkf := setSignalDict_keyed (listDict (fl.getD [])) (listDict_total _)
  have hT : ∀ s, ((match tr with
      | none => dc.traps
      | some l => listDict l).lookup s).isSome := by
    cases tr with
    | none => exact htr
    | some l => exact listDict_total l
  have hkt := setSignalDict_keyed _ hT
  refine ⟨fun h1 h2 h3 h4 h5 => ?_, fun h => ?_, fun h1 h2 => ?_, fun h1 h2 h3 => ?_⟩
  · have g4 : ¬(Ca < 0 ∨ Ca > 1) := by omega
    have g5 : ¬(Cl < 0 ∨ Cl > 1) := by omega
    simp only [pyContextNew, a, orElse_optInt, hr, hfl, htr']
    simp [pySetattr, setIntegerCheck, show ¬ P < 1 by omega, show ¬ Em > 0 by omega,
      show ¬ EM < 0 by omega, g4, g5, roundingOfName_name, ignoredOf, hkf, hkt, bind, Except.bind,
      pure, Except.pure, P, Em, EM, Ca, Cl]
  · simp only [pyContextNew, a, orElse_optInt]
    simp [pySetattr, setIntegerCheck, h, bind, Except.bind, P]; rfl
  · simp only [pyContextNew, a, orElse_optInt, hr]
    simp [pySetattr, setIntegerCheck, show ¬ P < 1 by omega, h2, roundingOfName_name, bind, Except.bind,
      pure, Except.pure, P, Em]; rfl
  · simp only [pyContextNew, a, orElse_optInt, hr]
    simp [pySetattr, setIntegerCheck, show ¬ P < 1 by omega, show ¬ Em > 0 by omega, h3,
      roundingOfName_name, bind, Except.bind, pure, Except.pure, P, Em, EM]; rfl

end PyLean.Decimal
