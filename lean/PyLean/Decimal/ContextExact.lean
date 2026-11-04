import PyLean.Decimal.ContextProps

/-!
`_pydecimal`'s `Context` attributes and constructor, outcome by outcome: what each
assignment stores and the exception, with its message, for every value it refuses.
-/

namespace PyLean.Decimal

open PyLean

/-! ## `__setattr__`, `_set_integer_check`, `_set_signal_dict` -/

/-- A dict whose keys are exactly the nine signals (each once or more). -/
def ValidSigDict (d : List (SigKey × Bool)) : Prop :=
  hasKey d .other = false ∧ ∀ s, hasKey d (.sig s) = true

/-- Every assignment to a `_pydecimal` `Context` attribute (_pydecimal.py:4005-4053):

* `prec`, `Emin`, `Emax`, `capitals`, `clamp` store an int (or a bool, an int to `isinstance`)
  inside `[1, inf]`, `[-inf, 0]`, `[0, inf]`, `[0, 1]`, `[0, 1]` and refuse one outside with
  `ValueError` and the exact text of `_set_integer_check` (:4008-4016), whose `%s` prints a bool as
  `True`/`False` and, for an int of more than 4300 digits, itself raises the int/str-limit
  `ValueError` (`limitOr`); anything that is not an int is a `TypeError`
  (`"%s must be an integer"`, :4006-4007);
* `rounding` stores one of the eight mode names and refuses any other string with
  `TypeError("<s>: invalid rounding mode")`; `value in _rounding_modes` (:4042) compares with `==`,
  so an object whose `__eq__` answers true for a mode is stored (the first such mode in
  `_rounding_modes` order), an exception from `__eq__` propagates, and an object equal to none of
  them is refused; an int (its `%s` subject to the limit), a bool, `None`, a tuple (the argument
  tuple of `%`), a list, a dict or a plain object is refused with the `TypeError` its formatting
  gives (:4045);
* `flags` and `traps` store a dict whose keys are exactly the signals; a dict with another key or
  a missing signal is a `KeyError`, anything else a `TypeError` (:4019-4028);
* `_ignored_flags` stores its value (:4049-4050);
* any other name is an `AttributeError` (:4051-4053).

Each refusal leaves the context unchanged: the model returns an exception and no context. -/
def SetattrExact : Prop :=
  ∀ (c : PyContext) (n : Int) (v : CtxArg),
    -- prec
    (1 ≤ n → pySetattr c "prec" (.int n) = .ok { c with prec := n }) ∧
    (n < 1 → pySetattr c "prec" (.int n) =
      .error (limitOr n (.valueError s!"prec must be in [1, inf]. got: {n}"))) ∧
    -- Emin
    (n ≤ 0 → pySetattr c "Emin" (.int n) = .ok { c with emin := n }) ∧
    (0 < n → pySetattr c "Emin" (.int n) =
      .error (limitOr n (.valueError s!"Emin must be in [-inf, 0]. got: {n}"))) ∧
    -- Emax
    (0 ≤ n → pySetattr c "Emax" (.int n) = .ok { c with emax := n }) ∧
    (n < 0 → pySetattr c "Emax" (.int n) =
      .error (limitOr n (.valueError s!"Emax must be in [0, inf]. got: {n}"))) ∧
    -- capitals, clamp
    ((n = 0 ∨ n = 1) → pySetattr c "capitals" (.int n) = .ok { c with capitals := n } ∧
      pySetattr c "clamp" (.int n) = .ok { c with clamp := n }) ∧
    (n ≠ 0 → n ≠ 1 →
      pySetattr c "capitals" (.int n) =
        .error (limitOr n (.valueError s!"capitals must be in [0, 1]. got {n}")) ∧
      pySetattr c "clamp" (.int n) = .error (limitOr n (.valueError s!"clamp must be in [0, 1]. got {n}"))) ∧
    -- bools
    (pySetattr c "prec" (.bool true) = .ok { c with prec := 1 } ∧
      pySetattr c "prec" (.bool false) = .error (.valueError "prec must be in [1, inf]. got: False") ∧
      pySetattr c "Emin" (.bool true) = .error (.valueError "Emin must be in [-inf, 0]. got: True") ∧
      pySetattr c "Emin" (.bool false) = .ok { c with emin := 0 } ∧
      ∀ b : Bool, pySetattr c "Emax" (.bool b) = .ok { c with emax := if b then 1 else 0 } ∧
        pySetattr c "capitals" (.bool b) = .ok { c with capitals := if b then 1 else 0 } ∧
        pySetattr c "clamp" (.bool b) = .ok { c with clamp := if b then 1 else 0 }) ∧
    -- not an int
    (intValue v = none →
      pySetattr c "prec" v = .error (.typeError "prec must be an integer") ∧
      pySetattr c "Emin" v = .error (.typeError "Emin must be an integer") ∧
      pySetattr c "Emax" v = .error (.typeError "Emax must be an integer") ∧
      pySetattr c "capitals" v = .error (.typeError "capitals must be an integer") ∧
      pySetattr c "clamp" v = .error (.typeError "clamp must be an integer")) ∧
    -- rounding: a str
    (∀ r : Rounding, pySetattr c "rounding" (.str r.name) = .ok { c with rounding := r, roundingObj := none }) ∧
    (∀ s : String, roundingOfName s = none →
      pySetattr c "rounding" (.str s) = .error (.typeError s!"{s}: invalid rounding mode")) ∧
    -- rounding: an object with its own `__eq__`
    (∀ (id : Nat) (eq : List EqAns) (i : Nat) (hi : i < roundingModes.length),
      (∀ j < i, eq.getD j .no = .no) →
      (eq.getD i .no = .yes → pySetattr c "rounding" (.eqObj id eq) =
        .ok { c with rounding := roundingModes[i]'hi, roundingObj := some (id, eq) }) ∧
      (∀ e, eq.getD i .no = .raises e → pySetattr c "rounding" (.eqObj id eq) = .error e)) ∧
    (∀ (id : Nat) (eq : List EqAns), (∀ j < roundingModes.length, eq.getD j .no = .no) →
      pySetattr c "rounding" (.eqObj id eq) = .error (.typeError "~: invalid rounding mode")) ∧
    -- rounding: anything else
    pySetattr c "rounding" (.int n) = .error (limitOr n (.typeError s!"{n}: invalid rounding mode")) ∧
    pySetattr c "rounding" (.bool true) = .error (.typeError "True: invalid rounding mode") ∧
    pySetattr c "rounding" (.bool false) = .error (.typeError "False: invalid rounding mode") ∧
    pySetattr c "rounding" .none = .error (.typeError "None: invalid rounding mode") ∧
    pySetattr c "rounding" (.tuple 0) = .error (.typeError "not enough arguments for format string (got 0)") ∧
    (∀ k : Nat, pySetattr c "rounding" (.tuple (k + 2)) = .error (.typeError
      s!"not all arguments converted during string formatting (required 1, got {k + 2})")) ∧
    ((v = .obj ∨ v = .tuple 1 ∨ (∃ l, v = .list l) ∨ (∃ d, v = .dict d)) →
      pySetattr c "rounding" v = .error (.typeError "~: invalid rounding mode")) ∧
    -- flags, traps
    (∀ d, ValidSigDict d →
      pySetattr c "flags" (.dict d) = .ok { c with flags := sigEntries d } ∧
      pySetattr c "traps" (.dict d) = .ok { c with traps := sigEntries d }) ∧
    (∀ d, (hasKey d .other = true ∨ ∃ s, hasKey d (.sig s) = false) →
      pySetattr c "flags" (.dict d) = .error (.keyError "~is not a valid signal dict") ∧
      pySetattr c "traps" (.dict d) = .error (.keyError "~is not a valid signal dict")) ∧
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
    setSignalDict (.dict d) = .error (.keyError "~is not a valid signal dict") := by
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

theorem eqIn_yes : ∀ (eq : List EqAns) (l : List Rounding) (i : Nat) (h : i < l.length),
    (∀ j < i, eq.getD j .no = .no) → eq.getD i .no = .yes → eqIn eq l = .ok (some (l[i]'h))
  | [], _ :: _, _, _, _, hy => by simp at hy
  | a :: as, r :: rs, 0, _, _, hy => by
    simp only [List.getD_cons_zero] at hy; subst hy; rfl
  | a :: as, r :: rs, i + 1, h, hp, hy => by
    have ha : a = .no := by simpa using hp 0 (by omega)
    subst ha
    simp only [eqIn, List.getElem_cons_succ]
    exact eqIn_yes as rs i (by simp at h; omega) (fun j hj => by simpa using hp (j + 1) (by omega))
      (by simpa using hy)

theorem eqIn_raises : ∀ (eq : List EqAns) (l : List Rounding) (i : Nat) (_ : i < l.length) (e : PyExc),
    (∀ j < i, eq.getD j .no = .no) → eq.getD i .no = .raises e → eqIn eq l = .error e
  | [], _ :: _, _, _, _, _, hy => by simp at hy
  | a :: as, r :: rs, 0, _, e, _, hy => by
    simp only [List.getD_cons_zero] at hy; subst hy; rfl
  | a :: as, r :: rs, i + 1, h, e, hp, hy => by
    have ha : a = .no := by simpa using hp 0 (by omega)
    subst ha
    simp only [eqIn]
    exact eqIn_raises as rs i (by simp at h; omega) e (fun j hj => by simpa using hp (j + 1) (by omega))
      (by simpa using hy)

theorem eqIn_none : ∀ (eq : List EqAns) (l : List Rounding),
    (∀ j < l.length, eq.getD j .no = .no) → eqIn eq l = .ok none
  | [], [], _ => rfl
  | _ :: _, [], _ => rfl
  | [], _ :: _, _ => rfl
  | a :: as, r :: rs, hp => by
    have ha : a = .no := by simpa using hp 0 (by simp)
    subst ha
    simp only [eqIn]
    exact eqIn_none as rs (fun j hj => by simpa using hp (j + 1) (by simp; omega))

theorem setattrExact_proven : SetattrExact := by
  intro c n v
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h1 h2 => ?_, ?_, fun hv => ?_, fun r => ?_, fun s hs => ?_, fun id eq i hi hp => ?_,
    fun id eq hp => ?_, ?_, ?_, ?_, ?_, ?_, fun k => ?_, fun hv => ?_, fun d hd => ?_,
    fun d hd => ?_, fun hv => ?_, fun l => ?_, fun name hn => ?_⟩
  · rw [pySetattr_prec, if_neg (by omega)]
  · rw [pySetattr_prec, if_pos h]
  · rw [pySetattr_emin, if_neg (by omega)]
  · rw [pySetattr_emin, if_pos h]
  · rw [pySetattr_emax, if_neg (by omega)]
  · rw [pySetattr_emax, if_pos h]
  · have g : ¬(n < 0 ∨ n > 1) := by omega
    exact ⟨by rw [pySetattr_capitals, if_neg g], by rw [pySetattr_clamp, if_neg g]⟩
  · have g : n < 0 ∨ n > 1 := by omega
    exact ⟨by rw [pySetattr_capitals, if_pos g], by rw [pySetattr_clamp, if_pos g]⟩
  · refine ⟨rfl, rfl, rfl, rfl, fun b => ?_⟩
    cases b <;> exact ⟨rfl, rfl, rfl⟩
  · cases v with
    | int m => simp [intValue] at hv
    | bool b => simp [intValue] at hv
    | _ => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · simp [pySetattr, roundingOfName_name, pure, Except.pure]
  · simp [pySetattr, hs, throw, throwThe, MonadExceptOf.throw]
  · refine ⟨fun hy => ?_, fun e he => ?_⟩
    · simp [pySetattr, eqIn_yes eq roundingModes i hi hp hy, bind, Except.bind, pure, Except.pure]
    · simp [pySetattr, eqIn_raises eq roundingModes i hi e hp he, bind, Except.bind]
  · simp [pySetattr, eqIn_none eq roundingModes hp, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw]
  · by_cases hl : maxStrDigits < numDigits n.natAbs <;>
      simp [pySetattr, invalidRoundingExc, intText, strLimit, limitOr, hl, bind, Except.bind, throw,
        throwThe, MonadExceptOf.throw, pure, Except.pure]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rcases hv with rfl | rfl | ⟨l, rfl⟩ | ⟨d, rfl⟩ <;> rfl
  · simp [pySetattr, setSignalDict_valid d hd, bind, Except.bind, pure, Except.pure]
  · have hm := setSignalDict_bad d hd
    exact ⟨by simp [pySetattr, hm, bind, Except.bind], by simp [pySetattr, hm, bind, Except.bind]⟩
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

/-- An optional rounding-mode argument, given by its name. -/
def optRound : Option Rounding → CtxArg
  | none => .none
  | some r => .str r.name

/-- A `flags` or `traps` argument: a list (of signals, `.other` standing for any other element)
or a dict. -/
inductive SigArg where
  | list (l : List SigKey)
  | dict (d : List (SigKey × Bool))

def SigArg.arg : SigArg → CtxArg
  | .list l => .list l
  | .dict d => .dict d

/-- An optional `flags` or `traps` argument. -/
def optSig : Option SigArg → CtxArg
  | none => .none
  | some t => t.arg

/-- An argument `_set_signal_dict` accepts: a list of signals only, or a dict whose keys are
exactly the signals. -/
def SigArg.valid : SigArg → Prop
  | .list l => SigKey.other ∉ l
  | .dict d => ValidSigDict d

/-- What a valid argument becomes: for a list, `dict((s, int(s in l)) for s in _signals + l)`
(_pydecimal.py:3994, :4001), each signal in `_signals` order, set exactly when listed; a dict is
stored as given. -/
def SigArg.stored : SigArg → SigDict
  | .list l => pySignals.map (fun s => (s, l.contains (.sig s)))
  | .dict d => sigEntries d

/-- `Context(prec, rounding, Emin, Emax, capitals, clamp, flags, traps, _ignored_flags)`
(_pydecimal.py:3969-4003) with ints, rounding modes, `_ignored_flags` a list of signals, and
`flags` and `traps` lists or dicts, for every `DefaultContext` (a context: its `traps` has every
signal, and a non-str `rounding` it holds compares equal to the mode stored with it, as
`__setattr__` checked when it was assigned). An argument that is not given (or `None`) is taken
from `DefaultContext`, except `flags`, which start clear, and `_ignored_flags`, which starts empty.
When every value is accepted the context holds exactly these values (a list of signals becoming the
dict of those set, a dict stored as is). Otherwise the attributes are assigned in the order `prec`,
`rounding`, `Emin`, `Emax`, `capitals`, `clamp`, `_ignored_flags`, `traps`, `flags`, and the first
refused value raises: the `ValueError` of `_set_integer_check` (the int/str-limit `ValueError` when
its `%s` has more than 4300 digits), the `TypeError` of an unknown rounding name, the `KeyError` of
a list with a non-signal or of a dict that is not a signal dict, or the `TypeError` of a `prec`
that is not an int. -/
def ContextInitExact : Prop :=
  ∀ (dc : PyContext) (p emin emax cap cl : Option Int) (r : Option Rounding)
    (ig : Option (List Signal)) (fl tr : Option SigArg),
    (∀ s, (dc.traps.lookup s).isSome) →
    (∀ id eq, dc.roundingObj = some (id, eq) → eqIn eq roundingModes = .ok (some dc.rounding)) →
    let P := p.getD dc.prec
    let Em := emin.getD dc.emin
    let EM := emax.getD dc.emax
    let Ca := cap.getD dc.capitals
    let Cl := cl.getD dc.clamp
    let a : CtxInit := { prec := optInt p, rounding := optRound r, emin := optInt emin,
                         emax := optInt emax, capitals := optInt cap, clamp := optInt cl,
                         flags := optSig fl, traps := optSig tr, ignored := ig }
    let IntsOk : Prop := 1 ≤ P ∧ Em ≤ 0 ∧ 0 ≤ EM ∧ (Ca = 0 ∨ Ca = 1) ∧ (Cl = 0 ∨ Cl = 1)
    let TrOk : Prop := ∀ t, tr = some t → t.valid
    (IntsOk → TrOk → (∀ f, fl = some f → f.valid) →
      pyContextNew dc a = .ok
        { prec := P, rounding := r.getD dc.rounding, emin := Em, emax := EM, capitals := Ca,
          clamp := Cl,
          flags := (match fl with
            | none => pySignals.map (fun s => (s, false))
            | some f => f.stored),
          traps := (match tr with
            | none => dc.traps
            | some t => t.stored),
          ignored := ig.getD [],
          roundingObj := (match r with
            | none => dc.roundingObj
            | some _ => none) }) ∧
    (P < 1 → pyContextNew dc a = .error (limitOr P (.valueError s!"prec must be in [1, inf]. got: {P}"))) ∧
    (∀ s, roundingOfName s = none → 1 ≤ P →
      pyContextNew dc { a with rounding := .str s } = .error (.typeError s!"{s}: invalid rounding mode")) ∧
    (1 ≤ P → 0 < Em →
      pyContextNew dc a = .error (limitOr Em (.valueError s!"Emin must be in [-inf, 0]. got: {Em}"))) ∧
    (1 ≤ P → Em ≤ 0 → EM < 0 →
      pyContextNew dc a = .error (limitOr EM (.valueError s!"Emax must be in [0, inf]. got: {EM}"))) ∧
    (1 ≤ P → Em ≤ 0 → 0 ≤ EM → ¬(Ca = 0 ∨ Ca = 1) →
      pyContextNew dc a = .error (limitOr Ca (.valueError s!"capitals must be in [0, 1]. got {Ca}"))) ∧
    (1 ≤ P → Em ≤ 0 → 0 ≤ EM → (Ca = 0 ∨ Ca = 1) → ¬(Cl = 0 ∨ Cl = 1) →
      pyContextNew dc a = .error (limitOr Cl (.valueError s!"clamp must be in [0, 1]. got {Cl}"))) ∧
    (IntsOk → ∀ t, tr = some t → ¬ t.valid →
      pyContextNew dc a = .error (.keyError "~is not a valid signal dict")) ∧
    (IntsOk → TrOk → ∀ f, fl = some f → ¬ f.valid →
      pyContextNew dc a = .error (.keyError "~is not a valid signal dict")) ∧
    (∀ v, intValue v = none → v ≠ .none →
      pyContextNew dc { a with prec := v } = .error (.typeError "prec must be an integer"))

theorem orElse_optInt (o : Option Int) (d : Int) : orElseArg (optInt o) (.int d) = .int (o.getD d) := by
  cases o <;> rfl

theorem orElse_ne (v d : CtxArg) (h : v ≠ .none) : orElseArg v d = v := by
  cases v <;> simp_all [orElseArg]

theorem listDict_total (l : List SigKey) (s : Signal) :
    ((pySignals.map (fun s => (s, l.contains (.sig s)))).lookup s).isSome := by
  cases s <;> rfl

theorem clearDict0_keyed :
    setSignalDict (.dict (keyed (pySignals.map (fun s => (s, false))))) =
      .ok (pySignals.map (fun s => (s, false))) :=
  setSignalDict_keyed _ clearDict0_total

theorem signalDictOf_valid (l : List SigKey) (h : SigKey.other ∉ l) :
    signalDictOf l = keyed (pySignals.map (fun s => (s, l.contains (.sig s)))) := by
  have h1 : l.contains .other = false := by simpa using h
  simp only [signalDictOf, h1, keyed, List.map_map]
  simp [Function.comp_def]

theorem sigArg_ok (dflt : List (SigKey × Bool)) (t : SigArg) (h : t.valid) :
    ∃ d, signalArg dflt t.arg = .ok (.dict d) ∧ setSignalDict (.dict d) = .ok t.stored := by
  cases t with
  | list l =>
    refine ⟨signalDictOf l, rfl, ?_⟩
    rw [signalDictOf_valid l h]
    exact setSignalDict_keyed _ (listDict_total l)
  | dict d => exact ⟨d, rfl, setSignalDict_valid d h⟩

theorem sigArg_bad (dflt : List (SigKey × Bool)) (t : SigArg) (h : ¬ t.valid) :
    ∃ d, signalArg dflt t.arg = .ok (.dict d) ∧
      setSignalDict (.dict d) = .error (.keyError "~is not a valid signal dict") := by
  cases t with
  | list l =>
    refine ⟨signalDictOf l, rfl, setSignalDict_bad _ (Or.inl ?_)⟩
    have hm : SigKey.other ∈ l := Classical.byContradiction h
    have h1 : l.contains .other = true := by simpa using hm
    simp [signalDictOf, h1, hasKey]
  | dict d =>
    refine ⟨d, rfl, setSignalDict_bad d ?_⟩
    by_cases ho : hasKey d .other = true
    · exact Or.inl ho
    · refine Or.inr (Classical.byContradiction fun hc => h ⟨by simpa using ho, fun s => ?_⟩)
      cases hs : hasKey d (.sig s)
      · exact absurd ⟨s, hs⟩ hc
      · rfl

/-- `signalArg` then `_set_signal_dict` on an accepted argument, or on none. -/
theorem sigStep (dflt : List (SigKey × Bool)) (D : SigDict) (o : Option SigArg)
    (hD : setSignalDict (.dict dflt) = .ok D) (hv : ∀ t, o = some t → t.valid) :
    ∃ d, signalArg dflt (optSig o) = .ok (.dict d) ∧
      setSignalDict (.dict d) = .ok (match o with
        | none => D
        | some t => t.stored) := by
  cases o with
  | none => exact ⟨dflt, rfl, hD⟩
  | some t => exact sigArg_ok dflt t (hv t rfl)

theorem pySetattr_rounding_init (dc c : PyContext) (r : Option Rounding)
    (hro : ∀ id eq, dc.roundingObj = some (id, eq) → eqIn eq roundingModes = .ok (some dc.rounding)) :
    pySetattr c "rounding" (orElseArg (optRound r) dc.roundingArg) =
      .ok { c with rounding := r.getD dc.rounding, roundingObj := (match r with
        | none => dc.roundingObj
        | some _ => none) } := by
  cases r with
  | some m => simp [optRound, orElseArg, pySetattr, roundingOfName_name, pure, Except.pure]
  | none =>
    simp only [optRound, orElseArg, PyContext.roundingArg, Option.getD_none]
    cases h : dc.roundingObj with
    | none => simp [pySetattr, roundingOfName_name, pure, Except.pure]
    | some x =>
      obtain ⟨id, eq⟩ := x
      simp [pySetattr, hro id eq h, bind, Except.bind, pure, Except.pure]

theorem pySetattr_ignored (c : PyContext) (l : List Signal) :
    pySetattr c "_ignored_flags" (.list (l.map .sig)) = .ok { c with ignored := l } := by
  simp [pySetattr, ignoredOf_map, pure, Except.pure]

theorem pySetattr_prec_type (c : PyContext) (v : CtxArg) (h : intValue v = none) :
    pySetattr c "prec" v = .error (.typeError "prec must be an integer") := by
  cases v with
  | int m => simp [intValue] at h
  | bool b => simp [intValue] at h
  | _ => rfl

theorem contextInitExact_proven : ContextInitExact := by
  intro dc p emin emax cap cl r ig fl tr htr hro
  dsimp only
  have hR := pySetattr_rounding_init dc · r hro
  have hT0 := setSignalDict_keyed dc.traps htr
  refine ⟨fun hI hT hF => ?_, fun h => ?_, fun s hs h1 => ?_, fun h1 h2 => ?_, fun h1 h2 h3 => ?_,
    fun h1 h2 h3 h4 => ?_, fun h1 h2 h3 h4 h5 => ?_, fun hI t ht hb => ?_, fun hI hT f hf hb => ?_,
    fun v hv hn => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hI
    obtain ⟨dT, e1, e2⟩ := sigStep (keyed dc.traps) dc.traps tr hT0 hT
    obtain ⟨dF, e3, e4⟩ := sigStep (keyed (pySignals.map (fun s => (s, false))))
      (pySignals.map (fun s => (s, false))) fl clearDict0_keyed hF
    have g1 : ¬ p.getD dc.prec < 1 := by omega
    have g2 : ¬ emin.getD dc.emin > 0 := by omega
    have g3 : ¬ emax.getD dc.emax < 0 := by omega
    have g4 : ¬ (cap.getD dc.capitals < 0 ∨ cap.getD dc.capitals > 1) := by omega
    have g5 : ¬ (cl.getD dc.clamp < 0 ∨ cl.getD dc.clamp > 1) := by omega
    simp only [pyContextNew, orElse_optInt, pySetattr_prec, if_neg g1, hR, pySetattr_emin, if_neg g2,
      pySetattr_emax, if_neg g3, pySetattr_capitals, if_neg g4, pySetattr_clamp, if_neg g5,
      pySetattr_ignored, e1, e3, pySetattr_traps, pySetattr_flags, e2, e4, bind, Except.bind, pure,
      Except.pure]
  · simp only [pyContextNew, orElse_optInt, pySetattr_prec, if_pos h, bind, Except.bind]
  · simp only [pyContextNew, orElse_optInt, pySetattr_prec, if_neg (show ¬ p.getD dc.prec < 1 by omega),
      bind, Except.bind]
    simp [orElseArg, pySetattr, hs, throw, throwThe, MonadExceptOf.throw]
  · simp only [pyContextNew, orElse_optInt, pySetattr_prec, if_neg (show ¬ p.getD dc.prec < 1 by omega),
      hR, pySetattr_emin, if_pos (show emin.getD dc.emin > 0 from h2), bind, Except.bind]
  · simp only [pyContextNew, orElse_optInt, pySetattr_prec, if_neg (show ¬ p.getD dc.prec < 1 by omega),
      hR, pySetattr_emin, if_neg (show ¬ emin.getD dc.emin > 0 by omega), pySetattr_emax, if_pos h3,
      bind, Except.bind]
  · have g4 : cap.getD dc.capitals < 0 ∨ cap.getD dc.capitals > 1 := by omega
    simp only [pyContextNew, orElse_optInt, pySetattr_prec, if_neg (show ¬ p.getD dc.prec < 1 by omega),
      hR, pySetattr_emin, if_neg (show ¬ emin.getD dc.emin > 0 by omega), pySetattr_emax,
      if_neg (show ¬ emax.getD dc.emax < 0 by omega), pySetattr_capitals, if_pos g4, bind, Except.bind]
  · have g4 : ¬ (cap.getD dc.capitals < 0 ∨ cap.getD dc.capitals > 1) := by omega
    have g5 : cl.getD dc.clamp < 0 ∨ cl.getD dc.clamp > 1 := by omega
    simp only [pyContextNew, orElse_optInt, pySetattr_prec, if_neg (show ¬ p.getD dc.prec < 1 by omega),
      hR, pySetattr_emin, if_neg (show ¬ emin.getD dc.emin > 0 by omega), pySetattr_emax,
      if_neg (show ¬ emax.getD dc.emax < 0 by omega), pySetattr_capitals, if_neg g4, pySetattr_clamp,
      if_pos g5, bind, Except.bind]
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hI
    subst ht
    obtain ⟨dT, e1, e2⟩ := sigArg_bad (keyed dc.traps) t hb
    have g4 : ¬ (cap.getD dc.capitals < 0 ∨ cap.getD dc.capitals > 1) := by omega
    have g5 : ¬ (cl.getD dc.clamp < 0 ∨ cl.getD dc.clamp > 1) := by omega
    simp only [pyContextNew, orElse_optInt, pySetattr_prec, if_neg (show ¬ p.getD dc.prec < 1 by omega),
      hR, pySetattr_emin, if_neg (show ¬ emin.getD dc.emin > 0 by omega), pySetattr_emax,
      if_neg (show ¬ emax.getD dc.emax < 0 by omega), pySetattr_capitals, if_neg g4, pySetattr_clamp,
      if_neg g5, pySetattr_ignored, optSig, e1, pySetattr_traps, e2, bind, Except.bind]
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hI
    subst hf
    obtain ⟨dT, e1, e2⟩ := sigStep (keyed dc.traps) dc.traps tr hT0 hT
    obtain ⟨dF, e3, e4⟩ := sigArg_bad (keyed (pySignals.map (fun s => (s, false)))) f hb
    have g4 : ¬ (cap.getD dc.capitals < 0 ∨ cap.getD dc.capitals > 1) := by omega
    have g5 : ¬ (cl.getD dc.clamp < 0 ∨ cl.getD dc.clamp > 1) := by omega
    simp only [pyContextNew, orElse_optInt, pySetattr_prec, if_neg (show ¬ p.getD dc.prec < 1 by omega),
      hR, pySetattr_emin, if_neg (show ¬ emin.getD dc.emin > 0 by omega), pySetattr_emax,
      if_neg (show ¬ emax.getD dc.emax < 0 by omega), pySetattr_capitals, if_neg g4, pySetattr_clamp,
      if_neg g5, pySetattr_ignored, e1, pySetattr_traps, e2, optSig, e3, pySetattr_flags, e4, bind,
      Except.bind, pure, Except.pure]
  · simp only [pyContextNew, orElse_ne v _ hn, pySetattr_prec_type _ v hv, bind, Except.bind]

end PyLean.Decimal
