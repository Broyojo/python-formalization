import PyLean.Decimal.ContextProps

/-!
`_pydecimal`'s `Context` attributes and constructor, outcome by outcome: what each
assignment stores and the exception, with its message, for every value it refuses.
-/

namespace PyLean.Decimal

open PyLean

/-! ## What formatting an object into a message raises, stated without the model's functions -/

/-- `repr()` of every element returns. -/
def AllPrint (l : List SigKey) : Prop := ∀ k ∈ l, k.reprErr = none

/-- `repr()` of the list raises `e`: the elements before one whose `repr()` raises `e` print. -/
def ListRaises (l : List SigKey) (e : PyExc) : Prop :=
  ∃ pre k post, l = pre ++ k :: post ∧ AllPrint pre ∧ k.reprErr = some e

/-- `repr()` of every key and value returns. -/
def DictPrints (d : List (SigKey × SigVal)) : Prop := ∀ p ∈ d, p.1.reprErr = none ∧ p.2.repr = none

/-- `repr()` of the dict raises `e`: the items before print, and then the key raises `e`, or the
key prints and its value raises `e`. -/
def DictRaises (d : List (SigKey × SigVal)) (e : PyExc) : Prop :=
  ∃ pre k v post, d = pre ++ (k, v) :: post ∧ DictPrints pre ∧
    (k.reprErr = some e ∨ (k.reprErr = none ∧ v.repr = some e))

/-- `str()` of a value returns: an int of at most 4300 digits, a list or dict whose elements
print, an object whose `__str__` returns; `None`, a bool and a str always. -/
def Prints : CtxArg → Prop
  | .int n => numDigits n.natAbs ≤ maxStrDigits
  | .eqObj _ _ s => s = none
  | .list l => AllPrint l
  | .dict d => DictPrints d
  | .obj s => s = none
  | _ => True

/-- `str()` of a value raises `e`. -/
def StrRaises : CtxArg → PyExc → Prop
  | .int n, e => maxStrDigits < numDigits n.natAbs ∧ e = .valueError limitToStrMsg
  | .eqObj _ _ s, e => s = some e
  | .list l, e => ListRaises l e
  | .dict d, e => DictRaises d e
  | .obj s, e => s = some e
  | _, _ => False

/-- `r` is what `fmt % v` with one `%s` raises for a `v` that is not a tuple: `ok` when `str(v)`
prints, its exception when it raises. -/
def PlainRaises (v : CtxArg) (ok r : PyExc) : Prop :=
  (Prints v → r = ok) ∧ ∀ e, StrRaises v e → r = e

/-- `r` is what `raise E(fmt % v)` raises, for a format with one `%s` and the exception `ok` built
from the formatted text: a tuple is `%`'s argument tuple (none: "not enough arguments"; the first
element formatted; a second one left: "not all arguments converted"), anything else is
`PlainRaises`. -/
def PctRaises (v : CtxArg) (ok r : PyExc) : Prop :=
  match v with
  | .tuple [] => r = .typeError "not enough arguments for format string (got 0)"
  | .tuple (some e :: _) => r = e
  | .tuple [none] => r = ok
  | .tuple (none :: _ :: rest) =>
    r = .typeError s!"not all arguments converted during string formatting (required 1, got {rest.length + 2})"
  | .none => PlainRaises .none ok r
  | .int n => PlainRaises (.int n) ok r
  | .bool b => PlainRaises (.bool b) ok r
  | .eqObj id eq st => PlainRaises (.eqObj id eq st) ok r
  | .str s => PlainRaises (.str s) ok r
  | .list l => PlainRaises (.list l) ok r
  | .dict d => PlainRaises (.dict d) ok r
  | .obj st => PlainRaises (.obj st) ok r

theorem listReprErr_none : ∀ l, AllPrint l → listReprErr l = none
  | [], _ => rfl
  | k :: rest, h => by
    have hk : k.reprErr = none := h k (by simp)
    simp only [listReprErr, hk]
    exact listReprErr_none rest (fun x hx => h x (by simp [hx]))

theorem listReprErr_some (e : PyExc) : ∀ (pre : List SigKey) (k : SigKey) (post : List SigKey),
    AllPrint pre → k.reprErr = some e → listReprErr (pre ++ k :: post) = some e
  | [], k, post, _, hk => by simp [listReprErr, hk]
  | x :: pre, k, post, h, hk => by
    have hx : x.reprErr = none := h x (by simp)
    simp only [List.cons_append, listReprErr, hx]
    exact listReprErr_some e pre k post (fun y hy => h y (by simp [hy])) hk

theorem dictReprErr_none : ∀ d, DictPrints d → dictReprErr d = none
  | [], _ => rfl
  | (k, v) :: rest, h => by
    obtain ⟨hk, hv⟩ := h (k, v) (by simp)
    have hk' : k.reprErr = none := hk
    have hv' : v.repr = none := hv
    simp only [dictReprErr, hk', hv']
    exact dictReprErr_none rest (fun x hx => h x (by simp [hx]))

theorem dictReprErr_some (e : PyExc) : ∀ (pre : List (SigKey × SigVal)) (k : SigKey) (v : SigVal)
    (post : List (SigKey × SigVal)), DictPrints pre →
    (k.reprErr = some e ∨ (k.reprErr = none ∧ v.repr = some e)) →
    dictReprErr (pre ++ (k, v) :: post) = some e
  | [], k, v, post, _, h => by
    rcases h with hk | ⟨hk, hv⟩
    · simp [dictReprErr, hk]
    · simp [dictReprErr, hk, hv]
  | (x, y) :: pre, k, v, post, h, hkv => by
    obtain ⟨hx, hy⟩ := h (x, y) (by simp)
    have hx' : x.reprErr = none := hx
    have hy' : y.repr = none := hy
    simp only [List.cons_append, dictReprErr, hx', hy']
    exact dictReprErr_some e pre k v post (fun p hp => h p (by simp [hp])) hkv

theorem plain_spec (v : CtxArg) (ok : PyExc) (hv : ∀ t, v ≠ .tuple t) :
    PlainRaises v ok (pctExc v.strErr ok) := by
  cases v with
  | tuple t => exact absurd rfl (hv t)
  | none => exact ⟨fun _ => rfl, fun e h => h.elim⟩
  | bool b => exact ⟨fun _ => rfl, fun e h => h.elim⟩
  | str s => exact ⟨fun _ => rfl, fun e h => h.elim⟩
  | int n =>
    refine ⟨fun h => ?_, fun e h => ?_⟩
    · have h' : numDigits n.natAbs ≤ maxStrDigits := h
      simp [pctExc, CtxArg.strErr, intStrErr, show ¬ maxStrDigits < numDigits n.natAbs by omega]
    · obtain ⟨h1, h2⟩ := h
      simp [pctExc, CtxArg.strErr, intStrErr, h1, h2]
  | eqObj id eq st =>
    refine ⟨fun h => ?_, fun e h => ?_⟩
    · have h' : st = none := h
      simp [pctExc, CtxArg.strErr, h']
    · have h' : st = some e := h
      simp [pctExc, CtxArg.strErr, h']
  | obj st =>
    refine ⟨fun h => ?_, fun e h => ?_⟩
    · have h' : st = none := h
      simp [pctExc, CtxArg.strErr, h']
    · have h' : st = some e := h
      simp [pctExc, CtxArg.strErr, h']
  | list l =>
    refine ⟨fun h => ?_, fun e h => ?_⟩
    · simp [pctExc, CtxArg.strErr, listReprErr_none l h]
    · obtain ⟨pre, k, post, rfl, hp, hk⟩ := h
      simp [pctExc, CtxArg.strErr, listReprErr_some e pre k post hp hk]
  | dict d =>
    refine ⟨fun h => ?_, fun e h => ?_⟩
    · simp [pctExc, CtxArg.strErr, dictReprErr_none d h]
    · obtain ⟨pre, k, w, post, rfl, hp, hk⟩ := h
      simp [pctExc, CtxArg.strErr, dictReprErr_some e pre k w post hp hk]

/-- `CtxArg.pct` is what the formatting raises. -/
theorem pct_spec (v : CtxArg) (ok : PyExc) : PctRaises v ok (v.pct ok) := by
  cases v with
  | tuple t =>
    match t with
    | [] => rfl
    | some e :: _ => rfl
    | [none] => rfl
    | none :: x :: rest => simp [PctRaises, CtxArg.pct, pctTupleExc]
  | none => exact plain_spec .none ok (fun t h => nomatch h)
  | int n => exact plain_spec (.int n) ok (fun t h => nomatch h)
  | bool b => exact plain_spec (.bool b) ok (fun t h => nomatch h)
  | eqObj id eq st => exact plain_spec (.eqObj id eq st) ok (fun t h => nomatch h)
  | str s => exact plain_spec (.str s) ok (fun t h => nomatch h)
  | list l => exact plain_spec (.list l) ok (fun t h => nomatch h)
  | dict d => exact plain_spec (.dict d) ok (fun t h => nomatch h)
  | obj st => exact plain_spec (.obj st) ok (fun t h => nomatch h)

/-! ## `__setattr__`, `_set_integer_check`, `_set_signal_dict` -/

/-- A dict whose keys are exactly the nine signals (each once or more). -/
def ValidSigDict (d : List (SigKey × SigVal)) : Prop :=
  hasOther d = false ∧ ∀ s, hasKey d (.sig s) = true

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
  them is refused; any other value is refused with what `raise TypeError("%s: invalid rounding
  mode" % value)` (:4045) raises (`PctRaises`): the `TypeError`, or the exception `str(value)`
  raises (an int of more than 4300 digits, `[10**5000]`, a `__str__` that raises), or for a tuple
  the argument-tuple errors of `%`;
* `flags` and `traps` store a dict whose keys are exactly the signals; a dict with another key or
  a missing signal raises what `raise KeyError("%s is not a valid signal dict" % d)` raises: the
  `KeyError`, or the exception `repr()` of the first key or value that does not print raises
  (`{10**5000: 1}`, `{Clamped: 10**5000, ...}`); anything else raises what
  `raise TypeError("%s must be a signal dict" % d)` raises (:4019-4028);
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
    (∀ (id : Nat) (eq : List EqAns) (st : StrErr) (i : Nat) (hi : i < roundingModes.length),
      (∀ j < i, eq.getD j .no = .no) →
      (eq.getD i .no = .yes → pySetattr c "rounding" (.eqObj id eq st) =
        .ok { c with rounding := roundingModes[i]'hi, roundingObj := some (id, eq, st) }) ∧
      (∀ e, eq.getD i .no = .raises e → pySetattr c "rounding" (.eqObj id eq st) = .error e)) ∧
    (∀ (id : Nat) (eq : List EqAns) (st : StrErr), (∀ j < roundingModes.length, eq.getD j .no = .no) →
      ∃ r, pySetattr c "rounding" (.eqObj id eq st) = .error r ∧
        PctRaises (.eqObj id eq st) (.typeError "~: invalid rounding mode") r) ∧
    -- rounding: anything else
    pySetattr c "rounding" (.int n) = .error (limitOr n (.typeError s!"{n}: invalid rounding mode")) ∧
    pySetattr c "rounding" (.bool true) = .error (.typeError "True: invalid rounding mode") ∧
    pySetattr c "rounding" (.bool false) = .error (.typeError "False: invalid rounding mode") ∧
    pySetattr c "rounding" .none = .error (.typeError "None: invalid rounding mode") ∧
    (((∃ s, v = .obj s) ∨ (∃ t, v = .tuple t) ∨ (∃ l, v = .list l) ∨ (∃ d, v = .dict d)) →
      ∃ r, pySetattr c "rounding" v = .error r ∧ PctRaises v (.typeError "~: invalid rounding mode") r) ∧
    -- flags, traps
    (∀ d, ValidSigDict d →
      pySetattr c "flags" (.dict d) = .ok { c with flags := sigEntries d } ∧
      pySetattr c "traps" (.dict d) = .ok { c with traps := sigEntries d }) ∧
    (∀ d, (hasOther d = true ∨ ∃ s, hasKey d (.sig s) = false) →
      ∃ r, pySetattr c "flags" (.dict d) = .error r ∧ pySetattr c "traps" (.dict d) = .error r ∧
        PctRaises (.dict d) (.keyError "~is not a valid signal dict") r) ∧
    ((∀ d, v ≠ .dict d) →
      ∃ r, pySetattr c "flags" v = .error r ∧ pySetattr c "traps" v = .error r ∧
        PctRaises v (.typeError "~must be a signal dict") r) ∧
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

theorem setSignalDict_valid (d : List (SigKey × SigVal)) (h : ValidSigDict d) :
    setSignalDict (.dict d) = .ok (sigEntries d) := by
  have h1 : pySignals.all (fun s => hasKey d (.sig s)) = true := by
    rw [List.all_eq_true]; intro s _; exact h.2 s
  simp [setSignalDict, h.1, h1]

theorem setSignalDict_bad (d : List (SigKey × SigVal))
    (h : hasOther d = true ∨ ∃ s, hasKey d (.sig s) = false) :
    setSignalDict (.dict d) = .error ((CtxArg.dict d).pct (.keyError "~is not a valid signal dict")) := by
  rcases h with h | ⟨s, hs⟩
  · simp [setSignalDict, h]
  · have h1 : pySignals.all (fun s => hasKey d (.sig s)) = false := by
      rw [List.all_eq_false]; exact ⟨s, pySignals_mem s, by simp [hs]⟩
    by_cases ho : hasOther d = true
    · simp [setSignalDict, ho]
    · simp [setSignalDict, ho, h1]

theorem setSignalDict_nondict (v : CtxArg) (h : ∀ d, v ≠ .dict d) :
    setSignalDict v = .error (v.pct (.typeError "~must be a signal dict")) := by
  cases v with
  | dict d => exact absurd rfl (h d)
  | _ => rfl

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

/-- An assignment to `rounding` that `value in _rounding_modes` refuses without calling Python
code raises the formatting's exception. -/
theorem pySetattr_rounding_other (c : PyContext) (v : CtxArg)
    (hv : (∃ s, v = .obj s) ∨ (∃ t, v = .tuple t) ∨ (∃ l, v = .list l) ∨ (∃ d, v = .dict d)) :
    pySetattr c "rounding" v = .error (v.pct (.typeError "~: invalid rounding mode")) := by
  rcases hv with ⟨s, rfl⟩ | ⟨t, rfl⟩ | ⟨l, rfl⟩ | ⟨d, rfl⟩ <;> rfl

theorem setattrExact_proven : SetattrExact := by
  intro c n v
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h1 h2 => ?_, ?_, fun hv => ?_, fun r => ?_, fun s hs => ?_, fun id eq st i hi hp => ?_,
    fun id eq st hp => ?_, ?_, ?_, ?_, ?_, fun hv => ?_, fun d hd => ?_,
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
  · simp [pySetattr, hs, invalidRoundingExc, CtxArg.pct, pctExc, CtxArg.strErr, roundingMsg, throw,
      throwThe, MonadExceptOf.throw]
  · refine ⟨fun hy => ?_, fun e he => ?_⟩
    · simp [pySetattr, eqIn_yes eq roundingModes i hi hp hy, bind, Except.bind, pure, Except.pure]
    · simp [pySetattr, eqIn_raises eq roundingModes i hi e hp he, bind, Except.bind]
  · refine ⟨_, ?_, pct_spec (.eqObj id eq st) (.typeError "~: invalid rounding mode")⟩
    simp [pySetattr, eqIn_none eq roundingModes hp, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw, invalidRoundingExc, roundingMsg]
  · by_cases hl : maxStrDigits < numDigits n.natAbs <;>
      simp [pySetattr, invalidRoundingExc, roundingMsg, CtxArg.pct, pctExc, CtxArg.strErr, intStrErr,
        limitOr, hl, throw, throwThe, MonadExceptOf.throw]
  · rfl
  · rfl
  · rfl
  · exact ⟨_, pySetattr_rounding_other c v hv, pct_spec v _⟩
  · simp [pySetattr, setSignalDict_valid d hd, bind, Except.bind, pure, Except.pure]
  · have hm := setSignalDict_bad d hd
    exact ⟨_, by simp [pySetattr, hm, bind, Except.bind], by simp [pySetattr, hm, bind, Except.bind],
      pct_spec (.dict d) _⟩
  · have hm := setSignalDict_nondict v hv
    exact ⟨_, by simp [pySetattr, hm, bind, Except.bind], by simp [pySetattr, hm, bind, Except.bind],
      pct_spec v _⟩
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
  have hm := h defaultContext (.tuple []) (fun d hd => nomatch hd)
  simp only [pySetattr, setSignalDict, CtxArg.pct, pctTupleExc] at hm
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

/-- A `flags` or `traps` argument: a list (of signals and other objects) or a dict. -/
inductive SigArg where
  | list (l : List SigKey)
  | dict (d : List (SigKey × SigVal))

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
  | .list l => ∀ k ∈ l, k.isSig = true
  | .dict d => ValidSigDict d

/-- What a valid argument becomes: for a list, `dict((s, int(s in l)) for s in _signals + l)`
(_pydecimal.py:3994, :4001), each signal in `_signals` order, set exactly when listed; a dict is
stored as given. -/
def SigArg.stored : SigArg → SigDict
  | .list l => pySignals.map (fun s => (s, l.contains (.sig s)))
  | .dict d => sigEntries d

/-- The dict an optional argument leaves: `D` when it is not given. -/
def SigArg.storedOr (D : SigDict) : Option SigArg → SigDict
  | none => D
  | some t => t.stored

/-- What `hash()` of an element raises (`none`: it is hashable); a signal is a class. -/
def SigKey.hashErr : SigKey → StrErr
  | .sig _ => none
  | .other _ h => h

/-- `r` is what `Context()` raises for a `flags` or `traps` argument `_set_signal_dict` refuses.
A list first becomes `dict((s, int(s in l)) for s in _signals + l)` (:3994, :4001), whose
construction hashes the elements in order: the first one whose `hash()` raises `e` stops it, a
`TypeError` becoming "cannot use '<type>' as a dict key (<e>)" and anything else propagating
(Objects/dictobject.c:2442-2461). When every element hashes, the dict has a key that is not a
signal and `raise KeyError("%s is not a valid signal dict" % d)` (:4024) formats it: the signals
and the `0`/`1` values print, so it raises the `KeyError` when every element prints, or the
exception `repr()` of the first element that does not print raises. A dict goes to
`_set_signal_dict` as is (`PctRaises`). -/
def SigRefusal : SigArg → PyExc → Prop
  | .list l, r =>
    (∀ pre k post e, l = pre ++ k :: post → (∀ x ∈ pre, x.hashErr = none) → k.hashErr = some e →
      (∀ m, e = .typeError m → r = .typeError s!"~cannot use as a dict key ({m})") ∧
      ((∀ m, e ≠ .typeError m) → r = e)) ∧
    ((∀ x ∈ l, x.hashErr = none) →
      (AllPrint l → r = .keyError "~is not a valid signal dict") ∧ ∀ e, ListRaises l e → r = e)
  | .dict d, r => PctRaises (.dict d) (.keyError "~is not a valid signal dict") r

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
its `%s` has more than 4300 digits), the `TypeError` of an unknown rounding name, what refusing a
`traps` or `flags` list or dict raises (`SigRefusal`: an unhashable element's `TypeError`, the
`KeyError`, or the exception of formatting the dict into its message, as for `Context(traps=[[]])`
and `Context(traps=[10**5000])`), or the `TypeError` of a `prec` that is not an int. -/
def ContextInitExact : Prop :=
  ∀ (dc : PyContext) (p emin emax cap cl : Option Int) (r : Option Rounding)
    (ig : Option (List Signal)) (fl tr : Option SigArg),
    (∀ s, (dc.traps.lookup s).isSome) →
    (∀ id eq st, dc.roundingObj = some (id, eq, st) → eqIn eq roundingModes = .ok (some dc.rounding)) →
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
          flags := SigArg.storedOr (pySignals.map (fun s => (s, false))) fl,
          traps := SigArg.storedOr dc.traps tr,
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
      ∃ e, pyContextNew dc a = .error e ∧ SigRefusal t e) ∧
    (IntsOk → TrOk → ∀ f, fl = some f → ¬ f.valid →
      ∃ e, pyContextNew dc a = .error e ∧ SigRefusal f e) ∧
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

/-- The items `otherItems` adds when every element hashes. -/
def otherList : List SigKey → List (SigKey × SigVal)
  | [] => []
  | .sig _ :: rest => otherList rest
  | .other r _ :: rest => (.other r none, { truth := true }) :: otherList rest

theorem otherItems_ok : ∀ l : List SigKey, (∀ x ∈ l, x.hashErr = none) →
    otherItems l = .ok (otherList l)
  | [], _ => rfl
  | .sig s :: rest, h => by
    simp only [otherItems, otherList]
    exact otherItems_ok rest (fun x hx => h x (by simp [hx]))
  | .other r hh :: rest, h => by
    have h0 : hh = none := h (.other r hh) (by simp)
    subst h0
    simp only [otherItems, otherList]
    rw [otherItems_ok rest (fun x hx => h x (by simp [hx]))]
    rfl

theorem otherItems_err (e : PyExc) : ∀ (pre : List SigKey) (k : SigKey) (post : List SigKey),
    (∀ x ∈ pre, x.hashErr = none) → k.hashErr = some e →
    otherItems (pre ++ k :: post) = .error (dictKeyExc e)
  | [], .sig s, post, _, hk => by simp [SigKey.hashErr] at hk
  | [], .other r h, post, _, hk => by
    simp only [SigKey.hashErr] at hk
    subst hk
    rfl
  | .sig s :: pre, k, post, hp, hk => by
    simp only [List.cons_append, otherItems]
    exact otherItems_err e pre k post (fun x hx => hp x (by simp [hx])) hk
  | .other r h :: pre, k, post, hp, hk => by
    have h0 : h = none := hp (.other r h) (by simp)
    subst h0
    simp only [List.cons_append, otherItems]
    rw [otherItems_err e pre k post (fun x hx => hp x (by simp [hx])) hk]
    rfl

theorem first_hash_err : ∀ l : List SigKey, ¬ (∀ x ∈ l, x.hashErr = none) →
    ∃ pre k post e, l = pre ++ k :: post ∧ (∀ x ∈ pre, x.hashErr = none) ∧ k.hashErr = some e
  | [], h => absurd (fun x hx => by simp at hx) h
  | k :: rest, h => by
    cases hk : k.hashErr with
    | some e => exact ⟨[], k, rest, e, rfl, by simp, hk⟩
    | none =>
      have h' : ¬ (∀ x ∈ rest, x.hashErr = none) := fun hr => h (fun x hx => by
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hk
        · exact hr x hx)
      obtain ⟨pre, k', post, e, h1, h2, h3⟩ := first_hash_err rest h'
      refine ⟨k :: pre, k', post, e, by simp [h1], fun x hx => ?_, h3⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hk
      · exact h2 x hx

theorem dictReprErr_otherList : ∀ l : List SigKey, dictReprErr (otherList l) = listReprErr l
  | [] => rfl
  | .sig s :: rest => by
    simp only [otherList, listReprErr, SigKey.reprErr]
    exact dictReprErr_otherList rest
  | .other r h :: rest => by
    cases r with
    | some e => simp [otherList, listReprErr, dictReprErr, SigKey.reprErr]
    | none =>
      simp only [otherList, listReprErr, dictReprErr, SigKey.reprErr]
      exact dictReprErr_otherList rest

theorem dictReprErr_sigs_append (b : Signal → Bool) (rest : List (SigKey × SigVal)) :
    dictReprErr (pySignals.map (fun s => (SigKey.sig s, ({ truth := b s } : SigVal))) ++ rest) =
      dictReprErr rest := by
  simp [pySignals, dictReprErr, SigKey.reprErr]

theorem hasOther_otherList : ∀ l : List SigKey, (∃ k ∈ l, k.isSig = false) →
    hasOther (otherList l) = true
  | [], ⟨k, hk, _⟩ => by simp at hk
  | .sig s :: rest, ⟨k, hk, hs⟩ => by
    simp only [List.mem_cons] at hk
    rcases hk with rfl | hk
    · simp [SigKey.isSig] at hs
    · simp only [otherList]
      exact hasOther_otherList rest ⟨k, hk, hs⟩
  | .other r h :: rest, _ => by simp [otherList, hasOther, SigKey.isSig]

theorem otherList_sigs : ∀ l : List SigKey, (∀ k ∈ l, k.isSig = true) → otherList l = []
  | [], _ => rfl
  | .sig s :: rest, h => by
    simp only [otherList]
    exact otherList_sigs rest (fun k hk => h k (by simp [hk]))
  | .other r hh :: rest, h => by simpa [SigKey.isSig] using h (.other r hh) (by simp)

theorem signalDictOf_valid (l : List SigKey) (h : ∀ k ∈ l, k.isSig = true) :
    signalDictOf l = .ok (keyed (pySignals.map (fun s => (s, l.contains (.sig s))))) := by
  have hh : ∀ x ∈ l, x.hashErr = none := fun x hx => by
    have := h x hx
    cases x with
    | sig s => rfl
    | other r e => simp [SigKey.isSig] at this
  simp only [signalDictOf, otherItems_ok l hh, otherList_sigs l h, keyed, List.map_map, List.append_nil,
    bind, Except.bind, pure, Except.pure]
  simp [Function.comp_def]

theorem sigArg_ok (dflt : List (SigKey × SigVal)) (t : SigArg) (h : t.valid) :
    ∃ d, signalArg dflt t.arg = .ok (.dict d) ∧ setSignalDict (.dict d) = .ok t.stored := by
  cases t with
  | list l =>
    refine ⟨keyed (pySignals.map (fun s => (s, l.contains (.sig s)))), ?_, ?_⟩
    · simp only [SigArg.arg, signalArg, signalDictOf_valid l h, bind, Except.bind, pure, Except.pure]
    · exact setSignalDict_keyed _ (listDict_total l)
  | dict d => exact ⟨d, rfl, setSignalDict_valid d h⟩

theorem dictKeyExc_spec (e : PyExc) :
    (∀ m, e = .typeError m → dictKeyExc e = .typeError s!"~cannot use as a dict key ({m})") ∧
    ((∀ m, e ≠ .typeError m) → dictKeyExc e = e) := by
  refine ⟨fun m hm => by subst hm; rfl, fun h => ?_⟩
  cases e with
  | typeError m => exact absurd rfl (h m)
  | _ => rfl

/-- A refused argument: the error comes from building the dict, or from `_set_signal_dict`. -/
theorem sigArg_bad (dflt : List (SigKey × SigVal)) (t : SigArg) (h : ¬ t.valid) :
    ∃ e, SigRefusal t e ∧ (signalArg dflt t.arg = .error e ∨
      ∃ d, signalArg dflt t.arg = .ok (.dict d) ∧ setSignalDict (.dict d) = .error e) := by
  cases t with
  | list l =>
    have hne : ∃ k ∈ l, k.isSig = false := by
      refine Classical.byContradiction fun hc => h (fun k hk => ?_)
      cases hs : k.isSig
      · exact absurd ⟨k, hk, hs⟩ hc
      · rfl
    by_cases hh : ∀ x ∈ l, x.hashErr = none
    · let D := pySignals.map (fun s => (SigKey.sig s, ({ truth := l.contains (.sig s) } : SigVal))) ++
        otherList l
      have hD : signalArg dflt (SigArg.list l).arg = .ok (.dict D) := by
        simp only [SigArg.arg, signalArg, signalDictOf, otherItems_ok l hh, bind, Except.bind, pure,
          Except.pure, D]
      have ho : hasOther D = true := by
        simp [D, hasOther, List.any_append]
        exact Or.inr (by simpa [hasOther] using hasOther_otherList l hne)
      refine ⟨_, ⟨fun pre k post e hl _ hk => ?_, fun _ => ⟨fun hp => ?_, fun e he => ?_⟩⟩,
        Or.inr ⟨D, hD, setSignalDict_bad D (Or.inl ho)⟩⟩
      · exact absurd (hh k (by simp [hl])) (by simp [hk])
      · simp [CtxArg.pct, pctExc, CtxArg.strErr, D, dictReprErr_sigs_append, dictReprErr_otherList,
          listReprErr_none l hp]
      · obtain ⟨pre, k, post, rfl, hp, hk⟩ := he
        simp [CtxArg.pct, pctExc, CtxArg.strErr, D, dictReprErr_sigs_append, dictReprErr_otherList,
          listReprErr_some e pre k post hp hk]
    · obtain ⟨pre, k, post, e, rfl, hp, hk⟩ := first_hash_err l hh
      have hE : signalArg dflt (SigArg.list (pre ++ k :: post)).arg = .error (dictKeyExc e) := by
        simp only [SigArg.arg, signalArg, signalDictOf, otherItems_err e pre k post hp hk, bind,
          Except.bind]
      refine ⟨_, ⟨fun pre' k' post' e' hl hp' hk' => ?_, fun hall => absurd hall hh⟩, Or.inl hE⟩
      have hE' := otherItems_err e' pre' k' post' hp' hk'
      rw [← hl, otherItems_err e pre k post hp hk] at hE'
      have heq : dictKeyExc e = dictKeyExc e' := by injection hE'
      rw [heq]
      exact dictKeyExc_spec e'
  | dict d =>
    have hb : hasOther d = true ∨ ∃ s, hasKey d (.sig s) = false := by
      by_cases ho : hasOther d = true
      · exact Or.inl ho
      · refine Or.inr (Classical.byContradiction fun hc => h ⟨by simpa using ho, fun s => ?_⟩)
        cases hs : hasKey d (.sig s)
        · exact absurd ⟨s, hs⟩ hc
        · rfl
    exact ⟨_, pct_spec (.dict d) _, Or.inr ⟨d, rfl, setSignalDict_bad d hb⟩⟩

/-- `signalArg` then `_set_signal_dict` on an accepted argument, or on none. -/
theorem sigStep (dflt : List (SigKey × SigVal)) (D : SigDict) (o : Option SigArg)
    (hD : setSignalDict (.dict dflt) = .ok D) (hv : ∀ t, o = some t → t.valid) :
    ∃ d, signalArg dflt (optSig o) = .ok (.dict d) ∧
      setSignalDict (.dict d) = .ok (SigArg.storedOr D o) := by
  cases o with
  | none => exact ⟨dflt, rfl, hD⟩
  | some t => exact sigArg_ok dflt t (hv t rfl)

theorem pySetattr_rounding_init (dc c : PyContext) (r : Option Rounding)
    (hro : ∀ id eq st, dc.roundingObj = some (id, eq, st) → eqIn eq roundingModes = .ok (some dc.rounding)) :
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
      obtain ⟨id, eq, st⟩ := x
      simp [pySetattr, hro id eq st h, bind, Except.bind, pure, Except.pure]

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
  have hR := fun c => pySetattr_rounding_init dc c r hro
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
    simp [orElseArg, pySetattr, hs, throw, throwThe, MonadExceptOf.throw, invalidRoundingExc,
      CtxArg.pct, pctExc, CtxArg.strErr, roundingMsg]
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
    obtain ⟨e, hs, hc⟩ := sigArg_bad (keyed dc.traps) t hb
    have g4 : ¬ (cap.getD dc.capitals < 0 ∨ cap.getD dc.capitals > 1) := by omega
    have g5 : ¬ (cl.getD dc.clamp < 0 ∨ cl.getD dc.clamp > 1) := by omega
    refine ⟨e, ?_, hs⟩
    rcases hc with e1 | ⟨dT, e1, e2⟩
    · simp only [pyContextNew, orElse_optInt, pySetattr_prec, if_neg (show ¬ p.getD dc.prec < 1 by omega),
        hR, pySetattr_emin, if_neg (show ¬ emin.getD dc.emin > 0 by omega), pySetattr_emax,
        if_neg (show ¬ emax.getD dc.emax < 0 by omega), pySetattr_capitals, if_neg g4, pySetattr_clamp,
        if_neg g5, pySetattr_ignored, optSig, e1, bind, Except.bind]
    · simp only [pyContextNew, orElse_optInt, pySetattr_prec, if_neg (show ¬ p.getD dc.prec < 1 by omega),
        hR, pySetattr_emin, if_neg (show ¬ emin.getD dc.emin > 0 by omega), pySetattr_emax,
        if_neg (show ¬ emax.getD dc.emax < 0 by omega), pySetattr_capitals, if_neg g4, pySetattr_clamp,
        if_neg g5, pySetattr_ignored, optSig, e1, pySetattr_traps, e2, bind, Except.bind]
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hI
    subst hf
    obtain ⟨dT, e1, e2⟩ := sigStep (keyed dc.traps) dc.traps tr hT0 hT
    obtain ⟨e, hs, hc⟩ := sigArg_bad (keyed (pySignals.map (fun s => (s, false)))) f hb
    have g4 : ¬ (cap.getD dc.capitals < 0 ∨ cap.getD dc.capitals > 1) := by omega
    have g5 : ¬ (cl.getD dc.clamp < 0 ∨ cl.getD dc.clamp > 1) := by omega
    refine ⟨e, ?_, hs⟩
    rcases hc with e3 | ⟨dF, e3, e4⟩
    · have e3' : signalArg (keyed (pySignals.map (fun s => (s, false)))) (optSig (some f)) =
        .error e := e3
      simp only [pyContextNew, orElse_optInt, pySetattr_prec, if_neg (show ¬ p.getD dc.prec < 1 by omega),
        hR, pySetattr_emin, if_neg (show ¬ emin.getD dc.emin > 0 by omega), pySetattr_emax,
        if_neg (show ¬ emax.getD dc.emax < 0 by omega), pySetattr_capitals, if_neg g4, pySetattr_clamp,
        if_neg g5, pySetattr_ignored, e1, pySetattr_traps, e2, e3', bind,
        Except.bind, pure, Except.pure]
    · have e3' : signalArg (keyed (pySignals.map (fun s => (s, false)))) (optSig (some f)) =
        .ok (.dict dF) := e3
      simp only [pyContextNew, orElse_optInt, pySetattr_prec, if_neg (show ¬ p.getD dc.prec < 1 by omega),
        hR, pySetattr_emin, if_neg (show ¬ emin.getD dc.emin > 0 by omega), pySetattr_emax,
        if_neg (show ¬ emax.getD dc.emax < 0 by omega), pySetattr_capitals, if_neg g4, pySetattr_clamp,
        if_neg g5, pySetattr_ignored, e1, pySetattr_traps, e2, e3', pySetattr_flags, e4, bind,
        Except.bind, pure, Except.pure]
  · simp only [pyContextNew, orElse_ne v _ hn, pySetattr_prec_type _ v hv, bind, Except.bind]

end PyLean.Decimal
