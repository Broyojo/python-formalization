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

/-! ## `x in seq` and `_set_signal_dict`, stated without the model's functions -/

/-- The first answer that is not `no`, or `no` when every one is: what `x in seq` gives when its
comparisons with the items of `seq` answer `as`, in order. -/
def firstAns : List EqAns → EqAns
  | [] => .no
  | .no :: rest => firstAns rest
  | a :: _ => a

/-- An answer that is not an exception. -/
def NotRaise (a : EqAns) : Prop := ∀ e, a ≠ .raises e

/-- What `k in _signals` answers (_pydecimal.py:4023): `signal == k` for each signal in order. -/
def KeyIn (k : SigKey) : EqAns := firstAns (pySignals.map k.eqSig)

/-- `_set_signal_dict(name, d)` on a dict `d` (_pydecimal.py:4019-4028), outcome by outcome, `r`
being its result and `K` what holds of the dict it stores (its signal entries, its other keys).
The keys are searched for in `_signals` in insertion order (:4022-4024): the first whose `__eq__`
raises raises that exception, and the first equal to no signal raises what
`raise KeyError("%s is not a valid signal dict" % d)` raises (`PctRaises`: the `KeyError`, or the
exception `repr()` of a key or value raises). When every key equals some signal, a signal that is
not a key raises the same (:4025-4027); otherwise `d` is stored, with any key that is not a signal
but compared equal to one. -/
def DictOutcome {α : Type} (d : List (SigKey × SigVal)) (r : Py α)
    (K : SigDict → List (SigKey × SigVal) → Prop) : Prop :=
  (∀ pre k v post e, d = pre ++ (k, v) :: post → (∀ p ∈ pre, KeyIn p.1 = .yes) →
    KeyIn k = .raises e → r = .error e) ∧
  (∀ pre k v post, d = pre ++ (k, v) :: post → (∀ p ∈ pre, KeyIn p.1 = .yes) → KeyIn k = .no →
    ∃ x, r = .error x ∧ PctRaises (.dict d) (.keyError "~is not a valid signal dict") x) ∧
  ((∀ p ∈ d, KeyIn p.1 = .yes) → (∃ s, ∀ v, (SigKey.sig s, v) ∉ d) →
    ∃ x, r = .error x ∧ PctRaises (.dict d) (.keyError "~is not a valid signal dict") x) ∧
  ((∀ p ∈ d, KeyIn p.1 = .yes) → (∀ s, ∃ v, (SigKey.sig s, v) ∈ d) →
    K (sigEntries d) (extrasOf d))

theorem ansIn_first : ∀ as : List EqAns, ansIn as =
    match firstAns as with
    | .yes => .ok true
    | .no => .ok false
    | .raises e => .error e
  | [] => rfl
  | .yes :: _ => rfl
  | .no :: rest => by simp only [ansIn, firstAns]; exact ansIn_first rest
  | .raises _ :: _ => rfl

theorem ansIn_ok_of (as : List EqAns) (h : NotRaise (firstAns as)) :
    ansIn as = .ok (decide (firstAns as = .yes)) := by
  rw [ansIn_first]
  cases hf : firstAns as with
  | yes => rfl
  | no => rfl
  | raises e => exact absurd hf (h e)

theorem ansIn_err_of (as : List EqAns) (e : PyExc) (h : firstAns as = .raises e) :
    ansIn as = .error e := by
  rw [ansIn_first, h]

theorem keyIn_yes {k : SigKey} (h : KeyIn k = .yes) : ansIn (pySignals.map k.eqSig) = .ok true := by
  have h' : firstAns (pySignals.map k.eqSig) = .yes := h
  rw [ansIn_first, h']

theorem keyIn_no {k : SigKey} (h : KeyIn k = .no) : ansIn (pySignals.map k.eqSig) = .ok false := by
  have h' : firstAns (pySignals.map k.eqSig) = .no := h
  rw [ansIn_first, h']

theorem keyIn_raises {k : SigKey} {e : PyExc} (h : KeyIn k = .raises e) :
    ansIn (pySignals.map k.eqSig) = .error e := by
  have h' : firstAns (pySignals.map k.eqSig) = .raises e := h
  rw [ansIn_first, h']

theorem checkKeys_cons_yes (fmt : PyExc) (k : SigKey) (v : SigVal) (rest : List (SigKey × SigVal))
    (h : KeyIn k = .yes) : checkKeys fmt ((k, v) :: rest) = checkKeys fmt rest := by
  simp [checkKeys, keyIn_yes h, bind, Except.bind, pure, Except.pure]

theorem checkKeys_cons_no (fmt : PyExc) (k : SigKey) (v : SigVal) (rest : List (SigKey × SigVal))
    (h : KeyIn k = .no) : checkKeys fmt ((k, v) :: rest) = .error fmt := by
  simp [checkKeys, keyIn_no h, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

theorem checkKeys_cons_raises (fmt e : PyExc) (k : SigKey) (v : SigVal) (rest : List (SigKey × SigVal))
    (h : KeyIn k = .raises e) : checkKeys fmt ((k, v) :: rest) = .error e := by
  simp [checkKeys, keyIn_raises h, bind, Except.bind]

theorem checkKeys_pre (fmt : PyExc) : ∀ (pre rest : List (SigKey × SigVal)),
    (∀ p ∈ pre, KeyIn p.1 = .yes) → checkKeys fmt (pre ++ rest) = checkKeys fmt rest
  | [], rest, _ => rfl
  | (k, v) :: pre, rest, h => by
    rw [List.cons_append, checkKeys_cons_yes fmt k v _ (h (k, v) (by simp))]
    exact checkKeys_pre fmt pre rest (fun p hp => h p (by simp [hp]))

theorem checkKeys_all (fmt : PyExc) (d : List (SigKey × SigVal)) (h : ∀ p ∈ d, KeyIn p.1 = .yes) :
    checkKeys fmt d = .ok () := by
  have := checkKeys_pre fmt d [] h
  simpa [checkKeys] using this

theorem hasKey_iff (d : List (SigKey × SigVal)) (s : Signal) :
    hasKey d (.sig s) = true ↔ ∃ v, (SigKey.sig s, v) ∈ d := by
  unfold hasKey
  rw [List.any_eq_true]
  constructor
  · rintro ⟨⟨k, v⟩, hm, hk⟩
    have : k = .sig s := by simpa using hk
    subst this
    exact ⟨v, hm⟩
  · rintro ⟨v, hm⟩
    exact ⟨(.sig s, v), hm, by simp⟩

/-- The model's `_set_signal_dict` on a dict has every outcome `DictOutcome` states. -/
theorem setSignalDict_outcome (d : List (SigKey × SigVal)) :
    DictOutcome d (setSignalDict (.dict d)) (fun T X => setSignalDict (.dict d) = .ok (T, X)) := by
  refine ⟨fun pre k v post e hd hp hk => ?_, fun pre k v post hd hp hk => ?_, fun hall hs => ?_,
    fun hall hs => ?_⟩
  · subst hd
    simp only [setSignalDict, checkKeys_pre _ pre _ hp, checkKeys_cons_raises _ e k v post hk, bind,
      Except.bind]
  · subst hd
    refine ⟨_, ?_, pct_spec _ _⟩
    simp only [setSignalDict, checkKeys_pre _ pre _ hp, checkKeys_cons_no _ k v post hk, bind,
      Except.bind]
  · refine ⟨_, ?_, pct_spec (.dict d) _⟩
    obtain ⟨s, hs⟩ := hs
    have h1 : pySignals.all (fun s => hasKey d (.sig s)) = false := by
      rw [List.all_eq_false]
      refine ⟨s, pySignals_mem s, fun hh => ?_⟩
      obtain ⟨v, hv⟩ := (hasKey_iff d s).1 hh
      exact hs v hv
    simp [setSignalDict, checkKeys_all _ d hall, h1, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw]
  · have h1 : pySignals.all (fun s => hasKey d (.sig s)) = true := by
      rw [List.all_eq_true]
      intro s _
      exact (hasKey_iff d s).2 (hs s)
    simp [setSignalDict, checkKeys_all _ d hall, h1, bind, Except.bind, pure, Except.pure]

theorem DictOutcome.bind {α : Type} {d : List (SigKey × SigVal)}
    {m : Py (SigDict × List (SigKey × SigVal))} {f : SigDict × List (SigKey × SigVal) → Py α}
    (h : DictOutcome d m (fun T X => m = .ok (T, X))) :
    DictOutcome d (m >>= f) (fun T X => (m >>= f) = f (T, X)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun pre k v post e hd hp hk => ?_, fun pre k v post hd hp hk => ?_, fun ha hs => ?_,
    fun ha hs => ?_⟩
  · rw [h1 pre k v post e hd hp hk]; try rfl
  · obtain ⟨x, hx, hpx⟩ := h2 pre k v post hd hp hk
    exact ⟨x, by rw [hx]; try rfl, hpx⟩
  · obtain ⟨x, hx, hpx⟩ := h3 ha hs
    exact ⟨x, by rw [hx]; try rfl, hpx⟩
  · rw [h4 ha hs]; try rfl

theorem DictOutcome.mono {α : Type} {d : List (SigKey × SigVal)} {r : Py α}
    {K K' : SigDict → List (SigKey × SigVal) → Prop}
    (h : DictOutcome d r K) (hk : ∀ T X, K T X → K' T X) : DictOutcome d r K' :=
  ⟨h.1, h.2.1, h.2.2.1, fun a b => hk _ _ (h.2.2.2 a b)⟩

/-! ## `__setattr__`, `_set_integer_check`, `_set_signal_dict` -/

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
* `flags` and `traps` given a dict have every outcome of `DictOutcome` (:4019-4028): each key is
  searched for in `_signals` with `==`, so a key whose `__eq__` raises raises that exception
  (`Context().traps = {k: 1}`), a key equal to no signal raises what
  `raise KeyError("%s is not a valid signal dict" % d)` raises (the `KeyError`, or the exception
  `repr()` of the first key or value that does not print raises: `{10**5000: 1}`,
  `{Clamped: 10**5000, ...}`), as does a missing signal, and otherwise the dict is stored, a key
  that is not a signal but compared equal to one included (the nine signals plus such a key are
  accepted); anything else raises what `raise TypeError("%s must be a signal dict" % d)` raises;
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
    (∀ d, DictOutcome d (pySetattr c "flags" (.dict d))
        (fun T X => pySetattr c "flags" (.dict d) = .ok { c with flags := T, flagsExtra := X }) ∧
      DictOutcome d (pySetattr c "traps" (.dict d))
        (fun T X => pySetattr c "traps" (.dict d) = .ok { c with traps := T, trapsExtra := X })) ∧
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
    fun id eq st hp => ?_, ?_, ?_, ?_, ?_, fun hv => ?_, fun d => ?_,
    fun hv => ?_, fun l => ?_, fun name hn => ?_⟩
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
  · refine ⟨?_, ?_⟩
    · rw [pySetattr_flags]; exact DictOutcome.bind (setSignalDict_outcome d)
    · rw [pySetattr_traps]; exact DictOutcome.bind (setSignalDict_outcome d)
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

/-- What `hash()` of an element raises (`none`: it is hashable); a signal is a class. -/
def SigKey.hashErr : SigKey → StrErr
  | .sig _ => none
  | .other _ h _ => h

/-- What `s in l` answers for a signal `s` (`int(s in traps)`, _pydecimal.py:3994): the elements'
comparisons with `s`, in order. -/
def SigAns (l : List SigKey) (s : Signal) : EqAns := firstAns (l.map (fun x : SigKey => x.eqSig s))

/-- What `k in l` answers for an element `k` before it reaches itself, `pre` the elements before
it: a signal `t` among them answers through `k`'s reflected `__eq__`, another non-signal element is
unequal (scope of `SigKey.other`). -/
def SelfAns (pre : List SigKey) (k : SigKey) : EqAns := firstAns (pre.map k.ansBefore)

/-- An element `dict(...)` takes in: its `k in l` does not raise and it hashes. -/
def ElemOk (pre : List SigKey) (k : SigKey) : Prop := NotRaise (SelfAns pre k) ∧ k.hashErr = none

/-- An element on which `dict(...)` stops with `r`: its `k in l` raises `r`, or it is hashed and
`hash()` raises, a `TypeError` becoming "cannot use '<type>' as a dict key (<e>)" and anything else
propagating (Objects/dictobject.c:2442-2461). -/
def ElemFails (pre : List SigKey) (k : SigKey) (r : PyExc) : Prop :=
  SelfAns pre k = .raises r ∨
  (NotRaise (SelfAns pre k) ∧ ∃ h, k.hashErr = some h ∧
    (∀ m, h = .typeError m → r = .typeError s!"~cannot use as a dict key ({m})") ∧
    ((∀ m, h ≠ .typeError m) → r = h))

/-- The items the elements of `l` that are not signals add, each with the value `1`. -/
def otherList : List SigKey → List (SigKey × SigVal)
  | [] => []
  | .sig _ :: rest => otherList rest
  | .other r _ eq :: rest => (.other r none eq, { truth := true }) :: otherList rest

/-- `dict((s, int(s in l)) for s in _signals + l)` when nothing raises: the nine signals, each set
when `s in l` is true, then the other elements. -/
def ListBuilt (l : List SigKey) : List (SigKey × SigVal) :=
  pySignals.map (fun s => (SigKey.sig s, ({ truth := decide (SigAns l s = .yes) } : SigVal))) ++
    otherList l

/-- `Context()` with the list `l` as `traps` or `flags` (_pydecimal.py:3993-3994, :4000-4001), `r`
being the result and `K` what holds of the stored dict: `dict(...)` takes the signals first, in
`_signals` order, and the first whose `s in l` raises raises that; then the elements in order, the
first that fails (`ElemFails`) raising its exception; then the dict goes to `_set_signal_dict`
(`DictOutcome`). -/
def ListOutcome {α : Type} (l : List SigKey) (r : Py α)
    (K : SigDict → List (SigKey × SigVal) → Prop) : Prop :=
  (∀ pre s post e, pySignals = pre ++ s :: post → (∀ t ∈ pre, NotRaise (SigAns l t)) →
    SigAns l s = .raises e → r = .error e) ∧
  ((∀ s, NotRaise (SigAns l s)) → ∀ pre k post e, l = pre ++ k :: post →
    (∀ pre1 k1 post1, pre = pre1 ++ k1 :: post1 → ElemOk pre1 k1) → ElemFails pre k e → r = .error e) ∧
  ((∀ s, NotRaise (SigAns l s)) → (∀ pre k post, l = pre ++ k :: post → ElemOk pre k) →
    DictOutcome (ListBuilt l) r K)

def SigOutcome {α : Type} : SigArg → Py α → (SigDict → List (SigKey × SigVal) → Prop) → Prop
  | .list l, r, K => ListOutcome l r K
  | .dict d, r, K => DictOutcome d r K

/-- An optional argument: when it is not given, the dict `D` with the other keys `X` is stored. -/
def SigOutcomeOpt {α : Type} (D : SigDict) (X : List (SigKey × SigVal)) :
    Option SigArg → Py α → (SigDict → List (SigKey × SigVal) → Prop) → Prop
  | none, _, K => K D X
  | some t, r, K => SigOutcome t r K

/-- A value that is neither a list nor a dict, given. -/
def NotSigArg (v : CtxArg) : Prop := v ≠ .none ∧ (∀ l, v ≠ .list l) ∧ ∀ d, v ≠ .dict d

/-- `Context(prec, rounding, Emin, Emax, capitals, clamp, flags, traps, _ignored_flags)`
(_pydecimal.py:3969-4003) with ints, rounding modes, `_ignored_flags` a list of signals, and
`flags` and `traps` lists or dicts, for every `DefaultContext` (a context: its `traps` has every
signal, any other key it holds compares equal to a signal, and a non-str `rounding` it holds
compares equal to the mode stored with it, as `__setattr__` checked when they were assigned). An
argument that is not given (or `None`) is taken from `DefaultContext` (`dc.traps.copy()`, other
keys included), except `flags`, which start clear, and `_ignored_flags`, which starts empty. The
attributes are assigned in the order `prec`, `rounding`, `Emin`, `Emax`, `capitals`, `clamp`,
`_ignored_flags`, `traps`, `flags`, and the first refused value raises: the `ValueError` of
`_set_integer_check` (the int/str-limit `ValueError` when its `%s` has more than 4300 digits), the
`TypeError` of an unknown rounding name, the `TypeError` of a `prec` that is not an int, and for
`traps` then `flags` every outcome of `ListOutcome` (a list: `s in l` and `k in l` run the
elements' `__eq__`, so `Context(traps=[k])` raises what `k.__eq__` raises, or with a `k` equal to
every signal traps every signal and keeps `k`; then hashing) or `DictOutcome` (a dict); any other
value fails at `_signals + value` with `TypeError`. When every value is accepted the context holds
exactly these values. -/
def ContextInitExact : Prop :=
  ∀ (dc : PyContext) (p emin emax cap cl : Option Int) (r : Option Rounding)
    (ig : Option (List Signal)) (fl tr : Option SigArg),
    (∀ s, (dc.traps.lookup s).isSome) →
    (∀ q ∈ dc.trapsExtra, q.1.isSig = false ∧ KeyIn q.1 = .yes) →
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
    let RO : Option (Nat × List EqAns × StrErr) := match r with
      | none => dc.roundingObj
      | some _ => none
    (IntsOk →
      SigOutcomeOpt dc.traps dc.trapsExtra tr (pyContextNew dc a) (fun T X =>
        SigOutcomeOpt (pySignals.map (fun s => (s, false))) [] fl (pyContextNew dc a) (fun F Y =>
          pyContextNew dc a = .ok
            { prec := P, rounding := r.getD dc.rounding, emin := Em, emax := EM, capitals := Ca,
              clamp := Cl, flags := F, traps := T, ignored := ig.getD [], roundingObj := RO,
              flagsExtra := Y, trapsExtra := X }))) ∧
    (IntsOk → ∀ v, NotSigArg v →
      pyContextNew dc { a with traps := v } = .error (.typeError "~can only concatenate list to list")) ∧
    (IntsOk → ∀ v, NotSigArg v →
      SigOutcomeOpt dc.traps dc.trapsExtra tr (pyContextNew dc { a with flags := v }) (fun _ _ =>
        pyContextNew dc { a with flags := v } = .error (.typeError "~can only concatenate list to list"))) ∧
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
    (∀ v, intValue v = none → v ≠ .none →
      pyContextNew dc { a with prec := v } = .error (.typeError "prec must be an integer"))

theorem orElse_optInt (o : Option Int) (d : Int) : orElseArg (optInt o) (.int d) = .int (o.getD d) := by
  cases o <;> rfl

theorem orElse_ne (v d : CtxArg) (h : v ≠ .none) : orElseArg v d = v := by
  cases v <;> simp_all [orElseArg]

theorem clearDict0_keyed :
    setSignalDict (.dict (keyed (pySignals.map (fun s => (s, false))))) =
      .ok (pySignals.map (fun s => (s, false)), []) :=
  setSignalDict_keyed _ clearDict0_total

theorem dictKeyExc_spec (e : PyExc) :
    (∀ m, e = .typeError m → dictKeyExc e = .typeError s!"~cannot use as a dict key ({m})") ∧
    ((∀ m, e ≠ .typeError m) → dictKeyExc e = e) := by
  refine ⟨fun m hm => by subst hm; rfl, fun h => ?_⟩
  cases e with
  | typeError m => exact absurd rfl (h m)
  | _ => rfl

theorem firstAns_noRaise : ∀ as : List EqAns, (∀ a ∈ as, NotRaise a) → NotRaise (firstAns as)
  | [], _ => fun e h => nomatch h
  | .yes :: _, _ => fun e h => nomatch h
  | .no :: rest, h => by
    simp only [firstAns]
    exact firstAns_noRaise rest (fun a ha => h a (by simp [ha]))
  | .raises e :: _, h => absurd rfl (h (.raises e) (by simp) e)

/-- A signal element never makes `dict(...)` stop. -/
theorem elemOk_sig (pre : List SigKey) (s : Signal) : ElemOk pre (.sig s) := by
  refine ⟨firstAns_noRaise _ (fun a ha => ?_), rfl⟩
  simp only [List.mem_map] at ha
  obtain ⟨x, _, rfl⟩ := ha
  cases x with
  | sig t =>
    show NotRaise ((SigKey.sig s).eqSig t)
    simp only [SigKey.eqSig]
    split <;> exact fun e h => nomatch h
  | other r h eq =>
    show NotRaise EqAns.no
    exact fun e h => nomatch h

theorem sigItems_ok (l : List SigKey) : ∀ ss : List Signal, (∀ s ∈ ss, NotRaise (SigAns l s)) →
    sigItems l ss =
      .ok (ss.map (fun s => (SigKey.sig s, ({ truth := decide (SigAns l s = .yes) } : SigVal))))
  | [], _ => rfl
  | s :: rest, h => by
    have ha := ansIn_ok_of (l.map (fun x : SigKey => x.eqSig s)) (h s (by simp))
    have hr := sigItems_ok l rest (fun t ht => h t (by simp [ht]))
    simp only [sigItems, ha, hr, bind, Except.bind, pure, Except.pure, List.map_cons]
    rfl

theorem sigItems_err (l : List SigKey) (e : PyExc) : ∀ (pre : List Signal) (s : Signal) (post : List Signal),
    (∀ t ∈ pre, NotRaise (SigAns l t)) → SigAns l s = .raises e →
    sigItems l (pre ++ s :: post) = .error e
  | [], s, post, _, hs => by
    simp only [List.nil_append, sigItems, ansIn_err_of _ e hs, bind, Except.bind]
  | t :: pre, s, post, hp, hs => by
    have ha := ansIn_ok_of (l.map (fun x : SigKey => x.eqSig t)) (hp t (by simp))
    simp only [List.cons_append, sigItems, ha, sigItems_err l e pre s post (fun x hx => hp x (by simp [hx])) hs,
      bind, Except.bind]

theorem selfIn_ok (k : SigKey) (pre : List SigKey) (h : NotRaise (SelfAns pre k)) :
    selfIn k pre = .ok () := by
  simp only [selfIn, ansIn_ok_of _ h, bind, Except.bind, pure, Except.pure]

theorem selfIn_err (k : SigKey) (pre : List SigKey) (e : PyExc) (h : SelfAns pre k = .raises e) :
    selfIn k pre = .error e := by
  simp only [selfIn, ansIn_err_of _ e h, bind, Except.bind]

theorem otherItems_ok : ∀ (l acc : List SigKey),
    (∀ pre k post, l = pre ++ k :: post → ElemOk (acc ++ pre) k) → otherItems acc l = .ok (otherList l)
  | [], _, _ => rfl
  | .sig t :: rest, acc, h => by
    simp only [otherItems, otherList]
    exact otherItems_ok rest (acc ++ [.sig t]) (fun pre k post hl => by
      have := h (.sig t :: pre) k post (by simp [hl])
      simpa using this)
  | .other r hh eq :: rest, acc, h => by
    have h0 := h [] (.other r hh eq) rest (by simp)
    simp only [List.append_nil] at h0
    obtain ⟨h1, h2⟩ := h0
    have h2' : hh = none := h2
    subst h2'
    have ih := otherItems_ok rest (acc ++ [.other r none eq]) (fun pre k post hl => by
      have := h (.other r none eq :: pre) k post (by simp [hl])
      simpa using this)
    simp only [otherItems, otherList, selfIn_ok _ _ h1, ih, bind, Except.bind, pure, Except.pure]

theorem otherItems_err (e : PyExc) : ∀ (pre acc : List SigKey) (k : SigKey) (post : List SigKey),
    (∀ pre1 k1 post1, pre = pre1 ++ k1 :: post1 → ElemOk (acc ++ pre1) k1) →
    ElemFails (acc ++ pre) k e → otherItems acc (pre ++ k :: post) = .error e
  | [], acc, .sig t, post, _, hf => by
    exfalso
    obtain ⟨hn, hh⟩ := elemOk_sig (acc ++ []) t
    rcases hf with hf | ⟨_, h, hh', _⟩
    · exact hn e hf
    · rw [hh] at hh'; exact nomatch hh'
  | [], acc, .other r hh eq, post, _, hf => by
    simp only [List.append_nil] at hf
    rcases hf with hf | ⟨hn, h, hh', h1, h2⟩
    · simp only [List.nil_append, otherItems, selfIn_err _ _ e hf, bind, Except.bind]
    · have hh'' : hh = some h := hh'
      subst hh''
      simp only [List.nil_append, otherItems, selfIn_ok _ _ hn, bind, Except.bind]
      by_cases ht : ∃ m, h = .typeError m
      · obtain ⟨m, hm⟩ := ht
        rw [(dictKeyExc_spec h).1 m hm, h1 m hm]
      · have hn' : ∀ m, h ≠ .typeError m := fun m hm => ht ⟨m, hm⟩
        rw [(dictKeyExc_spec h).2 hn', h2 hn']
  | x :: pre, acc, k, post, hp, hf => by
    have h0 := hp [] x pre (by simp)
    simp only [List.append_nil] at h0
    have ih := otherItems_err e pre (acc ++ [x]) k post (fun pre1 k1 post1 hl => by
      have := hp (x :: pre1) k1 post1 (by simp [hl])
      simpa using this) (by simpa using hf)
    cases x with
    | sig t =>
      simp only [List.cons_append, otherItems]
      exact ih
    | other r hh eq =>
      obtain ⟨h1, h2⟩ := h0
      have h2' : hh = none := h2
      subst h2'
      simp only [List.cons_append, otherItems, selfIn_ok _ _ h1, ih, bind, Except.bind]

/-- `signalArg` then `_set_signal_dict` on a list or dict argument, then `g`, has every outcome
`SigOutcome` states. -/
theorem sigArg_outcome {α : Type} (dflt : List (SigKey × SigVal)) (t : SigArg)
    (g : SigDict × List (SigKey × SigVal) → Py α) :
    SigOutcome t (signalArg dflt t.arg >>= fun v => setSignalDict v >>= g)
      (fun T X => (signalArg dflt t.arg >>= fun v => setSignalDict v >>= g) = g (T, X)) := by
  cases t with
  | dict d =>
    have e : (signalArg dflt (SigArg.dict d).arg >>= fun v => setSignalDict v >>= g) =
        (setSignalDict (.dict d) >>= g) := rfl
    simp only [SigOutcome]
    rw [e]
    exact DictOutcome.bind (setSignalDict_outcome d)
  | list l =>
    simp only [SigOutcome]
    refine ⟨fun pre s post e hps hp hs => ?_, fun hs pre k post e hl hp hf => ?_, fun hs he => ?_⟩
    · have : sigItems l pySignals = .error e := by rw [hps]; exact sigItems_err l e pre s post hp hs
      simp only [SigArg.arg, signalArg, signalDictOf, this, bind, Except.bind]
    · have h1 := sigItems_ok l pySignals (fun s _ => hs s)
      have h2 : otherItems [] l = .error e := by
        rw [hl]
        exact otherItems_err e pre [] k post (fun pre1 k1 post1 hq => by simpa using hp pre1 k1 post1 hq)
          (by simpa using hf)
      simp only [SigArg.arg, signalArg, signalDictOf, h1, h2, bind, Except.bind]
    · have h1 := sigItems_ok l pySignals (fun s _ => hs s)
      have h2 := otherItems_ok l [] (fun pre k post hq => by simpa using he pre k post hq)
      have e : (signalArg dflt (SigArg.list l).arg >>= fun v => setSignalDict v >>= g) =
          (setSignalDict (.dict (ListBuilt l)) >>= g) := by
        simp only [SigArg.arg, signalArg, signalDictOf, h1, h2, bind, Except.bind, pure, Except.pure,
          ListBuilt]
      rw [e]
      exact DictOutcome.bind (setSignalDict_outcome _)

theorem SigOutcome.mono {α : Type} {t : SigArg} {r : Py α} {K K' : SigDict → List (SigKey × SigVal) → Prop}
    (h : SigOutcome t r K) (hk : ∀ T X, K T X → K' T X) : SigOutcome t r K' := by
  cases t with
  | dict d => exact DictOutcome.mono h hk
  | list l => exact ⟨h.1, h.2.1, fun a b => DictOutcome.mono (h.2.2 a b) hk⟩

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

theorem ok_bind {α β : Type} (x : α) (f : α → Py β) : (Except.ok x >>= f) = f x := rfl

/-- The context `Context()` builds from accepted values (a proof device; `ContextInitExact` writes
it out). -/
def builtCtx (dc : PyContext) (p emin emax cap cl : Option Int) (r : Option Rounding)
    (ig : Option (List Signal)) (T : SigDict) (X : List (SigKey × SigVal)) (F : SigDict)
    (Y : List (SigKey × SigVal)) : PyContext :=
  { prec := p.getD dc.prec, rounding := r.getD dc.rounding, emin := emin.getD dc.emin,
    emax := emax.getD dc.emax, capitals := cap.getD dc.capitals, clamp := cl.getD dc.clamp,
    flags := F, traps := T, ignored := ig.getD [],
    roundingObj := (match r with
      | none => dc.roundingObj
      | some _ => none),
    flagsExtra := Y, trapsExtra := X }

/-- Under accepted ints, `Context()` comes down to its `traps` and `flags` steps. -/
theorem pyContextNew_sigs (dc : PyContext) (p emin emax cap cl : Option Int) (r : Option Rounding)
    (ig : Option (List Signal)) (trA flA : CtxArg)
    (hro : ∀ id eq st, dc.roundingObj = some (id, eq, st) → eqIn eq roundingModes = .ok (some dc.rounding))
    (h1 : 1 ≤ p.getD dc.prec) (h2 : emin.getD dc.emin ≤ 0) (h3 : 0 ≤ emax.getD dc.emax)
    (h4 : cap.getD dc.capitals = 0 ∨ cap.getD dc.capitals = 1)
    (h5 : cl.getD dc.clamp = 0 ∨ cl.getD dc.clamp = 1) :
    pyContextNew dc
        { prec := optInt p, rounding := optRound r, emin := optInt emin,
          emax := optInt emax, capitals := optInt cap, clamp := optInt cl, flags := flA, traps := trA,
          ignored := ig } =
      (signalArg (keyed dc.traps ++ dc.trapsExtra) trA >>= fun v => setSignalDict v >>= fun d =>
        signalArg (keyed (pySignals.map (fun s => (s, false)))) flA >>= fun w =>
          setSignalDict w >>= fun d' =>
            .ok (builtCtx dc p emin emax cap cl r ig d.1 d.2 d'.1 d'.2)) := by
  have g1 : ¬ p.getD dc.prec < 1 := by omega
  have g2 : ¬ emin.getD dc.emin > 0 := by omega
  have g3 : ¬ emax.getD dc.emax < 0 := by omega
  have g4 : ¬ (cap.getD dc.capitals < 0 ∨ cap.getD dc.capitals > 1) := by omega
  have g5 : ¬ (cl.getD dc.clamp < 0 ∨ cl.getD dc.clamp > 1) := by omega
  have hR := fun c => pySetattr_rounding_init dc c r hro
  simp only [pyContextNew, orElse_optInt, pySetattr_prec, if_neg g1, hR,
    pySetattr_emin, if_neg g2, pySetattr_emax, if_neg g3, pySetattr_capitals, if_neg g4, pySetattr_clamp,
    if_neg g5, pySetattr_ignored, pySetattr_traps, pySetattr_flags, ok_bind, bind_assoc, pure_bind]
  rfl

theorem contextInitExact_proven : ContextInitExact := by
  intro dc p emin emax cap cl r ig fl tr htr hxt hro
  dsimp only
  have hR := fun c => pySetattr_rounding_init dc c r hro
  have hx : ExtrasOk dc.trapsExtra := fun q hq => ⟨(hxt q hq).1, keyIn_yes (hxt q hq).2⟩
  have hT0 := setSignalDict_keyed_extra dc.traps dc.trapsExtra htr hx
  refine ⟨fun hI => ?_, fun hI v hv => ?_, fun hI v hv => ?_, fun h => ?_, fun s hs h1 => ?_,
    fun h1 h2 => ?_, fun h1 h2 h3 => ?_, fun h1 h2 h3 h4 => ?_, fun h1 h2 h3 h4 h5 => ?_,
    fun v hv hn => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hI
    rw [pyContextNew_sigs dc p emin emax cap cl r ig _ _ hro h1 h2 h3 h4 h5]
    -- the flags step, for the dict the traps step stored
    have hF : ∀ T X, SigOutcomeOpt (pySignals.map (fun s => (s, false))) [] fl
        (signalArg (keyed (pySignals.map (fun s => (s, false)))) (optSig fl) >>= fun w =>
          setSignalDict w >>= fun d' =>
            (Except.ok (builtCtx dc p emin emax cap cl r ig T X d'.1 d'.2) : Py PyContext))
        (fun F Y =>
          (signalArg (keyed (pySignals.map (fun s => (s, false)))) (optSig fl) >>= fun w =>
            setSignalDict w >>= fun d' =>
              (Except.ok (builtCtx dc p emin emax cap cl r ig T X d'.1 d'.2) : Py PyContext)) =
            .ok (builtCtx dc p emin emax cap cl r ig T X F Y)) := by
      intro T X
      cases fl with
      | none => simp only [SigOutcomeOpt, optSig, signalArg, clearDict0_keyed, ok_bind]
      | some f => exact SigOutcome.mono (sigArg_outcome _ f _) (fun F Y h => h)
    cases tr with
    | none =>
      have e0 : signalArg (keyed dc.traps ++ dc.trapsExtra) (optSig none) = .ok (.dict (keyed dc.traps ++ dc.trapsExtra)) := rfl
      simp only [SigOutcomeOpt, e0, ok_bind, hT0]
      exact hF dc.traps dc.trapsExtra
    | some t =>
      simp only [SigOutcomeOpt, optSig]
      refine SigOutcome.mono (sigArg_outcome _ t _) (fun T X hTX => ?_)
      rw [hTX]
      exact hF T X
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hI
    obtain ⟨hv1, hv2, hv3⟩ := hv
    have hs : signalArg (keyed dc.traps ++ dc.trapsExtra) v =
        .error (.typeError "~can only concatenate list to list") := by
      cases v with
      | none => exact absurd rfl hv1
      | list l => exact absurd rfl (hv2 l)
      | dict d => exact absurd rfl (hv3 d)
      | _ => rfl
    rw [pyContextNew_sigs dc p emin emax cap cl r ig _ _ hro h1 h2 h3 h4 h5, hs]
    rfl
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hI
    obtain ⟨hv1, hv2, hv3⟩ := hv
    have hs : signalArg (keyed (pySignals.map (fun s => (s, false)))) v =
        .error (.typeError "~can only concatenate list to list") := by
      cases v with
      | none => exact absurd rfl hv1
      | list l => exact absurd rfl (hv2 l)
      | dict d => exact absurd rfl (hv3 d)
      | _ => rfl
    rw [pyContextNew_sigs dc p emin emax cap cl r ig _ _ hro h1 h2 h3 h4 h5]
    cases tr with
    | none =>
      have e0 : signalArg (keyed dc.traps ++ dc.trapsExtra) (optSig none) = .ok (.dict (keyed dc.traps ++ dc.trapsExtra)) := rfl
      simp only [SigOutcomeOpt, e0, ok_bind, hT0, hs]
      rfl
    | some t =>
      simp only [SigOutcomeOpt, optSig]
      refine SigOutcome.mono (sigArg_outcome _ t _) (fun T X hTX => ?_)
      rw [hTX, hs]
      rfl
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
  · simp only [pyContextNew, orElse_ne v _ hn, pySetattr_prec_type _ v hv, bind, Except.bind]

end PyLean.Decimal
