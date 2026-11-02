import PyLean.CoreLibs.Warn.Model

/-!
C `warn_explicit` against `_py_warnings.warn_explicit`. `WarnTwinsNarrow` is proven; every case
it leaves out is on record as a refuted property below.
-/

namespace PyLean.CoreLibs.Warn

open PyLean

/-! ## Hypotheses -/

/-- No callback raises: `issubclass`, `_match_filename` and every filter's patterns. -/
def CallbacksTotal (E : Env) (fs : List Filter) : Prop :=
  (∀ a b, ∃ x, E.isSub a b = .ok x) ∧ (∀ m s, ∃ x, E.matchFilename m s = .ok x) ∧
  ∀ f ∈ fs, (∀ m, f.msg = .some m → ∀ s, ∃ x, m.call s = .ok x) ∧
    (∀ m, f.mod = .some m → ∀ s, ∃ x, m.call s = .ok x)

/-- The actions other than `once` and `module`. -/
def Plain (a : String) : Prop :=
  a = "error" ∨ a = "ignore" ∨ a = "always" ∨ a = "all" ∨ a = "default"

/-- `filterwarnings` and `simplefilter` accept any `lineno >= 0`. -/
def LinesValid (fs : List Filter) : Prop := ∀ f ∈ fs, 0 ≤ f.ln
def LinesFit (fs : List Filter) : Prop := ∀ f ∈ fs, 0 ≤ f.ln ∧ f.ln ≤ ssizeMax

def VersionFits (reg : Option Reg) : Prop :=
  ∀ r, reg = .some r → ∀ v, regGet r .version = .some v → -longMax - 1 ≤ v ∧ v ≤ longMax

def LineFits (c : Call) : Prop := -intMax - 1 ≤ c.lineno ∧ c.lineno ≤ intMax

def ModuleGiven (c : Call) : Prop := match c.module with | .none => False | _ => True

def Twins (E : Env) (fs : List Filter) (dflt : String) (ver : Int) (c : Call) (reg : Option Reg)
    (once : Reg) : Prop :=
  cWarnExplicit E fs dflt ver c reg once = pyWarnExplicit E fs dflt ver c reg once

/-! ## The proven agreement -/

/-- For every set of callbacks that do not raise, every filters list whose actions are `error`,
`ignore`, `always`, `all` or `default` and whose lines fit `Py_ssize_t`, the same default action,
every call with a line that fits C `int` and a `module` that is not an explicit `None`, every
registry (or none) whose `'version'` fits C long, and every filters version but 0 (the counter
starts at 1), the C and Python `warn_explicit` give the same result and leave the same registry
and once registry. -/
def WarnTwinsNarrow : Prop :=
  ∀ E fs dflt ver c reg once,
    ver ≠ 0 → CallbacksTotal E fs → (∀ f ∈ fs, Plain f.action) → Plain dflt → LinesFit fs →
    ModuleGiven c → LineFits c → VersionFits reg → Twins E fs dflt ver c reg once

theorem filterMatches_eq (E : Env) (c : Call) (f : Filter) (hm : ModuleGiven c)
    (hcb : (∀ a b, ∃ x, E.isSub a b = .ok x) ∧ (∀ m s, ∃ x, E.matchFilename m s = .ok x))
    (hmsg : ∀ m, f.msg = .some m → ∀ s, ∃ x, m.call s = .ok x)
    (hmod : ∀ m, f.mod = .some m → ∀ s, ∃ x, m.call s = .ok x)
    (hln : 0 ≤ f.ln ∧ f.ln ≤ ssizeMax) :
    cFilterMatches E false c (match c.module with | .some s => .some s | _ => .none) f =
      pyFilterMatches E c f := by
  obtain ⟨hs, hf⟩ := hcb
  have ha : asSsize f.ln = .ok f.ln := by
    unfold asSsize; rw [if_neg]; simp [ssizeMax] at hln ⊢; omega
  obtain ⟨gs, hgs⟩ := hs c.cat f.cat
  have hM : ∃ gm, checkMatched E false f.msg (.some c.text) c.filename = .ok gm ∧ pyMsgOk c f = .ok gm := by
    unfold pyMsgOk
    cases h : f.msg with
    | none => exact ⟨true, rfl, rfl⟩
    | some m => obtain ⟨x, hx⟩ := hmsg m h c.text; exact ⟨x, by simp [checkMatched, callPat, hx], hx⟩
  have hD : ∃ gd, checkMatched E false f.mod (match c.module with | .some s => .some s | _ => .none)
        c.filename = .ok gd ∧ pyModOk E c f = .ok gd := by
    unfold pyModOk
    cases h : f.mod with
    | none => exact ⟨true, rfl, rfl⟩
    | some m =>
      cases hc : c.module with
      | omitted =>
        obtain ⟨x, hx⟩ := hf m c.filename; exact ⟨x, by simp [checkMatched, hx], hx⟩
      | none => simp [ModuleGiven, hc] at hm
      | some s => obtain ⟨x, hx⟩ := hmod m h s; exact ⟨x, by simp [checkMatched, callPat, hx], hx⟩
  obtain ⟨gm, hm1, hm2⟩ := hM
  obtain ⟨gd, hd1, hd2⟩ := hD
  have hgs' : cIsSub E false c.cat f.cat = .ok gs := by simp [cIsSub, hgs]
  unfold cFilterMatches pyFilterMatches
  rw [hm1, hd1, hgs', hgs, ha, hm2, hd2]
  cases gm <;> cases gs <;> cases gd <;>
    by_cases hl : (f.ln == 0 || c.lineno == f.ln) = true <;>
    simp [hl, bind, Except.bind, pure, Except.pure]

theorem find_eq (E : Env) (c : Call) (fs : List Filter) (hm : ModuleGiven c)
    (hcb : CallbacksTotal E fs) (hl : LinesFit fs) :
    cFind E false c (match c.module with | .some s => .some s | _ => .none) fs = pyFind E c fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    obtain ⟨h1, h2, h3⟩ := hcb
    have e := filterMatches_eq E c f hm ⟨h1, h2⟩ (h3 f (by simp)).1 (h3 f (by simp)).2 (hl f (by simp))
    have ih' := ih ⟨h1, h2, fun g hg => h3 g (by simp [hg])⟩ (fun g hg => hl g (by simp [hg]))
    simp only [cFind, pyFind, e, ih']

/-- `already_warned` with a `'version'` that fits C long, against the Python check. -/
theorem alreadyWarned_eq (ver : Int) (r : Reg) (k : Key) (hv : ver ≠ 0) (hk : k ≠ .version)
    (hfit : ∀ v, regGet r .version = .some v → -longMax - 1 ≤ v ∧ v ≤ longMax) :
    cAlreadyWarned ver r k false =
      (false, truthy (regGet (pyRegPrep ver (.some r)) k), pyRegPrep ver (.some r)) := by
  have hget : regGet (regSet [] .version ver) k = .none := by
    simp [regGet, regSet, Ne.symm hk]
  unfold cAlreadyWarned pyRegPrep
  cases h : regGet r .version with
  | none =>
    simp [h, Ne.symm hv, hget, truthy]
  | some x =>
    have hx := hfit x h
    have hp : ¬ (x > longMax ∨ x < -longMax - 1) := by omega
    by_cases hxv : x = ver
    · subst hxv
      cases ht : truthy (regGet r k) <;> simp [h, hp, ht]
    · simp [h, hp, hxv, hget, truthy]

/-- The plain actions take the same steps in both twins. -/
theorem action_eq (E : Env) (ver : Int) (c : Call) (a : String) (b : Bool) (reg : Option Reg)
    (r1 once : Reg) (ha : Plain a) :
    cAction E ver c a (reg.map (fun _ => r1)) once =
      (false, (pyAction E c a b r1 once).1, reg.map (fun _ => (pyAction E c a b r1 once).2.1),
        (pyAction E c a b r1 once).2.2) := by
  rcases ha with h | h | h | h | h <;> subst h <;> cases reg <;> simp [cAction, pyAction]

theorem warnTwinsNarrow_proven : WarnTwinsNarrow := by
  intro E fs dflt ver c reg once hv hcb hact hdflt hl hm hline hver
  have hfind := find_eq E c fs hm hcb hl
  have hline' : ¬ (c.lineno > intMax ∨ c.lineno < -intMax - 1) := by
    simp only [LineFits] at hline; omega
  have hkey : Key.tri c.text c.cat c.lineno ≠ .version := by simp
  -- the chosen action is plain
  have hplain : ∀ item, pyFind E c fs = .ok item → Plain (actionOf item dflt) := by
    intro item hi
    cases item with
    | none => exact hdflt
    | some f =>
      have mem : ∀ fs' : List Filter, (∀ g ∈ fs', Plain g.action) →
          pyFind E c fs' = .ok (.some f) → Plain f.action := by
        intro fs' hp hf'
        induction fs' with
        | nil => simp [pyFind, pure, Except.pure] at hf'
        | cons g gs ih =>
          simp only [pyFind, bind, Except.bind] at hf'
          split at hf'
          · simp at hf'
          · rename_i b _
            cases b
            · exact ih (fun g' hg' => hp g' (by simp [hg'])) hf'
            · simp [pure, Except.pure] at hf'; subst hf'; exact hp g (by simp)
      exact mem fs hact hi
  unfold Twins cWarnExplicit pyWarnExplicit
  rw [if_neg hline']
  cases hcm : c.module with
  | none => simp [ModuleGiven, hcm] at hm
  | omitted | some s =>
    simp only [hcm] at hfind
    simp only
    cases reg with
    | none =>
      have hk0 : truthy (regGet (pyRegPrep ver .none) (.tri c.text c.cat c.lineno)) = false := by
        simp [pyRegPrep, regGet, regSet, Ne.symm hv, truthy]
      simp only [hk0, Bool.false_eq_true, if_false, hfind]
      cases hpf : pyFind E c fs with
      | error e => simp
      | ok item =>
        have e := action_eq E ver c (actionOf item dflt) (item.isSome || !fs.isEmpty) .none
          (pyRegPrep ver .none) once
          (hplain item hpf)
        simp only [Option.map] at e
        simp [e, withPending]
    | some r =>
      have haw := alreadyWarned_eq ver r (.tri c.text c.cat c.lineno) hv hkey (hver r rfl)
      simp only [haw, hfind]
      by_cases hw : truthy (regGet (pyRegPrep ver (.some r)) (.tri c.text c.cat c.lineno)) = true
      · simp [hw, withPending]
      · simp only [hw, Bool.false_eq_true, if_false]
        cases hpf : pyFind E c fs with
        | error e => simp
        | ok item =>
          have e := action_eq E ver c (actionOf item dflt) (item.isSome || !fs.isEmpty) (.some r)
            (pyRegPrep ver (.some r)) once
            (hplain item hpf)
          simp only [Option.map] at e
          simp [e, withPending]

/-- Two computed results that differ refute an equation between them. -/
theorem refute {α : Type} {a b x y : α} (h : a = b) (ha : a = x) (hb : b = y) (hxy : x ≠ y) :
    False := hxy (ha.symm.trans (h.trans hb))

/-! ## The cases left out, each refuted -/

/-- Callbacks that never raise and a trivial `_match_filename`. -/
def E0 : Env := ⟨fun _ _ => .ok true, fun _ _ => false, fun _ _ => .ok true, .ok ()⟩

def call0 (ln : Int) (m : ModArg) : Call := ⟨"x", 1, "a.py", ln, m⟩

/-- `once` is in scope: the documented "print only the first occurrence of matching warnings,
regardless of location" is what `_py_warnings` does with its global once registry, but the C code
uses the caller's registry when there is one (python/cpython#159792). A warning already in the once
registry is shown again by C. -/
def WarnTwinsOnce : Prop :=
  ∀ E fs ver c reg once,
    ver ≠ 0 → CallbacksTotal E fs → (∀ f ∈ fs, Plain f.action ∨ f.action = "once") → LinesFit fs →
    ModuleGiven c → LineFits c → VersionFits reg → Twins E fs "once" ver c reg once

theorem warnTwinsOnce_refuted : ¬ WarnTwinsOnce := fun h =>
  refute (congrArg Res.out (h E0 [] 1 (call0 1 (.some "a")) (.some []) [(.pair "x" 1, 1)]
    (by decide) ⟨fun _ _ => ⟨true, rfl⟩, fun _ _ => ⟨true, rfl⟩, by simp⟩ (by simp) (by simp [LinesFit])
    trivial (by simp [LineFits, call0, intMax]) (by simp [VersionFits, regGet])))
    (x := .ok true) (y := .ok false) (by rfl) (by rfl) (by simp)

/-- `module` is in scope: Python marks "already shown in this module" with the key
`(text, category, 0)`, which is also the key of the warning itself when its line is 0. So
`_py_warnings` never shows a line-0 warning under `module`, while C, whose key is
`(text, category)`, shows it once. -/
def WarnTwinsModule : Prop :=
  ∀ E fs ver c reg once,
    ver ≠ 0 → CallbacksTotal E fs → (∀ f ∈ fs, Plain f.action ∨ f.action = "module") →
    LinesFit fs → ModuleGiven c → LineFits c → VersionFits reg → Twins E fs "module" ver c reg once

theorem warnTwinsModule_refuted : ¬ WarnTwinsModule := fun h =>
  refute (congrArg Res.out (h E0 [] 1 (call0 0 (.some "a")) (.some []) []
    (by decide) ⟨fun _ _ => ⟨true, rfl⟩, fun _ _ => ⟨true, rfl⟩, by simp⟩ (by simp) (by simp [LinesFit])
    trivial (by simp [LineFits, call0, intMax]) (by simp [VersionFits, regGet])))
    (x := .ok true) (y := .ok false) (by rfl) (by rfl) (by simp)

/-- Filter lines as `filterwarnings` accepts them (any int `>= 0`): a filter with
`lineno=2**63` makes every C warning raise `OverflowError`; Python just never matches it. -/
def WarnTwinsValidLines : Prop :=
  ∀ E fs dflt ver c reg once,
    ver ≠ 0 → CallbacksTotal E fs → (∀ f ∈ fs, Plain f.action) → Plain dflt → LinesValid fs →
    ModuleGiven c → LineFits c → VersionFits reg → Twins E fs dflt ver c reg once

def bigLine : Filter := ⟨"error", .none, 1, .none, 2 ^ 63⟩

theorem warnTwinsValidLines_refuted : ¬ WarnTwinsValidLines := fun h =>
  refute (congrArg Res.out (h E0 [bigLine] "default" 1 (call0 1 (.some "a")) .none []
    (by decide) ⟨fun _ _ => ⟨true, rfl⟩, fun _ _ => ⟨true, rfl⟩, by simp [bigLine]⟩
    (by simp [bigLine, Plain]) (by simp [Plain]) (by simp [LinesValid, bigLine])
    trivial (by simp [LineFits, call0, intMax]) (by simp [VersionFits])))
    (x := .error (.overflowError "Python int too large to convert to C ssize_t")) (y := .ok true)
    (by rfl) (by rfl) (by simp)

/-- Any int as the registry's `'version'`: C reads it with `PyLong_AsLong` and does not check
for an error, so `{'version': 2**64}` ends in `SystemError`; Python clears the registry and
shows the warning. -/
def WarnTwinsAnyVersion : Prop :=
  ∀ E fs dflt ver c reg once,
    ver ≠ 0 → CallbacksTotal E fs → (∀ f ∈ fs, Plain f.action) → Plain dflt → LinesFit fs →
    ModuleGiven c → LineFits c → Twins E fs dflt ver c reg once

theorem warnTwinsAnyVersion_refuted : ¬ WarnTwinsAnyVersion := fun h =>
  refute (congrArg Res.out (h E0 [] "default" 1 (call0 1 (.some "a")) (.some [(.version, 2 ^ 64)]) []
    (by decide) ⟨fun _ _ => ⟨true, rfl⟩, fun _ _ => ⟨true, rfl⟩, by simp⟩ (by simp) (by simp [Plain])
    (by simp [LinesFit]) trivial (by simp [LineFits, call0, intMax])))
    (x := .error leaked) (y := .ok true) (by rfl) (by rfl) (by simp)

/-- The invariant on its own: C `warn_explicit` never leaks an internal error, for every registry
of ints. -/
def NoSystemError : Prop :=
  ∀ E fs dflt ver c reg once, (cWarnExplicit E fs dflt ver c reg once).out ≠ .error leaked

theorem noSystemError_refuted : ¬ NoSystemError := fun h =>
  h E0 [] "default" 1 (call0 1 (.some "a")) (.some [(.version, 2 ^ 64)]) [] (by rfl)

/-- Callbacks that raise: C runs the message test, the module test and `issubclass` before it
looks at any of them; Python stops at the first that fails. A filter whose message does not
match but whose category's `__subclasscheck__` raises is skipped by Python and raises in C. -/
def WarnTwinsRaising : Prop :=
  ∀ E fs dflt ver c reg once,
    ver ≠ 0 → (∀ f ∈ fs, Plain f.action) → Plain dflt → LinesFit fs → ModuleGiven c →
    LineFits c → VersionFits reg → Twins E fs dflt ver c reg once

def Eraise : Env := ⟨fun _ _ => .error (.keyError "boom"), fun _ _ => true, fun _ _ => .ok true, .ok ()⟩
def noMatch : Filter := ⟨"error", .some ⟨fun _ => .ok false, true⟩, 1, .none, 0⟩

theorem warnTwinsRaising_refuted : ¬ WarnTwinsRaising := fun h =>
  refute (congrArg Res.out (h Eraise [noMatch] "always" 1 (call0 1 (.some "a")) .none []
    (by decide) (by simp [noMatch, Plain]) (by simp [Plain]) (by simp [LinesFit, noMatch, ssizeMax])
    trivial (by simp [LineFits, call0, intMax]) (by simp [VersionFits])))
    (x := .error (.keyError "boom")) (y := .ok true) (by rfl) (by rfl) (by simp)

/-- `module=None` passed explicitly: C returns at once (`_warnings.c:812-813`, meant for
interpreter shutdown); Python treats it as omitted and applies the filters, so an `error` filter
raises in Python only. -/
def WarnTwinsNoneModule : Prop :=
  ∀ E fs dflt ver c reg once,
    ver ≠ 0 → CallbacksTotal E fs → (∀ f ∈ fs, Plain f.action) → Plain dflt → LinesFit fs →
    LineFits c → VersionFits reg → Twins E fs dflt ver c reg once

theorem warnTwinsNoneModule_refuted : ¬ WarnTwinsNoneModule := fun h =>
  refute (congrArg Res.out (h E0 [] "error" 1 (call0 1 .none) .none []
    (by decide) ⟨fun _ _ => ⟨true, rfl⟩, fun _ _ => ⟨true, rfl⟩, by simp⟩ (by simp) (by simp [Plain])
    (by simp [LinesFit]) (by simp [LineFits, call0, intMax]) (by simp [VersionFits])))
    (x := .ok false) (y := .error (warnRaised (call0 1 .none))) (by rfl) (by rfl) (by simp)

/-- A line outside C `int`: the clinic converter of C `warn_explicit` raises `OverflowError`;
Python's `int(lineno)` takes it. -/
def WarnTwinsAnyLine : Prop :=
  ∀ E fs dflt ver c reg once,
    ver ≠ 0 → CallbacksTotal E fs → (∀ f ∈ fs, Plain f.action) → Plain dflt → LinesFit fs →
    ModuleGiven c → VersionFits reg → Twins E fs dflt ver c reg once

theorem warnTwinsAnyLine_refuted : ¬ WarnTwinsAnyLine := fun h =>
  refute (congrArg Res.out (h E0 [] "always" 1 (call0 (2 ^ 31) (.some "a")) .none []
    (by decide) ⟨fun _ _ => ⟨true, rfl⟩, fun _ _ => ⟨true, rfl⟩, by simp⟩ (by simp) (by simp [Plain])
    (by simp [LinesFit]) trivial (by simp [VersionFits])))
    (x := .error (.overflowError "Python int too large to convert to C int")) (y := .ok true)
    (by rfl) (by rfl) (by simp)

/-- An action that is no known action (put in `warnings.filters` by hand, or as
`warnings.defaultaction`): both raise `RuntimeError`, but C has already stored the warning in the
registry, so the next identical call returns silently in C and raises again in Python. -/
def WarnTwinsUnknownAction : Prop :=
  ∀ E fs dflt ver c reg once,
    ver ≠ 0 → CallbacksTotal E fs → LinesFit fs → ModuleGiven c → LineFits c → VersionFits reg →
    Twins E fs dflt ver c reg once

theorem warnTwinsUnknownAction_refuted : ¬ WarnTwinsUnknownAction := fun h =>
  refute (congrArg Res.reg (h E0 [] "bogus" 1 (call0 1 (.some "a")) (.some []) []
    (by decide) ⟨fun _ _ => ⟨true, rfl⟩, fun _ _ => ⟨true, rfl⟩, by simp⟩ (by simp [LinesFit])
    trivial (by simp [LineFits, call0, intMax]) (by simp [VersionFits, regGet])))
    (x := .some [(.tri "x" 1 1, 1), (.version, 1)]) (y := .some [(.version, 1)])
    (by rfl) (by rfl) (by simp)

/-- An unknown action raises `RuntimeError` in `_py_warnings`, as it does in C, for every filters
list. With no filters and an unknown `defaultaction` the message formats `item`, the loop variable
that the empty loop never bound, and the call raises `UnboundLocalError` instead. -/
def PyUnknownActionRaises : Prop :=
  ∀ E fs dflt ver c reg once, ver ≠ 0 → CallbacksTotal E fs → LinesFit fs →
    (∀ f ∈ fs, f.action = dflt) → ¬ (Plain dflt ∨ dflt = "once" ∨ dflt = "module") →
    (cWarnExplicit E fs dflt ver c reg once).out = .error unrecognized →
    (pyWarnExplicit E fs dflt ver c reg once).out = .error unrecognized

theorem pyUnknownActionRaises_refuted : ¬ PyUnknownActionRaises := fun h =>
  refute (h E0 [] "bogus" 1 (call0 1 (.some "a")) .none [] (by decide)
    ⟨fun _ _ => ⟨true, rfl⟩, fun _ _ => ⟨true, rfl⟩, by simp⟩ (by simp [LinesFit]) (by simp)
    (by simp [Plain]) (by rfl)) (y := .error unrecognized) (x := .error unboundItem) (by rfl) rfl
    (by simp [unboundItem, unrecognized])

end PyLean.CoreLibs.Warn
