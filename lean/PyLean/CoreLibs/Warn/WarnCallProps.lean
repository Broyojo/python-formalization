import PyLean.CoreLibs.Warn.WarnCall
import PyLean.CoreLibs.Warn.Props

/-!
C `warnings.warn` against `_py_warnings.warn` (`WarnCall.lean`), built on the `warn_explicit`
agreement `WarnTwinsNarrow` (`Props.lean`).
-/

namespace PyLean.CoreLibs.Warn

open PyLean

/-! ## The walks -/

theorem pySkipFn_str (ps : List String) : pySkipFn (ps.map .str) = fun f => .ok (cSkipFn ps f) := by
  funext f
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, pySkipFn, pyStartsWith, bind, Except.bind, cSkipFn, List.any_cons]
    cases hp : p.toList.isPrefixOf f.toList
    · simpa [cSkipFn] using ih
    · rfl

theorem nextExt_pure (sk : String → Bool) (l : List Frame) (j : Nat) :
    ∃ r, nextExt (fun f => .ok (sk f)) l j = .ok r := by
  induction l generalizing j with
  | nil => exact ⟨none, rfl⟩
  | cons f fs ih =>
    unfold nextExt
    by_cases hi : internalFn f.filename
    · simp only [hi, if_true]; exact ih (j + 1)
    · simp only [hi, Bool.false_eq_true, if_false, bind, Except.bind]
      cases hs : sk f.filename
      · simp only [Bool.false_eq_true, if_false]; exact ⟨_, rfl⟩
      · simp only [if_true]; exact ih (j + 1)

theorem pyLoop_eq (fr : List Frame) (ps : List String) (n i : Nat) :
    pyLoop fr (ps.map .str) n i = .ok (cLoop (cStep fr ps) n (some i)) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [pyLoop, pySkipFn_str, bind, Except.bind, cLoop]
    obtain ⟨r, hr⟩ := nextExt_pure (cSkipFn ps) (after fr i) (i + 1)
    rw [hr]
    have hc : cStep fr ps i = r := by simp [cStep, hr]
    rw [hc]
    cases r with
    | none => cases n <;> rfl
    | some j => simp only [ih j]

theorem cLoop_none (st : Nat → Option Nat) (n : Nat) : cLoop st n none = none := by
  cases n <;> rfl

theorem cLoop_back (fr : List Frame) (n i : Nat) :
    cLoop (cBack fr) n (some i) = if i + n < fr.length ∨ n = 0 then some (i + n) else none := by
  induction n generalizing i with
  | zero => simp [cLoop]
  | succ n ih =>
    simp only [cLoop, cBack]
    by_cases h : i + 1 < fr.length
    · simp only [h, if_true, ih (i + 1)]
      have e : i + 1 + n = i + (n + 1) := by omega
      rw [e]
      by_cases h2 : i + (n + 1) < fr.length
      · simp [h2]
      · have : ¬ (i + 1 + n < fr.length) := by omega
        simp [h2]
        omega
    · simp only [h, if_false, cLoop_none]
      have : ¬ (i + (n + 1) < fr.length) := by omega
      simp [this]

/-- Where `setup_context` ends, as a position. -/
def cPos (fr : List Frame) (ps : List String) (s : Int) : Pos :=
  match cWalk fr ps s with
  | some i => .idx i
  | none => .sys

/-- For a stacklevel `>= 1` that fits a C `int` and prefixes that are strs, the Python walk ends
where the C one does. -/
theorem pyWalk_eq (fr : List Frame) (ps : List String) (s : Int) (h1 : 1 ≤ s) (h2 : s ≤ intMax) :
    pyWalk fr (ps.map .str) s = .ok (cPos fr ps s) := by
  have hfit : ¬ (s > intMax ∨ s < -intMax - 1) := by simp [intMax] at h2 ⊢; omega
  have hs0 : ¬ s ≤ 0 := by omega
  have hplain : pyPlain fr s =
      .ok (if (s - 1).toNat < fr.length then .idx (s - 1).toNat else .sys) := by
    unfold pyPlain getframe
    rw [if_neg hfit, if_neg hs0]
    split <;> simp_all [Except.map]
  unfold pyWalk cPos cWalk
  by_cases hs1 : s ≤ 1
  · have hs : s = 1 := by omega
    subst hs
    rw [if_pos hs1, hplain]
    cases fr with
    | nil => rfl
    | cons f fs => simp [cLoop]
  · rw [if_neg hs1]
    have hn : (s - 1).toNat = ((s - 1).toNat - 1) + 1 := by omega
    cases fr with
    | nil =>
      rw [hn]
      simp [cLoop_none]
    | cons f fs =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, internal0, hs0, decide_false,
        Bool.false_or]
      by_cases hin : internalFn f.filename
      · have hz : ¬ (s - 1).toNat = 0 := by omega
        simp only [hin, if_true, hplain, cLoop_back, Bool.or_true, Nat.zero_add]
        generalize (s - 1).toNat = k at *
        by_cases hl : k < fs.length + 1
        · simp [hl]
        · simp [hl, hz]
      · simp only [hin, Bool.false_eq_true, if_false, pyExt, pyLoop_eq, Except.map]
        cases cLoop (cStep (f :: fs) ps) (s - 1).toNat (some 0) <;> rfl

/-! ## The agreement -/

/-- `__name__` is a str or missing; the registry is missing, `None`, or a dict whose version is an
exact int within C long (the documented globals of a module; see `RegOk`). -/
def GlobalsOk (G : Globals) : Prop :=
  (G.name = .missing ∨ ∃ n, G.name = .str n) ∧
  (G.reg = .missing ∨ G.reg = .none ∨ ∃ r, G.reg = .dict r ∧
    ∀ v, regGet r .version = .some v → v.exact = true ∧ -longMax - 1 ≤ v.n ∧ v.n ≤ longMax)

/-- The category is `None` or a Warning subclass, or the message is a Warning instance. -/
def CatOk (m : MsgA) (c : CatA) : Prop :=
  (∃ k t, m = .warn k t) ∨ c = .none ∨ ∃ k n fq, c = .cls k n fq true

/-- For a documented call (a str or Warning message, a Warning subclass or `None` category, a
`stacklevel` from 1 to the C `int` maximum, `skip_file_prefixes` a tuple of strs), every stack whose
frames' lines are C `int`s and whose globals are `GlobalsOk`, and everything `WarnTwinsNarrow`
assumes of the filters, the callbacks and the message: C `warnings.warn` and `_py_warnings.warn`
give the same result, use the same globals' registry and leave it and the once registry the same
(`True == 1`). -/
def WarnCallTwinsNarrow : Prop :=
  ∀ (W : WEnv) E fs dflt ver once (m : MsgA) (c : CatA) (s : Int) (ps : List String),
    ver ≠ 0 → EnvOk E → ItemsOk fs → DfltOk dflt → (∀ k, W.mkMsg k = .ok ()) → CatOk m c →
    1 ≤ s → s ≤ intMax → (∀ f ∈ W.frames, -intMax - 1 ≤ f.lineno ∧ f.lineno ≤ intMax) →
    (∀ g, GlobalsOk (W.globals g)) →
    let r1 := cWarn W E fs dflt ver once m c s (.tuple (ps.map .str))
    let r2 := pyWarn W E fs dflt ver once m c s (.tuple (ps.map .str))
    r1.out = r2.out ∧ r1.reg.map (fun p => (p.1, norm p.2)) = r2.reg.map (fun p => (p.1, norm p.2)) ∧
      norm r1.once = norm r2.once

theorem cCheckPrefixes_str (ps : List String) : cCheckPrefixes (ps.map .str) = .ok ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [cCheckPrefixes, ih, Except.map]

theorem module_eq (G : Globals) (h : GlobalsOk G) : cModule G.name = pyModule G.name := by
  rcases h.1 with h | ⟨n, h⟩ <;> rw [h] <;> rfl

/-- The context both twins compute, for a stacklevel already raised for the prefixes. -/
def ctxAt (W : WEnv) (ps : List String) (s : Int) : WCtx :=
  let (g, fn, ln) := frameAt W (cPos W.frames ps s)
  ⟨fn, ln, g, pyModule (W.globals g).name, regOf (W.globals g).reg⟩

/-- The stacklevel after the prefixes raise it to 2. -/
def raised (ps : List String) (s : Int) : Int := if ps.isEmpty then s else max 2 s

theorem setup_eq (W : WEnv) (m : MsgA) (c : CatA) (s : Int) (ps : List String) (hc : CatOk m c)
    (h1 : 1 ≤ s) (h2 : s ≤ intMax) (hg : ∀ g, GlobalsOk (W.globals g)) :
    cWarnSetup W m c s (.tuple (ps.map .str)) =
      (pyGetCategory W m c).map (fun cat => (cat, ctxAt W ps (raised ps s))) ∧
    pyWarnSetup W m c s (.tuple (ps.map .str)) =
      (pyGetCategory W m c).map (fun cat => (cat, ctxAt W ps (raised ps s))) := by
  have hfit : ¬ (s > ssizeMax ∨ s < -ssizeMax - 1) := by simp [ssizeMax, intMax] at h2 ⊢; omega
  have hcat : cGetCategory W m c = pyGetCategory W m c := by
    rcases hc with ⟨k, t, rfl⟩ | rfl | ⟨k, n, fq, rfl⟩
    · rfl
    · cases m <;> rfl
    · cases m <;> rfl
  have hmax : (if s < 2 then 2 else s) = max 2 s := by split <;> omega
  have hs1 : 1 ≤ raised ps s := by unfold raised; split <;> omega
  have hs2 : raised ps s ≤ intMax := by unfold raised; split <;> simp [intMax] at h2 ⊢ <;> omega
  have hemp : (ps.map PElem.str).isEmpty = ps.isEmpty := by cases ps <;> rfl
  have hwalk := pyWalk_eq W.frames ps (raised ps s) hs1 hs2
  constructor
  · unfold cWarnSetup cSetup
    rw [hcat]
    cases hp : pyGetCategory W m c with
    | error e => simp [hfit, bind, Except.bind, pure, Except.pure, Except.map]
    | ok cat =>
      cases hpe : ps.isEmpty
      · simp only [hfit, if_false, bind, Except.bind, pure, Except.pure, hemp, hpe, Bool.false_eq_true,
          cCheckPrefixes_str, Except.map, hmax]
        simp only [ctxAt, raised, hpe, Bool.false_eq_true, if_false, cPos, module_eq _ (hg _)]
        rfl
      · have hnil : ps = [] := List.isEmpty_iff.mp hpe
        subst hnil
        simp only [hfit, if_false, bind, Except.bind, pure, Except.pure, List.map_nil, List.isEmpty_nil,
          if_true, Except.map]
        simp only [ctxAt, raised, List.isEmpty_nil, if_true, cPos, module_eq _ (hg _)]
        rfl
  · unfold pyWarnSetup
    cases hp : pyGetCategory W m c with
    | error e => simp [bind, Except.bind, Except.map]
    | ok cat =>
      have hsel : (if (ps.map PElem.str).isEmpty then s else max 2 s) = raised ps s := by
        rw [hemp]; rfl
      simp only [bind, Except.bind, pure, Except.pure, Except.map, hsel, hwalk]
      rfl

theorem frameAt_line (W : WEnv) (ps : List String) (s : Int)
    (hfl : ∀ f ∈ W.frames, -intMax - 1 ≤ f.lineno ∧ f.lineno ≤ intMax) :
    -intMax - 1 ≤ (ctxAt W ps s).lineno ∧ (ctxAt W ps s).lineno ≤ intMax := by
  unfold ctxAt
  cases hp : cPos W.frames ps s with
  | self =>
    unfold cPos at hp
    split at hp <;> simp at hp
  | idx i =>
    simp only [frameAt]
    cases hf : W.frames[i]? with
    | none => simp [intMax]
    | some f => exact hfl f (List.mem_of_getElem? hf)
  | sys => simp [frameAt, intMax]

theorem warnCallTwinsNarrow_proven : WarnCallTwinsNarrow := by
  intro W E fs dflt ver once m c s ps hv he hi hd hmk hc h1 h2 hfl hg
  obtain ⟨hC, hP⟩ := setup_eq W m c s ps hc h1 h2 hg
  simp only [cWarn, pyWarn, hC, hP]
  cases hp : pyGetCategory W m c with
  | error e => simp [Except.map, finish]
  | ok cat =>
    simp only [Except.map, finish]
    generalize hx : ctxAt W ps (raised ps s) = x
    have hl := frameAt_line W ps (raised ps s) hfl
    rw [hx] at hl
    have hmod : ModOk (callOf W m cat x) := by
      rw [← hx]
      simp only [ModOk, callOf, ctxAt]
      rcases (hg (frameAt W (cPos W.frames ps (raised ps s))).1).1 with h | ⟨n, h⟩ <;> simp [h, pyModule]
    have hreg : RegOk x.reg := by
      rw [← hx]
      simp only [ctxAt]
      rcases (hg (frameAt W (cPos W.frames ps (raised ps s))).1).2 with h | h | ⟨r, h, hr⟩
      · rw [h]; exact Or.inr ⟨[], rfl, by simp [regGet]⟩
      · rw [h]; exact Or.inl rfl
      · rw [h]; exact Or.inr ⟨r, rfl, hr⟩
    have hmsg : MsgOk (callOf W m cat x) := by
      simp only [MsgOk, callOf]; cases m <;> simp [hmk]
    have hline : LineOk (callOf W m cat x) := ⟨x.lineno, rfl, hl.1, hl.2⟩
    obtain ⟨t1, t2, t3⟩ := warnTwinsNarrow_proven E fs dflt ver (callOf W m cat x) x.reg once hv he hi hd
      hline hmod hmsg hreg
    refine ⟨t1, ?_, t3⟩
    revert t2
    cases (cWarnExplicit E fs dflt ver (callOf W m cat x) x.reg once).reg <;>
      cases (pyWarnExplicit E fs dflt ver (callOf W m cat x) x.reg once).reg <;> simp

/-! ## The cases left out -/

/-- Any `stacklevel`, any prefixes, any globals: refuted (python twin divergences, see the bug
record): `stacklevel=0` is the caller in C and `warn`'s own frame in Python. -/
def WarnCallTwins : Prop :=
  ∀ (W : WEnv) E fs dflt ver once (m : MsgA) (c : CatA) (s : Int) (skip : SkipA),
    ver ≠ 0 → EnvOk E → ItemsOk fs → DfltOk dflt → (∀ k, W.mkMsg k = .ok ()) →
    let r1 := cWarn W E fs dflt ver once m c s skip
    let r2 := pyWarn W E fs dflt ver once m c s skip
    r1.out = r2.out ∧ r1.reg.map (fun p => (p.1, norm p.2)) = r2.reg.map (fun p => (p.1, norm p.2))

def wE0 : WEnv := WEnv.mk [⟨"a.py", 3, 0⟩] ⟨"PYW", 505, 2⟩ (fun _ => ⟨.str "m", .missing⟩) 1 1
  (fun _ => .ok ())

theorem itemsNil : ItemsOk [] := fun _ h => by simp at h

theorem dfltOkDefault : DfltOk (some "default") := ⟨"default", rfl, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩

/-- `stacklevel=0`: C uses the caller's registry (globals 0), Python `warn`'s own (globals 2). -/
theorem warnCallTwins_refuted : ¬ WarnCallTwins := fun h =>
  refute (h wE0 E0 [] (some "default") 1 [] (.str "x") .none 0 (.tuple []) (by decide) envOk0 itemsNil
    dfltOkDefault (fun _ => rfl)).2
    (x := some (0, [(.tri "x" 1 3, 1), (.version, 1)])) (y := some (2, [(.tri "x" 1 505, 1), (.version, 1)]))
    (by rfl) (by rfl) (by simp)

/-- A prefix that is a tuple of strs: C refuses it, Python accepts it. -/
theorem warnCallTwins_refuted_prefix : ¬ WarnCallTwins := fun h =>
  refute (h wE0 E0 [] (some "default") 1 [] (.str "x") .none 1 (.tuple [.tup ["zz"]]) (by decide) envOk0
    itemsNil dfltOkDefault (fun _ => rfl)).1
    (x := .error (.typeError "Found non-str 'tuple' in skip_file_prefixes.")) (y := .ok true)
    (by rfl) (by rfl) (by simp)

/-- A `stacklevel` beyond `Py_ssize_t`: C's conversion raises, Python reports `<sys>`. -/
theorem warnCallTwins_refuted_huge : ¬ WarnCallTwins := fun h =>
  refute (h wE0 E0 [] (some "default") 1 [] (.str "x") .none (2 ^ 64) (.tuple []) (by decide) envOk0
    itemsNil dfltOkDefault (fun _ => rfl)).1
    (x := .error (.overflowError "Python int too large to convert to C ssize_t")) (y := .ok true)
    (by rfl) (by rfl) (by simp)

end PyLean.CoreLibs.Warn
