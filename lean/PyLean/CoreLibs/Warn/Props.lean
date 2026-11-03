import PyLean.CoreLibs.Warn.Model

/-!
C `warn_explicit` against `_py_warnings.warn_explicit`. `WarnTwinsNarrow` is proven; every case
it leaves out is on record as a refuted property below.
-/

namespace PyLean.CoreLibs.Warn

open PyLean

/-! ## Hypotheses -/

/-- The actions other than `once` and `module`. -/
def Plain (a : String) : Prop :=
  a = "error" ∨ a = "ignore" ∨ a = "always" ∨ a = "all" ∨ a = "default"

/-- A compiled pattern whose `match` does not raise. -/
def TotalPat (p : Pat) : Prop := ∃ call cf e, p = .regex call cf e ∧ ∀ s, ∃ x, call s = .ok x
/-- A compiled pattern. -/
def AnyRegex (p : Pat) : Prop := ∃ call cf e, p = .regex call cf e

/-- Every filters-list item has the given shape, action, patterns and line. -/
def ItemsOkG (shapeOk : Item → Filter → Prop) (actOk : AV → Prop) (patOk : Pat → Prop)
    (lnOk : LnV → Prop) (fs : List Item) : Prop :=
  ∀ it ∈ fs, ∃ f, shapeOk it f ∧ actOk f.action ∧ (∀ p, f.msg = .some p → patOk p) ∧
    (∀ p, f.mod = .some p → patOk p) ∧ lnOk f.ln

def IsTuple (it : Item) (f : Filter) : Prop := it = .tuple f
def PlainAct (a : AV) : Prop := ∃ s, a = .str s ∧ Plain s
def LnFits (l : LnV) : Prop := ∃ v, l = .int v ∧ 0 ≤ v ∧ v ≤ ssizeMax

/-- 5-tuples with a plain str action, compiled patterns that do not raise, int lines that fit
`Py_ssize_t`. -/
def ItemsOk (fs : List Item) : Prop := ItemsOkG IsTuple PlainAct TotalPat LnFits fs

/-- `issubclass` and `_match_filename` do not raise, and the show step finds both
`_showwarnmsg` (callable) and `WarningMessage`. -/
def EnvOk (E : Env) : Prop :=
  (∀ a b, ∃ x, E.isSub a b = .ok x) ∧ (∀ m s, ∃ x, E.matchFilename m s = .ok x) ∧
  ∃ wm fn, E.shw = .call wm fn

/-- An int line that fits C `int`. -/
def LineOk (c : Call) : Prop := ∃ v, c.lineno = .int v ∧ -intMax - 1 ≤ v ∧ v ≤ intMax
/-- `module` omitted or a str. -/
def ModOk (c : Call) : Prop := c.module = .omitted ∨ ∃ s, c.module = .some s
/-- The message object can be built, `module_globals` is `None`, and `linecache.getlines` does not
raise. -/
def MsgOk (c : Call) : Prop := c.mkMsg = .ok () ∧ c.globs = .none ∧ c.pyLines = .ok ()
/-- A dict (or `None`) whose `'version'`, if any, is an exact int within C long. -/
def RegOk (reg : RegArg) : Prop :=
  reg = .none ∨ ∃ r, reg = .dict r ∧
    ∀ v, regGet r .version = .some v → v.exact = true ∧ -longMax - 1 ≤ v.n ∧ v.n ≤ longMax
/-- The filters are a list, `defaultaction` a plain str action, `onceregistry` a dict. -/
def CfgOk (K : WCfg) : Prop :=
  K.tuple = false ∧ (∃ s, K.dflt = .val (.str s) ∧ Plain s) ∧ ∃ o, K.once = .dict o

/-- Same result, and the same registry and once registry as `==` sees them. -/
def Twins (E : Env) (K : WCfg) (fs : List Item) (ver : Int) (c : Call) (reg : RegArg) : Prop :=
  (cWarnExplicit E K fs ver c reg).out = (pyWarnExplicit E K fs ver c reg).out ∧
  (cWarnExplicit E K fs ver c reg).reg.map norm = (pyWarnExplicit E K fs ver c reg).reg.map norm ∧
  norm (cWarnExplicit E K fs ver c reg).once = norm (pyWarnExplicit E K fs ver c reg).once

/-! ## The proven agreement -/

/-- For every set of callbacks that do not raise (with `_showwarnmsg` and `WarningMessage`
present), every filters list (in `warnings.filters` or a context) of 5-tuples whose actions are
`error`, `ignore`, `always`, `all` or `default`, whose patterns are compiled regexes that do not
raise and whose lines are ints that fit `Py_ssize_t`, such a `defaultaction`, a dict
`onceregistry`, every call with an int line that fits C `int`, a `module` omitted or a str, a
message that can be built, no `module_globals`, and every registry that is `None` or a dict whose
`'version'` is an exact int within C long, and every filters version but 0 (the counter starts
at 1), the C and Python `warn_explicit` give the same result and leave the same registry and once
registry. -/
def WarnTwinsNarrow : Prop :=
  ∀ E K fs ver c reg,
    ver ≠ 0 → EnvOk E → ItemsOk fs → CfgOk K → LineOk c → ModOk c → MsgOk c → RegOk reg →
    Twins E K fs ver c reg

theorem filterMatches_eq (E : Env) (c : Call) (ln : Int) (f : Filter) (hm : ModOk c) (he : EnvOk E)
    (hmsg : ∀ p, f.msg = .some p → TotalPat p) (hmod : ∀ p, f.mod = .some p → TotalPat p)
    (hln : LnFits f.ln) :
    cFilterMatches E false c ln (modArg c) f = pyFilterMatches E c ln f := by
  obtain ⟨hs, hf, _⟩ := he
  obtain ⟨lv, hlv, hl0, hl1⟩ := hln
  have ha : asSsize f.ln = .ok lv := by
    rw [hlv]; simp only [asSsize]; rw [if_neg]; simp only [ssizeMax] at hl1 ⊢; omega
  have hpl : pyLnOk f.ln ln = (lv == 0 || ln == lv) := by rw [hlv]; rfl
  obtain ⟨gs, hgs⟩ := hs c.cat f.cat
  have hgs' : cIsSub E false c.cat f.cat = .ok gs := by simp [cIsSub, hgs]
  have hM : ∃ gm, checkMatched E false f.msg (.str c.text) c.filename = .ok gm ∧ pyMsgOk c f = .ok gm := by
    unfold pyMsgOk
    cases h : f.msg with
    | none => exact ⟨true, rfl, rfl⟩
    | some p =>
      obtain ⟨call, cf, e, rfl, ht⟩ := hmsg p h
      obtain ⟨x, hx⟩ := ht c.text
      exact ⟨x, by simp [checkMatched, callPat, hx], by simp [pyMatch, hx]⟩
  have hD : ∃ gd, checkMatched E false f.mod (modArg c) c.filename = .ok gd ∧ pyModOk E c f = .ok gd := by
    unfold pyModOk modArg
    cases h : f.mod with
    | none => exact ⟨true, rfl, rfl⟩
    | some p =>
      obtain ⟨call, cf, e, rfl, ht⟩ := hmod p h
      rcases hm with hc | ⟨s, hc⟩
      · obtain ⟨x, hx⟩ := hf (.regex call cf e) c.filename
        exact ⟨x, by simp [hc, checkMatched, hx], by simp [hc, hx]⟩
      · obtain ⟨x, hx⟩ := ht s
        exact ⟨x, by simp [hc, checkMatched, callPat, hx], by simp [hc, pyMatch, hx]⟩
  obtain ⟨gm, hm1, hm2⟩ := hM
  obtain ⟨gd, hd1, hd2⟩ := hD
  unfold cFilterMatches pyFilterMatches
  rw [hm1, hd1, hgs', hgs, ha, hm2, hd2, hpl]
  cases gm <;> cases gs <;> cases gd <;>
    by_cases hl : (lv == 0 || ln == lv) = true <;>
    simp [hl, bind, Except.bind, pure, Except.pure]

theorem find_eq (E : Env) (c : Call) (ln : Int) (fs : List Item) (hm : ModOk c) (he : EnvOk E)
    (hi : ItemsOk fs) : ∀ nm i, cFind E false c ln (modArg c) nm i fs = pyFind E c ln fs := by
  induction fs with
  | nil => intro nm i; rfl
  | cons it its ih =>
    intro nm i
    obtain ⟨f, hshape, ⟨a, ha, _⟩, hmsg, hmod, hln⟩ := hi it (by simp)
    have ih' := ih (fun g hg => hi g (by simp [hg]))
    unfold IsTuple at hshape
    subst hshape
    have e := filterMatches_eq E c ln f hm he hmsg hmod hln
    simp only [cFind, pyFind, ha, e, ih']

/-- `already_warned` with an exact `'version'` within C long, against the Python check. -/
theorem alreadyWarned_eq (ver : Int) (r : Reg) (k : Key) (hv : ver ≠ 0) (hk : k ≠ .version)
    (hfit : ∀ v, regGet r .version = .some v → v.exact = true ∧ -longMax - 1 ≤ v.n ∧ v.n ≤ longMax) :
    cAlreadyWarned ver r k false = (false, truthy (regGet (pyRegPrep ver r) k), pyRegPrep ver r) := by
  have hget : regGet (regSet [] .version (exactInt ver)) k = .none := by
    simp [regGet, regSet, Ne.symm hk]
  unfold cAlreadyWarned pyRegPrep
  cases h : regGet r .version with
  | none => simp [h, Ne.symm hv, hget, truthy]
  | some x =>
    obtain ⟨hx, h1, h2⟩ := hfit x h
    have hp : ¬ (x.n > longMax ∨ x.n < -longMax - 1) := by omega
    by_cases hxv : x.n = ver
    · have hp2 : ¬ (longMax < ver ∨ ver < -longMax - 1) := by omega
      cases ht : truthy (regGet r k) <;> simp [h, hp, hp2, hx, hxv, ht]
    · simp [h, hp, hx, hxv, hget, truthy]

/-- The two show steps agree when both attributes are there and `linecache.getlines` succeeds. -/
theorem show_eq (E : Env) (c : Call) (he : EnvOk E) (hl : c.pyLines = .ok ()) :
    cShow E = pyShow E c := by
  obtain ⟨_, _, wm, fn, hs⟩ := he
  simp [cShow, pyShow, hs, hl, bind, Except.bind, getWarningsAttr]

/-- The plain actions take the same steps in both twins, registries compared by `norm`. -/
theorem action_eq (E : Env) (K : WCfg) (ver : Int) (c : Call) (ln : Int) (a : String) (b : Bool)
    (reg : Option Reg) (r1 : Reg) (ha : Plain a) (hs : cShow E = pyShow E c) :
    (cAction E K ver c ln a (reg.map (fun _ => r1))).1 = false ∧
    (cAction E K ver c ln a (reg.map (fun _ => r1))).2.1 = (pyAction E K c ln (.str a) b r1).1 ∧
    (cAction E K ver c ln a (reg.map (fun _ => r1))).2.2.1.map norm =
      reg.map (fun _ => norm (pyAction E K c ln (.str a) b r1).2.1) ∧
    norm (cAction E K ver c ln a (reg.map (fun _ => r1))).2.2.2 =
      norm (pyAction E K c ln (.str a) b r1).2.2 := by
  rcases ha with h | h | h | h | h <;> subst h <;> cases reg <;>
    simp [cAction, pyAction, norm, regSet, cTrue, one, hs]

theorem warnTwinsNarrow_proven : WarnTwinsNarrow := by
  intro E K fs ver c reg hv he hi hk hline hm hmsg hreg
  obtain ⟨v, hl, hv1, hv2⟩ := hline
  have hline' : ¬ (v > intMax ∨ v < -intMax - 1) := by omega
  have hfind := find_eq E c v fs hm he hi
  obtain ⟨htup, ⟨a, hda, hpa⟩, o, ho⟩ := hk
  obtain ⟨hmk, hglob, hlines⟩ := hmsg
  have hshow := show_eq E c he hlines
  have hnm : cListName K = .ok (if K.ctx then "_warnings_context _filters" else "filters") := by
    simp [cListName, htup]
  have hkey : Key.tri c.text c.cat v ≠ .version := by simp
  -- the chosen action is plain and a str
  have hplain : ∀ f, pyFind E c v fs = .ok (.some f) → ∃ s, f.action = .str s ∧ Plain s := by
    intro f hit
    have mem : ∀ fs' : List Item, ItemsOk fs' → pyFind E c v fs' = .ok (.some f) →
        ∃ s, f.action = .str s ∧ Plain s := by
      intro fs' hp hf'
      induction fs' with
      | nil => simp [pyFind, pure, Except.pure] at hf'
      | cons g gs ih =>
        obtain ⟨g', hg', hact, _⟩ := hp g (by simp)
        unfold IsTuple at hg'; subst hg'
        simp only [pyFind, bind, Except.bind] at hf'
        split at hf'
        · simp at hf'
        · rename_i bb _
          cases bb
          · exact ih (fun g'' hg'' => hp g'' (by simp [hg''])) hf'
          · simp [pure, Except.pure] at hf'; subst hf'; exact hact
    exact mem fs hi hit
  unfold Twins cWarnExplicit pyWarnExplicit
  simp only [hl, hmk, hglob, hnm]
  rw [if_neg hline']
  cases hcm : c.module with
  | none => simp [ModOk, hcm] at hm
  | obj => simp [ModOk, hcm] at hm
  | omitted | some s =>
    simp only

    rcases hreg with rfl | ⟨r, rfl, hrv⟩
    · have hk0 : truthy (regGet (pyRegPrep ver []) (.tri c.text c.cat v)) = false := by
        simp [pyRegPrep, regGet, regSet, Ne.symm hv, truthy]
      simp only [hk0, Bool.false_eq_true, if_false, hfind]
      cases hpf : pyFind E c v fs with
      | error e => simp
      | ok item =>
        cases item with
        | none =>
          obtain ⟨e1, e2, e3, e4⟩ := action_eq E K ver c v a (!fs.isEmpty) .none (pyRegPrep ver []) hpa hshow
          simp only [Option.map_none] at e1 e2 e3 e4
          simp only [cDefault, getWarningsAttr, if_true, ite_true, hda, withPending, Bool.false_or, e1, Bool.false_eq_true, if_false]
          exact ⟨e2, by simpa using e3, e4⟩
        | some f =>
          obtain ⟨s', hs', hps⟩ := hplain f hpf
          obtain ⟨e1, e2, e3, e4⟩ := action_eq E K ver c v s' true .none (pyRegPrep ver []) hps hshow
          simp only [Option.map_none] at e1 e2 e3 e4
          simp only [hs', withPending, Bool.false_or, e1, Bool.false_eq_true, if_false]
          exact ⟨e2, by simpa using e3, e4⟩
    · have haw := alreadyWarned_eq ver r (.tri c.text c.cat v) hv hkey hrv
      simp only [haw, hfind]
      by_cases hw : truthy (regGet (pyRegPrep ver r) (.tri c.text c.cat v)) = true
      · simp [hw, withPending]
      · simp only [hw, Bool.false_eq_true, if_false]
        cases hpf : pyFind E c v fs with
        | error e => simp
        | ok item =>
          cases item with
          | none =>
            obtain ⟨e1, e2, e3, e4⟩ := action_eq E K ver c v a (!fs.isEmpty) (.some r) (pyRegPrep ver r) hpa hshow
            simp only [Option.map_some] at e1 e2 e3 e4
            simp only [cDefault, getWarningsAttr, if_true, ite_true, hda, withPending, Bool.false_or, e1, Bool.false_eq_true, if_false]
            exact ⟨e2, by simpa using e3, e4⟩
          | some f =>
            obtain ⟨s', hs', hps⟩ := hplain f hpf
            obtain ⟨e1, e2, e3, e4⟩ := action_eq E K ver c v s' true (.some r) (pyRegPrep ver r) hps hshow
            simp only [Option.map_some] at e1 e2 e3 e4
            simp only [hs', withPending, Bool.false_or, e1, Bool.false_eq_true, if_false]
            exact ⟨e2, by simpa using e3, e4⟩

/-! ## `get_warnings_attr` -/

/-- `get_warnings_attr` (_warnings.c:224-256), which every module lookup of C `warn_explicit` goes
through: with `try_import`, an `ImportError` (or a subclass, such as `ModuleNotFoundError`) from
`import warnings` is cleared and the result is `NULL` with no error set (so `call_show_warning`
falls back to `show_warning`), any other import error propagates; without it, a `warnings` absent
from `sys.modules` is `NULL`; then a present attribute is returned, a missing one is `NULL`
(`PyObject_GetOptionalAttr` clears the `AttributeError`, where Python's `_wm.x` raises it), and
a lookup that raises propagates. Measured on 3.15.2: `sys.modules['warnings'] = None` makes
`warn_explicit` print through `show_warning`; a module whose `__getattr__` raises makes it raise. -/
def GetWarningsAttrSpec : Prop :=
  (∀ (α : Type) (e : PyExc) (attr : AttrR α) b, isA e "ImportError" = true →
    getWarningsAttr true (.error e) b attr = .ok none) ∧
  (∀ (α : Type) (e : PyExc) (attr : AttrR α) b, isA e "ImportError" = false →
    getWarningsAttr true (.error e) b attr = .error e) ∧
  (∀ (α : Type) (imp : Py Unit) (attr : AttrR α), getWarningsAttr false imp false attr = .ok none) ∧
  (∀ (α : Type) t (a : α), getWarningsAttr t (.ok ()) true (.found a) = .ok (some a)) ∧
  (∀ (α : Type) t, getWarningsAttr t (.ok ()) true (AttrR.missing : AttrR α) = .ok none) ∧
  (∀ (α : Type) t e, getWarningsAttr t (.ok ()) true (AttrR.raises e : AttrR α) = .error e)

theorem getWarningsAttrSpec_proven : GetWarningsAttrSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α e attr b h; simp [getWarningsAttr, h]
  · intro α e attr b h; simp [getWarningsAttr, h]
  · intro α imp attr; simp [getWarningsAttr]
  · intro α t a; cases t <;> simp [getWarningsAttr]
  · intro α t; cases t <;> simp [getWarningsAttr]
  · intro α t e; cases t <;> simp [getWarningsAttr]

/-- `ModuleNotFoundError` is an `ImportError`. -/
theorem moduleNotFound_isImportError : isA (.named "ModuleNotFoundError" "x") "ImportError" = true := by decide

/-! ## The cases left out, each refuted -/

/-- Two computed results that differ refute an equation between them. -/
theorem refute {α : Type} {a b x y : α} (h : a = b) (ha : a = x) (hb : b = y) (hxy : x ≠ y) :
    False := hxy (ha.symm.trans (h.trans hb))

/-- Callbacks that never raise, a trivial `_match_filename`, and a show step that succeeds. -/
def E0 : Env := ⟨fun _ _ => .ok true, fun _ _ => false, fun _ _ => .ok true, .call (.ok ()) (.ok ())⟩

/-- `warnings.filters` a list, `defaultaction` the given one, an empty once registry. -/
def K0 (d : String) : WCfg := ⟨false, false, .val (.str d), .dict []⟩

def call0 (ln : Int) (m : ModArg) : Call := ⟨"x", 1, "a.py", .int ln, m, .ok (), .none, .ok ()⟩

def rx (b : Bool) : Pat := .regex (fun _ => .ok b) true (.typeError "~expected string")

theorem envOk0 : EnvOk E0 := ⟨fun _ _ => ⟨true, rfl⟩, fun _ _ => ⟨true, rfl⟩, _, _, rfl⟩
theorem lineOk0 (ln : Int) (m : ModArg) (h1 : -intMax - 1 ≤ ln) (h2 : ln ≤ intMax) :
    LineOk (call0 ln m) := ⟨ln, rfl, h1, h2⟩
theorem modOk0 : ModOk (call0 1 (.some "a")) := Or.inr ⟨"a", rfl⟩
theorem msgOk0 (ln : Int) (m : ModArg) : MsgOk (call0 ln m) := ⟨rfl, rfl, rfl⟩
theorem regOk_dict_nil : RegOk (.dict []) := Or.inr ⟨[], rfl, by simp [regGet]⟩
theorem cfgOk0 (d : String) (h : Plain d) : CfgOk (K0 d) := ⟨rfl, ⟨d, rfl, h⟩, [], rfl⟩
theorem plainAlways : Plain "always" := Or.inr (Or.inr (Or.inl rfl))
theorem plainDefault : Plain "default" := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
theorem plainError : Plain "error" := Or.inl rfl
theorem plainIgnore : Plain "ignore" := Or.inr (Or.inl rfl)

/-- `once` is in scope: the documented "print only the first occurrence of matching warnings,
regardless of location" is what `_py_warnings` does with its global once registry, but the C code
uses the caller's registry when there is one (python/cpython#159792). -/
def WarnTwinsOnce : Prop :=
  ∀ E ver c reg o, ver ≠ 0 → EnvOk E → LineOk c → ModOk c → MsgOk c → RegOk reg →
    Twins E ⟨false, false, .val (.str "once"), .dict o⟩ [] ver c reg

theorem warnTwinsOnce_refuted : ¬ WarnTwinsOnce := fun h =>
  refute (h E0 1 (call0 1 (.some "a")) (.dict []) [(.pair "x" 1, one)] (by decide) envOk0
    (lineOk0 _ _ (by decide) (by decide)) modOk0 (msgOk0 _ _) regOk_dict_nil).1
    (x := .ok true) (y := .ok false) (by rfl) (by rfl) (by simp)

/-- `module` is in scope: Python marks "already shown in this module" with the key
`(text, category, 0)`, which is also the key of the warning itself when its line is 0. -/
def WarnTwinsModule : Prop :=
  ∀ E ver c reg, ver ≠ 0 → EnvOk E → LineOk c → ModOk c → MsgOk c → RegOk reg →
    Twins E (K0 "module") [] ver c reg

theorem warnTwinsModule_refuted : ¬ WarnTwinsModule := fun h =>
  refute (h E0 1 (call0 0 (.some "a")) (.dict []) (by decide) envOk0
    (lineOk0 _ _ (by decide) (by decide)) (Or.inr ⟨"a", rfl⟩) (msgOk0 _ _) regOk_dict_nil).1
    (x := .ok true) (y := .ok false) (by rfl) (by rfl) (by simp)

/-- Filter lines as `filterwarnings` accepts them (any int `>= 0`). -/
def WarnTwinsValidLines : Prop :=
  ∀ E fs ver c reg, ver ≠ 0 → EnvOk E →
    ItemsOkG IsTuple PlainAct TotalPat (fun l => ∃ v, l = .int v ∧ 0 ≤ v) fs →
    LineOk c → ModOk c → MsgOk c → RegOk reg → Twins E (K0 "default") fs ver c reg

def bigLine : Item := .tuple ⟨.str "error", .none, 1, .none, .int (2 ^ 63)⟩

theorem warnTwinsValidLines_refuted : ¬ WarnTwinsValidLines := fun h =>
  refute (h E0 [bigLine] 1 (call0 1 (.some "a")) .none (by decide) envOk0
    (by
      intro it hit; simp only [List.mem_singleton] at hit; subst hit
      exact ⟨_, rfl, ⟨"error", rfl, Or.inl rfl⟩, by simp, by simp, _, rfl, by decide⟩)
    (lineOk0 _ _ (by decide) (by decide)) modOk0 (msgOk0 _ _) (Or.inl rfl)).1
    (x := .error (.overflowError "Python int too large to convert to C ssize_t")) (y := .ok true)
    (by rfl) (by rfl) (by simp)

/-- A filter line that is not an int (only a filters list edited by hand holds one): C's
`PyLong_AsSsize_t` raises `TypeError`; Python's `ln == 0 or lineno == ln` is false. -/
def WarnTwinsLineObj : Prop :=
  ∀ E fs ver c reg, ver ≠ 0 → EnvOk E →
    ItemsOkG IsTuple PlainAct TotalPat (fun _ => True) fs →
    LineOk c → ModOk c → MsgOk c → RegOk reg → Twins E (K0 "default") fs ver c reg

theorem warnTwinsLineObj_refuted : ¬ WarnTwinsLineObj := fun h =>
  refute (h E0 [.tuple ⟨.str "error", .none, 1, .none, .obj "str"⟩] 1 (call0 1 (.some "a")) .none
    (by decide) envOk0
    (by
      intro it hit; simp only [List.mem_singleton] at hit; subst hit
      exact ⟨_, rfl, ⟨"error", rfl, Or.inl rfl⟩, by simp, by simp, trivial⟩)
    (lineOk0 _ _ (by decide) (by decide)) modOk0 (msgOk0 _ _) (Or.inl rfl)).1
    (x := .error (.typeError "an integer is required")) (y := .ok true)
    (by rfl) (by rfl) (by simp)

/-- Any exact int as the registry's `'version'`: C reads it with `PyLong_AsLong` and does not check
for an error, so `{'version': 2**64}` ends in `SystemError`. -/
def WarnTwinsAnyVersion : Prop :=
  ∀ E ver c r, ver ≠ 0 → EnvOk E → LineOk c → ModOk c → MsgOk c →
    Twins E (K0 "default") [] ver c (.dict r)

theorem warnTwinsAnyVersion_refuted : ¬ WarnTwinsAnyVersion := fun h =>
  refute (h E0 1 (call0 1 (.some "a")) [(.version, exactInt (2 ^ 64))] (by decide) envOk0
    (lineOk0 _ _ (by decide) (by decide)) modOk0 (msgOk0 _ _)).1
    (x := .error leaked) (y := .ok true) (by rfl) (by rfl) (by simp)

/-- The invariant on its own: C `warn_explicit` never leaks an internal error. -/
def NoSystemError : Prop :=
  ∀ E K fs ver c reg, (cWarnExplicit E K fs ver c reg).out ≠ .error leaked

theorem noSystemError_refuted : ¬ NoSystemError := fun h =>
  h E0 (K0 "default") [] 1 (call0 1 (.some "a")) (.dict [(.version, exactInt (2 ^ 64))]) (by rfl)

/-- A `'version'` that is not an exact int (`True`, an int subclass): C treats the registry as
stale and clears it; Python compares with `!=`, so `True` passes for version 1. -/
def WarnTwinsInexactVersion : Prop :=
  ∀ E ver c r, ver ≠ 0 → EnvOk E → LineOk c → ModOk c → MsgOk c →
    (∀ v, regGet r .version = .some v → -longMax - 1 ≤ v.n ∧ v.n ≤ longMax) →
    Twins E (K0 "default") [] ver c (.dict r)

theorem warnTwinsInexactVersion_refuted : ¬ WarnTwinsInexactVersion := fun h =>
  refute (h E0 1 (call0 1 (.some "a")) [(.version, ⟨1, false⟩), (.tri "x" 1 1, one)] (by decide)
    envOk0 (lineOk0 _ _ (by decide) (by decide)) modOk0 (msgOk0 _ _)
    (by intro v hv; simp [regGet] at hv; subst hv; decide)).1
    (x := .ok true) (y := .ok false) (by rfl) (by rfl) (by simp)

/-- Callbacks that raise: C runs the message test, the module test and `issubclass` before it
looks at any of them; Python stops at the first that fails. -/
def WarnTwinsRaising : Prop :=
  ∀ E fs ver c reg, ver ≠ 0 → (∃ wm fn, E.shw = .call wm fn) →
    ItemsOkG IsTuple PlainAct AnyRegex LnFits fs → LineOk c → ModOk c →
    MsgOk c → RegOk reg → Twins E (K0 "always") fs ver c reg

def Eraise : Env := ⟨fun _ _ => .error (.keyError "boom"), fun _ _ => true, fun _ _ => .ok true, .call (.ok ()) (.ok ())⟩
def noMatch : Item := .tuple ⟨.str "error", .some (rx false), 1, .none, .int 0⟩

theorem warnTwinsRaising_refuted : ¬ WarnTwinsRaising := fun h =>
  refute (h Eraise [noMatch] 1 (call0 1 (.some "a")) .none (by decide) ⟨_, _, rfl⟩
    (by
      intro it hit; simp only [List.mem_singleton] at hit; subst hit
      refine ⟨_, rfl, ⟨"error", rfl, Or.inl rfl⟩, ?_, by simp, _, rfl, by simp [ssizeMax]⟩
      intro p hp; simp at hp; subst hp; exact ⟨_, _, _, rfl⟩)
    (lineOk0 _ _ (by decide) (by decide)) modOk0 (msgOk0 _ _) (Or.inl rfl)).1
    (x := .error (.keyError "boom")) (y := .ok true) (by rfl) (by rfl) (by simp)

/-- A filter whose pattern is a plain str, as C's internal default filters are: C compares it
with the module name; Python calls its `match` and raises `AttributeError`. -/
def WarnTwinsPlainFilter : Prop :=
  ∀ E fs ver c reg, ver ≠ 0 → EnvOk E → ItemsOkG IsTuple PlainAct (fun _ => True) LnFits fs →
    LineOk c → ModOk c → MsgOk c → RegOk reg → Twins E (K0 "always") fs ver c reg

def plainItem : Item := .tuple ⟨.str "ignore", .none, 1, .some (.plain "a"), .int 0⟩

theorem warnTwinsPlainFilter_refuted : ¬ WarnTwinsPlainFilter := fun h =>
  refute (h E0 [plainItem] 1 (call0 1 (.some "a")) .none (by decide) envOk0
    (by
      intro it hit; simp only [List.mem_singleton] at hit; subst hit
      exact ⟨_, rfl, ⟨"ignore", rfl, Or.inr (Or.inl rfl)⟩, by simp, by simp, _, rfl, by simp [ssizeMax]⟩)
    (lineOk0 _ _ (by decide) (by decide)) modOk0 (msgOk0 _ _) (Or.inl rfl)).1
    (x := .ok false) (y := .error noMatchAttr) (by rfl) (by rfl) (by simp)

/-- A filters-list item that is a 5-element list, or an action that is not a str: C refuses
both (`ValueError`, `TypeError`); Python unpacks the list and treats the action as unknown (or,
unhashable, raises `TypeError` from `action in {"always", "all"}`). -/
def WarnTwinsItemShape : Prop :=
  ∀ E fs ver c reg, ver ≠ 0 → EnvOk E →
    ItemsOkG (fun it f => it = .tuple f ∨ it = .list5 f) (fun _ => True) TotalPat LnFits fs →
    LineOk c → ModOk c → MsgOk c → RegOk reg → Twins E (K0 "always") fs ver c reg

def listItem : Item := .list5 ⟨.str "always", .none, 1, .none, .int 0⟩
def noStrAction : Item := .tuple ⟨.hashable "int", .none, 1, .none, .int 0⟩
def unhashAction : Item := .tuple ⟨.unhashable "list", .none, 1, .none, .int 0⟩

theorem warnTwinsItemShape_refuted : ¬ WarnTwinsItemShape := fun h =>
  refute (h E0 [listItem] 1 (call0 1 (.some "a")) .none (by decide) envOk0
    (by
      intro it hit; simp only [List.mem_singleton] at hit; subst hit
      exact ⟨_, Or.inr rfl, trivial, by simp, by simp, _, rfl, by simp [ssizeMax]⟩)
    (lineOk0 _ _ (by decide) (by decide)) modOk0 (msgOk0 _ _) (Or.inl rfl)).1
    (x := .error (notTuple 0)) (y := .ok true) (by rfl) (by rfl) (by simp [notTuple, notTupleIn])

theorem warnTwinsItemShape_refuted_action : ¬ WarnTwinsItemShape := fun h =>
  refute (h E0 [noStrAction] 1 (call0 1 (.some "a")) .none (by decide) envOk0
    (by
      intro it hit; simp only [List.mem_singleton] at hit; subst hit
      exact ⟨_, Or.inl rfl, trivial, by simp, by simp, _, rfl, by simp [ssizeMax]⟩)
    (lineOk0 _ _ (by decide) (by decide)) modOk0 (msgOk0 _ _) (Or.inl rfl)).1
    (x := .error actionTypeErr) (y := .error unrecognized) (by rfl) (by rfl)
    (by simp [actionTypeErr, unrecognized])

/-- An unhashable action: Python's `action in {"always", "all"}` (:601) raises `TypeError` about
hashing; C raises its own `TypeError` ("action must be a string") with another message. -/
theorem warnTwinsItemShape_refuted_unhashable : ¬ WarnTwinsItemShape := fun h =>
  refute (h E0 [unhashAction] 1 (call0 1 (.some "a")) .none (by decide) envOk0
    (by
      intro it hit; simp only [List.mem_singleton] at hit; subst hit
      exact ⟨_, Or.inl rfl, trivial, by simp, by simp, _, rfl, by simp [ssizeMax]⟩)
    (lineOk0 _ _ (by decide) (by decide)) modOk0 (msgOk0 _ _) (Or.inl rfl)).1
    (x := .error actionTypeErr) (y := .error (unhashableErr "list")) (by rfl) (by rfl)
    (by simp [actionTypeErr, unhashableErr]; decide)

/-- `module=None` passed explicitly: C returns at once (_warnings.c:812-813, meant for interpreter
shutdown); Python treats it as omitted and applies the filters. -/
def WarnTwinsNoneModule : Prop :=
  ∀ E ver c reg, ver ≠ 0 → EnvOk E → LineOk c → MsgOk c → RegOk reg →
    Twins E (K0 "error") [] ver c reg

theorem warnTwinsNoneModule_refuted : ¬ WarnTwinsNoneModule := fun h =>
  refute (h E0 1 (call0 1 .none) .none (by decide) envOk0 (lineOk0 _ _ (by decide) (by decide))
    (msgOk0 _ _) (Or.inl rfl)).1
    (x := .ok false) (y := .error (warnRaised (call0 1 .none))) (by rfl) (by rfl) (by simp)

/-- A `module` that is not a str: C calls the module pattern on it even when the message pattern
did not match; Python never gets that far. -/
def WarnTwinsModuleObj : Prop :=
  ∀ E fs ver c reg, ver ≠ 0 → EnvOk E → ItemsOkG IsTuple PlainAct AnyRegex LnFits fs →
    LineOk c → MsgOk c → RegOk reg → c.module ≠ .none → Twins E (K0 "always") fs ver c reg

def objItem : Item := .tuple ⟨.str "error", .some (rx false), 1, .some (rx true), .int 0⟩

theorem warnTwinsModuleObj_refuted : ¬ WarnTwinsModuleObj := fun h =>
  refute (h E0 [objItem] 1 (call0 1 .obj) .none (by decide) envOk0
    (by
      intro it hit; simp only [List.mem_singleton] at hit; subst hit
      refine ⟨_, rfl, ⟨"error", rfl, Or.inl rfl⟩, ?_, ?_, _, rfl, by simp [ssizeMax]⟩ <;>
      · intro p hp; simp at hp; subst hp; exact ⟨_, _, _, rfl⟩)
    (lineOk0 _ _ (by decide) (by decide)) (msgOk0 _ _) (Or.inl rfl) (by simp [call0])).1
    (x := .error (.typeError "~expected string")) (y := .ok true) (by rfl) (by rfl) (by simp)

/-- Any line: C's `int` converter refuses a line outside C `int` and anything that is not an int;
Python's `int(lineno)` takes both. -/
def WarnTwinsAnyLine : Prop :=
  ∀ E ver c reg, ver ≠ 0 → EnvOk E → ModOk c → MsgOk c → RegOk reg →
    Twins E (K0 "always") [] ver c reg

theorem warnTwinsAnyLine_refuted : ¬ WarnTwinsAnyLine := fun h =>
  refute (h E0 1 (call0 (2 ^ 31) (.some "a")) .none (by decide) envOk0 (Or.inr ⟨"a", rfl⟩)
    (msgOk0 _ _) (Or.inl rfl)).1
    (x := .error (.overflowError "Python int too large to convert to C int")) (y := .ok true)
    (by rfl) (by rfl) (by simp)

def callObjLine : Call := ⟨"x", 1, "a.py", .obj (.ok 5) (.typeError "~an integer is required"), .some "a",
  .ok (), .none, .ok ()⟩

theorem warnTwinsAnyLine_refuted_obj : ¬ WarnTwinsAnyLine := fun h =>
  refute (h E0 1 callObjLine .none (by decide) envOk0 (Or.inr ⟨"a", rfl⟩) ⟨rfl, rfl, rfl⟩ (Or.inl rfl)).1
    (x := .error (.typeError "~an integer is required")) (y := .ok true) (by rfl) (by rfl) (by simp)

/-- A registry that is neither a dict nor `None`: C raises `TypeError`; Python uses any mapping
(and raises `AttributeError` from `registry.get` for an object with no `get`). -/
def WarnTwinsRegObj : Prop :=
  ∀ E ver c reg, ver ≠ 0 → EnvOk E → LineOk c → ModOk c → MsgOk c →
    Twins E (K0 "always") [] ver c reg

theorem warnTwinsRegObj_refuted : ¬ WarnTwinsRegObj := fun h =>
  refute (h E0 1 (call0 1 (.some "a")) .obj (by decide) envOk0 (lineOk0 _ _ (by decide) (by decide))
    modOk0 (msgOk0 _ _)).1
    (x := .error regTypeErr) (y := .error noGetAttr) (by rfl) (by rfl) (by simp [regTypeErr, noGetAttr])

/-- A mapping registry that is not a dict: C refuses it, Python shows the warning. -/
theorem warnTwinsRegObj_refuted_mapping : ¬ WarnTwinsRegObj := fun h =>
  refute (h E0 1 (call0 1 (.some "a")) (.mapping []) (by decide) envOk0
    (lineOk0 _ _ (by decide) (by decide)) modOk0 (msgOk0 _ _)).1
    (x := .error regTypeErr) (y := .ok true) (by rfl) (by rfl) (by simp)

/-- A message that cannot be built (`category(message)` or `str(message)` raising): Python builds it
first; C checks `module` and the registry before. -/
def WarnTwinsMsgRaises : Prop :=
  ∀ E ver c reg, ver ≠ 0 → EnvOk E → LineOk c → ModOk c → c.globs = .none → c.pyLines = .ok () →
    Twins E (K0 "always") [] ver c reg

def callBadMsg : Call := ⟨"x", 1, "a.py", .int 1, .some "a", .error (.valueError "bad message"), .none, .ok ()⟩

theorem warnTwinsMsgRaises_refuted : ¬ WarnTwinsMsgRaises := fun h =>
  refute (h E0 1 callBadMsg .obj (by decide) envOk0 ⟨1, rfl, by decide, by decide⟩ (Or.inr ⟨"a", rfl⟩)
    rfl rfl).1
    (x := .error regTypeErr) (y := .error (.valueError "bad message")) (by rfl) (by rfl)
    (by simp [regTypeErr])

/-- An action that is a str but no known action: both raise `RuntimeError`, but C has already
stored the warning in the registry. -/
def WarnTwinsUnknownAction : Prop :=
  ∀ E ver c reg, ver ≠ 0 → EnvOk E → LineOk c → ModOk c → MsgOk c → RegOk reg →
    Twins E (K0 "bogus") [] ver c reg

theorem warnTwinsUnknownAction_refuted : ¬ WarnTwinsUnknownAction := fun h =>
  refute (h E0 1 (call0 1 (.some "a")) (.dict []) (by decide) envOk0
    (lineOk0 _ _ (by decide) (by decide)) modOk0 (msgOk0 _ _) regOk_dict_nil).2.1
    (x := .some [(.tri "x" 1 1, 1), (.version, 1)]) (y := .some [(.version, 1)])
    (by rfl) (by rfl) (by simp)

/-- A `defaultaction` that is not a str: C raises `TypeError` naming it; Python reaches its
unknown-action branch. -/
def WarnTwinsDfltType : Prop :=
  ∀ E ver c reg, ver ≠ 0 → EnvOk E → LineOk c → ModOk c → MsgOk c → RegOk reg →
    Twins E ⟨false, false, .val (.hashable "int"), .dict []⟩ [] ver c reg

theorem warnTwinsDfltType_refuted : ¬ WarnTwinsDfltType := fun h =>
  refute (h E0 1 (call0 1 (.some "a")) .none (by decide) envOk0
    (lineOk0 _ _ (by decide) (by decide)) modOk0 (msgOk0 _ _) (Or.inl rfl)).1
    (x := .error dfltTypeErr) (y := .error unboundItem) (by rfl) (by rfl) (by simp [dfltTypeErr, unboundItem])

/-- An unknown action raises `RuntimeError` in `_py_warnings`, as it does in C. With no filters
the message formats `item`, which the empty loop never bound: `UnboundLocalError`. -/
def PyUnknownActionRaises : Prop :=
  ∀ E ver c reg, ver ≠ 0 → EnvOk E → LineOk c → ModOk c → MsgOk c →
    (cWarnExplicit E (K0 "bogus") [] ver c reg).out = .error unrecognized →
    (pyWarnExplicit E (K0 "bogus") [] ver c reg).out = .error unrecognized

theorem pyUnknownActionRaises_refuted : ¬ PyUnknownActionRaises := fun h =>
  refute (h E0 1 (call0 1 (.some "a")) .none (by decide) envOk0 (lineOk0 _ _ (by decide) (by decide))
    modOk0 (msgOk0 _ _) (by rfl)) (y := .error unrecognized) (x := .error unboundItem) (by rfl) rfl
    (by simp [unboundItem, unrecognized])

/-! ## The module state, the show step and `module_globals`, each refuted -/

/-- Every state of the module attributes `warn_explicit` reads: the filters container, the
context, `defaultaction`, `onceregistry`, and the show step's `_showwarnmsg` and
`WarningMessage`. -/
def WarnTwinsModuleState : Prop :=
  ∀ (E : Env) K ver c reg, ver ≠ 0 → (∀ a b, ∃ x, E.isSub a b = .ok x) →
    LineOk c → ModOk c → MsgOk c → RegOk reg → Twins E K [] ver c reg

def Eshow (s : ShowA) : Env := ⟨fun _ _ => .ok true, fun _ _ => false, fun _ _ => .ok true, s⟩

/-- `warnings.filters` a tuple: C's `get_warnings_filters` refuses it (:356-360); Python iterates it. -/
theorem warnTwinsModuleState_refuted_tuple : ¬ WarnTwinsModuleState := fun h =>
  refute (h E0 ⟨false, true, .val (.str "always"), .dict []⟩ 1 (call0 1 (.some "a")) .none (by decide)
    (fun _ _ => ⟨_, rfl⟩) (lineOk0 _ _ (by decide) (by decide)) modOk0 (msgOk0 _ _) (Or.inl rfl)).1
    (x := .error (.valueError "_warnings.filters must be a list")) (y := .ok true) (by rfl) (by rfl) (by simp)

/-- The context's `_filters` a tuple: C refuses it too (:332-337). -/
theorem warnTwinsModuleState_refuted_ctxTuple : ¬ WarnTwinsModuleState := fun h =>
  refute (h E0 ⟨true, true, .val (.str "always"), .dict []⟩ 1 (call0 1 (.some "a")) .none (by decide)
    (fun _ _ => ⟨_, rfl⟩) (lineOk0 _ _ (by decide) (by decide)) modOk0 (msgOk0 _ _) (Or.inl rfl)).1
    (x := .error (.valueError "_filters of warnings._warnings_context must be a list")) (y := .ok true)
    (by rfl) (by rfl) (by simp)

/-- `warnings._showwarnmsg` deleted: C falls back to `show_warning` (:750-755) and returns;
Python raises `AttributeError`. -/
theorem warnTwinsModuleState_refuted_show : ¬ WarnTwinsModuleState := fun h =>
  refute (h (Eshow .deleted) (K0 "always") 1 (call0 1 (.some "a")) .none (by decide)
    (fun _ _ => ⟨_, rfl⟩) (lineOk0 _ _ (by decide) (by decide)) modOk0 (msgOk0 _ _) (Or.inl rfl)).1
    (x := .ok true) (y := .error (noModAttr "_showwarnmsg")) (by rfl) (by rfl) (by simp)

/-- `warnings.onceregistry` not a dict: C's `get_once_registry` raises `TypeError` (:416-422);
Python's `.get` raises `AttributeError`. -/
theorem warnTwinsModuleState_refuted_once : ¬ WarnTwinsModuleState := fun h =>
  refute (h E0 ⟨false, false, .val (.str "once"), .notDict "int" []⟩ 1 (call0 1 (.some "a")) .none
    (by decide) (fun _ _ => ⟨_, rfl⟩) (lineOk0 _ _ (by decide) (by decide)) modOk0 (msgOk0 _ _)
    (Or.inl rfl)).1
    (x := .error (.typeError "_warnings.onceregistry must be a dict, not 'int'"))
    (y := .error noGetAttr) (by rfl) (by rfl) (by simp [noGetAttr])

/-- `warnings.defaultaction` deleted: C uses the str it read last (:437-444); Python raises
`AttributeError`. -/
theorem warnTwinsModuleState_refuted_dflt : ¬ WarnTwinsModuleState := fun h =>
  refute (h E0 ⟨false, false, .deleted "always", .dict []⟩ 1 (call0 1 (.some "a")) .none
    (by decide) (fun _ _ => ⟨_, rfl⟩) (lineOk0 _ _ (by decide) (by decide)) modOk0 (msgOk0 _ _)
    (Or.inl rfl)).1
    (x := .ok true) (y := .error (noModAttr "defaultaction")) (by rfl) (by rfl) (by simp)

/-- `module_globals` given: C checks it and runs `get_source_line` before anything else
(:1328-1341), so even an ignored warning raises; Python only passes it to `linecache.getlines`
when it shows the warning. -/
def WarnTwinsGlobals : Prop :=
  ∀ E ver c reg, ver ≠ 0 → EnvOk E → LineOk c → ModOk c → c.mkMsg = .ok () → c.pyLines = .ok () →
    RegOk reg → Twins E (K0 "ignore") [] ver c reg

theorem warnTwinsGlobals_refuted : ¬ WarnTwinsGlobals := fun h =>
  refute (h E0 1 { call0 1 (.some "a") with globs := .obj "int" } .none (by decide) envOk0
    ⟨1, rfl, by decide, by decide⟩ modOk0 rfl rfl (Or.inl rfl)).1
    (x := .error (.typeError "module_globals must be a dict or a frozendict, not int")) (y := .ok false)
    (by rfl) (by rfl) (by simp)

/-- A dict whose loader's `get_source` raises: the same, from `get_source_line`. -/
theorem warnTwinsGlobals_refuted_loader : ¬ WarnTwinsGlobals := fun h =>
  refute (h E0 1 { call0 1 (.some "a") with globs := .dict (.error (.valueError "no source")) } .none
    (by decide) envOk0 ⟨1, rfl, by decide, by decide⟩ modOk0 rfl rfl (Or.inl rfl)).1
    (x := .error (.valueError "no source")) (y := .ok false) (by rfl) (by rfl) (by simp)

end PyLean.CoreLibs.Warn
