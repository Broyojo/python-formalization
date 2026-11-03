import PyLean.CoreLibs.Warn.Option
import PyLean.CoreLibs.Warn.FiltersProps

/-!
Properties of the `-W` parser (`Option.lean`).
-/

namespace PyLean.CoreLibs.Warn

open PyLean

theorem bind_err {α β : Type} {x : Py α} {f : α → Py β} {e : PyExc} (h : (x >>= f) = .error e) :
    x = .error e ∨ ∃ v, x = .ok v ∧ f v = .error e := by
  cases x with
  | error e' =>
    left
    simp only [bind, Except.bind, Except.error.injEq] at h
    rw [h]
  | ok v => exact Or.inr ⟨v, rfl, h⟩

theorem bind_ok {α β : Type} {x : Py α} {f : α → Py β} {r : β} (h : (x >>= f) = .ok r) :
    ∃ v, x = .ok v ∧ f v = .ok r := by
  cases x with
  | error e' => simp [bind, Except.bind] at h
  | ok v => exact ⟨v, rfl, h⟩

theorem str'_isEmpty (l : List Char) : (str' l).isEmpty = l.isEmpty := by
  cases h : l.isEmpty
  · have hne : str' l ≠ "" := by
      intro hl
      have := String.ofList_eq_empty_iff.mp hl
      simp [this] at h
    exact String.isEmpty_eq_false_iff.mpr hne
  · have : l = [] := List.isEmpty_iff.mp h
    subst this
    rfl

/-! ## `_getaction` -/

/-- `_getaction` (:410-416; the `-W` documentation lets the action be abbreviated): every action
name stands for itself, the empty field for `default`, and every answer is an action name that
the field abbreviates; anything else is an `_OptionError`. -/
def GetactionSpec : Prop :=
  (∀ n ∈ actionOrder, getaction n.toList = .ok n) ∧ getaction [] = .ok "default" ∧
  (∀ a n, getaction a = .ok n → n ∈ actionNames ∧ a.isPrefixOf n.toList = true) ∧
  (∀ a e, getaction a = .error e → e.className = "_OptionError")

theorem getactionSpec_proven : GetactionSpec := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro n hn
    simp only [actionOrder, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro a n h
    unfold getaction at h
    cases ha : a.isEmpty
    · simp only [ha, Bool.false_eq_true, if_false] at h
      cases hf : actionOrder.find? (fun n => a.isPrefixOf n.toList) with
      | none => simp [hf] at h
      | some x =>
        simp only [hf, Except.ok.injEq] at h
        subst h
        have hm := List.mem_of_find?_eq_some hf
        have hp := List.find?_some hf
        refine ⟨?_, hp⟩
        simp only [actionOrder, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [actionNames]
    · simp only [ha, if_true, Except.ok.injEq] at h
      subst h
      simp [List.isEmpty_iff.mp ha, actionNames]
  · intro a e h
    unfold getaction at h
    cases ha : a.isEmpty
    · simp only [ha, Bool.false_eq_true, if_false] at h
      cases hf : actionOrder.find? (fun n => a.isPrefixOf n.toList) with
      | none =>
        simp only [hf, Except.error.injEq] at h
        subst h
        rfl
      | some x => simp [hf] at h
    · simp [ha] at h

theorem find?_first {α : Type} [DecidableEq α] (P : α → Bool) (l : List α) (n : α) (hn : n ∈ l)
    (hpre : ∀ x ∈ l.takeWhile (· ≠ n), P x = false) (hP : P n = true) : l.find? P = some n := by
  induction l with
  | nil => simp at hn
  | cons x xs ih =>
    by_cases hx : x = n
    · subst hx; simp [List.find?, hP]
    · have hxP : P x = false := hpre x (by simp [List.takeWhile, hx])
      simp only [List.find?, hxP]
      have hn' : n ∈ xs := by
        simp only [List.mem_cons] at hn
        rcases hn with h | h
        · exact absurd h.symm hx
        · exact h
      exact ih hn' (fun y hy => hpre y (by simp only [List.takeWhile, hx, ne_eq, not_false_eq_true, decide_true, List.mem_cons]; exact Or.inr hy))

/-- The abbreviation of the `-W` action (the documentation: "the action ... may be abbreviated"):
a non-empty prefix of an action name stands for that name unless it is also a prefix of a name
earlier in `default, always, all, ignore, module, once, error` (so `a` and `al` are `always`,
`i` is `ignore`, `m` is `module`, `o` is `once`, `e` is `error`). -/
def GetactionAbbrev : Prop :=
  ∀ n ∈ actionOrder, ∀ p : List Char, p ≠ [] → p.isPrefixOf n.toList = true →
    (∀ n' ∈ actionOrder.takeWhile (· ≠ n), p.isPrefixOf n'.toList = false) → getaction p = .ok n

theorem getactionAbbrev_proven : GetactionAbbrev := by
  intro n hn p hp hpre hearly
  have hne : p.isEmpty = false := by cases p <;> simp_all
  unfold getaction
  rw [hne, find?_first _ actionOrder n hn hearly hpre]
  rfl

/-! ## What escapes `_processoptions` -/

/-- The environment the narrow property assumes: imports raise only `ImportError` (the empty
module name, for which `__import__` raises `ValueError`, is the refuted case), `getattr` only
`AttributeError`, every attribute found is a class, `Warning` is a Warning class, and `re.compile`
raises only `re.PatternError`, the same with or without `re.I`. -/
def OptEnvOk (E : OEnv) : Prop :=
  (∀ m k e, E.imp m k = .error e → isImportErr E.fenv.hier e = true) ∧
  (∀ m k e, E.getattr m k = .error e → isA E.fenv.hier e "AttributeError" = true) ∧
  (∀ m k, E.getattr m k ≠ .ok .nonclass) ∧
  (∀ m k i, E.getattr m k = .ok (.cls i) → E.fenv.isType i = true) ∧
  E.fenv.isType E.warning = true ∧ E.fenv.isWarn E.warning = true ∧
  (∀ p ci e, E.fenv.compile p ci = .error e → isPatternErr e = true) ∧
  (∀ p, E.fenv.compile p true = E.fenv.compile p false)

/-- The filters list `_processoptions` adds to: a list whose elements' `==` does not raise. -/
def ListOk (s : FState) : Prop := ∃ xs, s.cont = .list xs ∧ ∀ it, EqTotal it xs

theorem gcModule_err (E : OEnv) (h : OptEnvOk E) (c : List Char) (e : PyExc)
    (hc : gcModule E c = .error e) : e.className = "_OptionError" := by
  unfold gcModule at hc
  split at hc
  · simp at hc
  · split at hc
    split at hc
    · simp at hc
    · rename_i e2 himpe
      split at hc
      · simp only [Except.error.injEq] at hc; subst hc; rfl
      · rename_i hni; exact absurd (h.1 _ _ _ himpe) hni

theorem gcAttr_err (E : OEnv) (h : OptEnvOk E) (c : List Char) m k (e : PyExc)
    (hc : gcAttr E c m k = .error e) : e.className = "_OptionError" := by
  unfold gcAttr at hc
  split at hc
  · simp at hc
  · rename_i e2 hge
    split at hc
    · simp only [Except.error.injEq] at hc; subst hc; rfl
    · rename_i hna
      have := h.2.1 _ _ _ hge
      simp_all

theorem gcAttr_ok (E : OEnv) (c : List Char) m k (o : Found) (hc : gcAttr E c m k = .ok o) :
    E.getattr m k = .ok o := by
  unfold gcAttr at hc
  split at hc
  · rename_i o' hg; simp only [Except.ok.injEq] at hc; rw [← hc]; exact hg
  · split at hc <;> simp at hc

theorem gcCheck_err (E : OEnv) (c : List Char) (o : Found) (ho : o ≠ .nonclass) (e : PyExc)
    (hc : gcCheck E c o = .error e) : e.className = "_OptionError" := by
  cases o with
  | nonclass => exact absurd rfl ho
  | cls k =>
    simp only [gcCheck] at hc
    split at hc
    · simp at hc
    · simp only [Except.error.injEq] at hc; subst hc; rfl

theorem getcategory_ok (E : OEnv) (h : OptEnvOk E) (c : List Char) (i : Nat)
    (hc : getcategory E c = .ok i) : E.fenv.isType i = true ∧ E.fenv.isWarn i = true := by
  obtain ⟨_, _, hnc, hty, hwt, hww, _, _⟩ := h
  unfold getcategory at hc
  split at hc
  · simp only [Except.ok.injEq] at hc; subst hc; exact ⟨hwt, hww⟩
  · obtain ⟨⟨m, k⟩, _, hc⟩ := bind_ok hc
    obtain ⟨o, ho, hc⟩ := bind_ok hc
    have hga := gcAttr_ok E c m k o ho
    cases o with
    | nonclass => exact absurd hga (hnc _ _)
    | cls k' =>
      simp only [gcCheck] at hc
      split at hc
      · rename_i hw
        simp only [Except.ok.injEq] at hc; subst hc
        exact ⟨hty _ _ _ hga, hw⟩
      · simp at hc

theorem getcategory_err (E : OEnv) (h : OptEnvOk E) (c : List Char) (e : PyExc)
    (hc : getcategory E c = .error e) : e.className = "_OptionError" := by
  unfold getcategory at hc
  split at hc
  · simp at hc
  · rcases bind_err hc with h1 | ⟨⟨m, k⟩, _, hc⟩
    · exact gcModule_err E h c e h1
    · rcases bind_err hc with h2 | ⟨o, ho, hc⟩
      · exact gcAttr_err E h c m k e h2
      · exact gcCheck_err E c o (fun hn => h.2.2.1 m k (hn ▸ gcAttr_ok E c m k o ho)) e hc

theorem soLineno_ok (l : List Char) (v : Int) (h : soLineno l = .ok v) : 0 ≤ v := by
  unfold soLineno at h
  split at h
  · simp only [Except.ok.injEq] at h; omega
  · split at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq] at h; omega
    · simp at h

theorem soLineno_err (l : List Char) (e : PyExc) (h : soLineno l = .error e) :
    e.className = "_OptionError" := by
  unfold soLineno at h
  split at h
  · simp at h
  · split at h
    · split at h
      · simp only [Except.error.injEq] at h; subst h; rfl
      · simp at h
    · simp only [Except.error.injEq] at h; subst h; rfl

theorem soParse_err (E : OEnv) (h : OptEnvOk E) (arg : List Char) (e : PyExc)
    (hp : soParse E arg = .error e) : e.className = "_OptionError" := by
  unfold soParse at hp
  dsimp only at hp
  split at hp
  · simp only [Except.error.injEq] at hp; subst hp; rfl
  · rcases bind_err hp with h1 | ⟨a, _, hp⟩
    · exact getactionSpec_proven.2.2.2 _ _ h1
    · rcases bind_err hp with h2 | ⟨cat, _, hp⟩
      · exact getcategory_err E h _ _ h2
      · rcases bind_err hp with h3 | ⟨ln, _, hp⟩
        · exact soLineno_err _ _ h3
        · simp at hp

theorem soParse_ok (E : OEnv) (h : OptEnvOk E) (arg : List Char) a cat m md ln
    (hp : soParse E arg = .ok (a, cat, m, md, ln)) :
    a ∈ actionNames ∧ E.fenv.isType cat = true ∧ E.fenv.isWarn cat = true ∧ 0 ≤ ln := by
  unfold soParse at hp
  dsimp only at hp
  split at hp
  · simp at hp
  · obtain ⟨a', ha, hp⟩ := bind_ok hp
    obtain ⟨cat', hc, hp⟩ := bind_ok hp
    obtain ⟨ln', hl, hp⟩ := bind_ok hp
    simp only [Except.ok.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl, _, _, rfl⟩ := hp
    exact ⟨(getactionSpec_proven.2.2.1 _ _ ha).1, (getcategory_ok E h _ _ hc).1,
      (getcategory_ok E h _ _ hc).2, soLineno_ok _ _ hl⟩

theorem addSpec_mem (it : FItem) (ap : Bool) (xs : List Elem) (e : Elem) (h : e ∈ addSpec it ap xs) :
    e ∈ xs ∨ e = .item it := by
  unfold addSpec at h
  split at h
  · split at h
    · exact Or.inl h
    · simp only [List.mem_append, List.mem_singleton] at h; exact h
  · simp only [List.mem_cons] at h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl (List.mem_of_mem_eraseP h)

theorem listOk_add (it : FItem) (ap : Bool) (xs : List Elem) (h : ∀ it, EqTotal it xs) :
    ∀ it', EqTotal it' (addSpec it ap xs) := by
  intro it' e he
  rcases addSpec_mem it ap xs e he with h1 | h1
  · exact h it' e h1
  · subst h1; exact ⟨_, rfl⟩

/-- `soInstall` with what `soParse` gives, on a good list: it succeeds with a good list, or names
the bad field in an `_OptionError`. -/
theorem soInstall_ok_or_opt (E : OEnv) (h : OptEnvOk E) (a : String) (ha : a ∈ actionNames) (cat : Nat)
    (ht : E.fenv.isType cat = true) (hw : E.fenv.isWarn cat = true) (m md : List Char) (ln : Int)
    (hl : 0 ≤ ln) (s : FState) (hs : ListOk s) :
    (∃ s', soInstall E.fenv a cat m md ln s = .ok s' ∧ ListOk s') ∨
    (∃ e, soInstall E.fenv a cat m md ln s = .error e ∧ e.className = "_OptionError") := by
  obtain ⟨_, _, _, _, _, _, hpat, hflag⟩ := h
  obtain ⟨xs, hxs, htot⟩ := hs
  have hca : checkAction (.str a) = .ok a := by simp [checkAction, ha]
  have hcl : checkLineno (.int ln) = .ok ln := by simp [checkLineno]; omega
  have prep : fwPrep E.fenv (.str a) (.str (str' m)) cat (.str (str' md)) (.int ln) =
      (do let mrx ← compileOpt E.fenv (str' m) true
          let drx ← compileOpt E.fenv (str' md) false
          return (⟨a, mrx, cat, drx, ln⟩ : FItem)) := by
    simp [fwPrep, hca, hcl, ht, hw, bind, Except.bind, pure, Except.pure]
  unfold soInstall filterwarnings
  rw [prep]
  cases hm : compileOpt E.fenv (str' m) true with
  | error e1 =>
    -- the message pattern does not compile
    right
    have hne : m.isEmpty = false := by
      cases hme : m.isEmpty
      · rfl
      · simp [compileOpt, str'_isEmpty, hme] at hm
    have hc1 : E.fenv.compile (str' m) true = .error e1 := by
      unfold compileOpt at hm
      rw [str'_isEmpty, hne] at hm
      simp only [Bool.false_eq_true, if_false, bind, Except.bind] at hm
      cases hc : E.fenv.compile (str' m) true with
      | error e' => simp [hc] at hm; rw [hm]
      | ok u => simp [hc, pure, Except.pure] at hm
    have hp1 : isPatternErr e1 = true := hpat _ _ _ hc1
    have hstr : (str' m).isEmpty = false := by rw [str'_isEmpty]; exact hne
    refine ⟨optErr s!"invalid regular expression for {"message"}: {pyReprStr (str' m)}", ?_, rfl⟩
    simp [bind, Except.bind, hne, hp1, patternHandler, recheck, ← hflag, hc1]
  | ok mrx =>
    cases hd : compileOpt E.fenv (str' md) false with
    | error e2 =>
      right
      have hne : md.isEmpty = false := by
        cases hme : md.isEmpty
        · rfl
        · simp [compileOpt, str'_isEmpty, hme] at hd
      have hc2 : E.fenv.compile (str' md) false = .error e2 := by
        unfold compileOpt at hd
        rw [str'_isEmpty, hne] at hd
        simp only [Bool.false_eq_true, if_false, bind, Except.bind] at hd
        cases hc : E.fenv.compile (str' md) false with
        | error e' => simp [hc] at hd; rw [hd]
        | ok u => simp [hc, pure, Except.pure] at hd
      have hp2 : isPatternErr e2 = true := hpat _ _ _ hc2
      -- the message, if any, compiles without flags too
      have hmok : m.isEmpty = false → E.fenv.compile (str' m) false = .ok () := by
        intro hme
        rw [← hflag]
        exact compileOpt_okE E.fenv (str' m) true mrx hm (by rw [str'_isEmpty]; exact hme)
      refine ⟨optErr s!"invalid regular expression for {"module"}: {pyReprStr (str' md)}", ?_, rfl⟩
      cases hme : m.isEmpty
      · simp [bind, Except.bind, pure, Except.pure, hne, hme, hp2, patternHandler, recheck, hmok hme, hc2]
      · simp [bind, Except.bind, pure, Except.pure, hne, hme, hp2, patternHandler, recheck, hc2]
    | ok drx =>
      left
      obtain ⟨cont, v⟩ := s
      simp only at hxs
      subst hxs
      have e := addFilter_list E.fenv.hier ⟨a, mrx, cat, drx, ln⟩ false xs v (htot _)
      refine ⟨⟨.list (addSpec ⟨a, mrx, cat, drx, ln⟩ false xs), v + 1⟩, ?_,
        ⟨_, rfl, listOk_add _ false xs htot⟩⟩
      simp only [bind, Except.bind, pure, Except.pure, e]

theorem setoption_ok_or_opt (E : OEnv) (h : OptEnvOk E) (arg : List Char) (s : FState) (hs : ListOk s) :
    (∃ s', setoption E arg s = .ok s' ∧ ListOk s') ∨
    (∃ e, setoption E arg s = .error e ∧ e.className = "_OptionError") := by
  unfold setoption
  cases hp : soParse E arg with
  | error e => exact Or.inr ⟨e, by simp [bind, Except.bind], soParse_err E h arg e hp⟩
  | ok r =>
    obtain ⟨a, cat, m, md, ln⟩ := r
    obtain ⟨ha, ht, hw, hl⟩ := soParse_ok E h arg a cat m md ln hp
    simp only [bind, Except.bind]
    exact soInstall_ok_or_opt E h a ha cat ht hw m md ln hl s hs

/-- `-W` options never make `import warnings` fail in an environment where imports raise only
`ImportError`, every attribute named is a class, and patterns raise only `re.PatternError`: for
every list of options, on the startup filters list, `_processoptions` lets no exception escape. -/
def ProcessOptionsNoEscapeNarrow : Prop :=
  ∀ E args s, OptEnvOk E → ListOk s → (processoptions E args s).2.2 = none

theorem processOptionsNoEscapeNarrow_proven : ProcessOptionsNoEscapeNarrow := by
  intro E args
  induction args with
  | nil => intro s _ _; rfl
  | cons a as ih =>
    intro s h hs
    rcases setoption_ok_or_opt E h a s hs with ⟨s', hs1, hs2⟩ | ⟨e, he1, he2⟩
    · simp only [processoptions, hs1]
      exact ih s' h hs2
    · simp only [processoptions, he1, he2, beq_self_eq_true, if_true]
      exact ih s h hs

/-- The invariant without the narrowing: for the real `builtins`, `__import__` and `re` (an
attribute that is not a class, `__import__('')` raising `ValueError`, `re.compile` raising
`OverflowError` for a repetition count of 2**32), no `-W` option makes `_processoptions` raise.
Refuted three ways. -/
def ProcessOptionsNoEscape : Prop :=
  ∀ E args s, ListOk s → (processoptions E args s).2.2 = none

def optE (getattrPrint : Bool) : OEnv :=
  ⟨⟨fun p _ => if p = "a{4294967296}" then .error (.overflowError "the repetition number is too large") else .ok (),
    fun _ => true, fun i => i = 0, builtinHier⟩,
   fun m _ => if m = [] then .error (.valueError "Empty module name") else .ok 1,
   fun _ k => if getattrPrint ∧ k = "print".toList then .ok .nonclass else .ok (.cls 0), 0⟩

theorem listOk_nil : ListOk ⟨.list [], 0⟩ := ⟨[], rfl, fun _ _ h => by simp at h⟩

/-- `-W ignore::print`: `issubclass(print, Warning)` raises `TypeError`. -/
theorem processOptionsNoEscape_refuted : ¬ ProcessOptionsNoEscape := fun h =>
  refute (h (optE true) ["ignore::print".toList] ⟨.list [], 0⟩ listOk_nil)
    (x := some (.typeError "issubclass() arg 1 must be a class")) (y := none) (by rfl) rfl (by simp)

/-- `-W ignore::.Foo`: `__import__('')` raises `ValueError`. -/
theorem processOptionsNoEscape_refuted_module : ¬ ProcessOptionsNoEscape := fun h =>
  refute (h (optE false) ["ignore::.Foo".toList] ⟨.list [], 0⟩ listOk_nil)
    (x := some (.valueError "Empty module name")) (y := none) (by rfl) rfl (by simp)

/-- `-W ignore:/a{4294967296}/`: `re.compile` raises `OverflowError`. -/
theorem processOptionsNoEscape_refuted_regex : ¬ ProcessOptionsNoEscape := fun h =>
  refute (h (optE false) ["ignore:/a{4294967296}/".toList] ⟨.list [], 0⟩ listOk_nil)
    (x := some (.overflowError "the repetition number is too large")) (y := none) (by rfl) rfl (by simp)

end PyLean.CoreLibs.Warn
