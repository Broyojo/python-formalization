import PyLean.Datetime.ZoneCacheErrProps

/-!
# A subclass's weak cache: both twins use `Sub._weak_cache` (CPython 3.15.2)

C `get_weak_cache` returns the subclass's own `_weak_cache` attribute
(Modules/_zoneinfo.c:299-301), which `zoneinfo_init_subclass` stored; Python's
`cls._weak_cache` finds the same attribute. While the instances stay referenced (no
collection), every run of `Sub(key)` and `clear_cache` on a fresh subclass gives the same
results and leaves the same weak cache in both twins, for keys whose `__hash__` and `__eq__`
do not raise. A `get_weak_cache` returning a new dictionary each time would lose the cached
instance and fail this.
-/

namespace PyLean.Datetime.Zone

open PyLean

set_option linter.unusedSectionVars false

/-- `ZoneInfo(k)`, `clear_cache()` and `clear_cache(only_keys=...)` only. -/
def ZOp.isPlain {K : Type} : ZOp K → Bool
  | .get _ | .clear | .clearKeys _ _ => true
  | _ => false

section sub

variable {K : Type} [DecidableEq K] (o : KeyOps K)
  (hE : ∀ a b, ∃ r, o.eq a b = .ok r) (hH : ∀ a, ∃ h, o.hash a = .ok h)
include hE hH

theorem probe_ok (key : K) (h : Int) {Vt : Type} : ∀ l : List (K × Vt),
    ∃ r, dictProbe o key h l = .ok r := by
  intro l
  induction l with
  | nil => exact ⟨none, rfl⟩
  | cons e l ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨b, hb⟩ := hE e.1 key
    by_cases h1 : e.1 = key
    · exact ⟨some e, by simp [dictProbe, h1]⟩
    · by_cases h2 : hashIs o e.1 h = true
      · cases b with
        | true => exact ⟨some e, by simp [dictProbe, h1, h2, hb]⟩
        | false => exact ⟨r, by simp [dictProbe, h1, h2, hb, hr]⟩
      · exact ⟨r, by simp [dictProbe, h1, h2, hr]⟩

theorem dictFind_ok {Vt : Type} (l : List (K × Vt)) (key : K) : ∃ r, dictFind o l key = .ok r := by
  obtain ⟨h, hh⟩ := hH key
  obtain ⟨r, hr⟩ := probe_ok o hE hH key h l
  exact ⟨r, by simp [dictFind, hh, hr]⟩

theorem dictPop_ok (l : List (K × Inst K)) (key : K) : ∃ r, dictPop o l key = .ok r := by
  obtain ⟨r, hr⟩ := dictFind_ok o hE hH l key
  cases r with
  | none => exact ⟨(none, l), by simp [dictPop, hr]⟩
  | some e => exact ⟨(some e.2, l.erase e), by simp [dictPop, hr]⟩

theorem dictSet_ok (l : List (K × Inst K)) (key : K) (i : Inst K) : ∃ r, dictSet o l key i = .ok r := by
  obtain ⟨r, hr⟩ := dictFind_ok o hE hH l key
  cases r with
  | none => exact ⟨l ++ [(key, i)], by simp [dictSet, hr]⟩
  | some e => exact ⟨l.map fun p => if p = e then (e.1, i) else p, by simp [dictSet, hr]⟩

/-- Subclass states: Python's with its strong cache `ps`, C's without; one weak cache `W`. -/
def subP (ps W : List (K × Inst K)) (n : Nat) : ZCls K := ⟨false, ps, some W, [], n, []⟩

theorem sub_get (ps W : List (K × Inst K)) (n : Nat) (k : K) :
    (stepErrC o (subP [] W n) (.get k)).2 = (stepErrPy o (subP ps W n) (.get k)).2 ∧
    ∃ W' n' ps', (stepErrC o (subP [] W n) (.get k)).1 = subP [] W' n' ∧
      (stepErrPy o (subP ps W n) (.get k)).1 = subP ps' W' n' := by
  obtain ⟨⟨v0, s1⟩, h1⟩ := dictPop_ok o hE hH ps k
  cases hg : wvdGet o W k with
  | error x =>
    refine ⟨?_, W, n, ps, ?_, ?_⟩ <;>
      simp [stepErrC, stepErrPy, newErrC, newErrPy, zoneFromStrongC, getWeakC, getWeakPy, subP, hg]
  | ok r =>
    cases r with
    | some inst =>
      obtain ⟨s2, h2⟩ := dictSet_ok o hE hH s1 k (v0.getD inst)
      have ep : stepErrPy o (subP ps W n) (.get k) =
          (subP (if s2.length > 8 then s2.tail else s2) W n, .ok (some inst)) := by
        simp [stepErrPy, newErrPy, getWeakPy, subP, hg, setWeakPy, h1, h2, Except.map]
      have ec : stepErrC o (subP [] W n) (.get k) = (subP [] W n, .ok (some inst)) := by
        simp [stepErrC, newErrC, zoneFromStrongC, getWeakC, subP, hg, updateStrongC, Except.map]
      rw [ep, ec]; exact ⟨rfl, W, n, _, rfl, rfl⟩
    | none =>
      cases hl : o.loads k with
      | false =>
        refine ⟨?_, W, n, ps, ?_, ?_⟩ <;>
          simp [stepErrC, stepErrPy, newErrC, newErrPy, zoneFromStrongC, getWeakC, getWeakPy, subP,
            hg, hl]
      | true =>
        cases hs : wvdSetdefault o W k (k, n) with
        | error x =>
          refine ⟨?_, W, n, ps, ?_, ?_⟩ <;>
            simp [stepErrC, stepErrPy, newErrC, newErrPy, zoneFromStrongC, getWeakC, getWeakPy, subP,
              hg, hl, hs, Except.map]
        | ok p =>
          obtain ⟨inst, W'⟩ := p
          obtain ⟨s2, h2⟩ := dictSet_ok o hE hH s1 k (v0.getD inst)
          have ep : stepErrPy o (subP ps W n) (.get k) =
              (subP (if s2.length > 8 then s2.tail else s2) W' (n + 1), .ok (some inst)) := by
            simp [stepErrPy, newErrPy, getWeakPy, subP, hg, hl, hs, setWeakPy, h1, h2, Except.map]
          have ec : stepErrC o (subP [] W n) (.get k) = (subP [] W' (n + 1), .ok (some inst)) := by
            simp [stepErrC, newErrC, zoneFromStrongC, getWeakC, subP, hg, hl, hs, updateStrongC,
              Except.map]
          rw [ep, ec]; exact ⟨rfl, W', n + 1, _, rfl, rfl⟩

theorem sub_clearKeys (err : Option PyExc) : ∀ (ks : List K) (ps W : List (K × Inst K)) (n : Nat)
    (cw : Option (List (K × Inst K))),
    (clearKeysC o W err ⟨false, [], cw, [], n, []⟩ ks).2 = (clearKeysPy o err (subP ps W n) ks).2 ∧
    ∃ W' ps', (clearKeysC o W err ⟨false, [], cw, [], n, []⟩ ks).1 = subP [] W' n ∧
      (clearKeysPy o err (subP ps W n) ks).1 = subP ps' W' n := by
  intro ks
  induction ks with
  | nil => intro ps W n cw; exact ⟨rfl, W, ps, rfl, rfl⟩
  | cons k ks ih =>
    intro ps W n cw
    obtain ⟨⟨v1, W1⟩, hw⟩ := dictPop_ok o hE hH W k
    obtain ⟨⟨v2, ps1⟩, hp⟩ := dictPop_ok o hE hH ps k
    have hwp : wvdPop o W k = .ok W1 := by simp [wvdPop, hw]
    have hc : clearKeysC o W err ⟨false, [], cw, [], n, []⟩ (k :: ks) =
        clearKeysC o W1 err ⟨false, [], cw, [], n, []⟩ ks := by
      simp [clearKeysC, ejectC, hwp]
    have hpy : clearKeysPy o err (subP ps W n) (k :: ks) = clearKeysPy o err (subP ps1 W1 n) ks := by
      simp [clearKeysPy, getWeakPy, subP, hwp, setWeakPy, hp]
    rw [hc, hpy]
    exact ih ps1 W1 n cw

theorem sub_run : ∀ (ops : List (ZOp K)) (ps W : List (K × Inst K)) (n : Nat),
    ops.all ZOp.isPlain = true →
    (runErrC o (subP [] W n) ops).2 = (runErrPy o (subP ps W n) ops).2 ∧
    (runErrC o (subP [] W n) ops).1.weak = (runErrPy o (subP ps W n) ops).1.weak := by
  intro ops
  induction ops with
  | nil => intro ps W n _; exact ⟨rfl, rfl⟩
  | cons op ops ih =>
    intro ps W n hall
    simp only [List.all_cons, Bool.and_eq_true] at hall
    have step : (stepErrC o (subP [] W n) op).2 = (stepErrPy o (subP ps W n) op).2 ∧
        ∃ W' n' ps', (stepErrC o (subP [] W n) op).1 = subP [] W' n' ∧
          (stepErrPy o (subP ps W n) op).1 = subP ps' W' n' := by
      cases op with
      | get k => exact sub_get o hE hH ps W n k
      | clear =>
        refine ⟨rfl, [], n, [], ?_, ?_⟩ <;> simp [stepErrC, stepErrPy, clearErrC, clearErrPy,
          getWeakC, setWeakPy, subP]
      | clearKeys ks err =>
        have hc : stepErrC o (subP [] W n) (.clearKeys ks err) =
            clearKeysC o W err ⟨false, [], some W, [], n, []⟩ ks := by
          simp [stepErrC, clearErrC, getWeakC, subP]
        have hp : stepErrPy o (subP ps W n) (.clearKeys ks err) = clearKeysPy o err (subP ps W n) ks := rfl
        rw [hc, hp]
        obtain ⟨e, W', ps', h1, h2⟩ := sub_clearKeys o hE hH err ks ps W n (some W)
        exact ⟨e, W', n, ps', h1, h2⟩
      | drop _ => simp [ZOp.isPlain] at hall
      | delWeak => simp [ZOp.isPlain] at hall
      | setWeak _ => simp [ZOp.isPlain] at hall
    obtain ⟨e, W', n', ps', h1, h2⟩ := step
    obtain ⟨r1, r2⟩ := ih ps' W' n' hall.2
    simp only [runErrC, runErrPy]
    rw [show stepErrC o (subP [] W n) op = ((stepErrC o (subP [] W n) op).1,
        (stepErrC o (subP [] W n) op).2) from rfl,
      show stepErrPy o (subP ps W n) op = ((stepErrPy o (subP ps W n) op).1,
        (stepErrPy o (subP ps W n) op).2) from rfl, h1, h2, e]
    exact ⟨by simp [r1], r2⟩

end sub

/-- After `class Sub(ZoneInfo)` (no keywords, `weakref` as bound), while the instances stay
referenced, every run of `Sub(key)`, `Sub.clear_cache()` and `Sub.clear_cache(only_keys=...)`
gives the same results (the same instances, the same exceptions) and leaves the same weak
cache in both twins, for keys whose `__hash__` and `__eq__` do not raise: C's
`get_weak_cache` returns the `_weak_cache` attribute `zoneinfo_init_subclass` stored, as
Python's `cls._weak_cache` does. -/
def SubCacheTwins : Prop :=
  ∀ (K : Type) [DecidableEq K] (o : KeyOps K), (∀ a b, ∃ r, o.eq a b = .ok r) →
    (∀ a, ∃ h, o.hash a = .ok h) → ∀ (sp sc : ZCls K) (ops : List (ZOp K)),
    initSubclassErrPy [] (some (.ok ())) [] = .ok sp →
    initSubclassErrC [] (.ok (some (.ok ()))) [] = .ok sc →
    ops.all ZOp.isPlain = true →
    (runErrC o sc ops).2 = (runErrPy o sp ops).2 ∧ (runErrC o sc ops).1.weak = (runErrPy o sp ops).1.weak

theorem subCacheTwins_proven : SubCacheTwins := by
  intro K _ o hE hH sp sc ops hp hc hall
  simp only [initSubclassErrPy, newWeakCachePy, initSubclassErrC, newWeakCacheC,
    Except.ok.injEq] at hp hc
  subst hp; subst hc
  exact sub_run o hE hH ops [] [] 0 hall

end PyLean.Datetime.Zone
