import PyLean.Datetime.ZoneCacheErrProps

/-!
# Keys compared by identity: the fallible cache mirrors follow `ZoneCache.lean`

With keys whose `==` is identity and whose `hash()` does not raise, a base-class state of
`ZoneCacheErr.lean` is a state of `ZoneCache.lean` with key `k`'s instance `(k, ι k)`; every
step of `stepErrC`/`stepErrPy` is the abstract `stepC`/`stepPy` on it, with the same `ι`
update and the same result in both twins. So `CacheTwins` carries over to the mirrors,
iterator errors of `clear_cache(only_keys=...)` included.
-/

namespace PyLean.Datetime.Zone

open PyLean

section fallible

variable {K : Type} [DecidableEq K]

/-- `ι` with key `k` now naming instance `n`. -/
def upd (ι : K → Nat) (k : K) (n : Nat) : K → Nat := fun x => if x = k then n else ι x

/-- Key `k` with its current instance. -/
def pr (ι : K → Nat) (k : K) : K × Inst K := (k, (k, ι k))

theorem erase_pr (ι : K → Nat) (l : List K) (k : K) :
    (l.map (pr ι)).erase (k, (k, ι k)) = (l.erase k).map (pr ι) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : a = k
    · subst h; simp [pr]
    · have h' : ¬ (pr ι a == (k, (k, ι k))) = true := by simp [pr, h]
      have h'' : ¬ (a == k) = true := by simp [h]
      simp only [List.map_cons, List.erase_cons, h', h'', Bool.false_eq_true, ite_false, ih]

theorem eraseP_pr (ι : K → Nat) (l : List K) (k : K) :
    (l.map (pr ι)).eraseP (fun p => decide (p.2 = (k, ι k))) = (l.erase k).map (pr ι) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : a = k
    · subst h; simp [pr]
    · have h'' : ¬ (a == k) = true := by simp [h]
      have h3 : ¬ ((a, ι a) = (k, ι k)) := by simp [h]
      simp only [List.map_cons, List.eraseP_cons, List.erase_cons, h'', Bool.false_eq_true,
        ite_false, ih, pr, h3, decide_false, Bool.cond_false]

theorem map_pr_update (ι : K → Nat) (k : K) (n : Nat) (l : List K) (hk : k ∉ l) :
    l.map (pr (upd ι k n)) = l.map (pr ι) := by
  apply List.map_congr_left
  intro a ha
  have : a ≠ k := fun e => hk (e ▸ ha)
  simp [pr, upd, this]

theorem probe_id (o : KeyOps K) (hE : ∀ a b, o.eq a b = .ok (decide (a = b))) (ι : K → Nat)
    (key : K) (h : Int) : ∀ l : List K,
    dictProbe o key h (l.map (pr ι)) = .ok (if key ∈ l then some (pr ι key) else none) := by
  intro l
  induction l with
  | nil => rfl
  | cons e l ih =>
    by_cases he : e = key
    · subst he; simp [dictProbe, pr]
    · have hne : ¬ key = e := fun x => he x.symm
      have heq : o.eq e key = .ok false := by rw [hE]; simp [he]
      simp only [List.map_cons, dictProbe, pr, he, ite_false, heq] at ih ⊢
      rw [ih]
      simp [hne]

theorem dictFind_id (o : KeyOps K) (hE : ∀ a b, o.eq a b = .ok (decide (a = b)))
    (hH : ∀ k, ∃ h, o.hash k = .ok h) (ι : K → Nat) (key : K) (l : List K) :
    dictFind o (l.map (pr ι)) key = .ok (if key ∈ l then some (pr ι key) else none) := by
  obtain ⟨h, hh⟩ := hH key
  simp only [dictFind, hh]
  exact probe_id o hE ι key h l

theorem findStrongC_id (o : KeyOps K) (hE : ∀ a b, o.eq a b = .ok (decide (a = b))) (ι : K → Nat)
    (key : K) : ∀ l : List K,
    findStrongC o key (l.map (pr ι)) = .ok (if key ∈ l then some (pr ι key) else none) := by
  intro l
  induction l with
  | nil => rfl
  | cons e l ih =>
    by_cases he : key = e
    · subst he; simp [findStrongC, richEqBool, pr]
    · have heq : richEqBool o key e = .ok false := by simp [richEqBool, he, hE]
      simp only [List.map_cons, findStrongC, pr, heq] at ih ⊢
      rw [ih]
      simp [he]

section
variable (o : KeyOps K) (hE : ∀ a b, o.eq a b = .ok (decide (a = b)))
  (hH : ∀ k, ∃ h, o.hash k = .ok h) (ι : K → Nat)
include hE hH

theorem wvdGet_id (key : K) (l : List K) :
    wvdGet o (l.map (pr ι)) key = .ok (if key ∈ l then some (key, ι key) else none) := by
  simp only [wvdGet, dictFind_id o hE hH]
  split <;> simp [pr]

theorem wvdSetdefault_id (key : K) (n : Nat) (l : List K) (hk : key ∉ l) :
    wvdSetdefault o (l.map (pr ι)) key (key, n) =
      .ok ((key, n), (l ++ [key]).map (pr (upd ι key n))) := by
  simp only [wvdSetdefault, dictSet, dictFind_id o hE hH, hk, ite_false]
  simp [map_pr_update ι key n l hk, pr, upd]

theorem dictPop_id (key : K) (l : List K) :
    dictPop o (l.map (pr ι)) key =
      .ok (if key ∈ l then some (key, ι key) else none, (l.erase key).map (pr ι)) := by
  simp only [dictPop, dictFind_id o hE hH]
  by_cases hk : key ∈ l
  · simp [hk, pr, erase_pr]
  · simp [hk, List.erase_of_not_mem hk]

theorem wvdPop_id (key : K) (l : List K) :
    wvdPop o (l.map (pr ι)) key = .ok ((l.erase key).map (pr ι)) := by
  cases l with
  | nil => rfl
  | cons a l =>
    have := dictPop_id o hE hH ι key (a :: l)
    simp only [List.map_cons] at this
    simp only [List.map_cons, wvdPop, this]

theorem dictSet_id (key : K) (l : List K) (hk : key ∉ l) :
    dictSet o (l.map (pr ι)) key (key, ι key) = .ok ((l ++ [key]).map (pr ι)) := by
  simp only [dictSet, dictFind_id o hE hH, hk, ite_false]
  simp [pr]

end

theorem find_pr (ι : K → Nat) (w : List K) (k : K) :
    (w.map (pr ι)).find? (fun p => decide (p.1 = k)) = if k ∈ w then some (pr ι k) else none := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    by_cases h : a = k
    · subst h; simp [pr]
    · have : ¬ k = a := fun e => h e.symm
      rw [List.map_cons, List.find?_cons, ih]
      simp [pr, h, this]

theorem dropIn_pr (ι : K → Nat) (s w : List K) (k : K) (hsub : ∀ x ∈ s, x ∈ w) :
    dropIn (s.map (pr ι)) (w.map (pr ι)) k = (if k ∈ s then w else w.erase k).map (pr ι) := by
  have hf := find_pr ι w k
  have ha : (s.map (pr ι)).any (fun p => decide (p.2 = (k, ι k))) = decide (k ∈ s) := by
    rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
    simp only [List.mem_map, pr]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, h⟩
      simp only [decide_eq_true_eq, Prod.mk.injEq] at h
      exact h.1 ▸ ha
    · intro h; exact ⟨(k, (k, ι k)), ⟨k, h, rfl⟩, by simp⟩
  simp only [dropIn, hf]
  by_cases hw : k ∈ w
  · simp only [hw, ite_true, pr, ha]
    by_cases hs : k ∈ s
    · simp [hs]
    · simp only [hs, decide_false, Bool.false_eq_true, ite_false]
      exact eraseP_pr ι w k
  · have hs : k ∉ s := fun h => hw (hsub k h)
    simp [hw, hs, List.erase_of_not_mem hw]

/-- A base-class state of `ZoneCache.lean`; key `k`'s instance is `(k, ι k)`, `n` instances
built so far. -/
def embZ (s : CacheSt K) (ι : K → Nat) (n : Nat) : ZCls K :=
  ⟨true, s.strong.map (pr ι), some (s.weak.map (pr ι)), [], n, [], []⟩

def forget : ZOp K → CacheOp K
  | .get k => .get k
  | .clear => .clear
  | .clearKeys ks _ => .clearKeys ks
  | .drop k => .drop k
  | .delWeak => .clear
  | .setWeak _ => .clear
  | .release _ => .clear

/-- Whether the operation builds a new instance: `ZoneInfo(k)` with `k` not in the weak cache
and loadable. -/
def builds (loads : K → Bool) (w : List K) : ZOp K → Bool
  | .get k => !decide (k ∈ w) && loads k
  | _ => false

def nextι (loads : K → Bool) (w : List K) (ι : K → Nat) (n : Nat) (op : ZOp K) : K → Nat :=
  match op with
  | .get k => if builds loads w op then upd ι k n else ι
  | _ => ι

def nextN (loads : K → Bool) (w : List K) (n : Nat) (op : ZOp K) : Nat :=
  if builds loads w op then n + 1 else n

/-- The outcome, from whether the abstract step succeeded. -/
def resOf (ι : K → Nat) : ZOp K → Bool → Py (Option (Inst K))
  | .get k, true => .ok (some (k, ι k))
  | .get _, false => .error notFound
  | .clearKeys _ (some e), _ => .error e
  | _, _ => .ok none

theorem clearKeysC_id (o : KeyOps K) (hE : ∀ a b, o.eq a b = .ok (decide (a = b)))
    (hH : ∀ k, ∃ h, o.hash k = .ok h) (ι : K → Nat) (n : Nat) (err : Option PyExc)
    (cw : Option (List (K × Inst K))) :
    ∀ (ks st w : List K), clearKeysC o (w.map (pr ι)) err ⟨true, st.map (pr ι), cw, [], n, [], []⟩ ks =
      (embZ (ks.foldl (fun st k => ⟨st.strong.erase k, st.weak.erase k⟩) (⟨st, w⟩ : CacheSt K)) ι n,
        match err with | some e => .error e | none => .ok none) := by
  intro ks
  induction ks with
  | nil => intro st w; rfl
  | cons k ks ih =>
    intro st w
    have hej : ∃ f, ejectC o ⟨true, st.map (pr ι), cw, [], n, [], []⟩ k =
        .ok ((st.erase k).map (pr ι), f) := by
      simp only [ejectC, Bool.not_true, Bool.false_eq_true, ite_false, findStrongC_id o hE ι]
      by_cases hk : k ∈ st
      · exact ⟨some (k, ι k), by simp [hk, pr, erase_pr]⟩
      · exact ⟨none, by simp [hk, List.erase_of_not_mem hk]⟩
    obtain ⟨f, hej⟩ := hej
    simp only [clearKeysC, hej, freeCb_nil, wvdPop_id o hE hH, List.foldl_cons]
    exact ih _ _

theorem clearKeysPy_id (o : KeyOps K) (hE : ∀ a b, o.eq a b = .ok (decide (a = b)))
    (hH : ∀ k, ∃ h, o.hash k = .ok h) (ι : K → Nat) (n : Nat) (err : Option PyExc) :
    ∀ (ks st w : List K), clearKeysPy o err (embZ ⟨st, w⟩ ι n) ks =
      (embZ (ks.foldl (fun st k => ⟨st.strong.erase k, st.weak.erase k⟩) (⟨st, w⟩ : CacheSt K)) ι n,
        match err with | some e => .error e | none => .ok none) := by
  intro ks
  induction ks with
  | nil => intro st w; rfl
  | cons k ks ih =>
    intro st w
    simp only [clearKeysPy, embZ, getWeakPy, Option.getD_some, wvdPop_id o hE hH, setWeakPy,
      dictPop_id o hE hH, List.foldl_cons, freeCb_nil]
    exact ih _ _

theorem stepErrC_emb (o : KeyOps K) (hE : ∀ a b, o.eq a b = .ok (decide (a = b)))
    (hH : ∀ k, ∃ h, o.hash k = .ok h) (ι : K → Nat) (n : Nat) (s : CacheSt K)
    (hsub : ∀ x ∈ s.strong, x ∈ s.weak) (op : ZOp K) (hop : op.isDel = false) :
    stepErrC o (embZ s ι n) op =
      (embZ ((stepC o.loads s (forget op)).getD s) (nextι o.loads s.weak ι n op)
          (nextN o.loads s.weak n op),
        resOf (nextι o.loads s.weak ι n op) op (stepC o.loads s (forget op)).isSome) := by
  cases op with
  | get k =>
    simp only [stepErrC, newErrC, zoneFromStrongC, embZ, Bool.not_true, Bool.false_eq_true,
      ite_false, findStrongC_id o hE ι, forget, stepC, newC, nextι, nextN, builds]
    by_cases hs : k ∈ s.strong
    · have hw := hsub k hs
      simp [hs, hw, pr, erase_pr, resOf, Except.map]
    · simp only [hs, ite_false, getWeakC, ite_true, Option.getD_some, wvdGet_id o hE hH]
      by_cases hw : k ∈ s.weak
      · simp [hw, updateStrongC, pr, List.map_take, resOf, Except.map]
      · by_cases hl : o.loads k = true
        · simp only [hw, ite_false, hl, Bool.not_true, Bool.false_eq_true, decide_false,
            Bool.not_false, Bool.and_true, ite_true, wvdSetdefault_id o hE hH ι k n s.weak hw,
            Except.map, updateStrongC, Option.map_some, Option.getD_some, Option.isSome_some, resOf]
          simp [map_pr_update ι k n s.strong hs, pr, List.map_take, upd, hw, hl]
        · simp [hw, hl, resOf, Except.map]
  | clear => simp [stepErrC, clearErrC, getWeakC, embZ, forget, stepC, clearC, resOf, nextι, nextN, builds]
  | clearKeys ks err =>
    simp only [stepErrC, clearErrC, getWeakC, embZ, ite_true, Option.getD_some, forget, stepC,
      clearC, Option.isSome_some, nextι, nextN, builds, Bool.false_eq_true, ite_false]
    rw [clearKeysC_id o hE hH ι n err]
    cases err <;> rfl
  | drop k =>
    simp only [stepErrC, embZ, Option.map_some, dropIn_pr ι _ _ k hsub, forget, stepC,
      Option.getD_some, Option.isSome_some, resOf, nextι, nextN, builds, Bool.false_eq_true, ite_false]
  | delWeak => simp [ZOp.isDel] at hop
  | setWeak d => simp [ZOp.isDel] at hop
  | release k => simp [ZOp.isDel] at hop

theorem stepErrPy_emb (o : KeyOps K) (hE : ∀ a b, o.eq a b = .ok (decide (a = b)))
    (hH : ∀ k, ∃ h, o.hash k = .ok h) (ι : K → Nat) (n : Nat) (s : CacheSt K)
    (hnd : s.strong.Nodup) (hsub : ∀ x ∈ s.strong, x ∈ s.weak) (op : ZOp K)
    (hop : op.isDel = false) :
    stepErrPy o (embZ s ι n) op =
      (embZ ((stepPy o.loads s (forget op)).getD s) (nextι o.loads s.weak ι n op)
          (nextN o.loads s.weak n op),
        resOf (nextι o.loads s.weak ι n op) op (stepPy o.loads s (forget op)).isSome) := by
  have hnot : ∀ k, k ∉ s.strong.erase k := fun k hk =>
    ((List.Nodup.mem_erase_iff hnd).mp hk).1 rfl
  cases op with
  | get k =>
    simp only [stepErrPy, newErrPy, embZ, getWeakPy, Option.getD_some, wvdGet_id o hE hH, forget,
      stepPy, newPy, nextι, nextN, builds]
    by_cases hw : k ∈ s.weak
    · simp only [hw, ite_true, setWeakPy, dictPop_id o hE hH, decide_true, Bool.not_true,
        Bool.false_and, Bool.false_eq_true, ite_false]
      have hv : (if k ∈ s.strong then some (k, ι k) else none).getD (k, ι k) = (k, ι k) := by
        split <;> rfl
      simp only [hv, dictSet_id o hE hH ι k _ (hnot k)]
      simp [List.map_tail, resOf, Except.map]
      split <;> simp [pr]
    · have hs : k ∉ s.strong := fun h => hw (hsub k h)
      by_cases hl : o.loads k = true
      · simp only [hw, ite_false, hl, Bool.not_true, Bool.false_eq_true, decide_false,
          Bool.not_false, Bool.and_true, ite_true, wvdSetdefault_id o hE hH ι k n s.weak hw,
          Except.map, setWeakPy, List.erase_of_not_mem hs]
        rw [← map_pr_update ι k n s.strong hs, dictPop_id o hE hH (upd ι k n),
          List.erase_of_not_mem hs]
        simp only [hs, ite_false, Option.getD_none]
        have hk' : (k, n) = (k, upd ι k n k) := by simp [upd]
        rw [hk', dictSet_id o hE hH (upd ι k n) k _ hs]
        simp [List.map_tail, resOf, upd]
        split <;> simp [pr]
      · simp [hw, hl, resOf, Except.map]
  | clear =>
    simp [stepErrPy, clearErrPy, setWeakPy, embZ, forget, stepPy, clearPy, resOf, nextι, nextN, builds]
  | clearKeys ks err =>
    simp only [stepErrPy, clearErrPy, forget, stepPy, clearPy, Option.getD_some, Option.isSome_some,
      nextι, nextN, builds, Bool.false_eq_true, ite_false]
    rw [show embZ s ι n = embZ ⟨s.strong, s.weak⟩ ι n from rfl, clearKeysPy_id o hE hH ι n err]
    cases err <;> rfl
  | drop k =>
    simp only [stepErrPy, embZ, Option.map_some, dropIn_pr ι _ _ k hsub, forget, stepPy,
      Option.getD_some, Option.isSome_some, resOf, nextι, nextN, builds, Bool.false_eq_true, ite_false]
    simp [dropIn]
  | delWeak => simp [ZOp.isDel] at hop
  | setWeak d => simp [ZOp.isDel] at hop
  | release k => simp [ZOp.isDel] at hop

theorem run_twins (o : KeyOps K) (hE : ∀ a b, o.eq a b = .ok (decide (a = b)))
    (hH : ∀ k, ∃ h, o.hash k = .ok h) :
    ∀ (ops : List (ZOp K)) (sp sc : CacheSt K) (ι : K → Nat) (n : Nat), CInv sp sc →
      ops.all (fun op => !op.isDel) = true →
      (runErrC o (embZ sc ι n) ops).2 = (runErrPy o (embZ sp ι n) ops).2 ∧
      (runErrC o (embZ sc ι n) ops).1.strong = (runErrPy o (embZ sp ι n) ops).1.strong.reverse ∧
      (runErrPy o (embZ sp ι n) ops).1.strong.length ≤ 8 := by
  intro ops
  induction ops with
  | nil =>
    intro sp sc ι n h _
    refine ⟨rfl, ?_, ?_⟩
    · simp only [runErrC, runErrPy, embZ, h.strong, List.map_reverse]
    · simp only [runErrPy, embZ, List.length_map]; exact h.len
  | cons op ops ih =>
    intro sp sc ι n h hall
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hall
    have hsubc : ∀ x ∈ sc.strong, x ∈ sc.weak := fun x hx => by
      rw [h.strong, List.mem_reverse] at hx; rw [h.weak]; exact h.sub x hx
    have hs := step_inv o.loads sp sc h (forget op)
    simp only [runErrPy, runErrC, stepErrPy_emb o hE hH ι n sp h.nodup h.sub op hall.1,
      stepErrC_emb o hE hH ι n sc hsubc op hall.1, h.weak]
    cases hp : stepPy o.loads sp (forget op) <;> cases hc : stepC o.loads sc (forget op) <;>
      rw [hp, hc] at hs
    · obtain ⟨e1, e2, e3⟩ := ih sp sc (nextι o.loads sp.weak ι n op) (nextN o.loads sp.weak n op) h hall.2
      simp only [Option.getD_none, Option.isSome_none, e1, e2, e3, and_self, List.cons.injEq,
        true_and]
    · exact hs.elim
    · exact hs.elim
    · rename_i sp' sc'
      obtain ⟨e1, e2, e3⟩ := ih sp' sc' (nextι o.loads sp.weak ι n op) (nextN o.loads sp.weak n op) hs hall.2
      simp only [Option.getD_some, Option.isSome_some, e1, e2, e3, and_self, List.cons.injEq,
        true_and]

end fallible

/-- The base-class caches with the fallible-key mirrors, for keys whose `==` is identity and
whose `hash()` does not raise (keys without a custom `__eq__`/`__hash__`, or one object per key
value): every run of `ZoneInfo(key)`, `clear_cache()`, `clear_cache(only_keys=...)` whose
iterator may raise after any prefix, and collections gives the same outcome in both twins (the
same instance for each `ZoneInfo(key)`, the same exception for each failure) and the same
strong-cache entries in recency order (C newest first, Python oldest first), never more
than 8. -/
def CacheTwinsFallible : Prop :=
  ∀ (K : Type) [DecidableEq K] (o : KeyOps K), (∀ a b, o.eq a b = .ok (decide (a = b))) →
    (∀ k, ∃ h, o.hash k = .ok h) → ∀ ops : List (ZOp K), ops.all (fun op => !op.isDel) = true →
      (runErrC o freshBase ops).2 = (runErrPy o freshBase ops).2 ∧
      (runErrC o freshBase ops).1.strong = (runErrPy o freshBase ops).1.strong.reverse ∧
      (runErrPy o freshBase ops).1.strong.length ≤ 8

theorem cacheTwinsFallible_proven : CacheTwinsFallible := by
  intro K _ o hE hH ops hall
  have h0 : CInv (⟨[], []⟩ : CacheSt K) ⟨[], []⟩ := ⟨rfl, rfl, List.nodup_nil, by simp, by simp⟩
  have hf : (freshBase : ZCls K) = embZ ⟨[], []⟩ (fun _ => 0) 0 := rfl
  rw [hf]
  exact run_twins o hE hH ops _ _ _ _ h0 hall

end PyLean.Datetime.Zone
