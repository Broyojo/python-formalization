import PyLean.Itertools.CountRepeatProps

/-!
`count_next` and `count_nextlong` (Modules/itertoolsmodule.c:3620-3672, GIL build) with an
add that is Python code and can call `next()` on the same count object, which is the
path of python/cpython#154670.

`count_nextlong` takes `result = lz->long_cnt` (:3633) without a new reference: the comment
at :3630-3631 says the count's own reference is either returned or kept. It then calls
`PyNumber_Add(result, lz->long_step)` (:3635). If the step's `__radd__` calls `next()` on
the same count, the inner call reads the same `long_cnt`, hands the count's reference to
its caller and stores its own sum; the outer call then stores its sum over that one and
returns `result` again (:3639-3641), a reference it no longer owns. When the inner caller
drops its value the object is freed while the outer caller holds it: the use-after-free of
#154670. With a small int (immortal) the same path runs without memory damage, and shows
the value handed out twice.

References are modelled by name: `ref` is the strong reference the count holds to
`long_cnt`, every new reference gets a `fresh` name, and the log records, for every value
`next()` returned, the reference handed over with it. Python sees only the values.

`CountRepeat.lean`'s `cCountNext` is this function for an add that does not call back
(`cNextR_lift`), so the properties proved there apply.
-/

namespace PyLean.Itertools

open PyLean

variable {ν : Type}

/-- What `PyNumber_Add(result, lz->long_step)` does when `__add__` or `__radd__` is
Python code: return its result or raise (`ret`), or call `next()` on this same count
object and go on with what that call returned or raised (`callNext`). -/
inductive AddProg (ν : Type) where
  | ret (r : Py (CVal ν))
  | callNext (k : OpRes (CVal ν) → AddProg ν)

/-- The number types' `PyNumber_Add`, given how many adds this count has started before
(a stand-in for whatever state the Python methods keep). Nothing is assumed of it. -/
structure NumOpsR (ν : Type) where
  add : Nat → CVal ν → CVal ν → AddProg ν

/-- `PyNumber_Add`: two exact ints add in C (`long_add`), running no Python code. -/
def pyAddR (N : NumOpsR ν) (n : Nat) : CVal ν → CVal ν → AddProg ν
  | .int a, .int b => .ret (.ok (.int (a + b)))
  | a, b => N.add n a b

/-- An add of `CountRepeat.lean`, which never calls back. -/
def NumOps.lift (N : NumOps ν) : NumOpsR ν := ⟨fun _ a b => .ret (N.add a b)⟩

/-- A count object (`s`), the name `ref` of the reference it holds to `long_cnt` (while
that is set), the next unused name `fresh`, the number of adds started, and every value
`next()` returned or the exception it raised, with the name of the reference handed over. -/
structure CountR (ν : Type) where
  s : CountState ν
  ref : Nat := 0
  fresh : Nat := 1
  adds : Nat := 0
  log : List (OpRes (CVal ν) × Option Nat) := []

/-- Return `r` from `next()`, handing over reference `h`. -/
def CountR.ret (t : CountR ν) (r : OpRes (CVal ν)) (h : Option Nat) : OpRes (CVal ν) × CountR ν :=
  (r, { t with log := t.log ++ [(r, h)] })

/-- The switch to slow mode (:3622-3628): `long_cnt` becomes a new reference to
`PY_SSIZE_T_MAX`. -/
def CountR.slow (t : CountR ν) : CountR ν :=
  match t.s.longCnt with
  | some _ => t
  | none => { t with s := { t.s with longCnt := some (.int ssizeMax) }, ref := t.fresh, fresh := t.fresh + 1 }

/-- After `PyNumber_Add` returned (:3636-3641): on `NULL` return it; otherwise the new
reference `stepped_up` replaces whatever `long_cnt` is now, and `result`, with the reference
`held` taken before the add, is handed over. -/
def slowEnd (result : CVal ν) (held : Nat) : Py (CVal ν) × CountR ν → OpRes (CVal ν) × CountR ν
  | (.error e, t) => t.ret (.exc e) none
  | (.ok up, t) =>
    CountR.ret { t with s := { t.s with longCnt := some up }, ref := t.fresh, fresh := t.fresh + 1 }
      (.val result) (some held)

mutual
/-- `count_next` (:3645-3672, GIL build: :3649-3651) and `count_nextlong` (:3620-3642). -/
def cNextR (N : NumOpsR ν) : Nat → CountR ν → OpRes (CVal ν) × CountR ν
  | 0, t => t.ret (.exc .modelFuel) none
  | f + 1, t =>
    if t.s.cnt = ssizeMax then
      let t := t.slow
      -- :3633: `result` is the count's own reference, not a new one
      let result := t.s.longCnt.getD (.int ssizeMax)
      -- :3635: the add may run Python code that calls `next()` on this object
      slowEnd result t.ref (runAdd N f (pyAddR N t.adds result t.s.longStep) { t with adds := t.adds + 1 })
    else
      -- :3651: `PyLong_FromSsize_t(lz->cnt++)`, a new reference
      CountR.ret { t with s := { t.s with cnt := t.s.cnt + 1 }, fresh := t.fresh + 1 }
        (.val (.int t.s.cnt)) (some t.fresh)

/-- `PyNumber_Add` running Python code: each `next()` it calls is `cNextR` on the
current object. -/
def runAdd (N : NumOpsR ν) : Nat → AddProg ν → CountR ν → Py (CVal ν) × CountR ν
  | _, .ret r, t => (r, t)
  | 0, .callNext _, t => (.error .modelFuel, t)
  | f + 1, .callNext k, t =>
    match cNextR N f t with
    | (r, t) => runAdd N f (k r) t
end

/-- `k` top-level calls of `next()`. -/
def nextsR (N : NumOpsR ν) (fuel : Nat) : Nat → CountR ν → CountR ν
  | 0, t => t
  | k + 1, t => nextsR N fuel k (cNextR N fuel t).2

/-- `count(start, step)` (`itertools_count_impl`, :3520-3595, which holds one reference to
`long_cnt`, named 0), then `k` calls of `next()`. -/
def cCountR (N : NumOpsR ν) (fuel : Nat) (start step : Option (CVal ν)) (k : Nat) : Py (CountR ν) :=
  match cCountNew start step with
  | .error e => .error e
  | .ok s => .ok (nextsR N fuel k { s := s })

/-- The references handed over with the values, in order. -/
def CountR.handed (t : CountR ν) : List Nat := t.log.filterMap Prod.snd

/-! ## Equations -/

theorem runAdd_ret (N : NumOpsR ν) (f : Nat) (r : Py (CVal ν)) (t : CountR ν) :
    runAdd N f (.ret r) t = (r, t) := by
  cases f <;> simp [runAdd]

theorem runAdd_callNext (N : NumOpsR ν) (f : Nat) (k : OpRes (CVal ν) → AddProg ν) (t : CountR ν) :
    runAdd N (f + 1) (.callNext k) t = runAdd N f (k (cNextR N f t).1) (cNextR N f t).2 := by
  simp [runAdd]

theorem cNextR_zero (N : NumOpsR ν) (t : CountR ν) : cNextR N 0 t = t.ret (.exc .modelFuel) none := by
  simp [cNextR]

theorem cNextR_fast (N : NumOpsR ν) (f : Nat) (t : CountR ν) (hc : t.s.cnt ≠ ssizeMax) :
    cNextR N (f + 1) t =
      CountR.ret { t with s := { t.s with cnt := t.s.cnt + 1 }, fresh := t.fresh + 1 }
        (.val (.int t.s.cnt)) (some t.fresh) := by
  simp [cNextR, hc]

theorem cNextR_slow (N : NumOpsR ν) (f : Nat) (t : CountR ν) (hc : t.s.cnt = ssizeMax) :
    cNextR N (f + 1) t =
      slowEnd (t.slow.s.longCnt.getD (.int ssizeMax)) t.slow.ref
        (runAdd N f (pyAddR N t.slow.adds (t.slow.s.longCnt.getD (.int ssizeMax)) t.slow.s.longStep)
          { t.slow with adds := t.slow.adds + 1 }) := by
  simp [cNextR, hc]

/-! ## Without re-entry -/

/-- With an add that does not call back, this is `cCountNext`: the same result and the
same object, for every fuel and state, so `CountConsistent` and the other properties of
`CountRepeatProps.lean` hold of the mirror with re-entry. -/
theorem cNextR_lift (N : NumOps ν) (f : Nat) (t : CountR ν) :
    (cNextR N.lift (f + 1) t).1 = (cCountNext N t.s).1 ∧
      (cNextR N.lift (f + 1) t).2.s = (cCountNext N t.s).2 := by
  have hadd : ∀ (n : Nat) (a b : CVal ν), pyAddR N.lift n a b = .ret (pyAdd N a b) := by
    intro n a b
    cases a <;> cases b <;> rfl
  rcases t with ⟨⟨cnt, lc, st⟩, ref, fresh, adds, log⟩
  by_cases hc : cnt = ssizeMax
  · subst hc
    rw [cNextR_slow N.lift f _ rfl]
    cases lc with
    | none =>
      cases ha : pyAdd N (.int ssizeMax) st <;>
        simp [CountR.slow, hadd, runAdd_ret, slowEnd, cCountNext, ha, CountR.ret]
    | some v =>
      cases ha : pyAdd N v st <;>
        simp [CountR.slow, hadd, runAdd_ret, slowEnd, cCountNext, ha, CountR.ret]
  · rw [cNextR_fast N.lift f _ hc]
    simp [cCountNext, hc, CountR.ret]

/-- An add that never calls `next()` on the count. -/
def NoCallback (N : NumOpsR ν) : Prop := ∀ n a b, ∃ r, N.add n a b = .ret r

/-- The bookkeeping over the handed-over references `H`: all older than `fresh`, the
count's own (when it holds one) older too and not handed over, none handed over twice. -/
def RefOk (H : List Nat) (fresh ref : Nat) (holds : Bool) : Prop :=
  (∀ r ∈ H, r < fresh) ∧ (holds = true → ref < fresh ∧ ref ∉ H) ∧ H.Nodup

/-- What `count_nextlong` relies on (:3630-3631), for an object. -/
def RefInv (t : CountR ν) : Prop := RefOk t.handed t.fresh t.ref t.s.longCnt.isSome

theorem nodup_snoc (H : List Nat) (x : Nat) (h : H.Nodup) (hx : x ∉ H) : (H ++ [x]).Nodup := by
  rw [List.nodup_append]
  refine ⟨h, by simp, ?_⟩
  intro a ha b hb
  simp only [List.mem_singleton] at hb
  subst hb
  intro hab; subst hab; exact hx ha

theorem refOk_fast (H : List Nat) (f r : Nat) (b : Bool) (h : RefOk H f r b) : RefOk (H ++ [f]) (f + 1) r b := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun x hx => ?_, fun hb => ?_, nodup_snoc H f h3 (fun hm => by have := h1 _ hm; omega)⟩
  · simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx
    · have := h1 x hx; omega
    · omega
  · obtain ⟨h2a, h2b⟩ := h2 hb
    refine ⟨by omega, ?_⟩
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨h2b, by omega⟩

theorem refOk_new (H : List Nat) (f r : Nat) (b : Bool) (h : RefOk H f r b) : RefOk H (f + 1) f true := by
  obtain ⟨h1, _, h3⟩ := h
  exact ⟨fun x hx => by have := h1 x hx; omega, fun _ => ⟨by omega, fun hm => by have := h1 _ hm; omega⟩, h3⟩

theorem refOk_hand (H : List Nat) (f r : Nat) (h : RefOk H f r true) : RefOk (H ++ [r]) (f + 1) f true := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h2a, h2b⟩ := h2 rfl
  refine ⟨fun x hx => ?_, fun _ => ⟨by omega, ?_⟩, nodup_snoc H r h3 h2b⟩
  · simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx
    · have := h1 x hx; omega
    · omega
  · simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨fun hm => by have := h1 _ hm; omega, by omega⟩

theorem handed_log (t : CountR ν) (r : OpRes (CVal ν)) (h : Option Nat) :
    (t.ret r h).2.handed = t.handed ++ h.toList := by
  cases h <;> simp [CountR.ret, CountR.handed, List.filterMap_append]

theorem refInv_slow (t : CountR ν) (h : RefInv t) :
    RefOk t.slow.handed t.slow.fresh t.slow.ref true ∧ t.slow.s.longCnt.isSome = true := by
  unfold CountR.slow
  split
  · rename_i v hv
    unfold RefInv at h
    rw [hv] at h
    exact ⟨h, by simp [hv]⟩
  · exact ⟨refOk_new _ _ _ _ h, rfl⟩

theorem refInv_step {ν : Type} (N : NumOpsR ν) (hN : NoCallback N) (f : Nat) (t : CountR ν)
    (h : RefInv t) : RefInv (cNextR N f t).2 := by
  unfold RefInv at h
  cases f with
  | zero =>
    rw [cNextR_zero]
    unfold RefInv
    rw [handed_log]
    simpa [CountR.ret] using h
  | succ f =>
    by_cases hc : t.s.cnt = ssizeMax
    · obtain ⟨hs, hsome⟩ := refInv_slow t h
      have hadd : ∀ a b, ∃ r, pyAddR N t.slow.adds a b = .ret r := by
        intro a b
        cases a <;> cases b <;> first | exact ⟨_, rfl⟩ | exact hN _ _ _
      obtain ⟨r, hr⟩ := hadd (t.slow.s.longCnt.getD (.int ssizeMax)) t.slow.s.longStep
      rw [cNextR_slow N f t hc, hr, runAdd_ret]
      cases r with
      | error e =>
        unfold RefInv
        simp only [slowEnd]
        rw [handed_log]
        simpa [CountR.ret, CountR.handed, hsome] using hs
      | ok up =>
        unfold RefInv
        simp only [slowEnd]
        rw [handed_log]
        simpa [CountR.ret, CountR.handed] using refOk_hand _ _ _ hs
    · rw [cNextR_fast N f t hc]
      unfold RefInv
      rw [handed_log]
      simpa [CountR.ret, CountR.handed] using refOk_fast _ _ _ _ h

theorem refInv_nexts {ν : Type} (N : NumOpsR ν) (hN : NoCallback N) (fuel : Nat) :
    ∀ (k : Nat) (t : CountR ν), RefInv t → RefInv (nextsR N fuel k t)
  | 0, _, h => h
  | k + 1, t, h => refInv_nexts N hN fuel k _ (refInv_step N hN fuel t h)

/-- With an add that does not call back into the count, for every number type, start,
step, fuel and number of `next()` calls: the mirror with re-entry is `cCountNext` (result
and object), and no reference to a value is handed over twice, which is what the comment at
:3630-3631 relies on. -/
def CountNextNoReentry : Prop :=
  ∀ (ν : Type),
    (∀ (N : NumOps ν) (f : Nat) (t : CountR ν),
      (cNextR N.lift (f + 1) t).1 = (cCountNext N t.s).1 ∧
        (cNextR N.lift (f + 1) t).2.s = (cCountNext N t.s).2) ∧
    (∀ (N : NumOpsR ν) (fuel : Nat) (start step : Option (CVal ν)) (k : Nat) (t : CountR ν),
      NoCallback N → cCountR N fuel start step k = .ok t → t.handed.Nodup)

theorem countNextNoReentry_proven : CountNextNoReentry := by
  intro ν
  refine ⟨cNextR_lift, fun N fuel start step k t hN h => ?_⟩
  simp only [cCountR] at h
  split at h
  · cases h
  · rename_i s _
    cases h
    have h0 : RefInv ({ s := s } : CountR ν) :=
      ⟨by simp [CountR.handed], fun _ => ⟨Nat.zero_lt_one, by simp [CountR.handed]⟩, by simp [CountR.handed]⟩
    exact (refInv_nexts N hN fuel k _ h0).2.2

/-! ## The re-entrant `__radd__` of python/cpython#154670 -/

/-- In slow mode with value `v` and a step that is not an exact int, when the add calls
`next()` once and then answers `up`, and the add of that inner call answers `w` without
calling back: the inner call returns `v` and hands over the count's reference, and stores
`w` under a new reference; the outer call then stores `up` over it (that reference is never
released) and returns `v` again with the same reference (:3633-3641). So `next()` gives `v`
twice, `w` is lost, and one reference has been handed to two callers: when one of them drops
it, the other holds a freed object. For every number type, value, step and state. -/
def CountReentryTwice : Prop :=
  ∀ (ν : Type) (N : NumOpsR ν) (f : Nat) (t : CountR ν) (v w up : CVal ν)
    (k : OpRes (CVal ν) → AddProg ν),
    t.s.cnt = ssizeMax → t.s.longCnt = some v → (∀ i, t.s.longStep ≠ .int i) →
    N.add t.adds v t.s.longStep = .callNext k →
    N.add (t.adds + 1) v t.s.longStep = .ret (.ok w) →
    k (.val v) = .ret (.ok up) →
    cNextR N (f + 3) t =
      (.val v, { t with s := { t.s with longCnt := some up }, ref := t.fresh + 1, fresh := t.fresh + 2,
                        adds := t.adds + 2,
                        log := t.log ++ [(.val v, some t.ref), (.val v, some t.ref)] })

theorem countReentryTwice_proven : CountReentryTwice := by
  intro ν N f t v w up k h1 h2 h3 h4 h5 h6
  rcases t with ⟨⟨cnt, lc, st⟩, ref, fresh, adds, log⟩
  simp only at h1 h2 h3 h4 h5 ⊢
  subst h1 h2
  have hp : ∀ n, pyAddR N n v st = N.add n v st := by
    intro n
    cases v <;> cases st <;> first | rfl | exact absurd rfl (h3 _)
  rw [cNextR_slow N (f + 2) _ rfl]
  simp only [CountR.slow, Option.getD_some, hp, h4, runAdd_callNext]
  rw [cNextR_slow N f _ rfl]
  simp only [CountR.slow, Option.getD_some, hp, h5, runAdd_ret, slowEnd, CountR.ret, h6]
  simp [List.append_assoc]

/-- Broad: whatever the add does, no reference is handed over twice along any sequence
of top-level `next()` calls. -/
def CountHandsOutOnce : Prop :=
  ∀ (ν : Type) (N : NumOpsR ν) (fuel : Nat) (start step : Option (CVal ν)) (k : Nat) (t : CountR ν),
    cCountR N fuel start step k = .ok t → t.handed.Nodup

/-- The step of the reproducer: `__radd__` of its first call does `next(c)`, and every call
answers `other + 1`. -/
def reentrantStep : NumOpsR Unit :=
  ⟨fun n a _ =>
    let up : CVal Unit := .int (a.longVal + 1)
    if n = 0 then .callNext (fun _ => .ret (.ok up)) else .ret (.ok up)⟩

/-- What a run shows: the references handed over, the values returned, and `long_cnt`. -/
def CountR.shown (t : CountR ν) : List Nat × List (Option Int) × Option Int :=
  (t.handed, t.log.map (fun p => match p.1 with | .val v => some v.longVal | _ => none),
    t.s.longCnt.map CVal.longVal)

/-- `count(5, Step())` then one top-level `next()`: the inner and the outer call both return
`5` with reference 0, the count's own, and `long_cnt` is the outer sum `6`. -/
theorem reentrantStep_run :
    (cCountR reentrantStep 5 (some (.int 5)) (some (.num ())) 1).toOption.map CountR.shown =
      some ([0, 0], [some 5, some 5], some 6) := by
  decide

theorem countHandsOutOnce_refuted : ¬CountHandsOutOnce := by
  intro h
  have hr := reentrantStep_run
  revert hr
  cases hc : cCountR reentrantStep 5 (some (.int 5)) (some (.num ())) 1 with
  | error e => simp [Except.toOption]
  | ok t =>
    have := h Unit reentrantStep 5 _ _ 1 t hc
    intro hr
    simp only [Except.toOption, Option.map_some, Option.some.injEq, CountR.shown, Prod.mk.injEq] at hr
    rw [hr.1] at this
    exact absurd this (by decide)

end PyLean.Itertools
