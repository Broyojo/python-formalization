import PyLean.CoreLibs.Functools.Wrap
import PyLean.CoreLibs.Functools.DispatchProps
import PyLean.CoreLibs.Functools.LruProps

/-!
Properties of `update_wrapper`, `wraps`, `cached_property`, `singledispatchmethod`, the `reduce` wrapper and the
decorator layer of `lru_cache`.
-/

namespace PyLean.CoreLibs.Functools

open PyLean

section
variable {α : Type}

theorem setAttr_same (o : Attrs α) (k : String) (v : α) : (setAttr o k v).lookup k = some v := by
  unfold setAttr
  by_cases h : o.any (fun p => p.1 == k) = true
  · simp only [h, ite_true]
    induction o with
    | nil => simp at h
    | cons p ps ih =>
      by_cases e : p.1 = k
      · simp [e, List.lookup]
      · have e1 : (p.1 == k) = false := by simpa using e
        have e2 : (k == p.1) = false := by
          have : k ≠ p.1 := fun x => e x.symm
          simpa using this
        have h' : ps.any (fun p => p.1 == k) = true := by simpa [e1] using h
        simp only [List.map_cons, e1, Bool.false_eq_true, ite_false, List.lookup, e2]
        exact ih h'
  · have h' : o.any (fun p => p.1 == k) = false := Bool.eq_false_iff.mpr h
    simp only [h', Bool.false_eq_true, ite_false]
    induction o with
    | nil => simp [List.lookup]
    | cons p ps ih =>
      have e1 : (p.1 == k) = false := by
        cases hx : p.1 == k with
        | false => rfl
        | true => simp [hx] at h'
      have e : p.1 ≠ k := by simpa using e1
      have e2 : (k == p.1) = false := by
        have : k ≠ p.1 := fun x => e x.symm
        simpa using this
      have h2 : ps.any (fun p => p.1 == k) = false := by simpa [e1] using h'
      simp only [List.cons_append, List.lookup, e2]
      exact ih (by simp [h2]) h2

theorem setAttr_other (o : Attrs α) (k j : String) (v : α) (h : j ≠ k) :
    (setAttr o k v).lookup j = o.lookup j := by
  have e2 : (j == k) = false := by simpa using h
  unfold setAttr
  by_cases hh : o.any (fun p => p.1 == k) = true
  · simp only [hh, ite_true]
    clear hh
    induction o with
    | nil => rfl
    | cons p ps ih =>
      by_cases e : p.1 = k
      · have e1 : (j == p.1) = false := by rw [e]; exact e2
        have e3 : (p.1 == k) = true := by simp [e]
        simp only [List.map_cons, e3, ite_true, List.lookup, e2, e1]
        exact ih
      · have e1 : (p.1 == k) = false := by simpa using e
        simp only [List.map_cons, e1, Bool.false_eq_true, ite_false, List.lookup]
        cases hj : j == p.1 with
        | true => rfl
        | false => exact ih
  · have h' : o.any (fun p => p.1 == k) = false := Bool.eq_false_iff.mpr hh
    simp only [h', Bool.false_eq_true, ite_false]
    clear hh h'
    induction o with
    | nil => simp [List.lookup, e2]
    | cons p ps ih =>
      simp only [List.cons_append, List.lookup]
      cases hj : j == p.1 with
      | true => rfl
      | false => exact ih

/-- `assigned`'s effect on the table, when every read and write succeeds. -/
def assignDict (r : String → Option α) (assigned : List String) (d : Attrs α) : Attrs α :=
  assigned.foldl (fun acc a =>
    match r a with
    | some v => setAttr acc a v
    | none => acc) d

theorem assignLoop_ok (wrapped : Wrapped α) (r : String → Option α) (h : ∀ a, wrapped.read a = .ok (r a)) :
    ∀ (assigned : List String) (w : Wrapper α), w.hasDict = true → w.setFail = (fun _ => none) → w.descr = [] →
    assignLoop wrapped assigned w = .ok { w with dict := assignDict r assigned w.dict }
  | [], w, _, _, _ => rfl
  | a :: rest, w, hd, hs, hq => by
    have hf : assignDict r (a :: rest) w.dict = assignDict r rest (match r a with
        | some v => setAttr w.dict a v
        | none => w.dict) := rfl
    rw [hf]
    simp only [assignLoop, h]
    cases hr : r a with
    | none => exact assignLoop_ok wrapped r h rest w hd hs hq
    | some v =>
      have hw : wrapperSet w a v = .ok { w with dict := setAttr w.dict a v } := by
        simp [wrapperSet, hs, hd, hq]
      simp only [hw]
      exact assignLoop_ok wrapped r h rest { w with dict := setAttr w.dict a v } hd hs hq

theorem assign_lookup (r : String → Option α) (k : String) (v : α) (hv : r k = some v) :
    ∀ (assigned : List String) (d : Attrs α), (k ∈ assigned ∨ d.lookup k = some v) →
    (assignDict r assigned d).lookup k = some v
  | [], d, h => by simpa [assignDict] using h
  | a :: rest, d, h => by
    simp only [assignDict, List.foldl_cons]
    apply assign_lookup r k v hv rest
    by_cases e : a = k
    · subst e
      right
      simp only [hv, setAttr_same]
    · rcases h with h | h
      · rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm e
        · exact Or.inl h
      · right
        cases hr : r a with
        | none => simpa using h
        | some x => simp only [setAttr_other _ _ _ _ (fun y => e y.symm), h]

theorem assign_other (r : String → Option α) (k : String) : ∀ (assigned : List String) (d : Attrs α),
    k ∉ assigned → (assignDict r assigned d).lookup k = d.lookup k
  | [], _, _ => rfl
  | a :: rest, d, h => by
    have hf : assignDict r (a :: rest) d = assignDict r rest (match r a with
        | some v => setAttr d a v
        | none => d) := rfl
    have h1 : k ≠ a := fun e => h (by simp [e])
    have h2 : k ∉ rest := fun e => h (List.mem_cons_of_mem _ e)
    rw [hf, assign_other r k rest _ h2]
    cases r a with
    | none => rfl
    | some v => exact setAttr_other _ _ _ _ h1

theorem update_keeps (e : Attrs α) (k : String) (he : e.lookup k = none) : ∀ (d : Attrs α),
    (dictUpdate d e).lookup k = d.lookup k := by
  induction e with
  | nil => intro d; rfl
  | cons p ps ih =>
    intro d
    have e1 : (k == p.1) = false := by
      cases hx : k == p.1 with
      | false => rfl
      | true => simp [List.lookup, hx] at he
    have hk : k ≠ p.1 := by simpa using e1
    have hp : ps.lookup k = none := by simpa [List.lookup, e1] using he
    simp only [dictUpdate, List.foldl_cons]
    have := ih hp (setAttr d p.1 p.2)
    simp only [dictUpdate] at this
    rw [this, setAttr_other _ _ _ _ hk]

theorem update_last (e : Attrs α) (k : String) (v : α) (he : (e.reverse).lookup k = some v) :
    ∀ d : Attrs α, (dictUpdate d e).lookup k = some v := by
  intro d
  have key : ∀ (l : List (String × α)) (d : Attrs α), l.lookup k = some v →
      (l.foldr (fun p acc => setAttr acc p.1 p.2) d).lookup k = some v := by
    intro l
    induction l with
    | nil => intro d h; simp at h
    | cons x xs ih =>
      intro d h
      simp only [List.foldr_cons]
      simp only [List.lookup] at h
      cases hx : k == x.1 with
      | true =>
        simp only [hx, Option.some.injEq] at h
        subst h
        have : k = x.1 := by simpa using hx
        rw [this]
        exact setAttr_same _ _ _
      | false =>
        simp only [hx] at h
        have : k ≠ x.1 := by simpa using hx
        rw [setAttr_other _ _ _ _ this]
        exact ih d h
  simp only [dictUpdate, List.foldl_eq_foldr_reverse]
  exact key e.reverse d he

end

/-- `update_wrapper(wrapper, wrapped)` with the default `updated`, on a wrapper that keeps its attributes in `__dict__`,
which is the case `hasDict` with no `descr`, when every read and write succeeds: `__wrapped__` is the wrapped object even if `__dict__` copied a `__wrapped__` from it, which is why the
assignment comes last (issue 17482, Lib/functools.py:59); an entry of `wrapped.__dict__` wins, in the order of
the dict, over an assigned attribute of the same name, because the update comes second; an assigned attribute
not in that dict is copied; an attribute `wrapped` lacks is skipped; everything else on the wrapper stays. A
real `__dict__` table is used, so swapping any two steps fails one of these. -/
def UpdateWrapperOrder : Prop :=
  ∀ (α : Type) (w : Wrapper α) (wrapped : Wrapped α) (r : String → Option α) (D : Attrs α) (self v : α)
    (assigned : List String) (k : String),
    (∀ a, wrapped.read a = .ok (r a)) → wrapped.dictOf "__dict__" = .ok (some D) → w.hasDict = true →
    w.setFail = (fun _ => none) → w.descr = [] → w.readFail = (fun _ => none) → k ≠ "__wrapped__" →
    ∃ w', updateWrapper w wrapped self assigned ["__dict__"] = .ok w' ∧
      w'.dict.lookup "__wrapped__" = some self ∧
      (D.reverse.lookup k = some v → w'.dict.lookup k = some v) ∧
      (D.lookup k = none → r k = some v → k ∈ assigned → w'.dict.lookup k = some v) ∧
      (D.lookup k = none → k ∉ assigned → w'.dict.lookup k = w.dict.lookup k) ∧
      (D.lookup k = none → r k = none → w'.dict.lookup k = w.dict.lookup k ∨ k ∈ assigned)

theorem updateWrapperOrder_proven : UpdateWrapperOrder := by
  intro α w wrapped r D self v assigned k hr hd hhas hset hq hrf hk
  have h1 := assignLoop_ok wrapped r hr assigned w hhas hset hq
  let w1 : Wrapper α := { w with dict := assignDict r assigned w.dict }
  have hu : updateLoop wrapped ["__dict__"] w1 = .ok { w1 with dict := dictUpdate w1.dict D } := by
    simp [updateLoop, hd, w1, hhas, hrf]
  let w2 : Wrapper α := { w1 with dict := dictUpdate w1.dict D }
  refine ⟨{ w2 with dict := setAttr w2.dict "__wrapped__" self }, ?_, setAttr_same _ _ _, ?_, ?_, ?_, ?_⟩
  · have hu' : updateLoop wrapped ["__dict__"] { w with dict := assignDict r assigned w.dict } =
        .ok w2 := hu
    simp only [updateWrapper, h1, hu']
    simp [wrapperSet, w2, w1, hset, hhas, hq]
  · intro h
    simp only [setAttr_other _ _ _ _ hk]
    exact update_last D k v h _
  · intro h1 h2 h3
    simp only [setAttr_other _ _ _ _ hk, w2, w1, update_keeps D k h1]
    exact assign_lookup r k v h2 assigned _ (Or.inl h3)
  · intro h1 h3
    simp only [setAttr_other _ _ _ _ hk, w2, w1, update_keeps D k h1]
    exact assign_other r k assigned _ h3
  · intro h1 h2
    by_cases h3 : k ∈ assigned
    · exact Or.inr h3
    · left
      simp only [setAttr_other _ _ _ _ hk, w2, w1, update_keeps D k h1]
      exact assign_other r k assigned _ h3

/-- What `update_wrapper` does not catch: only `AttributeError` on a read of an assigned attribute is skipped. Any
other exception from that read, an exception from `setattr`, a wrapper with no `__dict__`, and an exception from
reading `wrapped.__dict__` all propagate. -/
def UpdateWrapperFailures : Prop :=
  ∀ (α : Type) (w : Wrapper α) (wrapped : Wrapped α) (self v : α) (a : String) (e : PyExc)
    (rest updated : List String),
    (wrapped.read a = .error e →
      updateWrapper w wrapped self (a :: rest) updated = .error e) ∧
    (wrapped.read a = .ok (some v) → w.setFail a = some e →
      updateWrapper w wrapped self (a :: rest) updated = .error e) ∧
    (w.readFail a = some e → updateLoop wrapped (a :: rest) w = .error e) ∧
    (w.readFail "__dict__" = none → w.hasDict = false →
      (updateLoop wrapped ("__dict__" :: rest) w).raises "AttributeError") ∧
    (w.readFail "__dict__" = none → w.hasDict = true → wrapped.dictOf "__dict__" = .error e →
      updateLoop wrapped ("__dict__" :: rest) w = .error e)

theorem updateWrapperFailures_proven : UpdateWrapperFailures := by
  intro α w wrapped self v a e rest updated
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    simp [updateWrapper, assignLoop, h]
  · intro h1 h2
    simp [updateWrapper, assignLoop, h1, wrapperSet, h2]
  · intro h
    simp [updateLoop, h]
  · intro h1 h2
    exact ⟨.named "AttributeError" "~object has no attribute", by simp [updateLoop, h1, h2], rfl⟩
  · intro h0 h1 h2
    simp [updateLoop, h0, h1, h2]

/-- `wraps(wrapped, assigned, updated)` builds the `partial` and applying it to a wrapper is `update_wrapper`
with those arguments: the docstring's "a decorator factory", through the real `partial`. -/
def WrapsIsPartial : Prop :=
  ∀ (α : Type) (wrapped : Wrapped α) (self : α) (a u : List String) (w : Wrapper α),
    ∃ p, wraps wrapped self a u = .ok p ∧ wrapsCall p w = updateWrapper w wrapped self a u

theorem wrapsIsPartial_proven : WrapsIsPartial := by
  intro α wrapped self a u w
  refine ⟨_, rfl, ?_⟩
  rfl

/-- `update_wrapper` on a function: the six names of `WRAPPER_ASSIGNMENTS` are data descriptors of the type, outside
`__dict__`, so what an entry of `wrapped.__dict__` does to the table does not reach them, and `wrapper.__name__` keeps the
assigned value, where on an object that stores its attributes in `__dict__` the entry wins (`UpdateWrapperOrder`). The
entry is still in the wrapper's `__dict__`. -/
def UpdateWrapperFunction : Prop :=
  ∀ (α : Type) (w : Wrapper α) (wrapped : Wrapped α) (self v d : α) (k : String) (D : Attrs α),
    w.hasDict = true → w.descr = [k] → w.setFail = (fun _ => none) → w.readFail = (fun _ => none) →
    wrapped.read k = .ok (some v) → wrapped.dictOf "__dict__" = .ok (some D) → D.reverse.lookup k = some d →
    k ≠ "__wrapped__" →
    ∃ w', updateWrapper w wrapped self [k] ["__dict__"] = .ok w' ∧ w'.get k = some v ∧ w'.dict.lookup k = some d ∧
      w'.get "__wrapped__" = some self

theorem updateWrapperFunction_proven : UpdateWrapperFunction := by
  intro α w wrapped self v d k D hh hq hs hr hrd hd hdl hk
  have hne : ("__wrapped__" : String) ≠ k := fun e => hk e.symm
  have hc : (w.descr.contains "__wrapped__") = false := by
    rw [hq]
    simp [hne]
  have hmem : k ∈ w.descr := by rw [hq]; simp
  let w1 : Wrapper α := { w with slots := setAttr w.slots k v }
  let w2 : Wrapper α := { w1 with dict := dictUpdate w1.dict D }
  have h1 : assignLoop wrapped [k] w = .ok w1 := by
    simp [assignLoop, hrd, wrapperSet, hs, hh, hmem, w1]
  have h2 : updateLoop wrapped ["__dict__"] w1 = .ok w2 := by
    simp [updateLoop, w1, w2, hd, hh, hr]
  have h3 : wrapperSet w2 "__wrapped__" self = .ok { w2 with dict := setAttr w2.dict "__wrapped__" self } := by
    simp only [wrapperSet, w2, w1, hs, hh, hc, Bool.not_false, Bool.and_self, ↓reduceIte]
  refine ⟨{ w2 with dict := setAttr w2.dict "__wrapped__" self }, ?_, ?_, ?_, ?_⟩
  · simp only [updateWrapper, h1, h2, h3]
  · have hc2 : w.descr.contains k = true := by simpa using hmem
    simp only [Wrapper.get, w2, w1, hc2, Bool.true_or, ↓reduceIte]
    exact setAttr_same _ _ _
  · simp only [setAttr_other _ _ _ _ hk, w2, w1]
    exact update_last D k d hdl _
  · simp only [Wrapper.get, w2, w1, hc, hh, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    exact setAttr_same _ _ _

/-- `wraps` takes any object, as `update_wrapper` does. False: `wraps` makes a `partial` with keywords, and `partial` refuses
`Placeholder` as a keyword, so `wraps(Placeholder)` raises `TypeError` while `update_wrapper(f, Placeholder)` works. -/
def WrapsAcceptsAnything : Prop :=
  ∀ (α : Type) (x y z : PArg (WArg α)), ∃ p, wrapsP x y z = .ok p

theorem wrapsAcceptsAnything_refuted : ¬WrapsAcceptsAnything := by
  intro h
  obtain ⟨p, hp⟩ := h Nat .ph (.val (.names [])) (.val (.names []))
  have e : wrapsP (α := Nat) .ph (.val (.names [])) (.val (.names [])) =
      .error (.typeError "Placeholder cannot be passed as a keyword argument") := rfl
  rw [e] at hp
  cases hp

/-- A cached function reports its own `cache_parameters()`: "a function `cache_parameters()` ... for introspection". False
when the wrapped object is a cached function itself: `update_wrapper` at Lib/functools.py:600 runs after `cache_parameters`
is set at :599 and copies the `__dict__` of the inner cache over it, so the outer cache reports the inner's `maxsize` and
`typed`. On the Python wrapper `cache_info` and `cache_clear` are overwritten too. -/
def LruOwnParams : Prop :=
  ∀ (τ : Type) (py : Bool) (id : Nat) (mode : Option Int → Py LruMode) (arg : MaxsizeArg) (t : τ) (m : Option Int)
    (user : Wrapped (LruAttr τ)) (self : LruAttr τ) (w : LruMode) (W : Wrapper (LruAttr τ)), lruCacheArg arg = .ok m →
    lruBuild py id mode arg t user self = .ok (w, W) → W.dict.lookup "cache_parameters" = some (.params m t)

theorem lruOwnParams_refuted : ¬LruOwnParams := by
  intro h
  let user : Wrapped (LruAttr Bool) :=
    ⟨fun _ => .ok none, fun _ => .ok (some [("cache_parameters", .params (some 7) false)])⟩
  have e : (match lruBuild false 2 (wrapperPyMode true) (.int 5) true user (.other 0) with
      | .ok (_, W) => W.dict.lookup "cache_parameters"
      | .error _ => none) = some (.params (some 7) false) := by decide +kernel
  cases hb : lruBuild false 2 (wrapperPyMode true) (.int 5) true user (.other 0) with
  | error x =>
    rw [hb] at e
    cases e
  | ok r =>
    obtain ⟨w, W⟩ := r
    have h1 := h Bool false 2 (wrapperPyMode true) (.int 5) true (some 5) user (.other 0) w W rfl hb
    rw [hb] at e
    simp only at e
    rw [h1] at e
    simp at e

/-- The narrowed statement: on a user function whose `__dict__` has no `cache_parameters`, the wrapper keeps its own, and
`typed` comes back as the object it was given, not as a truth value. -/
def LruParamsFresh : Prop :=
  ∀ (τ : Type) (py : Bool) (id : Nat) (mode : Option Int → Py LruMode) (arg : MaxsizeArg) (t : τ) (m : Option Int)
    (D : Attrs (LruAttr τ)) (self : LruAttr τ) (w : LruMode) (W : Wrapper (LruAttr τ)), lruCacheArg arg = .ok m →
    D.lookup "cache_parameters" = none →
    lruBuild py id mode arg t ⟨fun _ => .ok none, fun _ => .ok (some D)⟩ self = .ok (w, W) →
    W.dict.lookup "cache_parameters" = some (.params m t)

theorem lruParamsFresh_proven : LruParamsFresh := by
  intro τ py id mode arg t m D self w W ha hD h
  simp only [lruBuild, ha] at h
  split at h
  · simp at h
  rename_i w' hw
  split at h
  · simp at h
  rename_i r hr
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  have hne : ("cache_parameters" : String) ≠ "__wrapped__" := by decide
  simp only [updateWrapper, wrapperAssignments, assignLoop, wrapperUpdates, updateLoop] at hr
  simp only [dictUpdate] at hr
  simp [wrapperSet] at hr
  rw [← hr]
  have key : ∀ (d : Attrs (LruAttr τ)), d.lookup "cache_parameters" = some (.params m t) →
      (setAttr (dictUpdate d D) "__wrapped__" self).lookup "cache_parameters" = some (.params m t) := by
    intro d hd
    rw [setAttr_other _ _ _ _ hne, update_keeps D _ hD, hd]
  have hl : (lruDict py id m t).lookup "cache_parameters" = some (.params m t) := by
    cases py with
    | false => simp [lruDict]
    | true =>
      have h1 : ("cache_parameters" == "cache_info") = false := by decide
      have h2 : ("cache_parameters" == "cache_clear") = false := by decide
      simp only [lruDict, ↓reduceIte, List.cons_append, List.nil_append, List.lookup_cons, h1, h2, beq_self_eq_true]
  exact key _ hl

/-- `lru_cache` as a decorator, in both twins: `cache` is the unbounded wrapper with `maxsize=None` and
`typed=False`, connecting `cache` to the mode; a negative `maxsize` is `0`, which is uncached, and
`cache_parameters()` then says `0`; the bare form takes `128`; `typed` is kept; an exception from
`update_wrapper` comes out of the decoration. Lib/functools.py:581-601. -/
def LruDecorates : Prop :=
  ∀ (n : Int) (t : Bool) (e : PyExc), n < 0 →
    cacheDecorate (wrapperCMode true) none = .ok ⟨.infinite, none, false⟩ ∧
    cacheDecorate (wrapperPyMode true) none = .ok ⟨.infinite, none, false⟩ ∧
    lruDecorate (wrapperCMode true) (.int n) t none = .ok ⟨.uncached, some 0, t⟩ ∧
    lruDecorate (wrapperPyMode true) (.int n) t none = .ok ⟨.uncached, some 0, t⟩ ∧
    lruDecorate (wrapperCMode true) (.callable true) t none = .ok ⟨.bounded 128, some 128, t⟩ ∧
    lruDecorate (wrapperPyMode true) (.callable true) t none = .ok ⟨.bounded 128, some 128, t⟩ ∧
    lruDecorate (wrapperCMode true) .none t (some e) = .error e ∧
    (lruDecorate (wrapperPyMode true) (.callable false) t none).raises "TypeError"

theorem lruDecorates_proven : LruDecorates := by
  intro n t e h
  have h1 : (if n < 0 then (0 : Int) else n) = 0 := by simp [h]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, ⟨_, rfl, rfl⟩⟩
  · simp [lruDecorate, lruCacheArg, h1, wrapperCMode, ssizeMax, ssizeMin]
  · simp [lruDecorate, lruCacheArg, h1, wrapperPyMode]
  · simp [lruDecorate, lruCacheArg, wrapperCMode, ssizeMax, ssizeMin]
  · simp [lruDecorate, lruCacheArg, wrapperPyMode]

/-- The pure-Python `reduce` wrapper warns exactly when `function` or `sequence` is a keyword. If the warning
raises, as under `-W error`, `py_reduce` is not run; otherwise its outcome comes out unchanged, an exception
included. -/
def ReduceWarnWrapper : Prop :=
  ∀ (β : Type) (names : List String) (e : PyExc) (call : Py β),
    ((reduceWarnWrapper names (.ok ()) call).2 = true ↔ ("function" ∈ names ∨ "sequence" ∈ names)) ∧
    (reduceWarnWrapper names (.ok ()) call).1 = call ∧
    (("function" ∈ names ∨ "sequence" ∈ names) → (reduceWarnWrapper names (.error e) call).1 = .error e) ∧
    (¬("function" ∈ names ∨ "sequence" ∈ names) → (reduceWarnWrapper names (.error e) call).1 = call)

theorem reduceWarnWrapper_proven : ReduceWarnWrapper := by
  intro β names e call
  by_cases h : "function" ∈ names ∨ "sequence" ∈ names
  · have h' : (names.contains "function" || names.contains "sequence") = true := by simpa using h
    simp [reduceWarnWrapper, h', h]
  · have h' : (names.contains "function" || names.contains "sequence") = false := by
      simpa using h
    simp [reduceWarnWrapper, h', h]

/-- `cached_property`: on the class it gives itself. The first read runs the function, and stores what it returns under
the name in the instance dict as the function left it, overriding anything it stored there itself; a later read returns
that value without running any function. Without `__set_name__`, or without an instance `__dict__`, a read raises
`TypeError`; another exception from `instance.__dict__` or from `cache.get` propagates, before the function runs. A
function that raises stores nothing under the name, and what it did to the dict stays. A store that raises `TypeError`
is a `TypeError` of its own message, after running the function, and any other exception from the store propagates.
`__set_name__` accepts the same name twice and rejects a second name. Docs of `cached_property`. -/
def CachedPropertyOnce : Prop :=
  ∀ (α : Type) (func bad : Attrs α → Py α × Attrs α) (name : String) (doc mod v : α) (d d' : Attrs α) (e : PyExc),
    d.lookup name = none → func d = (.ok v, d') →
    let c (f : Attrs α → Py α × Attrs α) (n : Option String) : CachedProp α := ⟨f, n, doc, mod⟩
    (∃ d2, cachedGet (c func (some name)) (some (.dict d none none)) = (.ok (.val v), some d2) ∧
      d2.lookup name = some v ∧
      cachedGet (c bad (some name)) (some (.dict d2 none none)) = (.ok (.val v), some d2)) ∧
    (cachedGet (c func none) none).1 = .ok .self ∧
    (cachedGet (c func none) (some (.dict d none none))).1.raises "TypeError" ∧
    (cachedGet (c func (some name)) (some .none)).1.raises "TypeError" ∧
    (cachedGet (c bad (some name)) (some (.raises e))).1 = .error e ∧
    cachedGet (c bad (some name)) (some (.dict d (some e) none)) = (.error e, some d) ∧
    (bad d = (.error e, d') → cachedGet (c bad (some name)) (some (.dict d none none)) = (.error e, some d')) ∧
    (cachedGet (c func (some name)) (some (.dict d none (some (e, true))))).1.raises "TypeError" ∧
    (cachedGet (c func (some name)) (some (.dict d none (some (e, false))))) = (.error e, some d') ∧
    setName none name = .ok (some name) ∧ setName (some name) name = .ok (some name) ∧
    (∀ other, other ≠ name → (setName (some other) name).raises "TypeError")

theorem cachedPropertyOnce_proven : CachedPropertyOnce := by
  intro α func bad name doc mod v d d' e hd hf c
  refine ⟨⟨setAttr d' name v, ?_, setAttr_same _ _ _, ?_⟩, rfl, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, rfl, rfl, ?_, ?_, ?_,
    rfl, ?_, ?_⟩
  · simp [cachedGet, c, hd, hf]
  · simp [cachedGet, c, setAttr_same]
  · intro h
    simp [cachedGet, c, hd, h]
  · exact ⟨.typeError "~The '__dict__' attribute does not support item assignment", by
      simp [cachedGet, c, hd, hf], rfl⟩
  · simp [cachedGet, c, hd, hf]
  · simp [setName]
  · intro other h
    exact ⟨_, by simp [setName, h.symm]; rfl, rfl⟩

/-- `cached_property(func)` reads `__doc__` and `__module__` in that order, and either read failing, with
`AttributeError` too, stops the construction; a built one has no name yet. -/
def CachedPropertyInit : Prop :=
  ∀ (α : Type) (f : Attrs α → Py α × Attrs α) (read : String → Py (Option α)) (x y : α) (e : PyExc),
    (read "__doc__" = .error e → cachedNew f read = .error e) ∧
    (read "__doc__" = .ok (some x) → read "__module__" = .error e → cachedNew f read = .error e) ∧
    (read "__doc__" = .ok none → (cachedNew f read).raises "AttributeError") ∧
    (read "__doc__" = .ok (some x) → read "__module__" = .ok (some y) →
      cachedNew f read = .ok ⟨f, none, x, y⟩)

theorem cachedPropertyInit_proven : CachedPropertyInit := by
  intro α f read x y e
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; simp [cachedNew, h]
  · intro h1 h2; simp [cachedNew, h1, h2]
  · intro h; exact ⟨_, by simp [cachedNew, h]; rfl, rfl⟩
  · intro h1 h2; simp [cachedNew, h1, h2]

/-- The name in both `repr`s of `singledispatchmethod`: `__qualname__`, else `__name__`, else `'?'`, falling back
on `AttributeError` only, so any other exception from either read comes out of `repr`. All reads are universally
quantified. For the bound form, the object's own `repr` is shown only when `obj` is not `None`, and may raise. -/
def SdmRepr : Prop :=
  ∀ (read : String → Py (Option String)) (q n : String) (e : PyExc),
    (read "__qualname__" = .ok (some q) → nameOf read = .ok q) ∧
    (read "__qualname__" = .ok none → read "__name__" = .ok (some n) → nameOf read = .ok n) ∧
    (read "__qualname__" = .ok none → read "__name__" = .ok none → nameOf read = .ok "?") ∧
    (read "__qualname__" = .error e → nameOf read = .error e) ∧
    (read "__qualname__" = .ok none → read "__name__" = .error e → nameOf read = .error e)

theorem sdmRepr_proven : SdmRepr := by
  intro read q n e
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [nameOf, h]
  · intro h1 h2; simp [nameOf, h1, h2]
  · intro h1 h2; simp [nameOf, h1, h2]
  · intro h; simp [nameOf, h]
  · intro h1 h2; simp [nameOf, h1, h2]

/-- The `repr`s built on that name. -/
def SdmReprShape : Prop :=
  ∀ (α : Type) (s : Sdm α) (c o : α) (n r : String) (m d : Option String) (rep : α → Py String) (e : PyExc),
    nameOf s.func.read = .ok n →
    sdmRepr s = .ok ("<single dispatch method descriptor " ++ n ++ ">") ∧
    (let g : SdmGet α := ⟨s, none, c, m, d, 0⟩
     sdmGetRepr g rep = .ok ("<single dispatch method " ++ n ++ ">")) ∧
    (let g : SdmGet α := ⟨s, some o, c, m, d, 0⟩
     (rep o = .ok r → sdmGetRepr g rep = .ok ("<bound single dispatch method " ++ n ++ " of " ++ r ++ ">")) ∧
     (rep o = .error e → sdmGetRepr g rep = .error e))

theorem nameOf_get {α : Type} (g : SdmGet α) : nameOf (sdmGetattr g) = nameOf g.unbound.func.read := by
  simp [nameOf, sdmGetattr]

theorem sdmReprShape_proven : SdmReprShape := by
  intro α s c o n r m d rep e h
  refine ⟨by simp [sdmRepr, h], ?_, ?_, ?_⟩
  · simp [sdmGetRepr, nameOf_get, h]
  · intro h1
    simp [sdmGetRepr, nameOf_get, h, h1]
  · intro h1
    simp [sdmGetRepr, nameOf_get, h, h1]

/-- `_singledispatchmethod_get.__getattr__`: exactly the five names reach the function, and a read there may
raise anything; every other name is `AttributeError`, whatever the function holds. -/
def SdmGetattr : Prop :=
  ∀ (α : Type) (g : SdmGet α) (name : String),
    (name ∈ ["__name__", "__qualname__", "__isabstractmethod__", "__annotations__", "__type_params__"] →
      sdmGetattr g name = g.unbound.func.read name) ∧
    (name ∉ ["__name__", "__qualname__", "__isabstractmethod__", "__annotations__", "__type_params__"] →
      sdmGetattr g name = .ok none)

theorem sdmGetattr_proven : SdmGetattr := by
  intro α g name
  constructor
  · intro h; simp only [sdmGetattr, h, not_true_eq_false, ite_false]
  · intro h; simp only [sdmGetattr, h, not_false_eq_true, ite_true]

theorem singledispatch_reg {ι : Type} (o : Cls) (f : ι) (n : Py (Option String)) (d : Dispatcher ι)
    (h : singledispatch o f n = .ok d) : d.registry = [(o, f)] := by
  cases n with
  | error e => cases h
  | ok x =>
    simp only [singledispatch, Except.ok.injEq] at h
    subst h
    rfl

/-- `singledispatchmethod(func)`: rejects what is neither callable nor a descriptor, reports a failing
`__name__` read or `update_wrapper`, and otherwise registers `func` for `object`, as `singledispatch` does. -/
def SdmInit : Prop :=
  ∀ (α : Type) (object : Cls) (f : SdmFunc α) (e : PyExc),
    (f.callable = false → f.hasGet = false → (sdmNew object f).raises "TypeError") ∧
    (f.callable = true ∨ f.hasGet = true → f.read "__name__" = .error e → sdmNew object f = .error e) ∧
    (∀ s, sdmNew object f = .ok s → s.func.impl = f.impl ∧ s.dispatcher.registry.lookup object = some f.impl)

theorem sdmInit_proven : SdmInit := by
  intro α object f e
  refine ⟨?_, ?_, ?_⟩
  · intro h1 h2
    exact ⟨_, by simp [sdmNew, h1, h2]; rfl, rfl⟩
  · intro h1 h2
    have h3 : (!f.callable && !f.hasGet) = false := by
      rcases h1 with h | h <;> simp [h]
    simp [sdmNew, h3, sdmDispatcher, singledispatch, h2]
  · intro s h
    simp only [sdmNew] at h
    split at h
    · cases h
    · split at h
      · cases h
      · next d w hd =>
        simp only [sdmDispatcher] at hd
        cases hr : singledispatch object f.impl (f.read "__name__") with
        | error x =>
          rw [hr] at hd
          cases hd
        | ok d0 =>
          rw [hr] at hd
          simp only at hd
          have hreg : d0.registry = [(object, f.impl)] := singledispatch_reg _ _ _ _ hr
          split at hd
          · cases hd
          · simp only [Except.ok.injEq, Prod.mk.injEq] at hd
            obtain ⟨rfl, -⟩ := hd
            cases h
            simp [hreg, List.lookup]

/-- A call through `singledispatchmethod` runs the implementation for the class of the dispatch argument, through its
own `__get__`, if it has one: a function bound to the instance, or plain through the class; a `classmethod` bound to the
owner; a `staticmethod` with no binding; a `partial` as a method; and an object without `__get__` is called as it is,
Lib/functools.py:1096-1112. Through the class, with a plain function underneath, the dispatch argument is the second one,
:1064-1066, and a `classmethod` or a `staticmethod` implementation then drops the first argument, which it does not
expect. No positional argument is a `TypeError` naming the function, unless reading its name raises, and one positional
argument where two are needed is an `IndexError`. -/
def SdmCallBinds : Prop :=
  ∀ (α : Type) (W : World) (fuel tok : Nat) (s : Sdm α) (classOf : α → Cls) (id : Nat) (a b o c : α)
    (args : List α) (kw : List (String × α)) (m d : Option String) (e : PyExc) (f : Fn α),
    (∀ impl, s.dispatcher.cache.lookup (classOf a) = some (some impl) → s.dispatcher.token = none →
      (sdmCall W fuel tok ⟨s, some o, c, m, d, 0⟩ classOf (a :: args) kw).1 =
        implCall impl (some o) c 0 (a :: args) kw ∧
      (sdmCall W fuel tok ⟨s, none, c, m, d, 0⟩ classOf (a :: args) kw).1 =
        implCall impl none c 0 (a :: args) kw) ∧
    (∀ impl, s.dispatcher.cache.lookup (classOf b) = some (some impl) → s.dispatcher.token = none →
      (sdmCall W fuel tok ⟨s, none, c, m, d, 1⟩ classOf (a :: b :: args) kw).1 =
        implCall impl none c 1 (a :: b :: args) kw) ∧
    (sdmCall W fuel tok ⟨s, none, c, m, d, 1⟩ classOf [a] kw).1 = .error (.indexError "tuple index out of range") ∧
    implCall (.fn id) (some o) c 0 (a :: args) kw = .ok ⟨id, o :: a :: args, kw⟩ ∧
    implCall (.fn id) none c 1 (a :: args) kw = .ok ⟨id, a :: args, kw⟩ ∧
    implCall (.classm id) (some o) c 0 (a :: args) kw = .ok ⟨id, c :: a :: args, kw⟩ ∧
    implCall (.classm id) none c 1 (a :: args) kw = .ok ⟨id, c :: args, kw⟩ ∧
    implCall (.staticm id) (some o) c 0 (a :: args) kw = .ok ⟨id, a :: args, kw⟩ ∧
    implCall (.staticm id) none c 1 (a :: args) kw = .ok ⟨id, args, kw⟩ ∧
    implCall (.obj f) (some o) c 0 (a :: args) kw = callFn f (a :: args) kw ∧
    implCall (.partialObj f) (some o) c 0 (a :: args) kw = callFn f (o :: a :: args) kw ∧
    (s.func.read "__name__" = .error e →
      (sdmCall W fuel tok ⟨s, some o, c, m, d, 0⟩ classOf [] kw).1 = .error e) ∧
    (∀ n, s.func.read "__name__" = .ok n →
      (sdmCall W fuel tok ⟨s, some o, c, m, d, 0⟩ classOf [] kw).1.raises "TypeError")

theorem sdmCallBinds_proven : SdmCallBinds := by
  intro α W fuel tok s classOf id a b o c args kw m d e f
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro impl h1 h2
    simp [sdmCall, dispatch, tokenSync, h2, dispatchCached, h1]
  · intro impl h1 h2
    simp [sdmCall, dispatch, tokenSync, h2, dispatchCached, h1]
  · simp [implCall]
    cases f <;> rfl
  · intro h
    simp [sdmCall, h]
  · intro n h
    exact ⟨_, by simp [sdmCall, h]; rfl, rfl⟩

/-- `register` then a call: through `singledispatchmethod.register` and through the bound object's `register`,
the implementation of the registered class runs, whichever of the first two arguments is the dispatch argument. -/
def SdmRegisterThenCall : Prop :=
  ∀ (α : Type) (W : World) (fuel t tok : Nat) (s : Sdm α) (classOf : α → Cls) (impl : MKind α) (a b c : α)
    (args : List α) (m d : Option String),
    ∃ s', sdmRegister W t s (.val (.cls (classOf a))) (some impl) = .ok (.func impl, s') ∧
      (sdmCall W fuel tok ⟨s', none, c, m, d, 0⟩ classOf (a :: args) []).1 = implCall impl none c 0 (a :: args) [] ∧
      (sdmCall W fuel tok ⟨s', none, c, m, d, 1⟩ classOf (b :: a :: args) []).1 =
        implCall impl none c 1 (b :: a :: args) [] ∧
      sdmGetRegister W t ⟨s, none, c, m, d, 0⟩ (.val (.cls (classOf a))) (some impl) = .ok (.func impl, s')

theorem sdmRegisterThenCall_proven : SdmRegisterThenCall := by
  intro α W fuel t tok s classOf impl a b c args m d
  refine ⟨{ s with dispatcher := regStore W t s.dispatcher (.cls (classOf a)) impl }, rfl, ?_, ?_, rfl⟩
  all_goals
    have h := (registerThenDispatch_proven (MKind α) W fuel t tok s.dispatcher impl (classOf a) []).1
    simp only [sdmCall, List.getElem?_cons_zero, List.getElem?_cons_succ]
    generalize dispatch W fuel tok (regStore W t s.dispatcher (.cls (classOf a)) impl) (classOf a) = q at h ⊢
    obtain ⟨r, st⟩ := q
    simp only at h
    subst h
    rfl

/-- A callable without `__get__`, which `__init__` accepts, is usable: it is called with the arguments as they are.
This is what python/cpython#143535 changed: Lib/functools.py:1096-1112 calls the method even when it has no `__get__`. -/
def SdmCallableUsable : Prop :=
  ∀ (id o : Nat),
    let f : SdmFunc Nat := ⟨true, false, fun _ => .ok none, fun _ => .ok none, .ok none, .obj (.base id), false⟩
    (sdmCall world0 4 0 ⟨⟨newDispatcher 0 f.impl, f, { dict := [("__wrapped__", "<func>")] }⟩, some o, 0, none, none,
      0⟩ (fun _ => 0) [o] []).1 = .ok ⟨id, [o], []⟩

theorem sdmCallableUsable_proven : SdmCallableUsable := by
  intro id o
  rfl

/-- `_singledispatchmethod_get.__init__` reads `__module__` and `__doc__`, and skips only `AttributeError`. -/
def SdmGetReads : Prop :=
  ∀ (α : Type) (s : Sdm α) (obj : Option α) (c : α) (m d : Option String) (e : PyExc),
    (s.func.read "__module__" = .error e → sdmGet s obj c = .error e) ∧
    (s.func.read "__module__" = .ok m → s.func.read "__doc__" = .error e → sdmGet s obj c = .error e) ∧
    (s.func.read "__module__" = .ok m → s.func.read "__doc__" = .ok d →
      sdmGet s obj c = .ok ⟨s, obj, c, m, d, dispatchIndex s obj⟩) ∧
    (dispatchIndex s obj = if obj.isNone && s.func.isFunction then 1 else 0)

theorem sdmGetReads_proven : SdmGetReads := by
  intro α s obj c m d e
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; simp [sdmGet, h]
  · intro h1 h2; simp [sdmGet, h1, h2]
  · intro h1 h2; simp [sdmGet, h1, h2]
  · cases obj <;> simp [dispatchIndex]

end PyLean.CoreLibs.Functools
