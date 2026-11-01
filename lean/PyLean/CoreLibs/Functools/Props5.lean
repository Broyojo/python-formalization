import PyLean.CoreLibs.Functools.Props4

/-!
Properties of `functools`, part five: wrappers and descriptors.
-/

namespace PyLean.CoreLibs.Functools

open PyLean

theorem setAttr_same {α : Type} (o : Attrs α) (k : String) (v : α) :
    (setAttr o k v).lookup k = some v := by
  induction o with
  | nil => simp [setAttr, List.lookup]
  | cons p ps ih =>
    by_cases e : p.1 = k
    · simpa [setAttr, List.filter_cons, e] using ih
    · have e2 : (k == p.1) = false := by
        have : k ≠ p.1 := fun x => e x.symm
        simpa using this
      simpa [setAttr, List.filter_cons, e, List.lookup, e2] using ih

theorem setAttr_other {α : Type} (o : Attrs α) (k j : String) (v : α) (h : j ≠ k) :
    (setAttr o k v).lookup j = o.lookup j := by
  have e0 : (j == k) = false := by simpa using h
  induction o with
  | nil => simp [setAttr, List.lookup, e0]
  | cons p ps ih =>
    by_cases e : p.1 = k
    · have e2 : (j == p.1) = false := by rw [e]; exact e0
      simpa [setAttr, List.filter_cons, e, List.lookup, e0] using ih
    · simp only [setAttr] at ih ⊢
      rw [List.filter_cons_of_pos (by simpa using e)]
      by_cases e3 : j = p.1
      · subst e3
        simp [List.lookup]
      · have e4 : (j == p.1) = false := by simpa using e3
        simp only [List.cons_append, List.lookup, e4]
        exact ih

theorem assign_lookup {α : Type} (wrapped : Attrs α) (k : String) (v : α)
    (hv : wrapped.lookup k = some v) : ∀ (assigned : List String) (w : Attrs α),
    (k ∈ assigned ∨ w.lookup k = some v) →
    (assigned.foldl (fun acc a =>
      match wrapped.lookup a with
      | some x => setAttr acc a x
      | none => acc) w).lookup k = some v
  | [], _, h => by simpa using h
  | a :: as, w, h => by
    simp only [List.foldl_cons]
    apply assign_lookup wrapped k v hv as
    by_cases e : k = a
    · subst e
      right
      simp only [hv, setAttr_same]
    · rcases h with h | h
      · rcases List.mem_cons.mp h with h | h
        · exact absurd h e
        · exact Or.inl h
      · right
        cases hl : wrapped.lookup a with
        | none => simpa [hl] using h
        | some x => simpa [hl, setAttr_other w a k x e] using h

/-- `update_wrapper(wrapper, wrapped)` and `wraps` copy every listed attribute that `wrapped` has,
and set `__wrapped__` to `wrapped` last, so a copied `__dict__` cannot override it. Docstring and
gh-issue 17482 at Lib/functools.py:59. Quantified over any attribute table; `k` differs from
`__wrapped__`, which is set separately. -/
def UpdateWrapperCopies : Prop :=
  ∀ (α : Type) (wrapper wrapped wd wdd : Attrs α) (assigned : List String) (self v : α) (k : String),
    k ∈ assigned → k ≠ "__wrapped__" → wrapped.lookup k = some v →
    (updateWrapper wrapper wrapped wd wdd assigned self).1.lookup k = some v ∧
    (updateWrapper wrapper wrapped wd wdd assigned self).1.lookup "__wrapped__" = some self

theorem updateWrapperCopies_proven : UpdateWrapperCopies := by
  intro α wrapper wrapped wd wdd assigned self v k hk hne hv
  simp only [updateWrapper]
  refine ⟨?_, setAttr_same _ _ _⟩
  rw [setAttr_other _ _ _ _ hne]
  exact assign_lookup wrapped k v hv assigned wrapper (Or.inl hk)

/-- `cached_property`: the first read computes and stores under the attribute name, and a later read
returns that value without calling the function again, even if it would now raise. Without
`__set_name__`, or without an instance `__dict__`, a read raises `TypeError`. `__set_name__` accepts the
same name twice and rejects a second name. Docs of `cached_property`. -/
def CachedPropertyOnce : Prop :=
  ∀ (α : Type) (func bad : Py α) (name : String) (d : Attrs α) (v : α),
    d.lookup name = none → func = .ok v →
    (∃ d', cachedGet func (some name) (some d) false = .ok (v, d') ∧
      cachedGet bad (some name) (some d') false = .ok (v, d')) ∧
    (cachedGet func none (some d) false).raises "TypeError" ∧
    (cachedGet func (some name) none false).raises "TypeError" ∧
    setName none name = .ok (some name) ∧ setName (some name) name = .ok (some name) ∧
    (∀ other, other ≠ name → (setName (some other) name).raises "TypeError")

theorem cachedPropertyOnce_proven : CachedPropertyOnce := by
  intro α func bad name d v hd hf
  refine ⟨⟨setAttr d name v, ?_, ?_⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, rfl, ?_, ?_⟩
  · simp [cachedGet, hd, hf, bind, Except.bind, pure, Except.pure]
  · simp [cachedGet, setAttr_same]
  · simp [setName]
  · intro other h
    exact ⟨_, by simp [setName, h.symm]; rfl, rfl⟩

/-- The descriptors of `partial` and of the `lru_cache` wrapper: access on the class gives the object,
access on an instance prepends the instance to the arguments. The `lru_cache` wrapper is its own
copy and deep copy and pickles by qualified name, and `K` reports the signature `(obj)`. -/
def DescriptorsBindInstance : Prop :=
  ∀ (α : Type) (o : α) (args : List α) (q : String),
    descrGet none args = args ∧ descrGet (some o) args = o :: args ∧ lruCopy o = o ∧
    lruReduce q = q ∧ keyTextSignature = "(obj)"

theorem descriptorsBindInstance_proven : DescriptorsBindInstance :=
  fun _ _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `singledispatchmethod`: construction rejects what is neither callable nor a descriptor; its reprs
use `__qualname__`, then `__name__`, then `?`; the lazy attributes are the five listed, and calling
without a positional argument raises `TypeError`. `__isabstractmethod__` defaults to `False`. -/
def SingledispatchmethodSurface : Prop :=
  sdmInit false false = .error (.typeError "~is not callable or a descriptor") ∧
  (∀ c g : Bool, (c = true ∨ g = true) → sdmInit c g = .ok ()) ∧
  (∀ (q : String) (n : Option String),
    sdmRepr (some q) n = s!"<single dispatch method descriptor {q}>") ∧
  (∀ n : String, sdmRepr none (some n) = s!"<single dispatch method descriptor {n}>") ∧
  sdmRepr none none = "<single dispatch method descriptor ?>" ∧
  (∀ (q o : String) (n : Option String),
    sdmGetRepr (some q) n (some o) = s!"<bound single dispatch method {q} of {o}>") ∧
  (∀ (q : String) (n : Option String),
    sdmGetRepr (some q) n none = s!"<single dispatch method {q}>") ∧
  (sdmGetattrAllowed "__name__" = true ∧ sdmGetattrAllowed "__wrapped__" = false) ∧
  (∀ (W : World) (fuel tok : Nat) (name : String) (d : Dispatcher Nat),
    (dispatchCall W fuel tok name d none).1.raises "TypeError")

theorem singledispatchmethodSurface_proven : SingledispatchmethodSurface := by
  refine ⟨rfl, ?_, ?_, ?_, rfl, ?_, ?_, ⟨by simp [sdmGetattrAllowed], by simp [sdmGetattrAllowed]⟩, ?_⟩
  · intro c g h
    rcases h with h | h <;> simp [sdmInit, h]
  · intro q n; simp [sdmRepr]
  · intro n; simp [sdmRepr]
  · intro q o n; simp [sdmGetRepr]
  · intro q n; simp [sdmGetRepr]
  · intro W fuel tok name d
    exact ⟨_, rfl, rfl⟩

/-- The pure-Python `reduce` warns exactly when `function` or `sequence` is a keyword. -/
def ReduceWarnsOnDeprecatedKeywords : Prop :=
  ∀ names : List String,
    reduceWarns names = true ↔ ("function" ∈ names ∨ "sequence" ∈ names)

theorem reduceWarnsOnDeprecatedKeywords_proven : ReduceWarnsOnDeprecatedKeywords := by
  intro names
  simp [reduceWarns]

/-- `repr(partial)` shows the function, the positional arguments, then the keywords, in that order,
in the two twins' shared format. Twin property of `_partial_repr` and `partial_repr`. -/
def PartialReprOrder : Prop :=
  ∀ (cls func : String) (args : List String) (k v : String),
    partialRepr cls func args [(k, v)] =
      s!"{cls}({", ".intercalate (func :: (args ++ [s!"{k}={v}"]))})"

theorem partialReprOrder_proven : PartialReprOrder := by
  intro cls func args k v
  simp [partialRepr]

/-- The recency list of a key sequence: a used key moves to the end. -/
def recencyOf {K : Type} [DecidableEq K] (ks : List K) : List K :=
  ks.foldl (fun l k => l.filter (· ≠ k) ++ [k]) []

/-- After any sequence of calls of a function that never raises, the bounded cache holds exactly the
`maxsize` most recently used keys, oldest first. The "least recently used" of the name. -/
def LruRecency : Prop :=
  ∀ (K V : Type) [DecidableEq K] (m : Nat) (f : K → Py V) (ks : List K), 0 < m →
    (∀ k, ∃ v, f k = .ok v) →
    (runC m f emptyC (ks.map LruOp.call)).2.links.map Prod.fst =
      (recencyOf ks).drop ((recencyOf ks).length - m)

end PyLean.CoreLibs.Functools
