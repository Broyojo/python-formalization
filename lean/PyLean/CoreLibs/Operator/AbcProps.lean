import PyLean.CoreLibs.Operator.Abc

/-!
Properties of `abc` and `_abc`.
-/

namespace PyLean.CoreLibs.Operator

open PyLean

theorem put_get (s : AbcState) (c : Nat) (d : AbcData) : (s.put c d).get c = d := by
  simp [AbcState.put, AbcState.get, List.lookup]

theorem addCache_mem (s : AbcState) (c sub : Nat) : sub ∈ ((addCache s c sub).get c).cache := by
  simp [addCache, put_get]

/-- `issubclass(sub, cls)` on an ABC, in the order of Modules/_abc.c:717-854: the positive cache answers true with
no hook, whatever the world says now; a valid negative cache answers false with no hook; then
`__subclasshook__`, whose exception propagates with no cache written, whose `True` and `False` are final and
cached, and whose other results are an `AssertionError`; then a real subclass. -/
def AbcCheckOrder : Prop :=
  ∀ (W : AbcWorld) (fuel cls sub : Nat) (s : AbcState) (e : PyExc),
    (sub ∈ (s.get cls).cache → subCheck W (fuel + 1) cls sub s = (.ok true, s)) ∧
    (sub ∉ (s.get cls).cache → s.counter ≤ (s.get cls).version → sub ∈ (s.get cls).neg →
      subCheck W (fuel + 1) cls sub s = (.ok false, s)) ∧
    (sub ∉ (s.get cls).cache → s.counter ≤ (s.get cls).version → sub ∉ (s.get cls).neg →
      ((W.hook cls sub = .error e → subCheck W (fuel + 1) cls sub s = (.error e, s)) ∧
       (W.hook cls sub = .ok .tru → subCheck W (fuel + 1) cls sub s = (.ok true, addCache s cls sub)) ∧
       (W.hook cls sub = .ok .fals → subCheck W (fuel + 1) cls sub s = (.ok false, addNeg s cls sub)) ∧
       (W.hook cls sub = .ok .other → (subCheck W (fuel + 1) cls sub s).1.raises "AssertionError") ∧
       (W.hook cls sub = .ok .notImplemented → cls ∈ W.mro sub →
         subCheck W (fuel + 1) cls sub s = (.ok true, addCache s cls sub))))

theorem abcCheckOrder_proven : AbcCheckOrder := by
  intro W fuel cls sub s e
  refine ⟨?_, ?_, ?_⟩
  · intro h
    simp [subCheck, h]
  · intro h1 h2 h3
    have h4 : ¬ (s.get cls).version < s.counter := by omega
    simp [subCheck, h1, h3, h4]
  · intro h1 h2 h3
    have h4 : ¬ (s.get cls).version < s.counter := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro h; simp [subCheck, h1, h3, h4, h]
    · intro h; simp [subCheck, h1, h3, h4, h]
    · intro h; simp [subCheck, h1, h3, h4, h]
    · intro h
      exact ⟨_, by simp [subCheck, h1, h3, h4, h]; rfl, rfl⟩
    · intro h h5; simp [subCheck, h1, h3, h4, h, h5]

/-- `ABC.register` invalidates the negative caches: after a check said no and cached it, registering makes the
same check say yes, for a hook with no opinion. The counter is what does it, because the negative cache of
`cls` is only trusted at the current counter, and the fast path of the registry answers. -/
def AbcRegisterInvalidates : Prop :=
  ∀ (W : AbcWorld) (fuel cls sub : Nat) (s : AbcState),
    W.hook cls sub = .ok .notImplemented → cls ∉ W.mro sub → sub ∉ (s.get cls).cache →
    (s.get cls).version ≤ s.counter →
    let d := s.get cls
    let t : AbcState := { s.put cls { d with registry := sub :: d.registry } with counter := s.counter + 1 }
    (subCheck W (fuel + 1) cls sub t).1 = .ok true

theorem abcRegisterInvalidates_proven : AbcRegisterInvalidates := by
  intro W fuel cls sub s h1 h2 h3 h4 d t
  have g : t.get cls = { d with registry := sub :: d.registry } := by
    simp [t, AbcState.put, AbcState.get, List.lookup]
  have hc : sub ∉ (t.get cls).cache := by
    rw [g]
    exact h3
  have hv : (t.get cls).version < t.counter := by
    rw [g]
    show (s.get cls).version < s.counter + 1
    omega
  simp only [subCheck, hc, ite_false, hv, ite_true, h1, h2]
  have g2 : ∀ x : AbcData, ((t.put cls x).get cls) = x := put_get t cls
  simp [g2, g]

/-- A check that a hook answered with yes answers yes again without running anything, whatever the world and its
hook say by then: the positive cache is never cleared. -/
def AbcSecondCheck : Prop :=
  ∀ (W W' : AbcWorld) (fuel cls sub : Nat) (s : AbcState),
    s.counter ≤ (s.get cls).version → sub ∉ (s.get cls).neg → W.hook cls sub = .ok .tru →
    sub ∉ (s.get cls).cache →
    (subCheck W' (fuel + 1) cls sub (subCheck W (fuel + 1) cls sub s).2).1 = .ok true

theorem abcSecondCheck_proven : AbcSecondCheck := by
  intro W W' fuel cls sub s h1 h2 h3 h4
  have h5 : ¬ (s.get cls).version < s.counter := by omega
  have e : subCheck W (fuel + 1) cls sub s = (.ok true, addCache s cls sub) := by
    simp [subCheck, h2, h4, h5, h3]
  rw [e]
  simp [subCheck, addCache_mem]

/-- `register`: a non-class is a `TypeError`; an existing subclass changes nothing; a cycle is a `RuntimeError`,
tested after that, so that `X.register(X)` is allowed. A new registration bumps the counter, records the class and
returns it, for use as a class decorator. -/
def AbcRegister : Prop :=
  ∀ (W : AbcWorld) (fuel cls c : Nat) (s : AbcState),
    (register W fuel cls none s).1.raises "TypeError" ∧
    (W.isAbc cls = false → cls ∈ W.mro c → register W fuel cls (some c) s = (.ok c, s)) ∧
    (W.isAbc cls = false → W.isAbc c = false → cls ∉ W.mro c → c ∈ W.mro cls →
      (register W fuel cls (some c) s).1.raises "RuntimeError") ∧
    (W.isAbc cls = false → W.isAbc c = false → cls ∉ W.mro c → c ∉ W.mro cls →
      (register W fuel cls (some c) s).1 = .ok c ∧
      (register W fuel cls (some c) s).2.counter = s.counter + 1 ∧
      c ∈ ((register W fuel cls (some c) s).2.get cls).registry)

theorem abcRegister_proven : AbcRegister := by
  intro W fuel cls c s
  refine ⟨⟨_, rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro h1 h2
    simp [register, isSubclass, h1, h2]
  · intro h1 h2 h3 h4
    exact ⟨_, by simp [register, isSubclass, h1, h2, h3, h4]; rfl, rfl⟩
  · intro h1 h2 h3 h4
    have e : register W fuel cls (some c) s =
        (.ok c, { s.put cls { s.get cls with registry := c :: (s.get cls).registry } with
          counter := s.counter + 1 }) := by
      simp [register, isSubclass, h1, h2, h3, h4]
    rw [e]
    refine ⟨rfl, rfl, ?_⟩
    simp [AbcState.put, AbcState.get, List.lookup]

/-- `isinstance(obj, cls)`: an `__class__` that raises propagates, unless it is an `AttributeError`, which means the object's
type; the positive cache answers; for an object whose `__class__` is its type, the valid negative cache answers, else
`__subclasscheck__`; for an object that lies, its `__class__` is checked first and then its real type. -/
def AbcInstanceCheck : Prop :=
  ∀ (W : AbcWorld) (fuel cls k t : Nat) (s : AbcState) (e : PyExc),
    (isAttributeError e = false → instanceCheck W fuel cls (.error e) t s = (.error e, s)) ∧
    (isAttributeError e = true → instanceCheck W fuel cls (.error e) t s = instanceCheck W fuel cls (.ok t) t s) ∧
    (k ∈ (s.get cls).cache → instanceCheck W fuel cls (.ok k) t s = (.ok true, s)) ∧
    (k ∉ (s.get cls).cache → instanceCheck W fuel cls (.ok k) k s =
      if (s.get cls).version = s.counter ∧ k ∈ (s.get cls).neg then (.ok false, s)
      else subCheck W fuel cls k s) ∧
    (k ∉ (s.get cls).cache → t ≠ k → (subCheck W fuel cls k s).1 = .ok false →
      instanceCheck W fuel cls (.ok k) t s = subCheck W fuel cls t (subCheck W fuel cls k s).2)

theorem abcInstanceCheck_proven : AbcInstanceCheck := by
  intro W fuel cls k t s e
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [instanceCheck, classRead, h]
  · intro h; simp [instanceCheck, classRead, h]
  · intro h; simp [instanceCheck, classRead, h]
  · intro h; simp [instanceCheck, classRead, h]
  · intro h1 h2 h3
    simp only [instanceCheck, classRead, h1, ite_false, h2]
    generalize subCheck W fuel cls k s = r at h3
    obtain ⟨a, b⟩ := r
    simp only at h3
    subst h3
    rfl

/-- `ABCMeta.__new__`, through `compute_abstract_methods`, and `update_abstractmethods` find the same names on the
same class: the first scans the class and then the bases, and the second the other way round. A failure of the
`__isabstractmethod__` test propagates from both, and a class that is not an ABC is left alone. -/
def AbstractTwins : Prop :=
  ∀ (c : AbsClass) (a b : List String) (e : PyExc),
    (absScan Prod.fst Prod.snd c.own = .ok a → inheritedScan c c.parents = .ok b →
      computeAbstract c = .ok (a ++ b) ∧ updateAbstract true c = .ok (some (b ++ a))) ∧
    (absScan Prod.fst Prod.snd c.own = .error e → computeAbstract c = .error e) ∧
    (inheritedScan c c.parents = .error e → updateAbstract true c = .error e) ∧
    updateAbstract false c = .ok none

theorem abstractTwins_proven : AbstractTwins := by
  intro c a b e
  refine ⟨?_, ?_, ?_, rfl⟩
  · intro h1 h2
    exact ⟨by simp [computeAbstract, h1, h2], by simp [updateAbstract, h1, h2]⟩
  · intro h; simp [computeAbstract, h]
  · intro h; simp [updateAbstract, h]

/-- A name inherited from a base stays abstract only if it still is on the class, and a base's name that the class
has no attribute for is dropped: an implemented method is not abstract. Docs of `update_abstractmethods`. -/
def AbstractInherited : Prop :=
  ∀ (c : AbsClass) (n : String),
    (c.lookup n = some (.ok false) → inheritedScan c [[n]] = .ok []) ∧
    (c.lookup n = none → inheritedScan c [[n]] = .ok []) ∧
    (c.lookup n = some (.ok true) → inheritedScan c [[n]] = .ok [n])

theorem abstractInherited_proven : AbstractInherited := by
  intro c n
  refine ⟨?_, ?_, ?_⟩
  · intro h; simp [inheritedScan, absScan, h]
  · intro h; simp [inheritedScan, absScan, h]
  · intro h; simp [inheritedScan, absScan, h]

end PyLean.CoreLibs.Operator
