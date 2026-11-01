import PyLean.CoreLibs.Operator.AbcProps

/-!
The rest of `_abc__abc_subclasscheck_impl`, and what the abstract-method scans compute. `AbcCheckOrder` stops at the
direct-subclass step, and `AbstractTwins` is stated over the scans' results, which an always-raising scan satisfies.
-/

namespace PyLean.CoreLibs.Operator

open PyLean

/-- Steps 5 and 6 of the check, for a hook that does not answer and a class that is not a direct subclass. `sub` in
the registry is true and is not cached, as the fast path of `subclasscheck_check_registry` is written. A registered
class or a subclass that `sub` derives from is true and cached. An exception from a registered ABC is final. When
neither step answers, the result is false and it goes in the negative cache. -/
def AbcFallthrough : Prop :=
  ∀ (W : AbcWorld) (fuel cls sub r c : Nat) (rest : List Nat) (s t : AbcState) (e : PyExc),
    sub ∉ (s.get cls).cache → s.counter ≤ (s.get cls).version → sub ∉ (s.get cls).neg →
    W.hook cls sub = .ok .notImplemented → cls ∉ W.mro sub →
    (sub ∈ (s.get cls).registry → subCheck W (fuel + 1) cls sub s = (.ok true, s)) ∧
    (sub ∉ (s.get cls).registry → (s.get cls).registry = [] → W.subclasses cls = [] →
      subCheck W (fuel + 2) cls sub s = (.ok false, addNeg s cls sub)) ∧
    (sub ∉ (s.get cls).registry → (s.get cls).registry = r :: rest → W.isAbc r = false → r ∈ W.mro sub →
      subCheck W (fuel + 2) cls sub s = (.ok true, addCache s cls sub)) ∧
    (sub ∉ (s.get cls).registry → (s.get cls).registry = r :: rest → W.isAbc r = true →
      subCheck W fuel r sub s = (.error e, t) → subCheck W (fuel + 2) cls sub s = (.error e, t)) ∧
    (sub ∉ (s.get cls).registry → (s.get cls).registry = [] → W.subclasses cls = c :: rest → W.isAbc c = false →
      c ∈ W.mro sub → subCheck W (fuel + 2) cls sub s = (.ok true, addCache s cls sub))

theorem abcFallthrough_proven : AbcFallthrough := by
  intro W fuel cls sub r c rest s t e h1 h2 h3 h4 h5
  have hv : ¬ (s.get cls).version < s.counter := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h6
    rw [subCheck]
    simp [h1, hv, h3, h4, h5, h6]
  · intro h6 h7 h8
    rw [subCheck]
    simp [h1, hv, h3, h4, h5, h6, h7, h8, anySub]
  · intro h6 h7 h8 h9
    have ⟨n1, n2⟩ : ¬ sub = r ∧ sub ∉ rest := by
      rw [h7] at h6
      simpa using h6
    rw [subCheck]
    simp [h1, hv, h3, h4, h5, n1, n2, h7, h8, h9, anySub]
  · intro h6 h7 h8 h9
    have ⟨n1, n2⟩ : ¬ sub = r ∧ sub ∉ rest := by
      rw [h7] at h6
      simpa using h6
    rw [subCheck]
    simp [h1, hv, h3, h4, h5, n1, n2, h7, h8, h9, anySub]
  · intro h6 h7 h8 h9 h10
    rw [subCheck]
    simp [h1, hv, h3, h4, h5, h6, h7, h8, h9, h10, anySub]

/-- A stale negative cache: when the class's version is behind the counter, the cache is emptied and the version
caught up, whatever happens next, and the hook runs even for a class that was in the negative cache. -/
def AbcInvalidation : Prop :=
  ∀ (W : AbcWorld) (fuel cls sub : Nat) (s : AbcState) (e : PyExc),
    sub ∉ (s.get cls).cache → (s.get cls).version < s.counter →
    let t := s.put cls { s.get cls with neg := [], version := s.counter }
    (W.hook cls sub = .ok .fals → subCheck W (fuel + 1) cls sub s = (.ok false, addNeg t cls sub)) ∧
    (W.hook cls sub = .ok .tru → subCheck W (fuel + 1) cls sub s = (.ok true, addCache t cls sub)) ∧
    (W.hook cls sub = .error e → subCheck W (fuel + 1) cls sub s = (.error e, t))

theorem abcInvalidation_proven : AbcInvalidation := by
  intro W fuel cls sub s e h1 h2
  refine ⟨?_, ?_, ?_⟩
  · intro h3; rw [subCheck]; simp [h1, h2, h3]
  · intro h3; rw [subCheck]; simp [h1, h2, h3]
  · intro h3; rw [subCheck]; simp [h1, h2, h3]

/-- `absScan`: the names whose test is true, in order, and the first raising test stops it. -/
def AbsScanExact : Prop :=
  ∀ (β : Type) (name : β → String) (test : β → IsAbs) (p : β → Bool) (l pre post : List β) (z : β) (e : PyExc),
    ((∀ x ∈ l, test x = .ok (p x)) → absScan name test l = .ok ((l.filter p).map name)) ∧
    ((∀ x ∈ pre, ∃ b, test x = .ok b) → test z = .error e → absScan name test (pre ++ z :: post) = .error e)

theorem absScan_all {β : Type} (name : β → String) (test : β → IsAbs) (p : β → Bool) : ∀ l : List β,
    (∀ x ∈ l, test x = .ok (p x)) → absScan name test l = .ok ((l.filter p).map name)
  | [], _ => rfl
  | x :: xs, h => by
    have hx := h x (by simp)
    have ih := absScan_all name test p xs (fun y hy => h y (by simp [hy]))
    simp only [absScan, hx, ih]
    cases hp : p x <;> simp [hp]

theorem absScan_stop {β : Type} (name : β → String) (test : β → IsAbs) (z : β) (post : List β) (e : PyExc)
    (hz : test z = .error e) : ∀ pre : List β, (∀ x ∈ pre, ∃ b, test x = .ok b) →
    absScan name test (pre ++ z :: post) = .error e
  | [], _ => by simp [absScan, hz]
  | x :: xs, h => by
    obtain ⟨b, hb⟩ := h x (by simp)
    simp [absScan, hb, absScan_stop name test z post e hz xs (fun y hy => h y (by simp [hy]))]

theorem absScanExact_proven : AbsScanExact := fun _ name test p l pre post z e =>
  ⟨absScan_all name test p l, fun h1 h2 => absScan_stop name test z post e h2 pre h1⟩

/-- What stays abstract, for any number of bases. A name a base lists stays abstract exactly when the class's own
attribute of that name is abstract, and a missing attribute counts as not abstract. So the result of a class is its
abstract own items and the inherited names that nothing overrode, for `ABCMeta.__new__` and for
`update_abstractmethods`, which `update_abstractmethods` lists in the other order. -/
def AbstractExact : Prop :=
  ∀ (c : AbsClass) (p : String × IsAbs → Bool) (q : String → Bool),
    (∀ x ∈ c.own, x.2 = .ok (p x)) →
    (∀ names ∈ c.parents, ∀ n ∈ names, (c.lookup n).getD (.ok false) = .ok (q n)) →
    computeAbstract c = .ok ((c.own.filter p).map Prod.fst ++ c.parents.flatMap (·.filter q)) ∧
    updateAbstract true c = .ok (some (c.parents.flatMap (·.filter q) ++ (c.own.filter p).map Prod.fst))

theorem inherited_all (c : AbsClass) (q : String → Bool) : ∀ ps : List (List String),
    (∀ names ∈ ps, ∀ n ∈ names, (c.lookup n).getD (.ok false) = .ok (q n)) →
    inheritedScan c ps = .ok (ps.flatMap (·.filter q))
  | [], _ => rfl
  | names :: rest, h => by
    have h1 := absScan_all id (fun n => (c.lookup n).getD (.ok false)) q names (h names (by simp))
    have h2 := inherited_all c q rest (fun m hm => h m (by simp [hm]))
    simp [inheritedScan, h1, h2]

theorem abstractExact_proven : AbstractExact := by
  intro c p q h1 h2
  have ha := absScan_all Prod.fst Prod.snd p c.own h1
  have hb := inherited_all c q c.parents h2
  simp [computeAbstract, updateAbstract, ha, hb]

end PyLean.CoreLibs.Operator
