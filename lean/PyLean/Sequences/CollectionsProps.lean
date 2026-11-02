import PyLean.Sequences.DefaultDict

/-!
Properties of `defaultdict`, `_count_elements` and `_tuplegetter`. Keys are compared with
decidable equality, the "same hash and `==`" of `DefaultDict.lean`: `__hash__` and `__eq__`
of the keys are pure and consistent.
-/

namespace PyLean.Sequences

open PyLean

set_option linter.unusedSectionVars false

section Dict

variable {κ ν : Type} [DecidableEq κ]

theorem dictGet_set_same (d : PyDict κ ν) (k : κ) (v : ν) : dictGet (dictSet d k v) k = some v := by
  induction d with
  | nil => simp [dictSet, dictGet, List.lookup]
  | cons kv rest ih =>
    obtain ⟨k', v'⟩ := kv
    simp only [dictSet]
    split
    · simp [dictGet, List.lookup]
    · rename_i h
      simp only [dictGet, List.lookup] at ih ⊢
      have : (k == k') = false := by simp; exact fun e => h e.symm
      simp only [this]
      exact ih

theorem dictGet_set_other (d : PyDict κ ν) (k j : κ) (v : ν) (h : j ≠ k) :
    dictGet (dictSet d k v) j = dictGet d j := by
  induction d with
  | nil =>
    have : (j == k) = false := by simpa using h
    simp [dictSet, dictGet, List.lookup, this]
  | cons kv rest ih =>
    obtain ⟨k', v'⟩ := kv
    simp only [dictSet]
    split
    · rename_i e
      subst e
      have : (j == k') = false := by simpa using h
      simp [dictGet, List.lookup, this]
    · simp only [dictGet, List.lookup] at ih ⊢
      cases (j == k') <;> simp only [ih]

theorem dictSet_new (d : PyDict κ ν) (k : κ) (v : ν) (h : k ∉ d.map Prod.fst) :
    dictSet d k v = d ++ [(k, v)] := by
  induction d with
  | nil => rfl
  | cons kv rest ih =>
    obtain ⟨k', v'⟩ := kv
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [dictSet, List.cons_append]
    rw [iteF (fun e => h.1 e.symm), ih h.2]

theorem dictUpdate_fresh (pre l : PyDict κ ν) (h : ((pre ++ l).map Prod.fst).Nodup) :
    dictUpdate pre l = pre ++ l := by
  induction l generalizing pre with
  | nil => simp [dictUpdate]
  | cons kv l ih =>
    have hk : kv.1 ∉ pre.map Prod.fst := by
      intro hm
      rw [List.map_append, List.nodup_append] at h
      exact (h.2.2 _ hm kv.1 (by simp)) rfl
    have e : dictUpdate pre (kv :: l) = dictUpdate (dictSet pre kv.1 kv.2) l := rfl
    rw [e, dictSet_new _ _ _ hk, ih _ (by simpa using h)]
    simp

/-- `dd[key]`, for every defaultdict, every key and every factory (`__missing__`,
`defdict_missing`): a present key gives its value and changes nothing. A missing key
raises `KeyError(key)` without a factory, and leaves the dict as the factory left it when
the factory raises. Otherwise the factory's value is stored and returned, unless the
factory itself stored the key: then that value stays and is returned
(`PyDict_SetDefaultRef`). -/
def DefDictGetitem : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (dd : DefDict κ ν) (keyRepr : κ → String) (key : κ),
    (∀ v, dictGet dd.items key = some v → dd.getitem keyRepr key = (.ok v, dd)) ∧
    (dictGet dd.items key = none →
      ((∀ r run, dd.factory ≠ .call r run) →
        dd.getitem keyRepr key = (.error (.keyError (keyRepr key)), dd)) ∧
      ∀ r run, dd.factory = .call r run →
        (∀ e items, run dd.items = (.error e, items) →
          dd.getitem keyRepr key = (.error e, { dd with items })) ∧
        (∀ v items, run dd.items = (.ok v, items) →
          (∀ old, dictGet items key = some old →
            dd.getitem keyRepr key = (.ok old, { dd with items })) ∧
          (dictGet items key = none →
            ∃ dd', dd.getitem keyRepr key = (.ok v, dd') ∧ dictGet dd'.items key = some v ∧
              ∀ j, j ≠ key → dictGet dd'.items j = dictGet items j)))

theorem defDictGetitem_proven : DefDictGetitem := by
  intro κ ν _ dd keyRepr key
  refine ⟨fun v h => ?_, fun h => ⟨fun hn => ?_, fun r run hf => ⟨fun e items he => ?_, fun v items hv => ⟨fun old ho => ?_, fun hno => ?_⟩⟩⟩⟩
  · simp only [DefDict.getitem, h]
  · simp only [DefDict.getitem, h, DefDict.missing]
    cases hc : dd.factory with
    | null => rfl
    | none => rfl
    | call r run => exact absurd hc (hn r run)
  · simp only [DefDict.getitem, h, DefDict.missing, hf, he]
  · simp only [DefDict.getitem, h, DefDict.missing, hf, hv, ho]
  · refine ⟨{ dd with items := dictSet items key v }, ?_, dictGet_set_same _ _ _, fun j hj => dictGet_set_other _ _ _ _ hj⟩
    simp only [DefDict.getitem, h, DefDict.missing, hf, hv, hno]

/-- `dd.copy()` and `copy.copy(dd)`, for every defaultdict (type invariant: its keys are
distinct): same items in the same order, same type, same factory, a `NULL` factory
becoming `None`. `dd.__reduce__()` gives the items, and the factory exactly when it is
callable. -/
def DefDictCopyReduce : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (dd : DefDict κ ν), (dd.items.map Prod.fst).Nodup →
    dd.copy.items = dd.items ∧ dd.copy.tname = dd.tname ∧
    (∀ r run, dd.factory = .call r run → dd.copy.factory = .call r run) ∧
    ((∀ r run, dd.factory ≠ .call r run) → dd.copy.reduce.1 = none) ∧
    dd.reduce.2 = dd.items ∧
    (∀ r run, dd.factory = .call r run → dd.reduce.1 = some r)

theorem defDictCopyReduce_proven : DefDictCopyReduce := by
  intro κ ν _ dd hn
  refine ⟨?_, rfl, fun r run hf => ?_, fun hc => ?_, ?_, fun r run hf => ?_⟩
  · simp only [DefDict.copy, DefDict.newFrom]
    rw [dictUpdate_fresh [] _ (by simpa using hn)]
    simp
  · simp only [DefDict.copy, DefDict.newFrom, hf]
  · simp only [DefDict.copy, DefDict.newFrom, DefDict.reduce]
    cases hf : dd.factory with
    | null => rfl
    | none => rfl
    | call r run => exact absurd hf (hc r run)
  · simp only [DefDict.reduce]
    split <;> rfl
  · simp only [DefDict.reduce, hf]

/-- `repr(dd)` is `type(factory repr, dict repr)`, with `None` for no factory and `...` while
the factory is being printed. `dd.__init__`: a first argument that is neither callable nor
`None` raises `TypeError` and changes nothing; otherwise the factory is replaced before
`dict.__init__` runs, so it stays replaced when that raises. `left | right` for two
dict operands has the items of `left` updated by `right`, and the type and factory of the
defaultdict operand (the left one if both are); a `frozendict` operand counts as a dict
since 3.15, and anything else gives `NotImplemented`. -/
def DefDictReprInitOr : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (dd : DefDict κ ν) (base : PyDict κ ν → String),
    (∀ r run, dd.factory = .call r run →
      dd.repr base false = s!"{dd.tname}({r}, {base dd.items})" ∧
      dd.repr base true = s!"{dd.tname}({"..."}, {base dd.items})") ∧
    ((∀ r run, dd.factory ≠ .call r run) → dd.repr base false = s!"{dd.tname}({"None"}, {base dd.items})") ∧
    (∀ rest, dd.init .bad rest = (.error (.typeError "first argument must be callable or None"), dd)) ∧
    (∀ f e, dd.init (.given f) (.error e) = (.error e, { dd with factory := f })) ∧
    (∀ f kvs, dd.init (.given f) (.ok kvs) =
      (.ok (), { dd with factory := f, items := dictUpdate dd.items kvs })) ∧
    (∀ kvs, dd.init .absent (.ok kvs) =
      (.ok (), { dd with factory := .null, items := dictUpdate dd.items kvs })) ∧
    (∀ r : DefDict.Operand κ ν, r.items? ≠ none →
      ∀ i, r.items? = some i →
        DefDict.orOp (.dd dd) r = some { dd.newFrom dd.items with
          items := dictUpdate (dd.newFrom dd.items).items i }) ∧
    (∀ l : PyDict κ ν, DefDict.orOp (.plain l) (.dd dd) = some { dd.newFrom l with
          items := dictUpdate (dd.newFrom l).items dd.items }) ∧
    (∀ l : PyDict κ ν, DefDict.orOp (.frozen l) (.dd dd) = some { dd.newFrom l with
          items := dictUpdate (dd.newFrom l).items dd.items }) ∧
    DefDict.orOp (.dd dd) .notDict = none ∧ DefDict.orOp .notDict (.dd dd) = none

theorem defDictReprInitOr_proven : DefDictReprInitOr := by
  intro κ ν _ dd base
  refine ⟨fun r run hf => ?_, fun hn => ?_, fun rest => rfl, fun f e => rfl, fun f kvs => rfl, fun kvs => rfl,
    fun r _ i hi => ?_, fun l => rfl, fun l => rfl, rfl, rfl⟩
  · simp [DefDict.repr, hf]
  · simp only [DefDict.repr]
    cases hf : dd.factory with
    | null => simp
    | none => simp
    | call r run => exact absurd hf (hn r run)
  · cases r with
    | dd d =>
      simp only [DefDict.Operand.items?, Option.some.injEq] at hi
      subst hi
      rfl
    | plain p =>
      simp only [DefDict.Operand.items?, Option.some.injEq] at hi
      subst hi
      rfl
    | frozen p =>
      simp only [DefDict.Operand.items?, Option.some.injEq] at hi
      subst hi
      rfl
    | notDict => simp [DefDict.Operand.items?] at hi

/-- `_count_elements(mapping, keys)` on a real dict: the fast path, the slow path through
`mapping.get` and `mapping[k] = v`, and the pure-Python twin of
`Lib/collections/__init__.py:540-544` end in the same state with the same outcome, for
every key list, every initial dict, every `__hash__` (the same outcome on all three, which
abstracts the message: the slow path's `dict.get` words `TypeError` differently) and every
`__add__`, including one that raises. The hypotheses: `0 + 1` is `1`, what the fast path
stores for a new key, and the slow path's identity test `oldval is 0` only holds for 0. -/
def CountAgree : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (hash : κ → Py Unit) (add1 : ν → Py ν) (zero one : ν)
    (isZero : ν → Bool) (ks : List κ) (d : PyDict κ ν),
    add1 zero = .ok one → (∀ v, isZero v = true → v = zero) →
    countFast hash add1 one ks d =
      countSlow (dictMget hash zero) dictMset isZero add1 one ks d ∧
    countFast hash add1 one ks d = countPy (dictMget hash zero) dictMset add1 ks d

theorem countAgree_proven : CountAgree := by
  intro κ ν _ hash add1 zero one isZero ks d h1 hz
  induction ks generalizing d with
  | nil => exact ⟨rfl, rfl⟩
  | cons k ks ih =>
    simp only [countFast, countSlow, countPy, dictMget, dictMset]
    cases hh : hash k with
    | error e => exact ⟨rfl, rfl⟩
    | ok u =>
      cases u
      simp only
      cases hg : dictGet d k with
      | none =>
        simp only [Option.getD_none, h1]
        rw [show (if isZero zero = true then (.ok one : Py ν) else .ok one) = .ok one by split <;> rfl]
        exact ih _
      | some old =>
        simp only [Option.getD_some]
        by_cases hzo : isZero old = true
        · have : old = zero := hz _ hzo
          subst this
          rw [iteT hzo, h1]
          exact ih _
        · rw [iteF hzo]
          cases ha : add1 old with
          | error e => exact ⟨rfl, rfl⟩
          | ok v => exact ih _

/-- With `int` values and `+ 1`, for every key list and initial dict, the fast path adds
the number of occurrences of every key to its count (`Counter.update`'s promise), and
`_count_elements` keeps the counts it reached when the iterable raises. A non-iterable
raises `TypeError` and changes nothing. -/
def CountElements : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (ks : List κ) (d : PyDict κ Int),
    let add1 : Int → Py Int := fun v => .ok (v + 1)
    let hash : κ → Py Unit := fun _ => .ok ()
    (countFast hash add1 1 ks d).1 = .ok () ∧
    (∀ k, ((dictGet (countFast hash add1 1 ks d).2 k).getD 0 = (dictGet d k).getD 0 + ks.count k)) ∧
    (∀ e, e ≠ .stopIteration → countDict hash add1 1 (.iter ks (some e)) d =
      (.error e, (countFast hash add1 1 ks d).2)) ∧
    (∀ t, countDict hash add1 1 (.notIterable t) d = (.error (notIterableErr t), d))

theorem countElements_proven : CountElements := by
  intro κ _ ks d
  intro add1 hash
  have main : ∀ (ks : List κ) (d : PyDict κ Int), (countFast hash add1 1 ks d).1 = .ok () ∧
      ∀ k, ((dictGet (countFast hash add1 1 ks d).2 k).getD 0 = (dictGet d k).getD 0 + ks.count k) := by
    intro ks
    induction ks with
    | nil => intro d; exact ⟨rfl, fun k => by simp [countFast]⟩
    | cons x xs ih =>
      intro d
      cases hg : dictGet d x with
      | none =>
        have e : countFast hash add1 1 (x :: xs) d = countFast hash add1 1 xs (dictSet d x 1) := by
          simp only [countFast, hash, hg]
        rw [e]
        refine ⟨(ih _).1, fun k => ?_⟩
        rw [(ih _).2 k]
        by_cases hk : k = x
        · subst hk
          rw [dictGet_set_same, hg, List.count_cons_self]
          simp; omega
        · rw [dictGet_set_other _ _ _ _ hk, List.count_cons_of_ne (Ne.symm hk)]
      | some old =>
        have e : countFast hash add1 1 (x :: xs) d = countFast hash add1 1 xs (dictSet d x (old + 1)) := by
          simp only [countFast, hash, hg, add1]
        rw [e]
        refine ⟨(ih _).1, fun k => ?_⟩
        rw [(ih _).2 k]
        by_cases hk : k = x
        · subst hk
          rw [dictGet_set_same, hg, List.count_cons_self]
          simp; omega
        · rw [dictGet_set_other _ _ _ _ hk, List.count_cons_of_ne (Ne.symm hk)]
  refine ⟨(main ks d).1, (main ks d).2, fun e he => ?_, fun t => rfl⟩
  have h := (main ks d).1
  have hp : countFast hash add1 1 ks d = (.ok (), (countFast hash add1 1 ks d).2) := by
    cases hc : countFast hash add1 1 ks d with
    | mk r s =>
      rw [hc] at h
      simp only at h
      rw [h]
  simp only [countDict]
  rw [hp]
  simp only [countFinish]
  try (cases e <;> first | exact absurd rfl he | rfl)

end Dict

/-- `_tuplegetter`, for every index and every object: on a tuple it gives item `index`
when `0 <= index < len`, and `IndexError` otherwise, a negative index included (no wrap
around, unlike `t[i]`); any other object raises `TypeError`; on the class it is the
descriptor; assignment and deletion raise `AttributeError`; `__reduce__` rebuilds it; an
`index` outside `Py_ssize_t` is refused; `repr` shows index and doc. -/
def TupleGetterSpec : Prop :=
  ∀ (α δ : Type) [Inhabited α] (g : TupleGetter δ) (xs : List α) (t : String)
    (docRepr : δ → String),
    (∀ i : Nat, g.index = i → (h : i < xs.length) →
      tuplegetterGet (α := α) g (.tuple xs) = .ok (some xs[i])) ∧
    ((g.index < 0 ∨ g.index ≥ xs.length) →
      tuplegetterGet g (.tuple xs) = .error (.indexError "tuple index out of range")) ∧
    (tuplegetterGet (α := α) g (.other t)).raises "TypeError" ∧
    tuplegetterGet (α := α) g .none = .ok none ∧ tuplegetterGet (α := α) g .null = .ok none ∧
    (∀ v : Option α, (tuplegetterSet v).className = "AttributeError") ∧
    (ssizeMin ≤ g.index → g.index ≤ ssizeMax →
      tuplegetterNew (tuplegetterReduce g).1 (tuplegetterReduce g).2 = .ok g) ∧
    (∀ (i : Int) (d : δ), (i < ssizeMin ∨ i > ssizeMax) → (tuplegetterNew i d).raises "OverflowError") ∧
    tuplegetterRepr g docRepr = s!"_tuplegetter({g.index}, {docRepr g.doc})"

theorem tupleGetterSpec_proven : TupleGetterSpec := by
  intro α δ _ g xs t docRepr
  refine ⟨fun i hi h1 => ?_, fun h => ?_, ⟨_, rfl, rfl⟩, rfl, rfl, fun v => ?_, fun h0 h1 => ?_, fun i d h => ?_, rfl⟩
  · have hv : validIndex (i : Int) xs.length = true := by simp [validIndex]; omega
    simp only [tuplegetterGet, hi, hv, Bool.not_true, Bool.false_eq_true, ite_false]
    rw [ix_getElem _ _ h1]
  · have hv : validIndex g.index xs.length = false := by simp [validIndex]; omega
    simp only [tuplegetterGet, hv, Bool.not_false, ite_true]
  · cases v <;> rfl
  · obtain ⟨i, d⟩ := g
    simp only at h0 h1
    have hs : asSsize i = .ok i := by unfold asSsize; rw [iteT ⟨h0, h1⟩]
    simp only [tuplegetterNew, tuplegetterReduce, hs, bind, Except.bind, pure, Except.pure]
  · have hs : asSsize i = .error (.overflowError "Python int too large to convert to C ssize_t") := by
      unfold asSsize; rw [iteF (by omega)]
    simp only [tuplegetterNew, hs, bind, Except.bind]
    exact ⟨_, rfl, rfl⟩

end PyLean.Sequences
