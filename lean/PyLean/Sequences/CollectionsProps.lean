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
becoming `None`. `dd.__reduce__()` calls `dd.items()` (which a subclass may override):
with `dict.items` it returns the 5-tuple `(type(dd), args, None, None, iterator over the
items)`, with `args` empty for a `NULL` or `None` factory and `(factory,)` for a callable
one; an `items()` that raises makes `__reduce__` raise the same exception, and one that
returns a non-iterable raises `TypeError` from `iter()`. -/
def DefDictCopyReduce : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (dd : DefDict κ ν), (dd.items.map Prod.fst).Nodup →
    dd.copy.items = dd.items ∧ dd.copy.tname = dd.tname ∧
    (∀ r run, dd.factory = .call r run → dd.copy.factory = .call r run) ∧
    ((∀ r run, dd.factory ≠ .call r run) → dd.copy.factory = .none) ∧
    ((∀ r run, dd.factory ≠ .call r run) →
      dd.reduce (.ok (.iter dd.items none)) = .ok [.type dd.tname, .args [], .none, .none, .iter dd.items none]) ∧
    (∀ r run, dd.factory = .call r run →
      dd.reduce (.ok (.iter dd.items none)) =
        .ok [.type dd.tname, .args [.call r run], .none, .none, .iter dd.items none]) ∧
    (∀ e, dd.reduce (.error e) = .error e) ∧
    (∀ t, dd.reduce (.ok (.notIterable t)) = .error (notIterableErr t))

theorem defDictCopyReduce_proven : DefDictCopyReduce := by
  intro κ ν _ dd hn
  refine ⟨?_, rfl, fun r run hf => ?_, fun hc => ?_, fun hc => ?_, fun r run hf => ?_, fun e => rfl, fun t => rfl⟩
  · simp only [DefDict.copy, DefDict.newFrom]
    rw [dictUpdate_fresh [] _ (by simpa using hn)]
    simp
  · simp only [DefDict.copy, DefDict.newFrom, hf]
  · simp only [DefDict.copy, DefDict.newFrom]
    cases hf : dd.factory with
    | null => rfl
    | none => rfl
    | call r run => exact absurd hf (hc r run)
  · simp only [DefDict.reduce]
    cases hf : dd.factory with
    | null => rfl
    | none => rfl
    | call r run => exact absurd hf (hc r run)
  · simp only [DefDict.reduce, hf]

/-- `repr(dd)`, for every defaultdict, every `dict.__repr__` outcome `base` of its items
and every outcome `entered` of `Py_ReprEnter(factory)`: the dict's repr comes first, so
when it raises `e` the result is `e` whatever the factory; otherwise a `NULL` factory
prints `None` without `Py_ReprEnter` (even when that would fail); for any other factory a
failing `Py_ReprEnter` raises, a factory already being printed shows `...`, `None` shows
`None`, and a callable shows its `repr()`, or raises what that raises. The result is
`type(factory repr, dict repr)`.
`dd.__init__`: a first argument that is neither callable nor `None` raises `TypeError` and
changes nothing; otherwise the factory is replaced before `dict.__init__` runs, so it stays
replaced when that raises. `left | right` for two dict operands has the items of `left`
updated by `right`, and the type and factory of the defaultdict operand (the left one if
both are); a `frozendict` operand counts as a dict since 3.15, and anything else gives
`NotImplemented`. -/
def DefDictReprInitOr : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (dd : DefDict κ ν) (base : PyDict κ ν → Py String) (entered : Py Bool),
    (∀ e, base dd.items = .error e → dd.repr base entered = .error e) ∧
    (∀ s, base dd.items = .ok s →
      (dd.factory = .null → dd.repr base entered = .ok s!"{dd.tname}(None, {s})") ∧
      (dd.factory ≠ .null → ∀ e, entered = .error e → dd.repr base entered = .error e) ∧
      (dd.factory ≠ .null → entered = .ok true → dd.repr base entered = .ok s!"{dd.tname}(..., {s})") ∧
      (dd.factory = .none → entered = .ok false → dd.repr base entered = .ok s!"{dd.tname}(None, {s})") ∧
      (∀ r run, dd.factory = .call r run → entered = .ok false →
        (∀ t, r = .ok t → dd.repr base entered = .ok s!"{dd.tname}({t}, {s})") ∧
        (∀ e, r = .error e → dd.repr base entered = .error e))) ∧
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
  intro κ ν _ dd base entered
  refine ⟨fun e he => ?_, fun s hs => ⟨fun hf => ?_, fun hf e he => ?_, fun hf he => ?_, fun hf he => ?_,
    fun r run hf he => ⟨fun t ht => ?_, fun e hr => ?_⟩⟩, fun rest => rfl, fun f e => rfl, fun f kvs => rfl,
    fun kvs => rfl, fun r _ i hi => ?_, fun l => rfl, fun l => rfl, rfl, rfl⟩
  · simp only [DefDict.repr, he, bind, Except.bind]
  · simp only [DefDict.repr, hs, hf, bind, Except.bind, pure, Except.pure]
  · cases hc : dd.factory with
    | null => exact absurd hc hf
    | none => simp only [DefDict.repr, hs, hc, he, bind, Except.bind]
    | call r run => simp only [DefDict.repr, hs, hc, he, bind, Except.bind]
  · cases hc : dd.factory with
    | null => exact absurd hc hf
    | none => simp only [DefDict.repr, hs, hc, he, bind, Except.bind, pure, Except.pure, ite_true]
    | call r run => simp only [DefDict.repr, hs, hc, he, bind, Except.bind, pure, Except.pure, ite_true]
  · simp only [DefDict.repr, hs, hf, he, bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ite_false]
  · simp only [DefDict.repr, hs, hf, he, ht, bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ite_false]
  · simp only [DefDict.repr, hs, hf, he, hr, bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ite_false]
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

/-- `_count_elements(mapping, iterable)` on a real dict: the fast path, the slow path through
`mapping.get` and `mapping[k] = v`, and the pure-Python twin of
`Lib/collections/__init__.py:540-544` end in the same state with the same outcome, for
every iterator (each `__next__` may change the dict, raise, or raise `StopIteration`),
every initial dict, every `__hash__` (the same outcome on all three, which abstracts the
message: the slow path's `dict.get` words `TypeError` differently) and every `__add__`,
including one that raises and one that mutates or clears the dict (the C fast path stores
the sum into the dict as `__add__` left it, as the twin does). The hypotheses: `0 + 1` is
`1` without side effects, what the fast path stores for a new key, and the slow path's
identity test `oldval is 0` only holds for 0. -/
def CountAgree : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (hash : κ → Py Unit) (add1 : PyDict κ ν → ν → Py ν × PyDict κ ν)
    (zero one : ν) (isZero : ν → Bool) (nexts : List (KeyNext κ (PyDict κ ν))) (d : PyDict κ ν),
    (∀ s, add1 s zero = (.ok one, s)) → (∀ v, isZero v = true → v = zero) →
    countFast hash add1 one nexts d =
      countSlow (dictMget hash zero) dictMset isZero add1 one nexts d ∧
    countFast hash add1 one nexts d = countPy (dictMget hash zero) dictMset add1 nexts d

theorem countAgree_proven : CountAgree := by
  intro κ ν _ hash add1 zero one isZero nexts d h1 hz
  induction nexts generalizing d with
  | nil => exact ⟨rfl, rfl⟩
  | cons nx rest ih =>
    simp only [countFast, countSlow, countPy, dictMget, dictMset]
    rcases hn : nx d with ⟨r, d1⟩
    cases r with
    | error e => exact ⟨rfl, rfl⟩
    | ok k =>
      simp only
      cases hh : hash k with
      | error e => exact ⟨rfl, rfl⟩
      | ok u =>
        cases u
        simp only
        cases hg : dictGet d1 k with
        | none =>
          simp only [Option.getD_none, h1]
          rw [show (if isZero zero = true then ((.ok one : Py ν), d1) else (.ok one, d1)) = (.ok one, d1) by
            split <;> rfl]
          exact ih _
        | some old =>
          simp only [Option.getD_some]
          by_cases hzo : isZero old = true
          · have : old = zero := hz _ hzo
            subst this
            rw [iteT hzo, h1]
            exact ih _
          · rw [iteF hzo]
            rcases ha : add1 d1 old with ⟨r2, d2⟩
            cases r2 with
            | error e => exact ⟨rfl, rfl⟩
            | ok v => exact ih _

/-- With `int` counts and `+ 1`, for every key list and initial dict, the fast path adds
the number of occurrences of every key to its count (`Counter.update`'s promise), and
`_count_elements` keeps the counts it reached when the iterable raises (`StopIteration`
is the normal end). A non-iterable raises `TypeError` and changes nothing. For every
`__add__` and every key already present, the sum is stored into the dict as `__add__`
left it, so an `__add__` that clears the dict leaves only that key (the path the comment at
_collectionsmodule.c:2604-2606 guards). -/
def CountElements : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (ks : List κ) (d : PyDict κ Int),
    let add1 : PyDict κ Int → Int → Py Int × PyDict κ Int := fun s v => (.ok (v + 1), s)
    let hash : κ → Py Unit := fun _ => .ok ()
    (countFast hash add1 1 (pureKeys ks) d).1 = .ok () ∧
    (∀ k, ((dictGet (countFast hash add1 1 (pureKeys ks) d).2 k).getD 0 = (dictGet d k).getD 0 + ks.count k)) ∧
    (∀ e, e ≠ .stopIteration → countDict hash add1 1 (.ofIterable (.iter ks (some e))) d =
      (.error e, (countFast hash add1 1 (pureKeys ks) d).2)) ∧
    countDict hash add1 1 (.ofIterable (.iter ks (some .stopIteration))) d =
      (.ok (), (countFast hash add1 1 (pureKeys ks) d).2) ∧
    (∀ t, countDict hash add1 1 (.notIterable t) d = (.error (notIterableErr t), d)) ∧
    (∀ (add : PyDict κ Int → Int → Py Int × PyDict κ Int) (k : κ) (old v : Int) (d' : PyDict κ Int),
      dictGet d k = some old → add d old = (.ok v, d') →
      countFast hash add 1 (pureKeys [k]) d = (.ok (), dictSet d' k v))

theorem countFast_append (hash : κ → Py Unit) (add1 : PyDict κ ν → ν → Py ν × PyDict κ ν)
    (one : ν) (fin : List (KeyNext κ (PyDict κ ν))) :
    ∀ (ks : List κ) (d : PyDict κ ν), (countFast hash add1 one (pureKeys ks) d).1 = .ok () →
      countFast hash add1 one (pureKeys ks ++ fin) d =
        countFast hash add1 one fin (countFast hash add1 one (pureKeys ks) d).2
  | [], d, _ => rfl
  | k :: ks, d, h => by
    simp only [pureKeys, List.map_cons, List.cons_append, countFast] at h ⊢
    cases hh : hash k with
    | error e => rw [hh] at h; exact nomatch h
    | ok u =>
      cases u
      rw [hh] at h
      simp only at h ⊢
      cases hg : dictGet d k with
      | none => rw [hg] at h; exact countFast_append hash add1 one fin ks _ h
      | some old =>
        rw [hg] at h
        simp only at h ⊢
        rcases ha : add1 d old with ⟨r, d2⟩
        rw [ha] at h
        cases r with
        | error e => exact nomatch h
        | ok v => exact countFast_append hash add1 one fin ks _ h

theorem countElements_proven : CountElements := by
  intro κ _ ks d
  intro add1 hash
  have main : ∀ (ks : List κ) (d : PyDict κ Int), (countFast hash add1 1 (pureKeys ks) d).1 = .ok () ∧
      ∀ k, ((dictGet (countFast hash add1 1 (pureKeys ks) d).2 k).getD 0 = (dictGet d k).getD 0 + ks.count k) := by
    intro ks
    induction ks with
    | nil => intro d; exact ⟨rfl, fun k => by simp [countFast, pureKeys]⟩
    | cons x xs ih =>
      intro d
      cases hg : dictGet d x with
      | none =>
        have e : countFast hash add1 1 (pureKeys (x :: xs)) d = countFast hash add1 1 (pureKeys xs) (dictSet d x 1) := by
          simp only [pureKeys, List.map_cons, countFast, hash, hg]
        rw [e]
        refine ⟨(ih _).1, fun k => ?_⟩
        rw [(ih _).2 k]
        by_cases hk : k = x
        · subst hk
          rw [dictGet_set_same, hg, List.count_cons_self]
          simp; omega
        · rw [dictGet_set_other _ _ _ _ hk, List.count_cons_of_ne (Ne.symm hk)]
      | some old =>
        have e : countFast hash add1 1 (pureKeys (x :: xs)) d =
            countFast hash add1 1 (pureKeys xs) (dictSet d x (old + 1)) := by
          simp only [pureKeys, List.map_cons, countFast, hash, hg, add1]
        rw [e]
        refine ⟨(ih _).1, fun k => ?_⟩
        rw [(ih _).2 k]
        by_cases hk : k = x
        · subst hk
          rw [dictGet_set_same, hg, List.count_cons_self]
          simp; omega
        · rw [dictGet_set_other _ _ _ _ hk, List.count_cons_of_ne (Ne.symm hk)]
  have hp := countFast_append hash add1 1
  refine ⟨(main ks d).1, (main ks d).2, fun e he => ?_, ?_, fun t => rfl, fun add k old v d' hg ha => ?_⟩
  · simp only [countDict, KeySrc.ofIterable]
    rw [hp _ ks d (main ks d).1]
    simp only [countFast, iterEnd]
    cases e <;> first | exact absurd rfl he | rfl
  · simp only [countDict, KeySrc.ofIterable]
    rw [hp _ ks d (main ks d).1]
    rfl
  · simp only [pureKeys, List.map_cons, List.map_nil, countFast, hash, hg, ha]

end Dict

/-- `_tuplegetter`, for every index and every object: on a tuple it gives item `index`
when `0 <= index < len`, and `IndexError` otherwise, a negative index included (no wrap
around, unlike `t[i]`); any other object raises `TypeError`; on the class it is the
descriptor; assignment raises `AttributeError("can't set attribute")` and deletion
`AttributeError("can't delete attribute")`; `__reduce__` rebuilds it; an `index` outside
`Py_ssize_t` is refused. `repr(g)` is the type name followed by the repr of the
`__reduce__` arguments `(index, doc)` (decimal index, `repr(doc)`), for every doc
`repr`, and raises what `repr(doc)` raises. -/
def TupleGetterSpec : Prop :=
  ∀ (α δ : Type) [Inhabited α] (g : TupleGetter δ) (xs : List α) (t : String)
    (docRepr : δ → Py String),
    (∀ i : Nat, g.index = i → (h : i < xs.length) →
      tuplegetterGet (α := α) g (.tuple xs) = .ok (some xs[i])) ∧
    ((g.index < 0 ∨ g.index ≥ xs.length) →
      tuplegetterGet g (.tuple xs) = .error (.indexError "tuple index out of range")) ∧
    (tuplegetterGet (α := α) g (.other t)).raises "TypeError" ∧
    tuplegetterGet (α := α) g .none = .ok none ∧ tuplegetterGet (α := α) g .null = .ok none ∧
    (∀ v : α, tuplegetterSet (some v) = .named "AttributeError" "can't set attribute") ∧
    tuplegetterSet (none : Option α) = .named "AttributeError" "can't delete attribute" ∧
    (ssizeMin ≤ g.index → g.index ≤ ssizeMax →
      tuplegetterNew (tuplegetterReduce g).1 (tuplegetterReduce g).2 = .ok g) ∧
    (∀ (i : Int) (d : δ), (i < ssizeMin ∨ i > ssizeMax) → (tuplegetterNew i d).raises "OverflowError") ∧
    (∀ s, docRepr (tuplegetterReduce g).2 = .ok s →
      tuplegetterRepr g docRepr = .ok ("_tuplegetter" ++ s!"({(tuplegetterReduce g).1}, {s})")) ∧
    (∀ e, docRepr g.doc = .error e → tuplegetterRepr g docRepr = .error e)

theorem tupleGetterSpec_proven : TupleGetterSpec := by
  intro α δ _ g xs t docRepr
  refine ⟨fun i hi h1 => ?_, fun h => ?_, ⟨_, rfl, rfl⟩, rfl, rfl, fun v => rfl, rfl, fun h0 h1 => ?_,
    fun i d h => ?_, fun s hs => ?_, fun e he => ?_⟩
  · have hv : validIndex (i : Int) xs.length = true := by simp [validIndex]; omega
    simp only [tuplegetterGet, hi, hv, Bool.not_true, Bool.false_eq_true, ite_false]
    rw [ix_getElem _ _ h1]
  · have hv : validIndex g.index xs.length = false := by simp [validIndex]; omega
    simp only [tuplegetterGet, hv, Bool.not_false, ite_true]
  · obtain ⟨i, d⟩ := g
    simp only at h0 h1
    have hs : asSsize i = .ok i := by unfold asSsize; rw [iteT ⟨h0, h1⟩]
    simp only [tuplegetterNew, tuplegetterReduce, hs, bind, Except.bind, pure, Except.pure]
  · have hs : asSsize i = .error (.overflowError "Python int too large to convert to C ssize_t") := by
      unfold asSsize; rw [iteF (by omega)]
    simp only [tuplegetterNew, hs, bind, Except.bind]
    exact ⟨_, rfl, rfl⟩
  · simp only [tuplegetterReduce] at hs
    simp only [tuplegetterRepr, tuplegetterReduce, hs, bind, Except.bind, pure, Except.pure]
    rfl
  · simp only [tuplegetterRepr, he, bind, Except.bind]

end PyLean.Sequences
