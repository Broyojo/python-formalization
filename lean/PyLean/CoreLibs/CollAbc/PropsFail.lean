import PyLean.CoreLibs.CollAbc.Props
import PyLean.CoreLibs.CollAbc.PropsMap

/-!
The failure paths of the `Mapping`, `Sequence` and `throw` mixins, over any subclass's primitives. `PropsMap` and
`PropsSeq` compare the mixins with `dict` and `list`, whose primitives raise only `KeyError` and `IndexError`, so a
mixin that swallowed every exception would pass them. These statements take primitives that can raise anything.
-/

namespace PyLean.CoreLibs.CollAbc

open PyLean

/-! ### `throw` -/

/-- `Generator.throw` and the two others, every path of Lib/_collections_abc.py:374-380, for any objects: `raise typ`
calls a class with no arguments, so a class whose constructor needs arguments (`UnicodeDecodeError`) raises the
constructor's `TypeError` whatever `tb` is, and a class whose constructor makes a non-exception is a `TypeError`;
`val = typ()` calls any callable, so a function returning an exception works with a traceback, and an instance or a
non-callable is "object is not callable"; `with_traceback` refuses a non-traceback on an instance, does not apply on a
class, and is looked up on any other object, whose own method's result is raised. -/
def ThrowPaths : Prop :=
  ∀ (n m t : String) (b : Bool) (e : PyExc) (c w : Option TMade) (typ : TObj) (tb : TbArg) (mk : TMade),
    throwBody (.excClass n (.obj (.excInst m false))) none .absent = .ok ⟨m, false⟩ ∧
    throwBody (.excClass n (.raises e)) none tb = .error e ∧
    Py.raises (throwBody (.excClass n (.obj (.other t c w))) none .absent) "TypeError" ∧
    throwBody (.excInst n b) none .absent = .ok ⟨n, b⟩ ∧
    throwBody (.other t c w) none .absent = .error (.typeError "exceptions must derive from BaseException") ∧
    throwBody (.excClass n (.obj (.excInst m b))) none .traceback = .ok ⟨m, true⟩ ∧
    throwBody (.excClass n (.obj (.excInst m b))) none .other =
      .error (.typeError "__traceback__ must be a traceback or None") ∧
    (tb ≠ .absent → throwBody (.excInst n b) none tb = .error (.typeError s!"'{n}' object is not callable")) ∧
    (tb ≠ .absent → throwBody (.other t none w) none tb = .error (.typeError s!"'{t}' object is not callable")) ∧
    throwBody (.other t (some (.obj (.excInst m false))) w) none .traceback = .ok ⟨m, true⟩ ∧
    (tb ≠ .absent → throwBody (.other t (some (.raises e)) w) none tb = .error e) ∧
    throwBody typ (some (.excInst m b)) .absent = .ok ⟨m, b⟩ ∧
    throwBody typ (some (.excInst m b)) .traceback = .ok ⟨m, true⟩ ∧
    throwBody typ (some (.excInst m b)) .other = .error (.typeError "__traceback__ must be a traceback or None") ∧
    throwBody typ (some (.excClass n (.obj (.excInst m b)))) .absent = .ok ⟨m, b⟩ ∧
    (tb ≠ .absent → Py.raises (throwBody typ (some (.excClass n mk)) tb) "TypeError") ∧
    (tb ≠ .absent → throwBody typ (some (.other t c none)) tb =
      .error (.named "AttributeError" s!"'{t}' object has no attribute 'with_traceback'")) ∧
    throwBody typ (some (.other t c (some (.obj (.excInst m b))))) .traceback = .ok ⟨m, b⟩ ∧
    throwBody typ (some (.other t c w)) .absent = .error (.typeError "exceptions must derive from BaseException")

theorem throwPaths_proven : ThrowPaths := by
  intro n m t b e c w typ tb mk
  refine ⟨rfl, ?_, ⟨_, rfl, rfl⟩, rfl, rfl, rfl, rfl, ?_, ?_, rfl, ?_, rfl, rfl, rfl, rfl, ?_, ?_, rfl, rfl⟩
  · cases tb <;> rfl
  · intro h; cases tb <;> first | exact absurd rfl h | rfl
  · intro h; cases tb <;> first | exact absurd rfl h | rfl
  · intro h; cases tb <;> first | exact absurd rfl h | rfl
  · intro h; cases tb <;> first | exact absurd rfl h | exact ⟨_, rfl, rfl⟩
  · intro h; cases tb <;> first | exact absurd rfl h | rfl

/-! ### `Mapping` -/

/-- `get`, `__contains__` and `ItemsView.__contains__` catch `KeyError` and nothing else, for any `__getitem__`; the
unpack in `ItemsView.__contains__` is outside the `try` and raises before any lookup, with CPython's messages: the count
read in "not enough values", and the length in "too many values" only for an exact list, tuple or dict, so `"abc"`
and an iterator say only "(expected 2)"; an iterator that raises is the outcome. `KeysView.__contains__` is the
mapping's own `__contains__`. -/
def MappingPaths : Prop :=
  ∀ (K V : Type) (m : MapV K V) (E : EqOps V) (key : K) (default v value : V) (e : PyExc) (n : Nat) (t : String)
    (f : K → Py Bool),
    (m.getitem key = .ok v →
      m.get key default = .ok v ∧ m.contains key = .ok true ∧
      m.itemsContain E (.two key value none) = E.same v value) ∧
    (isKeyError e = true → m.getitem key = .error e →
      m.get key default = .ok default ∧ m.contains key = .ok false ∧
      m.itemsContain E (.two key value none) = .ok false) ∧
    (isKeyError e = false → m.getitem key = .error e →
      m.get key default = .error e ∧ m.contains key = .error e ∧
      m.itemsContain E (.two key value none) = .error e) ∧
    m.itemsContain E (.notIterable t : ItemArg K V) = .error (.typeError s!"cannot unpack non-iterable {t} object") ∧
    m.itemsContain E (.iterFails e : ItemArg K V) = .error e ∧
    m.itemsContain E (.zero none : ItemArg K V) =
      .error (.valueError "not enough values to unpack (expected 2, got 0)") ∧
    m.itemsContain E (.one key none : ItemArg K V) =
      .error (.valueError "not enough values to unpack (expected 2, got 1)") ∧
    m.itemsContain E (.zero (some e) : ItemArg K V) = .error e ∧
    m.itemsContain E (.one key (some e) : ItemArg K V) = .error e ∧
    m.itemsContain E (.two key value (some e)) = .error e ∧
    m.itemsContain E (.many key value none) = .error (.valueError "too many values to unpack (expected 2)") ∧
    (2 < n → m.itemsContain E (.many key value (some n)) =
      .error (.valueError s!"too many values to unpack (expected 2, got {n})")) ∧
    (E.is_ v value = true → E.same v value = .ok true) ∧
    (E.is_ v value = false → E.same v value = E.eq v value) ∧
    { m with containsOverride := some f }.keyIn key = f key ∧
    { m with containsOverride := none }.keyIn key = m.contains key

theorem mappingPaths_proven : MappingPaths := by
  intro K V m E key default v value e n t f
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, rfl, rfl⟩
  · intro h; simp [MapV.get, MapV.contains, MapV.itemsContain, unpack2, h, bind, Except.bind]
  · intro h1 h; simp [MapV.get, MapV.contains, MapV.itemsContain, unpack2, h, h1, bind, Except.bind]
  · intro h1 h; simp [MapV.get, MapV.contains, MapV.itemsContain, unpack2, h, h1, bind, Except.bind]
  · intro h; simp [MapV.itemsContain, unpack2, h, bind, Except.bind]
  · intro h; simp [EqOps.same, h, pure, Except.pure]
  · intro h; simp [EqOps.same, h]

theorem itemsOf_ok {K V : Type} (m : MapV K V) (f : K → V) : ∀ ks : List K, (∀ x ∈ ks, m.getitem x = .ok (f x)) →
    m.itemsOf ks = raiseTail m.tail (ks.map fun x => (x, f x)) ∧ m.valuesOf ks = raiseTail m.tail (ks.map f)
  | [], _ => ⟨rfl, rfl⟩
  | k :: ks, h => by
    have hk := h k (by simp)
    obtain ⟨ih1, ih2⟩ := itemsOf_ok m f ks (fun x hx => h x (by simp [hx]))
    constructor
    · simp only [MapV.itemsOf, hk, ih1, bind, Except.bind, List.map_cons]
      cases m.tail <;> rfl
    · simp only [MapV.valuesOf, hk, ih2, bind, Except.bind, List.map_cons]
      cases m.tail <;> rfl

theorem itemsOf_err {K V : Type} (m : MapV K V) (f : K → V) (k : K) (post : List K) (e : PyExc)
    (hk : m.getitem k = .error e) : ∀ pre : List K, (∀ x ∈ pre, m.getitem x = .ok (f x)) →
    m.itemsOf (pre ++ k :: post) = .error e ∧ m.valuesOf (pre ++ k :: post) = .error e
  | [], _ => by simp [MapV.itemsOf, MapV.valuesOf, hk, bind, Except.bind]
  | x :: xs, h => by
    have hx := h x (by simp)
    obtain ⟨ih1, ih2⟩ := itemsOf_err m f k post e hk xs (fun y hy => h y (by simp [hy]))
    simp [MapV.itemsOf, MapV.valuesOf, hx, ih1, ih2, bind, Except.bind]

theorem valuesLoop_pre {K V : Type} (m : MapV K V) (E : EqOps V) (value : V) (f : K → V) (k : K) (post : List K) :
    ∀ pre : List K, (∀ x ∈ pre, m.getitem x = .ok (f x) ∧ E.same (f x) value = .ok false) →
    m.valuesLoop E value (pre ++ k :: post) = m.valuesLoop E value (k :: post)
  | [], _ => rfl
  | x :: xs, h => by
    obtain ⟨h1, h2⟩ := h x (by simp)
    simp only [List.cons_append, MapV.valuesLoop, h1, h2, bind, Except.bind, Bool.false_eq_true, ite_false]
    exact valuesLoop_pre m E value f k post xs (fun y hy => h y (by simp [hy]))

theorem valuesLoop_all {K V : Type} (m : MapV K V) (E : EqOps V) (value : V) (f : K → V) :
    ∀ ks : List K, (∀ x ∈ ks, m.getitem x = .ok (f x) ∧ E.same (f x) value = .ok false) →
    m.valuesLoop E value ks = raiseTail m.tail false
  | [], _ => rfl
  | x :: xs, h => by
    obtain ⟨h1, h2⟩ := h x (by simp)
    simp only [MapV.valuesLoop, h1, h2, bind, Except.bind, Bool.false_eq_true, ite_false]
    exact valuesLoop_all m E value f xs (fun y hy => h y (by simp [hy]))

/-- `ItemsView.__iter__`, `ValuesView.__iter__` and `ValuesView.__contains__`, for any mapping primitives: a failing
`iter(mapping)` is the outcome; each key's `self._mapping[key]` is read in order and nothing is caught, so the first
lookup that raises (a `KeyError` too) is the outcome, and a mapping iterator that raises after the keys is the
outcome when the loop reaches it; `__contains__` stops with `True` at the first value that is or equals the value,
before any later failure, and a raising `__eq__` is the outcome. -/
def MapViewPaths : Prop :=
  ∀ (K V : Type) (m : MapV K V) (E : EqOps V) (value v : V) (ks pre post : List K) (k : K) (e : PyExc)
    (f : K → V),
    (m.iter = .error e → m.items = .error e ∧ m.values = .error e ∧ m.valuesContain E value = .error e) ∧
    (m.iter = .ok ks → (∀ x ∈ ks, m.getitem x = .ok (f x)) →
      m.items = raiseTail m.tail (ks.map fun x => (x, f x)) ∧ m.values = raiseTail m.tail (ks.map f)) ∧
    (m.iter = .ok (pre ++ k :: post) → (∀ x ∈ pre, m.getitem x = .ok (f x)) → m.getitem k = .error e →
      m.items = .error e ∧ m.values = .error e) ∧
    (m.iter = .ok (pre ++ k :: post) → (∀ x ∈ pre, m.getitem x = .ok (f x) ∧ E.same (f x) value = .ok false) →
      (m.getitem k = .error e → m.valuesContain E value = .error e) ∧
      (m.getitem k = .ok v → E.same v value = .error e → m.valuesContain E value = .error e) ∧
      (m.getitem k = .ok v → E.same v value = .ok true → m.valuesContain E value = .ok true)) ∧
    (m.iter = .ok ks → (∀ x ∈ ks, m.getitem x = .ok (f x) ∧ E.same (f x) value = .ok false) →
      m.valuesContain E value = raiseTail m.tail false)

theorem mapViewPaths_proven : MapViewPaths := by
  intro K V m E value v ks pre post k e f
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [MapV.items, MapV.values, MapV.valuesContain, h, bind, Except.bind]
  · intro h1 h2
    obtain ⟨a, b⟩ := itemsOf_ok m f ks h2
    simp only [MapV.items, MapV.values, h1, bind, Except.bind]
    exact ⟨a, b⟩
  · intro h1 h2 h3
    obtain ⟨a, b⟩ := itemsOf_err m f k post e h3 pre h2
    simp only [MapV.items, MapV.values, h1, bind, Except.bind]
    exact ⟨a, b⟩
  · intro h1 h2
    have hp := valuesLoop_pre m E value f k post pre h2
    refine ⟨?_, ?_, ?_⟩
    · intro h3; simp [MapV.valuesContain, h1, hp, MapV.valuesLoop, h3, bind, Except.bind]
    · intro h3 h4; simp [MapV.valuesContain, h1, hp, MapV.valuesLoop, h3, h4, bind, Except.bind]
    · intro h3 h4; simp [MapV.valuesContain, h1, hp, MapV.valuesLoop, h3, h4, bind, Except.bind, pure, Except.pure]
  · intro h1 h2
    simp only [MapV.valuesContain, h1, bind, Except.bind]
    exact valuesLoop_all m E value f ks h2

/-- `Mapping.__eq__` over any primitives: a non-`Mapping` is `NotImplemented`; `dict(self.items())` is built in full
first, and for each key `self[key]` is read, then the key is hashed for insertion, before the next key, so a failing
`iter(self)`, lookup or hash is the outcome before anything of `other` runs (a later key's lookup included); a key seen
again keeps its place and takes the new value; then `dict(other.items())` the same way; then the builtin comparison of
the two dicts. Lib/_collections_abc.py:819-822 with `PyDict_MergeFromSeq2`. -/
def MappingEqPaths : Prop :=
  ∀ (K V : Type) [DecidableEq K] (hashKey : K → Py Unit) (dictEq : List (K × V) → List (K × V) → Py Bool)
    (m o : MapV K V) (k : K) (ks ks2 : List K) (v : V) (e : PyExc) (acc a b : List (K × V)),
    mappingEq hashKey dictEq m none = .ok .notImplemented ∧
    (m.iter = .error e → mappingEq hashKey dictEq m (some o) = .error e) ∧
    (m.iter = .ok ks → dictOfItems hashKey m [] ks = .error e → mappingEq hashKey dictEq m (some o) = .error e) ∧
    (m.iter = .ok ks → dictOfItems hashKey m [] ks = .ok a → o.iter = .error e →
      mappingEq hashKey dictEq m (some o) = .error e) ∧
    (m.iter = .ok ks → dictOfItems hashKey m [] ks = .ok a → o.iter = .ok ks2 → dictOfItems hashKey o [] ks2 = .error e →
      mappingEq hashKey dictEq m (some o) = .error e) ∧
    (m.iter = .ok ks → dictOfItems hashKey m [] ks = .ok a → o.iter = .ok ks2 → dictOfItems hashKey o [] ks2 = .ok b →
      mappingEq hashKey dictEq m (some o) = Ret.val <$> dictEq a b) ∧
    (m.getitem k = .error e → dictOfItems hashKey m acc (k :: ks) = .error e) ∧
    (m.getitem k = .ok v → hashKey k = .error e → dictOfItems hashKey m acc (k :: ks) = .error e) ∧
    (m.getitem k = .ok v → hashKey k = .ok () →
      dictOfItems hashKey m acc (k :: ks) = dictOfItems hashKey m (dictSet acc k v) ks) ∧
    dictOfItems hashKey m acc [] = raiseTail m.tail acc

theorem mappingEqPaths_proven : MappingEqPaths := by
  intro K V _ hashKey dictEq m o k ks ks2 v e acc a b
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro h; simp [mappingEq, h, bind, Except.bind]
  · intro h1 h2; simp [mappingEq, h1, h2, bind, Except.bind]
  · intro h1 h2 h3; simp [mappingEq, h1, h2, h3, bind, Except.bind]
  · intro h1 h2 h3 h4; simp [mappingEq, h1, h2, h3, h4, bind, Except.bind]
  · intro h1 h2 h3 h4
    simp only [mappingEq, h1, h2, h3, h4, bind, Except.bind]
    cases dictEq a b <;> rfl
  · intro h; simp [dictOfItems, h, bind, Except.bind]
  · intro h1 h2; simp [dictOfItems, h1, h2, bind, Except.bind]
  · intro h1 h2; simp [dictOfItems, h1, h2, bind, Except.bind]

/-! ### `MutableMapping` -/

/-- `pop`, `popitem`, `setdefault` and `update`, every path, for any primitives: which exception is swallowed, that a
failing `__delitem__` or `__setitem__` is the outcome, and the order of the steps. `update` takes a `Mapping` by its
keys and `__getitem__`; anything else with a `keys` attribute (`hasattr` may raise) by `other.keys()`; and anything
else by iteration with `key, value = item`, whose unpack error is the outcome before that item's assignment. Each
branch is pinned by its first step and the recursion on the rest. The keywords come last, in order. -/
def MMapPaths : Prop :=
  ∀ (σ K V : Type) (M : MMap σ K V) (s s' : σ) (key : K) (d v : V) (e : PyExc) (rest : List K) (kw : List (K × V))
    (o : MapV K V) (hk : Py Bool) (ks : Py (List K)) (kt t : Option PyExc) (gi : K → Py V)
    (xs : Py (List (ItemArg K V))) (x : ItemArg K V) (ys : List (ItemArg K V)),
    ((M.view s).getitem key = .ok v →
      M.pop s key (some d) = (do let t ← M.delitem s key; pure (v, t)) ∧
      M.setdefault s key d = .ok (v, s)) ∧
    (isKeyError e = true → (M.view s).getitem key = .error e →
      M.pop s key none = .error e ∧ M.pop s key (some d) = .ok (d, s) ∧
      M.setdefault s key d = (do let t ← M.setitem s key d; pure (d, t))) ∧
    (isKeyError e = false → (M.view s).getitem key = .error e →
      M.pop s key none = .error e ∧ M.pop s key (some d) = .error e ∧ M.setdefault s key d = .error e) ∧
    ((M.view s).iter = .error e → M.popitem s = .error e) ∧
    ((M.view s).iter = .ok [] → (M.view s).tail = none → M.popitem s = .error bareKeyError) ∧
    ((M.view s).iter = .ok [] → (M.view s).tail = some e → M.popitem s = .error e) ∧
    ((M.view s).iter = .ok (key :: rest) → (M.view s).getitem key = .error e → M.popitem s = .error e) ∧
    ((M.view s).iter = .ok (key :: rest) → (M.view s).getitem key = .ok v → M.delitem s key = .error e →
      M.popitem s = .error e) ∧
    ((M.view s).iter = .ok (key :: rest) → (M.view s).getitem key = .ok v → M.delitem s key = .ok s' →
      M.popitem s = .ok ((key, v), s')) ∧
    -- `update` from a `Mapping`
    (o.iter = .error e → M.update s (.mapping o) kw = .error e) ∧
    (o.iter = .ok (key :: rest) → o.getitem key = .error e → M.update s (.mapping o) kw = .error e) ∧
    (o.iter = .ok (key :: rest) → o.getitem key = .ok v → M.setitem s key v = .error e →
      M.update s (.mapping o) kw = .error e) ∧
    (o.iter = .ok (key :: rest) → o.getitem key = .ok v → M.setitem s key v = .ok s' →
      M.update s (.mapping o) kw = M.update s' (.mapping { o with iter := .ok rest }) kw) ∧
    (o.iter = .ok [] → o.tail = some e → M.update s (.mapping o) kw = .error e) ∧
    (o.iter = .ok [] → o.tail = none → M.update s (.mapping o) kw = M.setAll s kw) ∧
    -- `update` from anything else
    (hk = .error e → M.update s (.other hk ks kt gi xs t) kw = .error e) ∧
    M.update s (.other (.ok true) (.error e) kt gi xs t) kw = .error e ∧
    (gi key = .error e → M.update s (.other (.ok true) (.ok (key :: rest)) kt gi xs t) kw = .error e) ∧
    (gi key = .ok v → M.setitem s key v = .ok s' →
      M.update s (.other (.ok true) (.ok (key :: rest)) kt gi xs t) kw =
        M.update s' (.other (.ok true) (.ok rest) kt gi xs t) kw) ∧
    M.update s (.other (.ok true) (.ok []) (some e) gi xs t) kw = .error e ∧
    M.update s (.other (.ok false) ks kt gi (.error e) t) kw = .error e ∧
    (unpack2 x = .error e → M.update s (.other (.ok false) ks kt gi (.ok (x :: ys)) t) kw = .error e) ∧
    (unpack2 x = .ok (key, v) → M.setitem s key v = .error e →
      M.update s (.other (.ok false) ks kt gi (.ok (x :: ys)) t) kw = .error e) ∧
    (unpack2 x = .ok (key, v) → M.setitem s key v = .ok s' →
      M.update s (.other (.ok false) ks kt gi (.ok (x :: ys)) t) kw =
        M.update s' (.other (.ok false) ks kt gi (.ok ys) t) kw) ∧
    M.update s (.other (.ok false) ks kt gi (.ok []) (some e)) kw = .error e ∧
    M.update s (.other (.ok false) ks kt gi (.ok []) none) kw = M.setAll s kw ∧
    -- the keywords
    (M.setitem s key v = .error e → M.setAll s ((key, v) :: kw) = .error e) ∧
    (M.setitem s key v = .ok s' → M.setAll s ((key, v) :: kw) = M.setAll s' kw)

theorem mMapPaths_proven : MMapPaths := by
  intro σ K V M s s' key d v e rest kw o hk ks kt t gi xs x ys
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro h; simp [MMap.pop, MMap.setdefault, h]
  · intro h1 h; simp [MMap.pop, MMap.setdefault, h, h1]
  · intro h1 h; simp [MMap.pop, MMap.setdefault, h, h1]
  · intro h; simp [MMap.popitem, h, bind, Except.bind]
  · intro h h2; simp [MMap.popitem, h, h2, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
  · intro h h2; simp [MMap.popitem, h, h2, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
  · intro h h2; simp [MMap.popitem, h, h2, bind, Except.bind]
  · intro h h2 h3; simp [MMap.popitem, h, h2, h3, bind, Except.bind]
  · intro h h2 h3; simp [MMap.popitem, h, h2, h3, bind, Except.bind, pure, Except.pure]
  · intro h; simp [MMap.update, h, bind, Except.bind]
  · intro h h2; simp [MMap.update, MMap.updateKeys, h, h2, bind, Except.bind]
  · intro h h2 h3; simp [MMap.update, MMap.updateKeys, h, h2, h3, bind, Except.bind]
  · intro h h2 h3; simp [MMap.update, MMap.updateKeys, h, h2, h3, bind, Except.bind]
  · intro h h2; simp [MMap.update, MMap.updateKeys, h, h2, raiseTail, bind, Except.bind]
  · intro h h2; simp [MMap.update, MMap.updateKeys, h, h2, raiseTail, bind, Except.bind]
  · intro h; simp [MMap.update, h, bind, Except.bind]
  · simp [MMap.update, bind, Except.bind]
  · intro h; simp [MMap.update, MMap.updateKeys, h, bind, Except.bind]
  · intro h h2; simp [MMap.update, MMap.updateKeys, h, h2, bind, Except.bind]
  · simp [MMap.update, MMap.updateKeys, raiseTail, bind, Except.bind]
  · simp [MMap.update, bind, Except.bind]
  · intro h; simp [MMap.update, MMap.setPairs, h, bind, Except.bind]
  · intro h h2; simp [MMap.update, MMap.setPairs, h, h2, bind, Except.bind]
  · intro h h2; simp [MMap.update, MMap.setPairs, h, h2, bind, Except.bind]
  · simp [MMap.update, MMap.setPairs, raiseTail, bind, Except.bind]
  · simp [MMap.update, MMap.setPairs, raiseTail, bind, Except.bind]
  · intro h; simp [MMap.setAll, h, bind, Except.bind]
  · intro h; simp [MMap.setAll, h, bind, Except.bind]

/-- `clear` is `popitem` until `KeyError`: that ends it, in the state it reached, and anything else propagates. -/
def MMapClear : Prop :=
  ∀ (σ K V : Type) (M : MMap σ K V) (fuel : Nat) (s s' : σ) (p : K × V) (e : PyExc),
    (isKeyError e = true → M.popitem s = .error e → M.clear (fuel + 1) s = .ok s) ∧
    (isKeyError e = false → M.popitem s = .error e → M.clear (fuel + 1) s = .error e) ∧
    (M.popitem s = .ok (p, s') → M.clear (fuel + 1) s = M.clear fuel s')

theorem mMapClear_proven : MMapClear := by
  intro σ K V M fuel s s' p e
  refine ⟨?_, ?_, ?_⟩
  · intro h1 h; simp [MMap.clear, h, h1]
  · intro h1 h; simp [MMap.clear, h, h1]
  · intro h; simp [MMap.clear, h]

/-! ### `Sequence` -/

/-- `xs` are the items from index `n` on. -/
def Holds {α : Type} (s : Seq α) (n : Int) (xs : List α) : Prop :=
  ∀ (j : Nat) (h : j < xs.length), s.getitem (n + j) = .ok xs[j]

section Seqs
variable {α : Type} (s : Seq α) (E : EqOps α) (value : α)

theorem Holds.tail {n : Int} {x : α} {xs : List α} (h : Holds s n (x :: xs)) : Holds s (n + 1) xs := by
  intro j hj
  have := h (j + 1) (by simpa using hj)
  have e : n + 1 + (j : Int) = n + ((j + 1 : Nat) : Int) := by omega
  rw [e]
  simpa using this

theorem Holds.head {n : Int} {x : α} {xs : List α} (h : Holds s n (x :: xs)) : s.getitem n = .ok x := by
  have := h 0 (by simp)
  simpa using this

theorem iterFrom_end (e : PyExc) (fuel : Nat) : ∀ (xs : List α) (n : Int), Holds s n xs →
    s.getitem (n + xs.length) = .error e → xs.length < fuel →
    s.iterFrom fuel n = if isIndexError e then .ok xs else .error e
  | [], n, _, h2, h3 => by
    cases fuel with
    | zero => simp at h3
    | succ f =>
      have : s.getitem n = .error e := by simpa using h2
      simp only [Seq.iterFrom, this]
  | x :: xs, n, h1, h2, h3 => by
    cases fuel with
    | zero => simp at h3
    | succ f =>
      have ih := iterFrom_end e f xs (n + 1) (h1.tail s)
        (by
          have e2 : n + 1 + (xs.length : Int) = n + ((x :: xs).length : Int) := by simp; omega
          rw [e2]; exact h2)
        (by simpa using h3)
      simp only [Seq.iterFrom, h1.head s, ih]
      split <;> simp [bind, Except.bind, pure, Except.pure]

theorem containsFrom_end (e : PyExc) (fuel : Nat) : ∀ (xs : List α) (n : Int), Holds s n xs →
    (∀ x ∈ xs, E.same x value = .ok false) → s.getitem (n + xs.length) = .error e → xs.length < fuel →
    s.containsFrom E value fuel n = if isIndexError e then .ok false else .error e
  | [], n, _, _, h2, h3 => by
    cases fuel with
    | zero => simp at h3
    | succ f =>
      have : s.getitem n = .error e := by simpa using h2
      simp only [Seq.containsFrom, this]
  | x :: xs, n, h1, hf, h2, h3 => by
    cases fuel with
    | zero => simp at h3
    | succ f =>
      have ih := containsFrom_end e f xs (n + 1) (h1.tail s) (fun y hy => hf y (by simp [hy]))
        (by
          have e2 : n + 1 + (xs.length : Int) = n + ((x :: xs).length : Int) := by simp; omega
          rw [e2]; exact h2)
        (by simpa using h3)
      have hx := hf x (by simp)
      simp [Seq.containsFrom, h1.head s, hx, bind, Except.bind, ih]

theorem containsFrom_hit (fuel : Nat) (v : α) (hv : E.same v value = .ok true) : ∀ (xs : List α) (n : Int),
    Holds s n xs → (∀ x ∈ xs, E.same x value = .ok false) → s.getitem (n + xs.length) = .ok v → xs.length < fuel →
    s.containsFrom E value fuel n = .ok true
  | [], n, _, _, h2, h3 => by
    cases fuel with
    | zero => simp at h3
    | succ f =>
      have : s.getitem n = .ok v := by simpa using h2
      simp [Seq.containsFrom, this, hv, bind, Except.bind, pure, Except.pure]
  | x :: xs, n, h1, hf, h2, h3 => by
    cases fuel with
    | zero => simp at h3
    | succ f =>
      have ih := containsFrom_hit f v hv xs (n + 1) (h1.tail s) (fun y hy => hf y (by simp [hy]))
        (by
          have e2 : n + 1 + (xs.length : Int) = n + ((x :: xs).length : Int) := by simp; omega
          rw [e2]; exact h2)
        (by simpa using h3)
      have hx := hf x (by simp)
      simp [Seq.containsFrom, h1.head s, hx, bind, Except.bind, ih]

theorem indexLoop_end (e : PyExc) (fuel : Nat) : ∀ (xs : List α) (n : Int), Holds s n xs →
    (∀ x ∈ xs, E.same x value = .ok false) → s.getitem (n + xs.length) = .error e → xs.length < fuel →
    s.indexLoop E value none fuel n = if isIndexError e then .error (.valueError "") else .error e
  | [], n, _, _, h2, h3 => by
    cases fuel with
    | zero => simp at h3
    | succ f =>
      have : s.getitem n = .error e := by simpa using h2
      simp only [Seq.indexLoop, Option.isNone_none, true_or, ↓reduceIte, this]
  | x :: xs, n, h1, hf, h2, h3 => by
    cases fuel with
    | zero => simp at h3
    | succ f =>
      have ih := indexLoop_end e f xs (n + 1) (h1.tail s) (fun y hy => hf y (by simp [hy]))
        (by
          have e2 : n + 1 + (xs.length : Int) = n + ((x :: xs).length : Int) := by simp; omega
          rw [e2]; exact h2)
        (by simpa using h3)
      have hx := hf x (by simp)
      simp [Seq.indexLoop, h1.head s, hx, bind, Except.bind, ih]

theorem indexLoop_hit (fuel : Nat) (v : α) (hv : E.same v value = .ok true) : ∀ (xs : List α) (n : Int),
    Holds s n xs → (∀ x ∈ xs, E.same x value = .ok false) → s.getitem (n + xs.length) = .ok v → xs.length < fuel →
    s.indexLoop E value none fuel n = .ok (n + xs.length)
  | [], n, _, _, h2, h3 => by
    cases fuel with
    | zero => simp at h3
    | succ f =>
      have : s.getitem n = .ok v := by simpa using h2
      simp [Seq.indexLoop, this, hv, bind, Except.bind, pure, Except.pure]
  | x :: xs, n, h1, hf, h2, h3 => by
    cases fuel with
    | zero => simp at h3
    | succ f =>
      have e2 : n + 1 + (xs.length : Int) = n + ((x :: xs).length : Int) := by simp; omega
      have ih := indexLoop_hit f v hv xs (n + 1) (h1.tail s) (fun y hy => hf y (by simp [hy]))
        (by rw [e2]; exact h2) (by simpa using h3)
      have hx := hf x (by simp)
      simp only [Seq.indexLoop, Option.isNone_none, true_or, ↓reduceIte, h1.head s]
      simp [hx, bind, Except.bind, ih, e2]

end Seqs

section Seqs2
variable {α : Type} (s : Seq α) (E : EqOps α) (value : α)

theorem countFrom_end (p : α → Bool) (e : PyExc) (fuel : Nat) : ∀ (xs : List α) (n : Int), Holds s n xs →
    (∀ x ∈ xs, E.same x value = .ok (p x)) → s.getitem (n + xs.length) = .error e → xs.length < fuel →
    s.countFrom E value fuel n = if isIndexError e then .ok (xs.filter p).length else .error e
  | [], n, _, _, h2, h3 => by
    cases fuel with
    | zero => simp at h3
    | succ f =>
      have : s.getitem n = .error e := by simpa using h2
      simp only [Seq.countFrom, this]
      split <;> simp
  | x :: xs, n, h1, hf, h2, h3 => by
    cases fuel with
    | zero => simp at h3
    | succ f =>
      have ih := countFrom_end p e f xs (n + 1) (h1.tail s) (fun y hy => hf y (by simp [hy]))
        (by
          have e2 : n + 1 + (xs.length : Int) = n + ((x :: xs).length : Int) := by simp; omega
          rw [e2]; exact h2)
        (by simpa using h3)
      have hx := hf x (by simp)
      simp only [Seq.countFrom, h1.head s, hx, ih, bind, Except.bind]
      by_cases c : isIndexError e
      · cases hp : p x <;> simp [c, hp, pure, Except.pure] <;> (try omega)
      · simp [c]

theorem reversedFrom_ok : ∀ (n : Nat) (ys : List α), ys.length = n →
    (∀ (j : Nat) (h : j < ys.length), s.getitem ((n - 1 - j : Nat) : Int) = .ok ys[j]) →
    s.reversedFrom n = .ok ys
  | 0, [], _, _ => rfl
  | 0, _ :: _, h, _ => by simp at h
  | n + 1, [], h, _ => by simp at h
  | n + 1, y :: ys, hl, h => by
    have h0 := h 0 (by simp)
    simp only [Nat.add_sub_cancel, Nat.sub_zero, List.getElem_cons_zero] at h0
    have ih := reversedFrom_ok n ys (by simpa using hl) (fun j hj => by
      have := h (j + 1) (by simp; omega)
      have e : n + 1 - 1 - (j + 1) = n - 1 - j := by omega
      rw [e] at this
      simpa using this)
    simp only [Seq.reversedFrom, h0, ih, bind, Except.bind, pure, Except.pure]

theorem reversedFrom_err (e : PyExc) : ∀ (n j : Nat), j < n →
    (∀ i < j, ∃ v, s.getitem ((n - 1 - i : Nat) : Int) = .ok v) →
    s.getitem ((n - 1 - j : Nat) : Int) = .error e → s.reversedFrom n = .error e
  | 0, j, hj, _, _ => absurd hj (by omega)
  | n + 1, 0, _, _, h => by
    simp only [Nat.add_sub_cancel, Nat.sub_zero] at h
    simp [Seq.reversedFrom, h, bind, Except.bind]
  | n + 1, j + 1, hj, hp, h => by
    obtain ⟨v, hv⟩ := hp 0 (by omega)
    simp only [Nat.add_sub_cancel, Nat.sub_zero] at hv
    have ih := reversedFrom_err e n j (by omega)
      (fun i hi => by
        obtain ⟨w, hw⟩ := hp (i + 1) (by omega)
        have e2 : n + 1 - 1 - (i + 1) = n - 1 - i := by omega
        rw [e2] at hw
        exact ⟨w, hw⟩)
      (by
        have e2 : n + 1 - 1 - (j + 1) = n - 1 - j := by omega
        rw [e2] at h
        exact h)
    simp [Seq.reversedFrom, hv, ih, bind, Except.bind]

end Seqs2

/-- The `Sequence` mixins over any `__getitem__` and `__len__`. With the items before index `n` as `xs`: `__iter__`,
`__contains__`, `count` and the loop of `index` treat `IndexError` as the end, and only that; another exception from
`self[n]` reaches the caller, where catching everything would give `xs`, `False`, a count or `ValueError`. The first
comparison that says yes ends the search, and a raising `__eq__` is the outcome. `index` starts at any `start`, calls
`len(self)` only for a negative bound, whose failure is then the outcome, and stops at `stop` without reading it.
`__reversed__` calls `len(self)` and then reads from the end down, catching nothing, so the first `self[i]` that
raises, `IndexError` included, is the outcome. Lib/_collections_abc.py:1016-1061. -/
def SeqPaths : Prop :=
  ∀ (α : Type) (s : Seq α) (E : EqOps α) (value v : α) (xs : List α) (e : PyExc) (fuel : Nat) (k : Int)
    (p : α → Bool),
    xs.length < fuel →
    (Holds s 0 xs → s.getitem xs.length = .error e →
      s.iterFrom fuel 0 = (if isIndexError e then .ok xs else .error e) ∧
      ((∀ x ∈ xs, E.same x value = .ok (p x)) →
        s.countFrom E value fuel 0 = (if isIndexError e then .ok (xs.filter p).length else .error e)) ∧
      ((∀ x ∈ xs, E.same x value = .ok false) →
        s.containsFrom E value fuel 0 = (if isIndexError e then .ok false else .error e))) ∧
    (Holds s 0 xs → s.getitem xs.length = .ok v → E.same v value = .ok true → (∀ x ∈ xs, E.same x value = .ok false) →
      s.containsFrom E value fuel 0 = .ok true) ∧
    (s.getitem 0 = .ok v → E.same v value = .error e →
      s.countFrom E value fuel 0 = .error e ∧ s.containsFrom E value fuel 0 = .error e) ∧
    (Holds s k xs → (∀ x ∈ xs, E.same x value = .ok false) → s.getitem (k + xs.length) = .error e →
      s.indexLoop E value none fuel k = (if isIndexError e then .error (.valueError "") else .error e)) ∧
    (Holds s k xs → (∀ x ∈ xs, E.same x value = .ok false) → s.getitem (k + xs.length) = .ok v →
      E.same v value = .ok true → s.indexLoop E value none fuel k = .ok (k + xs.length)) ∧
    (0 ≤ k → s.index E value k none fuel = s.indexLoop E value none fuel k) ∧
    (k < 0 → s.len = .error e → ∀ stop, s.index E value k stop fuel = .error e) ∧
    (0 ≤ k → ∀ t, t < 0 → s.len = .error e → s.index E value k (some t) fuel = .error e) ∧
    (∀ t, t ≤ k → s.indexLoop E value (some t) fuel k = .error (.valueError "")) ∧
    (s.len = .error e → s.reversed = .error e) ∧
    (∀ ys : List α, s.len = .ok ys.length →
      (∀ (j : Nat) (h : j < ys.length), s.getitem ((ys.length - 1 - j : Nat) : Int) = .ok ys[j]) →
      s.reversed = .ok ys) ∧
    (∀ n j : Nat, s.len = .ok n → j < n → (∀ i < j, ∃ w, s.getitem ((n - 1 - i : Nat) : Int) = .ok w) →
      s.getitem ((n - 1 - j : Nat) : Int) = .error e → s.reversed = .error e)

theorem seqPaths_proven : SeqPaths := by
  intro α s E value v xs e fuel k p hl
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h h2
    have h2' : s.getitem (0 + xs.length) = .error e := by simpa using h2
    refine ⟨iterFrom_end s e _ xs 0 h h2' hl, ?_, ?_⟩
    · intro hf
      exact countFrom_end s E value p e _ xs 0 h hf h2' hl
    · intro hf
      exact containsFrom_end s E value e _ xs 0 h hf h2' hl
  · intro h h2 hv hf
    have h2' : s.getitem (0 + xs.length) = .ok v := by simpa using h2
    exact containsFrom_hit s E value _ v hv xs 0 h hf h2' hl
  · intro h1 h2
    exact ⟨by simp [Seq.countFrom, h1, h2, bind, Except.bind], by simp [Seq.containsFrom, h1, h2, bind, Except.bind]⟩
  · intro h hf h2
    exact indexLoop_end s E value e _ xs k h hf h2 hl
  · intro h hf h2 hv
    exact indexLoop_hit s E value _ v hv xs k h hf h2 hl
  · intro hk
    have : ¬ k < 0 := by omega
    simp [Seq.index, this, pure, Except.pure, bind, Except.bind]
  · intro hk h stop
    simp [Seq.index, hk, h, bind, Except.bind]
  · intro hk t ht h
    have : ¬ k < 0 := by omega
    simp [Seq.index, this, ht, h, bind, Except.bind, pure, Except.pure]
  · intro t ht
    have : ¬ k < t := by omega
    simp [Seq.indexLoop, this]
  · intro h
    simp [Seq.reversed, h, bind, Except.bind]
  · intro ys h1 h2
    simp only [Seq.reversed, h1, bind, Except.bind]
    exact reversedFrom_ok s ys.length ys rfl h2
  · intro n j h1 hj hp h2
    simp only [Seq.reversed, h1, bind, Except.bind]
    exact reversedFrom_err s e n j hj hp h2

/-- `MutableSequence`'s mixins over any primitives. `clear` is `pop` until `IndexError`, in the state it reached, and
anything else propagates. `append` is `insert` at `len(self)`. `pop` reads `self[index]` and only then deletes it.
`extend` appends each item of the iterator in order, a failing `append` or iterator being the outcome; `extend(self)`
first builds `list(self)`, whose length hint calls `len(self)`: an exception other than `TypeError` from it is the
outcome before any item is read, a `TypeError` falls back to the hint 8, and a hint the allocator refuses is
`MemoryError`. A failing `index` means nothing is deleted. `reverse` calls `len(self)` and a failing first swap is the
outcome. `__iadd__` is whatever `extend` the class has, then `self`. Lib/_collections_abc.py:1127-1169. -/
def MSeqPaths : Prop :=
  ∀ (σ α : Type) (M : MSeq σ α) (E : EqOps α) (alloc : Nat → Bool) (fuel n : Nat) (s s' : σ) (v : α) (p : α × σ)
    (vs : List α) (e : PyExc) (i : Int) (t : Option PyExc),
    (isIndexError e = true → M.pop s = .error e → M.clear (fuel + 1) s = .ok s) ∧
    (isIndexError e = false → M.pop s = .error e → M.clear (fuel + 1) s = .error e) ∧
    (M.pop s = .ok p → M.clear (fuel + 1) s = M.clear fuel p.2) ∧
    (M.len s = .error e → M.append s v = .error e) ∧
    (M.len s = .ok n → M.append s v = M.insert s n v) ∧
    (M.getitem s i = .error e → M.pop s i = .error e) ∧
    (M.getitem s i = .ok v → M.delitem s i = .error e → M.pop s i = .error e) ∧
    (M.getitem s i = .ok v → M.delitem s i = .ok s' → M.pop s i = .ok (v, s')) ∧
    M.extend alloc s (.iter (.error e) t) fuel = .error e ∧
    (M.append s v = .error e → M.extend alloc s (.iter (.ok (v :: vs)) t) fuel = .error e) ∧
    (M.append s v = .ok s' →
      M.extend alloc s (.iter (.ok (v :: vs)) t) fuel = M.extend alloc s' (.iter (.ok vs) t) fuel) ∧
    M.extend alloc s (.iter (.ok []) (some e)) fuel = .error e ∧
    M.extend alloc s (.iter (.ok []) none) fuel = .ok s ∧
    (M.len s = .error e → isTypeError e = false → M.extend alloc s .self_ fuel = .error e) ∧
    (M.len s = .error e → isTypeError e = true → alloc 8 = true →
      M.extend alloc s .self_ fuel = ((M.view s).iterFrom fuel 0 >>= M.extendList none s)) ∧
    (M.len s = .ok n → n ≠ 0 → alloc n = false → M.extend alloc s .self_ fuel = .error (.named "MemoryError" "")) ∧
    (M.len s = .ok n → (n = 0 ∨ alloc n = true) → (M.view s).iterFrom fuel 0 = .error e →
      M.extend alloc s .self_ fuel = .error e) ∧
    (M.len s = .ok n → (n = 0 ∨ alloc n = true) → (M.view s).iterFrom fuel 0 = .ok vs →
      M.extend alloc s .self_ fuel = M.extendList none s vs) ∧
    ((M.view s).index E v 0 none fuel = .error e → M.remove E s v fuel = .error e) ∧
    ((M.view s).index E v 0 none fuel = .ok i → M.remove E s v fuel = M.delitem s i) ∧
    (M.len s = .error e → M.reverse s = .error e) ∧
    (M.len s = .ok n → 2 ≤ n → M.swap n s 0 = .error e → M.reverse s = .error e) ∧
    (∀ (β : Type) (ext : σ → β → Py σ) (x : β), MSeq.iadd ext s x = ext s x)

theorem mSeqPaths_proven : MSeqPaths := by
  intro σ α M E alloc fuel n s s' v p vs e i t
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h1 h; simp [MSeq.clear, h, h1]
  · intro h1 h; simp [MSeq.clear, h, h1]
  · intro h; obtain ⟨a, b⟩ := p; simp [MSeq.clear, h]
  · intro h; simp [MSeq.append, h, bind, Except.bind]
  · intro h; simp [MSeq.append, h, bind, Except.bind]
  · intro h; simp [MSeq.pop, h, bind, Except.bind]
  · intro h1 h2; simp [MSeq.pop, h1, h2, bind, Except.bind]
  · intro h1 h2; simp [MSeq.pop, h1, h2, bind, Except.bind, pure, Except.pure]
  · simp [MSeq.extend, bind, Except.bind]
  · intro h; simp [MSeq.extend, MSeq.extendList, h, bind, Except.bind]
  · intro h; simp [MSeq.extend, MSeq.extendList, h, bind, Except.bind]
  · simp [MSeq.extend, MSeq.extendList, raiseTail, bind, Except.bind]
  · simp [MSeq.extend, MSeq.extendList, raiseTail, bind, Except.bind]
  · intro h1 h2
    simp [MSeq.extend, h1, h2, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
  · intro h1 h2 h3
    simp [MSeq.extend, h1, h2, h3, bind, Except.bind, pure, Except.pure]
  · intro h1 h2 h3
    simp [MSeq.extend, h1, h2, h3, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw]
  · intro h1 h2 h3
    have hc : ¬ (n ≠ 0 ∧ alloc n = false) := by
      rintro ⟨a, b⟩
      rcases h2 with c | c
      · exact a c
      · rw [c] at b; cases b
    simp [MSeq.extend, h1, hc, h3, bind, Except.bind, pure, Except.pure]
  · intro h1 h2 h3
    have hc : ¬ (n ≠ 0 ∧ alloc n = false) := by
      rintro ⟨a, b⟩
      rcases h2 with c | c
      · exact a c
      · rw [c] at b; cases b
    simp [MSeq.extend, h1, hc, h3, bind, Except.bind, pure, Except.pure]
  · intro h; simp [MSeq.remove, h, bind, Except.bind]
  · intro h; simp [MSeq.remove, h, bind, Except.bind]
  · intro h; simp [MSeq.reverse, h, bind, Except.bind]
  · intro h1 h2 h3
    obtain ⟨k, hk⟩ : ∃ k, n / 2 = k + 1 := ⟨n / 2 - 1, by omega⟩
    simp [MSeq.reverse, h1, hk, MSeq.swapLoop, h3, bind, Except.bind]
  · intro β ext x
    simp [MSeq.iadd]

/-! ### The order of `reverse` -/

/-- The value at `j` of a sequence whose item at each index is the index itself, after the writes in `log`, newest
first. -/
def valAt (log : List (Int × Int)) (j : Int) : Int := (log.lookup j).getD j

/-- A sequence of length `n` that records its writes: its item at each index is that index until written, and the
state is the list of writes, newest first. -/
def traceMSeq (n : Nat) : MSeq (List (Int × Int)) Int where
  getitem s i := .ok (valAt s i)
  setitem s i v := .ok ((i, v) :: s)
  delitem s _ := .ok s
  insert s _ _ := .ok s
  len _ := .ok n

/-- The writes of the first `i` swaps of `reverse` on `n` items, newest first: `self[k]` gets the old `self[n-k-1]`,
then `self[n-k-1]` gets the old `self[k]`. -/
def revWrites (n : Nat) : Nat → List (Int × Int)
  | 0 => []
  | i + 1 => ((n : Int) - i - 1, (i : Int)) :: ((i : Int), (n : Int) - i - 1) :: revWrites n i

theorem revWrites_lookup (n : Nat) : ∀ (i : Nat) (j : Int), (i : Int) ≤ j → j < (n : Int) - i →
    (revWrites n i).lookup j = none
  | 0, _, _, _ => rfl
  | i + 1, j, h1, h2 => by
    have a : (j == (n : Int) - i - 1) = false := by simp; omega
    have b : (j == (i : Int)) = false := by simp; omega
    simp only [revWrites, List.lookup, a, b]
    exact revWrites_lookup n i j (by omega) (by omega)

theorem swapLoop_trace (n : Nat) : ∀ (k i : Nat), i + k = n / 2 →
    (traceMSeq n).swapLoop n k i (revWrites n i) = .ok (revWrites n (n / 2))
  | 0, i, h => by simp only [MSeq.swapLoop]; rw [show i = n / 2 by omega]
  | k + 1, i, h => by
    have l1 := revWrites_lookup n i ((n : Int) - i - 1) (by omega) (by omega)
    have l2 := revWrites_lookup n i (i : Int) (by omega) (by omega)
    have hs : (traceMSeq n).swap n (revWrites n i) i = .ok (revWrites n (i + 1)) := by
      simp [MSeq.swap, traceMSeq, valAt, l1, l2, revWrites, bind, Except.bind]
    simp only [MSeq.swapLoop, hs, bind, Except.bind]
    exact swapLoop_trace n k (i + 1) (by omega)

/-- `MutableSequence.reverse` makes exactly these writes, in this order, for every length: for `i` from 0 up to
`n // 2`, `self[i]` gets the old `self[n-i-1]` and then `self[n-i-1]` gets the old `self[i]`, both read before either
write (the tuple assignment of Lib/_collections_abc.py:1143). Pinned on a sequence that records its writes, so any
other algorithm, order or index, and a sequential swap that loses `self[i]`, differ from it. -/
def MSeqReverseOrder : Prop :=
  ∀ n : Nat, (traceMSeq n).reverse [] = .ok (revWrites n (n / 2))

theorem mSeqReverseOrder_proven : MSeqReverseOrder := by
  intro n
  simp only [MSeq.reverse, traceMSeq, bind, Except.bind]
  exact swapLoop_trace n (n / 2) 0 (by omega)

end PyLean.CoreLibs.CollAbc
