import PyLean.Datetime.ZoneProps
import PyLean.Datetime.ZoneCacheErr

/-!
# The `ZoneInfo` caches with fallible keys and subclasses: twin properties (CPython 3.15.2)
-/

namespace PyLean.Datetime.Zone

open PyLean

/-! ### Counterexample keys -/

def rtErr : PyExc := .named "RuntimeError" "eq"

/-- `str` subclass keys whose `__eq__` raises: distinct hashes. -/
def raisingKeys : KeyOps Nat := ⟨fun k => .ok k, fun _ _ => .error rtErr, fun _ => true⟩

/-- The same, all with one hash value. -/
def sameHashKeys : KeyOps Nat := ⟨fun _ => .ok 0, fun _ _ => .error rtErr, fun _ => true⟩

/-- Keys compared by identity, as plain `object`s are. -/
def idKeys : KeyOps Nat := ⟨fun k => .ok k, fun a b => .ok (decide (a = b)), fun _ => true⟩

def freshSub : ZCls Nat := ⟨false, [], some [], [], 0, []⟩

/-! ### Base class, keys whose comparison raises -/

/-- `ZoneInfo(key)` and `clear_cache` give the same outcomes in both twins for every run on
the base class, whatever the keys' `__hash__` and `__eq__` do. -/
def CacheErrTwins : Prop :=
  ∀ (K : Type) [DecidableEq K] (o : KeyOps K) (ops : List (ZOp K)),
    ops.all (fun op => !op.isDel) = true →
    (runErrC o freshBase ops).2 = (runErrPy o freshBase ops).2

/-- `ZoneInfo(0)`, then `clear_cache(only_keys=[1])` and `ZoneInfo(1)` with a key `1` whose
`__eq__` raises: C compares it with the cached node `0` (`find_in_strong_cache`, `rv < 0`) and
raises in both calls; Python's dict lookups never compare keys of different hash, so both
calls succeed. -/
theorem cacheErrTwins_refuted : ¬ CacheErrTwins := by
  intro h
  have := h Nat raisingKeys [.get 0, .clearKeys [1] none, .get 1] rfl
  revert this
  decide

/-! ### Subclasses -/

/-- For a subclass, `Sub(key)`, `clear_cache` and collections give the same outcomes in both
twins, whatever the keys do (`del Sub._weak_cache` excluded). -/
def CacheErrTwinsSub : Prop :=
  ∀ (K : Type) [DecidableEq K] (o : KeyOps K) (ops : List (ZOp K)) (sp sc : ZCls K),
    initSubclassErrPy [] (some (.ok ())) [] = .ok sp →
    initSubclassErrC [] (.ok (some (.ok ()))) [] = .ok sc →
    ops.all (fun op => !op.isDel) = true →
    (runErrC o sc ops).2 = (runErrPy o sp ops).2

/-- `Sub(0)`, the instance collected once unreferenced, then `Sub.clear_cache(only_keys=[1])`
with a key `1` of the same hash whose `__eq__` raises: Python's subclass strong cache kept the
instance, so its weak cache still has key `0` and `pop` compares and raises; C's subclass has
no strong cache (`eject_from_strong_cache` returns 0 at :2463-2465), the weak entry is gone,
and the call succeeds. -/
theorem cacheErrTwinsSub_refuted : ¬ CacheErrTwinsSub := by
  intro h
  have := h Nat sameHashKeys [.get 0, .drop 0, .clearKeys [1] none] freshSub freshSub rfl rfl rfl
  revert this
  decide

/-- The twins keep the same zones alive through a subclass's strong cache: after the class
statement (`__init_subclass__`, through `new_weak_cache`), every run of `Sub(key)` calls leaves
the same keys there. -/
def CacheTwinsSubclass : Prop :=
  ∀ (K : Type) [DecidableEq K] (o : KeyOps K) (bound : WvdAttr) (ks : List K) (sp sc : ZCls K),
    initSubclassErrPy [] bound [] = .ok sp → initSubclassErrC [] (.ok bound) [] = .ok sc →
    (runErrC o sc (ks.map .get)).1.strong = (runErrPy o sp (ks.map .get)).1.strong.reverse

/-- One `Sub(0)`: Python's subclass keeps the zone in its own strong cache, C keeps none. -/
theorem cacheTwinsSubclass_refuted : ¬ CacheTwinsSubclass := by
  intro h
  have := h Nat idKeys (some (.ok ())) [0] freshSub freshSub rfl rfl
  revert this
  decide

/-- `Sub(key)` behaves the same in both twins on every run, `del Sub._weak_cache` included
(C `get_weak_cache` vs Python's `cls._weak_cache`). -/
def WeakCacheAttrTwins : Prop :=
  ∀ (K : Type) [DecidableEq K] (o : KeyOps K) (ops : List (ZOp K)),
    (runErrC o ⟨false, [], some [], [], 0, []⟩ ops).2 = (runErrPy o ⟨false, [], some [], [], 0, []⟩ ops).2

/-- `del Sub._weak_cache; Sub(0)`: C's `PyObject_GetAttrString(type, "_weak_cache")`
(:299-301) raises `AttributeError`, Python's `cls._weak_cache` finds `ZoneInfo._weak_cache`
and returns a zone. -/
theorem weakCacheAttrTwins_refuted : ¬ WeakCacheAttrTwins := by
  intro h
  have := h Nat idKeys [.delWeak, .get 0]
  revert this
  decide

/-! ### Subclass creation -/

/-- With `sys.modules["weakref"]` the module `_zoneinfo.py` imported, the class statement
`class S(ZoneInfo, **kw)` succeeds or fails alike in both twins. -/
def InitSubclassTwins : Prop :=
  ∀ (kw : List String) (bound : WvdAttr),
    (initSubclassErrC kw (.ok bound) [] : Py (ZCls Nat)) = initSubclassErrPy kw bound []

/-- `class S(ZoneInfo, foo=1)`: C ignores the keyword (`METH_VARARGS | METH_KEYWORDS`),
Python's `__init_subclass__(cls)` raises `TypeError`. -/
theorem initSubclassTwins_refuted : ¬ InitSubclassTwins := by
  intro h
  have := h ["foo"] (some (.ok ()))
  revert this
  decide

/-- Without class keywords, the twins create a subclass alike whatever `sys.modules["weakref"]`
is at that point. -/
def InitSubclassWeakref : Prop :=
  ∀ (imported : Py WvdAttr) (bound : WvdAttr),
    (initSubclassErrC [] imported [] : Py (ZCls Nat)) = initSubclassErrPy [] bound []

/-- `sys.modules["weakref"]` replaced by a module without `WeakValueDictionary`: C's
`new_weak_cache` imports it and raises `AttributeError`; Python uses the `weakref` it bound
at import. -/
theorem initSubclassWeakref_refuted : ¬ InitSubclassWeakref := by
  intro h
  have := h (.ok none) (some (.ok ()))
  revert this
  decide

/-- Without class keywords and with `sys.modules["weakref"]` the module `_zoneinfo.py`
imported, both twins read `WeakValueDictionary` from it and call it: the same outcome for a
missing attribute, a raising call, and success. -/
def InitSubclassSameModule : Prop :=
  ∀ (K : Type) (bound : WvdAttr) (bw : List (K × Inst K)),
    initSubclassErrC [] (.ok bound) bw = initSubclassErrPy [] bound bw

theorem initSubclassSameModule_proven : InitSubclassSameModule := by
  intro K bound bw
  rcases bound with _ | (e | ⟨⟩) <;> rfl

end PyLean.Datetime.Zone

namespace PyLean.Datetime.Zone

/-- `Sub(key)` behaves the same in both twins on every run that does not delete
`Sub._weak_cache` (replacing it included). -/
def WeakCacheTypeTwins : Prop :=
  ∀ (K : Type) [DecidableEq K] (o : KeyOps K) (ops : List (ZOp K)),
    ops.all (fun op => match op with | .delWeak => false | _ => true) = true →
    (runErrC o ⟨false, [], some [], [], 0, []⟩ ops).2 = (runErrPy o ⟨false, [], some [], [], 0, []⟩ ops).2

/-- `Sub._weak_cache = {0: obj}` with `obj` not a `ZoneInfo`, then `Sub(0)`: C's
`PyObject_TypeCheck` (Modules/_zoneinfo.c:352-358) raises `RuntimeError`, Python returns
`obj`. -/
theorem weakCacheTypeTwins_refuted : ¬ WeakCacheTypeTwins := by
  intro h
  have := h Nat idKeys [.setWeak [(0, (0, 0))], .get 0] rfl
  revert this
  decide

end PyLean.Datetime.Zone

namespace PyLean.Datetime.Zone

/-- Key `1` is a `str` subclass with `__hash__ = None` equal to the plain key `0`. -/
def unhashableKeys : KeyOps Nat :=
  ⟨fun k => if k = 1 then .error (.typeError "~unhashable type") else .ok 0,
   fun _ _ => .ok true, fun _ => true⟩

/-- A second counterexample to `CacheErrTwins`: `ZoneInfo(0)`, then `ZoneInfo(1)` with an
unhashable key equal to `0`: C's strong cache compares without hashing and returns the cached
zone, Python's weak-cache lookup hashes the key and raises `TypeError`. -/
theorem cacheErrTwins_refuted_unhashable : ¬ CacheErrTwins := by
  intro h
  have := h Nat unhashableKeys [.get 0, .get 1] rfl
  revert this
  decide

end PyLean.Datetime.Zone

namespace PyLean.Datetime.Zone

/-- A third counterexample to `CacheErrTwins`: `clear_cache(only_keys=[k])` on empty caches
with an unhashable key `k`: C ejects nothing and calls the weak cache's `dict.pop`, which
returns at once on an empty dict without hashing, so the call succeeds; Python's
`OrderedDict.pop` on the strong cache hashes the key and raises `TypeError`. -/
theorem cacheErrTwins_refuted_empty : ¬ CacheErrTwins := by
  intro h
  have := h Nat unhashableKeys [.clearKeys [1] none] rfl
  revert this
  decide

end PyLean.Datetime.Zone
