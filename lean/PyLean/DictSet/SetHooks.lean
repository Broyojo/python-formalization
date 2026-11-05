import PyLean.DictSet.SetBranches

/-!
The Python code a set calls, on every path: `__hash__` and `__eq__` are world-threaded, may raise,
and may re-enter and change the very set being probed (`Proto.hashM`, `Proto.eq`). These are the
paths of `set_add_key`, `set_contains_key`, `set_discard_key`, `set_unhashable_type`, the restart
loops of `set_add_entry_takeref` and `set_lookkey`, the retries of `_PySet_Contains` and
`frozenset.__contains__`, and the iterator loops of `set_update_iterable_lock_held`,
`set_intersection` and `set_isdisjoint_impl`. Line numbers refer to `Objects/setobject.c` (3.15.2).
-/

namespace PyLean.DictSet

open PyLean

/-! ## Witness protocols, on `Nat` keys -/

/-- Distinct naturals: hash `n`, `==` is equality, no side effects; `%T` prints `K`. -/
def natSetProto : Proto Nat (SetObj Nat) :=
  { hash := fun k => .ok k, isStr := fun _ => false, isStrLike := fun _ => false
    strEq := fun a b => a == b, reprStr := fun _ => "", repr := fun _ => .ok ""
    typeName := fun _ => "K", eq := fun a b s => (.ok (a == b), s) }

/-- The probe of the review: key `0` is a `K` whose `__hash__` does `s.add(99)` and then raises
`TypeError("no")`. -/
def hashAddsProto : Proto Nat (SetObj Nat) :=
  { natSetProto with
    hashM := fun k s =>
      if k = 0 then (.error (.typeError "no"), (setAddKey natSetProto 99 s).2) else (.ok k, s) }

/-- `{1, 2, 3}`. -/
def set123 : SetObj Nat := setProg natSetProto [.add 1, .add 2, .add 3] {}

/-! ## `set_add_key`, `set_contains_key`, `set_discard_key`: the hash -/

/-- The withdrawn claim: a failed hash leaves the set as it was. -/
def SetHashFailureUnchanged : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (key : K) (so : SetObj K) (e : PyExc),
    (P.hashM key so).1 = .error e →
    setAddKey P key so = (.error (setUnhashableType P key e), so) ∧
    setContainsKey P key so = (.error (setUnhashableType P key e), so) ∧
    setDiscardKey P key so = (.error (setUnhashableType P key e), so)

/-- The review's probe, in the model: `s.add(K())`, `K() in s` and `s.discard(K())` on `{1, 2, 3}`
all raise `set_unhashable_type`'s error for `TypeError("no")`, and leave `99` in the set. -/
theorem hashAdds_probe :
    (setAddKey hashAddsProto 0 set123).1 = .error (setUnhashableType hashAddsProto 0 (.typeError "no")) ∧
    (setContainsKey hashAddsProto 0 set123).1 =
      .error (setUnhashableType hashAddsProto 0 (.typeError "no")) ∧
    (setDiscardKey hashAddsProto 0 set123).1 =
      .error (setUnhashableType hashAddsProto 0 (.typeError "no")) ∧
    setKeys (setAddKey hashAddsProto 0 set123).2 = [99, 1, 2, 3] ∧
    setKeys (setContainsKey hashAddsProto 0 set123).2 = [99, 1, 2, 3] ∧
    setKeys (setDiscardKey hashAddsProto 0 set123).2 = [99, 1, 2, 3] ∧
    setKeys set123 = [1, 2, 3] := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem setHashFailureUnchanged_refuted : ¬SetHashFailureUnchanged := by
  intro h
  have h1 := (h Nat hashAddsProto 0 set123 (.typeError "no") rfl).1
  have h2 := congrArg (fun r => setKeys r.2) h1
  have h3 := hashAdds_probe.2.2.2.1
  have h4 := hashAdds_probe.2.2.2.2.2.2
  simp only at h2
  rw [h3, h4] at h2
  exact absurd h2 (by decide)

/-- `set_add_key` (:600-609), `set_contains_key` (:611-620) and `set_discard_key` (:622-631), for every
key protocol: `_PyObject_HashFast` runs `__hash__` first, as Python code. When it raises `e`, leaving
the state `s'`, each raises `set_unhashable_type`'s exception for `e`, in `s'`: what `__hash__` did
stands. When it answers `h` in `s'`, each goes on to its entry function with `h`, from `s'`. -/
def SetHashFailure : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (key : K) (so s' : SetObj K),
    (∀ e, P.hashM key so = (.error e, s') →
      setAddKey P key so = (.error (setUnhashableType P key e), s') ∧
      setContainsKey P key so = (.error (setUnhashableType P key e), s') ∧
      setDiscardKey P key so = (.error (setUnhashableType P key e), s')) ∧
    (∀ h, P.hashM key so = (.ok h, s') →
      setAddKey P key so = setAddEntry P key h s' ∧
      setContainsKey P key so = setContainsEntry P key h s' ∧
      setDiscardKey P key so = setDiscardEntry P key h s')
theorem setHashFailure_proven : SetHashFailure := by
  intro K _ P key so s'
  refine ⟨fun e he => ?_, fun h he => ?_⟩
  · refine ⟨?_, ?_, ?_⟩ <;>
      simp [setAddKey, setContainsKey, setDiscardKey, setHashKey, M.tryCatch, M.bind_run, he]
  · refine ⟨?_, ?_, ?_⟩ <;>
      simp [setAddKey, setContainsKey, setDiscardKey, setHashKey, M.tryCatch, M.bind_run, he]

/-! ## `set_unhashable_type` -/

/-- `set_unhashable_type` (:345-359), for every key protocol: an exception whose type is exactly
`TypeError` (`Py_IS_TYPE`, :350) becomes `TypeError("cannot use '%T' as a set element (%S)")`, with
the key's type name and the old message; any other exception, a subclass of `TypeError` among them,
is re-raised as it was (:351-352). -/
def SetUnhashableType : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (key : K) (e : PyExc),
    (∀ m, e = .typeError m →
      setUnhashableType P key e = .typeError s!"cannot use '{P.typeName key}' as a set element ({m})") ∧
    ((∀ m, e ≠ .typeError m) → setUnhashableType P key e = e)
theorem setUnhashableType_proven : SetUnhashableType := by
  intro K _ P key e
  refine ⟨fun m hm => by subst hm; rfl, fun h => ?_⟩
  cases e with
  | typeError m => exact absurd rfl (h m)
  | _ => rfl

/-! ## `_PySet_Contains`, `set_contains`, `set.__contains__`, `frozenset.__contains__` -/

/-- `{1}`'s body, and the hash of `frozenset({1})`. -/
def bodyOne : SetBody Nat := (setAddKey natSetProto 1 {}).2.toSetBody
def fsOneHash : Int := frozensetHashImpl ({ toSetBody := bodyOne } : SetObj Nat)

/-- The probe of the review: key `7` is an instance of a `set` subclass holding `{1}` whose
`__hash__` raises `TE`, a subclass of `TypeError`; key `5` is `frozenset({1})`, which equals it. -/
def teSubProto : Proto Nat (SetObj Nat) :=
  { natSetProto with
    hashM := fun k s =>
      if k = 7 then (.error (.named "TE" "te"), s) else if k = 5 then (.ok fsOneHash, s) else (.ok k, s)
    isTypeError := fun e => match e with
      | .typeError _ => true
      | .named _ _ => true
      | _ => false
    eq := fun a b s => (.ok (a == b || (a == 5 && b == 7) || (a == 7 && b == 5)), s) }

/-- `PySet_Check(7)`, and its body. -/
def teKeySet : Nat → SetObj Nat → Option (SetBody Nat) := fun k _ => if k = 7 then some bodyOne else none

/-- `{frozenset({1})}`. -/
def setFsOne : SetObj Nat := (setAddKey teSubProto 5 {}).2

/-- The withdrawn third conjunct of `set-contains-retry`: a failed hash that is not exactly
`TypeError` is never retried. -/
def SetContainsRetryExact : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (keySet : K → SetObj K → Option (SetBody K))
    (key : K) (e : PyExc) (so s' : SetObj K),
    P.hashM key so = (.error e, s') → (∀ m, e ≠ .typeError m) →
    setContains P keySet key so = (.error (setUnhashableType P key e), s')

/-- `x in {frozenset([1])}` is `True` for an `x` of a set subclass holding `{1}` whose `__hash__`
raises a subclass of `TypeError`, by `set` and by `frozenset` alike. -/
theorem teSub_probe :
    (setContains teSubProto teKeySet 7 setFsOne).1 = .ok true ∧
    (frozensetContains teSubProto teKeySet 7 { setFsOne with frozen := true }).1 = .ok true := by
  constructor <;> decide +kernel

theorem setContainsRetryExact_refuted : ¬SetContainsRetryExact := by
  intro h
  have h1 := h Nat teSubProto teKeySet 7 (.named "TE" "te") setFsOne setFsOne rfl (fun m => nofun)
  have h2 := congrArg Prod.fst h1
  rw [teSub_probe.1] at h2
  exact nomatch h2

/-- `_PySet_Contains` (:2544-2564), `set_contains` (:2566-2571), `set.__contains__` (:2584-2593)
and `frozenset.__contains__` (:2606-2626), for every key protocol and every relation saying which
keys are sets: `__hash__` runs first and leaves `s'`.

* It raises `e`. If the key is a `set` (`PySet_Check`) and `e` is a `TypeError` or a subclass
  (`PyErr_ExceptionMatches`), the key is looked up by `frozenset_hash_impl` of its body as it
  stands in `s'` (:2556-2560, :2615-2618), by `set_lookkey` for a set and by one
  `set_compare_frozenset` walk for a frozenset. Otherwise each raises `set_unhashable_type`'s
  exception (:2551-2554, :2611-2614), in `s'`.
* It answers `h`: the lookup with `h`, from `s'`.
* `set_contains` gives `1`, `0` or the exception of `_PySet_Contains`, and `set.__contains__` the
  `bool` or the exception, on every path, in the state `_PySet_Contains` left. -/
def SetContainsRetry : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (keySet : K → SetObj K → Option (SetBody K))
    (key : K) (so s' : SetObj K),
    (∀ e, P.hashM key so = (.error e, s') →
      (∀ b, P.isTypeError e = true → keySet key s' = some b →
        setContains P keySet key so =
          setContainsEntry P key (frozensetHashImpl ({ toSetBody := b } : SetObj K)) s' ∧
        frozensetContains P keySet key so =
          frozenLookup P key (frozensetHashImpl ({ toSetBody := b } : SetObj K)) s') ∧
      ((P.isTypeError e = false ∨ keySet key s' = none) →
        setContains P keySet key so = (.error (setUnhashableType P key e), s') ∧
        frozensetContains P keySet key so = (.error (setUnhashableType P key e), s'))) ∧
    (∀ h, P.hashM key so = (.ok h, s') →
      setContains P keySet key so = setContainsEntry P key h s' ∧
      frozensetContains P keySet key so = frozenLookup P key h s') ∧
    (∀ r s'', setContains P keySet key so = (r, s'') →
      setSqContains P keySet key so =
        (match r with
         | .ok b => .ok (if b then 1 else 0)
         | .error e => .error e, s'') ∧
      setDunderContains P keySet key so = (r, s''))
theorem setContainsRetry_proven : SetContainsRetry := by
  intro K _ P keySet key so s'
  refine ⟨fun e he => ⟨fun b ht hk => ?_, fun hno => ?_⟩, fun h he => ?_, fun r s'' hr => ?_⟩
  · have hr : retryHash P keySet key e s' = some (frozensetHashImpl ({ toSetBody := b } : SetObj K)) := by
      simp [retryHash, keySetHash, ht, hk]
    constructor
    · simp only [setContains, containsHash, M.bind_run, he, hr]
    · simp only [frozensetContains, containsHash, M.bind_run, he, hr]
  · have hr : retryHash P keySet key e s' = none := by
      rcases hno with h1 | h1 <;> simp [retryHash, keySetHash, h1]
    constructor
    · simp only [setContains, containsHash, M.bind_run, he, hr]
    · simp only [frozensetContains, containsHash, M.bind_run, he, hr]
  · constructor
    · simp only [setContains, containsHash, M.bind_run, he]
    · simp only [frozensetContains, containsHash, M.bind_run, he]
  · constructor
    · cases r <;> simp [setSqContains, hr]
    · cases r with
      | error e => simp [setDunderContains, setSqContains, hr]
      | ok b => cases b <;> simp [setDunderContains, setSqContains, hr]

/-! ## `set_lookkey`: the dispatch and the restart -/

section Lookkey
variable {K : Type} [DecidableEq K] (P : Proto K (SetObj K))

theorem lookStep_frozen_ne_restart (key : K) (hash : Int) (slot : Nat) (s : SetObj K) :
    (lookStep P true key hash slot s).1 ≠ .ok (.inl .restart) := by
  simp only [lookStep, if_true, compareFrozen, M.bind_run, M.get_run]
  cases hs : s.slot slot with
  | null => simp [hs]
  | dummy => simp [hs]
  | active k h =>
    by_cases h1 : k = key
    · simp [hs, h1]
    · by_cases h2 : h = hash
      · rcases hq : P.eq k key s with ⟨r, s1⟩
        cases r with
        | error e => simp [hs, h1, h2, M.bind_run, hq]
        | ok b => cases b <;> simp [hs, h1, h2, M.bind_run, hq]
      · simp [hs, h1, h2]

theorem lookScan_frozen_ne_restart (key : K) (hash : Int) :
    ∀ (p slot : Nat) (s : SetObj K), (lookScan P true key hash p slot s).1 ≠ .ok .restart := by
  intro p
  induction p with
  | zero =>
    intro slot s
    have h := lookStep_frozen_ne_restart P key hash slot s
    simp only [lookScan, M.bind_run]
    rcases hq : lookStep P true key hash slot s with ⟨r, s1⟩
    rw [hq] at h
    cases r with
    | error e => simp
    | ok v =>
      cases v with
      | inl r => simpa using h
      | inr _ => simp
  | succ p ih =>
    intro slot s
    have h := lookStep_frozen_ne_restart P key hash slot s
    simp only [lookScan, M.bind_run]
    rcases hq : lookStep P true key hash slot s with ⟨r, s1⟩
    rw [hq] at h
    cases r with
    | error e => simp
    | ok v =>
      cases v with
      | inl r => simpa using h
      | inr _ => exact ih (slot + 1) s1

/-- `set_compare_frozenset` never answers `SET_LOOKKEY_CHANGED`, so the walk of an exact frozenset
ends with a slot, an exception, or the model's fuel, never a restart. -/
theorem lookOuter_frozen_ne_restart (key : K) (hash : Int) (mask : Nat) :
    ∀ (fuel i p : Nat) (s : SetObj K), (lookOuter P true key hash mask fuel i p s).1 ≠ .ok none := by
  intro fuel
  induction fuel with
  | zero => intro i p s; simp [lookOuter]
  | succ fuel ih =>
    intro i p s
    simp only [lookOuter, M.bind_run]
    have h := lookScan_frozen_ne_restart P key hash (linearProbes i mask) i s
    cases hr : lookScan P true key hash (linearProbes i mask) i s with
    | mk r s1 =>
      rw [hr] at h
      cases r with
      | error e => simp
      | ok v =>
        cases v with
        | found x => simp
        | restart => exact absurd rfl h
        | next => exact ih _ _ s1

end Lookkey

/-- `set_lookkey` (:413-433), for every key protocol. `PyFrozenSet_CheckExact(so)` (:417) runs one
`set_do_lookup` with `set_compare_frozenset` (:418-420) on `so->table` and `so->mask`: it never asks
for a restart, and its slot or exception is the answer. Anything else, a frozenset subclass too,
runs `set_compare_entry_lock_held` in the `do ... while (status == SET_LOOKKEY_CHANGED)` (:422-426):
a walk that asks for a restart starts again from the state `__eq__` left, with that state's table and
mask; a slot or an exception ends it. The two compare functions do differ (`FrozenIdentityFirst`):
on the same table an exact frozenset and a set give different slots (`lookkey_dispatch_probe`). -/
def SetLookkeyBody : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (key : K) (hash : Int) (n : Nat)
    (so s' : SetObj K),
    (so.frozenExact = true →
      (lookOuter P true key hash so.mask (setProbeFuel so.mask) (toU64 hash &&& so.mask) (toU64 hash)
        so).1 ≠ .ok none ∧
      (∀ s, lookOuter P true key hash so.mask (setProbeFuel so.mask) (toU64 hash &&& so.mask)
          (toU64 hash) so = (.ok (some s), s') → setLookkey P key hash so = (.ok s, s')) ∧
      (∀ e, lookOuter P true key hash so.mask (setProbeFuel so.mask) (toU64 hash &&& so.mask)
          (toU64 hash) so = (.error e, s') → setLookkey P key hash so = (.error e, s'))) ∧
    (so.frozenExact = false → setLookkey P key hash so = setLookkeyAux P key hash 256 so) ∧
    (lookOuter P false key hash so.mask (setProbeFuel so.mask) (toU64 hash &&& so.mask) (toU64 hash)
        so = (.ok none, s') → setLookkeyAux P key hash (n + 1) so = setLookkeyAux P key hash n s') ∧
    (∀ s, lookOuter P false key hash so.mask (setProbeFuel so.mask) (toU64 hash &&& so.mask)
        (toU64 hash) so = (.ok (some s), s') → setLookkeyAux P key hash (n + 1) so = (.ok s, s')) ∧
    (∀ e, lookOuter P false key hash so.mask (setProbeFuel so.mask) (toU64 hash &&& so.mask)
        (toU64 hash) so = (.error e, s') → setLookkeyAux P key hash (n + 1) so = (.error e, s'))
theorem setLookkeyBody_proven : SetLookkeyBody := by
  intro K _ P key hash n so s'
  refine ⟨fun hf => ⟨lookOuter_frozen_ne_restart P key hash so.mask _ _ _ so, fun s h => ?_,
      fun e h => ?_⟩, fun hf => ?_, fun h => ?_, fun s h => ?_, fun e h => ?_⟩
  · simp [setLookkey, M.bind_run, M.get_run, hf, h]
  · simp [setLookkey, M.bind_run, M.get_run, hf, h]
  · simp [setLookkey, M.bind_run, M.get_run, hf]
  · simp [setLookkeyAux, M.bind_run, M.get_run, h]
  · simp [setLookkeyAux, M.bind_run, M.get_run, h]
  · simp [setLookkeyAux, M.bind_run, M.get_run, h]

/-- The dispatch is observable: key `1` stored with hash `1`, looked up with hash `9` (the same slot
of an 8-slot table, as after `x`'s `__hash__` moved). An exact frozenset finds it at slot 1 by
identity; a set walks past it, and its next block (`(1 * 5 + 1) & 7`) is the NULL at slot 6 (CPython: `x in frozenset({x})` is True,
`x in {x}` is False). -/
theorem lookkey_dispatch_probe :
    (setLookkey natSetProto 1 9 { (setAddKey natSetProto 1 {}).2 with frozen := true }).1 = .ok 1 ∧
    (setLookkey natSetProto 1 9 (setAddKey natSetProto 1 {}).2).1 = .ok 6 := by
  constructor <;> decide +kernel

end PyLean.DictSet
