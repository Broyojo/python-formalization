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

/-- `x in {frozenset([1])}` is `True` for an `x` of a set subclass holding `{1}` whose `__hash__`
raises a subclass of `TypeError`, by `set` and by `frozenset` alike. -/
theorem teSub_probe :
    (setContains teSubProto teKeySet 7 setFsOne).1 = .ok true ∧
    (frozensetContains teSubProto teKeySet 7 { setFsOne with frozen := true }).1 = .ok true := by
  constructor <;> decide +kernel

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
  `bool` or the exception, on every path, in the state `_PySet_Contains` left.

Example (`teSub_probe`, as on 3.15.2): `x in {frozenset([1])}` is `True` for an instance `x` of a set
subclass holding `{1}` whose `__hash__` raises a subclass of `TypeError`. -/
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

/-! ## `set_add_entry_takeref`: the walk and the restart loop -/

/-- `set_add_entry_takeref` (:252-335), for every key protocol, step by step and turn by turn.

The walk of one turn: a step that ends the block (a NULL, `found_active`, `goto restart`, an
exception from `__eq__`) ends the walk with it (:275-297); a step that goes on moves to the next
entry with the mask and `freeslot` it left (:296, :298-302); a finished block moves to the next probe,
`(i * 5 + 1 + perturb) & mask` with the mask as the block left it (:303-305).

What a turn ends with:
* an exception: the result, in the state `__eq__` left (`comparison_error`, :332-334);
* `found_active`: nothing more (:328-330);
* `goto restart` (:294-295): the next turn, from the state `__eq__` left, with its mask and table and
  no `freeslot` (:264-269);
* a NULL and no `freeslot`: the key goes at the NULL, `fill` and `used` grow, and the table grows
  when `fill * 5 >= mask * 3` for the mask of the walk (:319-326);
* a NULL and a `freeslot` that is still a dummy: the key goes in the dummy and `used` grows, not
  `fill` (:314-317);
* a NULL and a `freeslot` that `__eq__` refilled (`freeslot->hash != -1`, :311-313): the next turn.

Scope: the table test of `addStep` names tables by identity (see `setLookkeyAux`). -/
def SetAddRestart : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (key : K) (hash : Int) (so s' : SetObj K),
    (∀ (slot mask p : Nat) (fs : Option Nat) (r : AddScan),
      addStep P key hash slot mask fs so = (.ok (.inl r), s') →
        addScan P key hash p slot mask fs so = (.ok r, s')) ∧
    (∀ (slot mask p m : Nat) (fs fs' : Option Nat),
      addStep P key hash slot mask fs so = (.ok (.inr (m, fs')), s') →
        addScan P key hash (p + 1) slot mask fs so = addScan P key hash p (slot + 1) m fs' s' ∧
        addScan P key hash 0 slot mask fs so = (.ok (.next fs' m), s')) ∧
    (∀ (slot mask p : Nat) (fs : Option Nat) (e : PyExc),
      addStep P key hash slot mask fs so = (.error e, s') →
        addScan P key hash p slot mask fs so = (.error e, s')) ∧
    (∀ (fuel i perturb mask m : Nat) (fs fs' : Option Nat),
      addScan P key hash (linearProbes i mask) i mask fs so = (.ok (.next fs' m), s') →
        addOuter P key hash (fuel + 1) i perturb mask fs so =
          addOuter P key hash fuel (setProbeStep m i perturb).1 (setProbeStep m i perturb).2 m fs' s') ∧
    (∀ (fuel i perturb mask : Nat) (fs : Option Nat) (r : AddScan), (∀ fs' m, r ≠ .next fs' m) →
      addScan P key hash (linearProbes i mask) i mask fs so = (.ok r, s') →
        addOuter P key hash (fuel + 1) i perturb mask fs so = (.ok r, s')) ∧
    (∀ (fuel i perturb mask : Nat) (fs : Option Nat) (e : PyExc),
      addScan P key hash (linearProbes i mask) i mask fs so = (.error e, s') →
        addOuter P key hash (fuel + 1) i perturb mask fs so = (.error e, s')) ∧
    ∀ n : Nat,
      (∀ e, addOuter P key hash (setProbeFuel so.mask) (toU64 hash &&& so.mask) (toU64 hash) so.mask
          none so = (.error e, s') → setAddEntryAux P key hash (n + 1) so = (.error e, s')) ∧
      (addOuter P key hash (setProbeFuel so.mask) (toU64 hash &&& so.mask) (toU64 hash) so.mask
          none so = (.ok .active, s') → setAddEntryAux P key hash (n + 1) so = (.ok (), s')) ∧
      (addOuter P key hash (setProbeFuel so.mask) (toU64 hash &&& so.mask) (toU64 hash) so.mask
          none so = (.ok .restart, s') →
        setAddEntryAux P key hash (n + 1) so = setAddEntryAux P key hash n s') ∧
      (∀ slot m, addOuter P key hash (setProbeFuel so.mask) (toU64 hash &&& so.mask) (toU64 hash)
          so.mask none so = (.ok (.unused slot none m), s') →
        setAddEntryAux P key hash (n + 1) so =
          if (s'.fill + 1) * 5 < m * 3 then
            (.ok (), { s' with fill := s'.fill + 1, used := s'.used + 1,
                               table := s'.table.set slot (.active key hash) })
          else setGrow { s' with fill := s'.fill + 1, used := s'.used + 1,
                                 table := s'.table.set slot (.active key hash) }) ∧
      (∀ slot m f, addOuter P key hash (setProbeFuel so.mask) (toU64 hash &&& so.mask) (toU64 hash)
          so.mask none so = (.ok (.unused slot (some f) m), s') → s'.slot f = .dummy →
        setAddEntryAux P key hash (n + 1) so =
          (.ok (), { s' with used := s'.used + 1, table := s'.table.set f (.active key hash) })) ∧
      (∀ slot m f, addOuter P key hash (setProbeFuel so.mask) (toU64 hash &&& so.mask) (toU64 hash)
          so.mask none so = (.ok (.unused slot (some f) m), s') → s'.slot f ≠ .dummy →
        setAddEntryAux P key hash (n + 1) so = setAddEntryAux P key hash n s')
theorem setAddRestart_proven : SetAddRestart := by
  intro K _ P key hash so s'
  refine ⟨fun slot mask p fs r h => ?_, fun slot mask p m fs fs' h => ?_, fun slot mask p fs e h => ?_,
    fun fuel i perturb mask m fs fs' h => ?_, fun fuel i perturb mask fs r hr h => ?_,
    fun fuel i perturb mask fs e h => ?_, fun n => ⟨fun e h => ?_, fun h => ?_, fun h => ?_,
      fun slot m h => ?_, fun slot m f h hd => ?_, fun slot m f h hd => ?_⟩⟩
  · cases p <;> simp [addScan, M.bind_run, h]
  · constructor
    · simp [addScan, M.bind_run, h]
    · simp [addScan, M.bind_run, h]
  · cases p <;> simp [addScan, M.bind_run, h]
  · simp [addOuter, M.bind_run, h]
  · cases r with
    | next fs' m => exact absurd rfl (hr fs' m)
    | _ => simp [addOuter, M.bind_run, h]
  · simp [addOuter, M.bind_run, h]
  · simp [setAddEntryAux, M.bind_run, M.get_run, h]
  · simp [setAddEntryAux, M.bind_run, M.get_run, h]
  · simp [setAddEntryAux, M.bind_run, M.get_run, h]
  · simp only [setAddEntryAux, M.bind_run, M.get_run, h]
    by_cases hc : (s'.fill + 1) * 5 < m * 3 <;> simp [M.bind_run, M.put_run, hc]
  · simp [setAddEntryAux, M.bind_run, M.get_run, h, hd]
  · simp only [setAddEntryAux, M.bind_run, M.get_run, h]
    try (split <;> simp_all)

/-- Keys `1`..`4` all hash `0`, and `==` is equality. -/
def plainZero : Proto Nat (SetObj Nat) := { natSetProto with hashM := fun _ s => (.ok 0, s) }

/-- The `__eq__` of key `2` against key `3` adds key `4` the first time, and answers no. -/
def refillProto : Proto Nat (SetObj Nat) :=
  { plainZero with
    eq := fun a b s =>
      if a = 2 ∧ b = 3 ∧ (setKeys s).all (· ≠ 4) = true then (.ok false, (setAddKey plainZero 4 s).2)
      else (.ok (a == b), s) }

/-- `{2}` with a dummy at slot 0, where `1` was: `s.add(1); s.add(2); s.discard(1)`. -/
def refillStart : SetObj Nat := setProg refillProto [.add 1, .add 2, .discard 1] {}

/-- The `freeslot->hash != -1` re-check is reached, and it matters: adding `3` walks past the dummy at
slot 0 (`freeslot`), compares with `2`, whose `__eq__` puts `4` into that dummy, and reaches the NULL
at slot 6 with a `freeslot` that is no longer a dummy; it restarts and puts `3` at slot 6. An add that
skipped the re-check would overwrite `4`. CPython 3.15.2 gives the same table order, `[4, 2, 3]`. -/
theorem freeslot_refill_probe :
    setKeys refillStart = [2] ∧ refillStart.slot 0 = .dummy ∧
    (addOuter refillProto 3 0 (setProbeFuel 7) 0 0 7 none refillStart).1 = .ok (.unused 6 (some 0) 7) ∧
    (addOuter refillProto 3 0 (setProbeFuel 7) 0 0 7 none refillStart).2.slot 0 = .active 4 0 ∧
    setKeys (setAddKey refillProto 3 refillStart).2 = [4, 2, 3] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The `__eq__` of key `1` against key `2` clears the set, and answers no. -/
def clearProto : Proto Nat (SetObj Nat) :=
  { plainZero with
    eq := fun a b s => if a = 1 ∧ b = 2 then (.ok false, setClearInternal s) else (.ok (a == b), s) }

/-- `goto restart` is reached, and it matters: adding `2` to `{1}` compares with `1`, whose `__eq__`
empties the set; the walk restarts and `2` goes into the empty table. An add that took the restart
for success would leave the set empty. CPython 3.15.2 gives `[2]`. -/
theorem restart_probe :
    (addOuter clearProto 2 0 (setProbeFuel 7) 0 0 7 none (setAddKey clearProto 1 {}).2).1 = .ok .restart ∧
    setKeys (setAddKey clearProto 2 (setAddKey clearProto 1 {}).2).2 = [2] := by
  constructor <;> decide +kernel

/-! ## `set_update_iterable_lock_held` -/

/-- `set_update_iterable_lock_held` (:1221-1244), for every key protocol and every iterator, turn
by turn: `PyObject_GetIter` first (:1226-1229), whose failure is the result; then each `PyIter_Next`
runs in the state the last turn left, and may raise (the result: `PyErr_Occurred()`, :1240-1241),
end the loop (:1231, :1239), or yield a key, which `set_add_key` adds (:1232); a failed add is the
result, in the state it left (:1232-1236), and otherwise the loop goes on from there. -/
def SetUpdateIterableBody : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (getIter : SM K Unit)
    (step : SM K (Option K)) (rest : List (SM K (Option K))) (key : K) (so s1 s2 s3 : SetObj K)
    (e : PyExc),
    (getIter so = (.error e, s1) →
      setUpdateIterable P ⟨getIter, step :: rest⟩ so = (.error e, s1)) ∧
    (getIter so = (.ok (), s1) →
      setUpdateIterable P ⟨getIter, []⟩ so = (.ok (), s1) ∧
      (step s1 = (.error e, s2) → setUpdateIterable P ⟨getIter, step :: rest⟩ so = (.error e, s2)) ∧
      (step s1 = (.ok none, s2) → setUpdateIterable P ⟨getIter, step :: rest⟩ so = (.ok (), s2)) ∧
      (step s1 = (.ok (some key), s2) →
        (setAddKey P key s2 = (.error e, s3) →
          setUpdateIterable P ⟨getIter, step :: rest⟩ so = (.error e, s3)) ∧
        (setAddKey P key s2 = (.ok (), s3) →
          setUpdateIterable P ⟨getIter, step :: rest⟩ so = setUpdateIterable P ⟨pure (), rest⟩ s3)))
theorem setUpdateIterableBody_proven : SetUpdateIterableBody := by
  intro K _ P getIter step rest key so s1 s2 s3 e
  refine ⟨fun h => ?_, fun h => ⟨?_, fun h2 => ?_, fun h2 => ?_, fun h2 => ⟨fun h3 => ?_, fun h3 => ?_⟩⟩⟩
  · simp [setUpdateIterable, M.bind_run, h]
  · simp [setUpdateIterable, forIter, M.bind_run, h]
  · simp [setUpdateIterable, forIter, M.bind_run, h, h2]
  · simp [setUpdateIterable, forIter, M.bind_run, h, h2]
  · simp [setUpdateIterable, forIter, M.bind_run, h, h2, h3]
  · simp [setUpdateIterable, forIter, M.bind_run, h, h2, h3]

section UpdateRefine
variable {K : Type} [DecidableEq K] {P : Proto K (SetObj K)} {hf : K → Int} {eqv : K → K → Bool}

/-- The loop of `set_update_iterable_lock_held` over items that are handed over as they are, then
`tail`: every item is added in order, or an add runs out of memory. -/
theorem forIter_adds (H : HonestSet P hf eqv) (tail : List (SM K (Option K))) :
    ∀ (items : List K) (so : SetObj K) (l : List K), SetWF hf eqv so → (setKeys so).Perm l →
      (∃ s n, n ≤ so.used + items.length ∧ SetTooBig n ∧
        forIter (fun key => do setAddKey P key; return false)
          (items.map (fun x => pure (some x)) ++ tail) so = (.error memoryError, s)) ∨
      ∃ so', SetWF hf eqv so' ∧ (setKeys so').Perm (setAbs eqv (items.map .add) l) ∧
        forIter (fun key => do setAddKey P key; return false)
          (items.map (fun x => pure (some x)) ++ tail) so =
        forIter (fun key => do setAddKey P key; return false) tail so' := by
  intro items
  induction items with
  | nil => intro so l w hp; exact Or.inr ⟨so, w, hp, rfl⟩
  | cons x rest ih =>
    intro so l w hp
    have hstep : ∀ s, forIter (fun key => do setAddKey P key; return false)
        ((x :: rest).map (fun x => pure (some x)) ++ tail) s =
        match setAddKey P x s with
        | (.ok _, s') => forIter (fun key => do setAddKey P key; return false)
            (rest.map (fun x => pure (some x)) ++ tail) s'
        | (.error e, s') => (.error e, s') := by
      intro s
      simp only [List.map_cons, List.cons_append, forIter, M.bind_run, M.pure_run]
      cases setAddKey P x s with
      | mk r s' => cases r <;> rfl
    rw [hstep]
    simp only [List.map_cons, setAbs]
    rw [← hp.any_eq]
    rcases setAddKey_spec H w x with ⟨h1, h2⟩ | ⟨h1, h3⟩
    · simp only [h2, h1, if_true]
      rcases ih so l w hp with ⟨s, n, a, b, c⟩ | g
      · exact Or.inl ⟨s, n, by simp only [List.length_cons]; omega, b, c⟩
      · exact Or.inr g
    · simp only [h1, Bool.false_eq_true, if_false]
      rcases h3 with ⟨hb, s, h3⟩ | ⟨so', a, b, c, _, _⟩
      · left
        exact ⟨s, so.used + 1, by simp, hb, by simp [h3]⟩
      · simp only [a]
        have hu : so'.used = so.used + 1 := by
          have e1 := b.used
          have e2 := w.used
          have e3 := c.length_eq
          simp only [setKeys, List.length_map, List.length_cons] at e3
          omega
        rcases ih so' _ b (c.trans ((hp.cons x).trans (List.perm_append_singleton x l).symm)) with
          ⟨s, n, g1, g2, g3⟩ | g
        · exact Or.inl ⟨s, n, by simp only [List.length_cons]; omega, g2, g3⟩
        · exact Or.inr g

end UpdateRefine

/-- `set.update(iterable)` (`set_update_iterable_lock_held`, :1221-1244) for an honest key protocol,
from any well-formed set, with an iterable whose `__iter__` may fail and whose iteration may end with
an exception: a failed `__iter__` changes nothing; otherwise either an add runs out of memory, for a
set that would need more than `PyMem_NEW` can give, or every item is added in order, the set stays
well formed and holds the keys of the list model, and then the iterator's exception, if any, is the
result in that state. -/
def SetUpdateIterableRefines : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (hf : K → Int) (eqv : K → K → Bool),
    HonestSet P hf eqv → ∀ (so : SetObj K) (it : Iterable K), SetWF hf eqv so →
      (∀ e, it.getIter = some e → setUpdateIterable P (ReIter.ofIterable it) so = (.error e, so)) ∧
      (it.getIter = none →
        (∃ s n, n ≤ so.used + it.items.length ∧ SetTooBig n ∧
          setUpdateIterable P (ReIter.ofIterable it) so = (.error memoryError, s)) ∨
        ∃ so', SetWF hf eqv so' ∧ (setKeys so').Perm (setAbs eqv (it.items.map .add) (setKeys so)) ∧
          setUpdateIterable P (ReIter.ofIterable it) so =
            (match it.stop with
             | some e => .error e
             | none => .ok (), so'))
theorem setUpdateIterableRefines_proven : SetUpdateIterableRefines := by
  intro K _ P hf eqv H so it w
  refine ⟨fun e he => ?_, fun hn => ?_⟩
  · simp [setUpdateIterable, ReIter.ofIterable, he, M.bind_run]
  · let tail : List (SM K (Option K)) := match it.stop with
      | some e => [M.throw e]
      | none => []
    have hrun : ∀ s, setUpdateIterable P (ReIter.ofIterable it) s =
        (match forIter (fun key => do setAddKey P key; return false)
            (it.items.map (fun x => pure (some x)) ++ tail) s with
         | (.ok _, s') => (.ok (), s')
         | (.error e, s') => (.error e, s')) := by
      intro s
      simp only [setUpdateIterable, ReIter.ofIterable, hn, M.bind_run, M.pure_run]
      cases forIter (fun key => do setAddKey P key; return false)
          (it.items.map (fun x => pure (some x)) ++ tail) s with
      | mk r s' => cases r <;> rfl
    rcases forIter_adds H tail it.items so (setKeys so) w (List.Perm.refl _) with
      ⟨s, n, a, b, c⟩ | ⟨so', a, b, c⟩
    · left
      exact ⟨s, n, a, b, by rw [hrun, c]⟩
    · right
      refine ⟨so', a, b, ?_⟩
      rw [hrun, c]
      cases hs : it.stop with
      | none => simp [tail, hs, forIter]
      | some e => simp [tail, hs, forIter, M.bind_run]

/-! ## `set_isdisjoint_impl` -/

/-- `set_isdisjoint_impl` (:1910-1968), for every key protocol and iterator: `so == other` answers
whether `so` is empty, and changes nothing (:1917-1922); only `PyAnySet_CheckExact(other)` (:1924)
takes the two-set branch, so an instance of a set subclass, whatever its table holds, goes through
`PyObject_GetIter(other)`, its type's `__iter__`, and the generic loop (:1948-1967), as does any
other iterable. -/
def SetIsdisjointBranches : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (so o : SetObj K) (it : ReIter (SetObj K) K),
    (o.ident = so.ident →
      setIsdisjoint P (.set o) so = (.ok (so.used == 0), so) ∧
      setIsdisjoint P (.sub o it) so = (.ok (so.used == 0), so)) ∧
    (o.ident ≠ so.ident →
      setIsdisjoint P (.sub o it) so = setDisjointIter P it so ∧
      (o.exact = false → setIsdisjoint P (.set o) so = setDisjointIter P (SetArg.set o).toReIter so)) ∧
    setIsdisjoint P (.live it) so = setDisjointIter P it so
theorem setIsdisjointBranches_proven : SetIsdisjointBranches := by
  intro K _ P so o it
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨?_, fun hx => ?_⟩, ?_⟩
  · simp [setIsdisjoint, M.bind_run, M.get_run, h]
  · simp [setIsdisjoint, M.bind_run, M.get_run, h]
  · simp [setIsdisjoint, M.bind_run, M.get_run, h, SetArg.toReIter]
  · simp [setIsdisjoint, M.bind_run, M.get_run, h, hx]
  · simp [setIsdisjoint, M.bind_run, M.get_run, SetArg.toReIter]

section DisjointRefine
variable {K : Type} [DecidableEq K] {P : Proto K (SetObj K)} {hf : K → Int} {eqv : K → K → Bool}
  {so : SetObj K}

theorem forIter_contains (H : HonestSet P hf eqv) (w : SetWF hf eqv so) (tail : List (SM K (Option K))) :
    ∀ items : List K,
      forIter (setContainsKey P) (items.map (fun x => pure (some x)) ++ tail) so =
        if items.any (fun x => (setKeys so).any (eqv · x)) then (.ok true, so)
        else forIter (setContainsKey P) tail so := by
  intro items
  induction items with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map_cons, List.cons_append, forIter, M.bind_run, M.pure_run, setContains_spec H w x,
      List.any_cons]
    by_cases hx : (setKeys so).any (eqv · x) = true
    · simp [hx]
    · have hx' : (setKeys so).any (eqv · x) = false := by simpa using hx
      simp only [hx', Bool.false_or, Bool.false_eq_true, if_false]
      exact ih

end DisjointRefine

/-- The generic branch of `set_isdisjoint_impl` for an honest key protocol, on a well-formed set and
an iterable whose `__iter__` may fail and whose iteration may end with an exception: a failed
`__iter__` is the result; an item the set holds answers `False` at once, before any later failure;
otherwise the iterator's exception, if any, and `True` if none. Nothing changes. -/
def SetDisjointIterRefines : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (hf : K → Int) (eqv : K → K → Bool),
    HonestSet P hf eqv → ∀ (so : SetObj K) (it : Iterable K), SetWF hf eqv so →
      setDisjointIter P (ReIter.ofIterable it) so =
        (match it.getIter with
         | some e => .error e
         | none =>
           if it.items.any (fun x => (setKeys so).any (eqv · x)) then .ok false
           else match it.stop with
             | some e => .error e
             | none => .ok true, so)
theorem setDisjointIterRefines_proven : SetDisjointIterRefines := by
  intro K _ P hf eqv H so it w
  cases hg : it.getIter with
  | some e => simp [setDisjointIter, ReIter.ofIterable, hg, M.bind_run]
  | none =>
    simp only [setDisjointIter, ReIter.ofIterable, hg, M.bind_run, M.pure_run]
    rw [forIter_contains H w]
    cases ha : it.items.any (fun x => (setKeys so).any (eqv · x)) with
    | true => simp
    | false =>
      cases hs : it.stop with
      | none => simp [forIter]
      | some e => simp [forIter, M.bind_run]

/-- The review's probe: `{1}.isdisjoint(S([2]))` for a set subclass `S` whose `__iter__` yields `1`
is `False`, since `PyAnySet_CheckExact` fails and the loop runs `S.__iter__`; walking the table of
`S([2])` instead would answer `True`. CPython 3.15.2 answers `False`. -/
theorem isdisjoint_sub_probe :
    (setIsdisjoint natSetProto
      (.sub { (setAddKey natSetProto 2 {}).2 with ident := 5, exact := false }
        (ReIter.ofIterable { items := [1] })) (setAddKey natSetProto 1 {}).2).1 = .ok false ∧
    (setIsdisjoint natSetProto
      (.set { (setAddKey natSetProto 2 {}).2 with ident := 5, exact := false })
      (setAddKey natSetProto 1 {}).2).1 = .ok true := by
  constructor <;> decide +kernel

/-! ## `set_intersection` -/

/-- `set_intersection` (:1708-1791), at the function level, for every key protocol, argument and
iterator: `so == other` is `set_copy_impl(so)` (:1716-1717), for an exact set and a subclass alike;
any other set (`PyAnySet_Check`, :1723), a subclass with its own `__iter__` too, takes the two-set
branch (`SetInterRefines` pins it); anything else makes the new result, puts it in focus with `so`
among the peers, runs `PyObject_GetIter` and the generic loop (`setInterIter`, :1756-1777, each turn
pinned by `InterIterBody`), and hands back the result, or the exception in the state the loop left
(:1779-1790). A failed `PyObject_GetIter` is the result. -/
def SetIntersectionBranches : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (id : Nat) (so o : SetObj K)
    (it : ReIter (SetObj K) K),
    (o.ident = so.ident →
      setIntersection P (.set o) id so = setCopy P id so ∧
      setIntersection P (.sub o it) id so = setCopy P id so) ∧
    (o.ident ≠ so.ident →
      setIntersection P (.set o) id so = withPeer o (setIntersectionSets P o id) so ∧
      setIntersection P (.sub o it) id so = withPeer o (setIntersectionSets P o id) so) ∧
    (∀ other : SetArg K, (∀ s, other ≠ .set s) → (∀ s it', other ≠ .sub s it') →
      setIntersection P other id so =
        (match onResult (newBasetype so.toSetBody id) (setInterIter P so.ident other.toReIter) so with
         | (.ok r, s) => (.ok r.2, s)
         | (.error e, s) => (.error e, s))) ∧
    (∀ e s1, it.getIter { newBasetype so.toSetBody id with peers := so.toSetBody :: so.peers } =
        (.error e, s1) → (setIntersection P (.live it) id so).1 = .error e)
theorem setIntersectionBranches_proven : SetIntersectionBranches := by
  intro K _ P id so o it
  have hgen : ∀ other : SetArg K, (∀ s, other ≠ .set s) → (∀ s it', other ≠ .sub s it') →
      setIntersection P other id so =
        (match onResult (newBasetype so.toSetBody id) (setInterIter P so.ident other.toReIter) so with
         | (.ok r, s) => (.ok r.2, s)
         | (.error e, s) => (.error e, s)) := by
    intro other h1 h2
    have hrun : setIntersection P other id so =
        (do let r ← onResult (newBasetype so.toSetBody id) (setInterIter P so.ident other.toReIter)
            pure r.2) so := by
      cases other with
      | set s => exact absurd rfl (h1 s)
      | sub s it' => exact absurd rfl (h2 s it')
      | _ => simp [setIntersection, M.bind_run, M.get_run]
    rw [hrun, M.bind_run]
    cases onResult (newBasetype so.toSetBody id) (setInterIter P so.ident other.toReIter) so with
    | mk r s => cases r <;> rfl
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩, hgen, fun e s1 he => ?_⟩
  · simp [setIntersection, M.bind_run, M.get_run, h]
  · simp [setIntersection, M.bind_run, M.get_run, h]
  · simp [setIntersection, M.bind_run, M.get_run, h]
  · simp [setIntersection, M.bind_run, M.get_run, h]
  · rw [hgen (.live it) (fun s => nofun) (fun s it' => nofun)]
    simp [onResult, setInterIter, SetArg.toReIter, M.bind_run, he]

/-! ## `_shuffle_bits` -/

/-- `_shuffle_bits` (:953-957) is `((h ^ 89869747) ^ (h << 16)) * 3644798167` on a 64-bit
`Py_uhash_t`: its values at the hash fields `frozenset_hash_impl` meets most (NULL's `0` and a dummy's
`-1`), at `1`, `2**63` and `12345`, and through `frozenset_hash_impl` the hashes CPython 3.15.2 gives
for `frozenset()`, `frozenset({0})`, `frozenset({1, 2})` and `frozenset(range(10))` (probed). A
shuffle with another constant, shift or width misses them; `FrozensetHashActive` is the property that
holds for any shuffle. -/
def ShuffleBitsValues : Prop :=
  shuffleBits 0 = 327557089134353749 ∧ shuffleBits 1 = 327318219996883070 ∧
  shuffleBits (2 ^ 64 - 1) = 327650953621548500 ∧ shuffleBits (2 ^ 63) = 9550929125989129557 ∧
  shuffleBits 12345 = 3264452959386040038 ∧
  frozensetHashImpl ({} : SetObj Nat) = 133146708735736 ∧
  frozensetHashImpl (setProg natSetProto [.add 0] {}) = -2704248722033767810 ∧
  frozensetHashImpl (setProg natSetProto [.add 1, .add 2] {}) = -1826646154956904602 ∧
  frozensetHashImpl (setProg natSetProto ((List.range 10).map .add) {}) = 3895031357313128696
theorem shuffleBitsValues_proven : ShuffleBitsValues := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## `set_dealloc` -/

/-- What `set_dealloc` (:733-754) does that Python can see, as hooks on a world `W`: the weak
references' callbacks (`PyObject_ClearWeakRefs`), and the release of the keys and the table, whose
`Py_DECREF`s can run `__del__` (left to the finalization scope limit, as a hook). -/
structure SetDeallocHooks (W : Type) where
  clearWeakrefs : W → W
  dropKeys : W → W

/-- `set_dealloc` (:733-754): untrack (no visible effect), then `FT_CLEAR_WEAKREFS(self,
so->weakreflist)` (:743), which in the GIL build calls `PyObject_ClearWeakRefs` only when the set has
a weak reference list (`Include/internal/pycore_weakref.h:46-52`), then the `Py_DECREF` loop over
the keys and the frees (:745-753). -/
def setDealloc {W : Type} (h : SetDeallocHooks W) (hasWeakrefs : Bool) (w : W) : W :=
  let w1 := if hasWeakrefs then h.clearWeakrefs w else w
  h.dropKeys w1

/-- `set_dealloc`, for every world and hooks: a set with weak references runs their callbacks first,
in the world as it is, and only then releases its keys, in the world the callbacks left (bpo-31095:
the untrack comes before any callback); a set without runs no callback. -/
def SetDeallocOrder : Prop :=
  ∀ (W : Type) (h : SetDeallocHooks W) (w : W),
    setDealloc h true w = h.dropKeys (h.clearWeakrefs w) ∧ setDealloc h false w = h.dropKeys w
theorem setDeallocOrder_proven : SetDeallocOrder := fun _ _ _ => ⟨rfl, rfl⟩

/-! ## The table re-check of `set_compare_entry_lock_held` and `set_add_entry_takeref` -/

/-- Keys below 50 hash to themselves; key `99` hashes to `10`. -/
def abaPlain : Proto Nat (SetObj Nat) :=
  { natSetProto with hashM := fun k s => (.ok (if k = 99 then 10 else k), s) }

/-- `{10, ..., 15}`, what `__eq__` refills the set from. -/
def abaRefill : SetObj Nat :=
  setProg abaPlain [.add 10, .add 11, .add 12, .add 13, .add 14, .add 15] { ident := 77 }

/-- `10 == 99` on the 32-slot table: `s.clear()`, which frees the table, then `s.update(refill)`,
which makes a 16-slot table; the allocator hands back the address just freed, as glibc does in
bugs/dictset-set-lookup-table-aba. -/
def abaProto : Proto Nat (SetObj Nat) :=
  { abaPlain with
    eq := fun a b s =>
      if a = 10 ∧ b = 99 ∧ s.mask = 31 then
        (.ok false, (setMerge abaPlain abaRefill { setClearInternal s with reuse := [s.tableId] }).2)
      else (.ok (a == b), s) }

/-- `{10, 1, 2, 3, 4}`: a 32-slot malloc'ed table, `10` at slot 10. -/
def abaStart : SetObj Nat := setProg abaPlain [.add 10, .add 1, .add 2, .add 3, .add 4] {}

/-- The world `__eq__` leaves: the same table identity, mask 15 instead of 31, and `10` still at
slot 10, so CPython's re-check `table != so->table || entry->key != startkey` (:159, :294) does
not fire. The lookup goes on with no restart; the add reloads `mask` (:296), walks on from slot 10
with the block the old mask allowed, and reaches slot 16, past the end of the new table, where it
stores: `used` becomes 7 while the table holds 6 keys, CPython's `len(s)` one over.

Scope: the model reads a slot past the end of a table as NULL (`List.getD`) and drops a store there
(`List.set`). CPython reads and writes the stale bytes of the old table: a lookup that finds the old
entry past the end (the discard that frees a key, in the bug record) is not expressible. -/
theorem aba_probe :
    abaStart.mask = 31 ∧ abaStart.slot 10 = .active 10 10 ∧
    (abaProto.eq 10 99 abaStart).1 = .ok false ∧
    (abaProto.eq 10 99 abaStart).2.mask = 15 ∧
    (abaProto.eq 10 99 abaStart).2.tableId = abaStart.tableId ∧
    (abaProto.eq 10 99 abaStart).2.slot 10 = .active 10 10 ∧
    (lookStep abaProto false 99 10 10 abaStart).1 = .ok (.inr ()) ∧
    (addStep abaProto 99 10 10 31 none abaStart).1 = .ok (.inr (15, none)) ∧
    (setAddKey abaProto 99 abaStart).2.used = 7 ∧
    (setKeys (setAddKey abaProto 99 abaStart).2).length = 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The claim the review found false on 3.15.2: when `__eq__` has replaced the table by one of
another size, the lookup starts over. -/
def SetLookupRestartsOnResize : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (key startkey : K) (hash : Int) (slot : Nat)
    (so s' : SetObj K) (b : Bool),
    so.slot slot = .active startkey hash → startkey ≠ key →
    ¬ ((P.isStr startkey = true ∧ P.isStr key = true) ∧ P.strEq startkey key = true) →
    P.eq startkey key so = (.ok b, s') → s'.mask ≠ so.mask →
    lookStep P false key hash slot so = (.ok (.inl .restart), s')

/-- The same claim for `set_add_entry_takeref` on an answer of no. -/
def SetAddRestartsOnResize : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (key startkey : K) (hash : Int)
    (slot mask : Nat) (so s' : SetObj K) (fs : Option Nat),
    so.slot slot = .active startkey hash → startkey ≠ key →
    ¬ ((P.isStr startkey = true ∧ P.isStr key = true) ∧ P.strEq startkey key = true) →
    P.eq startkey key so = (.ok false, s') → s'.mask ≠ so.mask →
    addStep P key hash slot mask fs so = (.ok (.inl .restart), s')

theorem aba_eq : abaProto.eq 10 99 abaStart = (.ok false, (abaProto.eq 10 99 abaStart).2) :=
  Prod.ext aba_probe.2.2.1 rfl

theorem aba_str : ¬ ((abaProto.isStr 10 = true ∧ abaProto.isStr 99 = true) ∧
    abaProto.strEq 10 99 = true) := by decide

theorem setLookupRestartsOnResize_refuted : ¬SetLookupRestartsOnResize := by
  intro h
  have h1 := h Nat abaProto 99 10 10 10 abaStart _ false aba_probe.2.1 (by decide) aba_str aba_eq
    (by rw [aba_probe.2.2.2.1, aba_probe.1]; decide)
  have h2 := congrArg Prod.fst h1
  rw [aba_probe.2.2.2.2.2.2.1] at h2
  exact nomatch h2

theorem setAddRestartsOnResize_refuted : ¬SetAddRestartsOnResize := by
  intro h
  have h1 := h Nat abaProto 99 10 10 10 31 abaStart _ none aba_probe.2.1 (by decide) aba_str aba_eq
    (by rw [aba_probe.2.2.2.1, aba_probe.1]; decide)
  have h2 := congrArg Prod.fst h1
  rw [aba_probe.2.2.2.2.2.2.2.1] at h2
  exact nomatch h2

end PyLean.DictSet
