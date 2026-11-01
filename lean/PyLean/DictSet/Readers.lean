import PyLean.DictSet.DictOps

/-!
The readers as faithful wrappers around `_Py_dict_lookup`, for every key protocol.

Nothing here assumes `Honest`. Each reader is shown to be a fixed function of what
`_Py_dict_lookup` returns in the current state, so the three paths that `Honest` hides are on
record: a hash that raises, a lookup (that is, an `__eq__`) that raises or mutates the table, and
a lookup that returns `ix >= 0` with no value, which is the split-table case the setdefault crash
mishandles (`dictobject.c:1915-1922`, `insertdict`'s "ix may not be DKIX_EMPTY because split table
may have key without value"). In every reader but setdefault, that case is read as "absent".
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type} [DecidableEq K]

/-- `_PyObject_HashFast` then `dict_unhashable_type`: hashing a key either gives `hf`-free
`h` or raises the rewritten exception, before any reader touches the table. -/
theorem hashKey_run {β : Type} (P : Proto K (PyDict K V)) (key : K) (f : Int → DM K V β)
    (mp : PyDict K V) :
    (hashKey P key >>= f) mp =
      match P.hash key with
      | .ok h => f h mp
      | .error e => (.error (dictUnhashableType P key e), mp) := by
  unfold hashKey
  cases P.hash key with
  | ok h => simp [M.bind_run]
  | error e => simp [M.bind_run]

section Wrap
variable (P : Proto K (PyDict K V)) (key : K) (hash : Int) (mp : PyDict K V)

/-- `_PyDict_GetItemRef_KnownHash` (:2438-2462): the value `_Py_dict_lookup` left, unchanged;
a NULL value (`r.2 = none`, the split-absent case) is "not found". -/
theorem refKnownHash_wrap :
    dictGetItemRefKnownHash P key hash mp =
      match dictLookup P key hash mp with
      | (.ok r, s) => (.ok r.2, s)
      | (.error e, s) => (.error e, s) := by
  simp only [dictGetItemRefKnownHash, M.bind_run]
  rcases h : dictLookup P key hash mp with ⟨a, s⟩
  rcases a with e | ⟨ix, v⟩
  · rfl
  · cases v <;> rfl

/-- `_PyDict_Contains_KnownHash` (:4860-4882): found iff the slot is non-empty and holds a value,
so a split key with no value is not contained. -/
theorem containsKnownHash_wrap :
    dictContainsKnownHash P key hash mp =
      match dictLookup P key hash mp with
      | (.ok r, s) => (.ok (r.1 != DKIX_EMPTY && r.2.isSome), s)
      | (.error e, s) => (.error e, s) := by
  simp only [dictContainsKnownHash, M.bind_run]
  rcases h : dictLookup P key hash mp with ⟨a, s⟩
  rcases a with e | ⟨ix, v⟩ <;> rfl

end Wrap

section Top
variable (P : Proto K (PyDict K V)) (key : K) (mp : PyDict K V)

/-- `PyDict_GetItemRef` (:2464-2481) on a real dict: hash, then the known-hash reader. -/
theorem getItemRef_wrap :
    pyDictGetItemRef P true key mp =
      match P.hash key with
      | .error e => (.error (dictUnhashableType P key e), mp)
      | .ok h => dictGetItemRefKnownHash P key h mp := by
  cases hh : P.hash key with
  | error e =>
    simp only [pyDictGetItemRef, hashKey, Bool.not_true, Bool.false_eq_true, if_false,
      M.bind_run, M.pure_run, M.throw_run, hh]
  | ok h =>
    simp only [pyDictGetItemRef, hashKey, Bool.not_true, Bool.false_eq_true, if_false,
      M.bind_run, M.pure_run, M.throw_run, hh]

/-- `PyDict_GetItemWithError` (:2515-2541) on a real dict: it returns the raw lookup value,
including NULL as not-found, and never consults `ix`. -/
theorem getItemWithError_wrap :
    pyDictGetItemWithError P true key mp =
      match P.hash key with
      | .error e => (.error (dictUnhashableType P key e), mp)
      | .ok h =>
        match dictLookup P key h mp with
        | (.ok r, s) => (.ok r.2, s)
        | (.error e, s) => (.error e, s) := by
  cases hh : P.hash key with
  | error e =>
    simp only [pyDictGetItemWithError, hashKey, Bool.not_true, Bool.false_eq_true, if_false,
      M.bind_run, M.pure_run, M.throw_run, hh]
  | ok h =>
    simp only [pyDictGetItemWithError, hashKey, Bool.not_true, Bool.false_eq_true, if_false,
      M.bind_run, M.pure_run, M.throw_run, hh]
    rcases hl : dictLookup P key h mp with ⟨a, s⟩
    rcases a with e | ⟨ix, v⟩ <;> rfl

/-- `PyDict_Contains` (:4835-4846), behind `key in d`. -/
theorem contains_wrap :
    pyDictContains P key mp =
      match P.hash key with
      | .error e => (.error (dictUnhashableType P key e), mp)
      | .ok h =>
        match dictLookup P key h mp with
        | (.ok r, s) => (.ok (r.1 != DKIX_EMPTY && r.2.isSome), s)
        | (.error e, s) => (.error e, s) := by
  cases hh : P.hash key with
  | error e =>
    simp only [pyDictContains, hashKey, M.bind_run, M.pure_run, M.throw_run, hh]
  | ok h =>
    simp only [pyDictContains, hashKey, dictContainsKnownHash, M.bind_run, M.pure_run, M.throw_run, hh]
    rcases hl : dictLookup P key h mp with ⟨a, s⟩
    rcases a with e | ⟨ix, v⟩ <;> rfl

/-- `dict_subscript` (:3504-3538) on an exact dict (`missing = none`): the value when the slot
holds one, else `KeyError`. A NULL value raises `KeyError` too. -/
theorem subscript_wrap :
    dictSubscript P none key mp =
      match P.hash key with
      | .error e => (.error (dictUnhashableType P key e), mp)
      | .ok h =>
        match dictLookup P key h mp with
        | (.ok r, s) =>
          match r.2 with
          | some v => if r.1 == DKIX_EMPTY then (.error (keyErr P key), s) else (.ok v, s)
          | none => (.error (keyErr P key), s)
        | (.error e, s) => (.error e, s) := by
  cases hh : P.hash key with
  | error e =>
    simp only [dictSubscript, hashKey, M.bind_run, M.pure_run, M.throw_run, hh]
  | ok h =>
    simp only [dictSubscript, hashKey, M.bind_run, M.pure_run, M.throw_run, hh]
    rcases hl : dictLookup P key h mp with ⟨a, s⟩
    rcases a with e | ⟨ix, v⟩
    · rfl
    · cases v with
      | none => rfl
      | some w => by_cases he : ix == DKIX_EMPTY <;> simp [he, subscriptMissing]

/-- `dict.get` (`dict_get_impl`, :4386-4406): the value or the default; a NULL value is the
default, and `ix == DKIX_EMPTY` is the default. -/
theorem get_wrap (dflt : V) :
    dictGet P key dflt mp =
      match P.hash key with
      | .error e => (.error (dictUnhashableType P key e), mp)
      | .ok h =>
        match dictLookup P key h mp with
        | (.ok r, s) =>
          (.ok (match r.2 with | some v => if r.1 == DKIX_EMPTY then dflt else v | none => dflt), s)
        | (.error e, s) => (.error e, s) := by
  cases hh : P.hash key with
  | error e =>
    simp only [dictGet, hashKey, M.bind_run, M.pure_run, M.throw_run, hh]
  | ok h =>
    simp only [dictGet, hashKey, M.bind_run, M.pure_run, M.throw_run, hh]
    rcases hl : dictLookup P key h mp with ⟨a, s⟩
    rcases a with e | ⟨ix, v⟩
    · rfl
    · cases v with
      | none => rfl
      | some w => by_cases he : ix == DKIX_EMPTY <;> simp [he]

end Top

/-- Every reader is faithful to `_Py_dict_lookup` for an arbitrary key protocol: a raising hash
propagates, a raising lookup (a raising or mutating `__eq__`) propagates with the state the lookup
left, and a slot with no value (`ix >= 0`, `*value_addr == NULL`: a split key this dict lacks) is
read as absent, never dereferenced. -/
def ReadersFaithful : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (key : K) (mp : PyDict K V),
    -- not a dict: the two C API readers that check raise `SystemError`
    pyDictGetItemRef P false key mp = (.error badInternalCall, mp) ∧
    pyDictGetItemWithError P false key mp = (.error badInternalCall, mp) ∧
    -- a raising hash: every reader raises the rewritten exception, dict unchanged
    (∀ e, P.hash key = .error e →
      pyDictGetItemRef P true key mp = (.error (dictUnhashableType P key e), mp) ∧
      pyDictGetItemWithError P true key mp = (.error (dictUnhashableType P key e), mp) ∧
      pyDictContains P key mp = (.error (dictUnhashableType P key e), mp) ∧
      dictSubscript P none key mp = (.error (dictUnhashableType P key e), mp) ∧
      ∀ dflt, dictGet P key dflt mp = (.error (dictUnhashableType P key e), mp)) ∧
    -- a raising lookup: every reader raises what it raised, in the state it left
    (∀ h e s, P.hash key = .ok h → dictLookup P key h mp = (.error e, s) →
      pyDictGetItemRef P true key mp = (.error e, s) ∧
      pyDictGetItemWithError P true key mp = (.error e, s) ∧
      pyDictContains P key mp = (.error e, s) ∧
      dictSubscript P none key mp = (.error e, s) ∧
      ∀ dflt, dictGet P key dflt mp = (.error e, s)) ∧
    -- a slot with no value: absent everywhere, no crash
    (∀ h r s, P.hash key = .ok h → dictLookup P key h mp = (.ok r, s) → r.2 = none →
      pyDictGetItemRef P true key mp = (.ok none, s) ∧
      pyDictGetItemWithError P true key mp = (.ok none, s) ∧
      pyDictContains P key mp = (.ok false, s) ∧
      dictSubscript P none key mp = (.error (keyErr P key), s) ∧
      ∀ dflt, dictGet P key dflt mp = (.ok dflt, s)) ∧
    -- a slot with a value: every reader returns that value, in the state the lookup left
    (∀ h ix v s, P.hash key = .ok h → dictLookup P key h mp = (.ok (ix, some v), s) →
      ix ≠ DKIX_EMPTY →
      pyDictGetItemRef P true key mp = (.ok (some v), s) ∧
      pyDictGetItemWithError P true key mp = (.ok (some v), s) ∧
      pyDictContains P key mp = (.ok true, s) ∧
      dictSubscript P none key mp = (.ok v, s) ∧
      ∀ dflt, dictGet P key dflt mp = (.ok v, s))

theorem readersFaithful_proven : ReadersFaithful := by
  intro K V _ P key mp
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro e he
    refine ⟨?_, ?_, ?_, ?_, fun dflt => ?_⟩ <;>
      simp only [getItemRef_wrap, getItemWithError_wrap, contains_wrap, subscript_wrap,
        get_wrap, he]
  · intro h e s hh hl
    refine ⟨?_, ?_, ?_, ?_, fun dflt => ?_⟩ <;>
      simp only [getItemRef_wrap, getItemWithError_wrap, contains_wrap, subscript_wrap,
        get_wrap, refKnownHash_wrap, hh, hl]
  · intro h r s hh hl hv
    refine ⟨?_, ?_, ?_, ?_, fun dflt => ?_⟩ <;>
      simp only [getItemRef_wrap, getItemWithError_wrap, contains_wrap, subscript_wrap,
        get_wrap, refKnownHash_wrap, hh, hl, hv, Option.isSome_none, Bool.and_false]
  · intro h ix v s hh hl hne
    have he : (ix == DKIX_EMPTY) = false := by simpa using hne
    have he' : (ix != DKIX_EMPTY) = true := by simpa using hne
    refine ⟨?_, ?_, ?_, ?_, fun dflt => ?_⟩ <;>
      simp [getItemRef_wrap, getItemWithError_wrap, contains_wrap, subscript_wrap,
        get_wrap, refKnownHash_wrap, hh, hl, he, he']

end PyLean.DictSet
