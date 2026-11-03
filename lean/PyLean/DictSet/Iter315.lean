import PyLean.DictSet.Iter

/-!
What `iter(d)`, `reversed(d)` and the six iterator types hand back, and `__length_hint__`
(CPython 3.15.2, `Objects/dictobject.c`).
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type}

/-- `dict_iter` (:5438-5443): `dictiter_new(dict, &PyDictIterKey_Type)`. -/
def dictIterObj (mp : PyDict K V) : DictIter := dictiterNew mp .key false

/-- `dict___reversed___impl` (:6352-6358): `dictiter_new(self, &PyDictRevIterKey_Type)`. -/
def dictReversedObj (mp : PyDict K V) : DictIter := dictiterNew mp .key true

/-- `list(it)` with what each `next()` hands back: `PySequence_List` after the hint, through
`dictiterYield`, which is the flavour's own `iternext`. -/
def dictiterYieldDrain (d : PyDict K V) :
    Nat → DictIter → List (IterItem K V) → Py (List (IterItem K V)) × DictIter
  | 0, di, _ => (.error .modelFuel, di)
  | fuel + 1, di, acc =>
    match dictiterYield d di with
    | (.error e, di') => (.error e, di')
    | (.ok none, di') => (.ok acc.reverse, di')
    | (.ok (some x), di') => dictiterYieldDrain d fuel di' (x :: acc)

def dictiterYieldList (d : PyDict K V) (di : DictIter) : Py (List (IterItem K V)) :=
  match dictiterLengthHint d di with
  | .error e => .error e
  | .ok _ => (dictiterYieldDrain d (d.body.nentries + d.used + 2) di []).1

/-- `next()` never changes which flavour an iterator is. -/
theorem dictiterNext_kind (d : PyDict K V) (di : DictIter) : (dictiterNext d di).2.kind = di.kind := by
  unfold dictiterNext dictiterNextForward dictiterNextReverse
  repeat' (first | rfl | split | dsimp only)

/-- Draining by `next()` hands back each pair through the flavour of the iterator. -/
theorem yieldDrain_eq (d : PyDict K V) :
    ∀ (fuel : Nat) (di : DictIter) (acc : List (K × V)),
      (dictiterYieldDrain d fuel di (acc.map di.kind.result)).1 =
        ((dictiterDrain d fuel di acc).1).map (·.map di.kind.result) := by
  intro fuel
  induction fuel with
  | zero => intro di acc; rfl
  | succ fuel ih =>
    intro di acc
    have hk := dictiterNext_kind d di
    simp only [dictiterYieldDrain, dictiterDrain, dictiterYield]
    rcases hn : dictiterNext d di with ⟨r, di'⟩
    rw [hn] at hk
    cases r with
    | error e => rfl
    | ok o =>
      cases o with
      | none => simp [Except.map, List.map_reverse]
      | some x =>
        simp only []
        have := ih di' (x :: acc)
        simp only [List.map_cons] at this
        rw [hk] at this
        exact this

/-- `list(it)` by `next()` for each of the six iterators, `iter(d)` and `reversed(d)`, on a
well-formed dict of either form: a key iterator hands back the keys, a value iterator the values and
an item iterator the pairs, forward in the order of the list and backward reversed; `iter(d)` is the
forward key iterator and `reversed(d)` the backward one. -/
def IterYields : Prop :=
  ∀ (K V : Type) [DecidableEq K] (hf : K → Int) (eqv : K → K → Bool) (isStr : K → Bool)
    (d : PyDict K V), (DictInv hf eqv isStr d ∨ SplitInv hf eqv isStr d) →
    dictiterYieldList d (dictiterNew d .key false) = .ok ((dictAssoc d).map fun p => .key p.1) ∧
    dictiterYieldList d (dictiterNew d .value false) = .ok ((dictAssoc d).map fun p => .value p.2) ∧
    dictiterYieldList d (dictiterNew d .item false) = .ok ((dictAssoc d).map fun p => .item p.1 p.2) ∧
    dictiterYieldList d (dictiterNew d .key true) = .ok ((dictAssoc d).reverse.map fun p => .key p.1) ∧
    dictiterYieldList d (dictiterNew d .value true) =
      .ok ((dictAssoc d).reverse.map fun p => .value p.2) ∧
    dictiterYieldList d (dictiterNew d .item true) =
      .ok ((dictAssoc d).reverse.map fun p => .item p.1 p.2) ∧
    dictiterYieldList d (dictIterObj d) = .ok ((dictAssoc d).map fun p => .key p.1) ∧
    dictiterYieldList d (dictReversedObj d) = .ok ((dictAssoc d).reverse.map fun p => .key p.1)

theorem yieldList_eq (d : PyDict K V) (di : DictIter) :
    dictiterYieldList d di = ((dictiterToList d di).1).map (·.map di.kind.result) := by
  simp only [dictiterYieldList, dictiterToList]
  cases dictiterLengthHint d di with
  | error e => rfl
  | ok _ =>
    simp only []
    exact yieldDrain_eq d _ di []

theorem iterYields_proven : IterYields := by
  intro K V _ hf eqv isStr d hd
  have h := fun kind => iter_toList d hd kind
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [yieldList_eq, (h .key).1]; rfl
  · rw [yieldList_eq, (h .value).1]; rfl
  · rw [yieldList_eq, (h .item).1]; rfl
  · rw [yieldList_eq, (h .key).2]; rfl
  · rw [yieldList_eq, (h .value).2]; rfl
  · rw [yieldList_eq, (h .item).2]; rfl
  · simp only [dictIterObj]; rw [yieldList_eq, (h .key).1]; rfl
  · simp only [dictReversedObj]; rw [yieldList_eq, (h .key).2]; rfl

/-- `__length_hint__` of a dict iterator (`dictiter_len`, :5636-5644): what is left while the
iterator is alive and the dict has the size it had, 0 otherwise; a new iterator over a dict of `n`
items says `n`. `ma_used` and `len` are `Py_ssize_t`, below `2**63`. -/
def DictIterLen : Prop :=
  ∀ (K V : Type) (d : PyDict K V) (di : DictIter) (kind : IterKind) (rev : Bool),
    (d.used < 2 ^ 63 → dictiterLen d (dictiterNew d kind rev) = d.used) ∧
    (di.alive = false → dictiterLen d di = 0) ∧
    (di.used ≠ d.used → dictiterLen d di = 0) ∧
    (di.alive = true → di.used = d.used → 0 ≤ di.len → di.len < 2 ^ 63 →
      dictiterLen d di = di.len.toNat)

theorem dictIterLen_proven : DictIterLen := by
  intro K V d di kind rev
  refine ⟨fun hu => ?_, fun h => by simp [dictiterLen, h], fun h => by simp [dictiterLen, h],
    fun h1 h2 h3 h4 => ?_⟩
  · simp [dictiterLen, dictiterNew, toU64]
    omega
  · simp [dictiterLen, h1, h2, toU64]
    omega

end PyLean.DictSet
