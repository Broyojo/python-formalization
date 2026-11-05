import PyLean.RangeSlice.Objects

/-!
`x in r`, `r.count(x)` and `r.index(x)` for every object `x`, Objects/rangeobject.c,
CPython 3.15.2. An exact `int` or a `bool` takes the arithmetic path
(`range_contains_long`, pinned by `ContainsMem` and `IndexCount`); anything else, including
an instance of an `int` subclass, goes through `_PySequence_IterSearch`
(Objects/abstract.c:2138-2226), which iterates the range and calls
`PyObject_RichCompareBool(item, x, Py_EQ)` on each value.

That comparison is a callback that may raise and may run arbitrary Python code, re-entering
the range or anything else. It is modelled as a state transformer `EqHook σ` on an abstract
world `σ`, so a stateful or re-entrant `__eq__` (one that answers differently on each call,
counts its calls, or raises on the third) is expressible. Neither the range nor the search's
iterator is reachable from that world: range objects are immutable and the iterator is local
to `_PySequence_IterSearch`.

`_PySequence_IterSearch` is mirrored here rather than imported from
`PyLean.TypeObj.Protocol` (`pySequenceIterSearch`), whose world model of values and types
does not connect to this module's `Range`. The loop below follows the same lines of
abstract.c; `PyObject_GetIter` on a range is `range_iter`, which cannot fail, and the range
iterators' `next` cannot raise, so those two error branches (:2150-2162 and :2170-2171) do not
arise.
-/

namespace PyLean.RangeSlice

open PyLean

/-- `PY_ITERSEARCH_COUNT`, `PY_ITERSEARCH_INDEX`, `PY_ITERSEARCH_CONTAINS`. -/
inductive SearchOp where
  | count | index | contains
  deriving Repr, DecidableEq, Inhabited

/-- `PyObject_RichCompareBool(item, x, Py_EQ)` for the probe `x`, as a fallible callback on
an abstract world `σ` (the reflected `x.__eq__`, `int.__eq__`, the `PyObject_IsTrue` of
the result, and any Python code those run). -/
abbrev EqHook (σ : Type) := Int → σ → Py Bool × σ

/-- A comparison that does not depend on or change the world. -/
def pureHook (p : Int → Py Bool) : EqHook Unit := fun x w => (p x, w)

def notInSeq : PyExc := .valueError "sequence.index(x): x not in sequence"
def countOverflow : PyExc := .overflowError "count exceeds C integer size"
def indexOverflow : PyExc := .overflowError "index exceeds C integer size"

/-- The loop of `_PySequence_IterSearch`, Objects/abstract.c:2165-2218: `PyIter_Next`
(:2168); exhaustion ends the loop (:2169-2173), after which `INDEX` raises the `ValueError`
(:2214-2218) and the others return `n`; the comparison (:2175-2178), whose error propagates;
a hit counts with the `OverflowError` at `PY_SSIZE_T_MAX` (:2182-2188), ends `INDEX` with
`n` unless the counter wrapped (:2190-2196), and ends `CONTAINS` with 1 (:2198-2200); `INDEX`
advances its counter after a miss, remembering a wrap past `PY_SSIZE_T_MAX` (:2207-2211).
`n` is a `Py_ssize_t`, so `++n` at `PY_SSIZE_T_MAX` wraps (`-fno-strict-overflow`). -/
def searchLoop {σ : Type} (eq : EqHook σ) (op : SearchOp) :
    Nat → RIter → Int → Bool → σ → Py Int × σ
  | 0, _, _, _, w => (.error .modelFuel, w)
  | fuel + 1, it, n, wr, w =>
    match iterNext it with
    | none => (if op = .index then .error notInSeq else .ok n, w)
    | some (item, it') =>
      match eq item w with
      | (.error e, w') => (.error e, w')
      | (.ok true, w') =>
        match op with
        | .count =>
          if n = ssizeMax then (.error countOverflow, w')
          else searchLoop eq op fuel it' (n + 1) wr w'
        | .index => if wr then (.error indexOverflow, w') else (.ok n, w')
        | .contains => (.ok 1, w')
      | (.ok false, w') =>
        if op = .index then
          searchLoop eq op fuel it' (if n = ssizeMax then ssizeMin else n + 1)
            (wr || decide (n = ssizeMax)) w'
        else searchLoop eq op fuel it' n wr w'

/-- `_PySequence_IterSearch(r, x, op)`, Objects/abstract.c:2138-2226, on a range: the
iterator is `range_iter`'s (:2149), which yields `r.length` values, so `r.length + 1` steps
of fuel always suffice (`iterSearch_elems`). -/
def iterSearch {σ : Type} (eq : EqHook σ) (op : SearchOp) (r : Range) (w : σ) : Py Int × σ :=
  searchLoop eq op (r.length.toNat + 1) (rangeIter r) 0 false w

/-- An exact `int` or a `bool` (`PyLong_CheckExact(ob) || PyBool_Check(ob)`), with its value. -/
def Obj.exactIntOrBool : Obj → Option Int
  | .int v => some v
  | .bool b => some (if b then 1 else 0)
  | _ => none

/-- `x in r`: `range_contains`, rangeobject.c:504-512 (`sq_contains`; `in` makes the 0 or 1 a
`bool`). -/
def rangeContainsObj {σ : Type} (r : Range) (ob : Obj) (eq : EqHook σ) (w : σ) : Py Bool × σ :=
  match ob.exactIntOrBool with
  | some v => (.ok (rangeContainsLong r v), w)
  | none =>
    let (res, w') := iterSearch eq .contains r w
    (res.map (fun n => n != 0), w')

/-- `r.count(x)`: `range_count`, rangeobject.c:631-646. -/
def rangeCountObj {σ : Type} (r : Range) (ob : Obj) (eq : EqHook σ) (w : σ) : Py Int × σ :=
  match ob.exactIntOrBool with
  | some v => (.ok (rangeCount r v), w)
  | none => iterSearch eq .count r w

/-- `r.index(x)`: `range_index`, rangeobject.c:649-685 (the search branch, :654-660, comes
first). -/
def rangeIndexObj {σ : Type} (r : Range) (ob : Obj) (eq : EqHook σ) (w : σ) : Py Int × σ :=
  match ob.exactIntOrBool with
  | none => iterSearch eq .index r w
  | some v => (rangeIndex r v, w)

/-! ### The search, over the list of elements -/

/-- `_PySequence_IterSearch`'s loop over a list of values. -/
def listSearch {σ : Type} (eq : EqHook σ) (op : SearchOp) :
    List Int → Int → Bool → σ → Py Int × σ
  | [], n, _, w => (if op = .index then .error notInSeq else .ok n, w)
  | item :: xs, n, wr, w =>
      match eq item w with
      | (.error e, w') => (.error e, w')
      | (.ok true, w') =>
        match op with
        | .count =>
          if n = ssizeMax then (.error countOverflow, w')
          else listSearch eq op xs (n + 1) wr w'
        | .index => if wr then (.error indexOverflow, w') else (.ok n, w')
        | .contains => (.ok 1, w')
      | (.ok false, w') =>
        if op = .index then
          listSearch eq op xs (if n = ssizeMax then ssizeMin else n + 1)
            (wr || decide (n = ssizeMax)) w'
        else listSearch eq op xs n wr w'

/-- The elements `r[0], ..., r[L-1]`. -/
def elems (r : Range) (L : Int) : List Int := (List.range L.toNat).map (fun k : Nat => r.elem k)

theorem elems_length (r : Range) (L : Int) : (elems r L).length = L.toNat := by simp [elems]

theorem elems_getElem (r : Range) (L : Int) (k : Nat) (hk : k < (elems r L).length) :
    (elems r L)[k] = r.elem k := by simp [elems]

theorem searchLoop_list {σ : Type} (eq : EqHook σ) (op : SearchOp) :
    ∀ (fuel : Nat) (it : RIter) (n : Int) (wr : Bool) (w : σ),
      (iterTake fuel it).1.length < fuel →
      searchLoop eq op fuel it n wr w = listSearch eq op (iterTake fuel it).1 n wr w := by
  intro fuel
  induction fuel with
  | zero => intro it n wr w h; simp at h
  | succ fuel ih =>
    intro it n wr w h
    cases hn : iterNext it with
    | none => simp [searchLoop, iterTake, hn, listSearch]
    | some p =>
      obtain ⟨x, it'⟩ := p
      have ht : (iterTake (fuel + 1) it).1 = x :: (iterTake fuel it').1 := by
        simp only [iterTake, hn]
      rw [ht] at h ⊢
      simp only [List.length_cons] at h
      have h' : (iterTake fuel it').1.length < fuel := by omega
      simp only [searchLoop, hn, listSearch]
      rcases hq : eq x w with ⟨res, w'⟩
      cases res with
      | error e => rfl
      | ok b =>
        cases b <;> cases op <;> simp [ih _ _ _ _ h']

/-- **The search visits exactly the elements, in order.** For every range (`r.WF`,
mathematical length `L`), every operation and every comparison callback with any state,
`_PySequence_IterSearch` on `r` is the search over `r[0], ..., r[L-1]`: the iterator yields
them, the world is threaded through the calls in that order, and the fuel never runs out. -/
theorem iterSearch_elems {σ : Type} (eq : EqHook σ) (op : SearchOp) (r : Range) (L : Int)
    (w : σ) (hw : r.WF) (hL : r.Len L) :
    iterSearch eq op r w = listSearch eq op (elems r L) 0 false w := by
  have hlen := hw.length_eq hL
  have hf := iterForward_proven r L (r.length.toNat + 1) hw hL
  have hmin : min (r.length.toNat + 1) L.toNat = L.toNat := by rw [hlen]; omega
  rw [hmin] at hf
  unfold iterSearch
  rw [searchLoop_list eq op _ _ _ _ _ (by rw [hf, List.length_map, List.length_range, hlen]; omega), hf]
  rfl

/-! ### Exact results for a comparison without state -/

section pure

variable (p : Int → Py Bool)

theorem ls_contains_none : ∀ (xs : List Int) (n : Int) (wr : Bool),
    (∀ x ∈ xs, p x = .ok false) → listSearch (pureHook p) .contains xs n wr () = (.ok n, ()) := by
  intro xs
  induction xs with
  | nil => intro n wr _; rfl
  | cons x xs ih =>
    intro n wr h
    have hx := h x (by simp)
    simp only [listSearch, pureHook, hx]
    exact ih n wr (fun y hy => h y (by simp [hy]))

theorem ls_contains_hit : ∀ (xs : List Int) (k : Nat) (hk : k < xs.length) (n : Int) (wr : Bool)
    (r : Py Bool), (∀ x ∈ xs.take k, p x = .ok false) → p xs[k] = r → r ≠ .ok false →
    listSearch (pureHook p) .contains xs n wr () =
      (match r with | .error e => .error e | .ok _ => .ok 1, ()) := by
  intro xs
  induction xs with
  | nil => intro k hk; simp at hk
  | cons x xs ih =>
    intro k hk n wr r hpre hk' hr
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero] at hk'
      simp only [listSearch, pureHook, hk']
      rcases r with e | b
      · rfl
      · cases b
        · exact absurd rfl hr
        · rfl
    | succ k =>
      have hx := hpre x (by simp)
      simp only [listSearch, pureHook, hx]
      exact ih k (by simp at hk; omega) n wr r (fun y hy => hpre y (by simp [hy])) (by simpa using hk') hr

theorem ls_index_none : ∀ (xs : List Int) (n : Int) (wr : Bool),
    (∀ x ∈ xs, p x = .ok false) → listSearch (pureHook p) .index xs n wr () = (.error notInSeq, ()) := by
  intro xs
  induction xs with
  | nil => intro n wr _; rfl
  | cons x xs ih =>
    intro n wr h
    have hx := h x (by simp)
    simp only [listSearch, pureHook, hx, ↓reduceIte]
    exact ih _ _ (fun y hy => h y (by simp [hy]))

theorem ls_index_err : ∀ (xs : List Int) (k : Nat) (hk : k < xs.length) (n : Int) (wr : Bool)
    (e : PyExc), (∀ x ∈ xs.take k, p x = .ok false) → p xs[k] = .error e →
    listSearch (pureHook p) .index xs n wr () = (.error e, ()) := by
  intro xs
  induction xs with
  | nil => intro k hk; simp at hk
  | cons x xs ih =>
    intro k hk n wr e hpre hk'
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero] at hk'
      simp only [listSearch, pureHook, hk']
    | succ k =>
      have hx := hpre x (by simp)
      simp only [listSearch, pureHook, hx, ↓reduceIte]
      exact ih k (by simp at hk; omega) _ _ e (fun y hy => hpre y (by simp [hy])) (by simpa using hk')

/-- The `INDEX` counter after `j` misses from 0: `j` until it wraps, and the wrap flag
records whether `j` passed `PY_SSIZE_T_MAX`. -/
theorem ls_index_hit : ∀ (xs : List Int) (k : Nat) (hk : k < xs.length) (j n : Int) (wr : Bool),
    (j ≤ ssizeMax → n = j) → wr = decide (ssizeMax < j) →
    (∀ x ∈ xs.take k, p x = .ok false) → p xs[k] = .ok true →
    listSearch (pureHook p) .index xs n wr () =
      (if j + k ≤ ssizeMax then .ok (j + k) else .error indexOverflow, ()) := by
  intro xs
  induction xs with
  | nil => intro k hk; simp at hk
  | cons x xs ih =>
    intro k hk j n wr hn hwr hpre hk'
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero] at hk'
      simp only [listSearch, pureHook, hk']
      subst hwr
      by_cases hj : j ≤ ssizeMax
      · rw [hn hj]; simp [show ¬ ssizeMax < j by omega, hj]
      · simp [show ssizeMax < j by omega]
    | succ k =>
      have hx := hpre x (by simp)
      simp only [listSearch, pureHook, hx, ↓reduceIte]
      have e : j + ((k + 1 : Nat) : Int) = (j + 1) + (k : Int) := by push_cast; omega
      rw [e]
      refine ih k (by simp at hk; omega) (j + 1) _ _ ?_ ?_ (fun y hy => hpre y (by simp [hy]))
        (by simpa using hk')
      · intro hj1
        rw [hn (by omega)]
        simp [show j ≠ ssizeMax by omega]
      · subst hwr
        by_cases hj : j ≤ ssizeMax
        · rw [hn hj]
          by_cases hjm : j = ssizeMax
          · simp [hjm, ssizeMax]
          · simp [hjm]; omega
        · simp [show ssizeMax < j by omega, show ssizeMax < j + 1 by omega]

/-- The number of hits. -/
def hits (xs : List Int) : Nat := xs.countP (fun x => decide (p x = .ok true))

theorem ls_count_all : ∀ (xs : List Int) (n : Int) (wr : Bool),
    (∀ x ∈ xs, ∃ b, p x = .ok b) → n + hits p xs ≤ ssizeMax →
    listSearch (pureHook p) .count xs n wr () = (.ok (n + hits p xs), ()) := by
  intro xs
  induction xs with
  | nil => intro n wr _ _; simp [listSearch, hits]
  | cons x xs ih =>
    intro n wr h hc
    obtain ⟨b, hb⟩ := h x (by simp)
    have hrest : ∀ y ∈ xs, ∃ b, p y = .ok b := fun y hy => h y (by simp [hy])
    cases b with
    | false =>
      have hh : hits p (x :: xs) = hits p xs := by simp [hits, hb]
      rw [hh] at hc ⊢
      simp only [listSearch, pureHook, hb]
      exact ih n wr hrest hc
    | true =>
      have hh : hits p (x :: xs) = hits p xs + 1 := by simp [hits, hb]
      rw [hh] at hc ⊢
      simp only [listSearch, pureHook, hb, show n ≠ ssizeMax by omega, ↓reduceIte]
      rw [ih (n + 1) wr hrest (by push_cast at hc ⊢; omega)]
      congr 2; push_cast; omega

theorem ls_count_stop : ∀ (xs : List Int) (k : Nat) (hk : k < xs.length) (n : Int) (wr : Bool),
    (∀ x ∈ xs.take k, ∃ b, p x = .ok b) →
    ((∀ e, p xs[k] = .error e → n + hits p (xs.take k) ≤ ssizeMax →
        listSearch (pureHook p) .count xs n wr () = (.error e, ())) ∧
     (n + hits p (xs.take k) = ssizeMax → p xs[k] = .ok true →
        listSearch (pureHook p) .count xs n wr () = (.error countOverflow, ()))) := by
  intro xs
  induction xs with
  | nil => intro k hk; simp at hk
  | cons x xs ih =>
    intro k hk n wr hpre
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero, List.take_zero, hits, List.countP_nil, Int.natCast_zero,
        Int.add_zero]
      refine ⟨fun e he _ => ?_, fun hn ht => ?_⟩
      · simp only [listSearch, pureHook, he]
      · simp only [listSearch, pureHook, ht, hn, ↓reduceIte]
    | succ k =>
      obtain ⟨b, hb⟩ := hpre x (by simp)
      have hrest : ∀ y ∈ xs.take k, ∃ b, p y = .ok b := fun y hy => hpre y (by simp [hy])
      have hk2 : k < xs.length := by simp at hk; omega
      have hget : (x :: xs)[k + 1] = xs[k] := by simp
      rw [hget]
      cases b with
      | false =>
        have hh : hits p ((x :: xs).take (k + 1)) = hits p (xs.take k) := by
          simp [hits, hb]
        rw [hh]
        simp only [listSearch, pureHook, hb]
        exact ih k hk2 n wr hrest
      | true =>
        have hh : hits p ((x :: xs).take (k + 1)) = hits p (xs.take k) + 1 := by
          simp [hits, hb]
        rw [hh]
        have := ih k hk2 (n + 1) wr hrest
        refine ⟨fun e he hc => ?_, fun hn ht => ?_⟩
        · simp only [listSearch, pureHook, hb, show n ≠ ssizeMax by push_cast at hc; omega, ↓reduceIte]
          exact this.1 e he (by push_cast at hc ⊢; omega)
        · simp only [listSearch, pureHook, hb, show n ≠ ssizeMax by push_cast at hn; omega, ↓reduceIte]
          exact this.2 (by push_cast at hn ⊢; omega) ht

end pure

/-- **`_PySequence_IterSearch` on a range, exact results** for a comparison that does not
depend on state (a `float`, an `int` subclass, a class whose `__eq__` is a function of its
argument; `xs` is `[r[0], ..., r[L-1]]`, `elems_getElem`). For `in` and `index`, what
matters is the first element whose comparison is not `False`: none gives 0 and the
`ValueError`; a `True` at position `k` gives 1 and `k` (or the `OverflowError` once `k`
passed `PY_SSIZE_T_MAX`); an exception there propagates, unchanged. For `count`, with no
exception the result is the number of `True`s (up to `PY_SSIZE_T_MAX`); the first exception
propagates; and the `PY_SSIZE_T_MAX + 1`-th `True` is the `OverflowError`. For every range
(`r.WF`, mathematical length `L`) and every comparison, `fun _ => .error` and "always the
first element" both fail it. -/
def SearchPureExact : Prop :=
  ∀ (r : Range) (L : Int) (p : Int → Py Bool), r.WF → r.Len L →
    let xs := elems r L
    let run := fun op => (iterSearch (pureHook p) op r ()).1
    ((∀ x ∈ xs, p x = .ok false) → run .contains = .ok 0 ∧ run .index = .error notInSeq) ∧
    (∀ (k : Nat) (hk : k < xs.length), (∀ x ∈ xs.take k, p x = .ok false) →
      (p xs[k] = .ok true → run .contains = .ok 1 ∧
        run .index = (if (k : Int) ≤ ssizeMax then .ok (k : Int) else .error indexOverflow)) ∧
      (∀ e, p xs[k] = .error e → run .contains = .error e ∧ run .index = .error e)) ∧
    ((∀ x ∈ xs, ∃ b, p x = .ok b) → (hits p xs : Int) ≤ ssizeMax →
      run .count = .ok (hits p xs : Int)) ∧
    (∀ (k : Nat) (hk : k < xs.length), (∀ x ∈ xs.take k, ∃ b, p x = .ok b) →
      (∀ e, p xs[k] = .error e → (hits p (xs.take k) : Int) ≤ ssizeMax → run .count = .error e) ∧
      ((hits p (xs.take k) : Int) = ssizeMax → p xs[k] = .ok true → run .count = .error countOverflow))

theorem searchPureExact_proven : SearchPureExact := by
  intro r L p hw hL xs run
  have hrun : ∀ op, run op = (listSearch (pureHook p) op xs 0 false ()).1 := by
    intro op; show (iterSearch (pureHook p) op r ()).1 = _; rw [iterSearch_elems _ _ r L () hw hL]
  refine ⟨fun h => ?_, fun k hk hpre => ⟨fun ht => ?_, fun e he => ?_⟩, fun h hc => ?_,
    fun k hk hpre => ⟨fun e he hc => ?_, fun hc ht => ?_⟩⟩
  · rw [hrun, hrun, ls_contains_none p xs 0 false h, ls_index_none p xs 0 false h]; exact ⟨rfl, rfl⟩
  · rw [hrun, hrun, ls_contains_hit p xs k hk 0 false _ hpre ht (by simp),
      ls_index_hit p xs k hk 0 0 false (fun _ => rfl) (by simp [ssizeMax]) hpre ht]
    simp
  · rw [hrun, hrun, ls_contains_hit p xs k hk 0 false _ hpre he (by simp),
      ls_index_err p xs k hk 0 false e hpre he]
    exact ⟨rfl, rfl⟩
  · rw [hrun, ls_count_all p xs 0 false h (by omega)]; simp
  · rw [hrun, (ls_count_stop p xs k hk 0 false hpre).1 e he (by omega)]
  · rw [hrun, (ls_count_stop p xs k hk 0 false hpre).2 (by omega) ht]

theorem containsObj_search {σ : Type} (r : Range) (ob : Obj) (eq : EqHook σ) (w : σ)
    (hob : ob.exactIntOrBool = none) :
    rangeContainsObj r ob eq w =
      ((iterSearch eq .contains r w).1.map (fun n => n != 0), (iterSearch eq .contains r w).2) := by
  simp only [rangeContainsObj, hob]

theorem countObj_search {σ : Type} (r : Range) (ob : Obj) (eq : EqHook σ) (w : σ)
    (hob : ob.exactIntOrBool = none) : rangeCountObj r ob eq w = iterSearch eq .count r w := by
  simp only [rangeCountObj, hob]

theorem indexObj_search {σ : Type} (r : Range) (ob : Obj) (eq : EqHook σ) (w : σ)
    (hob : ob.exactIntOrBool = none) : rangeIndexObj r ob eq w = iterSearch eq .index r w := by
  simp only [rangeIndexObj, hob]

/-- **The exact type check, and the order of the comparisons.** For every range (`r.WF`,
mathematical length `L`), every comparison callback with any state, and every object: an
exact `int` or a `bool` takes the arithmetic path with its value (pinned by `ContainsMem` and
`IndexCount`) and never runs the callback, so the world is unchanged; any other object, an
`int` subclass instance included, runs `_PySequence_IterSearch` over `r[0], ..., r[L-1]` in
order, threading the world through the calls, `in` reporting a non-zero result as `True`. -/
def SearchDispatch : Prop :=
  ∀ (σ : Type) (r : Range) (L : Int) (eq : EqHook σ) (w : σ) (ob : Obj), r.WF → r.Len L →
    (∀ v, ob.exactIntOrBool = some v →
      rangeContainsObj r ob eq w = (.ok (rangeContainsLong r v), w) ∧
      rangeCountObj r ob eq w = (.ok (rangeCount r v), w) ∧
      rangeIndexObj r ob eq w = (rangeIndex r v, w)) ∧
    (ob.exactIntOrBool = none →
      rangeContainsObj r ob eq w =
        ((listSearch eq .contains (elems r L) 0 false w).1.map (fun n => n != 0),
         (listSearch eq .contains (elems r L) 0 false w).2) ∧
      rangeCountObj r ob eq w = listSearch eq .count (elems r L) 0 false w ∧
      rangeIndexObj r ob eq w = listSearch eq .index (elems r L) 0 false w)

theorem searchDispatch_proven : SearchDispatch := by
  intro σ r L eq w ob hw hL
  refine ⟨fun v hv => ?_, fun hv => ?_⟩
  · simp [rangeContainsObj, rangeCountObj, rangeIndexObj, hv]
  · rw [containsObj_search r ob eq w hv, countObj_search r ob eq w hv, indexObj_search r ob eq w hv]
    simp only [iterSearch_elems eq _ r L w hw hL]
    exact ⟨trivial, trivial, trivial⟩

/-- `Obj.exactIntOrBool` is `none` for an instance of an `int` subclass: the check is
`PyLong_CheckExact`, not `PyLong_Check`. -/
theorem exactIntOrBool_intSub (v : Int) (tp : String) : (Obj.intSub v tp).exactIntOrBool = none := rfl

theorem mem_elems (r : Range) (L v : Int) : v ∈ elems r L ↔ r.MemL L v := by
  unfold elems Range.MemL
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, by omega, by omega, rfl⟩
  · rintro ⟨k, hk0, hkL, rfl⟩; exact ⟨k.toNat, by omega, by rw [Int.toNat_of_nonneg hk0]⟩

theorem elems_nodup (r : Range) (L : Int) (hs : r.step ≠ 0) : (elems r L).Nodup := by
  unfold elems List.Nodup
  rw [List.pairwise_map]
  exact List.nodup_range.imp (fun {a b} hab h => hab (by have := elem_inj hs h; omega))

/-- The value-equality comparison with `v`. -/
def eqHook (v : Int) : EqHook Unit := pureHook (fun x => .ok (decide (x = v)))

theorem ls_count_absent (v : Int) : ∀ (xs : List Int) (n : Int) (wr : Bool), v ∉ xs →
    listSearch (eqHook v) .count xs n wr () = (.ok n, ()) := by
  intro xs
  induction xs with
  | nil => intro n wr _; rfl
  | cons x xs ih =>
    intro n wr h
    have hx : x ≠ v := fun e => h (e ▸ List.mem_cons_self ..)
    simp only [listSearch, eqHook, pureHook, hx, decide_false]
    exact ih n wr (fun hm => h (List.mem_cons_of_mem _ hm))

theorem ls_count_present (v : Int) : ∀ (xs : List Int) (n : Int) (wr : Bool), xs.Nodup → v ∈ xs →
    n < ssizeMax → listSearch (eqHook v) .count xs n wr () = (.ok (n + 1), ()) := by
  intro xs
  induction xs with
  | nil => intro n wr _ h; simp at h
  | cons x xs ih =>
    intro n wr hnd hm hn
    rw [List.nodup_cons] at hnd
    by_cases hx : x = v
    · subst hx
      simp only [listSearch, eqHook, pureHook, decide_true, show n ≠ ssizeMax by omega, ↓reduceIte]
      exact ls_count_absent x xs (n + 1) wr hnd.1
    · have hm' : v ∈ xs := by
        rcases List.mem_cons.mp hm with h | h
        · exact absurd h.symm hx
        · exact h
      simp only [listSearch, eqHook, pureHook, hx, decide_false]
      exact ih n wr hnd.2 hm' hn

/-- **The two paths agree on `in` and `count`, and differ on `index` only in the message.**
For a probe on the search path whose comparison is value equality with `v` (a `float` equal
to `v`, an `int` subclass instance keeping `int.__eq__`, a class whose `__eq__` compares with
`v`), `x in r` and `r.count(x)` equal what the arithmetic path gives for the int `v`;
`r.index(x)` returns the same position when `v` is an element (or the `OverflowError` once
that position passed `PY_SSIZE_T_MAX`), and for a non-element raises `ValueError` with the
generic `_PySequence_IterSearch` message instead of `range_index`'s own. For every range and
every such probe. -/
def SearchTwin : Prop :=
  ∀ (r : Range) (L v : Int) (ob : Obj), r.WF → r.Len L → ob.exactIntOrBool = none →
    (rangeContainsObj r ob (eqHook v) ()).1 = (rangeContainsObj r (.int v) (eqHook v) ()).1 ∧
    (rangeCountObj r ob (eqHook v) ()).1 = (rangeCountObj r (.int v) (eqHook v) ()).1 ∧
    (∀ k, rangeIndex r v = .ok k →
      (rangeIndexObj r ob (eqHook v) ()).1 = if k ≤ ssizeMax then .ok k else .error indexOverflow) ∧
    (rangeIndex r v = .error (.valueError "range.index(x): x not in range") →
      (rangeIndexObj r ob (eqHook v) ()).1 = .error notInSeq)

theorem searchTwin_proven : SearchTwin := by
  intro r L v ob hw hL hob
  have hs := hw.1
  have hL0 := hL.1
  have hcm := containsMem_proven r L v hw hL
  have hic := indexCount_proven r L v hw hL
  have hsp := searchPureExact_proven r L (fun x => .ok (decide (x = v))) hw hL
  simp only at hsp
  obtain ⟨hnone, hhit, -, -⟩ := hsp
  rw [containsObj_search r ob _ () hob, countObj_search r ob _ () hob, indexObj_search r ob _ () hob]
  simp only [rangeContainsObj, rangeCountObj, Obj.exactIntOrBool]
  rw [iterSearch_elems _ .count r L () hw hL]
  by_cases hm : r.MemL L v
  · have hm2 := hm
    obtain ⟨k, hk0, hkL, hkv⟩ := hm2
    have hkn : k.toNat < (elems r L).length := by rw [elems_length]; omega
    have hget : (elems r L)[k.toNat] = v := by
      rw [elems_getElem, hkv]; congr 1; omega
    have hpre : ∀ x ∈ (elems r L).take k.toNat,
        (Except.ok (decide (x = v)) : Py Bool) = .ok false := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      rw [List.getElem_take, elems_getElem]
      have hik : i < k.toNat := by simp at hi; omega
      have : r.elem (i : Int) ≠ v := by
        intro hjv; rw [hkv] at hjv; have := elem_inj hs hjv; omega
      simp [this]
    obtain ⟨hc1, hi1⟩ := (hhit k.toNat hkn hpre).1 (by rw [hget]; simp)
    have hin : rangeContainsLong r v = true := hcm.2 hm
    refine ⟨?_, ?_, fun k' hk' => ?_, fun he => ?_⟩
    · show Except.map _ (iterSearch (eqHook v) .contains r ()).1 = _
      rw [show (iterSearch (eqHook v) .contains r ()).1 = .ok 1 from hc1, hin]; rfl
    · rw [ls_count_present v _ 0 false (elems_nodup r L hs) ((mem_elems r L v).2 hm) (by decide),
        hic.2.2.1 hm]
      rfl
    · obtain ⟨hk'0, hk'L, hk'v⟩ := (hic.1 k').1 hk'
      have : k' = k := elem_inj hs (by rw [hk'v, hkv])
      subst this
      show (iterSearch (eqHook v) .index r ()).1 = _
      rw [show (iterSearch (eqHook v) .index r ()).1 = _ from hi1, Int.toNat_of_nonneg hk'0]
    · exact absurd hm (hic.2.1.1 he)
  · have hall : ∀ x ∈ elems r L, (Except.ok (decide (x = v)) : Py Bool) = .ok false := by
      intro x hx
      have : x ≠ v := fun e => hm ((mem_elems r L v).1 (e ▸ hx))
      simp [this]
    obtain ⟨hc0, hi0⟩ := hnone hall
    have hin : rangeContainsLong r v = false := by
      cases h : rangeContainsLong r v
      · rfl
      · exact absurd (hcm.1 h) hm
    refine ⟨?_, ?_, fun k' hk' => ?_, fun _ => ?_⟩
    · show Except.map _ (iterSearch (eqHook v) .contains r ()).1 = _
      rw [show (iterSearch (eqHook v) .contains r ()).1 = .ok 0 from hc0, hin]; rfl
    · rw [ls_count_absent v _ 0 false (fun h => hm ((mem_elems r L v).1 h)), hic.2.2.2 hm]
    · obtain ⟨hk'0, hk'L, hk'v⟩ := (hic.1 k').1 hk'
      exact absurd ⟨k', hk'0, hk'L, hk'v.symm⟩ hm
    · exact hi0

end PyLean.RangeSlice
