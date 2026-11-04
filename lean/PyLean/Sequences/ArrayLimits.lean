import PyLean.Sequences.ArrayReentrant

/-!
`array.array`: what every size-changing method does while a buffer is exported, and the
explicit `MemoryError` checks of `newarrayobject` and the repeats.
-/

namespace PyLean.Sequences

open PyLean

set_option linter.unusedSectionVars false

theorem arrScan_some (a : Arr) (eqv : PyVal → Py Bool) (stop : Int) :
    ∀ (fuel : Nat) (i0 i : Int), arrScan a eqv stop fuel i0 = .ok (some i) → i0 ≤ i ∧ i < a.items.length := by
  intro fuel
  induction fuel with
  | zero => intro i0 i h; simp [arrScan] at h
  | succ f ih =>
    intro i0 i h
    unfold arrScan at h
    by_cases hc : i0 < stop ∧ i0 < a.items.length
    · rw [iteT hc] at h
      split at h
      · simp at h
      · split at h
        · simp at h
        · have : i0 = i := by simpa using h
          omega
        · have := ih _ _ h
          omega
    · rw [iteF hc] at h
      simp at h

/-- `array_del_slice(a, i, i+1)` for an index inside an exported array raises `BufferError`
(:1192-1196). -/
theorem arrDelSlice_exported (a : Arr) (i : Int) (hx : a.exports > 0) (h0 : 0 ≤ i)
    (h1 : i < a.items.length) : arrDelSlice a i (i + 1) = .error bufferErr := by
  unfold arrDelSlice
  simp only [bind, Except.bind, pure, Except.pure, throwE]
  have e1 : (if i < 0 then 0 else if i > (a.items.length : Int) then (a.items.length : Int) else i) = i := by
    split <;> (try split) <;> omega
  have e2 : (if i + 1 < 0 then 0 else i + 1) = i + 1 := by split <;> omega
  have e3 : (if i + 1 < i then i else if i + 1 > (a.items.length : Int) then (a.items.length : Int) else i + 1)
      = i + 1 := by
    split <;> (try split) <;> omega
  rw [e1, e2, e3, iteT ⟨by omega, hx⟩]

/-- While a buffer is exported, for every array (whose sizes fit, a type invariant):
`a.extend(b)`, `a += b` for a non-empty `b` of the same typecode raise `BufferError` from
the resize (arraymodule.c:1276-1277), after the overflow check; `a.remove(v)` raises
`BufferError` once it has found `v` (:1461-1462), after the comparison ran; `a.pop(i)` reads
the item first and then raises `BufferError` from the deletion (:1500-1506), or the read's own
error; `a.fromunicode(s)` of a non-empty `s` raises `BufferError` for `u`, and for `w` after the
`MemoryError` check (:2013-2034); `a *= n` raises the `MemoryError` of its two overflow checks
when one fails (:1313-1320), else `BufferError` (any `n` but 1, for a non-empty array). -/
def ArrayExportedResize : Prop :=
  ∀ a : Arr, a.exports > 0 →
    (∀ b : Arr, a.tc = b.tc → a.Fits (a.items.length + b.items.length) → b.items ≠ [] →
      arrDoExtendArr a b = .error bufferErr ∧ arrIConcat a (.inl b) = .error bufferErr ∧
      arrExtend a (.inl b) = (a, some bufferErr)) ∧
    (∀ (eqv : PyVal → Py Bool) (i : Int), arrScan a eqv a.items.length (a.items.length + 1) 0 = .ok (some i) →
      arrRemove a eqv = .error bufferErr) ∧
    (∀ i : Int, a.items ≠ [] →
      let j := if i < 0 then i + a.items.length else i
      0 ≤ j → j < a.items.length →
      (∀ v, a.get j = .ok v → arrPopK a i = .error bufferErr) ∧
      (∀ e, a.get j = .error e → arrPopK a i = .error e)) ∧
    (∀ s : List Nat, s ≠ [] →
      (a.tc = .u → arrFromUnicode a s = .error bufferErr) ∧
      (a.tc = .w → arrFromUnicode a s =
        .error (if (a.items.length : Int) + s.length > ssizeMax / 4 then memoryError else bufferErr))) ∧
    (∀ n : Int, a.items ≠ [] → n ≠ 1 →
      arrIRepeatC a n =
        .error (if (a.items.length : Int) > ssizeMax / a.tc.itemsize then memoryError
          else if max n 0 > 0 ∧ (a.items.length : Int) * a.tc.itemsize > ssizeMax / max n 0 then memoryError
          else bufferErr))

theorem arrayExportedResize_proven : ArrayExportedResize := by
  intro a hx
  have hlen0 : ∀ (l : List Int), l ≠ [] → (0 : Int) < l.length := fun l h => by
    cases l with
    | nil => exact absurd rfl h
    | cons _ _ => simp
  refine ⟨fun b ht hf hb => ?_, fun eqv i hs => ?_, fun i hne => ?_,
    fun s hs => ⟨fun hu => ?_, fun hw => ?_⟩, fun n hne hn1 => ?_⟩
  · have hpos := hlen0 b.items hb
    have hsz := itemsize_pos a.tc
    have hnm : ¬ ((a.items.length : Int) > ssizeMax - b.items.length ∨
        (a.items.length : Int) + b.items.length > ssizeMax / a.tc.itemsize) := by
      have : ssizeMax / a.tc.itemsize ≤ ssizeMax := Int.ediv_le_self _ (by unfold ssizeMax; omega)
      unfold Arr.Fits at hf; omega
    have hd : arrDoExtendArr a b = .error bufferErr := by
      have hnm' : ¬ ((a.items.length : Int) > ssizeMax - b.items.length ∨
          (a.items.length : Int) + b.items.length > ssizeMax / b.tc.itemsize) := by rw [← ht]; exact hnm
      unfold arrDoExtendArr
      simp only [bind, Except.bind, pure, Except.pure, throwE, ht, ne_eq, not_true_eq_false, ite_false]
      rw [iteF hnm', arrResize_exported a _ hx (by omega)]
    exact ⟨hd, by simp [arrIConcat, hd], by simp [arrExtend, hd]⟩
  · obtain ⟨h0, h1⟩ := arrScan_some a eqv _ _ 0 i hs
    unfold arrRemove
    rw [hs]
    exact arrDelSlice_exported a i hx h0 h1
  · dsimp only
    intro hj0 hj1
    have hn := hlen0 a.items hne
    refine ⟨fun v hv => ?_, fun e he => ?_⟩
    · unfold arrPopK
      simp only [bind, Except.bind, pure, Except.pure, throwE]
      rw [iteF (by omega), iteF (by omega), hv]
      simp only [arrDelSlice_exported a _ hx hj0 hj1]
    · unfold arrPopK
      simp only [bind, Except.bind, pure, Except.pure, throwE]
      rw [iteF (by omega), iteF (by omega), he]
  · have hpos : (0 : Int) < s.length := by
      cases s with
      | nil => exact absurd rfl hs
      | cons _ _ => simp
    unfold arrFromUnicode
    simp only [bind, Except.bind, pure, Except.pure, throwE, hu]
    simp (config := { decide := true }) only [ite_true, ite_false, ne_eq, not_true_eq_false, and_false,
      false_and]
    rw [iteT (show s.length > 0 by omega), arrResize_exported a _ hx (by omega)]
  · have hpos : (0 : Int) < s.length := by
      cases s with
      | nil => exact absurd rfl hs
      | cons _ _ => simp
    unfold arrFromUnicode
    simp only [bind, Except.bind, pure, Except.pure, throwE, hw]
    simp (config := { decide := true }) only [ite_true, ite_false, ne_eq, not_true_eq_false, and_false,
      false_and]
    by_cases hm : (a.items.length : Int) + s.length > ssizeMax / 4
    · rw [iteT hm, iteT hm]
    · rw [iteF hm, iteF hm, arrResize_exported a _ hx (by omega)]
  · have hpos := hlen0 a.items hne
    unfold arrIRepeatC
    simp only [bind, Except.bind, pure, Except.pure, throwE]
    rw [iteT ⟨hpos, hn1⟩]
    have hmx : (if n < 0 then 0 else n) = max n 0 := by split <;> omega
    rw [hmx]
    by_cases h1 : (a.items.length : Int) > ssizeMax / a.tc.itemsize
    · rw [iteT h1, iteT h1]
    · rw [iteF h1, iteF h1]
      by_cases h2 : max n 0 > 0 ∧ (a.items.length : Int) * a.tc.itemsize > ssizeMax / max n 0
      · rw [iteT h2, iteT h2]
      · rw [iteF h2, iteF h2]
        have hne' : max n 0 * (a.items.length : Int) ≠ a.items.length := by
          intro h
          have : (max n 0 - 1) * (a.items.length : Int) = 0 := by rw [Int.sub_mul]; omega
          rcases Int.mul_eq_zero.mp this with h3 | h3 <;> omega
        rw [arrResize_exported a _ hx hne']

/-- The explicit `MemoryError` checks before an allocation, for every typecode and size:
`newarrayobject` refuses exactly the sizes above `PY_SSIZE_T_MAX / itemsize` (:812-814) and
otherwise gives `size` items; `a * n` refuses `n > PY_SSIZE_T_MAX / len(a)` (:1152-1154) and then
a product above `PY_SSIZE_T_MAX / itemsize` through `newarrayobject`, e.g. `array('d', [0]) * 2**61`.
A product that passes both checks asks the allocator for up to `PY_SSIZE_T_MAX` bytes
(`array('b', [1]) * 2**62`), whose failure the model does not cover (it has no allocator). -/
def ArrayAllocLimits : Prop :=
  (∀ (t : String) (tc : TC) (size : Int), 0 ≤ size →
    (size > ssizeMax / tc.itemsize → newArr t tc size = .error memoryError) ∧
    (size ≤ ssizeMax / tc.itemsize → ∃ a, newArr t tc size = .ok a ∧ a.items = List.replicate size.toNat 0)) ∧
  (∀ (a : Arr) (n : Int), a.items ≠ [] → ssizeMin ≤ n → n ≤ ssizeMax →
    (max n 0 > ssizeMax / a.items.length → arrRepeat a n = .error memoryError) ∧
    (max n 0 ≤ ssizeMax / a.items.length → (a.items.length : Int) * max n 0 > ssizeMax / a.tc.itemsize →
      arrRepeat a n = .error memoryError))

theorem arrayAllocLimits_proven : ArrayAllocLimits := by
  refine ⟨fun t tc size h0 => ⟨fun h => ?_, fun h => ?_⟩, fun a n hne h0 h1 => ⟨fun h => ?_, fun h2 h3 => ?_⟩⟩
  · unfold newArr; rw [iteT h]
  · exact ⟨_, newArr_ok t tc size h, rfl⟩
  · have hpos : (0 : Int) < a.items.length := by
      cases ha : a.items with
      | nil => exact absurd ha hne
      | cons _ _ => simp
    have hrc : repeatCount n = .ok n := by unfold repeatCount asSsizeExc; rw [iteT ⟨h0, h1⟩]
    simp only [arrRepeat, hrc, arrRepeatC, bind, Except.bind, pure, Except.pure, throwE]
    have hmx : (if n < 0 then 0 else n) = max n 0 := by split <;> omega
    rw [hmx, iteT ⟨by omega, h⟩]
  · have hpos : (0 : Int) < a.items.length := by
      cases ha : a.items with
      | nil => exact absurd ha hne
      | cons _ _ => simp
    have hrc : repeatCount n = .ok n := by unfold repeatCount asSsizeExc; rw [iteT ⟨h0, h1⟩]
    simp only [arrRepeat, hrc, arrRepeatC, bind, Except.bind, pure, Except.pure, throwE]
    have hmx : (if n < 0 then 0 else n) = max n 0 := by split <;> omega
    rw [hmx, iteF (by omega)]
    unfold newArr
    rw [iteT h3]

/-! ### Search with a comparison that may raise -/

/-- The first position of `xs` (counted from `k`) whose item, read with `tcGetitem tc`, compares
true under `eqv`; the first exception of a read or a comparison ends the search. -/
def searchRef (tc : TC) (eqv : PyVal → Py Bool) : List Int → Nat → Py (Option Nat)
  | [], _ => .ok none
  | x :: xs, k =>
    match tcGetitem tc x with
    | .error e => .error e
    | .ok v =>
      match eqv v with
      | .error e => .error e
      | .ok true => .ok (some k)
      | .ok false => searchRef tc eqv xs (k + 1)

/-- How many items of `xs` compare true, reading and comparing in order; the first exception
ends the count. -/
def countRef (tc : TC) (eqv : PyVal → Py Bool) : List Int → Py Int
  | [] => .ok 0
  | x :: xs =>
    match tcGetitem tc x with
    | .error e => .error e
    | .ok v =>
      match eqv v with
      | .error e => .error e
      | .ok b => (countRef tc eqv xs).map (fun c => (if b then 1 else 0) + c)

theorem arrScan_ref (a : Arr) (eqv : PyVal → Py Bool) (stop : Int) (hs : (a.items.length : Int) ≤ stop) :
    ∀ (k i : Nat), i + k = a.items.length →
      arrScan a eqv stop (k + 1) i = (searchRef a.tc eqv (a.items.drop i) i).map (Option.map (fun n : Nat => (n : Int))) := by
  intro k
  induction k with
  | zero =>
    intro i hi
    rw [List.drop_eq_nil_of_le (by omega)]
    unfold arrScan
    rw [iteF (by omega)]
    rfl
  | succ k ih =>
    intro i hi
    have hlt : i < a.items.length := by omega
    rw [List.drop_eq_getElem_cons hlt]
    unfold arrScan
    rw [iteT ⟨by omega, by omega⟩]
    have hg : a.get i = tcGetitem a.tc a.items[i] := by
      unfold Arr.get; rw [ix_getElem _ _ hlt]
    rw [hg]
    simp only [searchRef]
    cases tcGetitem a.tc a.items[i] with
    | error e => rfl
    | ok v =>
      simp only
      cases eqv v with
      | error e => rfl
      | ok b =>
        cases b with
        | true => rfl
        | false =>
          simp only
          rw [show ((i : Int) + 1) = ((i + 1 : Nat) : Int) by omega]
          exact ih (i + 1) (by omega)

theorem arrCountLoop_ref (a : Arr) (eqv : PyVal → Py Bool) :
    ∀ (k i : Nat) (c : Int), i + k = a.items.length →
      arrCountLoop a eqv k i c = (countRef a.tc eqv (a.items.drop i)).map (fun r => c + r) := by
  intro k
  induction k with
  | zero =>
    intro i c hi
    rw [List.drop_eq_nil_of_le (by omega)]
    simp [arrCountLoop, countRef, Except.map]
  | succ k ih =>
    intro i c hi
    have hlt : i < a.items.length := by omega
    rw [List.drop_eq_getElem_cons hlt]
    unfold arrCountLoop
    have hg : a.get i = tcGetitem a.tc a.items[i] := by
      unfold Arr.get; rw [ix_getElem _ _ hlt]
    rw [hg]
    simp only [countRef]
    cases tcGetitem a.tc a.items[i] with
    | error e => rfl
    | ok v =>
      simp only
      cases eqv v with
      | error e => rfl
      | ok b =>
        simp only
        rw [show ((i : Int) + 1) = ((i + 1 : Nat) : Int) by omega, ih (i + 1) _ (by omega)]
        cases countRef a.tc eqv (a.items.drop (i + 1)) with
        | error e => rfl
        | ok r => simp only [Except.map]; congr 1; cases b <;> simp <;> omega

/-- `count`, `in`, `index` (no bounds) and `remove`, for every array (its items need not
decode) and every comparison `PyObject_RichCompareBool(item, v, Py_EQ)` that may raise: the
items are read with the typecode's getitem and compared in order, and the first exception, of a
read (an out-of-range `u`/`w` item, arraymodule.c:1356-1357, 1403-1404, 1428-1429, 1453-1454) or
of a comparison (:1360-1361, 1406-1407, 1431-1432, 1456-1457), is raised; no later item is
compared. `count` counts the true comparisons; `in`, `index` and `remove` stop at the first,
`remove` deleting it with `array_del_slice` (BufferError while exported). -/
def ArraySearchErrors : Prop :=
  ∀ (a : Arr) (eqv : PyVal → Py Bool), (a.items.length : Int) ≤ ssizeMax →
    arrCount a eqv = countRef a.tc eqv a.items ∧
    arrContains a eqv = (searchRef a.tc eqv a.items 0).map Option.isSome ∧
    arrIndex a eqv none none =
      (match searchRef a.tc eqv a.items 0 with
       | .error e => .error e
       | .ok (some k) => .ok (k : Int)
       | .ok none => .error (.valueError "array.index(x): x not in array")) ∧
    arrRemove a eqv =
      (match searchRef a.tc eqv a.items 0 with
       | .error e => .error e
       | .ok (some k) => arrDelSlice a k (k + 1)
       | .ok none => .error (.valueError "array.remove(x): x not in array"))

theorem arraySearchErrors_proven : ArraySearchErrors := by
  intro a eqv hl
  have hscan : ∀ stop : Int, (a.items.length : Int) ≤ stop →
      arrScan a eqv stop (a.items.length + 1) 0 =
        (searchRef a.tc eqv a.items 0).map (Option.map (fun n : Nat => (n : Int))) := by
    intro stop hs
    have := arrScan_ref a eqv stop hs a.items.length 0 (by omega)
    simpa using this
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold arrCount
    have h := arrCountLoop_ref a eqv a.items.length 0 0 (by omega)
    simp only [Int.natCast_zero, List.drop_zero] at h
    rw [h]
    cases countRef a.tc eqv a.items <;> simp [Except.map]
  · unfold arrContains
    rw [hscan _ (by omega)]
    cases searchRef a.tc eqv a.items 0 with
    | error e => rfl
    | ok r => cases r <;> rfl
  · unfold arrIndex
    have e0 : sliceIndex ((none : Option Int).getD 0) = 0 := by
      simp only [Option.getD_none, sliceIndex, RangeSlice.clampSsize]
      rw [iteF (by decide), iteF (by decide)]
    have e1 : sliceIndex ((none : Option Int).getD ssizeMax) = ssizeMax := by
      simp only [Option.getD_none, sliceIndex, RangeSlice.clampSsize]
      rw [iteF (by decide), iteF (by decide)]
    simp only [e0, e1]
    rw [iteF (by unfold ssizeMax; omega), iteF (by decide)]
    rw [hscan _ hl]
    cases searchRef a.tc eqv a.items 0 with
    | error e => rfl
    | ok r => cases r <;> rfl
  · unfold arrRemove
    rw [hscan _ (by omega)]
    cases searchRef a.tc eqv a.items 0 with
    | error e => rfl
    | ok r => cases r <;> rfl

end PyLean.Sequences
