import PyLean.Sequences.ArrayReModel
import PyLean.Sequences.ArrayOps

/-!
`array.array` with item conversions that run Python code (`ArrayReModel`): the re-check
`CHECK_ARRAY_BOUNDS` of every integer `*_setitem` after `__index__`, and the stale size of
`ins1`.
-/

namespace PyLean.Sequences

open PyLean

set_option linter.unusedSectionVars false

/-! ### Shapes -/

/-- A successful `array_resize` to a positive size leaves a buffer and the same descriptor. -/
theorem arrResize_pos (a a' : Arr) (m : Int) (h : arrResize a m = .ok a') (hm : 0 < m) :
    a'.hasBuf = true ∧ a'.tc = a.tc ∧ (a'.items.length : Int) = m ∧ a'.exports = a.exports ∧
      a'.tname = a.tname := by
  unfold arrResize at h
  dsimp only at h
  repeat' split at h
  all_goals (try (injection h with h; subst h))
  all_goals first
    | (simp at h; done)
    | omega
    | exact ⟨by simp_all, rfl, length_resized _ _ (by omega), rfl, rfl⟩
    | exact ⟨rfl, rfl, length_resized _ _ (by omega), rfl, rfl⟩

theorem memmove_length {α : Type} (mem r : List α) (d s c : Int) (h : memmove mem d s c = .ok r) :
    r.length = mem.length := by
  unfold memmove at h
  split at h
  · rename_i hc
    have : r = mem.take d.toNat ++ (mem.drop s.toNat).take c.toNat ++ mem.drop (d + c).toNat := by
      simpa using h.symm
    subst this
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  · simp at h

/-! ### Items that change nothing -/

/-- With an item that leaves the array alone, `ins1` is `arrIns1S`. -/
theorem arrIns1Re_pure (a : Arr) (w : Int) (v : PyVal) :
    arrIns1Re a w (ReVal.pure v) = arrIns1S a w v := by
  unfold arrIns1Re arrIns1S setitemRe ReVal.pure
  dsimp only
  simp only [storeAfter, show ((-1 : Int) < 0) from by decide, ite_true]
  cases hc : tcCheck a.tc v with
  | error e => rfl
  | ok u =>
    simp only
    cases hr : arrResize a ((a.items.length : Int) + 1) with
    | error e => rfl
    | ok a2 =>
      simp only
      obtain ⟨hb, ht, hl, _⟩ := arrResize_pos a a2 _ hr (by omega)
      have hw := ins1Pos_bounds (a.items.length : Int) w (by omega)
      generalize ins1Pos (a.items.length : Int) w = W at hw ⊢
      cases hm : (if W ≠ (a.items.length : Int) then memmove a2.items (W + 1) W ((a.items.length : Int) - W)
          else .ok a2.items : Py (List Int)) with
      | error e => rfl
      | ok items =>
        simp only
        have hlen : items.length = a2.items.length := by
          split at hm
          · exact memmove_length _ _ _ _ _ hm
          · injection hm with hm; rw [← hm]
        rw [iteF (show ¬ W < 0 by omega)]
        have hW : W < (items.length : Int) := by omega
        cases hs : tcSetitem a.tc true v <;> simp [hb, ht, hW, hs]

theorem arrAppendRe_pure (a : Arr) (v : PyVal) : arrAppendRe a (ReVal.pure v) = arrAppendS a v :=
  arrIns1Re_pure a _ v

theorem arrInsertRe_pure (a : Arr) (i : Int) (v : PyVal) :
    arrInsertRe a i (ReVal.pure v) = arrInsertS a i v := by
  unfold arrInsertRe arrInsertS
  cases asSsize i with
  | error e => rfl
  | ok i => exact arrIns1Re_pure a i v

theorem arrIterItemsRe_pure (vs : List PyVal) :
    ∀ a, arrIterItemsRe a (vs.map ReVal.pure) = arrIterItems a vs := by
  induction vs with
  | nil => intro a; rfl
  | cons v vs ih =>
    intro a
    simp only [List.map_cons, arrIterItemsRe, arrIterItems, arrIns1Re_pure]
    cases arrIns1S a a.items.length v with
    | mk a' r => cases r <;> simp [ih]

/-- `a[i] = v` with an item that leaves the array alone is `arrAssIndex`, for every array
with the allocation invariant (a NULL buffer only when empty). -/
theorem arrAssIndexRe_pure (a : Arr) (i : Int) (v : PyVal) (ha : a.Alloc) :
    arrAssIndexRe a i (ReVal.pure v) =
      match arrAssIndex a i (some v) with
      | .ok a' => (a', .ok ())
      | .error e => (a, .error e) := by
  unfold arrAssIndexRe arrAssIndex
  cases subIndex i with
  | error e => rfl
  | ok j =>
    simp only [bind, Except.bind, pure, Except.pure, throwE]
    generalize (if j < 0 then j + (a.items.length : Int) else j) = k
    by_cases hk : k < 0 ∨ k ≥ (a.items.length : Int)
    · rw [iteT hk, iteT hk]
    · rw [iteF hk, iteF hk]
      have hb : a.hasBuf = true := by
        cases hh : a.hasBuf
        · have := ha.2 hh; rw [this] at hk; simp at hk; omega
        · rfl
      simp only [setitemRe, ReVal.pure, storeAfter]
      rw [iteF (show ¬ k < 0 by omega)]
      have hk' : k < (a.items.length : Int) := by omega
      cases hs : tcSetitem a.tc true v <;> simp [hb, hk', hs]

/-! ### The re-check after `__index__` -/

/-- What the conversion of an integer typecode's `*_setitem` refuses before
`CHECK_ARRAY_BOUNDS`, for the int `x` that `__index__` returned:
`PyLong_AsLong` (Objects/longobject.c:673-688) for `b B h H i l`, then `PyArg_Parse`'s own
range checks (Python/getargs.c:723-800: `h` for `b` and `h`, `b` for `B`, `i` for `H` and
`i`); `PyLong_AsUnsignedLong` (Objects/longobject.c:757-806) for `I` and `L`, with the
`unsigned int` check of `II_setitem` (arraymodule.c:470-476); `PyLong_AsLongLong` and
`PyLong_AsUnsignedLongLong` (`_PyLong_AsByteArray`, Objects/longobject.c:1109-1250) for `q`
and `Q`. After the re-check come only `b_setitem`'s `signed char` checks (arraymodule.c:258-267)
and `HH_setitem`'s `unsigned short` checks come before it (:404-415). -/
def intPreCheck (tc : TC) (x : Int) : Option PyExc :=
  let inLong : Prop := longMin ≤ x ∧ x ≤ longMax
  let longErr : PyExc := .overflowError "Python int too large to convert to C long"
  match tc with
  | .b | .h =>
    if ¬ inLong then some longErr
    else if x < -32768 then some (.overflowError "signed short integer is less than minimum")
    else if x > 32767 then some (.overflowError "signed short integer is greater than maximum") else none
  | .B =>
    if ¬ inLong then some longErr
    else if x < 0 then some (.overflowError "unsigned byte integer is less than minimum")
    else if x > 255 then some (.overflowError "unsigned byte integer is greater than maximum") else none
  | .H =>
    if ¬ inLong then some longErr
    else if x > 2147483647 then some (.overflowError "signed integer is greater than maximum")
    else if x < -2147483648 then some (.overflowError "signed integer is less than minimum")
    else if x < 0 then some (.overflowError "unsigned short is less than minimum")
    else if x > 65535 then some (.overflowError "unsigned short is greater than maximum") else none
  | .i =>
    if ¬ inLong then some longErr
    else if x > 2147483647 then some (.overflowError "signed integer is greater than maximum")
    else if x < -2147483648 then some (.overflowError "signed integer is less than minimum") else none
  | .l => if ¬ inLong then some longErr else none
  | .I =>
    if x < 0 then some (.overflowError "can't convert negative value to unsigned int")
    else if x > 18446744073709551615 then some (.overflowError "Python int too large to convert to C unsigned long")
    else if x > 4294967295 then some (.overflowError "unsigned int is greater than maximum") else none
  | .L =>
    if x < 0 then some (.overflowError "can't convert negative value to unsigned int")
    else if x > 18446744073709551615 then some (.overflowError "Python int too large to convert to C unsigned long")
    else none
  | .q => if ¬ inLong then some (.overflowError "int too big to convert") else none
  | .Q =>
    if x < 0 then some (.overflowError "can't convert negative int to unsigned")
    else if x > 18446744073709551615 then some (.overflowError "int too big to convert") else none
  | _ => none

def boundsErr : PyExc := .indexError "array assignment index out of range"

/-- For every integer typecode (`b B h H i I l L q Q`), every array, every index `i >= 0`
and every item whose `__index__` runs code that leaves the array `a'` and returns the int
`x`: if `i` is no longer inside `a'` (or `a'` has no buffer), `setitem` raises the
conversion's own `OverflowError` when `x` fails a check that precedes `CHECK_ARRAY_BOUNDS`,
and otherwise `IndexError("array assignment index out of range")`, even for an `x` that
`b`'s later `signed char` check would refuse; nothing is stored. If `i` is inside `a'`, `x`
is converted and stored in `a'` (the array the code left). A conversion error that precedes the
re-check is also what an index in range gives. -/
def ArraySetitemRecheck : Prop :=
  ∀ (a a' : Arr) (i x : Int) (conv : Arr → Arr × PyVal), a'.tc.isInteger = true → 0 ≤ i →
    conv a = (a', .int x) →
    ((a'.hasBuf = false ∨ (a'.items.length : Int) ≤ i) →
      setitemRe a i conv = (a', .error ((intPreCheck a'.tc x).getD boundsErr))) ∧
    (∀ e, intPreCheck a'.tc x = some e → tcSetitem a'.tc true (.int x) = .error e) ∧
    (a'.hasBuf = true → i < a'.items.length →
      setitemRe a i conv =
        match tcSetitem a'.tc true (.int x) with
        | .ok y => ({ a' with items := a'.items.set i.toNat y }, .ok ())
        | .error e => (a', .error e))

theorem asLongV_int (x : Int) : asLongV (.int x) =
    if longMin ≤ x ∧ x ≤ longMax then .ok x
    else .error (.overflowError "Python int too large to convert to C long") := by
  simp only [asLongV, toIndex, bind, Except.bind, pure, Except.pure]
  split <;> rfl

theorem tcSetitem_false_int (tc : TC) (hi : tc.isInteger = true) (x : Int) :
    tcSetitem tc false (.int x) = .error ((intPreCheck tc x).getD boundsErr) := by
  cases tc <;> first | exact absurd hi (by decide) | skip
  all_goals simp only [tcSetitem, intPreCheck, asLongV_int, toIndex, bind, Except.bind, pure,
    Except.pure, throwE, Bool.not_false, boundsErr]
  all_goals by_cases hl : longMin ≤ x ∧ x ≤ longMax
  all_goals simp only [hl, ite_true, ite_false, not_true_eq_false, not_false_eq_true, and_self,
    true_and, if_true, if_false]
  all_goals (repeat' split)
  all_goals (try unfold longMin longMax at *)
  all_goals first | rfl | omega | simp_all

theorem tcSetitem_pre_int (tc : TC) (hi : tc.isInteger = true) (x : Int) (e : PyExc)
    (h : intPreCheck tc x = some e) : tcSetitem tc true (.int x) = .error e := by
  cases tc <;> first | exact absurd hi (by decide) | skip
  all_goals simp only [intPreCheck] at h
  all_goals simp only [tcSetitem, asLongV_int, toIndex, bind, Except.bind, pure, Except.pure,
    throwE, Bool.not_true, Bool.false_eq_true]
  all_goals by_cases hl : longMin ≤ x ∧ x ≤ longMax
  all_goals simp only [hl, ite_true, ite_false, not_true_eq_false, not_false_eq_true, and_self,
    true_and, if_true, if_false] at h ⊢
  all_goals (repeat' (first | split at h | split))
  all_goals (try unfold longMin longMax at *)
  all_goals first | (simp at h; done) | omega | (injection h with h; subst h; rfl) | simp_all

theorem arraySetitemRecheck_proven : ArraySetitemRecheck := by
  intro a a' i x conv hi h0 hc
  refine ⟨fun hout => ?_, fun e he => tcSetitem_pre_int _ hi x e he, fun hb hin => ?_⟩
  · simp only [setitemRe, hc, storeAfter]
    rw [iteF (show ¬ i < 0 by omega)]
    have hidx : (a'.hasBuf && decide (i < (a'.items.length : Int))) = false := by
      rcases hout with h | h
      · rw [h]; rfl
      · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; right; omega
    rw [hidx, tcSetitem_false_int _ hi x]
  · simp only [setitemRe, hc, storeAfter]
    rw [iteF (show ¬ i < 0 by omega)]
    have hin' : i < (a'.items.length : Int) := hin
    cases hs : tcSetitem a'.tc true (.int x) <;> simp [hb, hs, hin']

/-! ### The stale size of `ins1` -/

/-- An item whose `__index__` clears the array the first time it is called and returns `x`
every time (a `BufferError` from `clear` propagates out of `__index__`). -/
def clearThen (x : Int) : ReVal := fun k b =>
  if k = 0 then
    match arrClear b with
    | .ok b' => (b', .int x)
    | .error e => (b, .user "V" .plain none (some (.raises e)) none)
  else (b, .int x)

/-- `ins1` adds one item to the array it acts on: for every array without exported buffers
and every item whose first conversion may run code that changes the array (the second, the
store's, changing nothing), a successful `a.append(v)` leaves exactly one item more than that
code left. Refuted on 3.15.2: `ins1` reads `n = Py_SIZE(self)` before the code runs and
resizes to the stale `n + 1`. An array of 16 items whose `__index__` clears it gets 17 items
back, 16 of them never written (uninitialised memory in CPython); code that grows the array
loses the grown items. -/
def ArrayIns1Reentrant : Prop :=
  ∀ (a a' : Arr) (v : ReVal), a.exports = 0 → (∀ b, (v 1 b).1 = b) →
    arrAppendRe a v = (a', none) → a'.items.length = (v 0 a).1.items.length + 1

def q16 : Arr := ⟨.q, List.range 16 |>.map Int.ofNat, 16, true, 0, "array"⟩

theorem arrayIns1Reentrant_refuted : ¬ ArrayIns1Reentrant := by
  intro h
  have hr : arrAppendRe q16 (clearThen 7) = ((arrAppendRe q16 (clearThen 7)).1, none) := by decide
  have := h _ _ _ rfl (fun b => by simp [clearThen]) hr
  revert this
  decide

/-- What happens instead, for every integer typecode, every array of at least 16 items
without exported buffers (`n + 1` items fit) and every `x` in the typecode's range, with an
item whose `__index__` clears the array once and returns `x`: the clear frees the buffer
(`array_resize` to 0 from 16 or more items, arraymodule.c:157-169), and `a.append(v)` succeeds
with `n + 1` items, the first `n` of them the cells that `array_resize(self, n+1)` (:873)
obtained by reallocating a NULL buffer (:183-194) and nobody wrote: uninitialised memory in
CPython, 0 in the model. -/
def ArrayIns1Stale : Prop :=
  ∀ (a : Arr) (x : Int), a.tc.isInteger = true → a.exports = 0 → 16 ≤ a.items.length →
    a.Fits (a.items.length + 1) → a.tc.lo ≤ x ∧ x ≤ a.tc.hi →
    (clearThen x 0 a).1.items = [] ∧ (clearThen x 0 a).1.hasBuf = false ∧
    arrAppendRe a (clearThen x) =
      (⟨a.tc, List.replicate a.items.length 0 ++ [x],
        ((a.items.length : Int) + 1) / 16 + 3 + ((a.items.length : Int) + 1), true, a.exports, a.tname⟩, none)

theorem arrayIns1Stale_proven : ArrayIns1Stale := by
  intro a x hi hx h16 hf hr
  have hclear : arrClear a = .ok { a with items := [], hasBuf := false, allocated := 0 } := by
    unfold arrClear arrResize
    dsimp only
    rw [iteF (by omega), iteF (by omega), iteT rfl]
  have hv0 : clearThen x 0 a = ({ a with items := [], hasBuf := false, allocated := 0 }, .int x) := by
    simp only [clearThen, hclear, ite_true]
  refine ⟨by rw [hv0], by rw [hv0], ?_⟩
  have hs := tcSetitem_range a.tc hi x hr
  have hfit : ((a.items.length : Int) + 1) / 16 + (if ((0 : Nat) : Int) < 8 then 3 else 7) +
      ((a.items.length : Int) + 1) ≤ 18446744073709551615 / a.tc.itemsize := by
    unfold Arr.Fits ssizeMax at hf
    rcases itemsize_cases a.tc with h | h | h | h | h <;> rw [h] at hf ⊢ <;> simp <;> omega
  have hres : arrResize { a with items := [], hasBuf := false, allocated := 0 } ((a.items.length : Int) + 1) =
      .ok ⟨a.tc, List.replicate (a.items.length + 1) 0,
        ((a.items.length : Int) + 1) / 16 + 3 + ((a.items.length : Int) + 1), true, a.exports, a.tname⟩ := by
    unfold arrResize
    simp only [List.length_nil]
    rw [iteF (by omega), iteF (by omega), iteF (by omega), iteT hfit]
    simp only [resized, and_false, ite_false]
    rw [iteF (by simp)]
    simp [show ((a.items.length : Int) + 1).toNat = a.items.length + 1 by omega]
  unfold arrAppendRe arrIns1Re setitemRe
  dsimp only
  rw [hv0]
  simp only [storeAfter, show ((-1 : Int) < 0) from by decide, ite_true, tcCheck_of_set _ _ _ hs]
  rw [hres]
  simp only
  rw [ins1Pos_end _ (by omega)]
  simp only [ne_eq, not_true_eq_false, ite_false, clearThen, show ((1 : Nat) = 0) = False from by decide]
  rw [iteF (by omega)]
  have hidx : (true && decide ((a.items.length : Int) < ((List.replicate (a.items.length + 1) (0 : Int)).length : Int))) = true := by
    simp <;> omega
  simp only [hidx, hs]
  congr 2
  rw [show ((a.items.length : Int)).toNat = a.items.length by omega, List.replicate_succ',
    List.set_append_right _ _ (by simp)]
  simp

/-! ### `fromlist` -/

/-- `array_resize` to a size no larger than the array reads only the length and the first
`n` items. -/
theorem arrResize_take (b : Arr) (l1 l2 : List Int) (n : Int) (hl : l1.length = l2.length)
    (ht : l1.take n.toNat = l2.take n.toNat) (h0 : 0 ≤ n) (hn : n ≤ l1.length) :
    arrResize { b with items := l1 } n = (arrResize { b with items := l2 } n).map
      (fun c => { c with items := c.items }) := by
  unfold arrResize
  simp only [hl]
  have r1 : resized l1 n = l1.take n.toNat := resized_le _ _ h0 hn
  have r2 : resized l2 n = l2.take n.toNat := resized_le _ _ h0 (by omega)
  repeat' split
  all_goals simp [Except.map, r1, r2, ht]

theorem fromListReLoop_pure (a' : Arr) (vs : List PyVal) (old : Int) (hb : a'.hasBuf = true) (h0 : 0 ≤ old) :
    ∀ (k i : Nat) (cur : List Int), i + k = vs.length → (cur.length : Int) = old + vs.length →
      (∀ items, fromListLoop a'.tc (vs.drop i) (old + i) cur = .ok items →
        fromListReLoop pureConv vs.length old k i ({ a' with items := cur }, vs) =
          (.ok (), { a' with items }, vs)) ∧
      (∀ e, fromListLoop a'.tc (vs.drop i) (old + i) cur = .error e →
        ∃ cur', cur'.length = cur.length ∧ cur'.take old.toNat = cur.take old.toNat ∧
          fromListReLoop pureConv vs.length old k i ({ a' with items := cur }, vs) =
            ((fromListRestore { a' with items := cur' } old e).1,
              (fromListRestore { a' with items := cur' } old e).2, vs)) := by
  intro k
  induction k with
  | zero =>
    intro i cur hi hl
    have : vs.drop i = [] := List.drop_eq_nil_of_le (by omega)
    rw [this]
    refine ⟨fun items h => ?_, fun e h => ?_⟩
    · simp only [fromListLoop] at h
      injection h with h; subst h; rfl
    · simp [fromListLoop] at h
  | succ k ih =>
    intro i cur hi hl
    have hlt : i < vs.length := by omega
    have hd : vs.drop i = vs[i] :: vs.drop (i + 1) := List.drop_eq_getElem_cons hlt
    rw [hd]
    have hidx : (cur.length : Int) - (vs.length : Int) + (i : Int) = old + i := by omega
    have hstep : fromListReLoop pureConv vs.length old (k + 1) i ({ a' with items := cur }, vs) =
        match storeAfter { a' with items := cur } (old + i) vs[i] with
        | (a2, .error e) => ((fromListRestore a2 old e).1, (fromListRestore a2 old e).2, vs)
        | (a2, .ok ()) => fromListReLoop pureConv vs.length old k (i + 1) (a2, vs) := by
      rw [fromListReLoop]
      rw [iteT (by omega : (i : Int) < vs.length)]
      simp only [Int.toNat_natCast, List.getElem?_eq_getElem hlt, pureConv]
      rw [hidx]
      cases storeAfter { a' with items := cur } (old + i) vs[i] with
      | mk a2 r => cases r <;> simp
    rw [hstep]
    have hs : storeAfter { a' with items := cur } (old + i) vs[i] =
        match tcSetitem a'.tc true vs[i] with
        | .error e => ({ a' with items := cur }, .error e)
        | .ok x => ({ a' with items := cur.set (old + i).toNat x }, .ok ()) := by
      unfold storeAfter
      rw [iteF (by omega)]
      have hin : (old + i) < (cur.length : Int) := by omega
      simp only [hb, hin, decide_true, Bool.and_self]
      cases h : tcSetitem a'.tc true vs[i] <;> rfl
    rw [hs]
    cases hx : tcSetitem a'.tc true vs[i] with
    | error e =>
      refine ⟨fun items h => ?_, fun e' h => ?_⟩
      · simp [fromListLoop, hx] at h
      · simp only [fromListLoop, hx] at h
        injection h with h; subst h
        exact ⟨cur, rfl, rfl, rfl⟩
    | ok x =>
      simp only
      have hl' : ((cur.set (old + i).toNat x).length : Int) = old + vs.length := by simp [hl]
      obtain ⟨ih1, ih2⟩ := ih (i + 1) (cur.set (old + i).toNat x) (by omega) hl'
      have hpos : ((old + (i : Int)) + 1) = old + ((i + 1 : Nat) : Int) := by omega
      refine ⟨fun items h => ?_, fun e h => ?_⟩
      · simp only [fromListLoop, hx] at h
        rw [hpos] at h
        exact ih1 items h
      · simp only [fromListLoop, hx] at h
        rw [hpos] at h
        obtain ⟨cur', h1, h2, h3⟩ := ih2 e h
        refine ⟨cur', by rw [h1]; simp, ?_, h3⟩
        rw [h2]
        apply List.ext_getElem?
        intro j
        simp only [List.getElem?_take, List.getElem?_set]
        split <;> (try split) <;> first | rfl | omega

/-- With items whose conversion changes nothing, the re-entrant `fromlist` is `arrFromList`
(for every array without exported buffers whose new size fits). -/
theorem arrFromListRe_pure (a : Arr) (vs : List PyVal) (hx : a.exports = 0)
    (hf : a.Fits (a.items.length + vs.length)) :
    arrFromListRe pureConv a (.inl vs) = arrFromList a (.inl vs) := by
  unfold arrFromListRe arrFromList
  dsimp only
  by_cases hn : (vs.length : Int) > 0
  · rw [iteT hn, iteT hn]
    cases hr : arrResize a ((a.items.length : Int) + vs.length) with
    | error e => rfl
    | ok a' =>
      simp only
      obtain ⟨hb, ht, hl, he, _⟩ := arrResize_pos a a' _ hr (by omega)
      obtain ⟨ih1, ih2⟩ := fromListReLoop_pure a' vs a.items.length hb (by omega) vs.length 0 a'.items
        (by omega) hl
      have hself : ({ a' with items := a'.items } : Arr) = a' := rfl
      simp only [Int.natCast_zero, Int.add_zero, List.drop_zero] at ih1 ih2
      have htc : fromListLoop a.tc = fromListLoop a'.tc := by rw [ht]
      rw [htc]
      cases hloop : fromListLoop a'.tc vs (a.items.length : Int) a'.items with
      | ok items =>
        have h1 := ih1 items hloop
        rw [hself] at h1
        simp only [h1]
      | error e =>
        obtain ⟨cur', h1, h2, h3⟩ := ih2 e hloop
        rw [hself] at h3
        simp only [h3]
        have hfit : a'.Fits a.items.length := by unfold Arr.Fits at *; rw [ht]; omega
        obtain ⟨a'', hr2, _⟩ := arrResize_ok a' a.items.length (by rw [he, hx]) (by omega) hfit
        have hirr := arrResize_take a' cur' a'.items (a.items.length) h1 h2 (by omega) (by omega)
        rw [hself, hr2] at hirr
        simp only [fromListRestore, hirr, hr2, Except.map]
  · rw [iteF hn, iteF hn]

/-- `fromlist`'s two re-checks after Python code ran, for every integer typecode, every array
without exported buffers (the new size fits) and every list whose first item converts to an
`x` in range, by code that leaves the array alone and appends to the list being read: the item
is stored, then `n != PyList_GET_SIZE(list)` raises `RuntimeError("list changed size during
iteration")` and the array gets its old items back. If the first item's conversion fails, its
exception comes first. And while a buffer is exported, a non-empty list raises `BufferError`
before anything is converted. -/
def ArrayFromListGuard : Prop :=
  ∀ (a : Arr) (v : PyVal) (rest : List (Bool × PyVal)), a.tc.isInteger = true → a.exports = 0 →
    a.Fits (a.items.length + rest.length + 1) →
    let conv : Bool × PyVal → Arr × List (Bool × PyVal) → (Arr × List (Bool × PyVal)) × PyVal :=
      fun x s => ((s.1, if x.1 then s.2 ++ [(false, .int 0)] else s.2), x.2)
    (∀ x, tcSetitem a.tc true v = .ok x →
      (arrFromListRe conv a (.inl ((true, v) :: rest))).1 =
        .error (.named "RuntimeError" "list changed size during iteration") ∧
      (arrFromListRe conv a (.inl ((true, v) :: rest))).2.items = a.items) ∧
    (∀ e, tcSetitem a.tc true v = .error e →
      (arrFromListRe conv a (.inl ((true, v) :: rest))).1 = .error e ∧
      (arrFromListRe conv a (.inl ((true, v) :: rest))).2.items = a.items) ∧
    (∀ b, b.exports > 0 → ∀ l : List (Bool × PyVal), l ≠ [] →
      arrFromListRe conv b (.inl l) = (.error bufferErr, b))

theorem arrayFromListGuard_proven : ArrayFromListGuard := by
  intro a v rest hi hx hf
  dsimp only
  have hn : (((true, v) :: rest).length : Int) > 0 := by simp <;> omega
  obtain ⟨a', hr, hitems, ht, he, _⟩ := arrResize_ok a (a.items.length + ((true, v) :: rest).length) hx
    (by simp <;> omega) (by simp; unfold Arr.Fits at *; omega)
  obtain ⟨hb, _, hl, _, _⟩ := arrResize_pos a a' _ hr (by simp <;> omega)
  have hfit : a'.Fits a.items.length := by unfold Arr.Fits at *; rw [ht]; omega
  obtain ⟨a'', hr2, hi2, _⟩ := arrResize_ok a' a.items.length he (by omega) hfit
  have hback : a''.items = a.items := by
    rw [hi2, resized_le _ _ (by omega) (by omega), hitems,
      resized_gt _ _ (by simp <;> omega),
      show ((a.items.length : Int)).toNat = a.items.length by omega]
    simp
  have hstore : ∀ x, tcSetitem a.tc true v = .ok x →
      arrResize { a' with items := a'.items.set a.items.length x } a.items.length = .ok a'' := by
    intro x hs
    have := arrResize_take a' (a'.items.set a.items.length x) a'.items a.items.length (by simp)
      (by
        apply List.ext_getElem?
        intro j
        simp only [List.getElem?_take, List.getElem?_set]
        rw [show ((a.items.length : Int)).toNat = a.items.length by omega]
        split <;> (try split) <;> first | rfl | omega) (by omega) (by simp <;> omega)
    rw [this, show ({ a' with items := a'.items } : Arr) = a' from rfl, hr2]
    rfl
  have hhead : arrFromListRe (fun (x : Bool × PyVal) (s : Arr × List (Bool × PyVal)) =>
          ((s.1, if x.1 then s.2 ++ [(false, PyVal.int 0)] else s.2), x.2)) a (.inl ((true, v) :: rest)) =
        match storeAfter a' a.items.length v with
        | (a2, .error e) => fromListRestore a2 a.items.length e
        | (a2, .ok ()) => fromListRestore a2 a.items.length (.named "RuntimeError" "list changed size during iteration") := by
    unfold arrFromListRe
    simp only [iteT hn, hr]
    simp only [List.length_cons]
    rw [fromListReLoop.eq_def]
    simp only
    rw [iteT (by omega)]
    simp only [Int.toNat_zero, List.getElem?_cons_zero, ite_true]
    have hidx : (a'.items.length : Int) - ((rest.length + 1 : Nat) : Int) + 0 = a.items.length := by
      simp at hl; omega
    rw [hidx, show ({ a' with items := a'.items } : Arr) = a' from rfl]
    rcases storeAfter a' a.items.length v with ⟨a2, r⟩
    cases r with
    | error e => simp
    | ok u =>
      simp only [List.length_append, List.length_cons, List.length_singleton]
      rw [iteT (by omega)]
  have hst : storeAfter a' a.items.length v =
      match tcSetitem a'.tc true v with
      | .error e => (a', .error e)
      | .ok x => ({ a' with items := a'.items.set a.items.length x }, .ok ()) := by
    unfold storeAfter
    rw [iteF (by omega)]
    have hin : (a.items.length : Int) < a'.items.length := by simp at hl; omega
    have hok : (a'.hasBuf && decide ((a.items.length : Int) < (a'.items.length : Int))) = true := by
      rw [hb]; simp only [Bool.true_and, decide_eq_true_eq]; exact hin
    rw [hok, show ((a.items.length : Int)).toNat = a.items.length by omega]
    cases tcSetitem a'.tc true v <;> rfl
  refine ⟨fun x hs => ?_, fun e hs => ?_, fun b hbx l hl0 => ?_⟩
  · have hs' : tcSetitem a'.tc true v = .ok x := by rw [ht]; exact hs
    rw [hs'] at hst
    rw [hhead, hst]
    simp only [fromListRestore, hstore x hs]
    exact ⟨trivial, hback⟩
  · have hs' : tcSetitem a'.tc true v = .error e := by rw [ht]; exact hs
    rw [hs'] at hst
    rw [hhead, hst]
    simp only [fromListRestore, hr2]
    exact ⟨trivial, hback⟩
  · unfold arrFromListRe
    have hpos : (l.length : Int) > 0 := by
      cases l with
      | nil => exact absurd rfl hl0
      | cons _ _ => simp
    simp only [iteT hpos]
    rw [arrResize_exported b _ hbx (by omega)]

end PyLean.Sequences
