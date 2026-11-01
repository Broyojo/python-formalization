import PyLean.Sequences.ArrayBasic
import PyLean.Sequences.Subscript
import PyLean.Sequences.PopRemove

/-!
`array.array`: storing and reading items, subscripts, `insert`, `pop`, `remove`,
`count`, `index`, `in`, against the `list` model on the C values.
-/

namespace PyLean.Sequences

open PyLean
open PyLean.RangeSlice (Slice sliceIndices)

set_option linter.unusedSectionVars false

theorem find_code (tc : TC) : TC.all.find? (fun t => t.code == tc.code) = some tc := by
  cases tc <;> decide

theorem newArr_ok (t : String) (tc : TC) (n : Int) (h : n ≤ ssizeMax / tc.itemsize) :
    newArr t tc n = .ok ⟨tc, List.replicate n.toNat 0, n, decide (n > 0), 0, t⟩ := by
  unfold newArr; rw [iteF (by omega)]

theorem arrNew_list (t : String) (tc : TC) (vs : List PyVal) (xs : List Int)
    (h : vs.mapM (tcSetitem tc true) = .ok xs) (hf : (vs.length : Int) ≤ ssizeMax / tc.itemsize) :
    ∃ b, arrNew t tc.code (.list vs) = .ok b ∧ b.items = xs ∧ b.tc = tc ∧ b.exports = 0 ∧ b.tname = t := by
  unfold arrNew
  have hb : (if (tc.code == 'u' || tc.code == 'w') then (.ok () : Py Unit) else
      match Init.list vs with
      | .str _ => .error (.typeError s!"cannot use a str to initialize an array with typecode '{tc.code}'")
      | .arr o =>
        if o.tc == .u || o.tc == .w then
          .error (.typeError s!"cannot use a unicode array to initialize an array with typecode '{tc.code}'")
        else .ok ()
      | _ => .ok ()) = .ok () := by split <;> rfl
  simp only [hb, find_code, Option.isSome_none, Bool.false_eq_true, ite_false, newArr_ok t tc vs.length hf, h]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem arrNew_list_err (t : String) (tc : TC) (vs : List PyVal) (e : PyExc)
    (h : vs.mapM (tcSetitem tc true) = .error e) (hf : (vs.length : Int) ≤ ssizeMax / tc.itemsize) :
    arrNew t tc.code (.list vs) = .error e := by
  unfold arrNew
  have hb : (if (tc.code == 'u' || tc.code == 'w') then (.ok () : Py Unit) else
      match Init.list vs with
      | .str _ => .error (.typeError s!"cannot use a str to initialize an array with typecode '{tc.code}'")
      | .arr o =>
        if o.tc == .u || o.tc == .w then
          .error (.typeError s!"cannot use a unicode array to initialize an array with typecode '{tc.code}'")
        else .ok ()
      | _ => .ok ()) = .ok () := by split <;> rfl
  simp only [hb, find_code, Option.isSome_none, Bool.false_eq_true, ite_false, newArr_ok t tc vs.length hf, h]

theorem fits_one (tc : TC) : ((1 : Nat) : Int) ≤ ssizeMax / tc.itemsize := by
  rcases itemsize_cases tc with h | h | h | h <;> rw [h] <;> decide

theorem fits_le (a : Arr) (n m : Int) (h : n ≤ m) (hm : a.Fits m) : a.Fits n := by
  unfold Arr.Fits at *; omega

/-- For an integer typecode (`b B h H i I l L q Q`), every array (`len + 1` items fit
the address space; no buffer exported) and every object `v` with `__index__`
value `n`: `a.append(v)`, `a.insert(i, v)` (`i` in `Py_ssize_t`), `a[j] = v` (valid
`j`) and `array(tc, [v])` store exactly `n` when `n` fits the C type's range and raise
`OverflowError` otherwise (a failed call leaves the array as it was: the model
returns no new array). An object without `__index__` raises its `TypeError`. -/
def ArrayRangeCheck : Prop :=
  ∀ (a : Arr) (v : PyVal) (n i : Int), a.tc.isInteger = true → a.exports = 0 →
    a.Fits (a.items.length + 1) → (a.items.length : Int) ≤ ssizeMax → toIndex v = .ok n →
    let fits := a.tc.lo ≤ n ∧ n ≤ a.tc.hi
    (fits → (∃ a', arrAppend a v = .ok a' ∧ a'.items = a.items ++ [n]) ∧
      (ssizeMin ≤ i → i ≤ ssizeMax → ∃ a', arrInsert a i v = .ok a' ∧ n ∈ a'.items) ∧
      (0 ≤ i → i < a.items.length → arrAssIndex a i (some v) = .ok { a with items := a.items.set i.toNat n }) ∧
      (∃ b, arrNew "array" a.tc.code (.list [v]) = .ok b ∧ b.items = [n])) ∧
    (¬ fits → (tcSetitem a.tc true v).raises "OverflowError" ∧ (arrAppend a v).raises "OverflowError" ∧
      (ssizeMin ≤ i → i ≤ ssizeMax → (arrInsert a i v).raises "OverflowError") ∧
      (0 ≤ i → i < a.items.length → (arrAssIndex a i (some v)).raises "OverflowError") ∧
      (arrNew "array" a.tc.code (.list [v])).raises "OverflowError")

theorem arrIns1_err (a : Arr) (w : Int) (v : PyVal) (e : PyExc) (h : tcSetitem a.tc true v = .error e) :
    arrIns1 a w v = .error e := by
  unfold arrIns1
  simp only [h, bind, Except.bind]

theorem subIndex_ok (i : Int) (h0 : ssizeMin ≤ i) (h1 : i ≤ ssizeMax) : subIndex i = .ok i := by
  unfold subIndex asSsizeExc; rw [iteT ⟨h0, h1⟩]

theorem arrayRangeCheck_proven : ArrayRangeCheck := by
  intro a v n i hint hx hf hlen hv
  dsimp only
  obtain ⟨hyes, hno⟩ := tcSetitem_int a.tc hint v n hv
  refine ⟨fun fits => ?_, fun nf => ?_⟩
  · have hs := hyes fits
    refine ⟨?_, fun h0 h1 => ?_, fun h0 h1 => ?_, ?_⟩
    · obtain ⟨a', h1, h2, _⟩ := arrIns1_ok a a.items.length v n hx hs hf
      refine ⟨a', h1, ?_⟩
      rw [h2]
      have hb : ins1Pos a.items.length a.items.length = a.items.length := by
        unfold ins1Pos; dsimp only; split <;> (try split) <;> (try split) <;> omega
      rw [hb, show ((a.items.length : Int)).toNat = a.items.length by omega]
      unfold insAt
      simp [List.take_length, List.drop_length]
    · have hi : asSsize i = .ok i := by unfold asSsize; rw [iteT ⟨h0, h1⟩]
      obtain ⟨a', h2, h3, _⟩ := arrIns1_ok a i v n hx hs hf
      refine ⟨a', by simp only [arrInsert, hi, bind, Except.bind, h2], ?_⟩
      rw [h3]; unfold insAt; simp
    · simp only [arrAssIndex, subIndex_ok i (by unfold ssizeMin; omega) (by omega), bind, Except.bind,
        pure, Except.pure]
      rw [iteF (show ¬ i < 0 by omega), iteF (show ¬ (i < 0 ∨ i ≥ (a.items.length : Int)) by omega)]
      simp only [hs]
    · obtain ⟨b, h1, h2, _⟩ := arrNew_list "array" a.tc [v] [n] (by simp [List.mapM_cons, hs, bind, Except.bind, pure, Except.pure]) (fits_one a.tc)
      exact ⟨b, h1, h2⟩
  · obtain ⟨e, he, hc⟩ := hno nf
    refine ⟨⟨e, he, hc⟩, ⟨e, ?_, hc⟩, fun h0 h1 => ⟨e, ?_, hc⟩, fun h0 h1 => ⟨e, ?_, hc⟩, ⟨e, ?_, hc⟩⟩
    · exact arrIns1_err _ _ _ _ he
    · have hi : asSsize i = .ok i := by unfold asSsize; rw [iteT ⟨h0, h1⟩]
      simp only [arrInsert, hi, bind, Except.bind]
      exact arrIns1_err _ _ _ _ he
    · simp only [arrAssIndex, subIndex_ok i (by unfold ssizeMin; omega) (by omega), bind, Except.bind,
        pure, Except.pure]
      rw [iteF (show ¬ i < 0 by omega), iteF (show ¬ (i < 0 ∨ i ≥ (a.items.length : Int)) by omega)]
      simp only [he]
    · exact arrNew_list_err "array" a.tc [v] e (by simp [List.mapM_cons, he, bind, Except.bind]) (fits_one a.tc)

/-- `tcSetitem` refuses a value without `__index__` for an integer typecode. -/
def ArrayNonIndexItem : Prop :=
  ∀ (tc : TC) (v : PyVal) (e : PyExc), tc.isInteger = true → toIndex v = .error e →
    tcSetitem tc true v = .error e

theorem arrayNonIndexItem_proven : ArrayNonIndexItem := by
  intro tc v e hint he
  have hal : asLongV v = .error e := by simp only [asLongV, he, bind, Except.bind]
  cases tc <;> first | exact absurd hint (by decide) | skip
  all_goals simp only [tcSetitem, hal, he, bind, Except.bind]

/-- The character and `double` typecodes. `u` and `w` store the code point of a
one-character `str` and refuse anything else with `TypeError`; reading gives the
same character back for every valid code point, and `ValueError` for a stored value
outside `[0, 0x10FFFF]` (which only `frombytes` can store). `d` stores the bit
pattern of `PyFloat_AsDouble(v)` and reads it back unchanged. -/
def ArrayCharDouble : Prop :=
  (∀ (tc : TC) (c : Nat), (tc = .u ∨ tc = .w) → c ≤ 1114111 →
    tcSetitem tc true (.str [c]) = .ok c ∧ tcGetitem tc c = .ok (.str [c])) ∧
  (∀ (tc : TC) (x : Int), (tc = .u ∨ tc = .w) → (x < 0 ∨ x > 1114111) →
    tcGetitem tc x = .error (.valueError "chr() arg not in range(0x110000)")) ∧
  (∀ (tc : TC) (cs : List Nat) , (tc = .u ∨ tc = .w) → cs.length ≠ 1 →
    (tcSetitem tc true (.str cs)).raises "TypeError") ∧
  (∀ (tc : TC) (n : Int), (tc = .u ∨ tc = .w) → (tcSetitem tc true (.int n)).raises "TypeError") ∧
  (∀ (v : PyVal) (b : Nat), asDouble v = .ok b →
    tcSetitem .d true v = .ok b ∧ tcGetitem .d b = .ok (.float b))

theorem arrayCharDouble_proven : ArrayCharDouble := by
  refine ⟨fun tc c ht hc => ?_, fun tc x ht hx => ?_, fun tc cs ht hl => ?_, fun tc n ht => ?_, fun v b hb => ?_⟩
  · rcases ht with h | h <;> subst h
    · simp only [tcSetitem, tcGetitem, pure, Except.pure, bind, Except.bind, Bool.not_true,
        Bool.false_eq_true, ite_false]
      exact ⟨trivial, by rw [iteF (by omega)]; simp⟩
    · simp only [tcSetitem, tcGetitem, pure, Except.pure, bind, Except.bind, Bool.not_true,
        Bool.false_eq_true, ite_false]
      exact ⟨trivial, by rw [iteF (by omega)]; simp⟩
  · rcases ht with h | h <;> subst h <;> simp only [tcGetitem] <;> rw [iteT hx]
  · match cs, hl with
    | [], _ => rcases ht with h | h <;> subst h <;> exact ⟨_, rfl, rfl⟩
    | [_], h => exact absurd rfl h
    | _ :: _ :: _, _ => rcases ht with h | h <;> subst h <;> exact ⟨_, rfl, rfl⟩
  · rcases ht with h | h <;> subst h <;> exact ⟨_, rfl, rfl⟩
  · constructor
    · simp only [tcSetitem, hb, bind, Except.bind, pure, Except.pure, Bool.not_true, Bool.false_eq_true,
        ite_false]
    · simp only [tcGetitem, Int.toNat_natCast]

/-- `a[i]`, `a[i] = v`, `del a[i]` for every int `i`, and the `sq_item`/`sq_ass_item`
slots, against `seqGet`/`seqAss` on the C values: the same index arithmetic and
errors as `list` with the array's messages, the item then decoded by `tcGetitem`.
`a[i] = v` stores the C value of `v`. No buffer is exported. -/
def ArraySubscript : Prop :=
  ∀ (a : Arr) (i : Int), a.exports = 0 → a.Fits a.items.length → (a.items.length : Int) ≤ ssizeMax →
    arrGetItem a i = (seqGet "array index out of range" a.items i >>= tcGetitem a.tc) ∧
    (arrAssIndex a i none).map (·.items) = seqAss "array assignment index out of range" a.items i none ∧
    (∀ v x, tcSetitem a.tc true v = .ok x →
      (arrAssIndex a i (some v)).map (·.items) = seqAss "array assignment index out of range" a.items i (some x)) ∧
    (arrItem a i = if 0 ≤ i ∧ i < a.items.length then a.get i
      else .error (.indexError "array index out of range")) ∧
    (0 ≤ i → i < a.items.length →
      (arrAssItem a i none).map (·.items) = .ok (a.items.eraseIdx i.toNat) ∧
      ∀ v x, tcSetitem a.tc true v = .ok x → (arrAssItem a i (some v)).map (·.items) = .ok (a.items.set i.toNat x))

theorem arrItem_eq (a : Arr) (i : Int) : arrItem a i = if 0 ≤ i ∧ i < a.items.length then a.get i
      else .error (.indexError "array index out of range") := by
  unfold arrItem
  by_cases h : 0 ≤ i ∧ i < a.items.length
  · rw [iteF (by omega), iteT h]
  · rw [iteT (by omega), iteF h]

theorem arrAssCore_del1 (a : Arr) (i : Int) (hx : a.exports = 0) (h0 : 0 ≤ i) (hi : i < a.items.length)
    (hf : a.Fits a.items.length) :
    (arrAssCore a i (i + 1) 1 1 none).map (·.items) = .ok (a.items.eraseIdx i.toNat) := by
  unfold arrAssCore
  have hne : ¬ (a.exports > 0) := by omega
  have hst : ¬ ((1:Int) > 0 ∧ i + 1 < i ∨ (1:Int) < 0 ∧ i + 1 > i) := by omega
  simp only [bind, Except.bind, pure, Except.pure, Option.getD_none, throwE, hne, and_false, ite_false,
    hst, ite_true]
  rw [iteT (show (1:Int) > 0 by decide),
    memmove_ok _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
  simp only
  obtain ⟨a', hr, hi', _⟩ := arrResize_ok
    { a with items := a.items.take (i + 0).toNat ++ (a.items.drop (i + 1).toNat).take ((a.items.length : Int) - (i + 1)).toNat ++ a.items.drop (i + 0 + ((a.items.length : Int) - (i + 1))).toNat }
    ((a.items.length : Int) + 0 - 1) hx (by omega) (by unfold Arr.Fits at *; simp only; omega)
  simp only [hr]
  rw [iteF (show ¬ ((0:Int) > 0) by decide)]
  show Except.ok a'.items = _
  rw [hi', resized_le _ _ (by omega)
    (by simp only [List.length_append, List.length_take, List.length_drop]; omega),
    List.eraseIdx_eq_take_drop_succ]
  congr 1
  list_ext

theorem arrAssItem_del (a : Arr) (i : Int) (hx : a.exports = 0) (h0 : 0 ≤ i) (hi : i < a.items.length)
    (hf : a.Fits a.items.length) :
    (arrAssItem a i none).map (·.items) = .ok (a.items.eraseIdx i.toNat) := by
  unfold arrAssItem
  simp only [bind, Except.bind, pure, Except.pure, throwE]
  rw [iteF (show ¬ (i < 0 ∨ i ≥ (a.items.length : Int)) by omega)]
  obtain ⟨a', h1, h2, _⟩ := arrDelSlice_ok a i (i + 1) hx h0 (by omega) (by omega) hf
  rw [h1]
  simp only [Except.map, h2, List.eraseIdx_eq_take_drop_succ, show (i + 1).toNat = i.toNat + 1 by omega]

theorem arraySubscript_proven : ArraySubscript := by
  intro a i hx hf hlen
  refine ⟨?_, ?_, fun v x hs => ?_, arrItem_eq a i, fun h0 h1 => ⟨arrAssItem_del a i hx h0 h1 hf, fun v x hs => ?_⟩⟩
  · by_cases hs : ssizeMin ≤ i ∧ i ≤ ssizeMax
    · simp only [arrGetItem, seqGet, subIndex_ok i hs.1 hs.2, bind, Except.bind, pure, Except.pure]
      rw [arrItem_eq]
      generalize (if i < 0 then i + (a.items.length : Int) else i) = j
      by_cases hv : 0 ≤ j ∧ j < a.items.length
      · rw [iteT hv, iteT hv]; rfl
      · rw [iteF hv, iteF hv]; rfl
    · have : subIndex i = .error (.indexError "cannot fit 'int' into an index-sized integer") := by
        unfold subIndex asSsizeExc; rw [iteF hs]
      simp only [arrGetItem, seqGet, this, bind, Except.bind]
  · by_cases hs : ssizeMin ≤ i ∧ i ≤ ssizeMax
    · simp only [arrAssIndex, seqAss, subIndex_ok i hs.1 hs.2, bind, Except.bind, pure, Except.pure, throwE]
      generalize hj : (if i < 0 then i + (a.items.length : Int) else i) = j
      by_cases hv : 0 ≤ j ∧ j < a.items.length
      · rw [iteF (show ¬ (j < 0 ∨ j ≥ (a.items.length : Int)) by omega), iteT hv]
        exact arrAssCore_del1 a j hx hv.1 hv.2 hf
      · rw [iteT (show (j < 0 ∨ j ≥ (a.items.length : Int)) by omega), iteF hv]; rfl
    · have : subIndex i = .error (.indexError "cannot fit 'int' into an index-sized integer") := by
        unfold subIndex asSsizeExc; rw [iteF hs]
      simp only [arrAssIndex, seqAss, this, bind, Except.bind, Except.map]
  · by_cases hss : ssizeMin ≤ i ∧ i ≤ ssizeMax
    · simp only [arrAssIndex, seqAss, subIndex_ok i hss.1 hss.2, bind, Except.bind, pure, Except.pure, throwE]
      generalize hj : (if i < 0 then i + (a.items.length : Int) else i) = j
      by_cases hv : 0 ≤ j ∧ j < a.items.length
      · rw [iteF (show ¬ (j < 0 ∨ j ≥ (a.items.length : Int)) by omega), iteT hv]
        simp only [hs, Except.map]
      · rw [iteT (show (j < 0 ∨ j ≥ (a.items.length : Int)) by omega), iteF hv]; rfl
    · have : subIndex i = .error (.indexError "cannot fit 'int' into an index-sized integer") := by
        unfold subIndex asSsizeExc; rw [iteF hss]
      simp only [arrAssIndex, seqAss, this, bind, Except.bind, Except.map]
  · simp only [arrAssItem, bind, Except.bind, pure, Except.pure, throwE]
    rw [iteF (show ¬ (i < 0 ∨ i ≥ (a.items.length : Int)) by omega)]
    simp only [hs, Except.map]

/-- `a.insert(i, v)` is `list.insert` on the C values: for every array (`len + 1`
items fit the address space; no buffer exported), every int `i` and every `v` that
converts to the C value `x`. A `v` that does not convert raises the conversion's
exception for every `i` inside `Py_ssize_t`. -/
def ArrayInsertAgree : Prop :=
  ∀ (a : Arr) (i : Int) (v : PyVal) (x : Int), a.exports = 0 → a.Fits (a.items.length + 1) →
    tcSetitem a.tc true v = .ok x → (arrInsert a i v).map (·.items) = listInsert a.items i x

theorem arrayInsertAgree_proven : ArrayInsertAgree := by
  intro a i v x hx hf hs
  rw [listInsert_eq]
  unfold arrInsert asSsize
  by_cases hi : ssizeMin ≤ i ∧ i ≤ ssizeMax
  · rw [iteT hi, iteT hi]
    obtain ⟨a', h1, h2, _⟩ := arrIns1_ok a i v x hx hs hf
    simp only [bind, Except.bind, h1, Except.map, h2]
  · rw [iteF hi, iteF hi]; rfl

/-- The Python object of a stored C value, for arrays whose items all decode. -/
def decode (tc : TC) (x : Int) : PyVal := (tcGetitem tc x).toOption.getD default

/-- Every item decodes (no out-of-range `wchar_t`, which only `frombytes` can store). -/
def Arr.Decodes (a : Arr) : Prop := ∀ x ∈ a.items, ∃ v, tcGetitem a.tc x = .ok v

theorem get_decode (a : Arr) (h : a.Decodes) (i : Int) (h0 : 0 ≤ i) (h1 : i < a.items.length) :
    a.get i = .ok (decode a.tc (ix a.items i)) := by
  obtain ⟨v, hv⟩ := h _ (ix_mem a.items i h0 h1)
  unfold Arr.get decode
  rw [hv]; rfl

/-- `eqv` of a comparison that is pure and truth-valued. -/
def pureEq (g : PyVal → Bool) : PyVal → Py Bool := fun v => .ok (g v)

theorem arrScan_spec (a : Arr) (hd : a.Decodes) (g : PyVal → Bool) (stop : Int) :
    ∀ (fuel : Nat) (i : Int), 0 ≤ i → (a.items.length : Int) - i < fuel →
    ∃ r, arrScan a (pureEq g) stop fuel i = .ok r ∧ IsFirst (fun x => g (decode a.tc x)) a.items i stop r
  | 0, i, _, h => ⟨none, rfl, isFirst_empty _ _ _ _ (by omega)⟩
  | fuel + 1, i, h0, hf => by
    unfold arrScan
    by_cases hc : i < stop ∧ i < a.items.length
    · rw [iteT hc, get_decode a hd i h0 hc.2]
      simp only [pureEq]
      by_cases hg : g (decode a.tc (ix a.items i)) = true
      · simp only [hg]
        exact ⟨_, rfl, isFirst_here _ _ _ _ h0 hc.1 hc.2 hg⟩
      · have hg' : g (decode a.tc (ix a.items i)) = false := by simpa using hg
        simp only [hg']
        obtain ⟨r, hr, hfr⟩ := arrScan_spec a hd g stop fuel (i + 1) (by omega) (by omega)
        exact ⟨r, hr, isFirst_step _ _ _ _ _ hg' hfr⟩
    · rw [iteF hc]
      exact ⟨none, rfl, isFirst_empty _ _ _ _ hc⟩

theorem arrIndex_eq (a : Arr) (eqv : PyVal → Py Bool) (start stop : Option Int) :
    arrIndex a eqv start stop =
      match arrScan a eqv (normIdxA (sliceIndex (stop.getD ssizeMax)) a.items.length)
        (a.items.length + 1) (normIdx (sliceIndex (start.getD 0)) a.items.length) with
      | .error e => .error e
      | .ok r => toRes "array.index(x): x not in array" r := by
  unfold arrIndex toRes normIdx normIdxA
  dsimp only
  split <;> rename_i heq <;> rw [heq]

/-- `a.index(x[, start[, stop]])`, `x in a`, `a.count(x)`, `a.remove(x)`, `a.pop([i])`
for every array whose items decode (no buffer exported), every comparison with `x`
that is a pure truth-valued function `g` of the item (the case of ints, floats and
strs), and any int bounds: `index` returns the first position of a match in
`a[start:stop]`, as `list.index` does on the same items; `count` and `in` count and
find matches; `remove` deletes the first match; `pop` removes and returns item
`i`, with the index arithmetic and errors of `list.pop`. -/
def ArraySearchAgree : Prop :=
  ∀ (a : Arr) (g : PyVal → Bool) (start stop i : Option Int), a.Decodes → a.exports = 0 →
    a.Fits a.items.length → (a.items.length : Int) ≤ ssizeMax →
    let p := fun x => g (decode a.tc x)
    (∃ s e r, sliceIndices ⟨start, stop, none⟩ a.items.length = .ok (s, e, 1) ∧ IsFirst p a.items s e r ∧
      arrIndex a (pureEq g) start stop = toRes "array.index(x): x not in array" r ∧
      listIndex (fun y (_ : Int) => p y) a.items 0 start stop = toRes "list.index(x): x not in list" r) ∧
    arrCount a (pureEq g) = .ok (a.items.filter p).length ∧
    arrContains a (pureEq g) = .ok (a.items.any p) ∧
    (arrRemove a (pureEq g)).map (·.items) = removeSpec "array.remove(x): x not in array" a.items p ∧
    (arrPop a i).map (fun r => (r.1, r.2.items)) =
      (popSpec "pop from empty array" a.items i).map (fun r => (decode a.tc r.1, r.2))

theorem arrCountLoop_spec (a : Arr) (hd : a.Decodes) (g : PyVal → Bool) :
    ∀ (n : Nat) (i c : Int), 0 ≤ i → i + n = a.items.length →
    arrCountLoop a (pureEq g) n i c =
      .ok (c + ((a.items.drop i.toNat).filter (fun x => g (decode a.tc x))).length)
  | 0, i, c, _, h => by
    simp only [arrCountLoop]
    rw [List.drop_of_length_le (by omega)]; simp
  | n + 1, i, c, h0, h => by
    simp only [arrCountLoop]
    rw [get_decode a hd i h0 (by omega)]
    simp only [pureEq]
    rw [arrCountLoop_spec a hd g n (i + 1) _ (by omega) (by omega)]
    rw [List.drop_eq_getElem_cons (show i.toNat < a.items.length by omega), List.filter_cons,
      show (i + 1).toNat = i.toNat + 1 by omega]
    have hix : ix a.items i = a.items[i.toNat] := by
      have := ix_getElem a.items i.toNat (by omega)
      rwa [show ((i.toNat : Nat) : Int) = i by omega] at this
    rw [← hix]
    by_cases hg : g (decode a.tc (ix a.items i)) = true
    · simp only [hg, ite_true, List.length_cons]; congr 1; omega
    · simp only [hg, ite_false, Bool.false_eq_true]

theorem arrPop_eq (a : Arr) (hd : a.Decodes) (hx : a.exports = 0) (hf : a.Fits a.items.length) (i : Option Int) :
    (arrPop a i).map (fun r => (r.1, r.2.items)) =
      (popSpec "pop from empty array" a.items i).map (fun r => (decode a.tc r.1, r.2)) := by
  unfold arrPop popSpec
  cases popArg i with
  | error e => rfl
  | ok k =>
    simp only [bind, Except.bind, arrPopK, popSpecK, throwE, pure, Except.pure]
    by_cases he : a.items.length = 0
    · rw [iteT (show ((a.items.length : Nat) : Int) = 0 by omega), iteT he]; rfl
    · rw [iteF (show ¬ ((a.items.length : Nat) : Int) = 0 by omega), iteF he]
      simp only [validIndex]
      generalize (if k < 0 then k + (a.items.length : Int) else k) = j
      by_cases hv : 0 ≤ j ∧ j < a.items.length
      · rw [iteF (by omega), get_decode a hd j hv.1 hv.2]
        obtain ⟨a', h1, h2, _⟩ := arrDelSlice_ok a j (j + 1) hx hv.1 (by omega) (by omega) hf
        simp only [h1, hv, decide_true, and_self, Bool.not_true, Bool.false_eq_true, ite_false, Except.map, h2,
          List.eraseIdx_eq_take_drop_succ, show (j + 1).toNat = j.toNat + 1 by omega]
      · rw [iteT (by omega)]
        simp [hv]
        rfl

theorem arraySearchAgree_proven : ArraySearchAgree := by
  intro a g start stop i hd hx hf hlen
  dsimp only
  have hn : (0 : Int) ≤ a.items.length := by omega
  obtain ⟨r0, hr0, hf0⟩ := arrScan_spec a hd g (normIdxA (sliceIndex (stop.getD ssizeMax)) a.items.length)
    (a.items.length + 1) (normIdx (sliceIndex (start.getD 0)) a.items.length) (normIdx_nonneg _ _ hn)
    (by have := normIdx_nonneg (sliceIndex (start.getD 0)) a.items.length hn; omega)
  have hc := isFirst_congr _ _ _ _ (clip1 start 0 a.items.length) (clip1 stop a.items.length a.items.length) _
    (fun j h0 h1 => and_congr (clip_start start _ hn hlen j h0 h1) (clip_stop_arr stop _ hn hlen j h0 h1)) hf0
  obtain ⟨r1, hr1, hf1⟩ := list_isFirst (fun y (_ : Int) => g (decode a.tc y)) a.items 0 start stop hlen
  have hu := isFirst_unique _ _ _ _ _ _ hc hf1
  obtain ⟨r2, hr2, hf2⟩ := arrScan_spec a hd g a.items.length (a.items.length + 1) 0 (by omega) (by omega)
  refine ⟨⟨_, _, r0, sliceIndices_step1 start stop _ hn, hc, ?_, ?_⟩, ?_, ?_, ?_, arrPop_eq a hd hx hf i⟩
  · rw [arrIndex_eq, hr0]
  · rw [hr1, hu]
  · unfold arrCount
    rw [arrCountLoop_spec a hd g a.items.length 0 0 (by omega) (by omega)]
    simp
  · unfold arrContains
    rw [hr2]
    simp only
    rw [isFirst_any _ a.items r2 (by simpa using hf2)]
  · unfold arrRemove removeSpec
    rw [hr2]
    have hu2 := isFirst_unique _ _ _ _ _ _ (by simpa using hf2) (find_isFirst (fun x => g (decode a.tc x)) a.items)
    cases hfind : (List.range a.items.length).find? (fun (k : Nat) => g (decode a.tc (ix a.items k))) with
    | none =>
      rw [hfind] at hu2; simp at hu2; subst hu2; rfl
    | some k =>
      rw [hfind] at hu2; simp at hu2; subst hu2
      obtain ⟨_, n, hk, hkn, _⟩ := List.find?_eq_some_iff_getElem.mp hfind
      rw [List.getElem_range] at hkn
      subst hkn
      simp only [List.length_range] at hk
      obtain ⟨a', h1, h2, _⟩ := arrDelSlice_ok a n (n + 1) hx (by omega) (by omega) (by omega) hf
      simp only [h1, Except.map, h2, List.eraseIdx_eq_take_drop_succ]
      rfl

end PyLean.Sequences
