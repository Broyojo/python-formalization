import PyLean.Sequences.ArrayItems

/-!
`array_richcompare` (`Modules/arraymodule.c:908-1015`, CPython 3.15.2) against the comparison of
the lists of the items, `list(v) <op> list(w)`.
-/

namespace PyLean.Sequences

open PyLean

/-- The first pair of items at the same position that differ under `==`, over the common
length. -/
def firstDiffL : List PyVal → List PyVal → Option (PyVal × PyVal)
  | x :: xs, y :: ys => if pvEq x y then firstDiffL xs ys else some (x, y)
  | _, _ => none

/-- `list(v) <op> list(w)`: `list_richcompare_impl` (Objects/listobject.c:3459-3519) on two
lists of item objects. The lengths decide `==` and `!=` when they differ (:3470-3476); the loop
finds the first index where `PyObject_RichCompareBool(vitem, witem, Py_EQ)` is false
(:3479-3495); without one the sizes are compared (:3497-3500), otherwise `==` is false, `!=`
true, and any other operator compares the two items (:3503-3518). The identity shortcut of
:3482 does not change the outcome here: the items of `list(a)` are fresh floats and complex
numbers, or ints and one-character strs, which are equal whenever identical. This is the
lexicographic comparison of Doc/library/stdtypes.rst ("Sequences of the same type also support
comparisons ... compared lexicographically by comparing corresponding elements"). -/
def listRichSpec (op : CmpOp) (xs ys : List PyVal) : Py Bool :=
  if xs.length ≠ ys.length ∧ (op = .eq ∨ op = .ne) then .ok (op = .ne)
  else
    match firstDiffL xs ys with
    | none => .ok (sizeCmp op xs.length ys.length)
    | some (x, y) =>
      match op with
      | .eq => .ok false
      | .ne => .ok true
      | op => pvRich op x y

/-- The same comparison on the stored C values themselves, ordered as integers. -/
def rawFirstDiff : List Int → List Int → Option (Int × Int)
  | x :: xs, y :: ys => if x = y then rawFirstDiff xs ys else some (x, y)
  | _, _ => none

def rawCmp (op : CmpOp) (xs ys : List Int) : Bool :=
  if xs.length ≠ ys.length ∧ (op = .eq ∨ op = .ne) then op = .ne
  else
    match rawFirstDiff xs ys with
    | none => sizeCmp op xs.length ys.length
    | some (x, y) => opHolds op (compare x y)

/-- `array_richcompare`, for every operator:
* two arrays whose items all decode (of the same typecode or not, any of the seventeen)
  compare as the lists of their items, `list(v) <op> list(w)`: the fast path of same-typecode
  integer and character arrays (`compareitems` on the C values, :934-955) and the item-by-item
  path (:957-1012) give the same result. So NaNs are unequal, `-0.0 == 0.0`, an `int` item
  equals a `float` item of the same value, and complex items have no order;
* two arrays of the same integer or character typecode compare their stored C values in
  integer order, also when an item does not decode (a `wchar_t` outside the code points, which
  only `frombytes` can store and which `list(a)` refuses);
* an operand that is not an array gives `NotImplemented` (:918-919). -/
def ArrayRichcompare : Prop :=
  (∀ (op : CmpOp) (v w : Arr), v.Decodes → w.Decodes →
    arrRichcompare op (.inl v) (.inl w) =
      (listRichSpec op (v.items.map (decode v.tc)) (w.items.map (decode w.tc))).map some) ∧
  (∀ (op : CmpOp) (v w : Arr), v.tc = w.tc → v.tc.hasCompare = true →
    arrRich op v w = .ok (rawCmp op v.items w.items)) ∧
  (∀ (op : CmpOp) (v : Arr) (t : String),
    arrRichcompare op (.inl v) (.inr t) = .ok none ∧ arrRichcompare op (.inr t) (.inl v) = .ok none)

/-! ### The item-by-item path -/

theorem arrFirstDiff_spec (v w : Arr) (hv : v.Decodes) (hw : w.Decodes) :
    ∀ (fuel : Nat) (i : Nat), v.items.length - i < fuel →
      arrFirstDiff v w fuel i =
        .ok (firstDiffL ((v.items.drop i).map (decode v.tc)) ((w.items.drop i).map (decode w.tc)))
  | 0, i, h => by omega
  | fuel + 1, i, h => by
    unfold arrFirstDiff
    by_cases hc : (i : Int) < v.items.length ∧ (i : Int) < w.items.length
    · rw [if_pos hc, get_decode v hv i (by omega) hc.1, get_decode w hw i (by omega) hc.2]
      rw [List.drop_eq_getElem_cons (show i < v.items.length by omega),
        List.drop_eq_getElem_cons (show i < w.items.length by omega)]
      simp only [List.map_cons, firstDiffL]
      have e1 : ix v.items (i : Int) = v.items[i] := by
        have := ix_getElem v.items i (by omega); simpa using this
      have e2 : ix w.items (i : Int) = w.items[i] := by
        have := ix_getElem w.items i (by omega); simpa using this
      rw [e1, e2]
      by_cases hq : pvEq (decode v.tc v.items[i]) (decode w.tc w.items[i]) = true
      · rw [if_pos hq, if_pos hq]
        have := arrFirstDiff_spec v w hv hw fuel (i + 1) (by omega)
        simpa using this
      · rw [if_neg hq, if_neg hq]
    · rw [if_neg hc]
      have : v.items.drop i = [] ∨ w.items.drop i = [] := by
        rcases Classical.em ((i : Int) < v.items.length) with h1 | h1
        · right; apply List.drop_eq_nil_of_le; omega
        · left; apply List.drop_eq_nil_of_le; omega
      rcases this with h1 | h1 <;> rw [h1] <;> simp [firstDiffL]

/-! ### The fast path -/

/-- An item decoder that is injective and keeps the order, on the items `P` allows. -/
structure OrderDecoder (D : Int → PyVal) (P : Int → Prop) : Prop where
  eq : ∀ x y, P x → P y → pvEq (D x) (D y) = decide (x = y)
  rich : ∀ op x y, P x → P y → x ≠ y → pvRich op (D x) (D y) = .ok (opHolds op (compare x y))

theorem rawFirstDiff_map (D : Int → PyVal) (P : Int → Prop) (hD : OrderDecoder D P) :
    ∀ (xs ys : List Int), (∀ x ∈ xs, P x) → (∀ y ∈ ys, P y) →
      firstDiffL (xs.map D) (ys.map D) = (rawFirstDiff xs ys).map (fun p => (D p.1, D p.2))
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | x :: xs, y :: ys, hx, hy => by
    simp only [List.map_cons, firstDiffL, rawFirstDiff]
    rw [hD.eq x y (hx x (by simp)) (hy y (by simp))]
    by_cases h : x = y
    · simp only [h, decide_true, if_true]
      exact rawFirstDiff_map D P hD xs ys (fun z hz => hx z (by simp [hz])) (fun z hz => hy z (by simp [hz]))
    · simp [h]

theorem rawFirstDiff_ne : ∀ (xs ys : List Int) (x y : Int), rawFirstDiff xs ys = some (x, y) →
    x ≠ y ∧ x ∈ xs ∧ y ∈ ys
  | [], _, _, _, h => by simp [rawFirstDiff] at h
  | _ :: _, [], _, _, h => by simp [rawFirstDiff] at h
  | a :: as, b :: bs, x, y, h => by
    simp only [rawFirstDiff] at h
    by_cases hab : a = b
    · rw [if_pos hab] at h
      obtain ⟨h1, h2, h3⟩ := rawFirstDiff_ne as bs x y h
      exact ⟨h1, by simp [h2], by simp [h3]⟩
    · rw [if_neg hab] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hab, by simp, by simp⟩

/-- `compareitems` over the common length is the sign of the first difference. -/
theorem compareItems_eq : ∀ (xs ys : List Int),
    compareItems xs ys (min xs.length ys.length) =
      match rawFirstDiff xs ys with
      | none => 0
      | some (x, y) => if x < y then -1 else 1
  | [], _ => by simp [compareItems, rawFirstDiff]
  | _ :: _, [] => by simp [compareItems, rawFirstDiff]
  | x :: xs, y :: ys => by
    rw [show min (x :: xs).length (y :: ys).length = min xs.length ys.length + 1 by
      simp only [List.length_cons]; omega]
    simp only [compareItems, rawFirstDiff]
    by_cases h : x = y
    · rw [if_neg (by simpa using h), if_pos h]; exact compareItems_eq xs ys
    · rw [if_pos h, if_neg h]

theorem opHolds_sign (op : CmpOp) (x y : Int) (h : x ≠ y) :
    (match op with
      | .lt => (if x < y then (-1 : Int) else 1) < 0 | .le => (if x < y then (-1 : Int) else 1) ≤ 0
      | .eq => (if x < y then (-1 : Int) else 1) = 0 | .ne => (if x < y then (-1 : Int) else 1) ≠ 0
      | .gt => (if x < y then (-1 : Int) else 1) > 0 | .ge => (if x < y then (-1 : Int) else 1) ≥ 0 : Bool) =
      opHolds op (compare x y) := by
  rcases Int.lt_or_gt_of_ne h with hl | hl
  · have hc : compare x y = .lt := Int.compare_eq_lt.mpr hl
    rw [hc, if_pos hl]; cases op <;> decide
  · have hc : compare x y = .gt := Int.compare_eq_gt.mpr hl
    rw [hc, if_neg (by omega)]; cases op <;> decide

theorem arrRich_fast (op : CmpOp) (v w : Arr) (ht : v.tc = w.tc) (hc : v.tc.hasCompare = true) :
    arrRich op v w = .ok (rawCmp op v.items w.items) := by
  unfold arrRich rawCmp
  by_cases hl : v.items.length ≠ w.items.length ∧ (op = .eq ∨ op = .ne)
  · rw [if_pos ⟨(by have := hl.1; omega), hl.2⟩, if_pos hl]
  · rw [if_neg (fun h => hl ⟨(by have := h.1; omega), h.2⟩), if_neg hl, if_pos ⟨ht, hc⟩]
    simp only []
    rw [compareItems_eq]
    cases hr : rawFirstDiff v.items w.items with
    | none => simp
    | some p =>
      obtain ⟨x, y⟩ := p
      have hne := (rawFirstDiff_ne _ _ _ _ hr).1
      simp only []
      rw [if_neg (by split <;> omega)]
      simp only [Except.ok.injEq]
      exact opHolds_sign op x y hne

/-! ### Decoders of the typecodes with `compareitems` -/

theorem pvEq_int (x y : Int) : pvEq (.int x) (.int y) = decide (x = y) := by
  simp only [pvEq, PyVal.num, numOrder, cmpScaled]
  simp only [Int.sub_self, Int.toNat_zero, Int.pow_zero, Int.mul_one, Int.min_self]
  by_cases h : x = y
  · subst h; simp
  · rcases Int.lt_or_gt_of_ne h with hl | hl
    · rw [Int.compare_eq_lt.mpr hl]; simp [h]
    · rw [Int.compare_eq_gt.mpr hl]; simp [h]

theorem pvRich_int (op : CmpOp) (x y : Int) : pvRich op (.int x) (.int y) = .ok (opHolds op (compare x y)) := by
  simp only [pvRich, PyVal.num, numOrder, cmpScaled]
  simp only [Int.sub_self, Int.toNat_zero, Int.pow_zero, Int.mul_one, Int.min_self]

theorem intDecoder (tc : TC) (hi : tc.isInteger = true) : OrderDecoder (decode tc) (fun _ => True) where
  eq x y _ _ := by
    simp only [decode, tcGetitem_int tc hi]; exact pvEq_int x y
  rich op x y _ _ _ := by
    simp only [decode, tcGetitem_int tc hi]; exact pvRich_int op x y

/-- The code points a character item decodes. -/
def CharOk (x : Int) : Prop := 0 ≤ x ∧ x ≤ 1114111

theorem decode_char (tc : TC) (ht : tc = .u ∨ tc = .w) (x : Int) (h : CharOk x) :
    decode tc x = .str [x.toNat] := by
  unfold CharOk at h
  rcases ht with rfl | rfl <;> simp only [decode, tcGetitem] <;> rw [if_neg (by omega)] <;> rfl

theorem charDecoder (tc : TC) (ht : tc = .u ∨ tc = .w) : OrderDecoder (decode tc) CharOk where
  eq x y hx hy := by
    rw [decode_char tc ht x hx, decode_char tc ht y hy]
    unfold CharOk at hx hy
    simp only [pvEq, beq_iff_eq, List.cons.injEq, and_true]
    by_cases h : x = y
    · subst h; simp
    · have : x.toNat ≠ y.toNat := by omega
      simp [h, this]
  rich op x y hx hy hne := by
    rw [decode_char tc ht x hx, decode_char tc ht y hy]
    unfold CharOk at hx hy
    simp only [pvRich, strOrder]
    rcases Int.lt_or_gt_of_ne hne with hl | hl
    · rw [Int.compare_eq_lt.mpr hl, if_pos (by omega)]
    · rw [Int.compare_eq_gt.mpr hl, if_neg (by omega), if_pos (by omega)]

theorem decodes_char (a : Arr) (ht : a.tc = .u ∨ a.tc = .w) (h : a.Decodes) : ∀ x ∈ a.items, CharOk x := by
  intro x hx
  obtain ⟨v, hv⟩ := h x hx
  unfold CharOk
  rcases ht with ht | ht <;> rw [ht] at hv <;> simp only [tcGetitem] at hv <;> split at hv <;>
    first | omega | (simp at hv)

theorem hasCompare_cases (tc : TC) (h : tc.hasCompare = true) : tc.isInteger = true ∨ tc = .u ∨ tc = .w := by
  cases tc <;> simp_all [TC.hasCompare, TC.isInteger]

/-- The fast path agrees with the list comparison, given a decoder. -/
theorem rawCmp_list (op : CmpOp) (D : Int → PyVal) (P : Int → Prop) (hD : OrderDecoder D P)
    (xs ys : List Int) (hx : ∀ x ∈ xs, P x) (hy : ∀ y ∈ ys, P y) :
    listRichSpec op (xs.map D) (ys.map D) = .ok (rawCmp op xs ys) := by
  unfold listRichSpec rawCmp
  simp only [List.length_map]
  by_cases hl : xs.length ≠ ys.length ∧ (op = .eq ∨ op = .ne)
  · rw [if_pos hl, if_pos hl]
  · rw [if_neg hl, if_neg hl, rawFirstDiff_map D P hD xs ys hx hy]
    cases hr : rawFirstDiff xs ys with
    | none => rfl
    | some p =>
      obtain ⟨x, y⟩ := p
      obtain ⟨hne, hxm, hym⟩ := rawFirstDiff_ne _ _ _ _ hr
      simp only [Option.map_some]
      have := hD.rich op x y (hx x hxm) (hy y hym) hne
      cases op <;> simp_all [opHolds] <;> rcases Int.lt_or_gt_of_ne hne with hl | hl <;>
        simp [Int.compare_eq_lt.mpr, Int.compare_eq_gt.mpr, hl]

theorem arrayRichcompare_proven : ArrayRichcompare := by
  refine ⟨fun op v w hv hw => ?_, arrRich_fast, fun op v t => ⟨rfl, rfl⟩⟩
  unfold arrRichcompare
  simp only []
  by_cases hf : v.tc = w.tc ∧ v.tc.hasCompare = true
  · rw [arrRich_fast op v w hf.1 hf.2]
    rw [← hf.1]
    rcases hasCompare_cases v.tc hf.2 with hi | hch
    · rw [rawCmp_list op _ _ (intDecoder v.tc hi) v.items w.items (fun _ _ => trivial) (fun _ _ => trivial)]
      rfl
    · rw [rawCmp_list op _ _ (charDecoder v.tc hch) v.items w.items (decodes_char v hch hv)
        (decodes_char w (hf.1 ▸ hch) hw)]
      rfl
  · have hd : arrFirstDiff v w (v.items.length + 1) 0 =
        .ok (firstDiffL (v.items.map (decode v.tc)) (w.items.map (decode w.tc))) := by
      have := arrFirstDiff_spec v w hv hw (v.items.length + 1) 0 (by omega)
      simpa using this
    unfold arrRich listRichSpec
    simp only [List.length_map]
    by_cases hl : v.items.length ≠ w.items.length ∧ (op = .eq ∨ op = .ne)
    · rw [if_pos ⟨(by have := hl.1; omega), hl.2⟩, if_pos hl]; rfl
    · rw [if_neg (fun h => hl ⟨(by have := h.1; omega), h.2⟩), if_neg hl, if_neg hf, hd]
      cases firstDiffL (v.items.map (decode v.tc)) (w.items.map (decode w.tc)) with
      | none => rfl
      | some p =>
        obtain ⟨x, y⟩ := p
        cases op
        · dsimp only; cases pvRich .lt x y <;> rfl
        · dsimp only; cases pvRich .le x y <;> rfl
        · rfl
        · rfl
        · dsimp only; cases pvRich .gt x y <;> rfl
        · dsimp only; cases pvRich .ge x y <;> rfl

end PyLean.Sequences
