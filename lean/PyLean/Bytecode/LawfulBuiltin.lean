import PyLean.Bytecode.Props

/-!
The concrete object model satisfies `Lawful`: every specialization theorem's hypothesis about
the builtin slots holds of `Proto.builtinOM`, the model the difftest runs.

`builtinOM P` is `mkOM P 24`, a fuel-indexed record whose fields call the implementations at
fuel 23. Each law below is proved about the implementation for an arbitrary inner model, and
the record is unfolded by one level only. On a builtin immediate the user-method lookup walks a
builtin MRO, which holds no user dict, so it finds nothing and the builtin slot answers.
-/

namespace PyLean.Bytecode

open Proto Uop

theorem go_cls (name : String) (l : List String) (s : Rt) :
    userLookup.go name (l.map Val.cls) s = .ok none s := by
  induction l with
  | nil => rfl
  | cons x xs ih => simpa [userLookup.go] using ih

theorem userLookup_cls (n name : String) (s : Rt) :
    userLookup (.cls n) name s = .ok none s := by
  simp [userLookup, mroOf, bind, EStateM.bind, pure, EStateM.pure, go_cls]

theorem ord_beq (x y : Ordering) : (x == y) = decide (x = y) := by cases x <;> cases y <;> rfl
theorem ord_bne (x y : Ordering) : (x != y) = !decide (x = y) := by cases x <;> cases y <;> rfl

/-- The table of `Lawful.cmp_int`. -/
def cmpTable (op : Nat) (a b : Int) : Bool :=
  match op with
  | 0 => decide (a < b) | 1 => decide (a ≤ b) | 2 => decide (a = b)
  | 3 => decide (a ≠ b) | 4 => decide (a > b) | _ => decide (a ≥ b)

/-- `PyObject_RichCompare` on a total order agrees with the `ordResult` table. -/
theorem ordResult_int (a b : Int) (op : Nat) (h : op < 6) :
    ordResult (compare a b) op = cmpTable op a b := by
  unfold cmpTable
  obtain h | h | h | h | h | h : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 ∨ op = 4 ∨ op = 5 := by omega
  all_goals
    subst h
    cases hc : compare a b
    all_goals
      first
      | (have := Int.compare_eq_lt.1 hc; simp [ordResult, hc, ord_beq, ord_bne] <;> omega)
      | (have := Int.compare_eq_gt.1 hc; simp [ordResult, hc, ord_beq, ord_bne] <;> omega)
      | (have := Int.compare_eq_eq.1 hc; subst this; simp [ordResult, ord_beq, ord_bne])

section Impl
variable (om : ObjModel) (ctx : Ctx)

theorem isTrue_list (a : Addr) (items : Array Val) (rt : Rt) (h : rt.heap[a]? = some (.list items)) :
    isTrueImpl om ctx (.ref a) rt = .ok (items.size != 0) rt := by
  simp [isTrueImpl, getObj, h, bind, EStateM.bind, pure, EStateM.pure]

theorem binary_int (nb : Nat) (a b : Int) (rt : Rt) (x : Val) (hnb : nb ≠ 26)
    (h : intBinary (if nb ≥ 13 then nb - 13 else nb) a b rt = .ok (some x) rt) :
    binaryOpImpl om ctx nb (.int a) (.int b) rt = .ok x rt := by
  have h26 : (nb == 26) = false := by simpa using hnb
  simp only [binaryOpImpl, h26]
  by_cases hi : nb ≥ 13
  · simp only [hi, ite_true] at h
    simp [hi, typeOf, immType, userLookup_cls, isSubtype, mroOf, payload, bind, EStateM.bind, pure,
      EStateM.pure, builtinBinary, intOf, h]
  · simp only [hi, ite_false] at h
    simp [hi, typeOf, immType, userLookup_cls, isSubtype, mroOf, payload, bind, EStateM.bind, pure,
      EStateM.pure, builtinBinary, intOf, h]

theorem binary_float (nb : Nat) (a b : UInt64) (rt : Rt) (x : Val) (hnb : nb ≠ 26)
    (h : floatBinary (if nb ≥ 13 then nb - 13 else nb) a b rt = .ok (some x) rt) :
    binaryOpImpl om ctx nb (.float a) (.float b) rt = .ok x rt := by
  have h26 : (nb == 26) = false := by simpa using hnb
  simp only [binaryOpImpl, h26]
  by_cases hi : nb ≥ 13
  · simp only [hi, ite_true] at h
    simp [hi, typeOf, immType, userLookup_cls, isSubtype, mroOf, payload, bind, EStateM.bind, pure, EStateM.pure, builtinBinary, intOf, h]
  · simp only [hi, ite_false] at h
    simp [hi, typeOf, immType, userLookup_cls, isSubtype, mroOf, payload, bind, EStateM.bind, pure, EStateM.pure, builtinBinary, intOf, h]

theorem seqBinary_str (a b : String) (rt : Rt) :
    seqBinary om ctx 0 (.str a) (.str b) rt = .ok (some (.str (a ++ b))) rt := rfl

theorem binary_str (nb : Nat) (a b : String) (rt : Rt) (hnb : nb = 0 ∨ nb = 13) :
    binaryOpImpl om ctx nb (.str a) (.str b) rt = .ok (.str (a ++ b)) rt := by
  have h26 : (nb == 26) = false := by rcases hnb with rfl | rfl <;> rfl
  have hbase : (if nb ≥ 13 then nb - 13 else nb) = 0 := by rcases hnb with rfl | rfl <;> rfl
  simp only [binaryOpImpl, h26]
  by_cases hi : nb ≥ 13
  · have h0 : nb - 13 = 0 := by simpa [hi] using hbase
    simp [hi, h0, typeOf, immType, userLookup_cls, isSubtype, mroOf, payload, bind, EStateM.bind, pure, EStateM.pure, builtinBinary, intOf, seqBinary_str]
  · have h0 : nb = 0 := by simpa [hi] using hbase
    simp [hi, h0, typeOf, immType, userLookup_cls, isSubtype, mroOf, payload, bind, EStateM.bind, pure, EStateM.pure, builtinBinary, intOf, seqBinary_str]

theorem getItem_seq (a : Addr) (o : Obj) (items : Array Val) (i : Int) (v : Val) (rt : Rt)
    (h : rt.heap[a]? = some o) (ho : o = .list items ∨ o = .tuple items)
    (hb : PyLean.ssizeMin ≤ i ∧ i ≤ PyLean.ssizeMax)
    (h0 : 0 ≤ (if i < 0 then i + items.size else i))
    (hv : items[(if i < 0 then i + items.size else i).toNat]? = some v) :
    getItemImpl om ctx (.ref a) (.int i) rt = .ok v rt := by
  have hlt : (if i < 0 then i + items.size else i) < items.size := by
    have := (Array.getElem?_eq_some_iff.1 hv).1
    omega
  have hgd : items.getD (if i < 0 then i + items.size else i).toNat .null = v := by
    simp [Array.getD_eq_getD_getElem?, hv]
  have hrange : ¬ (if i < 0 then i + items.size else i) < 0 := by omega
  have hb1 : ¬ i > PyLean.ssizeMax := by omega
  have hb2 : ¬ i < PyLean.ssizeMin := by omega
  rcases ho with rfl | rfl <;>
  simp [getItemImpl, typeOf, immType, userLookup_cls, isSubtype, mroOf, payload, bind, EStateM.bind, pure, EStateM.pure, getObj, h, asIndex, indexSsize, hb1, hb2, hv, hrange,
    Int.not_le.2 hlt, Int.not_lt.2 h0]

theorem getItem_str (s : String) (i : Nat) (c : Char) (rt : Rt) (hc : s.toList[i]? = some c)
    (hb : (i : Int) ≤ PyLean.ssizeMax) :
    getItemImpl om ctx (.str s) (.int i) rt = .ok (.str (String.singleton c)) rt := by
  have hlt : i < s.toList.length := (List.getElem?_eq_some_iff.1 hc).1
  have hb1 : ¬ (i : Int) > PyLean.ssizeMax := by omega
  have hb2 : ¬ (i : Int) < PyLean.ssizeMin := by unfold PyLean.ssizeMin; omega
  have hn : ¬ (i : Int) < 0 := by omega
  have hnle : ¬ s.toList.length ≤ i := by omega
  obtain ⟨_, hget⟩ := List.getElem?_eq_some_iff.1 hc
  simp [getItemImpl, typeOf, immType, userLookup_cls, isSubtype, mroOf, payload, bind, EStateM.bind, pure, EStateM.pure, asIndex, indexSsize, hb1, hb2, hn, hlt, hc, hnle, hget]

theorem compare_int (a b : Int) (op : Nat) (rt : Rt) :
    richCompareImpl om ctx (.int a) (.int b) op rt = .ok (.bool (ordResult (compare a b) op)) rt := by
  simp [richCompareImpl, typeOf, immType, userLookup_cls, isSubtype, mroOf, payload, bind, EStateM.bind, pure, EStateM.pure, builtinCompare, intOf]

theorem compare_str (a b : String) (op : Nat) (rt : Rt) :
    richCompareImpl om ctx (.str a) (.str b) op rt = .ok (.bool (ordResult (compare a b) op)) rt := by
  simp [richCompareImpl, typeOf, immType, userLookup_cls, isSubtype, mroOf, payload, bind, EStateM.bind, pure, EStateM.pure, builtinCompare]

end Impl

theorem subscr_impl (om : ObjModel) (ctx : Ctx) (l r : Val) (rt : Rt) :
    binaryOpImpl om ctx 26 l r rt = getItemImpl om ctx l r rt := by
  simp [binaryOpImpl, bind, EStateM.bind]

theorem lawfulBuiltin_proven : LawfulBuiltin := by
  intro P
  refine {
    true_bool := fun _ _ _ => rfl
    true_int := fun _ _ _ => rfl
    true_none := fun _ _ => rfl
    true_str := fun _ _ _ => rfl
    true_list := fun ctx a items rt h => isTrue_list (mkOM P 23) ctx a items rt h
    add_int := fun ctx nb a b rt hnb => binary_int (mkOM P 23) ctx nb a b rt _ (by omega)
      (by rcases hnb with rfl | rfl <;> rfl)
    sub_int := fun ctx nb a b rt hnb => binary_int (mkOM P 23) ctx nb a b rt _ (by omega)
      (by rcases hnb with rfl | rfl <;> rfl)
    mul_int := fun ctx nb a b rt hnb => binary_int (mkOM P 23) ctx nb a b rt _ (by omega)
      (by rcases hnb with rfl | rfl <;> rfl)
    add_float := fun ctx nb a b rt hnb => binary_float (mkOM P 23) ctx nb a b rt _ (by omega)
      (by rcases hnb with rfl | rfl <;> rfl)
    sub_float := fun ctx nb a b rt hnb => binary_float (mkOM P 23) ctx nb a b rt _ (by omega)
      (by rcases hnb with rfl | rfl <;> rfl)
    mul_float := fun ctx nb a b rt hnb => binary_float (mkOM P 23) ctx nb a b rt _ (by omega)
      (by rcases hnb with rfl | rfl <;> rfl)
    add_str := fun ctx nb a b rt hnb => binary_str (mkOM P 23) ctx nb a b rt hnb
    or_int := fun ctx nb a b rt hnb => binary_int (mkOM P 23) ctx nb a b rt _ (by omega)
      (by rcases hnb with rfl | rfl <;> rfl)
    and_int := fun ctx nb a b rt hnb => binary_int (mkOM P 23) ctx nb a b rt _ (by omega)
      (by rcases hnb with rfl | rfl <;> rfl)
    xor_int := fun ctx nb a b rt hnb => binary_int (mkOM P 23) ctx nb a b rt _ (by omega)
      (by rcases hnb with rfl | rfl <;> rfl)
    subscr := fun ctx l r => funext fun rt => subscr_impl (mkOM P 23) ctx l r rt
    list_item := fun ctx a items i v rt h hv hb =>
      getItem_seq (mkOM P 23) ctx a _ items i v rt h (Or.inl rfl)
        ⟨by unfold PyLean.ssizeMin; omega, hb⟩ (by simp [show ¬ ((i : Int) < 0) by omega])
        (by simpa [show ¬ ((i : Int) < 0) by omega] using hv)
    list_item_neg := fun ctx a items i v rt h hneg hv h0 hb =>
      getItem_seq (mkOM P 23) ctx a _ items i v rt h (Or.inl rfl)
        ⟨hb, by unfold PyLean.ssizeMax; omega⟩ (by simp [hneg]; omega) (by simpa [hneg] using hv)
    tuple_item := fun ctx a items i v rt h hv hb =>
      getItem_seq (mkOM P 23) ctx a _ items i v rt h (Or.inr rfl)
        ⟨by unfold PyLean.ssizeMin; omega, hb⟩ (by simp [show ¬ ((i : Int) < 0) by omega])
        (by simpa [show ¬ ((i : Int) < 0) by omega] using hv)
    str_item := fun ctx s i c rt hc hb => getItem_str (mkOM P 23) ctx s i c rt hc hb
    cmp_int := fun ctx a b op rt hop => by
      show richCompareImpl (mkOM P 23) ctx (.int a) (.int b) op rt = _
      rw [compare_int, ordResult_int a b op hop]
      rfl
    cmp_str := fun ctx a b rt => by
      show richCompareImpl (mkOM P 23) ctx (.str a) (.str b) 2 rt = _
      rw [compare_str]
      simp only [ordResult, ord_beq, Std.compare_eq_iff_eq]
      by_cases hab : a = b <;> simp [hab]
    cmp_str_ne := fun ctx a b rt => by
      show richCompareImpl (mkOM P 23) ctx (.str a) (.str b) 3 rt = _
      rw [compare_str]
      simp only [ordResult, ord_bne, Std.compare_eq_iff_eq]
      by_cases hab : a = b <;> simp [hab] }

end PyLean.Bytecode
