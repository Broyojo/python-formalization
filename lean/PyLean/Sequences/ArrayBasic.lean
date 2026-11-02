import PyLean.Sequences.ArrayModel
import PyLean.Sequences.Insert

/-!
Basic facts about the `array.array` model: `array_resize`, the conversions of
each typecode, `ins1`, `array_del_slice`.
-/

namespace PyLean.Sequences

open PyLean

set_option linter.unusedSectionVars false

/-- A list identity, position by position. -/
macro "list_ext" : tactic => `(tactic| (
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_append, List.getElem?_take, List.getElem?_drop, List.length_append,
    List.length_take, List.length_drop, List.length_cons, List.length_nil, List.getElem?_cons,
    List.getElem?_set, List.getElem?_nil]
  repeat' split
  all_goals first
    | rfl
    | (exfalso; omega)
    | (congr 1; omega)
    | (apply List.getElem?_eq_none; omega)
    | (symm; apply List.getElem?_eq_none; omega)
    | (rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)])
    | skip))

theorem itemsize_cases (tc : TC) :
    tc.itemsize = 1 ∨ tc.itemsize = 2 ∨ tc.itemsize = 4 ∨ tc.itemsize = 8 ∨ tc.itemsize = 16 := by
  cases tc <;> simp [TC.itemsize]

/-- The array fits: `n` items of this typecode are below `sys.maxsize` bytes. -/
def Arr.Fits (a : Arr) (n : Int) : Prop := n ≤ ssizeMax / a.tc.itemsize

theorem memmove_ok {α : Type} (mem : List α) (dst src cnt : Int) (h1 : 0 ≤ dst) (h2 : 0 ≤ src) (h3 : 0 ≤ cnt)
    (h4 : dst + cnt ≤ mem.length) (h5 : src + cnt ≤ mem.length) :
    memmove mem dst src cnt =
      .ok (mem.take dst.toNat ++ (mem.drop src.toNat).take cnt.toNat ++ mem.drop (dst + cnt).toNat) := by
  unfold memmove
  rw [iteT ⟨h1, h2, h3, h4, h5⟩]

theorem resized_le (l : List Int) (n : Int) (h0 : 0 ≤ n) (h : n ≤ l.length) : resized l n = l.take n.toNat := by
  unfold resized; rw [iteT h]

theorem resized_gt (l : List Int) (n : Int) (h : ¬ n ≤ l.length) :
    resized l n = l ++ List.replicate (n - l.length).toNat 0 := by
  unfold resized; rw [iteF h]

theorem length_resized (l : List Int) (n : Int) (h0 : 0 ≤ n) : ((resized l n).length : Int) = n := by
  unfold resized
  split
  · simp only [List.length_take]; omega
  · simp only [List.length_append, List.length_replicate]; omega

/-- `array_resize` without exports, within the address space: the items are
truncated or extended, the rest of the object stays. -/
theorem arrResize_ok (a : Arr) (n : Int) (hx : a.exports = 0) (h0 : 0 ≤ n) (hn : a.Fits n) :
    ∃ a', arrResize a n = .ok a' ∧ a'.items = resized a.items n ∧ a'.tc = a.tc ∧ a'.exports = 0 ∧
      a'.tname = a.tname := by
  unfold arrResize Arr.Fits at *
  dsimp only
  rw [iteF (by omega)]
  split
  · exact ⟨_, rfl, rfl, rfl, hx, rfl⟩
  · split
    · rename_i hz
      refine ⟨_, rfl, ?_, rfl, hx, rfl⟩
      subst hz
      rw [resized_le _ _ (by omega) (by omega)]; simp
    · have hc := itemsize_cases a.tc
      unfold ssizeMax at hn
      have : n / 16 + (if (a.items.length : Int) < 8 then 3 else 7) + n ≤ 18446744073709551615 / a.tc.itemsize := by
        rcases hc with h | h | h | h | h <;> rw [h] at hn ⊢ <;> split <;> omega
      rw [iteT this]
      exact ⟨_, rfl, rfl, rfl, hx, rfl⟩

/-- With exports, only a resize that keeps the size passes. -/
theorem arrResize_exported (a : Arr) (n : Int) (hx : a.exports > 0) (h : n ≠ a.items.length) :
    arrResize a n = .error bufferErr := by
  unfold arrResize
  dsimp only
  rw [iteT ⟨hx, h⟩]

/-! ### Conversions -/

theorem throwE {α : Type} (e : PyExc) : (throw e : Py α) = .error e := rfl

theorem asLongV_ok (n : Int) (h0 : longMin ≤ n) (h1 : n ≤ longMax) : asLongV (.int n) = .ok n := by
  simp only [asLongV, toIndex, bind, Except.bind, pure, Except.pure]
  rw [iteT ⟨h0, h1⟩]

/-- `TC.isInteger` typecodes store exactly the ints of their range, and refuse
others with `OverflowError` (`__index__` objects are the same). -/
theorem tcSetitem_int (tc : TC) (hi : tc.isInteger = true) (v : PyVal) (n : Int) (hv : toIndex v = .ok n) :
    (tc.lo ≤ n ∧ n ≤ tc.hi → tcSetitem tc true v = .ok n) ∧
    (¬ (tc.lo ≤ n ∧ n ≤ tc.hi) → (tcSetitem tc true v).raises "OverflowError") := by
  by_cases hl : longMin ≤ n ∧ n ≤ longMax
  · have hal : asLongV v = .ok n := by
      simp only [asLongV, hv, bind, Except.bind, pure, Except.pure]; rw [iteT hl]
    unfold longMin longMax at hl
    constructor
    · intro h
      cases tc <;> first | exact absurd hi (by decide) | skip
      all_goals simp only [TC.lo, TC.hi] at h
      all_goals simp only [tcSetitem, hal, hv, bind, Except.bind, pure, Except.pure, Bool.not_true,
        Bool.false_eq_true, ite_false, longMin, longMax, throwE]
      all_goals (repeat' split)
      all_goals first | rfl | (exfalso; omega)
    · intro h
      cases tc <;> first | exact absurd hi (by decide) | skip
      all_goals simp only [TC.lo, TC.hi] at h
      all_goals simp only [tcSetitem, hal, hv, bind, Except.bind, pure, Except.pure, Bool.not_true,
        Bool.false_eq_true, ite_false, longMin, longMax, throwE]
      all_goals (repeat' split)
      all_goals first | (exfalso; omega) | (refine ⟨_, rfl, ?_⟩; rfl)
  · have hal : asLongV v = .error (.overflowError "Python int too large to convert to C long") := by
      simp only [asLongV, hv, bind, Except.bind]; rw [iteF hl]; rfl
    unfold longMin longMax at hl
    constructor
    · intro h
      cases tc <;> first | exact absurd hi (by decide) | skip
      all_goals simp only [TC.lo, TC.hi] at h
      all_goals first
        | (exfalso; omega)
        | skip
      all_goals simp only [tcSetitem, hal, hv, bind, Except.bind, pure, Except.pure, Bool.not_true,
        Bool.false_eq_true, ite_false, longMin, longMax, throwE]
      all_goals (repeat' split)
      all_goals first | rfl | (exfalso; omega)
    · intro h
      cases tc <;> first | exact absurd hi (by decide) | skip
      all_goals simp only [TC.lo, TC.hi] at h
      all_goals simp only [tcSetitem, hal, hv, bind, Except.bind, pure, Except.pure, Bool.not_true,
        Bool.false_eq_true, ite_false, longMin, longMax, throwE]
      all_goals (repeat' split)
      all_goals first | (exfalso; omega) | (refine ⟨_, rfl, ?_⟩; rfl)

/-- `tcGetitem` of an integer typecode is the C value. -/
theorem tcGetitem_int (tc : TC) (hi : tc.isInteger = true) (x : Int) : tcGetitem tc x = .ok (.int x) := by
  cases tc <;> first | exact absurd hi (by decide) | rfl

theorem tcSetitem_range (tc : TC) (hi : tc.isInteger = true) (x : Int) (h : tc.lo ≤ x ∧ x ≤ tc.hi) :
    tcSetitem tc true (.int x) = .ok x := (tcSetitem_int tc hi (.int x) x rfl).1 h

/-! ### `ins1` -/

theorem ins_memmove (l : List Int) (w : Nat) (x : Int) (h : w < l.length) :
    ((l ++ [0]).take (w + 1) ++ ((l ++ [0]).drop w).take (l.length - w) ++ (l ++ [0]).drop (l.length + 1)).set w x
      = insAt l w x := by
  unfold insAt
  list_ext

/-- A value `setitem` stores at an index also passes `setitem(self, -1, v)`. -/
theorem tcCheck_of_set (tc : TC) (v : PyVal) (x : Int) (h : tcSetitem tc true v = .ok x) :
    tcCheck tc v = .ok () := by
  cases tc
  case e =>
    simp only [tcCheck]
    cases hd : asDouble v with
    | ok b => rfl
    | error e => simp [tcSetitem, hd, bind, Except.bind] at h
  all_goals simp only [tcCheck, h]

/-- Only `e` refuses more at an index than at `-1`. -/
theorem tcCheck_err (tc : TC) (v : PyVal) (e : PyExc) (ht : tc ≠ .e) (h : tcSetitem tc true v = .error e) :
    tcCheck tc v = .error e := by
  cases tc
  case e => exact absurd rfl ht
  all_goals simp only [tcCheck, h]

theorem arrIns1S_err (a : Arr) (w : Int) (v : PyVal) (e : PyExc) (h : tcCheck a.tc v = .error e) :
    arrIns1S a w v = (a, some e) := by
  unfold arrIns1S
  simp only [h]

theorem arrIns1S_ok (a : Arr) (where_ : Int) (v : PyVal) (x : Int) (hx : a.exports = 0)
    (hs : tcSetitem a.tc true v = .ok x) (hn : a.Fits (a.items.length + 1)) :
    ∃ a', arrIns1S a where_ v = (a', none) ∧ a'.items = insAt a.items (ins1Pos a.items.length where_).toNat x ∧
      a'.tc = a.tc ∧ a'.exports = 0 ∧ a'.tname = a.tname := by
  obtain ⟨a1, hr, hi, ht, he, htn⟩ := arrResize_ok a (a.items.length + 1) hx (by omega) hn
  have hres : a1.items = a.items ++ [0] := by
    rw [hi, resized_gt _ _ (by omega), show ((a.items.length : Int) + 1 - a.items.length).toNat = 1 by omega]
    rfl
  have hb := ins1Pos_bounds a.items.length where_ (by omega)
  generalize hw : ins1Pos a.items.length where_ = w at hb
  unfold arrIns1S
  simp only [tcCheck_of_set _ _ _ hs, hr, hw, hs]
  by_cases hend : w = a.items.length
  · simp only [hend, ne_eq, not_true_eq_false, ite_false]
    refine ⟨_, rfl, ?_, ht, he, htn⟩
    show a1.items.set _ x = _
    rw [hres]
    unfold insAt
    rw [show ((a.items.length : Int)).toNat = a.items.length by omega, List.take_length, List.drop_length]
    list_ext
  · have hlen : (a1.items.length : Int) = a.items.length + 1 := by rw [hres]; simp
    rw [iteT hend, memmove_ok _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp only
    refine ⟨_, rfl, ?_, ht, he, htn⟩
    show List.set _ _ x = _
    rw [hres, show (w + 1).toNat = w.toNat + 1 by omega, show (a.items.length - w : Int).toNat = a.items.length - w.toNat by omega,
      show (w + 1 + ((a.items.length : Int) - w)).toNat = a.items.length + 1 by omega]
    exact ins_memmove a.items w.toNat x (by omega)

theorem arrIns1_ok (a : Arr) (where_ : Int) (v : PyVal) (x : Int) (hx : a.exports = 0)
    (hs : tcSetitem a.tc true v = .ok x) (hn : a.Fits (a.items.length + 1)) :
    ∃ a', arrIns1 a where_ v = .ok a' ∧ a'.items = insAt a.items (ins1Pos a.items.length where_).toNat x ∧
      a'.tc = a.tc ∧ a'.exports = 0 ∧ a'.tname = a.tname := by
  obtain ⟨a', h1, h2⟩ := arrIns1S_ok a where_ v x hx hs hn
  exact ⟨a', by simp only [arrIns1, h1], h2⟩

/-! ### `array_del_slice` -/

theorem del_memmove (l : List Int) (lo hi : Nat) (h1 : lo ≤ hi) (h2 : hi ≤ l.length) :
    (l.take lo ++ (l.drop hi).take (l.length - hi) ++ l.drop (lo + (l.length - hi))).take (l.length - (hi - lo))
      = l.take lo ++ l.drop hi := by
  list_ext

/-- `array_del_slice` for `0 <= lo <= hi <= len` without exports. -/
theorem arrDelSlice_ok (a : Arr) (lo hi : Int) (hx : a.exports = 0) (h0 : 0 ≤ lo) (h1 : lo ≤ hi)
    (h2 : hi ≤ a.items.length) (hf : a.Fits a.items.length) :
    ∃ a', arrDelSlice a lo hi = .ok a' ∧ a'.items = a.items.take lo.toNat ++ a.items.drop hi.toNat ∧
      a'.tc = a.tc ∧ a'.exports = 0 ∧ a'.tname = a.tname := by
  unfold arrDelSlice
  simp only [bind, Except.bind, pure, Except.pure]
  have e1 : (if lo < 0 then 0 else if lo > (a.items.length : Int) then (a.items.length : Int) else lo) = lo := by
    split <;> (try split) <;> omega
  have e2 : (if hi < 0 then 0 else hi) = hi := by split <;> omega
  have e3 : (if hi < lo then lo else if hi > (a.items.length : Int) then (a.items.length : Int) else hi) = hi := by
    split <;> (try split) <;> omega
  rw [e1, e2, e3]
  rw [iteF (show ¬ (hi - lo ≠ 0 ∧ a.exports > 0) by omega)]
  by_cases hd : hi - lo > 0
  · rw [iteT hd, memmove_ok _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp only
    obtain ⟨a', hr, hi', ht, he, htn⟩ := arrResize_ok
      { a with items := a.items.take (hi - (hi - lo)).toNat ++ (a.items.drop hi.toNat).take ((a.items.length : Int) - hi).toNat ++ a.items.drop (hi - (hi - lo) + ((a.items.length : Int) - hi)).toNat }
      ((a.items.length : Int) - (hi - lo)) hx (by omega) (by unfold Arr.Fits at *; simp only; omega)
    rw [hr]
    refine ⟨a', rfl, ?_, ht, he, htn⟩
    rw [hi', resized_le _ _ (by omega) (by simp only [List.length_append, List.length_take, List.length_drop]; omega)]
    list_ext
  · rw [iteF hd]
    refine ⟨a, rfl, ?_, rfl, hx, rfl⟩
    have : lo = hi := by omega
    subst this
    simp

end PyLean.Sequences
