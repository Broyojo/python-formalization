import PyLean.BytesObj.Bytes.BasicProps2
import PyLean.BytesObj.Bytes.ByteArray

/-!
Properties of the `bytes` methods, third part.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## Comparison -/

theorem memcmp_self (n : Nat) (a : Seq) : memcmp n a a = 0 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    cases a with
    | nil => rfl
    | cons x xs => simp [memcmp, ih]

theorem memcmp_eq_iff (a b : Seq) (h : a.length = b.length) : memcmp a.length a b = 0 ↔ a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [memcmp]
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.length_cons, memcmp, List.cons.injEq]
      by_cases h1 : x < y
      · have : x ≠ y := by omega
        simp [h1, this]
      · by_cases h2 : x > y
        · have : x ≠ y := by omega
          simp [h1, h2, this]
        · have e : x = y := by omega
          subst e
          simp [ih ys h]

/-- The `memcmp` sign is decided by the first byte when it differs. -/
theorem memcmp_head (n : Nat) (x y : Nat) (xs ys : Seq) (hxy : x ≠ y) :
    memcmp (n + 1) (x :: xs) (y :: ys) = if x < y then -1 else 1 := by
  simp only [memcmp]
  by_cases h : x < y
  · simp [h]
  · have : x > y := by omega
    simp [h, this]

theorem richResult_sign (op : CmpOp) (d e : Int) (h1 : d < 0 ↔ e < 0) (h2 : d > 0 ↔ e > 0) :
    richResult op d 0 = richResult op e 0 := by
  cases op <;> simp only [richResult] <;> congr 1 <;> simp only [eq_iff_iff] <;> omega

/-- `bytes_richcompare` and `bytearray_richcompare`, written separately (the first has a
first-byte shortcut and a length test first, the second runs `memcmp` directly), agree on
every pair of byte strings and every operator; `==` is list equality and `!=` its
negation. -/
def RichcompareTwins : Prop :=
  ∀ (a b : Seq) (op : CmpOp),
    baRichcompare (.bytes a) (.bytes b) op = some (bytesRichcompare a b op) ∧
    bytesRichcompare a b .eq = decide (a = b) ∧ bytesRichcompare a b .ne = !decide (a = b)

theorem compareEq_spec (a b : Seq) : bytesCompareEq a b = decide (a = b) := by
  unfold bytesCompareEq
  by_cases hl : b.length = a.length
  · cases a with
    | nil =>
      have : b = [] := by simpa using hl
      subst this
      simp [memcmp]
    | cons x xs =>
      cases b with
      | nil => simp at hl
      | cons y ys =>
        simp only [hl, ne_eq, not_true_eq_false, if_false, List.headD_cons]
        by_cases hxy : x = y
        · subst hxy
          have := memcmp_eq_iff (x :: xs) (x :: ys) hl.symm
          simp only [not_true_eq_false, if_false]
          by_cases he : (x :: xs) = (x :: ys)
          · obtain rfl : xs = ys := by simpa using he
            simp [memcmp_self]
          · have h2 : ¬ memcmp (x :: xs).length (x :: xs) (x :: ys) = 0 := fun e => he (this.mp e)
            simp only [he, h2, decide_false]
        · have : (x :: xs) ≠ (y :: ys) := by simp [hxy]
          simp [hxy, this]
  · have : a ≠ b := by intro e; exact hl (by rw [e])
    simp [hl, this]

theorem ne_len (a b : Seq) (h : a.length ≠ b.length) : a ≠ b := fun e => h (by rw [e])

theorem richcompareTwins_proven : RichcompareTwins := by
  intro a b op
  have hE : bytesRichcompare a b .eq = decide (a = b) := by
    simp [bytesRichcompare, compareEq_spec]
  have hN : bytesRichcompare a b .ne = !decide (a = b) := by
    simp [bytesRichcompare, compareEq_spec]
  refine ⟨?_, hE, hN⟩
  simp only [baRichcompare, Obj.buffer?]
  by_cases hop : op = .eq ∨ op = .ne
  · rcases hop with rfl | rfl
    · rw [hE]
      by_cases hl : a.length = b.length
      · simp only [hl, ne_eq, not_true_eq_false, false_and, if_false]
        have := memcmp_eq_iff a b hl
        rw [← hl]
        by_cases he : a = b
        · subst he
          simp [memcmp_self, richResult]
        · have h2 : memcmp a.length a b ≠ 0 := fun e => he (this.mp e)
          simp [h2, he, richResult]
      · simp [hl, ne_len a b hl]
    · rw [hN]
      by_cases hl : a.length = b.length
      · simp only [hl, ne_eq, not_true_eq_false, false_and, if_false]
        have := memcmp_eq_iff a b hl
        rw [← hl]
        by_cases he : a = b
        · subst he
          simp [memcmp_self, richResult]
        · have h2 : memcmp a.length a b ≠ 0 := fun e => he (this.mp e)
          simp [h2, he, richResult]
      · simp [hl, ne_len a b hl]
  · have hq : (op = .eq ∨ op = .ne) = False := by simpa using hop
    simp only [hq, and_false, if_false, bytesRichcompare]
    cases a with
    | nil => simp [memcmp]
    | cons x xs =>
      cases b with
      | nil => simp [memcmp]
      | cons y ys =>
        simp only [List.length_cons]
        have hmin : min (xs.length + 1) (ys.length + 1) = min xs.length ys.length + 1 := by omega
        rw [hmin]
        have hpos : min xs.length ys.length + 1 > 0 := by omega
        simp only [hpos, if_true, List.headD_cons]
        by_cases hxy : x = y
        · subst hxy
          by_cases hm : memcmp (min xs.length ys.length + 1) (x :: xs) (x :: ys) = 0 <;> simp [hm]
        · have hd : (x : Int) - y ≠ 0 := by omega
          rw [memcmp_head _ _ _ _ _ hxy]
          have hne : (if x < y then (-1 : Int) else 1) ≠ 0 := by split <;> decide
          simp only [hd, if_false, hne, ne_eq, not_false_eq_true, if_true]
          congr 1
          apply richResult_sign
          · split <;> omega
          · split <;> omega

/-! ## Subscript -/

theorem seqData_seq (s : Seq) : (seqData s).map Int.toNat = s := by
  simp [seqData, Function.comp_def]

/-- A bytearray with contents `s`. -/
def baOf (s : Seq) : BA := { data := seqData s }

theorem baOf_seq (s : Seq) : (baOf s).seq = s := seqData_seq s
theorem baOf_size (s : Seq) : (baOf s).size = s.length := by simp [BA.size, baOf, seqData]

/-- `bytes[slice]` and `bytearray[slice]` hold the same bytes, for every slice object,
in spite of the extra full-slice shortcut of `bytes`; an index reads the byte at the
Python position and is an `IndexError` outside, for ints of any size. -/
def SubscriptTwins : Prop :=
  (∀ (s : Seq) (sl : RangeSlice.Slice), bytesGetSlice s sl = baGetSlice (baOf s) sl) ∧
  (∀ (s : Seq) (i : Int), ssizeMin ≤ i → i ≤ ssizeMax → 0 ≤ i → i < s.length →
    bytesGetItem s i = .ok (s.getD i.toNat 0)) ∧
  (∀ (s : Seq) (i : Int), ssizeMin ≤ i → i ≤ ssizeMax → i ≥ s.length →
    bytesGetItem s i = .error (.indexError "index out of range"))

theorem subscriptTwins_proven : SubscriptTwins := by
  refine ⟨?_, ?_, ?_⟩
  · intro s sl
    simp only [bytesGetSlice, baGetSlice, baOf_seq, baOf_size, bind, Except.bind, pure, Except.pure]
    cases RangeSlice.sliceUnpack sl with
    | error e => rfl
    | ok t =>
      obtain ⟨st, sp, step⟩ := t
      simp only
      generalize RangeSlice.adjustIndices (s.length : Int) st sp step = r
      obtain ⟨a, b, len⟩ := r
      simp only
      by_cases h1 : len ≤ 0
      · simp [h1]
      · simp only [h1, if_false]
        by_cases h2 : a = 0 ∧ step = 1 ∧ len = s.length
        · obtain ⟨rfl, rfl, rfl⟩ := h2
          simp
        · simp only [h2, if_false]
  · intro s i h1 h2 h3 h4
    have e : Sequences.subIndex i = .ok i := by
      simp [Sequences.subIndex, Sequences.asSsizeExc, h1, h2]
    have h5 : ¬ (i < 0) := by omega
    have h6 : ¬ (i < 0 ∨ i ≥ s.length) := by omega
    unfold bytesGetItem
    simp only [bind, Except.bind, e]
    rw [if_neg h5, if_neg h6]
    rfl
  · intro s i h1 h2 h3
    have e : Sequences.subIndex i = .ok i := by
      simp [Sequences.subIndex, Sequences.asSsizeExc, h1, h2]
    have h5 : ¬ (i < 0) := by omega
    unfold bytesGetItem
    simp only [bind, Except.bind, e]
    rw [if_neg h5, if_pos (Or.inr h3)]
    rfl

/-! ## join -/

/-- `sep.join(items)` for bytes items is the items with `sep` between them; the first
item that is no buffer gives a `TypeError` naming its position. List, tuple and generator
arguments are the same. Sizes stay below `sys.maxsize`, which is a type invariant of the
result (the C code's overflow check is what raises otherwise). -/
def JoinSpec : Prop :=
  (∀ (sep : Seq) (xs : List Seq),
    (xs.foldr (fun x n => (x.length : Int) + sep.length + n) 0 + sep.length ≤ ssizeMax) →
    pyBytesJoin (.bytes sep) (.list (xs.map .bytes)) = .ok (joinWrite sep xs) ∧
    pyBytesJoin (.bytes sep) (.tuple (xs.map .bytes)) = .ok (joinWrite sep xs) ∧
    pyBytesJoin (.bytes sep) (.iter (xs.map .bytes)) = .ok (joinWrite sep xs)) ∧
  (∀ (sep : Seq) (v : Int) (rest : List Obj), pyBytesJoin (.bytes sep) (.list (.int v :: rest)) =
    .error (.typeError s!"sequence item {0}: expected a bytes-like object, {(Obj.int v).typeName} found"))

theorem fold_nonneg (sep : Seq) (xs : List Seq) :
    0 ≤ xs.foldr (fun x n => (x.length : Int) + sep.length + n) 0 := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldr_cons]
    omega

theorem joinPass_ok (sep : Seq) (xs : List Seq) (i : Nat) (sz : Int) (h0 : 0 ≤ sz)
    (h : sz + xs.foldr (fun x n => (x.length : Int) + sep.length + n) 0 + sep.length ≤ ssizeMax) :
    ∃ t, joinPass sep i (xs.map .bytes) sz = .ok (xs, t) := by
  induction xs generalizing i sz with
  | nil => exact ⟨sz, rfl⟩
  | cons x xs ih =>
    have hf := fold_nonneg sep xs
    simp only [List.foldr_cons] at h
    have h1 : ¬ ((x.length : Int) > ssizeMax - sz) := by omega
    have h2 : ¬ (i ≠ 0 ∧ (sep.length : Int) > ssizeMax - (sz + x.length)) := by omega
    obtain ⟨t, ht⟩ := ih (i + 1) (if i ≠ 0 then sz + x.length + sep.length else sz + x.length)
      (by split <;> omega) (by split <;> omega)
    refine ⟨t, ?_⟩
    simp only [List.map_cons, joinPass, Obj.buffer?]
    rw [if_neg h1, if_neg h2, ht]

theorem joinSpec_proven : JoinSpec := by
  refine ⟨?_, ?_⟩
  · intro sep xs h
    obtain ⟨t, ht⟩ := joinPass_ok sep xs 0 0 (by omega) (by simpa using h)
    simp [pyBytesJoin, stringlibJoin, iterItems?, ht]
  · intro sep v rest
    simp [pyBytesJoin, stringlibJoin, iterItems?, joinPass, Obj.buffer?]

/-! ## translate -/

/-- `bytes.translate` and `bytearray.translate` (separate code, one checks `bytes` first,
the other goes through `PyObject_GetBuffer`) agree on every input; the no-delete fast loop
equals the general loop; and with no table the result is the bytes outside `delete`. -/
def TranslateTwins : Prop :=
  (∀ (s : Seq) (table : Obj) (del : Option Obj),
    bytesTranslate s table del = bytearrayTranslate s table del) ∧
  (∀ s t : Seq, translateFast s t = translateSlow s (some t) []) ∧
  (∀ s del : Seq, translateSlow s none del = s.filter (fun c => decide (c ∉ del)))

theorem translateTwins_proven : TranslateTwins := by
  refine ⟨?_, ?_, ?_⟩
  · intro s table del
    cases table
    case bytes v =>
      unfold bytesTranslate bytearrayTranslate
      simp only [tableArg, getBuffer, Obj.buffer?, bind, Except.bind, pure, Except.pure, Option.map,
        Option.getD]
    case bytearray v =>
      unfold bytesTranslate bytearrayTranslate
      simp only [tableArg, getBuffer, Obj.buffer?, bind, Except.bind, pure, Except.pure, Option.map,
        Option.getD]
    case memview v a =>
      unfold bytesTranslate bytearrayTranslate
      simp only [tableArg, getBuffer, Obj.buffer?, bind, Except.bind, pure, Except.pure, Option.map,
        Option.getD]
    all_goals rfl
  · intro s t
    simp [translateFast, translateSlow, List.filterMap_eq_map]
  · intro s del
    have step : ∀ l : Seq, l.filterMap (fun c => if del.contains c = true then none else some c) =
        l.filter (fun c => decide (c ∉ del)) := by
      intro l
      induction l with
      | nil => rfl
      | cons c cs ih =>
        rw [List.filterMap_cons, List.filter_cons, ih]
        by_cases h : c ∈ del
        · have h1 : del.contains c = true := by simpa using h
          simp [h, h1]
        · have h1 : ¬ (del.contains c = true) := by simpa using h
          simp [h, h1]
    exact step s

end PyLean.BytesObj.Bytes
