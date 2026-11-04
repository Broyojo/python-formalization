import PyLean.Sequences.ArrayText
import PyLean.Sequences.ArraySubscr

/-!
Pickling support of `array.array`: the iterator's `__reduce__`/`__setstate__`
(arraymodule.c:3386-3426) and the machine format codes of `typecode_to_mformat_code`
(:2138-2233) read back through the slow path of `_array_reconstructor` (:2339-2544).
-/

namespace PyLean.Sequences

open PyLean

set_option linter.unusedSectionVars false

/-! ### The iterator -/

theorem arrDrain_past (a : Arr) (i : Int) (F : Nat) (h : (a.items.length : Int) ≤ i) :
    arrDrain a F ⟨i, true⟩ = [] := by
  cases F with
  | zero => rfl
  | succ F =>
    simp only [arrDrain, arrIterNext, Bool.not_true, Bool.false_eq_true, ite_false]
    rw [iteF (by omega)]

/-- `pickle` of an array iterator. For every array `a` and position `0 <= i <= PY_SSIZE_T_MAX`
of a live iterator (the index is a `Py_ssize_t` that only grows from 0): `it.__reduce__()` is
`(iter, (a,), i)`, the builtin `iter`, the array itself and the position, and calling
`iter(a)` then `__setstate__(i)` gives an iterator that yields exactly what `it` yields (also
when `a` shrank below `i`, where both yield nothing); an exhausted iterator reduces to
`(iter, ((),))`. `__setstate__` converts its argument with `PyLong_AsSsize_t` before it looks
at `ao`, for a live and an exhausted iterator alike: a state that is not an int or int
subclass (a float, an object with only `__index__`, None) raises
`TypeError("an integer is required")`, an int outside `Py_ssize_t` `OverflowError`; an int
subclass is taken by its value. -/
def ArrayIterPickle : Prop :=
  ∀ (a : Arr) (i : Int) (it : ArrIter) (state : PyVal),
    (0 ≤ i → i ≤ ssizeMax →
      arrIterReduce a ⟨i, true⟩ = .live "iter" a i ∧
      ∃ it2, arrIterSetstate a arrIter (.int i) = .ok it2 ∧ ∀ F, arrDrain a F it2 = arrDrain a F ⟨i, true⟩) ∧
    arrIterReduce a ⟨i, false⟩ = .exhausted "iter" ∧
    ((∀ n, state ≠ .int n) → (∀ t n f x c, state ≠ .user t (.int n) f x c) →
      arrIterSetstate a it state = .error (.typeError "an integer is required")) ∧
    ((i < ssizeMin ∨ i > ssizeMax) →
      arrIterSetstate a it (.int i) = .error (.overflowError "Python int too large to convert to C ssize_t")) ∧
    (∀ t f x c, arrIterSetstate a it (.user t (.int i) f x c) = arrIterSetstate a it (.int i))

theorem arrayIterPickle_proven : ArrayIterPickle := by
  intro a i it state
  refine ⟨fun h0 h1 => ⟨rfl, ?_⟩, rfl, fun hn hu => ?_, fun h => ?_, fun _ _ _ _ => rfl⟩
  · have hs : asSsize i = .ok i := by unfold asSsize; rw [iteT ⟨by unfold ssizeMin ssizeMax at *; omega, h1⟩]
    refine ⟨⟨if i < 0 then 0 else if i > a.items.length then a.items.length else i, true⟩,
      by simp only [arrIterSetstate, iterStateIndex, hs, bind, Except.bind, pure, Except.pure, arrIter,
      ite_true], fun F => ?_⟩
    rw [iteF (by omega)]
    by_cases hl : i > a.items.length
    · rw [iteT hl, arrDrain_past a _ F (by omega), arrDrain_past a _ F (by omega)]
    · rw [iteF hl]
  · unfold arrIterSetstate iterStateIndex
    cases state with
    | int n => exact absurd rfl (hn n)
    | user t b f x c =>
      cases b with
      | int n => exact absurd rfl (hu t n f x c)
      | _ => rfl
    | _ => rfl
  · have : asSsize i = .error (.overflowError "Python int too large to convert to C ssize_t") := by
      unfold asSsize; rw [iteF (by omega)]
    simp only [arrIterSetstate, iterStateIndex, this, bind, Except.bind]

/-! ### Machine format codes -/

theorem digits_add (m k u : Nat) : digits (m + k) u = digits m u ++ digits k (u / 256 ^ m) := by
  induction m generalizing u with
  | zero => simp [digits]
  | succ m ih =>
    rw [show m + 1 + k = (m + k) + 1 by omega, digits_succ, digits_succ, ih, List.cons_append,
      Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 256]

theorem leValue_split (u m k : Nat) :
    leValue ((digits (m + k) u).take m) = u % 2 ^ (8 * m) ∧
      leValue ((digits (m + k) u).drop m) = (u / 256 ^ m) % 2 ^ (8 * k) := by
  rw [digits_add]
  have hl : (digits m u).length = m := by simp [digits]
  rw [List.take_left' hl, List.drop_left' hl, leValue_digits, leValue_digits]
  exact ⟨rfl, rfl⟩

/-- The integer typecode the reconstructor's slow path picks for an integer machine format:
the last descriptor with that size and signedness (arraymodule.c:2504-2511), `q`/`Q` for the
8-byte rows. -/
def intCanon : TC → TC
  | .l => .q
  | .L => .Q
  | t => t

/-- What the slow path of `_array_reconstructor` makes of the bytes of one item stored under
typecode `tc`, read with the machine format `mformatOf tc`: the integer
(`_PyLong_FromByteArray`, :2527-2531), or the float or complex of the IEEE pattern
(`PyFloat_Unpack2/4/8`, :2350-2463). -/
def slowItem (tc : TC) (x : Int) : PyVal :=
  match tc with
  | .e => .float (halfToDouble x.toNat)
  | .f => .float (unpack4 x.toNat)
  | .d => .float x.toNat
  | .Zf => .complex (unpack4 (x.toNat % 4294967296)) (unpack4 (x.toNat / 4294967296))
  | .Zd => .complex (x.toNat % 18446744073709551616) (x.toNat / 18446744073709551616)
  | _ => .int x

/-- The machine format code of every typecode but `u` and `w` describes its bytes: for every
array `a` of such a typecode (items in range) and every typecode `t` with a different code
(so the reconstructor takes the slow path, as an unpickling machine with another layout does),
`_array_reconstructor(type(a), t, typecode_to_mformat_code(a.typecode), a.tobytes())` decodes each
item's bytes as the value `a` stores: the integer for an integer typecode (rebuilt with the
widest typecode of that size and signedness), the binary16, binary32 or binary64 value for `e`,
`f`, `d`, and the two binary32 or binary64 parts for `Zf`, `Zd`. A code naming another row
(an integer row for `f`, `d` or `Zf`, a float16 row for `H`, ...) decodes to other values or
fails the length check. (`u` and `w`: bugs/sequences-array-mformat-utf-sizes.yaml.) -/
def ArrayMformatSlow : Prop :=
  ∀ (a : Arr) (t : TC), a.tc ≠ .u → a.tc ≠ .w → a.WF → mformatOf t ≠ mformatOf a.tc →
    reconstruct a.tname t.code (mformatOf a.tc) (arrToBytes a) =
      makeArray a.tname (if a.tc.isInteger then (intCanon a.tc).code else t.code)
        (.list (a.items.map (slowItem a.tc)))

set_option maxHeartbeats 2000000 in
theorem arrayMformatSlow_proven : ArrayMformatSlow := by
  intro a t hu hw hwf hne
  have hc := chunks_flatMap a.tc a.items (arrToBytes a).length (by
    rw [length_arrToBytes]
    have : 1 ≤ a.tc.itemsize.toNat := by rcases itemsize_cases a.tc with h | h | h | h | h <;> rw [h] <;> decide
    exact Nat.le_mul_of_pos_right _ this)
  have hlen := length_arrToBytes a
  unfold reconstruct
  simp only [find_code]
  rw [iteF (mformat_range a.tc), iteF (Ne.symm hne)]
  rcases a with ⟨tc, items, al, hb, ex, tn⟩
  have hcg : ∀ {s1 s2 : String} {i1 i2 : Init}, s1 = s2 → i1 = i2 → makeArray tn s1 i1 = makeArray tn s2 i2 := by
    intro _ _ _ _ h1 h2; rw [h1, h2]
  simp only [Arr.WF] at hwf
  simp only at hc hlen hu hw ⊢
  unfold arrToBytes at hc hlen ⊢
  simp only at hc hlen ⊢
  cases tc <;> first | exact absurd rfl hu | exact absurd rfl hw | skip
  all_goals simp only [mformatOf, mformatDescr, TC.itemsize, TC.isInteger, intCanon, TC.isSigned,
    Int.reduceToNat] at hc hlen ⊢
  all_goals rw [iteF (by rw [hlen]; simp [Nat.mul_mod_left, Nat.mod_one])]
  all_goals simp only [Int.reduceEq, or_self, or_false, false_or, reduceIte, Bool.false_eq_true, true_and,
    false_and, ite_false, ite_true]
  all_goals rw [hc]
  all_goals refine hcg ?_ ?_
  all_goals try (show @Eq String _ _; first | rfl | decide)
  all_goals refine congrArg Init.list ?_
  all_goals rw [List.map_map]
  all_goals apply List.map_congr_left
  all_goals intro x hx
  all_goals have hr := hwf x hx
  all_goals simp only [TC.lo, TC.hi] at hr
  case e | f | d =>
    first
      | (have h := itemOfBytes_itemBytes .e x hr; simp only [itemOfBytes] at h)
      | (have h := itemOfBytes_itemBytes .f x hr; simp only [itemOfBytes] at h)
      | (have h := itemOfBytes_itemBytes .d x hr; simp only [itemOfBytes] at h)
    simp only [Function.comp, slowItem]
    simp only [TC.isSigned, Bool.false_or, beq_iff_eq, reduceCtorEq, Bool.false_eq_true, ite_false, decide_false] at h
    have h' := congrArg Int.toNat h
    simp only [Int.toNat_natCast] at h'
    rw [h']
  case Zf =>
    simp only [Function.comp, slowItem, itemBytes_eq, TC.itemsize, Int.reduceToNat]
    obtain ⟨h1, h2⟩ := leValue_split ((x % 2 ^ (8 * 8)).toNat) 4 4
    try simp only [Nat.reduceAdd, Nat.reduceMul, Nat.reducePow] at h1 h2 ⊢
    rw [h1, h2]
    congr 2 <;> omega
  case Zd =>
    simp only [Function.comp, slowItem, itemBytes_eq, TC.itemsize, Int.reduceToNat]
    obtain ⟨h1, h2⟩ := leValue_split ((x % 2 ^ (8 * 16)).toNat) 8 8
    try simp only [Nat.reduceAdd, Nat.reduceMul, Nat.reducePow] at h1 h2 ⊢
    rw [h1, h2]
    congr 1 <;> omega
  all_goals simp only [Function.comp, slowItem]
  all_goals refine congrArg PyVal.int ?_
  all_goals
    have h := itemOfBytes_itemBytes _ x (hwf x hx)
    simp only [itemOfBytes, TC.isSigned, TC.itemsize, Int.reduceToNat, Bool.true_or, Bool.false_or,
      beq_iff_eq, reduceCtorEq, decide_false, Bool.false_eq_true, ite_true, ite_false, Nat.reduceMul,
      Nat.reduceSub, Nat.reducePow] at h ⊢
    generalize ((leValue (itemBytes _ x) : Nat) : Int) = u at h ⊢
    repeat' split at h
    all_goals (repeat' split) <;> omega


end PyLean.Sequences
