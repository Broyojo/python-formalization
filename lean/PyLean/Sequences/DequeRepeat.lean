import PyLean.Sequences.DequeProps

/-!
`d *= n` for deques (with `maxlen`) and lists.
-/

namespace PyLean.Sequences

open PyLean

set_option linter.unusedSectionVars false

variable {α : Type} [Inhabited α]

/-- `items` repeated `n` times. -/
def rep (n : Nat) (l : List α) : List α := (List.replicate n l).flatten

theorem rep_add (a b : Nat) (l : List α) : rep (a + b) l = rep a l ++ rep b l := by
  unfold rep; rw [← List.replicate_append_replicate, List.flatten_append]

theorem rep_succ' (n : Nat) (l : List α) : rep (n + 1) l = rep n l ++ l := by
  rw [rep_add]; simp [rep]

theorem length_rep (n : Nat) (l : List α) : (rep n l).length = n * l.length := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [rep_succ', List.length_append, ih, Nat.succ_mul]

theorem keepLast_append_long (m : Int) (X Y : List α) (hm : 0 ≤ m) (hY : m ≤ Y.length) :
    keepLast m (X ++ Y) = keepLast m Y := by
  unfold keepLast
  rw [iteF (by omega), iteF (by omega), List.drop_append, List.length_append,
    List.drop_of_length_le (by omega), List.nil_append]
  congr 1; omega

theorem keepLast_keepLast' (m : Int) (A B : List α) : keepLast m (keepLast m A ++ B) = keepLast m (A ++ B) := by
  unfold keepLast
  split
  · rfl
  · exact keepLast_keepLast _ _ _

/-- `d *= n` keeps the last `maxlen` items of `list(d) * n` (all of them for
an unbounded deque), as the documented `maxlen` eviction implies: for every
deque of any element type (type invariant `WF`) and every int `n` inside
`Py_ssize_t`, whenever
that result has at most `sys.maxsize` items (always true for a bounded
deque), `d *= n` succeeds with exactly those items. -/
def DequeIRepeat : Prop :=
  ∀ (α : Type) [Inhabited α] (d : Deque α), d.WF → ∀ (n : Int), ssizeMin ≤ n → n ≤ ssizeMax →
    (0 ≤ d.maxlen ∨ (d.items.length : Int) * n ≤ ssizeMax) →
    ∃ d', d.irepeat n = .ok d' ∧ d'.items = keepLast d.maxlen (rep n.toNat d.items)

/-- The same, restricted to deques of at most one item or to results the
size check `size > PY_SSIZE_T_MAX / n` (done before `maxlen` is applied)
lets through; the result also keeps the invariant and `maxlen`. -/
def DequeIRepeatChecked : Prop :=
  ∀ (α : Type) [Inhabited α] (d : Deque α), d.WF → ∀ (n : Int), ssizeMin ≤ n → n ≤ ssizeMax →
    (d.items.length ≤ 1 ∨ (d.items.length : Int) * n ≤ ssizeMax) →
    ∃ d', d.irepeat n = .ok d' ∧ d'.items = keepLast d.maxlen (rep n.toNat d.items) ∧ d'.WF ∧
      d'.maxlen = d.maxlen

/-- `deque([1, 2], maxlen=3)`. -/
def d12 : Deque Int := ⟨1, 2, [1, 2], 3, 2, "deque"⟩

theorem d12_make : Deque.make [1, 2] (.int 3) = .ok d12 := by decide

theorem d12_wf : d12.WF := by
  refine ⟨?_, ?_⟩
  · rw [Deque.layout_iff]; decide
  · rw [Deque.maxOk_iff]; decide

theorem dequeIRepeat_refuted : ¬ DequeIRepeat := by
  intro h
  obtain ⟨d', h1, _⟩ := h Int d12 d12_wf (2 ^ 62) (by decide) (by decide) (Or.inl (by decide))
  have : d12.irepeat (2 ^ 62) = .error memoryError := by decide
  rw [this] at h1
  exact nomatch h1

theorem foldl_extend_rep (seq : List α) (k : Nat) : ∀ (d : Deque α), d.WF →
    let d' := (List.range k).foldl (fun d _ => d.extend seq) d
    d'.WF ∧ d'.items = keepLast d.maxlen (d.items ++ rep k seq) ∧ d'.maxlen = d.maxlen := by
  induction k with
  | zero =>
    intro d h
    have hmx : d.maxlen < 0 ∨ (d.items.length : Int) ≤ d.maxlen := by
      rcases h.2 with h2 | h2
      · left; omega
      · right; rw [Deque.size_eq] at h2; exact h2.2
    refine ⟨h, ?_, rfl⟩
    simp only [rep, List.replicate_zero, List.flatten_nil, List.append_nil]
    rw [keepLast_of_le _ _ hmx]
    rfl
  | succ k ih =>
    intro d h
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨w1, i1, m1⟩ := ih d h
    obtain ⟨w2, i2, m2⟩ := Deque.extend_spec _ seq w1
    refine ⟨w2, ?_, by rw [m2, m1]⟩
    rw [i2, i1, m1, keepLast_keepLast', rep_succ', List.append_assoc]

theorem dequeIRepeatChecked_proven : DequeIRepeatChecked := by
  intro α _ d h n hn0 hn1 hsmall
  have hL := h.1
  have h' := h.1
  rw [Deque.layout_iff] at h'
  have hmx : d.maxlen < 0 ∨ (d.items.length : Int) ≤ d.maxlen := by
    rcases h.2 with h2 | h2
    · left; omega
    · right; rw [Deque.size_eq] at h2; exact h2.2
  simp only [Deque.irepeat, repeatCount, asSsizeExc, bind, Except.bind]
  rw [iteT ⟨hn0, hn1⟩]
  unfold Deque.irepeatC
  simp only [pure, Except.pure, bind, Except.bind]
  -- size 0 or n == 1
  by_cases h01 : d.size = 0 ∨ n = 1
  · rw [iteT h01]
    refine ⟨d, rfl, ?_, h, rfl⟩
    rcases h01 with h0 | h1
    · rw [Deque.size_eq] at h0
      have : d.items = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [this]; unfold keepLast rep; simp
    · subst h1
      rw [show (1 : Int).toNat = 1 by rfl, show rep 1 d.items = d.items by simp [rep], keepLast_of_le _ _ hmx]
  rw [iteF h01]
  -- n <= 0: clear
  by_cases hneg : n ≤ 0
  · rw [iteT hneg]
    refine ⟨d.clear, rfl, ?_, ?_, ?_⟩
    · unfold Deque.clear; rw [iteF (by omega)]
      rw [show n.toNat = 0 by omega]; unfold keepLast rep; simp
    · unfold Deque.clear; rw [iteF (by omega)]
      refine ⟨?_, ?_⟩
      · rw [Deque.layout_iff]; simp [CENTER]
      · rw [Deque.maxOk_iff]; simp only [List.length_nil, Int.natCast_zero]
        rcases h.2 with h2 | h2
        · left; exact h2
        · right; omega
    · unfold Deque.clear; rw [iteF (by omega)]
  rw [iteF hneg]
  rw [Deque.size_eq] at h01
  by_cases hone : (d.items.length : Int) = 1
  · -- the single-item fill
    rw [Deque.size_eq, iteT hone]
    obtain ⟨x, hx⟩ : ∃ x, d.items = [x] := by
      match hd : d.items, hone with
      | [x], _ => exact ⟨x, rfl⟩
    generalize hn' : (if d.maxlen ≥ 0 ∧ n > d.maxlen then d.maxlen else n) = n'
    have hn'b : 1 ≤ n' ∧ n' ≤ n ∧ (d.maxlen ≥ 0 → n' ≤ d.maxlen) ∧ (d.maxlen < 0 → n' = n) ∧
        (d.maxlen ≥ 0 → n' = min n d.maxlen) := by
      rw [← hn']; rw [hx] at hmx; simp only [List.length_singleton] at hmx
      split <;> refine ⟨by omega, by omega, fun _ => by omega, fun _ => by omega, fun _ => by omega⟩
    refine ⟨_, rfl, ?_, ⟨?_, ?_⟩, rfl⟩
    · simp only [hx, show ix [x] 0 = x from rfl]
      have hrep : rep n.toNat [x] = List.replicate n.toNat x := by
        unfold rep; simp [List.flatten_replicate_singleton]
      rw [hrep, show [x] ++ List.replicate (n' - 1).toNat x = List.replicate n'.toNat x by
        rw [List.singleton_append, ← List.replicate_succ]; congr 1; omega]
      unfold keepLast
      split
      · rw [hn'b.2.2.2.1 (by omega)]
      · rw [List.drop_replicate, List.length_replicate, hn'b.2.2.2.2 (by omega)]
        congr 1; omega
    · rw [Deque.layout_iff]
      simp only [List.length_append, List.length_replicate, hx, List.length_singleton]
      rw [hx] at h'; simp only [List.length_singleton] at h'
      omega
    · rw [Deque.maxOk_iff]
      simp only [List.length_append, List.length_replicate, hx, List.length_singleton]
      rcases h.2 with h2 | h2
      · left; exact h2
      · right; refine ⟨h2.1, ?_⟩; have := hn'b.2.2.1 h2.1; omega
  rw [Deque.size_eq, iteF hone]
  -- at least two items: the size check passes
  have hs2 : 2 ≤ d.items.length := by omega
  have hprod : (d.items.length : Int) * n ≤ ssizeMax := by
    rcases hsmall with hs | hs
    · omega
    · exact hs
  have hcheck : ¬ ((d.items.length : Int) > ssizeMax / n) := by
    intro hgt
    have := (Int.le_ediv_iff_mul_le (show 0 < n by omega)).mpr (show (d.items.length : Int) * n ≤ ssizeMax from hprod)
    omega
  rw [iteF hcheck]
  generalize hlen : (d.items.length : Int) = len at *
  generalize hk : (if d.maxlen ≥ 0 ∧ n * len > d.maxlen then (d.maxlen + len - 1) / len else n) = k
  -- the reduced count is between 1 and n, and still covers maxlen items
  have hkb : 1 ≤ k ∧ k ≤ n ∧ (k ≠ n → 0 ≤ d.maxlen ∧ d.maxlen ≤ len * k) := by
    rw [← hk]
    split
    · rename_i hc
      have hlpos : 0 < len := by omega
      have e := Int.emod_add_mul_ediv (d.maxlen + len - 1) len
      have e0 := Int.emod_nonneg (d.maxlen + len - 1) (show len ≠ 0 by omega)
      have e1 := Int.emod_lt_of_pos (d.maxlen + len - 1) hlpos
      generalize (d.maxlen + len - 1) / len = q at e
      generalize (d.maxlen + len - 1) % len = r at e e0 e1
      have hq1 : 1 ≤ q := by
        apply Int.not_lt.mp; intro hq
        have : len * q ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
        omega
      have hqn : q ≤ n := by
        apply Int.not_lt.mp; intro hq
        have : len * (n + 1) ≤ len * q := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
        rw [Int.mul_add, Int.mul_one, Int.mul_comm len n] at this
        omega
      exact ⟨hq1, hqn, fun _ => ⟨hc.1, by omega⟩⟩
    · exact ⟨by omega, Int.le_refl _, fun h => absurd rfl h⟩
  obtain ⟨w, i1, m1⟩ := foldl_extend_rep d.items (k - 1).toNat d h
  refine ⟨_, rfl, ?_, w, m1⟩
  rw [i1]
  have e1 : d.items ++ rep (k - 1).toNat d.items = rep k.toNat d.items := by
    rw [show k.toNat = 1 + (k - 1).toNat by omega, rep_add]; simp [rep]
  rw [e1]
  by_cases hkn : k = n
  · rw [hkn]
  · obtain ⟨hm0, hmk⟩ := hkb.2.2 hkn
    rw [show n.toNat = (n - k).toNat + k.toNat by omega, rep_add, keepLast_append_long _ _ _ hm0]
    rw [length_rep, Int.natCast_mul, hlen, show ((k.toNat : Nat) : Int) = k by omega, Int.mul_comm]
    exact hmk

/-- `l *= n` and `l * n` (note (2) of Doc/library/stdtypes.rst:1263-1275 and
the `s * n` row of the common-sequence table): for every list of ints and
every int `n`: outside `Py_ssize_t` both raise `OverflowError`; `n <= 0`
gives `[]`; otherwise the result is `l` repeated `n` times, and `MemoryError`
is raised exactly when that would exceed `sys.maxsize` items. -/
def ListRepeat : Prop :=
  ∀ (α : Type) [Inhabited α] (l : List α) (n : Int), (l.length : Int) ≤ ssizeMax →
    ((n < ssizeMin ∨ ssizeMax < n) →
      listIRepeat l n = .error (.overflowError "cannot fit 'int' into an index-sized integer") ∧
      listRepeat l n = .error (.overflowError "cannot fit 'int' into an index-sized integer")) ∧
    (ssizeMin ≤ n → n ≤ ssizeMax →
      listIRepeat l n = listRepeat l n ∧
      (n ≤ 0 → listRepeat l n = .ok []) ∧
      (0 < n → (l.length : Int) * n ≤ ssizeMax → listRepeat l n = .ok (rep n.toNat l)) ∧
      (0 < n → ssizeMax < (l.length : Int) * n → listRepeat l n = .error memoryError))

theorem listRepeat_proven : ListRepeat := by
  intro α _ l n hlen
  refine ⟨fun hn => ?_, fun hn0 hn1 => ?_⟩
  · simp only [listIRepeat, listRepeat, repeatCount, asSsizeExc, bind, Except.bind]
    rw [iteF (by omega)]; exact ⟨rfl, rfl⟩
  have hc : repeatCount n = .ok n := by unfold repeatCount asSsizeExc; rw [iteT ⟨hn0, hn1⟩]
  simp only [listIRepeat, listRepeat, hc, bind, Except.bind, pure, Except.pure]
  have hdiv : ∀ (h : 0 < n), ((l.length : Int) > ssizeMax / n ↔ ssizeMax < (l.length : Int) * n) := by
    intro h
    constructor
    · intro hg; apply Int.not_le.mp; intro hle
      have := (Int.le_ediv_iff_mul_le h).mpr hle; omega
    · intro hg; apply Int.not_le.mp; intro hle
      have := (Int.le_ediv_iff_mul_le h).mp hle; omega
  refine ⟨?_, fun h => ?_, fun h hle => ?_, fun h hgt => ?_⟩
  · by_cases h0 : (l.length : Int) = 0
    · have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; simp
    by_cases h1 : n = 1
    · subst h1
      rw [iteT (show (l.length : Int) = 0 ∨ (1 : Int) = 1 from Or.inr rfl),
        iteF (show ¬ ((l.length : Int) = 0 ∨ (1 : Int) ≤ 0) by omega),
        iteF (show ¬ ((l.length : Int) > ssizeMax / 1) by rw [Int.ediv_one]; omega)]
      simp
    rw [iteF (show ¬ ((l.length : Int) = 0 ∨ n = 1) by omega)]
    by_cases hneg : n < 1
    · rw [iteT hneg, iteT (show (l.length : Int) = 0 ∨ n ≤ 0 by omega)]
    · rw [iteF hneg, iteF (show ¬ ((l.length : Int) = 0 ∨ n ≤ 0) by omega)]
  · by_cases h0 : (l.length : Int) = 0
    · rw [iteT (Or.inl h0)]
    · rw [iteT (Or.inr h)]
  · by_cases h0 : (l.length : Int) = 0
    · have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; rw [iteT (Or.inl h0)]; simp [rep]
    rw [iteF (show ¬ ((l.length : Int) = 0 ∨ n ≤ 0) by omega),
      iteF (show ¬ ((l.length : Int) > ssizeMax / n) from fun hA => absurd ((hdiv h).mp hA) (by omega))]; rfl
  · rw [iteF (show ¬ ((l.length : Int) = 0 ∨ n ≤ 0) by
      intro hh; rcases hh with hh | hh
      · rw [hh] at hgt; simp at hgt; unfold ssizeMax at hgt; omega
      · omega),
      iteT (show ((l.length : Int) > ssizeMax / n) from (hdiv h).mpr hgt)]; rfl

/-- `d.copy()`, `d + other`: for every deque (type invariant `WF`) and every other
deque, `copy()` has the same items, `maxlen` and type, and `d + other` holds the last
`d.maxlen` items of `list(d) + list(other)` with `d`'s `maxlen` and type
(Doc/library/collections.rst:503-507, 599-600); all results keep the invariant.
`__copy__` is the same function. -/
def DequeCopyConcat : Prop :=
  ∀ (α : Type) [Inhabited α] (d : Deque α), d.WF → ∀ (other : Deque α),
    ∃ c, d.copy = .ok c ∧ c.WF ∧ c.items = d.items ∧ c.maxlen = d.maxlen ∧ c.tname = d.tname ∧
      ∃ n, d.concat (.inl other) = .ok n ∧ n.WF ∧ n.items = keepLast d.maxlen (d.items ++ other.items) ∧
        n.maxlen = d.maxlen ∧ n.tname = d.tname

/-- The same for the exact type, and for a subclass whose `maxlen` is unbounded or
below `2**31` (the `"i"` format of the subclass path of `deque_copy_impl`). -/
def DequeCopyConcatChecked : Prop :=
  ∀ (α : Type) [Inhabited α] (d : Deque α), d.WF → (d.tname = "deque" ∨ d.maxlen < 2147483648) →
    ∀ (other : Deque α),
    ∃ c, d.copy = .ok c ∧ c.WF ∧ c.items = d.items ∧ c.maxlen = d.maxlen ∧ c.tname = d.tname ∧
      ∃ n, d.concat (.inl other) = .ok n ∧ n.WF ∧ n.items = keepLast d.maxlen (d.items ++ other.items) ∧
        n.maxlen = d.maxlen ∧ n.tname = d.tname

theorem maxOk_le (d : Deque α) (h : d.WF) : d.maxlen < 0 ∨ (d.items.length : Int) ≤ d.maxlen := by
  rcases h.2 with h2 | h2
  · left; omega
  · right; rw [Deque.size_eq] at h2; exact h2.2

theorem copyExact_spec (d : Deque α) (h : d.WF) :
    d.copyExact.WF ∧ d.copyExact.items = d.items ∧ d.copyExact.maxlen = d.maxlen ∧
      d.copyExact.tname = "deque" := by
  have hmx := maxOk_le d h
  unfold Deque.copyExact
  by_cases hs : d.size > 0
  · rw [iteT hs]
    have hpos : d.maxlen = -1 ∨ 0 < d.maxlen := by
      rcases h.2 with h2 | h2
      · left; exact h2
      · right; rw [Deque.size_eq] at h2 hs; omega
    have hl : ({ { (Deque.new : Deque α) with maxlen := d.maxlen } with left := 1, right := 0 } : Deque α).Layout := by
      rw [Deque.layout_iff]; simp [Deque.new]
    obtain ⟨a, b, c⟩ := Deque.foldl_appendM d.items _ hl hpos (by simp [Deque.new]; omega)
    refine ⟨⟨a, ?_⟩, ?_, ?_, ?_⟩
    · rw [Deque.maxOk_iff, c, b]
      simp only [Deque.new, List.nil_append]
      rw [keepLast_of_le _ _ hmx]
      rcases h.2 with h2 | h2
      · left; exact h2
      · right; rw [Deque.size_eq] at h2; exact h2
    · rw [b]; simp only [Deque.new, List.nil_append]; exact keepLast_of_le _ _ hmx
    · rw [c]
    · rw [foldl_appendM_tname]; rfl
  · rw [iteF hs]
    have : d.items = [] := List.eq_nil_of_length_eq_zero (by rw [Deque.size_eq] at hs; omega)
    refine ⟨new_wf "deque" d.maxlen (by rcases h.2 with h2 | h2 <;> omega), by simp [Deque.new, this], rfl, rfl⟩

theorem wrap32_of_lt (m : Int) (h0 : 0 ≤ m) (h1 : m < 2147483648) : wrap32 m = m := by
  unfold wrap32; rw [iteF (by omega)]; omega

theorem copy_spec (d : Deque α) (h : d.WF) (hc : d.tname = "deque" ∨ d.maxlen < 2147483648) :
    ∃ c, d.copy = .ok c ∧ c.WF ∧ c.items = d.items ∧ c.maxlen = d.maxlen ∧ c.tname = d.tname := by
  have hmx := maxOk_le d h
  unfold Deque.copy
  by_cases ht : d.tname = "deque"
  · rw [iteT ht]
    obtain ⟨a, b, c, e⟩ := copyExact_spec d h
    exact ⟨_, rfl, a, b, c, by rw [e, ht]⟩
  rw [iteF ht]
  have hlt := hc.resolve_left ht
  by_cases hneg : d.maxlen < 0
  · rw [iteT hneg]
    have hm : d.maxlen = -1 := by rcases h.2 with h2 | h2 <;> omega
    rw [makeOf_absent]
    obtain ⟨a, b, c⟩ := Deque.extend_spec { Deque.new d.tname with maxlen := -1 } d.items (new_wf _ (-1) (Or.inl rfl))
    refine ⟨_, rfl, a, ?_, by rw [c, hm], extend_tname _ _⟩
    rw [b]; simp [Deque.new, keepLast]
  · rw [iteF hneg, wrap32_of_lt _ (by omega) hlt,
      makeOf_int _ _ _ (by omega) (by unfold ssizeMax; omega)]
    obtain ⟨a, b, c⟩ := Deque.extend_spec { Deque.new d.tname with maxlen := d.maxlen } d.items
      (new_wf _ _ (Or.inr (by omega)))
    refine ⟨_, rfl, a, ?_, c, extend_tname _ _⟩
    rw [b]; simp only [Deque.new, List.nil_append]; exact keepLast_of_le _ _ hmx

/-- A subclass of `deque` with `maxlen=2**32`. -/
def dBig : Deque Int := ⟨1, 1, [1], 4294967296, 1, "D"⟩

theorem dequeCopyConcat_refuted : ¬ DequeCopyConcat := by
  intro h
  have hw : dBig.WF := by
    refine ⟨?_, ?_⟩
    · rw [Deque.layout_iff]; decide
    · rw [Deque.maxOk_iff]; decide
  obtain ⟨c, h1, _, h3, _⟩ := h Int dBig hw dBig
  have e : dBig.copy = .ok ⟨32, 31, [], 0, 0, "D"⟩ := by decide
  rw [e] at h1
  cases h1
  exact nomatch h3

theorem dequeCopyConcatChecked_proven : DequeCopyConcatChecked := by
  intro α _ d h hc other
  obtain ⟨c, h1, w, i, m, t⟩ := copy_spec d h hc
  obtain ⟨w2, i2, m2⟩ := Deque.extend_spec c other.items w
  refine ⟨c, h1, w, i, m, t, c.extend other.items, ?_, w2, ?_, ?_, ?_⟩
  · unfold Deque.concat; rw [h1]
  · rw [i2, m, i]
  · rw [m2, m]
  · rw [extend_tname, t]

end PyLean.Sequences
