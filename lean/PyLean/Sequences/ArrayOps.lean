import PyLean.Sequences.ArrayBytes
import PyLean.Sequences.ArraySlice
import PyLean.Sequences.Reverse

/-!
`array.array`: concatenation, repetition, `extend`, `clear`, copies, `fromlist`, `tolist`,
`reverse`, the attributes, the buffer protocol and the iterator.
-/

namespace PyLean.Sequences

open PyLean
open PyLean.RangeSlice (Slice)

set_option linter.unusedSectionVars false

theorem itemsize_pos (tc : TC) : 1 ≤ tc.itemsize := by cases tc <;> decide

theorem fits_ssize (a : Arr) (n : Int) (h : a.Fits n) : n ≤ ssizeMax := by
  unfold Arr.Fits at h
  have : ssizeMax / a.tc.itemsize ≤ ssizeMax := Int.ediv_le_self _ (by unfold ssizeMax; omega)
  omega

theorem fits_zero (a : Arr) : a.Fits 0 := by
  unfold Arr.Fits
  rcases itemsize_cases a.tc with h | h | h | h <;> rw [h] <;> decide

theorem resized_same (l : List Int) : resized l l.length = l := by
  rw [resized_le _ _ (by omega) (by omega), show ((l.length : Int)).toNat = l.length by omega,
    List.take_length]

/-! ### Concatenation -/

theorem arrConcat_ok (a b : Arr) (h : a.tc = b.tc) (hf : a.Fits (a.items.length + b.items.length)) :
    ∃ c, arrConcat a (.inl b) = .ok c ∧ c.items = a.items ++ b.items ∧ c.tc = a.tc ∧ c.tname = "array" := by
  have := fits_ssize a _ hf
  unfold arrConcat
  simp only [bind, Except.bind, pure, Except.pure, throwE]
  rw [iteF (show ¬ a.tc ≠ b.tc by simpa using h), iteF (by omega), newArr_ok _ _ _ hf]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem arrDoExtend_ok (a b : Arr) (h : a.tc = b.tc) (hx : a.exports = 0)
    (hf : a.Fits (a.items.length + b.items.length)) :
    ∃ c, arrDoExtendArr a b = .ok c ∧ c.items = a.items ++ b.items ∧ c.tc = a.tc ∧ c.exports = 0 ∧
      c.tname = a.tname := by
  have := fits_ssize a _ hf
  obtain ⟨a1, hr, hi, ht, he, hn⟩ := arrResize_ok a (a.items.length + b.items.length) hx (by omega) hf
  unfold arrDoExtendArr
  simp only [bind, Except.bind, pure, Except.pure, throwE]
  rw [iteF (show ¬ a.tc ≠ b.tc by simpa using h),
    iteF (show ¬ ((a.items.length : Int) > ssizeMax - b.items.length ∨
      (a.items.length : Int) + b.items.length > ssizeMax / a.tc.itemsize) by unfold Arr.Fits at hf; omega), hr]
  simp only
  by_cases hb : (b.items.length : Int) > 0
  · rw [iteT hb]
    refine ⟨_, rfl, ?_, ht, he, hn⟩
    show memcpy a1.items _ _ = _
    rw [hi, resized_grow _ _ (by omega)]
    exact memcpy_end a.items b.items
  · rw [iteF hb]
    refine ⟨a1, rfl, ?_, ht, he, hn⟩
    have hb0 : b.items = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hi, hb0]
    simp only [List.length_nil, Int.natCast_zero, Int.add_zero, List.append_nil]
    exact resized_same _

/-- `a + b`, `a += b` and `a.extend(b)` for arrays of the same typecode, for every array
`a` without exported buffers (the result fits the address space): the items of `a`
followed by those of `b`; `+` gives a new `array.array`, even for subclasses. Different
typecodes raise `TypeError` and leave `a` as it is; `+` and `+=` with a non-array
raise `TypeError`. -/
def ArrayConcat : Prop :=
  ∀ (a b : Arr), a.exports = 0 →
    (a.tc = b.tc → a.Fits (a.items.length + b.items.length) →
      (∃ c, arrConcat a (.inl b) = .ok c ∧ c.items = a.items ++ b.items ∧ c.tc = a.tc ∧ c.tname = "array") ∧
      (∃ c, arrIConcat a (.inl b) = .ok c ∧ c.items = a.items ++ b.items ∧ c.tc = a.tc ∧ c.tname = a.tname) ∧
      (arrExtend a (.inl b)).2 = none ∧ (arrExtend a (.inl b)).1.items = a.items ++ b.items) ∧
    (a.tc ≠ b.tc → (arrConcat a (.inl b)).raises "TypeError" ∧ (arrIConcat a (.inl b)).raises "TypeError" ∧
      (arrExtend a (.inl b)).1 = a) ∧
    (∀ t, (arrConcat a (.inr t)).raises "TypeError" ∧ (arrIConcat a (.inr t)).raises "TypeError")

theorem arrayConcat_proven : ArrayConcat := by
  intro a b hx
  refine ⟨fun h hf => ?_, fun h => ?_, fun t => ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩⟩
  · obtain ⟨c, h1, h2, h3, h4, h5⟩ := arrDoExtend_ok a b h hx hf
    refine ⟨arrConcat_ok a b h hf, ⟨c, h1, h2, h3, h5⟩, ?_, ?_⟩ <;> simp only [arrExtend, h1, h2]
  · have e1 : arrDoExtendArr a b = .error (.typeError "can only extend with array of same kind") := by
      simp only [arrDoExtendArr, bind, Except.bind, throwE]
      rw [iteT h]
    have e2 : arrConcat a (.inl b) = .error (.typeError "bad argument type for built-in operation") := by
      simp only [arrConcat, bind, Except.bind, throwE]
      rw [iteT h]
    refine ⟨⟨_, e2, rfl⟩, ⟨.typeError "can only extend with array of same kind", by simp only [arrIConcat, e1], rfl⟩, ?_⟩
    simp only [arrExtend, e1]

/-- What `ins1` stores of `vs`, up to the first refused item. -/
def storeAll (tc : TC) : List PyVal → List Int × Option PyExc
  | [] => ([], none)
  | v :: vs =>
    match tcSetitem tc true v with
    | .error e => ([], some e)
    | .ok x => let r := storeAll tc vs; (x :: r.1, r.2)

theorem arrIns1_end (a : Arr) (v : PyVal) (x : Int) (hx : a.exports = 0)
    (hs : tcSetitem a.tc true v = .ok x) (hn : a.Fits (a.items.length + 1)) :
    ∃ a', arrIns1 a a.items.length v = .ok a' ∧ a'.items = a.items ++ [x] ∧ a'.tc = a.tc ∧
      a'.exports = 0 ∧ a'.tname = a.tname := by
  obtain ⟨a', h1, h2, h3⟩ := arrIns1_ok a a.items.length v x hx hs hn
  refine ⟨a', h1, ?_, h3⟩
  rw [h2]
  have hb : ins1Pos a.items.length a.items.length = a.items.length := by
    unfold ins1Pos; dsimp only; split <;> (try split) <;> (try split) <;> omega
  rw [hb, show ((a.items.length : Int)).toNat = a.items.length by omega]
  unfold insAt
  simp [List.take_length, List.drop_length]

theorem arrIterItems_spec (vs : List PyVal) : ∀ a : Arr, a.exports = 0 →
    a.Fits (a.items.length + vs.length) →
    (arrIterItems a vs).1.items = a.items ++ (storeAll a.tc vs).1 ∧
      (arrIterItems a vs).2 = (storeAll a.tc vs).2 := by
  induction vs with
  | nil => intro a _ _; simp [arrIterItems, storeAll]
  | cons v vs ih =>
    intro a hx hf
    simp only [List.length_cons] at hf
    cases hs : tcSetitem a.tc true v with
    | error e =>
      simp only [arrIterItems, arrIns1_err a _ v e hs, storeAll, hs, List.append_nil, and_self]
    | ok x =>
      obtain ⟨a', h1, h2, h3, h4, _⟩ := arrIns1_end a v x hx hs (fits_shrink a _ _ (by omega) hf)
      have hf' : a'.Fits (a'.items.length + vs.length) := by
        unfold Arr.Fits at *
        rw [h3, h2]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      obtain ⟨h5, h6⟩ := ih a' h4 hf'
      simp only [arrIterItems, h1, storeAll, hs]
      rw [h5, h6, h2, h3]
      simp

/-- `a.extend(iterable)`, `array_iter_extend`, for every array without exported buffers
(all the items fit) and every iterable: items are stored one by one, so a refused item
leaves the earlier ones appended and raises its exception, and so does an iterator
that raises. A non-iterable raises `TypeError` and changes nothing. -/
def ArrayIterExtend : Prop :=
  ∀ (a : Arr) (vs : List PyVal) (e : Option PyExc), a.exports = 0 → a.Fits (a.items.length + vs.length) →
    (arrExtend a (.inr (.iter vs e))).1.items = a.items ++ (storeAll a.tc vs).1 ∧
    (arrExtend a (.inr (.iter vs e))).2 =
      (match (storeAll a.tc vs).2 with
       | some err => some err
       | none => if e = some .stopIteration then none else e) ∧
    ∀ t, arrExtend a (.inr (.notIterable t)) = (a, some (notIterableErr t))

theorem arrayIterExtend_proven : ArrayIterExtend := by
  intro a vs e hx hf
  obtain ⟨h1, h2⟩ := arrIterItems_spec vs a hx hf
  refine ⟨?_, ?_, fun t => rfl⟩
  · simp only [arrExtend, arrIterExtend]
    cases h : arrIterItems a vs with
    | mk a' err =>
      rw [h] at h1 h2
      simp only at h1 h2
      cases err with
      | some _ => exact h1
      | none =>
        simp only
        cases e with
        | none => exact h1
        | some x => cases x <;> exact h1
  · simp only [arrExtend, arrIterExtend]
    cases h : arrIterItems a vs with
    | mk a' err =>
      rw [h] at h1 h2
      simp only at h1 h2
      rw [← h2]
      cases err with
      | some _ => rfl
      | none =>
        cases e with
        | none => rfl
        | some x => cases x <;> rfl

/-! ### Repetition -/

theorem mul_fits (L n s : Int) (hL : 0 ≤ L) (hn : 0 ≤ n) (hs : 1 ≤ s) (h : L * n ≤ ssizeMax / s) :
    (L * s) * n ≤ ssizeMax ∧ L * n ≤ ssizeMax := by
  have h1 : (L * n) * s ≤ ssizeMax := (Int.le_ediv_iff_mul_le (by omega)).mp h
  have h2 : ssizeMax / s ≤ ssizeMax := Int.ediv_le_self _ (by unfold ssizeMax; omega)
  refine ⟨?_, by omega⟩
  rw [Int.mul_assoc, Int.mul_comm s n, ← Int.mul_assoc]
  exact h1

/-- `a * n` and `a *= n`, for every array without exported buffers (`len(a)` fits, as
does `len(a) * n`, a type invariant of the result) and every int `n`: the same as `list`,
including `OverflowError` outside `Py_ssize_t` and an empty result for `n <= 0`. `*` gives
a new `array.array` of the same typecode. -/
def ArrayRepeat : Prop :=
  ∀ (a : Arr) (n : Int), a.exports = 0 → a.Fits a.items.length → a.Fits (a.items.length * max n 0) →
    (arrRepeat a n).map (·.items) = listRepeat a.items n ∧
    (arrIRepeat a n).map (·.items) = listRepeat a.items n ∧
    (∀ c, arrRepeat a n = .ok c → c.tc = a.tc ∧ c.tname = "array")

theorem arrayRepeat_proven : ArrayRepeat := by
  intro a n hx hf0 hf
  by_cases hs : ssizeMin ≤ n ∧ n ≤ ssizeMax
  · have hrc : repeatCount n = .ok n := by unfold repeatCount asSsizeExc; rw [iteT hs]
    have hL0 : (0 : Int) ≤ a.items.length := by omega
    have hsz := itemsize_pos a.tc
    obtain ⟨hA, hB⟩ := mul_fits (a.items.length) (max n 0) a.tc.itemsize hL0 (by omega) hsz hf
    have hlist : ∀ (L : Int), L = a.items.length → listRepeat a.items n =
        if L = 0 ∨ n ≤ 0 then .ok [] else .ok (List.replicate n.toNat a.items).flatten := by
      intro L hL
      subst hL
      simp only [listRepeat, hrc, bind, Except.bind, pure, Except.pure, throwE]
      by_cases hc : (a.items.length : Int) = 0 ∨ n ≤ 0
      · rw [iteT hc, iteT hc]
      · rw [iteF hc, iteF hc]
        have hn : max n 0 = n := by omega
        rw [hn] at hB
        rw [iteF (show ¬ (a.items.length : Int) > ssizeMax / n from by
          have : (a.items.length : Int) ≤ ssizeMax / n :=
            Int.le_ediv_of_mul_le (by omega) hB
          omega)]
    rw [hlist _ rfl]
    have hnil : a.items = [] → (a.items.length : Int) = 0 := fun h => by simp [h]
    have hR : ∃ c, arrRepeat a n = .ok c ∧
        c.items = (if (a.items.length : Int) = 0 ∨ n ≤ 0 then [] else (List.replicate n.toNat a.items).flatten) ∧
        c.tc = a.tc ∧ c.tname = "array" := by
      simp only [arrRepeat, hrc, arrRepeatC, bind, Except.bind, pure, Except.pure, throwE]
      have hn' : (if n < 0 then 0 else n) = max n 0 := by split <;> omega
      rw [hn']
      rw [iteF (show ¬ ((a.items.length : Int) ≠ 0 ∧ max n 0 > ssizeMax / a.items.length) from by
        intro ⟨h1, h2⟩
        have : max n 0 ≤ ssizeMax / a.items.length :=
          Int.le_ediv_of_mul_le (by omega) (by rw [Int.mul_comm]; exact hB)
        omega)]
      rw [newArr_ok _ _ _ hf]
      simp only
      by_cases hz : (a.items.length : Int) * max n 0 = 0
      · rw [iteT hz]
        refine ⟨_, rfl, ?_, rfl, rfl⟩
        have hor : (a.items.length : Int) = 0 ∨ max n 0 = 0 := Int.mul_eq_zero.mp hz
        rw [iteT (by omega), hz]
        rfl
      · rw [iteF hz]
        have hor : ¬ ((a.items.length : Int) = 0 ∨ max n 0 = 0) := fun h => hz (Int.mul_eq_zero.mpr h)
        refine ⟨_, rfl, ?_, rfl, rfl⟩
        rw [iteF (by omega)]
        simp only
        rw [show (max n 0).toNat = n.toNat by omega]
    have hI : ∃ c, arrIRepeat a n = .ok c ∧
        c.items = (if (a.items.length : Int) = 0 ∨ n ≤ 0 then [] else (List.replicate n.toNat a.items).flatten) := by
      simp only [arrIRepeat, hrc, arrIRepeatC, bind, Except.bind, pure, Except.pure, throwE]
      by_cases hc : (a.items.length : Int) > 0 ∧ n ≠ 1
      · rw [iteT hc, iteF (by unfold Arr.Fits at hf0; omega)]
        have hn' : (if n < 0 then 0 else n) = max n 0 := by split <;> omega
        rw [hn']
        rw [iteF (show ¬ (max n 0 > 0 ∧ (a.items.length : Int) * a.tc.itemsize > ssizeMax / max n 0) from by
          intro ⟨h1, h2⟩
          have : (a.items.length : Int) * a.tc.itemsize ≤ ssizeMax / max n 0 :=
            Int.le_ediv_of_mul_le h1 hA
          omega)]
        have hF : a.Fits (max n 0 * a.items.length) := by rw [Int.mul_comm]; exact hf
        obtain ⟨c, h1, h2, _⟩ := arrResize_ok a (max n 0 * a.items.length) hx
          (Int.mul_nonneg (by omega) hL0) hF
        rw [h1]
        simp only
        refine ⟨_, rfl, ?_⟩
        simp only
        by_cases hc2 : n ≤ 0
        · rw [iteT (Or.inr hc2), show (max n 0).toNat = 0 by omega]
          rfl
        · rw [iteF (by omega), show (max n 0).toNat = n.toNat by omega]
      · rw [iteF hc]
        refine ⟨a, rfl, ?_⟩
        by_cases hz : (a.items.length : Int) = 0
        · rw [iteT (Or.inl hz)]
          exact List.eq_nil_of_length_eq_zero (by omega)
        · have hn1 : n = 1 := by omega
          subst hn1
          rw [iteF (by omega)]
          simp
    obtain ⟨c, h1, h2, h3, h4⟩ := hR
    obtain ⟨c', h1', h2'⟩ := hI
    refine ⟨?_, ?_, fun c2 hc2 => ?_⟩
    · rw [h1]
      simp only [Except.map, h2]
      split <;> rfl
    · rw [h1']
      simp only [Except.map, h2']
      split <;> rfl
    · rw [h1] at hc2
      have : c = c2 := by simpa using hc2
      subst this
      exact ⟨h3, h4⟩
  · have hrc : repeatCount n = .error (.overflowError "cannot fit 'int' into an index-sized integer") := by
      unfold repeatCount asSsizeExc; rw [iteF hs]
    refine ⟨?_, ?_, fun c hc => ?_⟩
    · simp only [arrRepeat, listRepeat, hrc, bind, Except.bind, Except.map]
    · simp only [arrIRepeat, listRepeat, hrc, bind, Except.bind, Except.map]
    · simp [arrRepeat, hrc, bind, Except.bind] at hc

/-! ### `clear`, copies, `array_slice` -/

/-- The lower bound `array_slice` uses. -/
def clipLo (n lo : Int) : Int := if lo < 0 then 0 else if lo > n then n else lo

/-- The upper bound `array_slice` uses, for the clipped lower bound `l`. -/
def clipHi (n l hi : Int) : Int := max l (min n (if hi < 0 then 0 else hi))

/-- `a.clear()`, `copy.copy(a)`, `copy.deepcopy(a)` and `array_slice`, for every array
(`len(a)` fits, a type invariant). `clear` empties an array with no buffer exported and
raises `BufferError` if one is exported and it has items. A copy is a new `array.array`
of the same typecode and items. `array_slice(a, lo, hi)` for any `lo`, `hi` clips them to
`0 <= lo <= hi <= len(a)` and takes those items. -/
def ArrayClearCopy : Prop :=
  ∀ (a : Arr), a.Fits a.items.length →
    (a.exports = 0 → ∃ c, arrClear a = .ok c ∧ c.items = [] ∧ c.tc = a.tc) ∧
    (a.exports > 0 → a.items ≠ [] → arrClear a = .error bufferErr) ∧
    (∃ c, arrCopy a = .ok c ∧ c.items = a.items ∧ c.tc = a.tc ∧ c.tname = "array" ∧ c.exports = 0) ∧
    (∀ lo hi : Int,
      let l := clipLo a.items.length lo
      let h := clipHi a.items.length l hi
      ∃ c, arrSlice a lo hi = .ok c ∧ c.items = (a.items.drop l.toNat).take (h - l).toNat ∧ c.tc = a.tc)

theorem arrSlice_spec (a : Arr) (hf : a.Fits a.items.length) (lo hi : Int) :
    ∃ c, arrSlice a lo hi = .ok c ∧
      c.items = (a.items.drop (clipLo a.items.length lo).toNat).take
        (clipHi a.items.length (clipLo a.items.length lo) hi - clipLo a.items.length lo).toNat ∧
      c.tc = a.tc ∧ c.tname = "array" ∧ c.exports = 0 := by
  unfold clipLo clipHi arrSlice
  simp only [bind, Except.bind, pure, Except.pure]
  generalize hl : (if lo < 0 then 0 else if lo > (a.items.length : Int) then (a.items.length : Int) else lo) = l
  have hl0 : 0 ≤ l ∧ l ≤ a.items.length := by rw [← hl]; split <;> (try split) <;> omega
  generalize hm : (if hi < 0 then 0 else hi) = m
  have hm0 : 0 ≤ m := by rw [← hm]; split <;> omega
  have e : (if m < l then l else if m > (a.items.length : Int) then (a.items.length : Int) else m)
      = max l (min (a.items.length : Int) m) := by
    split <;> (try split) <;> omega
  rw [e]
  rw [newArr_ok _ _ _ (by unfold Arr.Fits at hf; omega)]
  simp only
  by_cases hg : max l (min (a.items.length : Int) m) > l
  · rw [iteT hg]
    exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
  · rw [iteF hg]
    refine ⟨_, rfl, ?_, rfl, rfl, rfl⟩
    rw [show (max l (min (a.items.length : Int) m) - l).toNat = 0 by omega]
    simp

theorem arrayClearCopy_proven : ArrayClearCopy := by
  intro a hf
  refine ⟨fun hx => ?_, fun hx hne => ?_, ?_, fun lo hi => ?_⟩
  · obtain ⟨c, h1, h2, h3, _⟩ := arrResize_ok a 0 hx (by omega) (fits_zero a)
    refine ⟨c, h1, ?_, h3⟩
    rw [h2, resized_le _ _ (by omega) (by omega)]
    simp
  · have : (a.items.length : Int) ≠ 0 := fun h => hne (List.eq_nil_of_length_eq_zero (by omega))
    unfold arrClear arrResize
    rw [iteT ⟨hx, by omega⟩]
  · obtain ⟨c, h1, h2, h3, h4, h5⟩ := arrSlice_spec a hf 0 a.items.length
    refine ⟨c, h1, ?_, h3, h4, h5⟩
    rw [h2]
    have e1 : clipLo a.items.length 0 = 0 := by
      unfold clipLo; split <;> (try split) <;> omega
    rw [e1]
    simp only [Int.toNat_zero, List.drop_zero]
    apply List.take_of_length_le
    unfold clipHi
    split <;> omega
  · obtain ⟨c, h1, h2, h3, _⟩ := arrSlice_spec a hf lo hi
    exact ⟨c, h1, h2, h3⟩

/-! ### `fromlist`, `tolist` -/

theorem mapM_cons_ok (tc : TC) (v : PyVal) (vs : List PyVal) (xs : List Int)
    (h : (v :: vs).mapM (tcSetitem tc true) = .ok xs) :
    ∃ x r, tcSetitem tc true v = .ok x ∧ vs.mapM (tcSetitem tc true) = .ok r ∧ xs = x :: r := by
  rw [List.mapM_cons] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases h1 : tcSetitem tc true v with
  | error e => simp [h1] at h
  | ok x =>
    rw [h1] at h
    cases h2 : vs.mapM (tcSetitem tc true) with
    | error e => simp [h2] at h
    | ok r =>
      rw [h2] at h
      have : x :: r = xs := by simpa using h
      exact ⟨x, r, rfl, rfl, this.symm⟩

theorem fromListLoop_ok (tc : TC) (vs : List PyVal) : ∀ (xs : List Int) (pos : Nat) (items : List Int),
    vs.mapM (tcSetitem tc true) = .ok xs → pos + vs.length ≤ items.length →
    fromListLoop tc vs pos items = .ok (items.take pos ++ xs ++ items.drop (pos + vs.length)) := by
  induction vs with
  | nil =>
    intro xs pos items h hl
    have : xs = [] := by simpa [pure, Except.pure] using h.symm
    subst this
    simp only [fromListLoop, List.append_nil, Nat.add_zero, List.length_nil, List.take_append_drop]
  | cons v vs ih =>
    intro xs pos items h hl
    obtain ⟨x, r, h1, h2, rfl⟩ := mapM_cons_ok tc v vs xs h
    simp only [List.length_cons] at hl
    simp only [fromListLoop, h1]
    rw [show ((pos : Int) + 1) = ((pos + 1 : Nat) : Int) by omega,
      show ((pos : Int)).toNat = pos by omega,
      ih r (pos + 1) _ h2 (by simp; omega)]
    have e1 : (items.set pos x).take (pos + 1) = items.take pos ++ [x] := by list_ext
    have e2 : (items.set pos x).drop (pos + 1 + vs.length) = items.drop (pos + (vs.length + 1)) := by
      rw [show pos + (vs.length + 1) = pos + 1 + vs.length by omega]
      list_ext
    rw [e1, e2]
    simp only [List.length_cons, List.append_assoc, List.cons_append, List.nil_append]

theorem fromListLoop_err (tc : TC) (vs : List PyVal) : ∀ (e : PyExc) (pos : Int) (items : List Int),
    vs.mapM (tcSetitem tc true) = .error e → fromListLoop tc vs pos items = .error e := by
  induction vs with
  | nil => intro e pos items h; simp [pure, Except.pure] at h
  | cons v vs ih =>
    intro e pos items h
    rw [List.mapM_cons] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    simp only [fromListLoop]
    cases h1 : tcSetitem tc true v with
    | error e' =>
      rw [h1] at h
      simpa using h
    | ok x =>
      rw [h1] at h
      cases h2 : vs.mapM (tcSetitem tc true) with
      | error e' =>
        rw [h2] at h
        have : e' = e := by simpa using h
        subst this
        exact ih _ _ _ h2
      | ok r =>
        rw [h2] at h
        simp at h

/-- `a.fromlist(l)`, for every array without exported buffers (the items fit): all or
nothing. If every item of `l` is storable they are appended, otherwise the first refused
item's exception is raised and `a` keeps its items. An argument that is not a list raises
`TypeError`. `a.tolist()` on an integer typecode is the items. -/
def ArrayFromList : Prop :=
  ∀ (a : Arr) (vs : List PyVal), a.exports = 0 → a.Fits (a.items.length + vs.length) →
    (∀ xs, vs.mapM (tcSetitem a.tc true) = .ok xs →
      (arrFromList a (.inl vs)).1 = .ok () ∧ (arrFromList a (.inl vs)).2.items = a.items ++ xs) ∧
    (∀ e, vs.mapM (tcSetitem a.tc true) = .error e →
      (arrFromList a (.inl vs)).1 = .error e ∧ (arrFromList a (.inl vs)).2.items = a.items) ∧
    (∀ t, arrFromList a (.inr t) = (.error (.typeError "arg must be list"), a)) ∧
    (a.tc.isInteger = true → arrToList a = .ok (a.items.map .int))

theorem mapM_get_int (tc : TC) (hi : tc.isInteger = true) (l : List Int) :
    l.mapM (tcGetitem tc) = .ok (l.map .int) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, tcGetitem_int tc hi x]
    simp only [bind, Except.bind, ih, pure, Except.pure, List.map_cons]

theorem arrayFromList_proven : ArrayFromList := by
  intro a vs hx hf
  refine ⟨fun xs h => ?_, fun e h => ?_, fun t => rfl, fun hi => mapM_get_int _ hi _⟩
  · by_cases hn : (vs.length : Int) > 0
    · obtain ⟨a', hr, hi, ht, _⟩ := arrResize_ok a (a.items.length + vs.length) hx (by omega) hf
      have hres : a'.items = a.items ++ List.replicate vs.length 0 := by
        rw [hi]; exact resized_grow _ _ (by omega)
      have hlen : a'.items.length = a.items.length + vs.length := by rw [hres]; simp
      have hl := fromListLoop_ok a.tc vs xs a.items.length a'.items h (by omega)
      have hb : a'.items.take a.items.length = a.items := by
        rw [hres, List.take_left']
        rfl
      have hd : a'.items.drop (a.items.length + vs.length) = [] := List.drop_eq_nil_of_le (by omega)
      rw [hb, hd, List.append_nil] at hl
      simp only [arrFromList, hn, ite_true, hr, hl]
      exact ⟨by trivial, by trivial⟩
    · have hv : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hv
      have : xs = [] := by simpa [pure, Except.pure] using h.symm
      subst this
      simp [arrFromList]
  · have hn : (vs.length : Int) > 0 := by
      cases vs with
      | nil => simp [pure, Except.pure] at h
      | cons _ _ => simp
    obtain ⟨a', hr, hi, ht, he, _⟩ := arrResize_ok a (a.items.length + vs.length) hx (by omega) hf
    have hres : a'.items = a.items ++ List.replicate vs.length 0 := by
      rw [hi]; exact resized_grow _ _ (by omega)
    have hlen : (a'.items.length : Int) = a.items.length + vs.length := by rw [hres]; simp
    obtain ⟨a'', hr2, hi2, _⟩ := arrResize_ok a' a.items.length he (by omega)
      (by unfold Arr.Fits at *; rw [ht]; omega)
    have hl := fromListLoop_err a.tc vs e (a.items.length : Int) a'.items h
    simp only [arrFromList, hn, ite_true, hr, hl, hr2]
    refine ⟨trivial, ?_⟩
    rw [hi2, resized_le _ _ (by omega) (by omega), hres, show ((a.items.length : Int)).toNat = a.items.length by omega,
      List.take_left']
    rfl

/-! ### `reverse` -/

theorem arrReverseLoop_spec (l : List Int) (fuel k : Nat) (hk : k ≤ l.length / 2)
    (hf : l.length / 2 ≤ k + fuel) :
    arrReverseLoop fuel (swapped k l) k ((l.length : Int) - 1 - k) = l.reverse := by
  induction fuel generalizing k with
  | zero =>
    have : k = l.length / 2 := by omega
    rw [this]
    exact swapped_half l
  | succ fuel ih =>
    unfold arrReverseLoop
    by_cases h : (k : Int) < (l.length : Int) - 1 - k
    · rw [iteT h]
      dsimp only
      have e1 : ((l.length : Int) - 1 - k) = ((l.length - 1 - k : Nat) : Int) := by omega
      have hih := ih (k + 1) (by omega) (by omega)
      have e2 : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
      have e3 : (l.length : Int) - 1 - ((k + 1 : Nat) : Int) = ((l.length - 1 - k : Nat) : Int) - 1 := by omega
      rw [e3, e2, ← swapped_step l k (by omega)] at hih
      rw [e1, show ((k : Int)).toNat = k by omega, show ((l.length - 1 - k : Nat) : Int).toNat = l.length - 1 - k by omega]
      exact hih
    · rw [iteF h]
      have : k = l.length / 2 := by omega
      rw [this]
      exact swapped_half l

/-- `a.reverse()`, for every array: the items reversed in place, nothing else changes.
No resize happens, so an exported buffer does not matter. -/
def ArrayReverse : Prop :=
  ∀ a : Arr, arrReverse a = { a with items := a.items.reverse }

theorem arrayReverse_proven : ArrayReverse := by
  intro a
  unfold arrReverse
  dsimp only
  by_cases h : (a.items.length : Int) > 1
  · rw [iteT h]
    have := arrReverseLoop_spec a.items a.items.length 0 (by omega) (by omega)
    rw [swapped_zero] at this
    simp only [Int.natCast_zero, Int.sub_zero] at this
    rw [this]
  · rw [iteF h]
    obtain ⟨tc, items, al, hb, ex, tn⟩ := a
    simp only at h ⊢
    match items, h with
    | [], _ => rfl
    | [_], _ => rfl
    | _ :: _ :: _, h => simp at h; omega

/-! ### Attributes -/

/-- The allocation invariant of `array_resize`: `0 <= size <= allocated`, and a NULL
`ob_item` only for an empty array. -/
def Arr.Alloc (a : Arr) : Prop :=
  (a.items.length : Int) ≤ a.allocated ∧ (a.hasBuf = false → a.items = [])

theorem arrResize_alloc (a : Arr) (n : Int) (a' : Arr) (hn : 0 ≤ n) (h : a.Alloc)
    (hr : arrResize a n = .ok a') : a'.Alloc ∧ (a'.items.length : Int) = n := by
  unfold arrResize at hr
  dsimp only at hr
  split at hr
  · simp at hr
  · split at hr
    · rename_i hc
      have : a' = { a with items := resized a.items n } := by simpa using hr.symm
      subst this
      have hl := length_resized a.items n hn
      refine ⟨⟨?_, fun hb => ?_⟩, hl⟩
      · simp only; omega
      · simp only at hb; rw [hc.2.2] at hb; simp at hb
    · split at hr
      · rename_i hz
        have : a' = { a with items := [], hasBuf := false, allocated := 0 } := by simpa using hr.symm
        subst this
        exact ⟨⟨by simp, fun _ => rfl⟩, by simp; omega⟩
      · rename_i hz
        generalize hna : n / 16 + (if (a.items.length : Int) < 8 then (3 : Int) else 7) + n = na at hr
        split at hr
        · have : a' = { a with items := resized a.items n, hasBuf := true, allocated := na } := by
            simpa using hr.symm
          subst this
          have hl := length_resized a.items n hn
          refine ⟨⟨?_, fun hb => ?_⟩, hl⟩
          · simp only; rw [hl, ← hna]; split <;> omega
          · simp at hb
        · simp at hr

theorem newArr_alloc (t : String) (tc : TC) (n : Int) (a : Arr) (hn : 0 ≤ n)
    (h : newArr t tc n = .ok a) : a.Alloc := by
  unfold newArr at h
  split at h
  · simp at h
  · have : a = ⟨tc, List.replicate n.toNat 0, n, decide (n > 0), 0, t⟩ := by simpa using h.symm
    subst this
    refine ⟨by simp; omega, fun hb => ?_⟩
    have : ¬ n > 0 := by simpa using hb
    rw [show n.toNat = 0 by omega]
    rfl

/-- `array_resize`, `newarrayobject`: both keep `Alloc` for every size, and `resize` gives the
requested length. So `__sizeof__` covers at least `len(a) * itemsize` bytes,
`buffer_info()` has a NULL address only for an empty array (and its length is `len(a)`),
`typecode` names the descriptor, and `tobytes` has `len(a) * itemsize` bytes. -/
def ArrayAttrs : Prop :=
  (∀ (a a' : Arr) (n : Int), 0 ≤ n → a.Alloc → arrResize a n = .ok a' →
    a'.Alloc ∧ (a'.items.length : Int) = n) ∧
  (∀ (t : String) (tc : TC) (n : Int) (a : Arr), 0 ≤ n → newArr t tc n = .ok a →
    a.Alloc ∧ a.tc = tc ∧ a.items = List.replicate n.toNat 0 ∧ a.exports = 0) ∧
  (∀ (a : Arr) (b : Int), a.Alloc →
    b + arrLength a * a.tc.itemsize ≤ arrSizeof a b ∧
    (arrBufferInfo a).2 = arrLength a ∧ ((arrBufferInfo a).1 = false → arrLength a = 0) ∧
    ((arrToBytes a).length : Int) = arrLength a * a.tc.itemsize ∧
    TC.all.find? (fun t => t.code == a.tc.code) = some a.tc)

theorem arrayAttrs_proven : ArrayAttrs := by
  refine ⟨fun a a' n hn h hr => arrResize_alloc a n a' hn h hr, fun t tc n a hn h => ⟨newArr_alloc t tc n a hn h, ?_⟩, fun a b h => ⟨?_, rfl, fun hb => ?_, ?_, find_code a.tc⟩⟩
  · unfold newArr at h
    split at h
    · simp at h
    · have : a = ⟨tc, List.replicate n.toNat 0, n, decide (n > 0), 0, t⟩ := by simpa using h.symm
      subst this
      exact ⟨rfl, rfl, rfl⟩
  · unfold arrSizeof arrLength
    have hp := itemsize_pos a.tc
    have := Int.mul_le_mul_of_nonneg_right h.1 (show 0 ≤ a.tc.itemsize by omega)
    omega
  · have : a.items = [] := h.2 hb
    simp [arrLength, this]
  · have hl := length_arrToBytes a
    unfold arrLength
    rw [hl, Int.natCast_mul]
    congr 1
    rcases itemsize_cases a.tc with h | h | h | h <;> rw [h] <;> rfl

/-! ### The buffer protocol -/

/-- `memoryview(a)` and its release, for every array: the view has the array's format,
itemsize, length and `len * itemsize` bytes; exporting changes nothing but the
export count, and releasing restores the array. While a buffer is exported, every size change
raises `BufferError`: `array_resize`, `append` of a storable value, `clear` of a non-empty
array and any deletion of at least one item. -/
def ArrayBuffer : Prop :=
  ∀ a : Arr,
    (arrGetBuf a).1 = (a.tc.format, a.tc.itemsize, (a.items.length : Int), (a.items.length : Int) * a.tc.itemsize) ∧
    (arrGetBuf a).2.items = a.items ∧ (arrGetBuf a).2.exports = a.exports + 1 ∧
    arrRelBuf (arrGetBuf a).2 = a ∧
    (a.exports > 0 →
      (∀ n : Int, n ≠ a.items.length → arrResize a n = .error bufferErr) ∧
      (∀ v x, tcSetitem a.tc true v = .ok x → arrAppend a v = .error bufferErr) ∧
      (a.items ≠ [] → arrClear a = .error bufferErr) ∧
      (∀ lo hi : Int, 0 ≤ lo → lo < hi → hi ≤ a.items.length → arrDelSlice a lo hi = .error bufferErr))

theorem arrayBuffer_proven : ArrayBuffer := by
  intro a
  refine ⟨rfl, rfl, rfl, ?_, fun hx => ?_⟩
  · obtain ⟨tc, items, al, hb, ex, tn⟩ := a
    simp [arrRelBuf, arrGetBuf]
  · have hr : ∀ n : Int, n ≠ a.items.length → arrResize a n = .error bufferErr := by
      intro n hn
      unfold arrResize
      dsimp only
      rw [iteT ⟨by omega, hn⟩]
    refine ⟨hr, fun v x hs => ?_, fun hne => ?_, fun lo hi h0 h1 h2 => ?_⟩
    · simp only [arrAppend, arrIns1, hs, bind, Except.bind]
      rw [hr _ (by omega)]
    · exact hr _ (fun h => hne (List.eq_nil_of_length_eq_zero (by omega)))
    · unfold arrDelSlice
      simp only [bind, Except.bind, pure, Except.pure, throwE]
      have e1 : (if lo < 0 then 0 else if lo > (a.items.length : Int) then (a.items.length : Int) else lo) = lo := by
        split <;> (try split) <;> omega
      have e2 : (if hi < 0 then 0 else hi) = hi := by split <;> omega
      have e3 : (if hi < lo then lo else if hi > (a.items.length : Int) then (a.items.length : Int) else hi) = hi := by
        split <;> (try split) <;> omega
      rw [e1, e2, e3, iteT ⟨by omega, hx⟩]

/-! ### The iterator -/

/-- What `next(it)` gives until `StopIteration`: values and raised exceptions. -/
def arrDrain (a : Arr) : Nat → ArrIter → List (Py PyVal)
  | 0, _ => []
  | fuel + 1, it =>
    match arrIterNext a it with
    | (.ok none, _) => []
    | (.ok (some v), it') => .ok v :: arrDrain a fuel it'
    | (.error e, it') => .error e :: arrDrain a fuel it'

theorem arrDrain_spec (a : Arr) (k i : Nat) (hk : i + k = a.items.length) :
    arrDrain a (k + 1) ⟨i, true⟩ = (a.items.drop i).map (tcGetitem a.tc) := by
  induction k generalizing i with
  | zero =>
    have : a.items.drop i = [] := List.drop_eq_nil_of_le (by omega)
    rw [this]
    simp only [arrDrain, arrIterNext, Bool.not_true, Bool.false_eq_true, ite_false]
    rw [iteF (by omega)]
    rfl
  | succ k ih =>
    have hi : i < a.items.length := by omega
    rw [List.drop_eq_getElem_cons hi]
    have hg : a.get i = tcGetitem a.tc a.items[i] := by
      unfold Arr.get
      rw [ix_getElem _ _ hi]
    have hih := ih (i + 1) (by omega)
    rw [show ((i + 1 : Nat) : Int) = (i : Int) + 1 by omega] at hih
    have hn : arrIterNext a ⟨i, true⟩ = (match tcGetitem a.tc a.items[i] with
        | .ok v => ((.ok (some v), ⟨(i : Int) + 1, true⟩) : Py (Option PyVal) × ArrIter)
        | .error e => (.error e, ⟨(i : Int) + 1, true⟩)) := by
      simp only [arrIterNext, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [iteT (by omega), hg]
      rfl
    rw [arrDrain, hn, List.map_cons]
    cases tcGetitem a.tc a.items[i] with
    | ok v =>
      simp only
      rw [hih]
    | error e =>
      simp only
      rw [hih]

/-- The iterator, for every array that does not change while it runs: `iter(a)` yields
`a[0], a[1], ...` in order (an unreadable item raises and the iteration goes on) and stops
after `len(a)` items. Once exhausted it stays exhausted, whatever happens to the array
later. `__setstate__` clips to `0 <= i <= len(a)` and a state from `__reduce__` restores
the position; a state outside `Py_ssize_t` raises `OverflowError`, and an exhausted
iterator ignores `__setstate__`. -/
def ArrayIterator : Prop :=
  ∀ (a a' : Arr) (i : Int),
    arrDrain a (a.items.length + 1) arrIter = a.items.map (tcGetitem a.tc) ∧
    ((a.items.length : Int) ≤ i → arrIterNext a ⟨i, true⟩ = (.ok none, ⟨i, false⟩) ∧
      arrIterNext a' ⟨i, false⟩ = (.ok none, ⟨i, false⟩)) ∧
    (arrIterReduce ⟨i, true⟩ = some i ∧ arrIterReduce ⟨i, false⟩ = none) ∧
    (ssizeMin ≤ i → i ≤ ssizeMax →
      arrIterSetstate a arrIter i = .ok ⟨if i < 0 then 0 else if i > a.items.length then a.items.length else i, true⟩ ∧
      arrIterSetstate a ⟨0, false⟩ i = .ok ⟨0, false⟩) ∧
    ((i < ssizeMin ∨ i > ssizeMax) → (arrIterSetstate a arrIter i).raises "OverflowError")

theorem arrayIterator_proven : ArrayIterator := by
  intro a a' i
  refine ⟨?_, fun h => ⟨?_, rfl⟩, ⟨rfl, rfl⟩, fun h0 h1 => ⟨?_, ?_⟩, fun h => ?_⟩
  · have := arrDrain_spec a a.items.length 0 (by omega)
    simpa [arrIter] using this
  · simp only [arrIterNext, Bool.not_true, Bool.false_eq_true, ite_false]
    rw [iteF (by omega)]
  · have : asSsize i = .ok i := by unfold asSsize; rw [iteT ⟨h0, h1⟩]
    simp only [arrIterSetstate, this, bind, Except.bind, pure, Except.pure, arrIter, ite_true]
  · have : asSsize i = .ok i := by unfold asSsize; rw [iteT ⟨h0, h1⟩]
    simp only [arrIterSetstate, this, bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ite_false]
  · have : asSsize i = .error (.overflowError "Python int too large to convert to C ssize_t") := by
      unfold asSsize; rw [iteF (by omega)]
    simp only [arrIterSetstate, this, bind, Except.bind]
    exact ⟨_, rfl, rfl⟩

end PyLean.Sequences
