import PyLean.BytesObj.Bytes.BasicProps

/-!
Properties of the `bytes` methods, second part.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## Repeat -/

theorem take_flat (src : Seq) (m j : Nat) (hj : j ≤ m) :
    ((List.replicate m src).flatten).take (j * src.length) = (List.replicate j src).flatten := by
  induction j generalizing m with
  | zero => simp
  | succ j ih =>
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [List.replicate_succ, List.flatten_cons]
    have e : (j + 1) * src.length = src.length + j * src.length := by
      rw [Nat.add_mul]; omega
    rw [e, List.take_length_add_append]
    rw [ih m' (by omega)]

theorem repl_flat_length (src : Seq) (m : Nat) :
    ((List.replicate m src).flatten).length = m * src.length := by
  simp

theorem flat_add (src : Seq) (a b : Nat) :
    (List.replicate a src).flatten ++ (List.replicate b src).flatten =
      (List.replicate (a + b) src).flatten := by
  induction a with
  | zero => simp
  | succ a ih =>
    have e : a + 1 + b = (a + b) + 1 := by omega
    rw [e, List.replicate_succ, List.replicate_succ, List.flatten_cons, List.flatten_cons,
      List.append_assoc, ih]

/-- The doubling loop keeps a whole number of copies. -/
theorem repeatLoop_spec (src : Seq) (hne : src ≠ []) (k : Nat) (fuel m : Nat) (hm : 1 ≤ m) (hmk : m ≤ k)
    (hf : k - m ≤ fuel) :
    repeatLoop (k * src.length) fuel (List.replicate m src).flatten = (List.replicate k src).flatten := by
  have hL : 0 < src.length := List.length_pos_iff.mpr hne
  induction fuel generalizing m with
  | zero =>
    have : m = k := by omega
    subst this
    rfl
  | succ f ih =>
    simp only [repeatLoop, repl_flat_length]
    by_cases hlt : m * src.length < k * src.length
    · have hmk2 : m < k := Nat.lt_of_mul_lt_mul_right hlt
      rw [if_pos hlt]
      have hsub : k * src.length - m * src.length = (k - m) * src.length := by
        rw [Nat.sub_mul]
      rw [hsub]
      by_cases hle : m ≤ k - m
      · have hmin : min (m * src.length) ((k - m) * src.length) = m * src.length :=
          Nat.min_eq_left (Nat.mul_le_mul_right _ hle)
        rw [hmin, take_flat src m m (Nat.le_refl _), flat_add]
        exact ih (m + m) (by omega) (by omega) (by omega)
      · have hmin : min (m * src.length) ((k - m) * src.length) = (k - m) * src.length :=
          Nat.min_eq_right (Nat.mul_le_mul_right _ (by omega))
        rw [hmin, take_flat src m (k - m) (by omega), flat_add]
        have e : m + (k - m) = k := by omega
        rw [e]
        exact ih k (by omega) (by omega) (by omega)
    · have : m = k := by
        have := Nat.mul_le_mul_right src.length hmk
        have h2 : m * src.length = k * src.length := by omega
        exact Nat.eq_of_mul_eq_mul_right hL h2
      subst this
      rw [if_neg hlt]

/-- `_PyBytes_Repeat`, the doubling copy (or `memset` for one byte), produces `n` copies of
the source for every source and every `n ≥ 1`. -/
def RepeatFill : Prop :=
  ∀ (src : Seq) (n : Nat), src ≠ [] → 1 ≤ n →
    bytesRepeatFill (n * src.length) src = (List.replicate n src).flatten

theorem repeatFill_proven : RepeatFill := by
  intro src n hne hn
  have hL : 0 < src.length := List.length_pos_iff.mpr hne
  have hz : n * src.length ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  unfold bytesRepeatFill
  rw [if_neg hz]
  cases hs : src with
  | nil => exact absurd hs hne
  | cons c cs =>
    cases cs with
    | nil =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one]
      apply List.ext_getElem
      · simp [List.length_flatten]
      · intro i h1 h2
        have : ∀ x ∈ (List.replicate n [c]).flatten, x = c := by
          intro x hx
          simp at hx
          exact hx.2
        simp only [List.getElem_replicate]
        exact (this _ (List.getElem_mem h2)).symm
    | cons d ds =>
      have := repeatLoop_spec (c :: d :: ds) (by simp) n (n * (c :: d :: ds).length) 1 (by omega) hn
        (by
          have : n ≤ n * (c :: d :: ds).length := Nat.le_mul_of_pos_right _ (by simp)
          omega)
      simpa using this

/-- `b * n`: `n ≤ 0` is empty, `n = 1` is `b`, and otherwise `n` copies, except that a
result longer than `sys.maxsize` raises `OverflowError` (only for `len(b) > maxsize // n`)
and an impossible allocation `MemoryError`. -/
def BytesRepeatSpec : Prop :=
  ∀ (s : Seq) (n : Int), (s.length : Int) ≤ ssizeMax →
    (n ≤ 0 → s ≠ [] → bytesRepeat s n = .ok []) ∧
    (n = 1 → bytesRepeat s n = .ok s) ∧
    (n > 1 → (s.length : Int) > Int.tdiv ssizeMax n →
      bytesRepeat s n = .error (.overflowError "repeated bytes are too long")) ∧
    (n > 1 → s ≠ [] → (s.length : Int) ≤ Int.tdiv ssizeMax n →
      ¬ mallocFails (bytesObjectSize + (s.length : Int) * n) →
      bytesRepeat s n = .ok (List.replicate n.toNat s).flatten)

theorem bytesRepeatSpec_proven : BytesRepeatSpec := by
  intro s n hmax
  have hL : ∀ (_ : s ≠ []), 0 < s.length := fun h => List.length_pos_iff.mpr h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h hne
    have := hL hne
    have h1 : n < 0 ∨ n = 0 := by omega
    have hs : (s.length : Int) ≠ 0 := by omega
    have h3 : ¬ ((0 : Int) = s.length) := by omega
    rcases h1 with h1 | rfl
    · simp [bytesRepeat, h1, h3, bytesObjectSize, mallocFails, bytesRepeatFill]
    · simp [bytesRepeat, h3, bytesObjectSize, mallocFails, bytesRepeatFill]
  · intro h
    subst h
    simp [bytesRepeat, hmax, Int.tdiv_one]
  · intro h1 h2
    have h3 : ¬ (n < 0) := by omega
    simp [bytesRepeat, h3, show 0 < n by omega, h2]
  · intro h1 hne h2 h3
    have hp := hL hne
    have hn0 : ¬ (n < 0) := by omega
    have hover : ¬ (n > 0 ∧ (s.length : Int) > Int.tdiv ssizeMax n) := by omega
    have hsize : ¬ ((s.length : Int) * n = s.length) := by
      intro e
      have : (s.length : Int) * n > (s.length : Int) * 1 := Int.mul_lt_mul_of_pos_left (by omega) (by omega)
      omega
    obtain ⟨k, rfl⟩ : ∃ k : Nat, n = k := ⟨n.toNat, by omega⟩
    have hk : (((s.length : Int) * (k : Int)).toNat) = k * s.length := by
      rw [← Int.natCast_mul, Int.toNat_natCast, Nat.mul_comm]
    have hfill := repeatFill_proven s k hne (by omega)
    unfold bytesRepeat
    rw [if_neg hn0, if_neg hover, if_neg hsize]
    simp only [Bool.not_eq_true] at h3
    simp [h3, hk, hfill]

/-! ## Concatenation -/

/-- `a + b` for bytes-like operands is the concatenation, with a `TypeError` naming both
types otherwise, and the two branches of `PyBytes_Concat` (resize in place when the
reference is unique, `bytes_concat` otherwise) give the same result for every operand. -/
def ConcatSpec : Prop :=
  (∀ (a b : Seq), (a.length : Int) + b.length + 33 < 2 ^ 47 →
    bytesConcat (.bytes a) (.bytes b) = .ok (a ++ b)) ∧
  (∀ (a : Seq) (o : Obj), o.buffer? = none →
    bytesConcat (.bytes a) o =
      .error (.typeError s!"can't concat {o.typeName} to {(Obj.bytes a).typeName}")) ∧
  (∀ (v : Seq) (w : Obj), (v.length : Int) + (Obj.buffer? w |>.getD []).length + 33 < 2 ^ 47 →
    pyBytesConcat (some v) (some w) true = pyBytesConcat (some v) (some w) false)

theorem size_cast_lt (n : Int) (h : n + 33 < 2 ^ 47) (h0 : 0 ≤ n) : ¬ (n > ssizeMax - 33) := by
  rw [ssizeMax_val]
  omega

theorem from_string_ok (s : Seq) (hs : (s.length : Int) + 33 < 2 ^ 47) :
    bytesFromStringAndSize (some s) s.length = .ok s := by
  unfold bytesFromStringAndSize
  have h0 : ¬ ((s.length : Int) < 0) := by omega
  rw [if_neg h0]
  simp only
  by_cases h1 : (s.length : Int) = 1
  · simp only [h1, if_true]
    have : s.length = 1 := by omega
    simp [← this]
  · simp only [h1, if_false]
    by_cases h2 : (s.length : Int) = 0
    · have : s = [] := List.length_eq_zero_iff.mp (by omega)
      simp [this]
    · simp only [h2, if_false]
      simp [bytesFromSize_ok s.length hs, bind, Except.bind, pure, Except.pure]

theorem bytesResizeCheck_ok (old new : Nat) (hs : (new : Int) + 33 < 2 ^ 47) :
    bytesResizeCheck old new = .ok () := by
  unfold bytesResizeCheck
  rw [if_neg (by omega)]
  by_cases h1 : (old : Int) = new
  · rw [if_pos h1]
  rw [if_neg h1]
  by_cases h2 : (old : Int) = 0
  · rw [if_pos h2]
    exact bytesSizeCheck_ok _ (by omega) hs
  rw [if_neg h2]
  by_cases h3 : (new : Int) = 0
  · rw [if_pos h3]
  rw [if_neg h3]
  exact bytesSizeCheck_ok _ (by omega) hs

theorem bytesResize_grow (v : Seq) (n : Nat) (hn : v.length ≤ n) (hs : (n : Int) + 33 < 2 ^ 47) :
    ∃ o, bytesResize { data := v } n = .ok o ∧ o.data.take v.length = v := by
  unfold bytesResize
  simp only [bind, Except.bind, bytesResizeCheck_ok _ _ hs, pure, Except.pure]
  by_cases he : (n : Int) = v.length
  · refine ⟨{ data := v }, by simp [he], by simp⟩
  · refine ⟨{ data := v.take (n : Int).toNat ++ List.replicate ((n : Int).toNat - v.length) 0 }, ?_, ?_⟩
    · simp [he]
    · have e : (n : Int).toNat = n := by omega
      simp [e, hn, List.take_of_length_le]

theorem concatSpec_proven : ConcatSpec := by
  have hC : ∀ (a b : Seq), (a.length : Int) + b.length + 33 < 2 ^ 47 →
      bytesConcat (.bytes a) (.bytes b) = .ok (a ++ b) := by
    intro a b h
    have h1 : ¬ ((a.length : Int) > ssizeMax - b.length) := by rw [ssizeMax_val]; omega
    have h2 := from_string_ok (a ++ b) (by simp; omega)
    simp only [List.length_append, Int.natCast_add] at h2
    simp only [bytesConcat, Obj.buffer?, h1, if_false, h2]
  refine ⟨hC, ?_, ?_⟩
  · intro a o h
    have hA : (Obj.bytes a).buffer? = some a := rfl
    unfold bytesConcat
    rw [hA, h]
  · intro v w h
    have hA : (Obj.bytes v).buffer? = some v := rfl
    cases hb : w.buffer? with
    | none =>
      unfold pyBytesConcat bytesConcat
      simp [hb, hA]
    | some wb =>
      simp only [hb, Option.getD_some] at h
      have h1 : ¬ ((v.length : Int) > ssizeMax - wb.length) := by rw [ssizeMax_val]; omega
      have hshared : bytesConcat (.bytes v) w = .ok (v ++ wb) := by
        have h2 := from_string_ok (v ++ wb) (by simp; omega)
        simp only [List.length_append, Int.natCast_add] at h2
        unfold bytesConcat
        rw [hA, hb]
        simp only [h1, if_false, h2]
      obtain ⟨o, ho, hdata⟩ := bytesResize_grow v (v.length + wb.length) (by omega) (by simp; omega)
      unfold pyBytesConcat
      simp only [hb, h1, if_false, if_true, hshared]
      have e : ((v.length : Int) + wb.length) = ((v.length + wb.length : Nat) : Int) := by omega
      have ho' : bytesResize { data := v } ((v.length : Int) + wb.length) = .ok o := by rw [e]; exact ho
      simp [pyBytesResize, ho', hdata]

end PyLean.BytesObj.Bytes
