import PyLean.JsonMod.DecC

/-!
Lemmas about Python indexing at non-negative positions, whitespace skipping,
and `findTerm`/`cFind`.
-/

namespace PyLean.JsonMod

open PyLean

theorem pyIndex_nat (s : PStr) (i : Nat) : pyIndex s (i : Int) = s[i]? := by
  simp [pyIndex]

theorem sliceBound_nat (n i : Nat) : sliceBound n (i : Int) = min i n := by
  simp only [sliceBound]
  have : ¬ ((i : Int) < 0) := by omega
  simp [this]

theorem pySlice_nat (s : PStr) (a k : Nat) : pySlice s (a : Int) ((a : Int) + k) = (s.drop a).take k := by
  have : ((a : Int) + k) = ((a + k : Nat) : Int) := by omega
  rw [this]
  simp only [pySlice, sliceBound_nat]
  by_cases h : a ≤ s.length
  · rw [Nat.min_eq_left h, List.take_eq_take_iff]
    simp only [List.length_drop]
    omega
  · rw [Nat.min_eq_right (by omega : s.length ≤ a)]
    simp [List.drop_eq_nil_of_le (by omega : s.length ≤ a)]

theorem pySlice_nat1 (s : PStr) (a : Nat) : pySlice s (a : Int) ((a : Int) + 1) = (s.drop a).take 1 :=
  pySlice_nat s a 1

theorem clampPos_nat {s : PStr} {i : Nat} (h : i ≤ s.length) : clampPos s (i : Int) = i := by
  simp only [clampPos]
  have : ¬ ((i : Int) < 0) := by omega
  simp only [this, ↓reduceIte, Int.toNat_natCast]
  omega

theorem wsEnd_def (s : PStr) (i : Nat) : wsEnd s i = i + wsLen (s.drop i) := rfl


theorem wsLen_le (t : PStr) : wsLen t ≤ t.length := by
  induction t with
  | nil => simp [wsLen]
  | cons c t ih => simp only [wsLen]; split <;> simp <;> omega

theorem wsEnd_le {s : PStr} {i : Nat} (h : i ≤ s.length) : wsEnd s i ≤ s.length := by
  have := wsLen_le (s.drop i)
  simp only [List.length_drop] at this
  simp only [wsEnd]; omega

theorem wsEnd_ge (s : PStr) (i : Nat) : i ≤ wsEnd s i := by simp [wsEnd]

theorem wsEnd_of_none {s : PStr} {i : Nat} (h : s[i]? = none) : wsEnd s i = i := by
  have : s.drop i = [] := List.drop_eq_nil_of_le (by simpa using h)
  simp [wsEnd, this, wsLen]

theorem wsEnd_of_not_ws {s : PStr} {i c : Nat} (h : s[i]? = some c) (hc : isWs c = false) : wsEnd s i = i := by
  have : s.drop i = c :: s.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons (by have := List.getElem?_eq_some_iff.mp h; exact this.1)]
    congr; exact (List.getElem?_eq_some_iff.mp h).2
  simp [wsEnd, this, wsLen, hc]

theorem wsEnd_of_ws {s : PStr} {i c : Nat} (h : s[i]? = some c) (hc : isWs c = true) :
    wsEnd s i = wsEnd s (i + 1) := by
  have : s.drop i = c :: s.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons (by have := List.getElem?_eq_some_iff.mp h; exact this.1)]
    congr; exact (List.getElem?_eq_some_iff.mp h).2
  simp only [wsEnd, this, wsLen, hc, ↓reduceIte]; omega

/-- The character at `wsEnd` is not whitespace. -/
theorem wsEnd_char (s : PStr) (i : Nat) :
    s[wsEnd s i]? = none ∨ ∃ c, s[wsEnd s i]? = some c ∧ isWs c = false := by
  induction h : s.length - i generalizing i with
  | zero =>
    left
    rw [wsEnd_of_none (by simp; omega)]
    simp; omega
  | succ k ih =>
    cases hc : s[i]? with
    | none => left; rw [wsEnd_of_none hc]; exact hc
    | some c =>
      cases hw : isWs c with
      | false => right; rw [wsEnd_of_not_ws hc hw]; exact ⟨c, hc, hw⟩
      | true => rw [wsEnd_of_ws hc hw]; exact ih (i + 1) (by omega)

theorem wsEnd_idem (s : PStr) (i : Nat) : wsEnd s (wsEnd s i) = wsEnd s i := by
  rcases wsEnd_char s i with h | ⟨c, h, hc⟩
  · exact wsEnd_of_none h
  · exact wsEnd_of_not_ws h hc

theorem wsEndPy_nat {s : PStr} {i : Nat} (h : i ≤ s.length) : wsEndPy s (i : Int) = (wsEnd s i : Int) := by
  simp [wsEndPy, clampPos_nat h]

/-- `_w(s, end + 1).end()` right after a whitespace or missing character. -/
theorem wsEndPy_succ {s : PStr} {i : Nat} (h : i ≤ s.length)
    (hw : s[i]? = none ∨ ∃ c, s[i]? = some c ∧ isWs c = true) :
    wsEndPy s ((i : Int) + 1) = (wsEnd s i : Int) := by
  rcases hw with hn | ⟨c, hc, hw⟩
  · have hi : i = s.length := by
      have := List.getElem?_eq_none_iff.mp hn; omega
    subst hi
    have : ((s.length : Int) + 1) = ((s.length + 1 : Nat) : Int) := by omega
    rw [this]
    have h2 : clampPos s ((s.length + 1 : Nat) : Int) = s.length := by
      simp only [clampPos]
      have : ¬ (((s.length + 1 : Nat) : Int) < 0) := by omega
      simp only [this, ↓reduceIte, Int.toNat_natCast]
      omega
    simp only [wsEndPy]
    rw [h2, wsEnd_of_none hn]
  · have hlt : i < s.length := (List.getElem?_eq_some_iff.mp hc).1
    have : ((i : Int) + 1) = ((i + 1 : Nat) : Int) := by omega
    rw [this, wsEndPy_nat (by omega), wsEnd_of_ws hc hw]

theorem drop_take1 {s : PStr} {i : Nat} : (s.drop i).take 1 = (s[i]?).toList := by
  cases h : s[i]? with
  | none =>
    have : s.drop i = [] := List.drop_eq_nil_of_le (by simpa using h)
    simp [this]
  | some c =>
    have hlt := (List.getElem?_eq_some_iff.mp h)
    rw [List.drop_eq_getElem_cons hlt.1]
    simp [hlt.2]

theorem inWsSlice_toList (o : Option Nat) : inWsSlice o.toList = (match o with | none => true | some c => isWs c) := by
  cases o <;> rfl

end PyLean.JsonMod
