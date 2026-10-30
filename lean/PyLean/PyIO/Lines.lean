import PyLean.PyIO.Spec

/-!
Line scanning: `C.scanEol` (bytesio.c) and the byte-at-a-time loop of
`IOBase.readline` (_pyio.py) both read `lineLen` bytes.
-/

namespace PyLean.PyIO

open PyLean

/-- Length of the first line of `rest`, including its `\n`, or all of `rest`. -/
def lineLen (rest : List Nat) : Nat :=
  match findIdx? rest 10 with
  | some i => i + 1
  | none => rest.length

theorem lineLen_nil : lineLen [] = 0 := rfl

theorem lineLen_cons_nl (r : List Nat) : lineLen (10 :: r) = 1 := by
  simp [lineLen, findIdx?]

theorem lineLen_cons (x : Nat) (r : List Nat) (hx : x ≠ 10) : lineLen (x :: r) = lineLen r + 1 := by
  unfold lineLen
  simp only [findIdx?, hx, ite_false]
  cases findIdx? r 10 <;> simp

theorem findIdx?_lt (l : List Nat) (c i : Nat) (h : findIdx? l c = some i) : i < l.length := by
  induction l generalizing i with
  | nil => simp [findIdx?] at h
  | cons x xs ih =>
    simp only [findIdx?] at h
    split at h
    · simp at h; subst h; simp
    · cases h' : findIdx? xs c with
      | none => simp [h'] at h
      | some j => simp [h'] at h; have := ih j h'; simp; omega

theorem lineLen_le (r : List Nat) : lineLen r ≤ r.length := by
  unfold lineLen
  split
  · next i h => have := findIdx?_lt r 10 i h; omega
  · exact Nat.le_refl _

theorem lineLen_pos (r : List Nat) (h : r ≠ []) : 0 < lineLen r := by
  cases r with
  | nil => exact absurd rfl h
  | cons x xs =>
    by_cases hx : x = 10
    · subst hx; simp [lineLen_cons_nl]
    · rw [lineLen_cons x xs hx]; omega

theorem lineLen_eq_zero (r : List Nat) : lineLen r = 0 ↔ r = [] := by
  constructor
  · intro h
    cases r with
    | nil => rfl
    | cons x xs => have := lineLen_pos (x :: xs) (by simp); omega
  · intro h; subst h; rfl

theorem slice_length (buf : List Nat) (a n : Nat) (hn : n ≤ (buf.drop a).length) :
    (slice buf a n).length = n := by
  simp [slice] at hn ⊢; omega

theorem slice_eq_nil (buf : List Nat) (a n : Nat) (hn : n ≤ (buf.drop a).length) :
    slice buf a n = [] ↔ n = 0 := by
  constructor
  · intro h; have := slice_length buf a n hn; rw [h] at this; simp at this; omega
  · intro h; subst h; simp [slice]

/-- The tail of `scan_eol_lock_held` once the limit `L` is fixed. -/
theorem scanCore (r : List Nat) (L : Nat) (hL : L ≤ r.length) :
    (if L = 0 then 0 else match findIdx? (r.take L) 10 with
      | some i => i + 1
      | none => L) = lineLen (r.take L) := by
  split
  · next h => subst h; simp [lineLen_nil]
  · unfold lineLen
    split <;> simp_all [List.length_take]

/-- `C.scanEol` reads `lineLen` of the next `len` bytes (all remaining bytes for
a negative `len`). -/
theorem scanEol_eq (s : BState) (len : Int) :
    C.scanEol s len = lineLen ((s.buf.drop s.pos).take (if len < 0 then s.buf.length else len.toNat)) := by
  unfold C.scanEol
  by_cases hp : s.pos ≥ s.buf.length
  · have : s.buf.drop s.pos = [] := List.drop_eq_nil_of_le hp
    simp [hp, this, lineLen_nil]
  · simp only [hp, ite_false]
    have hlen : (s.buf.drop s.pos).length = s.buf.length - s.pos := by simp
    generalize hL : (if len < 0 ∨ len > ((s.buf.length - s.pos : Nat) : Int) then s.buf.length - s.pos
        else len.toNat) = L
    have hLle : L ≤ (s.buf.drop s.pos).length := by
      rw [hlen, ← hL]; split <;> omega
    have key : (s.buf.drop s.pos).take L =
        (s.buf.drop s.pos).take (if len < 0 then s.buf.length else len.toNat) := by
      rw [← hL]
      split
      · next h =>
        rcases h with h | h
        · simp only [h, ite_true]
          rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
        · have : ¬ len < 0 := by omega
          simp only [this, ite_false]
          rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      · next h =>
        have : ¬ len < 0 := by omega
        simp [this]
    rw [← key, ← scanCore _ L hLle]
    rfl

/-- One byte of `_pyio.BytesIO.read(1)` on an open stream. -/
theorem readRaw_one (s : BState) (hc : s.closed = false) :
    P.readRaw s (some 1) =
      if s.buf.length ≤ s.pos then (s, .ok []) else ({ s with pos := s.pos + 1 }, .ok (slice s.buf s.pos 1)) := by
  unfold P.readRaw
  simp only [hc, Bool.false_eq_true, ite_false, Option.getD_some]
  split
  · rfl
  · next h =>
    have h2 : min s.buf.length (s.pos + 1) = s.pos + 1 := by omega
    simp [h2]

theorem slice_succ (buf : List Nat) (a k : Nat) (ha : a < buf.length) :
    slice buf a (k + 1) = buf[a] :: slice buf (a + 1) k := by
  unfold slice
  rw [List.drop_eq_getElem_cons ha, List.take_succ_cons]

theorem take_drop_cons (buf : List Nat) (a m : Nat) (ha : a < buf.length) :
    (buf.drop a).take (m + 1) = buf[a] :: (buf.drop (a + 1)).take m := by
  rw [List.drop_eq_getElem_cons ha, List.take_succ_cons]

/-- The `IOBase.readline` loop of `_pyio.BytesIO` reads `lineLen` of the next
`size - len(res)` bytes. -/
theorem readlineLoop_eq (size : Int) : ∀ (fuel : Nat) (s : BState) (res : List Nat),
    s.closed = false → s.buf.length - s.pos < fuel → (size < 0 ∨ (res.length : Int) ≤ size) →
    P.readlineLoop size s res fuel =
      ({ s with pos := s.pos + lineLen ((s.buf.drop s.pos).take
          (if size < 0 then s.buf.length else (size - res.length).toNat)) },
       .ok (res ++ slice s.buf s.pos (lineLen ((s.buf.drop s.pos).take
          (if size < 0 then s.buf.length else (size - res.length).toNat))))) := by
  intro fuel
  induction fuel with
  | zero => intro s res _ h; omega
  | succ f ih =>
    intro s res hc hf hs
    unfold P.readlineLoop
    by_cases hgo : size < 0 ∨ (res.length : Int) < size
    · rw [if_pos hgo, readRaw_one s hc]
      by_cases hend : s.buf.length ≤ s.pos
      · have : s.buf.drop s.pos = [] := List.drop_eq_nil_of_le hend
        simp [hend, this, lineLen_nil, slice]
      · simp only [hend, ite_false]
        have hlt : s.pos < s.buf.length := by omega
        have hsl : slice s.buf s.pos 1 = [s.buf[s.pos]] := by
          rw [slice_succ _ _ _ hlt]; simp [slice]
        rw [hsl]
        simp only [List.cons_ne_nil, ite_false]
        -- the limit is at least one
        have hlim : ∃ m, (if size < 0 then s.buf.length else (size - res.length).toNat) = m + 1 := by
          split
          · exact ⟨s.buf.length - 1, by omega⟩
          · next h => exact ⟨(size - res.length).toNat - 1, by omega⟩
        obtain ⟨m, hm⟩ := hlim
        rw [hm, take_drop_cons _ _ _ hlt]
        by_cases hx : s.buf[s.pos] = 10
        · have : (res ++ [s.buf[s.pos]]).getLast? = some 10 := by simp [hx]
          simp only [this, ite_true]
          rw [hx, lineLen_cons_nl, slice_succ _ _ _ hlt, hx]
          simp [slice]
        · have : ¬ (res ++ [s.buf[s.pos]]).getLast? = some 10 := by simp [hx]
          simp only [this, ite_false]
          rw [ih { s with pos := s.pos + 1 } (res ++ [s.buf[s.pos]]) hc
            (by show s.buf.length - (s.pos + 1) < f; omega)
            (by simp only [List.length_append, List.length_singleton]; omega)]
          rw [lineLen_cons _ _ hx]
          have hm' : (if size < 0 then s.buf.length else (size - ((res ++ [s.buf[s.pos]]).length : Int)).toNat)
              = (if size < 0 then s.buf.length else m) := by
            split
            · rfl
            · next h => simp at hm ⊢; split at hm <;> omega
          simp only [hm']
          -- for size < 0 both limits cover the rest of the buffer
          have ht : (s.buf.drop (s.pos + 1)).take (if size < 0 then s.buf.length else m) =
              (s.buf.drop (s.pos + 1)).take m := by
            split
            · next h =>
              simp [h] at hm
              rw [List.take_of_length_le (by simp only [List.length_drop]; omega), List.take_of_length_le (by simp only [List.length_drop]; omega)]
            · rfl
          rw [ht, slice_succ _ _ _ hlt]
          refine Prod.ext ?_ ?_
          · simp; omega
          · simp
    · rw [if_neg hgo]
      have h0 : (if size < 0 then s.buf.length else (size - res.length).toNat) = 0 := by
        have : ¬ size < 0 := fun h => hgo (Or.inl h)
        simp only [this, ite_false]; omega
      rw [h0]; simp [lineLen_nil, slice]

/-- `_pyio.BytesIO.readline(size)` on an open stream reads the same bytes as
`C.scanEol`. -/
theorem readlineRaw_eq (s : BState) (size : Option Int) (hc : s.closed = false) :
    P.readlineRaw s size =
      ({ s with pos := s.pos + C.scanEol s (size.getD (-1)) },
       .ok (slice s.buf s.pos (C.scanEol s (size.getD (-1))))) := by
  unfold P.readlineRaw
  have hs : size.getD (-1) < 0 ∨ (([] : List Nat).length : Int) ≤ size.getD (-1) := by
    simp only [List.length_nil]; omega
  rw [readlineLoop_eq _ _ _ _ hc (by omega) hs]
  rw [scanEol_eq]
  have : (if size.getD (-1) < 0 then s.buf.length else (size.getD (-1) - (([] : List Nat).length : Int)).toNat)
      = (if size.getD (-1) < 0 then s.buf.length else (size.getD (-1)).toNat) := by simp
  rw [this]; simp

end PyLean.PyIO
