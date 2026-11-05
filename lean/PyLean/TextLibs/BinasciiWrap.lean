import PyLean.TextLibs.BinasciiRest

/-!
`wraplines`, `Modules/binascii.c:457-481`, as the C loop does it: it counts `(size - 1) / width`
newlines, gives the last line what is left, and moves the lines right from the back, one `memmove` and
one `'\n'` at a time, until the source pointer is back at the start.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

/-- The forward description the earlier proofs use: a newline after every `width` characters, none at
the end. `wraplinesC_eq` has the C loop equal to it. -/
def wraplines (width : Nat) : (fuel : Nat) → List Nat → List Nat
  | 0, s => s
  | fuel + 1, s =>
    if s.length ≤ width then s else s.take width ++ [10] ++ wraplines width fuel (s.drop width)

/-- The `while ((src -= line_len) != data)` loop, `Modules/binascii.c:472-477`. `src` is the source
offset, `acc` what is already written behind `dst`. When `src` reaches the start, the first line has not
moved: it is the data before `src`. `fuel` is the number of turns left; `wraplinesC` gives one more
than the loop takes. -/
def wrapBack (data : List Nat) (width : Nat) : (fuel src lineLen : Nat) → List Nat → List Nat
  | 0, src, _, acc => data.take src ++ acc
  | fuel + 1, src, lineLen, acc =>
    let src' := src - lineLen
    if src' = 0 then data.take src ++ acc
    else wrapBack data width fuel src' width (10 :: (data.extract src' src ++ acc))

/-- `wraplines(data, size, width)`, `Modules/binascii.c:461-481`: nothing when `size <= width`; else
`newlines = (size - 1) / width`, a last line of `size - newlines * width`, and the backward loop. The
callers never pass a width of zero. -/
def wraplinesC (data : List Nat) (width : Nat) : List Nat :=
  let size := data.length
  if size ≤ width then data
  else
    let newlines := (size - 1) / width
    let lineLen := size - newlines * width
    wrapBack data width (newlines + 1) size lineLen []

/-- A forward description: `m` newlines, each after `width` characters. -/
def chunksJoin (width : Nat) : (m : Nat) → List Nat → List Nat
  | 0, s => s
  | m + 1, s => s.take width ++ 10 :: chunksJoin width m (s.drop width)

theorem chunksJoin_snoc (w : Nat) : ∀ (j : Nat) (a b : List Nat), a.length = (j + 1) * w →
    chunksJoin w (j + 1) (a ++ b) = chunksJoin w j a ++ 10 :: b := by
  intro j
  induction j with
  | zero =>
    intro a b h
    have h1 : a.length = w := by simpa using h
    simp [chunksJoin, List.take_left' h1, List.drop_left' h1]
  | succ j ih =>
    intro a b h
    have hw : w ≤ a.length := by rw [h]; exact Nat.le_mul_of_pos_left w (by omega)
    have ht : (a ++ b).take w = a.take w := List.take_append_of_le_length hw
    have hd : (a ++ b).drop w = a.drop w ++ b := List.drop_append_of_le_length hw
    have hl : (a.drop w).length = (j + 1) * w := by
      simp only [List.length_drop, h]
      rw [Nat.succ_mul (j + 1)]
      omega
    rw [chunksJoin, ht, hd, ih _ _ hl, chunksJoin]
    simp

theorem take_split (data : List Nat) (a c : Nat) (h : a ≤ c) :
    data.take c = data.take a ++ data.extract a c := by
  rw [List.extract_eq_drop_take]
  have : c = a + (c - a) := by omega
  conv => lhs; rw [this]
  rw [List.take_add]

theorem wrapBack_eq (data : List Nat) (w : Nat) (hw : 0 < w) :
    ∀ (j len fuel : Nat) (acc : List Nat), 0 < len → j < fuel → j * w + len ≤ data.length →
      wrapBack data w fuel (j * w + len) len acc = chunksJoin w j (data.take (j * w + len)) ++ acc := by
  intro j
  induction j with
  | zero =>
    intro len fuel acc hl hf _
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp [wrapBack, chunksJoin]
  | succ j ih =>
    intro len fuel acc hl hf hd
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have e1 : (j + 1) * w = j * w + w := Nat.succ_mul j w
    have hs : (j + 1) * w + len - len = j * w + w := by omega
    have hne : ¬ (j * w + w = 0) := by omega
    simp only [wrapBack, hs, hne, if_false]
    rw [ih w f _ hw (by omega) (by omega)]
    rw [take_split data (j * w + w) ((j + 1) * w + len) (by omega)]
    have hl2 : (data.take (j * w + w)).length = (j + 1) * w := by
      simp only [List.length_take]; omega
    rw [chunksJoin_snoc w j _ _ hl2]
    simp

/-- `wraplinesC` is the forward description with `(size - 1) / width` newlines. -/
theorem wraplinesC_join (s : List Nat) (w : Nat) (hw : 0 < w) (h : w < s.length) :
    wraplinesC s w = chunksJoin w ((s.length - 1) / w) s := by
  have hm : (s.length - 1) / w * w ≤ s.length - 1 := Nat.div_mul_le_self _ _
  have hlt : s.length - 1 < ((s.length - 1) / w + 1) * w := by
    rw [Nat.succ_mul]
    have := Nat.lt_div_mul_add (a := s.length - 1) hw
    omega
  have e : (s.length - 1) / w * w + (s.length - (s.length - 1) / w * w) = s.length := by omega
  simp only [wraplinesC, if_neg (by omega : ¬ s.length ≤ w)]
  have := wrapBack_eq s w hw ((s.length - 1) / w) (s.length - (s.length - 1) / w * w) ((s.length - 1) / w + 1) []
    (by omega) (by omega) (by omega)
  rw [e] at this
  rw [this]
  simp

theorem wraplinesC_short (s : List Nat) (w : Nat) (h : s.length ≤ w) : wraplinesC s w = s := by
  simp [wraplinesC, h]

theorem wraplinesC_long (s : List Nat) (w : Nat) (hw : 0 < w) (h : w < s.length) :
    wraplinesC s w = s.take w ++ 10 :: wraplinesC (s.drop w) w := by
  rw [wraplinesC_join s w hw h]
  have hpos : 0 < (s.length - 1) / w := Nat.div_pos (by omega) hw
  obtain ⟨m, hm⟩ : ∃ m, (s.length - 1) / w = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hm, chunksJoin]
  congr 2
  by_cases h2 : (s.drop w).length ≤ w
  · rw [wraplinesC_short _ _ h2]
    have : m = 0 := by
      simp only [List.length_drop] at h2
      have : (s.length - 1) / w < 2 := by
        apply (Nat.div_lt_iff_lt_mul hw).mpr
        omega
      omega
    subst this
    rfl
  · rw [wraplinesC_join _ w hw (by omega)]
    congr 1
    simp only [List.length_drop]
    have e1 : s.length - w - 1 + w = s.length - 1 := by omega
    have e2 : (s.length - w - 1 + w) / w = (s.length - w - 1) / w + 1 := Nat.add_div_right _ hw
    rw [e1, hm] at e2
    omega

theorem wraplinesC_eq (w : Nat) (hw : 0 < w) : ∀ (f : Nat) (s : List Nat), s.length ≤ f →
    wraplinesC s w = wraplines w f s := by
  intro f
  induction f with
  | zero =>
    intro s h
    have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rfl
  | succ f ih =>
    intro s h
    by_cases hl : s.length ≤ w
    · rw [wraplinesC_short s w hl, wraplines, if_pos hl]
    · rw [wraplinesC_long s w hw (by omega), wraplines, if_neg hl, ih _ (by simp only [List.length_drop]; omega)]
      simp

theorem wraplinesC_length (w : Nat) (hw : 0 < w) : ∀ (f : Nat) (s : List Nat), s.length ≤ f → s ≠ [] →
    (wraplinesC s w).length = s.length + (s.length - 1) / w := by
  intro f
  induction f with
  | zero =>
    intro s h hne
    exact absurd (List.eq_nil_of_length_eq_zero (by omega)) hne
  | succ f ih =>
    intro s h hne
    by_cases hl : s.length ≤ w
    · rw [wraplinesC_short s w hl]
      have hs : 0 < s.length := List.length_pos_iff.mpr hne
      have : (s.length - 1) / w = 0 := Nat.div_eq_of_lt (by omega)
      omega
    · rw [wraplinesC_long s w hw (by omega)]
      have hd : s.drop w ≠ [] := by
        intro e
        have := congrArg List.length e
        simp only [List.length_drop, List.length_nil] at this
        omega
      have := ih (s.drop w) (by simp only [List.length_drop]; omega) hd
      simp only [List.length_append, List.length_take, List.length_cons, this, List.length_drop]
      have e1 : s.length - w - 1 + w = s.length - 1 := by omega
      have e2 : (s.length - w - 1 + w) / w = (s.length - w - 1) / w + 1 := Nat.add_div_right _ hw
      rw [e1] at e2
      omega

/-- Taking the newlines out gives the data back, when the data has none. -/
theorem wraplinesC_filter (w : Nat) (hw : 0 < w) : ∀ (f : Nat) (s : List Nat), s.length ≤ f → 10 ∉ s →
    (wraplinesC s w).filter (· != 10) = s := by
  intro f
  induction f with
  | zero =>
    intro s h _
    have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rfl
  | succ f ih =>
    intro s h hn
    have hf : ∀ t : List Nat, 10 ∉ t → t.filter (· != 10) = t := by
      intro t ht
      apply List.filter_eq_self.mpr
      intro c hc
      have : c ≠ 10 := fun e => ht (e ▸ hc)
      simpa using this
    by_cases hl : s.length ≤ w
    · rw [wraplinesC_short s w hl]
      exact hf s hn
    · rw [wraplinesC_long s w hw (by omega)]
      have hn2 : 10 ∉ s.drop w := fun e => hn (List.mem_of_mem_drop e)
      rw [List.filter_append, List.filter_cons, hf _ (fun e => hn (List.mem_of_mem_take e)),
        ih _ (by simp only [List.length_drop]; omega) hn2]
      simp

/-- Every character of the output is a character of the data or a newline. -/
theorem wraplinesC_mem (w : Nat) (hw : 0 < w) : ∀ (f : Nat) (s : List Nat), s.length ≤ f →
    ∀ c ∈ wraplinesC s w, c ∈ s ∨ c = 10 := by
  intro f
  induction f with
  | zero =>
    intro s h c hc
    have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [wraplinesC] at hc
  | succ f ih =>
    intro s h c hc
    by_cases hl : s.length ≤ w
    · rw [wraplinesC_short s w hl] at hc
      exact .inl hc
    · rw [wraplinesC_long s w hw (by omega)] at hc
      simp only [List.mem_append, List.mem_cons] at hc
      rcases hc with hc | hc | hc
      · exact .inl (List.mem_of_mem_take hc)
      · exact .inr hc
      · rcases ih _ (by simp only [List.length_drop]; omega) c hc with h1 | h1
        · exact .inl (List.mem_of_mem_drop h1)
        · exact .inr h1

end PyLean.TextLibs.Binascii
