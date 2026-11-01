import PyLean.TextLibs.ReEngineProps

/-!
Properties of the compiler's helpers: the bit and byte packing that the engine reads back, the
overlap table that the prefix search relies on, and `_simple`.
-/

namespace PyLean.TextLibs.Re

open PyLean

set_option linter.unusedSimpArgs false

/-! ### Packing -/

/-- A little-endian word: the digit at `k` of a `foldr` is the element at `k`. -/
theorem digit_fold (B : Nat) (hB : 0 < B) : ∀ (l : List Nat) (k : Nat), (∀ x ∈ l, x < B) →
    (l.foldr (fun x acc => acc * B + x) 0) / B ^ k % B = l.getD k 0 := by
  intro l
  induction l with
  | nil =>
    intro k _
    simp
  | cons x t ih =>
    intro k h
    have hx : x < B := h x (by simp)
    have ht := fun y (hy : y ∈ t) => h y (by simp [hy])
    simp only [List.foldr_cons]
    generalize hA : t.foldr (fun x acc => acc * B + x) 0 = A at *
    cases k with
    | zero =>
      simp only [Nat.pow_zero, Nat.div_one, List.getD_cons_zero]
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hx]
    | succ k =>
      have h1 : (A * B + x) / B = A := by
        rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt hx, Nat.add_zero]
      rw [Nat.pow_succ, Nat.mul_comm (B ^ k) B, ← Nat.div_div_eq_div_mul, h1, ih k ht]
      simp

/-- What `go` of `_bytes_to_codes` and of `_mk_bitmap` have in common: chunks of `n`, folded. -/
def chunkWords (n : Nat) (w : List Nat → Nat) : (fuel : Nat) → List Nat → List Nat
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, s => w (s.take n) :: chunkWords n w fuel (s.drop n)

theorem chunkWords_getD (n : Nat) (hn : 0 < n) (w : List Nat → Nat) : ∀ (fuel : Nat) (s : List Nat) (j : Nat),
    s.length ≤ fuel → j * n < s.length → (chunkWords n w fuel s).getD j 0 = w ((s.drop (j * n)).take n) := by
  intro fuel
  induction fuel with
  | zero => intro s j h1 h2; omega
  | succ fuel ih =>
    intro s j h1 h2
    match s with
    | [] => simp at h2
    | x :: t =>
      show (w ((x :: t).take n) :: chunkWords n w fuel ((x :: t).drop n)).getD j 0 = _
      generalize hs : x :: t = s at *
      cases j with
      | zero => simp
      | succ j =>
        have h3 : (j + 1) * n = n + j * n := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
        have hd : (s.drop n).length ≤ fuel := by
          simp only [List.length_drop]
          omega
        have hj : j * n < (s.drop n).length := by
          simp only [List.length_drop]
          rw [h3] at h2
          omega
        rw [List.getD_cons_succ, ih _ j hd hj, h3, List.drop_drop]

theorem take_getD (l : List Nat) (n k : Nat) (h : k < n) : (l.take n).getD k 0 = l.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]

theorem drop_getD (l : List Nat) (n k : Nat) : (l.drop n).getD k 0 = l.getD (n + k) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- The digit at `i` of a list packed in words of `n` digits. -/
theorem packed_digit (B n : Nat) (hB : 0 < B) (hn : 0 < n) (s : List Nat) (i : Nat)
    (h : ∀ x ∈ s, x < B) (hi : i < s.length) :
    (chunkWords n (fun l => l.foldr (fun x acc => acc * B + x) 0) s.length s).getD (i / n) 0 /
      B ^ (i % n) % B = s.getD i 0 := by
  have h1 : i / n * n ≤ i := Nat.div_mul_le_self i n
  rw [chunkWords_getD n hn _ _ s _ (Nat.le_refl _) (by omega), digit_fold B hB]
  · rw [take_getD _ _ _ (Nat.mod_lt _ hn), drop_getD]
    congr 1
    have := Nat.div_add_mod i n
    rw [Nat.mul_comm] at this
    omega
  · intro x hx
    exact h x (List.mem_of_mem_drop (List.mem_of_mem_take hx))

theorem mkBitmap_eq (bits : List Bool) :
    mkBitmap bits = chunkWords 32 (fun l => l.foldr (fun x acc => acc * 2 + x) 0)
      (bits.map fun b => if b then 1 else 0).length (bits.map fun b => if b then 1 else 0) := by
  have : ∀ (fuel : Nat) (b : List Bool), mkBitmap.go fuel b =
      chunkWords 32 (fun l => l.foldr (fun x acc => acc * 2 + x) 0) fuel
        (b.map fun b => if b then 1 else 0) := by
    intro fuel
    induction fuel with
    | zero => intro _; rfl
    | succ fuel ih =>
      intro b
      cases b with
      | nil => rfl
      | cons x t =>
        have e : (((x :: t).take 32).foldr (fun x acc => acc * 2 + (if x then 1 else 0)) 0) =
            (((x :: t).map fun b => if b then 1 else 0).take 32).foldr
              (fun x acc => acc * 2 + x) 0 := by
          rw [← List.map_take, List.foldr_map]
        show ((((x :: t).take 32).foldr (fun x acc => acc * 2 + (if x then 1 else 0)) 0) ::
            mkBitmap.go fuel ((x :: t).drop 32)) = _
        rw [e, ih, List.map_drop]
        rfl
  rw [List.length_map]
  exact this _ _

/-- `_mk_bitmap`: bit `i` of the words, read the way `SRE(charset)` reads `CHARSET`, is `bits[i]`. -/
def BitmapLaw : Prop :=
  ∀ (bits : List Bool) (i : Nat), i < bits.length →
    ((mkBitmap bits).getD (i / 32) 0 / 2 ^ (i % 32) % 2 == 1) = bits.getD i false

theorem bitmapLaw_proven : BitmapLaw := by
  intro bits i hi
  have hb : ∀ x ∈ bits.map (fun b => if b then 1 else 0), x < 2 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨b, _, rfl⟩ := hx
    split <;> omega
  rw [mkBitmap_eq, packed_digit 2 32 (by decide) (by decide) _ i hb (by simpa using hi)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : bits[i]? with
  | none => simp
  | some b => cases b <;> simp

theorem bytesToCodes_eq (b : List Nat) :
    bytesToCodes b = chunkWords 4 (fun l => l.foldr (fun x acc => acc * 256 + x) 0) b.length b := by
  have : ∀ (fuel : Nat) (s : List Nat), bytesToCodes.go fuel s =
      chunkWords 4 (fun l => l.foldr (fun x acc => acc * 256 + x) 0) fuel s := by
    intro fuel
    induction fuel with
    | zero => intro _; rfl
    | succ fuel ih =>
      intro s
      cases s with
      | nil => rfl
      | cons x t =>
        show ((((x :: t).take 4).foldr (fun x acc => acc * 256 + x) 0) ::
            bytesToCodes.go fuel ((x :: t).drop 4)) = _
        rw [ih]
        rfl
  exact this _ _

/-- `_bytes_to_codes`: byte `i` of the words, read the way `SRE(charset)` reads the block map of
`BIGCHARSET`, is `b[i]`. The hypothesis is the type invariant of a `bytes` value. -/
def BytesToCodesLaw : Prop :=
  ∀ (b : List Nat) (i : Nat), (∀ x ∈ b, x < 256) → i < b.length →
    (bytesToCodes b).getD (i / 4) 0 / 256 ^ (i % 4) % 256 = b.getD i 0

theorem bytesToCodesLaw_proven : BytesToCodesLaw := by
  intro b i hb hi
  rw [bytesToCodes_eq]
  exact packed_digit 256 4 (by decide) (by decide) b i hb hi

/-! ### The overlap table -/

/-- `k` is a proper border of `p[:i+1]`: its first `k` elements are also its last `k`. -/
def Border (p : List Nat) (i k : Nat) : Prop :=
  k ≤ i ∧ ∀ j, j < k → p.getD j 0 = p.getD (i + 1 - k + j) 0

/-- `k` is the longest proper border of `p[:i+1]`. -/
def IsMaxBorder (p : List Nat) (i k : Nat) : Prop :=
  Border p i k ∧ ∀ m, Border p i m → m ≤ k

/-- The table so far is right. -/
def TableOk (p : List Nat) (t : List Nat) : Prop :=
  ∀ j, j < t.length → IsMaxBorder p j (t.getD j 0)

theorem border_extend {p : List Nat} {i k : Nat} (h : Border p i k) (hc : p.getD (i + 1) 0 = p.getD k 0) :
    Border p (i + 1) (k + 1) := by
  refine ⟨by have := h.1; omega, fun j hj => ?_⟩
  by_cases hk : j = k
  · subst hk
    rw [show i + 1 + 1 - (j + 1) + j = i + 1 by have := h.1; omega]
    exact hc.symm
  · rw [show i + 1 + 1 - (k + 1) + j = i + 1 - k + j by have := h.1; omega]
    exact h.2 j (by omega)

/-- A border of `p[:i+1]` longer than `k + 1` shortens to a border of `p[:i]`. -/
theorem border_shrink {p : List Nat} {i m : Nat} (h : Border p (i + 1) (m + 1)) : Border p i m := by
  refine ⟨by have := h.1; omega, fun j hj => ?_⟩
  have := h.2 j (by omega)
  rwa [show i + 1 + 1 - (m + 1) + j = i + 1 - m + j by have := h.1; omega] at this

/-- A shorter border of the same prefix is a border of the longer border. -/
theorem border_of_border {p : List Nat} {i k m : Nat} (hk : Border p i k) (hm : Border p i m)
    (hlt : m < k) : Border p (k - 1) m := by
  refine ⟨by omega, fun j hj => ?_⟩
  have h1 := hm.2 j hj
  have h2 := hk.2 (k - m + j) (by omega)
  rw [show k - 1 + 1 - m + j = k - m + j by omega, h2, h1]
  congr 1
  have := hk.1
  omega

/-- A border of a border is a border. -/
theorem border_trans {p : List Nat} {i k m : Nat} (hk : Border p i k) (hk0 : 0 < k)
    (hm : Border p (k - 1) m) : Border p i m := by
  have h0 := hm.1
  have h1 := hk.1
  refine ⟨by omega, fun j hj => ?_⟩
  have h2 := hm.2 j hj
  have h3 := hk.2 (k - 1 + 1 - m + j) (by omega)
  rw [h2, h3]
  congr 1
  omega

theorem border_zero (p : List Nat) (i : Nat) : Border p i 0 := ⟨by omega, fun _ h => by omega⟩

/-- The `while` of `_generate_overlap_table`. `idx` is a border of `p[:i]`, and every border of
`p[:i+1]` extends a border no longer than `idx`, so the first extension found is the longest. -/
theorem walk_spec (p t : List Nat) (i : Nat) (hi : 1 ≤ i) (hlen : t.length = i) (ht : TableOk p t) :
    ∀ (fuel idx : Nat), idx < fuel → Border p (i - 1) idx →
    (∀ m, Border p i (m + 1) → m ≤ idx) →
    IsMaxBorder p i (overlapTable.walk (fun i => p.getD i 0) i t fuel idx) := by
  intro fuel
  induction fuel with
  | zero => intro idx h; omega
  | succ fuel ih =>
    intro idx hf hb hu
    have hi' : i - 1 + 1 = i := by omega
    unfold overlapTable.walk
    by_cases hc : (p.getD i 0 == p.getD idx 0) = true
    · simp only [hc, if_true]
      have hc' : p.getD i 0 = p.getD idx 0 := by simpa using hc
      refine ⟨?_, fun m hm => ?_⟩
      · have := border_extend (p := p) (i := i - 1) hb (by rw [hi']; exact hc')
        rwa [hi'] at this
      · cases m with
        | zero => omega
        | succ m => have := hu m hm; omega
    · have hne : p.getD i 0 ≠ p.getD idx 0 := by simpa using hc
      simp only [hc, Bool.false_eq_true, if_false]
      have hlt : ∀ m, Border p i (m + 1) → m < idx := by
        intro m hm
        have h1 := hu m hm
        by_cases h2 : m = idx
        · subst h2
          exfalso
          apply hne
          have := hm.2 m (by omega)
          rw [show i + 1 - (m + 1) + m = i by have := hm.1; omega] at this
          exact this.symm
        · omega
      by_cases h0 : (idx == 0) = true
      · simp only [h0, if_true]
        have h0' : idx = 0 := by simpa using h0
        subst h0'
        refine ⟨border_zero p i, fun m hm => ?_⟩
        cases m with
        | zero => omega
        | succ m => have := hlt m hm; omega
      · have h0' : idx ≠ 0 := by simpa using h0
        simp only [h0, Bool.false_eq_true, if_false]
        have hidx : idx - 1 < t.length := by
          have := hb.1
          omega
        obtain ⟨h3, h4⟩ := ht (idx - 1) hidx
        apply ih _ _ (border_trans hb (by omega) h3)
        · intro m hm
          have h5 := border_shrink (p := p) (i := i - 1) (m := m) (by rw [hi']; exact hm)
          exact h4 m (border_of_border hb h5 (hlt m hm))
        · have := h3.1
          omega

theorem getD_app_left (a b : List Nat) (i : Nat) (h : i < a.length) :
    (a ++ b).getD i 0 = a.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_self (a : List Nat) (x : Nat) : (a ++ [x]).getD a.length 0 = x := by
  simp [List.getD_eq_getElem?_getD]

/-- `go` keeps the table right, one entry at a time. -/
theorem go_spec (p : List Nat) : ∀ (fuel i : Nat) (t : List Nat), 1 ≤ i → t.length = i →
    i + fuel = p.length → TableOk p t →
    TableOk p (overlapTable.go (fun i => p.getD i 0) fuel i t) ∧
      (overlapTable.go (fun i => p.getD i 0) fuel i t).length = p.length := by
  intro fuel
  induction fuel with
  | zero =>
    intro i t _ h1 h2 h3
    exact ⟨h3, by simp only [overlapTable.go]; omega⟩
  | succ fuel ih =>
    intro i t hi h1 h2 h3
    simp only [overlapTable.go]
    have hprev : i - 1 < t.length := by omega
    obtain ⟨h4, h5⟩ := h3 (i - 1) hprev
    have hnew := walk_spec p t i hi h1 h3 (i + 1) (t.getD (i - 1) 0) (by have := h4.1; omega) h4
      (fun m hm => h5 m (border_shrink (p := p) (i := i - 1) (m := m)
        (by rw [show i - 1 + 1 = i by omega]; exact hm)))
    apply ih (i + 1) _ (by omega) (by simp [h1]) (by omega)
    intro j hj
    simp only [List.length_append, List.length_cons, List.length_nil] at hj
    by_cases hjt : j < t.length
    · rw [getD_app_left _ _ _ hjt]
      exact h3 j hjt
    · have : j = t.length := by omega
      subst this
      rw [getD_app_self, h1]
      exact hnew

/-- `_generate_overlap_table`: entry `i` is the length of the longest proper border of `p[:i+1]`,
which is what makes the prefix search skip no occurrence. For every prefix. -/
def OverlapTableLaw : Prop :=
  ∀ p : List Nat, (overlapTable p).length = p.length ∧
    ∀ i, i < p.length → IsMaxBorder p i ((overlapTable p).getD i 0)

theorem overlapTableLaw_proven : OverlapTableLaw := by
  intro p
  match p with
  | [] => exact ⟨rfl, fun i h => by simp at h⟩
  | x :: r =>
    have h0 : TableOk (x :: r) [0] := by
      intro j hj
      have : j = 0 := by simpa using hj
      subst this
      refine ⟨border_zero _ _, fun m hm => ?_⟩
      have := hm.1
      simpa using this
    obtain ⟨h1, h2⟩ := go_spec (x :: r) ((x :: r).length - 1) 1 [0] (by omega) rfl (by simp; omega) h0
    have e : overlapTable (x :: r) =
        overlapTable.go (fun i => (x :: r).getD i 0) ((x :: r).length - 1) 1 [0] := rfl
    rw [e]
    exact ⟨h2, fun i hi => h1 i (by rw [h2]; exact hi)⟩

/-! ### `_simple` -/

mutual
  theorem simple_width (gw : List (Option (Nat × Nat))) : ∀ p : List Node, simple p = true →
      widthList gw p = (1, 1)
    | [n], h => by
      have h1 := simpleNode_width gw n (by simpa [simple] using h) 0 0
      simp only [widthList]
      rw [h1]
    | [], h => by simp [simple] at h
    | _ :: _ :: _, h => by simp [simple] at h

  theorem simpleNode_width (gw : List (Option (Nat × Nat))) : ∀ n : Node, simpleNode n = true →
      ∀ lo hi, widthNode gw n lo hi = (lo + 1, hi + 1)
    | .literal _, _, _, _ => rfl
    | .notLiteral _, _, _, _ => rfl
    | .any, _, _, _ => rfl
    | .in_ _, _, _, _ => rfl
    | .subpattern none _ _ p, h, lo, hi => by
      have h1 := simple_width gw p (by simpa [simpleNode] using h)
      simp only [widthNode, h1]
      rfl
    | .subpattern (some _) _ _ _, h, _, _ => by simp [simpleNode] at h
    | .at_ _, h, _, _ => by simp [simpleNode] at h
    | .groupref _, h, _, _ => by simp [simpleNode] at h
    | .grouprefExists _ _ _, h, _, _ => by simp [simpleNode] at h
    | .branch _, h, _, _ => by simp [simpleNode] at h
    | .repeat_ _ _ _ _, h, _, _ => by simp [simpleNode] at h
    | .atomic _, h, _, _ => by simp [simpleNode] at h
    | .assert_ _ _, h, _, _ => by simp [simpleNode] at h
    | .assertNot _ _, h, _, _ => by simp [simpleNode] at h
    | .failure, h, _, _ => by simp [simpleNode] at h
end

/-- `_simple`: what it accepts has width exactly 1, which is what lets `REPEAT_ONE` step back one
character at a time. -/
def SimpleWidth : Prop :=
  ∀ (gw : List (Option (Nat × Nat))) (p : List Node), simple p = true → widthList gw p = (1, 1)

theorem simpleWidth_proven : SimpleWidth := simple_width

end PyLean.TextLibs.Re
