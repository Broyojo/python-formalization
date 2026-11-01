import PyLean.ListSort.Model

/-!
# `powerloop` and the pending-run stack bound

`gq N L x = ⌊x * 2^L / (2N)⌋` is the integer formed by the first `L` bits of the
binary expansion of `x / (2N)`. With `A = 2*s1 + n1` and `B = A + n1 + n2` (twice
the midpoints of two adjacent runs), `powerloop` returns the first bit position
at which `A/(2N)` and `B/(2N)` differ (`listsort.txt:382-393`):
`powerIter_spec` / `powerloop_spec`.

The stack bound needs the powers stored on the stack to be strictly increasing
towards the top (`listsort.txt:426-427`, the `assert` at `listobject.c:2663`).
That depends on history: a stored power belongs to the boundary between the
last *original* run of a block and the first original run of the block above,
and every boundary inside a block has a larger power than the block's stored
one. `Below`/`TopInv` record this with a ghost list of original runs per stack
entry. `no_equal_powers` is the arithmetic core: two boundaries with equal power
`L` cannot have only boundaries of power `> L` between them.
-/

namespace PyLean.ListSort

/-- The first `L` bits of `x / (2N)`. -/
def gq (N L x : Nat) : Nat := x * 2 ^ L / (2 * N)

theorem gq_succ_div (N L x : Nat) : gq N (L + 1) x / 2 = gq N L x := by
  unfold gq
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ, ← Nat.mul_assoc]
  exact Nat.mul_div_mul_right _ _ (by decide : 0 < 2)

theorem gq_mono (N L : Nat) {x y : Nat} (h : x ≤ y) : gq N L x ≤ gq N L y :=
  Nat.div_le_div_right (Nat.mul_le_mul_right _ h)

theorem gq_eq_of_le (N : Nat) {L L' x y : Nat} (hL : L' ≤ L) (h : gq N L x = gq N L y) :
    gq N L' x = gq N L' y := by
  obtain ⟨d, rfl⟩ : ∃ d, L = L' + d := ⟨L - L', by omega⟩
  clear hL
  induction d with
  | zero => exact h
  | succ d ih =>
    apply ih
    rw [← gq_succ_div N (L' + d) x, ← gq_succ_div N (L' + d) y, show L' + d + 1 = L' + (d + 1) by omega, h]

/-! ## powerloop -/

/-- Loop invariant of `powerIter` at `result = r`: `a`, `b` are the remainders of
`A * 2^(r-1)` and `B * 2^(r-1)` modulo `2N` with a common quotient. -/
def PInv (n A B r a b : Nat) : Prop :=
  1 ≤ r ∧ a ≤ b ∧ b < 2 * n ∧
    ∃ q, A * 2 ^ (r - 1) = 2 * n * q + a ∧ B * 2 ^ (r - 1) = 2 * n * q + b

theorem pow_pred_succ {r : Nat} (hr : 1 ≤ r) (X : Nat) : X * 2 ^ r = X * 2 ^ (r - 1) * 2 := by
  rw [Nat.mul_assoc, ← Nat.pow_succ]; congr 2; omega

theorem powerIter_spec (n A B : Nat) (hAB : A + 2 ≤ B) :
    ∀ fuel r a b ovf, PInv n A B r a b → fuel + r = n + 2 →
      let res := powerIter n fuel r a b ovf
      1 ≤ res.1 ∧ gq n (res.1 - 1) A = gq n (res.1 - 1) B ∧ gq n res.1 A < gq n res.1 B ∧
        (res.2 = true → ovf = true ∨ 2 ^ 63 < 2 * n) := by
  intro fuel
  induction fuel with
  | zero =>
    intro r a b ovf hi hf
    exfalso
    -- (B - A) * 2^(r-1) = b - a < 2n but r = n + 2
    obtain ⟨hr, hab, hb2, q, ha, hb⟩ := hi
    have h1 : (B - A) * 2 ^ (r - 1) ≤ b - a := by
      rw [Nat.sub_mul]; omega
    have h2 : 2 * 2 ^ (r - 1) ≤ (B - A) * 2 ^ (r - 1) := Nat.mul_le_mul_right _ (by omega)
    have h3 : n + 1 < 2 ^ (r - 1) := by
      have : r - 1 = n + 1 := by omega
      rw [this]; exact Nat.lt_two_pow_self
    omega
  | succ fuel ih =>
    intro r a b ovf hi hf
    obtain ⟨hr, hab, hb2, q, ha, hb⟩ := hi
    simp only [powerIter]
    split
    · -- both bits 1
      rename_i han
      have e : 2 * n * (2 * q + 1) = 2 * (2 * n * q) + 2 * n := by
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm (2 * n) 2 q]
      have hinv : PInv n A B (r + 1) (2 * (a - n)) (2 * (b - n)) := by
        refine ⟨by omega, by omega, by omega, 2 * q + 1, ?_, ?_⟩
        · rw [show r + 1 - 1 = r by omega, pow_pred_succ hr, ha, e]; omega
        · rw [show r + 1 - 1 = r by omega, pow_pred_succ hr, hb, e]; omega
      have := ih _ _ _ (ovf || decide (2 * (b - n) ≥ 2 ^ 63)) hinv (by omega)
      refine ⟨this.1, this.2.1, this.2.2.1, fun h => ?_⟩
      rcases this.2.2.2 h with h | h
      · simp at h
        rcases h with h | h
        · exact .inl h
        · exact .inr (by omega)
      · exact .inr h
    · rename_i han
      split
      · -- a bit 0, b bit 1: done
        rename_i hbn
        refine ⟨hr, ?_, ?_, ?_⟩
        · unfold gq; rw [ha, hb]
          rw [Nat.mul_add_div (by omega), Nat.mul_add_div (by omega),
            Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
        · unfold gq
          have e0 : 2 * n * (2 * q) = 2 * (2 * n * q) := Nat.mul_left_comm (2 * n) 2 q
          have e : 2 * n * (2 * q + 1) = 2 * (2 * n * q) + 2 * n := by
            rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm (2 * n) 2 q]
          have e1 : A * 2 ^ r = 2 * n * (2 * q) + 2 * a := by
            rw [pow_pred_succ hr, ha, e0]; omega
          have e2 : B * 2 ^ r = 2 * n * (2 * q + 1) + (2 * b - 2 * n) := by
            rw [pow_pred_succ hr, hb, e]; omega
          rw [e1, e2, Nat.mul_add_div (by omega), Nat.mul_add_div (by omega),
            Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
          omega
        · intro h; exact .inl h
      · -- both bits 0
        rename_i hbn
        have e0 : 2 * n * (2 * q) = 2 * (2 * n * q) := Nat.mul_left_comm (2 * n) 2 q
        have hinv : PInv n A B (r + 1) (2 * a) (2 * b) := by
          refine ⟨by omega, by omega, by omega, 2 * q, ?_, ?_⟩
          · rw [show r + 1 - 1 = r by omega, pow_pred_succ hr, ha, e0]; omega
          · rw [show r + 1 - 1 = r by omega, pow_pred_succ hr, hb, e0]; omega
        have := ih _ _ _ (ovf || decide (2 * b ≥ 2 ^ 63)) hinv (by omega)
        refine ⟨this.1, this.2.1, this.2.2.1, fun h => ?_⟩
        rcases this.2.2.2 h with h | h
        · simp at h
          rcases h with h | h
          · exact .inl h
          · exact .inr (by omega)
        · exact .inr h

theorem lt_of_div_eq {x y d : Nat} (hxy : x ≤ y) (h : x / d = y / d) (hd : 0 < d) : y - x < d := by
  have h1 := Nat.div_add_mod x d
  have h2 := Nat.div_add_mod y d
  have h3 := Nat.mod_lt x hd
  have h4 := Nat.mod_lt y hd
  rw [h] at h1
  omega

/-- `powerloop(s1, n1, n2, n)` is the first bit position `L >= 1` at which the
binary expansions of `(s1 + n1/2)/n` and `(s1 + n1 + n2/2)/n` differ
(`listsort.txt:382-393`); `2^L < 2n`; and when `n <= 2^62` no intermediate
value leaves `Py_ssize_t`. -/
theorem powerloop_spec (s1 n1 n2 n : Nat) (h1 : 0 < n1) (h2 : 0 < n2) (hn : s1 + n1 + n2 ≤ n) :
    1 ≤ powerloop s1 n1 n2 n ∧
      (∀ L', L' < powerloop s1 n1 n2 n → gq n L' (2 * s1 + n1) = gq n L' (2 * s1 + n1 + n1 + n2)) ∧
      gq n (powerloop s1 n1 n2 n) (2 * s1 + n1) < gq n (powerloop s1 n1 n2 n) (2 * s1 + n1 + n1 + n2) ∧
      2 ^ powerloop s1 n1 n2 n < 2 * n ∧
      (n ≤ 2 ^ 62 → (powerloopOvf s1 n1 n2 n).2 = false) := by
  have hinv : PInv n (2 * s1 + n1) (2 * s1 + n1 + n1 + n2) 1 (2 * s1 + n1) (2 * s1 + n1 + n1 + n2) :=
    ⟨by omega, by omega, by omega, 0, by simp, by simp⟩
  have H := powerIter_spec n (2 * s1 + n1) (2 * s1 + n1 + n1 + n2) (by omega) (n + 1) 1 _ _
    (decide (2 * s1 + n1 + n1 + n2 ≥ 2 ^ 63)) hinv (by omega)
  unfold powerloop powerloopOvf
  dsimp only
  generalize powerIter n (n + 1) 1 (2 * s1 + n1) (2 * s1 + n1 + n1 + n2)
    (decide (2 * s1 + n1 + n1 + n2 ≥ 2 ^ 63)) = res at H ⊢
  obtain ⟨hL, heq, hlt, hovf⟩ := H
  refine ⟨hL, fun L' hL' => gq_eq_of_le n (by omega) heq, hlt, ?_, ?_⟩
  · generalize res.1 = L at *
    -- (B - A) * 2^(L-1) < 2n
    have hle : (2 * s1 + n1) * 2 ^ (L - 1) ≤ (2 * s1 + n1 + n1 + n2) * 2 ^ (L - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have := lt_of_div_eq hle heq (by omega)
    rw [← Nat.sub_mul] at this
    have h2le : 2 * 2 ^ (L - 1) ≤ (2 * s1 + n1 + n1 + n2 - (2 * s1 + n1)) * 2 ^ (L - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have hp : 2 ^ L = 2 * 2 ^ (L - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    omega
  · intro h62
    cases hres : res.2
    · rfl
    · rcases hovf hres with h | h
      · simp at h; omega
      · omega

/-! ## Ghost runs and the stack invariant -/

/-- An original run found by the main loop: `(start, length)`. -/
abbrev Run := Nat × Nat

/-- Twice the run's midpoint, `2*s + len` (the `a` of `powerloop`). -/
def mid (r : Run) : Nat := 2 * r.1 + r.2

def Adj (r r' : Run) : Prop := r'.1 = r.1 + r.2

/-- The power of the boundary between adjacent runs `r` and `r'`. -/
def bp (N : Nat) (r r' : Run) : Nat := powerloop r.1 r.2 r'.2 N

/-- Every pair of neighbours satisfies `R`. -/
def Chn {β : Type} (R : β → β → Prop) : List β → Prop
  | a :: b :: l => R a b ∧ Chn R (b :: l)
  | _ => True

theorem chn_imp {β : Type} {R S : β → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ l : List β, Chn R l → Chn S l
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: l, hc => ⟨h a b hc.1, chn_imp h (b :: l) hc.2⟩

theorem chn_append {β : Type} {R : β → β → Prop} :
    ∀ (l1 l2 : List β) (x y : β), l1.getLast? = some x → l2.head? = some y →
      Chn R l1 → Chn R l2 → R x y → Chn R (l1 ++ l2)
  | [], _, _, _, h, _, _, _, _ => by simp at h
  | [a], b :: l2, x, y, hx, hy, _, h2, hr => by
    simp at hx hy; subst hx; subst hy; exact ⟨hr, h2⟩
  | a :: c :: l1, l2, x, y, hx, hy, h1, h2, hr =>
    ⟨h1.1, chn_append (c :: l1) l2 x y (by simpa [List.getLast?_cons_cons] using hx) hy h1.2 h2 hr⟩

theorem chn_mem {β : Type} {R : β → β → Prop} :
    ∀ (l : List β) (P : β → Prop), (∀ a b, R a b → P a → P b) → ∀ x, l.head? = some x → P x →
      Chn R l → ∀ y ∈ l, P y
  | [], _, _, _, _, _, _, _, h => by simp at h
  | [a], P, _, x, hx, hp, _, y, hy => by simp at hx hy; subst hx; subst hy; exact hp
  | a :: b :: l, P, hstep, x, hx, hp, hc, y, hy => by
    simp at hx; subst hx
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hp
    · exact chn_mem (b :: l) P hstep b rfl (hstep _ _ hc.1 hp) hc.2 y hy

/-- A block's ghost: adjacent non-empty runs inside `[0, N)`. -/
def Blk (N : Nat) (g : List Run) : Prop := Chn Adj g ∧ ∀ r ∈ g, 0 < r.2 ∧ r.1 + r.2 ≤ N

/-- `powerloop_spec` for adjacent runs, in terms of midpoints. -/
theorem bp_spec (N : Nat) (r r' : Run) (hadj : Adj r r') (h1 : 0 < r.2) (h2 : 0 < r'.2)
    (hN : r'.1 + r'.2 ≤ N) :
    1 ≤ bp N r r' ∧ (∀ L', L' < bp N r r' → gq N L' (mid r) = gq N L' (mid r')) ∧
      gq N (bp N r r') (mid r) < gq N (bp N r r') (mid r') ∧ 2 ^ bp N r r' < 2 * N := by
  unfold Adj at hadj
  have hm : mid r' = 2 * r.1 + r.2 + r.2 + r'.2 := by unfold mid; omega
  have := powerloop_spec r.1 r.2 r'.2 N h1 h2 (by omega)
  unfold bp mid at *
  rw [hm]
  exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩

/-- Inside a chain whose boundaries all have power `> L`, the first `L` bits of
the midpoints agree. -/
theorem chn_gq (N L : Nat) :
    ∀ (g : List Run) (f l : Run), Blk N g → Chn (fun r r' => L < bp N r r') g →
      g.head? = some f → g.getLast? = some l → gq N L (mid f) = gq N L (mid l)
  | [], _, _, _, _, h, _ => by simp at h
  | [a], f, l, _, _, hf, hl => by simp at hf hl; subst hf; subst hl; rfl
  | a :: b :: g, f, l, hb, hc, hf, hl => by
    simp at hf; subst hf
    have hb' : Blk N (b :: g) := ⟨hb.1.2, fun r hr => hb.2 r (List.mem_cons_of_mem _ hr)⟩
    have ih := chn_gq N L (b :: g) b l hb' hc.2 rfl (by simpa [List.getLast?_cons_cons] using hl)
    have hs := bp_spec N a b hb.1.1 (hb.2 a (by simp)).1 (hb.2 b (by simp)).1 (hb.2 b (by simp)).2
    rw [← ih]
    exact hs.2.1 L hc.1

/-- Two boundaries of equal power `L` with only boundaries of power `> L`
between them do not exist. -/
theorem no_equal_powers (N L : Nat) (r0 r1 r2 r3 : Run) (hL : 1 ≤ L)
    (h01 : ∀ L', L' < L → gq N L' (mid r0) = gq N L' (mid r1))
    (h01' : gq N L (mid r0) < gq N L (mid r1))
    (h23 : ∀ L', L' < L → gq N L' (mid r2) = gq N L' (mid r3))
    (h23' : gq N L (mid r2) < gq N L (mid r3))
    (h12 : gq N L (mid r1) = gq N L (mid r2)) : False := by
  have e1 := h01 (L - 1) (by omega)
  have e2 := h23 (L - 1) (by omega)
  rw [← gq_succ_div N (L - 1), ← gq_succ_div N (L - 1), show L - 1 + 1 = L by omega] at e1 e2
  omega

end PyLean.ListSort
