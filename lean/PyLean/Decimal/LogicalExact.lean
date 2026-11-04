import PyLean.Decimal.DivExact

/-!
`logical_and`, `logical_or`, `logical_xor` and `logical_invert` digit by digit: the operands'
decimal digits, all 0 or 1, combined position by position over the low `prec` positions.
-/

namespace PyLean.Decimal

open PyLean

/-! ## Digits of a number, least significant first -/

/-- The low `k` decimal digits of `x`, least significant first. -/
def digitsRev : Nat → Nat → List Char
  | 0, _ => []
  | k + 1, x => Nat.digitChar (x % 10) :: digitsRev k (x / 10)

theorem digitsRev_length : ∀ k x, (digitsRev k x).length = k
  | 0, _ => rfl
  | k + 1, x => by simp [digitsRev, digitsRev_length k (x / 10)]

theorem digitsRev_append : ∀ k j x, digitsRev k x ++ digitsRev j (x / 10 ^ k) = digitsRev (k + j) x
  | 0, j, x => by simp [digitsRev]
  | k + 1, j, x => by
    have := digitsRev_append k j (x / 10)
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ'] at this
    rw [show k + 1 + j = (k + j) + 1 by omega]
    simp only [digitsRev, List.cons_append, this]

theorem digitsRev_zero : ∀ j, digitsRev j 0 = List.replicate j '0'
  | 0 => rfl
  | j + 1 => by simp [digitsRev, digitsRev_zero j, List.replicate_succ]

theorem toDigits_reverse : ∀ x, (Nat.toDigits 10 x).reverse = digitsRev (numDigits x) x := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    by_cases hx : x < 10
    · have h1 : Nat.toDigits 10 x = [Nat.digitChar x] := Nat.toDigits_of_lt_base hx
      have h2 : numDigits x = 1 := by
        show (Nat.toDigits 10 x).length = 1
        rw [h1]; rfl
      rw [h1, h2]
      simp [digitsRev, Nat.mod_eq_of_lt hx]
    · have hpos : 0 < x / 10 := by omega
      have happ := Nat.toDigits_append_toDigits (b := 10) (by decide) hpos (Nat.mod_lt x (by decide))
      rw [Nat.div_add_mod] at happ
      have hd : Nat.toDigits 10 (x % 10) = [Nat.digitChar (x % 10)] := Nat.toDigits_of_lt_base (Nat.mod_lt x (by decide))
      rw [hd] at happ
      have hn : numDigits x = numDigits (x / 10) + 1 := by
        show (Nat.toDigits 10 x).length = (Nat.toDigits 10 (x / 10)).length + 1
        rw [← happ]; simp
      rw [← happ, hn, List.reverse_append, ih (x / 10) (by omega)]
      rfl

theorem div_pow_numDigits (x : Nat) : x / 10 ^ numDigits x = 0 :=
  Nat.div_eq_of_lt (lt_pow_numDigits x)

/-- `_fill_logical` of the digit string of `x` (_pydecimal.py:3432-3443) is its low `prec` digits. -/
theorem fill_reverse (prec x : Nat) :
    (fillDigits prec (Nat.toDigits 10 x)).reverse = digitsRev prec x := by
  have hl : (Nat.toDigits 10 x).length = numDigits x := rfl
  unfold fillDigits
  rw [hl]
  split
  · rename_i h
    rw [List.reverse_append, toDigits_reverse, List.reverse_replicate]
    have := digitsRev_append (numDigits x) (prec - numDigits x) x
    rw [div_pow_numDigits, digitsRev_zero, show numDigits x + (prec - numDigits x) = prec by omega] at this
    exact this
  · split
    · rename_i h1 h2
      rw [List.reverse_drop, toDigits_reverse, hl]
      rw [show numDigits x - (numDigits x - prec) = prec by omega]
      have := digitsRev_append prec (numDigits x - prec) x
      rw [show prec + (numDigits x - prec) = numDigits x by omega] at this
      rw [← this, List.take_left' (digitsRev_length prec x)]
    · rename_i h1 h2
      rw [toDigits_reverse, show numDigits x = prec by omega]

theorem fillDigits_length (prec : Nat) (L : List Char) : (fillDigits prec L).length = prec := by
  unfold fillDigits
  split
  · simp; omega
  · split
    · simp; omega
    · omega

/-! ## The digit-wise operation -/

/-- `f` applied to the low `k` digits of `x` and `y`, a digit being 1 exactly when it is `1`. -/
def lspec (f : Bool → Bool → Bool) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | k + 1, x, y => (if f (x % 10 = 1) (y % 10 = 1) then 1 else 0) + 10 * lspec f k (x / 10) (y / 10)

/-- The value of `f` applied to two digit strings, read from their least significant ends. -/
def rspec (f : Bool → Bool → Bool) : List Char → List Char → Nat
  | a :: as, b :: bs => (if f (a == '1') (b == '1') then 1 else 0) + 10 * rspec f as bs
  | _, _ => 0

theorem digitVal_bit (b : Bool) : (digitVal (if b then '1' else '0')).getD 0 = if b then 1 else 0 := by
  cases b <;> rfl

theorem digitsValue_concat (L : List Char) (c : Char) :
    digitsValue (L ++ [c]) = digitsValue L * 10 + (digitVal c).getD 0 := by
  simp [digitsValue, List.foldl_append]

theorem digitOp_value (f : Bool → Bool → Bool) : ∀ (n : Nat) (A B : List Char), A.length = n → B.length = n →
    digitsValue (digitOp f A B) = rspec f A.reverse B.reverse := by
  intro n
  induction n with
  | zero =>
    intro A B ha hb
    rw [List.eq_nil_of_length_eq_zero ha, List.eq_nil_of_length_eq_zero hb]; rfl
  | succ n ih =>
    intro A B ha hb
    rcases List.eq_nil_or_concat A with hA | ⟨A', a, rfl⟩
    · subst hA; simp at ha
    rcases List.eq_nil_or_concat B with hB | ⟨B', b, rfl⟩
    · subst hB; simp at hb
    simp only [List.concat_eq_append, List.length_append, List.length_singleton] at ha hb ⊢
    have hz : (A' ++ [a]).zip (B' ++ [b]) = A'.zip B' ++ [(a, b)] := by
      rw [List.zip_append (by omega)]; rfl
    simp only [digitOp] at ih ⊢
    rw [hz, List.map_append, List.map_cons, List.map_nil, digitsValue_concat, ih A' B' (by omega) (by omega)]
    simp only [List.map_cons, List.map_nil, List.concat_eq_append, List.reverse_append, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.singleton_append, rspec]
    rw [show (if f (a == '1') (b == '1') = true then '1' else '0') =
      (if f (a == '1') (b == '1') then '1' else '0') from rfl, digitVal_bit]
    omega

theorem digitChar_eq_one (d : Nat) (hd : d < 10) : (Nat.digitChar d == '1') = decide (d = 1) := by
  have : ∀ d, d < 10 → (Nat.digitChar d == '1') = decide (d = 1) := by decide
  exact this d hd

theorem rspec_digitsRev (f : Bool → Bool → Bool) : ∀ k x y,
    rspec f (digitsRev k x) (digitsRev k y) = lspec f k x y
  | 0, _, _ => rfl
  | k + 1, x, y => by
    simp only [digitsRev, rspec, lspec, digitChar_eq_one _ (Nat.mod_lt x (by decide)),
      digitChar_eq_one _ (Nat.mod_lt y (by decide)), rspec_digitsRev f k (x / 10) (y / 10)]

/-! ## `_islogical` -/

/-- A logical operand (_pydecimal.py:3418-3430, the docstring): a finite number with sign 0,
exponent 0 and every decimal digit 0 or 1. -/
def IsLogical (d : Dec) : Prop := ∃ x, d = .fin false x 0 ∧ ∀ i, x / 10 ^ i % 10 ≤ 1

theorem mem_digitsRev : ∀ (k x : Nat) (c : Char), c ∈ digitsRev k x ↔ ∃ i < k, c = Nat.digitChar (x / 10 ^ i % 10)
  | 0, x, c => by simp [digitsRev]
  | k + 1, x, c => by
    simp only [digitsRev, List.mem_cons, mem_digitsRev k (x / 10) c]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨0, by omega, by simpa using h⟩
      · refine ⟨i + 1, by omega, ?_⟩
        rw [h, Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
    · rintro ⟨i, hi, h⟩
      cases i with
      | zero => left; simpa using h
      | succ i =>
        right
        refine ⟨i, by omega, ?_⟩
        rw [h, Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

theorem digitChar_bin (d : Nat) (hd : d < 10) :
    ((Nat.digitChar d == '0' || Nat.digitChar d == '1') = true) ↔ d ≤ 1 := by
  have : ∀ d, d < 10 → (((Nat.digitChar d == '0' || Nat.digitChar d == '1') = true) ↔ d ≤ 1) := by decide
  exact this d hd

theorem islogical_iff (x : Nat) : islogical (.fin false x 0) = true ↔ ∀ i, x / 10 ^ i % 10 ≤ 1 := by
  simp only [islogical, List.all_eq_true]
  constructor
  · intro h i
    by_cases hi : i < numDigits x
    · have hm : Nat.digitChar (x / 10 ^ i % 10) ∈ Nat.toDigits 10 x := by
        rw [← List.mem_reverse, toDigits_reverse, mem_digitsRev]
        exact ⟨i, hi, rfl⟩
      exact (digitChar_bin _ (Nat.mod_lt _ (by decide))).mp (h _ hm)
    · have : x / 10 ^ i = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (lt_pow_numDigits x)
        (Nat.pow_le_pow_right (by decide) (by omega)))
      rw [this]; decide
  · intro h c hc
    rw [← List.mem_reverse, toDigits_reverse, mem_digitsRev] at hc
    obtain ⟨i, _, rfl⟩ := hc
    exact (digitChar_bin _ (Nat.mod_lt _ (by decide))).mpr (h i)

theorem isLogical_iff (d : Dec) : IsLogical d ↔ islogical d = true := by
  constructor
  · rintro ⟨x, rfl, h⟩
    exact (islogical_iff x).mpr h
  · intro h
    rcases d with ⟨s, x, e⟩ | _ | _
    · cases s
      · by_cases he : e = 0
        · subst he
          exact ⟨x, rfl, (islogical_iff x).mp h⟩
        · simp [islogical, he] at h
      · simp [islogical] at h
    · simp [islogical] at h
    · simp [islogical] at h

/-! ## The operations, exactly -/

open Classical in
theorem logicalOp_run (f : Bool → Bool → Bool) (c : Ctx) (fl : List Signal) (a b : Dec) :
    (logicalOp f c a b).run fl =
      if IsLogical a ∧ IsLogical b then
        match a, b with
        | .fin _ x _, .fin _ y _ => .ok (.fin false (lspec f c.prec x y) 0, fl)
        | _, _ => .ok (a, fl)
      else afterSig c .invalidOperation fl nanD := by
  by_cases h : IsLogical a ∧ IsLogical b
  · rw [if_pos h]
    obtain ⟨⟨x, rfl, hx⟩, ⟨y, rfl, hy⟩⟩ := h
    have h1 := (islogical_iff x).mpr hx
    have h2 := (islogical_iff y).mpr hy
    simp only [logicalOp, h1, h2, Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte, fillLogical]
    show Except.ok (Dec.fin false (digitsValue (digitOp f _ _)) 0, fl) = _
    rw [digitOp_value f c.prec _ _ (fillDigits_length _ _) (fillDigits_length _ _), fill_reverse, fill_reverse,
      rspec_digitsRev]
  · rw [if_neg h]
    have hn : (!islogical a || !islogical b) = true := by
      by_cases ha : islogical a = true
      · have : ¬ islogical b = true := fun hb => h ⟨(isLogical_iff a).mpr ha, (isLogical_iff b).mpr hb⟩
        simp [ha, this]
      · simp [ha]
    simp only [logicalOp, hn, ↓reduceIte]
    simpa [nanD] using invalid_run c fl

/-- `logical_and`, `logical_or`, `logical_xor` (_pydecimal.py:3445-3513) and `logical_invert`
(:3465-3473), for every context and operands: two logical operands (`IsLogical`: sign 0, exponent
0, every digit 0 or 1) give the logical number whose digit at each of the low `prec` positions is
the and / or / exclusive or of the operands' digits there (`lspec`; digits beyond `prec` are cut,
missing ones are 0), and `logical_invert` the one whose low `prec` digits are the inverted digits;
any other operand pair is InvalidOperation with a NaN. -/
def LogicalExact : Prop :=
  ∀ (c : Ctx) (fl : List Signal),
    (∀ x y : Nat, IsLogical (.fin false x 0) → IsLogical (.fin false y 0) →
      (logicalAnd c (.fin false x 0) (.fin false y 0)).run fl = .ok (.fin false (lspec (· && ·) c.prec x y) 0, fl) ∧
      (logicalOr c (.fin false x 0) (.fin false y 0)).run fl = .ok (.fin false (lspec (· || ·) c.prec x y) 0, fl) ∧
      (logicalXor c (.fin false x 0) (.fin false y 0)).run fl =
        .ok (.fin false (lspec (fun p q => p != q) c.prec x y) 0, fl)) ∧
    (∀ a b : Dec, ¬ (IsLogical a ∧ IsLogical b) →
      (logicalAnd c a b).run fl = afterSig c .invalidOperation fl nanD ∧
      (logicalOr c a b).run fl = afterSig c .invalidOperation fl nanD ∧
      (logicalXor c a b).run fl = afterSig c .invalidOperation fl nanD) ∧
    (∀ x : Nat, IsLogical (.fin false x 0) →
      (logicalInvert c (.fin false x 0)).run fl = .ok (.fin false (lspec (fun p _ => !p) c.prec x 0) 0, fl)) ∧
    (∀ a : Dec, ¬ IsLogical a → (logicalInvert c a).run fl = afterSig c .invalidOperation fl nanD)

/-- The number of `k` ones, `'1'*k` (_pydecimal.py:3472). -/
theorem ones_value : ∀ k, digitsValue (List.replicate k '1') % 10 = (if k = 0 then 0 else 1) ∧
    (k ≠ 0 → digitsValue (List.replicate k '1') / 10 = digitsValue (List.replicate (k - 1) '1'))
  | 0 => ⟨rfl, fun h => absurd rfl h⟩
  | k + 1 => by
    rw [List.replicate_succ', digitsValue_concat]
    refine ⟨by simp; rfl, fun _ => ?_⟩
    show (digitsValue (List.replicate k '1') * 10 + 1) / 10 = _
    simp only [Nat.add_sub_cancel]
    omega

theorem ones_digits : ∀ k i, digitsValue (List.replicate k '1') / 10 ^ i % 10 = (if i < k then 1 else 0)
  | 0, i => by simp [digitsValue]
  | k + 1, 0 => by simpa using (ones_value (k + 1)).1
  | k + 1, i + 1 => by
    rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul, (ones_value (k + 1)).2 (by omega),
      Nat.add_sub_cancel, ones_digits k i]
    simp

theorem lspec_xor_ones : ∀ k x, lspec (fun p q => p != q) k x (digitsValue (List.replicate k '1')) =
    lspec (fun p _ => !p) k x 0
  | 0, _ => rfl
  | k + 1, x => by
    have h1 := (ones_value (k + 1)).1
    have h2 := (ones_value (k + 1)).2 (by omega)
    simp only [Nat.add_sub_cancel] at h2
    simp only [lspec, h1, h2, lspec_xor_ones k (x / 10)]
    simp

theorem logicalExact_proven : LogicalExact := by
  intro c fl
  have hones : IsLogical (.fin false (digitsValue (List.replicate c.prec '1')) 0) := by
    unfold IsLogical
    exact ⟨_, rfl, fun i => by rw [ones_digits]; split <;> omega⟩
  refine ⟨fun x y hx hy => ?_, fun a b h => ?_, fun x hx => ?_, fun a ha => ?_⟩
  · refine ⟨?_, ?_, ?_⟩ <;>
      (simp only [logicalAnd, logicalOr, logicalXor]
       rw [logicalOp_run, if_pos ⟨hx, hy⟩])
  · refine ⟨?_, ?_, ?_⟩ <;>
      (simp only [logicalAnd, logicalOr, logicalXor]
       rw [logicalOp_run, if_neg h])
  · simp only [logicalInvert, logicalXor]
    rw [logicalOp_run, if_pos ⟨hx, hones⟩]
    simp only [lspec_xor_ones]
  · simp only [logicalInvert, logicalXor]
    rw [logicalOp_run, if_neg (fun h => ha h.1)]

end PyLean.Decimal
