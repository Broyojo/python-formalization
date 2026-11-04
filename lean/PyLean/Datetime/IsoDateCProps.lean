import PyLean.Datetime.IsoC

/-!
C `is_digit`, `parse_digits` and `parse_isoformat_date` (Modules/_datetimemodule.c:923-1012,
CPython 3.15.2) on every byte string: when `parse_digits` fails, the value it computes, and
every branch and return code of `parse_isoformat_date`, the ISO week branch included.
-/

namespace PyLean.Datetime

open PyLean

/-- The C loop's accumulation, `*var *= 10; *var += tmp` (:936-937), over `n` bytes from `p`. -/
def hornerAt (b : List Nat) (p : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => hornerAt b (p + 1) n (acc * 10 + (byteAt b p - 48))

theorem hornerAt_add (b : List Nat) (p n acc : Nat) :
    hornerAt b p n acc = acc * 10 ^ n + hornerAt b p n 0 := by
  induction n generalizing p acc with
  | zero => simp [hornerAt]
  | succ n ih =>
    simp only [hornerAt]
    rw [ih (p + 1) (acc * 10 + (byteAt b p - 48)), ih (p + 1) (0 * 10 + (byteAt b p - 48))]
    rw [Nat.pow_succ]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 10 (10 ^ n)]
    omega

/-- `parse_digits(ptr, var, n)` (:928-940), with `*var` starting at 0 as every caller sets it:
it fails (`NULL`) exactly when one of the `n` bytes from `p` is not an ASCII digit
(`is_digit`'s unsigned test, :924, `tmp > 9` at :933), and otherwise returns the pointer
`p + n` and the value the C loop accumulates. A NUL terminator is not a digit, so it never reads
past the end. -/
def ParseDigitsSpec : Prop :=
  (∀ c : Nat, c < 256 → (isDigitC c = true ↔ 48 ≤ c ∧ c ≤ 57)) ∧
  ∀ (b : List Nat) (p n : Nat),
    (parseDigitsC b p n = none ↔ ∃ i, i < n ∧ isDigitC (byteAt b (p + i)) = false) ∧
    (∀ v q, parseDigitsC b p n = some (v, q) → q = p + n ∧ v = hornerAt b p n 0)

theorem parseDigitsC_some (b : List Nat) (p n v q : Nat) (h : parseDigitsC b p n = some (v, q)) :
    q = p + n ∧ v = hornerAt b p n 0 ∧ ∀ i, i < n → isDigitC (byteAt b (p + i)) = true := by
  induction n generalizing p v q with
  | zero =>
    simp only [parseDigitsC, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1 h2
    exact ⟨rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ n ih =>
    unfold parseDigitsC at h
    simp only at h
    split at h
    · rename_i hd
      split at h
      · rename_i v' q' hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        obtain ⟨e1, e2, e3⟩ := ih (p + 1) v' q' hr
        refine ⟨by omega, ?_, fun i hi => ?_⟩
        · rw [← h1, e2]
          simp only [hornerAt]
          rw [hornerAt_add b (p + 1) n (0 * 10 + (byteAt b p - 48))]
          simp only [Nat.zero_mul, Nat.zero_add]
        · cases i with
          | zero => simpa using hd
          | succ i =>
            have := e3 i (by omega)
            rwa [show p + 1 + i = p + (i + 1) by omega] at this
      · simp at h
    · simp at h

theorem parseDigitsC_none (b : List Nat) (p n : Nat) :
    parseDigitsC b p n = none ↔ ∃ i, i < n ∧ isDigitC (byteAt b (p + i)) = false := by
  induction n generalizing p with
  | zero => simp [parseDigitsC]
  | succ n ih =>
    unfold parseDigitsC
    simp only
    by_cases hd : isDigitC (byteAt b p) = true
    · rw [if_pos hd]
      constructor
      · intro h
        split at h
        · simp at h
        · rename_i hr
          obtain ⟨i, hi, hf⟩ := (ih (p + 1)).mp hr
          exact ⟨i + 1, by omega, by rwa [show p + (i + 1) = p + 1 + i by omega]⟩
      · intro ⟨i, hi, hf⟩
        cases i with
        | zero => simp [hd] at hf
        | succ i =>
          have : parseDigitsC b (p + 1) n = none :=
            (ih (p + 1)).mpr ⟨i, by omega, by rwa [show p + 1 + i = p + (i + 1) by omega]⟩
          rw [this]
    · rw [if_neg hd]
      exact ⟨fun _ => ⟨0, by omega, by simpa using hd⟩, fun _ => rfl⟩

theorem parseDigitsSpec_proven : ParseDigitsSpec := by
  refine ⟨fun c _ => ?_, fun b p n => ⟨parseDigitsC_none b p n, fun v q h => ?_⟩⟩
  · unfold isDigitC; simp
  · obtain ⟨h1, h2, -⟩ := parseDigitsC_some b p n v q h
    exact ⟨h1, h2⟩

/-! ### `parse_isoformat_date` -/

/-- The ASCII digit byte of `n < 10`. -/
def digB (n : Nat) : Nat := 48 + n

/-- The four digit bytes of a year `Y < 10000`, and the two of a week `W < 100`. -/
def enc4 (Y : Nat) : List Nat := [digB (Y / 1000), digB (Y / 100 % 10), digB (Y / 10 % 10), digB (Y % 10)]
def enc2 (W : Nat) : List Nat := [digB (W / 10), digB (W % 10)]

/-- `parse_isoformat_date(dtstr, len, ...)` (:943-1012) on every byte string: the year must
be four ASCII digits (else `-1`, :956-959); a `W` after the year (and an optional `-`) starts
the ISO week branch (:966-995): two week digits (else `-3`), then, if bytes remain within
`len`, the separator (`-2` when the year had one and this is not `-`) and one day digit (else
`-4`), the day defaulting to 1 when nothing remains, and `iso_to_ymd`'s code `rv` becomes
`-3 + rv` (`-7` year, `-5` week, `-6` weekday); otherwise two month digits, the matching
separator (`-2`) and two day digits (`-1` for a missing digit). Stated for the four week
forms `YYYY-Www-D`, `YYYYWwwD`, `YYYY-Www` and `YYYYWww` with any digits, the separator
mismatches of both branches, and the digit failures. `len` is the UTF-8 length
`date.fromisoformat` passes. -/
def ParseIsoDateCSpec : Prop :=
  (∀ (b : List Nat) (len : Nat), (∃ i, i < 4 ∧ isDigitC (byteAt b i) = false) →
    parseIsoDateC b len = .error (-1)) ∧
  ∀ (Y W D : Nat), Y < 10000 → W < 100 → D < 10 →
    let rv := fun (r : Except Int (Int × Int × Int)) => match r with
      | .error e => Except.error (-3 + e) | .ok v => .ok v
    parseIsoDateC (enc4 Y ++ [45, 87] ++ enc2 W ++ [45, digB D]) 10 = rv (isoToYmdC Y W D) ∧
    parseIsoDateC (enc4 Y ++ [87] ++ enc2 W ++ [digB D]) 8 = rv (isoToYmdC Y W D) ∧
    parseIsoDateC (enc4 Y ++ [45, 87] ++ enc2 W) 8 = rv (isoToYmdC Y W 1) ∧
    parseIsoDateC (enc4 Y ++ [87] ++ enc2 W) 7 = rv (isoToYmdC Y W 1) ∧
    (∀ c, c ≠ 45 → parseIsoDateC (enc4 Y ++ [45, 87] ++ enc2 W ++ [c, digB D]) 10 = .error (-2)) ∧
    (∀ c, isDigitC c = false → parseIsoDateC (enc4 Y ++ [45, 87] ++ enc2 W ++ [45, c]) 10 = .error (-4)) ∧
    (∀ c, isDigitC c = false → parseIsoDateC (enc4 Y ++ [45, 87, c, digB 0, 45, digB D]) 10 = .error (-3)) ∧
    (∀ c, c ≠ 45 → c ≠ 87 → parseIsoDateC (enc4 Y ++ [45] ++ enc2 W ++ [c] ++ enc2 D) 10 = .error (-2)) ∧
    (∀ M : Nat, M < 100 → D < 10 → parseIsoDateC (enc4 Y ++ [45] ++ enc2 M ++ [45] ++ enc2 D) 10 = .ok (Y, M, D)) ∧
    (∀ M : Nat, M < 100 → parseIsoDateC (enc4 Y ++ enc2 M ++ enc2 D) 8 = .ok (Y, M, D))

theorem digB_isDigit (n : Nat) (h : n < 10) : isDigitC (digB n) = true := by
  unfold isDigitC digB; simp; omega

theorem dig_facts (b : List Nat) (p x : Nat) (hx : x < 10) (h0 : byteAt b p = digB x) :
    isDigitC (byteAt b p) = true ∧ byteAt b p - 48 = x := by
  rw [h0]; exact ⟨digB_isDigit x hx, by unfold digB; omega⟩

theorem pd1 (b : List Nat) (p x : Nat) (hx : x < 10) (h0 : byteAt b p = digB x) :
    parseDigitsC b p 1 = some (x, p + 1) := by
  obtain ⟨e0, v0⟩ := dig_facts b p x hx h0
  simp only [parseDigitsC, e0, v0, ite_true, Nat.pow_zero, Nat.mul_one, Nat.add_zero]

theorem pd2 (b : List Nat) (p W : Nat) (hW : W < 100) (h0 : byteAt b p = digB (W / 10))
    (h1 : byteAt b (p + 1) = digB (W % 10)) : parseDigitsC b p 2 = some (W, p + 2) := by
  have a0 := digB_isDigit (W / 10) (by omega)
  have a1 := digB_isDigit (W % 10) (by omega)
  unfold digB at a0 a1 h0 h1
  simp only [parseDigitsC, h0, h1, a0, a1, ite_true, Nat.reducePow, Option.some.injEq, Prod.mk.injEq,
    Nat.add_sub_cancel_left]
  clear h0 h1 a0 a1
  constructor <;> first | trivial | omega

theorem pd4 (b : List Nat) (Y : Nat) (hY : Y < 10000) (h0 : byteAt b 0 = digB (Y / 1000))
    (h1 : byteAt b 1 = digB (Y / 100 % 10)) (h2 : byteAt b 2 = digB (Y / 10 % 10))
    (h3 : byteAt b 3 = digB (Y % 10)) : parseDigitsC b 0 4 = some (Y, 4) := by
  have a0 := digB_isDigit (Y / 1000) (by omega)
  have a1 := digB_isDigit (Y / 100 % 10) (by omega)
  have a2 := digB_isDigit (Y / 10 % 10) (by omega)
  have a3 := digB_isDigit (Y % 10) (by omega)
  unfold digB at a0 a1 a2 a3 h0 h1 h2 h3
  simp only [parseDigitsC, Nat.zero_add, Nat.reduceAdd, h0, h1, h2, h3, a0, a1, a2, a3, ite_true,
    Nat.reducePow, Option.some.injEq, Prod.mk.injEq, Nat.add_sub_cancel_left]
  clear h0 h1 h2 h3 a0 a1 a2 a3
  constructor <;> first | trivial | omega

theorem pdNone1 (b : List Nat) (p : Nat) (h : isDigitC (byteAt b p) = false) : parseDigitsC b p 1 = none :=
  (parseDigitsC_none b p 1).mpr ⟨0, by omega, by simpa using h⟩

theorem pdNone2 (b : List Nat) (p : Nat) (h : isDigitC (byteAt b p) = false) : parseDigitsC b p 2 = none :=
  (parseDigitsC_none b p 2).mpr ⟨0, by omega, by simpa using h⟩

theorem digB_ne (n c : Nat) (h : n < 10) (hc : c = 45 ∨ c = 87) : digB n ≠ c := by
  unfold digB; omega

theorem parseIsoDateCSpec_proven : ParseIsoDateCSpec := by
  refine ⟨fun b len ⟨i, hi, hf⟩ => ?_, fun Y W D hY hW hD => ?_⟩
  · unfold parseIsoDateC
    rw [(parseDigitsC_none b 0 4).mpr ⟨i, hi, by simpa using hf⟩]
  · have hy : ∀ r : List Nat, parseDigitsC (enc4 Y ++ r) 0 4 = some (Y, 4) := fun r =>
      pd4 _ Y hY rfl rfl rfl rfl
    have w45 := digB_ne (W / 10) 45 (by omega) (Or.inl rfl)
    have w87 := digB_ne (W / 10) 87 (by omega) (Or.inr rfl)
    refine ⟨?_, ?_, ?_, ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc1 hc2 => ?_,
      fun M hM hD' => ?_, fun M hM => ?_⟩
    · unfold parseIsoDateC
      simp only [List.append_assoc]
      rw [hy]
      simp only [show byteAt (enc4 Y ++ ([45, 87] ++ (enc2 W ++ [45, digB D]))) 4 = 45 from rfl,
        show byteAt (enc4 Y ++ ([45, 87] ++ (enc2 W ++ [45, digB D]))) 5 = 87 from rfl, ite_true,
        Nat.reduceAdd, pd2 (enc4 Y ++ ([45, 87] ++ (enc2 W ++ [45, digB D]))) 6 W hW rfl rfl,
        show byteAt (enc4 Y ++ ([45, 87] ++ (enc2 W ++ [45, digB D]))) 8 = 45 from rfl,
        pd1 (enc4 Y ++ ([45, 87] ++ (enc2 W ++ [45, digB D]))) 9 D hD rfl]
      rfl
    · unfold parseIsoDateC
      simp only [List.append_assoc]
      rw [hy]
      simp only [show byteAt (enc4 Y ++ ([87] ++ (enc2 W ++ [digB D]))) 4 = 87 from rfl,
        Nat.reduceEqDiff, ite_true, ite_false, Nat.reduceAdd,
        pd2 (enc4 Y ++ ([87] ++ (enc2 W ++ [digB D]))) 5 W hW rfl rfl, false_and,
        pd1 (enc4 Y ++ ([87] ++ (enc2 W ++ [digB D]))) 7 D hD rfl, Nat.reduceLT]
      rfl
    · unfold parseIsoDateC
      simp only [List.append_assoc]
      rw [hy]
      simp only [show byteAt (enc4 Y ++ ([45, 87] ++ enc2 W)) 4 = 45 from rfl,
        show byteAt (enc4 Y ++ ([45, 87] ++ enc2 W)) 5 = 87 from rfl, ite_true,
        Nat.reduceAdd, pd2 (enc4 Y ++ ([45, 87] ++ enc2 W)) 6 W hW rfl rfl, Nat.lt_irrefl, ite_false]
      rfl
    · unfold parseIsoDateC
      simp only [List.append_assoc]
      rw [hy]
      simp only [show byteAt (enc4 Y ++ ([87] ++ enc2 W)) 4 = 87 from rfl, Nat.reduceEqDiff, ite_false,
        ite_true, Nat.reduceAdd, pd2 (enc4 Y ++ ([87] ++ enc2 W)) 5 W hW rfl rfl, Nat.lt_irrefl]
      rfl
    · unfold parseIsoDateC
      simp only [List.append_assoc]
      rw [hy]
      simp only [show byteAt (enc4 Y ++ ([45, 87] ++ (enc2 W ++ [c, digB D]))) 4 = 45 from rfl,
        show byteAt (enc4 Y ++ ([45, 87] ++ (enc2 W ++ [c, digB D]))) 5 = 87 from rfl, ite_true,
        Nat.reduceAdd, pd2 (enc4 Y ++ ([45, 87] ++ (enc2 W ++ [c, digB D]))) 6 W hW rfl rfl,
        show byteAt (enc4 Y ++ ([45, 87] ++ (enc2 W ++ [c, digB D]))) 8 = c from rfl, Nat.reduceLT,
        hc, ne_eq, not_false_eq_true, and_self]
    · unfold parseIsoDateC
      simp only [List.append_assoc]
      rw [hy]
      simp only [show byteAt (enc4 Y ++ ([45, 87] ++ (enc2 W ++ [45, c]))) 4 = 45 from rfl,
        show byteAt (enc4 Y ++ ([45, 87] ++ (enc2 W ++ [45, c]))) 5 = 87 from rfl, ite_true,
        Nat.reduceAdd, pd2 (enc4 Y ++ ([45, 87] ++ (enc2 W ++ [45, c]))) 6 W hW rfl rfl,
        show byteAt (enc4 Y ++ ([45, 87] ++ (enc2 W ++ [45, c]))) 8 = 45 from rfl, Nat.reduceLT,
        ne_eq, not_true_eq_false, and_false, ite_false,
        pdNone1 (enc4 Y ++ ([45, 87] ++ (enc2 W ++ [45, c]))) 9 (by rw [show byteAt (enc4 Y ++ ([45, 87] ++ (enc2 W ++ [45, c]))) 9 = c from rfl]; exact hc)]
    · unfold parseIsoDateC
      rw [hy]
      simp only [show byteAt (enc4 Y ++ [45, 87, c, digB 0, 45, digB D]) 4 = 45 from rfl,
        show byteAt (enc4 Y ++ [45, 87, c, digB 0, 45, digB D]) 5 = 87 from rfl, ite_true,
        Nat.reduceAdd, pdNone2 (enc4 Y ++ [45, 87, c, digB 0, 45, digB D]) 6 (by rw [show byteAt (enc4 Y ++ [45, 87, c, digB 0, 45, digB D]) 6 = c from rfl]; exact hc)]
    · unfold parseIsoDateC
      simp only [List.append_assoc]
      rw [hy]
      simp only [show byteAt (enc4 Y ++ ([45] ++ (enc2 W ++ ([c] ++ enc2 D)))) 4 = 45 from rfl,
        show byteAt (enc4 Y ++ ([45] ++ (enc2 W ++ ([c] ++ enc2 D)))) 5 = digB (W / 10) from rfl, ite_true,
        Nat.reduceAdd, w87, ite_false, pd2 (enc4 Y ++ ([45] ++ (enc2 W ++ ([c] ++ enc2 D)))) 5 W hW rfl rfl,
        show byteAt (enc4 Y ++ ([45] ++ (enc2 W ++ ([c] ++ enc2 D)))) 7 = c from rfl,
        hc1, ne_eq, not_false_eq_true, and_self]
    · have m87 := digB_ne (M / 10) 87 (by omega) (Or.inr rfl)
      unfold parseIsoDateC
      simp only [List.append_assoc]
      rw [hy]
      simp only [show byteAt (enc4 Y ++ ([45] ++ (enc2 M ++ ([45] ++ enc2 D)))) 4 = 45 from rfl,
        show byteAt (enc4 Y ++ ([45] ++ (enc2 M ++ ([45] ++ enc2 D)))) 5 = digB (M / 10) from rfl, ite_true,
        Nat.reduceAdd, m87, ite_false, pd2 (enc4 Y ++ ([45] ++ (enc2 M ++ ([45] ++ enc2 D)))) 5 M hM rfl rfl,
        show byteAt (enc4 Y ++ ([45] ++ (enc2 M ++ ([45] ++ enc2 D)))) 7 = 45 from rfl,
        ne_eq, not_true_eq_false, and_false,
        pd2 (enc4 Y ++ ([45] ++ (enc2 M ++ ([45] ++ enc2 D)))) 8 D (by omega) rfl rfl]
    · have m87 := digB_ne (M / 10) 87 (by omega) (Or.inr rfl)
      have m45 := digB_ne (M / 10) 45 (by omega) (Or.inl rfl)
      unfold parseIsoDateC
      simp only [List.append_assoc]
      rw [hy]
      simp only [show byteAt (enc4 Y ++ (enc2 M ++ enc2 D)) 4 = digB (M / 10) from rfl, m45, m87, ite_false,
        pd2 (enc4 Y ++ (enc2 M ++ enc2 D)) 4 M hM rfl rfl, false_and,
        pd2 (enc4 Y ++ (enc2 M ++ enc2 D)) 6 D (by omega) rfl rfl, Nat.reduceAdd]

end PyLean.Datetime
