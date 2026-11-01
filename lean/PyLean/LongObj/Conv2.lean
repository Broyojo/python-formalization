import PyLean.Registry
import PyLean.LongObj.Methods
import PyLean.MathInt.Bytes

/-!
The conversions built on `_PyLong_AsByteArray`: `PyLong_AsLongLong`,
`PyLong_AsUnsignedLongLong`, `PyLong_AsVoidPtr`, `PyLong_AsNativeBytes` and the
fixed-width `PyLong_As{Int,UInt}{32,64}`, plus `_PyLong_FromDigits`.

`PyLong_AsNativeBytes` calls `_PyLong_AsByteArray` with `with_exceptions = 0`, which fills
the buffer with the low bytes of the two's complement value. The buffer is modelled by
that value; `MathInt.asByteArray` models the raising form.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt PyLean.Registry

/-- `PyLong_AsLongLong(vv)`, longobject.c:1505-1544, for an exact int. -/
def asLongLong (v : Long) : Py Int :=
  if v.isCompact = true then .ok v.medium
  else
    match asByteArray v.toInt 8 true with
    | .ok bs => .ok (s64of (bytesVal bs))
    | .error e => .error e

/-- `PyLong_AsUnsignedLongLong(vv)`, longobject.c:1550-1591, for an exact int. -/
def asUnsignedLongLong (v : Long) : Py Nat :=
  if !v.neg && v.isCompact then .ok v.medium.toNat
  else
    match asByteArray v.toInt 8 false with
    | .ok bs => .ok (bytesVal bs)
    | .error e => .error e

/-- `PyLong_AsVoidPtr(vv)`, longobject.c:1447-1477, as the pointer's bit pattern. -/
def asVoidPtr (v : Long) : Py Nat :=
  if v.neg then
    match asLong v with
    | .ok x => .ok (x % 2 ^ 64).toNat
    | .error e => .error e
  else asUnsignedLong v

/-- `_PyLong_FromDigits(negative, digit_count, digits)`, longobject.c:201-214. -/
def fromDigits (negative : Bool) (ds : List Nat) : Py Long :=
  if ds.length = 0 then .ok ⟨false, []⟩
  else
    match longAlloc ds.length with
    | .error e => .error e
    | .ok _ => .ok ⟨negative, ds⟩

/-- `_fits_in_n_bits(v, n)`, longobject.c:1180-1189. -/
def fitsNBits (v : Int) (n : Nat) : Bool :=
  n ≥ 64 || (let e := v / 2 ^ (n - 1); e == 0 || e == -1)

/-- The result of `PyLong_AsNativeBytes(vv, buffer, n, flags)`, longobject.c:1248-1378,
for `n` bytes. `ub` is `Py_ASNATIVEBYTES_UNSIGNED_BUFFER`. The edge-case tests at :1349-1359
and :1369 are stated on the buffer's value. -/
def asNativeRes (v : Long) (n : Nat) (ub : Bool) : Nat :=
  if v.isCompact = true then
    let cv := v.medium
    if n = 0 then 8
    else if n ≤ 8 then
      if fitsNBits cv (n * 8) then n
      else if cv > 0 ∧ fitsNBits cv (n * 8 + 1) then (if ub then n else n + 1)
      else 8
    else 8
  else
    let nb := numBits v
    let res := nb / 8 + 1
    if n > 0 ∧ res = n + 1 ∧ nb % 8 = 0 then
      let m := (v.toInt % 2 ^ (8 * n)).toNat
      if v.neg then (if m = 2 ^ (8 * n - 1) then n else res)
      else if 2 ^ (8 * n - 1) ≤ m then (if ub then n else n + 1) else res
    else res

/-- What the caller may conclude from a result of at most `n`: the value is held by `n`
bytes, as signed, or as unsigned when the caller asked for that. -/
def NativeFit (a : Int) (n : Nat) (ub : Bool) : Prop :=
  (-(2 ^ (8 * n - 1) : Int) ≤ a ∧ a < 2 ^ (8 * n - 1)) ∨ (ub = true ∧ 0 ≤ a ∧ a < 2 ^ (8 * n))

/-- `LONG_TO_INT` and `LONG_TO_UINT`, longobject.c:6700-6742, with `n` bytes. -/
def toFixed (v : Long) (n : Nat) (unsigned : Bool) (name : String) : Py Unit :=
  if unsigned ∧ v.neg = true then .error (.valueError "Cannot convert negative int")
  else if asNativeRes v n unsigned > n then
    .error (.overflowError s!"Python int too large to convert to {name}")
  else .ok ()

theorem bytes_value {a : Int} {bs : List Nat} (h : (bytesVal bs : Int) = a % 2 ^ (8 * 8)) :
    bytesVal bs = (a % 2 ^ 64).toNat := by
  omega

/-- `PyLong_AsLongLong` is exact on `long long`, and raises `OverflowError` outside it. -/
theorem asLongLong_spec (a : Int) :
    (-(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 63 → asLongLong (.ofInt a) = .ok a) ∧
    (¬ (-(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 63) → (asLongLong (.ofInt a)).raises "OverflowError") := by
  have hc0 : ¬ (-(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 63) → (Long.ofInt a).isCompact ≠ true := by
    intro h hc
    have := (compact_iff a).1 hc
    omega
  have hf : FitsBytes a 8 true ↔ (-(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 63) := by
    simp only [FitsBytes, ite_true]
    omega
  have hout := asByteArray_spec a 8 true
  constructor
  · intro h
    unfold asLongLong
    by_cases hc : (Long.ofInt a).isCompact = true
    · rw [if_pos hc, Long.medium_ofInt ((compact_iff a).1 hc)]
    · rw [if_neg hc, Long.toInt_ofInt]
      rcases hout with ⟨⟨bs, h1, _, _, h4⟩, _⟩ | ⟨_, h2⟩
      · rw [h1]
        simp only
        have e := bytes_value h4
        rw [e]
        simp only [s64of]
        split <;> (congr 1; omega)
      · exact absurd (hf.2 h) h2
  · intro h
    unfold asLongLong
    rw [if_neg (hc0 h), Long.toInt_ofInt]
    rcases hout with ⟨_, h2⟩ | ⟨⟨e, h1, h2⟩, _⟩
    · exact absurd (hf.1 h2) h
    · rw [h1]
      exact ⟨e, rfl, h2⟩

/-- `PyLong_AsUnsignedLongLong` is exact on `unsigned long long`, and raises
`OverflowError` for negative and for too large values. -/
theorem asUnsignedLongLong_spec (a : Int) :
    (0 ≤ a ∧ a < 2 ^ 64 → asUnsignedLongLong (.ofInt a) = .ok a.toNat) ∧
    (¬ (0 ≤ a ∧ a < 2 ^ 64) → (asUnsignedLongLong (.ofInt a)).raises "OverflowError") := by
  have hf : FitsBytes a 8 false ↔ (0 ≤ a ∧ a < 2 ^ 64) := by
    simp only [FitsBytes, Bool.false_eq_true, ite_false]
    try omega
  have hout := asByteArray_spec a 8 false
  have hneg : (Long.ofInt a).neg = decide (a < 0) := rfl
  constructor
  · intro h
    unfold asUnsignedLongLong
    by_cases hc : (!(Long.ofInt a).neg && (Long.ofInt a).isCompact) = true
    · rw [if_pos hc]
      have hc2 : (Long.ofInt a).isCompact = true := by
        simp only [Bool.and_eq_true] at hc
        exact hc.2
      rw [Long.medium_ofInt ((compact_iff a).1 hc2)]
    · rw [if_neg hc, Long.toInt_ofInt]
      rcases hout with ⟨⟨bs, h1, _, _, h4⟩, _⟩ | ⟨_, h2⟩
      · rw [h1]
        simp only
        rw [bytes_value h4]
        congr 2
        omega
      · exact absurd (hf.2 h) h2
  · intro h
    unfold asUnsignedLongLong
    have hc : ¬ (!(Long.ofInt a).neg && (Long.ofInt a).isCompact) = true := by
      intro hc
      simp only [Bool.and_eq_true, Bool.not_eq_true', hneg, decide_eq_false_iff_not] at hc
      have := (compact_iff a).1 hc.2
      omega
    rw [if_neg hc, Long.toInt_ofInt]
    rcases hout with ⟨_, h2⟩ | ⟨⟨e, h1, h2⟩, _⟩
    · exact absurd (hf.1 h2) h
    · rw [h1]
      exact ⟨e, rfl, h2⟩

/-- `PyLong_AsVoidPtr` keeps the bit pattern for everything from `LONG_MIN` to `ULONG_MAX`. -/
theorem asVoidPtr_spec (a : Int) (h : -(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 64) :
    asVoidPtr (.ofInt a) = .ok (a % 2 ^ 64).toNat := by
  unfold asVoidPtr
  have hneg : (Long.ofInt a).neg = decide (a < 0) := rfl
  by_cases hn : a < 0
  · have h0 : (Long.ofInt a).neg = true := by rw [hneg]; exact decide_eq_true hn
    rw [if_pos h0, asLong_spec, if_pos (by omega)]
  · have h0 : (Long.ofInt a).neg = false := by rw [hneg]; exact decide_eq_false hn
    rw [if_neg (by simp [h0]), asUnsignedLong_spec, if_neg hn, if_pos (by omega)]
    congr 1
    omega

/-- `_PyLong_FromDigits` of a normalized vector builds the canonical object. -/
theorem fromDigits_spec {neg : Bool} {ds : List Nat} (hd : IsDigits ds) (hn : Normal ds)
    (hs : ds.length ≤ maxLongDigits) (hz : neg = true → ds ≠ []) :
    fromDigits neg ds = .ok (.ofInt (Long.toInt ⟨neg, ds⟩)) := by
  unfold fromDigits
  by_cases h0 : ds.length = 0
  · have e : ds = [] := List.eq_nil_of_length_eq_zero h0
    subst e
    cases neg with
    | true => exact absurd rfl (hz rfl)
    | false => simp [Long.toInt, Long.ofInt]
  · rw [if_neg h0, longAlloc_ok hs]
    simp only
    rw [← Long.ofInt_of_normal hd hn hz]

theorem two_pow_sub_one_mul {n : Nat} (hn : 1 ≤ n) (k : Nat) (h : k = 8 * n - 1) :
    (2 : Int) ^ (8 * n) = 2 * 2 ^ k := by
  rw [show 8 * n = k + 1 by omega, Int.pow_succ]
  grind

/-- The test of `_fits_in_n_bits`: all bits above `k` agree with the sign. -/
theorem fits_iff {v : Int} {k : Nat} : (v / 2 ^ k == 0 || v / 2 ^ k == -1) = true ↔
    (-(2 ^ k : Int) ≤ v ∧ v < 2 ^ k) := by
  have hp : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
  generalize hD : (2 : Int) ^ k = D at *
  have hm := Int.emod_add_mul_ediv v D
  have hlt := Int.emod_lt_of_pos v hp
  have hge := Int.emod_nonneg v (Int.ne_of_gt hp)
  simp only [Bool.or_eq_true, beq_iff_eq]
  generalize hq : v / D = q at *
  generalize hr : v % D = r at *
  constructor
  · rintro (h | h)
    · subst h
      simp only [Int.mul_zero, Int.add_zero] at hm
      omega
    · subst h
      have : D * -1 = -D := by omega
      rw [this] at hm
      omega
  · rintro ⟨h1, h2⟩
    by_cases h0 : 0 ≤ v
    · left
      rw [← hq]
      exact Int.ediv_eq_zero_of_lt h0 h2
    · right
      have e : v = (v + D) + D * (-1) := by omega
      rw [← hq, e, Int.add_mul_ediv_left _ _ (Int.ne_of_gt hp),
        Int.ediv_eq_zero_of_lt (by omega) (by omega)]
      rfl

theorem fits_iff' {v : Int} {k : Nat} :
    ((v / 2 ^ k == 0) = true ∨ (v / 2 ^ k == -1) = true) ↔ (-(2 ^ k : Int) ≤ v ∧ v < 2 ^ k) := by
  rw [← Bool.or_eq_true]
  exact fits_iff

theorem two_pow_mono_int {j k : Nat} (h : j ≤ k) : (2 : Int) ^ j ≤ 2 ^ k := by
  rw [← cast_two_pow, ← cast_two_pow]
  exact Int.ofNat_le.2 (Nat.pow_le_pow_right (by decide) h)

theorem bitLength_lt_pow {A k : Nat} (h : bitLength A ≤ k) : A < 2 ^ k :=
  Nat.lt_of_lt_of_le (lt_two_pow_bitLength' A) (Nat.pow_le_pow_right (by decide) h)

theorem pow_le_of_bitLength {A k : Nat} (hA : 1 ≤ A) (h : k < bitLength A) : 2 ^ k ≤ A :=
  (two_pow_le_iff_lt_bitLength A k hA).2 h

/-- The return value of `PyLong_AsNativeBytes` keeps its documented promise, in both
directions: at most `n` exactly when the value fits `n` bytes. -/
theorem asNativeRes_spec (a : Int) {n : Nat} (hn : 1 ≤ n) (ub : Bool) :
    asNativeRes (.ofInt a) n ub ≤ n ↔ NativeFit a n ub := by
  have hk8 : 2 ^ (8 * n - 1) ≥ 1 := Nat.two_pow_pos _
  have hPow : (2 : Int) ^ (8 * n) = 2 * 2 ^ (8 * n - 1) := two_pow_sub_one_mul hn _ rfl
  have hC : ((2 ^ (8 * n - 1) : Nat) : Int) = 2 ^ (8 * n - 1) := cast_two_pow _
  generalize hK : (2 : Int) ^ (8 * n - 1) = K at *
  unfold asNativeRes NativeFit
  rw [hPow, hK]
  by_cases hc : (Long.ofInt a).isCompact = true
  · rw [if_pos hc]
    have h1 := (compact_iff a).1 hc
    simp only [Long.medium_ofInt h1]
    rw [if_neg (by omega)]
    by_cases h8 : n ≤ 8
    · rw [if_pos h8]
      by_cases hn8 : n = 8
      · subst hn8
        have e : fitsNBits a (8 * 8) = true := rfl
        rw [if_pos e]
        have hKv : (2 : Int) ^ 30 ≤ K := by
          rw [← hK]; exact two_pow_mono_int (by omega)
        simp only [Nat.le_refl, true_iff]
        left
        omega
      · have hlt : ¬ n * 8 ≥ 64 := by omega
        have hf : fitsNBits a (n * 8) = true ↔ (-K ≤ a ∧ a < K) := by
          simp only [fitsNBits, Bool.or_eq_true, decide_eq_true_eq, hlt, false_or]
          rw [show n * 8 - 1 = 8 * n - 1 by omega, ← hK]
          exact fits_iff'
        have hf2 : fitsNBits a (n * 8 + 1) = true ↔ (-(2 * K) ≤ a ∧ a < 2 * K) := by
          by_cases h7 : n * 8 + 1 ≥ 64
          · omega
          · simp only [fitsNBits, Bool.or_eq_true, decide_eq_true_eq, h7, false_or]
            rw [show n * 8 + 1 - 1 = 8 * n by omega, ← hPow]
            exact fits_iff'
        by_cases hA : fitsNBits a (n * 8) = true
        · rw [if_pos hA]
          simp only [Nat.le_refl, true_iff]
          exact Or.inl (hf.1 hA)
        · rw [if_neg hA]
          have hnf : ¬ (-K ≤ a ∧ a < K) := fun h => hA (hf.2 h)
          by_cases hB : a > 0 ∧ fitsNBits a (n * 8 + 1) = true
          · rw [if_pos hB]
            have hB2 := hf2.1 hB.2
            cases ub with
            | true =>
              simp only [ite_true, Nat.le_refl, true_iff]
              right
              exact ⟨trivial, by omega, by omega⟩
            | false =>
              simp only [Bool.false_eq_true, ite_false, false_and, or_false]
              constructor
              · intro h; omega
              · intro h; exact absurd h hnf
          · rw [if_neg hB]
            constructor
            · intro h; omega
            · rintro (h | ⟨_, h2, h3⟩)
              · exact absurd h hnf
              · exact absurd ⟨by omega, hf2.2 (by omega)⟩ hB
    · rw [if_neg h8]
      have hKv : (2 : Int) ^ 30 ≤ K := by
        rw [← hK]; exact two_pow_mono_int (by omega)
      constructor
      · intro _; left; omega
      · intro _; omega
  · rw [if_neg hc]
    simp only [numBits_spec, Long.toInt_ofInt]
    have hne : (Long.ofInt a).neg = decide (a < 0) := rfl
    have hA1 : 1 ≤ a.natAbs := by
      rcases Nat.eq_zero_or_pos a.natAbs with h | h
      · exfalso
        apply hc
        rw [compact_iff]
        omega
      · exact h
    generalize hB : bitLength a.natAbs = nb at *
    by_cases hedge : n > 0 ∧ nb / 8 + 1 = n + 1 ∧ nb % 8 = 0
    · rw [if_pos hedge]
      have hnb : nb = 8 * n := by omega
      have hlo : 2 ^ (8 * n - 1) ≤ a.natAbs := pow_le_of_bitLength hA1 (by omega)
      have hhi : a.natAbs < 2 ^ (8 * n) := bitLength_lt_pow (by omega)
      have hhi2 : a.natAbs < 2 * 2 ^ (8 * n - 1) := by
        rw [show 8 * n = (8 * n - 1) + 1 by omega, Nat.pow_succ] at hhi
        omega
      have hlo' : K ≤ a.natAbs := by
        rw [← hK, ← cast_two_pow]; exact Int.ofNat_le.2 hlo
      have hhi' : (a.natAbs : Int) < 2 * K := by
        rw [← hK, ← cast_two_pow]; omega
      by_cases hneg : a < 0
      · have hn1 : (Long.ofInt a).neg = true := by rw [hne]; exact decide_eq_true hneg
        simp only [hn1, ite_true]
        have hmod : (a % (2 * K)).toNat = (2 ^ (8 * n - 1) : Nat) ↔ a = -K := by
          have e1 : a % (2 * K) = a + 2 * K := by
            have : a = (a + 2 * K) + (2 * K) * (-1) := by omega
            conv => lhs; rw [this]
            rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
          rw [e1]
          omega
        by_cases he : a = -K
        · rw [if_pos (hmod.2 he)]
          simp only [Nat.le_refl, true_iff]
          left; omega
        · rw [if_neg (fun h => he (hmod.1 h))]
          constructor
          · intro h; omega
          · rintro (h | ⟨_, h2, _⟩)
            · omega
            · omega
      · have hn1 : (Long.ofInt a).neg = false := by rw [hne]; exact decide_eq_false hneg
        simp only [hn1, Bool.false_eq_true, ite_false]
        have hmod : (2 : Nat) ^ (8 * n - 1) ≤ (a % (2 * K)).toNat := by
          rw [Int.emod_eq_of_lt (by omega) (by omega)]
          omega
        rw [if_pos hmod]
        cases ub with
        | true =>
          simp only [ite_true, Nat.le_refl, true_iff]
          right
          exact ⟨trivial, by omega, by omega⟩
        | false =>
          simp only [Bool.false_eq_true, ite_false, false_and, or_false]
          constructor
          · intro h; omega
          · intro h; omega
    · rw [if_neg hedge]
      by_cases hsmall : nb / 8 + 1 ≤ n
      · have hbl : a.natAbs < 2 ^ (8 * n - 1) := bitLength_lt_pow (by omega)
        have hb2 : (a.natAbs : Int) < K := by
          rw [← hK, ← cast_two_pow]; exact Int.ofNat_lt.2 hbl
        constructor
        · intro _; left; omega
        · intro _; exact hsmall
      · have hbig : 2 ^ (8 * n) ≤ a.natAbs := pow_le_of_bitLength hA1 (by omega)
        have hb2 : 2 * K ≤ (a.natAbs : Int) := by
          rw [← hPow, ← cast_two_pow]
          exact Int.ofNat_le.2 hbig
        constructor
        · intro h; omega
        · rintro (⟨h1, h2⟩ | ⟨_, h1, h2⟩) <;> omega

/-- `PyLong_AsInt32/64` and `PyLong_AsUInt32/64` raise exactly outside their type. -/
theorem toFixed_spec (a : Int) {n : Nat} (hn : 1 ≤ n) (name : String) :
    (toFixed (.ofInt a) n false name = .ok () ↔
      (-(2 ^ (8 * n - 1) : Int) ≤ a ∧ a < 2 ^ (8 * n - 1))) ∧
    (0 ≤ a → (toFixed (.ofInt a) n true name = .ok () ↔ a < 2 ^ (8 * n))) := by
  have hne : (Long.ofInt a).neg = decide (a < 0) := rfl
  constructor
  · have hs := asNativeRes_spec a hn false
    simp only [NativeFit, Bool.false_eq_true, false_and, or_false] at hs
    unfold toFixed
    simp only [Bool.false_eq_true, false_and, ite_false]
    by_cases h : asNativeRes (Long.ofInt a) n false > n
    · rw [if_pos h]
      simp only [reduceCtorEq, false_iff]
      intro h2
      have := hs.2 h2
      omega
    · rw [if_neg h]
      simp only [true_iff]
      exact hs.1 (by omega)
  · intro h0
    have hs := asNativeRes_spec a hn true
    simp only [NativeFit, true_and] at hs
    have hPow : (2 : Int) ^ (8 * n) = 2 * 2 ^ (8 * n - 1) := two_pow_sub_one_mul hn _ rfl
    have hP : (0 : Int) < 2 ^ (8 * n - 1) := Int.pow_pos (by decide)
    have hn0 : (Long.ofInt a).neg = false := by rw [hne]; exact decide_eq_false (by omega)
    unfold toFixed
    rw [hn0]
    simp only [Bool.false_eq_true, and_false, ite_false]
    by_cases h : asNativeRes (Long.ofInt a) n true > n
    · rw [if_pos h]
      simp only [reduceCtorEq, false_iff]
      intro h2
      have := hs.2 (Or.inr ⟨h0, h2⟩)
      omega
    · rw [if_neg h]
      simp only [true_iff]
      rcases hs.1 (by omega) with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega

/-! ## Statements -/

def LongLongExact : Prop :=
  ∀ a : Int,
    ((-(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 63 → asLongLong (.ofInt a) = .ok a) ∧
      (¬ (-(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 63) → (asLongLong (.ofInt a)).raises "OverflowError")) ∧
    ((0 ≤ a ∧ a < 2 ^ 64 → asUnsignedLongLong (.ofInt a) = .ok a.toNat) ∧
      (¬ (0 ≤ a ∧ a < 2 ^ 64) → (asUnsignedLongLong (.ofInt a)).raises "OverflowError"))

theorem longLongExact_proven : LongLongExact := fun a =>
  ⟨asLongLong_spec a, asUnsignedLongLong_spec a⟩

def VoidPtrExact : Prop :=
  ∀ a : Int, -(2 ^ 63 : Int) ≤ a ∧ a < 2 ^ 64 → asVoidPtr (.ofInt a) = .ok (a % 2 ^ 64).toNat

theorem voidPtrExact_proven : VoidPtrExact := asVoidPtr_spec

def FromDigitsExact : Prop :=
  ∀ (neg : Bool) (ds : List Nat), IsDigits ds → Normal ds → ds.length ≤ maxLongDigits →
    (neg = true → ds ≠ []) → fromDigits neg ds = .ok (.ofInt (Long.toInt ⟨neg, ds⟩))

theorem fromDigitsExact_proven : FromDigitsExact := fun _ _ h1 h2 h3 h4 => fromDigits_spec h1 h2 h3 h4

/-- The return value of `PyLong_AsNativeBytes` is at most `n` exactly when the value fits
`n` bytes, signed, or unsigned for an unsigned buffer. Docs: "If the returned value is
less than or equal to n, the entire value was copied". -/
def NativeBytesContract : Prop :=
  ∀ (a : Int) (n : Nat) (ub : Bool), 1 ≤ n →
    (asNativeRes (.ofInt a) n ub ≤ n ↔ NativeFit a n ub)

theorem nativeBytesContract_proven : NativeBytesContract := fun a _ ub h => asNativeRes_spec a h ub

/-- `PyLong_AsInt32/64` succeed exactly on their range; `PyLong_AsUInt32/64` likewise on
non-negative values. -/
def FixedWidthExact : Prop :=
  ∀ (a : Int) (n : Nat) (name : String), 1 ≤ n →
    (toFixed (.ofInt a) n false name = .ok () ↔
      (-(2 ^ (8 * n - 1) : Int) ≤ a ∧ a < 2 ^ (8 * n - 1))) ∧
    (0 ≤ a → (toFixed (.ofInt a) n true name = .ok () ↔ a < 2 ^ (8 * n)))

theorem fixedWidthExact_proven : FixedWidthExact := fun a _ name h => toFixed_spec a h name

def entriesConv2 : List Entry := [
  { id := "longobj-as-long-long", pyFile := "Objects/longobject.c"
    pyFns := ["PyLong_AsLongLong", "PyLong_AsUnsignedLongLong"]
    statement := "PyLong_AsLongLong and PyLong_AsUnsignedLongLong are exact on their type and raise OverflowError outside it."
    source := "C API docs: Integer Objects", status := .proven
    prop := ``LongLongExact, thm := some ``longLongExact_proven
    notes := "Non-compact values go through _PyLong_AsByteArray, MathInt.asByteArray here." },
  { id := "longobj-void-ptr", pyFile := "Objects/longobject.c", pyFns := ["PyLong_AsVoidPtr"]
    statement := "PyLong_AsVoidPtr keeps the 64 bit pattern of every int from LONG_MIN to ULONG_MAX."
    source := "C API docs: PyLong_AsVoidPtr", status := .proven
    prop := ``VoidPtrExact, thm := some ``voidPtrExact_proven },
  { id := "longobj-from-digits", pyFile := "Objects/longobject.c", pyFns := ["_PyLong_FromDigits"]
    statement := "_PyLong_FromDigits of a normalized vector builds the canonical object."
    source := "invariant", status := .proven
    prop := ``FromDigitsExact, thm := some ``fromDigitsExact_proven },
  { id := "longobj-native-bytes", pyFile := "Objects/longobject.c"
    pyFns := ["PyLong_AsNativeBytes", "_fits_in_n_bits", "_PyLong_NumBits"]
    statement := "For n >= 1 the result of PyLong_AsNativeBytes is at most n exactly when the value fits n bytes, signed, or unsigned for an unsigned buffer, including the 0x80..00 and top-bit-set edge cases."
    source := "C API docs: PyLong_AsNativeBytes", status := .proven
    prop := ``NativeBytesContract, thm := some ``nativeBytesContract_proven
    notes := "The buffer is modelled by its value; n == 0, used to query a size, is not covered." },
  { id := "longobj-fixed-width", pyFile := "Objects/longobject.c"
    pyFns := ["PyLong_AsInt32", "PyLong_AsInt64", "PyLong_AsUInt32", "PyLong_AsUInt64"]
    statement := "PyLong_AsInt32/64 succeed exactly on their range, and PyLong_AsUInt32/64 exactly on theirs for non-negative values."
    source := "C API docs: PyLong_AsInt64", status := .proven
    prop := ``FixedWidthExact, thm := some ``fixedWidthExact_proven }
]

end PyLean.LongObj
