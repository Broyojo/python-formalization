import PyLean.MathInt.ToBytes

/-!
`int.to_bytes` / `int.from_bytes` properties.
-/

namespace PyLean.MathInt

open PyLean

theorem asByteArray_spec (v : Int) (n : Nat) (signed : Bool) :
    BytesOutcome v n signed (asByteArray v n signed) := by
  by_cases hv : 0 ≤ v
  · obtain ⟨V, rfl⟩ : ∃ V : Nat, v = V := ⟨v.toNat, by omega⟩
    exact asByteArray_nonneg V n signed
  · cases signed with
    | true =>
      obtain ⟨V, rfl⟩ : ∃ V : Nat, v = -(V : Int) := ⟨v.natAbs, by omega⟩
      exact asByteArray_neg V n (by omega)
    | false =>
      right
      refine ⟨⟨_, by simp [asByteArray, show v < 0 by omega]; rfl, rfl⟩, ?_⟩
      unfold FitsBytes; simp; omega

/-- Little-endian view of the bytes `to_bytes` / `from_bytes` see. -/
def lsbOf (byteorder : String) (bs : List Nat) : List Nat :=
  if byteorder = "little" then bs else bs.reverse

theorem allBytes_reverse {bs : List Nat} (h : AllBytes bs) : AllBytes bs.reverse :=
  fun b hb => h b (List.mem_reverse.mp hb)

/-- `int.to_bytes` docs: "An OverflowError is raised if the integer is not
representable with the given number of bytes"; otherwise the result has
exactly `length` bytes holding `v mod 256**length` (two's complement when
`signed`) in the requested byte order. -/
def ToBytesExact : Prop :=
  ∀ (v : Int) (n : Nat) (byteorder : String) (signed : Bool),
    (byteorder = "little" ∨ byteorder = "big") → (n : Int) ≤ ssizeMax →
    (FitsBytes v n signed → ∃ bs, toBytes v n byteorder signed = .ok bs ∧ bs.length = n ∧
        AllBytes bs ∧ (bytesVal (lsbOf byteorder bs) : Int) = v % 2 ^ (8 * n)) ∧
    (¬ FitsBytes v n signed → (toBytes v n byteorder signed).raises "OverflowError")

theorem toBytes_eq (v : Int) (n : Nat) (byteorder : String) (signed : Bool)
    (ho : byteorder = "little" ∨ byteorder = "big") (hn : (n : Int) ≤ ssizeMax) :
    toBytes v n byteorder signed =
      (asByteArray v n signed).map (fun bs => if byteorder = "little" then bs else bs.reverse) := by
  unfold toBytes
  have h1 : ¬ ((n : Int) < ssizeMin ∨ (n : Int) > ssizeMax) := by
    unfold ssizeMin at *; omega
  have h2 : ¬ (byteorder ≠ "little" ∧ byteorder ≠ "big") := by
    rcases ho with h | h <;> simp [h]
  simp only [h1, h2, ite_false, show ¬ ((n : Int) < 0) by omega, Int.toNat_natCast]
  cases asByteArray v n signed <;> rfl

theorem toBytesExact_proven : ToBytesExact := by
  intro v n byteorder signed ho hn
  rw [toBytes_eq v n byteorder signed ho hn]
  rcases asByteArray_spec v n signed with ⟨⟨bs, hbs, hlen, hall, hval⟩, hfit⟩ | ⟨⟨e, he, hcls⟩, hnf⟩
  · refine ⟨fun _ => ⟨_, by rw [hbs]; rfl, ?_, ?_, ?_⟩, fun h => absurd hfit h⟩
    · split <;> simp [hlen]
    · split
      · exact hall
      · exact allBytes_reverse hall
    · unfold lsbOf; split <;> simp [hval]
  · refine ⟨fun h => absurd h hnf, fun _ => ⟨e, by rw [he]; rfl, hcls⟩⟩

/-- `int.from_bytes` docs: the bytes are read in the given byte order;
"signed indicates whether two's complement is used to represent the integer". -/
def FromBytesValue : Prop :=
  ∀ (bs : List Nat) (byteorder : String) (signed : Bool), AllBytes bs →
    (byteorder = "little" ∨ byteorder = "big") →
    fromBytes bs byteorder signed = .ok (bytesSigned (lsbOf byteorder bs) signed)

theorem fromBytesValue_proven : FromBytesValue := by
  intro bs byteorder signed hall ho
  unfold fromBytes lsbOf
  have h2 : ¬ (byteorder ≠ "little" ∧ byteorder ≠ "big") := by
    rcases ho with h | h <;> simp [h]
  simp only [h2, ite_false]
  split
  · rw [fromByteArray_spec _ _ hall]
  · rw [fromByteArray_spec _ _ (allBytes_reverse hall)]

theorem getLastD_eq_div (bs : List Nat) (hall : AllBytes bs) (k : Nat) (hk : bs.length = k + 1) :
    bs.getLastD 0 = bytesVal bs / 256 ^ k := by
  induction k generalizing bs with
  | zero =>
    match bs, hk with
    | [b], _ => simp [bytesVal]
  | succ k ih =>
    match bs, hk with
    | b :: rest, hk' =>
      have hb := hall b (by simp)
      have hrest : AllBytes rest := fun x hx => hall x (by simp [hx])
      have hlen : rest.length = k + 1 := by simp at hk'; omega
      have hne : rest ≠ [] := by intro h; rw [h] at hlen; simp at hlen
      rw [List.getLastD_cons, show rest.getLastD b = rest.getLastD 0 by
        cases rest with
        | nil => exact absurd rfl hne
        | cons r rs => rw [List.getLastD_cons, List.getLastD_cons], ih rest hrest hlen]
      simp only [bytesVal, Nat.pow_succ]
      rw [show 256 ^ k * 256 = 256 * 256 ^ k by rw [Nat.mul_comm], ← Nat.div_div_eq_div_mul,
        show (b + 256 * bytesVal rest) / 256 = bytesVal rest by omega]

/-- Round trip: `int.from_bytes(v.to_bytes(n, order, signed=s), order,
signed=s) == v` whenever `v` fits in `n` bytes. -/
def BytesRoundTrip : Prop :=
  ∀ (v : Int) (n : Nat) (byteorder : String) (signed : Bool),
    (byteorder = "little" ∨ byteorder = "big") → (n : Int) ≤ ssizeMax → FitsBytes v n signed →
    ∃ bs, toBytes v n byteorder signed = .ok bs ∧ fromBytes bs byteorder signed = .ok v

theorem bytesRoundTrip_proven : BytesRoundTrip := by
  intro v n byteorder signed ho hn hfit
  obtain ⟨bs, hbs, hlen, hall, hval⟩ := (toBytesExact_proven v n byteorder signed ho hn).1 hfit
  refine ⟨bs, hbs, ?_⟩
  rw [fromBytesValue_proven bs byteorder signed hall ho]
  congr 1
  have hlsb_len : (lsbOf byteorder bs).length = n := by unfold lsbOf; split <;> simp [hlen]
  have hlsb_all : AllBytes (lsbOf byteorder bs) := by
    unfold lsbOf; split
    · exact hall
    · exact allBytes_reverse hall
  generalize lsbOf byteorder bs = lsb at *
  unfold bytesSigned
  have hP : (2 : Int) ^ (8 * n) = ((256 ^ n : Nat) : Int) := by rw [pow256, Int.natCast_pow]; rfl
  have hB := bytesVal_lt lsb hlsb_all
  rw [hlsb_len] at hB
  unfold FitsBytes at hfit
  cases signed with
  | false =>
    simp only [Bool.false_eq_true, false_and, ite_false] at hfit ⊢
    rw [hval, Int.emod_eq_of_lt (by omega) (by omega)]
  | true =>
    simp only [ite_true, true_and] at hfit ⊢
    by_cases hn0 : n = 0
    · subst hn0
      have : lsb = [] := List.eq_nil_of_length_eq_zero hlsb_len
      subst this
      simp at hfit; simp [bytesVal]; omega
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hlast := getLastD_eq_div lsb hlsb_all k hlsb_len
    have hPk : (256 : Nat) ^ (k + 1) = 256 ^ k * 256 := Nat.pow_succ 256 k
    have hP' : ((256 ^ (k + 1) : Nat) : Int) = ((256 ^ k : Nat) : Int) * 256 := by
      rw [hPk, Int.natCast_mul]; rfl
    by_cases hv : 0 ≤ v
    · have hval' : (bytesVal lsb : Int) = v := by
        rw [hval, Int.emod_eq_of_lt hv (by omega)]
      have : bytesVal lsb / 256 ^ k < 128 := by
        apply (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).mpr
        have : 2 * (bytesVal lsb : Int) < ((256 ^ k : Nat) : Int) * 256 := by rw [← hP', ← hP]; omega
        omega
      simp only [hlast, show ¬ (bytesVal lsb / 256 ^ k ≥ 128) by omega, ite_false]
      exact hval'
    · have hval' : (bytesVal lsb : Int) = v + 2 ^ (8 * (k + 1)) := by
        rw [hval]
        have : v = (v + 2 ^ (8 * (k + 1))) + (-1) * 2 ^ (8 * (k + 1)) := by omega
        rw [this, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)]
        omega
      have : bytesVal lsb / 256 ^ k ≥ 128 := by
        apply (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))).mpr
        have : ((256 ^ k : Nat) : Int) * 256 ≤ 2 * (bytesVal lsb : Int) := by rw [← hP', ← hP]; omega
        omega
      simp only [hlast, this, ite_true, hlsb_len]
      have h256i : (256 : Int) ^ (k + 1) = 2 ^ (8 * (k + 1)) := by rw [Int.pow_mul]; rfl
      rw [hval', h256i]; omega

/-- Argument errors of `int.to_bytes` (longobject.c:6306-6324, after Argument
Clinic's `Py_ssize_t` conversion) and `int.from_bytes` (:6370-6380). -/
def BytesArgErrors : Prop :=
  ∀ (v length : Int) (byteorder : String) (signed : Bool) (bs : List Nat),
    ((byteorder ≠ "little" ∧ byteorder ≠ "big") → ssizeMin ≤ length → length ≤ ssizeMax →
      (toBytes v length byteorder signed).raises "ValueError" ∧
      (fromBytes bs byteorder signed).raises "ValueError") ∧
    ((byteorder = "little" ∨ byteorder = "big") → ssizeMin ≤ length → length < 0 →
      (toBytes v length byteorder signed).raises "ValueError") ∧
    ((length < ssizeMin ∨ length > ssizeMax) → (toBytes v length byteorder signed).raises "OverflowError")

theorem bytesArgErrors_proven : BytesArgErrors := by
  intro v length byteorder signed bs
  refine ⟨fun hb h1 h2 => ⟨?_, ?_⟩, fun hb h1 h2 => ?_, fun h => ?_⟩
  · refine ⟨.valueError "byteorder must be either 'little' or 'big'", ?_, rfl⟩
    unfold toBytes; simp only [show ¬ (length < ssizeMin ∨ length > ssizeMax) by omega, hb,
      ne_eq, not_false_eq_true, and_self, ite_true, ite_false]
  · refine ⟨.valueError "byteorder must be either 'little' or 'big'", ?_, rfl⟩
    unfold fromBytes; simp only [hb, ne_eq, not_false_eq_true, and_self, ite_true]
  · refine ⟨.valueError "length argument must be non-negative", ?_, rfl⟩
    have : ¬ (byteorder ≠ "little" ∧ byteorder ≠ "big") := by rcases hb with h | h <;> simp [h]
    unfold toBytes
    simp only [show ¬ (length < ssizeMin ∨ length > ssizeMax) by unfold ssizeMax ssizeMin at *; omega,
      this, h2, ite_true, ite_false]
  · refine ⟨.overflowError "Python int too large to convert to C ssize_t", ?_, rfl⟩
    unfold toBytes; simp only [h, ite_true]

end PyLean.MathInt
