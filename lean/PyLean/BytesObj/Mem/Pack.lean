import PyLean.BytesObj.Mem.Cast

/-!
`pack_single` and `unpack_single`: exact integer round trips, range errors, the
released-view checks, and the arm that has none.
-/

namespace PyLean.BytesObj.Mem

open PyLean

/-- `(low, high, size)` of the integer format `c`. -/
def intRange : Char → Option (Int × Int × Nat)
  | 'b' => some (-128, 127, 1)
  | 'B' => some (0, 255, 1)
  | 'h' => some (-32768, 32767, 2)
  | 'H' => some (0, 65535, 2)
  | 'i' => some (-2147483648, 2147483647, 4)
  | 'I' => some (0, 4294967295, 4)
  | 'l' | 'q' | 'n' => some (-9223372036854775808, 9223372036854775807, 8)
  | 'L' | 'Q' | 'N' => some (0, 18446744073709551615, 8)
  | _ => none

theorem wrBytes_keep_len (m : Mem) (p : Int) (bs : List Nat) :
    (wrBytes m p bs).length = m.length := wrBytes_length m p bs

theorem rd_after_write (m : Mem) (p : Int) (bs : List Nat) (k : Nat) (hk : bs.length = k)
    (hp : 0 ≤ p) (h : p + k ≤ m.length) : rdBytes (wrBytes m p bs) p k = bs := by
  subst hk
  exact rdBytes_wrBytes m p bs hp h

theorem decLE_encInt (v : Int) (k : Nat) :
    decLE (encInt v k) = (v % (2 ^ (8 * k) : Int)).toNat := by
  unfold encInt
  rw [decLE_encLE]
  have h1 : (256 : Nat) ^ k = 2 ^ (8 * k) := by
    rw [Nat.pow_mul]
  rw [h1]
  have hp : (0 : Int) < 2 ^ (8 * k) := by
    have : (0 : Nat) < 2 ^ (8 * k) := Nat.two_pow_pos _
    exact_mod_cast this
  have h0 := Int.emod_nonneg v (b := 2 ^ (8 * k)) (by omega)
  have hlt := Int.emod_lt_of_pos v hp
  apply Nat.mod_eq_of_lt
  have : ((v % (2 ^ (8 * k) : Int)).toNat : Int) < ((2 ^ (8 * k) : Nat) : Int) := by
    rw [Int.toNat_of_nonneg h0]
    exact_mod_cast hlt
  exact_mod_cast this

theorem asLong_ok (v : Int) (h : -9223372036854775808 ≤ v ∧ v < 9223372036854775808) :
    asLong v = .ok v := by
  unfold asLong
  rw [if_pos (by omega)]

theorem asLong_err (v : Int) (h : ¬ (-9223372036854775808 ≤ v ∧ v < 9223372036854775808)) :
    asLong v = .error (.overflowError "Python int too large to convert to C long") := by
  unfold asLong
  rw [if_neg (by omega)]

theorem asUnsignedLong_ok (v : Int) (h : 0 ≤ v ∧ v < 18446744073709551616) :
    asUnsignedLong v = .ok v := by
  unfold asUnsignedLong
  rw [if_neg (by omega), if_pos (by omega)]

theorem asUnsignedLong_err (v : Int) (h : ¬ (0 ≤ v ∧ v < 18446744073709551616)) :
    ∃ m, asUnsignedLong v = .error (.overflowError m) := by
  unfold asUnsignedLong
  split
  · exact ⟨_, rfl⟩
  · rw [if_neg (by omega)]
    exact ⟨_, rfl⟩

theorem longAsSsize_ok (v : Int) (h : -9223372036854775808 ≤ v ∧ v < 9223372036854775808) :
    longAsSsize v = .ok v := by
  unfold longAsSsize ssizeMin ssizeMax
  rw [if_pos (by omega)]

theorem longAsSsize_err (v : Int) (h : ¬ (-9223372036854775808 ≤ v ∧ v < 9223372036854775808)) :
    longAsSsize v = .error (.overflowError "Python int too large to convert to C ssize_t") := by
  unfold longAsSsize ssizeMin ssizeMax
  rw [if_neg (by omega)]

/-- An in-range int goes to the store, in every integer format. -/
theorem pack_int_ok (st : St) (self : Nat) (ptr v lo hi : Int) (c : Char) (k : Nat)
    (hc : intRange c = some (lo, hi, k)) (hrel : baseInaccessible st self = false)
    (h : lo ≤ v ∧ v ≤ hi) :
    packSingle self ptr (.int v) [c] st =
      (.ok (), { st with mem := wrBytes st.mem ptr (encInt v k) }) := by
  unfold intRange at hc
  split at hc <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hc
  all_goals obtain ⟨rfl, rfl, rfl⟩ := hc
  all_goals first
    | (have e1 := asLong_ok v (by omega)
       have e2 := longAsSsize_ok v (by omega)
       simp only [packSingle, cc, List.getD_cons_zero, M.bind_app, M.mapErr, pylongAsLd, pylongAsLld,
         pylongAsZd, numberIndex, M.lift, e1, e2, M.pure_app, checkReleased_ok _ _ hrel]
       try rw [if_neg (by omega)]
       rfl)
    | (have e1 := asUnsignedLong_ok v (by omega)
       simp only [packSingle, cc, List.getD_cons_zero, M.bind_app, M.mapErr, pylongAsLu, pylongAsLlu,
         pylongAsZu, numberIndex, M.lift, e1, M.pure_app, checkReleased_ok _ _ hrel]
       try rw [if_neg (by omega)]
       rfl)

/-- An out-of-range int raises `ValueError` and writes nothing, in every integer format,
including ints too large for the C conversion. -/
theorem pack_int_err (st : St) (self : Nat) (ptr v lo hi : Int) (c : Char) (k : Nat)
    (hc : intRange c = some (lo, hi, k)) (hrel : baseInaccessible st self = false)
    (h : ¬ (lo ≤ v ∧ v ≤ hi)) :
    packSingle self ptr (.int v) [c] st = (.error (valueErrorInt [c]), st) := by
  unfold intRange at hc
  split at hc <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hc
  all_goals obtain ⟨rfl, rfl, rfl⟩ := hc
  all_goals by_cases hL : -9223372036854775808 ≤ v ∧ v < 9223372036854775808
  all_goals by_cases hU : 0 ≤ v ∧ v < 18446744073709551616
  all_goals first
    | (have e1 := asLong_err v (by omega)
       have e2 := longAsSsize_err v (by omega)
       simp only [packSingle, cc, List.getD_cons_zero, M.bind_app, M.mapErr, pylongAsLd, pylongAsLld,
         pylongAsZd, numberIndex, M.lift, e1, e2, M.pure_app, fixErrorInt]
       done)
    | (have e1 := asLong_ok v (by omega)
       simp only [packSingle, cc, List.getD_cons_zero, M.bind_app, M.mapErr, pylongAsLd, numberIndex,
         M.lift, e1, M.pure_app, checkReleased_ok _ _ hrel]
       rw [if_pos (by omega)]
       rfl)
    | (have hn : ¬ (0 ≤ v ∧ v < 18446744073709551616) := by omega
       obtain ⟨m, e1⟩ := asUnsignedLong_err v hn
       simp only [packSingle, cc, List.getD_cons_zero, M.bind_app, M.mapErr, pylongAsLu, pylongAsLlu,
         pylongAsZu, numberIndex, M.lift, e1, M.pure_app, fixErrorInt]
       done)
    | (have e1 := asUnsignedLong_ok v (by omega)
       simp only [packSingle, cc, List.getD_cons_zero, M.bind_app, M.mapErr, pylongAsLu, numberIndex,
         M.lift, e1, M.pure_app, checkReleased_ok _ _ hrel]
       rw [if_pos (by omega)]
       rfl)

theorem sx1 (v : Int) (h : -128 ≤ v ∧ v ≤ 127) : sx 1 (v % 256).toNat = v := by
  simp only [sx, Nat.mul_one, show 8 - 1 = 7 from rfl]
  split <;> omega

theorem sx2 (v : Int) (h : -32768 ≤ v ∧ v ≤ 32767) : sx 2 (v % 65536).toNat = v := by
  simp only [sx, show 8 * 2 - 1 = 15 from rfl, show 8 * 2 = 16 from rfl]
  split <;> omega

theorem sx4 (v : Int) (h : -2147483648 ≤ v ∧ v ≤ 2147483647) : sx 4 (v % 4294967296).toNat = v := by
  simp only [sx, show 8 * 4 - 1 = 31 from rfl, show 8 * 4 = 32 from rfl]
  split <;> omega

theorem sx8 (v : Int) (h : -9223372036854775808 ≤ v ∧ v ≤ 9223372036854775807) :
    sx 8 (v % 18446744073709551616).toNat = v := by
  simp only [sx, show 8 * 8 - 1 = 63 from rfl, show 8 * 8 = 64 from rfl]
  split <;> omega

/-- What reading back gives: `rdU` of the write. -/
theorem rdU_write (m : Mem) (p v : Int) (k : Nat) (hp : 0 ≤ p) (h : p + k ≤ m.length) :
    rdU (wrBytes m p (encInt v k)) p k = (v % (2 ^ (8 * k) : Int)).toNat := by
  unfold rdU
  rw [rd_after_write _ _ _ k (by simp [encInt, encLE_length]) hp h, decLE_encInt]

theorem rdU_one (m : Mem) (p : Int) : rdU m p 1 = rdByte m p := by
  simp [rdU, rdBytes, decLE]

/-- `m[i] = v; m[i] == v` at the level of one item: for every native integer format, every
int in the format's range is stored and read back unchanged, with the store unchanged
outside the item; every other int raises `ValueError("memoryview: invalid value for format
...")` and writes nothing. Hypotheses: the view is live and the item lies in the store. -/
def PackUnpackInt : Prop :=
  ∀ (st : St) (self : Nat) (ptr : Int) (c : Char) (lo hi : Int) (k : Nat) (v : Int),
    intRange c = some (lo, hi, k) → baseInaccessible st self = false →
    0 ≤ ptr → ptr + k ≤ st.mem.length →
    let r := packSingle self ptr (.int v) [c] st
    if lo ≤ v ∧ v ≤ hi then
      r.1 = .ok () ∧ unpackRaw r.2.mem ptr [c] = .ok (.int v) ∧
      ∀ q : Int, 0 ≤ q → q + 1 ≤ ptr ∨ ptr + k ≤ q → rdByte r.2.mem q = rdByte st.mem q
    else r.1 = .error (valueErrorInt [c]) ∧ r.2.mem = st.mem

theorem unpack_after_pack (m : Mem) (ptr v lo hi : Int) (c : Char) (k : Nat)
    (hc : intRange c = some (lo, hi, k)) (hp : 0 ≤ ptr) (hk : ptr + k ≤ m.length)
    (h : lo ≤ v ∧ v ≤ hi) : unpackRaw (wrBytes m ptr (encInt v k)) ptr [c] = .ok (.int v) := by
  have hu := rdU_write m ptr v k hp
  unfold intRange at hc
  split at hc <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hc
  all_goals obtain ⟨rfl, rfl, rfl⟩ := hc
  all_goals simp only [unpackRaw, cc, List.getD_cons_zero, rdS, ← rdU_one]
  all_goals rw [hu hk]
  all_goals first
    | rw [show ((2 : Int) ^ (8 * 1)) = 256 from rfl, sx1 v (by omega)]
    | rw [show ((2 : Int) ^ (8 * 2)) = 65536 from rfl, sx2 v (by omega)]
    | rw [show ((2 : Int) ^ (8 * 4)) = 4294967296 from rfl, sx4 v (by omega)]
    | rw [show ((2 : Int) ^ (8 * 8)) = 18446744073709551616 from rfl, sx8 v (by omega)]
    | (rw [show ((2 : Int) ^ (8 * 1)) = 256 from rfl,
         show (((v % 256).toNat : Nat) : Int) = v by omega])
    | (rw [show ((2 : Int) ^ (8 * 2)) = 65536 from rfl,
         show (((v % 65536).toNat : Nat) : Int) = v by omega])
    | (rw [show ((2 : Int) ^ (8 * 4)) = 4294967296 from rfl,
         show (((v % 4294967296).toNat : Nat) : Int) = v by omega])
    | (rw [show ((2 : Int) ^ (8 * 8)) = 18446744073709551616 from rfl,
         show (((v % 18446744073709551616).toNat : Nat) : Int) = v by omega])

theorem encInt_length (v : Int) (k : Nat) : (encInt v k).length = k := by
  simp [encInt, encLE_length]

theorem packUnpackInt_proven : PackUnpackInt := by
  intro st self ptr c lo hi k v hc hrel hp hk
  dsimp only
  by_cases h : lo ≤ v ∧ v ≤ hi
  · rw [if_pos h, pack_int_ok st self ptr v lo hi c k hc hrel h]
    refine ⟨rfl, unpack_after_pack _ ptr v lo hi c k hc hp hk h, ?_⟩
    intro q hq hout
    exact rdByte_wrBytes_out _ _ _ _ hp hq (by rw [encInt_length]; omega)
  · rw [if_neg h, pack_int_err st self ptr v lo hi c k hc hrel h]
    exact ⟨rfl, rfl⟩

end PyLean.BytesObj.Mem
