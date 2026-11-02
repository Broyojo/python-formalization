import PyLean.BytesObj.Mem.Fortran
import PyLean.BytesObj.Mem.CmpTree

/-!
Items of the formats `Zf` and `Zd`, which `NativeView` leaves out. `unpack_cmp` compares them as C
floats or doubles, while `tolist` goes through `PyFloat_Unpack4`, which keeps a signalling NaN.
-/

namespace PyLean.BytesObj.Mem

set_option maxRecDepth 100000 in
/-- A signalling NaN pattern widens to a NaN, with the quiet bit set or, by `PyFloat_Unpack4`, cleared. -/
theorem sNaN_widen (x : Nat) (h : x / 2 ^ 23 % 2 ^ 8 = 255 ∧ x % 2 ^ 23 ≠ 0 ∧ x / 2 ^ 22 % 2 = 0) :
    dIsNaN (widen32 x) = true ∧ dIsNaN (widen32 x - 2 ^ 51) = true := by
  obtain ⟨h1, h2, h3⟩ := h
  have e1 : (2 : Nat) ^ 23 = 8388608 := by decide
  have e2 : (2 : Nat) ^ 22 = 4194304 := by decide
  have e3 : (2 : Nat) ^ 8 = 256 := by decide
  have e4 : (2 : Nat) ^ 31 = 2147483648 := by decide
  have e5 : (2 : Nat) ^ 29 = 536870912 := by decide
  have e6 : (2 : Nat) ^ 51 = 2251799813685248 := by decide
  have e7 : (2 : Nat) ^ 52 = 4503599627370496 := by decide
  have e8 : (2 : Nat) ^ 11 = 2048 := by decide
  have e9 : two63 = 9223372036854775808 := by decide
  have e10 : infBits = 9218868437227405312 := by decide
  rw [e1, e3] at h1
  rw [e1] at h2
  rw [e2] at h3
  simp only [widen32, e1, e2, e3, e4, e9, e10, e5, h1, if_true, h2, if_false]
  have hs2 : x / 2147483648 % 2 < 2 := by omega
  generalize x / 2147483648 % 2 = s at hs2 ⊢
  have hf : x % 8388608 % 4194304 = x % 8388608 := by omega
  rw [hf]
  have hf2 : x % 8388608 < 4194304 := by omega
  generalize x % 8388608 = f at h2 hf2 ⊢
  simp only [dIsNaN, dExp, dFrac, e7, e8, e6]
  have ha : (s * 9223372036854775808 + 9218868437227405312 + (f + 4194304) * 536870912) / 4503599627370496 % 2048 = 2047 := by
    omega
  have hb : (s * 9223372036854775808 + 9218868437227405312 + (f + 4194304) * 536870912 - 2251799813685248) / 4503599627370496 % 2048 = 2047 := by
    omega
  have hc : (s * 9223372036854775808 + 9218868437227405312 + (f + 4194304) * 536870912) % 4503599627370496 ≠ 0 := by
    omega
  have hd : (s * 9223372036854775808 + 9218868437227405312 + (f + 4194304) * 536870912 - 2251799813685248) % 4503599627370496 ≠ 0 := by
    omega
  simp [ha, hb, hc, hd]

/-- `PyFloat_Unpack4` and the C widening differ only in the quiet bit of a NaN. -/
theorem unpack4_nan (x : Nat) : dIsNaN (unpack4 x) = dIsNaN (widen32 x) := by
  unfold unpack4
  split
  · rename_i h
    obtain ⟨h1, h2⟩ := sNaN_widen x h
    rw [h1, h2]
  · rfl

theorem unpack4_of_not_nan (x : Nat) (h : ¬ dIsNaN (widen32 x) = true) : unpack4 x = widen32 x := by
  unfold unpack4
  split
  · rename_i hs
    exact absurd (sNaN_widen x hs).1 h
  · rfl

theorem dEq_unpack4 (x y : Nat) : dEq (unpack4 x) (unpack4 y) = dEq (widen32 x) (widen32 y) := by
  unfold dEq
  rw [unpack4_nan, unpack4_nan]
  by_cases h1 : dIsNaN (widen32 x) = true
  · simp [h1]
  by_cases h2 : dIsNaN (widen32 y) = true
  · simp [h2]
  rw [unpack4_of_not_nan x h1, unpack4_of_not_nan y h2]

/-- `unpack_cmp` on `Zd` and `Zf` is `==` on the items `tolist` gives: both parts, each as a C `==`, so
a NaN part makes an item differ from itself. The `Zf` items are read by `PyFloat_Unpack4`, which keeps
a signalling NaN, and compared as floats, which does not change the outcome. -/
def ComplexCmp : Prop :=
  ∀ (m : Mem) (p q : Int),
    (∃ a b, unpackRaw m p ['Z', 'd'] = .ok a ∧ unpackRaw m q ['Z', 'd'] = .ok b ∧
      unpackCmpNative m p q zdCode = .ok (itemEq a b)) ∧
    (∃ a b, unpackRaw m p ['Z', 'f'] = .ok a ∧ unpackRaw m q ['Z', 'f'] = .ok b ∧
      unpackCmpNative m p q zfCode = .ok (itemEq a b))

theorem complexCmp_proven : ComplexCmp := by
  intro m p q
  have hd : unpackCmpNative m p q zdCode =
      .ok (dEq (rdU m p 8) (rdU m q 8) && dEq (rdU m (p + 8) 8) (rdU m (q + 8) 8)) := rfl
  have hf : unpackCmpNative m p q zfCode =
      .ok (dEq (widen32 (rdU m p 4)) (widen32 (rdU m q 4)) &&
        dEq (widen32 (rdU m (p + 4) 4)) (widen32 (rdU m (q + 4) 4))) := rfl
  refine ⟨⟨_, _, rfl, rfl, ?_⟩, ⟨_, _, rfl, rfl, ?_⟩⟩
  · rw [hd]
    rfl
  · rw [hf]
    simp only [itemEq, dEq_unpack4]

/-- `pack_single` then `unpack_single` for `Zd` and `Zf`, for every memory: `Zd` stores both parts
exactly, and `Zf` reads back what `(float)` stored. Hypotheses: a live view; the item's space is in
the store; for `Zd`, parts that are doubles. -/
def PackUnpackComplex : Prop :=
  ∀ (st : St) (self : Nat) (ptr : Int), 0 ≤ ptr → ptr + 16 ≤ st.mem.length →
    baseInaccessible st self = false →
    (∀ a b : Nat, a < 2 ^ 64 → b < 2 ^ 64 → ∃ s,
      packSingle self ptr (.complex a b) ['Z', 'd'] st = (.ok (), s) ∧
      unpackRaw s.mem ptr ['Z', 'd'] = .ok (.complex a b)) ∧
    (∀ a b : Nat, ∃ s,
      packSingle self ptr (.complex a b) ['Z', 'f'] st = (.ok (), s) ∧
      unpackRaw s.mem ptr ['Z', 'f'] =
        .ok (.complex (unpack4 (narrow32 a % 2 ^ 32)) (unpack4 (narrow32 b % 2 ^ 32))))

theorem rdBytes_add (m : Mem) (p : Int) (i j : Nat) :
    rdBytes m p (i + j) = rdBytes m p i ++ rdBytes m (p + i) j := by
  induction i generalizing p with
  | zero => simp [rdBytes]
  | succ i ih =>
    have e : i + 1 + j = (i + j) + 1 := by omega
    rw [e]
    simp only [rdBytes, List.cons_append]
    rw [ih]
    have e2 : p + 1 + (i : Int) = p + ((i + 1 : Nat) : Int) := by omega
    rw [e2]

/-- The two parts of an item read back from the same store. -/
theorem rd_two (m : Mem) (p : Int) (k : Nat) (a b : Nat) (hp : 0 ≤ p) (h : p + (k + k : Nat) ≤ m.length) :
    rdU (wrBytes m p (encLE a k ++ encLE b k)) p k = a % 256 ^ k ∧
    rdU (wrBytes m p (encLE a k ++ encLE b k)) (p + k) k = b % 256 ^ k := by
  have h1 : rdBytes (wrBytes m p (encLE a k ++ encLE b k)) p (encLE a k ++ encLE b k).length =
      encLE a k ++ encLE b k := rdBytes_wrBytes m p _ hp (by simpa [encLE_length] using h)
  have hl : (encLE a k ++ encLE b k).length = k + k := by simp [encLE_length]
  rw [hl, rdBytes_add] at h1
  have h2 := List.append_inj h1 (by simp [rdBytes_length, encLE_length])
  simp only [rdU]
  rw [h2.1, h2.2, decLE_encLE, decLE_encLE]
  exact ⟨rfl, rfl⟩

theorem packUnpackComplex_proven : PackUnpackComplex := by
  intro st self ptr h0 h8 hl
  have hc := checkReleased_ok st self hl
  refine ⟨fun a b ha hb => ?_, fun a b => ?_⟩
  · refine ⟨{ st with mem := wrBytes st.mem ptr (encLE a 8 ++ encLE b 8) }, ?_, ?_⟩
    · simp only [packSingle, cc, List.getD_cons_zero, List.getD_cons_succ, M.bind_app, M.mapErr, complexAsC,
        M.pure_app, hc]
      rfl
    · obtain ⟨h1, h2⟩ := rd_two st.mem ptr 8 a b h0 (by omega)
      rw [Nat.mod_eq_of_lt (by omega)] at h1 h2
      show Except.ok (Item.complex (rdU _ ptr 8) (rdU _ (ptr + 8) 8)) = _
      rw [h1]
      have e : (ptr + ((8 : Nat) : Int)) = ptr + 8 := rfl
      rw [e] at h2
      rw [h2]
  · refine ⟨{ st with mem := wrBytes st.mem ptr (encLE (narrow32 a) 4 ++ encLE (narrow32 b) 4) }, ?_, ?_⟩
    · simp only [packSingle, cc, List.getD_cons_zero, List.getD_cons_succ, M.bind_app, M.mapErr, complexAsC,
        M.pure_app, hc]
      rfl
    · obtain ⟨h1, h2⟩ := rd_two st.mem ptr 4 (narrow32 a) (narrow32 b) h0 (by omega)
      show Except.ok (Item.complex (unpack4 (rdU _ ptr 4)) (unpack4 (rdU _ (ptr + 4) 4))) = _
      rw [h1]
      have e : (ptr + ((4 : Nat) : Int)) = ptr + 4 := rfl
      rw [e] at h2
      rw [h2]

/-- The `v == v` shortcut of `memory_richcompare`, memoryobject.c:3222-3244: a view of a format `struct`
knows that has no float is equal to itself, by that test alone, so it does not depend on the items.
`P`, the floats and the complex formats go on to the comparison; a `d` view holding a NaN is not equal
to itself. Hypothesis: a live view. -/
def SelfEqualShortcut : Prop :=
  (∀ (st : St) (v : Nat), baseInaccessible st v = false → selfEqualFormat (st.mv v).view.format = true →
    (memoryRichEqual v (.view v) st).1 = .ok (some true)) ∧
  (∀ c : Char, c ∈ "bBchHiIlLnNqQ?".toList → selfEqualFormat (some [c]) = true ∧
    selfEqualFormat (some ['@', c]) = true) ∧
  (∀ f : List Char, f ∈ [['d'], ['f'], ['e'], ['P'], ['Z', 'd'], ['Z', 'f'], ['@', 'd'], ['B', 'B']] →
    selfEqualFormat (some f) = false) ∧
  selfEqualFormat none = false

theorem selfEqualShortcut_proven : SelfEqualShortcut := by
  refine ⟨?_, by decide, by decide, rfl⟩
  intro st v h1 h2
  simp [memoryRichEqual, M.bind_app, M.get, h1, h2, M.pure_app]

end PyLean.BytesObj.Mem
