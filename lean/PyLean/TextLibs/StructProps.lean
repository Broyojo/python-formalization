import PyLean.TextLibs.StructModel

/-!
Properties of the `struct` model. Refutations carry the concrete counterexample
that the matching `bugs/textlibs-*.yaml` reproducer runs on CPython.
-/

namespace PyLean.TextLibs.Struct

open PyLean PyLean.TextLibs

/-! ### Refuted: the implementation disagreeing with itself -/

/-- 1e300 as a bit pattern. -/
def f1e300 : Nat := 0x7E37E43C8800759C

/-- Little- and big-endian `F` accept the same values: a format's byte order changes
the bytes, never whether a value can be packed. -/
def StdComplexOrderAgree : Prop :=
  ∀ v : SV, (modPack (.str ['<'.toNat, 'F'.toNat]) [v]).toBool
    = (modPack (.str ['>'.toNat, 'F'.toNat]) [v]).toBool

theorem stdComplexOrderAgree_refuted : ¬StdComplexOrderAgree := by
  intro h
  have := h (.float f1e300)
  revert this
  decide

/-- The module functions behave like `Struct(fmt)`: `pack(fmt, ...)` and `Struct(fmt).pack(...)` give the
same result for every hashable format object. `bytes` go through the cache key and `Struct` through
`set_format`, and both decode with `surrogateescape`. An unhashable format fails at the cache instead,
with its own message, and a `__hash__` that raises fails there too, so those are outside the statement.
A wrong `decodeSurrogate` on one path would fail this. -/
def ModuleMatchesStruct : Prop :=
  ∀ (f : FmtArg) (args : List SV), (∀ t, f ≠ .other t false) → (∀ t e, f ≠ .hashRaises t e) →
    modPack f args = (do structPack (← structInit f) args)

theorem moduleMatchesStruct_proven : ModuleMatchesStruct := by
  intro f args h1 h2
  cases f with
  | str s => rfl
  | bytes b => rfl
  | other t k =>
    cases k with
    | true => rfl
    | false => exact absurd rfl (h1 t)
  | hashRaises t e => exact absurd rfl (h2 t e)

/-- An `__index__` object packs like the int it stands for: same bytes or same error. -/
def PIndexLikeInt : Prop :=
  ∀ n : Int, modPack (.str ['P'.toNat]) [.index n] = modPack (.str ['P'.toNat]) [.int n]

theorem pIndexLikeInt_refuted : ¬PIndexLikeInt := by
  intro h
  have := h (2 ^ 64)
  revert this
  decide

/-- `pack_into` changes no byte outside the `calcsize(fmt)` bytes at `offset`. 3.14 wrote the count byte of
a `0p` field past the end; the count is now written only when `n > 0`. -/
def PackIntoStaysInside : Prop :=
  ∀ (f : FmtArg) (s : SObj) (buf out : List Nat) (o : Nat) (args : List SV),
    cacheStruct f = .ok s → modPackInto f buf o args = .ok out →
    out.drop (o + s.sSize) = buf.drop (o + s.sSize)

/-! ### Proven: tables and layout -/

/-- `init_endian_tables` swaps exactly the entries whose native size matches, except `?`, and changes no
format, size or alignment. -/
def EndianTableSwap : Prop :=
  lilendianTable.map (fun e => (e.format, e.size, e.alignment))
      = lilendianTable0.map (fun e => (e.format, e.size, e.alignment)) ∧
  (lilendianTable.filter (fun e => e.format = ['F'] ∨ e.format = ['D'] ∨ e.format = ['Z', 'f'] ∨
      e.format = ['Z', 'd'])).map (·.pack)
      = [.npFloatComplex, .npDoubleComplex, .npFloatComplex, .npDoubleComplex] ∧
  (lilendianTable.filter (fun e => e.format = ['f'] ∨ e.format = ['d'] ∨ e.format = ['?'])).map (·.pack)
      = [.bpBool, .npFloat, .npDouble] ∧
  (lilendianTable.filter (fun e => e.format = ['l'] ∨ e.format = ['L'])).map (·.pack)
      = [.lpInt, .lpUint]

theorem endianTableSwap_proven : EndianTableSwap := by
  unfold EndianTableSwap
  decide

/-- `align` returns the next multiple of the alignment, or `none` only when that would
pass `PY_SSIZE_T_MAX`. -/
def AlignNextMultiple : Prop :=
  ∀ (size : Nat) (e : FormatDef), size ≤ maxN → e.alignment ≠ 0 →
    match align size e with
    | some r => r % e.alignment = 0 ∧ size ≤ r ∧ r < size + e.alignment ∧ r ≤ maxN
    | none => size + (e.alignment - 1 - (size - 1) % e.alignment) > maxN

theorem alignNextMultiple_proven : AlignNextMultiple := by
  intro size e hs ha
  have hpos : 0 < e.alignment := Nat.pos_of_ne_zero ha
  unfold align
  by_cases h0 : size > 0
  · have hm := Nat.mod_lt (size - 1) hpos
    have hd := Nat.div_add_mod (size - 1) e.alignment
    generalize (size - 1) % e.alignment = m at hm hd ⊢
    generalize (size - 1) / e.alignment = q at hd
    have hcond : e.alignment ≠ 0 ∧ size > 0 := ⟨ha, h0⟩
    simp only [if_pos hcond]
    by_cases hx : e.alignment - 1 - m > maxN - size
    · rw [if_pos hx]
      show size + (e.alignment - 1 - m) > maxN
      omega
    · rw [if_neg hx]
      show (size + (e.alignment - 1 - m)) % e.alignment = 0 ∧ size ≤ size + (e.alignment - 1 - m) ∧
        size + (e.alignment - 1 - m) < size + e.alignment ∧ size + (e.alignment - 1 - m) ≤ maxN
      have hr : size + (e.alignment - 1 - m) = e.alignment * (q + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      refine ⟨?_, by omega, by omega, by omega⟩
      rw [hr]
      exact Nat.mul_mod_right _ _
  · have hz : size = 0 := by omega
    subst hz
    have hcond : ¬(e.alignment ≠ 0 ∧ 0 > 0) := by omega
    simp only [if_neg hcond]
    exact ⟨Nat.zero_mod _, Nat.le_refl _, by omega, by omega⟩

/-! ### Proven: byte conversions -/

theorem leVal_leBytes : ∀ (i x : Nat), leVal (leBytes i x) = x % 2 ^ (8 * i)
  | 0, x => by simp [leBytes, leVal, Nat.mod_one]
  | i + 1, x => by
    simp only [leBytes, leVal, leVal_leBytes i (x / 256)]
    have h : 2 ^ (8 * (i + 1)) = 256 * 2 ^ (8 * i) := by
      rw [Nat.mul_add, Nat.pow_add, Nat.mul_comm]
    rw [h, Nat.mod_mul]

/-- `pack` then `unpack` is the identity on every in-range integer of width `size`,
for the native two's-complement image (`np_*` then `nu_*`). -/
def NativeSignedRoundTrip : Prop :=
  ∀ (size : Nat) (x : Int), size ≠ 0 →
    -(2 ^ (size * 8 - 1) : Int) ≤ x → x < 2 ^ (size * 8 - 1) →
    signedOf size (leVal (twos size x)) = x

theorem nativeSignedRoundTrip_proven : NativeSignedRoundTrip := by
  intro size x hsize hlo hhi
  have hM : (2 : Nat) ^ (size * 8) = 2 * 2 ^ (size * 8 - 1) := by
    have : size * 8 = (size * 8 - 1) + 1 := by omega
    conv => lhs; rw [this, Nat.pow_succ, Nat.mul_comm]
  have hMi : (2 : Int) ^ (size * 8) = 2 * 2 ^ (size * 8 - 1) := by
    exact_mod_cast hM
  have hHpos : (0 : Int) < 2 ^ (size * 8 - 1) := Int.pow_pos (by decide)
  have hNonneg : 0 ≤ x % (2 : Int) ^ (size * 8) :=
    Int.emod_nonneg _ (by rw [hMi]; omega)
  have hLt : x % (2 : Int) ^ (size * 8) < 2 ^ (size * 8) :=
    Int.emod_lt_of_pos _ (by rw [hMi]; omega)
  have hval : ((x % (2 : Int) ^ (size * 8)).toNat : Nat) % 2 ^ (8 * size)
      = (x % (2 : Int) ^ (size * 8)).toNat := by
    apply Nat.mod_eq_of_lt
    rw [Nat.mul_comm 8]
    have : ((x % (2 : Int) ^ (size * 8)).toNat : Int) < ((2 ^ (size * 8) : Nat) : Int) := by
      rw [Int.toNat_of_nonneg hNonneg]
      exact_mod_cast hLt
    exact_mod_cast this
  unfold twos signedOf
  rw [leVal_leBytes, hval]
  by_cases hx : 0 ≤ x
  · have hm : x % (2 : Int) ^ (size * 8) = x := Int.emod_eq_of_lt hx (by rw [hMi]; omega)
    rw [hm]
    have hnot : ¬ (x.toNat ≥ 2 ^ (size * 8 - 1)) := by
      intro hge
      have : (x.toNat : Int) ≥ ((2 ^ (size * 8 - 1) : Nat) : Int) := by exact_mod_cast hge
      rw [Int.toNat_of_nonneg hx] at this
      have h2 : ((2 ^ (size * 8 - 1) : Nat) : Int) = 2 ^ (size * 8 - 1) := by norm_cast
      omega
    rw [if_neg hnot, Int.toNat_of_nonneg hx]
  · have hneg : x < 0 := by omega
    have hm : x % (2 : Int) ^ (size * 8) = x + 2 ^ (size * 8) := by
      have h2 : (x + (2 : Int) ^ (size * 8)) % 2 ^ (size * 8) = x % 2 ^ (size * 8) := by simp
      rw [← h2]
      exact Int.emod_eq_of_lt (by rw [hMi]; omega) (by rw [hMi]; omega)
    rw [hm]
    have hp : 0 ≤ x + (2 : Int) ^ (size * 8) := by rw [hMi]; omega
    have hge : (x + (2 : Int) ^ (size * 8)).toNat ≥ 2 ^ (size * 8 - 1) := by
      have : ((x + (2 : Int) ^ (size * 8)).toNat : Int) ≥ ((2 ^ (size * 8 - 1) : Nat) : Int) := by
        rw [Int.toNat_of_nonneg hp]
        have h2 : ((2 ^ (size * 8 - 1) : Nat) : Int) = 2 ^ (size * 8 - 1) := by norm_cast
        rw [hMi]; omega
      exact_mod_cast this
    rw [if_pos hge, Int.toNat_of_nonneg hp]
    omega

def NativeUnsignedRoundTrip : Prop :=
  ∀ (size : Nat) (x : Nat), x < 2 ^ (size * 8) → leVal (leBytes size x) = x

theorem nativeUnsignedRoundTrip_proven : NativeUnsignedRoundTrip := by
  intro size x h
  rw [leVal_leBytes, Nat.mul_comm 8, Nat.mod_eq_of_lt h]

/-! ### Proven: pack length -/

theorem overlay_length_ge (buf w : List Nat) (i : Nat) :
    buf.length ≤ (overlay buf i w).length := by
  simp only [overlay, List.length_append, List.length_take, List.length_drop]
  omega

/-- A successful `'s'` field holds the first `size` bytes of the value, NUL padded. -/
def PackSPads : Prop :=
  ∀ (code : Code) (p res : List Nat), res.length = code.size → (∀ b ∈ res, b = 0) →
    packS code (.bytes p) res
      = .ok (p.take code.size ++ List.replicate (code.size - p.length) 0)

/-- `?` reads any non-zero byte as `True` in all three tables. -/
def BoolAnyNonzero : Prop :=
  ∀ (b : Nat) (rest : List Nat),
    (runUnpack ⟨['?'], 1, 1, .nuBool, .npBool⟩ (b :: rest) = .ok (.bool (b != 0))) ∧
    (runUnpack ⟨['?'], 1, 0, .buBool, .bpBool⟩ (b :: rest) = .ok (.bool (b != 0)))

theorem packSPads_proven : PackSPads := by
  intro code p res hlen hz
  have hres : res = List.replicate code.size 0 := by
    apply List.eq_replicate_iff.mpr
    exact ⟨hlen, fun b hb => hz b hb⟩
  subst hres
  simp only [packS]
  by_cases h : p.length > code.size
  · simp only [if_pos h, List.drop_replicate]
    have : code.size - code.size = 0 := by omega
    have h2 : code.size - p.length = 0 := by omega
    simp [this, h2]
  · simp only [if_neg h, List.drop_replicate]
    have h3 : p.take p.length = p := List.take_length
    have h4 : p.take code.size = p := List.take_of_length_le (by omega)
    rw [h3, h4]

theorem boolAnyNonzero_proven : BoolAnyNonzero := by
  intro b rest
  constructor <;> (cases b <;> simp [runUnpack])

/-- `unpack` rejects every buffer whose length is not `s_size`, with the source message. -/
def UnpackWrongLength : Prop :=
  ∀ (s : SObj) (buf : List Nat), buf.length ≠ s.sSize →
    structUnpack s buf = .error (structErr s!"unpack requires a buffer of {s.sSize} bytes")

theorem unpackWrongLength_proven : UnpackWrongLength := by
  intro s buf h
  simp [structUnpack, h]

/-- `iter_unpack` rejects a zero-sized struct before looking at the buffer. -/
def IterUnpackZeroSize : Prop :=
  ∀ (s : SObj) (buf : List Nat), s.sSize = 0 →
    structIterUnpack s buf
      = .error (structErr "cannot iteratively unpack with a struct of length 0")

theorem iterUnpackZeroSize_proven : IterUnpackZeroSize := by
  intro s buf h
  simp [structIterUnpack, h]

/-- `pack` rejects a wrong argument count before converting any argument. -/
def PackWrongCount : Prop :=
  ∀ (s : SObj) (args : List SV), args.length ≠ s.sLen →
    structPack s args
      = .error (structErr s!"pack expected {s.sLen} items for packing (got {args.length})")

theorem packWrongCount_proven : PackWrongCount := by
  intro s args h
  simp [structPack, h]

end PyLean.TextLibs.Struct
