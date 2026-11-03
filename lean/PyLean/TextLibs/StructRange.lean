import PyLean.TextLibs.StructFail

/-!
The out-of-range half of the integer codes. `IntCodesRoundTrip` covers every value inside an entry's
range; here is what happens to every value outside it, so a conversion or a pack routine that wrapped
silently would fail these statements.

`GetConversions` is the six `get_*` helpers of `Modules/_struct.c:139-256` with the `PyLong_As*` each
one calls, for every int and every failure of `get_pylong`. `NativeIntPack` is the twelve native
`np_*` integer routines of `Modules/_struct.c:524-737`, in every table that uses them, for every
value and every failure of `__index__`.
-/

namespace PyLean.TextLibs.Struct

open PyLean PyLean.TextLibs

set_option linter.unusedSimpArgs false

/-! ### `get_*` -/

theorem asC_spec (lo hi : Int) (m : String) (n : Int) :
    asC lo hi m n = if lo ≤ n ∧ n ≤ hi then .ok n else .error (.overflowError m) := by
  unfold asC
  by_cases h : lo ≤ n ∧ n ≤ hi
  · rw [if_neg (by omega), if_pos h]
  · rw [if_pos (by omega), if_neg h]

theorem longMin_eq : longMin = -9223372036854775808 := by decide
theorem longMax_eq : longMax = 9223372036854775807 := by decide
theorem ulongMax_eq : ulongMax = 18446744073709551615 := by decide

/-- The six `get_*` helpers on the int `get_pylong` returned: in range they return it, and out of range
they raise the `OverflowError` of the `PyLong_As*` they call, with its message
(`Objects/longobject.c:681, 749, 786, 801-802, 830, 839, 1131, 1250`). A failure of `get_pylong`
comes out unchanged. A `get_*` that wrapped an out-of-range int would fail this. -/
def GetConversions : Prop :=
  ∀ v : SV,
    (∀ e, getPylong v = .error e →
      getLong v = .error e ∧ getSsizeT v = .error e ∧ getLonglong v = .error e ∧
      getUlong v = .error e ∧ getUlonglong v = .error e ∧ getSizeT v = .error e) ∧
    (∀ n, getPylong v = .ok n →
      getLong v = (if -9223372036854775808 ≤ n ∧ n ≤ 9223372036854775807 then .ok n
        else .error (.overflowError "Python int too large to convert to C long")) ∧
      getSsizeT v = (if -9223372036854775808 ≤ n ∧ n ≤ 9223372036854775807 then .ok n
        else .error (.overflowError "Python int too large to convert to C ssize_t")) ∧
      getLonglong v = (if -9223372036854775808 ≤ n ∧ n ≤ 9223372036854775807 then .ok n
        else .error (.overflowError "int too big to convert")) ∧
      getUlong v = (if n < 0 then .error (.overflowError "can't convert negative value to unsigned int")
        else if n ≤ 18446744073709551615 then .ok n
        else .error (.overflowError "Python int too large to convert to C unsigned long")) ∧
      getUlonglong v = (if n < 0 then .error (.overflowError "can't convert negative int to unsigned")
        else if n ≤ 18446744073709551615 then .ok n
        else .error (.overflowError "int too big to convert")) ∧
      getSizeT v = (if n < 0 then .error (.overflowError "can't convert negative value to size_t")
        else if n ≤ 18446744073709551615 then .ok n
        else .error (.overflowError "Python int too large to convert to C size_t")))

/-- The unsigned helpers: a negative test, then `asC 0 ulongMax`. -/
theorem unsigned_conv (n : Int) (m1 m2 : String) :
    (do if n < 0 then throw (PyExc.overflowError m1)
        asC 0 ulongMax m2 n : Py Int)
      = (if n < 0 then .error (.overflowError m1)
         else if n ≤ 18446744073709551615 then .ok n else .error (.overflowError m2)) := by
  by_cases h : n < 0
  · simp [h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · rw [if_neg h, asC_spec, ulongMax_eq]
    by_cases h2 : n ≤ 18446744073709551615
    · simp [h, h2, bind, Except.bind, pure, Except.pure]
    · simp [h, h2, bind, Except.bind, pure, Except.pure]

theorem getConversions_proven : GetConversions := by
  intro v
  refine ⟨fun e h => ?_, fun n h => ?_⟩
  · simp [getLong, getSsizeT, getLonglong, getUlong, getUlonglong, getSizeT, h, bind, Except.bind]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [getLong, h, bind, Except.bind, asC_spec, longMin_eq, longMax_eq]
    · simp only [getSsizeT, h, bind, Except.bind, asC_spec, longMin_eq, longMax_eq]
    · simp only [getLonglong, h, bind, Except.bind, asC_spec, longMin_eq, longMax_eq]
    · simp only [getUlong, h]
      exact unsigned_conv n _ _
    · simp only [getUlonglong, h]
      exact unsigned_conv n _ _
    · simp only [getSizeT, h]
      exact unsigned_conv n _ _

/-! ### The native integer pack routines -/

/-- The range and width of each native integer pack routine on LP64, as `Modules/_struct.c` checks
them: `np_byte` (534), `np_ubyte` (551), `np_short` (581), `np_ushort` (600), `np_int` (619-622),
`np_uint` (640-643), and the `long`, `Py_ssize_t`, `size_t`, `long long` routines, whose only check is
the conversion's `OverflowError`. -/
def npIntSpec : PFn → Option (Int × Int × Nat)
  | .npByte => some (-128, 127, 1)
  | .npUbyte => some (0, 255, 1)
  | .npShort => some (-32768, 32767, 2)
  | .npUshort => some (0, 65535, 2)
  | .npInt => some (-2147483648, 2147483647, 4)
  | .npUint => some (0, 4294967295, 4)
  | .npLong | .npSsizeT | .npLonglong => some (-9223372036854775808, 9223372036854775807, 8)
  | .npUlong | .npSizeT | .npUlonglong => some (0, 18446744073709551615, 8)
  | _ => none

/-- The message every native integer routine raises outside its range. -/
def npRangeMsg (e : FormatDef) (lo hi : Int) : PyExc :=
  structErr s!"'{e.name}' format requires {lo} <= number <= {hi}"

/-- Every native integer routine, in every table that uses it (the native table, `b` and `B` in the
standard tables, and the routines `init_endian_tables` swaps into the little-endian table). For the
int that `__index__` gives, it writes the `nb`-byte two's-complement image inside the range and
raises `struct.error` with the exact range outside it. An `OverflowError` from `__index__` is that
same range error, and every other exception from it comes out unchanged. A pack that wrapped or
truncated an out-of-range value, or that skipped a range check, would fail this. -/
def NativeIntPack : Prop :=
  ∀ (t : Tab) (e : FormatDef) (lo hi : Int) (nb : Nat), e ∈ t.table →
    npIntSpec e.pack = some (lo, hi, nb) → ∀ v : SV,
      (∀ n, getPylong v = .ok n →
        runPack e v = if lo ≤ n ∧ n ≤ hi then .ok (twos nb n) else .error (npRangeMsg e lo hi)) ∧
      (∀ m, getPylong v = .error (.overflowError m) → runPack e v = .error (npRangeMsg e lo hi)) ∧
      (∀ x, getPylong v = .error x → (∀ m, x ≠ .overflowError m) → runPack e v = .error x)

/-- Whether a native integer routine reports an unsigned range (`RANGE_ERROR(state, f, 1)`). -/
def npIsUnsigned : PFn → Bool
  | .npUbyte | .npUshort | .npUint | .npUlong | .npSizeT | .npUlonglong => true
  | _ => false

/-- The error each native integer routine raises outside its range: `_range_error`, or the
messages of its own that `np_longlong` and `np_ulonglong` format. -/
def npErr (e : FormatDef) : PyExc :=
  match e.pack with
  | .npLonglong => llRangeErr e
  | .npUlonglong => ullRangeErr e
  | p => rangeError e (npIsUnsigned p)

/-- The table facts the proof needs, as a `Bool` check. -/
def npEntryOk (e : FormatDef) : Bool :=
  match npIntSpec e.pack with
  | some (lo, hi, nb) => e.size == nb && npErr e == npRangeMsg e lo hi
  | none => true

/-- In every table, each native integer entry has the routine's width as its size, and `_range_error`
with the routine's signedness prints the routine's range. -/
theorem np_tables : ∀ t : Tab, ∀ e ∈ t.table, npEntryOk e = true := by
  intro t
  cases t <;> decide +kernel

theorem orRange_err (f : FormatDef) (u : Bool) (x : PyExc) (hx : ∀ m, x ≠ .overflowError m) :
    orRange f u (.error x) = .error x := by
  cases x with
  | overflowError m => exact absurd rfl (hx m)
  | _ => rfl

/-- The law for one routine, on an int, given the entry's size and range message. -/
theorem np_law_ok (e : FormatDef) (lo hi : Int) (nb : Nat) (hspec : npIntSpec e.pack = some (lo, hi, nb))
    (hs : e.size = nb) (hm : npErr e = npRangeMsg e lo hi) (v : SV) (n : Int)
    (h : getPylong v = .ok n) :
    runPack e v = if lo ≤ n ∧ n ≤ hi then .ok (twos nb n) else .error (npRangeMsg e lo hi) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (getConversions_proven v).2 n h
  by_cases hA : -9223372036854775808 ≤ n ∧ n ≤ 9223372036854775807 <;> by_cases hN : n < 0 <;>
    by_cases hU : n ≤ 18446744073709551615 <;> by_cases hC : lo ≤ n ∧ n ≤ hi <;>
    by_cases hD : n < lo ∨ n > hi <;>
    revert hspec hm hC hD <;>
  cases hp : e.pack <;> intro hspec hm hC hD <;> simp only [npIntSpec, reduceCtorEq] at hspec <;>
    simp only [Option.some.injEq, Prod.mk.injEq] at hspec <;> obtain ⟨rfl, rfl, rfl⟩ := hspec <;>
    simp only [npErr, npIsUnsigned, hp] at hm <;>
    simp only [runPack, hp, h1, h2, h3, h4, h5, h6, hs, npSigned, npUnsigned, longMin_eq,
      longMax_eq, ulongMax_eq] <;>
    simp only [hA, hN, hU, hC, hD, and_self, true_and, and_true, false_and, and_false, or_self,
      true_or, or_true, false_or, or_false, if_true, if_false, ↓reduceIte, orRange, bind, Except.bind,
      pure, Except.pure, hm, hs] <;>
    first | rfl | (exfalso; omega) | (split <;> first | rfl | (exfalso; omega))

theorem np_law_ovf (e : FormatDef) (lo hi : Int) (nb : Nat) (hspec : npIntSpec e.pack = some (lo, hi, nb))
    (hm : npErr e = npRangeMsg e lo hi) (v : SV) (m : String)
    (h : getPylong v = .error (.overflowError m)) :
    runPack e v = .error (npRangeMsg e lo hi) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (getConversions_proven v).1 _ h
  revert hspec hm
  cases hp : e.pack <;> intro hspec hm <;> simp only [npIntSpec, reduceCtorEq] at hspec <;>
    simp only [Option.some.injEq, Prod.mk.injEq] at hspec <;> obtain ⟨rfl, rfl, rfl⟩ := hspec <;>
    simp only [npErr, npIsUnsigned, hp] at hm <;>
    simp only [runPack, hp, h1, h2, h3, h4, h5, h6, orRange, bind, Except.bind, hm]
  all_goals first | rfl | (rw [← hm]; rfl)

theorem np_law_err (e : FormatDef) (lo hi : Int) (nb : Nat) (hspec : npIntSpec e.pack = some (lo, hi, nb))
    (v : SV) (x : PyExc) (h : getPylong v = .error x) (hx : ∀ m, x ≠ .overflowError m) :
    runPack e v = .error x := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (getConversions_proven v).1 _ h
  revert hspec
  cases hp : e.pack <;> intro hspec <;> simp only [npIntSpec, reduceCtorEq] at hspec <;>
    simp only [runPack, hp, h1, h2, h3, h4, h5, h6, orRange_err _ _ x hx, bind, Except.bind]
  all_goals cases x with
    | overflowError m => exact absurd rfl (hx m)
    | _ => rfl

theorem nativeIntPack_proven : NativeIntPack := by
  intro t e lo hi nb he hspec v
  have ht := np_tables t e he
  simp only [npEntryOk, hspec, Bool.and_eq_true, beq_iff_eq] at ht
  exact ⟨fun n h => np_law_ok e lo hi nb hspec ht.1 ht.2 v n h,
    fun m h => np_law_ovf e lo hi nb hspec ht.2 v m h,
    fun x h hx => np_law_err e lo hi nb hspec v x h hx⟩

/-! ### `?` -/

/-- `np_bool` and `bp_bool` write exactly one byte, `0x01` for a true object and `0x00` for a false one
(`_Bool x = y; memcpy(p, &x, sizeof x)`, `Modules/_struct.c:745-749`), in every table, and `?` reads
that byte back as the truth value. A raising `__bool__` raises out (`BoolRaises`). A pack that wrote
`[]`, `[2]` or two bytes for `True` fails this. -/
def BoolPacksByte : Prop :=
  ∀ (t : Tab) (e : FormatDef), e ∈ t.table → e.format = ['?'] →
    ∀ (v : SV) (b : Bool), isTrue v = .ok b →
      runPack e v = .ok [if b then 0x01 else 0x00] ∧ runUnpack e [if b then 0x01 else 0x00] = .ok (.bool b)

theorem bool_tables : ∀ t : Tab, ∀ e ∈ t.table, e.format = ['?'] →
    (e.pack = .npBool ∨ e.pack = .bpBool) ∧ (e.unpack = .nuBool ∨ e.unpack = .buBool) := by
  intro t
  cases t <;> decide +kernel

theorem boolPacksByte_proven : BoolPacksByte := by
  intro t e he hf v b h
  obtain ⟨hp, hu⟩ := bool_tables t e he hf
  constructor
  · rcases hp with hp | hp <;> simp [runPack, hp, h, bind, Except.bind, pure, Except.pure]
  · rcases hu with hu | hu <;> cases b <;> simp [runUnpack, hu]

end PyLean.TextLibs.Struct
