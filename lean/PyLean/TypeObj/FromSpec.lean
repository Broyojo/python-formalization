import PyLean.TypeObj.Model

/-!
The instance layout `PyType_FromMetaclass` computes for a type made from a `PyType_Spec`
(`Objects/typeobject.c`, CPython 3.15.2): `_align_up`, the size calculation of `:5628-5642`, and
`PyType_GetTypeDataSize`. Python sees the result as `__basicsize__`.
-/

namespace PyLean.TypeObj

/-- `ALIGNOF_MAX_ALIGN_T`: 16 in the `pyconfig.h` of the 3.15.2 x86-64 Linux build and on 64-bit
macOS (`Include/pymacconfig.h:81`). A power of two. -/
def alignofMaxAlignT : Int := 16

/-- `_align_up`, `Objects/typeobject.c:5193-5196`: `(size + A - 1) & ~(A - 1)` for `A` a power of
two. `x & ~(A - 1)` clears the low bits of `x`, which in two's complement is `x - x mod A` with a
non-negative remainder. Sizes here are a `tp_basicsize` and a spec size, far from overflow. -/
def alignUp (size : Int) : Int :=
  let x := size + alignofMaxAlignT - 1
  x - x % alignofMaxAlignT

/-- The sizes `PyType_FromMetaclass` takes from `spec->basicsize`, `:5339-5344`: a positive one is
the basic size, a negative one asks to extend the base by that many bytes. -/
def specSizes (specBasicsize : Int) : Int × Int :=
  (if specBasicsize > 0 then specBasicsize else 0, if specBasicsize < 0 then -specBasicsize else 0)

/-- "Calculate sizes", `Objects/typeobject.c:5626-5642`, for a base of `tp_basicsize`
`baseBasicsize`: the result is `(type_data_offset, tp_basicsize)`. Extending puts the type's data
at the base size rounded up and rounds the extra size up too (`:5629-5633`); a size of 0 inherits
the base's (`:5640-5643`). The `SystemError` for extending a variable-size base (`:5635-5638`)
is not modelled: the bases here are fixed-size. -/
def fromMetaclassSizes (baseBasicsize basicsize extra : Int) : Int × Int :=
  let off := if extra != 0 then alignUp baseBasicsize else basicsize
  let bs := if extra != 0 then alignUp baseBasicsize + alignUp extra else basicsize
  (off, if bs == 0 then baseBasicsize else bs)

/-- `PyType_GetTypeDataSize`, `Objects/typeobject.c:6153-6160`: the bytes after the base's
rounded-up size, 0 when there are none. -/
def typeDataSize (clsBasicsize baseBasicsize : Int) : Int :=
  let r := clsBasicsize - alignUp baseBasicsize
  if r < 0 then 0 else r

/-- **`_align_up` rounds up to the alignment.** For every size, the result is the least multiple
of `ALIGNOF_MAX_ALIGN_T` (16) at or above it: a multiple of 16, not below the size, and less than
16 above it. -/
def AlignUpExact : Prop :=
  ∀ s : Int, alignUp s % 16 = 0 ∧ s ≤ alignUp s ∧ alignUp s < s + 16

theorem alignUpExact_proven : AlignUpExact := by
  intro s
  simp only [alignUp, alignofMaxAlignT]
  refine ⟨?_, ?_, ?_⟩
  · simp [Int.sub_emod, Int.emod_emod_of_dvd]
  · have h1 := Int.emod_lt_of_pos (s + 16 - 1) (by decide : (0 : Int) < 16)
    omega
  · have h0 := Int.emod_nonneg (s + 16 - 1) (by decide : (16 : Int) ≠ 0)
    omega

/-- **The layout of a type made from a spec.** `PyType_FromMetaclass`, `Objects/typeobject.c:
5339-5344`, `:5626-5643`, and `PyType_GetTypeDataSize` (`:6153-6160`), for a base of size `base`:
* a negative `spec->basicsize = -n` extends the base: the type's data starts at the base size
  rounded up to 16 (`_align_up`), and `tp_basicsize` is that plus `n` rounded up to 16, so the
  data holds at least `n` bytes, begins at or after the base's end, and `PyType_GetTypeDataSize`
  is `n` rounded up;
* a positive one is `tp_basicsize` as it is, with the data offset that size;
* 0 inherits the base's `tp_basicsize`, and there is no type data.
Checked on 3.15.2 with `_testlimitedcapi.make_sized_heaptypes` (base of `16 + e` bytes, `e` and
the spec size): `(1, -1)` gives `__basicsize__` 48, data at 32, 16 bytes; `(5, -100)` gives 144,
32, 112; `(0, 0)` gives 16, no data. -/
def FromSpecSizesExact : Prop :=
  ∀ (base spec : Int), 0 ≤ base →
    let r := fromMetaclassSizes base (specSizes spec).1 (specSizes spec).2
    (spec < 0 →
      r.1 = alignUp base ∧ r.2 = alignUp base + alignUp (-spec) ∧ base ≤ r.1 ∧ r.1 % 16 = 0 ∧
        -spec ≤ r.2 - r.1 ∧ r.2 % 16 = 0 ∧ typeDataSize r.2 base = alignUp (-spec)) ∧
    (spec > 0 → r.1 = spec ∧ r.2 = spec) ∧
    (spec = 0 → r.1 = 0 ∧ r.2 = base ∧ typeDataSize r.2 base = 0)

theorem fromSpecSizesExact_proven : FromSpecSizesExact := by
  intro base spec _ r
  have ha := alignUpExact_proven base
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have hb := alignUpExact_proven (-spec)
    have hs : specSizes spec = (0, -spec) := by simp [specSizes]; omega
    have hne : (-spec != 0) = true := by simp; omega
    have hpos : (alignUp base + alignUp (-spec) == 0) = false := by simp; omega
    have hr : r = (alignUp base, alignUp base + alignUp (-spec)) := by
      simp only [r, hs, fromMetaclassSizes, hne, ite_true, hpos, Bool.false_eq_true, ite_false]
    rw [hr]
    refine ⟨rfl, rfl, ha.2.1, ha.1, by simp; omega, by simp; omega, ?_⟩
    have : ¬ (alignUp base + alignUp (-spec) - alignUp base < 0) := by omega
    simp only [typeDataSize, this, ite_false]; omega
  · have hs : specSizes spec = (spec, 0) := by simp [specSizes]; omega
    have h0 : (spec == 0) = false := by simp; omega
    have hr : r = (spec, spec) := by simp [r, hs, fromMetaclassSizes, h0]
    rw [hr]; exact ⟨rfl, rfl⟩
  · subst h
    have hr : r = (0, base) := by simp [r, specSizes, fromMetaclassSizes]
    rw [hr]
    refine ⟨rfl, rfl, ?_⟩
    have : base - alignUp base < 0 ∨ base - alignUp base = 0 := by omega
    simp only [typeDataSize]
    split <;> omega

def AlignUpLayout : Prop := AlignUpExact ∧ FromSpecSizesExact
theorem alignUpLayout_proven : AlignUpLayout := ⟨alignUpExact_proven, fromSpecSizesExact_proven⟩

/-- The difftest's view: `_testlimitedcapi.make_sized_heaptypes(e, spec)` makes a base of
`sizeof(PyObject) + e` = `16 + e` bytes and a subclass from `spec`; it reports the subclass's
`__basicsize__`, the offset of its type data (`PyObject_GetTypeData`, `_align_up` of the base's
size, `:6140-6144`) and `PyType_GetTypeDataSize`. -/
def sizedHeaptypes (e spec : Int) : List Int :=
  let base := 16 + e
  let r := fromMetaclassSizes base (specSizes spec).1 (specSizes spec).2
  [r.2, alignUp base, typeDataSize r.2 base]

end PyLean.TypeObj
