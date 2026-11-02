import PyLean.Core

/-!
The local-time type `zoneinfo` uses for instants before a file's first transition, in the C
accelerator (`ttinfo_before`, Modules/_zoneinfo.c:1170-1182) and the pure-Python twin
(`_tti_before`, Lib/zoneinfo/_zoneinfo.py:250-262). Types are given by index; `isdst` is the
file's flag per type and `transIdx` the type of each transition. RFC 8536 §3.2 names time type 0
for that period; both twins first look for the first non-DST type.
-/

namespace PyLean.TextLibs.Zoneinfo

/-- C: the first non-DST type, else type 0 if there are any types, else none. -/
def beforeC (isdst : List Bool) (_transIdx : List Nat) : Option Nat :=
  match isdst.findIdx? (· = false) with
  | some i => some i
  | none => if isdst = [] then none else some 0

/-- Python: the first non-DST type, else `self._ttinfos[0]`, the type of the first transition
(`self._ttinfos` holds one ttinfo per transition), else none. -/
def beforePy (isdst : List Bool) (transIdx : List Nat) : Option Nat :=
  match isdst.findIdx? (· = false) with
  | some i => some i
  | none => transIdx.head?

/-- The twins pick the same type for every file with at least one transition. -/
def BeforeTwins : Prop :=
  ∀ (isdst : List Bool) (transIdx : List Nat), transIdx ≠ [] → (∀ i ∈ transIdx, i < isdst.length) →
    beforeC isdst transIdx = beforePy isdst transIdx

/-- Two DST types and a first transition to type 1: C uses type 0, Python type 1. -/
theorem beforeTwins_refuted : ¬ BeforeTwins := by
  intro h
  have := h [true, true] [1] (by decide) (by decide)
  revert this
  decide

/-- With a non-DST type, or with the first transition naming type 0, they agree (transition
indices are below the type count, which `_common.load_data` checks). -/
def BeforeTwinsNarrow : Prop :=
  ∀ (isdst : List Bool) (transIdx : List Nat),
    (isdst.any (· = false) ∨ transIdx.head? = some 0) → transIdx ≠ [] →
    (∀ i ∈ transIdx, i < isdst.length) → beforeC isdst transIdx = beforePy isdst transIdx

theorem beforeTwinsNarrow_proven : BeforeTwinsNarrow := by
  intro isdst transIdx h hne hidx
  unfold beforeC beforePy
  cases hf : isdst.findIdx? (· = false) with
  | some i => rfl
  | none =>
    rcases h with h | h
    · exfalso
      rw [List.findIdx?_eq_none_iff] at hf
      obtain ⟨x, hx, hx'⟩ := List.any_eq_true.mp h
      exact absurd (hf x hx) (by simpa using hx')
    · rw [h]
      cases isdst with
      | nil =>
        cases transIdx with
        | nil => exact absurd rfl hne
        | cons j _ => exact absurd (hidx j (by simp)) (by simp)
      | cons _ _ => rfl

end PyLean.TextLibs.Zoneinfo
