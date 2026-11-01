import PyLean.DictSet.DictProps
import PyLean.DictSet.Stable

/-!
A lying `__eq__`: one that answers anything, and may raise, but leaves the dict alone. The lookup
writes only through `__eq__` (`dictLookup_stable`), so such a comparison leaves the table identical,
and every invariant of it survives. A comparison that mutates the dict is a different question, and
this file does not answer it; note that `DKIX_KEY_CHANGED` does not catch every mutation either,
since a mutation that keeps the keys object and the entry passes the test at `dictobject.c:1062`
and `:1118`.
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type} [DecidableEq K]

/-- `__eq__` may lie in its boolean, or raise, but leaves the state it was given. -/
def EqPure (P : Proto K (PyDict K V)) : Prop := ∀ a b mp, (P.eq a b mp).2 = mp

/-- `_Py_dict_lookup` leaves the table identical when `__eq__` does, whatever it answers. -/
theorem dictLookup_pure (P : Proto K (PyDict K V)) (hp : EqPure P) (key : K) (hash : Int)
    (mp : PyDict K V) : (dictLookup P key hash mp).2 = mp :=
  dictLookup_stable P id hp key hash mp

/-- The table invariant survives a lying `__eq__`: after `_Py_dict_lookup` the dict is identical, so
`DictInv` still holds, whatever the comparison answered. -/
def InvUnderLyingEq : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)), EqPure P →
    ∀ (hf : K → Int) (eqv : K → K → Bool) (mp : PyDict K V), DictInv hf eqv P.isStr mp →
      ∀ (key : K) (hash : Int),
        (dictLookup P key hash mp).2 = mp ∧ DictInv hf eqv P.isStr (dictLookup P key hash mp).2

theorem invUnderLyingEq_proven : InvUnderLyingEq := by
  intro K V _ P hp hf eqv mp hd key hash
  have h := dictLookup_pure P hp key hash mp
  exact ⟨h, by rw [h]; exact hd⟩

end PyLean.DictSet
