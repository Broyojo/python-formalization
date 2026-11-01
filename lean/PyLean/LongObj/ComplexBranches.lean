import PyLean.LongObj.ComplexCore

/-!
The branch structure of the NaN and infinity recovery in `_Py_c_prod` and
`_Py_c_quot`, over every `CDouble` instance. A ring or a field never reaches this
code (`ComplexAlgebra.lean`), so these statements record which branch runs, and in
which order, without saying anything about rounding. That the recovery produces an
infinity where C11 Annex G asks for one is a binary64 statement, and stays open.
-/

namespace PyLean.LongObj.Cplx

open CDouble

section

variable {R : Type} [CDouble R]

theorem prodBoxZ_of (s : ProdSt R) (h : (isinf s.a || isinf s.b) = false) : prodBoxZ s = s := by
  simp [prodBoxZ, h]

theorem prodBoxW_of (s : ProdSt R) (h : (isinf s.c || isinf s.d) = false) : prodBoxW s = s := by
  simp [prodBoxW, h]

theorem prodOverflow_of (ac bd ad bc : R) (s : ProdSt R)
    (h : (isinf ac || isinf bd || isinf ad || isinf bc) = false) :
    prodOverflow ac bd ad bc s = s := by
  simp [prodOverflow, h]

theorem prodBoxW_recalc (s : ProdSt R) (h : s.recalc = true) : (prodBoxW s).recalc = true := by
  simp only [prodBoxW]
  split
  · rfl
  · exact h

theorem prodOverflow_recalc (ac bd ad bc : R) (s : ProdSt R) (h : s.recalc = true) :
    (prodOverflow ac bd ad bc s).recalc = true := by
  simp only [prodOverflow]
  split
  · rfl
  · exact h

end

/-- `_Py_c_prod`, lines 94-147. The plain product is returned unless both of its parts
are NaN. If they are, it is still returned when neither operand and no partial
product is infinite, so NaN stays NaN. An infinite operand takes the first or second
box, which sets `recalc`, and the result is the recomputed one. -/
def CProdBranchOrder : Prop :=
  ∀ (R : Type) [CDouble R] (z w : Cx R),
    let a := z.real
    let b := z.imag
    let c := w.real
    let d := w.imag
    let r : Cx R := ⟨a *. c -. b *. d, a *. d +. b *. c⟩
    let s := prodOverflow (a *. c) (b *. d) (a *. d) (b *. c)
      (prodBoxW (prodBoxZ ⟨a, b, c, d, false⟩))
    ((isnan r.real && isnan r.imag) = false → c_prod z w = r) ∧
    ((isinf a || isinf b) = false → (isinf c || isinf d) = false →
      (isinf (a *. c) || isinf (b *. d) || isinf (a *. d) || isinf (b *. c)) = false →
      c_prod z w = r) ∧
    ((isnan r.real && isnan r.imag) = true → (isinf a || isinf b) = true →
      c_prod z w = ⟨inf *. (s.a *. s.c -. s.b *. s.d), inf *. (s.a *. s.d +. s.b *. s.c)⟩)

theorem cProdBranchOrder_proven : CProdBranchOrder := by
  intro R _ z w a b c d r s
  have key : c_prod z w = if (isnan r.real && isnan r.imag) = true then
      (if s.recalc = true then
        (⟨inf *. (s.a *. s.c -. s.b *. s.d), inf *. (s.a *. s.d +. s.b *. s.c)⟩ : Cx R)
       else r) else r := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro h
    simp [key, h]
  · intro h1 h2 h3
    have hs : s = ⟨a, b, c, d, false⟩ := by
      simp only [s]
      rw [prodBoxZ_of _ h1, prodBoxW_of _ h2, prodOverflow_of _ _ _ _ _ h3]
    have hr : s.recalc = false := by rw [hs]
    simp [key, hr]
  · intro h1 h2
    have h0 : (prodBoxZ (⟨a, b, c, d, false⟩ : ProdSt R)).recalc = true := by
      simp [prodBoxZ, h2]
    have hrc : s.recalc = true := prodOverflow_recalc _ _ _ _ _ (prodBoxW_recalc _ h0)
    rw [key, ite_eq_left h1, ite_eq_left hrc]

/-- `_Py_c_quot`, lines 195-222, in the order of the `if`s. The magnitude test picks
the divisor's larger part; a zero there is `EDOM`, without looking at `a`; and when
neither `>=` holds, which takes a NaN, the result is NaN before recovery. The
recovery of lines 226-243 touches only a result with both parts NaN. -/
def CQuotBranchOrder : Prop :=
  ∀ (R : Type) [CDouble R] (a b : Cx R) (e : Errno),
    isnan (zero : R) = false → isnan (nan : R) = true →
    (ge (absLt b.real) (absLt b.imag) = true → (absLt b.real ==. zero) = true →
      c_quot a b e = (⟨zero, zero⟩, Errno.edom)) ∧
    (ge (absLt b.real) (absLt b.imag) = false → ge (absLt b.imag) (absLt b.real) = false →
      ((isinf a.real || isinf a.imag) && isfinite b.real && isfinite b.imag) = false →
      ((isinf (absLt b.real) || isinf (absLt b.imag)) && isfinite a.real &&
        isfinite a.imag) = false →
      c_quot a b e = (⟨nan, nan⟩, e))

theorem cQuotBranchOrder_proven : CQuotBranchOrder := by
  intro R _ a b e hz hn
  constructor
  · intro h1 h2
    simp [c_quot, h1, h2, hz]
  · intro h1 h2 h3 h4
    simp [c_quot, h1, h2, hn, h3, h4]

end PyLean.LongObj.Cplx
