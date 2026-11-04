import PyLean.UnicodeObj.FormatEntryDoc
import PyLean.UnicodeObj.FormatFloat

/-!
`complex.__format__`, `complex___format___impl`, complexobject.c:914-929 (CPython 3.15.2),
over the format engine of `Objects/unicode_formatter.c` modelled in `PyLean.UnicodeObj`.
-/

namespace PyLean.Binary64

open PyLean.UnicodeObj

/-- `complex___format___impl`, complexobject.c:914-929: `_PyComplex_FormatAdvancedWriter`
(Objects/unicode_formatter.c:1929-1964) over the whole spec. `tpName` is
`Py_TYPE(self)->tp_name`; `strObj` is `PyObject_Str(self)`, which `format_obj`
(unicode_formatter.c:1778-1790) writes for an empty spec, so a subclass's `__str__` is what
`format(z, '')` gives. -/
def complex___format___impl (tpName : String) (strObj : Py Str) (self : C) (spec : Str) : Py Str :=
  formatComplexAdvancedObj tpName strObj self.re self.im spec

/-- `format(z, spec)` for a complex or complex subclass instance `z`. An empty spec is
`str(z)`, whatever `str` does for the type (unicode_formatter.c:1938-1939). Any other spec,
written from its documented fields, is parsed with default alignment `>` and goes to
`format_complex_internal` for the types `'' e E f F g G n`, and raises the unknown-type
`ValueError` otherwise. And the engine agrees with `complex_repr` where both apply: a spec
with no type, precision, sign or width (`format(z, '<')`) gives `repr(z)`, down to when the
real part is dropped and when the parentheses appear (`ComplexOmittedTypeIsRepr`). -/
def ComplexFormatExact : Prop :=
  ∀ (tn : String) (strObj : Py Str) (z : C),
    complex___format___impl tn strObj z [] = strObj ∧
    (∀ d : SpecFields, d.WF → renderSpec d ≠ [] →
      complex___format___impl tn strObj z (renderSpec d) =
        (docParse tn d 0 62 >>= fun f =>
          if f.type ∈ [0, 101, 69, 102, 70, 103, 71, 110] then formatComplexInternal z.re z.im f
          else .error (unknownTypeMessage f.type tn))) ∧
    (∀ (f : FormatSpec) (s r : Str), f.type = 0 → f.precision < 0 →
      f.alternate = false → f.noNeg0 = false → f.thousands = LT_NO_LOCALE →
      f.fracThousands = LT_NO_LOCALE → f.sign ≠ 43 → f.sign ≠ 32 → f.width = -1 →
      formatComplexInternal z.re z.im f = .ok s → complex_repr z = some r → s = r)

theorem complexFormatExact_proven : ComplexFormatExact := by
  intro tn strObj z
  refine ⟨?_, fun d hd hne => ?_, fun f s r h1 h2 h3 h4 h5 h6 h7 h8 h9 hs hr => ?_⟩
  · simp [complex___format___impl, formatComplexAdvancedObj, formatComplexDispatch, formatObj,
      bind, Except.bind]
  · unfold complex___format___impl
    rw [complexEntryDoc_proven tn strObj z.re z.im d hd, if_neg hne]
  · exact complexOmittedTypeIsRepr_proven z.re z.im f s r h1 h2 h3 h4 h5 h6 h7 h8 h9 hs hr

end PyLean.Binary64
