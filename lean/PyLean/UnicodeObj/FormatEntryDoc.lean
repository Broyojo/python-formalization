import PyLean.UnicodeObj.IntFormatDoc
import PyLean.UnicodeObj.FormatFloatDoc

/-!
The entry points `_PyLong_FormatAdvancedWriter` (Objects/unicode_formatter.c:1828-1887),
`_PyFloat_FormatAdvancedWriter` (:1890-1926) and `_PyComplex_FormatAdvancedWriter` (:1929-1964), with
`format_obj` (:1777-1789), for every instance of the type or of a subclass, against the docs: an empty
spec is `str(obj)` (Doc/library/string.rst: "an empty format specification produces the same result
as if you had called str() on the value"), which for a subclass is its own `__str__` and can raise;
any other spec is read as the grammar says (`docParse`) and formatted as the docs describe, an int
with a float type through `float(obj)` (the docs: "float() is used to convert the integer"), which for
a subclass can run its `__float__` and raise; an unknown type is refused with the object's type name.
The `str` entry point is `StrFormatSpecDoc`.
-/

namespace PyLean.UnicodeObj

open PyLean PyLean.Binary64

/-- `str(v)` for an exact int: its decimal digits, within the 4300-digit limit. -/
def docIntStr (v : Int) : Py Str :=
  if 4300 < (Nat.toDigits 10 v.natAbs).length then .error (.valueError intLimitMessage)
  else .ok ((if v < 0 then [45] else []) ++ (Nat.toDigits 10 v.natAbs).map Char.toNat)

/-- `format(x, spec)` for a float and a parsed spec with a float type, as the docs describe it. -/
def docFloat (x : F64) (f : FormatSpec) : Py Str :=
  if f.precision > 2 ^ 31 - 1 then .error (.valueError "precision too big")
  else docFloatBuf x f >>= fun buf => .ok (docFloatLayout buf f)

theorem renderSpec_isEmpty (d : SpecFields) (he : ¬ renderSpec d = []) : (renderSpec d).isEmpty = false := by
  cases h : renderSpec d with
  | nil => exact absurd h he
  | cons _ _ => rfl

def LongEntryDoc : Prop :=
  ∀ (tn : String) (exact : Bool) (strObj : Py Str) (toFloat : Py F64) (v : Int) (d : SpecFields), d.WF →
    formatLongAdvancedObj tn exact strObj toFloat v (renderSpec d) =
      if renderSpec d = [] then (if exact then docIntStr v else strObj)
      else docParse tn d 100 62 >>= fun f =>
        if f.type ∈ [98, 99, 100, 111, 120, 88, 110] then docInt v f
        else if f.type ∈ [101, 69, 102, 70, 103, 71, 37] then toFloat >>= fun x => docFloat x f
        else .error (unknownTypeMessage f.type tn)

theorem longEntryDoc_proven : LongEntryDoc := by
  intro tn exact strObj toFloat v d hd
  unfold formatLongAdvancedObj formatObj
  by_cases he : renderSpec d = []
  · rw [if_pos he]
    simp only [he, List.isEmpty_nil, if_true]
    cases exact
    · rfl
    · simp only [if_true, longFormat, docIntStr, digitsOf_eq 10 v.natAbs (by omega) (by omega),
        List.length_map, intLimitMessage]
      by_cases h : 4300 < (Nat.toDigits 10 v.natAbs).length
      · simp [h]
      · simp [h]
  · rw [if_neg he]
    simp only [renderSpec_isEmpty d he, Bool.false_eq_true, if_false]
    have hp := parseDoc_proven tn d 100 62 hd
    rw [hp]
    cases hq : docParse tn d 100 62 with
    | error e => rfl
    | ok f =>
      have hi : SpecInv f := parse_inv (t := tn) (spec := renderSpec d) (dt := 100) (da := 62) (by rfl)
        (by rw [hp, hq])
      simp only [bind, Except.bind]
      by_cases hint : f.type ∈ [98, 99, 100, 111, 120, 88, 110]
      · rw [if_pos hint, ← intFormatDoc_proven v f exact hi hint]
        have : (f.type == 98 || f.type == 99 || f.type == 100 || f.type == 111 || f.type == 120 ||
            f.type == 88 || f.type == 110) = true := by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hint
          rcases hint with h | h | h | h | h | h | h <;> simp [h]
        rw [if_pos this]
      · rw [if_neg hint]
        have : (f.type == 98 || f.type == 99 || f.type == 100 || f.type == 111 || f.type == 120 ||
            f.type == 88 || f.type == 110) = false := by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hint
          simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
        rw [if_neg (by simp [this])]
        by_cases hfl : f.type ∈ [101, 69, 102, 70, 103, 71, 37]
        · rw [if_pos hfl]
          have : (f.type == 101 || f.type == 69 || f.type == 102 || f.type == 70 || f.type == 103 ||
              f.type == 71 || f.type == 37) = true := by
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hfl
            rcases hfl with h | h | h | h | h | h | h <;> simp [h]
          rw [if_pos this]
          cases toFloat with
          | error e => rfl
          | ok x =>
            simp only []
            rw [floatFormatDoc_proven x f hi (by
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hfl ⊢; omega)]
            rfl
        · rw [if_neg hfl]
          have : (f.type == 101 || f.type == 69 || f.type == 102 || f.type == 70 || f.type == 103 ||
              f.type == 71 || f.type == 37) = false := by
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hfl
            simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
          rw [if_neg (by simp [this]), unknownTypeMessage_eq]

def FloatEntryDoc : Prop :=
  ∀ (tn : String) (strObj : Py Str) (x : F64) (d : SpecFields), d.WF →
    formatFloatAdvancedObj tn strObj x (renderSpec d) =
      if renderSpec d = [] then strObj
      else docParse tn d 0 62 >>= fun f =>
        if f.type ∈ [0, 101, 69, 102, 70, 103, 71, 110, 37] then docFloat x f
        else .error (unknownTypeMessage f.type tn)

theorem floatEntryDoc_proven : FloatEntryDoc := by
  intro tn strObj x d hd
  unfold formatFloatAdvancedObj formatObj formatFloatDispatch
  by_cases he : renderSpec d = []
  · rw [if_pos he]
    simp [he, bind, Except.bind]
  · rw [if_neg he]
    simp only [renderSpec_isEmpty d he, Bool.false_eq_true, if_false]
    have hp := parseDoc_proven tn d 0 62 hd
    rw [hp]
    cases hq : docParse tn d 0 62 with
    | error e => rfl
    | ok f =>
      have hi : SpecInv f := parse_inv (t := tn) (spec := renderSpec d) (dt := 0) (da := 62) (by rfl)
        (by rw [hp, hq])
      simp only [bind, Except.bind]
      by_cases hfl : f.type ∈ [0, 101, 69, 102, 70, 103, 71, 110, 37]
      · rw [if_pos hfl]
        have : (f.type == 0 || f.type == 101 || f.type == 69 || f.type == 102 || f.type == 70 ||
            f.type == 103 || f.type == 71 || f.type == 110 || f.type == 37) = true := by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hfl
          rcases hfl with h | h | h | h | h | h | h | h | h <;> simp [h]
        rw [if_pos this]
        simp only []
        rw [floatFormatDoc_proven x f hi hfl]
        rfl
      · rw [if_neg hfl]
        have : (f.type == 0 || f.type == 101 || f.type == 69 || f.type == 102 || f.type == 70 ||
            f.type == 103 || f.type == 71 || f.type == 110 || f.type == 37) = false := by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hfl
          simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
        rw [if_neg (by simp [this]), unknownTypeMessage_eq]

def ComplexEntryDoc : Prop :=
  ∀ (tn : String) (strObj : Py Str) (re im : F64) (d : SpecFields), d.WF →
    formatComplexAdvancedObj tn strObj re im (renderSpec d) =
      if renderSpec d = [] then strObj
      else docParse tn d 0 62 >>= fun f =>
        if f.type ∈ [0, 101, 69, 102, 70, 103, 71, 110] then formatComplexInternal re im f
        else .error (unknownTypeMessage f.type tn)

theorem complexEntryDoc_proven : ComplexEntryDoc := by
  intro tn strObj re im d hd
  unfold formatComplexAdvancedObj formatObj formatComplexDispatch
  by_cases he : renderSpec d = []
  · rw [if_pos he]
    simp [he, bind, Except.bind]
  · rw [if_neg he]
    simp only [renderSpec_isEmpty d he, Bool.false_eq_true, if_false]
    rw [parseDoc_proven tn d 0 62 hd]
    cases docParse tn d 0 62 with
    | error e => rfl
    | ok f =>
      simp only [bind, Except.bind]
      by_cases hfl : f.type ∈ [0, 101, 69, 102, 70, 103, 71, 110]
      · rw [if_pos hfl]
        have : (f.type == 0 || f.type == 101 || f.type == 69 || f.type == 102 || f.type == 70 ||
            f.type == 103 || f.type == 71 || f.type == 110) = true := by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hfl
          rcases hfl with h | h | h | h | h | h | h | h <;> simp [h]
        rw [if_pos this]
      · rw [if_neg hfl]
        have : (f.type == 0 || f.type == 101 || f.type == 69 || f.type == 102 || f.type == 70 ||
            f.type == 103 || f.type == 71 || f.type == 110) = false := by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hfl
          simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
        rw [if_neg (by simp [this]), unknownTypeMessage_eq]

end PyLean.UnicodeObj
