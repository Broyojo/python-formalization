import PyLean.TextLibs.ReParse

/-! Properties of the `re` parser model. -/

namespace PyLean.TextLibs.Re

open PyLean

set_option linter.unusedSimpArgs false

/-- The exception of a computation, so that a result without `DecidableEq` can be tested. -/
def errOf {α : Type} : Py α → Option PyExc
  | .error e => some e
  | .ok _ => none

theorem raises_of_errOf {α : Type} {r : Py α} {e : PyExc} {cls : String} (h : errOf r = some e)
    (hc : e.className = cls) : r.raises cls := by
  cases r with
  | error e' =>
    simp only [errOf, Option.some.injEq] at h
    exact ⟨e', rfl, h ▸ hc⟩
  | ok _ => simp [errOf] at h

/-- `a{ddd...}` with 641 digits, one past the lowest allowed `sys.set_int_max_str_digits`. -/
def hugeRepeat : List Nat := [97, 123] ++ List.replicate 641 57 ++ [125]

/-- For every allowed `sys.set_int_max_str_digits` value, a `str` pattern parsed with no flags
reports a bad pattern as `PatternError` or, for too large a repeat count, `OverflowError`: it never
leaks `ValueError`. The counterexample uses the lowest allowed limit, 640, because the kernel
cannot evaluate the parser on 4301 digits; `bugs/textlibs-re-int-digit-limit.yaml` shows the default
limit of 4300 on CPython. -/
def ParseNoValueError : Prop :=
  ∀ L, 640 ≤ L → ∀ s : List Nat, ¬ (parse true s 0 L).raises "ValueError"

theorem parseNoValueError_refuted : ¬ParseNoValueError := by
  intro h
  apply h 640 (Nat.le_refl _) hugeRepeat
  refine raises_of_errOf (e := .valueError "Exceeds the limit (640 digits) for integer string conversion: value has 641 digits; use sys.set_int_max_str_digits() to increase the limit") ?_ rfl
  decide +kernel

/-- A replacement template reports a bad group reference as `PatternError`, never `ValueError`. -/
def TemplateNoValueError : Prop :=
  ∀ L, 640 ≤ L → ∀ (s : List Nat) (g : Nat) (d : List (List Nat × Nat)),
    ¬ (parseTemplate true s g d L).raises "ValueError"

theorem templateNoValueError_refuted : ¬TemplateNoValueError := by
  intro h
  apply h 640 (Nat.le_refl _) ([92, 103, 60] ++ List.replicate 641 57 ++ [62]) 0 []
  refine raises_of_errOf (e := .valueError "Exceeds the limit (640 digits) for integer string conversion: value has 641 digits; use sys.set_int_max_str_digits() to increase the limit") ?_ rfl
  decide +kernel

/-- After reading a token, `tell()` is the position of that token, so error positions point at
the character being looked at. -/
def TellAfterAdv : Prop :=
  ∀ (t t' : Tk), t.adv = .ok t' → t'.next.isSome = true → t'.tell = t.index

theorem tellAfterAdv_proven : TellAfterAdv := by
  intro t t' h hn
  unfold Tk.adv at h
  split at h
  · cases h
    simp at hn
  · split at h
    · cases h
    · cases h
      simp [Tk.tell]
  · cases h
    simp [Tk.tell]

/-- `fix_flags`: a `str` pattern without `ASCII` gets `UNICODE`, and `LOCALE` is rejected. -/
def FixFlagsStr : Prop :=
  ∀ f : Nat,
    ((f &&& FLAG_LOCALE) ≠ 0 → fixFlags true f = .error (.valueError "cannot use LOCALE flag with a str pattern")) ∧
    ((f &&& FLAG_LOCALE) = 0 → (f &&& FLAG_ASCII) = 0 → fixFlags true f = .ok (f ||| FLAG_UNICODE))

theorem fixFlagsStr_proven : FixFlagsStr := by
  intro f
  constructor
  · intro h
    simp [fixFlags, h]
  · intro h1 h2
    simp [fixFlags, h1, h2]

/-- `_uniq` keeps exactly the same items. -/
def UniqMembers : Prop := ∀ (l : List SetItem) (x : SetItem), x ∈ uniq l ↔ x ∈ l

theorem uniqMembers_proven : UniqMembers := by
  intro l x
  simp [uniq, List.mem_eraseDups]

/-- A pattern without a newline gets the plain position suffix, and no line or column. -/
def MessagePlain : Prop :=
  ∀ (msg : String) (p : List Nat) (pos : Int), p.contains 10 = false →
    patternMessage msg p pos = msg ++ s!" at position {pos}"

theorem messagePlain_proven : MessagePlain := by
  intro msg p pos h
  have h' : ¬ 10 ∈ p := by simpa using h
  simp [patternMessage, h']

/-- `_escape` and `_class_escape` agree on every single-character ASCII escape, except the ones
that mean something else outside a set: `\b`, `\A`, `\B`, `\Z`, `\z` and the digits. -/
def EscapeTwins : Prop :=
  ∀ c < 128, c ≠ 98 ∧ c ≠ 65 ∧ c ≠ 66 ∧ c ≠ 90 ∧ c ≠ 122 ∧ ¬ (48 ≤ c ∧ c ≤ 57) →
    let st : PSt := { tk := ⟨true, [], 0, none⟩, flags := 0 }
    (match (escapeCode [92, c]).run st, (classEscape [92, c]).run st with
     | .ok (a, _), .ok (b, _) => (match a, b with
       | .literal x, .literal y => x == y
       | .in_ x, .in_ y => x == y
       | _, _ => false)
     | .error a, .error b => a == b
     | _, _ => false) = true

theorem escapeTwins_proven : EscapeTwins := by
  unfold EscapeTwins
  decide +kernel

end PyLean.TextLibs.Re
