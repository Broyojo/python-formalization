import PyLean.UnicodeObj.CodecsErrTrips

/-!
The names `namereplace` writes. The handler asks `unicodedata`'s C API for a name with
`getname(c, buffer, sizeof(buffer), 1)` (codecs.c:1095, :1119). The last argument,
`with_alias_and_seq`, makes `_getucname` (Modules/unicodedata.c:1434-1502) also answer for the
Plane 15 private-use code points where the database keeps its aliases (U+F0000..U+F01E0) and its
named sequences (U+F0200..U+F03CC). `unicodedata.name` passes 0 (unicodedata.c:1678) and finds no
name there.
-/

namespace PyLean.UnicodeObj.Codecs

open PyLean PyLean.UnicodeObj

/-- `_getucname(NULL, c, buffer, buflen, with_alias_and_seq)`, the current database. -/
structure Ucd where
  getname : Nat → Bool → Option Str

/-- `IS_ALIAS(c) || IS_NAMED_SEQ(c)`, unicodedata.c:1188-1190, with the bounds of
Modules/unicodename_db.h:17508-17509 and :17999-18000. -/
def isAliasOrSeq (c : Nat) : Bool :=
  (decide (0xF0000 ≤ c) && decide (c < 0xF01E1)) || (decide (0xF0200 ≤ c) && decide (c < 0xF03CD))

/-- What `_getucname` guarantees (unicodedata.c:1446-1447: without the flag, nothing in those
two ranges has a name; the flag changes nothing elsewhere), and one entry of the generated table:
the first alias, kept at U+F0000, is `NULL`, the alias of U+0000 (difftested through the C API
by `codecs_handler`). -/
def UcdOk (u : Ucd) : Prop :=
  (∀ c, isAliasOrSeq c = true → u.getname c false = none) ∧
  (∀ c, isAliasOrSeq c = false → u.getname c false = u.getname c true) ∧
  u.getname 0xF0000 true = some (lit "NULL")

/-- `unicodedata.name(chr(c))`: `_getucname(self, c, name, NAME_MAXLEN, 0)`, unicodedata.c:1678. -/
def ucdName (u : Ucd) (c : Nat) : Option Str := u.getname c false

/-- What `namereplace` gets from `_PyUnicode_GetNameCAPI`: `getname(c, buffer, 256, 1)`. -/
def capiOf (u : Ucd) : Except PyExc (Nat → Option Str) := .ok (fun c => u.getname c true)

/-- **namereplace writes the Name property.** codecs.rst: namereplace replaces with `\N{...}`
escape sequences, "what appears in the braces is the Name property from Unicode Character
Database"; `namereplace_errors`: "The set of characters that appear in the braces is the Name
property from Unicode Character Database." So for every encode error with any `start` and `end`,
the replacement is `\N{name}` for each character that `unicodedata.name` names, and the
`backslashreplace` escape for the others. -/
def NameReplaceWritesNames : Prop :=
  ∀ (u : Ucd) (H : Hier) (e : ExcObj) (s out : Str) (pos : Nat),
    UcdOk u → HierOk H → H.isEnc e.cls = true → e.object = .str s → Str.Valid s →
    callBuiltin H (capiOf u) .namereplace e = .ok (.str out, pos) →
    out = (slice s (stOf e s.length) pos).flatMap (fun c =>
      match ucdName u c with
      | some n => [92, 78, 123] ++ n ++ [125]
      | none => escapeEncodeChar c)

/-- `UnicodeEncodeError('ascii', '\U000f0000', 0, 1, 'r')`. -/
def aliasExc : ExcObj :=
  { cls := "UnicodeEncodeError", tpName := "UnicodeEncodeError",
    clsRepr := "<class 'UnicodeEncodeError'>", encoding := .str (lit "ascii"),
    object := .str [0xF0000], start := 0, stop := 1 }

/-- For every database that meets `UcdOk`, the real one included: `namereplace` writes
`\N{NULL}` for U+F0000, a private-use character that `unicodedata.name` does not name. -/
theorem nameReplace_alias (u : Ucd) (hu : UcdOk u) :
    callBuiltin builtinHier (capiOf u) .namereplace aliasExc =
      .ok (.str ([92, 78, 123] ++ lit "NULL" ++ [125]), 1) ∧ ucdName u 0xF0000 = none := by
  have hn := hu.2.2
  have hz := hu.1 0xF0000 (by decide)
  refine ⟨?_, hz⟩
  have hE : builtinHier.isEnc aliasExc.cls = true := by decide
  have hs : stOf aliasExc 1 = 0 := by decide
  have he : enOf aliasExc 1 = 1 := by decide
  rw [callBuiltin_ok]
  simp only [callRaw, nameReplaceErrors, hE, Bool.not_true, Bool.false_eq_true,
    if_false, capiOf, getParams_str aliasExc [0xF0000] rfl, pure, Except.pure, bind, Except.bind,
    Functor.map, Except.map, Body.result, List.length_singleton, hs, he, slice, List.drop_zero,
    Nat.sub_zero, List.take_one, List.head?_cons, Option.toList_some, nameSizeLoop, nameSize, hn]
  have hfit : ¬ ((ssizeMaxN : Int) - (3 + ((lit "NULL").length : Int) + 1) < 0) := by
    simp [ssizeMaxN, lit]
  simp [nameBlock, hn, hfit]

theorem nameReplaceWritesNames_refuted : ¬ NameReplaceWritesNames := by
  intro h
  let u0 : Ucd := ⟨fun c f => if c = 0xF0000 ∧ f = true then some (lit "NULL") else none⟩
  have hu0 : UcdOk u0 := by
    refine ⟨fun c _ => by simp [u0], fun c hc => ?_, by simp [u0]⟩
    have : c ≠ 0xF0000 := by intro h; subst h; simp [isAliasOrSeq] at hc
    simp [u0, this]
  obtain ⟨hcall, hname⟩ := nameReplace_alias u0 hu0
  have := h u0 builtinHier aliasExc [0xF0000] _ 1 hu0 builtinHier_ok (by decide) rfl
    (by intro x hx; simp at hx; subst hx; decide) hcall
  have hs : stOf aliasExc 1 = 0 := by decide
  simp only [List.length_singleton, hs, slice, List.drop_zero, Nat.sub_zero, List.take_one,
    List.head?_cons, Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    hname] at this
  revert this
  decide

end PyLean.UnicodeObj.Codecs

namespace PyLean.UnicodeObj.Codecs

open PyLean PyLean.UnicodeObj

/-! ## A metaclass `__subclasscheck__` in the re-raise -/

/-- **`HandlersAgree` without the `__subclasscheck__` part of its scope.** For a class whose MRO
keeps `UnicodeError` and that has the exception flag, `strict` re-raises its argument as the
codec loop's `bad` exception. False when a metaclass `__subclasscheck__` raises:
`_PyErr_SetObject` asks `issubclass(type(exc), type(exc))` before raising (errors.c:166-171), and
its error is what `strict` (and every re-raise of the surrogate handlers) raises. Python's own
`raise exc` does the same, so this records the scope limit of `Ordinary`; it is no bug. -/
def EncodeAgreeAll : Prop :=
  ∀ (H : Hier) (getname : Nat → Option Str) (e : ExcObj) (s : Str),
    HierOk H → H.isEnc e.cls = true → H.sub e.cls "UnicodeError" = true → H.excFlag e.cls = true →
    e.object = .str s → Str.Valid s →
    lowerEnc (encodeError "" s (stOf e s.length) (enOf e s.length) "") (callBuiltin H (.ok getname) .strict e) =
      encodeHandlerCall .strict getname "" .unknown s (stOf e s.length) (enOf e s.length) ""

/-- `class M(type): def __subclasscheck__(c, s): raise RuntimeError('subclasscheck')`,
`class E(UnicodeEncodeError, metaclass=M)`: an ordinary MRO and the flag. -/
def checkHier : Hier :=
  { sub := fun c b => if c = "E" then (b == "E" || builtinSub "UnicodeEncodeError" b) else builtinSub c b
    excFlag := fun _ => true
    subcheck := fun c => if c = "E" then .error (.named "RuntimeError" "subclasscheck") else .ok true }

theorem checkHier_ok : HierOk checkHier := by
  have nb : ∀ c ∈ builtinClasses, c ≠ "E" := by
    intro c hc; simp [builtinClasses] at hc; rcases hc with h | h | h | h | h | h | h | h | h <;>
      subst h <;> decide
  refine ⟨fun c hc b => by simp [checkHier, nb c hc], fun c _ => rfl,
    fun c hc => by simp [checkHier, nb c hc], ?_, ?_, ?_⟩
  all_goals
    intro c ⟨h1, h2⟩
    by_cases hE : c = "E"
    · subst hE; revert h2; decide
    · simp only [checkHier, hE, if_false] at h1 h2
      first
        | (have := builtinSub_enc c h1; subst this; revert h2; decide)
        | (have := builtinSub_dec c h1; subst this; revert h2; decide)

def checkExc : ExcObj :=
  { cls := "E", tpName := "E", clsRepr := "<class '__main__.E'>", encoding := .null,
    object := .str [0xff], start := 0, stop := 1 }

theorem checkExc_strict :
    callBuiltin checkHier (.ok fun _ => none) .strict checkExc =
      .error (.exc (.named "RuntimeError" "subclasscheck")) := by rfl

theorem encodeAgreeAll_refuted : ¬ EncodeAgreeAll := by
  intro h
  have := h checkHier (fun _ => none) checkExc [0xff] checkHier_ok (by decide) (by decide) rfl rfl
    (by intro x hx; simp at hx; subst hx; decide)
  rw [checkExc_strict] at this
  simp only [lowerEnc, encodeHandlerCall, Except.error.injEq] at this
  have hc := congrArg PyExc.className this
  unfold encodeError at hc
  split at hc <;> simp [PyExc.className] at hc

end PyLean.UnicodeObj.Codecs
