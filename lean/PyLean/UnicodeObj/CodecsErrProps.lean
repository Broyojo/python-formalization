import PyLean.UnicodeObj.CodecsErrSafe
import PyLean.UnicodeObj.CodecEscapeProps

/-!
Properties of the standard error handlers on every exception object: when the replacing
handlers succeed, the buffers they fill, the round trips, and the names `namereplace` writes.
-/

namespace PyLean.UnicodeObj.Codecs

open PyLean PyLean.UnicodeObj

/-! ## The builtin hierarchy satisfies `HierOk` -/

/-- The builtin classes with their static MROs, every other class unrelated to them and given
the exception flag. -/
def builtinHier : Hier := ⟨builtinSub, fun _ => true, fun _ => .ok true⟩

/-- `HierOk` can be met: it is no vacuous hypothesis. -/
theorem builtinHier_ok : HierOk builtinHier := by
  refine ⟨fun c _ b => rfl, fun c _ => rfl, fun c _ => rfl, ?_, ?_, ?_⟩
  all_goals
    intro c ⟨h1, h2⟩
    first
      | (have := builtinSub_enc c h1; subst this; revert h2; decide)
      | (have := builtinSub_dec c h1; subst this; revert h2; decide)

/-! ## When the replacing handlers succeed -/

/-- The classes each handler takes (codecs.c:806-812, :876-884, :896, :1052-1060, :1072,
:1400-1404, :1493-1497). -/
def takes (H : Hier) (h : ErrHandler) (c : String) : Bool :=
  match h with
  | .strict => true
  | .ignore | .replace | .backslashreplace => H.isEnc c || H.isDec c || H.isTr c
  | .xmlcharrefreplace | .namereplace => H.isEnc c
  | .surrogatepass | .surrogateescape => H.isEnc c || H.isDec c

/-- The `object` slot holds what the handler reads: `bytes` for a decode error, `str`
otherwise. -/
def objFits (H : Hier) (e : ExcObj) : Bool :=
  match e.object with
  | .str _ => !H.isDec e.cls
  | .bytes _ => H.isDec e.cls
  | _ => false

/-- **The replacing handlers always replace.** `ignore`, `replace`, `backslashreplace`,
`xmlcharrefreplace` and `namereplace` succeed exactly when the class is one they take, the
`object` attribute has the type that class needs, (for `namereplace`) `unicodedata` loads, and
(for `replace` on a decode error, whose `PyUnicodeDecodeError_GetEnd` checks for a
`UnicodeError`) the class's MRO has `UnicodeError`, which a custom `mro()` can drop.
On a class a handler does not take, every handler but `strict` raises the `TypeError` of
`wrong_exception_type`. -/
def HandlersTotal : Prop :=
  ∀ (H : Hier) (capi : Except PyExc (Nat → Option Str)) (h : ErrHandler) (e : ExcObj), HierOk H →
    (h ∈ [.ignore, .replace, .backslashreplace, .xmlcharrefreplace, .namereplace] →
      ((∃ r, callBuiltin H capi h e = .ok r) ↔
        (takes H h e.cls = true ∧ objFits H e = true ∧ (h = .namereplace → ∃ g, capi = .ok g) ∧
          (h = .replace → H.isDec e.cls = true → H.sub e.cls "UnicodeError" = true)))) ∧
    (h ≠ .strict → takes H h e.cls = false → callBuiltin H capi h e = wrongType e)

theorem handlersTotal_proven : HandlersTotal := by
  intro H capi h e hH
  have d1 := hH.2.2.2.1 e.cls
  have d2 := hH.2.2.2.2.1 e.cls
  have d3 := hH.2.2.2.2.2 e.cls
  constructor
  · intro hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    cases hU : H.sub e.cls "UnicodeError" <;>
    cases hE : H.isEnc e.cls <;> cases hD : H.isDec e.cls <;> cases hT : H.isTr e.cls <;>
      simp only [Hier.isEnc, Hier.isDec, Hier.isTr] at hE hD hT <;>
      (try simp_all) <;>
      cases ho : e.object <;> cases hcap : capi <;>
      rcases hm with rfl | rfl | rfl | rfl | rfl <;>
      simp_all [callBuiltin, callRaw, setObjectStep, ignoreErrors, ignoreError, replaceErrors, replaceEncode, replaceDecode,
        replaceTranslate, decodeGetEnd, checkType, backslashReplaceErrors, backslashEncode,
        backslashDecode, xmlCharRefReplaceErrors, nameReplaceErrors, getParams, asAttr, wrongType,
        raiseT, bind, Except.bind, pure, Except.pure, Functor.map, Except.map, takes, objFits,
        Hier.isEnc, Hier.isDec, Hier.isTr, Body.result]
  · intro hs ht
    cases h <;> simp only [takes, Bool.or_eq_false_iff] at ht <;> (try exact absurd rfl hs) <;>
      simp_all [callBuiltin, callRaw, setObjectStep, ignoreErrors, replaceErrors, backslashReplaceErrors,
        xmlCharRefReplaceErrors, nameReplaceErrors, surrogatePassErrors, surrogateEscapeErrors,
        Functor.map, Except.map, wrongType, raiseT, Hier.isEnc, Hier.isDec, Hier.isTr]

end PyLean.UnicodeObj.Codecs
