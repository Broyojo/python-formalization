import PyLean.TypeObj.ExcPropsUnicode2
import PyLean.TypeObj.ExcPropsBase2

/-!
Refusals of the Unicode error C API and `__init__`s, and the remaining `SyntaxError` branches
(`Objects/exceptions.c`, CPython 3.15.2).
-/

namespace PyLean.TypeObj

/-! ## The C API wrappers refuse a non-`UnicodeError` -/

/-- **Every `PyUnicode*Error_SetStart`, `GetEnd`, `SetEnd` and `SetReason` refuses a
non-`UnicodeError` first** (`check_unicode_error_type`, `:3127-3137`, called at `:3526`, `:3534`,
`:3542`, `:3568`, `:3576`, `:3584`, `:3594`, `:3602`, `:3610`, `:3646`, `:3654`, `:3662`):
`TypeError: expecting a <Kind> object, got <type>`, with the world unchanged. -/
def UnicodeCapiRefusals : Prop :=
  ∀ (k : UKind) (self : Val) (w : World), isSubtype w (typeOf w self) B.UnicodeError = false →
    (∀ n : Int, pyUnicodeErrorSetStart k self n w =
      .err (.exc B.TypeError s!"expecting a {k.name} object, got {typeFQN w (typeOf w self)}" none) w) ∧
    pyUnicodeErrorGetEnd k self w =
      .err (.exc B.TypeError s!"expecting a {k.name} object, got {typeFQN w (typeOf w self)}" none) w ∧
    (∀ n : Int, pyUnicodeErrorSetEnd k self n w =
      .err (.exc B.TypeError s!"expecting a {k.name} object, got {typeFQN w (typeOf w self)}" none) w) ∧
    (∀ r : String, pyUnicodeErrorSetReason k self r w =
      .err (.exc B.TypeError s!"expecting a {k.name} object, got {typeFQN w (typeOf w self)}" none) w)

theorem unicodeCapiRefusals_proven : UnicodeCapiRefusals := by
  intro k self w h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n; simp [pyUnicodeErrorSetStart, checkUnicodeErrorType, h, typeErr, raiseC]
  · simp [pyUnicodeErrorGetEnd, checkUnicodeErrorType, h, typeErr, raiseC]
  · intro n; simp [pyUnicodeErrorSetEnd, checkUnicodeErrorType, h, typeErr, raiseC]
  · intro r; simp [pyUnicodeErrorSetReason, checkUnicodeErrorType, h, typeErr, raiseC]

/-- **`GetReason` refuses a NULL or non-`str` reason with the `reason` label** (`:3175-3180`
through `as_unicode_error_attribute`, `:3093-3098`). -/
def UnicodeGetReasonRefusals : Prop :=
  ∀ (k : UKind) (self : Val) (w : World), isSubtype w (typeOf w self) B.UnicodeError = true →
    (memGet (excDataOf w self) "reason" = none → pyUnicodeErrorGetReason k self w =
      .err (.exc B.TypeError "UnicodeError 'reason' attribute is not set" none) w) ∧
    (∀ v, memGet (excDataOf w self) "reason" = some v → strOf w v = none →
      pyUnicodeErrorGetReason k self w =
        .err (.exc B.TypeError "UnicodeError 'reason' attribute must be a string" none) w)

theorem unicodeGetReasonRefusals_proven : UnicodeGetReasonRefusals := by
  intro k self w hu
  have hc : ∀ n, checkUnicodeErrorType self n w = .ok () w := fun n => by
    simp [checkUnicodeErrorType, hu]
  refine ⟨?_, ?_⟩
  · intro h1
    simp only [pyUnicodeErrorGetReason, M.bind_app, hc, unicodeErrorGetReasonImpl, getW_app, h1]
    simp [asUnicodeErrorAttribute, checkUnicodeErrorAttribute, typeErr, raiseC, String.append_assoc]
    try rfl
  · intro v h1 h2
    simp only [pyUnicodeErrorGetReason, M.bind_app, hc, unicodeErrorGetReasonImpl, getW_app, h1]
    simp [asUnicodeErrorAttribute, checkUnicodeErrorAttribute, h2, typeErr, raiseC,
      String.append_assoc]
    try rfl

/-! ## The Unicode `__init__`s: `U` and `n` -/

theorem strOf_excUpdW_eq {w : World} {a : Addr} {d : ExcData} (hx : IsExc w a d)
    (f : ExcData → ExcData) (v : Val) : strOf (excUpdW w a f) v = strOf w v := by
  by_cases hv : v = .obj a
  · subst hv
    have h1 := (hx.update f).body
    have h2 := hx.body
    simp [strOf, h1, h2]
  · cases v with
    | obj b => simp only [strOf]; rw [payloadOf_excUpdW_ne _ _ _ _ hv]
    | _ => rfl

theorem excArgName_excUpdW {w : World} {a : Addr} {d : ExcData} (hx : IsExc w a d)
    (f : ExcData → ExcData) (v : Val) : excArgName (excUpdW w a f) v = excArgName w v := by
  simp only [excArgName, typeName, tpName, typeOf_excUpdW' _ _ _ hx.size, tdata_excUpdW _ _ _ _ hx.size]

theorem argN_overflow (rt : Rt) (n : Int) (w : World) (h : inSsize n = false) :
    argN rt (.int n) w = .err (.exc B.OverflowError "Python int too large to convert to C ssize_t" none) w := by
  simp [argN, excNumberIndex, intOf, excAsSsizeLong, h, overflowErr, raiseC]

/-- The world after `BaseException_init` stored `args`. -/
abbrev withArgs (w : World) (a : Addr) (args : List Val) : World :=
  excUpdW w a fun d => { d with args := args }

/-- **`UnicodeEncodeError.__init__` parses `"UUnnU"`** (`:3724-3729`): a non-`str` encoding,
object or reason is `TypeError: argument i must be str, not T`, so a non-`str` object never
reaches the members (an `"OOnnO"` parse would store it); `start` and `end` go through `n`, so an
`int` outside `Py_ssize_t` is the `OverflowError` and any other value through `__index__` is
stored as the integer it gives. All refusals come after `BaseException_init` stored `args`. -/
def UnicodeEncodeInitParse : Prop :=
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (enc obj sv ev reason : Val) (w : World), IsExc w a d →
    strOf w enc = none →
    unicodeEncodeErrorInit rt (.obj a) [enc, obj, sv, ev, reason] [] w =
      .err (.exc B.TypeError s!"argument 1 must be str, not {excArgName w enc}" none)
        (withArgs w a [enc, obj, sv, ev, reason])) ∧
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (enc obj sv ev reason : Val) (se : String) (w : World),
    IsExc w a d → strOf w enc = some se → strOf w obj = none →
    unicodeEncodeErrorInit rt (.obj a) [enc, obj, sv, ev, reason] [] w =
      .err (.exc B.TypeError s!"argument 2 must be str, not {excArgName w obj}" none)
        (withArgs w a [enc, obj, sv, ev, reason])) ∧
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (enc obj ev reason : Val) (se so : String) (i : Int)
    (w : World), IsExc w a d → strOf w enc = some se → strOf w obj = some so → inSsize i = false →
    unicodeEncodeErrorInit rt (.obj a) [enc, obj, .int i, ev, reason] [] w =
      .err (.exc B.OverflowError "Python int too large to convert to C ssize_t" none)
        (withArgs w a [enc, obj, .int i, ev, reason])) ∧
  (∀ (rt : Rt) (a : Addr) (d d3 : ExcData) (enc obj sv ev reason : Val) (se so sr : String)
    (s e : Int) (w w2 w3 : World), IsExc w a d → strOf w enc = some se → strOf w obj = some so →
    argN rt sv (withArgs w a [enc, obj, sv, ev, reason]) = .ok s w2 → argN rt ev w2 = .ok e w3 →
    strOf w3 reason = some sr → IsExc w3 a d3 →
    ∃ w', unicodeEncodeErrorInit rt (.obj a) [enc, obj, sv, ev, reason] [] w = .ok () w' ∧
      ssizeMember (excDataOf w' (.obj a)) "start" = s ∧ ssizeMember (excDataOf w' (.obj a)) "end" = e ∧
      memGet (excDataOf w' (.obj a)) "object" = some obj) ∧
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (enc obj sv ev reason : Val) (se so : String) (s e : Int)
    (w w2 w3 : World), IsExc w a d → strOf w enc = some se → strOf w obj = some so →
    argN rt sv (withArgs w a [enc, obj, sv, ev, reason]) = .ok s w2 → argN rt ev w2 = .ok e w3 →
    strOf w3 reason = none →
    unicodeEncodeErrorInit rt (.obj a) [enc, obj, sv, ev, reason] [] w =
      .err (.exc B.TypeError s!"argument 5 must be str, not {excArgName w3 reason}" none) w3)

theorem unicodeEncodeInitParse_proven : UnicodeEncodeInitParse := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro rt a d enc obj sv ev reason w hx h1
    have g1 : strOf (withArgs w a [enc, obj, sv, ev, reason]) enc = none := by
      rw [strOf_excUpdW_eq hx]; exact h1
    simp only [withArgs] at *
    simp only [unicodeEncodeErrorInit, baseExceptionInit, argNoKeywords, M.bind_app, getW_app,
      List.isEmpty_nil, excUpdate_app, List.length_cons, List.length_nil, Nat.reduceAdd, argCount_eq']
    simp [List.getD, argU, g1, excArgName_excUpdW hx, typeErr, raiseC, argPrefix]
    try rfl
  · intro rt a d enc obj sv ev reason se w hx h1 h2
    have g1 : strOf (withArgs w a [enc, obj, sv, ev, reason]) enc = some se := by
      rw [strOf_excUpdW_eq hx]; exact h1
    have g2 : strOf (withArgs w a [enc, obj, sv, ev, reason]) obj = none := by
      rw [strOf_excUpdW_eq hx]; exact h2
    simp only [withArgs] at *
    simp only [unicodeEncodeErrorInit, baseExceptionInit, argNoKeywords, M.bind_app, getW_app,
      List.isEmpty_nil, excUpdate_app, List.length_cons, List.length_nil, Nat.reduceAdd, argCount_eq']
    simp [List.getD, g1, argU, g2, excArgName_excUpdW hx, typeErr, raiseC, argPrefix]
    try rfl
  · intro rt a d enc obj ev reason se so i w hx h1 h2 hi
    have g1 : strOf (withArgs w a [enc, obj, .int i, ev, reason]) enc = some se := by
      rw [strOf_excUpdW_eq hx]; exact h1
    have g2 : strOf (withArgs w a [enc, obj, .int i, ev, reason]) obj = some so := by
      rw [strOf_excUpdW_eq hx]; exact h2
    simp only [withArgs] at *
    simp only [unicodeEncodeErrorInit, baseExceptionInit, argNoKeywords, M.bind_app, getW_app,
      List.isEmpty_nil, excUpdate_app, List.length_cons, List.length_nil, Nat.reduceAdd, argCount_eq']
    simp [List.getD, argU_ok' _ _ _ _ _ g1, argU_ok' _ _ _ _ _ g2, argN_overflow _ _ _ hi]
  · intro rt a d d3 enc obj sv ev reason se so sr s e w w2 w3 hx h1 h2 hs he h3 hx3
    have g1 : strOf (withArgs w a [enc, obj, sv, ev, reason]) enc = some se := by
      rw [strOf_excUpdW_eq hx]; exact h1
    have g2 : strOf (withArgs w a [enc, obj, sv, ev, reason]) obj = some so := by
      rw [strOf_excUpdW_eq hx]; exact h2
    have x2 := isExc_memSet hx3 "encoding" (some enc)
    have x3 := isExc_memSet x2 "object" (some obj)
    have x4 := isExc_memSet x3 "start" (some (.int s))
    have x5 := isExc_memSet x4 "end" (some (.int e))
    have x6 := isExc_memSet x5 "reason" (some reason)
    refine ex_of_isExc x6 ?_ ?_
    · simp only [unicodeEncodeErrorInit, baseExceptionInit, argNoKeywords, M.bind_app, getW_app,
        List.isEmpty_nil, excUpdate_app, List.length_cons, List.length_nil, Nat.reduceAdd,
        argCount_eq']
      simp [List.getD, argU_ok' _ _ _ _ _ g1, argU_ok' _ _ _ _ _ g2, hs, he,
        argU_ok' _ _ _ _ _ h3, excUpdate_app]
      try rfl
    · intro x6
      simp only [ssizeMember]
      rw [x6.data]
      refine ⟨?_, ?_, ?_⟩
      · rw [memGet_memSet_ne _ "reason" "start" _ (by decide),
          memGet_memSet_ne _ "end" "start" _ (by decide), memGet_memSet_same]
      · rw [memGet_memSet_ne _ "reason" "end" _ (by decide), memGet_memSet_same]
      · rw [memGet_memSet_ne _ "reason" "object" _ (by decide),
          memGet_memSet_ne _ "end" "object" _ (by decide),
          memGet_memSet_ne _ "start" "object" _ (by decide), memGet_memSet_same]
  · intro rt a d enc obj sv ev reason se so s e w w2 w3 hx h1 h2 hs he h3
    have g1 : strOf (withArgs w a [enc, obj, sv, ev, reason]) enc = some se := by
      rw [strOf_excUpdW_eq hx]; exact h1
    have g2 : strOf (withArgs w a [enc, obj, sv, ev, reason]) obj = some so := by
      rw [strOf_excUpdW_eq hx]; exact h2
    simp only [withArgs] at *
    simp only [unicodeEncodeErrorInit, baseExceptionInit, argNoKeywords, M.bind_app, getW_app,
      List.isEmpty_nil, excUpdate_app, List.length_cons, List.length_nil, Nat.reduceAdd, argCount_eq']
    simp [List.getD, g1, g2, hs, he, argU, h3, typeErr, raiseC, argPrefix]
    try rfl

/-- **`UnicodeDecodeError.__init__` parses `"UOnnU"`** (`:3831-3835`): a non-`str` encoding or
reason is refused with its position, the object is not checked by the parse, and `start` and `end`
go through `n` (`OverflowError` outside `Py_ssize_t`). -/
def UnicodeDecodeInitParse : Prop :=
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (enc obj sv ev reason : Val) (w : World), IsExc w a d →
    strOf w enc = none →
    unicodeDecodeErrorInit rt (.obj a) [enc, obj, sv, ev, reason] [] w =
      .err (.exc B.TypeError s!"argument 1 must be str, not {excArgName w enc}" none)
        (withArgs w a [enc, obj, sv, ev, reason])) ∧
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (enc obj ev reason : Val) (se : String) (i : Int)
    (w : World), IsExc w a d → strOf w enc = some se → inSsize i = false →
    unicodeDecodeErrorInit rt (.obj a) [enc, obj, .int i, ev, reason] [] w =
      .err (.exc B.OverflowError "Python int too large to convert to C ssize_t" none)
        (withArgs w a [enc, obj, .int i, ev, reason])) ∧
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (enc obj sv ev reason : Val) (se : String) (s e : Int)
    (w w2 w3 : World), IsExc w a d → strOf w enc = some se →
    argN rt sv (withArgs w a [enc, obj, sv, ev, reason]) = .ok s w2 → argN rt ev w2 = .ok e w3 →
    strOf w3 reason = none →
    unicodeDecodeErrorInit rt (.obj a) [enc, obj, sv, ev, reason] [] w =
      .err (.exc B.TypeError s!"argument 5 must be str, not {excArgName w3 reason}" none) w3)

theorem unicodeDecodeInitParse_proven : UnicodeDecodeInitParse := by
  refine ⟨?_, ?_, ?_⟩
  · intro rt a d enc obj sv ev reason w hx h1
    have g1 : strOf (withArgs w a [enc, obj, sv, ev, reason]) enc = none := by
      rw [strOf_excUpdW_eq hx]; exact h1
    simp only [withArgs] at *
    simp only [unicodeDecodeErrorInit, baseExceptionInit, argNoKeywords, M.bind_app, getW_app,
      List.isEmpty_nil, excUpdate_app, List.length_cons, List.length_nil, Nat.reduceAdd, argCount_eq']
    simp [List.getD, argU, g1, excArgName_excUpdW hx, typeErr, raiseC, argPrefix]
    try rfl
  · intro rt a d enc obj ev reason se i w hx h1 hi
    have g1 : strOf (withArgs w a [enc, obj, .int i, ev, reason]) enc = some se := by
      rw [strOf_excUpdW_eq hx]; exact h1
    simp only [withArgs] at *
    simp only [unicodeDecodeErrorInit, baseExceptionInit, argNoKeywords, M.bind_app, getW_app,
      List.isEmpty_nil, excUpdate_app, List.length_cons, List.length_nil, Nat.reduceAdd, argCount_eq']
    simp [List.getD, argU_ok' _ _ _ _ _ g1, argN_overflow _ _ _ hi]
  · intro rt a d enc obj sv ev reason se s e w w2 w3 hx h1 hs he h3
    have g1 : strOf (withArgs w a [enc, obj, sv, ev, reason]) enc = some se := by
      rw [strOf_excUpdW_eq hx]; exact h1
    simp only [withArgs] at *
    simp only [unicodeDecodeErrorInit, baseExceptionInit, argNoKeywords, M.bind_app, getW_app,
      List.isEmpty_nil, excUpdate_app, List.length_cons, List.length_nil, Nat.reduceAdd, argCount_eq']
    simp [List.getD, g1, hs, he, argU, h3, typeErr, raiseC, argPrefix]
    try rfl

/-- **`UnicodeTranslateError.__init__` parses `"UnnU"`** (`:3953-3956`): a non-`str` object or
reason is refused with its position, `start` and `end` go through `n` (`OverflowError` outside
`Py_ssize_t`, `__index__` otherwise), and the stores take what the conversions gave. -/
def UnicodeTranslateInitParse : Prop :=
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (obj sv ev reason : Val) (w : World), IsExc w a d →
    strOf w obj = none →
    unicodeTranslateErrorInit rt (.obj a) [obj, sv, ev, reason] [] w =
      .err (.exc B.TypeError s!"argument 1 must be str, not {excArgName w obj}" none)
        (withArgs w a [obj, sv, ev, reason])) ∧
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (obj ev reason : Val) (so : String) (i : Int)
    (w : World), IsExc w a d → strOf w obj = some so → inSsize i = false →
    unicodeTranslateErrorInit rt (.obj a) [obj, .int i, ev, reason] [] w =
      .err (.exc B.OverflowError "Python int too large to convert to C ssize_t" none)
        (withArgs w a [obj, .int i, ev, reason])) ∧
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (obj sv ev reason : Val) (so : String) (s e : Int)
    (w w2 w3 : World), IsExc w a d → strOf w obj = some so →
    argN rt sv (withArgs w a [obj, sv, ev, reason]) = .ok s w2 → argN rt ev w2 = .ok e w3 →
    strOf w3 reason = none →
    unicodeTranslateErrorInit rt (.obj a) [obj, sv, ev, reason] [] w =
      .err (.exc B.TypeError s!"argument 4 must be str, not {excArgName w3 reason}" none) w3) ∧
  (∀ (rt : Rt) (a : Addr) (d d3 : ExcData) (obj sv ev reason : Val) (so sr : String)
    (s e : Int) (w w2 w3 : World), IsExc w a d → strOf w obj = some so →
    argN rt sv (withArgs w a [obj, sv, ev, reason]) = .ok s w2 → argN rt ev w2 = .ok e w3 →
    strOf w3 reason = some sr → IsExc w3 a d3 →
    ∃ w', unicodeTranslateErrorInit rt (.obj a) [obj, sv, ev, reason] [] w = .ok () w' ∧
      ssizeMember (excDataOf w' (.obj a)) "start" = s ∧ ssizeMember (excDataOf w' (.obj a)) "end" = e)

theorem unicodeTranslateInitParse_proven : UnicodeTranslateInitParse := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro rt a d obj sv ev reason w hx h1
    have g1 : strOf (withArgs w a [obj, sv, ev, reason]) obj = none := by
      rw [strOf_excUpdW_eq hx]; exact h1
    simp only [withArgs] at *
    simp only [unicodeTranslateErrorInit, baseExceptionInit, argNoKeywords, M.bind_app, getW_app,
      List.isEmpty_nil, excUpdate_app, List.length_cons, List.length_nil, Nat.reduceAdd, argCount_eq']
    simp [List.getD, argU, g1, excArgName_excUpdW hx, typeErr, raiseC, argPrefix]
    try rfl
  · intro rt a d obj ev reason so i w hx h1 hi
    have g1 : strOf (withArgs w a [obj, .int i, ev, reason]) obj = some so := by
      rw [strOf_excUpdW_eq hx]; exact h1
    simp only [withArgs] at *
    simp only [unicodeTranslateErrorInit, baseExceptionInit, argNoKeywords, M.bind_app, getW_app,
      List.isEmpty_nil, excUpdate_app, List.length_cons, List.length_nil, Nat.reduceAdd, argCount_eq']
    simp [List.getD, argU_ok' _ _ _ _ _ g1, argN_overflow _ _ _ hi]
  · intro rt a d obj sv ev reason so s e w w2 w3 hx h1 hs he h3
    have g1 : strOf (withArgs w a [obj, sv, ev, reason]) obj = some so := by
      rw [strOf_excUpdW_eq hx]; exact h1
    simp only [withArgs] at *
    simp only [unicodeTranslateErrorInit, baseExceptionInit, argNoKeywords, M.bind_app, getW_app,
      List.isEmpty_nil, excUpdate_app, List.length_cons, List.length_nil, Nat.reduceAdd, argCount_eq']
    simp [List.getD, g1, hs, he, argU, h3, typeErr, raiseC, argPrefix]
    try rfl
  · intro rt a d d3 obj sv ev reason so sr s e w w2 w3 hx h1 hs he h3 hx3
    have g1 : strOf (withArgs w a [obj, sv, ev, reason]) obj = some so := by
      rw [strOf_excUpdW_eq hx]; exact h1
    have x3 := isExc_memSet hx3 "object" (some obj)
    have x4 := isExc_memSet x3 "start" (some (.int s))
    have x5 := isExc_memSet x4 "end" (some (.int e))
    have x6 := isExc_memSet x5 "reason" (some reason)
    refine ex_of_isExc x6 ?_ ?_
    · simp only [unicodeTranslateErrorInit, baseExceptionInit, argNoKeywords, M.bind_app, getW_app,
        List.isEmpty_nil, excUpdate_app, List.length_cons, List.length_nil, Nat.reduceAdd,
        argCount_eq']
      simp [List.getD, argU_ok' _ _ _ _ _ g1, hs, he, argU_ok' _ _ _ _ _ h3, excUpdate_app]
      try rfl
    · intro x6
      simp only [ssizeMember]
      rw [x6.data]
      refine ⟨?_, ?_⟩
      · rw [memGet_memSet_ne _ "reason" "start" _ (by decide),
          memGet_memSet_ne _ "end" "start" _ (by decide), memGet_memSet_same]
      · rw [memGet_memSet_ne _ "reason" "end" _ (by decide), memGet_memSet_same]

/-- **`UnicodeDecodeError.__init__` stores what `n` gave** (`:3832`, `:3855-3859`): with a `str`
encoding and reason and any `start` and `end` whose `n` conversions (`__index__` included, so
`True` gives 1) return `s` and `e`, the members `start` and `end` are `s` and `e`, not the raw
arguments; a `bytes` object is stored as it is and another buffer as a new `bytes` copy. -/
def UnicodeDecodeInitStoresN : Prop :=
  (∀ (rt : Rt) (a : Addr) (d d3 : ExcData) (enc obj sv ev reason : Val) (se sr : String)
    (bs : List Nat) (s e : Int) (w w2 w3 : World), IsExc w a d → strOf w enc = some se →
    argN rt sv (withArgs w a [enc, obj, sv, ev, reason]) = .ok s w2 → argN rt ev w2 = .ok e w3 →
    strOf w3 reason = some sr → IsExc w3 a d3 → bytesOf w3 obj = some bs →
    ∃ w', unicodeDecodeErrorInit rt (.obj a) [enc, obj, sv, ev, reason] [] w = .ok () w' ∧
      ssizeMember (excDataOf w' (.obj a)) "start" = s ∧ ssizeMember (excDataOf w' (.obj a)) "end" = e ∧
      memGet (excDataOf w' (.obj a)) "object" = some obj) ∧
  (∀ (rt : Rt) (a : Addr) (d d3 : ExcData) (enc obj sv ev reason : Val) (se sr : String)
    (bs : List Nat) (s e : Int) (w w2 w3 : World), IsExc w a d → strOf w enc = some se →
    argN rt sv (withArgs w a [enc, obj, sv, ev, reason]) = .ok s w2 → argN rt ev w2 = .ok e w3 →
    strOf w3 reason = some sr → IsExc w3 a d3 → bytesOf w3 obj = none →
    payloadOf w3 obj = some (.bytes bs) →
    ∃ w', unicodeDecodeErrorInit rt (.obj a) [enc, obj, sv, ev, reason] [] w = .ok () w' ∧
      ssizeMember (excDataOf w' (.obj a)) "start" = s ∧ ssizeMember (excDataOf w' (.obj a)) "end" = e ∧
      memGet (excDataOf w' (.obj a)) "object" = some (.obj w3.heap.size))

theorem unicodeDecodeInitStoresN_proven : UnicodeDecodeInitStoresN := by
  refine ⟨?_, ?_⟩
  · intro rt a d d3 enc obj sv ev reason se sr bs s e w w2 w3 hx h1 hs he h3 hx3 hb
    have g1 : strOf (withArgs w a [enc, obj, sv, ev, reason]) enc = some se := by
      rw [strOf_excUpdW_eq hx]; exact h1
    have x2 := isExc_memSet hx3 "encoding" (some enc)
    have x3 := isExc_memSet x2 "object" (some obj)
    have x4 := isExc_memSet x3 "start" (some (.int s))
    have x5 := isExc_memSet x4 "end" (some (.int e))
    have x6 := isExc_memSet x5 "reason" (some reason)
    refine ex_of_isExc x6 ?_ ?_
    · simp only [withArgs] at *
      simp only [unicodeDecodeErrorInit, baseExceptionInit, argNoKeywords, M.bind_app, getW_app,
        List.isEmpty_nil, excUpdate_app, List.length_cons, List.length_nil, Nat.reduceAdd,
        argCount_eq']
      simp [List.getD, g1, argU_ok' _ _ _ _ _ g1, hs, he, argU_ok' _ _ _ _ _ h3, hb, excUpdate_app]
      try rfl
    · intro x6
      simp only [ssizeMember]
      rw [x6.data]
      refine ⟨?_, ?_, ?_⟩
      · rw [memGet_memSet_ne _ "reason" "start" _ (by decide),
          memGet_memSet_ne _ "end" "start" _ (by decide), memGet_memSet_same]
      · rw [memGet_memSet_ne _ "reason" "end" _ (by decide), memGet_memSet_same]
      · rw [memGet_memSet_ne _ "reason" "object" _ (by decide),
          memGet_memSet_ne _ "end" "object" _ (by decide),
          memGet_memSet_ne _ "start" "object" _ (by decide), memGet_memSet_same]
  · intro rt a d d3 enc obj sv ev reason se sr bs s e w w2 w3 hx h1 hs he h3 hx3 hb hp
    have g1 : strOf (withArgs w a [enc, obj, sv, ev, reason]) enc = some se := by
      rw [strOf_excUpdW_eq hx]; exact h1
    have y1 := hx3.push (.val { cls := B.bytes, body := .bytes bs })
    have x2 := isExc_memSet y1 "encoding" (some enc)
    have x3 := isExc_memSet x2 "object" (some (.obj w3.heap.size))
    have x4 := isExc_memSet x3 "start" (some (.int s))
    have x5 := isExc_memSet x4 "end" (some (.int e))
    have x6 := isExc_memSet x5 "reason" (some reason)
    refine ex_of_isExc x6 ?_ ?_
    · simp only [withArgs] at *
      simp only [unicodeDecodeErrorInit, baseExceptionInit, argNoKeywords, M.bind_app, getW_app,
        List.isEmpty_nil, excUpdate_app, List.length_cons, List.length_nil, Nat.reduceAdd,
        argCount_eq']
      simp [List.getD, g1, argU_ok' _ _ _ _ _ g1, hs, he, argU_ok' _ _ _ _ _ h3, hb, bufferOf, hp,
        alloc_app, excUpdate_app]
      try rfl
    · intro x6
      simp only [ssizeMember]
      rw [x6.data]
      refine ⟨?_, ?_, ?_⟩
      · rw [memGet_memSet_ne _ "reason" "start" _ (by decide),
          memGet_memSet_ne _ "end" "start" _ (by decide), memGet_memSet_same]
      · rw [memGet_memSet_ne _ "reason" "end" _ (by decide), memGet_memSet_same]
      · rw [memGet_memSet_ne _ "reason" "object" _ (by decide),
          memGet_memSet_ne _ "end" "object" _ (by decide),
          memGet_memSet_ne _ "start" "object" _ (by decide), memGet_memSet_same]

/-! ## `SyntaxError` -/

/-- **A list or other iterable `info` goes through `tuple()`** (`:2805`): an exact list is parsed
as the tuple of its items, and anything else is iterated, so a non-iterable is the `TypeError`
of `iter()`, after `msg` was stored. -/
def SyntaxErrorInfoTuple : Prop :=
  (∀ (rt : Rt) (self : Val) (l : Addr) (o : Obj) (xs : List Val) (w : World),
    w.get l = .val o → o.cls = B.list → o.body = .list xs →
    syntaxErrorParseInfo rt self (.obj l) w = syntaxErrorParseInfo rt self (.tuple xs) w) ∧
  (∀ (rt : Rt) (self v : Val) (e : PyErr) (w w1 : World), (∀ ys, v ≠ .tuple ys) →
    typeOf w v ≠ B.list → rt.getIter v w = .err e w1 →
    syntaxErrorParseInfo rt self v w = .err e w1)

theorem syntaxErrorInfoTuple_proven : SyntaxErrorInfoTuple := by
  refine ⟨?_, ?_⟩
  · intro rt self l o xs w hc hcls hb
    have h := argsSetGet_proven.2.2.2.1 rt l o xs w hc hcls hb
    simp only [syntaxErrorParseInfo, M.bind_app, h]
    rfl
  · intro rt self v e w w1 hv hl hi
    have h := argsSetGet_proven.2.2.2.2.2.1 rt v e w w1 hv hl hi
    simp only [syntaxErrorParseInfo, M.bind_app, h]

/-- **Without a location, `str(SyntaxError)` is `str(msg)`** (`:2931-2932`): when `filename` is not
a `str` (NULL, or set to anything else) and `lineno` is not an exact `int` (NULL, `True`, a
float, ...), the result is `str(msg)`, `str(None)` when `msg` is unset. -/
def SyntaxErrorStrPlainAll : Prop :=
  ∀ (rt : Rt) (v : Val) (w : World),
    (∀ f, memGet (excDataOf w v) "filename" = some f → strOf w f = none) →
    (∀ l, memGet (excDataOf w v) "lineno" ≠ some (.int l)) →
    syntaxErrorStr rt v w = (Val.str <$> rt.str (orNone (memGet (excDataOf w v) "msg"))) w

theorem syntaxErrorStrPlainAll_proven : SyntaxErrorStrPlainAll := by
  intro rt v w h1 h2
  have hf : (match memGet (excDataOf w v) "filename" with
      | some f => (strOf w f).map myBasename
      | none => (none : Option String)) = none := by
    cases hq : memGet (excDataOf w v) "filename" with
    | none => rfl
    | some f => simp [h1 f hq]
  cases hq : memGet (excDataOf w v) "filename" with
  | none =>
    cases hl : memGet (excDataOf w v) "lineno" with
    | none => simp [syntaxErrorStr, hq, hl]
    | some x =>
      cases x <;> first | exact absurd hl (h2 _) | simp [syntaxErrorStr, hq, hl]
  | some f =>
    have hs := h1 f hq
    cases hl : memGet (excDataOf w v) "lineno" with
    | none => simp [syntaxErrorStr, hq, hl, hs]
    | some x =>
      cases x <;> first | exact absurd hl (h2 _) | simp [syntaxErrorStr, hq, hl, hs]

end PyLean.TypeObj
