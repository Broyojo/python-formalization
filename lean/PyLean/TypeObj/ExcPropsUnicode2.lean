import PyLean.TypeObj.ExcPropsGroup2
import PyLean.TypeObj.ExcPropsRest2

/-!
Properties of the Unicode errors (`Objects/exceptions.c:3064-4043`): the attribute checks, the
helpers behind the C API, the clipping functions, the three `__init__`s and `__str__`s.
-/

namespace PyLean.TypeObj

/-! ## Attribute checks -/

/-- **`check_unicode_error_attribute` and `as_unicode_error_attribute`** (`:3064-3098`): NULL is
`UnicodeError 'n' attribute is not set`; with `as_bytes` a non-`bytes` is `... must be a bytes`,
without it a non-`str` is `... must be a string`; otherwise the attribute itself is returned. -/
def UnicodeAttributeFull : Prop :=
  (∀ (name : String) (asBytes : Bool) (w : World), asUnicodeErrorAttribute none name asBytes w =
    .err (.exc B.TypeError s!"UnicodeError '{name}' attribute is not set" none) w) ∧
  (∀ (a : Val) (name : String) (w : World), bytesOf w a = none →
    checkUnicodeErrorAttribute (some a) name true w =
      .err (.exc B.TypeError s!"UnicodeError '{name}' attribute must be a bytes" none) w ∧
    asUnicodeErrorAttribute (some a) name true w =
      .err (.exc B.TypeError s!"UnicodeError '{name}' attribute must be a bytes" none) w) ∧
  (∀ (a : Val) (name : String) (w : World), strOf w a = none →
    asUnicodeErrorAttribute (some a) name false w =
      .err (.exc B.TypeError s!"UnicodeError '{name}' attribute must be a string" none) w) ∧
  (∀ (a : Val) (name : String) (b : List Nat) (w : World), bytesOf w a = some b →
    asUnicodeErrorAttribute (some a) name true w = .ok a w) ∧
  (∀ (a : Val) (name s : String) (w : World), strOf w a = some s →
    asUnicodeErrorAttribute (some a) name false w = .ok a w) ∧
  (∀ (self : Val) (n : String) (w : World), isSubtype w (typeOf w self) B.UnicodeError = true →
    checkUnicodeErrorType self n w = .ok () w)

theorem unicodeAttributeFull_proven : UnicodeAttributeFull := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro name asBytes w
    simp [asUnicodeErrorAttribute, checkUnicodeErrorAttribute, typeErr, raiseC]
  · intro a name w h
    constructor
    · simp [checkUnicodeErrorAttribute, h, typeErr, raiseC, String.append_assoc]; try rfl
    · simp [asUnicodeErrorAttribute, checkUnicodeErrorAttribute, h, typeErr, raiseC, String.append_assoc]; try rfl
  · intro a name w h
    simp [asUnicodeErrorAttribute, checkUnicodeErrorAttribute, h, typeErr, raiseC, String.append_assoc]; try rfl
  · intro a name b w h
    simp [asUnicodeErrorAttribute, checkUnicodeErrorAttribute, h]
  · intro a name s w h
    simp [asUnicodeErrorAttribute, checkUnicodeErrorAttribute, h]
  · intro self n w h
    simp [checkUnicodeErrorType, h]

/-! ## The C API helpers -/

/-- **The getters return the attributes, the start and end getters clip.** On a `UnicodeError`,
`PyUnicode*Error_GetEncoding` and `GetReason` return the `str` attribute, `GetObject` the object
when it is a `bytes` (decode) or a `str` (the others) and the attribute error otherwise, and
`GetStart`/`GetEnd` return the stored value clipped by `unicode_error_adjust_start`/`_end` to the
length of the object (`:3149-3180`, `:3487-3494`, `:3555-3562`). -/
def UnicodeGettersRead : Prop :=
  ∀ (k : UKind) (self : Val) (w : World), isSubtype w (typeOf w self) B.UnicodeError = true →
    (∀ (v : Val) (s : String), memGet (excDataOf w self) "encoding" = some v → strOf w v = some s →
      pyUnicodeErrorGetEncoding k self w = .ok v w) ∧
    (memGet (excDataOf w self) "encoding" = none → pyUnicodeErrorGetEncoding k self w =
      .err (.exc B.TypeError "UnicodeError 'encoding' attribute is not set" none) w) ∧
    (∀ (v : Val) (s : String), memGet (excDataOf w self) "reason" = some v → strOf w v = some s →
      pyUnicodeErrorGetReason k self w = .ok v w) ∧
    (∀ (v : Val), memGet (excDataOf w self) "object" = some v →
      (if k.asBytes then (bytesOf w v).isSome else (strOf w v).isSome) = true →
      pyUnicodeErrorGetObject k self w = .ok v w ∧
      pyUnicodeErrorGetStart k self w =
        .ok (unicodeErrorAdjustStart (ssizeMember (excDataOf w self) "start")
          (unicodeObjectLen w v k.asBytes)) w ∧
      pyUnicodeErrorGetEnd k self w =
        .ok (unicodeErrorAdjustEnd (ssizeMember (excDataOf w self) "end")
          (unicodeObjectLen w v k.asBytes)) w) ∧
    (∀ (v : Val), memGet (excDataOf w self) "object" = some v → k = .decode → bytesOf w v = none →
      pyUnicodeErrorGetObject k self w =
        .err (.exc B.TypeError "UnicodeError 'object' attribute must be a bytes" none) w)

theorem asAttr_ok {a : Val} {name : String} {asBytes : Bool} {w : World}
    (h : (if asBytes then (bytesOf w a).isSome else (strOf w a).isSome) = true) :
    asUnicodeErrorAttribute (some a) name asBytes w = .ok a w := by
  cases asBytes <;> simp at h <;> simp [asUnicodeErrorAttribute, checkUnicodeErrorAttribute, h]

theorem uMapApp {α β : Type} (f : α → β) (x : M α) (w : World) :
    (f <$> x) w = (x >>= fun a => pure (f a)) w := rfl

theorem unicodeGettersRead_proven : UnicodeGettersRead := by
  intro k self w hu
  have hc : ∀ n, checkUnicodeErrorType self n w = .ok () w := fun n => by
    simp [checkUnicodeErrorType, hu]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v s h1 h2
    simp only [pyUnicodeErrorGetEncoding, M.bind_app, hc, unicodeErrorGetEncodingImpl, getW_app, h1]
    simp [asUnicodeErrorAttribute, checkUnicodeErrorAttribute, h2]
  · intro h1
    simp only [pyUnicodeErrorGetEncoding, M.bind_app, hc, unicodeErrorGetEncodingImpl, getW_app, h1]
    simp [asUnicodeErrorAttribute, checkUnicodeErrorAttribute, typeErr, raiseC, String.append_assoc]; try rfl
  · intro v s h1 h2
    simp only [pyUnicodeErrorGetReason, M.bind_app, hc, unicodeErrorGetReasonImpl, getW_app, h1]
    simp [asUnicodeErrorAttribute, checkUnicodeErrorAttribute, h2]
  · intro v h1 h2
    have ha := asAttr_ok (name := "object") h2
    refine ⟨?_, ?_, ?_⟩
    · simp only [pyUnicodeErrorGetObject, M.bind_app, hc, unicodeErrorGetObjectImpl, getW_app, h1, ha]
    · simp only [pyUnicodeErrorGetStart, M.bind_app, hc, uMapApp, unicodeErrorGetParams,
        getW_app, h1, ha]
      rfl
    · simp only [pyUnicodeErrorGetEnd, M.bind_app, hc, uMapApp, unicodeErrorGetParams, getW_app,
        h1, ha]
      rfl
  · intro v h1 hk h2
    subst hk
    simp only [pyUnicodeErrorGetObject, M.bind_app, hc, unicodeErrorGetObjectImpl, getW_app, h1]
    simp [UKind.asBytes, asUnicodeErrorAttribute, checkUnicodeErrorAttribute, h2, typeErr, raiseC, String.append_assoc]; try rfl

/-- **The setters store the raw value.** On a `UnicodeError`, `PyUnicode*Error_SetStart(n)` and
`SetEnd(n)` succeed and store `n` itself, unclipped (`:3207-3229`), which is what `e.start` and
`e.end` read (`Py_T_PYSSIZET` members); `SetReason(r)` stores the `str` `r` (`:3188-3199`). -/
def UnicodeSettersStore : Prop :=
  ∀ (rt : Rt) (owner : Addr) (k : UKind) (a : Addr) (d : ExcData) (w : World), IsExc w a d →
    isSubtype w (typeOf w (.obj a)) B.UnicodeError = true →
    (∀ n : Int, ∃ w', pyUnicodeErrorSetStart k (.obj a) n w = .ok () w' ∧
      ssizeMember (excDataOf w' (.obj a)) "start" = n ∧
      excGetsetGet rt owner "start" (.obj a) w' = .ok (.int n) w') ∧
    (∀ n : Int, ∃ w', pyUnicodeErrorSetEnd k (.obj a) n w = .ok () w' ∧
      ssizeMember (excDataOf w' (.obj a)) "end" = n ∧
      excGetsetGet rt owner "end" (.obj a) w' = .ok (.int n) w') ∧
    (∀ r : String, ∃ w', pyUnicodeErrorSetReason k (.obj a) r w = .ok () w' ∧
      memGet (excDataOf w' (.obj a)) "reason" = some (.str r))

theorem unicodeSettersStore_proven : UnicodeSettersStore := by
  intro rt owner k a d w hx hu
  have hc : ∀ n, checkUnicodeErrorType (.obj a) n w = .ok () w := fun n => by
    simp [checkUnicodeErrorType, hu]
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have h1 := isExc_memSet hx "start" (some (.int n))
    refine ex_of_isExc h1 ?_ ?_
    · simp only [pyUnicodeErrorSetStart, M.bind_app, hc, unicodeErrorSetStartImpl, excUpdate_app]
    · intro h1
      refine ⟨?_, ?_⟩
      · rw [h1.data]; simp [ssizeMember, memGet_memSet_same]
      · simp [excGetsetGet, h1.body, ssizeMember, memGet_memSet_same]
  · intro n
    have h1 := isExc_memSet hx "end" (some (.int n))
    refine ex_of_isExc h1 ?_ ?_
    · simp only [pyUnicodeErrorSetEnd, M.bind_app, hc, unicodeErrorSetEndImpl, excUpdate_app]
    · intro h1
      refine ⟨?_, ?_⟩
      · rw [h1.data]; simp [ssizeMember, memGet_memSet_same]
      · simp [excGetsetGet, h1.body, ssizeMember, memGet_memSet_same]
  · intro r
    have h1 := isExc_memSet hx "reason" (some (.str r))
    refine ex_of_isExc h1 ?_ ?_
    · simp only [pyUnicodeErrorSetReason, M.bind_app, hc, unicodeErrorSetReasonImpl, excUpdate_app]
    · intro h1; rw [h1.data]; exact memGet_memSet_same _ _ _

/-- **The clipping keeps values in range** (`:3242-3337`). A start in `[0, objlen)` is kept, a
negative one becomes 0 and one at or past the end becomes `max 0 (objlen - 1)`; an end in
`[1, objlen]` is kept, one below 1 becomes `min 1 objlen` and one past the end becomes `objlen`;
the length is `end - start` when that is not negative, else 0. -/
def UnicodeAdjustKeeps : Prop :=
  (∀ s n : Int, 0 ≤ s → s < n → unicodeErrorAdjustStart s n = s) ∧
  (∀ s n : Int, s < 0 → 0 ≤ n → unicodeErrorAdjustStart s n = 0) ∧
  (∀ s n : Int, 0 ≤ s → 0 ≤ n → n ≤ s → unicodeErrorAdjustStart s n = max 0 (n - 1)) ∧
  (∀ e n : Int, 1 ≤ e → e ≤ n → unicodeErrorAdjustEnd e n = e) ∧
  (∀ e n : Int, e < 1 → 0 ≤ n → unicodeErrorAdjustEnd e n = min 1 n) ∧
  (∀ e n : Int, 1 ≤ e → n < e → unicodeErrorAdjustEnd e n = n) ∧
  (∀ s e : Int, s ≤ e → unicodeErrorAdjustLen s e = e - s) ∧
  (∀ s e : Int, e < s → unicodeErrorAdjustLen s e = 0)

theorem unicodeAdjustKeeps_proven : UnicodeAdjustKeeps := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s n h1 h2
    simp only [unicodeErrorAdjustStart]
    rw [if_neg (by omega), if_neg (by omega)]
  · intro s n h1 h2
    simp only [unicodeErrorAdjustStart, if_pos h1]
    by_cases hn : n = 0
    · subst hn; decide
    · rw [if_neg (by omega)]
  · intro s n h1 h2 h3
    simp only [unicodeErrorAdjustStart, if_neg (show ¬ s < 0 by omega), if_pos (show s ≥ n by omega)]
    by_cases hn : n = 0
    · subst hn; decide
    · have : (n == 0) = false := by simpa using hn
      rw [this]; simp only [Bool.false_eq_true, if_false]; omega
  · intro e n h1 h2
    simp only [unicodeErrorAdjustEnd]
    rw [if_neg (by omega), if_neg (by omega)]
  · intro e n h1 h2
    simp only [unicodeErrorAdjustEnd, if_pos h1]
    split <;> omega
  · intro e n h1 h2
    simp only [unicodeErrorAdjustEnd, if_neg (show ¬ e < 1 by omega), if_pos h2]
  · intro s e h
    simp only [unicodeErrorAdjustLen]
    rw [if_neg (by omega)]
  · intro s e h
    simp only [unicodeErrorAdjustLen]
    rw [if_pos (by omega)]

/-! ### Reads that an update of the exception does not change -/

theorem baseChain_congr {w w' : World} (h : ∀ t, tdata w' t = tdata w t) :
    ∀ (f : Nat) (a b : Addr), baseChain w' f a b = baseChain w f a b := by
  intro f
  induction f with
  | zero => intro a b; unfold baseChain; rw [h a]
  | succ f ih =>
    intro a b
    unfold baseChain
    rw [h a]
    rcases (tdata w a).base with _ | p
    · rfl
    · simp only [ih]

theorem isSubtype_excUpdW (w : World) (a : Addr) (f : ExcData → ExcData) (ha : a < w.heap.size)
    (x y : Addr) : isSubtype (excUpdW w a f) x y = isSubtype w x y := by
  have ht := fun t => tdata_excUpdW w a t f ha
  simp only [isSubtype, ht, size_excUpdW]
  cases (tdata w x).mro with
  | some _ => rfl
  | none => exact baseChain_congr ht _ _ _

theorem typeOf_excUpdW' (w : World) (a : Addr) (f : ExcData → ExcData) (ha : a < w.heap.size)
    (v : Val) : typeOf (excUpdW w a f) v = typeOf w v := by
  cases v with
  | obj b => exact typeOf_excUpdW w a b f ha
  | _ => rfl

theorem payloadOf_excUpdW_ne (w : World) (a : Addr) (f : ExcData → ExcData) (v : Val)
    (h : v ≠ .obj a) : payloadOf (excUpdW w a f) v = payloadOf w v := by
  cases v with
  | obj b =>
    have hb : a ≠ b := fun e => h (by rw [e])
    simp [payloadOf, get_excUpdW_ne _ _ _ _ hb]
  | _ => rfl

theorem ne_self_of_payload {w : World} {a : Addr} {d : ExcData} (hx : IsExc w a d) {v : Val}
    {p : Payload} (hp : payloadOf w v = some p) (hne : ∀ e, p ≠ .exc e) : v ≠ .obj a := by
  intro h
  subst h
  rw [hx.body] at hp
  cases hp
  exact hne d rfl

theorem strOf_excUpdW {w : World} {a : Addr} {d : ExcData} (hx : IsExc w a d)
    (f : ExcData → ExcData) {v : Val} {s : String} (h : strOf w v = some s) :
    strOf (excUpdW w a f) v = some s := by
  cases v with
  | str t => exact h
  | obj b =>
    have hp : payloadOf w (.obj b) = some (.boxed (.str s)) := by
      simp only [strOf] at h
      split at h <;> simp_all
    have hne := ne_self_of_payload hx hp (fun e h => Payload.noConfusion h)
    simp only [strOf]
    rw [payloadOf_excUpdW_ne _ _ _ _ hne, hp]
  | _ => simp [strOf, payloadOf] at h ⊢

theorem bytesOf_excUpdW {w : World} {a : Addr} {d : ExcData} (hx : IsExc w a d)
    (f : ExcData → ExcData) {v : Val} (hv : ∀ e, payloadOf w v ≠ some (.exc e)) :
    bytesOf (excUpdW w a f) v = bytesOf w v := by
  have hne : v ≠ .obj a := by
    intro h; subst h; exact hv d hx.body
  simp only [bytesOf, typeOf_excUpdW' _ _ _ hx.size, isSubtype_excUpdW _ _ _ hx.size,
    payloadOf_excUpdW_ne _ _ _ _ hne]

theorem IsExc.push {w : World} {a : Addr} {d : ExcData} (hx : IsExc w a d) (c : Cell) :
    IsExc { w with heap := w.heap.push c } a d := by
  constructor
  · show a < (w.heap.push c).size
    rw [Array.size_push]; exact Nat.lt_succ_of_lt hx.size
  · have := hx.body
    simp only [payloadOf] at this ⊢
    rw [get_push_lt _ _ hx.size]
    exact this

/-! ## `__init__` -/

theorem argN_int (rt : Rt) (n : Int) (w : World) (h : inSsize n = true) :
    argN rt (.int n) w = .ok n w := by
  simp [argN, excNumberIndex, intOf, excAsSsizeLong, h]

/-- **`UnicodeEncodeError.__init__` stores its five arguments** (`:3715-3738`): with a `str`
encoding, object and reason and two `int`s in `Py_ssize_t`, `args` and the five members are set,
`start` and `end` raw. -/
def UnicodeEncodeInitStores : Prop :=
  ∀ (rt : Rt) (a : Addr) (d : ExcData) (enc obj reason : Val) (s e : Int) (se so sr : String)
    (w : World), IsExc w a d → strOf w enc = some se → strOf w obj = some so →
    strOf w reason = some sr → inSsize s = true → inSsize e = true →
    ∃ w', unicodeEncodeErrorInit rt (.obj a) [enc, obj, .int s, .int e, reason] [] w = .ok () w' ∧
      excArgs w' (.obj a) = [enc, obj, .int s, .int e, reason] ∧
      memGet (excDataOf w' (.obj a)) "encoding" = some enc ∧
      memGet (excDataOf w' (.obj a)) "object" = some obj ∧
      ssizeMember (excDataOf w' (.obj a)) "start" = s ∧
      ssizeMember (excDataOf w' (.obj a)) "end" = e ∧
      memGet (excDataOf w' (.obj a)) "reason" = some reason

theorem argU_ok' (f : Option String) (i : Nat) (v : Val) (s : String) (w : World)
    (h : strOf w v = some s) : argU f i v w = .ok () w := by
  simp [argU, h]

theorem argCount_eq' (n : Nat) (w : World) : argCount none n n n w = .ok () w := by
  simp [argCount]

theorem unicodeEncodeInitStores_proven : UnicodeEncodeInitStores := by
  intro rt a d enc obj reason s e se so sr w hx h1 h2 h3 hs he
  have x1 := hx.update (fun d => { d with args := [enc, obj, .int s, .int e, reason] })
  have g1 := strOf_excUpdW hx (fun d => { d with args := [enc, obj, .int s, .int e, reason] }) h1
  have g2 := strOf_excUpdW hx (fun d => { d with args := [enc, obj, .int s, .int e, reason] }) h2
  have g3 := strOf_excUpdW hx (fun d => { d with args := [enc, obj, .int s, .int e, reason] }) h3
  have x2 := isExc_memSet x1 "encoding" (some enc)
  have x3 := isExc_memSet x2 "object" (some obj)
  have x4 := isExc_memSet x3 "start" (some (.int s))
  have x5 := isExc_memSet x4 "end" (some (.int e))
  have x6 := isExc_memSet x5 "reason" (some reason)
  refine ex_of_isExc x6 ?_ ?_
  · simp only [unicodeEncodeErrorInit, baseExceptionInit, argNoKeywords, M.bind_app, getW_app,
      List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false, excUpdate_app, List.length_cons,
      List.length_nil, Nat.reduceAdd, argCount_eq']
    simp [List.getD, argU_ok' _ _ _ _ _ g1, argU_ok' _ _ _ _ _ g2, argU_ok' _ _ _ _ _ g3,
      argN_int _ _ _ hs, argN_int _ _ _ he, excUpdate_app]
    try rfl
  · intro x6
    simp only [excArgs, ssizeMember]
    rw [x6.data]
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [memGet_memSet_ne _ "reason" "encoding" _ (by decide),
        memGet_memSet_ne _ "end" "encoding" _ (by decide),
        memGet_memSet_ne _ "start" "encoding" _ (by decide),
        memGet_memSet_ne _ "object" "encoding" _ (by decide), memGet_memSet_same]
    · rw [memGet_memSet_ne _ "reason" "object" _ (by decide),
        memGet_memSet_ne _ "end" "object" _ (by decide),
        memGet_memSet_ne _ "start" "object" _ (by decide), memGet_memSet_same]
    · rw [memGet_memSet_ne _ "reason" "start" _ (by decide),
        memGet_memSet_ne _ "end" "start" _ (by decide), memGet_memSet_same]
    · rw [memGet_memSet_ne _ "reason" "end" _ (by decide), memGet_memSet_same]
    · rw [memGet_memSet_same]

/-- **`UnicodeTranslateError.__init__` stores its four arguments** (`:3944-3964`). -/
def UnicodeTranslateInitStores : Prop :=
  ∀ (rt : Rt) (a : Addr) (d : ExcData) (obj reason : Val) (s e : Int) (so sr : String)
    (w : World), IsExc w a d → strOf w obj = some so → strOf w reason = some sr →
    inSsize s = true → inSsize e = true →
    ∃ w', unicodeTranslateErrorInit rt (.obj a) [obj, .int s, .int e, reason] [] w = .ok () w' ∧
      excArgs w' (.obj a) = [obj, .int s, .int e, reason] ∧
      memGet (excDataOf w' (.obj a)) "object" = some obj ∧
      ssizeMember (excDataOf w' (.obj a)) "start" = s ∧
      ssizeMember (excDataOf w' (.obj a)) "end" = e ∧
      memGet (excDataOf w' (.obj a)) "reason" = some reason

theorem unicodeTranslateInitStores_proven : UnicodeTranslateInitStores := by
  intro rt a d obj reason s e so sr w hx h2 h3 hs he
  have x1 := hx.update (fun d => { d with args := [obj, .int s, .int e, reason] })
  have g2 := strOf_excUpdW hx (fun d => { d with args := [obj, .int s, .int e, reason] }) h2
  have g3 := strOf_excUpdW hx (fun d => { d with args := [obj, .int s, .int e, reason] }) h3
  have x3 := isExc_memSet x1 "object" (some obj)
  have x4 := isExc_memSet x3 "start" (some (.int s))
  have x5 := isExc_memSet x4 "end" (some (.int e))
  have x6 := isExc_memSet x5 "reason" (some reason)
  refine ex_of_isExc x6 ?_ ?_
  · simp only [unicodeTranslateErrorInit, baseExceptionInit, argNoKeywords, M.bind_app, getW_app,
      List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false, excUpdate_app, List.length_cons,
      List.length_nil, Nat.reduceAdd, argCount_eq']
    simp [List.getD, argU_ok' _ _ _ _ _ g2, argU_ok' _ _ _ _ _ g3,
      argN_int _ _ _ hs, argN_int _ _ _ he, excUpdate_app]
    try rfl
  · intro x6
    simp only [excArgs, ssizeMember]
    rw [x6.data]
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · rw [memGet_memSet_ne _ "reason" "object" _ (by decide),
        memGet_memSet_ne _ "end" "object" _ (by decide),
        memGet_memSet_ne _ "start" "object" _ (by decide), memGet_memSet_same]
    · rw [memGet_memSet_ne _ "reason" "start" _ (by decide),
        memGet_memSet_ne _ "end" "start" _ (by decide), memGet_memSet_same]
    · rw [memGet_memSet_ne _ "reason" "end" _ (by decide), memGet_memSet_same]
    · rw [memGet_memSet_same]

/-- **`UnicodeDecodeError.__init__` keeps a `bytes` object and copies any other buffer**
(`:3838-3852`): with a `str` encoding and reason, two `int`s in `Py_ssize_t`, and an object that is
a `bytes`, the object is stored as it is; a non-`bytes` buffer (a `bytearray`) is copied into a new
`bytes` with the same contents; anything else is the `TypeError` of `PyObject_GetBuffer`, whose
type name is cut by `%.100s` (`Objects/abstract.c:450-452`), raised after `args` was stored. -/
def UnicodeDecodeInitStores : Prop :=
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (enc obj reason : Val) (s e : Int) (se sr : String)
    (bs : List Nat) (w : World), IsExc w a d → strOf w enc = some se → bytesOf w obj = some bs →
    strOf w reason = some sr → inSsize s = true → inSsize e = true →
    ∃ w', unicodeDecodeErrorInit rt (.obj a) [enc, obj, .int s, .int e, reason] [] w = .ok () w' ∧
      excArgs w' (.obj a) = [enc, obj, .int s, .int e, reason] ∧
      memGet (excDataOf w' (.obj a)) "encoding" = some enc ∧
      memGet (excDataOf w' (.obj a)) "object" = some obj ∧
      ssizeMember (excDataOf w' (.obj a)) "start" = s ∧
      ssizeMember (excDataOf w' (.obj a)) "end" = e ∧
      memGet (excDataOf w' (.obj a)) "reason" = some reason) ∧
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (enc obj reason : Val) (s e : Int) (se sr : String)
    (bs : List Nat) (w : World), IsExc w a d → strOf w enc = some se → bytesOf w obj = none →
    payloadOf w obj = some (.bytes bs) →
    strOf w reason = some sr → inSsize s = true → inSsize e = true →
    ∃ w', unicodeDecodeErrorInit rt (.obj a) [enc, obj, .int s, .int e, reason] [] w = .ok () w' ∧
      memGet (excDataOf w' (.obj a)) "object" = some (.obj w.heap.size) ∧
      payloadOf w' (.obj w.heap.size) = some (.bytes bs) ∧
      typeOf w' (.obj w.heap.size) = B.bytes) ∧
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (enc obj reason : Val) (s e : Int) (se sr : String)
    (w : World), IsExc w a d → strOf w enc = some se → bytesOf w obj = none →
    (∀ p, payloadOf w obj = some p → (∀ bs, p ≠ .bytes bs) ∧ (∀ e, p ≠ .exc e)) →
    strOf w reason = some sr → inSsize s = true → inSsize e = true →
    unicodeDecodeErrorInit rt (.obj a) [enc, obj, .int s, .int e, reason] [] w =
      .err (.exc B.TypeError
        s!"a bytes-like object is required, not '{String.ofList (truncUtf8 100 (typeName w obj).toList)}'" none)
        (excUpdW w a fun d => { d with args := [enc, obj, .int s, .int e, reason] }))

theorem unicodeDecodeInitStores_proven : UnicodeDecodeInitStores := by
  refine ⟨?_, ?_, ?_⟩
  · intro rt a d enc obj reason s e se sr bs w hx h1 h2 h3 hs he
    let f : ExcData → ExcData := fun d => { d with args := [enc, obj, .int s, .int e, reason] }
    have x1 := hx.update f
    have hpo : ∀ e, payloadOf w obj ≠ some (.exc e) := by
      intro e' hp
      simp [bytesOf, hp] at h2
    have g1 := strOf_excUpdW hx f h1
    have g2 : bytesOf (excUpdW w a f) obj = some bs := by rw [bytesOf_excUpdW hx f hpo, h2]
    have g3 := strOf_excUpdW hx f h3
    have x2 := isExc_memSet x1 "encoding" (some enc)
    have x3 := isExc_memSet x2 "object" (some obj)
    have x4 := isExc_memSet x3 "start" (some (.int s))
    have x5 := isExc_memSet x4 "end" (some (.int e))
    have x6 := isExc_memSet x5 "reason" (some reason)
    refine ex_of_isExc x6 ?_ ?_
    · simp only [unicodeDecodeErrorInit, baseExceptionInit, argNoKeywords, M.bind_app, getW_app,
        List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false, excUpdate_app,
        List.length_cons, List.length_nil, Nat.reduceAdd, argCount_eq']
      simp [List.getD, argU_ok' _ _ _ _ _ g1, argU_ok' _ _ _ _ _ g3,
        argN_int _ _ _ hs, argN_int _ _ _ he, g2, excUpdate_app, f]
      try rfl
    · intro x6
      simp only [excArgs, ssizeMember]
      rw [x6.data]
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
      · rw [memGet_memSet_ne _ "reason" "encoding" _ (by decide),
          memGet_memSet_ne _ "end" "encoding" _ (by decide),
          memGet_memSet_ne _ "start" "encoding" _ (by decide),
          memGet_memSet_ne _ "object" "encoding" _ (by decide), memGet_memSet_same]
      · rw [memGet_memSet_ne _ "reason" "object" _ (by decide),
          memGet_memSet_ne _ "end" "object" _ (by decide),
          memGet_memSet_ne _ "start" "object" _ (by decide), memGet_memSet_same]
      · rw [memGet_memSet_ne _ "reason" "start" _ (by decide),
          memGet_memSet_ne _ "end" "start" _ (by decide), memGet_memSet_same]
      · rw [memGet_memSet_ne _ "reason" "end" _ (by decide), memGet_memSet_same]
      · rw [memGet_memSet_same]
  · intro rt a d enc obj reason s e se sr bs w hx h1 h2 hp h3 hs he
    have x1 := hx.update (fun d => { d with args := [enc, obj, .int s, .int e, reason] })
    have hpo : ∀ e, payloadOf w obj ≠ some (.exc e) := by
      intro e' h; rw [hp] at h; cases h
    have hne : obj ≠ .obj a := by intro h; subst h; exact hpo d hx.body
    have g1 := strOf_excUpdW hx (fun d => { d with args := [enc, obj, .int s, .int e, reason] }) h1
    have g2 : bytesOf (excUpdW w a fun d => { d with args := [enc, obj, .int s, .int e, reason] }) obj
        = none := by rw [bytesOf_excUpdW hx _ hpo, h2]
    have g3 := strOf_excUpdW hx (fun d => { d with args := [enc, obj, .int s, .int e, reason] }) h3
    have gp : payloadOf (excUpdW w a fun d => { d with args := [enc, obj, .int s, .int e, reason] }) obj
        = some (.bytes bs) := by
      rw [payloadOf_excUpdW_ne _ _ _ _ hne, hp]
    have hsz : (excUpdW w a fun d => { d with args := [enc, obj, .int s, .int e, reason] }).heap.size
        = w.heap.size := size_excUpdW _ _ _
    have y1 := x1.push (.val { cls := B.bytes, body := .bytes bs })
    have y2 := isExc_memSet y1 "encoding" (some enc)
    have y3 := isExc_memSet y2 "object" (some (.obj w.heap.size))
    have y4 := isExc_memSet y3 "start" (some (.int s))
    have y5 := isExc_memSet y4 "end" (some (.int e))
    have y6 := isExc_memSet y5 "reason" (some reason)
    have hnew : a ≠ w.heap.size := Nat.ne_of_lt hx.size
    refine ex_of_isExc y6 ?_ ?_
    · simp only [unicodeDecodeErrorInit, baseExceptionInit, argNoKeywords, M.bind_app, getW_app,
        List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false, excUpdate_app,
        List.length_cons, List.length_nil, Nat.reduceAdd, argCount_eq']
      simp [List.getD, argU_ok' _ _ _ _ _ g1, argU_ok' _ _ _ _ _ g3,
        argN_int _ _ _ hs, argN_int _ _ _ he, g2, bufferOf, gp, alloc_app, excUpdate_app, hsz]
      try rfl
    · intro y6
      have hget : ∀ (f : ExcData → ExcData) (W : World), W.heap.size = w.heap.size + 1 →
          w.heap.size ≠ a → (excUpdW W a f).get w.heap.size = W.get w.heap.size := by
        intro f W _ h; exact get_excUpdW_ne _ _ _ _ (Ne.symm h)
      refine ⟨?_, ?_, ?_⟩
      · rw [y6.data]
        rw [memGet_memSet_ne _ "reason" "object" _ (by decide),
          memGet_memSet_ne _ "end" "object" _ (by decide),
          memGet_memSet_ne _ "start" "object" _ (by decide), memGet_memSet_same]
      · simp only [payloadOf]
        rw [get_excUpdW_ne _ _ _ _ hnew, get_excUpdW_ne _ _ _ _ hnew, get_excUpdW_ne _ _ _ _ hnew,
          get_excUpdW_ne _ _ _ _ hnew, get_excUpdW_ne _ _ _ _ hnew]
        rw [← hsz, get_push_size]
      · simp only [typeOf]
        rw [get_excUpdW_ne _ _ _ _ hnew, get_excUpdW_ne _ _ _ _ hnew, get_excUpdW_ne _ _ _ _ hnew,
          get_excUpdW_ne _ _ _ _ hnew, get_excUpdW_ne _ _ _ _ hnew]
        rw [← hsz, get_push_size]
  · intro rt a d enc obj reason s e se sr w hx h1 h2 hp h3 hs he
    let f : ExcData → ExcData := fun d => { d with args := [enc, obj, .int s, .int e, reason] }
    have hpo : ∀ e, payloadOf w obj ≠ some (.exc e) := by
      intro e' h; exact (hp _ h).2 e' rfl
    have hne : obj ≠ .obj a := by intro h; subst h; exact hpo d hx.body
    have g1 := strOf_excUpdW hx f h1
    have g2 : bytesOf (excUpdW w a f) obj = none := by rw [bytesOf_excUpdW hx f hpo, h2]
    have g3 := strOf_excUpdW hx f h3
    have gb : bufferOf (excUpdW w a f) obj = typeErr
        s!"a bytes-like object is required, not '{String.ofList (truncUtf8 100 (typeName w obj).toList)}'" := by
      have hpn : payloadOf (excUpdW w a f) obj = payloadOf w obj := payloadOf_excUpdW_ne _ _ _ _ hne
      have htn : typeName (excUpdW w a f) obj = typeName w obj := by
        simp only [typeName, tpName, typeOf_excUpdW' _ _ _ hx.size, tdata_excUpdW _ _ _ _ hx.size]
      unfold bufferOf
      rw [hpn, htn]
      cases hq : payloadOf w obj with
      | none => rfl
      | some p =>
        have := (hp p hq).1
        cases p <;> first | rfl | exact absurd rfl (this _)
    simp only [unicodeDecodeErrorInit, baseExceptionInit, argNoKeywords, M.bind_app, getW_app,
      List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false, excUpdate_app,
      List.length_cons, List.length_nil, Nat.reduceAdd, argCount_eq']
    simp [List.getD, argU_ok' _ _ _ _ _ g1, argU_ok' _ _ _ _ _ g3,
      argN_int _ _ _ hs, argN_int _ _ _ he, g2, f, gb, typeErr, raiseC]
    try rfl

/-! ## `__str__` -/

/-- **`UnicodeEncodeError.__str__`** (`:3740-3801`). With `object` NULL it is `''`. Otherwise
`str(reason)` and `str(encoding)` run first (`<NULL>` for a deleted one), each in the world the
last left; `object` is then read again and must still be a `str` (a `__str__` may have replaced
it, `:3763-3766`); with one bad character the message names it with `\x`, `\u` or `\U` escapes,
otherwise the range `start`-`end - 1`. -/
def UnicodeEncodeStrFormats : Prop :=
  (∀ (rt : Rt) (self : Val) (w : World), memGet (excDataOf w self) "object" = none →
    unicodeEncodeErrorStr rt self w = .ok (.str "") w) ∧
  (∀ (rt : Rt) (w : World), strOrNull rt none w = .ok "<NULL>" w) ∧
  (∀ (rt : Rt) (self o : Val) (rs es : String) (w w1 w2 : World),
    memGet (excDataOf w self) "object" = some o →
    strOrNull rt (memGet (excDataOf w self) "reason") w = .ok rs w1 →
    strOrNull rt (memGet (excDataOf w self) "encoding") w1 = .ok es w2 →
    (∀ (o2 : Val) (t : String), memGet (excDataOf w2 self) "object" = some o2 → strOf w2 o2 = some t →
      (unicodeStrSingle (ssizeMember (excDataOf w2 self) "start") (ssizeMember (excDataOf w2 self) "end")
          t.toList.length = true →
        unicodeEncodeErrorStr rt self w = .ok (.str s!"'{es}' codec can't encode character '{badCharEscape (charAt t (ssizeMember (excDataOf w2 self) "start"))}' in position {ssizeMember (excDataOf w2 self) "start"}: {rs}") w2) ∧
      (unicodeStrSingle (ssizeMember (excDataOf w2 self) "start") (ssizeMember (excDataOf w2 self) "end")
          t.toList.length = false →
        unicodeEncodeErrorStr rt self w = .ok (.str s!"'{es}' codec can't encode characters in position {ssizeMember (excDataOf w2 self) "start"}-{ssizeWrap (ssizeMember (excDataOf w2 self) "end" - 1)}: {rs}") w2)) ∧
    (∀ (o2 : Val), memGet (excDataOf w2 self) "object" = some o2 → strOf w2 o2 = none →
      unicodeEncodeErrorStr rt self w =
        .err (.exc B.TypeError "UnicodeError 'object' attribute must be a string" none) w2))

theorem unicodeEncodeStrFormats_proven : UnicodeEncodeStrFormats := by
  refine ⟨?_, ?_, ?_⟩
  · intro rt self w h
    simp [unicodeEncodeErrorStr, h]
  · intro rt w; rfl
  · intro rt self o rs es w w1 w2 h0 h1 h2
    refine ⟨?_, ?_⟩
    · intro o2 t h3 h4
      refine ⟨?_, ?_⟩
      · intro hs
        simp only [unicodeEncodeErrorStr, M.bind_app, getW_app, h0, h1, h2]
        simp [checkUnicodeErrorAttribute, h3, h4, unicodeEncodeErrorStr.orNoneU, hs]
      · intro hs
        simp only [unicodeEncodeErrorStr, M.bind_app, getW_app, h0, h1, h2]
        simp [checkUnicodeErrorAttribute, h3, h4, unicodeEncodeErrorStr.orNoneU, hs]
    · intro o2 h3 h4
      simp only [unicodeEncodeErrorStr, M.bind_app, getW_app, h0, h1, h2]
      simp [checkUnicodeErrorAttribute, h3, h4, typeErr, raiseC, String.append_assoc]
      try rfl

/-- **`UnicodeDecodeError.__str__`** (`:3863-3924`): the same shape over the bytes object, with
`byte 0x%02x` for one bad byte, and the re-check that `object` is still a `bytes`
(`:3886-3889`). -/
def UnicodeDecodeStrFormats : Prop :=
  (∀ (rt : Rt) (self : Val) (w : World), memGet (excDataOf w self) "object" = none →
    unicodeDecodeErrorStr rt self w = .ok (.str "") w) ∧
  (∀ (rt : Rt) (self o : Val) (rs es : String) (w w1 w2 : World),
    memGet (excDataOf w self) "object" = some o →
    strOrNull rt (memGet (excDataOf w self) "reason") w = .ok rs w1 →
    strOrNull rt (memGet (excDataOf w self) "encoding") w1 = .ok es w2 →
    (∀ (o2 : Val) (bs : List Nat), memGet (excDataOf w2 self) "object" = some o2 → bytesOf w2 o2 = some bs →
      (unicodeStrSingle (ssizeMember (excDataOf w2 self) "start") (ssizeMember (excDataOf w2 self) "end")
          bs.length = true →
        unicodeDecodeErrorStr rt self w = .ok (.str s!"'{es}' codec can't decode byte 0x{hexPad 2 (bs.getD (ssizeMember (excDataOf w2 self) "start").toNat 0)} in position {ssizeMember (excDataOf w2 self) "start"}: {rs}") w2) ∧
      (unicodeStrSingle (ssizeMember (excDataOf w2 self) "start") (ssizeMember (excDataOf w2 self) "end")
          bs.length = false →
        unicodeDecodeErrorStr rt self w = .ok (.str s!"'{es}' codec can't decode bytes in position {ssizeMember (excDataOf w2 self) "start"}-{ssizeWrap (ssizeMember (excDataOf w2 self) "end" - 1)}: {rs}") w2)) ∧
    (∀ (o2 : Val), memGet (excDataOf w2 self) "object" = some o2 → bytesOf w2 o2 = none →
      unicodeDecodeErrorStr rt self w =
        .err (.exc B.TypeError "UnicodeError 'object' attribute must be a bytes" none) w2))

theorem unicodeDecodeStrFormats_proven : UnicodeDecodeStrFormats := by
  refine ⟨?_, ?_⟩
  · intro rt self w h
    simp [unicodeDecodeErrorStr, h]
  · intro rt self o rs es w w1 w2 h0 h1 h2
    refine ⟨?_, ?_⟩
    · intro o2 bs h3 h4
      refine ⟨?_, ?_⟩
      · intro hs
        simp only [unicodeDecodeErrorStr, M.bind_app, getW_app, h0, h1, h2]
        simp [checkUnicodeErrorAttribute, h3, h4, hs]
      · intro hs
        simp only [unicodeDecodeErrorStr, M.bind_app, getW_app, h0, h1, h2]
        simp [checkUnicodeErrorAttribute, h3, h4, hs]
    · intro o2 h3 h4
      simp only [unicodeDecodeErrorStr, M.bind_app, getW_app, h0, h1, h2]
      simp [checkUnicodeErrorAttribute, h3, h4, typeErr, raiseC, String.append_assoc]
      try rfl

/-- **`UnicodeTranslateError.__str__`** (`:3967-4022`): only `str(reason)` runs, then the same
re-check and formats as for encoding, without an encoding. -/
def UnicodeTranslateStrFormats : Prop :=
  (∀ (rt : Rt) (self : Val) (w : World), memGet (excDataOf w self) "object" = none →
    unicodeTranslateErrorStr rt self w = .ok (.str "") w) ∧
  (∀ (rt : Rt) (self o : Val) (rs : String) (w w1 : World),
    memGet (excDataOf w self) "object" = some o →
    strOrNull rt (memGet (excDataOf w self) "reason") w = .ok rs w1 →
    (∀ (o2 : Val) (t : String), memGet (excDataOf w1 self) "object" = some o2 → strOf w1 o2 = some t →
      (unicodeStrSingle (ssizeMember (excDataOf w1 self) "start") (ssizeMember (excDataOf w1 self) "end")
          t.toList.length = true →
        unicodeTranslateErrorStr rt self w = .ok (.str s!"can't translate character '{badCharEscape (charAt t (ssizeMember (excDataOf w1 self) "start"))}' in position {ssizeMember (excDataOf w1 self) "start"}: {rs}") w1) ∧
      (unicodeStrSingle (ssizeMember (excDataOf w1 self) "start") (ssizeMember (excDataOf w1 self) "end")
          t.toList.length = false →
        unicodeTranslateErrorStr rt self w = .ok (.str s!"can't translate characters in position {ssizeMember (excDataOf w1 self) "start"}-{ssizeWrap (ssizeMember (excDataOf w1 self) "end" - 1)}: {rs}") w1)) ∧
    (∀ (o2 : Val), memGet (excDataOf w1 self) "object" = some o2 → strOf w1 o2 = none →
      unicodeTranslateErrorStr rt self w =
        .err (.exc B.TypeError "UnicodeError 'object' attribute must be a string" none) w1))

theorem unicodeTranslateStrFormats_proven : UnicodeTranslateStrFormats := by
  refine ⟨?_, ?_⟩
  · intro rt self w h
    simp [unicodeTranslateErrorStr, h]
  · intro rt self o rs w w1 h0 h1
    refine ⟨?_, ?_⟩
    · intro o2 t h3 h4
      refine ⟨?_, ?_⟩
      · intro hs
        simp only [unicodeTranslateErrorStr, M.bind_app, getW_app, h0, h1]
        simp [checkUnicodeErrorAttribute, h3, h4, hs]
      · intro hs
        simp only [unicodeTranslateErrorStr, M.bind_app, getW_app, h0, h1]
        simp [checkUnicodeErrorAttribute, h3, h4, hs]
    · intro o2 h3 h4
      simp only [unicodeTranslateErrorStr, M.bind_app, getW_app, h0, h1]
      simp [checkUnicodeErrorAttribute, h3, h4, typeErr, raiseC, String.append_assoc]
      try rfl

/-- **The escapes of one character** (`:3772-3780`): `\x` with two digits up to 0xff, `\u` with
four up to 0xffff, `\U` with eight above, in lowercase hex; checked on the three characters of
the 3.15.2 runs. -/
def BadCharEscapes : Prop :=
  badCharEscape 0xe9 = "\\xe9" ∧ badCharEscape 0x100 = "\\u0100" ∧
  badCharEscape 0x1f600 = "\\U0001f600" ∧ badCharEscape 0x61 = "\\x61" ∧ hexPad 2 0xff = "ff"

theorem badCharEscapes_proven : BadCharEscapes := by
  unfold BadCharEscapes; decide +kernel

end PyLean.TypeObj
