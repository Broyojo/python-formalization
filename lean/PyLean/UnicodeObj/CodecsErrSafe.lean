import PyLean.UnicodeObj.CodecsErrAgree

/-!
The handlers on every exception object, whatever its class and attributes: what they raise,
where the position they return lies, when they succeed, and that each writes exactly the buffer
it allocated.
-/

namespace PyLean.UnicodeObj.Codecs

open PyLean PyLean.UnicodeObj

/-! ## Accessors -/

theorem asAttr_err (slot : Slot) (name : String) (ab : Bool) (x : HErr)
    (h : asAttr slot name ab = .error x) : ∃ m, x = .exc (.typeError m) := by
  cases slot <;> cases ab <;> simp [asAttr, raiseT] at h <;> exact ⟨_, h.symm⟩

theorem asAttr_ok (slot : Slot) (name : String) (ab : Bool) (l : List Nat)
    (h : asAttr slot name ab = .ok l) :
    (ab = false ∧ slot = .str l) ∨ (ab = true ∧ slot = .bytes l) := by
  unfold asAttr at h
  cases slot <;> cases ab <;> simp [raiseT] at h <;> simp [h]

theorem getParams_err (e : ExcObj) (ab : Bool) (x : HErr) (h : getParams e ab = .error x) :
    ∃ m, x = .exc (.typeError m) := by
  unfold getParams at h
  cases ha : asAttr e.object "object" ab with
  | error y => rw [ha] at h; simp [bind, Except.bind] at h; subst h; exact asAttr_err _ _ _ _ ha
  | ok l => rw [ha] at h; simp [bind, Except.bind, pure, Except.pure] at h

theorem getParams_ok (e : ExcObj) (ab : Bool) (p : Params) (h : getParams e ab = .ok p) :
    ∃ l, ((ab = false ∧ e.object = .str l) ∨ (ab = true ∧ e.object = .bytes l)) ∧
      p = ⟨l, l.length, stOf e l.length, enOf e l.length, enOf e l.length - stOf e l.length⟩ := by
  cases ha : asAttr e.object "object" ab with
  | error y =>
    unfold getParams at h; rw [ha] at h; simp [bind, Except.bind] at h
  | ok l =>
    refine ⟨l, asAttr_ok _ _ _ _ ha, ?_⟩
    rw [getParams_of e ab l ha] at h
    exact (Except.ok.inj h).symm

theorem checkType_err (H : Hier) (e : ExcObj) (s : String) (x : HErr) (h : checkType H e s = .error x) :
    ∃ m, x = .exc (.typeError m) := by
  unfold checkType at h; split at h
  · simp at h
  · simp [raiseT] at h; exact ⟨_, h.symm⟩

/-! ## What a handler may raise, and where it may stop -/

/-- The exceptions a handler body raises before `_PyErr_SetObject`'s normalization step: a
call of `PyErr_SetObject(type(exc), exc)` with a class that has the exception flag, a
`TypeError`, the failure to load `unicodedata`'s C API, or the UTF-8 encoder's error on the
`encoding` attribute. -/
def ErrOkRaw (H : Hier) (capi : Except PyExc (Nat → Option Str)) (e : ExcObj) : HErr → Prop
  | .reraise => H.excFlag e.cls = true
  | .normalize => False
  | .exc x => x.className = "TypeError" ∨ capi = .error x ∨
      ∃ enc, e.encoding = .str enc ∧ utf8Encode enc .strict = .error x

/-- The exceptions a standard handler raises: its argument (when its class has the exception
flag and `issubclass(cls, cls)` holds), the normalized `type(exc)(exc)` (when that `issubclass`
is false), what the metaclass's `__subclasscheck__` raised, a `TypeError`, the failure to load
`unicodedata`'s C API, or the UTF-8 encoder's error on the `encoding` attribute. Never anything
internal. -/
def ErrOk (H : Hier) (capi : Except PyExc (Nat → Option Str)) (e : ExcObj) : HErr → Prop
  | .reraise => H.excFlag e.cls = true ∧ H.subcheck e.cls = .ok true
  | .normalize => H.subcheck e.cls = .ok false
  | .exc x => x.className = "TypeError" ∨ capi = .error x ∨
      (∃ enc, e.encoding = .str enc ∧ utf8Encode enc .strict = .error x) ∨
      H.subcheck e.cls = .error x

/-- A returned position lies inside the `object` attribute, and past the clipped `start` when
the clipped range is not empty: the codec loop moves on. -/
def PosOk (e : ExcObj) (pos : Nat) : Prop :=
  ∃ l, (e.object = .str l ∨ e.object = .bytes l) ∧ pos ≤ l.length ∧
    (stOf e l.length < enOf e l.length → stOf e l.length < pos)

def ResOk (H : Hier) (capi : Except PyExc (Nat → Option Str)) (e : ExcObj) : HPy Body → Prop
  | .ok b => PosOk e b.pos
  | .error x => ErrOkRaw H capi e x

/-- `unicodedata` names fit the 256-byte buffer of codecs.c:1091 (NAME_MAXLEN). -/
def NamesFit (g : Nat → Option Str) : Prop := ∀ c n, g c = some n → n.length < 256

theorem typeErr_ok (H : Hier) (capi) (e : ExcObj) (x : HErr) (h : ∃ m, x = .exc (.typeError m)) :
    ErrOkRaw H capi e x := by
  obtain ⟨m, rfl⟩ := h; left; rfl

theorem resOk_params (H : Hier) (capi) (e : ExcObj) (ab : Bool) (f : Params → Body)
    (hf : ∀ p, getParams e ab = .ok p → PosOk e (f p).pos) :
    ResOk H capi e (do let p ← getParams e ab; pure (f p)) := by
  cases hp : getParams e ab with
  | error x => simp only [bind, Except.bind, ResOk]; exact typeErr_ok H capi e x (getParams_err e ab x hp)
  | ok p => simp only [bind, Except.bind, pure, Except.pure, ResOk]; exact hf p hp

theorem posOk_stop (e : ExcObj) (ab : Bool) (p : Params) (hp : getParams e ab = .ok p) :
    PosOk e p.stop := by
  obtain ⟨l, hl, rfl⟩ := getParams_ok e ab p hp
  refine ⟨l, ?_, enOf_le e l.length, fun h => h⟩
  rcases hl with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]

theorem guard_pos (w : Nat) (hw : 0 < w) (hw2 : w ≤ 10) (l : List Nat) (st en : Nat) (hen : en ≤ l.length) :
    (guardRange w ⟨l, l.length, st, en, en - st⟩).1 ≤ l.length ∧
    (st < en → st < (guardRange w ⟨l, l.length, st, en, en - st⟩).1) := by
  have : 1 ≤ ssizeMaxN / w := by unfold ssizeMaxN; exact (Nat.le_div_iff_mul_le hw).2 (by omega)
  unfold guardRange
  split <;> simp <;> omega

theorem posOk_guard (e : ExcObj) (ab : Bool) (p : Params) (hp : getParams e ab = .ok p) (w : Nat)
    (hw : 0 < w) (hw2 : w ≤ 10) : PosOk e (guardRange w p).1 := by
  obtain ⟨l, hl, rfl⟩ := getParams_ok e ab p hp
  have := guard_pos w hw hw2 l (stOf e l.length) (enOf e l.length) (enOf_le e l.length)
  refine ⟨l, ?_, this.1, this.2⟩
  rcases hl with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]

theorem nameSizeLoop_bounds (g : Nat → Option Str) (hg : NamesFit g) :
    ∀ (l : List Nat) (imax r : Nat),
      imax ≤ (nameSizeLoop g l imax r).1 ∧ (nameSizeLoop g l imax r).1 ≤ imax + l.length ∧
      (l ≠ [] → r ≤ ssizeMaxN - 300 → imax < (nameSizeLoop g l imax r).1)
  | [], imax, r => by simp [nameSizeLoop]
  | c :: cs, imax, r => by
    have hs : nameSize g c ≤ 260 := by
      cases hc : g c with
      | none => simp only [nameSize, hc]; unfold hexWidth; split <;> (try split) <;> omega
      | some n => simp only [nameSize, hc]; have := hg c n hc; simp; omega
    simp only [nameSizeLoop]
    split
    · rename_i hbr
      refine ⟨Nat.le_refl _, by simp, fun _ hr => ?_⟩
      exfalso; unfold ssizeMaxN at *; omega
    · have ih := nameSizeLoop_bounds g hg cs (imax + 1) (r + nameSize g c)
      simp only [List.length_cons]
      refine ⟨by omega, by omega, fun _ _ => by omega⟩

/-! ## Each handler -/

theorem ignore_resOk (H : Hier) (hH : HierOk H) (capi) (e : ExcObj) :
    ResOk H capi e (ignoreErrors H e) := by
  unfold ignoreErrors
  split
  · exact resOk_params H capi e false _ (fun p hp => posOk_stop e false p hp)
  · split
    · exact resOk_params H capi e true _ (fun p hp => posOk_stop e true p hp)
    · simp [wrongType, raiseT, ResOk, ErrOkRaw, PyExc.className]

theorem replace_resOk (H : Hier) (capi) (e : ExcObj) :
    ResOk H capi e (replaceErrors H e) := by
  unfold replaceErrors
  split
  · exact resOk_params H capi e false _ (fun p hp => posOk_stop e false p hp)
  · split
    · rename_i hE hD
      unfold replaceDecode decodeGetEnd
      cases hc : checkType H e "UnicodeDecodeError" with
      | error x =>
        simp only [hc, bind, Except.bind, ResOk]; exact typeErr_ok H capi e x (checkType_err _ _ _ x hc)
      | ok _ =>
        simp only [hc, bind, Except.bind]
        cases hp : getParams e true with
        | error x => simp only [ResOk]; exact typeErr_ok H capi e x (getParams_err e true x hp)
        | ok p => simp only [pure, Except.pure, ResOk]; exact posOk_stop e true p hp
    · split
      · exact resOk_params H capi e false _ (fun p hp => posOk_stop e false p hp)
      · simp [wrongType, raiseT, ResOk, ErrOkRaw, PyExc.className]

theorem xml_resOk (H : Hier) (capi) (e : ExcObj) : ResOk H capi e (xmlCharRefReplaceErrors H e) := by
  unfold xmlCharRefReplaceErrors
  split
  · simp [wrongType, raiseT, ResOk, ErrOkRaw, PyExc.className]
  · exact resOk_params H capi e false _ (fun p hp => posOk_guard e false p hp 10 (by omega) (by omega))

theorem backslash_resOk (H : Hier) (capi) (e : ExcObj) :
    ResOk H capi e (backslashReplaceErrors H e) := by
  unfold backslashReplaceErrors backslashEncode backslashDecode
  split
  · exact resOk_params H capi e false _ (fun p hp => posOk_guard e false p hp 10 (by omega) (by omega))
  · split
    · exact resOk_params H capi e true _ (fun p hp => posOk_stop e true p hp)
    · split
      · exact resOk_params H capi e false _ (fun p hp => posOk_guard e false p hp 10 (by omega) (by omega))
      · simp [wrongType, raiseT, ResOk, ErrOkRaw, PyExc.className]

theorem ok_bind {α β ε : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl
theorem err_bind {α β ε : Type} (x : ε) (f : α → Except ε β) : (Except.error x >>= f) = .error x := rfl

theorem resOk_bind_ite {H : Hier} {capi} {e : ExcObj} {c : Prop} [Decidable c] {x : List Nat}
    {k : List Nat → HPy Body} (hT : c → ResOk H capi e (k x)) (hF : ¬c → ErrOkRaw H capi e .reraise) :
    ResOk H capi e ((if c then (.ok x : HPy (List Nat)) else .error .reraise) >>= k) := by
  by_cases hc : c
  · rw [if_pos hc, ok_bind]; exact hT hc
  · rw [if_neg hc, err_bind]; exact hF hc

theorem resOk_params' (H : Hier) (capi) (e : ExcObj) (ab : Bool) (k : Params → HPy Body)
    (hk : ∀ p, getParams e ab = .ok p → ResOk H capi e (k p)) :
    ResOk H capi e (getParams e ab >>= k) := by
  cases hp : getParams e ab with
  | error x => rw [err_bind]; exact typeErr_ok H capi e x (getParams_err e ab x hp)
  | ok p => rw [ok_bind]; exact hk p hp

theorem name_resOk (H : Hier) (capi) (hc : ∀ g, capi = .ok g → NamesFit g) (e : ExcObj) :
    ResOk H capi e (nameReplaceErrors H capi e) := by
  unfold nameReplaceErrors
  split
  · simp [wrongType, raiseT, ResOk, ErrOkRaw, PyExc.className]
  · cases hcap : capi with
    | error x => simp [bind, Except.bind, ResOk, ErrOkRaw]
    | ok g =>
      simp only [pure, Except.pure, ok_bind]
      apply resOk_params'
      intro p hp
      simp only [pure, Except.pure, ResOk]
      obtain ⟨l, hl, rfl⟩ := getParams_ok e false p hp
      have hlen := slice_length l (stOf e l.length) (enOf e l.length) (enOf_le e l.length)
      have hb := nameSizeLoop_bounds g (hc g hcap) (slice l (stOf e l.length) (enOf e l.length))
        (stOf e l.length) 0
      have hen := enOf_le e l.length
      have hst := stOf_le e l.length
      dsimp only
      refine ⟨l, ?_, by omega, fun hlt => hb.2.2 ?_ (by unfold ssizeMaxN; omega)⟩
      · rcases hl with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
      · intro h0; rw [h0] at hlen; simp at hlen; omega

theorem stdEncoding_err (enc : Str) (x : HErr) (h : stdEncoding enc = .error x) :
    ∃ y, x = .exc y ∧ utf8Encode enc .strict = .error y := by
  unfold stdEncoding at h
  cases hu : utf8Encode enc .strict with
  | error y => rw [hu] at h; simp at h; exact ⟨y, h.symm, rfl⟩
  | ok u => rw [hu] at h; simp at h

theorem encCode_errOk (H : Hier) (capi) (e : ExcObj) (expect : String) (x : HErr)
    (h : encCodeOf H e expect = .error x) : ErrOkRaw H capi e x := by
  unfold encCodeOf getEncoding at h
  cases hc : checkType H e expect with
  | error y => rw [hc] at h; simp [bind, Except.bind] at h; subst h; exact typeErr_ok H capi e y (checkType_err H e expect y hc)
  | ok _ =>
    rw [hc] at h
    simp only [bind, Except.bind] at h
    cases ha : asAttr e.encoding "encoding" false with
    | error y => rw [ha] at h; simp at h; subst h; exact typeErr_ok H capi e y (asAttr_err _ _ _ _ ha)
    | ok enc =>
      rw [ha] at h; simp only at h
      obtain ⟨y, rfl, hy⟩ := stdEncoding_err enc x h
      right; right
      exact ⟨enc, (asAttr_ok _ _ _ _ ha).elim (fun h => h.2) (fun h => absurd h.1 (by simp)), hy⟩

theorem bytelength_pos (code : EncCode) (h : code ≠ .unknown) : 0 < code.bytelength ∧ code.bytelength ≤ 4 := by
  cases code <;> simp [EncCode.bytelength] at *

theorem reraise_ok (H : Hier) (capi) (e : ExcObj) (h : H.excFlag e.cls = true) :
    ErrOkRaw H capi e .reraise := h

/-- The scope of `HandlersSafe`: an encode or decode error has the exception flag. -/
def FlagOk (H : Hier) (e : ExcObj) : Prop :=
  H.isEnc e.cls = true ∨ H.isDec e.cls = true → H.excFlag e.cls = true

theorem pass_resOk (H : Hier) (capi) (e : ExcObj) (hF : FlagOk H e) :
    ResOk H capi e (surrogatePassErrors H e) := by
  unfold surrogatePassErrors
  split
  · rename_i hE
    have f := hF (Or.inl hE)
    unfold surrogatePassEncode
    try simp only [bail_flag f, bailOn_flag f]
    cases hc : encCodeOf H e "UnicodeEncodeError" with
    | error x => rw [err_bind]; exact encCode_errOk H capi e _ x hc
    | ok code =>
      rw [ok_bind]
      split
      · exact reraise_ok H capi e f
      · rename_i hu
        apply resOk_params'
        intro p hp
        try simp only
        rw [passWrite_eq]
        apply resOk_bind_ite
        · intro _
          simp only [pure, Except.pure, ResOk]
          have hb := bytelength_pos code hu
          exact posOk_guard e false p hp code.bytelength hb.1 (by omega)
        · intro _; exact reraise_ok H capi e f
  · split
    · rename_i hE hD
      have f := hF (Or.inr hD)
      unfold surrogatePassDecode
      try simp only [bail_flag f]
      cases hc : encCodeOf H e "UnicodeDecodeError" with
      | error x => rw [err_bind]; exact encCode_errOk H capi e _ x hc
      | ok code =>
        rw [ok_bind]
        split
        · exact reraise_ok H capi e f
        · rename_i hu
          apply resOk_params'
          intro p hp
          obtain ⟨l, hl, rfl⟩ := getParams_ok e true p hp
          have hst := stOf_le e l.length
          have hb := bytelength_pos code hu
          simp only
          by_cases hr : l.length - stOf e l.length ≥ code.bytelength
          · simp only [hr, if_true]
            split
            · exact reraise_ok H capi e f
            · simp only [pure, Except.pure, ResOk]
              refine ⟨l, ?_, by omega, fun _ => by omega⟩
              rcases hl with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
          · simp only [hr, if_false]
            have : (!isSurrogate 0) = true := by decide
            rw [if_pos this]
            exact reraise_ok H capi e f
    · simp [wrongType, raiseT, ResOk, ErrOkRaw, PyExc.className]

theorem escConsume_length : ∀ (k : Nat) (l : List Nat), (escConsume k l).length ≤ k
  | 0, _ => by simp [escConsume]
  | _ + 1, [] => by simp [escConsume]
  | k + 1, b :: bs => by
    simp only [escConsume]
    split
    · simp
    · simp only [List.length_cons]; have := escConsume_length k bs; omega

theorem esc_resOk (H : Hier) (capi) (e : ExcObj) (hF : FlagOk H e) :
    ResOk H capi e (surrogateEscapeErrors H e) := by
  unfold surrogateEscapeErrors
  split
  · rename_i hE
    have f := hF (Or.inl hE)
    unfold surrogateEscapeEncode
    try simp only [bailOn_flag f]
    apply resOk_params'
    intro p hp
    rw [escWrite_eq]
    apply resOk_bind_ite
    · intro _; simp only [pure, Except.pure, ResOk]; exact posOk_stop e false p hp
    · intro _; exact reraise_ok H capi e f
  · split
    · rename_i hE hD
      have f := hF (Or.inr hD)
      unfold surrogateEscapeDecode
      try simp only [bail_flag f]
      apply resOk_params'
      intro p hp
      obtain ⟨l, hl, rfl⟩ := getParams_ok e true p hp
      have hst := stOf_le e l.length
      have hen := enOf_le e l.length
      have hc := escConsume_length (min 4 (enOf e l.length - stOf e l.length)) (l.drop (stOf e l.length))
      simp only
      split
      · exact reraise_ok H capi e f
      · rename_i hz
        simp only [pure, Except.pure, ResOk]
        refine ⟨l, ?_, by omega, fun _ => by omega⟩
        rcases hl with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
    · simp [wrongType, raiseT, ResOk, ErrOkRaw, PyExc.className]

/-- **No internal error, positions in range**, for every object of any class and with any
attributes handed to a standard handler, provided an encode or decode error has the exception
flag (`FlagOk`; scope: only a custom `mro()` on a base class breaks it, see
`HandlersSafeAll`). The handler raises only its argument (when its class has the flag and
`issubclass(cls, cls)` holds), the normalized `type(exc)(exc)` (when that is false), what a
metaclass `__subclasscheck__` raised, a `TypeError`, the failure to load `unicodedata`'s C API,
or the UTF-8 encoder's error on the `encoding` attribute; and a position it returns lies inside `object`, past the clipped
`start` whenever the clipped range is not empty. -/
def HandlersSafe : Prop :=
  ∀ (H : Hier) (capi : Except PyExc (Nat → Option Str)) (h : ErrHandler) (e : ExcObj),
    HierOk H → (∀ g, capi = .ok g → NamesFit g) → FlagOk H e →
    match callBuiltin H capi h e with
    | .ok (_, pos) => PosOk e pos
    | .error x => ErrOk H capi e x

theorem resOk_map (H : Hier) (capi) (e : ExcObj) (r : HPy Body) (h : ResOk H capi e r) :
    match Body.result <$> r with
    | .ok (_, pos) => PosOk e pos
    | .error x => ErrOkRaw H capi e x := by
  cases r <;> simpa [Functor.map, Except.map, Body.result, ResOk] using h

/-- `_PyErr_SetObject`'s normalization step keeps what a body may raise inside `ErrOk`. -/
theorem step_lift (H : Hier) (capi) (e : ExcObj) (r : HPy (Rep × Nat))
    (h : match r with
      | .ok (_, pos) => PosOk e pos
      | .error x => ErrOkRaw H capi e x) :
    match setObjectStep H e r with
    | .ok (_, pos) => PosOk e pos
    | .error x => ErrOk H capi e x := by
  rcases r with x | ⟨_, pos⟩
  · cases x with
    | exc x =>
      simp only [setObjectStep, ErrOk]
      simp only [ErrOkRaw] at h
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    | reraise =>
      simp only [ErrOkRaw] at h
      simp only [setObjectStep]
      rcases hs : H.subcheck e.cls with y | b
      · simp [ErrOk, hs]
      · cases b <;> simp [ErrOk, hs, h]
    | normalize => simp [ErrOkRaw] at h
  · exact h

theorem handlersSafe_proven : HandlersSafe := by
  intro H capi h e hH hc hF
  apply step_lift
  cases h with
  | strict =>
    simp only [callRaw, strictErrors]
    by_cases hb : H.excFlag e.cls = true
    · simp only [hb, if_true, ErrOkRaw]
    · simp [hb, raiseT, ErrOkRaw, PyExc.className]
  | ignore => exact resOk_map H capi e _ (ignore_resOk H hH capi e)
  | replace => exact resOk_map H capi e _ (replace_resOk H capi e)
  | xmlcharrefreplace => exact resOk_map H capi e _ (xml_resOk H capi e)
  | backslashreplace => exact resOk_map H capi e _ (backslash_resOk H capi e)
  | namereplace => exact resOk_map H capi e _ (name_resOk H capi hc e)
  | surrogatepass => exact resOk_map H capi e _ (pass_resOk H capi e hF)
  | surrogateescape => exact resOk_map H capi e _ (esc_resOk H capi e hF)

/-- **The same for every class.** The surrogate handlers re-raise their argument with
`PyErr_SetObject(PyExceptionInstance_Class(exc), exc)` without the check `strict` makes; for a
class below `UnicodeEncodeError` by MRO but without the exception flag (a subclass of a class
whose metaclass `mro()` leaves out `BaseException`), `_PyErr_SetObject` raises `SystemError`. -/
def HandlersSafeAll : Prop :=
  ∀ (H : Hier) (capi : Except PyExc (Nat → Option Str)) (h : ErrHandler) (e : ExcObj),
    HierOk H → (∀ g, capi = .ok g → NamesFit g) →
    match callBuiltin H capi h e with
    | .ok (_, pos) => PosOk e pos
    | .error x => ErrOk H capi e x

theorem builtinSub_enc (c : String) (h : builtinSub c "UnicodeEncodeError" = true) :
    c = "UnicodeEncodeError" := by
  unfold builtinSub ancestors at h
  split at h <;> simp_all

theorem builtinSub_dec (c : String) (h : builtinSub c "UnicodeDecodeError" = true) :
    c = "UnicodeDecodeError" := by
  unfold builtinSub ancestors at h
  split at h <;> simp_all

/-- `class M(type): def mro(cls): return [cls, UnicodeEncodeError, object]`,
`class A(UnicodeEncodeError, metaclass=M)`, `class B(A)`: `B` is below `UnicodeEncodeError` by
MRO, and its `tp_base` `A` has no `BaseException` in its MRO, so `B` lacks the flag. -/
def oddHier : Hier :=
  { sub := fun c b => if c = "B" then b == "UnicodeEncodeError" else builtinSub c b
    excFlag := fun c => c != "B"
    subcheck := fun _ => .ok true }

theorem oddHier_ok : HierOk oddHier := by
  have nb : ∀ c ∈ builtinClasses, c ≠ "B" := by
    intro c hc; simp [builtinClasses] at hc; rcases hc with h | h | h | h | h | h | h | h | h <;>
      subst h <;> decide
  refine ⟨fun c hc b => by simp [oddHier, nb c hc], fun c hc => by simp [oddHier, nb c hc],
    fun c _ => rfl, ?_, ?_, ?_⟩
  all_goals
    intro c ⟨h1, h2⟩
    by_cases hB : c = "B"
    · subst hB; simp [oddHier] at h1 h2
    · simp only [oddHier, hB, if_false] at h1 h2
      first
        | (have := builtinSub_enc c h1; subst this; revert h2; decide)
        | (have := builtinSub_dec c h1; subst this; revert h2; decide)

def oddExc : ExcObj :=
  { cls := "B", tpName := "B", clsRepr := "<class '__main__.B'>", encoding := .null,
    object := .str [0xff], start := 0, stop := 1 }

theorem oddExc_systemError :
    callBuiltin oddHier (.ok fun _ => none) .surrogateescape oddExc =
      .error (.exc (.named "SystemError"
        "_PyErr_SetObject: exception <class '__main__.B'> is not a BaseException subclass")) := by
  rfl

theorem handlersSafeAll_refuted : ¬ HandlersSafeAll := by
  intro h
  have := h oddHier (.ok fun _ => none) .surrogateescape oddExc oddHier_ok (fun g hg c n hc => by
    cases hg; simp at hc)
  rw [oddExc_systemError] at this
  simp [ErrOk, PyExc.className, oddExc, oddHier] at this

/-! ## Classes with a custom `mro()` -/

/-- **What a custom `mro()` changes.** On a class below `UnicodeEncodeError` or
`UnicodeDecodeError` whose MRO leaves out `UnicodeError`, `PyUnicode*Error_GetEncoding` and
`PyUnicodeDecodeError_GetEnd` refuse the object (exceptions.c:3127-3137), so `surrogatepass`
and, on a decode error, `replace` raise "expecting a UnicodeEncodeError object, got X" (resp.
UnicodeDecodeError); and on a class without the exception flag `strict` raises "codec must pass
exception instance", whatever its MRO. -/
def OddClasses : Prop :=
  ∀ (H : Hier) (capi : Except PyExc (Nat → Option Str)) (e : ExcObj), HierOk H →
    (H.sub e.cls "UnicodeError" = false →
      (H.isEnc e.cls = true → callBuiltin H capi .surrogatepass e =
        raiseT s!"expecting a {("UnicodeEncodeError" : String)} object, got {e.tpName}") ∧
      (H.isDec e.cls = true → callBuiltin H capi .surrogatepass e =
        raiseT s!"expecting a {("UnicodeDecodeError" : String)} object, got {e.tpName}" ∧
        callBuiltin H capi .replace e = raiseT s!"expecting a {("UnicodeDecodeError" : String)} object, got {e.tpName}")) ∧
    (H.excFlag e.cls = false → callBuiltin H capi .strict e = raiseT "codec must pass exception instance")

theorem oddClasses_proven : OddClasses := by
  intro H capi e hH
  refine ⟨fun hU => ⟨fun hE => ?_, fun hD => ⟨?_, ?_⟩⟩, fun hf => ?_⟩
  · simp [callBuiltin, callRaw, setObjectStep, surrogatePassErrors, hE, surrogatePassEncode, encCodeOf, getEncoding,
      checkType, hU, raiseT, bind, Except.bind, Functor.map, Except.map]
  · have hE := hH.dec_not_enc hD
    simp [callBuiltin, callRaw, setObjectStep, surrogatePassErrors, hE, hD, surrogatePassDecode, encCodeOf, getEncoding,
      checkType, hU, raiseT, bind, Except.bind, Functor.map, Except.map]
  · have hE := hH.dec_not_enc hD
    simp [callBuiltin, callRaw, setObjectStep, replaceErrors, hE, hD, replaceDecode, decodeGetEnd, checkType, hU, raiseT,
      bind, Except.bind, Functor.map, Except.map]
  · simp [callBuiltin, callRaw, setObjectStep, strictErrors, hf, raiseT]

end PyLean.UnicodeObj.Codecs
