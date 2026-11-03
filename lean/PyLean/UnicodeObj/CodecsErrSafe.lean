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

/-- The exceptions a standard handler raises: its argument (which is then an exception), a
`TypeError`, the failure to load `unicodedata`'s C API, or the UTF-8 encoder's error on the
`encoding` attribute. Never anything internal. -/
def ErrOk (H : Hier) (capi : Except PyExc (Nat → Option Str)) (e : ExcObj) : HErr → Prop
  | .reraise => H.sub e.cls "BaseException" = true
  | .exc x => x.className = "TypeError" ∨ capi = .error x ∨
      ∃ enc, e.encoding = .str enc ∧ utf8Encode enc .strict = .error x

/-- A returned position lies inside the `object` attribute, and past the clipped `start` when
the clipped range is not empty: the codec loop moves on. -/
def PosOk (e : ExcObj) (pos : Nat) : Prop :=
  ∃ l, (e.object = .str l ∨ e.object = .bytes l) ∧ pos ≤ l.length ∧
    (stOf e l.length < enOf e l.length → stOf e l.length < pos)

def ResOk (H : Hier) (capi : Except PyExc (Nat → Option Str)) (e : ExcObj) : HPy Body → Prop
  | .ok b => PosOk e b.pos
  | .error x => ErrOk H capi e x

/-- `unicodedata` names fit the 256-byte buffer of codecs.c:1091 (NAME_MAXLEN). -/
def NamesFit (g : Nat → Option Str) : Prop := ∀ c n, g c = some n → n.length < 256

theorem typeErr_ok (H : Hier) (capi) (e : ExcObj) (x : HErr) (h : ∃ m, x = .exc (.typeError m)) :
    ErrOk H capi e x := by
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
    · simp [wrongType, raiseT, ResOk, ErrOk, PyExc.className]

theorem replace_resOk (H : Hier) (hH : HierOk H) (capi) (e : ExcObj) :
    ResOk H capi e (replaceErrors H e) := by
  unfold replaceErrors
  split
  · exact resOk_params H capi e false _ (fun p hp => posOk_stop e false p hp)
  · split
    · rename_i hE hD
      unfold replaceDecode decodeGetEnd checkType
      simp only [hH.dec_uerr hD, if_true, bind, Except.bind]
      cases hp : getParams e true with
      | error x => simp only [ResOk]; exact typeErr_ok H capi e x (getParams_err e true x hp)
      | ok p => simp only [pure, Except.pure, ResOk]; exact posOk_stop e true p hp
    · split
      · exact resOk_params H capi e false _ (fun p hp => posOk_stop e false p hp)
      · simp [wrongType, raiseT, ResOk, ErrOk, PyExc.className]

theorem xml_resOk (H : Hier) (capi) (e : ExcObj) : ResOk H capi e (xmlCharRefReplaceErrors H e) := by
  unfold xmlCharRefReplaceErrors
  split
  · simp [wrongType, raiseT, ResOk, ErrOk, PyExc.className]
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
      · simp [wrongType, raiseT, ResOk, ErrOk, PyExc.className]

theorem ok_bind {α β ε : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl
theorem err_bind {α β ε : Type} (x : ε) (f : α → Except ε β) : (Except.error x >>= f) = .error x := rfl

theorem resOk_bind_ite {H : Hier} {capi} {e : ExcObj} {c : Prop} [Decidable c] {x : List Nat}
    {k : List Nat → HPy Body} (hT : c → ResOk H capi e (k x)) (hF : ¬c → ErrOk H capi e .reraise) :
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
  · simp [wrongType, raiseT, ResOk, ErrOk, PyExc.className]
  · cases hcap : capi with
    | error x => simp [bind, Except.bind, ResOk, ErrOk]
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
    (h : encCodeOf H e expect = .error x) : ErrOk H capi e x := by
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

theorem reraise_ok (H : Hier) (hH : HierOk H) (capi) (e : ExcObj) (h : H.sub e.cls "UnicodeError" = true) :
    ErrOk H capi e .reraise := hH.uerr_base h

theorem pass_resOk (H : Hier) (hH : HierOk H) (capi) (e : ExcObj) :
    ResOk H capi e (surrogatePassErrors H e) := by
  unfold surrogatePassErrors
  split
  · rename_i hE
    unfold surrogatePassEncode
    cases hc : encCodeOf H e "UnicodeEncodeError" with
    | error x => rw [err_bind]; exact encCode_errOk H capi e _ x hc
    | ok code =>
      rw [ok_bind]
      split
      · exact reraise_ok H hH capi e (hH.enc_uerr hE)
      · rename_i hu
        apply resOk_params'
        intro p hp
        simp only
        rw [passWrite_eq]
        apply resOk_bind_ite
        · intro _
          simp only [pure, Except.pure, ResOk]
          have hb := bytelength_pos code hu
          exact posOk_guard e false p hp code.bytelength hb.1 (by omega)
        · intro _; exact reraise_ok H hH capi e (hH.enc_uerr hE)
  · split
    · rename_i hE hD
      unfold surrogatePassDecode
      cases hc : encCodeOf H e "UnicodeDecodeError" with
      | error x => rw [err_bind]; exact encCode_errOk H capi e _ x hc
      | ok code =>
        rw [ok_bind]
        split
        · exact reraise_ok H hH capi e (hH.dec_uerr hD)
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
            · exact reraise_ok H hH capi e (hH.dec_uerr hD)
            · simp only [pure, Except.pure, ResOk]
              refine ⟨l, ?_, by omega, fun _ => by omega⟩
              rcases hl with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
          · simp only [hr, if_false]
            have : (!isSurrogate 0) = true := by decide
            rw [if_pos this]
            exact reraise_ok H hH capi e (hH.dec_uerr hD)
    · simp [wrongType, raiseT, ResOk, ErrOk, PyExc.className]

theorem escConsume_length : ∀ (k : Nat) (l : List Nat), (escConsume k l).length ≤ k
  | 0, _ => by simp [escConsume]
  | _ + 1, [] => by simp [escConsume]
  | k + 1, b :: bs => by
    simp only [escConsume]
    split
    · simp
    · simp only [List.length_cons]; have := escConsume_length k bs; omega

theorem esc_resOk (H : Hier) (hH : HierOk H) (capi) (e : ExcObj) :
    ResOk H capi e (surrogateEscapeErrors H e) := by
  unfold surrogateEscapeErrors
  split
  · rename_i hE
    unfold surrogateEscapeEncode
    apply resOk_params'
    intro p hp
    rw [escWrite_eq]
    apply resOk_bind_ite
    · intro _; simp only [pure, Except.pure, ResOk]; exact posOk_stop e false p hp
    · intro _; exact reraise_ok H hH capi e (hH.enc_uerr hE)
  · split
    · rename_i hE hD
      unfold surrogateEscapeDecode
      apply resOk_params'
      intro p hp
      obtain ⟨l, hl, rfl⟩ := getParams_ok e true p hp
      have hst := stOf_le e l.length
      have hen := enOf_le e l.length
      have hc := escConsume_length (min 4 (enOf e l.length - stOf e l.length)) (l.drop (stOf e l.length))
      simp only
      split
      · exact reraise_ok H hH capi e (hH.dec_uerr hD)
      · rename_i hz
        simp only [pure, Except.pure, ResOk]
        refine ⟨l, ?_, by omega, fun _ => by omega⟩
        rcases hl with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
    · simp [wrongType, raiseT, ResOk, ErrOk, PyExc.className]

/-- **No internal error, positions in range.** For every object handed to a standard handler,
whatever its class and attributes: the handler raises only its argument (and only when that is
an exception), a `TypeError`, the failure to load `unicodedata`'s C API, or the UTF-8 encoder's
error on the `encoding` attribute; and a position it returns lies inside `object`, past the
clipped `start` whenever the clipped range is not empty. -/
def HandlersSafe : Prop :=
  ∀ (H : Hier) (capi : Except PyExc (Nat → Option Str)) (h : ErrHandler) (e : ExcObj),
    HierOk H → (∀ g, capi = .ok g → NamesFit g) →
    match callBuiltin H capi h e with
    | .ok (_, pos) => PosOk e pos
    | .error x => ErrOk H capi e x

theorem resOk_map (H : Hier) (capi) (e : ExcObj) (r : HPy Body) (h : ResOk H capi e r) :
    match Body.result <$> r with
    | .ok (_, pos) => PosOk e pos
    | .error x => ErrOk H capi e x := by
  cases r <;> simpa [Functor.map, Except.map, Body.result, ResOk] using h

theorem handlersSafe_proven : HandlersSafe := by
  intro H capi h e hH hc
  cases h with
  | strict =>
    simp only [callBuiltin, strictErrors]
    by_cases hb : H.sub e.cls "BaseException" = true
    · simp only [hb, if_true, ErrOk]
    · simp [hb, raiseT, ErrOk, PyExc.className]
  | ignore => exact resOk_map H capi e _ (ignore_resOk H hH capi e)
  | replace => exact resOk_map H capi e _ (replace_resOk H hH capi e)
  | xmlcharrefreplace => exact resOk_map H capi e _ (xml_resOk H capi e)
  | backslashreplace => exact resOk_map H capi e _ (backslash_resOk H capi e)
  | namereplace => exact resOk_map H capi e _ (name_resOk H capi hc e)
  | surrogatepass => exact resOk_map H capi e _ (pass_resOk H hH capi e)
  | surrogateescape => exact resOk_map H capi e _ (esc_resOk H hH capi e)

end PyLean.UnicodeObj.Codecs
