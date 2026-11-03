import PyLean.UnicodeObj.CodecsErr

/-!
Lemmas about the handler model of `CodecsErr.lean`: the accessors, the per-character
writers against the codec-loop model of `CodecHandlers.lean`, and the hierarchy.
-/

namespace PyLean.UnicodeObj.Codecs

open PyLean PyLean.UnicodeObj

/-! ## The hierarchy -/

theorem HierOk.sub_trans {H : Hier} (hH : HierOk H) {a b c : String} (h1 : H.sub a b = true)
    (h2 : H.sub b c = true) : H.sub a c = true := hH.2.1 a b c h1 h2

theorem HierOk.base {H : Hier} (hH : HierOk H) {c b : String} (h : builtinBase c = some b) :
    H.sub c b = true := hH.2.2.1 c b h

/-- Every class below `UnicodeError` is below `BaseException`. -/
theorem HierOk.uerr_base {H : Hier} (hH : HierOk H) {c : String} (h : H.sub c "UnicodeError" = true) :
    H.sub c "BaseException" = true := by
  have h1 := hH.base (c := "UnicodeError") (b := "ValueError") rfl
  have h2 := hH.base (c := "ValueError") (b := "Exception") rfl
  have h3 := hH.base (c := "Exception") (b := "BaseException") rfl
  exact hH.sub_trans (hH.sub_trans (hH.sub_trans h h1) h2) h3

theorem HierOk.enc_uerr {H : Hier} (hH : HierOk H) {c : String} (h : H.isEnc c = true) :
    H.sub c "UnicodeError" = true :=
  hH.sub_trans h (hH.base (c := "UnicodeEncodeError") rfl)

theorem HierOk.dec_uerr {H : Hier} (hH : HierOk H) {c : String} (h : H.isDec c = true) :
    H.sub c "UnicodeError" = true :=
  hH.sub_trans h (hH.base (c := "UnicodeDecodeError") rfl)

theorem HierOk.tr_uerr {H : Hier} (hH : HierOk H) {c : String} (h : H.isTr c = true) :
    H.sub c "UnicodeError" = true :=
  hH.sub_trans h (hH.base (c := "UnicodeTranslateError") rfl)

theorem HierOk.enc_not_dec {H : Hier} (hH : HierOk H) {c : String} (h : H.isEnc c = true) :
    H.isDec c = false := by
  cases hd : H.isDec c
  · rfl
  · exact absurd ⟨h, hd⟩ (hH.2.2.2.1 c)

theorem HierOk.enc_not_tr {H : Hier} (hH : HierOk H) {c : String} (h : H.isEnc c = true) :
    H.isTr c = false := by
  cases hd : H.isTr c
  · rfl
  · exact absurd ⟨h, hd⟩ (hH.2.2.2.2.1 c)

theorem HierOk.dec_not_enc {H : Hier} (hH : HierOk H) {c : String} (h : H.isDec c = true) :
    H.isEnc c = false := by
  cases hd : H.isEnc c
  · rfl
  · exact absurd ⟨hd, h⟩ (hH.2.2.2.1 c)

theorem HierOk.dec_not_tr {H : Hier} (hH : HierOk H) {c : String} (h : H.isDec c = true) :
    H.isTr c = false := by
  cases hd : H.isTr c
  · rfl
  · exact absurd ⟨h, hd⟩ (hH.2.2.2.2.2 c)

theorem HierOk.tr_not_enc {H : Hier} (hH : HierOk H) {c : String} (h : H.isTr c = true) :
    H.isEnc c = false := by
  cases hd : H.isEnc c
  · rfl
  · exact absurd ⟨hd, h⟩ (hH.2.2.2.2.1 c)

theorem HierOk.tr_not_dec {H : Hier} (hH : HierOk H) {c : String} (h : H.isTr c = true) :
    H.isDec c = false := by
  cases hd : H.isDec c
  · rfl
  · exact absurd ⟨hd, h⟩ (hH.2.2.2.2.2 c)

/-! ## Clamping -/

theorem adjustStart_nonneg (s : Int) (n : Nat) : 0 ≤ adjustStart s n := by
  simp only [adjustStart]; split <;> (try split) <;> (try split) <;> omega

theorem adjustStart_le (s : Int) (n : Nat) : adjustStart s n ≤ n := by
  simp only [adjustStart]; split <;> (try split) <;> (try split) <;> omega

theorem adjustStart_lt (s : Int) (n : Nat) (h : 0 < n) : adjustStart s n < n := by
  simp only [adjustStart]; split <;> (try split) <;> (try split) <;> omega

theorem adjustEnd_nonneg (t : Int) (n : Nat) : 0 ≤ adjustEnd t n := by
  simp only [adjustEnd]; split <;> (try split) <;> (try split) <;> omega

theorem adjustEnd_le (t : Int) (n : Nat) : adjustEnd t n ≤ n := by
  simp only [adjustEnd]; split <;> (try split) <;> (try split) <;> omega

/-- The clipped `start`, as a `Nat`. -/
def stOf (e : ExcObj) (n : Nat) : Nat := (adjustStart e.start n).toNat
/-- The clipped `end`, as a `Nat`. -/
def enOf (e : ExcObj) (n : Nat) : Nat := (adjustEnd e.stop n).toNat

theorem stOf_le (e : ExcObj) (n : Nat) : stOf e n ≤ n := by
  have := adjustStart_le e.start n; have := adjustStart_nonneg e.start n
  unfold stOf; omega

theorem stOf_lt (e : ExcObj) (n : Nat) (h : 0 < n) : stOf e n < n := by
  have := adjustStart_lt e.start n h; have := adjustStart_nonneg e.start n
  unfold stOf; omega

theorem enOf_le (e : ExcObj) (n : Nat) : enOf e n ≤ n := by
  have := adjustEnd_le e.stop n; have := adjustEnd_nonneg e.stop n
  unfold enOf; omega

theorem adjustLen_toNat (e : ExcObj) (n : Nat) :
    (adjustLen (adjustStart e.start n) (adjustEnd e.stop n)).toNat = enOf e n - stOf e n := by
  have := adjustStart_nonneg e.start n; have := adjustEnd_nonneg e.stop n
  simp only [adjustLen, enOf, stOf]; split <;> omega

/-- `_PyUnicodeError_GetParams` once the `object` slot has the right type. -/
theorem getParams_of (e : ExcObj) (asBytes : Bool) (l : List Nat)
    (h : asAttr e.object "object" asBytes = .ok l) :
    getParams e asBytes = .ok ⟨l, l.length, stOf e l.length, enOf e l.length,
      enOf e l.length - stOf e l.length⟩ := by
  unfold getParams
  rw [h]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [adjustLen_toNat]
  rfl

theorem asAttr_str (s : Str) (name : String) : asAttr (.str s) name false = .ok s := rfl
theorem asAttr_bytes (b : Bytes) (name : String) : asAttr (.bytes b) name true = .ok b := rfl

theorem getParams_str (e : ExcObj) (s : Str) (h : e.object = .str s) :
    getParams e false = .ok ⟨s, s.length, stOf e s.length, enOf e s.length,
      enOf e s.length - stOf e s.length⟩ :=
  getParams_of e false s (by rw [h]; rfl)

theorem getParams_bytes (e : ExcObj) (b : Bytes) (h : e.object = .bytes b) :
    getParams e true = .ok ⟨b, b.length, stOf e b.length, enOf e b.length,
      enOf e b.length - stOf e b.length⟩ :=
  getParams_of e true b (by rw [h]; rfl)

theorem slice_length (l : List Nat) (a b : Nat) (hb : b ≤ l.length) :
    (slice l a b).length = b - a := by
  unfold slice; simp; omega

/-! ## The writers against `CodecHandlers.lean` -/

theorem writeUnicodeHex_eq (c : Nat) : writeUnicodeHex c = escapeEncodeChar c := by
  unfold writeUnicodeHex escapeEncodeChar hexAt hexDigits
  by_cases h1 : c ≥ 0x10000
  · have h2 : ¬ c ≤ 0xff := by omega
    have h3 : ¬ c ≤ 0xffff := by omega
    simp [h1, h2, h3, List.range, List.range.loop]
  · by_cases h4 : c ≥ 0x100
    · have h2 : ¬ c ≤ 0xff := by omega
      have h3 : c ≤ 0xffff := by omega
      simp [h1, h4, h2, h3, List.range, List.range.loop]
    · have h2 : c ≤ 0xff := by omega
      simp [h1, h4, h2, List.range, List.range.loop]

theorem byteHex_eq (b : Nat) : byteHex b = [92, 120] ++ hexDigits 2 b := by
  simp [byteHex, hexDigits, List.range, List.range.loop]

/-- The number of decimal digits, by recursion. -/
def decLen : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n => if n / 10 = 0 then 1 else decLen f (n / 10) + 1

theorem decChars_decFill : ∀ (f n : Nat) (acc : List Nat), n < f →
    decChars f n acc = decFill (decLen f n) n acc
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, n, acc, h => by
    simp only [decChars, decLen]
    by_cases hz : n / 10 = 0
    · simp [hz, decFill]
    · simp only [hz, if_false]
      rw [decChars_decFill f (n / 10) _ (by omega)]
      rfl

theorem decLen_fuel : ∀ (f g n : Nat), n < f → n < g → decLen f n = decLen g n
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, g + 1, n, hf, hg => by
    simp only [decLen]
    by_cases hz : n / 10 = 0
    · simp [hz]
    · simp only [hz, if_false]
      rw [decLen_fuel f g (n / 10) (by omega) (by omega)]

theorem decLen_rec (n : Nat) :
    decLen (n + 1) n = if n < 10 then 1 else decLen (n / 10 + 1) (n / 10) + 1 := by
  by_cases h : n < 10
  · have : n / 10 = 0 := by omega
    rw [if_pos h]
    show (if n / 10 = 0 then 1 else decLen n (n / 10) + 1) = 1
    simp [this]
  · have : n / 10 ≠ 0 := by omega
    rw [if_neg h]
    show (if n / 10 = 0 then 1 else decLen n (n / 10) + 1) = _
    rw [if_neg this, decLen_fuel n (n / 10 + 1) (n / 10) (by omega) (by omega)]

theorem nDecimalDigits_step (n : Nat) (h1 : 10 ≤ n) (h : n < 10000000) :
    nDecimalDigits n = nDecimalDigits (n / 10) + 1 := by
  unfold nDecimalDigits
  repeat' split
  all_goals omega

theorem nDecimalDigits_eq : ∀ n, n < 10000000 → nDecimalDigits n = decLen (n + 1) n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro h
    rw [decLen_rec]
    by_cases h1 : n < 10
    · rw [if_pos h1]; unfold nDecimalDigits; simp [h1]
    · rw [if_neg h1, nDecimalDigits_step n (by omega) h, ih (n / 10) (by omega) (by omega)]

/-- `&#DIGITS;` as the handler writes it is `xmlRef` of the codec-loop model, for every code
point. -/
theorem xmlBlock_eq (c : Nat) (h : c ≤ maxUnicode) : xmlBlock c = xmlRef c := by
  have hm : maxUnicode = 0x10FFFF := rfl
  unfold xmlBlock xmlRef
  rw [decChars_decFill (c + 1) c [] (by omega), nDecimalDigits_eq c (by omega)]

end PyLean.UnicodeObj.Codecs
