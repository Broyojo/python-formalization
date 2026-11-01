import PyLean.UnicodeObj.ObjectFromFormat
import PyLean.UnicodeObj.ObjectWriterProps

/-!
Properties of `PyUnicode_FromFormat`.
-/

namespace PyLean.UnicodeObj

open PyLean PyLean.Binary64

/-- The text of a result, to compare two results. -/
def okText (r : Py (Str × Kind)) : Option Str :=
  match r with
  | .ok x => some x.1
  | .error _ => none

/-- Whether a run ended in `e`. -/
def endsIn {α : Type} (r : Py α) (e : PyExc) : Bool :=
  match r with
  | .error x => x == e
  | .ok _ => false

theorem endsIn_eq {α : Type} {r : Py α} {e : PyExc} (h : endsIn r e = true) : r = .error e := by
  cases r with
  | ok _ => simp [endsIn] at h
  | error x =>
    simp only [endsIn, beq_iff_eq] at h
    rw [h]

/-- No format and no arguments of the right types reach a copy with a negative count: `memcpy` of
a huge size, then `writer->pos` moved backwards. Refuted: `"%.*U"` with -1. Every object conversion
goes this way, `%U`, `%V`, `%S`, `%R`, `%A`, `%T` and `%N`, whatever the width. -/
def FromFormatNoNegativeCopy : Prop :=
  ∀ (fmt : Bytes) (args : List VArg), pyUnicodeFromFormat fmt args ≠ .error negCopy

theorem fromFormatNoNegativeCopy_refuted : ¬FromFormatNoNegativeCopy := by
  intro h
  exact h [37, 46, 42, 85] [.int (-1), .obj (.str [97, 98, 99])]
    (endsIn_eq (by decide +kernel))

/-- A negative `*` precision is an omitted precision, as in C, for every conversion. Refuted by
`%s`, which writes nothing, so `%.*s` and `%s` differ, with no crash involved. -/
def FromFormatNegativeStarOmitted : Prop :=
  ∀ (c : Nat) (args : List VArg),
    okText (pyUnicodeFromFormat [37, 46, 42, c] (.int (-1) :: args)) =
      okText (pyUnicodeFromFormat [37, c] args)

theorem fromFormatNegativeStarOmitted_refuted : ¬FromFormatNegativeStarOmitted := by
  intro h
  have := h 115 [.cstr [97]]
  revert this
  decide +kernel

/-- The integer conversions do read a negative `*` precision as omitted, with any flags, width and
size. This is what the sentinel -2 at unicodeobject.c:2761 is safe for. -/
def FromFormatIntStarOmitted : Prop :=
  ∀ (w : UWriter) (p : List Nat) (s : FSpec) (c : Nat) (g : List Nat) (args : List VArg),
    (c = 100 ∨ c = 105 ∨ c = 111 ∨ c = 117 ∨ c = 120 ∨ c = 88) →
    fromFormatConv w p { s with precision := -2 } (c :: g) args =
      fromFormatConv w p { s with precision := -1 } (c :: g) args

theorem intLayout_star (b : Str) (width : Int) (z l : Bool) :
    intLayout b width (-2) z l = intLayout b width (-1) z l := by
  unfold intLayout
  have e : ∀ n : Nat, max (-2 : Int) n = max (-1 : Int) n := by intro n; omega
  simp only [e]

theorem fromFormatIntStarOmitted_proven : FromFormatIntStarOmitted := by
  intro w p s c g args hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [fromFormatConv, fromFormatSwitch, ffBad, ffChar, intLayout_star]

/-- `unicode_fromformat_write_str` does the bad copy exactly when the precision is below -1: for
every string, width and flag, and whether or not the string is empty. A precision of -1 or more is
safe. -/
def WriteStrNegativeCopy : Prop :=
  ∀ (w : UWriter) (s : Str) (width precision : Int) (lj : Bool),
    fmtWriteStr w s width precision lj = .error negCopy ↔ precision < -1

theorem writeStrNegativeCopy_proven : WriteStrNegativeCopy := by
  intro w s width precision lj
  unfold fmtWriteStr
  dsimp only
  constructor
  · intro h
    by_cases hp : precision < -1
    · exact hp
    · exfalso
      have hl : ¬((if precision ≠ -1 then min precision (s.length : Int) else (s.length : Int)) < 0) := by
        split <;> omega
      split at h
      · simp at h
      · simp at h
  · intro hp
    rw [if_neg (by omega)]
    have hl : (if precision ≠ -1 then min precision (s.length : Int) else (s.length : Int)) < 0 := by
      rw [if_pos (by omega)]
      omega
    rw [if_pos hl]

/-! ## The parser -/

theorem flags_precision (s : FSpec) (f : List Nat) :
    (ffParseFlags s f).1.precision = s.precision := by
  induction f generalizing s with
  | nil => rfl
  | cons c t ih =>
    simp only [ffParseFlags]
    split
    · exact ih _
    · split
      · exact ih _
      · split
        · exact ih _
        · rfl

theorem digitLoop_nonneg {msg : String} {v r : Int} {f g : List Nat} (hv : 0 ≤ v)
    (h : digitLoop msg v f = .ok (r, g)) : 0 ≤ r := by
  induction f generalizing v with
  | nil =>
    simp only [digitLoop, Except.ok.injEq, Prod.mk.injEq] at h
    omega
  | cons c t ih =>
    simp only [digitLoop] at h
    split at h
    · next hd =>
      split at h
      · simp at h
      · have hc : 48 ≤ c := by
          simp only [isDigitC, Bool.and_eq_true, decide_eq_true_eq] at hd
          exact hd.1
        exact ih (by omega) h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      omega

theorem width_precision {s s' : FSpec} {f f' : List Nat} {a a' : List VArg}
    (h : ffParseWidth s f a = .ok (s', f', a')) : s'.precision = s.precision := by
  unfold ffParseWidth at h
  split at h
  · simp only [bind, Except.bind] at h
    cases hp : popInt a with
    | error e => simp [hp] at h
    | ok r =>
      obtain ⟨v, b⟩ := r
      simp only [hp] at h
      split at h <;>
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1]
  · split at h
    · simp only [bind, Except.bind] at h
      split at h
      · simp at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1]
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1]
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]

theorem precision_parse {s s' : FSpec} {f f' : List Nat} {a a' : List VArg} (hs : s.precision = -1)
    (h : ffParsePrecision s f a = .ok (s', f', a')) : s'.precision = -2 ∨ -1 ≤ s'.precision := by
  unfold ffParsePrecision at h
  split at h
  · simp only [bind, Except.bind] at h
    cases hp : popInt a with
    | error e => simp [hp] at h
    | ok r =>
      obtain ⟨v, b⟩ := r
      simp only [hp, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      show (if v < 0 then (-2 : Int) else v) = -2 ∨ -1 ≤ (if v < 0 then (-2 : Int) else v)
      split
      · exact .inl rfl
      · exact .inr (by omega)
  · split at h
    · next c t _ hd =>
      simp only [bind, Except.bind] at h
      cases hp : digitLoop "precision too big" ((c : Int) - 48) t with
      | error e => simp [hp] at h
      | ok r =>
        obtain ⟨v, b⟩ := r
        simp only [hp, Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        have hc : 48 ≤ c := by
          simp only [isDigitC, Bool.and_eq_true, decide_eq_true_eq] at hd
          exact hd.1
        have := digitLoop_nonneg (by omega) hp
        exact .inr (by show -1 ≤ v; omega)
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1, hs]
      exact .inr (by omega)
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1, hs]
    exact .inr (by omega)
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1, hs]
    exact .inr (by omega)

/-- A precision below -1 comes out of the parser only as the sentinel of a negative `*`: digits and
a bare `.` cannot produce it. Together with `WriteStrNegativeCopy`, a negative `*` is the only way
to the bad copy. -/
def ParserPrecisionRange : Prop :=
  ∀ (f f' : List Nat) (a a' : List VArg) (s : FSpec), parseSpec f a = .ok (s, f', a') →
    s.precision = -2 ∨ -1 ≤ s.precision

theorem parserPrecisionRange_proven : ParserPrecisionRange := by
  intro f f' a a' s h
  simp only [parseSpec, bind, Except.bind] at h
  cases h1 : ffParseWidth (ffParseFlags {} f).1 (ffParseFlags {} f).2 a with
  | error e => simp [h1] at h
  | ok r1 =>
    obtain ⟨s1, f1, a1⟩ := r1
    simp only [h1] at h
    cases h2 : ffParsePrecision s1 f1 a1 with
    | error e => simp [h2] at h
    | ok r2 =>
      obtain ⟨s2, f2, a2⟩ := r2
      simp only [h2, Except.ok.injEq, Prod.mk.injEq, Except.pure, pure] at h
      have e1 : s1.precision = -1 := by
        rw [width_precision h1, flags_precision]
      have := precision_parse e1 h2
      rw [← h.1]
      exact this

/-! ## The canonical kind -/

theorem hexLower_lt {d : Nat} (h : d < 16) : hexLower d < 128 := by
  simp only [hexLower]
  split <;> omega

theorem natDigits_chars (b : Nat) (hb : 0 < b ∧ b ≤ 16) (fuel n : Nat) (acc : Str)
    (h : ∀ c ∈ acc, c < 128) : ∀ c ∈ natDigits b fuel n acc, c < 128 := by
  induction fuel generalizing n acc with
  | zero => simpa [natDigits] using h
  | succ fuel ih =>
    have hd : hexLower (n % b) < 128 := hexLower_lt (by
      have := Nat.mod_lt n hb.1
      omega)
    have hc : ∀ c ∈ hexLower (n % b) :: acc, c < 128 := by
      intro c hm
      rcases List.mem_cons.1 hm with rfl | hm
      · exact hd
      · exact h c hm
    simp only [natDigits]
    split
    · exact hc
    · exact ih _ _ hc

theorem digitsOf_chars {b : Nat} (hb : 0 < b ∧ b ≤ 16) (n : Nat) :
    ∀ c ∈ digitsOf b n, c < 128 :=
  natDigits_chars b hb _ _ [] (by simp)

theorem sprintInt_ascii (c sz : Nat) (v : Int) : ∀ x ∈ sprintInt c sz v, x < 128 := by
  intro x hx
  unfold sprintInt at hx
  dsimp only at hx
  split at hx
  · exact digitsOf_chars (by omega) _ x hx
  · split at hx
    · exact digitsOf_chars (by omega) _ x hx
    · split at hx
      · exact digitsOf_chars (by omega) _ x hx
      · split at hx
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
          have := digitsOf_chars (b := 16) (by omega) _ y hy
          split <;> omega
        · rcases List.mem_append.1 hx with hx | hx
          · split at hx
            · simp at hx
              omega
            · simp at hx
          · exact digitsOf_chars (by omega) _ x hx

theorem replicate_ascii {n c x : Nat} (hc : c < 128) (h : x ∈ List.replicate n c) : x < 128 := by
  rw [List.eq_of_mem_replicate h]
  exact hc

theorem ite_ascii (q : Prop) [Decidable q] (x : List Nat) (hx : ∀ c ∈ x, c < 128) :
    ∀ c ∈ (if q then x else []), c < 128 := by
  intro c hc
  by_cases h : q
  · rw [if_pos h] at hc
    exact hx c hc
  · rw [if_neg h] at hc
    simp at hc

theorem intLayout_ascii {b : Str} (hb : ∀ c ∈ b, c < 128) (width precision : Int) (z l : Bool) :
    ∀ c ∈ intLayout b width precision z l, c < 128 := by
  intro c hc
  unfold intLayout at hc
  dsimp only at hc
  have hd : ∀ x ∈ (if (b.head? == some 45) = true then b.tail else b), x < 128 := by
    intro x hx
    split at hx
    · exact hb x (List.mem_of_mem_tail hx)
    · exact hb x hx
  have hr : ∀ (n d : Nat), d < 128 → ∀ x ∈ List.replicate n d, x < 128 :=
    fun _ _ hd _ hx => replicate_ascii hd hx
  rcases List.mem_append.1 hc with hc | hc
  · rcases List.mem_append.1 hc with hc | hc
    · rcases List.mem_append.1 hc with hc | hc
      · rcases List.mem_append.1 hc with hc | hc
        · exact ite_ascii _ _ (hr _ 32 (by omega)) c hc
        · exact ite_ascii _ [45] (by simp) c hc
      · exact hr _ 48 (by omega) c hc
    · exact hd c hc
  · exact ite_ascii _ _ (hr _ 32 (by omega)) c hc

theorem pointerText_ascii (v : Nat) : ∀ c ∈ pointerText v, c < 128 := by
  have h0 : ∀ c ∈ lit "(nil)", c < 128 := by decide
  have h1 : ∀ c ∈ lit "0x", c < 128 := by decide
  have h2 : ∀ c ∈ (if v = 0 then lit "(nil)" else lit "0x" ++ digitsOf 16 v), c < 128 := by
    intro c hc
    split at hc
    · exact h0 c hc
    · rcases List.mem_append.1 hc with hc | hc
      · exact h1 c hc
      · exact digitsOf_chars (by omega) _ c hc
  intro c hc
  unfold pointerText at hc
  dsimp only at hc
  generalize (if v = 0 then lit "(nil)" else lit "0x" ++ digitsOf 16 v) = n at hc h2
  split at hc
  · exact h2 c hc
  · rcases List.mem_append.1 hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem need_ne (m : Nat) : capNeed m ≠ 0 := by
  have := need_value m
  omega

theorem need_value_self {c : Nat} (hc : CapValue c) (h0 : c ≠ 0) : capNeed c = c := by
  rcases hc with h | h | h | h | h
  · exact absurd h h0
  all_goals (rw [h]; decide)

theorem fmtWriteStr_inv {w w' : UWriter} (hI : WInv w) {str : Str} {width precision : Int} {lj : Bool}
    (h : fmtWriteStr w str width precision lj = .ok w') : WInv w' := by
  have hc := hI.capValue
  unfold fmtWriteStr at h
  dsimp only at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    rw [writeText_eq hc]
    exact hI.expect _
  · generalize hL : (if precision ≠ -1 then min precision (str.length : Int) else (str.length : Int))
      = length at h
    have hle : length ≤ str.length := by
      subst hL
      split <;> omega
    split at h
    · simp at h
    · next hn =>
      simp only [Except.ok.injEq] at h
      subst h
      have hP : maxCharOf (str.take length.toNat) ≤ maxCharOf str :=
        foldl_max_le _ 0 _ (Nat.zero_le _)
          (fun c hm => foldl_max_mem str 0 c (List.mem_of_mem_take hm))
      generalize hPd : str.take length.toNat = part at *
      generalize hSd : List.replicate (max (width - length) 0).toNat 32 = spaces at *
      have hS : ∀ c ∈ spaces, c < 128 := by
        intro c hm
        rw [← hSd] at hm
        exact replicate_ascii (by omega) hm
      have hneed : capNeed (maxCharOf (if lj = true then part ++ spaces else spaces ++ part)) =
          capNeed (maxCharOf part) := by
        have e := need_ascii hS
        have := need_value (maxCharOf part)
        split
        · rw [maxCharOf_append, capNeed_max, e]
          omega
        · rw [maxCharOf_append, capNeed_max, e]
          omega
      generalize hX : (if lj = true then part ++ spaces else spaces ++ part) = X at hneed ⊢
      split
      · next ha =>
        have h0 : length = 0 := by omega
        have hw : width ≤ 0 := by omega
        have hp0 : part = [] := by
          rw [← hPd, h0]
          simp
        have hs0 : spaces = [] := by
          rw [← hSd]
          have : (max (width - length) 0).toNat = 0 := by omega
          rw [this]
          rfl
        have : X = [] := by
          rw [← hX]
          simp [hp0, hs0]
        rw [this]
        cases w
        simpa using hI
      · left
        show prepareCap w.cap _ = capNeed (maxCharOf (w.text ++ _))
        rw [prepare_max hc, maxCharOf_append, capNeed_max, hneed]
        split
        · rcases hI with hi | ⟨hi, ht⟩
          · rw [hi]
          · have := need_value (maxCharOf part)
            rw [hi, ht, need_empty]
            omega
        · next hnc =>
          have hle2 : capOf (kindOfMax (maxCharOf str)) ≤ w.cap := by
            simpa [canonicalKind] using hnc
          have hpos : capOf (kindOfMax (maxCharOf str)) ≠ 0 := by
            rw [← need_eq]
            exact need_ne _
          have h0 : w.cap ≠ 0 := by omega
          have hi : w.cap = capNeed (maxCharOf w.text) := by
            rcases hI with hi | ⟨hi, _⟩
            · exact hi
            · exact absurd hi h0
          have hm := need_mono hP
          rw [need_eq (maxCharOf str)] at hm
          rw [need_value_self hc h0, ← hi]
          omega

theorem decode_ok_inv {w : UWriter} (hI : WInv w) {b : Bytes} {h : ErrHandler} {c : Bool} {n : Nat}
    (hr : (decodeWriter w b h c).2 = .ok n) : WInv (decodeWriter w b h c).1 := by
  cases hd : utf8DecodeLoop b h c (b.length + 1) 0 b [] with
  | error e =>
    rw [(decodeWriter_err hd w).2] at hr
    simp at hr
  | ok r =>
    obtain ⟨s, m⟩ := r
    exact decode_inv hI hd

theorem bind_write_inv {α : Type} {w w' : UWriter} (hI : WInv w) {x : Py α} {f : α → Str}
    {width : Int} {lj : Bool}
    (h : (do let v ← x; fmtWriteStr w (f v) width (-1) lj : Py UWriter) = .ok w') : WInv w' := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok v => exact fmtWriteStr_inv hI h

theorem fmtWriteUtf8_inv {w w' : UWriter} (hI : WInv w) {str : Bytes} {width precision : Int}
    {lj : Bool} (h : fmtWriteUtf8 w str width precision lj = .ok w') : WInv w' := by
  unfold fmtWriteUtf8 at h
  dsimp only at h
  generalize (if precision = -1 then ((cstrOf str).length, false)
    else (boundedLen (cstrOf str) precision,
      decide ((boundedLen (cstrOf str) precision : Int) = precision))) = pr at h
  obtain ⟨length, stateful⟩ := pr
  dsimp only at h
  split at h
  · cases hd : decodeWriter w ((cstrOf str).take length) .replace stateful with
    | mk w1 r =>
      rw [hd] at h
      cases r with
      | error e => simp [bind, Except.bind] at h
      | ok n =>
        simp only [bind, Except.bind, Except.ok.injEq] at h
        subst h
        have := decode_ok_inv hI (b := (cstrOf str).take length) (h := .replace) (c := stateful)
          (n := n) (by rw [hd])
        rwa [hd] at this
  · split at h <;> exact bind_write_inv (f := id) hI h

theorem writeWide_inv {w : UWriter} (hI : WInv w) (s : Str) (size : Int) :
    WInv (writeWide w s size).1 :=
  applyOp_inv (op := .wide s size) hI trivial (by simp [WOp.isDecode])

theorem fmtWriteWcstr_inv {w w' : UWriter} (hI : WInv w) {str : Str} {width precision : Int}
    {lj : Bool} (h : fmtWriteWcstr w str width precision lj = .ok w') : WInv w' := by
  unfold fmtWriteWcstr at h
  dsimp only at h
  generalize (if precision = -1 then (str.takeWhile (· != 0)).length
    else boundedLen (str.takeWhile (· != 0)) precision) = length at h
  generalize List.take length (str.takeWhile (· != 0)) = part at h
  split at h
  · cases hd : writeWide w part length with
    | mk w1 r =>
      rw [hd] at h
      cases r with
      | error e => simp [bind, Except.bind] at h
      | ok n =>
        simp only [bind, Except.bind, Except.ok.injEq] at h
        subst h
        have := writeWide_inv hI part length
        rwa [hd] at this
  · split at h
    · exact fmtWriteStr_inv hI h
    · exact bind_write_inv (f := fun _ => part) hI h

theorem do_pair {x : Py UWriter} {t a : List VArg} {w' : UWriter}
    (h : (do return (← x, t) : Py (UWriter × List VArg)) = .ok (w', a)) : x = .ok w' := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok v =>
    change Except.ok (v, t) = _ at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [h.1]

theorem bind_pair_inv {w w' : UWriter} (hI : WInv w) {x : Py Str} {t a : List VArg} {wd pr : Int}
    {lj : Bool}
    (h : (do let text ← x; return (← fmtWriteStr w text wd pr lj, t) :
      Py (UWriter × List VArg)) = .ok (w', a)) : WInv w' := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok v => exact fmtWriteStr_inv hI (do_pair h)

theorem conv_inv {w w' : UWriter} (hI : WInv w) {p : List Nat} {s : FSpec} {f : List Nat}
    {args a : List VArg} (h : fromFormatConv w p s f args = .ok (w', a)) : WInv w' := by
  have hc := hI.capValue
  unfold fromFormatConv at h
  split at h
  · simp at h
  unfold fromFormatSwitch at h
  repeat' split at h
  all_goals first
    | (simp [vaError] at h; done)
    | exact fmtWriteStr_inv hI (do_pair h)
    | exact fmtWriteUtf8_inv hI (do_pair h)
    | exact fmtWriteWcstr_inv hI (do_pair h)
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, _⟩ := h
       first
       | (rw [writeAscii_eq hc (intLayout_ascii (sprintInt_ascii _ _ _) _ _ _ _)]
          exact hI.expect _)
       | (rw [writeAscii_eq hc (pointerText_ascii _)]
          exact hI.expect _)
       | (rw [write_char_eq hc]
          exact hI.expect _))
    | exact bind_pair_inv hI h
    | (dsimp only at h
       split at h
       · simp at h
       · simp only [Except.ok.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, _⟩ := h
         rw [write_char_eq hc]
         exact hI.expect _)

/-! ## What is left of the format -/

theorem flags_suffix (s : FSpec) (f : List Nat) : (ffParseFlags s f).2 <:+ f := by
  induction f generalizing s with
  | nil => exact List.suffix_refl _
  | cons c t ih =>
    simp only [ffParseFlags]
    split
    · exact (ih _).trans (List.suffix_cons _ _)
    · split
      · exact (ih _).trans (List.suffix_cons _ _)
      · split
        · exact (ih _).trans (List.suffix_cons _ _)
        · exact List.suffix_refl _

theorem digit_suffix {msg : String} {v r : Int} {f g : List Nat}
    (h : digitLoop msg v f = .ok (r, g)) : g <:+ f := by
  induction f generalizing v with
  | nil =>
    simp only [digitLoop, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact List.suffix_refl _
  | cons c t ih =>
    simp only [digitLoop] at h
    split at h
    · split at h
      · simp at h
      · exact (ih h).trans (List.suffix_cons _ _)
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact List.suffix_refl _

theorem width_suffix {s s' : FSpec} {f f' : List Nat} {a a' : List VArg}
    (h : ffParseWidth s f a = .ok (s', f', a')) : f' <:+ f := by
  unfold ffParseWidth at h
  split at h
  · simp only [bind, Except.bind] at h
    split at h
    · simp at h
    · split at h <;>
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2.1]
        exact List.suffix_cons _ _
  · split at h
    · simp only [bind, Except.bind] at h
      split at h
      · simp at h
      · next hd =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2.1]
        exact (digit_suffix hd).trans (List.suffix_cons _ _)
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2.1]
      exact List.suffix_refl _
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2.1]
    exact List.suffix_refl _

theorem precision_suffix {s s' : FSpec} {f f' : List Nat} {a a' : List VArg}
    (h : ffParsePrecision s f a = .ok (s', f', a')) : f' <:+ f := by
  unfold ffParsePrecision at h
  split at h
  · simp only [bind, Except.bind] at h
    split at h
    · simp at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2.1]
      exact (List.suffix_cons _ _).trans (List.suffix_cons _ _)
  · split at h
    · simp only [bind, Except.bind] at h
      split at h
      · simp at h
      · next hd =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2.1]
        exact (digit_suffix hd).trans ((List.suffix_cons _ _).trans (List.suffix_cons _ _))
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2.1]
      exact List.suffix_cons _ _
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2.1]
    exact List.nil_suffix
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2.1]
    exact List.suffix_refl _

theorem sizemod_suffix (f : List Nat) : (parseSizemod f).2 <:+ f := by
  unfold parseSizemod
  split
  · exact ⟨[108, 108], rfl⟩
  · exact ⟨[108], rfl⟩
  · exact ⟨[122], rfl⟩
  · exact ⟨[116], rfl⟩
  · exact ⟨[106], rfl⟩
  · exact List.suffix_refl _

theorem parse_suffix {f g : List Nat} {a b : List VArg} {s : FSpec}
    (h : parseSpec f a = .ok (s, g, b)) : g <:+ f := by
  simp only [parseSpec, bind, Except.bind] at h
  split at h
  · simp at h
  · next h1 =>
    split at h
    · simp at h
    · next h2 =>
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2.1]
      exact (sizemod_suffix _).trans
        ((precision_suffix h2).trans ((width_suffix h1).trans (flags_suffix _ _)))

theorem arg_inv {w w' : UWriter} (hI : WInv w) {c : Nat} {t f' : List Nat} {a a' : List VArg}
    (h : fromFormatArg w (c :: t) a = .ok (w', f', a')) : WInv w' ∧ f' <:+ t := by
  have hc := hI.capValue
  simp only [fromFormatArg] at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, _⟩ := h
    rw [write_char_eq hc]
    exact ⟨hI.expect _, List.tail_suffix _⟩
  · simp only [bind, Except.bind] at h
    split at h
    · simp at h
    · next hp =>
      split at h
      · simp at h
      · next hv =>
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, _⟩ := h
        exact ⟨conv_inv hI hv, (List.tail_suffix _).trans (parse_suffix hp)⟩

theorem loop_inv : ∀ (fuel : Nat) (f : List Nat) (args : List VArg) (w : UWriter),
    WInv w → (∀ c ∈ f, c < 128) → (fromFormatLoop fuel f args w).2 = .ok () →
    WInv (fromFormatLoop fuel f args w).1 := by
  intro fuel
  induction fuel with
  | zero => intro f args w _ _ h; simp [fromFormatLoop] at h
  | succ fuel ih =>
    intro f args w hI hf h
    cases f with
    | nil => exact hI
    | cons c t =>
      simp only [fromFormatLoop] at h ⊢
      split at h
      · next hc =>
        rw [if_pos hc]
        split at h
        · simp at h
        · next w' f' a' hr =>
          obtain ⟨h1, h2⟩ := arg_inv hI hr
          exact ih _ _ _ h1 (fun x hx => hf x (List.mem_cons_of_mem _ (h2.subset hx))) h
      · next hc =>
        rw [if_neg hc]
        have hs : ∀ x ∈ (c :: t).takeWhile (· != 37), x < 128 := fun x hx =>
          hf x ((List.takeWhile_sublist _).subset hx)
        apply ih _ _ _ _ _ h
        · rw [writeAscii_eq hI.capValue hs]
          exact hI.expect _
        · exact fun x hx => hf x (List.mem_of_mem_drop hx)

/-- Every str `PyUnicode_FromFormat` returns has the canonical kind: for every format and all
arguments, through every conversion, whatever the precision cut off and whatever padding was added.
A precision can make the text narrower than the string it came from, and this says the kind follows
the text. -/
def FromFormatCanonical : Prop :=
  ∀ (fmt : Bytes) (args : List VArg) (t : Str) (k : Kind),
    pyUnicodeFromFormat fmt args = .ok (t, k) → k = canonicalKind t

theorem unicodeFromFormat_inv {w0 w : UWriter} (hI : WInv w0) {fmt : Bytes} {args : List VArg}
    (h : unicodeFromFormat w0 fmt args = (w, .ok ())) : WInv w := by
  unfold unicodeFromFormat at h
  dsimp only at h
  split at h
  · simp at h
  · next hf =>
    have hall : ∀ c ∈ cstrOf fmt, c < 128 := by
      intro c hc
      have := List.find?_eq_none.1 hf c hc
      simp only [decide_eq_true_eq] at this
      omega
    have := loop_inv _ _ args w0 hI hall (by rw [h])
    rwa [h] at this

theorem fromFormatCanonical_proven : FromFormatCanonical := by
  intro fmt args t k h
  unfold pyUnicodeFromFormat at h
  cases hu : unicodeFromFormat {} fmt args with
  | mk w r =>
    rw [hu] at h
    cases r with
    | error e => simp at h
    | ok u =>
      have hI := unicodeFromFormat_inv (w0 := {}) (.inr ⟨rfl, rfl⟩) hu
      simp only [hI.finish, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1, ← h.2]

/-- `%V` is `%U` when it has an object, and `%s` or `%ls` when it does not, with any flags, width
and precision. The string argument is taken from the `...` either way. -/
def FromFormatVTwins : Prop :=
  ∀ (w : UWriter) (p p' : List Nat) (s : FSpec) (g : List Nat) (t : List VArg),
    (s.sizemod = 0 ∨ s.sizemod = F_LONG →
      ∀ (x : Str) (alt : VArg), fromFormatConv w p s (86 :: g) (.obj (.str x) :: alt :: t) =
        fromFormatConv w p' { s with sizemod := 0 } (85 :: g) (.obj (.str x) :: t)) ∧
    (s.sizemod = 0 → ∀ b : Bytes, fromFormatConv w p s (86 :: g) (.nullObj :: .cstr b :: t) =
        fromFormatConv w p' s (115 :: g) (.cstr b :: t)) ∧
    (s.sizemod = F_LONG → ∀ x : Str, fromFormatConv w p s (86 :: g) (.nullObj :: .wstr x :: t) =
        fromFormatConv w p' s (115 :: g) (.wstr x :: t))

theorem fromFormatVTwins_proven : FromFormatVTwins := by
  intro w p p' s g t
  refine ⟨?_, ?_, ?_⟩
  · intro hs x alt
    rcases hs with hs | hs <;> simp [fromFormatConv, fromFormatSwitch, ffBad, ffChar, hs, F_LONG]
  · intro hs b
    simp [fromFormatConv, fromFormatSwitch, ffBad, ffChar, hs]
  · intro hs x
    simp [fromFormatConv, fromFormatSwitch, ffBad, ffChar, hs, F_LONG]

/-- `PyUnicodeWriter_Format`, like `WriteUTF8`, is documented to leave the writer unchanged on
error. Refuted on 3.14: `"%c%c"` writes a wide character and then fails on the second, and what is
left is a writer too wide for its text. gh-158439 names this function too. -/
def WriterFormatUnobservable : Prop :=
  ∀ (w : UWriter) (fmt : Bytes) (args : List VArg) (e : PyExc), WInv w →
    (writerFormat w fmt args).2 = .error e → (writerFormat w fmt args).1.finish = w.finish

theorem writerFormatUnobservable_refuted : ¬WriterFormatUnobservable := by
  intro h
  have := h { text := [97], cap := 127 } [37, 99, 37, 99] [.int 0x20ac, .int 0x110000]
    (.overflowError "character argument not in range(0x110000)") (.inl (by decide))
    (by decide +kernel)
  revert this
  decide +kernel

end PyLean.UnicodeObj
