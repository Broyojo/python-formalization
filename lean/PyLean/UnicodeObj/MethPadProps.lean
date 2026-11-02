import PyLean.UnicodeObj.MethPad

/-!
Properties of `str.center`, `str.ljust`, `str.rjust`, `str.zfill` and of `PyUnicode_New`'s
size check.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- The largest size `PyUnicode_New` accepts for `maxchar`. -/
def newLimit (maxchar : Nat) : Int := (ssizeMax - (newSizes maxchar).2) / (newSizes maxchar).1 - 1

/-- For every positive size and valid `maxchar`, `PyUnicode_New`'s check passes exactly when
the allocation size `struct_size + (size + 1) * char_size` fits in `Py_ssize_t` (so it neither
overflows nor refuses a representable size), `char_size` is the width of the kind it picks, and
the only refusal is `MemoryError`. Type invariant: `maxchar` is a code point. -/
def NewSizeExact : Prop :=
  ∀ (size : Int) (maxchar : Nat), 0 < size → maxchar ≤ maxUnicode →
    (pyUnicodeNew size maxchar = .ok () ↔
      (newSizes maxchar).2 + (size + 1) * (newSizes maxchar).1 ≤ ssizeMax) ∧
    (newSizes maxchar).1 = (kindOfMax maxchar).width ∧
    (pyUnicodeNew size maxchar = .ok () ∨ pyUnicodeNew size maxchar = .error memoryError)

theorem newSizeExact_proven : NewSizeExact := by
  intro size m hs hm
  unfold maxUnicode at hm
  unfold pyUnicodeNew newSizes kindOfMax asciiStructSize compactStructSize ssizeMax
  have h0 : ¬ size = 0 := by omega
  simp only [h0, if_false]
  by_cases h1 : m < 128
  · simp only [h1, if_true, Kind.width]
    refine ⟨?_, rfl, ?_⟩
    · split
      · next h => exact absurd h.2 (by unfold maxUnicode; omega)
      · rw [if_neg (by omega)]; split <;> simp <;> omega
    · split
      · next h => exact absurd h.2 (by unfold maxUnicode; omega)
      · rw [if_neg (by omega)]; split <;> simp
  · by_cases h2 : m < 256
    · simp only [h1, h2, if_true, if_false, Kind.width]
      refine ⟨?_, rfl, ?_⟩
      · split
        · next h => exact absurd h.2 (by unfold maxUnicode; omega)
        · rw [if_neg (by omega)]; split <;> simp <;> omega
      · split
        · next h => exact absurd h.2 (by unfold maxUnicode; omega)
        · rw [if_neg (by omega)]; split <;> simp
    · by_cases h3 : m < 65536
      · simp only [h1, h2, h3, if_true, if_false, Kind.width]
        refine ⟨?_, rfl, ?_⟩
        · split
          · next h => exact absurd h.2 (by unfold maxUnicode; omega)
          · rw [if_neg (by omega)]; split <;> simp <;> omega
        · split
          · next h => exact absurd h.2 (by unfold maxUnicode; omega)
          · rw [if_neg (by omega)]; split <;> simp
      · simp only [h1, h2, h3, if_false, Kind.width]
        refine ⟨?_, rfl, ?_⟩
        · split
          · next h => exact absurd h.2 (by unfold maxUnicode; omega)
          · rw [if_neg (by omega)]; split <;> simp <;> omega
        · split
          · next h => exact absurd h.2 (by unfold maxUnicode; omega)
          · rw [if_neg (by omega)]; split <;> simp

theorem pyUnicodeNew_eq (size : Int) (m : Nat) (hs : 0 < size) (hm : m ≤ maxUnicode) :
    pyUnicodeNew size m = if size > newLimit m then .error memoryError else .ok () := by
  unfold pyUnicodeNew newLimit
  have h0 : ¬ size = 0 := by omega
  rw [if_neg h0]
  simp only
  rw [if_neg (by unfold maxUnicode at hm ⊢; omega), if_neg (by omega)]

theorem maxCharValue_le (s : Str) : maxCharValue s ≤ maxUnicode := by
  unfold maxCharValue maxUnicode
  cases canonicalKind s <;> simp [Kind.maxChar]

/-- `pad` with something to add and a size that fits. -/
theorem pad_eq (s : Str) (left right : Int) (fill : Nat) (hl : 0 ≤ left) (hr : 0 ≤ right)
    (hpos : 0 < left ∨ 0 < right) (hsum : left + s.length + right ≤ ssizeMax)
    (hf : fill ≤ maxUnicode) :
    pad s left right fill =
      if left + s.length + right > newLimit (max (maxCharValue s) fill) then .error memoryError
      else .ok (List.replicate left.toNat fill ++ s ++ List.replicate right.toNat fill) := by
  have hm : max (maxCharValue s) fill ≤ maxUnicode := by
    have := maxCharValue_le s; omega
  unfold pad
  simp only [if_neg (show ¬ left < 0 by omega), if_neg (show ¬ right < 0 by omega),
    if_neg (show ¬ (left = 0 ∧ right = 0) by omega),
    if_neg (show ¬ (left > ssizeMax - s.length ∨ right > ssizeMax - (left + s.length)) by omega)]
  rw [pyUnicodeNew_eq _ _ (by omega) hm]
  split <;> rfl

/-- `str.zfill`'s documented result: "Return a copy of the string left filled with ASCII '0'
digits to make a string of length width. A leading sign prefix ('+'/'-') is handled by
inserting the padding after the sign character rather than before." `k` zeros are added. -/
def zfillSpec (s : Str) (k : Nat) : Str :=
  match s with
  | c :: r => if c = 43 ∨ c = 45 then c :: (List.replicate k 48 ++ r) else List.replicate k 48 ++ s
  | [] => List.replicate k 48

/-- The left padding of `str.center`: half the margin, plus one when the margin and the width
are both odd. -/
def centerLeft (n w : Int) : Int := (w - n) / 2 + (if w % 2 = 1 ∧ (w - n) % 2 = 1 then 1 else 0)

/-- For every string, every `Py_ssize_t` width and every fill character: `ljust`, `rjust`,
`center` and `zfill` return the string itself when `width <= len(s)`, and otherwise the
documented string of exactly `width` characters (fill on the right, on the left, split with
the odd character on the left exactly when margin and width are odd, zeros after a leading
sign); the only error is `PyUnicode_New`'s `MemoryError` for a width beyond the representable
size, `pad`'s `OverflowError` being unreachable. Type invariants: `Str.Valid s`,
`width <= PY_SSIZE_T_MAX` (the clinic converter), `fill` a code point. -/
def PadDoc : Prop :=
  ∀ (s : Str) (w : Int) (f : Nat), Str.Valid s → w ≤ ssizeMax → f ≤ maxUnicode →
    unicodeLjustImpl s w f = (if w ≤ s.length then .ok s
      else if w > newLimit (max (maxCharValue s) f) then .error memoryError
      else .ok (s ++ List.replicate (w - s.length).toNat f)) ∧
    unicodeRjustImpl s w f = (if w ≤ s.length then .ok s
      else if w > newLimit (max (maxCharValue s) f) then .error memoryError
      else .ok (List.replicate (w - s.length).toNat f ++ s)) ∧
    unicodeCenterImpl s w f = (if w ≤ s.length then .ok s
      else if w > newLimit (max (maxCharValue s) f) then .error memoryError
      else .ok (List.replicate (centerLeft s.length w).toNat f ++ s ++
        List.replicate (w - s.length - centerLeft s.length w).toNat f)) ∧
    unicodeZfillImpl s w = (if w ≤ s.length then .ok s
      else if w > newLimit (max (maxCharValue s) 48) then .error memoryError
      else .ok (zfillSpec s (w - s.length).toNat))

theorem land_one_bit (a b : Nat) :
    (a &&& (b &&& 1) : Nat) = if b % 2 = 1 ∧ a % 2 = 1 then 1 else 0 := by
  rw [Nat.and_one_is_mod]
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases hb with hb | hb
  · rw [hb, Nat.and_zero]; simp
  · rw [hb, Nat.and_one_is_mod]
    have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
    rcases ha with ha | ha <;> simp [ha]

theorem rep_cons (k : Nat) (r : Str) :
    List.replicate k 48 ++ 48 :: r = 48 :: (List.replicate k 48 ++ r) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.cons_append, ih]; rfl

theorem zfill_set (k : Nat) (c : Nat) (r : Str) :
    ((List.replicate (k + 1) 48 ++ c :: r).set 0 c).set (k + 1) 48 =
      c :: (List.replicate (k + 1) 48 ++ r) := by
  rw [List.replicate_succ, List.cons_append, List.set_cons_zero, List.set_cons_succ,
    List.set_append_right _ _ (by simp), List.length_replicate, Nat.sub_self, List.set_cons_zero,
    rep_cons]
  rfl

theorem getD_rep (k : Nat) (l : Str) : (List.replicate k 48 ++ l).getD k 0 = l.getD 0 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.cons_append, List.getD_cons_succ, ih]

/-- The sign step of `unicode_zfill_impl` (:13353-13358) on `pad`'s result. -/
theorem zfill_core (k : Nat) (s : Str) :
    (let u := List.replicate (k + 1) 48 ++ s
     let chr := (u ++ [0]).getD (k + 1) 0
     if chr = 43 ∨ chr = 45 then (u.set 0 chr).set (k + 1) 48 else u) = zfillSpec s (k + 1) := by
  simp only
  rw [List.append_assoc, getD_rep]
  cases s with
  | nil => simp [zfillSpec]
  | cons c r =>
    simp only [List.cons_append, List.getD_cons_zero, zfillSpec]
    split
    · rw [zfill_set]
    · rfl

theorem padDoc_proven : PadDoc := by
  intro s w f hs hw hf
  have h48 : (48 : Nat) ≤ maxUnicode := by unfold maxUnicode; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold unicodeLjustImpl
    by_cases hle : w ≤ s.length
    · rw [if_pos (by omega), if_pos hle]
    · rw [if_neg (by omega), if_neg hle, pad_eq s 0 _ f (Int.le_refl _) (by omega) (by omega)
        (by omega) hf]
      simp only [Int.zero_add, Int.toNat_zero, List.replicate_zero, List.nil_append,
        Int.add_sub_cancel, show (s.length : Int) + (w - s.length) = w by omega]
  · unfold unicodeRjustImpl
    by_cases hle : w ≤ s.length
    · rw [if_pos (by omega), if_pos hle]
    · rw [if_neg (by omega), if_neg hle, pad_eq s _ 0 f (by omega) (Int.le_refl _) (by omega)
        (by omega) hf]
      simp only [Int.add_zero, Int.toNat_zero, List.replicate_zero, List.append_nil,
        show w - s.length + s.length = w by omega]
  · unfold unicodeCenterImpl
    by_cases hle : w ≤ s.length
    · rw [if_pos (by omega), if_pos hle]
    · rw [if_neg (by omega), if_neg hle]
      have hbit := land_one_bit (w - s.length).toNat w.toNat
      have hl : (w - s.length) / 2 + (((w - s.length).toNat &&& (w.toNat &&& 1) : Nat) : Int) =
          centerLeft s.length w := by
        rw [hbit, centerLeft]
        congr 1
        by_cases hc : w % 2 = 1 ∧ (w - s.length) % 2 = 1
        · rw [if_pos hc, if_pos (by omega)]; rfl
        · rw [if_neg hc, if_neg (by omega)]; rfl
      simp only [hl]
      have hcl : 0 ≤ centerLeft s.length w ∧ centerLeft s.length w ≤ w - s.length := by
        unfold centerLeft; split <;> omega
      rw [pad_eq s _ _ f hcl.1 (by omega) (by unfold centerLeft at hcl ⊢; split <;> omega)
        (by omega) hf]
      simp only [show centerLeft s.length w + s.length + (w - s.length - centerLeft s.length w) = w
        by omega]
  · unfold unicodeZfillImpl
    by_cases hle : w ≤ s.length
    · rw [if_pos (by omega), if_pos hle]; rfl
    · rw [if_neg (by omega), if_neg hle]
      obtain ⟨k, hk⟩ : ∃ k : Nat, w - s.length = ((k + 1 : Nat) : Int) :=
        ⟨(w - s.length).toNat - 1, by omega⟩
      simp only []
      rw [pad_eq s _ 0 48 (by omega) (Int.le_refl _) (by omega) (by omega) h48]
      simp only [Int.add_zero, Int.toNat_zero, List.replicate_zero, List.append_nil,
        show w - s.length + s.length = w by omega]
      by_cases hlim : w > newLimit (max (maxCharValue s) 48)
      · rw [if_pos hlim, if_pos hlim]; rfl
      · rw [if_neg hlim, if_neg hlim, hk, Int.toNat_natCast]
        have := zfill_core k s
        simp only at this
        rw [← this]
        simp only [bind, Except.bind]
        split <;> rfl

/-- The fill character as the documentation describes it: default a space, otherwise a `str`
of exactly one character. -/
def fillDoc : Option Arg → Py Nat
  | none => .ok 32
  | some (.str [c]) => .ok c
  | some (.str _) => .error (.typeError "The fill character must be exactly one character long")
  | some a => .error (.typeError s!"The fill character must be a unicode character, not {a.tpName}")

/-- The arguments as Python sees them: `width` goes through `__index__` (which may raise or
answer a non-int) and must fit `Py_ssize_t`; only then is the fill character checked; only
then does the method run. -/
def withWidth (w : Arg) (k : Int → Py Str) : Py Str :=
  match numberIndex w with
  | .error e => .error e
  | .ok v => if v < ssizeMin ∨ v > ssizeMax then .error ssizeOverflowExc else k v

def withFill (f : Option Arg) (k : Nat → Py Str) : Py Str :=
  match fillDoc f with
  | .error e => .error e
  | .ok c => k c

/-- For every string, width argument and fill argument, `center`, `ljust`, `rjust` and `zfill`
convert the width first (its `__index__` errors and `OverflowError` win), then the fill
character (a one-character `str`, else `TypeError`), then pad. -/
def PadArgs : Prop :=
  ∀ (s : Str) (w : Arg) (f : Option Arg),
    unicodeCenter s w f = withWidth w (fun v => withFill f (unicodeCenterImpl s v)) ∧
    unicodeLjust s w f = withWidth w (fun v => withFill f (unicodeLjustImpl s v)) ∧
    unicodeRjust s w f = withWidth w (fun v => withFill f (unicodeRjustImpl s v)) ∧
    unicodeZfill s w = withWidth w (unicodeZfillImpl s)

theorem convertUc_doc (a : Arg) : convertUc a = fillDoc (some a) := by
  cases a with
  | str c =>
    match c with
    | [] => rfl
    | [x] => rfl
    | x :: y :: t => simp [convertUc, fillDoc]
  | _ => rfl

theorem argSsize_bind (w : Arg) (k : Int → Py Str) : (argSsizeObj w >>= k) = withWidth w k := by
  unfold argSsizeObj withWidth mLongAsSsize
  cases numberIndex w with
  | error e => rfl
  | ok v =>
    show (if v < ssizeMin ∨ v > ssizeMax then .error ssizeOverflowExc else .ok v) >>= k =
      (if v < ssizeMin ∨ v > ssizeMax then .error ssizeOverflowExc else k v)
    by_cases h : v < ssizeMin ∨ v > ssizeMax
    · rw [if_pos h, if_pos h]; rfl
    · rw [if_neg h, if_neg h]; rfl

theorem fill_bind (f : Option Arg) (k : Nat → Py Str) : (fillArg f >>= k) = withFill f k := by
  cases f with
  | none => rfl
  | some a =>
    show convertUc a >>= k = _
    rw [convertUc_doc]
    unfold withFill
    cases fillDoc (some a) <;> rfl

theorem padArgs_proven : PadArgs := by
  intro s w f
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [unicodeCenter, argSsize_bind]; congr 1; funext v; rw [fill_bind]
  · rw [unicodeLjust, argSsize_bind]; congr 1; funext v; rw [fill_bind]
  · rw [unicodeRjust, argSsize_bind]; congr 1; funext v; rw [fill_bind]
  · rw [unicodeZfill, argSsize_bind]

end PyLean.UnicodeObj
