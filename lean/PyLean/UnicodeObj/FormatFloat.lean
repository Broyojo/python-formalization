import PyLean.UnicodeObj.FormatProps
import PyLean.UnicodeObj.FormatNumber
import PyLean.UnicodeObj.FormatPercent

/-!
Properties of float and complex formatting over the exact binary64 model.
-/

namespace PyLean.UnicodeObj

open PyLean PyLean.Binary64

/-- `parse_number` splits the number with nothing lost: the digits, the decimal point, the
fraction and the remainder add up to its length, for every string. -/
def ParseNumberSplit : Prop :=
  ∀ s : Str,
    (parseNumber s).1 + (if (parseNumber s).2.1 = true then 1 else 0) + (parseNumber s).2.2.1 +
      (parseNumber s).2.2.2 = s.length

theorem take_drop_length (p : Nat → Bool) (l : List Nat) :
    (l.takeWhile p).length + (l.dropWhile p).length = l.length := by
  rw [← List.length_append, List.takeWhile_append_dropWhile]

theorem split_rest (rest : List Nat) :
    (if (parseRest rest).1 = true then 1 else 0) + (parseRest rest).2.1 + (parseRest rest).2.2 =
      rest.length := by
  simp only [parseRest]
  by_cases hd : (rest.head? == some 46) = true
  · simp only [hd, if_true]
    have h2 := take_drop_length pyDigit rest.tail
    cases rest with
    | nil => simp at hd
    | cons x xs =>
      simp only [List.tail_cons, List.length_cons] at *
      omega
  · simp only [hd, if_false, Bool.false_eq_true]
    have h2 := take_drop_length pyDigit rest
    omega

theorem parseNumberSplit_proven : ParseNumberSplit := by
  intro s
  have h1 := take_drop_length pyDigit s
  have h2 := split_rest (s.dropWhile pyDigit)
  show (s.takeWhile pyDigit).length + (if (parseRest (s.dropWhile pyDigit)).1 = true then 1 else 0) +
    (parseRest (s.dropWhile pyDigit)).2.1 + (parseRest (s.dropWhile pyDigit)).2.2 = s.length
  omega

/-- `format(v, '')` is `str(v)` for an int, and `format(s, '')` is `s`: the empty-spec branch
of the dispatchers, which goes through `format_obj` for a subclass. -/
def FormatEmptySpec : Prop :=
  (∀ (v : Int) (name : String) (shown : Str),
    formatLongAdvanced v name [] shown = .ok (some shown)) ∧
  (∀ s : Str, formatStrAdvanced s [] = .ok s)

theorem formatEmptySpec_proven : FormatEmptySpec :=
  ⟨fun _ _ _ => rfl, fun _ => rfl⟩

/-! ## The text `parse_number` measures -/

theorem take_tw (p : Nat → Bool) (s : List Nat) : s.take (s.takeWhile p).length = s.takeWhile p := by
  induction s with
  | nil => rfl
  | cons a t ih =>
    simp only [List.takeWhile_cons]
    split <;> simp [ih]

theorem drop_tw (p : Nat → Bool) (s : List Nat) : s.drop (s.takeWhile p).length = s.dropWhile p := by
  induction s with
  | nil => rfl
  | cons a t ih =>
    simp only [List.takeWhile_cons, List.dropWhile_cons]
    split <;> simp [ih]

/-- What follows the integer digits and the decimal point. -/
def restOf (s : Str) : Str :=
  let d := s.dropWhile pyDigit
  if (d.head? == some 46) = true then d.tail else d

theorem splitNumber_eq (s : Str) :
    splitNumber s = (s.takeWhile pyDigit, (s.dropWhile pyDigit).head? == some 46,
      (restOf s).takeWhile pyDigit, (restOf s).dropWhile pyDigit) := by
  simp only [splitNumber, parseNumber, parseRest, take_tw, drop_tw, restOf]

theorem splitNumber_join (s : Str) :
    s.takeWhile pyDigit ++ (if ((s.dropWhile pyDigit).head? == some 46) = true then [46] else []) ++
      (restOf s).takeWhile pyDigit ++ (restOf s).dropWhile pyDigit = s := by
  have h0 : s.takeWhile pyDigit ++ s.dropWhile pyDigit = s := List.takeWhile_append_dropWhile
  have h1 : (restOf s).takeWhile pyDigit ++ (restOf s).dropWhile pyDigit = restOf s :=
    List.takeWhile_append_dropWhile
  rw [List.append_assoc, h1, List.append_assoc]
  suffices h : (if ((s.dropWhile pyDigit).head? == some 46) = true then [46] else []) ++ restOf s =
      s.dropWhile pyDigit by rw [h, h0]
  unfold restOf
  cases hd : s.dropWhile pyDigit with
  | nil => simp
  | cons a t => by_cases ha : a = 46 <;> simp [ha]

/-! ## The grouping loops -/

/-- What the loop's count means: it is the length of what the loop wrote. -/
theorem groupLoop_count (grouping : List Nat) (sep : Str) :
    ∀ (fuel i prev : Nat) (useSep : Bool) (rem mw : Int) (rev : List Nat) (count : Nat)
      (out : List Nat) (it n : Nat) (o : List Nat) (it' : Nat),
      groupLoop grouping sep fuel i prev useSep rem mw rev count out it = .ok (n, o, it') →
      rem = rev.length → o.length + count = n + out.length := by
  intro fuel
  induction fuel with
  | zero =>
    intro i prev useSep rem mw rev count out it n o it' h _
    simp [groupLoop] at h
  | succ fuel ih =>
    intro i prev useSep rem mw rev count out it n o it' h hrem
    simp only [groupLoop] at h
    generalize groupNext grouping i prev = g at h
    obtain ⟨len0, i', prev'⟩ := g
    simp only at h
    split at h
    · obtain ⟨len, hlen⟩ : ∃ len : Int, len = min (len0 : Int) (max (max rem mw) 1) := ⟨_, rfl⟩
      rw [← hlen] at h
      obtain ⟨z, hz⟩ : ∃ z : Int, z = max 0 (len - rem) := ⟨_, rfl⟩
      obtain ⟨k, hk⟩ : ∃ k : Int, k = max 0 (min rem len) := ⟨_, rfl⟩
      rw [← hz, ← hk] at h
      have hkr : k.toNat ≤ rev.length := by omega
      simp only [groupPiece] at h
      have hlenout : (List.replicate z.toNat 48 ++ (rev.take k.toNat).reverse ++
          (if useSep = true then sep else []) ++ out).length =
          z.toNat + k.toNat + (if useSep = true then sep.length else 0) + out.length := by
        cases useSep <;> simp [List.length_take, Nat.min_eq_left hkr] <;> omega
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        omega
      · have := ih _ _ true (rem - k) _ (rev.drop k.toNat) _ _ _ n o it' h
          (by rw [List.length_drop]; omega)
        omega
    · obtain ⟨len, hlen⟩ : ∃ len : Int, len = max (max rem mw) 1 := ⟨_, rfl⟩
      rw [← hlen] at h
      obtain ⟨z, hz⟩ : ∃ z : Int, z = max 0 (len - rem) := ⟨_, rfl⟩
      obtain ⟨k, hk⟩ : ∃ k : Int, k = max 0 (min rem len) := ⟨_, rfl⟩
      rw [← hz, ← hk] at h
      have hkr : k.toNat ≤ rev.length := by omega
      simp only [groupPiece, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      cases useSep <;> simp [List.length_take, Nat.min_eq_left hkr] <;> omega

theorem groupLoopFwd_count (grouping : List Nat) (sep : Str) :
    ∀ (fuel i prev : Nat) (useSep : Bool) (rem mw : Int) (ds : Str) (count : Nat)
      (out : Str) (n : Nat) (o : Str),
      groupLoopFwd grouping sep fuel i prev useSep rem mw ds count out = .ok (n, o) →
      rem = ds.length → o.length + count = n + out.length := by
  intro fuel
  induction fuel with
  | zero =>
    intro i prev useSep rem mw ds count out n o h _
    simp [groupLoopFwd] at h
  | succ fuel ih =>
    intro i prev useSep rem mw ds count out n o h hrem
    simp only [groupLoopFwd] at h
    generalize groupNext grouping i prev = g at h
    obtain ⟨len0, i', prev'⟩ := g
    simp only at h
    split at h
    · obtain ⟨len, hlen⟩ : ∃ len : Int, len = min (len0 : Int) (max (max rem mw) 1) := ⟨_, rfl⟩
      rw [← hlen] at h
      obtain ⟨z, hz⟩ : ∃ z : Int, z = max 0 (len - rem) := ⟨_, rfl⟩
      obtain ⟨k, hk⟩ : ∃ k : Int, k = max 0 (min rem len) := ⟨_, rfl⟩
      rw [← hz, ← hk] at h
      have hkr : k.toNat ≤ ds.length := by omega
      simp only [groupPieceFwd] at h
      have hlenout : (out ++ (if useSep = true then sep else []) ++ ds.take k.toNat ++
          List.replicate z.toNat 48).length =
          z.toNat + k.toNat + (if useSep = true then sep.length else 0) + out.length := by
        cases useSep <;> simp [List.length_take, Nat.min_eq_left hkr] <;> omega
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        omega
      · have := ih _ _ true (rem - k) _ (ds.drop k.toNat) _ _ n o h
          (by rw [List.length_drop]; omega)
        omega
    · obtain ⟨len, hlen⟩ : ∃ len : Int, len = max (max rem mw) 1 := ⟨_, rfl⟩
      rw [← hlen] at h
      obtain ⟨z, hz⟩ : ∃ z : Int, z = max 0 (len - rem) := ⟨_, rfl⟩
      obtain ⟨k, hk⟩ : ∃ k : Int, k = max 0 (min rem len) := ⟨_, rfl⟩
      rw [← hz, ← hk] at h
      have hkr : k.toNat ≤ ds.length := by omega
      simp only [groupPieceFwd, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases useSep <;> simp [List.length_take, Nat.min_eq_left hkr] <;> omega

/-! ## Layout without separators -/

/-- `LocaleInfo` for `LT_NO_LOCALE` with no fraction separator. -/
def noLoc (g : List Nat) : LocaleFull := { sep := [], fracSep := [], grouping := g }

/-- The two ways to have no grouping: `no_grouping`, and the empty `grouping` of the C locale. -/
def NoGroup (g : List Nat) : Prop := g = [127] ∨ g = []

/-- No grouping: the zeros that reach `min_width`, then the digits. -/
theorem noGroupMin (ds : Str) (hne : ds ≠ []) (w : Int) (g : List Nat) (hg : NoGroup g) (sep : Str) :
    ∃ it, insertThousandsGrouping ds w g sep =
      .ok ((max (ds.length : Int) w).toNat, List.replicate (w - ds.length).toNat 48 ++ ds, it) := by
  have hn : 0 < ds.length := List.length_pos_iff.2 hne
  refine ⟨0, ?_⟩
  simp only [insertThousandsGrouping]
  have hk : ds.length + (max 0 w).toNat + 2 = (ds.length + (max 0 w).toNat + 1) + 1 := rfl
  rw [hk]
  simp only [groupLoop, groupNext]
  have h1 : max (max (ds.length : Int) (max 0 w)) 1 = max (ds.length : Int) w := by omega
  have h2 : (max 0 (max (ds.length : Int) w - ds.length)).toNat = (w - ds.length).toNat := by omega
  have h3 : (max 0 (min (ds.length : Int) (max (ds.length : Int) w))).toNat = ds.length := by omega
  have h4 : ds.reverse.take ds.length = ds.reverse := List.take_of_length_le (by simp)
  rcases hg with rfl | rfl <;> simp [h1, h2, h3, h4, groupPiece] <;> omega

theorem noGroupFwd (ds : Str) (hne : ds ≠ []) (g : List Nat) (hg : NoGroup g) :
    insertGroupingFwd ds ds.length g [] = .ok (ds.length, ds) := by
  have hn : 0 < ds.length := List.length_pos_iff.2 hne
  simp only [insertGroupingFwd]
  have hk : ds.length + (max 0 (ds.length : Int)).toNat + 2 =
      (ds.length + (max 0 (ds.length : Int)).toNat + 1) + 1 := rfl
  rw [hk]
  simp only [groupLoopFwd, groupNext]
  have h0 : max 0 (ds.length : Int) = ds.length := by omega
  have h1 : max (ds.length : Int) 1 = ds.length := by omega
  rcases hg with rfl | rfl <;> simp [h0, h1, groupPieceFwd, List.take_of_length_le]

/-- What `fill_number` writes when no separator is in play. -/
def layoutOf (sg : Option Nat) (body : Str) (f : FormatSpec) : Str :=
  let (l, s, r) := padFields (f.width - (sg.toList.length + body.length)) f.align
  List.replicate l f.fillChar ++ sg.toList ++ List.replicate s f.fillChar ++ body ++
    List.replicate r f.fillChar

theorem padFields_nonpos (n : Int) (a : Nat) (h : n ≤ 0) : padFields n a = (0, 0, 0) := by
  simp [padFields, show ¬ n > 0 by omega]

/-- `calc_number_widths` once its two grouping calls have returned. -/
theorem calc_ok {sc : Nat} {digits : Str} {hd : Bool} {frac rem : Str} {loc : LocaleFull}
    {f : FormatSpec} {nF nG it : Nat} {fg g : Str}
    (hF : groupedFrac frac loc = .ok (nF, fg))
    (hG : groupedDigits digits (minWidthOf f (nonDigitOf (signField f.sign sc)
      (if hd = true then loc.decimal else []) frac rem) frac.length nF) loc = .ok (nG, g, it)) :
    calcNumberWidthsFull sc digits hd frac rem loc f =
      .ok (let nd := nonDigitOf (signField f.sign sc) (if hd = true then loc.decimal else []) frac rem
           let p := padFields (f.width - (nd + nG + nF - frac.length)) f.align
           { lpad := p.1, sign := signField f.sign sc, spad := p.2.1, grouped := g
             decimal := if hd = true then loc.decimal else [], fracGrouped := fg, remainder := rem
             rpad := p.2.2 }) := by
  simp only [calcNumberWidthsFull, hF, hG, bind, Except.bind]

/-- `calc_number_widths` and `fill_number` together: with no separator the digits lose their
grouping, a `0=` fill lands between the sign and the digits, and the fields add up to the
buffer. -/
theorem fill_plain (sc : Nat) (digits : Str) (hd : Bool) (frac rem : Str) (f : FormatSpec)
    (gr : List Nat) (hgr : NoGroup gr) :
    (calcNumberWidthsFull sc digits hd frac rem (noLoc gr) f >>= fun n =>
        (.ok (fillNumberFull n f.fillChar) : Py Str)) =
      .ok (layoutOf (signField f.sign sc) (digits ++ (if hd = true then [46] else []) ++ frac ++ rem) f) := by
  have hF : groupedFrac frac (noLoc gr) = .ok (frac.length, frac) := by
    cases frac with
    | nil => rfl
    | cons a t =>
      rw [groupedFrac, if_neg (by simp)]
      exact noGroupFwd _ (by simp) gr hgr
  have hdec : (if hd = true then (noLoc gr).decimal else []) = (if hd = true then ([46] : Str) else []) := rfl
  generalize hsg : signField f.sign sc = sg
  generalize hdd : (if hd = true then ([46] : Str) else []) = dec
  have hbody : ((digits ++ dec ++ frac ++ rem).length : Int) =
      digits.length + dec.length + frac.length + rem.length := by simp; omega
  obtain ⟨N, hN⟩ : ∃ N : Int, N = nonDigitOf sg dec frac rem := ⟨_, rfl⟩
  have hNv : N = sg.toList.length + dec.length + frac.length + rem.length := by
    rw [hN, nonDigitOf]
  obtain ⟨m, hm⟩ : ∃ m : Int, m = minWidthOf f N frac.length frac.length := ⟨_, rfl⟩
  have hlay : f.width - ((sg.toList.length : Int) + (digits ++ dec ++ frac ++ rem).length) =
      f.width - (N + digits.length) := by omega
  by_cases hdn : digits.length = 0
  · have hnil : digits = [] := List.eq_nil_of_length_eq_zero hdn
    subst hnil
    have hG : groupedDigits [] (minWidthOf f (nonDigitOf (signField f.sign sc)
        (if hd = true then (noLoc gr).decimal else []) frac rem) frac.length frac.length) (noLoc gr) =
        .ok (0, [], 0) := rfl
    rw [calc_ok hF hG, hdec, hsg, hdd, ← hN]
    have e : f.width - (N + ((0 : Nat) : Int) + frac.length - frac.length) =
        f.width - ((sg.toList.length : Int) + ([] ++ dec ++ frac ++ rem).length) := by
      simp only [List.length_nil, Int.natCast_zero] at hlay ⊢
      omega
    simp only [bind, Except.bind, fillNumberFull, layoutOf, e]
    simp [List.append_assoc]
  · have hne : digits ≠ [] := fun h => hdn (by simp [h])
    obtain ⟨it, hG0⟩ := noGroupMin digits hne m gr hgr []
    have hG : groupedDigits digits (minWidthOf f (nonDigitOf (signField f.sign sc)
        (if hd = true then (noLoc gr).decimal else []) frac rem) frac.length frac.length) (noLoc gr) =
        .ok ((max (digits.length : Int) m).toNat, List.replicate (m - digits.length).toNat 48 ++ digits, it) := by
      rw [hdec, hsg, hdd, ← hN, ← hm, groupedDigits, if_neg hdn]
      exact hG0
    rw [calc_ok hF hG, hdec, hsg, hdd, ← hN]
    simp only [bind, Except.bind, fillNumberFull, layoutOf, hlay]
    have hab : f.width - (N + ((max (digits.length : Int) m).toNat : Int) + frac.length - frac.length) =
        f.width - (N + (max (digits.length : Int) m)) := by omega
    rw [hab]
    by_cases hz : (f.fillChar == 48 && f.align == 61) = true
    · have hmv : m = f.width - N := by
        rw [hm, minWidthOf, if_pos hz]; omega
      have hfa : f.fillChar = 48 ∧ f.align = 61 := by simpa using hz
      by_cases hgt : m > digits.length
      · have e1 : padFields (f.width - (N + (max (digits.length : Int) m))) f.align = (0, 0, 0) :=
          padFields_nonpos _ _ (by omega)
        have e2 : padFields (f.width - (N + digits.length)) f.align = (0, (m - digits.length).toNat, 0) := by
          have : f.width - (N + digits.length) = m - digits.length := by omega
          have hp : m - digits.length > 0 := by omega
          rw [this, padFields, if_pos hp, hfa.2]
          rfl
        simp only [e1, e2, hfa.1]
        simp [List.append_assoc]
      · have e1 : padFields (f.width - (N + (max (digits.length : Int) m))) f.align = (0, 0, 0) :=
          padFields_nonpos _ _ (by omega)
        have e2 : padFields (f.width - (N + digits.length)) f.align = (0, 0, 0) :=
          padFields_nonpos _ _ (by omega)
        have e3 : (m - digits.length).toNat = 0 := by omega
        simp only [e1, e2, e3]
        simp [List.append_assoc]
    · have hm0 : m = 0 := by rw [hm, minWidthOf, if_neg hz]
      subst hm0
      have e : f.width - (N + (max (digits.length : Int) 0)) = f.width - (N + digits.length) := by
        omega
      have e3 : ((0 : Int) - digits.length).toNat = 0 := by omega
      simp only [e, e3]
      simp [List.append_assoc]

/-- The sign and the body of a buffer laid out by the spec. -/
def floatLayout (buf : Str) (f : FormatSpec) : Str :=
  layoutOf (signField f.sign (splitSign buf).1) (splitSign buf).2 f

theorem slow_plain (buf : Str) (f : FormatSpec) (h1 : f.thousands = LT_NO_LOCALE)
    (h2 : f.fracThousands = LT_NO_LOCALE) :
    formatFloatSlow buf f = .ok (floatLayout buf f) := by
  obtain ⟨gr, hgr, hloc⟩ : ∃ gr, NoGroup gr ∧ localeInfoFull
      (if f.type == 110 then LT_CURRENT_LOCALE else f.thousands) f.fracThousands = noLoc gr := by
    rw [h1, h2]
    by_cases h3 : f.type = 110
    · exact ⟨[], Or.inr rfl, by simp [h3]; rfl⟩
    · exact ⟨[127], Or.inl rfl, by simp [h3]; rfl⟩
  simp only [formatFloatSlow, floatLayout, hloc]
  generalize splitSign buf = sb
  obtain ⟨sc, body⟩ := sb
  simp only [splitNumber_eq]
  have := fill_plain sc (body.takeWhile pyDigit) ((body.dropWhile pyDigit).head? == some 46)
    ((restOf body).takeWhile pyDigit) ((restOf body).dropWhile pyDigit) f gr hgr
  rw [splitNumber_join body] at this
  exact this

theorem sign_join (buf : Str) (s : Nat) (h1 : s ≠ 43) (h2 : s ≠ 32) :
    (signField s (splitSign buf).1).toList ++ (splitSign buf).2 = buf := by
  have hs1 : (s == 43) = false := by simpa using h1
  have hs2 : (s == 32) = false := by simpa using h2
  cases buf with
  | nil => simp [signField, splitSign, hs1, hs2]
  | cons a t =>
    by_cases ha : a = 45
    · subst ha; simp [signField, splitSign, hs1, hs2]
    · have : (a == 45) = false := by simpa using ha
      simp [signField, splitSign, hs1, hs2, this]

/-- With no option that touches the digits and a width that cannot pad, the general layout
writes the buffer back. -/
theorem layout_self (buf : Str) (f : FormatSpec) (h1 : f.sign ≠ 43) (h2 : f.sign ≠ 32)
    (hw : f.width ≤ 0) : floatLayout buf f = buf := by
  have hj := sign_join buf f.sign h1 h2
  simp only [floatLayout, layoutOf]
  rw [padFields_nonpos _ _ (by omega)]
  simpa using hj

/-- `format_float_internal` has a fast path that writes the digits straight out. For every
float and every spec that takes it, the general path gives the same text. A width of 0 is
what leaves the fast path without asking for padding: `format(x, '00')` against
`format(x, '')`-style specs. -/
def FloatFastSlowAgree : Prop :=
  ∀ (x : F64) (f : FormatSpec), floatFastPath f = true →
    formatFloatInternal x f = formatFloatInternal x { f with width := 0 }

theorem floatFastPath_facts {f : FormatSpec} (h : floatFastPath f = true) :
    f.sign ≠ 43 ∧ f.sign ≠ 32 ∧ f.width = -1 ∧ f.type ≠ 110 ∧ f.thousands = LT_NO_LOCALE ∧
      f.fracThousands = LT_NO_LOCALE := by
  simpa [floatFastPath, Bool.and_eq_true, and_assoc] using h

theorem floatFastSlowAgree_proven : FloatFastSlowAgree := by
  intro x f hf
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := floatFastPath_facts hf
  have hg : floatFastPath { f with width := 0 } = false := by simp [floatFastPath]
  have hb : floatBuf x { f with width := 0 } = floatBuf x f := rfl
  by_cases hp : f.precision > 2 ^ 31 - 1
  · have hq : ({ f with width := 0 } : FormatSpec).precision > 2 ^ 31 - 1 := hp
    rw [formatFloatInternal, formatFloatInternal, if_pos hp, if_pos hq]
  · have hq : ¬ ({ f with width := 0 } : FormatSpec).precision > 2 ^ 31 - 1 := hp
    rw [formatFloatInternal, formatFloatInternal, if_neg hp, if_neg hq, hb]
    cases floatBuf x f with
    | error e => rfl
    | ok buf =>
      simp only [bind, Except.bind, hf, hg, if_true, Bool.false_eq_true, if_false]
      rw [slow_plain buf { f with width := 0 } h5 h6, layout_self buf { f with width := 0 } h1 h2 (by simp)]

/-! ## What `PyOS_double_to_string` can start with -/

/-- `l` does not start with `c`. -/
def NH (c : Nat) (l : Str) : Prop := l.head? ≠ some c

theorem nh_nil (c : Nat) : NH c [] := by simp [NH]

theorem nh_cons {c x : Nat} (t : Str) (h : x ≠ c) : NH c (x :: t) := by
  simp [NH]; omega

theorem nh_append {c : Nat} {a b : Str} (ha : NH c a) (hb : NH c b) : NH c (a ++ b) := by
  cases a with
  | nil => simpa using hb
  | cons x t => simpa [NH] using ha

theorem nh_dot {c : Nat} {a : Str} (r : Str) (hc : c ≠ 46) (ha : NH c a) : NH c (a ++ 46 :: r) := by
  cases a with
  | nil => exact nh_cons _ (Ne.symm hc)
  | cons x t => simpa [NH] using ha

theorem nh_repl {c : Nat} (n : Nat) (hc : c ≠ 48) : NH c (List.replicate n 48) := by
  cases n with
  | zero => exact nh_nil c
  | succ n => exact nh_cons _ (Ne.symm hc)

theorem nh_dropLast {c : Nat} {l : Str} (h : NH c l) : NH c l.dropLast := by
  cases l with
  | nil => exact nh_nil c
  | cons x t =>
    cases t with
    | nil => exact nh_nil c
    | cons y s => simpa [NH] using h

theorem nh_take {c : Nat} {l : Str} (n : Nat) (h : NH c l) : NH c (l.take n) := by
  cases l with
  | nil => simp [NH]
  | cons x t =>
    cases n with
    | zero => exact nh_nil c
    | succ n => simpa [NH] using h

/-- `dropDot` on the text. -/
def dd (R : Str) : Str := if (R.getLast? == some 46) = true then R.dropLast else R

theorem render_append (a b : List Piece) : render (a ++ b) = render a ++ render b := by
  simp [render]

theorem render_rev_cons (p : Piece) (l : List Piece) :
    render (p :: l).reverse = render l.reverse ++ p.render := by
  simp [render]

theorem dd_append_ne {X c : Str} (hc : c ≠ []) :
    dd (X ++ c) = X ++ dd c := by
  unfold dd
  cases hy : c.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.1 hy) hc
  | some y =>
    have h1 : (X ++ c).getLast? = some y := by simp [List.getLast?_append, hy]
    by_cases hx : y = 46
    · subst hx
      simp [h1, List.dropLast_append_of_ne_nil hc]
    · have : (some y == some 46) = false := by simpa using hx
      simp [h1, this]

theorem go_render (l : List Piece) :
    render (format_float_short.dropDot.go l).reverse = dd (render l.reverse) := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    cases p with
    | zeros n =>
      cases n with
      | zero =>
        simp only [format_float_short.dropDot.go]
        rw [ih, render_rev_cons]
        simp [Piece.render]
      | succ n =>
        simp only [format_float_short.dropDot.go]
        rw [render_rev_cons]
        have : dd (List.replicate (n + 1) 48) = List.replicate (n + 1) 48 := by
          simp [dd, List.getLast?_replicate]
        have hne : List.replicate (n + 1) 48 ≠ [] := by simp
        simp only [Piece.render]
        rw [dd_append_ne hne, this]
    | chars c =>
      cases hc : c with
      | nil =>
        simp only [format_float_short.dropDot.go]
        rw [ih, render_rev_cons]
        simp [Piece.render]
      | cons a t =>
        have hne : a :: t ≠ [] := by simp
        simp only [format_float_short.dropDot.go]
        rw [render_rev_cons]
        simp only [Piece.render]
        rw [dd_append_ne hne]
        split <;> simp_all [render, dd, Piece.render]

theorem render_dropDot (B : List Piece) :
    render (format_float_short.dropDot B) = dd (render B) := by
  simp only [format_float_short.dropDot]
  rw [go_render]
  simp

theorem nh_dd {c : Nat} {R : Str} (h : NH c R) : NH c (dd R) := by
  unfold dd
  split
  · exact nh_dropLast h
  · exact h

theorem fin_nh {c : Nat} {signP leftP midP rightP expP : List Piece} (alt : Bool)
    (hs : NH c (render signP)) (hl : NH c (render leftP)) (hm : NH c (render midP))
    (hr : NH c (render rightP)) (he : NH c (render expP)) :
    NH c (render ((if alt = true then signP ++ leftP ++ midP ++ rightP
      else format_float_short.dropDot (signP ++ leftP ++ midP ++ rightP)) ++ expP)) := by
  rw [render_append]
  have hb : NH c (render (signP ++ leftP ++ midP ++ rightP)) := by
    simp only [render_append]
    exact nh_append (nh_append (nh_append hs hl) hm) hr
  refine nh_append ?_ he
  split
  · exact hb
  · rw [render_dropDot]
    exact nh_dd hb

/-- The digits from `_Py_dg_dtoa` past the special-value test. -/
theorem digits_nh {c : Nat} {digits : List Nat} (hc : Binary64.isDigit c = false)
    (h : ¬ ((digits.length : Int) != 0 && !Binary64.isDigit (digits.headD 0)) = true) : NH c digits := by
  cases digits with
  | nil => exact nh_nil c
  | cons x t =>
    have hx : Binary64.isDigit x = true := by
      have h2 : ¬ ((t.length : Int) + 1 = 0) → Binary64.isDigit x = true := by simpa using h
      exact h2 (by omega)
    exact nh_cons _ (fun e => by rw [e, hc] at hx; cases hx)

/-- Without `Py_DTSF_SIGN` the text never starts with `+`. The `%` path and `format` read a
leading `+` differently, so their agreement rests on this. -/
theorem fss_head (d : F64) (code mode : Nat) (prec : Int) (fl : DtsFlags) (upper : Bool)
    (ps : List Piece) (ty : DtsType) (hs : fl.sign = false)
    (h : format_float_short d code mode prec fl upper = some (ps, ty)) : NH 43 (render ps) := by
  unfold format_float_short at h
  split at h
  · cases h
  · extract_lets digits digits_len sign0 sign1 d0c sign2 pre decpt0 vend0 signP at h
    split at h
    · have hp : NH 43 pre := by
        show NH 43 (if sign2 = true then [45] else if fl.sign = true then [43] else [])
        cases sign2
        · simp [hs, NH]
        · simp [NH]
      split at h <;>
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        simp only [render, List.map_cons, List.map_nil, Piece.render, List.flatten_cons,
          List.flatten_nil, List.append_nil]
        refine nh_append hp ?_
        split <;> exact nh_cons _ (by decide)
    · rename_i hg
      have hdig : NH 43 digits := digits_nh (by decide) hg
      split at h
      rename_i use_exp vend1 _
      split at h
      rename_i exp decpt _
      extract_lets vstart vend leftP midP rightP body body' expP at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have hS : NH 43 (render signP) := by
        show NH 43 (render (if sign1 = true then [.chars [45]] else if fl.sign = true then [.chars [43]] else []))
        cases sign1
        · simp [hs, NH, render]
        · simp [NH, render, Piece.render]
      have hL : NH 43 (render leftP) := by
        show NH 43 (render (if decpt ≤ 0 then [.zeros (decpt - vstart).toNat, .chars [46], .zeros (0 - decpt).toNat]
          else [.zeros (0 - vstart).toNat]))
        split
        · simp only [render, List.map_cons, List.map_nil, Piece.render, List.flatten_cons,
            List.flatten_nil, List.append_nil]
          exact nh_dot _ (by decide) (nh_repl _ (by decide))
        · simpa [render, Piece.render] using nh_repl _ (by decide)
      have hM : NH 43 (render midP) := by
        show NH 43 (render (if 0 < decpt && decpt ≤ digits_len then
          [.chars (digits.take decpt.toNat), .chars [46], .chars (digits.drop decpt.toNat)]
          else [.chars digits]))
        split
        · simp only [render, List.map_cons, List.map_nil, Piece.render, List.flatten_cons,
            List.flatten_nil, List.append_nil]
          exact nh_dot _ (by decide) (nh_take _ hdig)
        · simpa [render, Piece.render] using hdig
      have hR : NH 43 (render rightP) := by
        show NH 43 (render (if digits_len < decpt then
          [.zeros (decpt - digits_len).toNat, .chars [46], .zeros (vend - decpt).toNat]
          else [.zeros (vend - digits_len).toNat]))
        split
        · simp only [render, List.map_cons, List.map_nil, Piece.render, List.flatten_cons,
            List.flatten_nil, List.append_nil]
          exact nh_dot _ (by decide) (nh_repl _ (by decide))
        · simpa [render, Piece.render] using nh_repl _ (by decide)
      have hE : NH 43 (render expP) := by
        show NH 43 (render (if use_exp = true then [.chars ((if upper = true then 69 else 101) :: fmtExp exp)] else []))
        split
        · simp only [render, List.map_cons, List.map_nil, Piece.render, List.flatten_cons,
            List.flatten_nil, List.append_nil]
          split <;> exact nh_cons _ (by decide)
        · exact nh_nil 43
      exact fin_nh fl.alt hS hL hM hR hE

theorem dts_head (x : F64) (code : Nat) (prec : Int) (fl : DtsFlags) (buf : Str)
    (hs : fl.sign = false) (h : doubleToString x code prec fl = .ok buf) : NH 43 buf := by
  unfold doubleToString at h
  split at h
  · cases h
  · rename_i r hr
    have hb : render r.1 = buf := by simpa using h
    subst hb
    obtain ⟨ps, ty⟩ := r
    simp only [PyOS_double_to_string] at hr
    repeat' split at hr
    all_goals first
      | cases hr
      | exact fss_head _ _ _ _ _ _ _ _ hs hr

/-! ## `%` against `format` -/

/-- The spec of `format()` that says what a `%` directive says: `-` wins over `0`, and `+`
wins over a space. -/
def pctSpec (arg : FArg) : FormatSpec :=
  { fillChar := if arg.flags.zero && !arg.flags.ljust then 48 else 32
    align := if arg.flags.ljust then 60 else if arg.flags.zero then 61 else 62
    alternate := arg.flags.alt
    sign := if arg.flags.sign then 43 else if arg.flags.blank then 32 else 0
    width := arg.width, precision := arg.prec, type := arg.ch }

/-- The types of `formatfloat`. -/
def FloatCh (c : Nat) : Prop := c = 101 ∨ c = 69 ∨ c = 102 ∨ c = 70 ∨ c = 103 ∨ c = 71

/-- What is left of `unicode_format_arg_output` with no `0x` prefix to handle. -/
theorem tail_form (arg : FArg) (sign : Bool) (sc : Nat) (body str : Str) (pindex : Nat)
    (hd : str.drop pindex = body)
    (hna : (arg.flags.alt && (arg.ch == 120 || arg.ch == 88 || arg.ch == 111)) = false) :
    formatArgTail arg (if arg.flags.zero = true then 48 else 32) sign sc body.length pindex str =
      let sg : Str := if sign = true then [sc] else []
      let p := (arg.width - ((sg.length : Int) + body.length)).toNat
      if arg.flags.ljust = true then sg ++ body ++ List.replicate p 32
      else if arg.flags.zero = true then sg ++ List.replicate p 48 ++ body
      else List.replicate p 32 ++ sg ++ body := by
  have htake : (str.drop pindex).take ((body.length : Int)).toNat = body := by
    rw [hd]; simp
  obtain ⟨w, hw⟩ : ∃ w, w = arg.width := ⟨_, rfl⟩
  have b1 : ((48 : Nat) != 32) = true := rfl
  have b2 : ((48 : Nat) == 32) = false := rfl
  simp only [formatArgTail, hna, Bool.false_eq_true, if_false, htake, ← hw]
  cases hl : arg.flags.ljust <;> cases hz : arg.flags.zero <;> cases sign <;>
    simp only [Bool.false_eq_true, if_false, if_true, Bool.true_and,
      Bool.false_and, Bool.and_true, Bool.and_false, Bool.not_true, Bool.not_false,
      decide_eq_true_eq, bne_self_eq_false, beq_self_eq_true, b1, b2] <;>
    (repeat' split) <;> (try omega) <;> (try (simp at *; done)) <;>
      (simp [List.append_assoc]; try omega)

/-- The general layout with the spec of a `%` directive. -/
theorem layout_pct (arg : FArg) (sgo : Option Nat) (body : Str) :
    layoutOf sgo body (pctSpec arg) =
      let p := (arg.width - ((sgo.toList.length : Int) + body.length)).toNat
      if arg.flags.ljust = true then sgo.toList ++ body ++ List.replicate p 32
      else if arg.flags.zero = true then sgo.toList ++ List.replicate p 48 ++ body
      else List.replicate p 32 ++ sgo.toList ++ body := by
  obtain ⟨n, hn⟩ : ∃ n : Int, n = arg.width - ((sgo.toList.length : Int) + body.length) := ⟨_, rfl⟩
  have hw : (pctSpec arg).width = arg.width := rfl
  simp only [layoutOf, hw, ← hn]
  by_cases hp : n > 0
  · cases hl : arg.flags.ljust <;> cases hz : arg.flags.zero <;>
      simp [padFields, hp, pctSpec, hl, hz, List.append_assoc]
  · have h0 : n.toNat = 0 := by omega
    rw [padFields_nonpos _ _ (by omega)]
    cases hl : arg.flags.ljust <;> cases hz : arg.flags.zero <;>
      simp [h0, pctSpec, hl, hz, List.append_assoc]

theorem layout_fit (buf : Str) (f : FormatSpec) (h1 : f.sign ≠ 43) (h2 : f.sign ≠ 32)
    (hw : f.width ≤ buf.length) : floatLayout buf f = buf := by
  have hj := sign_join buf f.sign h1 h2
  have hl : ((signField f.sign (splitSign buf).1).toList.length : Int) + (splitSign buf).2.length =
      buf.length := by
    have := congrArg List.length hj
    simp only [List.length_append] at this
    omega
  simp only [floatLayout, layoutOf]
  rw [padFields_nonpos _ _ (by omega)]
  simpa using hj

theorem floatCh_facts {c : Nat} (hc : FloatCh c) :
    c ≠ 115 ∧ c ≠ 114 ∧ c ≠ 97 ∧ c ≠ 120 ∧ c ≠ 88 ∧ c ≠ 111 ∧ c ≠ 105 ∧ c ≠ 100 ∧ c ≠ 117 ∧
      c ≠ 0 ∧ c ≠ 110 ∧ c ≠ 37 ∧ c ≠ 114 := by
  unfold FloatCh at hc
  omega

/-- `unicode_format_arg_output` and `calc_number_widths` with `fill_number` are two separate
implementations of the same layout. For a buffer that does not start with `+`, every
combination of `-`, `0`, `+` and space lays it out alike. -/
theorem output_layout (arg : FArg) (buf : Str) (hc : FloatCh arg.ch) (hw : -1 ≤ arg.width)
    (h43 : NH 43 buf) : formatArgOutput arg true buf = floatLayout buf (pctSpec arg) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, -⟩ := floatCh_facts hc
  have hna : (arg.flags.alt && (arg.ch == 120 || arg.ch == 88 || arg.ch == 111)) = false := by
    simp [c4, c5, c6]
  have hst : (arg.ch == 115 || arg.ch == 114 || arg.ch == 97) = false := by simp [c1, c2, c3]
  unfold formatArgOutput
  simp only [Bool.true_and, hst, Bool.false_eq_true, false_and, if_false]
  split
  · rename_i hE
    obtain ⟨hA, -, hS, hB⟩ := hE
    have hs0 : arg.flags.sign = false := by simpa using hS
    have hb0 : arg.flags.blank = false := by simpa using hB
    have hsg : (pctSpec arg).sign = 0 := by simp [pctSpec, hs0, hb0]
    refine (layout_fit buf (pctSpec arg) (by omega) (by omega) ?_).symm
    show arg.width ≤ buf.length
    rcases hA with hA | hA
    · have : arg.width = -1 := by simpa using hA
      omega
    · exact hA
  · rename_i hE
    have hfp : (pctSpec arg).width = arg.width := rfl
    by_cases h45 : buf.headD 0 = 45
    · obtain ⟨t, rfl⟩ : ∃ t, buf = 45 :: t := by
        cases buf with
        | nil => simp at h45
        | cons a t =>
          have : a = 45 := by simpa using h45
          exact ⟨t, by rw [this]⟩
      have hlen : (((45 :: t : Str).length : Int) - 1) = t.length := by simp
      have hsf : signField (pctSpec arg).sign (splitSign (45 :: t)).1 = some 45 := by
        have e : (splitSign (45 :: t)).1 = 45 := rfl
        rw [e]
        simp only [signField, pctSpec]
        by_cases hs1 : arg.flags.sign = true <;> by_cases hb1 : arg.flags.blank = true <;> simp [hs1, hb1]
      have hsp : (splitSign (45 :: t)).2 = t := rfl
      have hh : (45 :: t : Str).headD 0 = 45 := rfl
      have e2 : ((45 : Nat) == 45 || (45 : Nat) == 43) = true := rfl
      simp only [hh, e2, if_true, hlen]
      have ht := tail_form arg true 45 t (45 :: t) 1 rfl hna
      simp only [if_true] at ht
      rw [ht, floatLayout, hsf, hsp, layout_pct]
      simp
    · have n43 : buf.headD 0 ≠ 43 := by
        intro h
        apply h43
        cases buf with
        | nil => simp at h
        | cons a t =>
          have : a = 43 := by simpa using h
          simp [this]
      have a1 : (buf.headD 0 == 45) = false := beq_eq_false_iff_ne.2 h45
      have a2 : (buf.headD 0 == 43) = false := beq_eq_false_iff_ne.2 n43
      have e1 : (buf.headD 0 == 45 || buf.headD 0 == 43) = false := by rw [a1, a2]; rfl
      have hsp : splitSign buf = (0, buf) := by
        simp only [splitSign, a1, Bool.false_eq_true, if_false]
      have hd0 : buf.drop 0 = buf := rfl
      simp only [e1, Bool.false_eq_true, if_false, if_true, floatLayout, hsp]
      rw [layout_pct]
      cases hs : arg.flags.sign
      · cases hb : arg.flags.blank
        · have ht := tail_form arg false 0 buf buf 0 hd0 hna
          simp only [Bool.false_eq_true, if_false] at ht
          simp only [hs, hb, Bool.false_eq_true, if_false, ht, signField, pctSpec]
          simp
        · have ht := tail_form arg true 32 buf buf 0 hd0 hna
          simp only [if_true] at ht
          simp only [hs, hb, Bool.false_eq_true, if_false, if_true, ht, signField, pctSpec]
          simp
      · have ht := tail_form arg true 43 buf buf 0 hd0 hna
        simp only [if_true] at ht
        simp only [hs, if_true, ht, signField, pctSpec]
        simp

/-- A directive's result as `unicode_format_arg` writes it. -/
def outText (arg : FArg) : FOut → Str
  | .direct s => s
  | .viaOutput s sign => formatArgOutput arg sign s

/-- `%` and `format()` are separate paths to the same digits: `'%-08.3f' % x` and the like go
through `formatfloat` and `unicode_format_arg_output`, `format` through
`format_float_internal`. For every float and every flag, width and precision of a `%e`, `%f`
or `%g` directive, they give the same text. `-1 ≤ width` is what the parser leaves: the one way
past it is `unicodeobj-format-percent-star-width`, on record as refuted. -/
def PercentFloatMatchesFormat : Prop :=
  ∀ (ctx ctx' : FCtx) (x : F64) (arg : FArg) (i : Nat),
    getNextArg ctx = .ok (.float x, ctx') → FloatCh arg.ch → -1 ≤ arg.width →
    arg.prec ≤ 2 ^ 31 - 1 →
    (formatArgFormat ctx arg i >>= fun r => (.ok (outText arg r.1, r.2) : Py (Str × FCtx))) =
      (formatFloatInternal x (pctSpec arg) >>= fun s => .ok (s, ctx'))

theorem floatBuf_pct (x : F64) (arg : FArg) (hc : FloatCh arg.ch) :
    floatBuf x (pctSpec arg) =
      doubleToString x arg.ch (if arg.prec < 0 then 6 else arg.prec) { alt := arg.flags.alt } := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, -⟩ := floatCh_facts hc
  have a0 : (arg.ch == 0) = false := beq_eq_false_iff_ne.2 c10
  have a1 : (arg.ch == 110) = false := beq_eq_false_iff_ne.2 c11
  have a2 : (arg.ch == 37) = false := beq_eq_false_iff_ne.2 c12
  have a3 : (arg.ch == 114) = false := beq_eq_false_iff_ne.2 c2
  by_cases hp : arg.prec < 0
  · simp only [floatBuf, pctSpec, a0, a1, a2, Bool.false_eq_true, if_false, if_pos hp]
    generalize doubleToString _ _ _ _ = y
    cases y <;> rfl
  · simp only [floatBuf, pctSpec, a0, a1, a2, a3, Bool.false_eq_true, if_false, if_neg hp]
    generalize doubleToString _ _ _ _ = y
    cases y <;> rfl

theorem percentFloatMatchesFormat_proven : PercentFloatMatchesFormat := by
  intro ctx ctx' x arg i hn hc hw hp
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, -⟩ := floatCh_facts hc
  have e1 : (arg.ch == 115 || arg.ch == 114 || arg.ch == 97) = false := by simp [c1, c2, c3]
  have e2 : (arg.ch == 105 || arg.ch == 100 || arg.ch == 117 || arg.ch == 111 || arg.ch == 120 ||
      arg.ch == 88) = false := by simp [c4, c5, c6, c7, c8, c9]
  have e3 : (arg.ch == 101 || arg.ch == 69 || arg.ch == 102 || arg.ch == 70 || arg.ch == 103 ||
      arg.ch == 71) = true := by
    unfold FloatCh at hc
    rcases hc with h | h | h | h | h | h <;> simp [h]
  have hpr : ¬ (pctSpec arg).precision > 2 ^ 31 - 1 := by
    show ¬ arg.prec > 2 ^ 31 - 1
    omega
  rw [formatFloatInternal, if_neg hpr, floatBuf_pct x arg hc]
  simp only [formatArgFormat, hn, bind, Except.bind, e1, e2, e3, Bool.false_eq_true, if_false,
    if_true, formatFloatPct, FObj.asDouble]
  cases hd : doubleToString x arg.ch (if arg.prec < 0 then 6 else arg.prec) { alt := arg.flags.alt } with
  | error e => rfl
  | ok buf =>
    have h43 : NH 43 buf := dts_head _ _ _ _ _ rfl hd
    have hL := output_layout arg buf hc hw h43
    have hthou : (pctSpec arg).thousands = LT_NO_LOCALE := rfl
    have hfrac : (pctSpec arg).fracThousands = LT_NO_LOCALE := rfl
    have hS := slow_plain buf (pctSpec arg) hthou hfrac
    by_cases hdir : (arg.width == -1 && arg.prec == -1 && !arg.flags.sign && !arg.flags.blank) = true
    · have hA : arg.width = -1 ∧ arg.prec = -1 ∧ arg.flags.sign = false ∧ arg.flags.blank = false := by
        simpa [Bool.and_eq_true, and_assoc] using hdir
      have hf : floatFastPath (pctSpec arg) = true := by
        simp [floatFastPath, pctSpec, hA.1, hA.2.2.1, hA.2.2.2, c11]
      simp only [hdir, if_true, hf, pure, Except.pure, outText]
    · have hdir' : (arg.width == -1 && arg.prec == -1 && !arg.flags.sign && !arg.flags.blank) = false := by
        simpa using hdir
      simp only [hdir', Bool.false_eq_true, if_false, pure, Except.pure, outText, hL]
      by_cases hf : floatFastPath (pctSpec arg) = true
      · obtain ⟨g1, g2, g3, -⟩ := floatFastPath_facts hf
        simp only [hf, if_true, layout_self buf (pctSpec arg) g1 g2 (by omega)]
      · have hf' : floatFastPath (pctSpec arg) = false := by simpa using hf
        simp only [hf', Bool.false_eq_true, if_false, hS]

/-- Every spec with no separator: `format_float_internal` gives the buffer of
`PyOS_double_to_string` with the sign the spec asks for and the padding of its width, fill and
alignment. The fast path and the general path are both in this statement. -/
def FloatSpecLayout : Prop :=
  ∀ (x : F64) (f : FormatSpec), f.thousands = LT_NO_LOCALE → f.fracThousands = LT_NO_LOCALE →
    f.precision ≤ 2 ^ 31 - 1 →
    formatFloatInternal x f = (floatBuf x f >>= fun buf => .ok (floatLayout buf f))

theorem floatSpecLayout_proven : FloatSpecLayout := by
  intro x f h1 h2 hp
  rw [formatFloatInternal, if_neg (by omega)]
  cases floatBuf x f with
  | error e => rfl
  | ok buf =>
    simp only [bind, Except.bind]
    by_cases hf : floatFastPath f = true
    · obtain ⟨g1, g2, g3, -⟩ := floatFastPath_facts hf
      rw [if_pos hf, layout_self buf f g1 g2 (by omega)]
    · rw [if_neg hf, slow_plain buf f h1 h2]

/-! ## The width is a minimum -/

theorem groupedFrac_len {frac : Str} {loc : LocaleFull} {n : Nat} {fg : Str}
    (h : groupedFrac frac loc = .ok (n, fg)) : fg.length = n := by
  unfold groupedFrac at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · unfold insertGroupingFwd at h
    have := groupLoopFwd_count _ _ _ _ _ _ _ _ _ _ _ _ _ h rfl
    simpa using this

theorem groupedDigits_len {ds : Str} {m : Int} {loc : LocaleFull} {n it : Nat} {g : Str}
    (h : groupedDigits ds m loc = .ok (n, g, it)) : g.length = n := by
  unfold groupedDigits at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    rfl
  · unfold insertThousandsGrouping at h
    have := groupLoop_count _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h (by simp)
    simpa using this

theorem padFields_sum (n : Int) (a : Nat) :
    (padFields n a).1 + (padFields n a).2.1 + (padFields n a).2.2 = n.toNat := by
  unfold padFields
  split
  · repeat' split
    all_goals simp only
    all_goals omega
  · simp only
    omega

theorem fill_width {sc : Nat} {digits : Str} {hd : Bool} {frac rem : Str} {loc : LocaleFull}
    {f : FormatSpec} {n : NumFields} (fill : Nat)
    (h : calcNumberWidthsFull sc digits hd frac rem loc f = .ok n) :
    f.width ≤ (fillNumberFull n fill).length := by
  cases hF : groupedFrac frac loc with
  | error e => simp [calcNumberWidthsFull, hF, bind, Except.bind] at h
  | ok rF =>
    obtain ⟨nF, fg⟩ := rF
    cases hG : groupedDigits digits (minWidthOf f (nonDigitOf (signField f.sign sc)
        (if hd = true then loc.decimal else []) frac rem) frac.length nF) loc with
    | error e => simp [calcNumberWidthsFull, hF, hG, bind, Except.bind] at h
    | ok rG =>
      obtain ⟨nG, g, it⟩ := rG
      rw [calc_ok hF hG] at h
      have l1 := groupedFrac_len hF
      have l2 := groupedDigits_len hG
      simp only [Except.ok.injEq] at h
      subst h
      generalize hnd : nonDigitOf (signField f.sign sc) (if hd = true then loc.decimal else []) frac rem = nd
      have hs := padFields_sum (f.width - (nd + nG + nF - frac.length)) f.align
      have hv : nd = (signField f.sign sc).toList.length + (if hd = true then loc.decimal else []).length +
          frac.length + rem.length := by rw [← hnd, nonDigitOf]
      simp only [fillNumberFull, List.length_append, List.length_replicate]
      omega

/-- The format spec docs: "width is a decimal integer defining the minimum total field width".
For every float and every spec, separators and all, the result is at least that long. -/
def FloatWidthIsMinimum : Prop :=
  ∀ (x : F64) (f : FormatSpec) (s : Str), formatFloatInternal x f = .ok s → f.width ≤ s.length

theorem slow_width {buf s : Str} {f : FormatSpec} (h : formatFloatSlow buf f = .ok s) :
    f.width ≤ s.length := by
  simp only [formatFloatSlow, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i n hn
    simp only [Except.ok.injEq] at h
    subst h
    exact fill_width _ hn

theorem floatWidthIsMinimum_proven : FloatWidthIsMinimum := by
  intro x f s h
  rw [formatFloatInternal] at h
  split at h
  · cases h
  · simp only [bind, Except.bind] at h
    split at h
    · cases h
    · split at h
      · rename_i hf
        have := (floatFastPath_facts hf).2.2.1
        omega
      · exact slow_width h

/-! ## Separators are all that grouping adds -/

theorem groupNext_single (g : Nat) (h0 : g ≠ 0) (h1 : g ≠ 127) (i prev : Nat)
    (h : (i = 0 ∧ prev = 0) ∨ (i = 1 ∧ prev = g)) : groupNext [g] i prev = (g, 1, g) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · unfold groupNext
    have : ([g] : List Nat)[0]? = some g := rfl
    rw [this]
    split <;> simp_all
  · rfl

theorem filter_all_true {F : Nat → Bool} {l : List Nat} (h : ∀ c ∈ l, F c = true) :
    l.filter F = l := List.filter_eq_self.2 h

theorem filter_all_false {F : Nat → Bool} {l : List Nat} (h : ∀ c ∈ l, F c = false) :
    l.filter F = [] := by
  rw [List.filter_eq_nil_iff]
  intro c hc
  simp [h c hc]

/-- The backward loop of `_PyUnicode_InsertThousandsGrouping` ends within its fuel, and what it
wrote minus the separator is the digits. -/
theorem groupLoop_filter (g : Nat) (sep : Str) (F : Nat → Bool) (h0 : g ≠ 0) (h1 : g ≠ 127)
    (hsep : ∀ c ∈ sep, F c = false) :
    ∀ (fuel i prev : Nat) (useSep : Bool) (mw : Int) (rev : List Nat) (count : Nat) (out : List Nat)
      (it : Nat), ((i = 0 ∧ prev = 0) ∨ (i = 1 ∧ prev = g)) → mw ≤ rev.length → rev ≠ [] →
      rev.length < fuel → (∀ c ∈ rev, F c = true) →
      ∃ n o it', groupLoop [g] sep fuel i prev useSep rev.length mw rev count out it = .ok (n, o, it') ∧
        o.filter F = rev.reverse ++ out.filter F := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ h _; omega
  | succ fuel ih =>
    intro i prev useSep mw rev count out it hi hmw hne hfuel hF
    have hL : 0 < rev.length := List.length_pos_iff.2 hne
    have hN := groupNext_single g h0 h1 i prev hi
    obtain ⟨k, hk⟩ : ∃ k, k = min g rev.length := ⟨_, rfl⟩
    have hk1 : 0 < k := by omega
    have e1 : min (g : Int) (max (max (rev.length : Int) mw) 1) = k := by omega
    have e2 : max 0 ((k : Int) - rev.length) = 0 := by omega
    have e3 : max 0 (min (rev.length : Int) (k : Int)) = k := by omega
    have htk : ∀ c ∈ (rev.take k).reverse, F c = true := by
      intro c hc
      exact hF c (List.mem_of_mem_take (List.mem_reverse.1 hc))
    have hflt : (List.replicate 0 48 ++ (rev.take k).reverse ++ (if useSep = true then sep else []) ++ out).filter F =
        (rev.take k).reverse ++ out.filter F := by
      simp only [List.replicate_zero, List.nil_append, List.filter_append, filter_all_true htk]
      cases useSep
      · simp
      · simp [filter_all_false hsep]
    simp only [groupLoop, hN, gt_iff_lt, Nat.pos_of_ne_zero h0, if_true, e1, e2, e3, groupPiece,
      Int.toNat_zero, Int.toNat_natCast]
    by_cases hend : k = rev.length
    · have hc : ((rev.length : Int) - k ≤ 0 ∧ mw - k ≤ 0) := by omega
      refine ⟨_, _, _, if_pos hc, ?_⟩
      rw [hflt, hend, List.take_length]
    · have hc : ¬ ((rev.length : Int) - k ≤ 0 ∧ mw - k ≤ 0) := by omega
      rw [if_neg hc]
      have hd : (rev.drop k).length = rev.length - k := List.length_drop ..
      have hcast : (rev.length : Int) - k = ((rev.drop k).length : Int) := by omega
      rw [hcast]
      have hne' : rev.drop k ≠ [] := by
        intro h
        rw [h] at hd
        simp at hd
        omega
      obtain ⟨n, o, it', h2, h3⟩ := ih 1 g true (mw - k - sep.length) (rev.drop k) _
        (List.replicate 0 48 ++ (rev.take k).reverse ++ (if useSep = true then sep else []) ++ out)
        (it + 1) (Or.inr ⟨rfl, rfl⟩) (by omega) hne' (by omega)
        (fun c hc => hF c (List.mem_of_mem_drop hc))
      refine ⟨n, o, it', h2, ?_⟩
      have hr : rev.reverse = (rev.drop k).reverse ++ (rev.take k).reverse := by
        rw [← List.reverse_append, List.take_append_drop]
      rw [h3, hflt, ← List.append_assoc, ← hr]

/-- The forward loop, for the fraction. -/
theorem groupLoopFwd_filter (g : Nat) (sep : Str) (F : Nat → Bool) (h0 : g ≠ 0) (h1 : g ≠ 127)
    (hsep : ∀ c ∈ sep, F c = false) :
    ∀ (fuel i prev : Nat) (useSep : Bool) (mw : Int) (ds : Str) (count : Nat) (out : Str),
      ((i = 0 ∧ prev = 0) ∨ (i = 1 ∧ prev = g)) → mw ≤ ds.length → ds ≠ [] →
      ds.length < fuel → (∀ c ∈ ds, F c = true) →
      ∃ n o, groupLoopFwd [g] sep fuel i prev useSep ds.length mw ds count out = .ok (n, o) ∧
        o.filter F = out.filter F ++ ds := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ _ h _; omega
  | succ fuel ih =>
    intro i prev useSep mw ds count out hi hmw hne hfuel hF
    have hL : 0 < ds.length := List.length_pos_iff.2 hne
    have hN := groupNext_single g h0 h1 i prev hi
    obtain ⟨k, hk⟩ : ∃ k, k = min g ds.length := ⟨_, rfl⟩
    have hk1 : 0 < k := by omega
    have e1 : min (g : Int) (max (max (ds.length : Int) mw) 1) = k := by omega
    have e2 : max 0 ((k : Int) - ds.length) = 0 := by omega
    have e3 : max 0 (min (ds.length : Int) (k : Int)) = k := by omega
    have htk : ∀ c ∈ ds.take k, F c = true := fun c hc => hF c (List.mem_of_mem_take hc)
    have hflt : (out ++ (if useSep = true then sep else []) ++ ds.take k ++ List.replicate 0 48).filter F =
        out.filter F ++ ds.take k := by
      simp only [List.replicate_zero, List.append_nil, List.filter_append, filter_all_true htk]
      cases useSep
      · simp
      · simp [filter_all_false hsep]
    simp only [groupLoopFwd, hN, gt_iff_lt, Nat.pos_of_ne_zero h0, if_true, e1, e2, e3, groupPieceFwd,
      Int.toNat_zero, Int.toNat_natCast]
    by_cases hend : k = ds.length
    · have hc : ((ds.length : Int) - k ≤ 0 ∧ mw - k ≤ 0) := by omega
      refine ⟨_, _, if_pos hc, ?_⟩
      rw [hflt, hend, List.take_length]
    · have hc : ¬ ((ds.length : Int) - k ≤ 0 ∧ mw - k ≤ 0) := by omega
      rw [if_neg hc]
      have hd : (ds.drop k).length = ds.length - k := List.length_drop ..
      have hcast : (ds.length : Int) - k = ((ds.drop k).length : Int) := by omega
      rw [hcast]
      have hne' : ds.drop k ≠ [] := by
        intro h
        rw [h] at hd
        simp at hd
        omega
      obtain ⟨n, o, h2, h3⟩ := ih 1 g true (mw - k - sep.length) (ds.drop k) _
        (out ++ (if useSep = true then sep else []) ++ ds.take k ++ List.replicate 0 48)
        (Or.inr ⟨rfl, rfl⟩) (by omega) hne' (by omega)
        (fun c hc => hF c (List.mem_of_mem_drop hc))
      refine ⟨n, o, h2, ?_⟩
      rw [h3, hflt, List.append_assoc, List.take_append_drop]

/-- With no padding, the grouped text is the digits with separators between them: dropping
the separator gives the digits back, and the count is the text's length. -/
theorem groupDigits_proven : GroupDigits := by
  intro ds sep g h0 hsep hne
  have hF : ∀ c ∈ ds, (c != sep) = true := by
    intro c hc
    have : c ≠ sep := fun e => hsep (e ▸ hc)
    simpa using this
  by_cases h1 : g = 127
  · subst h1
    obtain ⟨it, h⟩ := noGroupMin ds hne 0 [127] (Or.inl rfl) [sep]
    have hz : ((0 : Int) - ds.length).toNat = 0 := by omega
    rw [hz] at h
    refine ⟨_, _, _, h, ?_, ?_⟩
    · simp
    · simpa using filter_all_true hF
  · have hrev : ds.reverse ≠ [] := by simpa using hne
    obtain ⟨n, o, it, h2, h3⟩ := groupLoop_filter g [sep] (· != sep) (by omega) h1 (by simp)
      (ds.length + 2) 0 0 false 0 ds.reverse 0 [] 0 (Or.inl ⟨rfl, rfl⟩) (by simp) hrev (by simp)
      (by simpa using hF)
    have h4 : insertThousandsGrouping ds 0 [g] [sep] = .ok (n, o, it) := by
      have : ((ds.reverse.length : Nat) : Int) = (ds.length : Int) := by simp
      rw [this] at h2
      simpa [insertThousandsGrouping] using h2
    refine ⟨n, o, it, h4, ?_, ?_⟩
    · have := groupLoop_count _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h2 (by simp)
      simpa using this
    · simpa using h3

/-- Neither of the two separators. -/
def noSep (c : Nat) : Bool := c != 44 && c != 95

/-- The text with its separators taken out. -/
def ungroup (s : Str) : Str := s.filter noSep

theorem pyDigit_noSep {c : Nat} (h : pyDigit c = true) : noSep c = true := by
  simp only [pyDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [noSep, Bool.and_eq_true, bne_iff_ne]
  omega

/-- A `LocaleInfo` that groups by three. -/
structure GLoc (loc : LocaleFull) : Prop where
  dec : loc.decimal = [46]
  gr : loc.grouping = [3]
  sep : ∀ c ∈ loc.sep, noSep c = false
  frac : ∀ c ∈ loc.fracSep, noSep c = false

theorem gloc_of (t u : Nat) (ht : t = 0 ∨ t = 44 ∨ t = 95) (hu : u = 0 ∨ u = 44 ∨ u = 95)
    (h : ¬ (t = 0 ∧ u = 0)) : GLoc (localeInfoFull t u) := by
  rcases ht with rfl | rfl | rfl <;> rcases hu with rfl | rfl | rfl
  · exact absurd ⟨rfl, rfl⟩ h
  all_goals
    constructor
    · rfl
    · rfl
    · intro c hc
      simp only [localeInfoFull, localeInfo, LT_CURRENT_LOCALE, LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE,
        LT_UNDER_FOUR_LOCALE, LT_NO_LOCALE] at hc
      simp at hc
      try (subst hc; rfl)
    · intro c hc
      simp only [localeInfoFull, localeInfo, LT_CURRENT_LOCALE, LT_DEFAULT_LOCALE, LT_UNDERSCORE_LOCALE,
        LT_UNDER_FOUR_LOCALE, LT_NO_LOCALE] at hc
      simp at hc
      try (subst hc; rfl)

theorem gf_filter {loc : LocaleFull} (hl : GLoc loc) (frac : Str) (hf : ∀ c ∈ frac, noSep c = true) :
    ∃ nF fg, groupedFrac frac loc = .ok (nF, fg) ∧ fg.filter noSep = frac := by
  cases frac with
  | nil => exact ⟨0, [], rfl, rfl⟩
  | cons a t =>
    obtain ⟨n, o, h1, h2⟩ := groupLoopFwd_filter 3 loc.fracSep noSep (by decide) (by decide) hl.frac
      ((a :: t).length + (a :: t).length + 2) 0 0 false (a :: t).length (a :: t) 0 [] (Or.inl ⟨rfl, rfl⟩)
      (by omega) (by simp) (by omega) hf
    refine ⟨n, o, ?_, by simpa using h2⟩
    rw [groupedFrac, if_neg (by simp), insertGroupingFwd, hl.gr]
    have e : max 0 (((a :: t).length : Nat) : Int) = (a :: t).length := by omega
    rw [e, Int.toNat_natCast]
    exact h1

theorem gd_filter {loc : LocaleFull} (hl : GLoc loc) (ds : Str) (m : Int) (hm : m ≤ 0)
    (hd : ∀ c ∈ ds, noSep c = true) :
    ∃ nG g it, groupedDigits ds m loc = .ok (nG, g, it) ∧ g.filter noSep = ds := by
  cases ds with
  | nil => exact ⟨0, [], 0, rfl, rfl⟩
  | cons a t =>
    have hrev : (a :: t).reverse ≠ [] := by simp
    obtain ⟨n, o, it, h1, h2⟩ := groupLoop_filter 3 loc.sep noSep (by decide) (by decide) hl.sep
      ((a :: t).length + 2) 0 0 false 0 (a :: t).reverse 0 [] 0 (Or.inl ⟨rfl, rfl⟩) (by omega) hrev
      (by simp) (fun c hc => hd c (List.mem_reverse.1 hc))
    refine ⟨n, o, it, ?_, by simpa using h2⟩
    rw [groupedDigits, if_neg (by simp), insertThousandsGrouping, hl.gr]
    have e : max 0 m = 0 := by omega
    have e2 : ((a :: t).reverse.length : Int) = (a :: t).length := by simp
    rw [e2] at h1
    simpa [e] using h1

theorem mem_tw {p : Nat → Bool} {l : List Nat} {c : Nat} (h : c ∈ l.takeWhile p) : p c = true := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    simp only [List.takeWhile_cons] at h
    split at h
    · rename_i hp
      rcases List.mem_cons.1 h with rfl | h
      · exact hp
      · exact ih h
    · simp at h

theorem filter_takeWhile_all (l : Str) : ∀ c ∈ l.takeWhile pyDigit, noSep c = true := fun _ hc =>
  pyDigit_noSep (mem_tw hc)

theorem slow_grouped (buf : Str) (g : FormatSpec) (loc : LocaleFull)
    (hloc : localeInfoFull (if g.type == 110 then LT_CURRENT_LOCALE else g.thousands) g.fracThousands = loc)
    (hl : GLoc loc) (h1 : g.sign ≠ 43) (h2 : g.sign ≠ 32) (hw : g.width = -1) :
    ∃ s, formatFloatSlow buf g = .ok s ∧ ungroup s = ungroup buf := by
  have hj := sign_join buf g.sign h1 h2
  simp only [formatFloatSlow, hloc]
  generalize hsp : splitSign buf = sb at hj
  obtain ⟨sc, body⟩ := sb
  simp only at hj ⊢
  simp only [splitNumber_eq]
  have hjoin := splitNumber_join body
  generalize hdg : body.takeWhile pyDigit = digits at hjoin
  have hdn : ∀ c ∈ digits, noSep c = true := hdg ▸ filter_takeWhile_all body
  generalize hhd : ((body.dropWhile pyDigit).head? == some 46) = hd at hjoin
  have hfn : ∀ c ∈ (restOf body).takeWhile pyDigit, noSep c = true := filter_takeWhile_all _
  generalize (restOf body).takeWhile pyDigit = frac at hjoin hfn
  generalize (restOf body).dropWhile pyDigit = rem at hjoin
  obtain ⟨nF, fg, hF, hfg⟩ := gf_filter hl frac hfn
  generalize hnd : nonDigitOf (signField g.sign sc) (if hd = true then loc.decimal else []) frac rem = nd
  have hndv : nd = (signField g.sign sc).toList.length + (if hd = true then loc.decimal else []).length +
      frac.length + rem.length := by rw [← hnd, nonDigitOf]
  have hm : minWidthOf g nd frac.length nF ≤ 0 := by
    unfold minWidthOf
    split <;> omega
  obtain ⟨nG, gs, it, hG, hgs⟩ := gd_filter hl digits _ hm hdn
  have hG' : groupedDigits digits (minWidthOf g (nonDigitOf (signField g.sign sc)
      (if hd = true then loc.decimal else []) frac rem) frac.length nF) loc = .ok (nG, gs, it) := by
    rw [hnd]; exact hG
  rw [calc_ok hF hG', hnd]
  have hpad : padFields (g.width - (nd + nG + nF - frac.length)) g.align = (0, 0, 0) :=
    padFields_nonpos _ _ (by omega)
  simp only [bind, Except.bind, fillNumberFull, hpad]
  refine ⟨_, rfl, ?_⟩
  have hdec : (if hd = true then loc.decimal else []) = (if hd = true then ([46] : Str) else []) := by
    rw [hl.dec]
  rw [← hj, ← hjoin]
  simp only [ungroup, hdec, List.replicate_zero, List.nil_append, List.append_nil, List.filter_append, hgs, hfg,
    filter_all_true hdn, filter_all_true hfn, List.append_assoc]

/-- A separator does nothing but separate. For every float and every spec of the fast path,
adding `,` or `_` to the integer part, the fraction or both gives the same text once the
separators are taken out. That includes `format(x, '.3_f')` alone, where the fraction groups and
the integer loop runs with an empty separator. -/
def FloatGroupingOnlyInserts : Prop :=
  ∀ (x : F64) (f : FormatSpec) (t u : Nat), (t = 0 ∨ t = 44 ∨ t = 95) → (u = 0 ∨ u = 44 ∨ u = 95) →
    floatFastPath f = true →
    (formatFloatInternal x { f with thousands := t, fracThousands := u } >>= fun s => .ok (ungroup s)) =
      (formatFloatInternal x f >>= fun s => (.ok (ungroup s) : Py Str))

theorem floatGroupingOnlyInserts_proven : FloatGroupingOnlyInserts := by
  intro x f t u ht hu hf
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := floatFastPath_facts hf
  by_cases hz : t = 0 ∧ u = 0
  · obtain ⟨rfl, rfl⟩ := hz
    have : ({ f with thousands := 0, fracThousands := 0 } : FormatSpec) = f := by
      cases f
      simp_all [LT_NO_LOCALE]
    rw [this]
  · have hg : floatFastPath { f with thousands := t, fracThousands := u } = false := by
      apply Bool.eq_false_iff.2
      intro h
      obtain ⟨-, -, -, -, g5, g6⟩ := floatFastPath_facts h
      exact hz ⟨g5, g6⟩
    have hb : floatBuf x { f with thousands := t, fracThousands := u } = floatBuf x f := rfl
    have ht110 : (f.type == 110) = false := beq_eq_false_iff_ne.2 h4
    by_cases hp : f.precision > 2 ^ 31 - 1
    · have hq : ({ f with thousands := t, fracThousands := u } : FormatSpec).precision > 2 ^ 31 - 1 := hp
      rw [formatFloatInternal, formatFloatInternal, if_pos hp, if_pos hq]
    · have hq : ¬ ({ f with thousands := t, fracThousands := u } : FormatSpec).precision > 2 ^ 31 - 1 := hp
      rw [formatFloatInternal, formatFloatInternal, if_neg hp, if_neg hq, hb]
      cases floatBuf x f with
      | error e => rfl
      | ok buf =>
        obtain ⟨s, hs, hu'⟩ := slow_grouped buf { f with thousands := t, fracThousands := u }
          (localeInfoFull t u) (by simp [ht110]) (gloc_of t u ht hu hz) h1 h2 h3
        simp only [bind, Except.bind, hf, hg, if_true, Bool.false_eq_true, if_false, hs, hu']

/-! ## What `Py_DTSF_SIGN` adds -/

/-- The pieces of `format_float_short` after the sign, for a finite value: left, middle, right,
exponent. None of them reads `fl.sign`. -/
def fssParts (out : DtoaOut) (code : Nat) (precision : Int) (fl : DtsFlags) (upper : Bool) :
    List Piece × List Piece × List Piece × List Piece :=
  let digits := out.digits
  let digits_len : Int := digits.length
  let decpt0 := out.decpt
  let vend0 : Int := digits_len
  let (use_exp, vend1) : Bool × Int :=
    if code == 101 then (true, precision)
    else if code == 102 then (false, decpt0 + precision)
    else if code == 103 then
      (decide (decpt0 ≤ -4) ||
        decide ((if fl.add_dot_0 then precision - 1 else precision) < decpt0),
        if fl.alt then precision else vend0)
    else (decide (decpt0 ≤ -4) || decide (16 < decpt0), vend0)
  let (exp, decpt) : Int × Int := if use_exp then (decpt0 - 1, 1) else (0, decpt0)
  let vstart : Int := if decpt ≤ 0 then decpt - 1 else 0
  let vend : Int :=
    if !use_exp && fl.add_dot_0 then (if decpt < vend1 then vend1 else decpt + 1)
    else (if decpt < vend1 then vend1 else decpt)
  let leftP : List Piece :=
    if decpt ≤ 0 then
      [.zeros (decpt - vstart).toNat, .chars [46], .zeros (0 - decpt).toNat]
    else [.zeros (0 - vstart).toNat]
  let midP : List Piece :=
    if 0 < decpt && decpt ≤ digits_len then
      [.chars (digits.take decpt.toNat), .chars [46], .chars (digits.drop decpt.toNat)]
    else [.chars digits]
  let rightP : List Piece :=
    if digits_len < decpt then
      [.zeros (decpt - digits_len).toNat, .chars [46], .zeros (vend - decpt).toNat]
    else [.zeros (vend - digits_len).toNat]
  let expP : List Piece :=
    if use_exp then [.chars ((if upper then 69 else 101) :: fmtExp exp)] else []
  (leftP, midP, rightP, expP)

/-- `sign1` of `format_float_short`. -/
def fssSign1 (out : DtoaOut) (fl : DtsFlags) : Bool :=
  let digits_len : Int := out.digits.length
  if fl.no_neg_0 && out.sign && (digits_len == 0 || (digits_len == 1 && out.digits.head? == some 48))
  then false else out.sign

/-- The special-value test of `format_float_short`. -/
def fssGuard (out : DtoaOut) : Bool :=
  (out.digits.length : Int) != 0 && !Binary64.isDigit (out.digits.headD 0)

/-- `format_float_short` for a `dtoa` result, with `signP` standing for the sign. -/
def fssCase (out : DtoaOut) (code : Nat) (precision : Int) (fl : DtsFlags) (upper : Bool) :
    Option (List Piece × DtsType) :=
  let d0c := out.digits.headD 0
  let sign1 := fssSign1 out fl
  if fssGuard out then
    let sign2 := if d0c == 78 || d0c == 110 then false else sign1
    let pre : List Nat := if sign2 then [45] else if fl.sign then [43] else []
    if d0c == 73 || d0c == 105 then
      some ([.chars (pre ++ (if upper then [73, 78, 70] else [105, 110, 102]))], .infinite)
    else
      some ([.chars (pre ++ (if upper then [78, 65, 78] else [110, 97, 110]))], .nan)
  else
    let parts := fssParts out code precision fl upper
    let signP : List Piece :=
      if sign1 then [.chars [45]] else if fl.sign then [.chars [43]] else []
    let body := signP ++ parts.1 ++ parts.2.1 ++ parts.2.2.1
    let body' := if fl.alt then body else format_float_short.dropDot body
    some (body' ++ parts.2.2.2, .finite)

theorem fss_eq (d : F64) (code mode : Nat) (prec : Int) (fl : DtsFlags) (upper : Bool) :
    format_float_short d code mode prec fl upper =
      match _Py_dg_dtoa d mode prec with
      | none => none
      | some out => fssCase out code prec fl upper := by
  unfold format_float_short
  cases _Py_dg_dtoa d mode prec with
  | none => rfl
  | some out => rfl

theorem parts_flags (out : DtoaOut) (code : Nat) (prec : Int) (s : Bool) (upper : Bool) :
    fssParts out code prec { sign := s } upper = fssParts out code prec {} upper := rfl

theorem parts_form (out : DtoaOut) (code : Nat) (prec : Int) (fl : DtsFlags) (upper : Bool) :
    ∃ (decpt vstart vend exp : Int) (use_exp : Bool),
      fssParts out code prec fl upper =
        ((if decpt ≤ 0 then
            [.zeros (decpt - vstart).toNat, .chars [46], .zeros (0 - decpt).toNat]
          else [.zeros (0 - vstart).toNat]),
         (if 0 < decpt && decpt ≤ (out.digits.length : Int) then
            [.chars (out.digits.take decpt.toNat), .chars [46], .chars (out.digits.drop decpt.toNat)]
          else [.chars out.digits]),
         (if (out.digits.length : Int) < decpt then
            [.zeros (decpt - (out.digits.length : Int)).toNat, .chars [46], .zeros (vend - decpt).toNat]
          else [.zeros (vend - (out.digits.length : Int)).toNat]),
         (if use_exp then [.chars ((if upper then 69 else 101) :: fmtExp exp)] else [])) := by
  unfold fssParts
  extract_lets digits digits_len decpt0 vend0
  split
  rename_i use_exp vend1 _
  split
  rename_i exp decpt _
  exact ⟨decpt, _, _, exp, use_exp, rfl⟩

/-- Every piece after the sign avoids `c`, for a `c` that is no digit, point or `e`. -/
theorem parts_nh {c : Nat} (c46 : c ≠ 46) (c48 : c ≠ 48) (c69 : c ≠ 69) (c101 : c ≠ 101)
    (hd : Binary64.isDigit c = false) (out : DtoaOut) (code : Nat) (prec : Int) (fl : DtsFlags)
    (upper : Bool) (hg : ¬ fssGuard out = true) :
    NH c (render (fssParts out code prec fl upper).1) ∧
      NH c (render (fssParts out code prec fl upper).2.1) ∧
      NH c (render (fssParts out code prec fl upper).2.2.1) ∧
      NH c (render (fssParts out code prec fl upper).2.2.2) := by
  have hdig : NH c out.digits := digits_nh hd hg
  obtain ⟨decpt, vstart, vend, exp, use_exp, h⟩ := parts_form out code prec fl upper
  rw [h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only
    split
    · simp only [render, List.map_cons, List.map_nil, Piece.render, List.flatten_cons,
        List.flatten_nil, List.append_nil]
      exact nh_dot _ c46 (nh_repl _ c48)
    · simpa [render, Piece.render] using nh_repl _ c48
  · simp only
    split
    · simp only [render, List.map_cons, List.map_nil, Piece.render, List.flatten_cons,
        List.flatten_nil, List.append_nil]
      exact nh_dot _ c46 (nh_take _ hdig)
    · simpa [render, Piece.render] using hdig
  · simp only
    split
    · simp only [render, List.map_cons, List.map_nil, Piece.render, List.flatten_cons,
        List.flatten_nil, List.append_nil]
      exact nh_dot _ c46 (nh_repl _ c48)
    · simpa [render, Piece.render] using nh_repl _ c48
  · simp only
    split
    · simp only [render, List.map_cons, List.map_nil, Piece.render, List.flatten_cons,
        List.flatten_nil, List.append_nil]
      split
      · exact nh_cons _ (Ne.symm c69)
      · exact nh_cons _ (Ne.symm c101)
    · exact nh_nil c

theorem dd_cons {x : Nat} (hx : x ≠ 46) (R : Str) : dd (x :: R) = x :: dd R := by
  cases R with
  | nil =>
    have : (some x == some 46) = false := by simpa using hx
    simp [dd, this]
  | cons a t =>
    have e1 : (x :: a :: t).getLast? = (a :: t).getLast? := by simp
    have e2 : (x :: a :: t).dropLast = x :: (a :: t).dropLast := rfl
    unfold dd
    rw [e1, e2]
    split <;> rfl

/-- What `Py_DTSF_SIGN` adds to a buffer: a `+` unless it starts with `-`. -/
def plusSign (b : Str) : Str := if b.headD 0 == 45 then b else 43 :: b

theorem plusSign_nh {b : Str} (h : NH 45 b) : plusSign b = 43 :: b := by
  have : (b.headD 0 == 45) = false := by
    cases b with
    | nil => rfl
    | cons a t =>
      have ha : a ≠ 45 := by
        intro e
        apply h
        simp [e]
      exact beq_eq_false_iff_ne.2 ha
  simp only [plusSign, this, Bool.false_eq_true, if_false]

/-- `Py_DTSF_SIGN` changes nothing but the first character, for every value, `nan` included. -/
theorem fss_sign (d : F64) (code mode : Nat) (prec : Int) (upper : Bool) :
    (format_float_short d code mode prec { sign := true } upper).map (fun r => render r.1) =
      (format_float_short d code mode prec {} upper).map (fun r => plusSign (render r.1)) := by
  rw [fss_eq, fss_eq]
  cases _Py_dg_dtoa d mode prec with
  | none => rfl
  | some out =>
    simp only [fssCase]
    have hS : fssSign1 out { sign := true } = fssSign1 out {} := rfl
    rw [hS]
    generalize hs1 : fssSign1 out {} = S
    by_cases hg : fssGuard out = true
    · simp only [hg, if_true]
      generalize out.digits.headD 0 = d0
      cases upper <;> cases hsg : (if (d0 == 78 || d0 == 110) = true then false else S) <;>
        split <;> split <;> simp [render, Piece.render, plusSign]
    · simp only [hg, Bool.false_eq_true, if_false, parts_flags]
      generalize hP : fssParts out code prec {} upper = P
      obtain ⟨l, m, r, e⟩ := P
      have hn := parts_nh (c := 45) (by decide) (by decide) (by decide) (by decide) (by decide) out code prec {}
        upper hg
      rw [hP] at hn
      obtain ⟨n1, n2, n3, n4⟩ := hn
      have hR : NH 45 (render (l ++ m ++ r)) := by
        simp only [render_append]
        exact nh_append (nh_append n1 n2) n3
      have a0 : render (([] : List Piece) ++ l ++ m ++ r) = render l ++ render m ++ render r := by
        simp [render]
      have a1 : render (([Piece.chars [43]] : List Piece) ++ l ++ m ++ r) =
          43 :: (render l ++ render m ++ render r) := by simp [render, Piece.render]
      have a2 : render (([Piece.chars [45]] : List Piece) ++ l ++ m ++ r) =
          45 :: (render l ++ render m ++ render r) := by simp [render, Piece.render]
      simp only [render_append] at hR
      cases S
      · show some (render (format_float_short.dropDot ([Piece.chars [43]] ++ l ++ m ++ r) ++ e)) =
          some (plusSign (render (format_float_short.dropDot ([] ++ l ++ m ++ r) ++ e)))
        rw [render_append, render_append, render_dropDot, render_dropDot, a1, a0,
          dd_cons (by decide), plusSign_nh (nh_append (nh_dd hR) n4)]
        rfl
      · show some (render (format_float_short.dropDot ([Piece.chars [45]] ++ l ++ m ++ r) ++ e)) =
          some (plusSign (render (format_float_short.dropDot ([Piece.chars [45]] ++ l ++ m ++ r) ++ e)))
        rw [render_append, render_dropDot, a2, dd_cons (by decide)]
        simp [plusSign]

/-! ## `complex` -/

/-- A successful `format_float_internal` with no width is the general path on its buffer, which
is what `format_complex_internal` runs on each part. -/
theorem ok_slow {x : F64} {g : FormatSpec} {s : Str} (hw : g.width = -1)
    (h : formatFloatInternal x g = .ok s) :
    ¬ g.precision > 2 ^ 31 - 1 ∧ ∃ buf, floatBuf x g = .ok buf ∧ formatFloatSlow buf g = .ok s := by
  rw [formatFloatInternal] at h
  split at h
  · cases h
  · rename_i hp
    refine ⟨hp, ?_⟩
    cases hb : floatBuf x g with
    | error e =>
      rw [hb] at h
      cases h
    | ok buf =>
      rw [hb] at h
      simp only [bind, Except.bind] at h
      refine ⟨buf, rfl, ?_⟩
      split at h
      · rename_i hf
        obtain ⟨g1, g2, -, -, g5, g6⟩ := floatFastPath_facts hf
        rw [slow_plain buf g g5 g6, layout_self buf g g1 g2 (by omega)]
        exact h
      · exact h

/-- The buffer `format_float_internal` asks for, for a type that is neither absent nor `%`. -/
theorem floatBuf_typed (x : F64) (f : FormatSpec) (h0 : f.type ≠ 0) (h37 : f.type ≠ 37) :
    floatBuf x f = doubleToString x
      (if f.precision < 0 then (if f.type == 110 then 103 else f.type)
       else if (if f.type == 110 then 103 else f.type) == 114 then 103
       else (if f.type == 110 then 103 else f.type))
      (if f.precision < 0 then 6 else f.precision)
      { alt := f.alternate, no_neg_0 := f.noNeg0 } := by
  have a0 : (f.type == 0) = false := beq_eq_false_iff_ne.2 h0
  have a37 : (f.type == 37) = false := beq_eq_false_iff_ne.2 h37
  have e103 : ((103 : Nat) == 37) = false := rfl
  have e114 : ((103 : Nat) == 114) = false := rfl
  by_cases h110 : f.type = 110
  · have a110 : (f.type == 110) = true := beq_iff_eq.2 h110
    by_cases hp : f.precision < 0
    · simp only [floatBuf, a0, a110, e103, Bool.false_eq_true, if_false, if_true, if_pos hp]
      generalize doubleToString _ _ _ _ = y
      cases y <;> rfl
    · simp only [floatBuf, a0, a110, e103, e114, Bool.false_eq_true, if_false, if_true, if_neg hp]
      generalize doubleToString _ _ _ _ = y
      cases y <;> rfl
  · have a110 : (f.type == 110) = false := beq_eq_false_iff_ne.2 h110
    by_cases hp : f.precision < 0
    · simp only [floatBuf, a0, a110, a37, Bool.false_eq_true, if_false, if_pos hp]
      generalize doubleToString _ _ _ _ = y
      cases y <;> rfl
    · simp only [floatBuf, a0, a110, a37, Bool.false_eq_true, if_false, if_neg hp]
      generalize doubleToString _ _ _ _ = y
      cases y <;> rfl

/-- The padded form of `format_complex_internal`. -/
def complexPad (content : Str) (f : FormatSpec) : Str :=
  let (l, r, _) := calcPadding content.length f.width f.align
  fillPadding content f.fillChar l r

/-- With a presentation type, a complex is its two parts formatted as floats, the imaginary part
with a forced sign, then `j`, then the padding. `0` fill and `=` are the two options the
function refuses, and `%` is refused by the dispatcher. `format(z, '.3f')` is
`format(z.real, '.3f') + format(z.imag, '+.3f') + 'j'`, separators included. It is stated for
parts that format successfully, because the only failure either side can have under these
hypotheses is the model's own fuel, which is no Python outcome. -/
def ComplexPartsCompose : Prop :=
  ∀ (re im : F64) (f : FormatSpec) (a b : Str), f.type ≠ 0 → f.type ≠ 37 → f.fillChar ≠ 48 →
    f.align ≠ 61 →
    formatFloatInternal re { f with fillChar := 0, align := 60, width := -1 } = .ok a →
    formatFloatInternal im { f with fillChar := 0, align := 60, width := -1, sign := 43 } = .ok b →
    formatComplexInternal re im f = .ok (complexPad (a ++ b ++ [106]) f)

theorem complexPartsCompose_proven : ComplexPartsCompose := by
  intro re im f a b h0 h37 hfill halign ha hb
  obtain ⟨hp, bufA, hbA, hsA⟩ := ok_slow rfl ha
  obtain ⟨-, bufB, hbB, hsB⟩ := ok_slow rfl hb
  have hbA' := hbA
  have hbB' := hbB
  have eA : floatBuf re { f with fillChar := 0, align := 60, width := -1 } = floatBuf re f := rfl
  have eB : floatBuf im { f with fillChar := 0, align := 60, width := -1, sign := 43 } = floatBuf im f := rfl
  rw [eA, floatBuf_typed _ _ h0 h37] at hbA'
  rw [eB, floatBuf_typed _ _ h0 h37] at hbB'
  have a0 : (f.type == 0) = false := beq_eq_false_iff_ne.2 h0
  have a1 : (f.fillChar == 48) = false := beq_eq_false_iff_ne.2 hfill
  have a2 : (f.align == 61) = false := beq_eq_false_iff_ne.2 halign
  have hp' : ¬ f.precision > 2 ^ 31 - 1 := hp
  rw [formatComplexInternal, if_neg hp']
  simp only [a0, a1, a2, Bool.false_eq_true, if_false]
  simp only [bind, Except.bind, hbA', hbB', complexRest, hsA, hsB, Bool.false_eq_true, if_false]
  simp [complexPad]

theorem calcPadding_len (n : Nat) (w : Int) (a : Nat) :
    w ≤ (calcPadding n w a).1 + n + (calcPadding n w a).2.1 := by
  simp only [calcPadding]
  generalize hT : (if w ≥ 0 then (if (n : Int) > w then n else w.toNat) else n) = T
  have h1 : n ≤ T := by
    subst hT
    split
    · split <;> omega
    · omega
  have h2 : w ≤ T := by
    subst hT
    split
    · split <;> omega
    · omega
  split
  · omega
  · split <;> omega

theorem pad_width (c : Str) (f : FormatSpec) : f.width ≤ (complexPad c f).length := by
  have h := calcPadding_len c.length f.width f.align
  simp only [complexPad]
  generalize calcPadding c.length f.width f.align = P at h
  obtain ⟨l, r, x⟩ := P
  simp only [fillPadding, List.length_append, List.length_replicate] at h ⊢
  omega

theorem pad_none (c : Str) (f : FormatSpec) (hw : f.width = -1) : complexPad c f = c := by
  simp [complexPad, calcPadding, hw, fillPadding]

theorem complexRest_width {a b : Str} {f : FormatSpec} {sk ad : Bool} {s : Str}
    (h : complexRest a b f sk ad = .ok s) : f.width ≤ s.length := by
  simp only [complexRest, bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [Except.ok.injEq] at h
      subst h
      exact pad_width _ f

/-- The width is a minimum for a complex too, for every value and every spec. -/
def ComplexWidthIsMinimum : Prop :=
  ∀ (re im : F64) (f : FormatSpec) (s : Str), formatComplexInternal re im f = .ok s →
    f.width ≤ s.length

theorem complexWidthIsMinimum_proven : ComplexWidthIsMinimum := by
  intro re im f s h
  rw [formatComplexInternal] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · simp only [bind, Except.bind] at h
        split at h
        · cases h
        · split at h
          · cases h
          · exact complexRest_width h

theorem slow_plus (buf : Str) (g : FormatSpec) (h1 : g.thousands = LT_NO_LOCALE)
    (h2 : g.fracThousands = LT_NO_LOCALE) (hs : g.sign = 43) (hw : g.width = -1) :
    formatFloatSlow buf g = .ok (plusSign buf) := by
  rw [slow_plain buf g h1 h2]
  simp only [floatLayout, layoutOf, hs, hw]
  rw [padFields_nonpos _ _ (by omega)]
  cases buf with
  | nil => simp [splitSign, signField, plusSign]
  | cons a t =>
    by_cases ha : a = 45
    · subst ha
      simp [splitSign, signField, plusSign]
    · have : (a == 45) = false := beq_eq_false_iff_ne.2 ha
      simp [splitSign, signField, plusSign, this]

theorem dts_ok {x : F64} {code : Nat} {prec : Int} {fl : DtsFlags} {buf : Str}
    (h : doubleToString x code prec fl = .ok buf) :
    ∃ r, PyOS_double_to_string x code prec fl = some r ∧ render r.1 = buf := by
  unfold doubleToString at h
  split at h
  · cases h
  · rename_i r hr
    exact ⟨r, hr, by simpa using h⟩

/-- `format(z, '<')` and the other specs with no type, no precision and no option are `str(z)`:
two implementations of the same rule, down to when the real part is dropped and when the
parentheses appear. They are compared where both give a result, because the only failure either
can have is the model's own fuel, which is no Python outcome. -/
def ComplexOmittedTypeIsRepr : Prop :=
  ∀ (re im : F64) (f : FormatSpec) (s r : Str), f.type = 0 → f.precision < 0 →
    f.alternate = false → f.noNeg0 = false → f.thousands = LT_NO_LOCALE →
    f.fracThousands = LT_NO_LOCALE → f.sign ≠ 43 → f.sign ≠ 32 → f.width = -1 →
    formatComplexInternal re im f = .ok s → complex_repr ⟨re, im⟩ = some r → s = r

theorem rest_skip (reB imB : Str) (f : FormatSpec) (h1 : f.thousands = LT_NO_LOCALE)
    (h2 : f.fracThousands = LT_NO_LOCALE) (h3 : f.sign ≠ 43) (h4 : f.sign ≠ 32) (hw : f.width = -1) :
    complexRest reB imB f true false = .ok (imB ++ [106]) := by
  have s1 := slow_plain reB { f with fillChar := 0, align := 60, width := -1 } h1 h2
  have s2 := slow_plain imB { f with fillChar := 0, align := 60, width := -1 } h1 h2
  rw [layout_self reB { f with fillChar := 0, align := 60, width := -1 } h3 h4 (by simp)] at s1
  rw [layout_self imB { f with fillChar := 0, align := 60, width := -1 } h3 h4 (by simp)] at s2
  simp only [complexRest, bind, Except.bind, if_true, s1, s2, Bool.false_eq_true, if_false]
  have := pad_none (imB ++ [106]) f hw
  simpa [complexPad] using this

theorem rest_parens (reB imB : Str) (f : FormatSpec) (h1 : f.thousands = LT_NO_LOCALE)
    (h2 : f.fracThousands = LT_NO_LOCALE) (h3 : f.sign ≠ 43) (h4 : f.sign ≠ 32) (hw : f.width = -1) :
    complexRest reB imB f false true = .ok (40 :: reB ++ plusSign imB ++ [106, 41]) := by
  have s1 := slow_plain reB { f with fillChar := 0, align := 60, width := -1 } h1 h2
  rw [layout_self reB { f with fillChar := 0, align := 60, width := -1 } h3 h4 (by simp)] at s1
  have s2 := slow_plus imB { f with fillChar := 0, align := 60, width := -1, sign := 43 } h1 h2 rfl rfl
  simp only [complexRest, bind, Except.bind, if_true, s1, s2, Bool.false_eq_true, if_false]
  have := pad_none ([40] ++ reB ++ plusSign imB ++ [106] ++ [41]) f hw
  simpa [complexPad] using this

theorem dts_repr_sign (x : F64) :
    (PyOS_double_to_string x 114 0 { sign := true }).map (fun r => render r.1) =
      (PyOS_double_to_string x 114 0 {}).map (fun r => plusSign (render r.1)) :=
  fss_sign x 114 0 0 false

theorem complexOmittedTypeIsRepr_proven : ComplexOmittedTypeIsRepr := by
  intro re im f s r h0 hp ha hz h1 h2 h3 h4 hw h hr
  have hpr : ¬ f.precision > 2 ^ 31 - 1 := by omega
  rw [formatComplexInternal, if_neg hpr] at h
  by_cases hfill : (f.fillChar == 48) = true
  · simp [hfill] at h
  by_cases halign : (f.align == 61) = true
  · simp [hfill, halign] at h
  have a0 : (f.type == 0) = true := beq_iff_eq.2 h0
  have ez : ({ alt := f.alternate, no_neg_0 := f.noNeg0 } : DtsFlags) = {} := by simp [ha, hz]
  simp only [hfill, halign, a0, Bool.false_eq_true, if_false, if_true, if_pos hp, ez,
    bind, Except.bind] at h
  simp only [complex_repr] at hr
  by_cases hs : (F64.eq re d0 && !re.sign) = true
  · simp only [hs, if_true] at h hr
    split at h
    · cases h
    · rename_i reB hre
      split at h
      · cases h
      · rename_i imB him
        rw [rest_skip reB imB f h1 h2 h3 h4 hw] at h
        simp only [Except.ok.injEq] at h
        obtain ⟨q, hq, hrq⟩ := dts_ok (show doubleToString im 114 0 {} = .ok imB from him)
        rw [hq] at hr
        simp only [Option.map_some, Option.some.injEq] at hr
        rw [← h, ← hr, hrq]
  · have hs' : (F64.eq re d0 && !re.sign) = false := by simpa using hs
    simp only [hs', Bool.false_eq_true, if_false] at h hr
    split at h
    · cases h
    · rename_i reB hre
      split at h
      · cases h
      · rename_i imB him
        rw [rest_parens reB imB f h1 h2 h3 h4 hw] at h
        simp only [Except.ok.injEq] at h
        obtain ⟨q1, hq1, hrq1⟩ := dts_ok (show doubleToString re 114 0 {} = .ok reB from hre)
        obtain ⟨q2, hq2, hrq2⟩ := dts_ok (show doubleToString im 114 0 {} = .ok imB from him)
        have hsg := dts_repr_sign im
        rw [hq2] at hsg
        simp only [hq1] at hr
        split at hr
        · rename_i pre imr h5 h6
          simp only [Option.some.injEq] at h5 hr
          subst h5
          rw [h6] at hsg
          simp only [Option.map_some, Option.some.injEq] at hsg
          rw [← h, ← hr, hsg, hrq1, hrq2]
        · cases hr

/-! ## The width for an `int` -/

theorem insert_len {ds : Str} {m : Int} {g sep : List Nat} {n it : Nat} {o : Str}
    (h : insertThousandsGrouping ds m g sep = .ok (n, o, it)) : o.length = n := by
  unfold insertThousandsGrouping at h
  have := groupLoop_count _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h (by simp)
  simpa using this

/-- `calc_number_widths` with a prefix: the fields add up to at least the width. -/
theorem calcInt_width {nPrefix sc : Nat} {ds : Str} {nRem : Nat} {sep g : List Nat} {f : FormatSpec}
    {l s r : Nat} {sg : Option Nat} {text : Str}
    (h : calcNumberWidths nPrefix sc ds nRem sep g f = .ok (l, sg, s, r, text)) :
    f.width ≤ (l : Int) + sg.toList.length + nPrefix + s + text.length + nRem + r := by
  unfold calcNumberWidths at h
  generalize hns : (if f.sign == 43 then ((1 : Nat), some (if sc == 45 then 45 else 43))
    else if f.sign == 32 then (1, some (if sc == 45 then 45 else 32))
    else if sc == 45 then (1, some 45) else (0, none)) = ns at h
  obtain ⟨nSign, sign⟩ := ns
  have hlen : sign.toList.length = nSign := by
    revert hns
    split
    · intro e
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      rfl
    · split
      · intro e
        simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        rfl
      · split <;>
        · intro e
          simp only [Prod.mk.injEq] at e
          obtain ⟨rfl, rfl⟩ := e
          rfl
  simp only [bind, Except.bind, pure, Except.pure] at h
  have key : ∀ (nG : Nat) (tx : Str), tx.length = nG →
      (let nPadding := f.width - ((nSign : Int) + nPrefix + nRem + nG)
       let lsr : Nat × Nat × Nat := if nPadding > 0 then
          (if f.align == 60 then (0, 0, nPadding.toNat)
           else if f.align == 94 then (nPadding.toNat / 2, 0, nPadding.toNat - nPadding.toNat / 2)
           else if f.align == 61 then (0, nPadding.toNat, 0) else (nPadding.toNat, 0, 0))
          else (0, 0, 0)
       f.width ≤ (lsr.1 : Int) + nSign + nPrefix + lsr.2.1 + nG + nRem + lsr.2.2) := by
    intro nG tx _
    simp only
    split
    · repeat' split
      all_goals simp only
      all_goals omega
    · simp only
      omega
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    have := key 0 [] rfl
    simpa [hlen] using this
  · split at h
    · cases h
    · rename_i v hv
      obtain ⟨nG, o, it⟩ := v
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      have hl := insert_len hv
      have := key nG o hl
      simpa [hlen, hl] using this

theorem fillNumber_len (l : Nat) (sign : Option Nat) (pfx : Str) (s : Nat) (text rem : Str)
    (r fill : Nat) (up : Bool) :
    (fillNumber l sign pfx s text rem r fill up).length =
      l + sign.toList.length + pfx.length + s + text.length + rem.length + r := by
  simp only [fillNumber]
  cases up <;> simp <;> omega

/-- The prefix `format_long_internal` keeps is as long as it says. -/
theorem prefix_len {v : Int} {base skip : Nat} {tmp : Str}
    (hb : (base = 2 ∧ skip = 2) ∨ (base = 8 ∧ skip = 2) ∨ (base = 16 ∧ skip = 2) ∨ (base = 10 ∧ skip = 0))
    (h : longFormat v base = .ok tmp) :
    skip ≤ (if tmp.head? == some 45 then ((45 : Nat), tmp.tail) else (0, tmp)).2.length := by
  rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals first
    | exact Nat.zero_le _
    | (simp only [longFormat] at h
       simp at h
       subst h
       by_cases hv : v < 0 <;> simp [hv])

theorem longSlow_width {v : Int} {f : FormatSpec} {base skip : Nat} {s : Str}
    (hb : (base = 2 ∧ skip = 2) ∨ (base = 8 ∧ skip = 2) ∨ (base = 16 ∧ skip = 2) ∨ (base = 10 ∧ skip = 0))
    (h : formatLongSlow v f base skip = .ok s) : f.width ≤ s.length := by
  simp only [formatLongSlow, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i tmp hl
    have hp := prefix_len hb hl
    generalize (if tmp.head? == some 45 then ((45 : Nat), tmp.tail) else (0, tmp)) = st at h hp
    obtain ⟨sc, tmp1⟩ := st
    simp only at h hp
    split at h
    · cases h
    · rename_i fields hc
      obtain ⟨l, sg, sp, r, text⟩ := fields
      simp only [Except.ok.injEq] at h
      subst h
      have hw := calcInt_width hc
      have hpfx : (tmp1.take (if f.alternate = true then skip else 0)).length =
          (if f.alternate = true then skip else 0) := by
        rw [List.length_take]
        split <;> omega
      rw [fillNumber_len, hpfx]
      simp only [List.length_nil]
      omega

/-- `format()` of an int honours the width as a minimum, on the prefix path of `#x` and on the
`c` type, for every int and every spec. -/
def IntWidthIsMinimum : Prop :=
  ∀ (v : Int) (f : FormatSpec) (exact : Bool) (s : Str),
    formatLongInternal v f exact = .ok s → f.width ≤ s.length

theorem intWidthIsMinimum_proven : IntWidthIsMinimum := by
  intro v f exact s h
  unfold formatLongInternal at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i fields hc
      obtain ⟨l, sg, sp, r, text⟩ := fields
      simp only [Except.ok.injEq] at h
      subst h
      have hw := calcInt_width hc
      rw [fillNumber_len]
      simp only [List.length_nil, List.length_cons]
      omega
  · generalize hbs : (if f.type == 98 then ((2 : Nat), (2 : Nat)) else if f.type == 111 then (8, 2)
      else if f.type == 120 || f.type == 88 then (16, 2) else (10, 0)) = bs at h
    obtain ⟨base, skip⟩ := bs
    have hb : (base = 2 ∧ skip = 2) ∨ (base = 8 ∧ skip = 2) ∨ (base = 16 ∧ skip = 2) ∨
        (base = 10 ∧ skip = 0) := by
      revert hbs
      split
      · intro e; simp at e; omega
      · split
        · intro e; simp at e; omega
        · split <;> (intro e; simp at e; omega)
    simp only at h
    split at h
    · rename_i hc
      have : f.width = -1 := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact hc.1.1.1.1.2
      omega
    · exact longSlow_width hb h

end PyLean.UnicodeObj
