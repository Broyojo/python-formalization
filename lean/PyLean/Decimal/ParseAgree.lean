import PyLean.Decimal.RoundTrip

/-!
Without the three Unicode case variants, whatever `_pydecimal` parses `_decimal`
parses to the same value: for arbitrary Unicode strings, with Unicode digits,
whitespace and underscores.

`asc` is the per-character map of `numeric_as_ascii`. For a string the regex
accepts, the map produces the ASCII shape `mpd_num` handles.
-/

namespace PyLean.Decimal

open PyLean

/-- The map `numeric_as_ascii` applies to a character it keeps. -/
def asc (c : Char) : Char :=
  if 0 < c.toNat ∧ c.toNat ≤ 127 then c
  else if isSpace c then ' '
  else match digitVal c with
    | some d => Char.ofNat (48 + d)
    | none => c

/-- Characters `numeric_as_ascii` does not reject. -/
def Valid (c : Char) : Prop :=
  (0 < c.toNat ∧ c.toNat ≤ 127) ∨ isSpace c = true ∨ (digitVal c).isSome = true

theorem go_map (L acc : List Char) (h : ∀ c ∈ L, c = '_' ∨ Valid c) :
    numericAsAscii.go acc L = some (acc.reverse ++ (L.filter (· ≠ '_')).map asc) := by
  induction L generalizing acc with
  | nil => simp [numericAsAscii.go]
  | cons x xs ih =>
    have hr : ∀ c ∈ xs, c = '_' ∨ Valid c := fun c hc => h c (by simp [hc])
    by_cases hu : x = '_'
    · subst hu
      have : (('_' : Char) == '_') = true := by decide
      simp only [numericAsAscii.go, this, ↓reduceIte]
      rw [ih _ hr]
      simp
    · have hb : (x == '_') = false := beq_false_of_ne hu
      have hv : Valid x := (h x (by simp)).resolve_left hu
      have hfil : (x :: xs).filter (· ≠ '_') = x :: xs.filter (· ≠ '_') := by simp [hu]
      rw [hfil]
      simp only [numericAsAscii.go, hb, Bool.false_eq_true, ↓reduceIte, List.map_cons]
      by_cases ha : 0 < x.toNat ∧ x.toNat ≤ 127
      · rw [if_pos ha, ih _ hr]
        simp [asc, ha]
      · rw [if_neg ha]
        by_cases hs : isSpace x = true
        · simp only [hs, ↓reduceIte]
          rw [ih _ hr]
          simp [asc, ha, hs]
        · have hd : (digitVal x).isSome = true := by
            rcases hv with h1 | h1 | h1
            · exact absurd h1 ha
            · exact absurd h1 hs
            · exact h1
          obtain ⟨d, hd'⟩ := Option.isSome_iff_exists.mp hd
          simp only [hs, Bool.false_eq_true, ↓reduceIte, hd']
          rw [ih _ hr]
          simp [asc, ha, hs, hd']

/-! ## Facts about the digit table -/

theorem digitVal_some {c : Char} {d : Nat} (h : digitVal c = some d) :
    d < 10 ∧ ∃ z ∈ ndZeros, z ≤ c.toNat ∧ c.toNat ≤ z + 9 ∧ d = c.toNat - z := by
  unfold digitVal at h
  simp only at h
  split at h
  · rename_i z hz
    have hm := List.mem_of_find?_eq_some hz
    have hp := List.find?_some hz
    simp only [decide_eq_true_eq] at hp
    cases h
    exact ⟨by omega, z, hm, hp.1, hp.2, rfl⟩
  · cases h

theorem digit_small {c : Char} {d : Nat} (h : digitVal c = some d) (hn : c.toNat ≤ 127) :
    c.isDigit = true := by
  obtain ⟨_, z, hz, h1, h2, _⟩ := digitVal_some h
  rw [isDigit_iff']
  simp only [ndZeros, List.mem_cons, List.not_mem_nil, or_false] at hz
  omega

theorem digit_not_space {c : Char} {d : Nat} (h : digitVal c = some d) : isSpace c = false := by
  obtain ⟨_, z, hz, h1, h2, _⟩ := digitVal_some h
  cases hs : isSpace c with
  | false => rfl
  | true =>
    exfalso
    simp only [isSpace, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hs
    simp only [ndZeros, List.mem_cons, List.not_mem_nil, or_false] at hz
    omega

/-- `numeric_as_ascii` turns a digit into the ASCII digit of the same value. -/
theorem asc_digit {c : Char} (h : isDigit c = true) :
    (asc c).isDigit = true ∧ digitVal (asc c) = digitVal c := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp h
  by_cases ha : 0 < c.toNat ∧ c.toNat ≤ 127
  · simp only [asc, ha, and_self, ↓reduceIte]
    exact ⟨digit_small hd ha.2, trivial⟩
  · have hs := digit_not_space hd
    have hlt := (digitVal_some hd).1
    simp only [asc, ha, ↓reduceIte, hs, Bool.false_eq_true, hd]
    have hv := digitVal_ascii_aux d hlt
    have hdig : ∀ k, k < 10 → (Char.ofNat (48 + k)).isDigit = true := by decide
    exact ⟨hdig d hlt, hv⟩

theorem digitsValue_map (L : List Char) (h : ∀ c ∈ L, isDigit c = true) (acc : Nat) :
    (L.map asc).foldl (fun acc c => acc * 10 + (digitVal c).getD 0) acc =
      L.foldl (fun acc c => acc * 10 + (digitVal c).getD 0) acc := by
  induction L generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.foldl_cons, (asc_digit (h x (by simp))).2]
    exact ih (fun c hc => h c (by simp [hc])) _

theorem asc_ascii {c : Char} (h : 0 < c.toNat ∧ c.toNat ≤ 127) : asc c = c := by
  simp [asc, h]

theorem asc_AD {L : List Char} (h : ∀ c ∈ L, isDigit c = true) : AD (L.map asc) := by
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  exact (asc_digit (h c hc)).1

/-- A character whose image is `+`, `-`, `.`, `e`, `E` or a letter is that
character: only ASCII stays, and other kept characters become ` ` or digits. -/
theorem asc_eq {c d : Char} (hv : Valid c) (h : asc c = d)
    (h1 : d ≠ ' ') (h2 : d.isDigit = false) : c = d := by
  by_cases ha : 0 < c.toNat ∧ c.toNat ≤ 127
  · rw [asc_ascii ha] at h; exact h
  · exfalso
    rcases hv with h3 | h3 | h3
    · exact ha h3
    · simp only [asc, ha, ↓reduceIte, h3] at h
      exact h1 h.symm
    · have hdig : isDigit c = true := h3
      have := (asc_digit hdig).1
      rw [h, h2] at this
      cases this

/-! ## From the regex groups back to the string -/

theorem expSign_inv {cs : List Char} {n : Bool} {b : List Char} (h : expSign cs = (n, b)) :
    ∃ sg, cs = sg ++ b ∧ (sg = [] ∨ sg = ['+'] ∨ sg = ['-']) ∧ n = decide (sg = ['-']) := by
  unfold expSign at h
  split at h
  · cases h; exact ⟨['-'], rfl, by simp, by simp⟩
  · cases h; exact ⟨['+'], rfl, by simp, by decide⟩
  · cases h; exact ⟨[], rfl, by simp, by decide⟩

/-- An exponent part with Unicode digits. -/
def ExRaw : ExPart → Prop
  | none => True
  | some (ind, sg, D) => (ind = 'e' ∨ ind = 'E') ∧ (sg = [] ∨ sg = ['+'] ∨ sg = ['-']) ∧ D ≠ [] ∧
      ∀ c ∈ D, isDigit c = true

/-- `numeric_as_ascii` on an exponent part. -/
def exAsc : ExPart → ExPart
  | none => none
  | some (ind, sg, D) => some (ind, sg, D.map asc)

theorem matchExpEnd_inv {r2 : List Char} {g : Option (Bool × List Char)} (h : matchExpEnd r2 = some g) :
    ∃ ex, r2 = expPart ex ∧ ExRaw ex ∧ exGroup ex = g := by
  cases r2 with
  | nil =>
    simp only [matchExpEnd, Option.some.injEq] at h
    subst h
    exact ⟨none, rfl, trivial, rfl⟩
  | cons c cs =>
    simp only [matchExpEnd] at h
    split at h
    · rename_i hc
      generalize hs : expSign cs = pr at h
      obtain ⟨eneg, body⟩ := pr
      simp only at h
      split at h
      · rename_i hb
        cases h
        obtain ⟨sg, hcs, hsg, hn⟩ := expSign_inv hs
        have hind : c = 'e' ∨ c = 'E' := by simpa using hc
        refine ⟨some (c, sg, body), by simp [expPart, hcs], ⟨hind, hsg, hb.1, ?_⟩, ?_⟩
        · intro x hx
          exact List.all_eq_true.mp hb.2 x hx
        · simp [exGroup, hn]
      · cases h
    · cases h

theorem mem_takeWhile' {p : Char → Bool} {L : List Char} {c : Char} (h : c ∈ L.takeWhile p) : p c = true := by
  induction L with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.takeWhile_cons] at h
    split at h
    · rename_i hx
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact hx
      · exact ih h
    · simp at h

theorem matchNum_inv {neg neg' : Bool} {b I F : List Char} {g : Option (Bool × List Char)}
    (h : matchNum neg b = some (.num neg' I F g)) :
    ∃ fr ex, b = numBody I fr ++ expPart ex ∧ fr.getD [] = F ∧ ExRaw ex ∧ exGroup ex = g ∧ neg' = neg ∧
      (∀ c ∈ I, isDigit c = true) ∧ (∀ c ∈ F, isDigit c = true) := by
  simp only [matchNum] at h
  have hI : ∀ c ∈ b.takeWhile isDigit, isDigit c = true := fun c hc => mem_takeWhile' hc
  have hb : b = b.takeWhile isDigit ++ b.dropWhile isDigit := (List.takeWhile_append_dropWhile).symm
  generalize hr1 : b.dropWhile isDigit = r1 at *
  generalize hit : b.takeWhile isDigit = I0 at *
  generalize hmf : matchFrac r1 = pr at h
  obtain ⟨f0, r2⟩ := pr
  simp only at h
  cases hm : matchExpEnd r2 with
  | none => rw [hm] at h; cases h
  | some g0 =>
    rw [hm] at h
    simp only [Option.some.injEq, PyMatch.num.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    obtain ⟨ex, hr2, hraw, hgr⟩ := matchExpEnd_inv hm
    cases r1 with
    | nil =>
      simp only [matchFrac, Prod.mk.injEq] at hmf
      obtain ⟨rfl, rfl⟩ := hmf
      refine ⟨none, ex, ?_, rfl, hraw, hgr, rfl, hI, by simp⟩
      simp [numBody, ← hr2, hb]
    | cons x xs =>
      by_cases hx : x = '.'
      · subst hx
        simp only [matchFrac, Prod.mk.injEq] at hmf
        obtain ⟨rfl, rfl⟩ := hmf
        refine ⟨some (xs.takeWhile isDigit), ex, ?_, rfl, hraw, hgr, rfl, hI,
          fun c hc => mem_takeWhile' hc⟩
        rw [hb, ← hr2]
        simp only [numBody, List.append_assoc, List.cons_append]
        rw [List.takeWhile_append_dropWhile]
      · have hmf' : matchFrac (x :: xs) = ([], x :: xs) := by
          unfold matchFrac
          split <;> simp_all
        rw [hmf'] at hmf
        simp only [Prod.mk.injEq] at hmf
        obtain ⟨rfl, rfl⟩ := hmf
        refine ⟨none, ex, ?_, rfl, hraw, hgr, rfl, hI, by simp⟩
        simp [numBody, ← hr2, hb]

/-! ## The numeric branch -/

theorem asc_dot : asc '.' = '.' := by decide

theorem exRaw_ok {ex : ExPart} (h : ExRaw ex) : ExOk (exAsc ex) := by
  cases ex with
  | none => trivial
  | some t =>
    obtain ⟨ind, sg, D⟩ := t
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨h1, h2, by simpa using h3, asc_AD h4⟩

theorem exVal_asc {ex : ExPart} (h : ExRaw ex) : exVal (exAsc ex) = exVal ex := by
  cases ex with
  | none => rfl
  | some t =>
    obtain ⟨ind, sg, D⟩ := t
    have hv : digitsValue (D.map asc) = digitsValue D := digitsValue_map D h.2.2.2 0
    simp only [exVal, exAsc, hv]

theorem expPart_map {ex : ExPart} (h : ExRaw ex) : (expPart ex).map asc = expPart (exAsc ex) := by
  cases ex with
  | none => rfl
  | some t =>
    obtain ⟨ind, sg, D⟩ := t
    obtain ⟨h1, h2, _, _⟩ := h
    have hi : asc ind = ind := by rcases h1 with rfl | rfl <;> decide
    have hs : sg.map asc = sg := by rcases h2 with rfl | rfl | rfl <;> decide
    simp only [expPart, exAsc, List.map_cons, List.map_append, hi, hs]

theorem body_map (I : List Char) (fr : Option (List Char)) {ex : ExPart} (h : ExRaw ex) :
    (numBody I fr ++ expPart ex).map asc =
      numBody (I.map asc) (fr.map (List.map asc)) ++ expPart (exAsc ex) := by
  rw [List.map_append, expPart_map h]
  cases fr with
  | none => simp [numBody]
  | some F => simp [numBody, asc_dot]

/-- `mpd_qset_string` on a signed body starting with a digit or a point. -/
theorem mpdSetString_sign (sg : List Char) (hsg : sg = [] ∨ sg = ['+'] ∨ sg = ['-'])
    (x : Char) (r : List Char) (hx : x.isDigit = true ∨ x = '.') :
    mpdSetString (sg ++ x :: r) = mpdNumeric (decide (sg = ['-'])) (x :: r) := by
  rcases hsg with rfl | rfl | rfl
  · have := mpdSetString_num false x r hx
    simpa using this
  · have h1 := mpdSetString_num false x r hx
    have hsp : expSign (['+'] ++ x :: r) = (false, x :: r) := rfl
    have hsp0 : expSign (x :: r) = (false, x :: r) := by
      rcases hx with h | rfl
      · exact expSign_digit x r h
      · rfl
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, mpdSetString, hsp0] at h1
    simp only [mpdSetString, hsp]
    simpa using h1
  · exact mpdSetString_num true x r hx

theorem pyNum_ok {n : Bool} {I F : List Char} {ex : ExPart} {d : Dec}
    (h : pyNum n I F (exGroup ex) = .ok d) :
    d = .fin n (digitsValue (I ++ F)) (exVal ex - F.length) ∧ (I ++ F).length ≤ maxStrDigits := by
  have hlim : (I ++ F).length ≤ maxStrDigits := by
    rcases Nat.lt_or_ge maxStrDigits (I ++ F).length with hb | hb
    · exfalso
      have hi : intLimit (I ++ F).length = .error (.valueError (limitToIntMsg (I ++ F).length)) := by
        unfold intLimit
        rw [if_pos hb]
      cases ex with
      | none =>
        simp only [pyNum, exGroup, hi] at h
        cases h
      | some t =>
        obtain ⟨ind, sg, D⟩ := t
        simp only [pyNum, exGroup, hi] at h
        unfold intLimit at h
        split at h <;> cases h
    · exact hb
  have hi : intLimit (I ++ F).length = .ok () := by
    unfold intLimit
    rw [if_neg (Nat.not_lt.mpr hlim)]
  refine ⟨?_, hlim⟩
  cases ex with
  | none =>
    simp only [pyNum, exGroup, hi] at h
    cases h
    rfl
  | some t =>
    obtain ⟨ind, sg, D⟩ := t
    simp only [pyNum, exGroup, hi] at h
    unfold intLimit at h
    split at h
    · cases h
    · simp only [bind, Except.bind, pure, Except.pure] at h
      cases h
      simp [exVal]

/-! ## The alternatives of the regex -/

/-- None of the three non-ASCII characters that `re.IGNORECASE` folds onto a
letter of the pattern. -/
def NoFold (c : Char) : Prop := c.toNat ≠ 0x130 ∧ c.toNat ≠ 0x131 ∧ c.toNat ≠ 0x17F

theorem pyMatch_split {t b : List Char} {n : Bool} {m : PyMatch} (hs : expSign t = (n, b))
    (h : pyMatch t = some m) :
    (pyLook b = true ∧ matchNum n b = some m) ∨
    (pyLook b = false ∧ m = .inf n ∧ ∃ r, matchWord "inf".toList b = some r ∧
      (r = [] ∨ matchWord "inity".toList r = some [])) ∨
    (pyLook b = false ∧ matchWord "inf".toList b = none ∧ matchNan n b = some m) := by
  simp only [pyMatch, hs] at h
  cases hl : pyLook b with
  | true =>
    rw [hl] at h
    exact Or.inl ⟨rfl, by simpa using h⟩
  | false =>
    rw [hl] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    cases hw : matchWord "inf".toList b with
    | none =>
      rw [hw] at h
      exact Or.inr (Or.inr ⟨rfl, rfl, h⟩)
    | some r =>
      rw [hw] at h
      cases r with
      | nil =>
        simp only [Option.some.injEq] at h
        exact Or.inr (Or.inl ⟨rfl, h.symm, [], rfl, Or.inl rfl⟩)
      | cons x xs =>
        simp only at h
        split at h
        · rename_i h1
          simp only [Option.some.injEq] at h
          exact Or.inr (Or.inl ⟨rfl, h.symm, x :: xs, rfl, Or.inr h1⟩)
        · cases h

theorem mem_strip {c : Char} {s : List Char} (h : c ∈ strip s) : c ∈ s := by
  simp only [strip, List.mem_reverse] at h
  exact List.dropWhile_subset _ (by simpa using List.dropWhile_subset _ h)

/-- Letters of the pattern: ASCII, with an ASCII upper case. -/
def Lett (p : Char) : Prop := (0 < p.toNat ∧ p.toNat ≤ 127) ∧ (0 < p.toUpper.toNat ∧ p.toUpper.toNat ≤ 127)

instance : DecidablePred Lett := fun c => by unfold Lett; infer_instance

theorem ci_noFold {p c : Char} (h : ciMatch p c = true) (hc : NoFold c) (hp : Lett p) :
    (c == p || c == p.toUpper) = true ∧ 0 < c.toNat ∧ c.toNat ≤ 127 := by
  obtain ⟨h1, h2, h3⟩ := hc
  simp only [ciMatch, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with (h | h) | h | h
  · have hq : (c == p || c == p.toUpper) = true := by
      rcases h with h | h <;> simp [h]
    refine ⟨hq, ?_⟩
    rcases h with h | h
    · subst h; exact hp.1
    · subst h; exact hp.2
  · omega
  · omega

/-- `re.IGNORECASE` on a word against `_mpd_strneq`, without fold characters. -/
theorem matchWord_strneq (w b : List Char) (r : List Char) (nul : Bool) (hw : ∀ p ∈ w, Lett p)
    (hb : ∀ c ∈ b, NoFold c) (h : matchWord w b = some r) :
    strneq w (b.map asc) nul = strneq [] (r.map asc) nul ∧ ∀ c ∈ b, c ∈ r ∨ (0 < c.toNat ∧ c.toNat ≤ 127) := by
  induction w generalizing b with
  | nil =>
    simp only [matchWord, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun c hc => Or.inl hc⟩
  | cons p ps ih =>
    cases b with
    | nil => cases h
    | cons c cs =>
      simp only [matchWord] at h
      split at h
      · rename_i hm
        obtain ⟨h1, h2⟩ := ci_noFold hm (hb c (by simp)) (hw p (by simp))
        obtain ⟨h3, h4⟩ := ih cs (fun x hx => hw x (by simp [hx])) (fun x hx => hb x (by simp [hx])) h
        have hasc : asc c = c := asc_ascii h2
        refine ⟨?_, ?_⟩
        · simp only [List.map_cons, hasc, strneq, h1, ↓reduceIte]
          exact h3
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact Or.inr h2
          · exact h4 x hx
      · cases h

/-- What a word consumes comes from the input. -/
theorem List.exists_append_of_mem_matchWord {w b r : List Char} {c : Char}
    (h : matchWord w b = some r) (hc : c ∈ r) : c ∈ b := by
  induction w generalizing b with
  | nil =>
    simp only [matchWord, Option.some.injEq] at h
    subst h
    exact hc
  | cons p ps ih =>
    cases b with
    | nil => cases h
    | cons x xs =>
      simp only [matchWord] at h
      split at h
      · exact List.mem_cons_of_mem _ (ih h)
      · cases h

theorem pyLook_exp {ex : ExPart} (h : ExRaw ex) : pyLook (expPart ex) = false := by
  cases ex with
  | none => rfl
  | some t =>
    obtain ⟨ind, sg, D⟩ := t
    rcases h.1 with rfl | rfl <;> rfl

theorem pyLook_dot_exp {ex : ExPart} (h : ExRaw ex) : pyLook ('.' :: expPart ex) = false := by
  cases ex with
  | none => rfl
  | some t =>
    obtain ⟨ind, sg, D⟩ := t
    rcases h.1 with rfl | rfl <;> rfl

/-- The numeric alternative: `_decimal` reads what `_pydecimal` read. -/
theorem cParse_of_num (sg : List Char) (hsg : sg = [] ∨ sg = ['+'] ∨ sg = ['-'])
    (I : List Char) (fr : Option (List Char)) (ex : ExPart)
    (hI : ∀ c ∈ I, isDigit c = true) (hF : ∀ c ∈ fr.getD [], isDigit c = true) (hx : ExRaw ex)
    (hlook : pyLook (numBody I fr ++ expPart ex) = true) (hlen : (I ++ fr.getD []).length ≤ maxStrDigits)
    (hlim : InCLimits (.fin (decide (sg = ['-'])) (digitsValue (I ++ fr.getD []))
      (exVal ex - (fr.getD []).length))) :
    match mpdSetString (sg ++ (numBody I fr ++ expPart ex).map asc) with
    | .fin n c _ e =>
      n = decide (sg = ['-']) ∧ c = digitsValue (I ++ fr.getD []) ∧ e = exVal ex - (fr.getD []).length
    | _ => False := by
  have hadI : AD (I.map asc) := asc_AD hI
  have hfr : (fr.map (List.map asc)).getD [] = (fr.getD []).map asc := by cases fr <;> rfl
  have hadF : AD ((fr.map (List.map asc)).getD []) := by rw [hfr]; exact asc_AD hF
  have hvalL : digitsValue (I.map asc ++ (fr.map (List.map asc)).getD []) = digitsValue (I ++ fr.getD []) := by
    rw [hfr, ← List.map_append]
    exact digitsValue_map _ (fun c hc => by
      rcases List.mem_append.mp hc with h | h
      · exact hI c h
      · exact hF c h) 0
  have hflen : ((fr.map (List.map asc)).getD []).length = (fr.getD []).length := by rw [hfr]; simp
  have hok := exRaw_ok hx
  have hne : I.map asc ++ (fr.map (List.map asc)).getD [] ≠ [] := by
    intro h0
    have h1 : I = [] := by simpa using (List.eq_nil_of_append_eq_nil h0).1
    have h2 : (fr.map (List.map asc)).getD [] = [] := (List.eq_nil_of_append_eq_nil h0).2
    subst h1
    rw [hfr] at h2
    have h3 : fr.getD [] = [] := by simpa using h2
    cases fr with
    | none =>
      simp only [numBody, List.nil_append] at hlook
      rw [pyLook_exp hx] at hlook
      cases hlook
    | some F =>
      have : F = [] := h3
      subst this
      simp only [numBody, List.nil_append] at hlook
      rw [show (['.'] ++ expPart ex) = '.' :: expPart ex from rfl, pyLook_dot_exp hx] at hlook
      cases hlook
  obtain ⟨hl1, hl2, hl3⟩ := hlim
  have hnd := numDigits_pos (digitsValue (I ++ fr.getD []))
  have hb : (numBody (I.map asc) (fr.map (List.map asc)) ++ expPart (exAsc ex)) =
      numBody (I.map asc) (fr.map (List.map asc)) ++ expPart (exAsc ex) := rfl
  have hhead : ∃ x r, numBody (I.map asc) (fr.map (List.map asc)) ++ expPart (exAsc ex) = x :: r ∧
      (x.isDigit = true ∨ x = '.') := by
    cases hIc : I.map asc with
    | cons y ys =>
      refine ⟨y, _, rfl, Or.inl (hadI y (by rw [hIc]; simp))⟩
    | nil =>
      cases fr with
      | none =>
        exfalso
        apply hne
        simp [hIc]
      | some F => exact ⟨'.', _, rfl, Or.inr rfl⟩
  obtain ⟨x, r, hbody, hxd⟩ := hhead
  have hnum := mpd_num (decide (sg = ['-'])) (I.map asc) (fr.map (List.map asc)) (exAsc ex) hadI hadF hne hok
    (by rw [hflen]; simp only [maxStrDigits, mpdMaxPrec] at *
        have : (fr.getD []).length ≤ (I ++ fr.getD []).length := by simp
        omega)
    (by rw [hvalL]; exact hl1)
    (by rw [hflen, exVal_asc hx]; exact hl3)
    (by rw [hflen, exVal_asc hx]; simp only [mpdMaxEmax] at *; omega)
  rw [body_map I fr hx, hbody, mpdSetString_sign sg hsg x r hxd, ← hbody, hnum, hvalL, hflen, exVal_asc hx]
  exact ⟨rfl, rfl, rfl⟩

/-! ## The keyword alternatives -/

theorem lett_words : (∀ p ∈ "inf".toList, Lett p) ∧ (∀ p ∈ "inity".toList, Lett p) ∧ (∀ p ∈ "nan".toList, Lett p) := by
  decide

theorem pyNanVal_ok {n sig : Bool} {D : List Char} {d : Dec} (h : pyNanVal n sig D = .ok d) :
    d = .nan n sig (digitsValue D) := by
  unfold pyNanVal at h
  cases hl : intLimit (if D = [] then 1 else D.length) with
  | error e => rw [hl] at h; cases h
  | ok u =>
    rw [hl] at h
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    exact h.symm

theorem mpdPayload_map (n sig : Bool) (D : List Char) (hD : ∀ c ∈ D, isDigit c = true)
    (hlen : D.length ≤ maxStrDigits) :
    ∃ k, mpdPayload n sig (D.map asc) = .nan n sig (digitsValue D) k := by
  have hA : AD (D.map asc) := asc_AD hD
  have hv : digitsValue (D.map asc) = digitsValue D := digitsValue_map D hD 0
  unfold mpdPayload
  cases D with
  | nil => exact ⟨0, rfl⟩
  | cons x xs =>
    rw [if_neg (by simp)]
    generalize hL : (x :: xs).map asc = L at *
    have hs : scanPayload L = some (L.dropWhile (· == '0')) := by
      simp only [scanPayload]
      rw [if_pos]
      apply List.all_eq_true.mpr
      intro c hc
      exact isAsciiDigit_iff.mpr (hA c (List.dropWhile_subset _ hc))
    rw [hs]
    simp only
    have hl : ¬ ((L.dropWhile (· == '0')).length : Int) > mpdMaxPrec := by
      have h1 : (L.dropWhile (· == '0')).length ≤ L.length := (List.dropWhile_sublist _).length_le
      have h2 : L.length = (x :: xs).length := by rw [← hL]; simp
      simp only [maxStrDigits, mpdMaxPrec] at *
      omega
    rw [if_neg hl]
    have hsplit : L.takeWhile (· == '0') ++ L.dropWhile (· == '0') = L := List.takeWhile_append_dropWhile
    have hz : ∀ c ∈ L.takeWhile (· == '0'), c = '0' := fun c hc => by
      have := mem_takeWhile' hc
      simpa using this
    have hval : digitsValue (L.dropWhile (· == '0')) = digitsValue (x :: xs) := by
      rw [← hv, ← digitsValue_zeros _ _ hz, hsplit]
    exact ⟨_, by rw [hval]⟩

theorem expSign_prefix (sg s' : List Char) (hsg : sg = [] ∨ sg = ['+'] ∨ sg = ['-'])
    (hh : ∀ c r, s' = c :: r → c ≠ '+' ∧ c ≠ '-') :
    expSign (sg ++ s') = (decide (sg = ['-']), s') := by
  rcases hsg with rfl | rfl | rfl
  · simp only [List.nil_append]
    cases s' with
    | nil => rfl
    | cons c r =>
      obtain ⟨h1, h2⟩ := hh c r rfl
      have : expSign (c :: r) = (false, c :: r) := by
        unfold expSign
        split <;> simp_all
      simpa using this
  · rfl
  · rfl

theorem strneq_head_none (w : Char) (ws : List Char) (x : Char) (r : List Char) (hx : x ≠ w ∧ x ≠ w.toUpper) :
    strneq (w :: ws) (x :: r) false = none := by
  simp [strneq, hx.1, hx.2]

/-- The keyword alternatives, as `mpd_qset_string` sees them. -/
theorem mpdBody_inf (n : Bool) (b r : List Char) (hb : ∀ c ∈ b, NoFold c)
    (hw : matchWord "inf".toList b = some r) (hr : r = [] ∨ matchWord "inity".toList r = some []) :
    mpdBody n (b.map asc) = .inf n ∧ (∀ c ∈ b, 0 < c.toNat ∧ c.toNat ≤ 127) ∧
      ∃ x rr, b.map asc = x :: rr ∧ x ≠ '+' ∧ x ≠ '-' := by
  obtain ⟨hl1, hl2, _⟩ := lett_words
  obtain ⟨h1, h2⟩ := matchWord_strneq _ b r false hl1 hb hw
  cases b with
  | nil => cases hw
  | cons x xs =>
    have hm : ciMatch 'i' x = true ∧ matchWord "nf".toList xs = some r := by
      have : matchWord "inf".toList (x :: xs) = if ciMatch 'i' x then matchWord "nf".toList xs else none := rfl
      rw [this] at hw
      split at hw
      · exact ⟨by assumption, hw⟩
      · cases hw
    obtain ⟨hq, ha⟩ := ci_noFold hm.1 (hb x (by simp)) (by decide)
    have hxi : x = 'i' ∨ x = 'I' := by
      have hu : ('i' : Char).toUpper = 'I' := by decide
      rw [hu] at hq
      simpa using hq
    have hax : asc x = x := asc_ascii ha
    have hmap : (x :: xs).map asc = x :: xs.map asc := by simp [hax]
    have s1 : strneq "nan".toList (x :: xs.map asc) false = none := by
      show strneq ('n' :: ['a', 'n']) _ _ = none
      apply strneq_head_none
      rcases hxi with rfl | rfl <;> decide
    have s2 : strneq "snan".toList (x :: xs.map asc) false = none := by
      show strneq ('s' :: ['n', 'a', 'n']) _ _ = none
      apply strneq_head_none
      rcases hxi with rfl | rfl <;> decide
    have s3 : strneq "inf".toList (x :: xs.map asc) false = some (r.map asc) := by
      rw [← hmap, h1]; rfl
    have hall : ∀ c ∈ x :: xs, 0 < c.toNat ∧ c.toNat ≤ 127 := by
      intro c hc
      rcases h2 c hc with h | h
      · rcases hr with rfl | hr
        · simp at h
        · have hnf : ∀ c ∈ r, NoFold c := by
            intro y hy
            rcases List.exists_append_of_mem_matchWord hw hy with h'
            exact hb y h'
          rcases (matchWord_strneq _ r [] true hl2 hnf hr).2 c h with h' | h'
          · simp at h'
          · exact h'
      · exact h
    refine ⟨?_, hall, x, xs.map asc, hmap, ?_, ?_⟩
    · rw [hmap]
      simp only [mpdBody, s1, s2, s3]
      rcases hr with rfl | hr
      · simp
      · have hnf : ∀ c ∈ r, NoFold c := by
          intro y hy
          exact hb y (List.exists_append_of_mem_matchWord hw hy)
        have h3 := (matchWord_strneq _ r [] true hl2 hnf hr).1
        have h4 : strneq ['i', 'n', 'i', 't', 'y'] (r.map asc) true = some [] := by
          have : strneq "inity".toList (r.map asc) true = some [] := by rw [h3]; rfl
          exact this
        simp [h4]
    · rcases hxi with rfl | rfl <;> decide
    · rcases hxi with rfl | rfl <;> decide

theorem mpdBody_nan (n : Bool) (b : List Char) (m : PyMatch) (hb : ∀ c ∈ b, NoFold c)
    (h : matchNan n b = some m) :
    ∃ sig D, m = .nan n sig D ∧ (∀ c ∈ D, isDigit c = true) ∧
      mpdBody n (b.map asc) = mpdPayload n sig (D.map asc) ∧
      (∀ c ∈ b, c ∈ D ∨ (0 < c.toNat ∧ c.toNat ≤ 127)) ∧
      ∃ x rr, b.map asc = x :: rr ∧ x ≠ '+' ∧ x ≠ '-' := by
  obtain ⟨_, _, hl3⟩ := lett_words
  cases b with
  | nil =>
    have : matchNan n [] = none := rfl
    rw [this] at h
    cases h
  | cons x xs =>
    have hxn : NoFold x := hb x (by simp)
    have hxs : ∀ c ∈ xs, NoFold c := fun c hc => hb c (by simp [hc])
    by_cases hs : ciMatch 's' x = true
    · have hsp : matchSig (x :: xs) = (true, xs) := by simp [matchSig, hs]
      simp only [matchNan, hsp] at h
      cases hw : matchWord "nan".toList xs with
      | none => rw [hw] at h; cases h
      | some D =>
        rw [hw] at h
        simp only at h
        split at h
        · rename_i hall
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨hq, ha⟩ := ci_noFold hs hxn (by decide)
          have hxi : x = 's' ∨ x = 'S' := by
            have hu : ('s' : Char).toUpper = 'S' := by decide
            rw [hu] at hq
            simpa using hq
          have hax : asc x = x := asc_ascii ha
          have hmap : (x :: xs).map asc = x :: xs.map asc := by simp [hax]
          obtain ⟨h1, h2⟩ := matchWord_strneq _ xs D false hl3 hxs hw
          have s1 : strneq "nan".toList (x :: xs.map asc) false = none := by
            show strneq ('n' :: ['a', 'n']) _ _ = none
            apply strneq_head_none
            rcases hxi with rfl | rfl <;> decide
          have s2 : strneq "snan".toList (x :: xs.map asc) false = some (D.map asc) := by
            have h3 : strneq "nan".toList (xs.map asc) false = some (D.map asc) := by rw [h1]; rfl
            show strneq ('s' :: "nan".toList) (x :: xs.map asc) false = _
            have hk : (x == 's' || x == ('s' : Char).toUpper) = true := hq
            simp only [strneq, hk, ↓reduceIte]
            exact h3
          refine ⟨true, D, rfl, fun c hc => List.all_eq_true.mp hall c hc, ?_, ?_, x, xs.map asc, hmap, ?_, ?_⟩
          · rw [hmap]
            simp only [mpdBody, s1, s2]
          · intro c hc
            simp only [List.mem_cons] at hc
            rcases hc with rfl | hc
            · exact Or.inr ha
            · exact h2 c hc
          · rcases hxi with rfl | rfl <;> decide
          · rcases hxi with rfl | rfl <;> decide
        · cases h
    · have hsp : matchSig (x :: xs) = (false, x :: xs) := by simp [matchSig, hs]
      simp only [matchNan, hsp] at h
      cases hw : matchWord "nan".toList (x :: xs) with
      | none => rw [hw] at h; cases h
      | some D =>
        rw [hw] at h
        simp only at h
        split at h
        · rename_i hall
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨h1, h2⟩ := matchWord_strneq _ (x :: xs) D false hl3 hb hw
          have hm : ciMatch 'n' x = true := by
            have : matchWord "nan".toList (x :: xs) = if ciMatch 'n' x then matchWord "an".toList xs else none := rfl
            rw [this] at hw
            split at hw
            · assumption
            · cases hw
          obtain ⟨hq, ha⟩ := ci_noFold hm hxn (by decide)
          have hxi : x = 'n' ∨ x = 'N' := by
            have hu : ('n' : Char).toUpper = 'N' := by decide
            rw [hu] at hq
            simpa using hq
          have hax : asc x = x := asc_ascii ha
          have hmap : (x :: xs).map asc = x :: xs.map asc := by simp [hax]
          have s1 : strneq "nan".toList ((x :: xs).map asc) false = some (D.map asc) := by rw [h1]; rfl
          refine ⟨false, D, rfl, fun c hc => List.all_eq_true.mp hall c hc, ?_, h2, x, xs.map asc, hmap, ?_, ?_⟩
          · simp only [mpdBody, s1]
          · rcases hxi with rfl | rfl <;> decide
          · rcases hxi with rfl | rfl <;> decide
        · cases h

theorem matchNum_form {n : Bool} {b : List Char} {m : PyMatch} (h : matchNum n b = some m) :
    ∃ I F g, m = .num n I F g := by
  simp only [matchNum] at h
  generalize matchFrac (b.dropWhile isDigit) = pr at h
  obtain ⟨f, r2⟩ := pr
  simp only at h
  cases hm : matchExpEnd r2 with
  | none => rw [hm] at h; cases h
  | some g =>
    rw [hm] at h
    simp only [Option.some.injEq] at h
    exact ⟨_, _, _, h.symm⟩

/-- For every string without the three case-variant characters, if
`_pydecimal.Decimal(s)` returns a value within the C module's documented limits,
`_decimal.Decimal(s)` returns the same value. -/
def ParseCAcceptsPyCasefree : Prop :=
  ∀ (s : List Char) (d : Dec), (∀ c ∈ s, NoFold c) → pyParse s = .ok d → InCLimits d → cParse s = .ok d

theorem parseCAcceptsPyCasefree_proven : ParseCAcceptsPyCasefree := by
  intro s d hnf hpy hlim
  simp only [pyParse] at hpy
  have hmem : ∀ c ∈ (strip s).filter (· ≠ '_'), c ∈ s :=
    fun c hc => mem_strip (List.mem_filter.mp hc).1
  have hgo : (∀ c ∈ (strip s).filter (· ≠ '_'), Valid c) →
      numericAsAscii s = ((strip s).filter (· ≠ '_')).map asc := by
    intro hv
    simp only [numericAsAscii]
    rw [go_map (strip s) [] (fun c hc => by
      by_cases hu : c = '_'
      · exact Or.inl hu
      · exact Or.inr (hv c (List.mem_filter.mpr ⟨hc, by simpa using hu⟩)))]
    rfl
  generalize ht : (strip s).filter (· ≠ '_') = t at *
  cases hm : pyMatch t with
  | none => rw [hm] at hpy; cases hpy
  | some m =>
    rw [hm] at hpy
    generalize hes : expSign t = pr
    obtain ⟨n, b⟩ := pr
    obtain ⟨sg, htt, hsg, hn⟩ := expSign_inv hes
    have hbnf : ∀ c ∈ b, NoFold c := fun c hc => hnf c (hmem c (by rw [htt]; simp [hc]))
    have hsgmap : sg.map asc = sg := by rcases hsg with rfl | rfl | rfl <;> decide
    have hmap : t.map asc = sg ++ b.map asc := by rw [htt, List.map_append, hsgmap]
    have hsgv : ∀ c ∈ sg, Valid c := by
      intro c hc
      left
      rcases hsg with rfl | rfl | rfl
      · simp at hc
      · simp only [List.mem_singleton] at hc; subst hc; decide
      · simp only [List.mem_singleton] at hc; subst hc; decide
    have hvalid : (∀ c ∈ b, Valid c) → ∀ c ∈ t, Valid c := by
      intro hv c hc
      rw [htt] at hc
      rcases List.mem_append.mp hc with h | h
      · exact hsgv c h
      · exact hv c h
    rcases pyMatch_split hes hm with ⟨hlook, hnum⟩ | ⟨_, rfl, r, hw, hr⟩ | ⟨_, _, hnan⟩
    · obtain ⟨I, F, g, rfl⟩ := matchNum_form hnum
      obtain ⟨fr, ex, hbody, hfr, hraw, hgr, _, hI, hF⟩ := matchNum_inv hnum
      subst hfr hgr
      simp only at hpy
      obtain ⟨hd, hlen⟩ := pyNum_ok hpy
      subst hd
      have hbv : ∀ c ∈ b, Valid c := by
        intro c hc
        rw [hbody] at hc
        rcases List.mem_append.mp hc with h | h
        · simp only [numBody, List.mem_append] at h
          rcases h with h | h
          · exact Or.inr (Or.inr (hI c h))
          · cases fr with
            | none => simp at h
            | some F =>
              simp only [List.mem_cons] at h
              rcases h with rfl | h
              · left; decide
              · exact Or.inr (Or.inr (hF c h))
        · cases ex with
          | none => simp [expPart] at h
          | some te =>
            obtain ⟨ind, sg', D⟩ := te
            obtain ⟨hi, hs, _, hA⟩ := hraw
            simp only [expPart, List.mem_cons, List.mem_append] at h
            rcases h with rfl | h | h
            · left; rcases hi with rfl | rfl <;> decide
            · left
              rcases hs with rfl | rfl | rfl <;> simp at h <;> subst h <;> decide
            · exact Or.inr (Or.inr (hA c h))
      rw [hbody] at hlook hmap
      have hsgneg : n = decide (sg = ['-']) := hn
      subst hsgneg
      have hres := cParse_of_num sg hsg I fr ex hI hF hraw hlook hlen hlim
      simp only [cParse]
      rw [hgo (hvalid hbv), hmap]
      cases hmp : mpdSetString (sg ++ (numBody I fr ++ expPart ex).map asc) with
      | fin n' c' dg e' =>
        rw [hmp] at hres
        obtain ⟨rfl, rfl, rfl⟩ := hres
        simp only
        rw [if_pos hlim]
      | «syntax» => rw [hmp] at hres; exact hres.elim
      | inf _ => rw [hmp] at hres; exact hres.elim
      | nan _ _ _ _ => rw [hmp] at hres; exact hres.elim
    · simp only at hpy
      cases hpy
      obtain ⟨hbd, hasc, x, rr, hmb, h1, h2⟩ := mpdBody_inf n b r hbnf hw hr
      have hbv : ∀ c ∈ b, Valid c := fun c hc => Or.inl (hasc c hc)
      simp only [cParse]
      rw [hgo (hvalid hbv), hmap]
      have hes' : expSign (sg ++ b.map asc) = (decide (sg = ['-']), b.map asc) :=
        expSign_prefix sg _ hsg (fun c r hh => by
          rw [hmb] at hh
          simp only [List.cons.injEq] at hh
          rw [← hh.1]
          exact ⟨h1, h2⟩)
      simp only [mpdSetString, hes', ← hn, hbd]
    · obtain ⟨sig, D, rfl, hD, hbd, hch, x, rr, hmb, h1, h2⟩ := mpdBody_nan n b m hbnf hnan
      simp only at hpy
      have hd := pyNanVal_ok hpy
      subst hd
      have hlenD : D.length ≤ maxStrDigits := by
        unfold pyNanVal at hpy
        rcases Nat.lt_or_ge maxStrDigits D.length with hl | hl
        · exfalso
          have hne : D ≠ [] := by
            intro h0; subst h0; simp [maxStrDigits] at hl
          have : intLimit (if D = [] then 1 else D.length) =
              .error (.valueError (limitToIntMsg D.length)) := by
            rw [if_neg hne]
            unfold intLimit
            rw [if_pos hl]
          rw [this] at hpy
          cases hpy
        · exact hl
      have hbv : ∀ c ∈ b, Valid c := by
        intro c hc
        rcases hch c hc with h | h
        · exact Or.inr (Or.inr (hD c h))
        · exact Or.inl h
      obtain ⟨k, hk⟩ := mpdPayload_map n sig D hD hlenD
      simp only [cParse]
      rw [hgo (hvalid hbv), hmap]
      have hes' : expSign (sg ++ b.map asc) = (decide (sg = ['-']), b.map asc) :=
        expSign_prefix sg _ hsg (fun c r hh => by
          rw [hmb] at hh
          simp only [List.cons.injEq] at hh
          rw [← hh.1]
          exact ⟨h1, h2⟩)
      simp only [mpdSetString, hes', ← hn, hbd, hk]

end PyLean.Decimal
