import PyLean.Decimal.Scan
import PyLean.Decimal.Tuple

/-!
`Decimal(str(d)) == d`, sign, coefficient and exponent included, for both twins.

`sci_shape` says what `str(d)` looks like: `[-] digits [. digits] [E sign digits]`,
with digits reading back to the coefficient and the exponent reading back to `e`.
`mpd_num` (Scan.lean) then does the C side, `pyMatch_shape` the Python side.
-/

namespace PyLean.Decimal

open PyLean

theorem toDigits_len (c : Nat) : (Nat.toDigits 10 c).length = numDigits c := rfl

theorem take_drop_AD {ds : List Char} (h : AD ds) (k : Nat) : AD (ds.take k) ∧ AD (ds.drop k) :=
  ⟨fun x hx => h x (List.mem_of_mem_take hx), fun x hx => h x (List.mem_of_mem_drop hx)⟩

theorem replicate_zero_AD (k : Nat) : AD (List.replicate k '0') := by
  intro x hx
  rw [List.eq_of_mem_replicate hx]
  exact zero_isDigit

theorem toDigits_AD (c : Nat) : AD (Nat.toDigits 10 c) := fun _ hx => mem_toDigits_isDigit hx

/-- The exponent `E+x` / `E-x` that `__str__` appends. -/
def sciExp (x : Int) : ExPart := some ('E', [if x < 0 then '-' else '+'], Nat.toDigits 10 x.natAbs)

theorem sciExp_ok (x : Int) : ExOk (sciExp x) := by
  refine ⟨Or.inr rfl, ?_, Nat.toDigits_ne_nil, toDigits_AD _⟩
  by_cases h : x < 0 <;> simp [h]

theorem sciExp_val (x : Int) : exVal (sciExp x) = x := by
  simp only [exVal, sciExp, digitsValue_toDigits]
  by_cases h : x < 0
  · simp only [h, ↓reduceIte]; omega
  · have : ¬ (['+'] : List Char) = ['-'] := by decide
    simp only [h, ↓reduceIte, this]; omega

theorem sciExp_part (x : Int) : expPart (sciExp x) = 'E' :: fmtSigned x := by
  simp only [expPart, sciExp, fmtSigned]
  rfl

/-- `str(d)` of a finite decimal has the shape `[-] digits [. digits] [E sign digits]`. -/
theorem sci_shape (neg : Bool) (c : Nat) (e : Int) :
    ∃ I fr ex, sciFinite neg (Nat.toDigits 10 c) e true =
        (if neg then ['-'] else []) ++ numBody I fr ++ expPart ex ∧
      I ≠ [] ∧ AD I ∧ AD (fr.getD []) ∧ ExOk ex ∧
      digitsValue (I ++ fr.getD []) = c ∧ exVal ex - ((fr.getD []).length : Int) = e ∧
      ((fr.getD []).length ≤ numDigits c + 5) ∧ (I ++ fr.getD []).length ≤ numDigits c + 6 ∧
      (ex = none ∨ ex = sciExp (e + numDigits c - 1)) := by
  have hn := numDigits_pos c
  have hds := toDigits_AD c
  have hlen := toDigits_len c
  generalize hD : Nat.toDigits 10 c = ds at hds hlen
  have hval : digitsValue ds = c := by rw [← hD]; exact digitsValue_toDigits c
  generalize numDigits c = n at hn hlen ⊢
  simp only [sciFinite, hlen]
  by_cases h1 : e ≤ 0 ∧ e + (n : Int) > -6
  · simp only [h1, and_self, ↓reduceIte]
    by_cases h2 : e + (n : Int) ≤ 0
    · refine ⟨['0'], some (List.replicate (-(e + (n : Int))).toNat '0' ++ ds), none, ?_, by simp,
        ?_, ?_, trivial, ?_, ?_, ?_, ?_⟩
      · simp [h2, numBody, expPart]
      · intro x hx; simp at hx; subst hx; exact zero_isDigit
      · intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact replicate_zero_AD _ x h
        · exact hds x h
      · simp only [Option.getD_some, List.singleton_append]
        have : '0' :: (List.replicate (-(e + (n : Int))).toNat '0' ++ ds) =
            List.replicate ((-(e + (n : Int))).toNat + 1) '0' ++ ds := by
          simp [List.replicate_succ]
        rw [this, digitsValue_zeros _ _ (fun z hz => List.eq_of_mem_replicate hz), hval]
      · simp only [exVal, Option.getD_some, List.length_append, List.length_replicate, hlen]
        omega
      · simp only [Option.getD_some, List.length_append, List.length_replicate, hlen]
        omega
      · simp only [Option.getD_some, List.length_append, List.length_replicate, hlen,
          List.length_cons, List.length_nil]
        exact ⟨by omega, by simp⟩
    · by_cases h3 : e + (n : Int) ≥ n
      · have he : e = 0 := by omega
        subst he
        have hn0 : n ≠ 0 := by omega
        refine ⟨ds, none, none, ?_, ?_, hds, (fun _ hx => by simp at hx), trivial, ?_, ?_, ?_, ?_⟩
        · simp [hn0, numBody, expPart]
        · intro h0; subst h0; simp at hlen; omega
        · simpa using hval
        · simp [exVal]
        · simp
        · exact ⟨by simp; omega, by simp⟩
      · have hk : ds.take (e + (n : Int)).toNat ++ ds.drop (e + (n : Int)).toNat = ds :=
          List.take_append_drop _ _
        have ht := take_drop_AD hds (e + (n : Int)).toNat
        refine ⟨ds.take (e + (n : Int)).toNat, some (ds.drop (e + (n : Int)).toNat), none, ?_, ?_,
          ht.1, ht.2, trivial, ?_, ?_, ?_, ?_⟩
        · simp [h2, h3, numBody, expPart]
        · intro h0
          have hl := @List.length_take _ (e + (n : Int)).toNat ds
          rw [h0] at hl
          simp only [List.length_nil] at hl
          omega
        · simp only [Option.getD_some, hk, hval]
        · simp only [exVal, Option.getD_some, List.length_drop, hlen]
          omega
        · simp only [Option.getD_some, List.length_drop, hlen]
          omega
        · simp only [Option.getD_some, hk, hlen]
          exact ⟨by omega, by simp⟩
  · have hne1 : e + (n : Int) ≠ 1 := by omega
    simp only [h1, ↓reduceIte]
    by_cases h3 : n = 1
    · subst h3
      have hne1' : ¬ e + 1 = 1 := by simpa using hne1
      refine ⟨ds, none, sciExp (e + (1 : Nat) - 1), ?_, ?_, hds, (fun _ hx => by simp at hx), sciExp_ok _, ?_, ?_, ?_, ?_⟩
      · simp [numBody, sciExp_part, hne1']
      · intro h0; subst h0; simp at hlen
      · simpa using hval
      · simp [sciExp_val]
      · simp
      · exact ⟨by simp; omega, by simp⟩
    · have hk : ds.take 1 ++ ds.drop 1 = ds := List.take_append_drop _ _
      have ht := take_drop_AD hds 1
      refine ⟨ds.take 1, some (ds.drop 1), sciExp (e + (n : Int) - 1), ?_, ?_, ht.1, ht.2,
        sciExp_ok _, ?_, ?_, ?_, ?_⟩
      · have hn1 : ¬ (1 : Int) ≥ n := by omega
        simp [numBody, sciExp_part, hne1, hn1]
      · intro h0
        have hl := @List.length_take _ 1 ds
        rw [h0] at hl
        simp only [List.length_nil] at hl
        omega
      · simp only [Option.getD_some, hk, hval]
      · simp only [sciExp_val, Option.getD_some, List.length_drop, hlen]
        omega
      · simp only [Option.getD_some, List.length_drop, hlen]
        omega
      · simp only [Option.getD_some, hk, hlen]
        exact ⟨by omega, by simp⟩

/-! ## The C twin -/

/-- Characters `numeric_as_ascii` keeps unchanged. -/
def Plain (c : Char) : Prop := 0 < c.toNat ∧ c.toNat ≤ 127 ∧ c ≠ '_' ∧ isSpace c = false

instance : DecidablePred Plain := fun c => by unfold Plain; infer_instance

theorem dropWhile_false (p : Char → Bool) (L : List Char) (h : ∀ c ∈ L, p c = false) : L.dropWhile p = L := by
  cases L with
  | nil => rfl
  | cons x xs => simp [h x (by simp)]

theorem strip_plain (s : List Char) (h : ∀ c ∈ s, isSpace c = false) : strip s = s := by
  simp only [strip]
  rw [dropWhile_false _ _ h, dropWhile_false _ _ (fun c hc => h c (by simpa using hc)), List.reverse_reverse]

theorem go_plain (s acc : List Char) (h : ∀ c ∈ s, Plain c) :
    numericAsAscii.go acc s = some (acc.reverse ++ s) := by
  induction s generalizing acc with
  | nil => simp [numericAsAscii.go]
  | cons x xs ih =>
    obtain ⟨h1, h2, h3, _⟩ := h x (by simp)
    have h4 : (x == '_') = false := beq_false_of_ne h3
    simp only [numericAsAscii.go, h4, Bool.false_eq_true, ↓reduceIte]
    rw [if_pos ⟨h1, h2⟩, ih _ (fun c hc => h c (by simp [hc]))]
    simp

theorem numericAsAscii_plain (s : List Char) (h : ∀ c ∈ s, Plain c) : numericAsAscii s = s := by
  simp only [numericAsAscii]
  rw [strip_plain s (fun c hc => (h c hc).2.2.2), go_plain s [] h]
  rfl

theorem plain_digit {c : Char} (h : c.isDigit = true) : Plain c := by
  have := isDigit_iff'.mp h
  refine ⟨by omega, by omega, ne_of_digit h (by decide), ?_⟩
  cases hs : isSpace c with
  | false => rfl
  | true =>
    exfalso
    simp [isSpace] at hs
    omega

/-- A body starts with a digit or with `.`, so no keyword matches. -/
theorem mpdSetString_num (neg : Bool) (x : Char) (r : List Char) (hx : x.isDigit = true ∨ x = '.') :
    mpdSetString ((if neg then ['-'] else []) ++ x :: r) = mpdNumeric neg (x :: r) := by
  have hne : ∀ d : Char, d.toNat < 48 ∨ 57 < d.toNat → x ≠ '.' → x ≠ d := by
    intro d hd hdot
    rcases hx with h | h
    · exact ne_of_digit h hd
    · exact absurd h hdot
  have key : ∀ (d : Char), (d = 'n' ∨ d = 'N' ∨ d = 's' ∨ d = 'S' ∨ d = 'i' ∨ d = 'I' ∨ d = '+' ∨ d = '-') → x ≠ d := by
    intro d hd
    rcases hx with h | rfl
    · apply ne_of_digit h
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have s1 : strneq "nan".toList (x :: r) false = none := by
    show strneq ['n', 'a', 'n'] (x :: r) false = none
    simp [strneq, key 'n' (by simp), key 'N' (by simp)]
  have s2 : strneq "snan".toList (x :: r) false = none := by
    show strneq ['s', 'n', 'a', 'n'] (x :: r) false = none
    simp [strneq, key 's' (by simp), key 'S' (by simp)]
  have s3 : strneq "inf".toList (x :: r) false = none := by
    show strneq ['i', 'n', 'f'] (x :: r) false = none
    simp [strneq, key 'i' (by simp), key 'I' (by simp)]
  have hsp : expSign (x :: r) = (false, x :: r) := by
    have h1 := key '+' (by simp)
    have h2 := key '-' (by simp)
    unfold expSign
    split <;> simp_all
  have hsm : expSign (['-'] ++ x :: r) = (true, x :: r) := rfl
  cases neg
  · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, mpdSetString, hsp, s1, s2, s3]
  · simp only [↓reduceIte, mpdSetString, hsm, s1, s2, s3]

theorem numBody_cons (I : List Char) (fr : Option (List Char)) (ex : ExPart) (hI : I ≠ []) (hA : AD I) :
    ∃ x r, numBody I fr ++ expPart ex = x :: r ∧ x.isDigit = true := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hI
  exact ⟨x, _, rfl, hA x (by simp)⟩

theorem plain_body (I : List Char) (fr : Option (List Char)) (ex : ExPart) (hI : AD I)
    (hF : AD (fr.getD [])) (hx : ExOk ex) (neg : Bool) :
    ∀ c ∈ (if neg then ['-'] else []) ++ numBody I fr ++ expPart ex, Plain c := by
  intro c hc
  simp only [List.mem_append] at hc
  rcases hc with (hs | hb) | he
  · split at hs
    · simp only [List.mem_singleton] at hs; subst hs; decide
    · simp at hs
  · simp only [numBody, List.mem_append] at hb
    rcases hb with h | h
    · exact plain_digit (hI c h)
    · cases fr with
      | none => simp at h
      | some F =>
        simp only [List.mem_cons] at h
        rcases h with rfl | h
        · decide
        · exact plain_digit (hF c h)
  · cases ex with
    | none => simp [expPart] at he
    | some t =>
      obtain ⟨ind, sg, D⟩ := t
      obtain ⟨hi, hs, _, hA⟩ := hx
      simp only [expPart, List.mem_cons, List.mem_append] at he
      rcases he with rfl | h | h
      · rcases hi with rfl | rfl <;> decide
      · rcases hs with rfl | rfl | rfl <;> simp at h <;> subst h <;> decide
      · exact plain_digit (hA c h)

/-- `Decimal(str(d)) == d` in `_decimal`, for every value within the C limits
whose `str()` has at most `MPD_MAX_PREC` digits after the point. The bound
is on `fracdigits` in `mpd_qset_string` (io.c:286): the coefficient may have
up to `MPD_MAX_PREC` digits, but `0.00000ddd` adds up to five zeros to its
fraction. Such a string has about 10^18 characters, so the bound excludes
nothing that fits in memory. -/
def StrRoundTripC : Prop :=
  ∀ d : Dec, InCLimits d → (∀ neg c e, d = .fin neg c e → (numDigits c : Int) + 5 ≤ mpdMaxPrec) →
    cParse (toSci d) = .ok d

theorem scanPayload_toDigits (p : Nat) (hp : p ≠ 0) :
    scanPayload (Nat.toDigits 10 p) = some (Nat.toDigits 10 p) := by
  have hA := toDigits_AD p
  have hne : Nat.toDigits 10 p ≠ [] := Nat.toDigits_ne_nil
  have hd : (Nat.toDigits 10 p).dropWhile (· == '0') = Nat.toDigits 10 p := by
    obtain ⟨x, xs, hxs⟩ := List.exists_cons_of_ne_nil hne
    have hx0 : x ≠ '0' := by
      rintro rfl
      have hv := digitsValue_toDigits p
      rw [hxs] at hv
      apply hp
      -- a numeral with leading zero is not a spelling
      have hlen : numDigits p = (('0' : Char) :: xs).length := by simp only [numDigits, hxs]
      by_cases hxe : xs = []
      · subst hxe
        rw [← hv]; decide
      · exfalso
        have h1 := pow_numDigits_le hp
        have hxA : AD xs := fun c hc => hA c (by rw [hxs]; simp [hc])
        have hlt : digitsValue xs < 10 ^ xs.length := by
          rw [digitsValue_eq xs hxA]
          exact digits_lt xs hxA
        have heq : digitsValue (('0' : Char) :: xs) = digitsValue xs :=
          digitsValue_zeros ['0'] xs (by simp)
        rw [hv] at heq
        simp only [List.length_cons] at hlen
        rw [hlen, Nat.add_sub_cancel] at h1
        omega
    rw [hxs]
    simp [hx0]
  simp only [scanPayload, hd]
  rw [if_pos]
  apply List.all_eq_true.mpr
  intro c hc
  exact isAsciiDigit_iff.mpr (hA c hc)

/-- The digits `str` prints after `NaN`. -/
def payDigits (p : Nat) : List Char := if p = 0 then [] else Nat.toDigits 10 p

theorem payDigits_AD (p : Nat) : AD (payDigits p) := by
  intro c hc
  unfold payDigits at hc
  split at hc
  · simp at hc
  · exact mem_toDigits_isDigit hc

theorem nan_plain (neg sig : Bool) (p : Nat) :
    ∀ c ∈ (if neg then ['-'] else []) ++ (if sig then "sNaN" else "NaN").toList ++ payDigits p, Plain c := by
  intro c hc
  simp only [List.mem_append] at hc
  rcases hc with (h | h) | h
  · split at h
    · simp only [List.mem_singleton] at h; subst h; decide
    · simp at h
  · cases sig
    · simp only [Bool.false_eq_true, ↓reduceIte] at h
      have : ∀ c ∈ "NaN".toList, Plain c := by decide
      exact this c h
    · simp only [↓reduceIte] at h
      have : ∀ c ∈ "sNaN".toList, Plain c := by decide
      exact this c h
  · exact plain_digit (payDigits_AD p c h)

/-- `str` of a NaN reads back through `mpd_qset_string`. -/
theorem cParse_nan (neg sig : Bool) (p : Nat) (hlim : (numDigits p : Int) ≤ mpdMaxPrec) :
    cParse (toSci (.nan neg sig p)) = .ok (.nan neg sig p) := by
  have hplain := nan_plain neg sig p
  generalize hpay : payDigits p = pay at hplain
  have hpay' : (if p = 0 then [] else Nat.toDigits 10 p) = pay := hpay
  have hstr : toSci (.nan neg sig p) =
      (if neg then ['-'] else []) ++ (if sig then "sNaN" else "NaN").toList ++ pay := by
    simp only [toSci, hpay']
  have hres : mpdPayload neg sig pay = MpdParse.nan neg sig p (if p = 0 then 0 else numDigits p) := by
    unfold mpdPayload
    by_cases hp : p = 0
    · subst hp
      simp only [↓reduceIte] at hpay'
      subst hpay'
      simp
    · simp only [hp, ↓reduceIte] at hpay'
      subst hpay'
      rw [if_neg Nat.toDigits_ne_nil, scanPayload_toDigits p hp]
      simp only [toDigits_len, digitsValue_toDigits, hp, ↓reduceIte]
      rw [if_neg (Int.not_lt.mpr hlim)]
  have hws : ∀ b : Bool, expSign ((if b then ['-'] else []) ++ (if sig then "sNaN" else "NaN").toList ++ pay) =
      (b, (if sig then "sNaN" else "NaN").toList ++ pay) := by
    intro b
    cases b <;> cases sig <;> rfl
  rw [hstr]
  simp only [cParse]
  rw [numericAsAscii_plain _ hplain]
  simp only [mpdSetString, hws]
  cases sig
  · have s1 : strneq "nan".toList ("NaN".toList ++ pay) false = some pay := by
      show strneq ['n', 'a', 'n'] ('N' :: 'a' :: 'N' :: pay) false = some pay
      simp [strneq]
    simp only [s1, hres, Bool.false_eq_true, ↓reduceIte]
  · have s1 : strneq "nan".toList ("sNaN".toList ++ pay) false = none := by
      show strneq ['n', 'a', 'n'] ('s' :: 'N' :: 'a' :: 'N' :: pay) false = none
      simp [strneq]
    have s2 : strneq "snan".toList ("sNaN".toList ++ pay) false = some pay := by
      show strneq ['s', 'n', 'a', 'n'] ('s' :: 'N' :: 'a' :: 'N' :: pay) false = some pay
      simp [strneq]
    simp only [s1, s2, hres, ↓reduceIte]

theorem strRoundTripC_proven : StrRoundTripC := by
  intro d hlim hbound
  cases d with
  | inf neg => cases neg <;> decide
  | nan neg sig p => exact cParse_nan neg sig p hlim
  | fin neg c e =>
    obtain ⟨I, fr, ex, h1, hI0, hI, hF, hx, hv, he, hfl, hl, _⟩ := sci_shape neg c e
    obtain ⟨hl1, hl2, hl3⟩ := hlim
    have hb := hbound neg c e rfl
    have hn := numDigits_pos c
    simp only [mpdMaxPrec, mpdMaxEmax, mpdMinEmin, mpdMinEtiny] at hl1 hl2 hl3 hb
    have hstr : toSci (.fin neg c e) = (if neg then ['-'] else []) ++ numBody I fr ++ expPart ex := by
      simp only [toSci]; exact h1
    have hne : I ++ fr.getD [] ≠ [] := by
      intro h
      exact hI0 (List.eq_nil_of_append_eq_nil h).1
    obtain ⟨x, r, hbody, hxd⟩ := numBody_cons I fr ex hI0 hI
    have hmp : mpdSetString ((if neg then ['-'] else []) ++ numBody I fr ++ expPart ex) =
        mpdNumeric neg (numBody I fr ++ expPart ex) := by
      rw [List.append_assoc, hbody]
      exact mpdSetString_num neg x r (Or.inl hxd)
    have hnum := mpd_num neg I fr ex hI hF hne hx
      (by simp only [mpdMaxPrec]; omega)
      (by rw [hv]; simp only [mpdMaxPrec]; omega)
      (by rw [he]; simp only [mpdMinEtiny, mpdMinEmin, mpdMaxPrec]; omega)
      (by rw [he]; simp only [mpdMaxEmax]; omega)
    simp only [cParse]
    rw [hstr, numericAsAscii_plain _ (plain_body I fr ex hI hF hx neg), hmp, hnum, hv, he]
    simp only
    rw [if_pos]
    exact ⟨by simp only [mpdMaxPrec]; omega, by simp only [mpdMaxEmax]; omega,
      by simp only [mpdMinEtiny, mpdMinEmin, mpdMaxPrec]; omega⟩

/-! ## The Python twin -/

theorem not_isDigit_of {c : Char} (h : digitVal c = none) : isDigit c = false := by
  simp [isDigit, h]

theorem isDigit_dot : isDigit '.' = false := by decide
theorem isDigit_E : isDigit 'E' = false := by decide
theorem isDigit_e : isDigit 'e' = false := by decide

theorem takeWhile_AD (I T : List Char) (hI : AD I) (hT : ∀ c r, T = c :: r → isDigit c = false) :
    (I ++ T).takeWhile isDigit = I ∧ (I ++ T).dropWhile isDigit = T := by
  induction I with
  | nil =>
    cases T with
    | nil => exact ⟨rfl, rfl⟩
    | cons c r => simp [hT c r rfl]
  | cons x xs ih =>
    have hx : isDigit x = true := isDigit_of_digitVal (hI x (by simp))
    obtain ⟨h1, h2⟩ := ih (fun c hc => hI c (by simp [hc]))
    simp [hx, h1, h2]

theorem expPart_head (ex : ExPart) (hx : ExOk ex) : ∀ c r, expPart ex = c :: r → isDigit c = false := by
  intro c r h
  cases ex with
  | none => cases h
  | some t =>
    obtain ⟨ind, sg, D⟩ := t
    simp only [expPart, List.cons.injEq] at h
    rw [← h.1]
    rcases hx.1 with rfl | rfl <;> decide

/-- The group `exp` of the regex for a well-formed exponent part. -/
def exGroup : ExPart → Option (Bool × List Char)
  | none => none
  | some (_, sg, D) => some (decide (sg = ['-']), D)

theorem matchExpEnd_ok (ex : ExPart) (hx : ExOk ex) : matchExpEnd (expPart ex) = some (exGroup ex) := by
  cases ex with
  | none => rfl
  | some t =>
    obtain ⟨ind, sg, D⟩ := t
    obtain ⟨hi, hs, hD, hA⟩ := hx
    have hind : (ind == 'e' || ind == 'E') = true := by rcases hi with rfl | rfl <;> decide
    obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hD
    obtain ⟨_, _, _, _, f5, f6⟩ := digit_facts (hA d (by simp))
    have hp : d ≠ '+' := by simpa using f5
    have hm : d ≠ '-' := by simpa using f6
    have hsp : expSign (sg ++ d :: ds) = (decide (sg = ['-']), d :: ds) := by
      rcases hs with rfl | rfl | rfl
      · simp only [List.nil_append]
        have : expSign (d :: ds) = (false, d :: ds) := by
          unfold expSign
          split <;> simp_all
        simpa using this
      · rfl
      · rfl
    have hall : (d :: ds).all isDigit = true := by
      apply List.all_eq_true.mpr
      intro c hc
      exact isDigit_of_digitVal (hA c hc)
    simp only [expPart, matchExpEnd, hind, ↓reduceIte, hsp, exGroup]
    rw [if_pos ⟨by simp, hall⟩]

theorem matchFrac_shape (F E : List Char) (hF : AD F) (hE : ∀ c r, E = c :: r → isDigit c = false) :
    matchFrac ('.' :: (F ++ E)) = (F, E) := by
  obtain ⟨h1, h2⟩ := takeWhile_AD F E hF hE
  simp only [matchFrac, h1, h2]

theorem matchFrac_none (ex : ExPart) (hx : ExOk ex) : matchFrac (expPart ex) = ([], expPart ex) := by
  cases ex with
  | none => rfl
  | some t =>
    obtain ⟨ind, sg, D⟩ := t
    have : ind ≠ '.' := by rcases hx.1 with rfl | rfl <;> decide
    simp only [expPart]
    unfold matchFrac
    split <;> simp_all

theorem matchNum_shape (neg : Bool) (I : List Char) (fr : Option (List Char)) (ex : ExPart)
    (hI : AD I) (hF : AD (fr.getD [])) (hx : ExOk ex) :
    matchNum neg (numBody I fr ++ expPart ex) = some (.num neg I (fr.getD []) (exGroup ex)) := by
  have hE := expPart_head ex hx
  cases fr with
  | none =>
    obtain ⟨h1, h2⟩ := takeWhile_AD I (expPart ex) hI hE
    have hb : numBody I none ++ expPart ex = I ++ expPart ex := by simp [numBody]
    simp only [matchNum, hb, h1, h2, matchFrac_none ex hx, matchExpEnd_ok ex hx, Option.getD_none]
  | some F =>
    have hT : ∀ c r, ('.' :: (F ++ expPart ex)) = c :: r → isDigit c = false := by
      intro c r h
      simp only [List.cons.injEq] at h
      rw [← h.1]
      exact isDigit_dot
    obtain ⟨h1, h2⟩ := takeWhile_AD I _ hI hT
    have hb : numBody I (some F) ++ expPart ex = I ++ '.' :: (F ++ expPart ex) := by simp [numBody]
    simp only [matchNum, hb, h1, h2, matchFrac_shape F _ hF hE, matchExpEnd_ok ex hx, Option.getD_some]

theorem pyLook_digit (x : Char) (r : List Char) (hx : x.isDigit = true) : pyLook (x :: r) = true := by
  simp [pyLook, isDigit_of_digitVal hx]

theorem expSign_digit (x : Char) (r : List Char) (hx : x.isDigit = true) :
    expSign ((x :: r)) = (false, x :: r) := by
  obtain ⟨_, _, _, _, f5, f6⟩ := digit_facts hx
  have hp : x ≠ '+' := by simpa using f5
  have hm : x ≠ '-' := by simpa using f6
  unfold expSign
  split <;> simp_all

theorem pyMatch_shape (neg : Bool) (I : List Char) (fr : Option (List Char)) (ex : ExPart)
    (hI0 : I ≠ []) (hI : AD I) (hF : AD (fr.getD [])) (hx : ExOk ex) :
    pyMatch ((if neg then ['-'] else []) ++ numBody I fr ++ expPart ex) =
      some (.num neg I (fr.getD []) (exGroup ex)) := by
  have hm := matchNum_shape neg I fr ex hI hF hx
  obtain ⟨x, r, hbody, hxd⟩ := numBody_cons I fr ex hI0 hI
  rw [List.append_assoc, hbody]
  rw [hbody] at hm
  cases neg
  · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, pyMatch, expSign_digit x r hxd,
      pyLook_digit x r hxd]
    exact hm
  · have hsm : expSign (['-'] ++ x :: r) = (true, x :: r) := rfl
    simp only [↓reduceIte, pyMatch, hsm, pyLook_digit x r hxd]
    exact hm

theorem pyNum_shape (neg : Bool) (I F : List Char) (ex : ExPart) (hx : ExOk ex)
    (h1 : (I ++ F).length ≤ maxStrDigits)
    (h2 : ∀ ind sg D, ex = some (ind, sg, D) → D.length ≤ maxStrDigits) :
    pyNum neg I F (exGroup ex) = .ok (.fin neg (digitsValue (I ++ F)) (exVal ex - F.length)) := by
  have hl : intLimit (I ++ F).length = .ok () := by
    unfold intLimit; rw [if_neg (Nat.not_lt.mpr h1)]
  cases ex with
  | none =>
    simp only [pyNum, exGroup, hl, exVal]
    rfl
  | some t =>
    obtain ⟨ind, sg, D⟩ := t
    have hd : intLimit D.length = .ok () := by
      unfold intLimit; rw [if_neg (Nat.not_lt.mpr (h2 ind sg D rfl))]
    simp only [pyNum, exGroup, hd, hl, exVal, decide_eq_true_eq]
    rfl

theorem pyFilter_plain (s : List Char) (h : ∀ c ∈ s, Plain c) :
    (strip s).filter (· ≠ '_') = s := by
  rw [strip_plain s (fun c hc => (h c hc).2.2.2)]
  apply List.filter_eq_self.mpr
  intro c hc
  simpa using (h c hc).2.2.1

/-- `Decimal(str(d)) == d` in `_pydecimal`, for every value within the C limits
such that `str(d)` stays inside `int()`'s digit limit: the coefficient, plus the
up to six zeros of `0.00000ddd`, has at most 4300 digits, and so does a NaN
payload. The limit itself is `decimal-str-roundtrip-py`. -/
def StrRoundTripPyBounded : Prop :=
  ∀ d : Dec, InCLimits d →
    (∀ neg c e, d = .fin neg c e → numDigits c + 6 ≤ maxStrDigits) →
    (∀ neg s p, d = .nan neg s p → numDigits p ≤ maxStrDigits) →
    (pyStr d >>= pyParse) = .ok d

theorem pyParse_nan (neg sig : Bool) (p : Nat) (hd : numDigits p ≤ maxStrDigits) :
    pyParse ((if neg then ['-'] else []) ++ (if sig then "sNaN" else "NaN").toList ++ payDigits p) =
      .ok (.nan neg sig p) := by
  have hA := payDigits_AD p
  have hall : (payDigits p).all isDigit = true := by
    apply List.all_eq_true.mpr
    intro c hc
    exact isDigit_of_digitVal (hA c hc)
  have hws : expSign ((if neg then ['-'] else []) ++ (if sig then "sNaN" else "NaN").toList ++ payDigits p) =
      (neg, (if sig then "sNaN" else "NaN").toList ++ payDigits p) := by
    cases neg <;> cases sig <;> rfl
  have hv : digitsValue (payDigits p) = p := by
    unfold payDigits
    split
    · rename_i h; subst h; rfl
    · exact digitsValue_toDigits p
  have hnv : pyNanVal neg sig (payDigits p) = .ok (.nan neg sig p) := by
    have hl : intLimit (if payDigits p = [] then 1 else (payDigits p).length) = .ok () := by
      unfold intLimit
      rw [if_neg]
      split
      · simp [maxStrDigits]
      · rename_i hne
        unfold payDigits at hne ⊢
        split at hne
        · simp at hne
        · rename_i h0
          simp only [h0, ↓reduceIte]
          exact Nat.not_lt.mpr hd
    simp only [pyNanVal, hl, hv]
    rfl
  have hm : pyMatch ((if neg then ['-'] else []) ++ (if sig then "sNaN" else "NaN").toList ++ payDigits p) =
      some (.nan neg sig (payDigits p)) := by
    simp only [pyMatch, hws]
    cases sig
    · have h1 : pyLook ("NaN".toList ++ payDigits p) = false := rfl
      have h2 : matchWord "inf".toList ("NaN".toList ++ payDigits p) = none := rfl
      have h3 : matchSig ("NaN".toList ++ payDigits p) = (false, "NaN".toList ++ payDigits p) := rfl
      have h4 : matchWord "nan".toList ("NaN".toList ++ payDigits p) = some (payDigits p) := rfl
      simp only [Bool.false_eq_true, ↓reduceIte, h1, h2, matchNan, h3, h4, hall]
    · have h1 : pyLook ("sNaN".toList ++ payDigits p) = false := rfl
      have h2 : matchWord "inf".toList ("sNaN".toList ++ payDigits p) = none := rfl
      have h3 : matchSig ("sNaN".toList ++ payDigits p) = (true, "NaN".toList ++ payDigits p) := rfl
      have h4 : matchWord "nan".toList ("NaN".toList ++ payDigits p) = some (payDigits p) := rfl
      simp only [Bool.false_eq_true, ↓reduceIte, h1, h2, matchNan, h3, h4, hall]
  simp only [pyParse]
  rw [pyFilter_plain _ (nan_plain neg sig p), hm]
  exact hnv

theorem pyStrObj_num (neg : Bool) (I : List Char) (x : Int)
    (h : strLimit (x + (I.length : Int) - 1).natAbs = .ok ()) :
    pyStrObj ⟨neg, I, .num x⟩ = .ok (sciFinite neg I x true) := by
  simp only [pyStrObj]
  split <;> split <;> first
    | rfl
    | (rw [h]; rfl)
    | (exfalso; simp_all)

theorem strRoundTripPyBounded_proven : StrRoundTripPyBounded := by
  intro d hlim hb1 hb2
  cases d with
  | inf neg => cases neg <;> decide
  | nan neg sig p =>
    have hs : pyStr (.nan neg sig p) =
        .ok ((if neg then ['-'] else []) ++ (if sig then "sNaN" else "NaN").toList ++ payDigits p) := by
      cases sig <;> simp only [pyStr, Dec.toPyObj, pyStrObj, payDigits] <;> rfl
    rw [hs]
    exact pyParse_nan neg sig p (hb2 neg sig p rfl)
  | fin neg c e =>
    obtain ⟨I, fr, ex, h1, hI0, hI, hF, hx, hv, he, hfl, hl, hex⟩ := sci_shape neg c e
    obtain ⟨hl1, hl2, hl3⟩ := hlim
    have hb := hb1 neg c e rfl
    simp only [maxStrDigits] at hb
    have hn := numDigits_pos c
    simp only [mpdMaxEmax, mpdMinEtiny, mpdMinEmin, mpdMaxPrec] at hl2 hl3
    have hsl : ∀ m : Nat, m < 10 ^ 20 → numDigits m ≤ maxStrDigits := by
      intro m hm
      have := (numDigits_le_iff (n := m) (k := 20) (by decide)).mpr hm
      simp only [maxStrDigits]; omega
    have hsz : ∀ m : Nat, m < 10 ^ 20 → strLimit m = .ok () := by
      intro m hm
      unfold strLimit
      rw [if_neg (Nat.not_lt.mpr (hsl m hm))]
    have hs : pyStr (.fin neg c e) = .ok (sciFinite neg (Nat.toDigits 10 c) e true) :=
      pyStrObj_num neg _ e (hsz _ (by simp only [toDigits_len]; omega))
    rw [hs, h1]
    show pyParse _ = _
    simp only [pyParse]
    rw [pyFilter_plain _ (plain_body I fr ex hI hF hx neg), pyMatch_shape neg I fr ex hI0 hI hF hx]
    simp only
    rw [pyNum_shape neg I _ ex hx (by simp only [maxStrDigits]; omega) ?_, hv, he]
    intro ind sg D hD
    rcases hex with rfl | rfl
    · cases hD
    · simp only [sciExp, Option.some.injEq, Prod.mk.injEq] at hD
      rw [← hD.2.2]
      exact hsl _ (by omega)

end PyLean.Decimal
