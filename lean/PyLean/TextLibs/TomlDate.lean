import PyLean.TextLibs.TomlNum

/-!
Dates and times: `parse_value` through `RE_DATETIME`, `RE_LOCALTIME`, `match_to_datetime`,
`cached_tz` and `match_to_localtime` on every offset date-time, local date-time, local date and
local time TOML 1.1 allows (seconds optional).
-/

namespace PyLean.TextLibs.Toml

def pad2 (n : Nat) : Str := [48 + n / 10, 48 + n % 10]
def pad4 (n : Nat) : Str := [48 + n / 1000, 48 + n / 100 % 10, 48 + n / 10 % 10, 48 + n % 10]

/-- The positional value of decimal digits. -/
def digFold (ds : List Nat) : Nat := ds.foldl (fun a d => a * 10 + d) 0

/-- Fractional seconds truncated (not rounded) to microseconds, TOML 1.1 "Offset Date-Time":
the first six digits, padded with zeros. -/
def microsSpec (f : List Nat) : Nat := digFold ((f ++ List.replicate 6 0).take 6)

/-- `HH:MM`, optionally `:SS`, optionally `.` and fraction digits. -/
structure TimeTok where
  h : Nat
  mi : Nat
  sec : Option (Nat × Option (List Nat))

def fracTok : Option (List Nat) → Str
  | none => []
  | some f => 46 :: f.map (48 + ·)

def secTok : Option (Nat × Option (List Nat)) → Str
  | none => []
  | some (s, fr) => 58 :: pad2 s ++ fracTok fr

def TimeTok.enc (t : TimeTok) : Str := pad2 t.h ++ 58 :: pad2 t.mi ++ secTok t.sec

def TimeTok.ok (t : TimeTok) : Prop :=
  t.h < 24 ∧ t.mi < 60 ∧ ∀ s fr, t.sec = some (s, fr) → s < 60 ∧ ∀ f, fr = some f → f ≠ [] ∧ ∀ x ∈ f, x < 10

def TimeTok.secV (t : TimeTok) : Nat :=
  match t.sec with
  | none => 0
  | some (s, _) => s

def TimeTok.usV (t : TimeTok) : Nat :=
  match t.sec with
  | some (_, some f) => microsSpec f
  | _ => 0

/-- A time offset: none (local), `Z`/`z`, or `±HH:MM`. -/
inductive OffTok where
  | none
  | z (c : Nat)
  | ofs (sign oh om : Nat)

def OffTok.enc : OffTok → Str
  | .none => []
  | .z c => [c]
  | .ofs sg oh om => sg :: pad2 oh ++ 58 :: pad2 om

def OffTok.ok : OffTok → Prop
  | .none => True
  | .z c => c = 90 ∨ c = 122
  | .ofs sg oh om => (sg = 43 ∨ sg = 45) ∧ oh < 24 ∧ om < 60

/-- The offset in minutes: `Z` is UTC, `-HH:MM` is negative. -/
def OffTok.val : OffTok → Option Int
  | .none => Option.none
  | .z _ => some 0
  | .ofs sg oh om => some ((if sg = 43 then (1 : Int) else -1) * ((60 * oh + om : Nat) : Int))

/-- `YYYY-MM-DD`, optionally followed by `T`, `t` or a space, a time and an offset. -/
structure DtTok where
  y : Nat
  mo : Nat
  d : Nat
  time : Option (Nat × TimeTok × OffTok)

def timeTok : Option (Nat × TimeTok × OffTok) → Str
  | none => []
  | some (sep, tt, off) => sep :: tt.enc ++ off.enc

def DtTok.enc (t : DtTok) : Str := pad4 t.y ++ 45 :: pad2 t.mo ++ 45 :: pad2 t.d ++ timeTok t.time

/-- What `RE_DATETIME` and the TOML grammar allow: four-digit year, month 01-12, day 01-31. -/
def DtTok.ok (t : DtTok) : Prop :=
  t.y ≤ 9999 ∧ 1 ≤ t.mo ∧ t.mo ≤ 12 ∧ 1 ≤ t.d ∧ t.d ≤ 31 ∧
  ∀ sep tt off, t.time = some (sep, tt, off) → (sep = 84 ∨ sep = 116 ∨ sep = 32) ∧ tt.ok ∧ off.ok

def DtTok.val (t : DtTok) : TVal :=
  match t.time with
  | none => .date t.y t.mo t.d
  | some (_, tt, off) => .datetime t.y t.mo t.d tt.h tt.mi tt.secV tt.usV off.val

/-! ## Digits -/

theorem hourOk_pad : ∀ h < 24, hourOk (48 + h / 10) (48 + h % 10) = true := by decide
theorem sixtyOk_pad : ∀ m < 60, sixtyOk (48 + m / 10) (48 + m % 10) = true := by decide
theorem monthOk_pad : ∀ m < 13, 1 ≤ m → monthOk (48 + m / 10) (48 + m % 10) = true := by decide
theorem dayOk_pad : ∀ d < 32, 1 ≤ d → dayOk (48 + d / 10) (48 + d % 10) = true := by decide

theorem isDigit_48 {k : Nat} (h : k < 10) : isDigit (48 + k) = true := by
  simp [isDigit, inR]; omega

theorem decInt_pad2 (n : Nat) (h : n < 100) : decInt (pad2 n) = n := by
  simp [decInt, pad2]; omega

theorem decInt_pad4 (n : Nat) (h : n < 10000) : decInt (pad4 n) = n := by
  simp [decInt, pad4]; omega

theorem decInt_map (xs : List Nat) : ∀ a, (xs.map (48 + ·)).foldl (fun a c => a * 10 + (c - 48)) a =
    xs.foldl (fun a d => a * 10 + d) a := by
  induction xs with
  | nil => intro a; rfl
  | cons x xs ih => intro a; simp only [List.map_cons, List.foldl_cons]; rw [ih]; congr 1; omega

theorem digFold_lt : ∀ (xs : List Nat) (a : Nat), (∀ x ∈ xs, x < 10) →
    xs.foldl (fun a d => a * 10 + d) a < (a + 1) * 10 ^ xs.length
  | [], a, _ => by simp
  | x :: xs, a, h => by
    have hx := h x (by simp)
    have ih := digFold_lt xs (a * 10 + x) (fun y hy => h y (by simp [hy]))
    simp only [List.foldl_cons, List.length_cons, Nat.pow_succ]
    have : (a * 10 + x + 1) * 10 ^ xs.length ≤ (a + 1) * (10 ^ xs.length * 10) := by
      rw [show (a + 1) * (10 ^ xs.length * 10) = ((a + 1) * 10) * 10 ^ xs.length by
        rw [Nat.mul_comm (10 ^ xs.length) 10, Nat.mul_assoc]]
      exact Nat.mul_le_mul_right _ (by omega)
    omega

theorem microsSpec_lt (f : List Nat) (hf : ∀ x ∈ f, x < 10) : microsSpec f ≤ 999999 := by
  have hall : ∀ x ∈ (f ++ List.replicate 6 0).take 6, x < 10 := by
    intro x hx
    have := List.mem_of_mem_take hx
    simp only [List.mem_append, List.mem_replicate] at this
    rcases this with h | ⟨-, rfl⟩
    · exact hf x h
    · decide
  have hlen : ((f ++ List.replicate 6 0).take 6).length = 6 := by (simp) <;> omega
  have := digFold_lt _ 0 hall
  rw [hlen] at this
  unfold microsSpec digFold; omega

theorem micros_eq (f : List Nat) :
    decInt (ljust6 ((f.map (48 + ·)).take 6)) = microsSpec f := by
  unfold ljust6 decInt microsSpec digFold
  rw [← List.map_take, show List.replicate (6 - (List.map (48 + ·) (List.take 6 f)).length) 48 =
      (List.replicate (6 - (f.take 6).length) 0).map (48 + ·) by simp,
    ← List.map_append, decInt_map, List.take_append]
  congr 2
  simp only [List.take_replicate, List.length_take]
  first | done | (congr 1; omega)

/-! ## The patterns -/

theorem matchFrac_digits (f : List Nat) (hf : f ≠ []) (hd : ∀ x ∈ f, x < 10) (next : Str)
    (hn : ∀ c, next.head? = some c → isDigit c = false) :
    matchFrac (46 :: (f.map (48 + ·) ++ next)) = some ((f.map (48 + ·)).take 6, f.length + 1) := by
  have htw : (f.map (48 + ·) ++ next).takeWhile isDigit = f.map (48 + ·) :=
    takeWhile_append_stop (by intro x hx; simp at hx; obtain ⟨a, ha, rfl⟩ := hx; exact isDigit_48 (hd a ha)) hn
  have hne : (f.map (48 + ·)).isEmpty = false := by cases f <;> simp_all
  simp [matchFrac, htw, hne]

/-- What `RE_LOCALTIME` captures from a time token. -/
def TimeTok.m (t : TimeTok) : TimeM :=
  { hour := pad2 t.h, minute := pad2 t.mi,
    sec := t.sec.map (fun p => pad2 p.1),
    frac := match t.sec with
      | some (_, some f) => some ((f.map (48 + ·)).take 6)
      | _ => none,
    len := t.enc.length }

theorem matchTime_tok (t : TimeTok) (ht : t.ok) (next : Str)
    (hn : ∀ c, next.head? = some c → isDigit c = false ∧ c ≠ 58 ∧ c ≠ 46) :
    matchTime (t.enc ++ next) = some t.m := by
  obtain ⟨hh, hm, hs⟩ := ht
  have hcond : (hourOk (48 + t.h / 10) (48 + t.h % 10) && sixtyOk (48 + t.mi / 10) (48 + t.mi % 10)) = true := by
    simp [hourOk_pad _ hh, sixtyOk_pad _ hm]
  rcases hsec : t.sec with _ | ⟨s, fr⟩
  · -- no seconds: the next character is not `:`
    have henc : t.enc ++ next = (48 + t.h / 10) :: (48 + t.h % 10) :: 58 :: (48 + t.mi / 10) ::
        (48 + t.mi % 10) :: next := by simp [TimeTok.enc, pad2, hsec, secTok]
    rw [henc]; unfold matchTime; simp only [hcond, ite_true]
    cases next with
    | nil => simp [TimeTok.m, hsec, TimeTok.enc, secTok, pad2]
    | cons c r =>
      have := (hn c (by simp)).2.1
      cases r with
      | nil => simp [TimeTok.m, hsec, TimeTok.enc, secTok, pad2]
      | cons c2 r2 =>
        cases r2 with
        | nil => simp [TimeTok.m, hsec, TimeTok.enc, secTok, pad2]
        | cons c3 r3 => simp [TimeTok.m, hsec, TimeTok.enc, secTok, pad2, this]
  · obtain ⟨hs60, hfr⟩ := hs s fr hsec
    have h6 := sixtyOk_pad s hs60
    rcases hfrc : fr with _ | f
    · have henc : t.enc ++ next = (48 + t.h / 10) :: (48 + t.h % 10) :: 58 :: (48 + t.mi / 10) ::
          (48 + t.mi % 10) :: 58 :: (48 + s / 10) :: (48 + s % 10) :: next := by
        simp [TimeTok.enc, pad2, hsec, secTok, hfrc, fracTok]
      rw [henc]; unfold matchTime; simp only [hcond, ite_true, h6]
      have : matchFrac next = none := by
        cases next with
        | nil => rfl
        | cons c r =>
          have := (hn c (by simp)).2.2
          simp [matchFrac, this]
      simp [this, TimeTok.m, hsec, hfrc, TimeTok.enc, secTok, fracTok, pad2]
    · obtain ⟨hfne, hfd⟩ := hfr f hfrc
      have henc : t.enc ++ next = (48 + t.h / 10) :: (48 + t.h % 10) :: 58 :: (48 + t.mi / 10) ::
          (48 + t.mi % 10) :: 58 :: (48 + s / 10) :: (48 + s % 10) :: 46 :: (f.map (48 + ·) ++ next) := by
        simp [TimeTok.enc, pad2, hsec, secTok, hfrc, fracTok]
      rw [henc]; unfold matchTime; simp only [hcond, ite_true, h6]
      rw [matchFrac_digits f hfne hfd next (fun c hc => (hn c hc).1)]
      simp [TimeTok.m, hsec, hfrc, TimeTok.enc, secTok, fracTok, pad2]; omega

def OffTok.m : OffTok → OffM
  | .none => .none
  | .z _ => .zulu
  | .ofs sg oh om => .ofs sg (pad2 oh) (pad2 om)

theorem matchOffset_tok (o : OffTok) (ho : o.ok) (rest : Str) (hr : stopHead rest) :
    matchOffset (o.enc ++ rest) = (o.m, o.enc.length) := by
  cases o with
  | none =>
    simp only [OffTok.enc, List.nil_append, OffTok.m, List.length_nil]
    cases rest with
    | nil => rfl
    | cons z r =>
      have := hr z (by simp)
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  | z c =>
    rcases ho with rfl | rfl <;> rfl
  | ofs sg oh om =>
    obtain ⟨hsg, hoh, hom⟩ := ho
    have h1 := hourOk_pad oh hoh
    have h2 := sixtyOk_pad om hom
    simp only [OffTok.enc, pad2, List.cons_append, List.nil_append, OffTok.m]
    unfold matchOffset
    rcases hsg with rfl | rfl <;> simp [h1, h2]

theorem matchDatetime_tok (t : DtTok) (ht : t.ok) (rest : Str) (hr : stopHead rest)
    (hsp : t.time = none → ∀ r', rest = 32 :: r' → ∀ c, r'.head? = some c → isDigit c = false) :
    matchDatetime (t.enc ++ rest) = some
      { year := pad4 t.y, month := pad2 t.mo, day := pad2 t.d,
        time := t.time.map (fun p => (p.2.1.m, p.2.2.m)), len := t.enc.length } := by
  obtain ⟨hy, hmo1, hmo2, hd1, hd2, htime⟩ := ht
  have hcond : (isDigit (48 + t.y / 1000) && isDigit (48 + t.y / 100 % 10) && isDigit (48 + t.y / 10 % 10) &&
      isDigit (48 + t.y % 10) && monthOk (48 + t.mo / 10) (48 + t.mo % 10) &&
      dayOk (48 + t.d / 10) (48 + t.d % 10)) = true := by
    simp [isDigit_48 (show t.y / 1000 < 10 by omega), isDigit_48 (show t.y / 100 % 10 < 10 by omega),
      isDigit_48 (show t.y / 10 % 10 < 10 by omega), isDigit_48 (show t.y % 10 < 10 by omega),
      monthOk_pad _ (by omega) hmo1, dayOk_pad _ (by omega) hd1]
  have hst := stop_not_digit hr
  rcases htt : t.time with _ | ⟨sep, tt, off⟩
  · have henc : t.enc ++ rest = (48 + t.y / 1000) :: (48 + t.y / 100 % 10) :: (48 + t.y / 10 % 10) ::
        (48 + t.y % 10) :: 45 :: (48 + t.mo / 10) :: (48 + t.mo % 10) :: 45 :: (48 + t.d / 10) ::
        (48 + t.d % 10) :: rest := by simp [DtTok.enc, pad2, pad4, htt, timeTok]
    rw [henc]; unfold matchDatetime; simp only [hcond, ite_true]
    have hmt32 : ∀ r2, rest = 32 :: r2 → matchTime r2 = none := by
      intro r2 hr2; cases r2 with
      | nil => rfl
      | cons c r3 => exact matchTime_head (hsp htt (c :: r3) hr2 c rfl)
    cases hrest : rest with
    | nil => simp [DtTok.enc, pad2, pad4, htt, timeTok]
    | cons c r2 =>
      have hc := hr c (by simp [hrest])
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [hmt32 r2 hrest, DtTok.enc, pad2, pad4, htt, timeTok]
      all_goals simp [DtTok.enc, pad2, pad4, htt, timeTok]
  · obtain ⟨hsep, htok, hoff⟩ := htime sep tt off htt
    have hnext : ∀ c, (off.enc ++ rest).head? = some c → isDigit c = false ∧ c ≠ 58 ∧ c ≠ 46 := by
      intro c hc
      cases off with
      | none => have := hst c (by simpa [OffTok.enc] using hc); exact ⟨this.1, this.2.2.2.1, this.2.2.2.2.1⟩
      | z c' => simp [OffTok.enc] at hc; subst hc; rcases hoff with rfl | rfl <;> decide
      | ofs sg oh om => simp [OffTok.enc] at hc; subst hc; rcases hoff.1 with rfl | rfl <;> decide
    have hmt := matchTime_tok tt htok (off.enc ++ rest) hnext
    have hmo := matchOffset_tok off hoff rest hr
    have henc : t.enc ++ rest = (48 + t.y / 1000) :: (48 + t.y / 100 % 10) :: (48 + t.y / 10 % 10) ::
        (48 + t.y % 10) :: 45 :: (48 + t.mo / 10) :: (48 + t.mo % 10) :: 45 :: (48 + t.d / 10) ::
        (48 + t.d % 10) :: sep :: (tt.enc ++ (off.enc ++ rest)) := by
      simp [DtTok.enc, pad2, pad4, htt, timeTok]
    have hsepb : (sep == 84 || sep == 116 || sep == 32) = true := by
      rcases hsep with rfl | rfl | rfl <;> rfl
    have hdrop : List.drop tt.m.len (tt.enc ++ (off.enc ++ rest)) = off.enc ++ rest := by
      simp [TimeTok.m]
    rw [henc]; unfold matchDatetime; simp only [hcond, ite_true, hsepb, hmt, hdrop, hmo]
    simp [DtTok.enc, pad2, pad4, htt, timeTok, TimeTok.m]; omega

/-- Dates and times, TOML 1.1 "Offset Date-Time", "Local Date-Time", "Local Date" and "Local
Time", and the docs' conversion table: for every `YYYY-MM-DD` (month 01-12, day 01-31),
optionally with `T`, `t` or a space, `HH:MM`, optional seconds and fraction, and an optional `Z`
or `±HH:MM` offset (hour 00-23, minute 00-59), followed by nothing, whitespace (a space not
followed by a digit, for a date alone), a newline, `,`, `]`, `}` or `#`, `parse_value` returns
a `datetime.date`, or a `datetime.datetime` whose seconds default to 0, whose microseconds are
the first six fraction digits (truncated, zero-padded) and whose `tzinfo` is `None` (local),
UTC (`Z`) or the signed offset, when the date exists (year 1 or later, day within the month);
otherwise it raises `TOMLDecodeError` "Invalid date or datetime" at the token. Every `HH:MM`
local time token gives the corresponding `datetime.time`. -/
def DatetimeSpec : Prop :=
  (∀ (cfg : Cfg) (src : Str) (pos fuel : Nat) (t : DtTok) (rest : Str),
    t.ok → stopHead rest → (t.time = none → ∀ r', rest = 32 :: r' → ∀ c, r'.head? = some c → isDigit c = false) →
    src.drop pos = t.enc ++ rest →
    parseValue cfg src (fuel + 1) pos =
      if 1 ≤ t.y ∧ t.d ≤ daysInMonth t.y t.mo then .ok (pos + t.enc.length, t.val)
      else .error (tdeS "Invalid date or datetime" src pos)) ∧
  (∀ (cfg : Cfg) (src : Str) (pos fuel : Nat) (t : TimeTok) (rest : Str),
    t.ok → stopHead rest → src.drop pos = t.enc ++ rest →
    parseValue cfg src (fuel + 1) pos = .ok (pos + t.enc.length, .time t.h t.mi t.secV t.usV))

theorem matchDatetime_third {c0 c1 c2 : Nat} {t : Str} (h : isDigit c2 = false) :
    matchDatetime (c0 :: c1 :: c2 :: t) = none := by
  unfold matchDatetime; split
  · rename_i heq; simp at heq; obtain ⟨-, -, rfl, -⟩ := heq; simp [h]
  · rfl

theorem checkDate_ok {y m d : Nat} (hy : y ≤ 9999) (hm1 : 1 ≤ m) (hm2 : m ≤ 12) (hd1 : 1 ≤ d)
    (hv : 1 ≤ y ∧ d ≤ daysInMonth y m) : checkDate y m d = .ok () := by
  unfold checkDate
  have h1 : (decide (y < 1) || decide (y > 9999)) = false := by simp; omega
  have h2 : (decide (m < 1) || decide (m > 12)) = false := by simp; omega
  have h3 : (decide (d < 1) || decide (d > daysInMonth y m)) = false := by simp; omega
  simp only [h1, h2, h3, Bool.false_eq_true, ite_false]

theorem checkDate_err {y m d : Nat} (hv : ¬ (1 ≤ y ∧ d ≤ daysInMonth y m)) :
    ∃ msg, checkDate y m d = .error (.valueError msg) := by
  unfold checkDate
  by_cases hy : y < 1 ∨ y > 9999
  · exact ⟨_, by rw [if_pos (by simpa using hy)]⟩
  · rw [if_neg (by simpa using hy)]
    by_cases hm : m < 1 ∨ m > 12
    · exact ⟨_, by rw [if_pos (by simpa using hm)]⟩
    · rw [if_neg (by simpa using hm)]
      have hd : d < 1 ∨ d > daysInMonth y m := by omega
      exact ⟨_, by rw [if_pos (by simpa using hd)]⟩

theorem optBeq_ne {a b : Nat} (h : a ≠ b) : (some a == some b) = false := by simp [h]

theorem checkTime_ok {h mi s us : Nat} (h1 : h < 24) (h2 : mi < 60) (h3 : s < 60) (h4 : us ≤ 999999) :
    checkTime h mi s us = .ok () := by
  unfold checkTime
  simp [show ¬ h > 23 by omega, show ¬ mi > 59 by omega, show ¬ s > 59 by omega, show ¬ us > 999999 by omega]

theorem pad2_ne_nil (n : Nat) : (pad2 n).isEmpty = false := rfl

theorem tm_bounds (t : TimeTok) (ht : t.ok) : t.secV < 60 ∧ t.usV ≤ 999999 := by
  obtain ⟨hh, hmi, hs⟩ := ht
  unfold TimeTok.secV TimeTok.usV
  rcases hsec : t.sec with _ | ⟨s, fr⟩
  · simp
  · rcases hfr : fr with _ | f
    · simp; exact (hs s fr hsec).1
    · simp only; exact ⟨(hs s fr hsec).1, microsSpec_lt f ((hs s fr hsec).2 f hfr).2⟩

theorem take_map_ne (f : List Nat) (h : f ≠ []) : ((List.map (48 + ·) f).take 6).isEmpty = false := by
  cases f <;> simp_all

theorem localtime_tok (t : TimeTok) (ht : t.ok) :
    matchToLocaltime t.m = .ok (.time t.h t.mi t.secV t.usV) := by
  obtain ⟨b1, b2⟩ := tm_bounds t ht
  obtain ⟨hh, hmi, hs⟩ := ht
  rcases hsec : t.sec with _ | ⟨s, fr⟩
  · simp [matchToLocaltime, TimeTok.m, hsec, decInt_pad2 t.h (by omega), decInt_pad2 t.mi (by omega),
      checkTime_ok hh hmi (show 0 < 60 by decide) (show 0 ≤ 999999 by decide), TimeTok.secV, TimeTok.usV,
      bind, Except.bind, pure, Except.pure]
  · have hs60 := (hs s fr hsec).1
    rcases hfr : fr with _ | f
    · simp [matchToLocaltime, TimeTok.m, hsec, hfr, decInt_pad2 t.h (by omega), decInt_pad2 t.mi (by omega),
        decInt_pad2 s (by omega), pad2_ne_nil, checkTime_ok hh hmi hs60 (show 0 ≤ 999999 by decide),
        TimeTok.secV, TimeTok.usV, bind, Except.bind, pure, Except.pure]
    · obtain ⟨hfne, hfd⟩ := (hs s fr hsec).2 f hfr
      have hus := microsSpec_lt f hfd
      simp [matchToLocaltime, TimeTok.m, hsec, hfr, decInt_pad2 t.h (by omega), decInt_pad2 t.mi (by omega),
        decInt_pad2 s (by omega), pad2_ne_nil, take_map_ne f hfne, micros_eq, checkTime_ok hh hmi hs60 hus,
        TimeTok.secV, TimeTok.usV, bind, Except.bind, pure, Except.pure]

theorem cachedTz_tok (sg oh om : Nat) (hsg : sg = 43 ∨ sg = 45) (hoh : oh < 24) (hom : om < 60) :
    cachedTz (pad2 oh) (pad2 om) sg = .ok ((if sg = 43 then (1 : Int) else -1) * ((60 * oh + om : Nat) : Int)) := by
  simp only [cachedTz, decInt_pad2 oh (by omega), decInt_pad2 om (by omega)]
  rcases hsg with rfl | rfl
  · have : ¬ (((1 : Int) * (oh : Int) * 60 + 1 * (om : Int)).natAbs ≥ 24 * 60) := by omega
    simp only [show ((43 : Nat) == 43) = true from rfl, ite_true, this, ite_false]
    congr 1; omega
  · have : ¬ (((-1 : Int) * (oh : Int) * 60 + -1 * (om : Int)).natAbs ≥ 24 * 60) := by omega
    simp only [show ((45 : Nat) == 43) = false from rfl, Bool.false_eq_true, ite_false, this]
    rw [if_neg (by decide : ¬ (45 : Nat) = 43)]
    congr 1; omega

/-- What `RE_DATETIME` captures from a date token. -/
def DtTok.m (t : DtTok) : DtM :=
  { year := pad4 t.y, month := pad2 t.mo, day := pad2 t.d,
    time := t.time.map (fun p => (p.2.1.m, p.2.2.m)), len := t.enc.length }

/-- `match_to_datetime` on what `RE_DATETIME` captured from a token. -/
theorem datetime_tok (t : DtTok) (ht : t.ok) :
    ((1 ≤ t.y ∧ t.d ≤ daysInMonth t.y t.mo) → matchToDatetime t.m = .ok t.val) ∧
    (¬ (1 ≤ t.y ∧ t.d ≤ daysInMonth t.y t.mo) → ∃ msg, matchToDatetime t.m = .error (.valueError msg)) := by
  obtain ⟨hy, hmo1, hmo2, hd1, hd2, htime⟩ := ht
  have base := fun (v : Prop) => v
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · have hcd := checkDate_ok hy hmo1 hmo2 hd1 hv
    rcases htt : t.time with _ | ⟨sep, tt, off⟩
    · simp [matchToDatetime, DtTok.m, htt, decInt_pad4 t.y (by omega), decInt_pad2 t.mo (by omega),
        decInt_pad2 t.d (by omega), hcd, DtTok.val, bind, Except.bind, pure, Except.pure]
    · obtain ⟨hsep, ⟨hh, hmi, hs⟩, hoff⟩ := htime sep tt off htt
      have htz : ∀ v, off.val = v → (match off.m with
          | .ofs sg h mm => some <$> cachedTz h mm sg
          | .zulu => pure (some 0)
          | .none => pure none : Py (Option Int)) = .ok v := by
        intro v hv'; subst hv'
        cases off with
        | none => rfl
        | z c => rfl
        | ofs sg oh om =>
          obtain ⟨hsg, hoh, hom⟩ := hoff
          simp only [OffTok.m, cachedTz_tok sg oh om hsg hoh hom, OffTok.val]; rfl
      rcases hsec : tt.sec with _ | ⟨s, fr⟩
      · cases off <;>
        simp_all [matchToDatetime, DtTok.m, TimeTok.m, OffTok.m, decInt_pad4 t.y (by omega),
          decInt_pad2 t.mo (by omega), decInt_pad2 t.d (by omega), decInt_pad2 tt.h (by omega),
          decInt_pad2 tt.mi (by omega), checkTime_ok hh hmi (show 0 < 60 by decide) (show 0 ≤ 999999 by decide),
          cachedTz_tok, DtTok.val, OffTok.val, TimeTok.secV, TimeTok.usV, bind, Except.bind, pure,
          Except.pure, Functor.map, Except.map]
      · have hs60 := (hs s fr hsec).1
        rcases hfr : fr with _ | f
        · cases off <;>
          simp_all [matchToDatetime, DtTok.m, TimeTok.m, OffTok.m, decInt_pad4 t.y (by omega),
            decInt_pad2 t.mo (by omega), decInt_pad2 t.d (by omega), decInt_pad2 tt.h (by omega),
            decInt_pad2 tt.mi (by omega), decInt_pad2 s (by omega), pad2_ne_nil,
            checkTime_ok hh hmi hs60 (show 0 ≤ 999999 by decide),
            cachedTz_tok, DtTok.val, OffTok.val, TimeTok.secV, TimeTok.usV, bind, Except.bind, pure,
            Except.pure, Functor.map, Except.map]
        · obtain ⟨hfne, hfd⟩ := (hs s fr hsec).2 f hfr
          have hus := microsSpec_lt f hfd
          cases off <;>
          simp_all [matchToDatetime, DtTok.m, TimeTok.m, OffTok.m, decInt_pad4 t.y (by omega),
            decInt_pad2 t.mo (by omega), decInt_pad2 t.d (by omega), decInt_pad2 tt.h (by omega),
            decInt_pad2 tt.mi (by omega), decInt_pad2 s (by omega), pad2_ne_nil, take_map_ne f hfne, micros_eq,
            checkTime_ok hh hmi hs60 hus,
            cachedTz_tok, DtTok.val, OffTok.val, TimeTok.secV, TimeTok.usV, bind, Except.bind, pure,
            Except.pure, Functor.map, Except.map]
  · obtain ⟨msg, hmsg⟩ := checkDate_err hv
    refine ⟨msg, ?_⟩
    rcases htt : t.time with _ | ⟨sep, tt, off⟩
    · simp [matchToDatetime, DtTok.m, htt, decInt_pad4 t.y (by omega), decInt_pad2 t.mo (by omega),
        decInt_pad2 t.d (by omega), hmsg, bind, Except.bind]
    · obtain ⟨hsep, ⟨hh, hmi, hs⟩, hoff⟩ := htime sep tt off htt
      cases off <;>
      simp_all [matchToDatetime, DtTok.m, TimeTok.m, OffTok.m, decInt_pad4 t.y (by omega),
        decInt_pad2 t.mo (by omega), decInt_pad2 t.d (by omega), cachedTz_tok, OffTok.ok, bind, Except.bind,
        pure, Except.pure, Functor.map, Except.map]

theorem datetimeSpec_proven : DatetimeSpec := by
  refine ⟨?_, ?_⟩
  · intro cfg src pos fuel t rest ht hr hsp h
    have hm := matchDatetime_tok t ht rest hr hsp
    have hval := datetime_tok t ht
    change matchDatetime (t.enc ++ rest) = some t.m at hm
    obtain ⟨hy, hmo1, hmo2, hd1, hd2, htime⟩ := ht
    have hc0 : src.drop pos = (48 + t.y / 1000) :: ((pad4 t.y).tail ++ 45 :: pad2 t.mo ++ 45 :: pad2 t.d ++
        timeTok t.time ++ rest) := by rw [h]; simp [DtTok.enc, pad4]
    have hg := getElem?_of_drop hc0
    have hdig : 48 + t.y / 1000 ≠ 34 ∧ 48 + t.y / 1000 ≠ 39 ∧ 48 + t.y / 1000 ≠ 116 ∧ 48 + t.y / 1000 ≠ 102 ∧
        48 + t.y / 1000 ≠ 91 ∧ 48 + t.y / 1000 ≠ 123 := by omega
    rw [← h] at hm
    simp only [parseValue, hg, hm, optBeq_ne hdig.1, optBeq_ne hdig.2.1, optBeq_ne hdig.2.2.1,
      optBeq_ne hdig.2.2.2.1, optBeq_ne hdig.2.2.2.2.1, optBeq_ne hdig.2.2.2.2.2, Bool.false_and,
      Bool.false_eq_true, ite_false]
    by_cases hv : 1 ≤ t.y ∧ t.d ≤ daysInMonth t.y t.mo
    · rw [hval.1 hv, if_pos hv]; rfl
    · obtain ⟨msg, hmsg⟩ := hval.2 hv
      rw [hmsg, if_neg hv]
  · intro cfg src pos fuel t rest ht hr h
    have hst := stop_not_digit hr
    have hmt := matchTime_tok t ht rest (fun c hc => ⟨(hst c hc).1, (hst c hc).2.2.2.1, (hst c hc).2.2.2.2.1⟩)
    have hc0 : src.drop pos = (48 + t.h / 10) :: (48 + t.h % 10) :: 58 :: ((pad2 t.mi ++ secTok t.sec) ++ rest) := by
      rw [h]; simp [TimeTok.enc, pad2]
    have hg := getElem?_of_drop hc0
    have hd : matchDatetime (src.drop pos) = none := by rw [hc0]; exact matchDatetime_third (by decide)
    rw [← h] at hmt
    have hh := ht.1
    have hdig : 48 + t.h / 10 ≠ 34 ∧ 48 + t.h / 10 ≠ 39 ∧ 48 + t.h / 10 ≠ 116 ∧ 48 + t.h / 10 ≠ 102 ∧
        48 + t.h / 10 ≠ 91 ∧ 48 + t.h / 10 ≠ 123 := by omega
    simp only [parseValue, hg, hd, hmt, optBeq_ne hdig.1, optBeq_ne hdig.2.1, optBeq_ne hdig.2.2.1,
      optBeq_ne hdig.2.2.2.1, optBeq_ne hdig.2.2.2.2.1, optBeq_ne hdig.2.2.2.2.2, Bool.false_and,
      Bool.false_eq_true, ite_false, localtime_tok t ht]
    simp [Except.map, TimeTok.m]

end PyLean.TextLibs.Toml
