import PyLean.TextLibs.TomlStr

/-!
Numbers: `parse_value` on every integer and float token TOML 1.1 allows, through `RE_NUMBER`,
`match_to_number`, `int(s, 0)` and `make_safe_parse_float`.
-/

namespace PyLean.TextLibs.Toml

/-- A run of digits as written: the first digit, then each further digit with whether an `_`
comes before it. Each digit carries its case (`hexChar`), which only hex digits show. -/
structure Run where
  d0 : Nat
  up0 : Bool
  tail : List (Bool × Nat × Bool)

def tailEnc (t : Bool × Nat × Bool) : Str := (if t.1 then [95] else []) ++ [hexChar t.2.1 t.2.2]

def Run.enc (r : Run) : Str := hexChar r.d0 r.up0 :: r.tail.flatMap tailEnc

/-- The positional value of the digits in base `b`. -/
def Run.val (b : Nat) (r : Run) : Nat := r.tail.foldl (fun a t => a * b + t.2.1) r.d0

def Run.ok (b : Nat) (r : Run) : Prop := r.d0 < b ∧ ∀ t ∈ r.tail, t.2.1 < b

def signOk (s : Str) : Prop := s = [] ∨ s = [43] ∨ s = [45]

/-- A number token of TOML 1.1 "Integer" and "Float": a decimal integer (no leading zero), a
prefixed integer (`0x`, `0o`, `0b`, leading zeros allowed, no sign), a float (integer part, then
a fractional part, an exponent or both), or `inf`/`nan` with an optional sign. -/
inductive NumTok where
  | dec (sign : Str) (r : Run)
  | pre (letter base : Nat) (r : Run)
  | flt (sign : Str) (ip : Run) (frac : Option Run) (exp : Option (Nat × Str × Run))
  | special (sign : Str) (name : Str)

def fracEnc : Option Run → Str
  | some f => 46 :: f.enc
  | none => []

def expEnc : Option (Nat × Str × Run) → Str
  | some (e, es, er) => e :: es ++ er.enc
  | none => []

def NumTok.enc : NumTok → Str
  | .dec s r => s ++ r.enc
  | .pre l _ r => 48 :: l :: r.enc
  | .flt s ip fr ex => s ++ ip.enc ++ fracEnc fr ++ expEnc ex
  | .special s n => s ++ n

def NumTok.ok : NumTok → Prop
  | .dec s r => signOk s ∧ r.ok 10 ∧ (r.d0 = 0 → r.tail = [])
  | .pre l b r => ((l = 120 ∧ b = 16) ∨ (l = 111 ∧ b = 8) ∨ (l = 98 ∧ b = 2)) ∧ r.ok b
  | .flt s ip fr ex => signOk s ∧ ip.ok 10 ∧ (ip.d0 = 0 → ip.tail = []) ∧
      (∀ f, fr = some f → f.ok 10) ∧
      (∀ e es er, ex = some (e, es, er) → (e = 101 ∨ e = 69) ∧ signOk es ∧ er.ok 10) ∧
      (fr.isSome ∨ ex.isSome)
  | .special s n => signOk s ∧ (n = S "inf" ∨ n = S "nan")

/-- What a float token gives: `parse_float` is called with the token's text; its exception
propagates; a dict or list it returns raises `ValueError` (unless it is `float` itself). -/
def floatResult (pf : ParseFloat) (pos : Nat) (tok : Str) : Py (Nat × TVal) :=
  match pf.call tok with
  | .error e => .error e
  | .ok .dictOrList =>
    if pf.isFloat then .ok (pos + tok.length, .flt tok)
    else .error (.valueError "parse_float must not return dicts or lists")
  | .ok .other => .ok (pos + tok.length, .flt tok)

/-- The value TOML 1.1 gives each token, with Python's limit on decimal digits
(`sys.get_int_max_str_digits()`, counted without underscores; the docs' "Integers"
implementation detail) and none on power-of-two bases. -/
def NumTok.result (pf : ParseFloat) (maxD pos : Nat) : NumTok → Py (Nat × TVal)
  | .dec s r =>
    let n := r.tail.length + 1
    if n > 640 ∧ maxD > 0 ∧ n > maxD then .error (.valueError (limitMsg maxD n))
    else .ok (pos + (s ++ r.enc).length, .int (if s = [45] then -(r.val 10 : Int) else r.val 10))
  | .pre _ b r => .ok (pos + 2 + r.enc.length, .int (r.val b))
  | t@(.flt ..) => floatResult pf pos t.enc
  | t@(.special ..) => floatResult pf pos t.enc

/-- What may follow a value: nothing, whitespace, a newline, `,`, `]`, `}` or `#`. -/
def stopHead (rest : Str) : Prop :=
  ∀ c, rest.head? = some c → c = 32 ∨ c = 9 ∨ c = 10 ∨ c = 44 ∨ c = 93 ∨ c = 125 ∨ c = 35

/-! ## Runs -/

def basePred (b : Nat) : Nat → Bool :=
  if b = 16 then hexDigit else if b = 8 then isOct else if b = 2 then isBin else isDigit

theorem basePred_hexChar (b : Nat) (hb : b = 16 ∨ b = 8 ∨ b = 2 ∨ b = 10) :
    ∀ d < b, ∀ up, basePred b (hexChar d up) = true := by
  rcases hb with rfl | rfl | rfl | rfl <;> decide

theorem basePred_95 (b : Nat) : basePred b 95 = false := by
  unfold basePred
  by_cases h16 : b = 16
  · simp only [h16, ite_true]; decide
  · by_cases h8 : b = 8
    · simp only [h8, ite_true]; decide
    · by_cases h2 : b = 2
      · simp only [h16, h8, h2, ite_true, ite_false]; decide
      · simp only [h16, h8, h2, ite_false]; decide

theorem hexChar_ne_95 : ∀ d < 16, ∀ up, hexChar d up ≠ 95 := by decide
theorem hexChar_dec : ∀ d < 10, ∀ up, hexChar d up = 48 + d := by decide

theorem usRun_cons_pos {d : Nat → Bool} {c : Nat} {r : Str} (h : d c = true) :
    usRun d (c :: r) = usRun d r + 1 := by
  rw [usRun.eq_def]
  simp [h]

theorem usRun_us_pos {d : Nat → Bool} {c : Nat} {r : Str} (h95 : d 95 = false) (h : d c = true) :
    usRun d (95 :: c :: r) = usRun d r + 2 := by
  rw [usRun.eq_def]
  simp [h, h95]

theorem usRun_stop {d : Nat → Bool} {c : Nat} {r : Str} (h : d c = false) (h95 : c ≠ 95) :
    usRun d (c :: r) = 0 := by
  rw [usRun.eq_def]
  have : (c == 95) = false := by simp [h95]
  simp [h, this]

theorem usRun_tail (p : Nat → Bool) (hp95 : p 95 = false) (b : Nat) (hb : ∀ d < b, ∀ up, p (hexChar d up) = true) :
    ∀ (tail : List (Bool × Nat × Bool)), (∀ t ∈ tail, t.2.1 < b) → ∀ rest : Str,
    (∀ c, rest.head? = some c → p c = false ∧ c ≠ 95) →
    usRun p (tail.flatMap tailEnc ++ rest) = (tail.flatMap tailEnc).length
  | [], _, rest, hr => by
    cases rest with
    | nil => rfl
    | cons c r =>
      obtain ⟨h1, h2⟩ := hr c rfl
      exact usRun_stop h1 h2
  | (u, d, up) :: ts, ht, rest, hr => by
    have hd := hb d (ht (u, d, up) (by simp)) up
    have ih := usRun_tail p hp95 b hb ts (fun t h => ht t (by simp [h])) rest hr
    cases u with
    | true =>
      simp only [List.flatMap_cons, tailEnc, ite_true, List.append_assoc, List.cons_append, List.nil_append,
        List.singleton_append]
      rw [usRun_us_pos hp95 hd, ih]; simp
    | false =>
      simp only [List.flatMap_cons, tailEnc, Bool.false_eq_true, ite_false, List.nil_append,
        List.singleton_append, List.cons_append]
      rw [usRun_cons_pos hd, ih]; simp

theorem dRun_run (p : Nat → Bool) (hp95 : p 95 = false) (b : Nat) (hb : ∀ d < b, ∀ up, p (hexChar d up) = true)
    (r : Run) (hr : r.ok b) (rest : Str) (hrest : ∀ c, rest.head? = some c → p c = false ∧ c ≠ 95) :
    dRun p (r.enc ++ rest) = some r.enc.length := by
  have := usRun_tail p hp95 b hb r.tail hr.2 rest hrest
  simp [Run.enc, dRun, hb r.d0 hr.1 r.up0, this]

theorem filter_tail (b : Nat) (hb : b ≤ 16) : ∀ (tail : List (Bool × Nat × Bool)), (∀ t ∈ tail, t.2.1 < b) →
    (tail.flatMap tailEnc).filter (· != 95) = tail.map (fun t => hexChar t.2.1 t.2.2)
  | [], _ => rfl
  | (u, d, up) :: ts, ht => by
    have hdb : d < b := ht (u, d, up) (by simp)
    have hd : hexChar d up ≠ 95 := hexChar_ne_95 d (by omega) up
    have ih := filter_tail b hb ts (fun t h => ht t (by simp [h]))
    cases u <;> simp [tailEnc, List.filter_append, hd, ih]

theorem foldl_hexVal (b : Nat) (hb : b ≤ 16) : ∀ (tail : List (Bool × Nat × Bool)) (a : Nat),
    (∀ t ∈ tail, t.2.1 < b) →
    (tail.map (fun t => hexChar t.2.1 t.2.2)).foldl (fun a c => a * b + hexVal c) a =
      tail.foldl (fun a t => a * b + t.2.1) a
  | [], _, _ => rfl
  | (u, d, up) :: ts, a, ht => by
    have hd : d < b := ht (u, d, up) (by simp)
    simp only [List.map_cons, List.foldl_cons]
    rw [hexVal_hexChar d (by omega) up]
    exact foldl_hexVal b hb ts _ (fun t h => ht t (by simp [h]))

theorem digitsVal_run (b : Nat) (hb : b ≤ 16) (r : Run) (hr : r.ok b) : digitsVal b r.enc = r.val b := by
  have hd0 : hexChar r.d0 r.up0 ≠ 95 := hexChar_ne_95 _ (by have := hr.1; omega) _
  simp only [digitsVal, Run.enc, List.filter_cons, hd0, bne_iff_ne, ne_eq, not_false_eq_true,
    decide_true, ite_true, filter_tail b hb r.tail hr.2, List.foldl_cons]
  rw [Nat.zero_mul, Nat.zero_add, hexVal_hexChar _ (by have := hr.1; omega)]
  exact foldl_hexVal b hb r.tail _ hr.2

theorem ndigits_run (b : Nat) (hb : b ≤ 16) (r : Run) (hr : r.ok b) :
    (r.enc.filter (· != 95)).length = r.tail.length + 1 := by
  have hd0 : hexChar r.d0 r.up0 ≠ 95 := hexChar_ne_95 _ (by have := hr.1; omega) _
  simp [Run.enc, List.filter_cons, hd0, filter_tail b hb r.tail hr.2]

theorem run_chars (b : Nat) (hb : b ≤ 16) (r : Run) (hr : r.ok b) :
    ∀ c ∈ r.enc, c = 95 ∨ ∃ d < b, ∃ up, c = hexChar d up := by
  intro c hc
  simp only [Run.enc, List.mem_cons, List.mem_flatMap] at hc
  rcases hc with rfl | ⟨⟨u, d, up⟩, ht, hc⟩
  · exact Or.inr ⟨_, hr.1, _, rfl⟩
  · cases u <;> simp [tailEnc] at hc
    · exact Or.inr ⟨d, hr.2 _ ht, up, hc⟩
    · rcases hc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr ⟨d, hr.2 _ ht, up, rfl⟩

theorem hexChar_props : ∀ d < 16, ∀ up, hexChar d up ≠ 45 ∧ hexChar d up ≠ 58 ∧ hexChar d up ≠ 46 ∧
    hexChar d up ≠ 34 ∧ hexChar d up ≠ 39 ∧ hexChar d up ≠ 91 ∧ hexChar d up ≠ 123 := by decide

/-! ## The date and time patterns do not match a number -/

theorem matchDatetime_head {c : Nat} {t : Str} (h : isDigit c = false) : matchDatetime (c :: t) = none := by
  unfold matchDatetime; split
  · rename_i heq; simp at heq; obtain ⟨rfl, -⟩ := heq; simp [h]
  · rfl

theorem matchDatetime_second {c0 c1 : Nat} {t : Str} (h : isDigit c1 = false) :
    matchDatetime (c0 :: c1 :: t) = none := by
  unfold matchDatetime; split
  · rename_i heq; simp at heq; obtain ⟨-, rfl, -⟩ := heq; simp [h]
  · rfl

/-- `RE_DATETIME` needs four digits and `-`; a run without `-` followed by a non-digit that is
not `-` cannot give them. -/
theorem matchDatetime_none {a b : Str} (ha : 45 ∉ a)
    (hb : ∀ c, b.head? = some c → isDigit c = false ∧ c ≠ 45) : matchDatetime (a ++ b) = none := by
  unfold matchDatetime; split
  · rename_i y1 y2 y3 y4 mo1 mo2 d1 d2 r heq
    have key : (isDigit y1 && isDigit y2 && isDigit y3 && isDigit y4) = false := by
      match a, ha, heq with
      | [], _, heq =>
        have heq' : b = y1 :: y2 :: y3 :: y4 :: 45 :: mo1 :: mo2 :: 45 :: d1 :: d2 :: r := by simpa using heq
        have := (hb y1 (by simp [heq'])).1; simp [this]
      | [x1], _, heq =>
        have heq' : x1 = y1 ∧ b = y2 :: y3 :: y4 :: 45 :: mo1 :: mo2 :: 45 :: d1 :: d2 :: r := by
          simpa using heq
        have := (hb y2 (by simp [heq'.2])).1; simp [this]
      | [x1, x2], _, heq =>
        have heq' : x1 = y1 ∧ x2 = y2 ∧ b = y3 :: y4 :: 45 :: mo1 :: mo2 :: 45 :: d1 :: d2 :: r := by
          simpa using heq
        have := (hb y3 (by simp [heq'.2.2])).1; simp [this]
      | [x1, x2, x3], _, heq =>
        have heq' : x1 = y1 ∧ x2 = y2 ∧ x3 = y3 ∧ b = y4 :: 45 :: mo1 :: mo2 :: 45 :: d1 :: d2 :: r := by
          simpa using heq
        have := (hb y4 (by simp [heq'.2.2.2])).1; simp [this]
      | [x1, x2, x3, x4], _, heq =>
        have heq' : x1 = y1 ∧ x2 = y2 ∧ x3 = y3 ∧ x4 = y4 ∧ b = 45 :: mo1 :: mo2 :: 45 :: d1 :: d2 :: r := by
          simpa using heq
        exact absurd rfl (hb 45 (by simp [heq'.2.2.2.2])).2
      | x1 :: x2 :: x3 :: x4 :: x5 :: t, ha, heq =>
        have heq' : x1 = y1 ∧ x2 = y2 ∧ x3 = y3 ∧ x4 = y4 ∧ x5 = 45 ∧
            t ++ b = mo1 :: mo2 :: 45 :: d1 :: d2 :: r := by simpa using heq
        rw [heq'.2.2.2.2.1] at ha; simp at ha
    simp [key]
  · rfl

/-- `_TIME_RE_STR` needs `HH:`; a run without `:` followed by a non-digit that is not `:` cannot
give it. -/
theorem matchTime_none {a b : Str} (ha : 58 ∉ a)
    (hb : ∀ c, b.head? = some c → isDigit c = false ∧ c ≠ 58) : matchTime (a ++ b) = none := by
  unfold matchTime; split
  · rename_i h1 h2 m1 m2 r heq
    have hh : hourOk h1 h2 = true → isDigit h1 = true ∧ isDigit h2 = true := by
      unfold hourOk isDigit inR; intro h; simp at h ⊢; omega
    have key : hourOk h1 h2 = false := by
      match a, ha, heq with
      | [], _, heq =>
        have heq' : b = h1 :: h2 :: 58 :: m1 :: m2 :: r := by simpa using heq
        have := (hb h1 (by simp [heq'])).1
        cases hk : hourOk h1 h2
        · rfl
        · exact absurd (hh hk).1 (by simp [this])
      | [x], _, heq =>
        have heq' : x = h1 ∧ b = h2 :: 58 :: m1 :: m2 :: r := by simpa using heq
        have := (hb h2 (by simp [heq'.2])).1
        cases hk : hourOk h1 h2
        · rfl
        · exact absurd (hh hk).2 (by simp [this])
      | [x, y], _, heq =>
        have heq' : x = h1 ∧ y = h2 ∧ b = 58 :: m1 :: m2 :: r := by simpa using heq
        exact absurd rfl (hb 58 (by simp [heq'.2.2])).2
      | x :: y :: z :: t, ha, heq =>
        have heq' : x = h1 ∧ y = h2 ∧ z = 58 ∧ t ++ b = m1 :: m2 :: r := by simpa using heq
        rw [heq'.2.2.1] at ha; simp at ha
    simp [key]
  · rfl

/-! ## `RE_NUMBER`, piece by piece -/

def nAlt1 (s : Str) : Option Nat :=
  match s with
  | 48 :: 120 :: r => (dRun hexDigit r).map (· + 2)
  | 48 :: 98 :: r => (dRun isBin r).map (· + 2)
  | 48 :: 111 :: r => (dRun isOct r).map (· + 2)
  | _ => none

def nSign (s : Str) : Nat :=
  match s with
  | 43 :: _ | 45 :: _ => 1
  | _ => 0

def nIp (s1 : Str) : Option Nat :=
  match s1 with
  | 48 :: _ => some 1
  | c :: r => if inR 49 57 c then some (usRun isDigit r + 1) else none
  | [] => none

def nFr (s2 : Str) : Nat :=
  match s2 with
  | 46 :: r => ((dRun isDigit r).map (· + 1)).getD 0
  | _ => 0

def nEx (s3 : Str) : Nat :=
  match s3 with
  | e :: r =>
    if e == 101 || e == 69 then
      let es := match r with
        | 43 :: _ | 45 :: _ => 1
        | _ => 0
      ((dRun isDigit (r.drop es)).map (· + 1 + es)).getD 0
    else 0
  | [] => 0

theorem matchNumber_eq (s : Str) : matchNumber s =
    match nAlt1 s with
    | some n => some ⟨n, false⟩
    | none =>
      match nIp (s.drop (nSign s)) with
      | none => none
      | some ipn =>
        let fr := nFr ((s.drop (nSign s)).drop ipn)
        let ex := nEx (((s.drop (nSign s)).drop ipn).drop fr)
        some ⟨nSign s + ipn + fr + ex, fr + ex > 0⟩ := rfl

theorem stop_not_digit {rest : Str} (h : stopHead rest) :
    ∀ c, rest.head? = some c → isDigit c = false ∧ c ≠ 95 ∧ c ≠ 45 ∧ c ≠ 58 ∧ c ≠ 46 ∧ c ≠ 101 ∧
      c ≠ 69 ∧ c ≠ 120 ∧ c ≠ 98 ∧ c ≠ 111 ∧ hexDigit c = false := by
  intro c hc
  rcases h c hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem nIp_run (r : Run) (hr : r.ok 10) (h0 : r.d0 = 0 → r.tail = []) (next : Str)
    (hn : ∀ c, next.head? = some c → isDigit c = false ∧ c ≠ 95) :
    nIp (r.enc ++ next) = some r.enc.length := by
  by_cases hd : r.d0 = 0
  · have ht := h0 hd
    simp [Run.enc, hd, ht, hexChar, nIp]
  · have hc := hexChar_dec r.d0 hr.1 r.up0
    have hu := usRun_tail isDigit (by decide) 10 (fun d hd up => by
      rw [hexChar_dec d hd up]; simp [isDigit, inR]; omega) r.tail hr.2 next hn
    have h48 : hexChar r.d0 r.up0 ≠ 48 := by omega
    have hin : inR 49 57 (hexChar r.d0 r.up0) = true := by
      rw [hc]; have := hr.1; simp [inR]; omega
    simp only [Run.enc, List.cons_append]
    unfold nIp; split
    · rename_i heq; simp at heq; exact absurd heq.1 h48
    · rename_i c rr heq
      simp at heq; obtain ⟨rfl, rfl⟩ := heq
      simp [hin, hu]
    · simp at *

theorem nFr_run (f : Run) (hf : f.ok 10) (next : Str)
    (hn : ∀ c, next.head? = some c → isDigit c = false ∧ c ≠ 95) :
    nFr (46 :: (f.enc ++ next)) = f.enc.length + 1 := by
  have := dRun_run isDigit (by decide) 10 (fun d hd up => by
    rw [hexChar_dec d hd up]; simp [isDigit, inR]; omega) f hf next hn
  simp [nFr, this]

theorem nFr_none {s2 : Str} (h : ∀ c, s2.head? = some c → c ≠ 46) : nFr s2 = 0 := by
  unfold nFr; split
  · exact absurd rfl (h 46 (by simp))
  · rfl

theorem nEx_run (e : Nat) (es : Str) (er : Run) (he : e = 101 ∨ e = 69) (hes : signOk es)
    (hr : er.ok 10) (rest : Str) (hn : ∀ c, rest.head? = some c → isDigit c = false ∧ c ≠ 95) :
    nEx (e :: es ++ er.enc ++ rest) = es.length + er.enc.length + 1 := by
  have hd := dRun_run isDigit (by decide) 10 (fun d hd up => by
    rw [hexChar_dec d hd up]; simp [isDigit, inR]; omega) er hr rest hn
  have hee : (e == 101 || e == 69) = true := by rcases he with rfl | rfl <;> rfl
  have hfirst : ∃ c t, er.enc = c :: t ∧ isDigit c = true := by
    refine ⟨_, _, rfl, ?_⟩; rw [hexChar_dec _ hr.1]; have := hr.1; simp [isDigit, inR]; omega
  obtain ⟨c, t, het, hcd⟩ := hfirst
  have hc4 : c ≠ 43 ∧ c ≠ 45 := by
    constructor <;> intro e' <;> subst e' <;> simp [isDigit, inR] at hcd
  rcases hes with rfl | rfl | rfl
  · rw [het] at hd
    simp only [List.nil_append, nEx, hee, ite_true, het, List.cons_append]
    split
    · rename_i heq; simp at heq; exact absurd heq.1 hc4.1
    · rename_i heq; simp at heq; exact absurd heq.1 hc4.2
    · simp only [List.drop_zero]; rw [← List.cons_append, hd]; simp
  · simp [nEx, hee, hd]; omega
  · simp [nEx, hee, hd]; omega

theorem nEx_none {s3 : Str} (h : ∀ c, s3.head? = some c → c ≠ 101 ∧ c ≠ 69) : nEx s3 = 0 := by
  unfold nEx; split
  · rename_i e r
    have := h e (by simp)
    have : (e == 101 || e == 69) = false := by simp [this.1, this.2]
    simp [this]
  · rfl

theorem nAlt1_none {s : Str} (h1 : ∀ t, s ≠ 48 :: 120 :: t) (h2 : ∀ t, s ≠ 48 :: 98 :: t)
    (h3 : ∀ t, s ≠ 48 :: 111 :: t) : nAlt1 s = none := by
  unfold nAlt1; split
  · exact absurd rfl (h1 _)
  · exact absurd rfl (h2 _)
  · exact absurd rfl (h3 _)
  · rfl

theorem nAlt1_head {c : Nat} {t : Str} (h : c ≠ 48) : nAlt1 (c :: t) = none :=
  nAlt1_none (fun _ e => h (List.cons.inj e).1) (fun _ e => h (List.cons.inj e).1)
    (fun _ e => h (List.cons.inj e).1)

theorem nSign_sign {sg x : Str} (hs : signOk sg) (hx : sg = [] → ∀ c, x.head? = some c → c ≠ 43 ∧ c ≠ 45) :
    nSign (sg ++ x) = sg.length := by
  rcases hs with rfl | rfl | rfl
  · unfold nSign
    cases x with
    | nil => rfl
    | cons c t =>
      have := hx rfl c (by simp)
      simp only [List.nil_append]
      split <;> simp_all
  · rfl
  · rfl

theorem run_head (r : Run) (hr : r.ok 10) : ∃ t, r.enc = (48 + r.d0) :: t ∧ isDigit (48 + r.d0) = true ∧
    48 + r.d0 ≠ 43 ∧ 48 + r.d0 ≠ 45 := by
  refine ⟨_, by rw [Run.enc, hexChar_dec _ hr.1], ?_, ?_, ?_⟩ <;> have := hr.1 <;> simp [isDigit, inR] <;> omega

theorem run_no (b : Nat) (hb : b ≤ 16) (r : Run) (hr : r.ok b) (c : Nat)
    (hc : c ≠ 95 ∧ ∀ d < 16, ∀ up, hexChar d up ≠ c) : c ∉ r.enc := by
  intro m
  rcases run_chars b hb r hr c m with h | ⟨d, hd, up, h⟩
  · exact hc.1 h
  · exact hc.2 d (by omega) up h.symm

theorem no45 (b : Nat) (hb : b ≤ 16) (r : Run) (hr : r.ok b) : 45 ∉ r.enc :=
  run_no b hb r hr 45 ⟨by decide, by decide⟩

theorem no58 (b : Nat) (hb : b ≤ 16) (r : Run) (hr : r.ok b) : 58 ∉ r.enc :=
  run_no b hb r hr 58 ⟨by decide, by decide⟩

theorem matchTime_head {c : Nat} {t : Str} (h : isDigit c = false) : matchTime (c :: t) = none := by
  unfold matchTime; split
  · rename_i h1 h2 m1 m2 r heq
    simp at heq; obtain ⟨rfl, -⟩ := heq
    have : hourOk c h2 = false := by
      revert h; unfold hourOk isDigit inR; intro h; simp at h ⊢; omega
    simp [this]
  · rfl

theorem parseValue_num {cfg : Cfg} {src : Str} {pos fuel c0 : Nat} {t : Str} {m : NumM}
    (h : src.drop pos = c0 :: t) (hc : c0 ≠ 34 ∧ c0 ≠ 39 ∧ c0 ≠ 116 ∧ c0 ≠ 102 ∧ c0 ≠ 91 ∧ c0 ≠ 123)
    (hd : matchDatetime (src.drop pos) = none) (ht : matchTime (src.drop pos) = none)
    (hm : matchNumber (src.drop pos) = some m) :
    parseValue cfg src (fuel + 1) pos =
      (matchToNumber cfg (sl src pos (pos + m.len)) m).map (fun v => (pos + m.len, v)) := by
  have hg := getElem?_of_drop h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc
  simp [parseValue, hg, hd, ht, hm, h1, h2, h3, h4, h5, h6]

theorem parseValue_special {cfg : Cfg} {src : Str} {pos fuel c0 : Nat} {t : Str}
    (h : src.drop pos = c0 :: t) (hc : c0 ≠ 34 ∧ c0 ≠ 39 ∧ c0 ≠ 116 ∧ c0 ≠ 102 ∧ c0 ≠ 91 ∧ c0 ≠ 123)
    (hd : matchDatetime (src.drop pos) = none) (ht : matchTime (src.drop pos) = none)
    (hm : matchNumber (src.drop pos) = none) :
    parseValue cfg src (fuel + 1) pos =
      let firstThree := sl src pos (pos + 3)
      if firstThree == S "inf" || firstThree == S "nan" then do
        cfg.pf firstThree
        pure (pos + 3, .flt firstThree)
      else
        let firstFour := sl src pos (pos + 4)
        if firstFour == S "-inf" || firstFour == S "+inf" || firstFour == S "-nan" ||
            firstFour == S "+nan" then do
          cfg.pf firstFour
          pure (pos + 4, .flt firstFour)
        else .error (tdeS "Invalid value" src pos) := by
  have hg := getElem?_of_drop h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc
  simp only [parseValue, hg, hd, ht, hm]
  simp [h1, h2, h3, h4, h5, h6]

theorem pf_floatResult (pf : ParseFloat) (maxK maxD pos : Nat) (tok : Str) :
    (do (mkCfg pf maxK maxD).pf tok; pure (pos + tok.length, TVal.flt tok) : Py (Nat × TVal)) =
      floatResult pf pos tok := by
  rcases pf with ⟨isF, call⟩
  simp only [mkCfg, makeSafeParseFloat, floatResult]
  cases isF <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> cases call tok with
    | error e => rfl
    | ok v => cases v <;> rfl

theorem map_pf {cfg : Cfg} (g : Str) (f : TVal → Nat × TVal) :
    (do cfg.pf g; pure (TVal.flt g) : Py TVal).map f = (do cfg.pf g; pure (f (.flt g))) := by
  cases cfg.pf g <;> rfl

/-- Numbers, TOML 1.1 "Integer" and "Float": for every number token TOML allows, followed by
nothing, whitespace, a newline, `,`, `]`, `}` or `#`, `parse_value` returns the position after
it and (a) for a decimal integer, its signed positional value, or the `ValueError` of
`int()`'s digit limit when it has more digits (underscores not counted) than
`sys.get_int_max_str_digits()` allows; (b) for `0x`, `0o`, `0b` integers (any case, leading
zeros, underscores), their value, with no digit limit; (c) for a float (fraction, exponent or
both) or `inf`/`nan` with an optional sign, the object `parse_float` returns when called with
exactly the token's text, `parse_float`'s own exception, or `ValueError` "parse_float must not
return dicts or lists" when it returns a dict or list (unless it is `float` itself). -/
def NumberSpec : Prop :=
  ∀ (pf : ParseFloat) (maxK maxD : Nat) (src : Str) (pos fuel : Nat) (t : NumTok) (rest : Str),
    t.ok → stopHead rest → src.drop pos = t.enc ++ rest →
    parseValue (mkCfg pf maxK maxD) src (fuel + 1) pos = t.result pf maxD pos

/-- The decimal branch of `intBase0` once the sign is read. -/
def intBody (maxD : Nat) (neg : Bool) (body : Str) : Py Int :=
  let digits := (body.filter (· != 95)).length
  if digits > 640 && maxD > 0 && digits > maxD then .error (.valueError (limitMsg maxD digits))
  else
    let v : Int := digitsVal 10 body
    .ok (if neg then -v else v)

theorem intBase0_neg (maxD : Nat) (b : Str) : intBase0 maxD (45 :: b) = intBody maxD true b := rfl
theorem intBase0_pos (maxD : Nat) (b : Str) : intBase0 maxD (43 :: b) = intBody maxD false b := rfl
theorem intBase0_zero (maxD : Nat) : intBase0 maxD [48] = intBody maxD false [48] := rfl

theorem intBase0_plain (maxD c : Nat) (t : Str) (h48 : c ≠ 48) (h43 : c ≠ 43) (h45 : c ≠ 45) :
    intBase0 maxD (c :: t) = intBody maxD false (c :: t) := by
  unfold intBase0
  split <;> try simp_all
  split <;> simp_all [intBody]

theorem number_dec (pf : ParseFloat) (maxK maxD : Nat) (src : Str) (pos fuel : Nat) (sg : Str) (r : Run)
    (rest : Str) (hok : (NumTok.dec sg r).ok) (hrest : stopHead rest) (h : src.drop pos = (sg ++ r.enc) ++ rest) :
    parseValue (mkCfg pf maxK maxD) src (fuel + 1) pos = (NumTok.dec sg r).result pf maxD pos := by
  obtain ⟨hs, hr, h0⟩ := hok
  have hst := stop_not_digit hrest
  obtain ⟨rt, hre, hdig, h43, h45⟩ := run_head r hr
  have hstop2 : ∀ c, rest.head? = some c → isDigit c = false ∧ c ≠ 95 := fun c hc => ⟨(hst c hc).1, (hst c hc).2.1⟩
  -- the first character and the two date patterns
  have hcases : (∃ c0 tt, src.drop pos = c0 :: tt ∧ (c0 ≠ 34 ∧ c0 ≠ 39 ∧ c0 ≠ 116 ∧ c0 ≠ 102 ∧ c0 ≠ 91 ∧ c0 ≠ 123)) ∧
      matchDatetime (src.drop pos) = none := by
    rcases hs with rfl | rfl | rfl
    · refine ⟨⟨48 + r.d0, rt ++ rest, by rw [h, hre]; rfl, by have := hr.1; omega⟩, ?_⟩
      rw [h, List.nil_append]
      exact matchDatetime_none (no45 10 (by omega) r hr) (fun c hc => ⟨(hst c hc).1, (hst c hc).2.2.1⟩)
    · exact ⟨⟨43, _, by rw [h]; rfl, by decide⟩, by rw [h]; exact matchDatetime_head (by decide)⟩
    · exact ⟨⟨45, _, by rw [h]; rfl, by decide⟩, by rw [h]; exact matchDatetime_head (by decide)⟩
  obtain ⟨⟨c0, tt, hc0, hc⟩, hd⟩ := hcases
  have ht : matchTime (src.drop pos) = none := by
    rw [h]; refine matchTime_none ?_ (fun c hc => ⟨(hst c hc).1, (hst c hc).2.2.2.1⟩)
    simp only [List.mem_append, not_or]
    refine ⟨?_, no58 10 (by omega) r hr⟩
    rcases hs with rfl | rfl | rfl <;> decide
  have hm : matchNumber (src.drop pos) = some ⟨(sg ++ r.enc).length, false⟩ := by
    rw [h, matchNumber_eq]
    have ha1 : nAlt1 (sg ++ r.enc ++ rest) = none := by
      rcases hs with rfl | rfl | rfl
      · by_cases hd0 : r.d0 = 0
        · have hrt := h0 hd0
          have : r.enc = [48] := by simp [Run.enc, hd0, hrt, hexChar]
          rw [List.nil_append, this]
          cases rest with
          | nil => rfl
          | cons c t2 =>
            obtain ⟨-, -, -, -, -, -, -, h120, h98, h111, -⟩ := hst c (by simp)
            exact nAlt1_none (fun _ e => h120 (List.cons.inj (List.cons.inj e).2).1)
              (fun _ e => h98 (List.cons.inj (List.cons.inj e).2).1)
              (fun _ e => h111 (List.cons.inj (List.cons.inj e).2).1)
        · rw [List.nil_append, hre]; exact nAlt1_head (by omega)
      · exact nAlt1_head (by decide)
      · exact nAlt1_head (by decide)
    have hsg : nSign (sg ++ (r.enc ++ rest)) = sg.length :=
      nSign_sign hs (fun _ c hc => by rw [hre] at hc; simp at hc; subst hc; exact ⟨h43, h45⟩)
    have hip := nIp_run r hr h0 rest hstop2
    have hfr : nFr rest = 0 := nFr_none (fun c hc => (hst c hc).2.2.2.2.1)
    have hex : nEx rest = 0 := nEx_none (fun c hc => ⟨(hst c hc).2.2.2.2.2.1, (hst c hc).2.2.2.2.2.2.1⟩)
    rw [ha1]
    simp only [List.append_assoc, hsg, List.drop_left, hip, hfr, List.drop_zero, hex]
    simp
  rw [parseValue_num hc0 hc hd ht hm]
  have hsl : sl src pos (pos + (sg ++ r.enc).length) = sg ++ r.enc := sl_of_drop h
  simp only [hsl, matchToNumber, Bool.false_eq_true, ite_false, mkCfg]
  have hnd := ndigits_run 10 (by omega) r hr
  have hval := digitsVal_run 10 (by omega) r hr
  have hib : intBase0 maxD (sg ++ r.enc) = intBody maxD (sg == [45]) r.enc := by
    rcases hs with rfl | rfl | rfl
    · by_cases hd0 : r.d0 = 0
      · have : r.enc = [48] := by simp [Run.enc, hd0, h0 hd0, hexChar]
        rw [List.nil_append, this]; rfl
      · rw [List.nil_append, hre, intBase0_plain maxD _ _ (by omega) h43 h45]; rfl
    · exact intBase0_pos maxD r.enc
    · exact intBase0_neg maxD r.enc
  rw [hib]
  unfold intBody
  simp only [hnd, hval, NumTok.result]
  by_cases hlim : r.tail.length + 1 > 640 ∧ maxD > 0 ∧ r.tail.length + 1 > maxD
  · have hb : (decide (r.tail.length + 1 > 640) && decide (maxD > 0) && decide (r.tail.length + 1 > maxD)) = true := by
      simp [hlim.1, hlim.2.1, hlim.2.2]
    simp [hb, hlim, Except.map]
  · have hb : (decide (r.tail.length + 1 > 640) && decide (maxD > 0) && decide (r.tail.length + 1 > maxD)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    simp only [hb, Bool.false_eq_true, ite_false, hlim, Except.map]
    rcases hs with rfl | rfl | rfl <;> simp

theorem number_pre (pf : ParseFloat) (maxK maxD : Nat) (src : Str) (pos fuel : Nat) (l b : Nat) (r : Run)
    (rest : Str) (hok : (NumTok.pre l b r).ok) (hrest : stopHead rest)
    (h : src.drop pos = (48 :: l :: r.enc) ++ rest) :
    parseValue (mkCfg pf maxK maxD) src (fuel + 1) pos = (NumTok.pre l b r).result pf maxD pos := by
  obtain ⟨hlb, hr⟩ := hok
  have hst := stop_not_digit hrest
  have hb16 : b ≤ 16 := by rcases hlb with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  have hl : isDigit l = false ∧ l ≠ 58 := by
    rcases hlb with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hd : matchDatetime (src.drop pos) = none := by rw [h]; exact matchDatetime_second hl.1
  have ht : matchTime (src.drop pos) = none := by
    rw [h]; refine matchTime_none ?_ (fun c hc => ⟨(hst c hc).1, (hst c hc).2.2.2.1⟩)
    simp only [List.mem_cons, not_or]
    exact ⟨by decide, fun e => hl.2 e.symm, no58 b hb16 r hr⟩
  have hrun : ∀ (p : Nat → Bool), p 95 = false → (∀ d < b, ∀ up, p (hexChar d up) = true) →
      (∀ c, rest.head? = some c → p c = false) → dRun p (r.enc ++ rest) = some r.enc.length :=
    fun p hp95 hp hpr => dRun_run p hp95 b hp r hr rest (fun c hc => ⟨hpr c hc, (hst c hc).2.1⟩)
  have hstopc : ∀ c, rest.head? = some c → isOct c = false ∧ isBin c = false := by
    intro c hc; rcases hrest c hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have ha1 : nAlt1 (48 :: l :: r.enc ++ rest) = some (r.enc.length + 2) := by
    rcases hlb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show (dRun hexDigit (r.enc ++ rest)).map (· + 2) = _
      rw [hrun hexDigit (by decide) (basePred_hexChar 16 (by decide))
        (fun c hc => (hst c hc).2.2.2.2.2.2.2.2.2.2)]
      rfl
    · show (dRun isOct (r.enc ++ rest)).map (· + 2) = _
      rw [hrun isOct (by decide) (basePred_hexChar 8 (by decide)) (fun c hc => (hstopc c hc).1)]
      rfl
    · show (dRun isBin (r.enc ++ rest)).map (· + 2) = _
      rw [hrun isBin (by decide) (basePred_hexChar 2 (by decide)) (fun c hc => (hstopc c hc).2)]
      rfl
  have hm : matchNumber (src.drop pos) = some ⟨r.enc.length + 2, false⟩ := by
    rw [h, matchNumber_eq]; simp only [List.cons_append] at ha1 ⊢; rw [ha1]
  rw [parseValue_num h (by decide) hd ht hm]
  have hsl : sl src pos (pos + (r.enc.length + 2)) = 48 :: l :: r.enc := by
    have := sl_of_drop h; simp only [List.length_cons] at this
    rwa [show pos + (r.enc.length + 1 + 1) = pos + (r.enc.length + 2) by omega] at this
  have hval := digitsVal_run b hb16 r hr
  have hib : intBase0 maxD (48 :: l :: r.enc) = .ok (r.val b) := by
    rcases hlb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      (show Except.ok _ = _; rw [hval])
  simp only [hsl, matchToNumber, Bool.false_eq_true, ite_false, mkCfg, hib, NumTok.result, Except.map]
  congr 2; omega

theorem number_flt (pf : ParseFloat) (maxK maxD : Nat) (src : Str) (pos fuel : Nat) (sg : Str) (ip : Run)
    (fr : Option Run) (ex : Option (Nat × Str × Run)) (rest : Str) (hok : (NumTok.flt sg ip fr ex).ok)
    (hrest : stopHead rest) (h : src.drop pos = (sg ++ ip.enc ++ fracEnc fr ++ expEnc ex) ++ rest) :
    parseValue (mkCfg pf maxK maxD) src (fuel + 1) pos = (NumTok.flt sg ip fr ex).result pf maxD pos := by
  obtain ⟨hs, hip, hip0, hfr, hex, hsome⟩ := hok
  have hst := stop_not_digit hrest
  obtain ⟨rt, hre, hdig, h43, h45⟩ := run_head ip hip
  -- what follows the integer part, the fraction, the exponent
  have hafterExp : ∀ c, (expEnc ex ++ rest).head? = some c →
      isDigit c = false ∧ c ≠ 95 ∧ c ≠ 45 ∧ c ≠ 46 ∧ c ≠ 120 ∧ c ≠ 98 ∧ c ≠ 111 := by
    intro c hc
    cases ex with
    | none =>
      have := hst c (by simpa [expEnc] using hc)
      exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.1,
        this.2.2.2.2.2.2.2.2.2.1⟩
    | some e =>
      obtain ⟨e1, es, er⟩ := e
      have he := (hex e1 es er rfl).1
      simp [expEnc] at hc; subst hc
      rcases he with rfl | rfl <;> decide
  have hafterFr : ∀ c, (fracEnc fr ++ expEnc ex ++ rest).head? = some c →
      isDigit c = false ∧ c ≠ 95 ∧ c ≠ 45 ∧ c ≠ 120 ∧ c ≠ 98 ∧ c ≠ 111 := by
    intro c hc
    cases fr with
    | none =>
      have := hafterExp c (by simpa [fracEnc] using hc)
      exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.1, this.2.2.2.2.2.2⟩
    | some f => simp [fracEnc] at hc; subst hc; decide
  have hcases : (∃ c0 tt, src.drop pos = c0 :: tt ∧
      (c0 ≠ 34 ∧ c0 ≠ 39 ∧ c0 ≠ 116 ∧ c0 ≠ 102 ∧ c0 ≠ 91 ∧ c0 ≠ 123)) ∧
      matchDatetime (src.drop pos) = none := by
    rcases hs with rfl | rfl | rfl
    · refine ⟨⟨48 + ip.d0, rt ++ fracEnc fr ++ expEnc ex ++ rest, by rw [h, hre]; simp,
        by have := hip.1; omega⟩, ?_⟩
      rw [h]; simp only [List.nil_append, List.append_assoc]
      exact matchDatetime_none (no45 10 (by omega) ip hip)
        (fun c hc => ⟨(hafterFr c (by simpa using hc)).1, (hafterFr c (by simpa using hc)).2.2.1⟩)
    · exact ⟨⟨43, _, by rw [h]; rfl, by decide⟩, by rw [h]; exact matchDatetime_head (by decide)⟩
    · exact ⟨⟨45, _, by rw [h]; rfl, by decide⟩, by rw [h]; exact matchDatetime_head (by decide)⟩
  obtain ⟨⟨c0, tt, hc0, hc⟩, hd⟩ := hcases
  have h58 : 58 ∉ sg ++ ip.enc ++ fracEnc fr ++ expEnc ex := by
    simp only [List.mem_append, not_or]
    refine ⟨⟨⟨?_, no58 10 (by omega) ip hip⟩, ?_⟩, ?_⟩
    · rcases hs with rfl | rfl | rfl <;> decide
    · cases fr with
      | none => simp [fracEnc]
      | some f =>
        simp only [fracEnc, List.mem_cons, not_or]; exact ⟨by decide, no58 10 (by omega) f (hfr f rfl)⟩
    · cases ex with
      | none => simp [expEnc]
      | some e =>
        obtain ⟨e1, es, er⟩ := e
        obtain ⟨he, hes, her⟩ := hex e1 es er rfl
        intro m
        simp only [expEnc, List.cons_append, List.mem_cons, List.mem_append] at m
        rcases m with m | m | m
        · rcases he with rfl | rfl <;> simp at m
        · rcases hes with rfl | rfl | rfl <;> simp at m
        · exact no58 10 (by omega) er her m
  have ht : matchTime (src.drop pos) = none := by
    rw [h]; exact matchTime_none h58 (fun c hc => ⟨(hst c hc).1, (hst c hc).2.2.2.1⟩)
  have hlen_fr : nFr (fracEnc fr ++ (expEnc ex ++ rest)) = (fracEnc fr).length := by
    cases fr with
    | none =>
      simp only [fracEnc, List.nil_append]
      exact nFr_none (fun c hc => (hafterExp c hc).2.2.2.1)
    | some f =>
      simp only [fracEnc, List.cons_append, List.append_assoc]
      rw [nFr_run f (hfr f rfl) _ (fun c hc => ⟨(hafterExp c hc).1, (hafterExp c hc).2.1⟩)]; simp
  have hlen_ex : nEx (expEnc ex ++ rest) = (expEnc ex).length := by
    cases ex with
    | none =>
      simp only [expEnc, List.nil_append]
      exact nEx_none (fun c hc => ⟨(hst c hc).2.2.2.2.2.1, (hst c hc).2.2.2.2.2.2.1⟩)
    | some e =>
      obtain ⟨e1, es, er⟩ := e
      obtain ⟨he, hes, her⟩ := hex e1 es er rfl
      simp only [expEnc]
      rw [nEx_run e1 es er he hes her rest (fun c hc => ⟨(hst c hc).1, (hst c hc).2.1⟩)]
      simp only [List.length_cons, List.length_append]; omega
  have hpos : (fracEnc fr).length + (expEnc ex).length > 0 := by
    rcases hsome with hs' | hs'
    · cases fr with
      | none => simp at hs'
      | some f => simp [fracEnc]; omega
    · cases ex with
      | none => simp at hs'
      | some e => obtain ⟨e1, es, er⟩ := e; simp [expEnc]; omega
  have ha1 : nAlt1 (sg ++ (ip.enc ++ (fracEnc fr ++ (expEnc ex ++ rest)))) = none := by
    rcases hs with rfl | rfl | rfl
    · by_cases hd0 : ip.d0 = 0
      · have : ip.enc = [48] := by simp [Run.enc, hd0, hip0 hd0, hexChar]
        simp only [List.nil_append, this, List.cons_append]
        cases hx : fracEnc fr ++ (expEnc ex ++ rest) with
        | nil => rfl
        | cons c t2 =>
          have := hafterFr c (by rw [List.append_assoc, hx]; rfl)
          exact nAlt1_none (fun _ e => this.2.2.2.1 (List.cons.inj (List.cons.inj e).2).1)
            (fun _ e => this.2.2.2.2.1 (List.cons.inj (List.cons.inj e).2).1)
            (fun _ e => this.2.2.2.2.2 (List.cons.inj (List.cons.inj e).2).1)
      · simp only [List.nil_append, hre, List.cons_append]; exact nAlt1_head (by omega)
    · exact nAlt1_head (by decide)
    · exact nAlt1_head (by decide)
  have hsg : nSign (sg ++ (ip.enc ++ (fracEnc fr ++ (expEnc ex ++ rest)))) = sg.length :=
    nSign_sign hs (fun _ c hc => by rw [hre] at hc; simp at hc; subst hc; exact ⟨h43, h45⟩)
  have hipn : nIp (ip.enc ++ (fracEnc fr ++ (expEnc ex ++ rest))) = some ip.enc.length :=
    nIp_run ip hip hip0 _ (fun c hc => ⟨(hafterFr c (by simpa using hc)).1, (hafterFr c (by simpa using hc)).2.1⟩)
  have hm : matchNumber (src.drop pos) =
      some ⟨(sg ++ ip.enc ++ fracEnc fr ++ expEnc ex).length, true⟩ := by
    rw [h, matchNumber_eq]
    simp only [List.append_assoc, ha1, hsg, List.drop_left, hipn, hlen_fr, hlen_ex]
    simp only [List.length_append, Option.some.injEq, NumM.mk.injEq, decide_eq_true_eq]
    exact ⟨by omega, by omega⟩
  rw [parseValue_num hc0 hc hd ht hm]
  have hsl : sl src pos (pos + (sg ++ ip.enc ++ fracEnc fr ++ expEnc ex).length) =
      sg ++ ip.enc ++ fracEnc fr ++ expEnc ex := sl_of_drop h
  simp only [hsl, matchToNumber, decide_true, ite_true]
  rw [map_pf]
  exact pf_floatResult pf maxK maxD pos _

theorem number_special (pf : ParseFloat) (maxK maxD : Nat) (src : Str) (pos fuel : Nat) (sg n : Str)
    (rest : Str) (hok : (NumTok.special sg n).ok) (h : src.drop pos = (sg ++ n) ++ rest) :
    parseValue (mkCfg pf maxK maxD) src (fuel + 1) pos = (NumTok.special sg n).result pf maxD pos := by
  obtain ⟨hs, hn⟩ := hok
  have key : ∃ c0 tt, src.drop pos = c0 :: tt ∧ isDigit c0 = false ∧ c0 ≠ 48 ∧
      (c0 ≠ 34 ∧ c0 ≠ 39 ∧ c0 ≠ 116 ∧ c0 ≠ 102 ∧ c0 ≠ 91 ∧ c0 ≠ 123) := by
    rcases hs with rfl | rfl | rfl <;> rcases hn with rfl | rfl <;>
      exact ⟨_, _, by rw [h]; rfl, by decide, by decide, by decide⟩
  obtain ⟨c0, tt, hc0, hdg, h48, hc⟩ := key
  have hd : matchDatetime (src.drop pos) = none := by rw [hc0]; exact matchDatetime_head hdg
  have ht : matchTime (src.drop pos) = none := by rw [hc0]; exact matchTime_head hdg
  have hm : matchNumber (src.drop pos) = none := by
    rw [matchNumber_eq, hc0, nAlt1_head h48, ← hc0, h]
    rcases hs with rfl | rfl | rfl <;> rcases hn with rfl | rfl <;> rfl
  rw [parseValue_special hc0 hc hd ht hm]
  have s3 : ∀ tok : Str, tok.length = 3 → src.drop pos = tok ++ rest → sl src pos (pos + 3) = tok := by
    intro tok hl h'; have := sl_of_drop h'; rwa [hl] at this
  have s4 : ∀ tok : Str, tok.length = 4 → src.drop pos = tok ++ rest →
      sl src pos (pos + 3) = tok.take 3 ∧ sl src pos (pos + 4) = tok := by
    intro tok hl h'
    refine ⟨?_, by have := sl_of_drop h'; rwa [hl] at this⟩
    have h'' : src.drop pos = tok.take 3 ++ (tok.drop 3 ++ rest) := by rw [h', ← List.append_assoc, List.take_append_drop]
    have := sl_of_drop h''; rwa [show (tok.take 3).length = 3 by simp [hl]] at this
  have hinf : S "inf" = [105, 110, 102] := rfl
  have hnan : S "nan" = [110, 97, 110] := rfl
  rcases hs with rfl | rfl | rfl <;> rcases hn with rfl | rfl <;> simp only [hinf, hnan, List.nil_append] at h
  · rw [s3 _ rfl h]; exact pf_floatResult pf maxK maxD pos _
  · rw [s3 _ rfl h]; exact pf_floatResult pf maxK maxD pos _
  · obtain ⟨e3, e4⟩ := s4 [43, 105, 110, 102] rfl h
    rw [e3, e4]; exact pf_floatResult pf maxK maxD pos _
  · obtain ⟨e3, e4⟩ := s4 [43, 110, 97, 110] rfl h
    rw [e3, e4]; exact pf_floatResult pf maxK maxD pos _
  · obtain ⟨e3, e4⟩ := s4 [45, 105, 110, 102] rfl h
    rw [e3, e4]; exact pf_floatResult pf maxK maxD pos _
  · obtain ⟨e3, e4⟩ := s4 [45, 110, 97, 110] rfl h
    rw [e3, e4]; exact pf_floatResult pf maxK maxD pos _

/-- `NumberSpec` holds. -/
theorem numberSpec_proven : NumberSpec := by
  intro pf maxK maxD src pos fuel t rest hok hrest h
  cases t with
  | dec sg r => exact number_dec pf maxK maxD src pos fuel sg r rest hok hrest h
  | pre l b r => exact number_pre pf maxK maxD src pos fuel l b r rest hok hrest h
  | flt sg ip fr ex => exact number_flt pf maxK maxD src pos fuel sg ip fr ex rest hok hrest h
  | special sg n => exact number_special pf maxK maxD src pos fuel sg n rest hok h

end PyLean.TextLibs.Toml
