import PyLean.Decimal.Tuple
import PyLean.Decimal.Digits
import PyLean.Decimal.Lemmas

/-! The tuple constructor of the two twins, on tuples whose coefficient is a
tuple of ints in `0..9`. -/

namespace PyLean.Decimal

open PyLean

theorem collect_ne (L : List PyVal) (acc : List PyVal) (hacc : acc ≠ [])
    (hL : ∀ v ∈ L, ∃ k : Nat, k ≤ 9 ∧ v = .int k) :
    pyFromTuple.collect L acc = .ok (acc ++ L) := by
  induction L generalizing acc with
  | nil => simp [pyFromTuple.collect]
  | cons d rest ih =>
    obtain ⟨k, hk, rfl⟩ := hL d (by simp)
    simp only [pyFromTuple.collect, PyVal.asInt?]
    have h1 : (0 ≤ (k : Int) ∧ (k : Int) ≤ 9) := by omega
    simp only [h1, hacc, ne_eq, not_false_eq_true, true_or, ↓reduceIte]
    rw [ih _ (by simp) (fun v hv => hL v (by simp [hv]))]
    simp

theorem collect_nil (ks : List Nat) (hks : ∀ k ∈ ks, k ≤ 9) :
    pyFromTuple.collect (ks.map (fun k : Nat => PyVal.int (k : Int))) [] =
      .ok ((ks.dropWhile (· == 0)).map (fun k : Nat => PyVal.int (k : Int))) := by
  induction ks with
  | nil => simp [pyFromTuple.collect]
  | cons k rest ih =>
    simp only [List.map_cons, pyFromTuple.collect, PyVal.asInt?]
    have h1 : (0 ≤ (k : Int) ∧ (k : Int) ≤ 9) := by have := hks k (by simp); omega
    rw [if_pos h1]
    by_cases hk : k = 0
    · subst hk
      simp only [ne_eq, not_true_eq_false, false_or, List.dropWhile_cons]
      rw [if_neg (by simp)]
      rw [ih (fun x hx => hks x (by simp [hx]))]
      simp
    · have hne : [PyVal.int (k : Int)] ≠ [] := by simp
      rw [if_pos (by simp; omega)]
      simp only [List.nil_append]
      rw [collect_ne _ _ hne (fun v hv => by
        simp only [List.mem_map] at hv
        obtain ⟨j, hj, rfl⟩ := hv
        exact ⟨j, hks j (by simp [hj]), rfl⟩)]
      simp [List.dropWhile_cons, hk]

abbrev digs (ks : List Nat) : List PyVal := ks.map (fun k : Nat => PyVal.int (k : Int))

theorem digitChar_isDigit (k : Nat) (hk : k ≤ 9) : (Nat.digitChar k).isDigit = true := by
  have : ∀ k, k < 10 → (Nat.digitChar k).isDigit = true := by decide
  exact this k (by omega)

theorem digitChar_ne_zero (k : Nat) (hk : k ≤ 9) (h0 : k ≠ 0) : Nat.digitChar k ≠ '0' := by
  have : ∀ k, k < 10 → k ≠ 0 → Nat.digitChar k ≠ '0' := by decide
  exact this k (by omega) h0

theorem digitsValue_dropZeros (ks : List Nat) :
    digitsValue (ks.map Nat.digitChar) = digitsValue ((ks.dropWhile (· == 0)).map Nat.digitChar) := by
  induction ks with
  | nil => rfl
  | cons k rest ih =>
    by_cases hk : k = 0
    · subst hk
      simp only [List.map_cons, List.dropWhile_cons, BEq.rfl, ↓reduceIte]
      rw [← ih]; rfl
    · simp [List.dropWhile_cons, hk]

/-- The C payload/coefficient of a digit tuple, spelled back, is `_pydecimal`'s
`_int` (the digits without leading zeros), or `'0'`/empty for zero. -/
theorem toDigits_digs (ks : List Nat) (hks : ∀ k ∈ ks, k ≤ 9) :
    (ks.dropWhile (· == 0) = [] ∧ digitsValue (ks.map Nat.digitChar) = 0) ∨
    (ks.dropWhile (· == 0) ≠ [] ∧
      Nat.toDigits 10 (digitsValue (ks.map Nat.digitChar)) = (ks.dropWhile (· == 0)).map Nat.digitChar) := by
  have hks' : ∀ k ∈ ks.dropWhile (· == 0), k ≤ 9 := fun k hk => hks k (List.dropWhile_subset _ hk)
  rw [digitsValue_dropZeros]
  by_cases he : ks.dropWhile (· == 0) = []
  · left; exact ⟨he, by rw [he]; rfl⟩
  · right
    refine ⟨he, ?_⟩
    have hk0 := List.head_dropWhile_not (fun x => x == 0) he
    generalize hkr : ks.dropWhile (· == 0) = ks' at he hk0 hks'
    obtain ⟨k, rest, rfl⟩ := List.exists_cons_of_ne_nil he
    simp only [List.head_cons, beq_iff_eq] at hk0
    rw [digitsValue_eq _ (fun c hc => by
      simp only [List.mem_map] at hc
      obtain ⟨j, hj, rfl⟩ := hc
      exact digitChar_isDigit j (hks' j hj))]
    apply toDigits_ofDigitChars _ _ rfl
    · intro c hc
      simp only [List.mem_map] at hc
      obtain ⟨j, hj, rfl⟩ := hc
      exact digitChar_isDigit j (hks' j hj)
    · simp
    · simp only [List.map_cons, List.head?_cons, ne_eq, Option.some.injEq]
      exact digitChar_ne_zero k (hks' k (by simp)) (by simpa using hk0)

theorem mapM_digs (ks : List Nat) (hks : ∀ k ∈ ks, k ≤ 9) : (digs ks).mapM cDigit = .ok ks := by
  induction ks with
  | nil => rfl
  | cons k rest ih =>
    have hk := hks k (by simp)
    have h1 : cDigit (.int (k : Int)) = .ok k := by
      simp only [cDigit, PyVal.asInt?]
      rw [if_neg (by omega), if_neg (by omega)]
      simp
    simp only [digs, List.map_cons, List.mapM_cons, h1]
    simp only [digs] at ih
    rw [ih (fun x hx => hks x (by simp [hx]))]
    rfl

theorem flatMap_digs (ks : List Nat) (hks : ∀ k ∈ ks, k ≤ 9) :
    (digs ks).flatMap PyVal.pyStr = ks.map Nat.digitChar := by
  induction ks with
  | nil => rfl
  | cons k rest ih =>
    have hk := hks k (by simp)
    simp only [digs, List.map_cons, List.flatMap_cons, PyVal.pyStr, Int.toNat_natCast]
    simp only [digs] at ih
    rw [ih (fun x hx => hks x (by simp [hx])), Nat.toDigits_of_lt_base (by omega)]
    rfl

theorem ofNat_digs (ks : List Nat) (hks : ∀ k ∈ ks, k ≤ 9) :
    ks.map (fun v => Char.ofNat (48 + v)) = ks.map Nat.digitChar := by
  apply List.map_congr_left
  intro k hk
  exact (digitChar_aux k (by have := hks k hk; omega)).symm

theorem numDigits_le_18 {n : Nat} (h : n < 10 ^ 18) : numDigits n ≤ maxStrDigits := by
  have := (numDigits_le_iff (n := n) (k := 18) (by decide)).mpr h
  simp only [maxStrDigits]; omega

theorem py_tuple_ok (s : PyVal) (ks : List Nat) (e : PyVal) (o : PyObj) (hks : ∀ k ∈ ks, k ≤ 9)
    (hpy : pyFromTuple s (some (digs ks)) e = .ok o) :
    ∃ b : Bool, s.asInt? = some (if b then 1 else 0) ∧
      ((e = .str "F" ∧ o = ⟨b, ['0'], .inf⟩) ∨
       (e = .str "n" ∧ o = ⟨b, (ks.dropWhile (· == 0)).map Nat.digitChar, .qnan⟩) ∨
       (e = .str "N" ∧ o = ⟨b, (ks.dropWhile (· == 0)).map Nat.digitChar, .snan⟩) ∨
       (∃ x, e.asInt? = some x ∧ (∀ t, e ≠ .str t) ∧
          o = ⟨b, if ks.dropWhile (· == 0) = [] then ['0'] else (ks.dropWhile (· == 0)).map Nat.digitChar, .num x⟩)) := by
  have hcol := collect_nil ks hks
  have hfl := flatMap_digs (ks.dropWhile (· == 0)) (fun k hk => hks k (List.dropWhile_subset _ hk))
  unfold pyFromTuple at hpy
  rcases hsg : pySign s with err | b
  · rw [hsg] at hpy; simp [bind, Except.bind] at hpy
  have hsv : s.asInt? = some (if b then 1 else 0) := by
    unfold pySign at hsg
    split at hsg <;> simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  refine ⟨b, hsv, ?_⟩
  rw [hsg] at hpy
  cases e with
  | int x =>
    right; right; right
    refine ⟨x, rfl, ?_⟩
    refine ⟨fun t ht => (by cases ht), ?_⟩
    simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, hcol, pure, Except.pure, PyVal.asInt?, hfl] at hpy
    exact hpy.symm
  | bool bb =>
    right; right; right
    refine ⟨_, rfl, ?_⟩
    refine ⟨fun t ht => (by cases ht), ?_⟩
    simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, hcol, pure, Except.pure, PyVal.asInt?, hfl] at hpy
    exact hpy.symm
  | other =>
    simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, hcol, pure, Except.pure, PyVal.asInt?] at hpy
  | str t =>
    by_cases hF : t = "F"
    · subst hF; left
      simp [bind, Except.bind, pure, Except.pure] at hpy
      exact ⟨rfl, hpy.symm⟩
    by_cases hn : t = "n"
    · subst hn; right; left
      simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, hcol, pure, Except.pure, hfl] at hpy
      exact ⟨rfl, hpy.symm⟩
    by_cases hN : t = "N"
    · subst hN; right; right; left
      simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, hcol, pure, Except.pure, hfl] at hpy
      exact ⟨rfl, hpy.symm⟩
    exfalso
    simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, hcol, pure, Except.pure, hF] at hpy
    split at hpy <;> simp_all [PyVal.asInt?]


theorem tuple_agree (s : PyVal) (ks : List Nat) (e : PyVal) (o : PyObj) (hks : ∀ k ∈ ks, k ≤ 9)
    (he : ∀ x, e.asInt? = some x → x.natAbs ≤ 10 ^ 17) (hlen : ks.length ≤ 10 ^ 17)
    (hpy : pyFromTuple s (some (digs ks)) e = .ok o) :
    ∃ d, cFromTuple s (some (digs ks)) e = .ok d ∧ pyStrObj o = .ok (toSci d) := by
  obtain ⟨b, hsv, hcase⟩ := py_tuple_ok s ks e o hks hpy
  have hm := mapM_digs ks hks
  have hof := ofNat_digs ks hks
  have hp := toDigits_digs ks hks
  rw [← hof] at hp
  generalize hP : digitsValue (List.map (fun v => Char.ofNat (48 + v)) ks) = P at hp
  have hPd : numDigits P ≤ ks.length + 1 := by
    rcases hp with ⟨_, rfl⟩ | ⟨_, h2⟩
    · simp [numDigits_zero]
    · simp only [numDigits, h2, List.length_map]
      have := (List.dropWhile_sublist (l := ks) (· == 0)).length_le
      omega
  have hPm : ¬((P ≠ 0) ∧ mpdMaxPrec < (numDigits P : Int)) := by
    simp only [mpdMaxPrec]; omega
  -- `_int` of `_pydecimal` is the spelling of the C coefficient
  have hint : (if ks.dropWhile (· == 0) = [] then ['0'] else (ks.dropWhile (· == 0)).map Nat.digitChar) =
      Nat.toDigits 10 P := by
    rcases hp with ⟨h1, rfl⟩ | ⟨h1, h2⟩
    · simp [h1, Nat.toDigits_zero]
    · simp [h1, h2]
  have hpay : (if P = 0 then [] else Nat.toDigits 10 P) = (ks.dropWhile (· == 0)).map Nat.digitChar := by
    rcases hp with ⟨h1, rfl⟩ | ⟨h1, h2⟩
    · simp [h1]
    · have : P ≠ 0 := by
        intro h0; subst h0
        rw [Nat.toDigits_zero] at h2
        obtain ⟨k, rest, hk⟩ := List.exists_cons_of_ne_nil h1
        rw [hk] at h2
        have hk0 := List.head_dropWhile_not (fun x => x == 0) h1
        simp only [hk, List.head_cons, beq_eq_false_iff_ne, ne_eq] at hk0
        simp only [List.map_cons, List.cons.injEq] at h2
        exact digitChar_ne_zero k (hks k (List.dropWhile_subset _ (by rw [hk]; simp))) hk0 h2.1.symm
      simp [this, h2]
  have hlim : ∀ x : Int, x.natAbs ≤ 10 ^ 17 → ∀ b, InCLimits (.fin b P x) := by
    intro x hx b
    simp only [InCLimits, mpdMaxPrec, mpdMaxEmax, mpdMinEtiny, mpdMinEmin]
    omega
  have hsl : ∀ n : Nat, n < 10 ^ 18 → strLimit n = .ok () := by
    intro n hn
    have := (numDigits_le_iff (n := n) (k := 18) (by decide)).mpr hn
    unfold strLimit
    rw [if_neg (by simp only [maxStrDigits]; omega)]
  have hstr : ∀ x : Int, x.natAbs ≤ 10 ^ 17 → ∀ b (I : List Char), I.length ≤ ks.length + 1 →
      pyStrObj ⟨b, I, .num x⟩ = .ok (sciFinite b I x true) := by
    intro x hx b I hI
    simp only [pyStrObj]
    split <;> split <;> first | rfl | (rw [hsl _ (by omega)]; rfl) | (exfalso; simp_all)
  have hIl : (if ks.dropWhile (· == 0) = [] then ['0'] else (ks.dropWhile (· == 0)).map Nat.digitChar).length
      ≤ ks.length + 1 := by
    split
    · simp
    · simp only [List.length_map]
      have := (List.dropWhile_sublist (l := ks) (· == 0)).length_le
      omega
  have cdig : ∀ v, (digs ks).mapM cDigit = Except.ok v → v = ks := by
    intro v h; rw [hm] at h; cases h; rfl
  cases b <;> rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨x, hx, hns, rfl⟩
  · refine ⟨.inf false, ?_, rfl⟩
    unfold cFromTuple; rw [hsv]
    simp [hm, bind, Except.bind, pure, Except.pure]
  · refine ⟨.nan false false P, ?_, ?_⟩
    · unfold cFromTuple; rw [hsv]
      simp [hm, bind, Except.bind, pure, Except.pure, hP, hPm]
    · simp only [pyStrObj, toSci]; rw [hpay]; rfl
  · refine ⟨.nan false true P, ?_, ?_⟩
    · unfold cFromTuple; rw [hsv]
      simp [hm, bind, Except.bind, pure, Except.pure, hP, hPm]
    · simp only [pyStrObj, toSci]; rw [hpay]; rfl
  · refine ⟨.fin false P x, ?_, ?_⟩
    · have hxb := he x hx
      unfold cFromTuple; rw [hsv]
      cases e with
      | str t => exact absurd rfl (hns t)
      | other => simp [PyVal.asInt?] at hx
      | int y =>
        simp only [PyVal.asInt?, Option.some.injEq] at hx; subst hx
        simp [hm, bind, Except.bind, pure, Except.pure, hP, hlim _ hxb, PyVal.asInt?, mpdSsizeMin, mpdSsizeMax]
        omega
      | bool bb =>
        simp only [PyVal.asInt?, Option.some.injEq] at hx; subst hx
        simp [hm, bind, Except.bind, pure, Except.pure, hP, hlim _ hxb, PyVal.asInt?, mpdSsizeMin, mpdSsizeMax]
        cases bb <;> decide
    · rw [hstr x (he x hx) _ _ hIl, hint]; rfl
  · refine ⟨.inf true, ?_, rfl⟩
    unfold cFromTuple; rw [hsv]
    simp [hm, bind, Except.bind, pure, Except.pure]
  · refine ⟨.nan true false P, ?_, ?_⟩
    · unfold cFromTuple; rw [hsv]
      simp [hm, bind, Except.bind, pure, Except.pure, hP, hPm]
    · simp only [pyStrObj, toSci]; rw [hpay]; rfl
  · refine ⟨.nan true true P, ?_, ?_⟩
    · unfold cFromTuple; rw [hsv]
      simp [hm, bind, Except.bind, pure, Except.pure, hP, hPm]
    · simp only [pyStrObj, toSci]; rw [hpay]; rfl
  · refine ⟨.fin true P x, ?_, ?_⟩
    · have hxb := he x hx
      unfold cFromTuple; rw [hsv]
      cases e with
      | str t => exact absurd rfl (hns t)
      | other => simp [PyVal.asInt?] at hx
      | int y =>
        simp only [PyVal.asInt?, Option.some.injEq] at hx; subst hx
        simp [hm, bind, Except.bind, pure, Except.pure, hP, hlim _ hxb, PyVal.asInt?, mpdSsizeMin, mpdSsizeMax]
        omega
      | bool bb =>
        simp only [PyVal.asInt?, Option.some.injEq] at hx; subst hx
        simp [hm, bind, Except.bind, pure, Except.pure, hP, hlim _ hxb, PyVal.asInt?, mpdSsizeMin, mpdSsizeMax]
        cases bb <;> decide
    · rw [hstr x (he x hx) _ _ hIl, hint]; rfl


/-- For every tuple `(sign, digits, exp)` whose coefficient is a tuple of
ints in `0..9`, with `|exp| ≤ 10^17` and at most `10^17` digits (so the
value is within the C limits), if `_pydecimal.Decimal(t)` succeeds then
`_decimal.Decimal(t)` succeeds and both print the same. -/
def TupleTwinsAgreeDigits : Prop :=
  ∀ (s : PyVal) (ks : List Nat) (e : PyVal) (o : PyObj),
    (∀ k ∈ ks, k ≤ 9) →
    (∀ x, e.asInt? = some x → x.natAbs ≤ 10 ^ 17) → ks.length ≤ 10 ^ 17 →
    pyFromTuple s (some (digs ks)) e = .ok o →
    ∃ d, cFromTuple s (some (digs ks)) e = .ok d ∧ pyStrObj o = .ok (toSci d)

theorem tupleTwinsAgreeDigits_proven : TupleTwinsAgreeDigits :=
  fun s ks e o hks he hlen hpy => tuple_agree s ks e o hks he hlen hpy

end PyLean.Decimal
