import PyLean.TextLibs.HtmlModel

/-!
`html.escape` and `html.unescape`: the round trip on the real entity table, the `in` test before the
regex against the regex, and where the digit limit of `int` lets an exception out.
-/

namespace PyLean.TextLibs.Html

open PyLean

/-- What `escape` does to one character. -/
def escF (q : Bool) (c : Nat) : List Nat :=
  if c == 38 then eAmp else if c == 60 then eLt else if c == 62 then eGt
  else if q && c == 34 then eQuot else if q && c == 39 then eApos else [c]

theorem replaceCh_cons (c : Nat) (r : List Nat) (a : Nat) (b : List Nat) :
    replaceCh (c :: r) a b = (if c == a then b else [c]) ++ replaceCh r a b := by
  simp [replaceCh]

theorem replaceCh_append (x y : List Nat) (a : Nat) (b : List Nat) :
    replaceCh (x ++ y) a b = replaceCh x a b ++ replaceCh y a b := by
  simp [replaceCh]

theorem escape_cons (c : Nat) (r : List Nat) (q : Bool) :
    escape (c :: r) q = escF q c ++ escape r q := by
  have h1 : escape (c :: r) q = escape [c] q ++ escape r q := by
    cases q <;> simp [escape, replaceCh]
  rw [h1]
  congr 1
  by_cases h38 : c = 38
  · subst h38; cases q <;> decide
  by_cases h60 : c = 60
  · subst h60; cases q <;> decide
  by_cases h62 : c = 62
  · subst h62; cases q <;> decide
  by_cases h34 : c = 34
  · subst h34; cases q <;> decide
  by_cases h39 : c = 39
  · subst h39; cases q <;> decide
  cases q <;> simp [escape, replaceCh, escF, h38, h60, h62, h34, h39]

theorem sub_ref (f : Nat) (r g rest x y : List Nat) (hm : matchRef r = some (g, rest))
    (hx : replaceCharref g = .ok x) (hs : subLoop f rest = .ok y) :
    subLoop (f + 1) (38 :: r) = .ok (x ++ y) := by
  simp [subLoop, hm, hx, hs]

theorem sub_plain (f : Nat) (c : Nat) (r y : List Nat) (hc : c ≠ 38) (hs : subLoop f r = .ok y) :
    subLoop (f + 1) (c :: r) = .ok (c :: y) := by
  simp [subLoop, hc, hs]

theorem ref_amp : replaceCharref [97, 109, 112, 59] = .ok [38] := by decide +kernel
theorem ref_lt : replaceCharref [108, 116, 59] = .ok [60] := by decide +kernel
theorem ref_gt : replaceCharref [103, 116, 59] = .ok [62] := by decide +kernel
theorem ref_quot : replaceCharref [113, 117, 111, 116, 59] = .ok [34] := by decide +kernel
theorem ref_apos : replaceCharref [35, 120, 50, 55, 59] = .ok [39] := by decide +kernel

/-- Each reference `escape` writes is read back as itself, whatever follows it. -/
theorem sub_escape (q : Bool) : ∀ (s : List Nat) (f : Nat), (escape s q).length < f →
    subLoop f (escape s q) = .ok s := by
  intro s
  induction s with
  | nil =>
    intro f hf
    have e : escape [] q = [] := by cases q <;> rfl
    rw [e] at hf ⊢
    cases f with
    | zero => omega
    | succ f => rfl
  | cons c r ih =>
    intro f hf
    rw [escape_cons] at hf ⊢
    generalize hrest : escape r q = rest at hf ih
    have key : ∀ (x : List Nat) (y : List Nat) (g : List Nat), x = 38 :: y →
        matchRef (y ++ rest) = some (g, rest) → replaceCharref g = .ok [c] →
        (x ++ rest).length < f → subLoop f (x ++ rest) = .ok (c :: r) := by
      intro x y g hx hm hg hl
      subst hx
      cases f with
      | zero => omega
      | succ f =>
        have hr := ih f (by simp at hl; omega)
        exact sub_ref f _ g rest [c] r hm hg hr
    by_cases h38 : c = 38
    · subst h38
      exact key eAmp [97, 109, 112, 59] _ rfl rfl ref_amp hf
    by_cases h60 : c = 60
    · subst h60
      exact key eLt [108, 116, 59] _ rfl rfl ref_lt hf
    by_cases h62 : c = 62
    · subst h62
      exact key eGt [103, 116, 59] _ rfl rfl ref_gt hf
    by_cases h34 : q = true ∧ c = 34
    · obtain ⟨hq, rfl⟩ := h34
      subst hq
      exact key eQuot [113, 117, 111, 116, 59] _ rfl rfl ref_quot hf
    by_cases h39 : q = true ∧ c = 39
    · obtain ⟨hq, rfl⟩ := h39
      subst hq
      exact key eApos [35, 120, 50, 55, 59] _ rfl rfl ref_apos hf
    have hF : escF q c = [c] := by
      have a1 : (q && c == 34) = false := by
        cases q <;> simp
        intro h; exact h34 ⟨rfl, h⟩
      have a2 : (q && c == 39) = false := by
        cases q <;> simp
        intro h; exact h39 ⟨rfl, h⟩
      simp [escF, h38, h60, h62, a1, a2]
    rw [hF] at hf ⊢
    simp only [List.cons_append, List.nil_append, List.length_cons] at hf ⊢
    cases f with
    | zero => omega
    | succ f => exact sub_plain f c rest r h38 (ih f (by omega))

/-- `unescape` undoes `escape`, for every string and both values of `quote`. The entity table is the
real one, and the theorem would fail if `amp;` and the others were missing or wrong in it. -/
def UnescapeEscape : Prop := ∀ (s : List Nat) (q : Bool), unescape (escape s q) = .ok s

theorem unescapeEscape_proven : UnescapeEscape := by
  intro s q
  unfold unescape
  split
  · rename_i h
    -- no `&` in the output: the fast path returns it, and it has to be `s`
    have hs := sub_escape q s _ (Nat.lt_succ_self _)
    have : ∀ (t : List Nat) (f : Nat), t.contains 38 = false → t.length < f → subLoop f t = .ok t := by
      intro t
      induction t with
      | nil =>
        intro f _ hf
        cases f with
        | zero => omega
        | succ f => rfl
      | cons c r ih =>
        intro f h hf
        simp only [List.contains_cons, Bool.or_eq_false_iff] at h
        have hc : c ≠ 38 := by
          intro e; subst e; simp at h
        cases f with
        | zero => exact absurd hf (Nat.not_lt_zero _)
        | succ f => exact sub_plain f c r r hc (ih f h.2 (by simp at hf; omega))
    have h' : (escape s q).contains 38 = false := by simpa using h
    rw [this _ _ h' (Nat.lt_succ_self _)] at hs
    exact hs
  · exact sub_escape q s _ (Nat.lt_succ_self _)

/-- The test `'&' not in s` and the regex agree: without `&`, `sub` would change nothing either. -/
def UnescapeFastPath : Prop :=
  ∀ s : List Nat, s.contains 38 = false → subLoop (s.length + 1) s = unescape s

theorem unescapeFastPath_proven : UnescapeFastPath := by
  intro s h
  have key : ∀ (t : List Nat) (f : Nat), t.contains 38 = false → t.length < f → subLoop f t = .ok t := by
    intro t
    induction t with
    | nil =>
      intro f _ hf
      cases f with
      | zero => omega
      | succ f => rfl
    | cons c r ih =>
      intro f h hf
      simp only [List.contains_cons, Bool.or_eq_false_iff] at h
      have hc : c ≠ 38 := by
        intro e; subst e; simp at h
      cases f with
      | zero => exact absurd hf (Nat.not_lt_zero _)
      | succ f => exact sub_plain f c r r hc (ih f h.2 (by simp at hf; omega))
  have e : unescape s = .ok s := by
    unfold unescape
    rw [h]
    rfl
  rw [key s _ h (Nat.lt_succ_self _), e]

/-- `escape` leaves no markup characters behind. -/
def EscapeSafe : Prop :=
  ∀ (s : List Nat) (q : Bool), 60 ∉ escape s q ∧ 62 ∉ escape s q ∧
    (q = true → 34 ∉ escape s q ∧ 39 ∉ escape s q)

theorem escapeSafe_proven : EscapeSafe := by
  intro s q
  induction s with
  | nil => cases q <;> simp [escape, replaceCh]
  | cons c r ih =>
    rw [escape_cons]
    obtain ⟨h1, h2, h3⟩ := ih
    have hF : 60 ∉ escF q c ∧ 62 ∉ escF q c ∧ (q = true → 34 ∉ escF q c ∧ 39 ∉ escF q c) := by
      by_cases h38 : c = 38
      · subst h38; cases q <;> decide
      by_cases h60 : c = 60
      · subst h60; cases q <;> decide
      by_cases h62 : c = 62
      · subst h62; cases q <;> decide
      by_cases h34 : c = 34
      · subst h34; cases q <;> decide
      by_cases h39 : c = 39
      · subst h39; cases q <;> decide
      cases q <;> simp [escF, h38, h60, h62, h34, h39] <;> omega
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.mem_append, not_or]; exact ⟨hF.1, h1⟩
    · simp only [List.mem_append, not_or]; exact ⟨hF.2.1, h2⟩
    · intro hq
      have a := hF.2.2 hq
      have b := h3 hq
      simp only [List.mem_append, not_or]
      exact ⟨⟨a.1, b.1⟩, ⟨a.2, b.2⟩⟩

/-- `unescape` never raises. False, by the digit limit of `int`. -/
def UnescapeTotal : Prop := ∀ s : List Nat, (unescape s).toBool = true

theorem unescapeTotal_refuted : ¬UnescapeTotal := by
  intro h
  have := h (38 :: 35 :: List.replicate 4301 48 ++ [59])
  revert this
  decide +kernel

/-- A numeric reference means the same in decimal and in hexadecimal. False past the digit limit,
which the hexadecimal branch does not have. -/
def NumericTwin : Prop :=
  ∀ ds hs : List Nat, ds ≠ [] → hs ≠ [] → (∀ d ∈ ds, isDigit d = true) → (∀ d ∈ hs, isHex d = true) →
    ds.foldl (fun v c => v * 10 + (c - 48)) 0 = intHex hs →
    (replaceCharref (35 :: ds ++ [59])) = replaceCharref (35 :: 120 :: hs ++ [59])

theorem foldl_zeros (n : Nat) :
    (List.replicate n 48).foldl (fun v c => v * 10 + (c - 48)) 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ] using ih

theorem numericTwin_refuted : ¬NumericTwin := by
  intro h
  have := h (List.replicate 4301 48) [48] (by intro e; cases e) (by simp)
    (by intro d hd; rw [List.eq_of_mem_replicate hd]; rfl) (by decide +kernel)
    (by rw [foldl_zeros]; rfl)
  have := congrArg Except.toBool this
  revert this
  decide +kernel

theorem rstrip_digits (a b : List Nat) (ha : ∀ x ∈ a, x ≠ 59) (hb : b = [] ∨ b = [59]) :
    rstripSemi (a ++ b) = a := by
  have key : (a.reverse).dropWhile (· == 59) = a.reverse := by
    cases he : a.reverse with
    | nil => rfl
    | cons x t =>
      have hx : x ≠ 59 := ha x (by
        have : x ∈ a.reverse := by rw [he]; simp
        simpa using this)
      simp [List.dropWhile_cons, hx]
  rcases hb with rfl | rfl
  · simp [rstripSemi, key]
  · simp [rstripSemi, key]

/-- Narrows `NumericTwin`: at most 4300 digits, which is what the refutation excludes. -/
def NumericTwinNarrow : Prop :=
  ∀ ds hs : List Nat, ds ≠ [] → hs ≠ [] → ds.length ≤ 4300 → (∀ d ∈ ds, isDigit d = true) →
    (∀ d ∈ hs, isHex d = true) → ds.foldl (fun v c => v * 10 + (c - 48)) 0 = intHex hs →
    (replaceCharref (35 :: ds ++ [59])) = replaceCharref (35 :: 120 :: hs ++ [59])

theorem isDigit_ne {d : Nat} (h : isDigit d = true) : d ≠ 59 ∧ d ≠ 120 ∧ d ≠ 88 := by
  simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

theorem isHex_ne {d : Nat} (h : isHex d = true) : d ≠ 59 := by
  simp only [isHex, isDigit, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  omega

theorem numericTwinNarrow_proven : NumericTwinNarrow := by
  intro ds hs h1 h2 hl hd hh he
  have r1 := rstrip_digits ds [59] (fun x hx => (isDigit_ne (hd x hx)).1) (.inr rfl)
  have r2 := rstrip_digits hs [59] (fun x hx => isHex_ne (hh x hx)) (.inr rfl)
  obtain ⟨c, r, rfl⟩ := List.exists_cons_of_ne_nil h1
  have hc := isDigit_ne (hd c (by simp))
  have e1 : replaceCharref (35 :: (c :: r) ++ [59]) = .ok (numRef (intHex hs)) := by
    have hint : intDec (c :: r) = .ok (intHex hs) := by
      simp only [intDec]
      rw [if_neg (by omega)]
      exact congrArg _ he
    have : (35 :: (c :: r) ++ [59]) = 35 :: c :: (r ++ [59]) := rfl
    rw [this]
    have rs : rstripSemi (c :: (r ++ [59])) = c :: r := r1
    simp [replaceCharref, hc.2.1, hc.2.2, rs, hint]
  have e2 : replaceCharref (35 :: 120 :: hs ++ [59]) = .ok (numRef (intHex hs)) := by
    have : (35 :: 120 :: hs ++ [59]) = 35 :: 120 :: (hs ++ [59]) := rfl
    rw [this]
    simp [replaceCharref, r2]
  rw [e1, e2]

/-- What `unescape` writes for a numeric reference is empty, or one scalar value, for every number. -/
def NumericValid : Prop :=
  ∀ n : Nat, numRef n = [] ∨ ∃ c, numRef n = [c] ∧ c ≤ 0x10FFFF ∧ ¬(0xD800 ≤ c ∧ c ≤ 0xDFFF)

theorem lookup_good (P : Nat → Prop) : ∀ (l : List (Nat × Nat)) (n c : Nat), l.lookup n = some c →
    (∀ p ∈ l, P p.2) → P c := by
  intro l
  induction l with
  | nil => intro n c h; simp at h
  | cons p t ih =>
    intro n c h hp
    simp only [List.lookup] at h
    split at h
    · cases h
      exact hp p (by simp)
    · exact ih n c h (fun q hq => hp q (by simp [hq]))

theorem numericValid_proven : NumericValid := by
  intro n
  unfold numRef
  split
  · rename_i c hl
    right
    refine ⟨c, rfl, ?_⟩
    exact lookup_good (fun c => c ≤ 0x10FFFF ∧ ¬(0xD800 ≤ c ∧ c ≤ 0xDFFF)) _ n c hl (by decide)
  · split
    · right
      exact ⟨0xFFFD, rfl, by decide, by decide⟩
    · rename_i h
      split
      · exact .inl rfl
      · right
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, not_or, not_and] at h
        refine ⟨n, rfl, by omega, ?_⟩
        intro ⟨h3, h4⟩
        exact h.1 h3 h4

theorem prefix_none (s : List Nat) : ∀ x, prefixLoop s x = none → ∀ y, 2 ≤ y → y ≤ x → look (s.take y) = none := by
  intro x
  induction x with
  | zero => intro _ y h1 h2; omega
  | succ x ih =>
    intro h y h1 h2
    cases x with
    | zero => omega
    | succ x =>
      simp only [prefixLoop] at h
      split at h
      · simp at h
      · rename_i hl
        by_cases hy : y = x + 2
        · subst hy; exact hl
        · exact ih h y h1 (by omega)

theorem prefix_some (s : List Nat) : ∀ x r, prefixLoop s x = some r → ∃ y v, 2 ≤ y ∧ y ≤ x ∧
    look (s.take y) = some v ∧ r = v ++ s.drop y ∧ ∀ z, y < z → z ≤ x → look (s.take z) = none := by
  intro x
  induction x with
  | zero => intro r h; simp [prefixLoop] at h
  | succ x ih =>
    intro r h
    cases x with
    | zero => simp [prefixLoop] at h
    | succ x =>
      simp only [prefixLoop] at h
      split at h
      · rename_i v hl
        simp only [Option.some.injEq] at h
        exact ⟨x + 2, v, by omega, by omega, hl, h.symm, fun z h1 h2 => by omega⟩
      · rename_i hl
        obtain ⟨y, v, h1, h2, h3, h4, h5⟩ := ih r h
        refine ⟨y, v, h1, by omega, h3, h4, ?_⟩
        intro z hz hz2
        by_cases he : z = x + 2
        · subst he; exact hl
        · exact h5 z hz (by omega)

/-- The named branch, "the longest matching name": the whole name, else the longest proper prefix of at
least two characters that is in the table, else the text as it stands. It holds on the real table. -/
def NamedLongest : Prop :=
  ∀ s : List Nat, s.head? ≠ some 35 →
    (∃ v, look s = some v ∧ replaceCharref s = .ok v) ∨
    (look s = none ∧ ∃ y v, 2 ≤ y ∧ y < s.length ∧ look (s.take y) = some v ∧
      replaceCharref s = .ok (v ++ s.drop y) ∧ ∀ z, y < z → z < s.length → look (s.take z) = none) ∨
    (look s = none ∧ (∀ y, 2 ≤ y → y < s.length → look (s.take y) = none) ∧ replaceCharref s = .ok (38 :: s))

theorem namedLongest_proven : NamedLongest := by
  intro s hs
  have hn : replaceCharref s = .ok (namedRef s) := by
    cases s with
    | nil => rfl
    | cons a t =>
      have : a ≠ 35 := by intro e; subst e; simp at hs
      simp [replaceCharref, this]
  cases hl : look s with
  | some v =>
    left
    exact ⟨v, rfl, by rw [hn]; simp [namedRef, hl]⟩
  | none =>
    right
    cases hp : prefixLoop s (s.length - 1) with
    | some r =>
      left
      obtain ⟨y, v, h1, h2, h3, h4, h5⟩ := prefix_some s _ r hp
      refine ⟨rfl, y, v, h1, by omega, h3, ?_, fun z h6 h7 => h5 z h6 (by omega)⟩
      rw [hn]
      simp [namedRef, hl, hp, h4]
    | none =>
      right
      refine ⟨rfl, fun y h1 h2 => prefix_none s _ hp y h1 (by omega), ?_⟩
      rw [hn]
      simp [namedRef, hl, hp]

/-! ### Where the digit limit is the only way to fail -/

theorem takeSpan_spec (p : Nat → Bool) : ∀ (n : Nat) (s : List Nat),
    (takeSpan p n s).1 ++ (takeSpan p n s).2 = s ∧ ∀ x ∈ (takeSpan p n s).1, p x = true := by
  intro n
  induction n with
  | zero => intro s; simp [takeSpan]
  | succ n ih =>
    intro s
    cases s with
    | nil => simp [takeSpan]
    | cons c r =>
      simp only [takeSpan]
      split
      · rename_i hc
        obtain ⟨h1, h2⟩ := ih r
        refine ⟨by simp [h1], ?_⟩
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hc
        · exact h2 x hx
      · simp

theorem optSemi_spec (s : List Nat) :
    (optSemi s).1 ++ (optSemi s).2 = s ∧ ((optSemi s).1 = [] ∨ (optSemi s).1 = [59]) := by
  unfold optSemi
  split <;> simp

theorem runSemi_spec (p : Nat → Bool) (m : Nat) (s g r : List Nat) (h : runSemi p m s = some (g, r)) :
    ∃ a b, g = a ++ b ∧ s = a ++ b ++ r ∧ a ≠ [] ∧ (∀ x ∈ a, p x = true) ∧ (b = [] ∨ b = [59]) := by
  obtain ⟨h1, h2⟩ := takeSpan_spec p m s
  obtain ⟨h3, h4⟩ := optSemi_spec (takeSpan p m s).2
  simp only [runSemi] at h
  split at h
  · simp at h
  · rename_i hne
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨_, _, rfl, ?_, ?_, h2, h4⟩
    · rw [List.append_assoc, h3, h1]
    · intro he
      rw [he] at hne
      simp at hne

/-- No run of more than 4300 decimal digits anywhere in the string. -/
def ShortRuns (s : List Nat) : Prop :=
  ∀ p ds q, s = p ++ ds ++ q → (∀ d ∈ ds, isDigit d = true) → ds.length ≤ 4300

theorem shortRuns_suffix (p s : List Nat) (h : ShortRuns (p ++ s)) : ShortRuns s := by
  intro a ds q he hd
  exact h (p ++ a) ds q (by rw [he]; simp) hd

theorem replaceCharref_named (g : List Nat) (hg : g.head? ≠ some 35) :
    replaceCharref g = .ok (namedRef g) := by
  cases g with
  | nil => rfl
  | cons a t =>
    have : a ≠ 35 := by intro e; subst e; simp at hg
    simp [replaceCharref, this]

/-- Each match is a prefix of the text, and with short runs its callback does not raise. -/
theorem matchRef_ok (r g rest : List Nat) (hm : matchRef r = some (g, rest)) (hs : ShortRuns r) :
    r = g ++ rest ∧ ∃ x, replaceCharref g = .ok x := by
  unfold matchRef at hm
  split at hm
  · rename_i t
    split at hm
    · rename_i g' r' he
      simp only [Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      obtain ⟨a, b, rfl, h2, hne, h4, h5⟩ := runSemi_spec _ _ _ _ _ he
      refine ⟨by simp [h2], ?_⟩
      obtain ⟨c, u, rfl⟩ := List.exists_cons_of_ne_nil hne
      have hc := isDigit_ne (h4 c (by simp))
      have hl : (c :: u).length ≤ 4300 := hs [35] (c :: u) (b ++ r') (by simp [h2]) h4
      have rs := rstrip_digits (c :: u) b (fun x hx => (isDigit_ne (h4 x hx)).1) h5
      have hint : ∃ n, intDec (c :: u) = .ok n := by
        simp only [intDec]
        rw [if_neg (by omega)]
        exact ⟨_, rfl⟩
      obtain ⟨n, hn⟩ := hint
      refine ⟨numRef n, ?_⟩
      have e : (35 :: ((c :: u) ++ b)) = 35 :: c :: (u ++ b) := rfl
      rw [e]
      have rs' : rstripSemi (c :: (u ++ b)) = c :: u := rs
      simp [replaceCharref, hc.2.1, hc.2.2, rs', hn]
    · split at hm
      · rename_i x u _
        split at hm
        · rename_i hx
          split at hm
          · rename_i g' r' he
            simp only [Option.some.injEq, Prod.mk.injEq] at hm
            obtain ⟨rfl, rfl⟩ := hm
            obtain ⟨a, b, rfl, h2, _, _, _⟩ := runSemi_spec _ _ _ _ _ he
            refine ⟨by simp [h2], numRef (intHex (rstripSemi (a ++ b))), ?_⟩
            simp [replaceCharref, hx]
          · simp at hm
        · simp at hm
      · simp at hm
  · rename_i hne
    obtain ⟨a, b, rfl, h2, hane, h4, _⟩ := runSemi_spec _ _ _ _ _ hm
    refine ⟨by simp [h2], _, replaceCharref_named _ ?_⟩
    obtain ⟨c, u, rfl⟩ := List.exists_cons_of_ne_nil hane
    have := h4 c (by simp)
    intro he
    have hc : c = 35 := by simpa using he
    subst hc
    simp [nameChar] at this

theorem sub_total : ∀ (f : Nat) (s : List Nat), s.length < f → ShortRuns s → ∃ y, subLoop f s = .ok y := by
  intro f
  induction f with
  | zero => intro _ h; omega
  | succ f ih =>
    intro s hl hs
    cases s with
    | nil => exact ⟨[], rfl⟩
    | cons c r =>
      simp only [List.length_cons] at hl
      have hr : ShortRuns r := shortRuns_suffix [c] r hs
      by_cases hc : c = 38
      · subst hc
        cases hm : matchRef r with
        | none =>
          obtain ⟨y, hy⟩ := ih r (by omega) hr
          exact ⟨38 :: y, by simp [subLoop, hm, hy]⟩
        | some m =>
          obtain ⟨g, rest⟩ := m
          obtain ⟨he, x, hx⟩ := matchRef_ok r g rest hm hr
          have hle : rest.length ≤ r.length := by rw [he]; simp
          obtain ⟨y, hy⟩ := ih rest (by omega) (by rw [he] at hr; exact shortRuns_suffix g rest hr)
          exact ⟨x ++ y, sub_ref f r g rest x y hm hx hy⟩
      · obtain ⟨y, hy⟩ := ih r (by omega) hr
        exact ⟨c :: y, sub_plain f c r y hc hy⟩

/-- Narrows `UnescapeTotal`: no run of more than 4300 decimal digits, which is what the refutation
excludes. The digit limit is the only exception `unescape` can raise on a `str`. -/
def UnescapeTotalNarrow : Prop := ∀ s : List Nat, ShortRuns s → (unescape s).toBool = true

theorem unescapeTotalNarrow_proven : UnescapeTotalNarrow := by
  intro s hs
  unfold unescape
  split
  · rfl
  · obtain ⟨y, hy⟩ := sub_total _ s (Nat.lt_succ_self _) hs
    rw [hy]
    rfl

end PyLean.TextLibs.Html
