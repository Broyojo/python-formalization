import PyLean.Binary64.FloatObjProps
import PyLean.Binary64.StrtodProps

/-!
`float_from_string_inner` and `PyFloat_FromString` (floatobject.c:140-227, CPython 3.15.2) on
the strings that name an infinity or a NaN: the leading-whitespace scan (:145-148), the
trailing-whitespace strip (:156-159), `PyOS_string_to_double` falling back to
`_Py_parse_inf_or_nan` (pystrtod.c:92-113), and the `end != last` check (:165).
-/

namespace PyLean.Binary64

open PyLean F64

/-! ## Positions in an appended buffer -/

theorem at_append_lt {l r : List Nat} {i : Nat} (h : i < l.length) : at_ (l ++ r) i = l.getD i 0 := by
  unfold at_
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem at_append_ge {l r : List Nat} {i : Nat} (h : l.length ≤ i) :
    at_ (l ++ r) i = at_ r (i - l.length) := by
  unfold at_
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem at_ge_length {l : List Nat} {i : Nat} (h : l.length ≤ i) : at_ l i = 0 := by
  unfold at_
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

/-! ## The two whitespace scans -/

theorem scanLimit_go_spaces (s : List Nat) (len P : Nat) (hP : P < len)
    (hsp : ∀ i, i < P → isSpace (at_ s i) = true) (hstop : isSpace (at_ s P) = false) :
    ∀ fuel k, k ≤ P → P - k < fuel →
      float_from_string_inner.scanLimit.go s isSpace len fuel k = P := by
  intro fuel
  induction fuel with
  | zero => intro k _ h; omega
  | succ f ih =>
    intro k hk hf
    unfold float_from_string_inner.scanLimit.go
    by_cases hkP : k = P
    · subst hkP; simp [hstop]
    · have hlt : k < P := by omega
      have hl : decide (k < len) = true := by simp; omega
      simp only [hl, hsp k hlt, Bool.and_self, ↓reduceIte]
      exact ih (k + 1) (by omega) (by omega)

theorem scanLimit_spaces (s : List Nat) (len P : Nat) (hP : P < len)
    (hsp : ∀ i, i < P → isSpace (at_ s i) = true) (hstop : isSpace (at_ s P) = false) :
    float_from_string_inner.scanLimit s isSpace len 0 = P := by
  unfold float_from_string_inner.scanLimit
  exact scanLimit_go_spaces s len P hP hsp hstop (len + 1) 0 (by omega) (by omega)

theorem trimEnd_spaces (s : List Nat) (i0 L : Nat) (hL : i0 + 1 < L)
    (hspace : ∀ i, L ≤ i → i < s.length → isSpace (at_ s i) = true)
    (hstop : isSpace (at_ s (L - 1)) = false) :
    ∀ fuel last, L ≤ last → last ≤ s.length → last - L ≤ fuel →
      float_from_string_inner.trimEnd s i0 fuel last = L := by
  intro fuel
  induction fuel with
  | zero =>
    intro last h1 _ h3
    have : last = L := by omega
    subst this; rfl
  | succ f ih =>
    intro last h1 h2 h3
    unfold float_from_string_inner.trimEnd
    by_cases hlast : last = L
    · subst hlast; simp [hstop]
    · have hc : decide (i0 + 1 < last) = true := by simp; omega
      have hs : isSpace (at_ s (last - 1)) = true := hspace (last - 1) (by omega) (by omega)
      simp only [hc, hs, Bool.and_self, ↓reduceIte]
      exact ih (last - 1) (by omega) (by omega) (by omega)

/-! ## `strtodParse` on a letter -/

theorem strtodParse_letter (s : List Nat) (p : Nat)
    (hq : let q := if at_ s p == 45 || at_ s p == 43 then p + 1 else p
          isDigit (at_ s q) = false ∧ at_ s q ≠ 46) :
    strtodParse s p = none := by
  obtain ⟨hd, hdot⟩ := hq
  have hz : ∀ q, isDigit (at_ s q) = false → (at_ s q == 48) = false := by
    intro q h
    have : at_ s q ≠ 48 := fun e => by rw [e] at h; exact absurd h (by decide)
    simpa using this
  have hdot' : ∀ q, at_ s q ≠ 46 → (at_ s q == 46) = false := by intro q h; simpa using h
  have stops : ∀ q, isDigit (at_ s q) = false → at_ s q ≠ 46 →
      scanFrom s (fun x => x == 48) q = q ∧ scanFrom s isDigit q = q ∧ (at_ s q == 46) = false :=
    fun q h1 h2 => ⟨scanFrom_stop (p := fun x => x == 48) (hz q h1), scanFrom_stop h1, hdot' q h2⟩
  unfold strtodParse
  by_cases h1 : at_ s p == 45
  · simp only [h1, Bool.true_or, ↓reduceIte] at hd hdot
    obtain ⟨a, b, c⟩ := stops _ hd hdot
    simp [h1, a, b, c, bind, Option.bind]
  · by_cases h2 : at_ s p == 43
    · simp only [h1, h2, Bool.or_true, ↓reduceIte] at hd hdot
      obtain ⟨a, b, c⟩ := stops _ hd hdot
      simp [h1, h2, a, b, c, bind, Option.bind]
    · simp only [h1, h2, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hd hdot
      obtain ⟨a, b, c⟩ := stops _ hd hdot
      simp [h1, h2, a, b, c, bind, Option.bind]

/-! ## The property -/

def lowerInf : List Nat := [105, 110, 102]
def lowerInfinity : List Nat := [105, 110, 102, 105, 110, 105, 116, 121]
def lowerNan : List Nat := [110, 97, 110]

/-- `float()` on `[spaces] [sign] word [spaces]`, as bytes or as an ASCII str, where `word`
spells `inf`, `infinity` or `nan` in any mix of cases: an infinity, or a NaN, with the sign.
The same with one more non-space byte `c` after the word (other than `_`) raises
`ValueError`, from the `end != last` check: `float('infx')`, `float('nan1')`. -/
def FromStringInfNan : Prop :=
  ∀ (pre post sgn word : List Nat),
    (∀ c ∈ pre, isSpace c = true) → (∀ c ∈ post, isSpace c = true) →
    (sgn = [] ∨ sgn = [43] ∨ sgn = [45]) →
    (word.map toLower = lowerInf ∨ word.map toLower = lowerInfinity ∨ word.map toLower = lowerNan) →
    let v : F64 :=
      if word.map toLower = lowerNan then (if sgn = [45] then qnan.neg else qnan)
      else F64.inf (sgn = [45])
    PyFloat_FromString (.bytes (pre ++ sgn ++ word ++ post)) = .ok v ∧
    PyFloat_FromString (.str (pre ++ sgn ++ word ++ post)) = .ok v ∧
    (∀ c, isSpace c = false → c ≠ 95 →
      PyFloat_FromString (.bytes (pre ++ sgn ++ word ++ c :: post)) = strToFloatError)

/-! ## The parse at the first non-space -/

theorem toLower_cases {c t : Nat} (h : toLower c = t) (ht : 97 ≤ t ∧ t ≤ 122) : c = t ∨ c = t - 32 := by
  unfold toLower at h; split at h <;> omega

/-- `PyOS_string_to_double(s + P, &end, NULL)` on `[sign] word`, where the word is read
case-insensitively: `_Py_dg_strtod` consumes nothing, `_Py_parse_inf_or_nan` reads the
word, and the end is just past it. -/
theorem parse_word (s : List Nat) (P S : Nat) (neg : Bool) (target : List Nat)
    (hS : (S = 0 ∧ neg = false) ∨ (S = 1 ∧ at_ s P = if neg then 45 else 43))
    (ht : target = lowerInf ∨ target = lowerInfinity ∨ target = lowerNan)
    (hw : ∀ j, j < target.length → toLower (at_ s (P + S + j)) = target.getD j 0)
    (hafter : target = lowerInf →
      toLower (at_ s (P + S + 3)) ≠ 105 ∨ toLower (at_ s (P + S + 4)) ≠ 110) :
    PyOS_string_to_double s P true none =
      some (.ok (if target = lowerNan then (if neg then qnan.neg else qnan) else F64.inf neg),
        P + S + target.length) := by
  have hw0 := hw 0 (by rcases ht with rfl | rfl | rfl <;> decide)
  have h0 : at_ s (P + S) = 105 ∨ at_ s (P + S) = 73 ∨ at_ s (P + S) = 110 ∨ at_ s (P + S) = 78 := by
    rcases ht with rfl | rfl | rfl
    · have := toLower_cases (by simpa [lowerInf] using hw0) (by decide : 97 ≤ 105 ∧ 105 ≤ 122); omega
    · have := toLower_cases (by simpa [lowerInfinity] using hw0) (by decide : 97 ≤ 105 ∧ 105 ≤ 122); omega
    · have := toLower_cases (by simpa [lowerNan] using hw0) (by decide : 97 ≤ 110 ∧ 110 ≤ 122); omega
  -- the sign
  have hsign : (if at_ s P == 45 || at_ s P == 43 then P + 1 else P) = P + S ∧
      ((at_ s P == 45) = neg) ∧
      (if at_ s P == 45 then (true, P + 1) else if at_ s P == 43 then (false, P + 1) else (false, P)) =
        (neg, P + S) := by
    rcases hS with ⟨rfl, rfl⟩ | ⟨rfl, hc⟩
    · have : (at_ s P == 45) = false := by simp only [Nat.add_zero] at h0; simp; omega
      have h2 : (at_ s P == 43) = false := by simp only [Nat.add_zero] at h0; simp; omega
      simp [this, h2]
    · rw [hc]; cases neg <;> simp
  obtain ⟨hq, hneg, hpair⟩ := hsign
  have hparse : strtodParse s P = none := by
    apply strtodParse_letter
    rw [hq]
    refine ⟨?_, ?_⟩ <;> rcases h0 with h | h | h | h <;> rw [h] <;> decide
  have hdg : _Py_dg_strtod s P = some (d0, P, false) := by simp [_Py_dg_strtod, hparse]
  have cim := caseInsensitiveMatch_proven
  have hinf : case_insensitive_match s (P + S) lowerInf = (target != lowerNan) := by
    rcases ht with rfl | rfl | rfl
    · simp only [lowerInf, ne_eq, bne_iff_ne]
      have : case_insensitive_match s (P + S) [105, 110, 102] = true := by
        rw [cim]; intro j hj; exact hw j hj
      rw [this]; decide
    · simp only [lowerInf, lowerInfinity]
      have : case_insensitive_match s (P + S) [105, 110, 102] = true := by
        rw [cim]; intro j hj
        have h := hw j (by simp [lowerInfinity]; simp at hj; omega)
        simp at hj
        rcases j with _ | _ | _ | j
        · simpa [lowerInfinity] using h
        · simpa [lowerInfinity] using h
        · simpa [lowerInfinity] using h
        · omega
      rw [this]; decide
    · cases hc : case_insensitive_match s (P + S) lowerInf
      · decide
      · have := (cim _ _ _).1 hc 0 (by decide)
        simp only [Nat.add_zero] at this hw0
        rw [this] at hw0; simp [lowerInf, lowerNan] at hw0
  have hnan : target = lowerNan → case_insensitive_match s (P + S) lowerNan = true := by
    intro h; subst h; rw [cim]; intro j hj; exact hw j hj
  have hinity : target ≠ lowerNan →
      case_insensitive_match s (P + S + 3) [105, 110, 105, 116, 121] = (target == lowerInfinity) := by
    intro hn
    rcases ht with rfl | rfl | rfl
    · cases hc : case_insensitive_match s (P + S + 3) [105, 110, 105, 116, 121]
      · decide
      · exfalso
        have a := (cim _ _ _).1 hc 0 (by decide)
        have b := (cim _ _ _).1 hc 1 (by decide)
        simp only [Nat.add_zero] at a b
        rcases hafter rfl with h | h
        · exact h (by simpa using a)
        · exact h (by rw [show P + S + 4 = P + S + 3 + 1 by omega]; simpa using b)
    · have : case_insensitive_match s (P + S + 3) [105, 110, 105, 116, 121] = true := by
        rw [cim]; intro j hj
        have := hw (3 + j) (by simp [lowerInfinity] at hj ⊢; omega)
        rw [show P + S + (3 + j) = P + S + 3 + j by omega] at this
        rw [this]
        simp at hj
        rcases j with _ | _ | _ | _ | _ | j <;> first | rfl | omega
      rw [this]; decide
    · exact absurd rfl hn
  unfold PyOS_string_to_double _PyOS_ascii_strtod
  simp only [hdg, beq_self_eq_true, ↓reduceIte]
  unfold _Py_parse_inf_or_nan
  simp only [hpair]
  by_cases hn : target = lowerNan
  · have hf : case_insensitive_match s (P + S) lowerInf = false := by rw [hinf]; simp [hn]
    simp only [lowerInf] at hf
    simp only [hf, Bool.false_eq_true, ↓reduceIte]
    have := hnan hn
    simp only [lowerNan] at this
    simp only [this, ↓reduceIte, hn]
    subst hn
    simp [lowerNan] <;> omega
  · have hf : case_insensitive_match s (P + S) lowerInf = true := by rw [hinf]; simp [hn]
    simp only [lowerInf] at hf
    simp only [hf, ↓reduceIte, hinity hn, hn]
    rcases ht with rfl | rfl | rfl
    · simp [lowerInf, lowerInfinity] <;> omega
    · simp [lowerInfinity] <;> omega
    · exact absurd rfl hn

end PyLean.Binary64
