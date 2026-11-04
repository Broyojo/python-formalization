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

/-! ## `float_from_string_inner` around the word -/

theorem word_first {s : List Nat} {P S : Nat} {target : List Nat}
    (ht : target = lowerInf ∨ target = lowerInfinity ∨ target = lowerNan)
    (hw : ∀ j, j < target.length → toLower (at_ s (P + S + j)) = target.getD j 0) :
    at_ s (P + S) = 105 ∨ at_ s (P + S) = 73 ∨ at_ s (P + S) = 110 ∨ at_ s (P + S) = 78 := by
  have hw0 := hw 0 (by rcases ht with rfl | rfl | rfl <;> decide)
  rcases ht with rfl | rfl | rfl
  · have := toLower_cases (by simpa [lowerInf] using hw0) (by decide : 97 ≤ 105 ∧ 105 ≤ 122); omega
  · have := toLower_cases (by simpa [lowerInfinity] using hw0) (by decide : 97 ≤ 105 ∧ 105 ≤ 122); omega
  · have := toLower_cases (by simpa [lowerNan] using hw0) (by decide : 97 ≤ 110 ∧ 110 ≤ 122); omega

theorem word_last {s : List Nat} {P S : Nat} {target : List Nat}
    (ht : target = lowerInf ∨ target = lowerInfinity ∨ target = lowerNan)
    (hw : ∀ j, j < target.length → toLower (at_ s (P + S + j)) = target.getD j 0) :
    isSpace (at_ s (P + S + target.length - 1)) = false := by
  rcases ht with rfl | rfl | rfl
  · have h := hw 2 (by decide)
    have := toLower_cases (by simpa [lowerInf] using h) (by decide : 97 ≤ 102 ∧ 102 ≤ 122)
    simp only [lowerInf, List.length]
    rw [show P + S + (0 + 1 + 1 + 1) - 1 = P + S + 2 by omega]
    rcases this with h | h <;> rw [h] <;> decide
  · have h := hw 7 (by decide)
    have := toLower_cases (by simpa [lowerInfinity] using h) (by decide : 97 ≤ 121 ∧ 121 ≤ 122)
    simp only [lowerInfinity, List.length]
    rw [show P + S + (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) - 1 = P + S + 7 by omega]
    rcases this with h | h <;> rw [h] <;> decide
  · have h := hw 2 (by decide)
    have := toLower_cases (by simpa [lowerNan] using h) (by decide : 97 ≤ 110 ∧ 110 ≤ 122)
    simp only [lowerNan, List.length]
    rw [show P + S + (0 + 1 + 1 + 1) - 1 = P + S + 2 by omega]
    rcases this with h | h <;> rw [h] <;> decide

theorem target_len {target : List Nat}
    (ht : target = lowerInf ∨ target = lowerInfinity ∨ target = lowerNan) : 3 ≤ target.length := by
  rcases ht with rfl | rfl | rfl <;> decide

/-- `float_from_string_inner` on a buffer holding spaces, `[sign] word`, and spaces from
`last` on: the value when the word ends at `last`, and `ValueError` otherwise. -/
theorem inner_word (s : List Nat) (P S : Nat) (neg : Bool) (target : List Nat) (last : Nat)
    (hS : (S = 0 ∧ neg = false) ∨ (S = 1 ∧ at_ s P = if neg then 45 else 43))
    (ht : target = lowerInf ∨ target = lowerInfinity ∨ target = lowerNan)
    (hw : ∀ j, j < target.length → toLower (at_ s (P + S + j)) = target.getD j 0)
    (hafter : target = lowerInf →
      toLower (at_ s (P + S + 3)) ≠ 105 ∨ toLower (at_ s (P + S + 4)) ≠ 110)
    (hpre : ∀ i, i < P → isSpace (at_ s i) = true)
    (hlast : P + S + target.length ≤ last) (hlen : last ≤ s.length)
    (hsp : ∀ i, last ≤ i → i < s.length → isSpace (at_ s i) = true)
    (hstop : isSpace (at_ s (last - 1)) = false) :
    float_from_string_inner s s.length =
      if P + S + target.length = last then
        .ok (if target = lowerNan then (if neg then qnan.neg else qnan) else F64.inf neg)
      else strToFloatError := by
  have h3 := target_len ht
  have h0 := word_first ht hw
  have hP : isSpace (at_ s P) = false := by
    rcases hS with ⟨rfl, _⟩ | ⟨_, hc⟩
    · simp only [Nat.add_zero] at h0; rcases h0 with h | h | h | h <;> rw [h] <;> decide
    · rw [hc]; cases neg <;> decide
  have hi0 := scanLimit_spaces s s.length P (by omega) hpre hP
  have hlast' := trimEnd_spaces s P last (by omega) hsp hstop (s.length - P) s.length (by omega) (Nat.le_refl _)
    (by omega)
  unfold float_from_string_inner
  simp only [hi0]
  have hne : (P == s.length) = false := by simp; omega
  simp only [hne, Bool.false_eq_true, ↓reduceIte, hlast', parse_word s P S neg target hS ht hw hafter]
  by_cases he : P + S + target.length = last
  · simp [he]
  · have : (P + S + target.length != last) = true := by simp [he]
    simp [this, he]

/-! ## The property, proven -/

theorem at_app_lt {l r : List Nat} {i : Nat} (h : i < l.length) : at_ (l ++ r) i = at_ l i := by
  unfold at_; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem at_mem {l : List Nat} {i : Nat} (h : i < l.length) : at_ l i ∈ l := by
  unfold at_; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem at_map_toLower {l : List Nat} {j : Nat} (h : j < l.length) :
    toLower (at_ l j) = (l.map toLower).getD j 0 := by
  unfold at_; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem space_or_zero_lower {c : Nat} (h : isSpace c = true ∨ c = 0) : toLower c ≠ 105 ∧ toLower c ≠ 110 := by
  unfold toLower isSpace at *; rcases h with h | h
  · simp at h; split <;> omega
  · subst h; decide

theorem at_post_lower (post : List Nat) (hpost : ∀ c ∈ post, isSpace c = true) (k : Nat) :
    toLower (at_ post k) ≠ 105 ∧ toLower (at_ post k) ≠ 110 := by
  apply space_or_zero_lower
  by_cases hk : k < post.length
  · left; exact hpost _ (at_mem hk)
  · right; exact at_ge_length (by omega)

theorem letter_of_lower {c : Nat} (h : toLower c ∈ [105, 110, 102, 116, 121, 97]) : c < 128 ∧ c ≠ 95 ∧ isSpace c = false := by
  have h' : toLower c = 105 ∨ toLower c = 110 ∨ toLower c = 102 ∨ toLower c = 116 ∨ toLower c = 121 ∨
      toLower c = 97 := by simpa using h
  unfold toLower at h'
  unfold isSpace
  split at h'
  · rename_i hc; simp at hc; refine ⟨by omega, by omega, ?_⟩; simp; omega
  · rename_i hc; refine ⟨by omega, by omega, ?_⟩; simp; omega

theorem no_underscore (s : List Nat) (h : ∀ c ∈ s, c ≠ 95) :
    _Py_string_to_number_with_underscores s "float" float_from_string_inner =
      float_from_string_inner s s.length := by
  unfold _Py_string_to_number_with_underscores
  have : ¬ (95 ∈ s.takeWhile (· != 0)) := fun hm => h 95 (List.takeWhile_subset _ hm) rfl
  simp [this]

theorem buf_facts (pre sgn word tail : List Nat) :
    (∀ i, i < pre.length → at_ (pre ++ sgn ++ word ++ tail) i = at_ pre i) ∧
    (∀ j, j < sgn.length → at_ (pre ++ sgn ++ word ++ tail) (pre.length + j) = at_ sgn j) ∧
    (∀ j, j < word.length →
      at_ (pre ++ sgn ++ word ++ tail) (pre.length + sgn.length + j) = at_ word j) ∧
    (∀ k, at_ (pre ++ sgn ++ word ++ tail) (pre.length + sgn.length + word.length + k) = at_ tail k) ∧
    (pre ++ sgn ++ word ++ tail).length = pre.length + sgn.length + word.length + tail.length := by
  refine ⟨fun i h => ?_, fun j h => ?_, fun j h => ?_, fun k => ?_, by simp; omega⟩
  · rw [at_app_lt (by simp <;> omega), at_app_lt (by simp <;> omega), at_app_lt h]
  · rw [at_app_lt (by simp <;> omega), at_app_lt (by simp <;> omega), at_append_ge (by omega)]
    congr 1 <;> omega
  · rw [at_app_lt (by simp <;> omega), at_append_ge (by simp <;> omega)]
    congr 1 <;> simp <;> omega
  · rw [at_append_ge (by simp <;> omega)]
    congr 1 <;> simp <;> omega

theorem fromString_main (pre sgn word tail : List Nat) (neg : Bool) (target : List Nat)
    (hpre : ∀ c ∈ pre, isSpace c = true)
    (hsgn : (sgn = [] ∧ neg = false) ∨ (sgn = [43] ∧ neg = false) ∨ (sgn = [45] ∧ neg = true))
    (ht : word.map toLower = target)
    (ht' : target = lowerInf ∨ target = lowerInfinity ∨ target = lowerNan)
    (hafter : target = lowerInf → toLower (at_ tail 0) ≠ 105 ∨ toLower (at_ tail 1) ≠ 110)
    (last : Nat) (hlast : pre.length + sgn.length + word.length ≤ last)
    (hlen : last ≤ (pre ++ sgn ++ word ++ tail).length)
    (hsp : ∀ i, last ≤ i → i < (pre ++ sgn ++ word ++ tail).length →
      isSpace (at_ (pre ++ sgn ++ word ++ tail) i) = true)
    (hstop : isSpace (at_ (pre ++ sgn ++ word ++ tail) (last - 1)) = false) :
    float_from_string_inner (pre ++ sgn ++ word ++ tail) (pre ++ sgn ++ word ++ tail).length =
      if pre.length + sgn.length + word.length = last then
        .ok (if target = lowerNan then (if neg then qnan.neg else qnan) else F64.inf neg)
      else strToFloatError := by
  obtain ⟨f1, f2, f3, f4, _⟩ := buf_facts pre sgn word tail
  have hWlen : word.length = target.length := by rw [← ht, List.length_map]
  have hw : ∀ j, j < target.length →
      toLower (at_ (pre ++ sgn ++ word ++ tail) (pre.length + sgn.length + j)) = target.getD j 0 := by
    intro j hj
    rw [f3 j (by omega), at_map_toLower (by omega), ht]
  have hS : (sgn.length = 0 ∧ neg = false) ∨
      (sgn.length = 1 ∧ at_ (pre ++ sgn ++ word ++ tail) pre.length = if neg then 45 else 43) := by
    rcases hsgn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; exact ⟨rfl, rfl⟩
    · right; refine ⟨rfl, ?_⟩; have := f2 0 (by decide); rw [Nat.add_zero] at this; rw [this]; rfl
    · right; refine ⟨rfl, ?_⟩; have := f2 0 (by decide); rw [Nat.add_zero] at this; rw [this]; rfl
  have hafter' : target = lowerInf →
      toLower (at_ (pre ++ sgn ++ word ++ tail) (pre.length + sgn.length + 3)) ≠ 105 ∨
      toLower (at_ (pre ++ sgn ++ word ++ tail) (pre.length + sgn.length + 4)) ≠ 110 := by
    intro h
    have hW3 : word.length = 3 := by rw [hWlen, h]; rfl
    have a := f4 0
    have b := f4 1
    rw [hW3] at a b
    rw [show pre.length + sgn.length + 3 = pre.length + sgn.length + 3 + 0 by omega, a,
      show pre.length + sgn.length + 4 = pre.length + sgn.length + 3 + 1 by omega, b]
    exact hafter h
  have hpre' : ∀ i, i < pre.length → isSpace (at_ (pre ++ sgn ++ word ++ tail) i) = true := by
    intro i hi; rw [f1 i hi]; exact hpre _ (at_mem hi)
  have := inner_word (pre ++ sgn ++ word ++ tail) pre.length sgn.length neg target last hS ht' hw hafter'
    hpre' (by omega) hlen hsp hstop
  rw [this, hWlen]

theorem fromStringInfNan_proven : FromStringInfNan := by
  intro pre post sgn word hpre hpost hsgn hword
  simp only []
  generalize ht : word.map toLower = target at hword ⊢
  have hletter : ∀ c ∈ word, c < 128 ∧ c ≠ 95 ∧ isSpace c = false := by
    intro c hc
    apply letter_of_lower
    have : toLower c ∈ target := by rw [← ht]; exact List.mem_map_of_mem hc
    rcases hword with rfl | rfl | rfl <;> simp [lowerInf, lowerInfinity, lowerNan] at this ⊢ <;> omega
  have hWlen : word.length = target.length := by rw [← ht, List.length_map]
  have h3 := target_len hword
  obtain ⟨neg, hsgn', hneg⟩ : ∃ neg : Bool,
      ((sgn = [] ∧ neg = false) ∨ (sgn = [43] ∧ neg = false) ∨ (sgn = [45] ∧ neg = true)) ∧
      (decide (sgn = [45]) = neg) := by
    rcases hsgn with rfl | rfl | rfl
    · exact ⟨false, Or.inl ⟨rfl, rfl⟩, by decide⟩
    · exact ⟨false, Or.inr (Or.inl ⟨rfl, rfl⟩), by decide⟩
    · exact ⟨true, Or.inr (Or.inr ⟨rfl, rfl⟩), by decide⟩
  have hsgnc : ∀ c ∈ sgn, c < 128 ∧ c ≠ 95 ∧ isSpace c = false := by
    rcases hsgn with rfl | rfl | rfl <;> simp <;> decide
  have hspc : ∀ c, isSpace c = true → c < 128 ∧ c ≠ 95 := by
    intro c h; unfold isSpace at h; simp at h; omega
  obtain ⟨f1, f2, f3, f4, flen⟩ := buf_facts pre sgn word post
  have hstop0 : isSpace (at_ (pre ++ sgn ++ word ++ post) (pre.length + sgn.length + word.length - 1)) = false := by
    have := f3 (word.length - 1) (by omega)
    rw [show pre.length + sgn.length + word.length - 1 = pre.length + sgn.length + (word.length - 1) by omega,
      this]
    exact (hletter _ (at_mem (by omega))).2.2
  have hsp0 : ∀ i, pre.length + sgn.length + word.length ≤ i → i < (pre ++ sgn ++ word ++ post).length →
      isSpace (at_ (pre ++ sgn ++ word ++ post) i) = true := by
    intro i h1 h2
    have := f4 (i - (pre.length + sgn.length + word.length))
    rw [show pre.length + sgn.length + word.length + (i - (pre.length + sgn.length + word.length)) = i by omega]
      at this
    rw [this]; exact hpost _ (at_mem (by rw [flen] at h2; omega))
  have hafter0 : target = lowerInf → toLower (at_ post 0) ≠ 105 ∨ toLower (at_ post 1) ≠ 110 :=
    fun _ => Or.inl (at_post_lower post hpost 0).1
  have hmain := fromString_main pre sgn word post neg target hpre hsgn' ht hword hafter0
    (pre.length + sgn.length + word.length) (Nat.le_refl _) (by rw [flen]; omega) hsp0 hstop0
  simp only [↓reduceIte] at hmain
  have hall : ∀ c ∈ pre ++ sgn ++ word ++ post, c < 128 ∧ c ≠ 95 := by
    intro c hc
    simp only [List.mem_append] at hc
    rcases hc with ((h | h) | h) | h
    · exact hspc c (hpre c h)
    · exact ⟨(hsgnc c h).1, (hsgnc c h).2.1⟩
    · exact ⟨(hletter c h).1, (hletter c h).2.1⟩
    · exact hspc c (hpost c h)
  have hstr : transformDecimalAndSpace (pre ++ sgn ++ word ++ post) = pre ++ sgn ++ word ++ post := by
    unfold transformDecimalAndSpace
    have : (pre ++ sgn ++ word ++ post).all (· < 128) = true := by
      rw [List.all_eq_true]; intro c hc; simpa using (hall c hc).1
    rw [if_pos this]
  refine ⟨?_, ?_, fun c hc1 hc2 => ?_⟩
  · show _Py_string_to_number_with_underscores _ "float" float_from_string_inner = _
    rw [no_underscore _ (fun c hc => (hall c hc).2), hmain, hneg]
    have hiff : (sgn = [45]) = (neg = true) := by rw [← hneg]; simp
    simp only [hiff]
  · show _Py_string_to_number_with_underscores (transformDecimalAndSpace _) "float" float_from_string_inner = _
    rw [hstr, no_underscore _ (fun c hc => (hall c hc).2), hmain, hneg]
    have hiff : (sgn = [45]) = (neg = true) := by rw [← hneg]; simp
    simp only [hiff]
  · show _Py_string_to_number_with_underscores _ "float" float_from_string_inner = _
    obtain ⟨g1, g2, g3, g4, glen⟩ := buf_facts pre sgn word (c :: post)
    have hall' : ∀ d ∈ pre ++ sgn ++ word ++ c :: post, d ≠ 95 := by
      intro d hd
      simp only [List.mem_append, List.mem_cons] at hd
      rcases hd with ((h | h) | h) | h | h
      · exact (hspc d (hpre d h)).2
      · exact (hsgnc d h).2.1
      · exact (hletter d h).2.1
      · rw [h]; exact hc2
      · exact (hspc d (hpost d h)).2
    rw [no_underscore _ hall']
    have hstop1 : isSpace (at_ (pre ++ sgn ++ word ++ c :: post) (pre.length + sgn.length + word.length + 1 - 1)) = false := by
      rw [show pre.length + sgn.length + word.length + 1 - 1 = pre.length + sgn.length + word.length + 0 by omega, g4 0]
      exact hc1
    have hsp1 : ∀ i, pre.length + sgn.length + word.length + 1 ≤ i → i < (pre ++ sgn ++ word ++ c :: post).length →
        isSpace (at_ (pre ++ sgn ++ word ++ c :: post) i) = true := by
      intro i h1 h2
      have := g4 (i - (pre.length + sgn.length + word.length))
      rw [show pre.length + sgn.length + word.length + (i - (pre.length + sgn.length + word.length)) = i by omega]
        at this
      rw [this]
      have hk : i - (pre.length + sgn.length + word.length) = (i - (pre.length + sgn.length + word.length) - 1) + 1 := by
        omega
      rw [hk]
      show isSpace (at_ post _) = true
      exact hpost _ (at_mem (by rw [glen] at h2; simp at h2; omega))
    have hafter1 : target = lowerInf → toLower (at_ (c :: post) 0) ≠ 105 ∨ toLower (at_ (c :: post) 1) ≠ 110 :=
      fun _ => Or.inr (at_post_lower post hpost 0).2
    have hm := fromString_main pre sgn word (c :: post) neg target hpre hsgn' ht hword hafter1
      (pre.length + sgn.length + word.length + 1) (by omega) (by rw [glen]; simp <;> omega) hsp1 hstop1
    rw [hm]
    have : ¬ (pre.length + sgn.length + word.length = pre.length + sgn.length + word.length + 1) := by omega
    simp [this]

end PyLean.Binary64
