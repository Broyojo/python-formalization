import PyLean.PyGrammar.Unparse.Python
import PyLean.PyGrammar.Peg.Strings

/-!
A round trip that runs through the real decoder. `ast.unparse` writes a string constant as its
`repr`, and the parser reads it back with `_PyPegen_parse_string`, which calls
`decode_unicode_with_escapes` and `_PyUnicode_DecodeUnicodeEscapeInternal2`. `StrReprRoundTrip` says
this gives back the string.

The narrowing is that `repr` must produce pure ASCII: a printable non-ASCII character is written
as itself, and reading it back needs UTF-8 decoding, not covered here. Every other character is
covered, including controls, quotes, backslashes, unprintable non-ASCII and lone surrogates.
-/

namespace PyLean.PyGrammar.Unparse

open Lexer Peg

/-- `buf` holds `l` from `p`. -/
def At (buf : Array Nat) (p : Nat) (l : List Nat) : Prop :=
  ∀ i, i < l.length → p + i < buf.size ∧ buf.getD (p + i) 0 = l.getD i 0

theorem At.left {buf : Array Nat} {p : Nat} {a b : List Nat} (h : At buf p (a ++ b)) : At buf p a := by
  intro i hi
  have := h i (by simp; omega)
  refine ⟨this.1, ?_⟩
  rw [this.2]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem At.right {buf : Array Nat} {p : Nat} {a b : List Nat} (h : At buf p (a ++ b)) :
    At buf (p + a.length) b := by
  intro i hi
  have := h (a.length + i) (by simp; omega)
  have e : p + a.length + i = p + (a.length + i) := by omega
  rw [e]
  refine ⟨this.1, ?_⟩
  rw [this.2, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega)]
  simp

theorem digitVal_hexDigit : ∀ d, d < 16 → digitVal (hexDigit d) = d := by decide

theorem hexDigits_succ (buf : Array Nat) (w p ch : Nat) :
    hexDigits buf (w + 1) p ch =
      match hexDigits buf w p ch with
      | .ok (c, q) =>
        if q ≥ buf.size then .error q
        else if digitVal (buf.getD q 0) < 16 then .ok (c <<< 4 + digitVal (buf.getD q 0), q + 1)
        else .error q
      | .error e => .error e := by
  induction w generalizing p ch with
  | zero => simp [hexDigits]
  | succ w ih =>
    have e1 : hexDigits buf (w + 1 + 1) p ch =
        if p ≥ buf.size then .error p
        else if digitVal (buf.getD p 0) < 16 then
          hexDigits buf (w + 1) (p + 1) (ch <<< 4 + digitVal (buf.getD p 0))
        else .error p := by
      rw [hexDigits]
    have e2 : hexDigits buf (w + 1) p ch =
        if p ≥ buf.size then .error p
        else if digitVal (buf.getD p 0) < 16 then
          hexDigits buf w (p + 1) (ch <<< 4 + digitVal (buf.getD p 0))
        else .error p := by
      rw [hexDigits]
    rw [e1, e2]
    by_cases h1 : p ≥ buf.size
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : digitVal (buf.getD p 0) < 16
      · rw [if_pos h2, if_pos h2, ih]
      · rw [if_neg h2, if_neg h2]

theorem hexDigits_hexN (buf : Array Nat) (w : Nat) : ∀ (n p ch : Nat), n < 16 ^ w →
    At buf p (hexN n w) → hexDigits buf w p ch = .ok (ch * 16 ^ w + n, p + w) := by
  induction w with
  | zero =>
    intro n p ch hn _
    have : n = 0 := by simpa using hn
    subst this
    simp [hexDigits]
  | succ w ih =>
    intro n p ch hn ha
    have hsplit : hexN n (w + 1) = hexN (n >>> 4) w ++ [hexDigit (n &&& 15)] := rfl
    rw [hsplit] at ha
    have hlen : (hexN (n >>> 4) w).length = w := by
      clear ih ha hsplit hn
      induction w generalizing n with
      | zero => rfl
      | succ w ih =>
        show (hexN (n >>> 4 >>> 4) w ++ [hexDigit (n >>> 4 &&& 15)]).length = _
        simp [ih]
    have hshift : n >>> 4 = n / 16 := by simp [Nat.shiftRight_eq_div_pow]
    have hand : n &&& 15 = n % 16 := Nat.and_two_pow_sub_one_eq_mod n 4
    have hp : (16 : Nat) ^ (w + 1) = 16 ^ w * 16 := by rw [Nat.pow_succ]
    have hq : n / 16 < 16 ^ w := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      omega
    have h1 := ih (n >>> 4) p ch (by rw [hshift]; exact hq) ha.left
    have h2 := ha.right
    rw [hlen] at h2
    obtain ⟨h3, h4⟩ := h2 0 (by simp)
    have hd : digitVal (buf.getD (p + w) 0) = n % 16 := by
      have : buf.getD (p + w) 0 = hexDigit (n &&& 15) := by simpa using h4
      rw [this, hand]
      exact digitVal_hexDigit _ (Nat.mod_lt _ (by decide))
    have hs : p + w < buf.size := by simpa using h3
    rw [hexDigits_succ, h1]
    dsimp only
    rw [if_neg (by omega), hd, if_pos (Nat.mod_lt _ (by decide))]
    have e : (ch * 16 ^ w + n >>> 4) <<< 4 + n % 16 = ch * 16 ^ (w + 1) + n := by
      rw [hshift, Nat.shiftLeft_eq, hp]
      have h5 : n = 16 * (n / 16) + n % 16 := (Nat.div_add_mod n 16).symm
      generalize n / 16 = a at *
      generalize n % 16 = b at *
      have : ch * (16 ^ w * 16) = ch * 16 ^ w * 16 := (Nat.mul_assoc _ _ _).symm
      rw [this]
      generalize ch * 16 ^ w = m
      show (m + a) * 2 ^ 4 + b = _
      omega
    rw [e]
    rfl

/-- `\\` followed by a one-letter escape. -/
theorem dec_simple (ucn : List (List Nat × Nat)) (buf : Array Nat) (f p : Nat) (acc : List Nat)
    (inv : Option Nat) (x v : Nat) (hs : p + 1 < buf.size) (h0 : buf.getD p 0 = 92)
    (h1 : buf.getD (p + 1) 0 = x)
    (hx : (x = 92 ∧ v = 92) ∨ (x = 39 ∧ v = 39) ∨ (x = 34 ∧ v = 34) ∨ (x = 116 ∧ v = 9) ∨
      (x = 110 ∧ v = 10) ∨ (x = 114 ∧ v = 13)) :
    decodeUnicodeEscape ucn buf (f + 1) p acc inv =
      decodeUnicodeEscape ucn buf f (p + 2) (v :: acc) inv := by
  have h2 : ¬ p ≥ buf.size := by omega
  have h3 : ¬ p + 1 ≥ buf.size := by omega
  rw [decodeUnicodeEscape]
  rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [h0, h1, h2, h3]

/-- `\xNN`, `\uNNNN` or `\UNNNNNNNN`. -/
theorem dec_hex (ucn : List (List Nat × Nat)) (buf : Array Nat) (f p : Nat) (acc : List Nat)
    (inv : Option Nat) (x cnt c : Nat) (hs : p + 1 < buf.size) (h0 : buf.getD p 0 = 92)
    (h1 : buf.getD (p + 1) 0 = x)
    (hx : (x = 120 ∧ cnt = 2) ∨ (x = 117 ∧ cnt = 4) ∨ (x = 85 ∧ cnt = 8))
    (hd : hexDigits buf cnt (p + 2) 0 = .ok (c, p + 2 + cnt)) (hc : c ≤ 0x10FFFF) :
    decodeUnicodeEscape ucn buf (f + 1) p acc inv =
      decodeUnicodeEscape ucn buf f (p + 2 + cnt) (c :: acc) inv := by
  have h2 : ¬ p ≥ buf.size := by omega
  have h3 : ¬ p + 1 ≥ buf.size := by omega
  have h4 : ¬ c > 0x10FFFF := by omega
  rw [decodeUnicodeEscape]
  rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [h0, h1, h2, h3, h4, hd]

theorem dec_plain (ucn : List (List Nat × Nat)) (buf : Array Nat) (f p : Nat) (acc : List Nat)
    (inv : Option Nat) (c : Nat) (hs : p < buf.size) (h0 : buf.getD p 0 = c) (hc : c ≠ 92) :
    decodeUnicodeEscape ucn buf (f + 1) p acc inv =
      decodeUnicodeEscape ucn buf f (p + 1) (c :: acc) inv := by
  have h2 : ¬ p ≥ buf.size := by omega
  rw [decodeUnicodeEscape]
  simp [h0, h2, hc]

theorem hexN_length (n w : Nat) : (hexN n w).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih =>
    show (hexN (n >>> 4) w ++ [hexDigit (n &&& 15)]).length = _
    simp [ih]

theorem at_pair {buf : Array Nat} {p a b : Nat} {l : List Nat} (h : At buf p (a :: b :: l)) :
    p + 1 < buf.size ∧ buf.getD p 0 = a ∧ buf.getD (p + 1) 0 = b := by
  have h0 := h 0 (by simp)
  have h1 := h 1 (by simp)
  exact ⟨h1.1, by simpa using h0.2, by simpa using h1.2⟩

theorem dec_hexEscape (ucn : List (List Nat × Nat)) (buf : Array Nat) (f p : Nat) (acc : List Nat)
    (inv : Option Nat) (c : Nat) (hc : c ≤ 0x10FFFF) (ha : At buf p (hexEscape c)) :
    decodeUnicodeEscape ucn buf (f + 1) p acc inv =
      decodeUnicodeEscape ucn buf f (p + (hexEscape c).length) (c :: acc) inv := by
  have key : ∀ (x cnt : Nat), (x = 120 ∧ cnt = 2) ∨ (x = 117 ∧ cnt = 4) ∨ (x = 85 ∧ cnt = 8) →
      c < 16 ^ cnt → At buf p (92 :: x :: hexN c cnt) →
      decodeUnicodeEscape ucn buf (f + 1) p acc inv =
        decodeUnicodeEscape ucn buf f (p + (92 :: x :: hexN c cnt).length) (c :: acc) inv := by
    intro x cnt hx hl hat
    obtain ⟨h1, h2, h3⟩ := at_pair hat
    have hsplit : (92 :: x :: hexN c cnt) = [92, x] ++ hexN c cnt := rfl
    rw [hsplit] at hat
    have hr := hat.right
    have hd := hexDigits_hexN buf cnt c (p + 2) 0 hl hr
    have e : 0 * 16 ^ cnt + c = c := by simp
    rw [e] at hd
    rw [dec_hex ucn buf f p acc inv x cnt c h1 h2 h3 hx hd hc]
    congr 1
    simp [hexN_length]
    omega
  unfold hexEscape at ha ⊢
  split at ha
  · rename_i h
    rw [if_pos h]
    exact key 120 2 (Or.inl ⟨rfl, rfl⟩) (by omega) ha
  · rename_i h
    rw [if_neg h]
    split at ha
    · rename_i h'
      rw [if_pos h']
      exact key 117 4 (Or.inr (Or.inl ⟨rfl, rfl⟩)) (by omega) ha
    · rename_i h'
      rw [if_neg h']
      exact key 85 8 (Or.inr (Or.inr ⟨rfl, rfl⟩)) (by omega) ha

/-- A character `repr` writes in ASCII, and a valid code point. -/
def Plain (c : Nat) : Prop := c ≤ 0x10FFFF ∧ (c < 0x7f ∨ printable c = false)

theorem dec_seg (ucn : List (List Nat × Nat)) (buf : Array Nat) (f p : Nat) (acc : List Nat)
    (inv : Option Nat) (q c : Nat) (hq : q = 39 ∨ q = 34) (hc : Plain c)
    (ha : At buf p (reprEsc q c)) :
    decodeUnicodeEscape ucn buf (f + 1) p acc inv =
      decodeUnicodeEscape ucn buf f (p + (reprEsc q c).length) (c :: acc) inv := by
  unfold reprEsc at ha ⊢
  split at ha
  · rename_i h1
    rw [if_pos h1]
    obtain ⟨a, b, d⟩ := at_pair ha
    refine dec_simple ucn buf f p acc inv c c a b d ?_
    simp only [Bool.or_eq_true, beq_iff_eq] at h1
    rcases h1 with h1 | h1
    · subst h1
      rcases hq with rfl | rfl
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · subst h1
      exact Or.inl ⟨rfl, rfl⟩
  · rename_i h1
    rw [if_neg h1]
    split at ha
    · rename_i h2
      rw [if_pos h2]
      obtain ⟨a, b, d⟩ := at_pair ha
      have e : c = 9 := by simpa using h2
      subst e
      exact dec_simple ucn buf f p acc inv 116 9 a b d (by omega)
    · rename_i h2
      rw [if_neg h2]
      split at ha
      · rename_i h3
        rw [if_pos h3]
        obtain ⟨a, b, d⟩ := at_pair ha
        have e : c = 10 := by simpa using h3
        subst e
        exact dec_simple ucn buf f p acc inv 110 10 a b d (by omega)
      · rename_i h3
        rw [if_neg h3]
        split at ha
        · rename_i h4
          rw [if_pos h4]
          obtain ⟨a, b, d⟩ := at_pair ha
          have e : c = 13 := by simpa using h4
          subst e
          exact dec_simple ucn buf f p acc inv 114 13 a b d (by omega)
        · rename_i h4
          rw [if_neg h4]
          split at ha
          · rename_i h5
            rw [if_pos h5]
            exact dec_hexEscape ucn buf f p acc inv c hc.1 ha
          · rename_i h5
            rw [if_neg h5]
            have hne : c ≠ 92 := by
              intro e
              apply h1
              simp [e]
            split at ha
            · rename_i h6
              rw [if_pos h6]
              have h0 := ha 0 (by simp)
              exact dec_plain ucn buf f p acc inv c (by simpa using h0.1) (by simpa using h0.2) hne
            · rename_i h6
              rw [if_neg h6]
              split at ha
              · rename_i h7
                rcases hc.2 with h8 | h8
                · exact (h6 (by simpa using h8)).elim
                · rw [h8] at h7
                  cases h7
              · rename_i h7
                rw [if_neg h7]
                exact dec_hexEscape ucn buf f p acc inv c hc.1 ha

theorem dec_flat (ucn : List (List Nat × Nat)) (buf : Array Nat) (inv : Option Nat) (q : Nat)
    (hq : q = 39 ∨ q = 34) : ∀ (s : List Nat) (f p : Nat) (acc : List Nat), (∀ c, c ∈ s → Plain c) →
    At buf p (s.flatMap (reprEsc q)) → p + (s.flatMap (reprEsc q)).length = buf.size →
    s.length < f → decodeUnicodeEscape ucn buf f p acc inv = .ok (acc.reverse ++ s, inv)
  | [], f, p, acc, _, _, he, hf => by
    cases f with
    | zero => cases hf
    | succ f =>
      have : p ≥ buf.size := by simpa using Nat.le_of_eq he.symm
      rw [decodeUnicodeEscape]
      simp [this]
  | c :: s, f, p, acc, hp, ha, he, hf => by
    cases f with
    | zero => cases hf
    | succ f =>
      have ha' : At buf p (reprEsc q c ++ s.flatMap (reprEsc q)) := by simpa using ha
      rw [dec_seg ucn buf f p acc inv q c hq (hp c (List.mem_cons_self ..)) ha'.left]
      have he' : p + (reprEsc q c).length + (s.flatMap (reprEsc q)).length = buf.size := by
        rw [← he]
        simp
        omega
      rw [dec_flat ucn buf inv q hq s f _ (c :: acc)
        (fun x hx => hp x (List.mem_cons_of_mem _ hx)) ha'.right he' (by simpa using hf)]
      simp

/-- Text in which every backslash starts a pair and every byte is ASCII. -/
inductive BS : List Nat → Prop
  | nil : BS []
  | one {c : Nat} {l : List Nat} : c ≠ 92 → c < 0x80 → BS l → BS (c :: l)
  | two {x : Nat} {l : List Nat} : x < 0x80 → BS l → BS (92 :: x :: l)

theorem BS.append {a b : List Nat} (ha : BS a) (hb : BS b) : BS (a ++ b) := by
  induction ha with
  | nil => exact hb
  | one h1 h2 _ ih => exact BS.one h1 h2 ih
  | two h1 _ ih => exact BS.two h1 ih

theorem BS.ascii {l : List Nat} (h : BS l) : ∀ c, c ∈ l → c < 0x80 := by
  induction h with
  | nil => intro c hc; cases hc
  | one h1 h2 _ ih =>
    intro c hc
    rcases List.mem_cons.mp hc with e | e
    · rw [e]; exact h2
    · exact ih c e
  | two h1 _ ih =>
    intro c hc
    rcases List.mem_cons.mp hc with e | e
    · rw [e]; decide
    · rcases List.mem_cons.mp e with e | e
      · rw [e]; exact h1
      · exact ih c e

theorem hexDigit_ok : ∀ d, d < 16 → hexDigit d ≠ 92 ∧ hexDigit d < 0x80 := by decide

theorem BS_hexN (n w : Nat) : BS (hexN n w) := by
  induction w generalizing n with
  | zero => exact BS.nil
  | succ w ih =>
    have hd : n &&& 15 < 16 := by
      rw [show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (by decide)
    obtain ⟨a, b⟩ := hexDigit_ok _ hd
    exact (ih _).append (BS.one a b BS.nil)

theorem BS_hexEscape (c : Nat) : BS (hexEscape c) := by
  unfold hexEscape
  split
  · exact BS.two (by decide) (BS_hexN _ _)
  · split
    · exact BS.two (by decide) (BS_hexN _ _)
    · exact BS.two (by decide) (BS_hexN _ _)

theorem BS_reprEsc (q c : Nat) (hq : q = 39 ∨ q = 34) (hc : Plain c) : BS (reprEsc q c) := by
  unfold reprEsc
  split
  · rename_i h1
    simp only [Bool.or_eq_true, beq_iff_eq] at h1
    refine BS.two ?_ BS.nil
    rcases h1 with rfl | rfl
    · rcases hq with rfl | rfl <;> decide
    · decide
  · split
    · exact BS.two (by decide) BS.nil
    · split
      · exact BS.two (by decide) BS.nil
      · split
        · exact BS.two (by decide) BS.nil
        · split
          · exact BS_hexEscape c
          · rename_i h1 _ _ _ _
            have hne : c ≠ 92 := fun e => h1 (by simp [e])
            split
            · rename_i h6
              exact BS.one hne (by omega) BS.nil
            · split
              · rename_i h6 h7
                rcases hc.2 with h8 | h8
                · exact (h6 h8).elim
                · rw [h8] at h7
                  cases h7
              · exact BS_hexEscape c

theorem BS_flat (q : Nat) (hq : q = 39 ∨ q = 34) (s : List Nat) (hs : ∀ c, c ∈ s → Plain c) :
    BS (s.flatMap (reprEsc q)) := by
  induction s with
  | nil => exact BS.nil
  | cons c s ih =>
    simp only [List.flatMap_cons]
    exact (BS_reprEsc q c hq (hs c (List.mem_cons_self ..))).append
      (ih fun x hx => hs x (List.mem_cons_of_mem _ hx))

/-- `decode_unicode_with_escapes` leaves such text as it is. -/
theorem escape_id {l : List Nat} (h : BS l) : ∀ f, l.length < f → escapeNonAscii f l = l := by
  induction h with
  | nil =>
    intro f hf
    cases f with
    | zero => cases hf
    | succ f => simp [escapeNonAscii]
  | @one c l h1 h2 _ ih =>
    intro f hf
    cases f with
    | zero => cases hf
    | succ f =>
      have hn : ¬ c ≥ 0x80 := by omega
      rw [escapeNonAscii.eq_def]
      simp [h1, hn, ih f (by simpa using hf)]
  | @two x l h1 _ ih =>
    intro f hf
    cases f with
    | zero => cases hf
    | succ f =>
      have hn : ¬ x ≥ 0x80 := by omega
      rw [escapeNonAscii.eq_def]
      simp [hn, ih f (by simp at hf; omega)]

theorem utf8Encode_ascii {l : List Nat} (h : ∀ c, c ∈ l → c < 0x80) : utf8Encode l = l := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    have hc := h c (List.mem_cons_self ..)
    have e : utf8Enc c = [c] := by
      unfold utf8Enc
      rw [if_pos hc]
    simp only [utf8Encode, List.flatMap_cons, e]
    show c :: utf8Encode l = _
    rw [ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem decodeReplace_ascii {l : List Nat} (h : ∀ c, c ∈ l → c < 0x80) :
    ∀ f, l.length < f → decodeReplace f l = l := by
  induction l with
  | nil =>
    intro f hf
    cases f with
    | zero => cases hf
    | succ f => simp [decodeReplace]
  | cons c l ih =>
    intro f hf
    cases f with
    | zero => cases hf
    | succ f =>
      have hc := h c (List.mem_cons_self ..)
      rw [decodeReplace]
      simp [hc, ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) f (by simpa using hf)]

theorem reprEsc_head (q c : Nat) (hq : q = 39 ∨ q = 34) (hc : Plain c) :
    (reprEsc q c).head? ≠ some q := by
  have h92 : (92 : Nat) ≠ q := by rcases hq with rfl | rfl <;> decide
  have hx : (hexEscape c).head? = some 92 := by
    unfold hexEscape
    split
    · rfl
    · split <;> rfl
  unfold reprEsc
  split
  · simpa using h92
  · rename_i h1
    have hne : c ≠ q := fun e => h1 (by simp [e])
    split
    · simpa using h92
    · split
      · simpa using h92
      · split
        · simpa using h92
        · split
          · rw [hx]
            simpa using h92
          · split
            · simpa using hne
            · split
              · simpa using hne
              · rw [hx]
                simpa using h92

theorem hexEscape_mem (c : Nat) : 92 ∈ hexEscape c := by
  unfold hexEscape
  split
  · simp
  · split <;> simp

theorem reprEsc_cases (q c : Nat) : reprEsc q c = [c] ∨ 92 ∈ reprEsc q c := by
  unfold reprEsc
  repeat' split
  all_goals simp [hexEscape_mem]

theorem reprEsc_ne (q c : Nat) : reprEsc q c ≠ [] := by
  rcases reprEsc_cases q c with h | h
  · rw [h]
    simp
  · intro e
    rw [e] at h
    cases h

theorem flat_head (q : Nat) (hq : q = 39 ∨ q = 34) (s : List Nat) (hs : ∀ c, c ∈ s → Plain c) :
    (s.flatMap (reprEsc q)).head? ≠ some q := by
  cases s with
  | nil => simp
  | cons c s =>
    have h := reprEsc_head q c hq (hs c (List.mem_cons_self ..))
    simp only [List.flatMap_cons]
    cases hh : reprEsc q c with
    | nil => exact (reprEsc_ne q c hh).elim
    | cons x xs =>
      rw [hh] at h
      simpa using h

/-- A backslash-free `repr` is the string itself. -/
theorem flat_no_bs (q : Nat) (s : List Nat) (h : 92 ∉ s.flatMap (reprEsc q)) :
    s.flatMap (reprEsc q) = s := by
  induction s with
  | nil => rfl
  | cons c s ih =>
    simp only [List.flatMap_cons, List.mem_append, not_or] at h
    rcases reprEsc_cases q c with e | e
    · simp only [List.flatMap_cons, e, List.singleton_append]
      rw [ih h.2]
    · exact (h.1 e).elim

theorem flat_length (q : Nat) (s : List Nat) : s.length ≤ (s.flatMap (reprEsc q)).length := by
  induction s with
  | nil => simp
  | cons c s ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have : 0 < (reprEsc q c).length := List.length_pos_iff.mpr (reprEsc_ne q c)
    omega

theorem stringParts_repr (q : Nat) (flat : List Nat) (hq : q = 39 ∨ q = 34)
    (hh : flat.head? ≠ some q) :
    stringParts (q :: flat ++ [q]) = (flat, flat ++ [q], false, !(flat ++ [q]).contains 92) := by
  have hhead : ¬ (flat.length ≥ 4 ∧ (flat ++ [q]).getD 0 0 = q) := by
    rintro ⟨h4, h0⟩
    cases flat with
    | nil => simp at h4
    | cons x xs =>
      apply hh
      have : x = q := by simpa using h0
      simp [this]
  have hp : stringPfx 4 (q :: (flat ++ [q])) false false = (q :: (flat ++ [q]), false, false) := by
    rcases hq with rfl | rfl <;> simp [stringPfx]
  simp only [stringParts, List.cons_append, hp, List.headD_cons, List.drop_succ_cons, List.drop_zero]
  have hlen : (flat ++ [q]).length - 1 = flat.length := by simp
  simp only [hlen]
  have hc : (decide (flat.length ≥ 4) && (flat ++ [q]).getD 0 0 == q && (flat ++ [q]).getD 1 0 == q)
      = false := by
    by_cases h4 : flat.length ≥ 4
    · have h0 : ((flat ++ [q]).getD 0 0 == q) = false := by
        simpa using fun e => hhead ⟨h4, e⟩
      rw [h0, Bool.and_false, Bool.false_and]
    · simp [h4]
  simp only [hc, Bool.false_eq_true, if_false, Bool.false_or]
  simp

theorem at_toArray (l : List Nat) : At l.toArray 0 l := by
  intro i hi
  simp only [Nat.zero_add]
  refine ⟨by simpa using hi, ?_⟩
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem decode_flat (q : Nat) (hq : q = 39 ∨ q = 34) (s : List Nat) (hs : ∀ c, c ∈ s → Plain c)
    (t : Token) (p : PS) :
    decodeString (!((s.flatMap (reprEsc q)) ++ [q]).contains 92) (s.flatMap (reprEsc q)) (some t) p =
      (some s, p) := by
  have hb := BS_flat q hq s hs
  have hq92 : (q == 92) = false := by rcases hq with rfl | rfl <;> rfl
  cases hc : ((s.flatMap (reprEsc q)) ++ [q]).contains 92 with
  | false =>
    have hn : 92 ∉ s.flatMap (reprEsc q) := by
      intro h
      have : ((s.flatMap (reprEsc q)) ++ [q]).contains 92 = true := by simp [h]
      rw [hc] at this
      cases this
    have e := flat_no_bs q s hn
    show (some (utf8Decode (s.flatMap (reprEsc q))), p) = _
    rw [e]
    congr 2
    rw [e] at hb
    exact decodeReplace_ascii hb.ascii _ (Nat.lt_succ_self _)
  | true =>
    show decodeUnicodeWithEscapes (s.flatMap (reprEsc q)) (some t) p = _
    have he := escape_id hb _ (Nat.lt_succ_self _)
    have hd := dec_flat p.cfg.ucn (s.flatMap (reprEsc q)).toArray none q hq s
      ((s.flatMap (reprEsc q)).toArray.size + 1) 0 [] hs (at_toArray _) (by simp)
      (by
        show s.length < (s.flatMap (reprEsc q)).toArray.size + 1
        rw [List.size_toArray]
        exact Nat.lt_succ_of_le (flat_length q s))
    simp only [decodeUnicodeWithEscapes, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, he]
    rw [hd]
    simp
    rfl

/-- `_PyPegen_parse_string` inverts what `Unparser._write_constant` writes for a `str`: for every
string whose `repr` is pure ASCII, a `STRING` token holding that text decodes back to the string,
with no warning. It runs `decode_unicode_with_escapes` and the `unicode_escape` decoder on the
escapes `repr` uses. Hypothesis: `Plain`, valid code points, no printable non-ASCII. Only the `str`
branch of `_write_constant`. -/
def StrReprRoundTrip : Prop := ∀ (s b : List Nat) (t : Token) (p : PS),
  (∀ c, c ∈ s → Plain c) → constRepr (.str s) = .ok b → t.bytes = utf8Encode b →
  (parseString t p).1 = .str s ∧ (parseString t p).2 = p

theorem strReprRoundTrip_proven : StrReprRoundTrip := by
  intro s b t p hs hb' ht
  have hrep : b = strRepr s := by
    have : Except.ok (ε := PyExc) (strRepr s) = .ok b := hb'
    cases this
    rfl
  subst hrep
  have hq : reprQuote s = 39 ∨ reprQuote s = 34 := by
    unfold reprQuote
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  generalize hqq : reprQuote s = q at hq
  have hb := BS_flat q hq s hs
  have hqa : q < 0x80 := by rcases hq with rfl | rfl <;> decide
  have hasc : ∀ c, c ∈ strRepr s → c < 0x80 := by
    intro c hc
    unfold strRepr at hc
    rw [hqq] at hc
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h
    · omega
    · exact hb.ascii c h
    · omega
  have hbytes : t.bytes = q :: s.flatMap (reprEsc q) ++ [q] := by
    rw [ht, utf8Encode_ascii hasc]
    unfold strRepr
    rw [hqq]
  have hparts := stringParts_repr q (s.flatMap (reprEsc q)) hq (flat_head q hq s hs)
  have hd := decode_flat q hq s hs t p
  have e : parseString t p = (.str s, p) := by
    unfold parseString
    rw [hbytes, hparts]
    simp only [Bool.false_eq_true, ↓reduceIte, bind, StateT.bind, pure, StateT.pure, hd]
  rw [e]
  exact ⟨rfl, rfl⟩

end PyLean.PyGrammar.Unparse
