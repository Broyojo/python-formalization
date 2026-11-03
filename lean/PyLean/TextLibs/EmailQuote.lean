import PyLean.TextLibs.EmailUnstruct

/-!
Quoting round trips of `Lib/email/_header_value_parser.py` (CPython 3.15.2): the text
`quote_string` writes parses back with `get_bare_quoted_string`, and the text
`make_parenthesis_pairs` writes inside parentheses parses back with `get_comment`; and the
`had_qp` flag of `_get_ptext_to_endchars` against its docstring.
-/

namespace PyLean.TextLibs.Email

open PyLean.UnicodeObj

/-! ## Statements -/

/-- `Comment.content`, :303-305: the text between the parentheses, nested comments included. -/
def commentContent (c : Tok) : Str := strs c.kids

/-- For every text `s` and every rest `r`:
* `get_bare_quoted_string(quote_string(s) + r)` returns the rest `r` and a bare quoted string
  whose `value` is `s` and whose `str()` is `quote_string(s)`, when no encoded word decodes
  (`_ew.decode` rejects every argument; the parser decodes encoded words inside quoted strings,
  see `QuotedStringCanonical` for what happens when one does);
* `get_comment('(' + make_parenthesis_pairs(s) + ')' + r)` returns the rest `r` and a comment
  whose `content` is `s` and whose `str()` is `'(' + make_parenthesis_pairs(s) + ')'`.
`make_quoted_pairs` and `make_parenthesis_pairs` "escape dquote and backslash for use within a
quoted-string" and "parenthesis and backslash for use within a comment" (:100-108); the parsers
"unquote any quoted printables" (:1037-1043), keep whitespace in a quoted string's value
(:1244-1250) and a comment's content (:51-52). The fuel only has to exceed the length of `s`. -/
def QuotingRoundTrip : Prop :=
  (∀ (cfg : Cfg) (n : Nat) (s r : Str), (∀ x, cfg.dec x = .caught) → s.length + 1 < n →
    ∃ b, getBareQuotedString cfg n (quoteString s ++ r) = .ok (b, r) ∧
      b.str = quoteString s ∧ b.value = .ok s) ∧
  (∀ (n : Nat) (s r : Str), s.length + 1 < n →
    ∃ c, getComment n ([40] ++ makeParenPairs s ++ [41] ++ r) = .ok (c, r) ∧
      c.str = [40] ++ makeParenPairs s ++ [41] ∧ commentContent c = s)

/-- The third result of `_get_ptext_to_endchars` is "a flag that is True iff there were any
quoted printables decoded" (:1040-1043): whenever the text it returns is shorter than the text
it consumed (a backslash was dropped, the first half of a quoted pair), the flag is set. -/
def PtextQpFlag : Prop :=
  ∀ (v : Str) (endc : Nat → Bool) (p rest : Str) (qp : Bool),
    getPtextToEndchars v endc = .ok (p, rest, qp) → p.length + rest.length < v.length → qp = true

/-! ## Escaping -/

/-- Backslash-escape `\` and the characters `E` holds. -/
def escWith (E : Nat → Bool) (s : Str) : Str :=
  s.flatMap (fun c => if c == 92 || E c then [92, c] else [c])

def E34 (c : Nat) : Bool := c == 34
def Eparen (c : Nat) : Bool := c == 40 || c == 41

theorem makeQuotedPairs_eq (s : Str) : makeQuotedPairs s = escWith E34 s := by
  unfold makeQuotedPairs escWith
  congr 1
  funext c
  by_cases h1 : c = 92
  · subst h1; rfl
  · by_cases h2 : c = 34
    · subst h2; rfl
    · simp [E34, h1, h2]

theorem makeParenPairs_eq (s : Str) : makeParenPairs s = escWith Eparen s := by
  unfold makeParenPairs escWith
  congr 1
  funext c
  by_cases h1 : c = 92
  · subst h1; rfl
  · by_cases h2 : c = 40
    · subst h2; rfl
    · by_cases h3 : c = 41
      · subst h3; rfl
      · simp [Eparen, h1, h2, h3]

theorem escWith_nil (E : Nat → Bool) : escWith E [] = [] := rfl

theorem escWith_cons (E : Nat → Bool) (c : Nat) (s : Str) :
    escWith E (c :: s) = (if c == 92 || E c then [92, c] else [c]) ++ escWith E s := by
  simp [escWith]

theorem escWith_append (E : Nat → Bool) (a b : Str) : escWith E (a ++ b) = escWith E a ++ escWith E b := by
  simp [escWith]

/-- The escaping alphabets: no space character is escaped, and `\` is not an end character. -/
structure EscOk (E endc : Nat → Bool) : Prop where
  endc_E : ∀ c, endc c = true → E c = true
  endc_92 : endc 92 = false
  space : ∀ c, isSpace c = true → E c = false ∧ c ≠ 92

theorem escOk34 : EscOk E34 (fun c => c == 34) where
  endc_E := fun c h => h
  endc_92 := rfl
  space := by
    intro c h
    constructor
    · simp only [E34, beq_eq_false_iff_ne]; rintro rfl; revert h; decide
    · rintro rfl; revert h; decide

theorem escOkParen : EscOk Eparen (fun c => c == 40 || c == 41) where
  endc_E := fun c h => h
  endc_92 := rfl
  space := by
    intro c h
    constructor
    · simp only [Eparen, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
      constructor <;> (rintro rfl; revert h; decide)
    · rintro rfl; revert h; decide

/-- The loop of `_get_ptext_to_endchars` reads escaped text back. -/
theorem ptextLoop_esc {E endc : Nat → Bool} (hok : EscOk E endc) (x : Str) :
    ∀ (t : Str) (qp : Bool) (acc : Str), ∃ qp',
      ptextLoop endc (escWith E t ++ x) false qp acc = ptextLoop endc x false qp' (acc ++ t)
  | [], qp, acc => ⟨qp, by simp [escWith_nil]⟩
  | c :: t, qp, acc => by
    rw [escWith_cons]
    by_cases hc : (c == 92 || E c) = true
    · rw [if_pos hc]
      simp only [List.cons_append, List.nil_append, List.append_assoc]
      by_cases h92 : c = 92
      · subst h92
        obtain ⟨qp', h⟩ := ptextLoop_esc hok x t true (acc ++ [92])
        refine ⟨qp', ?_⟩
        simp only [ptextLoop, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, hok.endc_92]
        rw [h]; simp
      · have h92' : (c == 92) = false := by simpa using h92
        obtain ⟨qp', h⟩ := ptextLoop_esc hok x t qp (acc ++ [c])
        refine ⟨qp', ?_⟩
        simp only [ptextLoop, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, h92']
        rw [h]; simp
    · rw [if_neg hc]
      simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hc
      have hend : endc c = false := by
        cases h : endc c
        · rfl
        · exact absurd (hok.endc_E c h) (by simpa using hc.2)
      obtain ⟨qp', h⟩ := ptextLoop_esc hok x t qp (acc ++ [c])
      refine ⟨qp', ?_⟩
      simp only [List.cons_append, List.nil_append]
      have h92' : (c == 92) = false := by simpa using hc.1
      simp only [ptextLoop, h92', ↓reduceIte, Bool.false_eq_true, hend]
      rw [h]; simp

/-! ## Splitting escaped text -/

theorem takeWhile_append_all {p : Nat → Bool} :
    ∀ {A : Str} (B : Str), (∀ a ∈ A, p a = true) → (A ++ B).takeWhile p = A ++ B.takeWhile p
  | [], _, _ => rfl
  | a :: A, B, h => by
    simp only [List.cons_append, List.takeWhile_cons, h a (by simp), ↓reduceIte]
    rw [takeWhile_append_all B (fun x hx => h x (by simp [hx]))]

theorem dropWhile_append_all {p : Nat → Bool} :
    ∀ {A : Str} (B : Str), (∀ a ∈ A, p a = true) → (A ++ B).dropWhile p = B.dropWhile p
  | [], _, _ => rfl
  | a :: A, B, h => by
    simp only [List.cons_append, List.dropWhile_cons, h a (by simp), ↓reduceIte]
    exact dropWhile_append_all B (fun x hx => h x (by simp [hx]))

theorem escWith_noWsp {E : Nat → Bool} :
    ∀ {t : Str}, (∀ a ∈ t, isWsp a = false) → ∀ a ∈ escWith E t, (!isWsp a) = true
  | [], _, a, ha => by simp [escWith_nil] at ha
  | c :: t, h, a, ha => by
    rw [escWith_cons, List.mem_append] at ha
    rcases ha with ha | ha
    · split at ha
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with h1 | h1
        · rw [h1]; decide
        · rw [h1]; simp [h c (by simp)]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rw [ha]; simp [h c (by simp)]
    · exact escWith_noWsp (fun x hx => h x (by simp [hx])) a ha

theorem escWith_spaces {E endc : Nat → Bool} (hok : EscOk E endc) :
    ∀ {t : Str}, (∀ a ∈ t, isSpace a = true) → escWith E t = t
  | [], _ => rfl
  | c :: t, h => by
    have hs := hok.space c (h c (by simp))
    rw [escWith_cons, if_neg (by simp [hs.1, hs.2]), escWith_spaces hok (fun x hx => h x (by simp [hx]))]
    rfl

theorem mem_dropWhile_head {p : Nat → Bool} {l : Str} {d : Nat} {l' : Str}
    (h : l.dropWhile p = d :: l') : p d = false := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    rw [List.dropWhile_cons] at h
    split at h
    · exact ih h
    · rename_i hx; simp at h; obtain ⟨rfl, _⟩ := h; simpa using hx

theorem all_takeWhile {p : Nat → Bool} (l : Str) : ∀ a ∈ l.takeWhile p, p a = true :=
  fun _ ha => mem_takeWhile_p ha

/-- A value that starts with whitespace, escaped: `get_fws` takes exactly the whitespace. -/
theorem getFws_esc {E endc : Nat → Bool} (hok : EscOk E endc) (s : Str) {e : Nat} (r : Str)
    (he : isSpace e = false) :
    (getFws (escWith E s ++ e :: r)).1 = WT (s.takeWhile isSpace) "fws" ∧
    (getFws (escWith E s ++ e :: r)).2 = escWith E (s.dropWhile isSpace) ++ e :: r := by
  have hsplit := List.takeWhile_append_dropWhile (p := isSpace) (l := s)
  have hts := escWith_spaces hok (all_takeWhile (p := isSpace) s)
  have hv : escWith E s ++ e :: r =
      s.takeWhile isSpace ++ (escWith E (s.dropWhile isSpace) ++ e :: r) := by
    have h1 : escWith E s = escWith E (s.takeWhile isSpace ++ s.dropWhile isSpace) := by
      rw [hsplit]
    rw [h1, escWith_append, hts, List.append_assoc]
  -- the text after the run of spaces starts with a non-space
  have hhead : (escWith E (s.dropWhile isSpace) ++ e :: r).takeWhile isSpace = [] ∧
      (escWith E (s.dropWhile isSpace) ++ e :: r).dropWhile isSpace =
        escWith E (s.dropWhile isSpace) ++ e :: r := by
    cases hd : s.dropWhile isSpace with
    | nil => simp [escWith_nil, he]
    | cons d l' =>
      have hd' := mem_dropWhile_head hd
      rw [escWith_cons]
      split
      · have h92s : isSpace 92 = false := by decide
        simp [List.takeWhile_cons, List.dropWhile_cons, h92s]
      · simp [List.takeWhile_cons, List.dropWhile_cons, hd']
  rw [getFws_fst, getFws_snd, hv, takeWhile_append_all _ (all_takeWhile s),
    dropWhile_append_all _ (all_takeWhile s), hhead.1, hhead.2]
  simp

/-- One `qcontent`/`ctext` run of escaped text: `_get_ptext_to_endchars` returns the text up to
the next space or tab, unescaped, and leaves the rest escaped. -/
theorem ptext_esc {E endc : Nat → Bool} (hok : EscOk E endc) {c : Nat} {s : Str}
    (hc : isWsp c = false) {e : Nat} (r : Str) (he : endc e = true) (hew : isWsp e = false) :
    ∃ qp, getPtextToEndchars (escWith E (c :: s) ++ e :: r) endc =
      .ok ((c :: s).takeWhile (fun x => !isWsp x),
        escWith E ((c :: s).dropWhile (fun x => !isWsp x)) ++ e :: r, qp) := by
  obtain ⟨t, ht⟩ : ∃ t, t = (c :: s).takeWhile (fun x => !isWsp x) := ⟨_, rfl⟩
  obtain ⟨u, hu0⟩ : ∃ u, u = (c :: s).dropWhile (fun x => !isWsp x) := ⟨_, rfl⟩
  rw [← ht, ← hu0]
  have hsplit : t ++ u = c :: s := by rw [ht, hu0]; exact List.takeWhile_append_dropWhile
  have htnw : ∀ a ∈ t, isWsp a = false := fun a ha => by
    rw [ht] at ha; simpa using mem_takeWhile_p ha
  have hesc := escWith_noWsp (E := E) htnw
  have hv : escWith E (c :: s) ++ e :: r = escWith E t ++ (escWith E u ++ e :: r) := by
    rw [← hsplit, escWith_append, List.append_assoc]
  have htne : t ≠ [] := by
    rw [ht]; simp only [List.takeWhile_cons, hc, Bool.not_false, ↓reduceIte]; simp
  have hene : escWith E t ≠ [] := by
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil htne
    rw [hx, escWith_cons]; split <;> simp
  have he92 : (e == 92) = false := by
    cases h : (e == 92)
    · rfl
    · simp at h; subst h; rw [hok.endc_92] at he; cases he
  unfold getPtextToEndchars
  have hvne : (escWith E (c :: s) ++ e :: r).isEmpty = false := by simp
  rw [if_neg (by simp [hvne])]
  cases u with
  | nil =>
    simp only [escWith_nil, List.nil_append] at hv
    have hw : wspSplit (escWith E (c :: s) ++ e :: r) =
        (escWith E t ++ e :: r.takeWhile (fun x => !isWsp x), r.dropWhile (fun x => !isWsp x)) := by
      simp only [wspSplit, hv, takeWhile_append_all _ hesc, dropWhile_append_all _ hesc,
        List.takeWhile_cons, List.dropWhile_cons, hew, Bool.not_false, ↓reduceIte]
    simp only [hw]
    rw [if_neg (by simp [hene])]
    obtain ⟨qp', hl⟩ := ptextLoop_esc hok (e :: r.takeWhile (fun x => !isWsp x)) t false []
    refine ⟨qp', ?_⟩
    rw [hl]
    have hr := List.takeWhile_append_dropWhile (p := fun x => !isWsp x) (l := r)
    simp [ptextLoop, he, he92, hr, escWith_nil, pure, Except.pure]
  | cons w u' =>
    have hw' : isWsp w = true := by
      have := mem_dropWhile_head (p := fun x => !isWsp x) (l := c :: s) (d := w) (l' := u')
        hu0.symm
      simpa using this
    have hws := hok.space w (isSpace_of_wsp hw')
    have hesc_u : escWith E (w :: u') = w :: escWith E u' := by
      rw [escWith_cons, if_neg (by simp [hws.1, hws.2])]; rfl
    have hw : wspSplit (escWith E (c :: s) ++ e :: r) =
        (escWith E t, w :: (escWith E u' ++ e :: r)) := by
      simp only [wspSplit, hv, hesc_u, takeWhile_append_all _ hesc, dropWhile_append_all _ hesc,
        List.cons_append, List.takeWhile_cons, List.dropWhile_cons, hw', Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, List.append_nil]
    simp only [hw]
    rw [if_neg (by simp [hene])]
    obtain ⟨qp', hl⟩ := ptextLoop_esc hok [] t false []
    refine ⟨qp', ?_⟩
    rw [List.append_nil] at hl
    rw [hl]
    simp [ptextLoop, hesc_u, pure, Except.pure]

/-! ## The loops of `get_bare_quoted_string` and `get_comment` -/

/-- Escaped text that does not start with whitespace starts with a character that is neither
whitespace nor an end character. -/
theorem escWith_head {E endc : Nat → Bool} (hok : EscOk E endc) {c : Nat} {s : Str}
    (hc : isWsp c = false) (y : Str) :
    ∃ h tl, escWith E (c :: s) ++ y = h :: tl ∧ isWsp h = false ∧ endc h = false ∧
      (h = 92 ∨ (h = c ∧ E c = false)) := by
  rw [escWith_cons]
  split
  · refine ⟨92, c :: (escWith E s ++ y), by simp, by decide, hok.endc_92, .inl rfl⟩
  · rename_i hce
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hce
    have hE : E c = false := by simpa using hce.2
    refine ⟨c, escWith E s ++ y, by simp, hc, ?_, .inr ⟨rfl, hE⟩⟩
    cases h : endc c
    · rfl
    · rw [hok.endc_E c h] at hE; cases hE

theorem dropWhile_notWsp_lt {c : Nat} {s : Str} (hc : isWsp c = false) :
    ((c :: s).dropWhile (fun x => !isWsp x)).length ≤ s.length := by
  simp only [List.dropWhile_cons, hc, Bool.not_false, ↓reduceIte]
  exact dropWhile_length_le _ _

theorem split_noWsp (c : Nat) (s : Str) :
    (c :: s).takeWhile (fun x => !isWsp x) ++ (c :: s).dropWhile (fun x => !isWsp x) = c :: s :=
  List.takeWhile_append_dropWhile

theorem validateXtext_str (c : TC) (s : Str) (ty : String) (hc : c ≠ .ewws) :
    (validateXtext (.term c s ty [])).str = s ∧ (validateXtext (.term c s ty [])).ty = ty := by
  obtain ⟨ds', h⟩ := validateXtext_term c s ty []
  rw [h]
  cases c with
  | ws => exact ⟨rfl, rfl⟩
  | val => exact ⟨rfl, rfl⟩
  | ewws => exact absurd rfl hc

theorem validateXtext_VT (s : Str) (ty : String) :
    (validateXtext (VT s ty)).str = s ∧ (validateXtext (VT s ty)).ty = ty :=
  validateXtext_str .val s ty (by decide)

theorem validateXtext_WT (s : Str) (ty : String) :
    (validateXtext (WT s ty)).str = s ∧ (validateXtext (WT s ty)).ty = ty :=
  validateXtext_str .ws s ty (by decide)

theorem decSafe_of_caught {cfg : Cfg} (hc : ∀ x, cfg.dec x = .caught) : DecSafe cfg := by
  intro s c m h; rw [hc] at h; cases h

theorem bqsEw_caught {cfg : Cfg} (hc : ∀ x, cfg.dec x = .caught) (value : Str) (b : Tok) :
    bqsEw cfg value b = match getQcontent value with
      | .ok (tok, v') => .ok (tok, v', b, false)
      | .error e' => .error e' := by
  unfold bqsEw
  cases h : getEncodedWord cfg value "vtext" with
  | ok r => exact absurd h (getEncodedWord_caught hc value "vtext" r)
  | error e =>
    simp only
    rcases getEncodedWord_err (decSafe_of_caught hc) h with ⟨m, rfl⟩ | ⟨m, rfl⟩ <;>
      simp only [EExc.isHpe, ↓reduceIte] <;> rfl

theorem bqsLoop_esc {cfg : Cfg} (hc : ∀ x, cfg.dec x = .caught) (r : Str) :
    ∀ (n : Nat) (s : Str) (ty : String) (ks : List Tok) (ds : List Defect)
      (atts : List (String × AV)), s.length < n →
      ∃ ks', bqsLoop cfg n (escWith E34 s ++ 34 :: r) (.node .bareQuotedString ty ks ds atts) =
        .ok (.node .bareQuotedString ty (ks ++ ks') ds atts, 34 :: r) ∧ strs ks' = s
  | 0, _, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, [], ty, ks, ds, atts, _ => ⟨[], by simp [bqsLoop, escWith_nil]; rfl, rfl⟩
  | n + 1, c :: s, ty, ks, ds, atts, hlen => by
    simp only [List.length_cons] at hlen
    by_cases hw : isWsp c = true
    · have hs := isSpace_of_wsp hw
      have hsp := escOk34.space c hs
      have hv : escWith E34 (c :: s) ++ 34 :: r = c :: (escWith E34 s ++ 34 :: r) := by
        rw [escWith_cons, if_neg (by simp [hsp.1, hsp.2])]; rfl
      have hfws := getFws_esc escOk34 (c :: s) r (e := 34) (by decide)
      have hlt : ((c :: s).dropWhile isSpace).length < n := by
        rw [List.dropWhile_cons, if_pos hs]
        have := dropWhile_length_le isSpace s; omega
      obtain ⟨ks', h1, h2⟩ := bqsLoop_esc hc r n ((c :: s).dropWhile isSpace) ty
        (ks ++ [WT ((c :: s).takeWhile isSpace) "fws"]) ds atts hlt
      refine ⟨WT ((c :: s).takeWhile isSpace) "fws" :: ks', ?_, ?_⟩
      · rw [hv]
        unfold bqsLoop
        have hc34 : (c == 34) = false := by
          cases h : (c == 34)
          · rfl
          · simp at h; subst h; cases hw
        simp only [hc34, hw, Bool.false_eq_true, ↓reduceIte]
        rw [← hv, hfws.1, hfws.2]
        simp only [Tok.push]
        rw [h1]; simp
      · rw [strs, h2]
        simp only [Tok.str, WT]
        exact List.takeWhile_append_dropWhile
    · have hw' : isWsp c = false := by simpa using hw
      obtain ⟨h, tl, hv, hhw, hh34, _⟩ := escWith_head escOk34 (s := s) hw' (34 :: r)
      obtain ⟨qp, hq⟩ := ptext_esc escOk34 (s := s) hw' r (e := 34) rfl (by decide)
      obtain ⟨t, ht⟩ : ∃ t, t = (c :: s).takeWhile (fun x => !isWsp x) := ⟨_, rfl⟩
      obtain ⟨u, hu⟩ : ∃ u, u = (c :: s).dropWhile (fun x => !isWsp x) := ⟨_, rfl⟩
      rw [← ht, ← hu] at hq
      have hqc : getQcontent (escWith E34 (c :: s) ++ 34 :: r) =
          .ok (validateXtext (VT t "ptext"), escWith E34 u ++ 34 :: r) := by
        simp only [getQcontent, hq]; rfl
      have hlt : u.length < n := by
        have := dropWhile_notWsp_lt (s := s) hw'; rw [hu]; omega
      obtain ⟨ks', h1, h2⟩ := bqsLoop_esc hc r n u ty (ks ++ [validateXtext (VT t "ptext")]) ds
        atts hlt
      refine ⟨validateXtext (VT t "ptext") :: ks', ?_, ?_⟩
      · rw [hv]
        unfold bqsLoop
        simp only [hh34, hhw, Bool.false_eq_true, ↓reduceIte]
        rw [← hv]
        split
        · rw [bqsEw_caught hc, hqc]
          simp only [bqsCollapse, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Tok.push]
          rw [h1]; simp
        · rw [hqc]
          simp only [Tok.push]
          rw [h1]; simp
      · rw [strs, h2, (validateXtext_VT t "ptext").1, ht, hu]
        exact split_noWsp c s

theorem commentStrs_noComment : ∀ (ks : List Tok), (∀ k ∈ ks, k.ty ≠ "comment") →
    commentStrs ks = makeParenPairs (strs ks)
  | [], _ => rfl
  | k :: ks, h => by
    have hk := h k (by simp)
    rw [commentStrs, strs, if_neg (by simpa using hk),
      commentStrs_noComment ks (fun x hx => h x (by simp [hx]))]
    simp [makeParenPairs]

theorem commentLoop_esc (r : Str) :
    ∀ (n : Nat) (s : Str) (ty : String) (ks : List Tok) (ds : List Defect)
      (atts : List (String × AV)), s.length < n →
      ∃ ks', commentLoop n (escWith Eparen s ++ 41 :: r) (.node .comment ty ks ds atts) =
        .ok (.node .comment ty (ks ++ ks') ds atts, 41 :: r) ∧ strs ks' = s ∧
        (∀ k ∈ ks', k.ty ≠ "comment")
  | 0, _, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, [], ty, ks, ds, atts, _ =>
    ⟨[], by simp [commentLoop, escWith_nil]; rfl, rfl, by simp⟩
  | n + 1, c :: s, ty, ks, ds, atts, hlen => by
    simp only [List.length_cons] at hlen
    by_cases hw : isWsp c = true
    · have hs := isSpace_of_wsp hw
      have hsp := escOkParen.space c hs
      have hv : escWith Eparen (c :: s) ++ 41 :: r = c :: (escWith Eparen s ++ 41 :: r) := by
        rw [escWith_cons, if_neg (by simp [hsp.1, hsp.2])]; rfl
      have hfws := getFws_esc escOkParen (c :: s) r (e := 41) (by decide)
      have hlt : ((c :: s).dropWhile isSpace).length < n := by
        rw [List.dropWhile_cons, if_pos hs]
        have := dropWhile_length_le isSpace s; omega
      obtain ⟨ks', h1, h2, h3⟩ := commentLoop_esc r n ((c :: s).dropWhile isSpace) ty
        (ks ++ [WT ((c :: s).takeWhile isSpace) "fws"]) ds atts hlt
      refine ⟨WT ((c :: s).takeWhile isSpace) "fws" :: ks', ?_, ?_, ?_⟩
      · rw [hv]
        unfold commentLoop
        have hc41 : (c == 41) = false := by
          cases h : (c == 41)
          · rfl
          · simp at h; subst h; cases hw
        simp only [hc41, hw, Bool.false_eq_true, ↓reduceIte]
        rw [← hv, hfws.1, hfws.2]
        simp only [Tok.push]
        rw [h1]; simp
      · rw [strs, h2]
        simp only [Tok.str, WT]
        exact List.takeWhile_append_dropWhile
      · intro k hk
        simp only [List.mem_cons] at hk
        rcases hk with rfl | hk
        · simp [WT, Tok.ty]
        · exact h3 k hk
    · have hw' : isWsp c = false := by simpa using hw
      obtain ⟨h, tl, hv, hhw, hhend, hh⟩ := escWith_head escOkParen (s := s) hw' (41 :: r)
      have hh41 : (h == 41) = false := by
        simp only [Bool.or_eq_false_iff] at hhend; exact hhend.2
      have hh40 : (h == 40) = false := by
        simp only [Bool.or_eq_false_iff] at hhend; exact hhend.1
      obtain ⟨qp, hq⟩ := ptext_esc escOkParen (s := s) hw' r (e := 41) (by decide) (by decide)
      obtain ⟨t, ht⟩ : ∃ t, t = (c :: s).takeWhile (fun x => !isWsp x) := ⟨_, rfl⟩
      obtain ⟨u, hu⟩ : ∃ u, u = (c :: s).dropWhile (fun x => !isWsp x) := ⟨_, rfl⟩
      rw [← ht, ← hu] at hq
      have hqc : getQpCtext (escWith Eparen (c :: s) ++ 41 :: r) =
          .ok (validateXtext (WT t "ptext"), escWith Eparen u ++ 41 :: r) := by
        simp only [getQpCtext, hq]; rfl
      have hlt : u.length < n := by
        have := dropWhile_notWsp_lt (s := s) hw'; rw [hu]; omega
      obtain ⟨ks', h1, h2, h3⟩ := commentLoop_esc r n u ty (ks ++ [validateXtext (WT t "ptext")])
        ds atts hlt
      refine ⟨validateXtext (WT t "ptext") :: ks', ?_, ?_, ?_⟩
      · rw [hv]
        unfold commentLoop
        simp only [hh41, hh40, hhw, Bool.false_eq_true, ↓reduceIte]
        rw [← hv, hqc]
        simp only [Tok.push]
        rw [h1]; simp
      · rw [strs, h2, (validateXtext_WT t "ptext").1, ht, hu]
        exact split_noWsp c s
      · intro k hk
        simp only [List.mem_cons] at hk
        rcases hk with rfl | hk
        · rw [(validateXtext_WT t "ptext").2]; decide
        · exact h3 k hk

/-! ## The round trips -/

theorem quotingRoundTrip_proven : QuotingRoundTrip := by
  refine ⟨?_, ?_⟩
  · intro cfg n s r hc hn
    have hq : quoteString s ++ r = 34 :: (escWith E34 s ++ 34 :: r) := by
      simp [quoteString, makeQuotedPairs_eq]
    rw [hq]
    cases s with
    | nil =>
      refine ⟨mkL .bareQuotedString, by simp [getBareQuotedString, escWith_nil]; rfl, rfl, rfl⟩
    | cons c s =>
      obtain ⟨ks', h1, h2⟩ := bqsLoop_esc hc r n (c :: s) "bare-quoted-string" [] [] []
        (by simp at hn ⊢; omega)
      by_cases hw : isWsp c = true
      · have hsp := escOk34.space c (isSpace_of_wsp hw)
        have hv : escWith E34 (c :: s) ++ 34 :: r = c :: (escWith E34 s ++ 34 :: r) := by
          rw [escWith_cons, if_neg (by simp [hsp.1, hsp.2])]; rfl
        have hc34 : c ≠ 34 := by rintro rfl; cases hw
        refine ⟨.node .bareQuotedString "bare-quoted-string" ks' [] [], ?_, ?_, ?_⟩
        · unfold getBareQuotedString
          rw [hv]
          simp only
          split
          · rename_i heq; exact absurd (List.cons.inj heq).1 hc34
          · rw [← hv]
            simp only [mkL, LC.defTy] at h1 ⊢
            rw [h1]; simp; rfl
        · simp [Tok.str, quoteString, h2]
        · simp [Tok.value, valueF, h2]; rfl
      · have hw' : isWsp c = false := by simpa using hw
        obtain ⟨h, tl, hv, _, hh34, _⟩ := escWith_head escOk34 hw' (34 :: r)
        have hh : h ≠ 34 := by
          rintro rfl; simp at hh34
        refine ⟨.node .bareQuotedString "bare-quoted-string" ks' [] [], ?_, ?_, ?_⟩
        · unfold getBareQuotedString
          rw [hv]
          simp only
          split
          · rename_i heq; exact absurd (List.cons.inj heq).1 hh
          · rw [← hv]
            simp only [mkL, LC.defTy] at h1 ⊢
            rw [h1]; simp; rfl
        · simp [Tok.str, quoteString, h2]
        · simp [Tok.value, valueF, h2]; rfl
  · intro n s r hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨ks', h1, h2, h3⟩ := commentLoop_esc r m s "comment" [] [] [] (by omega)
    refine ⟨.node .comment "comment" ks' [] [], ?_, ?_, ?_⟩
    · have hv : [40] ++ makeParenPairs s ++ [41] ++ r = 40 :: (escWith Eparen s ++ 41 :: r) := by
        simp [makeParenPairs_eq]
      rw [hv, getComment]
      simp only [headIs, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.drop_succ_cons,
        List.drop_zero]
      simp only [mkL, LC.defTy] at h1 ⊢
      rw [h1]; simp; rfl
    · simp only [Tok.str]
      rw [commentStrs_noComment ks' (by simpa using h3), h2]
    · simp [commentContent, Tok.kids, h2]

/-! ## `had_qp` -/

/-- `a\b`: the quoted pair `\b` is decoded (the backslash is dropped), but `had_qp` is only set
for an escaped backslash (:1052-1055), so the flag is false. -/
theorem ptext_qp_unset :
    getPtextToEndchars [97, 92, 98] (fun c => c == 34) = .ok ([97, 98], [], false) := by
  rfl

/-- What it changes: `get_dtext` adds "quoted printable found in domain-literal" only when the
flag is set (:1595-1597), so the domain literal `[a\b]` gets no defect, while `[a\\b]` does. -/
theorem dtext_no_defect :
    ((getDtext [97, 92, 98]).toOption.map (·.1.ds), (getDtext [97, 92, 92, 98]).toOption.map
      (·.1.ds.map (·.cls))) = (some [], some ["ObsoleteHeaderDefect"]) := by
  decide +kernel

theorem ptextQpFlag_refuted : ¬ PtextQpFlag := by
  intro h
  have := h [97, 92, 98] (fun c => c == 34) [97, 98] [] false ptext_qp_unset (by decide)
  cases this

end PyLean.TextLibs.Email
