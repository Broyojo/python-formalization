import PyLean.TextLibs.TomlArr
import PyLean.TextLibs.TomlDate

/-!
The `TOMLDecodeError`s of strings, keys and values: each error path with its message and
position, quantified over every input that reaches it.
-/

namespace PyLean.TextLibs.Toml

/-! ## Escapes, _parser.py:566-611 -/

/-- The letters `parse_basic_str_escape` accepts after `\` outside the whitespace branch. -/
def escOk (c : Nat) : Bool :=
  c == 98 || c == 116 || c == 110 || c == 102 || c == 114 || c == 101 || c == 34 || c == 92 ||
    c == 120 || c == 117 || c == 85

theorem escRepl_none {c : Nat} (h : escOk c = false) : escRepl [92, c] = none := by
  simp only [escOk, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, -⟩, -⟩, -⟩ := h
  unfold escRepl; split <;> simp_all

/-- Escapes, TOML 1.1 "String" ("All other escape sequences not listed above are reserved; if
they are used, TOML should produce an error"; a line-ending backslash must be followed by
whitespace up to the newline): in both modes, `\` followed by a character that is not an escape
letter (nor, in a multi-line string, a space, tab or newline) raises "Unescaped '\\' in a
string" two characters on; `\x`, `\u` and `\U` not followed by 2, 4 or 8 hex digits raise
"Invalid hex value" after the letter; in a multi-line string, `\` then spaces or tabs then a
character that is not a newline raises "Unescaped '\\' in a string" at that character, and
spaces or tabs up to the end of the document end the escape there. A `\` that is the last
character of the document raises "Unescaped '\\' in a string" at `pos + 2`, one past the end
(see `DecodeErrorPosInDoc`). -/
def EscapeErrors : Prop :=
  (∀ (src : Str) (pos c : Nat) (ml : Bool) (rest : Str), src.drop pos = 92 :: c :: rest → escOk c = false →
    (ml = true → c ≠ 32 ∧ c ≠ 9 ∧ c ≠ 10) →
    parseBasicStrEscape src pos ml = .error (tdeS "Unescaped '\\' in a string" src (pos + 2))) ∧
  (∀ (src : Str) (pos l n : Nat) (ml : Bool) (rest : Str), src.drop pos = 92 :: l :: rest →
    ((l = 120 ∧ n = 2) ∨ (l = 117 ∧ n = 4) ∨ (l = 85 ∧ n = 8)) →
    ¬ ((rest.take n).length = n ∧ ∀ x ∈ rest.take n, hexDigit x = true) →
    parseBasicStrEscape src pos ml = .error (tdeS "Invalid hex value" src (pos + 2))) ∧
  (∀ (src : Str) (pos w d : Nat) (ws rest : Str), src.drop pos = 92 :: w :: ws ++ d :: rest →
    (w = 32 ∨ w = 9) → allWs ws → tomlWs d = false → d ≠ 10 →
    parseBasicStrEscape src pos true = .error (tdeS "Unescaped '\\' in a string" src (pos + 2 + ws.length))) ∧
  (∀ (src : Str) (pos w : Nat) (ws : Str), src.drop pos = 92 :: w :: ws → (w = 32 ∨ w = 9) → allWs ws →
    parseBasicStrEscape src pos true = .ok (pos + 2 + ws.length, [])) ∧
  (∀ (src : Str) (pos : Nat) (ml : Bool), src.drop pos = [92] →
    parseBasicStrEscape src pos ml = .error (tdeS "Unescaped '\\' in a string" src (pos + 2)))

theorem escapeErrors_proven : EscapeErrors := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro src pos c ml rest h hc hml
    have hsl : sl src pos (pos + 2) = [92, c] := sl_of_drop (a := [92, c]) (by simpa using h)
    have hn := escRepl_none hc
    simp only [escOk, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hc
    obtain ⟨⟨⟨-, h120⟩, h117⟩, h85⟩ := hc
    cases ml
    · simp [parseBasicStrEscape, hsl, h120, h117, h85, hn]
    · obtain ⟨a, b, d⟩ := hml rfl
      simp [parseBasicStrEscape, hsl, a, b, d, h120, h117, h85, hn]
  · intro src pos l n ml rest h hl hbad
    have hsl : sl src pos (pos + 2) = [92, l] := sl_of_drop (a := [92, l]) (by simpa using h)
    have h2 : src.drop (pos + 2) = rest := by simpa using drop_add_of_drop (a := [92, l]) (by simpa using h)
    have hhex : sl src (pos + 2) (pos + 2 + n) = rest.take n := by simp [sl, h2]
    have hbad' : ((rest.take n).length != n || !(rest.take n).all hexDigit) = true := by
      rw [Bool.or_eq_true]
      by_cases h1 : (rest.take n).length = n
      · right
        have : ¬ ∀ x ∈ rest.take n, hexDigit x = true := fun h' => hbad ⟨h1, h'⟩
        have hall : (rest.take n).all hexDigit = false := by
          rw [Bool.eq_false_iff]; intro hh; exact this (List.all_eq_true.mp hh)
        rw [hall]; rfl
      · left; exact bne_iff_ne.mpr h1
    have hph : parseHexChar src (pos + 2) n = .error (tdeS "Invalid hex value" src (pos + 2)) := by
      simp only [parseHexChar, hhex]; rw [if_pos hbad']
    rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases ml <;>
      simp [parseBasicStrEscape, hsl, hph]
  · intro src pos w d ws rest h hw hws hd h10
    have hsl : sl src pos (pos + 2) = [92, w] := sl_of_drop (a := [92, w]) (by simpa using h)
    have h2 : src.drop (pos + 2) = ws ++ d :: rest := by
      simpa using drop_add_of_drop (a := [92, w]) (by simpa using h)
    have hsk : skipChars src (pos + 2) tomlWs = pos + 2 + ws.length :=
      skipChars_of_drop h2 hws (by intro c hc; simp at hc; subst hc; exact hd)
    have hg : src[pos + 2 + ws.length]? = some d := getElem?_of_drop (by simpa using drop_add_of_drop h2)
    rcases hw with rfl | rfl <;> simp [parseBasicStrEscape, hsl, hsk, hg, h10]
  · intro src pos w ws h hw hws
    have hsl : sl src pos (pos + 2) = [92, w] := sl_of_drop (a := [92, w]) (by simpa using h)
    have h2 : src.drop (pos + 2) = ws ++ [] := by
      simpa using drop_add_of_drop (a := [92, w]) (by simpa using h)
    have hsk : skipChars src (pos + 2) tomlWs = pos + 2 + ws.length :=
      skipChars_of_drop h2 hws (by simp)
    have hg : src[pos + 2 + ws.length]? = none := getElem?_of_drop_nil (by simpa using drop_add_of_drop h2)
    rcases hw with rfl | rfl <;> simp [parseBasicStrEscape, hsl, hsk, hg]
  · intro src pos ml h
    have hsl : sl src pos (pos + 2) = [92] := by simp [sl, h]
    cases ml <;> simp [parseBasicStrEscape, hsl, escRepl]

/-! ## Unterminated basic strings, _parser.py:663-667 -/

/-- The loop of `parse_basic_str` (one-line) over pieces that run to the end of the document. -/
theorem basicStrLoop_eof (src : Str) : ∀ (ps : List Piece), (∀ p ∈ ps, p.ok) →
    ∀ (fuel pos start : Nat) (res : Str), src.drop pos = encAll ps → start ≤ pos →
    (encAll ps).length < fuel →
    basicStrLoop src false fuel pos start res = .error (tdeS "Unterminated string" src (pos + (encAll ps).length))
  | [], _, fuel, pos, start, res, h, _, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [encAll] at hf; omega⟩
    have hg := getElem?_of_drop_nil (by simpa [encAll] using h)
    simp [basicStrLoop, hg, encAll]
  | p :: ps, hok, fuel, pos, start, res, h, hs, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [encAll] at hf; omega⟩
    have hp := hok p (by simp)
    have hps : ∀ q ∈ ps, q.ok := fun q hq => hok q (by simp [hq])
    have hlen : (encAll (p :: ps)).length = p.enc.length + (encAll ps).length := by simp [encAll]
    have h' : src.drop pos = p.enc ++ encAll ps := by simpa [encAll] using h
    by_cases hr : ∃ c, p = .raw c
    · obtain ⟨c, rfl⟩ := hr
      obtain ⟨h34, h92, hill⟩ := hp
      have h1 : src.drop pos = c :: encAll ps := by simpa [Piece.enc] using h'
      have hg := getElem?_of_drop h1
      have ih := basicStrLoop_eof src ps hps f (pos + 1) start (res) (drop_succ_of_drop h1) (by omega)
        (by simp [Piece.enc] at hlen; omega)
      simp only [basicStrLoop, hg, beq_iff_eq, h34, h92, ite_false, hill, Bool.false_eq_true, ih]
      congr 2; simp [hlen, Piece.enc]; omega
    · have hraw : ∀ c, p ≠ .raw c := fun c e => hr ⟨c, e⟩
      have hesc := parseEscape_piece hp hraw h' false
      obtain ⟨t, ht⟩ : ∃ t, p.enc = 92 :: t := by
        cases p with
        | raw c => exact absurd rfl (hraw c)
        | _ => exact ⟨_, rfl⟩
      have hg : src[pos]? = some 92 := getElem?_of_drop (r := t ++ encAll ps) (by rw [h', ht]; rfl)
      have hd := drop_add_of_drop h'
      have hpos : 0 < p.enc.length := List.length_pos_iff.mpr (piece_enc_ne_nil p)
      have ih := basicStrLoop_eof src ps hps f _ _ (res ++ sl src start pos ++ [p.val]) hd
        (Nat.le_refl _) (by omega)
      simp only [basicStrLoop, hg, hesc]
      simp only [show (92 == 34) = false from rfl, show (92 == 92) = true from rfl, Bool.false_eq_true,
        ite_false, ite_true, bind, Except.bind]
      rw [ih]; congr 2; omega

/-! ## Keys, _parser.py:449-500 -/

/-- Keys, TOML 1.1 "Keys": `parse_key_part` at the end of the document or at a character that
cannot start a key (not `A-Za-z0-9_-`, `"` or `'`) raises "Invalid initial character for a key
part" there; `parse_key_value_pair` on a key (any dotted key `KeySpec` reads, with at most
`MAX_KEY_PARTS` parts) whose trailing whitespace is followed by anything but `=` (the end of the
document included) raises "Expected '=' after a key in a key/value pair" there, with at least eight
frames left below it. -/
def KeyErrors : Prop :=
  (∀ (src : Str) (pos : Nat), (∀ c, src[pos]? = some c → keyInitial c = false) →
    parseKeyPart src pos = .error (tdeS "Invalid initial character for a key part" src pos)) ∧
  (∀ (cfg : Cfg) (src : Str) (r pos fuel : Nat) (p0 : KPart) (ws0 : Str) (more : List (Str × KPart × Str))
    (rest : Str), 8 ≤ r → p0.ok → allWs ws0 → (∀ m ∈ more, allWs m.1 ∧ m.2.1.ok ∧ allWs m.2.2) →
    (∀ c, rest.head? = some c → tomlWs c = false ∧ c ≠ 46 ∧ bareKey c = false ∧ c ≠ 61) →
    more.length + 1 ≤ cfg.maxKeyParts →
    src.drop pos = p0.enc ++ ws0 ++ more.flatMap moreEnc ++ rest →
    parseKeyValuePair cfg src r (fuel + 1) pos =
      .error (tdeS "Expected '=' after a key in a key/value pair" src
        (pos + (p0.enc ++ ws0 ++ more.flatMap moreEnc).length)))

theorem keyErrors_proven : KeyErrors := by
  refine ⟨?_, ?_⟩
  · intro src pos h
    unfold parseKeyPart
    split
    · next c hc =>
      have hk := h c hc
      simp only [keyInitial, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hk
      obtain ⟨⟨hb, h34⟩, h39⟩ := hk
      simp [hb, h34, h39]
    · rfl
  · intro cfg src r pos fuel p0 ws0 more rest hr hp0 hws0 hmore hrest hmax h
    have hkey := keySpec_proven cfg.maxKeyParts src pos p0 ws0 more rest hp0 hws0 hmore
      (fun c hc => ⟨(hrest c hc).1, (hrest c hc).2.1, (hrest c hc).2.2.1⟩) h
    rw [if_pos (Or.inl hmax)] at hkey
    have hne : src[pos + (p0.enc ++ ws0 ++ more.flatMap moreEnc).length]? ≠ some 61 := by
      have hd := drop_add_of_drop (a := p0.enc ++ ws0 ++ more.flatMap moreEnc) (r := rest) (by simpa using h)
      cases hrr : rest with
      | nil => rw [hrr] at hd; rw [getElem?_of_drop_nil hd]; simp
      | cons c t => rw [hrr] at hd; rw [getElem?_of_drop hd]; simpa using (hrest c (by simp [hrr])).2.2.2
    simp only [parseKeyValuePair, need_parseKey hr, hkey, bind, Except.bind]
    have hne' : (src[pos + (p0.enc ++ ws0 ++ more.flatMap moreEnc).length]? != some 61) = true :=
      bne_iff_ne.mpr hne
    rw [if_pos hne']

/-! ## Values, _parser.py:686-751 -/

theorem matchNumber_head {c : Nat} {t : Str} (hd : isDigit c = false) (h43 : c ≠ 43) (h45 : c ≠ 45) :
    matchNumber (c :: t) = none := by
  have h48 : c ≠ 48 := by intro e; subst e; simp [isDigit, inR] at hd
  rw [matchNumber_eq, nAlt1_head h48]
  have hs : nSign (c :: t) = 0 := by unfold nSign; split <;> simp_all
  rw [hs]
  have hip : nIp (c :: t) = none := by
    unfold nIp; split
    · simp_all
    · next c' r heq =>
      simp at heq; obtain ⟨rfl, rfl⟩ := heq
      have : inR 49 57 c = false := by revert hd; simp [isDigit, inR]; omega
      simp [this]
    · rfl
  simp [hip]

/-- The characters that start no value: not a digit, `"`, `'`, `[`, `{`, `+`, `-`, `i` or `n`. -/
def noValueHead (c : Nat) : Bool :=
  !isDigit c && c != 34 && c != 39 && c != 91 && c != 123 && c != 43 && c != 45 && c != 105 && c != 110

/-- Values, TOML 1.1 ("Unspecified values are invalid"): `parse_value` at the end of the document,
or at a character that starts no value (`t` and `f` included, when not followed by the rest of
`true` or `false`), raises "Invalid value" there, with at least one frame left below it. -/
def InvalidValue : Prop :=
  ∀ (cfg : Cfg) (src : Str) (r pos fuel : Nat), 1 ≤ r →
    (∀ c, src[pos]? = some c → noValueHead c = true ∧ (c = 116 → startsAt src pos (S "true") = false) ∧
      (c = 102 → startsAt src pos (S "false") = false)) →
    parseValue cfg src r (fuel + 1) pos = .error (tdeS "Invalid value" src pos)

theorem invalidValue_proven : InvalidValue := by
  intro cfg src r pos fuel hr h
  cases hg : src[pos]? with
  | none =>
    have hd : src.drop pos = [] := by
      rw [List.getElem?_eq_none_iff] at hg; simp [List.drop_eq_nil_iff]; omega
    have h3 : sl src pos (pos + 3) = [] := by simp [sl, hd]
    have h4 : sl src pos (pos + 4) = [] := by simp [sl, hd]
    simp [parseValue, hg, hd, matchDatetime, matchTime, h3, h4, S, need_ok hr]
    rfl
  | some c =>
    obtain ⟨hv, ht, hf⟩ := h c hg
    simp only [noValueHead, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hv
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hdig, h34⟩, h39⟩, h91⟩, h123⟩, h43⟩, h45⟩, h105⟩, h110⟩ := hv
    obtain ⟨t, hd⟩ : ∃ t, src.drop pos = c :: t := by
      cases hdd : src.drop pos with
      | nil => rw [getElem?_of_drop_nil hdd] at hg; cases hg
      | cons c' t => rw [getElem?_of_drop hdd] at hg; cases hg; exact ⟨t, rfl⟩
    have hmd : matchDatetime (src.drop pos) = none := by rw [hd]; exact matchDatetime_head hdig
    have hmt : matchTime (src.drop pos) = none := by rw [hd]; exact matchTime_head hdig
    have hmn : matchNumber (src.drop pos) = none := by rw [hd]; exact matchNumber_head hdig h43 h45
    have h3 : (sl src pos (pos + 3) == S "inf" || sl src pos (pos + 3) == S "nan") = false := by
      have : (sl src pos (pos + 3)).head? = some c := by simp [sl, hd]
      cases hs : sl src pos (pos + 3) with
      | nil => simp [S]
      | cons x xs => rw [hs] at this; simp at this; subst this; simp [S, h105, h110]
    have h4 : (sl src pos (pos + 4) == S "-inf" || sl src pos (pos + 4) == S "+inf" ||
        sl src pos (pos + 4) == S "-nan" || sl src pos (pos + 4) == S "+nan") = false := by
      have : (sl src pos (pos + 4)).head? = some c := by simp [sl, hd]
      cases hs : sl src pos (pos + 4) with
      | nil => simp [S]
      | cons x xs => rw [hs] at this; simp at this; subst this; simp [S, h43, h45]
    have htrue : (some c == some 116 && startsAt src pos (S "true")) = false := by
      by_cases e : c = 116
      · simp [ht e]
      · simp [e]
    have hfalse : (some c == some 102 && startsAt src pos (S "false")) = false := by
      by_cases e : c = 102
      · simp [hf e]
      · simp [e]
    simp only [parseValue, hg, htrue, hfalse, optBeq_ne h34, optBeq_ne h39, optBeq_ne h91, optBeq_ne h123,
      Bool.false_eq_true, ite_false, hmd, hmt, hmn, h3, h4, need_ok hr]

/-- Unterminated strings, TOML 1.1 "String": `"` followed by characters and escapes (any the spec
allows) up to the end of the document raises "Unterminated string" at the end, with at least six
frames left below `parse_value`. -/
def UnterminatedString : Prop :=
  ∀ (cfg : Cfg) (src : Str) (r pos fuel : Nat) (ps : List Piece), 6 ≤ r → (∀ p ∈ ps, p.ok) →
    src.drop pos = 34 :: encAll ps →
    parseValue cfg src r (fuel + 1) pos = .error (tdeS "Unterminated string" src (pos + 1 + (encAll ps).length))

theorem unterminatedString_proven : UnterminatedString := by
  intro cfg src r pos fuel ps hr hok h
  have hg := getElem?_of_drop h
  have h1 : src.drop (pos + 1) = encAll ps := drop_succ_of_drop h
  have hst : startsAt src pos [34, 34, 34] = false := by
    unfold startsAt; rw [h]
    cases ps with
    | nil => simp [encAll, List.isPrefixOf]
    | cons p ps =>
      have hp := hok p (by simp)
      cases p <;> simp [encAll, Piece.enc, List.isPrefixOf] <;> simp [Piece.ok] at hp <;> omega
  have hlen : (encAll ps).length < src.length + 1 := by
    have := congrArg List.length h; simp at this; omega
  have hloop := basicStrLoop_eof src ps hok (src.length + 1) (pos + 1) (pos + 1) [] h1 (Nat.le_refl _) hlen
  simp only [parseValue, hg, hst, show (some 34 == some 34) = true from rfl, ite_true, Bool.false_eq_true,
    ite_false, need_ok (Nat.le_trans (parseOneLineBasicStrN_le src pos) hr), parseOneLineBasicStr,
    parseBasicStr, hloop]
  rfl

end PyLean.TextLibs.Toml
