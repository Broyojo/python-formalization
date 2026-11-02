import PyLean.TextLibs.TomlLemmas

/-!
Basic and literal strings: `parse_value` reads back every way the TOML 1.1 spec allows to
write a string.
-/

namespace PyLean.TextLibs.Toml

/-- The letter of the short escape of a character, TOML 1.1 "String" (`\b \t \n \f \r \e \" \\`). -/
def escLetter : Nat → Option Nat
  | 0x08 => some 98
  | 0x09 => some 116
  | 0x0a => some 110
  | 0x0c => some 102
  | 0x0d => some 114
  | 0x1b => some 101
  | 0x22 => some 34
  | 0x5c => some 92
  | _ => none

/-- A hex digit, upper or lower case. -/
def hexChar (d : Nat) (up : Bool) : Nat := if d < 10 then 48 + d else if up then 55 + d else 87 + d

/-- `n` in `w` hex digits. -/
def hexD (n : Nat) : Nat → Bool → Str
  | 0, _ => []
  | w + 1, up => hexD (n / 16) w up ++ [hexChar (n % 16) up]

/-- One character of a basic string as written: itself, its short escape, or `\xHH`, `\uHHHH`,
`\UHHHHHHHH` in either case. -/
inductive Piece where
  | raw (c : Nat)
  | short (c : Nat)
  | x (c : Nat) (up : Bool)
  | u (c : Nat) (up : Bool)
  | U (c : Nat) (up : Bool)
  deriving Repr, DecidableEq

def Piece.enc : Piece → Str
  | .raw c => [c]
  | .short c => [92, (escLetter c).getD 0]
  | .x c up => [92, 120] ++ hexD c 2 up
  | .u c up => [92, 117] ++ hexD c 4 up
  | .U c up => [92, 85] ++ hexD c 8 up

def Piece.val : Piece → Nat
  | .raw c | .short c | .x c _ | .u c _ | .U c _ => c

/-- What TOML 1.1 allows: a raw character that is not `"`, `\` or a control character other
than tab; a short escape; `\x` for code points below 256; `\u` and `\U` for Unicode scalar
values. -/
def Piece.ok : Piece → Prop
  | .raw c => c ≠ 34 ∧ c ≠ 92 ∧ illegalBasic c = false
  | .short c => (escLetter c).isSome = true
  | .x c _ => c < 256
  | .u c _ => c < 65536 ∧ isScalar c = true
  | .U c _ => isScalar c = true

def encAll (ps : List Piece) : Str := ps.flatMap Piece.enc

/-! ## Hex digits -/

theorem hexD_length (n : Nat) (up : Bool) : ∀ w, (hexD n w up).length = w
  | 0 => rfl
  | w + 1 => by simp [hexD, hexD_length (n / 16) up w]

theorem hexChar_hex : ∀ d < 16, ∀ up, hexDigit (hexChar d up) = true := by decide
theorem hexVal_hexChar : ∀ d < 16, ∀ up, hexVal (hexChar d up) = d := by decide

theorem hexD_all (up : Bool) : ∀ (w n : Nat), ∀ x ∈ hexD n w up, hexDigit x = true
  | 0, _ => by simp [hexD]
  | w + 1, n => by
    intro x hx
    simp only [hexD, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx
    · exact hexD_all up w (n / 16) x hx
    · subst hx; exact hexChar_hex _ (Nat.mod_lt _ (by decide)) up

theorem hexInt_snoc (l : Str) (x : Nat) : hexInt (l ++ [x]) = hexInt l * 16 + hexVal x := by
  simp [hexInt, List.foldl_append]

theorem hexInt_hexD (up : Bool) : ∀ (w n : Nat), hexInt (hexD n w up) = n % 16 ^ w
  | 0, n => by simp [hexD, hexInt]; omega
  | w + 1, n => by
    rw [hexD, hexInt_snoc, hexInt_hexD up w (n / 16), hexVal_hexChar _ (Nat.mod_lt _ (by decide)),
      Nat.pow_succ, Nat.mul_comm (16 ^ w) 16, Nat.mod_mul]
    omega

/-- `parse_hex_char` on `w` hex digits of a scalar value below `16 ** w`. -/
theorem parseHexChar_ok {src : Str} {pos c w : Nat} {up : Bool} {rest : Str}
    (h : src.drop pos = hexD c w up ++ rest) (hc : c < 16 ^ w) (hs : isScalar c = true) :
    parseHexChar src pos w = .ok (pos + w, [c]) := by
  have hsl : sl src pos (pos + w) = hexD c w up := by
    have := sl_of_drop h; rwa [hexD_length] at this
  have hall : (hexD c w up).all hexDigit = true := by
    simp only [List.all_eq_true]; exact hexD_all up w c
  simp [parseHexChar, hsl, hexD_length, hall, hexInt_hexD, Nat.mod_eq_of_lt hc, hs]

/-- ... and on a value that is not a Unicode scalar value. -/
theorem parseHexChar_notScalar {src : Str} {pos c w : Nat} {up : Bool} {rest : Str}
    (h : src.drop pos = hexD c w up ++ rest) (hc : c < 16 ^ w) (hs : isScalar c = false) :
    parseHexChar src pos w =
      .error (tdeS "Escaped character is not a Unicode scalar value" src (pos + w)) := by
  have hsl : sl src pos (pos + w) = hexD c w up := by
    have := sl_of_drop h; rwa [hexD_length] at this
  have hall : (hexD c w up).all hexDigit = true := by
    simp only [List.all_eq_true]; exact hexD_all up w c
  simp [parseHexChar, hsl, hexD_length, hall, hexInt_hexD, Nat.mod_eq_of_lt hc, hs]

theorem escLetter_spec {c l : Nat} (h : escLetter c = some l) :
    escRepl [92, l] = some c ∧ l ≠ 120 ∧ l ≠ 117 ∧ l ≠ 85 ∧ l ≠ 32 ∧ l ≠ 9 ∧ l ≠ 10 := by
  unfold escLetter at h
  split at h <;> simp at h <;> subst h <;> decide

theorem isScalar_lt {c : Nat} (h : isScalar c = true) : c < 16 ^ 8 := by
  simp [isScalar, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

/-- `parse_basic_str_escape` on any escaped piece (in both modes). -/
theorem parseEscape_piece {src : Str} {pos : Nat} {p : Piece} {rest : Str} (hp : p.ok)
    (hraw : ∀ c, p ≠ .raw c) (h : src.drop pos = p.enc ++ rest) (m : Bool) :
    parseBasicStrEscape src pos m = .ok (pos + p.enc.length, [p.val]) := by
  cases p with
  | raw c => exact absurd rfl (hraw c)
  | short c =>
    simp only [Piece.ok] at hp
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp hp
    obtain ⟨hr, h1, h2, h3, h4, h5, h6⟩ := escLetter_spec hl
    simp only [Piece.enc, hl, Option.getD_some] at h
    have hsl : sl src pos (pos + 2) = [92, l] := sl_of_drop (a := [92, l]) h
    simp [parseBasicStrEscape, hsl, h1, h2, h3, h4, h5, h6, hr, Piece.enc, Piece.val, hl]
  | x c up =>
    simp only [Piece.ok] at hp
    simp only [Piece.enc] at h
    have hsl : sl src pos (pos + 2) = [92, 120] := sl_of_drop (a := [92, 120]) (by simpa using h)
    have h2 : src.drop (pos + 2) = hexD c 2 up ++ rest := drop_add_of_drop (a := [92, 120]) (by simpa using h)
    have hs : isScalar c = true := by simp [isScalar]; omega
    have := parseHexChar_ok h2 (by omega) hs
    (simp [parseBasicStrEscape, hsl, this, Piece.enc, Piece.val, hexD_length]) <;> omega
  | u c up =>
    simp only [Piece.ok] at hp
    simp only [Piece.enc] at h
    have hsl : sl src pos (pos + 2) = [92, 117] := sl_of_drop (a := [92, 117]) (by simpa using h)
    have h2 : src.drop (pos + 2) = hexD c 4 up ++ rest := drop_add_of_drop (a := [92, 117]) (by simpa using h)
    have := parseHexChar_ok h2 (by omega) hp.2
    (simp [parseBasicStrEscape, hsl, this, Piece.enc, Piece.val, hexD_length]) <;> omega
  | U c up =>
    simp only [Piece.ok] at hp
    simp only [Piece.enc] at h
    have hsl : sl src pos (pos + 2) = [92, 85] := sl_of_drop (a := [92, 85]) (by simpa using h)
    have h2 : src.drop (pos + 2) = hexD c 8 up ++ rest := drop_add_of_drop (a := [92, 85]) (by simpa using h)
    have := parseHexChar_ok h2 (isScalar_lt hp) hp
    (simp [parseBasicStrEscape, hsl, this, Piece.enc, Piece.val, hexD_length]) <;> omega

theorem piece_enc_ne_nil (p : Piece) : p.enc ≠ [] := by
  cases p <;> simp [Piece.enc]

theorem piece_enc_head (p : Piece) (hp : p.ok) : ∃ t, p.enc = (match p with
    | .raw c => c
    | _ => 92) :: t := by
  cases p <;> simp [Piece.enc]

/-- The loop of `parse_basic_str` (one-line) over a run of pieces closed by `"`. -/
theorem basicStrLoop_pieces (src rest : Str) : ∀ (ps : List Piece), (∀ p ∈ ps, p.ok) →
    ∀ (fuel pos start : Nat) (res : Str), src.drop pos = encAll ps ++ 34 :: rest → start ≤ pos →
    (encAll ps).length < fuel →
    basicStrLoop src false fuel pos start res =
      .ok (pos + (encAll ps).length + 1, res ++ sl src start pos ++ ps.map Piece.val)
  | [], _, fuel, pos, start, res, h, _, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [encAll] at hf; omega⟩
    have hg := getElem?_of_drop (r := rest) (by simpa [encAll] using h)
    simp [basicStrLoop, hg, encAll]
  | p :: ps, hok, fuel, pos, start, res, h, hs, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [encAll] at hf; omega⟩
    have hp := hok p (by simp)
    have hps : ∀ q ∈ ps, q.ok := fun q hq => hok q (by simp [hq])
    have hlen : (encAll (p :: ps)).length = p.enc.length + (encAll ps).length := by simp [encAll]
    have h' : src.drop pos = p.enc ++ (encAll ps ++ 34 :: rest) := by simpa [encAll] using h
    by_cases hr : ∃ c, p = .raw c
    · obtain ⟨c, rfl⟩ := hr
      obtain ⟨h34, h92, hill⟩ := hp
      have h1 : src.drop pos = c :: (encAll ps ++ 34 :: rest) := by simpa [Piece.enc] using h'
      have hg := getElem?_of_drop h1
      have ih := basicStrLoop_pieces src rest ps hps f (pos + 1) start res (drop_succ_of_drop h1) (by omega)
        (by simp [Piece.enc] at hlen; omega)
      have hsn := sl_snoc hs h1
      simp only [basicStrLoop, hg, beq_iff_eq, h34, h92, ite_false, hill, Bool.false_eq_true, ih, hsn]
      (simp [hlen, Piece.enc, Piece.val]) <;> omega
    · have hraw : ∀ c, p ≠ .raw c := fun c e => hr ⟨c, e⟩
      have hesc := parseEscape_piece hp hraw h' false
      obtain ⟨t, ht⟩ : ∃ t, p.enc = 92 :: t := by
        cases p with
        | raw c => exact absurd rfl (hraw c)
        | _ => exact ⟨_, rfl⟩
      have hg : src[pos]? = some 92 := getElem?_of_drop (r := t ++ (encAll ps ++ 34 :: rest))
        (by rw [h', ht]; rfl)
      have hd := drop_add_of_drop h'
      have hpos : 0 < p.enc.length := List.length_pos_iff.mpr (piece_enc_ne_nil p)
      have ih := basicStrLoop_pieces src rest ps hps f _ _ (res ++ sl src start pos ++ [p.val]) hd
        (Nat.le_refl _) (by omega)
      simp only [basicStrLoop, hg, hesc]
      simp only [show (92 == 34) = false from rfl, show (92 == 92) = true from rfl, Bool.false_eq_true,
        ite_false, ite_true, bind, Except.bind]
      rw [ih]
      simp [hlen, sl_self]; omega

/-- Basic strings, TOML 1.1 "String": for every list of characters each written as itself
(when it is not `"`, `\` or a control character other than tab) or with any escape that the
spec allows for it (`\b \t \n \f \r \e \" \\`, `\xHH` below 256, `\uHHHH` and `\UHHHHHHHH` for
Unicode scalar values, hex in either case), `parse_value` on `"…"` returns that string and the
position after the closing quote. An escape of a value that is not a Unicode scalar value
(a surrogate, or above U+10FFFF) raises `TOMLDecodeError` "Escaped character is not a Unicode
scalar value", and a raw control character other than tab raises "Illegal character". -/
def BasicStrRoundTrip : Prop :=
  (∀ (cfg : Cfg) (src : Str) (pos fuel : Nat) (ps : List Piece) (rest : Str),
    (∀ p ∈ ps, p.ok) → src.drop pos = 34 :: encAll ps ++ 34 :: rest →
    ¬ (ps = [] ∧ rest.head? = some 34) →
    parseValue cfg src (fuel + 1) pos = .ok (pos + (encAll ps).length + 2, .str (ps.map Piece.val))) ∧
  (∀ (src : Str) (pos c : Nat) (up multiline : Bool) (rest : Str), isScalar c = false →
    (c < 65536 → src.drop pos = [92, 117] ++ hexD c 4 up ++ rest →
      parseBasicStrEscape src pos multiline =
        .error (tdeS "Escaped character is not a Unicode scalar value" src (pos + 6))) ∧
    (c < 16 ^ 8 → src.drop pos = [92, 85] ++ hexD c 8 up ++ rest →
      parseBasicStrEscape src pos multiline =
        .error (tdeS "Escaped character is not a Unicode scalar value" src (pos + 10)))) ∧
  (∀ (src : Str) (pos fuel start c : Nat) (res rest : Str), illegalBasic c = true →
    src.drop pos = c :: rest →
    basicStrLoop src false (fuel + 1) pos start res =
      .error (tde (S "Illegal character " ++ reprS [c]) src pos))

theorem startsAt3_a {src : Str} {pos q a : Nat} {t : Str} (h : src.drop pos = q :: a :: t) (ha : a ≠ q) :
    startsAt src pos [q, q, q] = false := by
  simp [startsAt, h, List.isPrefixOf, Ne.symm ha]

theorem startsAt3_b {src : Str} {pos q b : Nat} {t : Str} (h : src.drop pos = q :: q :: b :: t)
    (hb : b ≠ q) : startsAt src pos [q, q, q] = false := by
  simp [startsAt, h, List.isPrefixOf, Ne.symm hb]

theorem startsAt3_c {src : Str} {pos q : Nat} (h : src.drop pos = [q, q]) :
    startsAt src pos [q, q, q] = false := by
  simp [startsAt, h, List.isPrefixOf]

/-- `"` or `'` followed by `a ++ q :: rest`, where `a` does not start with `q` and is non-empty
or `rest` does not start with `q`, does not open a multi-line string. -/
theorem startsAt3_of {src : Str} {pos q : Nat} {a rest : Str} (h : src.drop pos = q :: a ++ q :: rest)
    (ha : a.head? ≠ some q) (hne : ¬ (a = [] ∧ rest.head? = some q)) :
    startsAt src pos [q, q, q] = false := by
  cases a with
  | cons x t => exact startsAt3_a (a := x) (t := t ++ q :: rest) (by simpa using h) (by simpa using ha)
  | nil =>
    cases rest with
    | nil => exact startsAt3_c (by simpa using h)
    | cons b r => exact startsAt3_b (b := b) (t := r) (by simpa using h) (by simpa using hne)

theorem basicStrRoundTrip_proven : BasicStrRoundTrip := by
  refine ⟨?_, ?_, ?_⟩
  · intro cfg src pos fuel ps rest hok h hne
    have hst : startsAt src pos [34, 34, 34] = false := by
      refine startsAt3_of (by simpa using h) ?_ (by
        rintro ⟨he, hr⟩; cases ps with
        | nil => exact hne ⟨rfl, hr⟩
        | cons p _ => cases p <;> simp [encAll, Piece.enc] at he)
      cases ps with
      | nil => simp [encAll]
      | cons p ps =>
        have hp := hok p (by simp)
        cases p <;> simp [encAll, Piece.enc]
        simp [Piece.ok] at hp; exact hp.1
    have hg := getElem?_of_drop h
    have h1 := drop_succ_of_drop h
    have hlen : src.length = pos + 1 + (encAll ps).length + 1 + rest.length := by
      have := congrArg List.length h; simp at this; omega
    have hloop := basicStrLoop_pieces src rest ps hok (src.length + 1) (pos + 1) (pos + 1) [] h1
      (Nat.le_refl _) (by omega)
    simp only [parseValue, hg, hst, parseOneLineBasicStr, parseBasicStr, hloop, sl_self]
    simp [Except.map]; omega
  · intro src pos c up multiline rest hs
    refine ⟨fun hc h => ?_, fun hc h => ?_⟩
    · have hsl : sl src pos (pos + 2) = [92, 117] := sl_of_drop (a := [92, 117]) (by simpa using h)
      have h2 : src.drop (pos + 2) = hexD c 4 up ++ rest := by
        simpa using drop_add_of_drop (a := [92, 117]) (by simpa using h)
      have := parseHexChar_notScalar h2 (by omega) hs
      rw [show pos + 6 = pos + 2 + 4 by omega]
      simp [parseBasicStrEscape, hsl, this]
    · have hsl : sl src pos (pos + 2) = [92, 85] := sl_of_drop (a := [92, 85]) (by simpa using h)
      have h2 : src.drop (pos + 2) = hexD c 8 up ++ rest := by
        simpa using drop_add_of_drop (a := [92, 85]) (by simpa using h)
      have := parseHexChar_notScalar h2 hc hs
      rw [show pos + 10 = pos + 2 + 8 by omega]
      simp [parseBasicStrEscape, hsl, this]
  · intro src pos fuel start c res rest hc h
    have hg := getElem?_of_drop h
    have h34 : c ≠ 34 := by intro e; subst e; simp [illegalBasic, asciiCtrl] at hc
    have h92 : c ≠ 92 := by intro e; subst e; simp [illegalBasic, asciiCtrl] at hc
    simp [basicStrLoop, hg, h34, h92, hc]

/-! ## Literal strings -/

/-- Literal strings, TOML 1.1 "String": for every string without `'` and without control
characters other than tab, `parse_value` on `'…'` returns it unchanged; a control character
other than tab raises "Found invalid character" at its position; without a closing `'`,
"Expected \"'\"" at the end of the document (before any check of the characters). -/
def LiteralStrSpec : Prop :=
  (∀ (cfg : Cfg) (src : Str) (pos fuel : Nat) (s rest : Str),
    (∀ x ∈ s, x ≠ 39 ∧ illegalBasic x = false) → src.drop pos = 39 :: s ++ 39 :: rest →
    ¬ (s = [] ∧ rest.head? = some 39) →
    parseValue cfg src (fuel + 1) pos = .ok (pos + s.length + 2, .str s)) ∧
  (∀ (cfg : Cfg) (src : Str) (pos fuel c : Nat) (s1 s2 rest : Str),
    (∀ x ∈ s1, x ≠ 39 ∧ illegalBasic x = false) → illegalBasic c = true → 39 ∉ s2 →
    src.drop pos = 39 :: s1 ++ c :: s2 ++ 39 :: rest →
    parseValue cfg src (fuel + 1) pos =
      .error (tde (S "Found invalid character " ++ reprS [c]) src (pos + 1 + s1.length))) ∧
  (∀ (cfg : Cfg) (src : Str) (pos fuel : Nat) (s : Str), 39 ∉ s → s ≠ [] →
    src.drop pos = 39 :: s →
    parseValue cfg src (fuel + 1) pos = .error (tde (S "Expected " ++ reprS [39]) src src.length))

theorem literalStrSpec_proven : LiteralStrSpec := by
  refine ⟨?_, ?_, ?_⟩
  · intro cfg src pos fuel s rest hs h hne
    have hst : startsAt src pos [39, 39, 39] = false := by
      refine startsAt3_of (by simpa using h) ?_ hne
      cases s with
      | nil => simp
      | cons x t => simpa using (hs x (by simp)).1
    have hg := getElem?_of_drop h
    have h1 : src.drop (pos + 1) = s ++ 39 :: rest := by simpa using drop_succ_of_drop h
    have hn39 : 39 ∉ s := fun m => (hs 39 m).1 rfl
    have hfind : findSub [39] (src.drop (pos + 1)) = some s.length := by rw [h1]; exact findSub_single hn39
    have hsl := sl_of_drop h1
    have hfi : firstIdx illegalBasic (sl src (pos + 1) (pos + 1 + s.length)) = none := by
      rw [hsl]; exact firstIdx_none (fun x hx => (hs x hx).2)
    have h34 : (some 39 == some 34) = false := by decide
    simp only [parseValue, hg, h34, hst, parseLiteralStr, skipUntil, hfind, hfi]
    simp [hsl, Except.map, bind, Except.bind, pure, Except.pure]; omega
  · intro cfg src pos fuel c s1 s2 rest hs1 hc hs2 h
    have hc39 : c ≠ 39 := by intro e; subst e; simp [illegalBasic, asciiCtrl] at hc
    have hst : startsAt src pos [39, 39, 39] = false := by
      refine startsAt3_of (a := s1 ++ c :: s2) (by simpa using h) ?_ (by simp)
      cases s1 with
      | nil => simpa using hc39
      | cons x t => simpa using (hs1 x (by simp)).1
    have hg := getElem?_of_drop h
    have hn39 : 39 ∉ s1 ++ c :: s2 := by
      simp only [List.mem_append, List.mem_cons, not_or]
      exact ⟨fun m => (hs1 39 m).1 rfl, fun e => hc39 e.symm, hs2⟩
    have h1 : src.drop (pos + 1) = (s1 ++ c :: s2) ++ 39 :: rest := by
      simpa using drop_succ_of_drop h
    have hfind : findSub [39] (src.drop (pos + 1)) = some (s1 ++ c :: s2).length := by
      rw [h1]; exact findSub_single hn39
    have hsl := sl_of_drop h1
    have hfi : firstIdx illegalBasic (sl src (pos + 1) (pos + 1 + (s1 ++ c :: s2).length)) = some s1.length := by
      rw [hsl]; exact firstIdx_append (fun x hx => (hs1 x hx).2) hc
    have hgc : src.getD (pos + 1 + s1.length) 0 = c := by
      have : src.drop (pos + 1 + s1.length) = c :: (s2 ++ 39 :: rest) :=
        drop_add_of_drop (a := s1) (by simpa using h1)
      simp [List.getD, getElem?_of_drop this]
    have h34 : (some 39 == some 34) = false := by decide
    simp only [parseValue, hg, h34, hst, parseLiteralStr, skipUntil, hfind, hfi, hgc]
    simp [Except.map, bind, Except.bind]
  · intro cfg src pos fuel s hs hne h
    have hst : startsAt src pos [39, 39, 39] = false := by
      cases s with
      | nil => exact absurd rfl hne
      | cons x t =>
        have : x ≠ 39 := fun e => hs (by simp [e])
        unfold startsAt; rw [h]; simp [List.isPrefixOf, Ne.symm this]
    have hg := getElem?_of_drop h
    have h1 : src.drop (pos + 1) = s := by simpa using drop_succ_of_drop h
    have hfind : findSub [39] (src.drop (pos + 1)) = none := by rw [h1]; exact findSub_single_none hs
    have h34 : (some 39 == some 34) = false := by decide
    simp only [parseValue, hg, h34, hst, parseLiteralStr, skipUntil, hfind]
    simp [Except.map, bind, Except.bind]

end PyLean.TextLibs.Toml
