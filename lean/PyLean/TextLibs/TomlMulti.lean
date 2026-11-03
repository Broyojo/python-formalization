import PyLean.TextLibs.TomlKey

/-!
Multi-line strings: `parse_multiline_str` and `parse_basic_str_escape_multiline`.
-/

namespace PyLean.TextLibs.Toml

/-- A piece of a multi-line basic string: a character (raw newlines allowed) or a line-ending
backslash `\`, spaces or tabs, a newline, then whitespace and newlines, which give nothing. -/
inductive MPiece where
  | p (x : Piece)
  | cont (ws1 ws2 : Str)

def MPiece.enc : MPiece → Str
  | .p x => x.enc
  | .cont ws1 ws2 => 92 :: ws1 ++ 10 :: ws2

def MPiece.vals : MPiece → Str
  | .p x => [x.val]
  | .cont _ _ => []

/-- TOML 1.1 multi-line basic strings: raw characters other than `"`, `\` and control characters
other than tab and newline; the escapes of basic strings; line-ending backslashes. -/
def MPiece.ok : MPiece → Prop
  | .p (.raw c) => c ≠ 34 ∧ c ≠ 92 ∧ illegalMl c = false
  | .p x => x.ok
  | .cont ws1 ws2 => allWs ws1 ∧ ∀ c ∈ ws2, tomlWsNl c = true

/-- Whether the piece starts with whitespace or a newline (a line-ending backslash would eat it). -/
def MPiece.wsHead : MPiece → Bool
  | .p (.raw c) => tomlWsNl c
  | _ => false

def MPiece.isCont : MPiece → Bool
  | .cont _ _ => true
  | _ => false

def mOk : List MPiece → Prop
  | [] => True
  | [m] => m.ok
  | m :: m' :: ms => m.ok ∧ (m.isCont = true → m'.wsHead = false) ∧ mOk (m' :: ms)

def encM (ms : List MPiece) : Str := ms.flatMap MPiece.enc
def valsM (ms : List MPiece) : Str := ms.flatMap MPiece.vals

theorem mOk_head {m : MPiece} {ms : List MPiece} (h : mOk (m :: ms)) : m.ok := by
  cases ms with
  | nil => exact h
  | cons _ _ => exact h.1

theorem mOk_tail {m : MPiece} {ms : List MPiece} (h : mOk (m :: ms)) : mOk ms := by
  cases ms with
  | nil => trivial
  | cons _ _ => exact h.2.2

theorem mpiece_enc_ne (m : MPiece) : m.enc ≠ [] := by
  cases m with
  | p x => exact piece_enc_ne_nil x
  | cont _ _ => simp [MPiece.enc]

/-- What follows a piece: the next piece, or the closing quotes. After a line-ending backslash it
is not whitespace or a newline. -/
theorem next_after_cont {ms : List MPiece} (q rest : Str) (hq : q = [] ∨ q = [34] ∨ q = [34, 34])
    (hok : ∀ m', ms.head? = some m' → m'.wsHead = false) (hms : mOk ms) :
    ∀ c, (encM ms ++ q ++ [34, 34, 34] ++ rest).head? = some c → tomlWsNl c = false := by
  intro c hc
  cases ms with
  | nil =>
    rcases hq with rfl | rfl | rfl <;> simp [encM] at hc <;> subst hc <;> decide
  | cons m ms' =>
    have hw := hok m rfl
    have hm := mOk_head hms
    cases m with
    | p x =>
      cases x with
      | raw c' => simp [encM, MPiece.enc, Piece.enc] at hc; subst hc; simpa [MPiece.wsHead] using hw
      | short c' => simp [encM, MPiece.enc, Piece.enc] at hc; subst hc; decide
      | x c' up => simp [encM, MPiece.enc, Piece.enc] at hc; subst hc; decide
      | u c' up => simp [encM, MPiece.enc, Piece.enc] at hc; subst hc; decide
      | U c' up => simp [encM, MPiece.enc, Piece.enc] at hc; subst hc; decide
    | cont _ _ => simp [encM, MPiece.enc] at hc; subst hc; decide

theorem startsAt_quotes {src : Str} {pos : Nat} {q rest : Str} (hq : q = [] ∨ q = [34] ∨ q = [34, 34])
    (h : src.drop pos = q ++ [34, 34, 34] ++ rest) : startsAt src pos [34, 34, 34] = true := by
  rcases hq with rfl | rfl | rfl
  · exact startsAt_of_drop (r := rest) (by simpa using h)
  · exact startsAt_of_drop (r := 34 :: rest) (by simpa using h)
  · exact startsAt_of_drop (r := 34 :: 34 :: rest) (by simpa using h)

/-- The loop of `parse_basic_str` (multi-line) over pieces, up to the closing quotes. -/
theorem mlLoop (src q rest : Str) (hq : q = [] ∨ q = [34] ∨ q = [34, 34]) :
    ∀ (ms : List MPiece), mOk ms → ∀ (fuel pos start : Nat) (res : Str),
    src.drop pos = encM ms ++ q ++ [34, 34, 34] ++ rest → start ≤ pos → (encM ms).length < fuel →
    basicStrLoop src true fuel pos start res = .ok (pos + (encM ms).length + 3, res ++ sl src start pos ++ valsM ms)
  | [], _, fuel, pos, start, res, h, _, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [encM] at hf; omega⟩
    have hst := startsAt_quotes hq (by simpa [encM] using h)
    have hg : src[pos]? = some 34 := by
      rcases hq with rfl | rfl | rfl <;> exact getElem?_of_drop (by simpa [encM] using h)
    simp [basicStrLoop, hg, hst, encM, valsM]
  | m :: ms, hok, fuel, pos, start, res, h, hs, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [encM] at hf; omega⟩
    have hm := mOk_head hok
    have hms := mOk_tail hok
    have hlen : (encM (m :: ms)).length = m.enc.length + (encM ms).length := by simp [encM]
    have hpos := List.length_pos_iff.mpr (mpiece_enc_ne m)
    have h' : src.drop pos = m.enc ++ (encM ms ++ q ++ [34, 34, 34] ++ rest) := by simpa [encM] using h
    have hd := drop_add_of_drop h'
    cases m with
    | p x =>
      by_cases hr : ∃ c, x = .raw c
      · obtain ⟨c, rfl⟩ := hr
        obtain ⟨h34, h92, hill⟩ := hm
        have h1 : src.drop pos = c :: (encM ms ++ q ++ [34, 34, 34] ++ rest) := by simpa [MPiece.enc, Piece.enc] using h'
        have hg := getElem?_of_drop h1
        have ih := mlLoop src q rest hq ms hms f (pos + 1) start res (drop_succ_of_drop h1) (by omega)
          (by simp [MPiece.enc, Piece.enc] at hlen; omega)
        have hsn := sl_snoc hs h1
        simp only [basicStrLoop, hg, beq_iff_eq, h34, h92, ite_false, Bool.not_true, Bool.false_eq_true, hill, ih,
          hsn, ite_true]
        simp [hlen, MPiece.enc, MPiece.vals, Piece.enc, Piece.val, valsM]; omega
      · have hraw : ∀ c, x ≠ .raw c := fun c e => hr ⟨c, e⟩
        have hxo : x.ok := by cases x <;> first | exact absurd rfl (hraw _) | exact hm
        have hesc := parseEscape_piece hxo hraw (by simpa [MPiece.enc] using h') true
        obtain ⟨t, ht⟩ : ∃ t, x.enc = 92 :: t := by
          cases x with
          | raw c => exact absurd rfl (hraw c)
          | _ => exact ⟨_, rfl⟩
        have hg : src[pos]? = some 92 := getElem?_of_drop (r := t ++ (encM ms ++ q ++ [34, 34, 34] ++ rest))
          (by rw [h']; simp [MPiece.enc, ht])
        have ih := mlLoop src q rest hq ms hms f _ _ (res ++ sl src start pos ++ [x.val]) (by simpa [MPiece.enc] using hd)
          (Nat.le_refl _) (by simp [MPiece.enc] at hlen hpos; omega)
        simp only [basicStrLoop, hg]
        simp only [show (92 == 34) = false from rfl, show (92 == 92) = true from rfl, Bool.false_eq_true,
          ite_false, ite_true, parseBasicStrEscapeMl, hesc, bind, Except.bind]
        rw [ih]
        have hxe : (MPiece.p x).enc.length = x.enc.length := rfl
        simp [hlen, sl_self, MPiece.vals, valsM]; omega
    | cont ws1 ws2 =>
      obtain ⟨hw1, hw2⟩ := hm
      have hnext := next_after_cont (ms := ms) q rest hq
        (fun m' hm' => by
          cases ms with
          | nil => simp at hm'
          | cons m2 ms2 => simp at hm'; subst hm'; exact hok.2.1 rfl) hms
      have h2 : src.drop pos = 92 :: (ws1 ++ 10 :: ws2 ++ (encM ms ++ q ++ [34, 34, 34] ++ rest)) := by
        simpa [MPiece.enc] using h'
      have hg := getElem?_of_drop h2
      have hd1 : src.drop (pos + 1) = ws1 ++ 10 :: ws2 ++ (encM ms ++ q ++ [34, 34, 34] ++ rest) := drop_succ_of_drop h2
      -- the escape: skip `ws1`, the newline, then `ws2`
      have hesc : parseBasicStrEscape src pos true =
          .ok (pos + (MPiece.cont ws1 ws2).enc.length, []) := by
        have hws2 : ∀ x ∈ ws2, tomlWsNl x = true := hw2
        cases ws1 with
        | nil =>
          have hsl : sl src pos (pos + 2) = [92, 10] := sl_of_drop (a := [92, 10]) (by simpa using h2)
          have hd2 : src.drop (pos + 2) = ws2 ++ (encM ms ++ q ++ [34, 34, 34] ++ rest) := by
            simpa using drop_add_of_drop (a := [92, 10]) (by simpa using h2)
          have hsk := skipChars_of_drop hd2 hws2 hnext
          simp [parseBasicStrEscape, hsl, hsk, MPiece.enc] <;> omega
        | cons w ws1' =>
          have hw : w = 32 ∨ w = 9 := by
            have := hw1 w (by simp); revert this; simp [tomlWs] <;> omega
          have hsl : sl src pos (pos + 2) = [92, w] := sl_of_drop (a := [92, w]) (by simpa using h2)
          have hd2 : src.drop (pos + 2) = ws1' ++ (10 :: (ws2 ++ (encM ms ++ q ++ [34, 34, 34] ++ rest))) := by
            simpa using drop_add_of_drop (a := [92, w]) (by simpa using h2)
          have hsk1 : skipChars src (pos + 2) tomlWs = pos + 2 + ws1'.length :=
            skipChars_of_drop hd2 (fun x hx => hw1 x (by simp [hx])) (by intro c hc; simp at hc; subst hc; decide)
          have hd3 : src.drop (pos + 2 + ws1'.length) = 10 :: (ws2 ++ (encM ms ++ q ++ [34, 34, 34] ++ rest)) :=
            drop_add_of_drop hd2
          have hg3 := getElem?_of_drop hd3
          have hd4 : src.drop (pos + 2 + ws1'.length + 1) = ws2 ++ (encM ms ++ q ++ [34, 34, 34] ++ rest) :=
            drop_succ_of_drop hd3
          have hsk2 := skipChars_of_drop hd4 hws2 hnext
          rcases hw with rfl | rfl <;>
            simp [parseBasicStrEscape, hsl, hsk1, hg3, hsk2, MPiece.enc] <;> omega
      have ih := mlLoop src q rest hq ms hms f _ _ (res ++ sl src start pos ++ []) hd
        (Nat.le_refl _) (by simp [MPiece.enc] at hlen ⊢; omega)
      simp only [basicStrLoop, hg]
      simp only [show (92 == 34) = false from rfl, show (92 == 92) = true from rfl, Bool.false_eq_true,
        ite_false, ite_true, parseBasicStrEscapeMl, hesc, bind, Except.bind]
      rw [ih]
      simp [hlen, sl_self, MPiece.vals, valsM]; omega

/-- Multi-line basic strings, TOML 1.1 "String": for every list of pieces (characters written raw,
newlines included, or with any escape basic strings allow; line-ending backslashes, which trim the
newline and the whitespace after them), optionally preceded by a newline right after the opening
`"""` (trimmed), and followed by up to two `"` before the closing `"""` (kept), `parse_value`
returns the text and the position after the closing quotes. -/
def MultilineBasicSpec : Prop :=
  ∀ (cfg : Cfg) (src : Str) (pos fuel : Nat) (ms : List MPiece) (nl q rest : Str),
    mOk ms → (nl = [] ∨ nl = [10]) → (q = [] ∨ q = [34] ∨ q = [34, 34]) →
    (nl = [] → ∀ c, (encM ms ++ q).head? = some c → c ≠ 10) → (∀ c, rest.head? = some c → c ≠ 34) →
    src.drop pos = [34, 34, 34] ++ nl ++ encM ms ++ q ++ [34, 34, 34] ++ rest →
    parseValue cfg src (fuel + 1) pos =
      .ok (pos + 6 + nl.length + (encM ms).length + q.length, .str (valsM ms ++ q))

theorem multilineBasicSpec_proven : MultilineBasicSpec := by
  intro cfg src pos fuel ms nl q rest hms hnl hq hhead hrest h
  have hg : src[pos]? = some 34 := getElem?_of_drop (r := [34, 34] ++ nl ++ encM ms ++ q ++ [34, 34, 34] ++ rest)
    (by rw [h]; simp)
  have hst3 : startsAt src pos [34, 34, 34] = true :=
    startsAt_of_drop (r := nl ++ encM ms ++ q ++ [34, 34, 34] ++ rest) (by rw [h]; simp)
  have hd3 : src.drop (pos + 3) = nl ++ (encM ms ++ q ++ [34, 34, 34] ++ rest) := by
    simpa using drop_add_of_drop (a := [34, 34, 34]) (by rw [h]; simp)
  -- the newline right after the opening quotes
  obtain ⟨p, hp, hpp, hdp⟩ : ∃ p, (if startsAt src (pos + 3) [10] = true then pos + 3 + 1 else pos + 3) = p ∧
      p = pos + 3 + nl.length ∧ src.drop p = encM ms ++ q ++ [34, 34, 34] ++ rest := by
    rcases hnl with rfl | rfl
    · have hns : startsAt src (pos + 3) [10] = false := by
        have hd' : src.drop (pos + 3) = encM ms ++ q ++ [34, 34, 34] ++ rest := by simpa using hd3
        unfold startsAt; rw [hd']
        cases hx : encM ms ++ q with
        | nil => simp [List.isPrefixOf]
        | cons c t =>
          have := hhead rfl c (by simp [hx])
          simp [List.isPrefixOf, Ne.symm this]
      exact ⟨pos + 3, by simp [hns], by simp, by simpa using hd3⟩
    · have hys : startsAt src (pos + 3) [10] = true := startsAt_of_drop (by simpa using hd3)
      exact ⟨pos + 3 + 1, by simp [hys], by simp, by simpa using drop_succ_of_drop (c := 10) (by simpa using hd3)⟩
  have hlen : (encM ms).length < src.length + 1 := by
    have := congrArg List.length h; simp at this; omega
  have hloop := mlLoop src q rest hq ms hms (src.length + 1) p p [] hdp (Nat.le_refl _) hlen
  -- after the closing quotes: the extra quotes of `q`, then `rest`
  have hdq : src.drop (p + (encM ms).length + 3) = q ++ rest := by
    have := drop_add_of_drop (a := encM ms ++ [34, 34, 34]) (r := q ++ rest) (by
      rw [hdp]; rcases hq with rfl | rfl | rfl <;> simp)
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    rw [show p + (encM ms).length + 3 = p + ((encM ms).length + (0 + 1 + 1 + 1)) by omega]
    exact this
  simp only [parseValue, hg, show (some 34 == some 34) = true from rfl, ite_true, hst3, parseMultilineStr, hp,
    Bool.false_eq_true, ite_false, parseBasicStr, hloop, bind, Except.bind, pure, Except.pure, sl_self,
    List.nil_append, Except.map]
  rcases hq with rfl | rfl | rfl
  · have h1 : startsAt src (p + (encM ms).length + 3) [34] = false := by
      unfold startsAt; rw [hdq]
      cases rest with
      | nil => rfl
      | cons c r => have := hrest c rfl; simp [List.isPrefixOf, Ne.symm this]
    simp [h1, hdp]; omega
  · have h1 : startsAt src (p + (encM ms).length + 3) [34] = true := startsAt_of_drop (by simpa using hdq)
    have h2 : startsAt src (p + (encM ms).length + 3 + 1) [34] = false := by
      unfold startsAt; rw [drop_succ_of_drop (by simpa using hdq)]
      cases rest with
      | nil => rfl
      | cons c r => have := hrest c rfl; simp [List.isPrefixOf, Ne.symm this]
    simp [h1, h2]; omega
  · have h1 : startsAt src (p + (encM ms).length + 3) [34] = true := startsAt_of_drop (by simpa using hdq)
    have hd1 : src.drop (p + (encM ms).length + 3 + 1) = 34 :: rest := drop_succ_of_drop (by simpa using hdq)
    have h2 : startsAt src (p + (encM ms).length + 3 + 1) [34] = true := startsAt_of_drop (by simpa using hd1)
    simp [h1, h2]; omega

end PyLean.TextLibs.Toml
