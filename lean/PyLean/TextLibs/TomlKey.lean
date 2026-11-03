import PyLean.TextLibs.TomlStr

/-!
Keys: `parse_key` and `parse_key_part` read back every dotted key TOML 1.1 allows, and the
`MAX_KEY_PARTS` limit.
-/

namespace PyLean.TextLibs.Toml

/-- One key part as written: bare, literal (`'…'`) or basic (`"…"`, with escapes). -/
inductive KPart where
  | bare (s : Str)
  | lit (s : Str)
  | basic (ps : List Piece)

def KPart.enc : KPart → Str
  | .bare s => s
  | .lit s => 39 :: s ++ [39]
  | .basic ps => 34 :: encAll ps ++ [34]

def KPart.val : KPart → Str
  | .bare s => s
  | .lit s => s
  | .basic ps => ps.map Piece.val

/-- TOML 1.1 "Keys": a bare key is non-empty and uses `A-Za-z0-9_-`; a quoted key follows the
rules of basic or literal strings. -/
def KPart.ok : KPart → Prop
  | .bare s => s ≠ [] ∧ ∀ c ∈ s, bareKey c = true
  | .lit s => ∀ c ∈ s, c ≠ 39 ∧ illegalBasic c = false
  | .basic ps => ∀ p ∈ ps, p.ok

/-- The text of one more part: `.`, whitespace, the part, whitespace. -/
def moreEnc (m : Str × KPart × Str) : Str := 46 :: m.1 ++ m.2.1.enc ++ m.2.2

def allWs (s : Str) : Prop := ∀ c ∈ s, tomlWs c = true

theorem KPart.head_not_ws {k : KPart} (hk : k.ok) : ∃ c t, k.enc = c :: t ∧ tomlWs c = false ∧ c ≠ 46 := by
  cases k with
  | bare s =>
    obtain ⟨hne, hall⟩ := hk
    cases s with
    | nil => exact absurd rfl hne
    | cons c t =>
      have := hall c (by simp)
      refine ⟨c, t, rfl, ?_, ?_⟩
      · revert this; simp [bareKey, tomlWs, inR]; omega
      · intro e; subst e; simp [bareKey, inR] at this
  | lit s => exact ⟨39, _, rfl, by decide, by decide⟩
  | basic ps => exact ⟨34, _, rfl, by decide, by decide⟩

theorem parseKeyPart_ok {src : Str} {pos : Nat} {k : KPart} {r : Str} (hk : k.ok)
    (h : src.drop pos = k.enc ++ r) (hr : ∀ c, r.head? = some c → bareKey c = false) :
    parseKeyPart src pos = .ok (pos + k.enc.length, k.val) := by
  cases k with
  | bare s =>
    obtain ⟨hne, hall⟩ := hk
    cases s with
    | nil => exact absurd rfl hne
    | cons c t =>
      have hg := getElem?_of_drop (r := t ++ r) (by simpa [KPart.enc] using h)
      have hb := hall c (by simp)
      have hsk := skipChars_of_drop (p := bareKey) h hall hr
      have hsl := sl_of_drop h
      simp only [KPart.enc, List.length_cons] at hsk hsl
      simp [parseKeyPart, hg, hb, hsk, hsl, KPart.enc, KPart.val]
  | lit s =>
    have hg := getElem?_of_drop (r := s ++ 39 :: r) (by simpa [KPart.enc] using h)
    have h1 : src.drop (pos + 1) = s ++ 39 :: r := by
      simpa using drop_succ_of_drop (c := 39) (r := s ++ 39 :: r) (by simpa [KPart.enc] using h)
    have hn39 : 39 ∉ s := fun m => (hk 39 m).1 rfl
    have hfind : findSub [39] (src.drop (pos + 1)) = some s.length := by rw [h1]; exact findSub_single hn39
    have hsl := sl_of_drop h1
    have hfi : firstIdx illegalBasic (sl src (pos + 1) (pos + 1 + s.length)) = none := by
      rw [hsl]; exact firstIdx_none (fun x hx => (hk x hx).2)
    have hb : bareKey 39 = false := by decide
    simp only [parseKeyPart, hg, hb, Bool.false_eq_true, ite_false, ite_true, parseLiteralStr, skipUntil,
      hfind, hfi, show (39 == 39) = true from rfl]
    simp [hsl, bind, Except.bind, pure, Except.pure, KPart.enc, KPart.val]; omega
  | basic ps =>
    have h0 : src.drop pos = 34 :: encAll ps ++ 34 :: r := by simpa [KPart.enc] using h
    have hg := getElem?_of_drop h0
    have h1 := drop_succ_of_drop h0
    have hlen : src.length = pos + 1 + (encAll ps).length + 1 + r.length := by
      have := congrArg List.length h0; simp at this; omega
    have hloop := basicStrLoop_pieces src r ps hk (src.length + 1) (pos + 1) (pos + 1) [] h1
      (Nat.le_refl _) (by omega)
    have hb : bareKey 34 = false := by decide
    simp only [parseKeyPart, hg, hb, Bool.false_eq_true, ite_false, ite_true, parseOneLineBasicStr,
      parseBasicStr, hloop, sl_self, show (34 == 39) = false from rfl, show (34 == 34) = true from rfl]
    simp [KPart.enc, KPart.val]; omega

theorem keyLoop_step {maxK : Nat} {src : Str} {f pos : Nat} {key : Key} (h : src[pos]? = some 46) :
    keyLoop maxK src (f + 1) pos key = (do
      let (p, part) ← parseKeyPart src (skipChars src (pos + 1) tomlWs)
      if (key ++ [part]).length > maxK then .error (.named "RecursionError" (keyPartsMsg maxK))
      else keyLoop maxK src f (skipChars src p tomlWs) (key ++ [part])) := by
  simp [keyLoop, h]

/-- The loop of `parse_key` over the remaining parts. -/
theorem keyLoop_spec (maxK : Nat) (src rest : Str)
    (hrest : ∀ c, rest.head? = some c → tomlWs c = false ∧ c ≠ 46 ∧ bareKey c = false) :
    ∀ (more : List (Str × KPart × Str)), (∀ m ∈ more, allWs m.1 ∧ m.2.1.ok ∧ allWs m.2.2) →
    ∀ (fuel pos : Nat) (key : Key), src.drop pos = more.flatMap moreEnc ++ rest → more.length < fuel →
    keyLoop maxK src fuel pos key =
      if key.length + more.length ≤ maxK ∨ more = [] then
        .ok (pos + (more.flatMap moreEnc).length, key ++ more.map (·.2.1.val))
      else .error (.named "RecursionError" (keyPartsMsg maxK))
  | [], _, fuel, pos, key, h, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hne : src[pos]? ≠ some 46 := by
      cases hr : rest with
      | nil => simp at h; rw [hr] at h; simp [getElem?_of_drop_nil h]
      | cons c t =>
        rw [hr] at h; simp at h
        rw [getElem?_of_drop h]; simpa using (hrest c (by simp [hr])).2.1
    simp [keyLoop, hne]
  | m :: ms, hok, fuel, pos, key, h, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    obtain ⟨hw1, hk, hw2⟩ := hok m (by simp)
    have hms : ∀ m ∈ ms, allWs m.1 ∧ m.2.1.ok ∧ allWs m.2.2 := fun x hx => hok x (by simp [hx])
    obtain ⟨c0, t0, he, hc0, hc46⟩ := KPart.head_not_ws hk
    have h0 : src.drop pos = 46 :: (m.1 ++ m.2.1.enc ++ m.2.2 ++ ms.flatMap moreEnc ++ rest) := by
      simpa [moreEnc] using h
    have hg := getElem?_of_drop h0
    have h1 : src.drop (pos + 1) = m.1 ++ (m.2.1.enc ++ m.2.2 ++ ms.flatMap moreEnc ++ rest) := by
      simpa using drop_succ_of_drop h0
    have hsk1 : skipChars src (pos + 1) tomlWs = pos + 1 + m.1.length :=
      skipChars_of_drop h1 hw1 (by intro c hc; rw [he] at hc; simp at hc; subst hc; exact hc0)
    have h2 : src.drop (pos + 1 + m.1.length) = m.2.1.enc ++ (m.2.2 ++ ms.flatMap moreEnc ++ rest) := by
      simpa using drop_add_of_drop h1
    -- what follows the part: whitespace, a dot, or `rest`
    have hnext : ∀ c, (m.2.2 ++ ms.flatMap moreEnc ++ rest).head? = some c →
        tomlWs c = true ∨ c = 46 ∨ (tomlWs c = false ∧ c ≠ 46 ∧ bareKey c = false) := by
      intro c hc
      cases hw : m.2.2 with
      | cons w _ => rw [hw] at hc; simp at hc; subst hc; exact Or.inl (hw2 _ (by simp [hw]))
      | nil =>
        rw [hw] at hc
        cases ms with
        | cons m' _ => simp [moreEnc] at hc; exact Or.inr (Or.inl hc.symm)
        | nil => exact Or.inr (Or.inr (hrest c (by simpa using hc)))
    have hpart := parseKeyPart_ok hk h2 (by
      intro c hc
      rcases hnext c hc with h | h | h
      · revert h; simp [tomlWs, bareKey, inR]; omega
      · subst h; decide
      · exact h.2.2)
    have h3 : src.drop (pos + 1 + m.1.length + m.2.1.enc.length) = m.2.2 ++ (ms.flatMap moreEnc ++ rest) := by
      simpa using drop_add_of_drop h2
    have hsk2 : skipChars src (pos + 1 + m.1.length + m.2.1.enc.length) tomlWs =
        pos + 1 + m.1.length + m.2.1.enc.length + m.2.2.length := by
      refine skipChars_of_drop h3 hw2 ?_
      intro c hc
      cases ms with
      | cons m' _ => simp [moreEnc] at hc; subst hc; decide
      | nil => exact (hrest c (by simpa using hc)).1
    have h4 : src.drop (pos + 1 + m.1.length + m.2.1.enc.length + m.2.2.length) = ms.flatMap moreEnc ++ rest := by
      simpa using drop_add_of_drop h3
    have ih := keyLoop_spec maxK src rest hrest ms hms f _ (key ++ [m.2.1.val]) h4 (by simp at hf; omega)
    rw [keyLoop_step hg, hsk1, hpart]
    simp only [bind, Except.bind]
    by_cases hx : (key ++ [m.2.1.val]).length > maxK
    · rw [if_pos hx]
      have : ¬ (key.length + (m :: ms).length ≤ maxK ∨ m :: ms = []) := by simp at hx ⊢; omega
      rw [if_neg this]
    · rw [if_neg hx, hsk2, ih]
      have hx' : key.length + 1 ≤ maxK := by
        simp only [List.length_append, List.length_singleton] at hx; omega
      by_cases hc : key.length + (m :: ms).length ≤ maxK
      · have : (key ++ [m.2.1.val]).length + ms.length ≤ maxK := by
          simp only [List.length_cons] at hc
          simp only [List.length_append, List.length_singleton]; omega
        rw [if_pos (Or.inl this), if_pos (Or.inl hc)]
        simp [moreEnc]; omega
      · by_cases hms0 : ms = []
        · subst hms0; simp only [List.length_cons, List.length_nil] at hc; omega
        · have : ¬ ((key ++ [m.2.1.val]).length + ms.length ≤ maxK ∨ ms = []) := by
            simp only [List.length_cons] at hc
            simp only [List.length_append, List.length_singleton, not_or]; exact ⟨by omega, hms0⟩
          rw [if_neg this, if_neg (not_or.mpr ⟨hc, by simp⟩)]

/-- Keys, TOML 1.1 "Keys": for every dotted key whose parts are each bare, literal or basic
(with any escapes), with spaces or tabs around the dots and after the key, `parse_key` returns
the parts and the position after the trailing whitespace, when the key has at most
`MAX_KEY_PARTS` parts or only one; a key with more parts raises `RecursionError` (the single
first part is never checked against the limit). The text after the key must not continue it:
it does not start with whitespace, `.` or a bare-key character. -/
def KeySpec : Prop :=
  ∀ (maxK : Nat) (src : Str) (pos : Nat) (p0 : KPart) (ws0 : Str) (more : List (Str × KPart × Str))
    (rest : Str),
    p0.ok → allWs ws0 → (∀ m ∈ more, allWs m.1 ∧ m.2.1.ok ∧ allWs m.2.2) →
    (∀ c, rest.head? = some c → tomlWs c = false ∧ c ≠ 46 ∧ bareKey c = false) →
    src.drop pos = p0.enc ++ ws0 ++ more.flatMap moreEnc ++ rest →
    parseKey maxK src pos =
      if more.length + 1 ≤ maxK ∨ more = [] then
        .ok (pos + (p0.enc ++ ws0 ++ more.flatMap moreEnc).length, p0.val :: more.map (·.2.1.val))
      else .error (.named "RecursionError" (keyPartsMsg maxK))

theorem keySpec_proven : KeySpec := by
  intro maxK src pos p0 ws0 more rest hp0 hws0 hmore hrest h
  have hnext : ∀ c, (ws0 ++ more.flatMap moreEnc ++ rest).head? = some c → bareKey c = false := by
    intro c hc
    cases hw : ws0 with
    | cons w _ =>
      rw [hw] at hc; simp at hc; subst hc
      have := hws0 w (by simp [hw]); revert this; simp [tomlWs, bareKey, inR]; omega
    | nil =>
      rw [hw] at hc
      cases more with
      | cons m _ => simp [moreEnc] at hc; subst hc; decide
      | nil => exact (hrest c (by simpa using hc)).2.2
  have hpart := parseKeyPart_ok hp0 (r := ws0 ++ more.flatMap moreEnc ++ rest) (by simpa using h) hnext
  have h1 : src.drop (pos + p0.enc.length) = ws0 ++ (more.flatMap moreEnc ++ rest) := by
    simpa using drop_add_of_drop (a := p0.enc) (by simpa using h)
  have hsk : skipChars src (pos + p0.enc.length) tomlWs = pos + p0.enc.length + ws0.length := by
    refine skipChars_of_drop h1 hws0 ?_
    intro c hc
    cases more with
    | cons m _ => simp [moreEnc] at hc; subst hc; decide
    | nil => exact (hrest c (by simpa using hc)).1
  have h2 : src.drop (pos + p0.enc.length + ws0.length) = more.flatMap moreEnc ++ rest := by
    simpa using drop_add_of_drop h1
  have hlen : more.length < src.length + 1 := by
    have hl := congrArg List.length h
    have : more.length ≤ (more.flatMap moreEnc).length := by
      clear h hl hmore h2 h1 hsk hpart hnext
      induction more with
      | nil => simp
      | cons m ms ih => simp [moreEnc] at ih ⊢; omega
    rw [List.length_drop] at hl; simp only [List.length_append] at hl; omega
  have hloop := keyLoop_spec maxK src rest hrest more hmore (src.length + 1) _ [p0.val] h2 hlen
  simp only [parseKey, hpart, bind, Except.bind, hsk, hloop]
  simp only [List.length_singleton, Nat.add_comm 1 more.length, List.singleton_append]
  split <;> simp <;> omega

end PyLean.TextLibs.Toml
