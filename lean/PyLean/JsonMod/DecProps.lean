import PyLean.JsonMod.DecTwins

/-!
C (`_json`) and pure-Python decoders: layered agreement properties.

* exact agreement of `json.loads`: refuted (error messages for control
  characters and invalid escapes);
* agreement up to the message text (same exception class, `pos`, `lineno`,
  `colno`): refuted (an invalid escape is reported one character apart);
* agreement up to exactly those two differences: proven;
* `raw_decode(s, idx)` for every int `idx`: refuted (negative `idx`);
* `raw_decode(s, idx)` for `0 <= idx <= sys.maxsize`: proven.

`lineno` and `colno` are computed from `(doc, pos)` by the shared
`JSONDecodeError.__init__` (`lineCol`), so equal `msg` and `pos` give equal
exceptions.
-/

namespace PyLean.JsonMod

open PyLean

/-- Python and C outcomes are equal, or differ only in the two known ways: an
`"Invalid control character at"` error (C) reported by Python with the
character's `repr` at the same position, or an `"Invalid \\escape"` error
reported by C at the backslash `q` and by Python at `q + 1` with the
character's `repr`. -/
def ScanTwin {α : Type} (s : PStr) (py c : DR α) : Prop :=
  py = c ∨
  (∃ (q : Nat) (ch : Nat), s[q]? = some ch ∧ ch < 32 ∧
    c = .error (.jde "Invalid control character at" q) ∧ py = .error (.jde (ctrlMsgPy ch) q)) ∨
  (∃ (q : Nat) (ch : Nat), s[q]? = some 92 ∧ s[q + 1]? = some ch ∧
    c = .error (.jde "Invalid \\escape" q) ∧ py = .error (.jde (escMsgPy ch) ((q : Int) + 1)))

/-- Same outcome, or `JSONDecodeError`s at the same position (so with the same
`pos`, `lineno` and `colno`), whatever their messages. -/
def SamePos {α : Type} (a b : DR α) : Prop :=
  a = b ∨ ∃ m1 m2 p, a = .error (.jde m1 p) ∧ b = .error (.jde m2 p)

theorem raw_nat_twin (cfg : DCfg) (s : PStr) (idx : Nat) (h : (idx : Int) ≤ ssizeMax) :
    ScanTwin s (rawDecodePy cfg s (idx : Int)) (rawDecodeC cfg s (idx : Int)) := by
  have hr : ¬ ((idx : Int) < ssizeMin ∨ (idx : Int) > ssizeMax) := by
    simp only [ssizeMin, ssizeMax] at h ⊢; omega
  have hn : ¬ ((idx : Int) < 0) := by omega
  simp only [rawDecodeC, hr, hn, ↓reduceIte, Int.toNat_natCast, rawDecodePy]
  rcases (sim cfg s (docFuel s)).1 idx with ⟨v, k, _, h1, h2⟩ | ⟨pe, ce, h1, h2, he⟩
  · rw [h1, h2]; exact Or.inl rfl
  · rw [h1, h2]
    rcases he with rfl | ⟨i, rfl, rfl⟩ | ⟨q, ch, hq, hch, rfl, rfl⟩ | ⟨q, ch, hq, hq1, rfl, rfl⟩
    · left; cases pe <;> rfl
    · left; rfl
    · right; left; exact ⟨q, ch, hq, hch, rfl, rfl⟩
    · right; right; exact ⟨q, ch, hq, hq1, rfl, rfl⟩

/-- `JSONDecoder.raw_decode(s, idx)`: for every `idx` the C scanner and the
pure-Python scanner agree up to `ScanTwin`. -/
def RawDecodeTwins : Prop :=
  ∀ (cfg : DCfg) (s : PStr) (idx : Int), ScanTwin s (rawDecodePy cfg s idx) (rawDecodeC cfg s idx)

/-- `raw_decode('12', -1)` is `(12, 2)` in pure Python (`string[-1]` is `'2'`,
then `NUMBER_RE.match(string, -1)` matches from index 0), and `ValueError:
idx cannot be negative` in C. -/
theorem rawDecodeTwins_refuted : ¬RawDecodeTwins := by
  intro h
  have h1 := h {} (cs "12") (-1)
  have e1 : rawDecodePy {} (cs "12") (-1) = .ok (.int 12, 2) := by decide
  have e2 : rawDecodeC {} (cs "12") (-1) = .error (.exc (.valueError "idx cannot be negative")) := by decide
  rw [e1, e2] at h1
  rcases h1 with h1 | ⟨_, _, _, _, h1, _⟩ | ⟨_, _, _, _, h1, _⟩ <;> cases h1

/-- For `0 <= idx <= sys.maxsize`, `raw_decode(s, idx)` agrees between the twins
up to `ScanTwin`. The bounds are exactly the refuted cases (negative `idx`;
`idx > sys.maxsize`, where C raises `OverflowError`). -/
def RawDecodeTwinsInRange : Prop :=
  ∀ (cfg : DCfg) (s : PStr) (idx : Int), 0 ≤ idx → idx ≤ ssizeMax →
    ScanTwin s (rawDecodePy cfg s idx) (rawDecodeC cfg s idx)

theorem rawDecodeTwinsInRange_proven : RawDecodeTwinsInRange := by
  intro cfg s idx h0 h1
  obtain ⟨n, rfl⟩ : ∃ n : Nat, idx = n := ⟨idx.toNat, by omega⟩
  exact raw_nat_twin cfg s n h1

/-- `json.loads(s)`: the C and pure-Python decoders return the same value or
raise the same exception (class and message). -/
def LoadsTwins : Prop := ∀ (cfg : DCfg) (s : PStr), loadsPy cfg s = loadsC cfg s

/-- `json.loads('"\x01"')`: C says `Invalid control character at: line 1
column 2 (char 1)`, Python `Invalid control character '\x01' at: ...`. -/
theorem loadsTwins_refuted : ¬LoadsTwins := by
  intro h
  have h1 := h {} [34, 1, 34]
  have e1 : loadsPy {} [34, 1, 34] = .error (.jde "Invalid control character '\\x01' at" 1) := by decide
  have e2 : loadsC {} [34, 1, 34] = .error (.jde "Invalid control character at" 1) := by decide
  rw [e1, e2] at h1
  exact absurd h1 (by decide)

/-- `json.loads(s)`: the twins agree up to the text of the `JSONDecodeError`
message: same value, or `JSONDecodeError` at the same `pos` (hence `lineno`,
`colno`) in both. -/
def LoadsTwinsPos : Prop := ∀ (cfg : DCfg) (s : PStr), SamePos (loadsPy cfg s) (loadsC cfg s)

/-- `json.loads('"\\x"')`: C reports `Invalid \escape` at the backslash (char 1),
Python `Invalid \escape: 'x'` at the `x` (char 2). -/
theorem loadsTwinsPos_refuted : ¬LoadsTwinsPos := by
  intro h
  have h1 := h {} (cs "\"\\x\"")
  have e1 : loadsPy {} (cs "\"\\x\"") = .error (.jde "Invalid \\escape: 'x'" 2) := by decide
  have e2 : loadsC {} (cs "\"\\x\"") = .error (.jde "Invalid \\escape" 1) := by decide
  rw [e1, e2] at h1
  rcases h1 with h1 | ⟨m1, m2, p, h1, h2⟩
  · exact absurd h1 (by decide)
  · simp only [Except.error.injEq, DErr.jde.injEq] at h1 h2
    omega

/-- `json.loads(s)` agrees between the twins except for exactly the two message
differences of `ScanTwin`, for every document and every combination of
`strict`, `object_pairs_hook` and `parse_int` (type invariant:
`len(s) <= sys.maxsize`). -/
def LoadsTwinsScan : Prop :=
  ∀ (cfg : DCfg) (s : PStr), (s.length : Int) ≤ ssizeMax → ScanTwin s (loadsPy cfg s) (loadsC cfg s)

theorem loadsTwinsScan_proven : LoadsTwinsScan := by
  intro cfg s hs
  have hw : ((wsEnd s 0 : Nat) : Int) ≤ ssizeMax := by
    have := wsEnd_le (s := s) (i := 0) (by omega); omega
  have := raw_nat_twin cfg s (wsEnd s 0) hw
  unfold loadsPy loadsC decodeWith
  rcases this with h | ⟨q, ch, hq, hch, h1, h2⟩ | ⟨q, ch, hq, hq1, h1, h2⟩
  · rw [h]; exact Or.inl rfl
  · rw [h1, h2]; exact Or.inr (Or.inl ⟨q, ch, hq, hch, rfl, rfl⟩)
  · rw [h1, h2]; exact Or.inr (Or.inr ⟨q, ch, hq, hq1, rfl, rfl⟩)

end PyLean.JsonMod
