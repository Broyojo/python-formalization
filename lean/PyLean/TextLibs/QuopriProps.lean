import PyLean.TextLibs.QuopriModel

/-!
`quopri`: its two bodies against each other, and the round trip of the body every build takes.
-/

namespace PyLean.TextLibs.Quopri

open PyLean PyLean.TextLibs.Binascii

/-- `encode` then `decode` on files, the body every build takes, for all bytes and both flags: one write
each, and the data comes back. Precondition: no `\r\n` in the data, the case `QpRoundTrip` refutes. -/
def FileRoundTrip : Prop :=
  ∀ (d : List Nat) (q h : Bool) (f g : FileSim), (∀ x ∈ d, x < 256) → noCL d = true →
    f.writes = [] → g.writes = [] →
    (encodeC (.ok d) f q h).2 = .ok () ∧
    (encodeC (.ok d) f q h).1.written = f.written ++ [b2aQp d ⟨q, true, h⟩] ∧
    (decodeC (.ok (b2aQp d ⟨q, true, h⟩)) g h).2 = .ok () ∧
    (decodeC (.ok (b2aQp d ⟨q, true, h⟩)) g h).1.written = g.written ++ [d]

theorem fileRoundTrip_proven : FileRoundTrip := by
  intro d q h f g hb hn hf hg
  have ht := qpRoundTripNarrow_proven d ⟨q, true, h⟩ hb (.inr hn)
  simp only at ht
  simp only [encodeC, decodeC, ht, FileSim.write, hf, hg, and_self]

/-- `encode` and `decode`, the body every build takes: an `input.read` that raises passes through with
nothing written, and a write that raises passes through after that one write. -/
def FileFailures : Prop :=
  ∀ (d : List Nat) (e w : PyExc) (rest : List (Py Unit)) (f : FileSim) (q h : Bool),
    encodeC (.error e) f q h = (f, .error e) ∧ decodeC (.error e) f h = (f, .error e) ∧
    (f.writes = .error w :: rest →
      (encodeC (.ok d) f q h).2 = .error w ∧
      (encodeC (.ok d) f q h).1.written = f.written ++ [b2aQp d ⟨q, true, h⟩] ∧
      (decodeC (.ok d) f h).2 = .error w)

theorem fileFailures_proven : FileFailures := by
  intro d e w rest f q h
  refine ⟨rfl, rfl, ?_⟩
  intro hw
  have ha : ∃ o, a2bQp (.bytes d) h = .ok o := ⟨_, rfl⟩
  obtain ⟨o, ho⟩ := ha
  simp [encodeC, decodeC, ho, FileSim.write, hw]

/-- In the middle of a line, `needsquoting` and the condition in `b2a_qp` quote the same bytes, whatever
the column, in text mode. The line break bytes are outside `needsquoting`'s job. -/
def QuoteSetTwin : Prop :=
  ∀ (c ll : Nat) (q h : Bool), c < 256 → c ≠ 10 → c ≠ 13 →
    qpMustEncode ⟨q, true, h⟩ ll c (some 97) = needsQuoting c q h

theorem quoteSetTwin_proven : QuoteSetTwin := by
  have key : ∀ c, c < 256 → ∀ q h z : Bool, c ≠ 10 → c ≠ 13 →
      (decide (c > 126) || c == 61 || (h && c == 95) ||
        (c == 46 && z && (some 97 == none || some 97 == some 10 || some 97 == some 13 || some 97 == some 0)) ||
        (!true && (c == 13 || c == 10)) || ((c == 9 || c == 32) && some 97 == none) ||
        (decide (c < 33) && c != 13 && c != 10 && (q || (c != 9 && c != 32)))) = needsQuoting c q h := by
    decide +kernel
  intro c ll q h hc h1 h2
  exact key c hc q h (ll == 0) h1 h2

/-- The pure-Python decoder undoes `quote`, for every byte, reading `=XY` through `ishex` and `unhex`. -/
def QuoteDecodes : Prop :=
  ∀ (c : Nat) (h : Bool), c < 256 → decodestringPy (quote c) h = [c]

theorem quoteDecodes_proven : QuoteDecodes := by
  have key : ∀ c, c < 256 → ∀ h : Bool, decodestringPy (quote c) h = [c] := by decide +kernel
  intro c h hc
  exact key c hc h

/-- `encodestring`'s two bodies agree. False: at the end of a line, among other differences. -/
def EncodeTwin : Prop :=
  ∀ (s : List Nat) (q h : Bool), encodestringC s q h = encodestringPy s q h

theorem encodeTwin_refuted : ¬EncodeTwin := by
  intro h
  have := h [32] false true
  revert this
  decide +kernel

/-- `decodestring`'s two bodies agree. False, on a lone `=` and on trailing whitespace. -/
def DecodeTwin : Prop :=
  ∀ (s : List Nat) (h : Bool), a2bQp (.bytes s) h = .ok (decodestringPy s h)

theorem decodeTwin_refuted : ¬DecodeTwin := by
  intro h
  have := h [97, 32, 10] false
  revert this
  decide +kernel

/-- The pure-Python body round-trips. False: the soft break can fall inside an `=XY`. -/
def PyRoundTrip : Prop :=
  ∀ (s : List Nat) (q h : Bool), (∀ x ∈ s, x < 256) → decodestringPy (encodestringPy s q h) h = s

theorem pyRoundTrip_refuted : ¬PyRoundTrip := by
  intro h
  have := h (List.replicate 74 97 ++ [255]) false false (by decide +kernel)
  revert this
  decide +kernel

end PyLean.TextLibs.Quopri
