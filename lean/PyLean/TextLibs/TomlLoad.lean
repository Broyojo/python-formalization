import PyLean.TextLibs.TomlModel
import PyLean.UnicodeObj.CodecProps

/-!
`load`, _parser.py:139-148: a binary file is `loads` of its UTF-8 text.
-/

namespace PyLean.TextLibs.Toml

open PyLean.UnicodeObj

/-- `load(fp)`: for every text of Unicode scalar values, a binary file holding its UTF-8
encoding loads exactly as `loads` of the text; bytes that are not UTF-8 raise the decoder's
`UnicodeDecodeError`; a file opened in text mode (whose `read()` gives a `str`, which has no
`decode`) raises `TypeError`, as does an `AttributeError` raised by a `decode` method; an
exception from `fp.read()` propagates. -/
def LoadSpec : Prop :=
  (∀ (pf : ParseFloat) (maxK maxD : Nat) (s : Str), (∀ c ∈ s, c ≤ maxUnicode ∧ isSurrogate c = false) →
    load pf maxK maxD (.ok (.bytes (s.flatMap utf8EncodeChar))) = loads pf maxK maxD (.str s)) ∧
  (∀ (pf : ParseFloat) (maxK maxD : Nat) (b : List Nat) (e : PyExc), utf8Decode b .strict = .error e →
    load pf maxK maxD (.ok (.bytes b)) = .error e) ∧
  (∀ (pf : ParseFloat) (maxK maxD : Nat), load pf maxK maxD (.ok .noDecode) = .error (.typeError binaryModeMsg)) ∧
  (∀ (pf : ParseFloat) (maxK maxD : Nat) (msg : String),
    load pf maxK maxD (.ok (.custom (.error (.named "AttributeError" msg)))) = .error (.typeError binaryModeMsg)) ∧
  (∀ (pf : ParseFloat) (maxK maxD : Nat) (e : PyExc), load pf maxK maxD (.error e) = .error e)

theorem loadSpec_proven : LoadSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro pf maxK maxD s hs
    have := (utf8RoundTrip_proven s hs).2
    simp [load, this, Except.map, bind, Except.bind]
  · intro pf maxK maxD b e he
    simp [load, he, Except.map, bind, Except.bind]
  · intro pf maxK maxD; rfl
  · intro pf maxK maxD msg; rfl
  · intro pf maxK maxD e; rfl

end PyLean.TextLibs.Toml
