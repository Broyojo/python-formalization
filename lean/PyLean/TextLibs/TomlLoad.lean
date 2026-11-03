import PyLean.TextLibs.TomlLemmas
import PyLean.UnicodeObj.CodecProps

/-!
`load`, _parser.py:139-148: a binary file is `loads` of its UTF-8 text.
-/

namespace PyLean.TextLibs.Toml

open PyLean.UnicodeObj

/-- `load(fp)`: for every text of Unicode scalar values, a binary file holding its UTF-8
encoding loads exactly as `loads` of the text, called one frame deeper; bytes that are not UTF-8
raise the decoder's `UnicodeDecodeError`; a file opened in text mode (whose `read()` gives a `str`,
which has no `decode`) raises `TypeError`, as does an `AttributeError` raised by a `decode` method;
an exception from `fp.read()` propagates. Each with at least one frame left for `load` itself;
with none, `RecursionError`. -/
def LoadSpec : Prop :=
  (∀ (pf : ParseFloat) (maxK maxD : Nat) (tz : TzCache) (fr : Nat) (s : Str), 1 ≤ fr →
    (∀ c ∈ s, c ≤ maxUnicode ∧ isSurrogate c = false) →
    load pf maxK maxD tz fr (.ok (.bytes (s.flatMap utf8EncodeChar))) = loads pf maxK maxD tz (fr - 1) (.str s)) ∧
  (∀ (pf : ParseFloat) (maxK maxD : Nat) (tz : TzCache) (fr : Nat) (b : List Nat) (e : PyExc), 1 ≤ fr →
    utf8Decode b .strict = .error e → load pf maxK maxD tz fr (.ok (.bytes b)) = .error e) ∧
  (∀ (pf : ParseFloat) (maxK maxD : Nat) (tz : TzCache) (fr : Nat), 1 ≤ fr →
    load pf maxK maxD tz fr (.ok .noDecode) = .error (.typeError binaryModeMsg)) ∧
  (∀ (pf : ParseFloat) (maxK maxD : Nat) (tz : TzCache) (fr : Nat) (msg : String), 1 ≤ fr →
    load pf maxK maxD tz fr (.ok (.custom (.error (.named "AttributeError" msg)))) =
      .error (.typeError binaryModeMsg)) ∧
  (∀ (pf : ParseFloat) (maxK maxD : Nat) (tz : TzCache) (fr : Nat) (e : PyExc), 1 ≤ fr →
    load pf maxK maxD tz fr (.error e) = .error e) ∧
  (∀ (pf : ParseFloat) (maxK maxD : Nat) (tz : TzCache) (rd : Py ReadVal),
    load pf maxK maxD tz 0 rd = .error recErr)

theorem loadSpec_proven : LoadSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro pf maxK maxD tz fr s hfr hs
    have := (utf8RoundTrip_proven s hs).2
    simp [load, need_ok hfr, this, Except.map, bind, Except.bind]
  · intro pf maxK maxD tz fr b e hfr he
    simp [load, need_ok hfr, he, Except.map, bind, Except.bind]
  · intro pf maxK maxD tz fr hfr; simp [load, need_ok hfr]; rfl
  · intro pf maxK maxD tz fr msg hfr; simp [load, need_ok hfr]; rfl
  · intro pf maxK maxD tz fr e hfr; simp [load, need_ok hfr]; rfl
  · intro pf maxK maxD tz rd; simp [load, need]

end PyLean.TextLibs.Toml
