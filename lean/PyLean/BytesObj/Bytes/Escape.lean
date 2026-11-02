import PyLean.BytesObj.Bytes.Writer

/-!
`_PyBytes_DecodeEscape2` and `PyBytes_DecodeEscape`, Objects/bytesobject.c:1170-1320,
reached from Python as `codecs.escape_decode`.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-- `_PyLong_DigitValue[c]`, Objects/longobject.c:3194-3211: 37 for a non-digit. -/
def digitValue (c : Nat) : Nat :=
  if 48 ≤ c ∧ c ≤ 57 then c - 48
  else if 65 ≤ c ∧ c ≤ 90 then c - 55
  else if 97 ≤ c ∧ c ≤ 122 then c - 87
  else 37

/-- `'0' <= c && c <= '7'`. -/
def isOct (c : Nat) : Bool := decide (48 ≤ c ∧ c ≤ 55)

/-- The `case 'x'` failure branch, bytesobject.c:1242-1264: the error handler,
then the hex digit skip. `pos` is the offset of the backslash; `rest` the input
after `\x`. -/
def badHex (errors : Option String) (pos : Nat) (rest out : Seq) : Py (Seq × Seq × Nat) :=
  let strict := match errors with | none => true | some e => e == "strict"
  if strict then .error (.valueError s!"invalid \\x escape at position {pos}")
  else
    let e := errors.getD ""
    let out' : Py Seq :=
      if e == "replace" then .ok (out ++ [63])
      else if e == "ignore" then .ok out
      else .error (.valueError s!"decoding error; unknown error handling code: {e}")
    match out' with
    | .error x => .error x
    | .ok out =>
      match rest with
      | c :: more => if isXDigitC c then .ok (out, more, 1) else .ok (out, rest, 0)
      | [] => .ok (out, rest, 0)

/-- The first invalid escape: `(character value, offset)`. -/
abbrev FirstBad := Option (Nat × Nat)

/-- The simple one-character escapes, bytesobject.c:1202-1211. -/
def simpleEscape (e : Nat) : Option Nat :=
  if e = 92 then some 92
  else if e = 39 then some 39
  else if e = 34 then some 34
  else if e = 98 then some 8
  else if e = 102 then some 12
  else if e = 116 then some 9
  else if e = 110 then some 10
  else if e = 114 then some 13
  else if e = 118 then some 11
  else if e = 97 then some 7
  else none

/-- The main loop of `_PyBytes_DecodeEscape2`, bytesobject.c:1186-1275. `pos` is
`s - (end - len)`, `rest` the input from `s`. -/
def decodeLoop (errors : Option String) : Nat → Nat → Seq → Seq → FirstBad → Py (Seq × FirstBad)
  | 0, _, _, _, _ => .error .modelFuel
  | _ + 1, _, [], out, fb => .ok (out, fb)
  | fuel + 1, pos, c :: rest, out, fb =>
    if c ≠ 92 then decodeLoop errors fuel (pos + 1) rest (out ++ [c]) fb
    else match rest with
    | [] => .error (.valueError "Trailing \\ in string")
    | e :: rest =>
      if e = 10 then decodeLoop errors fuel (pos + 2) rest out fb
      else match simpleEscape e with
      | some v => decodeLoop errors fuel (pos + 2) rest (out ++ [v]) fb
      | none =>
        if isOct e then
          -- at most two more octal digits
          let (c₁, n₁, rest) : Nat × Nat × Seq :=
            match rest with
            | d :: more => if isOct d then ((e - 48) * 8 + (d - 48), 1, more) else (e - 48, 0, rest)
            | [] => (e - 48, 0, [])
          let (c₂, n₂, rest) : Nat × Nat × Seq :=
            if n₁ = 1 then
              match rest with
              | d :: more => if isOct d then (c₁ * 8 + (d - 48), 1, more) else (c₁, 0, rest)
              | [] => (c₁, 0, [])
            else (c₁, 0, rest)
          let used := 2 + n₁ + n₂
          let fb := if c₂ > 255 ∧ fb.isNone then some (c₂, pos + used - 3) else fb
          decodeLoop errors fuel (pos + used) rest (out ++ [c₂ % 256]) fb
        else if e = 120 then
          match rest with
          | d1 :: d2 :: more =>
            if digitValue d1 < 16 ∧ digitValue d2 < 16 then
              decodeLoop errors fuel (pos + 4) more
                (out ++ [digitValue d1 * 16 + digitValue d2]) fb
            else match badHex errors pos rest out with
              | .ok (out, rest, n) => decodeLoop errors fuel (pos + 2 + n) rest out fb
              | .error x => .error x
          | _ =>
            match badHex errors pos rest out with
            | .ok (out, rest, n) => decodeLoop errors fuel (pos + 2 + n) rest out fb
            | .error x => .error x
        else
          let fb := if fb.isNone then some (e, pos + 1) else fb
          decodeLoop errors fuel (pos + 1) (e :: rest) (out ++ [92]) fb

/-- `_PyBytes_DecodeEscape2`, bytesobject.c:1170-1282. Fuel: each step consumes
input or turns an invalid escape into a plain byte. -/
def decodeEscape2 (s : Seq) (errors : Option String) : Py (Seq × FirstBad) :=
  decodeLoop errors (2 * s.length + 2) 0 s [] none

/-- The warning of `PyBytes_DecodeEscape`, bytesobject.c:1297-1318. -/
def escapeWarning : FirstBad → Option String
  | none => none
  | some (c, _) =>
    if c > 0xff then
      let oct := String.ofList (Nat.toDigits 8 c)
      some ("b\"\\" ++ oct ++ "\" is an invalid octal escape sequence. Such sequences will not work in the future. ")
    else
      some ("b\"\\" ++ String.ofList [Char.ofNat c] ++ "\" is an invalid escape sequence. Such sequences will not work in the future. ")

/-- `PyBytes_DecodeEscape`, bytesobject.c:1284-1320: the bytes and the
`DeprecationWarning` text. -/
def bytesDecodeEscape (s : Seq) (errors : Option String) : Py (Seq × Option String) := do
  let (r, fb) ← decodeEscape2 s errors
  return (r, escapeWarning fb)

/-! ## Round trip with `repr` -/

set_option maxRecDepth 100000 in
theorem hex_digit_roundtrip : ∀ c, c < 256 →
    digitValue (hexDigit (c / 16)) * 16 + digitValue (hexDigit (c % 16)) = c ∧
    digitValue (hexDigit (c / 16)) < 16 ∧ digitValue (hexDigit (c % 16)) < 16 := by
  decide

/-- `repr` round trip: for every byte string and either quote, decoding the body
of the literal `_Py_bytes_repr` writes gives back the bytes, with no invalid escape. A `bytearray`
repr has the same body, because 3.15 writes it with the same function. -/
def ReprDecodeRoundTrip : Prop :=
  ∀ (quote : Nat) (s : Seq), (quote = 39 ∨ quote = 34) → (∀ c ∈ s, c < 256) →
    decodeEscape2 (reprBody quote s) none = .ok (s, none)

/-- The general step: an escaped form produced by `reprByte` decodes to one byte, whatever follows it. -/
theorem decode_step (errors : Option String) (fuel pos : Nat) (t out : Seq) (fb : FirstBad)
    (c : Nat) (enc : Seq) (hc : c < 256)
    (henc : enc = [c] ∧ c ≠ 92 ∨
      enc = [92, c] ∧ (c = 39 ∨ c = 34 ∨ c = 92) ∨
      enc = [92, 116] ∧ c = 9 ∨ enc = [92, 110] ∧ c = 10 ∨ enc = [92, 114] ∧ c = 13 ∨
      enc = [92, 120, hexDigit (c / 16), hexDigit (c % 16)]) :
    decodeLoop errors (fuel + 1) pos (enc ++ t) out fb =
      decodeLoop errors fuel (pos + enc.length) t (out ++ [c]) fb := by
  rcases henc with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | rfl
  · simp [decodeLoop, h]
  · rcases h with rfl | rfl | rfl <;> simp [decodeLoop, simpleEscape]
  · subst h; simp [decodeLoop, simpleEscape]
  · subst h; simp [decodeLoop, simpleEscape]
  · subst h; simp [decodeLoop, simpleEscape]
  · obtain ⟨h1, h2, h3⟩ := hex_digit_roundtrip c hc
    simp [decodeLoop, simpleEscape, isOct, h1, h2, h3]

theorem reprByte_form (quote c : Nat) (hq : quote = 39 ∨ quote = 34) :
    let enc := reprByte quote c
    enc = [c] ∧ c ≠ 92 ∨
      enc = [92, c] ∧ (c = 39 ∨ c = 34 ∨ c = 92) ∨
      enc = [92, 116] ∧ c = 9 ∨ enc = [92, 110] ∧ c = 10 ∨ enc = [92, 114] ∧ c = 13 ∨
      enc = [92, 120, hexDigit (c / 16), hexDigit (c % 16)] := by
  simp only [reprByte]
  split
  · rename_i h; right; left; refine ⟨rfl, ?_⟩; omega
  · split
    · rename_i h1 h2; subst h2; simp
    · split
      · rename_i h2; subst h2; simp
      · split
        · rename_i h2; subst h2; simp
        · split
          · simp
          · rename_i h1 h2 h3 h4 h5; left; refine ⟨rfl, ?_⟩; omega

def EncForm (enc : Nat → Seq) : Prop :=
  ∀ c, c < 256 → (enc c = [c] ∧ c ≠ 92 ∨
      enc c = [92, c] ∧ (c = 39 ∨ c = 34 ∨ c = 92) ∨
      enc c = [92, 116] ∧ c = 9 ∨ enc c = [92, 110] ∧ c = 10 ∨ enc c = [92, 114] ∧ c = 13 ∨
      enc c = [92, 120, hexDigit (c / 16), hexDigit (c % 16)])

theorem decode_flat (enc : Nat → Seq) (hform : EncForm enc)
    (s : Seq) (hs : ∀ c ∈ s, c < 256) (fuel pos : Nat) (out : Seq) (hf : s.length < fuel) :
    decodeLoop none fuel pos (s.flatMap enc) out none = .ok (out ++ s, none) := by
  induction s generalizing fuel pos out with
  | nil =>
    cases fuel with
    | zero => simp at hf
    | succ f => simp [decodeLoop]
  | cons c rest ih =>
    have hc := hs c (by simp)
    have hrest : ∀ x ∈ rest, x < 256 := fun x hx => hs x (by simp [hx])
    simp only [List.flatMap_cons]
    cases fuel with
    | zero => simp at hf
    | succ f =>
      rw [decode_step none f pos _ out none c (enc c) hc (hform c hc)]
      rw [ih hrest f _ _ (by simp at hf; omega)]
      simp

theorem flat_length (enc : Nat → Seq) (hform : EncForm enc) (s : Seq) (hs : ∀ c ∈ s, c < 256) :
    s.length ≤ (s.flatMap enc).length := by
  induction s with
  | nil => simp
  | cons c rest ih =>
    have hc := hs c (by simp)
    have h1 : 1 ≤ (enc c).length := by
      rcases hform c hc with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | h <;> simp [h]
    have := ih (fun x hx => hs x (by simp [hx]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem reprDecodeRoundTrip_proven : ReprDecodeRoundTrip := by
  intro quote s hq hs
  have f1 : EncForm (reprByte quote) := fun c _ => reprByte_form quote c hq
  have hl := flat_length _ f1 s hs
  have := decode_flat (reprByte quote) f1 s hs
    (2 * (s.flatMap (reprByte quote)).length + 2) 0 [] (by omega)
  simpa [decodeEscape2, reprBody] using this

end PyLean.BytesObj.Bytes
