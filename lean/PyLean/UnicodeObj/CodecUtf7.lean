import PyLean.UnicodeObj.CodecWide

/-!
UTF-7: `PyUnicode_DecodeUTF7Stateful` (unicodeobject.c:4734-4928) and
`_PyUnicode_EncodeUTF7` (:4932-5029). `str.encode` calls the encoder with `base64SetO` and
`base64WhiteSpace` both 0, so Set O and whitespace are direct; only that case is reachable
from Python, and only it is modelled.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- `IS_BASE64`, unicodeobject.c:4642-4647. -/
def isBase64 (c : Nat) : Bool :=
  (decide (65 ≤ c) && decide (c ≤ 90)) || (decide (97 ≤ c) && decide (c ≤ 122)) ||
  (decide (48 ≤ c) && decide (c ≤ 57)) || c == 43 || c == 47

/-- `FROM_BASE64`, unicodeobject.c:4651-4655. -/
def fromBase64 (c : Nat) : Nat :=
  if 65 ≤ c ∧ c ≤ 90 then c - 65
  else if 97 ≤ c ∧ c ≤ 122 then c - 97 + 26
  else if 48 ≤ c ∧ c ≤ 57 then c - 48 + 52
  else if c = 43 then 62 else 63

/-- `TO_BASE64`, unicodeobject.c:4659-4660. -/
def toBase64 (n : Nat) : Nat :=
  let v := n % 64
  if v < 26 then 65 + v
  else if v < 52 then 97 + v - 26
  else if v < 62 then 48 + v - 52
  else if v = 62 then 43 else 47

/-- `DECODE_DIRECT`, unicodeobject.c:4667-4668. -/
def decodeDirect (c : Nat) : Bool := decide (c ≤ 127) && c != 43

/-- `utf7_category`, unicodeobject.c:4682-4699: set D is 0, set O 1, whitespace 2, others 3. -/
def utf7Category (c : Nat) : Nat :=
  if c = 9 ∨ c = 10 ∨ c = 13 ∨ c = 32 then 2
  else if c = 39 ∨ c = 40 ∨ c = 41 ∨ c = 44 ∨ c = 45 ∨ c = 46 ∨ c = 47 ∨ c = 58 ∨ c = 63 then 0
  else if 48 ≤ c ∧ c ≤ 57 then 0
  else if 65 ≤ c ∧ c ≤ 90 then 0
  else if 97 ≤ c ∧ c ≤ 122 then 0
  else if c = 33 ∨ c = 34 ∨ c = 35 ∨ c = 36 ∨ c = 37 ∨ c = 38 ∨ c = 42 ∨ c = 59 ∨ c = 60 ∨
    c = 61 ∨ c = 62 ∨ c = 64 ∨ c = 91 ∨ c = 93 ∨ c = 94 ∨ c = 95 ∨ c = 96 ∨ c = 123 ∨
    c = 124 ∨ c = 125 then 1
  else 3

/-- `ENCODE_DIRECT(c, 1, 1)`, unicodeobject.c:4706-4710. -/
def encodeDirect (c : Nat) : Bool :=
  decide (c < 128) && decide (c > 0) && (utf7Category c == 0 || utf7Category c == 2 ||
    utf7Category c == 1)

/-- The decoder's state. -/
structure U7 where
  inShift : Bool := false
  base64bits : Nat := 0
  base64buffer : Nat := 0
  surrogate : Nat := 0
  startinpos : Nat := 0
  shiftOutStart : Nat := 0
  deriving Repr, DecidableEq

/-- What one round does: output, the next position, the state; or an error span. -/
inductive U7Step where
  | go (w : Str) (n : Nat) (st : U7)
  | fail (reason : String) (n : Nat) (st : U7)
  deriving Repr, DecidableEq

/-- A base-64 character in a shift, unicodeobject.c:4769-4802. -/
def u7Base64 (st : U7) (ch : Nat) : U7Step :=
  let buffer := st.base64buffer * 64 + fromBase64 ch
  let bits := st.base64bits + 6
  if bits < 16 then .go [] 1 { st with base64buffer := buffer, base64bits := bits }
  else
    let outCh := buffer >>> (bits - 16)
    let bits := bits - 16
    let buffer := buffer % (2 ^ bits)
    let st := { st with base64buffer := buffer, base64bits := bits }
    if st.surrogate != 0 && isLowSurrogate outCh then
      .go [joinSurrogates st.surrogate outCh] 1 { st with surrogate := 0 }
    else
      let w : Str := if st.surrogate != 0 then [st.surrogate] else []
      if isHighSurrogate outCh then .go w 1 { st with surrogate := outCh }
      else .go (w ++ [outCh]) 1 { st with surrogate := 0 }

/-- Leaving a shift, unicodeobject.c:4804-4830. -/
def u7Leave (st : U7) (ch : Nat) : U7Step :=
  let st := { st with inShift := false }
  if st.base64bits ≥ 6 then .fail "partial character in shift sequence" 1 st
  else if st.base64bits > 0 ∧ st.base64buffer != 0 then
    .fail "non-zero padding bits in shift sequence" 1 st
  else
    let w : Str := if st.surrogate != 0 && decodeDirect ch then [st.surrogate] else []
    .go w (if ch == 45 then 1 else 0) { st with surrogate := 0 }

/-- One round of the `while (s < e)` of the decoder, unicodeobject.c:4764-4861. `pos` is the
position of `ch`, `outLen` is `writer.pos`. -/
def u7Step (st : U7) (pos outLen ch : Nat) (next : Option Nat) : U7Step :=
  if st.inShift then
    if isBase64 ch then u7Base64 st ch else u7Leave st ch
  else if ch == 43 then
    let st := { st with startinpos := pos }
    match next with
    | some 45 => .go [43] 2 st
    | some n =>
      if !isBase64 n then .fail "ill-formed sequence" 2 st
      else .go [] 1 { st with inShift := true, surrogate := 0, shiftOutStart := outLen,
                              base64bits := 0, base64buffer := 0 }
    | none =>
      .go [] 1 { st with inShift := true, surrogate := 0, shiftOutStart := outLen,
                         base64bits := 0, base64buffer := 0 }
  else if decodeDirect ch then .go [ch] 1 st
  else .fail "unexpected special character" 1 { st with startinpos := pos }

/-- `utf7Error`, unicodeobject.c:4857-4865. -/
def u7Handler (h : ErrHandler) (input : Bytes) (start stop : Nat) (reason : String) :
    Py (Str × Nat) :=
  decodeHandlerCall h "utf7" .unknown input start stop reason

/-- The decoder's loop, with the end-of-string part of unicodeobject.c:4868-4888. -/
def utf7Loop (input : Bytes) (h : ErrHandler) (consumed : Bool) :
    Nat → Nat → List Nat → U7 → Str → Py (Str × U7 × Nat)
  | 0, _, _, _, _ => .error .modelFuel
  | fuel + 1, pos, [], st, out =>
    if st.inShift && !consumed then
      let st := { st with inShift := false }
      if st.surrogate != 0 || decide (st.base64bits ≥ 6) ||
          (decide (st.base64bits > 0) && st.base64buffer != 0) then
        match u7Handler h input st.startinpos input.length "unterminated shift sequence" with
        | .error e => .error e
        | .ok (rep, newpos) =>
          utf7Loop input h consumed fuel newpos (input.drop newpos) st (out ++ rep)
      else .ok (out, st, pos)
    else .ok (out, st, pos)
  | fuel + 1, pos, ch :: t, st, out =>
    match u7Step st pos out.length ch t.head? with
    | .go w n st' => utf7Loop input h consumed fuel (pos + n) ((ch :: t).drop n) st' (out ++ w)
    | .fail reason n st' =>
      match u7Handler h input st'.startinpos (pos + n) reason with
      | .error e => .error e
      | .ok (rep, newpos) =>
        utf7Loop input h consumed fuel newpos (input.drop newpos) st' (out ++ rep)

/-- `PyUnicode_DecodeUTF7Stateful`, unicodeobject.c:4734-4928: the text and the bytes
consumed. In a shift at the end with `final=False`, the output is cut back to where the
shift began and `*consumed` is `startinpos`. -/
def utf7Decode (input : Bytes) (h : ErrHandler) (final : Bool) : Py (Str × Nat) :=
  if input.isEmpty then .ok ([], 0)
  else
    match utf7Loop input h (!final) (3 * input.length + 3) 0 input {} [] with
    | .error e => .error e
    | .ok (out, st, pos) =>
      if !final && st.inShift then .ok (out.take st.shiftOutStart, st.startinpos)
      else .ok (out, pos)

/-- The encoder's state: `inShift`, `base64bits`, `base64buffer`. -/
structure U7Enc where
  inShift : Bool := false
  bits : Nat := 0
  buffer : Nat := 0
  deriving Repr, DecidableEq

/-- The `while (base64bits >= 6)` loops, unicodeobject.c:5005 and :5012. `fuel` bounds them. -/
def u7Drain : Nat → U7Enc → Bytes → U7Enc × Bytes
  | 0, e, out => (e, out)
  | fuel + 1, e, out =>
    if e.bits ≥ 6 then
      u7Drain fuel { e with bits := e.bits - 6 } (out ++ [toBase64 (e.buffer >>> (e.bits - 6))])
    else (e, out)

/-- `encode_char`, unicodeobject.c:5000-5015. -/
def u7EncodeChar (e : U7Enc) (ch : Nat) (out : Bytes) : U7Enc × Bytes :=
  let (e, out, ch) : U7Enc × Bytes × Nat :=
    if ch ≥ 0x10000 then
      let e' := { e with bits := e.bits + 16, buffer := e.buffer * 65536 + highSurrogate ch }
      let (e', out) := u7Drain 4 e' out
      (e', out, lowSurrogate ch)
    else (e, out, ch)
  u7Drain 4 { e with bits := e.bits + 16, buffer := e.buffer * 65536 + ch } out

/-- One round of the `for` of the encoder, unicodeobject.c:4968-4998. -/
def u7EncodeStep (e : U7Enc) (ch : Nat) (out : Bytes) : U7Enc × Bytes :=
  if e.inShift then
    if encodeDirect ch then
      let out := if e.bits != 0 then out ++ [toBase64 (e.buffer * 2 ^ (6 - e.bits))] else out
      let out := if isBase64 ch || ch == 45 then out ++ [45] else out
      ({ inShift := false, bits := 0, buffer := if e.bits != 0 then 0 else e.buffer }, out ++ [ch])
    else u7EncodeChar e ch out
  else if ch == 43 then (e, out ++ [43, 45])
  else if encodeDirect ch then (e, out ++ [ch])
  else u7EncodeChar { e with inShift := true } ch (out ++ [43])

/-- `_PyUnicode_EncodeUTF7`, unicodeobject.c:4932-5029. -/
def utf7Encode (s : Str) : Bytes :=
  let (e, out) := s.foldl (fun p ch => u7EncodeStep p.1 ch p.2) (({} : U7Enc), ([] : Bytes))
  let out := if e.bits != 0 then out ++ [toBase64 (e.buffer * 2 ^ (6 - e.bits))] else out
  if e.inShift then out ++ [45] else out

end PyLean.UnicodeObj
