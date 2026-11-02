import PyLean.UnicodeObj.CodecHandlers

/-!
UTF-8: `STRINGLIB(utf8_decode)` and `STRINGLIB(utf8_encoder)`,
Objects/stringlib/codecs.h:22-252 and codecs.h:259-482, driven by `unicode_decode_utf8_impl`,
Objects/unicodeobject.c:5187-5306.

The four instantiations of `utf8_decode` differ in `STRINGLIB_MAX_CHAR`, and the
out-of-range return only widens the writer, so one model covers them. Byte fields use
`/`, `%`, `*` and `+`, where C uses `>>`, `&`, `<<` and `|` on the same disjoint bits.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- `IS_CONTINUATION_BYTE`. -/
def isCont (b : Nat) : Bool := decide (0x80 ≤ b) && decide (b < 0xC0)

/-- The result of one round of the `while` loop of `utf8_decode`. -/
inductive U8 where
  /-- A character and the bytes it took. -/
  | char (c n : Nat)
  /-- `break`: truncated input at the end, return value 0. -/
  | stop
  /-- `goto InvalidStart` (1) or `InvalidContinuation1..3` (2, 3, 4). -/
  | err (code : Nat)
  deriving Repr, DecidableEq

/-- The two-byte branch, codecs.h:97-125, with a byte available. -/
def step2 (ch ch2 : Nat) : U8 :=
  if !isCont ch2 then .err 2
  else .char (ch * 64 + ch2 - (0xC0 * 64 + 0x80)) 2

/-- The three-byte branch for a full sequence, codecs.h:142-175. -/
def step3 (ch ch2 ch3 : Nat) : U8 :=
  if !isCont ch2 then .err 2
  else if ch == 0xE0 && decide (ch2 < 0xA0) then .err 2
  else if ch != 0xE0 && ch == 0xED && decide (ch2 ≥ 0xA0) then .err 2
  else if !isCont ch3 then .err 3
  else .char (ch * 4096 + ch2 * 64 + ch3 - (0xE0 * 4096 + 0x80 * 64 + 0x80)) 3

/-- The four-byte branch for a full sequence, codecs.h:197-232. -/
def step4 (ch ch2 ch3 ch4 : Nat) : U8 :=
  if !isCont ch2 then .err 2
  else if ch == 0xF0 && decide (ch2 < 0x90) then .err 2
  else if ch != 0xF0 && ch == 0xF4 && decide (ch2 ≥ 0x90) then .err 2
  else if !isCont ch3 then .err 3
  else if !isCont ch4 then .err 4
  else .char (ch * 262144 + ch2 * 4096 + ch3 * 64 + ch4 -
    (0xF0 * 262144 + 0x80 * 4096 + 0x80 * 64 + 0x80)) 4

/-- One round of `utf8_decode` at the head of the input. -/
def utf8Step : List Nat → U8
  | [] => .stop
  | ch :: t =>
    if ch < 0x80 then .char ch 1
    else if ch < 0xE0 then
      if ch < 0xC2 then .err 1
      else match t with
        | [] => .stop
        | ch2 :: _ => step2 ch ch2
    else if ch < 0xF0 then
      match t with
      | [] => .stop
      | [ch2] =>
        if !isCont ch2 || (if ch2 < 0xA0 then ch == 0xE0 else ch == 0xED) then .err 2
        else .stop
      | ch2 :: ch3 :: _ => step3 ch ch2 ch3
    else if ch < 0xF5 then
      match t with
      | [] => .stop
      | [ch2] =>
        if !isCont ch2 || (if ch2 < 0x90 then ch == 0xF0 else ch == 0xF4) then .err 2
        else .stop
      | [ch2, ch3] =>
        if !isCont ch2 || (if ch2 < 0x90 then ch == 0xF0 else ch == 0xF4) then .err 2
        else if !isCont ch3 then .err 3
        else .stop
      | ch2 :: ch3 :: ch4 :: _ => step4 ch ch2 ch3 ch4
    else .err 1

/-- The `switch (ch)` and the error handling of `unicode_decode_utf8_impl`,
unicodeobject.c:5206-5298. `input` is the whole buffer, `pos` the offset of `rest`,
`consumed` is true for `final=False`. Returns the text and the bytes consumed. -/
def utf8DecodeLoop (input : Bytes) (h : ErrHandler) (consumed : Bool) :
    Nat → Nat → List Nat → Str → Py (Str × Nat)
  | 0, _, _, _ => .error .modelFuel
  | _ + 1, pos, [], out => .ok (out, pos)
  | fuel + 1, pos, rest@(b0 :: tl), out =>
    let onError (reason : String) (stopAt : Nat) : Py (Str × Nat) :=
      let n := stopAt - pos
      let bad := rest.take n
      let go (w : Str) := utf8DecodeLoop input h consumed fuel stopAt (rest.drop n) (out ++ w)
      match h with
      | .ignore => go []
      | .replace => go [0xfffd]
      | .surrogateescape => go (bad.map (· + 0xdc00))
      | _ =>
        match decodeHandlerCall h "utf-8" .utf8 input pos stopAt reason with
        | .error e => .error e
        | .ok (rep, newpos) =>
          utf8DecodeLoop input h consumed fuel newpos (input.drop newpos) (out ++ rep)
    match utf8Step rest with
    | .char c n =>
      utf8DecodeLoop input h consumed fuel (pos + n) (rest.drop n) (out ++ [c])
    | .stop =>
      if consumed then .ok (out, pos)
      else onError "unexpected end of data" input.length
    | .err 1 => onError "invalid start byte" (pos + 1)
    | .err code =>
      if code == 2 && consumed && b0 == 0xED && rest.length == 2 &&
          decide (0xA0 ≤ tl.headD 0) && decide (tl.headD 0 ≤ 0xBF) then .ok (out, pos)
      else onError "invalid continuation byte" (pos + code - 1)

/-- `unicode_decode_utf8` with `consumed == NULL` (`bytes.decode('utf-8', errors)`). -/
def utf8Decode (input : Bytes) (h : ErrHandler) : Py Str := do
  let (s, _) ← utf8DecodeLoop input h false (input.length + 1) 0 input []
  .ok s

/-- `PyUnicode_DecodeUTF8Stateful` with `final=False`: text and bytes consumed. -/
def utf8DecodeStateful (input : Bytes) (h : ErrHandler) : Py (Str × Nat) :=
  utf8DecodeLoop input h true (input.length + 1) 0 input []

/-- Table 3-7 of the Unicode Standard: well-formed UTF-8. -/
def utf8Wf : Nat → List Nat → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | fuel + 1, a :: t =>
    if a < 0x80 then utf8Wf fuel t
    else match t with
      | b :: t2 =>
        if 0xC2 ≤ a ∧ a ≤ 0xDF ∧ isCont b then utf8Wf fuel t2
        else match t2 with
          | c :: t3 =>
            if ((a == 0xE0 && decide (0xA0 ≤ b) && decide (b ≤ 0xBF)) ||
                (decide (0xE1 ≤ a) && decide (a ≤ 0xEC) && isCont b) ||
                (a == 0xED && decide (0x80 ≤ b) && decide (b ≤ 0x9F)) ||
                (decide (0xEE ≤ a) && decide (a ≤ 0xEF) && isCont b)) && isCont c then
              utf8Wf fuel t3
            else match t3 with
              | d :: t4 =>
                if ((a == 0xF0 && decide (0x90 ≤ b) && decide (b ≤ 0xBF)) ||
                    (decide (0xF1 ≤ a) && decide (a ≤ 0xF3) && isCont b) ||
                    (a == 0xF4 && decide (0x80 ≤ b) && decide (b ≤ 0x8F))) &&
                    isCont c && isCont d then
                  utf8Wf fuel t4
                else false
              | [] => false
          | [] => false
      | [] => false

/-- The encoder's bytes for one character, codecs.h:286-345. -/
def utf8EncodeChar (ch : Nat) : List Nat :=
  if ch < 0x80 then [ch]
  else if ch < 0x0800 then [0xc0 + ch / 64, 0x80 + ch % 64]
  else if ch < 0x10000 then [0xe0 + ch / 4096, 0x80 + ch / 64 % 64, 0x80 + ch % 64]
  else [0xf0 + ch / 262144, 0x80 + ch / 4096 % 64, 0x80 + ch / 64 % 64, 0x80 + ch % 64]

end PyLean.UnicodeObj
