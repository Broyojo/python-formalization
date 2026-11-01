import PyLean.UnicodeObj.CodecWide

/-!
ASCII and Latin-1: `unicode_encode_ucs1` (unicodeobject.c:7245-7425),
`PyUnicode_DecodeASCII` (:7453-7549), `PyUnicode_DecodeLatin1` (:7136-7142), with the
`backslashreplace` (@3.14.7:851-912) and `xmlcharrefreplace` (@3.14.7:917-971) writers.

The decoder's fast paths (`ascii_decode` and the `replace`/`surrogateescape` case) write
what the generic handler call would, so `decodeDriver` models them; the difftest checks it.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- The leading characters at or above `limit`: the `while` at unicodeobject.c:7288-7289,
as characters. -/
def unencodableRun (limit : Nat) : List Nat → List Nat
  | [] => []
  | c :: cs => if c ≥ limit then c :: unencodableRun limit cs else []

/-- `surrogateescape`'s test, unicodeobject.c:7335-7348. -/
def isEscapedByte (c : Nat) : Bool := decide (0xdc80 ≤ c) && decide (c ≤ 0xdcff)

/-- The longest prefix `surrogateescape` can write. -/
def escapedPrefix : List Nat → List Nat
  | [] => []
  | c :: cs => if isEscapedByte c then c :: escapedPrefix cs else []

/-- The `while (pos < size)` of `unicode_encode_ucs1`, unicodeobject.c@3.14.7:7409-7537. -/
def ucs1EncodeLoop (input : Str) (limit : Nat) (h : ErrHandler) (nameOf : Nat → Option Str) :
    Nat → Nat → List Nat → Bytes → Py Bytes
  | 0, _, _, _ => .error .modelFuel
  | _ + 1, _, [], out => .ok out
  | fuel + 1, pos, c :: cs, out =>
    if c < limit then ucs1EncodeLoop input limit h nameOf fuel (pos + 1) cs (out ++ [c])
    else
      let enc := if limit == 256 then "latin-1" else "ascii"
      let reason := if limit == 256 then "ordinal not in range(256)"
        else "ordinal not in range(128)"
      let run := unencodableRun limit (c :: cs)
      let collend := pos + run.length
      let go (w : Bytes) :=
        ucs1EncodeLoop input limit h nameOf fuel collend ((c :: cs).drop run.length) (out ++ w)
      let viaHandler (collstart : Nat) (out : Bytes) : Py Bytes :=
        match encodeHandlerCall h nameOf enc .unknown input collstart collend reason with
        | .error e => .error e
        | .ok (rep, newpos) =>
          let next (w : Bytes) :=
            ucs1EncodeLoop input limit h nameOf fuel newpos (input.drop newpos) (out ++ w)
          match rep with
          | .bytes b => next b
          | .str r =>
            if r.all (· < limit) then next r
            else .error (encodeError enc input collstart collend reason)
      match h with
      | .strict => .error (encodeError enc input pos collend reason)
      | .replace => go (List.replicate run.length 63)
      | .ignore => go []
      | .backslashreplace => go (run.flatMap escapeEncodeChar)
      | .xmlcharrefreplace => go (run.flatMap xmlRef)
      | .surrogateescape =>
        let pre := escapedPrefix run
        if pre.length = run.length then go (pre.map (· - 0xdc00))
        else viaHandler (pos + pre.length) (out ++ pre.map (· - 0xdc00))
      | _ => viaHandler pos out

/-- `_PyUnicode_AsASCIIString` (:7552-7564), `_PyUnicode_AsLatin1String` (:7428-7442). -/
def ucs1Encode (s : Str) (limit : Nat) (h : ErrHandler) (nameOf : Nat → Option Str) : Py Bytes :=
  ucs1EncodeLoop s limit h nameOf (s.length + 1) 0 s []

/-- One round of the loop of `PyUnicode_DecodeASCII`, unicodeobject.c:7482-7534. -/
def stepAscii : List Nat → DStep
  | [] => .stop
  | c :: _ => if c < 128 then .char c 1 else .fail "ordinal not in range(128)" 0 1

/-- `PyUnicode_DecodeASCII`, unicodeobject.c:7453-7549. -/
def asciiDecode (input : Bytes) (h : ErrHandler) : Py Str := do
  let (s, _) ← decodeDriver stepAscii h "ascii" .unknown input (input.length + 1) 0 input []
  .ok s

/-- `PyUnicode_DecodeLatin1`, unicodeobject.c:7136-7142: `_PyUnicode_FromUCS1`. -/
def latin1Decode (input : Bytes) : Str := input

end PyLean.UnicodeObj
