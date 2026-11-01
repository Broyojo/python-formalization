import PyLean.UnicodeObj.ObjectWriter
import PyLean.UnicodeObj.CodecCallback

/-!
The UTF-8 decoder with any error handler, as C runs it: into a writer, with its fast paths.
Objects/unicodeobject.c:5187-5453 and 14171-14192.

`utf8DecodeLoopX` is `unicode_decode_utf8_impl` with custom handlers. Here it is run the way C runs
it, with what was written before a failure, since those characters decide how wide the buffer got.

A custom handler can loop forever, so the budget is a parameter. `.modelFuel` is never a Python
outcome. The word-at-a-time loops of `ascii_decode` and `find_first_nonascii` are not mirrored:
they return the length of the ASCII prefix, which is `asciiPrefix`.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- `utf8DecodeLoopX`, also saying what had been written when it failed. -/
def utf8WriterLoopX (H : DH) (consumed : Bool) :
    Nat → Bytes → List DecView → Nat → List Nat → Str → Str × Py Nat
  | 0, _, _, _, _, out => (out, .error .modelFuel)
  | _ + 1, _, _, pos, [], out => (out, .ok pos)
  | fuel + 1, input, hist, pos, rest@(b0 :: tl), out =>
    let onError (reason : String) (stopAt : Nat) : Str × Py Nat :=
      let n := stopAt - pos
      let bad := rest.take n
      let go (w : Str) := utf8WriterLoopX H consumed fuel input hist stopAt (rest.drop n) (out ++ w)
      let viaCallback : Str × Py Nat :=
        match handlerStep H "utf-8" .utf8 reason input hist pos stopAt with
        | .error e => (out, .error e)
        | .ok (hist', input', rep, newpos) =>
          utf8WriterLoopX H consumed fuel input' hist' newpos (input'.drop newpos) (out ++ rep)
      match H with
      | .std .ignore => go []
      | .std .replace => go [0xfffd]
      | .std .surrogateescape => go (bad.map (· + 0xdc00))
      | _ => viaCallback
    match utf8Step rest with
    | .char c n =>
      utf8WriterLoopX H consumed fuel input hist (pos + n) (rest.drop n) (out ++ [c])
    | .stop =>
      if consumed then (out, .ok pos)
      else onError "unexpected end of data" input.length
    | .err 1 => onError "invalid start byte" (pos + 1)
    | .err code =>
      if code == 2 && consumed && b0 == 0xED && rest.length == 2 &&
          decide (0xA0 ≤ tl.headD 0) && decide (tl.headD 0 ≤ 0xBF) then (out, .ok pos)
      else onError "invalid continuation byte" (pos + code - 1)

/-- `unicode_decode_utf8_impl` from where the fast path stopped, in a writer of capacity `cap`, and
what it left. -/
def decodeRestX (w : UWriter) (cap : Nat) (b pre : Bytes) (H : DH) (consumed : Bool) (fuel : Nat) :
    UWriter × Py Nat :=
  let (out, r) := utf8WriterLoopX H consumed (fuel - pre.length) b [] pre.length (b.drop pre.length) pre
  let cap' := prepareCap cap (maxCharOf out)
  match r with
  | .ok n => ({ text := w.text ++ out, cap := cap' }, .ok n)
  | .error e => ({ w with cap := cap' }, .error e)

/-- `unicode_decode_utf8_writer`, unicodeobject.c@3.14.7:5523-5559, with the put back of `pos` that its
callers do. -/
def decodeWriterX (w : UWriter) (b : Bytes) (H : DH) (consumed : Bool) (fuel : Nat) :
    UWriter × Py Nat :=
  if b.isEmpty then (w, .ok 0)
  else
    let cap := prepareCap w.cap 127
    if cap ≤ 255 then
      let pre := asciiPrefix b
      if pre.length = b.length then ({ text := w.text ++ pre, cap }, .ok b.length)
      else decodeRestX w cap b pre H consumed fuel
    else decodeRestX w cap b [] H consumed fuel

/-- `PyUnicodeWriter_DecodeUTF8Stateful`, unicodeobject.c@3.14.7:14171-14192. `consumed` is whether
`*consumed` was passed. The result is the value of `*consumed`, which is 0 if it was not. -/
def writerDecodeStateful (w : UWriter) (b : Bytes) (size : Int) (H : DH) (consumed : Bool)
    (fuel : Nat) : UWriter × Py Nat :=
  let r := decodeWriterX w (sizedBytes b size) H consumed fuel
  if consumed then r else noConsumed r

/-- The capacity `unicode_decode_utf8` starts from when `errors` is NULL, from the first byte that is
not ASCII: unicodeobject.c:5361-5377. -/
def leadCap (ch : Nat) : Nat :=
  if ch < 0xc4 then 0xff else if ch < 0xf0 then 0xffff else 0x10ffff

/-- `unicode_decode_utf8`, unicodeobject.c:5310-5399, and `PyUnicode_DecodeUTF8Stateful`.
`strict` is `error_handler == _Py_ERROR_STRICT`, which means `errors` was NULL. -/
def unicodeDecodeUtf8 (b : Bytes) (H : DH) (strict consumed : Bool) (fuel : Nat) :
    Py ((Str × Kind) × Nat) :=
  if b.isEmpty then .ok (([], .ascii), 0)
  else if b.length = 1 ∧ b.getD 0 0 < 128 then .ok ((b, .ascii), 1)
  else
    let pre := asciiPrefix b
    if pre.length = b.length then .ok ((b, .ascii), b.length)
    else
      let ch := b.getD pre.length 0
      let maxchr := if strict && !consumed && decide (ch ≥ 0xc2) then leadCap ch else 127
      let kept := if maxchr ≤ 255 then pre else []
      let (out, r) := utf8WriterLoopX H consumed (fuel - kept.length) b [] kept.length
        (b.drop kept.length) kept
      match r with
      | .error e => .error e
      | .ok n => .ok (({ text := out, cap := prepareCap maxchr (maxCharOf out) } : UWriter).finish, n)

end PyLean.UnicodeObj
