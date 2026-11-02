import PyLean.UnicodeObj.FormatStr
import PyLean.UnicodeObj.CodecProps

/-!
`PyUnicodeWriter`, the public API over `_PyUnicodeWriter`: Objects/unicode_writer.c:66-633.

The state is what can be observed: the text up to `pos`, and `writer->maxchar`, the capacity of the
buffer's kind. Capacity is separate from the text because it does not shrink: a rollback of `pos`
leaves the buffer as wide as the write made it. The growth arithmetic of
`_PyUnicodeWriter_PrepareInternal` (overallocation, `min_length`) decides only how much memory is
held, not what `Finish` returns, so it is not modelled, and allocation failure is not modelled.

`PyUnicodeWriter_Create` sets `overallocate`, so none of these operations enters the `readonly` mode
on its own; `PyUnicodeWriter_Format` can, by clearing `overallocate` on its last chunk (see
`ObjectFromFormat.lean`). That mode keeps a reference to a string instead of copying it, with the
same text and capacity, so this state does not tell them apart. `wchar_t` is taken to be four bytes, as on the platforms tested; a two-byte `wchar_t`
would add the surrogate pairing of `find_maxchar_surrogates`.
-/

namespace PyLean.UnicodeObj

open PyLean PyLean.Binary64

/-- `PyUnicode_MAX_CHAR_VALUE` of a kind. -/
def capOf : Kind → Nat
  | .ascii => 127
  | .ucs1 => 255
  | .ucs2 => 65535
  | .ucs4 => 0x10ffff

/-- The observable state of a writer. `cap` is `writer->maxchar`, 0 with no buffer yet. -/
structure UWriter where
  text : Str := []
  cap : Nat := 0
  deriving Repr, DecidableEq

/-- `_PyUnicodeWriter_Prepare` for a non-empty write: the buffer is replaced by a wider one only
if `maxchar` does not fit, and `min_char` keeps it at least ASCII. -/
def prepareCap (cap m : Nat) : Nat :=
  if max m 127 > cap then capOf (kindOfMax (max m 127)) else cap

/-- What `PyUnicodeWriter_Finish` returns, with its kind: `_PyUnicodeWriter_Finish`,
unicode_writer.c:587-616, then `_PyUnicode_Result`, unicodeobject.c:718-746. Neither looks at the
characters, so the kind is the buffer's, except that one character of a one-byte buffer becomes the
`LATIN1` singleton, and nothing at all becomes the empty string. -/
def UWriter.finish (w : UWriter) : Str × Kind :=
  match w.text with
  | [] => ([], .ascii)
  | [c] => if w.cap ≤ 255 then ([c], kindOfMax c) else ([c], kindOfMax w.cap)
  | t => (t, kindOfMax w.cap)

/-- `unicode_decode_utf8_impl`, unicodeobject.c:5206-5298, into a writer. It is `utf8DecodeLoop` with
one difference: it also says what had been written when it failed, because those characters decide
how wide the buffer got. `utf8WriterLoop_tie` is the proof that it is otherwise the same loop. -/
def utf8WriterLoop (input : Bytes) (h : ErrHandler) (consumed : Bool) :
    Nat → Nat → List Nat → Str → Str × Py Nat
  | 0, _, _, out => (out, .error .modelFuel)
  | _ + 1, pos, [], out => (out, .ok pos)
  | fuel + 1, pos, rest@(b0 :: tl), out =>
    let onError (reason : String) (stopAt : Nat) : Str × Py Nat :=
      let n := stopAt - pos
      let bad := rest.take n
      let go (w : Str) := utf8WriterLoop input h consumed fuel stopAt (rest.drop n) (out ++ w)
      match h with
      | .ignore => go []
      | .replace => go [0xfffd]
      | .surrogateescape => go (bad.map (· + 0xdc00))
      | _ =>
        match decodeHandlerCall h "utf-8" .utf8 input pos stopAt reason with
        | .error e => (out, .error e)
        | .ok (rep, newpos) =>
          utf8WriterLoop input h consumed fuel newpos (input.drop newpos) (out ++ rep)
    match utf8Step rest with
    | .char c n =>
      utf8WriterLoop input h consumed fuel (pos + n) (rest.drop n) (out ++ [c])
    | .stop =>
      if consumed then (out, .ok pos)
      else onError "unexpected end of data" input.length
    | .err 1 => onError "invalid start byte" (pos + 1)
    | .err code =>
      if code == 2 && consumed && b0 == 0xED && rest.length == 2 &&
          decide (0xA0 ≤ tl.headD 0) && decide (tl.headD 0 ≤ 0xBF) then (out, .ok pos)
      else onError "invalid continuation byte" (pos + code - 1)

/-- `size` of `PyUnicodeWriter_WriteUTF8` and `DecodeUTF8Stateful`: negative means `strlen`. -/
def sizedBytes (b : Bytes) (size : Int) : Bytes :=
  if size < 0 then b.takeWhile (· != 0) else b.take size.toNat

/-- What `ascii_decode` returns: the leading ASCII bytes. -/
def asciiPrefix (b : Bytes) : Bytes := b.takeWhile (· < 128)

/-- `unicode_decode_utf8_impl` from where the ASCII fast path stopped, and the put back of `pos` by
the callers. A failure keeps `w.text` and nothing else undoes: the buffer stays as wide as the
characters made it. -/
def decodeRest (w : UWriter) (cap : Nat) (b pre : Bytes) (h : ErrHandler) (consumed : Bool) :
    UWriter × Py Nat :=
  let (out, r) := utf8WriterLoop b h consumed (b.length + 1 - pre.length) pre.length
    (b.drop pre.length) pre
  let cap' := prepareCap cap (maxCharOf out)
  match r with
  | .ok n => ({ text := w.text ++ out, cap := cap' }, .ok n)
  | .error e => ({ w with cap := cap' }, .error e)

/-- `_PyUnicode_DecodeUTF8Writer`, unicodeobject.c:5404-5441: `Prepare(size, 127)`, then, in a
one-byte buffer, the ASCII fast path, which may finish the job. -/
def decodeWriter (w : UWriter) (b : Bytes) (h : ErrHandler) (consumed : Bool) : UWriter × Py Nat :=
  if b.isEmpty then (w, .ok 0)
  else
    let cap := prepareCap w.cap 127
    if cap ≤ 255 then
      let pre := asciiPrefix b
      if pre.length = b.length then ({ text := w.text ++ pre, cap }, .ok b.length)
      else decodeRest w cap b pre h consumed
    else decodeRest w cap b [] h consumed

/-- An operation of the public API. -/
inductive WOp where
  | char (c : Nat)
  /-- `PyUnicodeWriter_WriteStr`. -/
  | str (o : GObj)
  /-- `PyUnicodeWriter_WriteRepr`, with `none` for NULL. -/
  | repr (o : Option GObj)
  /-- `PyUnicodeWriter_WriteASCII`. A `size` below -1, or a non-ASCII byte, is undefined behaviour
  by its documentation. -/
  | ascii (b : Bytes) (size : Int)
  | ucs4 (s : Str) (size : Int)
  | wide (s : Str) (size : Int)
  | sub (o : GObj) (start stop : Int)
  | utf8 (b : Bytes) (size : Int)
  /-- `PyUnicodeWriter_DecodeUTF8Stateful`. `consumed` is whether `*consumed` was passed, which
  is what makes the decoder stop at an incomplete sequence. -/
  | decode (b : Bytes) (size : Int) (h : ErrHandler) (consumed : Bool)

/-- `_PyUnicodeWriter_WriteStr`, unicode_writer.c:280-309, for an exact `str`: its kind decides,
not its characters. -/
def writeText (w : UWriter) (s : Str) : UWriter :=
  if s.isEmpty then w
  else { text := w.text ++ s, cap := prepareCap w.cap (capOf (canonicalKind s)) }

/-- `_PyUnicodeWriter_WriteASCIIString`, unicode_writer.c:415-478, and what
`_PyLong_FormatWriter` does to the buffer. -/
def writeAsciiText (w : UWriter) (s : Str) : UWriter :=
  if s.isEmpty then w else { text := w.text ++ s, cap := prepareCap w.cap 127 }

/-- `_PyUnicodeWriter_WriteSubstring`, unicode_writer.c:358-389: the characters are scanned only
if the kind of the whole string does not fit. -/
def writeSubstring (w : UWriter) (s : Str) (start stop : Nat) : UWriter :=
  if start = 0 ∧ stop = s.length then writeText w s
  else if stop - start = 0 then w
  else
    let part := (s.drop start).take (stop - start)
    let m := if capOf (canonicalKind s) > w.cap then maxCharOf part else w.cap
    { text := w.text ++ part, cap := prepareCap w.cap m }

/-- The bytes of `WriteASCII`: only -1 means `strlen`. -/
def asciiBytes (b : Bytes) (size : Int) : Bytes :=
  if size = -1 then b.takeWhile (· != 0) else b.take size.toNat

def wideError (ch : Nat) : PyExc :=
  .valueError s!"character U+{hexPlain ch} is not in range [U+0000; U+10ffff]"

/-- `find_maxchar_surrogates` for a four-byte `wchar_t`: the check runs only on a new maximum, which
any out of range character is. -/
def findMaxcharSurrogates : Str → Nat → Py Nat
  | [], m => .ok m
  | ch :: t, m =>
    if ch > m then
      if ch > maxUnicode then .error (wideError ch) else findMaxcharSurrogates t ch
    else findMaxcharSurrogates t m

/-- The characters of `WriteWideChar`: negative means `wcslen`. -/
def sizedWide (s : Str) (size : Int) : Str :=
  if size < 0 then s.takeWhile (· != 0) else s.take size.toNat

/-- A decode whose `*consumed` is not reported. -/
def noConsumed (r : UWriter × Py Nat) : UWriter × Py Nat :=
  (r.1, r.2.map fun _ => 0)

/-- `*consumed` after `PyUnicodeWriter_DecodeUTF8Stateful`: `unicode_decode_utf8_impl` sets it on
success, and unicode_writer.c:532-534 resets it on failure. -/
def consumedOut : Py Nat → Nat
  | .ok n => n
  | .error _ => 0

/-- `PyUnicodeWriter_WriteUCS4`, unicodeobject.c:2271-2330. `ucs4lib_find_max_char` rounds to
the limit of a kind, which `prepareCap` does too. Unlike `WriteWideChar` nothing checks the range in a
release build, on purpose, gh-158445: only a `Py_DEBUG` build scans for it and raises `SystemError`.
This is the release build. -/
def writeUCS4 (w : UWriter) (s : Str) (size : Int) : UWriter × Py Nat :=
  if size < 0 then (w, .error (.valueError "size must be positive"))
  else
    let t := s.take size.toNat
    if t.isEmpty then (w, .ok 0)
    else ({ text := w.text ++ t, cap := prepareCap w.cap (maxCharOf t) }, .ok 0)

/-- `PyUnicodeWriter_WriteWideChar`, unicodeobject.c:1973-2038. -/
def writeWide (w : UWriter) (s : Str) (size : Int) : UWriter × Py Nat :=
  let t := sizedWide s size
  if t.isEmpty then (w, .ok 0)
  else
    match findMaxcharSurrogates t 0 with
    | .error e => (w, .error e)
    | .ok m => ({ text := w.text ++ t, cap := prepareCap w.cap m }, .ok 0)

/-- `PyUnicodeWriter_WriteSubstring`, unicode_writer.c:393-411. -/
def writeSubOp (w : UWriter) (o : GObj) (start stop : Int) : UWriter × Py Nat :=
  match o with
  | .str s =>
    if start < 0 ∨ start > stop then (w, .error (.valueError "invalid start argument"))
    else if stop > s.length then (w, .error (.valueError "invalid end argument"))
    else (writeSubstring w s start.toNat stop.toNat, .ok 0)
  | o => (w, .error (.typeError s!"expect str, not {o.tpName}"))

/-- `PyUnicodeWriter_WriteStr`, unicode_writer.c:313-332. -/
def writeStrOp (w : UWriter) (o : GObj) : UWriter × Py Nat :=
  match o with
  | .str s => (writeText w s, .ok 0)
  | .int v =>
    match longFormat v 10 false with
    | .ok s => (writeAsciiText w s, .ok 0)
    | .error e => (w, .error e)
  | o =>
    match strG reprFuel o with
    | .ok s => (writeText w s, .ok 0)
    | .error e => (w, .error e)

/-- `PyUnicodeWriter_WriteRepr`, unicode_writer.c:336-354. -/
def writeReprOp (w : UWriter) : Option GObj → UWriter × Py Nat
  | none => (writeAsciiText w (lit "<NULL>"), .ok 0)
  | some (.int v) =>
    match longFormat v 10 false with
    | .ok s => (writeAsciiText w s, .ok 0)
    | .error e => (w, .error e)
  | some o =>
    match reprG reprFuel o with
    | .ok s => (writeText w s, .ok 0)
    | .error e => (w, .error e)

/-- One operation: the state after it and what it returned, with `*consumed` on success. -/
def applyOp (w : UWriter) : WOp → UWriter × Py Nat
  | .char c =>
    if c > maxUnicode then (w, .error (.valueError "character must be in range(0x110000)"))
    else ({ text := w.text ++ [c], cap := prepareCap w.cap c }, .ok 0)
  | .str o => writeStrOp w o
  | .repr o => writeReprOp w o
  | .ascii b size => (writeAsciiText w (asciiBytes b size), .ok 0)
  | .ucs4 s size => writeUCS4 w s size
  | .wide s size => writeWide w s size
  | .sub o start stop => writeSubOp w o start stop
  | .utf8 b size => noConsumed (decodeWriter w (sizedBytes b size) .strict false)
  | .decode b size h true => decodeWriter w (sizedBytes b size) h true
  | .decode b size h false => noConsumed (decodeWriter w (sizedBytes b size) h false)

/-- A sequence of operations, with what each one returned. -/
def runOps : UWriter → List WOp → UWriter × List (Py Nat)
  | w, [] => (w, [])
  | w, op :: t =>
    let r := applyOp w op
    let rest := runOps r.1 t
    (rest.1, r.2 :: rest.2)

/-- `PyUnicodeWriter_Create`, unicode_writer.c:105-132. `Prepare` does nothing for length 0, so
that writer has no buffer yet. -/
def writerCreate (length : Int) : Py UWriter :=
  if length < 0 then .error (.valueError "length must be positive")
  else if length > 0 then .ok { cap := 127 }
  else .ok {}

end PyLean.UnicodeObj
