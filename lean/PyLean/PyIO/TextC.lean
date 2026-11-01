import PyLean.PyIO.BytesExtra
import PyLean.PyIO.Newline
import PyLean.PyIO.Double
import PyLean.PyIO.BufRaw
import PyLean.PyIO.StringC

/-!
`Modules/_io/textio.c`: the C `TextIOWrapper` over a C `BytesIO`, CPython 3.14.7.

`TC` holds the fields of `textio` (textio.c:669-727). The encoders are the
specialized ones of textio.c:739-815; decoding covers utf-8, ascii and latin-1
(utf-16 and utf-32 streams are only written). `pending` is `pending_bytes`
flattened; only its concatenation and count are observable.
-/

namespace PyLean.PyIO

open PyLean SM

inductive TEnc where
  | utf8 | ascii | latin1 | utf16 | utf16le | utf16be | utf32 | utf32le | utf32be
  deriving Repr, DecidableEq, Inhabited

def encErr : PyExc := unicodeEncodeError

def le16 (u : Nat) : List Nat := [u % 256, u / 256]
def be16 (u : Nat) : List Nat := [u / 256, u % 256]
def le32 (c : Nat) : List Nat := [c % 256, c / 256 % 256, c / 65536 % 256, c / 16777216]
def be32 (c : Nat) : List Nat := [c / 16777216, c / 65536 % 256, c / 256 % 256, c % 256]

/-- `_PyUnicode_EncodeUTF16`: code units of one code point. -/
def units16 (c : Nat) : List Nat :=
  if c < 0x10000 then [c] else
  let v := c - 0x10000
  [0xD800 + v / 1024, 0xDC00 + v % 1024]

/-- One code point in the encoding, with `errors='strict'` unless `pass`
(`surrogatepass`). -/
def encode1 (enc : TEnc) (pass : Bool) (c : Nat) : Py (List Nat) :=
  if !pass && isSurrogate c then .error encErr else
  match enc with
  | .utf8 => .ok (utf8Enc1 c)
  | .ascii => if c < 128 then .ok [c] else .error encErr
  | .latin1 => if c < 256 then .ok [c] else .error encErr
  | .utf16 | .utf16le => .ok ((units16 c).flatMap le16)
  | .utf16be => .ok ((units16 c).flatMap be16)
  | .utf32 | .utf32le => .ok (le32 c)
  | .utf32be => .ok (be32 c)

def encodeAll (enc : TEnc) (pass : Bool) : List Nat → Py (List Nat)
  | [] => .ok []
  | c :: r =>
    match encode1 enc pass c, encodeAll enc pass r with
    | .error e, _ => .error e
    | _, .error e => .error e
    | .ok a, .ok b => .ok (a ++ b)

/-- `ascii_encode` .. `latin1_encode`, textio.c:739-815: `utf16_encode` and
`utf32_encode` add a BOM at the start of the stream, little-endian here. -/
def encodeFunc (enc : TEnc) (pass start : Bool) (s : List Nat) : Py (List Nat) :=
  match encodeAll enc pass s with
  | .error e => .error e
  | .ok b =>
    match enc, start with
    | .utf16, true => .ok ([0xff, 0xfe] ++ b)
    | .utf32, true => .ok ([0xff, 0xfe, 0, 0] ++ b)
    | _, _ => .ok b

/-- Decoding step of the wrapped codec (`decode(data, final)` with its buffer). -/
def decodeBytes (enc : TEnc) (pass final : Bool) (l : List Nat) : Py (List Nat × List Nat) :=
  match enc with
  | .ascii => if l.all (· < 128) then .ok (l, []) else .error unicodeDecodeError
  | .latin1 => .ok (l, [])
  | _ =>
    match utf8Dec final l with
    | .error e => .error e
    | .ok (cs, t) =>
      if !pass && cs.any isSurrogate then .error unicodeDecodeError else .ok (cs, t)

structure TC where
  b : BState
  ok : Bool
  detached : Bool
  chunk : Nat
  enc : TEnc
  encName : List Nat
  errName : List Nat
  pass : Bool
  readnl : Option (List Nat)
  readuniversal : Bool
  readtranslate : Bool
  writetranslate : Bool
  writenl : Option (List Nat)
  lineBuffering : Bool
  writeThrough : Bool
  telling : Bool
  startOfStream : Bool
  decoded : List Nat
  /-- `self->decoded_chars != NULL`. -/
  decodedNN : Bool
  used : Int
  pending : List Nat
  snapshot : Option (Int × List Nat)
  b2c : Nat × Nat
  dec : NDec
  deriving Repr, DecidableEq, Inhabited

abbrev TM := SM TC

namespace TCm

def checkAttached : TM Unit := do
  let t ← SM.get
  if !t.ok then
    thr (.valueError (if t.detached then "underlying buffer has been detached"
      else "I/O operation on uninitialized object"))

/-- `CHECK_CLOSED`, textio.c:1534-1544. -/
def checkClosed : TM Unit := do
  let t ← SM.get
  if t.b.closed then thr (.valueError "I/O operation on closed file.")

def setDecoded (cs : List Nat) : TM Unit := SM.mod fun t => { t with decoded := cs, used := 0, decodedNN := false }

/-- `textiowrapper_get_decoded_chars`, textio.c:1827-1856. -/
def getDecoded (n : Int) : TM (List Nat) := do
  let t ← SM.get
  let avail : Int := (t.decoded.length : Int) - t.used
  let n := if n < 0 ∨ n > avail then avail else n
  if t.used > 0 ∨ n < avail then
    if t.used < 0 then thr (.named "SystemError" "bad argument to internal function")
    SM.mod fun t => { t with used := t.used + n }
    pure (slice t.decoded t.used.toNat n.toNat)
  else
    SM.mod fun t => { t with used := t.used + n }
    pure t.decoded

/-- The codec stack: `_textiowrapper_decode`, textio.c:932-948. -/
def decodeStep (t : TC) (input : List Nat) (final : Bool) : Py (NDec × List Nat) :=
  match decodeBytes t.enc t.pass final (t.dec.inner.getD [] ++ input) with
  | .error e => .error e
  | .ok (out, rest) =>
    let d := { t.dec with inner := some rest }
    if t.readuniversal then
      let (d, out) := d.pendStep out final
      .ok (NC.record d out)
    else .ok (d, out)

def decState (t : TC) : List Nat × Nat :=
  (t.dec.inner.getD [], if t.readuniversal && t.dec.pendingcr then 1 else 0)

def decSet (t : TC) (st : List Nat × Int) : TC :=
  let pc := t.readuniversal && decide (st.2 % 2 = 1)
  { t with dec := { t.dec with inner := some st.1, pendingcr := pc } }

def decReset (t : TC) : TC :=
  { t with dec := { t.dec with inner := some [], pendingcr := false, seennl := ⟨false, false, false⟩ } }

/-- `_textiowrapper_writeflush`, textio.c:1585-1654. -/
def writeflush : TM Unit := do
  let t ← SM.get
  if t.pending ≠ [] then
    let (b, r) := C.write { t.b with } t.pending
    SM.put { t with b := b, pending := [] }
    match r with
    | .error e => thr e
    | .ok _ => pure ()

/-- `_io_TextIOWrapper_flush_impl`, textio.c:3129-3138. -/
def flush : TM Val := do
  checkAttached
  checkClosed
  SM.mod fun t => { t with telling := true }
  writeflush
  pure .none

/-- `textiowrapper_read_chunk`, textio.c:1861-1986: `false` at EOF. -/
def readChunk (hint : Int) : TM Bool := do
  let t ← SM.get
  let (decBuf, decFlags) := decState t
  let hint : Int :=
    if hint > 0 then
      let (a, b) := t.b2c
      if a ≥ b ∧ b > 0 then dTrunc (dMulNat (dDiv a b) hint.toNat) else hint
    else hint
  let size : Int := max (t.chunk : Int) hint
  let (b, r) := C.read t.b (some size)
  SM.put { t with b := b }
  let chunk : List Nat := match r with
    | .ok v => v.bytesOf
    | _ => []
  let eof := chunk = []
  match decodeStep t chunk eof with
  | .error e => thr e
  | .ok (d, out) =>
    let ratio : Nat × Nat := if out = [] then (0, 1) else (chunk.length, out.length)
    SM.mod fun t => { t with decoded := out, used := 0, dec := d, decodedNN := true, b2c := ratio }
    SM.mod fun t => if t.telling then { t with snapshot := some (decFlags, decBuf ++ chunk) } else t
    pure (!(eof && out = []))

/-- The chunk loop of `_io_TextIOWrapper_read_impl`, textio.c:2052-2074. -/
def readLoop : Nat → Int → List Nat → TM (List Nat)
  | 0, _, _ => thr .modelFuel
  | fuel + 1, remaining, acc => do
    if remaining > 0 then
      let more ← readChunk remaining
      if !more then pure acc else
      let r ← getDecoded remaining
      readLoop fuel (remaining - r.length) (acc ++ r)
    else pure acc

/-- `_io_TextIOWrapper_read_impl`, textio.c:1996-2103. -/
def read (n : Int) : TM Val := do
  checkAttached
  checkClosed
  writeflush
  if n < 0 then
    let t ← SM.get
    let (b, r) := C.read t.b none
    SM.put { t with b := b }
    let chunk : List Nat := match r with
      | .ok v => v.bytesOf
      | _ => []
    match decodeStep t chunk true with
    | .error e => thr e
    | .ok (d, out) =>
      SM.mod fun t => { t with dec := d }
      let r ← getDecoded (-1)
      let t ← SM.get
      if t.snapshot.isSome then
        SM.mod fun t => { t with decoded := [], used := 0, snapshot := none, decodedNN := false }
      pure (.str (r ++ out))
  else
    let r ← getDecoded n
    let t ← SM.get
    let o ← readLoop (t.b.buf.length - t.b.pos + 3) (n - r.length) r
    pure (.str o)

/-- `_PyIO_find_line_ending`, textio.c:2128-2211: `.inl endpos`, or `.inr consumed`. -/
def findEnding (t : TC) (seg : List Nat) : Nat ⊕ Nat :=
  if t.readtranslate then
    match findIdx? seg 10 with
    | some i => .inl (i + 1)
    | none => .inr seg.length
  else if t.readuniversal then
    let rec uni (i : Nat) : List Nat → Option Nat
      | [] => none
      | 10 :: _ => some (i + 1)
      | 13 :: 10 :: _ => some (i + 2)
      | 13 :: _ => some (i + 1)
      | _ :: r => uni (i + 1) r
    match uni 0 seg with
    | some e => .inl e
    | none => .inr seg.length
  else
    let nl := t.readnl.getD []
    let p := findFrom seg nl 0
    if p ≥ 0 then .inl (p.toNat + nl.length)
    else if nl.length = 2 ∧ seg.getLast? = some 13 then .inr (seg.length - 1)
    else .inr seg.length

/-- The main loop of `_textiowrapper_readline`, textio.c:2223-2318: `acc` is
`chunks`, `rem` is `remaining`, `chunked` their length. -/
def lineLoop (limit : Int) : Nat → List Nat → Option (List Nat) → Int → TM (List Nat)
  | 0, _, _, _ => thr .modelFuel
  | fuel + 1, acc, rem, chunked => do
    -- first, get some data if necessary
    let t ← SM.get
    let res ← if t.decoded = [] then
        let more ← refill (t.b.buf.length - t.b.pos + 3)
        pure more
      else pure true
    if !res then
      setDecoded []
      SM.mod fun t => { t with snapshot := none }
      pure (acc ++ rem.getD [])
    else
      let t ← SM.get
      let (line, start, offset) : List Nat × Int × Int := match rem with
        | none => (t.decoded, t.used, 0)
        | some r => (r ++ t.decoded, 0, r.length)
      if start < 0 then thr (.named "SystemError" "bad argument to internal function") else
      let seg := line.drop start.toNat
      match findEnding t seg with
      | .inl e =>
        let endpos : Int := e + start
        let endpos := if limit ≥ 0 ∧ (endpos - start) + chunked ≥ limit then start + limit - chunked else endpos
        finish acc line start endpos offset
      | .inr consumed =>
        let endpos : Int := consumed + start
        if limit ≥ 0 ∧ (endpos - start) + chunked ≥ limit then
          finish acc line start (start + limit - chunked) offset
        else
          let piece := slice line start.toNat (endpos - start).toNat
          let (acc, chunked) := if endpos > start then (acc ++ piece, chunked + piece.length) else (acc, chunked)
          let rem : Option (List Nat) := if endpos < line.length then some (line.drop endpos.toNat) else none
          setDecoded []
          lineLoop limit fuel acc rem chunked
where
  refill : Nat → TM Bool
    | 0 => thr .modelFuel
    | fuel + 1 => do
      let more ← readChunk 0
      if !more then pure false else
      let t ← SM.get
      if t.decoded = [] then refill fuel else pure true
  finish (acc line : List Nat) (start endpos offset : Int) : TM (List Nat) := do
    SM.mod fun t => { t with used := endpos - offset }
    pure (acc ++ slice line start.toNat (endpos - start).toNat)

/-- `_textiowrapper_readline`, textio.c:2214-2370. -/
def readlineRaw (limit : Int) : TM (List Nat) := do
  checkClosed
  writeflush
  let t ← SM.get
  lineLoop limit (t.b.buf.length - t.b.pos + t.decoded.length + 3) [] none 0

/-- `textiowrapper_iternext_lock_held`, textio.c:3193-3229. -/
def next : TM Val := do
  checkAttached
  SM.mod fun t => { t with telling := false }
  let l ← readlineRaw (-1)
  if l = [] then
    SM.mod fun t => { t with snapshot := none, telling := true }
    thr .stopIteration
  else pure (.str l)

/-- `_io_TextIOWrapper_write_impl`, textio.c:1664-1815. -/
def write (s : List Nat) : TM Val := do
  checkAttached
  checkClosed
  let t ← SM.get
  let textlen := s.length
  let haslf := (((t.writetranslate && t.writenl.isSome) || t.lineBuffering) && s.contains 10)
  let text := if haslf && t.writetranslate && t.writenl.isSome then replaceLf (t.writenl.getD []) s else s
  let needflush := t.lineBuffering && (haslf || text.contains 13)
  match encodeFunc t.enc t.pass t.startOfStream text with
  | .error e => thr e
  | .ok b =>
    SM.mod fun t => { t with startOfStream := false }
    let n := b.length
    if n ≥ t.chunk then writeflush
    SM.mod fun t => { t with pending := t.pending ++ b }
    let t ← SM.get
    if t.pending.length ≥ t.chunk ∨ needflush ∨ t.writeThrough then writeflush
    SM.mod fun t =>
      if t.snapshot.isSome then { t with decoded := [], used := 0, snapshot := none, decodedNN := false } else t
    SM.mod decReset
    pure (.int textlen)

/-- `textiowrapper_build_cookie`, textio.c:2454-2466 (LP64, little-endian). -/
def buildCookie (start decFlags feed skip : Int) (eof : Bool) : Int :=
  (start % 2 ^ 64) + (decFlags % 2 ^ 32) * 2 ^ 64 + (feed % 2 ^ 32) * 2 ^ 96 +
    (skip % 2 ^ 32) * 2 ^ 128 + (if eof then 1 else 0) * 2 ^ 160

/-- `int` from 32 bits, `Py_off_t` from 64. -/
def s32 (x : Int) : Int := if x ≥ 2 ^ 31 then x - 2 ^ 32 else x
def s64 (x : Int) : Int := if x ≥ 2 ^ 63 then x - 2 ^ 64 else x

/-- `textiowrapper_parse_cookie`, textio.c:2430-2451. -/
def parseCookie (c : Int) : Py (Int × Int × Int × Int × Bool) :=
  if c ≥ 2 ^ 168 then .error (.overflowError "int too big to convert") else
  .ok (s64 (c % 2 ^ 64), s32 (c / 2 ^ 64 % 2 ^ 32), s32 (c / 2 ^ 96 % 2 ^ 32),
    s32 (c / 2 ^ 128 % 2 ^ 32), c / 2 ^ 160 % 256 ≠ 0)

/-- `_textiowrapper_decoder_setstate`, textio.c:2469-2490. -/
def decoderSetstate (start flags : Int) : TM Unit :=
  SM.mod fun t => if start = 0 ∧ flags = 0 then decReset t else decSet t ([], flags)

/-- The fast search of `_io_TextIOWrapper_tell_impl`, textio.c:2835-2862. -/
def tellSkip (next : List Nat) (start : Int) : Nat → Int → Int → Int → Int → TM (Int × Int × Int)
  | 0, _, _, _, _ => thr .modelFuel
  | fuel + 1, skipBytes, skipBack, flags, cts => do
    if skipBytes > 0 then
      decoderSetstate start flags
      let t ← SM.get
      match decodeStep t (next.take skipBytes.toNat) false with
      | .error e => thr e
      | .ok (d, out) =>
        SM.mod fun t => { t with dec := d }
        let t ← SM.get
        let n : Int := out.length
        if n ≤ cts then
          let (b, dd) := decState t
          if b = [] then pure (skipBytes, dd, cts - n)
          else tellSkip next start fuel (skipBytes - b.length) 1 flags cts
        else tellSkip next start fuel (skipBytes - skipBack) (skipBack * 2) flags cts
    else
      decoderSetstate start flags
      pure (0, flags, cts)

/-- The byte loop of `tell`, textio.c:2880-2901: `(start, flags, feed, decoded, skip, broke)`. -/
def tellFeed : List Nat → Int → Int → Int → Int → Int → TM (Int × Int × Int × Int × Int × Bool)
  | [], sp, fl, bf, cd, cts => pure (sp, fl, bf, cd, cts, false)
  | x :: xs, sp, fl, bf, cd, cts => do
    let t ← SM.get
    match decodeStep t [x] false with
    | .error e => thr e
    | .ok (d, out) =>
      SM.mod fun t => { t with dec := d }
      let t ← SM.get
      let cd := cd + out.length
      let bf := bf + 1
      let (buf, dfl) := decState t
      let (sp, fl, bf, cd, cts) :=
        if buf = [] ∧ cd ≤ cts then (sp + bf, (dfl : Int), 0, 0, cts - cd) else (sp, fl, bf, cd, cts)
      if cd ≥ cts then pure (sp, fl, bf, cd, cts, true)
      else tellFeed xs sp fl bf cd cts

/-- `_io_TextIOWrapper_tell_impl`, textio.c:2742-2966. -/
def tell : TM Int := do
  checkAttached
  checkClosed
  let t ← SM.get
  if !t.telling then thr (osError "telling position disabled by next() call")
  writeflush
  let _ ← flush
  let t ← SM.get
  let pos : Int := t.b.pos
  match t.snapshot with
  | none => pure pos
  | some (flags, next) =>
    let start := pos - next.length
    if t.used = 0 then pure (buildCookie start flags 0 0 false) else
    let saved := t.dec
    let cts := t.used
    let skip : Int := dTrunc (dMulNat (dDiv t.b2c.1 t.b2c.2) cts.toNat)
    let r ← SM.attempt (do
      let (skip, flags, cts) ← tellSkip next start (skip.toNat + 2) skip 1 flags cts
      let start := start + skip
      if cts = 0 then pure (buildCookie start flags 0 0 false) else
      let (sp, fl, bf, cd, cts, broke) ← tellFeed (next.drop skip.toNat) start flags 0 0 cts
      if broke then pure (buildCookie sp fl bf cts false) else
      let t ← SM.get
      match decodeStep t [] true with
      | .error e => thr e
      | .ok (d, out) =>
        SM.mod fun t => { t with dec := d }
        if cd + out.length < cts then thr (osError "can't reconstruct logical file position")
        pure (buildCookie sp fl bf cts true))
    SM.mod fun t => { t with dec := { t.dec with inner := saved.inner, pendingcr := saved.pendingcr } }
    match r with
    | .error e => thr e
    | .ok v => pure v

/-- `_textiowrapper_encoder_setstate`/`_reset`, textio.c:2493-2517. -/
def encoderReset (atStart : Bool) : TM Unit :=
  SM.mod fun t => { t with startOfStream := atStart }

/-- `_io_TextIOWrapper_seek_impl`, textio.c:2544-2729, after `whence` is converted. -/
def seek (cookie whence : Int) : TM Val := do
  checkAttached
  checkClosed
  let c ← (do
    if whence = 1 then
      if cookie ≠ 0 then thr (unsupportedOp "can't do nonzero cur-relative seeks")
      tell
    else if whence = 2 then
      if cookie ≠ 0 then thr (unsupportedOp "can't do nonzero end-relative seeks")
      pure (-1)
    else if whence = 0 then pure cookie
    else thr (.valueError s!"invalid whence ({whence}, should be 0, 1 or 2)") : TM Int)
  if whence = 2 then
    let _ ← flush
    setDecoded []
    SM.mod fun t => { t with snapshot := none }
    SM.mod decReset
    let t ← SM.get
    let (b, r) := C.seek t.b 0 2
    SM.put { t with b := b }
    let p : Int := match r with
      | .ok (.int v) => v
      | _ => 0
    encoderReset (p = 0)
    pure (.int p)
  else
    if c < 0 then thr (.valueError s!"negative seek position {c}")
    let _ ← flush
    match parseCookie c with
    | .error e => thr e
    | .ok (start, flags, feed, skip, eof) =>
      let t ← SM.get
      let (b, r) := C.seek t.b start 0
      SM.put { t with b := b }
      match r with
      | .error e => thr e
      | .ok _ =>
        setDecoded []
        SM.mod fun t => { t with snapshot := none }
        decoderSetstate start flags
        if skip ≠ 0 then
          let t ← SM.get
          let (b, r) := C.read t.b (some feed)
          SM.put { t with b := b }
          let chunk : List Nat := match r with
            | .ok v => v.bytesOf
            | _ => []
          SM.mod fun t => { t with snapshot := some (flags, chunk) }
          let t ← SM.get
          match decodeStep t chunk eof with
          | .error e => thr e
          | .ok (d, out) =>
            SM.mod fun t => { t with dec := d, decoded := out, used := 0, decodedNN := true }
            if (out.length : Int) < skip then thr (osError "can't restore logical file position")
            SM.mod fun t => { t with used := skip }
        else
          SM.mod fun t => { t with snapshot := some (flags, []) }
        encoderReset (start = 0 ∧ flags = 0)
        pure (.int c)

/-- `_io_TextIOWrapper_truncate_impl`, textio.c:2976-2986. -/
def truncate (p : Option Int) : TM Val := do
  checkAttached
  let _ ← flush
  let t ← SM.get
  let (b, r) := C.truncate t.b p
  SM.put { t with b := b }
  match r with
  | .error e => thr e
  | .ok v => pure v

/-- `_io_TextIOWrapper_close_impl`, textio.c:3146-3190. -/
def close : TM Val := do
  checkAttached
  let t ← SM.get
  if t.b.closed then pure .none else
  let fl ← SM.attempt flush
  let t ← SM.get
  let (b, r) := C.step t.b .close
  SM.put { t with b := b }
  match r, fl with
  | .error e, _ => thr e
  | .ok _, .error e => thr e
  | .ok _, .ok _ => pure .none

/-- `_io_TextIOWrapper_detach_impl`, textio.c:1568-1580. -/
def detach : TM Val := do
  checkAttached
  let _ ← flush
  SM.mod fun t => { t with detached := true, ok := false }
  pure .none

/-- `set_newline` and `_io_TextIOWrapper___init___impl`, textio.c:859-892, :1104-1269. -/
def init (data : List Nat) (enc : TEnc) (encName errName : List Nat) (pass : Bool) (nl : Option (List Nat))
    (lb wt : Bool) (chunk : Nat) : Py TC :=
  let legal := nl = none ∨ nl = some [] ∨ nl = some [10] ∨ nl = some [13] ∨ nl = some [13, 10]
  if !legal then .error (illegalNewline (nl.getD [])) else
  let ru := nl.isNone || nl = some []
  let rt := nl.isNone
  .ok { b := bInit data, ok := true, detached := false, chunk := chunk, enc := enc, encName := encName, errName := errName, pass := pass
        readnl := nl, readuniversal := ru, readtranslate := rt
        writetranslate := nl ≠ some []
        writenl := if !ru && nl ≠ some [10] then nl else none
        lineBuffering := lb, writeThrough := wt, telling := true, startOfStream := true
        decoded := [], decodedNN := false, used := 0, pending := [], snapshot := none, b2c := (0, 1)
        dec := NDec.fresh (some []) rt }

end TCm

end PyLean.PyIO
