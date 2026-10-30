import PyLean.PyIO.BytesIO
import PyLean.PyIO.Text
import PyLean.PyIO.Double

/-!
`_pyio.StringIO` (`Lib/_pyio.py:2716-2764`): a `TextIOWrapper`
(`Lib/_pyio.py:2033-2714`) over a `_pyio.BytesIO`, with encoding UTF-8,
errors `surrogatepass`, no line buffering, `os.linesep == '\n'`.

The model keeps the wrapper's fields (`_decoded_chars`,
`_decoded_chars_used`, `_snapshot`, `_telling`, `_decoder`, `_b2cratio`,
the newline configuration) and the `BState` of the underlying `BytesIO`.
The decoder is the UTF-8 incremental decoder (`codecs.BufferedIncrementalDecoder`,
`Lib/codecs.py:322-350`), wrapped in `IncrementalNewlineDecoder`
(`Lib/_pyio.py:1948-2030`) when reading in universal mode. The UTF-8
encoder is stateless, so `_encoder` and `_reset_encoder` are not modelled.
`_CHUNK_SIZE` is 2048.
-/

namespace PyLean.PyIO

open PyLean

/-- The decoder: `ubuf` is the UTF-8 decoder's byte buffer; `nl` says
whether it is wrapped in an `IncrementalNewlineDecoder`. -/
structure Dec where
  ubuf : List Nat
  nl : Bool
  translate : Bool
  pendingcr : Bool
  seennl : NlKinds
  deriving Repr, DecidableEq, Inhabited

namespace Dec

def none0 : NlKinds := ⟨false, false, false⟩

/-- `IncrementalNewlineDecoder.decode` (_pyio.py:1962-1990) over
`BufferedIncrementalDecoder.decode` (codecs.py:329-335). On a decoding error
nothing changes. -/
def decode (d : Dec) (input : List Nat) (final : Bool) : Py (Dec × List Nat) := do
  let (out, rest) ← utf8Dec final (d.ubuf ++ input)
  let d := { d with ubuf := rest }
  if !d.nl then return (d, out)
  let (out, d) := if d.pendingcr && (out ≠ [] || final) then (13 :: out, { d with pendingcr := false })
    else (out, d)
  let (out, d) := if out.getLast? = some 13 && !final then (out.dropLast, { d with pendingcr := true })
    else (out, d)
  let d := { d with seennl := d.seennl.union (nlKinds out) }
  return (d, if d.translate then translateNl out else out)

/-- `getstate()` (_pyio.py:1992-2000; codecs.py:343-345). -/
def getstate (d : Dec) : List Nat × Nat := (d.ubuf, if d.nl && d.pendingcr then 1 else 0)

/-- `setstate((buf, flag))` (_pyio.py:2002-2006; codecs.py:347-350). -/
def setstate (d : Dec) (st : List Nat × Nat) : Dec :=
  if d.nl then { d with ubuf := st.1, pendingcr := st.2 % 2 = 1 } else { d with ubuf := st.1 }

/-- `reset()` (_pyio.py:2008-2012; codecs.py:337-339). -/
def reset (d : Dec) : Dec :=
  if d.nl then { d with ubuf := [], pendingcr := false, seennl := none0 } else { d with ubuf := [] }

end Dec

structure TState where
  b : BState
  decoded : List Nat
  used : Nat
  snapshot : Option (Nat × List Nat)
  telling : Bool
  decoder : Option Dec
  /-- `_b2cratio` as `len(input_chunk) / len(decoded_chars)` (`(0, 1)` is 0.0). -/
  b2c : Nat × Nat
  readuniversal : Bool
  readtranslate : Bool
  readnl : Option (List Nat)
  writetranslate : Bool
  writenl : List Nat
  deriving Repr, DecidableEq, Inhabited

namespace TP

def closedDot : PyExc := .valueError "I/O operation on closed file."

/-- `_get_decoder` (_pyio.py:2285-2291). -/
def getDecoder (t : TState) : TState × Dec :=
  match t.decoder with
  | some d => (t, d)
  | none =>
    let d : Dec := ⟨[], t.readuniversal, t.readtranslate, false, Dec.none0⟩
    ({ t with decoder := some d }, d)

def setDecoded (t : TState) (cs : List Nat) : TState := { t with decoded := cs, used := 0 }

/-- `_get_decoded_chars(n)` (_pyio.py:2299-2307). -/
def getDecodedChars (t : TState) (n : Option Nat) : TState × List Nat :=
  let rest := t.decoded.drop t.used
  let cs := match n with
    | none => rest
    | some n => rest.take n
  ({ t with used := t.used + cs.length }, cs)

/-- `flush()` (_pyio.py:2231-2233): `BytesIO.flush` is `IOBase.flush`, which
checks `closed`. -/
def flush (t : TState) : Py TState :=
  if t.b.closed then .error closedDot else .ok { t with telling := true }

/-- `_read_chunk` (_pyio.py:2322-2360); `read1` is `read` for `BytesIO`. -/
def readChunk (t : TState) : TState × Py Bool :=
  match t.decoder with
  | none => (t, .error (.valueError "no decoder"))
  | some d =>
    let (decBuf, decFlags) := d.getstate
    match P.readRaw t.b (some 2048) with
    | (b', .error e) => ({ t with b := b' }, .error e)
    | (b', .ok chunk) =>
      let t := { t with b := b' }
      let eof := chunk = []
      match d.decode chunk eof with
      | .error e => (t, .error e)
      | .ok (d2, out) =>
        let ratio : Nat × Nat := if out = [] then (0, 1) else (chunk.length, out.length)
        let t := { (setDecoded t out) with decoder := some d2, b2c := ratio }
        let t := if t.telling then { t with snapshot := some (decFlags, decBuf ++ chunk) } else t
        (t, .ok (!eof))

/-- The `while len(result) < size and not eof` loop of `read` (_pyio.py:2560-2565). -/
def readLoop (size : Nat) : TState → List Nat → Nat → TState × Py (List Nat)
  | t, _, 0 => (t, .error .modelFuel)
  | t, res, fuel + 1 =>
    if res.length < size then
      match readChunk t with
      | (t, .error e) => (t, .error e)
      | (t, .ok more) =>
        let (t, cs) := getDecodedChars t (some (size - res.length))
        let res := res ++ cs
        if more then readLoop size t res fuel else (t, .ok res)
    else (t, .ok res)

/-- `read(size)` (_pyio.py:2537-2566). -/
def read (t : TState) (size : Option Int) : TState × Py Val :=
  if t.b.closed then (t, .error closedDot) else
  let size := size.getD (-1)
  let (t, d) := getDecoder t
  if size < 0 then
    match P.readRaw t.b none with
    | (b', .error e) => ({ t with b := b' }, .error e)
    | (b', .ok chunk) =>
      let (t, pre) := getDecodedChars { t with b := b' } none
      match d.decode chunk true with
      | .error e => (t, .error e)
      | .ok (d2, out) =>
        let t := { t with decoder := some d2 }
        let t := if t.snapshot.isSome then { (setDecoded t []) with snapshot := none } else t
        (t, .ok (.str (pre ++ out)))
  else
    let (t, res) := getDecodedChars t (some size.toNat)
    match readLoop size.toNat t res (t.b.buf.length - t.b.pos + 3) with
    | (t, .error e) => (t, .error e)
    | (t, .ok r) => (t, .ok (.str r))

/-- The line-ending search of `readline` (_pyio.py:2604-2647): `some endpos`
or the next `start`. -/
def search (t : TState) (line : List Nat) (start : Nat) : Option Nat × Nat :=
  if t.readtranslate then
    let p := findFrom line [10] start
    if p ≥ 0 then (some (p.toNat + 1), start) else (none, line.length)
  else if t.readuniversal then
    let nlpos := findFrom line [10] start
    let crpos := findFrom line [13] start
    if crpos = -1 then
      if nlpos = -1 then (none, line.length) else (some (nlpos.toNat + 1), start)
    else if nlpos = -1 then (some (crpos.toNat + 1), start)
    else if nlpos < crpos then (some (nlpos.toNat + 1), start)
    else if nlpos = crpos + 1 then (some (crpos.toNat + 2), start)
    else (some (crpos.toNat + 1), start)
  else
    let nl := t.readnl.getD []
    let p := findFrom line nl 0
    if p ≥ 0 then (some (p.toNat + nl.length), start) else (none, start)

/-- `while self._read_chunk(): if self._decoded_chars: break` (_pyio.py:2654-2656). -/
def chunkLoop : TState → Nat → TState × Py Unit
  | t, 0 => (t, .error .modelFuel)
  | t, fuel + 1 =>
    match readChunk t with
    | (t, .error e) => (t, .error e)
    | (t, .ok more) => if more && t.decoded = [] then chunkLoop t fuel else (t, .ok ())

/-- The end of `readline` (_pyio.py:2667-2672). -/
def finishLine (t : TState) (size : Int) (line : List Nat) (endpos : Nat) : TState × Py (List Nat) :=
  let endpos := if size ≥ 0 ∧ (endpos : Int) > size then size.toNat else endpos
  let n := line.length - endpos
  if t.used < n then (t, .error (.assertionError "rewind decoded_chars out of bounds"))
  else ({ t with used := t.used - n }, .ok (line.take endpos))

/-- The `while True` loop of `readline` (_pyio.py:2601-2665). -/
def lineLoop (size : Int) : TState → List Nat → Nat → Nat → TState × Py (List Nat)
  | t, _, _, 0 => (t, .error .modelFuel)
  | t, line, start, fuel + 1 =>
    match search t line start with
    | (some endpos, _) => finishLine t size line endpos
    | (none, start) =>
      if size ≥ 0 ∧ (line.length : Int) ≥ size then finishLine t size line size.toNat else
      match chunkLoop t (t.b.buf.length - t.b.pos + 3) with
      | (t, .error e) => (t, .error e)
      | (t, .ok ()) =>
        if t.decoded ≠ [] then
          let (t, cs) := getDecodedChars t none
          lineLoop size t (line ++ cs) start fuel
        else ({ (setDecoded t []) with snapshot := none }, .ok line)

/-- `readline(size)` (_pyio.py:2582-2672). -/
def readlineRaw (t : TState) (size : Option Int) : TState × Py (List Nat) :=
  if t.b.closed then (t, .error (.valueError "read from closed file")) else
  let size := size.getD (-1)
  let (t, line) := getDecodedChars t none
  let (t, _) := getDecoder t
  lineLoop size t line 0 (t.b.buf.length - t.b.pos + t.decoded.length + 3)

/-- `__next__` (_pyio.py:2574-2580). -/
def next (t : TState) : TState × Py Val :=
  match readlineRaw { t with telling := false } none with
  | (t, .error e) => (t, .error e)
  | (t, .ok l) =>
    if l = [] then ({ t with snapshot := none, telling := true }, .error .stopIteration)
    else (t, .ok (.str l))

/-- `for line in self` of `IOBase.readlines` (_pyio.py:566-580). -/
def readlinesLoop (hint : Option Int) : TState → Int → List Atom → Nat → TState × Py Val
  | t, _, _, 0 => (t, .error .modelFuel)
  | t, n, acc, fuel + 1 =>
    match next t with
    | (t, .error .stopIteration) => (t, .ok (.list acc.reverse))
    | (t, .error e) => (t, .error e)
    | (t, .ok v) =>
      let l := v.strOf
      let acc := Atom.str l :: acc
      let n := n + l.length
      match hint with
      | some h => if n ≥ h then (t, .ok (.list acc.reverse)) else readlinesLoop hint t n acc fuel
      | none => readlinesLoop hint t n acc fuel

def readlines (t : TState) (hint : Option Int) : TState × Py Val :=
  if t.b.closed then (t, .error closedDot) else
  let hint := match hint with
    | some h => if h ≤ 0 then none else some h
    | none => none
  readlinesLoop hint t 0 [] (t.b.buf.length - t.b.pos + t.decoded.length + 3)

/-- `write(s)` (_pyio.py:2251-2272). -/
def write (t : TState) (s : List Nat) : TState × Py Val :=
  if t.b.closed then (t, .error (.valueError "write to closed file")) else
  let length := s.length
  let haslf := t.writetranslate && s.contains 10
  let s := if haslf && t.writetranslate && t.writenl ≠ [10] then replaceLf t.writenl s else s
  match P.write t.b (utf8Enc s) with
  | (b', .error e) => ({ t with b := b' }, .error e)
  | (b', .ok _) =>
    let t := { t with b := b' }
    let t := if t.snapshot.isSome then { (setDecoded t []) with snapshot := none } else t
    let t := { t with decoder := t.decoder.map Dec.reset }
    (t, .ok (.int length))

/-- `_pack_cookie` (_pyio.py:2362-2368). -/
def pack (position decFlags bytesToFeed : Nat) (needEof : Bool) (charsToSkip : Nat) : Nat :=
  position ||| (decFlags <<< 64) ||| (bytesToFeed <<< 128) ||| (charsToSkip <<< 192) |||
    ((if needEof then 1 else 0) <<< 256)

/-- The fast search of `tell` (_pyio.py:2401-2423): returns the decoder
(always, since decoding updates `seennl` even when a later call fails) and
`skip_bytes`, `dec_flags`, `chars_to_skip`. -/
def tellSkip (nextInput : List Nat) : Dec → Int → Nat → Nat → Nat → Nat → Dec × Py (Int × Nat × Nat)
  | d, _, _, _, _, 0 => (d, .error .modelFuel)
  | d, skipBytes, skipBack, decFlags, charsToSkip, fuel + 1 =>
    if skipBytes > 0 then
      let d := d.setstate ([], decFlags)
      match d.decode (nextInput.take skipBytes.toNat) false with
      | .error e => (d, .error e)
      | .ok (d, out) =>
        let n := out.length
        if n ≤ charsToSkip then
          let (b, dd) := d.getstate
          if b = [] then (d, .ok (skipBytes, dd, charsToSkip - n))
          else tellSkip nextInput d (skipBytes - b.length) 1 decFlags charsToSkip fuel
        else tellSkip nextInput d (skipBytes - skipBack) (skipBack * 2) decFlags charsToSkip fuel
    else (d.setstate ([], decFlags), .ok (0, decFlags, charsToSkip))

/-- The byte-by-byte loop of `tell` (_pyio.py:2429-2450) over
`(start_pos, start_flags, bytes_fed, chars_decoded, chars_to_skip)`; the
final flag says whether the loop ended with `break`. -/
def tellFeed : List Nat → Dec → Nat → Nat → Nat → Nat → Nat →
    Dec × Py (Nat × Nat × Nat × Nat × Nat × Bool)
  | [], d, sp, sf, bf, cd, cts => (d, .ok (sp, sf, bf, cd, cts, false))
  | x :: xs, d, sp, sf, bf, cd, cts =>
    let bf := bf + 1
    match d.decode [x] false with
    | .error e => (d, .error e)
    | .ok (d, out) =>
      let cd := cd + out.length
      let (decBuffer, decFlags) := d.getstate
      let (sp, sf, bf, cd, cts) :=
        if decBuffer = [] ∧ cd ≤ cts then (sp + bf, decFlags, 0, 0, cts - cd) else (sp, sf, bf, cd, cts)
      if cd ≥ cts then (d, .ok (sp, sf, bf, cd, cts, true))
      else tellFeed xs d sp sf bf cd cts

/-- The `try` body of `tell` after `saved_state` (_pyio.py:2387-2457). -/
def tellBody (t : TState) (d : Dec) (position : Nat) (decFlags : Nat) (nextInput : List Nat)
    (charsToSkip : Nat) : Dec × Py Nat :=
  let skipBytes := dTrunc (dMulNat (dDiv t.b2c.1 t.b2c.2) charsToSkip)
  if skipBytes > nextInput.length then (d, .error (.assertionError "")) else
  match tellSkip nextInput d skipBytes 1 decFlags charsToSkip (skipBytes + 2) with
  | (d, .error e) => (d, .error e)
  | (d, .ok (skipBytes, decFlags, charsToSkip)) =>
    let skipBytes := skipBytes.toNat
    let startPos := position + skipBytes
    if charsToSkip = 0 then (d, .ok (pack startPos decFlags 0 false 0)) else
    match tellFeed (nextInput.drop skipBytes) d startPos decFlags 0 0 charsToSkip with
    | (d, .error e) => (d, .error e)
    | (d, .ok (sp, sf, bf, _, cts, true)) => (d, .ok (pack sp sf bf false cts))
    | (d, .ok (sp, sf, bf, cd, cts, false)) =>
      match d.decode [] true with
      | .error e => (d, .error e)
      | .ok (d, out) =>
        let cd := cd + out.length
        if cd < cts then (d, .error (osError "can't reconstruct logical file position"))
        else (d, .ok (pack sp sf bf true cts))

/-- `tell()` (_pyio.py:2370-2460). -/
def tell (t : TState) : TState × Py Int :=
  if !t.telling then (t, .error (osError "telling position disabled by next() call")) else
  match flush t with
  | .error e => (t, .error e)
  | .ok t =>
  let position := t.b.pos
  match t.decoder, t.snapshot with
  | some d, some (decFlags, nextInput) =>
    if position < nextInput.length then (t, .error .modelFuel) else  -- unreachable
    let position := position - nextInput.length
    let charsToSkip := t.used
    if charsToSkip = 0 then (t, .ok (pack position decFlags 0 false 0)) else
    let saved := d.getstate
    let (d, r) := tellBody t d position decFlags nextInput charsToSkip
    ({ t with decoder := some (d.setstate saved) }, r.map (fun n => (n : Int)))
  | _, _ =>
    if t.decoded ≠ [] then (t, .error (.assertionError "pending decoded text"))
    else (t, .ok position)

/-- `_unpack_cookie` (_pyio.py:2364-2369) for a cookie `>= 0`. -/
def unpack (c : Nat) : Nat × Nat × Nat × Bool × Nat :=
  let position := c % 2 ^ 64
  let rest := c / 2 ^ 64
  let decFlags := rest % 2 ^ 64
  let rest := rest / 2 ^ 64
  let bytesToFeed := rest % 2 ^ 64
  let rest := rest / 2 ^ 64
  (position, decFlags, bytesToFeed, rest / 2 ^ 64 ≠ 0, rest % 2 ^ 64)

/-- `seek(cookie, 0)` for `cookie >= 0` after the checks (_pyio.py:2508-2535). -/
def seekCookie (t : TState) (cookie : Nat) : TState × Py Val :=
  match flush t with
  | .error e => (t, .error e)
  | .ok t =>
  let (startPos, decFlags, bytesToFeed, needEof, charsToSkip) := unpack cookie
  let (b, _) := P.seek t.b startPos 0
  let t := { setDecoded { t with b := b } [] with snapshot := none }
  let t :=
    if cookie = 0 ∧ t.decoder.isSome then { t with decoder := t.decoder.map Dec.reset }
    else if t.decoder.isSome ∨ decFlags ≠ 0 ∨ charsToSkip ≠ 0 then
      let (t, d) := getDecoder t
      { t with decoder := some (d.setstate ([], decFlags)), snapshot := some (decFlags, []) }
    else t
  if charsToSkip ≠ 0 then
    match P.readRaw t.b (some bytesToFeed) with
    | (b, .error e) => ({ t with b := b }, .error e)
    | (b, .ok chunk) =>
      let t := { t with b := b }
      let d := (t.decoder.getD default)
      match d.decode chunk needEof with
      | .error e => (t, .error e)
      | .ok (d, out) =>
        let t := { (setDecoded t out) with decoder := some d, snapshot := some (decFlags, chunk) }
        if out.length < charsToSkip then (t, .error (osError "can't restore logical file position"))
        else ({ t with used := charsToSkip }, .ok (.int cookie))
  else (t, .ok (.int cookie))

/-- `seek(cookie, whence)` (_pyio.py:2470-2535). -/
def seek (t : TState) (cookie whence : Int) : TState × Py Val :=
  if t.b.closed then (t, .error (.valueError "tell on closed file")) else
  if whence = 1 then
    if cookie ≠ 0 then (t, .error (unsupportedOp "can't do nonzero cur-relative seeks")) else
    match tell t with
    | (t, .error e) => (t, .error e)
    | (t, .ok c) =>
      if c < 0 then (t, .error (.valueError s!"negative seek position {c}")) else seekCookie t c.toNat
  else if whence = 2 then
    if cookie ≠ 0 then (t, .error (unsupportedOp "can't do nonzero end-relative seeks")) else
    match flush t with
    | .error e => (t, .error e)
    | .ok t =>
      let (b, r) := P.seek t.b 0 2
      let t := { setDecoded { t with b := b } [] with snapshot := none }
      ({ t with decoder := t.decoder.map Dec.reset }, r)
  else if whence ≠ 0 then (t, .error (.valueError s!"unsupported whence ({whence})"))
  else if cookie < 0 then (t, .error (.valueError s!"negative seek position {cookie}"))
  else seekCookie t cookie.toNat

/-- `truncate(pos)` (_pyio.py:2462-2466). -/
def truncate (t : TState) (pos : Option Int) : TState × Py Val :=
  match flush t with
  | .error e => (t, .error e)
  | .ok t =>
    match pos with
    | some p => let (b, r) := P.truncate t.b (some p); ({ t with b := b }, r)
    | none =>
      match tell t with
      | (t, .error e) => (t, .error e)
      | (t, .ok p) => let (b, r) := P.truncate t.b (some p); ({ t with b := b }, r)

/-- `StringIO.getvalue()` (_pyio.py:2739-2747). -/
def getvalue (t : TState) : TState × Py Val :=
  match flush t with
  | .error e => (t, .error e)
  | .ok t =>
    let (t, d) := getDecoder t
    let old := d.getstate
    let d := d.reset
    match d.decode t.b.buf true with
    | .error e => ({ t with decoder := some (d.setstate old) }, .error e)
    | .ok (d2, out) => ({ t with decoder := some (d2.setstate old) }, .ok (.str out))

/-- The `newlines` property (_pyio.py:2674-2676): a plain UTF-8 decoder has
no `newlines` attribute. -/
def newlines (t : TState) : Py Val :=
  match t.decoder with
  | none => .ok .none
  | some d => if d.nl then .ok (newlinesVal d.seennl)
      else .error (.named "AttributeError" "'IncrementalDecoder' object has no attribute 'newlines'")

/-- `close()` (_pyio.py:2235-2240). -/
def close (t : TState) : TState × Py Val :=
  if t.b.closed then (t, .ok .none) else
  let (b, r) := P.close t.b
  ({ t with b := b, telling := true }, r)

def step (t : TState) : SOp → TState × Py Val
  | .read n => read t n
  | .readline n =>
    match readlineRaw t n with
    | (t, .error e) => (t, .error e)
    | (t, .ok l) => (t, .ok (.str l))
  | .readlines h => readlines t h
  | .write s => write t s
  | .seek p w => seek t p w
  | .tell => let (t, r) := tell t; (t, r.map .int)
  | .truncate n => truncate t n
  | .getvalue => getvalue t
  | .close => close t
  | .next => next t
  | .closed => (t, .ok (.bool t.b.closed))
  | .newlines => (t, newlines t)
  | .seekTell =>
    match tell t with
    | (t, .error e) => (t, .error e)
    | (t, .ok c) => seek t c 0

/-- `StringIO(initial_value, newline)` (_pyio.py:2722-2737): the
`TextIOWrapper` constructor checks `newline` (_pyio.py:2097-2101) and
configures (`_configure`, :2103-2117); then the value is written and the
stream rewound. -/
def init (value : Option (List Nat)) (newline : Option (List Nat)) : Py TState :=
  match newline with
  | some nl =>
    if !(nl = [] ∨ nl = [10] ∨ nl = [13] ∨ nl = [13, 10]) then .error (illegalNewline nl)
    else build
  | none => build
where
  build : Py TState :=
    let t : TState :=
      { b := bInit [], decoded := [], used := 0, snapshot := none, telling := true, decoder := none
        b2c := (0, 1)
        readuniversal := newline.isNone || newline = some []
        readtranslate := newline.isNone
        readnl := newline
        writetranslate := newline ≠ some [] && newline.isSome
        writenl := match newline with
          | some [] | none => [10]
          | some nl => nl }
    match value with
    | none => .ok t
    | some v =>
      match write t v with
      | (_, .error e) => .error e
      | (t, .ok _) =>
        match seek t 0 0 with
        | (_, .error e) => .error e
        | (t, .ok _) => .ok t

end TP

def runSPy (value : Option (List Nat)) (newline : Option (List Nat)) (ops : List SOp) : Py (List (Py Val)) :=
  match TP.init value newline with
  | .error e => .error e
  | .ok t => .ok (runOps TP.step t ops).2

end PyLean.PyIO
