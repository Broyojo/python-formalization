import PyLean.TextLibs.BinasciiModel
import PyLean.TextLibs.BinasciiCrcTable

/-!
The rest of `Modules/binascii.c` and `Lib/base64.py`: uu, quoted-printable, `crc_hqx`, the
85-based codecs and the legacy interface, CPython 3.14.7.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

/-! ### uu -/

/-- The `for` loop of `binascii_a2b_uu_impl`, `Modules/binascii.c:238-276`. An exhausted buffer
reads as NUL bytes, so the loop runs on past the end; `fuel` bounds it. The result is the bytes
and the unread input. -/
def a2bUuLoop : (fuel : Nat) → (binLen left bits : Nat) → List Nat → Py (List Nat × List Nat)
  | 0, _, _, _, _ => .error .modelFuel
  | fuel + 1, binLen, left, bits, ascii =>
    if binLen = 0 then .ok ([], ascii)
    else
      let this : Py Nat :=
        match ascii with
        | [] => .ok 0
        | c :: _ =>
          if c = 10 ∨ c = 13 then .ok 0
          else if c < 32 ∨ c > 96 then .error (err "Illegal char")
          else .ok ((c - 32) % 64)
      match this with
      | .error e => .error e
      | .ok v =>
        let left' := left * 64 + v
        let bits' := bits + 6
        if bits' ≥ 8 then
          let b2 := bits' - 8
          let byte := left' / 2 ^ b2 % 256
          match a2bUuLoop fuel (binLen - 1) (left' % 2 ^ b2) b2 (ascii.drop 1) with
          | .error e => .error e
          | .ok (out, r) => .ok (byte :: out, r)
        else a2bUuLoop fuel binLen left' bits' (ascii.drop 1)

/-- The trailing check, `Modules/binascii.c:281-294`. -/
def uuTrailingOk (r : List Nat) : Bool := r.all fun c => c = 32 || c = 96 || c = 10 || c = 13

/-- `binascii_a2b_uu_impl`, `Modules/binascii.c:203-296`. -/
def a2bUuBytes : List Nat → Py (List Nat)
  | [] => .error (err "Missing length byte")
  | c :: rest =>
    -- `(*ascii_data++ - ' ') & 077` on an `int`
    let binLen := (c + 256 - 32) % 64
    match a2bUuLoop (2 * binLen + 2) binLen 0 0 rest with
    | .error e => .error e
    | .ok (out, r) =>
      if uuTrailingOk r then .ok out else .error (err "Trailing garbage")

def a2bUu (d : Data) : Py (List Nat) := do a2bUuBytes (← asciiBuffer d)

/-- One encoded character, `Modules/binascii.c:359-362`. -/
def uuChar (backtick : Bool) (v : Nat) : Nat := if backtick && v == 0 then 96 else v + 32

/-- The `while (leftbits >= 6)` of `binascii_b2a_uu_impl`, `Modules/binascii.c:356-363`. -/
def uuDrain (backtick : Bool) (left : Nat) : (fuel bits : Nat) → List Nat × Nat
  | 0, bits => ([], bits)
  | fuel + 1, bits =>
    if bits ≥ 6 then
      let c := uuChar backtick (left / 2 ^ (bits - 6) % 64)
      let (r, bits') := uuDrain backtick left fuel (bits - 6)
      (c :: r, bits')
    else ([], bits)

/-- The `for` loop of `binascii_b2a_uu_impl`, `Modules/binascii.c:347-364`; bytes past the end
are the zero padding. `leftchar` is an `unsigned int`. -/
def b2aUuLoop (backtick : Bool) : (fuel : Nat) → List Nat → (left bits : Nat) → List Nat
  | 0, _, _, _ => []
  | fuel + 1, data, left, bits =>
    if data.isEmpty ∧ bits = 0 then []
    else
      let left' := (left * 256 + data.headD 0) % 2 ^ 32
      let (out, bits') := uuDrain backtick left' 3 (bits + 8)
      out ++ b2aUuLoop backtick fuel (data.drop 1) left' bits'

/-- `binascii_b2a_uu_impl`, `Modules/binascii.c:309-368`. -/
def b2aUu (data : List Nat) (backtick : Bool) : Py (List Nat) :=
  if data.length > 45 then .error (err "At most 45 bytes at once")
  else
    let first := if backtick && data.isEmpty then 96 else 32 + data.length
    .ok (first :: b2aUuLoop backtick (data.length + 3) data 0 0 ++ [10])

/-! ### crc_hqx -/

/-- One step of the `while`, `Modules/binascii.c:618`. -/
def crcStep (crc b : Nat) : Nat :=
  (crc * 256 % 65536) ^^^ crctabHqx.getD ((crc / 256) ^^^ b) 0

/-- `binascii_crc_hqx_impl`, `Modules/binascii.c:606-622`; `crc` is the masked `unsigned int`. -/
def crcHqx (data : List Nat) (crc : Int) : Nat :=
  data.foldl crcStep ((crc % 2 ^ 32).toNat % 65536)

/-! ### quoted-printable -/

def isHexChar (c : Nat) : Bool :=
  (65 ≤ c && c ≤ 70) || (97 ≤ c && c ≤ 102) || (48 ≤ c && c ≤ 57)

/-- `while (in < datalen && ascii_data[in] != '\n') in++`, then the `if (in < datalen) in++` of
the soft line break. -/
def qpSkipLine : List Nat → List Nat
  | [] => []
  | 10 :: r => r
  | _ :: r => qpSkipLine r

/-- The loop of `binascii_a2b_qp_impl`, `Modules/binascii.c:993-1036`, on the unread suffix. -/
def a2bQpLoop (header : Bool) : (fuel : Nat) → List Nat → List Nat
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, c :: r =>
    if c = 61 then
      match r with
      | [] => []
      | 10 :: t => a2bQpLoop header fuel t
      | 13 :: t => a2bQpLoop header fuel (qpSkipLine t)
      | 61 :: t => 61 :: a2bQpLoop header fuel t
      | a :: b :: t =>
        if isHexChar a && isHexChar b then
          (digitValue a * 16 + digitValue b) % 256 :: a2bQpLoop header fuel t
        else 61 :: a2bQpLoop header fuel r
      | _ => 61 :: a2bQpLoop header fuel r
    else if header && c == 95 then 32 :: a2bQpLoop header fuel r
    else c :: a2bQpLoop header fuel r

/-- `binascii_a2b_qp_impl`, `Modules/binascii.c:970-1040`. -/
def a2bQp (d : Data) (header : Bool) : Py (List Nat) := do
  let b ← asciiBuffer d
  return a2bQpLoop header (b.length + 1) b

/-- `to_hex`, `Modules/binascii.c:1042-1051`: the two digits, in output order. -/
def toHex (ch : Nat) : List Nat :=
  let digit (v : Nat) := if v < 10 then 48 + v else 55 + v
  [digit (ch / 16 % 16), digit (ch % 16)]

/-- Options of `b2a_qp`. -/
structure QpOpts where
  quotetabs : Bool
  istext : Bool
  header : Bool
  deriving Repr, DecidableEq, Inhabited

def MAXLINESIZE : Nat := 76

/-- The condition shared by both passes, `Modules/binascii.c:1102-1112` and `:1176-1186`.
`b` is `databuf[in]`, `next` is `databuf[in+1]` when it exists. -/
def qpMustEncode (o : QpOpts) (linelen : Nat) (b : Nat) (next : Option Nat) : Bool :=
  decide (b > 126) || b == 61 || (o.header && b == 95) ||
  (b == 46 && linelen == 0 &&
    (next == none || next == some 10 || next == some 13 || next == some 0)) ||
  (!o.istext && (b == 13 || b == 10)) ||
  ((b == 9 || b == 32) && next == none) ||
  (decide (b < 33) && b != 13 && b != 10 && (o.quotetabs || (b != 9 && b != 32)))

/-- `memchr` for `'\n'` and the look-behind, `Modules/binascii.c:1094-1096`. -/
def qpCrlf (d : List Nat) : Bool :=
  match d.findIdx? (· == 10) with
  | some (i + 1) => d[i]? == some 13
  | _ => false

/-- A soft line break. -/
def qpSoft (crlf : Bool) : List Nat := if crlf then [61, 13, 10] else [61, 10]

/-- A hard line end. -/
def qpEol (crlf : Bool) : List Nat := if crlf then [13, 10] else [10]

/-- A trailing space or tab before a line end is encoded, `Modules/binascii.c:1192-1201`. -/
def qpProtect : List Nat → List Nat
  | [] => []
  | ch :: t => if ch == 32 || ch == 9 then (toHex ch).reverse ++ [61] ++ t else ch :: t

/-- The second pass of `binascii_b2a_qp_impl`, `Modules/binascii.c:1174-1241`. `out` is the
output so far, newest first, because the line-end branch rewrites `odata[out-1]`. -/
def b2aQpLoop (o : QpOpts) (crlf : Bool) : (fuel : Nat) → List Nat → (linelen : Nat) → List Nat → List Nat
  | 0, _, _, out => out
  | _ + 1, [], _, out => out
  | fuel + 1, b :: r, linelen, out =>
    let next := r.head?
    if qpMustEncode o linelen b next then
      let (out, linelen) :=
        if linelen + 3 ≥ MAXLINESIZE then ((qpSoft crlf).reverse ++ out, 0) else (out, linelen)
      b2aQpLoop o crlf fuel r (linelen + 3) ((toHex b).reverse ++ [61] ++ out)
    else if o.istext && (b == 10 || (b == 13 && next == some 10)) then
      let r' := if b == 13 then r.drop 1 else r
      b2aQpLoop o crlf fuel r' 0 ((qpEol crlf).reverse ++ qpProtect out)
    else
      let (out, linelen) :=
        if next != none && next != some 10 && linelen + 1 ≥ MAXLINESIZE then
          ((qpSoft crlf).reverse ++ out, 0)
        else (out, linelen)
      let c := if o.header && b == 32 then 95 else b
      b2aQpLoop o crlf fuel r (linelen + 1) (c :: out)

/-- `binascii_b2a_qp_impl`, `Modules/binascii.c:1072-1245`. The first pass only sizes the
buffer; the bound `textlibs-binascii-qp-buffer-bound` compares the two. -/
def b2aQp (d : List Nat) (o : QpOpts) : List Nat :=
  (b2aQpLoop o (qpCrlf d) (d.length + 1) d 0 []).reverse

/-- The first pass, `Modules/binascii.c:1100-1164`: `odatalen`. -/
def b2aQpSize (o : QpOpts) (crlf : Bool) : (fuel : Nat) → (prev : Option Nat) → List Nat → (linelen : Nat) → Nat
  | 0, _, _, _ => 0
  | _ + 1, _, [], _ => 0
  | fuel + 1, prev, b :: r, linelen =>
    let next := r.head?
    let soft := if crlf then 3 else 2
    if qpMustEncode o linelen b next then
      let (delta, linelen) := if linelen + 3 ≥ MAXLINESIZE then (soft, 0) else (0, linelen)
      delta + 3 + b2aQpSize o crlf fuel (some b) r (linelen + 3)
    else if o.istext && (b == 10 || (b == 13 && next == some 10)) then
      let protect := if prev == some 32 || prev == some 9 then 2 else 0
      let eol := if crlf then 2 else 1
      let r' := if b == 13 then r.drop 1 else r
      let prev' := if b == 13 then r.head? else some b
      protect + eol + b2aQpSize o crlf fuel prev' r' 0
    else
      let (delta, linelen) :=
        if next != none && next != some 10 && linelen + 1 ≥ MAXLINESIZE then (soft, 0)
        else (0, linelen)
      delta + 1 + b2aQpSize o crlf fuel (some b) r (linelen + 1)

/-! ### Ascii85 and base85 -/

/-- The characters of a word, `chars2[w // 614125] + chars2[w // 85 % 7225] + chars[w % 85]`. -/
def word5 (chars : Nat → Nat) (w : Nat) : List Nat :=
  let hi := w / 614125
  let mid := w / 85 % 7225
  [chars (hi / 85), chars (hi % 85), chars (mid / 85), chars (mid % 85), chars (w % 85)]

/-- `struct.Struct('!%dI' ...).unpack`: big-endian 4-byte words. -/
def words4 : (fuel : Nat) → List Nat → List Nat
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, s =>
    (s.take 4).foldl (fun x b => x * 256 + b) 0 :: words4 fuel (s.drop 4)

/-- `_85encode`, `Lib/base64.py:299-321`. -/
def enc85 (b : List Nat) (chars : Nat → Nat) (pad foldnuls foldspaces : Bool) : List Nat :=
  let padding := (4 - b.length % 4) % 4
  let b' := b ++ List.replicate padding 0
  let chunks := (words4 b'.length b').map fun w =>
    if foldnuls && w == 0 then [122]
    else if foldspaces && w == 0x20202020 then [121]
    else word5 chars w
  let chunks :=
    if padding ≠ 0 ∧ !pad then
      let last := chunks.getLast?.getD []
      let last := if last == [122] then List.replicate 5 (chars 0) else last
      chunks.dropLast ++ [last.take (last.length - padding)]
    else chunks
  chunks.flatten

def a85char (i : Nat) : Nat := 33 + i

/-- Split into `wrapcol` pieces, `Lib/base64.py:356-357`. -/
def chunksOf (n : Nat) : (fuel : Nat) → List Nat → List (List Nat)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, s => s.take n :: chunksOf n fuel (s.drop n)

/-- `a85encode`, `Lib/base64.py:323-365`; `wrapcol` is any int. -/
def a85encode (b : List Nat) (foldspaces : Bool) (wrapcol : Int) (pad adobe : Bool) : List Nat :=
  let result := enc85 b a85char pad true foldspaces
  let result := if adobe then [60, 126] ++ result else result
  let result :=
    if wrapcol ≠ 0 then
      let w := max (if adobe then 2 else 1) wrapcol
      let chunks := chunksOf w.toNat result.length result
      let chunks :=
        if adobe ∧ ((chunks.getLast?.getD []).length : Int) + 2 > w then chunks ++ [[]]
        else chunks
      List.intercalate [10] chunks
    else result
  if adobe then result ++ [126, 62] else result

/-- `struct.Struct('!I').pack`. -/
def packI (acc : Nat) : List Nat :=
  [acc / 2 ^ 24 % 256, acc / 2 ^ 16 % 256, acc / 2 ^ 8 % 256, acc % 256]

/-- The `for x in b + b'u' * 4` loop, `Lib/base64.py:406-430`. `dec` is newest first. -/
def a85Loop (foldspaces : Bool) (ignore : List Nat) :
    List Nat → (curr dec : List Nat) → Py (List Nat × List Nat)
  | [], curr, dec => .ok (curr, dec)
  | x :: xs, curr, dec =>
    if 33 ≤ x ∧ x ≤ 117 then
      let curr := curr ++ [x]
      if curr.length = 5 then
        let acc := curr.foldl (fun a c => 85 * a + (c - 33)) 0
        if acc ≥ 2 ^ 32 then .error (.valueError "Ascii85 overflow")
        else a85Loop foldspaces ignore xs [] ((packI acc).reverse ++ dec)
      else a85Loop foldspaces ignore xs curr dec
    else if x = 122 then
      if !curr.isEmpty then .error (.valueError "z inside Ascii85 5-tuple")
      else a85Loop foldspaces ignore xs curr ([0, 0, 0, 0] ++ dec)
    else if foldspaces && x == 121 then
      if !curr.isEmpty then .error (.valueError "y inside Ascii85 5-tuple")
      else a85Loop foldspaces ignore xs curr ([32, 32, 32, 32] ++ dec)
    else if ignore.contains x then a85Loop foldspaces ignore xs curr dec
    else .error (.valueError s!"Non-Ascii85 digit found: {String.singleton (Char.ofNat x)}")

def defaultIgnore : List Nat := [32, 9, 10, 13, 11]

/-- `a85decode`, `Lib/base64.py:367-437`. -/
def a85decode (b0 : Data) (foldspaces adobe : Bool) (ignore : List Nat) : Py (List Nat) := do
  let b ← bytesFromDecodeData b0
  let b ←
    if adobe then
      if !([126, 62].isSuffixOf b) then
        Except.error (.valueError "Ascii85 encoded byte sequences must end with b'~>'")
      else if [60, 126].isPrefixOf b then pure ((b.drop 2).take (b.length - 4))
      else pure (b.take (b.length - 2))
    else pure b
  let (curr, dec) ← a85Loop foldspaces ignore (b ++ [117, 117, 117, 117]) [] []
  let result := dec.reverse
  let padding := 4 - curr.length
  return if padding ≠ 0 then result.take (result.length - padding) else result

def b85alphabet : List Nat :=
  ("0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ" ++ "abcdefghijklmnopqrstuvwxyz!#$%&()*+-;<=>?@^_`{|}~").toList.map Char.toNat

def b85char (i : Nat) : Nat := b85alphabet.getD i 0

/-- `b85encode`, `Lib/base64.py:447-461`. -/
def b85encode (b : List Nat) (pad : Bool) : List Nat := enc85 b b85char pad false false

/-- `_b85dec[c]`. -/
def b85dec (c : Nat) : Option Nat := b85alphabet.findIdx? (· == c)

/-- `for c in chunk: acc = acc * 85 + _b85dec[c]`, with the error position of the `except`. -/
def b85Chunk : List Nat → (j acc : Nat) → Sum Nat Nat
  | [], _, acc => .inr acc
  | c :: cs, j, acc =>
    match b85dec c with
    | none => .inl j
    | some v => b85Chunk cs (j + 1) (acc * 85 + v)

/-- The `for i in range(0, len(b), 5)` loop, `Lib/base64.py:484-500`. -/
def b85Loop : (fuel : Nat) → List Nat → (i : Nat) → Py (List Nat)
  | 0, _, _ => .ok []
  | _ + 1, [], _ => .ok []
  | fuel + 1, b, i =>
    match b85Chunk (b.take 5) 0 0 with
    | .inl j => .error (.valueError s!"bad base85 character at position {i + j}")
    | .inr acc =>
      if acc ≥ 2 ^ 32 then
        .error (.valueError s!"base85 overflow in hunk starting at byte {i}")
      else do
        return packI acc ++ (← b85Loop fuel (b.drop 5) (i + 5))

/-- `b85decode` after `_bytes_from_decode_data`, `Lib/base64.py:479-505`. -/
def b85decodeBytes (b : List Nat) : Py (List Nat) := do
  let padding := (5 - b.length % 5) % 5
  let b' := b ++ List.replicate padding 126
  let result ← b85Loop b'.length b' 0
  return if padding ≠ 0 then result.take (result.length - padding) else result

def b85decode (b : Data) : Py (List Nat) := do b85decodeBytes (← bytesFromDecodeData b)

def z85alphabet : List Nat :=
  ("0123456789abcdefghijklmnopqrstuvwxyz" ++ "ABCDEFGHIJKLMNOPQRSTUVWXYZ.-:+=^!/*?&<>()[]{}@%$#").toList.map Char.toNat

/-- `z85encode`, `Lib/base64.py:518-520`. -/
def z85encode (s : List Nat) : List Nat := translate b85alphabet z85alphabet (b85encode s false)

/-- `_z85_decode_translation`, `Lib/base64.py:512-515`. -/
def z85DecodeMap (s : List Nat) : List Nat :=
  translate (z85alphabet ++ ";_`|~".toList.map Char.toNat) (b85alphabet ++ [0, 0, 0, 0, 0]) s

/-- `e.args[0].replace('base85', 'z85')`. -/
def z85Message : PyExc → PyExc
  | .valueError m => .valueError (m.replace "base85" "z85")
  | e => e

/-- `z85decode`, `Lib/base64.py:522-532`. -/
def z85decode (s0 : Data) : Py (List Nat) := do
  let s ← bytesFromDecodeData s0
  match b85decode (.bytes (z85DecodeMap s)) with
  | .ok r => .ok r
  | .error e => .error (z85Message e)

/-! ### The legacy interface -/

def MAXBINSIZE : Nat := 57

/-- `b2a_base64` on successive `MAXBINSIZE` slices, as `encodebytes` makes them. -/
def encodeStream : (fuel : Nat) → List Nat → List Nat
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, s =>
    b2aBase64 (s.take MAXBINSIZE) true ++ encodeStream fuel (s.drop MAXBINSIZE)

/-- A binary file object. `read(n)` returns at most `n` bytes of `data`, as the file API promises:
`reads` is what each call does, `give k` returning at most `k` more limits it further, and `raises`
raising. With the script used up, reads are full. `writes` is what each `write` does; `written` is
every argument `write` was given. -/
inductive ReadStep where
  | give (k : Nat)
  | raises (e : PyExc)
  deriving Repr, DecidableEq, Inhabited

structure FileSim where
  data : List Nat
  reads : List ReadStep := []
  writes : List (Py Unit) := []
  written : List (List Nat) := []
  deriving Repr, Inhabited

def FileSim.read (f : FileSim) (n : Nat) : FileSim × Py (List Nat) :=
  match f.reads with
  | [] => ({ f with data := f.data.drop n }, .ok (f.data.take n))
  | .raises e :: r => ({ f with reads := r }, .error e)
  | .give k :: r =>
    let m := min k n
    ({ f with reads := r, data := f.data.drop m }, .ok (f.data.take m))

def FileSim.write (f : FileSim) (line : List Nat) : FileSim × Py Unit :=
  let f := { f with written := f.written ++ [line] }
  match f.writes with
  | [] => (f, .ok ())
  | r :: rest => ({ f with writes := rest }, r)

/-- The inner `while`, `Lib/base64.py:544-545`. -/
def fillChunk : (fuel : Nat) → FileSim → List Nat → FileSim × Py (List Nat)
  | 0, f, _ => (f, .error .modelFuel)
  | fuel + 1, f, s =>
    if s.length < MAXBINSIZE then
      match f.read (MAXBINSIZE - s.length) with
      | (f, .error e) => (f, .error e)
      | (f, .ok ns) => if ns.isEmpty then (f, .ok s) else fillChunk fuel f (s ++ ns)
    else (f, .ok s)

/-- `encode`, `Lib/base64.py:541-547`. -/
def encodeFile : (fuel : Nat) → FileSim → FileSim × Py Unit
  | 0, f => (f, .error .modelFuel)
  | fuel + 1, f =>
    match f.read MAXBINSIZE with
    | (f, .error e) => (f, .error e)
    | (f, .ok s) =>
      if s.isEmpty then (f, .ok ())
      else
        match fillChunk (MAXBINSIZE + 1) f s with
        | (f, .error e) => (f, .error e)
        | (f, .ok s) =>
          match f.write (b2aBase64 s true) with
          | (f, .error e) => (f, .error e)
          | (f, .ok ()) => encodeFile fuel f

/-- `encodebytes`, `Lib/base64.py:572-580`. -/
def encodebytes (s : List Nat) : List Nat := encodeStream (s.length + 1) s

/-- `decodebytes`, `Lib/base64.py:583-586`. -/
def decodebytes (s : List Nat) : Py (List Nat) := a2bBase64 false (.bytes s)

/-- Split after each `\n`, as `readline` does. -/
def splitLines : (fuel : Nat) → List Nat → List (List Nat)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, s =>
    match s.findIdx? (· == 10) with
    | some i => s.take (i + 1) :: splitLines fuel (s.drop (i + 1))
    | none => [s]

/-- `decode`, `Lib/base64.py:550-554`: each line is decoded on its own. `lines` is what `readline`
returns or raises, and an empty line ends the loop. -/
def decodeFile : List (Py (List Nat)) → FileSim → FileSim × Py Unit
  | [], f => (f, .ok ())
  | .error e :: _, f => (f, .error e)
  | .ok l :: ls, f =>
    if l.isEmpty then (f, .ok ())
    else
      match a2bBase64 false (.bytes l) with
      | .error e => (f, .error e)
      | .ok s =>
        match f.write s with
        | (f, .error e) => (f, .error e)
        | (f, .ok ()) => decodeFile ls f

/-- What `_input_type_check` sees of its argument. -/
inductive TypeCheck where
  /-- `memoryview(s)` raises `TypeError`. -/
  | notBuffer (cls : String)
  | view (format : String) (ndim : Nat) (cls : String)
  deriving Repr, DecidableEq, Inhabited

/-- `_input_type_check`, `Lib/base64.py:556-569`. -/
def inputTypeCheck : TypeCheck → Py Unit
  | .notBuffer c => .error (.typeError s!"expected bytes-like object, not {c}")
  | .view f n c =>
    if !(f == "c" || f == "b" || f == "B") then
      .error (.typeError s!"expected single byte elements, not '{f}' from {c}")
    else if n ≠ 1 then .error (.typeError s!"expected 1-D data, not {n}-D data from {c}")
    else .ok ()

/-- `standard_b64encode`, `Lib/base64.py:88-93`. -/
def standardB64encode (s : List Nat) : Py (List Nat) := b64encode s none

/-- `standard_b64decode`, `Lib/base64.py:95-103`. -/
def standardB64decode (s : Data) : Py (List Nat) := b64decode s none false

/-- The argument of `_input_type_check`, from a `Data`. -/
def typeCheckOf : Data → Py TypeCheck
  | .bytes _ => .ok (.view "B" 1 "bytes")
  | .str _ => .ok (.notBuffer "str")
  | .notBuffer t => .ok (.notBuffer t)
  | .raises t (.typeError _) => .ok (.notBuffer t)
  | .raises _ e => .error e

/-- `binascii.b2a_base64` with its arguments as objects: `newline` is a `bool` converter, which runs
`__bool__`, after `data`. -/
def b2aBase64A (d : Data) (newline : Py Bool) : Py (List Nat) := do
  let b ← bufData d
  return b2aBase64 b (← newline)

def a2bBase64A (d : Data) (strict : Py Bool) : Py (List Nat) := do
  let b ← asciiBuffer d
  a2bBase64Bytes (← strict) b

/-- `binascii_b2a_hex_impl`, `Modules/binascii.c:849-856`, and `binascii_hexlify_impl`,
`Modules/binascii.c:867-874`, which is the same call. -/
def b2aHexA (d : Data) (sep : SepArg) (group : Py Int) : Py (List Nat) := do
  let b ← bufData d
  let g ← group
  if g < -(2 ^ 31) ∨ g > 2 ^ 31 - 1 then
    throw (.overflowError "Python int too large to convert to C int")
  strhexBytes b sep g

def a2bHexA (d : Data) : Py (List Nat) := a2bHex d

def a2bUuA (d : Data) : Py (List Nat) := a2bUu d

def b2aUuA (d : Data) (backtick : Py Bool) : Py (List Nat) := do
  let b ← bufData d
  b2aUu b (← backtick)

/-- `crc_hqx`: `crc` is `unsigned_int(bitwise=True)`, so only `__index__` can fail. -/
def crcHqxA (d : Data) (crc : Py Int) : Py Nat := do
  let b ← bufData d
  return crcHqx b (← crc)

def a2bQpA (d : Data) (header : Py Bool) : Py (List Nat) := do
  let b ← asciiBuffer d
  let _ := b
  a2bQp d (← header)

def b2aQpA (d : Data) (quotetabs istext header : Py Bool) : Py (List Nat) := do
  let b ← bufData d
  return b2aQp b ⟨← quotetabs, ← istext, ← header⟩

/-- The encoders of `Lib/base64.py` on any object: the first thing each does with its argument. -/
def encodeAny (name : String) (d : Data) : Py (List Nat) :=
  match name with
  | "b64encode" | "standard_b64encode" => do b64encode (← bufData d) none
  | "urlsafe_b64encode" => do return urlsafeEncode (← bufData d)
  | "b32encode" => do return b32encode b32alphabet (← toBytesView d)
  | "b32hexencode" => do return b32encode b32hexalphabet (← toBytesView d)
  | "b16encode" => do return b16encode (← bufData d)
  | "a85encode" => do return a85encode (← toBytesView d) false 0 false false
  | "b85encode" => do return b85encode (← toBytesView d) false
  | "z85encode" => do return z85encode (← toBytesView d)
  | "encodebytes" => do
    inputTypeCheck (← typeCheckOf d)
    return encodebytes (← bufData d)
  | _ => do
    inputTypeCheck (← typeCheckOf d)
    decodebytes (← bufData d)

/-- `main`'s flag loop, `Lib/base64.py:604-609`: the last flag wins, `-h` returns at once. -/
def mainSelect : List Char → Option Bool → Option Bool
  | [], f => f
  | 'h' :: _, _ => none
  | 'e' :: r, _ => mainSelect r (some true)
  | _ :: r, _ => mainSelect r (some false)

end PyLean.TextLibs.Binascii
