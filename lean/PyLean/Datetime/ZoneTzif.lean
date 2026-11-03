import PyLean.Core

/-!
# The TZif reader of `zoneinfo` (CPython 3.15.2)

`zoneinfo._common.load_data` (Lib/zoneinfo/_common.py:32-132) with `_TZifHeader.from_file`
(:150-168) and `_TZifHeader.__init__` (:146-148), over raw bytes.

Both twins run this one function. The C `load_data` (Modules/_zoneinfo.c:986-987) calls
`_common.load_data` through `PyObject_CallMethod` and only converts its tuple
(`PyLong_AsLongLong`, `PyLong_AsLong`, `PyObject_IsTrue`); see `ZoneLoad.lean`.

The file object is an `io.BytesIO` (Modules/_io/bytesio.c), which is what
`ZoneInfo.from_file(io.BytesIO(data))` passes. Scope limit: a file object whose `read`, `seek`
or `readline` raise or return something else is not modelled.
-/

namespace PyLean.Datetime.Zone

open PyLean

abbrev Bytes := List UInt8

/-! ### `io.BytesIO` -/

structure BIO where
  data : Bytes
  pos : Nat
  deriving Repr

/-- `BytesIO.read(size)`, Modules/_io/bytesio.c:509-525 with `read_bytes_lock_held`
(:468-497): a negative size, or one past the end, reads what is left, and nothing when the
position is past the end (`size` is clamped at 0). The sizes `load_data` passes are below
`2**35`, inside the `Py_ssize_t` converter. -/
def BIO.read (f : BIO) (size : Int) : Bytes × BIO :=
  let n : Int := (f.data.length : Int) - f.pos
  let size : Int := if size < 0 ∨ size > n then (if n < 0 then 0 else n) else size
  ((f.data.drop f.pos).take size.toNat, { f with pos := f.pos + size.toNat })

/-- `BytesIO.seek(pos, 1)`, bytesio.c:774-818 (whence 1): the clinic `Py_ssize_t` converter
refuses an out-of-range `pos`, a sum past `PY_SSIZE_T_MAX` is an `OverflowError`
(:790-795), and a negative position becomes 0 (:810-811). -/
def BIO.seekCur (f : BIO) (off : Int) : Py BIO :=
  if off < ssizeMin ∨ off > ssizeMax then
    .error (.overflowError "Python int too large to convert to C ssize_t")
  else if off > ssizeMax - f.pos then .error (.overflowError "new position too large")
  else
    let p := off + f.pos
    .ok { f with pos := if p < 0 then 0 else p.toNat }

/-- `BytesIO.readline()`, bytesio.c:561-571 with `scan_eol_lock_held` (:123-150): up to and
including the first newline, else the rest; nothing at or past the end. -/
def BIO.readline (f : BIO) : Bytes × BIO :=
  let rest := f.data.drop f.pos
  let n := match rest.findIdx? (· == 10) with
    | some i => i + 1
    | none => rest.length
  (rest.take n, { f with pos := f.pos + n })

/-! ### Byte helpers -/

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- `repr(bytes)`, `_Py_bytes_repr` (Objects/bytesobject.c:1436-1495) with smart quotes. -/
def bytesRepr (b : Bytes) : String :=
  let q : UInt8 := if b.contains 39 && !b.contains 34 then 34 else 39
  let body := b.flatMap fun c =>
    let n := c.toNat
    if c == q || n == 92 then ['\\', Char.ofNat n]
    else if n == 9 then ['\\', 't']
    else if n == 10 then ['\\', 'n']
    else if n == 13 then ['\\', 'r']
    else if n < 32 || n ≥ 127 then ['\\', 'x', hexDigit (n / 16), hexDigit (n % 16)]
    else [Char.ofNat n]
  String.ofList (['b', Char.ofNat q.toNat] ++ body ++ [Char.ofNat q.toNat])

/-- Big-endian unsigned value. -/
def beNat (bs : Bytes) : Nat := bs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Big-endian two's-complement value of `bs.length` bytes. -/
def beInt (bs : Bytes) : Int :=
  let n := beNat bs
  if n < 2 ^ (8 * bs.length - 1) then n else (n : Int) - 2 ^ (8 * bs.length)

/-- `k` consecutive pieces of `size` bytes. -/
def chunks (size : Nat) : Nat → Bytes → List Bytes
  | 0, _ => []
  | k + 1, bs => bs.take size :: chunks size k (bs.drop size)

/-- `struct.error`, whose `type(e).__name__` is `error`. -/
def structError (msg : String) : PyExc := .named "error" msg

/-- `struct.unpack(f">{count}{c}", buf)` for one format letter `c` of `size` bytes
(Modules/_struct.c): the `-` of a negative count is "bad char in struct format" (:1611), and
the buffer must hold exactly `count * size` bytes (:2113). `signed` picks `q`/`l`/`b` over
`B`. -/
def unpackN (count : Int) (size : Nat) (signed : Bool) (buf : Bytes) : Py (List Int) :=
  if count < 0 then .error (structError "bad char in struct format")
  else if buf.length ≠ count.toNat * size then
    .error (structError s!"unpack requires a buffer of {count.toNat * size} bytes")
  else .ok ((chunks size count.toNat buf).map fun c => if signed then beInt c else (beNat c : Int))

/-- `struct.unpack(">lbb", buf)` (_common.py:81): offset, isdst and abbreviation index, all
signed. -/
def unpackType (buf : Bytes) : Py (Int × Int × Int) :=
  if buf.length ≠ 6 then .error (structError "unpack requires a buffer of 6 bytes")
  else .ok (beInt (buf.take 4), beInt [buf.getD 4 0], beInt [buf.getD 5 0])

/-- Strict UTF-8 (Unicode Table 3-7), which `bytes.decode()` enforces: no overlong forms,
no surrogates, nothing above U+10FFFF, no truncated sequence. -/
def inR (b : UInt8) (lo hi : Nat) : Bool := lo ≤ b.toNat && b.toNat ≤ hi

def utf8Valid : Bytes → Bool
  | [] => true
  | b :: rest =>
    if b.toNat < 0x80 then utf8Valid rest
    else if inR b 0xC2 0xDF then
      match rest with
      | c :: r => inR c 0x80 0xBF && utf8Valid r
      | [] => false
    else if inR b 0xE0 0xEF then
      match rest with
      | c1 :: c2 :: r =>
        (if b.toNat = 0xE0 then inR c1 0xA0 0xBF
         else if b.toNat = 0xED then inR c1 0x80 0x9F else inR c1 0x80 0xBF) &&
        inR c2 0x80 0xBF && utf8Valid r
      | _ => false
    else if inR b 0xF0 0xF4 then
      match rest with
      | c1 :: c2 :: c3 :: r =>
        (if b.toNat = 0xF0 then inR c1 0x90 0xBF
         else if b.toNat = 0xF4 then inR c1 0x80 0x8F else inR c1 0x80 0xBF) &&
        inR c2 0x80 0xBF && inR c3 0x80 0xBF && utf8Valid r
      | _ => false
    else false

/-- `UnicodeDecodeError` from `.decode()`; its message embeds the byte and position. -/
def decodeError : PyExc := .named "UnicodeDecodeError" "~'utf-8' codec can't decode bytes"

/-- `bytes.find(b"\x00", start)`, `find_internal` (Objects/bytes_methods.c:453-500) after
`ADJUST_INDICES` (:433-450): a negative start counts from the end, and a start at or past
the end finds nothing. -/
def findNul (s : Bytes) (start : Int) : Int :=
  let len : Int := s.length
  let st : Int := if start < 0 then (if start + len < 0 then 0 else start + len) else start
  if len - st < 1 then -1
  else match (s.drop st.toNat).findIdx? (· == 0) with
    | some i => st + i
    | none => -1

/-- One bound of `s[a:b]` (`PySlice_AdjustIndices`). -/
def sliceIdx (len : Nat) (i : Int) : Nat :=
  if i < 0 then (if i + len < 0 then 0 else (i + len).toNat) else min i.toNat len

/-- `s[a:b]`. -/
def pySlice {α : Type} (s : List α) (a b : Int) : List α :=
  let i := sliceIdx s.length a
  let j := sliceIdx s.length b
  (s.drop i).take (j - i)

/-- `get_abbr(idx)`, _common.py:95-110: the bytes from `idx` to the next NUL, decoded. With no
NUL after `idx`, `find` gives -1 and the slice `[idx:-1]` drops the last byte. `abbr_vals`
only memoises this, so it is not modelled. -/
def getAbbr (chars : Bytes) (idx : Int) : Py Bytes :=
  let spanEnd := findNul chars idx
  let raw := pySlice chars idx spanEnd
  if utf8Valid raw then .ok raw else .error decodeError

/-- `line.rstrip(b"\n")`. -/
def rstripNL (l : Bytes) : Bytes := (l.reverse.dropWhile (· == 10)).reverse

/-! ### The header -/

/-- `_TZifHeader`, _common.py:135-148: `__init__` assigns the seven slots in order from
exactly seven arguments (`zip(..., strict=True)` never fails for `from_file`'s tuple). -/
structure Header where
  version : Int
  isutcnt : Int
  isstdcnt : Int
  leapcnt : Int
  timecnt : Int
  typecnt : Int
  charcnt : Int
  deriving Repr, DecidableEq

/-- `int(_version)` (_common.py:160) on what `stream.read(1)` returns, a single byte or `b''`
(`_PyLong_FromBytes`, Objects/longobject.c:3166-3183): an ASCII digit is its value, and
anything else, a lone white-space byte included, is an invalid literal. -/
def intOfVersionByte (v : Bytes) : Py Int :=
  match v with
  | [b] => if 48 ≤ b.toNat ∧ b.toNat ≤ 57 then .ok ((b.toNat - 48 : Nat) : Int)
    else .error (.valueError s!"invalid literal for int() with base 10: {bytesRepr v}")
  | _ => .error (.valueError s!"invalid literal for int() with base 10: {bytesRepr v}")

/-- `_TZifHeader.from_file`, _common.py:150-168. -/
def headerFromFile (f : BIO) : Py (Header × BIO) := do
  let (magic, f) := f.read 4
  if magic ≠ [84, 90, 105, 102] then throw (.valueError "Invalid TZif file: magic not found")
  let (v, f) := f.read 1
  let version ← if v = [0] then pure 1 else intOfVersionByte v
  let (_, f) := f.read 15
  let (raw, f) := f.read 24
  let xs ← unpackN 6 4 true raw
  pure (⟨version, xs.getD 0 0, xs.getD 1 0, xs.getD 2 0, xs.getD 3 0, xs.getD 4 0, xs.getD 5 0⟩, f)

/-! ### `load_data` -/

/-- The tuple `load_data` returns: `(trans_idx, trans_list_utc, utcoff, isdst, abbr, tz_str)`. -/
structure TzifData where
  transIdx : List Int
  transUtc : List Int
  utcoff : List Int
  isdst : List Int
  abbr : List Bytes
  tzStr : Option Bytes
  deriving Repr, DecidableEq

/-- The `ttinfo` records, `struct.unpack(">lbb", fobj.read(6)) for i in range(typecnt)`
(_common.py:81), read in order; the first short read raises. -/
def readTypes : Nat → BIO → Py (List (Int × Int × Int) × BIO)
  | 0, f => .ok ([], f)
  | n + 1, f => do
    let (buf, f) := f.read 6
    let t ← unpackType buf
    let (ts, f) ← readTypes n f
    pure (t :: ts, f)

/-- `_common.load_data`, _common.py:65-76: the transition times, then their type indices
(unsigned), checked against `typecnt`. -/
def readTrans (timecnt typecnt : Int) (timeSize : Nat) (f : BIO) : Py (List Int × List Int × BIO) :=
  if timecnt ≠ 0 then do
    let (buf, f) := f.read (timecnt * timeSize)
    let tu ← unpackN timecnt timeSize true buf
    let (buf, f) := f.read timecnt
    let ti ← unpackN timecnt 1 false buf
    let mx := ti.foldl max (ti.headD 0)
    if mx ≥ typecnt then
      throw (.valueError s!"Invalid transition index found while reading TZif: {mx}")
    pure (tu, ti, f)
  else pure ([], [], f)

/-- `_common.load_data`, _common.py:79-86: `zip(*records)` unpacked into three names; no
records (a negative count) fails. -/
def readTypesStage (typecnt : Int) (f : BIO) : Py (List (Int × Int × Int) × BIO) :=
  if typecnt ≠ 0 then do
    let (ts, f) ← readTypes typecnt.toNat f
    if ts = [] then throw (.valueError "not enough values to unpack (expected 3, got 0)")
    pure (ts, f)
  else pure ([], f)

/-- `_common.load_data`, _common.py:117-130: the footer of a version 2+ file. -/
def readFooter (header : Header) (f : BIO) : Py (Option Bytes) :=
  if header.version ≥ 2 then do
    let skip := header.isutcnt + header.isstdcnt + header.leapcnt * 12
    let f ← f.seekCur skip
    let (c, f) := f.read 1
    if c ≠ [10] then throw (.assertionError (bytesRepr c))                   -- `assert c == b"\n", c`
    let (line, _) := f.readline
    if line.getLast? ≠ some 10 then throw (.valueError "Invalid TZif file: unexpected end of file")
    pure (some (rstripNL line))
  else pure none

/-- `_common.load_data(fobj)`, Lib/zoneinfo/_common.py:32-132, line by line. -/
def loadData (bytes : Bytes) : Py TzifData := do
  let f : BIO := ⟨bytes, 0⟩
  let (header, f) ← headerFromFile f                                         -- :33
  -- :35-58: version 1 reads 32-bit times; otherwise skip the v1 block and read the second header
  let (timeSize, header, f) ← (if header.version = 1 then pure (4, header, f) else do
      let skip := header.timecnt * 5 + header.typecnt * 6 + header.charcnt +
        header.leapcnt * 8 + header.isstdcnt + header.isutcnt
      let f ← f.seekCur skip
      let (h2, f) ← headerFromFile f
      pure (8, h2, f) : Py (Nat × Header × BIO))
  let (transUtc, transIdx, f) ← readTrans header.timecnt header.typecnt timeSize f   -- :60-76
  let (types, f) ← readTypesStage header.typecnt f                           -- :79-86
  let utcoff := types.map (·.1)
  let isdst := types.map (·.2.1)
  let abbrind := types.map (·.2.2)
  -- :92-112: the designations
  let (abbrChars, f) := f.read header.charcnt
  let abbr ← abbrind.mapM (getAbbr abbrChars)
  let tzStr ← readFooter header f                                            -- :117-130
  pure ⟨transIdx, transUtc, utcoff, isdst, abbr, tzStr⟩

end PyLean.Datetime.Zone
