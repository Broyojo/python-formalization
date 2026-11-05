import PyLean.TextLibs.BinasciiWrap

/-!
The codecs of `Modules/binascii.c` as they stand in CPython 3.15.2, where base32, base85 and Ascii85
moved into C and every codec gained `padded`, `wrapcol`, `alphabet`, `ignorechars` and `canonical`, and
`Lib/base64.py`, which is now a thin layer over them.

Each loop is mirrored with its fast path. A bound such as "Too much data for base64" needs an object of
about `2 ** 62` bytes, which no allocator returns, so those branches are left out, as a stated limit.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

/-- `_PyLong_Size_t_Converter`, `Objects/longobject.c:1812-1836`, on an `int`. -/
def sizeT (n : Int) : Py Nat :=
  if n < 0 then .error (.valueError "Cannot convert negative int")
  else if n ≥ 2 ^ 64 then .error (.overflowError "Python int too large for C size_t")
  else .ok n.toNat

def asciiRange (a b : Nat) : List Nat := (List.range (b + 1 - a)).map (· + a)

/-- `table_b2a_base64`, `Modules/binascii.c:113-114`, and `BASE64_ALPHABET`. -/
def b64Alpha : List Nat := asciiRange 65 90 ++ asciiRange 97 122 ++ asciiRange 48 57 ++ [43, 47]
/-- `URLSAFE_BASE64_ALPHABET`, `Modules/binascii.c:2708-2711`. -/
def urlAlpha : List Nat := asciiRange 65 90 ++ asciiRange 97 122 ++ asciiRange 48 57 ++ [45, 95]
/-- `table_b2a_base32`, `Modules/binascii.c:271-272`. -/
def b32Alpha : List Nat := asciiRange 65 90 ++ asciiRange 50 55
/-- `BASE32HEX_ALPHABET`, `Modules/binascii.c:2761-2762`. -/
def b32hexAlpha : List Nat := asciiRange 48 57 ++ asciiRange 65 86
/-- `table_b2a_base85`, `Modules/binascii.c:232-234`. -/
def b85Alpha : List Nat :=
  asciiRange 48 57 ++ asciiRange 65 90 ++ asciiRange 97 122 ++
    [33, 35, 36, 37, 38, 40, 41, 42, 43, 45, 59, 60, 61, 62, 63, 64, 94, 95, 96, 123, 124, 125, 126]
/-- `table_b2a_base85_a85`, `Modules/binascii.c:236-238`. -/
def a85Alpha : List Nat := asciiRange 33 117
/-- `Z85_ALPHABET`, `Modules/binascii.c:2748-2752`. -/
def z85Alpha : List Nat :=
  asciiRange 48 57 ++ asciiRange 97 122 ++ asciiRange 65 90 ++
    [46, 45, 58, 43, 61, 94, 33, 47, 42, 63, 38, 60, 62, 40, 41, 91, 93, 123, 125, 64, 37, 36, 35]

/-- The table `get_reverse_table`, `Modules/binascii.c:663-706`, builds: the last index of `c` in the
alphabet, and `padchar` on top. The tables in static storage are this function of their alphabets. The
cache in the module state is keyed on the alphabet, so it is not observable. -/
def revT (alpha : List Nat) (pad : Option Nat) (c : Nat) : Nat :=
  if pad == some c then alpha.length
  else (((alpha.zipIdx).reverse.find? (·.1 == c)).map (·.2)).getD 255

/-- `ignorechar`, `Modules/binascii.c:710-725`: the cache has no effect on the answer. -/
def ign (ig : Option (List Nat)) (c : Nat) : Bool :=
  match ig with
  | none => false
  | some l => l.contains c

/-- `alphabet: PyBytesObject` of a decoder, as the clinic receives it. -/
inductive AlphaArg where
  | absent
  | bytes (b : List Nat)
  | other (ty : String)
  deriving Repr, DecidableEq, Inhabited

/-- The clinic check of `alphabet: PyBytesObject`, naming the function. -/
def alphaDec (fname : String) : AlphaArg → Py (Option (List Nat))
  | .absent => .ok none
  | .bytes b => .ok (some b)
  | .other t => .error (.typeError s!"{fname}() argument 'alphabet' must be bytes, not {t}")

/-- The clinic `Py_buffer` of `alphabet` of an encoder and of `ignorechars`. -/
def bufOpt : Option Data → Py (Option (List Nat))
  | none => .ok none
  | some d => do return some (← bufData d)

/-- `get_reverse_table` and its length check. -/
def decTable (alpha : Option (List Nat)) (default : Nat → Nat) (size : Nat) (pad : Option Nat) :
    Py (Nat → Nat) :=
  match alpha with
  | none => .ok default
  | some a =>
    if a.length ≠ size then .error (.valueError s!"alphabet must have length {size}")
    else .ok (revT a pad)

/-- The table of an encoder, `Modules/binascii.c:970-976`. -/
def encTable (alpha : Option (List Nat)) (default : List Nat) (size : Nat) : Py (List Nat) :=
  match alpha with
  | none => .ok default
  | some a =>
    if a.length ≠ size then .error (.valueError s!"alphabet must have length {size}")
    else .ok a

/-! ### base64 -/

/-- The fixed options of the decoding loop. -/
structure B64 where
  strict : Bool
  padded : Bool
  tbl : Nat → Nat
  ig : Option (List Nat)

/-- `base64_decode_quad`, `Modules/binascii.c:152-169`. -/
def quad64 (t : Nat → Nat) (a b c d : Nat) : Option (List Nat) :=
  let v0 := t a
  let v1 := t b
  let v2 := t c
  let v3 := t d
  if v0 ≥ 64 ∨ v1 ≥ 64 ∨ v2 ≥ 64 ∨ v3 ≥ 64 then none
  else some [(v0 * 4 + v1 / 16) % 256, (v1 * 16 + v2 / 4) % 256, (v2 * 64 + v3) % 256]

/-- `base64_decode_fast`, `Modules/binascii.c:175-189`: the rest of the input and the output. -/
def fast64 (t : Nat → Nat) : List Nat → List Nat → List Nat × List Nat
  | a :: b :: c :: d :: r, out =>
    match quad64 t a b c d with
    | some o => fast64 t r (out ++ o)
    | none => (a :: b :: c :: d :: r, out)
  | s, out => (s, out)

/-- The slow path, `Modules/binascii.c:811-898`, with the `goto fastpath` of `:896`. -/
def a2b64Run (c : B64) : (fuel : Nat) → List Nat → Dec → Py Dec
  | 0, _, _ => .error .modelFuel
  | _ + 1, [], st => .ok st
  | fuel + 1, x :: xs, st =>
    if c.padded && x == 61 then
      let pads := st.pads + 1
      let st' := { st with pads }
      if st.quad ≥ 2 ∧ st.quad + pads ≤ 4 then a2b64Run c fuel xs st'
      else if !c.strict || ign c.ig 61 then a2b64Run c fuel xs st'
      else if st.quad = 1 then .ok st'
      else .error (err (if st.quad = 0 ∧ st.out.isEmpty then "Leading padding not allowed"
                        else "Excess padding not allowed"))
    else
      let v := c.tbl x
      if v ≥ 64 then
        if c.strict && !ign c.ig x then
          .error (err (if x = 61 then "Padding not allowed" else "Only base64 data is allowed"))
        else a2b64Run c fuel xs st
      else if st.pads ≠ 0 ∧ c.strict ∧ !ign c.ig 61 then
        .error (err (if st.quad + st.pads = 4 then "Excess data after padding"
                     else "Discontinuous padding not allowed"))
      else
        let st' := decStep { st with pads := 0 } v
        if st.quad = 3 then
          let f := fast64 c.tbl xs st'.out
          a2b64Run c fuel f.1 { st' with out := f.2 }
        else a2b64Run c fuel xs st'

/-- `binascii_a2b_base64_impl`, `Modules/binascii.c:749-942`, from the fast path on. -/
def a2b64Core (c : B64) (canonical : Bool) (s : List Nat) : Py (List Nat) := do
  let f := fast64 c.tbl s []
  let st ← a2b64Run c (s.length + 1) f.1 { out := f.2 }
  if st.quad = 1 then
    throw (err s!"Invalid base64-encoded string: number of data characters \
      ({st.out.length / 3 * 4 + 1}) cannot be 1 more than a multiple of 4")
  if c.padded ∧ st.quad ≠ 0 ∧ st.quad + st.pads < 4 then throw (err "Incorrect padding")
  if canonical ∧ st.left ≠ 0 then throw (err "Non-zero padding bits")
  return st.out

/-- `binascii.a2b_base64`, with its clinic wrapper. `strict` is `none` when not given. -/
def a2bB64 (d : Data) (strict : Option Bool) (padded : Bool) (alpha : AlphaArg) (ig : Option Data)
    (canonical : Bool) : Py (List Nat) := do
  let s ← asciiBuffer d
  let a ← alphaDec "a2b_base64" alpha
  let ig ← bufOpt ig
  let strict := strict.getD ig.isSome
  let ig := if !strict || ig.isNone || ig == some [] then none else ig
  let t ← decTable a (revT b64Alpha (some 61)) 64 (some 61)
  a2b64Core ⟨strict, padded, t, ig⟩ canonical s

/-- `base64_encode_fast`, `Modules/binascii.c:133-147`, with `base64_encode_trio`. -/
def fastEnc64 (t : List Nat) : List Nat → List Nat × List Nat
  | a :: b :: c :: r =>
    let v := a * 65536 + b * 256 + c
    let x := fastEnc64 t r
    ([t.getD (v / 2 ^ 18 % 64) 0, t.getD (v / 2 ^ 12 % 64) 0, t.getD (v / 2 ^ 6 % 64) 0,
      t.getD (v % 64) 0] ++ x.1, x.2)
  | s => ([], s)

/-- The tail, `Modules/binascii.c:1019-1036`. -/
def tail64 (t : List Nat) : List Nat → List Nat
  | [a] => [t.getD (a / 4 % 64) 0, t.getD (a * 16 % 64) 0]
  | [a, b] =>
    let v := a * 256 + b
    [t.getD (v / 2 ^ 10 % 64) 0, t.getD (v / 2 ^ 4 % 64) 0, t.getD (v * 4 % 64) 0]
  | _ => []

/-- `binascii_b2a_base64_impl`, `Modules/binascii.c:960-1049`, past its argument checks. -/
def b2a64Core (t data : List Nat) (padded : Bool) (wrapcol : Nat) (newline : Bool) : List Nat :=
  let n := data.length
  let pads := (3 - n % 3) % 3 * 4 / 3
  let pads := if padded then pads else 0
  let f := fastEnc64 t data
  let out := f.1 ++ tail64 t f.2 ++ List.replicate pads 61
  let wrapcol := if wrapcol = 0 then 0 else if wrapcol < 4 then 4 else wrapcol / 4 * 4
  let out := if wrapcol ≠ 0 then wraplinesC out wrapcol else out
  if newline then out ++ [10] else out

/-- `binascii.b2a_base64`, with its clinic wrapper. -/
def b2aB64 (d : Data) (padded : Bool) (wrapcol : Int) (newline : Bool) (alpha : Option Data) :
    Py (List Nat) := do
  let data ← bufData d
  let w ← sizeT wrapcol
  let a ← bufOpt alpha
  let t ← encTable a b64Alpha 64
  return b2a64Core t data padded w newline

/-! ### base32 -/

/-- The state of `binascii_a2b_base32_impl`. -/
structure Dec32 where
  octa : Nat := 0
  pads : Nat := 0
  left : Nat := 0
  out : List Nat := []
  deriving Repr, DecidableEq, Inhabited

/-- The `switch (octa_pos)`, `Modules/binascii.c:1777-1817`. -/
def decStep32 (st : Dec32) (v : Nat) : Dec32 :=
  match st.octa with
  | 0 => { st with octa := 1, left := v }
  | 1 => { st with octa := 2, out := st.out ++ [(st.left * 8 + v / 4) % 256], left := v % 4 }
  | 2 => { st with octa := 3, left := (st.left * 32 + v) % 256 }
  | 3 => { st with octa := 4, out := st.out ++ [(st.left * 2 + v / 16) % 256], left := v % 16 }
  | 4 => { st with octa := 5, out := st.out ++ [(st.left * 16 + v / 2) % 256], left := v % 2 }
  | 5 => { st with octa := 6, left := (st.left * 32 + v) % 256 }
  | 6 => { st with octa := 7, out := st.out ++ [(st.left * 4 + v / 8) % 256], left := v % 8 }
  | _ => { st with octa := 0, out := st.out ++ [(st.left * 32 + v) % 256], left := 0 }

/-- `base32_decode_octa`, `Modules/binascii.c:326-349`. -/
def octa32 (t : Nat → Nat) (l : List Nat) : Option (List Nat) :=
  let v := l.map t
  if v.any (· ≥ 32) then none
  else
    let g (i : Nat) := v.getD i 0
    some [(g 0 * 8 + g 1 / 4) % 256, (g 1 * 64 + g 2 * 2 + g 3 / 16) % 256, (g 3 * 16 + g 4 / 2) % 256,
          (g 4 * 128 + g 5 * 4 + g 6 / 8) % 256, (g 6 * 32 + g 7) % 256]

/-- `base32_decode_fast`, `Modules/binascii.c:356-370`. -/
def fast32 (t : Nat → Nat) : (fuel : Nat) → List Nat → List Nat → List Nat × List Nat
  | 0, s, out => (s, out)
  | fuel + 1, s, out =>
    if s.length ≥ 8 then
      match octa32 t (s.take 8) with
      | some o => fast32 t fuel (s.drop 8) (out ++ o)
      | none => (s, out)
    else (s, out)

/-- The slow path, `Modules/binascii.c:1715-1818`. -/
def a2b32Run (t : Nat → Nat) (padded : Bool) (ig : Option (List Nat)) :
    (fuel : Nat) → List Nat → Dec32 → Py Dec32
  | 0, _, _ => .error .modelFuel
  | _ + 1, [], st => .ok st
  | fuel + 1, x :: xs, st =>
    if padded && x == 61 then
      let pads := st.pads + 1
      let st' := { st with pads }
      if (st.octa == 2 || st.octa == 4 || st.octa == 5 || st.octa == 7) && decide (st.octa + pads ≤ 8) then
        a2b32Run t padded ig fuel xs st'
      else if ign ig 61 then a2b32Run t padded ig fuel xs st'
      else if st.octa == 1 || st.octa == 3 || st.octa == 6 then .ok st'
      else .error (err (if st.octa = 0 ∧ st.out.isEmpty then "Leading padding not allowed"
                        else "Excess padding not allowed"))
    else
      let v := t x
      if v ≥ 32 then
        if !ign ig x then
          .error (err (if x = 61 then "Padding not allowed" else "Only base32 data is allowed"))
        else a2b32Run t padded ig fuel xs st
      else if st.pads ≠ 0 ∧ !ign ig 61 then
        .error (err (if st.octa + st.pads = 8 then "Excess data after padding"
                     else "Discontinuous padding not allowed"))
      else
        let st' := decStep32 st v
        if st.octa = 7 then
          let f := fast32 t xs.length xs st'.out
          a2b32Run t padded ig fuel f.1 { st' with out := f.2, pads := 0 }
        else a2b32Run t padded ig fuel xs st'

/-- `binascii_a2b_base32_impl`, `Modules/binascii.c:1656-1858`, from the fast path on. -/
def a2b32Core (t : Nat → Nat) (padded : Bool) (ig : Option (List Nat)) (canonical : Bool) (s : List Nat) :
    Py (List Nat) := do
  let f := fast32 t s.length s []
  let st ← a2b32Run t padded ig (s.length + 1) f.1 { out := f.2 }
  if st.octa == 1 || st.octa == 3 || st.octa == 6 then
    throw (err s!"Invalid base32-encoded string: number of data characters \
      ({st.out.length / 5 * 8 + st.octa}) cannot be 1, 3, or 6 more than a multiple of 8")
  if padded ∧ st.octa ≠ 0 ∧ st.octa + st.pads < 8 then throw (err "Incorrect padding")
  if canonical ∧ st.left ≠ 0 then throw (err "Non-zero padding bits")
  return st.out

/-- `binascii.a2b_base32`, with its clinic wrapper. -/
def a2bB32 (d : Data) (padded : Bool) (alpha : AlphaArg) (ig : Data) (canonical : Bool) : Py (List Nat) := do
  let s ← asciiBuffer d
  let a ← alphaDec "a2b_base32" alpha
  let ig ← bufData ig
  let t ← decTable a (revT b32Alpha none) 32 (some 61)
  a2b32Core t padded (if ig.isEmpty then none else some ig) canonical s

/-- `base32_encode_fast`, `Modules/binascii.c:306-320`, with `base32_encode_quint`. -/
def fastEnc32 (t : List Nat) : (fuel : Nat) → List Nat → List Nat × List Nat
  | 0, s => ([], s)
  | fuel + 1, s =>
    if s.length ≥ 5 then
      let v := (s.take 5).foldl (fun x b => x * 256 + b) 0
      let x := fastEnc32 t fuel (s.drop 5)
      (((List.range 8).map fun i => t.getD (v / 2 ^ (35 - 5 * i) % 32) 0) ++ x.1, x.2)
    else ([], s)

/-- The tail, `Modules/binascii.c:1930-1975`. -/
def tail32 (t s : List Nat) : List Nat :=
  let g (v sh : Nat) : Nat := t.getD (v / 2 ^ sh % 32) 0
  let h (v m : Nat) : Nat := t.getD (v * m % 32) 0
  match s with
  | [a] => [g a 3, h a 4]
  | [a, b] =>
    let v := a * 256 + b
    [g v 11, g v 6, g v 1, h v 16]
  | [a, b, c] =>
    let v := a * 65536 + b * 256 + c
    [g v 19, g v 14, g v 9, g v 4, h v 2]
  | [a, b, c, d] =>
    let v := a * 16777216 + b * 65536 + c * 256 + d
    [g v 27, g v 22, g v 17, g v 12, g v 7, g v 2, h v 8]
  | _ => []

/-- `binascii_b2a_base32_impl`, `Modules/binascii.c:1874-1986`, past its argument checks. -/
def b2a32Core (t data : List Nat) (padded : Bool) (wrapcol : Nat) : List Nat :=
  let n := data.length
  let pads := (5 - n % 5) % 5 * 8 / 5
  let pads := if padded then pads else 0
  let f := fastEnc32 t n data
  let out := f.1 ++ tail32 t f.2 ++ List.replicate pads 61
  if wrapcol ≠ 0 ∧ !out.isEmpty then
    wraplinesC out (if wrapcol < 8 then 8 else wrapcol / 8 * 8)
  else out

/-- `binascii.b2a_base32`, with its clinic wrapper. -/
def b2aB32 (d : Data) (padded : Bool) (wrapcol : Int) (alpha : Option Data) : Py (List Nat) := do
  let data ← bufData d
  let w ← sizeT wrapcol
  let a ← bufOpt alpha
  let t ← encTable a b32Alpha 32
  return b2a32Core t data padded w

/-! ### Ascii85 and base85 -/

/-- `pow85`, `Modules/binascii.c:248`. -/
def pow85 (n : Nat) : Nat := 85 ^ n

/-- `canonical_top / pow85[n_pad] != leftchar / pow85[n_pad]`, `Modules/binascii.c:1229-1233`. -/
def nonCanon (left chunk : Nat) : Bool :=
  let n := 4 - chunk
  let top := left / 2 ^ (n * 8) * 2 ^ (n * 8)
  top / pow85 n != left / pow85 n

/-- The first `chunk` bytes of a big-endian word. -/
def word4 (w chunk : Nat) : List Nat :=
  (List.range chunk).map fun i => w / 2 ^ (24 - 8 * i) % 256

/-- The state of the Ascii85 loop. `from_z` says the group came from `z`. -/
structure Dec85 where
  left : Nat := 0
  pos : Nat := 0
  fromZ : Bool := false
  out : List Nat := []
  deriving Repr, DecidableEq, Inhabited

/-- "Write current chunk", `Modules/binascii.c:1189-1247`. `len` is `ascii_len`, 1 or more while there
is input, and 0, -1, ... on the padding digits. -/
def flushA85 (canonical : Bool) (len : Int) (st : Dec85) : Py Dec85 :=
  let chunk : Nat := if len < 1 then (3 + len).toNat else 4
  if chunk = 0 then .error (err "Incomplete Ascii85 group")
  else
    let out := st.out ++ word4 st.left chunk
    if canonical && chunk == 4 && st.left == 0 && !st.fromZ then
      .error (err "Non-canonical encoding, use 'z' for all-zero groups")
    else if canonical && decide (chunk < 4) && nonCanon st.left chunk then
      .error (err "Non-zero padding bits")
    else .ok { out }

/-- `Non-Ascii85 digit found: %c`: `%c` of a byte, one character. -/
def chr1 (c : Nat) : String := String.singleton (Char.ofNat c)

/-- The loop of `binascii_a2b_ascii85_impl`, `Modules/binascii.c:1137-1248`. The input comes first,
then the padding digits, so `len` goes to 0 and below. -/
def a2bA85Loop (foldspaces canonical : Bool) (ig : List Nat) :
    (fuel : Nat) → List Nat → Int → Dec85 → Py Dec85
  | 0, _, _, _ => .error .modelFuel
  | fuel + 1, s, len, st =>
    if len ≤ 0 && st.pos == 0 then .ok st
    else
      let (cur, rest) : Option Nat × List Nat :=
        match s with
        | c :: r => (some c, r)
        | [] => (none, [])
      let digit : Nat :=
        match cur with
        | some c => revT a85Alpha none c
        | none => 84
      let next (st : Dec85) : Py Dec85 :=
        if st.pos != 5 then a2bA85Loop foldspaces canonical ig fuel rest (len - 1) st
        else
          match flushA85 canonical len st with
          | .error e => .error e
          | .ok st => a2bA85Loop foldspaces canonical ig fuel rest (len - 1) st
      if digit < 85 then
        if st.pos == 4 && decide (st.left * 85 + digit ≥ 2 ^ 32) then .error (err "Ascii85 overflow")
        else next { st with left := st.left * 85 + digit, pos := st.pos + 1 }
      else
        let c := cur.getD 0
        if (c == 121 && foldspaces) || c == 122 then
          if st.pos != 0 then .error (err s!"'{chr1 c}' inside Ascii85 5-tuple")
          else next { st with left := if c == 121 then 0x20202020 else 0, fromZ := c == 122, pos := 5 }
        else if !ig.contains c then .error (err s!"Non-Ascii85 digit found: {chr1 c}")
        else next st

/-- `binascii_a2b_ascii85_impl`, `Modules/binascii.c:1070-1255`. -/
def a2bA85Core (foldspaces adobe : Bool) (ig : List Nat) (canonical : Bool) (s : List Nat) : Py (List Nat) := do
  let s ←
    if adobe then
      if s.length < 2 || s.getD (s.length - 2) 0 != 126 || s.getD (s.length - 1) 0 != 62 then
        throw (err "Ascii85 encoded byte sequences must end with b'~>'")
      let t := s.take (s.length - 2)
      if t.length ≥ 2 && t.getD 0 0 == 60 && t.getD 1 0 == 126 then pure (t.drop 2) else pure t
    else pure s
  let st ← a2bA85Loop foldspaces canonical ig (s.length + 6) s s.length {}
  return st.out

/-- `binascii.a2b_ascii85`, with its clinic wrapper. -/
def a2bA85 (d : Data) (foldspaces adobe : Bool) (ig : Data) (canonical : Bool) : Py (List Nat) := do
  let s ← asciiBuffer d
  let ig ← bufData ig
  a2bA85Core foldspaces adobe ig canonical s

/-- Five digits of a word, most significant first. -/
def digits85 (t : List Nat) (w : Nat) : List Nat :=
  (List.range 5).map fun i => t.getD (w / 85 ^ (4 - i) % 85) 0

/-- The word of up to four bytes, zero-padded on the right. -/
def wordOf (s : List Nat) : Nat := (s ++ List.replicate (4 - s.length) 0).foldl (fun x b => x * 256 + b) 0

/-- The full chunks of `binascii_b2a_ascii85_impl`, `Modules/binascii.c:1321-1343`. -/
def fullA85 (foldspaces : Bool) : (fuel : Nat) → List Nat → List Nat × List Nat
  | 0, s => ([], s)
  | fuel + 1, s =>
    if s.length ≥ 4 then
      let w := wordOf (s.take 4)
      let g : List Nat :=
        if w == 0 then [122]
        else if foldspaces && w == 0x20202020 then [121]
        else digits85 a85Alpha w
      let x := fullA85 foldspaces fuel (s.drop 4)
      (g ++ x.1, x.2)
    else ([], s)

/-- The partial chunk, `Modules/binascii.c:1346-1367`. -/
def partA85 (pad : Bool) (s : List Nat) : List Nat :=
  if s.isEmpty then []
  else
    let w := wordOf s
    if pad && w == 0 then [122]
    else (digits85 a85Alpha w).take (if pad then 5 else s.length + 1)

/-- `binascii_b2a_ascii85_impl`, `Modules/binascii.c:1275-1386`, past its conversions. The last lines
move a lone `>` back: the newline goes before the `~>`. -/
def b2aA85Core (data : List Nat) (foldspaces : Bool) (wrapcol : Nat) (pad adobe : Bool) : List Nat :=
  let wrapcol := if adobe && wrapcol == 1 then 2 else wrapcol
  let f := fullA85 foldspaces data.length data
  let body := f.1 ++ partA85 pad f.2
  let out := if adobe then [60, 126] ++ body ++ [126, 62] else body
  let outLen := (data.length + 3) / 4 * 5 + (if adobe then 4 else 0) -
    (if !pad && data.length % 4 != 0 then 4 - data.length % 4 else 0)
  if wrapcol ≠ 0 ∧ outLen ≠ 0 then
    let w := wraplinesC out wrapcol
    let n := w.length
    if adobe && n ≥ 2 && w.getD (n - 2) 0 == 10 then w.take (n - 3) ++ [10, 126, 62] else w
  else out

/-- `binascii.b2a_ascii85`, with its clinic wrapper. -/
def b2aA85 (d : Data) (foldspaces : Bool) (wrapcol : Int) (pad adobe : Bool) : Py (List Nat) := do
  let data ← bufData d
  let w ← sizeT wrapcol
  return b2aA85Core data foldspaces w pad adobe

/-- The state of the base85 loop. -/
structure St85 where
  left : Nat := 0
  pos : Nat := 0
  out : List Nat := []
  deriving Repr, DecidableEq, Inhabited

/-- The loop of `binascii_a2b_base85_impl`, `Modules/binascii.c:1445-1525`. `total` is `data->len`. -/
def a2bB85Loop (t : Nat → Nat) (ig : Option (List Nat)) (canonical : Bool) (total : Nat) :
    (fuel : Nat) → List Nat → Int → St85 → Py St85
  | 0, _, _, _ => .error .modelFuel
  | fuel + 1, s, len, st =>
    if len ≤ 0 && st.pos == 0 then .ok st
    else
      let (cur, rest) : Option Nat × List Nat :=
        match s with
        | c :: r => (some c, r)
        | [] => (none, [])
      let digit : Nat :=
        match cur with
        | some c => t c
        | none => 84
      let next (st : St85) : Py St85 :=
        if st.pos != 5 then a2bB85Loop t ig canonical total fuel rest (len - 1) st
        else
          let chunk : Nat := if len < 1 then (3 + len).toNat else 4
          if chunk = 0 then .error (err "Incomplete Base85 group")
          else if canonical && decide (chunk < 4) && nonCanon st.left chunk then
            .error (err "Non-zero padding bits")
          else
            a2bB85Loop t ig canonical total fuel rest (len - 1) { out := st.out ++ word4 st.left chunk }
      if digit < 85 then
        if st.pos == 4 && decide (st.left * 85 + digit ≥ 2 ^ 32) then
          .error (err s!"Base85 overflow in hunk starting at byte {(((total : Int) - len).toNat) / 5 * 5}")
        else next { st with left := st.left * 85 + digit, pos := st.pos + 1 }
      else if !ign ig (cur.getD 0) then
        .error (err s!"bad Base85 character at position {(total : Int) - len}")
      else next st

/-- `binascii.a2b_base85`, with its clinic wrapper. -/
def a2bB85 (d : Data) (alpha : AlphaArg) (ig : Data) (canonical : Bool) : Py (List Nat) := do
  let s ← asciiBuffer d
  let a ← alphaDec "a2b_base85" alpha
  let ig ← bufData ig
  let t ← decTable a (revT b85Alpha none) 85 none
  let st ← a2bB85Loop t (if ig.isEmpty then none else some ig) canonical s.length (s.length + 6) s s.length {}
  return st.out

/-- The full chunks of `binascii_b2a_base85_impl`, `Modules/binascii.c:1595-1610`. -/
def fullB85 (t : List Nat) : (fuel : Nat) → List Nat → List Nat × List Nat
  | 0, s => ([], s)
  | fuel + 1, s =>
    if s.length ≥ 4 then
      let x := fullB85 t fuel (s.drop 4)
      (digits85 t (wordOf (s.take 4)) ++ x.1, x.2)
    else ([], s)

/-- `binascii_b2a_base85_impl`, `Modules/binascii.c:1550-1637`, past its checks. -/
def b2aB85Core (t data : List Nat) (pad : Bool) (wrapcol : Nat) : List Nat :=
  let f := fullB85 t data.length data
  let part :=
    if f.2.isEmpty then [] else (digits85 t (wordOf f.2)).take (if pad then 5 else f.2.length + 1)
  let out := f.1 ++ part
  if wrapcol ≠ 0 ∧ !out.isEmpty then
    wraplinesC out (if wrapcol < 5 then 5 else wrapcol / 5 * 5)
  else out

/-- `binascii.b2a_base85`, with its clinic wrapper. -/
def b2aB85 (d : Data) (pad : Bool) (wrapcol : Int) (alpha : Option Data) : Py (List Nat) := do
  let data ← bufData d
  let w ← sizeT wrapcol
  let a ← bufOpt alpha
  let t ← encTable a b85Alpha 85
  return b2aB85Core t data pad w

/-! ### hex -/

/-- The loop of `binascii_a2b_hex_impl`, `Modules/binascii.c:2310-2343`. `pair` is `leftchar` while
`pair_pos` is 1. -/
def a2bHexIg (ig : Option (List Nat)) : List Nat → Option Nat → List Nat → Py (List Nat)
  | [], none, out => .ok out
  | [], some _, _ => .error (err "Odd number of hexadecimal digits")
  | c :: cs, pair, out =>
    let d := digitValue c
    if d ≥ 16 then
      if !ign ig c then .error (err "Non-hexadecimal digit found")
      else a2bHexIg ig cs pair out
    else
      match pair with
      | none => a2bHexIg ig cs (some d) out
      | some l => a2bHexIg ig cs none (out ++ [l * 16 + d])

/-- `binascii_a2b_hex_impl`, `Modules/binascii.c:2283-2350`, with its clinic wrapper. -/
def a2bHexI (d : Data) (ig : Data) : Py (List Nat) := do
  let s ← asciiBuffer d
  let ig ← bufData ig
  a2bHexIg (if ig.isEmpty then none else some ig) s none []

/-! ### `Lib/base64.py` -/

/-- `bytes(memoryview(x))`, or `x` when it is `bytes` already: `Lib/base64.py:303`. -/
def toBytesIg (d : Data) : Py (List Nat) := toBytesView d

/-- `b64encode`, `Lib/base64.py:49-67`. -/
def pyB64encode (s : Data) (alt : Option (List Nat)) (padded : Bool) (wrapcol : Int) : Py (List Nat) :=
  match alt with
  | some a =>
    if a.length ≠ 2 then .error (.valueError s!"~invalid altchars: {a}")
    else b2aB64 s padded wrapcol false (some (.bytes (b64Alpha.take 62 ++ a)))
  | none => b2aB64 s padded wrapcol false none

/-- `badchar` of `b64decode`, `Lib/base64.py:106-109`: which standard character the alternative
alphabet does not cover and the data holds. It only decides a warning. -/
def badcharOf (a s : List Nat) : Option Nat :=
  [43, 47].find? fun b => !a.contains b && s.contains b

/-- `b64decode`, `Lib/base64.py:70-132`, but for its warnings. `validate` and `ig` are `none` when not specified. -/
def pyB64decode (s0 : Data) (alt : Option Data) (validate : Option Bool) (padded : Bool)
    (ig : Option Data) (canonical : Bool) : Py (List Nat) := do
  let s ← bytesFromDecodeData s0
  let validate := validate.getD ig.isSome
  match alt with
  | some a =>
    let a ← bytesFromDecodeData a
    if a.length ≠ 2 then throw (.valueError s!"~invalid altchars: {a}")
    match ig with
    | some g =>
      a2bB64 (.bytes s) (some validate) padded (.bytes (b64Alpha.take 62 ++ a)) (some g) canonical
    | none =>
      a2bB64 (.bytes (translate a plusSlash s)) (some validate) padded .absent (some (.bytes [])) canonical
  | none => a2bB64 (.bytes s) (some validate) padded .absent (some (ig.getD (.bytes []))) canonical

/-- `urlsafe_b64encode`, `Lib/base64.py:155-165`. -/
def pyUrlsafeEnc (s : Data) (padded : Bool) : Py (List Nat) :=
  b2aB64 s padded 0 false (some (.bytes urlAlpha))

/-- `urlsafe_b64decode`, `Lib/base64.py:167-193`, but for its `FutureWarning`. -/
def pyUrlsafeDec (s0 : Data) (padded : Bool) : Py (List Nat) := do
  let s ← bytesFromDecodeData s0
  a2bB64 (.bytes (translate dashUnderscore plusSlash s)) (some false) padded .absent none false

/-- `b32decode`, `Lib/base64.py:235-247`. -/
def pyB32decode (s0 : Data) (casefold : Bool) (map01 : Option Data) (padded : Bool) (ig : Data)
    (canonical : Bool) : Py (List Nat) := do
  let s ← bytesFromDecodeData s0
  let s ← match map01 with
    | none => pure s
    | some m =>
      let m ← bytesFromDecodeData m
      if m.length ≠ 1 then throw (.valueError "maketrans arguments must have same length")
      pure (translate [48, 49] (79 :: m) s)
  let s := if casefold then upper s else s
  a2bB32 (.bytes s) padded .absent ig canonical

/-- `b32hexdecode`, `Lib/base64.py:256-264`. -/
def pyB32hexdecode (s0 : Data) (casefold padded : Bool) (ig : Data) (canonical : Bool) : Py (List Nat) := do
  let s ← bytesFromDecodeData s0
  let s := if casefold then upper s else s
  a2bB32 (.bytes s) padded (.bytes b32hexAlpha) ig canonical

/-- `b16encode`, `Lib/base64.py:272-284`. -/
def pyB16encode (s : Data) (wrapcol : Int) : Py (List Nat) := do
  if wrapcol = 0 then
    let d ← bufData s
    return upper (b2aHex d)
  if wrapcol < 0 then throw (.valueError "Negative wrapcol")
  let w := if wrapcol < 2 then 2 else wrapcol
  let d ← bufData s
  if w / 2 > 2 ^ 63 then
    throw (.overflowError "Python int too large to convert to C ssize_t")
  let r ← strhexBytes d (.bytes [10]) (-(w / 2))
  return upper r

/-- `b16decode`, `Lib/base64.py:287-308`. -/
def pyB16decode (s0 : Data) (casefold : Bool) (ig : Data) : Py (List Nat) := do
  if !casefold then
    let s ← bytesFromDecodeData s0
    let g ← toBytesIg ig
    let lower := [97, 98, 99, 100, 101, 102]
    if lower.any (fun b => s.contains b && !g.contains b) then
      throw (err "Non-base16 digit found")
    a2bHexI (.bytes (s.filter fun c => !lower.contains c)) (.bytes g)
  else a2bHexI s0 ig

/-- `a85decode`'s default `ignorechars`, `Lib/base64.py:336`. -/
def a85Ignore : List Nat := [32, 9, 10, 13, 11]

/-- `encodebytes`, `Lib/base64.py:446-453`, past `_input_type_check`. -/
def pyEncodebytes (s : List Nat) : List Nat :=
  let r := b2a64Core b64Alpha s true 76 true
  if r == [10] then [] else r

/-- The encoders of `Lib/base64.py` on any object, with every option at its default. -/
def encodeAnyC (name : String) (d : Data) : Py (List Nat) :=
  match name with
  | "b64encode" | "standard_b64encode" => pyB64encode d none true 0
  | "urlsafe_b64encode" => pyUrlsafeEnc d true
  | "b32encode" => b2aB32 d true 0 none
  | "b32hexencode" => b2aB32 d true 0 (some (.bytes b32hexAlpha))
  | "b16encode" => pyB16encode d 0
  | "a85encode" => b2aA85 d false 0 false false
  | "b85encode" => b2aB85 d false 0 none
  | "z85encode" => b2aB85 d false 0 (some (.bytes z85Alpha))
  | "encodebytes" => do
    inputTypeCheck (← typeCheckOf d)
    return pyEncodebytes (← bufData d)
  | _ => do
    inputTypeCheck (← typeCheckOf d)
    decodebytes (← bufData d)

end PyLean.TextLibs.Binascii
