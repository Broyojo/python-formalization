import PyLean.TextLibs.QpProps

/-!
`Lib/quopri.py`, CPython 3.15.2. Each of `encode`, `decode`, `encodestring` and `decodestring` has two
bodies: the one that calls `binascii`, which every build takes, and the pure-Python one below it, taken
when `b2a_qp` is `None`. They differ, so both are modelled. `quotetabs` and `header` are flags, so they
are `Bool`, a stated scope limit: the source only tests their truth.

`input` and `output` are fallible: `lines` is what successive `readline` calls return or raise, and
`FileSim.write` records every write and may raise.
-/

namespace PyLean.TextLibs.Quopri

open PyLean PyLean.TextLibs.Binascii

/-- `needsquoting`, `Lib/quopri.py:19-32`. -/
def needsQuoting (c : Nat) (quotetabs header : Bool) : Bool :=
  if c == 32 || c == 9 then quotetabs
  else if c == 95 then header
  else c == 61 || !(32 ≤ c && c ≤ 126)

/-- `quote`, `Lib/quopri.py:34-38`. -/
def quote (c : Nat) : List Nat :=
  let hex (v : Nat) := if v < 10 then 48 + v else 55 + v
  [61, hex (c / 16), hex (c % 16)]

/-- `ishex`, `Lib/quopri.py:165-168`. -/
def ishex (c : Nat) : Bool :=
  (48 ≤ c && c ≤ 57) || (97 ≤ c && c ≤ 102) || (65 ≤ c && c ≤ 70)

/-- One step of `unhex`, `Lib/quopri.py:170-184`, on a digit that `ishex` accepted. -/
def hexVal (c : Nat) : Nat :=
  if 48 ≤ c ∧ c ≤ 57 then c - 48 else if 97 ≤ c ∧ c ≤ 102 then c - 87 else c - 55

/-- `unhex`, `Lib/quopri.py:170-184`. -/
def unhex (s : List Nat) : Nat := s.foldl (fun bits c => bits * 16 + hexVal c) 0

/-- The un-length-limited line, `Lib/quopri.py:76-83`. -/
def outline (q h : Bool) (line : List Nat) : List Nat :=
  line.flatMap fun c =>
    if needsQuoting c q h then quote c
    else if h && c == 32 then [95]
    else [c]

/-- The inner `write`, `Lib/quopri.py:57-65`. -/
def writeOut (f : FileSim) (s lineEnd : List Nat) : FileSim × Py Unit :=
  match s.getLast? with
  | some l =>
    if l == 32 || l == 9 then f.write (s.dropLast ++ quote l ++ lineEnd)
    else if s == [46] then f.write (quote 46 ++ lineEnd)
    else f.write (s ++ lineEnd)
  | none => f.write lineEnd

/-- `Lib/quopri.py:90-94`. -/
def softBreaks : (fuel : Nat) → FileSim → List Nat → FileSim × Py (List Nat)
  | 0, f, _ => (f, .error .modelFuel)
  | fuel + 1, f, s =>
    if s.length > MAXLINESIZE then
      match writeOut f (s.take (MAXLINESIZE - 1)) [61, 10] with
      | (f, .error e) => (f, .error e)
      | (f, .ok ()) => softBreaks fuel f (s.drop (MAXLINESIZE - 1))
    else (f, .ok s)

/-- `Lib/quopri.py:98-99`. -/
def encodeEnd (f : FileSim) (prev : Option (List Nat)) (stripped : List Nat) : FileSim × Py Unit :=
  match prev with
  | some p => writeOut f p stripped
  | none => (f, .ok ())

/-- `Lib/quopri.py:68-99`. An empty line, or the end of `lines`, is the end of the input. -/
def encodeLoop (q h : Bool) : List (Py (List Nat)) → FileSim → Option (List Nat) → List Nat → FileSim × Py Unit
  | [], f, prev, stripped => encodeEnd f prev stripped
  | .error e :: _, f, _, _ => (f, .error e)
  | .ok line :: ls, f, prev, stripped =>
    if line.isEmpty then encodeEnd f prev stripped
    else
      let (line, stripped) :=
        if line.getLast? == some 10 then (line.dropLast, [10]) else (line, [])
      let this := outline q h line
      let w : FileSim × Py Unit :=
        match prev with
        | some p => writeOut f p [10]
        | none => (f, .ok ())
      match w with
      | (f, .error e) => (f, .error e)
      | (f, .ok ()) =>
        match softBreaks (this.length + 1) f this with
        | (f, .error e) => (f, .error e)
        | (f, .ok rest) => encodeLoop q h ls f (some rest) stripped

/-- `encode`, its pure-Python body. -/
def encodePy (lines : List (Py (List Nat))) (f : FileSim) (q h : Bool) : FileSim × Py Unit :=
  encodeLoop q h lines f none []

/-- `encode`, `Lib/quopri.py:51-55`, the body every build takes. -/
def encodeC (rd : Py (List Nat)) (f : FileSim) (q h : Bool) : FileSim × Py Unit :=
  match rd with
  | .error e => (f, .error e)
  | .ok d => f.write (b2aQp d ⟨q, true, h⟩)

/-- The lines of a `BytesIO`. -/
def bytesLines (s : List Nat) : List (Py (List Nat)) := (splitLines (s.length + 1) s).map .ok

/-- `encodestring`, `Lib/quopri.py:104-108`, its pure-Python body: `BytesIO` does not fail. -/
def encodestringPy (s : List Nat) (q h : Bool) : List Nat :=
  ((encodePy (bytesLines s) {data := []} q h).1.written).flatten

/-- `encodestring`, `Lib/quopri.py:102-103`. -/
def encodestringC (s : List Nat) (q h : Bool) : List Nat := b2aQp s ⟨q, true, h⟩

/-- The inner `while i < n`, `Lib/quopri.py:133-146`, on `line[i:n]`. `new` is newest first. -/
def decodeBody (h : Bool) : (fuel : Nat) → List Nat → List Nat → Bool → List Nat × Bool
  | 0, _, new, part => (new, part)
  | _ + 1, [], new, part => (new, part)
  | fuel + 1, c :: r, new, part =>
    if c == 95 && h then decodeBody h fuel r (32 :: new) part
    else if c != 61 then decodeBody h fuel r (c :: new) part
    else if r.isEmpty && !part then (new, true)
    else
      match r with
      | 61 :: t => decodeBody h fuel t (61 :: new) part
      | a :: b :: t =>
        if ishex a && ishex b then decodeBody h fuel t (unhex [a, b] :: new) part
        else decodeBody h fuel r (c :: new) part
      | _ => decodeBody h fuel r (c :: new) part

/-- `Lib/quopri.py:125-132`: the line up to `n`, and `part`. -/
def lineBody (line : List Nat) : List Nat × Bool :=
  if line.getLast? == some 10 then
    let body := line.dropLast.reverse.dropWhile (fun c => c == 32 || c == 9 || c == 13)
    (body.reverse, false)
  else (line, true)

/-- `Lib/quopri.py:150-151`. -/
def decodeEnd (f : FileSim) (new : List Nat) : FileSim × Py Unit :=
  if new.isEmpty then (f, .ok ()) else f.write new.reverse

/-- `Lib/quopri.py:124-151`. -/
def decodeLoop (h : Bool) : List (Py (List Nat)) → FileSim → List Nat → FileSim × Py Unit
  | [], f, new => decodeEnd f new
  | .error e :: _, f, _ => (f, .error e)
  | .ok line :: ls, f, new =>
    if line.isEmpty then decodeEnd f new
    else
      let (body, part) := lineBody line
      let (new, part) := decodeBody h (body.length + 1) body new part
      if part then decodeLoop h ls f new
      else
        match f.write (new.reverse ++ [10]) with
        | (f, .error e) => (f, .error e)
        | (f, .ok ()) => decodeLoop h ls f []

/-- `decode`, its pure-Python body. -/
def decodePy (lines : List (Py (List Nat))) (f : FileSim) (h : Bool) : FileSim × Py Unit :=
  decodeLoop h lines f []

/-- `decode`, `Lib/quopri.py:117-121`. -/
def decodeC (rd : Py (List Nat)) (f : FileSim) (h : Bool) : FileSim × Py Unit :=
  match rd with
  | .error e => (f, .error e)
  | .ok d =>
    match a2bQp (.bytes d) h with
    | .error e => (f, .error e)
    | .ok o => f.write o

/-- `decodestring`, `Lib/quopri.py:156-160`, its pure-Python body. -/
def decodestringPy (s : List Nat) (h : Bool) : List Nat :=
  ((decodePy (bytesLines s) {data := []} h).1.written).flatten

end PyLean.TextLibs.Quopri
