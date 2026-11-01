import PyLean.JsonMod.Basic

/-!
The pure-Python decoder of CPython 3.14.7: `py_scanstring`, `JSONObject` and
`JSONArray` (Lib/json/decoder.py), `py_make_scanner` (Lib/json/scanner.py) and
`JSONDecoder.decode`/`raw_decode`, as obtained with
`import_fresh_module('json', blocked=['_json'])`.

Positions are Python ints: `s[i]`, `s[i:j]` and `pattern.match(s, i)` follow
Python's rules for negative indices (`pyIndex`, `pySlice`, `clampPos`), which
matters for `raw_decode(s, idx)` with `idx < 0`.

Recursion uses fuel: `pyScanOnce (n+1)` enters an array or object loop with
`n`, and each loop iteration consumes one unit. `JVal`-building hooks
(`object_hook`) and the recursion limit are out of scope.
-/

namespace PyLean.JsonMod

open PyLean

/-- `STRINGCHUNK = (.*?)(["\\\x00-\x1f])`, decoder.py:54: the terminators. -/
def isTerm (c : Nat) : Bool := c == 34 || c == 92 || c < 32

/-- Offset of the first `STRINGCHUNK` terminator. -/
def findTerm : PStr → Option Nat
  | [] => none
  | c :: t => if isTerm c then some 0 else (findTerm t).map (· + 1)

/-- The `while 1` loop of `py_scanstring`, decoder.py:83-126, from `end`
(non-negative: `chunk.end()`), with the chunks decoded so far. -/
def pyScanLoop (s : PStr) (strict : Bool) (begin : Int) : Nat → Nat → PStr → DR (PStr × Int)
  | 0, _, _ => fuelOut
  | f + 1, e, acc =>
    match findTerm (s.drop e) with
    | none => .error (.jde "Unterminated string starting at" begin)
    | some k =>
      let term := s.getD (e + k) 0
      let acc := acc ++ (s.drop e).take k
      let e := e + k + 1
      if term = 34 then .ok (acc, (e : Int))
      else if term ≠ 92 then
        if strict then .error (.jde (ctrlMsgPy term) ((e : Int) - 1))
        else pyScanLoop s strict begin f e (acc ++ [term])
      else
        match s[e]? with
        | none => .error (.jde "Unterminated string starting at" begin)
        | some esc =>
          if esc ≠ 117 then
            match backslash esc with
            | none => .error (.jde (escMsgPy esc) e)
            | some ch => pyScanLoop s strict begin f (e + 1) (acc ++ [ch])
          else
            -- `_decode_uXXXX(s, end)` raises at `end`
            match hex4 s (e + 1) with
            | none => .error (.jde "Invalid \\uXXXX escape" e)
            | some uni =>
              let e := e + 5
              if 0xd800 ≤ uni ∧ uni ≤ 0xdbff ∧ (s.drop e).take 2 = [92, 117] then
                match hex4 s (e + 2) with
                | none => .error (.jde "Invalid \\uXXXX escape" ((e : Int) + 1))
                | some uni2 =>
                  if 0xdc00 ≤ uni2 ∧ uni2 ≤ 0xdfff then
                    pyScanLoop s strict begin f (e + 6) (acc ++ [joinSurrogates uni uni2])
                  else pyScanLoop s strict begin f e (acc ++ [uni])
              else pyScanLoop s strict begin f e (acc ++ [uni])

/-- `py_scanstring(s, end, strict)`, decoder.py:70-127. The first
`STRINGCHUNK.match(s, end)` clamps `end`; `begin = end - 1`. -/
def pyScanstring (s : PStr) (e : Int) (strict : Bool) : DR (PStr × Int) :=
  pyScanLoop s strict (e - 1) (s.length + 1) (clampPos s e) []

/-- `-?` at the start of `NUMBER_RE`: the sign and the rest. -/
def reSign (t : PStr) : PStr × PStr :=
  match t with
  | 45 :: r => ([45], r)
  | r => ([], r)

/-- `(?:0|[1-9][0-9]*)`. -/
def reInt (t : PStr) : Option PStr :=
  match t with
  | 48 :: _ => some [48]
  | c :: r => if 49 ≤ c ∧ c ≤ 57 then some (c :: r.take (digitsLen r)) else none
  | [] => none

/-- `(\.[0-9]+)?` (`[]` when the group does not participate). -/
def reFrac (t : PStr) : PStr :=
  match t with
  | 46 :: r => if digitsLen r = 0 then [] else 46 :: r.take (digitsLen r)
  | _ => []

/-- `([eE][-+]?[0-9]+)?`. -/
def reExp (t : PStr) : PStr :=
  match t with
  | e :: r =>
    if e = 101 ∨ e = 69 then
      let (sg, r2) : PStr × PStr := match r with
        | 45 :: r2 => ([45], r2)
        | 43 :: r2 => ([43], r2)
        | _ => ([], r)
      if digitsLen r2 = 0 then [] else e :: sg ++ r2.take (digitsLen r2)
    else []
  | [] => []

/-- `NUMBER_RE = (-?(?:0|[1-9][0-9]*))(\.[0-9]+)?([eE][-+]?[0-9]+)?`,
scanner.py:11-13, matched at the start of `t`: the groups `integer`, `frac`,
`exp` (`[]` for a group that did not participate). -/
def numberRe (t : PStr) : Option (PStr × PStr × PStr) :=
  let (sign, t1) := reSign t
  match reInt t1 with
  | none => none
  | some ip =>
    let t2 := t1.drop ip.length
    let frac := reFrac t2
    let exp := reExp (t2.drop frac.length)
    some (sign ++ ip, frac, exp)

/-- `nextchar in _ws` for `nextchar = s[i:i+1]` (`'' in ' \t\n\r'` is true). -/
def inWsSlice (t : PStr) : Bool :=
  match t with
  | [] => true
  | [c] => isWs c
  | _ => false

/-- The `try:` blocks that skip white space after `,` (decoder.py:248-255) and
`:` (decoder.py:178-184):
`if s[end] in _ws: end += 1; if s[end] in _ws: end = _w(s, end + 1).end()`,
then (array only) `nextchar = s[end:end + 1]`. Returns `end` and `nextchar`,
which keeps its previous value `nc` when `IndexError` ends the block. -/
def pyTryWs (s : PStr) (e : Int) (nc : PStr) : Int × PStr :=
  match pyIndex s e with
  | none => (e, nc)
  | some c =>
    if isWs c then
      match pyIndex s (e + 1) with
      | none => (e + 1, nc)
      | some c2 =>
        let e' := if isWs c2 then wsEndPy s (e + 2) else e + 1
        (e', pySlice s e' (e' + 1))
    else (e, pySlice s e (e + 1))

/-- The part of `JSONArray` after one element was scanned, decoder.py:237-257:
`end` is the element's end. Returns the error, `]` (array closed at the new
`end`), or the position of the next element. -/
inductive ArrStep where
  | close (e : Int)
  | next (e : Int)
  | err (e : DErr)

def pyArrAfter (s : PStr) (e : Int) : ArrStep :=
  let nc := pySlice s e (e + 1)
  let (e, nc) : Int × PStr :=
    if inWsSlice nc then (wsEndPy s (e + 1), pySlice s (wsEndPy s (e + 1)) (wsEndPy s (e + 1) + 1))
    else (e, nc)
  let e := e + 1
  if nc = [93] then .close e
  else if nc ≠ [44] then .err (.jde "Expecting ',' delimiter" (e - 1))
  else
    let comma := e - 1
    -- the `try:` block, decoder.py:248-255; `IndexError` leaves `nextchar == ','`
    let (e, nc) := pyTryWs s e nc
    if nc = [93] then .err (.jde "Illegal trailing comma before end of array" comma)
    else .next e

/-- The part of `JSONObject` after a key was scanned up to the value,
decoder.py:172-185: the position where the value is scanned. -/
def pyObjColon (s : PStr) (e : Int) : Except DErr Int :=
  let e' : Int := if pySlice s e (e + 1) ≠ [58] then wsEndPy s e else e
  if pySlice s e' (e' + 1) ≠ [58] then .error (.jde "Expecting ':' delimiter" e')
  else
    -- the `try:` block, decoder.py:178-184
    .ok (pyTryWs s (e' + 1) []).1

/-- decoder.py:191-197: `try: nextchar = s[end]; if nextchar in _ws:
end = _w(s, end + 1).end(); nextchar = s[end]` `except IndexError: nextchar = ''`
(`none` stands for `''`). -/
def pyNextChar (s : PStr) (e : Int) : Int × Option Nat :=
  match pyIndex s e with
  | none => (e, none)
  | some c =>
    if isWs c then (wsEndPy s (e + 1), pyIndex s (wsEndPy s (e + 1)))
    else (e, some c)

/-- Outcome of the part of `JSONObject` after a value, decoder.py:191-212. -/
inductive ObjStep where
  | close (e : Int)
  /-- Next key: `end` is past its opening quote. -/
  | next (e : Int)
  | err (e : DErr)

def pyObjAfter (s : PStr) (e : Int) : ObjStep :=
  let (e, nc) := pyNextChar s e
  let e := e + 1
  if nc = some 125 then .close e
  else if nc ≠ some 44 then .err (.jde "Expecting ',' delimiter" (e - 1))
  else
    let comma := e - 1
    let e := wsEndPy s e
    let nc := pySlice s e (e + 1)
    let e := e + 1
    if nc ≠ [34] then
      if nc = [125] then .err (.jde "Illegal trailing comma before end of object" comma)
      else .err (.jde "Expecting property name enclosed in double quotes" (e - 1))
    else .next e

/-- `dict(pairs)` or `object_pairs_hook(pairs)`, decoder.py:156-162, 213-219. -/
def pyMkObj (cfg : DCfg) (pairs : List (PStr × JVal)) : JVal :=
  if cfg.pairsHook then .obj pairs else .obj (dictOf pairs)

/-- `NUMBER_RE` and the literals after it in `_scan_once`, scanner.py:48-63. -/
def pyScanNumber (cfg : DCfg) (s : PStr) (idx : Int) (c : Nat) : DR (JVal × Int) :=
  let p := clampPos s idx
  match numberRe (s.drop p) with
  | some (i, fr, ex) =>
    let e : Int := (p + (i.length + fr.length + ex.length) : Nat)
    if fr ≠ [] ∨ ex ≠ [] then .ok (.hook .float (i ++ fr ++ ex), e)
    else (parseInt cfg i).map (·, e)
  | none =>
    if c = 78 ∧ pySlice s idx (idx + 3) = cs "NaN" then .ok (.hook .const (cs "NaN"), idx + 3)
    else if c = 73 ∧ pySlice s idx (idx + 8) = cs "Infinity" then
      .ok (.hook .const (cs "Infinity"), idx + 8)
    else if c = 45 ∧ pySlice s idx (idx + 9) = cs "-Infinity" then
      .ok (.hook .const (cs "-Infinity"), idx + 9)
    else .error (.stop idx)

mutual
/-- `_scan_once(string, idx)`, scanner.py:28-63. -/
def pyScanOnce (cfg : DCfg) (s : PStr) : Nat → Int → DR (JVal × Int)
  | 0, _ => fuelOut
  | n + 1, idx =>
    match pyIndex s idx with
    | none => .error (.stop idx)
    | some c =>
      if c = 34 then
        match pyScanstring s (idx + 1) cfg.strict with
        | .ok (v, e) => .ok (.str v, e)
        | .error err => .error err
      else if c = 123 then
        -- `JSONObject((string, idx + 1), ...)`, decoder.py:139-166
        let e := idx + 1
        let nc := pySlice s e (e + 1)
        if nc ≠ [34] then
          let (e, nc) : Int × PStr :=
            if inWsSlice nc then (wsEndPy s e, pySlice s (wsEndPy s e) (wsEndPy s e + 1)) else (e, nc)
          if nc = [125] then .ok (pyMkObj cfg [], e + 1)
          else if nc ≠ [34] then .error (.jde "Expecting property name enclosed in double quotes" e)
          else pyObjLoop cfg s n (e + 1) []
        else pyObjLoop cfg s n (e + 1) []
      else if c = 91 then
        -- `JSONArray((string, idx + 1), _scan_once)`, decoder.py:221-231
        let e := idx + 1
        let nc := pySlice s e (e + 1)
        let (e, nc) : Int × PStr :=
          if inWsSlice nc then (wsEndPy s (e + 1), pySlice s (wsEndPy s (e + 1)) (wsEndPy s (e + 1) + 1))
          else (e, nc)
        if nc = [93] then .ok (.arr [], e + 1)
        else pyArrLoop cfg s n e []
      else if c = 110 ∧ pySlice s idx (idx + 4) = cs "null" then .ok (.null, idx + 4)
      else if c = 116 ∧ pySlice s idx (idx + 4) = cs "true" then .ok (.bool true, idx + 4)
      else if c = 102 ∧ pySlice s idx (idx + 5) = cs "false" then .ok (.bool false, idx + 5)
      else pyScanNumber cfg s idx c

/-- The `while True` loop of `JSONArray`, decoder.py:232-257. -/
def pyArrLoop (cfg : DCfg) (s : PStr) : Nat → Int → List JVal → DR (JVal × Int)
  | 0, _, _ => fuelOut
  | n + 1, e, acc =>
    match pyScanOnce cfg s n e with
    | .error (.stop i) => .error (.jde "Expecting value" i)
    | .error err => .error err
    | .ok (v, e) =>
      match pyArrAfter s e with
      | .close e => .ok (.arr (acc ++ [v]), e)
      | .err err => .error err
      | .next e => pyArrLoop cfg s n e (acc ++ [v])

/-- The `while True` loop of `JSONObject`, decoder.py:167-212, entered with
`end` just past the opening quote of a key. -/
def pyObjLoop (cfg : DCfg) (s : PStr) : Nat → Int → List (PStr × JVal) → DR (JVal × Int)
  | 0, _, _ => fuelOut
  | n + 1, e, pairs =>
    match pyScanstring s e cfg.strict with
    | .error err => .error err
    | .ok (key, e) =>
      match pyObjColon s e with
      | .error err => .error err
      | .ok e =>
        match pyScanOnce cfg s n e with
        | .error (.stop i) => .error (.jde "Expecting value" i)
        | .error err => .error err
        | .ok (v, e) =>
          match pyObjAfter s e with
          | .close e => .ok (pyMkObj cfg (pairs ++ [(key, v)]), e)
          | .err err => .error err
          | .next e => pyObjLoop cfg s n e (pairs ++ [(key, v)])
end

/-- Fuel for one document: every two nested calls consume a character. -/
def docFuel (s : PStr) : Nat := 4 * s.length + 8

/-- Turns `StopIteration(i)` into `JSONDecodeError("Expecting value", s, i)`. -/
def stopToJde {α : Type} : DR α → DR α
  | .error (.stop i) => .error (.jde "Expecting value" i)
  | r => r

/-- `JSONDecoder.raw_decode(s, idx)`, decoder.py:351-364. -/
def rawDecodePy (cfg : DCfg) (s : PStr) (idx : Int) : DR (JVal × Int) :=
  stopToJde (pyScanOnce cfg s (docFuel s) idx)

/-- `JSONDecoder.decode(s)`, decoder.py:340-349, for a given `raw_decode`. -/
def decodeWith (raw : PStr → Int → DR (JVal × Int)) (s : PStr) : DR JVal :=
  match raw s (wsEnd s 0) with
  | .error e => .error e
  | .ok (v, e) =>
    let e := wsEndPy s e
    if e ≠ s.length then .error (.jde "Extra data" e) else .ok v

/-- `json.loads(s)` in the pure-Python implementation. -/
def loadsPy (cfg : DCfg) (s : PStr) : DR JVal := decodeWith (rawDecodePy cfg) s

end PyLean.JsonMod
