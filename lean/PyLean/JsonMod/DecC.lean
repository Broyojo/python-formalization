import PyLean.JsonMod.Basic
import PyLean.JsonMod.DecPy

/-!
The C decoder of CPython 3.14.7, Modules/_json.c: `scanstring_unicode`,
`_parse_object_unicode`, `_parse_array_unicode`, `_match_number_unicode`,
`scan_once_unicode` and `scanner_call`.

`PyUnicode_READ(kind, str, i)` is `s.getD i 0`; every read in these functions
is guarded so that `i < len`. Indices are `Py_ssize_t`; `scanner_call` rejects
negative and out-of-range `idx`, after which every index stays in
`[0, len + 1]`, so they are `Nat`. `end_idx = len - 1` comparisons are written
with `len`: `idx <= end_idx` is `idx < len`, `idx < end_idx` is `idx + 1 < len`.

Fuel follows the same pattern as the pure-Python model: `cScanOnce (n+1)`
enters an array or object loop with `n`, and each loop iteration consumes one
unit (an object iteration after checking for the key's opening quote).
-/

namespace PyLean.JsonMod

open PyLean

/-! The C loop `while (idx <= end_idx && IS_WHITESPACE(PyUnicode_READ(kind, str, idx))) idx++;`
is `wsEnd s idx` (`idx + wsLen (s.drop idx)`). -/

/-- Result of the inner `for` loop of `scanstring_unicode`, :504-513. -/
inductive CFind where
  /-- `"` or `\` at this offset. -/
  | found (k : Nat)
  /-- A control character at this offset while `strict`. -/
  | ctrl (k : Nat)
  /-- Reached the end of the string. -/
  | eof
  deriving DecidableEq, Repr

def cFind (strict : Bool) : PStr → CFind
  | [] => .eof
  | d :: t =>
    if d = 34 ∨ d = 92 then .found 0
    else if d ≤ 31 ∧ strict then .ctrl 0
    else match cFind strict t with
      | .found k => .found (k + 1)
      | .ctrl k => .ctrl (k + 1)
      | .eof => .eof

/-- The `while (1)` loop of `scanstring_unicode`, :498-635, from `end` with the
writer's contents `acc` (`none` while the writer is empty). -/
def cScanLoop (s : PStr) (strict : Bool) (begin : Int) : Nat → Nat → Option PStr → DR (PStr × Nat)
  | 0, _, _ => fuelOut
  | f + 1, e, acc =>
    match cFind strict (s.drop e) with
    | .ctrl k => .error (.jde "Invalid control character at" ((e + k : Nat) : Int))
    | .eof => .error (.jde "Unterminated string starting at" begin)
    | .found k =>
      let next := e + k
      let c := s.getD next 0
      if c = 34 ∧ acc = none then
        -- fast path, :517-525
        .ok ((s.drop e).take k, next + 1)
      else
        let acc := acc.getD [] ++ (s.drop e).take k
        let next := next + 1
        if c = 34 then .ok (acc, next)
        else if next = s.length then .error (.jde "Unterminated string starting at" begin)
        else
          let c := s.getD next 0
          if c ≠ 117 then
            let e := next + 1
            match backslash c with
            | none => .error (.jde "Invalid \\escape" ((e - 2 : Nat) : Int))
            | some ch => cScanLoop s strict begin f e (some (acc ++ [ch]))
          else
            let next := next + 1
            let e := next + 4
            if e > s.length then .error (.jde "Invalid \\uXXXX escape" ((next - 1 : Nat) : Int))
            else
              match hex4 s next with
              | none => .error (.jde "Invalid \\uXXXX escape" ((e - 5 : Nat) : Int))
              | some c =>
                -- surrogate pair, :600-626
                if 0xd800 ≤ c ∧ c ≤ 0xdbff ∧ e + 6 < s.length ∧ s.getD e 0 = 92 ∧ s.getD (e + 1) 0 = 117 then
                  match hex4 s (e + 2) with
                  | none => .error (.jde "Invalid \\uXXXX escape" ((e + 6 - 5 : Nat) : Int))
                  | some c2 =>
                    if 0xdc00 ≤ c2 ∧ c2 ≤ 0xdfff then
                      cScanLoop s strict begin f (e + 6) (some (acc ++ [joinSurrogates c c2]))
                    else cScanLoop s strict begin f e (some (acc ++ [c]))
                else cScanLoop s strict begin f e (some (acc ++ [c]))

/-- `scanstring_unicode(pystr, end, strict)`, :470-644 (`end <= len`). -/
def cScanstring (s : PStr) (e : Nat) (strict : Bool) : DR (PStr × Nat) :=
  if s.length < e then .error (.exc (.valueError "end is out of bounds"))
  else cScanLoop s strict ((e : Int) - 1) (s.length + 1) e none

/-- The sign, :1008-1015: `if (idx > end_idx) raise_stop_iteration(start)`. -/
def cNumSign (s : PStr) (start : Nat) : Option Nat :=
  if s.getD start 0 = 45 then (if start + 1 ≥ s.length then none else some (start + 1)) else some start

/-- The integer digits, :1017-1030. -/
def cNumInt (s : PStr) (idx : Nat) : Option Nat :=
  if 49 ≤ s.getD idx 0 ∧ s.getD idx 0 ≤ 57 then some (idx + 1 + digitsLen (s.drop (idx + 1)))
  else if s.getD idx 0 = 48 then some (idx + 1) else none

/-- The fraction, :1032-1037: the new `idx` and `is_float`. -/
def cNumFrac (s : PStr) (idx : Nat) : Nat × Bool :=
  if idx + 1 < s.length ∧ s.getD idx 0 = 46 ∧ isDigit (s.getD (idx + 1) 0) then
    (idx + 2 + digitsLen (s.drop (idx + 2)), true)
  else (idx, false)

/-- The exponent, :1039-1056 (backtracking to `e_start` without digits). -/
def cNumExp (s : PStr) (idx : Nat) (isFloat : Bool) : Nat × Bool :=
  if idx + 1 < s.length ∧ (s.getD idx 0 = 101 ∨ s.getD idx 0 = 69) then
    let eStart := idx
    let idx := idx + 1
    let idx := if idx + 1 < s.length ∧ (s.getD idx 0 = 45 ∨ s.getD idx 0 = 43) then idx + 1 else idx
    let idx := idx + digitsLen (s.drop idx)
    if isDigit (s.getD (idx - 1) 0) then (idx, true) else (eStart, isFloat)
  else (idx, isFloat)

/-- `_match_number_unicode`, :984-1096, at `start < len`. -/
def cMatchNumber (cfg : DCfg) (s : PStr) (start : Nat) : DR (JVal × Nat) :=
  match cNumSign s start with
  | none => .error (.stop start)
  | some idx =>
    match cNumInt s idx with
    | none => .error (.stop start)
    | some idx =>
      let (idx, isFloat) := cNumFrac s idx
      let (idx, isFloat) := cNumExp s idx isFloat
      let numstr := (s.drop start).take (idx - start)
      if isFloat then (cfg.parseFloat numstr).map (·, idx)
      else (parseInt cfg numstr).map (·, idx)

/-- `has_pairs_hook ? PyList_Append : PyDict_SetItem`, :809-825. -/
def cAddPair (cfg : DCfg) (acc : List (PStr × JVal)) (k : PStr) (v : JVal) : List (PStr × JVal) :=
  if cfg.pairsHook.isSome then acc ++ [(k, v)] else dictSet k v acc

/-- The end of `_parse_object_unicode`, :853-864: `object_pairs_hook(rval)`, or
`object_hook(rval)`, or `rval`. -/
def cFinish (cfg : DCfg) (acc : List (PStr × JVal)) : DR JVal :=
  match cfg.pairsHook with
  | some h => h acc
  | none =>
    match cfg.objectHook with
    | some h => h acc
    | none => .ok (.obj acc)

/-- `_parse_constant`, :958-982. -/
def cConst (cfg : DCfg) (name : String) (idx : Nat) : DR (JVal × Nat) :=
  (cfg.parseConstant (cs name)).map (·, idx + (cs name).length)

/-- Matches `lit` at `idx` (the guarded `PyUnicode_READ` chains of `scan_once_unicode`). -/
def litAt (s : PStr) (idx : Nat) (lit : String) : Bool :=
  idx + (cs lit).length - 1 < s.length && (s.drop idx).take (cs lit).length == cs lit

/-- What `_parse_array_unicode` does after an element, :916-936; `.close` carries
`*next_idx_ptr = idx + 1` (:944). -/
def cArrAfter (s : PStr) (next : Nat) : ArrStep :=
  let idx := wsEnd s next
  if idx < s.length ∧ s.getD idx 0 = 93 then .close ((idx + 1 : Nat) : Int)
  else if idx ≥ s.length ∨ s.getD idx 0 ≠ 44 then .err (.jde "Expecting ',' delimiter" idx)
  else
    let comma := idx
    let idx := wsEnd s (idx + 1)
    if idx < s.length ∧ s.getD idx 0 = 93 then
      .err (.jde "Illegal trailing comma before end of array" comma)
    else .next idx

/-- What `_parse_object_unicode` does after a value, :828-847 (the next key's
quote is checked at the top of the loop, so `.next` is the quote's position);
`.close` carries `*next_idx_ptr = idx + 1` (:851). -/
def cObjAfter (s : PStr) (next : Nat) : ObjStep :=
  let idx := wsEnd s next
  if idx < s.length ∧ s.getD idx 0 = 125 then .close ((idx + 1 : Nat) : Int)
  else if idx ≥ s.length ∨ s.getD idx 0 ≠ 44 then .err (.jde "Expecting ',' delimiter" idx)
  else
    let comma := idx
    let idx := wsEnd s (idx + 1)
    if idx < s.length ∧ s.getD idx 0 = 125 then
      .err (.jde "Illegal trailing comma before end of object" comma)
    else .next idx

mutual
/-- `scan_once_unicode`, :1098-1205, at `idx >= 0`. -/
def cScanOnce (cfg : DCfg) (s : PStr) : Nat → Nat → DR (JVal × Nat)
  | 0, _ => fuelOut
  | n + 1, idx =>
    if idx ≥ s.length then .error (.stop idx)
    else
      let c := s.getD idx 0
      if c = 34 then
        match cScanstring s (idx + 1) cfg.strict with
        | .ok (v, e) => .ok (.str v, e)
        | .error err => .error err
      else if c = 123 then
        -- `_parse_object_unicode`, :773-777
        let idx := wsEnd s (idx + 1)
        if idx ≥ s.length ∨ s.getD idx 0 ≠ 125 then
          -- top of the `while (1)` loop, :781-785
          if idx ≥ s.length ∨ s.getD idx 0 ≠ 34 then
            .error (.jde "Expecting property name enclosed in double quotes" idx)
          else cObjBody cfg s n idx []
        else (cFinish cfg []).map (·, idx + 1)
      else if c = 91 then
        -- `_parse_array_unicode`, :898-942
        let idx := wsEnd s (idx + 1)
        if idx ≥ s.length ∨ s.getD idx 0 ≠ 93 then cArrLoop cfg s n idx []
        else .ok (.arr [], idx + 1)
      else if c = 110 ∧ litAt s idx "null" then .ok (.null, idx + 4)
      else if c = 116 ∧ litAt s idx "true" then .ok (.bool true, idx + 4)
      else if c = 102 ∧ litAt s idx "false" then .ok (.bool false, idx + 5)
      else if c = 78 ∧ litAt s idx "NaN" then cConst cfg "NaN" idx
      else if c = 73 ∧ litAt s idx "Infinity" then cConst cfg "Infinity" idx
      else if c = 45 ∧ litAt s idx "-Infinity" then cConst cfg "-Infinity" idx
      else cMatchNumber cfg s idx

/-- The `while (1)` loop of `_parse_array_unicode`, :903-936. -/
def cArrLoop (cfg : DCfg) (s : PStr) : Nat → Nat → List JVal → DR (JVal × Nat)
  | 0, _, _ => fuelOut
  | n + 1, idx, acc =>
    match cScanOnce cfg s n idx with
    | .error err => .error err
    | .ok (v, next) =>
      match cArrAfter s next with
      | .close i =>
        -- the check `idx > end_idx || PyUnicode_READ(...) != ']'` at :939-942
        -- cannot fail after `break`
        .ok (.arr (acc ++ [v]), i.toNat)
      | .err err => .error err
      | .next i => cArrLoop cfg s n i.toNat (acc ++ [v])

/-- One iteration of the `while (1)` loop of `_parse_object_unicode`
(:778-849) after the check for the key's opening quote at `idx`. -/
def cObjBody (cfg : DCfg) (s : PStr) : Nat → Nat → List (PStr × JVal) → DR (JVal × Nat)
  | 0, _, _ => fuelOut
  | n + 1, idx, acc =>
    match cScanstring s (idx + 1) cfg.strict with
    | .error err => .error err
    | .ok (key, next) =>
      let idx := wsEnd s next
      if idx ≥ s.length ∨ s.getD idx 0 ≠ 58 then .error (.jde "Expecting ':' delimiter" idx)
      else
        let idx := wsEnd s (idx + 1)
        match cScanOnce cfg s n idx with
        | .error err => .error err
        | .ok (v, next) =>
          let acc := cAddPair cfg acc key v
          match cObjAfter s next with
          | .close i => (cFinish cfg acc).map (·, i.toNat)
          | .err err => .error err
          | .next i =>
            -- top of the `while (1)` loop, :781-785
            if i.toNat ≥ s.length ∨ s.getD i.toNat 0 ≠ 34 then
              .error (.jde "Expecting property name enclosed in double quotes" i.toNat)
            else cObjBody cfg s n i.toNat acc
end

/-- `scanner_call(string, idx)` (:1207-1236) as used by
`JSONDecoder.raw_decode`, decoder.py:364-377: `idx` is converted with the `n`
format (`OverflowError` outside `Py_ssize_t`), then `scan_once_unicode` rejects
negative `idx`. -/
def rawDecodeC (cfg : DCfg) (s : PStr) (idx : Int) : DR (JVal × Int) :=
  if idx < ssizeMin ∨ idx > ssizeMax then
    .error (.exc (.overflowError "Python int too large to convert to C ssize_t"))
  else if idx < 0 then .error (.exc (.valueError "idx cannot be negative"))
  else
    match stopToJde (cScanOnce cfg s (docFuel s) idx.toNat) with
    | .ok (v, e) => .ok (v, (e : Int))
    | .error err => .error err

/-- `json.loads(s)` with the C scanner. -/
def loadsC (cfg : DCfg) (s : PStr) : DR JVal := decodeWith (rawDecodeC cfg) s

end PyLean.JsonMod
