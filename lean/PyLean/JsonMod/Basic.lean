import PyLean.Core

/-!
Shared vocabulary for the `json` models (CPython 3.15.2).

* A Python `str` is a list of code points (`PStr`). Lone surrogates are
  ordinary code points here, as in CPython, which a Lean `String` could not hold.
* Positions are `Nat` in the C model (after `scanner_call` has rejected negative
  and out-of-range indices) and `Int` in the pure-Python model, whose indexing
  and slicing follow Python's rules for negative and out-of-range indices.
* The decoder's callbacks are abstract functions (`DCfg`): `object_hook`,
  `object_pairs_hook`, `parse_float`, `parse_int` and `parse_constant` may return
  any value or raise, and so may `array_hook`. The default `parse_int` is `int`, exact with the 4300-digit
  limit. The default `parse_float`, `float`, is abstract too: it records the text
  it receives (`JVal.hook`), until the binary64 model exists; the default
  `parse_constant` likewise.
-/

namespace PyLean.JsonMod

open PyLean

/-- A Python `str`: its code points (surrogates allowed). -/
abbrev PStr := List Nat

/-- ASCII text as code points. -/
def cs (s : String) : PStr := s.toList.map Char.toNat

/-- `' \t\n\r'`: `WHITESPACE_STR`, Lib/json/decoder.py:134, and `IS_WHITESPACE`,
Modules/_json.c:123. -/
def isWs (c : Nat) : Bool := c == 32 || c == 9 || c == 10 || c == 13

/-- Number of leading JSON whitespace code points. -/
def wsLen : PStr → Nat
  | [] => 0
  | c :: t => if isWs c then wsLen t + 1 else 0

/-- First non-whitespace index at or after `i`. -/
def wsEnd (s : PStr) (i : Nat) : Nat := i + wsLen (s.drop i)

/-- ASCII decimal digit. -/
def isDigit (c : Nat) : Bool := 48 ≤ c && c ≤ 57

/-- Number of leading ASCII digits. -/
def digitsLen : PStr → Nat
  | [] => 0
  | c :: t => if isDigit c then digitsLen t + 1 else 0

/-! ### Python indexing -/

/-- `pattern.match(s, pos)`: `_sre` clamps `pos` into `[0, len(s)]`. -/
def clampPos (s : PStr) (i : Int) : Nat := if i < 0 then 0 else min i.toNat s.length

/-- Python `s[i]`; `none` is `IndexError`. -/
def pyIndex (s : PStr) (i : Int) : Option Nat :=
  if 0 ≤ i then s[i.toNat]?
  else if -(s.length : Int) ≤ i then s[(i + s.length).toNat]? else none

/-- A slice bound after Python's adjustment (`PySlice_AdjustIndices`, step 1). -/
def sliceBound (n : Nat) (i : Int) : Nat := if i < 0 then (i + n).toNat else min i.toNat n

/-- Python `s[a:b]`. -/
def pySlice (s : PStr) (a b : Int) : PStr :=
  (s.drop (sliceBound s.length a)).take (sliceBound s.length b - sliceBound s.length a)

/-- `WHITESPACE.match(s, i).end()` with `WHITESPACE = [ \t\n\r]*`, decoder.py:133. -/
def wsEndPy (s : PStr) (i : Int) : Int := (wsEnd s (clampPos s i) : Nat)

/-! ### Values -/

/-- Which hook a decoded number went to. -/
inductive NumKind where
  | float | int | const
  deriving DecidableEq, Repr

/-- A decoded JSON value. An object is its list of (key, value) pairs: with
`object_pairs_hook=list` exactly the pairs in document order, otherwise the
`dict` (first-insertion order, last value wins). -/
inductive JVal where
  | null
  | bool (b : Bool)
  | int (n : Int)
  | str (s : PStr)
  /-- `parse_float(text)`, `parse_int(text)` (when given) or `parse_constant(text)`. -/
  | hook (k : NumKind) (text : PStr)
  | arr (xs : List JVal)
  | obj (kvs : List (PStr × JVal))
  deriving Repr, Inhabited

mutual
def JVal.beq : JVal → JVal → Bool
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .int a, .int b => a == b
  | .str a, .str b => a == b
  | .hook k a, .hook l b => k == l && a == b
  | .arr xs, .arr ys => JVal.beqList xs ys
  | .obj xs, .obj ys => JVal.beqPairs xs ys
  | _, _ => false
def JVal.beqList : List JVal → List JVal → Bool
  | [], [] => true
  | x :: xs, y :: ys => JVal.beq x y && JVal.beqList xs ys
  | _, _ => false
def JVal.beqPairs : List (PStr × JVal) → List (PStr × JVal) → Bool
  | [], [] => true
  | (k, x) :: xs, (l, y) :: ys => k == l && JVal.beq x y && JVal.beqPairs xs ys
  | _, _ => false
end

mutual
theorem JVal.eq_of_beq : ∀ a b : JVal, JVal.beq a b = true → a = b
  | .null, .null, _ => rfl
  | .bool a, .bool b, h => by simp [JVal.beq] at h; rw [h]
  | .int a, .int b, h => by simp [JVal.beq] at h; rw [h]
  | .str a, .str b, h => by simp [JVal.beq] at h; rw [h]
  | .hook k a, .hook l b, h => by simp [JVal.beq] at h; rw [h.1, h.2]
  | .arr xs, .arr ys, h => by simp only [JVal.beq] at h; rw [JVal.eq_of_beqList xs ys h]
  | .obj xs, .obj ys, h => by simp only [JVal.beq] at h; rw [JVal.eq_of_beqPairs xs ys h]
  | .null, .bool _, h | .null, .int _, h | .null, .str _, h | .null, .hook _ _, h
  | .null, .arr _, h | .null, .obj _, h
  | .bool _, .null, h | .bool _, .int _, h | .bool _, .str _, h | .bool _, .hook _ _, h
  | .bool _, .arr _, h | .bool _, .obj _, h
  | .int _, .null, h | .int _, .bool _, h | .int _, .str _, h | .int _, .hook _ _, h
  | .int _, .arr _, h | .int _, .obj _, h
  | .str _, .null, h | .str _, .bool _, h | .str _, .int _, h | .str _, .hook _ _, h
  | .str _, .arr _, h | .str _, .obj _, h
  | .hook _ _, .null, h | .hook _ _, .bool _, h | .hook _ _, .int _, h | .hook _ _, .str _, h
  | .hook _ _, .arr _, h | .hook _ _, .obj _, h
  | .arr _, .null, h | .arr _, .bool _, h | .arr _, .int _, h | .arr _, .str _, h
  | .arr _, .hook _ _, h | .arr _, .obj _, h
  | .obj _, .null, h | .obj _, .bool _, h | .obj _, .int _, h | .obj _, .str _, h
  | .obj _, .hook _ _, h | .obj _, .arr _, h => by simp [JVal.beq] at h
theorem JVal.eq_of_beqList : ∀ a b : List JVal, JVal.beqList a b = true → a = b
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [JVal.beqList, Bool.and_eq_true] at h
    rw [JVal.eq_of_beq x y h.1, JVal.eq_of_beqList xs ys h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [JVal.beqList] at h
theorem JVal.eq_of_beqPairs : ∀ a b : List (PStr × JVal), JVal.beqPairs a b = true → a = b
  | [], [], _ => rfl
  | (k, x) :: xs, (l, y) :: ys, h => by
    simp only [JVal.beqPairs, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1, JVal.eq_of_beq x y h.1.2, JVal.eq_of_beqPairs xs ys h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [JVal.beqPairs] at h
end

mutual
theorem JVal.beq_refl : ∀ a : JVal, JVal.beq a a = true
  | .null => rfl
  | .bool _ | .int _ | .str _ | .hook _ _ => by simp [JVal.beq]
  | .arr xs => by simp only [JVal.beq]; exact JVal.beqList_refl xs
  | .obj xs => by simp only [JVal.beq]; exact JVal.beqPairs_refl xs
theorem JVal.beqList_refl : ∀ a : List JVal, JVal.beqList a a = true
  | [] => rfl
  | x :: xs => by simp only [JVal.beqList, JVal.beq_refl x, JVal.beqList_refl xs, Bool.and_self]
theorem JVal.beqPairs_refl : ∀ a : List (PStr × JVal), JVal.beqPairs a a = true
  | [] => rfl
  | (k, x) :: xs => by
    simp only [JVal.beqPairs, beq_self_eq_true, JVal.beq_refl x, JVal.beqPairs_refl xs, Bool.and_self]
end

instance : DecidableEq JVal := fun a b =>
  if h : JVal.beq a b then isTrue (JVal.eq_of_beq a b h)
  else isFalse (fun e => by subst e; exact h (JVal.beq_refl a))

/-- `d[k] = v` on a dict given by its items in insertion order. -/
def dictSet (k : PStr) (v : JVal) : List (PStr × JVal) → List (PStr × JVal)
  | [] => [(k, v)]
  | (k', v') :: t => if k' = k then (k', v) :: t else (k', v') :: dictSet k v t

/-- `dict(pairs)`. -/
def dictOf (ps : List (PStr × JVal)) : List (PStr × JVal) :=
  ps.foldl (fun d p => dictSet p.1 p.2 d) []

/-! ### Errors -/

/-- Decoder outcomes other than a value. -/
inductive DErr where
  /-- `StopIteration(idx)` raised by `scan_once`. -/
  | stop (idx : Int)
  /-- `JSONDecodeError(msg, doc, pos)`. -/
  | jde (msg : String) (pos : Int)
  /-- Any other exception (`ValueError` from `int()`, `OverflowError`, ...). -/
  | exc (e : PyExc)
  deriving Repr, DecidableEq, Inhabited

abbrev DR (α : Type) := Except DErr α

instance {α : Type} [DecidableEq α] : DecidableEq (DR α)
  | .ok a, .ok b => if h : a = b then .isTrue (h ▸ rfl) else .isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then .isTrue (h ▸ rfl) else .isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => .isFalse (fun e => nomatch e)
  | .error _, .ok _ => .isFalse (fun e => nomatch e)

def fuelOut {α : Type} : DR α := .error (.exc .modelFuel)

/-- Decoder options, after `JSONDecoder.__init__`. -/
structure DCfg where
  strict : Bool := true
  /-- `object_hook`, called with the `dict`. -/
  objectHook : Option (List (PStr × JVal) → DR JVal) := none
  /-- `object_pairs_hook`, called with the list of pairs; it takes priority. -/
  pairsHook : Option (List (PStr × JVal) → DR JVal) := none
  /-- `array_hook`, called with the `list`. -/
  arrayHook : Option (List JVal → DR JVal) := none
  /-- `parse_float`: `float` unless given. -/
  parseFloat : PStr → DR JVal := fun t => .ok (.hook .float t)
  /-- `parse_int`: `int` when `none`. -/
  parseIntFn : Option (PStr → DR JVal) := none
  /-- `parse_constant`: `_CONSTANTS.__getitem__` unless given. -/
  parseConstant : PStr → DR JVal := fun t => .ok (.hook .const t)

/-- `array_hook(values)` when it is given: `JSONArray`, decoder.py:230-231, :261-262,
and `_parse_array_unicode`, Modules/_json.c:945-950. An exception of the hook
propagates. -/
def mkArr (cfg : DCfg) (xs : List JVal) : DR JVal :=
  match cfg.arrayHook with
  | some h => h xs
  | none => .ok (.arr xs)

/-- `sys.get_int_max_str_digits()` default. -/
def maxStrDigits : Nat := 4300

/-- Value of a list of ASCII digits. -/
def decVal (t : PStr) : Nat := t.foldl (fun a c => 10 * a + (c - 48)) 0

/-- `int(text)` for a text matched as a JSON integer (`-?(0|[1-9][0-9]*)`):
`PyLong_FromString`, Objects/longobject.c:3027-3031 for the digit limit. -/
def pyIntOfText (t : PStr) : Except PyExc Int :=
  let (neg, ds) : Bool × PStr := match t with
    | 45 :: ds => (true, ds)
    | ds => (false, ds)
  if ds.length > maxStrDigits then
    .error (.valueError s!"Exceeds the limit (4300 digits) for integer string conversion: value has {ds.length} digits; use sys.set_int_max_str_digits() to increase the limit")
  else .ok (if neg then -(decVal ds : Int) else (decVal ds : Int))

/-- `parse_int(text)`. -/
def parseInt (cfg : DCfg) (t : PStr) : DR JVal :=
  match cfg.parseIntFn with
  | some h => h t
  | none =>
    match pyIntOfText t with
    | .ok n => .ok (.int n)
    | .error e => .error (.exc e)

/-- `BACKSLASH`, decoder.py:55-58; the same table as the `switch` in
`scanstring_unicode`, Modules/_json.c:557-571. -/
def backslash (c : Nat) : Option Nat :=
  if c = 34 then some 34 else if c = 92 then some 92 else if c = 47 then some 47
  else if c = 98 then some 8 else if c = 102 then some 12 else if c = 110 then some 10
  else if c = 114 then some 13 else if c = 116 then some 9 else none

/-- One hex digit `[0-9A-Fa-f]`. -/
def hexVal (c : Nat) : Option Nat :=
  if 48 ≤ c ∧ c ≤ 57 then some (c - 48)
  else if 97 ≤ c ∧ c ≤ 102 then some (c - 87)
  else if 65 ≤ c ∧ c ≤ 70 then some (c - 55) else none

/-- Four hex digits at `p`: `HEXDIGITS.match(s, p)` + `int(_, 16)` in
`_decode_uXXXX` (decoder.py:60-68), and the digit loops of
`scanstring_unicode` (Modules/_json.c:581-597, 506-521). -/
def hex4 (s : PStr) (p : Nat) : Option Nat :=
  match (s.drop p).take 4 with
  | [a, b, c, d] =>
    match hexVal a, hexVal b, hexVal c, hexVal d with
    | some a, some b, some c, some d => some (((a * 16 + b) * 16 + c) * 16 + d)
    | _, _, _, _ => none
  | _ => none

/-- `Py_UNICODE_JOIN_SURROGATES` / decoder.py:123. -/
def joinSurrogates (hi lo : Nat) : Nat := 0x10000 + ((hi - 0xd800) * 1024 + (lo - 0xdc00))

/-! ### Messages -/

def hexChar (n : Nat) : Char := Char.ofNat (if n < 10 then 48 + n else 87 + n)

/-- `repr()` of a one-character ASCII string. -/
def reprAscii (c : Nat) : String :=
  if c = 39 then "\"'\""
  else if c = 92 then "'\\\\'"
  else if c = 9 then "'\\t'"
  else if c = 10 then "'\\n'"
  else if c = 13 then "'\\r'"
  else if c < 32 ∨ c = 127 then "'\\x" ++ String.ofList [hexChar (c / 16), hexChar (c % 16)] ++ "'"
  else "'" ++ String.ofList [Char.ofNat c] ++ "'"

/-- `"Invalid control character {0!r} at".format(c)` (decoder.py:99), `c < 32`. -/
def ctrlMsgPy (c : Nat) : String := "Invalid control character " ++ reprAscii c ++ " at"

/-- `"Invalid \\escape: {0!r}".format(c)` (decoder.py:114). The model renders
`repr` exactly for ASCII only; other messages are marked `~`. -/
def escMsgPy (c : Nat) : String :=
  if c < 128 then "Invalid \\escape: " ++ reprAscii c else "~Invalid \\escape: (non-ASCII)"

/-- `doc.count('\n', 0, pos)`. -/
def countNl (doc : PStr) (pos : Int) : Nat := ((pySlice doc 0 pos).filter (· == 10)).length

/-- `doc.rfind('\n', 0, pos)`. -/
def rfindNl (doc : PStr) (pos : Int) : Int :=
  let pre := pySlice doc 0 pos
  match (pre.zipIdx.filter (·.1 == 10)).getLast? with
  | some (_, i) => i
  | none => -1

/-- `JSONDecodeError.__init__`, decoder.py:31-40: `(lineno, colno)`. -/
def lineCol (doc : PStr) (pos : Int) : Int × Int := (countNl doc pos + 1, pos - rfindNl doc pos)

/-- The exception a decoder outcome stands for: `str(JSONDecodeError)` is
`'%s: line %d column %d (char %d)' % (msg, lineno, colno, pos)`. -/
def DErr.toPy (doc : PStr) : DErr → PyExc
  | .stop i => .named "StopIteration" s!"{i}"
  | .jde msg pos =>
    let (l, c) := lineCol doc pos
    .named "JSONDecodeError" s!"{msg}: line {l} column {c} (char {pos})"
  | .exc e => e

end PyLean.JsonMod
