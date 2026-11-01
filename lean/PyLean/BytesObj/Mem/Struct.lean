import PyLean.BytesObj.Mem.Base

/-!
The part of `struct.Struct` that `memoryview` comparison reaches through
`struct_get_unpacker` (memoryobject.c:2075-2124): format parsing (`whichtable`,
`prepare_s`, Modules/_struct.c:1557-1579, :1625-1720) and `unpack_from`
(`s_unpack_internal`). Formats reach it as C strings from a buffer exporter.
-/

namespace PyLean.BytesObj.Mem

open PyLean

/-- `native_table` sizes (`Modules/_struct.c`), 64-bit Linux and macOS. The alignment of
each is its size; `x c b B ? s p` have size 1. -/
def nativeSize : Char → Option Nat
  | 'x' | 'c' | 'b' | 'B' | '?' | 's' | 'p' => some 1
  | 'h' | 'H' | 'e' => some 2
  | 'i' | 'I' | 'f' => some 4
  | 'l' | 'L' | 'n' | 'N' | 'q' | 'Q' | 'd' | 'P' => some 8
  | _ => none

/-- `lilendian_table` / `bigendian_table` sizes: no alignment, no `n N P`. -/
def standardSize : Char → Option Nat
  | 'x' | 'c' | 'b' | 'B' | '?' | 's' | 'p' => some 1
  | 'h' | 'H' | 'e' => some 2
  | 'i' | 'I' | 'l' | 'L' | 'f' => some 4
  | 'q' | 'Q' | 'd' => some 8
  | _ => none

/-- A compiled `Struct`: `(format, repeat, item size, offset)` per code. -/
structure SFmt where
  big : Bool
  codes : List (Char × Nat × Nat × Nat)
  size : Nat
  deriving Repr, DecidableEq, Inhabited

def isCSpace (c : Char) : Bool := c == ' ' || (9 ≤ c.toNat && c.toNat ≤ 13)
def isDigit (c : Char) : Bool := 48 ≤ c.toNat && c.toNat ≤ 57

/-- The digits of a repeat count, and the text after them. -/
def spanDigits : List Char → Nat → Nat × List Char
  | c :: cs, n => if isDigit c then spanDigits cs (10 * n + (c.toNat - 48)) else (n, c :: cs)
  | [], n => (n, [])

/-- `align`, Modules/_struct.c:1600-1612. -/
def alignTo (size a : Nat) : Nat :=
  if a > 0 ∧ size > 0 then size + ((a - 1) - (size - 1) % a) else size

/-- The loop of `prepare_s`. `fuel` is the format's length. -/
def parseCodes (native : Bool) : Nat → List Char → Nat → List (Char × Nat × Nat × Nat) →
    Py (List (Char × Nat × Nat × Nat) × Nat)
  | 0, _, _, _ => .error .modelFuel
  | _ + 1, [], size, acc => .ok (acc.reverse, size)
  | fuel + 1, c :: cs, size, acc =>
    if isCSpace c then parseCodes native fuel cs size acc
    else
      let (num, c, cs, bad) :=
        if isDigit c then
          let (n, rest) := spanDigits (c :: cs) 0
          match rest with
          | [] => (n, c, [], true)
          | c' :: rest' => (n, c', rest', false)
        else (1, c, cs, false)
      if bad then .error (structError "repeat count given without format specifier")
      else
        match (if native then nativeSize c else standardSize c) with
        | none => .error (structError "bad char in struct format")
        | some itemsize =>
          let size := alignTo size (if native then itemsize else 0)
          let acc :=
            match c with
            | 'x' => acc
            | 's' | 'p' => (c, 1, num, size) :: acc
            | _ => if num = 0 then acc else (c, num, itemsize, size) :: acc
          parseCodes native fuel cs (size + num * itemsize) acc

/-- `Struct(fmt)`: `whichtable`, then `prepare_s`. -/
def structParse (fmt : List Char) : Py SFmt :=
  let (big, native, rest) :=
    match fmt with
    | '<' :: r => (false, false, r)
    | '>' :: r | '!' :: r => (true, false, r)
    | '=' :: r => (false, false, r)
    | '@' :: r => (false, true, r)
    | r => (false, true, r)
  match parseCodes native (rest.length + 1) rest 0 [] with
  | .ok (codes, size) => .ok ⟨big, codes, size⟩
  | .error e => .error e

/-- One item of format `c` from its bytes in memory order, `big` selecting the order. -/
def structItem (big : Bool) (c : Char) (bs : List Nat) : Item :=
  let n := decLE (if big then bs.reverse else bs)
  match c with
  | 'c' => .bytes bs
  | '?' => .bool (n != 0)
  | 'b' | 'h' | 'i' | 'l' | 'q' | 'n' => .int (sx bs.length n)
  | 'e' => .float (unpack2 n)
  | 'f' => .float (widen32 n)
  | 'd' => .float n
  | _ => .int n

/-- Slice `[o, o + n)` of the item. -/
def sub (bs : List Nat) (o n : Nat) : List Nat := (bs.drop o).take n

/-- `s_unpack_internal` over one code. -/
def unpackCode (big : Bool) (bs : List Nat) : Char × Nat × Nat × Nat → List Item
  | ('s', _, size, o) => [.bytes (sub bs o size)]
  | ('p', _, size, o) =>
    let n := (bs.getD o 0)
    let n := if n ≥ size then size - 1 else n
    [.bytes (sub bs (o + 1) n)]
  | (c, count, size, o) =>
    (List.range count).map fun i => structItem big c (sub bs (o + i * size) size)

/-- `Struct.unpack_from(buffer)`: the items of the tuple. -/
def structUnpackFrom (sf : SFmt) (bs : List Nat) : Py (List Item) :=
  if bs.length < sf.size then
    .error (structError s!"~unpack_from requires a buffer of at least {sf.size} bytes")
  else .ok (sf.codes.flatMap (unpackCode sf.big bs))

/-- `v == w` for two results of `struct_unpack_single`, memoryobject.c:2128-2144: a
one-item tuple is unwrapped, so an item never equals a tuple. -/
def structResultEq (v w : List Item) : Bool :=
  match v, w with
  | [a], [b] => itemEq a b
  | [_], _ | _, [_] => false
  | v, w => v.length == w.length && (v.zip w).all (fun p => itemEq p.1 p.2)

end PyLean.BytesObj.Mem
