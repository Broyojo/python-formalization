import PyLean.DiffCore
import PyLean.LongObj.Pylong

/-!
Differential-testing cases for the int/str conversions and `_pylong`. Ints travel
as hex strings (`"-0x..."`), since Python's `json` cannot print them past the
string conversion limit; strings travel as lists of code points, so that NUL bytes
and lone surrogates survive.
-/

namespace PyLean.LongObj

open Lean PyLean PyLean.Diff

def decHexDigit (c : Char) : Except String Nat :=
  if '0' ≤ c ∧ c ≤ '9' then .ok (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
  else .error s!"bad hex digit {c}"

def decHexInt (s : String) : Except String Int := do
  let (neg, body) := match s.toList with
    | '-' :: r => (true, r)
    | r => (false, r)
  let v ← (body.drop 2).foldlM (fun acc c => do return acc * 16 + (← decHexDigit c)) 0
  return if neg then -(v : Int) else v

def encHexInt (i : Int) : Json :=
  toJson (String.ofList
    ((if i < 0 then ['-'] else []) ++ ['0', 'x'] ++ Nat.toDigits 16 i.natAbs))

def encNat (n : Nat) : Json := encHexInt n

def encChars (s : List Char) : Json := toJson (String.ofList s)

def getHex (j : Json) (key : String) : Except String Int := do decHexInt (← getStr j key)
def getHexNat (j : Json) (key : String) : Except String Nat := do return (← getHex j key).toNat

def getNats (j : Json) (key : String) : Except String (List Nat) := do
  let a ← (← field j key).getArr?
  return (← a.toList.mapM (fun x => x.getNat?))

def getHexes (j : Json) (key : String) : Except String (List Nat) := do
  let a ← (← field j key).getArr?
  let l ← a.toList.mapM (fun x => do decHexInt (← x.getStr?))
  return l.map Int.toNat

def encLong (x : Long) : Json := encHexInt x.toInt

/-- The items of a `compute_powers` result, sorted by key as the tester sends them. -/
def encDict (d : PowDict Nat) : Json :=
  let items := d.toArray.qsort (fun a b => a.1 < b.1)
  Json.arr (items.map (fun kv => Json.arr #[toJson kv.1, encNat kv.2]))

/-- `long_format` output: `pend` is the number of bytes consumed, or `null`. -/
def encCStr (orig : List Nat) (r : Py Long × Option (List Nat)) : Json :=
  let pend : Json := match r.2 with
    | some p => toJson (orig.length - p.length)
    | none => Json.null
  Json.mkObj [("ok", Json.arr #[encPy encLong r.1, pend])]

def runStr (fn : String) (j : Json) : Option (Except String Json) :=
  let lim := fun (_ : Unit) => getNat j "lim"
  match fn with
  | "str" => some do
    return encPy encChars (longToDecimalString (← lim ()) (Long.ofInt (← getHex j "v")))
  | "fmtbin" => some do
    return encPy encChars (longFormatBinary (Long.ofInt (← getHex j "v")) (← getNat j "base")
      (← getBool j "alt"))
  | "fmt" => some do
    return encPy encChars (pyLongFormat (← lim ()) (Long.ofInt (← getHex j "v")) (← getNat j "base"))
  | "fmtw" => some do
    return encPy encChars (pyLongFormatW (← lim ()) (Long.ofInt (← getHex j "v"))
      (← getNat j "base") (← getBool j "alt"))
  | "intstr" => some do
    return encPy encLong (intOfStr (← lim ()) (← getNats j "u") (← getInt j "base"))
  | "intbytes" => some do
    return encPy encLong (intOfBytes (← lim ()) (← getNats j "u") (← getInt j "base"))
  | "intcstr" => some do
    let u ← getNats j "u"
    return encCStr u (intOfCStr (← lim ()) u (← getInt j "base"))
  | "cp" => some do
    return encPy encDict (computePowersNat (← getNat j "w") (← getNat j "b") (← getNat j "more")
      (← getBool j "hi"))
  | "consumer" => some do
    let w ← getNat j "w"
    let r := consumerInner (← getNat j "more") (← getBool j "hi") (2 * w + 2) w ([], [])
    return Json.mkObj [("ok", Json.arr ((r.2.toArray.qsort (· < ·)).map toJson))]
  | "itd" => some do
    return encPy encHexInt (intToDecimal (← getHex j "v"))
  | "itds" => some do
    let l ← lim ()
    return encPy encChars
      (intToDecimalString (fun n => longStrF 2 l (Long.ofInt n)) (← getHex j "v"))
  | "sti" => some do
    return encPy encHexInt (strToIntInner (pylongLeaf 2 (← lim ())) (← getNats j "u"))
  | "dsi" => some do
    let l ← lim ()
    return encPy encNat
      (decStrToIntInner (decLeafOf (pylongLeaf 2 l)) (← getNats j "u") (← getNat j "guard"))
  | "ifs" => some do
    let l ← lim ()
    let leaf := pylongLeaf 2 l
    return encPy encHexInt (intFromString leaf (decLeafOf leaf) (← getNats j "u"))
  | "s2i" => some do
    let l ← lim ()
    let leaf := pylongLeaf 2 l
    return encPy encHexInt (strToInt leaf (decLeafOf leaf) (← getNats j "u"))
  | "div2" => some do
    let n ← getNat j "n"
    return encPy (fun p => Json.arr #[encNat p.1, encNat p.2])
      (div2n1n (2 * n + 2) (← getHexNat j "a") (← getHexNat j "b") n)
  | "div3" => some do
    let n ← getNat j "n"
    return encPy (fun p => Json.arr #[encNat p.1, encNat p.2])
      (div3n2n (2 * n + 2) (← getHexNat j "a12") (← getHexNat j "a3") (← getHexNat j "b")
        (← getHexNat j "b1") (← getHexNat j "b2") n)
  | "i2d" => some do
    return encPy (fun l => Json.arr (l.toArray.map encNat))
      (int2digits (← getHexNat j "a") (← getNat j "n"))
  | "d2i" => some do
    return encPy encNat (digits2int (← getHexes j "digits") (← getNat j "n"))
  | "dmp" => some do
    return encPy (fun p => Json.arr #[encNat p.1, encNat p.2])
      (divmodPos (← getHexNat j "a") (← getHexNat j "b"))
  | _ => none

end PyLean.LongObj
