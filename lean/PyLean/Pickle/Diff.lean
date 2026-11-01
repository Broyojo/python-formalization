import PyLean.DiffCore
import PyLean.Pickle.Enc
import PyLean.Pickle.DecC
import PyLean.Pickle.Tools

/-!
Differential-testing handler for `pickle` cases (`"mod": "pickle"`).

* `dumps`: `{"impl": "c"|"py", "proto": p, "val": V}` returns the pickle as a
  list of byte values.
* `loads`: `{"impl": "c"|"py", "data": [bytes]}` returns the decoded object.
* `roundtrip`: `{"enc": .., "dec": .., "proto": p, "val": V}` returns
  `loads(dumps(val, p))`.

`V` encodes a `PV`: `{"t": kind, "o": oid, "v": payload}` with `oid` one of
`{"u": n}`, `{"s1": c}`, `{"b1": b}`. Decoded objects come back as
`{"t": kind, "v": payload}`; set and frozenset elements are sorted by their
compact JSON text, and a container reached again on the current path is
`{"t": "rec", "v": depth}` (`difftest/pickle_diff.py` does the same).

`pickletools` cases take `{"data": [bytes]}` and `tell`, false for a file
without `tell`:

* `genops` returns `[name, arg, pos, end_pos]` for each opcode.
* `optimize` returns the optimized pickle.
* `dis` also takes `indent`, `annotate` and `memo`, pairs of key and stack
  object name. It returns the printed text, or the exception with that text
  and a NUL before the message.
-/

namespace PyLean.Pickle

open Lean PyLean PyLean.Diff

/-- Python's `hex(i)`: ints travel as hex text, which has no digit limit. -/
def hexInt (i : Int) : String :=
  let rec digits (n : Nat) (acc : List Char) (fuel : Nat) : List Char :=
    match fuel with
    | 0 => acc
    | f + 1 => if n < 16 then Char.ofNat (hexDigit n).toNat :: acc
               else digits (n / 16) (Char.ofNat (hexDigit (n % 16)).toNat :: acc) f
  (if i < 0 then "-0x" else "0x") ++ String.ofList (digits i.natAbs [] (i.natAbs.log2 + 2))

def parseHexInt (s : String) : Except String Int := do
  let (neg, r) := if s.startsWith "-" then (true, (s.drop 1).toString) else (false, s)
  unless r.startsWith "0x" do throw s!"bad hex {s}"
  let ds := (r.drop 2).toString.toList
  let v ← ds.foldlM (fun (a : Nat) c => do
    let d ← match hexVal c.toNat.toUInt8 with
      | some d => pure d
      | none => throw s!"bad hex {s}"
    return a * 16 + d) 0
  return if neg then -(v : Int) else v

def getOid (j : Json) : Except String Oid := do
  match j.getObjVal? "u", j.getObjVal? "s1", j.getObjVal? "b1" with
  | .ok n, _, _ => return .u (← n.getNat?)
  | _, .ok c, _ => return .str1 (← c.getNat?)
  | _, _, .ok b => return .bytes1 (← b.getNat?)
  | _, _, _ => throw "bad oid"

def getBytesArr (j : Json) : Except String Bytes := do
  let arr ← j.getArr?
  arr.toList.mapM fun x => do return (← x.getNat?).toUInt8

def getNats (j : Json) : Except String (List Nat) := do
  let arr ← j.getArr?
  arr.toList.mapM (·.getNat?)

partial def getPV (j : Json) : Except String PV := do
  let t ← getStr j "t"
  match t with
  | "none" => return .none
  | "bool" => return .bool (← getBool j "v")
  | "int" => return .int (← parseHexInt (← getStr j "v"))
  | _ =>
    let o ← getOid (← field j "o")
    let v ← field j "v"
    match t with
    | "str" => return .str o (← getNats v)
    | "bytes" => return .bytes o (← getBytesArr v)
    | "bytearray" => return .bytearray o (← getBytesArr v)
    | "tuple" => return .tuple o (← (← v.getArr?).toList.mapM getPV)
    | "list" => return .list o (← (← v.getArr?).toList.mapM getPV)
    | "set" => return .set o (← (← v.getArr?).toList.mapM getPV)
    | "frozenset" => return .frozenset o (← (← v.getArr?).toList.mapM getPV)
    | "dict" => return .dict o (← (← v.getArr?).toList.mapM fun p => do
        let a ← p.getArr?
        match a.toList with
        | [k, x] => return (← getPV k, ← getPV x)
        | _ => throw "bad dict item")
    | _ => throw s!"bad kind {t}"

def mk (t : String) (v : Json) : Json := Json.mkObj [("t", toJson t), ("v", v)]

def sortJson (xs : List Json) : List Json :=
  (xs.map fun x => (x.compress, x)).mergeSort (fun a b => decide (a.1 ≤ b.1)) |>.map (·.2)

def bytesJson (b : Bytes) : Json := toJson (b.map (·.toNat))

/-- The decoded object as JSON; `path` holds the heap addresses being visited. -/
def dvJson (h : Heap) : Nat → List Nat → DV → Json
  | 0, _, _ => mk "fuel" Json.null
  | _ + 1, _, .none => mk "none" Json.null
  | _ + 1, _, .bool b => mk "bool" (toJson b)
  | _ + 1, _, .int i => mk "int" (toJson (hexInt i))
  | _ + 1, _, .str s => mk "str" (toJson s)
  | _ + 1, _, .bytes b => mk "bytes" (bytesJson b)
  | _ + 1, _, .glob g => mk "glob" (toJson g.name)
  | f + 1, p, .tuple xs => mk "tuple" (Json.arr (xs.map (dvJson h f p)).toArray)
  | f + 1, p, .frozenset xs => mk "frozenset" (Json.arr (sortJson (xs.map (dvJson h f p))).toArray)
  | f + 1, p, .ref a =>
    match p.idxOf? a with
    | some i => mk "rec" (toJson (p.length - 1 - i))
    | none =>
      let p' := a :: p
      match h.get a with
      | .list xs => mk "list" (Json.arr (xs.map (dvJson h f p')).toArray)
      | .set xs => mk "set" (Json.arr (sortJson (xs.map (dvJson h f p'))).toArray)
      | .bytearray b => mk "bytearray" (bytesJson b)
      | .dict kvs => mk "dict" (Json.arr (kvs.map fun (k, v) =>
          Json.arr #[dvJson h f p' k, dvJson h f p' v]).toArray)

def loadsJson (r : Py (DV × Heap)) : Json :=
  encPy (fun (v, h) => dvJson h 100000 [] v) r

def tvJson : Option TV → Json
  | none => Json.null
  | some (.int i) => mk "int" (toJson (hexInt i))
  | some (.bool b) => mk "bool" (toJson b)
  | some (.bytes b) => mk "bytes" (bytesJson b)
  | some (.bytearray b) => mk "bytearray" (bytesJson b)
  | some (.str s) => mk "str" (toJson s)
  | some (.float b) => mk "float" (bytesJson b)

def genopJson (op : GenOp) : Json :=
  Json.arr #[toJson op.info.name, tvJson op.arg, toJson op.pos, toJson op.endPos]

/-- A `dis` outcome. A `~` message is not rendered, so its text is not compared. -/
def disJson : String × Option PyExc → Json
  | (out, none) => Json.mkObj [("ok", toJson out)]
  | (out, some e) =>
    if e.message.startsWith "~" then encPy (α := String) toJson (.error e)
    else Json.mkObj [("exc", toJson e.className), ("msg", toJson (out ++ "\x00" ++ e.message))]

/-- The `memo` dict of a `dis` case: a repeated key keeps the last value. -/
def getMemoPairs (j : Json) : Except String (List (Int × String)) := do
  let ps ← (← j.getArr?).toList.mapM fun p => do
    match (← p.getArr?).toList with
    | [k, n] => return ((← k.getInt?), (← n.getStr?))
    | _ => throw "bad memo pair"
  return ps.foldl (fun m kv => memoStore m kv.1 kv.2) []

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "genops" =>
    let d ← getBytesArr (← field j "data")
    let tell ← getBool j "tell"
    return encPy (fun ops => Json.arr (ops.map genopJson).toArray) (genops tell d)
  | "optimize" =>
    return encPy bytesJson (optimize (← getBytesArr (← field j "data")))
  | "dis" =>
    let d ← getBytesArr (← field j "data")
    let tell ← getBool j "tell"
    let memo ← getMemoPairs (← field j "memo")
    return disJson (dis tell d memo (← getNat j "indent") (← getNat j "annotate"))
  | "dumps" =>
    let isC := (← getStr j "impl") == "c"
    let x ← getPV (← field j "val")
    let p ← getInt j "proto"
    return encPy bytesJson (if isC then cDumps x p else pyDumps x p)
  | "loads" =>
    let isC := (← getStr j "impl") == "c"
    let d ← getBytesArr (← field j "data")
    return loadsJson (if isC then cLoads d else pyLoads d)
  | "roundtrip" =>
    let encC := (← getStr j "enc") == "c"
    let decC := (← getStr j "dec") == "c"
    let x ← getPV (← field j "val")
    let p ← getInt j "proto"
    let r : Py (DV × Heap) := do
      let b ← if encC then cDumps x p else pyDumps x p
      if decC then cLoads b else pyLoads b
    return loadsJson r
  | _ => throw s!"unknown fn {fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.Pickle
