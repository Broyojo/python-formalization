import PyLean.DiffCore
import PyLean.Ipaddress.Model

/-! Differential-testing handler for `ipaddress`. A network is `[addr, prefixlen]`. -/

namespace PyLean.Ipaddress

open Lean PyLean PyLean.Diff

def encNet (n : Net) : Json := Json.arr #[toJson n.addr, toJson n.prefixlen]

def getNet (j : Json) (bits : Nat) (key : String) : Except String Net := do
  let arr ← (← j.getObjVal? key).getArr?
  let some a := arr[0]? | throw s!"{key}: missing addr"
  let some p := arr[1]? | throw s!"{key}: missing prefixlen"
  return ⟨bits, ← a.getNat?, ← p.getNat?⟩

def run (fn : String) (j : Json) : Except String Json := do
  let bits ← (← j.getObjVal? "bits").getNat?
  match fn with
  | "summarize" =>
    let first ← (← j.getObjVal? "first").getNat?
    let last ← (← j.getObjVal? "last").getNat?
    return encPy (fun ns => Json.arr (ns.map encNet).toArray) (summarizeAddressRange bits first last)
  | "mknet" =>
    let a ← (← j.getObjVal? "addr").getInt?
    let p ← (← j.getObjVal? "prefixlen").getInt?
    return encPy encNet (mkNet bits a p)
  | "subnets" =>
    let n ← getNet j bits "net"
    let d ← (← j.getObjVal? "diff").getInt?
    return encPy (fun ns => Json.arr (ns.map encNet).toArray) (subnets n d (← getOptInt j "new_prefix"))
  | "supernet" =>
    let n ← getNet j bits "net"
    let d ← (← j.getObjVal? "diff").getInt?
    return encPy encNet (supernet n d (← getOptInt j "new_prefix"))
  | "getitem" =>
    let n ← getNet j bits "net"
    let i ← (← j.getObjVal? "i").getInt?
    return encPy toJson (getitem n i)
  | "contains" =>
    let n ← getNet j bits "net"
    let a ← (← j.getObjVal? "addr").getNat?
    return encPy toJson (.ok (contains n a) : Py Bool)
  | "overlaps" =>
    let a ← getNet j bits "a"
    let b ← getNet j bits "b"
    return encPy toJson (.ok (overlaps a b) : Py Bool)
  | "subnet_of" =>
    let a ← getNet j bits "a"
    let b ← getNet j bits "b"
    return encPy toJson (.ok (subnetOf a b) : Py Bool)
  | "address_exclude" =>
    let a ← getNet j bits "a"
    let b ← getNet j bits "b"
    return encPy (fun ns => Json.arr (ns.map encNet).toArray) (addressExclude a b)
  | other => throw s!"unknown fn {other}"

def handler : Handler := fun fn j => some (run fn j)


end PyLean.Ipaddress
