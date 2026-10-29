import Lean.Data.Json
import PyLean

/-!
Differential-testing driver. Reads one JSON case per line on stdin:
`{"fn": "<name>", ...args}` and writes one JSON result per line:
`{"ok": <value>}` or `{"exc": "<class>", "msg": "<message>"}`.
A network is encoded as `[addr, prefixlen]`.
-/

open Lean PyLean PyLean.Ipaddress

def encNet (n : Net) : Json := Json.arr #[toJson n.addr, toJson n.prefixlen]

def encPy {α : Type} (enc : α → Json) : Py α → Json
  | .ok v => Json.mkObj [("ok", enc v)]
  | .error e => Json.mkObj [("exc", toJson e.className), ("msg", toJson e.message)]

def getNet (j : Json) (bits : Nat) (key : String) : Except String Net := do
  let arr ← (← j.getObjVal? key).getArr?
  let some a := arr[0]? | throw s!"{key}: missing addr"
  let some p := arr[1]? | throw s!"{key}: missing prefixlen"
  return ⟨bits, ← a.getNat?, ← p.getNat?⟩

def getOptInt (j : Json) (key : String) : Except String (Option Int) :=
  match j.getObjVal? key with
  | .ok .null | .error _ => .ok none
  | .ok v => some <$> v.getInt?

def runCase (j : Json) : Except String Json := do
  let fn ← (← j.getObjVal? "fn").getStr?
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

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let out := match Json.parse line.trimAscii.toString >>= runCase with
    | .ok r => r
    | .error e => Json.mkObj [("harness_error", toJson e)]
  stdout.putStrLn out.compress
  stdout.flush
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
