import PyLean.DiffCore
import PyLean.Ipaddress.Model
import PyLean.Ipaddress.Exploded
import PyLean.Ipaddress.Parse4
import PyLean.Ipaddress.Hosts
import PyLean.Ipaddress.Mask4
import PyLean.Ipaddress.Parse6
import PyLean.Ipaddress.Parse6Errors

/-! Differential-testing handler for `ipaddress`. A network is `[addr, prefixlen, scope]`, the scope
id of its network address a string or `null` (and may be left out on input). -/

namespace PyLean.Ipaddress

open Lean PyLean PyLean.Diff

def encScope : Option String → Json
  | some s => toJson s
  | none => Json.null

def encNet (n : Net) : Json := Json.arr #[toJson n.addr, toJson n.prefixlen, encScope n.scope]

def getScope (v : Option Json) : Except String (Option String) :=
  match v with
  | none | some .null => pure none
  | some s => some <$> s.getStr?

def getNet (j : Json) (bits : Nat) (key : String) : Except String Net := do
  let arr ← (← j.getObjVal? key).getArr?
  let some a := arr[0]? | throw s!"{key}: missing addr"
  let some p := arr[1]? | throw s!"{key}: missing prefixlen"
  return ⟨bits, ← a.getNat?, ← p.getNat?, ← getScope arr[2]?⟩

/-- `"arg": ["int", n]`, `["bytes", [b, ...]]` or `["str", s]`. -/
def getAddrArg (j : Json) : Except String AddrArg := do
  let arg ← j.getObjVal? "arg"
  match ← (← arg.getArrVal? 0).getStr? with
  | "int" => return .int (← (← arg.getArrVal? 1).getInt?)
  | "bytes" => return .bytes ((← (← arg.getArrVal? 1).getArr?).toList.filterMap (fun x => x.getNat?.toOption))
  | _ => return .str (← (← arg.getArrVal? 1).getStr?).toList

/-- `{"k": "addr", "bits": b, "ip": n, "scope": s}`, `{"k": "net", "bits": b, "net": [a, p, s]}` or
`{"k": "other", "ty": "int"}`. -/
def getOperand (j : Json) : Except String Operand := do
  match ← getStr j "k" with
  | "addr" => return .addr (← getNat j "bits") (← getNat j "ip") (← getScope (j.getObjVal? "scope").toOption)
  | "net" => return .net (← getNet j (← getNat j "bits") "net")
  | _ => return .other (← getStr j "ty")

def run (fn : String) (j : Json) : Except String Json := do
  let bits ← (← j.getObjVal? "bits").getNat?
  match fn with
  | "exploded" =>
    let kind ← match ← getStr j "kind" with
      | "address" => pure V6Kind.address
      | "interface" => pure V6Kind.interface
      | "network" => pure V6Kind.network
      | k => throw s!"unknown kind {k}"
    let scope := (getStr j "scope").toOption.map String.toList
    return encPy (fun cs => toJson (String.ofList cs))
      (explode kind (← getNat j "ip") (← getNat j "prefixlen") scope)
  | "iface_unspecified" =>
    return encPy toJson (.ok (ifaceIsUnspecified bits (← getNat j "ip") (← getNat j "prefixlen")) : Py Bool)
  | "getattr" =>
    return encPy toJson (moduleGetattr (← getStr j "name"))
  | "summarize" =>
    let first ← getOperand (← j.getObjVal? "first")
    let last ← getOperand (← j.getObjVal? "last")
    return encPy (fun ns => Json.arr (ns.map encNet).toArray) (summarizeOp first last)
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
    return encPy toJson (containsOp n (← getOperand (← j.getObjVal? "other")))
  | "overlaps" =>
    let a ← getNet j bits "a"
    return encPy toJson (overlapsOp a (← getOperand (← j.getObjVal? "other")))
  | "subnet_of" =>
    let a ← getNet j bits "a"
    return encPy toJson (subnetOfOp a (← getOperand (← j.getObjVal? "other")))
  | "address_exclude" =>
    let a ← getNet j bits "a"
    return encPy (fun ns => Json.arr (ns.map encNet).toArray) (addressExcludeOp a (← getOperand (← j.getObjVal? "other")))
  | "hosts" =>
    let n ← getNet j bits "net"
    return encPy toJson (.ok (Json.arr #[toJson (iterList n), toJson (hostsList n), toJson n.numAddresses]) : Py Json)
  | "v6init" =>
    let a ← getAddrArg j
    let r : Py (Nat × Option (List Char) × List Char) := do
      let (ip, sc) ← ipv6Init a
      let t ← ipv6StrPy ip sc
      pure (ip, sc, t)
    return encPy (fun (ip, sc, t) => Json.arr #[toJson ip,
        match sc with | some x => toJson (String.ofList x) | none => Json.null, toJson (String.ofList t)]) r
  | "mask4" =>
    return encPy toJson (makeNetmask4 (← getStr j "s").toList)
  | "mask" =>
    -- `"arg"`: `["int", n]`, `["str", s]`, `["bytes", [b, ...]]`, `["num", n, ty]` (a number equal
    -- to the int n), `["other", ty]`, `["unhashable", key, ty, cls, msg]`; `"cache"`: the ints `_make_netmask` was
    -- called with first, in order, after the class cache was cleared.
    let arg ← j.getObjVal? "arg"
    let a ← match ← (← arg.getArrVal? 0).getStr? with
      | "int" => pure (MaskArg.int (← (← arg.getArrVal? 1).getInt?))
      | "bytes" => pure (MaskArg.bytes ((← (← arg.getArrVal? 1).getArr?).toList.filterMap
          (fun x => x.getNat?.toOption)))
      | "num" => pure (MaskArg.numEq (← (← arg.getArrVal? 1).getInt?) (← (← arg.getArrVal? 2).getStr?))
      | "other" => pure (MaskArg.other (← (← arg.getArrVal? 1).getStr?))
      | "unhashable" => do
        -- `["unhashable", key, %T name, exception class, str(exception)]`: an exact `TypeError` is
        -- `.typeError`, any other class (a `TypeError` subclass included) is `.named`.
        let cls ← (← arg.getArrVal? 3).getStr?
        let m ← (← arg.getArrVal? 4).getStr?
        pure (MaskArg.unhashable (← (← arg.getArrVal? 2).getStr?)
          (if cls = "TypeError" then .typeError m else .named cls m))
      | _ => pure (MaskArg.str (← (← arg.getArrVal? 1).getStr?).toList)
    let pre : List Int ← match j.getObjVal? "cache" with
      | .ok v => do
        let arr ← v.getArr?
        arr.toList.mapM (fun x => x.getInt?)
      | .error _ => pure []
    let cache := pre.foldl (fun c k => (makeNetmaskCached bits c (.int k)).2) []
    return encPy toJson (makeNetmaskCached bits cache a).1
  | "prefix_from_ip_int" =>
    return encPy toJson (prefixFromIpInt bits (← getNat j "n"))
  | "string_from_ip_int" =>
    let a ← match j.getObjVal? "n" with
      | .ok .null | .error _ => pure none
      | .ok v => some <$> v.getNat?
    let cls ← match (getStr j "cls").toOption with
      | some "interface" => pure V6Cls.interface
      | some "network" => pure V6Cls.network
      | _ => pure V6Cls.address
    return encPy (fun cs => toJson (String.ofList cs)) (stringFromIpInt6Py cls a)
  | "mapped_to_str" =>
    return encPy (fun cs => toJson (String.ofList cs)) (ipv4MappedToStr (← getNat j "ip"))
  | "v6_ip_int" =>
    return encPy toJson (ipIntFromString6 (← getStr j "s").toList)
  | "parse_hextet" =>
    let s := (← getStr j "s").toList
    return encPy toJson (match parseHextet s with
      | .ok v => .ok v
      | .error e => .error (.valueError ((hexMsg s e).getD "~ValueError")) : Py Nat)
  | "parse_octet" =>
    let s := (← getStr j "s").toList
    return encPy toJson (match parseOctet s with
      | .ok v => .ok v
      | .error e => .error (.valueError ((octetMsg s e).getD "~ValueError")) : Py Nat)
  | "v4init" =>
    return encPy (fun n => Json.arr #[toJson n, toJson (String.ofList (ipv4Str n))]) (ipv4Init (← getAddrArg j))
  | other => throw s!"unknown fn {other}"

def handler : Handler := fun fn j => some (run fn j)


end PyLean.Ipaddress
