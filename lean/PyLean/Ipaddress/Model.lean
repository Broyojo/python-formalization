import PyLean.Core

/-!
Model of the integer core of CPython `Lib/ipaddress.py` (3.15.2): network
construction from `(int, int)`,
`summarize_address_range`, `subnets`, `supernet`, `__getitem__`,
`__contains__`, `overlaps`, `subnet_of` and `address_exclude`.

A network is modelled by its `max_prefixlen` (32 for IPv4, 128 for IPv6),
the integer value of its network address, and its prefix length. Text
is in `Parse4`, `Parse6` and `Mask4`; exception messages that embed a formatted
address start with `~` and the differential tester compares only their class.
An argument that may be of another kind is an `Operand`.
-/

namespace PyLean.Ipaddress

open PyLean

structure Net where
  /-- `max_prefixlen`: 32 for IPv4, 128 for IPv6. -/
  bits : Nat
  /-- `int(self.network_address)`. -/
  addr : Nat
  /-- `self._prefixlen`. -/
  prefixlen : Nat
  deriving Repr, DecidableEq, Inhabited

/-- `_ALL_ONES`, ipaddress.py:1143 and :1619. -/
def allOnes (bits : Nat) : Nat := 2 ^ bits - 1

/-- `_ip_int_from_prefix`, ipaddress.py:424-434. -/
def ipIntFromPrefix (bits prefixlen : Nat) : Nat :=
  allOnes bits ^^^ (allOnes bits >>> prefixlen)

/-- `int(self.netmask)`. -/
def Net.netmask (n : Net) : Nat := ipIntFromPrefix n.bits n.prefixlen

/-- `hostmask`, ipaddress.py:755-757. -/
def Net.hostmask (n : Net) : Nat := n.netmask ^^^ allOnes n.bits

/-- `broadcast_address`, ipaddress.py:750-753. -/
def Net.broadcast (n : Net) : Nat := n.addr ||| n.hostmask

/-- `num_addresses`, ipaddress.py:771-774. -/
def Net.numAddresses (n : Net) : Nat := n.broadcast - n.addr + 1

/-- `version` of the address and network classes with this `max_prefixlen`: 4 for 32, 6 for
128. The model identifies a class by its `max_prefixlen`; any other width stands for a class of
neither family, whose version the model takes to be 0. -/
def versionOf (bits : Nat) : Nat := if bits = 32 then 4 else if bits = 128 then 6 else 0

/-- `_check_int_address`, ipaddress.py:407-414. Returns the int that `__init__` stores. -/
def checkIntAddress (bits : Nat) (a : Int) : Py Nat :=
  if a < 0 then
    .error (.named "AddressValueError" s!"{a} (< 0) is not permitted as an IPv{versionOf bits} address")
  else if a > allOnes bits then
    .error (.named "AddressValueError"
      s!"{a} (>= 2**{bits}) is not permitted as an IPv{versionOf bits} address")
  else .ok a.toNat

/-- Two lowercase hex digits. -/
def hex2 (x : Nat) : String :=
  String.ofList [Nat.digitChar (x / 16 % 16), Nat.digitChar (x % 16)]

/-- `repr(b)` of a bytes object (`Objects/bytesobject.c`, `PyBytes_Repr`): single quotes unless the
bytes hold a single quote and no double quote; backslash, the chosen quote, tab, newline and carriage
return escaped, other bytes outside 32..126 as `\x` and two lowercase hex digits. -/
def bytesRepr (b : List Nat) : String :=
  let dq := b.contains 39 && !b.contains 34
  let q := if dq then "\"" else "'"
  let esc (x : Nat) : String :=
    if x = 92 then "\\\\"
    else if x = 39 ∧ dq = false then "\\'"
    else if x = 9 then "\\t" else if x = 10 then "\\n" else if x = 13 then "\\r"
    else if x < 32 ∨ 127 ≤ x then "\\x" ++ hex2 x
    else (Char.ofNat x).toString
  "b" ++ q ++ String.join (b.map esc) ++ q

/-- `_check_packed_address(address, expected_len)`, ipaddress.py:416-421. -/
def checkPackedAddress (bits expectedLen : Nat) (b : List Nat) : Py Unit :=
  if b.length ≠ expectedLen then
    .error (.named "AddressValueError"
      s!"{bytesRepr b} (len {b.length} != {expectedLen}) is not permitted as an IPv{versionOf bits} address")
  else .ok ()

/-- `IPv4Network((addr, prefixlen))` / `IPv6Network(...)` with `strict=True`
and int arguments, ipaddress.py:1499-1551 and :2298-2340, through
`_split_addr_prefix` (:526-547) and the int branch of `_make_netmask`
(:1154-1178, :1629-1647). -/
def mkNet (bits : Nat) (addr prefixlen : Int) : Py Net := do
  let a ← checkIntAddress bits addr
  if ¬(0 ≤ prefixlen ∧ prefixlen ≤ bits) then
    throw (.named "NetmaskValueError" s!"{prefixlen} is not a valid netmask")
  let p := prefixlen.toNat
  if a &&& ipIntFromPrefix bits p ≠ a then
    throw (.valueError "~has host bits set")
  return ⟨bits, a, p⟩

/-- `IPv6Address.ipv4_mapped`, ipaddress.py:2165-2176: the IPv4 address in the low 32 bits when the
high 96 are `::ffff` (:2174-2176), else `None`. -/
def ipv4Mapped (ip : Nat) : Option Nat :=
  if ip >>> 32 = 0xFFFF then some (ip &&& 0xFFFFFFFF) else none

/-- `_count_righthand_zero_bits`, ipaddress.py:181-194. -/
def countRighthandZeroBits (number bits : Nat) : Nat :=
  if number = 0 then bits
  else min bits (bitLength (notAnd number (number - 1)))

/-- The `while` loop of `summarize_address_range`, ipaddress.py:242-249.
`fuel` bounds the iteration count; the caller passes the range length plus one,
which suffices because each iteration advances `first` by at least one and
the extra unit pays for the final `first > last` test. -/
def summarizeLoop (bits last : Nat) : Nat → Nat → Py (List Net)
  | 0, _ => .error .modelFuel
  | fuel + 1, first =>
    if first ≤ last then do
      let nbits := min (countRighthandZeroBits first bits) (bitLength (last - first + 1) - 1)
      let net ← mkNet bits first (bits - nbits : Nat)
      let first' := first + (1 <<< nbits)
      if first' - 1 = allOnes bits then return [net]
      let rest ← summarizeLoop bits last fuel first'
      return net :: rest
    else .ok []

/-- `list(summarize_address_range(first, last))` from the comparison on, for two addresses of the
same version with `max_prefixlen` `bits`, ipaddress.py:229-249: `first > last` compares `_ip`
(`_BaseAddress.__lt__`, :576-584, through `functools.total_ordering`), then the version picks the
network class (:232-237). -/
def summarizeAddressRange (bits first last : Nat) : Py (List Net) :=
  if first > last then .error (.valueError "last IP address must be greater than first")
  else if versionOf bits ≠ 4 ∧ versionOf bits ≠ 6 then .error (.valueError "unknown IP version")
  else summarizeLoop bits last (last - first + 2) first

/-- An argument where an address or network is expected. -/
inductive Operand where
  /-- An `IPv4Address` or `IPv6Address` with `max_prefixlen` `bits` and `_ip` `ip`. -/
  | addr (bits : Nat) (ip : Nat)
  /-- An `IPv4Network` or `IPv6Network`. -/
  | net (n : Net)
  /-- An object of type `tyName` with no `version` attribute that supports neither `in` nor
  iteration, such as an int or `None`. -/
  | other (tyName : String)
  deriving Repr, DecidableEq

/-- `list(summarize_address_range(first, last))`, ipaddress.py:197-249: the `isinstance` check
(:223-225) and the version check (:226-228) come first. -/
def summarizeOp (first last : Operand) : Py (List Net) :=
  match first, last with
  | .addr b1 x, .addr b2 y =>
    if versionOf b1 ≠ versionOf b2 then .error (.typeError "~are not of the same version")
    else summarizeAddressRange b1 x y
  | _, _ => .error (.typeError "first and last must be IP addresses, not networks")

/-- `list(range(start, stop, step))` for `step > 0`. -/
def pyRange (start stop step : Nat) : List Nat :=
  go (stop - start) start
where
  go : Nat → Nat → List Nat
    | 0, _ => []
    | fuel + 1, x => if x < stop then x :: go fuel (x + step) else []

/-- `list(self.subnets(prefixlen_diff, new_prefix))`, ipaddress.py:921-972. -/
def subnets (n : Net) (prefixlenDiff : Int) (newPrefix : Option Int) : Py (List Net) := do
  if n.prefixlen = n.bits then return [n]
  let mut diff := prefixlenDiff
  if let some np := newPrefix then
    if np < n.prefixlen then throw (.valueError "new prefix must be longer")
    if prefixlenDiff ≠ 1 then throw (.valueError "cannot set prefixlen_diff and new_prefix")
    diff := np - n.prefixlen
  if diff < 0 then throw (.valueError "prefix length diff must be > 0")
  let newPrefixlen : Int := n.prefixlen + diff
  if newPrefixlen > n.bits then
    throw (.valueError "~prefix length diff is invalid for netblock")
  let step := (n.hostmask + 1) >>> diff.toNat
  (pyRange n.addr (n.broadcast + 1) step).mapM (fun (a : Nat) => mkNet n.bits a newPrefixlen)

/-- `self.supernet(prefixlen_diff, new_prefix)`, ipaddress.py:974-1013.
`int(self.netmask) << prefixlen_diff` raises for a negative shift count. -/
def supernet (n : Net) (prefixlenDiff : Int) (newPrefix : Option Int) : Py Net := do
  if n.prefixlen = 0 then return n
  let mut diff := prefixlenDiff
  if let some np := newPrefix then
    if np > n.prefixlen then throw (.valueError "new prefix must be shorter")
    if prefixlenDiff ≠ 1 then throw (.valueError "cannot set prefixlen_diff and new_prefix")
    diff := n.prefixlen - np
  let newPrefixlen : Int := n.prefixlen - diff
  if newPrefixlen < 0 then
    throw (.valueError s!"current prefixlen is {n.prefixlen}, cannot have a prefixlen_diff of {diff}")
  if diff < 0 then throw (.valueError "negative shift count")
  mkNet n.bits (n.addr &&& (n.netmask <<< diff.toNat)) newPrefixlen

/-- `int(self[i])`, ipaddress.py:695-706. -/
def getitem (n : Net) (i : Int) : Py Nat :=
  let network : Int := n.addr
  let broadcast : Int := n.broadcast
  if 0 ≤ i then
    if network + i > broadcast then .error (.indexError "address out of range")
    else .ok (network + i).toNat
  else
    let i := i + 1
    if broadcast + i < network then .error (.indexError "address out of range")
    else .ok (broadcast + i).toNat

/-- `other._ip & self.netmask._ip == self.network_address._ip`, ipaddress.py:741. -/
def contains (n : Net) (a : Nat) : Bool := a &&& n.netmask == n.addr

/-- `other in self`, `_BaseNetwork.__contains__`, ipaddress.py:731-741: a version mismatch is
`False` (:733-734), a network is `False` (:736-737), an address is tested against the mask
(:741). `other.version` raises `AttributeError` for an object without it. -/
def containsOp (n : Net) : Operand → Py Bool
  | .other ty => .error (.named "AttributeError" s!"'{ty}' object has no attribute 'version'")
  | .addr b x => if versionOf n.bits ≠ versionOf b then .ok false else .ok (contains n x)
  | .net m => if versionOf n.bits ≠ versionOf m.bits then .ok false else .ok false

/-- `x in c` for an address `x`: a network's `__contains__`; an address or another object has
neither `__contains__` nor `__iter__`, and `in` raises `TypeError`. -/
def inOp (x : Operand) : Operand → Py Bool
  | .net m => containsOp m x
  | .addr b _ => .error (.typeError s!"argument of type 'IPv{versionOf b}Address' is not a container or iterable")
  | .other ty => .error (.typeError s!"argument of type '{ty}' is not a container or iterable")

/-- `self.overlaps(other)`, ipaddress.py:743-748: four `in` tests joined by `or`. For an `other`
that is not a network the first `in` raises, so `other.network_address` is reached only for a
network. -/
def overlapsOp (s : Net) (o : Operand) : Py Bool := do
  if ← inOp (.addr s.bits s.addr) o then return true
  if ← inOp (.addr s.bits s.broadcast) o then return true
  match o with
  | .net m =>
    if ← containsOp s (.addr m.bits m.addr) then return true
    containsOp s (.addr m.bits m.broadcast)
  | _ => .error (.named "AttributeError" "~object has no attribute 'network_address'")

/-- `b.network_address <= a.network_address and b.broadcast_address >= a.broadcast_address`,
ipaddress.py:1033-1034, for networks of the same version. -/
def subnetOf (a b : Net) : Bool := b.addr ≤ a.addr && b.broadcast ≥ a.broadcast

/-- `_BaseNetwork._is_subnet_of(a, b)` for a network `a`, ipaddress.py:1028-1037: `b.version`
(an `AttributeError` for an object without it) and the version check (:1031-1032) come first;
`b.network_address` on an address raises `AttributeError`; both `AttributeError`s become
`TypeError` (:1035-1037). -/
def isSubnetOf (a : Net) (b : Operand) : Py Bool :=
  match b with
  | .other _ => .error (.typeError "~Unable to test subnet containment between")
  | .addr bb _ =>
    if versionOf a.bits ≠ versionOf bb then .error (.typeError "~are not of the same version")
    else .error (.typeError "~Unable to test subnet containment between")
  | .net m =>
    if versionOf a.bits ≠ versionOf m.bits then .error (.typeError "~are not of the same version")
    else .ok (subnetOf a m)

/-- `self.subnet_of(other)`, ipaddress.py:1039-1041. -/
def subnetOfOp (s : Net) (o : Operand) : Py Bool := isSubnetOf s o

/-- `s1, s2 = net.subnets()`; unpacking raises when there is one subnet. -/
def halves (n : Net) : Py (Net × Net) := do
  match ← subnets n 1 none with
  | [a, b] => return (a, b)
  | [_] => throw (.valueError "not enough values to unpack (expected 2, got 1)")
  | _ => throw (.valueError "~too many values to unpack")

/-- The `while` loop and tail of `address_exclude`, ipaddress.py:841-861. -/
def excludeLoop (other : Net) : Nat → Net → Net → Py (List Net)
  | 0, _, _ => .error .modelFuel
  | fuel + 1, s1, s2 =>
    if s1 ≠ other ∧ s2 ≠ other then
      if subnetOf other s1 then do
        let (a, b) ← halves s1
        return s2 :: (← excludeLoop other fuel a b)
      else if subnetOf other s2 then do
        let (a, b) ← halves s2
        return s1 :: (← excludeLoop other fuel a b)
      else .error (.assertionError "~Error performing exclusion")
    else if s1 = other then .ok [s2]
    else if s2 = other then .ok [s1]
    else .error (.assertionError "~Error performing exclusion")

/-- `list(self.address_exclude(other))` for two networks of the same version,
ipaddress.py:831-861. `other.subnet_of(self)` (:831) is `subnetOf other s` for networks of one
version. Re-creating `other` from its network address and prefix length (:837-838) is the
identity on `Net`. -/
def addressExclude (s other : Net) : Py (List Net) := do
  if ¬subnetOf other s then throw (.valueError "~not contained in")
  if other = s then return []
  let (s1, s2) ← halves s
  excludeLoop other (s.bits + 1) s1 s2

/-- `list(self.address_exclude(other))`, ipaddress.py:788-861: `other.version` (an
`AttributeError` for an object without it) and the version check (:824-826), then the network
check (:828-829). -/
def addressExcludeOp (s : Net) (o : Operand) : Py (List Net) :=
  match o with
  | .other ty => .error (.named "AttributeError" s!"'{ty}' object has no attribute 'version'")
  | .addr b _ =>
    if versionOf s.bits ≠ versionOf b then .error (.typeError "~are not of the same version")
    else .error (.typeError "~is not a network object")
  | .net m =>
    if versionOf s.bits ≠ versionOf m.bits then .error (.typeError "~are not of the same version")
    else addressExclude s m

end PyLean.Ipaddress
