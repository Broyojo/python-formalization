import PyLean.Core

/-!
Model of the integer core of CPython `Lib/ipaddress.py` (3.15.2): network
construction from `(int, int)`,
`summarize_address_range`, `subnets`, `supernet`, `__getitem__`,
`__contains__`, `overlaps`, `subnet_of` and `address_exclude`.

A network is modelled by its `max_prefixlen` (32 for IPv4, 128 for IPv6),
the integer value of its network address, its prefix length, and the scope id of its network
address (`IPv6Address._scope_id`, which `IPv6Address.__eq__` compares, :2010-2016). Text
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
  /-- `self.network_address._scope_id`: `None` (`none`) or the text after `%`. Only an IPv6
  network built from a string or an address with a scope id has one; every network `__init__`
  builds from an int (`subnets`, `supernet`, `summarize_address_range`, a non-strict network with
  host bits, :2338-2339) has none. IPv4 addresses have no `_scope_id`, and the IPv4 comparisons
  below never read this field. -/
  scope : Option String
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
(:1154-1178, :1629-1647). `IPv6Address(int)` stores no scope id (:1939-1943). -/
def mkNet (bits : Nat) (addr prefixlen : Int) : Py Net := do
  let a ← checkIntAddress bits addr
  if ¬(0 ≤ prefixlen ∧ prefixlen ≤ bits) then
    throw (.named "NetmaskValueError" s!"{prefixlen} is not a valid netmask")
  let p := prefixlen.toNat
  if a &&& ipIntFromPrefix bits p ≠ a then
    throw (.valueError "~has host bits set")
  return ⟨bits, a, p, none⟩

/-- `IPv6Address.ipv4_mapped`, ipaddress.py:2165-2176: the IPv4 address in the low 32 bits when the
high 96 are `::ffff` (:2174-2176), else `None`. -/
def ipv4Mapped (ip : Nat) : Option Nat :=
  if ip >>> 32 = 0xFFFF then some (ip &&& 0xFFFFFFFF) else none

/-! ## Address comparisons

`_BaseAddress` defines `__eq__` (:569-574) and `__lt__` (:576-584) and is decorated with
`functools.total_ordering` (:555), which derives `<=`, `>` and `>=` from `__lt__` and `==`
(Lib/functools.py:89-108). `IPv6Address` overrides `__eq__` to compare `_scope_id` too
(:2009-2015) and keeps the inherited `__lt__`, which compares `_ip` only. The functions below take
two addresses of one version, given by `max_prefixlen` `bits`, `_ip` and `_scope_id`. -/

/-- `self < other`, `_BaseAddress.__lt__`, ipaddress.py:576-584, after its type and version
checks (:577-581): `_ip` only (:582-584). -/
def addrLt (x y : Nat) : Bool := if x ≠ y then decide (x < y) else false

/-- `self == other`: `_BaseAddress.__eq__` (:569-574) compares `_ip` (and the version, equal
here); for IPv6, `IPv6Address.__eq__` (:2009-2015) returns `False` when that does (:2013-2014) and
otherwise compares `self._scope_id == getattr(other, '_scope_id', None)` (:2015). -/
def addrEq (bits x : Nat) (sx : Option String) (y : Nat) (sy : Option String) : Bool :=
  let addressEqual := x == y
  if !addressEqual then false
  else if versionOf bits = 6 then sx == sy
  else true

/-- `self <= other`, `total_ordering`'s `_le_from_lt` (Lib/functools.py:96-101):
`op_result or self == other`. -/
def addrLe (bits x : Nat) (sx : Option String) (y : Nat) (sy : Option String) : Bool :=
  addrLt x y || addrEq bits x sx y sy

/-- `self > other`, `_gt_from_lt` (Lib/functools.py:89-94): `not op_result and self != other`. -/
def addrGt (bits x : Nat) (sx : Option String) (y : Nat) (sy : Option String) : Bool :=
  !addrLt x y && !addrEq bits x sx y sy

/-- `self >= other`, `_ge_from_lt` (Lib/functools.py:103-108): `not op_result`. -/
def addrGe (x y : Nat) : Bool := !addrLt x y

/-- `self == other` for two networks, `_BaseNetwork.__eq__`, ipaddress.py:720-726: the version,
the network addresses (whose `IPv6Address.__eq__` compares the scope ids) and `int(netmask)`. -/
def netEq (a b : Net) : Bool :=
  versionOf a.bits == versionOf b.bits && addrEq a.bits a.addr a.scope b.addr b.scope &&
    a.netmask == b.netmask

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
same version with `max_prefixlen` `bits`, `_ip` `first` and `last` and scope ids `sf` and `sl`,
ipaddress.py:229-249: `first > last` (:229) is `total_ordering`'s `not first < last and
first != last` (`addrGt`), then the version picks the network class (:232-237), and the loop reads
only `_ip` (:240-241). -/
def summarizeAddressRange (bits first : Nat) (sf : Option String) (last : Nat)
    (sl : Option String) : Py (List Net) :=
  if addrGt bits first sf last sl then .error (.valueError "last IP address must be greater than first")
  else if versionOf bits ≠ 4 ∧ versionOf bits ≠ 6 then .error (.valueError "unknown IP version")
  else summarizeLoop bits last (last - first + 2) first

/-- `summarize_address_range` after `first > last` (:229) let the arguments through: the version
picks the network class (:232-237) and the loop runs on `first._ip` and `last._ip` (:239-249). -/
def summarizeInts (bits first last : Nat) : Py (List Net) :=
  if versionOf bits ≠ 4 ∧ versionOf bits ≠ 6 then .error (.valueError "unknown IP version")
  else summarizeLoop bits last (last - first + 2) first

/-- `self < other` for two networks of one version, `_BaseNetwork.__lt__`, ipaddress.py:708-718,
after its type and version checks (:709-713): `network_address != other.network_address` is
`not ==` (`IPv6Address.__eq__` compares the scope ids, :2009-2015), and then `<` on the network
addresses (`_ip` only, :576-584); otherwise the netmasks, which are built from ints and so have no
scope id (:714-717). -/
def netLt (a b : Net) : Bool :=
  if !addrEq a.bits a.addr a.scope b.addr b.scope then addrLt a.addr b.addr
  else if a.netmask ≠ b.netmask then decide (a.netmask < b.netmask)
  else false

/-- `self.network` of an interface with `max_prefixlen` `bits`, `_ip` `ip`, scope id `scope` and
prefix length `p`: `IPv4Interface.__init__` (:1415-1421) and `IPv6Interface.__init__`
(:2209-2215) build it as `IPvXNetwork((addr, mask), strict=False)`, whose `network_address` is
`IPvXAddress(addr)`, scope id included, unless host bits are set, when it is rebuilt from the masked
int with no scope id (:1541-1548, :2331-2339). -/
def ifaceNet (bits ip : Nat) (scope : Option String) (p : Nat) : Net :=
  let a := ip &&& ipIntFromPrefix bits p
  ⟨bits, a, p, if a = ip then scope else none⟩

/-- An argument where an address or network is expected. -/
inductive Operand where
  /-- An `IPv4Address` or `IPv6Address` with `max_prefixlen` `bits`, `_ip` `ip` and (IPv6)
  `_scope_id` `scope`. -/
  | addr (bits : Nat) (ip : Nat) (scope : Option String)
  /-- An `IPv4Interface` or `IPv6Interface` (a subclass of the address class, :1413, :2207) with
  `max_prefixlen` `bits`, `_ip` `ip`, (IPv6) `_scope_id` `scope` and prefix length `prefixlen`; its
  `network` is `ifaceNet bits ip scope prefixlen`. It overrides `__eq__` and `__lt__`
  (:1431-1453, :2225-2247), has `network` but no `network_address`, and no `__contains__`. -/
  | iface (bits : Nat) (ip : Nat) (scope : Option String) (prefixlen : Nat)
  /-- An `IPv4Network` or `IPv6Network`. -/
  | net (n : Net)
  /-- An object of type `tyName` with no `version` attribute that supports neither `in` nor
  iteration, such as an int or `None`. -/
  | other (tyName : String)
  deriving Repr, DecidableEq

/-- `max_prefixlen` of an operand with a `version` (0 for `other`, which has none). -/
@[simp] def Operand.bits : Operand → Nat
  | .addr b _ _ | .iface b _ _ _ => b
  | .net n => n.bits
  | .other _ => 0

/-- The operand has no `version` attribute. -/
@[simp] def Operand.isOther : Operand → Bool
  | .other _ => true
  | .addr _ _ _ | .iface _ _ _ _ | .net _ => false

/-- The network, for an operand that has `network_address` and `broadcast_address`. -/
@[simp] def Operand.asNet : Operand → Option Net
  | .net n => some n
  | .addr _ _ _ | .iface _ _ _ _ | .other _ => none

/-- `self < other` for two interfaces of one version, `IPv4Interface.__lt__` (:1443-1453) and
`IPv6Interface.__lt__` (:2237-2247): `address_less` is the address comparison (`_ip` only), then
`self.network < other.network or self.network == other.network and address_less`. -/
def ifaceLt (bits x : Nat) (sx : Option String) (px y : Nat) (sy : Option String) (py : Nat) : Bool :=
  let n1 := ifaceNet bits x sx px
  let n2 := ifaceNet bits y sy py
  netLt n1 n2 || (netEq n1 n2 && addrLt x y)

/-- `self == other` for two interfaces of one version, `IPv4Interface.__eq__` (:1431-1441) and
`IPv6Interface.__eq__` (:2225-2235): the address equality (`_ip`, and for IPv6 the scope ids), and
if that holds `self.network == other.network`. -/
def ifaceEq (bits x : Nat) (sx : Option String) (px y : Nat) (sy : Option String) (py : Nat) : Bool :=
  addrEq bits x sx y sy && netEq (ifaceNet bits x sx px) (ifaceNet bits y sy py)

/-- `self < other` for an interface `self` (`max_prefixlen` `bits`, `_ip` `x`, scope id `sx`, prefix
length `px`) and an address or interface `other` of its version, `IPv4Interface.__lt__`
(:1443-1453) and `IPv6Interface.__lt__` (:2237-2247): `address_less` is not `NotImplemented` for an
address; then `self.network < other.network or ...`, where an address has no `network`, and the
`AttributeError` gives `False` (:1450-1453, "the unassociated address is considered less than all
interfaces"). -/
def ifaceLtOp (bits x : Nat) (sx : Option String) (px : Nat) : Operand → Bool
  | .iface _ y sy py => ifaceLt bits x sx px y sy py
  | .addr _ _ _ | .net _ | .other _ => false

/-- `self == other` for an interface `self` and an address or interface `other` of its version,
`IPv4Interface.__eq__` (:1431-1441) and `IPv6Interface.__eq__` (:2225-2235): unequal addresses
return `False` (:1433-1434); equal ones go on to `self.network == other.network`, and an address has
no `network`, so the `AttributeError` gives `False` (:1435-1441). -/
def ifaceEqOp (bits x : Nat) (sx : Option String) (px : Nat) : Operand → Bool
  | .iface _ y sy py => ifaceEq bits x sx px y sy py
  | .addr _ y sy => if !addrEq bits x sx y sy then false else false
  | .net _ | .other _ => false

/-- `first > last` (:229) for two operands of one version that pass the `isinstance` check (an
address or an interface). Two addresses: `addrGt`. An interface `first`: `first.__gt__` is
`total_ordering`'s `_gt_from_lt` (Lib/functools.py:89-94), `not first < last and first != last`
with the interface's `__lt__`, and `!=` is `not first.__eq__(last)` (Objects/typeobject.c:7590-7597).
An address `first` and an interface `last`: the interface's type is a proper subclass of the
address's, so Python calls the reflected `last.__lt__(first)` first (Objects/object.c:1055-1061),
and its result, never `NotImplemented` for an address, is the answer. -/
def summarizeGt (first last : Operand) : Bool :=
  match first, last with
  | .addr b x sx, .addr _ y sy => addrGt b x sx y sy
  | .iface b x sx px, l => !ifaceLtOp b x sx px l && !ifaceEqOp b x sx px l
  | .addr _ _ _, .iface b y sy py => ifaceLtOp b y sy py first
  | _, _ => false

/-- `list(summarize_address_range(first, last))`, ipaddress.py:197-249: the `isinstance` check
against `_BaseAddress` (:223-225), which interfaces pass, and the version check (:226-228) come
first; then `first > last` (:229, `summarizeGt`), and the rest reads only `_ip`. -/
def summarizeOp (first last : Operand) : Py (List Net) :=
  match first, last with
  | .addr b1 x sx, .addr b2 y sy =>
    if versionOf b1 ≠ versionOf b2 then .error (.typeError "~are not of the same version")
    else summarizeAddressRange b1 x sx y sy
  | .iface b1 x _ _, .addr b2 y _ | .addr b1 x _, .iface b2 y _ _
  | .iface b1 x _ _, .iface b2 y _ _ =>
    if versionOf b1 ≠ versionOf b2 then .error (.typeError "~are not of the same version")
    else if summarizeGt first last then
      .error (.valueError "last IP address must be greater than first")
    else summarizeInts b1 x y
  | _, _ => .error (.typeError "first and last must be IP addresses, not networks")

/-- `list(range(start, stop, step))` for `step > 0`. -/
def pyRange (start stop step : Nat) : List Nat :=
  go (stop - start) start
where
  go : Nat → Nat → List Nat
    | 0, _ => []
    | fuel + 1, x => if x < stop then x :: go fuel (x + step) else []

/-- `list(self.subnets(prefixlen_diff, new_prefix))`, ipaddress.py:921-972: a network of one
address yields itself, scope id included (:947-949); otherwise the argument checks (:951-965), and
networks built from ints (:967-972), so with no scope id. -/
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

/-- `self.supernet(prefixlen_diff, new_prefix)`, ipaddress.py:974-1013: a `/0` network returns
itself (:995-996); otherwise the argument checks (:998-1009) and a network built from an int
(:1010-1013), so with no scope id. `int(self.netmask) << prefixlen_diff` raises for a negative
shift count. -/
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
`False` (:733-734), a network is `False` (:736-737), an address or interface is tested against the
mask through its `_ip` (:741). `other.version` raises `AttributeError` for an object without it. -/
def containsOp (n : Net) : Operand → Py Bool
  | .other ty => .error (.named "AttributeError" s!"'{ty}' object has no attribute 'version'")
  | .addr b x _ => if versionOf n.bits ≠ versionOf b then .ok false else .ok (contains n x)
  | .iface b x _ _ => if versionOf n.bits ≠ versionOf b then .ok false else .ok (contains n x)
  | .net m => if versionOf n.bits ≠ versionOf m.bits then .ok false else .ok false

/-- `x in c` for an address `x`: a network's `__contains__`; an address, an interface or another
object has neither `__contains__` nor `__iter__`, and `in` raises `TypeError`. -/
def inOp (x : Operand) : Operand → Py Bool
  | .net m => containsOp m x
  | .addr b _ _ => .error (.typeError s!"argument of type 'IPv{versionOf b}Address' is not a container or iterable")
  | .iface b _ _ _ => .error (.typeError s!"argument of type 'IPv{versionOf b}Interface' is not a container or iterable")
  | .other ty => .error (.typeError s!"argument of type '{ty}' is not a container or iterable")

/-- `self.overlaps(other)`, ipaddress.py:743-748: four `in` tests joined by `or`. For an `other`
that is not a network the first `in` raises, so `other.network_address` is reached only for a
network. A network address carries its network's scope id; `broadcast_address` is built from an
int (:750-753), so it has none. -/
def overlapsOp (s : Net) (o : Operand) : Py Bool := do
  if ← inOp (.addr s.bits s.addr s.scope) o then return true
  if ← inOp (.addr s.bits s.broadcast none) o then return true
  match o with
  | .net m =>
    if ← containsOp s (.addr m.bits m.addr m.scope) then return true
    containsOp s (.addr m.bits m.broadcast none)
  | _ => .error (.named "AttributeError" "~object has no attribute 'network_address'")

/-- `b.network_address <= a.network_address and b.broadcast_address >= a.broadcast_address`,
ipaddress.py:1033-1034, for networks of the same version: `<=` is `total_ordering`'s
`b < a or b == a` on the network addresses, scope ids included (`addrLe`); the broadcast addresses
are built from ints (:750-753) and `>=` is `not b < a` (`addrGe`). -/
def subnetOf (a b : Net) : Bool :=
  addrLe b.bits b.addr b.scope a.addr a.scope && addrGe b.broadcast a.broadcast

/-- `_BaseNetwork._is_subnet_of(a, b)`, ipaddress.py:1028-1037, for any two operands (a static
method: `subnet_of` passes `self` as `a`, `supernet_of` passes its argument). In the `try`
(:1029-1034): `a.version` and `b.version` (an `AttributeError` for an object without one), the
version check, which raises `TypeError` (:1031-1032) that the `except AttributeError` does not
catch; then `b.network_address` and `a.network_address`, which an address or an interface lacks
(`AttributeError`), and the comparisons of two networks (`subnetOf`). Every `AttributeError` becomes
`TypeError('Unable to test subnet containment between ...')` (:1035-1037). -/
def isSubnetOf (a b : Operand) : Py Bool :=
  if a.isOther || b.isOther then .error (.typeError "~Unable to test subnet containment between")
  else if versionOf a.bits ≠ versionOf b.bits then .error (.typeError "~are not of the same version")
  else match b.asNet, a.asNet with
    | some nb, some na => .ok (subnetOf na nb)
    | _, _ => .error (.typeError "~Unable to test subnet containment between")

/-- `self.subnet_of(other)`, ipaddress.py:1039-1041: `_is_subnet_of(self, other)`. -/
def subnetOfOp (s : Net) (o : Operand) : Py Bool := isSubnetOf (.net s) o

/-- `self.supernet_of(other)`, ipaddress.py:1043-1045: `_is_subnet_of(other, self)`. -/
def supernetOfOp (s : Net) (o : Operand) : Py Bool := isSubnetOf o (.net s)

/-- `s1, s2 = net.subnets()`; unpacking raises when there is one subnet. -/
def halves (n : Net) : Py (Net × Net) := do
  match ← subnets n 1 none with
  | [a, b] => return (a, b)
  | [_] => throw (.valueError "not enough values to unpack (expected 2, got 1)")
  | _ => throw (.valueError "~too many values to unpack")

/-- The `while` loop and tail of `address_exclude`, ipaddress.py:841-861: `s1 != other` is
`not s1 == other` (`netEq`). -/
def excludeLoop (other : Net) : Nat → Net → Net → Py (List Net)
  | 0, _, _ => .error .modelFuel
  | fuel + 1, s1, s2 =>
    if !netEq s1 other && !netEq s2 other then
      if subnetOf other s1 then do
        let (a, b) ← halves s1
        return s2 :: (← excludeLoop other fuel a b)
      else if subnetOf other s2 then do
        let (a, b) ← halves s2
        return s1 :: (← excludeLoop other fuel a b)
      else .error (.assertionError "~Error performing exclusion")
    else if netEq s1 other then .ok [s2]
    else if netEq s2 other then .ok [s1]
    else .error (.assertionError "~Error performing exclusion")

/-- `list(self.address_exclude(other))` for two networks of the same version,
ipaddress.py:831-861. `other.subnet_of(self)` (:831) is `subnetOf other s` for networks of one
version, and `other == self` (:833) is `netEq`. Re-creating `other` from
`'%s/%s' % (other.network_address, other.prefixlen)` (:837-838) is the identity on `Net`: `str` of
an IPv6 address appends `%` and its scope id (:2004), `IPv6Address` reads every 128-bit address and
scope id back from that (`V6RoundTrip`), and a stored scope id never holds `/`
(`IPv6Address.__init__` refuses one first, :1955-1956, `V6InitStr`), so `_split_optional_netmask`
(:153-158) splits at the prefix. `self.subnets()` (:840) builds both halves from ints, so they have
no scope id. -/
def addressExclude (s other : Net) : Py (List Net) := do
  if ¬subnetOf other s then throw (.valueError "~not contained in")
  if netEq other s then return []
  let (s1, s2) ← halves s
  excludeLoop other (s.bits + 1) s1 s2

/-- `list(self.address_exclude(other))`, ipaddress.py:788-861: `other.version` (an
`AttributeError` for an object without it) and the version check (:824-826), then the network
check (:828-829), which an address or an interface fails. -/
def addressExcludeOp (s : Net) (o : Operand) : Py (List Net) :=
  match o with
  | .other ty => .error (.named "AttributeError" s!"'{ty}' object has no attribute 'version'")
  | .addr b _ _ | .iface b _ _ _ =>
    if versionOf s.bits ≠ versionOf b then .error (.typeError "~are not of the same version")
    else .error (.typeError "~is not a network object")
  | .net m =>
    if versionOf s.bits ≠ versionOf m.bits then .error (.typeError "~are not of the same version")
    else addressExclude s m

end PyLean.Ipaddress
