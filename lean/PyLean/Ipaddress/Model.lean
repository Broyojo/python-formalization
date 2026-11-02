import PyLean.Core

/-!
Model of the integer core of CPython `Lib/ipaddress.py` (3.15.2): network
construction from `(int, int)`,
`summarize_address_range`, `subnets`, `supernet`, `__getitem__`,
`__contains__`, `overlaps`, `subnet_of` and `address_exclude`.

A network is modelled by its `max_prefixlen` (32 for IPv4, 128 for IPv6),
the integer value of its network address, and its prefix length. String
parsing and formatting are out of scope here; exception messages that embed a
formatted address start with `~` and the differential tester compares only
their class.
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

/-- `_check_int_address`, ipaddress.py:407-414. -/
def checkIntAddress (bits : Nat) (a : Int) : Py Nat :=
  if a < 0 then .error (.named "AddressValueError" "~(< 0) is not permitted")
  else if a > allOnes bits then .error (.named "AddressValueError" "~(>= 2**n) is not permitted")
  else .ok a.toNat

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

/-- `list(summarize_address_range(first, last))` for two addresses of the same
version, ipaddress.py:197-249. -/
def summarizeAddressRange (bits first last : Nat) : Py (List Net) :=
  if first > last then .error (.valueError "last IP address must be greater than first")
  else summarizeLoop bits last (last - first + 2) first

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

/-- `address in self` for an address of the same version, ipaddress.py:731-741. -/
def contains (n : Net) (a : Nat) : Bool := a &&& n.netmask == n.addr

/-- `a.subnet_of(b)` for networks of the same version, ipaddress.py:1028-1041. -/
def subnetOf (a b : Net) : Bool := b.addr ≤ a.addr && b.broadcast ≥ a.broadcast

/-- `self.overlaps(other)`, ipaddress.py:743-748. -/
def overlaps (s o : Net) : Bool :=
  contains o s.addr || contains o s.broadcast || contains s o.addr || contains s o.broadcast

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
ipaddress.py:788-861. Re-creating `other` from its network address and
prefix length (:839-840) is the identity on `Net`. -/
def addressExclude (s other : Net) : Py (List Net) := do
  if ¬subnetOf other s then throw (.valueError "~not contained in")
  if other = s then return []
  let (s1, s2) ← halves s
  excludeLoop other (s.bits + 1) s1 s2

end PyLean.Ipaddress
