import PyLean.Ipaddress.Spec

/-!
`subnets`, `supernet` and `address_exclude` on valid arguments.
-/

namespace PyLean.Ipaddress

open PyLean

/-- `subnets` docstring, ipaddress.py:925-951: with a valid `prefixlen_diff`
the result is the `2^prefixlen_diff` subnets of the new prefix length that
"join to make the current subnet", in ascending order. -/
def SubnetsPartition : Prop :=
  ∀ (n : Net) (d : Nat), IsVersion n.bits → n.Valid → n.prefixlen < n.bits →
    n.prefixlen + d ≤ n.bits →
    ∃ ns, subnets n d none = .ok ns ∧ ns.length = 2 ^ d ∧
      (∀ m ∈ ns, m.bits = n.bits ∧ m.Valid ∧ m.prefixlen = n.prefixlen + d) ∧
      Tiles ns n.addr (n.addr + n.size - 1)

theorem subnetsPartition_proven : SubnetsPartition := by
  sorry

/-- `supernet` docstring, ipaddress.py:978-998: for `0 <= d <= prefixlen` the
result is the unique valid network of prefix length `prefixlen - d` that
contains `self`. -/
def SupernetContains : Prop :=
  ∀ (n : Net) (d : Nat), IsVersion n.bits → n.Valid → 0 < n.prefixlen → d ≤ n.prefixlen →
    ∃ s, supernet n d none = .ok s ∧ s.bits = n.bits ∧ s.Valid ∧
      s.prefixlen = n.prefixlen - d ∧ subnetOf n s = true

theorem supernetContains_proven : SupernetContains := by
  sorry

/-- `address_exclude` docstring, ipaddress.py:792-825: for `other` a subnet of
`self`, the result is "self minus other": valid networks of the same version
that, together with `other`, cover every address of `self` exactly once. -/
def AddressExcludePartition : Prop :=
  ∀ s o : Net, IsVersion s.bits → s.Valid → o.Valid → o.bits = s.bits →
    subnetOf o s = true →
    ∃ out, addressExclude s o = .ok out ∧
      (∀ m ∈ out, m.bits = s.bits ∧ m.Valid) ∧
      ∀ x, out.countP (fun m => m.mem x) = if s.mem x && !o.mem x then 1 else 0

theorem addressExcludePartition_proven : AddressExcludePartition := by
  sorry

end PyLean.Ipaddress
