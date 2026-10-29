import PyLean.Ipaddress.Model

/-!
Arithmetic vocabulary for stating `ipaddress` properties without bitwise
operations: a valid network is an aligned block of `2^(bits - prefixlen)`
addresses.
-/

namespace PyLean.Ipaddress

/-- The address families CPython implements. -/
def IsVersion (bits : Nat) : Prop := bits = 32 ∨ bits = 128

instance : DecidablePred IsVersion := fun b => inferInstanceAs (Decidable (b = 32 ∨ b = 128))

/-- What `IPvXNetwork(...)` with `strict=True` can produce. -/
def Net.Valid (n : Net) : Prop :=
  n.prefixlen ≤ n.bits ∧ n.addr < 2 ^ n.bits ∧ n.addr % 2 ^ (n.bits - n.prefixlen) = 0

instance (n : Net) : Decidable n.Valid := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Number of addresses in the block. -/
def Net.size (n : Net) : Nat := 2 ^ (n.bits - n.prefixlen)

/-- Address `x` lies in the block. -/
def Net.mem (n : Net) (x : Nat) : Bool := n.addr ≤ x && x < n.addr + n.size

/-- `ns` lists blocks in ascending order that together cover exactly the
addresses `lo, lo+1, ..., hi` once each (empty when `lo = hi + 1`). -/
def Tiles : List Net → Nat → Nat → Prop
  | [], lo, hi => lo = hi + 1
  | n :: ns, lo, hi => n.addr = lo ∧ Tiles ns (lo + n.size) hi

end PyLean.Ipaddress
