import PyLean.Ipaddress.Spec

/-!
Indexing and membership: `__getitem__`, `__contains__`, `overlaps`,
`subnet_of`.
-/

namespace PyLean.Ipaddress

open PyLean

/-- `net[i]` behaves like indexing a Python sequence of the block's addresses:
for `-size <= i < size` it returns `addr + i mod size`, otherwise it raises
`IndexError`. Library docs: "network objects ... can be indexed". -/
def GetitemSequence : Prop :=
  ∀ (n : Net) (i : Int), n.Valid →
    getitem n i =
      if -(n.size : Int) ≤ i ∧ i < n.size then .ok (n.addr + (i % n.size).toNat)
      else .error (.indexError "address out of range")

theorem getitemSequence_proven : GetitemSequence := by
  sorry

/-- `address in net` holds exactly for the addresses of the block. -/
def ContainsMem : Prop :=
  ∀ (n : Net) (x : Nat), n.Valid → x < 2 ^ n.bits → contains n x = n.mem x

theorem containsMem_proven : ContainsMem := by
  sorry

/-- `overlaps` docstring, ipaddress.py:747: "Tell if self is partly contained
in other", i.e. the two blocks share an address. -/
def OverlapsShareAddress : Prop :=
  ∀ a b : Net, a.Valid → b.Valid → a.bits = b.bits →
    (overlaps a b = true ↔ ∃ x, a.mem x = true ∧ b.mem x = true)

theorem overlapsShareAddress_proven : OverlapsShareAddress := by
  sorry

/-- `subnet_of`: every address of `a` is an address of `b`. -/
def SubnetOfMem : Prop :=
  ∀ a b : Net, a.Valid → b.Valid → a.bits = b.bits →
    (subnetOf a b = true ↔ ∀ x, a.mem x = true → b.mem x = true)

theorem subnetOfMem_proven : SubnetOfMem := by
  sorry

end PyLean.Ipaddress
