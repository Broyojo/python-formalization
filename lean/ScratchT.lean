theorem t1 (S p : Nat) : S + 0x7f800000 + 0x400000 + p = S + 0x7fc00000 + p := by omega
theorem t2 (S p : Nat) : S + 0x7f800000 + 0 + p = S + 0x7fc00000 + p - 0x400000 := by omega
theorem t3 (S p : Nat) : S + 0x7f800000 + 0x400000 + p = S + 0x7fc00000 + p := by
  rw [Nat.add_assoc S 0x7f800000 0x400000]
