import PyLean.Ipaddress.Spec

/-!
Argument validation of `subnets` and `supernet` against their docstrings.
Both functions return early for the extreme prefix length (`/32` or `/128`
for `subnets`, `/0` for `supernet`) before any argument check runs.
-/

namespace PyLean.Ipaddress

open PyLean

/-- `subnets` docstring, ipaddress.py:943-949: "Raises: ValueError: The
prefixlen_diff is too small or too large. OR prefixlen_diff and new_prefix are
both set or new_prefix is a smaller number than the current prefix". -/
def SubnetsRejectsInvalidArgs : Prop :=
  ∀ (n : Net) (d : Int) (np : Option Int), IsVersion n.bits → n.Valid →
    ((∃ k, np = some k ∧ (k < n.prefixlen ∨ d ≠ 1)) ∨
     (np = none ∧ (d < 0 ∨ n.prefixlen + d > n.bits))) →
    (subnets n d np).raises "ValueError"

/-- `IPv4Network('192.0.2.1/32').subnets(new_prefix=24)` returns the network
itself; the same call on any shorter prefix raises `ValueError`. -/
theorem subnetsRejectsInvalidArgs_refuted : ¬SubnetsRejectsInvalidArgs := by
  intro h
  have hr := h ⟨32, 3221225985, 32⟩ 1 (some 24) (Or.inl rfl) (by decide)
    (Or.inl ⟨24, rfl, Or.inl (by decide)⟩)
  have hv : subnets ⟨32, 3221225985, 32⟩ 1 (some 24) = .ok [⟨32, 3221225985, 32⟩] := by decide
  obtain ⟨e, he, -⟩ := hr
  rw [hv] at he
  cases he

/-- `supernet` docstring, ipaddress.py:990-997: "Raises: ValueError: If
self.prefixlen - prefixlen_diff < 0. I.e., you have a negative prefix length.
OR If prefixlen_diff and new_prefix are both set or new_prefix is a larger
number than the current prefix". -/
def SupernetRejectsInvalidArgs : Prop :=
  ∀ (n : Net) (d : Int) (np : Option Int), IsVersion n.bits → n.Valid →
    ((∃ k, np = some k ∧ (k > n.prefixlen ∨ d ≠ 1)) ∨
     (np = none ∧ (n.prefixlen : Int) - d < 0)) →
    (supernet n d np).raises "ValueError"

/-- `IPv4Network('0.0.0.0/0').supernet(prefixlen_diff=5)` and
`.supernet(new_prefix=8)` return the network itself. -/
theorem supernetRejectsInvalidArgs_refuted : ¬SupernetRejectsInvalidArgs := by
  intro h
  have hr := h ⟨32, 0, 0⟩ 5 none (Or.inl rfl) (by decide) (Or.inr ⟨rfl, by decide⟩)
  have hv : supernet ⟨32, 0, 0⟩ 5 none = .ok ⟨32, 0, 0⟩ := by decide
  obtain ⟨e, he, -⟩ := hr
  rw [hv] at he
  cases he

end PyLean.Ipaddress
