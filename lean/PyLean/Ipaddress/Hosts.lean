import PyLean.Ipaddress.Lookup

/-!
`list(net)` (`_BaseNetwork.__iter__`, Lib/ipaddress.py:689-693), `list(net.hosts())` and
`num_addresses` (:771-774), CPython 3.15.2. `hosts` is `_BaseNetwork.hosts` (:677-687) for IPv4,
`IPv6Network.hosts` (:2346-2355) for IPv6, and is rebound per instance by `IPv4Network.__init__`
(:1546-1549) and `IPv6Network.__init__` (:2341-2344) at the two longest prefixes.
-/

namespace PyLean.Ipaddress

open PyLean

/-- `list(net)`: `range(network, broadcast + 1)`. -/
def iterList (n : Net) : List Nat := pyRange n.addr (n.broadcast + 1) 1

/-- `list(net.hosts())`. At `max_prefixlen - 1` the instance's `hosts` is `__iter__`; at
`max_prefixlen` it yields the constructor's address, which is the network address there. -/
def hostsList (n : Net) : List Nat :=
  if n.prefixlen = n.bits - 1 then iterList n
  else if n.prefixlen = n.bits then [n.addr]
  else if n.bits = 32 then pyRange (n.addr + 1) n.broadcast 1
  else pyRange (n.addr + 1) (n.broadcast + 1) 1

/-- What the documentation says `hosts()` leaves out of the network's addresses: for IPv4 the
network and broadcast addresses, except at /31 and /32; for IPv6 the Subnet-Router anycast
(network) address, except at /127 and /128 (Doc/library/ipaddress.rst, `hosts()`). -/
def docKeep (n : Net) (x : Nat) : Bool :=
  if n.prefixlen + 1 ≥ n.bits then true
  else if n.bits = 32 then x != n.addr && x != n.addr + n.size - 1
  else x != n.addr

/-- For every valid IPv4 or IPv6 network: iterating it yields all `2**(bits - prefixlen)`
addresses from the network address up, `num_addresses` is that count, and `hosts()` yields the same
addresses in the same order minus exactly the ones the documentation excludes. -/
def HostsDoc : Prop :=
  ∀ n : Net, n.Valid → IsVersion n.bits →
    iterList n = List.range' n.addr n.size ∧ n.numAddresses = n.size ∧
    hostsList n = (List.range' n.addr n.size).filter (docKeep n)

theorem pyRange_go (stop : Nat) : ∀ k x, x + k = stop → pyRange.go stop 1 k x = List.range' x k := by
  intro k
  induction k with
  | zero => intro x _; simp [pyRange.go]
  | succ k ih =>
    intro x hx
    simp only [pyRange.go, show x < stop by omega, if_true, List.range'_succ]
    rw [ih (x + 1) (by omega)]

theorem pyRange_one (a b : Nat) (h : a ≤ b) : pyRange a b 1 = List.range' a (b - a) :=
  pyRange_go b (b - a) a (by omega)

theorem filter_ends (a k : Nat) (hk : 2 ≤ k) :
    (List.range' a k).filter (fun x => x != a && x != a + k - 1) = List.range' (a + 1) (k - 2) := by
  have e : List.range' a k = a :: (List.range' (a + 1) (k - 2) ++ [a + k - 1]) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rw [show j + 2 = (j + 1) + 1 by omega, List.range'_succ]
    congr 1
    have := @List.range'_append_1 (a + 1) j 1
    rw [← this]; simp; omega
  rw [e, List.filter_cons, List.filter_append]
  simp only [bne_self_eq_false, Bool.false_and, Bool.false_eq_true, if_false]
  rw [List.filter_eq_self.mpr, List.filter_eq_nil_iff.mpr]
  · simp
  · intro x hx; simp at hx; subst hx; simp
  · intro x hx
    simp only [List.mem_range'_1] at hx
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]; omega

theorem filter_first (a k : Nat) (hk : 1 ≤ k) :
    (List.range' a k).filter (fun x => x != a) = List.range' (a + 1) (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [List.range'_succ, List.filter_cons]
  simp only [bne_self_eq_false, Bool.false_eq_true, if_false, Nat.add_sub_cancel]
  rw [List.filter_eq_self.mpr]
  intro x hx; simp only [List.mem_range'_1] at hx; simp only [bne_iff_ne, ne_eq]; omega

theorem filter_all_true (l : List Nat) : l.filter (fun _ => true) = l :=
  List.filter_eq_self.mpr (by simp)

theorem hostsDoc_proven : HostsDoc := by
  intro n hv hver
  have hb := Net.broadcast_eq n hv
  have hs := Net.size_pos n
  have hit : iterList n = List.range' n.addr n.size := by
    unfold iterList; rw [hb, pyRange_one _ _ (by omega)]; congr 1; omega
  refine ⟨hit, ?_, ?_⟩
  · unfold Net.numAddresses; omega
  · obtain ⟨hp, _, _⟩ := hv
    unfold hostsList docKeep
    by_cases h1 : n.prefixlen = n.bits - 1
    · have hc : n.prefixlen + 1 ≥ n.bits := by omega
      rw [if_pos h1]; simp only [hc, ite_true, filter_all_true, hit]
    · rw [if_neg h1]
      by_cases h2 : n.prefixlen = n.bits
      · have hc : n.prefixlen + 1 ≥ n.bits := by omega
        have : n.size = 1 := by unfold Net.size; rw [h2, Nat.sub_self]
        rw [if_pos h2]; simp only [hc, ite_true, filter_all_true, this]; simp [List.range']
      · have hc : ¬ (n.prefixlen + 1 ≥ n.bits) := by omega
        rw [if_neg h2]
        simp only [hc, ite_false]
        have hsz : 4 ≤ n.size := by
          unfold Net.size
          have : 2 ≤ n.bits - n.prefixlen := by omega
          calc 4 = 2 ^ 2 := rfl
            _ ≤ 2 ^ (n.bits - n.prefixlen) := Nat.pow_le_pow_right (by decide) this
        by_cases h32 : n.bits = 32
        · simp only [h32, ite_true]
          rw [hb, pyRange_one _ _ (by omega), filter_ends _ _ (by omega)]
          congr 1; omega
        · simp only [h32, ite_false]
          rw [hb, pyRange_one _ _ (by omega), filter_first _ _ (by omega)]
          congr 1; omega

end PyLean.Ipaddress
