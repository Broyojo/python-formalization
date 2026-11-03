import PyLean.Ipaddress.Parse6Props

/-!
The 3.15 changes to `ipaddress` outside the integer core: `exploded` of IPv6 objects,
`is_unspecified` of interfaces and the module `__getattr__`.

`_BaseV6._explode_shorthand_ip_string` builds `ip_str` (ipaddress.py:1868-1873) and parses it
back with `_ip_int_from_string` (:1875), here `ipIntFromString6`. For an address the text is
`_string_from_ip_int(self._ip)`, for an interface `str(self.ip)` (an `IPv6Address` without the
scope id), and for a network `str(self.network_address)`, which keeps the scope id the parser
then refuses.

Text is `List Char`, as in `Fractions.Format`, so that counterexamples evaluate.
-/

namespace PyLean.Ipaddress

open PyLean

/-- Which of the three classes `self` is. -/
inductive V6Kind where
  | address
  | interface
  | network
  deriving Repr, DecidableEq, Inhabited

/-- `'%04x'` of a value below `2**16`. -/
def hextet (v : Nat) : List Char :=
  [v / 4096 % 16, v / 256 % 16, v / 16 % 16, v % 16].map Nat.digitChar

/-- The eight 16-bit groups of an address, most significant first. -/
def hextets (ip : Nat) : List Nat :=
  (List.range 8).map (fun i => (ip >>> (16 * (7 - i))) &&& 0xffff)

/-- `':'.join([hex_str[x:x+4] for x in range(0, 32, 4)])` with
`hex_str = '%032x' % ip_int`, ipaddress.py:1876-1877. -/
def explodedHex (ip : Nat) : List Char :=
  List.intercalate [':'] ((hextets ip).map hextet)

/-- `'%s/%d' % (s, self._prefixlen)`. -/
def withPrefix (s : List Char) (p : Nat) : List Char := s ++ '/' :: Nat.toDigits 10 p

/-- `ip_str` of `_BaseV6._explode_shorthand_ip_string`, ipaddress.py:1868-1873: `str` of the
network address, which carries the scope id (:1869); `str(self.ip)`, where `ip` is
`IPv6Address(self._ip)` without the scope id (:1871, :2255-2256); `_string_from_ip_int(self._ip)`
(:1873). -/
def explodeIpStr (kind : V6Kind) (ip : Nat) (scope : Option (List Char)) : Py (List Char) :=
  match kind with
  | .network => ipv6StrPy ip scope
  | .interface => ipv6StrPy ip none
  | .address => stringFromIpInt6Py .address (some ip)

/-- `_BaseV6._explode_shorthand_ip_string`, ipaddress.py:1861-1884: the text, its re-parse
(:1875), the 32 hex digits in groups of four (:1876-1877), the prefix for a network (:1878-1879),
the scope id if there is one (:1880-1881), the prefix for an interface (:1882-1883). -/
def baseExplode (kind : V6Kind) (ip p : Nat) (scope : Option (List Char)) : Py (List Char) := do
  let ipStr ← explodeIpStr kind ip scope
  let ipInt ← ipIntFromString6 ipStr
  let exploded := explodedHex ipInt
  if kind = .network then return withPrefix exploded p
  let exploded := addScope exploded scope
  if kind = .interface then return withPrefix exploded p
  return exploded

/-- `str(IPv4Address(v))`, `_string_from_ip_int`, ipaddress.py:1241-1250. -/
def dottedQuad (v : Nat) : List Char :=
  List.intercalate ['.'] ([24, 16, 8, 0].map (fun s => Nat.toDigits 10 ((v >>> s) &&& 255)))

/-- `self.exploded`, ipaddress.py:386-389. `IPv6Address._explode_shorthand_ip_string`,
:1961-1967, which `IPv6Interface` inherits, keeps the first 30 characters of the base
result and appends the IPv4 part. `IPv6Network` has only the base method. -/
def explode (kind : V6Kind) (ip p : Nat) (scope : Option (List Char)) : Py (List Char) :=
  match kind, ipv4Mapped ip with
  | .address, some v4 | .interface, some v4 =>
    (fun raw => raw.take 30 ++ dottedQuad v4) <$> baseExplode kind ip p scope
  | _, _ => baseExplode kind ip p scope

/-- Every object the constructors build has an `exploded` form: `exploded` is a property
that takes no argument, and `compressed` and `str()` work on the same objects. -/
def ExplodedTotal : Prop :=
  ∀ (kind : V6Kind) (ip p : Nat) (scope : Option (List Char)),
    ip < 2 ^ 128 → p ≤ 128 → scope ≠ some [] → ∃ s, explode kind ip p scope = .ok s

set_option maxRecDepth 20000 in
theorem explode_scoped_net : (explode .network 0 64 (some ['e'])).toBool = false := by decide

/-- `IPv6Network('1::%e/128').exploded` raises `AddressValueError`, here at `::%e/64`. -/
theorem explodedTotal_refuted : ¬ExplodedTotal := by
  intro h
  obtain ⟨s, hs⟩ := h .network 0 64 (some ['e']) (by decide) (by decide) (by decide)
  have := explode_scoped_net
  rw [hs] at this
  cases this

/-- The exploded text of an interface ends in `/prefixlen`, and of a scoped address in its
scope id, as `compressed` and `str()` do. -/
def ExplodedKeepsSuffix : Prop :=
  (∀ (ip p : Nat) (scope : Option (List Char)) (s : List Char),
    explode .interface ip p scope = .ok s → ('/' :: Nat.toDigits 10 p).isSuffixOf s = true) ∧
  (∀ (ip p : Nat) (sc s : List Char),
    explode .address ip p (some sc) = .ok s → ('%' :: sc).isSuffixOf s = true)

set_option maxRecDepth 20000 in
theorem explode_mapped_iface : explode .interface 0xffff01020304 64 none =
    .ok "0000:0000:0000:0000:0000:ffff:1.2.3.4".toList := by decide

/-- `IPv6Interface('::ffff:1.2.3.4/64').exploded` loses the `/64`. -/
theorem explodedKeepsSuffix_refuted : ¬ExplodedKeepsSuffix := by
  intro h
  have := h.1 0xffff01020304 64 none _ explode_mapped_iface
  revert this
  decide

/-- What `exploded` is, by case, once those two are set aside, for every 128-bit address: a
network without scope id and every object outside `::ffff:0:0/96` keep the prefix and the scope
id, and an IPv4-mapped address or interface is the 30 characters of its first six groups and a
dotted quad, with neither. The re-parse (:1875) gives the address back in each case. No scope id or
prefix reaches a mapped result: that is the refuted `ExplodedKeepsSuffix`, as a positive
statement. -/
def ExplodedByCase : Prop :=
  ∀ (ip p : Nat) (scope : Option (List Char)), ip < 2 ^ 128 →
    explode .network ip p none = .ok (withPrefix (explodedHex ip) p) ∧
    (ipv4Mapped ip = none →
      explode .address ip p scope = .ok (addScope (explodedHex ip) scope) ∧
      explode .interface ip p scope = .ok (withPrefix (addScope (explodedHex ip) scope) p)) ∧
    (∀ v4, ipv4Mapped ip = some v4 →
      explode .address ip p scope = .ok ((addScope (explodedHex ip) scope).take 30 ++ dottedQuad v4) ∧
      explode .interface ip p scope =
        .ok ((withPrefix (addScope (explodedHex ip) scope) p).take 30 ++ dottedQuad v4))

theorem str_reparse (ip : Nat) (h : ip < 2 ^ 128) :
    ipv6StrPy ip none = .ok (base6 ip) ∧ ipIntFromString6 (base6 ip) = .ok ip := by
  refine ⟨?_, (base6_ok ip h).2⟩
  rw [ipv6StrPy_eq ip h]
  rfl

theorem plain_reparse (ip : Nat) (h : ip < 2 ^ 128) :
    stringFromIpInt6Py .address (some ip) = .ok (stringFromIpInt6 ip) ∧
      ipIntFromString6 (stringFromIpInt6 ip) = .ok ip := by
  exact ⟨stringFromIpInt6Py_nat .address ip h, plain_roundtrip ip h⟩

theorem explodedByCase_proven : ExplodedByCase := by
  intro ip p scope hip
  obtain ⟨s1, s2⟩ := str_reparse ip hip
  obtain ⟨a1, a2⟩ := plain_reparse ip hip
  refine ⟨?_, fun h => ?_, fun v4 h => ?_⟩
  · simp [explode, baseExplode, explodeIpStr, s1, s2, bind, Except.bind, pure, Except.pure]
  · simp [explode, baseExplode, explodeIpStr, h, s1, s2, a1, a2, bind, Except.bind, pure, Except.pure]
  · simp [explode, baseExplode, explodeIpStr, h, s1, s2, a1, a2, bind, Except.bind, pure, Except.pure,
      Functor.map, Except.map]

/-- The groups `exploded` prints are the address: read back as a base-65536 number they
give `ip`, for every 128-bit `ip`. So `_ip_int_from_string`'s round trip, which the model
leaves out, loses nothing here. -/
def HextetsRecompose : Prop :=
  ∀ ip : Nat, ip < 2 ^ 128 → (hextets ip).foldl (fun acc g => acc * 65536 + g) 0 = ip

theorem hextetsRecompose_proven : HextetsRecompose := by
  intro ip h
  have e : ∀ k : Nat, (ip >>> k) &&& 0xffff = ip / 2 ^ k % 65536 := by
    intro k
    rw [Nat.shiftRight_eq_div_pow, show (0xffff : Nat) = 2 ^ 16 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod]
  simp only [hextets, List.range, List.range.loop, List.map, List.foldl, e,
    show 16 * (7 - 0) = 112 from rfl, show 16 * (7 - 1) = 96 from rfl, show 16 * (7 - 2) = 80 from rfl,
    show 16 * (7 - 3) = 64 from rfl, show 16 * (7 - 4) = 48 from rfl, show 16 * (7 - 5) = 32 from rfl,
    show 16 * (7 - 6) = 16 from rfl, show 16 * (7 - 7) = 0 from rfl]
  omega

/-! ### `is_unspecified` -/

/-- `IPv4Address.is_unspecified`, ipaddress.py:1371-1380, and
`IPv6Address.is_unspecified`, :2137-2149, which looks through `ipv4_mapped`. -/
def addrIsUnspecified (bits a : Nat) : Bool :=
  if bits = 128 then
    match ipv4Mapped a with
    | some v4 => v4 == 0
    | none => a == 0
  else a == 0

/-- `_BaseNetwork.is_unspecified`, ipaddress.py:1099-1108. -/
def netIsUnspecified (n : Net) : Bool :=
  addrIsUnspecified n.bits n.addr && addrIsUnspecified n.bits n.broadcast

/-- `IPv4Interface.is_unspecified`, ipaddress.py:1479-1481, new in 3.15, and
`IPv6Interface.is_unspecified`, :2273-2275. `self.network` is the masked network. -/
def ifaceIsUnspecified (bits ip p : Nat) : Bool :=
  ip == 0 && netIsUnspecified ⟨bits, ip &&& ipIntFromPrefix bits p, p, none⟩

/-- An interface is unspecified exactly when it is `0.0.0.0/32` or `::/128`. `0.0.0.0/8`
is not: its address is zero, but its network is not the single unspecified address. -/
def IfaceUnspecified : Prop :=
  (∀ ip p : Nat, ip ≠ 0 → ifaceIsUnspecified 32 ip p = false ∧ ifaceIsUnspecified 128 ip p = false) ∧
  (∀ p : Fin 33, ifaceIsUnspecified 32 0 p = (p.val == 32)) ∧
  (∀ p : Fin 129, ifaceIsUnspecified 128 0 p = (p.val == 128))

set_option maxRecDepth 100000 in
theorem ifaceUnspecified_proven : IfaceUnspecified := by
  refine ⟨?_, by decide, by decide⟩
  intro ip p h
  simp [ifaceIsUnspecified, h]

/-! ### Module `__getattr__` -/

/-- `ipaddress.<name>`, ipaddress.py:2425-2431: `__version__` moved here from a module
constant in 3.15, and warns. The warning is not modelled. -/
def moduleGetattr (name : String) : Py String :=
  if name = "__version__" then .ok "1.0"
  else .error (.named "AttributeError" s!"module 'ipaddress' has no attribute '{name}'")

end PyLean.Ipaddress
