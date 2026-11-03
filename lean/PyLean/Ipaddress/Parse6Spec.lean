import PyLean.Ipaddress.Parse6Props
import PyLean.Ipaddress.Mask4

/-!
IPv6 text beyond the round trip, CPython 3.15.2 `Lib/ipaddress.py`: what `__str__` prints
(`IPv6Address.__str__` :1998-2004, `_ipv4_mapped_ipv6_to_str` :1980-1996, `ipv4_mapped`
:2165-2176), the int and bytes constructors (:1939-1950), `_split_scope_id` (:1895-1913),
`_parse_hextet` (:1762-1786) on every spelling, and `_ip_int_from_string` (:1648-1760) on
uncompressed, compressed and dotted-quad spellings and on every refusal.
-/

namespace PyLean.Ipaddress

open PyLean

/-! ## `__str__` -/

/-- `IPv6Address.ipv4_mapped` (:2165-2176), `_ipv4_mapped_ipv6_to_str` (:1980-1996) and `__str__`
(:1998-2004), for every 128-bit address and scope id: `ipv4_mapped` is the low 32 bits exactly
for `::ffff:0:0/96`; such an address prints as `::ffff:` and its dotted quad (RFC 4291 2.2 item 3,
the method's docstring), and `_ipv4_mapped_ipv6_to_str` refuses every other address with
`AddressValueError`; every other address prints as `_string_from_ip_int` of it (which
`CompressRFC5952` pins); a non-empty scope id follows a `%`. -/
def V6StrForm : Prop :=
  ∀ ip : Nat, ip < 2 ^ 128 →
    ipv4Mapped ip = (if ip / 2 ^ 32 = 0xFFFF then some (ip % 2 ^ 32) else none) ∧
    (ip / 2 ^ 32 = 0xFFFF →
      ipv4MappedToStr ip = .ok ("::ffff:".toList ++ ipv4Str (ip % 2 ^ 32)) ∧
      ∀ sc, ipv6StrPy ip sc = .ok (addScope ("::ffff:".toList ++ ipv4Str (ip % 2 ^ 32)) sc)) ∧
    (ip / 2 ^ 32 ≠ 0xFFFF →
      ipv4MappedToStr ip = .error (.named "AddressValueError" "~Can not apply to non-IPv4-mapped IPv6 address") ∧
      ∀ sc, ipv6StrPy ip sc = .ok (addScope (stringFromIpInt6 ip) sc))

theorem v6StrForm_proven : V6StrForm := by
  intro ip hip
  have hle : ¬ ip > allOnes 128 := by unfold allOnes; omega
  have hq' : ¬ (65535 : Nat) > allOnes 128 := by unfold allOnes; decide
  refine ⟨ipv4Mapped_eq ip, fun hq => ?_, fun hq => ?_⟩
  · have h1 : ipv4MappedToStr ip = .ok ("::ffff:".toList ++ ipv4Str (ip % 2 ^ 32)) := by
      simp only [ipv4MappedToStr, ipv4Mapped_eq, hq, ↓reduceIte, stringFromIpInt6Py, shiftRight32]
      simp only [hq', ↓reduceIte, bind, Except.bind, pure, Except.pure]
      rw [show (0xFFFF : Nat) = 65535 from rfl, ffff_str]
      rfl
    refine ⟨h1, fun sc => ?_⟩
    simp only [ipv6StrPy, ipv4Mapped_eq, hq, ↓reduceIte, h1, bind, Except.bind, pure, Except.pure]
  · refine ⟨by simp [ipv4MappedToStr, ipv4Mapped_eq, hq], fun sc => ?_⟩
    simp [ipv6StrPy, ipv4Mapped_eq, hq, stringFromIpInt6Py, hle, bind, Except.bind, pure, Except.pure]

/-! ## Int and bytes -/

theorem foldl_bytes (l : List Nat) (a : Nat) :
    l.foldl (fun v b => v * 256 + b) a = a * 256 ^ l.length + l.foldl (fun v b => v * 256 + b) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (a * 256 + b), ih (0 * 256 + b), Nat.pow_succ]
    have e : a * (256 ^ l.length * 256) = a * 256 * 256 ^ l.length := by
      rw [Nat.mul_comm (256 ^ l.length) 256, Nat.mul_assoc]
    rw [e]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_mul]
    omega

theorem toBytesBE_succ (k n : Nat) : toBytesBE (k + 1) n = (n / 256 ^ k % 256) :: toBytesBE k n := by
  unfold toBytesBE
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.add_sub_cancel, Nat.sub_zero]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_apply, List.mem_range] at hi ⊢
  congr 3
  omega

/-- `int.from_bytes(n.to_bytes(k, 'big'), 'big')` is `n` modulo `256**k`. -/
theorem fromBytes_toBytesBE (k n : Nat) : fromBytesBig (toBytesBE k n) = n % 256 ^ k := by
  induction k with
  | zero => simp [toBytesBE, fromBytesBig, Nat.mod_one]
  | succ k ih =>
    rw [toBytesBE_succ]
    unfold fromBytesBig at ih ⊢
    rw [List.foldl_cons, foldl_bytes, ih]
    have hl : (toBytesBE k n).length = k := by simp [toBytesBE]
    rw [hl, Nat.pow_succ, Nat.mod_mul]
    simp only [Nat.zero_mul, Nat.zero_add]
    rw [Nat.mul_comm (256 ^ k)]
    omega

/-- `IPv6Address(int)` and `IPv6Address(bytes)`, ipaddress.py:1939-1950, with `_check_int_address`
(:407-414) and `_check_packed_address(address, 16)` (:416-421): an int is stored, with no scope id,
exactly when it is in `[0, 2**128)`, and otherwise `AddressValueError` names it and the bound;
sixteen bytes are read big-endian (so `n.to_bytes(16, 'big')` gives `n` back), and any other
length raises `AddressValueError` with the bytes' repr and both lengths. -/
def V6InitIntBytes : Prop :=
  (∀ v : Int, ipv6Init (.int v) =
    if v < 0 then
      .error (.named "AddressValueError" s!"{v} (< 0) is not permitted as an IPv{(6 : Nat)} address")
    else if 2 ^ 128 ≤ v then
      .error (.named "AddressValueError"
        s!"{v} (>= 2**{(128 : Nat)}) is not permitted as an IPv{(6 : Nat)} address")
    else .ok (v.toNat, none)) ∧
  (∀ b : List Nat, b.length = 16 → ipv6Init (.bytes b) = .ok (fromBytesBig b, none)) ∧
  (∀ n : Nat, n < 2 ^ 128 → ipv6Init (.bytes (toBytesBE 16 n)) = .ok (n, none)) ∧
  (∀ b : List Nat, b.length ≠ 16 →
    ipv6Init (.bytes b) = .error (.named "AddressValueError"
      s!"{bytesRepr b} (len {b.length} != {(16 : Nat)}) is not permitted as an IPv{(6 : Nat)} address"))

theorem v6InitIntBytes_proven : V6InitIntBytes := by
  refine ⟨fun v => ?_, fun b hb => ?_, fun n hn => ?_, fun b hb => ?_⟩
  · have hA : ((allOnes 128 : Nat) : Int) = 2 ^ 128 - 1 := by simp [allOnes]
    have hv : versionOf 128 = 6 := rfl
    simp only [ipv6Init, checkIntAddress, hA, hv]
    by_cases h0 : v < 0
    · simp [h0, bind, Except.bind]
    · by_cases h1 : (340282366920938463463374607431768211455 : Int) < v
      · have h1' : (340282366920938463463374607431768211456 : Int) ≤ v := by omega
        simp [h0, h1, h1', bind, Except.bind]
      · have h1' : ¬ (340282366920938463463374607431768211456 : Int) ≤ v := by omega
        simp [h0, h1, h1', bind, Except.bind, pure, Except.pure]
  · simp [ipv6Init, checkPackedAddress, hb, bind, Except.bind, pure, Except.pure]
  · have hl : (toBytesBE 16 n).length = 16 := by simp [toBytesBE]
    have hv := fromBytes_toBytesBE 16 n
    rw [Nat.mod_eq_of_lt (by omega)] at hv
    simp [ipv6Init, checkPackedAddress, hl, hv, bind, Except.bind, pure, Except.pure]
  · simp [ipv6Init, checkPackedAddress, hb, versionOf, bind, Except.bind]

/-! ## The scope id -/

/-- `_split_scope_id`, ipaddress.py:1895-1913 ("See RFC 4007"): a string without `%` has no scope
id; otherwise the scope id is everything after the first `%`, and an empty one or one holding a
second `%` raises `AddressValueError('Invalid IPv6 address: "%r"')` (:1911-1912), which
`IPv6Address` passes on (:1957). -/
def SplitScopeSpec : Prop :=
  (∀ a, '%' ∉ a → splitScopeId a = .ok (a, none)) ∧
  (∀ a sc, '%' ∉ a → sc ≠ [] → '%' ∉ sc → splitScopeId (a ++ '%' :: sc) = .ok (a, some sc)) ∧
  (∀ a sc, '%' ∉ a → (sc = [] ∨ '%' ∈ sc) →
    splitScopeId (a ++ '%' :: sc) =
      .error (avErr ((reprPlain (a ++ '%' :: sc)).map (fun r => "Invalid IPv6 address: \"" ++ r ++ "\"")))) ∧
  (∀ a sc, '%' ∉ a → (sc = [] ∨ '%' ∈ sc) → '/' ∉ a ++ '%' :: sc →
    ipv6Init (.str (a ++ '%' :: sc)) =
      .error (avErr ((reprPlain (a ++ '%' :: sc)).map (fun r => "Invalid IPv6 address: \"" ++ r ++ "\""))))

theorem splitScopeSpec_proven : SplitScopeSpec := by
  have bad : ∀ a sc, '%' ∉ a → (sc = [] ∨ '%' ∈ sc) →
      splitScopeId (a ++ '%' :: sc) =
        .error (avErr ((reprPlain (a ++ '%' :: sc)).map (fun r => "Invalid IPv6 address: \"" ++ r ++ "\""))) := by
    intro a sc ha hsc
    rcases hsc with rfl | h
    · simp [splitScopeId, partition_some a [] ha]
    · simp [splitScopeId, partition_some a sc ha, h]
  refine ⟨fun a ha => ?_, fun a sc ha h1 h2 => ?_, bad, fun a sc ha hsc hs => ?_⟩
  · simp [splitScopeId, partition_none a ha]
  · have h1' : sc.isEmpty = false := by cases sc <;> simp_all
    simp [splitScopeId, partition_some a sc ha, h1', h2]
  · simp [ipv6Init, ipv6InitStr, hs, bad a sc ha hsc, bind, Except.bind]

/-! ## Hextets -/

/-- A hex digit worth `k < 16`: `0-9`, then `a-f`, or `A-F` when `upper`. -/
def hexDigit (upper : Bool) (k : Nat) : Char :=
  if k < 10 then Char.ofNat (48 + k) else if upper then Char.ofNat (55 + k) else Char.ofNat (87 + k)

def hexDigitB (u : Bool) (k : Nat) : Bool := isHexC (hexDigit u k) && hexValC (hexDigit u k) == k

theorem hexDigitB_all : ∀ u : Bool, ∀ k, k < 16 → hexDigitB u k = true := by decide

theorem hexDigit_facts (u : Bool) (k : Nat) (h : k < 16) :
    isHexC (hexDigit u k) = true ∧ hexValC (hexDigit u k) = k := by
  have := hexDigitB_all u k h
  simp only [hexDigitB, Bool.and_eq_true, beq_iff_eq] at this
  exact this

theorem hexVal_digits (ds : List (Nat × Bool)) (hd : ∀ d ∈ ds, d.1 < 16) (a : Nat) :
    (ds.map fun d => hexDigit d.2 d.1).foldl (fun v c => v * 16 + hexValC c) a =
      ds.foldl (fun v d => v * 16 + d.1) a := by
  induction ds generalizing a with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [(hexDigit_facts d.2 d.1 (hd d (by simp))).2]
    exact ih (fun x hx => hd x (by simp [hx])) _

/-- `_parse_hextet`, ipaddress.py:1762-1786, docstring "Convert an IPv6 hextet string into an
integer ... Raises: ValueError: if the input isn't strictly a hex number from [0..FFFF]": every
spelling of one to four hex digits, each in either case and with any leading zeros, is read as its
base-16 value; a string with a character outside `0-9a-fA-F` raises 'Only hex digits permitted in
%r' (:1777-1778), five or more hex digits raise 'At most 4 characters permitted in %r'
(:1781-1783), and the empty string passes both checks and raises `int('', 16)`'s `ValueError`
(:1785). `hexMsg` holds the three messages. -/
def HextetSpec : Prop :=
  (∀ ds : List (Nat × Bool), 1 ≤ ds.length → ds.length ≤ 4 → (∀ d ∈ ds, d.1 < 16) →
    parseHextet (ds.map fun d => hexDigit d.2 d.1) = .ok (ds.foldl (fun v d => v * 16 + d.1) 0)) ∧
  (∀ s : List Char, (∃ c ∈ s, isHexC c = false) → parseHextet s = .error .nonHex) ∧
  (∀ s : List Char, s.all isHexC = true → 4 < s.length → parseHextet s = .error .tooLong) ∧
  parseHextet [] = .error .emptyLit

theorem hextetSpec_proven : HextetSpec := by
  refine ⟨fun ds h1 h4 hd => ?_, fun s ⟨c, hc, hx⟩ => ?_, fun s ha hl => ?_, rfl⟩
  · have hall : (ds.map fun d => hexDigit d.2 d.1).all isHexC = true := by
      simp only [List.all_map, List.all_eq_true, Function.comp_apply]
      intro d hm; exact (hexDigit_facts d.2 d.1 (hd d hm)).1
    have hne : (ds.map fun d => hexDigit d.2 d.1).isEmpty = false := by
      cases ds with
      | nil => simp at h1
      | cons _ _ => rfl
    have hl : ¬ (ds.map fun d => hexDigit d.2 d.1).length > 4 := by simp; omega
    simp only [parseHextet, hall, hne, hl, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hexVal]
    rw [hexVal_digits ds hd 0]
  · have : s.all isHexC = false := by
      rw [Bool.eq_false_iff]; intro h; rw [List.all_eq_true] at h; rw [h c hc] at hx; cases hx
    simp [parseHextet, this]
  · simp [parseHextet, ha, hl]

/-! ## Spellings `_ip_int_from_string` accepts -/

theorem parseHextet_good (h : List Char) (v : Nat) (hp : parseHextet h = .ok v) : HexGood h v := by
  unfold parseHextet at hp
  by_cases ha : h.all isHexC = true
  · by_cases hl : h.length > 4
    · simp [ha, hl] at hp
    · by_cases he : h.isEmpty = true
      · simp [ha, hl, he] at hp
      · simp only [ha, hl, he, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hp
        refine ⟨?_, ha, ?_, by omega, ?_⟩
        · simp [parseHextet, ha, hl, he, hp]
        · intro e; subst e; simp at he
        · intro e; subst e; rw [← hp]; rfl
  · simp [ha] at hp

theorem hexGood_parts (h : List Char) (v : Nat) (g : HexGood h v) :
    '.' ∉ h ∧ (h.all isHexC = true ∧ h.length ≤ 4) ∧ h ≠ [] := by
  obtain ⟨_, a, e, l, _⟩ := g
  exact ⟨not_mem_of_hex h a '.' (by decide), ⟨a, l⟩, e⟩

/-- `_ip_int_from_string`, ipaddress.py:1648-1760, on the spellings RFC 4291 2.2 allows: eight
hextets, each any spelling `_parse_hextet` reads (either case, leading zeros), are the address
whose groups they are, and so is `_compress_hextets` of them joined (a run of `'0'` replaced by
`::`); and six hextets followed by a dotted quad `IPv4Address` accepts (:1684-1690) put the quad's
32 bits in the low two groups. `combine vs 0 []` is the base-65536 number with digits `vs`. -/
def V6ParseSpellings : Prop :=
  (∀ (h0 h1 h2 h3 h4 h5 h6 h7 : List Char) (v0 v1 v2 v3 v4 v5 v6 v7 : Nat),
    parseHextet h0 = .ok v0 → parseHextet h1 = .ok v1 → parseHextet h2 = .ok v2 →
    parseHextet h3 = .ok v3 → parseHextet h4 = .ok v4 → parseHextet h5 = .ok v5 →
    parseHextet h6 = .ok v6 → parseHextet h7 = .ok v7 →
    ipIntFromString6 (joinOn1 ':' [h0, h1, h2, h3, h4, h5, h6, h7]) =
      .ok (combine [v0, v1, v2, v3, v4, v5, v6, v7] 0 []) ∧
    ipIntFromString6 (joinOn1 ':' (compressHextets [h0, h1, h2, h3, h4, h5, h6, h7])) =
      .ok (combine [v0, v1, v2, v3, v4, v5, v6, v7] 0 [])) ∧
  (∀ (h0 h1 h2 h3 h4 h5 q : List Char) (v0 v1 v2 v3 v4 v5 w : Nat),
    parseHextet h0 = .ok v0 → parseHextet h1 = .ok v1 → parseHextet h2 = .ok v2 →
    parseHextet h3 = .ok v3 → parseHextet h4 = .ok v4 → parseHextet h5 = .ok v5 →
    ipv4Init (.str q) = .ok w →
    ipIntFromString6 (joinOn1 ':' [h0, h1, h2, h3, h4, h5, q]) =
      .ok (combine [v0, v1, v2, v3, v4, v5, w / 65536, w % 65536] 0 []))

theorem v6ParseSpellings_proven : V6ParseSpellings := by
  refine ⟨fun h0 h1 h2 h3 h4 h5 h6 h7 v0 v1 v2 v3 v4 v5 v6 v7 p0 p1 p2 p3 p4 p5 p6 p7 => ?_,
    fun h0 h1 h2 h3 h4 h5 q v0 v1 v2 v3 v4 v5 w p0 p1 p2 p3 p4 p5 hq => ?_⟩
  · have G0 := parseHextet_good _ _ p0
    have G1 := parseHextet_good _ _ p1
    have G2 := parseHextet_good _ _ p2
    have G3 := parseHextet_good _ _ p3
    have G4 := parseHextet_good _ _ p4
    have G5 := parseHextet_good _ _ p5
    have G6 := parseHextet_good _ _ p6
    have G7 := parseHextet_good _ _ p7
    refine ⟨?_, compressed_parse _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G0 G1 G2 G3 G4 G5 G6 G7⟩
    obtain ⟨d0, k0, e0⟩ := hexGood_parts _ _ G0
    obtain ⟨d1, k1, e1⟩ := hexGood_parts _ _ G1
    obtain ⟨d2, k2, e2⟩ := hexGood_parts _ _ G2
    obtain ⟨d3, k3, e3⟩ := hexGood_parts _ _ G3
    obtain ⟨d4, k4, e4⟩ := hexGood_parts _ _ G4
    obtain ⟨d5, k5, e5⟩ := hexGood_parts _ _ G5
    obtain ⟨d6, k6, e6⟩ := hexGood_parts _ _ G6
    obtain ⟨d7, k7, e7⟩ := hexGood_parts _ _ G7
    refine parse_join _ ?_ (by simp) (by simp) _ ?_
    · repeat' (first | exact allHexGood_nil | refine allHexGood_cons _ _ ?_ ?_ | assumption)
    intro s hs he hl
    unfold ipIntFromString6
    simp [hs, he, hl, ipv6Suffix, ipv6Layout, ipv6Hextets, skipScan, p0, p1, p2, p3, p4, p5, p6, p7, d0, d1, d2, d3, d4, d5, d6, d7,
      e0, e1, e2, e3, e4, e5, e6, e7, parseHextets, head!_cons', Except.map]
    simp only [pure, Except.pure, Except.ok.injEq]
  · obtain ⟨hw, hqs⟩ := v4Canonical_proven q w hq
    subst hqs
    obtain ⟨qa, ql, qd⟩ := ipv4Str_facts w
    have hc : ':' ∉ ipv4Str w := quad_not _ qa ':' (by decide)
    have G0 := parseHextet_good _ _ p0
    have G1 := parseHextet_good _ _ p1
    have G2 := parseHextet_good _ _ p2
    have G3 := parseHextet_good _ _ p3
    have G4 := parseHextet_good _ _ p4
    have G5 := parseHextet_good _ _ p5
    obtain ⟨d0, ⟨a0, l0⟩, e0⟩ := hexGood_parts _ _ G0
    obtain ⟨d1, ⟨a1, l1⟩, e1⟩ := hexGood_parts _ _ G1
    obtain ⟨d2, ⟨a2, l2⟩, e2⟩ := hexGood_parts _ _ G2
    obtain ⟨d3, ⟨a3, l3⟩, e3⟩ := hexGood_parts _ _ G3
    obtain ⟨d4, ⟨a4, l4⟩, e4⟩ := hexGood_parts _ _ G4
    obtain ⟨d5, ⟨a5, l5⟩, e5⟩ := hexGood_parts _ _ G5
    obtain ⟨pa, -, ea, -, -⟩ := hexStr_facts (w / 65536 % 65536) (Nat.mod_lt _ (by decide))
    obtain ⟨pb, -, eb, -, -⟩ := hexStr_facts (w % 65536) (Nat.mod_lt _ (by decide))
    have hs := splitMax_join ':' [h0, h1, h2, h3, h4, h5, ipv4Str w] 9 (by simp) (by simp) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact not_mem_of_hex _ a0 ':' (by decide)
      · exact not_mem_of_hex _ a1 ':' (by decide)
      · exact not_mem_of_hex _ a2 ':' (by decide)
      · exact not_mem_of_hex _ a3 ':' (by decide)
      · exact not_mem_of_hex _ a4 ':' (by decide)
      · exact not_mem_of_hex _ a5 ':' (by decide)
      · exact hc)
    have hl : ¬ (joinOn1 ':' [h0, h1, h2, h3, h4, h5, ipv4Str w]).length > 45 := by
      simp [joinOn1]; omega
    have he : (joinOn1 ':' [h0, h1, h2, h3, h4, h5, ipv4Str w]).isEmpty = false := by
      simp [joinOn1]
    have hw1 : w / 65536 % 65536 = w / 65536 := Nat.mod_eq_of_lt (by omega)
    have hne1 : hexStr (w / 65536 % 65536) ≠ [] := ea
    have hne2 : hexStr (w % 65536) ≠ [] := eb
    have hv4 := v4RoundTrip_proven w hw
    generalize joinOn1 ':' [h0, h1, h2, h3, h4, h5, ipv4Str w] = s at hs hl he ⊢
    unfold ipIntFromString6
    simp [hs, he, hl, qd, hv4, ipv6Suffix, ipv6Layout, ipv6Hextets, skipScan, p0, p1, p2, p3, p4, p5, pa, pb, d0, d1, d2, d3, d4, d5,
      e0, e1, e2, e3, e4, e5, hne1, hne2, parseHextets, head!_cons', Except.map]
    simp only [pure, Except.pure, Except.ok.injEq, hw1]

end PyLean.Ipaddress
