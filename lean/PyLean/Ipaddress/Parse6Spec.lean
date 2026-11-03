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
  have hs : stringFromIpInt6Py .address (some ((ip >>> 32 : Nat) : Int)) =
      .ok (stringFromIpInt6 (ip / 2 ^ 32)) := by
    rw [shiftRight32]; exact stringFromIpInt6Py_nat .address _ (by omega)
  have hp := stringFromIpInt6Py_nat .address ip hip
  refine ⟨ipv4Mapped_eq ip, fun hq => ?_, fun hq => ?_⟩
  · have h1 : ipv4MappedToStr ip = .ok ("::ffff:".toList ++ ipv4Str (ip % 2 ^ 32)) := by
      simp only [ipv4MappedToStr, ipv4Mapped_eq, hq, ↓reduceIte, hs]
      simp only [bind, Except.bind, pure, Except.pure]
      rw [show (0xFFFF : Nat) = 65535 from rfl, ffff_str]
      rfl
    refine ⟨h1, fun sc => ?_⟩
    simp only [ipv6StrPy, ipv4Mapped_eq, hq, ↓reduceIte, h1, bind, Except.bind, pure, Except.pure]
  · refine ⟨by simp [ipv4MappedToStr, ipv4Mapped_eq, hq], fun sc => ?_⟩
    simp [ipv6StrPy, ipv4Mapped_eq, hq, hp, bind, Except.bind, pure, Except.pure]

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

/-- The uncompressed spellings and `_compress_hextets`' own (see `V6ParseSpellings`). -/
def V6ParseSpellingsBase : Prop :=
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

theorem v6ParseSpellingsBase_proven : V6ParseSpellingsBase := by
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

/-! ## `::` for any run, and before a dotted quad -/

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 4000000 in
/-- `_ip_int_from_string` of eight hextet spellings with the groups `[b, b + bl)` (`bl ≥ 1`, all
zero) replaced by `::`, written as `compress_shape` writes a run (an extra `''` at either end): the
36 shapes, one by one. -/
theorem run_parse (h0 h1 h2 h3 h4 h5 h6 h7 : List Char) (v0 v1 v2 v3 v4 v5 v6 v7 : Nat)
    (G0 : HexGood h0 v0) (G1 : HexGood h1 v1) (G2 : HexGood h2 v2) (G3 : HexGood h3 v3)
    (G4 : HexGood h4 v4) (G5 : HexGood h5 v5) (G6 : HexGood h6 v6) (G7 : HexGood h7 v7)
    (b bl : Nat) (hbl : 1 ≤ bl) (hb : b + bl ≤ 8)
    (hrun : ∀ i, b ≤ i → i < b + bl → [v0, v1, v2, v3, v4, v5, v6, v7][i]? = some 0) :
    ipIntFromString6 (joinOn1 ':' ((if b = 0 then [[]] else []) ++
      [h0, h1, h2, h3, h4, h5, h6, h7].take b ++ [[]] ++
      (if b + bl = 8 then [[]] else [h0, h1, h2, h3, h4, h5, h6, h7].drop (b + bl)))) =
      .ok (combine [v0, v1, v2, v3, v4, v5, v6, v7] 0 []) := by
  obtain ⟨p0, a0, e0, l0, -⟩ := G0
  obtain ⟨p1, a1, e1, l1, -⟩ := G1
  obtain ⟨p2, a2, e2, l2, -⟩ := G2
  obtain ⟨p3, a3, e3, l3, -⟩ := G3
  obtain ⟨p4, a4, e4, l4, -⟩ := G4
  obtain ⟨p5, a5, e5, l5, -⟩ := G5
  obtain ⟨p6, a6, e6, l6, -⟩ := G6
  obtain ⟨p7, a7, e7, l7, -⟩ := G7
  have d0 := not_mem_of_hex h0 a0 '.' (by decide)
  have d1 := not_mem_of_hex h1 a1 '.' (by decide)
  have d2 := not_mem_of_hex h2 a2 '.' (by decide)
  have d3 := not_mem_of_hex h3 a3 '.' (by decide)
  have d4 := not_mem_of_hex h4 a4 '.' (by decide)
  have d5 := not_mem_of_hex h5 a5 '.' (by decide)
  have d6 := not_mem_of_hex h6 a6 '.' (by decide)
  have d7 := not_mem_of_hex h7 a7 '.' (by decide)
  have k0 : h0.all isHexC = true ∧ h0.length ≤ 4 := ⟨a0, l0⟩
  have k1 : h1.all isHexC = true ∧ h1.length ≤ 4 := ⟨a1, l1⟩
  have k2 : h2.all isHexC = true ∧ h2.length ≤ 4 := ⟨a2, l2⟩
  have k3 : h3.all isHexC = true ∧ h3.length ≤ 4 := ⟨a3, l3⟩
  have k4 : h4.all isHexC = true ∧ h4.length ≤ 4 := ⟨a4, l4⟩
  have k5 : h5.all isHexC = true ∧ h5.length ≤ 4 := ⟨a5, l5⟩
  have k6 : h6.all isHexC = true ∧ h6.length ≤ 4 := ⟨a6, l6⟩
  have k7 : h7.all isHexC = true ∧ h7.length ≤ 4 := ⟨a7, l7⟩
  have knil : ([] : List Char).all isHexC = true ∧ ([] : List Char).length ≤ 4 := ⟨rfl, by decide⟩
  have y0 : b ≤ 0 → 0 < b + bl → v0 = 0 := fun x y => by simpa using hrun 0 x y
  have y1 : b ≤ 1 → 1 < b + bl → v1 = 0 := fun x y => by simpa using hrun 1 x y
  have y2 : b ≤ 2 → 2 < b + bl → v2 = 0 := fun x y => by simpa using hrun 2 x y
  have y3 : b ≤ 3 → 3 < b + bl → v3 = 0 := fun x y => by simpa using hrun 3 x y
  have y4 : b ≤ 4 → 4 < b + bl → v4 = 0 := fun x y => by simpa using hrun 4 x y
  have y5 : b ≤ 5 → 5 < b + bl → v5 = 0 := fun x y => by simpa using hrun 5 x y
  have y6 : b ≤ 6 → 6 < b + bl → v6 = 0 := fun x y => by simpa using hrun 6 x y
  have y7 : b ≤ 7 → 7 < b + bl → v7 = 0 := fun x y => by simpa using hrun 7 x y
  clear hrun
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by omega
  all_goals
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
        bl = 1 ∨ bl = 2 ∨ bl = 3 ∨ bl = 4 ∨ bl = 5 ∨ bl = 6 ∨ bl = 7 ∨ bl = 8 := by omega
  all_goals try (exfalso; omega)
  all_goals
    simp (failIfUnchanged := false) only [Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceAdd, Nat.le_refl,
      Nat.zero_le, false_implies, true_implies, Nat.not_succ_le_zero, Nat.lt_irrefl] at y0 y1 y2 y3 y4 y5 y6 y7
    subst_vars
  all_goals
    simp only [Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte, List.take_succ_cons, List.take_zero,
      List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.cons_append,
      List.nil_append, List.append_nil]
    refine parse_join _ ?_ (by simp) (by simp) _ ?_
    · repeat' (first | exact allHexGood_nil | refine allHexGood_cons _ _ ?_ ?_ | assumption)
    intro s hs he hl
    unfold ipIntFromString6
    simp [hs, he, hl, ipv6Suffix, ipv6Layout, ipv6Hextets, skipScan, p0, p1, p2, p3, p4, p5, p6, p7, d0, d1, d2, d3, d4, d5, d6, d7,
      e0, e1, e2, e3, e4, e5, e6, e7, parseHextets, head!_cons', Except.map]
    simp only [pure, Except.pure, Except.ok.injEq]
    rw [combine_zeros]
    rfl

theorem noColon_nil : ∀ p ∈ ([] : List (List Char)), ':' ∉ p := by simp

theorem noColon_cons (p : List Char) (l : List (List Char)) (h : ':' ∉ p) (t : ∀ q ∈ l, ':' ∉ q) :
    ∀ q ∈ p :: l, ':' ∉ q := by
  intro q hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · exact h
  · exact t q hq

/-- `parse_join` for parts holding no `:`, such as a dotted quad. -/
theorem parse_join4 (P : List (List Char)) (hC : ∀ p ∈ P, ':' ∉ p) (h2 : 2 ≤ P.length)
    (h9 : P.length ≤ 10) (hlen : (joinOn1 ':' P).length ≤ 45) (r : Py Nat)
    (H : ∀ s, splitMax ':' 9 s = P → s.isEmpty = false → ¬ s.length > 45 → ipIntFromString6 s = r) :
    ipIntFromString6 (joinOn1 ':' P) = r := by
  have hne : P ≠ [] := by intro e; subst e; simp at h2
  refine H _ (splitMax_join ':' P 9 hne (by omega) hC) ?_ (by omega)
  match P, h2 with
  | p :: q :: qs, _ => simp [joinOn1]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 4000000 in
/-- `_ip_int_from_string` of six hextet spellings with the groups `[b, b + bl)` (`bl ≥ 1`, all
zero) replaced by `::`, then a dotted quad that `IPv4Address` reads (:1684-1690): the 21 shapes,
one by one. -/
theorem run_parse4 (h0 h1 h2 h3 h4 h5 q : List Char) (v0 v1 v2 v3 v4 v5 w : Nat)
    (G0 : HexGood h0 v0) (G1 : HexGood h1 v1) (G2 : HexGood h2 v2) (G3 : HexGood h3 v3)
    (G4 : HexGood h4 v4) (G5 : HexGood h5 v5) (hq : ipv4Init (.str q) = .ok w)
    (b bl : Nat) (hbl : 1 ≤ bl) (hb : b + bl ≤ 6)
    (hrun : ∀ i, b ≤ i → i < b + bl → [v0, v1, v2, v3, v4, v5][i]? = some 0) :
    ipIntFromString6 (joinOn1 ':' ((if b = 0 then [[]] else []) ++ [h0, h1, h2, h3, h4, h5].take b ++
      [[]] ++ [h0, h1, h2, h3, h4, h5].drop (b + bl) ++ [q])) =
      .ok (combine [v0, v1, v2, v3, v4, v5, w / 65536, w % 65536] 0 []) := by
  obtain ⟨hw, hqs⟩ := v4Canonical_proven q w hq
  subst hqs
  obtain ⟨qa, ql, qd⟩ := ipv4Str_facts w
  have hc : ':' ∉ ipv4Str w := quad_not _ qa ':' (by decide)
  obtain ⟨p0, a0, e0, l0, -⟩ := G0
  obtain ⟨p1, a1, e1, l1, -⟩ := G1
  obtain ⟨p2, a2, e2, l2, -⟩ := G2
  obtain ⟨p3, a3, e3, l3, -⟩ := G3
  obtain ⟨p4, a4, e4, l4, -⟩ := G4
  obtain ⟨p5, a5, e5, l5, -⟩ := G5
  have d0 := not_mem_of_hex h0 a0 '.' (by decide)
  have d1 := not_mem_of_hex h1 a1 '.' (by decide)
  have d2 := not_mem_of_hex h2 a2 '.' (by decide)
  have d3 := not_mem_of_hex h3 a3 '.' (by decide)
  have d4 := not_mem_of_hex h4 a4 '.' (by decide)
  have d5 := not_mem_of_hex h5 a5 '.' (by decide)
  have c0 := not_mem_of_hex h0 a0 ':' (by decide)
  have c1 := not_mem_of_hex h1 a1 ':' (by decide)
  have c2 := not_mem_of_hex h2 a2 ':' (by decide)
  have c3 := not_mem_of_hex h3 a3 ':' (by decide)
  have c4 := not_mem_of_hex h4 a4 ':' (by decide)
  have c5 := not_mem_of_hex h5 a5 ':' (by decide)
  have cnil : ':' ∉ ([] : List Char) := by simp
  obtain ⟨pa, -, ea, -, -⟩ := hexStr_facts (w / 65536 % 65536) (Nat.mod_lt _ (by decide))
  obtain ⟨pb, -, eb, -, -⟩ := hexStr_facts (w % 65536) (Nat.mod_lt _ (by decide))
  have hw1 : w / 65536 % 65536 = w / 65536 := Nat.mod_eq_of_lt (by omega)
  have hv4 := v4RoundTrip_proven w hw
  have y0 : b ≤ 0 → 0 < b + bl → v0 = 0 := fun x y => by simpa using hrun 0 x y
  have y1 : b ≤ 1 → 1 < b + bl → v1 = 0 := fun x y => by simpa using hrun 1 x y
  have y2 : b ≤ 2 → 2 < b + bl → v2 = 0 := fun x y => by simpa using hrun 2 x y
  have y3 : b ≤ 3 → 3 < b + bl → v3 = 0 := fun x y => by simpa using hrun 3 x y
  have y4 : b ≤ 4 → 4 < b + bl → v4 = 0 := fun x y => by simpa using hrun 4 x y
  have y5 : b ≤ 5 → 5 < b + bl → v5 = 0 := fun x y => by simpa using hrun 5 x y
  clear hrun
  obtain rfl | rfl | rfl | rfl | rfl | rfl : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 := by omega
  all_goals
    obtain rfl | rfl | rfl | rfl | rfl | rfl : bl = 1 ∨ bl = 2 ∨ bl = 3 ∨ bl = 4 ∨ bl = 5 ∨ bl = 6 := by
      omega
  all_goals try (exfalso; omega)
  all_goals
    simp (failIfUnchanged := false) only [Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceAdd, Nat.le_refl,
      Nat.zero_le, false_implies, true_implies, Nat.not_succ_le_zero, Nat.lt_irrefl] at y0 y1 y2 y3 y4 y5
    subst_vars
  all_goals
    simp only [Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte, List.take_succ_cons, List.take_zero,
      List.drop_succ_cons, List.drop_zero, List.drop_nil, List.cons_append, List.nil_append,
      List.append_nil]
    refine parse_join4 _ ?_ (by simp) (by simp) (by simp [joinOn1]; omega) _ ?_
    · repeat' (first | exact noColon_nil | refine noColon_cons _ _ ?_ ?_ | assumption)
    intro s hs he hl
    unfold ipIntFromString6
    simp [hs, he, hl, qd, hv4, ipv6Suffix, ipv6Layout, ipv6Hextets, skipScan, p0, p1, p2, p3, p4, p5,
      pa, pb, d0, d1, d2, d3, d4, d5, e0, e1, e2, e3, e4, e5, ea, eb, parseHextets, head!_cons',
      Except.map]
    simp only [pure, Except.pure, Except.ok.injEq, hw1]
    rw [combine_zeros]
    rfl

/-- `_ip_int_from_string`, ipaddress.py:1648-1760, on every spelling RFC 4291 2.2 allows (the forms
the ipaddress docs accept). (1) Eight hextets, each any spelling `_parse_hextet` reads (either
case, leading zeros), are the address whose groups they are, and so is `_compress_hextets` of
them joined. (2) Any run of one or more groups, all zero, may be replaced by `::`, wherever it is
and however long: `'1:2:3:4:5:6::8'` (one group), `'1::2:0:0:0:3'` (not the longest run),
`'::2:3:4:5:6:7:8'`, `'1:2:3:4:5:6:7::'`, `'::'`; the result has the written groups in place and
zeros in the run (:1712-1728, :1747-1758). (3) Six groups, written out or with a run replaced by
`::`, followed by a dotted quad `IPv4Address` accepts (:1684-1690) put the quad's 32 bits in the
low two groups, whatever the high 96 bits (`'::13.1.68.3'`, RFC 4291 2.2's own example, and
`'::ffff:129.144.52.38'` alike). With `V6ParseRefusals`, which says exactly when and how every
other string is refused, the parser is pinned on every string. `combine vs 0 []` is the
base-65536 number with digits `vs`. -/
def V6ParseSpellings : Prop :=
  V6ParseSpellingsBase ∧
  (∀ (h0 h1 h2 h3 h4 h5 h6 h7 : List Char) (v0 v1 v2 v3 v4 v5 v6 v7 : Nat),
    parseHextet h0 = .ok v0 → parseHextet h1 = .ok v1 → parseHextet h2 = .ok v2 →
    parseHextet h3 = .ok v3 → parseHextet h4 = .ok v4 → parseHextet h5 = .ok v5 →
    parseHextet h6 = .ok v6 → parseHextet h7 = .ok v7 →
    ∀ b bl : Nat, 1 ≤ bl → b + bl ≤ 8 →
      (∀ i, b ≤ i → i < b + bl → [v0, v1, v2, v3, v4, v5, v6, v7][i]? = some 0) →
      ipIntFromString6 (joinOn1 ':' ((if b = 0 then [[]] else []) ++
        [h0, h1, h2, h3, h4, h5, h6, h7].take b ++ [[]] ++
        (if b + bl = 8 then [[]] else [h0, h1, h2, h3, h4, h5, h6, h7].drop (b + bl)))) =
        .ok (combine [v0, v1, v2, v3, v4, v5, v6, v7] 0 [])) ∧
  (∀ (h0 h1 h2 h3 h4 h5 q : List Char) (v0 v1 v2 v3 v4 v5 w : Nat),
    parseHextet h0 = .ok v0 → parseHextet h1 = .ok v1 → parseHextet h2 = .ok v2 →
    parseHextet h3 = .ok v3 → parseHextet h4 = .ok v4 → parseHextet h5 = .ok v5 →
    ipv4Init (.str q) = .ok w →
    ∀ b bl : Nat, 1 ≤ bl → b + bl ≤ 6 →
      (∀ i, b ≤ i → i < b + bl → [v0, v1, v2, v3, v4, v5][i]? = some 0) →
      ipIntFromString6 (joinOn1 ':' ((if b = 0 then [[]] else []) ++ [h0, h1, h2, h3, h4, h5].take b ++
        [[]] ++ [h0, h1, h2, h3, h4, h5].drop (b + bl) ++ [q])) =
        .ok (combine [v0, v1, v2, v3, v4, v5, w / 65536, w % 65536] 0 []))

theorem v6ParseSpellings_proven : V6ParseSpellings :=
  ⟨v6ParseSpellingsBase_proven,
   fun h0 h1 h2 h3 h4 h5 h6 h7 v0 v1 v2 v3 v4 v5 v6 v7 p0 p1 p2 p3 p4 p5 p6 p7 b bl hbl hb hrun =>
    run_parse h0 h1 h2 h3 h4 h5 h6 h7 v0 v1 v2 v3 v4 v5 v6 v7 (parseHextet_good _ _ p0)
      (parseHextet_good _ _ p1) (parseHextet_good _ _ p2) (parseHextet_good _ _ p3)
      (parseHextet_good _ _ p4) (parseHextet_good _ _ p5) (parseHextet_good _ _ p6)
      (parseHextet_good _ _ p7) b bl hbl hb hrun,
   fun h0 h1 h2 h3 h4 h5 q v0 v1 v2 v3 v4 v5 w p0 p1 p2 p3 p4 p5 hq b bl hbl hb hrun =>
    run_parse4 h0 h1 h2 h3 h4 h5 q v0 v1 v2 v3 v4 v5 w (parseHextet_good _ _ p0)
      (parseHextet_good _ _ p1) (parseHextet_good _ _ p2) (parseHextet_good _ _ p3)
      (parseHextet_good _ _ p4) (parseHextet_good _ _ p5) hq b bl hbl hb hrun⟩

/-! ## `IPv6Address.__init__` on a str -/

theorem span_loop_eq (p : Char → Bool) : ∀ (s acc : List Char),
    (List.span.loop p s acc).1 ++ (List.span.loop p s acc).2 = acc.reverse ++ s := by
  intro s
  induction s with
  | nil => intro acc; simp [List.span.loop]
  | cons c s ih =>
    intro acc
    simp only [List.span.loop]
    cases hc : p c
    · rfl
    · show (List.span.loop p s (c :: acc)).1 ++ (List.span.loop p s (c :: acc)).2 = acc.reverse ++ c :: s
      rw [ih]
      simp

/-- `str.partition('%')` with a separator: the string is the head, one character, and the tail. -/
theorem partition_true (s a b : List Char) (h : partitionPct s = (a, true, b)) :
    ∃ c, s = a ++ c :: b := by
  unfold partitionPct List.span at h
  have he := span_loop_eq (fun x => decide (x ≠ '%')) s []
  revert h he
  generalize List.span.loop (fun x => decide (x ≠ '%')) s [] = r
  intro h he
  obtain ⟨t, d⟩ := r
  cases d with
  | nil =>
    have h' : (t, false, ([] : List Char)) = (a, true, b) := h
    simp at h'
  | cons c b' =>
    have h' : (t, true, b') = (a, true, b) := h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, -, rfl⟩ := h'
    exact ⟨c, by simpa using he.symm⟩

/-- `IPv6Address.__init__` for a str, ipaddress.py:1952-1959: a string holding `/` is refused first
(:1955-1956), with `AddressValueError("Unexpected '/' in %r")`, before the scope id is split off
(:1957), so `'::1%a/b'` is refused rather than stored with the scope id `'a/b'`. So the scope id an
address stores is `None` or a non-empty string without `%` or `/`, which is what lets `str()` of an
address, a `/` and a prefix length be read back as a network (`address_exclude`, :837-838). -/
def V6InitStr : Prop :=
  (∀ s : List Char, '/' ∈ s → ipv6Init (.str s) = .error (avMsg "Unexpected '/' in " s)) ∧
  (∀ (s : List Char) (ip : Nat) (sc : Option (List Char)), ipv6Init (.str s) = .ok (ip, sc) →
    sc = none ∨ ∃ t, sc = some t ∧ t ≠ [] ∧ '%' ∉ t ∧ '/' ∉ t)

theorem v6InitStr_proven : V6InitStr := by
  have slash : ∀ s : List Char, '/' ∈ s → ipv6Init (.str s) = .error (avMsg "Unexpected '/' in " s) := by
    intro s h
    simp only [ipv6Init, ipv6InitStr, h, ↓reduceIte] <;> rfl
  refine ⟨slash, fun s ip sc h => ?_⟩
  by_cases hsl : '/' ∈ s
  · rw [slash s hsl] at h; cases h
  · cases hsp : splitScopeId s with
    | error e =>
      simp [ipv6Init, ipv6InitStr, hsl, hsp, bind, Except.bind] at h
    | ok r =>
      obtain ⟨addr, scope⟩ := r
      have hsc : scope = sc := by
        cases hip : ipIntFromString6 addr with
        | error e => simp [ipv6Init, ipv6InitStr, hsl, hsp, hip, bind, Except.bind] at h
        | ok v =>
          simp [ipv6Init, ipv6InitStr, hsl, hsp, hip, bind, Except.bind, pure, Except.pure] at h
          exact h.2
      subst hsc
      unfold splitScopeId at hsp
      rcases hpp : partitionPct s with ⟨a, sep, x⟩
      rw [hpp] at hsp
      cases sep with
      | false =>
        left
        simp at hsp
        obtain ⟨-, h2⟩ := hsp
        first | exact h2.symm | exact h2
      | true =>
        by_cases hx : x.isEmpty = true ∨ '%' ∈ x
        · have hx' : x = [] ∨ '%' ∈ x := by
            rcases hx with h | h
            · left; cases x <;> simp_all
            · right; exact h
          simp [hx'] at hsp
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hx, Except.ok.injEq,
            Prod.mk.injEq] at hsp
          obtain ⟨-, rfl⟩ := hsp
          right
          refine ⟨x, rfl, ?_, ?_, ?_⟩
          · intro e; subst e; exact hx (Or.inl rfl)
          · intro e; exact hx (Or.inr e)
          · intro e
            obtain ⟨c, hs⟩ := partition_true s a x hpp
            exact hsl (by rw [hs]; simp [e])

end PyLean.Ipaddress
