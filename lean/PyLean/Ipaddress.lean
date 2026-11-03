import PyLean.Registry
import PyLean.Ipaddress.Model
import PyLean.Ipaddress.Spec
import PyLean.Ipaddress.Validation
import PyLean.Ipaddress.Lookup
import PyLean.Ipaddress.Summarize
import PyLean.Ipaddress.Subnets
import PyLean.Ipaddress.Exploded
import PyLean.Ipaddress.Parse4Props
import PyLean.Ipaddress.Hosts
import PyLean.Ipaddress.Mask4
import PyLean.Ipaddress.Parse6Props
import PyLean.Ipaddress.Parse6Spec
import PyLean.Ipaddress.Parse6Errors
import PyLean.Ipaddress.Compress6

/-!
`Lib/ipaddress.py`, CPython 3.15.2. The model covers the integer core of networks and their
operations on addresses, networks and other objects (`Operand`), `exploded` of IPv6 objects,
`is_unspecified` of interfaces, masks, and IPv4 and IPv6 text: parsing, refusals, formatting and
the address constructors.
-/

namespace PyLean.Ipaddress

open PyLean.Registry

/-- `_ip_int_from_prefix`, ipaddress.py:424-434, docstring "Turn the prefix length into a bitwise
netmask": for a prefix length `p <= max_prefixlen` (the documented argument) the netmask is `p`
ones followed by `max_prefixlen - p` zeros. -/
def IpIntFromPrefixSpec : Prop :=
  ∀ bits p : Nat, p ≤ bits → ipIntFromPrefix bits p = (2 ^ p - 1) <<< (bits - p)

theorem ipIntFromPrefixSpec_proven : IpIntFromPrefixSpec := ipIntFromPrefix_eq

def entries : List Entry := [
  { id := "ipaddress-subnets-validation", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseNetwork.subnets"]
    statement := "subnets raises ValueError for new_prefix shorter than the current prefix, for both arguments set, and for a negative or too-large prefixlen_diff."
    source := "subnets docstring, Lib/ipaddress.py:940-946", status := .refuted
    prop := ``SubnetsRejectsInvalidArgs, thm := some ``subnetsRejectsInvalidArgs_refuted
    bug := some "ipaddress-subnets-host-network-skips-validation"
    notes := "A /32 or /128 network yields itself before any argument is checked." },
  { id := "ipaddress-subnets-args", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseNetwork.subnets"]
    statement := "A network of one address yields itself for any arguments; otherwise new_prefix shorter than the prefix, new_prefix with prefixlen_diff != 1, a negative prefixlen_diff and a new prefix past max_prefixlen raise ValueError with the source's messages, and new_prefix=k equals prefixlen_diff=k-prefixlen."
    source := "subnets docstring, Lib/ipaddress.py:922-948; code :949-966", status := .proven
    prop := ``SubnetsArgs, thm := some ``subnetsArgs_proven
    notes := "With ipaddress-subnets-partition (valid prefixlen_diff) every argument is covered." },
  { id := "ipaddress-supernet-validation", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseNetwork.supernet"]
    statement := "supernet raises ValueError for new_prefix longer than the current prefix, for both arguments set, and when prefixlen - prefixlen_diff < 0."
    source := "supernet docstring, Lib/ipaddress.py:987-994", status := .refuted
    prop := ``SupernetRejectsInvalidArgs, thm := some ``supernetRejectsInvalidArgs_refuted
    bug := some "ipaddress-supernet-zero-prefix-skips-validation"
    notes := "A /0 network returns itself before any argument is checked." },
  { id := "ipaddress-supernet-args", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseNetwork.supernet"]
    statement := "A /0 network returns itself for any arguments; otherwise new_prefix longer than the prefix and new_prefix with prefixlen_diff != 1 raise ValueError, new_prefix=k equals prefixlen_diff=prefixlen-k, a prefixlen_diff past the prefix raises ValueError naming both, and a negative one raises ValueError('negative shift count')."
    source := "supernet docstring, Lib/ipaddress.py:975-995; code :996-1013", status := .proven
    prop := ``SupernetArgs, thm := some ``supernetArgs_proven
    notes := "With ipaddress-supernet-contains (0 <= prefixlen_diff <= prefixlen) every argument is covered." },
  { id := "ipaddress-getitem-sequence", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseNetwork.__getitem__"]
    statement := "net[i] returns addr + i mod size for -size <= i < size and raises IndexError otherwise."
    source := "invariant: sequence indexing", status := .proven
    prop := ``GetitemSequence, thm := some ``getitemSequence_proven },
  { id := "ipaddress-contains-mem", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseNetwork.__contains__"]
    statement := "address in net holds exactly for the addresses of the block; an address of the other version and any network are not in it; an object without version raises AttributeError."
    source := "invariant; comment at Lib/ipaddress.py:732", status := .proven
    prop := ``ContainsMem, thm := some ``containsMem_proven },
  { id := "ipaddress-overlaps-share", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseNetwork.overlaps", "_BaseNetwork.__contains__"]
    statement := "a.overlaps(b) holds exactly when the blocks share an address for b of the same version, is False for b of the other version, and raises TypeError for an address or a non-container."
    source := "overlaps docstring, Lib/ipaddress.py:744", status := .proven
    prop := ``OverlapsShareAddress, thm := some ``overlapsShareAddress_proven },
  { id := "ipaddress-subnet-of-mem", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseNetwork.subnet_of", "_BaseNetwork._is_subnet_of"]
    statement := "a.subnet_of(b) holds exactly when every address of a is in b for a network b of the same version; another version, an address or an object without version raise TypeError."
    source := "subnet_of docstring, Lib/ipaddress.py:1040; code :1028-1037", status := .proven
    prop := ``SubnetOfMem, thm := some ``subnetOfMem_proven },
  { id := "ipaddress-summarize-exact-cover", pyFile := "Lib/ipaddress.py"
    pyFns := ["summarize_address_range", "_count_righthand_zero_bits"]
    statement := "For addresses first <= last of one version, summarize_address_range returns valid networks, each the largest aligned block starting where the previous one ended and not passing last (a list Greedy admits only one of)."
    source := "summarize_address_range docstring and doctest, Lib/ipaddress.py:198-229", status := .proven
    prop := ``SummarizeExactCover, thm := some ``summarizeExactCover_proven
    notes := "greedy_unique: the conditions fix the list. Difftest fn summarize (addresses of both versions, networks, ints): 100%." },
  { id := "ipaddress-summarize-rejects", pyFile := "Lib/ipaddress.py"
    pyFns := ["summarize_address_range"]
    statement := "summarize_address_range raises TypeError for a non-address argument and for two versions, ValueError when first > last, and ValueError('unknown IP version') for a version other than 4 and 6."
    source := "summarize_address_range docstring Raise list, Lib/ipaddress.py:214-221; code :223-237", status := .proven
    prop := ``SummarizeRejects, thm := some ``summarizeRejects_proven },
  { id := "ipaddress-crzb-exact", pyFile := "Lib/ipaddress.py"
    pyFns := ["_count_righthand_zero_bits"]
    statement := "_count_righthand_zero_bits(n, bits) is bits for 0 and otherwise the number of trailing zero bits of n, capped at bits."
    source := "_count_righthand_zero_bits docstring, Lib/ipaddress.py:182-191", status := .proven
    prop := ``CrzbExact, thm := some ``crzbExact_proven },
  { id := "ipaddress-subnets-partition", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseNetwork.subnets"]
    statement := "For a valid prefixlen_diff, subnets returns 2^diff valid networks of the new prefix that tile the network in order."
    source := "subnets docstring, Lib/ipaddress.py:922-948", status := .proven
    prop := ``SubnetsPartition, thm := some ``subnetsPartition_proven },
  { id := "ipaddress-supernet-contains", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseNetwork.supernet"]
    statement := "For 0 <= diff <= prefixlen, supernet returns a valid network of prefix prefixlen - diff containing self."
    source := "supernet docstring, Lib/ipaddress.py:975-995", status := .proven
    prop := ``SupernetContains, thm := some ``supernetContains_proven },
  { id := "ipaddress-address-exclude-partition", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseNetwork.address_exclude", "_BaseNetwork.subnets", "_BaseNetwork.subnet_of",
      "_BaseNetwork._is_subnet_of"]
    statement := "For a network o of the same version inside s, address_exclude yields, for each prefix length from s.prefixlen+1 to o.prefixlen in that order, the block of that length next to the one holding o, and these cover s minus o once; an o outside s raises ValueError; another version, an address or an object without version raise TypeError or AttributeError."
    source := "address_exclude docstring, Lib/ipaddress.py:789-822, and its doctest in Doc/library/ipaddress.rst", status := .proven
    prop := ``AddressExcludePartition, thm := some ``addressExcludePartition_proven
    notes := "The docstring's example lists the blocks in ascending order; the code and the rst doctest yield them largest first, which is what is stated." },
  { id := "ipaddress-exploded-total", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseV6._explode_shorthand_ip_string"]
    statement := "exploded succeeds on every IPv6 address, interface and network the constructors accept."
    source := "exploded, Lib/ipaddress.py:386-389: a property with no failure mode, as compressed and str()", status := .refuted
    prop := ``ExplodedTotal, thm := some ``explodedTotal_refuted
    bug := some "ipaddress-exploded-scoped-network-raises"
    notes := "gh-88178 fixed IPv6Address and IPv6Interface in 3.15; IPv6Network still re-parses str(network_address), scope id included." },
  { id := "ipaddress-exploded-keeps-suffix", pyFile := "Lib/ipaddress.py"
    pyFns := ["IPv6Address._explode_shorthand_ip_string", "_BaseV6._explode_shorthand_ip_string"]
    statement := "exploded of an IPv6 interface ends in /prefixlen, and of a scoped IPv6 address in %scope, as compressed does."
    source := "invariant: exploded and compressed are two spellings of one object", status := .refuted
    prop := ``ExplodedKeepsSuffix, thm := some ``explodedKeepsSuffix_refuted
    bug := some "ipaddress-exploded-ipv4-mapped-truncates"
    notes := "IPv6Address._explode_shorthand_ip_string keeps 30 characters of the base result, which cuts off everything after the sixth group." },
  { id := "ipaddress-exploded-by-case", pyFile := "Lib/ipaddress.py"
    pyFns := ["IPv6Address._explode_shorthand_ip_string", "_BaseV6._explode_shorthand_ip_string",
      "_BaseV6._ip_int_from_string", "_BaseV6._string_from_ip_int", "IPv6Address.__str__"]
    statement := "For every 128-bit address, exploded of an unscoped network and of any address or interface outside ::ffff:0:0/96 is the eight hextets with the prefix and scope id; of an IPv4-mapped address or interface it is the first 30 characters of that and a dotted quad."
    source := "Lib/ipaddress.py:1861-1884, :1961-1966", status := .proven
    prop := ``ExplodedByCase, thm := some ``explodedByCase_proven
    notes := "The re-parse of :1875 is modelled (ipIntFromString6). The two refuted entries above are the cases this one sets aside or describes as they are." },
  { id := "ipaddress-exploded-hextets", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseV6._explode_shorthand_ip_string"]
    statement := "For every 128-bit ip, the eight hextets exploded prints, read as a base-65536 number, are ip."
    source := "invariant: exploded names the same address", status := .proven
    prop := ``HextetsRecompose, thm := some ``hextetsRecompose_proven },
  { id := "ipaddress-iface-unspecified", pyFile := "Lib/ipaddress.py"
    pyFns := ["IPv4Interface.is_unspecified", "IPv6Interface.is_unspecified"]
    statement := "An IPv4 or IPv6 interface is unspecified exactly when its address is zero and its prefix is the full length."
    source := "Lib/ipaddress.py:1479-1481, :2273-2275; _BaseNetwork.is_unspecified docstring, :1099-1106", status := .proven
    prop := ``IfaceUnspecified, thm := some ``ifaceUnspecified_proven },
  { id := "ipaddress-v4-text-roundtrip", pyFile := "Lib/ipaddress.py"
    pyFns := ["IPv4Address.__init__", "_BaseV4._ip_int_from_string", "_BaseV4._parse_octet",
      "_BaseV4._string_from_ip_int", "_BaseAddress.__str__"]
    statement := "For every n in [0, 2**32), IPv4Address(str(IPv4Address(n))) stores n."
    source := "docs: IPv4Address(int(IPv4Address('192.0.2.1'))) == IPv4Address('192.0.2.1'); invariant: str round-trips", status := .proven
    prop := ``V4RoundTrip, thm := some ``v4RoundTrip_proven
    notes := "Difftest fn v4init (strings, ints, bytes, exact messages)." },
  { id := "ipaddress-v4-text-canonical", pyFile := "Lib/ipaddress.py"
    pyFns := ["IPv4Address.__init__", "_BaseV4._ip_int_from_string", "_BaseV4._parse_octet",
      "_BaseV4._string_from_ip_int", "_BaseAddress.__str__"]
    statement := "For every string s that IPv4Address accepts, the address is below 2**32 and str of it is s: the parser accepts exactly one spelling per address."
    source := "ipaddress.py:1229-1230, leading zeros rejected 'as strict as glibc's inet_pton()' (bpo-36384)", status := .proven
    prop := ``V4Canonical, thm := some ``v4Canonical_proven
    notes := "Smoke-tested on 300k random strings over digits, dots, spaces, signs and non-ASCII digits." },
  { id := "ipaddress-v4-str-refusals", pyFile := "Lib/ipaddress.py"
    pyFns := ["IPv4Address.__init__", "_BaseV4._ip_int_from_string", "_BaseV4._parse_octet"]
    statement := "IPv4Address(s) for a str s stores an int or raises AddressValueError, never another class, with the message of the first failed check: '/', empty, not four parts, then the first octet _parse_octet refuses ('<message> in <repr>')."
    source := "IPv4Address docstring Raises, Lib/ipaddress.py:1281-1282; ip_address relies on the class, :41-49", status := .proven
    prop := ``V4StrRefusals, thm := some ``v4StrRefusals_proven },
  { id := "ipaddress-v4-parse-octet", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseV4._parse_octet"]
    statement := "_parse_octet refuses the empty string, a non-ASCII-digit character, more than three digits, a leading zero and a value above 255, in that order, and reads every other string as its decimal value."
    source := "_parse_octet docstring, Lib/ipaddress.py:1207-1218; code :1219-1239", status := .proven
    prop := ``ParseOctetSpec, thm := some ``parseOctetSpec_proven },
  { id := "ipaddress-v4-init-int-bytes", pyFile := "Lib/ipaddress.py"
    pyFns := ["IPv4Address.__init__", "_IPAddressBase._check_int_address", "_IPAddressBase._check_packed_address"]
    statement := "IPv4Address(int) accepts exactly [0, 2**32) and stores the int, otherwise AddressValueError naming the int and the bound; four big-endian bytes give the int back, any other length raises AddressValueError with the bytes' repr and both lengths."
    source := "IPv4Address docstring, ipaddress.py:1271-1284; _check_int_address and _check_packed_address", status := .proven
    prop := ``V4InitIntBytes, thm := some ``v4InitIntBytes_proven },
  { id := "ipaddress-v6-init-int-bytes", pyFile := "Lib/ipaddress.py"
    pyFns := ["IPv6Address.__init__", "_IPAddressBase._check_int_address", "_IPAddressBase._check_packed_address"]
    statement := "IPv6Address(int) accepts exactly [0, 2**128) and stores the int with no scope id, otherwise AddressValueError naming the int and the bound; sixteen bytes are read big-endian, so n.to_bytes(16, 'big') gives n back, and any other length raises AddressValueError with the bytes' repr and both lengths."
    source := "IPv6Address docstring, ipaddress.py:1924-1935; code :1939-1950", status := .proven
    prop := ``V6InitIntBytes, thm := some ``v6InitIntBytes_proven },
  { id := "ipaddress-hosts-doc", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseNetwork.hosts", "IPv6Network.hosts", "_BaseNetwork.__iter__", "_BaseNetwork.num_addresses",
      "_BaseNetwork.broadcast_address"]
    statement := "For every valid IPv4 or IPv6 network, list(net) is every address from the network address up, num_addresses counts them, and list(net.hosts()) is that list minus exactly what the documentation excludes (IPv4: network and broadcast below /31; IPv6: the Subnet-Router anycast address below /127)."
    source := "Doc/library/ipaddress.rst, hosts() for IPv4Network and IPv6Network", status := .proven
    prop := ``HostsDoc, thm := some ``hostsDoc_proven
    notes := "Difftest fn hosts (list, hosts, num_addresses on prefixes within 10 of the maximum)." },
  { id := "ipaddress-ip-int-from-prefix", pyFile := "Lib/ipaddress.py"
    pyFns := ["_IPAddressBase._ip_int_from_prefix"]
    statement := "For a prefix length p <= max_prefixlen, _ip_int_from_prefix(p) is p ones followed by max_prefixlen - p zeros."
    source := "_ip_int_from_prefix docstring, Lib/ipaddress.py:425-433", status := .proven
    prop := ``IpIntFromPrefixSpec, thm := some ``ipIntFromPrefixSpec_proven },
  { id := "ipaddress-prefix-from-ip-int", pyFile := "Lib/ipaddress.py"
    pyFns := ["_IPAddressBase._prefix_from_ip_int", "_count_righthand_zero_bits"]
    statement := "_prefix_from_ip_int returns the prefix length whose netmask is the int, found as if by trying every prefix length, and raises ValueError('Netmask pattern %r mixes zeroes & ones') with the int's big-endian bytes for every other int."
    source := "_prefix_from_ip_int docstring Raises, Lib/ipaddress.py:438-447", status := .proven
    prop := ``PrefixFromIpIntSpec, thm := some ``prefixFromIpIntSpec_proven },
  { id := "ipaddress-prefix-string", pyFile := "Lib/ipaddress.py"
    pyFns := ["_IPAddressBase._prefix_from_prefix_string", "_IPAddressBase._report_invalid_netmask"]
    statement := "For max_prefixlen 32 and 128, _prefix_from_prefix_string reads a non-empty string of at most 4300 ASCII digits whose value is at most max_prefixlen as that value, str(p) as p, and raises NetmaskValueError('%r is not a valid netmask') for everything else."
    source := "_prefix_from_prefix_string docstring Raises, Lib/ipaddress.py:468-478", status := .proven
    prop := ``PrefixStringSpec, thm := some ``prefixStringSpec_proven
    notes := "The 4300-digit cap is int()'s default str-digits limit; '0' * 5000 is refused (difftest)." },
  { id := "ipaddress-prefix-from-ip-string", pyFile := "Lib/ipaddress.py"
    pyFns := ["_IPAddressBase._prefix_from_ip_string", "_IPAddressBase._prefix_from_ip_int",
      "_IPAddressBase._report_invalid_netmask", "_BaseV4._ip_int_from_string", "_BaseV4._parse_octet"]
    statement := "_prefix_from_ip_string raises NetmaskValueError('%r is not a valid netmask') for a string IPv4Address refuses and for a quad that is neither a netmask nor the complement of one, and otherwise returns the prefix of the netmask, else of the complement."
    source := "_prefix_from_ip_string docstring Raises, Lib/ipaddress.py:493-503", status := .proven
    prop := ``PrefixFromIpStringSpec, thm := some ``prefixFromIpStringSpec_proven },
  { id := "ipaddress-v4-mask-roundtrip", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseV4._make_netmask", "_IPAddressBase._prefix_from_prefix_string",
      "_IPAddressBase._prefix_from_ip_string", "_IPAddressBase._prefix_from_ip_int",
      "_IPAddressBase._report_invalid_netmask"]
    statement := "For every prefix length p in [0, 32] and every cache, an IPv4 mask string is read as p when it is str(p), the netmask of /p, or (0 < p < 32) the hostmask of /p."
    source := "Doc/library/ipaddress.rst, IPv4Network: prefix, net mask or host mask", status := .proven
    prop := ``MaskRoundTrip, thm := some ``maskRoundTrip_proven
    notes := "Difftest fn mask4 (_make_netmask on prefix strings, netmasks, hostmasks, flipped bits, random quads, junk; exact NetmaskValueError messages)." },
  { id := "ipaddress-v4-mask-int", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseV4._make_netmask", "_BaseV6._make_netmask", "_IPAddressBase._report_invalid_netmask"]
    statement := "With any cache _make_netmask filled, an int mask is its own prefix length in [0, max_prefixlen] and otherwise raises NetmaskValueError('<n> is not a valid netmask'); a str is read by _prefix_from_prefix_string, and for IPv4 failing that by _prefix_from_ip_string."
    source := "ipaddress.py:1153-1178 and :1628-1647; IPv4Network docs, a two-tuple with a prefix length", status := .proven
    prop := ``MaskInt, thm := some ``maskInt_proven
    notes := "The cache is modelled (makeNetmaskCached); a non-int key equal to a cached int is the refuted ipaddress-v4-netmask-cache." },
  { id := "ipaddress-v6-text-roundtrip", pyFile := "Lib/ipaddress.py"
    pyFns := ["IPv6Address.__init__", "_BaseV6._ip_int_from_string", "_BaseV6._parse_hextet",
      "_BaseV6._compress_hextets", "_BaseV6._string_from_ip_int", "_BaseV6._split_scope_id",
      "IPv6Address.__str__", "IPv6Address._ipv4_mapped_ipv6_to_str", "IPv6Address.ipv4_mapped"]
    statement := "For every 128-bit int and every accepted scope id, str(IPv6Address) succeeds and IPv6Address of it gives the same address and scope (what __reduce__ relies on)."
    source := "IPv6Address docstring; __reduce__ pickles str(self)", status := .proven
    prop := ``V6RoundTrip, thm := some ``v6RoundTrip_proven
    notes := "Difftest fn v6init (parse, scope, str). The proof covers every _compress_hextets output shape (29) and the ::ffff:a.b.c.d form." },
  { id := "ipaddress-v6-str-form", pyFile := "Lib/ipaddress.py"
    pyFns := ["IPv6Address.__str__", "IPv6Address._ipv4_mapped_ipv6_to_str", "IPv6Address.ipv4_mapped",
      "_BaseV6._string_from_ip_int", "_BaseAddress.__str__"]
    statement := "For every 128-bit address, ipv4_mapped is the low 32 bits exactly in ::ffff:0:0/96; such an address prints as '::ffff:' and its dotted quad, every other address as _string_from_ip_int of it, and a scope id follows a '%'; _ipv4_mapped_ipv6_to_str refuses an unmapped address with AddressValueError."
    source := "_ipv4_mapped_ipv6_to_str docstring (RFC 4291 2.2 item 3), Lib/ipaddress.py:1981-1989; ipv4_mapped docstring :2167-2173", status := .proven
    prop := ``V6StrForm, thm := some ``v6StrForm_proven },
  { id := "ipaddress-v6-split-scope", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseV6._split_scope_id", "IPv6Address.__init__"]
    statement := "_split_scope_id gives no scope id for a string without '%', the text after the first '%' otherwise, and raises AddressValueError('Invalid IPv6 address: \"%r\"') for an empty scope id or one holding '%', which IPv6Address passes on."
    source := "_split_scope_id docstring (RFC 4007), Lib/ipaddress.py:1896-1913", status := .proven
    prop := ``SplitScopeSpec, thm := some ``splitScopeSpec_proven },
  { id := "ipaddress-v6-parse-hextet", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseV6._parse_hextet"]
    statement := "_parse_hextet reads every spelling of one to four hex digits, either case, leading zeros allowed, as its value; a non-hex character, five or more digits and the empty string raise its three ValueErrors."
    source := "_parse_hextet docstring, Lib/ipaddress.py:1763-1775", status := .proven
    prop := ``HextetSpec, thm := some ``hextetSpec_proven },
  { id := "ipaddress-v6-parse-spellings", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseV6._ip_int_from_string", "_BaseV6._parse_hextet", "_BaseV6._compress_hextets",
      "IPv4Address.__init__", "_BaseV4._ip_int_from_string", "_BaseV4._parse_octet"]
    statement := "_ip_int_from_string reads eight hextets in any spelling _parse_hextet accepts, uncompressed or with a run of '0' replaced by '::', as the address with those groups, and six hextets followed by a dotted quad IPv4Address accepts as those groups and the quad's 32 bits."
    source := "RFC 4291 2.2 (the forms ipaddress docs accept); _ip_int_from_string docstring, Lib/ipaddress.py:1650-1659", status := .proven
    prop := ``V6ParseSpellings, thm := some ``v6ParseSpellings_proven },
  { id := "ipaddress-v6-parse-refusals", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseV6._ip_int_from_string", "_BaseV6._parse_hextet", "IPv4Address.__init__"]
    statement := "_ip_int_from_string raises only AddressValueError, and each of its refusals (empty, over 45 characters, fewer than 3 parts, a bad IPv4 suffix, more than 8 colons, two '::', leading or trailing ':', too many parts with or without '::', a bad hextet) happens exactly under the source's condition, in its order, with its message."
    source := "_ip_int_from_string docstring Raises, Lib/ipaddress.py:1658-1659; ip_address relies on the class, :41-49", status := .proven
    prop := ``V6ParseRefusals, thm := some ``v6ParseRefusals_proven },
  { id := "ipaddress-v4-netmask-cache", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseV4._make_netmask"]
    statement := "The result of _make_netmask(arg) does not depend on what earlier calls cached."
    source := "invariant: a cache must not change results; docs: the mask is an int prefix length or a str", status := .refuted
    prop := ``NetmaskCacheTransparent, thm := some ``netmaskCacheTransparent_refuted
    bug := some "ipaddress-netmask-cache-history" },
  { id := "ipaddress-v4-mask-doc-rule", pyFile := "Lib/ipaddress.py"
    pyFns := ["_IPAddressBase._prefix_from_ip_string", "_IPAddressBase._prefix_from_ip_int", "_BaseV4._make_netmask"]
    statement := "A dotted mask whose first field is non-zero is accepted only as a netmask, as the documentation's rule says."
    source := "Doc/library/ipaddress.rst, IPv4Network item 1", status := .refuted
    prop := ``DocMaskRule, thm := some ``docMaskRule_refuted, bug := some "ipaddress-mask-rule-hostmask-first-field" },
  { id := "ipaddress-v6-compress-rfc5952", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseV6._compress_hextets", "_BaseV6._string_from_ip_int"]
    statement := "_string_from_ip_int raises TypeError with no argument (cls._ip is the slot descriptor) and ValueError above 2**128 - 1; for every 128-bit int it writes the eight hextets in '%x' joined by ':' when no two adjacent hextets are zero, and otherwise replaces the first longest run of zero hextets (length at least two) by '::'."
    source := "RFC 5952 4.2; the ipaddress docs' compressed form; _string_from_ip_int docstring Raises, Lib/ipaddress.py:1845-1846", status := .proven
    prop := ``CompressRFC5952, thm := some ``compressRFC5952_proven
    notes := "The loop of _compress_hextets reads a hextet only through hextet == '0', and '%x' % v == '0' iff v == 0, so the fold runs on the Bool mask; decide checks the run it ends on for all 256 masks." }
]

end PyLean.Ipaddress
