import PyLean.Registry
import PyLean.Ipaddress.Model
import PyLean.Ipaddress.Spec
import PyLean.Ipaddress.Validation
import PyLean.Ipaddress.Lookup
import PyLean.Ipaddress.Summarize
import PyLean.Ipaddress.Subnets
import PyLean.Ipaddress.Exploded

/-!
`Lib/ipaddress.py`, CPython 3.15.2. The model covers the integer core of networks,
`exploded` of IPv6 objects and `is_unspecified` of interfaces; string parsing and the
other formatting are not modelled yet.
-/

namespace PyLean.Ipaddress

open PyLean.Registry

def entries : List Entry := [
  { id := "ipaddress-subnets-validation", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseNetwork.subnets"]
    statement := "subnets raises ValueError for new_prefix shorter than the current prefix, for both arguments set, and for a negative or too-large prefixlen_diff."
    source := "subnets docstring, Lib/ipaddress.py:940-946", status := .refuted
    prop := ``SubnetsRejectsInvalidArgs, thm := some ``subnetsRejectsInvalidArgs_refuted
    bug := some "ipaddress-subnets-host-network-skips-validation"
    notes := "A /32 or /128 network yields itself before any argument is checked." },
  { id := "ipaddress-supernet-validation", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseNetwork.supernet"]
    statement := "supernet raises ValueError for new_prefix longer than the current prefix, for both arguments set, and when prefixlen - prefixlen_diff < 0."
    source := "supernet docstring, Lib/ipaddress.py:987-994", status := .refuted
    prop := ``SupernetRejectsInvalidArgs, thm := some ``supernetRejectsInvalidArgs_refuted
    bug := some "ipaddress-supernet-zero-prefix-skips-validation"
    notes := "A /0 network returns itself before any argument is checked." },
  { id := "ipaddress-getitem-sequence", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseNetwork.__getitem__"]
    statement := "net[i] returns addr + i mod size for -size <= i < size and raises IndexError otherwise."
    source := "invariant: sequence indexing", status := .proven
    prop := ``GetitemSequence, thm := some ``getitemSequence_proven },
  { id := "ipaddress-contains-mem", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseNetwork.__contains__"]
    statement := "address in net holds exactly for the addresses of the block."
    source := "invariant", status := .proven
    prop := ``ContainsMem, thm := some ``containsMem_proven },
  { id := "ipaddress-overlaps-share", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseNetwork.overlaps"]
    statement := "a.overlaps(b) holds exactly when the blocks share an address."
    source := "overlaps docstring, Lib/ipaddress.py:744", status := .proven
    prop := ``OverlapsShareAddress, thm := some ``overlapsShareAddress_proven },
  { id := "ipaddress-subnet-of-mem", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseNetwork.subnet_of", "_BaseNetwork._is_subnet_of"]
    statement := "a.subnet_of(b) holds exactly when every address of a is in b."
    source := "subnet_of docstring, Lib/ipaddress.py:1040", status := .proven
    prop := ``SubnetOfMem, thm := some ``subnetOfMem_proven },
  { id := "ipaddress-summarize-exact-cover", pyFile := "Lib/ipaddress.py"
    pyFns := ["summarize_address_range", "_count_righthand_zero_bits"]
    statement := "For first <= last, summarize_address_range returns valid networks that tile first..last in ascending order."
    source := "summarize_address_range docstring, Lib/ipaddress.py:198-229", status := .proven
    prop := ``SummarizeExactCover, thm := some ``summarizeExactCover_proven },
  { id := "ipaddress-summarize-reversed", pyFile := "Lib/ipaddress.py"
    pyFns := ["summarize_address_range"]
    statement := "summarize_address_range raises ValueError when first > last."
    source := "summarize_address_range, Lib/ipaddress.py:229-230", status := .proven
    prop := ``SummarizeRejectsReversed, thm := some ``summarizeRejectsReversed_proven },
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
    pyFns := ["_BaseNetwork.address_exclude"]
    statement := "For other a subnet of self, address_exclude returns valid networks that with other cover self exactly once."
    source := "address_exclude docstring, Lib/ipaddress.py:789-822", status := .proven
    prop := ``AddressExcludePartition, thm := some ``addressExcludePartition_proven },
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
    pyFns := ["IPv6Address._explode_shorthand_ip_string", "_BaseV6._explode_shorthand_ip_string"]
    statement := "exploded of an unscoped network and of any address or interface outside ::ffff:0:0/96 is the eight hextets with the prefix and scope id; of an IPv4-mapped address or interface it is the first 30 characters of that and a dotted quad."
    source := "Lib/ipaddress.py:1861-1884, :1961-1966", status := .proven
    prop := ``ExplodedByCase, thm := some ``explodedByCase_proven
    notes := "The two refuted entries above are the cases this one sets aside or describes as they are." },
  { id := "ipaddress-exploded-hextets", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseV6._explode_shorthand_ip_string"]
    statement := "For every 128-bit ip, the eight hextets exploded prints, read as a base-65536 number, are ip."
    source := "invariant: exploded names the same address", status := .proven
    prop := ``HextetsRecompose, thm := some ``hextetsRecompose_proven },
  { id := "ipaddress-iface-unspecified", pyFile := "Lib/ipaddress.py"
    pyFns := ["IPv4Interface.is_unspecified", "IPv6Interface.is_unspecified"]
    statement := "An IPv4 or IPv6 interface is unspecified exactly when its address is zero and its prefix is the full length."
    source := "Lib/ipaddress.py:1479-1481, :2273-2275; _BaseNetwork.is_unspecified docstring, :1099-1106", status := .proven
    prop := ``IfaceUnspecified, thm := some ``ifaceUnspecified_proven }
]

end PyLean.Ipaddress
