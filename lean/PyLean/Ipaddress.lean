import PyLean.Registry
import PyLean.Ipaddress.Model
import PyLean.Ipaddress.Spec
import PyLean.Ipaddress.Validation
import PyLean.Ipaddress.Lookup
import PyLean.Ipaddress.Summarize
import PyLean.Ipaddress.Subnets

/-!
`Lib/ipaddress.py`, CPython 3.14.7. The model covers the integer core of
networks; string parsing and formatting are not modelled yet.
-/

namespace PyLean.Ipaddress

open PyLean.Registry

def entries : List Entry := [
  { id := "ipaddress-subnets-validation", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseNetwork.subnets"]
    statement := "subnets raises ValueError for new_prefix shorter than the current prefix, for both arguments set, and for a negative or too-large prefixlen_diff."
    source := "subnets docstring, Lib/ipaddress.py:943-949", status := .refuted
    prop := ``SubnetsRejectsInvalidArgs, thm := some ``subnetsRejectsInvalidArgs_refuted
    bug := some "ipaddress-subnets-host-network-skips-validation"
    notes := "A /32 or /128 network yields itself before any argument is checked." },
  { id := "ipaddress-supernet-validation", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseNetwork.supernet"]
    statement := "supernet raises ValueError for new_prefix longer than the current prefix, for both arguments set, and when prefixlen - prefixlen_diff < 0."
    source := "supernet docstring, Lib/ipaddress.py:990-997", status := .refuted
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
    source := "overlaps docstring, Lib/ipaddress.py:747", status := .proven
    prop := ``OverlapsShareAddress, thm := some ``overlapsShareAddress_proven },
  { id := "ipaddress-subnet-of-mem", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseNetwork.subnet_of", "_BaseNetwork._is_subnet_of"]
    statement := "a.subnet_of(b) holds exactly when every address of a is in b."
    source := "subnet_of docstring, Lib/ipaddress.py:1043", status := .proven
    prop := ``SubnetOfMem, thm := some ``subnetOfMem_proven },
  { id := "ipaddress-summarize-exact-cover", pyFile := "Lib/ipaddress.py"
    pyFns := ["summarize_address_range", "_count_righthand_zero_bits"]
    statement := "For first <= last, summarize_address_range returns valid networks that tile first..last in ascending order."
    source := "summarize_address_range docstring, Lib/ipaddress.py:201-232", status := .proven
    prop := ``SummarizeExactCover, thm := some ``summarizeExactCover_proven },
  { id := "ipaddress-summarize-reversed", pyFile := "Lib/ipaddress.py"
    pyFns := ["summarize_address_range"]
    statement := "summarize_address_range raises ValueError when first > last."
    source := "summarize_address_range docstring, Lib/ipaddress.py:228-230", status := .proven
    prop := ``SummarizeRejectsReversed, thm := some ``summarizeRejectsReversed_proven },
  { id := "ipaddress-subnets-partition", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseNetwork.subnets"]
    statement := "For a valid prefixlen_diff, subnets returns 2^diff valid networks of the new prefix that tile the network in order."
    source := "subnets docstring, Lib/ipaddress.py:925-951", status := .open
    prop := ``SubnetsPartition, thm := some ``subnetsPartition_proven },
  { id := "ipaddress-supernet-contains", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseNetwork.supernet"]
    statement := "For 0 <= diff <= prefixlen, supernet returns a valid network of prefix prefixlen - diff containing self."
    source := "supernet docstring, Lib/ipaddress.py:978-998", status := .open
    prop := ``SupernetContains, thm := some ``supernetContains_proven },
  { id := "ipaddress-address-exclude-partition", pyFile := "Lib/ipaddress.py"
    pyFns := ["_BaseNetwork.address_exclude"]
    statement := "For other a subnet of self, address_exclude returns valid networks that with other cover self exactly once."
    source := "address_exclude docstring, Lib/ipaddress.py:792-825", status := .open
    prop := ``AddressExcludePartition, thm := some ``addressExcludePartition_proven }
]

end PyLean.Ipaddress
