import PyLean.Ipaddress.Parse4Props

/-!
IPv4 masks given as strings: `_BaseV4._make_netmask` (Lib/ipaddress.py:1154-1178) for a str
argument, `_prefix_from_prefix_string` (:467-490), `_prefix_from_ip_string` (:492-524),
`_prefix_from_ip_int` (:437-460) and `_report_invalid_netmask` (:462-465), CPython 3.15.2.
-/

namespace PyLean.Ipaddress

open PyLean

def netmaskErr (s : List Char) : PyExc :=
  .named "NetmaskValueError" ((reprPlain s).map (· ++ " is not a valid netmask") |>.getD "~is not a valid netmask")

/-- `_prefix_from_prefix_string`: ASCII digits, then `0 <= int(s) <= 32`. `none` is
`NetmaskValueError`. -/
def prefixFromPrefixString (s : List Char) : Option Nat :=
  if !(s.all isDigitC && !s.isEmpty) then none
  else
    let p := digitsVal s
    if p ≤ 32 then some p else none

/-- `_prefix_from_ip_int`: the prefix of a contiguous netmask; `none` is the `ValueError`
"Netmask pattern ... mixes zeroes & ones". -/
def prefixFromIpInt (n : Nat) : Option Nat :=
  let tz := countRighthandZeroBits n 32
  let p := 32 - tz
  if n >>> tz != 2 ^ p - 1 then none else some p

/-- `_prefix_from_ip_string`: parse the dotted quad, try it as a netmask, then its complement as
one (a hostmask). -/
def prefixFromIpString (s : List Char) : Option Nat :=
  match ipIntFromString4 s with
  | .error _ => none
  | .ok n =>
    match prefixFromIpInt n with
    | some p => some p
    | none => prefixFromIpInt (n ^^^ allOnes 32)

/-- `_make_netmask(arg)` for a str `arg`: a prefix length first, then a dotted quad. -/
def makeNetmask4 (s : List Char) : Py Nat :=
  match prefixFromPrefixString s with
  | some p => .ok p
  | none =>
    match prefixFromIpString s with
    | some p => .ok p
    | none => .error (netmaskErr s)

/-- `_make_netmask(arg)` for an int `arg`, :1163-1167. -/
def makeNetmask4Int (p : Int) : Py Nat :=
  if 0 ≤ p ∧ p ≤ 32 then .ok p.toNat
  else .error (.named "NetmaskValueError" s!"{p} is not a valid netmask")

/-- An int mask is accepted exactly in `[0, 32]` and is its own prefix length; anything else raises
`NetmaskValueError` naming it. -/
def MaskInt : Prop :=
  ∀ p : Int, (0 ≤ p ∧ p ≤ 32 → makeNetmask4Int p = .ok p.toNat) ∧
    (¬ (0 ≤ p ∧ p ≤ 32) → makeNetmask4Int p = .error (.named "NetmaskValueError" s!"{p} is not a valid netmask"))

theorem maskInt_proven : MaskInt := fun p =>
  ⟨fun h => by simp [makeNetmask4Int, h], fun h => by simp [makeNetmask4Int, h]⟩

def okNat (r : Py Nat) (p : Nat) : Bool := match r with | .ok v => v == p | .error _ => false

/-- For every prefix length `p` in `[0, 32]`, `IPv4Network('a/m')` reads the mask `m` as `p` when
`m` is `str(p)`, the netmask of `/p`, or (for `0 < p < 32`) the hostmask of `/p`. At `/0` and `/32`
the hostmask is the netmask of the other, and the documented exception (all-zero is a netmask)
decides. -/
def MaskRoundTrip : Prop :=
  ∀ p, p ≤ 32 →
    okNat (makeNetmask4 (toString p).toList) p = true ∧
    okNat (makeNetmask4 (stringFromIpInt4 (ipIntFromPrefix 32 p))) p = true ∧
    (1 ≤ p → p ≤ 31 → okNat (makeNetmask4 (stringFromIpInt4 (ipIntFromPrefix 32 p ^^^ allOnes 32))) p = true)

set_option maxRecDepth 100000 in
theorem maskRoundTrip_proven : MaskRoundTrip := by unfold MaskRoundTrip; decide

/-- The documented rule (Doc/library/ipaddress.rst, IPv4Network): a dotted mask "is interpreted as
a *net mask* if it starts with a non-zero field, or as a *host mask* if it starts with a zero
field, with the single exception of an all-zero mask which is treated as a *net mask*". So a mask
whose first field is non-zero is accepted only if it is a netmask. The code tries the netmask
reading, then the hostmask one, and accepts `127.255.255.255` as the hostmask of `/1`. -/
def DocMaskRule : Prop :=
  ∀ n p, n < 2 ^ 32 → n / 2 ^ 24 ≠ 0 → makeNetmask4 (stringFromIpInt4 n) = .ok p →
    n = ipIntFromPrefix 32 p

theorem docMaskRule_refuted : ¬ DocMaskRule := by
  intro h
  have := h 0x7fffffff 1 (by decide) (by decide) (by decide)
  revert this; decide

/-! ## The cache -/

/-- A mask argument: an int, a str, or another number equal to the int `v` (a float such as
`8.0`, `Decimal(8)`), which `in` and dict lookup treat as `v`. -/
inductive MaskArg where
  | int (v : Int)
  | str (s : List Char)
  | numEq (v : Int) (tyName : String)

/-- `_netmask_cache` as the prefix lengths it holds, keyed by the int value they were stored under
(a str key is kept apart). -/
abbrev NetmaskCache := List (Int × Nat)

/-- `_BaseV4._make_netmask(arg)`, ipaddress.py:1154-1178: the cache is consulted first
(`arg not in cls._netmask_cache`, :1162), and only a miss checks the type (:1163); a non-int,
non-str argument reaches `_prefix_from_prefix_string`, whose `isascii()` call raises
`AttributeError`. Returns the prefix length and the cache afterwards. -/
def makeNetmaskCached (cache : NetmaskCache) (a : MaskArg) : Py Nat × NetmaskCache :=
  match a with
  | .str s => (makeNetmask4 s, cache)
  | .int v =>
    match cache.lookup v with
    | some p => (.ok p, cache)
    | none => match makeNetmask4Int v with
      | .ok p => (.ok p, (v, p) :: cache)
      | .error e => (.error e, cache)
  | .numEq v ty =>
    match cache.lookup v with
    | some p => (.ok p, cache)
    | none => (.error (.named "AttributeError" s!"'{ty}' object has no attribute 'isascii'"), cache)

/-- The cache is an optimisation: the result of `_make_netmask(arg)` does not depend on what
earlier calls stored. Refuted: `8.0` raises `AttributeError` with an empty cache and gives 8 once
the int 8 is cached (bug ipaddress-netmask-cache-history). -/
def NetmaskCacheTransparent : Prop :=
  ∀ (c1 c2 : NetmaskCache) (a : MaskArg),
    (∀ k p, c1.lookup k = some p → makeNetmask4Int k = .ok p) →
    (∀ k p, c2.lookup k = some p → makeNetmask4Int k = .ok p) →
    (makeNetmaskCached c1 a).1 = (makeNetmaskCached c2 a).1

theorem netmaskCacheTransparent_refuted : ¬ NetmaskCacheTransparent := by
  intro h
  have := h [] [(8, 8)] (.numEq 8 "float") (by simp) (by
    intro k p hk; simp [List.lookup] at hk; split at hk <;> simp_all [makeNetmask4Int])
  simp [makeNetmaskCached, List.lookup] at this

end PyLean.Ipaddress
