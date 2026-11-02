import PyLean.Ipaddress.Parse4Props

/-!
IPv6 text: `_BaseV6._parse_hextet` (Lib/ipaddress.py:1762-1786), `_BaseV6._ip_int_from_string`
(:1649-1760), `_BaseV6._compress_hextets` (:1788-1834), `_BaseV6._string_from_ip_int`
(:1836-1855), `_BaseV6._split_scope_id` (:1896-1913), `IPv6Address.__init__` (:1921-1964),
`IPv6Address.ipv4_mapped`, `_ipv4_mapped_ipv6_to_str` (:1983-1996) and `IPv6Address.__str__`
(:1998-2004), CPython 3.15.2. Strings are lists of code points; messages embedding `%r` are
rendered exactly when the string is printable ASCII without a quote or backslash.
-/

namespace PyLean.Ipaddress

open PyLean

/-- `c in _HEX_DIGITS`. -/
def isHexC (c : Char) : Bool :=
  (48 ≤ c.toNat && c.toNat ≤ 57) || (97 ≤ c.toNat && c.toNat ≤ 102) || (65 ≤ c.toNat && c.toNat ≤ 70)

def hexValC (c : Char) : Nat :=
  if c.toNat ≤ 57 then c.toNat - 48 else if c.toNat ≤ 70 then c.toNat - 55 else c.toNat - 87

/-- `int(s, 16)` on hex digits. -/
def hexVal (s : List Char) : Nat := s.foldl (fun v c => v * 16 + hexValC c) 0

/-- The `ValueError`s of `_parse_hextet`; `emptyLit` is `int('', 16)`'s, since the empty string
passes both checks. -/
inductive HexErr where
  | nonHex
  | tooLong
  | emptyLit
  deriving DecidableEq, Repr

/-- `_BaseV6._parse_hextet`, :1762-1786. -/
def parseHextet (s : List Char) : Except HexErr Nat :=
  if !(s.all isHexC) then .error .nonHex
  else if s.length > 4 then .error .tooLong
  else if s.isEmpty then .error .emptyLit
  else .ok (hexVal s)

def hexMsg (s : List Char) : HexErr → Option String
  | .nonHex => (reprPlain s).map ("Only hex digits permitted in " ++ ·)
  | .tooLong => (reprPlain s).map ("At most 4 characters permitted in " ++ ·)
  | .emptyLit => some "invalid literal for int() with base 16: ''"

/-- `s.split(sep, maxsplit)` for a one-character separator. -/
def splitMax (sep : Char) : Nat → List Char → List (List Char)
  | _, [] => [[]]
  | m, c :: cs =>
    if c = sep ∧ m > 0 then [] :: splitMax sep (m - 1) cs
    else match splitMax sep m cs with
      | p :: ps => (c :: p) :: ps
      | [] => [[c]]

/-- One lowercase hex digit. -/
def hd (k : Nat) : Char := Char.ofNat (if k < 10 then 48 + k else 87 + k)

/-- `'%x' % v` for `v < 2**16`, the only values the model formats: lowercase, no leading zeros. -/
def hexStr (v : Nat) : List Char :=
  if v < 16 then [hd v]
  else if v < 256 then [hd (v / 16), hd (v % 16)]
  else if v < 4096 then [hd (v / 256), hd (v / 16 % 16), hd (v % 16)]
  else [hd (v / 4096), hd (v / 256 % 16), hd (v / 16 % 16), hd (v % 16)]

def avMsg (pre : String) (s : List Char) : PyExc := avErr ((reprPlain s).map (pre ++ ·))

/-- The hextet loops of :1745-1758, parts read left to right; the first `ValueError` is kept. -/
def parseHextets : List (List Char) → Except (List Char × HexErr) (List Nat)
  | [] => .ok []
  | p :: ps =>
    match parseHextet p with
    | .error e => .error (p, e)
    | .ok v => (parseHextets ps).map (v :: ·)

/-- `ip_int` from the high parts, the skipped zeros and the low parts. -/
def combine (hi : List Nat) (skipped : Nat) (lo : List Nat) : Nat :=
  let x := hi.foldl (fun v h => v * 65536 + h) 0
  let x := x * 65536 ^ skipped
  lo.foldl (fun v h => v * 65536 + h) x

/-- The first index in `[1, len - 1)` holding an empty part, and whether there is a second. -/
def skipScan (parts : List (List Char)) : Option Nat × Bool :=
  let inner := ((parts.drop 1).take (parts.length - 2)).zipIdx
  inner.foldl (fun (sk, two) (p, i) =>
    if p.isEmpty then (if sk.isSome then (sk, true) else (some (i + 1), two)) else (sk, two)) (none, false)

/-- `_BaseV6._ip_int_from_string`, :1649-1760. -/
def ipIntFromString6 (s : List Char) : Py Nat := do
  if s.isEmpty then throw (avErr (some "Address cannot be empty"))
  if s.length > 45 then
    let shorten := if s.length > 100 then
        s.take 45 ++ s!"({s.length - 90} chars elided)".toList ++ s.drop (s.length - 45)
      else s
    throw (avMsg "At most 45 characters expected in " shorten)
  let parts := splitMax ':' 9 s
  if parts.length < 3 then throw (avMsg "At least 3 parts expected in " s)
  let parts ← if '.' ∈ parts.getLast! then
      match ipv4Init (.str parts.getLast!) with
      | .error e =>
        throw (avErr (do let r ← reprPlain s; if e.message.startsWith "~" then none else
          some (e.message ++ " in " ++ r)))
      | .ok v => pure (parts.dropLast ++ [hexStr (v / 65536 % 65536), hexStr (v % 65536)])
    else pure parts
  if parts.length > 9 then throw (avMsg "At most 8 colons permitted in " s)
  let (skip, two) := skipScan parts
  if two then throw (avMsg "At most one '::' permitted in " s)
  let (hi, lo, skipped) ← match skip with
    | some sk =>
      let hi := if parts.head!.isEmpty then sk - 1 else sk
      if parts.head!.isEmpty ∧ hi ≠ 0 then
        throw (avMsg "Leading ':' only permitted as part of '::' in " s)
      let lo := if parts.getLast!.isEmpty then parts.length - sk - 2 else parts.length - sk - 1
      if parts.getLast!.isEmpty ∧ lo ≠ 0 then
        throw (avMsg "Trailing ':' only permitted as part of '::' in " s)
      if 8 < hi + lo + 1 then
        throw (avMsg "Expected at most 7 other parts with '::' in " s)
      pure (hi, lo, 8 - (hi + lo))
    | none =>
      if parts.length ≠ 8 then throw (avMsg "Exactly 8 parts expected without '::' in " s)
      if parts.head!.isEmpty then throw (avMsg "Leading ':' only permitted as part of '::' in " s)
      if parts.getLast!.isEmpty then throw (avMsg "Trailing ':' only permitted as part of '::' in " s)
      pure (parts.length, 0, 0)
  let hiParts := parts.take hi
  let loParts := parts.drop (parts.length - lo)
  match parseHextets (hiParts ++ loParts) with
  | .error (p, e) => throw (avErr (do let m ← hexMsg p e; let r ← reprPlain s; pure (m ++ " in " ++ r)))
  | .ok vs => pure (combine (vs.take hi) skipped (vs.drop hi))

/-- `_BaseV6._compress_hextets`, :1788-1834: the first longest run of `'0'` hextets, if longer
than one, becomes `''` (with an extra `''` at either end). -/
def compressHextets (hs : List (List Char)) : List (List Char) :=
  let step := fun (st : Int × Nat × Int × Nat) (hi : List Char × Nat) =>
    let (bs, bl, ds, dl) := st
    let (h, i) := hi
    if h = ['0'] then
      let dl := dl + 1
      let ds := if ds = -1 then (i : Int) else ds
      if dl > bl then (ds, dl, ds, dl) else (bs, bl, ds, dl)
    else (bs, bl, -1, 0)
  let (bs, bl, _, _) := hs.zipIdx.foldl step (-1, 0, -1, 0)
  if bl > 1 then
    let e := bs.toNat + bl
    let hs := if e = hs.length then hs ++ [[]] else hs
    let hs := hs.take bs.toNat ++ [[]] ++ hs.drop e
    if bs = 0 then [] :: hs else hs
  else hs

/-- The eight hextets of `'%032x' % ip_int`, each as `'%x'`. -/
def hextetsOf (n : Nat) : List (List Char) :=
  (List.range 8).map fun i => hexStr (n / 65536 ^ (7 - i) % 65536)

/-- `_BaseV6._string_from_ip_int`, :1836-1855, for `ip_int < 2**128`. -/
def stringFromIpInt6 (n : Nat) : List Char := joinOn1 ':' (compressHextets (hextetsOf n))

/-- `IPv6Address.__str__`, :1998-2004, with `ipv4_mapped` and `_ipv4_mapped_ipv6_to_str`. -/
def ipv6Str (ip : Nat) (scope : Option (List Char)) : List Char :=
  let s := if ip / 2 ^ 32 = 0xFFFF then stringFromIpInt6 (ip / 2 ^ 32) ++ ':' :: ipv4Str (ip % 2 ^ 32)
    else stringFromIpInt6 ip
  match scope with
  | some sc => if sc.isEmpty then s else s ++ '%' :: sc
  | none => s

/-- `str.partition('%')`. -/
def partitionPct (s : List Char) : List Char × Bool × List Char :=
  match s.span (· ≠ '%') with
  | (a, []) => (a, false, [])
  | (a, _ :: b) => (a, true, b)

/-- `IPv6Address.__init__` for a str, :1921-1964: the `/` check, `_split_scope_id`, the parse. -/
def ipv6InitStr (s : List Char) : Py (Nat × Option (List Char)) := do
  if '/' ∈ s then throw (avMsg "Unexpected '/' in " s)
  let (addr, sep, scope) := partitionPct s
  let scope ← if !sep then pure none
    else if scope.isEmpty ∨ '%' ∈ scope then
      throw (avErr ((reprPlain s).map (fun r => "Invalid IPv6 address: \"" ++ r ++ "\"")))
    else pure (some scope)
  let ip ← ipIntFromString6 addr
  pure (ip, scope)

/-- For every 128-bit int and every scope that `IPv6Address` accepts (non-empty, no `%`, no `/`),
parsing `str()` of the address gives the address and the scope back. `__reduce__` pickles an
IPv6Address as `str(self)`, so this is what makes pickling exact.

Proven in `Parse6Props.lean` (`v6RoundTrip_proven`): (1) for `k < 16`, `hd k` is a hex digit
worth `k`; for `v < 2**16`, `parseHextet (hexStr v) = .ok v`, `hexStr v` is non-empty with at most
4 hex digits, and `hexStr v = ['0'] → v = 0`. (2) The fold of `compressHextets` keeps the invariant
"the best run `[bs, bs + bl)` and the current run `[ds, k)` hold only `'0'` hextets", so the output
is the eight hextets or `pre ++ H.take bs ++ [[]] ++ post` (`pre = [[]]` iff `bs = 0`, `post = [[]]`
if `bs + bl = 8`, else `H.drop (bs + bl)`). (3) `splitMax ':' 9` of `joinOn1 ':' parts` is `parts`
when no part holds `:` and there are at most 10 parts. (4) Each of the 29 shapes parses back, and
`combine` gives the value (zeros in the run). (5) The IPv4-mapped form is `"::ffff:" ++ ipv4Str low`,
whose last part goes through `ipv4Init` (`v4RoundTrip_proven`). (6) No `%` or `/` before the scope
suffix, so `partitionPct` splits there. -/
def V6RoundTrip : Prop :=
  ∀ (n : Nat) (sc : Option (List Char)), n < 2 ^ 128 →
    (∀ x, sc = some x → x ≠ [] ∧ '%' ∉ x ∧ '/' ∉ x) →
    ipv6InitStr (ipv6Str n sc) = .ok (n, sc)

end PyLean.Ipaddress
