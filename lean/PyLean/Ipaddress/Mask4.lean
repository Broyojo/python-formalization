import PyLean.Ipaddress.Parse4Props
import PyLean.Ipaddress.Summarize

/-!
Masks: `_BaseV4._make_netmask` (Lib/ipaddress.py:1153-1177) and `_BaseV6._make_netmask`
(:1628-1646) with `_netmask_cache`, `_prefix_from_prefix_string` (:466-489),
`_prefix_from_ip_string` (:491-523), `_prefix_from_ip_int` (:436-459) and
`_report_invalid_netmask` (:461-464), CPython 3.15.2, for str, bytes and other arguments.
-/

namespace PyLean.Ipaddress

open PyLean

/-- `sys.get_int_max_str_digits()` at its default: `int(s)` of a decimal string with more digits
raises `ValueError` (the 4300-digit limit, `Objects/longobject.c`). -/
def intMaxStrDigits : Nat := 4300

/-- The `NetmaskValueError` of `_report_invalid_netmask` for a str: `'%r is not a valid netmask'`,
rendered where `reprPlain` renders `repr(s)`. -/
def netmaskErr (s : List Char) : PyExc :=
  .named "NetmaskValueError" ((reprPlain s).map (· ++ " is not a valid netmask") |>.getD "~is not a valid netmask")

/-- `_report_invalid_netmask(netmask_str)`, ipaddress.py:462-465: `'%r is not a valid netmask'`.
`reprArg` is `repr` of the argument where the model renders it (`some (toString p)` for an int,
`reprPlain s` for a str). `raise ... from None` only suppresses the exception context, which the
exception model does not record. -/
def reportInvalidNetmask {α : Type} (reprArg : Option String) : Py α :=
  .error (.named "NetmaskValueError" ((reprArg.map (· ++ " is not a valid netmask")).getD "~is not a valid netmask"))

/-- `_prefix_from_prefix_string`, ipaddress.py:467-490, for `max_prefixlen` `maxp` and a str:
`isascii() and isdigit()` (:481-482), `int()` (:483-486, which fails past the digit limit), then
the range (:487-488). -/
def prefixFromPrefixString (maxp : Nat) (s : List Char) : Py Nat :=
  if !(s.all isDigitC && !s.isEmpty) then reportInvalidNetmask (reprPlain s)
  else if s.length > intMaxStrDigits then reportInvalidNetmask (reprPlain s)
  else
    let p := digitsVal s
    if p ≤ maxp then .ok p else reportInvalidNetmask (reprPlain s)

/-- `_prefix_from_ip_int`, ipaddress.py:437-460, for `max_prefixlen` `bits`: the trailing zeros
(:449-450), the prefix length (:451), the leading ones (:452-453); for a mismatch (:454) the
`to_bytes` (:455-456), which raises first for an int of more than `max_prefixlen` bits, then the
`ValueError` (:457-458). -/
def prefixFromIpInt (bits n : Nat) : Py Nat :=
  let tz := countRighthandZeroBits n bits
  let p := bits - tz
  if n >>> tz ≠ 2 ^ p - 1 then
    match toBytesPy (bits / 8) n with
    | .error e => .error e
    | .ok details => .error (.valueError s!"Netmask pattern {bytesRepr details} mixes zeroes & ones")
  else .ok p

/-- `_prefix_from_ip_string`, ipaddress.py:492-524 (IPv4 only calls it): parse the dotted quad
(an `AddressValueError` becomes the report, :505-508), try it as a netmask (:513-516), then its
complement (:519-524). -/
def prefixFromIpString (s : List Char) : Py Nat :=
  match ipIntFromString4 s with
  | .error (.named "AddressValueError" _) => reportInvalidNetmask (reprPlain s)
  | .error e => .error e
  | .ok n =>
    match prefixFromIpInt 32 n with
    | .ok p => .ok p
    | .error (.valueError _) =>
      match prefixFromIpInt 32 (n ^^^ allOnes 32) with
      | .ok p => .ok p
      | .error (.valueError _) => reportInvalidNetmask (reprPlain s)
      | .error e => .error e
    | .error e => .error e

/-- The str branch of `_BaseV4._make_netmask`, ipaddress.py:1168-1175: a prefix length first,
then, on `NetmaskValueError`, a dotted quad. -/
def makeNetmask4 (s : List Char) : Py Nat :=
  match prefixFromPrefixString 32 s with
  | .ok p => .ok p
  | .error (.named "NetmaskValueError" _) => prefixFromIpString s
  | .error e => .error e

/-- The int branch of `_make_netmask`, ipaddress.py:1163-1167 and :1638-1641. -/
def makeNetmaskInt (bits : Nat) (p : Int) : Py Nat :=
  if 0 ≤ p ∧ p ≤ bits then .ok p.toNat else reportInvalidNetmask (some (toString p))

/-- The str branch for one family: `_BaseV6._make_netmask` takes only a prefix length (:1642-1643). -/
def makeNetmaskStr (bits : Nat) (s : List Char) : Py Nat :=
  if bits = 32 then makeNetmask4 s else prefixFromPrefixString bits s

/-! ## A bytes mask

`_make_netmask` checks only `isinstance(arg, int)` (:1163, :1638), so a bytes object reaches the
str functions, and bytes has `isascii`, `isdigit`, `int()` and `split` too. -/

/-- `bytes.isdigit()` on one byte: an ASCII digit. -/
def isDigitB (x : Nat) : Bool := 48 ≤ x && x ≤ 57

/-- `bytes.isascii()` on one byte. -/
def isAsciiB (x : Nat) : Bool := x < 128

/-- `int(b)` of a bytes object of ASCII digits. -/
def bytesDigitsVal (b : List Nat) : Nat := b.foldl (fun v x => v * 10 + (x - 48)) 0

/-- `_prefix_from_prefix_string(b)`, ipaddress.py:467-490, for a bytes `b`: `b.isascii() and
b.isdigit()` (:481-482; `bytes.isdigit()` is false for `b''`), `int(b)` (:483-486, under the same
digit limit as a str), the range (:487-488); the report shows `repr(b)` (:462-465). -/
def prefixFromPrefixBytes (maxp : Nat) (b : List Nat) : Py Nat :=
  if !(b.all isAsciiB && (!b.isEmpty && b.all isDigitB)) then reportInvalidNetmask (some (bytesRepr b))
  else if b.length > intMaxStrDigits then reportInvalidNetmask (some (bytesRepr b))
  else
    let p := bytesDigitsVal b
    if p ≤ maxp then .ok p else reportInvalidNetmask (some (bytesRepr b))

/-- `_prefix_from_ip_string(b)` for a bytes `b`, ipaddress.py:492-524 (IPv4 only calls it):
`_BaseV4._ip_int_from_string(b)` raises `AddressValueError('Address cannot be empty')` for `b''`
(:1193-1194), which becomes the report (:505-508); for any other bytes `ip_str.split('.')` (:1196)
raises `TypeError`, which nothing catches. -/
def prefixFromIpBytes4 (b : List Nat) : Py Nat :=
  if b.isEmpty then reportInvalidNetmask (some (bytesRepr b))
  else .error (.typeError "a bytes-like object is required, not 'str'")

/-- The non-int branch of `_make_netmask` for a bytes `b`: IPv4 tries a prefix length, then on
`NetmaskValueError` a dotted quad (:1168-1174); IPv6 only a prefix length (:1643). -/
def makeNetmaskBytes (bits : Nat) (b : List Nat) : Py Nat :=
  if bits = 32 then
    match prefixFromPrefixBytes 32 b with
    | .ok p => .ok p
    | .error (.named "NetmaskValueError" _) => prefixFromIpBytes4 b
    | .error e => .error e
  else prefixFromPrefixBytes bits b

/-! ## The cache -/

/-- A mask argument: an int, a str, a bytes object, another number equal to the int `v` (a float
such as `8.0`, `Decimal(8)`), which `in` and dict lookup treat as `v`, another hashable object of
type `tyName` equal to no int, str or bytes and without `isascii` (`8.5`, `None`, a tuple), or an
object whose `__hash__` raises `hashExc` (a list or `bytearray` raises
`TypeError("unhashable type: 'list'")`; a tuple holding a list raises the list's error; a class may
raise anything). `tyQual` is the argument type's fully qualified name, as `%T` prints it (`list`,
`mod.C`). -/
inductive MaskArg where
  | int (v : Int)
  | str (s : List Char)
  | bytes (b : List Nat)
  | numEq (v : Int) (tyName : String)
  | other (tyName : String)
  | unhashable (tyQual : String) (hashExc : PyExc)

/-- `_netmask_cache` as the prefix lengths it holds, keyed by the int value they were stored under.
A str or bytes key can only be hit by an equal str or bytes, whose result it repeats, so it is left
out. -/
abbrev NetmaskCache := List (Int × Nat)

/-- `dict_unhashable_type(op, key)` for a non-frozen dict, Objects/dictobject.c:2442-2460: the
exception `key`'s hash raised is kept unless its type is exactly `TypeError` (:2446,
`Py_IS_TYPE`, so a subclass is kept too), and a `TypeError` is replaced by one whose message
formats the key's type (`%T`, fully qualified) and the original exception (`%S`, its `str`, which
for a one-argument `TypeError` is the message). -/
def dictUnhashableType (tyQual : String) : PyExc → PyExc
  | .typeError m => .typeError s!"cannot use '{tyQual}' as a dict key ({m})"
  | e => e

/-- `_make_netmask(arg)` with the class's `_netmask_cache`, ipaddress.py:1153-1177 (IPv4,
`bits = 32`) and :1628-1646 (IPv6, `bits = 128`): the cache is consulted first
(`arg not in cls._netmask_cache`, :1162 and :1637), which hashes `arg` through `dict_contains`
(Objects/dictobject.c:5235-5240); a hash error goes through `dict_unhashable_type` (:2442-2460),
which re-raises any exception other than an exact `TypeError` unchanged and replaces a `TypeError`
by `TypeError("cannot use '%T' as a dict key (%S)")` around the original message. Only a miss
checks the type (:1163, :1638); a non-int argument goes to the
str functions: a bytes object works through them, and any other object raises `AttributeError` at
`isascii()` (:481). Returns the prefix length and the cache afterwards; the netmask is
`_ip_int_from_prefix` of it (:1175, :1644). -/
def makeNetmaskCached (bits : Nat) (cache : NetmaskCache) (a : MaskArg) : Py Nat × NetmaskCache :=
  match a with
  | .str s => (makeNetmaskStr bits s, cache)
  | .bytes b => (makeNetmaskBytes bits b, cache)
  | .int v =>
    match cache.lookup v with
    | some p => (.ok p, cache)
    | none => match makeNetmaskInt bits v with
      | .ok p => (.ok p, (v, p) :: cache)
      | .error e => (.error e, cache)
  | .numEq v ty =>
    match cache.lookup v with
    | some p => (.ok p, cache)
    | none => (.error (.named "AttributeError" s!"'{ty}' object has no attribute 'isascii'"), cache)
  | .other ty => (.error (.named "AttributeError" s!"'{ty}' object has no attribute 'isascii'"), cache)
  | .unhashable ty e => (.error (dictUnhashableType ty e), cache)

/-- A cache that only `_make_netmask` filled: each int key holds what the int branch computes. -/
def CacheOk (bits : Nat) (c : NetmaskCache) : Prop :=
  ∀ k p, c.lookup k = some p → makeNetmaskInt bits k = .ok p

/-! ## `_prefix_from_ip_int` -/

theorem testBit_ipIntFromPrefix' (b p i : Nat) :
    (ipIntFromPrefix b p).testBit i = decide (i < b ∧ b ≤ p + i) := by
  simp only [ipIntFromPrefix, allOnes, Nat.testBit_xor, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases h1 : i < b <;> by_cases h2 : p + i < b <;> simp [h1, h2] <;> omega

/-- The netmask of `/p` is `p` ones followed by `bits - p` zeros. -/
theorem ipIntFromPrefix_eq (bits p : Nat) (hp : p ≤ bits) :
    ipIntFromPrefix bits p = (2 ^ p - 1) <<< (bits - p) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_ipIntFromPrefix', Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le]
  constructor
  · intro h; exact ⟨by omega, by omega⟩
  · intro h; exact ⟨by omega, by omega⟩

theorem two_pow_sub_one_odd (p : Nat) (hp : 1 ≤ p) : 2 ^ p - 1 = 2 * (2 ^ (p - 1) - 1) + 1 := by
  have : 2 ^ p = 2 * 2 ^ (p - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  have := Nat.one_le_two_pow (n := p - 1)
  omega

/-- `_prefix_from_ip_int` reads the netmask of `/p` as `p`. -/
theorem prefixFromIpInt_mask (bits p : Nat) (hp : p ≤ bits) :
    prefixFromIpInt bits (ipIntFromPrefix bits p) = .ok p := by
  rw [ipIntFromPrefix_eq bits p hp]
  by_cases h0 : p = 0
  · subst h0
    simp [prefixFromIpInt, countRighthandZeroBits]
  · have e := two_pow_sub_one_odd p (by omega)
    have hz : (2 ^ p - 1) <<< (bits - p) = 2 ^ (bits - p) * (2 * (2 ^ (p - 1) - 1) + 1) := by
      rw [Nat.shiftLeft_eq, Nat.mul_comm, e]
    have hc : countRighthandZeroBits ((2 ^ p - 1) <<< (bits - p)) bits = bits - p := by
      rw [hz, crzb_odd]; omega
    have hsh : (2 ^ p - 1) <<< (bits - p) >>> (bits - p) = 2 ^ p - 1 := Nat.shiftLeft_shiftRight _ _
    have hbp : bits - (bits - p) = p := by omega
    simp only [prefixFromIpInt, hc, hsh, hbp, ne_eq, not_true_eq_false, ↓reduceIte]

/-- `_prefix_from_ip_int` accepts only netmasks. -/
theorem prefixFromIpInt_ok (bits n p : Nat) (h : prefixFromIpInt bits n = .ok p) :
    p ≤ bits ∧ n = ipIntFromPrefix bits p := by
  simp only [prefixFromIpInt] at h
  split at h
  · split at h <;> cases h
  · rename_i hn
    simp only [Except.ok.injEq] at h
    obtain ⟨hr, hd⟩ := crzb_spec n bits
    generalize countRighthandZeroBits n bits = tz at hn h hr hd
    subst h
    refine ⟨Nat.sub_le _ _, ?_⟩
    rw [ipIntFromPrefix_eq bits (bits - tz) (Nat.sub_le _ _), show bits - (bits - tz) = tz by omega]
    have hn' : n >>> tz = 2 ^ (bits - tz) - 1 := by simpa using hn
    rw [← hn', Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    exact (Nat.div_mul_cancel hd).symm

/-- The prefix whose netmask is `n`, found by trying every prefix length: a specification that does
not count bits. -/
def maskPrefix? (bits n : Nat) : Option Nat :=
  (List.range (bits + 1)).find? fun p => ipIntFromPrefix bits p == n

/-- `_prefix_from_ip_int`, ipaddress.py:437-460, docstring "Raises: ValueError: If the input
intermingles zeroes & ones", for `max_prefixlen` 32 and 128 and every int `>= 0`: for every netmask
it returns the prefix length whose netmask is that int; every other int below `2**max_prefixlen` (a
pattern such as `0xff00ff00`, or a hostmask) raises `ValueError('Netmask pattern %r mixes zeroes &
ones')` with the int's big-endian bytes; an int of more bits is never a netmask, and
`to_bytes` (:456) raises `OverflowError('int too big to convert')` for it before the `ValueError`. -/
def PrefixFromIpIntSpec : Prop :=
  ∀ bits : Nat, bits = 32 ∨ bits = 128 → ∀ n : Nat,
    prefixFromIpInt bits n = match maskPrefix? bits n with
      | some p => .ok p
      | none =>
        if n < 2 ^ bits then
          .error (.valueError s!"Netmask pattern {bytesRepr (toBytesBE (bits / 8) n)} mixes zeroes & ones")
        else .error (.overflowError "int too big to convert")

theorem prefixFromIpIntSpec_proven' (bits n : Nat) (hb : bits = 32 ∨ bits = 128) :
    prefixFromIpInt bits n = match maskPrefix? bits n with
      | some p => .ok p
      | none =>
        if n < 2 ^ bits then
          .error (.valueError s!"Netmask pattern {bytesRepr (toBytesBE (bits / 8) n)} mixes zeroes & ones")
        else .error (.overflowError "int too big to convert") := by
  have h256 : 256 ^ (bits / 8) = 2 ^ bits := by rcases hb with rfl | rfl <;> decide
  cases hm : maskPrefix? bits n with
  | some p =>
    unfold maskPrefix? at hm
    have h1 := List.find?_some hm
    have h2 := List.mem_of_find?_eq_some hm
    simp only [beq_iff_eq] at h1
    simp only [List.mem_range] at h2
    rw [← h1]
    exact prefixFromIpInt_mask bits p (by omega)
  | none =>
    unfold maskPrefix? at hm
    rw [List.find?_eq_none] at hm
    cases hr : prefixFromIpInt bits n with
    | ok p =>
      obtain ⟨hp, he⟩ := prefixFromIpInt_ok bits n p hr
      exact absurd (by simp [he]) (hm p (List.mem_range.mpr (by omega)))
    | error e =>
      show Except.error e = (if n < 2 ^ bits then _ else _)
      simp only [prefixFromIpInt] at hr
      split at hr
      · rw [← hr]
        unfold toBytesPy
        rw [h256]
        by_cases hlt : n < 2 ^ bits
        · have h2 : ¬ 2 ^ bits ≤ n := by omega
          simp only [h2, hlt, ↓reduceIte]
        · have h2 : 2 ^ bits ≤ n := by omega
          simp only [h2, hlt, ↓reduceIte]
      · cases hr

theorem prefixFromIpIntSpec_proven : PrefixFromIpIntSpec :=
  fun bits hb n => prefixFromIpIntSpec_proven' bits n hb

/-- Below `2**max_prefixlen`, `_prefix_from_ip_int` never reaches the `OverflowError`. -/
theorem prefixFromIpInt_lt (bits n : Nat) (hb : bits = 32 ∨ bits = 128) (hn : n < 2 ^ bits) :
    prefixFromIpInt bits n = match maskPrefix? bits n with
      | some p => .ok p
      | none => .error (.valueError s!"Netmask pattern {bytesRepr (toBytesBE (bits / 8) n)} mixes zeroes & ones") := by
  rw [prefixFromIpIntSpec_proven' bits n hb]
  cases maskPrefix? bits n with
  | some p => rfl
  | none => simp only [hn, ↓reduceIte]

/-! ## Strings -/

/-- `_prefix_from_prefix_string`, ipaddress.py:467-490, docstring "Raises: NetmaskValueError: If
the input is not a valid netmask", for IPv4 (`maxp = 32`) and IPv6 (`maxp = 128`, which IPv6's
`_make_netmask` passes, :1643): a non-empty string of ASCII digits within the int digit limit is
read as its decimal value if that is at most `maxp` (leading zeros allowed: `int()` accepts them);
everything else, including `''`, signs, spaces, non-ASCII digits and `maxp + 1`, raises
`NetmaskValueError('%r is not a valid netmask')`. And `str(p)` is read back as `p`. -/
def PrefixStringSpec : Prop :=
  ∀ maxp : Nat, maxp = 32 ∨ maxp = 128 →
    (∀ s : List Char, prefixFromPrefixString maxp s =
      if s ≠ [] ∧ s.all isDigitC = true ∧ s.length ≤ intMaxStrDigits ∧ digitsVal s ≤ maxp
      then .ok (digitsVal s) else .error (netmaskErr s)) ∧
    (∀ p : Nat, p ≤ maxp → prefixFromPrefixString maxp (toString p).toList = .ok p)

def prefixB (maxp p : Nat) : Bool :=
  match prefixFromPrefixString maxp (toString p).toList with
  | .ok v => v == p
  | .error _ => false

set_option maxRecDepth 20000 in
theorem prefixB_32 : ∀ p, p < 33 → prefixB 32 p = true := by decide
set_option maxRecDepth 20000 in
theorem prefixB_128 : ∀ p, p < 129 → prefixB 128 p = true := by decide

theorem prefixStringSpec_proven : PrefixStringSpec := by
  intro maxp hm
  refine ⟨fun s => ?_, fun p hp => ?_⟩
  · unfold prefixFromPrefixString reportInvalidNetmask netmaskErr
    by_cases hd : s.all isDigitC = true
    · by_cases he : s = []
      · subst he; simp
      · have hne : s.isEmpty = false := by cases s <;> simp_all
        by_cases hl : s.length > intMaxStrDigits
        · have hl' : ¬ s.length ≤ intMaxStrDigits := by omega
          simp [hd, hne, hl, hl']
        · have hl' : s.length ≤ intMaxStrDigits := by omega
          by_cases hv : digitsVal s ≤ maxp
          · simp [hd, hne, hl, hl', hv, he]
          · simp [hd, hne, hl, hl', hv]
    · have hd' : s.all isDigitC = false := by simpa using hd
      simp [hd']
  · have hb : prefixB maxp p = true := by
      rcases hm with rfl | rfl
      · exact prefixB_32 p (by omega)
      · exact prefixB_128 p (by omega)
    unfold prefixB at hb
    split at hb
    · rename_i v hv; simp only [beq_iff_eq] at hb; rw [hv, hb]
    · cases hb

/-- `ipIntFromString4` reads only dotted quads below `2**32`. -/
theorem ipIntFromString4_lt (s : List Char) (n : Nat) (h : ipIntFromString4 s = .ok n) :
    n < 2 ^ 32 := by
  unfold ipIntFromString4 at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · simp at h
    · rename_i hlen
      split at h
      · rename_i bs hbs
        simp only [Except.ok.injEq] at h
        subst h
        generalize splitOn1 '.' s = parts at hbs hlen
        match parts, hlen, hbs with
        | [o1, o2, o3, o4], _, hbs =>
          cases e1 : parseOctet o1 <;> simp [parseOctets, e1, Except.map] at hbs
          rename_i b1
          cases e2 : parseOctet o2 <;> simp [e2] at hbs
          rename_i b2
          cases e3 : parseOctet o3 <;> simp [e3] at hbs
          rename_i b3
          cases e4 : parseOctet o4 <;> simp [e4] at hbs
          rename_i b4
          subst hbs
          exact (to_from_bytes b1 b2 b3 b4 (octet_canon o1 b1 e1).1 (octet_canon o2 b2 e2).1
            (octet_canon o3 b3 e3).1 (octet_canon o4 b4 e4).1).2
        | [], h, _ | [_], h, _ | [_, _], h, _ | [_, _, _], h, _ => simp at h
        | _ :: _ :: _ :: _ :: _ :: _, h, _ => simp at h
      · simp at h

/-- `_ip_int_from_string` raises only `AddressValueError`. -/
theorem ipIntFromString4_class (s : List Char) :
    (∃ n, ipIntFromString4 s = .ok n) ∨ ∃ m, ipIntFromString4 s = .error (.named "AddressValueError" m) := by
  unfold ipIntFromString4 avErr
  dsimp only
  split
  · exact Or.inr ⟨_, rfl⟩
  · split
    · exact Or.inr ⟨_, rfl⟩
    · split
      · exact Or.inl ⟨_, rfl⟩
      · exact Or.inr ⟨_, rfl⟩

/-- `_prefix_from_ip_string`, ipaddress.py:492-524, docstring "Raises: NetmaskValueError: If the
input is not a valid netmask/hostmask": a string `IPv4Address` refuses, and a dotted quad that is
neither a netmask nor the complement of one, raise `NetmaskValueError('%r is not a valid
netmask')`; a netmask gives its prefix length, and otherwise a hostmask gives the prefix length of
its complement. Stated with `maskPrefix?`, which tries every prefix length. -/
def PrefixFromIpStringSpec : Prop :=
  ∀ s : List Char, prefixFromIpString s =
    match ipIntFromString4 s with
    | .error _ => .error (netmaskErr s)
    | .ok n =>
      match maskPrefix? 32 n with
      | some p => .ok p
      | none =>
        match maskPrefix? 32 (n ^^^ allOnes 32) with
        | some p => .ok p
        | none => .error (netmaskErr s)

theorem prefixFromIpStringSpec_proven : PrefixFromIpStringSpec := by
  intro s
  rcases ipIntFromString4_class s with ⟨n, hn⟩ | ⟨m, hm⟩
  · have hlt := ipIntFromString4_lt s n hn
    have hlt2 : n ^^^ allOnes 32 < 2 ^ 32 := Nat.xor_lt_two_pow hlt (by unfold allOnes; decide)
    simp only [prefixFromIpString, hn, prefixFromIpInt_lt 32 n (Or.inl rfl) hlt,
      prefixFromIpInt_lt 32 _ (Or.inl rfl) hlt2]
    cases maskPrefix? 32 n with
    | some p => rfl
    | none =>
      cases maskPrefix? 32 (n ^^^ allOnes 32) with
      | some p => rfl
      | none => rfl
  · simp only [prefixFromIpString, hm]; rfl

theorem prefixFromPrefixBytes_eq (maxp : Nat) (b : List Nat) :
    prefixFromPrefixBytes maxp b =
      if b ≠ [] ∧ b.all isDigitB = true ∧ b.length ≤ intMaxStrDigits ∧ bytesDigitsVal b ≤ maxp
      then .ok (bytesDigitsVal b)
      else .error (.named "NetmaskValueError" (bytesRepr b ++ " is not a valid netmask")) := by
  unfold prefixFromPrefixBytes reportInvalidNetmask
  by_cases hd : b.all isDigitB = true
  · have ha : b.all isAsciiB = true := by
      rw [List.all_eq_true] at hd ⊢
      intro x hx
      have := hd x hx
      simp only [isDigitB, Bool.and_eq_true, decide_eq_true_eq] at this
      simp only [isAsciiB, decide_eq_true_eq]
      omega
    by_cases he : b = []
    · subst he; simp
    · have hne : b.isEmpty = false := by cases b <;> simp_all
      by_cases hl : b.length > intMaxStrDigits
      · have hl' : ¬ b.length ≤ intMaxStrDigits := by omega
        simp [ha, hd, hne, hl, hl']
      · have hl' : b.length ≤ intMaxStrDigits := by omega
        by_cases hv : bytesDigitsVal b ≤ maxp
        · simp [ha, hd, hne, hl, hl', hv, he]
        · simp [ha, hd, hne, hl, hl', hv]
  · have hd' : b.all isDigitB = false := by simpa using hd
    simp [hd']

/-- `_make_netmask` for every argument, both families, with any cache `_make_netmask` itself
filled (`CacheOk`). An int is its own prefix length in `[0, max_prefixlen]` and otherwise raises
`NetmaskValueError('<n> is not a valid netmask')` (:1163-1167, :1638-1641). A str is, for IPv6, the
prefix length `_prefix_from_prefix_string` reads (:1643), and for IPv4 that or, failing it, the
dotted-quad reading (:1168-1174). A bytes object of at most 4300 ASCII digits whose value is at
most `max_prefixlen` is read as that value (`IPv4Network(('10.0.0.0', b'8'))` is `/8`); any other
bytes raises `NetmaskValueError` with its repr, except that IPv4 then tries the dotted-quad reading,
whose `split('.')` leaks `TypeError` for every non-empty bytes (`b'255.0.0.0'`). A number equal to
an int is the cached prefix length if that int is cached and otherwise raises `AttributeError` at
`isascii()` (`NetmaskCacheTransparent`, refuted), another object without `isascii` raises
`AttributeError`, and one whose hash raises an exact `TypeError` with message `m` raises
`TypeError("cannot use '<qualified type>' as a dict key (<m>)")` at the cache lookup (:1162, :1637;
`dict_unhashable_type`, Objects/dictobject.c:2446-2458), while any other hash exception propagates
unchanged. The netmask is `_ip_int_from_prefix` of the prefix (:1175, :1644). -/
def MaskInt : Prop :=
  ∀ bits : Nat, bits = 32 ∨ bits = 128 → ∀ c : NetmaskCache, CacheOk bits c →
    (∀ p : Int, (makeNetmaskCached bits c (.int p)).1 =
      if 0 ≤ p ∧ p ≤ bits then .ok p.toNat
      else .error (.named "NetmaskValueError" s!"{p} is not a valid netmask")) ∧
    (∀ s : List Char, (makeNetmaskCached bits c (.str s)).1 =
      if bits = 32 then
        match prefixFromPrefixString 32 s with
        | .ok p => .ok p
        | .error _ => prefixFromIpString s
      else prefixFromPrefixString bits s) ∧
    (∀ b : List Nat, (makeNetmaskCached bits c (.bytes b)).1 =
      if b ≠ [] ∧ b.all isDigitB = true ∧ b.length ≤ intMaxStrDigits ∧ bytesDigitsVal b ≤ bits
      then .ok (bytesDigitsVal b)
      else if bits = 32 ∧ b ≠ [] then .error (.typeError "a bytes-like object is required, not 'str'")
      else .error (.named "NetmaskValueError" (bytesRepr b ++ " is not a valid netmask"))) ∧
    (∀ (v : Int) (ty : String), (makeNetmaskCached bits c (.numEq v ty)).1 =
      if (c.lookup v).isSome then .ok v.toNat
      else .error (.named "AttributeError" s!"'{ty}' object has no attribute 'isascii'")) ∧
    (∀ ty : String, (makeNetmaskCached bits c (.other ty)).1 =
      .error (.named "AttributeError" s!"'{ty}' object has no attribute 'isascii'")) ∧
    (∀ (ty m : String), (makeNetmaskCached bits c (.unhashable ty (.typeError m))).1 =
      .error (.typeError s!"cannot use '{ty}' as a dict key ({m})")) ∧
    (∀ (ty : String) (e : PyExc), (∀ m, e ≠ .typeError m) →
      (makeNetmaskCached bits c (.unhashable ty e)).1 = .error e)

theorem maskInt_proven : MaskInt := by
  intro bits hbits c hc
  refine ⟨fun p => ?_, fun s => ?_, fun b => ?_, fun v ty => ?_, fun ty => rfl, fun ty m => rfl, fun ty e he => ?_⟩
  · have hint : makeNetmaskInt bits p = if 0 ≤ p ∧ p ≤ bits then .ok p.toNat
        else .error (.named "NetmaskValueError" s!"{p} is not a valid netmask") := by
      unfold makeNetmaskInt reportInvalidNetmask; split <;> rfl
    simp only [makeNetmaskCached]
    cases hl : c.lookup p with
    | some q => simp only; rw [← hint, hc p q hl]
    | none =>
      simp only
      cases h : makeNetmaskInt bits p with
      | ok q => simp only; rw [← hint, h]
      | error e => simp only; rw [← hint, h]
  · simp only [makeNetmaskCached, makeNetmaskStr]
    split
    · simp only [makeNetmask4]
      rw [(prefixStringSpec_proven 32 (Or.inl rfl)).1 s]
      by_cases hc : s ≠ [] ∧ s.all isDigitC = true ∧ s.length ≤ intMaxStrDigits ∧ digitsVal s ≤ 32
      · rw [if_pos hc]
      · simp only [hc, ↓reduceIte]; rfl
    · rfl
  · -- bytes
    simp only [makeNetmaskCached, makeNetmaskBytes]
    by_cases h32 : bits = 32
    · subst h32
      simp only [eq_self_iff_true, true_and, ↓reduceIte, prefixFromPrefixBytes_eq]
      by_cases hk : b ≠ [] ∧ b.all isDigitB = true ∧ b.length ≤ intMaxStrDigits ∧ bytesDigitsVal b ≤ 32
      · simp only [if_pos hk]
      · simp only [if_neg hk]
        show prefixFromIpBytes4 b = _
        unfold prefixFromIpBytes4 reportInvalidNetmask
        by_cases he : b = []
        · subst he; simp
        · have hne : b.isEmpty = false := by cases b <;> simp_all
          simp [he, hne]
    · have h32' : ¬ (bits = 32 ∧ b ≠ []) := fun h => h32 h.1
      simp only [h32, false_and, ↓reduceIte, h32', prefixFromPrefixBytes_eq]
  · -- a number equal to an int
    simp only [makeNetmaskCached]
    cases hl : c.lookup v with
    | none => simp
    | some p =>
      have h := hc v p hl
      unfold makeNetmaskInt reportInvalidNetmask at h
      split at h
      · cases h; simp
      · cases h
  · -- a hash error other than an exact `TypeError` propagates
    show Except.error (dictUnhashableType ty e) = Except.error e
    cases e <;> first | rfl | exact absurd rfl (he _)

/-- IPv6's cache, as `NetmaskCacheTransparent` is IPv4's: the result of `_BaseV6._make_netmask(arg)`
does not depend on what earlier calls stored. Refuted: `64.0` raises `AttributeError` with an empty
cache and gives 64 once the int 64 is cached (:1637), as for IPv4 (bug
ipaddress-netmask-cache-history). -/
def NetmaskCacheTransparent6 : Prop :=
  ∀ (c1 c2 : NetmaskCache) (a : MaskArg), CacheOk 128 c1 → CacheOk 128 c2 →
    (makeNetmaskCached 128 c1 a).1 = (makeNetmaskCached 128 c2 a).1

theorem netmaskCacheTransparent6_refuted : ¬NetmaskCacheTransparent6 := by
  intro h
  have := h [] [(64, 64)] (.numEq 64 "float") (by intro k p hk; simp at hk) (by
    intro k p hk; simp [List.lookup] at hk; split at hk <;> simp_all [makeNetmaskInt])
  simp [makeNetmaskCached, List.lookup] at this

def okNat (r : Py Nat) (p : Nat) : Bool := match r with | .ok v => v == p | .error _ => false

/-- For every prefix length `p` in `[0, 32]` and every cache, `IPv4Network('a/m')` reads the mask
`m` as `p` when `m` is `str(p)`, the netmask of `/p`, or (for `0 < p < 32`) the hostmask of `/p`.
At `/0` and `/32` the hostmask is the netmask of the other, and the documented exception (all-zero
is a netmask) decides. -/
def MaskRoundTrip : Prop :=
  ∀ c : NetmaskCache, ∀ p, p ≤ 32 →
    okNat (makeNetmaskCached 32 c (.str (toString p).toList)).1 p = true ∧
    okNat (makeNetmaskCached 32 c (.str (stringFromIpInt4 (ipIntFromPrefix 32 p)))).1 p = true ∧
    (1 ≤ p → p ≤ 31 →
      okNat (makeNetmaskCached 32 c (.str (stringFromIpInt4 (ipIntFromPrefix 32 p ^^^ allOnes 32)))).1 p = true)

def maskRT (p : Nat) : Bool :=
  okNat (makeNetmask4 (toString p).toList) p &&
  okNat (makeNetmask4 (stringFromIpInt4 (ipIntFromPrefix 32 p))) p &&
  (!(1 ≤ p && p ≤ 31) || okNat (makeNetmask4 (stringFromIpInt4 (ipIntFromPrefix 32 p ^^^ allOnes 32))) p)

set_option maxRecDepth 100000 in
theorem maskRT_all : ∀ p, p < 33 → maskRT p = true := by decide

theorem maskRoundTrip_proven : MaskRoundTrip := by
  intro c p hp
  have h := maskRT_all p (by omega)
  simp only [maskRT, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun a b => ?_⟩
  rcases h3 with h3 | h3
  · rcases h3 with h3 | h3 <;> simp_all
  · exact h3

/-- The documented rule (Doc/library/ipaddress.rst, IPv4Network): a dotted mask "is interpreted as
a *net mask* if it starts with a non-zero field, or as a *host mask* if it starts with a zero
field, with the single exception of an all-zero mask which is treated as a *net mask*". So a mask
whose first field is non-zero is accepted only if it is a netmask. The code tries the netmask
reading, then the hostmask one, and accepts `127.255.255.255` as the hostmask of `/1`. -/
def DocMaskRule : Prop :=
  ∀ c n p, n < 2 ^ 32 → n / 2 ^ 24 ≠ 0 → (makeNetmaskCached 32 c (.str (stringFromIpInt4 n))).1 = .ok p →
    n = ipIntFromPrefix 32 p

theorem docMaskRule_refuted : ¬ DocMaskRule := by
  intro h
  have := h [] 0x7fffffff 1 (by decide) (by decide) (by decide)
  revert this; decide

/-- The cache is an optimisation: the result of `_make_netmask(arg)` does not depend on what
earlier calls stored. Refuted: `8.0` raises `AttributeError` with an empty cache and gives 8 once
the int 8 is cached (bug ipaddress-netmask-cache-history). -/
def NetmaskCacheTransparent : Prop :=
  ∀ (c1 c2 : NetmaskCache) (a : MaskArg), CacheOk 32 c1 → CacheOk 32 c2 →
    (makeNetmaskCached 32 c1 a).1 = (makeNetmaskCached 32 c2 a).1

theorem netmaskCacheTransparent_refuted : ¬ NetmaskCacheTransparent := by
  intro h
  have := h [] [(8, 8)] (.numEq 8 "float") (by intro k p hk; simp at hk) (by
    intro k p hk; simp [List.lookup] at hk; split at hk <;> simp_all [makeNetmaskInt])
  simp [makeNetmaskCached, List.lookup] at this

end PyLean.Ipaddress
