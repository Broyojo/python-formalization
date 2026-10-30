import PyLean.Core

/-!
Model of the search, split and pad methods of `str`, `bytes` and `bytearray`
in CPython 3.14.7 (`Objects/unicodeobject.c`, `Objects/bytes_methods.c`,
`Objects/bytesobject.c`, `Objects/bytearrayobject.c`, `Objects/stringlib/*.h`).

A `str` is the list of its code points and a `bytes`/`bytearray` the list of
its byte values, both `List Nat`. Argument parsing (`slice_index` clamping,
`Py_ssize_t` and C `int` conversions), index normalisation (`ADJUST_INDICES`),
the `tailmatch` logic, the dispatch between the specialised code paths and the
overflow checks are mirrored from the source.

Abstractions (each one is checked by `difftest/strsearch_diff.py`):
* `FASTSEARCH` (fastsearch.h:772-834: `find_char`, `rfind_char`,
  `default_find`, `adaptive_find`, the two-way algorithm, `default_rfind`,
  `count_char`) is modelled by its result: the first match, the last match, or
  the number of non-overlapping left-to-right matches capped at `maxcount`.
* Inner scanning loops that only look for the next occurrence of a character
  (`memchr`, `findchar`, the `for` loops of `split_char`/`rsplit_char`, the
  heuristic loop of `replace_1char_inplace`) are modelled the same way.
* Allocation failures (`MemoryError`, and `bytes`' "byte string is too large")
  are not modelled; the difftest keeps results small.
* `str` vs `asciilib`/`ucs1lib`/`ucs2lib`/`ucs4lib` instantiations share one
  model: they differ only in the element width.
-/

namespace PyLean.StrSearch

open PyLean

/-- A `str` (code points) or a `bytes`/`bytearray` (byte values). -/
abbrev Seq := List Nat

/-! ## Argument conversion -/

/-- `PyNumber_AsSsize_t(v, NULL)`, used by `_PyEval_SliceIndex`
(Python/ceval.c) for `slice_index` arguments: out-of-range ints are clamped. -/
def clampSsize (x : Int) : Int := max ssizeMin (min ssizeMax x)

/-- `start: slice_index(accept={int, NoneType}, c_default='0') = None`. -/
def argStart : Option Int → Int
  | none => 0
  | some x => clampSsize x

/-- `end: slice_index(accept={int, NoneType}, c_default='PY_SSIZE_T_MAX') = None`. -/
def argEnd : Option Int → Int
  | none => ssizeMax
  | some x => clampSsize x

/-- A `Py_ssize_t` clinic argument (`maxsplit`, `count`, `width`). -/
def argSsize (x : Int) : Py Int :=
  if x < ssizeMin ∨ x > ssizeMax then
    .error (.overflowError "Python int too large to convert to C ssize_t")
  else .ok x

/-- A C `int` clinic argument (`tabsize`). -/
def argCInt (x : Int) : Py Int :=
  if x < -(2 ^ 31) ∨ x > 2 ^ 31 - 1 then
    .error (.overflowError "Python int too large to convert to C int")
  else .ok x

/-- `ADJUST_INDICES`, unicodeobject.c:9662-9678 and bytes_methods.c:434-450. -/
def adjustIndices (start «end» len : Int) : Int × Int :=
  let e := if «end» > len then len
    else if «end» < 0 then (if «end» + len < 0 then 0 else «end» + len)
    else «end»
  let s := if start < 0 then (if start + len < 0 then 0 else start + len) else start
  (s, e)

/-- `str + start` with length `n` (`n ≥ 0`): the C pointer arithmetic. -/
def window (s : Seq) (start n : Int) : Seq := (s.drop start.toNat).take n.toNat

/-! ## Search primitives (the results of `FASTSEARCH`) -/

/-- Offset of the first occurrence of `p` in `s`. -/
def findL (p : Seq) : Seq → Option Nat
  | [] => if p.isPrefixOf [] then some 0 else none
  | c :: cs => if p.isPrefixOf (c :: cs) then some 0 else (findL p cs).map (· + 1)

/-- Offset of the last occurrence of `p` in `s`. -/
def rfindL (p : Seq) : Seq → Option Nat
  | [] => if p.isPrefixOf [] then some 0 else none
  | c :: cs =>
    match rfindL p cs with
    | some i => some (i + 1)
    | none => if p.isPrefixOf (c :: cs) then some 0 else none

theorem findL_le {p s : Seq} {i : Nat} (h : findL p s = some i) : i + p.length ≤ s.length := by
  induction s generalizing i with
  | nil =>
    simp only [findL] at h
    split at h
    · cases h; have := (List.isPrefixOf_iff_prefix.mp ‹_›).length_le; simp only [List.length_nil, List.length_cons] at this ⊢; omega
    · cases h
  | cons c cs ih =>
    simp only [findL] at h
    split at h
    · cases h; have := (List.isPrefixOf_iff_prefix.mp ‹_›).length_le; simp only [List.length_nil, List.length_cons] at this ⊢; omega
    · cases hf : findL p cs with
      | none => simp [hf] at h
      | some j => simp [hf] at h; have := ih hf; simp; omega

theorem rfindL_le {p s : Seq} {i : Nat} (h : rfindL p s = some i) : i + p.length ≤ s.length := by
  induction s generalizing i with
  | nil =>
    simp only [rfindL] at h
    split at h
    · cases h; have := (List.isPrefixOf_iff_prefix.mp ‹_›).length_le; simp only [List.length_nil, List.length_cons] at this ⊢; omega
    · cases h
  | cons c cs ih =>
    simp only [rfindL] at h
    cases hf : rfindL p cs with
    | some j => simp [hf] at h; have := ih hf; simp; omega
    | none =>
      simp only [hf] at h
      split at h
      · cases h; have := (List.isPrefixOf_iff_prefix.mp ‹_›).length_le; simp only [List.length_nil, List.length_cons] at this ⊢; omega
      · cases h

/-- Greedy left-to-right split of `s` at the first `k` occurrences of `p`. -/
def splitN (p : Seq) : Nat → Seq → List Seq
  | 0, s => [s]
  | k + 1, s =>
    match findL p s with
    | none => [s]
    | some i => s.take i :: splitN p k (s.drop (i + p.length))

/-- Number of non-overlapping left-to-right matches, at most `k`. -/
def countN (p : Seq) (k : Nat) (s : Seq) : Nat := (splitN p k s).length - 1

/-- All non-overlapping left-to-right matches (`s.length + 1` bounds them). -/
def countAll (p s : Seq) : Nat := countN p (s.length + 1) s

inductive Mode where
  | count | search | rsearch
  deriving DecidableEq, Repr

def optIdx : Option Nat → Int
  | some i => i
  | none => -1

/-- `FASTSEARCH(s, n, p, m, maxcount, mode)`, fastsearch.h:772-834, by result. -/
def fastsearch (s p : Seq) (maxcount : Int) (mode : Mode) : Int :=
  if s.length < p.length ∨ (mode = .count ∧ maxcount = 0) then -1
  else if p.length = 0 then -1
  else match mode with
    | .search => optIdx (findL p s)
    | .rsearch => optIdx (rfindL p s)
    | .count => min (countAll p s : Int) maxcount

/-- `STRINGLIB(count)`, count.h:13-31. `n` is the (possibly negative) length. -/
def stringlibCount (s : Seq) (n : Int) (p : Seq) (maxcount : Int) : Int :=
  if n < 0 then 0
  else if p.length = 0 then (if n < maxcount then n + 1 else maxcount)
  else
    let c := fastsearch s p maxcount .count
    if c < 0 then 0 else c

/-- `STRINGLIB(find)`, find.h:8-24, with `str = s` and `offset`. -/
def stringlibFind (s p : Seq) (offset : Int) : Int :=
  if p.length = 0 then offset
  else
    let pos := fastsearch s p (-1) .search
    if pos ≥ 0 then pos + offset else pos

/-- `STRINGLIB(rfind)`, find.h:26-42. -/
def stringlibRFind (s p : Seq) (offset : Int) : Int :=
  if p.length = 0 then s.length + offset
  else
    let pos := fastsearch s p (-1) .rsearch
    if pos ≥ 0 then pos + offset else pos

/-- `find_char`/`rfind_char`/`findchar`: index of the first (`dir > 0`) or
last occurrence of `c`, or -1. -/
def findChar (s : Seq) (c : Nat) (forward : Bool) : Int :=
  optIdx (if forward then findL [c] s else rfindL [c] s)

/-! ## `str` representation -/

/-- `PyUnicode_KIND`: 1, 2 or 4 bytes per code point. -/
def kindOf (s : Seq) : Nat :=
  if s.all (· < 256) then 1 else if s.all (· < 65536) then 2 else 4

/-- `PyUnicode_IS_ASCII`. -/
def isAscii (s : Seq) : Bool := s.all (· < 128)

/-- `PyUnicode_MAX_CHAR_VALUE`: the largest code point the representation allows. -/
def maxCharValue (s : Seq) : Nat :=
  if isAscii s then 127 else if kindOf s = 1 then 255 else if kindOf s = 2 then 65535 else 1114111

/-! ## find / rfind / index / rindex / count -/

/-- `any_find_slice`, unicodeobject.c:9681-9761. `forward` is `direction > 0`. -/
def anyFindSlice (s sub : Seq) (start «end» : Int) (forward : Bool) : Int :=
  if kindOf s < kindOf sub then -1
  else
    let (start, «end») := adjustIndices start «end» s.length
    if «end» - start < sub.length then -1
    else if sub.length = 1 then
      let r := findChar (window s start («end» - start)) sub.head! forward
      if r = -1 then -1 else start + r
    else if forward then stringlibFind (window s start («end» - start)) sub start
    else stringlibRFind (window s start («end» - start)) sub start

/-- `str.find` / `str.rfind`, unicodeobject.c:11968-11980 and :13062-13073. -/
def strFind (s sub : Seq) (start «end» : Option Int) (forward : Bool := true) : Int :=
  let r := anyFindSlice s sub (argStart start) (argEnd «end») forward
  if r < 0 then -1 else r

/-- `str.index` / `str.rindex`, unicodeobject.c:12031-12043 and :13083-13096. -/
def strIndex (s sub : Seq) (start «end» : Option Int) (forward : Bool := true) : Py Int :=
  let r := anyFindSlice s sub (argStart start) (argEnd «end») forward
  if r = -1 then .error (.valueError "substring not found") else .ok r

/-- `str.count`, unicodeobject.c:11783-11841. -/
def strCount (s sub : Seq) (start «end» : Option Int) : Int :=
  if kindOf s < kindOf sub then 0
  else
    let (start, «end») := adjustIndices (argStart start) (argEnd «end») s.length
    if «end» - start < sub.length then 0
    else stringlibCount (window s start («end» - start)) («end» - start) sub ssizeMax

/-- The first argument of the `bytes` search methods: an int or a buffer. -/
inductive BSub where
  | byte (v : Int)
  | buf (b : Seq)
  deriving Repr, DecidableEq

/-- `parse_args_finds_byte`, bytes_methods.c:403-431: an int is converted with
`PyNumber_AsSsize_t(sub, NULL)` (clamping) and must lie in `range(0, 256)`. -/
def parseFindsByte : BSub → Py Seq
  | .buf b => .ok b
  | .byte v =>
    let v := clampSsize v
    if v < 0 ∨ v > 255 then .error (.valueError "byte must be in range(0, 256)")
    else .ok [v.toNat]

/-- `find_internal`, bytes_methods.c:452-509. -/
def bytesFindInternal (s : Seq) (sub : BSub) (start «end» : Int) (forward : Bool) : Py Int := do
  let sub ← parseFindsByte sub
  let (start, «end») := adjustIndices start «end» s.length
  if «end» - start < sub.length then return -1
  else if sub.length = 1 then
    let r := findChar (window s start («end» - start)) sub.head! forward
    return if r ≥ 0 then r + start else r
  else if forward then return stringlibFind (window s start («end» - start)) sub start
  else return stringlibRFind (window s start («end» - start)) sub start

/-- `bytes.find` / `bytes.rfind` (and `bytearray`), bytes_methods.c:511-546. -/
def bytesFind (s : Seq) (sub : BSub) (start «end» : Option Int) (forward : Bool := true) : Py Int :=
  bytesFindInternal s sub (argStart start) (argEnd «end») forward

/-- `bytes.index` / `bytes.rindex`, bytes_methods.c:521-560. -/
def bytesIndex (s : Seq) (sub : BSub) (start «end» : Option Int) (forward : Bool := true) : Py Int := do
  let r ← bytesFindInternal s sub (argStart start) (argEnd «end») forward
  if r = -1 then throw (.valueError "subsection not found")
  return r

/-- `_Py_bytes_count`, bytes_methods.c:562-596. -/
def bytesCount (s : Seq) (sub : BSub) (start «end» : Option Int) : Py Int := do
  let sub ← parseFindsByte sub
  let (start, «end») := adjustIndices (argStart start) (argEnd «end») s.length
  return stringlibCount (window s start («end» - start)) («end» - start) sub ssizeMax

/-! ## startswith / endswith -/

/-- The `prefix`/`suffix` argument: one string or a tuple of strings. -/
inductive Affix where
  | one (p : Seq)
  | tuple (ps : List Seq)
  deriving Repr, DecidableEq

/-- `s[i:i+len(p)] == p` for in-range `i ≥ 0` (the `memcmp`). -/
def matchAt (s p : Seq) (i : Int) : Bool := p.isPrefixOf (s.drop i.toNat)

/-- `tailmatch`, unicodeobject.c:9946-10007. The first/last character
comparison before the `memcmp` does not change the result. -/
def strTailmatch (s sub : Seq) (start «end» : Int) (forward : Bool) : Bool :=
  let (start, «end») := adjustIndices start «end» s.length
  let «end» := «end» - sub.length
  if «end» < start then false
  else if sub.length = 0 then true
  else matchAt s sub (if forward then «end» else start)

/-- `tailmatch`, bytes_methods.c:640-686. `forward` is `direction >= 0` (endswith). -/
def bytesTailmatch (s sub : Seq) (start «end» : Int) (forward : Bool) : Bool :=
  let len : Int := s.length
  let slen : Int := sub.length
  let (start, «end») := adjustIndices start «end» len
  if !forward then
    -- startswith
    if start > len - slen then false
    else if «end» - start < slen then false
    else matchAt s sub start
  else
    -- endswith
    if «end» - start < slen ∨ start > len then false
    else
      let start := if «end» - slen > start then «end» - slen else start
      if «end» - start < slen then false
      else matchAt s sub start

/-- The tuple loop of `unicode_startswith_impl`/`unicode_endswith_impl`
(unicodeobject.c:13627-13723) and `_Py_bytes_tailmatch` (bytes_methods.c:688-718). -/
def affixMatch (tm : Seq → Bool) : Affix → Bool
  | .one p => tm p
  | .tuple ps => ps.any tm

def strStartswith (s : Seq) (a : Affix) (start «end» : Option Int) : Bool :=
  affixMatch (fun p => strTailmatch s p (argStart start) (argEnd «end») false) a

def strEndswith (s : Seq) (a : Affix) (start «end» : Option Int) : Bool :=
  affixMatch (fun p => strTailmatch s p (argStart start) (argEnd «end») true) a

def bytesStartswith (s : Seq) (a : Affix) (start «end» : Option Int) : Bool :=
  affixMatch (fun p => bytesTailmatch s p (argStart start) (argEnd «end») false) a

def bytesEndswith (s : Seq) (a : Affix) (start «end» : Option Int) : Bool :=
  affixMatch (fun p => bytesTailmatch s p (argStart start) (argEnd «end») true) a

/-! ## removeprefix / removesuffix -/

/-- `unicode_removeprefix_impl`, unicodeobject.c:12919-12931. -/
def strRemoveprefix (s p : Seq) : Seq :=
  if strTailmatch s p 0 ssizeMax false then s.drop p.length else s

/-- `unicode_removesuffix_impl`, unicodeobject.c:12947-12959. -/
def strRemovesuffix (s p : Seq) : Seq :=
  if strTailmatch s p 0 ssizeMax true then s.take (s.length - p.length) else s

/-- `bytes_removeprefix_impl`, bytesobject.c:2340-2360 (and bytearray). -/
def bytesRemoveprefix (s p : Seq) : Seq :=
  if s.length ≥ p.length ∧ p.length > 0 ∧ p.isPrefixOf s then s.drop p.length else s

/-- `bytes_removesuffix_impl`, bytesobject.c:2377-2398 (and bytearray). -/
def bytesRemovesuffix (s p : Seq) : Seq :=
  if s.length ≥ p.length ∧ p.length > 0 ∧ p.isPrefixOf (s.drop (s.length - p.length))
  then s.take (s.length - p.length) else s

/-! ## partition / rpartition -/

/-- `STRINGLIB(partition)`, partition.h:12-66. -/
def stringlibPartition (s sep : Seq) : Py (Seq × Seq × Seq) :=
  if sep.length = 0 then .error (.valueError "empty separator")
  else
    let pos := fastsearch s sep (-1) .search
    if pos < 0 then .ok (s, [], [])
    else .ok (s.take pos.toNat, sep, s.drop (pos.toNat + sep.length))

/-- `STRINGLIB(rpartition)`, partition.h:68-123. -/
def stringlibRPartition (s sep : Seq) : Py (Seq × Seq × Seq) :=
  if sep.length = 0 then .error (.valueError "empty separator")
  else
    let pos := fastsearch s sep (-1) .rsearch
    if pos < 0 then .ok ([], [], s)
    else .ok (s.take pos.toNat, sep, s.drop (pos.toNat + sep.length))

/-- `PyUnicode_Partition`, unicodeobject.c:13168-13218. -/
def strPartition (s sep : Seq) : Py (Seq × Seq × Seq) :=
  if kindOf s < kindOf sep ∨ s.length < sep.length then .ok (s, [], [])
  else stringlibPartition s sep

/-- `PyUnicode_RPartition`, unicodeobject.c:13221-13271. -/
def strRPartition (s sep : Seq) : Py (Seq × Seq × Seq) :=
  if kindOf s < kindOf sep ∨ s.length < sep.length then .ok ([], [], s)
  else stringlibRPartition s sep

/-- `bytes.partition`/`bytearray.partition`: `stringlib_partition` on the
buffer (bytesobject.c:1808-1815, bytearrayobject.c:1806-1824). -/
def bytesPartition (s sep : Seq) : Py (Seq × Seq × Seq) := stringlibPartition s sep

def bytesRPartition (s sep : Seq) : Py (Seq × Seq × Seq) := stringlibRPartition s sep

/-! ## split / rsplit -/

/-- `Py_UNICODE_ISSPACE` (`str.isspace` of one code point). -/
def uniSpace (c : Nat) : Bool :=
  (9 ≤ c ∧ c ≤ 13) || (0x1c ≤ c ∧ c ≤ 0x20) || c == 0x85 || c == 0xa0 || c == 0x1680 ||
  (0x2000 ≤ c ∧ c ≤ 0x200a) || c == 0x2028 || c == 0x2029 || c == 0x202f ||
  c == 0x205f || c == 0x3000

/-- `Py_ISSPACE` (pyctype.h): ASCII whitespace, as used by `bytes`. -/
def byteSpace (c : Nat) : Bool := (9 ≤ c ∧ c ≤ 13) || c == 32

/-- `_Py_ascii_whitespace`, unicodeobject.c:470-505, used by the ASCII fast
path of `str.strip()`. -/
def asciiWhitespaceTable (c : Nat) : Bool := c < 128 && ((9 ≤ c ∧ c ≤ 13) || (0x1c ≤ c ∧ c ≤ 0x20))


/-- `Py_UNICODE_ISLINEBREAK` / `BLOOM_LINEBREAK`, used by `str.splitlines`. -/
def uniLinebreak (c : Nat) : Bool :=
  (10 ≤ c ∧ c ≤ 13) || (0x1c ≤ c ∧ c ≤ 0x1e) || c == 0x85 || c == 0x2028 || c == 0x2029

/-- `STRINGLIB_ISLINEBREAK` of stringdefs.h:17, used by `bytes.splitlines`. -/
def byteLinebreak (c : Nat) : Bool := c == 10 || c == 13

theorem dropWhile_length_le (f : Nat → Bool) (l : Seq) : (l.dropWhile f).length ≤ l.length :=
  (List.dropWhile_suffix f).length_le

/-- `STRINGLIB(split_whitespace)`, split.h:53-98, on the remainder `str + i`.
The loop body runs while `maxcount-- > 0`; afterwards a non-empty remainder
(minus leading whitespace) becomes the last piece. -/
def splitWs (isSp : Nat → Bool) (maxcount : Int) (rest : Seq) : List Seq :=
  if maxcount > 0 then
    match h : rest.dropWhile isSp with
    | [] => []
    | c :: cs => (c :: cs.takeWhile (fun x => !isSp x)) ::
        splitWs isSp (maxcount - 1) (cs.dropWhile (fun x => !isSp x))
  else
    let r := rest.dropWhile isSp
    if r = [] then [] else [r]
termination_by rest.length
decreasing_by
  have h1 := dropWhile_length_le (fun x => !isSp x) cs
  have h2 := dropWhile_length_le isSp rest
  rw [h] at h2; simp at h2; omega

/-- `STRINGLIB(rsplit_whitespace)`, split.h:194-238: the mirror image of
`split_whitespace` (scanning from the right, collecting pieces right to left,
then `PyList_Reverse`). -/
def rsplitWs (isSp : Nat → Bool) (maxcount : Int) (s : Seq) : List Seq :=
  ((splitWs isSp maxcount s.reverse).map List.reverse).reverse

/-- `STRINGLIB(split_char)`, split.h:100-140, on the remainder `str + i`
(`i = j` at the top of each outer iteration). The outer loop runs while
`j < str_len && maxcount-- > 0`; the final `SPLIT_ADD(str, i, str_len)` always runs. -/
def splitChar (ch : Nat) (maxcount : Int) (rest : Seq) : List Seq :=
  if rest ≠ [] ∧ maxcount > 0 then
    match h : findL [ch] rest with
    | some k => rest.take k :: splitChar ch (maxcount - 1) (rest.drop (k + 1))
    | none => [rest]
  else [rest]
termination_by rest.length
decreasing_by have := findL_le h; simp at this ⊢; omega

/-- The loop of `STRINGLIB(split)`, split.h:160-169, on the remainder `str + i`. -/
def splitLoop (sep : Seq) (maxcount : Int) (rest : Seq) : List Seq :=
  if maxcount > 0 ∧ sep ≠ [] then
    match h : findL sep rest with
    | some pos => rest.take pos :: splitLoop sep (maxcount - 1) (rest.drop (pos + sep.length))
    | none => [rest]
  else [rest]
termination_by rest.length
decreasing_by
  have := findL_le h
  have : sep.length ≥ 1 := List.length_pos_iff.mpr ‹maxcount > 0 ∧ sep ≠ []›.2
  simp; omega

/-- `STRINGLIB(split)`, split.h:142-186. -/
def stringlibSplit (s sep : Seq) (maxcount : Int) : Py (List Seq) :=
  if sep.length = 0 then .error (.valueError "empty separator")
  else if sep.length = 1 then .ok (splitChar sep.head! maxcount s)
  else .ok (splitLoop sep maxcount s)

/-- `STRINGLIB(rsplit_char)`, split.h:240-277, on the prefix `str[:j+1]`;
pieces are collected right to left. -/
def rsplitCharLoop (ch : Nat) (maxcount : Int) (pre : Seq) : List Seq :=
  if pre ≠ [] ∧ maxcount > 0 then
    match h : rfindL [ch] pre with
    | some k => pre.drop (k + 1) :: rsplitCharLoop ch (maxcount - 1) (pre.take k)
    | none => [pre]
  else [pre]
termination_by pre.length
decreasing_by have := rfindL_le h; simp at this ⊢; omega

/-- The loop of `STRINGLIB(rsplit)`, split.h:296-305, on the prefix `str[:j]`;
pieces are collected right to left. -/
def rsplitLoop (sep : Seq) (maxcount : Int) (pre : Seq) : List Seq :=
  if maxcount > 0 ∧ sep ≠ [] then
    match h : rfindL sep pre with
    | some pos => pre.drop (pos + sep.length) :: rsplitLoop sep (maxcount - 1) (pre.take pos)
    | none => [pre]
  else [pre]
termination_by pre.length
decreasing_by
  have := rfindL_le h
  have : sep.length ≥ 1 := List.length_pos_iff.mpr ‹maxcount > 0 ∧ sep ≠ []›.2
  simp; omega

/-- `STRINGLIB(rsplit)`, split.h:279-322 (including the final `PyList_Reverse`). -/
def stringlibRSplit (s sep : Seq) (maxcount : Int) : Py (List Seq) :=
  if sep.length = 0 then .error (.valueError "empty separator")
  else if sep.length = 1 then .ok (rsplitCharLoop sep.head! maxcount s).reverse
  else .ok (rsplitLoop sep maxcount s).reverse

/-- `maxcount` for `str.split()`/`str.rsplit()` without a separator:
`(len1 - 1) / 2 + 1` in C division (unicodeobject.c:10579-10581). -/
def strWsMaxcount (len : Nat) (maxcount : Int) : Int :=
  if maxcount < 0 then Int.tdiv ((len : Int) - 1) 2 + 1 else maxcount

/-- `maxcount` for `str.split(sep)`: `len1 / len2 + 1`, and `len1` if that
overflowed (unicodeobject.c:10609-10614). -/
def strSepMaxcount (len1 len2 : Nat) (maxcount : Int) : Int :=
  if maxcount < 0 then
    let m : Int := if len2 = 0 then 0 else (len1 / len2 : Nat) + 1
    if m > ssizeMax then len1 else m
  else maxcount

/-- `str.split`, unicodeobject.c:10568-10658 and :13153-13165. -/
def strSplit (s : Seq) (sep : Option Seq) (maxsplit : Int) : Py (List Seq) := do
  let maxcount ← argSsize maxsplit
  match sep with
  | none => return splitWs uniSpace (strWsMaxcount s.length maxcount) s
  | some sep =>
    let maxcount := strSepMaxcount s.length sep.length maxcount
    if kindOf s < kindOf sep ∨ s.length < sep.length then return [s]
    stringlibSplit s sep maxcount

/-- `str.rsplit`, unicodeobject.c:10660-10750. -/
def strRSplit (s : Seq) (sep : Option Seq) (maxsplit : Int) : Py (List Seq) := do
  let maxcount ← argSsize maxsplit
  match sep with
  | none => return rsplitWs uniSpace (strWsMaxcount s.length maxcount) s
  | some sep =>
    let maxcount := strSepMaxcount s.length sep.length maxcount
    if kindOf s < kindOf sep ∨ s.length < sep.length then return [s]
    stringlibRSplit s sep maxcount

/-- `bytes.split` (bytesobject.c:1769-1789) and `bytearray.split`
(bytearrayobject.c:1754-1784). -/
def bytesSplit (s : Seq) (sep : Option Seq) (maxsplit : Int) : Py (List Seq) := do
  let maxsplit ← argSsize maxsplit
  let maxsplit := if maxsplit < 0 then ssizeMax else maxsplit
  match sep with
  | none => return splitWs byteSpace maxsplit s
  | some sep => stringlibSplit s sep maxsplit

/-- `bytes.rsplit` (bytesobject.c:1856-1876) and `bytearray.rsplit`. -/
def bytesRSplit (s : Seq) (sep : Option Seq) (maxsplit : Int) : Py (List Seq) := do
  let maxsplit ← argSsize maxsplit
  let maxsplit := if maxsplit < 0 then ssizeMax else maxsplit
  match sep with
  | none => return rsplitWs byteSpace maxsplit s
  | some sep => stringlibRSplit s sep maxsplit

/-! ## splitlines -/

/-- One iteration of the loop of `STRINGLIB(splitlines)`, split.h:340-381:
the line (with its line break if `keepends`; `\r\n` counts as one break) and
the remainder `str + i`. -/
def lineBreak (isLB : Nat → Bool) (keepends : Bool) (s : Seq) : Seq × Seq :=
  let line := s.takeWhile (fun x => !isLB x)
  match s.dropWhile (fun x => !isLB x) with
  | [] => (line, [])
  | c :: cs =>
    if c = 13 ∧ cs.head? = some 10 then (if keepends then line ++ [13, 10] else line, cs.drop 1)
    else (if keepends then line ++ [c] else line, cs)

theorem lineBreak_snd (isLB : Nat → Bool) (keepends : Bool) (s : Seq) :
    (lineBreak isLB keepends s).2 = [] ∨
    ∃ c cs, s.dropWhile (fun x => !isLB x) = c :: cs ∧
      ((lineBreak isLB keepends s).2 = cs ∨ (lineBreak isLB keepends s).2 = cs.drop 1) := by
  unfold lineBreak
  split
  · exact Or.inl rfl
  · next c cs h =>
    refine Or.inr ⟨c, cs, h, ?_⟩
    split
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem lineBreak_snd_len (isLB : Nat → Bool) (keepends : Bool) {s : Seq} (hs : s ≠ []) :
    (lineBreak isLB keepends s).2.length < s.length := by
  rcases lineBreak_snd isLB keepends s with h | ⟨c, cs, h1, h2 | h2⟩
  · rw [h]; exact List.length_pos_iff.mpr hs
  · have := (List.dropWhile_suffix (l := s) (fun x => !isLB x)).length_le
    rw [h1] at this; rw [h2]; simp at this; omega
  · have := (List.dropWhile_suffix (l := s) (fun x => !isLB x)).length_le
    rw [h1] at this; rw [h2]; simp at this ⊢; omega

theorem lineBreak_snd_mem (isLB : Nat → Bool) (keepends : Bool) {s : Seq} {x : Nat}
    (hx : x ∈ (lineBreak isLB keepends s).2) : x ∈ s := by
  rcases lineBreak_snd isLB keepends s with h | ⟨c, cs, h1, h2 | h2⟩
  · rw [h] at hx; simp at hx
  · have := (List.dropWhile_suffix (l := s) (fun x => !isLB x)).subset
    rw [h1] at this; rw [h2] at hx; exact this (List.mem_cons_of_mem c hx)
  · have := (List.dropWhile_suffix (l := s) (fun x => !isLB x)).subset
    rw [h1] at this; rw [h2] at hx; exact this (List.mem_cons_of_mem c (List.mem_of_mem_drop hx))

/-- `STRINGLIB(splitlines)`, split.h:324-388: the loop `for (i = j = 0; i < str_len; )`
on the remainder `str + j`. -/
def splitlines (isLB : Nat → Bool) (keepends : Bool) (s : Seq) : List Seq :=
  if h : s = [] then []
  else (lineBreak isLB keepends s).1 :: splitlines isLB keepends (lineBreak isLB keepends s).2
termination_by s.length
decreasing_by exact lineBreak_snd_len isLB keepends h

def strSplitlines (s : Seq) (keepends : Bool) : List Seq := splitlines uniLinebreak keepends s
def bytesSplitlines (s : Seq) (keepends : Bool) : List Seq := splitlines byteLinebreak keepends s

/-! ## replace -/

/-- `replace_1char_inplace` (stringlib/replace.h:7-56) and
`stringlib_replace_single_character_in_place` (transmogrify.h:422-461), by
result: the first `maxcount` occurrences of `u1` become `u2`. -/
def replaceChars (u1 u2 : Nat) : Int → Seq → Seq
  | _, [] => []
  | mc, c :: cs =>
    if c = u1 ∧ mc > 0 then u2 :: replaceChars u1 u2 (mc - 1) cs
    else c :: replaceChars u1 u2 mc cs

/-- The `while (--maxcount > 0)` loop of the equal-length substring
replacement (unicodeobject.c:10927-10937, transmogrify.h:500-509), on the
remainder after the first match. -/
def replaceInplace (old new : Seq) (maxcount : Int) (rest : Seq) : Seq :=
  if maxcount > 0 ∧ old ≠ [] then
    match h : findL old rest with
    | some j => rest.take j ++ new ++ replaceInplace old new (maxcount - 1) (rest.drop (j + old.length))
    | none => rest
  else rest
termination_by rest.length
decreasing_by
  have := findL_le h
  have : old.length ≥ 1 := List.length_pos_iff.mpr ‹maxcount > 0 ∧ old ≠ []›.2
  simp; omega

/-- The copy loop that performs `n` counted replacements
(unicodeobject.c:10991-11021, transmogrify.h:402-418, :564-587, :656-680). -/
def replaceLoop (old new : Seq) : Nat → Seq → Seq
  | 0, rest => rest
  | n + 1, rest =>
    match findL old rest with
    | none => rest
    | some j => rest.take j ++ new ++ replaceLoop old new n (rest.drop (j + old.length))

/-- Insert `new` before each of the first `n` characters (and at the end if
`n = len + 1`): unicodeobject.c:11023-11040, transmogrify.h:310-336. -/
def interleave (new : Seq) : Nat → Seq → Seq
  | 0, rest => rest
  | n + 1, rest => new ++ (if n = 0 then rest else rest.take 1 ++ interleave new n (rest.drop 1))

/-- `str.replace`: `replace`, unicodeobject.c:10811-11067. The
`if (str1 == str2) goto nothing` identity shortcut (:10835) is omitted:
replacing a string by an equal one yields the same value. -/
def strReplace (s old new : Seq) (count : Int) : Py Seq := do
  let maxcount ← argSsize count
  let slen := s.length
  let len1 := old.length
  let len2 := new.length
  if slen < len1 then return s
  let maxcount := if maxcount < 0 then ssizeMax else maxcount
  if maxcount = 0 then return s
  if maxCharValue s < maxCharValue old then return s
  if len1 = len2 then
    if len1 = 0 then return s
    if len1 = 1 then
      let pos := findChar s old.head! true
      if pos < 0 then return s
      return s.take pos.toNat ++ replaceChars old.head! new.head! maxcount (s.drop pos.toNat)
    else
      let i := stringlibFind s old 0
      if i < 0 then return s
      return s.take i.toNat ++ new ++ replaceInplace old new (maxcount - 1) (s.drop (i.toNat + len1))
  else
    let rkind : Int := max (kindOf s) (kindOf new)
    let n := stringlibCount s slen old maxcount
    if n = 0 then return s
    if len1 < len2 ∧ ((len2 : Int) - len1) > (ssizeMax - slen) / n then
      throw (.overflowError "replace string is too long")
    let newSize : Int := slen + n * ((len2 : Int) - len1)
    if newSize = 0 then return []
    if newSize > ssizeMax / rkind then throw (.overflowError "replace string is too long")
    if len1 > 0 then return replaceLoop old new n.toNat s
    else return interleave new n.toNat s

/-- `countchar`, transmogrify.h:256-271. -/
def countChar (s : Seq) (c : Nat) (maxcount : Int) : Int := min ((s.filter (· == c)).length : Int) maxcount

/-- `stringlib_replace`, transmogrify.h:681-737, with its seven helpers
(transmogrify.h:276-679); used by `bytes.replace` and `bytearray.replace`. -/
def bytesReplace (s old new : Seq) (count : Int) : Py Seq := do
  let maxcount ← argSsize count
  let selfLen : Int := s.length
  let fromLen : Int := old.length
  let toLen : Int := new.length
  if selfLen < fromLen then return s
  let maxcount := if maxcount < 0 then ssizeMax else maxcount
  if maxcount = 0 then return s
  if fromLen = 0 then
    if toLen = 0 then return s
    -- stringlib_replace_interleave, transmogrify.h:276-337
    let cnt : Int := if maxcount ≤ selfLen then maxcount else selfLen + 1
    if toLen > (ssizeMax - selfLen) / cnt then throw (.overflowError "replace bytes is too long")
    return interleave new cnt.toNat s
  if toLen = 0 then
    if fromLen = 1 then
      -- stringlib_replace_delete_single_character, transmogrify.h:341-379
      let cnt := countChar s old.head! maxcount
      if cnt = 0 then return s
      return replaceLoop old [] cnt.toNat s
    else
      -- stringlib_replace_delete_substring, transmogrify.h:383-420
      let cnt := stringlibCount s selfLen old maxcount
      if cnt = 0 then return s
      return replaceLoop old [] cnt.toNat s
  if fromLen = toLen then
    if fromLen = 1 then
      -- stringlib_replace_single_character_in_place, transmogrify.h:422-461
      let next := findChar s old.head! true
      if next < 0 then return s
      return s.take next.toNat ++ replaceChars old.head! new.head! maxcount (s.drop next.toNat)
    else
      -- stringlib_replace_substring_in_place, transmogrify.h:463-512
      let offset := stringlibFind s old 0
      if offset = -1 then return s
      return s.take offset.toNat ++ new ++
        replaceInplace old new (maxcount - 1) (s.drop (offset.toNat + old.length))
  if fromLen = 1 then
    -- stringlib_replace_single_character, transmogrify.h:514-590
    let cnt := countChar s old.head! maxcount
    if cnt = 0 then return s
    if toLen - 1 > (ssizeMax - selfLen) / cnt then throw (.overflowError "replace bytes is too long")
    return replaceLoop old new cnt.toNat s
  else
    -- stringlib_replace_substring, transmogrify.h:592-679
    let cnt := stringlibCount s selfLen old maxcount
    if cnt = 0 then return s
    if toLen - fromLen > (ssizeMax - selfLen) / cnt then throw (.overflowError "replace bytes is too long")
    return replaceLoop old new cnt.toNat s

/-! ## expandtabs -/

/-- First pass of `unicode_expandtabs_impl`, unicodeobject.c:11893-11917:
the output size `j` (`none` on `goto overflow`) and whether a tab was seen. -/
def strExpandSize (tabsize : Int) : Seq → Int → Int → Bool → Option (Int × Bool)
  | [], j, _, found => some (j, found)
  | ch :: rest, j, linePos, found =>
    if ch = 9 then
      if tabsize > 0 then
        let incr := tabsize - linePos % tabsize
        if j > ssizeMax - incr then none
        else strExpandSize tabsize rest (j + incr) (linePos + incr) true
      else strExpandSize tabsize rest j linePos true
    else if j > ssizeMax - 1 then none
    else strExpandSize tabsize rest (j + 1) (if ch = 10 ∨ ch = 13 then 0 else linePos + 1) found

/-- First pass of `stringlib_expandtabs_impl`, transmogrify.h:44-70: `i` is
the size of the completed lines, `j` the current column. -/
def bytesExpandSize (tabsize : Int) : Seq → Int → Int → Option Int
  | [], i, j => if i > ssizeMax - j then none else some (i + j)
  | ch :: rest, i, j =>
    if ch = 9 then
      if tabsize > 0 then
        let incr := tabsize - j % tabsize
        if j > ssizeMax - incr then none
        else bytesExpandSize tabsize rest i (j + incr)
      else bytesExpandSize tabsize rest i j
    else if j > ssizeMax - 1 then none
    else if ch = 10 ∨ ch = 13 then
      if i > ssizeMax - (j + 1) then none
      else bytesExpandSize tabsize rest (i + (j + 1)) 0
    else bytesExpandSize tabsize rest i (j + 1)

/-- Second pass, identical in unicodeobject.c:11926-11942 and transmogrify.h:79-93. -/
def expandFill (tabsize : Int) : Seq → Int → Seq
  | [], _ => []
  | ch :: rest, col =>
    if ch = 9 then
      if tabsize > 0 then
        let incr := tabsize - col % tabsize
        List.replicate incr.toNat 32 ++ expandFill tabsize rest (col + incr)
      else expandFill tabsize rest col
    else ch :: expandFill tabsize rest (if ch = 10 ∨ ch = 13 then 0 else col + 1)

/-- `str.expandtabs`, unicodeobject.c:11882-11948. -/
def strExpandtabs (s : Seq) (tabsize : Int) : Py Seq := do
  let tabsize ← argCInt tabsize
  match strExpandSize tabsize s 0 0 false with
  | none => throw (.overflowError "new string is too long")
  | some (_, false) => return s
  | some (_, true) => return expandFill tabsize s 0

/-- `bytes.expandtabs`/`bytearray.expandtabs`, transmogrify.h:36-98. -/
def bytesExpandtabs (s : Seq) (tabsize : Int) : Py Seq := do
  let tabsize ← argCInt tabsize
  match bytesExpandSize tabsize s 0 0 with
  | none => throw (.overflowError "result too long")
  | some _ => return expandFill tabsize s 0

/-! ## Padding -/

/-- `pad`, unicodeobject.c:10492-10531. -/
def strPad (s : Seq) (left right : Int) (fill : Nat) : Py Seq :=
  let left := if left < 0 then 0 else left
  let right := if right < 0 then 0 else right
  if left = 0 ∧ right = 0 then .ok s
  else if left > ssizeMax - s.length ∨ right > ssizeMax - (left + s.length) then
    .error (.overflowError "padded string is too long")
  else .ok (List.replicate left.toNat fill ++ s ++ List.replicate right.toNat fill)

/-- `pad`, transmogrify.h:103-130 (no overflow check). -/
def bytesPad (s : Seq) (left right : Int) (fill : Nat) : Seq :=
  let left := if left < 0 then 0 else left
  let right := if right < 0 then 0 else right
  if left = 0 ∧ right = 0 then s
  else List.replicate left.toNat fill ++ s ++ List.replicate right.toNat fill

/-- `left = marg / 2 + (marg & width & 1)` for `marg, width > 0`. -/
def centerLeft (marg width : Int) : Int :=
  marg / 2 + ((marg.toNat &&& width.toNat &&& 1 : Nat) : Int)

/-- `str.center`, unicodeobject.c:11176-11188. -/
def strCenter (s : Seq) (width : Int) (fill : Nat := 32) : Py Seq := do
  let width ← argSsize width
  if s.length ≥ width then return s
  let marg := width - s.length
  let left := centerLeft marg width
  strPad s left (marg - left) fill

/-- `str.ljust`, unicodeobject.c:12561-12568. -/
def strLjust (s : Seq) (width : Int) (fill : Nat := 32) : Py Seq := do
  let width ← argSsize width
  if s.length ≥ width then return s
  strPad s 0 (width - s.length) fill

/-- `str.rjust`, unicodeobject.c:13110-13117. -/
def strRjust (s : Seq) (width : Int) (fill : Nat := 32) : Py Seq := do
  let width ← argSsize width
  if s.length ≥ width then return s
  strPad s (width - s.length) 0 fill

/-- Moving the sign: `if (u[fill] == '+' || u[fill] == '-') { u[0] = u[fill];
u[fill] = '0'; }`. When `s` is empty `u[fill]` is the terminating NUL. -/
def zfillSign (u : Seq) (fill : Nat) : Seq :=
  let chr := u.getD fill 0
  if chr = 43 ∨ chr = 45 then (u.set 0 chr).set fill 48 else u

/-- `str.zfill`, unicodeobject.c:13577-13608. -/
def strZfill (s : Seq) (width : Int) : Py Seq := do
  let width ← argSsize width
  if s.length ≥ width then return s
  let fill := width - s.length
  let u ← strPad s fill 0 48
  return zfillSign u fill.toNat

/-- `bytes.center`, transmogrify.h:184-207. -/
def bytesCenter (s : Seq) (width : Int) (fill : Nat := 32) : Py Seq := do
  let width ← argSsize width
  if s.length ≥ width then return s
  let marg := width - s.length
  let left := centerLeft marg width
  return bytesPad s left (marg - left) fill

/-- `bytes.ljust`, transmogrify.h:144-152. -/
def bytesLjust (s : Seq) (width : Int) (fill : Nat := 32) : Py Seq := do
  let width ← argSsize width
  if s.length ≥ width then return s
  return bytesPad s 0 (width - s.length) fill

/-- `bytes.rjust`, transmogrify.h:167-175. -/
def bytesRjust (s : Seq) (width : Int) (fill : Nat := 32) : Py Seq := do
  let width ← argSsize width
  if s.length ≥ width then return s
  return bytesPad s (width - s.length) 0 fill

/-- `bytes.zfill`, transmogrify.h:220-246. -/
def bytesZfill (s : Seq) (width : Int) : Py Seq := do
  let width ← argSsize width
  if s.length ≥ width then return s
  let fill := width - s.length
  return zfillSign (bytesPad s fill 0 48) fill.toNat

/-! ## strip -/

inductive StripType where
  | left | right | both
  deriving DecidableEq, Repr

/-- The two index loops shared by every strip implementation: `i` advances
over leading members, then `j` moves back from the end while `j >= i`. -/
def stripWith (mem : Nat → Bool) (t : StripType) (s : Seq) : Seq :=
  let i := if t ≠ .right then (s.takeWhile mem).length else 0
  let j := if t ≠ .left then i + ((s.drop i).reverse.dropWhile mem).length else s.length
  (s.drop i).take (j - i)

/-- `str.strip`/`lstrip`/`rstrip`: `do_strip` (unicodeobject.c:12677-12729,
ASCII fast path with `_Py_ascii_whitespace`) for `chars=None`, else
`_PyUnicode_XStrip` (:12596-12640). -/
def strStrip (s : Seq) (chars : Option Seq) (t : StripType) : Seq :=
  match chars with
  | none => if isAscii s then stripWith asciiWhitespaceTable t s else stripWith uniSpace t s
  | some cs => stripWith (fun c => cs.contains c) t s

/-- `bytes.strip`...: `do_strip` (bytesobject.c:2034-2061) and `do_xstrip` (:1994-2031). -/
def bytesStrip (s : Seq) (chars : Option Seq) (t : StripType) : Seq :=
  match chars with
  | none => stripWith byteSpace t s
  | some cs => stripWith (fun c => cs.contains c) t s

/-- `bytearray_strip_impl_helper`, bytearrayobject.c:2320-2356: `None` means
the six bytes of `"\t\n\r\f\v "`. -/
def bytearrayStrip (s : Seq) (chars : Option Seq) (t : StripType) : Seq :=
  let cs := chars.getD [9, 10, 13, 12, 11, 32]
  stripWith (fun c => cs.contains c) t s

end PyLean.StrSearch
