import PyLean.BytesObj.Bytes.Escape

/-!
`bytes.fromhex`/`bytearray.fromhex` (`_PyBytes_FromHex`, Objects/bytesobject.c:2519-2628)
and `hex` (`_Py_strhex_impl`, Python/pystrhex.c:7-143).

`_PyBytes_FromHex` walks a raw pointer. Its loop tests `str < end` only at the
top, so it can read `*str` at `end`: harmless for a NUL-terminated `str`, `bytes`
or `bytearray`, but for a buffer that is not NUL-terminated it reads whatever is
stored after the view. The model therefore parses `mem = data ++ after`, where
`after` is the memory that follows the data, and a read past `mem` is `cUB`.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-- A read at `i`; past the allocation it is undefined. -/
def memRead (mem : Seq) (i : Nat) : Py Nat :=
  match mem[i]? with
  | some c => .ok c
  | none => .error (Sequences.cUB "read past the buffer")

/-- `do { str++; } while (Py_ISSPACE(*str));`, bytesobject.c:2578-2580. -/
def skipSpaces (mem : Seq) : Nat → Nat → Py Nat
  | 0, _ => .error .modelFuel
  | fuel + 1, i =>
    match memRead mem (i + 1) with
    | .error e => .error e
    | .ok c => if isSpaceC c then skipSpaces mem fuel (i + 1) else .ok (i + 1)

def invalidAt (i : Nat) : PyExc :=
  .valueError s!"non-hexadecimal number found in fromhex() arg at position {i}"

def oddDigits : PyExc :=
  .valueError "fromhex() arg must contain an even number of hexadecimal digits"

/-- The loop of `_PyBytes_FromHex`, bytesobject.c:2575-2605. `len` is `hexlen`,
`i` is `str - start`. -/
def fromHexLoop (mem : Seq) (len : Nat) : Nat → Nat → Seq → Py Seq
  | 0, _, _ => .error .modelFuel
  | fuel + 1, i, out =>
    if i < len then
      match memRead mem i with
      | .error e => .error e
      | .ok c =>
        let afterSpace : Py Nat := if isSpaceC c then skipSpaces mem (mem.length + 1) i else .ok i
        match afterSpace with
        | .error e => .error e
        | .ok i =>
          if i ≥ len ∧ isSpaceC c then .ok out
          else
            match memRead mem i with
            | .error e => .error e
            | .ok t =>
              let top := digitValue t
              if top ≥ 16 then .error (invalidAt i)
              else
                match memRead mem (i + 1) with
                | .error e => .error e
                | .ok b =>
                  let bot := digitValue b
                  if bot ≥ 16 then
                    if i + 1 ≥ len then .error oddDigits else .error (invalidAt (i + 1))
                  else fromHexLoop mem len fuel (i + 2) (out ++ [top * 16 + bot])
    else .ok out

/-- `_PyBytes_FromHex(string, use_bytearray)` on the input `mem`, whose first `len`
items are the argument. The allocation in the writer is `hexlen / 2`. -/
def fromHexRaw (mem : Seq) (len : Nat) : Py Seq :=
  fromHexLoop mem len (len + 1) 0 []

/-- `_PyBytes_FromHex`, bytesobject.c:2519-2628, on an object. A `str` and a
`bytes`/`bytearray` are NUL-terminated; a memoryview is followed by `after`. -/
def bytesFromHex (o : Obj) : Py Seq :=
  match o with
  | .str cs =>
    match cs.findIdx? (· ≥ 128) with
    | some i => .error (invalidAt i)
    | none => fromHexRaw (cs ++ [0]) cs.length
  | .bytes s | .bytearray s => fromHexRaw (s ++ [0]) s.length
  | .memview s after => fromHexRaw (s ++ after) s.length
  | _ => .error (.typeError s!"fromhex() argument must be str or bytes-like, not {o.typeName}")

/-! ## `hex` -/

/-- `len(x)` as `PyObject_Length` reads it. -/
def objLength (o : Obj) : Py Nat :=
  match o with
  | .str s | .bytes s | .bytearray s | .memview s _ => .ok s.length
  | .list xs | .tuple xs => .ok xs.length
  | .dict kv => .ok kv.length
  | _ => .error (.typeError s!"object of type '{o.typeName}' has no len()")

def hexPair (c : Nat) : Seq := [hexDigit (c / 16), hexDigit (c % 16)]

/-- The `bytes_per_sep_group < 0` loop, pystrhex.c:99-115: `abs` bytes then the
separator, `chunks` times, from the left. -/
def chunkLeft (sep abs : Nat) : Nat → Seq → Seq
  | 0, bs => bs.flatMap hexPair
  | k + 1, bs => (bs.take abs).flatMap hexPair ++ [sep] ++ chunkLeft sep abs k (bs.drop abs)

/-- The `bytes_per_sep_group > 0` loop, pystrhex.c:116-133: the same from the right. -/
def chunkRight (sep abs : Nat) : Nat → Seq → Seq
  | 0, bs => bs.flatMap hexPair
  | k + 1, bs =>
    let n := bs.length - abs
    chunkRight sep abs k (bs.take n) ++ [sep] ++ (bs.drop n).flatMap hexPair

/-- `_Py_strhex_impl(argbuf, arglen, sep, bytes_per_sep_group, return_bytes)`,
pystrhex.c:7-143. The second argument of `hex` is a C `int`. -/
def strhexImpl (arg : Seq) (sep : Option Obj) (bytesPerSep : Int) (returnBytes : Bool) : Py Seq := do
  let parsed : Option Nat ←
    match sep with
    | none => pure none
    | some o => do
      let seplen ← objLength o
      if seplen ≠ 1 then throw (.valueError "sep must be length 1.")
      let c : Nat ← match o with
        | .str cs =>
          if cs.headD 0 ≥ 256 then throw (.valueError "sep must be ASCII.")
          pure (cs.headD 0)
        | .bytes s => pure (s.headD 0)
        | _ => throw (.typeError "sep must be str or bytes.")
      if c > 127 ∧ !returnBytes then throw (.valueError "sep must be ASCII.")
      pure (some c)
  let group : Int := if parsed.isSome then bytesPerSep else 0
  let sepChar := parsed.getD 0
  let abs : Nat := group.natAbs
  let arglen : Int := arg.length
  let resultlen : Int := if group ≠ 0 ∧ arglen > 0 then Int.tdiv (arglen - 1) abs else 0
  if arglen ≥ Int.tdiv ssizeMax 2 - resultlen then throw memoryError
  let group := if (abs : Int) ≥ arglen then 0 else group
  let abs := if (group = 0) then 0 else abs
  if group = 0 then return arg.flatMap hexPair
  let chunks := (arg.length - 1) / abs
  if group < 0 then return chunkLeft sepChar abs chunks arg
  return chunkRight sepChar abs chunks arg

/-- `bytes.hex(sep, bytes_per_sep)` (`bytes_hex_impl`, bytesobject.c:2654-2661) and
`bytearray.hex` (`bytearray_hex_impl`, bytearrayobject.c:2621-2634): the argument
clinic `int`, then `_Py_strhex_with_sep`. -/
def bytesHex (s : Seq) (sep : Option Obj) (bytesPerSep : Int) : Py Seq :=
  if bytesPerSep < -2147483648 ∨ bytesPerSep > 2147483647 then
    .error (.overflowError "Python int too large to convert to C int")
  else strhexImpl s sep bytesPerSep false

/-! ## Properties -/

set_option maxRecDepth 100000 in
theorem hexPair_digits : ∀ c, c < 256 →
    digitValue (hexDigit (c / 16)) * 16 + digitValue (hexDigit (c % 16)) = c ∧
    digitValue (hexDigit (c / 16)) < 16 ∧ digitValue (hexDigit (c % 16)) < 16 ∧
    isSpaceC (hexDigit (c / 16)) = false :=
  by decide

theorem fromHex_flat (s : Seq) (hs : ∀ c ∈ s, c < 256) (mem : Seq) (len : Nat) (i : Nat)
    (out : Seq) (fuel : Nat) (hm : mem.drop i = (s.flatMap hexPair) ++ [0])
    (hlen : len = i + 2 * s.length) (hf : s.length < fuel) :
    fromHexLoop mem len fuel i out = .ok (out ++ s) := by
  induction s generalizing i out fuel with
  | nil =>
    cases fuel with
    | zero => simp at hf
    | succ f => simp [fromHexLoop, hlen]
  | cons c rest ih =>
    obtain ⟨d1, d2, hsp⟩ : ∃ a b, hexPair c = [a, b] ∧ True := ⟨_, _, rfl, trivial⟩
    have hc := hs c (by simp)
    obtain ⟨h1, h2, h3, h4⟩ := hexPair_digits c hc
    cases fuel with
    | zero => simp at hf
    | succ f =>
      simp only [List.flatMap_cons, hexPair, List.cons_append, List.nil_append] at hm
      have m0 : mem[i]? = some (hexDigit (c / 16)) := by
        have := congrArg (fun l => l[0]?) hm
        simpa using this
      have m1 : mem[i + 1]? = some (hexDigit (c % 16)) := by
        have h : (mem.drop i)[1]? = some (hexDigit (c % 16)) := by rw [hm]; rfl
        simpa [List.getElem?_drop] using h
      have mrest : mem.drop (i + 2) = rest.flatMap hexPair ++ [0] := by
        have := congrArg (fun l => l.drop 2) hm
        simpa [List.drop_drop, Nat.add_comm] using this
      have hlt : i < len := by simp at hlen; omega
      simp only [fromHexLoop, hlt, if_true, memRead, m0, h4, Bool.false_eq_true, if_false, m1]
      have htop : ¬ (digitValue (hexDigit (c / 16)) ≥ 16) := by omega
      have hbot : ¬ (digitValue (hexDigit (c % 16)) ≥ 16) := by omega
      have hge : ¬ (i ≥ len ∧ False) := by simp
      simp only [htop, hbot, if_false, h1, false_and]
      rw [ih (fun x hx => hs x (by simp [hx])) (i + 2) _ f mrest (by simp at hlen; omega) (by simp at hf; omega)]
      simp

/-- `_PyBytes_FromHex` does not depend on what follows the buffer: whatever is
stored after a view, `fromhex` of the view is `fromhex` of the same bytes in a
`bytes` object. This is the property a `memoryview` slice breaks. -/
def FromHexIgnoresTail : Prop :=
  ∀ s after : Seq, bytesFromHex (.memview s after) = bytesFromHex (.bytes s) ∨
    ∃ x, bytesFromHex (.memview s after) = .error x ∧ x = Sequences.cUB "read past the buffer"

theorem fromHexIgnoresTail_refuted : ¬ FromHexIgnoresTail := by
  intro h
  have := h [49] [50]
  simp [bytesFromHex, fromHexRaw, fromHexLoop, memRead, isSpaceC, byteSpace, digitValue, oddDigits] at this

/-- For a NUL-terminated argument the parser never needs what follows: the input
is a `str`, `bytes` or `bytearray` and there is no memory to depend on. A byte read
at `end` is the NUL, which is neither a space nor a hex digit, so an odd digit count
is reported; this is the case the code was written for. -/
def FromHexTerminated : Prop :=
  ∀ c : Nat, c < 256 → digitValue c < 16 →
    bytesFromHex (.bytes [c]) = .error oddDigits ∧ bytesFromHex (.bytearray [c]) = .error oddDigits

set_option maxRecDepth 100000 in
theorem hexdigit_not_space : ∀ c, c < 256 → digitValue c < 16 → isSpaceC c = false := by
  decide

theorem fromHexTerminated_proven : FromHexTerminated := by
  intro c hc hd
  have hs := hexdigit_not_space c hc hd
  have h0 : ¬ (digitValue c ≥ 16) := by omega
  have hz : digitValue 0 = 37 := rfl
  have hodd : ¬ (37 < 16) := by decide
  simp [bytesFromHex, fromHexRaw, fromHexLoop, memRead, hs, h0, hz]

end PyLean.BytesObj.Bytes
