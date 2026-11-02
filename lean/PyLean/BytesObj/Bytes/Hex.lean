import PyLean.BytesObj.Bytes.Escape

/-!
`bytes.fromhex`/`bytearray.fromhex` (`_PyBytes_FromHex`, Objects/bytesobject.c:2628-2741)
and `hex` (`_Py_strhex_impl`, Python/pystrhex.c:115-253).

`_PyBytes_FromHex` walks a raw pointer and tests it against `end` before every read, so it does not
depend on what follows the argument (gh-issue: the loop before 3.15 read `*str` at `end`). The model
keeps the memory after the view, `mem = data ++ after`, to state that.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-- A read at `i`; past the allocation it is undefined. -/
def memRead (mem : Seq) (i : Nat) : Py Nat :=
  match mem[i]? with
  | some c => .ok c
  | none => .error (Sequences.cUB "read past the buffer")

/-- `do { str++; if (str >= end) goto done; } while (Py_ISSPACE(*str));`, bytesobject.c:2689-2694:
`none` is `goto done`. -/
def skipSpaces (mem : Seq) (len : Nat) : Nat → Nat → Py (Option Nat)
  | 0, _ => .error .modelFuel
  | fuel + 1, i =>
    if i + 1 ≥ len then .ok none
    else
      match memRead mem (i + 1) with
      | .error e => .error e
      | .ok c => if isSpaceC c then skipSpaces mem len fuel (i + 1) else .ok (some (i + 1))

def invalidAt (i : Nat) : PyExc :=
  .valueError s!"non-hexadecimal number found in fromhex() arg at position {i}"

def oddDigits : PyExc :=
  .valueError "fromhex() arg must contain an even number of hexadecimal digits"

/-- The loop of `_PyBytes_FromHex`, bytesobject.c:2686-2717, from a non-space at `i`. -/
def fromHexDigits (mem : Seq) (len i : Nat) : Py (Option Nat) :=
  match memRead mem i with
  | .error e => .error e
  | .ok t =>
    if digitValue t ≥ 16 then .error (invalidAt i)
    else if i + 1 ≥ len then .error oddDigits
    else
      match memRead mem (i + 1) with
      | .error e => .error e
      | .ok b =>
        if digitValue b ≥ 16 then .error (invalidAt (i + 1))
        else .ok (some (digitValue t * 16 + digitValue b))

/-- The loop of `_PyBytes_FromHex`, bytesobject.c:2686-2717. `len` is `hexlen`,
`i` is `str - start`. -/
def fromHexLoop (mem : Seq) (len : Nat) : Nat → Nat → Seq → Py Seq
  | 0, _, _ => .error .modelFuel
  | fuel + 1, i, out =>
    if i < len then
      match memRead mem i with
      | .error e => .error e
      | .ok c =>
        let afterSpace : Py (Option Nat) :=
          if isSpaceC c then skipSpaces mem len (len + 1) i else .ok (some i)
        match afterSpace with
        | .error e => .error e
        | .ok none => .ok out
        | .ok (some i) =>
          match fromHexDigits mem len i with
          | .error e => .error e
          | .ok none => .ok out
          | .ok (some v) => fromHexLoop mem len fuel (i + 2) (out ++ [v])
    else .ok out

/-- `_PyBytes_FromHex(string, use_bytearray)` on the input `mem`, whose first `len`
items are the argument. The allocation in the writer is `hexlen / 2`. -/
def fromHexRaw (mem : Seq) (len : Nat) : Py Seq :=
  fromHexLoop mem len (len + 1) 0 []

/-- `_PyBytes_FromHex`, bytesobject.c:2628-2741, on an object. A memoryview is followed by `after`. -/
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

/-- The `bytes_per_sep_group < 0` loop, pystrhex.c:210-226: `abs` bytes then the
separator, `chunks` times, from the left. -/
def chunkLeft (sep abs : Nat) : Nat → Seq → Seq
  | 0, bs => bs.flatMap hexPair
  | k + 1, bs => (bs.take abs).flatMap hexPair ++ [sep] ++ chunkLeft sep abs k (bs.drop abs)

/-- The `bytes_per_sep_group > 0` loop, pystrhex.c:227-244: the same from the right. -/
def chunkRight (sep abs : Nat) : Nat → Seq → Seq
  | 0, bs => bs.flatMap hexPair
  | k + 1, bs =>
    let n := bs.length - abs
    chunkRight sep abs k (bs.take n) ++ [sep] ++ (bs.drop n).flatMap hexPair

/-- `_Py_strhex_impl(argbuf, arglen, sep, bytes_per_sep_group, return_bytes)`,
pystrhex.c:115-253. The second argument of `hex` is a `Py_ssize_t`. -/
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

/-- `bytes.hex(sep, bytes_per_sep)` (`bytes_hex_impl`, bytesobject.c:2766-2773) and
`bytearray.hex` (`bytearray_hex_impl`, bytearrayobject.c:2733-2747): the argument
clinic `Py_ssize_t`, then `_Py_strhex_with_sep`. -/
def bytesHex (s : Seq) (sep : Option Obj) (bytesPerSep : Int) : Py Seq :=
  if bytesPerSep < ssizeMin ∨ bytesPerSep > ssizeMax then
    .error (.overflowError "Python int too large to convert to C ssize_t")
  else strhexImpl s sep bytesPerSep false

/-! ## Properties -/

set_option maxRecDepth 100000 in
theorem hexPair_digits : ∀ c, c < 256 →
    digitValue (hexDigit (c / 16)) * 16 + digitValue (hexDigit (c % 16)) = c ∧
    digitValue (hexDigit (c / 16)) < 16 ∧ digitValue (hexDigit (c % 16)) < 16 ∧
    isSpaceC (hexDigit (c / 16)) = false :=
  by decide

/-- The parser reads only the first `len` items of the memory. -/
theorem skipSpaces_congr (m1 m2 : Seq) (len : Nat) (h : ∀ i, i < len → m1[i]? = m2[i]?) :
    ∀ (f : Nat) (i : Nat), skipSpaces m1 len f i = skipSpaces m2 len f i := by
  intro f
  induction f with
  | zero => intro i; rfl
  | succ f ih =>
    intro i
    simp only [skipSpaces]
    split
    · rfl
    · rename_i hl
      have e := h (i + 1) (by omega)
      simp only [memRead, e]
      split
      · rfl
      · simp only [ih]

theorem fromHexDigits_congr (m1 m2 : Seq) (len i : Nat) (h : ∀ i, i < len → m1[i]? = m2[i]?)
    (hi : i < len) : fromHexDigits m1 len i = fromHexDigits m2 len i := by
  simp only [fromHexDigits, memRead, h i hi]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · simp only [h (i + 1) (by omega)]

theorem skipSpaces_lt (m : Seq) (len : Nat) : ∀ (f i j : Nat),
    skipSpaces m len f i = .ok (some j) → j < len := by
  intro f
  induction f with
  | zero => intro i j h; simp [skipSpaces] at h
  | succ f ih =>
    intro i j h
    simp only [skipSpaces] at h
    split at h
    · simp at h
    · rename_i hl
      split at h
      · simp at h
      · split at h
        · exact ih _ _ h
        · simp only [Except.ok.injEq, Option.some.injEq] at h
          omega

theorem fromHexLoop_congr (m1 m2 : Seq) (len : Nat) (h : ∀ i, i < len → m1[i]? = m2[i]?) :
    ∀ (f : Nat) (i : Nat) (out : Seq), fromHexLoop m1 len f i out = fromHexLoop m2 len f i out := by
  intro f
  induction f with
  | zero => intro i out; rfl
  | succ f ih =>
    intro i out
    simp only [fromHexLoop]
    split
    · rename_i hi
      simp only [memRead, h i hi]
      split
      · rfl
      · rename_i c hc
        by_cases hs : isSpaceC c = true
        · simp only [hs, if_true, ← skipSpaces_congr m1 m2 len h]
          cases hk : skipSpaces m1 len (len + 1) i with
          | error e => rfl
          | ok r =>
            cases r with
            | none => rfl
            | some j =>
              simp only [fromHexDigits_congr m1 m2 len j h (skipSpaces_lt _ _ _ _ _ hk)]
              split
              · rfl
              · rfl
              · simp only [ih]
        · simp only [hs, Bool.false_eq_true, if_false, fromHexDigits_congr m1 m2 len i h hi]
          split
          · rfl
          · rfl
          · simp only [ih]
    · rfl

/-- `_PyBytes_FromHex` does not depend on what follows the buffer: whatever is stored after a view,
`fromhex` of the view is `fromhex` of the same bytes in a `bytes` object, because the parser tests
`end` before every read. -/
def FromHexIgnoresTail : Prop :=
  ∀ s after : Seq, bytesFromHex (.memview s after) = bytesFromHex (.bytes s)

theorem fromHexIgnoresTail_proven : FromHexIgnoresTail := by
  intro s after
  simp only [bytesFromHex, fromHexRaw]
  apply fromHexLoop_congr
  intro i hi
  rw [List.getElem?_append_left hi, List.getElem?_append_left hi]

/-- `fromhex` of what `hex` writes. -/
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
      have hd : fromHexDigits mem len i = .ok (some c) := by
        have htop : ¬ (digitValue (hexDigit (c / 16)) ≥ 16) := by omega
        have hbot : ¬ (digitValue (hexDigit (c % 16)) ≥ 16) := by omega
        have hl : ¬ (i + 1 ≥ len) := by simp at hlen; omega
        simp only [fromHexDigits, memRead, m0, m1, htop, hbot, hl, if_false, h1]
      simp only [fromHexLoop, hlt, if_true, memRead, m0, h4, Bool.false_eq_true, if_false, hd]
      rw [ih (fun x hx => hs x (by simp [hx])) (i + 2) _ f mrest (by simp at hlen; omega) (by simp at hf; omega)]
      simp

/-- A single hex digit is reported as an odd digit count, for a `bytes`, a `bytearray` and a view
whatever follows it: the second digit is at `end` and is not read. -/
def FromHexTerminated : Prop :=
  ∀ c : Nat, c < 256 → digitValue c < 16 → ∀ after : Seq,
    bytesFromHex (.bytes [c]) = .error oddDigits ∧ bytesFromHex (.bytearray [c]) = .error oddDigits ∧
    bytesFromHex (.memview [c] after) = .error oddDigits

set_option maxRecDepth 100000 in
theorem hexdigit_not_space : ∀ c, c < 256 → digitValue c < 16 → isSpaceC c = false := by
  decide

theorem fromHexTerminated_proven : FromHexTerminated := by
  intro c hc hd after
  have hs := hexdigit_not_space c hc hd
  have h0 : ¬ (digitValue c ≥ 16) := by omega
  simp [bytesFromHex, fromHexRaw, fromHexLoop, fromHexDigits, memRead, hs, h0]

end PyLean.BytesObj.Bytes
