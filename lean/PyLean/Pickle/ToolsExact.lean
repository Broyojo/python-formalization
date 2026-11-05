import PyLean.Pickle.ToolsGen

/-!
Every outcome of the counted argument readers of `Lib/pickletools.py` and of
`read_stringnl`: the value on a complete payload, and each `ValueError` with its
exact message (truncated count field, truncated payload, a count above
`sys.maxsize`, a negative signed count, a missing newline, missing quotes).
-/

namespace PyLean.Pickle

open PyLean

/-- A reader's result at position `s`. -/
def atPos {α : Type} (r : Py α) (s : Nat) : Except PyExc (α × Nat) :=
  match r with
  | .ok a => .ok (a, s)
  | .error e => .error e

/-! ## Reading lemmas -/

theorem tRead_short (pre short : Bytes) (n : Nat) (h : short.length ≤ n) :
    tRead n pre.length (pre ++ short) = .ok (short, pre.length + short.length) := by
  have hd : (pre ++ short).drop pre.length = short := List.drop_left
  simp only [tRead, hd, List.take_of_length_le h]

theorem needBytes_err (n : Nat) (name : String) (data : Bytes) (pos : Nat) (d : Bytes)
    (h : data.length ≠ n) :
    needBytes n name data pos d =
      .error (.valueError s!"expected {n} bytes in a {name}, but only {data.length} remain") := by
  unfold needBytes
  rw [if_neg h]
  rfl

theorem readUint_short (k : Nat) (name : String) (pre short : Bytes) (h : short.length < k) :
    readUintN k name pre.length (pre ++ short) =
      .error (.valueError s!"not enough data in stream to read {name}") := by
  unfold readUintN
  rw [tBind, tRead_short pre short k (by omega)]
  dsimp only
  rw [if_neg (by omega)]
  rfl

theorem bind_err {α β : Type} (m : TM α) (f : α → TM β) (pos : Nat) (d : Bytes) (e : PyExc)
    (h : m pos d = .error e) : (m >>= f) pos d = .error e := by
  rw [tBind, h]

theorem readInt4_short (pre short : Bytes) (h : short.length < 4) :
    readInt4 pre.length (pre ++ short) =
      .error (.valueError "not enough data in stream to read int4") := by
  unfold readInt4
  rw [tBind, tRead_short pre short 4 (by omega)]
  dsimp only
  rw [if_neg (by omega)]
  rfl

/-- `read_int4` on the bytes `struct.pack("<i", x)` wrote, for any `x`. -/
theorem readInt4_pack (x : Int) (b pre rest : Bytes) (h : packI32 x = .ok b) :
    readInt4 pre.length (pre ++ b ++ rest) = .ok (x, pre.length + 4) :=
  readInt4Roundtrip_proven x b pre rest h

theorem packI32_length (x : Int) (b : Bytes) (h : packI32 x = .ok b) : b.length = 4 := by
  unfold packI32 at h
  split at h
  · injection h with h; subst h; exact leBytes_length _ _
  · cases h

theorem readInt4_then_pack {β : Type} (x : Int) (b pre rest : Bytes) (h : packI32 x = .ok b)
    (f : Int → TM β) :
    (readInt4 >>= f) pre.length (pre ++ b ++ rest) = f x (pre.length + 4) (pre ++ b ++ rest) := by
  rw [tBind, readInt4_pack x b pre rest h]

/-- `struct.pack("<i", n)` of a count `n < 2**31` is its four little-endian bytes. -/
theorem packI32_nat (n : Nat) (h : n < 2 ^ 31) : packI32 (n : Int) = .ok (leBytes n 4) := by
  unfold packI32 toBytesSigned
  rw [if_pos (by omega)]
  have : ((n : Int) % (2 : Int) ^ (8 * 4)).toNat = n := by
    rw [Int.emod_eq_of_lt (by omega) (by omega)]; simp
  rw [this]

/-! ## `read_int4` -/

/-- `read_int4` (`Lib/pickletools.py:254-266`) returns the int `struct.pack("<i")`
wrote, negative ones included, at any position of any stream, and raises
`ValueError` with the exact message of `:266` on fewer than four bytes. A reader
that takes the bytes as unsigned, pads short data or skips the length check fails
one of the two. -/
def ReadInt4Exact : Prop :=
  (∀ (x : Int) (b pre rest : Bytes), packI32 x = .ok b →
    readInt4 pre.length (pre ++ b ++ rest) = .ok (x, pre.length + 4)) ∧
  (∀ pre short : Bytes, short.length < 4 →
    readInt4 pre.length (pre ++ short) =
      .error (.valueError "not enough data in stream to read int4"))

theorem readInt4Exact_proven : ReadInt4Exact :=
  ⟨readInt4_pack, readInt4_short⟩

/-! ## Counted readers -/

/-- Every outcome of a counted reader `r` whose count is `k` little-endian
unsigned bytes read by `read_uint{k}` (`cname`):

* `full`: a complete payload `b` gives `val b` and moves past it;
* `short`: a payload shorter than its count `n` raises `ValueError(shortMsg n len)`;
* `count`: fewer than `k` bytes of count raise `read_uint{k}`'s `ValueError`;
* `big`: a count above `limit` (`sys.maxsize` for the 8-byte counts) raises
  `ValueError("{name} byte count > sys.maxsize: {n}")`.

For one-byte counts `big` is vacuous: no count exceeds `sys.maxsize`. -/
structure CountedSpec {α : Type} (r : TM α) (k : Nat) (cname name : String) (val : Bytes → Py α)
    (shortMsg : Nat → Nat → String) : Prop where
  full : ∀ pre b rest : Bytes, b.length ≤ ssizeMaxN → b.length < 256 ^ k →
    r pre.length (pre ++ leBytes b.length k ++ (b ++ rest)) =
      atPos (val b) (pre.length + k + b.length)
  short : ∀ (pre short : Bytes) (n : Nat), n ≤ ssizeMaxN → n < 256 ^ k → short.length < n →
    r pre.length (pre ++ leBytes n k ++ short) = .error (.valueError (shortMsg n short.length))
  count : ∀ pre short : Bytes, short.length < k →
    r pre.length (pre ++ short) = .error (.valueError s!"not enough data in stream to read {cname}")
  big : ∀ (pre rest : Bytes) (n : Nat), ssizeMaxN < n → n < 256 ^ k →
    r pre.length (pre ++ leBytes n k ++ rest) =
      .error (.valueError s!"{name} byte count > sys.maxsize: {n}")

/-- The same for a count read by `read_int4`, which is signed: `neg` is the
`"{name} byte count < 0"` `ValueError` on every negative count. -/
structure Counted4Spec {α : Type} (r : TM α) (name : String) (val : Bytes → Py α)
    (shortMsg : Nat → Nat → String) : Prop where
  full : ∀ pre b rest : Bytes, b.length < 2 ^ 31 →
    r pre.length (pre ++ leBytes b.length 4 ++ (b ++ rest)) =
      atPos (val b) (pre.length + 4 + b.length)
  short : ∀ (pre short : Bytes) (n : Nat), n < 2 ^ 31 → short.length < n →
    r pre.length (pre ++ leBytes n 4 ++ short) = .error (.valueError (shortMsg n short.length))
  count : ∀ pre short : Bytes, short.length < 4 →
    r pre.length (pre ++ short) = .error (.valueError "not enough data in stream to read int4")
  neg : ∀ (pre b rest : Bytes) (n : Int), packI32 n = .ok b → n < 0 →
    r pre.length (pre ++ b ++ rest) = .error (.valueError s!"{name} byte count < 0: {n}")

/-- `"expected %d bytes in a %s, but only %d remain"`. -/
def expectedMsg (name : String) (n m : Nat) : String :=
  s!"expected {n} bytes in a {name}, but only {m} remain"

theorem assoc3 (pre c b rest : Bytes) : pre ++ c ++ (b ++ rest) = (pre ++ c) ++ b ++ rest := by
  simp [List.append_assoc]

theorem len_cnt (pre : Bytes) (n k : Nat) : (pre ++ leBytes n k).length = pre.length + k := by
  simp [leBytes_length]

/-- The body after the count, for the readers without a `sys.maxsize` check:
`data = f.read(n)` and the length test. -/
theorem readBody_short (n : Nat) (name : String) (q short : Bytes) (h : short.length < n) :
    (tRead n >>= fun data => needBytes n name data) q.length (q ++ short) =
      .error (.valueError (expectedMsg name n short.length)) := by
  rw [tBind, tRead_short q short n (by omega)]
  exact needBytes_err n name short _ _ (by omega)

theorem readCounted_short (n : Nat) (name : String) (q short : Bytes) (h1 : n ≤ ssizeMaxN)
    (h2 : short.length < n) :
    readCounted n name q.length (q ++ short) =
      .error (.valueError (expectedMsg name n short.length)) := by
  unfold readCounted
  rw [if_neg (by omega)]
  exact readBody_short n name q short h2

theorem readCounted_big (n : Nat) (name : String) (pos : Nat) (d : Bytes) (h : ssizeMaxN < n) :
    readCounted n name pos d = .error (.valueError s!"{name} byte count > sys.maxsize: {n}") := by
  unfold readCounted
  rw [if_pos h]
  rfl

theorem readUint_then' {β : Type} (k : Nat) (name : String) (n : Nat) (pre rest : Bytes)
    (h : n < 256 ^ k) (f : Nat → TM β) :
    (readUintN k name >>= f) pre.length (pre ++ leBytes n k ++ rest) =
      f n (pre ++ leBytes n k).length (pre ++ leBytes n k ++ rest) := by
  rw [readUint_then k name n pre rest h, len_cnt]

/-- A counted reader built as `readCounted` after `read_uint{k}`. -/
theorem countedSpec_of {α : Type} (k : Nat) (cname name : String) (post : Bytes → Py α)
    (hk : 0 < k) :
    CountedSpec (readUintN k cname >>= fun n => readCounted n name >>= fun d => tLift (post d))
      k cname name post (expectedMsg name) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro pre b rest hb hk'
    rw [readUint_then' k _ _ _ _ hk', assoc3, tBind, len_cnt, readCounted_at name pre b rest k hb]
    dsimp only
    simp only [tLift, atPos]
    cases post b <;> rfl
  · intro pre short n hn hk' hs
    rw [readUint_then' k _ _ _ _ hk', tBind, readCounted_short n name _ short hn hs]
  · intro pre short hs
    exact bind_err _ _ _ _ _ (readUint_short k cname pre short hs)
  · intro pre rest n hn hk'
    rw [readUint_then' k _ _ _ _ hk', tBind, readCounted_big n name _ _ hn]

/-- A one-byte counted reader: `n = read_uint1(f)`, `data = f.read(n)`, the
length test, then `post`. -/
theorem countedSpec_one {α : Type} (name : String) (post : Bytes → Py α) :
    CountedSpec (readUintN 1 "uint1" >>= fun n => tRead n >>= fun data =>
        needBytes n name data >>= fun d => tLift (post d))
      1 "uint1" name post (expectedMsg name) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro pre b rest _ hk'
    rw [readUint_then' 1 _ _ _ _ hk', assoc3, tBind, len_cnt]
    have hr := tRead_at (pre ++ leBytes b.length 1) b rest
    rw [len_cnt] at hr
    rw [hr]
    dsimp only
    rw [tBind, needBytes_ok]
    dsimp only
    simp only [tLift, atPos]
    cases post b <;> rfl
  · intro pre short n _ hk' hs
    rw [readUint_then' 1 _ _ _ _ hk', tBind, tRead_short _ short n (by omega)]
    dsimp only
    rw [tBind, needBytes_err n name short _ _ (by omega)]
    rfl
  · intro pre short hs
    exact bind_err _ _ _ _ _ (readUint_short 1 "uint1" pre short hs)
  · intro pre rest n hn hk'
    unfold ssizeMaxN at hn
    omega

theorem tLift_pure {α : Type} (a : α) : (tLift (.ok a) : TM α) = pure a := rfl

theorem bind_tLift_ok {α : Type} (m : TM α) : (m >>= fun d => tLift (.ok d)) = m := by
  funext pos d
  rw [tBind]
  cases m pos d with
  | ok r => rfl
  | error e => rfl

theorem bind_tLift_ok' {α β : Type} (m : TM α) (g : α → β) :
    (m >>= fun d => tLift (.ok (g d))) = (m >>= fun d => pure (g d)) := rfl

/-- `read_bytes1` (`:474-489`), `read_string1` (`:411-426`), `read_bytes4`
(`:502-523`), `read_bytes8` (`:536-558`) and `read_bytearray8` (`:571-593`): every
outcome, with the exact messages of the source. -/
def ReadBytesExact : Prop :=
  CountedSpec readBytes1 1 "uint1" "bytes1" .ok (expectedMsg "bytes1") ∧
  CountedSpec readString1 1 "uint1" "string1" (fun b => .ok (latin1 b)) (expectedMsg "string1") ∧
  CountedSpec readBytes4 4 "uint4" "bytes4" .ok (expectedMsg "bytes4") ∧
  CountedSpec readBytes8 8 "uint8" "bytes8" .ok (expectedMsg "bytes8") ∧
  CountedSpec readBytearray8 8 "uint8" "bytearray8" .ok (expectedMsg "bytearray8")

theorem readBytes1_eq : readBytes1 = (readUintN 1 "uint1" >>= fun n => tRead n >>= fun data =>
    needBytes n "bytes1" data >>= fun d => tLift (.ok d)) := by
  unfold readBytes1 readUint1
  congr; funext n; congr; funext data
  exact (bind_tLift_ok _).symm

theorem readString1_eq : readString1 = (readUintN 1 "uint1" >>= fun n => tRead n >>= fun data =>
    needBytes n "string1" data >>= fun d => tLift (.ok (latin1 d))) := rfl

theorem readCountedK_eq (k : Nat) (cname name : String) :
    (readUintN k cname >>= fun n => readCounted n name) =
      (readUintN k cname >>= fun n => readCounted n name >>= fun d => tLift (.ok d)) := by
  congr; funext n
  exact (bind_tLift_ok _).symm

theorem readBytesExact_proven : ReadBytesExact := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [readBytes1_eq]; exact countedSpec_one "bytes1" .ok
  · rw [readString1_eq]; exact countedSpec_one "string1" (fun b => .ok (latin1 b))
  · show CountedSpec (readUintN 4 "uint4" >>= fun n => readCounted n "bytes4") _ _ _ _ _
    rw [readCountedK_eq]; exact countedSpec_of 4 "uint4" "bytes4" .ok (by decide)
  · show CountedSpec (readUintN 8 "uint8" >>= fun n => readCounted n "bytes8") _ _ _ _ _
    rw [readCountedK_eq]; exact countedSpec_of 8 "uint8" "bytes8" .ok (by decide)
  · show CountedSpec (readUintN 8 "uint8" >>= fun n => readCounted n "bytearray8") _ _ _ _ _
    rw [readCountedK_eq]; exact countedSpec_of 8 "uint8" "bytearray8" .ok (by decide)

/-- `read_unicodestring1` (`:631-655`), `read_unicodestring4` (`:670-696`) and
`read_unicodestring8` (`:711-737`): the `utf-8`/`surrogatepass` decoding of a
complete payload (or its `UnicodeDecodeError`), and each `ValueError`. -/
def ReadUnicodeExact : Prop :=
  CountedSpec readUnicodestring1 1 "uint1" "unicodestring1" decodeUtf8SP
    (expectedMsg "unicodestring1") ∧
  CountedSpec readUnicodestring4 4 "uint4" "unicodestring4" decodeUtf8SP
    (expectedMsg "unicodestring4") ∧
  CountedSpec readUnicodestring8 8 "uint8" "unicodestring8" decodeUtf8SP
    (expectedMsg "unicodestring8")

theorem readUnicodeExact_proven : ReadUnicodeExact := by
  refine ⟨?_, ?_, ?_⟩
  · exact countedSpec_one "unicodestring1" decodeUtf8SP
  · exact countedSpec_of 4 "uint4" "unicodestring4" decodeUtf8SP (by decide)
  · exact countedSpec_of 8 "uint8" "unicodestring8" decodeUtf8SP (by decide)

/-! ## Signed counts: `read_string4` and `read_long4` -/

theorem readInt4_then_nat {β : Type} (n : Nat) (pre rest : Bytes) (h : n < 2 ^ 31) (f : Int → TM β) :
    (readInt4 >>= f) pre.length (pre ++ leBytes n 4 ++ rest) =
      f (n : Int) (pre ++ leBytes n 4).length (pre ++ leBytes n 4 ++ rest) := by
  rw [readInt4_then n pre rest h, len_cnt]

/-- `read_string4` (`Lib/pickletools.py:440-460`): every outcome, the negative
count included. -/
def ReadString4Exact : Prop :=
  Counted4Spec readString4 "string4" (fun b => .ok (latin1 b)) (expectedMsg "string4")

theorem readString4Exact_proven : ReadString4Exact := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro pre b rest h
    exact readString4Roundtrip_proven pre b rest h
  · intro pre short n hn hs
    unfold readString4
    rw [readInt4_then_nat n pre short hn, if_neg (by omega)]
    have hn' : ((n : Int)).toNat = n := by omega
    rw [hn', tBind, tRead_short _ short n (by omega)]
    dsimp only
    rw [tBind, needBytes_err n _ short _ _ (by omega)]
    rfl
  · intro pre short hs
    exact bind_err _ _ _ _ _ (readInt4_short pre short hs)
  · intro pre b rest n hb hn
    unfold readString4
    rw [readInt4_then_pack n b pre rest hb, if_pos hn]
    rfl

/-- `read_long1` (`:875-894`) and `read_long4` (`:907-928`): `decode_long` of a
complete payload (so `encode_long` reads back), and each `ValueError`; for
`read_long4` also the negative count that the `long4` descriptor rules out
("requires the size to be >= 0", `:936-937`). -/
def ReadLongExact : Prop :=
  CountedSpec readLong1 1 "uint1" "long1" (fun b => .ok (decodeLong b))
    (fun _ _ => "not enough data in stream to read long1") ∧
  Counted4Spec readLong4 "long4" (fun b => .ok (decodeLong b))
    (fun _ _ => "not enough data in stream to read long4") ∧
  ReadLongRoundtrip

theorem readLongExact_proven : ReadLongExact := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, readLongRoundtrip_proven⟩
  · intro pre b rest _ hk
    unfold readLong1 readUint1
    rw [readUint_then' 1 _ _ _ _ hk, assoc3, tBind, len_cnt]
    have hr := tRead_at (pre ++ leBytes b.length 1) b rest
    rw [len_cnt] at hr
    rw [hr]
    dsimp only
    rw [if_neg (by simp)]
    rfl
  · intro pre short n _ hk hs
    unfold readLong1 readUint1
    rw [readUint_then' 1 _ _ _ _ hk, tBind, tRead_short _ short n (by omega)]
    dsimp only
    rw [if_pos (by omega)]
    rfl
  · intro pre short hs
    exact bind_err _ _ _ _ _ (readUint_short 1 "uint1" pre short hs)
  · intro pre rest n hn hk
    unfold ssizeMaxN at hn
    omega
  · intro pre b rest h
    unfold readLong4
    rw [readInt4_then_nat b.length pre (b ++ rest) h, if_neg (by omega), assoc3]
    have hn : ((b.length : Int)).toNat = b.length := by omega
    rw [hn, tBind]
    have hr := tRead_at (pre ++ leBytes b.length 4) b rest
    rw [len_cnt] at hr
    rw [len_cnt, hr]
    dsimp only
    rw [if_neg (by simp)]
    rfl
  · intro pre short n hn hs
    unfold readLong4
    rw [readInt4_then_nat n pre short hn, if_neg (by omega)]
    have hn' : ((n : Int)).toNat = n := by omega
    rw [hn', tBind, tRead_short _ short n (by omega)]
    dsimp only
    rw [if_pos (by omega)]
    rfl
  · intro pre short hs
    exact bind_err _ _ _ _ _ (readInt4_short pre short hs)
  · intro pre b rest n hb hn
    unfold readLong4
    rw [readInt4_then_pack n b pre rest hb, if_pos hn]
    rfl

/-! ## `read_stringnl` -/

/-- One byte of `repr(bytes)` between its quotes, `q` being the quote:
`_Py_bytes_repr`, `Objects/bytesobject.c:1480-1497`. -/
def reprEsc (q c : UInt8) : Bytes :=
  if c == q || c == 0x5c then [0x5c, c]
  else if c == 0x09 then [0x5c, 0x74]
  else if c == 0x0a then [0x5c, 0x6e]
  else if c == 0x0d then [0x5c, 0x72]
  else if c < 0x20 || c ≥ 0x7f then [0x5c, 0x78, hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]
  else [c]

theorem hexVal_hexDigit (n : Nat) (h : n < 16) : hexVal (hexDigit n) = some n := by
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨
      n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by omega
  rcases this with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide

theorem hexDigit_ne_nl (n : Nat) (h : n < 16) : hexDigit n ≠ nl := by
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨
      n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by omega
  rcases this with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide

theorem escapeDecode_bs (pos : Nat) (d : UInt8) (r : Bytes) :
    escapeDecode pos (0x5c :: d :: r) =
      if d == 0x0a then escapeDecode (pos + 2) r
      else if d == 0x5c then (0x5c :: ·) <$> escapeDecode (pos + 2) r
      else if d == 0x27 then (0x27 :: ·) <$> escapeDecode (pos + 2) r
      else if d == 0x22 then (0x22 :: ·) <$> escapeDecode (pos + 2) r
      else if d == 0x62 then (0x08 :: ·) <$> escapeDecode (pos + 2) r
      else if d == 0x66 then (0x0c :: ·) <$> escapeDecode (pos + 2) r
      else if d == 0x74 then (0x09 :: ·) <$> escapeDecode (pos + 2) r
      else if d == 0x6e then (0x0a :: ·) <$> escapeDecode (pos + 2) r
      else if d == 0x72 then (0x0d :: ·) <$> escapeDecode (pos + 2) r
      else if d == 0x76 then (0x0b :: ·) <$> escapeDecode (pos + 2) r
      else if d == 0x61 then (0x07 :: ·) <$> escapeDecode (pos + 2) r
      else if 0x30 ≤ d && d ≤ 0x37 then
        match r with
        | e :: r2 =>
          if 0x30 ≤ e && e ≤ 0x37 then
            match r2 with
            | f :: r3 =>
              if 0x30 ≤ f && f ≤ 0x37 then
                ((((d.toNat - 48) * 64 + (e.toNat - 48) * 8 + (f.toNat - 48)) % 256).toUInt8 :: ·) <$>
                  escapeDecode (pos + 4) r3
              else (((d.toNat - 48) * 8 + (e.toNat - 48)).toUInt8 :: ·) <$> escapeDecode (pos + 3) (f :: r3)
            | [] => pure [((d.toNat - 48) * 8 + (e.toNat - 48)).toUInt8]
          else ((d.toNat - 48).toUInt8 :: ·) <$> escapeDecode (pos + 2) (e :: r2)
        | [] => pure [(d.toNat - 48).toUInt8]
      else if d == 0x78 then
        match r with
        | e :: f :: r2 => match hexVal e, hexVal f with
          | some a, some b => ((a * 16 + b).toUInt8 :: ·) <$> escapeDecode (pos + 4) r2
          | _, _ => .error (.valueError s!"invalid \\x escape at position {pos}")
        | _ => .error (.valueError s!"invalid \\x escape at position {pos}")
      else (0x5c :: ·) <$> escapeDecode (pos + 1) (d :: r) := by
  rw [escapeDecode.eq_def]
  rfl

/-- `escape_decode` undoes each escape `repr(bytes)` writes. -/
theorem escapeDecode_reprEsc (q c : UInt8) (hq : q = 0x22 ∨ q = 0x27) (pos : Nat) (r : Bytes) :
    escapeDecode pos (reprEsc q c ++ r) =
      (c :: ·) <$> escapeDecode (pos + (reprEsc q c).length) r := by
  unfold reprEsc
  by_cases h1 : (c == q || c == 0x5c) = true
  · rw [if_pos h1]
    have hc : c = 0x22 ∨ c = 0x27 ∨ c = 0x5c := by
      simp only [Bool.or_eq_true, beq_iff_eq] at h1
      rcases h1 with h | h
      · rcases hq with e | e <;> subst e <;> simp [h]
      · simp [h]
    show escapeDecode pos (0x5c :: c :: r) = _
    rw [escapeDecode_bs]
    rcases hc with e | e | e <;> subst e <;> rfl
  rw [if_neg h1]
  have hq' : c ≠ 0x5c := by
    intro e; apply h1; simp [e]
  by_cases h2 : (c == 0x09) = true
  · rw [if_pos h2]
    have : c = 0x09 := by simpa using h2
    subst this
    show escapeDecode pos (0x5c :: 0x74 :: r) = _
    rw [escapeDecode_bs]; rfl
  rw [if_neg h2]
  by_cases h3 : (c == 0x0a) = true
  · rw [if_pos h3]
    have : c = 0x0a := by simpa using h3
    subst this
    show escapeDecode pos (0x5c :: 0x6e :: r) = _
    rw [escapeDecode_bs]; rfl
  rw [if_neg h3]
  by_cases h4 : (c == 0x0d) = true
  · rw [if_pos h4]
    have : c = 0x0d := by simpa using h4
    subst this
    show escapeDecode pos (0x5c :: 0x72 :: r) = _
    rw [escapeDecode_bs]; rfl
  rw [if_neg h4]
  by_cases h5 : (c < 0x20 || c ≥ 0x7f) = true
  · rw [if_pos h5]
    have hc16 : c.toNat / 16 < 16 := by have := c.toNat_lt; omega
    have hm16 : c.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
    show escapeDecode pos (0x5c :: 0x78 :: hexDigit (c.toNat / 16) :: hexDigit (c.toNat % 16) :: r) = _
    rw [escapeDecode_bs]
    simp only [show ((0x78 : UInt8) == 0x0a) = false from rfl, show ((0x78 : UInt8) == 0x5c) = false from rfl,
      show ((0x78 : UInt8) == 0x27) = false from rfl, show ((0x78 : UInt8) == 0x22) = false from rfl,
      show ((0x78 : UInt8) == 0x62) = false from rfl, show ((0x78 : UInt8) == 0x66) = false from rfl,
      show ((0x78 : UInt8) == 0x74) = false from rfl, show ((0x78 : UInt8) == 0x6e) = false from rfl,
      show ((0x78 : UInt8) == 0x72) = false from rfl, show ((0x78 : UInt8) == 0x76) = false from rfl,
      show ((0x78 : UInt8) == 0x61) = false from rfl,
      show ((0x30 : UInt8) ≤ 0x78 && (0x78 : UInt8) ≤ 0x37) = false from rfl,
      show ((0x78 : UInt8) == 0x78) = true from rfl, Bool.false_eq_true, if_false, if_true,
      hexVal_hexDigit _ hc16, hexVal_hexDigit _ hm16]
    have hv : ((c.toNat / 16) * 16 + c.toNat % 16).toUInt8 = c := by
      rw [Nat.mul_comm, Nat.div_add_mod]
      exact UInt8.ofNat_toNat
    rw [hv]
    rfl
  rw [if_neg h5]
  show escapeDecode pos (c :: r) = _
  rw [escapeDecode.eq_def]
  simp only [bne_iff_ne, ne_eq, hq', not_false_eq_true, if_true]
  rfl

/-- The text between the quotes of `repr(b)` with quote `q`. -/
def reprBody (q : UInt8) (b : Bytes) : Bytes := b.flatMap (reprEsc q)

theorem escapeDecode_reprBody (q : UInt8) (hq : q = 0x22 ∨ q = 0x27) (b : Bytes) (pos : Nat) :
    escapeDecode pos (reprBody q b) = .ok b := by
  induction b generalizing pos with
  | nil => unfold reprBody; rw [escapeDecode.eq_def]; rfl
  | cons c r ih =>
    unfold reprBody at ih ⊢
    rw [List.flatMap_cons, escapeDecode_reprEsc q c hq, ih]
    rfl

theorem nl_not_mem_reprEsc (q c : UInt8) (hq : q = 0x22 ∨ q = 0x27) : nl ∉ reprEsc q c := by
  have hqn : q ≠ nl := by rcases hq with e | e <;> (subst e; decide)
  unfold reprEsc
  by_cases h1 : (c == q || c == 0x5c) = true
  · rw [if_pos h1]
    have hc : c ≠ nl := by
      simp only [Bool.or_eq_true, beq_iff_eq] at h1
      rcases h1 with h | h
      · rw [h]; exact hqn
      · rw [h]; decide
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
    exact ⟨by decide, fun e => hc e.symm⟩
  rw [if_neg h1]
  by_cases h2 : (c == 0x09) = true
  · rw [if_pos h2]; decide
  rw [if_neg h2]
  by_cases h3 : (c == 0x0a) = true
  · rw [if_pos h3]; decide
  rw [if_neg h3]
  by_cases h4 : (c == 0x0d) = true
  · rw [if_pos h4]; decide
  rw [if_neg h4]
  by_cases h5 : (c < 0x20 || c ≥ 0x7f) = true
  · rw [if_pos h5]
    have hc16 : c.toNat / 16 < 16 := by have := c.toNat_lt; omega
    have hm16 : c.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
    exact ⟨by decide, by decide, fun e => hexDigit_ne_nl _ hc16 e.symm,
      fun e => hexDigit_ne_nl _ hm16 e.symm⟩
  rw [if_neg h5]
  have hc : c ≠ nl := fun e => h3 (by simp [e, nl])
  simp only [List.mem_singleton]
  exact fun e => hc e.symm

theorem nl_not_mem_reprBody (q : UInt8) (hq : q = 0x22 ∨ q = 0x27) (b : Bytes) :
    nl ∉ reprBody q b := by
  unfold reprBody
  simp only [List.mem_flatMap, not_exists, not_and]
  intro c _
  exact nl_not_mem_reprEsc q c hq

/-- `read_stringnl` (`Lib/pickletools.py:317-362`) with its defaults, every outcome:

* `escapes`: on the line `repr(b)[1:]` (a quoted `repr` of bytes, with either quote,
  as protocol 0 `STRING` was written), it returns `b` decoded as Latin-1: "Embedded
  escapes are undone in the result" (`:339-341`);
* `body`: on any line quoted with `q`, the result is `escape_decode` of what is
  between the quotes, or its exception;
* `nonl`: no newline: `ValueError("no newline found when trying to read stringnl")`;
* `onequote`: a line that starts with a quote and does not end with it raises
  `"string quote %r not found at both ends of %r"`;
* `noquote`: a line that starts with neither quote raises `"no string quotes around %r"`.

A reader that ignores escapes, skips the newline check or skips the closing-quote
check fails. -/
def ReadStringnlExact : Prop :=
  (∀ (q : UInt8) (b pre rest : Bytes), (q = 0x22 ∨ q = 0x27) →
    readStringnl pre.length (pre ++ (q :: reprBody q b ++ [q]) ++ nl :: rest) =
      .ok (latin1 b, pre.length + ((reprBody q b).length + 2) + 1)) ∧
  (∀ (q : UInt8) (body pre rest : Bytes), (q = 0x22 ∨ q = 0x27) → nl ∉ body →
    readStringnl pre.length (pre ++ (q :: body ++ [q]) ++ nl :: rest) =
      atPos (latin1 <$> escapeDecode 0 body) (pre.length + (body.length + 2) + 1)) ∧
  (∀ pre short : Bytes, nl ∉ short →
    readStringnl pre.length (pre ++ short) =
      .error (.valueError "no newline found when trying to read stringnl")) ∧
  (∀ (q : UInt8) (line pre rest : Bytes), (q = 0x22 ∨ q = 0x27) → nl ∉ line →
    line.head? = some q → line.getLast? ≠ some q →
    readStringnl pre.length (pre ++ line ++ nl :: rest) =
      .error (.valueError "~string quote not found at both ends")) ∧
  (∀ line pre rest : Bytes, nl ∉ line → line.head? ≠ some 0x22 → line.head? ≠ some 0x27 →
    readStringnl pre.length (pre ++ line ++ nl :: rest) =
      .error (.valueError "~no string quotes around"))

theorem readStringnl_quoted (q : UInt8) (body pre rest : Bytes) (hq : q = 0x22 ∨ q = 0x27)
    (hn : nl ∉ body) :
    readStringnl pre.length (pre ++ (q :: body ++ [q]) ++ nl :: rest) =
      atPos (latin1 <$> escapeDecode 0 body) (pre.length + (body.length + 2) + 1) := by
  have hqn : q ≠ nl := by rcases hq with e | e <;> (rw [e]; decide)
  have hl : nl ∉ q :: body ++ [q] := by
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_singleton, not_or,
      List.not_mem_nil, or_false]
    exact ⟨fun e => hqn e.symm, hn, fun e => hqn e.symm⟩
  have hg : (q :: body ++ [q]).getLast? = some q := List.getLast?_concat
  have hh : (q :: body ++ [q]).head? = some q := rfl
  have hd : ((q :: body ++ [q]).drop 1).dropLast = body := by simp
  have hstrip : stripQuotes (q :: body ++ [q]) = .ok body := by
    unfold stripQuotes
    rw [hh, hg, hd]
    rcases hq with e | e <;> subst e <;> rfl
  have hlen : (q :: body ++ [q]).length = body.length + 2 := by simp
  unfold readStringnl
  rw [tBind, readRawnl_at pre _ rest hl, hlen]
  dsimp only
  rw [tBind]
  simp only [tLift, hstrip]
  rw [tBind]
  cases escapeDecode 0 body <;> rfl

theorem readStringnl_line (line pre rest : Bytes) (hn : nl ∉ line) :
    readStringnl pre.length (pre ++ line ++ nl :: rest) =
      match stripQuotes line with
      | .ok data => atPos (latin1 <$> escapeDecode 0 data) (pre.length + line.length + 1)
      | .error e => .error e := by
  unfold readStringnl
  rw [tBind, readRawnl_at pre line rest hn]
  dsimp only
  rw [tBind]
  cases stripQuotes line with
  | error e => rfl
  | ok data =>
    simp only [tLift]
    rw [tBind]
    cases escapeDecode 0 data <;> rfl

theorem readStringnlExact_proven : ReadStringnlExact := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q b pre rest hq
    rw [readStringnl_quoted q _ pre rest hq (nl_not_mem_reprBody q hq b),
      escapeDecode_reprBody q hq b 0]
    rfl
  · intro q body pre rest hq hn
    exact readStringnl_quoted q body pre rest hq hn
  · intro pre short h
    have hd : (pre ++ short).drop pre.length = short := List.drop_left
    have hl : (short.getLast? == some nl) ≠ true := by
      intro hb
      exact h (List.mem_of_getLast? (beq_iff_eq.mp hb))
    unfold readStringnl readRawnl
    rw [tBind, tBind]
    simp only [tReadline, hd, findIdx_none short h]
    rw [if_neg hl]
    rfl
  · intro q line pre rest hq hn hh hl
    rw [readStringnl_line line pre rest hn]
    have hs : stripQuotes line = .error (.valueError "~string quote not found at both ends") := by
      unfold stripQuotes
      rcases hq with e | e <;> subst e
      · rw [hh]
        simp only [beq_self_eq_true, if_true]
        rw [if_neg (by intro hb; exact hl (beq_iff_eq.mp hb))]
      · rw [hh]
        simp only [show (some (0x27 : UInt8) == some 0x22) = false from rfl, beq_self_eq_true,
          Bool.false_eq_true, if_false, if_true]
        rw [if_neg (by intro hb; exact hl (beq_iff_eq.mp hb))]
    rw [hs]
  · intro line pre rest hn h1 h2
    rw [readStringnl_line line pre rest hn]
    have hs : stripQuotes line = .error (.valueError "~no string quotes around") := by
      unfold stripQuotes
      rw [if_neg (by intro hb; exact h1 (beq_iff_eq.mp hb)),
        if_neg (by intro hb; exact h2 (beq_iff_eq.mp hb))]
    rw [hs]

end PyLean.Pickle
