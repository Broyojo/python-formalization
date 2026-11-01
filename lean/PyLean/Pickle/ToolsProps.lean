import PyLean.Pickle.Tools
import PyLean.Pickle.TextRoundtrip
import PyLean.Pickle.LongProps
import PyLean.Pickle.IntLineProps
import PyLean.Pickle.Narrow

/-!
Properties of the `pickletools` argument readers: each reads back what the
picklers write, at any position of any stream, and the text readers agree with
the unpickler's parsers.
-/

namespace PyLean.Pickle

open PyLean

theorem tBind {α β : Type} (m : TM α) (f : α → TM β) (pos : Nat) (d : Bytes) :
    (m >>= f) pos d = (match m pos d with
      | .ok (a, s) => f a s d
      | .error e => .error e) := by
  simp only [Bind.bind, StateT.bind, ReaderT.bind, Except.bind]
  cases m pos d <;> rfl

theorem tPure {α : Type} (a : α) (pos : Nat) (d : Bytes) :
    (pure a : TM α) pos d = .ok (a, pos) := rfl

theorem tRead_at (pre b rest : Bytes) :
    tRead b.length pre.length (pre ++ b ++ rest) = .ok (b, pre.length + b.length) := by
  have h : ((pre ++ b ++ rest).drop pre.length).take b.length = b := by
    rw [List.append_assoc, List.drop_left, List.take_left]
  simp only [tRead, h]

theorem needBytes_ok (b : Bytes) (name : String) (pos : Nat) (d : Bytes) :
    needBytes b.length name b pos d = .ok (b, pos) := by
  simp only [needBytes, if_true]
  rfl

/-- `readUintN` at any position of any stream. -/
theorem readUint_at (k : Nat) (name : String) (n : Nat) (pre rest : Bytes) (h : n < 256 ^ k) :
    readUintN k name pre.length (pre ++ leBytes n k ++ rest) = .ok (n, pre.length + k) := by
  have hr := tRead_at pre (leBytes n k) rest
  rw [leBytes_length] at hr
  unfold readUintN
  rw [tBind, hr]
  dsimp only
  rw [if_pos (leBytes_length n k), leNat_leBytes, Nat.mod_eq_of_lt h]
  rfl

/-- `readUintN` followed by a continuation. -/
theorem readUint_then {β : Type} (k : Nat) (name : String) (n : Nat) (pre rest : Bytes)
    (h : n < 256 ^ k) (f : Nat → TM β) :
    (readUintN k name >>= f) pre.length (pre ++ leBytes n k ++ rest) =
      f n (pre.length + k) (pre ++ leBytes n k ++ rest) := by
  rw [tBind, readUint_at k name n pre rest h]

/-- `read_uint1`, `read_uint2`, `read_uint4` and `read_uint8` return the integer
`struct.pack` wrote, and raise `ValueError` on fewer than `k` bytes. -/
def ReadUintExact : Prop :=
  (∀ (k : Nat) (name : String) (n : Nat) (pre rest : Bytes), n < 256 ^ k →
    readUintN k name pre.length (pre ++ leBytes n k ++ rest) = .ok (n, pre.length + k)) ∧
  (∀ (k : Nat) (name : String) (pre short : Bytes), short.length < k →
    ∃ m, readUintN k name pre.length (pre ++ short) = .error (.valueError m))

theorem readUintExact_proven : ReadUintExact := by
  refine ⟨readUint_at, ?_⟩
  intro k name pre short h
  refine ⟨s!"not enough data in stream to read {name}", ?_⟩
  have hd : (pre ++ short).drop pre.length = short := List.drop_left
  have hl : ((pre ++ short).drop pre.length).take k = short := by
    rw [hd]; exact List.take_of_length_le (by omega)
  unfold readUintN
  rw [tBind]
  simp only [tRead, hl]
  rw [if_neg (by omega)]
  rfl

/-- The pickler's `struct.pack("<i", x)` reads back through `read_int4`. -/
def ReadInt4Roundtrip : Prop :=
  ∀ (x : Int) (b pre rest : Bytes), packI32 x = .ok b →
    readInt4 pre.length (pre ++ b ++ rest) = .ok (x, pre.length + 4)

theorem readInt4Roundtrip_proven : ReadInt4Roundtrip := by
  intro x b pre rest h
  unfold packI32 at h
  split at h
  · rename_i hx
    injection h with h
    subst h
    have hl : (toBytesSigned x 4).length = 4 := leBytes_length _ _
    have hv : leInt (toBytesSigned x 4) = x :=
      leInt_toBytesSigned x 4 (by omega) (by omega) (by omega)
    have hr := tRead_at pre (toBytesSigned x 4) rest
    rw [hl] at hr
    unfold readInt4
    rw [tBind, hr]
    dsimp only
    rw [if_pos hl, hv]
    rfl
  · cases h

/-- Every counted reader returns the payload the matching opcode wrote, and
stops right after it. The bounds are the sizes of the count fields. -/
def ReadCountedRoundtrip : Prop :=
  ∀ pre b rest : Bytes,
    (b.length < 256 → readBytes1 pre.length (pre ++ leBytes b.length 1 ++ (b ++ rest)) =
      .ok (b, pre.length + 1 + b.length)) ∧
    (b.length < 256 → readString1 pre.length (pre ++ leBytes b.length 1 ++ (b ++ rest)) =
      .ok (latin1 b, pre.length + 1 + b.length)) ∧
    (b.length < 2 ^ 32 → readBytes4 pre.length (pre ++ leBytes b.length 4 ++ (b ++ rest)) =
      .ok (b, pre.length + 4 + b.length)) ∧
    (b.length ≤ ssizeMaxN → readBytes8 pre.length (pre ++ leBytes b.length 8 ++ (b ++ rest)) =
      .ok (b, pre.length + 8 + b.length)) ∧
    (b.length ≤ ssizeMaxN → readBytearray8 pre.length (pre ++ leBytes b.length 8 ++ (b ++ rest)) =
      .ok (b, pre.length + 8 + b.length))

theorem readCounted_at (name : String) (pre b rest : Bytes) (k : Nat) (hb : b.length ≤ ssizeMaxN) :
    readCounted b.length name (pre.length + k)
      ((pre ++ leBytes b.length k) ++ b ++ rest) = .ok (b, pre.length + k + b.length) := by
  have hp : (pre ++ leBytes b.length k).length = pre.length + k := by simp [leBytes_length]
  have hr := tRead_at (pre ++ leBytes b.length k) b rest
  rw [hp] at hr
  unfold readCounted
  rw [if_neg (by omega), tBind, hr]
  exact needBytes_ok b name _ _

theorem readCountedRoundtrip_proven : ReadCountedRoundtrip := by
  intro pre b rest
  have hp (k : Nat) : (pre ++ leBytes b.length k).length = pre.length + k := by
    simp [leBytes_length]
  have rd (k : Nat) := tRead_at (pre ++ leBytes b.length k) b rest
  have assoc (k : Nat) : pre ++ leBytes b.length k ++ (b ++ rest) =
      (pre ++ leBytes b.length k) ++ b ++ rest := by simp [List.append_assoc]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · unfold readBytes1 readUint1
    rw [readUint_then 1 _ _ _ _ (by omega), assoc, tBind, ← hp 1, rd 1]
    exact needBytes_ok b _ _ _
  · unfold readString1 readUint1
    rw [readUint_then 1 _ _ _ _ (by omega), assoc, tBind, ← hp 1, rd 1]
    dsimp only
    rw [tBind, needBytes_ok]
    rfl
  · unfold readBytes4 readUint4
    have hs : b.length ≤ ssizeMaxN := by unfold ssizeMaxN; omega
    show (readUintN 4 "uint4" >>= fun n => readCounted n "bytes4") _ _ = _
    rw [readUint_then 4 _ _ _ _ (by omega), assoc]
    exact readCounted_at _ pre b rest 4 hs
  · unfold readBytes8 readUint8
    have hlt : b.length < 256 ^ 8 := by unfold ssizeMaxN at h; omega
    show (readUintN 8 "uint8" >>= fun n => readCounted n "bytes8") _ _ = _
    rw [readUint_then 8 _ _ _ _ hlt, assoc]
    exact readCounted_at _ pre b rest 8 h
  · unfold readBytearray8 readUint8
    have hlt : b.length < 256 ^ 8 := by unfold ssizeMaxN at h; omega
    show (readUintN 8 "uint8" >>= fun n => readCounted n "bytearray8") _ _ = _
    rw [readUint_then 8 _ _ _ _ hlt, assoc]
    exact readCounted_at _ pre b rest 8 h

theorem leInt_small (b : Bytes) (hl : b.length = 4) (h : leNat b < 2 ^ 31) :
    leInt b = (leNat b : Int) := by
  unfold leInt
  rw [if_neg]
  intro hc
  have h2 := hc.2
  rw [hl] at h2
  exact absurd h2 (Nat.not_le.mpr h)

theorem readInt4_at (n : Nat) (pre rest : Bytes) (h : n < 2 ^ 31) :
    readInt4 pre.length (pre ++ leBytes n 4 ++ rest) = .ok ((n : Int), pre.length + 4) := by
  have hr := tRead_at pre (leBytes n 4) rest
  rw [leBytes_length] at hr
  have hv : leNat (leBytes n 4) = n := by
    rw [leNat_leBytes]; exact Nat.mod_eq_of_lt (by omega)
  have hi : leInt (leBytes n 4) = (n : Int) := by
    rw [leInt_small _ (leBytes_length n 4) (by rw [hv]; exact h), hv]
  unfold readInt4
  rw [tBind, hr]
  dsimp only
  rw [if_pos (leBytes_length n 4), hi]
  rfl

theorem readInt4_then {β : Type} (n : Nat) (pre rest : Bytes) (h : n < 2 ^ 31) (f : Int → TM β) :
    (readInt4 >>= f) pre.length (pre ++ leBytes n 4 ++ rest) =
      f (n : Int) (pre.length + 4) (pre ++ leBytes n 4 ++ rest) := by
  rw [tBind, readInt4_at n pre rest h]

/-- `read_string4`: the count is a signed int, so payloads under 2**31 bytes. -/
def ReadString4Roundtrip : Prop :=
  ∀ pre b rest : Bytes, b.length < 2 ^ 31 →
    readString4 pre.length (pre ++ leBytes b.length 4 ++ (b ++ rest)) =
      .ok (latin1 b, pre.length + 4 + b.length)

theorem readString4Roundtrip_proven : ReadString4Roundtrip := by
  intro pre b rest h
  have hp : (pre ++ leBytes b.length 4).length = pre.length + 4 := by simp [leBytes_length]
  have hr := tRead_at (pre ++ leBytes b.length 4) b rest
  rw [hp] at hr
  have assoc : pre ++ leBytes b.length 4 ++ (b ++ rest) =
      (pre ++ leBytes b.length 4) ++ b ++ rest := by simp [List.append_assoc]
  unfold readString4
  rw [readInt4_then _ _ _ h, assoc, if_neg (by omega)]
  have hn : ((b.length : Int)).toNat = b.length := by omega
  rw [hn, tBind, hr]
  dsimp only
  rw [tBind, needBytes_ok]
  rfl

/-- `read_long1` and `read_long4` read back `encode_long`, at every size their
count fields hold. -/
def ReadLongRoundtrip : Prop :=
  ∀ (x : Int) (pre rest : Bytes),
    ((encodeLong x).length < 256 →
      readLong1 pre.length (pre ++ leBytes (encodeLong x).length 1 ++ (encodeLong x ++ rest)) =
        .ok (x, pre.length + 1 + (encodeLong x).length)) ∧
    ((encodeLong x).length < 2 ^ 31 →
      readLong4 pre.length (pre ++ leBytes (encodeLong x).length 4 ++ (encodeLong x ++ rest)) =
        .ok (x, pre.length + 4 + (encodeLong x).length))

theorem readLongRoundtrip_proven : ReadLongRoundtrip := by
  intro x pre rest
  have hx := decodeEncodeLong_proven x
  generalize encodeLong x = e at hx ⊢
  have hp (k : Nat) : (pre ++ leBytes e.length k).length = pre.length + k := by
    simp [leBytes_length]
  have rd (k : Nat) := tRead_at (pre ++ leBytes e.length k) e rest
  have assoc (k : Nat) : pre ++ leBytes e.length k ++ (e ++ rest) =
      (pre ++ leBytes e.length k) ++ e ++ rest := by simp [List.append_assoc]
  constructor
  · intro h
    unfold readLong1 readUint1
    rw [readUint_then 1 _ _ _ _ (by omega), assoc, tBind, ← hp 1, rd 1]
    dsimp only
    rw [if_neg (by simp), hx]
    rfl
  · intro h
    unfold readLong4
    rw [readInt4_then _ _ _ h, assoc, if_neg (by omega)]
    have hn : ((e.length : Int)).toNat = e.length := by omega
    rw [hn, tBind, ← hp 4, rd 4]
    dsimp only
    rw [if_neg (by simp), hx]
    rfl

/-- The counted unicode readers return the decoder's result on the payload. -/
def ReadUnicodeRoundtrip : Prop :=
  ∀ (pre b rest : Bytes) (s : List Nat), decodeUtf8SP b = .ok s →
    (b.length < 256 → readUnicodestring1 pre.length (pre ++ leBytes b.length 1 ++ (b ++ rest)) =
      .ok (s, pre.length + 1 + b.length)) ∧
    (b.length < 2 ^ 32 → readUnicodestring4 pre.length (pre ++ leBytes b.length 4 ++ (b ++ rest)) =
      .ok (s, pre.length + 4 + b.length)) ∧
    (b.length ≤ ssizeMaxN → readUnicodestring8 pre.length (pre ++ leBytes b.length 8 ++ (b ++ rest)) =
      .ok (s, pre.length + 8 + b.length))

theorem readUnicodeRoundtrip_proven : ReadUnicodeRoundtrip := by
  intro pre b rest s hs
  have hp (k : Nat) : (pre ++ leBytes b.length k).length = pre.length + k := by
    simp [leBytes_length]
  have rd (k : Nat) := tRead_at (pre ++ leBytes b.length k) b rest
  have assoc (k : Nat) : pre ++ leBytes b.length k ++ (b ++ rest) =
      (pre ++ leBytes b.length k) ++ b ++ rest := by simp [List.append_assoc]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · unfold readUnicodestring1 readUint1
    rw [readUint_then 1 _ _ _ _ (by omega), assoc, tBind, ← hp 1, rd 1]
    dsimp only
    rw [tBind, needBytes_ok]
    simp only [tLift, hs]
  · have hb : b.length ≤ ssizeMaxN := by unfold ssizeMaxN; omega
    unfold readUnicodestring4 readUint4
    rw [readUint_then 4 _ _ _ _ (by omega), assoc, tBind, readCounted_at _ pre b rest 4 hb]
    simp only [tLift, hs]
  · have hlt : b.length < 256 ^ 8 := by unfold ssizeMaxN at h; omega
    unfold readUnicodestring8 readUint8
    rw [readUint_then 8 _ _ _ _ hlt, assoc, tBind, readCounted_at _ pre b rest 8 h]
    simp only [tLift, hs]

/-- `read_float8` returns exactly eight bytes, and raises on fewer. The value
of those bytes as a float is left to `struct.unpack`. -/
def ReadFloat8Exact : Prop :=
  (∀ pre b rest : Bytes, b.length = 8 →
    readFloat8 pre.length (pre ++ b ++ rest) = .ok (b, pre.length + 8)) ∧
  (∀ pre short : Bytes, short.length < 8 →
    readFloat8 pre.length (pre ++ short) =
      .error (.valueError "not enough data in stream to read float8"))

theorem readFloat8Exact_proven : ReadFloat8Exact := by
  constructor
  · intro pre b rest h
    have hr := tRead_at pre b rest
    rw [h] at hr
    unfold readFloat8
    rw [tBind, hr]
    dsimp only
    rw [if_pos h]
    rfl
  · intro pre short h
    have hd : (pre ++ short).drop pre.length = short := List.drop_left
    have hl : ((pre ++ short).drop pre.length).take 8 = short := by
      rw [hd]; exact List.take_of_length_le (by omega)
    unfold readFloat8
    rw [tBind]
    simp only [tRead, hl]
    rw [if_neg (by omega)]
    rfl

/-! ## Line readers -/

theorem findIdx_nl (line rest : Bytes) (h : nl ∉ line) :
    (line ++ nl :: rest).findIdx? (· == nl) = some line.length := by
  induction line with
  | nil => simp [List.findIdx?_cons]
  | cons a l ih =>
    have ha : a ≠ nl := fun e => h (e ▸ List.mem_cons_self)
    have hl : nl ∉ l := fun m => h (List.mem_cons_of_mem _ m)
    simp [List.findIdx?_cons, ha, ih hl]

theorem tReadline_at (pre line rest : Bytes) (h : nl ∉ line) :
    tReadline pre.length (pre ++ line ++ nl :: rest) =
      .ok (line ++ [nl], pre.length + line.length + 1) := by
  have hd : (pre ++ line ++ nl :: rest).drop pre.length = line ++ nl :: rest := by
    rw [List.append_assoc, List.drop_left]
  have ht : ∀ l : Bytes, (l ++ nl :: rest).take (l.length + 1) = l ++ [nl] := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp only [List.cons_append, List.length_cons, List.take_succ_cons, ih]
  simp only [tReadline, hd, findIdx_nl line rest h, ht]
  simp [Nat.add_assoc]

theorem readRawnl_at (pre line rest : Bytes) (h : nl ∉ line) :
    readRawnl pre.length (pre ++ line ++ nl :: rest) =
      .ok (line, pre.length + line.length + 1) := by
  have h1 : (line ++ [nl]).getLast? = some nl := by simp
  have h2 : (line ++ [nl]).dropLast = line := by simp
  unfold readRawnl
  rw [tBind, tReadline_at pre line rest h]
  dsimp only
  rw [if_pos (by rw [h1]; rfl), h2]
  rfl

/-- `pickletools` calls `int(s)` without the newline, the unpickler calls
`int(data)` with it: the same outcome. -/
theorem pyInt_nl (s : Bytes) : SameOutcome (pyIntOfBytes s) (pyIntOfBytes (s ++ [nl])) := by
  by_cases hz : (0 : UInt8) ∈ s
  · have h1 := pyIntOfBytes_nul s hz
    have h2 := pyIntOfBytes_nul (s ++ [nl]) (List.mem_append_left _ hz)
    cases ha : pyIntOfBytes s with
    | ok v => rw [ha] at h1; simp [isErr] at h1
    | error e =>
      cases hb : pyIntOfBytes (s ++ [nl]) with
      | ok v => rw [hb] at h2; simp [isErr] at h2
      | error e' => exact trivial
  · have hz2 : (0 : UInt8) ∉ s ++ [nl] := by
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨hz, by decide⟩
    unfold pyIntOfBytes
    dsimp only
    rw [takeWhile_ne_zero_of_not_mem hz, takeWhile_ne_zero_of_not_mem hz2,
      pyLongFromString_append_space _ isSpace_nl]
    cases pyLongFromString s <;> simp [SameOutcome]

/-- The int-or-bool result of `load_int` as a `read_decimalnl_short` value. -/
def tvOfInt : IntVal → TV
  | .int i => .int i
  | .bool b => .bool b

/-- The value of a reader, without its position. -/
def valOf {α : Type} (r : Except PyExc (α × Nat)) : Py α :=
  match r with
  | .ok (a, _) => .ok a
  | .error e => .error e

/-- On every complete line, `read_decimalnl_short` and the unpickler's `load_int`
accept the same lines and return the same int or bool. Source: `pickletools`
vs `pickle`. -/
def DecimalShortTwin : Prop :=
  ∀ pre line rest : Bytes, nl ∉ line →
    SameOutcome (valOf (readDecimalnlShort pre.length (pre ++ line ++ nl :: rest)))
      (tvOfInt <$> pyLoadIntLine (line ++ [nl]))

theorem decimalShortTwin_proven : DecimalShortTwin := by
  intro pre line rest h
  unfold readDecimalnlShort
  rw [tBind, readRawnl_at pre line rest h]
  dsimp only
  by_cases h0 : line = [0x30, 0x30]
  · subst h0
    rfl
  by_cases h1 : line = [0x30, 0x31]
  · subst h1
    rfl
  have n0 : line ++ [nl] ≠ [0x30, 0x30, nl] := fun e =>
    h0 (List.append_cancel_right (show line ++ [nl] = [0x30, 0x30] ++ [nl] from e))
  have n1 : line ++ [nl] ≠ [0x30, 0x31, nl] := fun e =>
    h1 (List.append_cancel_right (show line ++ [nl] = [0x30, 0x31] ++ [nl] from e))
  have hpy : pyLoadIntLine (line ++ [nl]) = IntVal.int <$> pyIntOfBytes (line ++ [nl]) := by
    unfold pyLoadIntLine
    rw [if_neg n0, if_neg n1]
  rw [hpy, if_neg h0, if_neg h1]
  have hs := pyInt_nl line
  cases ha : pyIntOfBytes line with
  | ok v =>
    cases hb : pyIntOfBytes (line ++ [nl]) with
    | ok w =>
      rw [ha, hb] at hs
      simp only [SameOutcome] at hs
      subst hs
      rfl
    | error e => rw [ha, hb] at hs; exact hs.elim
  | error e =>
    cases hb : pyIntOfBytes (line ++ [nl]) with
    | ok w => rw [ha, hb] at hs; exact hs.elim
    | error e' => exact trivial

/-- On every complete line, `read_decimalnl_long` and the unpickler's `load_long`
are the same function, message included. -/
def DecimalLongTwin : Prop :=
  ∀ pre line rest : Bytes, nl ∉ line →
    valOf (readDecimalnlLong pre.length (pre ++ line ++ nl :: rest)) =
      pyLoadLongLine (line ++ [nl])

theorem decimalLongTwin_proven : DecimalLongTwin := by
  intro pre line rest h
  have hd : (line ++ [nl]).dropLast = line := by simp
  unfold readDecimalnlLong pyLoadLongLine
  rw [tBind, readRawnl_at pre line rest h]
  dsimp only
  rw [hd]
  by_cases hL : line.getLast? = some 0x4c
  · have hne : line ≠ [] := by intro e; subst e; simp at hL
    simp [hL, hne, tLift, valOf]
    cases pyIntOfBytes line.dropLast <;> rfl
  · simp [hL, tLift, valOf]
    cases pyIntOfBytes line <;> rfl

theorem escapeDecode_plain (b : Bytes) (h : (0x5c : UInt8) ∉ b) (pos : Nat) :
    escapeDecode pos b = .ok b := by
  induction b generalizing pos with
  | nil => rw [escapeDecode.eq_def]
  | cons c r ih =>
    have hc : c ≠ 0x5c := fun e => h (e ▸ List.mem_cons_self)
    have hr : (0x5c : UInt8) ∉ r := fun m => h (List.mem_cons_of_mem _ m)
    rw [escapeDecode.eq_def]
    dsimp only
    rw [if_pos (bne_iff_ne.mpr hc), ih hr (pos + 1)]
    rfl

/-- `read_stringnl` on a quoted line without escapes returns what is between the
quotes, with either quote. -/
def ReadStringnlPlain : Prop :=
  ∀ (q : UInt8) (body pre rest : Bytes), (q = 0x22 ∨ q = 0x27) → nl ∉ body → 0x5c ∉ body →
    readStringnl pre.length (pre ++ (q :: body ++ [q]) ++ nl :: rest) =
      .ok (latin1 body, pre.length + (body.length + 2) + 1)

theorem readStringnlPlain_proven : ReadStringnlPlain := by
  intro q body pre rest hq hn hb
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
  simp only [escapeDecode_plain body hb 0]
  rfl

/-- `read_stringnl_noescape` returns the line as `load_global` and `load_persid`
read it: decoded and otherwise untouched. The descriptor says "without embedded
escapes", and the unpickler undoes none. -/
def NoescapeVerbatim : Prop :=
  ∀ (line : Bytes) (s : List Nat), nl ∉ line → utf8Dec false line = some s →
    valOf (readStringnlNoescape 0 (line ++ [nl])) = .ok s

theorem noescapeVerbatim_refuted : ¬NoescapeVerbatim := by
  intro h
  have hu : utf8Dec false [0x5c] = some [0x5c] := by decide +kernel
  have h1 := h [0x5c] [0x5c] (by decide) hu
  have hr := readRawnl_at [] [0x5c] [] (by decide)
  have he : escapeDecode 0 [0x5c] = .error (.valueError "Trailing \\ in string") := by
    rw [escapeDecode.eq_def]; rfl
  simp only [List.nil_append, List.length_nil] at hr
  have hs : readStringnlNoescape 0 ([0x5c] ++ [nl]) =
      .error (.valueError "Trailing \\ in string") := by
    unfold readStringnlNoescape
    rw [tBind]
    have e2 : [(0x5c : UInt8)] ++ [nl] = [0x5c] ++ nl :: [] := rfl
    rw [e2, hr]
    dsimp only
    rw [tBind]
    simp only [tLift, he]
  rw [hs] at h1
  cases h1

theorem noescape_at (line pre rest : Bytes) (hn : nl ∉ line) (hb : (0x5c : UInt8) ∉ line) :
    readStringnlNoescape pre.length (pre ++ line ++ nl :: rest) =
      match utf8Dec false line with
      | some s => .ok (s, pre.length + line.length + 1)
      | none => .error unicodeDecodeError := by
  unfold readStringnlNoescape
  rw [tBind, readRawnl_at pre line rest hn]
  dsimp only
  rw [tBind]
  simp only [tLift, escapeDecode_plain line hb 0]
  cases utf8Dec false line <;> rfl

/-- The same on every line without a backslash, and for the module and name pair
of `GLOBAL`. -/
def NoescapeNoBackslash : Prop :=
  (∀ (line pre rest : Bytes), nl ∉ line → 0x5c ∉ line →
    valOf (readStringnlNoescape pre.length (pre ++ line ++ nl :: rest)) =
      match utf8Dec false line with
      | some s => .ok s
      | none => .error unicodeDecodeError) ∧
  (∀ (a b : Bytes) (u v : List Nat), nl ∉ a → nl ∉ b → 0x5c ∉ a → 0x5c ∉ b →
    utf8Dec false a = some u → utf8Dec false b = some v →
    valOf (readStringnlNoescapePair 0 (a ++ nl :: b ++ [nl])) = .ok (u ++ [0x20] ++ v))

theorem noescapeNoBackslash_proven : NoescapeNoBackslash := by
  constructor
  · intro line pre rest hn hb
    rw [noescape_at line pre rest hn hb]
    cases utf8Dec false line <;> rfl
  · intro a b u v hna hnb hba hbb hu hv
    have h1 := noescape_at a [] (b ++ [nl]) hna hba
    have h2 := noescape_at b (a ++ [nl]) [] hnb hbb
    rw [hu] at h1
    rw [hv] at h2
    have e1 : ([] : Bytes) ++ a ++ nl :: (b ++ [nl]) = a ++ nl :: b ++ [nl] := by simp
    have e2 : a ++ [nl] ++ b ++ nl :: [] = a ++ nl :: b ++ [nl] := by simp
    have l1 : ([] : Bytes).length + a.length + 1 = (a ++ [nl]).length := by simp
    have h0 : ([] : Bytes).length = 0 := rfl
    rw [e1, l1, h0] at h1
    rw [e2] at h2
    unfold readStringnlNoescapePair
    rw [tBind, h1]
    dsimp only
    rw [tBind, h2]
    rfl

end PyLean.Pickle
