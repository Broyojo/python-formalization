import PyLean.Pickle.EncRecProps
import PyLean.Pickle.LongLemmas

/-!
Exact outputs of the bounded twins, so that the twin theorems are not satisfied by two encoders
that always raise or pick the same wrong opcode: the atoms and the `buffer_callback` check for
every protocol, the memo opcodes by index size, the opcode and length field of every size class
of the `bytes`, `str` and `bytearray` savers, and the frames of both framers. Each length field is
stated by what it decodes to (`leNat`), not by the encoder that wrote it.
-/

namespace PyLean.Pickle

open PyLean

theorem leNat_le4 {n : Nat} (h : n < 2 ^ 32) : leNat (leBytes n 4) = n := by
  rw [leNat_leBytes]; exact Nat.mod_eq_of_lt h

theorem leNat_le1 {n : Nat} (h : n < 2 ^ 8) : leNat (leBytes n 1) = n := by
  rw [leNat_leBytes]; exact Nat.mod_eq_of_lt h

theorem leNat_le8 {n : Nat} (h : n < 2 ^ 64) : leNat (leBytes n 8) = n := by
  rw [leNat_leBytes]; exact Nat.mod_eq_of_lt h

/-! ## Atoms and `buffer_callback`, every protocol -/

/-- The opcode bytes of `None` and the bools (`save_none`, `save_bool`). -/
def atomOp (p : Nat) : PV → Bytes
  | .none => [oNONE]
  | .bool v => if p ≥ 2 then [if v then oNEWTRUE else oNEWFALSE] else [oINT, 0x30, if v then 0x31 else 0x30, nl]
  | _ => []

/-- `pickle.dumps(x, p, buffer_callback=...)` for `None`, `True` and `False`: ValueError when a
callback is given below protocol 5, else `PROTO p` from protocol 2, the opcode, `STOP`; the
frame of protocol 4 and up holds fewer than 4 bytes, so it gets no `FRAME` header. -/
def atomOut (p : Nat) (bufcb : Bool) (x : PV) : Py Bytes :=
  if bufcb = true ∧ p < 5 then .error bufErr
  else .ok ((if p ≥ 2 then [oPROTO, p.toUInt8] else []) ++ atomOp p x ++ [oSTOP])

def AtomsExact : Prop :=
  ∀ (p : Nat) (bufcb : Bool) (x : PV) (c b : Nat), p ≤ 5 → (x = .none ∨ x = .bool true ∨ x = .bool false) →
    4 ≤ c → 18 ≤ b →
    cDumpsA c x { protocol := .int p, bufcb := bufcb } = atomOut p bufcb x ∧
    pyDumpsA b x { protocol := .int p, bufcb := bufcb } = atomOut p bufcb x

theorem atomsExact_proven : AtomsExact := by
  intro p bufcb x c b hp hx hc hb
  have hd : x.dep = 0 := by rcases hx with rfl | rfl | rfl <;> rfl
  rw [cDumpsA_exact x _ (by omega), pyDumpsA_exact x _ (by omega)]
  obtain rfl | rfl | rfl | rfl | rfl | rfl : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 := (by omega)
  all_goals (cases bufcb <;> rcases hx with rfl | rfl | rfl <;> decide +kernel)

/-! ## Memo opcodes by index size -/

/-- `memo_put`/`memo_get` (C) and `_Pickler.put`/`_Pickler.get` (Python): `MEMOIZE` from
protocol 4; text `PUT`/`GET` with the decimal index at protocol 0; otherwise a one-byte index
below 256, a 4-byte index that reads back as `i` below `2**32`, and an error above. -/
def MemoOpsExact : Prop :=
  ∀ (p i : Nat),
    (p ≥ 4 → cPut p i = .ok [oMEMOIZE] ∧ pyPut p i = .ok [oMEMOIZE]) ∧
    (p = 0 → cPut p i = .ok (oPUT :: decDigits i ++ [nl]) ∧ pyPut p i = .ok (oPUT :: decDigits i ++ [nl]) ∧
      cGet p i = .ok (oGET :: decDigits i ++ [nl]) ∧ pyGet p i = .ok (oGET :: decDigits i ++ [nl])) ∧
    (1 ≤ p → p < 4 → i < 256 → cPut p i = .ok [oBINPUT, i.toUInt8] ∧ pyPut p i = .ok [oBINPUT, i.toUInt8]) ∧
    (1 ≤ p → i < 256 → cGet p i = .ok [oBINGET, i.toUInt8] ∧ pyGet p i = .ok [oBINGET, i.toUInt8]) ∧
    (1 ≤ p → p < 4 → 256 ≤ i → i < 2 ^ 32 → ∃ f, f.length = 4 ∧ leNat f = i ∧
      cPut p i = .ok (oLONG_BINPUT :: f) ∧ pyPut p i = .ok (oLONG_BINPUT :: f)) ∧
    (1 ≤ p → 256 ≤ i → i < 2 ^ 32 → ∃ f, f.length = 4 ∧ leNat f = i ∧
      cGet p i = .ok (oLONG_BINGET :: f) ∧ pyGet p i = .ok (oLONG_BINGET :: f)) ∧
    (1 ≤ p → p < 4 → 2 ^ 32 ≤ i → (∃ e, cPut p i = .error e) ∧ ∃ e, pyPut p i = .error e) ∧
    (1 ≤ p → 2 ^ 32 ≤ i → (∃ e, cGet p i = .error e) ∧ ∃ e, pyGet p i = .error e)

theorem memoOpsExact_proven : MemoOpsExact := by
  intro p i
  refine ⟨fun h => ?_, fun h => ?_, fun h1 h4 hi => ?_, fun h1 hi => ?_, fun h1 h4 hl hu => ?_,
    fun h1 hl hu => ?_, fun h1 h4 hu => ?_, fun h1 hu => ?_⟩
  · simp [cPut, pyPut, h]
  · subst h; simp [cPut, pyPut, cGet, pyGet]
  · simp [cPut, pyPut, show ¬ p ≥ 4 by omega, show p ≠ 0 by omega, show p ≥ 1 by omega, hi]
  · simp [cGet, pyGet, show p ≠ 0 by omega, show p ≥ 1 by omega, hi]
  · refine ⟨leBytes i 4, leBytes_length _ _, leNat_le4 hu, ?_, ?_⟩
    · simp [cPut, show ¬ p ≥ 4 by omega, show p ≠ 0 by omega, show ¬ i < 256 by omega,
        show i ≤ 0xffffffff by omega]
    · simp [pyPut, packU32, show ¬ p ≥ 4 by omega, show p ≥ 1 by omega, show ¬ i < 256 by omega,
        show i ≤ 4294967295 by omega, Functor.map, Except.map]
  · refine ⟨leBytes i 4, leBytes_length _ _, leNat_le4 hu, ?_, ?_⟩
    · simp [cGet, show p ≠ 0 by omega, show ¬ i < 256 by omega, show i ≤ 0xffffffff by omega]
    · simp [pyGet, packU32, show p ≥ 1 by omega, show ¬ i < 256 by omega,
        show i ≤ 4294967295 by omega, Functor.map, Except.map]
  · refine ⟨⟨picklingError "memo id too large for LONG_BINPUT", ?_⟩,
      ⟨structError "'I' format requires 0 <= number <= 4294967295", ?_⟩⟩
    · simp [cPut, show ¬ p ≥ 4 by omega, show p ≠ 0 by omega, show ¬ i < 256 by omega,
        show ¬ i ≤ 0xffffffff by omega]
    · simp [pyPut, packU32, show ¬ p ≥ 4 by omega, show p ≥ 1 by omega, show ¬ i < 256 by omega,
        show ¬ i ≤ 4294967295 by omega, Functor.map, Except.map]
  · refine ⟨⟨picklingError "memo id too large for LONG_BINGET", ?_⟩,
      ⟨structError "'I' format requires 0 <= number <= 4294967295", ?_⟩⟩
    · simp [cGet, show p ≠ 0 by omega, show ¬ i < 256 by omega, show ¬ i ≤ 0xffffffff by omega]
    · simp [pyGet, packU32, show p ≥ 1 by omega, show ¬ i < 256 by omega,
        show ¬ i ≤ 4294967295 by omega, Functor.map, Except.map]

/-! ## Size classes of the data savers -/

/-- The calls a saver leaves, most recent first. -/
def After (s : EncSt) (evs : List Event) : EncSt := { s with ev := evs ++ s.ev }

/-- How C's `_Pickler_write_bytes` (`Modules/_pickle.c:2553-2617`) passes a header and payload
to `dumps`: past `FRAME_SIZE_TARGET` outside the frame, else two writes. -/
def cHP (h d : Bytes) : List Event := if d.length ≥ 65536 then [.large h d] else [.w d, .w h]

/-- How Python passes them: `_write_large_bytes` past the target, else one `write`. -/
def pyHP (h d : Bytes) : List Event := if d.length ≥ 65536 then [.large h d] else [.w (h ++ d)]

theorem ex_bytesData {b : Nat} (hb : 2 ≤ b) (p : Nat) (d : Bytes) :
    pySaveBytesDataR b p d = pySaveBytesData p d :=
  eq_ite (fun _ => ex_pyW (by omega) _) fun _ => eq_ite (fun _ => ex_large hb _ _ _) fun _ =>
    eq_ite (fun _ => eq_bind rfl fun _ => ex_large hb _ _ _) (fun _ => eq_bind rfl fun _ => ex_pyW (by omega) _)

theorem ex_bytearrayData {b : Nat} (hb : 2 ≤ b) (p : Nat) (d : Bytes) :
    pySaveBytearrayDataR b p d = pySaveBytearrayData d :=
  eq_ite (fun _ => ex_large hb _ _ _) (fun _ => ex_pyW (by omega) _)

/-- The size classes of `_save_bytes_data` and `_save_bytes_no_memo`, protocol 3 and up, for a
header-and-payload layout `hp`: `SHORT_BINBYTES` with a 1-byte length to 255, `BINBYTES` with a
4-byte length that reads back as the size below `2**32`, `BINBYTES8` with an 8-byte one from
protocol 4, an error at protocol 3. -/
def BytesClasses (hp : Bytes → Bytes → List Event) (m : Nat → Bytes → EncM Unit) : Prop :=
  ∀ (p : Nat) (d : Bytes) (s : EncSt), 3 ≤ p →
    (d.length ≤ 0xff → ∃ f, f.length = 1 ∧ leNat f = d.length ∧
      m p d s = .ok ((), After s (hp (oSHORT_BINBYTES :: f) d))) ∧
    (0xff < d.length → d.length < 2 ^ 32 → ∃ f, f.length = 4 ∧ leNat f = d.length ∧
      m p d s = .ok ((), After s (hp (oBINBYTES :: f) d))) ∧
    (2 ^ 32 ≤ d.length → d.length < 2 ^ 64 → 4 ≤ p → ∃ f, f.length = 8 ∧ leNat f = d.length ∧
      m p d s = .ok ((), After s (hp (oBINBYTES8 :: f) d))) ∧
    (2 ^ 32 ≤ d.length → p = 3 → ∃ e, m p d s = .error e)

theorem cBytesClasses : BytesClasses cHP cSaveBytesData := by
  intro p d s hp3
  refine ⟨fun h => ⟨leBytes d.length 1, leBytes_length _ _, leNat_le1 (by omega), ?_⟩, fun h1 h2 => ⟨leBytes d.length 4, leBytes_length _ _, leNat_le4 h2, ?_⟩,
    fun h1 h2 h4 => ⟨leBytes d.length 8, leBytes_length _ _, leNat_le8 h2, ?_⟩, fun h1 h3 => ⟨.overflowError "serializing a bytes object larger than 4 GiB requires pickle protocol 4 or higher", ?_⟩⟩
  · unfold cSaveBytesData cWriteBytes
    rw [if_pos h]
    simp only [pure_bind, frameSizeTarget, cHP, show ¬ d.length ≥ 65536 by omega, ↓reduceIte]
    rfl
  · unfold cSaveBytesData cWriteBytes
    rw [if_neg (by omega), if_pos (show d.length ≤ 0xffffffff by omega)]
    unfold cHP frameSizeTarget
    split <;> rfl
  · unfold cSaveBytesData cWriteBytes
    rw [if_neg (by omega), if_neg (show ¬ d.length ≤ 0xffffffff by omega), if_pos h4,
]
    simp only [pure_bind, frameSizeTarget, cHP, show d.length ≥ 65536 by omega, ↓reduceIte]
    rfl
  · unfold cSaveBytesData
    rw [if_neg (by omega), if_neg (show ¬ d.length ≤ 0xffffffff by omega), if_neg (by omega)]
    rfl

theorem pyBytesClasses (b : Nat) (hb : 2 ≤ b) : BytesClasses pyHP (fun p d => pySaveBytesDataR b p d) := by
  intro p d s hp3
  simp only
  rw [ex_bytesData hb]
  refine ⟨fun h => ⟨leBytes d.length 1, leBytes_length _ _, leNat_le1 (by omega), ?_⟩, fun h1 h2 => ⟨leBytes d.length 4, leBytes_length _ _, leNat_le4 h2, ?_⟩,
    fun h1 h2 h4 => ⟨leBytes d.length 8, leBytes_length _ _, leNat_le8 h2, ?_⟩, fun h1 h3 => ⟨structError "'I' format requires 0 <= number <= 4294967295", ?_⟩⟩
  · unfold pySaveBytesData
    rw [if_pos h]
    simp only [pyHP, show ¬ d.length ≥ 65536 by omega, ↓reduceIte]
    rfl
  · unfold pySaveBytesData
    rw [if_neg (by omega), if_neg (by omega)]
    have hpk : packU32 d.length = .ok (leBytes d.length 4) := by unfold packU32; rw [if_pos (by omega)]
    rw [hpk]
    unfold pyHP frameSizeTarget
    split <;> rfl
  · unfold pySaveBytesData
    rw [if_neg (by omega), if_pos ⟨by omega, h4⟩]
    simp only [pyHP, show d.length ≥ 65536 by omega, if_true]
    rfl
  · unfold pySaveBytesData
    have hpk : packU32 d.length = .error (structError "'I' format requires 0 <= number <= 4294967295") := by
      unfold packU32; rw [if_neg (by omega)]
    rw [if_neg (by omega), if_neg (by omega), if_pos (by simp only [frameSizeTarget]; omega), hpk]
    rfl

/-- The size classes of `write_unicode_binary` and the binary branch of `save_str`, on the
UTF-8 data, protocol 1 and up: `SHORT_BINUNICODE` to 255 bytes from protocol 4, `BINUNICODE`
with a 4-byte length below `2**32`, `BINUNICODE8` from protocol 4, an error below protocol 4. -/
def StrClasses (hp : Bytes → Bytes → List Event) (m : Nat → Bytes → EncM Unit) : Prop :=
  ∀ (p : Nat) (d : Bytes) (s : EncSt), 1 ≤ p →
    (d.length ≤ 0xff → 4 ≤ p → ∃ f, f.length = 1 ∧ leNat f = d.length ∧
      m p d s = .ok ((), After s (hp (oSHORT_BINUNICODE :: f) d))) ∧
    (d.length < 2 ^ 32 → (0xff < d.length ∨ p < 4) → ∃ f, f.length = 4 ∧ leNat f = d.length ∧
      m p d s = .ok ((), After s (hp (oBINUNICODE :: f) d))) ∧
    (2 ^ 32 ≤ d.length → d.length < 2 ^ 64 → 4 ≤ p → ∃ f, f.length = 8 ∧ leNat f = d.length ∧
      m p d s = .ok ((), After s (hp (oBINUNICODE8 :: f) d))) ∧
    (2 ^ 32 ≤ d.length → p < 4 → ∃ e, m p d s = .error e)

theorem cStrClasses : StrClasses cHP cStrData := by
  intro p d s hp1
  refine ⟨fun h h4 => ⟨leBytes d.length 1, leBytes_length _ _, leNat_le1 (by omega), ?_⟩, fun h2 h3 => ⟨leBytes d.length 4, leBytes_length _ _, leNat_le4 h2, ?_⟩,
    fun h1 h2 h4 => ⟨leBytes d.length 8, leBytes_length _ _, leNat_le8 h2, ?_⟩, fun h1 h3 => ⟨.overflowError "serializing a string larger than 4 GiB requires pickle protocol 4 or higher", ?_⟩⟩
  · unfold cStrData cWriteBytes
    rw [if_pos ⟨h, h4⟩]
    simp only [pure_bind, frameSizeTarget, cHP, show ¬ d.length ≥ 65536 by omega, ↓reduceIte]
    rfl
  · unfold cStrData cWriteBytes
    rw [if_neg (by omega), if_pos (show d.length ≤ 0xffffffff by omega)]
    unfold cHP frameSizeTarget
    split <;> rfl
  · unfold cStrData cWriteBytes
    rw [if_neg (by omega), if_neg (show ¬ d.length ≤ 0xffffffff by omega), if_pos h4,
]
    simp only [pure_bind, frameSizeTarget, cHP, show d.length ≥ 65536 by omega, ↓reduceIte]
    rfl
  · unfold cStrData
    rw [if_neg (by omega), if_neg (show ¬ d.length ≤ 0xffffffff by omega), if_neg (by omega)]
    rfl

theorem pyStrClasses (b : Nat) (hb : 2 ≤ b) : StrClasses pyHP (fun p d => pyStrDataR b p d) := by
  intro p d s hp1
  simp only
  rw [ex_strData hb]
  refine ⟨fun h h4 => ⟨leBytes d.length 1, leBytes_length _ _, leNat_le1 (by omega), ?_⟩, fun h2 h3 => ⟨leBytes d.length 4, leBytes_length _ _, leNat_le4 h2, ?_⟩,
    fun h1 h2 h4 => ⟨leBytes d.length 8, leBytes_length _ _, leNat_le8 h2, ?_⟩, fun h1 h3 => ⟨structError "'I' format requires 0 <= number <= 4294967295", ?_⟩⟩
  · unfold pyStrData
    rw [if_pos ⟨h, h4⟩]
    simp only [pyHP, show ¬ d.length ≥ 65536 by omega, ↓reduceIte]
    rfl
  · unfold pyStrData
    rw [if_neg (by omega), if_neg (by omega)]
    have hpk : packU32 d.length = .ok (leBytes d.length 4) := by unfold packU32; rw [if_pos (by omega)]
    rw [hpk]
    unfold pyHP frameSizeTarget
    split <;> rfl
  · unfold pyStrData
    rw [if_neg (by omega), if_pos ⟨by omega, h4⟩]
    simp only [pyHP, show d.length ≥ 65536 by omega, if_true]
    rfl
  · unfold pyStrData
    have hpk : packU32 d.length = .error (structError "'I' format requires 0 <= number <= 4294967295") := by
      unfold packU32; rw [if_neg (by omega)]
    rw [if_neg (by omega), if_neg (by omega), if_pos (by simp only [frameSizeTarget]; omega), hpk]
    rfl

/-- `save_unicode`/`save_str` before the memo, protocol 0: `UNICODE`, the raw-unicode-escape
text, a newline; C writes them separately (`Modules/_pickle.c:2986-2994`), Python in one
`write` after its five `replace`s, and the two texts are equal (`rue_eq_c`). -/
theorem strBody0 (b : Nat) (hb : 2 ≤ b) (st : List Nat) (s : EncSt) :
    cStrBody 0 st s = .ok ((), After s [.w [nl], .w (cRawUnicodeEscape st), .w [oUNICODE]]) ∧
    pyStrBodyR b 0 st s = .ok ((), After s [.w (oUNICODE :: cRawUnicodeEscape st ++ [nl])]) := by
  refine ⟨rfl, ?_⟩
  rw [ex_strBody hb]
  unfold pyStrBody
  rw [if_neg (by omega), rue_eq_c]
  rfl

/-- `_save_bytearray_data` and `_save_bytearray_no_memo` (protocol 5): `BYTEARRAY8` with an
8-byte length that reads back as the size. -/
theorem bytearrayData (b p : Nat) (hb : 2 ≤ b) (d : Bytes) (s : EncSt) (hl : d.length < 2 ^ 64) :
    ∃ f, f.length = 8 ∧ leNat f = d.length ∧
      cWriteBytes (oBYTEARRAY8 :: leBytes d.length 8) d s = .ok ((), After s (cHP (oBYTEARRAY8 :: f) d)) ∧
      pySaveBytearrayDataR b p d s = .ok ((), After s (pyHP (oBYTEARRAY8 :: f) d)) := by
  refine ⟨leBytes d.length 8, leBytes_length _ _, leNat_le8 hl, ?_, ?_⟩
  · unfold cWriteBytes cHP frameSizeTarget
    split <;> rfl
  · rw [ex_bytearrayData hb]
    unfold pySaveBytearrayData pyHP frameSizeTarget
    split <;> rfl

/-! ## Frames -/

/-- The C framer ends where Python's does on every call sequence between `start` and `finish`
(the invariant `FR` of `EncFrame.lean`). -/
theorem cFrame_py (l : List Event) (hl : ∀ e ∈ l, Clean e) :
    cFrame (.start :: l ++ [.finish]) = pyFrame (.start :: l ++ [.finish]) := by
  unfold cFrame pyFrame
  simp only [List.cons_append, List.foldl_cons, List.foldl_append, List.foldl_nil]
  exact (FR_finish _ _ (FR_fold l hl _ _ (by simp [FR, PyFramer.step, CFramer.step]))).symm

/-- Both framers on `start`, one write, `finish` (`_Pickler_Write`'s 9-byte placeholder filled by
`_Pickler_CommitFrame`; `_Framer.start_framing`, `write`, `end_framing`/`commit_frame`): `FRAME`
with an 8-byte length that reads back as the size when the frame holds at least 4 bytes, the
bare bytes otherwise; and at an opcode boundary a frame of at least 64 KiB is committed and a new
one opened, a smaller one is not. -/
def FramesExact : Prop :=
  ∀ (d e : Bytes), d.length < 2 ^ 64 →
    (4 ≤ d.length → ∃ f, f.length = 8 ∧ leNat f = d.length ∧
      cFrame [.start, .w d, .finish] = oFRAME :: f ++ d ∧ pyFrame [.start, .w d, .finish] = oFRAME :: f ++ d) ∧
    (d.length < 4 → cFrame [.start, .w d, .finish] = d ∧ pyFrame [.start, .w d, .finish] = d) ∧
    (65536 ≤ d.length → 4 ≤ e.length → e.length < 2 ^ 64 →
      cFrame [.start, .w d, .boundary, .w e, .finish] = oFRAME :: leBytes d.length 8 ++ d ++ (oFRAME :: leBytes e.length 8 ++ e) ∧
      pyFrame [.start, .w d, .boundary, .w e, .finish] = oFRAME :: leBytes d.length 8 ++ d ++ (oFRAME :: leBytes e.length 8 ++ e)) ∧
    (4 ≤ d.length → d.length + e.length < 65536 →
      cFrame [.start, .w d, .boundary, .w e, .finish] = oFRAME :: leBytes (d ++ e).length 8 ++ (d ++ e) ∧
      pyFrame [.start, .w d, .boundary, .w e, .finish] = oFRAME :: leBytes (d ++ e).length 8 ++ (d ++ e))

theorem framesExact_proven : FramesExact := by
  intro d e hd
  have hph : ∀ x : Bytes, (ph ++ x).length - 0 - frameHeaderSize = x.length := by
    intro x; simp [ph_length, frameHeaderSize]
  refine ⟨fun h4 => ⟨leBytes d.length 8, leBytes_length _ _, leNat_le8 hd, ?_, ?_⟩, fun h4 => ⟨?_, ?_⟩,
    fun h6 he4 he => ⟨?_, ?_⟩, fun h4 hs => ⟨?_, ?_⟩⟩
  · simp [cFrame, CFramer.step, CFramer.write, CFramer.commit, frameHeaderSize, frameSizeMin,
      show 4 ≤ d.length from h4]
  · simp [pyFrame, PyFramer.step, pyCommit, frameSizeMin, show 4 ≤ d.length from h4,
      show 0 < d.length by omega]
  · simp [cFrame, CFramer.step, CFramer.write, CFramer.commit, frameHeaderSize, frameSizeMin,
      show ¬ 4 ≤ d.length by omega]
  · simp only [pyFrame, PyFramer.step, List.foldl, List.nil_append]
    by_cases h0 : d.length > 0
    · simp [h0, pyCommit, frameSizeMin, show ¬ 4 ≤ d.length by omega]
    · have : d = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; simp
  · rw [show ([.start, .w d, .boundary, .w e, .finish] : List Event) =
        .start :: [.w d, .boundary, .w e] ++ [.finish] from rfl,
      cFrame_py _ (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                      rcases hx with rfl | rfl | rfl <;> trivial)]
    simp [pyFrame, PyFramer.step, pyCommit, frameSizeMin, frameSizeTarget, show 65536 ≤ d.length from h6,
      show 4 ≤ d.length by omega, he4, show 0 < e.length by omega]
  · simp [pyFrame, PyFramer.step, pyCommit, frameSizeMin, frameSizeTarget, show 65536 ≤ d.length from h6,
      show 4 ≤ d.length by omega, he4, show 0 < e.length by omega]
  · simp [cFrame, CFramer.step, CFramer.write, CFramer.commit, frameHeaderSize, frameSizeMin,
      frameSizeTarget, show ¬ 65536 ≤ d.length by omega, show 4 ≤ d.length + e.length by omega, ph_length]
  · simp [pyFrame, PyFramer.step, pyCommit, frameSizeMin, frameSizeTarget, show ¬ 65536 ≤ d.length by omega,
      show 4 ≤ d.length + e.length by omega, show 0 < d.length + e.length by omega]

end PyLean.Pickle

namespace PyLean.Pickle

/-- Both twins' `bytes` savers, every size class. -/
def BytesClassesBoth : Prop :=
  BytesClasses cHP cSaveBytesData ∧ ∀ b, 2 ≤ b → BytesClasses pyHP (fun p d => pySaveBytesDataR b p d)

theorem bytesClassesBoth_proven : BytesClassesBoth := ⟨cBytesClasses, pyBytesClasses⟩

/-- Both twins' `str` savers before the memo: every size class of the binary branch, and the
protocol 0 text line. -/
def StrClassesBoth : Prop :=
  StrClasses cHP cStrData ∧ (∀ b, 2 ≤ b → StrClasses pyHP (fun p d => pyStrDataR b p d)) ∧
  ∀ (b : Nat) (st : List Nat) (s : EncSt), 2 ≤ b →
    cStrBody 0 st s = .ok ((), After s [.w [nl], .w (cRawUnicodeEscape st), .w [oUNICODE]]) ∧
    pyStrBodyR b 0 st s = .ok ((), After s [.w (oUNICODE :: cRawUnicodeEscape st ++ [nl])])

theorem strClassesBoth_proven : StrClassesBoth :=
  ⟨cStrClasses, pyStrClasses, fun b st s hb => strBody0 b hb st s⟩

/-- Both twins' `bytearray` savers at protocol 5. -/
def BytearrayExact : Prop :=
  ∀ (b p : Nat) (d : Bytes) (s : EncSt), 2 ≤ b → d.length < 2 ^ 64 →
    ∃ f, f.length = 8 ∧ leNat f = d.length ∧
      cWriteBytes (oBYTEARRAY8 :: leBytes d.length 8) d s = .ok ((), After s (cHP (oBYTEARRAY8 :: f) d)) ∧
      pySaveBytearrayDataR b p d s = .ok ((), After s (pyHP (oBYTEARRAY8 :: f) d))

theorem bytearrayExact_proven : BytearrayExact := fun b p d s hb hl => bytearrayData b p hb d s hl

end PyLean.Pickle
