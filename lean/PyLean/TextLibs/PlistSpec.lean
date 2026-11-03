import PyLean.TextLibs.PlistRefute

/-! What each reader function does on every input, refusals included: `_read`, `_read_ints`,
`_get_size`, the tokens of `_read_object`, `load`'s detection, `loads`' `str` branch and the
exception class. -/

namespace PyLean.TextLibs.Plist

open PyLean PyLean.TextLibs

/-- `raise InvalidFileException()` raises an exception whose message is `'Invalid file'` and which
is a `ValueError` (so `parse` itself catches it, :508-510); with no frame left the instantiation
raises `RecursionError` instead. -/
def InvalidFileSpec : Prop :=
  (∀ r, 1 ≤ r → (raiseInvalid r : Py Unit) = .error invalidFile) ∧
  invalidFile.className = "InvalidFileException" ∧ invalidFile.message = "Invalid file" ∧
  isInst invalidFile "ValueError" = true ∧ isInst invalidFile "Exception" = true ∧
  parseCatches invalidFile = true ∧ (raiseInvalid 0 : Py Unit) = .error recErr

theorem invalidFileSpec_proven : InvalidFileSpec := by
  refine ⟨fun r hr => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨r, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
  rfl

/-! ## `_read` -/

theorem read_gen (B : List Nat) (p k : Nat) :
    FP.read ⟨B, p⟩ k = ((B.drop p).take k, ⟨B, p + ((B.drop p).take k).length⟩) := by
  simp [FP.read]

theorem readLoop_short (r : Nat) (hr : 1 ≤ r) (B : List Nat) (p size : Nat) (hshort : B.length - p < size) :
    ∀ fuel cursize q, q = p + ((B.drop p).take cursize).length → cursize ≤ size →
      (cursize = 0 → size = 0) → size - cursize < fuel →
      readLoop r size fuel ⟨B, q⟩ cursize ((B.drop p).take cursize) = .error invalidFile
  | 0, _, _, _, _, _, hf => by omega
  | fuel + 1, cursize, q, hq, h1, h0, hf => by
    unfold readLoop
    have hl : ((B.drop p).take cursize).length = min cursize (B.length - p) := by simp
    by_cases hne : ((B.drop p).take cursize).length ≠ cursize
    · rw [if_pos hne]
      obtain ⟨r, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
      rfl
    · rw [if_neg hne]
      rw [if_neg (by omega)]
      have hpos : 0 < cursize := by
        rcases Nat.eq_zero_or_pos cursize with h | h
        · have := h0 h; omega
        · exact h
      simp only
      rw [read_gen]
      simp only
      have hq' : q = p + cursize := by omega
      rw [hq', show B.drop (p + cursize) = (B.drop p).drop cursize by rw [List.drop_drop],
        ← List.take_add]
      exact readLoop_short r hr B p size hshort fuel _ _ (by simp; omega) (by omega) (by omega) (by omega)

/-- `_read(size)` returns the next `size` bytes when there are that many, and otherwise raises
`InvalidFileException` (:526-527), whatever the chunking. -/
def ReadSpec : Prop :=
  ∀ (r : Nat) (B : List Nat) (p size : Nat), 2 ≤ r →
    readR r ⟨B, p⟩ size = if size ≤ B.length - p then .ok ((B.drop p).take size, ⟨B, p + size⟩)
      else .error invalidFile

theorem readSpec_proven : ReadSpec := by
  intro r B p size hr
  split
  · rename_i h
    have hd : B.drop p = (B.drop p).take size ++ (B.drop p).drop size := (List.take_append_drop _ _).symm
    have := readR_prefix r hr B p _ _ hd
    rw [List.length_take, Nat.min_eq_left (by simp; omega)] at this
    exact this
  · rename_i h
    obtain ⟨r, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
    simp only [readR, call]
    have hm : min size minReadBuf ≤ size := Nat.min_le_left _ _
    have hrd : FP.read ⟨B, p⟩ (min size minReadBuf) =
        ((B.drop p).take (min size minReadBuf), ⟨B, p + ((B.drop p).take (min size minReadBuf)).length⟩) := by
      simp [FP.read]
    rw [hrd]
    exact readLoop_short r (by omega) B p size (by omega) _ _ _ rfl hm
      (by intro hz; have : minReadBuf = 2 ^ 20 := rfl; omega) (by omega)

/-! ## `_read_ints` -/

/-- `_read_ints(n, size)` reads `size * n` bytes and splits them into `n` big-endian integers of
`size` bytes, for every size (struct for 1, 2, 4, 8; `int.from_bytes` for 3, 5, 6, 7 and above 8);
size 0 raises `InvalidFileException` (:539-540), and so does a short read. -/
def ReadIntsSpec : Prop :=
  ∀ (r : Nat) (B : List Nat) (p n size : Nat), 3 ≤ r →
    readIntsR r ⟨B, p⟩ n size =
      if size * n ≤ B.length - p then
        (if size = 0 then .error invalidFile
         else .ok ((chunks size n ((B.drop p).take (size * n))).map beVal, ⟨B, p + size * n⟩))
      else .error invalidFile

theorem readIntsSpec_proven : ReadIntsSpec := by
  intro r B p n size hr
  obtain ⟨r, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
  simp only [readIntsR, call]
  rw [readSpec_proven (r + 1) B p (size * n) (by omega)]
  by_cases hs : size * n ≤ B.length - p
  · simp only [hs, ↓reduceIte, bind, Except.bind]
    by_cases h0 : size = 0
    · subst h0; simp [binaryFormat, raiseInvalid, call]
    · by_cases hb : binaryFormat size = true
      · simp [hb, h0]
      · simp [hb, h0, call]
  · simp [hs, bind, Except.bind]

/-! ## `_get_size` -/

/-- `_get_size(tokenL)`: a low nibble other than 0xF is the size; 0xF reads a marker byte
(`IndexError` at the end of the file, :515), keeps its low two bits (`& 0x3`), and reads a
big-endian size of 1, 2, 4 or 8 bytes (`struct.error` when fewer are left, :518). -/
def GetSizeSpec : Prop :=
  ∀ (r : Nat) (B : List Nat) (p t : Nat), 1 ≤ r →
    getSizeR r ⟨B, p⟩ t =
      if t ≠ 15 then .ok (t, ⟨B, p⟩)
      else match B[p]? with
        | none => .error (.indexError "index out of range")
        | some m =>
          if 2 ^ (m &&& 3) ≤ B.length - (p + 1) then
            .ok (beVal ((B.drop (p + 1)).take (2 ^ (m &&& 3))), ⟨B, p + 1 + 2 ^ (m &&& 3)⟩)
          else .error (structErr s!"unpack requires a buffer of {2 ^ (m &&& 3)} bytes")

theorem getSizeSpec_proven : GetSizeSpec := by
  intro r B p t hr
  obtain ⟨r, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
  simp only [getSizeR, call]
  by_cases ht : t = 15
  · subst ht
    simp only [↓reduceIte, ne_eq, not_true_eq_false]
    cases hp : B[p]? with
    | none =>
      have : B.length ≤ p := by
        rcases Nat.lt_or_ge p B.length with h | h
        · rw [List.getElem?_eq_getElem h] at hp; cases hp
        · exact h
      simp [FP.read, List.drop_eq_nil_of_le this]
    | some m =>
      have hlt := lt_of_getElem?_some hp
      have hd : B.drop p = m :: B.drop (p + 1) := by
        rw [List.drop_eq_getElem_cons hlt]
        rw [List.getElem?_eq_getElem hlt] at hp; cases hp; rfl
      rw [read_one B p m _ hd]
      simp only
      rw [read_gen B (p + 1) (2 ^ (m &&& 3))]
      by_cases h : 2 ^ (m &&& 3) ≤ B.length - (p + 1)
      · have hl : ((B.drop (p + 1)).take (2 ^ (m &&& 3))).length = 2 ^ (m &&& 3) := by simp; omega
        simp only [hl, ne_eq, not_true_eq_false, ↓reduceIte, h]
      · have hl : ((B.drop (p + 1)).take (2 ^ (m &&& 3))).length ≠ 2 ^ (m &&& 3) := by simp; omega
        simp only [hl, ne_eq, not_false_eq_true, ↓reduceIte, h]
  · simp [ht]

/-! ## The tokens of `_read_object` -/

/-- Every leaf token of `_read_object` (:562-613) and every unknown one, after the token byte at
position `p`: None, False, True, `b''` (0x0f), an int of `1 << L` bytes (signed from L = 3, and
silently shorter at the end of the file), a float32 through `PyFloat_Unpack4` (0x22) and a float64
(0x23) with `struct.error` when short, a date (0x33: `timedelta(seconds=f)` added to 2001-01-01),
a UID of `1 + L` bytes (through `UID.__init__`), and `InvalidFileException` for every other
token. -/
def ReadTokenSpec : Prop :=
  ∀ (cfg : PCfg) (r : Nat) (rd : Nat → PState → Py PState) (ref : Nat) (st : PState) (B : List Nat)
    (p t : Nat), 1 ≤ r →
    let leaf := fun (o : Obj) (q : Nat) => (.ok (({ fp := ⟨B, q⟩, objs := st.objs } : PState).put ref o) : Py PState)
    let avail := B.length - p
    (t = 0x00 → readToken cfg r rd ref st t ⟨B, p⟩ = leaf .none p) ∧
    (t = 0x08 → readToken cfg r rd ref st t ⟨B, p⟩ = leaf (.bool false) p) ∧
    (t = 0x09 → readToken cfg r rd ref st t ⟨B, p⟩ = leaf (.bool true) p) ∧
    (t = 0x0f → readToken cfg r rd ref st t ⟨B, p⟩ = leaf (.data []) p) ∧
    (∀ L, L < 16 → t = 0x10 + L → readToken cfg r rd ref st t ⟨B, p⟩ =
      leaf (.int (fromBytes ((B.drop p).take (2 ^ L)) (decide (L ≥ 3)))) (p + min (2 ^ L) avail)) ∧
    (t = 0x22 → readToken cfg r rd ref st t ⟨B, p⟩ =
      if 4 ≤ avail then leaf (.real (Struct.pyFloatUnpack4Bits (beVal ((B.drop p).take 4)))) (p + 4)
      else .error (structErr "unpack requires a buffer of 4 bytes")) ∧
    (t = 0x23 → readToken cfg r rd ref st t ⟨B, p⟩ =
      if 8 ≤ avail then leaf (.real (beVal ((B.drop p).take 8))) (p + 8)
      else .error (structErr "unpack requires a buffer of 8 bytes")) ∧
    (t = 0x33 → readToken cfg r rd ref st t ⟨B, p⟩ =
      if 8 ≤ avail then
        (do let td ← deltaFromSeconds (Binary64.F64.ofBits (beVal ((B.drop p).take 8)))
            let us ← epochPlus td
            leaf (.date us cfg.aware) (p + 8))
      else .error (structErr "unpack requires a buffer of 8 bytes")) ∧
    (∀ L, L < 16 → t = 0x80 + L → readToken cfg r rd ref st t ⟨B, p⟩ =
      (do let d ← uidR r (beVal ((B.drop p).take (1 + L)))
          leaf (.uid d) (p + min (1 + L) avail))) ∧
    (t ≠ 0x00 → t ≠ 0x08 → t ≠ 0x09 → t ≠ 0x0f → t ≠ 0x22 → t ≠ 0x23 → t ≠ 0x33 →
      t &&& 0xF0 ≠ 0x10 → t &&& 0xF0 ≠ 0x40 → t &&& 0xF0 ≠ 0x50 → t &&& 0xF0 ≠ 0x60 →
      t &&& 0xF0 ≠ 0x80 → t &&& 0xF0 ≠ 0xA0 → t &&& 0xF0 ≠ 0xD0 →
      readToken cfg r rd ref st t ⟨B, p⟩ = raiseInvalid r)

theorem take_min_len (l : List Nat) (k : Nat) : l.take (min k l.length) = l.take k := by
  rcases Nat.le_total k l.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.take_of_length_le (Nat.le_refl _), List.take_of_length_le h]

theorem nib_or : ∀ L, L < 16 → (0x10 + L) &&& 0xF0 = 0x10 ∧ (0x10 + L) &&& 0x0F = L ∧
    (0x80 + L) &&& 0xF0 = 0x80 ∧ (0x80 + L) &&& 0x0F = L := by decide

theorem readTokenSpec_proven : ReadTokenSpec := by
  intro cfg r rd ref st B p t hr
  simp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro rfl; simp [readToken]
  · rintro rfl; simp [readToken]
  · rintro rfl; simp [readToken]
  · rintro rfl; simp [readToken]
  · intro L hL ht; subst ht
    have hn := nib_or L hL
    have h1 : 0x10 + L ≠ 0 ∧ 0x10 + L ≠ 8 ∧ 0x10 + L ≠ 9 ∧ 0x10 + L ≠ 15 := by omega
    simp only [readToken, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, hn.1, hn.2.1, ↓reduceIte]
    have := take_min_len (B.drop p) (2 ^ L)
    simp only [List.length_drop] at this
    simp [FP.read]
    rw [this]
  · rintro rfl
    simp only [readToken]
    rw [read_gen B p 4]
    by_cases h : 4 ≤ B.length - p
    · have hl : ((B.drop p).take 4).length = 4 := by simp; omega
      simp [hl, h, unpackReal, bind, Except.bind]
    · have hl : ((B.drop p).take 4).length ≠ 4 := by simp; omega
      have hm : ¬ (min 4 (B.length - p) = 4) := by omega
      simp [hm, h, unpackReal, bind, Except.bind]
      rfl
  · rintro rfl
    simp only [readToken]
    rw [read_gen B p 8]
    by_cases h : 8 ≤ B.length - p
    · have hl : ((B.drop p).take 8).length = 8 := by simp; omega
      simp [hl, h, unpackReal, bind, Except.bind]
    · have hl : ((B.drop p).take 8).length ≠ 8 := by simp; omega
      have hm : ¬ (min 8 (B.length - p) = 8) := by omega
      simp [hm, h, unpackReal, bind, Except.bind]
      rfl
  · rintro rfl
    simp only [readToken]
    rw [read_gen B p 8]
    by_cases h : 8 ≤ B.length - p
    · have hl : ((B.drop p).take 8).length = 8 := by simp; omega
      simp [hl, h, unpackReal, bind, Except.bind]
    · have hl : ((B.drop p).take 8).length ≠ 8 := by simp; omega
      have hm : ¬ (min 8 (B.length - p) = 8) := by omega
      simp [hm, h, unpackReal, bind, Except.bind]
      rfl
  · intro L hL ht; subst ht
    have hn := nib_or L hL
    have h1 : 0x80 + L ≠ 0 ∧ 0x80 + L ≠ 8 ∧ 0x80 + L ≠ 9 ∧ 0x80 + L ≠ 15 ∧ 0x80 + L ≠ 0x22 ∧
        0x80 + L ≠ 0x23 ∧ 0x80 + L ≠ 0x33 := by omega
    simp only [readToken, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1,
      h1.2.2.2.2.2.2, hn.2.2.1, hn.2.2.2, ↓reduceIte]
    rw [read_gen B p (1 + L)]
    simp
  · intro h0 h8 h9 h15 h22 h23 h33 hA hB hC hD hE hF hG
    simp only [readToken, h0, h8, h9, h15, h22, h23, h33, hA, hB, hC, hD, hE, hF, hG, ↓reduceIte]

/-! ## `load` and `loads` -/

/-- `load` with `fmt=None` refuses a header that is neither XML nor `bplist00` (:906-907), and
`_FORMATS[fmt]` raises `KeyError(fmt)` for any other format object (:910). -/
def LoadDispatchSpec : Prop :=
  (∀ (xml : XmlParse) (r : Nat) (buf : List Nat) (aware : Bool), 3 ≤ r →
    isFmtXml (buf.take 32) = false → isFmtBinary (buf.take 32) = false →
    loadsR xml r (.bytes buf) .none aware = .error invalidFile) ∧
  (∀ (xml : XmlParse) (r : Nat) (buf : List Nat) (aware : Bool) (rp : String), 2 ≤ r →
    loadsR xml r (.bytes buf) (.other rp) aware = .error (.keyError rp)) ∧
  (∀ (xml : XmlParse) (r : Nat) (buf : List Nat) (aware : Bool), 3 ≤ r →
    isFmtXml (buf.take 32) = true → loadsR xml r (.bytes buf) .none aware = xml (r - 2) aware buf)

theorem loadDispatchSpec_proven : LoadDispatchSpec := by
  refine ⟨?_, ?_, ?_⟩
  · intro xml r buf aware hr hx hb
    obtain ⟨r, rfl⟩ : ∃ j, r = j + 3 := ⟨r - 3, by omega⟩
    simp [loadsR, loadR, call, bind, Except.bind, header_take, hx, hb, raiseInvalid]
  · intro xml r buf aware rp hr
    obtain ⟨r, rfl⟩ : ∃ j, r = j + 2 := ⟨r - 2, by omega⟩
    simp [loadsR, loadR, call, bind, Except.bind]
  · intro xml r buf aware hr hx
    obtain ⟨r, rfl⟩ : ∃ j, r = j + 3 := ⟨r - 3, by omega⟩
    simp [loadsR, loadR, call, bind, Except.bind, header_take, hx]

/-- `loads(s)` for a `str`: with `fmt=FMT_BINARY` a `TypeError` (:921-923); otherwise the UTF-8
encoding of `s` is loaded (:924), and a lone surrogate's `UnicodeEncodeError` propagates. -/
def LoadsStrSpec : Prop :=
  ∀ (xml : XmlParse) (r : Nat) (s : List Nat) (fmt : Fmt) (aware : Bool), 1 ≤ r →
    loadsR xml r (.str s) fmt aware =
      if fmt = .binary then .error (.typeError "value must be bytes-like object when fmt is FMT_BINARY")
      else match UnicodeObj.utf8Encode s .strict with
        | .ok b => loadR xml (r - 1) b fmt aware
        | .error e => .error e

theorem loadsStrSpec_proven : LoadsStrSpec := by
  intro xml r s fmt aware hr
  obtain ⟨r, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
  simp only [loadsR, call, bind, Except.bind]
  split
  · rfl
  · split <;> rename_i h <;> rw [h] <;> rfl

end PyLean.TextLibs.Plist
