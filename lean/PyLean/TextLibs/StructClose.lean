import PyLean.TextLibs.StructRound

/-!
The rest of `Modules/_struct.c`: `prepare_s`, the float and complex routines through
byte-order twin laws, the character and bool codes, and the accessors.
-/

namespace PyLean.TextLibs.Struct

open PyLean PyLean.TextLibs

set_option linter.unusedSimpArgs false

/-! ### `prepare_s`: the two passes agree -/

def sumRepeat (cs : List Code) : Nat := (cs.map (·.repeat_)).sum

theorem sumRepeat_append (cs : List Code) (c : Code) :
    sumRepeat (cs ++ [c]) = sumRepeat cs + c.repeat_ := by
  simp [sumRepeat, List.sum_append]

theorem scan_agree : ∀ (s : List Char) (n num : Nat) (c : Char) (r : List Char),
    scanDigits1 n s = some (num, some c, r) → scanDigits2 n s = (num, some c, r) := by
  intro s
  induction s with
  | nil => intro _ _ _ _ h; simp [scanDigits1] at h
  | cons x xs ih =>
    intro n num c r h
    unfold scanDigits1 at h
    unfold scanDigits2
    by_cases hd : isDigit x = true
    · simp only [hd, if_true] at h ⊢
      split at h
      · simp at h
      · exact ih _ _ _ _ h
    · simp only [hd, Bool.false_eq_true, if_false] at h ⊢
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl

theorem getentry_mem {c : Char} : ∀ {tbl : List FormatDef} {e : FormatDef},
    getentry c tbl = .ok e → e ∈ tbl ∧ e.format = c := by
  intro tbl
  induction tbl with
  | nil => intro e h; cases h
  | cons f fs ih =>
    intro e h
    unfold getentry at h
    split at h
    · cases h
      exact ⟨by simp, by assumption⟩
    · obtain ⟨h1, h2⟩ := ih h
      exact ⟨by simp [h1], h2⟩

/-- `s`, `p` and `x` are one byte in every table, and no entry has size 0. -/
theorem table_sizes : ∀ t : Tab, ∀ e ∈ t.table,
    e.size ≠ 0 ∧ ((e.format = 's' ∨ e.format = 'p' ∨ e.format = 'x') → e.size = 1) := by
  intro t
  cases t <;> decide +kernel

/-- Agreement between a pass-1 state and a pass-2 accumulator. -/
def Inv (st : Pass1) (acc : List Code × Nat) : Prop :=
  acc.2 = st.size ∧ sumRepeat acc.1 = st.len ∧ acc.1.length = st.ncodes

theorem item_agree (t : Tab) (st st' : Pass1) (num : Nat) (c : Char) (acc : List Code × Nat)
    (h : pass1Item t.table st num c = .ok st') (hi : Inv st acc) :
    Inv st' (pass2Item t.table acc num c) := by
  obtain ⟨codes, size⟩ := acc
  obtain ⟨hs, hl, hn⟩ := hi
  simp only at hs hl hn
  subst hs
  unfold pass1Item at h
  unfold pass2Item
  cases hg : getentry c t.table with
  | error e' => simp [hg, bind, Except.bind] at h
  | ok e =>
    obtain ⟨hm, hf⟩ := getentry_mem hg
    obtain ⟨_, hsz⟩ := table_sizes t e hm
    simp only [hg, bind, Except.bind] at h
    simp only [hg]
    by_cases hsp : c = 's' ∨ c = 'p'
    · have h1 : e.size = 1 := hsz (by rw [hf]; rcases hsp with h | h <;> simp [h])
      rw [if_pos hsp] at h
      split at h
      · cases h
      · simp only [pure, Except.pure] at h
        cases ha : align st.size e with
        | none => rw [ha] at h; cases h
        | some sz =>
          rw [ha] at h
          simp only at h
          split at h
          · cases h
          · cases h
            simp only [ha, Option.getD_some, if_pos hsp, h1, Nat.mul_one]
            refine ⟨rfl, ?_, ?_⟩
            · simp only [sumRepeat_append, hl]
            · simp [hn]
    · rw [if_neg hsp] at h
      by_cases hx : c = 'x'
      · have h1 : e.size = 1 := hsz (by rw [hf, hx]; simp)
        rw [if_pos hx] at h
        simp only [pure, Except.pure] at h
        cases ha : align st.size e with
        | none => rw [ha] at h; cases h
        | some sz =>
          rw [ha] at h
          simp only at h
          split at h
          · cases h
          · cases h
            simp only [ha, Option.getD_some, if_neg hsp, if_pos hx, h1, Nat.mul_one]
            exact ⟨rfl, hl, hn⟩
      · rw [if_neg hx] at h
        split at h
        · cases h
        · simp only [pure, Except.pure] at h
          cases ha : align st.size e with
          | none => rw [ha] at h; cases h
          | some sz =>
            rw [ha] at h
            simp only at h
            split at h
            · cases h
            · cases h
              simp only [ha, Option.getD_some, if_neg hsp, if_neg hx]
              by_cases hnum : num = 0
              · subst hnum
                simp [Inv, hl, hn]
              · simp only [if_pos hnum]
                refine ⟨by show sz + e.size * num = sz + num * e.size; rw [Nat.mul_comm], ?_, ?_⟩
                · simp only [sumRepeat_append, hl]
                · simp [hn]

theorem pass_agree (t : Tab) : ∀ (fuel : Nat) (s : List Char) (st st' : Pass1) (acc : List Code × Nat),
    pass1 t.table fuel s st = .ok st' → Inv st acc → Inv st' (pass2 t.table fuel s acc) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ h; cases h
  | succ fuel ih =>
    intro s st st' acc h hi
    match s with
    | [] =>
      simp only [pass1, pure, Except.pure] at h
      cases h
      exact hi
    | c :: s =>
      unfold pass1 at h
      unfold pass2
      by_cases hsp : isSpace c = true
      · simp only [hsp, if_true] at h ⊢
        exact ih _ _ _ _ h hi
      · simp only [hsp, Bool.false_eq_true, if_false] at h ⊢
        by_cases hd : isDigit c = true
        · simp only [hd, if_true] at h ⊢
          cases hs1 : scanDigits1 (digit c) s with
          | none => rw [hs1] at h; cases h
          | some res =>
            obtain ⟨num, c', r⟩ := res
            rw [hs1] at h
            cases c' with
            | none => cases h
            | some c' =>
              rw [scan_agree _ _ _ _ _ hs1]
              cases hit : pass1Item t.table st num c' with
              | error e => simp [hit, bind, Except.bind] at h
              | ok st2 =>
                simp only [hit, bind, Except.bind] at h
                exact ih _ _ _ _ h (item_agree t st st2 num c' acc hit hi)
        · simp only [hd, Bool.false_eq_true, if_false] at h ⊢
          cases hit : pass1Item t.table st 1 c with
          | error e => simp [hit, bind, Except.bind] at h
          | ok st2 =>
            simp only [hit, bind, Except.bind] at h
            exact ih _ _ _ _ h (item_agree t st st2 1 c acc hit hi)

/-- `prepare_s` runs two independent passes over the format: the first computes `s_size`,
`s_len` and the code count with overflow checks, the second builds the codes. For every
accepted format they agree: the object's size is the first pass's, `s_len` is the sum of the
codes' repeats (so `pack` consumes exactly `s_len` arguments), and there is one code per
counted item. -/
def PrepareSAgree : Prop :=
  ∀ (format : List Nat) (s : SObj), prepareS format = .ok s →
    ∃ st : Pass1,
      pass1 (whichtable (asciiChars format)).1.table ((whichtable (asciiChars format)).2.length + 1)
        (whichtable (asciiChars format)).2 {} = .ok st ∧
      s.sSize = st.size ∧ s.sLen = sumRepeat s.codes ∧ s.codes.length = st.ncodes ∧
      s.format = format

theorem prepareSAgree_proven : PrepareSAgree := by
  intro format s h
  unfold prepareS at h
  by_cases h0 : 0 ∈ format
  · rw [if_pos h0] at h
    cases h
  rw [if_neg h0] at h
  cases hw : whichtable (asciiChars format) with
  | mk t fmt =>
    simp only [hw] at h ⊢
    cases hp : pass1 t.table (fmt.length + 1) fmt {} with
    | error e => rw [hp] at h; cases h
    | ok st =>
      rw [hp] at h
      simp only at h
      by_cases hm : st.ncodes + 1 > maxN / 32
      · rw [if_pos hm] at h
        cases h
      rw [if_neg hm] at h
      have hi := pass_agree t _ fmt {} st ([], 0) hp ⟨rfl, rfl, rfl⟩
      cases hq : pass2 t.table (fmt.length + 1) fmt ([], 0) with
      | mk codes size =>
        rw [hq] at h hi
        obtain ⟨h1, h2, h3⟩ := hi
        cases h
        exact ⟨st, rfl, h1, h2.symm, h3, rfl⟩

/-! ### `c` and `?` -/

def charEntries : List FormatDef := [⟨'c', 1, 0, .nuChar, .npChar⟩]

/-- `c` round-trips every byte and rejects everything but a length-1 `bytes`. -/
def CharCode : Prop :=
  ∀ e ∈ charEntries, (∀ b : Nat, runPack e (.bytes [b]) = .ok [b] ∧
      runUnpack e [b] = .ok (.bytes [b])) ∧
    (∀ v : SV, (∀ b, v ≠ .bytes [b]) →
      runPack e v = .error (structErr "char format requires a bytes object of length 1"))

theorem charCode_proven : CharCode := by
  intro e he
  simp only [charEntries, List.mem_singleton] at he
  subst he
  refine ⟨fun b => ⟨rfl, rfl⟩, fun v hv => ?_⟩
  cases v with
  | bytes l =>
    match l, hv with
    | [], _ => rfl
    | [b], hv => exact absurd rfl (hv b)
    | _ :: _ :: _, _ => rfl
  | _ => rfl

/-- `?` stores the truth value of any object in one byte, and reads it back. -/
def BoolCode : Prop :=
  ∀ (v : SV) (nat std : FormatDef), nat = ⟨'?', 1, 1, .nuBool, .npBool⟩ →
    std = ⟨'?', 1, 0, .buBool, .bpBool⟩ →
    (∃ w, runPack nat v = .ok w ∧ runUnpack nat w = .ok (.bool (isTrue v))) ∧
    (∃ w, runPack std v = .ok w ∧ runUnpack std w = .ok (.bool (isTrue v)))

theorem boolCode_proven : BoolCode := by
  intro v nat std h1 h2
  subst h1 h2
  constructor <;> (refine ⟨[if isTrue v then 1 else 0], rfl, ?_⟩; cases isTrue v <;> rfl)

/-! ### Byte-order twin laws for float and complex -/

theorem leVal_eq_beVal_reverse : ∀ p : List Nat, leVal p = beVal p.reverse := by
  intro p
  induction p with
  | nil => rfl
  | cons b bs ih =>
    rw [List.reverse_cons, beVal_snoc, ← ih, leVal]
    omega

theorem ordered_rev (n v : Nat) : ordered true n v = (ordered false n v).reverse := by
  simp [ordered]

/-- Pairs of little- and big-endian entries, including the pre-swap routines and the
native ones that replace them. -/
def scalarPairs : List (FormatDef × FormatDef) :=
  [(⟨'e', 2, 0, .luHalffloat, .lpHalffloat⟩, ⟨'e', 2, 0, .buHalffloat, .bpHalffloat⟩),
   (⟨'e', 2, 0, .nuHalffloat, .npHalffloat⟩, ⟨'e', 2, 0, .buHalffloat, .bpHalffloat⟩),
   (⟨'f', 4, 0, .luFloat, .lpFloat⟩, ⟨'f', 4, 0, .buFloat, .bpFloat⟩),
   (⟨'d', 8, 0, .luDouble, .lpDouble⟩, ⟨'d', 8, 0, .buDouble, .bpDouble⟩),
   (⟨'d', 8, 8, .nuDouble, .npDouble⟩, ⟨'d', 8, 0, .buDouble, .bpDouble⟩)]

/-- For every value, the little-endian bytes are the reverse of the big-endian bytes, or both
raise the same error; and for every buffer of the right size, unpacking it little-endian equals
unpacking its reverse big-endian. -/
def ScalarByteOrder : Prop :=
  ∀ q ∈ scalarPairs,
    (∀ v : SV, runPack q.1 v = (runPack q.2 v).map List.reverse) ∧
    (∀ p : List Nat, p.length = q.1.size → runUnpack q.1 p = runUnpack q.2 p.reverse)

theorem ordered_map (x : Py Nat) (n : Nat) :
    (do return ordered true n (← x) : Py (List Nat))
      = (do return ordered false n (← x) : Py (List Nat)).map List.reverse := by
  cases x <;> simp [bind, Except.bind, pure, Except.pure, Except.map, ordered_rev]

theorem scalarByteOrder_proven : ScalarByteOrder := by
  intro q hq
  simp only [scalarPairs, List.mem_cons, List.not_mem_nil, or_false] at hq
  have hrev : ∀ (n : Nat) (p : List Nat), p.length = n →
      leVal (p.take n) = beVal (p.reverse.take n) := by
    intro n p h
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by simp; omega)]
    exact leVal_eq_beVal_reverse p
  rcases hq with rfl | rfl | rfl | rfl | rfl <;> constructor
  all_goals first
    | (intro v
       simp only [runPack, packHalffloat, packFloatStd, packDoubleStd]
       cases asDouble v with
       | none => rfl
       | some x =>
         simp only
         first
           | exact ordered_map _ _
           | simp [Except.map, ordered_rev, ordered])
    | (intro p hp
       simp only [runUnpack]
       rw [hrev _ p hp])

/-- Native `f` packs like `<f`, so its bytes are the reverse of `>f`'s for every value (native
and standard differ on unpack only). -/
def NativeFloatPack : Prop :=
  ∀ v : SV, runPack ⟨'f', 4, 4, .nuFloat, .npFloat⟩ v
    = (runPack ⟨'f', 4, 0, .buFloat, .bpFloat⟩ v).map List.reverse

theorem nativeFloatPack_proven : NativeFloatPack := by
  intro v
  simp only [runPack, packFloatStd]
  cases asDouble v with
  | none => rfl
  | some x =>
    simp only
    exact ordered_map _ _

/-! ### Complex byte order -/

/-- Reverse the two `n`-byte parts in place. -/
def swapParts (n : Nat) (w : List Nat) : List Nat := (w.take n).reverse ++ (w.drop n).reverse

theorem swapParts_ordered (n a b : Nat) :
    swapParts n (ordered false n a ++ ordered false n b) = ordered true n a ++ ordered true n b := by
  have h : (ordered false n a).length = n := by simp [ordered, leBytes_length]
  unfold swapParts
  rw [List.take_left' h, List.drop_left' h, ordered_rev, ordered_rev]

/-- `<D` and `>D`, and `<F` and `>F` through the pre-swap routines: each part is byte-reversed
and the parts stay in order, for every value and every buffer of the right size. -/
def complexPairs : List (FormatDef × FormatDef × Nat) :=
  [(⟨'D', 16, 0, .luDoubleComplex, .lpDoubleComplex⟩, ⟨'D', 16, 0, .buDoubleComplex, .bpDoubleComplex⟩, 8),
   (⟨'D', 16, 0, .nuDoubleComplex, .npDoubleComplex⟩, ⟨'D', 16, 0, .buDoubleComplex, .bpDoubleComplex⟩, 8),
   (⟨'F', 8, 0, .luFloatComplex, .lpFloatComplex⟩, ⟨'F', 8, 0, .buFloatComplex, .bpFloatComplex⟩, 4)]

def ComplexByteOrder : Prop :=
  ∀ q ∈ complexPairs,
    (∀ v : SV, runPack q.1 v = (runPack q.2.1 v).map (swapParts q.2.2)) ∧
    (∀ p : List Nat, p.length = 2 * q.2.2 → runUnpack q.1 p = runUnpack q.2.1 (swapParts q.2.2 p))

theorem part_views (n : Nat) (p : List Nat) (h : p.length = 2 * n) :
    (swapParts n p).take n = (p.take n).reverse ∧ (swapParts n p).drop n = (p.drop n).reverse ∧
      ((p.drop n).reverse).length = n ∧ (p.take n).length = n := by
  have h1 : ((p.take n).reverse).length = n := by simp; omega
  unfold swapParts
  refine ⟨List.take_left' h1, List.drop_left' h1, by simp; omega, by simp; omega⟩

theorem packFC_order (v : SV) : packFCStd v true = (packFCStd v false).map (swapParts 4) := by
  unfold packFCStd
  cases asCComplex v with
  | none => rfl
  | some ab =>
    obtain ⟨a, b⟩ := ab
    simp only
    generalize pyFloatPack4Bits a = x
    generalize pyFloatPack4Bits b = y
    cases x <;> cases y <;>
      simp [bind, Except.bind, pure, Except.pure, Except.map, swapParts_ordered]

theorem packDC_order (v : SV) : packDCStd v true = (packDCStd v false).map (swapParts 8) := by
  unfold packDCStd
  cases asCComplex v with
  | none => rfl
  | some ab =>
    obtain ⟨a, b⟩ := ab
    simp [Except.map, swapParts_ordered]

theorem packDN_order (v : SV) : runPack ⟨'D', 16, 0, .nuDoubleComplex, .npDoubleComplex⟩ v
    = (packDCStd v false).map (swapParts 8) := by
  simp only [runPack, packDCStd]
  cases asCComplex v with
  | none => rfl
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have h : leBytes 8 a ++ leBytes 8 b = ordered true 8 a ++ ordered true 8 b := by simp [ordered]
    simp only [Except.map, swapParts_ordered, h]

theorem complexByteOrder_proven : ComplexByteOrder := by
  intro q hq
  simp only [complexPairs, List.mem_cons, List.not_mem_nil, or_false] at hq
  have hle : ∀ (n : Nat) (p : List Nat), p.length = 2 * n →
      leVal ((p.drop 0).take n) = beVal (((swapParts n p).drop 0).take n) ∧
      leVal ((p.drop n).take n) = beVal (((swapParts n p).drop n).take n) := by
    intro n p h
    obtain ⟨h1, h2, h3, _⟩ := part_views n p h
    rw [List.drop_zero, List.drop_zero, h1, h2]
    constructor
    · exact leVal_eq_beVal_reverse _
    · rw [List.take_of_length_le (l := (p.drop n).reverse) (by omega),
        List.take_of_length_le (l := p.drop n) (by simp; omega)]
      exact leVal_eq_beVal_reverse _
  rcases hq with rfl | rfl | rfl
  · refine ⟨fun v => packDC_order v, fun p hp => ?_⟩
    obtain ⟨h1, h2⟩ := hle 8 p hp
    simp only [runUnpack]
    rw [h1, h2]
  · refine ⟨fun v => packDN_order v, fun p hp => ?_⟩
    obtain ⟨h1, h2⟩ := hle 8 p hp
    simp only [runUnpack]
    rw [h1, h2]
  · refine ⟨fun v => packFC_order v, fun p hp => ?_⟩
    obtain ⟨h1, h2⟩ := hle 4 p hp
    simp only [runUnpack]
    rw [h1, h2]

/-! ### Refuted: native `f` and `F` quiet a signalling NaN -/

/-- `unpack('f', b)` and `unpack('<f', b)` agree on every 4-byte buffer: on a little-endian
build, native and standard differ only in alignment. -/
def NativeFloatMatchesStd : Prop :=
  ∀ b : List Nat, b.length = 4 →
    modUnpack (.str ['f'.toNat]) b = modUnpack (.str ['<'.toNat, 'f'.toNat]) b

theorem nativeFloatMatchesStd_refuted : ¬NativeFloatMatchesStd := by
  intro h
  have := h [1, 0, 0x80, 0x7f] rfl
  revert this
  decide +kernel

/-- `unpack('F', b)` and `unpack('>F', swapped b)` agree on every 8-byte buffer. -/
def NativeComplexMatchesBig : Prop :=
  ∀ b : List Nat, b.length = 8 →
    modUnpack (.str ['F'.toNat]) b = modUnpack (.str ['>'.toNat, 'F'.toNat]) (swapParts 4 b)

theorem nativeComplexMatchesBig_refuted : ¬NativeComplexMatchesBig := by
  intro h
  have := h [1, 0, 0x80, 0x7f, 1, 0, 0x80, 0x7f] rfl
  revert this
  decide +kernel

/-! ### `unpack_from`, the iterator, the accessors -/

/-- A negative offset counts from the end of the buffer, and offset 0 on an exact-size buffer
is `unpack`. `len < 2 ** 63` is the type invariant of a Python buffer. -/
def UnpackFromOffsets : Prop :=
  ∀ (f : FmtArg) (s : SObj) (buf : List Nat), cacheStruct f = .ok s → (buf.length : Int) ≤ longMax →
    (∀ k : Nat, 0 < k → k ≤ buf.length → s.sSize ≤ k →
      modUnpackFrom f buf (-(k : Int)) = modUnpackFrom f buf ((buf.length : Int) - k)) ∧
    (buf.length = s.sSize → modUnpackFrom f buf 0 = modUnpack f buf)

theorem unpackFromOffsets_proven : UnpackFromOffsets := by
  intro f s buf hs hlen
  have hl : longMax = 9223372036854775807 := rfl
  have hm : longMin = -9223372036854775808 := rfl
  have harg : ∀ o : Int, longMin ≤ o → o ≤ longMax → ssizeArg o = .ok o := by
    intro o h1 h2
    unfold ssizeArg
    rw [if_neg (by omega)]
  constructor
  · intro k hk hle hsz
    simp only [modUnpackFrom, hs, bind, Except.bind]
    simp only [structUnpackFrom, bind, Except.bind]
    rw [harg _ (by omega) (by omega), harg _ (by omega) (by omega)]
    simp only
    rw [if_pos (by omega : -(k : Int) < 0), if_neg (by omega), if_neg (by omega),
      if_neg (by omega : ¬ ((buf.length : Int) - k < 0))]
    simp only [pure, Except.pure]
    rw [show -(k : Int) + (buf.length : Int) = (buf.length : Int) - k by omega]
  · intro he
    simp only [modUnpackFrom, modUnpack, hs, bind, Except.bind]
    simp only [structUnpackFrom, structUnpack, bind, Except.bind]
    rw [harg _ (by omega) (by omega)]
    simp only
    rw [if_neg (by omega : ¬ ((0 : Int) < 0))]
    simp only [pure, Except.pure]
    rw [if_neg (by omega), if_neg (by omega)]
    simp

theorem iterLoop_length (s : SObj) (buf : List Nat) (hs : 0 < s.sSize) :
    ∀ (fuel index : Nat) (l : List (List SV)), iterLoop s buf fuel index = .ok l →
      l.length = (buf.length - index + s.sSize - 1) / s.sSize := by
  intro fuel
  induction fuel with
  | zero => intro _ _ h; cases h
  | succ fuel ih =>
    intro index l h
    unfold iterLoop at h
    by_cases hi : index ≥ buf.length
    · rw [if_pos hi] at h
      cases h
      have : buf.length - index + s.sSize - 1 < s.sSize := by omega
      rw [Nat.div_eq_of_lt this]
      rfl
    · rw [if_neg hi] at h
      cases h1 : sUnpackInternal s (buf.drop index) with
      | error e => simp [h1, bind, Except.bind] at h
      | ok r =>
        cases h2 : iterLoop s buf fuel (index + s.sSize) with
        | error e => simp [h1, h2, bind, Except.bind] at h
        | ok rs =>
          simp only [h1, h2, bind, Except.bind, pure, Except.pure] at h
          cases h
          rw [List.length_cons, ih _ _ h2]
          by_cases hD : buf.length - index ≥ s.sSize
          · have e : buf.length - index + s.sSize - 1
                = (buf.length - (index + s.sSize) + s.sSize - 1) + s.sSize := by omega
            rw [e, Nat.add_div_right _ hs]
          · have e1 : buf.length - (index + s.sSize) + s.sSize - 1 < s.sSize := by omega
            have e2 : (buf.length - index + s.sSize - 1) / s.sSize = 1 := by
              apply Nat.div_eq_of_lt_le <;> omega
            rw [Nat.div_eq_of_lt e1, e2]

/-- `iter_unpack` yields exactly `len(buffer) / size` tuples, which is the `__length_hint__`
of the fresh iterator. -/
def IterUnpackLength : Prop :=
  ∀ (f : FmtArg) (s : SObj) (buf : List Nat) (l : List (List SV)),
    cacheStruct f = .ok s → modIterUnpack f buf = .ok l → l.length = unpackiterLen s buf 0

theorem iterUnpackLength_proven : IterUnpackLength := by
  intro f s buf l hs h
  simp only [modIterUnpack, hs, bind, Except.bind] at h
  unfold structIterUnpack at h
  by_cases h0 : s.sSize = 0
  · rw [if_pos h0] at h
    cases h
  rw [if_neg h0] at h
  by_cases hm : buf.length % s.sSize ≠ 0
  · rw [if_pos hm] at h
    cases h
  rw [if_neg hm] at h
  have hpos : 0 < s.sSize := Nat.pos_of_ne_zero h0
  rw [iterLoop_length s buf hpos _ _ _ h]
  unfold unpackiterLen
  have hdvd : buf.length = s.sSize * (buf.length / s.sSize) := by
    have := Nat.div_add_mod buf.length s.sSize
    omega
  generalize buf.length / s.sSize = k at hdvd
  simp only [Nat.sub_zero]
  rw [hdvd]
  have e : s.sSize * k + s.sSize - 1 = (s.sSize - 1) + s.sSize * k := by omega
  rw [e, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt (by omega)]
  omega

/-- For every accepted ASCII `str` format: `Struct(fmt).format == fmt`, `.size` and
`calcsize(fmt)` are the size `prepare_s` computed, and `__sizeof__` counts one `formatcode` per
code plus the sentinel. -/
def Accessors : Prop :=
  ∀ (cps : List Nat) (s : SObj), structInit (.str cps) = .ok s →
    sGetFormat s = cps ∧ sGetSize (some s) = (s.sSize : Int) ∧
    calcsize (.str cps) = .ok s.sSize ∧ sSizeof s = 56 + 32 * (s.codes.length + 1)

theorem accessors_proven : Accessors := by
  intro cps s h
  have hc : cacheStruct (.str cps) = .ok s := h
  have hf : s.format = cps := by
    simp only [structInit] at h
    split at h
    · obtain ⟨st, _, _, _, _, hf⟩ := prepareSAgree_proven cps s h
      exact hf
    · cases h
  refine ⟨hf, rfl, ?_, ?_⟩
  · simp only [calcsize, hc, bind, Except.bind, pure, Except.pure]
  · simp only [sSizeof]
    omega

/-- Before `__init__`, `.size` is -1, and every method raises `RuntimeError`. -/
def UninitStruct : Prop :=
  sGetSize sNew = -1 ∧ ∀ (α : Type) (k : SObj → Py α),
    (ensureReady sNew >>= k) = .error (.named "RuntimeError" "Struct object is not initialized")

theorem uninitStruct_proven : UninitStruct := ⟨rfl, fun _ _ => rfl⟩

/-- `_range_error`'s message states the exact range of the entry, for every integer entry whose
pack routine uses it. -/
def RangeErrorBounds : Prop :=
  ∀ e ∈ intEntries, e.format ≠ 'P' →
    rangeError e (isUnsignedCode e.format)
      = structErr s!"'{e.format}' format requires {loOf e} <= number <= {hiOf e}"

theorem rangeErrorBounds_proven : RangeErrorBounds := by
  unfold RangeErrorBounds
  decide +kernel

/-- `repr(Struct(fmt))` of a format without whitespace is `Struct('fmt')`. -/
def ReprPlain : Prop :=
  ∀ s : SObj, (∀ c ∈ s.format, 32 ≤ c) →
    sRepr s = "Struct('" ++ String.join (s.format.map (fun c => String.singleton (Char.ofNat c))) ++ "')"

theorem reprPlain_proven : ReprPlain := by
  intro s h
  have hm : s.format.map reprChar = s.format.map (fun c => String.singleton (Char.ofNat c)) := by
    apply List.map_congr_left
    intro c hc
    have := h c hc
    unfold reprChar
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
  unfold sRepr
  rw [hm]

/-- Every non-NaN float survives `unpack('<f')` then `pack('<f')`. Stated, not yet proven. -/
def FloatRoundTrip : Prop :=
  ∀ y < 2 ^ 32, f32.isNaN y = false → pyFloatPack4Bits (pyFloatUnpack4Bits y) = .ok y


end PyLean.TextLibs.Struct
