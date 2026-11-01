import PyLean.CoreLibs.CollAbc.Model

/-!
`Set._hash` against `frozenset_hash`: the Python loop over arbitrary-precision `int` with masking
and the C loop over `Py_uhash_t` table slots compute the same value.
-/

namespace PyLean.CoreLibs.CollAbc

open PyLean

theorem ofInt_pyXor (a b : Int) :
    BitVec.ofInt 64 (pyXor a b) = BitVec.ofInt 64 a ^^^ BitVec.ofInt 64 b := by
  cases a with
  | ofNat a =>
    cases b with
    | ofNat b =>
      simp only [pyXor, Int.ofNat_eq_natCast, BitVec.ofInt_natCast, BitVec.ofNat_xor]
    | negSucc b =>
      simp only [pyXor, Int.ofNat_eq_natCast, BitVec.ofInt_natCast,
        BitVec.ofInt_negSucc_eq_not_ofNat, BitVec.ofNat_xor, BitVec.not_xor_right]
  | negSucc a =>
    cases b with
    | ofNat b =>
      simp only [pyXor, Int.ofNat_eq_natCast, BitVec.ofInt_natCast,
        BitVec.ofInt_negSucc_eq_not_ofNat, BitVec.ofNat_xor, BitVec.not_xor_left]
    | negSucc b =>
      simp only [pyXor, Int.ofNat_eq_natCast, BitVec.ofInt_natCast,
        BitVec.ofInt_negSucc_eq_not_ofNat, BitVec.ofNat_xor]
      rw [← BitVec.not_xor_left, ← BitVec.not_xor_right, BitVec.not_not]

theorem ofInt_shuffle (hx : Int) :
    BitVec.ofInt 64 ((pyXor (pyXor hx (hx * 2 ^ 16)) 89869747) * 3644798167) =
      shuffleBits (BitVec.ofInt 64 hx) := by
  rw [BitVec.ofInt_mul, ofInt_pyXor, ofInt_pyXor, BitVec.ofInt_mul]
  simp only [shuffleBits, BitVec.shiftLeft_eq_mul_twoPow]
  generalize BitVec.ofInt 64 hx = b
  have h1 : BitVec.ofInt 64 ((2 : Int) ^ 16) = BitVec.twoPow 64 16 := by decide
  have h2 : BitVec.ofInt 64 (89869747 : Int) = 89869747#64 := by decide
  have h3 : BitVec.ofInt 64 (3644798167 : Int) = 3644798167#64 := by decide
  rw [h1, h2, h3, BitVec.xor_assoc, BitVec.xor_comm (b * _), ← BitVec.xor_assoc]

theorem ofInt_toNat_cast (b : BitVec 64) : BitVec.ofInt 64 (b.toNat : Int) = b := by
  simp

theorem hashRound_toNat (b : BitVec 64) (hx : Int) :
    hashRound b.toNat hx = (b ^^^ shuffleBits (BitVec.ofInt 64 hx)).toNat := by
  have key := ofInt_pyXor (b.toNat : Int) ((pyXor (pyXor hx (hx * 2 ^ 16)) 89869747) * 3644798167)
  rw [ofInt_shuffle, ofInt_toNat_cast] at key
  rw [← key, BitVec.toNat_ofInt]
  rfl

def foldHash (b : BitVec 64) (l : List Int) : BitVec 64 :=
  l.foldl (fun h x => h ^^^ shuffleBits (BitVec.ofInt 64 x)) b

theorem foldl_hashRound (l : List Int) (b : BitVec 64) :
    l.foldl hashRound b.toNat = (foldHash b l).toNat := by
  induction l generalizing b with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, foldHash]
    rw [hashRound_toNat, ih]
    rfl

theorem foldHash_xor (l : List Int) (b c : BitVec 64) :
    foldHash (b ^^^ c) l = b ^^^ foldHash c l := by
  induction l generalizing c with
  | nil => rfl
  | cons x xs ih =>
    simp only [foldHash, List.foldl_cons]
    have := ih (c ^^^ shuffleBits (BitVec.ofInt 64 x))
    simp only [foldHash] at this
    rw [← this, BitVec.xor_assoc]

theorem foldHash_norm (b : BitVec 64) (l : List Int) : foldHash b l = b ^^^ foldHash 0#64 l := by
  have := foldHash_xor l b 0#64
  rwa [BitVec.xor_zero] at this

/-- The final stage on `Py_uhash_t`. -/
def bvFinish (h : BitVec 64) : Int :=
  let h := h ^^^ ((h >>> 11) ^^^ (h >>> 25))
  let h := h * 69069#64 + 907133923#64
  let h := if h = BitVec.ofInt 64 (-1) then 590923713#64 else h
  h.toInt

theorem toInt_const : (590923713#64).toInt = 590923713 := by decide
theorem toInt_neg_one : (BitVec.ofInt 64 (-1)).toInt = -1 := by decide

theorem sign_eq (c : BitVec 64) :
    (if (c.toNat : Int) > hashMax then (c.toNat : Int) - 2 ^ 64 else (c.toNat : Int)) = c.toInt := by
  rw [BitVec.toInt_eq_toNat_cond]
  have hlt := c.isLt
  unfold hashMax
  by_cases h : 2 * c.toNat < 2 ^ 64
  · rw [if_pos h, if_neg (by omega)]
  · rw [if_neg h, if_pos (by omega)]
    simp

theorem nat_stage (b : BitVec 64) : b.toNat ^^^ ((b.toNat >>> 11) ^^^ (b.toNat >>> 25)) =
    (b ^^^ ((b >>> 11) ^^^ (b >>> 25))).toNat := by
  simp only [BitVec.toNat_xor, BitVec.toNat_ushiftRight]

theorem mul_stage (m : BitVec 64) : (m.toNat * 69069 + 907133923) % 2 ^ 64 =
    (m * 69069#64 + 907133923#64).toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_mul]
  have h1 : (69069#64).toNat = 69069 := rfl
  have h2 : (907133923#64).toNat = 907133923 := rfl
  rw [h1, h2]
  omega

theorem hashFinish_eq (b : BitVec 64) : hashFinish b.toNat = bvFinish b := by
  simp only [hashFinish, bvFinish, nat_stage, mul_stage]
  generalize (b ^^^ ((b >>> 11) ^^^ (b >>> 25))) * 69069#64 + 907133923#64 = c
  rw [sign_eq]
  by_cases he : c = BitVec.ofInt 64 (-1)
  · rw [if_pos he, he, toInt_neg_one, if_pos rfl, toInt_const]
  · rw [if_neg he, if_neg]
    intro h
    apply he
    apply BitVec.eq_of_toInt_eq
    rw [h, toInt_neg_one]

def actives : List Slot → List Int
  | [] => []
  | .active h :: t => h :: actives t
  | _ :: t => actives t

theorem actives_length : ∀ t : List Slot, (actives t).length = (t.filter Slot.isActive).length
  | [] => rfl
  | .null :: t => by simpa [actives, Slot.isActive] using actives_length t
  | .dummy :: t => by simpa [actives, Slot.isActive] using actives_length t
  | .active h :: t => by
    have := actives_length t
    simp only [actives, List.length_cons, List.filter_cons_of_pos (p := Slot.isActive)
      (a := Slot.active h) rfl, this]

def parity (n : Nat) (t : BitVec 64) : BitVec 64 := if n % 2 = 1 then t else 0#64

theorem parity_succ (n : Nat) (t : BitVec 64) : parity (n + 1) t = t ^^^ parity n t := by
  unfold parity
  by_cases h : n % 2 = 1
  · rw [if_neg (by omega), if_pos h, BitVec.xor_self]
  · rw [if_pos (by omega), if_neg h, BitVec.xor_zero]

theorem xor_parity (h t : BitVec 64) (n : Nat) :
    (if n % 2 = 1 then h ^^^ t else h) = h ^^^ parity n t := by
  unfold parity
  by_cases c : n % 2 = 1
  · rw [if_pos c, if_pos c]
  · rw [if_neg c, if_neg c, BitVec.xor_zero]

def nullBits : BitVec 64 := shuffleBits 0
def dummyBits : BitVec 64 := shuffleBits (BitVec.ofInt 64 (-1))

theorem slot_fold (table : List Slot) (c : BitVec 64) :
    table.foldl (fun h e => h ^^^ shuffleBits e.hash) c =
      foldHash c (actives table) ^^^
        (parity (table.filter Slot.isNull).length nullBits ^^^
         parity (table.filter Slot.isDummy).length dummyBits) := by
  induction table generalizing c with
  | nil => simp [actives, foldHash, parity]
  | cons e t ih =>
    rw [List.foldl_cons, ih]
    cases e with
    | null =>
      have h1 : (Slot.null :: t).filter Slot.isNull = Slot.null :: t.filter Slot.isNull :=
        List.filter_cons_of_pos rfl
      have h2 : (Slot.null :: t).filter Slot.isDummy = t.filter Slot.isDummy :=
        List.filter_cons_of_neg (by simp [Slot.isDummy])
      rw [h1, h2, List.length_cons, parity_succ]
      simp only [actives, Slot.hash]
      rw [show shuffleBits 0 = nullBits from rfl, foldHash_norm (c ^^^ nullBits),
        foldHash_norm c]
      ac_rfl
    | dummy =>
      have h1 : (Slot.dummy :: t).filter Slot.isNull = t.filter Slot.isNull :=
        List.filter_cons_of_neg (by simp [Slot.isNull])
      have h2 : (Slot.dummy :: t).filter Slot.isDummy = Slot.dummy :: t.filter Slot.isDummy :=
        List.filter_cons_of_pos rfl
      rw [h1, h2, List.length_cons, parity_succ]
      simp only [actives, Slot.hash]
      rw [show shuffleBits (BitVec.ofInt 64 (-1)) = dummyBits from rfl,
        foldHash_norm (c ^^^ dummyBits), foldHash_norm c]
      ac_rfl
    | active h =>
      have h1 : (Slot.active h :: t).filter Slot.isNull = t.filter Slot.isNull :=
        List.filter_cons_of_neg (by simp [Slot.isNull])
      have h2 : (Slot.active h :: t).filter Slot.isDummy = t.filter Slot.isDummy :=
        List.filter_cons_of_neg (by simp [Slot.isDummy])
      rw [h1, h2]
      rfl

/-- Twin property: `Set._hash` computes the same value as the builtin `frozenset` hash, for every
table of `frozenset_hash`: any mix of null, dummy and active slots, any element hashes including
negative ones, in the table's iteration order. The source promises this: "We match the algorithm
used by the built-in frozenset type." -/
def SetHashMatchesFrozenset : Prop :=
  ∀ table : List Slot, setHash (actives table).length (actives table) = frozensetHash table

theorem setHashMatchesFrozenset_proven : SetHashMatchesFrozenset := by
  intro table
  have hlen := actives_length table
  let n := (actives table).length
  let b0 : BitVec 64 := BitVec.ofNat 64 (n + 1) * 1927868237#64
  have hinit : (1927868237 * (n + 1)) % 2 ^ 64 = b0.toNat := by
    have h := BitVec.toNat_ofNat (1927868237 * (n + 1)) 64
    rw [← h]
    show _ = (BitVec.ofNat 64 (n + 1) * BitVec.ofNat 64 1927868237).toNat
    rw [BitVec.ofNat_mul_ofNat, Nat.mul_comm]
  simp only [setHash, frozensetHash]
  rw [hinit, foldl_hashRound, hashFinish_eq, slot_fold]
  rw [← hlen]
  simp only [xor_parity]
  rw [foldHash_norm b0]
  have cancel : ∀ (a p q c : BitVec 64),
      (a ^^^ (p ^^^ q)) ^^^ p ^^^ q ^^^ c = c ^^^ a := by
    intro a p q c
    have : (a ^^^ (p ^^^ q)) ^^^ p ^^^ q ^^^ c = a ^^^ ((p ^^^ p) ^^^ ((q ^^^ q) ^^^ c)) := by
      ac_rfl
    rw [this, BitVec.xor_self, BitVec.xor_self, BitVec.zero_xor, BitVec.zero_xor, BitVec.xor_comm]
  rw [show (BitVec.ofInt 64 (-1) |> shuffleBits) = dummyBits from rfl,
    show shuffleBits 0 = nullBits from rfl, cancel]
  rfl

/-- `_DeprecateByteStringMeta`: creating a class warns unless it is `ByteString` itself, so that
the module's own definition is silent; `isinstance` warns every time and does not change the
`ABCMeta` answer. The deprecation note in `collections.abc`. -/
def ByteStringMeta : Prop :=
  (∀ name : String, byteStringMetaWarns name = true ↔ name ≠ "ByteString") ∧
  (∀ answer : Bool, byteStringInstanceCheck answer = (true, answer))

theorem byteStringMeta_proven : ByteStringMeta := by
  refine ⟨?_, fun _ => rfl⟩
  intro name
  simp [byteStringMetaWarns]

end PyLean.CoreLibs.CollAbc
