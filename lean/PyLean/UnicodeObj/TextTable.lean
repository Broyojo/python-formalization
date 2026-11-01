import PyLean.UnicodeObj.Ctype

/-!
Facts about every code point, proved by kernel evaluation of the two-stage
tables.

Reading the tables once per code point exhausts the kernel's memory limit, so the
check follows the structure of the tables. Each of the distinct 64-entry blocks of
`index2` is checked once (`blockCheck`), which settles everything that does not
depend on the code point. What does depend on it is `ch + delta` of the non-extended
records, and only blocks with a non-zero delta need it: for those, every code point
that reaches the block through `index1` is checked (`hiCheck`).
-/

namespace PyLean.UnicodeObj

open Tables

/-- All of `p lo .. p (lo + 2^k - 1)`, by bisection so the recursion depth is `k`. -/
def rangeAll (p : Nat → Bool) : Nat → Nat → Bool
  | 0, lo => p lo
  | k + 1, lo => rangeAll p k lo && rangeAll p k (lo + 2 ^ k)

theorem rangeAll_spec (p : Nat → Bool) (k lo : Nat) (h : rangeAll p k lo = true) :
    ∀ i, lo ≤ i → i < lo + 2 ^ k → p i = true := by
  induction k generalizing lo with
  | zero =>
    intro i h1 h2
    simp only [Nat.pow_zero] at h2
    have : i = lo := by omega
    subst this; simpa [rangeAll] using h
  | succ k ih =>
    intro i h1 h2
    simp only [rangeAll, Bool.and_eq_true] at h
    by_cases hi : i < lo + 2 ^ k
    · exact ih lo h.1 i h1 hi
    · have e : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
      exact ih (lo + 2 ^ k) h.2 i (by omega) (by omega)

/-- A full case mapping has 1 to 3 valid code points. -/
def goodMapping (m : List Nat) : Bool :=
  decide (1 ≤ m.length) && decide (m.length ≤ 3) && m.all (· ≤ maxUnicode)

/-- How the property flags relate. Stated over `Bool`s, so consequences follow by
`decide`: `isdecimal` implies `isdigit` implies `isnumeric`; lower, upper and title
exclude each other and together make up cased; XID_Start is in XID_Continue. -/
def flagFact (dec dig num l u t cased xs xc : Bool) : Bool :=
  (!dec || dig) && (!dig || num) && !(l && u) && !(l && t) && !(u && t) &&
  (!l || cased) && (!u || cased) && (!t || cased) && (!cased || l || u || t) && (!xs || xc)

theorem flagFact_spec : ∀ dec dig num l u t cased xs xc : Bool,
    flagFact dec dig num l u t cased xs xc = true →
    (dec = true → dig = true) ∧ (dig = true → num = true) ∧
    (¬ (l = true ∧ u = true) ∧ ¬ (l = true ∧ t = true) ∧ ¬ (u = true ∧ t = true) ∧
      (cased = true ↔ l = true ∨ u = true ∨ t = true)) ∧ (xs = true → xc = true) := by
  intro dec dig num l u t cased xs xc h
  cases dec <;> cases dig <;> cases num <;> cases l <;> cases u <;> cases t <;> cases cased <;>
    cases xs <;> cases xc <;> first | exact absurd h (by decide) | simp

theorem addUCS4_zero {c : Nat} (h : c ≤ maxUnicode) : addUCS4 c 0 = c := by
  have hm : maxUnicode = 0x10FFFF := rfl
  have h2 : (2 : Int) ^ 32 = 4294967296 := by decide
  have : ((c : Int) + 0) % 2 ^ 32 = c := Int.emod_eq_of_lt (by omega) (by omega)
  simp only [addUCS4, this]
  simp

/-- `_PyUnicode_To*Full` on a given record. -/
def fullOf (field : TypeRecord → Int) (r : TypeRecord) (ch : Nat) : List Nat :=
  if hasFlag r EXTENDED_CASE_MASK then
    let v := (field r).toNat
    extendedRun (v &&& 0xFFFF) (v >>> 24)
  else [addUCS4 ch (field r)]

/-- `_PyUnicode_ToFoldedFull` on a given record. -/
def foldOf (r : TypeRecord) (ch : Nat) : List Nat :=
  let lower := r.lower.toNat
  if hasFlag r EXTENDED_CASE_MASK && ((lower >>> 20) &&& 7) != 0 then
    extendedRun ((lower &&& 0xFFFF) + (lower >>> 24)) ((lower >>> 20) &&& 7)
  else fullOf TypeRecord.lower r ch

theorem toLowerFull_eq (c) : toLowerFull c = fullOf TypeRecord.lower (gettyperecord c) c := rfl
theorem toUpperFull_eq (c) : toUpperFull c = fullOf TypeRecord.upper (gettyperecord c) c := rfl
theorem toTitleFull_eq (c) : toTitleFull c = fullOf TypeRecord.title (gettyperecord c) c := rfl
theorem toFoldedFull_eq (c) : toFoldedFull c = foldOf (gettyperecord c) c := rfl

/-- What must hold of a record, independently of the code point. The mappings are
read at `ch = 0`; for an extended record they do not depend on `ch`. -/
def recIndep (r : TypeRecord) : Bool :=
  let f := fun m => hasFlag r m
  flagFact (f DECIMAL_MASK) (f DIGIT_MASK) (f NUMERIC_MASK) (f LOWER_MASK) (f UPPER_MASK)
    (f TITLE_MASK) (f CASED_MASK) (f XID_START_MASK) (f XID_CONTINUE_MASK) &&
  decide (r.decimal ≤ 9) && decide (r.digit ≤ 9) &&
  (!f DECIMAL_MASK || decide (r.decimal = r.digit)) &&
  (!f EXTENDED_CASE_MASK ||
    (goodMapping (fullOf TypeRecord.lower r 0) && goodMapping (fullOf TypeRecord.upper r 0) &&
     goodMapping (fullOf TypeRecord.title r 0) && goodMapping (foldOf r 0)))

/-- `ch + delta` is in range, for a non-extended record. -/
def deltaOk (c : Nat) (r : TypeRecord) : Bool :=
  hasFlag r EXTENDED_CASE_MASK ||
    (decide (addUCS4 c r.upper ≤ maxUnicode) && decide (addUCS4 c r.lower ≤ maxUnicode) &&
     decide (addUCS4 c r.title ≤ maxUnicode))

/-- All case deltas are zero, or the record is extended. -/
def recZero (r : TypeRecord) : Bool :=
  hasFlag r EXTENDED_CASE_MASK ||
    (decide (r.upper = 0) && decide (r.lower = 0) && decide (r.title = 0))

/-- The type record of entry `j` of block `b`. -/
def recInBlock (b j : Nat) : TypeRecord :=
  recordAt (pickChunked index2Chunk 6 16 ((b <<< shift) + j))

/-- `index1`. -/
def idx1 (hi : Nat) : Nat := pickChunked index1Chunk 6 16 hi

def hasDelta (b : Nat) : Bool := ((deltaBlocks >>> b) &&& 1) != 0

def blockCheck (b : Nat) : Bool :=
  decide (blockCount ≤ b) ||
    (rangeAll (fun j => recIndep (recInBlock b j)) 6 0 &&
     (hasDelta b || rangeAll (fun j => recZero (recInBlock b j)) 6 0))

def hiCheck (hi : Nat) : Bool :=
  decide (0x4400 ≤ hi) ||
    (decide (idx1 hi < blockCount) &&
     (!hasDelta (idx1 hi) ||
       rangeAll (fun j => deltaOk (hi * 64 + j) (recInBlock (idx1 hi) j)) 6 0))

theorem blocks_ok : rangeAll blockCheck 11 0 = true := by decide +kernel
theorem his_ok : rangeAll hiCheck 15 0 = true := by decide +kernel

theorem gettyperecord_eq {c : Nat} (h : c ≤ maxUnicode) :
    gettyperecord c = recInBlock (idx1 (c >>> 6)) (c &&& 63) := by
  have hm : maxUnicode = 0x10FFFF := rfl
  have : ¬ c ≥ 0x110000 := by omega
  simp only [gettyperecord, this, if_false]
  rfl

theorem c_parts {c : Nat} (h : c ≤ maxUnicode) :
    c >>> 6 < 0x4400 ∧ c &&& 63 < 64 ∧ (c >>> 6) * 64 + (c &&& 63) = c := by
  have hm : maxUnicode = 0x10FFFF := rfl
  have h1 : c >>> 6 = c / 64 := by simp [Nat.shiftRight_eq_div_pow]
  have h2 : c &&& 63 = c % 64 := Nat.and_two_pow_sub_one_eq_mod c 6
  rw [h1, h2]
  omega

theorem rec_facts {c : Nat} (h : c ≤ maxUnicode) :
    recIndep (gettyperecord c) = true ∧ deltaOk c (gettyperecord c) = true := by
  obtain ⟨h1, h2, h3⟩ := c_parts h
  rw [gettyperecord_eq h]
  generalize hb : idx1 (c >>> 6) = b
  generalize hj : c &&& 63 = j at *
  have hhi := rangeAll_spec _ _ _ his_ok (c >>> 6) (Nat.zero_le _) (by
    have : (2 : Nat) ^ 15 = 32768 := by decide
    have : (0x4400 : Nat) ≤ 32768 := by decide
    omega)
  simp only [hiCheck, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true'] at hhi
  rcases hhi with hhi | ⟨hlt, hd⟩
  · omega
  · rw [hb] at hlt hd
    have hbl := rangeAll_spec _ _ _ blocks_ok b (Nat.zero_le _) (by
      have : blockCount ≤ 2 ^ 11 := by decide
      omega)
    simp only [blockCheck, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hbl
    rcases hbl with hbl | ⟨ha, hz⟩
    · omega
    · have hj64 : j < 0 + 2 ^ 6 := by
        have : (2 : Nat) ^ 6 = 64 := by decide
        omega
      refine ⟨rangeAll_spec _ _ _ ha j (Nat.zero_le _) hj64, ?_⟩
      by_cases hdb : hasDelta b = true
      · rcases hd with hd | hd
        · simp [hdb] at hd
        · have := rangeAll_spec _ _ _ hd j (Nat.zero_le _) hj64
          rwa [h3] at this
      · have hzero : rangeAll (fun j => recZero (recInBlock b j)) 6 0 = true := by
          rcases hz with hz | hz
          · exact absurd hz hdb
          · exact hz
        have := rangeAll_spec _ _ _ hzero j (Nat.zero_le _) hj64
        simp only [recZero, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
        simp only [deltaOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        rcases this with hx | ⟨⟨u, l⟩, t⟩
        · exact Or.inl hx
        · refine Or.inr ?_
          rw [u, l, t, addUCS4_zero h]
          exact ⟨⟨h, h⟩, h⟩

theorem charFact_all {c : Nat} (h : c ≤ maxUnicode) :
    (flagFact (hasFlag (gettyperecord c) DECIMAL_MASK) (hasFlag (gettyperecord c) DIGIT_MASK)
      (hasFlag (gettyperecord c) NUMERIC_MASK) (hasFlag (gettyperecord c) LOWER_MASK)
      (hasFlag (gettyperecord c) UPPER_MASK) (hasFlag (gettyperecord c) TITLE_MASK)
      (hasFlag (gettyperecord c) CASED_MASK) (hasFlag (gettyperecord c) XID_START_MASK)
      (hasFlag (gettyperecord c) XID_CONTINUE_MASK) = true) ∧
    (gettyperecord c).decimal ≤ 9 ∧ (gettyperecord c).digit ≤ 9 := by
  have := (rec_facts h).1
  simp only [recIndep, Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1.1.1.1, this.1.1.1.2, this.1.1.2⟩

theorem fullOf_ext (field r c) (h : hasFlag r EXTENDED_CASE_MASK = true) :
    fullOf field r c = fullOf field r 0 := by
  simp [fullOf, h]

theorem good_of_delta (field : TypeRecord → Int) (r c) (hx : hasFlag r EXTENDED_CASE_MASK = false)
    (hd : addUCS4 c (field r) ≤ maxUnicode) : goodMapping (fullOf field r c) = true := by
  simp [fullOf, hx, goodMapping, hd]

theorem charFact_case {c} (h : c ≤ maxUnicode) :
    goodMapping (toLowerFull c) = true ∧ goodMapping (toUpperFull c) = true ∧
    goodMapping (toTitleFull c) = true ∧ goodMapping (toFoldedFull c) = true := by
  obtain ⟨h1, h2⟩ := rec_facts h
  rw [toLowerFull_eq, toUpperFull_eq, toTitleFull_eq, toFoldedFull_eq]
  generalize gettyperecord c = r at *
  simp only [recIndep, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h1
  have h3 := h1.2
  cases hx : hasFlag r EXTENDED_CASE_MASK with
  | true =>
    rcases h3 with h3 | ⟨⟨⟨a, b⟩, c'⟩, d⟩
    · simp [hx] at h3
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [fullOf_ext _ _ _ hx]; exact a
      · rw [fullOf_ext _ _ _ hx]; exact b
      · rw [fullOf_ext _ _ _ hx]; exact c'
      · have e : foldOf r c = foldOf r 0 := by
          simp only [foldOf]
          split
          · rfl
          · exact fullOf_ext _ _ _ hx
        rw [e]; exact d
  | false =>
    simp only [deltaOk, hx, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h2
    obtain ⟨⟨u, l⟩, t⟩ := h2
    refine ⟨good_of_delta _ _ _ hx l, good_of_delta _ _ _ hx u, good_of_delta _ _ _ hx t, ?_⟩
    simp only [foldOf, hx, Bool.false_and, Bool.false_eq_true, if_false]
    exact good_of_delta _ _ _ hx l

theorem isDecimalDigit_flag (c : Nat) :
    isDecimalDigit c = hasFlag (gettyperecord c) DECIMAL_MASK := by
  simp only [isDecimalDigit, toDecimalDigit]
  by_cases f : hasFlag (gettyperecord c) DECIMAL_MASK = true
  · simp only [f, if_true]; simp [Int.not_lt]
  · simp only [f, if_false]; simp

theorem isDigit_flag (c : Nat) : isDigit c = hasFlag (gettyperecord c) DIGIT_MASK := by
  simp only [isDigit, toDigit]
  by_cases f : hasFlag (gettyperecord c) DIGIT_MASK = true
  · simp only [f, if_true]; simp [Int.not_lt]
  · simp only [f, if_false]; simp

theorem flags_ok {c} (h : c ≤ maxUnicode) :
    flagFact (isDecimalDigit c) (isDigit c) (isNumeric c) (isLowercase c) (isUppercase c)
      (isTitlecase c) (isCased c) (isXidStart c) (isXidContinue c) = true := by
  rw [isDecimalDigit_flag, isDigit_flag]
  exact (charFact_all h).1

theorem decimal_bound {c} (h : c ≤ maxUnicode) : toDecimalDigit c ≤ 9 := by
  have h9 := (charFact_all h).2.1
  simp only [toDecimalDigit]
  split <;> omega

end PyLean.UnicodeObj
