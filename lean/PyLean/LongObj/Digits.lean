import PyLean.MathInt.ToBytes

/-!
Foundations of the digit-level model of `Objects/longobject.c` (CPython 3.15.2).

Build assumptions (the interpreter under test): `PyLong_SHIFT = 30`, `digit` is
`uint32_t`, `twodigits` is `uint64_t`, `sdigit` is `int32_t`, `stwodigits` is
`int64_t`, and `long`, `long long`, `size_t` and `Py_ssize_t` are 64 bits.

An `int` is a sign and a little-endian list of digits (`Long`). `int` values use
Lean `Int` at the Python boundary, `Long.ofInt` being the canonical object
(`digitsOf` from `MathInt`: non-zero top digit, no digits for zero).

C-width arithmetic is checked rather than assumed: `chk32`, `chk64` and
`chkS64` report any intermediate that does not fit its C type as `cOverflow`,
which is never a Python outcome. A theorem of the form `f x = .ok y` therefore
also says that no carry or borrow ever left its C type. Where the C code relies
on unsigned wraparound (`borrow = a - b - borrow`) the model reduces modulo
`2^32`, as the C does.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt

/-! ## C widths -/

/-- `PyLong_MASK`. -/
def MASK : Nat := 2 ^ 30 - 1

/-- `MAX_LONG_DIGITS` on a 64-bit build, longobject.c:155: `(INT64_MAX-1) / PyLong_SHIFT`. -/
def maxLongDigits : Nat := (2 ^ 63 - 2) / 30

/-- Not a Python outcome: an intermediate did not fit its C type, or a pointer
left its buffer. -/
def cOverflow : PyExc := .named "COverflow" "~C integer overflow"

/-- The value is a `digit` / `uint32_t` expression that did not wrap. -/
def chk32 (x : Nat) : Py Nat := if x < 2 ^ 32 then .ok x else .error cOverflow
/-- The value is a `twodigits` / `uint64_t` expression that did not wrap. -/
def chk64 (x : Nat) : Py Nat := if x < 2 ^ 64 then .ok x else .error cOverflow
/-- The value fits `stwodigits` / `int64_t` (overflow would be undefined behaviour). -/
def chkS64 (x : Int) : Py Int :=
  if -(2 ^ 63 : Int) ≤ x ∧ x < 2 ^ 63 then .ok x else .error cOverflow

/-- `a - b - c` on `uint32_t`, longobject.c:3818: wraps modulo `2^32`. -/
def subU32 (a b c : Nat) : Nat := (((a : Int) - b - c) % 2 ^ 32).toNat

/-- `long_alloc(size)`, longobject.c:159-197, as far as it is observable: the
limit check at :163-167. `MemoryError` from `PyObject_Malloc` is not modelled. -/
def longAlloc (size : Nat) : Py Unit :=
  if size > maxLongDigits then .error (.overflowError "too many digits in integer")
  else .ok ()

theorem longAlloc_ok {s : Nat} (h : s ≤ maxLongDigits) : longAlloc s = .ok () := by
  simp [longAlloc, Nat.not_lt.2 h]

theorem chk32_ok {x : Nat} (h : x < 2 ^ 32) : chk32 x = .ok x := if_pos h
theorem chk64_ok {x : Nat} (h : x < 2 ^ 64) : chk64 x = .ok x := if_pos h
theorem chkS64_ok {x : Int} (h : -(2 ^ 63 : Int) ≤ x ∧ x < 2 ^ 63) : chkS64 x = .ok x := if_pos h

/-! `bind_ok` and `pure_ok` are not `rfl` theorems, for the reason given at `val_nil`. -/
theorem bind_ok {α β : Type} (a : α) (f : α → Py β) : (Except.ok a >>= f) = f a := Eq.trans rfl rfl
theorem pure_ok {α : Type} (a : α) : (pure a : Py α) = .ok a := Eq.trans rfl rfl

theorem shr30 (x : Nat) : x >>> 30 = x / 2 ^ 30 := by simp [Nat.shiftRight_eq_div_pow]
theorem and30 (x : Nat) : x &&& MASK = x % 2 ^ 30 := Nat.and_two_pow_sub_one_eq_mod x 30

/-! ## Digit vectors -/

/-- Value of a little-endian digit vector. -/
abbrev val : List Nat → Nat := digitsValue

/-- Every entry is a `digit` holding `PyLong_SHIFT` bits. -/
def IsDigits (l : List Nat) : Prop := ∀ d ∈ l, d < 2 ^ 30

/-- The top digit of a vector, if any, is non-zero (`long_normalize`'s postcondition). -/
def Normal (l : List Nat) : Prop := ∀ h : l ≠ [], l.getLast h ≠ 0

/-! `val_nil` and `val_cons` are deliberately not `rfl` theorems. `simp` would use
those as definitional rewrites, leaving the kernel to compare terms such as
`d + 2^30 * (x + 2^30 * 0)` by unfolding `Nat.mul` on an open term, which runs out
of memory on the literal `2^30`. -/
@[simp] theorem val_nil : val [] = 0 := Eq.trans rfl rfl
@[simp] theorem val_cons (d : Nat) (ds : List Nat) : val (d :: ds) = d + 2 ^ 30 * val ds :=
  Eq.trans rfl rfl

theorem isDigits_nil : IsDigits [] := by simp [IsDigits]
theorem isDigits_cons {d : Nat} {ds : List Nat} :
    IsDigits (d :: ds) ↔ d < 2 ^ 30 ∧ IsDigits ds := by
  simp [IsDigits]
theorem isDigits_append {a b : List Nat} : IsDigits (a ++ b) ↔ IsDigits a ∧ IsDigits b := by
  simp only [IsDigits, List.mem_append]
  constructor
  · intro h; exact ⟨fun d hd => h d (Or.inl hd), fun d hd => h d (Or.inr hd)⟩
  · rintro ⟨h1, h2⟩ d (hd | hd)
    · exact h1 d hd
    · exact h2 d hd
theorem isDigits_take {a : List Nat} (h : IsDigits a) (n : Nat) : IsDigits (a.take n) :=
  fun d hd => h d (List.mem_of_mem_take hd)
theorem isDigits_drop {a : List Nat} (h : IsDigits a) (n : Nat) : IsDigits (a.drop n) :=
  fun d hd => h d (List.mem_of_mem_drop hd)
theorem isDigits_replicate_zero (k : Nat) : IsDigits (List.replicate k 0) := by
  intro d hd
  rw [List.eq_of_mem_replicate hd]
  decide

theorem val_append : ∀ a b : List Nat, val (a ++ b) = val a + 2 ^ (30 * a.length) * val b
  | [], b => by simp
  | x :: xs, b => by
    have ih := val_append xs b
    simp only [List.cons_append, val_cons, ih, List.length_cons]
    rw [show 30 * (xs.length + 1) = 30 * xs.length + 30 by omega, Nat.pow_add]
    simp only [Nat.mul_add, Nat.add_assoc]
    rw [Nat.mul_comm (2 ^ 30) (2 ^ (30 * xs.length) * val b), Nat.mul_assoc]
    grind

theorem val_replicate_zero (k : Nat) : val (List.replicate k 0) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

theorem val_lt : ∀ {l : List Nat}, IsDigits l → val l < 2 ^ (30 * l.length)
  | [], _ => by simp
  | x :: xs, h => by
    have ⟨h1, h2⟩ := isDigits_cons.1 h
    have ih := val_lt h2
    simp only [val_cons, List.length_cons]
    rw [show 30 * (xs.length + 1) = 30 + 30 * xs.length by omega, Nat.pow_add]
    generalize 2 ^ (30 * xs.length) = P at *
    have : 2 ^ 30 * (val xs + 1) ≤ 2 ^ 30 * P := Nat.mul_le_mul_left _ ih
    rw [Nat.mul_add] at this
    omega

theorem val_le_of_len {l : List Nat} (h : IsDigits l) {n : Nat} (hn : l.length ≤ n) :
    val l < 2 ^ (30 * n) :=
  Nat.lt_of_lt_of_le (val_lt h) (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hn))

/-- A list that holds no digit above position `i` keeps its value when cut there. -/
theorem val_take_add_drop (l : List Nat) (n : Nat) :
    val l = val (l.take n) + 2 ^ (30 * (l.take n).length) * val (l.drop n) := by
  conv => lhs; rw [← List.take_append_drop n l]
  exact val_append _ _

/-! ## `long_normalize` -/

/-- The loop `while (i > 0 && ob_digit[i-1] == 0) --i;`, longobject.c:131-132. -/
def topNonzero (l : List Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => if l.getD i 0 = 0 then topNonzero l i else i + 1

/-- `long_normalize(v)`, longobject.c:126-142: drop the leading zero digits. -/
def normalize (l : List Nat) : List Nat := l.take (topNonzero l l.length)

theorem normal_nil : Normal [] := fun h => absurd rfl h

theorem normal_of_cons {d : Nat} {ds : List Nat} (h : Normal (d :: ds)) : Normal ds := by
  intro hne
  have := h (by simp)
  rwa [List.getLast_cons hne] at this

theorem normal_cons {d : Nat} {ds : List Nat} (h : Normal ds) (hne : ds ≠ []) : Normal (d :: ds) := by
  intro _
  rw [List.getLast_cons hne]
  exact h hne

theorem normal_singleton {d : Nat} (h : d ≠ 0) : Normal [d] := by
  intro _; simpa using h

theorem normal_concat {l : List Nat} {d : Nat} (h : d ≠ 0) : Normal (l ++ [d]) := by
  intro _
  simpa using h

private theorem take_topNonzero (l : List Nat) (i : Nat) (hi : i ≤ l.length) :
    val (l.take (topNonzero l i)) = val (l.take i) ∧ Normal (l.take (topNonzero l i)) := by
  induction i with
  | zero => simp [topNonzero, normal_nil]
  | succ i ih =>
    have hlt : i < l.length := hi
    have htake : l.take (i + 1) = l.take i ++ [l[i]] := by simp
    have hget : l.getD i 0 = l[i] := by simp [List.getD, hlt]
    simp only [topNonzero, hget]
    by_cases h0 : l[i] = 0
    · simp only [h0, ite_true]
      obtain ⟨h1, h2⟩ := ih (Nat.le_of_lt hlt)
      refine ⟨?_, h2⟩
      rw [h1, htake, val_append, h0]
      simp
    · simp only [h0, ite_false]
      refine ⟨trivial, ?_⟩
      rw [htake]
      exact normal_concat h0

theorem val_normalize (l : List Nat) : val (normalize l) = val l := by
  have := (take_topNonzero l l.length (Nat.le_refl _)).1
  simpa [normalize] using this

theorem normal_normalize (l : List Nat) : Normal (normalize l) :=
  (take_topNonzero l l.length (Nat.le_refl _)).2

theorem isDigits_normalize {l : List Nat} (h : IsDigits l) : IsDigits (normalize l) :=
  isDigits_take h _

theorem length_normalize_le (l : List Nat) : (normalize l).length ≤ l.length := by
  simp [normalize]; omega

theorem eq_nil_of_val_zero : ∀ {l : List Nat}, Normal l → val l = 0 → l = []
  | [], _, _ => rfl
  | x :: xs, hn, hv => by
    simp only [val_cons] at hv
    have hx : x = 0 := by omega
    have hxs : val xs = 0 := by
      have : 2 ^ 30 * val xs = 0 := by omega
      exact (Nat.mul_eq_zero.1 this).resolve_left (by decide)
    by_cases hne : xs = []
    · subst hne
      exact absurd hx (by simpa using hn (by simp))
    · exact absurd (eq_nil_of_val_zero (normal_of_cons hn) hxs) hne

/-- Normal digit vectors are determined by their value. -/
theorem eq_of_val_eq : ∀ {a b : List Nat}, IsDigits a → IsDigits b → Normal a → Normal b →
    val a = val b → a = b
  | [], b, _, _, _, hnb, h => (eq_nil_of_val_zero hnb (by simpa using h.symm)).symm
  | a, [], _, _, hna, _, h => eq_nil_of_val_zero hna (by simpa using h)
  | x :: xs, y :: ys, hda, hdb, hna, hnb, h => by
    have ⟨hx, hxs⟩ := isDigits_cons.1 hda
    have ⟨hy, hys⟩ := isDigits_cons.1 hdb
    simp only [val_cons] at h
    have hxy : x = y := by omega
    have hv : val xs = val ys := by
      have : 2 ^ 30 * val xs = 2 ^ 30 * val ys := by omega
      exact Nat.eq_of_mul_eq_mul_left (by decide) this
    subst hxy
    rw [eq_of_val_eq hxs hys (normal_of_cons hna) (normal_of_cons hnb) hv]

theorem digitsOf_digits (V : Nat) : IsDigits (digitsOf V) := (digitsOf_spec V).2.1
theorem val_digitsOf (V : Nat) : val (digitsOf V) = V := (digitsOf_spec V).2.2
theorem length_digitsOf (V : Nat) : (digitsOf V).length = digitCount V := (digitsOf_spec V).1

theorem normal_digitsOf (V : Nat) : Normal (digitsOf V) := by
  intro hne
  obtain ⟨l, d, hl⟩ : ∃ l d, digitsOf V = l ++ [d] :=
    ⟨(digitsOf V).dropLast, (digitsOf V).getLast hne, (List.dropLast_concat_getLast hne).symm⟩
  simp only [hl, List.getLast_concat]
  intro hd
  have hlen := length_digitsOf V
  have hv := val_digitsOf V
  have hdig := digitsOf_digits V
  rw [hl] at hlen hv hdig
  rw [val_append, hd] at hv
  simp only [val_cons, val_nil, Nat.mul_zero, Nat.add_zero] at hv
  have hl' := val_lt (isDigits_append.1 hdig).1
  have hV1 : 1 ≤ V := by
    rcases Nat.eq_zero_or_pos V with h0 | h0
    · subst h0
      have : digitCount 0 = 0 := by decide
      simp [this] at hlen
    · exact h0
  have := (digitCount_spec V).2 hV1
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  rw [← hlen] at this
  simp only [Nat.add_sub_cancel, Nat.add_zero] at this
  omega

theorem digitsOf_unique {l : List Nat} (hd : IsDigits l) (hn : Normal l) :
    digitsOf (val l) = l :=
  eq_of_val_eq (digitsOf_digits _) hd (normal_digitsOf _) hn (val_digitsOf _)

theorem digitsOf_normalize {l : List Nat} (hd : IsDigits l) :
    normalize l = digitsOf (val l) := by
  rw [← val_normalize l]
  exact (digitsOf_unique (isDigits_normalize hd) (normal_normalize l)).symm

@[simp] theorem digitsOf_zero : digitsOf 0 = [] := by decide

theorem digitsOf_eq_nil {V : Nat} : digitsOf V = [] ↔ V = 0 := by
  constructor
  · intro h
    have := val_digitsOf V
    rw [h] at this
    simpa using this.symm
  · rintro rfl; exact digitsOf_zero

/-! ## The object: sign and magnitude -/

/-- A `PyLongObject`: sign and magnitude digits. Zero has no digits and is not
negative in the canonical form `ofInt`. -/
structure Long where
  neg : Bool
  ds : List Nat
  deriving Repr, DecidableEq, Inhabited

/-- The unique normalized object of value `v`. -/
def Long.ofInt (v : Int) : Long := ⟨decide (v < 0), digitsOf v.natAbs⟩

/-- The Python value of an object. -/
def Long.toInt (x : Long) : Int := if x.neg then -(val x.ds : Int) else val x.ds

/-- `_PyLong_FlipSign`, pycore_long.h:321-326: the tag of zero is unchanged. -/
def Long.flip (x : Long) : Long := if x.ds = [] then x else { x with neg := !x.neg }

theorem Long.toInt_ofInt (v : Int) : (Long.ofInt v).toInt = v := by
  simp only [Long.ofInt, Long.toInt, val_digitsOf, decide_eq_true_eq]
  split <;> omega

theorem Long.ofInt_neg (v : Int) : Long.ofInt (-v) = (Long.ofInt v).flip := by
  simp only [Long.ofInt, Long.flip, Int.natAbs_neg]
  by_cases h : v = 0
  · subst h; simp
  · have : digitsOf v.natAbs ≠ [] := by
      rw [Ne, digitsOf_eq_nil]; omega
    simp only [this, ite_false, Long.mk.injEq, and_true]
    by_cases hv : v < 0
    · have h2 : ¬ (-v < 0) := by omega
      simp [hv, h2]; omega
    · have h2 : -v < 0 := by omega
      simp [hv, h2]; omega

/-- A normalized magnitude with a sign is the canonical object of its value. -/
theorem Long.ofInt_of_normal {neg : Bool} {l : List Nat} (hd : IsDigits l) (hn : Normal l)
    (hz : neg = true → l ≠ []) : (⟨neg, l⟩ : Long) = Long.ofInt (Long.toInt ⟨neg, l⟩) := by
  have hne : l ≠ [] → 0 < val l := by
    intro hl
    rcases Nat.eq_zero_or_pos (val l) with h | h
    · exact absurd (eq_nil_of_val_zero hn h) hl
    · exact h
  cases neg with
  | true =>
    have hp := hne (hz rfl)
    simp only [Long.toInt, ite_true, Long.ofInt, Int.natAbs_neg, Int.natAbs_natCast,
      digitsOf_unique hd hn, Long.mk.injEq, and_true]
    simp; omega
  | false =>
    simp [Long.toInt, Long.ofInt, Int.natAbs_natCast, digitsOf_unique hd hn]

/-- `ofInt` of a natural: the non-negative canonical object. -/
theorem Long.ofInt_natCast (n : Nat) : Long.ofInt (n : Int) = ⟨false, digitsOf n⟩ := by
  simp [Long.ofInt]

theorem Long.ofInt_neg_natCast {n : Nat} (hn : 0 < n) :
    Long.ofInt (-(n : Int)) = ⟨true, digitsOf n⟩ := by
  simp [Long.ofInt]; omega

/-- `_PyLong_IsCompact(x)`, longintrepr.h:122-125: at most one digit. -/
def Long.isCompact (x : Long) : Bool := x.ds.length ≤ 1

/-- `medium_value(x)`, longobject.c:27 / `_PyLong_CompactValue`, longintrepr.h:130-142. -/
def Long.medium (x : Long) : Int :=
  if x.neg then -(x.ds.headD 0 : Int) else x.ds.headD 0

/-- `_PyLong_BothAreCompact(a, b)`, pycore_long.h:212-216. -/
def bothCompact (a b : Long) : Bool := a.isCompact && b.isCompact

theorem Long.medium_eq {x : Long} (h : x.ds.length ≤ 1) : x.medium = x.toInt := by
  match hx : x with
  | ⟨neg, []⟩ => simp [Long.medium, Long.toInt]
  | ⟨neg, [d]⟩ => simp [Long.medium, Long.toInt]
  | ⟨_, _ :: _ :: _⟩ => simp at h

theorem digitCount_le_one_iff (V : Nat) : digitCount V ≤ 1 ↔ V < 2 ^ 30 := by
  constructor
  · intro h
    have := (digitCount_spec V).1
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))
  · intro h
    have hb : bitLength V ≤ 30 := bitLength_le_of_lt' h
    unfold digitCount
    omega

theorem Long.isCompact_ofInt (v : Int) : (Long.ofInt v).isCompact = decide (v.natAbs < 2 ^ 30) := by
  simp only [Long.isCompact, Long.ofInt, length_digitsOf, digitCount_le_one_iff]

theorem Long.medium_ofInt {v : Int} (h : v.natAbs < 2 ^ 30) : (Long.ofInt v).medium = v := by
  rw [Long.medium_eq]
  · exact Long.toInt_ofInt v
  · simp only [Long.ofInt, length_digitsOf]
    exact (digitCount_le_one_iff _).2 h

/-! ## Constructing small objects -/

/-- `_PY_NSMALLPOSINTS`, pycore_runtime_structs.h:97: 1025 since 3.15, and it was 257. -/
def nSmallPos : Int := 1025
/-- `_PY_NSMALLNEGINTS`, pycore_runtime_structs.h:98. -/
def nSmallNeg : Int := 5

/-- `IS_SMALL_INT(ival)`, pycore_long.h:67-68. -/
def isSmallInt (x : Int) : Bool := decide (-nSmallNeg ≤ x) && decide (x < nSmallPos)

/-- `is_medium_int(x)`, longobject.c:53-58: the unsigned comparison
`(twodigits)x + MASK < MASK + BASE`, with `uint64_t` wraparound. -/
def isMediumInt (x : Int) : Bool :=
  decide (((x + MASK) % 2 ^ 64).toNat < MASK + 2 ^ 30)

theorem isMediumInt_iff {x : Int} (h1 : -(2 ^ 63 : Int) ≤ x) (h2 : x < 2 ^ 63) :
    isMediumInt x = decide (-(MASK : Int) ≤ x ∧ x ≤ MASK) := by
  simp only [isMediumInt, MASK]
  apply decide_eq_decide.2
  omega

/-- `get_small_int(ival)`, longobject.c:61-65, and `_PyLong_FromMedium(x)`,
longobject.c:251-270: an object of one digit `|x|` (none for zero, which the
static table holds with digit count 0). -/
def fromSingle (x : Int) : Long :=
  ⟨decide (x < 0), if x = 0 then [] else [x.natAbs]⟩

/-- `*p++ = t & MASK; t >>= SHIFT;` until `t` is zero, longobject.c:302-306,
:395-399 and :435-438. -/
def digitLoop : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, t => if t ≠ 0 then (t &&& MASK) :: digitLoop f (t >>> 30) else []

/-- `_PyLong_FromLarge(ival)`, longobject.c:273-309 (64 bits need at most 3 digits;
the counting loop at :291-296 only sizes the allocation). -/
def fromLarge (x : Int) : Long :=
  ⟨decide (x < 0), digitLoop 3 ((if x < 0 then (-x).toNat else x.toNat))⟩

/-- `_PyLong_FromSTwoDigits(x)`, longobject.c:313-323. -/
def fromSTwoDigits (x : Int) : Long :=
  if isSmallInt x then fromSingle x
  else if isMediumInt x then fromSingle x
  else fromLarge x

/-- `medium_from_stwodigits(x)`, longobject.c:327-350: `_PyLong_FromSTwoDigits` for a
medium result only. `none` is `PyStackRef_NULL`: it is not an exception, and the
specialized instruction falls back to the generic `long_add`, `long_sub` or `long_mul`. -/
def mediumFromSTwoDigits (x : Int) : Option Long :=
  if isSmallInt x then some (fromSingle x)
  else if !isMediumInt x then none
  else some (fromSingle x)

/-- `_PyCompactLong_Add(a, b)`, longobject.c:3869-3875, for compact `a` and `b`. -/
def compactAdd (a b : Long) : Option Long := mediumFromSTwoDigits (a.medium + b.medium)

/-- `_PyCompactLong_Subtract(a, b)`, longobject.c:3914-3920. -/
def compactSub (a b : Long) : Option Long := mediumFromSTwoDigits (a.medium - b.medium)

/-- `_PyCompactLong_Multiply(a, b)`, longobject.c:4361-4367. -/
def compactMul (a b : Long) : Option Long := mediumFromSTwoDigits (a.medium * b.medium)

theorem digitLoop_eq (f t : Nat) (h : t < 2 ^ (30 * f)) : digitLoop f t = digitsOf t := by
  have key : ∀ f t, t < 2 ^ (30 * f) →
      IsDigits (digitLoop f t) ∧ Normal (digitLoop f t) ∧ val (digitLoop f t) = t := by
    intro f
    induction f with
    | zero =>
      intro t ht
      have : t = 0 := by simpa using ht
      subst this
      exact ⟨isDigits_nil, normal_nil, rfl⟩
    | succ f ih =>
      intro t ht
      simp only [digitLoop]
      by_cases h0 : t = 0
      · subst h0; exact ⟨isDigits_nil, normal_nil, rfl⟩
      · simp only [ne_eq, h0, not_false_eq_true, ite_true]
        have hlt : t / 2 ^ 30 < 2 ^ (30 * f) := by
          apply Nat.div_lt_of_lt_mul
          rw [← Nat.pow_add, show 30 + 30 * f = 30 * (f + 1) by omega]
          exact ht
        obtain ⟨h1, h2, h3⟩ := ih (t >>> 30) (by rw [shr30]; exact hlt)
        refine ⟨?_, ?_, ?_⟩
        · refine isDigits_cons.2 ⟨?_, h1⟩
          rw [and30]; exact Nat.mod_lt _ (by decide)
        · by_cases hn : digitLoop f (t >>> 30) = []
          · rw [hn]
            apply normal_singleton
            rw [hn] at h3
            rw [and30]
            simp only [val_nil, shr30] at h3
            omega
          · exact normal_cons h2 hn
        · simp only [val_cons, and30]
          rw [h3, shr30]
          exact Nat.mod_add_div _ _
  obtain ⟨h1, h2, h3⟩ := key f t h
  have := digitsOf_unique h1 h2
  rw [h3] at this
  exact this.symm

theorem fromLarge_eq {x : Int} (h : x.natAbs < 2 ^ 90) : fromLarge x = Long.ofInt x := by
  simp only [fromLarge, Long.ofInt, Long.mk.injEq, true_and]
  rw [digitLoop_eq 3 _ (by split <;> omega)]
  congr 1
  split <;> omega

theorem fromSingle_eq {x : Int} (h : x.natAbs < 2 ^ 30) : fromSingle x = Long.ofInt x := by
  simp only [fromSingle, Long.ofInt, Long.mk.injEq, true_and]
  by_cases h0 : x = 0
  · subst h0; simp
  · simp only [h0, ite_false]
    have hne : x.natAbs ≠ 0 := by omega
    have hd : IsDigits [x.natAbs] := isDigits_cons.2 ⟨h, isDigits_nil⟩
    have := digitsOf_unique hd (normal_singleton hne)
    simpa using this.symm

/-- `_PyLong_FromSTwoDigits` builds the canonical object for all of `int64_t`. -/
theorem fromSTwoDigits_eq {x : Int} (h1 : -(2 ^ 63 : Int) ≤ x) (h2 : x < 2 ^ 63) :
    fromSTwoDigits x = Long.ofInt x := by
  unfold fromSTwoDigits
  by_cases hs : isSmallInt x = true
  · simp only [hs, ite_true]
    apply fromSingle_eq
    simp only [isSmallInt, nSmallNeg, nSmallPos, Bool.and_eq_true] at hs
    have h3 := of_decide_eq_true hs.1
    have h4 := of_decide_eq_true hs.2
    omega
  · simp only [hs, ite_false]
    by_cases hm : isMediumInt x = true
    · simp only [hm, ite_true]
      rw [isMediumInt_iff h1 h2] at hm
      apply fromSingle_eq
      have h3 := of_decide_eq_true hm
      simp only [MASK] at h3
      omega
    · simp only [hm, ite_false]
      exact fromLarge_eq (by omega)

/-- `medium_from_stwodigits` gives the canonical object of a medium `x` and declines the rest. -/
theorem mediumFromSTwoDigits_eq {x : Int} (h1 : -(2 ^ 63 : Int) ≤ x) (h2 : x < 2 ^ 63) :
    mediumFromSTwoDigits x = if x.natAbs < 2 ^ 30 then some (Long.ofInt x) else none := by
  unfold mediumFromSTwoDigits
  by_cases hs : isSmallInt x = true
  · have hb : x.natAbs < 2 ^ 30 := by
      simp only [isSmallInt, nSmallNeg, nSmallPos, Bool.and_eq_true] at hs
      have h3 := of_decide_eq_true hs.1
      have h4 := of_decide_eq_true hs.2
      omega
    rw [if_pos hs, if_pos hb, fromSingle_eq hb]
  · rw [if_neg hs]
    by_cases hm : isMediumInt x = true
    · have hb : x.natAbs < 2 ^ 30 := by
        rw [isMediumInt_iff h1 h2] at hm
        have h3 := of_decide_eq_true hm
        simp only [MASK] at h3
        omega
      simp only [hm, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [if_pos hb, fromSingle_eq hb]
    · have hb : ¬ x.natAbs < 2 ^ 30 := by
        intro hb
        apply hm
        rw [isMediumInt_iff h1 h2]
        apply decide_eq_true
        simp only [MASK]
        omega
      have hm' : isMediumInt x = false := by simpa using hm
      simp only [hm', Bool.not_false, ite_true]
      rw [if_neg hb]

end PyLean.LongObj
