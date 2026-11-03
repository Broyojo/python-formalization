import PyLean.TextLibs.StructFloat

/-!
The standard-size integer routines `bp_int`, `bp_uint`, `bp_longlong`, `bp_ulonglong` and their `lp_*`
twins (`Modules/_struct.c:998-1099, 1324-1425`), for every value, and the table swap of
`init_endian_tables` (`Modules/_struct.c:1519-1557`) for every entry.
-/

namespace PyLean.TextLibs.Struct

open PyLean PyLean.TextLibs

set_option linter.unusedSimpArgs false

/-! ### `bp_*` and `lp_*` integer routines -/

/-- The range each standard integer routine checks: `bp_int`/`lp_int` by the entry's size (1011-1017,
1337-1343), `bp_uint`/`lp_uint` against `1 << (8 * size)` (1039-1044, 1365-1370), and the `long long`
routines through `_PyLong_AsByteArray` on 8 bytes. -/
def stdIntSpec (e : FormatDef) : Option (Int × Int) :=
  match e.pack with
  | .bpInt | .lpInt =>
    if e.size = 2 then some (-32768, 32767) else if e.size = 4 then some (-2147483648, 2147483647) else none
  | .bpUint | .lpUint =>
    if e.size = 2 then some (0, 65535) else if e.size = 4 then some (0, 4294967295) else none
  | .bpLonglong | .lpLonglong => some (-9223372036854775808, 9223372036854775807)
  | .bpUlonglong | .lpUlonglong => some (0, 18446744073709551615)
  | _ => none

/-- Does the routine take `get_pylong`'s result straight to `_PyLong_AsByteArray`? -/
def stdIsLonglong : PFn → Bool
  | .bpLonglong | .lpLonglong | .bpUlonglong | .lpUlonglong => true
  | _ => false

/-- The standard tables and their byte order: big-endian, and the little-endian one both before and
after `init_endian_tables` (the routines it replaces are reached only by proofs on this build). -/
def stdTables : List (List FormatDef × Bool) :=
  [(bigendianTable, false), (lilendianTable0, true), (lilendianTable, true)]

/-- Every standard integer routine in every standard table: for the int `__index__` gives, it writes the
entry's size in bytes, two's complement in the table's order, inside the range, and raises
`struct.error('<c> format requires lo <= number <= hi')` outside it. An exception from `__index__` other
than `OverflowError` comes out unchanged. An `OverflowError` from `__index__` is the range error for
`bp_int`, `bp_uint`, `lp_int` and `lp_uint`, which go through `get_long`/`get_ulong` (1004-1009), and
comes out unchanged from the `long long` routines, which call `get_pylong` and no `PyLong_As*`
(1056-1058). A pack that wrapped, truncated or skipped a check fails this. -/
def StdIntPack : Prop :=
  ∀ (tbl : List FormatDef) (le : Bool), (tbl, le) ∈ stdTables → ∀ e ∈ tbl, ∀ lo hi : Int,
    stdIntSpec e = some (lo, hi) → ∀ v : SV,
      (∀ n, getPylong v = .ok n →
        runPack e v = if lo ≤ n ∧ n ≤ hi then .ok (if le then lpLoop e.size n else bpLoop e.size n)
          else .error (npRangeMsg e lo hi)) ∧
      (∀ m, getPylong v = .error (.overflowError m) →
        runPack e v = .error (if stdIsLonglong e.pack then .overflowError m else npRangeMsg e lo hi)) ∧
      (∀ x, getPylong v = .error x → (∀ m, x ≠ .overflowError m) → runPack e v = .error x)

/-- The error each standard routine raises outside its range. -/
def stdErr (e : FormatDef) : PyExc :=
  match e.pack with
  | .bpLonglong | .lpLonglong => llRangeErr e
  | .bpUlonglong | .lpUlonglong => ullRangeErr e
  | .bpUint | .lpUint => rangeError e true
  | _ => rangeError e false

def stdEntryOk (le : Bool) (e : FormatDef) : Bool :=
  match stdIntSpec e with
  | some (lo, hi) =>
    stdErr e == npRangeMsg e lo hi &&
      (match e.pack with
       | .bpInt | .bpUint | .bpLonglong | .bpUlonglong => !le
       | .lpInt | .lpUint | .lpLonglong | .lpUlonglong => le
       | _ => false) &&
      (stdIsLonglong e.pack → e.size = 8)
  | none => true

theorem std_tables : ∀ p ∈ stdTables, ∀ e ∈ p.1, stdEntryOk p.2 e = true := by
  decide +kernel

theorem std_law_ok (e : FormatDef) (le : Bool) (lo hi : Int) (hspec : stdIntSpec e = some (lo, hi))
    (hok : stdEntryOk le e = true) (v : SV) (n : Int) (h : getPylong v = .ok n) :
    runPack e v = if lo ≤ n ∧ n ≤ hi then .ok (if le then lpLoop e.size n else bpLoop e.size n)
      else .error (npRangeMsg e lo hi) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (getConversions_proven v).2 n h
  have hm : stdErr e = npRangeMsg e lo hi := by
    simp only [stdEntryOk, hspec, Bool.and_eq_true, beq_iff_eq] at hok; exact hok.1.1
  have hl : (match e.pack with
       | .bpInt | .bpUint | .bpLonglong | .bpUlonglong => !le
       | .lpInt | .lpUint | .lpLonglong | .lpUlonglong => le
       | _ => false) = true := by
    simp only [stdEntryOk, hspec, Bool.and_eq_true] at hok; exact hok.1.2
  have h8 : stdIsLonglong e.pack = true → e.size = 8 := by
    simp only [stdEntryOk, hspec, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.2
  revert hspec hm hl h8
  cases hp : e.pack <;> intro hspec hm hl h8 <;> simp only [stdIntSpec, hp, reduceCtorEq] at hspec
  all_goals
    simp only [stdErr, hp, llRangeErr, ullRangeErr, longMin_eq, longMax_eq, ulongMax_eq] at hm
    simp only [hp, Bool.not_eq_true'] at hl
    subst hl
    simp only [stdIsLonglong, hp, forall_const, Bool.false_eq_true, false_implies] at h8
  all_goals
    by_cases hs2 : e.size = 2 <;> by_cases hs4 : e.size = 4 <;>
      simp only [hs2, hs4, if_true, if_false, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hspec h8
  all_goals
    obtain ⟨rfl, rfl⟩ := hspec
    simp only [runPack, hp, packIntStd, packUintStd, packLonglongStd, packUlonglongStd, h, h1, h2, h3, h4,
      h5, h6, longMin_eq, longMax_eq, ulongMax_eq, hs2, hs4, h8]
    by_cases hA : -9223372036854775808 ≤ n ∧ n ≤ 9223372036854775807 <;> by_cases hN : n < 0 <;>
      by_cases hU : n ≤ 18446744073709551615 <;>
      simp (config := {decide := true}) only [hA, hN, hU, and_self, true_and, and_true, false_and,
        and_false, or_self, true_or, or_true, false_or, or_false, if_true, if_false, ↓reduceIte, orRange,
        bind, Except.bind, pure, Except.pure, hm, ne_eq, throw, throwThe, MonadExceptOf.throw,
        Bool.false_eq_true, reduceCtorEq, not_false_eq_true, Nat.reduceMul, Nat.reducePow] <;>
      repeat' split
  all_goals first
    | rfl
    | (exfalso; omega)
    | (simp only [Except.error.injEq, Except.ok.injEq, reduceCtorEq]; omega)
    | (simp only [Except.error.injEq, Except.ok.injEq]; done)

theorem std_law_err (e : FormatDef) (lo hi : Int) (hspec : stdIntSpec e = some (lo, hi))
    (hm : stdErr e = npRangeMsg e lo hi) (v : SV) (x : PyExc) (h : getPylong v = .error x) :
    runPack e v = .error (match x with
      | .overflowError m => if stdIsLonglong e.pack then .overflowError m else npRangeMsg e lo hi
      | x => x) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (getConversions_proven v).1 _ h
  revert hspec hm
  cases hp : e.pack <;> intro hspec hm <;> simp only [stdIntSpec, hp, reduceCtorEq] at hspec <;>
    simp only [stdErr, hp, llRangeErr, ullRangeErr, longMin_eq, longMax_eq, ulongMax_eq] at hm <;>
    cases x <;>
    simp only [runPack, hp, packIntStd, packUintStd, packLonglongStd, packUlonglongStd, h, h1, h2, h3, h4,
      h5, h6, orRange, bind, Except.bind, stdIsLonglong, if_true, if_false, Bool.false_eq_true, hm] <;>
    first | rfl | (split at hspec <;> first | (cases hspec; done) | skip) | skip

theorem stdIntPack_proven : StdIntPack := by
  intro tbl le hmem e he lo hi hspec v
  have hok := std_tables (tbl, le) hmem e he
  have hm : stdErr e = npRangeMsg e lo hi := by
    simp only [stdEntryOk, hspec, Bool.and_eq_true, beq_iff_eq] at hok; exact hok.1.1
  refine ⟨fun n h => std_law_ok e le lo hi hspec hok v n h, fun m h => ?_, fun x h hx => ?_⟩
  · rw [std_law_err e lo hi hspec hm v _ h]
  · rw [std_law_err e lo hi hspec hm v _ h]
    cases x with
    | overflowError m => exact absurd rfl (hx m)
    | _ => rfl

/-! ### The twins disagree: `<q` and `>q` on an `OverflowError` from `__index__` -/

/-- `'<q'` (where `init_endian_tables` put `np_longlong`) and `'>q'` (`bp_longlong`) pack every value to
mirrored bytes or raise the same exception. False: `np_longlong` replaces an `OverflowError` from
`__index__` with `struct.error` (`Modules/_struct.c:708-715`), and `bp_longlong` lets it through
(1056-1058). -/
def StdLonglongTwins : Prop :=
  ∀ v : SV, modPack (.str ['<'.toNat, 'q'.toNat]) [v]
    = (modPack (.str ['>'.toNat, 'q'.toNat]) [v]).map List.reverse

def idxOverflow : SV := .obj { index := some (.error (.overflowError "boom")) }

theorem stdLonglongTwins_refuted : ¬StdLonglongTwins := by
  intro h
  have := h idxOverflow
  revert this
  decide +kernel

/-! ### `init_endian_tables` -/

/-- What `init_endian_tables` should do to one entry of the little-endian table: give it the pack and
unpack routines of the native entry with the same format if that entry has the same size, except for
`?`, whose standard routine is kept on purpose (1544-1547). -/
def swapRule (e : FormatDef) : FormatDef :=
  match nativeTable.find? (fun n => n.format == e.format) with
  | some n => if n.size = e.size ∧ e.format ≠ ['?'] then { e with pack := n.pack, unpack := n.unpack } else e
  | none => e

/-- `init_endian_tables` applies `swapRule` to every entry of the little-endian table, both routines of
each: on this build `b`, `B`, `c`, `h`, `H`, `i`, `I`, `q`, `Q`, `e`, `f`, `d`, `F`, `D`, `Zf` and `Zd` get the
native pack and unpack routines, `?` keeps `bp_bool`/`bu_bool`, and the 4-byte `l` and `L` keep their
`lp_*`/`lu_*` routines. An init that skipped any swap, or swapped pack but not unpack, fails this. -/
def EndianTableSwap : Prop :=
  lilendianTable = lilendianTable0.map swapRule ∧
  (lilendianTable.filter (fun e => e.format ∈ [['h'], ['H'], ['i'], ['I'], ['q'], ['Q'], ['e'], ['f'],
      ['d'], ['F'], ['D'], ['Z', 'f'], ['Z', 'd']])).map (fun e => (e.pack, e.unpack))
    = [(.npShort, .nuShort), (.npUshort, .nuUshort), (.npInt, .nuInt), (.npUint, .nuUint),
       (.npLonglong, .nuLonglong), (.npUlonglong, .nuUlonglong), (.npHalffloat, .nuHalffloat),
       (.npFloat, .nuFloat), (.npDouble, .nuDouble), (.npFloatComplex, .nuFloatComplex),
       (.npDoubleComplex, .nuDoubleComplex), (.npFloatComplex, .nuFloatComplex),
       (.npDoubleComplex, .nuDoubleComplex)] ∧
  (lilendianTable.filter (fun e => e.format ∈ [['?'], ['l'], ['L']])).map (fun e => (e.pack, e.unpack))
    = [(.lpInt, .luInt), (.lpUint, .luUint), (.bpBool, .buBool)]

theorem endianTableSwap_proven : EndianTableSwap := by
  unfold EndianTableSwap
  decide +kernel

end PyLean.TextLibs.Struct
