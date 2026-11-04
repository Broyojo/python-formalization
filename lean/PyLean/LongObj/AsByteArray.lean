import PyLean.MathInt.ToBytes
import PyLean.LongObj.Digits

/-!
`_PyLong_AsByteArray(v, bytes, n, little_endian, is_signed, with_exceptions)`,
`Objects/longobject.c:1108-1254` (CPython 3.15.2), with what it leaves in the buffer when
it fails and with `with_exceptions = 0`.

`MathInt.asByteArray` models the raising form, `with_exceptions = 1`, and drops the
buffer on failure. `PyLong_AsNativeBytes` calls this function with
`with_exceptions = 0` (:1406) and reads the buffer afterwards: the comment at
:1154-1157 says it relies on all `n` bytes being written even when the conversion
fails. This mirror keeps the stores made before each `goto Overflow`.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt

/-- "Store as many bytes as possible", longobject.c:1191-1200. `.error st` is the jump
to `Overflow` (:1193-1194) with the bytes stored so far in `st.out`. -/
def storeBytesW (n : Nat) : Nat → ABState → Except ABState ABState
  | 0, st => .ok st
  | fuel + 1, st =>
    if st.accumbits ≥ 8 then
      if st.out.length ≥ n then .error st
      else storeBytesW n fuel { st with out := st.out ++ [st.accum % 256],
                                        accumbits := st.accumbits - 8, accum := st.accum / 256 }
    else .ok st

/-- The digit loop, longobject.c:1164-1201: the two's complement step (:1166-1170), the
prepend into `accum` (:1174), the sign-bit count of the top digit (:1178-1189), then
the stores. -/
def asByteArrayLoopW (n : Nat) (twos : Bool) : List Nat → ABState → Except ABState ABState
  | [], st => .ok st
  | d :: ds, st =>
    let (d, carry) :=
      if twos then
        let t := (d ^^^ digitMask) + st.carry
        (t &&& digitMask, t >>> 30)
      else (d, st.carry)
    let accum := st.accum ||| (d <<< st.accumbits)
    let accumbits :=
      if ds = [] then st.accumbits + bitLength (if twos then d ^^^ digitMask else d)
      else st.accumbits + 30
    match storeBytesW n (accumbits + 1) ⟨st.out, accum, accumbits, carry⟩ with
    | .error st => .error st
    | .ok st => asByteArrayLoopW n twos ds st

/-- The return value and the bytes stored, in store order (from `bytes[0]` up for
little endian, from `bytes[n-1]` down for big endian); bytes not stored keep the
caller's contents. `ret` is `.ok ()` for 0, and `.error e` for -1, where `e` is the
exception set, `none` when `with_exceptions` is 0. -/
structure ABResult where
  ret : Except (Option PyExc) Unit
  stored : List Nat

/-- `_PyLong_AsByteArray`, longobject.c:1108-1254: the negative-unsigned refusal
(:1127-1134), the loop, the straggler (:1203-1218), the sign-bit test on an exactly
full buffer (:1219-1237), the sign fill (:1239-1244), and `Overflow` (:1248-1252). -/
def asByteArrayW (v : Long) (n : Nat) (signed withExc : Bool) : ABResult :=
  let exc (msg : String) : Option PyExc := if withExc then some (.overflowError msg) else none
  let overflow (out : List Nat) : ABResult := ⟨.error (exc "int too big to convert"), out⟩
  if v.neg ∧ ¬signed then ⟨.error (exc "can't convert negative int to unsigned"), []⟩
  else
    let twos := v.neg
    match asByteArrayLoopW n twos v.ds ⟨[], 0, 0, if twos then 1 else 0⟩ with
    | .error st => overflow st.out
    | .ok st =>
      let fill (out : List Nat) : ABResult :=
        ⟨.ok (), out ++ List.replicate (n - out.length) (if twos then 255 else 0)⟩
      if st.accumbits > 0 then
        if st.out.length ≥ n then overflow st.out
        else
          let accum := if twos then st.accum ||| (255 <<< st.accumbits) else st.accum
          fill (st.out ++ [accum % 256])
      else if st.out.length = n ∧ signed then
        let signBitSet := decide (n > 0 ∧ st.out.getLastD 0 ≥ 128)
        if signBitSet = twos then ⟨.ok (), st.out⟩ else overflow st.out
      else fill st.out

/-- Whenever `v >= 0` or the conversion is signed, `_PyLong_AsByteArray` stores exactly
`n` bytes holding `v mod 256**n` (two's complement), whether or not it succeeds, as
PyLong_AsNativeBytes relies on (comment at longobject.c:1154-1157); it returns 0
exactly when `v` fits; on failure it sets OverflowError only when `with_exceptions`.
A negative `v` with `is_signed = 0` stores nothing. Canonical objects are the type
invariant. -/
def AsByteArrayStores : Prop :=
  ∀ (v : Int) (n : Nat) (signed withExc : Bool),
    ((0 ≤ v ∨ signed = true) →
      (asByteArrayW (.ofInt v) n signed withExc).stored.length = n ∧
      (bytesVal (asByteArrayW (.ofInt v) n signed withExc).stored : Int) = v % 2 ^ (8 * n) ∧
      ((asByteArrayW (.ofInt v) n signed withExc).ret = .ok () ↔ FitsBytes v n signed) ∧
      (¬ FitsBytes v n signed → (asByteArrayW (.ofInt v) n signed withExc).ret =
        .error (if withExc then some (.overflowError "int too big to convert") else none))) ∧
    (v < 0 → signed = false →
      asByteArrayW (.ofInt v) n signed withExc = ⟨.error (if withExc then
        some (.overflowError "can't convert negative int to unsigned") else none), []⟩)

end PyLean.LongObj
