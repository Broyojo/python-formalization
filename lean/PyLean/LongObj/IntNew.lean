import PyLean.LongObj.Conv2

/-!
`int(...)` dispatch, `long_new_impl`, `long_subtype_new` and `long_vectorcall`, and the
`PyLong_FromNativeBytes` family.

The conversions the dispatch calls are parameters: `PyNumber_Long`, the string parsers and
`PyNumber_AsSsize_t` are generic, as AGENTS.md asks, so these statements hold for any
behaviour of those functions. The parsers themselves are modelled in `FromString.lean`.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt PyLean.Registry

/-- The argument `x` of `int(x, base)`, by the checks of longobject.c:5904-5913. -/
inductive IntArg (α : Type) where
  | str (s : α)
  | bytes (b : α)
  | other (o : α)

/-- The conversions `long_new_impl` delegates to. -/
structure IntOps (α : Type) where
  /-- `PyNumber_Long(x)`. -/
  numberLong : IntArg α → Py Int
  /-- `PyNumber_AsSsize_t(obase, NULL)`: clipped, so it never overflows. -/
  asSsize : α → Py Int
  /-- `PyLong_FromUnicodeObject(x, base)`. -/
  fromUnicode : α → Int → Py Int
  /-- `_PyLong_FromBytes(string, size, base)`. -/
  fromBytes : α → Int → Py Int

/-- `long_new_impl(type, x, obase)`, longobject.c:5876-5919, for `type == int`. -/
def longNew {α : Type} (ops : IntOps α) (x : Option (IntArg α)) (obase : Option α) : Py Int :=
  match x with
  | none =>
    match obase with
    | some _ => .error (.typeError "int() missing string argument")
    | none => .ok 0
  | some x =>
    match obase with
    | none => ops.numberLong x
    | some b =>
      match ops.asSsize b with
      | .error e => .error e
      | .ok base =>
        if (base ≠ 0 ∧ base < 2) ∨ base > 36 then
          .error (.valueError "int() base must be >= 2 and <= 36, or 0")
        else
          match x with
          | .str s => ops.fromUnicode s base
          | .bytes s => ops.fromBytes s base
          | .other _ => .error (.typeError "int() can't convert non-string with explicit base")

/-- `long_subtype_new(type, x, obase)`, longobject.c:5927-5955: the value of `int(...)`,
copied digit by digit into the subclass instance. `n == 0` becomes one digit of the
always-present `ob_digit[0]`. -/
def longSubtypeNew {α : Type} (ops : IntOps α) (x : Option (IntArg α)) (obase : Option α) : Py Int :=
  match longNew ops x obase with
  | .error e => .error e
  | .ok v =>
    let l := Long.ofInt v
    let n := max l.ds.length 1
    let copied : Long := ⟨l.neg, (l.ds ++ [0]).take n |>.take l.ds.length⟩
    .ok copied.toInt

/-- `long_vectorcall(type, args, nargsf, kwnames)`, longobject.c:6425-6445, without keywords. -/
def longVectorcall {α : Type} (ops : IntOps α) (args : List (IntArg α)) (base : IntArg α → α) :
    Py Int :=
  match args with
  | [] => .ok 0
  | [x] => ops.numberLong x
  | [x, b] => longNew ops (some x) (some (base b))
  | _ => .error (.typeError s!"int expected at most 2 arguments, got {args.length}")

/-- `_resolve_endianness(&endianness)`, longobject.c:1192-1201, on a little-endian build. -/
def resolveEndianness (flags : Int) : Bool :=
  if flags = -1 ∨ (flags.toNat &&& 2 ≠ 0) then true else flags.toNat &&& 1 = 1

/-- `PyLong_FromNativeBytes(buffer, n, flags)`, longobject.c:1389-1407. -/
def fromNativeBytes (bs : List Nat) (flags : Int) : Py Int :=
  fromBytes bs (if resolveEndianness flags then "little" else "big")
    (flags = -1 ∨ flags.toNat &&& 4 = 0)

/-- `PyLong_FromUnsignedNativeBytes(buffer, n, flags)`, longobject.c:1411-1424. -/
def fromUnsignedNativeBytes (bs : List Nat) (flags : Int) : Py Int :=
  fromBytes bs (if resolveEndianness flags then "little" else "big") false

/-- `PyLong_LAYOUT`, longobject.c:6755-6760, as `PyLong_GetNativeLayout` returns it:
`bits_per_digit`, `digit_size`, `digits_order`, `digit_endianness`. -/
def nativeLayout : Nat × Nat × Int × Int := (30, 4, -1, -1)

/-! ## Statements -/

/-- The dispatch of `int(...)`, for every behaviour of the conversions it calls: `int()`
is `0`, a base without a value is `TypeError`, a bad base is `ValueError` before the value
is looked at, and otherwise the value's type picks the parser. -/
def IntNewDispatch : Prop :=
  ∀ (α : Type) (ops : IntOps α),
    longNew ops none none = .ok 0 ∧
    (∀ b, longNew ops none (some b) = .error (.typeError "int() missing string argument")) ∧
    (∀ x, longNew ops (some x) none = ops.numberLong x) ∧
    (∀ x b base, ops.asSsize b = .ok base → ((base ≠ 0 ∧ base < 2) ∨ base > 36) →
      longNew ops (some x) (some b) =
        .error (.valueError "int() base must be >= 2 and <= 36, or 0")) ∧
    (∀ s b base, ops.asSsize b = .ok base → ¬ ((base ≠ 0 ∧ base < 2) ∨ base > 36) →
      longNew ops (some (.str s)) (some b) = ops.fromUnicode s base ∧
      longNew ops (some (.bytes s)) (some b) = ops.fromBytes s base ∧
      longNew ops (some (.other s)) (some b) =
        .error (.typeError "int() can't convert non-string with explicit base"))

theorem intNewDispatch_proven : IntNewDispatch := by
  intro α ops
  refine ⟨rfl, fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · intro x b base h1 h2
    simp only [longNew, h1, h2, ite_true]
  · intro s b base h1 h2
    simp only [longNew, h1, h2, ite_false, and_self]

/-- A subclass of `int` gets the digits and sign of `int(...)` unchanged. -/
def IntSubtypeSameValue : Prop :=
  ∀ (α : Type) (ops : IntOps α) (x : Option (IntArg α)) (b : Option α),
    longSubtypeNew ops x b = longNew ops x b

theorem intSubtypeSameValue_proven : IntSubtypeSameValue := by
  intro α ops x b
  unfold longSubtypeNew
  cases h : longNew ops x b with
  | error e => rfl
  | ok v =>
    simp only
    have hl : (((Long.ofInt v).ds ++ [0]).take (max (Long.ofInt v).ds.length 1)).take
        (Long.ofInt v).ds.length = (Long.ofInt v).ds := by
      rw [List.take_take]
      have : min (Long.ofInt v).ds.length (max (Long.ofInt v).ds.length 1)
          = (Long.ofInt v).ds.length := by omega
      rw [this]
      simp
    have e : (Long.mk (Long.ofInt v).neg (Long.ofInt v).ds).toInt = v := Long.toInt_ofInt v
    rw [hl, e]

/-- `int()` by vectorcall agrees with `long_new_impl`, for any conversions, and rejects a
third argument. -/
def IntVectorcallAgrees : Prop :=
  ∀ (α : Type) (ops : IntOps α) (base : IntArg α → α),
    longVectorcall ops [] base = longNew ops none none ∧
    (∀ x, longVectorcall ops [x] base = longNew ops (some x) none) ∧
    (∀ x b, longVectorcall ops [x, b] base = longNew ops (some x) (some (base b))) ∧
    (∀ x y z t, (longVectorcall ops (x :: y :: z :: t) base).raises "TypeError")

theorem intVectorcallAgrees_proven : IntVectorcallAgrees := by
  intro α ops base
  exact ⟨rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ _ _ => ⟨_, rfl, rfl⟩⟩

/-- `PyLong_FromNativeBytes`, on a little-endian build with native flags, is the signed
value of the bytes, and with `UNSIGNED_BUFFER` or through the unsigned entry the unsigned
value. `-1` selects native order and signed. -/
def FromNativeBytesExact : Prop :=
  ∀ bs : List Nat, AllBytes bs →
    fromNativeBytes bs (-1) = .ok (bytesSigned bs true) ∧
    fromNativeBytes bs 7 = .ok (bytesSigned bs false) ∧
    fromUnsignedNativeBytes bs (-1) = .ok (bytesSigned bs false)

theorem fromNativeBytesExact_proven : FromNativeBytesExact := by
  intro bs h
  have hl : resolveEndianness (-1) = true := rfl
  have hn : resolveEndianness 7 = true := by decide
  refine ⟨?_, ?_, ?_⟩
  · simp only [fromNativeBytes, hl, ite_true]
    have := fromBytesValue_proven bs "little" true h (Or.inl rfl)
    simpa [lsbOf] using this
  · simp only [fromNativeBytes, hn, ite_true]
    have := fromBytesValue_proven bs "little" false h (Or.inl rfl)
    have e : decide ((7 : Int) = -1 ∨ (7 : Int).toNat &&& 4 = 0) = false := by decide
    simpa [lsbOf, e] using this
  · simp only [fromUnsignedNativeBytes, hl, ite_true]
    have := fromBytesValue_proven bs "little" false h (Or.inl rfl)
    simpa [lsbOf] using this

def NativeLayoutExact : Prop := nativeLayout = (30, 4, -1, -1)

theorem nativeLayoutExact_proven : NativeLayoutExact := rfl

def entriesIntNew : List Entry := [
  { id := "longobj-int-new", pyFile := "Objects/longobject.c", pyFns := ["long_new_impl"]
    statement := "int() is 0; int(base=b) raises TypeError; a base outside {0} and 2..36 raises ValueError before the value is examined; otherwise the type of the value picks the parser, and a non-string raises TypeError."
    source := "int() docs; longobject.c:5883-5918", status := .proven
    prop := ``IntNewDispatch, thm := some ``intNewDispatch_proven
    notes := "Generic over PyNumber_Long, PyNumber_AsSsize_t and the parsers." },
  { id := "longobj-subtype-new", pyFile := "Objects/longobject.c", pyFns := ["long_subtype_new"]
    statement := "A subclass of int receives exactly the value of int(...)."
    source := "comment at longobject.c:5921-5925", status := .proven
    prop := ``IntSubtypeSameValue, thm := some ``intSubtypeSameValue_proven },
  { id := "longobj-vectorcall", pyFile := "Objects/longobject.c", pyFns := ["long_vectorcall"]
    statement := "int(...) through vectorcall agrees with long_new_impl for 0, 1 and 2 arguments and raises TypeError for more."
    source := "implementation twins", status := .proven
    prop := ``IntVectorcallAgrees, thm := some ``intVectorcallAgrees_proven },
  { id := "longobj-from-native-bytes", pyFile := "Objects/longobject.c"
    pyFns := ["PyLong_FromNativeBytes", "PyLong_FromUnsignedNativeBytes", "_resolve_endianness"]
    statement := "PyLong_FromNativeBytes is the signed value of the bytes with flags -1 and the unsigned value with UNSIGNED_BUFFER; PyLong_FromUnsignedNativeBytes is always unsigned."
    source := "C API docs: PyLong_FromNativeBytes", status := .proven
    prop := ``FromNativeBytesExact, thm := some ``fromNativeBytesExact_proven },
  { id := "longobj-native-layout", pyFile := "Objects/longobject.c", pyFns := ["PyLong_GetNativeLayout"]
    statement := "PyLong_GetNativeLayout describes 30-bit digits of 4 bytes, least significant first, little-endian."
    source := "C API docs: PyLong_GetNativeLayout", status := .proven
    prop := ``NativeLayoutExact, thm := some ``nativeLayoutExact_proven }
]

end PyLean.LongObj
