import PyLean.TextLibs.StructClose

/-!
What `_struct.c` does when a conversion fails or re-enters. An argument here is an object by what its
`__index__`, `__float__`, `__complex__` and `__bool__` do, and any of those can raise. Conversions
can also call `Struct.__init__`, which is the source of the refutations at the end.
-/

namespace PyLean.TextLibs.Struct

open PyLean PyLean.TextLibs

set_option linter.unusedSimpArgs false

/-! ### Integer conversions -/

/-- The routines that go through `get_pylong`. -/
def intRoutine : PFn → Bool
  | .npByte | .npUbyte | .npShort | .npUshort | .npInt | .npUint | .npLong | .npUlong | .npSsizeT
  | .npSizeT | .npLonglong | .npUlonglong | .npVoidP | .bpInt | .bpUint | .bpLonglong | .bpUlonglong
  | .lpInt | .lpUint | .lpLonglong | .lpUlonglong => true
  | _ => false

theorem getPylong_obj (o : PyO) (r : Py Int) (h : o.index = some r) : getPylong (.obj o) = r := by
  cases o with
  | mk index float cplx truth reinit =>
    simp only at h
    subst h
    rfl

/-- `get_pylong` for every object: the result of `__index__`, including what it raises, and
`struct.error` for an object without it. -/
def GetPylongLaw : Prop :=
  ∀ o : PyO,
    (∀ r, o.index = some r → getPylong (.obj o) = r) ∧
    (o.index = none → getPylong (.obj o) = .error (structErr "required argument is not an integer"))

theorem getPylongLaw_proven : GetPylongLaw := by
  intro o
  refine ⟨fun r h => getPylong_obj o r h, fun h => ?_⟩
  cases o with
  | mk index float cplx truth reinit =>
    simp only at h
    subst h
    rfl

/-- An exception from `__index__`, other than `OverflowError`, comes out of every integer format
unchanged: it is neither swallowed nor turned into `struct.error`. -/
def IndexRaises : Prop :=
  ∀ (f : FormatDef) (o : PyO) (e : PyExc), intRoutine f.pack = true → o.index = some (.error e) →
    (∀ m, e ≠ .overflowError m) → packCall f (.obj o) = .error e

theorem indexRaises_proven : IndexRaises := by
  intro f o e h1 h2 h3
  have hg : getPylong (.obj o) = .error e := getPylong_obj o _ h2
  have hr : ∀ (u : Bool) (x : Py Int), x = .error e → orRange f u x = .error e := by
    intro u x hx
    subst hx
    cases e with
    | overflowError m => exact absurd rfl (h3 m)
    | _ => rfl
  have hne : ∀ (P : PyExc → Py (List Nat)), (match (Except.error e : Py Int) with
      | .error (.overflowError _) => .error (structErr "x")
      | .error e => .error e
      | .ok _ => .ok [] : Py (List Nat)) = .error e := by
    intro _
    cases e with
    | overflowError m => exact absurd rfl (h3 m)
    | _ => rfl
  have hrun : runPack f (.obj o) = .error e := by
    cases hp : f.pack <;> simp only [intRoutine, hp, Bool.false_eq_true] at h1 <;>
      simp only [runPack, hp, packLonglongStd, packUlonglongStd, packIntStd, packUintStd, getLong,
        getUlong, getLonglong, getUlonglong, getSsizeT, getSizeT, hg, bind, Except.bind, hr _ _ rfl] <;>
      first
        | rfl
        | (cases e with
           | overflowError m => exact absurd rfl (h3 m)
           | _ => rfl)
  simp only [packCall, hrun]

/-- An `OverflowError` from `__index__`, like one from a large value, becomes the format's range
error under the formats that test for it. -/
def IndexOverflow : Prop :=
  ∀ (f : FormatDef) (o : PyO) (m : String),
    f.pack = .npInt → o.index = some (.error (.overflowError m)) →
    packCall f (.obj o) = .error (rangeError f false)

theorem indexOverflow_proven : IndexOverflow := by
  intro f o m h1 h2
  have hg : getPylong (.obj o) = .error (.overflowError m) := getPylong_obj o _ h2
  simp [packCall, runPack, h1, getLong, hg, orRange, bind, Except.bind]

/-! ### `?` -/

/-- A raising `__bool__` raises out of `?`, in both format tables, rather than counting as false. -/
def BoolRaises : Prop :=
  ∀ (o : PyO) (e : PyExc), o.truth = .error e →
    runPack ⟨'?', 1, 1, .nuBool, .npBool⟩ (.obj o) = .error e ∧
    runPack ⟨'?', 1, 0, .buBool, .bpBool⟩ (.obj o) = .error e

theorem boolRaises_proven : BoolRaises := by
  intro o e h
  have ht : isTrue (.obj o) = .error e := h
  simp [runPack, ht, bind, Except.bind]

/-! ### Floats and complex numbers -/

/-- The routines that go through `PyFloat_AsDouble`. -/
def floatRoutine : PFn → Bool
  | .npHalffloat | .npFloat | .npDouble | .bpHalffloat | .bpFloat | .bpDouble | .lpHalffloat
  | .lpFloat | .lpDouble => true
  | _ => false

theorem asDouble_raises (o : PyO) (e : PyExc) (h : o.float = some (.error e)) :
    asDouble (.obj o) = none := by
  simp [asDouble, h, okOf]

/-- The conversion order of `PyFloat_AsDouble`: `__float__` wins over `__index__`, and without
`__float__` the value of `__index__` is used. -/
def FloatOrder : Prop :=
  ∀ (o : PyO),
    (∀ x, o.float = some (.ok x) → asDouble (.obj o) = some x) ∧
    (∀ n, o.float = none → o.index = some (.ok n) → asDouble (.obj o) = intToDouble n) ∧
    (o.float = none → o.index = none → asDouble (.obj o) = none)

theorem floatOrder_proven : FloatOrder := by
  intro o
  refine ⟨fun x h => ?_, fun n h h2 => ?_, fun h h2 => ?_⟩ <;> simp [asDouble, h, okOf, *]

/-- Unlike `__index__`, a `__float__` that raises does not get through: the float routines replace
every failure of `PyFloat_AsDouble` with `struct.error`, whatever the exception was. -/
def FloatFailureReplaced : Prop :=
  ∀ (f : FormatDef) (o : PyO) (e : PyExc), floatRoutine f.pack = true → o.float = some (.error e) →
    runPack f (.obj o) = .error notFloat

theorem floatFailureReplaced_proven : FloatFailureReplaced := by
  intro f o e h1 h2
  have ha := asDouble_raises o e h2
  cases hp : f.pack <;> simp only [floatRoutine, hp, Bool.false_eq_true] at h1 <;>
    simp [runPack, hp, packHalffloat, packFloatStd, packDoubleStd, ha]

/-- `PyComplex_AsCComplex`: `__complex__` wins, and its failure is replaced by `struct.error`. Without
it the object is a real number through `PyFloat_AsDouble`, with imaginary part zero. -/
def ComplexOrder : Prop :=
  ∀ (o : PyO),
    (∀ z, o.cplx = some (.ok z) → asCComplex (.obj o) = some z) ∧
    (∀ e, o.cplx = some (.error e) → asCComplex (.obj o) = none) ∧
    (o.cplx = none → asCComplex (.obj o) = (asDouble (.obj o)).map (·, 0))

theorem complexOrder_proven : ComplexOrder := by
  intro o
  cases o with
  | mk index float cplx truth reinit =>
    refine ⟨fun z h => ?_, fun e h => ?_, fun h => ?_⟩
    · simp only at h
      subst h
      rfl
    · simp only at h
      subst h
      rfl
    · simp only at h
      subst h
      rfl

/-! ### Buffers and offsets -/

/-- The two buffer formats fail differently: `y*` lets an exception from `__buffer__` through, and the
`w*` of `pack_into` replaces it with `TypeError`, which also refuses `bytes`. -/
def BufferLaws : Prop :=
  ∀ (t : String) (e : PyExc) (b : List Nat),
    readBuf (.raises t e) = .error e ∧
    writeBuf (.raises t e) = .error (.typeError s!"argument must be read-write bytes-like object, not {t}") ∧
    writeBuf (.bytes b) = .error (.typeError "argument must be read-write bytes-like object, not bytes") ∧
    writeBuf (.bytearray b) = .ok b ∧ readBuf (.bytes b) = .ok b ∧ readBuf (.bytearray b) = .ok b

theorem bufferLaws_proven : BufferLaws := by
  intro t e b
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `s_pack_into` checks in the order of its body: the item count, then the buffer, then the offset.
So a bad buffer is reported even with a raising offset, and only then does `__index__` run. -/
def PackIntoOrder : Prop :=
  ∀ (s : SObj) (b : BufArg) (off : OffArg) (args : List SV),
    (args.length ≠ s.sLen → structPackIntoA s (.full b off args) =
      .error (structErr s!"pack_into expected {s.sLen} items for packing (got {args.length})")) ∧
    (args.length = s.sLen → ∀ e, writeBuf b = .error e → structPackIntoA s (.full b off args) = .error e) ∧
    (args.length = s.sLen → ∀ buf e, writeBuf b = .ok buf → offNumber off = .error e →
      structPackIntoA s (.full b off args) = .error e)

theorem packIntoOrder_proven : PackIntoOrder := by
  intro s b off args
  refine ⟨fun h => ?_, fun h e h2 => ?_, fun h buf e h2 h3 => ?_⟩
  · simp [structPackIntoA, h]
  · simp [structPackIntoA, h, h2, bind, Except.bind]
  · simp [structPackIntoA, h, h2, h3, bind, Except.bind]

/-- The same offset is reported differently by two functions: too large for `Py_ssize_t`, `pack_into`
raises `IndexError` and `unpack_from` raises `OverflowError`. An exception from `__index__` comes out
of both unchanged. -/
def OffsetLaws : Prop :=
  ∀ (e : PyExc) (t : String) (s : SObj) (b : List Nat) (args : List SV), args.length = s.sLen →
    offSsize (.index t (.error e) none) = .error e ∧
    offSsize (.int (2 ^ 63)) = .error (.overflowError "Python int too large to convert to C ssize_t") ∧
    structPackIntoA s (.full (.bytearray b) (.index t (.ok (2 ^ 63)) none) args) =
      .error (.indexError s!"cannot fit '{t}' into an index-sized integer") ∧
    structPackIntoA s (.full (.bytearray b) (.index t (.error e) none) args) = .error e

theorem offsetLaws_proven : OffsetLaws := by
  intro e t s b args h
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rfl
  · simp [structPackIntoA, h, writeBuf, offNumber, asSsizeIndex, longMin, longMax, OffArg.ty, bind,
      Except.bind]
  · simp [structPackIntoA, h, writeBuf, offNumber, bind, Except.bind]

/-- The module functions convert the format first, so a bad format is reported ahead of a bad buffer,
and otherwise they are the `Struct` methods. Both `pack` and `pack_into` need a format at all. -/
def ModuleOrder : Prop :=
  ∀ (f : FmtArg) (b : BufArg) (off : OffArg) (a : List SV) (p : PackIntoArgs),
    modPackA a none = .error (.typeError "missing format argument") ∧
    modPackIntoA p none = .error (.typeError "missing format argument") ∧
    (∀ e, cacheStruct f = .error e →
      modUnpackA f b = .error e ∧ modUnpackFromA f b off = .error e ∧ modIterUnpackA f b = .error e ∧
      modPackA a (some f) = .error e ∧ modPackIntoA p (some f) = .error e) ∧
    (∀ s, cacheStruct f = .ok s →
      modUnpackA f b = structUnpackA s b ∧ modUnpackFromA f b off = structUnpackFromA s b off ∧
      modIterUnpackA f b = structIterUnpackA s b ∧ modPackA a (some f) = structPack s a ∧
      modPackIntoA p (some f) = structPackIntoA s p)

theorem moduleOrder_proven : ModuleOrder := by
  intro f b off a p
  refine ⟨rfl, rfl, fun e h => ?_, fun s h => ?_⟩
  · simp [modUnpackA, modUnpackFromA, modIterUnpackA, modPackA, modPackIntoA, h, bind, Except.bind]
  · simp [modUnpackA, modUnpackFromA, modIterUnpackA, modPackA, modPackIntoA, h, bind, Except.bind]

/-- `Struct.unpack` raises what the buffer conversion raises, before it looks at the length. -/
def UnpackBufferFirst : Prop :=
  ∀ (s : SObj) (b : BufArg) (off : OffArg) (e : PyExc), readBuf b = .error e →
    structUnpackA s b = .error e ∧ structUnpackFromA s b off = .error e

theorem unpackBufferFirst_proven : UnpackBufferFirst := by
  intro s b off e h
  simp [structUnpackA, structUnpackFromA, h, bind, Except.bind]

/-- `iter_unpack` checks in the order of its body: a zero-sized format is refused before the buffer is
touched, then the buffer's own failure, and then its length. -/
def IterUnpackOrder : Prop :=
  ∀ (s : SObj) (b : BufArg),
    (s.sSize = 0 → structIterUnpackA s b =
      .error (structErr "cannot iteratively unpack with a struct of length 0")) ∧
    (s.sSize ≠ 0 → ∀ e, readBuf b = .error e → structIterUnpackA s b = .error e) ∧
    (s.sSize ≠ 0 → ∀ buf, readBuf b = .ok buf → buf.length % s.sSize ≠ 0 →
      structIterUnpackA s b = .error (structErr
        s!"iterative unpacking requires a buffer of a multiple of {s.sSize} bytes")) ∧
    (s.sSize ≠ 0 → ∀ buf, readBuf b = .ok buf → buf.length % s.sSize = 0 →
      structIterUnpackA s b = .ok { buf })

theorem iterUnpackOrder_proven : IterUnpackOrder := by
  intro s b
  refine ⟨fun h => ?_, fun h e h2 => ?_, fun h buf h2 h3 => ?_, fun h buf h2 h3 => ?_⟩
  · simp [structIterUnpackA, h]
  · simp [structIterUnpackA, h, h2]
  · simp only [structIterUnpackA]
    rw [if_neg h, h2]
    simp only [if_pos h3]
  · simp only [structIterUnpackA]
    rw [if_neg h, h2]
    simp [h3]

/-! ### The iterator object -/

/-- With the `Struct` left alone, driving the iterator object gives the tuples of the list model: the
read bound holds, because the buffer is a multiple of `s_size`. -/
def IterDriveAgrees : Prop :=
  ∀ (s : SObj) (buf : List Nat) (fuel index : Nat), 0 < s.sSize →
    (buf.length - index) % s.sSize = 0 → index ≤ buf.length →
    iterDrive s fuel { buf, index } = iterLoop s buf fuel index

theorem iterDriveAgrees_proven : IterDriveAgrees := by
  intro s buf fuel
  induction fuel with
  | zero => intro index _ _ _; rfl
  | succ f ih =>
    intro index h1 h2 h3
    by_cases he : index ≥ buf.length
    · simp [iterDrive, iterNextU, iterLoop, he]
    · have hlen : index < buf.length := by omega
      have hfit : ¬(index + s.sSize > buf.length) := by
        have hd := Nat.dvd_of_mod_eq_zero h2
        have := Nat.le_of_dvd (by omega) hd
        omega
      have hrest : (buf.length - (index + s.sSize)) % s.sSize = 0 := by
        obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h2
        cases k with
        | zero =>
          simp at hk
          omega
        | succ j =>
          rw [Nat.mul_succ] at hk
          have e1 : buf.length - (index + s.sSize) = s.sSize * j := by omega
          rw [e1]
          exact Nat.mul_mod_right _ _
      have hi := ih (index + s.sSize) h1 hrest (by omega)
      simp only [iterDrive, iterNextU, iterLoop, he, hfit, if_false, Bool.not_true,
        Bool.false_eq_true]
      cases hu : sUnpackInternal s (buf.drop index) with
      | error e => simp [hu, bind, Except.bind]
      | ok r =>
        simp only [hu, bind, Except.bind]
        rw [hi]

/-- The hint of the iterator object is the one of the list model, as long as `s_size` is not `0`. -/
def IterLenAgrees : Prop :=
  ∀ (s : SObj) (buf : List Nat) (index : Nat), 0 < s.sSize →
    iterLenU s { buf, index } = .ok (unpackiterLen s buf index)

theorem iterLenAgrees_proven : IterLenAgrees := by
  intro s buf index h
  have : s.sSize ≠ 0 := by omega
  simp [iterLenU, this, unpackiterLen]

/-! ### `Struct.__init__` from inside a method

`Struct.__init__` can be called again on a live object, from a conversion or between two calls. It
frees `s_codes` and changes `s_size` and `s_len`, and nothing in the C keeps a method or an iterator
from going on with them. Each statement below is the plain requirement that this cannot reach memory
it should not, and each is false. -/

/-- The object a format gives, for stating examples. -/
def sOf (f : FmtArg) : SObj :=
  match structInit f with
  | .ok s => s
  | .error _ => default

/-- A format does not change under `pack`: no conversion can free the codes being walked. -/
def PackNoUnsafe : Prop :=
  ∀ (f : FmtArg) (s : SObj) (args : List SV), structInit f = .ok s →
    structPack s args ≠ .error MEMORY

theorem packNoUnsafe_refuted : ¬PackNoUnsafe := by
  intro h
  exact h (.str [105]) (sOf (.str [105])) [.obj { index := some (.ok 1), reinit := true }]
    (by decide +kernel) (by decide +kernel)

/-- `pack_into` reads only the arguments it was given. -/
def PackIntoNoUnsafe : Prop :=
  ∀ (f g : FmtArg) (s t : SObj) (args : List SV) (buf : List Nat) (n : Int),
    structInit f = .ok s → structInit g = .ok t →
    structPackIntoA s (.full (.bytearray buf) (.index "O" (.ok n) (some t)) args) ≠ .error MEMORY

theorem packIntoNoUnsafe_refuted : ¬PackIntoNoUnsafe := by
  intro h
  exact h (.str [105]) (.str [105, 105]) (sOf (.str [105])) (sOf (.str [105, 105])) [.int 1]
    (List.replicate 8 0) 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- `iter_unpack` reads only the buffer it was given, whatever happens to the `Struct` after the
iterator is made. -/
def IterNoOverRead : Prop :=
  ∀ (f g : FmtArg) (s t : SObj) (b : List Nat) (it : UIter),
    structInit f = .ok s → structInit g = .ok t → structIterUnpackA s (.bytes b) = .ok it →
    (iterNextU t it).2 ≠ .error MEMORY

theorem iterNoOverRead_refuted : ¬IterNoOverRead := by
  intro h
  exact h (.str [98]) (.str [105]) (sOf (.str [98])) (sOf (.str [105])) [0, 0] { buf := [0, 0] }
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- `__length_hint__` does not divide by zero. -/
def IterLenNoCrash : Prop :=
  ∀ (f g : FmtArg) (s t : SObj) (b : List Nat) (it : UIter),
    structInit f = .ok s → structInit g = .ok t → structIterUnpackA s (.bytes b) = .ok it →
    iterLenU t it ≠ .error MEMORY

theorem iterLenNoCrash_refuted : ¬IterLenNoCrash := by
  intro h
  exact h (.str [98]) (.str [48, 115]) (sOf (.str [98])) (sOf (.str [48, 115])) [0, 0] { buf := [0, 0] }
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end PyLean.TextLibs.Struct
