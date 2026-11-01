import PyLean.CoreLibs.Rand.Exact
import PyLean.CoreLibs.Rand.Sha512

/-!
The stateful part of `class Random` in `Lib/random.py` (CPython 3.14.7): `__init__`,
`seed`, `getstate`, `setstate` and pickling, on top of the C model in `Mt.lean`.
-/

namespace PyLean.CoreLibs.Rand

open PyLean Flt

variable {F : Type}

/-- A `Random` instance: the C state plus the attribute `gauss_next`
(a float or `None`). -/
structure Obj (F : Type) where
  core : State
  gaussNext : Option F
  deriving Inhabited

/-- `Random` as a `Gen`: `_random_Random_random_impl` (_randommodule.c:187-193) and
`_random_Random_getrandbits` (clinic converter, then
`_random_Random_getrandbits_impl`). `mallocOk` is the allocator. -/
def mtGen [Flt F] (mallocOk : Nat → Bool) : Gen State F where
  random s :=
    let ((a, b), s) := randomParts s
    let ofN (n : Nat) : F := (Flt.ofInt (n : Int)).getD default
    ((ofN a * 67108864.0 + ofN b) * (1.0 / 9007199254740992.0), s)
  getrandbits x s :=
    match uint64Converter x with
    | .error e => (.error e, s)
    | .ok k => getrandbitsImpl mallocOk k s

/-- The object passed to `Random.seed`. `h` is its `hash()`, which is randomized
for `str` and `bytes`, so it is data here. -/
inductive SeedArg where
  | none
  | int (n : Int)
  /-- `bool` or another `int` subclass. -/
  | intSub (n : Int)
  | float (h : Int)
  /-- Code points; Python strings may hold lone surrogates. -/
  | str (cps : List Nat) (h : Int)
  | bytes (b : List Nat) (h : Int)
  | bytearray (b : List Nat)
  /-- Any other type. -/
  | other
  deriving Repr, DecidableEq

/-- One step of the version 1 loop, Lib/random.py:150. -/
def seedV1Step (x c : Nat) : Nat := ((1000003 * x) ^^^ c) &&& 0xFFFFFFFFFFFFFFFF

/-- `x = ord(a[0]) << 7 if a else 0`, Lib/random.py:148. -/
def seedV1Init : List Nat → Nat
  | [] => 0
  | c :: _ => c <<< 7

/-- The version 1 string hash, Lib/random.py:148-152. `x` stays non-negative, so
the `-2 if x == -1` of :152 (kept from the signed C hash of Python 2) cannot fire. -/
def seedV1 (cps : List Nat) : Int :=
  let x := seedV1Init cps
  let x := cps.foldl seedV1Step x
  let x := x ^^^ cps.length
  if (x : Int) = -1 then -2 else (x : Int)

/-- `s.encode()`: strict UTF-8, Objects/unicodeobject.c. A lone surrogate raises
`UnicodeEncodeError`. -/
def utf8Encode : List Nat → Py (List Nat)
  | [] => .ok []
  | c :: cs => do
    let b : List Nat ←
      if c < 0x80 then .ok [c]
      else if c < 0x800 then .ok [0xC0 + c / 64, 0x80 + c % 64]
      else if 0xD800 ≤ c ∧ c ≤ 0xDFFF then .error (.named "UnicodeEncodeError" "~surrogate")
      else if c < 0x10000 then .ok [0xE0 + c / 4096, 0x80 + (c / 64) % 64, 0x80 + c % 64]
      else .ok [0xF0 + c / 262144, 0x80 + (c / 4096) % 64, 0x80 + (c / 64) % 64, 0x80 + c % 64]
    let rest ← utf8Encode cs
    return b ++ rest

/-- `int.from_bytes(b)` (big-endian, the default). -/
def fromBytesBE (b : List Nat) : Nat := b.foldl (fun acc x => acc * 256 + x) 0

/-- `int.from_bytes(a + _sha512(a).digest())`, Lib/random.py:167. -/
def seedV2 (b : List Nat) : Int := fromBytesBE (b ++ Sha512.digest b)

/-- The object `super().seed(a)` receives, Lib/random.py:146-173. -/
def seedConvert (a : SeedArg) (version : Int) : Py CArg :=
  match a with
  | .str cps h =>
    if version = 1 then .ok (.exactInt (seedV1 cps))
    else if version = 2 then do
      let b ← utf8Encode cps
      return .exactInt (seedV2 b)
    else .ok (.hashable h)
  | .bytes b h =>
    if version = 1 then .ok (.exactInt (seedV1 b))
    else if version = 2 then .ok (.exactInt (seedV2 b))
    else .ok (.hashable h)
  | .bytearray b =>
    if version = 2 then .ok (.exactInt (seedV2 b)) else .ok (.unhashable "bytearray")
  | .other =>
    .error (.typeError "The only supported seed types are:\nNone, int, float, str, bytes, and bytearray.")
  | .none => .ok .none
  | .int n => .ok (.exactInt n)
  | .intSub n => .ok (.intSubclass n)
  | .float h => .ok (.hashable h)

/-- `Random.seed`, Lib/random.py:128-174. Nothing is written when an exception
is raised: `super().seed(a)` is the first write and it is all-or-nothing. -/
def pySeed (ent : Entropy) (a : SeedArg) (version : Int) (o : Obj F) : Py Unit × Obj F :=
  match seedConvert a version with
  | .error e => (.error e, o)
  | .ok arg =>
    match randomSeed o.core arg ent with
    | .error e => (.error e, o)
    | .ok s => (.ok (), { core := s, gaussNext := none })

/-- `Random.__init__`, Lib/random.py:119-126, on the object from `tp_new`:
`self.seed(x); self.gauss_next = None`. -/
def pyInit (ent : Entropy) (x : SeedArg) : Py (Obj F) :=
  match pySeed ent x 2 ({ core := genericNew, gaussNext := none } : Obj F) with
  | (.error e, _) => .error e
  | (.ok (), o) => .ok { o with gaussNext := none }

/-- The tuple `Random.getstate` returns, Lib/random.py:176-178. `VERSION = 3`, :117. -/
structure PyState (F : Type) where
  version : Int
  internal : List Int
  gaussNext : Option F
  deriving Inhabited

/-- `Random.getstate`, Lib/random.py:176-178. -/
def pyGetstate (o : Obj F) : PyState F :=
  { version := 3, internal := cGetstate o.core, gaussNext := o.gaussNext }

/-- A value compared with `3` and `2` and formatted with `%s`. -/
structure VersionV where
  /-- The integer it equals, if any: `3`, `3.0` and `True` (`1`) are all numbers. -/
  value : Option Int
  /-- `str(version)`. -/
  text : String
  deriving Repr, DecidableEq, Inhabited

/-- The second item of the state. -/
inductive InternalArg where
  | tuple (xs : List Elem)
  | list (xs : List Elem)
  | notIterable (tyName : String)
  deriving Repr, DecidableEq

/-- The argument of `Random.setstate`. -/
inductive SetArg (F : Type) where
  /-- Not subscriptable. -/
  | notSubscriptable (tyName : String)
  /-- The empty tuple or list. -/
  | empty (isList : Bool)
  /-- A tuple or list of `len ≥ 1` items: `version` first, and when `len = 3` the
  `internal` state and `gauss_next`. -/
  | seq (len : Nat) (version : VersionV) (internal : InternalArg) (gauss : Option F)

/-- `x % (2 ** 32)` on an element of a version 2 state, Lib/random.py:193. A float
stays a float (and the C code then rejects it). `None` has no `%`. Any other
object here stands for one whose `__mod__` raises `ValueError`. -/
def modElem : Elem → Py Elem
  | .int n => .ok (.int (n % (2 ^ 32)))
  | .other ty =>
    if ty = "float" then .ok (.other "float")
    else if ty = "NoneType" then
      .error (.typeError "unsupported operand type(s) for %: 'NoneType' and 'int'")
    else .error (.typeError "")

/-- `tuple(x % (2 ** 32) for x in internalstate)` with its `except ValueError`,
Lib/random.py:192-195. -/
def modElems : List Elem → Py (List Elem)
  | [] => .ok []
  | e :: es => do
    let x ← modElem e
    let rest ← modElems es
    return x :: rest

/-- The `super().setstate(internalstate)` of `Random.setstate`: a failure leaves
the C state alone. -/
def applyC (st : CStateArg) (o : Obj F) : Py Unit × Obj F :=
  match cSetstate st with
  | .error e => (.error e, o)
  | .ok s => (.ok (), { o with core := s })

/-- `version, internalstate, self.gauss_next = state`, Lib/random.py:184 and :187.
The message is `unpack_iterable`'s, Python/ceval.c. -/
def unpackError (len : Nat) : PyExc :=
  if len < 3 then .valueError s!"not enough values to unpack (expected 3, got {len})"
  else .valueError s!"too many values to unpack (expected 3, got {len})"

/-- `Random.setstate`, Lib/random.py:180-200. The tuple unpacking at :184 and :187
assigns `self.gauss_next` before the C call that can still fail, so a rejected
state replaces `gauss_next`. -/
def pySetstate (state : SetArg F) (o : Obj F) : Py Unit × Obj F :=
  match state with
  | .notSubscriptable ty => (.error (.typeError s!"'{ty}' object is not subscriptable"), o)
  | .empty isList =>
    (.error (.indexError (if isList then "list index out of range" else "tuple index out of range")), o)
  | .seq len version internal gauss =>
    match version.value with
    | some 3 =>
      if len ≠ 3 then (.error (unpackError len), o)
      else
        let o := { o with gaussNext := gauss }
        match internal with
        | .tuple xs => applyC (.tuple xs) o
        | _ => applyC .notTuple o
    | some 2 =>
      if len ≠ 3 then (.error (unpackError len), o)
      else
        let o := { o with gaussNext := gauss }
        match internal with
        | .notIterable ty => (.error (.typeError s!"'{ty}' object is not iterable"), o)
        | .tuple xs | .list xs =>
          match modElems xs with
          | .error e => (.error e, o)
          | .ok ys => applyC (.tuple ys) o
    | _ =>
      (.error (.valueError s!"state with version {version.text} passed to Random.setstate() of version 3"), o)

/-- A `PyState` as an argument of `setstate`. -/
def PyState.toArg (st : PyState F) : SetArg F :=
  .seq 3 { value := some st.version, text := toString st.version }
    (.tuple (st.internal.map .int)) st.gaussNext

/-- `Random.__getstate__`, Lib/random.py:213-214. -/
def pyDunderGetstate (o : Obj F) : PyState F := pyGetstate o

/-- `Random.__setstate__`, Lib/random.py:216-217. -/
def pyDunderSetstate (state : SetArg F) (o : Obj F) : Py Unit × Obj F := pySetstate state o

/-- `Random.__reduce__`, Lib/random.py:219-220: `self.__class__, (), self.getstate()`.
The class and the empty tuple are constants, so only the state is data. -/
def pyReduce (o : Obj F) : PyState F := pyGetstate o

/-- Unpickling: `cls()` builds an instance with fresh entropy `ent`, and
`obj.__setstate__(state)` overwrites it. -/
def pyUnpickle (ent : Entropy) (state : PyState F) : Py (Obj F) := do
  let o ← pyInit ent .none
  match pyDunderSetstate state.toArg o with
  | (.error e, _) => .error e
  | (.ok (), o) => return o

end PyLean.CoreLibs.Rand
