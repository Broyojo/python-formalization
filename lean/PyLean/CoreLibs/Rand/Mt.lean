import PyLean.Core

/-!
Model of `Modules/_randommodule.c` (CPython 3.14.7): the Mersenne Twister core.

* `uint32_t` is Lean's `UInt32`, so `*`, `+`, `<<`, `-` wrap exactly as in C.
* `uint32_t state[N]` is an `Array UInt32`; `rd`/`wr` are C's `mt[i]` read and
  write. In C the array has exactly `N` slots. The model keeps that as the type
  invariant `State.WF`, and `rd`/`wr` are total so that the invariant can be a
  theorem (`genrand_wf`, `setstate` and the seeding lemmas) instead of an
  assumption.
* `int index` is a `Nat`: it starts at `0` or `N`, `setstate` rejects anything
  outside `[0, N]`, and `genrand_uint32` only adds one.
* CPython's bit layout is little-endian 32-bit words. The big-endian branches
  (`#if PY_BIG_ENDIAN`, :360-370, :537) compute the same integer on other hosts
  and are not modelled separately.
-/

namespace PyLean.CoreLibs.Rand

open PyLean

/-- `#define N 624`, _randommodule.c:90. -/
def N : Nat := 624
/-- `#define M 397`, _randommodule.c:91. -/
def MM : Nat := 397
/-- `#define MATRIX_A 0x9908b0dfU`, _randommodule.c:92. -/
def MATRIX_A : UInt32 := 0x9908b0df
/-- `#define UPPER_MASK 0x80000000U`, _randommodule.c:93. -/
def UPPER_MASK : UInt32 := 0x80000000
/-- `#define LOWER_MASK 0x7fffffffU`, _randommodule.c:94. -/
def LOWER_MASK : UInt32 := 0x7fffffff

/-- `RandomObject`, _randommodule.c:114-118 (without the object header). -/
structure State where
  mt : Array UInt32
  index : Nat
  deriving Inhabited, DecidableEq, Repr

/-- The type invariant of a live `RandomObject`: `N` words and `0 ≤ index ≤ N`. -/
def State.WF (s : State) : Prop := s.mt.size = N ∧ s.index ≤ N

/-- `mt[i]`. -/
@[inline] def rd (mt : Array UInt32) (i : Nat) : UInt32 := mt.getD i 0
/-- `mt[i] = v`. -/
@[inline] def wr (mt : Array UInt32) (i : Nat) (v : UInt32) : Array UInt32 := mt.setIfInBounds i v

/-- `mag01[y & 0x1U]`, _randommodule.c:138. -/
def mag01 (y : UInt32) : UInt32 := if y &&& 1 = 0 then 0 else MATRIX_A

/-- One twist assignment: `y = (mt[kk]&UPPER_MASK)|(mt[kk1]&LOWER_MASK);
mt[kk] = mt[kkm] ^ (y >> 1) ^ mag01[y & 0x1U];`, _randommodule.c:147-148, :151-152, :154-155. -/
@[inline] def twist (mt : Array UInt32) (kk kk1 kkm : Nat) : Array UInt32 :=
  let y := (rd mt kk &&& UPPER_MASK) ||| (rd mt kk1 &&& LOWER_MASK)
  wr mt kk (rd mt kkm ^^^ (y >>> 1) ^^^ mag01 y)

/-- `for (kk=0;kk<N-M;kk++)`, _randommodule.c:146-149. The first argument is the
number of iterations left. -/
def twistLow : Nat → Nat → Array UInt32 → Array UInt32
  | 0, _, mt => mt
  | n + 1, kk, mt => twistLow n (kk + 1) (twist mt kk (kk + 1) (kk + MM))

/-- `for (;kk<N-1;kk++)`, _randommodule.c:150-153; `kk+(M-N)` is computed in
`int`, and `kk ≥ N-M` keeps it non-negative. -/
def twistHigh : Nat → Nat → Array UInt32 → Array UInt32
  | 0, _, mt => mt
  | n + 1, kk, mt => twistHigh n (kk + 1) (twist mt kk (kk + 1) (kk + MM - N))

/-- The "generate N words at one time" block, _randommodule.c:144-155. -/
def regenerate (mt : Array UInt32) : Array UInt32 :=
  let mt := twistLow (N - MM) 0 mt
  let mt := twistHigh (N - 1 - (N - MM)) (N - MM) mt
  twist mt (N - 1) 0 (MM - 1)

/-- The tempering, _randommodule.c:161-164. -/
def temper (y : UInt32) : UInt32 :=
  let y := y ^^^ (y >>> 11)
  let y := y ^^^ ((y <<< 7) &&& 0x9d2c5680)
  let y := y ^^^ ((y <<< 15) &&& 0xefc60000)
  y ^^^ (y >>> 18)

/-- `genrand_uint32`, _randommodule.c:134-166. -/
def genrand (self : State) : UInt32 × State :=
  let self := if self.index ≥ N then { mt := regenerate self.mt, index := 0 } else self
  (temper (rd self.mt self.index), { self with index := self.index + 1 })

/-- `genrand_uint32` called `n` times, dropping the words: the state after
exactly `n` words. This is the measure of "how much of the stream was used". -/
def advance : Nat → State → State
  | 0, s => s
  | n + 1, s => advance n (genrand s).2

/-- The successive words of `genrand_uint32`. -/
def stream : Nat → State → List UInt32
  | 0, _ => []
  | n + 1, s => (genrand s).1 :: stream n (genrand s).2

/-- The numerator pair `a, b` of `_random_Random_random_impl`,
_randommodule.c:191: `a=genrand_uint32(self)>>5, b=genrand_uint32(self)>>6`,
with `a` drawn first. -/
def randomParts (s : State) : (Nat × Nat) × State :=
  let (w1, s) := genrand s
  let (w2, s) := genrand s
  (((w1 >>> 5).toNat, (w2 >>> 6).toNat), s)

/-- The exact numerator of `random()`: `a*67108864.0+b`, _randommodule.c:192. It
is below `2**53`, so the double in C holds it exactly, and multiplying by
`1.0/9007199254740992.0` only changes the exponent. -/
def randomNum (s : State) : Nat × State :=
  let ((a, b), s) := randomParts s
  (a * 67108864 + b, s)

/-- `random()` as an exact rational: `(a*67108864+b)/2**53`. -/
def randomRat (s : State) : Rat × State :=
  let (m, s) := randomNum s
  ((m : Rat) / (9007199254740992 : Rat), s)

/-- `for (mti=1; mti<N; mti++) mt[mti] = (1812433253U * (mt[mti-1] ^ (mt[mti-1] >> 30)) + mti);`,
_randommodule.c:204-211. -/
def initLoop : Nat → Nat → Array UInt32 → Array UInt32
  | 0, _, mt => mt
  | n + 1, mti, mt =>
    let p := rd mt (mti - 1)
    initLoop n (mti + 1) (wr mt mti ((1812433253 : UInt32) * (p ^^^ (p >>> 30)) + mti.toUInt32))

/-- `init_genrand`, _randommodule.c:196-214. -/
def initGenrand (self : State) (s : UInt32) : State :=
  { mt := initLoop (N - 1) 1 (wr self.mt 0 s), index := N }

/-- The first loop of `init_by_array`, _randommodule.c:229-235. Arguments:
`k` (counts down), `i`, `j`, `mt`. The result carries the final `i`, which the
second loop continues from. `key` has `key_length ≥ 1` entries. -/
def byArrayKey (key : Array UInt32) : Nat → Nat → Nat → Array UInt32 → Nat × Array UInt32
  | 0, i, _, mt => (i, mt)
  | k + 1, i, j, mt =>
    let p := rd mt (i - 1)
    let mt := wr mt i ((rd mt i ^^^ ((p ^^^ (p >>> 30)) * 1664525)) + rd key j + j.toUInt32)
    let i := i + 1
    let j := j + 1
    let (mt, i) := if i ≥ N then (wr mt 0 (rd mt (N - 1)), 1) else (mt, i)
    let j := if j ≥ key.size then 0 else j
    byArrayKey key k i j mt

/-- The second loop of `init_by_array`, _randommodule.c:236-241. -/
def byArrayMix : Nat → Nat → Array UInt32 → Array UInt32
  | 0, _, mt => mt
  | k + 1, i, mt =>
    let p := rd mt (i - 1)
    let mt := wr mt i ((rd mt i ^^^ ((p ^^^ (p >>> 30)) * 1566083941)) - i.toUInt32)
    let i := i + 1
    let (mt, i) := if i ≥ N then (wr mt 0 (rd mt (N - 1)), 1) else (mt, i)
    byArrayMix k i mt

/-- `init_by_array`, _randommodule.c:219-244. -/
def initByArray (self : State) (key : Array UInt32) : State :=
  let self := initGenrand self 19650218
  let r := byArrayKey key (if N > key.size then N else key.size) 1 0 self.mt
  let mt := byArrayMix (N - 1) r.1 r.2
  { self with mt := wr mt 0 0x80000000 }

/-- The state of a new instance: `tp_new` is `PyType_GenericNew`
(_randommodule.c:584), so the object comes from `PyType_GenericAlloc`, which
zero-fills it. Only `tp_init` seeds. -/
def genericNew : State := { mt := Array.replicate N 0, index := 0 }

/-! ### Seeding, _randommodule.c:251-379 -/

/-- What `random_seed` reads from the operating system: the
`_PyOS_URandomNonblock` key (`none` when it fails), and the `PyTime_Time`,
`getpid`, `PyTime_Monotonic` values for the fallback. -/
structure Entropy where
  urandom : Option (Array UInt32)
  now : Py Int
  pid : UInt32
  monotonic : Py Int

/-- `random_seed_urandom`, _randommodule.c:251-261. `none` is the `-1` return. -/
def randomSeedUrandom (self : State) (ent : Entropy) : Option State :=
  ent.urandom.map (initByArray self)

/-- `key[0] = (uint32_t)(now & 0xffffffffU); key[1] = (uint32_t)(now >> 32);`,
_randommodule.c:272-273 and :286-287. `>>` on the signed `PyTime_t` is an
arithmetic shift, which `Int` division by `2^32` matches. -/
def timeWords (now : Int) : UInt32 × UInt32 :=
  ((now % (2 ^ 32)).toNat.toUInt32, ((now / (2 ^ 32)) % (2 ^ 32)).toNat.toUInt32)

/-- `random_seed_time_pid`, _randommodule.c:263-291, `getpid` branch. -/
def randomSeedTimePid (self : State) (ent : Entropy) : Py State := do
  let now ← ent.now
  let (k0, k1) := timeWords now
  let mono ← ent.monotonic
  let (k3, k4) := timeWords mono
  return initByArray self #[k0, k1, ent.pid, k3, k4]

/-- The Python object `random_seed` receives. -/
inductive CArg where
  /-- `arg == NULL`: `Random()` with no argument. -/
  | null
  | none
  /-- `PyLong_CheckExact(arg)`. -/
  | exactInt (n : Int)
  /-- `PyLong_Check(arg)` on a strict subclass (includes `bool`). -/
  | intSubclass (n : Int)
  /-- Any other object, whose `hash()` is `h`. `PyObject_Hash` never returns
  `-1` without an exception, and `Py_hash_t` is signed 64-bit. -/
  | hashable (h : Int)
  /-- `PyObject_Hash` raises: `-1` with an exception. -/
  | unhashable (tyName : String)
  deriving Repr, DecidableEq

/-- `keyused = bits == 0 ? 1 : (size_t)((bits - 1) / 32 + 1);`, _randommodule.c:343. -/
def keyUsed (bits : Nat) : Nat := if bits = 0 then 1 else (bits - 1) / 32 + 1

/-- `_PyLong_AsByteArray(n, key, keyused * 4, little, unsigned)`,
_randommodule.c:351-355, read back as native `uint32_t`s: the words of `n`,
least significant first. `keyused` words are always enough, so the overflow
branch (`res == -1`) is unreachable (`keyWords_reassemble`). -/
def keyWords (n used : Nat) : Array UInt32 :=
  (Array.range used).map fun i => (n >>> (32 * i)).toUInt32

/-- The non-`None` part of `random_seed`: `n`, the unsigned value to split,
_randommodule.c:316-333. -/
def seedValue : CArg → Py Nat
  | .null | .none => .ok 0  -- not reached: handled by the caller at :303
  | .exactInt n | .intSubclass n => .ok n.natAbs
  | .hashable h => .ok (h % (2 ^ 64)).toNat
  | .unhashable ty => .error (.typeError s!"unhashable type: '{ty}'")

/-- `random_seed`, _randommodule.c:293-379. On an error `self` is untouched,
because the state is only written by `init_by_array`. -/
def randomSeed (self : State) (arg : CArg) (ent : Entropy) : Py State :=
  match arg with
  | .null | .none =>
    match randomSeedUrandom self ent with
    | some s => .ok s
    | none => randomSeedTimePid self ent
  | _ => do
    let n ← seedValue arg
    let bits := bitLength n
    let keyused := keyUsed bits
    return initByArray self (keyWords n keyused)

/-- `random_init_impl`, _randommodule.c:561-566, the `tp_init` of `_random.Random`
(which `Random.__init__` shadows): `tp_new` then `random_seed`. -/
def cInit (arg : CArg) (ent : Entropy) : Py State := randomSeed genericNew arg ent

/-- `_random_Random_seed_impl`, _randommodule.c:395-403. -/
def cSeedMethod (self : State) (n : CArg) (ent : Entropy) : Py State := randomSeed self n ent

/-! ### `getstate`, `setstate`, _randommodule.c:414-493 -/

/-- `_random_Random_getstate_impl`, _randommodule.c:414-440: the 625-tuple. -/
def cGetstate (self : State) : List Int :=
  (List.range N).map (fun i => ((rd self.mt i).toNat : Int)) ++ [(self.index : Int)]

/-- An element of the tuple handed to `setstate`. -/
inductive Elem where
  | int (n : Int)
  /-- A non-`int` object with this type name. -/
  | other (tyName : String)
  deriving Repr, DecidableEq, Inhabited

/-- `PyLong_AsUnsignedLong`, Objects/longobject.c: no `__index__`, 64-bit
`unsigned long`. -/
def asUnsignedLong : Elem → Py Nat
  | .other _ => .error (.typeError "an integer is required")
  | .int n =>
    if n < 0 then .error (.overflowError "can't convert negative value to unsigned int")
    else if n ≥ 2 ^ 64 then .error (.overflowError "Python int too large to convert to C unsigned long")
    else .ok n.toNat

/-- `PyLong_AsLong`, Objects/longobject.c: calls `__index__`, 64-bit `long`. -/
def asLong : Elem → Py Int
  | .other ty => .error (.typeError s!"'{ty}' object cannot be interpreted as an integer")
  | .int n =>
    if n < -(2 ^ 63) ∨ n ≥ 2 ^ 63 then .error (.overflowError "Python int too large to convert to C long")
    else .ok n

/-- The conversion loop `for (i=0; i<N ; i++)`, _randommodule.c:474-479:
`new_state[i] = (uint32_t)element;` truncates silently. -/
def convertWords : List Elem → Py (List UInt32)
  | [] => .ok []
  | e :: es => do
    let w ← asUnsignedLong e
    let rest ← convertWords es
    return w.toUInt32 :: rest

/-- The argument of `_random.Random.setstate`. -/
inductive CStateArg where
  | tuple (xs : List Elem)
  | notTuple
  deriving Repr, DecidableEq

/-- `_random_Random_setstate_impl`, _randommodule.c:454-493. All checks come
before the first write (:488), so on an error `self` keeps its state, and on
success the old state does not matter: the result is the new `State`. -/
def cSetstate (state : CStateArg) : Py State :=
  match state with
  | .notTuple => .error (.typeError "state vector must be a tuple")
  | .tuple xs =>
    if xs.length ≠ N + 1 then .error (.valueError "state vector is the wrong size")
    else do
      let new_state ← convertWords (xs.take N)
      let index ← asLong (xs.getD N (.int 0))
      if index < 0 ∨ index > (N : Int) then .error (.valueError "invalid state")
      else
        -- :488-490: `self->index = (int)index;` then the word copy loop.
        return { mt := new_state.toArray, index := index.toNat }

/-! ### `getrandbits`, _randommodule.c:506-550 -/

/-- `_PyLong_UInt64_Converter`, Objects/longobject.c:1737-1755 and :1765, the
clinic `uint64` converter (Modules/clinic/_randommodule.c.h:136). -/
inductive IntArg where
  | int (n : Int)
  /-- `True`/`False`. -/
  | bool (b : Bool)
  /-- A non-`int`, non-`__index__` object with this type name. -/
  | other (tyName : String)
  deriving Repr, DecidableEq, Inhabited

/-- `operator.index(x)`. -/
def IntArg.index : IntArg → Py Int
  | .int n => .ok n
  | .bool b => .ok (if b then 1 else 0)
  | .other ty => .error (.typeError s!"'{ty}' object cannot be interpreted as an integer")

/-- `_PyLong_UInt64_Converter`. -/
def uint64Converter (x : IntArg) : Py Nat := do
  let n ← x.index
  if n < 0 then .error (.valueError "Cannot convert negative int")
  else if n ≥ 2 ^ 64 then .error (.overflowError "Python int too large for C uint64_t")
  else .ok n.toNat

/-- `PY_SSIZE_T_MAX / 4u`, _randommodule.c:521. -/
def maxWords : Nat := (2 ^ 63 - 1) / 4

/-- The fill loop, _randommodule.c:535-544, on a little-endian host. The first
argument is the words left (`i < words`); `k` is the bits left. The word for
which `k < 32` is the last one, so the wrap of the `uint64_t` `k -= 32` is never
observed. -/
def fillWords : Nat → Nat → State → List UInt32 × State
  | 0, _, s => ([], s)
  | w + 1, k, s =>
    let (r, s) := genrand s
    let r := if k < 32 then r >>> (32 - k).toUInt32 else r
    let (rest, s) := fillWords w (k - 32) s
    (r :: rest, s)

/-- `_PyLong_FromByteArray(wordarray, words * 4, little, unsigned)`,
_randommodule.c:546-547. -/
def wordsToNat : List UInt32 → Nat
  | [] => 0
  | w :: ws => w.toNat + 2 ^ 32 * wordsToNat ws

/-- `_random_Random_getrandbits_impl`, _randommodule.c:506-550. `mallocOk n` is
whether `PyMem_Malloc(n)` succeeds. The word-count check at :521 cannot fire on a
64-bit build (`uint64_t` gives at most `2**59` words), but it stays in the
mirror. -/
def getrandbitsImpl (mallocOk : Nat → Bool) (k : Nat) (self : State) : Py Nat × State :=
  if k = 0 then (.ok 0, self)
  else if k ≤ 32 then
    let (w, s) := genrand self
    (.ok (w >>> (32 - k).toUInt32).toNat, s)
  else if (k - 1) / 32 + 1 > maxWords then (.error (.named "MemoryError" ""), self)
  else
    let words := (k - 1) / 32 + 1
    if !mallocOk (words * 4) then (.error (.named "MemoryError" ""), self)
    else
      let r := fillWords words k self
      (.ok (wordsToNat r.1), r.2)

end PyLean.CoreLibs.Rand
