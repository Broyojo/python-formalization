import PyLean.CoreLibs.Rand.Seed
import PyLean.CoreLibs.Rand.Dist

/-!
`SystemRandom`, `Random.__init_subclass__` and the command-line `main` of
`Lib/random.py` (CPython 3.14.7).

`SystemRandom` draws from `os.urandom`. The bytes come from the operating system,
so they are an abstract function `raw` with the contract `len(os.urandom(n)) == n`.
Everything around them is modelled.
-/

namespace PyLean.CoreLibs.Rand

open PyLean RM Flt

variable {σ F : Type}

/-! ### `SystemRandom`, Lib/random.py:897-931 -/

/-- `os.urandom(size)`, Modules/posixmodule.c: the `Py_ssize_t` clinic conversion,
the negative-size check, then the operating system. -/
def osUrandom (raw : Nat → RM σ (List Nat)) (size : IntArg) : RM σ (List Nat) := do
  let n ← lift size.index
  if n > ssizeMax ∨ n < ssizeMin then
    raise (.overflowError "Python int too large to convert to C ssize_t")
  else if n < 0 then raise (.valueError "size cannot be negative")
  else raw n.toNat

/-- The contract of `os.urandom`: exactly `n` bytes. -/
def RawValid (raw : Nat → RM σ (List Nat)) : Prop :=
  ∀ n s r s', raw n s = (.ok r, s') → r.length = n ∧ ∀ b ∈ r, b < 256

/-- The numerator of `SystemRandom.random`: `int.from_bytes(_urandom(7)) >> 3`,
Lib/random.py:908. -/
def sysRandomNum (raw : Nat → RM σ (List Nat)) : RM σ Nat := do
  let b ← osUrandom raw (.int 7)
  return fromBytesBE b >>> 3

/-- `SystemRandom.random`, Lib/random.py:906-908. `RECIP_BPF = 2 ** -BPF`, :98. -/
def sysRandom [Flt F] (raw : Nat → RM σ (List Nat)) : RM σ F := do
  let m ← sysRandomNum raw
  let x : F ← lift (pyFloat (m : Int))
  return x * 1.1102230246251565e-16

/-- `SystemRandom.getrandbits`, Lib/random.py:910-916. For `k` that is not an `int`,
`k < 0` is the first failure (`None`, `str`), and a non-negative float fails at
`_urandom`, because `(k + 7) // 8` is still a float. -/
def sysGetrandbits (raw : Nat → RM σ (List Nat)) (k : IntArg) : RM σ Nat := do
  match k with
  | .other ty =>
    if ty = "float" then raise (.typeError "'float' object cannot be interpreted as an integer")
    else raise (.typeError s!"'<' not supported between instances of '{ty}' and 'int'")
  | _ =>
    let k ← lift k.index
    if k < 0 then raise (.valueError "number of bits must be non-negative")
    else
      let numbytes := (k + 7) / 8
      let b ← osUrandom raw (.int numbytes)
      let x := fromBytesBE b
      return x >>> (numbytes * 8 - k).toNat

/-- `SystemRandom.randbytes`, Lib/random.py:918-922. -/
def sysRandbytes (raw : Nat → RM σ (List Nat)) (n : IntArg) : RM σ (List Nat) := osUrandom raw n

/-- `SystemRandom.seed`, Lib/random.py:924-926: a stub, whatever the arguments. -/
def sysSeed {β : Type} (_args : β) : RM σ Unit := pure ()

/-- `SystemRandom._notimplemented`, Lib/random.py:928-931, which is also
`getstate` and `setstate`. -/
def sysNotImplemented {β α : Type} (_args : β) : RM σ α :=
  raise (.named "NotImplementedError" "System entropy source does not have state.")

/-- `SystemRandom` as a `Gen`. `os.urandom(7)` failing inside `random()` (no entropy
source at all) is a platform condition, so `random` falls back to `default` there. -/
def sysGen [Flt F] (raw : Nat → RM σ (List Nat)) : Gen σ F where
  random s :=
    match (sysRandom raw : RM σ F) s with
    | (.ok x, s') => (x, s')
    | (.error _, s') => (default, s')
  getrandbits := sysGetrandbits raw

/-! ### `Random.__init_subclass__`, Lib/random.py:225-243 -/

/-- A class in the MRO: which of the three names its `__dict__` holds, and the
function `_randbelow` is bound to there. -/
structure ClsDict where
  randbelow : Option String
  hasGetrandbits : Bool
  hasRandom : Bool
  deriving Repr, DecidableEq, Inhabited

/-- The `for c in cls.__mro__` loop, Lib/random.py:234-243. The result is the
function `cls._randbelow` ends up as: `none` when the loop found nothing and
assigned nothing. -/
def initSubclass : List ClsDict → Option String
  | [] => none
  | c :: mro =>
    match c.randbelow with
    | some f => some f
    | none =>
      if c.hasGetrandbits then some "_randbelow_with_getrandbits"
      else if c.hasRandom then some "_randbelow_without_getrandbits"
      else initSubclass mro

/-! ### `main`, Lib/random.py:1047-1083 -/

/-- A positional argument, with what `int(val)`, `float(val)` and `val.split()`
give for it (these are `str` and `int` behaviour, modelled elsewhere). -/
structure CliInput (F : Type) where
  asInt : Option Int
  asFloat : Option F
  words : List String

/-- The namespace `_parse_args` returns, Lib/random.py:1020-1044. -/
structure CliArgs (F : Type) where
  choice : Option (List String)
  integer : Option Int
  float : Option F
  test : Option Int
  input : List (CliInput F)
  inputStrs : List String

/-- What `main` returns. -/
inductive CliOut (F : Type) where
  | str (s : String)
  | int (n : Int)
  | flt (x : F)

/-- `except ValueError:` around `f`: run `handler` with the state at the raise. -/
def tryValue {α : Type} (x : RM σ α) (handler : RM σ α) : RM σ α := fun s =>
  match x s with
  | (.error (.valueError _), s') => handler s'
  | r => r

/-- `uniform(0, b)` for the module-level `uniform`. The `int` `0` converts exactly. -/
def cliUniform [Flt F] (g : Gen σ F) (b : F) : RM σ F := uniform g 0.0 b

/-- The positional-argument branch, Lib/random.py:1065-1078. The rebinding
`val = int(val)` at :1069 means that the `except ValueError` at :1071, which also
catches the `ValueError` of `randint(1, val)`, runs `float(val)` on the *int*. -/
def mainOne [Flt F] (below : Nat → RM σ Nat) (g : Gen σ F) (i : CliInput F) : RM σ (CliOut F) :=
  match i.asInt with
  | some n =>
    tryValue
      (do
        let r ← randint below (.int 1) (.int n)
        return .int r)
      (do
        let x : F ← lift (pyFloat n)
        let r ← cliUniform g x
        return .flt r)
  | none =>
    match i.asFloat with
    | some x => do
      let r ← cliUniform g x
      return .flt r
    | none => do
      let w ← choice below (listSeq i.words)
      return .str w

/-- `main`, Lib/random.py:1047-1083, on what `_parse_args` returned. `_test` only
prints timings, so the branch at :1060-1062 returns `""`. -/
def cliMain [Flt F] (below : Nat → RM σ Nat) (g : Gen σ F) (args : CliArgs F) (helpText : String) :
    RM σ (CliOut F) :=
  match args.choice with
  | some (c :: cs) => do
    let w ← choice below (listSeq (c :: cs))
    return .str w
  | _ =>
    match args.integer with
    | some n => do
      let r ← randint below (.int 1) (.int n)
      return .int r
    | none =>
      match args.float with
      | some x => do
        let r ← cliUniform g x
        return .flt r
      | none =>
        match args.test with
        | some t =>
          if t ≠ 0 then pure (.str "")
          else mainRest
        | none => mainRest
where
  /-- From `# No explicit argument`, Lib/random.py:1064. -/
  mainRest : RM σ (CliOut F) :=
    match args.input with
    | [i] => mainOne below g i
    | [] => pure (.str helpText)
    | _ => do
      let w ← choice below (listSeq args.inputStrs)
      return .str w

end PyLean.CoreLibs.Rand
