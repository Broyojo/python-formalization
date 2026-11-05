import PyLean.TextLibs.BinasciiC

/-!
`get_reverse_table`, `Modules/binascii.c:662-706`, with the module's `reverse_table_cache`: a `dict`
made at import (`:2767`) and keyed by the alphabet object itself. A lookup hashes the alphabet and
compares it with the stored keys of the same hash, so what a `bytes` subclass's `__hash__` and
`__eq__` say is observable, and a raising `__hash__` or `__eq__` propagates.

Scope limits, stated: a hash is a token, the hash of a `bytes` value or some other number, and two
distinct `bytes` values are taken to hash apart; keys of one hash are compared in the order they were
stored (the probe order of a dict without deletions); `__hash__` and `__eq__` give the same answer every
time they are asked, so the second hashing by `PyDict_SetItem` agrees with the first.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

/-- A hash value. -/
inductive HTok where
  | ofBytes (v : List Nat)
  | other (n : Int)
  deriving Repr, DecidableEq, Inhabited

/-- An alphabet object: an exact `bytes`, or an instance of a `bytes` subclass with identity `oid`,
value `v`, what its `__hash__` gives, and what its `__eq__` says about a `bytes` of a given value (its
truth value, or an exception). -/
inductive AObj where
  | bytes (v : List Nat)
  | sub (oid : Nat) (v : List Nat) (hash : Py HTok) (eqv : List Nat → Py Bool)

def AObj.value : AObj → List Nat
  | .bytes v | .sub _ v _ _ => v

/-- `PyObject_Hash`. -/
def AObj.hash : AObj → Py HTok
  | .bytes v => .ok (.ofBytes v)
  | .sub _ _ h _ => h

/-- `PyObject_RichCompare(stored, query, Py_EQ)` as a dict lookup asks it, after its identity test: a
subclass's reflected `__eq__` is asked first when the stored key is a plain `bytes`. -/
def keyEqC : AObj → AObj → Py Bool
  | .bytes a, .bytes b => .ok (a == b)
  | .bytes a, .sub _ _ _ eq => eq a
  | .sub i _ _ eq, q =>
    match q with
    | .sub j _ _ _ => if i == j then .ok true else eq q.value
    | .bytes b => eq b

/-- A value in the cache: what `get_reverse_table` stores, or another object (only `gc.get_referents`
reaches the dict). -/
inductive CVal where
  | table (b : List Nat)
  | other

/-- The cache, in the order the entries were stored, with the hash each was stored under. -/
abbrev RCache := List (AObj × HTok × CVal)

/-- `PyDict_GetItemRef(cache, alphabet)`. -/
def rcLookup : RCache → AObj → HTok → Py (Option CVal)
  | [], _, _ => .ok none
  | (k, h', v) :: r, q, h =>
    if h' == h then
      match keyEqC k q with
      | .error e => .error e
      | .ok true => .ok (some v)
      | .ok false => rcLookup r q h
    else rcLookup r q h

/-- The table built at `Modules/binascii.c:678-687`: 255 everywhere, `out[in[i]] = i` for each `i` in
order, then the pad character set to `size`. -/
def buildRev (alpha : List Nat) (size : Nat) (pad : Option Nat) : List Nat :=
  let out := (List.range size).foldl (fun out i => out.set (alpha.getD i 0) i) (List.replicate 256 255)
  match pad with
  | some p => out.set p size
  | none => out

def brokenCache : PyExc := .named "RuntimeError" "Broken binascii cache"

/-- `get_reverse_table(state, alphabet, size, padchar)`, `Modules/binascii.c:662-706`: the length
first, then the lookup (which hashes the alphabet), then on a miss the new table stored under the
alphabet, on a hit the check that the value is a 256-byte `bytes`. -/
def getReverseTable (c : RCache) (a : AObj) (size : Nat) (pad : Option Nat) : Py (List Nat) × RCache :=
  if a.value.length ≠ size then (.error (.valueError s!"alphabet must have length {size}"), c)
  else
    match a.hash with
    | .error e => (.error e, c)
    | .ok h =>
      match rcLookup c a h with
      | .error e => (.error e, c)
      | .ok none =>
        let t := buildRev a.value size pad
        (.ok t, c ++ [(a, h, .table t)])
      | .ok (some (.table t)) => if t.length ≠ 256 then (.error brokenCache, c) else (.ok t, c)
      | .ok (some .other) => (.error brokenCache, c)

/-- `alphabet: PyBytesObject` with the cache: absent, a `bytes` (or subclass) object, or another type. -/
inductive AlphaArgC where
  | absent
  | obj (a : AObj)
  | other (ty : String)

def alphaDecC (fname : String) : AlphaArgC → Py (Option AObj)
  | .absent => .ok none
  | .obj a => .ok (some a)
  | .other t => .error (.typeError s!"{fname}() argument 'alphabet' must be bytes, not {t}")

/-- The table of a decoder: the static one, or `get_reverse_table`'s, read as `table_a2b[this_ch]`. -/
def decTableC (c : RCache) (alpha : Option AObj) (default : Nat → Nat) (size : Nat) (pad : Option Nat) :
    Py (Nat → Nat) × RCache :=
  match alpha with
  | none => (.ok default, c)
  | some a =>
    match getReverseTable c a size pad with
    | (.ok t, c') => (.ok (fun ch => t.getD ch 255), c')
    | (.error e, c') => (.error e, c')

/-- `binascii.a2b_base64` with the cache. -/
def a2bB64S (c : RCache) (d : Data) (strict : Option Bool) (padded : Bool) (alpha : AlphaArgC) (ig : Option Data)
    (canonical : Bool) : Py (List Nat) × RCache :=
  match asciiBuffer d, alphaDecC "a2b_base64" alpha, bufOpt ig with
  | .error e, _, _ => (.error e, c)
  | .ok _, .error e, _ => (.error e, c)
  | .ok _, .ok _, .error e => (.error e, c)
  | .ok s, .ok a, .ok ig =>
    let strict := strict.getD ig.isSome
    let ig := if !strict || ig.isNone || ig == some [] then none else ig
    match decTableC c a (revT b64Alpha (some 61)) 64 (some 61) with
    | (.error e, c') => (.error e, c')
    | (.ok t, c') => (a2b64Core ⟨strict, padded, t, ig⟩ canonical s, c')

/-- `binascii.a2b_base32` with the cache. -/
def a2bB32S (c : RCache) (d : Data) (padded : Bool) (alpha : AlphaArgC) (ig : Data) (canonical : Bool) :
    Py (List Nat) × RCache :=
  match asciiBuffer d, alphaDecC "a2b_base32" alpha, bufData ig with
  | .error e, _, _ => (.error e, c)
  | .ok _, .error e, _ => (.error e, c)
  | .ok _, .ok _, .error e => (.error e, c)
  | .ok s, .ok a, .ok ig =>
    match decTableC c a (revT b32Alpha none) 32 (some 61) with
    | (.error e, c') => (.error e, c')
    | (.ok t, c') => (a2b32Core t padded (if ig.isEmpty then none else some ig) canonical s, c')

/-- `binascii.a2b_base85` with the cache. -/
def a2bB85S (c : RCache) (d : Data) (alpha : AlphaArgC) (ig : Data) (canonical : Bool) : Py (List Nat) × RCache :=
  match asciiBuffer d, alphaDecC "a2b_base85" alpha, bufData ig with
  | .error e, _, _ => (.error e, c)
  | .ok _, .error e, _ => (.error e, c)
  | .ok _, .ok _, .error e => (.error e, c)
  | .ok s, .ok a, .ok ig =>
    match decTableC c a (revT b85Alpha none) 85 none with
    | (.error e, c') => (.error e, c')
    | (.ok t, c') =>
      ((do
        let st ← a2bB85Loop t (if ig.isEmpty then none else some ig) canonical s.length (s.length + 6) s s.length {}
        return st.out), c')

end PyLean.TextLibs.Binascii
