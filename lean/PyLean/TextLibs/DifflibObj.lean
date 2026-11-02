import PyLean.TextLibs.DifflibModel

/-!
`SequenceMatcher`, `Lib/difflib.py:45-664`, over any hashable element. `DifflibModel.lean` is the same
class on natural numbers, with no failure in the element: `DifflibObjSim.lean` shows the two agree on
lawful elements, and so carries its theorems over.

`__hash__` and `__eq__` are `Ops.hash` and `Ops.eq`, each a function of its arguments that may raise.
`Ops.eq` is the whole of a Python `==` in a condition, the truth test of the result included, which is
why it is `Py Bool`. `Ops.same` is `is`. What this leaves out, as stated limits: a `__hash__` or `__eq__`
that gives different answers at different calls, and one that changes the sequences while they are
being read. `del b2j[elt]`, `junk.add` and `popular.add` only repeat comparisons of an older key with a
newer one that the dict has already made, so they cannot fail here.

A `dict` or `set` is its entries in insertion order, with the stored hash. Two keys of equal hash lie on
one probe sequence, with the older first, and a resize reinserts in order, so that is the order they are
compared in; keys of other hashes are never compared. Deletions leave the rest of a chain in order too.
-/

namespace PyLean.TextLibs.Difflib

open PyLean

/-- What the matcher can do with an element. -/
structure Ops (α : Type) where
  hash : α → Py Nat
  eq : α → α → Py Bool
  same : α → α → Bool

/-- A `dict`: key, stored hash, value. -/
abbrev DictO (α V : Type) := List (α × Nat × V)

/-- A `set`: key, stored hash. -/
abbrev SetO (α : Type) := List (α × Nat)

section Dict

variable {α V : Type} (o : Ops α)

/-- The test of `compare_generic`, `Objects/dictobject.c:1182-1207`, and of `set_do_lookup`: the identity
first, and `==` only for an equal stored hash, with the stored key on the left. -/
def keyIs (k : α) (h : Nat) (x : α) (hx : Nat) : Py Bool :=
  if o.same k x then .ok true
  else if h == hx then o.eq k x
  else .ok false

/-- `d.get(x)` for `x` of hash `hx`. -/
def dget (x : α) (hx : Nat) : DictO α V → Py (Option V)
  | [] => .ok none
  | (k, h, v) :: r =>
    match keyIs o k h x hx with
    | .error e => .error e
    | .ok true => .ok (some v)
    | .ok false => dget x hx r

/-- `x in s`. -/
def scontains (x : α) (hx : Nat) : SetO α → Py Bool
  | [] => .ok false
  | (k, h) :: r =>
    match keyIs o k h x hx with
    | .error e => .error e
    | .ok true => .ok true
    | .ok false => scontains x hx r

/-- `d[x] = f(old)`: an existing key stays, with its place. -/
def dput (x : α) (hx : Nat) (f : Option V → V) : DictO α V → Py (DictO α V)
  | [] => .ok [(x, hx, f none)]
  | (k, h, v) :: r =>
    match keyIs o k h x hx with
    | .error e => .error e
    | .ok true => .ok ((k, h, f (some v)) :: r)
    | .ok false =>
      match dput x hx f r with
      | .error e => .error e
      | .ok r => .ok ((k, h, v) :: r)

end Dict

/-- The members of a `SequenceMatcher` that these methods read and write. -/
structure SMO (α : Type) where
  a : List α
  b : List α
  isjunk : Option (α → Py Bool) := none
  autojunk : Bool := true
  b2j : DictO α (List Nat) := []
  bjunk : SetO α := []
  bpopular : SetO α := []
  blocks : Option (List T) := none
  opcodes : Option (List Op) := none
  fullb : Option (DictO α Nat) := none

section Chain

variable {α : Type} (o : Ops α)

/-- The `for` of `Lib/difflib.py:281-283`: `b2j` as far as it got, and how the loop ended. The hash is
taken and compared before anything is stored, so a failure leaves `m` as it was. -/
def buildO : List α → Nat → DictO α (List Nat) → DictO α (List Nat) × Py Unit
  | [], _, m => (m, .ok ())
  | x :: r, i, m =>
    match o.hash x with
    | .error e => (m, .error e)
    | .ok h =>
      match dput o x h (fun v => v.getD [] ++ [i]) m with
      | .error e => (m, .error e)
      | .ok m => buildO r (i + 1) m

/-- `Lib/difflib.py:289-293`: what is left of `b2j`, the set as far as it got, and how the loop ended. -/
def junkO (f : α → Py Bool) : DictO α (List Nat) → DictO α (List Nat) × SetO α × Py Unit
  | [] => ([], [], .ok ())
  | (k, h, v) :: r =>
    match f k with
    | .error e => ([], [], .error e)
    | .ok true =>
      let x := junkO f r
      (x.1, (k, h) :: x.2.1, x.2.2)
    | .ok false =>
      let x := junkO f r
      ((k, h, v) :: x.1, x.2.1, x.2.2)

/-- The `if isjunk:` of `Lib/difflib.py:288`. -/
def junkStepO (isjunk : Option (α → Py Bool)) (m : DictO α (List Nat)) : DictO α (List Nat) × SetO α × Py Unit :=
  match isjunk with
  | some f => junkO f m
  | none => (m, [], .ok ())

/-- `Lib/difflib.py:267-304`, on the matcher with `b` set. `b2j` is assigned before its loop, so a raising
`__hash__` or `__eq__` leaves it holding what it got to, with the old `bjunk` and `bpopular`. -/
def chainBO (s : SMO α) : SMO α × Py Unit :=
  let r := buildO o s.b 0 []
  match r.2 with
  | .error e => ({ s with b2j := r.1 }, .error e)
  | .ok () =>
    let j := junkStepO s.isjunk r.1
    match j.2.2 with
    | .error e => ({ s with b2j := r.1, bjunk := j.2.1 }, .error e)
    | .ok () =>
      let n := s.b.length
      let popular : Bool := s.autojunk && decide (n ≥ 200)
      let isPop (e : α × Nat × List Nat) : Bool := popular && decide (e.2.2.length > n / 100 + 1)
      ({ s with
          b2j := j.1.filter (fun e => !isPop e),
          bjunk := j.2.1,
          bpopular := (j.1.filter isPop).map (fun e => (e.1, e.2.1)) }, .ok ())

/-- `set_seq1`, `Lib/difflib.py:197-221`. -/
def setSeq1O (s : SMO α) (a : List α) (same : Bool) : SMO α :=
  if same then s else { s with a, blocks := none, opcodes := none }

/-- `set_seq2`, `Lib/difflib.py:223-249`. -/
def setSeq2O (s : SMO α) (b : List α) (same : Bool) : SMO α × Py Unit :=
  if same then (s, .ok ())
  else chainBO o { s with b, blocks := none, opcodes := none, fullb := none }

/-- `set_seqs`, `Lib/difflib.py:185-195`. -/
def setSeqsO (s : SMO α) (a b : List α) (sameA sameB : Bool) : SMO α × Py Unit :=
  setSeq2O o (setSeq1O s a sameA) b sameB

/-- `__init__`, `Lib/difflib.py:121-183`, on two sequences. -/
def makeO (isjunk : Option (α → Py Bool)) (a b : List α) (autojunk : Bool) : Py (SMO α) :=
  match setSeq2O o { a, b := [], isjunk, autojunk } b false with
  | (s, .ok ()) => .ok s
  | (_, .error e) => .error e

end Chain

section Match

variable {α : Type} (o : Ops α)

/-- `seq[i]`. -/
def atO (l : List α) (i : Nat) : Py α :=
  match l[i]? with
  | some x => .ok x
  | none => .error (.indexError "list index out of range")

/-- The outer `for`, `Lib/difflib.py:375-389`, with `b2j.get(a[i], nothing)`, whose hash and comparisons
can raise. -/
def outerO (s : SMO α) (blo bhi ahi : Nat) : (fuel : Nat) → Nat → List (Nat × Nat) → Best → Py Best
  | 0, _, _, best => .ok best
  | fuel + 1, i, j2len, best =>
    match atO s.a i with
    | .error e => .error e
    | .ok x =>
      match o.hash x with
      | .error e => .error e
      | .ok h =>
        match dget o x h s.b2j with
        | .error e => .error e
        | .ok v =>
          let r := innerLoop blo bhi i j2len (v.getD []) [] best
          outerO s blo bhi ahi fuel (i + 1) r.1 r.2

/-- A condition of the extension loops: `isbjunk(b[..])`, with the sense given by `junk`, then
`a[..] == b[..]`, whose `__eq__` has no identity shortcut. -/
def extTestO (s : SMO α) (junk : Bool) (ia ib : Nat) : Py Bool :=
  match atO s.b ib with
  | .error e => .error e
  | .ok y =>
    match o.hash y with
    | .error e => .error e
    | .ok h =>
      match scontains o y h s.bjunk with
      | .error e => .error e
      | .ok c =>
        if c != junk then .ok false
        else
          match atO s.a ia with
          | .error e => .error e
          | .ok x => o.eq x y

/-- `Lib/difflib.py:395-398` and `:411-414`. -/
def extendLeftO (s : SMO α) (junk : Bool) (alo blo : Nat) : Nat → Best → Py Best
  | 0, b => .ok b
  | fuel + 1, (i, j, k) =>
    if i > alo && j > blo then
      match extTestO o s junk (i - 1) (j - 1) with
      | .error e => .error e
      | .ok true => extendLeftO s junk alo blo fuel (i - 1, j - 1, k + 1)
      | .ok false => .ok (i, j, k)
    else .ok (i, j, k)

/-- `Lib/difflib.py:399-402` and `:415-418`. -/
def extendRightO (s : SMO α) (junk : Bool) (ahi bhi : Nat) : Nat → Best → Py Best
  | 0, b => .ok b
  | fuel + 1, (i, j, k) =>
    if i + k < ahi && j + k < bhi then
      match extTestO o s junk (i + k) (j + k) with
      | .error e => .error e
      | .ok true => extendRightO s junk ahi bhi fuel (i, j, k + 1)
      | .ok false => .ok (i, j, k)
    else .ok (i, j, k)

/-- `find_longest_match`, `Lib/difflib.py:306-420`. -/
def findLongestO (s : SMO α) (alo ahi blo bhi : Nat) : Py Best :=
  match outerO o s blo bhi ahi (ahi - alo) alo [] (alo, blo, 0) with
  | .error e => .error e
  | .ok b =>
    let f := ahi + bhi + 1
    match extendLeftO o s false alo blo f b with
    | .error e => .error e
    | .ok b =>
      match extendRightO o s false ahi bhi f b with
      | .error e => .error e
      | .ok b =>
        match extendLeftO o s true alo blo f b with
        | .error e => .error e
        | .ok b => extendRightO o s true ahi bhi f b

/-- `Lib/difflib.py:453-464`, with the found blocks newest first. -/
def blockLoopO (s : SMO α) : Nat → List Box → List T → Py (List T)
  | 0, _, _ => .error .modelFuel
  | _ + 1, [], found => .ok found
  | fuel + 1, (alo, ahi, blo, bhi) :: q, found =>
    match findLongestO o s alo ahi blo bhi with
    | .error e => .error e
    | .ok (i, j, k) =>
      if k != 0 then
        let q := if alo < i && blo < j then (alo, i, blo, j) :: q else q
        let q := if i + k < ahi && j + k < bhi then (i + k, ahi, j + k, bhi) :: q else q
        blockLoopO s fuel q ((i, j, k) :: found)
      else blockLoopO s fuel q found

/-- `get_matching_blocks`, `Lib/difflib.py:422-491`. `self.matching_blocks` is assigned at the end, so a
failure leaves no cache here. -/
def getBlocksO (s : SMO α) : Py (SMO α × List T) :=
  match s.blocks with
  | some b => .ok (s, b)
  | none =>
    let la := s.a.length
    let lb := s.b.length
    match blockLoopO o s (2 * la + 2) [(0, la, 0, lb)] [] with
    | .error e => .error e
    | .ok found =>
      let r := collapse (0, 0, 0) (sortT found) ++ [(la, lb, 0)]
      .ok ({ s with blocks := some r }, r)

/-- `get_opcodes`, `Lib/difflib.py:493-546`. It assigns `self.opcodes = answer = []` at `:525`, ahead of
`get_matching_blocks`, and that list is what stays when the call raises. -/
def getOpcodesO (s : SMO α) : SMO α × Py (List Op) :=
  match s.opcodes with
  | some x => (s, .ok x)
  | none =>
    let s0 := { s with opcodes := some [] }
    match getBlocksO o s0 with
    | .error e => (s0, .error e)
    | .ok (s, blocks) =>
      let x := opLoop blocks 0 0
      ({ s with opcodes := some x }, .ok x)

/-- `get_grouped_opcodes`, `Lib/difflib.py:548-596`, run to the end. -/
def getGroupedO (s : SMO α) (n : Nat) : SMO α × Py (List (List Op)) :=
  match getOpcodesO o s with
  | (s, .error e) => (s, .error e)
  | (s, .ok ops) =>
    let codes : List Op := if ops.isEmpty then [(.equal, 0, 1, 0, 1)] else ops
    let codes := fixLast n (fixFirst n codes)
    let s := if ops.isEmpty then s else { s with opcodes := some codes }
    let r := groupLoop n codes [] []
    (s, .ok (r.1 ++ closeGroup r.2))

/-- `ratio`, `Lib/difflib.py:598-621`, as `(matches, length)`. -/
def ratioPairO (s : SMO α) : Py (SMO α × Nat × Nat) :=
  match getBlocksO o s with
  | .error e => .error e
  | .ok (s, b) => .ok (s, sumBlocks b, s.a.length + s.b.length)

/-- `fullbcount`, `Lib/difflib.py:633-636`: the dict as far as it got, and how the loop ended. -/
def countO : List α → DictO α Nat → DictO α Nat × Py Unit
  | [], m => (m, .ok ())
  | x :: r, m =>
    match o.hash x with
    | .error e => (m, .error e)
    | .ok h =>
      match dput o x h (fun v => v.getD 0 + 1) m with
      | .error e => (m, .error e)
      | .ok m => countO r m

/-- The `for` of `Lib/difflib.py:642-649`. `avail` goes below 0, as it does in the source. -/
def quickO (full : DictO α Nat) : List α → DictO α Int → Nat → Py Nat
  | [], _, m => .ok m
  | e :: r, avail, m =>
    match o.hash e with
    | .error er => .error er
    | .ok h =>
      let numb : Py Int :=
        match dget o e h avail with
        | .error er => .error er
        | .ok (some v) => .ok v
        | .ok none =>
          match dget o e h full with
          | .error er => .error er
          | .ok v => .ok (v.getD 0 : Nat)
      match numb with
      | .error er => .error er
      | .ok numb =>
        match dput o e h (fun _ => numb - 1) avail with
        | .error er => .error er
        | .ok avail => quickO full r avail (if numb > 0 then m + 1 else m)

/-- `quick_ratio`, `Lib/difflib.py:623-650`, as `(matches, length)`. `self.fullbcount` is assigned ahead of
its loop. -/
def quickPairO (s : SMO α) : SMO α × Py (Nat × Nat) :=
  let c : DictO α Nat × Py Unit :=
    match s.fullb with
    | some f => (f, .ok ())
    | none => countO o s.b []
  let s1 := { s with fullb := some c.1 }
  match c.2 with
  | .error e => (s1, .error e)
  | .ok () =>
    match quickO o c.1 s.a [] 0 with
    | .error e => (s1, .error e)
    | .ok m => (s1, .ok (m, s.a.length + s.b.length))

end Match

end PyLean.TextLibs.Difflib
