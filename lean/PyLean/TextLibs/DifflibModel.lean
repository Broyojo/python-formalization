import PyLean.Core

/-!
`SequenceMatcher`, `Lib/difflib.py:44-663`, CPython 3.14.7. Scope limits, as stated rules for this file:
elements are `int`s compared by value, the sequences are lists, positions passed to
`find_longest_match` are not negative, and `n` of `get_grouped_opcodes` is not negative. `isjunk` is
fallible, and it is called once for each distinct element, so a function of the element covers a
stateful callable too. `set_seq1` and `set_seq2` test `is`: `same` says whether the new sequence is the
object already held. Generators are run to the end, as `list(...)` does.
-/

namespace PyLean.TextLibs.Difflib

open PyLean

/-- A block `(i, j, k)`, or a `Match`. -/
abbrev T := Nat × Nat × Nat

/-- The tags of `get_opcodes`. -/
inductive Tag where
  | replace | delete | insert | equal
  deriving Repr, DecidableEq, Inhabited

/-- `(tag, i1, i2, j1, j2)`. -/
abbrev Op := Tag × Nat × Nat × Nat × Nat

/-- The members of a `SequenceMatcher` that these methods read and write. -/
structure SM where
  a : List Nat
  b : List Nat
  isjunk : Option (Nat → Py Bool) := none
  autojunk : Bool := true
  b2j : List (Nat × List Nat) := []
  bjunk : List Nat := []
  bpopular : List Nat := []
  blocks : Option (List T) := none
  opcodes : Option (List Op) := none
  fullb : Option (List (Nat × Nat)) := none

/-- `b2j.setdefault(elt, []).append(i)`: keys stay in first-seen order, as in a `dict`. -/
def addIdx : List (Nat × List Nat) → Nat → Nat → List (Nat × List Nat)
  | [], elt, i => [(elt, [i])]
  | (k, v) :: r, elt, i => if k == elt then (k, v ++ [i]) :: r else (k, v) :: addIdx r elt i

/-- The `for` of `Lib/difflib.py:280-282`. -/
def buildB2j (b : List Nat) : List (Nat × List Nat) :=
  (b.zipIdx).foldl (fun m p => addIdx m p.1 p.2) []

/-- `Lib/difflib.py:288-290`: the set as far as it got, and how the loop ended. -/
def junkOf (f : Nat → Py Bool) : List (Nat × List Nat) → List Nat × Py Unit
  | [] => ([], .ok ())
  | (k, _) :: r =>
    match f k with
    | .error e => ([], .error e)
    | .ok true =>
      let x := junkOf f r
      (k :: x.1, x.2)
    | .ok false => junkOf f r

/-- `Lib/difflib.py:266-303`, on the matcher with `b` set. When `isjunk` raises, `b2j` holds everything,
`bjunk` the elements judged so far, and `bpopular` its old value, and the object can still be used. -/
def chainB (s : SM) : SM × Py Unit :=
  let b2j := buildB2j s.b
  let j : List Nat × Py Unit :=
    match s.isjunk with
    | some f => junkOf f b2j
    | none => ([], .ok ())
  match j.2 with
  | .error e => ({ s with b2j, bjunk := j.1 }, .error e)
  | .ok () =>
    let junk := j.1
    let b2j := b2j.filter (fun p => !junk.contains p.1)
    let n := s.b.length
    let popular : List Nat :=
      if s.autojunk && decide (n ≥ 200) then
        (b2j.filter (fun p => decide (p.2.length > n / 100 + 1))).map (·.1)
      else []
    let b2j := b2j.filter (fun p => !popular.contains p.1)
    ({ s with b2j, bjunk := junk, bpopular := popular }, .ok ())

/-- `set_seq1`, `Lib/difflib.py:196-220`. -/
def setSeq1 (s : SM) (a : List Nat) (same : Bool) : SM :=
  if same then s else { s with a, blocks := none, opcodes := none }

/-- `set_seq2`, `Lib/difflib.py:222-248`. -/
def setSeq2 (s : SM) (b : List Nat) (same : Bool) : SM × Py Unit :=
  if same then (s, .ok ())
  else chainB { s with b, blocks := none, opcodes := none, fullb := none }

/-- `set_seqs`, `Lib/difflib.py:184-194`. -/
def setSeqs (s : SM) (a b : List Nat) (sameA sameB : Bool) : SM × Py Unit :=
  setSeq2 (setSeq1 s a sameA) b sameB

/-- `__init__`, `Lib/difflib.py:120-182`, on two sequences. -/
def make (isjunk : Option (Nat → Py Bool)) (a b : List Nat) (autojunk : Bool) : Py SM :=
  match setSeq2 { a, b := [], isjunk, autojunk } b false with
  | (s, .ok ()) => .ok s
  | (_, .error e) => .error e

/-- `seq[i]`. -/
def at? (l : List Nat) (i : Nat) : Py Nat :=
  match l[i]? with
  | some x => .ok x
  | none => .error (.indexError "list index out of range")

/-- `b2j.get(x, nothing)`. -/
def lookupIdx (m : List (Nat × List Nat)) (x : Nat) : List Nat := (m.lookup x).getD []

/-- `j2lenget(j-1, 0)`. -/
def j2get (m : List (Nat × Nat)) (j : Nat) : Nat :=
  match j with
  | 0 => 0
  | j + 1 => (m.lookup j).getD 0

/-- The state of the scan: `besti`, `bestj`, `bestsize`. -/
abbrev Best := Nat × Nat × Nat

/-- The inner `for`, `Lib/difflib.py:379-387`, at `i`. -/
def innerLoop (blo bhi i : Nat) (old : List (Nat × Nat)) :
    List Nat → List (Nat × Nat) → Best → List (Nat × Nat) × Best
  | [], new, best => (new, best)
  | j :: r, new, best =>
    if j < blo then innerLoop blo bhi i old r new best
    else if j ≥ bhi then (new, best)
    else
      let k := j2get old j + 1
      let new := (j, k) :: new
      let best := if k > best.2.2 then (i + 1 - k, j + 1 - k, k) else best
      innerLoop blo bhi i old r new best

/-- The outer `for`, `Lib/difflib.py:374-388`, over `range(i, ahi)` with `fuel` the length. -/
def outerLoop (s : SM) (blo bhi ahi : Nat) : (fuel : Nat) → Nat → List (Nat × Nat) → Best → Py Best
  | 0, _, _, best => .ok best
  | fuel + 1, i, j2len, best =>
    match at? s.a i with
    | .error e => .error e
    | .ok x =>
      let r := innerLoop blo bhi i j2len (lookupIdx s.b2j x) [] best
      outerLoop s blo bhi ahi fuel (i + 1) r.1 r.2

/-- A condition of the extension loops: `isbjunk(b[..])`, with the sense given by `junk`, then `==`. -/
def extTest (s : SM) (junk : Bool) (ia ib : Nat) : Py Bool :=
  match at? s.b ib with
  | .error e => .error e
  | .ok y =>
    if s.bjunk.contains y != junk then .ok false
    else
      match at? s.a ia with
      | .error e => .error e
      | .ok x => .ok (x == y)

/-- `Lib/difflib.py:394-397` and `:410-413`. -/
def extendLeft (s : SM) (junk : Bool) (alo blo : Nat) : Nat → Best → Py Best
  | 0, b => .ok b
  | fuel + 1, (i, j, k) =>
    if i > alo && j > blo then
      match extTest s junk (i - 1) (j - 1) with
      | .error e => .error e
      | .ok true => extendLeft s junk alo blo fuel (i - 1, j - 1, k + 1)
      | .ok false => .ok (i, j, k)
    else .ok (i, j, k)

/-- `Lib/difflib.py:398-401` and `:414-417`. -/
def extendRight (s : SM) (junk : Bool) (ahi bhi : Nat) : Nat → Best → Py Best
  | 0, b => .ok b
  | fuel + 1, (i, j, k) =>
    if i + k < ahi && j + k < bhi then
      match extTest s junk (i + k) (j + k) with
      | .error e => .error e
      | .ok true => extendRight s junk ahi bhi fuel (i, j, k + 1)
      | .ok false => .ok (i, j, k)
    else .ok (i, j, k)

/-- `find_longest_match`, `Lib/difflib.py:305-419`. -/
def findLongest (s : SM) (alo ahi blo bhi : Nat) : Py Best :=
  match outerLoop s blo bhi ahi (ahi - alo) alo [] (alo, blo, 0) with
  | .error e => .error e
  | .ok b =>
    let f := ahi + bhi + 1
    match extendLeft s false alo blo f b with
    | .error e => .error e
    | .ok b =>
      match extendRight s false ahi bhi f b with
      | .error e => .error e
      | .ok b =>
        match extendLeft s true alo blo f b with
        | .error e => .error e
        | .ok b => extendRight s true ahi bhi f b

/-- A box of the queue. -/
abbrev Box := Nat × Nat × Nat × Nat

/-- `Lib/difflib.py:452-463`, with the found blocks newest first. -/
def blockLoop (s : SM) : Nat → List Box → List T → Py (List T)
  | 0, _, _ => .error .modelFuel
  | _ + 1, [], found => .ok found
  | fuel + 1, (alo, ahi, blo, bhi) :: q, found =>
    match findLongest s alo ahi blo bhi with
    | .error e => .error e
    | .ok (i, j, k) =>
      if k != 0 then
        let q := if alo < i && blo < j then (alo, i, blo, j) :: q else q
        let q := if i + k < ahi && j + k < bhi then (i + k, ahi, j + k, bhi) :: q else q
        blockLoop s fuel q ((i, j, k) :: found)
      else blockLoop s fuel q found

/-- The order of `Match` tuples. -/
def tLe (x y : T) : Bool :=
  decide (x.1 < y.1) || (x.1 == y.1 &&
    (decide (x.2.1 < y.2.1) || (x.2.1 == y.2.1 && decide (x.2.2 ≤ y.2.2))))

def insertT (x : T) : List T → List T
  | [] => [x]
  | y :: r => if tLe x y then x :: y :: r else y :: insertT x r

/-- `matching_blocks.sort()`. The triples have one order, so any sort gives this result. -/
def sortT : List T → List T
  | [] => []
  | x :: r => insertT x (sortT r)

/-- `Lib/difflib.py:469-486`. `cur` is `(i1, j1, k1)`. -/
def collapse : T → List T → List T
  | (i1, j1, k1), [] => if k1 != 0 then [(i1, j1, k1)] else []
  | (i1, j1, k1), (i2, j2, k2) :: r =>
    if i1 + k1 == i2 && j1 + k1 == j2 then collapse (i1, j1, k1 + k2) r
    else if k1 != 0 then (i1, j1, k1) :: collapse (i2, j2, k2) r
    else collapse (i2, j2, k2) r

/-- `get_matching_blocks`, `Lib/difflib.py:421-490`. -/
def getBlocks (s : SM) : Py (SM × List T) :=
  match s.blocks with
  | some b => .ok (s, b)
  | none =>
    let la := s.a.length
    let lb := s.b.length
    match blockLoop s (2 * la + 2) [(0, la, 0, lb)] [] with
    | .error e => .error e
    | .ok found =>
      let r := collapse (0, 0, 0) (sortT found) ++ [(la, lb, 0)]
      .ok ({ s with blocks := some r }, r)

/-- The `for` of `Lib/difflib.py:525-544`. -/
def opLoop : List T → Nat → Nat → List Op
  | [], _, _ => []
  | (ai, bj, size) :: r, i, j =>
    let tag : Option Tag :=
      if i < ai && j < bj then some .replace
      else if i < ai then some .delete
      else if j < bj then some .insert
      else none
    let first : List Op :=
      match tag with
      | some t => [(t, i, ai, j, bj)]
      | none => []
    let eq : List Op := if size != 0 then [(.equal, ai, ai + size, bj, bj + size)] else []
    first ++ eq ++ opLoop r (ai + size) (bj + size)

/-- `get_opcodes`, `Lib/difflib.py:492-545`. -/
def getOpcodes (s : SM) : Py (SM × List Op) :=
  match s.opcodes with
  | some o => .ok (s, o)
  | none =>
    match getBlocks s with
    | .error e => .error e
    | .ok (s, blocks) =>
      let o := opLoop blocks 0 0
      .ok ({ s with opcodes := some o }, o)

/-- The first line of the fixup, `Lib/difflib.py:576-578`. -/
def fixFirst (n : Nat) : List Op → List Op
  | (.equal, i1, i2, j1, j2) :: r => (.equal, max i1 (i2 - n), i2, max j1 (j2 - n), j2) :: r
  | l => l

/-- The rest of it, `Lib/difflib.py:579-581`. -/
def fixLast (n : Nat) : List Op → List Op
  | [] => []
  | [(.equal, i1, i2, j1, j2)] => [(.equal, i1, min i2 (i1 + n), j1, min j2 (j1 + n))]
  | [o] => [o]
  | o :: r => o :: fixLast n r

/-- The `for` of `Lib/difflib.py:585-593`, with the groups done so far in `done`, oldest first, and the
open group newest first. -/
def groupLoop (n : Nat) : List Op → List (List Op) → List Op → List (List Op) × List Op
  | [], done, group => (done, group)
  | (t, i1, i2, j1, j2) :: r, done, group =>
    if t == .equal && decide (i2 - i1 > n + n) then
      let g := ((.equal, i1, min i2 (i1 + n), j1, min j2 (j1 + n)) :: group).reverse
      groupLoop n r (done ++ [g]) [(t, max i1 (i2 - n), i2, max j1 (j2 - n), j2)]
    else groupLoop n r done ((t, i1, i2, j1, j2) :: group)

/-- The last two lines, `Lib/difflib.py:594-595`, on the reversed open group. -/
def closeGroup : List Op → List (List Op)
  | [] => []
  | [(.equal, _, _, _, _)] => []
  | g => [g.reverse]

/-- `get_grouped_opcodes`, `Lib/difflib.py:547-595`, run to the end. `codes = self.get_opcodes()` is
the cached list itself, so the two assignments at `:578` and `:581` write into the cache. -/
def getGrouped (s : SM) (n : Nat) : Py (SM × List (List Op)) :=
  match getOpcodes s with
  | .error e => .error e
  | .ok (s, ops) =>
    let codes : List Op := if ops.isEmpty then [(.equal, 0, 1, 0, 1)] else ops
    let codes := fixLast n (fixFirst n codes)
    let s := if ops.isEmpty then s else { s with opcodes := some codes }
    let r := groupLoop n codes [] []
    .ok (s, r.1 ++ closeGroup r.2)

/-- The sum of the sizes of the blocks. -/
def sumBlocks : List T → Nat
  | [] => 0
  | (_, _, k) :: r => k + sumBlocks r

/-- `ratio`, `Lib/difflib.py:597-620`, as `(matches, length)`. `_calculate_ratio` at `:39-42` gives
`2.0 * matches / length`, and `1.0` for length 0. -/
def ratioPair (s : SM) : Py (SM × Nat × Nat) :=
  match getBlocks s with
  | .error e => .error e
  | .ok (s, b) => .ok (s, sumBlocks b, s.a.length + s.b.length)

/-- `fullbcount`, `Lib/difflib.py:632-635`. -/
def countB : List Nat → List (Nat × Nat) → List (Nat × Nat)
  | [], m => m
  | e :: r, m =>
    let c := (m.lookup e).getD 0
    countB r ((e, c + 1) :: m)

/-- The `for` of `Lib/difflib.py:641-648`. `avail` is a map with the newest entry first, and goes
below 0, as it does in the source. -/
def quickLoop (full : List (Nat × Nat)) : List Nat → List (Nat × Int) → Nat → Nat
  | [], _, m => m
  | e :: r, avail, m =>
    let numb : Int :=
      match avail.lookup e with
      | some v => v
      | none => ((full.lookup e).getD 0 : Nat)
    quickLoop full r ((e, numb - 1) :: avail) (if numb > 0 then m + 1 else m)

/-- `quick_ratio`, `Lib/difflib.py:622-649`, as `(matches, length)`. -/
def quickPair (s : SM) : SM × Nat × Nat :=
  let full := match s.fullb with
    | some f => f
    | none => countB s.b []
  ({ s with fullb := some full }, quickLoop full s.a [] 0, s.a.length + s.b.length)

/-- `real_quick_ratio`, `Lib/difflib.py:651-661`, as `(matches, length)`. -/
def realQuickPair (s : SM) : Nat × Nat :=
  (min s.a.length s.b.length, s.a.length + s.b.length)

end PyLean.TextLibs.Difflib
