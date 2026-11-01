/-!
# Model of `list.sort` (CPython 3.14.7, `Objects/listobject.c`)

Line numbers refer to `Objects/listobject.c` of CPython 3.14.7.

Representation. The C code sorts an array in place and keeps a stack of
pending runs `struct s_slice {base, len, power}` that point into it
(`listobject.c:1763-1767`). The model keeps exactly that: the array is a
`List α`, a pending run is a `Slice` holding its start index, length and power,
and the stack is a `List Slice` with the top (C's `pending[ms->n - 1]`) at the
head. The merge routines receive the two adjacent runs as lists cut out of the
array and return the merged run, which is written back in place.

Comparisons. Every `ISLT(X, Y)` (`listobject.c:1730`) is one call of the
element comparison `lt X Y` and increments `MS.ncmp`, so the model reports the
exact number of `__lt__` calls; the difftest compares that count with CPython.
`lt` never raises in the model (exceptions raised by `__lt__` and mutation of
the list during the sort are out of scope).

Loops are structural recursion on a fuel argument, given enough fuel to
finish (each iteration consumes an element). The proofs show the fuel never
runs out for a consistent comparison; for an inconsistent one the results of
the permutation and stack theorems hold whether or not it does.
-/

namespace PyLean.ListSort

/-- `MIN_GALLOP` (`listobject.c:1749`). -/
def MIN_GALLOP : Nat := 7
/-- `MAX_MINRUN` (`listobject.c:1755`). -/
def MAX_MINRUN : Nat := 64
/-- `MAX_MERGE_PENDING` = `SIZEOF_SIZE_T * 8` on a 64-bit build (`listobject.c:1744`). -/
def MAX_MERGE_PENDING : Nat := 64

/-- The parts of `MergeState` (`listobject.c:1770-1820`) that influence the
result: `min_gallop`, plus the model's comparison counter. -/
structure MS where
  minGallop : Nat := MIN_GALLOP
  ncmp : Nat := 0
  deriving Repr, Inhabited

variable {α : Type}

/-- `ISLT(x, y)`: one call of `x < y`. -/
@[inline] def islt (lt : α → α → Bool) (ms : MS) (x y : α) : Bool × MS :=
  (lt x y, { ms with ncmp := ms.ncmp + 1 })

/-! ## binarysort (`listobject.c:1822-1953`) -/

/-- The binary search loop of `binarysort`/`gallop_*`: `while (lo < hi)`, with
`m = lo + ((hi - lo) >> 1)` (`binarysort` writes `(L + R) >> 1`, the same
value for `0 <= L <= R`). `test m` is true when `a[m]` belongs left of the
item being placed; then `lo = m + 1`, else `hi = m`. -/
def binLoop (test : Nat → MS → Bool × MS) : Nat → Nat → Nat → MS → Nat × MS
  | 0, lo, _, ms => (lo, ms)
  | fuel + 1, lo, hi, ms =>
    if lo < hi then
      let m := lo + (hi - lo) / 2
      let (c, ms) := test m ms
      if c then binLoop test fuel (m + 1) hi ms else binLoop test fuel lo m ms
    else (lo, ms)

/-- One pivot of `binarysort` (`listobject.c:1897-1941`): find `L` in the sorted
`a[:ok]` with `IFLT(pivot, a[M]) R = M; else L = M + 1`, and insert the pivot at
`L`, sliding `a[L:ok]` right. -/
def bsInsert (lt : α → α → Bool) (sorted : List α) (pivot : α) (ms : MS) : List α × MS :=
  let test := fun (m : Nat) (ms : MS) =>
    let (c, ms) := islt lt ms pivot (sorted.getD m pivot)
    (!c, ms)
  let (l, ms) := binLoop test (sorted.length + 1) 0 sorted.length ms
  (sorted.take l ++ pivot :: sorted.drop l, ms)

/-- Insert the pivots `a[ok]`, `a[ok+1]`, ... in turn. -/
def bsLoop (lt : α → α → Bool) : List α → List α → MS → List α × MS
  | sorted, [], ms => (sorted, ms)
  | sorted, p :: ps, ms =>
    let (sorted, ms) := bsInsert lt sorted p ms
    bsLoop lt sorted ps ms

/-- `binarysort(ms, ss, n, ok)`: sort `a[:n]` given that `a[:ok]` is sorted;
`a[n:]` is untouched. (`if (! ok) ++ok;`, `listobject.c:1845-1846`.) -/
def binarysort (lt : α → α → Bool) (a : List α) (n ok : Nat) (ms : MS) : List α × MS :=
  let ok := if ok = 0 then 1 else ok
  let (s, ms) := bsLoop lt (a.take ok) ((a.take n).drop ok) ms
  (s ++ a.drop n, ms)

/-! ## count_run (`listobject.c:1963-2064`) -/

/-- An ascending loop `for (; n < nremaining; ++n) { IF_NEXT_SMALLER break; }`
starting after `prev = lo[n-1]`: returns the items appended to the run and the
rest of the slice. -/
def ascTake (lt : α → α → Bool) : α → List α → MS → List α × List α × MS
  | _, [], ms => ([], [], ms)
  | prev, z :: rest, ms =>
    let (c, ms) := islt lt ms z prev
    if c then ([], z :: rest, ms)
    else
      let (t, r, ms) := ascTake lt z rest ms
      (z :: t, r, ms)

/-- The descending loop (`listobject.c:2030-2045`). The slice so far is `done`
(all-equal groups already reversed in place by `REVERSE_LAST_NEQ`) followed by
the current all-equal group `grp` (original order; `neq + 1` items) whose last
item is `prev = lo[n-1]`. Returns the slice prefix after the final
`REVERSE_LAST_NEQ` (before the whole-run reversal) and the rest. -/
def descLoop (lt : α → α → Bool) : List α → List α → α → List α → MS → List α × List α × MS
  | done, grp, _, [], ms => (done ++ grp.reverse, [], ms)
  | done, grp, prev, z :: rest, ms =>
    let (c, ms) := islt lt ms z prev            -- IF_NEXT_SMALLER
    if c then descLoop lt (done ++ grp.reverse) [z] z rest ms   -- REVERSE_LAST_NEQ
    else
      let (d, ms) := islt lt ms prev z          -- IF_NEXT_LARGER
      if d then (done ++ grp.reverse, z :: rest, ms)            -- break
      else descLoop lt done (grp ++ [z]) z rest ms              -- ++neq

/-- `count_run(ms, slo, nremaining)` with `slo` the remaining slice `xs`.
Returns the run length `n` and the new contents of the slice, whose first `n`
items are now ascending. -/
def countRun (lt : α → α → Bool) (xs : List α) (ms : MS) : Nat × List α × MS :=
  match xs with
  | [] => (0, [], ms)                                   -- unreachable: assert(nremaining)
  | x0 :: rest =>
    let (t, r, ms) := ascTake lt x0 rest ms            -- try ascending run first
    let asc := x0 :: t
    match r with
    | [] => (asc.length, xs, ms)                        -- n == nremaining
    | y :: r' =>
      -- lo[n] = y is strictly less than lo[n-1]
      let (early, ms) :=
        if asc.length > 1 then islt lt ms x0 (asc.getLast (by simp [asc])) else (false, ms)
      if early then (asc.length, xs, ms)                -- IFLT(lo[0], lo[n-1]) return n
      else
        -- the all-equal prefix is reversed in place (sortslice_reverse(slo, n)); ++n
        let (pre, r2, ms) := descLoop lt asc.reverse [y] y r' ms
        let run := pre.reverse                          -- sortslice_reverse(slo, n)
        -- extend by a naturally increasing suffix
        match run with
        | [] => (0, xs, ms)                             -- unreachable
        | w :: ws =>
          let (e, r3, ms) := ascTake lt ((w :: ws).getLast (by simp)) r2 ms
          (run.length + e.length, run ++ e ++ r3, ms)

/-! ## gallop_left / gallop_right (`listobject.c:2066-2249`) -/

/-- Gallop rightwards from `hint` (`a[hint]` belongs left of the key): `while
(ofs < maxofs) { IFLT-test(a[hint+ofs]) { lastofs = ofs; ofs = (ofs << 1) + 1; }
else break; }`. Returns `(lastofs, ofs)`. -/
def gallopUp (test : Nat → MS → Bool × MS) (hint maxofs : Nat) :
    Nat → Nat → Nat → MS → Nat × Nat × MS
  | 0, lastofs, ofs, ms => (lastofs, ofs, ms)
  | fuel + 1, lastofs, ofs, ms =>
    if ofs < maxofs then
      let (c, ms) := test (hint + ofs) ms
      if c then gallopUp test hint maxofs fuel ofs (2 * ofs + 1) ms else (lastofs, ofs, ms)
    else (lastofs, ofs, ms)

/-- Gallop leftwards from `hint` (`a[hint]` does not belong left of the key):
`while (ofs < maxofs) { if test(a[hint-ofs]) break; lastofs = ofs; ofs = (ofs << 1) + 1; }`. -/
def gallopDown (test : Nat → MS → Bool × MS) (hint maxofs : Nat) :
    Nat → Nat → Nat → MS → Nat × Nat × MS
  | 0, lastofs, ofs, ms => (lastofs, ofs, ms)
  | fuel + 1, lastofs, ofs, ms =>
    if ofs < maxofs then
      let (c, ms) := test (hint - ofs) ms
      if c then (lastofs, ofs, ms) else gallopDown test hint maxofs fuel ofs (2 * ofs + 1) ms
    else (lastofs, ofs, ms)

/-- The common body of `gallop_left` and `gallop_right` over a sorted vector
`a[0:n]` (read through `get`). `test i` is true when `a[i]` belongs strictly to
the left of the key: `IFLT(a[i], key)` for `gallop_left`, `!IFLT(key, a[i])` for
`gallop_right`; with that substitution the two C functions are this code line
for line. The C variable `lastofs` can be `-1` after the leftward gallop; the
model keeps `lastofs + 1` (the C value after `++lastofs`) as a `Nat`. -/
def gallopCore (test : Nat → MS → Bool × MS) (n hint : Nat) (ms : MS) : Nat × MS :=
  let (c, ms) := test hint ms
  let (lo, hi, ms) :=
    if c then
      -- a[hint] belongs left: gallop right until a[hint+lastofs] < key <= a[hint+ofs]
      let maxofs := n - hint
      let (lastofs, ofs, ms) := gallopUp test hint maxofs (n + 1) 0 1 ms
      let ofs := if ofs > maxofs then maxofs else ofs
      (lastofs + hint + 1, ofs + hint, ms)
    else
      -- gallop left until a[hint-ofs] < key <= a[hint-lastofs]
      let maxofs := hint + 1
      let (lastofs, ofs, ms) := gallopDown test hint maxofs (n + 1) 0 1 ms
      let ofs := if ofs > maxofs then maxofs else ofs
      -- k = lastofs; lastofs = hint - ofs; ofs = hint - k; then ++lastofs
      (hint + 1 - ofs, hint - lastofs, ms)
  binLoop test (n + 1) lo hi ms

/-- `gallop_left(ms, key, a, n, hint)`: the `k` with `a[k-1] < key <= a[k]`. -/
def gallopLeft (lt : α → α → Bool) (key : α) (get : Nat → α) (n hint : Nat) (ms : MS) : Nat × MS :=
  gallopCore (fun i ms => islt lt ms (get i) key) n hint ms

/-- `gallop_right(ms, key, a, n, hint)`: the `k` with `a[k-1] <= key < a[k]`. -/
def gallopRight (lt : α → α → Bool) (key : α) (get : Nat → α) (n hint : Nat) (ms : MS) : Nat × MS :=
  gallopCore (fun i ms => let (c, ms) := islt lt ms key (get i); (!c, ms)) n hint ms

/-! ## merge_lo (`listobject.c:2341-2471`) -/

/-- The `for (;;)` body of `merge_lo` after `dest` received the items `out`.
`A` is the rest of run A (in the temp array), `B` the rest of run B, `mg` the
local `min_gallop`. `gallop = false` is the "straightforward" one-pair-at-a-time
loop with counters `acount`/`bcount`; `gallop = true` is the `do { } while`
galloping loop. -/
def loLoop (lt : α → α → Bool) :
    Nat → Bool → Nat → Nat → Nat → List α → List α → List α → MS → List α × MS
  | 0, _, _, _, _, out, A, B, ms => (out ++ A ++ B, ms)
  | fuel + 1, false, mg, acount, bcount, out, A, B, ms =>
    match A, B with
    | a :: A', b :: B' =>
      let (c, ms) := islt lt ms b a                       -- ISLT(ssb.keys[0], ssa.keys[0])
      if c then
        if B' = [] then (out ++ [b] ++ A, ms)             -- nb == 0: Succeed
        else if bcount + 1 ≥ mg then loLoop lt fuel true (mg + 1) 0 0 (out ++ [b]) A B' ms
        else loLoop lt fuel false mg 0 (bcount + 1) (out ++ [b]) A B' ms
      else
        if A'.length = 1 then (out ++ [a] ++ B ++ A', ms)  -- na == 1: CopyB
        else if acount + 1 ≥ mg then loLoop lt fuel true (mg + 1) 0 0 (out ++ [a]) A' B ms
        else loLoop lt fuel false mg (acount + 1) 0 (out ++ [a]) A' B ms
    | _, _ => (out ++ A ++ B, ms)                         -- unreachable
  | fuel + 1, true, mg, _, _, out, A, B, ms =>
    -- `mg` is the local `min_gallop` after the `++min_gallop` that precedes the
    -- `do` loop (callers entering galloping pass `mg + 1`); one `do` iteration:
    let mg := mg - (if mg > 1 then 1 else 0)
    let ms := { ms with minGallop := mg }
    match B with
    | [] => (out ++ A, ms)                                -- unreachable
    | b :: B' =>
      let (k, ms) := gallopRight lt b (fun i => A.getD i b) A.length 0 ms
      let acount := k
      let out := out ++ A.take k
      let A := A.drop k
      if k ≠ 0 ∧ A.length = 1 then (out ++ B ++ A, ms)   -- CopyB
      else if k ≠ 0 ∧ A.length = 0 then (out ++ A ++ B, ms)  -- na == 0: Succeed
      else
        let out := out ++ [b]                            -- copy B[0]
        if B' = [] then (out ++ A, ms)                    -- nb == 0: Succeed
        else
          match A with
          | [] => (out ++ B', ms)                         -- unreachable
          | a :: A' =>
            let (k, ms) := gallopLeft lt a (fun i => B'.getD i a) B'.length 0 ms
            let bcount := k
            let out := out ++ B'.take k
            let B := B'.drop k
            if k ≠ 0 ∧ B = [] then (out ++ A ++ B, ms)    -- nb == 0: Succeed
            else
              let out := out ++ [a]                      -- copy A[0]
              if A'.length = 1 then (out ++ B ++ A', ms)  -- na == 1: CopyB
              else if acount ≥ MIN_GALLOP ∨ bcount ≥ MIN_GALLOP then
                loLoop lt fuel true mg 0 0 out A' B ms   -- next `do` iteration
              else
                let mg := mg + 1                          -- penalize leaving galloping mode
                loLoop lt fuel false mg 0 0 out A' B { ms with minGallop := mg }

/-- `merge_lo(ms, ssa, na, ssb, nb)` on runs `A` (with `na <= nb`) and `B`. -/
def mergeLo (lt : α → α → Bool) (A B : List α) (ms : MS) : List α × MS :=
  match B with
  | [] => (A, ms)                                        -- unreachable: nb > 0
  | b :: B' =>
    if B' = [] then ([b] ++ A, ms)                       -- --nb == 0: Succeed
    else if A.length = 1 then ([b] ++ B' ++ A, ms)       -- na == 1: CopyB
    else loLoop lt (A.length + B.length + 1) false ms.minGallop 0 0 [b] A B' ms

/-! ## merge_hi (`listobject.c:2473-2613`), the mirror image -/

/-- The `for (;;)` body of `merge_hi`. The model keeps the unmerged parts of A
and B reversed (`Ar`, `Br`; their heads are C's `*ssa.keys` and `*ssb.keys`) and
the merged suffix `out` already stored at the right end. -/
def hiLoop (lt : α → α → Bool) :
    Nat → Bool → Nat → Nat → Nat → List α → List α → List α → MS → List α × MS
  | 0, _, _, _, _, out, Ar, Br, ms => (Ar.reverse ++ Br.reverse ++ out, ms)
  | fuel + 1, false, mg, acount, bcount, out, Ar, Br, ms =>
    match Ar, Br with
    | a :: Ar', b :: Br' =>
      let (c, ms) := islt lt ms b a                       -- ISLT(ssb.keys[0], ssa.keys[0])
      if c then
        if Ar' = [] then (Br.reverse ++ a :: out, ms)       -- na == 0: Succeed
        else if acount + 1 ≥ mg then hiLoop lt fuel true (mg + 1) 0 0 (a :: out) Ar' Br ms
        else hiLoop lt fuel false mg (acount + 1) 0 (a :: out) Ar' Br ms
      else
        if Br'.length = 1 then (Br' ++ Ar.reverse ++ b :: out, ms)   -- nb == 1: CopyA
        else if bcount + 1 ≥ mg then hiLoop lt fuel true (mg + 1) 0 0 (b :: out) Ar Br' ms
        else hiLoop lt fuel false mg 0 (bcount + 1) (b :: out) Ar Br' ms
    | _, _ => (Ar.reverse ++ Br.reverse ++ out, ms)        -- unreachable
  | fuel + 1, true, mg, _, _, out, Ar, Br, ms =>
    let mg := mg - (if mg > 1 then 1 else 0)
    let ms := { ms with minGallop := mg }
    match Br with
    | [] => (Ar.reverse ++ out, ms)                        -- unreachable
    | b :: Br' =>
      -- k = gallop_right(ms, *ssb.keys, basea.keys, na, na-1); k = na - k
      let na := Ar.length
      let (k0, ms) := gallopRight lt b (fun i => Ar.getD (na - 1 - i) b) na (na - 1) ms
      let k := na - k0
      let acount := k
      let out := (Ar.take k).reverse ++ out
      let Ar := Ar.drop k
      if k ≠ 0 ∧ Ar = [] then (Br.reverse ++ out, ms)       -- na == 0: Succeed
      else
        let out := b :: out                                -- copy *ssb
        if Br'.length = 1 then (Br' ++ Ar.reverse ++ out, ms)  -- nb == 1: CopyA
        else
          match Ar with
          | [] => (Br'.reverse ++ out, ms)                 -- unreachable
          | a :: Ar' =>
            -- k = gallop_left(ms, *ssa.keys, baseb.keys, nb, nb-1); k = nb - k
            let nb := Br'.length
            let (k0, ms) := gallopLeft lt a (fun i => Br'.getD (nb - 1 - i) a) nb (nb - 1) ms
            let k := nb - k0
            let bcount := k
            let out := (Br'.take k).reverse ++ out
            let Br := Br'.drop k
            if k ≠ 0 ∧ Br.length = 1 then (Br ++ Ar.reverse ++ out, ms)  -- CopyA
            else if k ≠ 0 ∧ Br = [] then (Ar.reverse ++ out, ms)        -- nb == 0: Succeed
            else
              let out := a :: out                          -- copy *ssa
              if Ar' = [] then (Br.reverse ++ out, ms)      -- na == 0: Succeed
              else if acount ≥ MIN_GALLOP ∨ bcount ≥ MIN_GALLOP then
                hiLoop lt fuel true mg 0 0 out Ar' Br ms
              else
                let mg := mg + 1
                hiLoop lt fuel false mg 0 0 out Ar' Br { ms with minGallop := mg }

/-- `merge_hi(ms, ssa, na, ssb, nb)` on runs `A` and `B` (with `na >= nb`). -/
def mergeHi (lt : α → α → Bool) (A B : List α) (ms : MS) : List α × MS :=
  match A.reverse with
  | [] => (B, ms)                                        -- unreachable: na > 0
  | a :: Ar' =>
    if Ar' = [] then (B ++ [a], ms)                      -- --na == 0: Succeed
    else if B.length = 1 then (B ++ Ar'.reverse ++ [a], ms)  -- nb == 1: CopyA
    else hiLoop lt (A.length + B.length + 1) false ms.minGallop 0 0 [a] Ar' B.reverse ms

/-! ## merge_at (`listobject.c:2615-2671`) -/

/-- The data part of `merge_at(ms, i)`: merge the adjacent runs `A` and `B`. -/
def mergeAt (lt : α → α → Bool) (A B : List α) (ms : MS) : List α × MS :=
  match B with
  | [] => (A, ms)                                        -- unreachable: nb > 0
  | b0 :: _ =>
    -- Where does b start in a?
    let (k, ms) := gallopRight lt b0 (fun i => A.getD i b0) A.length 0 ms
    let pre := A.take k
    let A := A.drop k
    match A.getLast? with
    | none => (pre ++ B, ms)                             -- na == 0
    | some alast =>
      -- Where does a end in b?
      let (nb, ms) := gallopLeft lt alast (fun i => B.getD i alast) B.length (B.length - 1) ms
      if nb = 0 then (pre ++ A ++ B, ms)
      else
        let suf := B.drop nb
        let B := B.take nb
        let (m, ms) := if A.length ≤ B.length then mergeLo lt A B ms else mergeHi lt A B ms
        (pre ++ m ++ suf, ms)

/-- `merge_at` on the array: merge `arr[base:base+na]` and `arr[base+na:base+na+nb]`. -/
def mergeAtArr (lt : α → α → Bool) (base na nb : Nat) (st : List α × MS) : List α × MS :=
  let (arr, ms) := st
  let A := (arr.drop base).take na
  let B := (arr.drop (base + na)).take nb
  let (m, ms) := mergeAt lt A B ms
  (arr.take base ++ m ++ arr.drop (base + na + nb), ms)

/-! ## The merge policy: powerloop, found_new_run, merge_force_collapse -/

/-- A pending run `struct s_slice` (`listobject.c:1763-1767`): start index
(`base.keys - ms->basekeys`), length and power. -/
structure Slice where
  base : Nat
  len : Nat
  power : Nat
  deriving Repr, DecidableEq, Inhabited

/-- The `for (;;)` loop of `powerloop` (`listobject.c:2694-2710`) after
`++result`: `result` is the value after the increment. Also reports whether a
value outside `Py_ssize_t` (`>= 2**63`) was ever produced. -/
def powerIter (n : Nat) : Nat → Nat → Nat → Nat → Bool → Nat × Bool
  | 0, result, _, _, ovf => (result, ovf)
  | fuel + 1, result, a, b, ovf =>
    if a ≥ n then
      -- both quotient bits are 1
      let a := a - n
      let b := b - n
      powerIter n fuel (result + 1) (2 * a) (2 * b) (ovf || 2 * b ≥ 2 ^ 63)
    else if b ≥ n then (result, ovf)
    else powerIter n fuel (result + 1) (2 * a) (2 * b) (ovf || 2 * b ≥ 2 ^ 63)

/-- `powerloop(s1, n1, n2, n)` (`listobject.c:2678-2712`) with the overflow flag:
`a = 2*s1 + n1; b = a + n1 + n2;` then the bit loop. The fuel `n + 1` is never
exhausted (`powerloop_spec`). -/
def powerloopOvf (s1 n1 n2 n : Nat) : Nat × Bool :=
  let a := 2 * s1 + n1
  let b := a + n1 + n2
  powerIter n (n + 1) 1 a b (b ≥ 2 ^ 63)

def powerloop (s1 n1 n2 n : Nat) : Nat := (powerloopOvf s1 n1 n2 n).1

/-- The `while` loop of `found_new_run` (`listobject.c:2735-2738`): merge the
two topmost runs (`merge_at(ms, ms->n - 2)`) while the second one's power
exceeds `power`. `mergeFn base na nb` performs the data part of the merge. -/
def mergeWhile {σ : Type} (mergeFn : Nat → Nat → Nat → σ → σ) (power : Nat) :
    List Slice → σ → List Slice × σ
  | t :: u :: rest, s =>
    if u.power > power then
      mergeWhile mergeFn power (⟨u.base, u.len + t.len, u.power⟩ :: rest) (mergeFn u.base u.len t.len s)
    else (t :: u :: rest, s)
  | stk, s => (stk, s)
termination_by stk => stk.length

/-- `found_new_run(ms, n2)` (`listobject.c:2714-2743`). -/
def foundNewRun {σ : Type} (mergeFn : Nat → Nat → Nat → σ → σ) (listlen n2 : Nat)
    (stk : List Slice) (s : σ) : List Slice × σ :=
  match stk with
  | [] => ([], s)
  | top :: rest =>
    let power := powerloop top.base top.len n2 listlen
    match mergeWhile mergeFn power (top :: rest) s with
    | (t :: rest', s') => ({ t with power := power } :: rest', s')
    | ([], s') => ([], s')

/-- `merge_force_collapse(ms)` (`listobject.c:2745-2764`). -/
def forceCollapse {σ : Type} (mergeFn : Nat → Nat → Nat → σ → σ) :
    List Slice → σ → List Slice × σ
  | t :: u :: v :: rest, s =>
    if v.len < t.len then
      forceCollapse mergeFn (t :: ⟨v.base, v.len + u.len, v.power⟩ :: rest) (mergeFn v.base v.len u.len s)
    else
      forceCollapse mergeFn (⟨u.base, u.len + t.len, u.power⟩ :: v :: rest) (mergeFn u.base u.len t.len s)
  | [t, u], s => forceCollapse mergeFn [⟨u.base, u.len + t.len, u.power⟩] (mergeFn u.base u.len t.len s)
  | stk, s => (stk, s)
termination_by stk => stk.length

/-- `merge_compute_minrun(n)` (`listobject.c@3.14.7:2690-2711`). -/
def minrunLoop : Nat → Nat → Nat → Nat
  | 0, n, r => n + r
  | fuel + 1, n, r => if n ≥ MAX_MINRUN then minrunLoop fuel (n / 2) (r ||| n % 2) else n + r

def computeMinrun (n : Nat) : Nat := minrunLoop n n 0

/-! ## The main loop of `list_sort_impl` (`listobject.c:3140-3184`) -/

/-- Sorter state: the array, the merge state, the pending stack, and whether
every `assert(ms.n < MAX_MERGE_PENDING)` before a push held. -/
structure Sorter (α : Type) where
  arr : List α
  ms : MS
  stk : List Slice
  pushOk : Bool

/-- One iteration of the `do { } while (nremaining)` loop at array position
`pos` (`listobject.c:3143-3172`). -/
def sortStep (lt : α → α → Bool) (N minrun pos : Nat) (st : Sorter α) : Sorter α × Nat :=
  let nremaining := N - pos
  let (n, rest, ms) := countRun lt (st.arr.drop pos) st.ms
  -- If short, extend to min(minrun, nremaining).
  let (n, rest, ms) :=
    if n < minrun then
      let force := if nremaining ≤ minrun then nremaining else minrun
      let (rest, ms) := binarysort lt rest force n ms
      (force, rest, ms)
    else (n, rest, ms)
  let arr := st.arr.take pos ++ rest
  let (stk, (arr, ms)) := foundNewRun (mergeAtArr lt) N n st.stk (arr, ms)
  let ok := st.pushOk && decide (stk.length < MAX_MERGE_PENDING)
  ({ arr := arr, ms := ms, stk := ⟨pos, n, 0⟩ :: stk, pushOk := ok }, n)

def sortLoop (lt : α → α → Bool) (N minrun : Nat) : Nat → Nat → Sorter α → Sorter α
  | 0, _, st => st
  | fuel + 1, pos, st =>
    let (st, n) := sortStep lt N minrun pos st
    if pos + n < N ∧ n ≠ 0 then sortLoop lt N minrun fuel (pos + n) st else st

/-- The sorting part of `list_sort_impl` on `xs` (already reversed if
`reverse=True`), from `merge_init` to `merge_force_collapse`. -/
def sortCore (lt : α → α → Bool) (xs : List α) : Sorter α :=
  let N := xs.length
  let st : Sorter α := { arr := xs, ms := {}, stk := [], pushOk := true }
  if N < 2 then st
  else
    let minrun := computeMinrun N
    let st := sortLoop lt N minrun N 0 st
    let (stk, (arr, ms)) := forceCollapse (mergeAtArr lt) st.stk (st.arr, st.ms)
    { st with arr := arr, ms := ms, stk := stk }

/-- `list.sort(reverse=reverse)` on items compared with `lt`: the sorted list
and the number of `<` calls. The list is reversed before and after a stable
forward sort (`listobject.c:3132-3138`, `:3201-3202`). -/
def listSortCnt (lt : α → α → Bool) (xs : List α) (reverse : Bool) : List α × Nat :=
  if xs.length < 2 then (xs, 0)
  else
    let ys := if reverse then xs.reverse else xs
    let st := sortCore lt ys
    ((if reverse then st.arr.reverse else st.arr), st.ms.ncmp)

def listSort (lt : α → α → Bool) (xs : List α) (reverse : Bool := false) : List α :=
  (listSortCnt lt xs reverse).1

/-- `list.sort(key=f, reverse=reverse)`: the keys are computed once
(`listobject.c:3013-3024`) and sorted with the items moved in lockstep (the
`sortslice` `values` array). -/
def listSortKeyCnt {κ : Type} (f : α → κ) (lt : κ → κ → Bool) (xs : List α) (reverse : Bool) :
    List α × Nat :=
  let (r, c) := listSortCnt (fun p q : κ × α => lt p.1 q.1) (xs.map fun x => (f x, x)) reverse
  (r.map Prod.snd, c)

def listSortKey {κ : Type} (f : α → κ) (lt : κ → κ → Bool) (xs : List α) (reverse : Bool := false) :
    List α :=
  (listSortKeyCnt f lt xs reverse).1

end PyLean.ListSort
