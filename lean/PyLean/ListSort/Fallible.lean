import PyLean.Core
import PyLean.ListSort.Model

/-!
# `list.sort` with a comparison that can raise (CPython 3.15.2, `Objects/listobject.c`)

`Model.lean` takes `lt : α → α → Bool`, so no `goto fail` path exists there. This file is the same
code with `ISLT` (:1730) returning `Py Bool`: every `IFLT` (:1737-1738) and every `k < 0` test after a
gallop jumps to the function's failure exit, and each function returns the array as the C code leaves
it there. Definitions follow `Model.lean` branch by branch; `FallibleProps.lean` shows that with a
comparison that never raises they are those definitions, and that the array is always a permutation
of the input.

The failure states:

* `binarysort` (:1897-1950): the search for a pivot's slot moves nothing, so the array is the sorted
  prefix, the pivot in place, and the rest (:1914, :1951);
* `count_run` (:1972-2064): untouched during the ascending scan and the `IFLT(lo[0], lo[n-1])` test;
  during the descending scan the all-equal prefix and the finished equal groups are already reversed
  in place, the current group not;
* `gallop_left`/`gallop_right` (:2158, :2247) move nothing and return `-1`;
* `merge_lo` (:2461-2463) copies the rest of run A back after the merged prefix, so the array is
  `merged ++ rest of A ++ rest of B`; `merge_hi` (:2601-2603) copies the rest of B before the merged
  suffix: `rest of A ++ rest of B ++ merged`;
* `merge_at` (:2650, :2661) returns the gallop's `-1`; the main loop and `merge_force_collapse` then
  stop merging (`goto fail`, :3148-3175).

`MERGE_GETMEM` (:2358, :2490) can fail only when `PyMem_Malloc` does: its overflow test cannot fire for
`need <= len / 2` (`MergeMemSpec`), and the allocator is outside the model.
-/

namespace PyLean.ListSort

open PyLean

variable {α : Type}

/-- A comparison that may raise: `PyObject_RichCompareBool(x, y, Py_LT)` or a specialised compare. -/
abbrev PLt (α : Type) := α → α → Py Bool

/-- `ISLT(x, y)` (:1730): one call, counted whether or not it raises. -/
@[inline] def isltF (lt : PLt α) (ms : MS) (x y : α) : Py Bool × MS :=
  (lt x y, { ms with ncmp := ms.ncmp + 1 })

/-- A comparison result negated, the error passed on. -/
@[inline] def notF : Py Bool × MS → Py Bool × MS
  | (.ok c, ms) => (.ok (!c), ms)
  | (.error e, ms) => (.error e, ms)

/-- The array as it stands, the merge state, and the exception that stopped the function. -/
abbrev FRes (α : Type) := List α × MS × Option PyExc

/-! ## binarysort -/

def binLoopF (test : Nat → MS → Py Bool × MS) : Nat → Nat → Nat → MS → Py Nat × MS
  | 0, lo, _, ms => (.ok lo, ms)
  | fuel + 1, lo, hi, ms =>
    if lo < hi then
      let m := lo + (hi - lo) / 2
      match test m ms with
      | (.ok c, ms) => if c then binLoopF test fuel (m + 1) hi ms else binLoopF test fuel lo m ms
      | (.error e, ms) => (.error e, ms)
    else (.ok lo, ms)

def bsInsertF (lt : PLt α) (sorted : List α) (pivot : α) (ms : MS) : Py (List α) × MS :=
  let test := fun (m : Nat) (ms : MS) => notF (isltF lt ms pivot (sorted.getD m pivot))
  match binLoopF test (sorted.length + 1) 0 sorted.length ms with
  | (.ok l, ms) => (.ok (sorted.take l ++ pivot :: sorted.drop l), ms)
  | (.error e, ms) => (.error e, ms)

/-- A failed search leaves the pivot where it was (:1914, `goto fail` before the slide). -/
def bsLoopF (lt : PLt α) : List α → List α → MS → FRes α
  | sorted, [], ms => (sorted, ms, none)
  | sorted, p :: ps, ms =>
    match bsInsertF lt sorted p ms with
    | (.ok s, ms) => bsLoopF lt s ps ms
    | (.error e, ms) => (sorted ++ p :: ps, ms, some e)

def binarysortF (lt : PLt α) (a : List α) (n ok : Nat) (ms : MS) : FRes α :=
  let ok := if ok = 0 then 1 else ok
  let (s, ms, e) := bsLoopF lt (a.take ok) ((a.take n).drop ok) ms
  (s ++ a.drop n, ms, e)

/-! ## count_run -/

/-- `ascTake` with a failing compare: the items passed so far, the rest, untouched. -/
def ascTakeF (lt : PLt α) : α → List α → MS → List α × List α × MS × Option PyExc
  | _, [], ms => ([], [], ms, none)
  | prev, z :: rest, ms =>
    match isltF lt ms z prev with
    | (.error e, ms) => ([], z :: rest, ms, some e)
    | (.ok true, ms) => ([], z :: rest, ms, none)
    | (.ok false, ms) =>
      let (t, r, ms, er) := ascTakeF lt z rest ms
      (z :: t, r, ms, er)

/-- `descLoop` with a failing compare: on failure the current equal group `grp` has not been
reversed (`REVERSE_LAST_NEQ` runs only after the loop or on a smaller item). -/
def descLoopF (lt : PLt α) : List α → List α → α → List α → MS → List α × List α × MS × Option PyExc
  | done, grp, _, [], ms => (done ++ grp.reverse, [], ms, none)
  | done, grp, prev, z :: rest, ms =>
    match isltF lt ms z prev with
    | (.error e, ms) => (done ++ grp, z :: rest, ms, some e)
    | (.ok true, ms) => descLoopF lt (done ++ grp.reverse) [z] z rest ms
    | (.ok false, ms) =>
      match isltF lt ms prev z with
      | (.error e, ms) => (done ++ grp, z :: rest, ms, some e)
      | (.ok true, ms) => (done ++ grp.reverse, z :: rest, ms, none)
      | (.ok false, ms) => descLoopF lt done (grp ++ [z]) z rest ms

/-- `count_run(ms, slo, nremaining)`: the run length, the slice as it now stands, and the exception
(the C `-1`, :2058-2059). -/
def countRunF (lt : PLt α) (xs : List α) (ms : MS) : Nat × List α × MS × Option PyExc :=
  match xs with
  | [] => (0, [], ms, none)
  | x0 :: rest =>
    match ascTakeF lt x0 rest ms with
    | (_, _, ms, some e) => (0, xs, ms, some e)
    | (t, r, ms, none) =>
      let asc := x0 :: t
      match r with
      | [] => (asc.length, xs, ms, none)
      | y :: r' =>
        let early : Py Bool × MS :=
          if asc.length > 1 then isltF lt ms x0 (asc.getLast (by simp [asc])) else (.ok false, ms)
        match early with
        | (.error e, ms) => (0, xs, ms, some e)
        | (.ok true, ms) => (asc.length, xs, ms, none)
        | (.ok false, ms) =>
          match descLoopF lt asc.reverse [y] y r' ms with
          | (pre, r2, ms, some e) => (0, pre ++ r2, ms, some e)
          | (pre, r2, ms, none) =>
            let run := pre.reverse
            match run with
            | [] => (0, xs, ms, none)
            | w :: ws =>
              match ascTakeF lt ((w :: ws).getLast (by simp)) r2 ms with
              | (e, r3, ms, some er) => (0, run ++ e ++ r3, ms, some er)
              | (e, r3, ms, none) => (run.length + e.length, run ++ e ++ r3, ms, none)

/-! ## gallop_left / gallop_right -/

def gallopUpF (test : Nat → MS → Py Bool × MS) (hint maxofs : Nat) :
    Nat → Nat → Nat → MS → Py (Nat × Nat) × MS
  | 0, lastofs, ofs, ms => (.ok (lastofs, ofs), ms)
  | fuel + 1, lastofs, ofs, ms =>
    if ofs < maxofs then
      match test (hint + ofs) ms with
      | (.ok c, ms) =>
        if c then gallopUpF test hint maxofs fuel ofs (2 * ofs + 1) ms else (.ok (lastofs, ofs), ms)
      | (.error e, ms) => (.error e, ms)
    else (.ok (lastofs, ofs), ms)

def gallopDownF (test : Nat → MS → Py Bool × MS) (hint maxofs : Nat) :
    Nat → Nat → Nat → MS → Py (Nat × Nat) × MS
  | 0, lastofs, ofs, ms => (.ok (lastofs, ofs), ms)
  | fuel + 1, lastofs, ofs, ms =>
    if ofs < maxofs then
      match test (hint - ofs) ms with
      | (.ok c, ms) =>
        if c then (.ok (lastofs, ofs), ms) else gallopDownF test hint maxofs fuel ofs (2 * ofs + 1) ms
      | (.error e, ms) => (.error e, ms)
    else (.ok (lastofs, ofs), ms)

/-- `gallopCore` with the `-1` return of `gallop_left`/`gallop_right` (:2158-2159, :2247-2248). -/
def gallopCoreF (test : Nat → MS → Py Bool × MS) (n hint : Nat) (ms : MS) : Py Nat × MS :=
  match test hint ms with
  | (.error e, ms) => (.error e, ms)
  | (.ok c, ms) =>
    let r : Py (Nat × Nat) × MS :=
      if c then
        let maxofs := n - hint
        match gallopUpF test hint maxofs (n + 1) 0 1 ms with
        | (.ok (lastofs, ofs), ms) =>
          let ofs := if ofs > maxofs then maxofs else ofs
          (.ok (lastofs + hint + 1, ofs + hint), ms)
        | (.error e, ms) => (.error e, ms)
      else
        let maxofs := hint + 1
        match gallopDownF test hint maxofs (n + 1) 0 1 ms with
        | (.ok (lastofs, ofs), ms) =>
          let ofs := if ofs > maxofs then maxofs else ofs
          (.ok (hint + 1 - ofs, hint - lastofs), ms)
        | (.error e, ms) => (.error e, ms)
    match r with
    | (.error e, ms) => (.error e, ms)
    | (.ok (lo, hi), ms) => binLoopF test (n + 1) lo hi ms

def gallopLeftF (lt : PLt α) (key : α) (get : Nat → α) (n hint : Nat) (ms : MS) : Py Nat × MS :=
  gallopCoreF (fun i ms => isltF lt ms (get i) key) n hint ms

def gallopRightF (lt : PLt α) (key : α) (get : Nat → α) (n hint : Nat) (ms : MS) : Py Nat × MS :=
  gallopCoreF (fun i ms => notF (isltF lt ms key (get i))) n hint ms

/-! ## merge_lo, merge_hi: the `Fail` exits copy the rest of the run in the temp array back -/

/-- `loLoop` with `goto Fail`: the array is then `out ++ A ++ B` (:2461-2463). -/
def loLoopF (lt : PLt α) :
    Nat → Bool → Nat → Nat → Nat → List α → List α → List α → MS → FRes α
  | 0, _, _, _, _, out, A, B, ms => (out ++ A ++ B, ms, none)
  | fuel + 1, false, mg, acount, bcount, out, A, B, ms =>
    match A, B with
    | a :: A', b :: B' =>
      match isltF lt ms b a with
      | (.error e, ms) => (out ++ A ++ B, ms, some e)
      | (.ok c, ms) =>
        if c then
          if B' = [] then (out ++ [b] ++ A, ms, none)
          else if bcount + 1 ≥ mg then loLoopF lt fuel true (mg + 1) 0 0 (out ++ [b]) A B' ms
          else loLoopF lt fuel false mg 0 (bcount + 1) (out ++ [b]) A B' ms
        else
          if A'.length = 1 then (out ++ [a] ++ B ++ A', ms, none)
          else if acount + 1 ≥ mg then loLoopF lt fuel true (mg + 1) 0 0 (out ++ [a]) A' B ms
          else loLoopF lt fuel false mg (acount + 1) 0 (out ++ [a]) A' B ms
    | _, _ => (out ++ A ++ B, ms, none)
  | fuel + 1, true, mg, _, _, out, A, B, ms =>
    let mg := mg - (if mg > 1 then 1 else 0)
    let ms := { ms with minGallop := mg }
    match B with
    | [] => (out ++ A, ms, none)
    | b :: B' =>
      match gallopRightF lt b (fun i => A.getD i b) A.length 0 ms with
      | (.error e, ms) => (out ++ A ++ B, ms, some e)
      | (.ok k, ms) =>
        let acount := k
        let out := out ++ A.take k
        let A := A.drop k
        if k ≠ 0 ∧ A.length = 1 then (out ++ B ++ A, ms, none)
        else if k ≠ 0 ∧ A.length = 0 then (out ++ A ++ B, ms, none)
        else
          let out := out ++ [b]
          if B' = [] then (out ++ A, ms, none)
          else
            match A with
            | [] => (out ++ B', ms, none)
            | a :: A' =>
              match gallopLeftF lt a (fun i => B'.getD i a) B'.length 0 ms with
              | (.error e, ms) => (out ++ (a :: A') ++ B', ms, some e)
              | (.ok k, ms) =>
                let bcount := k
                let out := out ++ B'.take k
                let B := B'.drop k
                if k ≠ 0 ∧ B = [] then (out ++ (a :: A') ++ B, ms, none)
                else
                  let out := out ++ [a]
                  if A'.length = 1 then (out ++ B ++ A', ms, none)
                  else if acount ≥ MIN_GALLOP ∨ bcount ≥ MIN_GALLOP then
                    loLoopF lt fuel true mg 0 0 out A' B ms
                  else
                    let mg := mg + 1
                    loLoopF lt fuel false mg 0 0 out A' B { ms with minGallop := mg }

def mergeLoF (lt : PLt α) (A B : List α) (ms : MS) : FRes α :=
  match B with
  | [] => (A, ms, none)
  | b :: B' =>
    if B' = [] then ([b] ++ A, ms, none)
    else if A.length = 1 then ([b] ++ B' ++ A, ms, none)
    else loLoopF lt (A.length + B.length + 1) false ms.minGallop 0 0 [b] A B' ms

/-- `hiLoop` with `goto Fail`: the array is then `rest of A ++ rest of B ++ out` (:2601-2603). -/
def hiLoopF (lt : PLt α) :
    Nat → Bool → Nat → Nat → Nat → List α → List α → List α → MS → FRes α
  | 0, _, _, _, _, out, Ar, Br, ms => (Ar.reverse ++ Br.reverse ++ out, ms, none)
  | fuel + 1, false, mg, acount, bcount, out, Ar, Br, ms =>
    match Ar, Br with
    | a :: Ar', b :: Br' =>
      match isltF lt ms b a with
      | (.error e, ms) => (Ar.reverse ++ Br.reverse ++ out, ms, some e)
      | (.ok c, ms) =>
        if c then
          if Ar' = [] then (Br.reverse ++ a :: out, ms, none)
          else if acount + 1 ≥ mg then hiLoopF lt fuel true (mg + 1) 0 0 (a :: out) Ar' Br ms
          else hiLoopF lt fuel false mg (acount + 1) 0 (a :: out) Ar' Br ms
        else
          if Br'.length = 1 then (Br' ++ Ar.reverse ++ b :: out, ms, none)
          else if bcount + 1 ≥ mg then hiLoopF lt fuel true (mg + 1) 0 0 (b :: out) Ar Br' ms
          else hiLoopF lt fuel false mg 0 (bcount + 1) (b :: out) Ar Br' ms
    | _, _ => (Ar.reverse ++ Br.reverse ++ out, ms, none)
  | fuel + 1, true, mg, _, _, out, Ar, Br, ms =>
    let mg := mg - (if mg > 1 then 1 else 0)
    let ms := { ms with minGallop := mg }
    match Br with
    | [] => (Ar.reverse ++ out, ms, none)
    | b :: Br' =>
      let na := Ar.length
      match gallopRightF lt b (fun i => Ar.getD (na - 1 - i) b) na (na - 1) ms with
      | (.error e, ms) => (Ar.reverse ++ Br.reverse ++ out, ms, some e)
      | (.ok k0, ms) =>
        let k := na - k0
        let acount := k
        let out := (Ar.take k).reverse ++ out
        let Ar := Ar.drop k
        if k ≠ 0 ∧ Ar = [] then (Br.reverse ++ out, ms, none)
        else
          let out := b :: out
          if Br'.length = 1 then (Br' ++ Ar.reverse ++ out, ms, none)
          else
            match Ar with
            | [] => (Br'.reverse ++ out, ms, none)
            | a :: Ar' =>
              let nb := Br'.length
              match gallopLeftF lt a (fun i => Br'.getD (nb - 1 - i) a) nb (nb - 1) ms with
              | (.error e, ms) => ((a :: Ar').reverse ++ Br'.reverse ++ out, ms, some e)
              | (.ok k0, ms) =>
                let k := nb - k0
                let bcount := k
                let out := (Br'.take k).reverse ++ out
                let Br := Br'.drop k
                if k ≠ 0 ∧ Br.length = 1 then (Br ++ (a :: Ar').reverse ++ out, ms, none)
                else if k ≠ 0 ∧ Br = [] then ((a :: Ar').reverse ++ out, ms, none)
                else
                  let out := a :: out
                  if Ar' = [] then (Br.reverse ++ out, ms, none)
                  else if acount ≥ MIN_GALLOP ∨ bcount ≥ MIN_GALLOP then
                    hiLoopF lt fuel true mg 0 0 out Ar' Br ms
                  else
                    let mg := mg + 1
                    hiLoopF lt fuel false mg 0 0 out Ar' Br { ms with minGallop := mg }

def mergeHiF (lt : PLt α) (A B : List α) (ms : MS) : FRes α :=
  match A.reverse with
  | [] => (B, ms, none)
  | a :: Ar' =>
    if Ar' = [] then (B ++ [a], ms, none)
    else if B.length = 1 then (B ++ Ar'.reverse ++ [a], ms, none)
    else hiLoopF lt (A.length + B.length + 1) false ms.minGallop 0 0 [a] Ar' B.reverse ms

/-! ## merge_at and the main loop -/

/-- `merge_at` with the `k < 0` and `nb < 0` returns (:2650-2651, :2661-2662). -/
def mergeAtF (lt : PLt α) (A B : List α) (ms : MS) : FRes α :=
  match B with
  | [] => (A, ms, none)
  | b0 :: _ =>
    match gallopRightF lt b0 (fun i => A.getD i b0) A.length 0 ms with
    | (.error e, ms) => (A ++ B, ms, some e)
    | (.ok k, ms) =>
      let pre := A.take k
      let A := A.drop k
      match A.getLast? with
      | none => (pre ++ B, ms, none)
      | some alast =>
        match gallopLeftF lt alast (fun i => B.getD i alast) B.length (B.length - 1) ms with
        | (.error e, ms) => (pre ++ A ++ B, ms, some e)
        | (.ok nb, ms) =>
          if nb = 0 then (pre ++ A ++ B, ms, none)
          else
            let suf := B.drop nb
            let B := B.take nb
            let (m, ms, e) := if A.length ≤ B.length then mergeLoF lt A B ms else mergeHiF lt A B ms
            (pre ++ m ++ suf, ms, e)

/-- `merge_at` on the array; once a merge has failed, `goto fail` skips every later one. -/
def mergeAtArrF (lt : PLt α) (base na nb : Nat) (st : FRes α) : FRes α :=
  match st with
  | (arr, ms, some e) => (arr, ms, some e)
  | (arr, ms, none) =>
    let A := (arr.drop base).take na
    let B := (arr.drop (base + na)).take nb
    let (m, ms, e) := mergeAtF lt A B ms
    (arr.take base ++ m ++ arr.drop (base + na + nb), ms, e)

/-- One pass of the main loop (:3143-3172); a failing `count_run`, `binarysort` or `found_new_run`
stops the sort with the array as it stands. -/
def sortStepF (lt : PLt α) (N pos : Nat) (st : Sorter α) : Sorter α × Nat × Option PyExc :=
  let nremaining := N - pos
  match countRunF lt (st.arr.drop pos) st.ms with
  | (_, rest, ms, some e) => ({ st with arr := st.arr.take pos ++ rest, ms := ms }, 0, some e)
  | (n, rest, ms, none) =>
    let (minrun, mr) := minrunNext st.mr
    let r : Nat × List α × MS × Option PyExc :=
      if n < minrun then
        let force := if nremaining ≤ minrun then nremaining else minrun
        let (rest, ms, e) := binarysortF lt rest force n ms
        (force, rest, ms, e)
      else (n, rest, ms, none)
    match r with
    | (_, rest, ms, some e) => ({ st with arr := st.arr.take pos ++ rest, ms := ms, mr := mr }, 0, some e)
    | (n, rest, ms, none) =>
      let arr := st.arr.take pos ++ rest
      let (stk, (arr, ms, e)) := foundNewRun (mergeAtArrF lt) N n st.stk (arr, ms, none)
      let ok := st.pushOk && decide (stk.length < MAX_MERGE_PENDING)
      ({ arr := arr, ms := ms, stk := ⟨pos, n, 0⟩ :: stk, pushOk := ok, mr := mr }, n, e)

def sortLoopF (lt : PLt α) (N : Nat) : Nat → Nat → Sorter α → Sorter α × Option PyExc
  | 0, _, st => (st, none)
  | fuel + 1, pos, st =>
    match sortStepF lt N pos st with
    | (st, _, some e) => (st, some e)
    | (st, n, none) => if pos + n < N ∧ n ≠ 0 then sortLoopF lt N fuel (pos + n) st else (st, none)

def sortCoreF (lt : PLt α) (xs : List α) : Sorter α × Option PyExc :=
  let N := xs.length
  let st : Sorter α := { arr := xs, ms := {}, stk := [], pushOk := true, mr := mergeInitMr N }
  if N < 2 then (st, none)
  else
    match sortLoopF lt N N 0 st with
    | (st, some e) => (st, some e)
    | (st, none) =>
      let (stk, (arr, ms, e)) := forceCollapse (mergeAtArrF lt) st.stk (st.arr, st.ms, none)
      ({ st with arr := arr, ms := ms, stk := stk }, e)

/-- `list.sort(reverse=reverse)` with a comparison that may raise: the list afterwards, the number of
calls, and the exception. The final reversal runs on the failure path too (`fail:` precedes it,
:3200-3201). -/
def listSortCntF (lt : PLt α) (xs : List α) (reverse : Bool) : List α × Nat × Option PyExc :=
  if xs.length < 2 then (xs, 0, none)
  else
    let ys := if reverse then xs.reverse else xs
    let (st, e) := sortCoreF lt ys
    ((if reverse then st.arr.reverse else st.arr), st.ms.ncmp, e)

/-! ## `list_sort_impl` -/

/-- The key loop of `list_sort_impl` (:3013-3022): `key` is user code that sees the list under sort
(empty, `allocated == -1`, :2989-2994) and may change it. The first key that raises ends the loop. -/
def keysLoop {κ : Type} {β : Type} (key : α → β → Py κ × β) : List α → β → List κ → Py (List κ) × β
  | [], u, acc => (.ok acc.reverse, u)
  | x :: xs, u, acc =>
    match key x u with
    | (.ok k, u) => keysLoop key xs u (k :: acc)
    | (.error e, u) => (.error e, u)

/-- The list under sort as user code sees it: `list_sort_impl` empties it and sets `allocated` to
`-1` (:2989-2994); "any operation will reset it to >= 0". -/
structure LView (α : Type) where
  items : List α
  allocated : Int

def LView.during : LView α := ⟨[], -1⟩

/-- `list_sort_impl(self, NULL, reverse)` (:2965-3227) with a comparison that may raise (and, in this
model, leaves the list alone): the items afterwards and the exception. -/
def listSortImplF (lt : PLt α) (xs : List α) (reverse : Bool) : List α × Option PyExc :=
  let (r, _, e) := listSortCntF lt xs reverse
  (r, e)

/-- `list_sort_impl(self, keyfunc, reverse)` (:2965-3227) for a comparison of keys that may raise and a
key function that may raise and may change the list it sees: the items afterwards and the exception. A
failing key function goes to `keyfunc_fail` (:3204), which restores the items untouched; otherwise
the sort runs on `(key, item)` pairs, and when it ends without its own exception a list that user code
left with `allocated != -1` raises `ValueError("list modified during sort")` (:3193-3199). What user
code put in the list meanwhile is released (:3207-3217), and the list holds the sorted items again. -/
def listSortKeyImplF {κ : Type} (lt : PLt κ) (key : α → LView α → Py κ × LView α)
    (xs : List α) (reverse : Bool) : List α × Option PyExc :=
  match keysLoop key xs LView.during [] with
  | (.error e, _) => (xs, some e)
  | (.ok ks, during) =>
    let (r, _, e) := listSortCntF (fun p q : κ × α => lt p.1 q.1) (ks.zip xs) reverse
    let e := match e with
      | some e => some e
      | none => if during.allocated ≠ -1 then some (.valueError "list modified during sort") else none
    (r.map Prod.snd, e)

/-- `PyErr_BadInternalCall()`'s exception. -/
def sortSystemError : PyExc := .named "SystemError" "~bad argument to internal function"

/-- `PyList_Sort(v)` (:3231-3245): `none` is `NULL` or a non-list (`SystemError`); otherwise
`list_sort_impl(v, NULL, 0)`, with `-1` (the exception) when it returns `NULL`, else `0`. The list
afterwards is the second component. -/
def pyListSortF (lt : PLt α) (op : Option (List α)) : Py Unit × List α :=
  match op with
  | none => (.error sortSystemError, [])
  | some l =>
    match listSortImplF lt l false with
    | (r, some e) => (.error e, r)
    | (r, none) => (.ok (), r)

end PyLean.ListSort
