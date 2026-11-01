import PyLean.BytesObj.Seq.ListModel

/-!
The parts of `list.sort` in Objects/listobject.c that `PyLean.ListSort` leaves:
the `sortslice` helpers (which keep `keys` and `values` parallel), `merge_init`,
`merge_getmem`, and the specialised comparisons other than the int one.
-/

namespace PyLean.BytesObj.Seq

open PyLean

variable {κ α ρ : Type}

/-- `sortslice`, listobject.c:1669-1672: `values == NULL` is `none`. -/
structure SortSlice (κ α : Type) where
  keys : List κ
  values : Option (List α)
  deriving Repr, DecidableEq

/-- `s[i] := x` on a list; writes outside are `cUB` in the callers' hypotheses. -/
def setAt (l : List κ) (i : Nat) (x : κ) : List κ := l.set i x

/-- `sortslice_copy(s1, i, s2, j)`, listobject.c:1674-1680. -/
def sortsliceCopy (s1 : SortSlice κ α) (i : Nat) (s2 : SortSlice κ α) (j : Nat) : SortSlice κ α :=
  { keys := match s2.keys[j]? with
      | some k => s1.keys.set i k
      | none => s1.keys
    values := match s1.values, s2.values with
      | some v1, some v2 =>
        match v2[j]? with
        | some v => some (v1.set i v)
        | none => some v1
      | v1, _ => v1 }

/-- `memcpy`/`memmove` of `n` items from `src[j..]` to `dst[i..]`, for ranges that
fit; both read the source as it was. -/
def blit {β : Type} (dst : List β) (i : Nat) (src : List β) (j n : Nat) : List β :=
  dst.take i ++ (src.drop j).take n ++ dst.drop (i + n)

/-- `sortslice_memcpy(s1, i, s2, j, n)`, listobject.c:1699-1706; `sortslice_memmove`,
:1708-1715, differs only in allowing overlap, which `blit` does by reading `s2`
as a value. -/
def sortsliceMemcpy (s1 : SortSlice κ α) (i : Nat) (s2 : SortSlice κ α) (j n : Nat) :
    SortSlice κ α :=
  { keys := blit s1.keys i s2.keys j n
    values := match s1.values, s2.values with
      | some v1, some v2 => some (blit v1 i v2 j n)
      | v1, _ => v1 }

/-- `sortslice_advance(slice, n)`, listobject.c:1717-1723. -/
def sortsliceAdvance (s : SortSlice κ α) (n : Nat) : SortSlice κ α :=
  { keys := s.keys.drop n, values := s.values.map (·.drop n) }

/-- `sortslice_copy_incr(dst, src)`, listobject.c:1682-1688: one item forward. Each
returned pair is `(dst after the copy, advanced dst, advanced src)`; `sortslice_copy_decr`,
:1690-1696, is the same copy with the cursors going back, so it is a `sortsliceCopy`
at `i`, `j` as well. -/
def sortsliceCopyIncr (dst src : SortSlice κ α) : SortSlice κ α × SortSlice κ α × SortSlice κ α :=
  let d := sortsliceCopy dst 0 src 0
  (d, sortsliceAdvance d 1, sortsliceAdvance src 1)

/-- `sortslice_reverse(s, n)`, listobject.c:1956-1961: `reverse_slice` on both. -/
def sortsliceReverse (s : SortSlice κ α) (n : Nat) : SortSlice κ α :=
  let rev {β : Type} (l : List β) := (l.take n).reverse ++ l.drop n
  { keys := rev s.keys, values := s.values.map rev }

/-- `keys[i]` is the key of `values[i]`, for each `i`. -/
def Parallel (f : α → κ) (s : SortSlice κ α) : Prop :=
  match s.values with
  | none => True
  | some vs => s.keys = vs.map f

/-! ## merge_init, merge_getmem -/

/-- `MERGESTATE_TEMP_SIZE`, listobject.c:1738 (256). -/
def MERGESTATE_TEMP_SIZE : Int := 256

/-- The state `merge_init` and `merge_getmem` care about. -/
structure MergeMem where
  alloced : Int
  /-- `ms->a.values != NULL`. -/
  hasValues : Bool
  /-- `ms->a.keys` is on the heap. -/
  onHeap : Bool
  deriving Repr, DecidableEq

/-- `merge_init(ms, list_size, has_keyfunc, lo)`, listobject.c:2252-2289. -/
def mergeInit (listSize : Int) (hasKeyfunc : Bool) : MergeMem :=
  if hasKeyfunc then
    let a := (listSize + 1) / 2
    let a := if MERGESTATE_TEMP_SIZE / 2 < a then MERGESTATE_TEMP_SIZE / 2 else a
    { alloced := a, hasValues := true, onHeap := false }
  else { alloced := MERGESTATE_TEMP_SIZE, hasValues := false, onHeap := false }

/-- `merge_getmem(ms, need)`, listobject.c:2308-2337, with `MERGE_GETMEM`, :2338.
`merge_freemem`, :2295-2303, has no effect beyond the pointer it clears. -/
def mergeGetmem (ms : MergeMem) (need : Int) : Py MergeMem :=
  if need ≤ ms.alloced then .ok ms
  else
    let multiplier : Int := if ms.hasValues then 2 else 1
    if need > ssizeMax / 8 / multiplier then .error memoryError
    else .ok { ms with alloced := need, onHeap := true }

/-! ## Comparisons selected before sorting -/

/-- `safe_object_compare(v, w, ms)`, listobject.c:2787-2792. -/
def safeObjectCompare (E : ElemOps α ρ) (v w : α) : Py Bool := richBool E .lt v w

/-- `memcmp(a, b, n)` on bytes: the sign of the first difference. -/
def memcmpL : Nat → List Nat → List Nat → Int
  | 0, _, _ => 0
  | n + 1, x :: xs, y :: ys => if x < y then -1 else if y < x then 1 else memcmpL n xs ys
  | _, _, _ => 0

/-- `unsafe_latin_compare(v, w, ms)`, listobject.c:2835-2856, on 1-byte strings. -/
def unsafeLatinCompare (v w : List Nat) : Bool :=
  let len := min v.length w.length
  let res := memcmpL len v w
  if res ≠ 0 then decide (res < 0) else decide (v.length < w.length)

/-- Lexicographic `<` on code points: `unicode_compare`, which `str.__lt__` uses. -/
def strLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x < y then true else if y < x then false else strLt xs ys

/-- The tuple comparison for a sort key, `unsafe_tuple_compare(v, w, ms)`,
listobject.c:2904-2938: `first` is `ms->tuple_elem_compare`, used only when the
first pair differs. Both tuples are non-empty. -/
def unsafeTupleCompare (E : ElemOps α ρ) (first : α → α → Py Bool) (v w : List α) : Py Bool :=
  let rec go : Nat → List α → List α → Py Bool
    | i, x :: xs, y :: ys =>
      match richBool E .eq x y with
      | .ok true => go (i + 1) xs ys
      | .ok false => if i = 0 then first x y else richBool E .lt x y
      | .error e => .error e
    | _, xs, ys => .ok (xs.length < ys.length)
  go 0 v w

end PyLean.BytesObj.Seq
