import PyLean.DiffCore
import PyLean.ListSort.Model
import PyLean.ListSort.Compare
import PyLean.ListSort.Minrun
import PyLean.ListSort.FallibleBridge
import PyLean.ListSort.Modified

/-!
Differential-testing handler for `listsort` cases (`"mod": "listsort"`).

* `"a"`: the list of ints; `"key"`: a key function name from `keyFn`
  (`"none"` is `key=None`); `"reverse"`: the `reverse` flag.
* `fn = "sort"`: `[sorted list, number of < calls]` (Python counts the calls
  with a key wrapper whose `__lt__` increments a counter).
* `fn = "plain"`: the sorted list only (Python sorts the bare ints, which
  exercises the type-specialised compares; the model uses `selectCompare`, the
  digit-level model of the same selection).
* `fn = "evil"`: `[result list, number of < calls]` for an inconsistent `__lt__`
  (`"mode"`, `"m"`, see `evilLt`), which reaches the branches a consistent
  comparison cannot ("na == 0 is impossible now if the comparison function is
  consistent"). It backs the properties quantified over every comparison.
* `fn = "runs"`: the length of every run the main loop pushes, for shuffled distinct
  ints. Python reads them off the sequence of comparisons, so this observes
  `minrun_next` directly in the real interpreter.
* `fn = "objcmp"`: a two-item list of objects whose `__lt__` and `__gt__` answer as
  `"lt"` and `"gt"` say, which is one call of `unsafe_object_compare`.
* `fn = "minrun"`, `"powerloop"`: the helpers on their own (Python reimplements
  them line by line; they are not reachable from Python otherwise).
-/

namespace PyLean.ListSort

open Lean PyLean PyLean.Diff

/-- Key functions used by the difftest (Python: `difftest/listsort_diff.py`). -/
def keyFn : String → Except String (Int → Int)
  | "none" => .ok id
  | "neg" => .ok (fun x => -x)
  | "div3" => .ok (fun x => Int.fdiv x 3)
  | "mod7" => .ok (fun x => Int.fmod x 7)
  | "abs" => .ok (fun x => (x.natAbs : Int))
  | k => .error s!"unknown key {k}"

/-- Inconsistent comparisons (Python: `EVIL` in `difftest/listsort_diff.py`).
`noisy` is `<` with a pseudo-random sparse set of pairs flipped, `hash` has
nothing to do with the order of the values. -/
def evilLt (mode : String) (m : Int) (x y : Int) : Bool :=
  match mode with
  | "noisy" => decide (x < y) != decide ((x * y + x + 3 * y) % m = 0)
  | _ => decide (((7 * x + 13 * y + x * y) % m) * 2 < m)

def getIntList (j : Json) (k : String) : Except String (List Int) := do
  let arr ← (← field j k).getArr?
  arr.toList.mapM (·.getInt?)

def encList (l : List Int) : Json := Json.arr (l.map toJson).toArray

/-- The lengths of the runs the main loop pushes, read off `sortStep`. -/
def sortRuns {α : Type} (lt : α → α → Bool) (N : Nat) : Nat → Nat → Sorter α → List Nat
  | 0, _, _ => []
  | fuel + 1, pos, st =>
    let (st, n) := sortStep lt N pos st
    n :: (if pos + n < N ∧ n ≠ 0 then sortRuns lt N fuel (pos + n) st else [])

/-- The `__lt__` or `__gt__` of `difftest/listsort_diff.py`: `RES` there. -/
def richOf : String → Except String (Py (RichRes Bool))
  | "true" => .ok (.ok (.bool true))
  | "false" => .ok (.ok (.bool false))
  | "notimpl" => .ok (.ok .notImplemented)
  | "raise" => .ok (.error (.valueError "cmp"))
  | "one" | "full" => .ok (.ok (.other true))
  | "zero" | "empty" | "none" => .ok (.ok (.other false))
  | "badbool" => .ok (.ok (.other false))
  | m => .error s!"unknown compare result {m}"

/-- `PyObject_IsTrue` on the objects of `richOf`: the only falsy-looking one that raises
is `badbool`. -/
def isTrueOf (mode : String) (o : Bool) : Py Bool :=
  if mode == "badbool" then .error (.valueError "bool") else .ok o

/-- `PyObject_RichCompareBool(v, w, Py_LT)` after `__lt__` said `NotImplemented`:
`do_richcompare` tries the reflected `w.__gt__(v)`, then raises. -/
def fallbackOf (gt : String) (rich : Py (RichRes Bool)) : Py Bool :=
  match rich with
  | .ok .notImplemented => .error (.typeError "'<' not supported between instances of 'O' and 'O'")
  | .error e => .error e
  | .ok (.bool b) => .ok b
  | .ok (.other o) => isTrueOf gt o

/-- What the twin's `M.__lt__` does to the list it sorts: `add` is `append(0)`, `clear` is `clear()`
(nothing on the empty list without an array that `list_sort_impl` leaves), `pop` is `pop()` on a
non-empty list (the generator only pops after an `add`), which frees the array when it empties it. -/
def viewEff (name : String) (v : LView Int) : LView Int :=
  match name with
  | "add" => { items := v.items ++ [0], allocated := max v.allocated (v.items.length + 1 : Int) }
  | "clear" => if v.items = [] ∧ v.allocated ≤ 0 then v else { items := [], allocated := 0 }
  | "pop" =>
    let items := v.items.dropLast
    { items := items, allocated := if items = [] then 0 else v.allocated }
  | _ => v

/-- The effects of the call number `at`, in order. -/
def callEff (at_ : Nat) (effs : List String) : Nat → LView Int → LView Int := fun k v =>
  if k = at_ then effs.foldl (fun v e => viewEff e v) v else v

def encExc : Option PyExc → Json
  | none => Json.null
  | some e => toJson e.className

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "sort" | "plain" =>
    let a ← getIntList j "a"
    let k ← getStr j "key"
    let f ← keyFn k
    let rev ← getBool j "reverse"
    if fn == "sort" then
      let (r, c) := listSortKeyCnt f (fun x y : Int => decide (x < y)) a rev
      return Json.mkObj [("ok", Json.arr #[encList r, toJson c])]
    else
      let bounded := allCompact (a.map f)
      let (r, _) := listSortKeyCnt f (selectCompare bounded) a rev
      return Json.mkObj [("ok", encList r)]
  | "raise" =>
    let a ← getIntList j "a"
    let bad ← getInt j "bad"
    let rev ← getBool j "reverse"
    let lt : PLt Int := fun x y => if x = bad ∨ y = bad then .error (.valueError "lt") else .ok (decide (x < y))
    let (r, c, e) := listSortCntF lt a rev
    return Json.mkObj [("ok", Json.arr #[encList r, toJson c, toJson e.isSome])]
  | "keyraise" =>
    let a ← getIntList j "a"
    let bad ← getInt j "bad"
    let mut' ← getBool j "mut"
    let rev ← getBool j "reverse"
    -- the twin's key: append 0 to the list it sorts (when `mut`), then raise on `bad`
    let key : Int → LView Int → Py Int × LView Int := fun x u =>
      let u := if mut' then ({ items := u.items ++ [0], allocated := 4 } : LView Int) else u
      if x = bad then (.error (.named "KeyError" "~key"), u) else (.ok x, u)
    let (r, e) := listSortKeyImplF (pureLt (fun x y : Int => decide (x < y))) key a rev
    let en : Json := match e with
      | none => Json.null
      | some ex => toJson ex.className
    return Json.mkObj [("ok", Json.arr #[encList r, en])]
  | "cmpmut" =>
    let a ← getIntList j "a"
    let bad ← getInt j "bad"
    let rev ← getBool j "reverse"
    let at_ ← getNat j "at"
    let effs ← (← (← field j "eff").getArr?).toList.mapM (fun e => e.getStr?)
    let lt : PLt Int := fun x y =>
      if x = bad ∨ y = bad then .error (.named "KeyError" "~bad") else .ok (decide (x < y))
    match ← getBool j "key" with
    | false =>
      let (r, e) := listSortImplFx lt (callEff at_ effs) a rev
      return Json.mkObj [("ok", Json.arr #[encList r, encExc e])]
    | true =>
      let kmut ← getBool j "kmut"
      let kbad ← getInt j "kbad"
      let key : Int → LView Int → Py Int × LView Int := fun x u =>
        let u := if kmut then viewEff "add" u else u
        if x = kbad then (.error (.named "IndexError" "~key"), u) else (.ok x, u)
      let (r, e) := listSortKeyImplFx lt key (callEff at_ effs) a rev
      return Json.mkObj [("ok", Json.arr #[encList r, encExc e])]
  | "evil" =>
    let a ← getIntList j "a"
    let mode ← getStr j "mode"
    let m ← getInt j "m"
    let rev ← getBool j "reverse"
    let (r, c) := listSortCnt (evilLt mode m) a rev
    return Json.mkObj [("ok", Json.arr #[encList r, toJson c])]
  | "runs" =>
    let a ← getIntList j "a"
    let N := a.length
    let lt := fun x y : Int => decide (x < y)
    let st : Sorter Int := { arr := a, ms := {}, stk := [], pushOk := true, mr := mergeInitMr N }
    let rs := if N < 2 then [] else sortRuns lt N N 0 st
    return Json.mkObj [("ok", Json.arr (rs.map toJson).toArray)]
  | "objcmp" =>
    let ltm ← getStr j "lt"
    let gtm ← getStr j "gt"
    let rich ← richOf ltm
    let grich ← richOf gtm
    return encPy (fun (r : List Int) => encList r)
      ((fun b => listSort (fun _ _ : Int => b) [0, 1]) <$>
        unsafeObjectCompare true rich (isTrueOf ltm) (fallbackOf gtm grich))
  | "minrun" =>
    let n ← getNat j "n"
    let k ← getNat j "k"
    return Json.mkObj [("ok", Json.arr (((List.range k).map (minrunAt n)).map toJson).toArray)]
  | "powerloop" =>
    let s1 ← getNat j "s1"
    let n1 ← getNat j "n1"
    let n2 ← getNat j "n2"
    let n ← getNat j "n"
    return Json.mkObj [("ok", toJson (powerloop s1 n1 n2 n))]
  | other => throw s!"unknown fn {other}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.ListSort
