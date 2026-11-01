import PyLean.DiffCore
import PyLean.ListSort.Model

/-!
Differential-testing handler for `listsort` cases (`"mod": "listsort"`).

* `"a"`: the list of ints; `"key"`: a key function name from `keyFn`
  (`"none"` is `key=None`); `"reverse"`: the `reverse` flag.
* `fn = "sort"`: `[sorted list, number of < calls]` (Python counts the calls
  with a key wrapper whose `__lt__` increments a counter).
* `fn = "plain"`: the sorted list only (Python sorts the bare ints, which
  exercises the type-specialised compares).
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

def getIntList (j : Json) (k : String) : Except String (List Int) := do
  let arr ← (← field j k).getArr?
  arr.toList.mapM (·.getInt?)

def encList (l : List Int) : Json := Json.arr (l.map toJson).toArray

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "sort" | "plain" =>
    let a ← getIntList j "a"
    let k ← getStr j "key"
    let f ← keyFn k
    let rev ← getBool j "reverse"
    let (r, c) := listSortKeyCnt f (fun x y : Int => decide (x < y)) a rev
    if fn == "sort" then return Json.mkObj [("ok", Json.arr #[encList r, toJson c])]
    else return Json.mkObj [("ok", encList r)]
  | "minrun" =>
    let n ← getNat j "n"
    return Json.mkObj [("ok", toJson (computeMinrun n))]
  | "powerloop" =>
    let s1 ← getNat j "s1"
    let n1 ← getNat j "n1"
    let n2 ← getNat j "n2"
    let n ← getNat j "n"
    return Json.mkObj [("ok", toJson (powerloop s1 n1 n2 n))]
  | other => throw s!"unknown fn {other}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.ListSort
