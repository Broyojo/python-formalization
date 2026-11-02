import PyLean.DiffCore
import PyLean.Accel.Bisect
import PyLean.Accel.Heap
import PyLean.Accel.Select

/-!
Differential-testing handler for `accel` cases (`"mod": "accel"`).

* `"impl"` is `"c"` or `"py"` and selects the twin for bisect and heap
  functions; `nsmallest`, `nlargest` and `merge` exist only in Python.
* `"key"` names a key function from `keyFn` (`"none"` is `key=None`).
* `"max": true` selects the `*_max` heap variant.
* Heap results are `[returned item or null, final list]`; insort results are the
  final list.
* `"size"` is the outcome of `len(iterable)` in `nsmallest`/`nlargest`: a count, or
  `{"exc": class, "msg": message}` when it raises.
-/

namespace PyLean.Accel

open Lean PyLean PyLean.Diff

/-- The key functions the difftest uses, by name (Python: `difftest/accel_diff.py`). -/
def keyFn : String → Except String (Option (Int → Int))
  | "none" => .ok none
  | "neg" => .ok (some fun x => -x)
  | "div3" => .ok (some fun x => Int.fdiv x 3)
  | "mod3" => .ok (some fun x => Int.fmod x 3)
  | "abs" => .ok (some fun x => (x.natAbs : Int))
  | k => .error s!"unknown key {k}"

def getIntList (j : Json) (k : String) : Except String (List Int) := do
  let arr ← (← field j k).getArr?
  arr.toList.mapM (·.getInt?)

def encList (l : List Int) : Json := Json.arr (l.map toJson).toArray

def encHeap (r : Option Int × List Int) : Json :=
  Json.arr #[match r.1 with | some v => toJson v | none => Json.null, encList r.2]

/-- The outcome of `len(iterable)` as `(sized, size, lenRaises)` for `nsmallest`. -/
def getSize (j : Json) (it : List Int) : Except String (Bool × Int × Option PyExc) := do
  let v ← field j "size"
  match v.getInt? with
  | .ok n => return (true, n, none)
  | .error _ =>
    let cls ← (← v.getObjVal? "exc").getStr?
    let msg ← (← v.getObjVal? "msg").getStr?
    if cls = "TypeError" ∨ cls = "AttributeError" then return (false, it.length, none)
    return (true, it.length, some (.named cls msg))

def run (fn : String) (j : Json) : Except String Json := do
  let key ← keyFn ((getStr j "key").toOption.getD "none")
  let isC := (getStr j "impl").toOption == some "c"
  match fn with
  | "bisect_left" | "bisect_right" | "insort_left" | "insort_right" =>
    let a ← getIntList j "a"
    let x ← getInt j "x"
    let lo ← getInt j "lo"
    let hi ← getOptInt j "hi"
    match fn, isC with
    | "bisect_left", true => return encPy toJson (cBisectLeft a x lo hi key)
    | "bisect_left", false => return encPy toJson (pyBisectLeft a x lo hi key)
    | "bisect_right", true => return encPy toJson (cBisectRight a x lo hi key)
    | "bisect_right", false => return encPy toJson (pyBisectRight a x lo hi key)
    | "insort_left", true => return encPy encList (cInsortLeft a x lo hi key)
    | "insort_left", false => return encPy encList (pyInsortLeft a x lo hi key)
    | "insort_right", true => return encPy encList (cInsortRight a x lo hi key)
    | _, _ => return encPy encList (pyInsortRight a x lo hi key)
  | "heappush" | "heappop" | "heapreplace" | "heappushpop" | "heapify" =>
    let heap ← getIntList j "heap"
    let lt := heapLt ((getBool j "max").toOption.getD false)
    let item := (getInt j "item").toOption.getD 0
    let r : Py (Option Int × List Int) :=
      match fn, isC with
      | "heappush", true => (fun h => (none, h)) <$> cHeappush lt heap item
      | "heappush", false => .ok (none, pyHeappush lt heap item)
      | "heappop", true => (fun (v, h) => (some v, h)) <$> cHeappop lt heap
      | "heappop", false => (fun (v, h) => (some v, h)) <$> pyHeappop lt heap
      | "heapreplace", true => (fun (v, h) => (some v, h)) <$> cHeapreplace lt heap item
      | "heapreplace", false => (fun (v, h) => (some v, h)) <$> pyHeapreplace lt heap item
      | "heappushpop", true => (fun (v, h) => (some v, h)) <$> cHeappushpop lt heap item
      | "heappushpop", false => let (v, h) := pyHeappushpop lt heap item; .ok (some v, h)
      | "heapify", true => (fun h => (none, h)) <$> cHeapify lt heap
      | _, _ => .ok (none, pyHeapify lt heap)
    return encPy encHeap r
  | "nsmallest" | "nlargest" =>
    let n ← getInt j "n"
    let it ← getIntList j "it"
    let (sized, size, lenRaises) ← getSize j it
    return encPy encList (if fn == "nsmallest" then nsmallest n it sized key size lenRaises
      else nlargest n it sized key size lenRaises)
  | "merge" =>
    let its ← (← (← field j "its").getArr?).toList.mapM (fun v => do
      (← v.getArr?).toList.mapM (·.getInt?))
    let rev ← getBool j "reverse"
    return encPy encList (merge its key rev)
  | other => throw s!"unknown fn {other}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.Accel
