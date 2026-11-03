import PyLean.DiffCore
import PyLean.Accel.Bisect
import PyLean.Accel.Heap
import PyLean.Accel.HeapqModel
import PyLean.Accel.Select

/-!
Differential-testing handler for `accel` cases (`"mod": "accel"`).

* `"impl"` is `"c"` or `"py"` and selects the twin for bisect and heap
  functions; `nsmallest`, `nlargest` and `merge` exist only in Python.
* `"key"` names a key function from `keyFn` (`"none"` is `key=None`).
* `"max": true` selects the `*_max` heap variant.
* Heap functions run the effectful models of `HeapqModel.lean` with the scripted comparison
  `scriptCmp`: comparison `k` (counting from 1) logs its operands and then runs
  `"script"[k]`, a list of actions (`["append", v]`, `["pop"]`, `["clear"]`, `["set", i, v]`,
  `["flip"]`, `["raise"]`, `["boolraise"]`). `"arg"` is `"list"` (default), `"tuple"` or
  `"none"`. A heap result is always `{"ok": {"r", "exc", "heap", "log"}}` (the returned item or
  null, the exception or null, the final contents and the comparison log), or
  `{"ok": {"crash": true}}` when the C model reads or writes out of bounds.
* Insort results are the final list.
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

namespace Heapq

/-- The difftest's comparison state: how many comparisons ran, and their operands. -/
structure St where
  k : Nat
  log : List (Int × Int)

/-- An action the scripted `__lt__` performs (`difftest/accel_diff.py`, `E.__lt__`). -/
inductive Act where
  | append (v : Int)
  | pop
  | clear
  | set (i : Nat) (v : Int)
  | flip
  | raise
  | boolraise

/-- Run comparison `k`'s actions on the heap list, starting from the honest answer `res`. -/
def runActs (k : Nat) : Bool → List Act → List Int → Except PyExc Bool × List Int
  | res, [], h => (.ok res, h)
  | _, .raise :: _, h => (.error (.named "ValueError" s!"cmp {k}"), h)
  | _, .boolraise :: _, h => (.error (.typeError s!"bool {k}"), h)
  | res, .append v :: as, h => runActs k res as (h ++ [v])
  | res, .pop :: as, h => runActs k res as h.dropLast
  | res, .clear :: as, _ => runActs k res as []
  | res, .set i v :: as, h => runActs k res as (if i < h.length then h.set i v else h)
  | res, .flip :: as, h => runActs k (!res) as h

/-- The scripted comparison: `a < b` on the ints, after logging and the script's actions. -/
def scriptCmp (script : List (Nat × List Act)) : Cmp St Int := fun a b => ⟨fun w =>
  let k := w.st.k + 1
  let acts := ((script.find? (·.1 == k)).map (·.2)).getD []
  let r := runActs k (decide (a < b)) acts w.heap
  (r.1, { st := { k := k, log := w.st.log ++ [(a, b)] }, heap := r.2 })⟩

/-- A `tuple` argument (immutable; `heap` holds its items). -/
def tupleSeq : Seq (HW St Int) Int where
  len := ⟨fun w => (.ok w.heap.length, w)⟩
  get i := ⟨fun w => match listIndex i w.heap.length with
    | some j => (.ok (at! w.heap j), w)
    | none => (.error (.indexError "tuple index out of range"), w)⟩
  set _ _ := ⟨fun w => (.error (.typeError "'tuple' object does not support item assignment"), w)⟩
  append _ := ⟨fun w => (.error (.named "AttributeError" "'tuple' object has no attribute 'append'"), w)⟩
  pop := ⟨fun w => (.error (.named "AttributeError" "'tuple' object has no attribute 'pop'"), w)⟩
  truth := ⟨fun w => (.ok (!w.heap.isEmpty), w)⟩

/-- A `None` argument. -/
def noneSeq : Seq (HW St Int) Int where
  len := ⟨fun w => (.error (.typeError "object of type 'NoneType' has no len()"), w)⟩
  get _ := ⟨fun w => (.error (.typeError "'NoneType' object is not subscriptable"), w)⟩
  set _ _ := ⟨fun w => (.error (.typeError "'NoneType' object does not support item assignment"), w)⟩
  append _ := ⟨fun w => (.error (.named "AttributeError" "'NoneType' object has no attribute 'append'"), w)⟩
  pop := ⟨fun w => (.error (.named "AttributeError" "'NoneType' object has no attribute 'pop'"), w)⟩
  truth := ⟨fun w => (.ok false, w)⟩

end Heapq

def getAct (v : Json) : Except String Heapq.Act := do
  let a ← v.getArr?
  let name ← (a[0]?.getD Json.null).getStr?
  match name with
  | "append" => return .append (← (a[1]?.getD Json.null).getInt?)
  | "pop" => return .pop
  | "clear" => return .clear
  | "set" => return .set (← (a[1]?.getD Json.null).getNat?) (← (a[2]?.getD Json.null).getInt?)
  | "flip" => return .flip
  | "raise" => return .raise
  | "boolraise" => return .boolraise
  | n => throw s!"unknown action {n}"

/-- `"script"`: a list of `[k, [action, ...]]`. -/
def getScript (j : Json) : Except String (List (Nat × List Heapq.Act)) :=
  match j.getObjVal? "script" with
  | .error _ | .ok .null => .ok []
  | .ok v => do
    let arr ← v.getArr?
    arr.toList.mapM fun e => do
      let p ← e.getArr?
      let k ← (p[0]?.getD Json.null).getNat?
      let acts ← ((p[1]?.getD Json.null).getArr?)
      return (k, ← acts.toList.mapM getAct)

def encWorld (w : Heapq.HW Heapq.St Int) : List (String × Json) :=
  [("heap", encList w.heap),
   ("log", Json.arr (w.st.log.map (fun (a, b) => Json.arr #[toJson a, toJson b])).toArray)]

def encR (r : Option Int) : Json := match r with | some v => toJson v | none => Json.null

def encHeapPy (r : Except PyExc (Option Int) × Heapq.HW Heapq.St Int) : Json :=
  match r.1 with
  | .ok v => Json.mkObj ([("r", encR v), ("exc", Json.null)] ++ encWorld r.2)
  | .error e => Json.mkObj ([("r", Json.null),
      ("exc", Json.arr #[toJson e.className, toJson e.message])] ++ encWorld r.2)

def encHeapC (r : Except Heapq.CErr (Option Int) × Heapq.HW Heapq.St Int) : Json :=
  match r.1 with
  | .ok v => Json.mkObj ([("r", encR v), ("exc", Json.null)] ++ encWorld r.2)
  | .error (.py e) => Json.mkObj ([("r", Json.null),
      ("exc", Json.arr #[toJson e.className, toJson e.message])] ++ encWorld r.2)
  | .error (.crash _) => Json.mkObj [("crash", toJson true)]

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
    let mx := (getBool j "max").toOption.getD false
    let item := (getInt j "item").toOption.getD 0
    let arg := (getStr j "arg").toOption.getD "list"
    let script ← getScript j
    let lt := Heapq.scriptCmp script
    let w0 : Heapq.HW Heapq.St Int := ⟨⟨0, []⟩, heap⟩
    if isC then
      let carg : Heapq.CArg := match arg with
        | "list" => ⟨true, "list"⟩
        | "tuple" => ⟨false, "tuple"⟩
        | _ => ⟨false, "None"⟩
      let r : Except Heapq.CErr (Option Int) × Heapq.HW Heapq.St Int :=
        match fn with
        | "heappush" => let (e, w) := (Heapq.cHeappush mx lt carg item).run w0; (e.map (fun _ => none), w)
        | "heappop" => let (e, w) := (Heapq.cHeappop mx lt carg).run w0; (e.map some, w)
        | "heapreplace" => let (e, w) := (Heapq.cHeapreplace mx lt carg item).run w0; (e.map some, w)
        | "heappushpop" => let (e, w) := (Heapq.cHeappushpop mx lt carg item).run w0; (e.map some, w)
        | _ => let (e, w) := (Heapq.cHeapify mx lt carg).run w0; (e.map (fun _ => none), w)
      return Json.mkObj [("ok", encHeapC r)]
    else
      let S : Heapq.Seq (Heapq.HW Heapq.St Int) Int := match arg with
        | "list" => Heapq.listSeq
        | "tuple" => Heapq.tupleSeq
        | _ => Heapq.noneSeq
      let r : Except PyExc (Option Int) × Heapq.HW Heapq.St Int :=
        match fn with
        | "heappush" => let (e, w) := (Heapq.pyHeappush S lt mx item).run w0; (e.map (fun _ => none), w)
        | "heappop" => let (e, w) := (Heapq.pyHeappop S lt mx).run w0; (e.map some, w)
        | "heapreplace" => let (e, w) := (Heapq.pyHeapreplace S lt mx item).run w0; (e.map some, w)
        | "heappushpop" => let (e, w) := (Heapq.pyHeappushpop S lt mx item).run w0; (e.map some, w)
        | _ => let (e, w) := (Heapq.pyHeapify S lt mx).run w0; (e.map (fun _ => none), w)
      return Json.mkObj [("ok", encHeapPy r)]
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
