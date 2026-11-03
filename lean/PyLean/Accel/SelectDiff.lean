import PyLean.DiffCore
import PyLean.Accel.HeapqSelect

/-!
Difftest harness for `nsmallest`, `nlargest` and `merge` (`difftest/accel_diff.py`, classes
`E`, `Key`, `Src`, `It`): a concrete `SEnv` whose callbacks log every call and follow a script
(`[kind, j, action]`: the `j`-th call of that kind raises `ValueError('<kind> <j>')`, raises
`StopIteration`, returns an object whose truth test raises `TypeError('bool <kind> <j>')`, or
flips its answer), and CPython's `list.sort` for lists shorter than 64 items (one natural run
from `count_run`, extended by `binarysort`; Objects/listobject.c:1834-1968, :1972-2063,
:3080-3110), which is all the difftest exercises.
-/

namespace PyLean.Accel.SelDiff

open Lean PyLean PyLean.Diff PyLean.Accel.Heapq

/-- An element: an object id and the int it wraps. -/
structure Obj where
  id : Nat
  v : Int
  deriving DecidableEq, Inhabited, Repr

/-- `len()` of a source: no `__len__`, a count, or an exception. -/
inductive LenSpec where
  | none
  | val (n : Nat)
  | exc (cls msg : String)

/-- An iterable (`Src`, whose `__iter__` returns a fresh `It`) or an iterator (`It`). -/
inductive OSt where
  | src (name : String) (items : List Obj) (len : LenSpec)
  | it (name : String) (items : List Obj) (pos : Nat)

inductive Ev where
  | cmp (kind : String) (a b : Int)
  | one (kind : String) (a : Int)
  | named (kind name : String)

structure SW where
  ctr : List (String × Nat)
  log : List Ev
  objs : List OSt
  fresh : Nat

instance : Inhabited OSt := ⟨.it "" [] 0⟩

abbrev Script := List (String × Nat × String)

def bump (kind : String) (w : SW) : Nat × SW :=
  let j := ((w.ctr.find? (·.1 == kind)).map (·.2)).getD 0 + 1
  (j, { w with ctr := (kind, j) :: w.ctr.filter (·.1 != kind) })

def action (sc : Script) (kind : String) (j : Nat) : Option String :=
  -- the difftest builds a dict from the script, so the last entry for `(kind, j)` wins
  (sc.reverse.find? (fun (k, i, _) => k == kind && i == j)).map (·.2.2)

def logEv (e : Ev) (w : SW) : SW := { w with log := w.log ++ [e] }

/-- A comparison callback `kind` (`lt` or `eq`) on two elements, honest answer `res`. -/
def cmpCall (sc : Script) (kind : String) (a b : Obj) (res : Bool) : Eff SW PyExc Bool :=
  ⟨fun w =>
    let w := logEv (.cmp kind a.v b.v) w
    let (j, w) := bump kind w
    match action sc kind j with
    | some "raise" => (.error (.named "ValueError" s!"{kind} {j}"), w)
    | some "stop" => (.error .stopIteration, w)
    | some "boolraise" => (.error (.typeError s!"bool {kind} {j}"), w)
    | some "flip" => (.ok (!res), w)
    | _ => (.ok res, w)⟩

def keyFun : String → Option (Int → Int)
  | "neg" => some (fun x => -x)
  | "div3" => some (fun x => Int.fdiv x 3)
  | "mod3" => some (fun x => Int.fmod x 3)
  | "abs" => some (fun x => (x.natAbs : Int))
  | _ => none

/-- The `Key` callable: logs, follows the script, returns a fresh element. -/
def keyCall (sc : Script) (f : Int → Int) (x : Obj) : Eff SW PyExc Obj :=
  ⟨fun w =>
    let w := logEv (.one "key" x.v) w
    let (j, w) := bump "key" w
    match action sc "key" j with
    | some "raise" => (.error (.named "ValueError" s!"key {j}"), w)
    | some "stop" => (.error .stopIteration, w)
    | _ => (.ok ⟨w.fresh, f x.v⟩, { w with fresh := w.fresh + 1 })⟩

def objAt (w : SW) (o : Nat) : OSt := w.objs.getD o default

def oname : OSt → String
  | .src n _ _ => n
  | .it n _ _ => n

def iterF (sc : Script) (o : Nat) : Eff SW PyExc Nat := ⟨fun w =>
  let s := objAt w o
  let w := logEv (.named "iter" (oname s)) w
  let (j, w) := bump "iter" w
  match action sc "iter" j with
  | some "raise" => (.error (.named "ValueError" s!"iter {j}"), w)
  | some "stop" => (.error .stopIteration, w)
  | _ => match s with
    | .src n items _ => (.ok w.objs.length, { w with objs := w.objs ++ [.it (n ++ "'") items 0] })
    | .it _ _ _ => (.ok o, w)⟩

def nextF (sc : Script) (o : Nat) : Eff SW PyExc Obj := ⟨fun w =>
  match objAt w o with
  | .src n _ _ => (.error (.typeError s!"'Src' object is not an iterator {n}"), w)
  | .it n items pos =>
    let w := logEv (.named "next" n) w
    let (j, w) := bump "next" w
    match action sc "next" j with
    | some "raise" => (.error (.named "ValueError" s!"next {j}"), w)
    | some "stop" => (.error .stopIteration, w)
    | _ => match items[pos]? with
      | some x => (.ok x, { w with objs := w.objs.set o (.it n items (pos + 1)) })
      | none => (.error .stopIteration, w)⟩

def lenF (sc : Script) (o : Nat) : Eff SW PyExc Nat := ⟨fun w =>
  match objAt w o with
  | .it _ _ _ => (.error (.typeError "object of type 'It' has no len()"), w)
  | .src _ _ .none => (.error (.typeError "object of type 'Src' has no len()"), w)
  | .src n _ spec =>
    let w := logEv (.named "len" n) w
    let (j, w) := bump "len" w
    match action sc "len" j with
    | some "raise" => (.error (.named "ValueError" s!"len {j}"), w)
    | some "stop" => (.error .stopIteration, w)
    | _ => match spec with
      | .val k => (.ok k, w)
      | .exc c m => (.error (.named c m), w)
      | .none => (.error (.typeError ""), w)⟩

def hasLenF (o : Nat) : Eff SW PyExc Bool :=
  ⟨fun w => (.ok (match objAt w o with | .src _ _ .none => false | .src _ _ _ => true | _ => false), w)⟩

def drainIt (sc : Script) (it : Nat) : Nat → Eff SW PyExc (List Obj)
  | 0 => Eff.raise .modelFuel
  | f + 1 => do
    let r ← Eff.attempt (nextF sc it)
    match r with
    | .ok x => do
      let rest ← drainIt sc it f
      pure (x :: rest)
    | .error e => if isA builtinHier e "StopIteration" then pure [] else Eff.raise e

/-- `list(x)`: `list_extend_iter` (Objects/listobject.c:1301-1311): `iter(x)`, then
`PyObject_LengthHint(x)` (Objects/abstract.c:95-118: `__len__` if any, with `TypeError`
cleared; the test classes have no `__length_hint__`), then `next()` until `StopIteration`. -/
def toListF (sc : Script) (o : Nat) : Eff SW PyExc (List Obj) := do
  let it ← iterF sc o
  let hasLen ← hasLenF o
  if hasLen then do
    let r ← Eff.attempt (lenF sc o)
    match r with
    | .error e => if isA builtinHier e "TypeError" then pure () else Eff.raise e
    | .ok _ => pure ()
  drainIt sc it 1000

def env (sc : Script) : SEnv SW Obj Nat where
  lt a b := cmpCall sc "lt" a b (decide (a.v < b.v))
  gt a b := cmpCall sc "lt" b a (decide (b.v < a.v))     -- `a > b` is `b.__lt__(a)` for `E`
  eq a b := cmpCall sc "eq" a b (decide (a.v = b.v))
  iter := iterF sc
  next := nextF sc
  len := lenF sc
  toList := toListF sc
  hier := builtinHier

/-! ### CPython's `list.sort` below 64 items -/

/-- Reverse `l[lo:hi]`. -/
def revSlice {β : Type} (l : List β) (lo hi : Nat) : List β :=
  l.take lo ++ ((l.drop lo).take (hi - lo)).reverse ++ l.drop hi

/-- `IFLT(l[i], l[j])`. -/
def ltAt {β : Type} [Inhabited β] (lt : β → β → Eff SW PyExc Bool) (l : List β) (i j : Nat) :
    Eff SW PyExc Bool := lt (l.getD i default) (l.getD j default)

/-- The ascending scan of `count_run` from `n`: stop at the first `l[n] < l[n-1]`. -/
def ascScan {β : Type} [Inhabited β] (lt : β → β → Eff SW PyExc Bool) (l : List β) (nrem : Nat) :
    Nat → Nat → Eff SW PyExc Nat
  | 0, n => pure n
  | f + 1, n =>
    if n < nrem then do
      let c ← ltAt lt l n (n - 1)
      if c then pure n else ascScan lt l nrem f (n + 1)
    else pure n

/-- The descending scan of `count_run` (:2027-2041), reversing all-equal stretches. -/
def descScan {β : Type} [Inhabited β] (lt : β → β → Eff SW PyExc Bool) (nrem : Nat) :
    Nat → List β → Nat → Nat → Eff SW PyExc (List β × Nat × Nat)
  | 0, l, n, neq => pure (l, n, neq)
  | f + 1, l, n, neq =>
    if n < nrem then do
      let c ← ltAt lt l n (n - 1)
      if c then
        let l := if neq ≠ 0 then revSlice l (n - (neq + 1)) n else l
        descScan lt nrem f l (n + 1) 0
      else do
        let c2 ← ltAt lt l (n - 1) n
        if c2 then pure (l, n, neq)
        else descScan lt nrem f l (n + 1) (neq + 1)
    else pure (l, n, neq)

/-- `count_run`, Objects/listobject.c:1972-2063: the run it finds, made ascending in place. -/
def countRun {β : Type} [Inhabited β] (lt : β → β → Eff SW PyExc Bool) (l : List β) :
    Eff SW PyExc (List β × Nat) := do
  let nrem := l.length
  let n ← ascScan lt l nrem nrem 1
  if n = nrem then return (l, n)
  if n > 1 then
    let c ← ltAt lt l 0 (n - 1)
    if c then return (l, n)
  let l := if n > 1 then revSlice l 0 n else l
  let (l, n, neq) ← descScan lt nrem nrem l (n + 1) 0
  let l := if neq ≠ 0 then revSlice l (n - (neq + 1)) n else l
  let l := revSlice l 0 n
  let n ← ascScan lt l nrem nrem n
  return (l, n)

/-- The bisection of `binarysort` for the pivot at `ok` (:1895-1912). -/
def bisect {β : Type} [Inhabited β] (lt : β → β → Eff SW PyExc Bool) (l : List β) (pivot : β) :
    Nat → Nat → Nat → Eff SW PyExc Nat
  | 0, lo, _ => pure lo
  | f + 1, lo, hi =>
    if lo < hi then do
      let m := (lo + hi) / 2
      let c ← lt pivot (l.getD m default)
      if c then bisect lt l pivot f lo m else bisect lt l pivot f (m + 1) hi
    else pure lo

/-- `binarysort`, :1834-1928. -/
def binSort {β : Type} [Inhabited β] (lt : β → β → Eff SW PyExc Bool) (n : Nat) :
    Nat → List β → Nat → Eff SW PyExc (List β)
  | 0, l, _ => pure l
  | f + 1, l, ok =>
    if ok < n then do
      let pivot := l.getD ok default
      let pos ← bisect lt l pivot (ok + 1) 0 ok
      let l := (l.take ok).insertIdx pos pivot ++ l.drop (ok + 1)
      binSort lt n f l (ok + 1)
    else pure l

def smallSort {β : Type} [Inhabited β] (lt : β → β → Eff SW PyExc Bool) (rev : Bool) (l : List β) :
    Eff SW PyExc (List β) :=
  if l.length < 2 then pure l
  else do
    let l := if rev then l.reverse else l
    let (l, n) ← countRun lt l
    let l ← if n < l.length then binSort lt l.length l.length l (max n 1) else pure l
    pure (if rev then l.reverse else l)

def sorter : Sorter SW where
  sort {β} lt rev l :=
    match l with
    | [] => pure []
    | x :: xs => @smallSort β ⟨x⟩ lt rev (x :: xs)

/-! ### JSON -/

def getSrc (objs : List Obj) (v : Json) : Except String OSt := do
  let kind ← (← v.getObjVal? "kind").getStr?
  let name ← (← v.getObjVal? "name").getStr?
  let items ← (← (← v.getObjVal? "items").getArr?).toList.mapM (fun i => do
    let i ← i.getNat?
    pure (objs.getD i default))
  if kind == "it" then return .it name items 0
  let len ← match v.getObjVal? "len" with
    | .error _ | .ok .null => pure LenSpec.none
    | .ok l => match l.getNat? with
      | .ok k => pure (LenSpec.val k)
      | .error _ => do
        let c ← (← l.getObjVal? "exc").getStr?
        let m ← (← l.getObjVal? "msg").getStr?
        pure (LenSpec.exc c m)
  return .src name items len

def getScript (j : Json) : Except String Script :=
  match j.getObjVal? "script" with
  | .error _ | .ok .null => .ok []
  | .ok v => do
    (← v.getArr?).toList.mapM fun e => do
      let a ← e.getArr?
      let k ← (a[0]?.getD Json.null).getStr?
      let n ← (a[1]?.getD Json.null).getNat?
      let act ← (a[2]?.getD Json.null).getStr?
      pure (k, n, act)

def encEv : Ev → Json
  | .cmp k a b => Json.arr #[toJson k, toJson a, toJson b]
  | .one k a => Json.arr #[toJson k, toJson a]
  | .named k n => Json.arr #[toJson k, toJson n]

def encExc (e : Option PyExc) : Json :=
  match e with
  | none => Json.null
  | some e => Json.arr #[toJson e.className, toJson e.message]

def encOut (r : List Int) (e : Option PyExc) (w : SW) (extra : List (String × Json) := []) : Json :=
  Json.mkObj ([("r", Json.arr (r.map toJson).toArray), ("exc", encExc e),
    ("log", Json.arr (w.log.map encEv).toArray)] ++ extra)

/-- Drive the merge generator by `next()` calls, keeping what it yielded before an exception. -/
def driveMerge (E : SEnv SW Obj Nat) (impl : Bool) (key : Option (Obj → Eff SW PyExc Obj)) (rev : Bool)
    (its : List Nat) : Nat → MSt Obj Nat → SW → List Int × Option PyExc × SW × MSt Obj Nat
  | 0, st, w => ([], some .modelFuel, w, st)
  | f + 1, st, w =>
    match (mergeStep E impl key rev its st).run w with
    | (.ok (some v, st'), w') =>
      let (r, e, w'', st'') := driveMerge E impl key rev its f st' w'
      (v.v :: r, e, w'', st'')
    | (.ok (none, st'), w') => ([], none, w', st')
    | (.error e, w') => ([], some e, w', .done)

def runSel (fn : String) (isC : Bool) (j : Json) : Except String Json := do
  let vals ← (← (← field j "objs").getArr?).toList.mapM (·.getInt?)
  let objs : List Obj := vals.zipIdx.map (fun (v, i) => ⟨i, v⟩)
  let sc ← getScript j
  let E := env sc
  let keyName := (getStr j "key").toOption.getD "none"
  let key : Option (Obj → Eff SW PyExc Obj) := (keyFun keyName).map (fun f => keyCall sc f)
  if fn == "merge" then
    let srcs ← (← (← field j "srcs").getArr?).toList.mapM (getSrc objs)
    let rev ← getBool j "reverse"
    let w0 : SW := ⟨[], [], srcs, 1000000⟩
    let its := (List.range srcs.length)
    let (r, e, w, st) := driveMerge E isC key rev its 10000 .start w0
    -- one more `next()` after the end or the exception
    let after := match (mergeStep E isC key rev its st).run w with
      | (.ok (none, _), _) => Json.str "stop"
      | (.ok (some v, _), _) => toJson v.v
      | (.error e, _) => encExc (some e)
    return Json.mkObj [("ok", encOut r e w [("after", after)])]
  else
    let src ← getSrc objs (← field j "src")
    let n ← getInt j "n"
    let w0 : SW := ⟨[], [], [src], 1000000⟩
    match (nSelect E sorter isC (fn == "nlargest") 10000 n 0 key).run w0 with
    | (.ok r, w) => return Json.mkObj [("ok", encOut (r.map (·.v)) none w)]
    | (.error e, w) => return Json.mkObj [("ok", encOut [] (some e) w)]

end PyLean.Accel.SelDiff
