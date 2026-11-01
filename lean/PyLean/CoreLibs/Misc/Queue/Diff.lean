import PyLean.CoreLibs.Misc.Common
import PyLean.CoreLibs.Misc.Queue.Model
import PyLean.CoreLibs.Misc.Sched.Diff

/-! `misc.queue` cases: `{"cls": "fifo" | "lifo" | "prio", "maxsize": n, "ops": [...]}` for `Queue`
and its subclasses, and `{"cls": "pysimple" | "csimple", "ops": [...]}` for the SimpleQueue twins.
Items are ints or strs, so `PriorityQueue` comparisons can raise. -/

namespace PyLean.CoreLibs.Misc.Queue

open Lean PyLean PyLean.Diff PyLean.CoreLibs.Misc
open PyLean.CoreLibs.Misc.Sched (TV tvLt tvJson parseTV)

def jTV : TV → Json := tvJson

def stepQ {ρ : Type} (I : Impl TV ρ) (qs : Q ρ) (op : Json) : Except String (Q ρ × Json) := do
  match ← jStrAt op 0 with
  | "put" =>
    let x ← parseTV (← jGetI op 1)
    let (q, r) := put I qs x (← jBoolAt op 2) (← jOptIntAt op 3)
    return (q, encR jUnit r)
  | "get" =>
    let (q, r) := get I qs (← jBoolAt op 1) (← jOptIntAt op 2)
    return (q, encR jTV r)
  | "put_nowait" =>
    let (q, r) := putNowait I qs (← parseTV (← jGetI op 1))
    return (q, encR jUnit r)
  | "get_nowait" =>
    let (q, r) := getNowait I qs
    return (q, encR jTV r)
  | "task_done" =>
    let (q, r) := taskDone qs
    return (q, encR jUnit r)
  | "join" => return (qs, encR jUnit (join qs))
  | "qsize" => return (qs, encR (fun (n : Nat) => toJson n) (.ok (qsize I qs)))
  | "empty" => return (qs, encR jBool (.ok (isEmpty I qs)))
  | "full" => return (qs, encR jBool (.ok (isFull I qs)))
  | "shutdown" =>
    let (q, r) := shutdown I qs (← jBoolAt op 1)
    return (q, encR jUnit r)
  | o => throw s!"unknown op {o}"

def runQ {ρ : Type} (I : Impl TV ρ) (dumpR : ρ → Json) (maxsize : Int) (ops : List Json) :
    Except String Json := do
  let mut q := init I maxsize
  let mut out : Array Json := #[]
  for op in ops do
    let (q', r) ← stepQ I q op
    q := q'
    out := out.push r
  let d := Json.arr #[dumpR q.queue, jInt q.unfinished, jBool q.isShutdown]
  return Json.mkObj [("ok", Json.arr (out.push d))]

def stepPy (s : PySQ TV) (op : Json) : Except String (PySQ TV × Json) := do
  match ← jStrAt op 0 with
  | "put" =>
    return (s.put (← parseTV (← jGetI op 1)) (← jBoolAt op 2) (← jOptIntAt op 3), encR jUnit (.ok ()))
  | "get" =>
    let (q, r) := s.get (← jBoolAt op 1) (← jOptIntAt op 2)
    return (q, encR jTV r)
  | "put_nowait" => return (s.putNowait (← parseTV (← jGetI op 1)), encR jUnit (.ok ()))
  | "get_nowait" =>
    let (q, r) := s.getNowait
    return (q, encR jTV r)
  | "qsize" => return (s, encR (fun (n : Nat) => toJson n) (.ok s.qsize))
  | "empty" => return (s, encR jBool (.ok s.isEmpty))
  | o => throw s!"unknown op {o}"

def stepC (s : List TV) (op : Json) : Except String (List TV × Json) := do
  match ← jStrAt op 0 with
  | "put" => return (cPut s (← parseTV (← jGetI op 1)), encR jUnit (.ok ()))
  | "get" =>
    let (q, r) := cGet s (← jBoolAt op 1) (← jOptIntAt op 2)
    return (q, encR jTV r)
  | "put_nowait" => return (cPut s (← parseTV (← jGetI op 1)), encR jUnit (.ok ()))
  | "get_nowait" =>
    let (q, r) := cGet s false
    return (q, encR jTV r)
  | "qsize" => return (s, encR (fun (n : Nat) => toJson n) (.ok s.length))
  | "empty" => return (s, encR jBool (.ok s.isEmpty))
  | o => throw s!"unknown op {o}"

def runCase (j : Json) : Except String Json := do
  let cls ← getStr j "cls"
  let ops ← jArr (← field j "ops")
  match cls with
  | "fifo" => runQ fifo (jList jTV) (← getInt j "maxsize") ops
  | "lifo" => runQ lifo (jList jTV) (← getInt j "maxsize") ops
  | "prio" => runQ (prio tvLt) (jList jTV) (← getInt j "maxsize") ops
  | "pysimple" =>
    let mut s : PySQ TV := PySQ.init
    let mut out : Array Json := #[]
    for op in ops do
      let (s', r) ← stepPy s op
      s := s'
      out := out.push r
    return Json.mkObj [("ok", Json.arr (out.push (Json.arr #[jList jTV s.queue, jInt s.count])))]
  | "csimple" =>
    let mut s : List TV := []
    let mut out : Array Json := #[]
    for op in ops do
      let (s', r) ← stepC s op
      s := s'
      out := out.push r
    return Json.mkObj [("ok", Json.arr (out.push (jList jTV s)))]
  | c => throw s!"unknown cls {c}"

end PyLean.CoreLibs.Misc.Queue
