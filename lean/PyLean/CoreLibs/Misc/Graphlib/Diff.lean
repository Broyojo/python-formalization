import PyLean.CoreLibs.Misc.Common
import PyLean.CoreLibs.Misc.Graphlib.Model

/-! Script runner for `misc.graphlib` cases: `{"graph": null | [[node, [preds]], ...],
"ops": [[name, args...], ...]}`, nodes are ints. The result lists every operation's outcome and
ends with a dump of the sorter's state. -/

namespace PyLean.CoreLibs.Misc.Graphlib

open Lean PyLean PyLean.Diff PyLean.CoreLibs.Misc

def rI (i : Int) : String := toString i

def dump (s : Sorter Int) : Json :=
  Json.arr #[
    jList (fun i => Json.arr #[jInt i.node, jInt i.npredecessors, jList jInt i.successors])
      s.node2info,
    jOpt (jList jInt) s.readyNodes, toJson s.npassedout, toJson s.nfinished]

def step (s : Sorter Int) (last : List Int) (op : Json) :
    Except String (Sorter Int × List Int × Json) := do
  match ← jStrAt op 0 with
  | "add" =>
    let n ← jIntAt op 1
    let ps ← jIntListAt op 2
    match add s n ps with
    | .ok s => return (s, last, encR jUnit (.ok ()))
    | .error e => return (s, last, encR jUnit (.error e))
  | "prepare" =>
    let (s, r) := prepare rI s
    return (s, last, encR jUnit r)
  | "get_ready" =>
    let (s, r) := getReady s
    let last := match r with
      | .ok l => l
      | .error _ => last
    return (s, last, encR (jList jInt) r)
  | "is_active" => return (s, last, encR jBool (isActive s))
  | "bool" => return (s, last, encR jBool (bool s))
  | "done" =>
    let (s, r) := done rI s (← jIntListAt op 1)
    return (s, last, encR jUnit r)
  | "done_ready" =>
    let (s, r) := done rI s last
    return (s, [], encR jUnit r)
  | "static_order" =>
    let (s, r) := staticOrder rI s
    return (s, last, encR (jList jInt) r)
  | o => throw s!"unknown op {o}"

def run (j : Json) : Except String Json := do
  let g ← field j "graph"
  let graph ← match g with
    | .null => pure none
    | _ => do
      let items ← jArr g
      some <$> items.mapM (fun kv => do return ((← jIntAt kv 0 : Int), (← jIntListAt kv 1)))
  match init graph with
  | .error e => return Json.mkObj [("ok", Json.arr #[encR jInt (.error e)])]
  | .ok s0 =>
    let ops ← jArr (← field j "ops")
    let mut s := s0
    let mut out : Array Json := #[]
    let mut last : List Int := []
    for op in ops do
      let (s', l, r) ← step s last op
      s := s'
      last := l
      out := out.push r
    return Json.mkObj [("ok", Json.arr (out.push (dump s)))]

end PyLean.CoreLibs.Misc.Graphlib
