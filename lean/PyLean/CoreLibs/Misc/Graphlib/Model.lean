import PyLean.Core

/-!
`Lib/graphlib.py`, CPython 3.14.7: `TopologicalSorter`.

Nodes are an abstract type `α` with decidable equality, which stands for hashable objects whose
`__eq__`/`__hash__` are lawful. `_node2info` is a Python dict, so it is an association list in
insertion order, keyed by `NodeInfo.node`. A method that mutates and then raises returns the
mutated state next to the exception (`Sorter α × Py β`). `r` renders `{node!r}`.
-/

namespace PyLean.CoreLibs.Misc.Graphlib

open PyLean

/-- `_NODE_OUT`, Lib/graphlib.py:5. -/
def NODE_OUT : Int := -1
/-- `_NODE_DONE`, Lib/graphlib.py:6. -/
def NODE_DONE : Int := -2

/-- `_NodeInfo`, Lib/graphlib.py:9-23. -/
structure NodeInfo (α : Type) where
  node : α
  npredecessors : Int
  successors : List α
  deriving Repr, DecidableEq

/-- `_NodeInfo.__init__`, Lib/graphlib.py:12-23. -/
def NodeInfo.init {α : Type} (node : α) : NodeInfo α :=
  { node, npredecessors := 0, successors := [] }

/-- The instance attributes of `TopologicalSorter`, Lib/graphlib.py:44-48. -/
structure Sorter (α : Type) where
  node2info : List (NodeInfo α)
  readyNodes : Option (List α)
  npassedout : Nat
  nfinished : Nat
  deriving Repr, DecidableEq

variable {α : Type} [DecidableEq α]

/-- `self._node2info.get(node)`. -/
def n2iGet (m : List (NodeInfo α)) (k : α) : Option (NodeInfo α) :=
  m.find? (fun i => decide (i.node = k))

/-- Update the `_NodeInfo` of `k` in place. -/
def n2iMod (m : List (NodeInfo α)) (k : α) (f : NodeInfo α → NodeInfo α) : List (NodeInfo α) :=
  m.map (fun i => if i.node = k then f i else i)

/-- `TopologicalSorter._get_nodeinfo`, Lib/graphlib.py:54-57. The returned object is what the
caller goes on mutating, so here the caller uses `n2iMod`. -/
def getNodeinfo (m : List (NodeInfo α)) (node : α) : List (NodeInfo α) :=
  match n2iGet m node with
  | some _ => m
  | none => m ++ [NodeInfo.init node]

/-- The `for pred in predecessors` loop of `add`, Lib/graphlib.py:82-84. -/
def addEdges (node : α) (m : List (NodeInfo α)) (preds : List α) : List (NodeInfo α) :=
  preds.foldl
    (fun m pred =>
      n2iMod (getNodeinfo m pred) pred (fun i => { i with successors := i.successors ++ [node] }))
    m

/-- `TopologicalSorter.add`, Lib/graphlib.py:59-84. -/
def add (s : Sorter α) (node : α) (preds : List α) : Py (Sorter α) :=
  if s.readyNodes.isSome then
    .error (.valueError "Nodes cannot be added after a call to prepare()")
  else
    let m := n2iMod (getNodeinfo s.node2info node) node
      (fun i => { i with npredecessors := i.npredecessors + preds.length })
    .ok { s with node2info := addEdges node m preds }

/-- A sorter with nothing added, the first four lines of `__init__`, Lib/graphlib.py:45-48. -/
def Sorter.empty : Sorter α :=
  { node2info := [], readyNodes := none, npassedout := 0, nfinished := 0 }

/-- `TopologicalSorter.__init__`, Lib/graphlib.py:44-52. `none` is `graph=None`. -/
def init (graph : Option (List (α × List α))) : Py (Sorter α) :=
  match graph with
  | none => .ok Sorter.empty
  | some g => g.foldlM (fun s kv => add s kv.1 kv.2) Sorter.empty

/-- The `while stack:` backtracking loop of `_find_cycle`, Lib/graphlib.py:227-239. `frames` is
`stack` and `itstack` zipped, top first, each frame holding the successors its iterator has not
produced yet. `none` is the `else: break` exit. -/
def backtrack : List (α × List α) → Option (α × List (α × List α))
  | [] => none
  | (n, s :: rest) :: fr => some (s, (n, rest) :: fr)
  | (_, []) :: fr => backtrack fr

/-- `stack[node2stacki[node]:] + [node]`, Lib/graphlib.py:217, on top-first frames. -/
def cycleOf (frames : List (α × List α)) (node : α) : List α :=
  node :: (((frames.map (·.1)).takeWhile (· ≠ node)).reverse ++ [node])

/-- The successors of `node`, `n2i[node].successors`. -/
def succs (m : List (NodeInfo α)) (node : α) : List α :=
  match n2iGet m node with
  | some i => i.successors
  | none => []

/-- The `while True:` loop of `_find_cycle`, Lib/graphlib.py:214-239. `node in node2stacki` is
membership in `frames`. Returns the updated `seen`, or the cycle. -/
def walk (m : List (NodeInfo α)) :
    Nat → α → List (α × List α) → List α → Py (List α ⊕ List α)
  | 0, _, _, _ => .error .modelFuel
  | fuel + 1, node, frames, seen =>
    if node ∈ seen then
      if node ∈ frames.map (·.1) then
        .ok (.inr (cycleOf frames node))
      else
        match backtrack frames with
        | some (node', frames') => walk m fuel node' frames' seen
        | none => .ok (.inl seen)
    else
      let seen := node :: seen
      let frames := (node, succs m node) :: frames
      match backtrack frames with
      | some (node', frames') => walk m fuel node' frames' seen
      | none => .ok (.inl seen)

/-- Enough steps for `walk`: every step pushes a node or consumes a successor. -/
def walkFuel (m : List (NodeInfo α)) : Nat :=
  m.foldl (fun acc i => acc + i.successors.length + 1) 1

/-- The `for node in n2i:` loop of `_find_cycle`, Lib/graphlib.py:210-213. -/
def forNodes (m : List (NodeInfo α)) : List (NodeInfo α) → List α → Py (Option (List α))
  | [], _ => .ok none
  | i :: rest, seen =>
    if i.node ∈ seen then forNodes m rest seen
    else
      match walk m (walkFuel m) i.node [] seen with
      | .error e => .error e
      | .ok (.inr c) => .ok (some c)
      | .ok (.inl seen) => forNodes m rest seen

/-- `TopologicalSorter._find_cycle`, Lib/graphlib.py:203-240. -/
def findCycle (m : List (NodeInfo α)) : Py (Option (List α)) := forNodes m m []

/-- `CycleError("nodes are in a cycle", cycle)`; `str()` of an exception with two arguments is
the repr of the args tuple. -/
def cycleError (r : α → String) (cycle : List α) : PyExc :=
  .named "CycleError" s!"('nodes are in a cycle', [{", ".intercalate (cycle.map r)}])"

/-- `[i.node for i in self._node2info.values() if i.npredecessors == 0]`, Lib/graphlib.py:101-103. -/
def initialReady (m : List (NodeInfo α)) : List α :=
  (m.filter (fun i => i.npredecessors = 0)).map (·.node)

/-- `TopologicalSorter.prepare`, Lib/graphlib.py:86-110. -/
def prepare (r : α → String) (s : Sorter α) : Sorter α × Py Unit :=
  if s.npassedout > 0 then (s, .error (.valueError "cannot prepare() after starting sort"))
  else
    let s := match s.readyNodes with
      | none => { s with readyNodes := some (initialReady s.node2info) }
      | some _ => s
    match findCycle s.node2info with
    | .error e => (s, .error e)
    | .ok (some c) => (s, .error (cycleError r c))
    | .ok none => (s, .ok ())

/-- "prepare() must be called first", Lib/graphlib.py:123, :149, :168. -/
def notPrepared : PyExc := .valueError "prepare() must be called first"

/-- `TopologicalSorter.get_ready`, Lib/graphlib.py:112-136. -/
def getReady (s : Sorter α) : Sorter α × Py (List α) :=
  match s.readyNodes with
  | none => (s, .error notPrepared)
  | some ready =>
    let m := ready.foldl (fun m n => n2iMod m n (fun i => { i with npredecessors := NODE_OUT }))
      s.node2info
    ({ s with node2info := m, readyNodes := some [], npassedout := s.npassedout + ready.length },
      .ok ready)

/-- `TopologicalSorter.is_active`, Lib/graphlib.py:138-150. -/
def isActive (s : Sorter α) : Py Bool :=
  match s.readyNodes with
  | none => .error notPrepared
  | some ready => .ok (decide (s.nfinished < s.npassedout) || !ready.isEmpty)

/-- `TopologicalSorter.__bool__`, Lib/graphlib.py:152-153. -/
def bool (s : Sorter α) : Py Bool := isActive s

/-- The `for successor in nodeinfo.successors:` loop of `done`, Lib/graphlib.py:195-199. -/
def releaseSuccs (m : List (NodeInfo α)) (ready : List α) (succs : List α) :
    List (NodeInfo α) × List α :=
  succs.foldl
    (fun (st : List (NodeInfo α) × List α) successor =>
      let m := n2iMod st.1 successor (fun i => { i with npredecessors := i.npredecessors - 1 })
      match n2iGet m successor with
      | some i => if i.npredecessors = 0 then (m, st.2 ++ [successor]) else (m, st.2)
      | none => (m, st.2))
    (m, ready)

/-- One iteration of the `for node in nodes:` loop of `done`, Lib/graphlib.py:172-200. -/
def doneOne (r : α → String) (s : Sorter α) (ready : List α) (node : α) :
    Py (Sorter α × List α) :=
  match n2iGet s.node2info node with
  | none => .error (.valueError s!"node {r node} was not added using add()")
  | some nodeinfo =>
    let stat := nodeinfo.npredecessors
    if stat ≠ NODE_OUT ∧ stat ≥ 0 then
      .error (.valueError s!"node {r node} was not passed out (still not ready)")
    else if stat ≠ NODE_OUT ∧ stat = NODE_DONE then
      .error (.valueError s!"node {r node} was already marked done")
    else if stat ≠ NODE_OUT then
      .error (.assertionError s!"node {r node}: unknown status {stat}")
    else
      let m := n2iMod s.node2info node (fun i => { i with npredecessors := NODE_DONE })
      let (m, ready) := releaseSuccs m ready nodeinfo.successors
      .ok ({ s with node2info := m, nfinished := s.nfinished + 1 }, ready)

/-- The `for node in nodes:` loop of `done`. Nodes processed before a failing one stay processed,
so the exception comes back with the state reached. -/
def doneLoop (r : α → String) : List α → Sorter α → List α → Sorter α × Py Unit
  | [], s, ready => ({ s with readyNodes := some ready }, .ok ())
  | node :: rest, s, ready =>
    match doneOne r s ready node with
    | .error e => ({ s with readyNodes := some ready }, .error e)
    | .ok (s, ready) => doneLoop r rest s ready

/-- `TopologicalSorter.done`, Lib/graphlib.py:155-200. -/
def done (r : α → String) (s : Sorter α) (nodes : List α) : Sorter α × Py Unit :=
  match s.readyNodes with
  | none => (s, .error notPrepared)
  | some ready => doneLoop r nodes s ready

/-- The `while self.is_active():` loop of `static_order`, Lib/graphlib.py:252-255. The accumulator
collects what `yield from` has produced. -/
def staticLoop (r : α → String) : Nat → Sorter α → List α → Sorter α × Py (List α)
  | 0, s, _ => (s, .error .modelFuel)
  | fuel + 1, s, acc =>
    match isActive s with
    | .error e => (s, .error e)
    | .ok false => (s, .ok acc)
    | .ok true =>
      match getReady s with
      | (s, .error e) => (s, .error e)
      | (s, .ok group) =>
        match done r s group with
        | (s, .error e) => (s, .error e)
        | (s, .ok ()) => staticLoop r fuel s (acc ++ group)

/-- `TopologicalSorter.static_order`, Lib/graphlib.py:242-255, run to exhaustion. The loop body
runs at most once per node, plus the exit test. -/
def staticOrder (r : α → String) (s : Sorter α) : Sorter α × Py (List α) :=
  match prepare r s with
  | (s, .error e) => (s, .error e)
  | (s, .ok ()) => staticLoop r (s.node2info.length + 1) s []

end PyLean.CoreLibs.Misc.Graphlib
