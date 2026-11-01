import PyLean.CoreLibs.Misc.Graphlib.Order

/-! The validation of `TopologicalSorter`: each method's guards, for every state. -/

namespace PyLean.CoreLibs.Misc.Graphlib

open PyLean

variable {α : Type} [DecidableEq α]

/-- "Raises ValueError if called without calling "prepare" previously": `get_ready`, `is_active`,
`__bool__` and `done` all raise it before `prepare` and change nothing. "Raises ValueError if called
after "prepare"": `add` raises and changes nothing. -/
def PrepareGuards : Prop :=
  ∀ (α : Type) [DecidableEq α] (r : α → String) (s : Sorter α) (n : α) (ps : List α) (l : List α),
    (s.readyNodes = none →
      getReady s = (s, .error notPrepared) ∧ isActive s = .error notPrepared ∧
      bool s = .error notPrepared ∧ done r s l = (s, .error notPrepared)) ∧
    (s.readyNodes.isSome = true →
      add s n ps = .error (.valueError "Nodes cannot be added after a call to prepare()"))

theorem prepareGuards_proven : PrepareGuards := by
  intro α _ r s n ps l
  constructor
  · intro h
    simp [getReady, isActive, bool, done, h]
  · intro h
    simp [add, h]

/-- `prepare`: "Raise ValueError if nodes have already been passed out of the sorter". Calling it
again before that recomputes nothing: `_ready_nodes` stays. A cycle is raised after `_ready_nodes` is
set, "if the user wants to catch the CycleError, that's fine, they can continue using the instance to
grab as many nodes as possible". -/
def PrepareCases : Prop :=
  ∀ (α : Type) [DecidableEq α] (r : α → String) (s : Sorter α) (ready c : List α),
    (s.npassedout > 0 →
      prepare r s = (s, .error (.valueError "cannot prepare() after starting sort"))) ∧
    (s.npassedout = 0 → s.readyNodes = some ready → findCycle s.node2info = .ok none →
      prepare r s = (s, .ok ())) ∧
    (s.npassedout = 0 → s.readyNodes = none → findCycle s.node2info = .ok (some c) →
      (prepare r s).2 = .error (cycleError r c) ∧
      (prepare r s).1.readyNodes = some (initialReady s.node2info))

theorem prepareCases_proven : PrepareCases := by
  intro α _ r s ready c
  refine ⟨?_, ?_, ?_⟩
  · intro h; simp [prepare, h]
  · intro h1 h2 h3
    simp [prepare, h1, h2, h3]
  · intro h1 h2 h3
    simp [prepare, h1, h2, h3]

/-- `done` validates each node as its docstring lists: not added, not passed out, already done. Those
are the only three failures for a state whose counters are `Dyn`'s. A failing node keeps the effect
of the nodes before it. -/
def DoneValidation : Prop :=
  ∀ (α : Type) [DecidableEq α] (r : α → String) (s : Sorter α) (ready : List α) (n : α)
    (i : NodeInfo α),
    s.readyNodes = some ready →
    (n2iGet s.node2info n = none →
      done r s [n] = ({ s with readyNodes := some ready },
        .error (.valueError s!"node {r n} was not added using add()"))) ∧
    (n2iGet s.node2info n = some i → 0 ≤ i.npredecessors →
      done r s [n] = ({ s with readyNodes := some ready },
        .error (.valueError s!"node {r n} was not passed out (still not ready)"))) ∧
    (n2iGet s.node2info n = some i → i.npredecessors = NODE_DONE →
      done r s [n] = ({ s with readyNodes := some ready },
        .error (.valueError s!"node {r n} was already marked done"))) ∧
    (Dyn s.node2info ready → ∀ j ∈ s.node2info,
      j.npredecessors = NODE_DONE ∨ j.npredecessors = NODE_OUT ∨ 0 ≤ j.npredecessors)

theorem doneValidation_proven : DoneValidation := by
  intro α _ r s ready n i hr
  refine ⟨?_, ?_, ?_, fun h => h.status⟩
  · intro h
    simp [done, hr, doneLoop, doneOne, h]
  · intro h1 h2
    have h3 : i.npredecessors ≠ NODE_OUT := by simp only [NODE_OUT]; omega
    simp [done, hr, doneLoop, doneOne, h1, h3, h2]
  · intro h1 h2
    have h3 : ¬ (NODE_DONE = NODE_OUT) := by decide
    have h4 : ¬ (0 ≤ NODE_DONE) := by decide
    simp [done, hr, doneLoop, doneOne, h1, h3, h4, h2]

/-- `is_active` and `__bool__`: "Return True if more progress can be made": exactly when some node
is passed out and not done, or some node is ready. `get_ready` hands out each ready node once: it
returns `_ready_nodes`, a second call returns `()`, and `_npassedout` counts them. -/
def ActiveReady : Prop :=
  ∀ (α : Type) [DecidableEq α] (s : Sorter α) (ready : List α),
    s.readyNodes = some ready →
    (isActive s = .ok true ↔ (s.nfinished < s.npassedout ∨ ready ≠ [])) ∧
    bool s = isActive s ∧
    (getReady s).2 = .ok ready ∧
    (getReady s).1.npassedout = s.npassedout + ready.length ∧
    (getReady (getReady s).1).2 = .ok []

theorem activeReady_proven : ActiveReady := by
  intro α _ s ready h
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · simp only [isActive, h, Except.ok.injEq, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      List.isEmpty_eq_false_iff, ne_eq]
  · simp [getReady, h]
  · simp [getReady, h]
  · simp [getReady, h]

/-- `add` builds what `_NodeInfo` promises: for every sorter built by `__init__` and `add`, node keys
are distinct, every successor is a node, and "The list can contain duplicated elements as long as
they're all reflected in the successor's npredecessors attribute": `npredecessors` is the number of
occurrences in the successor lists. -/
def AddInvariant : Prop :=
  ∀ (α : Type) [DecidableEq α] (s : Sorter α), Built s →
    (keys s.node2info).Nodup ∧
    (∀ i ∈ s.node2info, ∀ y ∈ i.successors, y ∈ keys s.node2info) ∧
    (∀ i ∈ s.node2info, i.npredecessors = inDeg s.node2info i.node)

theorem addInvariant_proven : AddInvariant := by
  intro α _ s h
  obtain ⟨w, _⟩ := built_state h
  exact ⟨w.nodup, w.closed, fun i hi => by simpa using w.deg i hi⟩

end PyLean.CoreLibs.Misc.Graphlib
