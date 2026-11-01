import PyLean.DictSet.Props3
import PyLean.DictSet.ODict

/-!
Views over a well-formed dict, and the `OrderedDict` list operations. The list operations are stated
without the dict: `od_state` "is incremented whenever the LL changes" (`odictobject.c:500`), which is
what lets an iterator detect mutation.
-/

namespace PyLean.DictSet

open PyLean

/-- `len(d.keys())` and friends. -/
def ViewLen : Prop :=
  ∀ (K V : Type) [DecidableEq K] (hf : K → Int) (eqv : K → K → Bool) (isStr : K → Bool)
    (d : PyDict K V) (kind : ViewKind), DictInv hf eqv isStr d →
    dictviewLen (viewNew kind d) = (dictAssoc d).length
theorem viewLen_proven : ViewLen := fun _ _ _ hf eqv isStr d _ hd => len_spec d hf eqv isStr hd

/-- Iterating a view of an unchanged dict walks the dict in order. -/
def ViewIterOrder : Prop :=
  ∀ (K V : Type) [DecidableEq K] (d : PyDict K V) (k : Keys K V) (kind : ViewKind),
    d.body = .combined k → d.used = (liveEntries k).length → d.used < 2 ^ 63 →
    (dictiterToList d (dictviewIter (viewNew kind d) false)).1 = .ok k.items
theorem viewIterOrder_proven : ViewIterOrder := by
  intro K V _ d k kind hb hu hmax
  cases kind <;> exact iter_toList d k hb hu hmax _

/-- `x in d.keys()` is `x in d`. -/
def KeysViewContains : Prop :=
  ∀ (K V : Type) [DecidableEq K] (E : Env K V) (hf : K → Int) (eqv : K → K → Bool) (d : PyDict K V),
    Honest E.D hf eqv → DictInv hf eqv E.D.isStr d → ∀ x : K,
      dictkeysContains E d x = .ok (assocGet eqv (dictAssoc d) x).isSome
theorem keysViewContains_proven : KeysViewContains := by
  intro K V _ E hf eqv d H hd x
  simp only [dictkeysContains, (contains_spec H d hd x).1]

/-- Adding at either end changes the list as named and bumps `od_state`. -/
def OdictListEnds : Prop :=
  ∀ (K V : Type) (od : ODict K V) (n : Node K),
    (odictAddTail od n).nodes = od.nodes ++ [n] ∧ (odictAddTail od n).state = od.state + 1 ∧
    (odictAddHead od n).nodes = n :: od.nodes ∧ (odictAddHead od n).state = od.state + 1
theorem odictListEnds_proven : OdictListEnds := fun _ _ _ _ => ⟨rfl, rfl, rfl, rfl⟩

/-- Removing a node drops exactly that node and bumps `od_state`. -/
def OdictRemoveNode : Prop :=
  ∀ (K V : Type) [DecidableEq K] (od : ODict K V) (n : Node K),
    (odictRemoveNode od n).state = od.state + 1 ∧
    (odictRemoveNode od n).nodes = od.nodes.filter (fun m => m.id != n.id) ∧
    ∀ m ∈ (odictRemoveNode od n).nodes, m.id ≠ n.id
theorem odictRemoveNode_proven : OdictRemoveNode := by
  intro K V _ od n
  refine ⟨rfl, rfl, ?_⟩
  intro m hm
  have := (List.mem_filter.mp hm).2
  simpa using this

/-- Clearing the nodes empties the list and the fast table, and bumps `od_state`. -/
def OdictClearNodes : Prop :=
  ∀ (K V : Type) (od : ODict K V),
    (odictClearNodes od).nodes = [] ∧ (odictClearNodes od).fastNodes = [] ∧
    (odictClearNodes od).sentinel = none ∧ (odictClearNodes od).state = od.state + 1
theorem odictClearNodes_proven : OdictClearNodes := fun _ _ _ => ⟨rfl, rfl, rfl, rfl⟩

/-- An odict iterator starts at the end it says, with the current size and state. -/
def OdictIterStart : Prop :=
  ∀ (K V : Type) (od : ODict K V) (kind : IterKind) (rev : Bool),
    let di := odictiterNew od kind rev
    di.current = (if rev then od.nodes.getLast? else od.nodes.head?).map (·.key) ∧
    di.size = od.d.used ∧ di.state = od.state
theorem odictIterStart_proven : OdictIterStart := fun _ _ _ _ _ => ⟨rfl, rfl, rfl⟩

/-- A new `OrderedDict` has no nodes and an empty dict. -/
def OdictNewEmpty : Prop :=
  ∀ (K V : Type) (id : Nat), (odictNew id : ODict K V).nodes = [] ∧ (odictNew id : ODict K V).d.used = 0
theorem odictNewEmpty_proven : OdictNewEmpty := fun _ _ _ => ⟨rfl, rfl⟩

end PyLean.DictSet
