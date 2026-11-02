import PyLean.DictSet.DictProps2
import PyLean.DictSet.ODictPy
import PyLean.DictSet.Managed

/-!
The refuted properties. Each quantifies over every key protocol that keeps the `__hash__` and
`__eq__` contract (`Honest`), so nothing is assumed about the keys, and each state is reached by
operations from an empty object rather than written down by hand. A counterexample is then a
real program, the one in the matching `bugs/` record.
-/

namespace PyLean.DictSet

open PyLean

/-- All keys equal, one hash: `0` plays an exact `str`, every other number a `str` subclass
instance equal to it. -/
def strSubProto : Proto Nat (PyDict Nat Nat) :=
  { hash := fun _ => .ok 5
    isStr := fun k => k == 0
    isStrLike := fun _ => true
    strEq := fun _ _ => true
    reprStr := fun _ => ""
    repr := fun _ => .ok ""
    typeName := fun _ => ""
    eq := fun _ _ s => (.ok true, s) }

theorem strSubProto_honest : Honest strSubProto (fun _ => 5) (fun _ _ => true) :=
  { hash_ok := fun _ => rfl
    eq_ok := fun _ _ _ => rfl
    str_eq := fun _ _ _ _ => rfl
    refl := fun _ => rfl
    symm := fun _ _ => rfl
    trans := fun _ _ _ _ _ => rfl
    hash_cons := fun _ _ _ => rfl }

/-- `dict.setdefault` never dereferences NULL on a fresh instance `__dict__`, whatever the class's
shared keys hold. -/
def SetdefaultNoCrash : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (attrs : List K) (key : K) (dflt : V),
      (dictSetdefault P key dflt (newDictWithSharedKeys 1 (dictNewKeysForClass P attrs))).1
        ≠ .error (crash "")

theorem setdefaultNoCrash_refuted : ¬SetdefaultNoCrash := by
  intro h
  exact h Nat Nat strSubProto _ _ strSubProto_honest [0] 1 7 (by decide +kernel)

/-- Distinct ints: `hash(n)` is `n`. -/
def intProto : Proto Nat (PyDict Nat Nat) :=
  { hash := fun k => .ok k
    isStr := fun _ => false
    isStrLike := fun _ => false
    strEq := fun a b => a == b
    reprStr := fun _ => ""
    repr := fun _ => .ok ""
    typeName := fun _ => ""
    eq := fun a b s => (.ok (a == b), s) }

theorem intProto_honest : Honest intProto (fun k => (k : Int)) (fun a b => a == b) :=
  { hash_ok := fun _ => rfl
    eq_ok := fun _ _ _ => rfl
    str_eq := fun _ _ h _ => Bool.noConfusion h
    refl := fun a => beq_self_eq_true a
    symm := fun a b => by
      by_cases h : a = b
      · subst h; rfl
      · have h' : b ≠ a := fun x => h x.symm
        show (a == b) = (b == a)
        rw [beq_false_of_ne h, beq_false_of_ne h']
    trans := fun a b c h1 h2 => by
      have e1 : a = b := beq_iff_eq.mp h1
      have e2 : b = c := beq_iff_eq.mp h2
      subst e1
      subst e2
      exact beq_self_eq_true _
    hash_cons := fun a b h => by
      have e : a = b := beq_iff_eq.mp h
      subst e
      rfl }

/-- One step of a program using an `OrderedDict` and the `dict` underneath it. -/
inductive OdStep (K V : Type) where
  | set (k : K) (v : V)
  /-- `dict.popitem(od)`. -/
  | rawPopitem

def odRun {K V : Type} [DecidableEq K] (P : Proto K (PyDict K V)) :
    List (OdStep K V) → ODict K V → ODict K V
  | [], od => od
  | .set k v :: rest, od => odRun P rest (odictSetItem P k v od).2
  | .rawPopitem :: rest, od => odRun P rest (onDict dictPopitem od).2

/-- Does iterating `od`, for at most `n` steps, stay within the nodes it has? -/
def odIterWithin0 {K V : Type} [DecidableEq K] (P : Proto K (PyDict K V)) (n : Nat) (od : ODict K V) : Bool :=
  match (odictiterTake P n od (odictiterNew od .key false) []).1 with
  | .ok l => decide (l.length ≤ od.nodes.length)
  | .error _ => true

/-- After any program of `od[k] = v` and `dict.popitem(od)`, `od.popitem()` does not crash, and
iteration yields no more items than the linked list has. -/
def OdictNoStaleNode : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (steps : List (OdStep K V)) (n : Nat),
      let od := odRun P steps (odictNew 1)
      (odictPopitem P true od).1 ≠ .error (crash "") ∧ odIterWithin0 P n od = true

theorem odictNoStaleNode_refuted : ¬OdictNoStaleNode := by
  intro h
  have := h Nat Nat intProto _ _ intProto_honest [.set 0 0, .set 1 1, .rawPopitem] 0
  exact this.1 (by decide +kernel)

/-- Does iterating `od`, for at most `n` steps, stay within the nodes it has? -/
def odIterWithin {K V : Type} [DecidableEq K] (P : Proto K (PyDict K V)) (n : Nat) (od : ODict K V) : Bool :=
  match (odictiterTake P n od (odictiterNew od .key false) []).1 with
  | .ok l => decide (l.length ≤ od.nodes.length)
  | .error _ => true

/-- A stronger counterexample for the second half, on its own: two raw pops, and the walk from the
stale node yields more items than there are nodes. -/
def OdictIterBounded : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (steps : List (OdStep K V)) (n : Nat),
      odIterWithin P n (odRun P steps (odictNew 1)) = true

theorem odictIterBounded_refuted : ¬OdictIterBounded := by
  intro h
  have := h Nat Nat intProto _ _ intProto_honest
    [.set 0 0, .set 1 1, .set 2 2, .rawPopitem, .rawPopitem] 8
  exact absurd this (by decide +kernel)

/-- One step of a program on an `OrderedDict`, through its own methods only. -/
inductive OdOp (K V : Type) where
  | set (k : K) (v : V)
  | del (k : K)
  | moveToEnd (k : K) (last : Bool)

def odProg {K V : Type} [DecidableEq K] (P : Proto K (PyDict K V)) :
    List (OdOp K V) → ODict K V → ODict K V
  | [], od => od
  | .set k v :: rest, od => odProg P rest (odictSetItem P k v od).2
  | .del k :: rest, od => odProg P rest (odictDelItem P k od).2
  | .moveToEnd k l :: rest, od => odProg P rest (odictMoveToEnd P k l od).2

def pyProg {K V : Type} [DecidableEq K] (P : Proto K (PyDict K V)) (Q : Proto K (PyDict K Nat)) :
    List (OdOp K V) → PyOD K V → PyOD K V
  | [], o => o
  | .set k v :: rest, o => pyProg P Q rest (pyodSetItem P Q k v o).2
  | .del k :: rest, o => pyProg P Q rest (pyodDelItem P Q k o).2
  | .moveToEnd k l :: rest, o => pyProg P Q rest (pyodMoveToEnd Q k l o).2

/-- For keys that keep the contract, the C and pure-Python `OrderedDict` hold the same keys in the
same order after any program of their own methods. Open: it needs `Chain`-style invariants for
`od_fast_nodes` and the deferred `_odict_resize`, and for the link heap. The difftest checks each
twin against its own model on 50k-case runs. -/
def OdictTwinsAgree : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (Q : Proto K (PyDict K Nat))
    (hf : K → Int) (eqv : K → K → Bool), Honest P hf eqv → Honest Q hf eqv →
    ∀ ops : List (OdOp K V),
      (odProg P ops (odictNew 1)).nodes.map (·.key) = (pyProg P Q ops (pyodNew 1)).keysList

/-- One step of a program using a reverse dict iterator. -/
inductive RevStep (K V : Type) where
  | set (k : K) (v : V)
  | del (k : K)
  | start
  | next

def revRun {K V : Type} [DecidableEq K] (P : Proto K (PyDict K V)) :
    List (RevStep K V) → PyDict K V → DictIter → PyDict K V × DictIter
  | [], d, di => (d, di)
  | .set k v :: rest, d, di => revRun P rest (dictSetItem P k v d).2 di
  | .del k :: rest, d, di => revRun P rest (dictDelItem P k d).2 di
  | .start :: rest, d, _ => revRun P rest d (dictiterNew d .key true)
  | .next :: rest, d, di => revRun P rest d (dictiterNext d di).2

/-- `__length_hint__` of a reverse dict iterator is a valid `Py_ssize_t`, under any program. -/
def RevIterLenNonneg : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ steps : List (RevStep K V),
      let r := revRun P steps { ident := 1 } (dictiterNew ({ ident := 1 } : PyDict K V) .key true)
      dictiterLen r.1 r.2 < 2 ^ 63

/-- The same protocol, on sets. -/
def intSetProto : Proto Nat (SetObj Nat) :=
  { hash := fun k => .ok k
    isStr := fun _ => false
    isStrLike := fun _ => false
    strEq := fun a b => a == b
    reprStr := fun _ => ""
    repr := fun _ => .ok ""
    typeName := fun _ => ""
    eq := fun a b s => (.ok (a == b), s) }

inductive SetStep (K : Type) where
  | add (k : K)
  | discard (k : K)
  | start
  | next

def setRun {K : Type} [DecidableEq K] (P : Proto K (SetObj K)) :
    List (SetStep K) → SetObj K → SetIter → SetObj K × SetIter
  | [], s, si => (s, si)
  | .add k :: rest, s, si => setRun P rest (setAddKey P k s).2 si
  | .discard k :: rest, s, si => setRun P rest (setDiscardKey P k s).2 si
  | .start :: rest, s, _ => setRun P rest s (setIterNew s)
  | .next :: rest, s, si => setRun P rest s (setiterNext s si).2

/-- `__length_hint__` of a set iterator is not negative, under any program. -/
def SetIterLenNonneg : Prop :=
  ∀ steps : List (SetStep Nat),
    let r := setRun intSetProto steps {} (setIterNew ({} : SetObj Nat))
    0 ≤ setiterLen r.1 r.2

theorem setIterLenNonneg_refuted : ¬SetIterLenNonneg := by
  intro h
  have := h [.add 1, .add 2, .start, .next, .next, .discard 2, .add 3, .next]
  exact absurd this (by decide +kernel)

end PyLean.DictSet
