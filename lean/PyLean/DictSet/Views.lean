import PyLean.DictSet.DictOps
import PyLean.DictSet.SetOps

/-!
Dict views (`Objects/dictobject.c:5957-6782`): `len`, `repr`, comparison and the set
operations, which is where the dict and set tables meet. Line numbers refer to
`Objects/dictobject.c`. Views of the three kinds behave alike, so the three `*_iter` and
`*_reversed` slots and `dict_keys_impl`/`dict_items_impl`/`dict_values_impl` are one
definition each.
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type}

inductive ViewKind where
  | keys | items | values
  deriving DecidableEq, Repr, Inhabited

/-- `_PyDictViewObject`: its dict and its kind. `exactDict` is `PyDict_CheckExact`. -/
structure View (K V : Type) where
  kind : ViewKind
  d : PyDict K V
  exactDict : Bool := true
  ident : Nat := 0

/-- `dict_keys_impl` (:6565-6570), `dict_items_impl` (:6677-6682), `dict_values_impl`
(:6767-6772), `_PyDictView_New` (:5991-6012). -/
def viewNew (kind : ViewKind) (d : PyDict K V) : View K V := { kind, d }

/-- `dictview_len` (:5981-5989). -/
def dictviewLen (v : View K V) : Nat := v.d.used

/-- `dictkeys_iter` (:6149-6157), `dictitems_iter` (:6584-6592), `dictvalues_iter`
(:6696-6704), and the `*_reversed` slots (:6572-6580, :6684-6692, :6774-6782). -/
def dictviewIter (v : View K V) (rev : Bool) : DictIter :=
  dictiterNew v.d (match v.kind with
    | .keys => .key
    | .items => .item
    | .values => .value) rev

/-- How a set-side operation reaches `dict` and `tuple`. -/
structure Env (K V : Type) where
  D : Proto K (PyDict K V)
  S : Proto K (SetObj K)
  /-- `PyTuple_Pack(2, key, value)`; values are objects too. -/
  pair : K → V → K
  /-- `PyTuple_Check(obj) && PyTuple_GET_SIZE(obj) == 2`, and the two items. -/
  unpair : K → Option (K × V)
  /-- `PyObject_RichCompareBool` on values. -/
  veq : V → V → Py Bool
  vrepr : V → Py String

/-- An exact dict as `SetArg` sees it. -/
def dictAsArg [DecidableEq K] (E : Env K V) (d : PyDict K V) : DictArg K :=
  { size := d.used
    items := (dictItems d).map fun e => (e.1, e.2.2)
    contains := fun k h => (dictContainsKnownHash E.D k h d).1 }

/-- The items a view yields under iteration, as objects. -/
def viewItems (E : Env K V) (v : View K V) : List K :=
  match v.kind with
  | .keys => dictKeysList v.d
  | .items => (dictItemsList v.d).map fun p => E.pair p.1 p.2
  | .values => []

def viewIterable (E : Env K V) (v : View K V) : Iterable K := { items := viewItems E v }

/-- The operand of a view operation. -/
inductive ViewArg (K V : Type) where
  | view (v : View K V)
  /-- `PyAnySet_Check`; `exact` is on the object. -/
  | set (s : SetObj K)
  | other (a : SetArg K)

def ViewArg.toSetArg (E : Env K V) [DecidableEq K] : ViewArg K V → SetArg K
  | .view v => .iter (viewIterable E v)
  | .set s => .set s
  | .other a => a

section
variable [DecidableEq K] (E : Env K V)

/-- `dictviews_to_set` (:6182-6194). -/
def dictviewsToSet (self : ViewArg K V) (id : Nat) : Py (SetObj K) :=
  let shell : SetObj K := { ident := id }
  match self with
  | .view v =>
    if v.kind == .keys && v.exactDict then
      makeNewSet E.S shell (some (.dict (dictAsArg E v.d)))
    else
      makeNewSet E.S shell (some (.iter (viewIterable E v)))
  | a => makeNewSet E.S shell (some (a.toSetArg E))

/-- `dictviews_sub` (:6196-6213). -/
def dictviewsSub (self other : ViewArg K V) (id : Nat) : Py (SetObj K) :=
  match dictviewsToSet E self id with
  | .error e => .error e
  | .ok r => runNew (setDifferenceUpdateMulti E.S [other.toSetArg E] id) r

/-- `dictviews_or` (:6303-6316). -/
def dictviewsOr (self other : ViewArg K V) (id : Nat) : Py (SetObj K) :=
  match dictviewsToSet E self id with
  | .error e => .error e
  | .ok r => runNew (setUpdate E.S (other.toSetArg E)) r

/-- `dictkeys_contains` (:6159-6166). -/
def dictkeysContains (d : PyDict K V) (obj : K) : Py Bool := (pyDictContains E.D obj d).1

/-- `dictitems_contains` (:6594-6612). -/
def dictitemsContains (d : PyDict K V) (obj : K) : Py Bool :=
  match E.unpair obj with
  | none => .ok false
  | some (key, value) =>
    match (pyDictGetItemRef E.D true key d).1 with
    | .error e => .error e
    | .ok none => .ok false
    | .ok (some found) => E.veq found value

/-- `PySequence_Contains(view, x)`. -/
def viewContains (v : View K V) (x : K) : Py Bool :=
  match v.kind with
  | .items => dictitemsContains E v.d x
  | _ => dictkeysContains E v.d x

/-- The loop of `_PyDictView_Intersect` (:6277-6288). -/
def viewInterLoop (self : View K V) : List K → Option PyExc → SM K Unit
  | [], stop =>
    match stop with
    | some e => M.throw e
    | none => pure ()
  | key :: rest, stop => do
    let rv ← M.lift (viewContains E self key)
    if rv then setAddKey E.S key
    viewInterLoop self rest stop

/-- `_PyDictView_Intersect` (:6218-6301). `self` is the view (the swap at :6230-6234 has
been applied by the caller). -/
def dictviewIntersect (self : View K V) (other : ViewArg K V) (id : Nat) : Py (SetObj K) :=
  let viaSet := match other with
    | .set s => if s.exact && !s.frozen && decide (dictviewLen self ≤ s.used) then some s else none
    | _ => none
  match viaSet with
  | some s => setIntersection E.S s (.iter (viewIterable E self)) id
  | none =>
    let (self', other') : View K V × ViewArg K V :=
      match other with
      | .view o => if dictviewLen o > dictviewLen self then (o, .view self) else (self, other)
      | _ => (self, other)
    let it := (other'.toSetArg E).toIterable
    let result : SetObj K := { ident := id }
    match it.getIter with
    | some e => .error e
    | none => runNew (viewInterLoop E self' it.items it.stop) result

/-- `dictitems_xor_lock_held` (:6318-6400), `dictitems_xor` (:6402-6416). -/
def dictitemsXor (d1 d2 : PyDict K V) (id : Nat) : Py (SetObj K) :=
  match dictCopy E.D d1 0 false (.dict d1) with
  | .error e => .error e
  | .ok temp =>
    let rec go : List (K × V × Int) → PyDict K V → SetObj K → Py (PyDict K V × SetObj K)
      | [], t, r => .ok (t, r)
      | (key, val2, hash) :: rest, t, r =>
        let step : Py (Bool) :=
          match (dictGetItemKnownHash E.D true key hash t).1 with
          | .error e => .error e
          | .ok none => .ok false
          | .ok (some val1) => E.veq val1 val2
        match step with
        | .error e => .error e
        | .ok toDelete =>
          if toDelete then
            match dictDelItemKnownHash E.D key hash t with
            | (.error e, _) => .error e
            | (.ok _, t') => go rest t' r
          else
            match setAddKey E.S (E.pair key val2) r with
            | (.error e, _) => .error e
            | (.ok _, r') => go rest t r'
    match go (dictItems d2) temp { ident := id } with
    | .error e => .error e
    | .ok (t, r) =>
      runNew (setUpdateIterable E.S
        { items := (dictItemsList t).map fun p => E.pair p.1 p.2 }) r

/-- `dictviews_xor` (:6418-6438). -/
def dictviewsXor (self other : ViewArg K V) (id : Nat) : Py (SetObj K) :=
  match self, other with
  | .view a, .view b =>
    if a.kind == .items && b.kind == .items then dictitemsXor E a.d b.d id
    else
      match dictviewsToSet E self id with
      | .error e => .error e
      | .ok r => runNew (setSymmetricDifferenceUpdate E.S (other.toSetArg E) id) r
  | _, _ =>
    match dictviewsToSet E self id with
    | .error e => .error e
    | .ok r => runNew (setSymmetricDifferenceUpdate E.S (other.toSetArg E) id) r

/-- `PySequence_Contains(set_or_view, x)`. -/
def argContains (a : ViewArg K V) (x : K) : Py Bool :=
  match a with
  | .view v => viewContains E v x
  | .set s => (setContains E.S (fun _ => none) x s).1
  | .other (.set s) => (setContains E.S (fun _ => none) x s).1
  | .other (.dict d) =>
    match E.S.hash x with
    | .error e => .error e
    | .ok h => d.contains x h
  | .other (.iter it) => .ok (it.items.any fun y => (E.S.eq x y default).1 == .ok true)

/-- `all_contained_in` (:6040-6062). -/
def allContainedIn (self other : ViewArg K V) : Py Bool :=
  let it := (self.toSetArg E).toIterable
  let rec go : List K → Py Bool
    | [] =>
      match it.stop with
      | some e => .error e
      | none => .ok true
    | x :: rest =>
      match argContains E other x with
      | .error e => .error e
      | .ok ok => if ok then go rest else .ok false
  go it.items

/-- `len(arg)` for a set or a view. -/
def argLen : ViewArg K V → Nat
  | .view v => dictviewLen v
  | .set s => s.used
  | .other (.set s) => s.used
  | .other (.dict d) => d.size
  | .other (.iter it) => it.items.length

/-- `dictview_richcompare` (:6064-6121): `other` must be a set or a view (otherwise
`NotImplemented`). -/
def dictviewRichcompare (self : View K V) (other : ViewArg K V) (op : CmpOp) : Py Bool :=
  let s : ViewArg K V := .view self
  let lenSelf := dictviewLen self
  let lenOther := argLen other
  match op with
  | .eq => if lenSelf == lenOther then allContainedIn E s other else .ok false
  | .ne =>
    if lenSelf == lenOther then
      match allContainedIn E s other with
      | .error e => .error e
      | .ok b => .ok (!b)
    else .ok true
  | .lt => if lenSelf < lenOther then allContainedIn E s other else .ok false
  | .le => if lenSelf ≤ lenOther then allContainedIn E s other else .ok false
  | .gt => if lenSelf > lenOther then allContainedIn E other s else .ok false
  | .ge => if lenSelf ≥ lenOther then allContainedIn E other s else .ok false

/-- `dictviews_isdisjoint` (:6459-6508). `sameObject` is `self == other`. -/
def dictviewsIsdisjoint (self : View K V) (other : ViewArg K V) (sameObject : Bool) : Py Bool :=
  if sameObject then .ok (dictviewLen self == 0)
  else
    let s : ViewArg K V := .view self
    let swap : Bool := match other with
      | .view _ | .set _ | .other (.set _) => decide (argLen other > dictviewLen self)
      | _ => false
    let (a, b) : ViewArg K V × ViewArg K V := if swap then (other, s) else (s, other)
    let it := (b.toSetArg E).toIterable
    match it.getIter with
    | some e => .error e
    | none =>
      let rec go : List K → Py Bool
        | [] =>
          match it.stop with
          | some e => .error e
          | none => .ok true
        | x :: rest =>
          match argContains E a x with
          | .error e => .error e
          | .ok c => if c then .ok false else go rest
      go it.items

/-- `dictview_repr` (:6123-6145). `seqRepr` is `repr(list(view))`. -/
def dictviewRepr (tpName : String) (inRepr : Bool) (seqRepr : Py String) : Py String :=
  if inRepr then .ok "..."
  else
    match seqRepr with
    | .error e => .error e
    | .ok r => .ok s!"{tpName}({r})"

end

end PyLean.DictSet
