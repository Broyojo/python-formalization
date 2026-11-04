import PyLean.Bytecode.Ceval

/-!
The keyword-only defaults loop of `initialize_locals` (`Python/ceval.c:1942-1966`, CPython 3.15.2)
at the level of C pointers and reference counts, with the generic dict lookup it calls
(`PyDict_GetItemRef`, `_PyDict_GetItemRef_KnownHash`, `_Py_dict_lookup`, `do_lookup`,
`compare_generic`, `Objects/dictobject.c:2565-2581`, `:2539-2563`, `:1328-1384`, `:1082-1128`,
`:1182-1207`).

`initializeLocals` in `Ceval.lean` is the version the machine and the difftest run: it looks the
parameter name up in `func.kwdefaults` by string, its heap never frees anything, and no Python code
runs. In C, `func->func_kwdefaults` is passed to `PyDict_GetItemRef` as a borrowed reference
(`:1949-1951`). When the dict has a key that is not a `str` (so its keys are `DICT_KEYS_GENERAL`)
with the same hash as the parameter name, `compare_generic` calls that key's `__eq__`
(`PyObject_RichCompareBool(startkey, key, Py_EQ)`, `:1193`), which is Python code, and that code
can assign `f.__kwdefaults__` (`func_set_kwdefaults`, `Objects/funcobject.c:875-906`, which drops the
old dict with `Py_XDECREF`). If the function held the only reference, the dict is freed while the
lookup still uses it: `compare_generic` reads `mp->ma_keys` right after the comparison (`:1198`).

## Scope

* Objects are numbered and none is `0`. A live object has a reference count. A dict object has the
  identity of its keys object (`ma_keys`) and its entries in probe order (`do_lookup`'s
  `i*5 + perturb + 1` sequence over the index table, `:1086-1124`, reduced to the order it visits
  them); every key and value is a non-dict object, so freeing one frees nothing else.
* The parameter names are exact interned `str` objects with their cached hashes
  (`_PyObject_HashFast`); a stored key is the same object or another one.
* What a stored key's `__eq__` (against the parameter name) does is a list of
  `f.__kwdefaults__ = d` / `f.__kwdefaults__ = None` assignments, then a truth value or an exception
  (`PyObject_RichCompareBool`'s outcome). Any other effect is outside the scope.
* `dict_dealloc` decrefs the keys and values of the freed dict. Reading a freed object is
  undefined behaviour, the `ub` outcome.
* Restarts of `_Py_dict_lookup` (`goto start`, `DKIX_KEY_CHANGED`) are bounded by fuel; running out
  is the `fuel` outcome, not a Python one.
-/

namespace PyLean.Bytecode.KwDefC

/-- What Python code in a key's `__eq__` does: `f.__kwdefaults__ = d` (`some d`) or
`f.__kwdefaults__ = None` / `del f.__kwdefaults__` (`none`). -/
inductive Act where
  | setKwdefaults (d : Option Nat)
  deriving DecidableEq, Repr

/-- A stored key's `__eq__` against the parameter name: its assignments in order, then its result,
`none` when it raises. -/
structure Meth where
  acts : List Act := []
  result : Option Bool := some false
  deriving DecidableEq, Repr

/-- A `PyDictKeyEntry`: `me_hash`, `me_key`, `me_value`. -/
structure Entry where
  hash : Int
  key : Nat
  value : Nat
  deriving DecidableEq, Repr

/-- A live object. `dict = some (dk, entries)` for a dict: the identity of `ma_keys` and the
entries; `eq` is what comparing it, as a stored key, with a parameter name does. -/
structure CObj where
  rc : Nat
  eq : Meth := {}
  dict : Option (Nat × List Entry) := none
  deriving DecidableEq, Repr

/-- The C heap and `func->func_kwdefaults` (`none` is `NULL`). -/
structure St where
  objs : List (Nat × CObj)
  kwdefaults : Option Nat
  deriving DecidableEq, Repr

/-- Outcome of a C function: a value, a raised exception, undefined behaviour, or fuel. -/
inductive CR (α : Type) where
  | ok (a : α) (s : St)
  | raise (s : St)
  | ub (what : String) (s : St)
  | fuel (s : St)
  deriving DecidableEq, Repr

def CR.bind {α β : Type} (r : CR α) (f : α → St → CR β) : CR β :=
  match r with
  | .ok a s => f a s
  | .raise s => .raise s
  | .ub w s => .ub w s
  | .fuel s => .fuel s

/-- Did this run read freed memory? -/
def CR.isUb {α : Type} : CR α → Bool
  | .ub _ _ => true
  | _ => false

def find (s : St) (a : Nat) : Option CObj := (s.objs.find? (·.1 == a)).map (·.2)

/-- Drop the object at `a` from the heap, without touching what it refers to. -/
def remove (s : St) (a : Nat) : St := { s with objs := s.objs.filter (·.1 != a) }

def setRc (s : St) (a : Nat) (rc : Nat) : St :=
  { s with objs := s.objs.map fun p => if p.1 == a then (p.1, { p.2 with rc := rc }) else p }

/-- `Py_INCREF`. -/
def incref (a : Nat) (s : St) : St :=
  match find s a with
  | some o => setRc s a (o.rc + 1)
  | none => s

/-- `Py_DECREF` of an object that holds no references (a key or a value). -/
def decrefLeaf (a : Nat) (s : St) : St :=
  match find s a with
  | some o => if o.rc ≤ 1 then remove s a else setRc s a (o.rc - 1)
  | none => s

/-- `Py_DECREF`: a dict freed by it runs `dict_dealloc`, which decrefs its keys and values. -/
def decref (a : Nat) (s : St) : St :=
  match find s a with
  | some o =>
    if o.rc ≤ 1 then
      let s := remove s a
      match o.dict with
      | some (_, es) => es.foldl (fun s e => decrefLeaf e.value (decrefLeaf e.key s)) s
      | none => s
    else setRc s a (o.rc - 1)
  | none => s

/-- `func_set_kwdefaults`, `Objects/funcobject.c:875-906`: store the new value with a new
reference, then `Py_XDECREF` the old one. -/
def runAct (s : St) : Act → St
  | .setKwdefaults d =>
    let old := s.kwdefaults
    let s := match d with
      | some n => incref n s
      | none => s
    let s := { s with kwdefaults := d }
    match old with
    | some o => decref o s
    | none => s

/-- `compare_generic`'s result: `DKIX_ERROR`, a match or not, or `DKIX_KEY_CHANGED`. -/
inductive Cmp where
  | error | found | no | changed
  deriving DecidableEq, Repr

/-- `compare_generic(mp, dk, ep0, ix, key, hash)`, `Objects/dictobject.c:1182-1207`. `e` is the
entry at `ix` as `do_lookup` read it. -/
def compareGeneric (mp dk : Nat) (ix : Nat) (e : Entry) (key : Nat) (hash : Int) (s : St) : CR Cmp :=
  if e.key == key then .ok .found s
  else if e.hash == hash then
    match find s e.key with
    | none => .ub s!"__eq__ of freed key {e.key}" s
    | some startObj =>
      -- `Py_INCREF(startkey)`, the comparison, `Py_DECREF(startkey)`
      let s := incref e.key s
      let s := startObj.eq.acts.foldl runAct s
      let s := decref e.key s
      match startObj.eq.result with
      | none => .raise s
      | some cmp =>
        -- `if (dk == mp->ma_keys && ep->me_key == startkey)`, `:1198`
        match find s mp with
        | none => .ub s!"mp->ma_keys of freed dict {mp}" s
        | some m =>
          match m.dict with
          | some (dk', es) =>
            if dk' == dk && (es[ix]?.map (·.key)) == some e.key then
              .ok (if cmp then .found else .no) s
            else .ok .changed s
          | none => .ub "not a dict" s
  else .ok .no s

/-- `do_lookup(mp, dk, key, hash, compare_generic)`, `:1082-1128`, over the entries in probe
order: the index of the match, `none` at `DKIX_EMPTY`, or the error or restart. -/
def doLookup (mp dk : Nat) (key : Nat) (hash : Int) : List Entry → Nat → St → CR (Option (Option Nat))
  | [], _, s => .ok (some none) s
  | e :: rest, ix, s =>
    (compareGeneric mp dk ix e key hash s).bind fun c s =>
      match c with
      | .error => .raise s
      | .found => .ok (some (some ix)) s
      | .changed => .ok none s
      | .no => doLookup mp dk key hash rest (ix + 1) s

/-- `_Py_dict_lookup(mp, key, hash, &value)`, `:1328-1384`, for `DICT_KEYS_GENERAL`: `start:`
reads `mp->ma_keys`, a `DKIX_KEY_CHANGED` goes back there. The value of the match, or `none`. -/
def dictLookup (mp : Nat) (key : Nat) (hash : Int) : Nat → St → CR (Option Nat)
  | 0, s => .fuel s
  | fuel + 1, s =>
    match find s mp with
    | none => .ub s!"mp->ma_keys of freed dict {mp}" s
    | some m =>
      match m.dict with
      | none => .ub "not a dict" s
      | some (dk, es) =>
        (doLookup mp dk key hash es 0 s).bind fun r s =>
          match r with
          | none => dictLookup mp key hash fuel s
          | some none => .ok none s
          | some (some ix) => .ok ((es[ix]?).map (·.value)) s

/-- `PyDict_GetItemRef(op, key, &result)` (`:2565-2581`) through `_PyDict_GetItemRef_KnownHash`
(`:2539-2563`): the value with a new reference (`Py_NewRef`), or `none` when missing. -/
def getItemRef (op : Nat) (key : Nat) (hash : Int) (fuel : Nat) (s : St) : CR (Option Nat) :=
  (dictLookup op key hash fuel s).bind fun v s =>
    match v with
    | some val => .ok (some val) (incref val s)
    | none => .ok none s

/-- The loop of `:1945-1960` over the keyword-only parameters whose local is still `NULL`, each
`(varname, hash)`: `func->func_kwdefaults` is read afresh each time and passed borrowed to
`PyDict_GetItemRef`; a hit fills the local, a miss counts as missing. -/
def kwonlyDefaults (fuel : Nat) : List (Nat × Int) → St → CR (List (Option Nat))
  | [], s => .ok [] s
  | (varname, hash) :: rest, s =>
    match s.kwdefaults with
    | some d =>
      (getItemRef d varname hash fuel s).bind fun v s =>
        (kwonlyDefaults fuel rest s).bind fun vs s => .ok (v :: vs) s
    | none => (kwonlyDefaults fuel rest s).bind fun vs s => .ok (none :: vs) s

/-- The same loop with a strong reference to the dict held across the lookup
(`Py_XNewRef(func->func_kwdefaults)` before, `Py_XDECREF` after), as the fix would do. -/
def kwonlyDefaultsFixed (fuel : Nat) : List (Nat × Int) → St → CR (List (Option Nat))
  | [], s => .ok [] s
  | (varname, hash) :: rest, s =>
    match s.kwdefaults with
    | some d =>
      let s := incref d s
      (getItemRef d varname hash fuel s).bind fun v s =>
        let s := decref d s
        (kwonlyDefaultsFixed fuel rest s).bind fun vs s => .ok (v :: vs) s
    | none => (kwonlyDefaultsFixed fuel rest s).bind fun vs s => .ok (none :: vs) s

/-! ## Reachable states -/

/-- The references held: `func_kwdefaults`, and the keys and values of every live dict. -/
def holders (s : St) : List Nat :=
  s.kwdefaults.toList ++ s.objs.flatMap fun p =>
    match p.2.dict with
    | some (_, es) => es.flatMap fun e => [e.key, e.value]
    | none => []

/-- A state Python code can reach: addresses are distinct and not `0`, a live object has a count
of at least one, every held pointer is a live object whose count covers its holders, and the
dicts' keys and values are not dicts. -/
def wf (s : St) : Bool :=
  decide (s.objs.map (·.1)).Nodup && s.objs.all (fun p => p.1 != 0 && 1 ≤ p.2.rc) &&
  (holders s).all (fun a =>
    match find s a with
    | some o => decide ((holders s).count a ≤ o.rc)
    | none => false) &&
  s.objs.all fun p =>
    match p.2.dict with
    | some (_, es) => es.all fun e =>
        (match find s e.key with | some o => o.dict.isNone | none => false) &&
        (match find s e.value with | some o => o.dict.isNone | none => false)
    | none => true

/-! ## Properties -/

/-- **The keyword-only defaults loop does not crash**: from every reachable state, for every list
of missing keyword-only parameters, whatever the stored keys' `__eq__` do among the
`__kwdefaults__` assignments of `Act`, no step reads a freed object. Invariant: no crash from pure
Python code. FALSE on 3.15.2: `func->func_kwdefaults` is borrowed (`Python/ceval.c:1949-1951`), so a
key whose `__eq__` sets `f.__kwdefaults__ = None` frees the dict, and `compare_generic` then reads
`mp->ma_keys` (`Objects/dictobject.c:1198`). -/
def KwonlyDefaultsNoCrash : Prop :=
  ∀ (fuel : Nat) (params : List (Nat × Int)) (s : St), wf s = true →
    (kwonlyDefaults fuel params s).isUb = false

/-- `def f(*, b)` with `f.__kwdefaults__ = {K(): 1}`, `hash(K()) == hash('b')` (7 here), and
`K.__eq__` running `f.__kwdefaults__ = None` and returning `False`: the dict is object 1, held only
by the function, its one key the `K()` instance 2 and its value the int 3; the parameter name
`'b'` is object 100 (interned, immortal, not in the dict). The reproducer of
`bytecode-kwonly-defaults-borrowed-dict`. -/
def uafState : St :=
  { objs := [(1, { rc := 1, dict := some (10, [⟨7, 2, 3⟩]) }),
             (2, { rc := 1, eq := { acts := [.setKwdefaults none], result := some false } }),
             (3, { rc := 1 })]
    kwdefaults := some 1 }

def uafParams : List (Nat × Int) := [(100, 7)]

theorem uafState_wf : wf uafState = true := by decide +kernel

theorem uafState_ub : (kwonlyDefaults 2 uafParams uafState).isUb = true := by decide +kernel

theorem kwonlyDefaultsNoCrash_refuted : ¬KwonlyDefaultsNoCrash := by
  intro h
  have := h 2 uafParams uafState uafState_wf
  rw [uafState_ub] at this
  exact Bool.noConfusion this

/-- **A strong reference removes this crash.** Holding `Py_XNewRef(func->func_kwdefaults)` across
the lookup, the same state finds no default for `b` (the comparison said `False` and the dict was
not changed under the lookup), so `initialize_locals` goes on to `missing_arguments`, and frees
the dict only afterwards. -/
def KwonlyDefaultsFixedOnUaf : Prop :=
  ∃ s', kwonlyDefaultsFixed 2 uafParams uafState = .ok [none] s' ∧ s'.kwdefaults = none ∧ s'.objs = []

theorem kwonlyDefaultsFixedOnUaf_proven : KwonlyDefaultsFixedOnUaf :=
  ⟨{ objs := [], kwdefaults := none }, by decide +kernel, rfl, rfl⟩

end PyLean.Bytecode.KwDefC
