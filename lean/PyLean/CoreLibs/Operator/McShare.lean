import PyLean.CoreLibs.Operator.Strength

/-!
`methodcaller` and the keyword dict it shares with `functools.partial`, CPython 3.15.2.

`Getters.lean` models a `methodcaller` as a value. Here the C object holds `mc->kwds`, the address of a dict on a
heap, with that dict's reference count, because two paths hand that very dict to `functools.partial`:

* `methodcaller_reduce`, Modules/_operator.c:1876-1908, calls `PyObject_VectorcallDict(partial, newargs, 2,
  mc->kwds)` (:1903). `partial` has no vectorcall, so `_PyObject_VectorcallDictTstate` goes to
  `_PyObject_MakeTpCall` (Objects/call.c:127-131), which passes a dict through as it is (:222-223), and
  `type_call` gives it to `partial_new` (Objects/typeobject.c:2512).
* `methodcaller_call`, :1779-1796, the path of a `methodcaller` with eight or more arguments, calls
  `PyObject_Call(method, mc->args, mc->kwds)` (:1793); when the method is the `functools.partial` type, that is
  `type_call` again (Objects/call.c:343-362).

`partial_new`, Modules/_functoolsmodule.c:295-305, adopts a dict that is uniquely referenced instead of copying
it (`pto->kw = Py_NewRef(kw)`, :299-300). A `methodcaller` is the only holder of `mc->kwds`, so `partial.keywords`
becomes the `methodcaller`'s own dict. Writing to it changes what `repr(mc)` prints, while `mc(obj)` on the
vectorcall path still passes the values computed at construction, and a key that is not a `str` makes
`methodcaller_repr` format it with `%U` (:1838), undefined behaviour (a segfault on 3.15.2).

The Python twin, Lib/operator.py:337-342, rebuilds with `**self._kwargs`, a new dict, so it shares nothing.
-/

namespace PyLean.CoreLibs.Operator.McShare

open PyLean
open PyLean.CoreLibs.Operator

/-- A dict key. `PyDict_SetItem` takes any hashable object; the keyword syntax only makes `str`. -/
inductive Key where
  | str (s : String)
  | other (n : Int)
  deriving Repr, DecidableEq

/-- A dict on the heap: its entries table in insertion order, where a deleted entry stays as `none` at its index
(`delitem_common` leaves a dummy, Objects/dictobject.c), and `Py_REFCNT`. Positions matter because `PyDict_Next`
walks by index. Scope limit: the table is not compacted when an insertion resizes it (`insertion_resize`), so a
mutation that both deletes and then inserts past the table's usable size is out of scope. -/
structure DictObj (α : Type) where
  entries : List (Option (Key × α))
  refs : Nat
  deriving Repr, DecidableEq

/-- The dicts, by address. -/
abbrev Heap (α : Type) := List (DictObj α)

def updAt {β : Type} : List β → Nat → (β → β) → List β
  | [], _, _ => []
  | x :: xs, 0, f => f x :: xs
  | x :: xs, n + 1, f => x :: updAt xs n f

/-- The entries at an address; a dangling address reads as empty (it never occurs here). -/
def entriesAt {α : Type} (h : Heap α) (d : Nat) : List (Option (Key × α)) := (h[d]?.map (·.entries)).getD []

/-- The live items at an address, in order. -/
def itemsAt {α : Type} (h : Heap α) (d : Nat) : List (Key × α) := (entriesAt h d).filterMap id

def refsAt {α : Type} (h : Heap α) (d : Nat) : Nat := (h[d]?.map (·.refs)).getD 0

/-- `Py_INCREF` and `Py_DECREF` of a dict that stays alive. -/
def incref {α : Type} (h : Heap α) (d : Nat) : Heap α := updAt h d (fun o => { o with refs := o.refs + 1 })
def decref {α : Type} (h : Heap α) (d : Nat) : Heap α := updAt h d (fun o => { o with refs := o.refs - 1 })

/-- A new dict with one reference and a compact table; its address is the old length. -/
def alloc {α : Type} (h : Heap α) (items : List (Key × α)) : Heap α × Nat := (h ++ [⟨items.map some, 1⟩], h.length)

/-- `d[k] = v`, `PyDict_SetItem`: an equal key keeps its entry and takes the value; a new key gets a new entry at the
end. -/
def dictSet {α : Type} (es : List (Option (Key × α))) (k : Key) (v : α) : List (Option (Key × α)) :=
  if es.any (fun e => match e with | some p => decide (p.1 = k) | none => false) then
    es.map (fun e => match e with | some p => if p.1 = k then some (p.1, v) else some p | none => none)
  else es ++ [some (k, v)]

/-- `del d[k]`: the entry stays, emptied. -/
def dictDel {α : Type} (es : List (Option (Key × α))) (k : Key) : List (Option (Key × α)) :=
  es.map (fun e => match e with | some p => if p.1 = k then none else some p | none => none)

/-- An object `partial_new` and `methodcaller_new` see as an argument: the `methodcaller` type, a `str`, or a value
of the abstract type. -/
inductive PObj (α : Type) where
  | mcType
  | str (s : String)
  | val (a : α)
  deriving Repr, DecidableEq

/-- `partialobject`, Modules/_functoolsmodule.c, as far as here: the function, the arguments, and `pto->kw`. -/
structure PartialObj (α : Type) where
  fn : PObj α
  args : List (PObj α)
  kw : Nat
  deriving Repr, DecidableEq

/-- What `partial_new` asks of its arguments: `PyCallable_Check`, and `== state->placeholder`. -/
structure PWorld (α : Type) where
  callable : PObj α → Bool
  isPh : PObj α → Bool

/-- `partial_new`, Modules/_functoolsmodule.c:161-319, for a `func` that is not itself a `partial` (it is the
`methodcaller` type, or what a test passes), so `pto_args` and `pto_kw` stay NULL (:207-223). The checks in source
order, then the keyword dict: NULL gives a new one (:296-297), a uniquely referenced one is adopted (:299-300), any
other is copied (:302-303). -/
def partialNew {α : Type} (W : PWorld α) (h : Heap α) (args : List (PObj α)) (kw : Option Nat) :
    Py (PartialObj α × Heap α) :=
  match args with
  | [] => .error (.typeError "type 'partial' takes at least one argument")
  | func :: rest =>
    if !W.callable func then .error (.typeError "the first argument must be callable") else
    if (rest.getLast?.map W.isPh).getD false then .error (.typeError "trailing Placeholders are not allowed") else
    let kwItems := match kw with | none => [] | some d => itemsAt h d
    if kwItems.any (fun p => W.isPh (.val p.2)) then
      .error (.typeError "Placeholder cannot be passed as a keyword argument") else
    match kw with
    | none =>
      let (h', d') := alloc h []
      .ok (⟨func, rest, d'⟩, h')
    | some d =>
      if refsAt h d = 1 then .ok (⟨func, rest, d⟩, incref h d)
      else
        let (h', d') := alloc h (itemsAt h d)
        .ok (⟨func, rest, d'⟩, h')

/-! ### The C `methodcaller` -/

/-- `methodcallerobject`, Modules/_operator.c:1613-1621. `vec` is `vectorcall_args` with `vectorcall_kwnames`,
`none` when `mc->vectorcall` is NULL. -/
structure McObj (α : Type) where
  name : String
  args : List α
  kwds : Option Nat
  vec : Option (List α × List Key)
  deriving Repr, DecidableEq

/-- `methodcaller_new`, Modules/_operator.c:1690-1741, with `kwds` the dict `type_call` passes: the count (:1695),
the name (:1701-1706), `Py_XNewRef(kwds)` (:1717), the positional slice (:1724), and the vectorcall arguments when
fewer than `_METHODCALLER_MAX_ARGS` (:1730-1737), from `_methodcaller_initialize_vectorcall` (:1649-1686): the
values after the positional arguments and the keys apart. -/
def mcNewHeap {α : Type} (h : Heap α) (args : List (PObj α)) (kwds : Option Nat) : Py (McObj α × Heap α) :=
  match args with
  | [] => .error (.typeError "methodcaller needs at least one argument, the method name")
  | .str s :: rest =>
    let h1 := match kwds with | none => h | some d => incref h d
    let pos : List α := rest.filterMap (fun o => match o with | .val a => some a | _ => none)
    let kws := match kwds with | none => [] | some d => itemsAt h1 d
    let vec := if rest.length + 1 + kws.length < 8 then
        some (if kws.isEmpty then (pos, []) else (pos ++ kws.map Prod.snd, kws.map Prod.fst))
      else none
    .ok (⟨s, pos, kwds, vec⟩, h1)
  | _ :: _ => .error (.typeError "method name must be a string")

/-- `operator.methodcaller(name, *args, **kw)` from Python: `_PyObject_MakeTpCall` builds the keyword dict from the
names (`_PyStack_AsDict`, Objects/call.c:226-233; none for no keywords, :234-235), `methodcaller_new` takes its
reference, and `_PyObject_MakeTpCall` drops its own (:248-250). Keyword syntax gives `str` names. -/
def mcFromCall {α : Type} (h : Heap α) (name : String) (args : List α) (kw : List (String × α)) :
    Py (McObj α × Heap α) :=
  let kwItems := kw.map (fun p => (Key.str p.1, p.2))
  if kw.isEmpty then mcNewHeap h (.str name :: args.map .val) none
  else
    let (h1, d) := alloc h kwItems
    match mcNewHeap h1 (.str name :: args.map .val) (some d) with
    | .error e => .error e
    | .ok (mc, h2) => .ok (mc, decref h2 d)

/-- What `__reduce__` returns: `(type(mc), (name, *args))`, or `(partial(type(mc), name, **kwds), args)`. -/
inductive Reduced (α : Type) where
  | plain (args : List (PObj α))
  | viaPartial (p : PartialObj α) (args : List α)
  deriving Repr, DecidableEq

/-- `methodcaller_reduce`, Modules/_operator.c:1876-1908. No keywords (NULL or empty, :1879) is the plain branch;
otherwise `functools.partial` is imported, which can fail (:1897-1899), and called through
`PyObject_VectorcallDict` with `mc->kwds` itself (:1901-1903). -/
def mcReduceC {α : Type} (W : PWorld α) (imp : Py Unit) (h : Heap α) (mc : McObj α) : Py (Reduced α × Heap α) :=
  let n := match mc.kwds with | none => 0 | some d => (itemsAt h d).length
  if mc.kwds.isNone || n == 0 then .ok (.plain (.str mc.name :: mc.args.map .val), h)
  else
    match imp with
    | .error e => .error e
    | .ok () =>
      match partialNew W h [.mcType, .str mc.name] mc.kwds with
      | .error e => .error e
      | .ok (p, h') => .ok (.viaPartial p mc.args, h')

/-- `p.keywords[k] = v` in Python: the `keywords` member is `pto->kw` itself (Modules/_functoolsmodule.c:688),
read-only as an attribute and mutable as a dict. -/
def setKeyword {α : Type} (h : Heap α) (p : PartialObj α) (k : Key) (v : α) : Heap α :=
  updAt h p.kw (fun o => { o with entries := dictSet o.entries k v })

/-- `del p.keywords[k]`. -/
def delKeyword {α : Type} (h : Heap α) (p : PartialObj α) (k : Key) : Heap α :=
  updAt h p.kw (fun o => { o with entries := dictDel o.entries k })

/-- `p.keywords.clear()`: `PyDict_Clear` gives the dict an empty table. -/
def clearKeywords {α : Type} (h : Heap α) (p : PartialObj α) : Heap α :=
  updAt h p.kw (fun o => { o with entries := [] })

/-- The keyword part of `methodcaller_repr`, :1834-1848: `PyUnicode_FromFormat("%U=%R", key, value)` for each item.
`%U` of a key that is not a `str` is undefined behaviour (`none`): unicodeobject.c only asserts the type. -/
def kwReprs {α : Type} (rep : α → Py String) : List (Key × α) → Option (Py (List String))
  | [] => some (.ok [])
  | (.other _, _) :: _ => none
  | (.str s, v) :: rest =>
    match rep v with
    | .error e => some (.error e)
    | .ok r =>
      match kwReprs rep rest with
      | none => none
      | some (.error e) => some (.error e)
      | some (.ok l) => some (.ok ((s ++ "=" ++ r) :: l))

/-- A `repr` that may run Python code: its outcome, and the heap after it. A value's `__repr__` can write to
`p.keywords`, which is `mc->kwds` once shared. -/
abbrev RepS (α : Type) := α → Heap α → Py String × Heap α

/-- A `repr` that touches nothing. -/
def pureRep {α : Type} (rep : α → Py String) : RepS α := fun a h => (rep a, h)

/-- The positional loop of `methodcaller_repr`, :1827-1832: the first failing `PyObject_Repr` stops it. -/
def posReprs {α : Type} (rep : RepS α) : List α → Heap α → Py (List String) × Heap α
  | [], h => (.ok [], h)
  | a :: as, h =>
    match rep a h with
    | (.error e, h') => (.error e, h')
    | (.ok r, h') =>
      match posReprs rep as h' with
      | (.error e, h'') => (.error e, h'')
      | (.ok rs, h'') => (.ok (r :: rs), h'')

/-- The entries from index `j` on: the first live one with its index. -/
def nextFrom {α : Type} : List (Option (Key × α)) → Nat → Option (Nat × Key × α)
  | [], _ => none
  | none :: es, j => nextFrom es (j + 1)
  | some (k, v) :: es, j => some (j, k, v)

/-- `PyDict_Next(mp, &pos, &key, &value)`: the first live entry at index `pos` or later of the table as it is now. -/
def dictNext {α : Type} (es : List (Option (Key × α))) (pos : Nat) : Option (Nat × Key × α) :=
  nextFrom (es.drop pos) pos

def changedSize : PyExc := .named "RuntimeError" "keywords dict changed size during iteration"

/-- The keyword loop of `methodcaller_repr`, :1834-1853. `PyDict_Next` reads the dict at each step, so a value's
`__repr__` that writes to it is seen. Each item is `PyUnicode_FromFormat("%U=%R", key, value)` (:1838): `%U` of a key
that is not a `str` is undefined behaviour (`none`), and `%R` runs the value's `__repr__`, whose failure stops the
loop (:1839-1840). An item past `numtotalargs` is the size check of :1841-1845, and a loop that ends short of it is
the check of :1849-1853, both `RuntimeError`. `i` starts at the number of positional arguments. The fuel is never
the outcome: `i` grows each step and the loop stops once it reaches `total`. -/
def kwLoop {α : Type} (rep : RepS α) (d total : Nat) :
    Nat → Nat → Nat → Heap α → List String → Option (Py (List String) × Heap α)
  | 0, _, _, h, _ => some (.error .modelFuel, h)
  | fuel + 1, pos, i, h, acc =>
    match dictNext (entriesAt h d) pos with
    | none => if i = total then some (.ok acc, h) else some (.error changedSize, h)
    | some (_, .other _, _) => none
    | some (j, .str s, v) =>
      match rep v h with
      | (.error e, h') => some (.error e, h')
      | (.ok r, h') =>
        if total ≤ i then some (.error changedSize, h')
        else kwLoop rep d total fuel (j + 1) (i + 1) h' (acc ++ [s ++ "=" ++ r])

/-- `methodcaller_repr`, Modules/_operator.c:1799-1873, reading `mc->kwds` from the heap, with reprs that may write to
it. `numkwdargs` is read once, before any `repr` runs (:1811), and the keyword loop runs only when it was not zero
(:1834). `none` is undefined behaviour. The name is an exact `str` here, with `nameRepr` its repr. -/
def mcReprHeapS {α : Type} (rep : RepS α) (running : Bool) (cls nameRepr : String) (h : Heap α)
    (mc : McObj α) : Option (Py String × Heap α) :=
  if running then some (.ok (cls ++ "(...)"), h) else
  let nk := match mc.kwds with | none => 0 | some d => (itemsAt h d).length
  let np := mc.args.length
  if np + nk = 0 then some (.ok (cls ++ "(" ++ nameRepr ++ ")"), h) else
  match posReprs rep mc.args h with
  | (.error e, h1) => some (.error e, h1)
  | (.ok a, h1) =>
    let kwPart : Option (Py (List String) × Heap α) :=
      match mc.kwds with
      | none => some (.ok [], h1)
      | some d => if nk = 0 then some (.ok [], h1) else kwLoop rep d (np + nk) (np + nk + 1) 0 np h1 []
    match kwPart with
    | none => none
    | some (.error e, h2) => some (.error e, h2)
    | some (.ok k, h2) => some (.ok (cls ++ "(" ++ nameRepr ++ ", " ++ joinArgs (a ++ k) ++ ")"), h2)

/-- `methodcaller_repr` with reprs that write nothing: the outcome only. -/
def mcReprHeap {α : Type} (rep : α → Py String) (running : Bool) (cls nameRepr : String) (h : Heap α)
    (mc : McObj α) : Option (Py String) :=
  (mcReprHeapS (pureRep rep) running cls nameRepr h mc).map Prod.fst

/-- What `getattr(obj, name)` gives: the `functools.partial` type, or another callable taking the arguments and
the keyword items. -/
inductive Method (α β : Type) where
  | partialType
  | other (f : List α → List (Key × α) → Py β)

/-- The result of a call: a new `partial`, or whatever another method returns. -/
inductive CallOut (α β : Type) where
  | made (p : PartialObj α)
  | value (b : β)
  deriving DecidableEq

/-- Calling `mc(obj)` once the argument check passed. With `vec`, `methodcaller_vectorcall` (:1628-1646): the
method gets the stored values, and a type without vectorcall gets a new dict built from `vectorcall_kwnames`
(Objects/call.c:226-233), which it may keep; without `vec`, `methodcaller_call` (:1779-1796) passes `mc->kwds`
itself to `PyObject_Call`, which `type_call` hands to `partial_new`. -/
def mcCallHeap {α β : Type} (W : PWorld α) (lookup : Py (Method α β)) (h : Heap α) (mc : McObj α) :
    Py (CallOut α β × Heap α) :=
  match lookup with
  | .error e => .error e
  | .ok m =>
    match mc.vec with
    | some (flat, names) =>
      let n := mc.args.length
      let kwItems := names.zip (flat.drop n)
      match m with
      | .other f => (f (flat.take n) kwItems).map (fun b => (.value b, h))
      | .partialType =>
        if kwItems.isEmpty then
          (partialNew W h ((flat.take n).map .val) none).map (fun r => (.made r.1, r.2))
        else
          let (h1, d) := alloc h kwItems
          match partialNew W h1 ((flat.take n).map .val) (some d) with
          | .error e => .error e
          | .ok (p, h2) => .ok (.made p, decref h2 d)
    | none =>
      match m with
      | .other f => (f mc.args (match mc.kwds with | none => [] | some d => itemsAt h d)).map (fun b => (.value b, h))
      | .partialType =>
        (partialNew W h (mc.args.map .val) mc.kwds).map (fun r => (.made r.1, r.2))

/-! ### Properties -/

/-- `methodcaller_reduce`, every branch: no keywords is `(type(mc), (name, *args))` and touches nothing; a failing
`import functools` propagates; a `Placeholder` among the values is `partial_new`'s `TypeError`; otherwise the
result is `partial(type(mc), name)` holding `mc->kwds` itself when the `methodcaller` was its only holder, and a
copy at a new address when anything else holds it. -/
def McReduceExact : Prop :=
  ∀ (α : Type) (W : PWorld α) (h : Heap α) (mc : McObj α) (d : Nat) (e : PyExc),
    W.callable .mcType = true → W.isPh (.str mc.name) = false →
    (mc.kwds = none → mcReduceC W (.ok ()) h mc = .ok (.plain (.str mc.name :: mc.args.map .val), h)) ∧
    (mc.kwds = some d → itemsAt h d = [] →
      ∀ imp, mcReduceC W imp h mc = .ok (.plain (.str mc.name :: mc.args.map .val), h)) ∧
    (mc.kwds = some d → itemsAt h d ≠ [] → mcReduceC W (.error e) h mc = .error e) ∧
    (mc.kwds = some d → itemsAt h d ≠ [] → (itemsAt h d).any (fun p => W.isPh (.val p.2)) = true →
      mcReduceC W (.ok ()) h mc = .error (.typeError "Placeholder cannot be passed as a keyword argument")) ∧
    (mc.kwds = some d → itemsAt h d ≠ [] → (itemsAt h d).any (fun p => W.isPh (.val p.2)) = false →
      refsAt h d = 1 →
      mcReduceC W (.ok ()) h mc = .ok (.viaPartial ⟨.mcType, [.str mc.name], d⟩ mc.args, incref h d)) ∧
    (mc.kwds = some d → itemsAt h d ≠ [] → (itemsAt h d).any (fun p => W.isPh (.val p.2)) = false →
      refsAt h d ≠ 1 →
      mcReduceC W (.ok ()) h mc =
        .ok (.viaPartial ⟨.mcType, [.str mc.name], h.length⟩ mc.args, h ++ [⟨(itemsAt h d).map some, 1⟩]))

theorem mcReduceExact_proven : McReduceExact := by
  intro α W h mc d e hc hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h1; simp [mcReduceC, h1]
  · intro h1 h2 imp; simp [mcReduceC, h1, h2]
  · intro h1 h2
    have : (itemsAt h d).length ≠ 0 := fun x => h2 (List.length_eq_zero_iff.mp x)
    simp [mcReduceC, h1, this]
  · intro h1 h2 h3
    have : (itemsAt h d).length ≠ 0 := fun x => h2 (List.length_eq_zero_iff.mp x)
    simp [mcReduceC, partialNew, h1, this, hc, hp, h3]
  · intro h1 h2 h3 h4
    have : (itemsAt h d).length ≠ 0 := fun x => h2 (List.length_eq_zero_iff.mp x)
    simp [mcReduceC, partialNew, h1, this, hc, hp, h3, h4]
  · intro h1 h2 h3 h4
    have : (itemsAt h d).length ≠ 0 := fun x => h2 (List.length_eq_zero_iff.mp x)
    simp [mcReduceC, partialNew, h1, this, hc, hp, h3, h4, alloc]

/-- The world of the counterexamples: everything is callable and nothing is the `Placeholder`. -/
def plainWorld (α : Type) : PWorld α := ⟨fun _ => true, fun _ => false⟩

/-- What `__reduce__` gives is independent of the `methodcaller`: writing to the keywords of the `partial` it
returns leaves `repr(mc)` as it was. The pickle protocol takes the reduce value as a recipe for a new object, and
the Python twin (Lib/operator.py:337-342) rebuilds the dict with `**self._kwargs`, so there it holds. False in C:
`partial_new` adopts `mc->kwds`, which only the `methodcaller` holds. `methodcaller('f', a=1)`, then
`p.keywords['a'] = 2`, prints `operator.methodcaller('f', a=2)`, while `mc(obj)` still passes `a=1` from the
vectorcall arguments stored at construction (gh-none; bugs/operator-methodcaller-reduce-shares-kwargs.yaml). -/
def McReduceIsolated : Prop :=
  ∀ (α : Type) (rep : α → Py String) (cls nameRepr name : String) (args : List α) (kw : List (String × α))
    (h h1 h2 : Heap α) (mc : McObj α) (p : PartialObj α) (pargs : List α) (k : Key) (v : α),
    mcFromCall h name args kw = .ok (mc, h1) →
    mcReduceC (plainWorld α) (.ok ()) h1 mc = .ok (.viaPartial p pargs, h2) →
    mcReprHeap rep false cls nameRepr (setKeyword h2 p k v) mc = mcReprHeap rep false cls nameRepr h2 mc

theorem mcReduceIsolated_refuted : ¬McReduceIsolated := by
  intro hI
  have := hI String (fun s => .ok s) "operator.methodcaller" "'f'" "f" [] [("a", "1")] []
    [⟨[some (.str "a", "1")], 1⟩] [⟨[some (.str "a", "1")], 2⟩] ⟨"f", [], some 0, some (["1"], [.str "a"])⟩
    ⟨.mcType, [.str "f"], 0⟩ [] (.str "a") "2" (by decide) (by decide)
  revert this
  decide

/-- `repr(mc)` is defined for every `methodcaller` built with keyword syntax, after anything Python does with what
`__reduce__` returned: writing any key into `partial.keywords` is ordinary Python. Built with keyword syntax, so
every key is a `str` (a non-`str` key passed with `**{1: 2}` is python/cpython#155733, not this). False in C: the
`partial` holds `mc->kwds`, and `p.keywords[1] = 2` puts an `int` key there, which `methodcaller_repr` formats
with `%U` (Modules/_operator.c:1838): a segfault on 3.15.2 and on main. -/
def McReduceNoCrash : Prop :=
  ∀ (α : Type) (rep : α → Py String) (cls nameRepr name : String) (args : List α) (kw : List (String × α))
    (h h1 h2 : Heap α) (mc : McObj α) (p : PartialObj α) (pargs : List α) (k : Key) (v : α),
    mcFromCall h name args kw = .ok (mc, h1) →
    mcReduceC (plainWorld α) (.ok ()) h1 mc = .ok (.viaPartial p pargs, h2) →
    (mcReprHeap rep false cls nameRepr (setKeyword h2 p k v) mc).isSome = true

theorem mcReduceNoCrash_refuted : ¬McReduceNoCrash := by
  intro hN
  have := hN String (fun s => .ok s) "operator.methodcaller" "'f'" "f" [] [("a", "1")] []
    [⟨[some (.str "a", "1")], 1⟩] [⟨[some (.str "a", "1")], 2⟩] ⟨"f", [], some 0, some (["1"], [.str "a"])⟩
    ⟨.mcType, [.str "f"], 0⟩ [] (.other 1) "2" (by decide) (by decide)
  revert this
  decide

/-- The same through a call: when `mc(obj)` returns a new `partial` (the method is `functools.partial` itself),
writing to that `partial`'s keywords leaves `repr(mc)` as it was. False on the `methodcaller_call` path, taken with
eight or more arguments: `PyObject_Call(method, mc->args, mc->kwds)` (Modules/_operator.c:1793) gives `partial_new`
the `methodcaller`'s own dict. On the vectorcall path the dict is new and this holds. -/
def McCallIsolated : Prop :=
  ∀ (α β : Type) (rep : α → Py String) (cls nameRepr name : String) (args : List α) (kw : List (String × α))
    (h h1 h2 : Heap α) (mc : McObj α) (q : PartialObj α) (k : Key) (v : α),
    mcFromCall h name args kw = .ok (mc, h1) →
    mcCallHeap (β := β) (plainWorld α) (.ok .partialType) h1 mc = .ok (.made q, h2) →
    mcReprHeap rep false cls nameRepr (setKeyword h2 q k v) mc = mcReprHeap rep false cls nameRepr h2 mc

/-- `methodcaller('f', print, k0=0, ..., k6=6)`: one name, one positional argument and seven keywords, eight in
all, so no vectorcall. -/
def bigKw : List (String × String) :=
  [("k0", "0"), ("k1", "1"), ("k2", "2"), ("k3", "3"), ("k4", "4"), ("k5", "5"), ("k6", "6")]

def bigItems : List (Key × String) := bigKw.map (fun p => (Key.str p.1, p.2))

theorem mcCallIsolated_refuted : ¬McCallIsolated := by
  intro hC
  have := hC String Unit (fun s => .ok s) "operator.methodcaller" "'f'" "f" ["print"] bigKw []
    [⟨bigItems.map some, 1⟩] [⟨bigItems.map some, 2⟩] ⟨"f", ["print"], some 0, none⟩
    ⟨.val "print", [], 0⟩ (.str "k0") "changed" (by decide) (by decide)
  revert this
  decide

/-- On the vectorcall path the call is isolated: a `partial` made by `mc(obj)` gets a dict of its own, at a new
address, so `repr(mc)` cannot see a write to it. -/
def McVectorcallFresh : Prop :=
  ∀ (α β : Type) (h h2 : Heap α) (mc : McObj α) (q : PartialObj α) (flat : List α) (names : List Key) (d : Nat),
    mc.vec = some (flat, names) → mc.kwds = some d → d < h.length →
    mcCallHeap (β := β) (plainWorld α) (.ok .partialType) h mc = .ok (.made q, h2) → q.kw ≠ d

/-- Where `partial_new` puts the keywords: a new dict at the end of the heap, or the one it was given. -/
theorem partialNew_kw {α : Type} (W : PWorld α) (h : Heap α) (args : List (PObj α)) (kw : Option Nat)
    (p : PartialObj α) (h' : Heap α) (hp : partialNew W h args kw = .ok (p, h')) :
    p.kw = h.length ∨ (kw = some p.kw ∧ refsAt h p.kw = 1) := by
  unfold partialNew at hp
  match args, kw with
  | [], _ => simp at hp
  | func :: rest, none =>
    simp only at hp
    split at hp
    · simp at hp
    split at hp
    · simp at hp
    split at hp
    · simp at hp
    simp only [alloc, Except.ok.injEq, Prod.mk.injEq] at hp
    exact Or.inl (by rw [← hp.1])
  | func :: rest, some d =>
    simp only at hp
    split at hp
    · simp at hp
    split at hp
    · simp at hp
    split at hp
    · simp at hp
    split at hp
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hp
      rw [← hp.1]
      exact Or.inr ⟨rfl, by assumption⟩
    · simp only [alloc, Except.ok.injEq, Prod.mk.injEq] at hp
      exact Or.inl (by rw [← hp.1])

theorem mcVectorcallFresh_proven : McVectorcallFresh := by
  intro α β h h2 mc q flat names d hv hk hd hc
  simp only [mcCallHeap, hv, Except.map] at hc
  split at hc
  · split at hc
    · simp at hc
    · rename_i r hp
      obtain ⟨p, h'⟩ := r
      simp only [Except.ok.injEq, Prod.mk.injEq, CallOut.made.injEq] at hc
      rcases partialNew_kw _ _ _ _ _ _ hp with h3 | ⟨h3, _⟩
      · rw [← hc.1, h3]; omega
      · simp at h3
  · split at hc
    · simp at hc
    · rename_i p h' hp
      simp only [Except.ok.injEq, Prod.mk.injEq, CallOut.made.injEq] at hc
      rcases partialNew_kw _ _ _ _ _ _ hp with h3 | ⟨h3, _⟩
      · rw [← hc.1, h3]; simp [alloc]; omega
      · simp only [alloc, Option.some.injEq] at h3
        rw [← hc.1, ← h3]; omega

/-! ### The size check of `methodcaller_repr` -/

/-- The keyword loop of `methodcaller_repr`, every step, for any `repr` and any heap: with no entry left it answers
the text exactly when it printed `numtotalargs` items, and is otherwise the `RuntimeError` of :1849-1853; an entry
past `numtotalargs` is the `RuntimeError` of :1841-1845, raised after that entry's `repr` ran; otherwise the entry is
printed and the loop goes on from the next index of the dict as the `repr` left it; a failing `repr` stops it; a key
that is not a `str` is undefined behaviour. -/
def McReprGuard : Prop :=
  ∀ (α : Type) (rep : RepS α) (d total fuel pos i j : Nat) (h h' : Heap α) (acc : List String) (s r : String)
    (v : α) (n : Int) (e : PyExc),
    (dictNext (entriesAt h d) pos = none → i = total →
      kwLoop rep d total (fuel + 1) pos i h acc = some (.ok acc, h)) ∧
    (dictNext (entriesAt h d) pos = none → i ≠ total →
      kwLoop rep d total (fuel + 1) pos i h acc = some (.error changedSize, h)) ∧
    (dictNext (entriesAt h d) pos = some (j, .str s, v) → rep v h = (.ok r, h') → total ≤ i →
      kwLoop rep d total (fuel + 1) pos i h acc = some (.error changedSize, h')) ∧
    (dictNext (entriesAt h d) pos = some (j, .str s, v) → rep v h = (.ok r, h') → i < total →
      kwLoop rep d total (fuel + 1) pos i h acc =
        kwLoop rep d total fuel (j + 1) (i + 1) h' (acc ++ [s ++ "=" ++ r])) ∧
    (dictNext (entriesAt h d) pos = some (j, .str s, v) → rep v h = (.error e, h') →
      kwLoop rep d total (fuel + 1) pos i h acc = some (.error e, h')) ∧
    (dictNext (entriesAt h d) pos = some (j, .other n, v) → kwLoop rep d total (fuel + 1) pos i h acc = none)

theorem mcReprGuard_proven : McReprGuard := by
  intro α rep d total fuel pos i j h h' acc s r v n e
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h1 h2; simp [kwLoop, h1, h2]
  · intro h1 h2; simp [kwLoop, h1, h2]
  · intro h1 h2 h3; simp [kwLoop, h1, h2, h3]
  · intro h1 h2 h3
    have : ¬ total ≤ i := by omega
    simp [kwLoop, h1, h2, this]
  · intro h1 h2; simp [kwLoop, h1, h2]
  · intro h1; simp [kwLoop, h1]

theorem posReprs_pure {α : Type} (rep : α → Py String) :
    ∀ (args : List α) (h : Heap α), posReprs (pureRep rep) args h = (mapPy rep args, h)
  | [], _ => rfl
  | a :: as, h => by
    simp only [posReprs, pureRep, mapPy]
    cases rep a with
    | error e => rfl
    | ok x =>
      have := posReprs_pure rep as h
      simp only [this]
      cases mapPy rep as <;> rfl

theorem kwLoop_pure {α : Type} (rep : α → Py String) (d total : Nat) (h : Heap α) :
    ∀ (items : List (Key × α)) (fuel pos i : Nat) (acc : List String),
      (entriesAt h d).drop pos = items.map some → i + items.length = total → items.length < fuel →
      kwLoop (pureRep rep) d total fuel pos i h acc =
        (kwReprs rep items).map (fun r => (r.map (acc ++ ·), h))
  | [], fuel, pos, i, acc, hd, hi, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hn : dictNext (entriesAt h d) pos = none := by simp [dictNext, hd, nextFrom]
    simp at hi
    simp [kwLoop, hn, hi, kwReprs, Except.map]
  | (k, v) :: rest, fuel, pos, i, acc, hd, hi, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hn : dictNext (entriesAt h d) pos = some (pos, k, v) := by
      simp only [dictNext, hd, List.map_cons, nextFrom]
    have hd' : (entriesAt h d).drop (pos + 1) = rest.map some := by
      rw [← List.tail_drop, hd]; rfl
    cases k with
    | other m => simp [kwLoop, hn, kwReprs]
    | str s =>
      simp only [List.length_cons] at hi hf
      cases hr : rep v with
      | error e => simp [kwLoop, hn, pureRep, hr, kwReprs, Except.map]
      | ok x =>
        have hlt : ¬ total ≤ i := by omega
        have ih := kwLoop_pure rep d total h rest f (pos + 1) (i + 1) (acc ++ [s ++ "=" ++ x]) hd' (by omega)
          (by omega)
        simp only [kwLoop, hn, pureRep, hr, hlt, ite_false]
        rw [ih]
        simp only [kwReprs, hr]
        cases kwReprs rep rest with
        | none => rfl
        | some q =>
          cases q with
          | error e => rfl
          | ok l => simp [Except.map]

/-- With reprs that write nothing, the size check never fires and `methodcaller_repr` over a compact keyword dict is
the name, the positional reprs and the `key=repr` items joined, the first failure being the outcome. -/
def McReprPure : Prop :=
  ∀ (α : Type) (rep : α → Py String) (cls nameRepr : String) (h : Heap α) (mc : McObj α) (d : Nat)
    (items : List (Key × α)),
    mc.kwds = some d → entriesAt h d = items.map some →
    mcReprHeap rep false cls nameRepr h mc =
      if mc.args.isEmpty && items.isEmpty then some (.ok (cls ++ "(" ++ nameRepr ++ ")")) else
      match mapPy rep mc.args with
      | .error e => some (.error e)
      | .ok a =>
        match kwReprs rep items with
        | none => none
        | some (.error e) => some (.error e)
        | some (.ok k) => some (.ok (cls ++ "(" ++ nameRepr ++ ", " ++ joinArgs (a ++ k) ++ ")"))

theorem mcReprPure_proven : McReprPure := by
  intro α rep cls nameRepr h mc d items hk he
  have hl : (itemsAt h d).length = items.length := by
    simp only [itemsAt, he]
    induction items with
    | nil => rfl
    | cons x xs ih => simp [ih]
  have hz : (mc.args.length + items.length = 0) ↔ (mc.args.isEmpty && items.isEmpty) = true := by
    simp [List.isEmpty_iff, List.length_eq_zero_iff]
  simp only [mcReprHeap, mcReprHeapS, Bool.false_eq_true, ite_false, hk, hl, posReprs_pure]
  by_cases h0 : mc.args.length + items.length = 0
  · simp [h0, hz.mp h0]
  · have h0' : ¬ (mc.args.isEmpty && items.isEmpty) = true := fun x => h0 (hz.mpr x)
    simp only [h0, ite_false, h0', Bool.false_eq_true]
    cases hm : mapPy rep mc.args with
    | error e => rfl
    | ok a =>
      simp only
      by_cases hi : items.length = 0
      · have : items = [] := List.length_eq_zero_iff.mp hi
        subst this
        simp [kwReprs, Except.map]
      · have hk2 := kwLoop_pure rep d (mc.args.length + items.length) h items
          (mc.args.length + items.length + 1) 0 mc.args.length [] (by simp [he]) rfl (by omega)
        simp only [hi, ite_false, hk2]
        cases kwReprs rep items with
        | none => rfl
        | some q => cases q <;> rfl

/-- What a value's `__repr__` does to `p.keywords` in the cases measured on 3.15.2: add a key `zz`, delete `a` or
`b`, clear the dict, or set `b` to `"9"`; any other value prints itself. -/
def mutRep (p : PartialObj String) : RepS String := fun v h =>
  if v = "add" then (.ok "V", setKeyword h p (.str "zz") "0")
  else if v = "del_a" then (.ok "V", delKeyword h p (.str "a"))
  else if v = "del_b" then (.ok "V", delKeyword h p (.str "b"))
  else if v = "clear" then (.ok "V", clearKeywords h p)
  else if v = "set_b" then (.ok "V", setKeyword h p (.str "b") "9")
  else (.ok v, h)

/-- `repr(mc)` for `mc = methodcaller('f', **kw)` once `p = mc.__reduce__()[0]` shares the dict, the values' reprs
writing to `p.keywords`. -/
def reprAfter (kw : List (String × String)) : Option (Py String) :=
  match mcFromCall [] "f" [] kw with
  | .error _ => none
  | .ok (mc, h1) =>
    match mcReduceC (plainWorld String) (.ok ()) h1 mc with
    | .ok (.viaPartial p _, h2) => (mcReprHeapS (mutRep p) false "operator.methodcaller" "'f'" h2 mc).map Prod.fst
    | _ => none

/-- The size check reached through the shared dict, as measured on 3.15.2 and main: a key added anywhere, a key
deleted before it is reached, or a clear before the end is `RuntimeError`; a key deleted after it was printed, a
clear at the last item, a value changed in place, and a deletion balanced by an addition are not, and the text
shows what the loop read. -/
def McReprMutations : Prop :=
  reprAfter [("a", "add"), ("b", "1")] = some (.error changedSize) ∧
  reprAfter [("a", "1"), ("b", "add")] = some (.error changedSize) ∧
  reprAfter [("a", "del_b"), ("b", "1")] = some (.error changedSize) ∧
  reprAfter [("a", "1"), ("b", "del_a")] = some (.ok "operator.methodcaller('f', a=1, b=V)") ∧
  reprAfter [("a", "del_a"), ("b", "1")] = some (.ok "operator.methodcaller('f', a=V, b=1)") ∧
  reprAfter [("a", "clear"), ("b", "1")] = some (.error changedSize) ∧
  reprAfter [("a", "1"), ("b", "clear")] = some (.ok "operator.methodcaller('f', a=1, b=V)") ∧
  reprAfter [("a", "set_b"), ("b", "1")] = some (.ok "operator.methodcaller('f', a=V, b=9)") ∧
  reprAfter [("a", "del_b"), ("b", "1"), ("c", "add")] = some (.ok "operator.methodcaller('f', a=V, c=V, zz=0)")

theorem mcReprMutations_proven : McReprMutations := by unfold McReprMutations; decide

end PyLean.CoreLibs.Operator.McShare
