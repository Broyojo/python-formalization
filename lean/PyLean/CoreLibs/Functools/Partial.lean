import PyLean.CoreLibs.Functools.Lru

/-!
`partial`, `partialmethod` and `Placeholder`, Lib/functools.py:273-514 and
Modules/_functoolsmodule.c:63-110, 168-768.

`_partial_new` is one body with a class-specific head, so `newCore` is the shared part and `partialNewPy`
and `partialmethodNew` are the two heads. The order list and `itemgetter(*order)` of
`_partial_prepare_merger` are mirrored by `prepareMerger` and `itemget`; `fill` and `fillCall` are the
structural form of the same loops, and PartialProps.lean proves that they agree.

In a call the arguments are `List α`: neither twin compares a call argument with `Placeholder`, so an actual
`Placeholder` passed in a call is an opaque `α`. `_merger` is not a field of `Fn`: every assignment of it,
Lib/functools.py:356 and :432, writes the merger of the `args` assigned next to it.
-/

namespace PyLean.CoreLibs.Functools

open PyLean

/-- A stored positional argument: `Placeholder`, or any other object. -/
inductive PArg (α : Type) where
  | ph
  | val (a : α)
  deriving Repr, DecidableEq, Inhabited

/-- A callable, or what is in the place of one. `dict` of `pobj` is `__dict__`, `none` while it was never
created; `override` is the identity of a subclass's `__call__`. `bound` is a `MethodType`. -/
inductive Fn (α : Type) where
  | base (id : Nat)
  | notCallable
  /-- A callable whose call raises. -/
  | fails (e : PyExc)
  | bound (f : Fn α) (self : α)
  | pobj (override : Option Nat) (dict : Option (List (String × α))) (func : Fn α)
      (args : List (PArg α)) (kw : List (String × α)) (phcount : Nat)
  deriving Repr, DecidableEq

def Fn.isCallable {α : Type} : Fn α → Bool
  | .notCallable => false
  | _ => true

def isPh {α : Type} : PArg α → Bool
  | .ph => true
  | .val _ => false

def phCount {α : Type} (args : List (PArg α)) : Nat := (args.filter isPh).length

/-- `{**a, **b}`: later keys keep the first position and take the later value. -/
def mergeKw {α : Type} (a b : List (String × α)) : List (String × α) :=
  b.foldl (fun acc p =>
    if acc.any (fun q => q.1 == p.1) then acc.map (fun q => if q.1 == p.1 then p else q)
    else acc ++ [p]) a

/-- Fill the placeholders of `base` from `new`, left to right. A placeholder with nothing left stays;
what is left of `new` after the last slot goes at the end. This is the loop at
Modules/_functoolsmodule.c:262-277, with `i` walking `base` and `j` walking `new`. -/
def fill {α : Type} : List (PArg α) → List (PArg α) → List (PArg α)
  | [], new => new
  | .ph :: rest, n :: new => n :: fill rest new
  | .ph :: rest, [] => .ph :: fill rest []
  | a :: rest, new => a :: fill rest new

def trailingPh {α : Type} (args : List (PArg α)) : Bool :=
  match args.getLast? with
  | some .ph => true
  | _ => false

def trailingMsg := "trailing Placeholders are not allowed"
def kwPhMsg := "Placeholder cannot be passed as a keyword argument"

def kwVals {α : Type} (kw : List (String × PArg α)) : Option (List (String × α)) :=
  kw.mapM (fun p => match p.2 with
    | .val a => some (p.1, a)
    | .ph => none)

/-- The loop of `_partial_prepare_merger`, Lib/functools.py:303-308: the position each slot takes its
value from, and the final `j`. -/
def orderLoop {α : Type} : List (PArg α) → Nat → Nat → List Nat × Nat
  | [], _, j => ([], j)
  | .ph :: rest, i, j =>
    let r := orderLoop rest (i + 1) (j + 1)
    (j :: r.1, r.2)
  | .val _ :: rest, i, j =>
    let r := orderLoop rest (i + 1) j
    (i :: r.1, r.2)

/-- `_partial_prepare_merger(args)`, Lib/functools.py:297-311, split so that `__setstate__` can give the
length of the tuple and its iteration separately: `len(args)` is `n`, `enumerate(args)` walks `items`. The
merger is its order list. `itemgetter` of one index returns a bare item, but a one-element tuple with a
placeholder is a trailing placeholder, which every caller has rejected. -/
def prepareMergerOf {α : Type} (n : Nat) (items : List (PArg α)) : Nat × Option (List Nat) :=
  if n = 0 then (0, none) else
  let r := orderLoop items 0 n
  let phcount := r.2 - n
  (phcount, if phcount ≠ 0 then some r.1 else none)

def prepareMerger {α : Type} (args : List (PArg α)) : Nat × Option (List Nat) :=
  prepareMergerOf args.length args

/-- `itemgetter(*order)(t)`, with the `IndexError` of a position past the end of the tuple. -/
def itemget {β : Type} (order : List Nat) (t : List β) : Py (List β) :=
  mapPy (fun i => match t[i]? with
    | some v => .ok v
    | none => .error (.indexError "tuple index out of range")) order

/-- Lines 324-349 of `_partial_new`, Lib/functools.py, shared by both classes: `inner` is `func`'s
`(args, keywords, _phcount)` when `isinstance(func, base_cls)`. The result is `tot_args`, the keywords and
`phcount`. -/
def newCore {α : Type} (args : List (PArg α)) (kw : List (String × PArg α))
    (inner : Option (List (PArg α) × List (String × α) × Nat)) :
    Py (List (PArg α) × List (String × α) × Nat) :=
  if trailingPh args then .error (.typeError trailingMsg) else
  match kwVals kw with
  | none => .error (.typeError kwPhMsg)
  | some kw' =>
    match inner with
    | none => .ok (args, kw', (prepareMerger args).1)
    | some (pargs, pkw, pph) =>
      if args.isEmpty then .ok (pargs, mergeKw pkw kw', pph)
      else
        let tot := pargs ++ args
        if pph ≠ 0 then
          let nargs := args.length
          let tot := if nargs < pph then tot ++ List.replicate (pph - nargs) .ph else tot
          match (prepareMerger pargs).2 with
          | none => .error .modelFuel  -- `pph ≠ 0` means `func._merger` is not `None`
          | some order =>
            match itemget order tot with
            | .error e => .error e
            | .ok tot =>
              let tot := if nargs > pph then tot ++ args.drop pph else tot
              .ok (tot, mergeKw pkw kw', (prepareMerger tot).1)
        else .ok (tot, mergeKw pkw kw', (prepareMerger tot).1)

/-- The `partial` head of `_partial_new`, Lib/functools.py:314-317, 329, 346, 351-357. Every `isinstance` of
`partial` is flattened, so a subclass's `__call__` is dropped. `outer` is the new object's own `override`. -/
def partialNewPy {α : Type} (outer : Option Nat) (func : Fn α) (args : List (PArg α))
    (kw : List (String × PArg α)) : Py (Fn α) :=
  if !func.isCallable then .error (.typeError "the first argument must be callable") else
  match func with
  | .pobj _ _ inner pargs pkw pph =>
    match newCore args kw (some (pargs, pkw, pph)) with
    | .error e => .error e
    | .ok (t, k, p) => .ok (.pobj outer none inner t k p)
  | _ =>
    match newCore args kw none with
    | .error e => .error e
    | .ok (t, k, p) => .ok (.pobj outer none func t k p)

/-- An object whose `__class__` claims `partial`, with the attributes one has. `isinstance` at Lib/functools.py:329 accepts it
through `__class__`, so the Python class takes it apart like a `partial`. -/
def duckNewPy {α : Type} (outer : Option Nat) (inner : Fn α) (pargs : List (PArg α)) (pkw : List (String × α)) (pph : Nat)
    (args : List (PArg α)) (kw : List (String × PArg α)) : Py (Fn α) :=
  match newCore args kw (some (pargs, pkw, pph)) with
  | .error e => .error e
  | .ok (t, k, p) => .ok (.pobj outer none inner t k p)

/-- The checks of `partial_new`, Modules/_functoolsmodule.c:181-211, in that order. -/
def validateNew {α : Type} (func : Fn α) (args : List (PArg α)) (kw : List (String × PArg α)) :
    Py (List (String × α)) :=
  if !func.isCallable then .error (.typeError "the first argument must be callable")
  else if trailingPh args then .error (.typeError trailingMsg)
  else
    match kwVals kw with
    | none => .error (.typeError kwPhMsg)
    | some kw' => .ok kw'

/-- The flattening of `partial_new`, Modules/_functoolsmodule.c:213-295, which takes a `partial`
instance apart only when its `__dict__` was never created, :219-230. -/
def flattenC {α : Type} (outer : Option Nat) (func : Fn α) (args : List (PArg α))
    (kw' : List (String × α)) : Fn α :=
  match func with
  | .pobj _ none inner pargs pkw pph =>
    let newPh := phCount args
    if pph > 0 ∧ !args.isEmpty then
      let tot := fill pargs args
      .pobj outer none inner tot (mergeKw pkw kw') (pph - min pph args.length + newPh)
    else
      .pobj outer none inner (pargs ++ args) (mergeKw pkw kw') (pph + newPh)
  | _ => .pobj outer none func args kw' (phCount args)

def partialNewC {α : Type} (outer : Option Nat) (func : Fn α) (args : List (PArg α))
    (kw : List (String × PArg α)) : Py (Fn α) := do
  pure (flattenC outer func args (← validateNew func args kw))

/-- `partial()` with no function at all: :174-178 in C, and the signature of `_partial_new` in Python. -/
def partialNoFuncC : PyExc := .typeError "type 'partial' takes at least one argument"
def partialNoFuncPy : PyExc :=
  .typeError "_partial_new() missing 1 required positional argument: 'func'"

/-- A completed call: which function, with which positional and keyword arguments. -/
structure Called (α : Type) where
  id : Nat
  args : List α
  kw : List (String × α)
  deriving Repr, DecidableEq

def missingMsg (phcount got : Nat) : String :=
  s!"missing positional arguments in 'partial' call; expected at least {phcount}, got {got}"

/-- The merged positional arguments of a call with enough arguments. -/
def fillCall {α : Type} : List (PArg α) → List α → List α
  | [], new => new
  | .ph :: rest, n :: new => n :: fillCall rest new
  | .ph :: rest, [] => fillCall rest []
  | .val a :: rest, new => a :: fillCall rest new

/-- Calling a function object. -/
def callFn {α : Type} : Fn α → List α → List (String × α) → Py (Called α)
  | .base id, args, kw => .ok ⟨id, args, kw⟩
  | .notCallable, _, _ => .error (.typeError "~object is not callable")
  | .fails e, _, _ => .error e
  | .bound f self, args, kw => callFn f (self :: args) kw
  | .pobj (some o) _ _ _ _ _, args, kw => .ok ⟨o, args, kw⟩
  | .pobj none _ func pargs pkw ph, args, kw =>
    if args.length < ph then .error (.typeError (missingMsg ph args.length))
    else callFn func (fillCall pargs args) (mergeKw pkw kw)

def valsOf {α : Type} (l : List (PArg α)) : List α :=
  l.filterMap (fun a => match a with
    | .val v => some v
    | .ph => none)

/-- `partial.__call__`, Lib/functools.py:380-393, on a plain `partial`: `self._merger(self.args + args)`, whose
`IndexError` becomes the `TypeError`, then `args[phcount:]`. -/
def partialCallPy {α : Type} (func : Fn α) (pargs : List (PArg α)) (pkw : List (String × α))
    (ph : Nat) (args : List α) (kw : List (String × α)) : Py (Called α) :=
  if ph ≠ 0 then
    match (prepareMerger pargs).2 with
    | none => .error .modelFuel
    | some order =>
      match itemget order (pargs ++ args.map .val) with
      | .error _ => .error (.typeError (missingMsg ph args.length))
      | .ok pto => callFn func (valsOf pto ++ args.drop ph) (mergeKw pkw kw)
  else callFn func (valsOf pargs ++ args) (mergeKw pkw kw)

/-- A read past the end of the call's argument array, which C does not check. -/
def oobRead : PyExc := .named "SIGSEGV" "read past the end of the call arguments"

/-- The first loop of the merge in `partial_call`, Modules/_functoolsmodule.c:550-558, and of
`partial_vectorcall`, :450-458: `none` when `args[j]` is past the end. -/
def cMergeLoop {α : Type} (args : List α) : List (PArg α) → Nat → Option (List α × Nat)
  | [], j => some ([], j)
  | .ph :: rest, j =>
    match args[j]? with
    | none => none
    | some a => (cMergeLoop args rest (j + 1)).map (fun r => (a :: r.1, r.2))
  | .val v :: rest, j => (cMergeLoop args rest j).map (fun r => (v :: r.1, r.2))

/-- The whole merge, with `phcount` taken from the object as C does: the second loop, :560-565, copies
`nargs - phcount` items from `j` on. -/
def cMerge {α : Type} (pargs : List (PArg α)) (ph : Nat) (args : List α) : Option (List α) :=
  match cMergeLoop args pargs 0 with
  | none => none
  | some (h, j) =>
    if j + (args.length - ph) ≤ args.length then some (h ++ (args.drop j).take (args.length - ph))
    else none

/-- `partial_call`, Modules/_functoolsmodule.c:497-580. -/
def partialCallC {α : Type} (func : Fn α) (pargs : List (PArg α)) (pkw : List (String × α))
    (ph : Nat) (args : List α) (kw : List (String × α)) : Py (Called α) :=
  if args.length < ph then .error (.typeError (missingMsg ph args.length))
  else
    let totKw := if pkw.isEmpty then kw else mergeKw pkw kw
    if ph ≠ 0 then
      match cMerge pargs ph args with
      | none => .error oobRead
      | some tot => callFn func tot totKw
    else callFn func (valsOf pargs ++ args) totKw

/-- A `memcpy` past the end of the stack array, which C does not check. -/
def oobWrite : PyExc := .named "SIGABRT" "write past the end of the stack array"

/-- The merge of `partial_vectorcall`, :450-462. The stack holds `pto_nargs + nargs - phcount` items, sized by
`phcount`, and the `memcpy` at :460-462 copies `nargs - j` items after the stored ones, so it stays inside only
when `j` is `phcount`. -/
def vecMerge {α : Type} (pargs : List (PArg α)) (ph : Nat) (args : List α) : Py (List α) :=
  match cMergeLoop args pargs 0 with
  | none => .error oobRead
  | some (_, j) =>
    if ph < args.length ∧ j ≠ ph then .error oobWrite
    else
      match cMerge pargs ph args with
      | none => .error oobRead
      | some tot => .ok tot

/-- `partial_vectorcall`, Modules/_functoolsmodule.c:386-476, reached when the wrapped function
supports vectorcall (`partial_setvectorcall`, :480-492); `partial_vectorcall_fallback`, :374-383,
sends a `partial` with stored keywords to `partial_call`. The fast path for a one-element tuple, :419-428,
gives the same call on a well-formed object, where such a tuple has no placeholder. -/
def partialVectorcall {α : Type} (func : Fn α) (pargs : List (PArg α)) (pkw : List (String × α))
    (ph : Nat) (args : List α) (kw : List (String × α)) : Py (Called α) :=
  if !pkw.isEmpty then partialCallC func pargs pkw ph args kw
  else if args.length < ph then .error (.typeError (missingMsg ph args.length))
  else if ph ≠ 0 then
    match vecMerge pargs ph args with
    | .error e => .error e
    | .ok tot => callFn func tot kw
  else callFn func (valsOf pargs ++ args) kw

/-- `partial.__get__`, Lib/functools.py:395-398, `partial_descr_get`, Modules/_functoolsmodule.c:362-368, and
`lru_cache_descr_get`, :1658-1664: `None` gives the object itself, anything else a `MethodType`. -/
def descrGet {α : Type} (self : Fn α) (obj : Option α) : Fn α :=
  match obj with
  | none => self
  | some o => .bound self o

/-! ### `repr` -/

/-- The `repr` of the stored values, which may raise. -/
structure ReprEnv (α : Type) where
  val : α → Py String

def argRepr {α : Type} (E : ReprEnv α) : PArg α → Py String
  | .ph => .ok "Placeholder"
  | .val a => E.val a

/-- `{k}={v!r}`. -/
def kwRepr {α : Type} (E : ReprEnv α) (p : String × α) : Py String :=
  match E.val p.2 with
  | .error e => .error e
  | .ok v => .ok (p.1 ++ "=" ++ v)

/-- `', '.join(l)`. -/
def joinComma : List String → String
  | [] => ""
  | x :: xs => xs.foldl (fun a s => a ++ ", " ++ s) x

/-- `_partial_repr`, Lib/functools.py:359-366: `repr(self.func)`, then the arguments, then the keywords. -/
def partialReprPy {α : Type} (E : ReprEnv α) (cls : String) (func : Py String)
    (args : List (PArg α)) (kw : List (String × α)) : Py String := do
  let f ← func
  let a ← mapPy (argRepr E) args
  let k ← mapPy (kwRepr E) kw
  pure (cls ++ "(" ++ joinComma (f :: a ++ k) ++ ")")

/-- The fold at Modules/_functoolsmodule.c:639-646 and :648-661: `arglist` grows by `", x"`. -/
def reprFold {β : Type} (f : β → Py String) : String → List β → Py String
  | acc, [] => .ok acc
  | acc, x :: xs =>
    match f x with
    | .error e => .error e
    | .ok s => reprFold f (acc ++ ", " ++ s) xs

/-- `partial_repr`, Modules/_functoolsmodule.c:610-687: the arguments, the keywords, and `repr(fn)` last. -/
def partialReprC {α : Type} (E : ReprEnv α) (cls : String) (func : Py String)
    (args : List (PArg α)) (kw : List (String × α)) : Py String := do
  let a ← reprFold (argRepr E) "" args
  let l ← reprFold (kwRepr E) a kw
  let f ← func
  pure (cls ++ "(" ++ f ++ l ++ ")")

/-- The generator of `_partial_repr`, Lib/functools.py:365: `mut v` says that `repr(v)` changes the size of `self.keywords`, so
the iterator raises `RuntimeError` at its next step, the last one too. -/
def kwLoopPy {α : Type} (E : ReprEnv α) (grows : α → Bool) : List (String × α) → Py (List String)
  | [] => .ok []
  | p :: r =>
    match kwRepr E p with
    | .error e => .error e
    | .ok s =>
      if grows p.2 then .error (.named "RuntimeError" "dictionary changed size during iteration")
      else
        match kwLoopPy E grows r with
        | .error e => .error e
        | .ok l => .ok (s :: l)

/-- The `PyDict_Next` loop of `partial_repr`, Modules/_functoolsmodule.c:648-661, which has no check on the size: a `repr` that
adds `extra` to the dict only makes the loop go further. -/
def kwLoopC {α : Type} (E : ReprEnv α) (grows : α → Bool) (extra : String × α) : String → List (String × α) → Py String
  | acc, [] => .ok acc
  | acc, p :: r =>
    match kwRepr E p with
    | .error e => .error e
    | .ok s =>
      if grows p.2 then reprFold (kwRepr E) (acc ++ ", " ++ s) (r ++ [extra])
      else kwLoopC E grows extra (acc ++ ", " ++ s) r

/-- `_partial_repr`, Lib/functools.py:359-366, with each read: `cls.__module__`, `cls.__qualname__`, which a metaclass can
intercept, `repr(self.func)`, the arguments and the keywords, in order. -/
def partialReprFullPy {α : Type} (E : ReprEnv α) (grows : α → Bool) (mod qual : Py String) (func : Py String)
    (args : List (PArg α)) (kw : List (String × α)) : Py String := do
  let m ← mod
  let q ← qual
  let f ← func
  let a ← mapPy (argRepr E) args
  let k ← kwLoopPy E grows kw
  pure (m ++ "." ++ q ++ "(" ++ joinComma (f :: a ++ k) ++ ")")

/-- `partial_repr`, Modules/_functoolsmodule.c:610-687, in its order: the arguments, the keywords, the module and the qualified
name from the type itself, and `repr(fn)` last. -/
def partialReprFullC {α : Type} (E : ReprEnv α) (grows : α → Bool) (extra : String × α) (cls : String) (func : Py String)
    (args : List (PArg α)) (kw : List (String × α)) : Py String := do
  let a ← reprFold (argRepr E) "" args
  let l ← kwLoopC E grows extra a kw
  let f ← func
  pure (cls ++ "(" ++ f ++ l ++ ")")

/-- `recursive_repr()` around `_partial_repr`, Lib/reprlib.py:12-29, and `Py_ReprEnter`, :619-625:
`running` says the object is already being repr'd on this thread. `partialmethod.__repr__` has no guard,
Lib/functools.py:451. -/
def reprGuard (running : Bool) (body : Py String) : Py String :=
  if running then .ok "..." else body

/-! ### `__reduce__` and `__setstate__` -/

/-- A tuple subclass in a state. `raw` is what `PyTuple_GET_ITEM` sees, so what C reads. The Python twin goes through the
protocol, which a subclass can override: `truth` is `bool(args)` at Lib/functools.py:415, `last` is `args[-1]` there, `len` is
`len(args)` at :300, and `iter1` and `iter2` are the iterations at :303 and :419, which a stateful `__iter__` can make differ.
C iterates once, at Modules/_functoolsmodule.c:739-743, which is `iter1`. -/
structure TupSub (α : Type) where
  raw : List (PArg α)
  truth : Py Bool
  last : Py (PArg α)
  len : Py Nat
  iter1 : Py (List (PArg α))
  iter2 : Py (List (PArg α))

/-- A tuple subclass that overrides none of this, the case `tuple(args)` at Lib/functools.py:419 exists for. -/
def TupSub.honest {α : Type} (raw : List (PArg α)) : TupSub α :=
  ⟨raw, .ok (!raw.isEmpty), .ok (raw.getLast?.getD .ph), .ok raw.length, .ok raw, .ok raw⟩

/-- A tuple subclass with its own `__iter__`, the same on each iteration. -/
def TupSub.iterates {α : Type} (raw : List (PArg α)) (it : Py (List (PArg α))) : TupSub α :=
  { TupSub.honest raw with iter1 := it, iter2 := it }

/-- The second item of a state. -/
inductive StArgs (α : Type) where
  | tuple (items : List (PArg α))
  | sub (t : TupSub α)
  | other

/-- The third item of a state. -/
inductive StKw (α : Type) where
  | none
  | exact (items : List (String × α))
  /-- A dict subclass with these items, and the exception `dict(kwds)` raises from an overridden `keys` or
  `__iter__`. `PyDict_Copy` skips the items of an empty dict, so C does not run them there. -/
  | sub (items : List (String × α)) (fail : Option PyExc)
  | other

/-- The fourth item of a state. A dict is stored as it is, so a subclass is no different from a dict. -/
inductive StNs (α : Type) where
  | none
  | dict (items : List (String × α))
  | other

/-- The argument of `__setstate__`. -/
inductive PState (α : Type) where
  | notTuple
  | size (n : Nat)
  | four (func : Fn α) (args : StArgs α) (kw : StKw α) (ns : StNs α)

def StArgs.raw {α : Type} : StArgs α → Option (List (PArg α))
  | .tuple i => some i
  | .sub t => some t.raw
  | .other => none

/-- Whether the tuple and dict checks at Lib/functools.py:410-412, Modules/_functoolsmodule.c:716-719, pass. -/
def stateShapeOk {α : Type} (func : Fn α) (args : StArgs α) (kw : StKw α) (ns : StNs α) : Bool :=
  func.isCallable && (args.raw.isSome) &&
    (match kw with
     | .other => false
     | _ => true) &&
    (match ns with
     | .other => false
     | _ => true)

def invalidState := "invalid partial state"

/-- `args and args[-1] is Placeholder`, once `bool(args)` is `b`. -/
def lastIsPh {α : Type} (t : TupSub α) (b : Bool) : Py Bool :=
  if b then
    match t.last with
    | .error e => .error e
    | .ok a => .ok (isPh a)
  else .ok false

/-- The reads of `args` in `partial.__setstate__`, Lib/functools.py:415-419, in order: the items that are kept, and
`phcount`. `_partial_prepare_merger` starts with `if not args`, at :298, so with `args` false it reads nothing more. -/
def pyHead {α : Type} (t : TupSub α) : Py (List (PArg α) × Nat) :=
  match t.truth with
  | .error e => .error e
  | .ok b =>
    match lastIsPh t b with
    | .error e => .error e
    | .ok true => .error (.typeError trailingMsg)
    | .ok false =>
      if !b then
        -- the only iteration is the one at :419
        match t.iter1 with
        | .error e => .error e
        | .ok it => .ok (it, 0)
      else
      match t.len with
      | .error e => .error e
      | .ok n =>
        match t.iter1 with
        | .error e => .error e
        | .ok it1 =>
          match t.iter2 with
          | .error e => .error e
          | .ok it2 => .ok (it2, (prepareMergerOf n it1).1)

/-- `partial.__setstate__`, Lib/functools.py:404-432, as a replacement of the object. Nothing is assigned
until every step that can raise has passed, so a failure leaves the object as it was. `__dict__` is
always set; the mirror writes `some`. -/
def setstatePy {α : Type} (outer : Option Nat) : PState α → Py (Fn α)
  | .notTuple => .error (.typeError "argument to __setstate__ must be a tuple")
  | .size n => .error (.typeError s!"expected 4 items in state, got {n}")
  | .four func args kw ns =>
    if !stateShapeOk func args kw ns then .error (.typeError invalidState) else
    match args.raw with
    | none => .error (.typeError invalidState)
    | some raw =>
      let t := match args with
        | .sub t => t
        | _ => TupSub.honest raw
      match pyHead t with
      | .error e => .error e
      | .ok (items, phcount) =>
        let kwds : Py (List (String × α)) :=
          match kw with
          | .exact d => .ok d
          | .sub d none => .ok d
          | .sub _ (some e) => .error e
          | _ => .ok []
        match kwds with
        | .error e => .error e
        | .ok d =>
          let n := match ns with
            | .dict x => x
            | _ => []
          .ok (.pobj outer (some n) func items d phcount)

/-- `partial_setstate`, Modules/_functoolsmodule.c:706-768. The placeholders are counted on the raw tuple
at :732-737, and `PySequence_Tuple` runs after that, at :739-743, so `phcount` can describe another tuple. -/
def setstateC {α : Type} (outer : Option Nat) : PState α → Py (Fn α)
  | .notTuple | .size _ => .error (.typeError invalidState)
  | .four func args kw ns =>
    if !stateShapeOk func args kw ns then .error (.typeError invalidState) else
    match args.raw with
    | none => .error (.typeError invalidState)
    | some raw =>
      if trailingPh raw then .error (.typeError trailingMsg) else
      let phcount := phCount raw
      let items : Py (List (PArg α)) :=
        match args with
        | .sub t => t.iter1
        | _ => .ok raw
      match items with
      | .error e => .error e
      | .ok items =>
        let kwds : Py (List (String × α)) :=
          match kw with
          | .exact d => .ok d
          | .sub [] _ => .ok []
          | .sub d none => .ok d
          | .sub _ (some e) => .error e
          | _ => .ok []
        match kwds with
        | .error e => .error e
        | .ok d =>
          let dict := match ns with
            | .dict x => some x
            | _ => none
          .ok (.pobj outer dict func items d phcount)

/-- `partial.__reduce__`, Lib/functools.py:400-402: the state of a `partial`, with empty keywords and an
empty `__dict__` written as `None`. -/
def pReducePy {α : Type} : Fn α → PState α
  | .pobj _ d f a k _ =>
    .four f (.tuple a) (if k.isEmpty then .none else .exact k)
      (match d with
       | some (x :: xs) => .dict (x :: xs)
       | _ => .none)
  | _ => .notTuple

/-- `partial_reduce`, Modules/_functoolsmodule.c:697-703: keeps the empty dict of keywords, and a created
`__dict__` even when it is empty. -/
def pReduceC {α : Type} : Fn α → PState α
  | .pobj _ d f a k _ =>
    .four f (.tuple a) (.exact k)
      (match d with
       | some x => .dict x
       | none => .none)
  | _ => .notTuple

/-- The first and second items of the `__reduce__` tuple give a fresh object, which the state then replaces. -/
def unpickleWith {α : Type} (new : Option Nat → Fn α → List (PArg α) → List (String × PArg α) → Py (Fn α))
    (set : Option Nat → PState α → Py (Fn α)) (reduce : Fn α → PState α) (self : Fn α) : Py (Fn α) :=
  match self with
  | .pobj o _ f _ _ _ =>
    match new o f [] [] with
    | .error e => .error e
    | .ok _ => set o (reduce self)
  | _ => .error (.typeError "~not a partial")

/-! ### `Placeholder` -/

/-- The class attribute `__instance`, Lib/functools.py:278, or `state->placeholder`, Modules/_functoolsmodule.c,
and the next free identity in the heap. -/
structure PhState where
  inst : Option Nat := none
  next : Nat := 0
  deriving Repr, DecidableEq

/-- `_PlaceholderType.__new__`, Lib/functools.py:284-287. The result is an object identity: without the
test at :285 each call would allocate a new one. -/
def placeholderNewPy (s : PhState) : Nat × PhState :=
  match s.inst with
  | some i => (i, s)
  | none => (s.next, { inst := some s.next, next := s.next + 1 })

/-- `placeholder_new`, Modules/_functoolsmodule.c:89-109. The Python twin's `__new__(cls)` rejects arguments
through its signature. -/
def placeholderNewC (nargs : Nat) (s : PhState) : Py (Nat × PhState) :=
  if nargs ≠ 0 then .error (.typeError "PlaceholderType takes no arguments") else
  match s.inst with
  | some i => .ok (i, s)
  | none => .ok (s.next, { inst := some s.next, next := s.next + 1 })

/-- `_PlaceholderType.__init_subclass__`, Lib/functools.py:281-282: any class statement raises, and names
the new class. -/
def placeholderSubclassPy (name : String) : PyExc :=
  .typeError s!"type '{name}' is not an acceptable base type"

/-- The C type has no `Py_TPFLAGS_BASETYPE`, so `type.__new__` raises and names the base. -/
def placeholderSubclassC : PyExc :=
  .typeError "type 'functools._PlaceholderType' is not an acceptable base type"

def placeholderRepr : String := "Placeholder"
def placeholderReduce : String := "Placeholder"

/-- `_unwrap_partial`, Lib/functools.py:500-503. -/
def unwrapPartial {α : Type} : Fn α → Fn α
  | .pobj _ _ f _ _ _ => unwrapPartial f
  | f => f

/-! ### `partialmethod` -/

/-- What `self.func` of a `partialmethod` is, which decides `getattr(self.func, "__get__", None)`. -/
inductive MKind (α : Type) where
  /-- A plain function. -/
  | fn (id : Nat)
  /-- `classmethod(f)`, which is not callable. -/
  | classm (id : Nat)
  /-- `staticmethod(f)`, whose `__get__` returns `f`. -/
  | staticm (id : Nat)
  /-- A callable, or a non-callable, without `__get__`. -/
  | obj (f : Fn α)
  /-- A `partial`, whose `__get__` is `partial.__get__`. -/
  | partialObj (f : Fn α)
  /-- A user descriptor. `get` is the result of its `__get__`, with `none` for `self.func` itself, `selfAttr`
  reads `__self__` of the result, with `none` for `AttributeError`, and `call` is `self.func` as a callable. -/
  | custom (get : Option α → Py (Option (Fn α))) (selfAttr : Py (Option α)) (call : Fn α)

/-- `self.func` with the attribute read by `__isabstractmethod__`, Lib/functools.py:491-493: `none` for
`AttributeError`, so the default; any other exception propagates; the value need not be a bool. -/
structure MTarget (α : Type) where
  kind : MKind α
  abstract : Py (Option α)
  /-- An exception from `hasattr(func, "__get__")` that is not `AttributeError`, and one from `repr(func)`. -/
  getFail : Option PyExc := none
  reprFail : Option PyExc := none

/-- A `partialmethod`. `dict` is absent because `__get__` does not read it. -/
structure PMeth (α : Type) where
  func : MTarget α
  args : List (PArg α)
  keywords : List (String × α)
  phcount : Nat

def MKind.isCallable {α : Type} : MKind α → Bool
  | .classm _ => false
  | .obj f => f.isCallable
  | _ => true

def MKind.hasGet {α : Type} : MKind α → Bool
  | .obj _ => false
  | _ => true

/-- The first argument of `partialmethod(...)`: a `partialmethod`, to flatten, or anything else. -/
inductive MArg (α : Type) where
  | pm (p : PMeth α)
  | target (t : MTarget α)

/-- The `partialmethod` head of `_partial_new`, Lib/functools.py:318-323, 329, 346, 351-357. The `repr` in
the message makes it a wildcard. A `partialmethod` has `__get__`, so the check passes for one. -/
def partialmethodNew {α : Type} (func : MArg α) (args : List (PArg α)) (kw : List (String × PArg α)) :
    Py (PMeth α) :=
  match func with
  | .pm p =>
    match newCore args kw (some (p.args, p.keywords, p.phcount)) with
    | .error e => .error e
    | .ok (t, k, ph) => .ok ⟨p.func, t, k, ph⟩
  | .target t =>
    let body : Py (PMeth α) :=
      match newCore args kw none with
      | .error e => .error e
      | .ok (a, k, ph) => .ok ⟨t, a, k, ph⟩
    if t.kind.isCallable then body
    else
      match t.getFail with
      | some e => .error e
      | none =>
        if t.kind.hasGet then body
        else
          match t.reprFail with
          | some e => .error e
          | none => .error (.typeError "~the first argument must be a callable or a descriptor")

/-- The function `_make_unbound_method` returns, Lib/functools.py:453-470. -/
structure UMethod (α : Type) where
  /-- `_method.__partialmethod__`. -/
  self : PMeth α
  /-- `_method.__isabstractmethod__`, with `none` for the default `False`. -/
  isAbstract : Option α

def makeUnbound {α : Type} (p : PMeth α) : Py (UMethod α) :=
  match p.func.abstract with
  | .error e => .error e
  | .ok a => .ok ⟨p, a⟩

def missingMethodMsg (phcount got : Nat) : String :=
  s!"missing positional arguments in 'partialmethod' call; expected at least {phcount}, got {got}"

/-- `self.func(...)`, for a `self.func` reached directly. -/
def callKind {α : Type} : MKind α → List α → List (String × α) → Py (Called α)
  | .fn id, args, kw => .ok ⟨id, args, kw⟩
  | .classm _, _, _ => .error (.typeError "'classmethod' object is not callable")
  | .staticm id, args, kw => .ok ⟨id, args, kw⟩
  | .obj f, args, kw => callFn f args kw
  | .partialObj f, args, kw => callFn f args kw
  | .custom _ _ c, args, kw => callFn c args kw

/-- `_method`, Lib/functools.py:454-467. `first` is `cls_or_self`. -/
def methodCall {α : Type} (u : UMethod α) (first : α) (args : List α) (kw : List (String × α)) :
    Py (Called α) :=
  let p := u.self
  if p.phcount ≠ 0 then
    match (prepareMerger p.args).2 with
    | none => .error .modelFuel
    | some order =>
      match itemget order (p.args ++ args.map .val) with
      | .error _ => .error (.typeError (missingMethodMsg p.phcount args.length))
      | .ok pto =>
        callKind p.func.kind (first :: valsOf pto ++ args.drop p.phcount) (mergeKw p.keywords kw)
  else callKind p.func.kind (first :: valsOf p.args ++ args) (mergeKw p.keywords kw)

/-- What `partialmethod.__get__` returns. -/
inductive PmGot (α : Type) where
  /-- `partial(new_func, ...)`. -/
  | part (p : Fn α)
  /-- `_method` through the class. -/
  | func (u : UMethod α)
  /-- `_method` bound to the instance. -/
  | bound (u : UMethod α) (obj : α)

/-- `partial(new_func, *self.args, **self.keywords)`: the stored arguments are given again. `new` is
whichever `partial` the module has. -/
abbrev PartialNew (α : Type) := Option Nat → Fn α → List (PArg α) → List (String × PArg α) → Py (Fn α)

/-- `result.__self__ = new_func.__self__`, Lib/functools.py:481-484: an instance attribute of the new
`partial`, so its `__dict__` exists from here on. -/
def setSelf {α : Type} (f : Fn α) (v : α) : Fn α :=
  match f with
  | .pobj o d g a k p => .pobj o (some ((d.getD []) ++ [("__self__", v)])) g a k p
  | f => f

/-- The partial built by `__get__`, :480-484. -/
def pmBound {α : Type} (new : PartialNew α) (p : PMeth α) (newFunc : Fn α) (self : Py (Option α)) :
    Py (PmGot α) :=
  match new none newFunc p.args (p.keywords.map (fun q => (q.1, .val q.2))) with
  | .error e => .error e
  | .ok r =>
    match self with
    | .error e => .error e
    | .ok none => .ok (.part r)
    | .ok (some v) => .ok (.part (setSelf r v))

/-- :485-489: `self._make_unbound_method().__get__(obj, cls)`, a function's `__get__`. -/
def pmUnbound {α : Type} (p : PMeth α) (obj : Option α) : Py (PmGot α) :=
  match makeUnbound p with
  | .error e => .error e
  | .ok u =>
    match obj with
    | none => .ok (.func u)
    | some o => .ok (.bound u o)

/-- `partialmethod.__get__`, Lib/functools.py:472-489. `cls` is the owner, what `classmethod.__get__` binds. -/
def pmGet {α : Type} (new : PartialNew α) (p : PMeth α) (obj : Option α) (cls : α) : Py (PmGot α) :=
  match p.func.kind with
  | .fn id =>
    match obj with
    | none => pmUnbound p obj               -- `function.__get__(None, cls)` is `self.func`
    | some o => pmBound new p (.bound (.base id) o) (.ok (some o))
  | .classm id => pmBound new p (.bound (.base id) cls) (.ok (some cls))
  | .staticm id => pmBound new p (.base id) (.ok none)
  | .obj _ => pmUnbound p obj
  | .partialObj f =>
    match obj with
    | none => pmUnbound p obj
    | some o => pmBound new p (.bound f o) (.ok (some o))
  | .custom get selfAttr _ =>
    match get obj with
    | .error e => .error e
    | .ok none => pmUnbound p obj
    | .ok (some nf) => pmBound new p nf selfAttr

/-- Calling what `__get__` returned. -/
def callGot {α : Type} : PmGot α → List α → List (String × α) → Py (Called α)
  | .part p, args, kw => callFn p args kw
  | .func _, [], _ => .error (.typeError "~_method() missing 1 required positional argument: 'cls_or_self'")
  | .func u, a :: args, kw => methodCall u a args kw
  | .bound u o, args, kw => methodCall u o args kw

/-- An object as `_unwrap_partialmethod` sees it. -/
inductive UObj where
  | leaf (id : Nat)
  | part (f : UObj)
  | pm (f : UObj)
  /-- An object whose `__partialmethod__` is this value. -/
  | method (attr : UObj)
  /-- An object whose `__partialmethod__` read raises this. -/
  | bad (msg : String)
  deriving Repr, DecidableEq

def UObj.isPm : UObj → Bool
  | .pm _ => true
  | _ => false

/-- The inner loop at Lib/functools.py:509-510: `Bool` says whether it moved. The fuel is the size of the
object: each step goes to a strict part. -/
def stripMethods : Nat → UObj → Py (UObj × Bool)
  | 0, _ => .error .modelFuel
  | fuel + 1, f =>
    match f with
    | .bad m => .error (.valueError m)
    | .method a =>
      if a.isPm then
        match stripMethods fuel a with
        | .error e => .error e
        | .ok r => .ok (r.1, true)
      else .ok (f, false)
    | _ => .ok (f, false)

/-- The inner loop at :511-512. -/
def stripPms : Nat → UObj → UObj × Bool
  | 0, f => (f, false)
  | fuel + 1, f =>
    match f with
    | .pm g => ((stripPms fuel g).1, true)
    | _ => (f, false)

/-- `_unwrap_partial` on the same objects, :513. -/
def stripParts : Nat → UObj → UObj × Bool
  | 0, f => (f, false)
  | fuel + 1, f =>
    match f with
    | .part g => ((stripParts fuel g).1, true)
    | _ => (f, false)

def UObj.size : UObj → Nat
  | .leaf _ | .bad _ => 1
  | .part f | .pm f | .method f => f.size + 1

/-- `_unwrap_partialmethod`, Lib/functools.py:505-514: the outer loop ends when a pass moved nothing, which
is `func is prev` because each inner loop goes to a strict part or stays. -/
def unwrapPartialmethod : Nat → UObj → Py UObj
  | 0, _ => .error .modelFuel
  | fuel + 1, f =>
    match stripMethods (f.size + 1) f with
    | .error e => .error e
    | .ok (f1, m1) =>
      let (f2, m2) := stripPms (f1.size + 1) f1
      let (f3, m3) := stripParts (f2.size + 1) f2
      if m1 || m2 || m3 then unwrapPartialmethod fuel f3 else .ok f3

end PyLean.CoreLibs.Functools
