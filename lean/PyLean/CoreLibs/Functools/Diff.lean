import PyLean.DiffCore
import PyLean.CoreLibs.Functools.Wrap

/-! Differential-testing handler for `corelibs` cases with `"fn": "functools.<name>"`.
The dispatcher in `CoreLibs/Diff.lean` strips the `functools.` prefix. Most cases carry
`"twin": "c"` or `"py"`, and the Python side runs the C-accelerated or the pure module. -/

namespace PyLean.CoreLibs.Functools

open Lean PyLean PyLean.Diff

def getArr (j : Json) (key : String) : Except String (List Json) := do
  pure (← (← field j key).getArr?).toList

def getIntList (j : Json) (key : String) : Except String (List Int) := do
  (← getArr j key).mapM (·.getInt?)

def getNatList (j : Json) (key : String) : Except String (List Nat) := do
  (← getArr j key).mapM (·.getNat?)

def getStrList (j : Json) (key : String) : Except String (List String) := do
  (← getArr j key).mapM (·.getStr?)

def okJ (j : Json) : Json := Json.mkObj [("ok", j)]

def intFun (bad : Option Int) (kind : String) : Int → Int → Py Int := fun a b =>
  if some b = bad then .error (.valueError "f")
  else .ok (if kind == "add" then a + b else a - b)

def parseSource (j : Json) : Except String (Source Int) := do
  if ← getBool j "noniter" then pure .notIterable
  else
    let err : Option PyExc := if ← getBool j "itfail" then some (.valueError "it") else none
    pure (.iter (← getIntList j "xs") err)

def parseOp : String → Except String OrdOp
  | "__lt__" => pure .lt
  | "__le__" => pure .le
  | "__gt__" => pure .gt
  | "__ge__" => pure .ge
  | o => throw s!"op {o}"

def parseCmp : String → Except String CmpOp
  | "lt" => pure .lt
  | "le" => pure .le
  | "eq" => pure .eq
  | "ne" => pure .ne
  | "gt" => pure .gt
  | "ge" => pure .ge
  | o => throw s!"cmp {o}"

def parsePArg (j : Json) : Except String (PArg Int) :=
  match j with
  | .str "PH" => pure .ph
  | v => do pure (.val (← v.getInt?))

def parseKw (j : Json) : Except String (List (String × PArg Int)) := do
  let a ← j.getArr?
  a.toList.mapM fun p => do
    pure (← (← p.getArrVal? 0).getStr?, ← parsePArg (← p.getArrVal? 1))

def parseKwV (j : Json) : Except String (List (String × Int)) := do
  let a ← j.getArr?
  a.toList.mapM fun p => do
    pure (← (← p.getArrVal? 0).getStr?, ← (← p.getArrVal? 1).getInt?)

/-- Build the object described by a spec with the twin's constructor, like the Python side. -/
partial def build (c : Bool) (j : Json) : Except String (Py (Fn Int)) := do
  match ← getStr j "kind" with
  | "base" => pure (.ok (.base (← getNat j "id")))
  | "noncallable" => pure (.ok .notCallable)
  | _ =>
    let inner ← build c (← field j "func")
    let args ← (← getArr j "args").mapM parsePArg
    let kw ← parseKw (← field j "kw")
    let override ← match (← field j "override") with
      | .null => pure none
      | v => some <$> v.getNat?
    let hasDict ← getBool j "dict"
    pure (do
      let f ← inner
      let p ← (if c then partialNewC else partialNewPy) override f args kw
      match p with
      | .pobj o _ g a k ph => pure (.pobj o (if hasDict then some [("x", 1)] else none) g a k ph)
      | x => pure x)

def fnJ : Fn Int → Json
  | .base id => toJson id
  | .notCallable => "noncallable"
  | .fails _ => "fails"
  | .bound _ _ => "bound"
  | .pobj o _ _ _ _ _ => Json.mkObj [("partial", toJson o)]

def pargJ : PArg Int → Json
  | .ph => "PH"
  | .val a => toJson a

def kwJ (k : List (String × Int)) : Json := toJson (k.map fun p => toJson [toJson p.1, toJson p.2])

def calledJ (c : Called Int) : Json :=
  toJson [toJson c.id, toJson c.args, kwJ c.kw]

/-- The call of the outermost object goes through the twin's own `__call__`. -/
def callTop (c : Bool) (f : Fn Int) (more : List Int) (kw : List (String × Int)) : Py (Called Int) :=
  match f with
  | .pobj none _ g a k ph =>
    if c then partialVectorcall g a k ph more kw else partialCallPy g a k ph more kw
  | _ => callFn f more kw

def objJ (c : Bool) (f : Fn Int) (more : List Int) (kw : List (String × Int)) : Json :=
  match f with
  | .pobj _ _ g a k _ =>
    Json.mkObj [("func", fnJ g), ("args", toJson (a.map pargJ)), ("kw", kwJ k),
      ("call", encPy calledJ (callTop c f more kw))]
  | _ => "notpartial"

/-- Keys compare by value, so `1 == 1.0`, and a `str` differs from every number: strings are
shifted out of the range the generator uses. -/
def strShift : Int := 1000

def unshift (a : Int) : Int := if a ≥ strShift then a - strShift else a

/-- The key of a call, with the value-equality Python uses: `1 == 1.0` inside a tuple. -/
def keyOf (typed : Bool) (j : Json) : Except String (CacheKey Int) := do
  let args ← (← getArr j "args").mapM fun p => do
    pure ((← (← p.getArrVal? 0).getInt?, ← (← p.getArrVal? 1).getNat?) : Int × Nat)
  let kw ← (← getArr j "kw").mapM fun p => do
    let v ← p.getArrVal? 1
    pure ((← (← p.getArrVal? 0).getStr?,
      (← (← v.getArrVal? 0).getInt?, ← (← v.getArrVal? 1).getNat?)) : String × (Int × Nat))
  let O : MkKeyOps (Int × Nat) := ⟨fun p => p.2 == 0 || p.2 == 2, fun p => p.2⟩
  let shift : Int × Nat → Int := fun a => if a.2 == 2 then a.1 + strShift else a.1
  let norm : KeyItem (Int × Nat) → KeyItem Int := fun i => match i with
    | .val a => .val (shift a)
    | .mark => .mark
    | .name s => .name s
    | .typeOf t => .typeOf t
  pure (match makeKeyC O args kw typed with
    | .scalar a => .scalar (shift a)
    | .tuple l => .tuple (l.map norm))

def infoJ (i : CacheInfo) : Json :=
  toJson [toJson i.hits, toJson i.misses, toJson i.maxsize, toJson i.currsize]

def resJ (rs : List (Py Int)) : Json := toJson (rs.map (encPy toJson))

/-- One step of a user-function script. -/
inductive Step where
  | ret (v : Int)
  | raise
  | call (k : Nat)
  | clear

def parseStep (j : Json) : Except String Step := do
  match ← (← j.getArrVal? 0).getStr? with
  | "ret" => pure (.ret (← (← j.getArrVal? 1).getInt?))
  | "raise" => pure .raise
  | "call" => pure (.call (← (← j.getArrVal? 1).getNat?))
  | "clear" => pure .clear
  | s => throw s!"step {s}"

/-- The script as a program. A failed inner call is caught, so the script goes on. -/
def stepsProg : List Step → Prog Nat Int
  | [] => .ret 0
  | .ret v :: _ => .ret v
  | .raise :: _ => .raise (.valueError "f")
  | .call k :: rest => .call k (fun _ => stepsProg rest)
  | .clear :: rest => .clear (stepsProg rest)

/-- Key `n` has script `a[n]` on an odd miss count and `b[n]` on an even one. -/
def scriptF (a b : List (List Step)) (k m : Nat) : Prog Nat Int :=
  if m % 2 == 1 then stepsProg (a.getD k []) else stepsProg (b.getD k [])

/-- The faults of the colliding keys, which all have one hash. A key marked `hash` is unhashable; a key marked
`get`, `recheck` or `insert` raises from `__eq__` at the first compare of that stage, so only when
the cache holds something; and `insert` is armed only when there is room for one more after it, so that the
`del cache[oldkey]` of a full cache, whose compares depend on the probe order, is not involved. -/
def faultsOf (maxsize : Option Nat) (hashK getK recheckK insertK : List Nat) : Faults Nat where
  get k ks :=
    if hashK.contains k then some (.typeError "~unhashable")
    else if getK.contains k && !ks.isEmpty then some (.valueError "eq")
    else none
  recheck k ks := if recheckK.contains k && !ks.isEmpty then some (.valueError "eq") else none
  evict _ _ := none
  insert k ks :=
    if insertK.contains k && !ks.isEmpty && (maxsize.map (fun m => decide (ks.length + 1 < m))).getD false then
      some (.valueError "eq")
    else none

def lruFuel : Nat := 200

/-- Run a list of operations through one of the wrappers. `clear` is `cache_clear()`. -/
def driveOps {σ : Type} (empty : σ) (call : Nat → σ → Py Int × σ) (st : σ) (ops : List (Option Nat)) :
    List (Py Int) × σ :=
  ops.foldl (fun (acc : List (Py Int) × σ) op =>
    match op with
    | none => (acc.1, empty)
    | some k =>
      let (r, s) := call k acc.2
      (acc.1 ++ [r], s)) ([], st)

def getBad (j : Json) : Except String (List (Nat × Nat)) := do
  (← getArr j "bad").mapM fun p => do
    pure (← (← p.getArrVal? 0).getNat?, ← (← p.getArrVal? 1).getNat?)

def getWorld (j : Json) : Except String World := do
  let tbl (key : String) : Except String (List (List Nat)) := do
    (← getArr j key).mapM fun r => do (← r.getArr?).toList.mapM (·.getNat?)
  let bases ← tbl "bases"
  let mro ← tbl "mro"
  let subs ← tbl "subclasses"
  let isSub ← tbl "issub"
  let abc ← getNatList j "abc"
  let bad ← getBad j
  let pseudoT ← getNatList j "notype"
  let pseudoA ← getNatList j "alias"
  pure ⟨fun c => bases.getD c [], fun c => mro.getD c [],
    fun a b => if bad.contains (a, b) then .error (.valueError "hook")
      else .ok ((isSub.getD a []).contains b),
    fun c => abc.contains c, fun c => subs.getD c [],
    fun c => !pseudoT.contains c, fun c => pseudoA.contains c⟩

def getSeqs (j : Json) (key : String) : Except String (List (List Nat)) := do
  (← getArr j key).mapM fun r => do (← r.getArr?).toList.mapM (·.getNat?)

def worldFuel : Nat := 12

def emptyWorld : World :=
  ⟨fun _ => [], fun _ => [], fun _ _ => .ok false, fun _ => false, fun _ => [], fun _ => true, fun _ => false⟩

def parseTypeVal (j : Json) : Except String TypeVal := do
  match j with
  | .str "fw" => pure .forwardRef
  | .str "other" => pure .other
  | _ =>
    match j.getObjVal? "cls" with
    | .ok c => pure (.cls (← c.getNat?))
    | .error _ =>
      let u ← (← (j.getObjVal? "union")).getArr?
      pure (.union (← u.toList.mapM fun x => match x with
        | .null => pure none
        | v => some <$> v.getNat?))

/-- A table of attribute reads: a value, `null` for `AttributeError`, or `"RAISE"`. -/
def readerOf (tbl : List (String × Json)) (k : String) : Py (Option String) :=
  match tbl.lookup k with
  | none => .ok none
  | some .null => .ok none
  | some (.str "RAISE") => .error (.valueError "read")
  | some (.str s) => .ok (some s)
  | some _ => .ok none

def parseTable (j : Json) (key : String) : Except String (List (String × Json)) := do
  (← getArr j key).mapM fun p => do pure (← (← p.getArrVal? 0).getStr?, ← p.getArrVal? 1)

def parseMKindI (j : Json) : Except String (MKind Int) := do
  let id ← getNat j "id"
  match ← getStr j "kind" with
  | "fn" => pure (.fn id)
  | "classm" => pure (.classm id)
  | "staticm" => pure (.staticm id)
  | "obj" => pure (.obj (.base id))
  | "partial" => pure (.partialObj (.base id))
  | k => throw s!"mkind {k}"

/-- A user descriptor, or one of the plain kinds, with what its `__get__` and `__self__` do. -/
def parseMKind (j : Json) : Except String (MKind Int) := do
  match ← getStr j "kind" with
  | "custom" =>
    let id ← getNat j "id"
    let get : Option Int → Py (Option (Fn Int)) := fun _ => match j.getObjValD "get" with
      | .str "raise" => .error (.valueError "get")
      | .str "self" => .ok none
      | _ => .ok (some (.base (id + 100)))
    let sel : Py (Option Int) := match j.getObjValD "self" with
      | .str "raise" => .error (.valueError "self")
      | .str "attr" => .ok (some 700)
      | _ => .ok none
    pure (.custom get sel (.base id))
  | _ => parseMKindI j

def run (fn : String) (j : Json) : Except String Json := do
  let c := (j.getObjVal? "twin").toOption.bind (·.getStr?.toOption) == some "c"
  let newP : PartialNew Int := if c then partialNewC else partialNewPy
  match fn with
  | "reduce" =>
    let f := intFun (← getOptInt j "bad") (← getStr j "kind")
    let s ← parseSource j
    let i ← getOptInt j "initial"
    pure (encPy toJson ((if c then reduceC else reducePy) f s i))
  | "reduce_wrapper" =>
    let names ← getStrList j "names"
    let warnE ← getBool j "werror"
    let call : Py Int :=
      if names.contains "function" && names.contains "sequence" then .ok 1
      else .error (.typeError "~reduce() missing")
    let warn : Py Unit := if warnE then .error (.named "DeprecationWarning" "~reduce") else .ok ()
    let (r, w) := reduceWarnWrapper names warn call
    pure (okJ (toJson [encPy toJson r, toJson w]))
  | "total_ordering" =>
    let roots ← (← getArr j "roots").mapM (fun x => do parseOp (← x.getStr?))
    let setFail ← match (← field j "setfail") with
      | .null => pure none
      | v => some <$> parseOp (← v.getStr?)
    let C : OrdClass :=
      ⟨fun o => .ok (if o ∈ roots then some 1 else some 0), fun _ => some 0,
        fun o => if some o = setFail then .error (.valueError "set") else .ok ()⟩
    let op ← parseOp (← getStr j "op")
    let res ← getInt j "res"
    let eqv ← getInt j "eq"
    let nev ← getInt j "ne"
    let foreign ← getBool j "foreign"
    let rootBad ← getBool j "rootbad"
    let P : OrdPrims Int Int :=
      ⟨fun _ _ => if rootBad then .error (.valueError "root")
          else if foreign then .ok .notImplemented else .ok (.val res),
        fun _ _ => .ok eqv, fun _ _ => .ok nev,
        fun v => if v == 9 then .error (.valueError "bool") else .ok (v != 0),
        fun b => if b then 101 else 100⟩
    let rJ : Ret Int → Json := fun r => match r with
      | .val a => Json.mkObj [("val", toJson a)]
      | .notImplemented => "NotImplemented"
    match totalOrdering C with
    | .error e => pure (encPy toJson (.error e : Py Int))
    | .ok (root, added) =>
      if op ∈ added then
        match (convert root).lookup op with
        | some s => pure (encPy rJ (derived P s 0 0))
        | none => throw "not added"
      else if op ∈ roots then pure (encPy rJ (P.root 0 0))
      else throw "no such method"
  | "cmp_key" =>
    let bad ← getOptInt j "bad"
    let cmp : Int → Int → Py Int := fun a b =>
      if some a = bad then .error (.valueError "cmp") else .ok (a - b)
    let test : Int → CmpOp → Bool := fun r o => match o with
      | .lt => r < 0
      | .le => r ≤ 0
      | .eq => r == 0
      | .ne => r != 0
      | .gt => r > 0
      | .ge => r ≥ 0
    let kindR ← getStr j "res"
    let ofB : Bool → Int := fun b => if b then 101 else 100
    let K : KeyOps Int Int :=
      ⟨fun r o => match kindR with
        | "boom" => .error (.valueError "cmp0")
        | "obj" => if o == .ne then .ok 7 else .ok (if test r o then 1 else 0)
        | _ => .ok (ofB (test r o)),
       fun v => .ok (v != 0 && v != 100), ofB⟩
    let other : KeyOther Int ← match ← getStr j "otherkind" with
      | "key" => pure (.key (some (← getInt j "other")))
      | "duck" => pure (.duck (← getInt j "other"))
      | _ => pure .plain
    let op ← parseCmp (← getStr j "op")
    pure (encPy toJson ((if c then keyCompareC else keyComparePy) K cmp op (some (← getInt j "x")) other))
  | "key_new" =>
    pure (encPy toJson (keyNew (← getIntList j "pos") (← parseKwV (← field j "kw"))))
  | "partial" =>
    match ← build c (← field j "spec") with
    | .error e => pure (encPy toJson (.error e : Py Int))
    | .ok f => pure (okJ (objJ c f (← getIntList j "more") (← parseKwV (← field j "morekw"))))
  | "partial_reduce" =>
    match ← build c (← field j "spec") with
    | .error e => pure (encPy toJson (.error e : Py Int))
    | .ok f =>
      let r := if c then unpickleWith partialNewC setstateC pReduceC f
        else unpickleWith partialNewPy setstatePy pReducePy f
      let more ← getIntList j "more"
      pure (encPy (fun g => objJ c g more []) r)
  | "descr_get" =>
    match ← build c (← field j "spec") with
    | .error e => pure (encPy toJson (.error e : Py Int))
    | .ok f =>
      let obj ← getOptInt j "obj"
      pure (encPy calledJ (callFn (descrGet f obj) (← getIntList j "more") []))
  | "setstate" =>
    let st ← field j "state"
    let parsed : PState Int ← match ← getStr st "shape" with
      | "nottuple" => pure .notTuple
      | "size" => pure (.size (← getNat st "n"))
      | _ =>
        let func : Fn Int := if ← getBool st "callable" then .base 1 else .notCallable
        let raw ← (← getArr st "raw").mapM parsePArg
        let args : StArgs Int ← match ← getStr st "argkind" with
          | "tuple" => pure (.tuple raw)
          | "sub" =>
            if ← getBool st "iterbad" then pure (.sub raw (.error (.valueError "iter")))
            else pure (.sub raw (.ok (← (← getArr st "iter").mapM parsePArg)))
          | _ => pure .other
        let kwv ← parseKwV (← field st "kwitems")
        let kw : StKw Int ← match ← getStr st "kw" with
          | "none" => pure .none
          | "dict" => pure (.exact kwv)
          | "sub" => pure (.sub kwv none)
          | "subbad" => pure (.sub kwv (some (.valueError "conv")))
          | _ => pure .other
        let ns : StNs Int ← match ← getStr st "ns" with
          | "none" => pure .none
          | "dict" => pure (.dict (← parseKwV (← field st "nsitems")))
          | _ => pure .other
        pure (.four func args kw ns)
    let r := (if c then setstateC else setstatePy) none parsed
    let reduced : Fn Int → Json := fun f =>
      match (if c then pReduceC f else pReducePy f) with
      | .four _ (.tuple a) k n =>
        toJson [toJson (a.map pargJ),
          (match k with
           | .exact d => kwJ d
           | _ => Json.null),
          (match n with
           | .dict d => kwJ d
           | _ => Json.null)]
      | _ => Json.null
    let more ← getIntList j "more"
    let callIt ← getBool j "call"
    pure (encPy (fun f => toJson [reduced f,
      if callIt then encPy calledJ (callTop c f more []) else Json.null]) r)
  | "partial_repr" =>
    let kw ← parseKwV (← field j "kw")
    let args ← (← getArr j "args").mapM parsePArg
    let E : ReprEnv Int := ⟨fun v =>
      if v == -1 then .error (.valueError "arg")
      else if v == -2 then reprGuard true (.ok "x")
      else .ok (toString v)⟩
    let func : Py String := if ← getBool j "funcbad" then .error (.valueError "func") else .ok "F"
    let cls := "functools.partial"
    pure (encPy toJson (reprGuard false ((if c then partialReprC else partialReprPy) E cls func args kw)))
  | "placeholder" =>
    let s : PhState := {}
    let (a, s1) := placeholderNewPy s
    let (b, _) := placeholderNewPy s1
    let name ← getStr j "name"
    let n ← getNat j "nargs"
    let e := if c then placeholderSubclassC else placeholderSubclassPy name
    let newR : Py Nat := if c then (placeholderNewC n s1).map Prod.fst
      else if n ≠ 0 then .error (.typeError "~takes 1 positional argument") else .ok a
    pure (okJ (toJson [toJson (a == b), toJson placeholderRepr, toJson placeholderReduce,
      encPy (fun _ => Json.null) (.error e : Py Nat), encPy (fun x => toJson (x == a)) newR]))
  | "pm_get" =>
    let ab : Py (Option Int) ← match ← getStr j "abstract" with
      | "raise" => pure (.error (.valueError "abs"))
      | "true" => pure (.ok (some 1))
      | _ => pure (.ok none)
    let pargs ← (← getArr j "args").mapM parsePArg
    let pkw ← parseKwV (← field j "kw")
    let t : MTarget Int := ⟨← parseMKind j, ab⟩
    let nest ← (← getArr j "nest").mapM parsePArg
    let obj := if ← getBool j "instance" then some (501 : Int) else none
    let more ← getIntList j "more"
    let morekw ← parseKwV (← field j "morekw")
    let r : Py (Called Int) := do
      let p0 ← partialmethodNew (.target t) pargs (pkw.map fun q => (q.1, .val q.2))
      let p ← if nest.isEmpty then pure p0 else partialmethodNew (.pm p0) nest []
      let got ← pmGet newP p obj 502
      callGot got more morekw
    pure (encPy calledJ r)
  | "pm_new" =>
    let t : MTarget Int := ⟨.obj .notCallable, .ok none⟩
    let args ← (← getArr j "args").mapM parsePArg
    pure (encPy (fun _ => Json.null) (partialmethodNew (.target t) args []))
  | "unwrap" =>
    let rec parseU : Nat → Json → Except String UObj
      | 0, _ => throw "too deep"
      | n + 1, u => do
        match ← getStr u "k" with
        | "leaf" => pure (.leaf (← getNat u "id"))
        | "bad" => pure (.bad "read")
        | "part" => pure (.part (← parseU n (← field u "f")))
        | "pm" => pure (.pm (← parseU n (← field u "f")))
        | _ => pure (.method (← parseU n (← field u "f")))
    let u ← parseU 30 (← field j "obj")
    let rJ : UObj → Json := fun r => match r with
      | .leaf i => toJson i
      | _ => "method"
    pure (encPy rJ (unwrapPartialmethod (u.size + 1) u))
  | "make_key" =>
    let key ← keyOf (← getBool j "typed") j
    pure (okJ (match key with
      | .scalar a => toJson (unshift a)
      | .tuple _ => "tuple"))
  | "lru" =>
    let tbl (k : String) : Except String (List (List Step)) := do
      (← getArr j k).mapM fun r => do (← r.getArr?).toList.mapM parseStep
    let a ← tbl "scripta"
    let b ← tbl "scriptb"
    let f := scriptF a b
    let ops : List (Option Nat) ← (← getArr j "ops").mapM fun o => match o with
      | .str "clear" => pure none
      | v => some <$> v.getNat?
    let keys (k : String) := getNatList j k
    match (← field j "maxsize") with
    | .null =>
      let F := faultsOf none (← keys "hash") (← keys "getk") [] []
      let (rs, s) := driveOps emptyC (callInf f F lruFuel) emptyC ops
      pure (okJ (toJson [resJ rs, toJson [toJson s.hits, toJson s.misses, Json.null,
        toJson s.cache.length]]))
    | m =>
      let m ← m.getNat?
      if m == 0 then
        let (rs, s) := driveOps 0 (callNone f lruFuel) 0 ops
        pure (okJ (toJson [resJ rs, toJson [toJson (0 : Nat), toJson s, toJson (0 : Nat),
          toJson (0 : Nat)]]))
      else
        let F := faultsOf (some m) (← keys "hash") (← keys "getk") (← keys "recheckk") (← keys "insertk")
        let cfg : Cfg Nat Int := ⟨m, f, F⟩
        if c then
          let (rs, s) := driveOps emptyC (callC cfg lruFuel) emptyC ops
          pure (okJ (toJson [resJ rs, infoJ (infoC m s)]))
        else
          let (rs, s) := driveOps emptyPy (callPy cfg lruFuel) emptyPy ops
          pure (okJ (toJson [resJ rs, infoJ (infoPy m s)]))
  | "lru_dec" =>
    let arg ← match ← getStr j "kind" with
      | "int" => pure (MaxsizeArg.int (← getInt j "n"))
      | "none" => pure .none
      | "callable" => pure (.callable (← getBool j "typedbool"))
      | _ => pure .other
    let user ← getBool j "callable"
    let typedB ← getBool j "typedbool"
    let typed := if (← getStr j "kind") == "callable" then false else typedB
    let fail : Option PyExc := if ← getBool j "fail" then some (.valueError "read") else none
    let mode : Option Int → Py LruMode := if c then wrapperCMode user else wrapperPyMode
    let r := if ← getBool j "viacache" then cacheDecorate mode fail else lruDecorate mode arg typed fail
    pure (encPy (fun (x : LruRec) => toJson [
      (match x.mode with
       | .uncached => Json.str "uncached"
       | .infinite => "infinite"
       | .bounded n => toJson n), toJson x.maxsize, toJson x.typed]) r)
  | "c3_merge" =>
    let seqs ← getSeqs j "seqs"
    pure (encPy toJson (c3Merge ((seqs.map List.length).sum + 2) seqs))
  | "c3_mro" =>
    pure (encPy toJson (c3Mro (← getWorld j) worldFuel (← getNat j "cls") (← getNatList j "abcs")))
  | "compose_mro" =>
    pure (encPy toJson (composeMro (← getWorld j) worldFuel (← getNat j "cls")
      (← getNatList j "types")))
  | "find_impl" =>
    let reg := (← getNatList j "types").map fun t => (t, t + 1000)
    pure (encPy toJson (findImpl (← getWorld j) worldFuel (← getNat j "cls") reg))
  | "dispatch" =>
    let worlds ← (← getArr j "worlds").mapM getWorld
    let ops ← getArr j "ops"
    let mut d : Dispatcher Nat := newDispatcher 0 1000
    let mut out : List Json := []
    for o in ops do
      let w := worlds.getD (← getNat o "w") emptyWorld
      let tok ← getNat o "token"
      match ← getStr o "op" with
      | "reg" => d := regStore w tok d (.cls (← getNat o "c")) (← getNat o "impl")
      | "regu" => d := regStore w tok d (.union (← getNatList o "cs")) (← getNat o "impl")
      | _ =>
        let (r, d') := dispatch w worldFuel tok d (← getNat o "c")
        d := d'
        out := out ++ [encPy toJson r]
    pure (okJ (toJson out))
  | "register" =>
    let first ← field j "first"
    let func : Option Nat := if ← getBool j "withfunc" then some 7 else none
    let arg : RegFirst Nat ← match ← getStr first "k" with
      | "val" => pure (.val (← parseTypeVal (← field first "v")))
      | "func" =>
        match (← field first "hints") with
        | .null => pure (.func 7 none)
        | h =>
          let items ← h.getArr?
          let parsed ← items.toList.mapM fun p => do
            pure (← (← p.getArrVal? 0).getStr?, ← parseTypeVal (← p.getArrVal? 1))
          pure (.func 7 (some (.ok parsed)))
      | k => throw s!"register {k}"
    let d : Dispatcher Nat := newDispatcher 0 1000
    let keysJ : Dispatcher Nat → Json := fun x => toJson ((x.registry.map Prod.fst).mergeSort)
    pure (encPy (fun (p : Registered Nat × Dispatcher Nat) => toJson [
      (match p.1 with
       | .func _ => Json.str "func"
       | .decorator _ => "decorator"), keysJ p.2]) (register emptyWorld 0 d arg func))
  | "sd_noarg" =>
    let nameR : Py (Option String) := readerOf (← parseTable j "tbl") "__name__"
    match singledispatch 0 (1000 : Nat) nameR with
    | .error e => pure (encPy toJson (.error e : Py Int))
    | .ok d => pure (encPy toJson (dispatchCall emptyWorld worldFuel 0 d none).1)
  | "update_wrapper" =>
    let wr ← field j "wrapper"
    let wd ← field j "wrapped"
    let setF := (wr.getObjVal? "setfail").toOption.bind (·.getStr?.toOption)
    let w0 : Wrapper Int :=
      { dict := ← parseKwV (← field wr "dict"), hasDict := ← getBool wr "hasdict",
        setFail := fun k => if some k = setF then some (.valueError "set") else none }
    let attrs ← parseKwV (← field wd "attrs")
    let badA := (wd.getObjVal? "bad").toOption.bind (·.getStr?.toOption)
    let dictD : Py (Option (Attrs Int)) ← match ← getStr wd "dictkind" with
      | "bad" => pure (.error (.valueError "dict"))
      | "none" => pure (.ok none)
      | _ => pure (.ok (some (← parseKwV (← field wd "dict"))))
    let wrapped : Wrapped Int :=
      ⟨fun k => if some k = badA then .error (.valueError "read") else .ok (attrs.lookup k),
        fun _ => dictD⟩
    let assigned ← getStrList j "assigned"
    let updated ← getStrList j "updated"
    let sortJ : Attrs Int → Json := fun l =>
      toJson ((l.mergeSort (fun a b => decide (a.1 ≤ b.1))).map fun p => toJson [toJson p.1, toJson p.2])
    let viaWraps ← getBool j "viawraps"
    let r : Py (Wrapper Int) :=
      if viaWraps then
        match wraps wrapped (7 : Int) assigned updated with
        | .error e => .error e
        | .ok p => wrapsCall p w0
      else updateWrapper w0 wrapped 7 assigned updated
    pure (encPy (fun x => toJson [sortJ x.dict, sortJ x.slots]) r)
  | "cached_get" =>
    let name := (← field j "name").getStr?.toOption
    let dkind ← getStr j "dict"
    let d ← parseKwV (← field j "items")
    let inst : Option (InstDict Int) := match dkind with
      | "class" => none
      | "none" => some .none
      | "frozen" => some (.dict d true)
      | _ => some (.dict d false)
    let mode ← getStr j "func"
    let func : Attrs Int → Py (Int × Attrs Int) := fun x => match mode with
      | "raise" => .error (.valueError "f")
      | "mutate" => .ok (5, setAttr (setAttr x "extra" 3) (name.getD "p") 9)
      | _ => .ok (5, x)
    let cJ : CachedOut Int → Json := fun o => match o with
      | .self => "self"
      | .val v x => toJson [toJson v,
          toJson ((x.mergeSort (fun a b => decide (a.1 ≤ b.1))).map fun p => toJson [toJson p.1, toJson p.2])]
    pure (encPy cJ (cachedGet ⟨func, name, 0, 0⟩ inst))
  | "cached_init" =>
    let tbl ← parseTable j "tbl"
    let read : String → Py (Option Int) := fun k => (readerOf tbl k).map (·.map (fun _ => 1))
    pure (encPy (fun (x : CachedProp Int) => toJson x.attrname) (cachedNew (fun d => .ok (0, d)) read))
  | "set_name" =>
    let a := (← field j "attr").getStr?.toOption
    pure (encPy toJson (setName a (← getStr j "name")))
  | "sdm" =>
    let tbl ← parseTable j "tbl"
    let read := readerOf tbl
    let impl ← parseMKindI j
    let f : SdmFunc Int := ⟨← getBool j "callable", ← getBool j "hasget", read, fun _ => .ok none,
      if (← getBool j "absbad") then .error (.valueError "read") else .ok none, impl⟩
    let objR ← getOptInt j "obj"
    let world : World := ⟨fun c => if c == 0 then [] else [0], fun c => if c == 0 then [0] else [c, 0],
      fun a b => .ok (a == b || b == 0), fun _ => false, fun _ => [], fun _ => true, fun _ => false⟩
    let more ← getIntList j "more"
    let what ← getStr j "what"
    let reprO : Int → Py String := fun v =>
      if v == -1 then .error (.valueError "objrepr") else .ok (toString v)
    let nameA ← getStr j "name"
    let doReg ← getBool j "register"
    let r : Py Json := do
      let s ← sdmNew 0 f
      match what with
      | "repr" => pure (toJson (← sdmRepr s))
      | "abstract" => pure (toJson ((← sdmIsAbstract s).isSome))
      | _ =>
        let g ← sdmGet s objR 502
        match what with
        | "getrepr" => pure (toJson (← sdmGetRepr g reprO))
        | "getattr" => pure (toJson (← sdmGetattr g nameA))
        | "wrapped" => pure (toJson (decide ((sdmWrapped g).impl.isCallable = impl.isCallable)))
        | _ =>
          let s' ← if doReg then
              (sdmGetRegister world 0 g (.val (.cls 1)) (some impl)).map Prod.snd
            else pure s
          let g' := { g with unbound := s' }
          let (r, _) := sdmCall world worldFuel 0 g' (fun _ => 1) more []
          pure (calledJ (← r))
    pure (encPy id r)
  | "key_sig" => pure (okJ (toJson keyTextSignature))
  | "lru_misc" => pure (okJ (toJson [lruReduce (← getStr j "q")]))
  | _ => throw s!"unknown fn functools.{fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.CoreLibs.Functools
