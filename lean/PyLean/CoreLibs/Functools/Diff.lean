import PyLean.DiffCore
import PyLean.CoreLibs.Functools.Model

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

def okJ (j : Json) : Json := Json.mkObj [("ok", j)]

def retJ {α : Type} (e : α → Json) : Ret α → Json
  | .val a => Json.mkObj [("val", e a)]
  | .notImplemented => "NotImplemented"

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
      | .pobj o _ g a k ph => pure (.pobj o hasDict g a k ph)
      | x => pure x)

def fnJ : Fn Int → Json
  | .base id => toJson id
  | .notCallable => "noncallable"
  | .pobj o _ _ _ _ _ => Json.mkObj [("partial", toJson o)]

def pargJ : PArg Int → Json
  | .ph => "PH"
  | .val a => toJson a

def calledJ (c : Called Int) : Json :=
  toJson [toJson c.id, toJson c.args, toJson (c.kw.map fun p => toJson [toJson p.1, toJson p.2])]

def objJ (f : Fn Int) (more : List Int) (kw : List (String × Int)) : Json :=
  match f with
  | .pobj _ _ g a k _ =>
    Json.mkObj [("func", fnJ g), ("args", toJson (a.map pargJ)),
      ("kw", toJson (k.map fun p => toJson [toJson p.1, toJson p.2])),
      ("call", encPy calledJ (callFn f more kw))]
  | _ => "notpartial"

/-- Keys compare by value, so `1 == 1.0`, and a `str` differs from every number: strings are
shifted out of the range the generator uses. -/
def strShift : Int := 1000

def unshift (a : Int) : Int := if a ≥ strShift then a - strShift else a

def valOfItems (l : List (KeyItem Int)) : Int :=
  l.foldl (fun acc i => match i with
    | .val a => acc + unshift a
    | _ => acc) 0

def lruF (bad : Option Int) (k : CacheKey Int) : Py Int :=
  let v := match k with
    | .scalar a => unshift a
    | .tuple l => valOfItems l
  if some v = bad then .error (.valueError "f") else .ok v

/-- The key of a call, with the value-equality Python uses: `1 == 1.0` inside a tuple. -/
def keyOf (typed : Bool) (j : Json) : Except String (CacheKey Int) := do
  let args ← (← getArr j "args").mapM fun p => do
    pure ((← (← p.getArrVal? 0).getInt?, ← (← p.getArrVal? 1).getNat?) : Int × Nat)
  let kw ← (← getArr j "kw").mapM fun p => do
    let v ← p.getArrVal? 1
    pure ((← (← p.getArrVal? 0).getStr?,
      (← (← v.getArrVal? 0).getInt?, ← (← v.getArrVal? 1).getNat?)) : String × (Int × Nat))
  let O : KeyOps (Int × Nat) := ⟨fun p => p.2 == 0 || p.2 == 2, fun p => p.2⟩
  let shift : Int × Nat → Int := fun a => if a.2 == 2 then a.1 + strShift else a.1
  let norm : KeyItem (Int × Nat) → KeyItem Int := fun i => match i with
    | .val a => .val (shift a)
    | .mark => .mark
    | .name s => .name s
    | .typeOf t => .typeOf t
  pure (match makeKeyC O args kw typed with
    | .scalar a => .scalar (shift a)
    | .tuple l => .tuple (l.map norm))

def parseOps (typed : Bool) (j : Json) : Except String (List (LruOp (CacheKey Int))) := do
  (← getArr j "ops").mapM fun o =>
    match o with
    | .str "clear" => pure .clear
    | _ => do pure (.call (← keyOf typed o))

def infoJ (i : CacheInfo) : Json :=
  toJson [toJson i.hits, toJson i.misses, toJson i.maxsize, toJson i.currsize]

def resJ (rs : List (Py Int)) : Json := toJson (rs.map (encPy toJson))

/-- Unbounded and uncached wrappers under the same operation list. -/
def runInfinite (f : CacheKey Int → Py Int) :
    CLru (CacheKey Int) Int → List (LruOp (CacheKey Int)) → List (Py Int) × CLru (CacheKey Int) Int
  | s, [] => ([], s)
  | _, .clear :: ops => runInfinite f emptyC ops
  | s, .call k :: ops =>
    let (r, s') := stepInfinite f s k
    let (rs, t) := runInfinite f s' ops
    (r :: rs, t)

def runUncached (f : CacheKey Int → Py Int) : Nat → List (LruOp (CacheKey Int)) → List (Py Int) × Nat
  | m, [] => ([], m)
  | _, .clear :: ops => runUncached f 0 ops
  | m, .call k :: ops =>
    let (r, m') := stepUncached f m k
    let (rs, t) := runUncached f m' ops
    (r :: rs, t)

def getWorld (j : Json) : Except String World := do
  let n ← getNat j "n"
  let tbl (key : String) : Except String (List (List Nat)) := do
    (← getArr j key).mapM fun r => do (← r.getArr?).toList.mapM (·.getNat?)
  let bases ← tbl "bases"
  let mro ← tbl "mro"
  let subs ← tbl "subclasses"
  let isSub ← tbl "issub"
  let abc ← getNatList j "abc"
  let _ := n
  pure ⟨fun c => bases.getD c [], fun c => mro.getD c [],
    fun a b => (isSub.getD a []).contains b, fun c => abc.contains c,
    fun c => subs.getD c []⟩

def getSeqs (j : Json) (key : String) : Except String (List (List Nat)) := do
  (← getArr j key).mapM fun r => do (← r.getArr?).toList.mapM (·.getNat?)

def worldFuel : Nat := 12

def run (fn : String) (j : Json) : Except String Json := do
  let c := (j.getObjVal? "twin").toOption.bind (·.getStr?.toOption) == some "c"
  match fn with
  | "reduce" =>
    let f := intFun (← getOptInt j "bad") (← getStr j "kind")
    let s ← parseSource j
    let i ← getOptInt j "initial"
    pure (encPy toJson ((if c then reduceC else reducePy) f s i))
  | "total_ordering" =>
    let roots ← (← getArr j "roots").mapM (fun x => do parseOp (← x.getStr?))
    match totalOrdering roots with
    | .error e => pure (encPy toJson (.error e : Py Int))
    | .ok (root, added) =>
      let op ← parseOp (← getStr j "op")
      let a ← getInt j "a"
      let b ← getInt j "b"
      let foreign ← getBool j "foreign"
      let test : OrdOp → Int → Int → Bool := fun o x y => match o with
        | .lt => x < y
        | .le => x ≤ y
        | .gt => x > y
        | .ge => x ≥ y
      if op ∈ roots then
        pure (okJ (retJ toJson (if foreign then .notImplemented else .val (test op a b))))
      else
        let P : OrdPrims Int := ⟨fun x y => .ok (if foreign then .notImplemented else
          .val (test root x y)), fun x y => .ok (x == y), fun x y => .ok (x != y)⟩
        match added.lookup op with
        | some s => pure (encPy (retJ toJson) (derived P s a b))
        | none => throw "not added"
  | "cmp_key" =>
    let bad ← getOptInt j "bad"
    let cmp : Int → Int → Py Int := fun a b =>
      if some a = bad then .error (.valueError "cmp") else .ok (a - b)
    let other ← getOptInt j "other"
    let op ← parseCmp (← getStr j "op")
    pure (encPy toJson ((if c then keyCompareC else keyComparePy) cmp op (← getInt j "x") other))
  | "partial" =>
    match ← build c (← field j "spec") with
    | .error e => pure (encPy toJson (.error e : Py Int))
    | .ok f => pure (okJ (objJ f (← getIntList j "more") (← parseKwV (← field j "morekw"))))
  | "setstate" =>
    let args ← (← getArr j "args").mapM parsePArg
    let st : PState Int := ⟨← getBool j "isTuple", ← getNat j "size", ← getBool j "callable",
      ← getBool j "argsTuple", args, ← getBool j "kwNone", ← getBool j "kwDict",
      ← getBool j "nsNone", ← getBool j "nsDict"⟩
    pure (encPy toJson ((if c then setstateC else setstatePy) st))
  | "partial_repr" =>
    let kw ← (← getArr j "kw").mapM fun p => do
      pure (← (← p.getArrVal? 0).getStr?, ← (← p.getArrVal? 1).getStr?)
    let args ← (← getArr j "args").mapM (·.getStr?)
    pure (okJ (toJson (partialRepr (← getStr j "cls") (← getStr j "func") args kw)))
  | "make_key" =>
    let key ← keyOf (← getBool j "typed") j
    pure (okJ (match key with
      | .scalar a => toJson (unshift a)
      | .tuple _ => "tuple"))
  | "lru" =>
    let typed ← getBool j "typed"
    let ops ← parseOps typed j
    let f := lruF (← getOptInt j "bad")
    match (← field j "maxsize") with
    | .null =>
      let (rs, s) := runInfinite f emptyC ops
      pure (okJ (toJson [resJ rs, toJson [toJson s.hits, toJson s.misses, Json.null,
        toJson s.links.length]]))
    | m =>
      let m ← m.getNat?
      if m == 0 then
        let (rs, s) := runUncached f 0 ops
        pure (okJ (toJson [resJ rs, toJson [toJson (0 : Nat), toJson s, toJson (0 : Nat),
          toJson (0 : Nat)]]))
      else if c then
        let (rs, s) := runC m f emptyC ops
        pure (okJ (toJson [resJ rs, infoJ (infoC m s)]))
      else
        let (rs, s) := runPy m f emptyPy ops
        pure (okJ (toJson [resJ rs, infoJ (infoPy m s)]))
  | "lru_mode" =>
    let arg ← match ← getStr j "kind" with
      | "int" => pure (MaxsizeArg.int (← getInt j "n"))
      | "none" => pure .none
      | "callable" => pure (.callable (← getBool j "typedbool"))
      | _ => pure .other
    let r : Py LruMode := do
      let v ← lruCacheArg arg
      if c then wrapperCMode v else wrapperPyMode v
    pure (encPy (fun m => match m with
      | .uncached => "uncached"
      | .infinite => "infinite"
      | .bounded n => toJson n) r)
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
      let w := worlds.getD (← getNat o "w") ⟨fun _ => [], fun _ => [], fun _ _ => false,
        fun _ => false, fun _ => []⟩
      let tok ← getNat o "token"
      match ← getStr o "op" with
      | "reg" => d := register w tok d (.cls (← getNat o "c")) (← getNat o "impl")
      | "regu" => d := register w tok d (.union (← getNatList o "cs")) (← getNat o "impl")
      | _ =>
        let (r, d') := dispatch w worldFuel tok d (← getNat o "c")
        d := d'
        out := out ++ [encPy toJson r]
    pure (okJ (toJson out))
  | "update_wrapper" =>
    let parse (k : String) : Except String (Attrs Int) := do
      (← getArr j k).mapM fun p => do
        pure (← (← p.getArrVal? 0).getStr?, ← (← p.getArrVal? 1).getInt?)
    let assigned ← (← getArr j "assigned").mapM (·.getStr?)
    let (w, d) := updateWrapper (← parse "wrapper") (← parse "wrapped") (← parse "wrapperd")
      (← parse "wrappedd") assigned 7
    let sortJ : Attrs Int → Json := fun l =>
      toJson ((l.mergeSort (fun a b => decide (a.1 ≤ b.1))).map fun p => toJson [toJson p.1, toJson p.2])
    pure (okJ (toJson [sortJ w, sortJ d]))
  | "cached_get" =>
    let name := (← field j "name").getStr?.toOption
    let dict ← match (← field j "dict") with
      | .null => pure none
      | v => some <$> ((← v.getArr?).toList.mapM fun p => do
          pure (← (← p.getArrVal? 0).getStr?, ← (← p.getArrVal? 1).getInt?))
    let func : Py Int := if ← getBool j "fail" then .error (.valueError "f") else .ok 5
    pure (encPy (fun (p : Int × Attrs Int) =>
      toJson [toJson p.1, toJson (p.2.map fun q => toJson [toJson q.1, toJson q.2])])
      (cachedGet func name dict (← getBool j "frozen")))
  | "set_name" =>
    let a := (← field j "attr").getStr?.toOption
    pure (encPy toJson (setName a (← getStr j "name")))
  | "sdm_repr" =>
    let q := (← field j "q").getStr?.toOption
    let n := (← field j "n").getStr?.toOption
    let o := (← field j "o").getStr?.toOption
    pure (okJ (toJson [sdmRepr q n, sdmGetRepr q n o]))
  | _ => throw s!"unknown fn functools.{fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.CoreLibs.Functools
