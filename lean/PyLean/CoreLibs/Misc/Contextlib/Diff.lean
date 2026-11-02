import PyLean.CoreLibs.Misc.Common
import PyLean.CoreLibs.Misc.Contextlib.Model

/-!
`misc.ctx` cases. The concrete generator is a script of steps, run by `GS`; it follows CPython's
generator protocol (`gen_send_ex2`, `gen_throw`, `gen_close` in Objects/genobject.c): PEP 479
conversion, `close` ignoring `GeneratorExit` and `StopIteration`. Exit callbacks are scripts too.
Exceptions are compared by class, first argument, cause and context, to depth 3, and objects with a
role in the case by their label.
-/

namespace PyLean.CoreLibs.Misc.Contextlib

open Lean PyLean PyLean.Diff PyLean.CoreLibs.Misc

def clsOf : String → Cls
  | "ValueError" => ["ValueError", "Exception", "BaseException"]
  | "KeyError" => ["KeyError", "LookupError", "Exception", "BaseException"]
  | "LookupError" => ["LookupError", "Exception", "BaseException"]
  | "RuntimeError" => clsRuntime
  | "MiscRt" => ["MiscRt", "RuntimeError", "Exception", "BaseException"]
  | "StopIteration" => clsStop
  | "StopAsyncIteration" => clsStopAsync
  | "GeneratorExit" => clsGenExit
  | "KeyboardInterrupt" => ["KeyboardInterrupt", "BaseException"]
  | "BadInit" => ["BadInit", "Exception", "BaseException"]
  | "ExceptionGroup" => clsEG
  | "BaseExceptionGroup" => clsBEG
  | "MiscEG" => ["MiscEG", "ExceptionGroup", "BaseExceptionGroup", "Exception", "BaseException"]
  | n => [n, "Exception", "BaseException"]

/-- `typ()`: class `BadInit` raises in `__init__`. -/
def instantiate {σ : Type} : Instantiate σ := fun s t =>
  match t with
  | "BadInit" :: _ =>
    let (s, e) := s.raiseNew (clsOf "ValueError") "init failed"
    (s, .error e)
  | _ =>
    let (h, e) := s.h.alloc { cls := t }
    ({ s with h := h }, .ok e)

/-- A generator body: what happens after each resumption. -/
inductive GStep where
  | yld (v : Int)
  | ret
  | raiseNew (c : String)
  | reraise
  deriving Repr, DecidableEq

structure GS where
  script : List GStep
  started : Bool
  finished : Bool
  /-- `sys.exception()` at the caller. -/
  handled : Option ExcId
  isAsync : Bool
  /-- `ag_closed` -/
  agClosed : Bool := false
  deriving Repr

/-- The mark for a traceback that a resumption extended. -/
def dirtyTb : Nat := 999999

def stopOf (a : Bool) : Cls := if a then clsStopAsync else clsStop

def finish (s : St GS) : St GS := { s with g := { s.g with finished := true } }

/-- The exception leaving a generator frame, after PEP 479 (`gen_send_ex2`). -/
def leaving (s : St GS) (e : ExcId) : St GS × ExcId :=
  let a := s.g.isAsync
  let pre := if a then "async generator raised " else "generator raised "
  let conv (n : String) : St GS × ExcId :=
    let (h, r) := s.h.alloc
      { cls := clsRuntime, msg := pre ++ n, context := some e, cause := some e }
    ({ s with h := h }, r)
  if s.h.isInst e "StopIteration" then conv "StopIteration"
  else if a && s.h.isInst e "StopAsyncIteration" then conv "StopAsyncIteration"
  else (s, e)

/-- Run the body from its resumption point. -/
def resume (s : St GS) (thrown handled : Option ExcId) : St GS × Res Int :=
  let ended (s : St GS) : St GS × Res Int :=
    let (h, e) := s.h.alloc { cls := stopOf s.g.isAsync }
    (finish { s with h := h }, .error e)
  match s.g.script with
  | [] => ended s
  | step :: rest =>
    let s := { s with g := { s.g with script := rest, started := true } }
    match step with
    | .yld v => (s, .ok v)
    | .ret => ended s
    | .raiseNew c =>
      let (s, e) := s.raiseNew (clsOf c) "gen" handled
      let (s, r) := leaving s e
      (finish s, .error r)
    | .reraise =>
      match thrown with
      | some t =>
        let s := { s with h := s.h.raiseCtx t handled }
        let (s, r) := leaving s t
        (finish s, .error r)
      | none =>
        let (s, e) := s.raiseNew clsRuntime "nothing" handled
        (finish s, .error e)

def gsNext (s : St GS) : St GS × Res Int :=
  if s.g.finished then
    let (h, e) := s.h.alloc { cls := stopOf s.g.isAsync }
    ({ s with h := h }, .error e)
  else
    let s' := { s with g := { s.g with started := true } }
    resume s' none s.g.handled

/-- `gen.throw`, and `agen.athrow`, `async_gen_athrow_send`: on a finished frame the awaitable just
ends, so `await agen.athrow(v)` returns `None`; on a closed one it raises `StopAsyncIteration`. -/
def gsThrow (s : St GS) (v : ExcId) : St GS × Res Int :=
  if s.g.finished && s.g.isAsync then (s, .ok 0)
  else if s.g.agClosed && s.g.isAsync then
    let (h, e) := s.h.alloc { cls := clsStopAsync }
    ({ s with h := h }, .error e)
  else
  let s := { s with h := s.h.setTb v (some dirtyTb) }
  if s.g.finished then (s, .error v)
  else if !s.g.started then
    -- The frame has not entered the body, so the PEP 479 handler does not cover it. A
    -- `StopIteration` leaving `athrow`'s `send` ends the await.
    let s := finish { s with h := s.h.raiseCtx v s.g.handled }
    if s.g.isAsync && s.h.isInst v "StopIteration" then (s, .ok 0)
    else if s.g.isAsync && (s.h.isInst v "StopAsyncIteration" || s.h.isInst v "GeneratorExit") then
      ({ s with g := { s.g with agClosed := true } }, .error v)
    else (s, .error v)
  else
    match resume s (some v) s.g.handled with
    | (s, .error e) =>
      if s.g.isAsync && (s.h.isInst e "StopAsyncIteration" || s.h.isInst e "GeneratorExit") then
        ({ s with g := { s.g with agClosed := true } }, .error e)
      else (s, .error e)
    | r => r

def gsClose (s : St GS) (handled : Option ExcId) : St GS × Res Unit :=
  if s.g.isAsync && s.g.agClosed && !s.g.finished then
    let (s, e) := s.raiseNew clsStopAsync "" handled
    (s, .error e)
  else
  let s := { s with g := { s.g with agClosed := s.g.isAsync } }
  if s.g.finished then (s, .ok ())
  else if !s.g.started then (finish s, .ok ())
  else
    let (h, ge) := s.h.alloc { cls := clsGenExit }
    let s := { s with h := h.raiseCtx ge handled }
    match resume s (some ge) handled with
    | (s, .ok _) =>
      let pre := if s.g.isAsync then "async generator" else "generator"
      let (s, e) := s.raiseNew clsRuntime (pre ++ " ignored GeneratorExit") handled
      (s, .error e)
    | (s, .error e) =>
      if s.h.isInst e (if s.g.isAsync then "StopAsyncIteration" else "StopIteration") ||
          s.h.isInst e "GeneratorExit" then (s, .ok ())
      else (s, .error e)

def gsOps : GenOps GS Int :=
  { next := gsNext, throw := gsThrow, close := gsClose, handled := fun s => s.g.handled }

def withHandled (s : St GS) (e : Option ExcId) : St GS := { s with g := { s.g with handled := e } }

def parseStep (j : Json) : Except String GStep := do
  match ← jStrAt j 0 with
  | "y" => return .yld (← jIntAt j 1)
  | "ret" => return .ret
  | "raise" => return .raiseNew (← jStrAt j 1)
  | "reraise" => return .reraise
  | o => throw s!"bad step {o}"

/-- Exception description; `labels` gives objects with a role in the case. -/
def desc (labels : List (ExcId × String)) (h : Heap) : Nat → Option ExcId → Json
  | _, none => Json.null
  | 0, some _ => jStr "..."
  | d + 1, some e =>
    match labels.lookup e with
    | some l => jStr l
    | none =>
      let o := h.get e
      Json.arr #[jStr (o.cls.headD ""), jStr o.msg, desc labels h d o.cause, desc labels h d o.context]

def encRes {α : Type} (labels : List (ExcId × String)) (h : Heap) (enc : α → Json) : Res α → Json
  | .ok v => Json.arr #["ok", enc v]
  | .error e => Json.arr #["exc", desc labels h 3 (some e)]

def cfgOf (a : Bool) : Cfg := if a then asyncCfg else syncCfg
def nameOf (a : Bool) : String :=
  if a then "_AsyncGeneratorContextManager" else "_GeneratorContextManager"

def enterOf (a : Bool) (self : GCM) (s : St GS) : GCM × St GS × Res Int :=
  if a then agcmEnter gsOps self s else gcmEnter syncCfg gsOps (nameOf false) self s

def exitOf (a : Bool) (s : St GS) (typ : Option Cls) (value : Option ExcId) (tb : Option Nat) :
    St GS × Res Bool :=
  if a then agcmExit gsOps instantiate s typ value tb
  else gcmExit syncCfg gsOps instantiate s typ value tb

def gcmCM (a : Bool) (self : GCM) : CM GS Int where
  enter := fun s =>
    let (_, s, r) := enterOf a self s
    (s, r)
  exit := fun s e =>
    let s := withHandled s e
    let (s, r) := match e with
      | none => exitOf a s none none none
      | some v => exitOf a s (some (s.h.get v).cls) (some v) (s.h.get v).tb
    (withHandled s none, r)

def initGS (script : List GStep) (a : Bool) : St GS :=
  { h := [], g := { script, started := false, finished := false, handled := none, isAsync := a } }

def runGcm (j : Json) : Except String Json := do
  let a ← getBool j "async"
  let script ← (← jArr (← field j "script")).mapM parseStep
  let mut s := initGS script a
  let mut self := contextmanager
  let mut out : Array Json := #[]
  let mut labels : List (ExcId × String) := []
  let mut vals : List (ExcId × Option Nat) := []
  for op in (← jArr (← field j "ops")) do
    match ← jStrAt op 0 with
    | "enter" =>
      let (g, s', r) := enterOf a self s
      self := g
      s := s'
      out := out.push (encRes labels s.h jInt r)
    | "exit_none" =>
      let (s', r) := exitOf a s none none none
      s := s'
      out := out.push (encRes labels s.h jBool r)
    | "exit_inst" =>
      let c := clsOf (← jStrAt op 1)
      let tb : Option Nat := if (← jBoolAt op 2) then some 7 else none
      let (h, v) := s.h.alloc { cls := c, msg := "body" }
      s := { s with h := h }
      labels := labels ++ [(v, "value")]
      vals := vals ++ [(v, tb)]
      let (s', r) := exitOf a s (some c) (some v) tb
      s := s'
      out := out.push (encRes labels s.h jBool r)
      out := out.push (jBool ((s.h.get v).tb == tb))
    | "exit_type" =>
      let (s', r) := exitOf a s (some (clsOf (← jStrAt op 1))) none none
      s := s'
      out := out.push (encRes labels s.h jBool r)
    | o => throw s!"bad op {o}"
  return Json.mkObj [("ok", Json.arr (out.push (jBool s.g.finished)))]

/-- `with cm: body`. `body = none` runs to the end; `some c` raises a new `c("body")`. -/
def bodyOf (b : Option String) (_ : Int) (s : St GS) : St GS × Res Int :=
  match b with
  | none => (s, .ok 1)
  | some c =>
    let (s, e) := s.raiseNew (clsOf c) "body"
    (s, .error e)

def jBody (j : Json) : Except String (Option String) :=
  match j with
  | .null => .ok none
  | v => some <$> v.getStr?

def runWith (j : Json) : Except String Json := do
  let a ← getBool j "async"
  let script ← (← jArr (← field j "script")).mapM parseStep
  let body ← jBody (← field j "body")
  let (s, r) := withStmt (gcmCM a contextmanager) (bodyOf body) (initGS script a)
  let (s, r) := if a then coBoundary s r else (s, r)
  return Json.mkObj [("ok", Json.arr #[encRes [] s.h (jOpt jInt) r, jBool s.g.finished])]

/-- Two calls of a function decorated with a generator context manager. `recreate` makes a new
generator from `func` each time. -/
def runDeco (j : Json) : Except String Json := do
  let a ← getBool j "async"
  let script ← (← jArr (← field j "script")).mapM parseStep
  let body ← jBody (← field j "body")
  let call (s : St GS) : St GS × Res (Option Int) :=
    let s := { s with g := (initGS script a).g }
    ContextDecorator.call
      (gcmRecreate (nameOf a) contextmanager (fun s => (s, .ok ()))) (gcmCM a)
      (fun s =>
        let (s, r) := bodyOf body 0 s
        if a then coBoundary s r else (s, r)) s
  let (s, r1) := call (initGS script a)
  let j1 := encRes [] s.h (jOpt jInt) r1
  let (s, r2) := call s
  return Json.mkObj [("ok", Json.arr #[j1, encRes [] s.h (jOpt jInt) r2])]

/-! ### `suppress` -/

partial def buildTree (j : Json) (h : Heap) : Except String (Heap × ExcId) := do
  match ← jStrAt j 0 with
  | "leaf" =>
    let (h, e) := h.alloc { cls := clsOf (← jStrAt j 1), msg := "leaf" }
    return (h, e)
  | "group" =>
    let cls := clsOf (← jStrAt j 1)
    let mut hp := h
    let mut ids : List ExcId := []
    for c in (← jArr (← jGetI j 2)) do
      let (h', e) ← buildTree c hp
      hp := h'
      ids := ids ++ [e]
    let cls := if cls == clsBEG then deriveCls hp ids else cls
    let (h'', e) := hp.alloc { cls, msg := "g", children := some ids }
    return (h'', e)
  | o => throw s!"bad tree {o}"

partial def treeJson (h : Heap) (orig : List (ExcId × String)) (e : ExcId) : Json :=
  match orig.lookup e with
  | some l => jStr l
  | none =>
    let o := h.get e
    match o.children with
    | none => Json.arr #[jStr (o.cls.headD ""), jStr o.msg]
    | some cs =>
      Json.arr #[jStr (o.cls.headD ""), jStr o.msg, Json.arr (cs.map (treeJson h orig)).toArray]

def runSuppress (j : Json) : Except String Json := do
  let cs ← (← jArr (← field j "classes")).mapM (fun x => x.getStr?)
  let cs := cs.flatMap (fun c => [c])
  let (h, e) ← buildTree (← field j "tree") []
  let leafLabels : List (ExcId × String) := [(e, "orig")]
  let s : St Unit := { h, g := () }
  let handled : Option ExcId := if (← getBool j "with") then some e else none
  let (s, r) := suppressExit cs s handled (some e)
  match r with
  | .ok v => return Json.mkObj [("ok", Json.arr #["ok", jOpt jBool v])]
  | .error x =>
    let ctx := (s.h.get x).context
    return Json.mkObj [("ok", Json.arr #["exc", treeJson s.h leafLabels x,
      jOpt (fun c => treeJson s.h leafLabels c) ctx, jBool (x == e)])]

/-! ### `ExitStack` and `AsyncExitStack` -/

inductive Beh where
  | ret (b : Bool)
  | raiseNew (c : String)
  | reraise
  | pushCb (b : Beh) (id : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- The world of a stack case. -/
structure SW where
  log : List Json
  frame : Option ExcId
  labels : List (ExcId × String)

abbrev XF := Nat × Beh

def behRun (bh : Beh) (x : Xs SW XF XF Unit) (d : Option ExcId) :
    Xs SW XF XF Unit × Res Bool :=
  match bh with
  | .ret b => (x, .ok b)
  | .raiseNew c =>
    let (s, e) := x.1.raiseNew (clsOf c) "cb" x.1.g.frame
    ((s, x.2), .error e)
  | .reraise =>
    match d with
    | some e => (({ x.1 with h := x.1.h.raiseCtx e x.1.g.frame }, x.2), .error e)
    | none =>
      let (s, e) := x.1.raiseNew clsRuntime "nothing" x.1.g.frame
      ((s, x.2), .error e)
  | .pushCb b i => ((x.1, (true, .raw (i, b)) :: x.2), .ok false)

def stackLog (x : Xs SW XF XF Unit) (i : Nat) (d : Option ExcId) (tag : String) : Xs SW XF XF Unit :=
  let w := x.1.g
  let e := desc w.labels x.1.h 1 d
  ({ x.1 with g := { w with log := w.log ++ [Json.arr #[toJson i, jStr tag, e]] } }, x.2)

/-- An `async def` callback's frame converts `StopIteration`. -/
def behBoundary (tag : String) (r : Xs SW XF XF Unit × Res Bool) : Xs SW XF XF Unit × Res Bool :=
  if tag == "a" then
    let (s, res) := coBoundary r.1.1 r.2
    ((s, r.1.2), res)
  else r

def mkCalls (tag : String) : Calls SW XF XF Unit where
  raw := fun f x d => behBoundary tag (behRun f.2 (stackLog x f.1 d tag) d)
  bound := fun m _ x d => behBoundary tag (behRun m.2 (stackLog x m.1 d tag) d)
  wrapped := fun f _ x =>
    match behBoundary tag (behRun f.2 (stackLog x f.1 none tag) none) with
    | (x, .error e) => (x, .error e)
    | (x, .ok _) => (x, .ok ())

def parseBeh : Nat → Json → Except String Beh
  | 0, _ => .error "too deep"
  | d + 1, j => do
    match ← jStrAt j 0 with
    | "ret" => return .ret (← jBoolAt j 1)
    | "raise" => return .raiseNew (← jStrAt j 1)
    | "reraise" => return .reraise
    | "pushcb" => return .pushCb (← parseBeh d (← jGetI j 1)) (← jNatAt j 2)
    | o => throw s!"bad beh {o}"

def fixFuel (h : Heap) : Nat := h.length + 1

def runStack (j : Json) : Except String Json := do
  let a ← getBool j "async"
  let mut x : Xs SW XF XF Unit := ({ h := [], g := { log := [], frame := none, labels := [] } }, [])
  let mut out : Array Json := #[]
  for op in (← jArr (← field j "ops")) do
    let beh (i : Nat) : Except String XF := do
      return (← jNatAt op 1, ← parseBeh 4 (← jGetI op i))
    match ← jStrAt op 0 with
    | "push_fn" =>
      let f ← beh 2
      let ret : Stack XF XF Unit := if ← jBoolAt op 3
        then (pushAsyncExit (fun _ => none) id x.2 f).1
        else (push (fun _ => none) id x.2 f).1
      x := (x.1, ret)
      out := out.push (toJson f.1)
    | "push_cm" =>
      let f ← beh 2
      let look : ExitLookup XF XF Unit := fun o => some (.get (.ok (.bound o o)))
      let ret : Stack XF XF Unit := if ← jBoolAt op 3
        then (pushAsyncExit look id x.2 f).1
        else (push look id x.2 f).1
      x := (x.1, ret)
      out := out.push (toJson f.1)
    | "push_static" =>
      let f ← beh 2
      let kind ← jStrAt op 4
      let look : ExitLookup XF XF Unit := fun o =>
        some (match kind with
          | "class" => .isClass (.raw o)
          | "noget" => .noGet (.raw o)
          | _ => .get (.ok (.raw o)))
      let ret : Stack XF XF Unit := if ← jBoolAt op 3
        then (pushAsyncExit look id x.2 f).1
        else (push look id x.2 f).1
      x := (x.1, ret)
      out := out.push (toJson f.1)
    | "push_descfail" =>
      let (s, e) := x.1.raiseNew (clsOf "ValueError") "descr"
      let isAsync ← jBoolAt op 1
      let look : ExitLookup XF XF Unit := fun _ => some (.get (.error e))
      let (st, r) := if isAsync then pushAsyncExit look id x.2 (0, .ret false) else push look id x.2 (0, .ret false)
      x := (s, st)
      out := out.push (encRes x.1.g.labels x.1.h (fun _ => Json.null) r)
    | "callback" =>
      let f ← beh 2
      x := (x.1, if ← jBoolAt op 3 then pushAsyncCallback x.2 f () else callback x.2 f ())
      out := out.push (toJson f.1)
    | "enter_ctx" =>
      let f ← beh 2
      let en : Int ← jIntAt op 3
      let en2 ← jBoolAt op 4
      let isAsync ← jBoolAt op 5
      let m : XF → Option (Descr (Xs SW XF XF Unit → Xs SW XF XF Unit × Res Int)) := fun _ =>
        some (.get (.ok (fun x =>
          if en2 then
            let (s, e) := x.1.raiseNew (clsOf "ValueError") "enter"
            ((s, x.2), .error e)
          else (x, .ok en))))
      let (x', r) := enterContext m (fun o => some (.get (.ok (.bound o o)))) "" (!isAsync) x f
      x := x'
      out := out.push (encRes x.1.g.labels x.1.h jInt r)
    | "enter_bad" =>
      let isAsync ← jBoolAt op 1
      let kind ← jStrAt op 2
      let tail := if isAsync then "asynchronous context manager protocol" else "context manager protocol"
      let msg := s!"'__main__.{if kind == "noexit" then "MiscNoExit" else "MiscNoCM"}' object does not support the {tail}"
      let body : Xs SW XF XF Unit → Xs SW XF XF Unit × Res Int := fun x => (x, .ok 0)
      let (x', r) ← match kind with
        | "none" => pure (enterContext (fun _ => none) (fun _ => none) msg true x ((0, .ret false) : XF))
        | "noexit" => pure (enterContext (fun _ => some (.noGet body)) (fun _ => none) msg true x ((0, .ret false) : XF))
        | "enterfail" =>
          let (s, e) := x.1.raiseNew (clsOf "ValueError") "descr"
          let y : Xs SW XF XF Unit := (s, x.2)
          pure (enterContext (fun _ => some (.get (.error e))) (fun _ => none) msg true y ((0, .ret false) : XF))
        | _ =>
          let (s, e) := x.1.raiseNew (clsOf "ValueError") "descr"
          let y : Xs SW XF XF Unit := (s, x.2)
          pure (enterContext (fun _ => some (.noGet body)) (fun _ => some (.get (.error e))) msg true y ((0, .ret false) : XF))
      x := x'
      out := out.push (encRes x.1.g.labels x.1.h jInt r)
    | "pop_all" =>
      let (new, kept) := popAll x.2
      out := out.push (toJson kept.length)
      x := (x.1, new)
    | "exit" =>
      let excSpec ← jGetI op 1
      let frame ← jBoolAt op 2
      let mut exc : Option ExcId := none
      match excSpec with
      | .null => pure ()
      | v =>
        let cn ← v.getStr?
        let (h, e) := x.1.h.alloc { cls := clsOf cn, msg := "body" }
        exc := some e
        x := ({ x.1 with h := h, g := { x.1.g with labels := x.1.g.labels ++ [(e, "value")] } }, x.2)
      let f : Option ExcId := if frame then exc else none
      x := ({ x.1 with g := { x.1.g with frame := f } }, x.2)
      let c := mkCalls "s"
      let ac := mkCalls "a"
      let r : Py (Xs SW XF XF Unit × Res Bool) :=
        if a then aexit c ac 64 (fixFuel x.1.h + 40) x exc f
        else exit c 64 (fixFuel x.1.h + 40) x exc f
      match r with
      | .error e => throw s!"model error {e.className}"
      | .ok (x', res) =>
        x := ({ x'.1 with g := { x'.1.g with frame := none } }, x'.2)
        out := out.push (encRes x.1.g.labels x.1.h jBool res)
    | "close" =>
      let c := mkCalls "s"
      let ac := mkCalls "a"
      let r : Py (Xs SW XF XF Unit × Res Bool) :=
        if a then aexit c ac 64 (fixFuel x.1.h + 40) x none none
        else exit c 64 (fixFuel x.1.h + 40) x none none
      match r with
      | .error e => throw s!"model error {e.className}"
      | .ok (x', res) =>
        x := x'
        let res' : Res Unit := match res with
          | .ok _ => .ok ()
          | .error e => .error e
        out := out.push (encRes x.1.g.labels x.1.h jUnit res')
    | o => throw s!"bad op {o}"
  return Json.mkObj [("ok", Json.arr #[Json.arr out, Json.arr x.1.g.log.toArray, toJson x.2.length])]

/-! ### Small context managers -/

instance : Inhabited (Redirect Int) := ⟨Redirect.init 0⟩
instance : Inhabited (Chdir String) := ⟨Chdir.init ""⟩

def runRedirect (j : Json) : Except String Json := do
  let mut rs : Array (Redirect Int) := #[Redirect.init 1, Redirect.init 2]
  let mut cur : Int := 0
  let mut out : Array Json := #[]
  for op in (← jArr (← field j "ops")) do
    let i ← jNatAt op 1
    let r := rs[i]!
    match ← jStrAt op 0 with
    | "enter" =>
      let (r', c, v) := r.enter cur
      rs := rs.set! i r'
      cur := c
      out := out.push (jInt v)
    | "exit" =>
      match r.exit with
      | none => out := out.push (Json.arr #["exc", "IndexError", jStr popEmpty])
      | some (r', c) =>
        rs := rs.set! i r'
        cur := c
        out := out.push (jInt c)
    | o => throw s!"bad op {o}"
    out := out.push (Json.arr #[jInt cur, jList jInt rs[0]!.oldTargets, jList jInt rs[1]!.oldTargets])
  return Json.mkObj [("ok", Json.arr out)]

def fsChdir (p _cwd : String) : Except String String :=
  if p == "/nonexistent" then .error s!"[Errno 2] No such file or directory: '{p}'"
  else if p == "." then .ok _cwd
  else .ok p

def runChdir (j : Json) : Except String Json := do
  let paths ← (← jArr (← field j "paths")).mapM (fun x => x.getStr?)
  let mut cs : Array (Chdir String) := (paths.map Chdir.init).toArray
  let mut cur : String := "/"
  let mut out : Array Json := #[]
  for op in (← jArr (← field j "ops")) do
    let i ← jNatAt op 1
    let c := cs[i]!
    match ← jStrAt op 0 with
    | "enter" =>
      let (c', cwd, r) := c.enter fsChdir cur
      cs := cs.set! i c'
      cur := cwd
      out := out.push (match r with
        | .ok () => Json.arr #["ok", Json.null]
        | .error m => Json.arr #["exc", "FileNotFoundError", jStr m])
    | "exit" =>
      match c.exit fsChdir cur with
      | none => out := out.push (Json.arr #["exc", "IndexError", jStr popEmpty])
      | some (c', cwd, r) =>
        cs := cs.set! i c'
        cur := cwd
        out := out.push (match r with
          | .ok () => Json.arr #["ok", Json.null]
          | .error m => Json.arr #["exc", "FileNotFoundError", jStr m])
    | o => throw s!"bad op {o}"
    out := out.push (jStr cur)
  return Json.mkObj [("ok", Json.arr out)]

def runHook (j : Json) : Except String Json := do
  let parseD (d : Json) : Except String (List (String × Bool)) := do
    (← jArr d).mapM (fun kv => do return ((← jStrAt kv 0), (← jBoolAt kv 1)))
  let mro : MroDicts ← (← jArr (← field j "mro")).mapM parseD
  let a ← getBool j "async"
  let exact ← getBool j "exact"
  let ms := if a then ["__aenter__", "__aexit__"] else ["__enter__", "__exit__"]
  return Json.mkObj [("ok", jOpt jBool (subclasshook exact ms mro))]

def runClosing (j : Json) : Except String Json := do
  let failClose ← getBool j "fail"
  let body ← jBody (← field j "body")
  let closeF (handled : Option ExcId) (s : St Nat) : St Nat × Res Unit :=
    let s := { s with g := s.g + 1 }
    if failClose then
      let (s, e) := s.raiseNew (clsOf "ValueError") "close" handled
      (s, .error e)
    else (s, .ok ())
  let cm : CM Nat Int :=
    { enter := fun s => (s, .ok (closingEnter (5 : Int)))
      exit := fun s e => closingExit (closeF e) s }
  let bodyF (_ : Int) (s : St Nat) : St Nat × Res Int :=
    match body with
    | none => (s, .ok 1)
    | some c =>
      let (s, e) := s.raiseNew (clsOf c) "body"
      (s, .error e)
  let (s, r) := withStmt cm bodyF { h := [], g := 0 }
  return Json.mkObj [("ok", Json.arr #[encRes [] s.h (jOpt jInt) r, toJson s.g])]

def runNull (j : Json) : Except String Json := do
  let v ← getInt j "v"
  let body ← jBody (← field j "body")
  let cm : CM Unit Int :=
    { enter := fun s => (s, .ok (nullEnter v))
      exit := fun s e => (s, .ok (nullExit e)) }
  let bodyF (x : Int) (s : St Unit) : St Unit × Res Int :=
    match body with
    | none => (s, .ok x)
    | some c =>
      let (s, e) := s.raiseNew (clsOf c) "body"
      (s, .error e)
  let (s, r) := withStmt cm bodyF { h := [], g := () }
  return Json.mkObj [("ok", encRes [] s.h (jOpt jInt) r)]

def runCase (j : Json) : Except String Json := do
  match ← getStr j "k" with
  | "gcm" => runGcm j
  | "with" => runWith j
  | "deco" => runDeco j
  | "suppress" => runSuppress j
  | "stack" => runStack j
  | "redirect" => runRedirect j
  | "chdir" => runChdir j
  | "hook" => runHook j
  | "closing" => runClosing j
  | "null" => runNull j
  | k => throw s!"bad kind {k}"

end PyLean.CoreLibs.Misc.Contextlib
