import PyLean.Bytecode.GenObj.AsyncGen

/-!
# A scripted frame evaluator for the differential test

`difftest/bytecode_gen_diff.py` turns each script below into a real Python
generator, coroutine or async generator. This file interprets the same script as
an instance of `Hooks`, so that the state machine in `Model.lean` and
`AsyncGen.lean` can be compared with CPython. Nothing here is proved about; it is
the `resume` argument for the difftest and the one place the `Hooks` knot is tied:
`hooksAt n` re-enters the model with `hooksAt (n - 1)`, so a body can call
`next(self)`.

The `yield from` loop mirrors `_SEND` (`Python/bytecodes.c:1676-1720`) and
`CLEANUP_THROW` (`:1960-1978`); `await` adds `_PyEval_GetAwaitable`
(`Python/ceval.c:3646-3667`).
-/

namespace PyLean.Bytecode.GenObj.Script

/-- The opaque objects of a script. -/
inductive SV where
  | int (i : Int)
  /-- A foreign iterator instance. -/
  | foreign (id : Nat)
  /-- An object with `__await__`, wrapping foreign iterator `id`. -/
  | awaitable (id : Nat) (spec : Nat)
  /-- A bound method of a foreign iterator. -/
  | meth (id : Nat) (name : String)
  /-- An object known only by its type name. -/
  | junk (tp : String)
  deriving Inhabited

abbrev O := Obj SV

/-- A foreign iterator: yields `100, 101, ...`, then raises `StopIteration(retv)`.
`throwB`: 0 no attribute, 1 reraise, 2 return 200, 3 `StopIteration(300)`, 4
`RuntimeError("t")`, 5 attribute raises `ValueError("attr")`, 6 attribute raises
`AttributeError`, 7 the lookup runs `reent` and then raises `AttributeError`. `closeB`: 0
no attribute, 1 fine, 2 `ValueError("c")`, 3 `StopIteration(301)`, 4 attribute raises
`ValueError("attr")`, 5 attribute raises `AttributeError`, 6 as `throwB` 7. `reent` runs in
`throw`/`close`, on the top object. -/
structure FSpec where
  items : Nat := 0
  retv : Option Int := none
  hasSend : Bool := true
  throwB : Nat := 1
  closeB : Nat := 1
  reent : Option Nat := none
  deriving Inhabited

/-- What a reentrant call does. -/
inductive ReOp where
  | next | send (v : Int) | close | throw (cls : String) | flags
  | anext | asend (v : Int) | aclose | athrow (cls : String)
  | heldSend (i : Nat) | heldThrow (i : Nat) (cls : String) | heldClose (i : Nat)
  deriving Inhabited

mutual
  inductive Act where
    /-- `x = yield v; log(x)` -/
    | yld (v : Int)
    /-- `x = yield from sub` or `x = await sub`; `log(x)` -/
    | yldFrom (s : Sub)
    | ret (v : Option Int)
    | raise (cls : String)
    | tryExc (body : List Act) (cls : String) (handler : List Act)
    | tryFin (body fin : List Act)
    | loop (n : Nat) (body : List Act)
    /-- A reentrant call on the top object (`self := false`) or on this frame's
    own object, with exceptions logged. -/
    | reent (op : ReOp) (self : Bool)
  inductive Sub where
    | script (body : List Act)
    /-- A `types.coroutine` generator (`CO_ITERABLE_COROUTINE`), for `await`. -/
    | iterCoro (body : List Act)
    | foreign (spec : FSpec)
    /-- `await` of an awaitable that misbehaves: 0 `int`, 1 `__await__` returns a
    coroutine, 2 `__await__` returns an int, 3 `__await__` raises, 4 no `__await__`. Kinds 1-3
    are instances of the nested class `Outer.BadAw`, kind 4 of `Outer.NoAw`. -/
    | badAwait (k : Nat)
end

instance : Inhabited Act := ⟨.ret none⟩

/-- `except cls:` for the classes the scripts use. -/
def classMatches (excCls handler : String) : Bool :=
  excCls == handler ||
    (handler == "BaseException") ||
    (handler == "Exception" && !(excCls == "GeneratorExit" || excCls == "MyGE" || excCls == "BaseException")) ||
    (handler == "GeneratorExit" && excCls == "MyGE") ||
    (handler == "StopIteration" && excCls == "MySI") ||
    (handler == "StopAsyncIteration" && excCls == "MySAI") ||
    (handler == "LookupError" && excCls == "KeyError")

def kindOfClass (cls : String) : ExcKind :=
  if cls == "StopIteration" || cls == "MySI" then .stopIteration
  else if cls == "StopAsyncIteration" || cls == "MySAI" then .stopAsyncIteration
  else if cls == "GeneratorExit" || cls == "MyGE" then .generatorExit
  else .plain

def renderInt (i : Int) : String := toString i

def renderObj : O → String
  | .none => "None"
  | .gen _ => "<gen>"
  | .wrapped _ => "<wrapped>"
  | .str s => s
  | .traceback => "<tb>"
  | .excClass _ c => c
  | .excInst _ c _ _ => c
  | .other (.int i) => renderInt i
  | .other (.foreign _) => "<foreign>"
  | .other (.awaitable _ _) => "<awaitable>"
  | .other (.meth _ _) => "<meth>"
  | .other (.junk t) => t

/-- `str(e)`. -/
def excStr (e : Exc SV) : String :=
  if e.kind == .stopIteration && e.msg == "" then
    match e.value with
    | .none => ""
    | v => renderObj v
  else if e.cls == "KeyError" && e.msg != "" then "'" ++ e.msg ++ "'"
  else e.msg

def mkExc (cls msg : String) (value : O := .none) : Exc SV :=
  ⟨kindOfClass cls, cls, msg, value⟩

/-- `raise cls("m")`; a `StopIteration`'s value is its argument. -/
def raised (cls : String) (msg : String := "m") : Exc SV :=
  mkExc cls msg (if kindOfClass cls == .stopIteration then .str msg else .none)

def Exc' := Exc SV

inductive Mode where
  | run
  | unwind (e : Exc SV)
  | returning (v : O)
  | send (recv : O) (v : O)

inductive K where
  | seq (rest : List Act)
  | tryE (cls : String) (handler : List Act)
  | tryF (fin : List Act)
  | handler
  | afterFin (m : Mode)
  | loop (n : Nat) (body : List Act)
  /-- Suspended at a `yield`. -/
  | recv
  /-- Suspended in a `yield from` on this receiver. -/
  | sending (recv : O)

instance : Inhabited K := ⟨.handler⟩

structure FState where
  spec : FSpec := {}
  next : Nat := 0
  deriving Inhabited

structure Ext where
  frames : Ref → List K := fun _ => []
  foreign : Nat → FState := fun _ => default
  /-- Newest first. -/
  trace : List String := []
  nextGen : Ref := 1
  nextForeign : Nat := 0
  nextAw : Nat := 0
  /-- The top object. -/
  top : Ref := 0
  /-- `(is asend, ref)` of awaitables held by the driver, oldest first. -/
  held : List (Bool × Ref) := []
  /-- The context the top object runs in. -/
  warnErr : Bool := false
  firstiterB : Nat := 0
  finalizerB : Nat := 0

abbrev W := World SV Ext
abbrev H := Hooks SV Ext

def log (w : W) (s : String) : W := { w with ext.trace := s :: w.ext.trace }

def setFrame (w : W) (r : Ref) (k : List K) : W :=
  { w with ext.frames := fun q => if q = r then k else w.ext.frames q }

def setForeign (w : W) (id : Nat) (f : FState) : W :=
  { w with ext.foreign := fun q => if q = id then f else w.ext.foreign q }

def retRender : Ret SV → String
  | .ok v => "ok:" ++ renderObj v
  | .err none => "null"
  | .err (some e) => "exc:" ++ e.cls ++ ":" ++ excStr e

def depth1 : List K → Bool
  | [] => true
  | .tryE .. :: _ | .tryF .. :: _ | .handler :: _ => false
  | .afterFin (.unwind _) :: _ => false
  | _ :: k => depth1 k

def codeFor (kind : GenKind) : Code :=
  { name := "f", qualname := "f"
    flags := match kind with
      | .gen => CO_GENERATOR | .coro => CO_COROUTINE | .asyncGen => CO_ASYNC_GENERATOR }

/-- Allocate a generator object for a script. -/
def allocGen (w : W) (kind : GenKind) (body : List Act) : W × Ref :=
  let r := w.ext.nextGen
  let g : GenObj SV := genNewWithQualname kind (codeFor kind) none none
  let w1 := setFrame (w.set r g) r [.seq body]
  ({ w1 with ext.nextGen := r + 1 }, r)

def allocForeign (w : W) (spec : FSpec) : W × Nat :=
  let id := w.ext.nextForeign
  let w1 := setForeign w id { spec := spec }
  ({ w1 with ext.nextForeign := id + 1 }, id)

def foreignNext (w : W) (id : Nat) : W × Ret SV :=
  let f := w.ext.foreign id
  if f.next < f.spec.items then
    let w1 := setForeign w id { f with next := f.next + 1 }
    (w1, .ok (.other (.int (100 + f.next))))
  else
    let v : O := match f.spec.retv with
      | some i => .other (.int i)
      | none => .none
    (w, .err (some (setStopIterationValue v)))

def attrError (name : String) : Exc SV :=
  mkExc "AttributeError" ("'It' object has no attribute '" ++ name ++ "'")

/-- The `(typ, val)` a foreign `throw` raises for behaviour 1. -/
def reraise (h : H) (typ : O) (val : Option O) : Exc SV :=
  match typ with
  | .excClass .. => h.normalize typ val
  | .excInst k c m v => ⟨k, c, m, v⟩
  | _ => mkExc "RuntimeError" "bad typ"

/-- The three-argument `genThrowF` shape of `gen.throw(cls)`. -/
def throwArgs (cls : String) : List O := [.excClass (kindOfClass cls) cls]

def allocAw (w : W) : W × Nat :=
  let a := w.ext.nextAw
  ({ w with ext.nextAw := a + 1 }, a)

def foreignSpecReent : Nat → ReOp
  | 0 => .next
  | 1 => .send 1
  | 2 => .close
  | 3 => .throw "ValueError"
  | 5 => .anext
  | 6 => .aclose
  | 7 => .athrow "ValueError"
  | _ => .flags

/-- A reentrant call, as `rop` in the difftest driver does it. -/
def doReOp (h : H) (n : Nat) (w : W) (r : Ref) (op : ReOp) : W × Ret SV :=
  let cStatus (res : W × CStatus SV) (k : W → W × Ret SV) : W × Ret SV :=
    match res with
    | (w1, .fail e) => (w1, .err e)
    | (w1, .ok) => k w1
  match op with
  | .next => nextCall h w r
  | .send v => genSend h w r (some (.other (.int v)))
  | .close => genCloseF h n w r
  | .throw cls => genThrow h n w r (throwArgs cls)
  | .flags => (w, .ok .none)
  | .anext =>
    let (w0, a) := allocAw w
    cStatus (asyncGenAnext h w0 r a) (fun w1 => asyncGenAsendSend h w1 a (some .none))
  | .asend v =>
    let (w0, a) := allocAw w
    cStatus (asyncGenAsend h w0 r a (.other (.int v)))
      (fun w1 => asyncGenAsendSend h w1 a (some .none))
  | .aclose =>
    let (w0, a) := allocAw w
    cStatus (asyncGenAclose h w0 r a) (fun w1 => asyncGenAthrowSend h n w1 a .none)
  | .athrow cls =>
    let (w0, a) := allocAw w
    cStatus (asyncGenAthrow h w0 r a (throwArgs cls)) (fun w1 => asyncGenAthrowSend h n w1 a .none)
  | .heldSend i =>
    match w.ext.held[i]? with
    | some (true, a) => asyncGenAsendSend h w a (some .none)
    | some (false, a) => asyncGenAthrowSend h n w a .none
    | none => (w, .ok .none)
  | .heldThrow i cls =>
    match w.ext.held[i]? with
    | some (true, a) => asyncGenAsendThrow h n w a (throwArgs cls)
    | some (false, a) => asyncGenAthrowThrow h n w a (throwArgs cls)
    | none => (w, .ok .none)
  | .heldClose i =>
    match w.ext.held[i]? with
    | some (true, a) => asyncGenAsendClose h n w a
    | some (false, a) => asyncGenAthrowClose h n w a
    | none => (w, .ok .none)

def opName : ReOp → String
  | .next => "next" | .send _ => "send" | .close => "close" | .throw _ => "throw"
  | .flags => "flags" | .anext => "anext" | .asend _ => "asend" | .aclose => "aclose"
  | .athrow _ => "athrow" | .heldSend _ => "hsend" | .heldThrow _ _ => "hthrow"
  | .heldClose _ => "hclose"

def boolStr (b : Bool) : String := if b then "1" else "0"

/-- `gi_running`/`cr_running`, or `ag_running` for an async generator. -/
def runningFlag (w : W) (r : Ref) : Bool :=
  let g := w.get r
  if g.kind = .asyncGen then g.agRunningAsync else genGetRunning g

/-- Run a reentrant call and log the outcome and the target's flags. -/
def logReOp (h : H) (n : Nat) (w : W) (r : Ref) (op : ReOp) : W :=
  let (w1, res) := doReOp h n w r op
  log w1 ("re:" ++ opName op ++ ":" ++ retRender res ++ ":" ++ boolStr (runningFlag w1 r))

/-- The receiver of `_SEND`, `Python/bytecodes.c:1676-1720`. An exact generator or coroutine
below `FRAME_EXECUTING` is resumed inline, which is what `gen_send_ex` does for it; one that
is not goes through `PyIter_Send` to `am_send`, which is `gen_send_ex` as well. For anything
else `PyIter_Send` (`Objects/abstract.c:2925-2953`) takes `tp_iternext` for `None` when there
is one, else the `send` method. -/
def doSend (h : H) (w : W) (recv : O) (v : O) : W × Ret SV :=
  match recv with
  | .gen sub => genSend h w sub (some v)
  | .other (.foreign id) =>
    if v.isNone = true then
      foreignNext (log w "f.next") id
    else if (w.ext.foreign id).spec.hasSend then
      foreignNext (log w ("f.send:" ++ renderObj v)) id
    else (w, .err (some (attrError "send")))
  | _ => (w, .err (some (mkExc "TypeError" "bad receiver")))

/-- `yield from sub`/`await sub`: make the receiver. For `await` this is
`_PyEval_GetAwaitable`, `Python/ceval.c:3646-3667`, on an object that the script
just made. -/
def startSub (h : H) (w : W) (kind : GenKind) (s : Sub) : W × Except (Exc SV) O :=
  match s, kind with
  | .script body, .gen =>
    let (w1, r) := allocGen w .gen body
    (w1, .ok (.gen r))
  | .script body, _ =>
    let (w1, r) := allocGen w .coro body
    match pyCoroGetAwaitableIter h w1 (.gen r) with
    | (w2, .ok o) => (w2, .ok o)
    | (w2, .err e) => (w2, .error (e.getD Exc.fuel))
  | .iterCoro body, _ =>
    let (w1, r) := allocGen w .gen body
    let w2 := w1.set r { w1.get r with
      code := { codeFor .gen with flags := CO_GENERATOR ||| CO_ITERABLE_COROUTINE } }
    match pyCoroGetAwaitableIter h w2 (.gen r) with
    | (w3, .ok o) => (w3, .ok o)
    | (w3, .err e) => (w3, .error (e.getD Exc.fuel))
  | .foreign spec, _ =>
    let (w1, id) := allocForeign w spec
    (w1, .ok (.other (.foreign id)))
  | .badAwait k, _ =>
    let o : O := match k with
      | 0 => .other (.junk "int")
      | _ => .other (.awaitable 0 k)
    match pyCoroGetAwaitableIter h w o with
    | (w2, .ok o') => (w2, .ok o')
    | (w2, .err e) => (w2, .error (e.getD Exc.fuel))

/-- The frame loop. `s` is step fuel; `n` is the recursion fuel for nested model
calls. -/
def runK (h : H) (n : Nat) : Nat → W → Ref → Mode → List K → W × ResumeOutcome SV
  | 0, w, _, _, _ => (w, .raised Exc.fuel)
  | s + 1, w, r, mode, k =>
    let kind := (w.get r).kind
    match mode, k with
    | .send recv v, k' =>
      let (w1, res) := doSend h w recv v
      match res with
      | .ok y => (setFrame w1 r (.sending recv :: k'),
          .yielded true y { opcode := RESUME, oparg := 2 } recv)
      | .err e =>
        match fetchStopIterationValue e with
        | .ok val => runK h n s (log w1 ("yf:" ++ renderObj val)) r .run k'
        | .err e' => runK h n s w1 r (.unwind (e'.getD Exc.fuel)) k'
    | .run, [] => (w, .returned .none)
    | .run, .seq [] :: k' => runK h n s w r .run k'
    | .run, .seq (a :: as) :: k' =>
      let k1 := K.seq as :: k'
      match a with
      | .yld v =>
        let value : O := match kind with
          | .asyncGen => .wrapped (.other (.int v))
          | _ => .other (.int v)
        (setFrame w r (.recv :: k1), .yielded false value (InstrPtr.resumeAfterYield (depth1 k1)) .none)
      | .yldFrom sub =>
        match startSub h w kind sub with
        | (w1, .ok recv) => runK h n s w1 r (.send recv .none) k1
        | (w1, .error e) => runK h n s w1 r (.unwind e) k1
      | .ret v =>
        runK h n s w r (.returning (match v with | some i => .other (.int i) | none => .none)) k1
      | .raise c => runK h n s w r (.unwind (raised c)) k1
      | .tryExc b c hd => runK h n s w r .run (.seq b :: .tryE c hd :: k1)
      | .tryFin b f => runK h n s w r .run (.seq b :: .tryF f :: k1)
      | .loop m b => runK h n s w r .run (.loop m b :: k1)
      | .reent op self =>
        runK h n s (logReOp h n w (if self then r else w.ext.top) op) r .run k1
    | .run, .tryE .. :: k' => runK h n s w r .run k'
    | .run, .tryF f :: k' => runK h n s w r .run (.seq f :: .afterFin .run :: k')
    | .run, .handler :: k' => runK h n s w r .run k'
    | .run, .afterFin m :: k' => runK h n s w r m k'
    | .run, .loop 0 _ :: k' => runK h n s w r .run k'
    | .run, .loop (m + 1) b :: k' => runK h n s w r .run (.seq b :: .loop m b :: k')
    | .run, _ :: k' => runK h n s w r .run k'
    | .unwind e, [] => (w, .raised (stopIterationError kind e))
    | .unwind e, .tryE c hd :: k' =>
      if classMatches e.cls c then
        runK h n s (log w ("caught:" ++ e.cls ++ ":" ++ excStr e)) r .run (.seq hd :: .handler :: k')
      else runK h n s w r (.unwind e) k'
    | .unwind e, .tryF f :: k' => runK h n s w r .run (.seq f :: .afterFin (.unwind e) :: k')
    | .unwind e, _ :: k' => runK h n s w r (.unwind e) k'
    | .returning v, [] => (w, .returned v)
    | .returning v, .tryF f :: k' =>
      runK h n s w r .run (.seq f :: .afterFin (.returning v) :: k')
    | .returning v, _ :: k' => runK h n s w r (.returning v) k'

def stepFuel : Nat := 400

/-- The `resume` of a script frame. -/
def runFrame (h : H) (n : Nat) (w : W) (r : Ref) (arg : O) (thrown : Option (Exc SV)) :
    W × ResumeOutcome SV :=
  let w0 := w.set r { w.get r with instr := InstrPtr.other }
  let k := w.ext.frames r
  match thrown, k with
  | some e, .sending _ :: k' =>
    if e.isStopIteration then
      runK h n stepFuel (log w0 ("yf:" ++ renderObj e.value)) r .run k'
    else runK h n stepFuel w0 r (.unwind e) k'
  | some e, .recv :: k' => runK h n stepFuel w0 r (.unwind e) k'
  -- Thrown into a `FRAME_CREATED` frame: the exception is raised at the first
  -- `RESUME`, outside the handler the compiler wraps the body in, so it leaves the
  -- frame unchanged (no `stopiteration_error`).
  | some e, _ => (w0, .raised e)
  | none, .recv :: k' => runK h n stepFuel (log w0 ("recv:" ++ renderObj arg)) r .run k'
  | none, .sending recv :: k' => runK h n stepFuel w0 r (.send recv arg) k'
  | none, k' => runK h n stepFuel w0 r .run k'

/-- `BaseException.__init__` and `str`, as far as the scripts go. -/
def normalize (typ : O) (val : Option O) : Exc SV :=
  match typ with
  | .excClass k c =>
    let msg := match val with
      | some .none | none => ""
      | some v => renderObj v
    let value : O := match k, val with
      | .stopIteration, some v => v
      | _, _ => .none
    ⟨k, c, msg, value⟩
  | _ => Exc.fuel

def typeNameOf : O → String
  | .none => "NoneType"
  | .gen _ => "generator"
  | .wrapped _ => "async_generator_wrapped_value"
  | .str _ => "str"
  | .traceback => "traceback"
  | .excClass _ _ => "type"
  | .excInst _ c _ _ => c
  | .other (.int _) => "int"
  | .other (.foreign _) => "It"
  | .other (.awaitable _ k) => if k = 4 then "NoAw" else "BadAw"
  | .other (.meth _ _) => "method"
  | .other (.junk t) => t

/-- `%T`: the difftest runs as `__main__`, so no module prefix. -/
def typeFqNameOf : O → String
  | .other (.awaitable _ k) => if k = 4 then "Outer.NoAw" else "Outer.BadAw"
  | o => typeNameOf o

def baseHooks : H where
  resume w _ _ _ := (w, .raised Exc.fuel)
  getClose w _ := (w, .error Exc.fuel)
  getThrow w _ := (w, .error Exc.fuel)
  callNoArgs w _ := (w, .err (some Exc.fuel))
  callOneArg w _ _ := (w, .err (some Exc.fuel))
  callThrow w _ _ _ _ := (w, .err (some Exc.fuel))
  unraisable w _ _ := w
  warn w _ := (w, none)
  warnUnawaitedCoro w _ := w
  warnUnawaitedAgen w _ _ := w
  normalize := normalize
  typeName := typeNameOf
  typeFqName := typeFqNameOf
  audit _ _ := none
  frameObject _ _ := .other (.junk "frame")
  isIter _ := false
  amAwait _ _ := none

/-- Hooks one recursion level up from `inner`. -/
def scriptHooks (inner : H) (n : Nat) : H :=
  { baseHooks with
    resume := fun w r arg thrown => runFrame inner n w r arg thrown
    getClose := fun w o =>
      match o with
      | .other (.foreign id) =>
        match (w.ext.foreign id).spec.closeB with
        | 0 | 5 => (w, .ok none)
        | 4 => (w, .error (raised "ValueError" "attr"))
        | 6 =>
          match (w.ext.foreign id).spec.reent with
          | some op => (logReOp inner n w w.ext.top (foreignSpecReent op), .ok none)
          | none => (w, .ok none)
        | _ => (w, .ok (some (.other (.meth id "close"))))
      | _ => (w, .ok none)
    getThrow := fun w o =>
      match o with
      | .other (.foreign id) =>
        match (w.ext.foreign id).spec.throwB with
        | 0 | 6 => (w, .ok none)
        | 5 => (w, .error (raised "ValueError" "attr"))
        | 7 =>
          match (w.ext.foreign id).spec.reent with
          | some op => (logReOp inner n w w.ext.top (foreignSpecReent op), .ok none)
          | none => (w, .ok none)
        | _ => (w, .ok (some (.other (.meth id "throw"))))
      | _ => (w, .ok none)
    callNoArgs := fun w m =>
      match m with
      | .other (.meth id "close") =>
        let spec := (w.ext.foreign id).spec
        let w1 := log w "f.close"
        let w2 := match spec.reent with
          | some op => logReOp inner n w1 w1.ext.top (foreignSpecReent op)
          | none => w1
        match spec.closeB with
        | 2 => (w2, .err (some (raised "ValueError" "c")))
        | 3 => (w2, .err (some (setStopIterationValue (.other (.int 301)))))
        | _ => (w2, .ok .none)
      | _ => (w, .err (some Exc.fuel))
    callThrow := fun w m typ val _ =>
      match m with
      | .other (.meth id "throw") =>
        let spec := (w.ext.foreign id).spec
        let w1 := log w ("f.throw:" ++ renderObj typ)
        let w2 := match spec.reent with
          | some op => logReOp inner n w1 w1.ext.top (foreignSpecReent op)
          | none => w1
        match spec.throwB with
        | 2 => (w2, .ok (.other (.int 200)))
        | 3 => (w2, .err (some (setStopIterationValue (.other (.int 300)))))
        | 4 => (w2, .err (some (raised "RuntimeError" "t")))
        | _ => (w2, .err (some (reraise baseHooks typ val)))
      | _ => (w, .err (some Exc.fuel))
    callOneArg := fun w f _ =>
      match f with
      | .other (.junk "firstiter") =>
        let w1 := log w "hook:firstiter"
        if w1.ext.firstiterB = 2 then (w1, .err (some (raised "ValueError" "h")))
        else (w1, .ok .none)
      | .other (.junk "finalizer") =>
        let w1 := log w "hook:finalizer"
        if w1.ext.finalizerB = 2 then (w1, .err (some (raised "ValueError" "h")))
        else (w1, .ok .none)
      | _ => (w, .err (some Exc.fuel))
    unraisable := fun w _ e => log w ("unraisable:" ++ e.cls ++ ":" ++ excStr e)
    warn := fun w msg =>
      if w.ext.warnErr then (w, some (mkExc "DeprecationWarning" msg))
      else (log w "warn:DeprecationWarning", none)
    warnUnawaitedCoro := fun w _ => log w "warn:RuntimeWarning"
    warnUnawaitedAgen := fun w _ _ => log w "warn:RuntimeWarning"
    isIter := fun o =>
      match o with
      | .other (.foreign _) => true
      | _ => false
    amAwait := fun w o =>
      match o with
      | .other (.awaitable _ 1) =>
        let (w1, r) := allocGen w .coro []
        some (w1, .ok (.gen r))
      | .other (.awaitable _ 2) => some (w, .ok (.other (.int 3)))
      | .other (.awaitable _ 4) => none
      | .other (.awaitable _ _) => some (w, .err (some (raised "ValueError" "aw")))
      | _ => none }

def hooksAt : Nat → H
  | 0 => baseHooks
  | n + 1 => scriptHooks (hooksAt n) n

/-- Recursion depth the difftest runs with. -/
def depth : Nat := 24

def emptyGen : GenObj SV := {}

/-- A world holding one object of the given kind at `Ref` 0. -/
def initialWorld (kind : GenKind) (body : List Act) (warnErr : Bool)
    (firstiterB finalizerB : Nat) : W :=
  let w0 : W :=
    { gens := fun _ => emptyGen
      asends := fun _ => default
      athrows := fun _ => default
      firstiter := if firstiterB = 0 then none else some (.other (.junk "firstiter"))
      finalizerHook := if finalizerB = 0 then none else some (.other (.junk "finalizer"))
      ext := { warnErr := warnErr, firstiterB := firstiterB, finalizerB := finalizerB } }
  let g : GenObj SV := genNewWithQualname kind (codeFor kind) none none
  setFrame (w0.set 0 g) 0 [.seq body]

end PyLean.Bytecode.GenObj.Script
