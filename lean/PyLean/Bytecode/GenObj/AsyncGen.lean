import PyLean.Bytecode.GenObj.Model

/-!
# The async generator state machine in `Objects/genobject.c`

`async_gen_*` and the `asend`/`athrow` awaitables, :1496-2421. Awaitables live in
the world's tables because the generator body can hold and re-enter them.
-/

namespace PyLean.Bytecode.GenObj

variable {V X : Type}

/-- `async_gen_init_hooks`, :1496-1530. Note the order: `ag_hooks_inited` is set
before `firstiter` runs, so a raising hook is not retried. -/
def asyncGenInitHooks (h : Hooks V X) (w : World V X) (r : Ref) : World V X × CStatus V :=
  if (w.get r).agHooksInited = true then (w, .ok)
  else
    let w1 := w.set r { w.get r with agHooksInited := true }
    let w2 := match w1.finalizerHook with
      | some f => w1.set r { w1.get r with finalizer := some f }
      | none => w1
    match w2.firstiter with
    | some firstiter =>
      match h.callOneArg w2 firstiter (.gen r) with
      | (w3, .err e) => (w3, .fail e)
      | (w3, .ok _) => (w3, .ok)
    | none => (w2, .ok)

/-- `async_gen_asend_new`, :1965-1982. `a` is the freshly allocated object. -/
def asyncGenAsendNew (w : World V X) (a r : Ref) (sendval : Option (Obj V)) : World V X :=
  { w with asends := fun q => if q = a then { gen := r, sendval := sendval, state := .init }
                              else w.asends q }

/-- `async_gen_athrow_new`, :2408-2421. -/
def asyncGenAthrowNew (w : World V X) (a r : Ref) (args : Option (List (Obj V))) : World V X :=
  { w with athrows := fun q => if q = a then { gen := r, args := args, state := .init }
                               else w.athrows q }

/-- `async_gen_anext`, :1533-1541. -/
def asyncGenAnext (h : Hooks V X) (w : World V X) (r a : Ref) : World V X × CStatus V :=
  match asyncGenInitHooks h w r with
  | (w1, .fail e) => (w1, .fail e)
  | (w1, .ok) => (asyncGenAsendNew w1 a r none, .ok)

/-- `async_gen_asend`, :1544-1552. -/
def asyncGenAsend (h : Hooks V X) (w : World V X) (r a : Ref) (arg : Obj V) :
    World V X × CStatus V :=
  match asyncGenInitHooks h w r with
  | (w1, .fail e) => (w1, .fail e)
  | (w1, .ok) => (asyncGenAsendNew w1 a r (some arg), .ok)

/-- `async_gen_aclose`, :1555-1563. -/
def asyncGenAclose (h : Hooks V X) (w : World V X) (r a : Ref) : World V X × CStatus V :=
  match asyncGenInitHooks h w r with
  | (w1, .fail e) => (w1, .fail e)
  | (w1, .ok) => (asyncGenAthrowNew w1 a r none, .ok)

/-- `async_gen_athrow`, :1565-1581. The argument count is not checked here on 3.14:
that happens at the first `send`, after the state has moved (:2169). -/
def asyncGenAthrow (h : Hooks V X) (w : World V X) (r a : Ref) (args : List (Obj V)) :
    World V X × CStatus V :=
  let (w1, warned) : World V X × Option (Exc V) :=
    if args.length > 1 then
      h.warn w "the (type, exc, tb) signature of athrow() is deprecated, use the single-arg signature instead."
    else (w, none)
  match warned with
  | some e => (w1, .fail (some e))
  | none =>
    match asyncGenInitHooks h w1 r with
    | (w2, .fail e) => (w2, .fail e)
    | (w2, .ok) => (asyncGenAthrowNew w2 a r (some args), .ok)

/-- `async_gen_unwrap_value`, :1727-1754. -/
def asyncGenUnwrapValue (w : World V X) (r : Ref) : Ret V → World V X × Ret V
  | .err e =>
    let e' := e.getD Exc.stopAsyncIteration
    let w1 := if e'.isStopAsyncIteration || e'.isGeneratorExit then w.setClosed r else w
    (w1.setRunning r false, .err (some e'))
  | .ok (.wrapped val) => (w.setRunning r false, .err (some (setStopIterationValue val)))
  | .ok v => (w, .ok v)

/-- `arg == NULL || arg == Py_None` (:1809). -/
def isNullOrNone : Option (Obj V) → Bool
  | none | some .none => true
  | some _ => false

def reuseAsendMsg : String := "cannot reuse already awaited __anext__()/asend()"
def anextRunningMsg : String := "anext(): asynchronous generator is already running"

/-- `async_gen_asend_send`, :1789-1824 (`arg` is `none` from
`async_gen_asend_iternext`, :1827-1831). -/
def asyncGenAsendSend (h : Hooks V X) (w : World V X) (a : Ref) (arg : Option (Obj V)) :
    World V X × Ret V :=
  let o := w.asends a
  if o.state = .closed then
    (w, .err (some (Exc.runtimeError reuseAsendMsg)))
  else if o.state = .init ∧ (w.get o.gen).agRunningAsync = true then
    (w.setAsendState a .closed, .err (some (Exc.runtimeError anextRunningMsg)))
  else
    let (w1, arg') : World V X × Option (Obj V) :=
      if o.state = .init then
        (w.setAsendState a .iter, if isNullOrNone arg then o.sendval else arg)
      else (w, arg)
    let w2 := w1.setRunning o.gen true
    let (w3, res) := genSend h w2 o.gen arg'
    match asyncGenUnwrapValue w3 o.gen res with
    | (w4, .err e) => (w4.setAsendState a .closed, .err e)
    | (w4, .ok v) => (w4, .ok v)

/-- `async_gen_asend_iternext`, :1827-1831. -/
def asyncGenAsendIternext (h : Hooks V X) (w : World V X) (a : Ref) : World V X × Ret V :=
  asyncGenAsendSend h w a none

/-- `async_gen_asend_throw`, :1834-1868. -/
def asyncGenAsendThrow (h : Hooks V X) (fuel : Nat) (w : World V X) (a : Ref)
    (args : List (Obj V)) : World V X × Ret V :=
  let o := w.asends a
  if o.state = .closed then
    (w, .err (some (Exc.runtimeError reuseAsendMsg)))
  else if o.state = .init ∧ (w.get o.gen).agRunningAsync = true then
    (w.setAsendState a .closed, .err (some (Exc.runtimeError anextRunningMsg)))
  else
    let w1 := if o.state = .init then (w.setAsendState a .iter).setRunning o.gen true else w
    let (w2, res) := genThrow h fuel w1 o.gen args
    match asyncGenUnwrapValue w2 o.gen res with
    | (w3, .err e) => ((w3.setRunning o.gen false).setAsendState a .closed, .err e)
    | (w3, .ok v) => (w3, .ok v)

/-- The exception a `close()` of an awaitable passes on, :1881-1885 and :2321-2325. -/
def swallowedByClose : Option (Exc V) → Bool
  | some e => e.isStopIteration || e.isStopAsyncIteration || e.isGeneratorExit
  | none => false

/-- `async_gen_asend_close`, :1871-1894. -/
def asyncGenAsendClose (h : Hooks V X) (fuel : Nat) (w : World V X) (a : Ref) :
    World V X × Ret V :=
  if (w.asends a).state = .closed then (w, .ok .none)
  else
    match asyncGenAsendThrow h fuel w a [.excClass .generatorExit "GeneratorExit"] with
    | (w1, .err e) => if swallowedByClose e then (w1, .ok .none) else (w1, .err e)
    | (w1, .ok _) => (w1, .err (some (Exc.runtimeError "coroutine ignored GeneratorExit")))

/-- `async_gen_asend_finalize`, :1896-1903. -/
def asyncGenAsendFinalize (h : Hooks V X) (w : World V X) (a : Ref) : World V X :=
  if (w.asends a).state = .init then
    h.warnUnawaitedAgen w (w.asends a).gen "asend"
  else w

/-- `_PyAsyncGenValueWrapperNew`, :2050-2067. -/
def asyncGenValueWrapperNew (val : Obj V) : Obj V := .wrapped val

def reuseAthrowMsg : String := "cannot reuse already awaited aclose()/athrow()"

/-- `yield_close:`, :2207-2212. -/
def athrowYieldClose (w : World V X) (a gen : Ref) : World V X × Ret V :=
  (((w.setRunning gen false).setAthrowState a .closed),
   .err (some (Exc.runtimeError (ignoredExitMsg .asyncGen))))

/-- `check_error:`, :2214-2230. -/
def athrowCheckError (w : World V X) (a gen : Ref) (acloseMode : Bool) (e : Option (Exc V)) :
    World V X × Ret V :=
  let w1 := (w.setRunning gen false).setAthrowState a .closed
  if matchesStopAsyncOrExit e = true ∧ acloseMode = true then
    (w1, .err (some Exc.stopIterationNone))
  else (w1, .err e)

/-- :2124-2133 and :2249-2258. -/
def athrowRunningMsg : Option (List (Obj V)) → String
  | none => "aclose(): asynchronous generator is already running"
  | some _ => "athrow(): asynchronous generator is already running"

def nonInitCoroMsg : String := "can't send non-None value to a just-started coroutine"

/-- `async_gen_athrow_send`, :2101-2231. -/
def asyncGenAthrowSend (h : Hooks V X) (fuel : Nat) (w : World V X) (a : Ref) (arg : Obj V) :
    World V X × Ret V :=
  let o := w.athrows a
  let gen := o.gen
  if o.state = .closed then
    (w, .err (some (Exc.runtimeError reuseAthrowMsg)))
  else if (w.get gen).state.finished = true then
    (w.setAthrowState a .closed, .err (some Exc.stopIterationNone))
  else if o.state = .init then
    if (w.get gen).agRunningAsync = true then
      (w.setAthrowState a .closed, .err (some (Exc.runtimeError (athrowRunningMsg o.args))))
    else if (w.get gen).agClosed = true then
      (w.setAthrowState a .closed, .err (some Exc.stopAsyncIteration))
    else if arg.isNone = false then
      (w, .err (some (Exc.runtimeError nonInitCoroMsg)))
    else
      let w1 := (w.setAthrowState a .iter).setRunning gen true
      match o.args with
      | none =>
        let w2 := w1.setClosed gen
        match genThrowF h fuel w2 gen false (.excClass .generatorExit "GeneratorExit") none none with
        | (w3, .ok (.wrapped _)) => athrowYieldClose w3 a gen
        | (w3, .ok v) => (w3, .ok v)
        | (w3, .err e) => athrowCheckError w3 a gen true e
      | some args =>
        match checkPositional "athrow" args.length 1 3 with
        | some e => (w1, .err (some e))
        | none =>
          let (typ, val, tb) := unpackThrowArgs args
          let (w2, res) := genThrowF h fuel w1 gen false typ val tb
          match asyncGenUnwrapValue w2 gen res with
          | (w3, .ok v) => (w3, .ok v)
          | (w3, .err e) => athrowCheckError w3 a gen false e
  else
    let (w1, retval) := genSend h w gen (some arg)
    match o.args with
    | some _ => asyncGenUnwrapValue w1 gen retval
    | none =>
      match retval with
      | .ok (.wrapped _) => athrowYieldClose w1 a gen
      | .ok v => (w1, .ok v)
      | .err e => athrowCheckError w1 a gen true e

/-- `async_gen_athrow_iternext`, :2304-2308. -/
def asyncGenAthrowIternext (h : Hooks V X) (fuel : Nat) (w : World V X) (a : Ref) :
    World V X × Ret V :=
  asyncGenAthrowSend h fuel w a .none

/-- `async_gen_athrow_throw`, :2234-2301. -/
def asyncGenAthrowThrow (h : Hooks V X) (fuel : Nat) (w : World V X) (a : Ref)
    (args : List (Obj V)) : World V X × Ret V :=
  let o := w.athrows a
  let gen := o.gen
  if o.state = .closed then
    (w, .err (some (Exc.runtimeError reuseAthrowMsg)))
  else if o.state = .init ∧ (w.get gen).agRunningAsync = true then
    (w.setAthrowState a .closed, .err (some (Exc.runtimeError (athrowRunningMsg o.args))))
  else
    let w1 := if o.state = .init then (w.setAthrowState a .iter).setRunning gen true else w
    let (w2, retval) := genThrow h fuel w1 gen args
    match o.args with
    | some _ =>
      match asyncGenUnwrapValue w2 gen retval with
      | (w3, .err e) => ((w3.setRunning gen false).setAthrowState a .closed, .err e)
      | (w3, .ok v) => (w3, .ok v)
    | none =>
      match retval with
      | .ok (.wrapped _) =>
        (((w2.setRunning gen false).setAthrowState a .closed),
         .err (some (Exc.runtimeError (ignoredExitMsg .asyncGen))))
      | .ok v => (w2, .ok v)
      | .err e =>
        let w3 := (w2.setRunning gen false).setAthrowState a .closed
        if matchesStopAsyncOrExit e = true then (w3, .err (some Exc.stopIterationNone))
        else (w3, .err e)

/-- `async_gen_athrow_close`, :2311-2334. -/
def asyncGenAthrowClose (h : Hooks V X) (fuel : Nat) (w : World V X) (a : Ref) :
    World V X × Ret V :=
  if (w.athrows a).state = .closed then (w, .ok .none)
  else
    match asyncGenAthrowThrow h fuel w a [.excClass .generatorExit "GeneratorExit"] with
    | (w1, .err e) => if swallowedByClose e then (w1, .ok .none) else (w1, .err e)
    | (w1, .ok _) => (w1, .err (some (Exc.runtimeError "coroutine ignored GeneratorExit")))

/-- `async_gen_athrow_finalize`, :2337-2345. -/
def asyncGenAthrowFinalize (h : Hooks V X) (w : World V X) (a : Ref) : World V X :=
  let o := w.athrows a
  if o.state = .init then
    h.warnUnawaitedAgen w o.gen (match o.args with | some _ => "athrow" | none => "aclose")
  else w

end PyLean.Bytecode.GenObj
