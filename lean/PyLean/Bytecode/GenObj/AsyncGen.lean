import PyLean.Bytecode.GenObj.Model

/-!
# The async generator state machine in `Objects/genobject.c`

`async_gen_*` and the `asend`/`athrow` awaitables, :1668-2621. Awaitables live in
the world's tables because the generator body can hold and re-enter them.
-/

namespace PyLean.Bytecode.GenObj

variable {V X : Type}

/-- `async_gen_init_hooks`, :1669-1702. Note the order: `ag_hooks_inited` is set
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
      let c := h.callOneArg w2 firstiter (.gen r)
      match c.2 with
      | .err e => (c.1, .fail e)
      | .ok _ => (c.1, .ok)
    | none => (w2, .ok)

/-- `async_gen_asend_new`, :2161-2177. `a` is the freshly allocated object. -/
def asyncGenAsendNew (w : World V X) (a r : Ref) (sendval : Option (Obj V)) : World V X :=
  { w with asends := fun q => if q = a then { gen := r, sendval := sendval, state := .init }
                              else w.asends q }

/-- `async_gen_athrow_new`, :2599-2621, past the `PyArg_UnpackTuple` that `asyncGenAthrow`
does: `args` is what it unpacked. -/
def asyncGenAthrowNew (w : World V X) (a r : Ref)
    (args : Option (Obj V × Option (Obj V) × Option (Obj V))) : World V X :=
  { w with athrows := fun q => if q = a then { gen := r, args := args, state := .init }
                               else w.athrows q }

/-- `async_gen_anext`, :1706-1713. -/
def asyncGenAnext (h : Hooks V X) (w : World V X) (r a : Ref) : World V X × CStatus V :=
  match asyncGenInitHooks h w r with
  | (w1, .fail e) => (w1, .fail e)
  | (w1, .ok) => (asyncGenAsendNew w1 a r none, .ok)

/-- `async_gen_asend`, :1717-1724. -/
def asyncGenAsend (h : Hooks V X) (w : World V X) (r a : Ref) (arg : Obj V) :
    World V X × CStatus V :=
  match asyncGenInitHooks h w r with
  | (w1, .fail e) => (w1, .fail e)
  | (w1, .ok) => (asyncGenAsendNew w1 a r (some arg), .ok)

/-- `async_gen_aclose`, :1728-1735. -/
def asyncGenAclose (h : Hooks V X) (w : World V X) (r a : Ref) : World V X × CStatus V :=
  match asyncGenInitHooks h w r with
  | (w1, .fail e) => (w1, .fail e)
  | (w1, .ok) => (asyncGenAthrowNew w1 a r none, .ok)

/-- `async_gen_athrow`, :1738-1753, and `PyArg_UnpackTuple` at the top of
`async_gen_athrow_new`, :2604-2606: since 3.15 a wrong argument count fails here, after the
hooks ran and before any awaitable exists, not at the first `send`. -/
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
    | (w2, .ok) =>
      match checkPositional "athrow" args.length 1 3 with
      | some e => (w2, .fail (some e))
      | none => (asyncGenAthrowNew w2 a r (some (unpackThrowArgs args)), .ok)

/-- `async_gen_unwrap_value`, :1912-1938. -/
def asyncGenUnwrapValue (w : World V X) (r : Ref) : Ret V → World V X × Ret V
  | .err e =>
    let e' := e.getD Exc.stopAsyncIteration
    let w1 := if e'.isStopAsyncIteration || e'.isGeneratorExit then w.setClosed r else w
    (w1.setRunning r false, .err (some e'))
  | .ok (.wrapped val) => (w.setRunning r false, .err (some (setStopIterationValue val)))
  | .ok v => (w, .ok v)

/-- `arg == NULL || arg == Py_None` (:1993). -/
def isNullOrNone : Option (Obj V) → Bool
  | none | some .none => true
  | some _ => false

def reuseAsendMsg : String := "cannot reuse already awaited __anext__()/asend()"
def anextRunningMsg : String := "anext(): asynchronous generator is already running"

/-- :2001-2007, the tail shared by `send`: unwrap, and close the awaitable on `NULL`. -/
def asendFinish (w : World V X) (a gen : Ref) (res : Ret V) : World V X × Ret V :=
  let u := asyncGenUnwrapValue w gen res
  match u.2 with
  | .err e => (u.1.setAsendState a .closed, .err e)
  | .ok v => (u.1, .ok v)

/-- `async_gen_asend_send`, :1974-2008 (`arg` is `none` from
`async_gen_asend_iternext`, :2025-2028). -/
def asyncGenAsendSend (h : Hooks V X) (w : World V X) (a : Ref) (arg : Option (Obj V)) :
    World V X × Ret V :=
  let o := w.asends a
  if o.state = .closed then
    (w, .err (some (Exc.runtimeError reuseAsendMsg)))
  else if o.state = .init ∧ (w.get o.gen).agRunningAsync = true then
    (w.setAsendState a .closed, .err (some (Exc.runtimeError anextRunningMsg)))
  else
    let w1 := if o.state = .init then w.setAsendState a .iter else w
    let arg' := if o.state = .init ∧ isNullOrNone arg = true then o.sendval else arg
    let res := genSend h (w1.setRunning o.gen true) o.gen arg'
    asendFinish res.1 a o.gen res.2

/-- `async_gen_asend_iternext`, :2025-2028. -/
def asyncGenAsendIternext (h : Hooks V X) (w : World V X) (a : Ref) : World V X × Ret V :=
  asyncGenAsendSend h w a none

/-- :2057-2062. -/
def asendThrowFinish (w : World V X) (a gen : Ref) (res : Ret V) : World V X × Ret V :=
  let u := asyncGenUnwrapValue w gen res
  match u.2 with
  | .err e => ((u.1.setRunning gen false).setAsendState a .closed, .err e)
  | .ok v => (u.1, .ok v)

/-- `async_gen_asend_throw`, :2032-2065. -/
def asyncGenAsendThrow (h : Hooks V X) (fuel : Nat) (w : World V X) (a : Ref)
    (args : List (Obj V)) : World V X × Ret V :=
  let o := w.asends a
  if o.state = .closed then
    (w, .err (some (Exc.runtimeError reuseAsendMsg)))
  else if o.state = .init ∧ (w.get o.gen).agRunningAsync = true then
    (w.setAsendState a .closed, .err (some (Exc.runtimeError anextRunningMsg)))
  else
    let w1 := if o.state = .init then (w.setAsendState a .iter).setRunning o.gen true else w
    let res := genThrow h fuel w1 o.gen args
    asendThrowFinish res.1 a o.gen res.2

/-- The exceptions a `close()` of an awaitable swallows, :2078-2082 and :2511-2515. -/
def swallowedByClose : Option (Exc V) → Bool
  | some e => e.isStopIteration || e.isStopAsyncIteration || e.isGeneratorExit
  | none => false

/-- :2076-2090 and :2509-2523. -/
def closeResult (res : Ret V) : Ret V :=
  match res with
  | .err e => if swallowedByClose e then .ok .none else .err e
  | .ok _ => .err (some (Exc.runtimeError "coroutine ignored GeneratorExit"))

/-- `async_gen_asend_close`, :2069-2091. -/
def asyncGenAsendClose (h : Hooks V X) (fuel : Nat) (w : World V X) (a : Ref) :
    World V X × Ret V :=
  if (w.asends a).state = .closed then (w, .ok .none)
  else
    let t := asyncGenAsendThrow h fuel w a [.excClass .generatorExit "GeneratorExit"]
    (t.1, closeResult t.2)

/-- `async_gen_asend_finalize`, :2094-2100. -/
def asyncGenAsendFinalize (h : Hooks V X) (w : World V X) (a : Ref) : World V X :=
  if (w.asends a).state = .init then
    h.warnUnawaitedAgen w (w.asends a).gen "asend"
  else w

/-- `async_gen_asend_dealloc`, :1945-1961: `PyObject_CallFinalizerFromDealloc` runs
`async_gen_asend_finalize` unless the collector already did (`finalized`); the rest drops
references and returns the object to the freelist. -/
def asyncGenAsendDealloc (h : Hooks V X) (w : World V X) (a : Ref) (finalized : Bool) : World V X :=
  if finalized then w else asyncGenAsendFinalize h w a

/-- `_PyAsyncGenValueWrapperNew`, :2246-2262. -/
def asyncGenValueWrapperNew (val : Obj V) : Obj V := .wrapped val

def reuseAthrowMsg : String := "cannot reuse already awaited aclose()/athrow()"

/-- `yield_close:`, :2397-2402. -/
def athrowYieldClose (w : World V X) (a gen : Ref) : World V X × Ret V :=
  (((w.setRunning gen false).setAthrowState a .closed),
   .err (some (Exc.runtimeError (ignoredExitMsg .asyncGen))))

/-- `check_error:`, :2404-2420. -/
def athrowCheckError (w : World V X) (a gen : Ref) (acloseMode : Bool) (e : Option (Exc V)) :
    World V X × Ret V :=
  let w1 := (w.setRunning gen false).setAthrowState a .closed
  if matchesStopAsyncOrExit e = true ∧ acloseMode = true then
    (w1, .err (some Exc.stopIterationNone))
  else (w1, .err e)

/-- :2323-2332 and :2439-2448. -/
def athrowRunningMsg : Option (Obj V × Option (Obj V) × Option (Obj V)) → String
  | none => "aclose(): asynchronous generator is already running"
  | some _ => "athrow(): asynchronous generator is already running"

def nonInitCoroMsg : String := "can't send non-None value to a just-started coroutine"

/-- :2356-2361 and :2384-2394: what `aclose()` mode does with a result. -/
def acloseTail (w : World V X) (a gen : Ref) : Ret V → World V X × Ret V
  | .ok (.wrapped _) => athrowYieldClose w a gen
  | .ok v => (w, .ok v)
  | .err e => athrowCheckError w a gen true e

/-- :2350-2362: `aclose()` mode, first step. -/
def athrowStartAclose (h : Hooks V X) (fuel : Nat) (w : World V X) (a gen : Ref) :
    World V X × Ret V :=
  let t := genThrowF h fuel (w.setClosed gen) gen false
    (.excClass .generatorExit "GeneratorExit") none none
  acloseTail t.1 a gen t.2

/-- :2363-2369: `athrow()` mode, first step. -/
def athrowStartArgs (h : Hooks V X) (fuel : Nat) (w : World V X) (a gen : Ref)
    (tv : Obj V × Option (Obj V) × Option (Obj V)) : World V X × Ret V :=
  let t := genThrowF h fuel w gen false tv.1 tv.2.1 tv.2.2
  let u := asyncGenUnwrapValue t.1 gen t.2
  match u.2 with
  | .ok v => (u.1, .ok v)
  | .err e => athrowCheckError u.1 a gen false e

/-- :2378-2395: later steps. In `athrow()` mode the result goes through
`async_gen_unwrap_value` and is returned at once, so `agt_state` stays
`AWAITABLE_STATE_ITER` even when the awaitable is finished. -/
def athrowIter (h : Hooks V X) (w : World V X) (a gen : Ref)
    (args : Option (Obj V × Option (Obj V) × Option (Obj V))) (arg : Obj V) : World V X × Ret V :=
  let t := genSend h w gen (some arg)
  match args with
  | some _ => asyncGenUnwrapValue t.1 gen t.2
  | none => acloseTail t.1 a gen t.2

/-- `async_gen_athrow_send`, :2301-2421. -/
def asyncGenAthrowSend (h : Hooks V X) (fuel : Nat) (w : World V X) (a : Ref) (arg : Obj V) :
    World V X × Ret V :=
  let o := w.athrows a
  if o.state = .closed then
    (w, .err (some (Exc.runtimeError reuseAthrowMsg)))
  else if (w.get o.gen).state.finished = true then
    (w.setAthrowState a .closed, .err (some Exc.stopIterationNone))
  else if o.state = .init then
    if (w.get o.gen).agRunningAsync = true then
      (w.setAthrowState a .closed, .err (some (Exc.runtimeError (athrowRunningMsg o.args))))
    else if (w.get o.gen).agClosed = true then
      (w.setAthrowState a .closed, .err (some Exc.stopAsyncIteration))
    else if arg.isNone = false then
      (w, .err (some (Exc.runtimeError nonInitCoroMsg)))
    else
      let w1 := (w.setAthrowState a .iter).setRunning o.gen true
      match o.args with
      | none => athrowStartAclose h fuel w1 a o.gen
      | some args => athrowStartArgs h fuel w1 a o.gen args
  else
    athrowIter h w a o.gen o.args arg

/-- `async_gen_athrow_iternext`, :2495-2498. -/
def asyncGenAthrowIternext (h : Hooks V X) (fuel : Nat) (w : World V X) (a : Ref) :
    World V X × Ret V :=
  asyncGenAthrowSend h fuel w a .none

/-- :2456-2490. -/
def athrowThrowFinish (w : World V X) (a gen : Ref)
    (args : Option (Obj V × Option (Obj V) × Option (Obj V))) (res : Ret V) :
    World V X × Ret V :=
  match args with
  | some _ =>
    let u := asyncGenUnwrapValue w gen res
    match u.2 with
    | .err e => ((u.1.setRunning gen false).setAthrowState a .closed, .err e)
    | .ok v => (u.1, .ok v)
  | none =>
    match res with
    | .ok (.wrapped _) =>
      ((w.setRunning gen false).setAthrowState a .closed,
       .err (some (Exc.runtimeError (ignoredExitMsg .asyncGen))))
    | .ok v => (w, .ok v)
    | .err e =>
      let w3 := (w.setRunning gen false).setAthrowState a .closed
      if matchesStopAsyncOrExit e = true then (w3, .err (some Exc.stopIterationNone))
      else (w3, .err e)

/-- `async_gen_athrow_throw`, :2425-2491. -/
def asyncGenAthrowThrow (h : Hooks V X) (fuel : Nat) (w : World V X) (a : Ref)
    (args : List (Obj V)) : World V X × Ret V :=
  let o := w.athrows a
  if o.state = .closed then
    (w, .err (some (Exc.runtimeError reuseAthrowMsg)))
  else if o.state = .init ∧ (w.get o.gen).agRunningAsync = true then
    (w.setAthrowState a .closed, .err (some (Exc.runtimeError (athrowRunningMsg o.args))))
  else
    let w1 := if o.state = .init then (w.setAthrowState a .iter).setRunning o.gen true else w
    let res := genThrow h fuel w1 o.gen args
    athrowThrowFinish res.1 a o.gen o.args res.2

/-- `async_gen_athrow_close`, :2502-2524. -/
def asyncGenAthrowClose (h : Hooks V X) (fuel : Nat) (w : World V X) (a : Ref) :
    World V X × Ret V :=
  if (w.athrows a).state = .closed then (w, .ok .none)
  else
    let t := asyncGenAthrowThrow h fuel w a [.excClass .generatorExit "GeneratorExit"]
    (t.1, closeResult t.2)

/-- `async_gen_athrow_finalize`, :2528-2535. -/
def asyncGenAthrowFinalize (h : Hooks V X) (w : World V X) (a : Ref) : World V X :=
  let o := w.athrows a
  if o.state = .init then
    h.warnUnawaitedAgen w o.gen (match o.args with | some _ => "athrow" | none => "aclose")
  else w

/-- `async_gen_athrow_dealloc`, :2272-2285, as `async_gen_asend_dealloc`. -/
def asyncGenAthrowDealloc (h : Hooks V X) (w : World V X) (a : Ref) (finalized : Bool) : World V X :=
  if finalized then w else asyncGenAthrowFinalize h w a

end PyLean.Bytecode.GenObj
