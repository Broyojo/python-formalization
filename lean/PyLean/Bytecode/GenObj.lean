import PyLean.Registry
import PyLean.Bytecode.GenObj.Legal

/-!
`Objects/genobject.c`, CPython 3.15.2: generators, coroutines, async generators.

The model is `GenObj/Model.lean` and `GenObj/AsyncGen.lean`, a state machine over an
abstract `Hooks` record whose `resume` field is the frame evaluator. `GenObj/Script.lean`
instantiates it for the difftest (`difftest/bytecode_gen_diff.py`). The properties hold
for every instantiation; `HooksLegal` in `GenObj/Legal.lean` is the only assumption made
about the interpreter, and only where a statement says so.
-/

namespace PyLean.Bytecode.GenObj

open PyLean.Registry

private def src : String := "Objects/genobject.c"

def entries : List Entry := [
  { id := "gen-send-rejected-no-effect", pyFile := src, pyFns := ["gen_send_ex", "PyGen_am_send"]
    statement := "For every generator, coroutine or async generator, every argument and every frame evaluator: a call gen_send_ex rejects (non-None to a just-started object, already executing, finished) changes nothing and gives the same result under any frame evaluator, so a finished or running frame is never resumed and each state check comes before any effect."
    source := "invariant: genobject.c:335-367 precede the first write at :368", status := .proven
    prop := ``GenSendRejectedNoEffect, thm := some ``genSendRejectedNoEffect_proven },
  { id := "gen-already-executing", pyFile := src, pyFns := ["gen_send_ex", "gen_raise_already_executing_error"]
    statement := "For every argument, gen_send_ex on an object in FRAME_EXECUTING raises ValueError with the message of its type (generator, coroutine, async generator already executing) and changes nothing."
    source := "Doc/reference/expressions.rst; genobject.c:241-252, :349-352", status := .proven
    prop := ``GenAlreadyExecuting, thm := some ``genAlreadyExecuting_proven },
  { id := "gen-resume-sees-executing", pyFile := src, pyFns := ["gen_send_ex2", "gen_send_ex", "gen_close", "_gen_throw"]
    statement := "Through gen_send_ex, gen_close or _gen_throw at any delegation depth, every call of the frame evaluator sees the frame marked FRAME_EXECUTING: replacing resume by anything at all on any other state changes no result, so a FRAME_CLEARED frame is never resumed."
    source := "invariant: the assert at genobject.c:262", status := .proven
    prop := ``GenResumeSeesExecuting, thm := some ``genResumeSeesExecuting_proven
    notes := "Hypothesis: HooksLegal, new on 3.15. gen_send_ex needs none, but gen_close and _gen_throw run Python code after their write and before the resume and do not look at the state again, so the statement rests on that code not being able to move a FRAME_EXECUTING frame. Every operation of the model refuses to." },
  { id := "gen-send-state-edges", pyFile := src, pyFns := ["gen_send_ex", "gen_send_ex2"]
    statement := "For every object, argument and frame outcome (yielded with oparg 0 or 1, returned, raised), gen_send_ex moves gi_frame_state along a legal edge: CREATED or SUSPENDED* to SUSPENDED* or CLEARED, EXECUTING and CLEARED unchanged."
    source := "invariant: asserts at genobject.c:262, :286, :298, :306", status := .proven
    prop := ``GenSendStateEdges, thm := some ``genSendStateEdges_proven },
  { id := "gen-iternext-vs-send-none", pyFile := src, pyFns := ["gen_iternext", "gen_send", "gen_send_ex", "gen_set_stop_iteration"]
    statement := "On generators and coroutines, next(g) and g.send(None) agree exactly, in result and in the resulting world, for every state and every frame outcome, once a NULL with no exception is read as StopIteration."
    source := "twin paths: gen_iternext (:760-774) and gen_send (:405-414); Doc/reference/expressions.rst generator.__next__", status := .proven
    prop := ``GenIternextVsSendNone, thm := some ``genIternextVsSendNone_proven
    notes := "Precondition: not an async generator, the type assert at genobject.c:763." },
  { id := "gen-send-vs-am-send", pyFile := src, pyFns := ["gen_send", "gen_send_ex", "PyGen_am_send", "gen_set_stop_iteration"]
    statement := "On generators and coroutines, gen.send(arg) is PyGen_am_send(arg) with gen_set_stop_iteration: same world, a yield is returned, a returned value v becomes a StopIteration carrying v, and errors are unchanged. The model does not track object identity."
    source := "twin paths: PyGen_am_send (:377-382) and gen_send (:405-414)", status := .proven
    prop := ``GenSendVsAmSend, thm := some ``genSendVsAmSend_proven },
  { id := "gen-close-idempotent", pyFile := src, pyFns := ["gen_close", "gen_clear_frame"]
    statement := "For every object and frame outcome: if close() returns normally the object is finished, and closing again returns None and changes nothing."
    source := "Doc/reference/expressions.rst generator.close", status := .proven
    prop := ``GenCloseIdempotent, thm := some ``genCloseIdempotent_proven },
  { id := "gen-close-rejects-executing", pyFile := src, pyFns := ["gen_close", "gen_raise_already_executing_error"]
    statement := "close() on an object in FRAME_EXECUTING raises the already-executing ValueError and changes nothing."
    source := "Doc/reference/expressions.rst; invariant: a running frame is not cleared; genobject.c:483-486", status := .proven
    prop := ``GenCloseRejectsExecuting, thm := some ``genCloseRejectsExecuting_proven
    notes := "Refuted on 3.14.7 (bytecode-gen-close-clears-running-frame, which crashed from a __del__ running at a generator's RESUME). 3.15 moved the check to the top of gen_close, before the fast path." },
  { id := "gen-close-rejects-executing-past-resume", pyFile := src, pyFns := ["gen_close"]
    statement := "The same for a frame anywhere but at a depth-1 RESUME with no unwind tools. Kept from the narrowing on 3.14.7, where that was the only case that held; on 3.15 it follows from gen-close-rejects-executing."
    source := "narrowing of gen-close-rejects-executing", status := .proven
    prop := ``GenCloseRejectsExecutingPastResume, thm := some ``genCloseRejectsExecutingPastResume_proven },
  { id := "gen-close-fast-slow-agree", pyFile := src, pyFns := ["gen_close", "is_resume", "gen_clear_frame", "gen_send_ex2"]
    statement := "For a suspended generator at a depth-1 RESUME whose frame raises a thrown GeneratorExit unchanged, gen_close's fast path (no unwind tools) and the slow path (with tools) give the same result, None, and the same final state, FRAME_CLEARED, and the fast path drops the frame's stack."
    source := "fast path vs slow path, genobject.c:499-540", status := .proven
    prop := ``GenCloseFastSlowAgree, thm := some ``genCloseFastSlowAgree_proven
    notes := "The hypothesis on the frame is what depth 1 means: no handler but the outermost, whose stopiteration_error passes GeneratorExit through." },
  { id := "gen-ops-state-edges", pyFile := src, pyFns := ["gen_close", "gen_close_iter", "_gen_throw", "gen_throw", "gen_throw_current_exception", "gen_set_exception"]
    statement := "gen_close and gen_throw move every generator in the world along legal edges, write back the state they hold FRAME_EXECUTING over whenever the frame did not run, and leave ag_closed and all awaitables monotone, for all arguments, frame outcomes and reentrant uses of the model from the hooks."
    source := "invariant", status := .proven
    prop := ``GenOpsStateEdges, thm := some ``genOpsStateEdges_proven
    notes := "Hypothesis: HooksLegal (Python code acts through the model). On 3.14.7 this also needed an invariant on executing frames and an assumption on the throw lookup, the two exclusions of the refuted gen-close-rejects-executing and gen-throw-lookup-sees-executing. Neither is needed on 3.15." },
  { id := "gen-async-ops-state-edges", pyFile := src, pyFns := ["async_gen_asend_send", "async_gen_asend_iternext", "async_gen_asend_throw", "async_gen_athrow_send", "async_gen_athrow_iternext", "async_gen_athrow_throw"]
    statement := "The send and throw of asend and athrow awaitables move awaitables only forward (INIT, ITER, CLOSED), frame states along legal edges, and only ever set ag_closed."
    source := "AwaitableState, genobject.c:1601-1605", status := .proven
    prop := ``AsyncOpsStateEdges, thm := some ``asyncOpsStateEdges_proven
    notes := "Hypothesis: HooksLegal, as for gen-ops-state-edges." },
  { id := "gen-async-unwrap-value", pyFile := src, pyFns := ["async_gen_unwrap_value", "_PyAsyncGenValueWrapperNew"]
    statement := "async_gen_unwrap_value: on NULL it clears ag_running_async, turns no-exception into StopAsyncIteration and never clears ag_closed; a wrapped value becomes StopIteration(value) with the flag cleared; anything else passes through with no change."
    source := "genobject.c:1911-1938", status := .proven
    prop := ``AsyncGenUnwrapValue, thm := some ``asyncGenUnwrapValue_proven },
  { id := "gen-asend-error-closes", pyFile := src, pyFns := ["async_gen_asend_send", "async_gen_asend_iternext", "async_gen_asend_throw"]
    statement := "After send or throw of an asend awaitable raises, the awaitable is AWAITABLE_STATE_CLOSED."
    source := "message at genobject.c:1980: an awaited asend cannot be reused", status := .proven
    prop := ``AsendErrorCloses, thm := some ``asendErrorCloses_proven },
  { id := "gen-asend-error-clears-running", pyFile := src, pyFns := ["async_gen_asend_send", "async_gen_asend_throw"]
    statement := "An asend awaitable that passed its state checks clears ag_running_async on every path where send or throw raises."
    source := "invariant: ag_running_async is set only while an awaitable runs the generator", status := .proven
    prop := ``AsendErrorClearsRunning, thm := some ``asendErrorClearsRunning_proven },
  { id := "gen-aclose-error-closes", pyFile := src, pyFns := ["async_gen_athrow_send", "async_gen_athrow_iternext"]
    statement := "An aclose() awaitable that raises from send(None), at any step, is closed."
    source := "narrowing of gen-athrow-error-closes", status := .proven
    prop := ``AcloseErrorCloses, thm := some ``acloseErrorCloses_proven },
  { id := "gen-athrow-start-error-closes", pyFile := src, pyFns := ["async_gen_athrow_send"]
    statement := "The first step of athrow or aclose closes the awaitable and clears ag_running_async whenever it raises."
    source := "narrowing of gen-athrow-error-closes", status := .proven
    prop := ``AThrowStartErrorCloses, thm := some ``aThrowStartErrorCloses_proven },
  { id := "gen-athrow-error-closes", pyFile := src, pyFns := ["async_gen_athrow_send"]
    statement := "An athrow() or aclose() awaitable that raises from send(None), at any step, is closed."
    source := "message at genobject.c:2311; sibling paths at :1820-1822, :2458-2462", status := .refuted
    prop := ``AThrowErrorCloses, thm := some ``aThrowErrorCloses_refuted
    bug := some "bytecode-gen-athrow-awaitable-reusable" },
  { id := "gen-athrow-error-clears-running", pyFile := src, pyFns := ["async_gen_athrow_send"]
    statement := "An athrow() or aclose() awaitable that passed its state checks clears ag_running_async whenever send(None) raises."
    source := "invariant: ag_running_async is set only while an awaitable runs the generator", status := .proven
    prop := ``AThrowErrorClearsRunning, thm := some ``aThrowErrorClearsRunning_proven
    notes := "Refuted on 3.14.7 (bytecode-gen-athrow-bad-args-stuck-running): a bad argument count failed at the first send, after the flag was set. See gen-athrow-bad-args-at-creation." },
  { id := "gen-athrow-bad-args-at-creation", pyFile := src, pyFns := ["async_gen_athrow", "async_gen_athrow_new"]
    statement := "athrow() with no argument or more than three fails where the awaitable would be made, so no awaitable holds a bad argument list."
    source := "genobject.c:2604-2606", status := .proven
    prop := ``AthrowBadArgsRejected, thm := some ``athrowBadArgsRejected_proven
    notes := "Replaces gen-athrow-valid-args-clears-running, the narrowing that gen-athrow-error-clears-running needed on 3.14.7." },
  { id := "gen-athrow-throw-error-closes", pyFile := src, pyFns := ["async_gen_athrow_throw"]
    statement := "After throw on an athrow or aclose awaitable raises, the awaitable is closed, and if it passed its state checks ag_running_async is cleared, in both modes."
    source := "genobject.c:2456-2491", status := .proven
    prop := ``AThrowThrowErrorCloses, thm := some ``aThrowThrowErrorCloses_proven },
  { id := "gen-awaitable-close-idempotent", pyFile := src, pyFns := ["async_gen_asend_close", "async_gen_athrow_close"]
    statement := "If close() of an asend or athrow awaitable returns normally, closing again returns None with no effect."
    source := "genobject.c:2073-2075, :2506-2508", status := .proven
    prop := ``AwaitableCloseIdempotent, thm := some ``awaitableCloseIdempotent_proven },
  { id := "gen-awaitable-closed-terminal", pyFile := src, pyFns := ["async_gen_asend_send", "async_gen_asend_iternext", "async_gen_asend_throw", "async_gen_asend_close", "async_gen_athrow_send", "async_gen_athrow_iternext", "async_gen_athrow_throw", "async_gen_athrow_close"]
    statement := "On a closed awaitable send, next and throw raise the cannot-reuse RuntimeError and close returns None, changing nothing and never reaching the frame."
    source := "genobject.c:1978-1983, :2036-2041, :2305-2310, :2429-2434", status := .proven
    prop := ``AwaitableClosedTerminal, thm := some ``awaitableClosedTerminal_proven },
  { id := "gen-awaitable-running-exclusion", pyFile := src, pyFns := ["async_gen_asend_send", "async_gen_asend_throw", "async_gen_athrow_send", "async_gen_athrow_throw"]
    statement := "A fresh awaitable on a generator with ag_running_async set fails with the matching already-running RuntimeError (anext, aclose or athrow), closes itself and leaves the generator alone."
    source := "genobject.c:1986-1992, :2044-2050, :2321-2334, :2437-2450", status := .proven
    prop := ``AwaitableRunningExclusion, thm := some ``awaitableRunningExclusion_proven },
  { id := "gen-athrow-on-finished", pyFile := src, pyFns := ["async_gen_athrow_send", "async_gen_athrow_iternext"]
    statement := "On a finished generator, send on an open athrow or aclose awaitable closes it with StopIteration, whatever its state and argument, without touching the frame."
    source := "genobject.c:2315-2318", status := .proven
    prop := ``AthrowOnFinished, thm := some ``athrowOnFinished_proven },
  { id := "gen-athrow-on-closed", pyFile := src, pyFns := ["async_gen_athrow_send"]
    statement := "With ag_closed set on an unfinished generator (an ignored aclose()), a fresh athrow or aclose raises StopAsyncIteration without resuming it."
    source := "genobject.c:2337-2341; Doc/reference/expressions.rst agen.aclose", status := .proven
    prop := ``AthrowOnClosed, thm := some ``athrowOnClosed_proven },
  { id := "gen-async-hooks-once", pyFile := src, pyFns := ["async_gen_init_hooks"]
    statement := "async_gen_init_hooks does nothing once ag_hooks_inited is set, and firstiter runs with the flag already set, so a raising hook is not retried and a reentrant call does not run it twice."
    source := "genobject.c:1676-1680", status := .proven
    prop := ``AsyncGenHooksOnce, thm := some ``asyncGenHooksOnce_proven },
  { id := "gen-async-methods-create", pyFile := src, pyFns := ["async_gen_anext", "async_gen_asend", "async_gen_aclose", "async_gen_athrow", "async_gen_asend_new", "async_gen_athrow_new"]
    statement := "anext, asend, aclose and athrow, after the hooks, create an AWAITABLE_STATE_INIT awaitable on the generator holding exactly their argument, or NULL for anext and aclose."
    source := "genobject.c:1705-1753, :2160-2180, :2598-2621", status := .proven
    prop := ``AsyncGenMethodsCreate, thm := some ``asyncGenMethodsCreate_proven },
  { id := "gen-close-stack-bounded", pyFile := src, pyFns := ["gen_close", "gen_close_iter"]
    statement := "A fixed amount of C stack closes any generator: there is a K such that gen_close never recurses more than K levels."
    source := "invariant: no crash from pure Python at the default recursion limit", status := .refuted
    prop := ``GenCloseStackBounded, thm := some ``genCloseStackBounded_refuted
    bug := some "bytecode-gen-close-deep-chain-stack-overflow"
    notes := "The model's fuel stands for the C stack. Segfaults 3.14.7 and main from pure Python." },
  { id := "gen-throw-stack-bounded", pyFile := src, pyFns := ["_gen_throw"]
    statement := "A fixed amount of C stack serves any throw(): there is a K such that _gen_throw never recurses more than K levels."
    source := "invariant: no crash from pure Python at the default recursion limit", status := .refuted
    prop := ``GenThrowStackBounded, thm := some ``genThrowStackBounded_refuted
    bug := some "bytecode-gen-close-deep-chain-stack-overflow" },
  { id := "gen-throw-bad-arg-undelegated", pyFile := src, pyFns := ["gen_throw", "_gen_throw", "gen_set_exception"]
    statement := "With no sub-iterator, throw() of something that cannot be raised changes nothing, on every state, and is the documented TypeError, except that a running generator raises the already-executing ValueError and a finished coroutine the cannot-reuse RuntimeError, since 3.15 looks at the state first."
    source := "genobject.c:628-645, :584-591", status := .proven
    prop := ``GenThrowBadArgUndelegated, thm := some ``genThrowBadArgUndelegated_proven },
  { id := "gen-throw-bad-arg-no-effect", pyFile := src, pyFns := ["gen_throw", "_gen_throw"]
    statement := "With or without a sub-iterator, throw() of something that cannot be raised leaves the generator's state alone."
    source := "method vs equivalent method: the same call with and without delegation", status := .refuted
    prop := ``GenThrowBadArgNoEffect, thm := some ``genThrowBadArgNoEffect_refuted
    bug := some "bytecode-gen-throw-bad-arg-kills-delegator" },
  { id := "gen-throw-no-delegation", pyFile := src, pyFns := ["_gen_throw", "gen_set_exception", "gen_throw_current_exception"]
    statement := "With no sub-iterator, throw of an exception class refuses a running generator, gives a finished generator the normalized exception without running it and a finished coroutine the cannot-reuse RuntimeError, and otherwise throws the normalized exception into the frame with the generator FRAME_EXECUTING."
    source := "genobject.c:628-650, :719-725", status := .proven
    prop := ``GenThrowNoDelegation, thm := some ``genThrowNoDelegation_proven },
  { id := "gen-throw-lookup-sees-executing", pyFile := src, pyFns := ["_gen_throw"]
    statement := "All Python code _gen_throw runs for a sub-iterator runs with the delegating generator marked FRAME_EXECUTING."
    source := "genobject.c:649, before everything at :651-716", status := .proven
    prop := ``GenThrowLookupSeesExecuting, thm := some ``genThrowLookupSeesExecuting_proven
    notes := "Refuted on 3.14.7 (bytecode-gen-throw-attr-lookup-unguarded, which crashed through a throw property). 3.15 marks the generator before any of it." },
  { id := "gen-close-iter-foreign", pyFile := src, pyFns := ["gen_close_iter"]
    statement := "gen_close_iter on an object that is not a generator succeeds when the object has no close attribute, and also when looking the attribute up fails, which is reported and ignored."
    source := "genobject.c:435-440", status := .proven
    prop := ``GenCloseIterForeign, thm := some ``genCloseIterForeign_proven },
  { id := "gen-pep479-conversion", pyFile := "Python/intrinsics.c", pyFns := ["stopiteration_error"]
    statement := "stopiteration_error leaves no StopIteration, and in an async generator no StopAsyncIteration, and passes every other exception through unchanged, which is what the asserts in gen_send_ex2 rely on."
    source := "PEP 479; asserts at genobject.c:318-320; Python/intrinsics.c:141-182", status := .proven
    prop := ``Pep479Conversion, thm := some ``pep479Conversion_proven },
  { id := "gen-frame-never-raises-stopiteration", pyFile := src, pyFns := []
    statement := "A frame never ends by raising StopIteration (the assert at genobject.c:318), on the frames of the difftest's evaluator."
    source := "asserts at genobject.c:318-320", status := .refuted
    prop := ``FrameNeverRaisesStopIteration, thm := some ``frameNeverRaisesStopIteration_refuted
    bug := some "bytecode-gen-throw-created-skips-pep479"
    notes := "Duplicate of python/cpython#152685; aborts debug builds. The counterexample runs the difftest script evaluator, so it covers no CPython function." },
  { id := "gen-name-setters", pyFile := src, pyFns := ["gen_get_name", "gen_set_name", "gen_get_qualname", "gen_set_qualname"]
    statement := "__name__ and __qualname__: anything but a str, or deletion, is a TypeError and changes nothing; a str reads back and only that attribute changes."
    source := "genobject.c:848-854, :875-881", status := .proven
    prop := ``GenNameSetters, thm := some ``genNameSetters_proven },
  { id := "gen-make-coro-kinds", pyFile := src, pyFns := ["make_gen", "_Py_MakeCoro"]
    statement := "_Py_MakeCoro picks the type from the code flags, starts from a cleared frame with the function's names, and initialises the async generator flags and cr_origin."
    source := "genobject.c:1095-1162", status := .proven
    prop := ``PyMakeCoroKinds, thm := some ``pyMakeCoroKinds_proven },
  { id := "gen-cr-origin-take", pyFile := src, pyFns := ["_PyCoro_ComputeOrigin"]
    statement := "cr_origin is the innermost origin_depth frames, innermost first, and no more than the stack has."
    source := "Doc/library/sys.rst set_coroutine_origin_tracking_depth", status := .proven
    prop := ``CrOriginTake, thm := some ``crOriginTake_proven },
  { id := "gen-awaitable-iter-result", pyFile := src, pyFns := ["_PyCoro_GetAwaitableIter", "gen_is_coroutine"]
    statement := "_PyCoro_GetAwaitableIter returns a coroutine or types.coroutine generator as it is, and otherwise only an iterator that is not a coroutine."
    source := "PEP 492; genobject.c:1262-1275, :1225-1232", status := .proven
    prop := ``AwaitableIterResult, thm := some ``awaitableIterResult_proven },
  { id := "gen-finalize-branches", pyFile := src, pyFns := ["gen_finalize"]
    statement := "gen_finalize does nothing to a finished generator, only warns on an unstarted coroutine, and on an async generator with a finalizer only calls it, in each case without resuming the frame."
    source := "genobject.c:107-164", status := .proven
    prop := ``GenFinalizeBranches, thm := some ``genFinalizeBranches_proven }
]

end PyLean.Bytecode.GenObj
