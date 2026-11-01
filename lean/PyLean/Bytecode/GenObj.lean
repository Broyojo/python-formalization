import PyLean.Registry
import PyLean.Bytecode.GenObj.Legal

/-!
`Objects/genobject.c`, CPython 3.14.7: generators, coroutines, async generators.

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
  { id := "gen-send-rejected-no-effect", pyFile := src, pyFns := ["gen_send_ex2", "PyGen_am_send"]
    statement := "For every generator, coroutine or async generator, every argument and every frame evaluator: a call gen_send_ex2 rejects (non-None to a just-started object, already executing, finished) changes nothing and gives the same result under any frame evaluator, so a finished or running frame is never resumed and each state check comes before any effect."
    source := "invariant: genobject.c@3.14.7:199-239 precede the first write at :246", status := .proven
    prop := ``GenSendRejectedNoEffect, thm := some ``genSendRejectedNoEffect_proven },
  { id := "gen-already-executing", pyFile := src, pyFns := ["gen_send_ex2"]
    statement := "For every argument, gen_send_ex2 on an object in FRAME_EXECUTING raises ValueError with the message of its type (generator, coroutine, async generator already executing) and changes nothing."
    source := "Doc/reference/expressions.rst@3.14.7:784; genobject.c@3.14.7:212-222", status := .proven
    prop := ``GenAlreadyExecuting, thm := some ``genAlreadyExecuting_proven },
  { id := "gen-resume-sees-executing", pyFile := src, pyFns := ["gen_send_ex2", "gen_close", "_gen_throw"]
    statement := "Through gen_send_ex2, gen_close or _gen_throw at any delegation depth, every call of the frame evaluator sees the frame marked FRAME_EXECUTING: replacing resume by anything at all on any other state changes no result, so a FRAME_CLEARED frame is never resumed."
    source := "invariant: genobject.c@3.14.7:241-242, :257", status := .proven
    prop := ``GenResumeSeesExecuting, thm := some ``genResumeSeesExecuting_proven },
  { id := "gen-send-state-edges", pyFile := src, pyFns := ["gen_send_ex2"]
    statement := "For every object, argument and frame outcome (yielded with oparg 0 or 1, returned, raised), gen_send_ex2 moves gi_frame_state along a legal edge: CREATED or SUSPENDED* to SUSPENDED* or CLEARED, EXECUTING and CLEARED unchanged."
    source := "invariant: asserts at genobject.c@3.14.7:241-242, :262, :285", status := .proven
    prop := ``GenSendStateEdges, thm := some ``genSendStateEdges_proven },
  { id := "gen-iternext-vs-send-none", pyFile := src, pyFns := ["gen_iternext", "gen_send", "gen_send_ex"]
    statement := "On generators and coroutines, next(g) and g.send(None) agree exactly, in result and in the resulting world, for every state and every frame outcome, once a NULL with no exception is read as StopIteration."
    source := "twin paths: gen_iternext (:629-643) and gen_send (:321-325); Doc/reference/expressions.rst generator.__next__", status := .proven
    prop := ``GenIternextVsSendNone, thm := some ``genIternextVsSendNone_proven
    notes := "Precondition: not an async generator, the type assert at genobject.c:763." },
  { id := "gen-send-vs-am-send", pyFile := src, pyFns := ["gen_send", "gen_send_ex", "PyGen_am_send"]
    statement := "On generators and coroutines, gen.send(arg) is PyGen_am_send(arg) with the conversion at :301-313: same world, a yield is returned, a returned value v becomes a StopIteration carrying v, and errors are unchanged. The model does not track object identity."
    source := "twin paths: PyGen_am_send (:290-295) and gen_send_ex (:297-315)", status := .proven
    prop := ``GenSendVsAmSend, thm := some ``genSendVsAmSend_proven },
  { id := "gen-close-idempotent", pyFile := src, pyFns := ["gen_close", "gen_clear_frame"]
    statement := "For every object and frame outcome: if close() returns normally the object is finished, and closing again returns None and changes nothing."
    source := "Doc/reference/expressions.rst generator.close", status := .proven
    prop := ``GenCloseIdempotent, thm := some ``genCloseIdempotent_proven },
  { id := "gen-close-rejects-executing", pyFile := src, pyFns := ["gen_close", "is_resume", "gen_clear_frame"]
    statement := "close() on an object in FRAME_EXECUTING raises the already-executing ValueError and changes nothing."
    source := "Doc/reference/expressions.rst@3.14.7:784; invariant: a running frame is not cleared", status := .refuted
    prop := ``GenCloseRejectsExecuting, thm := some ``genCloseRejectsExecuting_refuted
    bug := some "bytecode-gen-close-clears-running-frame"
    notes := "Crashes 3.14.7 from a __del__ running at a generator's RESUME; fixed on main." },
  { id := "gen-close-rejects-executing-past-resume", pyFile := src, pyFns := ["gen_close", "is_resume"]
    statement := "The same for a frame anywhere but at a depth-1 RESUME with no unwind tools: the refuted case above is the only way close() on a running generator goes wrong."
    source := "narrowing of gen-close-rejects-executing", status := .proven
    prop := ``GenCloseRejectsExecutingPastResume, thm := some ``genCloseRejectsExecutingPastResume_proven },
  { id := "gen-close-fast-slow-agree", pyFile := src, pyFns := ["gen_close", "is_resume", "gen_clear_frame"]
    statement := "For a suspended generator at a depth-1 RESUME whose frame raises a thrown GeneratorExit unchanged, gen_close's fast path (no unwind tools) and the slow path (with tools) give the same result, None, and the same final state, FRAME_CLEARED."
    source := "fast path vs slow path, genobject.c:499-515", status := .proven
    prop := ``GenCloseFastSlowAgree, thm := some ``genCloseFastSlowAgree_proven
    notes := "The hypothesis on the frame is what depth 1 means: no handler but the outermost, whose stopiteration_error passes GeneratorExit through." },
  { id := "gen-ops-state-edges", pyFile := src, pyFns := ["gen_close", "gen_close_iter", "_gen_throw", "gen_throw"]
    statement := "gen_close and gen_throw move every generator in the world along legal edges, restore every state they bracket with FRAME_EXECUTING, and leave ag_closed and all awaitables monotone, for all arguments, frame outcomes and reentrant uses of the model from the hooks."
    source := "invariant", status := .proven
    prop := ``GenOpsStateEdges, thm := some ``genOpsStateEdges_proven
    notes := "Hypotheses: HooksLegal (Python code acts through the model; YIELD_VALUE 1 is not followed by a depth-1 RESUME; the throw attribute lookup does not touch frames) and Inv (no executing frame at a depth-1 RESUME). The two exclusions are the refuted gen-throw-lookup-sees-executing and gen-close-rejects-executing." },
  { id := "gen-async-ops-state-edges", pyFile := src, pyFns := ["async_gen_asend_send", "async_gen_asend_iternext", "async_gen_asend_throw", "async_gen_athrow_send", "async_gen_athrow_iternext", "async_gen_athrow_throw"]
    statement := "The send and throw of asend and athrow awaitables move awaitables only forward (INIT, ITER, CLOSED), frame states along legal edges, and only ever set ag_closed."
    source := "AwaitableState, genobject.c:1601-1605", status := .proven
    prop := ``AsyncOpsStateEdges, thm := some ``asyncOpsStateEdges_proven
    notes := "Hypotheses: HooksLegal and Inv, as for gen-ops-state-edges." },
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
    statement := "The first step of athrow or aclose with a well-formed argument list closes the awaitable and clears ag_running_async whenever it raises."
    source := "narrowing of gen-athrow-error-closes and gen-athrow-error-clears-running", status := .proven
    prop := ``AThrowStartErrorCloses, thm := some ``aThrowStartErrorCloses_proven },
  { id := "gen-athrow-error-closes", pyFile := src, pyFns := ["async_gen_athrow_send"]
    statement := "An athrow() or aclose() awaitable that raises from send(None), at any step, is closed."
    source := "message at genobject.c:2310; sibling paths at :1819-1821, :2269-2272", status := .refuted
    prop := ``AThrowErrorCloses, thm := some ``aThrowErrorCloses_refuted
    bug := some "bytecode-gen-athrow-awaitable-reusable" },
  { id := "gen-athrow-error-clears-running", pyFile := src, pyFns := ["async_gen_athrow_send"]
    statement := "An athrow() or aclose() awaitable that passed its state checks clears ag_running_async whenever send(None) raises."
    source := "invariant: ag_running_async is set only while an awaitable runs the generator", status := .refuted
    prop := ``AThrowErrorClearsRunning, thm := some ``aThrowErrorClearsRunning_refuted
    bug := some "bytecode-gen-athrow-bad-args-stuck-running" },
  { id := "gen-athrow-valid-args-clears-running", pyFile := src, pyFns := ["async_gen_athrow_send"]
    statement := "The same for an awaitable with a well-formed argument list, at any step: a bad argument count is the only way to leave the flag set."
    source := "narrowing of gen-athrow-error-clears-running", status := .proven
    prop := ``AThrowValidArgsClearsRunning, thm := some ``aThrowValidArgsClearsRunning_proven },
  { id := "gen-athrow-throw-error-closes", pyFile := src, pyFns := ["async_gen_athrow_throw"]
    statement := "After throw on an athrow or aclose awaitable raises, the awaitable is closed, and if it passed its state checks ag_running_async is cleared, in both modes."
    source := "genobject.c:2456-2490", status := .proven
    prop := ``AThrowThrowErrorCloses, thm := some ``aThrowThrowErrorCloses_proven },
  { id := "gen-awaitable-close-idempotent", pyFile := src, pyFns := ["async_gen_asend_close", "async_gen_athrow_close"]
    statement := "If close() of an asend or athrow awaitable returns normally, closing again returns None with no effect."
    source := "genobject.c:2072-2074, :2315-2317", status := .proven
    prop := ``AwaitableCloseIdempotent, thm := some ``awaitableCloseIdempotent_proven },
  { id := "gen-awaitable-closed-terminal", pyFile := src, pyFns := ["async_gen_asend_send", "async_gen_asend_iternext", "async_gen_asend_throw", "async_gen_asend_close", "async_gen_athrow_send", "async_gen_athrow_iternext", "async_gen_athrow_throw", "async_gen_athrow_close"]
    statement := "On a closed awaitable send, next and throw raise the cannot-reuse RuntimeError and close returns None, changing nothing and never reaching the frame."
    source := "genobject.c:1977-1982, :1839-1844, :2108-2113, :2239-2244", status := .proven
    prop := ``AwaitableClosedTerminal, thm := some ``awaitableClosedTerminal_proven },
  { id := "gen-awaitable-running-exclusion", pyFile := src, pyFns := ["async_gen_asend_send", "async_gen_asend_throw", "async_gen_athrow_send", "async_gen_athrow_throw"]
    statement := "A fresh awaitable on a generator with ag_running_async set fails with the matching already-running RuntimeError (anext, aclose or athrow), closes itself and leaves the generator alone."
    source := "genobject.c:1985-1991, :1847-1853, :2122-2135, :2247-2260", status := .proven
    prop := ``AwaitableRunningExclusion, thm := some ``awaitableRunningExclusion_proven },
  { id := "gen-athrow-on-finished", pyFile := src, pyFns := ["async_gen_athrow_send", "async_gen_athrow_iternext"]
    statement := "On a finished generator, send on an open athrow or aclose awaitable closes it with StopIteration, whatever its state and argument, without touching the frame."
    source := "genobject.c:2314-2318", status := .proven
    prop := ``AthrowOnFinished, thm := some ``athrowOnFinished_proven },
  { id := "gen-athrow-on-closed", pyFile := src, pyFns := ["async_gen_athrow_send"]
    statement := "With ag_closed set on an unfinished generator (an ignored aclose()), a fresh athrow or aclose raises StopAsyncIteration without resuming it."
    source := "genobject.c:2336-2340; Doc/reference/expressions.rst agen.aclose", status := .proven
    prop := ``AthrowOnClosed, thm := some ``athrowOnClosed_proven },
  { id := "gen-async-hooks-once", pyFile := src, pyFns := ["async_gen_init_hooks"]
    statement := "async_gen_init_hooks does nothing once ag_hooks_inited is set, and firstiter runs with the flag already set, so a raising hook is not retried and a reentrant call does not run it twice."
    source := "genobject.c:1675-1679", status := .proven
    prop := ``AsyncGenHooksOnce, thm := some ``asyncGenHooksOnce_proven },
  { id := "gen-async-methods-create", pyFile := src, pyFns := ["async_gen_anext", "async_gen_asend", "async_gen_aclose", "async_gen_athrow", "async_gen_asend_new", "async_gen_athrow_new"]
    statement := "anext, asend, aclose and athrow, after the hooks, create an AWAITABLE_STATE_INIT awaitable on the generator holding exactly their argument, or NULL for anext and aclose."
    source := "genobject.c:1705-1753, :1965-1982, :2408-2421", status := .proven
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
  { id := "gen-throw-bad-arg-undelegated", pyFile := src, pyFns := ["gen_throw", "_gen_throw"]
    statement := "With no sub-iterator, throw() of something that cannot be raised is the documented TypeError and changes nothing."
    source := "genobject.c@3.14.7:578-584", status := .proven
    prop := ``GenThrowBadArgUndelegated, thm := some ``genThrowBadArgUndelegated_proven },
  { id := "gen-throw-bad-arg-no-effect", pyFile := src, pyFns := ["gen_throw", "_gen_throw"]
    statement := "With or without a sub-iterator, throw() of something that cannot be raised leaves the generator's state alone."
    source := "method vs equivalent method: the same call with and without delegation", status := .refuted
    prop := ``GenThrowBadArgNoEffect, thm := some ``genThrowBadArgNoEffect_refuted
    bug := some "bytecode-gen-throw-bad-arg-kills-delegator" },
  { id := "gen-throw-no-delegation", pyFile := src, pyFns := ["_gen_throw"]
    statement := "With no sub-iterator, throw of an exception class is gen_send_ex with the normalized exception pending."
    source := "genobject.c@3.14.7:541-587", status := .proven
    prop := ``GenThrowNoDelegation, thm := some ``genThrowNoDelegation_proven },
  { id := "gen-throw-lookup-sees-executing", pyFile := src, pyFns := ["_gen_throw"]
    statement := "All Python code _gen_throw runs for a sub-iterator runs with the delegating generator marked FRAME_EXECUTING."
    source := "the brackets at genobject.c@3.14.7:482-485, :504-508, :526-529", status := .refuted
    prop := ``GenThrowLookupSeesExecuting, thm := some ``genThrowLookupSeesExecuting_refuted
    bug := some "bytecode-gen-throw-attr-lookup-unguarded"
    notes := "Crashes 3.14.7 through a throw property; fixed on main." },
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
    source := "genobject.c:848-854, :738-744", status := .proven
    prop := ``GenNameSetters, thm := some ``genNameSetters_proven },
  { id := "gen-make-coro-kinds", pyFile := src, pyFns := ["make_gen", "_Py_MakeCoro"]
    statement := "_Py_MakeCoro picks the type from the code flags, starts from a cleared frame with the function's names, and initialises the async generator flags and cr_origin."
    source := "genobject.c:1095-1162", status := .proven
    prop := ``PyMakeCoroKinds, thm := some ``pyMakeCoroKinds_proven },
  { id := "gen-cr-origin-take", pyFile := src, pyFns := ["compute_cr_origin"]
    statement := "cr_origin is the innermost origin_depth frames, innermost first, and no more than the stack has."
    source := "Doc/library/sys.rst set_coroutine_origin_tracking_depth", status := .proven
    prop := ``CrOriginTake, thm := some ``crOriginTake_proven },
  { id := "gen-awaitable-iter-result", pyFile := src, pyFns := ["_PyCoro_GetAwaitableIter", "gen_is_coroutine"]
    statement := "_PyCoro_GetAwaitableIter returns a coroutine or types.coroutine generator as it is, and otherwise only an iterator that is not a coroutine."
    source := "PEP 492; genobject.c:1237-1244, :1087-1088", status := .proven
    prop := ``AwaitableIterResult, thm := some ``awaitableIterResult_proven },
  { id := "gen-finalize-branches", pyFile := src, pyFns := ["_PyGen_Finalize"]
    statement := "_PyGen_Finalize does nothing to a finished generator, only warns on an unstarted coroutine, and on an async generator with a finalizer only calls it, in each case without resuming the frame."
    source := "genobject.c:112-148", status := .proven
    prop := ``GenFinalizeBranches, thm := some ``genFinalizeBranches_proven }
]

end PyLean.Bytecode.GenObj
