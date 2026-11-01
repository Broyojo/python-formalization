import PyLean.Registry
import PyLean.Bytecode.Diff
import PyLean.Bytecode.Props
import PyLean.Bytecode.SpecMore
import PyLean.Bytecode.Frames
import PyLean.Bytecode.FrameProps
import PyLean.Bytecode.StackEffect
import PyLean.Bytecode.IterObj

/-!
The bytecode virtual machine: `Python/bytecodes.c`, `Python/ceval.c`, `Python/intrinsics.c`,
`Objects/genobject.c`, `Objects/frameobject.c`, `Objects/iterobject.c`, `Objects/enumobject.c`,
`Objects/cellobject.c`, CPython 3.14.7.
-/

namespace PyLean.Bytecode

open PyLean.Registry

/-- Opcode names in the `opcode:NAME` form of `coverage/methods/Python__bytecodes.c.tsv`. -/
def op (n : String) : String := "opcode:" ++ n

def entries : List Entry := [
  -- Specialized binary operators equal their generic form, over all stacks and all lawful models.
  { id := "bytecode-binary-op-add-int", pyFile := "Python/bytecodes.c"
    pyFns := [op "BINARY_OP_ADD_INT", op "_BINARY_OP_ADD_INT", op "_GUARD_TOS_INT", op "_GUARD_NOS_INT",
              op "BINARY_OP", op "_BINARY_OP", op "_SPECIALIZE_BINARY_OP"]
    statement := "For every stack and every object model with the builtin int-add slot, BINARY_OP_ADD_INT steps exactly as the generic BINARY_OP (oparg NB_ADD or NB_INPLACE_ADD)."
    source := "invariant: specialized opcode refines its generic form (adaptive interpreter contract)"
    status := .proven, prop := ``BinaryAddInt, thm := some ``binaryAddInt_proven },
  { id := "bytecode-binary-op-sub-int", pyFile := "Python/bytecodes.c"
    pyFns := [op "BINARY_OP_SUBTRACT_INT", op "_BINARY_OP_SUBTRACT_INT"]
    statement := "BINARY_OP_SUBTRACT_INT steps as BINARY_OP for every stack and lawful model (oparg NB_SUBTRACT or NB_INPLACE_SUBTRACT)."
    source := "invariant: specialized opcode refines its generic form"
    status := .proven, prop := ``BinarySubInt, thm := some ``binarySubInt_proven },
  { id := "bytecode-binary-op-mul-int", pyFile := "Python/bytecodes.c"
    pyFns := [op "BINARY_OP_MULTIPLY_INT", op "_BINARY_OP_MULTIPLY_INT"]
    statement := "BINARY_OP_MULTIPLY_INT steps as BINARY_OP for every stack and lawful model."
    source := "invariant: specialized opcode refines its generic form"
    status := .proven, prop := ``BinaryMulInt, thm := some ``binaryMulInt_proven },
  { id := "bytecode-binary-op-add-float", pyFile := "Python/bytecodes.c"
    pyFns := [op "BINARY_OP_ADD_FLOAT", op "_BINARY_OP_ADD_FLOAT", op "_GUARD_TOS_FLOAT", op "_GUARD_NOS_FLOAT"]
    statement := "BINARY_OP_ADD_FLOAT steps as BINARY_OP for every stack and lawful model."
    source := "invariant: specialized opcode refines its generic form"
    status := .proven, prop := ``BinaryAddFloat, thm := some ``binaryAddFloat_proven },
  { id := "bytecode-binary-op-sub-float", pyFile := "Python/bytecodes.c"
    pyFns := [op "BINARY_OP_SUBTRACT_FLOAT", op "_BINARY_OP_SUBTRACT_FLOAT"]
    statement := "BINARY_OP_SUBTRACT_FLOAT steps as BINARY_OP for every stack and lawful model."
    source := "invariant: specialized opcode refines its generic form"
    status := .proven, prop := ``BinarySubFloat, thm := some ``binarySubFloat_proven },
  { id := "bytecode-binary-op-mul-float", pyFile := "Python/bytecodes.c"
    pyFns := [op "BINARY_OP_MULTIPLY_FLOAT", op "_BINARY_OP_MULTIPLY_FLOAT"]
    statement := "BINARY_OP_MULTIPLY_FLOAT steps as BINARY_OP for every stack and lawful model."
    source := "invariant: specialized opcode refines its generic form"
    status := .proven, prop := ``BinaryMulFloat, thm := some ``binaryMulFloat_proven },
  { id := "bytecode-binary-op-add-unicode", pyFile := "Python/bytecodes.c"
    pyFns := [op "BINARY_OP_ADD_UNICODE", op "_BINARY_OP_ADD_UNICODE", op "_GUARD_TOS_UNICODE", op "_GUARD_NOS_UNICODE"]
    statement := "BINARY_OP_ADD_UNICODE steps as BINARY_OP for every stack and lawful model."
    source := "invariant: specialized opcode refines its generic form"
    status := .proven, prop := ``BinaryAddUnicode, thm := some ``binaryAddUnicode_proven },
  { id := "bytecode-binary-op-subscr-list-int", pyFile := "Python/bytecodes.c"
    pyFns := [op "BINARY_OP_SUBSCR_LIST_INT", op "_BINARY_OP_SUBSCR_LIST_INT"]
    statement := "For every stack of live values and every lawful model, BINARY_OP_SUBSCR_LIST_INT steps as BINARY_OP (NB_SUBSCR) for any index, including negative, out-of-range and huge ints."
    source := "invariant: specialized opcode refines its generic form"
    status := .proven, prop := ``SubscrListInt, thm := some ``subscrListInt_proven },
  -- Stack effects against the generated metadata.
  { id := "bytecode-stack-effects", pyFile := "Python/bytecodes.c"
    pyFns := [op "LOAD_FAST", op "STORE_FAST", op "POP_TOP", op "COPY", op "SWAP", op "BUILD_TUPLE",
              op "BUILD_LIST", op "BUILD_MAP", op "LIST_APPEND", op "UNPACK_SEQUENCE", op "UNPACK_EX",
              op "LOAD_GLOBAL", op "LOAD_ATTR", op "CALL", op "COMPARE_OP", op "IS_OP", op "CONTAINS_OP"]
    statement := "Every opcode that completes in the same frame pops exactly _PyOpcode_num_popped(op, oparg) values and pushes _PyOpcode_num_pushed(op, oparg), leaving the rest of the stack unchanged, for all stacks and args. Excludes the two super-instructions (CALL_LIST_APPEND, BINARY_OP_INPLACE_ADD_UNICODE), the frame-leaving opcodes, and the peek-and-dispatch opcodes (FOR_ITER, SEND, WITH_EXCEPT_START, RERAISE), noted in StackEffect.lean."
    source := "invariant: stack effect matches Include/internal/pycore_opcode_metadata.h (stack_effect / flowgraph.c)"
    status := .proven, prop := ``StackEffects, thm := some ``stackEffects_proven },
  { id := "bytecode-instrumented-plain", pyFile := "Python/bytecodes.c"
    pyFns := [op "INSTRUMENTED_END_SEND", op "INSTRUMENTED_FOR_ITER", op "INSTRUMENTED_RETURN_VALUE",
              op "INSTRUMENTED_JUMP_FORWARD", op "INSTRUMENTED_POP_JUMP_IF_TRUE",
              op "INSTRUMENTED_POP_JUMP_IF_FALSE", op "INSTRUMENTED_POP_JUMP_IF_NONE",
              op "INSTRUMENTED_POP_JUMP_IF_NOT_NONE"]
    statement := "With no monitoring tool registered, each INSTRUMENTED_* opcode steps exactly as its plain counterpart."
    source := "invariant: instrumentation is identity without a registered callback"
    status := .proven, prop := ``InstrumentedPlain, thm := some ``instrumentedPlain_proven },
  { id := "bytecode-plain-families", pyFile := "Python/bytecodes.c"
    pyFns := [op "NOT_TAKEN", op "RESUME_CHECK", op "LOAD_CONST_MORTAL", op "LOAD_CONST_IMMORTAL",
              op "LOAD_FAST_BORROW", op "POP_ITER", op "JUMP_BACKWARD_NO_JIT", op "RESUME",
              op "LOAD_CONST", op "NOP", op "JUMP_BACKWARD"]
    statement := "Each form the interpreter quickens to (RESUME_CHECK, LOAD_CONST_MORTAL, ...) steps exactly as the opcode it replaces."
    source := "invariant: quickening preserves behaviour"
    status := .proven, prop := ``PlainFamilies, thm := some ``plainFamilies_proven },
  -- Refutations: specialization and interpreter bugs.
  { id := "bytecode-send-gen-recursion", pyFile := "Python/bytecodes.c"
    pyFns := [op "SEND_GEN", op "_SEND_GEN_FRAME", op "_PUSH_FRAME", op "FOR_ITER_GEN", op "_FOR_ITER_GEN_FRAME"]
    statement := "SEND_GEN steps as the generic SEND. It does not: the generic path runs the generator frame through _PyEval_EvalFrame (gen_send_ex2), which enters start_frame and enforces the Python recursion limit, while SEND_GEN's _PUSH_FRAME pushes the generator frame with no _CHECK_RECURSION_REMAINING, so a deep resume that the generic form stops with RecursionError proceeds."
    source := "invariant: specialized opcode refines its generic form"
    status := .refuted, prop := ``SendGenAgrees, thm := some ``sendGenAgrees_refuted
    bug := some "bytecode-push-frame-gen-recursion" }
  ,
  { id := "bytecode-call-alloc-abstract", pyFile := "Python/bytecodes.c"
    pyFns := [op "CALL_ALLOC_AND_ENTER_INIT", op "_CHECK_AND_ALLOCATE_OBJECT", op "_CREATE_INIT_FRAME"]
    statement := "Calling a class with a non-empty __abstractmethods__ always raises TypeError without allocating. It does not once specialized to CALL_ALLOC_AND_ENTER_INIT, which allocates with PyType_GenericAlloc and skips object_new's abstract-class check."
    source := "invariant: the specialized call refines the generic one, which reaches object_new"
    status := .refuted, prop := ``AbstractNeverAllocates, thm := some ``abstractNeverAllocates_refuted
    bug := some "bytecode-call-alloc-abstract" },
  { id := "bytecode-flineno-stack-swap", pyFile := "Objects/frameobject.c"
    pyFns := ["stack_swap", "mark_stacks", "compatible_stack", "frame_lineno_set_impl", "push_value",
              "pop_value", "top_of_stack", "peek", "pop_to_level", "compatible_kind"]
    statement := "mark_stacks's stack_swap computes a 64-bit stack. It does not: stack_swap is declared to return Kind (32-bit), truncating the stack, so a f_lineno jump analysed over a >32-bit stack (deep nesting with a SWAP) is approved wrongly and the interpreter resumes with a corrupt stack (TypeError on 3.14.7, segfault on main)."
    source := "invariant: f_lineno from a trace function must not corrupt the interpreter"
    status := .refuted, prop := ``FrameObj.StackSwapKeepsStack, thm := some ``FrameObj.stackSwapKeepsStack_refuted
    bug := some "bytecode-flineno-stack-swap-truncation" },
  { id := "bytecode-flineno-swap-overflow", pyFile := "Objects/frameobject.c"
    pyFns := ["stack_swap"]
    statement := "An OVERFLOWED stack stays OVERFLOWED across a SWAP in the jump analysis. It does not: stack_swap's 32-bit truncation turns OVERFLOWED (-1) into a positive stack of invalid kinds, losing the 'too deep to analyze' marker."
    source := "invariant: OVERFLOWED is absorbing (push_value/pop_value preserve it)"
    status := .refuted, prop := ``FrameObj.SwapKeepsOverflowed, thm := some ``FrameObj.swapKeepsOverflowed_refuted
    bug := some "bytecode-flineno-stack-swap-truncation" },
  { id := "bytecode-flineno-null-on-stack", pyFile := "Objects/frameobject.c"
    pyFns := ["mark_stacks", "compatible_stack", "frame_lineno_set_impl"]
    statement := "The jump analysis never lets a jump land where a NULL on the eval stack is required to be an object. It does: LOAD_SPECIAL's self_or_null slot is modelled as Object, so a jump into a `with` body is approved and the interpreter reads a NULL as an object (segfault on 3.14.7 and main)."
    source := "invariant: f_lineno from a trace function must not corrupt the interpreter"
    status := .refuted, prop := ``FrameObj.JumpKeepsObjects, thm := some ``FrameObj.jumpKeepsObjects_refuted
    bug := some "bytecode-flineno-null-on-stack" },
  { id := "bytecode-anext-default-restarts-await", pyFile := "Objects/iterobject.c"
    pyFns := ["anextawaitable_getiter", "anextawaitable_iternext", "PyAnextAwaitable_New",
              "anextawaitable_proxy", "PyCallIter_New"]
    statement := "await anext(a, default) awaits a.__anext__() once, like await a.__anext__(). It does not when __anext__ returns a non-coroutine awaitable: anextawaitable_iternext rebuilds the iterator via __await__ on every resume, so a multi-step __await__ never finishes (3.14.7; fixed on main)."
    source := "Doc/library/functions.rst: anext returns the next item, or default if exhausted"
    status := .refuted, prop := ``IterObj.AnextAwaitsOnce, thm := some ``IterObj.anextAwaitsOnce_refuted
    bug := some "bytecode-anext-default-restarts-await" },
  -- iterobject / enumobject / cellobject properties.
  { id := "bytecode-iter-exhausted-sticky", pyFile := "Objects/iterobject.c"
    pyFns := ["iter_iternext", "PySeqIter_New"]
    statement := "Once iter(seq) is exhausted (it_seq == NULL) it returns NULL without calling __getitem__ again, for every sequence."
    source := "iter_iternext, Objects/iterobject.c:52-83"
    status := .proven, prop := ``IterObj.IterExhaustedSticky, thm := some ``IterObj.iterExhaustedSticky_proven },
  { id := "bytecode-iter-step", pyFile := "Objects/iterobject.c"
    pyFns := ["iter_iternext"]
    statement := "iter(seq).__next__() advances the index by one on success, stops permanently on IndexError or StopIteration, and leaves the iterator unchanged (retryable) on any other exception, for every __getitem__."
    source := "iter_iternext, Objects/iterobject.c:52-83"
    status := .proven, prop := ``IterObj.IterStep, thm := some ``IterObj.iterStep_proven },
  { id := "bytecode-iter-setstate", pyFile := "Objects/iterobject.c"
    pyFns := ["iter_setstate"]
    statement := "iter(seq).__setstate__(i) never leaves a negative index and never revives an exhausted iterator, for every i."
    source := "iter_setstate, Objects/iterobject.c:127-140"
    status := .proven, prop := ``IterObj.IterSetstate, thm := some ``IterObj.iterSetstate_proven },
  { id := "bytecode-iter-len-reduce", pyFile := "Objects/iterobject.c"
    pyFns := ["iter_len", "iter_reduce"]
    statement := "iter(seq).__length_hint__() is never negative for a live iterator, and __reduce__/__setstate__ round-trips the index."
    source := "iter_len/iter_reduce, Objects/iterobject.c:85-140"
    status := .proven, prop := ``IterObj.IterLenReduce, thm := some ``IterObj.iterLenReduce_proven },
  { id := "bytecode-calliter-ends", pyFile := "Objects/iterobject.c"
    pyFns := ["calliter_iternext", "PyCallIter_New", "calliter_reduce"]
    statement := "iter(callable, sentinel) ends permanently on a sentinel match or StopIteration, and keeps running on any other exception, for every callable and comparison."
    source := "calliter_iternext, Objects/iterobject.c:223-254"
    status := .proven, prop := ``IterObj.CalliterEnds, thm := some ``IterObj.calliterEnds_proven },
  { id := "bytecode-anext-coroutine", pyFile := "Objects/iterobject.c"
    pyFns := ["anextawaitable_iternext", "anextawaitable_getiter"]
    statement := "For a coroutine from __anext__ (state kept in the object), await anext(a, default) drives it to completion like await a.__anext__(), when it does not raise StopAsyncIteration."
    source := "anextawaitable_iternext, Objects/iterobject.c:369-407"
    status := .proven, prop := ``IterObj.AnextCoroutine, thm := some ``IterObj.anextCoroutine_proven },
  { id := "bytecode-enum-counts", pyFile := "Objects/enumobject.c"
    pyFns := ["enum_new_impl", "enumerate_vectorcall", "enum_next", "enum_next_long",
              "increment_longindex_lock_held"]
    statement := "enumerate(iterable, start) yields the indices start, start+1, ... for every start and length, across the Py_ssize_t fast path and the PyLong slow path and their switch at PY_SSIZE_T_MAX."
    source := "enum_next/enum_next_long, Objects/enumobject.c:197-286"
    status := .proven, prop := ``IterObj.EnumCounts, thm := some ``IterObj.enumCounts_proven },
  { id := "bytecode-enum-reduce", pyFile := "Objects/enumobject.c"
    pyFns := ["enum_reduce"]
    statement := "Pickling enumerate and rebuilding continues the count unbroken, in both the fast and the slow index state."
    source := "enum_reduce, Objects/enumobject.c:288-303"
    status := .proven, prop := ``IterObj.EnumReduce, thm := some ``IterObj.enumReduce_proven },
  { id := "bytecode-enum-args", pyFile := "Objects/enumobject.c"
    pyFns := ["enumerate_vectorcall", "check_keyword"]
    statement := "enumerate binds its iterable and start arguments the same way however they are spelled positionally or by keyword."
    source := "enumerate_vectorcall, Objects/enumobject.c:103-153"
    status := .proven, prop := ``IterObj.EnumArgs, thm := some ``IterObj.enumArgs_proven },
  { id := "bytecode-reversed-yields", pyFile := "Objects/enumobject.c"
    pyFns := ["reversed_new_impl", "reversed_vectorcall", "reversed_next"]
    statement := "reversed(seq) yields the sequence back to front, for every list."
    source := "reversed_next, Objects/enumobject.c:456-478"
    status := .proven, prop := ``IterObj.RevYieldsReversed, thm := some ``IterObj.revYieldsReversed_proven },
  { id := "bytecode-reversed-setstate", pyFile := "Objects/enumobject.c"
    pyFns := ["reversed_setstate", "reversed_len"]
    statement := "reversed.__setstate__ clamps the index to [-1, n-1] and leaves an exhausted iterator alone; __length_hint__ is then in [0, n]."
    source := "reversed_setstate/reversed_len, Objects/enumobject.c:480-534"
    status := .proven, prop := ``IterObj.RevSetstate, thm := some ``IterObj.revSetstate_proven },
  { id := "bytecode-cell-order", pyFile := "Objects/cellobject.c"
    pyFns := ["cell_richcompare", "cell_compare_impl"]
    statement := "An empty cell sorts before every full cell, two empty cells compare equal, and two full cells compare by contents, for every element comparison."
    source := "cell_compare_impl, Objects/cellobject.c:85-115"
    status := .proven, prop := ``IterObj.CellOrder, thm := some ``IterObj.cellOrder_proven },
  { id := "bytecode-cell-contents", pyFile := "Objects/cellobject.c"
    pyFns := ["cell_get_contents", "cell_set_contents", "PyCell_Get", "PyCell_Set"]
    statement := "cell.cell_contents reads back what was stored, an empty cell raises ValueError, and del empties the cell."
    source := "cell_get_contents/cell_set_contents, Objects/cellobject.c:146-165"
    status := .proven, prop := ``IterObj.CellContents, thm := some ``IterObj.cellContents_proven },
  { id := "bytecode-cell-new", pyFile := "Objects/cellobject.c"
    pyFns := ["cell_new", "PyCell_New"]
    statement := "cell() takes at most one positional argument and no keywords."
    source := "cell_new, Objects/cellobject.c:36-53"
    status := .proven, prop := ``IterObj.CellNew, thm := some ``IterObj.cellNew_proven },
  -- Frame-switching and unwinding invariants.
  { id := "bytecode-return-value", pyFile := "Python/bytecodes.c"
    pyFns := [op "RETURN_VALUE"]
    statement := "RETURN_VALUE pops the frame, restores the Python recursion budget, and resumes the caller at instr_ptr + return_offset with the returned value on top, for every caller stack."
    source := "RETURN_VALUE, Python/bytecodes.c:1202-1217"
    status := .proven, prop := ``ReturnValue, thm := some ``returnValue_proven },
  { id := "bytecode-unwind-to-handler", pyFile := "Python/bytecodes.c"
    pyFns := [op "RAISE_VARARGS", "get_exception_handler", "scan_back_to_entry_start", "skip_to_next_entry"]
    statement := "exception_unwind truncates the stack to the handler's recorded depth, pushes lasti if the entry says so, pushes the exception, and jumps to the handler; every value below the recorded level survives."
    source := "exception_unwind, Python/bytecodes.c:5424-5460; get_exception_handler, Python/ceval.c:1630-1678"
    status := .proven, prop := ``UnwindToHandler, thm := some ``unwindToHandler_proven },
  { id := "bytecode-unwind-no-handler", pyFile := "Python/bytecodes.c"
    pyFns := ["_PyEval_FrameClearAndPop", "clear_thread_frame"]
    statement := "With no handler, exception_unwind pops the frame, restores the recursion budget, and continues the search in the caller; the frame's own stack is discarded."
    source := "exception_unwind / exit_unwind, Python/bytecodes.c:5429-5507"
    status := .proven, prop := ``UnwindNoHandler, thm := some ``unwindNoHandler_proven },
  { id := "bytecode-unwind-exit", pyFile := "Python/bytecodes.c"
    pyFns := []
    statement := "With no handler in the last frame above the entry frame, _PyEval_EvalFrameDefault returns NULL with the exception set, leaving the heap as it was."
    source := "exit_unwind, Python/bytecodes.c:5479-5503"
    status := .proven, prop := ``UnwindExit, thm := some ``unwindExit_proven },
  { id := "bytecode-exc-info-nests", pyFile := "Python/bytecodes.c"
    pyFns := [op "PUSH_EXC_INFO", op "POP_EXCEPT"]
    statement := "PUSH_EXC_INFO then POP_EXCEPT restores tstate->exc_info->exc_value, so except blocks nest: the handled exception after a block is the one before it."
    source := "PUSH_EXC_INFO/POP_EXCEPT, Python/bytecodes.c:1421-1426, 3579-3592"
    status := .proven, prop := ``ExcInfoNests, thm := some ``excInfoNests_proven },
  { id := "bytecode-for-iter-exhausted", pyFile := "Python/bytecodes.c"
    pyFns := [op "FOR_ITER", op "_FOR_ITER", op "_SPECIALIZE_FOR_ITER"]
    statement := "FOR_ITER on an exhausted iterator jumps over END_FOR with only the iterator left on the stack (the folded END_FOR/POP_ITER), for every iterator."
    source := "_FOR_ITER, Python/bytecodes.c:3146-3175"
    status := .proven, prop := ``ForIterExhausted, thm := some ``forIterExhausted_proven },
  { id := "bytecode-for-iter-next", pyFile := "Python/bytecodes.c"
    pyFns := [op "FOR_ITER"]
    statement := "FOR_ITER with a next item pushes it above the iterator, for every iterator."
    source := "_FOR_ITER, Python/bytecodes.c:3146-3175"
    status := .proven, prop := ``ForIterNext, thm := some ``forIterNext_proven },
  { id := "bytecode-yield-suspends", pyFile := "Python/bytecodes.c"
    pyFns := [op "YIELD_VALUE"]
    statement := "YIELD_VALUE sets gi_frame_state to FRAME_SUSPENDED + oparg, stores the frame with instr_ptr advanced and its stack saved, resumes the caller after the SEND/FOR_ITER, and moves the generator's handled exception back into the generator, for every state."
    source := "YIELD_VALUE, Python/bytecodes.c:1370-1402"
    status := .proven, prop := ``YieldSuspends, thm := some ``yieldSuspends_proven },
  -- frameobject stack analysis facts.
  { id := "bytecode-frame-compatible-kind", pyFile := "Objects/frameobject.c"
    pyFns := ["compatible_kind"]
    statement := "compatible_kind: nothing is compatible with kind 0, NULL is never compatible with Object, anything is compatible with Null, and otherwise the kinds must match."
    source := "compatible_kind, Objects/frameobject.c:1175-1187"
    status := .proven, prop := ``FrameObj.CompatibleKind, thm := some ``FrameObj.compatibleKind_proven },
  { id := "bytecode-frame-push-pop", pyFile := "Objects/frameobject.c"
    pyFns := ["push_value", "pop_value", "top_of_stack"]
    statement := "Below the overflow threshold, pop_value undoes push_value and top_of_stack reads the kind pushed."
    source := "push_value/pop_value/top_of_stack, Objects/frameobject.c:1199-1222"
    status := .proven, prop := ``FrameObj.PushPop, thm := some ``FrameObj.pushPop_proven },
  { id := "bytecode-frame-overflowed", pyFile := "Objects/frameobject.c"
    pyFns := ["push_value", "pop_value"]
    statement := "An OVERFLOWED stack stays OVERFLOWED under push_value and pop_value."
    source := "push_value/pop_value, Objects/frameobject.c:1199-1214"
    status := .proven, prop := ``FrameObj.Overflowed, thm := some ``FrameObj.overflowed_proven },
  { id := "bytecode-frame-swap-shallow", pyFile := "Objects/frameobject.c"
    pyFns := ["stack_swap", "peek"]
    statement := "stack_swap is correct while its result fits 32 bits (at most ten stack entries): there the truncating version equals the full 64-bit computation."
    source := "stack_swap, Objects/frameobject.c:1231-1241"
    status := .proven, prop := ``FrameObj.StackSwapShallow, thm := some ``FrameObj.stackSwapShallow_proven },
  { id := "bytecode-frame-first-line", pyFile := "Objects/frameobject.c"
    pyFns := ["first_line_not_before", "marklines"]
    statement := "first_line_not_before returns a line that is in the table and not before the request, or -1 when none exists."
    source := "first_line_not_before, Objects/frameobject.c:1594-1607"
    status := .proven, prop := ``FrameObj.FirstLine, thm := some ``FrameObj.firstLine_proven }
]

end PyLean.Bytecode
