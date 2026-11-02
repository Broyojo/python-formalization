import PyLean.Registry
import PyLean.Bytecode.Diff
import PyLean.Bytecode.Props
import PyLean.Bytecode.Frames
import PyLean.Bytecode.FrameProps
import PyLean.Bytecode.StackEffect
import PyLean.Bytecode.IterObj
import PyLean.Bytecode.GenObj
import PyLean.Bytecode.SpecLocals
import PyLean.Bytecode.SpecToBool
import PyLean.Bytecode.SpecCompare
import PyLean.Bytecode.LawfulBuiltin
import PyLean.Bytecode.SpecCompareFloat
import PyLean.Bytecode.SpecSubscr
import PyLean.Bytecode.SpecCells

/-!
The bytecode virtual machine: `Python/bytecodes.c`, `Python/ceval.c`, `Python/intrinsics.c`,
`Objects/genobject.c`, `Objects/frameobject.c`, `Objects/iterobject.c`, `Objects/enumobject.c`,
`Objects/cellobject.c`, CPython 3.15.2.
-/

namespace PyLean.Bytecode

open PyLean.Registry

/-- Opcode names in the `opcode:NAME` form of `coverage/methods/Python__bytecodes.c.tsv`. -/
def op (n : String) : String := "opcode:" ++ n

def entries : List Entry := GenObj.entries ++ [
  { id := "bytecode-cells", pyFile := "Python/bytecodes.c"
    pyFns := [op "LOAD_DEREF", op "STORE_DEREF", op "DELETE_DEREF"]
    statement := "STORE_DEREF writes the cell and LOAD_DEREF reads back what was stored; DELETE_DEREF empties a bound cell; on an empty cell LOAD_DEREF and DELETE_DEREF raise the same exception with the stack and cell unchanged."
    source := "invariant: Python/bytecodes.c LOAD_DEREF, STORE_DEREF, DELETE_DEREF; _PyEval_FormatExcUnbound"
    status := .proven, prop := ``CellRules, thm := some ``cellRules_proven },
  { id := "bytecode-make-cell", pyFile := "Python/bytecodes.c"
    pyFns := [op "MAKE_CELL"]
    statement := "MAKE_CELL replaces the local with a new cell holding its value, which a following LOAD_DEREF reads back."
    source := "Python/bytecodes.c MAKE_CELL"
    status := .proven, prop := ``MakeCellRules, thm := some ``makeCellRules_proven },
  { id := "bytecode-build-seq", pyFile := "Python/bytecodes.c"
    pyFns := [op "BUILD_TUPLE", op "BUILD_LIST"]
    statement := "BUILD_TUPLE n and BUILD_LIST n pop their operands and push one new object holding them in push order, leaving the rest of the stack alone."
    source := "Python/bytecodes.c BUILD_TUPLE, BUILD_LIST"
    status := .proven, prop := ``BuildRules, thm := some ``buildRules_proven },
  { id := "bytecode-store-subscr-list-int", pyFile := "Python/bytecodes.c"
    pyFns := [op "STORE_SUBSCR_LIST_INT", op "_STORE_SUBSCR_LIST_INT"]
    statement := "STORE_SUBSCR_LIST_INT equals STORE_SUBSCR on every live stack, negative indices included, given list_ass_subscript."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c STORE_SUBSCR_LIST_INT (3.15 counts a negative index from the end)"
    status := .proven, prop := ``StoreSubscrListInt, thm := some ``storeSubscrListInt_proven },
  { id := "bytecode-subscr-tuple-int", pyFile := "Python/bytecodes.c"
    pyFns := [op "BINARY_OP_SUBSCR_TUPLE_INT", op "_BINARY_OP_SUBSCR_TUPLE_INT", op "_GUARD_BINARY_OP_SUBSCR_TUPLE_INT_BOUNDS", op "_GUARD_NOS_TUPLE"]
    statement := "BINARY_OP_SUBSCR_TUPLE_INT equals BINARY_OP for [] on every live stack, given tuplesubscript."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c BINARY_OP_SUBSCR_TUPLE_INT"
    status := .proven, prop := ``SubscrTupleInt, thm := some ``subscrTupleInt_proven },
  { id := "bytecode-subscr-str-int", pyFile := "Python/bytecodes.c"
    pyFns := [op "BINARY_OP_SUBSCR_STR_INT", op "_BINARY_OP_SUBSCR_STR_INT", op "_GUARD_NOS_COMPACT_ASCII", op "BINARY_OP_SUBSCR_USTR_INT", op "_BINARY_OP_SUBSCR_USTR_INT"]
    statement := "BINARY_OP_SUBSCR_STR_INT and the 3.15 BINARY_OP_SUBSCR_USTR_INT equal BINARY_OP for [] on every stack, given unicode_subscript."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c BINARY_OP_SUBSCR_STR_INT, _USTR_INT"
    status := .proven, prop := ``SubscrStrInt, thm := some ``subscrStrInt_proven },
  { id := "bytecode-compare-float", pyFile := "Python/bytecodes.c"
    pyFns := [op "COMPARE_OP_FLOAT", op "_COMPARE_OP_FLOAT"]
    statement := "COMPARE_OP_FLOAT equals COMPARE_OP on every stack for the operand the compiler emits, NaN, infinities and signed zeros included, given float_richcompare."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c:3253, :3262-3278; COMPARISON_BIT, Include/internal/pycore_code.h:523"
    status := .proven, prop := ``CompareFloat, thm := some ``compareFloat_proven },
  { id := "bytecode-compare-fused", pyFile := "Python/bytecodes.c"
    pyFns := [op "COMPARE_OP", op "_COMPARE_OP"]
    statement := "COMPARE_OP with the bool-coercion bit is COMPARE_OP without it followed by TO_BOOL, on every stack and for every object model, a raising __lt__ or __bool__ included."
    source := "compiler contract: COMPARE_OP fuses TO_BOOL (oparg & 16); Python/bytecodes.c:3232-3249"
    status := .proven, prop := ``CompareFused, thm := some ``compareFused_proven },
  { id := "bytecode-compare-int", pyFile := "Python/bytecodes.c"
    pyFns := [op "COMPARE_OP_INT", op "_COMPARE_OP_INT"]
    statement := "COMPARE_OP_INT equals COMPARE_OP on every stack for the operand the compiler emits, given long_richcompare."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c:3256, :3280-3300"
    status := .proven, prop := ``CompareInt, thm := some ``compareInt_proven },
  { id := "bytecode-compare-str", pyFile := "Python/bytecodes.c"
    pyFns := [op "COMPARE_OP_STR", op "_COMPARE_OP_STR"]
    statement := "COMPARE_OP_STR equals COMPARE_OP for == and != on every stack, given unicode_compare_eq."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c:3259, :3302-3318"
    status := .proven, prop := ``CompareStr, thm := some ``compareStr_proven },
  { id := "bytecode-to-bool-generic", pyFile := "Python/bytecodes.c"
    pyFns := [op "TO_BOOL", op "_TO_BOOL"]
    statement := "Generic TO_BOOL pushes the truth value __bool__ or __len__ gives, and when either raises it pops the value and propagates the exception, for any object model."
    source := "Python/bytecodes.c:486-511"
    status := .proven, prop := ``ToBoolGeneric, thm := some ``toBoolGeneric_proven },
  { id := "bytecode-to-bool-specialized", pyFile := "Python/bytecodes.c"
    pyFns := [op "TO_BOOL_BOOL", op "TO_BOOL_INT", op "_TO_BOOL_INT", op "TO_BOOL_NONE", op "TO_BOOL_STR", op "_TO_BOOL_STR", op "TO_BOOL_LIST", op "_TO_BOOL_LIST", op "_GUARD_TOS_LIST"]
    statement := "TO_BOOL_BOOL, _INT, _NONE, _STR and _LIST equal TO_BOOL for every value on every stack, given the builtin bool slots; TO_BOOL_STR's identity test against the empty-string singleton agreed with emptiness for all 77 constructors probed on 3.15.2 and main."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c:513-582"
    status := .proven, prop := ``ToBoolSpecialized, thm := some ``toBoolSpecialized_proven },
  { id := "bytecode-load-fast", pyFile := "Python/bytecodes.c"
    pyFns := [op "LOAD_FAST", op "LOAD_FAST_BORROW"]
    statement := "LOAD_FAST and LOAD_FAST_BORROW push the local and change nothing else, for every state."
    source := "invariant: Python/bytecodes.c:283-291"
    status := .proven, prop := ``LoadFastPushes, thm := some ``loadFastPushes_proven },
  { id := "bytecode-load-fast-check", pyFile := "Python/bytecodes.c"
    pyFns := [op "LOAD_FAST_CHECK"]
    statement := "LOAD_FAST_CHECK is LOAD_FAST on a bound local, and on an unbound one raises UnboundLocalError naming the variable with the stack and locals unchanged."
    source := "Python/bytecodes.c:271-281, UNBOUNDLOCAL_ERROR_MSG at Python/ceval_macros.h:399"
    status := .proven, prop := ``LoadFastCheckRules, thm := some ``loadFastCheckRules_proven },
  { id := "bytecode-load-clear-store", pyFile := "Python/bytecodes.c"
    pyFns := [op "LOAD_FAST_AND_CLEAR", op "STORE_FAST"]
    statement := "LOAD_FAST_AND_CLEAR pushes the local and unbinds it, and STORE_FAST then restores the state exactly, also for an unbound local."
    source := "PEP 709: comprehension inlining saves and restores a name; Python/bytecodes.c:293-296, :323-330"
    status := .proven, prop := ``LoadClearStoreRestores, thm := some ``loadClearStoreRestores_proven },
  { id := "bytecode-store-fast", pyFile := "Python/bytecodes.c"
    pyFns := [op "STORE_FAST"]
    statement := "STORE_FAST moves the top of the stack into the local, and LOAD_FAST reads back what was stored."
    source := "invariant: Python/bytecodes.c:323-330"
    status := .proven, prop := ``StoreFastRules, thm := some ``storeFastRules_proven },
  { id := "bytecode-load-superinstructions", pyFile := "Python/bytecodes.c"
    pyFns := [op "LOAD_FAST_LOAD_FAST", op "LOAD_FAST_BORROW_LOAD_FAST_BORROW"]
    statement := "A load superinstruction is the two loads it replaces, high nibble first."
    source := "compiler contract: Python/flowgraph.c insert_superinstructions; Python/bytecodes.c:298-310"
    status := .proven, prop := ``SuperinstructionsExpand, thm := some ``superinstructionsExpand_proven },
  { id := "bytecode-store-superinstructions", pyFile := "Python/bytecodes.c"
    pyFns := [op "STORE_FAST_STORE_FAST", op "STORE_FAST_LOAD_FAST"]
    statement := "A store superinstruction is the store then the second operation it replaces, including when both operands name the same local."
    source := "compiler contract: Python/bytecodes.c:336-357"
    status := .proven, prop := ``StoreSuperExpand, thm := some ``storeSuperExpand_proven },
  { id := "bytecode-delete-fast", pyFile := "Python/bytecodes.c"
    pyFns := [op "DELETE_FAST"]
    statement := "DELETE_FAST unbinds a bound local, and on an unbound one raises the same UnboundLocalError as LOAD_FAST_CHECK, with the stack unchanged."
    source := "Python/bytecodes.c:2354-2362"
    status := .proven, prop := ``DeleteFastRules, thm := some ``deleteFastRules_proven },
  { id := "bytecode-load-const", pyFile := "Python/bytecodes.c"
    pyFns := [op "LOAD_CONST", op "LOAD_SMALL_INT"]
    statement := "LOAD_CONST pushes co_consts[oparg] and LOAD_SMALL_INT pushes the int oparg."
    source := "Python/bytecodes.c:312-321"
    status := .proven, prop := ``LoadConstRules, thm := some ``loadConstRules_proven },
  { id := "bytecode-stack-drops", pyFile := "Python/bytecodes.c"
    pyFns := [op "POP_TOP", op "END_FOR", op "POP_ITER", op "END_SEND", op "PUSH_NULL"]
    statement := "POP_TOP, END_FOR and POP_ITER drop their operands, END_SEND keeps the value and drops what was below it, and PUSH_NULL then POP_TOP changes nothing."
    source := "Python/bytecodes.c:359-361, :389-407, :428-434"
    status := .proven, prop := ``StackDrops, thm := some ``stackDrops_proven },
  { id := "bytecode-copy", pyFile := "Python/bytecodes.c"
    pyFns := [op "COPY"]
    statement := "COPY n pushes a duplicate of the nth item from the top and changes nothing else."
    source := "Python/bytecodes.c:5906-5908"
    status := .proven, prop := ``CopyRules, thm := some ``copyRules_proven },
  { id := "bytecode-swap", pyFile := "Python/bytecodes.c"
    pyFns := [op "SWAP"]
    statement := "SWAP n exchanges the top with the nth item, and doing it twice changes nothing."
    source := "Python/bytecodes.c:5942-5947"
    status := .proven, prop := ``SwapRules, thm := some ``swapRules_proven },
  { id := "bytecode-jumps", pyFile := "Python/bytecodes.c"
    pyFns := [op "JUMP_FORWARD", op "JUMP_BACKWARD_NO_INTERRUPT", op "JUMP_BACKWARD"]
    statement := "Jumps move next_instr by oparg and touch nothing else, and a jump forward then back returns to the start."
    source := "Python/bytecodes.c:3494-3496, :3544-3550, :3656"
    status := .proven, prop := ``JumpRules, thm := some ``jumpRules_proven },
  { id := "bytecode-branches", pyFile := "Python/bytecodes.c"
    pyFns := [op "POP_JUMP_IF_TRUE", op "POP_JUMP_IF_FALSE", op "POP_JUMP_IF_NONE", op "POP_JUMP_IF_NOT_NONE", op "_POP_JUMP_IF_TRUE", op "_POP_JUMP_IF_FALSE", op "_IS_NONE"]
    statement := "Each conditional branch jumps exactly when its condition holds, skips a NOT_TAKEN on fall-through, and pops the value it tested."
    source := "Python/bytecodes.c:3621-3654"
    status := .proven, prop := ``BranchRules, thm := some ``branchRules_proven },
  { id := "bytecode-unary-not", pyFile := "Python/bytecodes.c"
    pyFns := [op "UNARY_NOT"]
    statement := "UNARY_NOT flips a bool, and doing it twice changes nothing."
    source := "Python/bytecodes.c:477"
    status := .proven, prop := ``UnaryNotRules, thm := some ``unaryNotRules_proven },
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
    pyFns := []
    statement := "Every opcode that completes in the same frame pops exactly _PyOpcode_num_popped(op, oparg) values and pushes _PyOpcode_num_pushed(op, oparg), leaving the rest of the stack unchanged, for every stack and oparg."
    source := "invariant: stack effect matches Include/internal/pycore_opcode_metadata.h (stack_effect / flowgraph.c)"
    status := .open, prop := ``StackEffects
    notes := "Withdrawn from proven. stackEffects_proven covers ten opcodes and reads only the (pop, push) annotation of the stk wrapper, so it holds for any body. The prop is that sample, not the statement. A real proof needs the effect of each body, including the opcodes that peek and dispatch." },
  { id := "bytecode-send-gen-recursion", pyFile := "Python/bytecodes.c"
    pyFns := [op "SEND_GEN", op "_SEND_GEN_FRAME", op "_PUSH_FRAME"]
    statement := "SEND_GEN steps as the generic SEND. It does not: the generic path runs the generator frame through _PyEval_EvalFrame (gen_send_ex2), which enters start_frame and enforces the Python recursion limit, while SEND_GEN's _PUSH_FRAME pushes the generator frame with no _CHECK_RECURSION_REMAINING, so a deep resume that the generic form stops with RecursionError proceeds."
    source := "invariant: specialized opcode refines its generic form"
    status := .refuted, prop := ``SendGenAgrees, thm := some ``sendGenAgrees_refuted
    bug := some "bytecode-push-frame-gen-recursion" }
  ,
  { id := "bytecode-call-alloc-abstract", pyFile := "Python/bytecodes.c"
    pyFns := [op "CALL_ALLOC_AND_ENTER_INIT", op "_CHECK_OBJECT", op "_ALLOCATE_OBJECT", op "_CREATE_INIT_FRAME"]
    statement := "Calling a class with a non-empty __abstractmethods__ always raises TypeError without allocating. It does not once specialized to CALL_ALLOC_AND_ENTER_INIT, which allocates with PyType_GenericAlloc and skips object_new's abstract-class check."
    source := "invariant: the specialized call refines the generic one, which reaches object_new"
    status := .refuted, prop := ``AbstractNeverAllocates, thm := some ``abstractNeverAllocates_refuted
    bug := some "bytecode-call-alloc-abstract" },
  { id := "bytecode-flineno-stack-swap", pyFile := "Objects/frameobject.c"
    pyFns := ["stack_swap", "mark_stacks", "compatible_stack", "frame_lineno_set_impl", "push_value",
              "pop_value", "top_of_stack", "peek", "pop_to_level", "compatible_kind"]
    statement := "mark_stacks's stack_swap computes a 64-bit stack. It does not: stack_swap is declared to return Kind (32-bit), truncating the stack, so a f_lineno jump analysed over a >32-bit stack (deep nesting with a SWAP) is approved wrongly and the interpreter resumes with a corrupt stack."
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
    statement := "The jump analysis never lets a jump land where a NULL on the eval stack is required to be an object. It does: LOAD_SPECIAL's self_or_null slot is modelled as Object, so a jump into a `with` body is approved and the interpreter reads a NULL as an object (segfault on 3.15.2 and main)."
    source := "invariant: f_lineno from a trace function must not corrupt the interpreter"
    status := .refuted, prop := ``FrameObj.JumpKeepsObjects, thm := some ``FrameObj.jumpKeepsObjects_refuted
    bug := some "bytecode-flineno-null-on-stack" },
  { id := "bytecode-flineno-iter-index-as-object", pyFile := "Objects/frameobject.c"
    pyFns := ["mark_stacks", "compatible_kind", "compatible_stack", "first_line_not_before",
              "frame_lineno_set_impl", "push_value", "pop_value", "top_of_stack", "peek"]
    statement := "No approved f_lineno jump keeps the second output of GET_ITER in a slot the target needs to be an object, for every function. It does: that slot holds a tagged index or NULL (Python/ceval.c:1136, :1139), mark_stacks gives it the kind Iterator, and compatible_kind lets Iterator flow into Object, so a jump from a for body to a line that resumes mid-expression lands on BUILD_LIST with the index as an operand (segfault on 3.15.2 and main; 3.14.7 had one slot there and rejected that target)."
    source := "invariant: f_lineno from a trace function must not corrupt the interpreter"
    status := .refuted, prop := ``FrameObj.JumpKeepsIterIndex, thm := some ``FrameObj.jumpKeepsIterIndex_refuted
    bug := some "bytecode-flineno-iter-index-as-object" },
  { id := "bytecode-anext-default-restarts-await", pyFile := "Objects/iterobject.c"
    pyFns := ["anextawaitable_getiter", "anextawaitable_iternext", "PyAnextAwaitable_New",
              "anextawaitable_proxy", "PyCallIter_New"]
    statement := "await anext(a, default) awaits a.__anext__() once, like await a.__anext__(). It does not when __anext__ returns a non-coroutine awaitable: anextawaitable_iternext rebuilds the iterator via __await__ on every resume, so a multi-step __await__ never finishes."
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
  { id := "bytecode-calliter-ends", pyFile := "Objects/iterobject.c"
    pyFns := ["calliter_iternext", "PyCallIter_New", "calliter_reduce"]
    statement := "iter(callable, sentinel) ends permanently on a sentinel match or StopIteration, and keeps running on any other exception, for every callable and comparison."
    source := "calliter_iternext, Objects/iterobject.c:223-254"
    status := .proven, prop := ``IterObj.CalliterEnds, thm := some ``IterObj.calliterEnds_proven },
  { id := "bytecode-enum-counts", pyFile := "Objects/enumobject.c"
    pyFns := ["enum_new_impl", "enumerate_vectorcall", "enum_next", "enum_next_long",
              "increment_longindex_lock_held"]
    statement := "enumerate(iterable, start) yields the indices start, start+1, ... for every start and length, across the Py_ssize_t fast path and the PyLong slow path and their switch at PY_SSIZE_T_MAX."
    source := "enum_next/enum_next_long, Objects/enumobject.c:199-272"
    status := .proven, prop := ``IterObj.EnumCounts, thm := some ``IterObj.enumCounts_proven },
  { id := "bytecode-cell-new", pyFile := "Objects/cellobject.c"
    pyFns := ["cell_new", "PyCell_New"]
    statement := "cell() takes at most one positional argument and no keywords."
    source := "cell_new, Objects/cellobject.c:36-53"
    status := .proven, prop := ``IterObj.CellNew, thm := some ``IterObj.cellNew_proven },
  -- Frame-switching and unwinding invariants.
  { id := "bytecode-return-value", pyFile := "Python/bytecodes.c"
    pyFns := [op "RETURN_VALUE", op "_RETURN_VALUE"]
    statement := "RETURN_VALUE pops the frame, restores the Python recursion budget, and resumes the caller at instr_ptr + return_offset with the returned value on top, for every caller stack."
    source := "RETURN_VALUE, Python/bytecodes.c:1573-1593"
    status := .proven, prop := ``ReturnValue, thm := some ``returnValue_proven },
  { id := "bytecode-unwind-to-handler", pyFile := "Python/bytecodes.c"
    pyFns := [op "RAISE_VARARGS", "get_exception_handler", "scan_back_to_entry_start", "skip_to_next_entry"]
    statement := "exception_unwind truncates the stack to the handler's recorded depth, pushes lasti if the entry says so, pushes the exception, and jumps to the handler; every value below the recorded level survives."
    source := "exception_unwind, Python/bytecodes.c:6485-6524; get_exception_handler, Python/ceval.h:457-510"
    status := .proven, prop := ``UnwindToHandler, thm := some ``unwindToHandler_proven },
  { id := "bytecode-unwind-no-handler", pyFile := "Python/bytecodes.c"
    pyFns := ["_PyEval_FrameClearAndPop", "clear_thread_frame"]
    statement := "With no handler, exception_unwind pops the frame, restores the recursion budget, and continues the search in the caller; the frame's own stack is discarded."
    source := "exception_unwind / exit_unwind, Python/bytecodes.c:6493-6577"
    status := .proven, prop := ``UnwindNoHandler, thm := some ``unwindNoHandler_proven },
  { id := "bytecode-unwind-exit", pyFile := "Python/bytecodes.c"
    pyFns := []
    statement := "With no handler in the last frame above the entry frame, _PyEval_EvalFrameDefault returns NULL with the exception set, leaving the heap as it was."
    source := "exit_unwind, Python/bytecodes.c:6543-6573"
    status := .proven, prop := ``UnwindExit, thm := some ``unwindExit_proven },
  { id := "bytecode-exc-info-nests", pyFile := "Python/bytecodes.c"
    pyFns := [op "PUSH_EXC_INFO", op "POP_EXCEPT"]
    statement := "PUSH_EXC_INFO then POP_EXCEPT restores tstate->exc_info->exc_value, so except blocks nest: the handled exception after a block is the one before it."
    source := "PUSH_EXC_INFO/POP_EXCEPT, Python/bytecodes.c:1911-1916, 3579-3592"
    status := .proven, prop := ``ExcInfoNests, thm := some ``excInfoNests_proven },
  { id := "bytecode-for-iter-exhausted", pyFile := "Python/bytecodes.c"
    pyFns := [op "FOR_ITER", op "_FOR_ITER", op "_SPECIALIZE_FOR_ITER"]
    statement := "FOR_ITER on an exhausted iterator jumps over END_FOR with iter and index_or_null left on the stack for the POP_ITER at the target, for every iterator and both forms of the slot."
    source := "_FOR_ITER, Python/bytecodes.c:3810-3821"
    status := .proven, prop := ``ForIterExhausted, thm := some ``forIterExhausted_proven },
  { id := "bytecode-for-iter-next", pyFile := "Python/bytecodes.c"
    pyFns := [op "FOR_ITER"]
    statement := "FOR_ITER with a next item writes the new index_or_null back to its slot and pushes the item above it, for every iterator."
    source := "_FOR_ITER, Python/bytecodes.c:3810-3821; _PyForIter_VirtualIteratorNext, Python/ceval.c:3709-3739"
    status := .proven, prop := ``ForIterNext, thm := some ``forIterNext_proven },
  { id := "bytecode-frame-swap-shallow", pyFile := "Objects/frameobject.c"
    pyFns := ["stack_swap", "peek"]
    statement := "stack_swap is correct while its result fits 32 bits (at most ten stack entries): there the truncating version equals the full 64-bit computation."
    source := "stack_swap, Objects/frameobject.c:1239-1249"
    status := .proven, prop := ``FrameObj.StackSwapShallow, thm := some ``FrameObj.stackSwapShallow_proven },
  { id := "bytecode-frame-first-line", pyFile := "Objects/frameobject.c"
    pyFns := ["first_line_not_before", "marklines"]
    statement := "first_line_not_before returns a line that is in the table and not before the request, or -1 when none exists."
    source := "first_line_not_before, Objects/frameobject.c:1606-1619"
    status := .proven, prop := ``FrameObj.FirstLine, thm := some ``FrameObj.firstLine_proven },
  { id := "bytecode-iter-setstate", pyFile := "Objects/iterobject.c"
    pyFns := ["iter_setstate"]
    statement := "iter(seq).__setstate__(i) never leaves a negative index and never revives an exhausted iterator, for every i."
    source := "iter_setstate, Objects/iterobject.c:127-140"
    status := .open, prop := ``IterObj.IterSetstate
    notes := "Proof did not survive; needs the arithmetic of the clamp at iterobject.c." },
  { id := "bytecode-iter-len-reduce", pyFile := "Objects/iterobject.c"
    pyFns := ["iter_len", "iter_reduce"]
    statement := "iter(seq).__length_hint__() is never negative for a live iterator, and __reduce__/__setstate__ round-trips the index."
    source := "iter_len/iter_reduce, Objects/iterobject.c:85-140"
    status := .open, prop := ``IterObj.IterLenReduce
    notes := "Proof did not survive; the statement was also ill-typed and is fixed here." },
  { id := "bytecode-anext-coroutine", pyFile := "Objects/iterobject.c"
    pyFns := ["anextawaitable_iternext", "anextawaitable_getiter"]
    statement := "For a coroutine from __anext__ (state kept in the object), await anext(a, default) drives it to completion like await a.__anext__(), when it does not raise StopAsyncIteration."
    source := "anextawaitable_iternext, Objects/iterobject.c:370-408"
    status := .open, prop := ``IterObj.AnextCoroutine
    notes := "Proof did not survive; needs induction over runAnext and runAwait. The refuted bytecode-anext-default-restarts-await is the non-coroutine case." },
  { id := "bytecode-enum-reduce", pyFile := "Objects/enumobject.c"
    pyFns := ["enum_reduce"]
    statement := "Pickling enumerate and rebuilding continues the count unbroken, in both the fast and the slow index state."
    source := "enum_reduce, Objects/enumobject.c:274-289"
    status := .open, prop := ``IterObj.EnumReduce
    notes := "Proof did not survive; needs an invariant over the enum_next fold across PY_SSIZE_T_MAX." },
  { id := "bytecode-reversed-setstate", pyFile := "Objects/enumobject.c"
    pyFns := ["reversed_setstate", "reversed_len"]
    statement := "reversed.__setstate__ clamps the index to [-1, n-1] and leaves an exhausted iterator alone; __length_hint__ is then in [0, n]."
    source := "reversed_setstate/reversed_len, Objects/enumobject.c:466-520"
    status := .open, prop := ``IterObj.RevSetstate
    notes := "Proof did not survive; needs the clamp arithmetic of reversed_setstate." },
  { id := "bytecode-yield-suspends", pyFile := "Python/bytecodes.c"
    pyFns := [op "YIELD_VALUE"]
    statement := "YIELD_VALUE sets gi_frame_state to FRAME_SUSPENDED + oparg, stores the frame with instr_ptr advanced and its stack saved, resumes the caller after the SEND/FOR_ITER, and moves the generator's handled exception back into the generator, for every state."
    source := "YIELD_VALUE, Python/bytecodes.c:1851-1891"
    status := .open, prop := ``YieldSuspends
    notes := "Proof did not survive: excInfo and prev are projections of regs, so they cannot be substituted; needs rewriting with the hypotheses instead." },
  -- frameobject stack analysis facts.,
  { id := "bytecode-frame-push-pop", pyFile := "Objects/frameobject.c"
    pyFns := ["push_value", "pop_value", "top_of_stack"]
    statement := "Below the overflow threshold, pop_value undoes push_value and top_of_stack reads the kind pushed."
    source := "push_value/pop_value/top_of_stack, Objects/frameobject.c:1207-1230"
    status := .open, prop := ``FrameObj.PushPop
    notes := "Proof did not survive: needs the shift arithmetic of push_value below the overflow threshold in core Lean." },
  { id := "bytecode-lawful-builtin", pyFile := "Python/bytecodes.c"
    pyFns := []
    statement := "The concrete object model satisfies Lawful, the laws every bytecode specialization theorem assumes, so those theorems hold of the model the difftest runs."
    source := "the hypothesis of bytecode-binary-op-*, bytecode-to-bool-specialized and bytecode-compare-*; Objects/abstract.c, Objects/longobject.c, Objects/floatobject.c, Objects/unicodeobject.c"
    status := .proven, prop := ``LawfulBuiltin, thm := some ``lawfulBuiltin_proven
    notes := "Two laws were restated to make them true: subscr needed the model's generic subscript to call PyObject_GetItem at the same depth, as _PyEval_BinaryOps[NB_SUBSCR] does, and the indexing laws now require the index to fit a Py_ssize_t, as indexSsize does." },
  { id := "bytecode-gap-str-percent", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "str % args and bytes % args with a conversion in the template format their arguments."
    source := "PyUnicode_Format, unicode_format.c:1031; _PyBytes_FormatEx, bytesobject.c:618"
    status := .open, prop := ``FormatRuns
    notes := "The model has no conversions and faults. bytecode_diff.py exclusion: str-percent-conversion. Not started." },
  { id := "bytecode-gap-float-pow-complex", pyFile := "Objects/floatobject.c"
    pyFns := []
    statement := "A negative float to a non-integer power gives a complex."
    source := "float_pow, floatobject.c:686-803"
    status := .open, prop := ``FloatPowRuns
    notes := "The machine has no complex value and faults. bytecode_diff.py exclusion: float-pow-complex." },
  { id := "bytecode-gap-huge-shift", pyFile := "Objects/longobject.c"
    pyFns := []
    statement := "A nonzero int shifted left by 2**24 or more behaves as in long_lshift."
    source := "long_lshift, longobject.c"
    status := .open, prop := ``HugeShiftRuns
    notes := "The model faults rather than allocate. bytecode_diff.py exclusion: huge-shift." },
  { id := "bytecode-gap-huge-int-pow", pyFile := "Objects/longobject.c"
    pyFns := []
    statement := "int ** int with a large result behaves as in long_pow, including MemoryError."
    source := "long_pow, longobject.c"
    status := .open, prop := ``NotYetStated
    notes := "Allocation failure is not modelled. bytecode_diff.py exclusion: huge-int-pow." },
  { id := "bytecode-gap-huge-seq-repeat", pyFile := "Objects/abstract.c"
    pyFns := []
    statement := "A sequence repeated by a count past Py_ssize_t raises OverflowError, and an unallocatable repeat raises MemoryError."
    source := "sequence_repeat, abstract.c:1147-1163"
    status := .open, prop := ``NotYetStated
    notes := "PyNumber_AsSsize_t overflow and allocation failure are not modelled. bytecode_diff.py exclusion: huge-seq-repeat." },
  { id := "bytecode-gap-is-on-immediates", pyFile := "Python/bytecodes.c"
    pyFns := []
    statement := "`is` on ints, floats and strs agrees with CPython."
    source := "IS_OP, Py_Is"
    status := .open, prop := ``NotYetStated
    notes := "Those values have no address in the machine, so equal values compare identical; CPython depends on its small-int cache, interning and constant merging. bytecode_diff.py exclusion: is-on-immediates." },
  { id := "bytecode-gap-set-iteration-order", pyFile := "Objects/setobject.c"
    pyFns := []
    statement := "Set iteration order agrees with CPython."
    source := "set_next, setobject.c"
    status := .open, prop := ``NotYetStated
    notes := "The model keeps insertion order, not the hash table. bytecode_diff.py exclusion: set-iteration-order." },
  { id := "bytecode-gap-refcount-finalizers", pyFile := "Objects/genobject.c"
    pyFns := []
    statement := "Finalizers run when CPython runs them."
    source := "_PyGen_Finalize; reference counting"
    status := .open, prop := ``NotYetStated
    notes := "The machine has no reference counts. bytecode_diff.py exclusion: refcount-finalizer-order." }
]

end PyLean.Bytecode
