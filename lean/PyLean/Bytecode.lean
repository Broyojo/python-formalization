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
import PyLean.Bytecode.SpecForIter
import PyLean.Bytecode.SpecDict
import PyLean.Bytecode.GenericProps
import PyLean.Bytecode.SpecJumps
import PyLean.Bytecode.SpecUnpack
import PyLean.Bytecode.SpecBuild
import PyLean.Bytecode.SpecMisc
import PyLean.Bytecode.SpecCall
import PyLean.Bytecode.SpecCallGeneric
import PyLean.Bytecode.SpecLoadAttr
import PyLean.Bytecode.AttrRecursion
import PyLean.Bytecode.SpecImport
import PyLean.Bytecode.SpecCallPy
import PyLean.Bytecode.SpecCallPyFast
import PyLean.Bytecode.SpecExcMatch
import PyLean.Bytecode.SpecAsync

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
  { id := "bytecode-load-name", pyFile := "Python/bytecodes.c"
    pyFns := []
    statement := "LOAD_NAME looks in the locals, then the globals, then the builtins, and pushes the value, or raises NameError naming it with the stack unchanged; for exact-dict namespaces."
    source := "Python/bytecodes.c LOAD_NAME; _PyEval_LoadName, Python/ceval.c"
    status := .proven, prop := ``LoadNameRules, thm := some ``loadNameRules_proven
    notes := "Credits no row: the non-dict namespace path (a metaclass __prepare__ mapping) and the no-locals SystemError are part of the body and not stated yet." },
  { id := "bytecode-name-roundtrip", pyFile := "Python/bytecodes.c"
    pyFns := []
    statement := "STORE_NAME name then LOAD_NAME name pushes the stored value, on exact-dict locals."
    source := "invariant: Python/bytecodes.c STORE_NAME, LOAD_NAME"
    status := .proven, prop := ``NameRoundTrip, thm := some ``nameRoundTrip_proven
    notes := "Credits no row, for the same reason as bytecode-load-name." },
  { id := "bytecode-global-roundtrip", pyFile := "Python/bytecodes.c"
    pyFns := [op "STORE_GLOBAL"]
    statement := "STORE_GLOBAL name then LOAD_GLOBAL name pushes the stored value and nothing else, on exact-dict globals; every other name keeps its value."
    source := "invariant: Python/bytecodes.c STORE_GLOBAL, _LOAD_GLOBAL; PyDict_SetItem then PyDict_GetItemRef on a str key"
    status := .proven, prop := ``GlobalRoundTrip, thm := some ``globalRoundTrip_proven },
  { id := "bytecode-load-global", pyFile := "Python/bytecodes.c"
    pyFns := [op "LOAD_GLOBAL", op "_LOAD_GLOBAL", op "_PUSH_NULL_CONDITIONAL"]
    statement := "LOAD_GLOBAL looks the name up in the globals then the builtins with PyMapping_GetOptionalItem (any mapping, a dict subclass from exec included) and pushes the value, with a NULL after it for the call form; when neither has the name it raises NameError with the stack unchanged, and, when no exception is being handled (the case NameErrorName states), that NameError carries the name in .name (UnboundLocalError does not); a raising lookup propagates with the stack unchanged."
    source := "Python/bytecodes.c:2270-2289; _PyEval_LoadGlobalStackRef, Python/ceval.c:3597-3630; _PyEval_FormatExcCheckArg, Python/ceval.c:3449-3475"
    status := .proven, prop := ``LoadGlobalFull, thm := some ``loadGlobalFull_proven },
  { id := "bytecode-attr-dispatch", pyFile := "Python/bytecodes.c"
    pyFns := [op "STORE_ATTR", op "_STORE_ATTR", op "DELETE_ATTR", op "LOAD_ATTR", op "_LOAD_ATTR"]
    statement := "STORE_ATTR, DELETE_ATTR and LOAD_ATTR take the name from co_names, call PyObject_SetAttr, PyObject_DelAttr and getattr (or the method form with self_or_null on top), and pop their operands on success and failure, for any object model."
    source := "Python/bytecodes.c _STORE_ATTR, DELETE_ATTR, _LOAD_ATTR"
    status := .proven, prop := ``AttrRules, thm := some ``attrRules_proven },
  { id := "bytecode-dispatch", pyFile := "Python/bytecodes.c"
    pyFns := [op "CONTAINS_OP", op "_CONTAINS_OP", op "STORE_SUBSCR", op "_STORE_SUBSCR", op "DELETE_SUBSCR"]
    statement := "CONTAINS_OP asks the container (PySequence_Contains(c, x)) and inverts for not in, keeping both operands when the lookup raises; STORE_SUBSCR and DELETE_SUBSCR call PyObject_SetItem(c, k, v) and PyObject_DelItem(c, k) and pop their operands either way; for any object model."
    source := "Python/bytecodes.c _CONTAINS_OP (ERROR_NO_POP), _STORE_SUBSCR, DELETE_SUBSCR"
    status := .proven, prop := ``DispatchRules, thm := some ``dispatchRules_proven },
  { id := "bytecode-list-append", pyFile := "Python/bytecodes.c"
    pyFns := [op "LIST_APPEND"]
    statement := "LIST_APPEND n appends the top of the stack to the list n below it and pops only the value."
    source := "Python/bytecodes.c LIST_APPEND"
    status := .proven, prop := ``ListAppendRules, thm := some ``listAppendRules_proven },
  { id := "bytecode-build-slice", pyFile := "Python/bytecodes.c"
    pyFns := [op "BUILD_SLICE"]
    statement := "BUILD_SLICE 2 and 3 push a new slice of their operands in order, with step None for two."
    source := "Python/bytecodes.c BUILD_SLICE"
    status := .proven, prop := ``BuildSliceRules, thm := some ``buildSliceRules_proven },
  { id := "bytecode-build-string", pyFile := "Python/bytecodes.c"
    pyFns := [op "BUILD_STRING"]
    statement := "BUILD_STRING n on n strings pushes their concatenation in push order."
    source := "Python/bytecodes.c BUILD_STRING"
    status := .proven, prop := ``BuildStringRules, thm := some ``buildStringRules_proven },
  { id := "bytecode-get-len", pyFile := "Python/bytecodes.c"
    pyFns := [op "GET_LEN"]
    statement := "GET_LEN pushes len(o) above o and keeps o; when __len__ raises nothing is popped, for any object model."
    source := "Python/bytecodes.c GET_LEN"
    status := .proven, prop := ``GetLenRules, thm := some ``getLenRules_proven },
  { id := "bytecode-unary", pyFile := "Python/bytecodes.c"
    pyFns := [op "UNARY_NEGATIVE", op "UNARY_INVERT"]
    statement := "UNARY_NEGATIVE and UNARY_INVERT replace the operand with what __neg__ and __invert__ return, or propagate their exception with the operand still on the stack (ERROR_NO_POP, new in 3.15), for any object model; on an int ~x is -(x+1), as the language reference states."
    source := "Python/bytecodes.c:451-461, :604-614; Doc/reference/expressions.rst (bitwise inversion of x is -(x+1))"
    status := .proven, prop := ``UnaryRules, thm := some ``unaryRules_proven },
  { id := "bytecode-for-iter-range", pyFile := "Python/bytecodes.c"
    pyFns := [op "FOR_ITER_RANGE", op "_ITER_CHECK_RANGE", op "_ITER_JUMP_RANGE", op "_ITER_NEXT_RANGE"]
    statement := "FOR_ITER_RANGE equals FOR_ITER on every live stack GET_ITER could have left, given rangeiter_next; and the fast path itself, on a range iterator, pushes start and advances it by step while len > 0, jumps over END_FOR when len <= 0, and exits on anything that is not a range iterator."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c:4053-4101 (_ITER_CHECK_RANGE .. FOR_ITER_RANGE); Objects/rangeobject.c rangeiter_next"
    status := .proven, prop := ``ForIterRangeRules, thm := some ``forIterRangeRules_proven },
  { id := "bytecode-for-iter-seq", pyFile := "Python/bytecodes.c"
    pyFns := [op "FOR_ITER_LIST", op "_ITER_CHECK_LIST", op "_ITER_JUMP_LIST", op "_ITER_NEXT_LIST", op "FOR_ITER_TUPLE", op "_ITER_CHECK_TUPLE", op "_ITER_JUMP_TUPLE", op "_ITER_NEXT_TUPLE"]
    statement := "FOR_ITER_LIST and FOR_ITER_TUPLE equal FOR_ITER on every live stack GET_ITER could have left; and on an exact list or tuple with a tagged index they push item i and bump the tag, or at the end jump over END_FOR with both slots kept, and exit on anything else."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c:3927-4051 (_ITER_CHECK_LIST .. FOR_ITER_TUPLE)"
    status := .proven, prop := ``ForIterSeqRules, thm := some ``forIterSeqRules_proven },
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
    statement := "STORE_SUBSCR_LIST_INT equals STORE_SUBSCR on every live stack, negative indices included, given list_ass_subscript; and on an exact list and a compact int whose adjusted index is in range it stores in place and pops all three, exiting on every other stack."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c:1420-1452 (3.15 counts a negative index from the end)"
    status := .proven, prop := ``StoreSubscrListIntRules, thm := some ``storeSubscrListIntRules_proven },
  { id := "bytecode-subscr-tuple-int", pyFile := "Python/bytecodes.c"
    pyFns := [op "BINARY_OP_SUBSCR_TUPLE_INT", op "_BINARY_OP_SUBSCR_TUPLE_INT", op "_GUARD_BINARY_OP_SUBSCR_TUPLE_INT_BOUNDS", op "_GUARD_NOS_TUPLE"]
    statement := "BINARY_OP_SUBSCR_TUPLE_INT equals BINARY_OP for [] on every live stack, given tuplesubscript; and its bounds guard passes exactly on a non-negative compact index below the length, the macro answers the item there and exits on every other stack."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c:1230-1278"
    status := .proven, prop := ``SubscrTupleIntRules, thm := some ``subscrTupleIntRules_proven },
  { id := "bytecode-subscr-str-int", pyFile := "Python/bytecodes.c"
    pyFns := [op "BINARY_OP_SUBSCR_STR_INT", op "_BINARY_OP_SUBSCR_STR_INT", op "_GUARD_NOS_COMPACT_ASCII", op "BINARY_OP_SUBSCR_USTR_INT", op "_BINARY_OP_SUBSCR_USTR_INT"]
    statement := "BINARY_OP_SUBSCR_STR_INT and the 3.15 BINARY_OP_SUBSCR_USTR_INT equal BINARY_OP for [] on every stack, given unicode_subscript; and they answer the one-character str at a non-negative compact in-range index of an ASCII str (STR_INT) or of any str whose character there is ASCII (USTR_INT), exiting on every other stack."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c:564-568, :1185-1228"
    status := .proven, prop := ``SubscrStrIntRules, thm := some ``subscrStrIntRules_proven },
  { id := "bytecode-compare-float", pyFile := "Python/bytecodes.c"
    pyFns := [op "COMPARE_OP_FLOAT", op "_COMPARE_OP_FLOAT"]
    statement := "COMPARE_OP_FLOAT equals COMPARE_OP on every stack for the operand the compiler emits, NaN, infinities and signed zeros included, given float_richcompare; and on two floats it answers the IEEE-754 relation oparg >> 5 of left with right, exiting with the stack unchanged otherwise."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c:3253, :3262-3278; COMPARISON_BIT, Include/internal/pycore_code.h:523"
    status := .proven, prop := ``CompareFloatRules, thm := some ``compareFloatRules_proven },
  { id := "bytecode-compare-fused", pyFile := "Python/bytecodes.c"
    pyFns := []
    statement := "COMPARE_OP with the bool-coercion bit is COMPARE_OP without it followed by TO_BOOL, on every stack and for every object model, a raising __lt__ or __bool__ included."
    source := "compiler contract: COMPARE_OP fuses TO_BOOL (oparg & 16); Python/bytecodes.c:3232-3249"
    status := .proven, prop := ``CompareFused, thm := some ``compareFused_proven
    notes := "Credits no row by itself: COMPARE_OP and _COMPARE_OP are credited through bytecode-compare-op, which includes this statement." },
  { id := "bytecode-compare-int", pyFile := "Python/bytecodes.c"
    pyFns := [op "COMPARE_OP_INT", op "_COMPARE_OP_INT"]
    statement := "COMPARE_OP_INT equals COMPARE_OP on every stack for the operand the compiler emits, given long_richcompare; and on two compact ints it answers the comparison oparg >> 5 of left with right, exiting with the stack unchanged otherwise."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c:3256, :3280-3300"
    status := .proven, prop := ``CompareIntRules, thm := some ``compareIntRules_proven },
  { id := "bytecode-compare-str", pyFile := "Python/bytecodes.c"
    pyFns := [op "COMPARE_OP_STR", op "_COMPARE_OP_STR"]
    statement := "COMPARE_OP_STR equals COMPARE_OP for == and != on every stack, given unicode_compare_eq; and on two strs it answers a == b or a != b, exiting with the stack unchanged otherwise."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c:3259, :3302-3318"
    status := .proven, prop := ``CompareStrRules, thm := some ``compareStrRules_proven },
  { id := "bytecode-to-bool-generic", pyFile := "Python/bytecodes.c"
    pyFns := [op "TO_BOOL", op "_TO_BOOL"]
    statement := "Generic TO_BOOL pushes the truth value __bool__ or __len__ gives, and when either raises it pops the value and propagates the exception, for any object model."
    source := "Python/bytecodes.c:486-511"
    status := .proven, prop := ``ToBoolGeneric, thm := some ``toBoolGeneric_proven },
  { id := "bytecode-to-bool-specialized", pyFile := "Python/bytecodes.c"
    pyFns := [op "TO_BOOL_BOOL", op "TO_BOOL_INT", op "_TO_BOOL_INT", op "TO_BOOL_NONE", op "TO_BOOL_STR", op "_TO_BOOL_STR", op "TO_BOOL_LIST", op "_TO_BOOL_LIST", op "_GUARD_TOS_LIST"]
    statement := "TO_BOOL_BOOL, _INT, _NONE, _STR and _LIST equal TO_BOOL for every value on every stack, given the builtin bool slots; and each answers by itself on its own type (a compact int for TO_BOOL_INT since 3.15, None, a str, a list, a bool) and exits with the stack unchanged on every other value. TO_BOOL_STR's identity test against the empty-string singleton agreed with emptiness for all 77 constructors probed on 3.15.2 and main."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c:514-589"
    status := .proven, prop := ``ToBoolRules, thm := some ``toBoolRules_proven },
  { id := "bytecode-fast-guards", pyFile := "Python/bytecodes.c"
    pyFns := [op "_GUARD_TOS_INT", op "_GUARD_NOS_INT", op "_GUARD_TOS_FLOAT", op "_GUARD_NOS_FLOAT",
              op "_GUARD_TOS_UNICODE", op "_GUARD_NOS_UNICODE", op "_GUARD_NOS_COMPACT_ASCII",
              op "_GUARD_TOS_LIST", op "_GUARD_NOS_LIST", op "_GUARD_NOS_TUPLE", op "_GUARD_TOS_TUPLE",
              op "_GUARD_TOS_SLICE", op "TO_BOOL_BOOL"]
    statement := "Each type guard of the BINARY_OP, COMPARE_OP, TO_BOOL and STORE_SUBSCR families passes, changing nothing, exactly on the values it asks for (a compact exact int, an exact float, an exact str, an exact ASCII str, an exact list, an exact tuple, a slice, a bool) and exits with the state unchanged on every other live value."
    source := "Python/bytecodes.c:514-517, :530-543, :564-578, :635-643, :768-776, :1230-1238"
    status := .proven, prop := ``GuardRules, thm := some ``guardRules_proven },
  { id := "bytecode-load-fast", pyFile := "Python/bytecodes.c"
    pyFns := []
    statement := "LOAD_FAST and LOAD_FAST_BORROW push the local and change nothing else, for every state."
    source := "invariant: Python/bytecodes.c:283-291"
    status := .proven, prop := ``LoadFastPushes, thm := some ``loadFastPushes_proven
    notes := "Credits no row: LOAD_FAST and LOAD_FAST_BORROW are one branch-free read of a local, excluded as trivial: in the inventory." },
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
    pyFns := []
    statement := "LOAD_CONST pushes co_consts[oparg] and LOAD_SMALL_INT pushes the int oparg."
    source := "Python/bytecodes.c:312-321"
    status := .proven, prop := ``LoadConstRules, thm := some ``loadConstRules_proven
    notes := "Credits no row: LOAD_CONST and LOAD_SMALL_INT return one constant with no branch, excluded as trivial: in the inventory." },
  { id := "bytecode-stack-drops", pyFile := "Python/bytecodes.c"
    pyFns := []
    statement := "POP_TOP, END_FOR and POP_ITER drop their operands, END_SEND keeps the value and drops what was below it, and PUSH_NULL then POP_TOP changes nothing."
    source := "Python/bytecodes.c:359-361, :389-407, :428-434"
    status := .proven, prop := ``StackDrops, thm := some ``stackDrops_proven
    notes := "Credits no row: POP_TOP, POP_ITER, END_SEND and PUSH_NULL are branch-free moves excluded as trivial:, and END_FOR is credited through bytecode-end-for." },
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
    pyFns := [op "JUMP_FORWARD", op "JUMP_BACKWARD_NO_INTERRUPT", op "JUMP_BACKWARD", op "_CHECK_PERIODIC"]
    statement := "Fetched by the dispatch loop, JUMP_FORWARD and JUMP_BACKWARD_NO_INTERRUPT at offset p continue at the target Lib/dis.py's _get_jump_target reports (p + 1 + caches +/- the oparg dis accumulates over EXTENDED_ARG prefixes), with only instr_ptr and next_instr changed: stack, heap and a pending eval-breaker event (left for the innermost generator, bpo-30039) are untouched. JUMP_BACKWARD runs _CHECK_PERIODIC first: with nothing pending it jumps back, and when the pending handler raises it propagates that exception with the stack unchanged and without jumping."
    source := "Python/bytecodes.c:158-161, :3494-3496, :3544-3548, :3656-3664, :6054-6060; check_periodics, Python/ceval_macros.h:540-548; _get_jump_target and _unpack_opargs, Lib/dis.py"
    status := .proven, prop := ``JumpFull, thm := some ``jumpFull_proven },
  { id := "bytecode-branches", pyFile := "Python/bytecodes.c"
    pyFns := [op "POP_JUMP_IF_TRUE", op "POP_JUMP_IF_FALSE", op "POP_JUMP_IF_NONE", op "POP_JUMP_IF_NOT_NONE", op "_POP_JUMP_IF_TRUE", op "_POP_JUMP_IF_FALSE", op "_IS_NONE"]
    statement := "Each conditional branch jumps exactly when its condition holds, skips a NOT_TAKEN on fall-through, and pops the value it tested."
    source := "Python/bytecodes.c:3621-3654"
    status := .proven, prop := ``BranchRules, thm := some ``branchRules_proven },
  { id := "bytecode-unary-not", pyFile := "Python/bytecodes.c"
    pyFns := [op "UNARY_NOT"]
    statement := "UNARY_NOT flips a bool, doing it twice changes nothing, and `not x` (TO_BOOL then UNARY_NOT) pushes the negation of PyObject_IsTrue(x) or propagates its exception with x popped, for any object model."
    source := "Python/bytecodes.c:477-482, :505-512"
    status := .proven, prop := ``UnaryNotFull, thm := some ``unaryNotFull_proven },
  -- Specialized binary operators equal their generic form, over all stacks and all lawful models.
  { id := "bytecode-binary-op-add-int", pyFile := "Python/bytecodes.c"
    pyFns := [op "BINARY_OP_ADD_INT", op "_BINARY_OP_ADD_INT"]
    statement := "BINARY_OP_ADD_INT steps as BINARY_OP for + and += on every stack and lawful model; and it answers left + right exactly when both operands and the sum are compact ints, exiting otherwise."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c:672-685, :705; _PyCompactLong_Add, Objects/longobject.c:3870"
    status := .proven, prop := ``BinaryAddIntRules, thm := some ``binaryAddIntRules_proven },
  { id := "bytecode-binary-op-sub-int", pyFile := "Python/bytecodes.c"
    pyFns := [op "BINARY_OP_SUBTRACT_INT", op "_BINARY_OP_SUBTRACT_INT"]
    statement := "BINARY_OP_SUBTRACT_INT steps as BINARY_OP for every stack and lawful model; and it answers left - right exactly when both operands and the difference are compact ints, exiting otherwise."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c:687-700, :708; Objects/longobject.c:3915"
    status := .proven, prop := ``BinarySubIntRules, thm := some ``binarySubIntRules_proven },
  { id := "bytecode-binary-op-mul-int", pyFile := "Python/bytecodes.c"
    pyFns := [op "BINARY_OP_MULTIPLY_INT", op "_BINARY_OP_MULTIPLY_INT"]
    statement := "BINARY_OP_MULTIPLY_INT steps as BINARY_OP for every stack and lawful model; and it answers left * right exactly when both operands and the product are compact ints, exiting otherwise."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c:657-670, :702; Objects/longobject.c:4362"
    status := .proven, prop := ``BinaryMulIntRules, thm := some ``binaryMulIntRules_proven },
  { id := "bytecode-binary-op-add-float", pyFile := "Python/bytecodes.c"
    pyFns := [op "BINARY_OP_ADD_FLOAT", op "_BINARY_OP_ADD_FLOAT"]
    statement := "BINARY_OP_ADD_FLOAT steps as BINARY_OP for every stack and lawful model; and it answers the binary64 sum of two exact floats, exiting with the stack unchanged otherwise."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c:798-816, :840"
    status := .proven, prop := ``BinaryAddFloatRules, thm := some ``binaryAddFloatRules_proven },
  { id := "bytecode-binary-op-sub-float", pyFile := "Python/bytecodes.c"
    pyFns := [op "BINARY_OP_SUBTRACT_FLOAT", op "_BINARY_OP_SUBTRACT_FLOAT"]
    statement := "BINARY_OP_SUBTRACT_FLOAT steps as BINARY_OP for every stack and lawful model; and it answers the binary64 difference left - right of two exact floats, exiting with the stack unchanged otherwise."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c:818-836, :842"
    status := .proven, prop := ``BinarySubFloatRules, thm := some ``binarySubFloatRules_proven },
  { id := "bytecode-binary-op-mul-float", pyFile := "Python/bytecodes.c"
    pyFns := [op "BINARY_OP_MULTIPLY_FLOAT", op "_BINARY_OP_MULTIPLY_FLOAT"]
    statement := "BINARY_OP_MULTIPLY_FLOAT steps as BINARY_OP for every stack and lawful model; and it answers the binary64 product of two exact floats, exiting with the stack unchanged otherwise."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c:778-796, :838"
    status := .proven, prop := ``BinaryMulFloatRules, thm := some ``binaryMulFloatRules_proven },
  { id := "bytecode-binary-op-add-unicode", pyFile := "Python/bytecodes.c"
    pyFns := [op "BINARY_OP_ADD_UNICODE", op "_BINARY_OP_ADD_UNICODE"]
    statement := "BINARY_OP_ADD_UNICODE steps as BINARY_OP for every stack and lawful model; and it answers the concatenation left + right of two exact strs, exiting with the stack unchanged otherwise."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c:945-963"
    status := .proven, prop := ``BinaryAddUnicodeRules, thm := some ``binaryAddUnicodeRules_proven },
  { id := "bytecode-binary-op-subscr-list-int", pyFile := "Python/bytecodes.c"
    pyFns := [op "BINARY_OP_SUBSCR_LIST_INT", op "_BINARY_OP_SUBSCR_LIST_INT"]
    statement := "BINARY_OP_SUBSCR_LIST_INT steps as BINARY_OP (NB_SUBSCR) for every stack of live values and every lawful model, any index; and on an exact list and a compact int it answers the item, a negative index counting from the end, exiting on any other stack or an index outside the list."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c:1134-1162"
    status := .proven, prop := ``SubscrListIntRules, thm := some ``subscrListIntRules_proven },
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
    statement := "RETURN_VALUE pops the frame, restores the Python recursion budget, and resumes the caller at instr_ptr + return_offset with the returned value on top, for every caller stack; from a generator's frame it also marks the generator FRAME_CLEARED, gives tstate->exc_info back to the item below the generator's, clears the generator's handled exception and drops its frame's locals."
    source := "RETURN_VALUE, Python/bytecodes.c:1573-1593; clear_gen_frame and _PyEval_FrameClearAndPop, Python/ceval.c:2001-2030"
    status := .proven, prop := ``ReturnValueRules, thm := some ``returnValueRules_proven },
  { id := "bytecode-unwind-to-handler", pyFile := "Python/bytecodes.c"
    pyFns := ["get_exception_handler", "scan_back_to_entry_start", "skip_to_next_entry"]
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
    pyFns := [op "POP_EXCEPT"]
    statement := "PUSH_EXC_INFO then POP_EXCEPT restores tstate->exc_info->exc_value, so except blocks nest: the handled exception after a block is the one before it."
    source := "PUSH_EXC_INFO/POP_EXCEPT, Python/bytecodes.c:1911-1916, :4213-4226"
    status := .proven, prop := ``ExcInfoNests, thm := some ``excInfoNests_proven },
  { id := "bytecode-for-iter-exhausted", pyFile := "Python/bytecodes.c"
    pyFns := []
    statement := "FOR_ITER on an exhausted iterator jumps over END_FOR with iter and index_or_null left on the stack for the POP_ITER at the target, with the runtime the last step left, for every iterator and both forms of the slot."
    source := "_FOR_ITER, Python/bytecodes.c:3810-3821"
    status := .proven, prop := ``ForIterExhausted, thm := some ``forIterExhausted_proven
    notes := "Credits no row by itself: FOR_ITER and _FOR_ITER are credited through bytecode-for-iter, which includes this statement." },
  { id := "bytecode-for-iter-next", pyFile := "Python/bytecodes.c"
    pyFns := []
    statement := "FOR_ITER with a next item writes the new index_or_null back to its slot and pushes the item above it, with the runtime the step left, for every iterator."
    source := "_FOR_ITER, Python/bytecodes.c:3810-3821; _PyForIter_VirtualIteratorNext, Python/ceval.c:3709-3739"
    status := .proven, prop := ``ForIterNext, thm := some ``forIterNext_proven
    notes := "Credits no row by itself: FOR_ITER is credited through bytecode-for-iter, which includes this statement." },
  { id := "bytecode-for-iter", pyFile := "Python/bytecodes.c"
    pyFns := [op "FOR_ITER", op "_FOR_ITER"]
    statement := "FOR_ITER over an iterator object (NULL slot) calls tp_iternext once: an item is pushed above both slots with the runtime that one call left, NULL with no exception ends the loop (jump over END_FOR, both slots kept), StopIteration ends it the same way after clearing, and any other exception propagates with both slots kept (ERROR_NO_POP); over an exact list or tuple with a tagged index it pushes item i of the sequence as it is now and tags i + 1, or ends past the end; for every object model, so for stateful and Python-level __next__."
    source := "_FOR_ITER, Python/bytecodes.c:3810-3823; _PyForIter_VirtualIteratorNext, Python/ceval.c:3709-3739"
    status := .proven, prop := ``ForIterRules, thm := some ``forIterRules_proven },
  { id := "bytecode-binary-op", pyFile := "Python/bytecodes.c"
    pyFns := [op "BINARY_OP", op "_BINARY_OP"]
    statement := "BINARY_OP calls _PyEval_BinaryOps[oparg](lhs, rhs) with lhs the second value and replaces both operands with the result, and when the slot raises it propagates the exception with both operands still on the stack (ERROR_NO_POP); for every object model, oparg and operands."
    source := "Python/bytecodes.c:5924-5940"
    status := .proven, prop := ``BinaryOpRules, thm := some ``binaryOpRules_proven },
  { id := "bytecode-compare-op", pyFile := "Python/bytecodes.c"
    pyFns := [op "COMPARE_OP", op "_COMPARE_OP"]
    statement := "COMPARE_OP calls PyObject_RichCompare(left, right, oparg >> 5) with left the second value and pushes the result, or with bit 16 its truth value as a bool; when either call raises both operands are popped and the exception propagates. With bit 16 it is COMPARE_OP without it followed by TO_BOOL. For every object model."
    source := "Python/bytecodes.c:3232-3251"
    status := .proven, prop := ``CompareOpFull, thm := some ``compareOpFull_proven },
  { id := "bytecode-push-exc-info", pyFile := "Python/bytecodes.c"
    pyFns := [op "PUSH_EXC_INFO"]
    statement := "PUSH_EXC_INFO makes the exception on top of the stack the handled one (exc_info->exc_value) and pushes the previous handled exception, or None, below it; followed by POP_EXCEPT it restores the previous one."
    source := "Python/bytecodes.c:4213-4226, :1911-1916"
    status := .proven, prop := ``PushExcInfoFull, thm := some ``pushExcInfoFull_proven },
  { id := "bytecode-raise-varargs", pyFile := "Python/bytecodes.c"
    pyFns := [op "RAISE_VARARGS"]
    statement := "RAISE_VARARGS 1 raises the top of the stack and RAISE_VARARGS 2 the second value with the top as its cause, through do_raise, popping the operands; RAISE_VARARGS 0 re-raises the handled exception through exception_unwind, or raises RuntimeError when there is none."
    source := "Python/bytecodes.c:1531-1542; do_raise, Python/ceval.c"
    status := .proven, prop := ``RaiseVarargsRules, thm := some ``raiseVarargsRules_proven },
  { id := "bytecode-create-init-frame", pyFile := "Python/bytecodes.c"
    pyFns := [op "_CREATE_INIT_FRAME"]
    statement := "_CREATE_INIT_FRAME raises in the caller, with its operands consumed, no shim frame left, return_offset and the recursion counter untouched, when __init__'s frame cannot be built; otherwise the _Py_InitCleanup shim holding self becomes the frame __init__ returns to, the caller records return_offset 1 + INLINE_CACHE_ENTRIES_CALL, and one recursion unit is taken."
    source := "Python/bytecodes.c:4790-4813"
    status := .proven, prop := ``CreateInitFrameRules, thm := some ``createInitFrameRules_proven },
  { id := "bytecode-end-for", pyFile := "Python/bytecodes.c"
    pyFns := [op "END_FOR"]
    statement := "END_FOR is no_save_ip: dispatching it leaves frame->instr_ptr unchanged, where POP_TOP with the same body records its own address; then it pops its operand."
    source := "Python/bytecodes.c:393-398"
    status := .proven, prop := ``EndForRules, thm := some ``endForRules_proven },
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
    notes := "Those values have no address in the machine: IS_OP asks the Rt.sameImmediate oracle for two equal ones (bytecode-is-op), and the difftest's runtime answers false, while CPython's answer depends on its small-int cache, interning, constant merging and on copies of one object. bytecode_diff.py exclusion: is-on-immediates." },
  { id := "bytecode-is-op", pyFile := "Python/bytecodes.c"
    pyFns := [op "IS_OP", op "_IS_OP"]
    statement := "IS_OP replaces both operands by the bool of Py_Is(left, right) ^ oparg, for any two values: heap objects are identical exactly when they share an address, differing values never are, equal singletons (None, bools, builtin types and functions) always are, and two equal ints, floats, strs or bytes are as the runtime's sameImmediate oracle says, not by value equality."
    source := "Python/bytecodes.c:3320-3328; Py_Is, Include/object.h:185"
    status := .proven, prop := ``IsOpRules, thm := some ``isOpRules_proven },
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
    notes := "The machine has no reference counts. bytecode_diff.py exclusion: refcount-finalizer-order." },
  -- Unpacking.
  { id := "bytecode-unpack-sequence", pyFile := "Python/bytecodes.c"
    pyFns := [op "UNPACK_SEQUENCE", op "_UNPACK_SEQUENCE", op "UNPACK_SEQUENCE_TWO_TUPLE",
      op "_UNPACK_SEQUENCE_TWO_TUPLE", op "UNPACK_SEQUENCE_TUPLE", op "_UNPACK_SEQUENCE_TUPLE",
      op "UNPACK_SEQUENCE_LIST", op "_UNPACK_SEQUENCE_LIST"]
    statement := "UNPACK_SEQUENCE n, for every object model, calls PyIter_Next on iter(v) one item at a time: with exactly n items and then the end it replaces v by them, item 0 on top, in the runtime the exhausting call left; fewer gives ValueError 'not enough values to unpack (expected n, got k)'; one more gives 'too many values to unpack (expected n, got len)' for an exact list, tuple or dict longer than n (its size read after the extra call) and '(expected n)' otherwise; an exception from __next__ propagates; a TypeError from iter() on a value with neither tp_iter nor the sequence protocol becomes 'cannot unpack non-iterable T object'; v is popped on every error. UNPACK_SEQUENCE_TUPLE, _LIST and _TWO_TUPLE unpack an exact tuple or list of exactly n (2) items the same way and on every other value are the generic UNPACK_SEQUENCE."
    source := "Python/bytecodes.c:2057-2146; _PyEval_UnpackIterableStackRef, Python/ceval.c:2357-2459"
    status := .proven, prop := ``UnpackRules, thm := some ``unpackRules_proven },
  { id := "bytecode-unpack-ex", pyFile := "Python/bytecodes.c"
    pyFns := [op "UNPACK_EX"]
    statement := "UNPACK_EX (before | after << 8), for every object model: the first `before` items come one PyIter_Next call at a time; then PySequence_List(it) makes a new empty list L and calls _PyList_Extend(L, it) on the iterator itself (the object model's listExtend, which is where PyObject_GetIter(it), PyObject_LengthHint(it, 8) and the loop live), and the stack gets the first items (item 0 on top), L cut to all but its last `after` items, and those last items in order; too few items gives 'not enough values to unpack (expected at least before+after, got k)' with k counted as CPython counts it in each loop; exceptions from __next__ and from _PyList_Extend propagate; an exception from iter(v) propagates unless it is a TypeError on a value with neither tp_iter nor the sequence protocol, which becomes 'cannot unpack non-iterable T object' (a TypeError of an iterable value is kept); v is popped on every error."
    source := "Python/bytecodes.c:2148-2153; _PyEval_UnpackIterableStackRef, Python/ceval.c:2357-2451 (GetIter failure :2368-2378); PySequence_List, Objects/abstract.c:2081-2101"
    status := .proven, prop := ``UnpackExFull, thm := some ``unpackExFull_proven },
  -- Builders.
  { id := "bytecode-builders", pyFile := "Python/bytecodes.c"
    pyFns := [op "LIST_EXTEND", op "_LIST_EXTEND", op "SET_UPDATE", op "_SET_UPDATE", op "DICT_UPDATE",
      op "_DICT_UPDATE", op "DICT_MERGE", op "_DICT_MERGE", op "SET_ADD", op "MAP_ADD", op "BUILD_SET",
      op "BUILD_MAP"]
    statement := "For every object model: LIST_EXTEND, SET_UPDATE, DICT_UPDATE and DICT_MERGE call _PyList_Extend, _PySet_Update, PyDict_Update and _PyDict_MergeUniq on the container oparg below the top, pop only the top on success and keep every operand on failure (ERROR_NO_POP); LIST_EXTEND rewrites a TypeError on a non-iterable to 'Value after * must be an iterable, not T'; DICT_UPDATE rewrites an AttributeError to \"'T' object is not a mapping\" exactly when update has no keys, restores it when it has, and chains it as __context__ when the probe raises; DICT_MERGE reports the duplicate key of _PyDict_MergeUniq as 'F got multiple values for keyword argument K' (F the _PyObject_FunctionStr or 'function'), and its AttributeError as 'Value after ** must be a mapping, not T' under the same keys rule, every other exception (a mapping's own KeyError included) unchanged. _PyObject_FunctionStr looks up __qualname__, then __module__, compares it with 'builtins', and only then runs str() of the module and of the qualname, returning NULL at the first exception (a raising lookup, Py_NE comparison or its truth test, str(module), str(qualname) in every branch, or str(x) with no __qualname__; so a raising __module__ lookup never calls str(qualname)); a raising str(dupkey) makes DICT_MERGE raise that exception, since _PyErr_FormatV sets nothing when PyUnicode_FromFormatV fails. SET_ADD refuses anything but an exact set with \"'T' object is not a set\" (3.15, gh-154902); on failure SET_ADD pops only the value and MAP_ADD only key and value, leaving the container and the items above it for the comprehension's cleanup handler. BUILD_SET and BUILD_MAP add the values (pairs) to a new set (dict) from the bottom up, each add in the runtime the previous left, stopping at the first failure with every value popped."
    source := "Python/bytecodes.c:1380-1392, :2511-2581, :2610-2666; Python/generated_cases.c.h:10292-10293, :11384-11396; _PyEval_FormatKwargsError, Python/ceval.c:3414-3446; _PyObject_FunctionStr, Objects/object.c:976-1009; _PyErr_FormatV, Python/errors.c:1219-1233"
    status := .proven, prop := ``BuildersRules, thm := some ``buildersRules_proven },
  { id := "bytecode-get-iter", pyFile := "Python/bytecodes.c"
    pyFns := [op "GET_ITER", op "_GET_ITER", op "GET_ITER_SELF", op "_GUARD_ITERATOR", op "GET_ITER_VIRTUAL",
      op "_GUARD_ITER_VIRTUAL", op "_PUSH_TAGGED_ZERO"]
    statement := "GET_ITER, for every object model: on a type with _tp_iteritem (exact list, tuple, str, bytes) it keeps the value and pushes a tagged 0 without calling __iter__; otherwise on a type whose tp_iter is PyObject_SelfIter it keeps the value and pushes NULL; otherwise it replaces the value by PyObject_GetIter's result with NULL above, or propagates its exception with the value popped; a coroutine in a plain generator's yield from raises TypeError 'cannot 'yield from' a coroutine object in a non-coroutine generator'. GET_ITER_VIRTUAL and GET_ITER_SELF give GET_ITER's result on the values their guards accept and are GET_ITER on every other value."
    source := "Python/bytecodes.c:3720-3774; _PyEval_GetIter, Python/ceval.c:1131-1163"
    status := .proven, prop := ``GetIterRules, thm := some ``getIterRules_proven },
  { id := "bytecode-format", pyFile := "Python/bytecodes.c"
    pyFns := [op "CONVERT_VALUE", op "FORMAT_SIMPLE", op "FORMAT_WITH_SPEC"]
    statement := "CONVERT_VALUE 1/2/3 replaces the value by PyObject_Str/Repr/ASCII of it (!s, !r, !a); FORMAT_SIMPLE keeps an exact str without calling anything and replaces anything else by PyObject_Format(v, NULL); FORMAT_WITH_SPEC replaces value and spec by PyObject_Format(v, spec); every failure propagates with the operands popped. For every object model."
    source := "Python/bytecodes.c:5873-5904"
    status := .proven, prop := ``FormatRules, thm := some ``formatRules_proven },
  { id := "bytecode-intrinsics", pyFile := "Python/bytecodes.c"
    pyFns := [op "CALL_INTRINSIC_1", op "_CALL_INTRINSIC_1", op "CALL_INTRINSIC_2", op "_CALL_INTRINSIC_2"]
    statement := "CALL_INTRINSIC_1 calls _PyIntrinsics_UnaryFunctions[oparg] on the value and CALL_INTRINSIC_2 calls _PyIntrinsics_BinaryFunctions[oparg](value2, value1) with value2 the deeper operand, replacing the operands by the result; when the intrinsic fails both leave through ERROR_NO_POP with the operands kept (new in 3.15). For every object model and oparg."
    source := "Python/bytecodes.c:1498-1529"
    status := .proven, prop := ``IntrinsicRules, thm := some ``intrinsicRules_proven
    notes := "The intrinsic functions themselves are Python/intrinsics.c rows." },
  { id := "bytecode-call-builtins", pyFile := "Python/bytecodes.c"
    pyFns := [op "_CHECK_PERIODIC_AT_END", op "_GUARD_NOS_NULL", op "_GUARD_THIRD_NULL",
      op "_GUARD_CALLABLE_TYPE_1", op "_CALL_TYPE_1", op "CALL_TYPE_1", op "_GUARD_CALLABLE_STR_1", op "_CALL_STR_1",
      op "CALL_STR_1", op "_GUARD_CALLABLE_TUPLE_1", op "_CALL_TUPLE_1", op "CALL_TUPLE_1", op "CALL_LEN",
      op "_GUARD_CALLABLE_LEN", op "_CALL_LEN", op "_GUARD_CALLABLE_ISINSTANCE", op "_CALL_ISINSTANCE",
      op "CALL_ISINSTANCE", op "CALL_LIST_APPEND", op "_GUARD_CALLABLE_LIST_APPEND", op "_CALL_LIST_APPEND"]
    statement := "For every object model: with a NULL self_or_null and the builtin type, str, tuple, len or isinstance itself as the callable, CALL_TYPE_1, CALL_STR_1, CALL_TUPLE_1, CALL_LEN and CALL_ISINSTANCE push Py_TYPE(arg), PyObject_Str(arg), tuple(arg), len(arg) as an int, or the bool of isinstance(inst, cls) in place of their operands, keep every operand when that slot raises (ERROR_NO_POP), and CALL_STR_1/CALL_TUPLE_1 end with _CHECK_PERIODIC_AT_END; CALL_LIST_APPEND with list.append and an exact list as self appends and leaves None; on every stack a guard rejects, each is the generic CALL. _CHECK_PERIODIC_AT_END handles a pending event like _CHECK_PERIODIC except right after a LOAD_SPECIAL code unit, where it leaves it pending."
    source := "Python/bytecodes.c:163-166, :1753-1755, :4671-4756, :4988-5090; check_periodics_at_end, Python/ceval_macros.h:550-563"
    status := .proven, prop := ``CallSpecRules, thm := some ``callSpecRules_proven },
  { id := "bytecode-call-generic", pyFile := "Python/bytecodes.c"
    pyFns := [op "CALL", op "_MAYBE_EXPAND_METHOD", op "_DO_CALL", op "CALL_KW", op "_MAYBE_EXPAND_METHOD_KW",
      op "_DO_CALL_KW", op "CALL_FUNCTION_EX", op "_MAKE_CALLARGS_A_TUPLE", op "_DO_CALL_FUNCTION_EX"]
    statement := "For every object model and every live callable: CALL and CALL_KW first split a bound method object with a NULL self_or_null into im_func and im_self and are then exactly themselves on the split stack; a function object is inlined (operands popped, _PyEvalFramePushAndInit on self then the arguments, with kwnames for CALL_KW, return_offset = INSTRUCTION_SIZE, DISPATCH_INLINED), its frame-building error raised with the operands consumed; anything else goes to PyObject_Vectorcall, whose result replaces the operands (then _CHECK_PERIODIC_AT_END for CALL) and whose error pops them. CALL_FUNCTION_EX makes a non-tuple callargs a tuple after the 'Value after * must be an iterable, not T' check, keeping every operand on either failure, and is then itself on the tuple; with a tuple it inlines a function object with the kwargs dict unpacked after the positional items by _PyStack_UnpackDict, which takes every key whose type has Py_TPFLAGS_UNICODE_SUBCLASS (an exact str or any str-subclass instance, as its str value; a subclass __eq__ run by initialize_locals' slow loop and the subclass key object kept in **kwargs are a stated scope limit) and otherwise raises 'keywords must be strings' after the loop, and hands anything else to PyObject_Call with the dict itself, result then _CHECK_PERIODIC_AT_END, error popping the operands."
    source := "Python/bytecodes.c:4373-4457, :5407-5472, :5565-5569, :5620-5732; _Py_Check_ArgsIterable, Python/ceval.c:3403-3412; _PyEvalFramePushAndInit_Ex, Python/ceval.c:2074-2125; _PyStack_UnpackDict, Objects/call.c:1013-1080; _PyObject_Call, Objects/call.c:333-367"
    status := .proven, prop := ``CallGenericFull, thm := some ``callGenericFull_proven },
  { id := "bytecode-attr-specialized", pyFile := "Python/bytecodes.c"
    pyFns := [op "LOAD_ATTR_SLOT", op "_LOAD_ATTR_SLOT", op "LOAD_ATTR_MODULE", op "_LOAD_ATTR_MODULE",
      op "LOAD_ATTR_CLASS", op "_CHECK_ATTR_CLASS", op "_LOAD_ATTR_CLASS", op "LOAD_ATTR_CLASS_WITH_METACLASS_CHECK",
      op "STORE_ATTR_SLOT", op "_STORE_ATTR_SLOT", op "_GUARD_TYPE_VERSION"]
    statement := "For every object model: LOAD_ATTR_SLOT, under the owner's cached type version, replaces an instance by the non-NULL value in its cached slot (a NULL above it for the method form) and is the generic LOAD_ATTR on another version or an empty slot; LOAD_ATTR_MODULE replaces a module by the non-NULL value at the cached index of its dict under the cached keys version, and is LOAD_ATTR on anything but a module, another version or a NULL value; LOAD_ATTR_CLASS replaces a class object with the cached version by the cached descriptor and is LOAD_ATTR otherwise; LOAD_ATTR_CLASS_WITH_METACLASS_CHECK asks the metaclass version first and then the class version, each mismatch being LOAD_ATTR; STORE_ATTR_SLOT stores the value in the cached slot of an instance under the cached type version, popping both, and is the generic STORE_ATTR on another version."
    source := "Python/bytecodes.c:2862-2866, :2918-2948, :2999-3054, :3193-3212"
    status := .proven, prop := ``AttrSpecRules, thm := some ``attrSpecRules_proven
    notes := "A slot index and a dict entry index stand for C's byte offset and DK_UNICODE_ENTRIES index. The machine's builtin types carry no tp_version_tag, so _CHECK_ATTR_CLASS exits on them where CPython could pass." },
  { id := "bytecode-property-frame-recursion", pyFile := "Python/bytecodes.c"
    pyFns := [op "LOAD_ATTR_PROPERTY", op "_LOAD_ATTR_PROPERTY_FRAME"]
    statement := "With the recursion budget spent (py_recursion_remaining <= 1), LOAD_ATTR_PROPERTY does not enter the getter's frame, as every CALL form that pushes a Python frame checks with _CHECK_RECURSION_REMAINING. It does: _GUARD_TYPE_VERSION, the function-version and stack-space exits of _LOAD_ATTR_PROPERTY_FRAME, _SAVE_RETURN_OFFSET and _PUSH_FRAME pass, and _PUSH_FRAME tests nothing, so a recursive property passes the limit once its site has specialized."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c:3056-3077, :4611-4613, :4628-4642"
    status := .refuted, prop := ``PropertyFrameChecksRecursion, thm := some ``propertyFrameChecksRecursion_refuted
    bug := some "bytecode-attr-frame-recursion" },
  { id := "bytecode-getattribute-frame-recursion", pyFile := "Python/bytecodes.c"
    pyFns := [op "LOAD_ATTR_GETATTRIBUTE_OVERRIDDEN", op "_LOAD_ATTR_GETATTRIBUTE_OVERRIDDEN_FRAME"]
    statement := "With the recursion budget spent, LOAD_ATTR_GETATTRIBUTE_OVERRIDDEN does not enter the overriding __getattribute__'s frame. It does, by the same _PUSH_FRAME with no _CHECK_RECURSION_REMAINING."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c:3079-3105, :4628-4642"
    status := .refuted, prop := ``GetattributeFrameChecksRecursion, thm := some ``getattributeFrameChecksRecursion_refuted
    bug := some "bytecode-attr-frame-recursion" },
  { id := "bytecode-import", pyFile := "Python/bytecodes.c"
    pyFns := [op "IMPORT_NAME", op "IMPORT_FROM"]
    statement := "For every object model: IMPORT_NAME takes the name co_names[oparg >> 2]; without bit 1 it calls _PyEval_LazyImportName with bit 0 as the lazy flag (PEP 810), with bit 1 _PyEval_ImportName, on fromlist and level, and pops both on success and failure; IMPORT_FROM keeps the module and pushes _PyEval_LazyImportFrom of a lazy import object, _PyEval_ImportFrom of anything else, keeping the module on failure."
    source := "Python/bytecodes.c:3456-3492; Python/codegen.c:2936-2946"
    status := .proven, prop := ``ImportRules, thm := some ``importRules_proven
    notes := "What _PyEval_LazyImportName, _PyEval_ImportName and the lazy import object do is Python/ceval.c, Python/import.c and Objects/lazyimportobject.c; the difftest model imports nothing and has no lazy import." },
  { id := "bytecode-null-guards", pyFile := "Python/bytecodes.c"
    pyFns := [op "_GUARD_NOS_NOT_NULL", op "_GUARD_TOS_NOT_NULL", op "_GUARD_NOS_NULL", op "_GUARD_THIRD_NULL"]
    statement := "_GUARD_NOS_NOT_NULL exits exactly when the second value is NULL and _GUARD_TOS_NOT_NULL exactly when the top is; _GUARD_NOS_NULL and _GUARD_THIRD_NULL exit exactly when their slot is not NULL; each leaves the stack unchanged, for every stack."
    source := "Python/bytecodes.c:1753-1755, :3868-3870, :4671-4677"
    status := .proven, prop := ``NullGuardRules, thm := some ``nullGuardRules_proven },
  { id := "bytecode-match", pyFile := "Python/bytecodes.c"
    pyFns := [op "MATCH_CLASS", op "_MATCH_CLASS", op "MATCH_MAPPING", op "MATCH_SEQUENCE", op "MATCH_KEYS"]
    statement := "MATCH_CLASS replaces subject, type and names by _PyEval_MatchClass's attribute tuple, or None on no match, keeping all three when it raises (ERROR_NO_POP, 3.15); MATCH_MAPPING and MATCH_SEQUENCE push above the subject whether its type has Py_TPFLAGS_MAPPING / Py_TPFLAGS_SEQUENCE; MATCH_KEYS pushes _PyEval_MatchKeys(subject, keys) above both and keeps both when it raises. For every object model."
    source := "Python/bytecodes.c:3675-3717"
    status := .proven, prop := ``MatchRules, thm := some ``matchRules_proven
    notes := "_PyEval_MatchClass and _PyEval_MatchKeys themselves are Python/ceval.c rows." }
,
  -- The specialized Python calls against their generic forms (SpecCallPy.lean).
  { id := "bytecode-call-py-general", pyFile := "Python/bytecodes.c"
    pyFns := [op "CALL_PY_GENERAL", op "_CHECK_FUNCTION_VERSION", op "_CHECK_RECURSION_REMAINING",
      op "_PY_FRAME_GENERAL", op "_SAVE_RETURN_OFFSET", op "_PUSH_FRAME"]
    statement := "For every live callable, self_or_null, argument list, runtime and object model, and next_instr = this_instr + INSTRUCTION_SIZE: what the machine does after CALL_PY_GENERAL (carry on, raise, return, stop) is what it does after the generic CALL. It exits to CALL on a non-function or a stale func_version and when py_recursion_remaining <= 1; otherwise _PyEvalFramePushAndInit builds the same frame (or fails the same way, operands consumed) and _SAVE_RETURN_OFFSET + _PUSH_FRAME leave exactly the state CALL's return_offset = INSTRUCTION_SIZE + DISPATCH_INLINED + start_frame leave, recursion counter decremented once. _PyEvalFramePushAndInit is proven to leave py_recursion_remaining alone (KeepsRec), so the check before it and start_frame's after it see the same budget. The body on its own (before execOp's withDeopt restart, CallPyGeneralFast): a non-function or a function whose func_version differs from the cached one exits with the stack unchanged; a matching version with py_recursion_remaining <= 1 exits; otherwise it is .ok in exactly enteredSt of the frame _PyEvalFramePushAndInit builds, or that builder's error with the operands consumed."
    source := "Python/bytecodes.c:4460-4506, :4611-4613, :4628-4642, :6136-6140; DISPATCH_INLINED, Python/ceval_macros.h; _PyEvalFramePushAndInit, Python/ceval.c:2033-2068"
    status := .proven, prop := ``CallPyGeneralSpec, thm := some ``callPyGeneralSpec_proven
    notes := "No PEP 523 eval-frame hook is modelled, so _CHECK_PEP_523 never exits; it is not listed." },
  { id := "bytecode-call-bound-method-general", pyFile := "Python/bytecodes.c"
    pyFns := [op "CALL_BOUND_METHOD_GENERAL", op "_CHECK_METHOD_VERSION", op "_EXPAND_METHOD"]
    statement := "For every live callable whose method objects are well formed (im_self not NULL, im_func live), every runtime and object model: what the machine does after CALL_BOUND_METHOD_GENERAL is what it does after CALL. It exits unless the callable is a method object whose im_func is a function with the cached version and self_or_null is NULL, and with py_recursion_remaining <= 1; otherwise it splits the method into im_func and im_self as CALL's _MAYBE_EXPAND_METHOD does and builds and enters the same frame. The body on its own (CallBoundMethodGeneralFast): every stack _CHECK_METHOD_VERSION rejects, a method whose im_func has another func_version included, exits with the stack unchanged; past it, with py_recursion_remaining <= 1 it exits on the split stack (im_func, im_self), and otherwise it is .ok in exactly enteredSt of the frame built on im_func, or that builder's error with the operands consumed."
    source := "Python/bytecodes.c:4508-4539"
    status := .proven, prop := ``CallBoundMethodGeneralSpec, thm := some ``callBoundMethodGeneralSpec_proven },
  { id := "bytecode-call-py-exact-args", pyFile := "Python/bytecodes.c"
    pyFns := [op "CALL_PY_EXACT_ARGS", op "_CHECK_FUNCTION_EXACT_ARGS", op "_CHECK_STACK_SPACE",
      op "_INIT_CALL_PY_EXACT_ARGS"]
    statement := "For every live callable, runtime and object model, when the function the version guard lets through has SIMPLE_FUNCTION code (no *args, **kwargs or keyword-only parameters, CO_OPTIMIZED: the invariant specialize_py_call maintains): what the machine does after CALL_PY_EXACT_ARGS is what it does after CALL. It exits on a non-function, a stale version, co_argcount != oparg + (self_or_null != NULL), no data-stack space and py_recursion_remaining <= 1; otherwise the frame _INIT_CALL_PY_EXACT_ARGS fills by copying the arguments (NULL locals) is the frame _PyEvalFramePushAndInit/initialize_locals builds, entered the same way. The body on its own, for any code (CallPyExactArgsFast): each of the four guards exits with the stack unchanged on exactly the stacks it rejects, in that order, and with all passing it is .ok in exactly enteredSt of exactFrame (_PyFrame_PushUnchecked, NULL locals, self then the arguments copied)."
    source := "Python/bytecodes.c:4596-4626, :4659-4669; function_kind and specialize_py_call, Python/specialize.c:1472-1481, :1754-1792"
    status := .proven, prop := ``CallPyExactArgsSpec, thm := some ``callPyExactArgsSpec_proven
    notes := "The SIMPLE_FUNCTION hypothesis is necessary: the copy leaves a *args or keyword-only local NULL where initialize_locals fills it." },
  { id := "bytecode-call-bound-method-exact-args", pyFile := "Python/bytecodes.c"
    pyFns := [op "CALL_BOUND_METHOD_EXACT_ARGS", op "_CHECK_CALL_BOUND_METHOD_EXACT_ARGS",
      op "_INIT_CALL_BOUND_METHOD_EXACT_ARGS"]
    statement := "For every live callable with well-formed method objects whose im_func satisfies the SIMPLE_FUNCTION invariant: what the machine does after CALL_BOUND_METHOD_EXACT_ARGS is what it does after CALL. It exits unless the callable is a method object and self_or_null is NULL; otherwise it splits the method and is then CALL_PY_EXACT_ARGS on im_func and im_self, its later exits restarting CALL on the split stack (the flush), which CALL would have made itself. The body on its own (CallBoundMethodExactArgsFast with CallPyExactArgsFast): a non-method or a non-NULL self_or_null exits with the stack unchanged, and a method object makes it the CALL_PY_EXACT_ARGS body on im_func, im_self, whose guard and completion clauses are stated."
    source := "Python/bytecodes.c:4577-4590, :4644-4657"
    status := .proven, prop := ``CallBoundMethodExactArgsSpec, thm := some ``callBoundMethodExactArgsSpec_proven },
  { id := "bytecode-call-kw-py", pyFile := "Python/bytecodes.c"
    pyFns := [op "CALL_KW_PY", op "_CHECK_FUNCTION_VERSION_KW", op "_PY_FRAME_KW"]
    statement := "For every live callable, argument list and kwnames tuple of names, every runtime and object model: what the machine does after CALL_KW_PY is what it does after CALL_KW. It exits on a non-function, a stale version and py_recursion_remaining <= 1 (the check python/cpython#137887 added); otherwise it builds the frame with the keyword names and enters it as CALL_KW does, or fails as it does. The body on its own (CallKwPyFast): a non-function or a stale func_version exits with the stack unchanged, a matching one with py_recursion_remaining <= 1 exits, and otherwise it is .ok in exactly enteredSt of _PY_FRAME_KW's frame, or its error with the operands consumed."
    source := "Python/bytecodes.c:5474-5519"
    status := .proven, prop := ``CallKwPySpec, thm := some ``callKwPySpec_proven },
  { id := "bytecode-call-kw-bound-recursion", pyFile := "Python/bytecodes.c"
    pyFns := [op "CALL_KW_BOUND_METHOD", op "_CHECK_METHOD_VERSION_KW", op "_EXPAND_METHOD_KW", op "_PY_FRAME_KW"]
    statement := "CALL_KW_BOUND_METHOD completes exactly when CALL_KW does. False: it has no _CHECK_RECURSION_REMAINING, so with py_recursion_remaining = 0 it pushes the method's frame where CALL_KW's start_frame raises RecursionError (python/cpython#155151, fix in PR 156346)."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c:5521-5551, :4628-4642"
    status := .refuted, prop := ``CallKwBoundMethodRefines, thm := some ``callKwBoundMethodRefines_refuted
    bug := some "bytecode-call-ex-kw-bound-recursion" },
  { id := "bytecode-call-kw-bound-budget", pyFile := "Python/bytecodes.c"
    pyFns := [op "CALL_KW_BOUND_METHOD", op "_CHECK_METHOD_VERSION_KW", op "_EXPAND_METHOD_KW", op "_PY_FRAME_KW"]
    statement := "The narrowing of bytecode-call-kw-bound-recursion: with py_recursion_remaining > 0, for every live callable with well-formed method objects, every argument list and kwnames tuple, runtime and object model, what the machine does after CALL_KW_BOUND_METHOD is what it does after CALL_KW: it exits unless the callable is a method object with a function im_func of the cached version and a NULL self_or_null, and otherwise splits it and builds and enters CALL_KW's frame. The body on its own, at any budget (CallKwBoundMethodFast): every stack _CHECK_METHOD_VERSION_KW rejects (a stale im_func version included) exits with the stack unchanged, and past it the body is .ok in exactly enteredSt of the frame built on im_func, im_self and the keyword names, with no recursion check, or that builder's error with the operands consumed."
    source := "Python/bytecodes.c:5521-5551"
    status := .proven, prop := ``CallKwBoundMethodSpec, thm := some ``callKwBoundMethodSpec_proven },
  { id := "bytecode-call-ex-py-recursion", pyFile := "Python/bytecodes.c"
    pyFns := [op "CALL_EX_PY", op "_CHECK_IS_PY_CALLABLE_EX", op "_PY_FRAME_EX"]
    statement := "CALL_EX_PY completes exactly when CALL_FUNCTION_EX does. False: it has no _CHECK_RECURSION_REMAINING, so with py_recursion_remaining = 0 it pushes the function's frame where CALL_FUNCTION_EX's start_frame raises RecursionError (python/cpython#155151, fix in PR 156346)."
    source := "invariant: specialized opcode refines its generic form; Python/bytecodes.c:5734-5771, :4628-4642"
    status := .refuted, prop := ``CallExPyRefines, thm := some ``callExPyRefines_refuted
    bug := some "bytecode-call-ex-kw-bound-recursion" },
  { id := "bytecode-call-ex-py-budget", pyFile := "Python/bytecodes.c"
    pyFns := [op "CALL_EX_PY", op "_CHECK_IS_PY_CALLABLE_EX", op "_PY_FRAME_EX", op "_MAKE_CALLARGS_A_TUPLE"]
    statement := "The narrowing of bytecode-call-ex-py-recursion: with an exact tuple as callargs and py_recursion_remaining > 0, for every live callable, every kwargs (NULL or a dict), runtime and object model, what the machine does after CALL_EX_PY is what it does after CALL_FUNCTION_EX: it exits on anything but a Python function; on one it unpacks the dict with _PyStack_UnpackDict (refusing non-str keys the same way) and builds and enters CALL_FUNCTION_EX's frame with _PyEvalFramePushAndInit_Ex, or fails as it does. Every other callargs goes through CALL_EX_PY's own _MAKE_CALLARGS_A_TUPLE first (CallExPyFast): the 'Value after * must be an iterable, not T' TypeError and a failing tuple() keep every operand and are what CALL_FUNCTION_EX raises, and a successful conversion makes the body and the dispatch exactly themselves on the stack with that tuple, so tuple(callargs) runs once even when _CHECK_IS_PY_CALLABLE_EX then exits (JUMP_TO_PREDICTED keeps the converted stack). The body on its own: on an exact tuple anything but a Python function exits with the stack unchanged; a function gets _PyStack_UnpackDict's error with the operands consumed, or the frame entered (enteredSt) at any budget, or the builder's error."
    source := "Python/bytecodes.c:5734-5771; _PyEvalFramePushAndInit_Ex, Python/ceval.c:2074-2125"
    status := .proven, prop := ``CallExPySpec, thm := some ``callExPySpec_proven },
  -- The exception-handling instructions (SpecExcMatch.lean).
  { id := "bytecode-check-exc-match", pyFile := "Python/bytecodes.c"
    pyFns := [op "CHECK_EXC_MATCH"]
    statement := "For every object model: CHECK_EXC_MATCH on (left, right) raises _PyEval_CheckExceptTypeValid(right)'s error with both operands kept (ERROR_NO_POP), and otherwise replaces right by the bool of PyErr_GivenExceptionMatches(left, right), keeping left; the type check comes first. Both use PyTuple_Check, so an instance of a tuple subclass is checked and matched exactly as the exact tuple of its items (except T((KeyError, ValueError)) catches a ValueError)."
    source := "Python/bytecodes.c:3441-3453; _PyEval_CheckExceptTypeValid, Python/ceval.c:3340-3363; PyErr_GivenExceptionMatches, Python/errors.c:331-370"
    status := .proven, prop := ``CheckExcMatchSpec, thm := some ``checkExcMatchSpec_proven },
  { id := "bytecode-check-eg-match", pyFile := "Python/bytecodes.c"
    pyFns := [op "CHECK_EG_MATCH", "_PyEval_ExceptionGroupMatch"]
    statement := "For every object model: CHECK_EG_MATCH on (exc_value, match_type) raises _PyEval_CheckExceptStarTypeValid's error, then _PyEval_ExceptionGroupMatch's, with both operands popped; otherwise (match, rest) replace them, match on top, and a match that is not None becomes tstate->exc_info->exc_value, whatever it is. _PyEval_ExceptionGroupMatch gives (None, None) for None; on a full PyErr_GivenExceptionMatches match, the group itself or the naked exception wrapped by _PyExc_CreateExceptionGroup, rest None; for a group that does not match, it calls the group's split attribute with match_type and requires an exact tuple (TypeError 'T.split must return a tuple, not U') of at least two items (TypeError 'T.split must return a 2-tuple, got tuple of size n'), whose first two items are (match, rest) unchecked; the attribute's and the call's errors propagate; anything else gives (None, exc_value)."
    source := "Python/bytecodes.c:3415-3439; _PyEval_ExceptionGroupMatch, Python/ceval.c:2263-2348; _PyErr_SetHandledException, Python/errors.c:619-622"
    status := .proven, prop := ``CheckEgMatchSpec, thm := some ``checkEgMatchSpec_proven
    notes := "The wrapping of a naked exception (PyTuple_Pack, _PyExc_CreateExceptionGroup, the traceback from the frame) is the egWrap oracle." },
  { id := "bytecode-eg-match-handled", pyFile := "Python/bytecodes.c"
    pyFns := [op "CHECK_EG_MATCH", "_PyEval_ExceptionGroupMatch"]
    statement := "CHECK_EG_MATCH keeps the handled exception (tstate->exc_info->exc_value) NULL or an exception instance. False: for an ExceptionGroup subclass whose split() returns (1, None) the int 1 is installed by PyErr_SetHandledException, sys.exception() returns it, and the next raise in the handler crashes in PyException_GetContext."
    source := "invariant: sys.exception() returns the exception instance being handled; Python/ceval.c:2339-2340, Python/bytecodes.c:3434-3436"
    status := .refuted, prop := ``EgMatchHandledIsException, thm := some ``egMatchHandledIsException_refuted
    bug := some "bytecode-eg-match-split-items-unchecked" },
  { id := "bytecode-reraise", pyFile := "Python/bytecodes.c"
    pyFns := [op "RERAISE"]
    statement := "For every stack (values[oparg], exc): RERAISE re-raises exc through exception_unwind (no traceback entry for this instruction), leaving the oparg values; with oparg != 0 it first sets frame->instr_ptr to the offset tagged in values[0] (lasti), with oparg = 0 it leaves the frame alone."
    source := "Python/bytecodes.c:1918-1929"
    status := .proven, prop := ``ReraiseRules, thm := some ``reraiseRules_proven },
  { id := "bytecode-cleanup-throw", pyFile := "Python/bytecodes.c"
    pyFns := [op "CLEANUP_THROW"]
    statement := "For every object model: CLEANUP_THROW on (sub_iter, null_in, last_sent_val, exc_value) replaces the four by (None, null_in, exc_value.value) when PyErr_GivenExceptionMatches(exc_value, StopIteration) (a subclass included), and otherwise re-raises exc_value through exception_unwind (the model pops the four first; in C the unwinding to the handler's depth, below them, pops them)."
    source := "Python/bytecodes.c:1960-1978"
    status := .proven, prop := ``CleanupThrowRules, thm := some ``cleanupThrowRules_proven },
  -- `async for` (SpecAsync.lean).
  { id := "bytecode-get-aiter", pyFile := "Python/bytecodes.c"
    pyFns := [op "GET_AITER"]
    statement := "For every object model, GET_AITER replaces obj by am_aiter's result and pops it on failure; and for every inner object model, the protocol the difftest model installs (getAIterImpl): no __aiter__ on the type gives TypeError \"'async for' requires an object with __aiter__ method, got T\" (%.100s), the lookup's or call's error propagates, a result whose type has no __anext__ gives TypeError \"'async for' received an object from __aiter__ that does not implement __anext__: U\", and otherwise the result is pushed as it is."
    source := "Python/bytecodes.c:1607-1641; slot_am_aiter, Objects/typeobject.c"
    status := .proven, prop := ``GetAIterRules, thm := some ``getAIterRules_proven
    notes := "Scope limit: the builtin async iterators (async_generator and its asend objects) have no am_aiter/am_anext in the difftest object model, so async for over an async generator object is a TypeError there; the instruction statement holds for every object model." },
  { id := "bytecode-get-anext", pyFile := "Python/bytecodes.c"
    pyFns := [op "GET_ANEXT", "_PyEval_GetANext"]
    statement := "For every object model, GET_ANEXT pushes _PyEval_GetANext(aiter) above aiter and keeps aiter when it fails (ERROR_NO_POP); and for every inner object model, _PyEval_GetANext (getANextImpl): no __anext__ gives TypeError \"'async for' requires an iterator with __anext__ method, got T\", the lookup's or call's error propagates, the result goes through _PyCoro_GetAwaitableIter and any exception it raises (not only a TypeError) becomes __cause__ and __context__ of TypeError \"'async for' received an invalid object from __anext__: U\", raised without further chaining (_PyErr_FormatFromCause)."
    source := "Python/bytecodes.c:1643-1649; _PyEval_GetANext, Python/ceval.c:3557-3594; _PyErr_FormatFromCause, Python/errors.c"
    status := .proven, prop := ``GetANextRules, thm := some ``getANextRules_proven
    notes := "The PyAsyncGen_CheckExact fast path (:3563-3565) is outside the difftest model (see bytecode-get-aiter); the model previously wrapped only a TypeError and chained __context__ to the handled exception." }
]

end PyLean.Bytecode
