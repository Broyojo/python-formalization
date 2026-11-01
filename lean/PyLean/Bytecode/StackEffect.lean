import PyLean.Bytecode.Exec

/-!
Stack effects against the generated metadata. For a representative set of opcodes,
the step rule pops exactly `_PyOpcode_num_popped(op, oparg)` values and pushes
`_PyOpcode_num_pushed(op, oparg)`, leaving the rest of the stack unchanged, for
every stack and every `oparg`. The tables are generated from
`Include/internal/pycore_opcode_metadata.h`; the step rules mirror
`Python/bytecodes.c`. Each proof is by definitional reduction: `execOp e op`
reduces to the opcode's `stk`/`stkK` combinator, whose effect is exactly its
declared `(pop, push)` numbers (`eff_stk`, `eff_stkK` in `Stack.lean`), and
`numPopped`/`numPushed` reduce to those same numbers.

These proofs read only the `(pop, push)` annotation of `stk`, so they hold for any
body: they check the annotations against the metadata, and they are not coverage of
any opcode. The registry entry is `.open`.

The full 398-opcode version is future work; the peek-and-dispatch opcodes
(`FOR_ITER`, `SEND`, `WITH_EXCEPT_START`, `RERAISE`, `END_ASYNC_FOR`,
`CLEANUP_THROW`), the two super-instructions (`CALL_LIST_APPEND`,
`BINARY_OP_INPLACE_ADD_UNICODE`), and the frame-leaving opcodes each need their
own treatment and are noted here rather than covered by one uniform theorem.
-/

namespace PyLean.Bytecode

open Uop

/-- `Eff p q (execOp e op)` for a fixed opcode, read off the metadata. Proof is
`exact eff_stk _ _ _` / `exact eff_stkK _ _ _` up to definitional reduction. -/
theorem eff_pop_top (e : Env) :
    Eff (numPopped .POP_TOP e.oparg) (numPushed .POP_TOP e.oparg) (execOp e .POP_TOP) :=
  eff_stk _ _ _
theorem eff_push_null (e : Env) :
    Eff (numPopped .PUSH_NULL e.oparg) (numPushed .PUSH_NULL e.oparg) (execOp e .PUSH_NULL) :=
  eff_stk _ _ _
theorem eff_end_for (e : Env) :
    Eff (numPopped .END_FOR e.oparg) (numPushed .END_FOR e.oparg) (execOp e .END_FOR) :=
  eff_stk _ _ _
theorem eff_load_fast (e : Env) :
    Eff (numPopped .LOAD_FAST e.oparg) (numPushed .LOAD_FAST e.oparg) (execOp e .LOAD_FAST) :=
  eff_stk _ _ _
theorem eff_load_small_int (e : Env) :
    Eff (numPopped .LOAD_SMALL_INT e.oparg) (numPushed .LOAD_SMALL_INT e.oparg)
      (execOp e .LOAD_SMALL_INT) :=
  eff_stk _ _ _
theorem eff_store_fast (e : Env) :
    Eff (numPopped .STORE_FAST e.oparg) (numPushed .STORE_FAST e.oparg) (execOp e .STORE_FAST) :=
  eff_stk _ _ _
theorem eff_store_fast_store_fast (e : Env) :
    Eff (numPopped .STORE_FAST_STORE_FAST e.oparg) (numPushed .STORE_FAST_STORE_FAST e.oparg)
      (execOp e .STORE_FAST_STORE_FAST) :=
  eff_stk _ _ _
theorem eff_unary_not (e : Env) :
    Eff (numPopped .UNARY_NOT e.oparg) (numPushed .UNARY_NOT e.oparg) (execOp e .UNARY_NOT) :=
  eff_stk _ _ _
theorem eff_unary_negative (e : Env) :
    Eff (numPopped .UNARY_NEGATIVE e.oparg) (numPushed .UNARY_NEGATIVE e.oparg)
      (execOp e .UNARY_NEGATIVE) :=
  eff_stk _ _ _
theorem eff_build_tuple (e : Env) :
    Eff (numPopped .BUILD_TUPLE e.oparg) (numPushed .BUILD_TUPLE e.oparg) (execOp e .BUILD_TUPLE) :=
  eff_stk _ _ _
theorem eff_build_list (e : Env) :
    Eff (numPopped .BUILD_LIST e.oparg) (numPushed .BUILD_LIST e.oparg) (execOp e .BUILD_LIST) :=
  eff_stk _ _ _
theorem eff_build_set (e : Env) :
    Eff (numPopped .BUILD_SET e.oparg) (numPushed .BUILD_SET e.oparg) (execOp e .BUILD_SET) :=
  eff_stk _ _ _
theorem eff_build_string (e : Env) :
    Eff (numPopped .BUILD_STRING e.oparg) (numPushed .BUILD_STRING e.oparg) (execOp e .BUILD_STRING) :=
  eff_stk _ _ _
theorem eff_build_map (e : Env) :
    Eff (numPopped .BUILD_MAP e.oparg) (numPushed .BUILD_MAP e.oparg) (execOp e .BUILD_MAP) :=
  eff_stk _ _ _
theorem eff_build_slice (e : Env) :
    Eff (numPopped .BUILD_SLICE e.oparg) (numPushed .BUILD_SLICE e.oparg) (execOp e .BUILD_SLICE) :=
  eff_stk _ _ _
theorem eff_get_iter (e : Env) :
    Eff (numPopped .GET_ITER e.oparg) (numPushed .GET_ITER e.oparg) (execOp e .GET_ITER) :=
  eff_stk _ _ _
theorem eff_get_aiter (e : Env) :
    Eff (numPopped .GET_AITER e.oparg) (numPushed .GET_AITER e.oparg) (execOp e .GET_AITER) :=
  eff_stk _ _ _
theorem eff_is_op (e : Env) :
    Eff (numPopped .IS_OP e.oparg) (numPushed .IS_OP e.oparg) (execOp e .IS_OP) :=
  eff_stk _ _ _
theorem eff_delete_subscr (e : Env) :
    Eff (numPopped .DELETE_SUBSCR e.oparg) (numPushed .DELETE_SUBSCR e.oparg)
      (execOp e .DELETE_SUBSCR) :=
  eff_stk _ _ _
theorem eff_get_len (e : Env) :
    Eff (numPopped .GET_LEN e.oparg) (numPushed .GET_LEN e.oparg) (execOp e .GET_LEN) :=
  eff_stkK _ _ _
theorem eff_match_keys (e : Env) :
    Eff (numPopped .MATCH_KEYS e.oparg) (numPushed .MATCH_KEYS e.oparg) (execOp e .MATCH_KEYS) :=
  eff_stkK _ _ _
theorem eff_import_from (e : Env) :
    Eff (numPopped .IMPORT_FROM e.oparg) (numPushed .IMPORT_FROM e.oparg) (execOp e .IMPORT_FROM) :=
  eff_stkK _ _ _
theorem eff_check_exc_match (e : Env) :
    Eff (numPopped .CHECK_EXC_MATCH e.oparg) (numPushed .CHECK_EXC_MATCH e.oparg)
      (execOp e .CHECK_EXC_MATCH) :=
  eff_stkK _ _ _
theorem eff_import_name (e : Env) :
    Eff (numPopped .IMPORT_NAME e.oparg) (numPushed .IMPORT_NAME e.oparg) (execOp e .IMPORT_NAME) :=
  eff_stk _ _ _

end PyLean.Bytecode
