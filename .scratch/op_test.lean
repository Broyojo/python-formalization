import PyLean.Bytecode.Opcode
open PyLean.Bytecode
example : (Op.BINARY_OP_ADD_INT).deopt = .BINARY_OP := rfl
example : numPopped .CALL 3 = 5 := rfl
example : numPushed .UNPACK_EX 0x0102 = 1 + 2 + 1 := rfl
example : Op.ofNat? 128 = some .RESUME := by native_decide
#eval (Op.BINARY_OP).toNat
#eval (Op.ofNat? 44)
