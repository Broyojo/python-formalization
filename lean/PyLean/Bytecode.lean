import PyLean.Registry
import PyLean.Bytecode.Diff

/-!
The bytecode virtual machine: `Python/bytecodes.c`, `Python/ceval.c`, `Python/intrinsics.c`, CPython 3.14.7.
-/

namespace PyLean.Bytecode

open PyLean.Registry

def entries : List Entry := []

end PyLean.Bytecode
