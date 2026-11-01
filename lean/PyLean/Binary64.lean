import PyLean.Registry
import PyLean.Binary64.Diff

/-!
Shared exact IEEE-754 binary64 model, and `Objects/floatobject.c`, `Python/dtoa.c`, `Python/pystrtod.c`, CPython 3.14.7.
-/

namespace PyLean.Binary64

open PyLean.Registry

def entries : List Entry := []

end PyLean.Binary64
