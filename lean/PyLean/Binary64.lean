import PyLean.Registry
import PyLean.Binary64.Model
import PyLean.Binary64.Bigint
import PyLean.Binary64.Float
import PyLean.Binary64.Strtod
import PyLean.Binary64.Dtoa
import PyLean.Binary64.Diff

/-!
Shared exact IEEE-754 binary64 model, and `Objects/floatobject.c`, `Python/dtoa.c`, `Python/pystrtod.c`, CPython 3.14.7.
-/

namespace PyLean.Binary64

open PyLean.Registry

def entries : List Entry := []

end PyLean.Binary64
