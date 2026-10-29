import PyLean.Registry
import PyLean.Accel.Diff

/-!
C accelerators vs. their pure-Python twins: `bisect` (`Modules/_bisectmodule.c`) and `heapq` (`Modules/_heapqmodule.c`), CPython 3.14.7.
-/

namespace PyLean.Accel

open PyLean.Registry

def entries : List Entry := []

end PyLean.Accel
