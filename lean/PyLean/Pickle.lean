import PyLean.Registry
import PyLean.Pickle.Diff
import PyLean.Pickle.SaveLongProps
import PyLean.Pickle.LongLineProps
import PyLean.Pickle.DecProps

/-!
`Lib/pickle.py` vs `Modules/_pickle.c`, CPython 3.14.7.
-/

namespace PyLean.Pickle

open PyLean.Registry

def entries : List Entry := []

end PyLean.Pickle
