import PyLean.Registry
import PyLean.Sequences.Diff
import PyLean.Sequences.DequeProps
import PyLean.Sequences.Subscript
import PyLean.Sequences.Index

/-!
`collections.deque` (`Modules/_collectionsmodule.c`), `list` (`Objects/listobject.c`) and `array` (`Modules/arraymodule.c`) sequence methods, CPython 3.14.7.
-/

namespace PyLean.Sequences

open PyLean.Registry

def entries : List Entry := []

end PyLean.Sequences
