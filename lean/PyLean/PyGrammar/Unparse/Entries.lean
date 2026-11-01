import PyLean.Registry

/-! Registry entries for the `Unparse` part of `PyGrammar`. The round trip needs the parser, so
it sits in `Peg/Entries.lean`, which imports both. -/

namespace PyLean.PyGrammar.Unparse

open PyLean.Registry

def entries : List Entry := []

end PyLean.PyGrammar.Unparse
