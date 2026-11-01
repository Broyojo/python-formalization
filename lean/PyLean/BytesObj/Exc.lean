import PyLean.Core

/-!
`PyErr_ExceptionMatches`: the C code tests an exception against a class, and a subclass matches. An
exception in the models is a class name, so the hierarchy is a table of the built-in classes that
are subclasses of a class some C code tests, and of the difftest's own subclasses.
-/

namespace PyLean.BytesObj

open PyLean

/-- The classes above `cls` that some C code tests for, nearest first. -/
def excBases : String → List String
  | "ModuleNotFoundError" => ["ImportError"]
  | "UnicodeDecodeError" | "UnicodeEncodeError" | "UnicodeTranslateError" => ["UnicodeError", "ValueError"]
  | "UnicodeError" => ["ValueError"]
  | "TSub" => ["TypeError"]
  | "VSub" => ["ValueError"]
  | "OSub" => ["OverflowError"]
  | "ISub" => ["ImportError"]
  | "MSub" => ["MemoryError"]
  | _ => []

/-- `PyErr_ExceptionMatches(cls)`, Python/errors.c: the class itself or a subclass. -/
def excMatches (e : PyExc) (cls : String) : Bool :=
  e.className == cls || (excBases e.className).contains cls

end PyLean.BytesObj
