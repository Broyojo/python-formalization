import PyLean

/-! Every module's registry entries, for `Audit.lean` and `Report.lean`. -/

def PyLean.allEntries : List PyLean.Registry.Entry :=
  PyLean.Ipaddress.entries ++
  PyLean.Datetime.entries ++
  PyLean.Fractions.entries ++
  PyLean.RangeSlice.entries ++
  PyLean.MathInt.entries ++
  PyLean.StrSearch.entries ++
  PyLean.Accel.entries ++
  PyLean.Decimal.entries ++
  PyLean.PyIO.entries ++
  PyLean.JsonMod.entries ++
  PyLean.Pickle.entries ++
  PyLean.Itertools.entries ++
  PyLean.Sequences.entries ++
  PyLean.ListSort.entries ++
  PyLean.Binary64.entries ++
  PyLean.DictSet.entries ++
  PyLean.LongObj.entries ++
  PyLean.BytesObj.entries ++
  PyLean.UnicodeObj.entries ++
  PyLean.TypeObj.entries ++
  PyLean.Bytecode.entries ++
  PyLean.PyGrammar.entries ++
  PyLean.TextLibs.entries ++
  PyLean.CoreLibs.entries
