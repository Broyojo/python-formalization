import PyLean.Registry
import PyLean.CoreLibs.Diff
import PyLean.CoreLibs.Coll
import PyLean.CoreLibs.CollAbc
import PyLean.CoreLibs.Functools
import PyLean.CoreLibs.Operator
import PyLean.CoreLibs.EnumDC
import PyLean.CoreLibs.Misc
import PyLean.CoreLibs.CalStat
import PyLean.CoreLibs.Rand
import PyLean.CoreLibs.Warn

/-!
Core libraries, CPython 3.15.2. One area per group of source files:
* `Coll`: Lib/collections/__init__.py (everything except OrderedDict)
* `CollAbc`: Lib/_collections_abc.py, Lib/collections/abc.py
* `Functools`: Lib/functools.py, Modules/_functoolsmodule.c
* `Operator`: Lib/operator.py, Modules/_operator.c, Lib/copy.py, Lib/abc.py
* `EnumDC`: Lib/enum.py, Lib/dataclasses.py
* `Misc`: Lib/contextlib.py, Lib/numbers.py, Lib/keyword.py, Lib/types.py, Lib/weakref.py, Lib/graphlib.py, Lib/sched.py, Lib/queue.py
* `CalStat`: Lib/calendar.py, Lib/statistics.py
* `Rand`: Lib/random.py, Modules/_randommodule.c
* `Warn`: Python/_warnings.c, Lib/_py_warnings.py (`warn_explicit`)
-/

namespace PyLean.CoreLibs

open PyLean.Registry

def entries : List Entry :=
  Coll.entries ++
  CollAbc.entries ++
  Functools.entries ++
  Operator.entries ++
  EnumDC.entries ++
  Misc.entries ++
  CalStat.entries ++
  Rand.entries ++
  Warn.entries

end PyLean.CoreLibs
