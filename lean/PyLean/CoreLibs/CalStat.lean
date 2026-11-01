import PyLean.Registry
import PyLean.CoreLibs.CalStat.Diff
import PyLean.CoreLibs.CalStat.CalEntries
import PyLean.CoreLibs.CalStat.StatEntries

/-! Registry for the `CalStat` area of CoreLibs: Lib/calendar.py, Lib/statistics.py, CPython 3.14.7. -/

namespace PyLean.CoreLibs.CalStat

open PyLean.Registry

def entries : List Entry := calendarEntries ++ statisticsEntries

end PyLean.CoreLibs.CalStat
