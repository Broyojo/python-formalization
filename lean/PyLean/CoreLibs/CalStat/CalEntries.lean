import PyLean.Registry
import PyLean.CoreLibs.CalStat.CalHtmlProps

/-! Registry entries for `Lib/calendar.py`. -/

namespace PyLean.CoreLibs.CalStat

open PyLean.Registry

private def cal (id : String) (fns : List String) (st src : String) (p t : Lean.Name) : Entry :=
  { id := "calstat-calendar-" ++ id, pyFile := "calendar.py", pyFns := fns, statement := st,
    source := src, status := .proven, prop := p, thm := some t }

def calendarEntries : List Entry := [
  cal "leapdays-count" ["leapdays", "isleap"]
    "For all ints y1 <= y2, leapdays(y1, y2) equals the number of y in range(y1, y2) with isleap(y)."
    "docstring of leapdays" ``LeapdaysCount ``leapdaysCount_proven,
  cal "isleap-cycle" ["isleap", "leapdays"]
    "isleap has period 400 and leapdays(y, y+400) == 97 for every int y."
    "invariant (Gregorian cycle)" ``IsleapCycle ``isleapCycle_proven,
  cal "weekday-cycle" ["weekday"]
    "weekday results are in 0..6, and adding any multiple of 400 to the year keeps the result, for all int years; so the substitution 2000 + year % 400 is exact."
    "invariant; calendar.py:177-178" ``WeekdayCycle ``weekdayCycle_proven,
  cal "weekday-next-day" ["weekday", "_nextmonth"]
    "Consecutive days have consecutive weekdays in every int year, also over month and year ends and across years 0 and 10000."
    "invariant" ``WeekdayNextDay ``weekdayNextDay_proven,
  cal "monthrange-spec" ["monthrange", "_monthlen", "_validate_month", "IllegalMonthError.__init__",
      "IllegalMonthError.__str__"]
    "For 1 <= month <= 12 and every int year, monthrange returns (weekday of the 1st, length), in 0..6 and 28..31, February has 29 days exactly in leap years, _monthlen agrees; any other month raises IllegalMonthError with the source's message."
    "docstring of monthrange" ``MonthrangeSpec ``monthrangeSpec_proven,
  cal "monthrange-chain" ["monthrange", "_nextmonth"]
    "The first weekday of the next month is (first weekday + length) % 7 for every int year."
    "invariant" ``MonthrangeChain ``monthrangeChain_proven,
  cal "prev-next-month" ["_prevmonth", "_nextmonth"]
    "_prevmonth and _nextmonth map month 1..12 into 1..12 and invert each other."
    "invariant" ``PrevNextMonth ``prevNextMonth_proven,
  cal "firstweekday-modulo" ["Calendar.__init__", "Calendar.getfirstweekday",
      "Calendar.setfirstweekday", "Calendar.iterweekdays"]
    "For every int first weekday, getfirstweekday is that int mod 7 and iterweekdays is a permutation of 0..6 starting there; fw and fw + 7 give the same week."
    "docstring of iterweekdays; calendar.py:223" ``FirstweekdayModulo ``firstweekdayModulo_proven,
  cal "itermonthdays-shape" ["Calendar.itermonthdays"]
    "itermonthdays yields 28 to 42 entries, a multiple of 7, whose non-zero entries are exactly 1..ndays, for every int year and first weekday."
    "docstring" ``ItermonthdaysShape ``itermonthdaysShape_proven,
  cal "itermonthdays-vs-3" ["Calendar.itermonthdays", "Calendar.itermonthdays3"]
    "itermonthdays equals itermonthdays3 with entries of adjacent months replaced by 0."
    "docstrings (method vs equivalent method)" ``ItermonthdaysVs3 ``itermonthdaysVs3_proven,
  cal "itermonthdays2-weekday" ["Calendar.itermonthdays2"]
    "Every (d, wd) of itermonthdays2 has wd in 0..6 and, for d != 0, wd == weekday(year, month, d)."
    "docstring" ``Itermonthdays2Weekday ``itermonthdays2Weekday_proven,
  cal "itermonthdays4-weekday" ["Calendar.itermonthdays4", "Calendar.itermonthdays3", "_monthlen",
      "_prevmonth"]
    "Every (y, m, d, wd) of itermonthdays4 is a valid day of a valid month with wd == weekday(y, m, d), also in the adjacent months and outside datetime's year range."
    "docstring: Can be used for dates outside of datetime.date range" ``Itermonthdays4Weekday
    ``itermonthdays4Weekday_proven,
  cal "itermonthdays3-consecutive" ["Calendar.itermonthdays3"]
    "itermonthdays3 yields consecutive days, in complete weeks, starting on the first weekday."
    "docstring of itermonthdates (always iterates through complete weeks)" ``Itermonthdays3Consecutive
    ``itermonthdays3Consecutive_proven,
  cal "itermonthdates-restricted" ["Calendar.itermonthdates"]
    "itermonthdates equals itermonthdays3 when all years are in 1..9999, and raises otherwise."
    "Doc/library/calendar.rst (not restricted by the datetime.date range)" ``ItermonthdatesRestricted
    ``itermonthdatesRestricted_proven,
  cal "month-matrices" ["Calendar.monthdayscalendar", "Calendar.monthdays2calendar"]
    "Month matrices have 4 to 6 weeks of exactly 7 entries and flatten to the iterators."
    "docstrings" ``MonthMatrices ``monthMatrices_proven,
  cal "month-dates-matrix" ["Calendar.monthdatescalendar"]
    "When it succeeds, monthdatescalendar has 4 to 6 weeks of 7 dates that flatten to itermonthdates."
    "docstring" ``MonthDatesMatrix ``monthDatesMatrix_proven,
  cal "year-matrices" ["Calendar.yeardatescalendar", "Calendar.yeardays2calendar",
      "Calendar.yeardayscalendar"]
    "Year matrices are rows of at most width months that flatten to January..December; width 0 raises ValueError from range(), a negative width gives no rows."
    "docstrings" ``YearMatrices ``yearMatrices_proven,
  cal "timegm-ordinal" ["timegm"]
    "timegm(1970, 1, 1, 0, 0, 0) == 0, and for a valid date timegm is (toordinal - epoch)*86400 + h*3600 + m*60 + s."
    "docstring; Doc/library/calendar.rst" ``TimegmOrdinal ``timegmOrdinal_proven,
  cal "timegm-roundtrip" ["timegm"]
    "For t >= 0 up to the end of year 9999, converting t to a date with date.fromordinal and a time of day, and calling timegm, gives t back."
    "Doc/library/calendar.rst (inverse of gmtime)" ``TimegmRoundtrip ``timegmRoundtrip_proven,
  cal "text-week-width" ["TextCalendar.formatday", "TextCalendar.formatweek", "TextCalendar.prweek"]
    "A week of n day numbers below 100 formats to exactly n*w + n-1 characters for w >= 2; prweek prints it."
    "invariant (columns line up)" ``TextWeekWidth ``textWeekWidth_proven,
  cal "text-header-width" ["TextCalendar.formatweekday", "TextCalendar.formatweekheader"]
    "For every first weekday and any locale table of seven names, formatweekheader(w) succeeds and has 7*w + 6 characters."
    "invariant (columns line up)" ``TextHeaderWidth ``textHeaderWidth_proven,
  cal "formatstring-width" ["formatstring", "format"]
    "n columns no wider than colwidth give n*colwidth + (n-1)*spacing characters; format prints that and a newline."
    "docstring of formatstring" ``FormatstringWidth ``formatstringWidth_proven,
  cal "formatmonth-lines" ["TextCalendar.formatmonth", "TextCalendar.prmonth"]
    "formatmonth has a title line, a header line and one line per week, each followed by max(1, l) newlines; prmonth prints the same text."
    "docstring" ``FormatmonthLines ``formatmonthLines_proven,
  cal "formatmonthname" ["TextCalendar.formatmonthname", "HTMLCalendar.formatmonthname"]
    "Both formatmonthname raise IllegalMonthError for a month outside 1..12, including 0; a valid month gives the centred name."
    "calendar.py:397, :511" ``FormatmonthnameSpec ``formatmonthnameSpec_proven,
  cal "formatyear-lines" ["TextCalendar.formatyear", "TextCalendar.pryear"]
    "For m >= 1, formatyear has a title block and, per month row, a blank block, a names line, a header line and height week lines, each followed by max(1, l) newlines; pryear prints the same."
    "docstring" ``FormatyearLines ``formatyearLines_proven,
  cal "text-year-months" ["TextCalendar.formatyear"]
    "For every m >= 1 the months computed for row i at calendar.py:441 are the months yeardays2calendar lays out in row i."
    "invariant" ``TextYearMonths ``textYearMonths_proven,
  cal "formatyear-month-count" ["TextCalendar.formatyear", "HTMLCalendar.formatyear"]
    "TextCalendar.formatyear with m == 0 raises the ValueError of range(); HTMLCalendar.formatyear with width <= 0 behaves as width 1."
    "calendar.py:561, :551; actual behaviour of the two clamps" ``FormatyearMonthCount
    ``formatyearMonthCount_proven,
  cal "demo-colours" ["_CLIDemoCalendar.formatday", "_CLIDemoCalendar.formatweekheader",
      "_CLIDemoCalendar.formatmonthname"]
    "For any theme, the highlighted day is wrapped and no other; the week header is wrapped in weekday; a month name is wrapped in header, or for the highlighted month its stripped text in highlight, inside the padding; and the failure of the plain formatter is the outcome."
    "Lib/calendar.py:693-742" ``DemoColours ``demoColours_proven,
  cal "demo-week-exact" ["_CLIDemoCalendar.formatweek", "TextCalendar.formatday", "TextCalendar.formatweek"]
    "A week of _CLIDemoCalendar is the cells of TextCalendar joined by one space, with the highlighted day wrapped and no other."
    "Lib/calendar.py:361-375, :693-715" ``DemoWeekExact ``demoWeekExact_proven,
  cal "text-weekday-exact" ["TextCalendar.formatweekday"]
    "formatweekday is the full name when width holds the longest one, the abbreviation otherwise, cut to width and centred, for any table of seven names."
    "Lib/calendar.py:377-385" ``TextWeekdayExact ``textWeekdayExact_proven,
  cal "monthname-exact" ["TextCalendar.formatmonthname", "HTMLCalendar.formatmonthname"]
    "Both formatmonthname use the standalone name of that month, with the year when asked; the text one centres it and the HTML one puts it in the month heading."
    "Lib/calendar.py:393-402, :525-534" ``MonthNameExact ``monthNameExact_proven,
  cal "html-cells-exact" ["HTMLCalendar.formatday", "HTMLCalendar.formatweek", "HTMLCalendar.formatweekday",
      "HTMLCalendar.formatweekheader"]
    "A day outside the month is the noday cell, a day is a cell with the class of its weekday and its number, a weekday past the table is an IndexError, a week is its cells in order and the header is the abbreviations in the order of iterweekdays."
    "Lib/calendar.py:495-523" ``HtmlCellsExact ``htmlCellsExact_proven,
  cal "html-month-exact" ["HTMLCalendar.formatmonth"]
    "formatmonth is the table, its name row, its header row and the rows of monthdays2calendar, each on a line of its own, and the first failure in that order."
    "Lib/calendar.py:536-553" ``HtmlMonthExact ``htmlMonthExact_proven,
  cal "html-year-exact" ["HTMLCalendar.formatyear"]
    "formatyear counts a width below one as one, its heading spans that many columns, and each row holds the month tables without the year."
    "Lib/calendar.py:555-575" ``HtmlYearExact ``htmlYearExact_proven,
  cal "html-page-exact" ["HTMLCalendar._format_html_page", "HTMLCalendar.formatyearpage", "HTMLCalendar.formatmonthpage"]
    "The content sits in the body of the page, the stylesheet line is there exactly when css is given, None means UTF-8, an unknown encoding is a LookupError, and a failed content comes first."
    "Lib/calendar.py:577-617" ``HtmlPageExact ``htmlPageExact_proven,
  cal "demo-is-text" ["_CLIDemoCalendar.__init__", "_CLIDemoCalendar.formatweek",
      "_CLIDemoCalendar.formatmonth", "_CLIDemoLocaleCalendar.__init__"]
    "Without a highlighted day in view, or with colours off, _CLIDemoCalendar returns exactly what TextCalendar returns."
    "twin: subclass vs base class" ``DemoIsText ``demoIsText_proven,
  cal "demo-year-column" []
    "In a row of distinct months, formatweek gets the highlighted day exactly in the column of the highlighted month."
    "calendar.py:795-817" ``DemoYearColumn ``demoYearColumn_proven,
  cal "html-month-lines" ["HTMLCalendar.formatday", "HTMLCalendar.formatweek",
      "HTMLCalendar.formatweekday", "HTMLCalendar.formatweekheader", "HTMLCalendar.formatmonth"]
    "formatmonth succeeds for every year and first weekday and has one line each for the table tag, the name row, the header row, each week and the closing tag."
    "docstring" ``HtmlMonthLines ``htmlMonthLines_proven,
  cal "html-year-months" ["HTMLCalendar.formatyear"]
    "For every width >= 1 the rows of formatyear hold January..December exactly once, at most width per row."
    "docstring; calendar.py:565-567" ``HtmlYearMonths ``htmlYearMonths_proven,
  cal "xmlcharref-ascii" ["HTMLCalendar.formatyearpage"]
    "encode(ascii, xmlcharrefreplace) gives only ASCII and leaves ASCII unchanged, so formatyearpage(encoding='ascii') is pure ASCII for every css."
    "calendar.py:603" ``XmlcharrefAscii ``xmlcharrefAscii_proven,
  cal "different-locale-restores" ["different_locale.__init__", "different_locale.__enter__",
      "different_locale.__exit__"]
    "If the locale can be set, the body runs under it and LC_TIME is restored afterwards, also after an exception in the body; otherwise locale.Error is raised and nothing changed."
    "with-statement contract" ``DifferentLocaleRestores ``differentLocaleRestores_proven,
  cal "get-default-locale" ["_get_default_locale", "LocaleTextCalendar.__init__",
      "LocaleHTMLCalendar.__init__"]
    "_get_default_locale is the current LC_TIME, or the user's locale when that is C; the calendars keep an explicit locale."
    "calendar.py:633-640" ``GetDefaultLocaleSpec ``getDefaultLocaleSpec_proven,
  cal "locale-calendar-methods" ["LocaleTextCalendar.formatweekday", "LocaleTextCalendar.formatmonthname",
      "LocaleHTMLCalendar.formatweekday", "LocaleHTMLCalendar.formatmonthname"]
    "The overridden locale methods return the base method with that locale's names and leave LC_TIME unchanged."
    "docstrings of the locale classes" ``LocaleCalendarMethods ``localeCalendarMethods_proven,
  cal "main-checks" ["main"]
    "main exits with status 2 for --locale without --encoding and for a month with -t html, and raises IllegalMonthError for a bad month in text mode."
    "calendar.py:945-982" ``MainChecks ``mainChecks_proven,
  cal "main-month-output" ["main"]
    "python -m calendar YEAR MONTH prints _CLIDemoCalendar.formatmonth; for another month than today's, that is TextCalendar.formatmonth."
    "calendar.py:983-993" ``MainMonthOutput ``mainMonthOutput_proven,
  cal "setfirstweekday" ["setfirstweekday", "IllegalWeekdayError.__init__", "IllegalWeekdayError.__str__"]
    "Module setfirstweekday stores 0..6 and raises IllegalWeekdayError with the source's message otherwise."
    "Doc/library/calendar.rst" ``SetfirstweekdaySpec ``setfirstweekdaySpec_proven,
  cal "module-getattr" ["__getattr__"]
    "calendar.January and calendar.February are 1 and 2; other missing names raise AttributeError."
    "calendar.py:47-57" ``ModuleGetattrSpec ``moduleGetattrSpec_proven,
  cal "localized-tables" ["_localized_month.__init__", "_localized_month.__getitem__",
      "_localized_month.__len__", "_localized_day.__init__", "_localized_day.__getitem__",
      "_localized_day.__len__"]
    "month_name and day_name have lengths 13 and 7, month 0 is empty, negative indices count from the end, out-of-range is IndexError, [:] is the whole table, and date(2001, 1, i+1) is weekday i."
    "calendar.py:97-132" ``LocalizedTables ``localizedTables_proven
]

end PyLean.CoreLibs.CalStat
