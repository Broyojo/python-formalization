import PyLean.DiffCore
import PyLean.CoreLibs.CalStat.CalFmt

/-! Differential-test dispatch for the `calendar` half of the area. -/

namespace PyLean.CoreLibs.CalStat

open Lean PyLean PyLean.Diff

def encS (s : Str) : Json := toJson (String.ofList s)
def encIL (l : List Int) : Json := Json.arr (l.map toJson).toArray
def encDate (d : Date) : Json := encIL [d.1, d.2.1, d.2.2]
def encPair (p : Int × Int) : Json := encIL [p.1, p.2]
def encL {α : Type} (f : α → Json) (l : List α) : Json := Json.arr (l.map f).toArray
def encBytes (b : List Nat) : Json := toJson (String.ofList (b.map Char.ofNat))

def getS (j : Json) (k : String) : Except String Str := do return (← getStr j k).toList
def getIL (j : Json) (k : String) : Except String (List Int) := do
  let a ← (← field j k).getArr?
  a.toList.mapM (fun x => x.getInt?)
def getOptS (j : Json) (k : String) : Except String (Option Str) :=
  match j.getObjVal? k with
  | .ok .null | .error _ => .ok none
  | .ok v => do return some (← v.getStr?).toList
def getWeek (j : Json) (k : String) : Except String (List (Int × Int)) := do
  let a ← (← field j k).getArr?
  a.toList.mapM (fun p => do
    let x ← p.getArr?
    return (← (x[0]!).getInt?, ← (x[1]!).getInt?))
def getSL (j : Json) (k : String) : Except String (List Str) := do
  let a ← (← field j k).getArr?
  a.toList.mapM (fun x => do return (← x.getStr?).toList)

def getTable (j : Json) : Except String (List Str) := do
  let t ← getStr j "table"
  return match t with
    | "day_name" => cNames.dayName
    | "day_abbr" => cNames.dayAbbr
    | "month_name" => localizedMonthList cNames.monthName
    | _ => localizedMonthList cNames.monthAbbr

def testEnv (cur user : String) : LocaleEnv where
  current := cur
  userDefault := user
  supported := fun l => l == "C" || l == "C.utf8"
  names := fun _ => cNames

def testAnsi : Ansi := ⟨lit "\x1b[1m", lit "\x1b[30m\x1b[43m", lit "\x1b[36m", lit "\x1b[0m"⟩

def getHl (j : Json) : Except String Highlight := do
  match j.getObjVal? "hl" with
  | .ok .null | .error _ => return none
  | .ok _ =>
    let l ← getIL j "hl"
    return some (l[0]!, l[1]!, l[2]!)

def encMain : MainOut → Json
  | .text s => encBytes (s.flatMap utf8Bytes)
  | .bytes b => encBytes b

def getOptions (j : Json) : Except String Options := do
  return {
    width := ← getInt j "width", lines := ← getInt j "lines", spacing := ← getInt j "spacing",
    months := ← getInt j "months", css := ← getS j "css", locale := ← getOptS j "locale",
    encoding := ← getOptS j "encoding", type := ← getS j "type",
    firstWeekday := ← getInt j "fw", year := ← getOptInt j "year", month := ← getOptInt j "month" }

/-- `calendar` cases. `none` for a name that is not a calendar function. -/
def runCal (fn : String) (j : Json) : Option (Except String Json) :=
  let cal : Except String Calendar := do return ⟨← getInt j "fw"⟩
  match fn with
  | "isleap" => some do return toJson (isleap (← getInt j "y"))
  | "leapdays" => some do return toJson (leapdays (← getInt j "a") (← getInt j "b"))
  | "weekday" => some do return encPy toJson (weekday (← getInt j "y") (← getInt j "m") (← getInt j "d"))
  | "monthrange" => some do return encPy encPair (monthrange (← getInt j "y") (← getInt j "m"))
  | "_monthlen" => some do return encPy toJson (monthlen (← getInt j "y") (← getInt j "m"))
  | "_prevmonth" => some do return encPair (prevmonth (← getInt j "y") (← getInt j "m"))
  | "_nextmonth" => some do return encPair (nextmonth (← getInt j "y") (← getInt j "m"))
  | "getfirstweekday" => some do return toJson (← cal).firstweekday
  | "iterweekdays" => some do return encIL (← cal).iterweekdays
  | "itermonthdates" => some do
    return encPy (encL encDate) ((← cal).itermonthdates (← getInt j "y") (← getInt j "m"))
  | "itermonthdays" => some do
    return encPy encIL ((← cal).itermonthdays (← getInt j "y") (← getInt j "m"))
  | "itermonthdays2" => some do
    return encPy (encL encPair) ((← cal).itermonthdays2 (← getInt j "y") (← getInt j "m"))
  | "itermonthdays3" => some do
    return encPy (encL encDate) ((← cal).itermonthdays3 (← getInt j "y") (← getInt j "m"))
  | "itermonthdays4" => some do
    return encPy (encL (fun t => encIL [t.1, t.2.1, t.2.2.1, t.2.2.2]))
      ((← cal).itermonthdays4 (← getInt j "y") (← getInt j "m"))
  | "monthdatescalendar" => some do
    return encPy (encL (encL encDate)) ((← cal).monthdatescalendar (← getInt j "y") (← getInt j "m"))
  | "monthdays2calendar" => some do
    return encPy (encL (encL encPair)) ((← cal).monthdays2calendar (← getInt j "y") (← getInt j "m"))
  | "monthdayscalendar" => some do
    return encPy (encL encIL) ((← cal).monthdayscalendar (← getInt j "y") (← getInt j "m"))
  | "yeardatescalendar" => some do
    return encPy (encL (encL (encL (encL encDate))))
      ((← cal).yeardatescalendar (← getInt j "y") (← getInt j "width"))
  | "yeardays2calendar" => some do
    return encPy (encL (encL (encL (encL encPair))))
      ((← cal).yeardays2calendar (← getInt j "y") (← getInt j "width"))
  | "yeardayscalendar" => some do
    return encPy (encL (encL (encL encIL)))
      ((← cal).yeardayscalendar (← getInt j "y") (← getInt j "width"))
  | "setfirstweekday" => some do
    return encPy (fun c => toJson c.firstweekday) (setfirstweekdayModule ⟨0⟩ (← getInt j "fw"))
  | "exc_month" => some do return Json.mkObj [("msg", toJson (illegalMonth (← getInt j "m")).message)]
  | "exc_weekday" => some do return Json.mkObj [("msg", toJson (illegalWeekday (← getInt j "m")).message)]
  | "__getattr__" => some do
    return encPy (fun p => Json.arr #[toJson p.1, toJson p.2]) (moduleGetattr (← getStr j "name"))
  | "loc_get" => some do
    return encPy encS (localizedGet (← getTable j) (← getInt j "i"))
  | "loc_slice" => some do
    return encPy (encL encS) (localizedSlice (← getTable j) (← getOptInt j "start") (← getOptInt j "stop") (← getInt j "step"))
  | "loc_len" => some do
    return toJson (if (← getStr j "table").startsWith "month" then localizedMonthLen else localizedDayLen)
  | "formatstring" => some do
    return encS (formatstring (← getSL j "cols") (← getInt j "colwidth") (← getInt j "spacing"))
  | "format" => some do
    return encS (formatPrint (← getSL j "cols") (← getInt j "colwidth") (← getInt j "spacing"))
  | "timegm" => some do
    let t ← getIL j "t"
    return encPy toJson (timegm t[0]! t[1]! t[2]! t[3]! t[4]! t[5]!)
  | "t.formatday" => some do return encS (tFormatday (← getInt j "d") (← getInt j "wd") (← getInt j "width"))
  | "t.formatweek" => some do return encS (tFormatweek (← getWeek j "week") (← getInt j "width"))
  | "t.prweek" => some do return encS (tPrweek (← getWeek j "week") (← getInt j "width"))
  | "t.formatweekday" => some do return encPy encS (tFormatweekday cNames (← getInt j "d") (← getInt j "width"))
  | "t.formatweekheader" => some do return encPy encS (tFormatweekheader cNames (← cal) (← getInt j "width"))
  | "t.formatmonthname" => some do
    return encPy encS (tFormatmonthname cNames (← getInt j "y") (← getInt j "m") (← getInt j "width") (← getBool j "withyear"))
  | "t.formatmonth" => some do
    return encPy encS (tFormatmonth cNames (← cal) (← getInt j "y") (← getInt j "m") (← getInt j "w") (← getInt j "l"))
  | "t.prmonth" => some do
    return encPy encS (tPrmonth cNames (← cal) (← getInt j "y") (← getInt j "m") (← getInt j "w") (← getInt j "l"))
  | "t.formatyear" => some do
    return encPy encS (tFormatyear cNames (← cal) (← getInt j "y") (← getInt j "w") (← getInt j "l") (← getInt j "c") (← getInt j "m"))
  | "t.pryear" => some do
    return encPy encS (tPryear cNames (← cal) (← getInt j "y") (← getInt j "w") (← getInt j "l") (← getInt j "c") (← getInt j "m"))
  | "h.formatday" => some do return encPy encS (hFormatday (← getInt j "d") (← getInt j "wd"))
  | "h.formatweek" => some do return encPy encS (hFormatweek (← getWeek j "week"))
  | "h.formatweekday" => some do return encPy encS (hFormatweekday cNames (← getInt j "d"))
  | "h.formatweekheader" => some do return encPy encS (hFormatweekheader cNames (← cal))
  | "h.formatmonthname" => some do
    return encPy encS (hFormatmonthname cNames (← getInt j "y") (← getInt j "m") (← getBool j "withyear"))
  | "h.formatmonth" => some do
    return encPy encS (hFormatmonth cNames (← cal) (← getInt j "y") (← getInt j "m") (← getBool j "withyear"))
  | "h.formatyear" => some do
    return encPy encS (hFormatyear cNames (← cal) (← getInt j "y") (← getInt j "width"))
  | "h.formatyearpage" => some do
    return encPy encBytes (hFormatyearpage cNames (← cal) (← getInt j "y") (← getInt j "width") (← getOptS j "css") (← getOptS j "encoding"))
  | "l.default" => some do
    return encPy toJson (getDefaultLocale (testEnv (← getStr j "cur") (← getStr j "user")))
  | "l.init" => some do
    let loc := (← getOptS j "locale").map String.ofList
    return encPy toJson (initLocale (testEnv (← getStr j "cur") (← getStr j "user")) loc)
  | "l.enter_exit" => some do
    let (r, e) := withDifferentLocale (testEnv (← getStr j "cur") (← getStr j "user")) (← getStr j "locale")
      (fun e' => .ok e'.current)
    return encPy (fun s => Json.arr #[toJson s, toJson e.current]) r
  | "lt.formatweekday" => some do
    let e := testEnv "C" "C"
    return encPy encS (ltFormatweekday e (← getStr j "locale") (← getInt j "d") (← getInt j "width")).1
  | "lt.formatmonthname" => some do
    let e := testEnv "C" "C"
    return encPy encS (ltFormatmonthname e (← getStr j "locale") (← getInt j "y") (← getInt j "m") (← getInt j "width") (← getBool j "withyear")).1
  | "lh.formatweekday" => some do
    let e := testEnv "C" "C"
    return encPy encS (lhFormatweekday e (← getStr j "locale") (← getInt j "d")).1
  | "lh.formatmonthname" => some do
    let e := testEnv "C" "C"
    return encPy encS (lhFormatmonthname e (← getStr j "locale") (← getInt j "y") (← getInt j "m") (← getBool j "withyear")).1
  | "d.formatweek" => some do
    let hd ← getOptInt j "hd"
    return encS (dFormatweek testAnsi (← getWeek j "week") (← getInt j "width") hd)
  | "d.formatmonth" => some do
    return encPy encS (dFormatmonth testAnsi cNames (← cal) (← getHl j) (← getInt j "y") (← getInt j "m") (← getInt j "w") (← getInt j "l"))
  | "d.formatyear" => some do
    return encPy encS (dFormatyear testAnsi cNames (← cal) (← getHl j) (← getInt j "y") (← getInt j "w") (← getInt j "l") (← getInt j "c") (← getInt j "m"))
  | "main" => some do
    let t ← getIL j "today"
    return encPy encMain (mainRun testAnsi cNames (t[0]!, t[1]!, t[2]!) (← getOptions j))
  | _ => none

end PyLean.CoreLibs.CalStat
