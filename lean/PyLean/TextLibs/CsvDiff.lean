import PyLean.DiffCore
import PyLean.TextLibs.CsvModel

/-! `csv.*` difftest cases; see `difftest/textlibs_diff.py`. -/

namespace PyLean.TextLibs.Csv

open Lean PyLean PyLean.Diff

def nats (j : Json) : Except String (List Nat) := do
  (← j.getArr?).toList.mapM Json.getNat?

def decObj (j : Json) : Except String Obj := do
  if j.isNull then return .none
  if let .ok s := j.getObjVal? "s" then return .str (← nats s)
  if let .ok n := j.getObjVal? "i" then return .int (← n.getInt?)
  if let .ok b := j.getObjVal? "b" then return .bool (← b.getBool?)
  return .other (← getStr j "o") (← getBool j "t")

def optObj (j : Json) (k : String) : Except String (Option Obj) :=
  match j.getObjVal? k with
  | .error _ => .ok Option.none
  | .ok v => some <$> decObj v

def decArgs (j : Json) : Except String DArgs := do
  return { delimiter := ← optObj j "delimiter", doublequote := ← optObj j "doublequote",
           escapechar := ← optObj j "escapechar", lineterminator := ← optObj j "lineterminator",
           quotechar := ← optObj j "quotechar", quoting := ← optObj j "quoting",
           skipinitialspace := ← optObj j "skipinitialspace", strict := ← optObj j "strict" }

def decSrc (r : Registry) (j : Json) : Except String DSrc := do
  let _ := r
  match j.getObjVal? "src" with
  | .ok .null | .error _ => return .absent
  | .ok v => return .name (← nats v)

def encChar (c : Nat) : Json := if c = NOT_SET then Json.null else toJson [c]

def encDialect (d : Dialect) : Json :=
  Json.mkObj [("delimiter", encChar d.delimiter), ("doublequote", toJson d.doublequote),
    ("escapechar", encChar d.escapechar), ("lineterminator", toJson d.lineterminator),
    ("quotechar", encChar d.quotechar), ("quoting", toJson d.quoting),
    ("skipinitialspace", toJson d.skipinitialspace), ("strict", toJson d.strict)]

def encField : Field → Json
  | .str s => Json.mkObj [("s", toJson s)]
  | .none => Json.null
  | .float b => Json.mkObj [("f", toJson b)]

def encExc : Option PyExc → Json
  | Option.none => Json.null
  | some e => Json.arr #[toJson e.className, toJson e.message]

def decLine (j : Json) : Except String Line := do
  if let .ok s := j.getObjVal? "s" then return .str (← nats s)
  return .notStr (← getStr j "o")

def getLines (j : Json) : Except String (List Line) := do
  (← (← field j "lines").getArr?).toList.mapM decLine

def decW (j : Json) : Except String WField := do
  if j.isNull then return .none
  if let .ok s := j.getObjVal? "s" then return .str (← nats s)
  return .other (← nats (← field j "t")) (← getBool j "num")

def getRow (j : Json) : Except String (List WField) := do
  j.getArr? >>= fun a => a.toList.mapM decW

def dialectOf (j : Json) : Except String (Py Dialect) := do
  let a ← decArgs (← field j "args")
  return dialectNew initialRegistry (← decSrc initialRegistry j) a

def encPairs (d : List (Option (List Nat) × DVal)) : Json :=
  Json.arr (d.map fun p =>
    Json.arr #[(match p.1 with | some k => toJson k | Option.none => Json.null),
      (match p.2 with
       | .field f => encField f
       | .rest fs => Json.mkObj [("rest", Json.arr (fs.map encField).toArray)]
       | .restval => Json.mkObj [("restval", Json.null)])]).toArray

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "csv.dialect" => return encPy encDialect (← dialectOf j)
  | "csv.reader" =>
    let lines ← getLines j
    let limit ← getInt j "limit"
    return encPy (fun d =>
      let (rows, e, n) := readAll d limit (lines.length + 1) lines 0
      Json.mkObj [("rows", Json.arr (rows.map fun r => Json.arr (r.map encField).toArray).toArray),
        ("exc", encExc e), ("n", toJson n)]) (← dialectOf j)
  | "csv.writerow" =>
    let row ← getRow (← field j "row")
    let d? ← dialectOf j
    return encPy toJson (do writerow (← d?) row)
  | "csv.writerows" =>
    let rows ← (← (← field j "rows").getArr?).toList.mapM getRow
    return encPy (fun d =>
      let (t, e) := writerows d rows
      Json.mkObj [("text", toJson t), ("exc", encExc e)]) (← dialectOf j)
  | "csv.field_size_limit" =>
    let cur ← getInt j "cur"
    return encPy (fun (p : Int × Int) => Json.arr #[toJson p.1, toJson p.2])
      (fieldSizeLimit cur (← optObj j "new"))
  | "csv.registry" =>
    let name ← nats (← field j "name")
    let op ← getStr j "op"
    let a ← decArgs (← field j "args")
    let r : Py Registry := match op with
      | "register" => registerDialect initialRegistry name .absent a
      | _ => unregisterDialect initialRegistry name
    return encPy (fun r => toJson (listDialects r)) r
  | "csv.get_dialect" =>
    return encPy encDialect (registryGet initialRegistry (← nats (← field j "name")))
  | "csv.dictreader" =>
    let lines ← getLines j
    let names0 ← match j.getObjVal? "names" with
      | .ok .null | .error _ => pure Option.none
      | .ok v => some <$> ((← v.getArr?).toList.mapM nats)
    let restkey ← match j.getObjVal? "restkey" with
      | .ok .null | .error _ => pure Option.none
      | .ok v => some <$> nats v
    let (rows, e) := dictRead excel 131072 names0 lines restkey
    return Json.mkObj [("ok", Json.mkObj [("rows", Json.arr (rows.map encPairs).toArray),
      ("exc", encExc e)])]
  | "csv.dictwriter" =>
    let names ← (← (← field j "names").getArr?).toList.mapM nats
    let raises ← getBool j "raises"
    let items ← (← (← field j "row").getArr?).toList.mapM fun p => do
      let a ← p.getArr?
      return ((← nats (a[0]!)), (← decW (a[1]!)))
    return encPy toJson (dictWriterow excel names (.str []) raises items)
  | "csv.writeheader" =>
    let names ← (← (← field j "names").getArr?).toList.mapM nats
    return encPy toJson (writeheader excel names)
  | "csv.extrasaction" =>
    return encPy toJson (extrasactionCheck (← nats (← field j "s")))
  | _ => throw s!"unknown fn {fn}"

end PyLean.TextLibs.Csv
