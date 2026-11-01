import PyLean.DiffCore
import PyLean.TextLibs.CsvSniff

/-! `csv.*` difftest cases; see `difftest/textlibs_diff.py`. Objects arrive as JSON descriptions,
and the Python side builds real objects from the same description. -/

namespace PyLean.TextLibs.Csv

open Lean PyLean PyLean.Diff

def nats (j : Json) : Except String (List Nat) := do
  (← j.getArr?).toList.mapM Json.getNat?

def decExc (j : Json) : Except String PyExc := do
  let a ← j.getArr?
  let cls ← a[0]!.getStr?
  let msg ← a[1]!.getStr?
  return match cls with
    | "ValueError" => .valueError msg
    | "TypeError" => .typeError msg
    | _ => .named cls msg

def decKey (j : Json) : Except String KeyProbe := do
  if j.isNull then return .noMatch
  if let .ok e := j.getObjVal? "hash" then return .hashRaises (← decExc e)
  if let .ok e := j.getObjVal? "eq" then return .eqRaisesAt (strToList "excel") (← decExc e)
  return .equals (← nats (← field j "k"))

def decTy (j : Json) : Except String TyName := do
  return ⟨← getStr j "full", ← getStr j "tp", ← getStr j "short"⟩

def otherTy : TyName := ⟨"m.Other", "Other", "Other"⟩

/-- `{"ok": v}` or `{"raise": [cls, msg]}`. -/
def decRes {α : Type} (f : Json → Except String α) (j : Json) : Except String (Except PyExc α) := do
  if let .ok e := j.getObjVal? "raise" then return .error (← decExc e)
  return .ok (← f (← field j "ok"))

def builtinOther (name : String) (t : Bool) : Obj :=
  let ty := builtinTy name
  let notIter : Except PyExc (List Step) := .error (.typeError s!"'{name}' object is not iterable")
  match name with
  | "list" => .other ty (.ok t) (.hashRaises (.typeError "unhashable type: 'list'")) [] false
      ([], .ok (strToList "[]")) (.ok [])
  | "float" => .other ty (.ok t) .noMatch [] true ([], .ok (strToList "1.5")) notIter
  | "bytes" => .other ty (.ok t) .noMatch [] false ([], .ok (strToList "b'x'")) (.ok [.ret (.int 120)])
  | _ => .other ty (.ok t) .noMatch [] false ([], .ok []) notIter

mutual
  partial def decObj (j : Json) : Except String Obj := do
    if j.isNull then return .none
    if let .ok s := j.getObjVal? "s" then return .str (← nats s)
    if let .ok n := j.getObjVal? "i" then return .int (← n.getInt?)
    if (j.getObjVal? "big").toOption.isSome then return .int (10 ^ 4400)
    if let .ok b := j.getObjVal? "b" then return .bool (← b.getBool?)
    if let .ok s := j.getObjVal? "sub" then
      return .strSub ⟨"m.Sub", "Sub", "Sub"⟩ (← nats s) (← decKey (← field j "key"))
    if let .ok n := j.getObjVal? "d" then
      return (match regFind initialRegistry (← nats n) with
        | .ok (some (_, d)) => d
        | _ => .none)
    if let .ok x := j.getObjVal? "dsub" then
      let base ← (← (← field x "base").getArr?).toList.mapM fun p => do
        let a ← p.getArr?
        return (strToList (← a[0]!.getStr?), ← decObj a[1]!)
      let attrs ← (← (← field x "attrs").getArr?).toList.mapM fun p => do
        let a ← p.getArr?
        return ((← a[0]!.getStr?), (← decRes decObj a[1]!))
      let ty : TyName := ⟨"m.DSub", "DSub", "DSub"⟩
      match dialectNew initialRegistry ty ⟨[], base⟩ with
      | .ok (.fresh _ d l) =>
        return .dialectX ty d (some l) attrs (← decRes (fun _ => pure ()) (← field x "init"))
      | _ => throw "bad dsub"
    if let .ok n := j.getObjVal? "cls" then
      return match ← n.getStr? with
        | "excel" => dialectClass "excel" [44] [13, 10] QUOTE_MINIMAL
        | "excel_tab" => dialectClass "excel_tab" [9] [13, 10] QUOTE_MINIMAL
        | _ => dialectClass "unix_dialect" [44] [10] QUOTE_ALL
    if let .ok c := j.getObjVal? "func" then
      return .func (← (← c.getArr?).toList.mapM decCall)
    if let .ok o := j.getObjVal? "o" then
      if let .ok spec := j.getObjVal? "spec" then
        let attrs ← (← (← field spec "attrs").getArr?).toList.mapM fun p => do
          let a ← p.getArr?
          return ((← a[0]!.getStr?), (← decRes decObj a[1]!))
        let st ← field spec "str"
        let effs ← (← (← field st "effs").getArr?).toList.mapM decEff
        return .other otherTy (← decRes Json.getBool? (← field spec "truth")) (← decKey (← field spec "key"))
          attrs (← getBool spec "num") (effs, ← decRes nats (← field st "res"))
          (← decRes (fun x => do (← x.getArr?).toList.mapM decStep) (← field spec "iter"))
      return builtinOther (← o.getStr?) (← getBool j "t")
    throw "bad object"

  partial def decEff (j : Json) : Except String Eff := do
    match ← getStr j "e" with
    | "advance" => return .advance
    | "limit" => return .setLimit (← decObj (← field j "n"))
    | _ => return .writerow (← decObj (← field j "row"))

  partial def decStep (j : Json) : Except String Step := do
    match ← getStr j "k" with
    | "eff" => return .eff (← decEff (← field j "e"))
    | "ret" => return .ret (← decObj (← field j "o"))
    | "raise" => return .raise (← decExc (← field j "x"))
    | _ => return .stop

  partial def decCall (j : Json) : Except String (List Eff × Except PyExc Obj) := do
    let effs ← (← (← field j "effs").getArr?).toList.mapM decEff
    return (effs, ← decRes decObj (← field j "res"))
end

def kwOf (j : Json) : Except String (List (List Nat × Obj)) := do
  match j.getObjVal? "args" with
  | .error _ => return []
  | .ok v =>
    let o ← v.getObj?
    let l := o.toArray.toList
    l.mapM fun p => do return (strToList p.1, ← decObj p.2)

def srcOf (j : Json) : Except String (List Obj) := do
  match j.getObjVal? "src" with
  | .ok .null | .error _ => return []
  | .ok v =>
    if (v.getArr?).toOption.isSome then return [.str (← nats v)]
    return [← decObj v]

def encChar (c : Nat) : Json := if c = NOT_SET then Json.null else toJson [c]

def encDialect (d : Dialect) : Json :=
  Json.mkObj [("delimiter", encChar d.delimiter), ("doublequote", toJson d.doublequote),
    ("escapechar", encChar d.escapechar), ("lineterminator", toJson d.lineterminator),
    ("quotechar", encChar d.quotechar), ("quoting", toJson d.quoting),
    ("skipinitialspace", toJson d.skipinitialspace), ("strict", toJson d.strict)]

def encField : Field → Json
  | .str s => Json.mkObj [("s", toJson s)]
  | .none => Json.null
  | .float x => Json.mkObj [("f", toJson x.bits)]

def encExc : Option PyExc → Json
  | Option.none => Json.null
  | some e => Json.arr #[toJson e.className, toJson e.message]

def encObj : Obj → Json
  | .none => Json.null
  | .str s => Json.mkObj [("s", toJson s)]
  | .int n => Json.mkObj [("i", toJson n)]
  | .bool b => Json.mkObj [("b", toJson b)]
  | _ => Json.mkObj [("obj", Json.null)]

def fuelFor (n : Nat) : Nat := 64 + 16 * n

/-- The keys of the registry by text, as `list_dialects` compares them. -/
def keysOf (r : Registry) : List (List Nat) := (csvListDialects r).filterMap (·.asStr)

/-- An operation run by a callback: its errors are caught there. -/
def duringOp (r : Registry) (j : Json) : Except String Registry := do
  let name ← decObj (← field j "name")
  if (← getStr j "op") == "reg" then
    return (match regSet r name (.dialect dialectTy { excel with delimiter := 59 }) with
      | .ok r2 => r2
      | .error _ => r)
  return (match csvUnregisterDialect r name with
    | .ok r2 => r2
    | .error _ => r)

def decLine (j : Json) : Except String Step := do
  if let .ok s := j.getObjVal? "s" then return .ret (.str (← nats s))
  if (j.getObjVal? "k").toOption.isSome then return ← decStep j
  return .ret (.int 7)

def getLines (j : Json) : Except String (List Step) := do
  (← (← field j "lines").getArr?).toList.mapM decLine

def encPairs (d : List (Field × DVal)) : Json :=
  Json.arr (d.map fun p =>
    Json.arr #[encField p.1,
      (match p.2 with
       | .field f => encField f
       | .rest fs => Json.mkObj [("rest", Json.arr (fs.map encField).toArray)]
       | .restval => Json.mkObj [("restval", Json.null)])]).toArray

def encRows (rows : List (List Field)) : Json :=
  Json.arr (rows.map fun r => Json.arr (r.map encField).toArray).toArray

def encCtx (c : WCtx) : Json := toJson c.written

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "csv.sniff" =>
    let s ← nats (← field j "s")
    let ds : Option (List Nat) ← match j.getObjVal? "delims" with
      | .ok .null => pure none
      | .ok v => pure (some (← nats v))
      | .error _ => pure none
    return encPy (fun (r : Sniffed) => Json.mkObj [("d", toJson r.delimiter), ("q", toJson r.quotechar),
      ("dq", toJson r.doublequote), ("skip", toJson r.skipinitialspace)]) (sniff s ds)
  | "csv.dialect" =>
    let pos ← srcOf j
    return encPy (fun (r : DRes) => Json.mkObj [("d", encDialect r.dialect),
      ("same", toJson (match r with | .same _ _ => true | .fresh _ _ _ => false))])
      (typeCall initialRegistry ⟨pos, ← kwOf j⟩)
  | "csv.reader" =>
    let lines ← getLines j
    let limit ← getInt j "limit"
    let args : Args := ⟨iterObj lines :: (← srcOf j), ← kwOf j⟩
    return match csvReader initialRegistry limit args with
      | .error e => encPy (fun (_ : Unit) => Json.null) (.error e)
      | .ok p =>
        let (rows, e, c) := readAll p.1 (fuelFor lines.length) (lines.length + 2) p.2
        if decide (e = some CRASH) then encPy (fun (_ : Unit) => Json.null) (.error CRASH)
        else Json.mkObj [("ok", Json.mkObj [("rows", encRows rows), ("exc", encExc e),
          ("n", toJson c.lineNum), ("limit", toJson c.limit)])]
  | "csv.writer" =>
    let file ← decObj (← field j "file")
    let ops ← (← (← field j "ops").getArr?).toList.mapM fun o => do
      let a ← o.getArr?
      return ((← a[0]!.getStr?), (← decObj a[1]!))
    let args : Args := ⟨file :: (← srcOf j), ← kwOf j⟩
    return encPy (fun (p : Dialect × WCtx) => Id.run do
      let mut c := p.2
      let mut out : Array Json := #[]
      for (k, o) in ops do
        let (c', r) := if k == "row" then writerowM p.1 256 c o else writerowsM p.1 256 c o
        c := c'
        out := out.push (encPy encObj r)
      return Json.mkObj [("res", Json.arr out), ("written", toJson c.written)])
      (csvWriter initialRegistry args)
  | "csv.field_size_limit" =>
    let cur ← getInt j "cur"
    let n ← match j.getObjVal? "new" with
      | .ok v => some <$> decObj v
      | .error _ => pure Option.none
    return encPy (fun (p : Int × Int) => Json.arr #[toJson p.1, toJson p.2]) (fieldSizeLimit cur n)
  | "csv.registry" =>
    let name ← decObj (← field j "name")
    let op ← getStr j "op"
    let r : Py Registry ← if op == "register" then do
        let (r2, x) := csvRegisterDialect initialRegistry id ⟨name :: (← srcOf j), ← kwOf j⟩
        pure (match x with
          | .ok () => .ok r2
          | .error e => .error e)
      else pure (csvUnregisterDialect initialRegistry name)
    return encPy (fun r => toJson (keysOf r)) r
  | "csv.regseq" =>
    let mut r := initialRegistry
    let mut out : Array Json := #[]
    for o in (← (← field j "ops").getArr?).toList do
      let name ← decObj (← field o "name")
      match ← getStr o "op" with
      | "register" =>
        let ops := (← (← field o "during").getArr?).toList
        let hooked := !ops.isEmpty
        let after ← ops.foldlM duringOp r
        let kw : List (List Nat × Obj) := if hooked then [(strToList "doublequote", .bool true)] else []
        let (r2, x) := csvRegisterDialect r (fun _ => after) ⟨[name], (strToList "delimiter", .str [59]) :: kw⟩
        r := r2
        out := out.push (encPy (fun (_ : Unit) => Json.null) x)
      | "get" =>
        out := out.push (encPy (fun (o : Obj) => match o.getattr "delimiter" with
          | .ok (.str c) => toJson c
          | _ => Json.null) (csvGetDialect r name))
      | _ =>
        match csvUnregisterDialect r name with
        | .ok r2 =>
          r := r2
          out := out.push (encPy (fun (_ : Unit) => Json.null) (.ok ()))
        | .error e => out := out.push (encPy (fun (_ : Unit) => Json.null) (.error e))
    return Json.mkObj [("ok", Json.mkObj [("out", Json.arr out), ("keys", toJson (keysOf r)),
      ("sub", toJson ((csvListDialects r).map fun k => match k with
        | .strSub _ _ _ => true
        | _ => false))])]
  | "csv.pickle" =>
    return encPy (fun (_ : Unit) => Json.null)
      (dialectPickle (← decObj (← field j "obj")) (← getStr j "method"))
  | "csv.ltget" =>
    let o ← decObj (← field j "obj")
    return encPy (fun (x : Obj) => Json.arr #[toJson (x.asStr.getD []),
      toJson (match x with
        | .strSub _ _ _ => true
        | _ => false)]) (o.getattr "lineterminator")
  | "csv.readerd" =>
    return encPy (fun (x : Dialect × RCtx) => encDialect x.1)
      (csvReader initialRegistry 131072 ⟨iterObj [] :: (← srcOf j), ← kwOf j⟩)
  | "csv.writerd" =>
    let f : Obj := .other otherTy (.ok true) .noMatch [("write", .ok (.func []))] false ([], .ok [])
      (.error (.typeError "not iterable"))
    return encPy (fun (x : Dialect × WCtx) => encDialect x.1)
      (csvWriter initialRegistry ⟨f :: (← srcOf j), ← kwOf j⟩)
  | "csv.get_dialect" =>
    return encPy (fun (o : Obj) => match o with
      | .dialect _ d => encDialect d
      | .dialectX _ d _ _ _ => encDialect d
      | _ => Json.null) (csvGetDialect initialRegistry (← decObj (← field j "name")))
  | "csv.unpack" =>
    let pos ← (← (← field j "pos").getArr?).toList.mapM decObj
    return match ← getStr j "f" with
      | "reader" => encPy (fun _ => Json.null) (csvReader initialRegistry 131072 ⟨pos, []⟩)
      | "writer" => encPy (fun _ => Json.null) (csvWriter initialRegistry ⟨pos, []⟩)
      | _ =>
        let (r, x) := csvRegisterDialect initialRegistry id ⟨pos, []⟩
        encPy (fun (_ : Unit) => toJson (keysOf r)) x
  | "csv.dictreader" =>
    let lines ← getLines j
    let names0 ← match j.getObjVal? "names" with
      | .ok .null | .error _ => pure Option.none
      | .ok v => some <$> ((← v.getArr?).toList.mapM fun x => do return Field.str (← nats x))
    let restkey ← match j.getObjVal? "restkey" with
      | .ok .null | .error _ => pure Field.none
      | .ok v => Field.str <$> nats v
    let fuel := fuelFor lines.length
    return encPy (fun (p : Dialect × DR) =>
      let (rows, e, r) := drAll p.1 fuel (lines.length + 2) (lines.length + 2) p.2
      Json.mkObj [("rows", Json.arr (rows.map encPairs).toArray), ("exc", encExc e), ("n", toJson r.lineNum)])
      (drInit initialRegistry 131072 (iterObj lines) names0 restkey (.str (strToList "excel")) [])
  | "csv.dictwriter" =>
    let names ← (← (← field j "names").getArr?).toList.mapM nats
    let raises ← getBool j "raises"
    let items ← (← (← field j "row").getArr?).toList.mapM fun p => do
      let a ← p.getArr?
      return ((← nats (a[0]!)), (← decObj (a[1]!)))
    let (c, r) := dictWriterow excel 256 names (.str []) raises {} items
    return Json.mkObj [("ok", Json.mkObj [("res", encPy encObj r), ("written", toJson c.written)])]
  | "csv.dictwriterows" =>
    let names ← (← (← field j "names").getArr?).toList.mapM nats
    let raises ← getBool j "raises"
    let rows ← (← (← field j "rows").getArr?).toList.mapM fun row => do
      (← row.getArr?).toList.mapM fun p => do
        let a ← p.getArr?
        return ((← nats (a[0]!)), (← decObj (a[1]!)))
    let (c, r) := dictWriterows excel 256 names (.str []) raises {} rows
    return Json.mkObj [("ok", Json.mkObj [("res", encPy encObj r), ("written", toJson c.written)])]
  | "csv.writeheader" =>
    let names ← (← (← field j "names").getArr?).toList.mapM nats
    let (c, r) := writeheader excel 256 {} names
    return Json.mkObj [("ok", Json.mkObj [("res", encPy encObj r), ("written", toJson c.written)])]
  | "csv.extrasaction" =>
    return encPy toJson (extrasactionCheck (← nats (← field j "s")))
  | "csv.classvalidate" =>
    return encPy (fun _ => Json.null) (dialectInit initialRegistry (← decObj (← field j "obj")))
  | _ => throw s!"unknown fn {fn}"

end PyLean.TextLibs.Csv
