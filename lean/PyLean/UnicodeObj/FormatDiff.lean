import PyLean.DiffCore
import PyLean.StrSearch.Diff
import PyLean.UnicodeObj.FormatSpec
import PyLean.UnicodeObj.FormatNumber
import PyLean.UnicodeObj.FormatPercent
import PyLean.UnicodeObj.FormatStr
import PyLean.UnicodeObj.ObjectWriter
import PyLean.UnicodeObj.ObjectFromFormat

/-! Difftest handler for the formatting slice (`fn` names start with `fmt_`). -/

namespace PyLean.UnicodeObj.FormatDiff

open Lean PyLean PyLean.Diff PyLean.StrSearch

/-- An int sent as a hex string, because `json` refuses ints over 4300 digits. -/
def getHexInt (j : Json) (key : String) : Except String Int := do
  let s ← getStr j key
  let (neg, body) := if s.startsWith "-" then (true, s.drop 1) else (false, s.toSlice)
  let v := body.toString.foldl (fun acc c =>
    acc * 16 + (if c ≤ '9' then c.toNat - 48 else c.toNat - 87)) 0
  return if neg then -(v : Int) else v

def getObj (j : Json) : Except String FObj := do
  match ← getStr j "t" with
  | "int" => return .int (← getHexInt j "v")
  | "bool" => return .bool (← getBool j "v")
  | "float" => return .float (Binary64.F64.ofBits (← getHexInt j "v").toNat)
  | "str" => return .str (← getSeq j "s")
  | "none" => return .none
  | t => throw s!"bad obj {t}"

def getArgs (j : Json) : Except String FArgs := do
  match ← getStr j "k" with
  | "tuple" =>
    let arr ← (← field j "items").getArr?
    return .tuple (← arr.toList.mapM getObj)
  | "dict" =>
    let arr ← (← field j "items").getArr?
    return .dict (← arr.toList.mapM fun e => do
      let pair ← e.getArr?
      let k ← (pair[0]!).getArr?
      return (← k.toList.mapM (·.getNat?), ← getObj pair[1]!))
  | _ => return .single (← getObj (← field j "item"))

mutual
  /-- An object of `str.format`. -/
  partial def getG (j : Json) : Except String GObj := do
    match ← getStr j "t" with
    | "int" => return .int (← getHexInt j "v")
    | "bool" => return .bool (← getBool j "v")
    | "float" => return .float (Binary64.F64.ofBits (← getHexInt j "v").toNat)
    | "complex" =>
      return .complex (Binary64.F64.ofBits (← getHexInt j "re").toNat)
        (Binary64.F64.ofBits (← getHexInt j "im").toNat)
    | "str" => return .str (← getSeq j "s")
    | "none" => return .none
    | "tuple" => return .tuple (← (← (← field j "items").getArr?).toList.mapM getG)
    | "dict" =>
      return .dict (← (← (← field j "items").getArr?).toList.mapM fun e => do
        let pair ← e.getArr?
        let k ← (pair[0]!).getArr?
        return (← k.toList.mapM (·.getNat?), ← getG pair[1]!))
    | "user" =>
      let fmt ← getR (← field j "fmt")
      let toStr ← getR (← field j "str")
      let toRepr ← getR (← field j "repr")
      let attrs ← (← (← field j "attrs").getArr?).toList.mapM fun e => do
        let pair ← e.getArr?
        let k ← (pair[0]!).getArr?
        return ((← k.toList.mapM (·.getNat?) : List Nat), ← getR pair[1]!)
      let item : Option (GKey → Except PyExc GObj) ←
        match (← field j "item") with
        | .null => pure Option.none
        | v => do
          let r ← getR v
          pure (some fun _ => r)
      let self : Str → PyExc := fun name =>
        .named "AttributeError" s!"'U' object has no attribute '{toLeanString name}'"
      return .user "U" (fun _ => fmt) toStr toRepr
        (fun name => (attrs.lookup name).getD (.error (self name))) item
    | t => throw s!"bad object {t}"

  /-- What a method of a user object does. -/
  partial def getR (j : Json) : Except String (Except PyExc GObj) := do
    match ← getStr j "k" with
    | "raise" => return .error (.valueError "boom")
    | _ => return .ok (← getG (← field j "v"))
end

def getWHandler : String → Except String ErrHandler
  | "strict" => .ok .strict
  | "ignore" => .ok .ignore
  | "replace" => .ok .replace
  | "surrogateescape" => .ok .surrogateescape
  | "backslashreplace" => .ok .backslashreplace
  | "surrogatepass" => .ok .surrogatepass
  | "xmlcharrefreplace" => .ok .xmlcharrefreplace
  | "namereplace" => .ok .namereplace
  | o => .error s!"bad handler {o}"

/-- One operation of a writer script. -/
def getWOp (j : Json) : Except String WOp := do
  match ← getStr j "op" with
  | "char" => return .char (← getNat j "c")
  | "str" => return .str (← getG (← field j "o"))
  | "repr" => return .repr (some (← getG (← field j "o")))
  | "reprnull" => return .repr none
  | "ascii" => return .ascii (← getSeq j "s") (← getInt j "n")
  | "ucs4" => return .ucs4 (← getSeq j "s") (← getInt j "n")
  | "wide" => return .wide (← getSeq j "s") (← getInt j "n")
  | "sub" => return .sub (← getG (← field j "o")) (← getInt j "a") (← getInt j "b")
  | "utf8" => return .utf8 (← getSeq j "s") (← getInt j "n")
  | "decode" =>
    return .decode (← getSeq j "s") (← getInt j "n") (← getWHandler (← getStr j "h"))
      (← (← field j "consumed").getBool?)
  | o => throw s!"bad op {o}"

def getTName (j : Json) : Except String TName := do
  match ← getStr j "k" with
  | "static" => return .static (← getSeq j "s")
  | "heap" =>
    let m ← field j "m"
    let q ← getSeq j "q"
    if m == Json.null then return .heap none q
    else return .heap (some (← getSeq j "m")) q
  | o => throw s!"bad type {o}"

def getVArg (j : Json) : Except String VArg := do
  match ← getStr j "t" with
  | "int" => return .int (← getInt j "v")
  | "obj" => return .obj (← getG (← field j "o"))
  | "null" => return .nullObj
  | "cstr" => return .cstr (← getSeq j "s")
  | "wstr" => return .wstr (← getSeq j "s")
  | "ptr" => return .ptr (← getNat j "v")
  | "type" => return .type (← getTName (← field j "n"))
  | "inst" => return .inst (← getTName (← field j "n"))
  | o => throw s!"bad arg {o}"

def kindJson : Kind → Json
  | .ascii => Json.arr #[toJson (1 : Nat), toJson true]
  | .ucs1 => Json.arr #[toJson (1 : Nat), toJson false]
  | .ucs2 => Json.arr #[toJson (2 : Nat), toJson false]
  | .ucs4 => Json.arr #[toJson (4 : Nat), toJson false]

def encOptStr : Option Str → Json
  | some s => toJson s
  | none => Json.null

def encIdxStr : Nat ⊕ Str → Json
  | .inl n => Json.mkObj [("i", toJson n)]
  | .inr s => Json.mkObj [("s", toJson s)]

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "fmt_str" =>
    return encPy toJson (formatStrAdvanced (← getSeq j "s") (← getSeq j "spec"))
  | "fmt_int" =>
    let v ← getHexInt j "v"
    let name ← getStr j "name"
    let shown : Str := if name == "bool" then lit (if v == 1 then "True" else "False")
      else match longFormat v 10 false with | .ok s => s | .error _ => []
    let spec ← getSeq j "spec"
    if spec.isEmpty && name == "int" then
      return encPy (fun (s : Str) => toJson s) (longFormat v 10 false)
    return encPy toJson (do
      match ← formatLongAdvanced v name spec shown with
      | some s => .ok s
      | none => formatLongAsFloat v spec name)
  | "fmt_strformat" =>
    let s ← getSeq j "s"
    let args ← (← (← field j "args").getArr?).toList.mapM getG
    let kwItems ← (← (← field j "kw").getArr?).toList.mapM fun e => do
      let pair ← e.getArr?
      let k ← (pair[0]!).getArr?
      return ((← k.toList.mapM (·.getNat?) : List Nat), ← getG pair[1]!)
    let kw : Option KwMap := if kwItems.isEmpty then none else some (dictKw kwItems)
    return encPy toJson (doStringFormat s args kw)
  | "fmt_format_map" =>
    let s ← getSeq j "s"
    let script ← (← (← field j "map").getArr?).toList.mapM getR
    -- the n-th lookup gets the n-th answer, and past the end the key is missing
    let m : KwMap := fun hist =>
      (script[hist.length - 1]?).getD (.error (.keyError (toLeanString (unicodeRepr (hist.getLastD [])))))
    return encPy toJson (doStringFormatMap s m)
  | "fmt_parser" =>
    let s ← getSeq j "s"
    return encPy (fun (items : List ParserItem) => Json.arr (items.map fun (l, n, sp, c) =>
      Json.arr #[toJson l, encOptStr n, encOptStr sp, encOptStr c]).toArray)
      (formatterParserObj (if (← getBool j "bad") then .int 1 else .str s))
  | "fmt_fieldsplit" =>
    let s ← getSeq j "s"
    return encPy (fun (r : (Nat ⊕ Str) × List (Bool × (Nat ⊕ Str))) =>
      Json.arr #[encIdxStr r.1, Json.arr (r.2.map fun (b, v) => Json.arr #[toJson b, encIdxStr v]).toArray])
      (formatterFieldNameSplitObj (if (← getBool j "bad") then .int 1 else .str s))
  | "fmt_writer" =>
    let ops ← (← (← field j "ops").getArr?).toList.mapM getWOp
    return encPy (fun (w0 : UWriter) =>
      let (w, trace) := runOps w0 ops
      let (text, kind) := w.finish
      let step (r : Py Nat) : Json := Json.arr #[encPy (fun (_ : Nat) => Json.null) r,
        toJson (consumedOut r)]
      Json.arr #[Json.arr (trace.map step).toArray, toJson text, kindJson kind])
      (writerCreate (← getInt j "n"))
  | "fmt_fromformat" =>
    let args ← (← (← field j "args").getArr?).toList.mapM getVArg
    return encPy (fun (r : Str × Kind) => Json.arr #[toJson r.1, kindJson r.2])
      (pyUnicodeFromFormat (← getSeq j "fmt") args)
  | "fmt_writerformat" =>
    let args ← (← (← field j "args").getArr?).toList.mapM getVArg
    let pre ← (← (← field j "pre").getArr?).toList.mapM getWOp
    let post ← (← (← field j "post").getArr?).toList.mapM getWOp
    let (w1, _) := runOps {} pre
    let (w2, r) := writerFormat w1 (← getSeq j "fmt") args
    let (w3, _) := runOps w2 post
    let (text, kind) := w3.finish
    return encPy (fun (x : Json) => x)
      (.ok (Json.arr #[encPy (fun (_ : Unit) => Json.null) r, toJson text, kindJson kind]))
  | "fmt_percent" =>
    return encPy toJson (pyUnicodeFormat (← getSeq j "fmt") (← getArgs (← field j "args")))
  | "fmt_float" =>
    let x := Binary64.F64.ofBits (← getHexInt j "x").toNat
    return encPy toJson (formatFloatAdvanced x (← getSeq j "spec"))
  | "fmt_complex" =>
    let re := Binary64.F64.ofBits (← getHexInt j "re").toNat
    let im := Binary64.F64.ofBits (← getHexInt j "im").toNat
    return encPy toJson (formatComplexAdvanced re im (← getSeq j "spec"))
  | _ => throw s!"unknown fn {fn}"

def handler : Handler := fun fn j =>
  if fn.startsWith "fmt_" then some (run fn j) else none

end PyLean.UnicodeObj.FormatDiff
