import PyLean.DiffCore
import PyLean.StrSearch.Diff
import PyLean.UnicodeObj.CodecsErr
import PyLean.UnicodeObj.CodecsModule
import PyLean.UnicodeObj.CodecAscii
import PyLean.UnicodeObj.CodecEscapeProps

/-! Difftest handler for `Python/codecs.c` and `Modules/_codecsmodule.c` (`fn` names start
with `codecs_`). -/

namespace PyLean.UnicodeObj.CodecsDiff

open Lean PyLean PyLean.Diff PyLean.StrSearch PyLean.UnicodeObj PyLean.UnicodeObj.Codecs

def getErrH (name : String) : Except String ErrHandler := do
  match name with
  | "strict" => return .strict
  | "ignore" => return .ignore
  | "replace" => return .replace
  | "surrogateescape" => return .surrogateescape
  | "backslashreplace" => return .backslashreplace
  | "surrogatepass" => return .surrogatepass
  | "xmlcharrefreplace" => return .xmlcharrefreplace
  | "namereplace" => return .namereplace
  | e => throw s!"bad handler {e}"

def getSlot (j : Json) : Except String Slot := do
  match ← getStr j "k" with
  | "null" => return .null
  | "str" => return .str (← getSeq j "v")
  | "bytes" => return .bytes (← getSeq j "v")
  | "none" | "int" => return .other
  | k => throw s!"bad slot {k}"

/-- The hierarchy of a case: the MRO of the object's class as Python reports it, and the
builtin bases for every other class. -/
def getHier (j : Json) : Except String Hier := do
  let cls ← getStr j "cls"
  let mro ← (← field j "mro").getArr?
  let mro ← mro.toList.mapM (·.getStr?)
  let flag ← getBool j "flag"
  return ⟨fun c b => if c == cls then mro.contains b else Codecs.builtinSub c b,
    fun c => if c == cls then flag else true⟩

def getExcObj (j : Json) : Except String ExcObj := do
  return { cls := ← getStr j "cls", tpName := ← getStr j "tp", clsRepr := ← getStr j "repr",
           encoding := ← getSlot (← field j "encoding"), object := ← getSlot (← field j "object"),
           start := ← getInt j "start", stop := ← getInt j "end" }

/-- `ucnhash_capi->getname(c, buf, 256, 1)` for the characters of a case. -/
def getNameTable (j : Json) : Except String (Nat → Option Str) := do
  let arr ← (← field j "names").getArr?
  let l ← arr.toList.mapM fun e => do
    let pair ← e.getArr?
    let c ← pair[0]!.getNat?
    match pair[1]! with
    | .null => return (c, none)
    | v => return (c, some (← (← v.getArr?).toList.mapM (·.getNat?)))
  return fun c => (l.lookup c).join

def encRep : Rep → Json
  | .str s => Json.arr #[toJson "str", toJson s]
  | .bytes b => Json.arr #[toJson "bytes", toJson b]

def encHandler (r : HPy (Rep × Nat)) : Json :=
  match r with
  | .ok (rep, pos) => Json.mkObj [("rep", encRep rep), ("pos", toJson pos)]
  | .error .reraise => Json.mkObj [("raised", toJson "self")]
  | .error (.exc e) => Json.mkObj [("raised", toJson e.className), ("msg", toJson e.message)]


/-! ## The registry -/

def getVal (j : Json) : Except String Val := do
  match ← getStr j "k" with
  | "bytes" => return .bytes (← getSeq j "v")
  | "str" => return .str (← getSeq j "v")
  | "bytearray" => return .bytearray (← getSeq j "v")
  | "int" => return .int (← getInt j "v")
  | k => throw s!"bad val {k}"

/-- A search function's or a coder's answer. -/
inductive RRet where
  | none | info (i : Nat) | bad (form : Nat) | raise
  | nargs | pair (v : Val)

def getRet (j : Json) : Except String RRet := do
  match ← getStr j "t" with
  | "none" => return .none
  | "info" => return .info (← getNat j "i")
  | "bad" => return .bad (← getNat j "form")
  | "raise" => return .raise
  | "nargs" => return .nargs
  | "pair" => return .pair (← getVal (← field j "v"))
  | t => throw s!"bad ret {t}"

def funcVal (i : Nat) : Val := .obj (1 + i) "function"
def coderVal (i : Nat) : Val := .obj (200 + i) "function"

def getOps (j : Json) : Except String (List Op) := do
  (← j.getArr?).toList.mapM fun o => do
    let f := funcVal (← getNat o "f")
    match ← getStr o "t" with
    | "reg" => return Op.register f
    | _ => return Op.unregister f

structure InfoSpec where
  kind : String
  items : List Nat
  ie : Option Nat
  id : Option Nat
  text : Option Json

def getInfo (j : Json) : Except String InfoSpec := do
  let kind ← getStr j "kind"
  let items ← (← (← field j "items").getArr?).toList.mapM (·.getNat?)
  let optN (k : String) : Except String (Option Nat) := match j.getObjVal? k with
    | .ok .null | .error _ => .ok none
    | .ok v => some <$> v.getNat?
  return { kind, items, ie := ← optN "ie", id := ← optN "id",
           text := match j.getObjVal? "text" with | .ok v => some v | .error _ => none }

def infoVal (infos : List InfoSpec) (i : Nat) : Val :=
  let spec := infos.getD i ⟨"tuple", [], none, none, none⟩
  .tuple (100 + i) (spec.items.map coderVal) (spec.kind == "tuple")

def retVal (infos : List InfoSpec) : RRet → Py Val
  | .none => .ok .none
  | .info i => .ok (infoVal infos i)
  | .bad 0 => .ok (.tuple 9990 [.int 1, .int 2, .int 3] true)
  | .bad 1 => .ok (.tuple 9991 [.int 1, .int 2, .int 3, .int 4, .int 5] true)
  | .bad 2 => .ok (.obj 9992 "list")
  | .bad _ => .ok (.str (lit "x"))
  | _ => .error (.valueError "search failed")

def coderRet (r : RRet) (args : List Val) : Py Val :=
  match r with
  | .nargs => .ok (.int args.length)
  | .pair v => .ok (.tuple 9993 [v, .int 0] true)
  | .bad 0 => .ok (.str (lit "x"))
  | .bad 1 => .ok (.tuple 9994 [.int 1] true)
  | .bad _ => .ok (.tuple 9995 [.int 1, .int 2, .int 3] true)
  | _ => .error (.valueError "boom")

/-- The world of a case: its search functions, coders and codec objects. -/
def mkWorld (funcs : List (List (Str × RRet × List Op) × RRet × List Op)) (coders : List RRet)
    (infos : List InfoSpec) : World where
  call f args :=
    match f with
    | .obj 0 _ => ([], .ok .none)
    | .obj i tp =>
      if 1 ≤ i ∧ i < 100 then
        match funcs[i - 1]? with
        | some (rules, dflt, dops) =>
          let name := match args with
            | [.str v] => v
            | _ => []
          match rules.find? (·.1 == name) with
          | some (_, r, ops) => (ops, retVal infos r)
          | none => (dops, retVal infos dflt)
        | none => ([], .error (.typeError s!"'{tp}' object is not callable"))
      else if 200 ≤ i ∧ i < 300 then ([], coderRet (coders.getD (i - 200) .raise) args)
      else ([], .error (.typeError s!"'{tp}' object is not callable"))
    | v => ([], .error (.typeError s!"'{v.tpName}' object is not callable"))
  getattr v name :=
    match v with
    | .tuple i _ _ =>
      if 100 ≤ i ∧ i < 200 then
        match infos[i - 100]? with
        | some spec =>
          if spec.kind != "ci" then .ok none
          else if name == "encode" then .ok (some (coderVal (spec.items.getD 0 0)))
          else if name == "decode" then .ok (some (coderVal (spec.items.getD 1 0)))
          else if name == "streamreader" then .ok (some (coderVal (spec.items.getD 2 0)))
          else if name == "streamwriter" then .ok (some (coderVal (spec.items.getD 3 0)))
          else if name == "incrementalencoder" then .ok (some (match spec.ie with | some c => coderVal c | none => .none))
          else if name == "incrementaldecoder" then .ok (some (match spec.id with | some c => coderVal c | none => .none))
          else if name == "_is_text_encoding" then
            match spec.text with
            | some (.bool false) => .ok (some (.int 0))
            | some (.str "raise") => .ok (some (.obj 777 "RegBadBool"))
            | _ => .ok (some (.int 1))
          else .ok none
        | none => .ok none
      else .ok none
    | _ => .ok none
  truth v :=
    match v with
    | .int n => .ok (n != 0)
    | .obj 777 _ => .error (.valueError "bad bool")
    | _ => .ok true
  callable v :=
    match v with
    | .obj i _ => i < 100 || (200 ≤ i && i < 400) || (500 ≤ i && i < 510)
    | _ => false

def encVal : Val → Json
  | .none => Json.mkObj [("none", toJson 1)]
  | .str s => Json.mkObj [("str", toJson s)]
  | .bytes b => Json.mkObj [("bytes", toJson b)]
  | .bytearray b => Json.mkObj [("bytearray", toJson b)]
  | .int n => Json.mkObj [("int", toJson n)]
  | .tuple i _ _ => if 100 ≤ i ∧ i < 200 then Json.mkObj [("id", toJson i)] else Json.mkObj [("other", toJson "tuple")]
  | .obj i tp =>
    if (1 ≤ i ∧ i < 100) ∨ (200 ≤ i ∧ i < 400) then Json.mkObj [("id", toJson i)]
    else Json.mkObj [("other", toJson tp)]

def encErr (e : PyExc) (notes : List String) : Json :=
  Json.mkObj [("exc", toJson e.className),
    ("msg", toJson (if e.className == "AttributeError" then "~" else e.message)), ("notes", toJson notes)]

def encStep (r : NPy Val) : Json :=
  match r with
  | .ok v => Json.mkObj [("ok", encVal v)]
  | .error ⟨e, notes⟩ => encErr e notes

def builtinReg : Reg :=
  { path := [.obj 0 "function"], cache := [],
    errors := builtinNames.zipIdx.map fun (n, k) => (n, .obj (500 + k) "builtin_function_or_method") }

def optSeq (j : Json) (k : String) : Except String (Option Str) :=
  match j.getObjVal? k with
  | .ok .null | .error _ => .ok none
  | .ok v => do return some (← (← v.getArr?).toList.mapM (·.getNat?))

/-- The C string of a name the difftest passes through ctypes (UTF-8, no NUL). -/
def cName (s : Str) : List Nat := (utf8Encode s .strict).toOption.getD []

def runStep (W : World) (st : Reg) (j : Json) : Except String (Reg × Json) := do
  let t ← getStr j "t"
  let wrap (r : Reg × Py Val) : Reg × Json := (r.1, encStep (plain r.2))
  match t with
  | "register" =>
    let f := match j.getObjVal? "bad" with
      | .ok _ => Val.int 5
      | .error _ => funcVal ((getNat j "f").toOption.getD 0)
    return wrap (codecsRegister W st f)
  | "unregister" => return wrap (codecsUnregister st (funcVal (← getNat j "f")))
  | "lookup" => return wrap (codecsLookup W st (← getSeq j "name"))
  | "encode" | "decode" =>
    let f := if t == "encode" then codecsEncode else codecsDecode
    let r := f W st (.str (lit "abc")) (some (← getSeq j "name")) (← optSeq j "errors")
    return (r.1, encStep r.2)
  | "strencode" =>
    let r := strEncodeRegistry W st (lit "abc") (cName (← getSeq j "name")) (← optSeq j "errors")
    return (r.1, encStep r.2)
  | "bytesdecode" =>
    let r := bytesDecodeRegistry W st (.obj 9999 "memoryview") (cName (← getSeq j "name")) (← optSeq j "errors")
    return (r.1, encStep r.2)
  | "known" =>
    let (st', b) := knownEncoding W st (cName (← getSeq j "name"))
    return (st', Json.mkObj [("ok", Json.mkObj [("int", toJson (if b then 1 else 0))])])
  | "capi" =>
    let name := cName (← getSeq j "name")
    let err ← optSeq j "errors"
    let stream : Val := .bytes (lit "stream")
    match ← getStr j "which" with
    | "Encoder" => return wrap (pyCodecEncoder W st name)
    | "Decoder" => return wrap (pyCodecDecoder W st name)
    | "IncrementalEncoder" => return wrap (pyCodecIncEncoder W st name err)
    | "IncrementalDecoder" => return wrap (pyCodecIncDecoder W st name err)
    | "StreamReader" => return wrap (pyCodecStreamReader W st name stream err)
    | _ => return wrap (pyCodecStreamWriter W st name stream err)
  | "pyget" =>
    let name ← getSeq j "name"
    let eargs := ((← optSeq j "errors").map Val.str).toList
    let stream : Val := .bytes (lit "stream")
    match ← getStr j "which" with
    | "encoder" => return wrap (libGetAttr W st name "encode")
    | "decoder" => return wrap (libGetAttr W st name "decode")
    | "incenc" => return wrap (libCall W (libGetIncremental W st name "incrementalencoder") eargs)
    | "incdec" => return wrap (libCall W (libGetIncremental W st name "incrementaldecoder") eargs)
    | "reader" => return wrap (libCall W (libGetAttr W st name "streamreader") (stream :: eargs))
    | _ => return wrap (libCall W (libGetAttr W st name "streamwriter") (stream :: eargs))
  | "regerr" =>
    let h : Val := match j.getObjVal? "h" with
      | .ok (.num n) => .obj (300 + n.mantissa.toNat) "function"
      | _ => .int 5
    return wrap (codecsRegisterError W st (← getStr j "name") h)
  | "lookuperr" =>
    let name ← getStr j "name"
    return (st, encStep (plain (codecsLookupError st name)))
  | _ =>
    let (st', r) := codecsUnregisterError st (← getStr j "name")
    return (st', encStep (plain (r.map fun b => Val.int (if b then 1 else 0))))

def runRegistry (j : Json) : Except String Json := do
  let coders ← (← (← field j "coders").getArr?).toList.mapM getRet
  let infos ← (← (← field j "infos").getArr?).toList.mapM getInfo
  let funcs ← (← (← field j "funcs").getArr?).toList.mapM fun f => do
    let rules ← (← (← field f "rules").getArr?).toList.mapM fun r => do
      let a ← r.getArr?
      return ((← (← a[0]!.getArr?).toList.mapM (·.getNat?)), ← getRet a[1]!, ← getOps a[2]!)
    return (rules, ← getRet (← field f "default"), ← getOps (← field f "dops"))
  let W := mkWorld funcs coders infos
  let steps ← (← field j "steps").getArr?
  let mut st := builtinReg
  let mut out : Array Json := #[]
  for s in steps do
    let (st', r) ← runStep W st s
    st := st'
    out := out.push r
  return Json.mkObj [("ok", Json.arr out)]

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "codecs_registry" => runRegistry j
  | "codecs_normalize" => return encPy toJson (normalizeEncodingC (← getSeq j "s"))
  | "codecs_escape" =>
    let b ← getSeq j "b"
    let r := if (← getBool j "enc") then escapeEncode b else
      escapeDecode b (match j.getObjVal? "errors" with
        | .ok (.str e) => some e
        | _ => none)
    return encPy (fun (p : Bytes × Nat) => Json.arr #[toJson p.1, toJson p.2]) r
  | "codecs_handler" =>
    let H ← getHier j
    let e ← getExcObj j
    let h ← getErrH (← getStr j "h")
    let names ← getNameTable j
    return Json.mkObj [("ok", encHandler (callBuiltin H (.ok names) h e))]
  | "codecs_ucs1_encode" =>
    let names ← getNameTable j
    return encPy toJson (ucs1Encode (← getSeq j "s") (← getNat j "limit")
      (← getErrH (← getStr j "h")) names)
  | _ => throw s!"unknown fn {fn}"

def handler : PyLean.Diff.Handler := fun fn j =>
  if fn.startsWith "codecs_" then some (run fn j) else none

end PyLean.UnicodeObj.CodecsDiff
