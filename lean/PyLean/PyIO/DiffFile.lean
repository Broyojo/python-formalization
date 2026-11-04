import PyLean.DiffCore
import PyLean.PyIO.Base
import PyLean.PyIO.BytesExtra

/-! Difftest handler for the abstract base classes and the remaining BytesIO
methods: `none` for a `fn` this area does not own. -/

namespace PyLean.PyIO

open Lean PyLean PyLean.Diff

def getNats (j : Json) (key : String) : Except String (List Nat) := do
  let arr ← (← field j key).getArr?
  (arr.mapM Json.getNat?).map Array.toList

def getOptNats (j : Json) (key : String) : Except String (Option (List Nat)) :=
  match j.getObjVal? key with
  | .ok .null | .error _ => .ok none
  | .ok _ => some <$> getNats j key

def getSOp (j : Json) : Except String SOp := do
  match ← getStr j "op" with
  | "read" => return .read (← getOptInt j "n")
  | "readline" => return .readline (← getOptInt j "n")
  | "readlines" => return .readlines (← getOptInt j "n")
  | "write" => return .write (← getNats j "b")
  | "seek" => return .seek (← getInt j "pos") (← getInt j "whence")
  | "tell" => return .tell
  | "truncate" => return .truncate (← getOptInt j "n")
  | "getvalue" => return .getvalue
  | "close" => return .close
  | "next" => return .next
  | "closed" => return .closed
  | "newlines" => return .newlines
  | "seektell" => return .seekTell
  | o => throw s!"unknown op {o}"

def bAtom : Atom → Json
  | .none => Json.null
  | .int i => toJson i
  | .bool b => toJson b
  | .bytes b => Json.mkObj [("b", toJson b)]
  | .str s => Json.mkObj [("s", toJson s)]

def bVal : Val → Json
  | .atom a => bAtom a
  | .list l => Json.arr (l.map bAtom).toArray

def bNats (j : Json) : Except String (List Nat) := do
  (← j.getArr?).toList.mapM Json.getNat?

def getRet (j : Json) : Except String Ret :=
  match j with
  | .null => .ok .none
  | .num _ => do return .int (← j.getInt?)
  | _ =>
    match j.getObjVal? "raise" with
    | .ok c => do return .raise (← c.getStr?) (← (← j.getObjVal? "msg").getStr?)
    | .error _ => do return .bytes (← bNats (← j.getObjVal? "b"))

def getRets (j : Json) (k : String) : Except String (List Ret) := do
  (← (← field j k).getArr?).toList.mapM getRet

/-- An inquiry or `closed` answer: a JSON bool, int, `null`, or `{"raise": cls, "msg": m}`. -/
def getIRet (j : Json) : Except String IRet :=
  match j with
  | .null => .ok .none
  | .bool b => .ok (.bool b)
  | .num _ => do return .int (← j.getInt?)
  | _ => do return .raise (← (← j.getObjVal? "raise").getStr?) (← (← j.getObjVal? "msg").getStr?)

def getOptStr (j : Json) (k : String) : Except String (Option String) :=
  match j.getObjVal? k with
  | .ok .null | .error _ => .ok none
  | .ok v => some <$> v.getStr?

def getUOp (j : Json) : Except String UOp := do
  match ← getStr j "op" with
  | "seek" => return .seek | "tell" => return .tell | "truncate" => return .truncate
  | "flush" => return .flush | "close" => return .close | "closed" => return .closed
  | "seekable" => return .seekable | "readable" => return .readable | "writable" => return .writable
  | "checkClosed" => return .checkClosed (← getOptStr j "msg")
  | "checkSeekable" => return .checkSeekable (← getOptStr j "msg")
  | "checkReadable" => return .checkReadable (← getOptStr j "msg")
  | "checkWritable" => return .checkWritable (← getOptStr j "msg")
  | "enter" => return .enter | "exit" => return .exit | "fileno" => return .fileno
  | "isatty" => return .isatty | "readline" => return .readline (← getOptInt j "n")
  | "iter" => return .iter | "next" => return .next
  | "readlines" => return .readlines (← getOptInt j "n")
  | "writelines" =>
    let stop : Option (String × String) ← match j.getObjVal? "stop" with
      | .ok .null | .error _ => pure none
      | .ok r => pure (some ((← (← r.getObjVal? "raise").getStr?), (← (← r.getObjVal? "msg").getStr?)))
    return .writelines (← (← (← field j "ls").getArr?).toList.mapM bNats) stop
  | "del" => return .del | "rawRead" => return .rawRead (← getOptInt j "n")
  | "rawReadall" => return .rawReadall | "rawReadinto" => return .rawReadinto
  | "rawWrite" => return .rawWrite | "bRead" => return .bRead | "bRead1" => return .bRead1
  | "bReadinto" => return .bReadinto (← getNat j "n")
  | "bReadinto1" => return .bReadinto1 (← getNat j "n")
  | "bWrite" => return .bWrite | "bDetach" => return .bDetach
  | "tRead" => return .tRead | "tReadline" => return .tReadline | "tWrite" => return .tWrite
  | "tTruncate" => return .tTruncate | "tDetach" => return .tDetach
  | "tEncoding" => return .tEncoding | "tNewlines" => return .tNewlines | "tErrors" => return .tErrors
  | o => throw s!"unknown op {o}"

def encCall : Call → Json
  | .read n => Json.arr #[toJson "read", toJson n]
  | .read1 n => Json.arr #[toJson "read1", toJson n]
  | .peek n => Json.arr #[toJson "peek", toJson n]
  | .readinto n => Json.arr #[toJson "readinto", toJson n]
  | .write b => Json.arr #[toJson "write", toJson b]
  | .flush => Json.arr #[toJson "flush"]
  | .seek p w => Json.arr #[toJson "seek", toJson p, toJson w]
  | .inquiry n => Json.arr #[toJson "inquiry", toJson n]

def runUOps (step : UObj → UOp → UObj × Py Val) : UObj → List UOp → UObj × List (Py Val)
  | u, [] => (u, [])
  | u, o :: os =>
    let (u', r) := step u o
    let (u'', rs) := runUOps step u' os
    (u'', r :: rs)

def getUObj (j : Json) : Except String (UObj × List UOp) := do
  let reads ← getRets j "reads"
  let peeks ← getRets j "peeks"
  let intos ← (← (← field j "intos").getArr?).toList.mapM fun p => do
    let a ← p.getArr?
    return ((← bNats (a.getD 0 .null)), (← getRet (a.getD 1 .null)))
  let writes ← getRets j "writes"
  let flushes ← getRets j "flushes"
  let raw ← getBool j "raw"
  let peek ← getBool j "peek"
  let ops ← (← (← field j "ops").getArr?).toList.mapM getUOp
  let keep ← getBool j "keep"
  let seeks : Option (List Ret) ← match j.getObjVal? "seeks" with
    | .ok .null | .error _ => pure none
    | .ok v => some <$> (← v.getArr?).toList.mapM getRet
  let inqs : Option (List IRet) ← match j.getObjVal? "inqs" with
    | .ok .null | .error _ => pure none
    | .ok v => some <$> (← v.getArr?).toList.mapM getIRet
  let closedProp : Option IRet ← match j.getObjVal? "closedprop" with
    | .error _ => pure none
    | .ok v => match v.getObjVal? "v" with
      | .ok w => some <$> getIRet w
      | .error _ => pure none
  return ({ name := "S", reads, peeks := if peek then some peeks else none, intos, writes, flushes,
            rawRead := raw, isClosed := false, log := [], keepView := keep, seeks, inqs, closedProp }, ops)

def getHook (j : Json) : Except String Hook := do
  match ← getStr j "h" with
  | "close" => return .close | "getbuffer" => return .getbuffer | "tell" => return .tell
  | "seekabs" => return .seekAbs (← getNat j "p")
  | "seekcur" => return .seekCur
  | "write" => return .write (← bNats (← field j "b"))
  | o => throw s!"unknown hook {o}"

/-- `{"kind": "index", "hook": [...], "v": n or null}`, or `{"kind": "str" | "float"}`. -/
def getTArg (j : Json) : Except String TArg := do
  match ← getStr j "kind" with
  | "index" =>
    return .index (← (← (← field j "hook").getArr?).toList.mapM getHook) (← getOptInt j "v")
  | "str" => return .noIndex "str" "'a'"
  | "float" => return .noIndex "float" "1.5"
  | o => throw s!"unknown kind {o}"

def getOptBytes (j : Json) (key : String) : Except String (Option (List Nat)) :=
  match j.getObjVal? key with
  | .ok .null | .error _ => .ok none
  | .ok v => some <$> bNats v

def getXOp (j : Json) : Except String (BOp ⊕ XOp) := do
  match ← getStr j "op" with
  | "readable" => return .inr .readable | "writable" => return .inr .writable
  | "seekable" => return .inr .seekable | "flush" => return .inr .flush | "isatty" => return .inr .isatty
  | "writelines" => return .inr (.writelines (← (← (← field j "ls").getArr?).toList.mapM bNats))
  | "getstate" => return .inr .getstate
  | "setstate" => return .inr (.setstate (← bNats (← field j "b")) (← getInt j "pos"))
  | "readinto_self" => return .inr (.readintoSelf (← getNat j "off") (← getNat j "n"))
  | "reinit" => return .inr (.reinit (← getOptBytes j "b"))
  | "reinit_obj" => return .inr (.reinitObj (← getOptBytes j "b"))
  | "truncobj" => return .inr (.truncateObj (← getTArg (← field j "a")))
  | "readobj" => return .inr (.readObj (← getTArg (← field j "a")))
  | "readlineobj" => return .inr (.readlineObj (← getTArg (← field j "a")))
  | "seekobj" => return .inr (.seekObj (← getTArg (← field j "a")) (← getInt j "whence"))
  | "readlinesf" => return .inr (.readlinesFloat (Binary64.F64.ofBits (← getNat j "bits")))
  | "writeobj" =>
    let w ← field j "w"
    match w.getObjVal? "s" with
    | .ok _ => return .inr (.writeObj (.str (← getNats w "s")))
    | .error _ => return .inr (.writeObj (.obj (← getStr w "t")))
  | "read" => return .inl (.read (← getOptInt j "n"))
  | "read1" => return .inl (.read1 (← getOptInt j "n"))
  | "readline" => return .inl (.readline (← getOptInt j "n"))
  | "readlines" => return .inl (.readlines (← getOptInt j "n"))
  | "readinto" => return .inl (.readinto (← getNat j "n"))
  | "write" => return .inl (.write (← bNats (← field j "b")))
  | "seek" => return .inl (.seek (← getInt j "pos") (← getInt j "whence"))
  | "tell" => return .inl .tell
  | "truncate" => return .inl (.truncate (← getOptInt j "n"))
  | "getvalue" => return .inl .getvalue
  | "getbuffer" => return .inl .getbuffer
  | "release" => return .inl .release
  | "close" => return .inl .close
  | "next" => return .inl .next
  | "closed" => return .inl .closed
  | o => throw s!"unknown op {o}"

def runFile (fn : String) (j : Json) : Option (Except String Json) :=
  match fn with
  | "base_c" | "base_py" => some do
    let (u, ops) ← getUObj j
    let (u', rs) := runUOps (if fn = "base_c" then BC.step else BP.step) u ops
    return Json.mkObj [("ok", Json.arr (rs.map (encPy bVal)).toArray),
      ("log", Json.arr (u'.log.map encCall).toArray)]
  | "bytesx_c" | "bytesx_py" => some do
    let init ← bNats (← field j "init")
    let ops ← (← (← field j "ops").getArr?).toList.mapM getXOp
    let rs := (runOps (if fn = "bytesx_c" then stepAnyC else stepAnyP) (bInit init) ops).2
    return Json.mkObj [("ok", Json.arr (rs.map (encPy bVal)).toArray)]
  | _ => none

end PyLean.PyIO
