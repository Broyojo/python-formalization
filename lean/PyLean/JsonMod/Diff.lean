import PyLean.DiffCore
import PyLean.JsonMod.Tool
import PyLean.JsonMod.DecRecProps
import PyLean.JsonMod.EncFullRefute

/-!
Differential-testing handler for `json` cases (`"mod": "json"`).

Strings travel as lists of code points; ints as decimal strings. A decoded
value is `null`, a bool, `{"int": "<n>"}`, `{"s": [...]}`,
`{"hook": "float"|"int"|"const", "t": [...]}`, a JSON list, or
`{"obj": [[key, value], ...]}`; with `opaque` a `hook` value is `{"float": 1}`,
because `float` itself is not modelled. An encoder input uses `null`, bools,
`{"i": "<n>"}`, `{"s": [...]}`, `{"f": "<bits>", "r": [...]}`, `{"l": [...]}`,
`{"d": [[key, value], ...]}`, `{"back": k}` and `{"other": n, "t": "<type>"}`;
keys are `{"s": [...]}`, `{"i": "<n>"}`, `{"b": bool}`, `null`, `{"f": ...}` or
`{"t": "<n>"}`.
-/

namespace PyLean.JsonMod

open Lean PyLean PyLean.Diff

def encStr (s : PStr) : Json := Json.arr (s.toArray.map toJson)

partial def encJVal (opq : Bool) : JVal → Json
  | .null => Json.null
  | .bool b => toJson b
  | .int n => Json.mkObj [("int", toJson (toString n))]
  | .str s => Json.mkObj [("s", encStr s)]
  | .hook k t =>
    if opq && k != .int then Json.mkObj [("float", toJson (1 : Nat))]
    else
      let kn := match k with
        | .float => "float"
        | .int => "int"
        | .const => "const"
      Json.mkObj [("hook", toJson kn), ("t", encStr t)]
  | .arr xs => Json.arr (xs.toArray.map (encJVal opq))
  | .obj kvs => Json.mkObj [("obj", Json.arr (kvs.toArray.map fun (k, v) => Json.arr #[encStr k, encJVal opq v]))]

def decStr (j : Json) : Except String PStr := do
  let a ← j.getArr?
  a.toList.mapM (·.getNat?)

def decIntStr (j : Json) : Except String Int := do
  let t ← j.getStr?
  match t.toInt? with
  | some n => pure n
  | none => throw s!"bad int {t}"

def decNatStr (j : Json) : Except String Nat := do
  return (← decIntStr j).toNat

def decKey (j : Json) : Except String EKey :=
  match j with
  | .null => pure .none
  | _ =>
    match j.getObjVal? "s", j.getObjVal? "i", j.getObjVal? "b", j.getObjVal? "t", j.getObjVal? "f" with
    | .ok s, _, _, _, _ => .str <$> decStr s
    | _, .ok i, _, _, _ => .int <$> decIntStr i
    | _, _, .ok b, _, _ => .bool <$> b.getBool?
    | _, _, _, .ok t, _ => .tup <$> decIntStr t
    | _, _, _, _, .ok f => do return .flt (← decNatStr f) (← decStr (← field j "r"))
    | _, _, _, _, _ => throw "bad key"

partial def decEVal (j : Json) : Except String EVal :=
  match j with
  | .null => pure .none
  | .bool b => pure (.bool b)
  | _ =>
    match j.getObjVal? "s", j.getObjVal? "i", j.getObjVal? "l", j.getObjVal? "d" with
    | .ok s, _, _, _ => .str <$> decStr s
    | _, .ok i, _, _ => .int <$> decIntStr i
    | _, _, .ok l, _ => do
      let a ← l.getArr?
      return .list (← a.toList.mapM decEVal)
    | _, _, _, .ok d => do
      let a ← d.getArr?
      let ps ← a.toList.mapM fun p => do
        let q ← p.getArr?
        return (← decKey (q.getD 0 .null), ← decEVal (q.getD 1 .null))
      return .dict ps
    | _, _, _, _ =>
      match j.getObjVal? "back", j.getObjVal? "other", j.getObjVal? "f" with
      | .ok k, _, _ => .back <$> k.getNat?
      | _, .ok n, _ => do return .other (← n.getNat?) (← getStr j "t")
      | _, _, .ok f => do return .flt (← decNatStr f) (← decStr (← field j "r"))
      | _, _, _ => throw "bad value"

/-- A small int field, 0 when absent. -/
def mode (j : Json) (key : String) : Nat :=
  match j.getObjVal? key with
  | .ok v => (v.getNat?).toOption.getD 0
  | .error _ => 0

def hookRaise : PyExc := .valueError "hook"

/-- `0` or `1` records the text, `2` raises `ValueError`, `3` raises `StopIteration(3)`. -/
def textHook (k : NumKind) (m : Nat) : PStr → DR JVal :=
  match m with
  | 2 => fun _ => .error (.exc hookRaise)
  | 3 => fun _ => .error (.stop 3)
  | _ => fun t => .ok (.hook k t)

def objHook (tag : Option String) (m : Nat) : List (PStr × JVal) → DR JVal :=
  match m with
  | 2 => fun _ => .error (.exc hookRaise)
  | 3 => fun _ => .error (.stop 3)
  | _ => fun kvs =>
    match tag with
    | some t => .ok (.arr [.str (cs t), .obj kvs])
    | none => .ok (.obj kvs)

/-- `0` is `None`, `1` wraps the list, `2` and `3` raise. -/
def arrHook (m : Nat) : Option (List JVal → DR JVal) :=
  match m with
  | 0 => none
  | 2 => some fun _ => .error (.exc hookRaise)
  | 3 => some fun _ => .error (.stop 3)
  | _ => some fun xs => .ok (.arr [.str (cs "A"), .arr xs])

def getDCfg (j : Json) : Except String DCfg := do
  let oh := mode j "ohook"
  let ph := mode j "phook"
  let pi := mode j "pint"
  return { strict := ← getBool j "strict"
           objectHook := if oh = 0 then none else some (objHook (some "H") oh)
           pairsHook := if ph = 0 then none else some (objHook none ph)
           arrayHook := arrHook (mode j "ahook")
           parseFloat := textHook .float (mode j "pfloat")
           parseIntFn := if pi = 0 then none else some (textHook .int pi)
           parseConstant := textHook .const (mode j "pconst") }

/-- A float returned by `default()`, or the exception it raises, by object. -/
def getDflt (j : Json) : Except String (List (Nat × Option EVal)) := do
  let a ← (← field j "dflt").getArr?
  a.toList.mapM fun p => do
    let q ← p.getArr?
    let n ← (q.getD 0 .null).getNat?
    match q.getD 1 .null with
    | .null => return (n, none)
    | v => return (n, some (← decEVal (v.getObjValD "v")))

def dfltFn (tbl : List (Nat × Option EVal)) (n : Nat) (t : String) : Except PyExc EVal :=
  match tbl.lookup n with
  | some (some v) => .ok v
  | some none => .error (.valueError "boom")
  | none => .error (defaultErr t)

def dfltBound (tbl : List (Nat × Option EVal)) : Nat :=
  tbl.foldl (fun a p => a + (match p.2 with
    | some v => v.depth
    | none => 0) + 2) 0

def getECfg (j : Json) : Except String ECfg := do
  let indent ← match j.getObjVal? "indent" with
    | .ok .null | .error _ => pure none
    | .ok v => some <$> decStr v
  let tbl ← getDflt j
  return { ensureAscii := ← getBool j "ensure_ascii", checkCircular := ← getBool j "check_circular",
           allowNan := ← getBool j "allow_nan", sortKeys := ← getBool j "sort_keys",
           skipKeys := ← getBool j "skipkeys", indent,
           itemSep := ← decStr (← field j "item_sep"), keySep := ← decStr (← field j "key_sep")
           dflt := dfltFn tbl, dfltDepth := dfltBound tbl }

def getEncArgs (j : Json) : Except String EncArgs := do
  let indent : IndentArg ← match j.getObjVal? "indent" with
    | .ok .null | .error _ => pure .none
    | .ok v =>
      match v.getObjVal? "s", v.getObjVal? "i" with
      | .ok s, _ => .str <$> decStr s
      | _, .ok i => .int <$> decIntStr i
      | _, _ => throw "bad indent"
  let separators ← match j.getObjVal? "seps" with
    | .ok .null | .error _ => pure none
    | .ok v =>
      let a ← v.getArr?
      pure (some (← decStr (a.getD 0 .null), ← decStr (a.getD 1 .null)))
  let hasD := mode j "has_default" = 1
  let tbl ← getDflt j
  let kw ← (← field j "kw").getArr?
  return { skipkeys := ← getBool j "skipkeys", ensureAscii := ← getBool j "ensure_ascii"
           checkCircular := ← getBool j "check_circular", allowNan := ← getBool j "allow_nan"
           sortKeys := ← getBool j "sort_keys", indent, separators
           default := if hasD then some (dfltFn tbl) else none
           dfltDepth := dfltBound tbl
           kw := ← kw.toList.mapM (·.getStr?) }

/-- The hooks of `json.loads`: `0` is `None`, `1` records, `2` and `3` raise, `4`
is a false callable. -/
def apiHook (tag : String) (m : Nat) : HookArg :=
  match m with
  | 0 => none
  | 1 => some (true, fun t => .ok (.arr [.str (cs tag), .str t]))
  | 2 => some (true, fun _ => .error (.exc hookRaise))
  | 3 => some (true, fun _ => .error (.stop 3))
  | _ => some (false, fun t => .ok (.str t))

def getDecArgs (j : Json) : Except String DecArgs := do
  let oh := mode j "ohook"
  let ph := mode j "phook"
  let kw ← (← field j "kw").getArr?
  let strict ← match j.getObjVal? "strict" with
    | .ok .null | .error _ => pure none
    | .ok v => some <$> v.getBool?
  return { objectHook := if oh = 0 then none else some (objHook (some "H") oh)
           objectPairsHook := if ph = 0 then none else some (objHook none ph)
           arrayHook := arrHook (mode j "ahook")
           parseFloat := apiHook "F" (mode j "pfloat")
           parseInt := apiHook "I" (mode j "pint")
           parseConstant := apiHook "C" (mode j "pconst")
           strict, kw := ← kw.toList.mapM (·.getStr?) }

def getLoadArg (j : Json) : Except String LoadArg := do
  let a ← field j "arg"
  match a.getObjVal? "s", a.getObjVal? "b" with
  | .ok s, _ => .str <$> decStr s
  | _, .ok b => .bytes <$> decStr b
  | _, _ => .other <$> getStr a "other"

def getStrArg (a : Json) : Except String StrArg :=
  match a.getObjVal? "s" with
  | .ok s => .str <$> decStr s
  | .error _ => .other <$> getStr a "other"

def encDR {α : Type} (doc : PStr) (enc : α → Json) : DR α → Json
  | .ok v => Json.mkObj [("ok", enc v)]
  | .error e => encPy enc (.error (e.toPy doc))

/-- Chunks and the class of the exception that ended them. -/
def encYield (y : Yield) : Json :=
  Json.mkObj [("ok", Json.mkObj [("chunks", Json.arr (y.1.toArray.map encStr)),
    ("exc", match y.2 with
      | some e => toJson e.className
      | none => Json.null)])]

/-- The fixed theme of the difftest. -/
def testTheme : Theme where
  color c := cs (if c = "definition" then "<K>" else if c = "string" then "<S>"
    else if c = "number" then "<N>" else "<W>")
  reset := cs "</>"

def encFn (m : Nat) : EncoderArg :=
  match m with
  | 0 => .cAscii
  | 1 => .cPlain
  | 2 => .custom fun s => .ok (.str ([60] ++ s ++ [62]))
  | 3 => .custom fun _ => .ok (.nonstr "int")
  | 5 => .custom fun _ => .ok (.nonstr (String.ofList (List.replicate 41 'é')))
  | _ => .custom fun _ => .error (.valueError "boom")

def isSurrChunk (c : PStr) : Bool := c.any fun x => 0xd800 ≤ x && x ≤ 0xdfff

def getToolEnv (j : Json) : Except String ToolEnv := do
  let a ← (← field j "floats").getArr?
  let ps ← a.toList.mapM fun p => do
    let q ← p.getArr?
    return (← decStr (q.getD 0 .null), (← decNatStr (q.getD 1 .null), ← decStr (q.getD 2 .null)))
  let strictOut ← getBool j "strict_out"
  return { fl := fun t => match ps.lookup t with
             | some (b, r) => .flt b r
             | none => .none
           theme := if mode j "color" = 1 then some testTheme else none
           wr := fun c =>
             if strictOut && isSurrChunk c then some (.named "UnicodeEncodeError" "~surrogate") else none }

def getToolOpts (j : Json) : Except String ToolOpts := do
  let indent ← match j.getObjVal? "indent" with
    | .ok .null | .error _ => pure ToolIndent.none
    | .ok v =>
      match v.getStr? with
      | .ok _ => pure ToolIndent.tab
      | .error _ => .num <$> v.getInt?
  return { sortKeys := ← getBool j "sort_keys", ensureAscii := ← getBool j "ensure_ascii"
           jsonLines := ← getBool j "json_lines", compact := ← getBool j "compact", indent }

/-! ### The full encoder model (`EncFull.lean`) -/

def decPyType (j : Json) : Except String PyType := do
  return { name := ← getStr j "name", qualname := ← getStr j "qualname", module := ← getStr j "module",
           tpName := ← getStr j "tpName", heap := ← getBool j "heap" }

def decXKey (j : Json) : Except String XKey :=
  match j with
  | .null => pure .none
  | _ =>
    match j.getObjVal? "s", j.getObjVal? "i", j.getObjVal? "b", j.getObjVal? "o", j.getObjVal? "f" with
    | .ok s, _, _, _, _ => .str <$> decStr s
    | _, .ok i, _, _, _ => .int <$> decIntStr i
    | _, _, .ok b, _, _ => .bool <$> b.getBool?
    | _, _, _, .ok o, _ => do return .obj (← decPyType o) (← decIntStr (← field j "ord"))
    | _, _, _, _, .ok f => do return .flt (← decNatStr f) (← decStr (← field j "r"))
    | _, _, _, _, _ => throw "bad key"

def decStop (j : Json) : Except String (Option PyExc) :=
  match j.getObjVal? "stop" with
  | .ok .null | .error _ => pure none
  | .ok m => do return some (.valueError (← m.getStr?))

mutual
partial def decXVal (j : Json) : Except String XVal :=
  match j with
  | .null => pure .none
  | .bool b => pure (.bool b)
  | _ =>
    match j.getObjVal? "s", j.getObjVal? "i", j.getObjVal? "l", j.getObjVal? "d" with
    | .ok s, _, _, _ => .str <$> decStr s
    | _, .ok i, _, _ => .int <$> decIntStr i
    | _, _, .ok l, _ => do
      let a ← l.getArr?
      let xs ← a.toList.mapM decXVal
      match j.getObjVal? "sub" with
      | .ok sb => return .seqSub (← decPyType (← field j "t")) (← getBool sb "truth") xs (← decStop sb)
      | .error _ => return .seq (← decPyType (← field j "t")) xs
    | _, _, _, .ok d => do
      let a ← d.getArr?
      match j.getObjVal? "sub" with
      | .ok sb =>
        let its ← a.toList.mapM fun p => do
          let q ← p.getArr?
          let sh : ItemShape := match (q.getD 0 .null).getNat? with
            | .ok 1 => .lst
            | .ok 2 => .bad (.valueError "too many values to unpack (expected 2, got 3)")
            | _ => .tup
          return (sh, ← decXKey (q.getD 1 .null), ← decXVal (q.getD 2 .null))
        let head : ItemsHead ← match mode sb "head" with
          | 1 => pure (.raises (.valueError "items"))
          | 2 => pure (.notIter { name := "int" })
          | _ => pure .ok
        return .mapSub (← decPyType (← field j "t")) (← getNat sb "used") (← getBool sb "truth") head its (← decStop sb)
      | .error _ =>
        let kvs ← a.toList.mapM fun p => do
          let q ← p.getArr?
          return (← decXKey (q.getD 0 .null), ← decXVal (q.getD 1 .null))
        return .map (← decPyType (← field j "t")) kvs
    | _, _, _, _ =>
      match j.getObjVal? "back", j.getObjVal? "other", j.getObjVal? "f" with
      | .ok k, _, _ => .back <$> k.getNat?
      | _, .ok n, _ => do return .other (← n.getNat?) (← decPyType (← field j "t"))
      | _, _, .ok f => do return .flt (← decNatStr f) (← decStr (← field j "r"))
      | _, _, _ => throw "bad value"
end

/-- A separator: `0` an exact `str`, `1` a subclass whose `__str__` returns `'X'`, `2` one whose
`__str__` raises `ValueError('sep')`. -/
def decSObj (j : Json) : Except String SObj := do
  let s ← decStr (← field j "s")
  match mode j "sub" with
  | 1 => return ⟨s, false, .ok (cs "X")⟩
  | 2 => return ⟨s, false, .error (.valueError "sep")⟩
  | _ => return SObj.ofStr s

def getXCfg (j : Json) : Except String XCfg := do
  let indent ← match j.getObjVal? "indent" with
    | .ok .null | .error _ => pure none
    | .ok v => some <$> decStr v
  let a ← (← field j "dflt").getArr?
  let tbl ← a.toList.mapM fun p => do
    let q ← p.getArr?
    let n ← (q.getD 0 .null).getNat?
    match q.getD 1 .null with
    | .null => return (n, none)
    | v => return (n, some (← decXVal (v.getObjValD "v")))
  return { ensureAscii := ← getBool j "ensure_ascii", checkCircular := ← getBool j "check_circular",
           allowNan := ← getBool j "allow_nan", sortKeys := ← getBool j "sort_keys",
           skipKeys := ← getBool j "skipkeys", indent,
           itemSep := ← decSObj (← field j "item_sep"), keySep := ← decSObj (← field j "key_sep")
           dflt := fun n t => match tbl.lookup n with
             | some (some v) => .ok v
             | some none => .error (.valueError "boom")
             | none => .error (defaultErr t.name) }

/-- `repr` of an ASCII `str` (`unicode_repr`): single quotes unless the text has one and no double
quote; `\\`, the quote, `\t`, `\n`, `\r` and `\xNN` escaped. Other code points are not rendered. -/
def reprAsciiStr (s : PStr) : String :=
  let q : Nat := if 39 ∈ s ∧ 34 ∉ s then 34 else 39
  let body := s.flatMap fun c =>
    if c = 92 then [92, 92] else if c = q then [92, q] else if c = 10 then [92, 110]
    else if c = 13 then [92, 114] else if c = 9 then [92, 116]
    else if c < 32 ∨ c = 127 then [92, 120] ++ ((hex2 c).toList.map Char.toNat)
    else if c < 127 then [c] else cs "?"
  String.ofList ((q :: body ++ [q]).map Char.ofNat)

def KeyShown.text : KeyShown → String
  | .str s => reprAsciiStr s
  | .int n => toString n
  | .flt r => String.ofList (r.map Char.ofNat)
  | .bool b => if b then "True" else "False"
  | .none => "None"
  | .obj t => s!"<{t}>"

def NoteShown.text : NoteShown → String
  | .item tn i => s!"when serializing {tn} item {i}"
  | .key tn k => s!"when serializing {tn} item {k.text}"
  | .obj tn => s!"when serializing {tn} object"

def encXR (show_ : Note → NoteShown) : XR → Json
  | .ok t => Json.mkObj [("ok", Json.mkObj [("text", encStr t)])]
  | .error (e, ns) => Json.mkObj [("ok", Json.mkObj [("exc", toJson e.className),
      ("msg", toJson (if e.message.startsWith "~" then "~" else e.message)),
      ("notes", Json.arr (ns.toArray.map fun n => toJson (show_ n).text))])]

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "loads_py" | "loads_c" =>
    let s ← decStr (← field j "s")
    let cfg ← getDCfg j
    let r := if fn = "loads_py" then loadsPy cfg s else loadsC cfg s
    return encDR s (encJVal false) r
  | "raw_py" | "raw_c" =>
    let s ← decStr (← field j "s")
    let cfg ← getDCfg j
    let idx ← decIntStr (← field j "idx")
    let r := if fn = "raw_py" then rawDecodePy cfg s idx else rawDecodeC cfg s idx
    return encDR s (fun (v, e) => Json.arr #[encJVal false v, toJson (toString e)]) r
  | "scanstr_py" =>
    let s ← decStr (← field j "s")
    let e ← decIntStr (← field j "end")
    return encDR s (fun (v, e) => Json.arr #[encStr v, toJson (toString e)]) (pyScanstringCall s e (← getBool j "strict"))
  | "scanstr_c" =>
    let x ← getStrArg (← field j "x")
    let e ← decIntStr (← field j "end")
    let doc := match x with
      | .str s => s
      | .other _ => []
    return encDR doc (fun (v, e) => Json.arr #[encStr v, toJson (toString e)]) (cPyScanstring x e (← getBool j "strict"))
  | "encstr_c" =>
    let x ← getStrArg (← field j "x")
    let r := if ← getBool j "ascii" then cPyEncodeBasestringAscii x else cPyEncodeBasestring x
    return encPy encStr r
  | "encstr_py" =>
    let s ← decStr (← field j "s")
    return encPy encStr (.ok (if ← getBool j "ascii" then pyEncodeBasestringAscii s else pyEncodeBasestring s))
  | "dumps_py" | "dumps_c" =>
    let v ← decEVal (← field j "v")
    let cfg ← getECfg j
    let r := if fn = "dumps_py" then dumpsPy cfg v else dumpsC cfg v
    return encPy encStr r
  | "api_dumps_py" | "api_dumps_c" =>
    let v ← decEVal (← field j "v")
    let a ← getEncArgs j
    return encPy encStr (jsonDumps (if fn = "api_dumps_py" then dumpsPy else dumpsC) a v)
  | "api_dump" =>
    let v ← decEVal (← field j "v")
    let a ← getEncArgs j
    let k ← getInt j "fail"
    return encYield (jsonDump a (fun i _ => if (i : Int) = k then some (.valueError "write") else none) v)
  | "iter" =>
    let v ← decEVal (← field j "v")
    return encYield (iterencode (← getECfg j) v)
  | "api_loads_py" | "api_loads_c" =>
    let x ← getLoadArg j
    let a ← getDecArgs j
    return encPy (encJVal true) (jsonLoads (if fn = "api_loads_py" then loadsPy else loadsC) a x)
  | "api_load" =>
    let x ← getLoadArg j
    let a ← getDecArgs j
    let rd := if mode j "read_fail" = 1 then .error (.named "OSError" "no read") else .ok x
    return encPy (encJVal true) (jsonLoad loadsC a rd)
  | "detect" =>
    let b ← decStr (← field j "b")
    return Json.mkObj [("ok", toJson (detectEncoding b))]
  | "decode" =>
    let b ← decStr (← field j "b")
    return encPy encStr (decodeBytes (detectEncoding b) b)
  | "jde" =>
    let e := jdeInit (← getStr j "msg") (← decStr (← field j "doc")) (← decIntStr (← field j "pos"))
    let (m, d, p) := jdeReduce e
    return Json.mkObj [("ok", Json.arr #[toJson e.errmsg, toJson (toString e.lineno), toJson (toString e.colno),
      Json.arr #[toJson m, encStr d, toJson (toString p)]])]
  | "scan_once" =>
    let x ← getStrArg (← field j "x")
    let cfg ← getDCfg j
    let idx ← decIntStr (← field j "idx")
    let doc := match x with
      | .str s => s
      | .other _ => []
    return encDR doc (fun (v, e) => Json.arr #[encJVal false v, toJson (toString e)]) (cScannerCall cfg x idx)
  | "scanner_new" =>
    let attrs ← (← (← field j "attrs").getArr?).toList.mapM (·.getStr?)
    let raising ← match j.getObjVal? "raising" with
      | .ok r => do (← r.getArr?).toList.mapM (·.getStr?)
      | .error _ => pure []
    let tp ← getStr j "tp"
    let ctx : ScanCtx := { getattr := fun a =>
                             if a ∈ raising then .error (.valueError a)
                             else if a ∈ attrs then .ok () else .error (attrErr tp a)
                           strict := match mode j "strict_mode" with
                             | 0 => .ok true
                             | 1 => .ok false
                             | _ => .error (.valueError "boom") }
    return encPy (fun (c : DCfg) => toJson c.strict) (scannerNew ctx {})
  | "make_enc" =>
    let v ← decEVal (← field j "v")
    let tbl ← getDflt j
    let indent ← match j.getObjVal? "indent" with
      | .ok .null | .error _ => pure none
      | .ok v => some <$> decStr v
    let markers : MarkersArg := match mode j "markers" with
      | 0 => .none
      | 1 => .dict
      | _ => .other "list"
    let r := encoderNew markers (dfltFn tbl) (dfltBound tbl) (encFn (mode j "encoder")) indent
      (← getStrArg (← field j "key_sep")) (← getStrArg (← field j "item_sep"))
      (← getBool j "sort_keys") (← getBool j "skipkeys") (← getBool j "allow_nan")
    let level ← decIntStr (← field j "level")
    return encPy (fun l => Json.arr (l.toArray.map encStr)) (r.bind fun cfg => encoderCall cfg v level)
  | "loads_rec_py" | "loads_rec_c" =>
    let s ← decStr (← field j "s")
    let cfg : DCfg := { strict := ← getBool j "strict" }
    let n ← getNat j "budget"
    let r := if fn = "loads_rec_py" then loadsPyR cfg n s
      else loadsCR cfg n (match getNat j "frames" with
        | .ok m => m
        | .error _ => 100000) s
    return encDR s (encJVal true) r
  | "dumpsx_py" | "dumpsx_c" =>
    let v ← decXVal (← field j "v")
    let cfg ← getXCfg j
    let n ← getNat j "budget"
    if fn = "dumpsx_py" then return encXR showPy (dumpsPyX cfg n v)
    else return encXR showC (dumpsCX cfg n v)
  | "colorize" =>
    return Json.mkObj [("ok", encStr (colorizeJson testTheme (← decStr (← field j "s"))))]
  | "tool" =>
    let r := toolMain (← getToolOpts j) (← getToolEnv j) (← decStr (← field j "s"))
    return Json.mkObj [("ok", Json.mkObj [("out", encStr r.out),
      ("exc", match r.exit with
        | some e => toJson e.className
        | none => Json.null),
      ("msg", match r.exit with
        | some e => toJson e.message
        | none => Json.null)])]
  | other => throw s!"unknown fn {other}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.JsonMod
