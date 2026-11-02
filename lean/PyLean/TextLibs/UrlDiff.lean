import PyLean.DiffCore
import PyLean.TextLibs.UrlModel

/-! `url.*` difftest cases; see `UrlArea` in `difftest/textlibs_diff.py`.

An argument is `null` (None), `{"s": [...]}` (str), `{"b": [...]}` (bytes) or `{"ba": [...]}`
(bytearray). The two library oracles come with the case: `nfkc` maps a character to its NFKC
form (other characters map to themselves; the generator only uses characters whose NFKC form
does not interact with their neighbours), and `ip` lists the strings `ipaddress.ip_address`
accepts, with `true` for IPv4. -/

namespace PyLean.TextLibs.Url

open Lean PyLean PyLean.Diff

def natsJ (j : Json) : Except String (List Nat) := do (← j.getArr?).toList.mapM Json.getNat?

def argJ (j : Json) : Except String Arg :=
  match j with
  | .null => .ok .none
  | _ =>
    match j.getObjVal? "s", j.getObjVal? "b", j.getObjVal? "ba" with
    | .ok v, _, _ => (natsJ v).map .str
    | _, .ok v, _ => (natsJ v).map (fun b => .bytes b false)
    | _, _, .ok v => (natsJ v).map (fun b => .bytes b true)
    | _, _, _ => .error "arg"

def encArg : Arg → Json
  | .none => .null
  | .str s => Json.mkObj [("s", toJson s)]
  | .bytes b false => Json.mkObj [("b", toJson b)]
  | .bytes b true => Json.mkObj [("ba", toJson b)]

def encOpt (x : Option Str) : Json := match x with
  | none => .null
  | some s => toJson s

def encRes (r : Res) : Json :=
  Json.mkObj [("f", Json.arr (r.fields.map encOpt).toArray), ("b", toJson r.isBytes),
    ("k", match r.keep with
      | none => .null
      | some k => toJson k)]

def resJ (j : Json) : Except String Res := do
  let f ← (← (← field j "f").getArr?).toList.mapM (fun x => match x with
    | .null => .ok none
    | v => (natsJ v).map some)
  let k ← match ← field j "k" with
    | .null => pure none
    | v => some <$> v.getBool?
  return { fields := f, isBytes := ← getBool j "b", keep := k }

def optBool (j : Json) (k : String) : Except String (Option Bool) :=
  match j.getObjVal? k with
  | .ok .null => .ok none
  | .ok v => some <$> v.getBool?
  | .error _ => .ok none

def encName : String → Except String Enc
  | "utf-8" => .ok .utf8
  | "ascii" => .ok .ascii
  | "latin-1" => .ok .latin1
  | e => .error s!"bad encoding {e}"

def handlerName : String → Except String UnicodeObj.ErrHandler
  | "strict" => .ok .strict
  | "ignore" => .ok .ignore
  | "replace" => .ok .replace
  | "surrogateescape" => .ok .surrogateescape
  | "backslashreplace" => .ok .backslashreplace
  | "surrogatepass" => .ok .surrogatepass
  | "xmlcharrefreplace" => .ok .xmlcharrefreplace
  | e => .error s!"bad handler {e}"

/-- `encoding`: absent gives `dflt`, `null` gives `None`. -/
def encOptJ (j : Json) (k : String) (dflt : Option Enc) : Except String (Option Enc) :=
  match j.getObjVal? k with
  | .ok .null => .ok none
  | .ok v => do some <$> encName (← v.getStr?)
  | .error _ => .ok dflt

def errOptJ (j : Json) (k : String) (dflt : Option UnicodeObj.ErrHandler) :
    Except String (Option UnicodeObj.ErrHandler) :=
  match j.getObjVal? k with
  | .ok .null => .ok none
  | .ok v => do some <$> handlerName (← v.getStr?)
  | .error _ => .ok dflt

def nfkcJ (j : Json) : Except String (Str → Str) := do
  let tbl ← match j.getObjVal? "nfkc" with
    | .ok v => (← v.getArr?).toList.mapM (fun p => do
        match (← p.getArr?).toList with
        | [c, m] => return ((← c.getNat?), (← natsJ m))
        | _ => throw "nfkc")
    | .error _ => pure []
  return fun s => s.flatMap (fun c => match tbl.find? (·.1 == c) with
    | some (_, m) => m
    | none => [c])

def ipJ (j : Json) : Except String (Str → Option Bool) := do
  let tbl ← match j.getObjVal? "ip" with
    | .ok v => (← v.getArr?).toList.mapM (fun p => do
        match (← p.getArr?).toList with
        | [s, v4] => return ((← natsJ s), (← v4.getBool?))
        | _ => throw "ip")
    | .error _ => pure []
  return fun s => (tbl.find? (·.1 == s)).map (·.2)

def encPyArg (r : Py Arg) : Json := encPy encArg r
def encPyStr (r : Py Str) : Json := encPy (fun (s : Str) => toJson s) r

def portJ' (x : Option Nat) : Json := match x with
  | none => Json.null
  | some n => toJson n

/-- The attributes of a split or parse result, and `geturl()`, `encode`/`decode`. -/
def resOut (r : Res) (geturl : Res → Py Arg) : Json :=
  let trans := if r.isBytes then resDecode r .ascii .strict else resEncode r .ascii .strict
  Json.mkObj [("res", encRes r), ("user", encOpt (username r)), ("pw", encOpt (password r)),
    ("host", encPy (fun (x : Option Str) => encOpt x) (hostname r)),
    ("port", encPy portJ' (port r)),
    ("geturl", encPyArg (geturl r)), ("trans", encPy encRes trans)]

def qvJ : Json → Except String QV
  | j =>
    match j.getObjVal? "s", j.getObjVal? "b" with
    | .ok v, _ => (natsJ v).map .str
    | _, .ok v => (natsJ v).map .bytes
    | _, _ => do
      let t ← natsJ (← field j "o")
      match j.getObjVal? "items" with
      | .ok (.arr a) => return .obj t (some (← a.toList.mapM qvLeaf))
      | _ => return .obj t none
where
  qvLeaf (j : Json) : Except String QV :=
    match j.getObjVal? "s", j.getObjVal? "b" with
    | .ok v, _ => (natsJ v).map .str
    | _, .ok v => (natsJ v).map .bytes
    | _, _ => do return .obj (← natsJ (← field j "o")) none

def queryJ (j : Json) : Except String Query := do
  match ← getStr j "kind" with
  | "map" => return .mapping (← (← (← field j "items").getArr?).toList.mapM (fun p => do
      match (← p.getArr?).toList with
      | [k, v] => return ((← qvJ k), (← qvJ v))
      | _ => throw "pair"))
  | "seq" => return .seq (← (← (← field j "items").getArr?).toList.mapM (fun e => do
      return ((← getBool e "tuple"), (← (← (← field e "xs").getArr?).toList.mapM qvJ))))
  | _ => return .noLen

def qslOptsJ (j : Json) : Except String QslOpts := do
  return { keepBlank := ← getBool j "keep", strict := ← getBool j "strict",
           encoding := ← encOptJ j "enc" (some .utf8), errors := ← errOptJ j "err" (some .replace),
           maxNum := ← getOptInt j "max", sep := ← argJ (← field j "sep") }

def nportJ (p : Str × Option Int) : Json :=
  let n : Json := match p.2 with
    | none => Json.null
    | some n => toJson n
  Json.arr #[toJson p.1, n]

def portJ (x : Option Nat) : Json := match x with
  | none => Json.null
  | some n => toJson n

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "url.split" =>
    let r := urlsplit (← nfkcJ j) (← ipJ j) (← argJ (← field j "url")) (← argJ (← field j "scheme"))
      (← getBool j "frag") (← getBool j "man")
    return encPy (fun r => resOut r splitGeturl) r
  | "url.parse" =>
    let r := urlparse (← nfkcJ j) (← ipJ j) (← argJ (← field j "url")) (← argJ (← field j "scheme"))
      (← getBool j "frag") (← getBool j "man")
    return encPy (fun r => resOut r parseGeturl) r
  | "url.defrag" =>
    let r := urldefrag (← nfkcJ j) (← ipJ j) (← argJ (← field j "url")) (← getBool j "man")
    return encPy (fun r => Json.mkObj [("res", encRes r), ("geturl", encPyArg (defragGeturl r))]) r
  | "url.unsplit" | "url.unparse" =>
    let parts ← (← (← field j "parts").getArr?).toList.mapM argJ
    let c : Comp := { parts, keep := ← optBool j "keep" }
    let ke ← optBool j "ke"
    return encPyArg (if fn == "url.unsplit" then urlunsplit c ke else urlunparse c ke)
  | "url.join" =>
    return encPyArg (urljoin (← nfkcJ j) (← ipJ j) (← argJ (← field j "base"))
      (← argJ (← field j "url")) (← getBool j "frag"))
  | "url.quote" | "url.quote_plus" =>
    let s ← argJ (← field j "s")
    let safe ← argJ (← field j "safe")
    let e ← encOptJ j "enc" none
    let h ← errOptJ j "err" none
    return encPyStr (if fn == "url.quote" then quote s safe e h else quotePlus s safe e h)
  | "url.qfb" => return encPyStr (quoteFromBytes (← argJ (← field j "s")) (← argJ (← field j "safe")))
  | "url.unquote" | "url.unquote_plus" =>
    let s ← argJ (← field j "s")
    let e ← encOptJ j "enc" (some .utf8)
    let h ← errOptJ j "err" (some .replace)
    return encPyStr (if fn == "url.unquote" then unquote s e h else unquotePlus s e h)
  | "url.uqtb" => return encPyStr (unquoteToBytes (← argJ (← field j "s")))
  | "url.qsl" =>
    return encPy (fun (l : List (Str × Str)) => toJson l)
      (parseQsl (← argJ (← field j "qs")) (← qslOptsJ j))
  | "url.qs" =>
    return encPy (fun (l : List (Str × List Str)) => toJson l)
      (parseQs (← argJ (← field j "qs")) (← qslOptsJ j))
  | "url.encode" =>
    let doseq ← getBool j "doseq"
    let safe ← argJ (← field j "safe")
    let encoding ← encOptJ j "enc" none
    let errors ← errOptJ j "err" none
    let plain ← getBool j "plain"
    let o : EncOpts := { doseq, safe, encoding, errors, via := if plain then .plain else .plus }
    return encPyStr (urlencode (← queryJ (← field j "query")) o)
  | "url.geturl" =>
    let r ← resJ (← field j "res")
    return encPyArg (match ← getStr j "kind" with
      | "split" => splitGeturl r
      | "parse" => parseGeturl r
      | _ => defragGeturl r)
  | "url.helpers" =>
    let s ← natsJ (← field j "s")
    let oj (x : Option Str) := encOpt x
    let pj (p : Str × Option Str) := Json.arr #[toJson p.1, oj p.2]
    let nport := encPy nportJ (splitnport s (← getInt j "defport"))
    return Json.mkObj [("ok", Json.mkObj [
      ("type", encPy (fun (p : Option Str × Str) => Json.arr #[oj p.1, toJson p.2]) (splittype s)),
      ("host", Json.arr #[oj (splithost s).1, toJson (splithost s).2]),
      ("user", Json.arr #[oj (splituser s).1, toJson (splituser s).2]),
      ("passwd", pj (splitpasswd s)), ("port", pj (splitport s)), ("nport", nport),
      ("query", pj (splitquery s)), ("tag", pj (splittag s)),
      ("attr", Json.arr #[toJson (splitattr s).1, toJson (splitattr s).2]),
      ("value", pj (splitvalue s)), ("unwrap", toJson (unwrap s)),
      ("tobytes", encPyStr (toBytes s))])]
  | _ => throw s!"unknown fn {fn}"

end PyLean.TextLibs.Url
