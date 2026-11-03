import PyLean.DiffCore
import PyLean.TextLibs.TomlModel

/-! `toml.*` difftest cases; see `TomlArea` in `difftest/textlibs_diff.py`.

A document travels as a list of code points. `pf` names the `parse_float` the case uses:
`float`, `tag` (returns an object), `raise_e` (raises `ValueError('pf-raise')` on strings with
`e` or `E`), `list_dot` (returns `[]` on strings with `.`), `dict_inf` (returns `{}` on strings
with `i`). A value is `{"s"}`, `{"i": hex}`, `{"f"}`, `{"b"}`, `{"d"}`, `{"dt", "tz"}`, `{"t"}`,
`{"a"}` or `{"o": [[key, value], ...]}`. -/

namespace PyLean.TextLibs.Toml

open Lean PyLean PyLean.Diff

def natsJ (j : Json) : Except String (List Nat) := do (← j.getArr?).toList.mapM Json.getNat?

def hexStr (i : Int) : String :=
  (if i < 0 then "-" else "") ++ String.ofList (Nat.toDigits 16 i.natAbs)

partial def encVal : TVal → Json
  | .str s => Json.mkObj [("s", toJson s)]
  | .int i => Json.mkObj [("i", toJson (hexStr i))]
  | .flt s => Json.mkObj [("f", toJson s)]
  | .bool b => Json.mkObj [("b", toJson b)]
  | .date y m d => Json.mkObj [("d", toJson [y, m, d])]
  | .datetime y mo d h mi s us tz =>
    Json.mkObj [("dt", toJson [y, mo, d, h, mi, s, us]), ("tz", match tz with
      | none => Json.null
      | some m => toJson m)]
  | .time h mi s us => Json.mkObj [("t", toJson [h, mi, s, us])]
  | .arr xs => Json.mkObj [("a", Json.arr (xs.map encVal).toArray)]
  | .tbl kvs => Json.mkObj [("o", Json.arr (kvs.map (fun p => Json.arr #[toJson p.1, encVal p.2])).toArray)]

def hasC (s : Str) (cs : List Nat) : Bool := s.any (fun c => cs.contains c)

/-- The callables of `toml_pf`; `frames` counts their Python frames: `TomlTag(s)` runs
`TomlTag.__init__`, the functions are one frame and call `TomlTag` unless they raise or return a
list or dict. -/
def pfJ (name : String) : Except String ParseFloat :=
  match name with
  | "float" => .ok (ParseFloat.mk true (fun _ => .ok .other) (fun _ => 0))
  | "tag" => .ok (ParseFloat.mk false (fun _ => .ok .other) (fun _ => 1))
  | "raise_e" => .ok (ParseFloat.mk false
      (fun s => if hasC s [101, 69] then .error (.valueError "pf-raise") else .ok .other)
      (fun s => if hasC s [101, 69] then 1 else 2))
  | "list_dot" => .ok (ParseFloat.mk false (fun s => .ok (if hasC s [46] then .dictOrList else .other))
      (fun s => if hasC s [46] then 1 else 2))
  | "dict_inf" => .ok (ParseFloat.mk false (fun s => .ok (if hasC s [105] then .dictOrList else .other))
      (fun s => if hasC s [105] then 1 else 2))
  | n => .error s!"bad pf {n}"

/-- The difftest fills `cached_tz`'s cache with every offset before it starts. -/
def tzAll : Str → Str → Nat → Bool := fun _ _ _ => true

def eargJ (j : Json) : Except String EArg :=
  match j with
  | .null => .ok .dflt
  | _ =>
    match j.getObjVal? "s", j.getObjVal? "i", j.getObjVal? "o" with
    | .ok v, _, _ => (natsJ v).map .str
    | _, .ok v, _ => v.getInt?.map .int
    | _, _, .ok v => (natsJ v).map .obj
    | _, _, _ => .error "earg"

def encEArg : EArg → Json
  | .dflt => Json.null
  | .str s => Json.mkObj [("s", toJson s)]
  | .int i => Json.mkObj [("i", toJson i)]
  | .obj t => Json.mkObj [("o", toJson t)]

def encInit : TdeInit → Json
  | .legacy args => Json.mkObj [("legacy", Json.arr (args.map encEArg).toArray)]
  | .full r => Json.mkObj [("errmsg", toJson r.errmsg), ("msg", toJson r.msg), ("doc", toJson r.doc),
      ("pos", toJson r.pos), ("lineno", toJson r.lineno), ("colno", toJson r.colno)]

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "toml.loads" =>
    let pf ← pfJ (← getStr j "pf")
    let s ← match j.getObjVal? "doc" with
      | .ok v => SArg.str <$> natsJ v
      | .error _ => SArg.other <$> getStr j "type"
    let r := loads pf (← getNat j "maxk") (← getNat j "maxd") tzAll (← getNat j "frames") s
    return encPy (fun (d : Dict) => encVal (.tbl d)) r
  | "toml.load" =>
    let pf ← pfJ (← getStr j "pf")
    let rd : Py ReadVal ← match j.getObjVal? "bytes" with
      | .ok v => (fun b => .ok (.bytes b)) <$> natsJ v
      | .error _ => pure (.ok .noDecode)
    let r := load pf (← getNat j "maxk") (← getNat j "maxd") tzAll (← getNat j "frames") rd
    return encPy (fun (d : Dict) => encVal (.tbl d)) r
  | "toml.err" =>
    let args ← (← (← field j "args").getArr?).toList.mapM eargJ
    let r := tdeInit (← getBool j "werr") (← eargJ (← field j "msg")) (← eargJ (← field j "doc"))
      (← eargJ (← field j "pos")) args
    return encPy encInit r
  | _ => throw s!"unknown fn {fn}"

end PyLean.TextLibs.Toml
