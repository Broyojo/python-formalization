import PyLean.DiffCore
import PyLean.TextLibs.EmailHeaders
import PyLean.TextLibs.EmailFrames

/-! `email.*` difftest cases; see `EmailArea` in `difftest/textlibs_diff.py`.

A case carries the input `v` (code points), the `_ew.decode` calls CPython made on it (`dec`:
`[arg, outcome]` pairs, where an outcome is `{"ok": [text, charset, lang, defects]}`,
`{"caught": 0}` or `{"raise": [cls, msg]}`; a call the table lacks is an `OracleMiss`
exception, so a model that decodes something CPython did not shows up as a mismatch),
`maxd`, and for `get_invalid_mailbox` and `_get_ptext_to_endchars` the end characters `endc`.

The answer is always `{"ok": ...}`: `{"err": [cls, msg]}` for an exception, otherwise
`{"r": [tree, rest, str, value]}` where `rest` is `null` for the `parse_*` functions, `str` is
`null` for a tree with a `MimeParameters` node (its `__str__` is not modelled), and
`value` is `{"v": text}` or `{"e": [cls, msg]}`. A tree is `["T", class, text, token_type,
defects]` or `["L", class, token_type, elements, defects, attributes]`. -/

namespace PyLean.TextLibs.Email

open Lean PyLean PyLean.Diff

def natsJ (j : Json) : Except String (List Nat) := do (← j.getArr?).toList.mapM Json.getNat?

def strJ (s : Str) : Json := toJson s

def defectJ (d : Defect) : Json := Json.arr #[toJson d.cls, strJ d.msg]

def avJ : AV → Json
  | .s x => Json.mkObj [("s", strJ x)]
  | .n x => Json.mkObj [("n", toJson (toString x))]
  | .b x => Json.mkObj [("b", toJson x)]

partial def tokJ : Tok → Json
  | .term c s ty ds => Json.arr #[toJson "T", toJson c.name, strJ s, toJson ty,
      Json.arr (ds.map defectJ).toArray]
  | .node c ty ks ds a => Json.arr #[toJson "L", toJson c.name, toJson ty,
      Json.arr (ks.map tokJ).toArray, Json.arr (ds.map defectJ).toArray,
      Json.arr (a.map (fun p => Json.arr #[toJson p.1, avJ p.2])).toArray]

def excJ (e : EExc) : Json := Json.arr #[toJson e.cls, strJ e.msg]

def valJ (r : EPy Str) : Json :=
  match r with
  | .ok v => Json.mkObj [("v", strJ v)]
  | .error e => Json.mkObj [("e", excJ e)]

/-- The tree holds a `mime-parameters` node, whose `__str__` is not modelled. -/
partial def hasMp : Tok → Bool
  | .node .mimeParameters .. => true
  | .node _ _ ks _ _ => ks.any hasMp
  | .term .. => false

def treeJ (t : Tok) (rest : Option Str) : Json :=
  Json.mkObj [("r", Json.arr #[tokJ t, (match rest with
    | some r => strJ r
    | none => Json.null), if hasMp t then Json.null else strJ t.str, valJ t.value])]

def errJ (e : EExc) : Json := Json.mkObj [("err", excJ e)]

def outJ {α : Type} (f : α → Json) : EPy α → Json
  | .ok a => Json.mkObj [("ok", f a)]
  | .error e => Json.mkObj [("ok", errJ e)]

def decOutJ (j : Json) : Except String DecOut := do
  match j.getObjVal? "ok", j.getObjVal? "raise" with
  | .ok v, _ =>
    let a ← v.getArr?
    let ds ← (← (a.getD 3 Json.null).getArr?).toList.mapM (fun d => do
      let p ← d.getArr?
      pure (⟨← (p.getD 0 Json.null).getStr?, ← natsJ (p.getD 1 Json.null)⟩ : Defect))
    pure (.ok (← natsJ (a.getD 0 Json.null)) (← natsJ (a.getD 1 Json.null))
      (← natsJ (a.getD 2 Json.null)) ds)
  | _, .ok v =>
    let a ← v.getArr?
    pure (.raise (← (a.getD 0 Json.null).getStr?) (← natsJ (a.getD 1 Json.null)))
  | _, _ => pure .caught

def cfgJ (j : Json) : Except String Cfg := do
  let tbl ← (← (← field j "dec").getArr?).toList.mapM (fun e => do
    let p ← e.getArr?
    pure (← natsJ (p.getD 0 Json.null), ← decOutJ (p.getD 1 Json.null)))
  let dec : Str → DecOut := fun s => match tbl.find? (·.1 == s) with
    | some (_, o) => o
    | none => .raise "OracleMiss" s
  pure { dec, maxd := ← getNat j "maxd" }

def run (fn : String) (j : Json) : Except String Json := do
  let cfg ← cfgJ j
  let v ← natsJ (← field j "v")
  let n := 8 * v.length + 64
  let endc ← match j.getObjVal? "endc" with
    | .ok e => natsJ e
    | .error _ => pure []
  let pair (r : EPy (Tok × Str)) : Json := outJ (fun p => treeJ p.1 (some p.2)) r
  let whole (r : EPy Tok) : Json := outJ (fun t => treeJ t none) r
  match fn with
  | "email.get_address_list" => return pair (getAddressList cfg n v)
  | "email.get_unstructured" => return whole (getUnstructured cfg n v)
  | "email.get_mailbox_list" => return pair (getMailboxList cfg n v)
  | "email.get_mailbox" => return pair (getMailbox cfg n v)
  | "email.get_address" => return pair (getAddress cfg n v)
  | "email.get_group" => return pair (getGroup cfg n v)
  | "email.get_group_list" => return pair (getGroupList cfg n v)
  | "email.get_name_addr" => return pair (getNameAddr cfg n v)
  | "email.get_angle_addr" => return pair (getAngleAddr cfg n v)
  | "email.get_obs_route" => return pair (getObsRoute cfg n v)
  | "email.get_addr_spec" => return pair (getAddrSpec cfg n v)
  | "email.get_local_part" => return pair (getLocalPart cfg n v)
  | "email.get_obs_local_part" => return pair (getObsLocalPart cfg n v)
  | "email.get_domain" => return pair (getDomain cfg n v)
  | "email.get_domain_literal" => return pair (getDomainLiteral n v)
  | "email.get_dtext" => return pair (getDtext v)
  | "email.get_display_name" =>
    return outJ (fun (p : Tok × Str) => Json.mkObj [("r", (treeJ p.1 (some p.2)).getObjValD "r"),
      ("dn", valJ (displayName p.1))]) (getDisplayName cfg n v)
  | "email.get_phrase" => return pair (getPhrase cfg n v)
  | "email.get_word" => return pair (getWord cfg n v)
  | "email.get_atom" => return pair (getAtom cfg n v)
  | "email.get_dot_atom" => return pair (getDotAtom cfg n v)
  | "email.get_dot_atom_text" => return pair (getDotAtomText n v)
  | "email.get_atext" => return pair (getAtext v)
  | "email.get_quoted_string" => return pair (getQuotedString cfg n v)
  | "email.get_bare_quoted_string" => return pair (getBareQuotedString cfg n v)
  | "email.get_qcontent" => return pair (getQcontent v)
  | "email.get_qp_ctext" => return pair (getQpCtext v)
  | "email.get_comment" => return pair (getComment n v)
  | "email.get_cfws" => return pair (getCfws n v)
  | "email.get_fws" => return pair (.ok (getFws v))
  | "email.get_encoded_word" => return pair (getEncodedWord cfg v "vtext")
  | "email.get_invalid_mailbox" => return pair (getInvalidMailbox cfg n v (endc.contains ·))
  | "email.get_no_fold_literal" => return pair (getNoFoldLiteral v)
  | "email.get_msg_id" => return pair (getMsgId cfg n v)
  | "email.parse_message_id" => return whole (parseMessageId cfg n v)
  | "email.parse_message_ids" => return whole (parseMessageIds cfg n v)
  | "email.parse_mime_version" => return whole (parseMimeVersion cfg n v)
  | "email.get_invalid_parameter" => return pair (getInvalidParameter cfg n v)
  | "email.get_ttext" => return pair (getTtext v)
  | "email.get_token" => return pair (getToken n v)
  | "email.get_attrtext" => return pair (getAttrtext v)
  | "email.get_attribute" => return pair (getAttribute n v)
  | "email.get_extended_attrtext" => return pair (getExtendedAttrtext v)
  | "email.get_extended_attribute" => return pair (getExtendedAttribute n v)
  | "email.get_section" => return pair (getSection cfg v)
  | "email.get_value" => return pair (getValue cfg n v)
  | "email.get_parameter" => return pair (getParameter cfg n v)
  | "email.parse_mime_parameters" => return whole (parseMimeParameters cfg n v)
  | "email.parse_content_type_header" => return whole (parseContentTypeHeader cfg n v)
  | "email.parse_content_disposition_header" => return whole (parseContentDispositionHeader cfg n v)
  | "email.parse_content_transfer_encoding_header" => return whole (parseCteHeader cfg n v)
  | "email._get_ptext_to_endchars" =>
    return outJ (fun (r : Str × Str × Bool) => Json.mkObj [("p", Json.arr #[strJ r.1, strJ r.2.1,
      toJson r.2.2])]) (getPtextToEndchars v (endc.contains ·))
  | _ => throw s!"unknown fn {fn}"

/-- `emailfr.get_comment` cases: `get_comment(v)` with `r` frames left, then `str()` and
`content` of the comment with `r` frames left. -/
def runFrames (j : Json) : Except String Json := do
  let v ← natsJ (← field j "v")
  let r ← getNat j "r"
  let n := 8 * v.length + 64
  return Json.mkObj [("ok", match getCommentR r n v with
    | .ok (c, rest) => Json.mkObj [("t", tokJ c), ("rest", strJ rest),
        ("s", valJ (commentStrR r c)), ("c", valJ (commentContentR r c))]
    | .error e => errJ e)]

end PyLean.TextLibs.Email
