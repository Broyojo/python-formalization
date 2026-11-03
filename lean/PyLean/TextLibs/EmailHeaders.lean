import PyLean.TextLibs.EmailMime

/-!
`Lib/email/_header_value_parser.py`, CPython 3.15.2: `parse_mime_parameters` and the
Content-Type, Content-Disposition and Content-Transfer-Encoding parsers, :2635-2818.
Conventions as in `EmailLex.lean`.
-/

namespace PyLean.TextLibs.Email

open PyLean.UnicodeObj

/-- The `while value:` loop of `parse_mime_parameters`, :2649-2684. -/
def mimeParamsLoop (cfg : Cfg) : Nat → Str → Tok → EPy Tok
  | 0, _, _ => throw .fuel
  | n + 1, value, mp =>
    match value with
    | [] => pure mp
    | c :: _ => do
      let r ← (match getParameter cfg n value with
        | .ok (tok, v) => pure (.inr (mp.push tok, v))
        | .error e =>
          if !e.isHpe then throw e
          else do
            let (leader, value) ← if isCfwsLeader c then do
                let (l, v) ← getCfws n value
                pure (some l, v)
              else pure (none, value)
            match value with
            | [] =>
              -- `mime_parameters.append(leader); return`; `leader` is always set here, since
              -- `value` was not empty before `get_cfws`.
              pure (.inl (match leader with
                | some l => mp.push l
                | none => mp))
            | 59 :: _ =>
              let mp := match leader with
                | some l => mp.push l
                | none => mp
              pure (.inr (mp.addDefect (invalidHeader (S "parameter entry with no content")), value))
            | _ => do
              let (tok, v) ← getInvalidParameter cfg n value
              let tok := match leader with
                | some l => tok.prepend l
                | none => tok
              pure (.inr ((mp.push tok).addDefect (invalidHeader (S "invalid parameter " ++ tok.repr)), v))
        : EPy (Tok ⊕ (Tok × Str)))
      match r with
      | .inl mp => pure mp
      | .inr (mp, value) =>
        let (mp, value) ←
          if headIs (· != 59) value then
            match mp.kids.getLast? with
            | none => throw listIndexError
            | some param => do
              let (tok, v) ← getInvalidParameter cfg n value
              let param' := (param.setTy "invalid-parameter").pushAll tok.kids
              pure ((mp.setKids (mp.kids.dropLast ++ [param'])).addDefect
                (invalidHeader (S "parameter with invalid trailing text " ++ tok.repr)), v)
          else pure (mp, value)
        match value with
        | [] => pure mp
        | _ :: v => mimeParamsLoop cfg n v (mp.push (VT [59] "parameter-separator"))

/-- `parse_mime_parameters`, :2635-2685. -/
def parseMimeParameters (cfg : Cfg) (n : Nat) (value : Str) : EPy Tok :=
  mimeParamsLoop cfg n value (mkL .mimeParameters)

/-- The `while` loop of `_find_mime_parameters`, :2691-2697. -/
def findParamsLoop (cfg : Cfg) : Nat → Str → Tok → EPy (Tok × Str)
  | 0, _, _ => throw .fuel
  | n + 1, value, t =>
    match value with
    | [] => pure (t, [])
    | c :: rest =>
      if c == 59 then pure (t, value)
      else if isPhraseEnd c then findParamsLoop cfg n rest (t.push (VT [c] "misplaced-special"))
      else do
        let (tok, v) ← getPhrase cfg n value
        findParamsLoop cfg n v (t.push tok)

/-- `_find_mime_parameters`, :2687-2701, returning the token list it appends to. -/
def findMimeParameters (cfg : Cfg) (n : Nat) (t : Tok) (value : Str) : EPy Tok := do
  let (t, value) ← findParamsLoop cfg n value t
  match value with
  | [] => pure t
  | _ :: v => do
    let mp ← parseMimeParameters cfg n v
    pure ((t.push (VT [59] "parameter-separator")).push mp)

/-- `token.value.strip().lower()`. -/
def tokenName (t : Tok) : EPy Str := do
  let v ← t.value
  pure (lower (strip v))

/-- `parse_content_type_header`, :2703-2757. -/
def parseContentTypeHeader (cfg : Cfg) (n : Nat) (value : Str) : EPy Tok := do
  let ct := mkL .contentType
  if value.isEmpty then
    return ct.addDefect (missingValue (S "Missing content type specification"))
  match getToken n value with
  | .error e =>
    if !e.isHpe then throw e
    findMimeParameters cfg n (ct.addDefect (invalidHeader
      (S "Expected content maintype but found " ++ unicodeRepr value))) value
  | .ok (tok, value) =>
    let ct := ct.push tok
    match value with
    | 47 :: value =>
      let mt ← tokenName tok
      let ct := (ct.setAttr "maintype" (.s mt)).push (VT [47] "content-type-separator")
      match getToken n value with
      | .error e =>
        if !e.isHpe then throw e
        findMimeParameters cfg n (ct.addDefect (invalidHeader
          (S "Expected content subtype but found " ++ unicodeRepr value))) value
      | .ok (tok, value) =>
        let st ← tokenName tok
        let ct := (ct.push tok).setAttr "subtype" (.s st)
        match value with
        | [] => pure ct
        | 59 :: v => do
          let mp ← parseMimeParameters cfg n v
          pure ((ct.push (VT [59] "parameter-separator")).push mp)
        | _ =>
          let ct := ((ct.addDefect (invalidHeader
            (S "Only parameters are valid after content type, but found " ++ unicodeRepr value))).delAttr
            "maintype").delAttr "subtype"
          findMimeParameters cfg n ct value
    | _ =>
      let ct := ct.addDefect (invalidHeader (S "Invalid content type"))
      if value.isEmpty then pure ct else findMimeParameters cfg n ct value

/-- `parse_content_disposition_header`, :2759-2787. -/
def parseContentDispositionHeader (cfg : Cfg) (n : Nat) (value : Str) : EPy Tok := do
  let cd := mkL .contentDisposition
  if value.isEmpty then
    return cd.addDefect (missingValue (S "Missing content disposition"))
  match getToken n value with
  | .error e =>
    if !e.isHpe then throw e
    findMimeParameters cfg n (cd.addDefect (invalidHeader
      (S "Expected content disposition but found " ++ unicodeRepr value))) value
  | .ok (tok, value) =>
    let d ← tokenName tok
    let cd := (cd.push tok).setAttr "content_disposition" (.s d)
    match value with
    | [] => pure cd
    | 59 :: v => do
      let mp ← parseMimeParameters cfg n v
      pure ((cd.push (VT [59] "parameter-separator")).push mp)
    | _ =>
      findMimeParameters cfg n (cd.addDefect (invalidHeader
        (S "Only parameters are valid after content disposition, but found " ++ unicodeRepr value)))
        value

/-- The `while value:` loop of `parse_content_transfer_encoding_header`, :2809-2817. -/
def cteLoop (cfg : Cfg) : Nat → Str → Tok → EPy Tok
  | 0, _, _ => throw .fuel
  | n + 1, value, t =>
    match value with
    | [] => pure t
    | c :: rest =>
      let t := t.addDefect (invalidHeader (S "Extra text after content transfer encoding"))
      if isPhraseEnd c then cteLoop cfg n rest (t.push (VT [c] "misplaced-special"))
      else do
        let (tok, v) ← getPhrase cfg n value
        cteLoop cfg n v (t.push tok)

/-- `parse_content_transfer_encoding_header`, :2789-2818. -/
def parseCteHeader (cfg : Cfg) (n : Nat) (value : Str) : EPy Tok := do
  let t := mkL .cte
  if value.isEmpty then
    return t.addDefect (missingValue (S "Missing content transfer encoding"))
  let (t, value) ← match getToken n value with
    | .error e =>
      if !e.isHpe then throw e
      else pure (t.addDefect (invalidHeader
        (S "Expected content transfer encoding but found " ++ unicodeRepr value)), value)
    | .ok (tok, v) => do
      let c ← tokenName tok
      pure ((t.push tok).setAttr "cte" (.s c), v)
  cteLoop cfg n value t

end PyLean.TextLibs.Email
