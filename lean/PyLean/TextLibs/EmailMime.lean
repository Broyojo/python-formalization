import PyLean.TextLibs.EmailAddr

/-!
`Lib/email/_header_value_parser.py`, CPython 3.15.2: message ids, MIME-Version and the MIME
parameter parsers, :2087-2818. Conventions as in `EmailLex.lean`.
-/

namespace PyLean.TextLibs.Email

open PyLean.UnicodeObj

/-! ## Message ids -/

/-- `get_no_fold_literal`, :2087-2107. -/
def getNoFoldLiteral (value : Str) : EPy (Tok × Str) := do
  match value with
  | [] => throw (.hpe (S "expected no-fold-literal but found '" ++ value ++ S "'"))
  | c :: v =>
    if c != 91 then
      throw (.hpe (S "expected '[' at the start of no-fold-literal but found '" ++ value ++ S "'"))
    let nf := (mkL .noFoldLiteral).push (VT [91] "no-fold-literal-start")
    let (tok, v) ← getDtext v
    match v with
    | 93 :: v' => pure ((nf.push tok).push (VT [93] "no-fold-literal-end"), v')
    | _ => throw (.hpe (S "expected ']' at the end of no-fold-literal but found '" ++ v ++ S "'"))

/-- `get_msg_id`, :2109-2175. -/
def getMsgId (cfg : Cfg) (n : Nat) (value : Str) : EPy (Tok × Str) := do
  let (m, value) ← optCfws n (mkL .msgId) value
  match value with
  | 60 :: value =>
    let m := m.push (VT [60] "msg-id-start")
    let (m, tok, value) ←
      match getDotAtomText n value with
      | .ok (t, v) => pure (m, t, v)
      | .error e =>
        if !e.isHpe then throw e
        else match getObsLocalPart cfg n value with
          | .ok (t, v) => pure (m.addDefect (obsoleteHeader (S "obsolete id-left in msg-id")), t, v)
          | .error e2 =>
            if e2.isHpe then
              throw (.hpe (S "expected dot-atom-text or obs-id-left but found '" ++ value ++ S "'"))
            else throw e2
    let m := m.push tok
    match value with
    | 64 :: value =>
      let m := m.push (VT [64] "address-at-symbol")
      let (m, tok, value) ←
        match getDotAtomText n value with
        | .ok (t, v) => pure (m, t, v)
        | .error e =>
          if !e.isHpe then throw e
          else match getNoFoldLiteral value with
            | .ok (t, v) => pure (m, t, v)
            | .error e2 =>
              if !e2.isHpe then throw e2
              else match getDomain cfg n value with
                | .ok (t, v) => pure (m.addDefect (obsoleteHeader (S "obsolete id-right in msg-id")), t, v)
                | .error e3 =>
                  if e3.isHpe then
                    throw (.hpe (S "expected dot-atom-text, no-fold-literal or obs-id-right but found '"
                      ++ value ++ S "'"))
                  else throw e3
      let m := m.push tok
      let (m, value) := match value with
        | 62 :: v => (m, v)
        | _ => (m.addDefect (invalidHeader (S "missing trailing '>' on msg-id")), value)
      optCfws n (m.push (VT [62] "msg-id-end")) value
    | _ =>
      let m := m.addDefect (invalidHeader (S "msg-id with no id-right"))
      match value with
      | 62 :: v => pure (m.push (VT [62] "msg-id-end"), v)
      | _ => pure (m, value)
  | _ => throw (.hpe (S "expected msg-id but found '" ++ value ++ S "'"))

/-- `repr(ex)` of a `HeaderParseError` (or subclass) with one argument. -/
def excRepr (e : EExc) : Str := S e.cls ++ [40] ++ unicodeRepr e.msg ++ [41]

/-- `parse_message_id`, :2178-2196. -/
def parseMessageId (cfg : Cfg) (n : Nat) (value : Str) : EPy Tok :=
  match getMsgId cfg n value with
  | .ok (tok, v) =>
    let mi := (mkL .messageId).push tok
    pure (if v.isEmpty then mi else mi.addDefect (invalidHeader (S "Unexpected " ++ unicodeRepr v)))
  | .error e =>
    if e.isHpe then do
      let tok ← getUnstructured cfg n value
      pure ((mkL .invalidMessageId tok.kids).addDefect
        (invalidHeader (S "Invalid msg-id: " ++ excRepr e)))
    else throw e

/-- The `while value:` loop of `parse_message_ids`, :2203-2221. -/
def messageIdsLoop (cfg : Cfg) : Nat → Str → Tok → EPy Tok
  | 0, _, _ => throw .fuel
  | n + 1, value, l =>
    match value with
    | [] => pure l
    | 44 :: v =>
      messageIdsLoop cfg n v ((l.addDefect (invalidHeader (S "comma in msg-id list"))).push
        (WT [32] "invalid-comma-replacement"))
    | _ =>
      match getMsgId cfg n value with
      | .ok (tok, v) => messageIdsLoop cfg n v (l.push tok)
      | .error e =>
        if e.isHpe then do
          let tok ← getUnstructured cfg n value
          pure ((l.push (mkL .invalidMessageId tok.kids)).addDefect
            (invalidHeader (S "Invalid msg-id: " ++ excRepr e)))
        else throw e

/-- `parse_message_ids`, :2198-2222. -/
def parseMessageIds (cfg : Cfg) (n : Nat) (value : Str) : EPy Tok :=
  messageIdsLoop cfg n value (mkL .messageIdList)

/-! ## MIME-Version -/

/-- `parse_mime_version`, :2232-2298. -/
def parseMimeVersion (cfg : Cfg) (n : Nat) (value : Str) : EPy Tok := do
  let mv := mkL .mimeVersion
  if value.isEmpty then
    return mv.addDefect (missingValue (S "Missing MIME version number (eg: 1.0)"))
  let (mv, value) ← if headIs isCfwsLeader value then do
      let (tok, v) ← getCfws n value
      let mv := mv.push tok
      pure (if v.isEmpty then
        mv.addDefect (missingValue (S "Expected MIME version number but found only CFWS")) else mv, v)
    else pure (mv, value)
  let digits := value.takeWhile (fun c => c != 46 && !isCfwsLeader c)
  let value := value.drop digits.length
  let mv ← if !isdigitStr digits then
      pure ((mv.addDefect (invalidHeader (S "Expected MIME major version number but found "
        ++ unicodeRepr digits))).push (VT digits "xtext"))
    else do
      let k ← pyInt cfg.maxd digits
      pure ((mv.setAttr "major" (.n k)).push (VT digits "digits"))
  let (mv, value) ← optCfws n mv value
  let hasMajor := (mv.getAttr "major").isSome
  let incomplete := invalidHeader (S "Incomplete MIME version; found only major number")
  match value with
  | 46 :: value =>
    let mv := mv.push (VT [46] "version-separator")
    let (mv, value) ← optCfws n mv value
    if value.isEmpty then return (if hasMajor then mv.addDefect incomplete else mv)
    let digits := value.takeWhile (fun c => !isCfwsLeader c)
    let value := value.drop digits.length
    let mv ← if !isdigitStr digits then
        pure ((mv.addDefect (invalidHeader (S "Expected MIME minor version number but found "
          ++ unicodeRepr digits))).push (VT digits "xtext"))
      else do
        let k ← pyInt cfg.maxd digits
        pure ((mv.setAttr "minor" (.n k)).push (VT digits "digits"))
    let (mv, value) ← optCfws n mv value
    if value.isEmpty then return mv
    return (mv.addDefect (invalidHeader (S "Excess non-CFWS text after MIME version"))).push
      (VT value "xtext")
  | _ =>
    let mv := if hasMajor then mv.addDefect incomplete else mv
    return (if value.isEmpty then mv else mv.push (VT value "xtext"))

/-! ## MIME parameters -/

/-- The `while` loop of `get_invalid_parameter`, :2308-2315. -/
def invalidParameterLoop (cfg : Cfg) : Nat → Str → Tok → EPy (Tok × Str)
  | 0, _, _ => throw .fuel
  | n + 1, value, ip =>
    match value with
    | [] => pure (ip, [])
    | c :: rest =>
      if c == 59 then pure (ip, value)
      else if isPhraseEnd c then
        invalidParameterLoop cfg n rest (ip.push (VT [c] "misplaced-special"))
      else do
        let (tok, v) ← getPhrase cfg n value
        invalidParameterLoop cfg n v (ip.push tok)

/-- `get_invalid_parameter`, :2300-2316. -/
def getInvalidParameter (cfg : Cfg) (n : Nat) (value : Str) : EPy (Tok × Str) :=
  invalidParameterLoop cfg n value (mkL .invalidParameter)

/-- `get_ttext`, :2318-2335 (`_non_token_end_matcher`, :1019-1020). -/
def getTtext (value : Str) : EPy (Tok × Str) :=
  let m := value.takeWhile (fun c => !isTokenEnd c)
  if m.isEmpty then throw (.hpe (S "expected ttext but found '" ++ value ++ S "'"))
  else pure (validateXtext (VT m "ttext"), value.drop m.length)

/-- `get_token`, :2337-2358. -/
def getToken (n : Nat) (value : Str) : EPy (Tok × Str) := do
  let (t, value) ← optCfws n (mkL .token) value
  if headIs isTokenEnd value then throw (.hpe (S "expected token but found '" ++ value ++ S "'"))
  let (tok, value) ← getTtext value
  optCfws n (t.push tok) value

/-- `get_attrtext`, :2360-2377 (`_non_attribute_end_matcher`, :1021-1022). -/
def getAttrtext (value : Str) : EPy (Tok × Str) :=
  let m := value.takeWhile (fun c => !isAttributeEnd c)
  if m.isEmpty then throw (.hpe (S "expected attrtext but found " ++ unicodeRepr value))
  else pure (validateXtext (VT m "attrtext"), value.drop m.length)

/-- `get_attribute`, :2379-2400. -/
def getAttribute (n : Nat) (value : Str) : EPy (Tok × Str) := do
  let (a, value) ← optCfws n (mkL .attribute) value
  if headIs isAttributeEnd value then throw (.hpe (S "expected token but found '" ++ value ++ S "'"))
  let (tok, value) ← getAttrtext value
  optCfws n (a.push tok) value

/-- `get_extended_attrtext`, :2402-2418 (`_non_extended_attribute_end_matcher`, :1023-1024). -/
def getExtendedAttrtext (value : Str) : EPy (Tok × Str) :=
  let m := value.takeWhile (fun c => !isExtAttributeEnd c)
  if m.isEmpty then throw (.hpe (S "expected extended attrtext but found " ++ unicodeRepr value))
  else pure (validateXtext (VT m "extended-attrtext"), value.drop m.length)

/-- `get_extended_attribute`, :2420-2440. -/
def getExtendedAttribute (n : Nat) (value : Str) : EPy (Tok × Str) := do
  let (a, value) ← optCfws n (mkL .attribute) value
  if headIs isExtAttributeEnd value then
    throw (.hpe (S "expected token but found '" ++ value ++ S "'"))
  let (tok, value) ← getExtendedAttrtext value
  optCfws n (a.push tok) value

/-- `get_section`, :2442-2469. `int(digits)` can raise `ValueError`: `str.isdigit` accepts
digits such as `²` that `int` rejects, and there is the digit limit. -/
def getSection (cfg : Cfg) (value : Str) : EPy (Tok × Str) := do
  match value with
  | 42 :: value =>
    let sec := (mkL .section).push (VT [42] "section-marker")
    if !headIs isDigit value then
      throw (.hpe (S "Expected section number but found " ++ value))
    let digits := value.takeWhile isDigit
    let value := value.drop digits.length
    let sec := if digits.headD 0 == 48 && digits != [48] then
        sec.addDefect (invalidHeader (S "section number has an invalid leading 0")) else sec
    let k ← pyInt cfg.maxd digits
    pure ((sec.setAttr "number" (.n k)).push (VT digits "digits"), value)
  | _ => throw (.hpe (S "Expected section but found " ++ value))

/-- `get_value`, :2472-2492. -/
def getValue (cfg : Cfg) (n : Nat) (value : Str) : EPy (Tok × Str) := do
  if value.isEmpty then throw (.hpe (S "Expected value but found end of string"))
  let (leader, value) ← if headIs isCfwsLeader value then do
      let (l, v) ← getCfws n value
      pure (some l, v)
    else pure (none, value)
  if value.isEmpty then
    throw (.hpe (S "Expected value but found only " ++ ((leader.map Tok.str).getD (S "None"))))
  let (tok, value) ← if headIs (· == 34) value then getQuotedString cfg n value
    else getExtendedAttribute n value
  let tok := match leader with
    | some l => tok.prepend l
    | none => tok
  pure ((mkL .value).push tok, value)

/-- `Parameter.section_number`, :694-697. -/
def sectionNumber (p : Tok) : Nat :=
  if p.getAttr "sectioned" == some (.b true) then
    match (p.kids.getD 1 default).getAttr "number" with
    | some (.n k) => k
    | _ => 0
  else 0

/-- Applies `f` to the first `bare-quoted-string` element of `q`. -/
def modBqs (f : Tok → Tok) (q : Tok) : Tok :=
  let rec go : List Tok → List Tok
    | [] => []
    | k :: ks => if k.ty == "bare-quoted-string" then f k :: ks else k :: go ks
  q.setKids (go q.kids)

/-- `appendto.append(x)` of `get_parameter`: `appendto` is the parameter, or the bare quoted
string inside the quoted string that is the parameter's last element. -/
def appendTo (useBqs : Bool) (x : Tok) (p : Tok) : Tok :=
  if useBqs then p.setKids (p.kids.dropLast ++ [modBqs (·.push x) (p.kids.getLast?.getD default)])
  else p.push x

/-- The `while value:` loop that rebuilds the rest of a quoted extended value, :2617-2625. -/
def remainderLoop : Nat → Str → Tok → EPy (Tok × Str)
  | 0, _, _ => throw .fuel
  | n + 1, value, v =>
    match value with
    | [] => pure (v, [])
    | c :: rest =>
      if isWsp c then
        let (tok, value) := getFws value
        remainderLoop n value (v.push tok)
      else if c == 34 then remainderLoop n rest (v.push (VT [34] "DQUOTE"))
      else do
        let (tok, value) ← getQcontent value
        remainderLoop n value (v.push tok)

/-- `get_parameter`, :2494-2633. -/
def getParameter (cfg : Cfg) (n : Nat) (value : Str) : EPy (Tok × Str) := do
  let (tok, value) ← getAttribute n value
  let param := (mkL .parameter).push tok
  if value.isEmpty || headIs (· == 59) value then
    return (param.addDefect (invalidHeader
      (S "Parameter contains name (" ++ tok.str ++ S ") but no value")), value)
  let (param, value) ← if headIs (· == 42) value then do
      let (param, value) ← match getSection cfg value with
        | .ok (sec, v) => pure ((param.setAttr "sectioned" (.b true)).push sec, v)
        | .error e => if e.isHpe then pure (param, value) else throw e
      if value.isEmpty then throw (.hpe (S "Incomplete parameter"))
      match value with
      | 42 :: v =>
        pure ((param.push (VT [42] "extended-parameter-marker")).setAttr "extended" (.b true), v)
      | _ => pure (param, value)
    else pure (param, value)
  let c ← match value with
    | c :: _ => pure c
    | [] => throw strIndexError
  if c != 61 then throw (.hpe (S "Parameter not followed by '='"))
  let (param, value) ← optCfws n (param.push (VT [61] "parameter-separator")) (value.drop 1)
  let extended := param.getAttr "extended" == some (.b true)
  let (param, value, remainder, useBqs) ←
    if extended && headIs (· == 34) value then do
      let (qstring, rem) ← getQuotedString cfg n value
      let inner := match qstring.kids.find? (·.ty == "bare-quoted-string") with
        | some b => strs b.kids
        | none => []
      let semi ← if sectionNumber param == 0 then
          if headIs (· == 39) inner then pure true
          else do
            let (_, rest) ← getAttrtext inner
            pure (headIs (· == 39) rest)
        else match getExtendedAttrtext inner with
          | .ok (_, rest) => pure rest.isEmpty
          | .error _ => pure false
      if semi then
        let param := (param.addDefect (invalidHeader
          (S "Quoted string value for extended parameter is invalid"))).push qstring
        let hasB := qstring.kids.any (·.ty == "bare-quoted-string")
        let param := if hasB then
            param.setKids (param.kids.dropLast ++ [modBqs (·.setKids []) qstring]) else param
        pure (param, inner, some rem, hasB)
      else
        pure (param.addDefect (invalidHeader (S "Parameter marked as extended but appears to have a quoted string value that is non-encoded")),
          value, none, false)
    else pure (param, value, none, false)
  let (tok, value) ← if headIs (· == 39) value then pure (none, value)
    else do
      let (t, v) ← getValue cfg n value
      pure (some t, v)
  let addTok (p : Tok) : Tok := match tok with
    | some t => appendTo useBqs t p
    | none => p
  let finish (p : Tok) (v : Str) : EPy (Tok × Str) :=
    match remainder with
    | some r => if v.isEmpty then pure (p, r) else throw (.assertionError v)
    | none => pure (p, v)
  let notInitial := !extended || decide (sectionNumber param > 0)
  if notInitial && (value.isEmpty || !headIs (· == 39) value) then
    return (← finish (addTok param) value)
  let param := if notInitial then param.addDefect (invalidHeader (S "Apparent initial-extended-value but attribute was not marked as extended or was not initial section")) else param
  let (param, value, done) ←
    if value.isEmpty then do
      let param := addTok (param.addDefect (invalidHeader (S "Missing required charset/lang delimiters")))
      pure (param, value, remainder.isNone)
    else do
      let param ← match tok with
        | some t =>
          match t.kids.find? (·.ty == "extended-attrtext") with
          | some x => do
            let cs ← x.value
            pure ((appendTo useBqs x param).setAttr "charset" (.s cs))
          | none =>
            match t.kids.getLast? with
            | some x => do
              let cs ← x.value
              pure ((appendTo useBqs x param).setAttr "charset" (.s cs))
            | none => throw (.unboundLocal "cannot access local variable 't' where it is not associated with a value")
        | none => pure param
      if !headIs (· == 39) value then
        throw (.hpe (S "Expected RFC2231 char/lang encoding delimiter, but found " ++ unicodeRepr value))
      let param := appendTo useBqs (VT [39] "RFC2231-delimiter") param
      let value := value.drop 1
      let (param, value) ← if headIs (· != 39) value then do
          let (t, v) ← getAttrtext value
          let lang ← t.value
          let param := (appendTo useBqs t param).setAttr "lang" (.s lang)
          if !headIs (· == 39) v then
            throw (.hpe (S "Expected RFC2231 char/lang encoding delimiter, but found " ++ v))
          pure (param, v)
        else pure (param, value)
      pure (appendTo useBqs (VT [39] "RFC2231-delimiter") param, value.drop 1, false)
  if done then return (param, value)
  let (tok, value) ← match remainder with
    | some _ => remainderLoop n value (mkL .value)
    | none => getValue cfg n value
  finish (appendTo useBqs tok param) value

end PyLean.TextLibs.Email
