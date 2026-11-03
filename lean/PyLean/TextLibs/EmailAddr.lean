import PyLean.TextLibs.EmailLex

/-!
`Lib/email/_header_value_parser.py`, CPython 3.15.2: the address parsers, :1702-2084
(`get_obs_route` through `get_address_list`). Conventions as in `EmailLex.lean`.
-/

namespace PyLean.TextLibs.Email

open PyLean.UnicodeObj

/-- The first `while` loop of `get_obs_route`, :1710-1716. -/
def obsRouteLoop1 : Nat → Str → Tok → EPy (Tok × Str)
  | 0, _, _ => throw .fuel
  | n + 1, value, o =>
    match value with
    | [] => pure (o, [])
    | c :: rest =>
      if isCfwsLeader c then do
        let (t, v) ← getCfws n value
        obsRouteLoop1 n v (o.push t)
      else if c == 44 then obsRouteLoop1 n rest (o.push ListSeparator)
      else pure (o, value)

/-- The second `while` loop of `get_obs_route`, :1723-1736. -/
def obsRouteLoop2 (cfg : Cfg) : Nat → Str → Tok → EPy (Tok × Str)
  | 0, _, _ => throw .fuel
  | n + 1, value, o =>
    match value with
    | 44 :: v => do
      let o := o.push ListSeparator
      if v.isEmpty then return (o, v)
      let (o, v) ← optCfws n o v
      if v.isEmpty then return (o, v)
      match v with
      | 64 :: v' =>
        let (tok, v'') ← getDomain cfg n v'
        obsRouteLoop2 cfg n v'' ((o.push RouteComponentMarker).push tok)
      | _ => obsRouteLoop2 cfg n v o
    | _ => pure (o, value)

/-- `get_obs_route`, :1702-1743. -/
def getObsRoute (cfg : Cfg) (n : Nat) (value : Str) : EPy (Tok × Str) := do
  let (o, value) ← obsRouteLoop1 n value (mkL .obsRoute)
  match value with
  | 64 :: v =>
    let (tok, v) ← getDomain cfg n v
    let (o, v) ← obsRouteLoop2 cfg n v ((o.push RouteComponentMarker).push tok)
    match v with
    | [] => throw (.hpe (S "end of header while parsing obs-route"))
    | 58 :: v' => pure (o.push (VT [58] "end-of-obs-route-marker"), v')
    | _ => throw (.hpe (S "expected ':' marking end of obs-route but found '" ++ v ++ S "'"))
  | _ => throw (.hpe (S "expected obs-route domain but found '" ++ value ++ S "'"))

/-- `get_angle_addr`, :1745-1789. -/
def getAngleAddr (cfg : Cfg) (n : Nat) (value : Str) : EPy (Tok × Str) := do
  let (a, value) ← optCfws n (mkL .angleAddr) value
  match value with
  | 60 :: value =>
    let a := a.push (VT [60] "angle-addr-start")
    match value with
    | 62 :: v =>
      return ((a.push (VT [62] "angle-addr-end")).addDefect
        (invalidHeader (S "null addr-spec in angle-addr")), v)
    | _ =>
    let (a, tok, value) ←
      match getAddrSpec cfg n value with
      | .ok (tok, v) => pure (a, tok, v)
      | .error e =>
        if !e.isHpe then throw e
        else
          match getObsRoute cfg n value with
          | .ok (route, v) => do
            let a := (a.addDefect (obsoleteHeader (S "obsolete route specification in angle-addr"))).push route
            let (tok, v) ← getAddrSpec cfg n v
            pure (a, tok, v)
          | .error e2 =>
            if e2.isHpe then
              throw (.hpe (S "expected addr-spec or obs-route but found '" ++ value ++ S "'"))
            else throw e2
    let a := a.push tok
    let (a, value) := match value with
      | 62 :: v => (a, v)
      | _ => (a.addDefect (invalidHeader (S "missing trailing '>' on angle-addr")), value)
    optCfws n (a.push (VT [62] "angle-addr-end")) value
  | _ => throw (.hpe (S "expected angle-addr but found '" ++ value ++ S "'"))

/-- `get_display_name`, :1791-1803: the phrase's elements and a copy of its defects. -/
def getDisplayName (cfg : Cfg) (n : Nat) (value : Str) : EPy (Tok × Str) := do
  let (tok, value) ← getPhrase cfg n value
  pure (.node .displayName "display-name" tok.kids tok.ds [], value)

/-- `get_name_addr`, :1806-1840. -/
def getNameAddr (cfg : Cfg) (n : Nat) (value : Str) : EPy (Tok × Str) := do
  if value.isEmpty then throw (.hpe (S "expected name-addr but found '" ++ value ++ S "'"))
  let (leader, value) ← if headIs isCfwsLeader value then do
      let (l, v) ← getCfws n value
      if v.isEmpty then throw (.hpe (S "expected name-addr but found '" ++ l.str ++ S "'"))
      pure (some l, v)
    else pure (none, value)
  let (na, leader, value) ← (match value with
    | c :: _ =>
      if c != 60 then do
        if isPhraseEnd c then throw (.hpe (S "expected name-addr but found '" ++ value ++ S "'"))
        let (tok, value) ← getDisplayName cfg n value
        if value.isEmpty then throw (.hpe (S "expected name-addr but found '" ++ tok.str ++ S "'"))
        let tok ← match leader with
          | some l =>
            match tok.kids with
            | k0 :: rest => pure (if k0.isList then tok.setKids (k0.prepend l :: rest) else tok.prepend l)
            | [] => throw listIndexError
          | none => pure tok
        pure ((mkL .nameAddr).push tok, none, value)
      else pure (mkL .nameAddr, leader, value)
    | [] => pure (mkL .nameAddr, leader, value) : EPy (Tok × Option Tok × Str))
  let (tok, value) ← getAngleAddr cfg n value
  let tok := match leader with
    | some l => tok.prepend l
    | none => tok
  pure (na.push tok, value)

/-- `get_mailbox`, :1842-1861. -/
def getMailbox (cfg : Cfg) (n : Nat) (value : Str) : EPy (Tok × Str) := do
  let (tok, value) ←
    match getNameAddr cfg n value with
    | .ok r => pure r
    | .error e =>
      if !e.isHpe then throw e
      else match getAddrSpec cfg n value with
        | .ok r => pure r
        | .error e2 =>
          if e2.isHpe then throw (.hpe (S "expected mailbox but found '" ++ value ++ S "'"))
          else throw e2
  let mb := mkL .mailbox
  let mb := if tok.allDefects.any (·.cls == "InvalidHeaderDefect") then mb.setTy "invalid-mailbox" else mb
  pure (mb.push tok, value)

/-- The `while` loop of `get_invalid_mailbox`, :1871-1878. -/
def invalidMailboxLoop (cfg : Cfg) (endc : Nat → Bool) : Nat → Str → Tok → EPy (Tok × Str)
  | 0, _, _ => throw .fuel
  | n + 1, value, im =>
    match value with
    | [] => pure (im, [])
    | c :: rest =>
      if endc c then pure (im, value)
      else if isPhraseEnd c then invalidMailboxLoop cfg endc n rest (im.push (VT [c] "misplaced-special"))
      else do
        let (tok, v) ← getPhrase cfg n value
        invalidMailboxLoop cfg endc n v (im.push tok)

/-- `get_invalid_mailbox`, :1863-1879. -/
def getInvalidMailbox (cfg : Cfg) (n : Nat) (value : Str) (endc : Nat → Bool) : EPy (Tok × Str) :=
  invalidMailboxLoop cfg endc n value (mkL .invalidMailbox)

def commaSemi (c : Nat) : Bool := c == 44 || c == 59
def isComma (c : Nat) : Bool := c == 44

/-- The `while` loop of `get_mailbox_list`, :1894-1934. -/
def mailboxListLoop (cfg : Cfg) : Nat → Str → Tok → EPy (Tok × Str)
  | 0, _, _ => throw .fuel
  | n + 1, value, ml =>
    match value with
    | [] => pure (ml, [])
    | c :: _ =>
      if c == 59 then pure (ml, value)
      else do
        let invalidMb := invalidHeader (S "invalid mailbox in mailbox-list")
        let (ml, value) ←
          match getMailbox cfg n value with
          | .ok (tok, v) => pure (ml.push tok, v)
          | .error e =>
            if !e.isHpe then throw e
            else if isCfwsLeader c then do
              let (leader, v) ← getCfws n value
              if v.isEmpty || headIs commaSemi v then
                pure ((ml.push leader).addDefect (obsoleteHeader (S "empty element in mailbox-list")), v)
              else do
                let (tok, v') ← getInvalidMailbox cfg n v commaSemi
                pure ((ml.push (tok.prepend leader)).addDefect invalidMb, v')
            else if c == 44 then
              pure (ml.addDefect (obsoleteHeader (S "empty element in mailbox-list")), value)
            else do
              let (tok, v') ← getInvalidMailbox cfg n value commaSemi
              pure ((ml.push tok).addDefect invalidMb, v')
        let (ml, value) ←
          if headIs (fun c => !commaSemi c) value then
            match ml.kids.getLast? with
            | none => throw listIndexError
            | some mb => do
              let (tok, v) ← getInvalidMailbox cfg n value commaSemi
              let mb' := (mb.setTy "invalid-mailbox").pushAll tok.kids
              pure ((ml.setKids (ml.kids.dropLast ++ [mb'])).addDefect invalidMb, v)
          else pure (ml, value)
        match value with
        | 44 :: v => mailboxListLoop cfg n v (ml.push ListSeparator)
        | _ => mailboxListLoop cfg n value ml

/-- `get_mailbox_list`, :1881-1935. -/
def getMailboxList (cfg : Cfg) (n : Nat) (value : Str) : EPy (Tok × Str) :=
  mailboxListLoop cfg n value (mkL .mailboxList)

/-- `MailboxList.all_mailboxes`, :363-366. -/
def mailboxListAll (ml : Tok) : List Tok :=
  ml.kids.filter (fun x => x.ty == "mailbox" || x.ty == "invalid-mailbox")

/-- `get_group_list`, :1938-1973. -/
def getGroupList (cfg : Cfg) (n : Nat) (value : Str) : EPy (Tok × Str) := do
  let gl := mkL .groupList
  if value.isEmpty then
    return (gl.addDefect (invalidHeader (S "end of header before group-list")), value)
  let (leader, value) ← if headIs isCfwsLeader value then do
      let (l, v) ← getCfws n value
      pure (some l, v)
    else pure (none, value)
  match leader with
  | some l =>
    if value.isEmpty then
      return ((gl.addDefect (invalidHeader (S "end of header in group-list"))).push l, value)
    if headIs (· == 59) value then return (gl.push l, value)
  | none => pure ()
  let (tok, value) ← getMailboxList cfg n value
  if (mailboxListAll tok).isEmpty then
    let gl := match leader with
      | some l => gl.push l
      | none => gl
    return ((gl.pushAll tok.kids).addDefect (obsoleteHeader (S "group-list with empty entries")), value)
  let tok := match leader with
    | some l => tok.prepend l
    | none => tok
  pure (gl.push tok, value)

/-- `get_group`, :1975-2003. -/
def getGroup (cfg : Cfg) (n : Nat) (value : Str) : EPy (Tok × Str) := do
  let (tok, value) ← getDisplayName cfg n value
  match value with
  | 58 :: value =>
    let g := ((mkL .group).push tok).push (VT [58] "group-display-name-terminator")
    match value with
    | 59 :: v => return (g.push (VT [59] "group-terminator"), v)
    | _ =>
    let (tok, value) ← getGroupList cfg n value
    let g := g.push tok
    let g ← match value with
      | [] => pure (g.addDefect (invalidHeader (S "end of header in group")))
      | c :: _ =>
        if c != 59 then throw (.hpe (S "expected ';' at end of group but found " ++ value))
        else pure g
    optCfws n (g.push (VT [59] "group-terminator")) (value.drop 1)
  | _ => throw (.hpe (S "expected ':' at end of group display name but found '" ++ value ++ S "'"))

/-- `get_address`, :2005-2032. -/
def getAddress (cfg : Cfg) (n : Nat) (value : Str) : EPy (Tok × Str) := do
  let (tok, value) ←
    match getGroup cfg n value with
    | .ok r => pure r
    | .error e =>
      if !e.isHpe then throw e
      else match getMailbox cfg n value with
        | .ok r => pure r
        | .error e2 =>
          if e2.isHpe then throw (.hpe (S "expected address but found '" ++ value ++ S "'"))
          else throw e2
  pure ((mkL .address).push tok, value)

/-- The `while value:` loop of `get_address_list`, :2045-2083. -/
def addressListLoop (cfg : Cfg) : Nat → Str → Tok → EPy (Tok × Str)
  | 0, _, _ => throw .fuel
  | n + 1, value, al =>
    match value with
    | [] => pure (al, [])
    | c :: _ => do
      let invalidAddr := invalidHeader (S "invalid address in address-list")
      let (al, value) ←
        match getAddress cfg n value with
        | .ok (tok, v) => pure (al.push tok, v)
        | .error e =>
          if !e.isHpe then throw e
          else if isCfwsLeader c then do
            let (leader, v) ← getCfws n value
            if v.isEmpty || headIs isComma v then
              pure ((al.push leader).addDefect
                (obsoleteHeader (S "address-list entry with no content")), v)
            else do
              let (tok, v') ← getInvalidMailbox cfg n v isComma
              pure ((al.push (mkL .address [tok.prepend leader])).addDefect invalidAddr, v')
          else if c == 44 then
            pure (al.addDefect (obsoleteHeader (S "empty element in address-list")), value)
          else do
            let (tok, v') ← getInvalidMailbox cfg n value isComma
            pure ((al.push (mkL .address [tok])).addDefect invalidAddr, v')
      let (al, value) ←
        if headIs (fun c => !isComma c) value then do
          let (tok, v) ← getInvalidMailbox cfg n value isComma
          pure ((al.push (mkL .address [tok])).addDefect invalidAddr, v)
        else pure (al, value)
      match value with
      | [] => addressListLoop cfg n [] al
      | _ :: v => addressListLoop cfg n v (al.push ListSeparator)

/-- `get_address_list`, :2034-2084. -/
def getAddressList (cfg : Cfg) (n : Nat) (value : Str) : EPy (Tok × Str) :=
  addressListLoop cfg n value (mkL .addressList)

end PyLean.TextLibs.Email
