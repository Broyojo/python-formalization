import PyLean.TextLibs.EmailBase

/-!
`Lib/email/_header_value_parser.py`, CPython 3.15.2: the lexical parsers, :1015-1700
(`_validate_xtext` through `get_addr_spec`).

Library calls are parameters (`Cfg`):
* `_ew.decode` (Lib/email/_encoded_words.py) is `Cfg.dec`, a function of its argument: it
  returns `(text, charset, lang, defects)`, raises an exception `get_encoded_word` catches
  (`ValueError` or `KeyError`, subclasses included: `.caught`), or raises another one.
* `sys.get_int_max_str_digits()` is `Cfg.maxd`.

Every `while` loop but the one of `get_encoded_word` (see there) and the recursion of
`get_comment` run on fuel `n`; `EExc.fuel` is never a
Python outcome. Each function's fuel is passed unchanged to the functions it calls, and a loop
spends one unit per iteration.
-/

namespace PyLean.TextLibs.Email

open PyLean.UnicodeObj

/-- Outcome of `_ew.decode(s)`. -/
inductive DecOut where
  | ok (text charset lang : Str) (ds : List Defect)
  /-- Raised `ValueError` or `KeyError`. -/
  | caught
  /-- Raised another exception. -/
  | raise (cls : String) (msg : Str)
  deriving Repr, DecidableEq, Inhabited

structure Cfg where
  dec : Str → DecOut
  maxd : Nat := 4300

/-- `_wsp_splitter(value, 1)`, :1015, as `fragment, ''.join(remainder)`: the text before the
first run of `[ \t]` and the rest (the run included). -/
def wspSplit (v : Str) : Str × Str := (v.takeWhile (fun c => !isWsp c), v.dropWhile (fun c => !isWsp c))

/-- `str.partition('=?')` as `before, ''.join([sep, after])`. -/
def partitionEq (v : Str) : Str × Str :=
  match split1 v (S "=?") with
  | (b, some a) => (b, S "=?" ++ a)
  | (b, none) => (b, [])

/-! ## `rfc2047_matcher`, :117-125 -/

/-- `.*?\?=` from here: a `?=` before any newline (`.` does not match `\n`). -/
def qeBeforeNl : Str → Bool
  | 63 :: 61 :: _ => true
  | 10 :: _ => false
  | _ :: t => qeBeforeNl t
  | [] => false

/-- The pattern anchored at the start of `s`: `=\?`, then `[^?]*\?` (which can only stop at the
first `?`), `[qQbB]`, `\?`, then `.*?\?=`. -/
def rfcMatchAt (s : Str) : Bool :=
  match s with
  | 61 :: 63 :: r =>
    match r.dropWhile (· != 63) with
    | 63 :: c :: 63 :: r' => mem "qQbB" c && qeBeforeNl r'
    | _ => false
  | _ => false

/-- `rfc2047_matcher.search(s)` is not `None`. -/
def rfcSearch : Str → Bool
  | [] => false
  | s@(_ :: t) => rfcMatchAt s || rfcSearch t

/-! ## Terminals -/

/-- `_non_printable_finder`, :1018: the characters in `[\x00-\x20\x7F]`. -/
def nonPrintables (s : Str) : Str := s.filter (fun c => c ≤ 32 || c == 127)

/-- `utils._has_surrogates(s)` (Lib/email/utils.py:47-56): `s.encode()` fails, which for
UTF-8 means `s` holds a surrogate code point. -/
def hasSurrogates (s : Str) : Bool := s.any (fun c => 0xD800 ≤ c && c ≤ 0xDFFF)

/-- `str(NonPrintableDefect(cs))`, Lib/email/errors.py:97-106: the list's repr. -/
def nonPrintableDefect (cs : Str) : Defect :=
  let items := cs.map (fun c => unicodeRepr [c])
  let body := match items with
    | [] => []
    | i :: is => is.foldl (fun acc x => acc ++ S ", " ++ x) i
  ⟨"NonPrintableDefect", S "the following ASCII non-printables found in header: [" ++ body ++ S "]"⟩

/-- `_validate_xtext`, :1026-1034, on a fresh terminal. -/
def validateXtext : Tok → Tok
  | .term c s ty ds =>
    let ds1 := if (nonPrintables s).isEmpty then ds else ds ++ [nonPrintableDefect (nonPrintables s)]
    let ds2 := if hasSurrogates s then
      ds1 ++ [⟨"UndecodableBytesDefect", S "Non-ASCII characters found in header token"⟩] else ds1
    .term c s ty ds2
  | t => t

/-- The `for ... else` loop of `_get_ptext_to_endchars`, :1051-1065, over the fragment: the
characters kept, the fragment from the `break` on (`none` when the loop ran to the end), and
`had_qp`. -/
def ptextLoop (endc : Nat → Bool) : Str → Bool → Bool → Str → Str × Option Str × Bool
  | [], _, qp, acc => (acc, none, qp)
  | c :: cs, esc, qp, acc =>
    if c == 92 then
      if esc then
        if endc c then (acc, some (c :: cs), true) else ptextLoop endc cs false true (acc ++ [c])
      else ptextLoop endc cs true qp acc
    else if esc then ptextLoop endc cs false qp (acc ++ [c])
    else if endc c then (acc, some (c :: cs), qp)
    else ptextLoop endc cs false qp (acc ++ [c])

def unboundPos : EExc :=
  .unboundLocal "cannot access local variable 'pos' where it is not associated with a value"

/-- `_get_ptext_to_endchars`, :1036-1066. On a value that starts with a space or tab the
fragment is empty, the `for` body never runs, and the `else` clause reads the unbound `pos`. -/
def getPtextToEndchars (v : Str) (endc : Nat → Bool) : EPy (Str × Str × Bool) :=
  if v.isEmpty then pure ([], [], false)
  else
    let (frag, rem) := wspSplit v
    if frag.isEmpty then throw unboundPos
    else
      let (vc, brk, qp) := ptextLoop endc frag false false []
      pure (vc, brk.getD [] ++ rem, qp)

/-- `get_fws`, :1068-1078. -/
def getFws (v : Str) : Tok × Str :=
  let nv := lstrip v
  (WT (v.take (v.length - nv.length)) "fws", nv)

/-! ## Encoded words and unstructured text -/

/-- The `while text:` loop of `get_encoded_word`, :1113-1122. -/
def ewTextLoop (termTy : String) : Nat → Str → List Tok → EPy (List Tok)
  | 0, _, _ => throw .fuel
  | n + 1, text, acc =>
    match text with
    | [] => pure acc
    | c :: _ =>
      if isWsp c then ewTextLoop termTy n (getFws text).2 (acc ++ [(getFws text).1])
      else
        ewTextLoop termTy n (wspSplit text).2 (acc ++ [validateXtext (VT (wspSplit text).1 termTy)])

/-- The second split of `get_encoded_word`, :1093-1099: when the `?=` that ended the token is
followed by two hex digits and the token has fewer than two `?`, that `?=` was the start of a
`=XX` escape, and the token runs to the next `?=`. The token and the rest of the value. -/
def ewHexFix (tok0 remstr : Str) : Str × Str :=
  if decide (remstr.length > 1) && isHexDigit (remstr.getD 0 0) && isHexDigit (remstr.getD 1 0)
      && decide (tok0.count 63 < 2) then
    ((tok0 ++ S "?=" ++ (split1 remstr (S "?=")).1), ((split1 remstr (S "?=")).2.getD []))
  else (tok0, remstr)

/-- The token tree of `get_encoded_word` once `_ew.decode` returned, :1110-1127. -/
def ewBuild (termTy : String) (value tok rest text charset lang : Str) (dds : List Defect) :
    EPy (Tok × Str) := do
  let ds0 := if twoWords tok then [invalidHeader (S "whitespace inside encoded word")] else []
  let ks ← ewTextLoop termTy (text.length + 1) text []
  let ds := ds0 ++ dds ++
    (if headIs (fun c => !isWsp c) rest then
      [invalidHeader (S "missing trailing whitespace after encoded-word")] else [])
  pure (.node .encodedWord "encoded-word" ks ds
    [("cte", .s value), ("charset", .s charset), ("lang", .s lang)], rest)

/-- `get_encoded_word`, :1080-1127. `tok == value[2:]` (:1089) holds exactly when there is no
`?=` after the `=?`. The `while text:` loop gets its own fuel, `len(text) + 1`: each iteration
drops at least one character. -/
def getEncodedWord (cfg : Cfg) (value : Str) (termTy : String) : EPy (Tok × Str) :=
  let found := S "expected encoded word but found " ++ value
  if !startsWith value (S "=?") then throw (.hpe found)
  else
    let v2 := value.drop 2
    let tok0 := (split1 v2 (S "?=")).1
    if tok0 == v2 then throw (.hpe found)
    else
      let tr := ewHexFix tok0 ((split1 v2 (S "?=")).2.getD [])
      match cfg.dec (S "=?" ++ tr.1 ++ S "?=") with
      | .caught => throw (.invalidEw (S "encoded word format invalid: '" ++ value ++ S "'"))
      | .raise c m => throw (.decRaise c m)
      | .ok text charset lang dds => ewBuild termTy value tr.1 tr.2 text charset lang dds

/-- `EWWhiteSpaceTerminal(x, 'fws')`: its text is `str(x)`. -/
def ewws (x : Tok) : Tok := .term .ewws x.str "fws" []

/-- The `try` of `get_unstructured`, :1158-1167: the encoded word and the rest when one parsed,
and `valid_ew`. -/
def ewAttempt (cfg : Cfg) (value : Str) : EPy (Option (Tok × Str) × Bool) :=
  if startsWith value (S "=?") then
    match getEncodedWord cfg value "utext" with
    | .ok r => pure (some r, true)
    | .error (.invalidEw _) => pure (none, false)
    | .error (.hpe _) => pure (none, true)
    | .error e => throw e
  else pure (none, true)

/-- Appending a parsed encoded word in `get_unstructured`, :1169-1179. -/
def ewAppend (u tok : Tok) : Tok :=
  let ks := u.kids
  let (u1, haveWs) :=
    match ks.getLast? with
    | some l => if l.ty != "fws" then
        (u.addDefect (invalidHeader (S "missing whitespace before encoded word")), false)
        else (u, true)
    | none => (u, true)
  let u2 :=
    if haveWs && decide (ks.length > 1) && (ks.getD (ks.length - 2) default).ty == "encoded-word"
    then u1.setKids (ks.dropLast ++ [ewws (ks.getLast?.getD default)]) else u1
  u2.push tok

/-- The next word of `get_unstructured`, :1181-1189: up to the next space or tab, or up to the
first `=?` when the word holds an RFC 2047 encoded word and `valid_ew`. -/
def wordSplit (validEw : Bool) (value : Str) : Str × Str :=
  if validEw && rfcSearch (wspSplit value).1 then partitionEq value else wspSplit value

/-- The `while value:` loop of `get_unstructured`, :1153-1193. -/
def unstructLoop (cfg : Cfg) : Nat → Str → Tok → EPy Tok
  | 0, _, _ => throw .fuel
  | n + 1, value, u =>
    match value with
    | [] => pure u
    | c :: _ =>
      if isWsp c then unstructLoop cfg n (getFws value).2 (u.push (getFws value).1)
      else
        match ewAttempt cfg value with
        | .error e => throw e
        | .ok (some (tok, v'), _) => unstructLoop cfg n v' (ewAppend u tok)
        | .ok (none, validEw) =>
          unstructLoop cfg n (wordSplit validEw value).2
            (u.push (validateXtext (VT (wordSplit validEw value).1 "utext")))

/-- `get_unstructured`, :1129-1194. -/
def getUnstructured (cfg : Cfg) (n : Nat) (value : Str) : EPy Tok :=
  unstructLoop cfg n value (mkL .unstructured)

/-! ## Quoted strings, comments, CFWS -/

/-- `get_qp_ctext`, :1196-1211. -/
def getQpCtext (value : Str) : EPy (Tok × Str) := do
  let (ptext, v, _) ← getPtextToEndchars value (fun c => c == 40 || c == 41)
  pure (validateXtext (WT ptext "ptext"), v)

/-- `get_qcontent`, :1213-1226. -/
def getQcontent (value : Str) : EPy (Tok × Str) := do
  let (ptext, v, _) ← getPtextToEndchars value (fun c => c == 34)
  pure (validateXtext (VT ptext "ptext"), v)

/-- `get_atext`, :1228-1242 (`_non_atom_end_matcher`, :1016-1017). -/
def getAtext (value : Str) : EPy (Tok × Str) :=
  let m := value.takeWhile (fun c => !isAtomEnd c)
  if m.isEmpty then throw (.hpe (S "expected atext but found '" ++ value ++ S "'"))
  else pure (validateXtext (VT m "atext"), value.drop m.length)

/-- The `while` loop of `get_bare_quoted_string`, :1258-1279. -/
def bqsLoop (cfg : Cfg) : Nat → Str → Tok → EPy (Tok × Str)
  | 0, _, _ => throw .fuel
  | n + 1, value, b =>
    match value with
    | [] => pure (b, [])
    | c :: _ =>
      if c == 34 then pure (b, value)
      else if isWsp c then
        let (tok, v') := getFws value
        bqsLoop cfg n v' (b.push tok)
      else if value.take 2 == S "=?" then do
        let (tok, v', b1, valid) ← (match getEncodedWord cfg value "vtext" with
          | .ok (tok, v') =>
            pure (tok, v', b.addDefect (invalidHeader (S "encoded word inside quoted string")), true)
          | .error e =>
            if e.isHpe then do
              let (tok, v') ← getQcontent value
              pure (tok, v', b, false)
            else throw e : EPy (Tok × Str × Tok × Bool))
        let ks := b1.kids
        let b2 :=
          if valid && decide (ks.length > 1) && (ks.getLast?.getD default).ty == "fws"
              && (ks.getD (ks.length - 2) default).ty == "encoded-word"
          then b1.setKids (ks.dropLast ++ [ewws (ks.getLast?.getD default)]) else b1
        bqsLoop cfg n v' (b2.push tok)
      else do
        let (tok, v') ← getQcontent value
        bqsLoop cfg n v' (b.push tok)

/-- `get_bare_quoted_string`, :1244-1284. -/
def getBareQuotedString (cfg : Cfg) (n : Nat) (value : Str) : EPy (Tok × Str) := do
  match value with
  | 34 :: v =>
    match v with
    | 34 :: v' => pure (mkL .bareQuotedString, v')
    | _ =>
      let (b, v') ← bqsLoop cfg n v (mkL .bareQuotedString)
      match v' with
      | [] => pure (b.addDefect (invalidHeader (S "end of header inside quoted string")), [])
      | _ :: v'' => pure (b, v'')
  | _ => throw (.hpe (S "expected '\"' but found '" ++ value ++ S "'"))

mutual
/-- `get_comment`, :1286-1309. -/
def getComment : Nat → Str → EPy (Tok × Str)
  | 0, _ => throw .fuel
  | n + 1, value =>
    if headIs (· != 40) value then throw (.hpe (S "expected '(' but found '" ++ value ++ S "'"))
    else do
      let (c, v) ← commentLoop n (value.drop 1) (mkL .comment)
      match v with
      | [] => pure (c.addDefect (invalidHeader (S "end of header inside comment")), [])
      | _ :: v' => pure (c, v')
/-- The `while` loop of `get_comment`, :1297-1304. -/
def commentLoop : Nat → Str → Tok → EPy (Tok × Str)
  | 0, _, _ => throw .fuel
  | n + 1, value, c =>
    match value with
    | [] => pure (c, [])
    | ch :: _ =>
      if ch == 41 then pure (c, value)
      else if isWsp ch then
        let (t, v) := getFws value
        commentLoop n v (c.push t)
      else if ch == 40 then do
        let (t, v) ← getComment n value
        commentLoop n v (c.push t)
      else do
        let (t, v) ← getQpCtext value
        commentLoop n v (c.push t)
end

/-- The `while` loop of `get_cfws`, :1316-1321. -/
def cfwsLoop : Nat → Str → Tok → EPy (Tok × Str)
  | 0, _, _ => throw .fuel
  | n + 1, value, t =>
    match value with
    | [] => pure (t, [])
    | c :: _ =>
      if isCfwsLeader c then
        if isWsp c then
          let (tok, v) := getFws value
          cfwsLoop n v (t.push tok)
        else do
          let (tok, v) ← getComment n value
          cfwsLoop n v (t.push tok)
      else pure (t, value)

/-- `get_cfws`, :1311-1322. -/
def getCfws (n : Nat) (value : Str) : EPy (Tok × Str) := cfwsLoop n value (mkL .cfws)

/-- `if value and value[0] in CFWS_LEADER: token, value = get_cfws(value); x.append(token)`. -/
def optCfws (n : Nat) (x : Tok) (value : Str) : EPy (Tok × Str) :=
  if headIs isCfwsLeader value then do
    let (tok, v) ← getCfws n value
    pure (x.push tok, v)
  else pure (x, value)

/-- `get_quoted_string`, :1324-1340. -/
def getQuotedString (cfg : Cfg) (n : Nat) (value : Str) : EPy (Tok × Str) := do
  let (q, value) ← optCfws n (mkL .quotedString) value
  let (tok, value) ← getBareQuotedString cfg n value
  optCfws n (q.push tok) value

/-! ## Atoms, words, phrases -/

/-- `get_atom`, :1342-1367. -/
def getAtom (cfg : Cfg) (n : Nat) (value : Str) : EPy (Tok × Str) := do
  let (a, value) ← optCfws n (mkL .atom) value
  if headIs isAtomEnd value then throw (.hpe (S "expected atom but found '" ++ value ++ S "'"))
  let (tok, value) ←
    if startsWith value (S "=?") then
      match getEncodedWord cfg value "vtext" with
      | .ok r => pure r
      | .error e => if e.isHpe then getAtext value else throw e
    else getAtext value
  optCfws n (a.push tok) value

/-- The `while` loop of `get_dot_atom_text`, :1377-1382. -/
def dotAtomTextLoop : Nat → Str → Tok → EPy (Tok × Str)
  | 0, _, _ => throw .fuel
  | n + 1, value, d =>
    if headIs (fun c => !isAtomEnd c) value then do
      let (tok, value) ← getAtext value
      match value with
      | 46 :: v => dotAtomTextLoop n v ((d.push tok).push DOT)
      | _ => dotAtomTextLoop n value (d.push tok)
    else pure (d, value)

/-- `get_dot_atom_text`, :1369-1386. The final check `dot_atom_text[-1] is DOT` holds exactly
when the last element is a `dot` terminal, since only `DOT` has that type here. -/
def getDotAtomText (n : Nat) (value : Str) : EPy (Tok × Str) := do
  if value.isEmpty || headIs isAtomEnd value then
    throw (.hpe (S "expected atom at a start of dot-atom-text but found '" ++ value ++ S "'"))
  let (d, value) ← dotAtomTextLoop n value (mkL .dotAtomText)
  match d.kids.getLast? with
  | some l =>
    if l.ty == "dot" then
      throw (.hpe (S "expected atom at end of dot-atom-text but found '" ++ [46] ++ value ++ S "'"))
    else pure (d, value)
  | none => throw listIndexError

/-- `get_dot_atom`, :1388-1411. -/
def getDotAtom (cfg : Cfg) (n : Nat) (value : Str) : EPy (Tok × Str) := do
  let c ← match value with
    | c :: _ => pure c
    | [] => throw strIndexError
  let (d, value) ← if isCfwsLeader c then optCfws n (mkL .dotAtom) value else pure (mkL .dotAtom, value)
  let (tok, value) ←
    if startsWith value (S "=?") then
      match getEncodedWord cfg value "vtext" with
      | .ok r => pure r
      | .error e => if e.isHpe then getDotAtomText n value else throw e
    else getDotAtomText n value
  optCfws n (d.push tok) value

/-- `get_word`, :1413-1445. -/
def getWord (cfg : Cfg) (n : Nat) (value : Str) : EPy (Tok × Str) := do
  let c ← match value with
    | c :: _ => pure c
    | [] => throw strIndexError
  let (leader, value) ← if isCfwsLeader c then do
      let (l, v) ← getCfws n value
      pure (some l, v)
    else pure (none, value)
  let c ← match value with
    | c :: _ => pure c
    | [] => throw (.hpe (S "Expected 'atom' or 'quoted-string' but found nothing."))
  let (tok, value) ←
    if c == 34 then getQuotedString cfg n value
    else if isSpecial c then
      throw (.hpe (S "Expected 'atom' or 'quoted-string' but found '" ++ value ++ S "'"))
    else getAtom cfg n value
  pure (match leader with
    | some l => tok.prepend l
    | none => tok, value)

/-- The condition of :1475-1481, given the new token and the phrase's elements; `none` when
`token[0]` raises. -/
def ewAfterEw (tok : Tok) (ks : List Tok) : EPy Bool :=
  match tok.kids.head? with
  | none => throw listIndexError
  | some t0 =>
    pure <| t0.ty == "encoded-word" && !ks.isEmpty &&
      (match ks.getLast? with
       | some l =>
         l.ty == "atom" && decide (l.kids.length > 1) &&
         (l.kids.getD (l.kids.length - 2) default).ty == "encoded-word" &&
         (match l.kids.getLast? with
          | some x => x.ty == "cfws" && !(x.kids.any (·.ty == "comment"))
          | none => false)
       | none => false)

/-- The `while` loop of `get_phrase`, :1466-1492. -/
def phraseLoop (cfg : Cfg) : Nat → Str → Tok → EPy (Tok × Str)
  | 0, _, _ => throw .fuel
  | n + 1, value, p =>
    match value with
    | [] => pure (p, [])
    | c :: rest =>
      if isPhraseEnd c then pure (p, value)
      else if c == 46 then
        phraseLoop cfg n rest ((p.push DOT).addDefect (obsoleteHeader (S "period in 'phrase'")))
      else
        match getWord cfg n value with
        | .ok (tok, v') => do
          let ks := p.kids
          let p1 ← (do
            if ← ewAfterEw tok ks then
              let l := ks.getLast?.getD default
              pure (p.setKids (ks.dropLast ++ [l.setKids (l.kids.dropLast ++ [ewws l])]))
            else pure p : EPy Tok)
          phraseLoop cfg n v' (p1.push tok)
        | .error e =>
          if e.isHpe && isCfwsLeader c then do
            let (tok, v') ← getCfws n value
            phraseLoop cfg n v'
              ((p.addDefect (obsoleteHeader (S "comment found without atom"))).push tok)
          else throw e

/-- `get_phrase`, :1447-1493. -/
def getPhrase (cfg : Cfg) (n : Nat) (value : Str) : EPy (Tok × Str) :=
  match getWord cfg n value with
  | .ok (tok, v) => phraseLoop cfg n v ((mkL .phrase).push tok)
  | .error e =>
    if e.isHpe then
      phraseLoop cfg n value ((mkL .phrase).addDefect
        (invalidHeader (S "phrase does not start with word")))
    else throw e

/-! ## Local parts -/

/-- The `while` loop of `get_obs_local_part`, :1534-1561. -/
def obsLocalLoop (cfg : Cfg) : Nat → Str → Tok → Bool → EPy (Tok × Str)
  | 0, _, _, _ => throw .fuel
  | n + 1, value, o, lastDot =>
    match value with
    | [] => pure (o, [])
    | c :: rest =>
      if !(c == 92 || !isPhraseEnd c) then pure (o, value)
      else if c == 46 then
        let o := if lastDot then o.addDefect (invalidHeader (S "invalid repeated '.'")) else o
        obsLocalLoop cfg n rest (o.push DOT) true
      else if c == 92 then
        obsLocalLoop cfg n rest ((o.push (VT [92] "misplaced-special")).addDefect
          (invalidHeader (S "'\\' character outside of quoted-string/ccontent"))) false
      else
        let o := match o.kids.getLast? with
          | some l => if l.ty != "dot" then
              o.addDefect (invalidHeader (S "missing '.' between words")) else o
          | none => o
        match getWord cfg n value with
        | .ok (tok, v) => obsLocalLoop cfg n v (o.push tok) false
        | .error e =>
          if e.isHpe && isCfwsLeader c then do
            let (tok, v) ← getCfws n value
            obsLocalLoop cfg n v (o.push tok) lastDot
          else throw e

/-- `get_obs_local_part`, :1529-1579. -/
def getObsLocalPart (cfg : Cfg) (n : Nat) (value : Str) : EPy (Tok × Str) := do
  let (o, value) ← obsLocalLoop cfg n value (mkL .obsLocalPart) false
  let ks := o.kids
  if ks.isEmpty then throw (.hpe (S "expected obs-local-part but found '" ++ value ++ S "'"))
  let ty (i : Nat) := (ks.getD i default).ty
  let o := if ty 0 == "dot" || (ty 0 == "cfws" && decide (ks.length > 1) && ty 1 == "dot") then
      o.addDefect (invalidHeader (S "Invalid leading '.' in local part")) else o
  let o := if ty (ks.length - 1) == "dot" ||
      (ty (ks.length - 1) == "cfws" && decide (ks.length > 1) && ty (ks.length - 2) == "dot") then
      o.addDefect (invalidHeader (S "Invalid trailing '.' in local part")) else o
  pure (if o.ds.isEmpty then o else o.setTy "invalid-obs-local-part", value)

/-- `get_local_part`, :1495-1527. -/
def getLocalPart (cfg : Cfg) (n : Nat) (value : Str) : EPy (Tok × Str) := do
  let (leader, value) ← if headIs isCfwsLeader value then do
      let (l, v) ← getCfws n value
      pure (some l, v)
    else pure (none, value)
  if value.isEmpty then throw (.hpe (S "expected local-part but found '" ++ value ++ S "'"))
  let c := value.headD 0
  let (tok, value) ←
    match getDotAtom cfg n value with
    | .ok r => pure r
    | .error e =>
      if e.isHpe then
        match getWord cfg n value with
        | .ok r => pure r
        | .error e2 =>
          if e2.isHpe then
            if c != 92 && isPhraseEnd c then throw e2 else pure (plainL [], value)
          else throw e2
      else throw e
  let tok := match leader with
    | some l => tok.prepend l
    | none => tok
  let lp := (mkL .localPart).push tok
  if headIs (fun c => c == 92 || !isPhraseEnd c) value then
    let (o, value) ← getObsLocalPart cfg n (lp.str ++ value)
    let lp := if o.ty == "invalid-obs-local-part" then
        lp.addDefect (invalidHeader (S "local-part is not dot-atom, quoted-string, or obs-local-part"))
      else lp.addDefect (obsoleteHeader (S "local-part is not a dot-atom (contains CFWS)"))
    pure (lp.setKids [o], value)
  else pure (lp, value)

/-! ## Domains -/

/-- `get_dtext`, :1581-1599. -/
def getDtext (value : Str) : EPy (Tok × Str) := do
  let (ptext, v, hadQp) ← getPtextToEndchars value (fun c => c == 91 || c == 93)
  let t := VT ptext "ptext"
  let t := if hadQp then t.addDefect (obsoleteHeader (S "quoted printable found in domain-literal")) else t
  pure (validateXtext t, v)

/-- `_check_for_early_dl_end`, :1601-1607: `none` when `value` is not empty, else the
domain-literal with the defect and the closing terminal. -/
def checkEarlyDlEnd (value : Str) (dl : Tok) : Option Tok :=
  if !value.isEmpty then none
  else some ((dl.addDefect (invalidHeader (S "end of input inside domain-literal"))).push
    (VT [93] "domain-literal-end"))

/-- `get_domain_literal`, :1609-1646. -/
def getDomainLiteral (n : Nat) (value : Str) : EPy (Tok × Str) := do
  let c ← match value with
    | c :: _ => pure c
    | [] => throw strIndexError
  let (dl, value) ← if isCfwsLeader c then optCfws n (mkL .domainLiteral) value
    else pure (mkL .domainLiteral, value)
  match value with
  | [] => throw (.hpe (S "expected domain-literal"))
  | c :: v =>
    if c != 91 then
      throw (.hpe (S "expected '[' at start of domain-literal but found '" ++ value ++ S "'"))
    let dl := dl.push (VT [91] "domain-literal-start")
    match checkEarlyDlEnd v dl with
    | some d => return (d, v)
    | none =>
    let (dl, value) := if headIs isWsp v then (let (t, v') := getFws v; (dl.push t, v')) else (dl, v)
    let (tok, value) ← getDtext value
    let dl := dl.push tok
    match checkEarlyDlEnd value dl with
    | some d => return (d, value)
    | none =>
    let (dl, value) := if headIs isWsp value then (let (t, v') := getFws value; (dl.push t, v'))
      else (dl, value)
    match checkEarlyDlEnd value dl with
    | some d => return (d, value)
    | none =>
    match value with
    | 93 :: v' => optCfws n (dl.push (VT [93] "domain-literal-end")) v'
    | _ => throw (.hpe (S "expected ']' at end of domain-literal but found '" ++ value ++ S "'"))

/-- The `while` loop of `get_domain`, :1680-1683. -/
def domainDotLoop (cfg : Cfg) : Nat → Str → Tok → EPy (Tok × Str)
  | 0, _, _ => throw .fuel
  | n + 1, value, d =>
    match value with
    | 46 :: v => do
      let (tok, v') ← getAtom cfg n v
      domainDotLoop cfg n v' ((d.push DOT).push tok)
    | _ => pure (d, value)

/-- `get_domain`, :1648-1684. -/
def getDomain (cfg : Cfg) (n : Nat) (value : Str) : EPy (Tok × Str) := do
  let (leader, value) ← if headIs isCfwsLeader value then do
      let (l, v) ← getCfws n value
      pure (some l, v)
    else pure (none, value)
  let pre (t : Tok) := match leader with
    | some l => t.prepend l
    | none => t
  match value with
  | [] => throw (.hpe (S "expected domain but found '" ++ value ++ S "'"))
  | c :: _ =>
    if c == 91 then
      let (tok, value) ← getDomainLiteral n value
      return ((mkL .domain).push (pre tok), value)
    let (tok, value) ←
      match getDotAtom cfg n value with
      | .ok r => pure r
      | .error e => if e.isHpe then getAtom cfg n value else throw e
    if headIs (· == 64) value then throw (.hpe (S "Invalid Domain"))
    let d := (mkL .domain).push (pre tok)
    if headIs (· == 46) value then
      let d := d.addDefect (obsoleteHeader (S "domain is not a dot-atom (contains CFWS)"))
      let d := if (d.kids.headD default).ty == "dot-atom" then d.setKids (d.kids.headD default).kids
        else d
      domainDotLoop cfg n value d
    else pure (d, value)

/-- `get_addr_spec`, :1686-1700. -/
def getAddrSpec (cfg : Cfg) (n : Nat) (value : Str) : EPy (Tok × Str) := do
  let (tok, value) ← getLocalPart cfg n value
  let a := (mkL .addrSpec).push tok
  match value with
  | 64 :: v =>
    let (tok, v') ← getDomain cfg n v
    pure ((a.push (VT [64] "address-at-symbol")).push tok, v')
  | _ => pure (a.addDefect (invalidHeader (S "addr-spec local part with no domain")), value)

end PyLean.TextLibs.Email
