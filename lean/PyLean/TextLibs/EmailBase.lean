import PyLean.UnicodeObj.Repr
import PyLean.UnicodeObj.TextCase

/-!
Model of `Lib/email/_header_value_parser.py`, CPython 3.15.2: character sets, the token tree,
and the methods of the token classes (`__str__`, `value`, `all_defects`, `__repr__`,
`DisplayName.display_name`, ...).

A `str` is a list of code points (`UnicodeObj.Str`), so the surrogate-escaped bytes
`_validate_xtext` looks for can be represented.

The tree. A `TokenList` subclass instance is `Tok.node c ty kids ds attrs`: its class `c`, its
`token_type` (an instance can override the class's, as `get_mailbox` does), its elements, its
`defects` list and the attributes set on the instance (`vars(x)` without `defects` and
`token_type`, in insertion order; `del` removes one, and a read then falls back to the class
default). A `Terminal` is `Tok.term c s ty ds`: its class, its text (the `str` it is), its
`token_type` and `defects`. The parser never shares a mutable token between two places of a
tree, except the module constants `DOT`, `ListSeparator` and `RouteComponentMarker`, which it
never mutates; so a tree of values describes the Python objects.

Exceptions are `EExc` rather than `PyExc` because their messages embed the parsed text, which
may hold lone surrogates that a Lean `String` cannot.
-/

namespace PyLean.TextLibs.Email

open PyLean PyLean.UnicodeObj

abbrev Str := UnicodeObj.Str

/-- Code points of a Lean string literal. -/
def S (s : String) : Str := s.toList.map Char.toNat

/-! ## Exceptions -/

/-- The exceptions the parser can raise. -/
inductive EExc where
  /-- `errors.HeaderParseError(msg)`. -/
  | hpe (msg : Str)
  /-- `_InvalidEwError(msg)`, a subclass of `HeaderParseError`, _header_value_parser.py:981-982. -/
  | invalidEw (msg : Str)
  | indexError (msg : String)
  /-- `ValueError` from `int()`. -/
  | valueError (msg : Str)
  | unboundLocal (msg : String)
  | assertionError (msg : Str)
  /-- An exception raised by `_ew.decode` that `get_encoded_word` does not catch. -/
  | decRaise (cls : String) (msg : Str)
  /-- `RecursionError("maximum recursion depth exceeded")`: a Python call found no frame left
  (`_Py_CheckRecursiveCallPy`, Python/ceval.c). -/
  | recursionError
  /-- Not a Python exception: the model's loop fuel ran out. -/
  | fuel
  deriving Repr, DecidableEq, Inhabited

abbrev EPy (α : Type) := Except EExc α

/-- `except errors.HeaderParseError:` catches this exception. -/
def EExc.isHpe : EExc → Bool
  | .hpe _ | .invalidEw _ => true
  | _ => false

/-- `type(e).__name__`. -/
def EExc.cls : EExc → String
  | .hpe _ => "HeaderParseError"
  | .invalidEw _ => "_InvalidEwError"
  | .indexError _ => "IndexError"
  | .valueError _ => "ValueError"
  | .unboundLocal _ => "UnboundLocalError"
  | .assertionError _ => "AssertionError"
  | .decRaise c _ => c
  | .recursionError => "RecursionError"
  | .fuel => "<model fuel exhausted>"

/-- `str(e)`. -/
def EExc.msg : EExc → Str
  | .hpe m | .invalidEw m | .valueError m | .assertionError m | .decRaise _ m => m
  | .indexError m | .unboundLocal m => S m
  | .recursionError => S "maximum recursion depth exceeded"
  | .fuel => []

def strIndexError : EExc := .indexError "string index out of range"
def listIndexError : EExc := .indexError "list index out of range"

/-! ## Character sets, _header_value_parser.py:83-97 -/

def mem (cs : String) (c : Nat) : Bool := (S cs).contains c

/-- `WSP`, :83-84. -/
def isWsp (c : Nat) : Bool := c == 32 || c == 9
/-- `CFWS_LEADER`, :85. -/
def isCfwsLeader (c : Nat) : Bool := isWsp c || c == 40
/-- `SPECIALS`, :86. -/
def isSpecial (c : Nat) : Bool := mem "()<>@,:;.\\\"[]" c
/-- `ATOM_ENDS`, :87. -/
def isAtomEnd (c : Nat) : Bool := isSpecial c || isWsp c
/-- `DOT_ATOM_ENDS`, :88. -/
def isDotAtomEnd (c : Nat) : Bool := isAtomEnd c && c != 46
/-- `PHRASE_ENDS`, :90. -/
def isPhraseEnd (c : Nat) : Bool := isSpecial c && !mem ".\"(" c
/-- `TSPECIALS`, :91. -/
def isTSpecial (c : Nat) : Bool := (isSpecial c || mem "/?=" c) && c != 46
/-- `TOKEN_ENDS`, :92. -/
def isTokenEnd (c : Nat) : Bool := isTSpecial c || isWsp c
/-- `ASPECIALS`, :93. -/
def isASpecial (c : Nat) : Bool := isTSpecial c || mem "*'%" c
/-- `ATTRIBUTE_ENDS`, :94. -/
def isAttributeEnd (c : Nat) : Bool := isASpecial c || isWsp c
/-- `EXTENDED_ATTRIBUTE_ENDS`, :95. -/
def isExtAttributeEnd (c : Nat) : Bool := isAttributeEnd c && c != 37
/-- `string.hexdigits`. -/
def isHexDigit (c : Nat) : Bool := mem "0123456789abcdefABCDEF" c

/-- `value[0] in SET`, false on an empty value (callers guard with `value and`). -/
def headIs (p : Nat → Bool) : Str → Bool
  | c :: _ => p c
  | [] => false

/-! ## `str` methods -/

/-- `str.lstrip()`: drops leading `Py_UNICODE_ISSPACE` characters. -/
def lstrip (s : Str) : Str := s.dropWhile isSpace
/-- `str.rstrip()`. -/
def rstrip (s : Str) : Str := (s.reverse.dropWhile isSpace).reverse
/-- `str.strip()`. -/
def strip (s : Str) : Str := rstrip (lstrip s)

/-- `len(s.split()) > 1`: `s` has two runs of non-whitespace characters. -/
def twoWords (s : Str) : Bool :=
  (((s.dropWhile isSpace).dropWhile (fun c => !isSpace c)).any (fun c => !isSpace c))

/-- `''.join(s.split())`: `s` without its whitespace characters. -/
def joinSplit (s : Str) : Str := s.filter (fun c => !isSpace c)

/-- `str.lower()`, Objects/unicodeobject.c (`do_lower`; the ASCII fast path agrees). -/
def lower (s : Str) : Str := (doLower s).res

/-- `str.startswith(p)`. -/
def startsWith (s p : Str) : Bool := p.isPrefixOf s

/-- `str.split(sep, 1)` for a non-empty separator: `(before, some after)` at the first
occurrence, `(s, none)` when there is none. -/
def split1 (s sep : Str) : Str × Option Str :=
  match s with
  | [] => ([], none)
  | c :: cs =>
    if sep.isPrefixOf s then ([], some (s.drop sep.length))
    else
      let r := split1 cs sep
      (c :: r.1, r.2)

/-- `s.replace(a, b)` for a one-character `a`. -/
def replace1 (a : Nat) (b : Str) (s : Str) : Str := s.flatMap (fun c => if c == a then b else [c])

/-- `str.isdigit()`: non-empty and every character has a digit value. -/
def isdigitStr (s : Str) : Bool := !s.isEmpty && s.all isDigit

/-- `int(s)` (base 10) for a string of `str.isdigit()` characters,
Objects/longobject.c:3186-3212 (`PyLong_FromUnicodeObject`): non-ASCII decimal digits become
ASCII ones, any other non-ASCII character becomes `?`; `PyLong_FromString` reads the digits
and raises `ValueError` past `sys.get_int_max_str_digits()` (`maxd`, 0 = no limit) when they
are more than 640; trailing junk gives "invalid literal", with the repr cut to 200 characters
(`%.200R`). -/
def pyInt (maxd : Nat) (s : Str) : EPy Nat :=
  let ascii := s.map (fun c => if c < 128 then c
    else if toDecimalDigit c ≥ 0 then 48 + (toDecimalDigit c).toNat else 63)
  let ds := ascii.takeWhile (fun c => 48 ≤ c && c ≤ 57)
  if maxd > 0 && ds.length > 640 && ds.length > maxd then
    .error (.valueError (S s!"Exceeds the limit ({maxd} digits) for integer string conversion: value has {ds.length} digits; use sys.set_int_max_str_digits() to increase the limit"))
  else if ds.length == s.length && !s.isEmpty then
    .ok (ds.foldl (fun a c => 10 * a + (c - 48)) 0)
  else .error (.valueError (S "invalid literal for int() with base 10: " ++ (unicodeRepr s).take 200))

/-! ## Defects (Lib/email/errors.py) -/

/-- A defect: its class name and `str(defect)`. -/
structure Defect where
  cls : String
  msg : Str
  deriving Repr, DecidableEq, Inhabited

def invalidHeader (m : Str) : Defect := ⟨"InvalidHeaderDefect", m⟩
def obsoleteHeader (m : Str) : Defect := ⟨"ObsoleteHeaderDefect", m⟩
def missingValue (m : Str) : Defect := ⟨"HeaderMissingRequiredValue", m⟩

/-! ## The token tree -/

/-- Terminal classes: `WhiteSpaceTerminal`, `ValueTerminal`, `EWWhiteSpaceTerminal`. -/
inductive TC where
  | ws | val | ewws
  deriving Repr, DecidableEq, Inhabited

def TC.name : TC → String
  | .ws => "WhiteSpaceTerminal"
  | .val => "ValueTerminal"
  | .ewws => "EWWhiteSpaceTerminal"

/-- `TokenList` and the subclasses the parser instantiates. -/
inductive LC where
  | plain | unstructured | phrase | cfws | atom | token | encodedWord | quotedString
  | bareQuotedString | comment | addressList | address | mailboxList | groupList | group
  | nameAddr | angleAddr | obsRoute | mailbox | invalidMailbox | domain | dotAtom
  | dotAtomText | noFoldLiteral | addrSpec | obsLocalPart | displayName | localPart
  | domainLiteral | mimeVersion | parameter | invalidParameter | attribute | section | value
  | mimeParameters | contentType | contentDisposition | cte | msgId | messageId
  | invalidMessageId | messageIdList
  deriving Repr, DecidableEq, Inhabited

/-- The class name, as `type(x).__name__` prints it. -/
def LC.name : LC → String
  | .plain => "TokenList" | .unstructured => "UnstructuredTokenList" | .phrase => "Phrase"
  | .cfws => "CFWSList" | .atom => "Atom" | .token => "Token" | .encodedWord => "EncodedWord"
  | .quotedString => "QuotedString" | .bareQuotedString => "BareQuotedString"
  | .comment => "Comment" | .addressList => "AddressList" | .address => "Address"
  | .mailboxList => "MailboxList" | .groupList => "GroupList" | .group => "Group"
  | .nameAddr => "NameAddr" | .angleAddr => "AngleAddr" | .obsRoute => "ObsRoute"
  | .mailbox => "Mailbox" | .invalidMailbox => "InvalidMailbox" | .domain => "Domain"
  | .dotAtom => "DotAtom" | .dotAtomText => "DotAtomText" | .noFoldLiteral => "NoFoldLiteral"
  | .addrSpec => "AddrSpec" | .obsLocalPart => "ObsLocalPart" | .displayName => "DisplayName"
  | .localPart => "LocalPart" | .domainLiteral => "DomainLiteral"
  | .mimeVersion => "MIMEVersion" | .parameter => "Parameter"
  | .invalidParameter => "InvalidParameter" | .attribute => "Attribute"
  | .section => "Section" | .value => "Value" | .mimeParameters => "MimeParameters"
  | .contentType => "ContentType" | .contentDisposition => "ContentDisposition"
  | .cte => "ContentTransferEncoding" | .msgId => "MsgID" | .messageId => "MessageID"
  | .invalidMessageId => "InvalidMessageID" | .messageIdList => "MessageIDList"

/-- The class attribute `token_type` (`None` for `TokenList`), :132-897. -/
def LC.defTy : LC → String
  | .plain => "None" | .unstructured => "unstructured" | .phrase => "phrase"
  | .cfws => "cfws" | .atom => "atom" | .token => "token" | .encodedWord => "encoded-word"
  | .quotedString => "quoted-string" | .bareQuotedString => "bare-quoted-string"
  | .comment => "comment" | .addressList => "address-list" | .address => "address"
  | .mailboxList => "mailbox-list" | .groupList => "group-list" | .group => "group"
  | .nameAddr => "name-addr" | .angleAddr => "angle-addr" | .obsRoute => "obs-route"
  | .mailbox => "mailbox" | .invalidMailbox => "invalid-mailbox" | .domain => "domain"
  | .dotAtom => "dot-atom" | .dotAtomText => "dot-atom-text"
  | .noFoldLiteral => "no-fold-literal" | .addrSpec => "addr-spec"
  | .obsLocalPart => "obs-local-part" | .displayName => "display-name"
  | .localPart => "local-part" | .domainLiteral => "domain-literal"
  | .mimeVersion => "mime-version" | .parameter => "parameter"
  | .invalidParameter => "invalid-parameter" | .attribute => "attribute"
  | .section => "section" | .value => "value" | .mimeParameters => "mime-parameters"
  | .contentType => "content-type" | .contentDisposition => "content-disposition"
  | .cte => "content-transfer-encoding" | .msgId => "msg-id" | .messageId => "message-id"
  | .invalidMessageId => "invalid-message-id" | .messageIdList => "message-id-list"

/-- An instance attribute's value. -/
inductive AV where
  | s (x : Str)
  | n (x : Nat)
  | b (x : Bool)
  deriving Repr, DecidableEq, Inhabited

inductive Tok where
  | term (c : TC) (s : Str) (ty : String) (ds : List Defect)
  | node (c : LC) (ty : String) (kids : List Tok) (ds : List Defect) (attrs : List (String × AV))
  deriving Repr, Inhabited

namespace Tok

def ty : Tok → String
  | term _ _ t _ | node _ t _ _ _ => t

def kids : Tok → List Tok
  | node _ _ ks _ _ => ks
  | term .. => []

def ds : Tok → List Defect
  | term _ _ _ d | node _ _ _ d _ => d

/-- `isinstance(x, TokenList)`. -/
def isList : Tok → Bool
  | node .. => true
  | term .. => false

def addDefect (d : Defect) : Tok → Tok
  | term c s t ds => term c s t (ds ++ [d])
  | node c t ks ds a => node c t ks (ds ++ [d]) a

/-- `x.append(y)` on a `TokenList`. Never called on a terminal. -/
def push : Tok → Tok → Tok
  | node c t ks ds a, y => node c t (ks ++ [y]) ds a
  | x, _ => x

/-- `x.extend(ys)`. -/
def pushAll (ys : List Tok) : Tok → Tok
  | node c t ks ds a => node c t (ks ++ ys) ds a
  | x => x

/-- `x[:0] = [y]`. Never called on a terminal. -/
def prepend : Tok → Tok → Tok
  | node c t ks ds a, y => node c t (y :: ks) ds a
  | x, _ => x

/-- `x[:] = ys`. -/
def setKids (ys : List Tok) : Tok → Tok
  | node c t _ ds a => node c t ys ds a
  | x => x

/-- `x.token_type = t`. -/
def setTy (t : String) : Tok → Tok
  | term c s _ ds => term c s t ds
  | node c _ ks ds a => node c t ks ds a

/-- `x.k = v`: a new attribute goes last, an existing one keeps its place. -/
def setAttr (k : String) (v : AV) : Tok → Tok
  | node c t ks ds a =>
    node c t ks ds (if a.any (·.1 == k) then a.map (fun p => if p.1 == k then (k, v) else p)
      else a ++ [(k, v)])
  | x => x

/-- `del x.k`. -/
def delAttr (k : String) : Tok → Tok
  | node c t ks ds a => node c t ks ds (a.filter (·.1 != k))
  | x => x

def getAttr (k : String) : Tok → Option AV
  | node _ _ _ _ a => (a.find? (·.1 == k)).map (·.2)
  | term .. => none

end Tok

/-- A fresh instance of a `TokenList` subclass. -/
def mkL (c : LC) (ks : List Tok := []) : Tok := .node c c.defTy ks [] []
/-- `TokenList(xs)`. -/
def plainL (ks : List Tok) : Tok := mkL .plain ks
/-- `ValueTerminal(s, ty)`. -/
def VT (s : Str) (ty : String) : Tok := .term .val s ty []
/-- `WhiteSpaceTerminal(s, ty)`. -/
def WT (s : Str) (ty : String) : Tok := .term .ws s ty []

/-- `DOT`, :988. -/
def DOT : Tok := VT [46] "dot"
/-- `ListSeparator`, :989-991. -/
def ListSeparator : Tok := VT [44] "list-separator"
/-- `RouteComponentMarker`, :992. -/
def RouteComponentMarker : Tok := VT [64] "route-component-marker"

/-! ## `__str__` -/

/-- `make_quoted_pairs`, :100-102. The two `replace` calls never see each other's output. -/
def makeQuotedPairs (s : Str) : Str :=
  s.flatMap (fun c => if c == 92 then [92, 92] else if c == 34 then [92, 34] else [c])

/-- `make_parenthesis_pairs`, :105-108, and the body of `Comment.quote`, :299-301. -/
def makeParenPairs (s : Str) : Str :=
  s.flatMap (fun c => if c == 92 then [92, 92] else if c == 40 then [92, 40]
    else if c == 41 then [92, 41] else [c])

/-- `quote_string`, :111-113. -/
def quoteString (s : Str) : Str := [34] ++ makeQuotedPairs s ++ [34]

mutual
/-- `str(x)`: `TokenList.__str__` (:142-143), `BareQuotedString.__str__` (:277-278),
`Comment.__str__` (:289-294), `EWWhiteSpaceTerminal.__str__` (:977-978); other terminals are
their text. Scope limit: `MimeParameters.__str__` (:829-837) renders the decoded parameters
(`MimeParameters.params`, RFC 2231 decoding through `urllib.parse` and codecs), which is not
modelled; on a tree holding a `mime-parameters` node this is not `str(x)`, and nothing here
uses it there (the parser itself only takes `str` of local parts). -/
def Tok.str : Tok → Str
  | .term .ewws _ _ _ => []
  | .term _ s _ _ => s
  | .node .bareQuotedString _ ks _ _ => quoteString (strs ks)
  | .node .comment _ ks _ _ => [40] ++ commentStrs ks ++ [41]
  | .node _ _ ks _ _ => strs ks
/-- `''.join(str(x) for x in xs)`. -/
def strs : List Tok → Str
  | [] => []
  | t :: ts => t.str ++ strs ts
/-- `[self.quote(x) for x in self]` of `Comment.__str__`; `Comment.quote`, :296-301. -/
def commentStrs : List Tok → Str
  | [] => []
  | t :: ts => (if t.ty == "comment" then t.str else makeParenPairs t.str) ++ commentStrs ts
end

mutual
/-- `all_defects`: `TokenList.all_defects` (:154-155) and `Terminal.all_defects` (:924-925). -/
def Tok.allDefects : Tok → List Defect
  | .term _ _ _ ds => ds
  | .node _ _ ks ds _ => ds ++ allDefectsL ks
def allDefectsL : List Tok → List Defect
  | [] => []
  | t :: ts => t.allDefects ++ allDefectsL ts
end

mutual
/-- `repr(x)`: `TokenList.__repr__` (:145-147) and `Terminal.__repr__` (:917-918). -/
def Tok.repr : Tok → Str
  | .term c s _ _ => S c.name ++ [40] ++ unicodeRepr s ++ [41]
  | .node c _ ks _ _ => S c.name ++ S "([" ++ reprs ks ++ S "])"
/-- The elements of `list.__repr__`, joined by `", "`. -/
def reprs : List Tok → Str
  | [] => []
  | [t] => t.repr
  | t :: ts => t.repr ++ S ", " ++ reprs ts
end

/-! ## `value` -/

mutual
/-- Number of nodes, the fuel for `Tok.valueF`. -/
def Tok.size : Tok → Nat
  | .term .. => 1
  | .node _ _ ks _ _ => sizeL ks + 1
def sizeL : List Tok → Nat
  | [] => 0
  | t :: ts => t.size + sizeL ts
end

/-- `isinstance(x, TokenList) and x[pick].token_type == 'cfws'` for `pick` = first or last. -/
def listEdgeCfws (first : Bool) (x : Tok) : EPy Bool :=
  if x.isList then
    match (if first then x.kids.head? else x.kids.getLast?) with
    | some y => pure (y.ty == "cfws")
    | none => throw listIndexError
  else pure false

/-- The list `res` of `DisplayName.display_name`, :586-600: a copy of the elements without the
leading and trailing CFWS (taken off the first and last element when those are lists). -/
def displayNameRes (ks : List Tok) : EPy (List Tok) := do
  let res ← match ks with
    | k :: rest =>
      if k.ty == "cfws" then pure rest
      else if k.isList then
        match k.kids with
        | k0 :: krest => pure (if k0.ty == "cfws" then plainL krest :: rest else ks)
        | [] => throw listIndexError
      else pure ks
    | [] => pure ks
  match res.getLast? with
  | none => throw listIndexError
  | some l =>
    if l.ty == "cfws" then pure res.dropLast
    else if l.isList then
      match l.kids.getLast? with
      | some x => pure (if x.ty == "cfws" then res.dropLast ++ [plainL l.kids.dropLast] else res)
      | none => throw listIndexError
    else pure res

/-- `x.value`, with fuel (`Tok.value` gives enough): `TokenList.value` (:150-151),
`WhiteSpaceTokenList.value` (:207-208), `BareQuotedString.value` (:281-282), `AddrSpec.value`
(:556-559), `DisplayName.value` (:604-624) with `DisplayName.display_name` (:585-601),
`LocalPart.value` (:633-637), `QuotedString.quoted_value` (:257-264),
`WhiteSpaceTerminal.value` (:954-955), `ValueTerminal.value` (:964-965),
`EWWhiteSpaceTerminal.value` (:974-975). `TokenList.value` is
`''.join(x.value for x in self if x.value)`; leaving out the empty values changes nothing. -/
def valueF : Nat → Tok → EPy Str
  | 0, _ => throw .fuel
  | _ + 1, .term .ws _ _ _ => pure [32]
  | _ + 1, .term .val s _ _ => pure s
  | _ + 1, .term .ewws _ _ _ => pure []
  | _ + 1, .node .cfws _ _ _ _ => pure [32]
  | _ + 1, .node .comment _ _ _ _ => pure [32]
  | _ + 1, .node .bareQuotedString _ ks _ _ => pure (strs ks)
  | n + 1, .node .localPart _ ks _ _ =>
    match ks with
    | k :: _ =>
      if k.ty == "quoted-string" then
        k.kids.foldlM (fun acc t => do
          let a ← if t.ty == "bare-quoted-string" then pure t.str else valueF n t
          pure (acc ++ a)) []
      else valueF n k
    | [] => throw listIndexError
  | n + 1, .node .addrSpec _ ks _ _ =>
    match ks with
    | k0 :: k1 :: k2 :: _ => do
      let a ← valueF n k0
      let b ← valueF n k1
      let c ← valueF n k2
      pure (rstrip a ++ b ++ lstrip c)
    | k :: _ => valueF n k
    | [] => throw listIndexError
  | n + 1, .node .displayName _ ks ds _ => do
    let quote := !ds.isEmpty || ks.any (·.ty == "quoted-string")
    match ks with
    | k0 :: _ =>
      if quote then
        let pre ← if k0.ty == "cfws" then pure true else listEdgeCfws true k0
        let kl := (ks.getLast?).getD k0
        let post ← if kl.ty == "cfws" then pure true else listEdgeCfws false kl
        let res ← displayNameRes ks
        let dn ← res.foldlM (fun acc t => do pure (acc ++ (← valueF n t))) []
        pure ((if pre then [32] else []) ++ quoteString dn ++ (if post then [32] else []))
      else ks.foldlM (fun acc t => do pure (acc ++ (← valueF n t))) []
    | [] => pure []
  | n + 1, .node _ _ ks _ _ => ks.foldlM (fun acc t => do pure (acc ++ (← valueF n t))) []

/-- `x.value`. -/
def Tok.value (x : Tok) : EPy Str := valueF (x.size + 1) x

/-- `TokenList(xs).value`. -/
def valuesJoin (xs : List Tok) : EPy Str := (plainL xs).value

/-- `DisplayName.display_name`, :585-601. -/
def displayName (x : Tok) : EPy Str :=
  if x.kids.isEmpty then pure [] else do
    let res ← displayNameRes x.kids
    valuesJoin res

end PyLean.TextLibs.Email
