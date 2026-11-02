import PyLean.TextLibs.EtreeModel
import PyLean.UnicodeObj.Repr
import PyLean.LongObj.Pylong

/-!
`xml.etree.ElementPath` (Lib/xml/etree/ElementPath.py, CPython 3.15.2) and the C accelerator's
`find`, `findtext`, `findall` and `iterfind` (Modules/_elementtree.c:1192-1442), which take a fast
path of their own when `checkpath` finds no XPath character.

Strings are lists of code points. `\s` and `\d` in the tokenizer's `re` pattern are
`Py_UNICODE_ISSPACE` and `Py_UNICODE_ISDECIMAL` for a str pattern (`UnicodeObj.isSpace`,
`UnicodeObj.isDecimalDigit`); `int()` is `LongObj.intOfStr` with the default 4300-digit limit.

Scope: tags, texts, paths, prefixes and URIs are `str`; `namespaces` is `None` or a dict of str
to str. The selector cache `_cache` is left out: a compiled selector list depends only on the
cache key, so a cache hit returns what compiling again would, and an empty path is never cached.
The selectors are data (`Sel`); `run` executes the ones that do not need a parent map
(child, `*`, `.`, `//` and the wildcard tags) and reports the rest as unmodelled.
-/

namespace PyLean.TextLibs.Etree

open PyLean
open PyLean.UnicodeObj (isSpace isDecimalDigit unicodeRepr)
open PyLean.LongObj (intOfStr)

/-- A str as code points. -/
abbrev S := List Nat

def ch (c : Char) : Nat := c.toNat

/-- `"".join` of literals. -/
def lit (s : String) : S := s.toList.map Char.toNat

def syntaxError (msg : S) : PyExc := .named "SyntaxError" (String.ofList (msg.map Char.ofNat))

/-! ## `xpath_tokenizer_re.findall` (ElementPath.py:61-72) -/

/-- A match: group 1 (an operator or a quoted string) and group 2 (a tag); `\s+` gives `("", "")`. -/
abbrev Tok := S × S

/-- `[^q]*q` after an opening quote `q`: the text and the rest after the closing quote. -/
def quoted (q : Nat) : S → Option (S × S)
  | [] => none
  | x :: xs => if x = q then some ([], xs) else (quoted q xs).map fun (a, r) => (x :: a, r)

/-- `[/.*:\[\]\(\)@=]`. -/
def isOpChar (x : Nat) : Bool := (lit "/.*:[]()@=").contains x

/-- `[^/\[\]\(\)@!=\s]`. -/
def isTagChar (x : Nat) : Bool := !(lit "/[]()@!=").contains x && !isSpace x

/-- Group 1, alternatives tried left to right (ElementPath.py:63-69): the quoted strings,
`::`, `//?`, `..`, `()`, `!=`, then one operator character. -/
def matchOp : S → Option (S × S)
  | [] => none
  | x :: rest =>
    let q := if x = ch '\'' ∨ x = ch '"' then (quoted x rest).map (fun (inner, r) => (x :: inner ++ [x], r))
      else none
    match q with
    | some m => some m
    | none =>
      match rest with
      | y :: r2 =>
        if (x = ch ':' ∧ y = ch ':') ∨ (x = ch '/' ∧ y = ch '/') ∨ (x = ch '.' ∧ y = ch '.') ∨
            (x = ch '(' ∧ y = ch ')') ∨ (x = ch '!' ∧ y = ch '=') then some ([x, y], r2)
        else if isOpChar x then some ([x], rest) else none
      | [] => if isOpChar x then some ([x], []) else none

/-- The longest run of tag characters. -/
def tagRun : S → S × S
  | [] => ([], [])
  | x :: xs => if isTagChar x then let (a, r) := tagRun xs; (x :: a, r) else ([], x :: xs)

/-- `[^}]*}`: the text up to the first `}` and the rest after it. -/
def upToBrace : S → Option (S × S)
  | [] => none
  | x :: xs => if x = ch '}' then some ([], xs) else (upToBrace xs).map fun (a, r) => (x :: a, r)

/-- Group 2, `(?:\{[^}]+\})?[^/\[\]\(\)@!=\s]+` (ElementPath.py:70): the optional braced
namespace is tried first, and dropped when no tag character follows it. -/
def matchTag (s : S) : Option (S × S) :=
  let withBrace : Option (S × S) :=
    match s with
    | x :: xs =>
      if x = ch '{' then
        match upToBrace xs with
        | some (inner, r) =>
          if inner = [] then none
          else
            let (t, r') := tagRun r
            if t = [] then none else some (x :: inner ++ ch '}' :: t, r')
        | none => none
      else none
    | [] => none
  match withBrace with
  | some m => some m
  | none => let (t, r) := tagRun s; if t = [] then none else some (t, r)

def spaceRun : S → S
  | [] => []
  | x :: xs => if isSpace x then spaceRun xs else x :: xs

/-- `re.findall` with this pattern: at each position the first alternative that matches wins;
a character no alternative matches (a `!` not followed by `=`, say) is skipped. Every match is
nonempty, so the string's length is enough fuel. -/
def tokenizeF : Nat → S → List Tok
  | 0, _ => []
  | _ + 1, [] => []
  | f + 1, x :: xs =>
    match matchOp (x :: xs) with
    | some (op, r) => (op, []) :: tokenizeF f r
    | none =>
      match matchTag (x :: xs) with
      | some (t, r) => ([], t) :: tokenizeF f r
      | none => if isSpace x then ([], []) :: tokenizeF f (spaceRun xs) else tokenizeF f xs

def tokenize (s : S) : List Tok := tokenizeF s.length s

/-! ## `xpath_tokenizer` (ElementPath.py:74-95) -/

/-- The tokens a generator yields before it raises (`err`) or ends (`err = none`). -/
structure Stream where
  toks : List Tok
  err : Option PyExc

def Stream.cons (t : Tok) (s : Stream) : Stream := ⟨t :: s.toks, s.err⟩

/-- `namespaces[k]` / `namespaces.get(k)` on a dict given as its items. -/
def nsLookup (ns : List (S × S)) (k : S) : Option S := (ns.find? (·.1 == k)).map (·.2)

/-- `tag.split(":", 1)` for a tag containing `:`. -/
def splitColon (t : S) : S × S := (t.takeWhile (· ≠ ch ':'), (t.dropWhile (· ≠ ch ':')).drop 1)

def prefixError (p : S) : PyExc :=
  syntaxError (lit "prefix " ++ unicodeRepr p ++ lit " not found in prefix map")

/-- The generator body, token by token; `pa` is `parsing_attribute`. -/
def nsToks (ns : List (S × S)) (dflt : Option S) : Bool → List Tok → Stream
  | _, [] => ⟨[], none⟩
  | pa, (ttype, tag) :: rest =>
    if tag ≠ [] ∧ tag.head? ≠ some (ch '{') then
      if ch ':' ∈ tag then
        let (pre, uri) := splitColon tag
        if ns = [] then ⟨[], some (prefixError pre)⟩
        else match nsLookup ns pre with
          | none => ⟨[], some (prefixError pre)⟩
          | some u => (nsToks ns dflt false rest).cons (ttype, ch '{' :: u ++ ch '}' :: uri)
      else match dflt with
        | some d =>
          if d ≠ [] ∧ !pa then (nsToks ns dflt false rest).cons (ttype, ch '{' :: d ++ ch '}' :: tag)
          else (nsToks ns dflt false rest).cons (ttype, tag)
        | none => (nsToks ns dflt false rest).cons (ttype, tag)
    else (nsToks ns dflt (ttype == lit "@") rest).cons (ttype, tag)

/-- `xpath_tokenizer(pattern, namespaces)`: `default_namespace = namespaces.get('') if namespaces
else None`; a dict is falsy when empty. -/
def xpathTokenizer (pattern : S) (ns : List (S × S)) : Stream :=
  nsToks ns (if ns = [] then none else nsLookup ns []) false (tokenize pattern)

/-- `next()` on the generator: a token, `StopIteration` (`none`), or what the generator raises. -/
def Stream.next (s : Stream) : Py (Option (Tok × Stream)) :=
  match s.toks with
  | t :: ts => .ok (some (t, ⟨ts, s.err⟩))
  | [] => match s.err with
    | some e => .error e
    | none => .ok none

/-! ## Selectors (ElementPath.py:108-344) -/

/-- A compiled step. -/
inductive Sel where
  /-- `prepare_child`, a plain tag (`{}` already stripped). -/
  | child (tag : S)
  /-- `prepare_child` with a wildcard tag, through `_prepare_tag`. -/
  | childW (tag : S)
  | star
  | self
  | parent
  /-- `prepare_descendant`, a plain tag or `*`. -/
  | desc (tag : S)
  | descW (tag : S)
  | attrHas (key : S)
  | attrEq (key value : S) (neg : Bool)
  | hasChild (tag : S)
  | textEq (tag value : S) (neg : Bool)
  | index (i : Int)
  deriving Repr, DecidableEq

/-- `_is_wildcard_tag`, ElementPath.py:108-109. -/
def isWildcard (tag : S) : Bool := tag.take 3 == lit "{*}" || (tag.length ≥ 2 && tag.drop (tag.length - 2) == lit "}*")

/-- `if tag[:2] == '{}': tag = tag[2:]`. -/
def stripEmptyNs (tag : S) : S := if tag.take 2 == lit "{}" then tag.drop 2 else tag

/-- `prepare_child`, ElementPath.py:153-170. -/
def prepareChild (tag : S) : Sel := if isWildcard tag then .childW tag else .child (stripEmptyNs tag)

/-- `prepare_descendant`, ElementPath.py:183-212. `none` is its bare `return`. -/
def prepareDescendant (s : Stream) : Py (Option Sel × Stream) :=
  match s.next with
  | .error e => .error e
  | .ok none => .ok (none, ⟨[], none⟩)
  | .ok (some ((ty, tag), s')) =>
    if ty = lit "*" then .ok (some (.desc (lit "*")), s')
    else if ty = [] then
      .ok (some (if isWildcard tag then .descW tag else .desc (stripEmptyNs tag)), s')
    else .error (syntaxError (lit "invalid descendant"))

/-- The token loop of `prepare_predicate` (ElementPath.py:232-245): signature and predicate parts
up to `]`, or `none` when the tokens run out first. -/
def predLoop : Nat → Stream → List S → List S → Py (Option (List S × List S × Stream))
  | 0, _, _, _ => .error .modelFuel
  | f + 1, s, sig, pred =>
    match s.next with
    | .error e => .error e
    | .ok none => .ok none
    | .ok (some ((ty, tag), s')) =>
      if ty = lit "]" then .ok (some (sig, pred, s'))
      else if ty = [] ∧ tag = [] then predLoop f s' sig pred
      else
        let (ty, tag) :=
          if ty ≠ [] ∧ (ty.head? = some (ch '\'') ∨ ty.head? = some (ch '"')) then
            (lit "'", (ty.drop 1).dropLast) else (ty, tag)
        predLoop f s' (sig ++ [if ty = [] then lit "-" else ty]) (pred ++ [tag])

/-- `re.match(r"\-?\d+$", p)` on a tag token (which holds no newline). -/
def isIntLit (p : S) : Bool :=
  match p with
  | x :: ds => if x = ch '-' && ds ≠ [] && ds.all isDecimalDigit then true
    else p.all isDecimalDigit
  | [] => false

/-- `int(p)`. -/
def pyIntOf (p : S) : Py Int := do
  let v ← intOfStr 4300 p 10
  return v.toInt

def getD (l : List S) (i : Nat) : S := l.getD i []

/-- The signature dispatch of `prepare_predicate`, ElementPath.py:246-344. `predicate[-1]` is the
last part. -/
def predSelect (sig : S) (pred : List S) : Py Sel :=
  let last := pred.getLastD []
  if sig = lit "@-" then .ok (.attrHas (getD pred 1))
  else if sig = lit "@-='" ∨ sig = lit "@-!='" then
    .ok (.attrEq (getD pred 1) last (decide (sig = lit "@-!='")))
  else if sig = lit "-" ∧ !isIntLit (getD pred 0) then .ok (.hasChild (getD pred 0))
  else if sig = lit ".='" ∨ sig = lit ".!='" ∨
      ((sig = lit "-='" ∨ sig = lit "-!='") ∧ !isIntLit (getD pred 0)) then
    .ok (.textEq (getD pred 0) last (decide (sig = lit ".!='" ∨ sig = lit "-!='")))
  else if sig = lit "-" ∨ sig = lit "-()" ∨ sig = lit "-()-" then
    if sig = lit "-" then
      match pyIntOf (getD pred 0) with
      | .error e => .error e
      | .ok n => if n - 1 < 0 then .error (syntaxError (lit "XPath position >= 1 expected")) else .ok (.index (n - 1))
    else if getD pred 0 ≠ lit "last" then .error (syntaxError (lit "unsupported function"))
    else if sig = lit "-()-" then
      match pyIntOf (getD pred 2) with
      | .error _ => .error (syntaxError (lit "unsupported expression"))
      | .ok n => if n - 1 > -2 then .error (syntaxError (lit "XPath offset from last() must be negative"))
        else .ok (.index (n - 1))
    else .ok (.index (-1))
  else .error (syntaxError (lit "invalid predicate"))

/-- `prepare_predicate`, ElementPath.py:227-344. `none` is its bare `return` at :236. -/
def preparePredicate (s : Stream) : Py (Option Sel × Stream) :=
  match predLoop (s.toks.length + 1) s [] [] with
  | .error e => .error e
  | .ok none => .ok (none, ⟨[], none⟩)
  | .ok (some (sig, pred, s')) =>
    match predSelect (sig.foldl (· ++ ·) []) pred with
    | .ok sel => .ok (some sel, s')
    | .error e => .error e

/-- `ops[token[0]](next, token)`, ElementPath.py:346-353: a token type outside the table raises
`KeyError(token[0])`. -/
def applyOp (tok : Tok) (s : Stream) : Py (Option Sel × Stream) :=
  let (ty, tag) := tok
  if ty = [] then .ok (some (prepareChild tag), s)
  else if ty = lit "*" then .ok (some .star, s)
  else if ty = lit "." then .ok (some .self, s)
  else if ty = lit ".." then .ok (some .parent, s)
  else if ty = lit "//" then prepareDescendant s
  else if ty = lit "[" then preparePredicate s
  else .error (.keyError (String.ofList ((unicodeRepr ty).map Char.ofNat)))

/-- The compile loop of `iterfind`, ElementPath.py:388-399. -/
def compileLoop : Nat → Tok → Stream → List (Option Sel) → Py (List (Option Sel))
  | 0, _, _, _ => .error .modelFuel
  | f + 1, tok, s, acc =>
    match applyOp tok s with
    | .error e => .error e
    | .ok (sel, s) =>
      let acc := acc ++ [sel]
      match s.next with
      | .error e => .error e
      | .ok none => .ok acc
      | .ok (some (t, s)) =>
        if t.1 = lit "/" then
          match s.next with
          | .error e => .error e
          | .ok none => .ok acc
          | .ok (some (t2, s2)) => compileLoop f t2 s2 acc
        else compileLoop f t s acc

/-- Every selector, or `none` if one is `None`. -/
def allSome : List (Option Sel) → Option (List Sel)
  | [] => some []
  | none :: _ => none
  | some x :: xs => (allSome xs).map (x :: ·)

/-- What `iterfind` hands back: `None` (its bare `return` at :387) or the generator chain. -/
inductive IterOut where
  | none
  | gen (sels : List Sel)
  deriving Repr, DecidableEq

/-- `iterfind(elem, path, namespaces)`, ElementPath.py:367-406. Calling each `select` only creates
a generator, except a `None` left by `prepare_predicate`/`prepare_descendant`, which is called. -/
def iterfindPath (path : S) (ns : List (S × S)) : Py IterOut :=
  let path := if path.getLast? = some (ch '/') then path ++ lit "*" else path
  if path.head? = some (ch '/') then .error (syntaxError (lit "cannot use absolute path on element"))
  else
    let s := xpathTokenizer path ns
    match s.next with
    | .error e => .error e
    | .ok none => .ok .none
    | .ok (some (t, s)) =>
      match compileLoop (s.toks.length + 2) t s [] with
      | .error e => .error e
      | .ok sels =>
        match allSome sels with
        | some ss => .ok (.gen ss)
        | none => .error (.typeError "'NoneType' object is not callable")

/-! ## Running selectors on a tree -/

/-- An element: tag, text, children. -/
inductive Elem where
  | mk (tag : S) (text : Option S) (kids : List Elem)
  deriving Repr, Inhabited

def Elem.tag : Elem → S | .mk t _ _ => t
def Elem.text : Elem → Option S | .mk _ x _ => x
def Elem.kids : Elem → List Elem | .mk _ _ k => k

mutual
/-- `elem.iter()`, document order, `elem` first. -/
def Elem.iterAll : Elem → List Elem
  | .mk t x k => .mk t x k :: iterList k
def iterList : List Elem → List Elem
  | [] => []
  | e :: es => e.iterAll ++ iterList es
end

/-- Elements a generator yields before it raises (`err`) or ends. -/
abbrev Gen := List Elem × Option PyExc

/-- `_prepare_tag(tag)`'s filter on one element (ElementPath.py:112-150): `el_tag[0]` raises
`IndexError` on an empty tag. -/
def wildOk (tag : S) (el : S) : Py Bool :=
  if tag = lit "{*}*" then .ok true
  else if tag = lit "{}*" then
    match el.head? with
    | some c0 => .ok (c0 ≠ ch '{')
    | none => .error (.indexError "string index out of range")
  else if tag.take 3 = lit "{*}" then
    let suffix := tag.drop 2
    .ok (el = tag.drop 3 || (el.length ≥ suffix.length && el.drop (el.length - suffix.length) == suffix) ||
      (el.length < suffix.length && el == suffix))
  else .ok (el.take (tag.length - 1) == tag.take (tag.length - 1))

/-- Filter a generator through a fallible test, stopping at the first exception. -/
def filterGen (p : Elem → Py Bool) : List Elem → Gen
  | [] => ([], none)
  | e :: es => match p e with
    | .error x => ([], some x)
    | .ok true => let (r, x) := filterGen p es; (e :: r, x)
    | .ok false => filterGen p es

/-- One selector over the incoming generator; `none` for the selectors that need a parent map or
`find` recursion, which this model does not execute. -/
def runSel (sel : Sel) (g : Gen) : Option Gen :=
  let (es, err) := g
  let joinErr : Gen → Gen := fun (r, x) => (r, match x with | some x => some x | none => err)
  match sel with
  | .child tag => some (joinErr ((es.flatMap Elem.kids).filter (·.tag == tag), none))
  | .childW tag => some (joinErr (filterGen (fun e => wildOk tag e.tag) (es.flatMap Elem.kids)))
  | .star => some (joinErr (es.flatMap Elem.kids, none))
  | .self => some g
  | .desc tag => some (joinErr ((es.flatMap fun e => (e.iterAll.drop 1).filter
      fun d => tag == lit "*" || d.tag == tag), none))
  | .descW tag => some (joinErr (filterGen (fun e => wildOk tag e.tag) (es.flatMap fun e => e.iterAll.drop 1)))
  | _ => none

def runSels : List Sel → Gen → Option Gen
  | [], g => some g
  | s :: ss, g => match runSel s g with
    | some g' => runSels ss g'
    | none => none

/-! ## The Python-level entry points (ElementPath.py:411-430) -/

/-- `findall(elem, path, namespaces)`: `list(iterfind(...))`. `none` when a selector is not run
by this model. -/
def findallPy (root : Elem) (path : S) (ns : List (S × S)) : Option (Py (List Elem)) :=
  match iterfindPath path ns with
  | .error e => some (.error e)
  | .ok .none => some (.error (.typeError "'NoneType' object is not iterable"))
  | .ok (.gen sels) => (runSels sels ([root], none)).map fun (es, x) =>
      match x with | some e => .error e | none => .ok es

/-- `find`: `next(iterfind(...), None)`. -/
def findPy (root : Elem) (path : S) (ns : List (S × S)) : Option (Py (Option Elem)) :=
  match iterfindPath path ns with
  | .error e => some (.error e)
  | .ok .none => some (.error (.typeError "'NoneType' object is not an iterator"))
  | .ok (.gen sels) => (runSels sels ([root], none)).map fun (es, x) =>
      match es with
      | e :: _ => .ok (some e)
      | [] => match x with | some e => .error e | none => .ok none

/-- `findtext`: the first match's text (`""` for `None`), or `default`. -/
def findtextPy (root : Elem) (path : S) (dflt : Option S) (ns : List (S × S)) : Option (Py (Option S)) :=
  match iterfindPath path ns with
  | .error e => some (.error e)
  | .ok .none => some (.error (.typeError "'NoneType' object is not an iterator"))
  | .ok (.gen sels) => (runSels sels ([root], none)).map fun (es, x) =>
      match es with
      | e :: _ => .ok (some (e.text.getD []))
      | [] => match x with | some e => .error e | none => .ok dflt

/-! ## The C accelerator (Modules/_elementtree.c) -/

/-- `PATHCHAR`, :1199-1200. -/
def isPathChar (x : Nat) : Bool := (lit "/*[@.").contains x

/-- The scan of `checkpath`, :1210-1218: a `{` turns checking off, a `}` back on. -/
def checkScan : Bool → S → Bool
  | _, [] => false
  | check, x :: xs =>
    if x = ch '{' then checkScan false xs
    else if x = ch '}' then checkScan true xs
    else if check && isPathChar x then true
    else checkScan check xs

/-- `checkpath(tag)` for a str, :1192-1219: `{}tag` and `{*}tag` are paths, otherwise any
`PATHCHAR` outside braces. -/
def checkpath (p : S) : Bool :=
  match p with
  | a :: b :: c :: _ => if a = ch '{' ∧ (b = ch '}' ∨ (b = ch '*' ∧ c = ch '}')) then true else checkScan true p
  | _ => checkScan true p

/-- `Element.findall(path, namespaces)`, :1387-1420: ElementPath when `checkpath(path)` or
`namespaces is not None`, else the children whose tag equals `path`. `ns = none` is `None`. -/
def findallC (root : Elem) (path : S) (ns : Option (List (S × S))) : Option (Py (List Elem)) :=
  if checkpath path || ns.isSome then findallPy root path (ns.getD [])
  else some (.ok (root.kids.filter (·.tag == path)))

/-- `Element.find`, :1295-1324. -/
def findC (root : Elem) (path : S) (ns : Option (List (S × S))) : Option (Py (Option Elem)) :=
  if checkpath path || ns.isSome then findPy root path (ns.getD [])
  else some (.ok (root.kids.find? (·.tag == path)))

/-- `Element.findtext`, :1338-1374; `element_get_text` gives `""` for `None`. -/
def findtextC (root : Elem) (path : S) (dflt : Option S) (ns : Option (List (S × S))) :
    Option (Py (Option S)) :=
  if checkpath path || ns.isSome then findtextPy root path dflt (ns.getD [])
  else some (.ok (match root.kids.find? (·.tag == path) with
    | some e => some (e.text.getD [])
    | none => dflt))

/-- `Element.iterfind`, :1433-1442: always ElementPath. -/
def iterfindC (path : S) (ns : Option (List (S × S))) : Py IterOut := iterfindPath path (ns.getD [])

end PyLean.TextLibs.Etree
