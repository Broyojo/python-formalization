import PyLean.UnicodeObj.FormatPercent
import PyLean.UnicodeObj.Ctype

/-!
`str.format` and `str.format_map`: Objects/stringlib/unicode_format.h.

The objects are a small universe with one open door. `user` is an instance of a Python class: its
`__format__`, `__str__`, `__repr__`, `__getattr__` and `__getitem__` are `Py`-valued, so each can
raise or return the wrong type. The mapping of `format_map` is a function of the keys asked so far,
so it can have state, as `__missing__` or a `__getitem__` that re-enters can. `args` is a tuple and
cannot change. A `__format__` that calls back into `str.format` touches none of this code's state:
`AutoNumber` and the writer are local to the outer call.

Attributes of built-in objects are modelled for `real`, `imag`, `numerator` and `denominator`. Any
other name that exists on a built-in type, such as a bound method, is not.
-/

namespace PyLean.UnicodeObj

open PyLean PyLean.Binary64

/-- The key of `obj[...]` in a field name. -/
inductive GKey where
  | idx (n : Nat)
  | name (s : Str)
  deriving Repr, DecidableEq

/-- The objects `str.format` is modelled on. -/
inductive GObj where
  | int (v : Int)
  | bool (b : Bool)
  | float (x : F64)
  | complex (re im : F64)
  | str (s : Str)
  | none
  | tuple (items : List GObj)
  | dict (items : List (Str × GObj))
  /-- An instance of a class called `tp`. `item` is `none` with no `__getitem__`. -/
  | user (tp : String) (fmt : Str → Except PyExc GObj) (toStr toRepr : Except PyExc GObj)
      (attr : Str → Except PyExc GObj) (item : Option (GKey → Except PyExc GObj))

/-- `Py_TYPE(obj)->tp_name`. -/
def GObj.tpName : GObj → String
  | .int _ => "int"
  | .bool _ => "bool"
  | .float _ => "float"
  | .complex _ _ => "complex"
  | .str _ => "str"
  | .none => "NoneType"
  | .tuple _ => "tuple"
  | .dict _ => "dict"
  | .user tp _ _ _ _ _ => tp

/-- `PyObject_Repr`. `fuel` bounds the nesting. -/
def reprG : Nat → GObj → Py Str
  | 0, _ => .error .modelFuel
  | _ + 1, .int v => longFormat v 10 false
  | _ + 1, .bool b => .ok (lit (if b then "True" else "False"))
  | _ + 1, .float x =>
    match float_repr x with
    | Option.none => .error .modelFuel
    | some s => .ok s
  | _ + 1, .complex re im =>
    match complex_repr ⟨re, im⟩ with
    | Option.none => .error .modelFuel
    | some s => .ok s
  | _ + 1, .str s => .ok (unicodeRepr s)
  | _ + 1, .none => .ok (lit "None")
  | fuel + 1, .tuple items => do
    let parts ← items.mapM (reprG fuel)
    match parts with
    | [one] => .ok (lit "(" ++ one ++ lit ",)")
    | _ => .ok (lit "(" ++ (lit ", ").intercalate parts ++ lit ")")
  | fuel + 1, .dict items => do
    let parts ← items.mapM fun kv => do
      return unicodeRepr kv.1 ++ lit ": " ++ (← reprG fuel kv.2)
    .ok (lit "{" ++ (lit ", ").intercalate parts ++ lit "}")
  | _ + 1, .user _ _ _ toRepr _ _ => do
    match ← toRepr with
    | .str s => .ok s
    | o => .error (.typeError s!"__repr__ returned non-string (type {o.tpName})")

/-- `PyObject_Str`. -/
def strG (fuel : Nat) : GObj → Py Str
  | .str s => .ok s
  | .user _ _ toStr _ _ _ => do
    match ← toStr with
    | .str s => .ok s
    | o => .error (.typeError s!"__str__ returned non-string (type {o.tpName})")
  | o => reprG fuel o

/-- `PyObject_ASCII`. -/
def asciiG (fuel : Nat) (o : GObj) : Py Str := do
  return (← reprG fuel o).flatMap asciiEscapeChar

/-- How deep a repr goes here. -/
def reprFuel : Nat := 8

/-- `object___format___impl`, Objects/typeobject.c:8503-8513. -/
def objectFormat (o : GObj) (spec : Str) : Py Str :=
  if spec.length > 0 then
    .error (.typeError s!"unsupported format string passed to {o.tpName}.__format__")
  else strG reprFuel o

/-- `int.__format__` and `bool.__format__`. -/
def intFormat (v : Int) (name : String) (shown : Str) (spec : Str) : Py Str := do
  match ← formatLongAdvanced v name spec shown with
  | some s => .ok s
  | Option.none => formatLongAsFloat v spec name

/-- `PyObject_Format`, Objects/abstract.c:853-916: `format(obj, spec)`. -/
def pyObjectFormat (o : GObj) (spec : Str) : Py Str :=
  match o, spec with
  | .str s, [] => .ok s
  | .int v, [] => longFormat v 10 false
  | .str s, _ => formatStrAdvanced s spec
  | .int v, _ => intFormat v "int" [] spec
  | .bool b, _ => intFormat (if b then 1 else 0) "bool" (lit (if b then "True" else "False")) spec
  | .float x, _ => formatFloatAdvanced x spec
  | .complex re im, _ => formatComplexAdvanced re im spec
  | .user _ fmt _ _ _ _, _ => do
    match ← fmt spec with
    | .str s => .ok s
    | r => .error (.typeError s!"__format__ must return a str, not {r.tpName}")
  | o, _ => objectFormat o spec

/-- `render_field`, unicode_format.h:500-552: the exact types go straight to their formatter. -/
def renderField (o : GObj) (spec : Str) : Py Str :=
  match o with
  | .str s => formatStrAdvanced s spec
  | .int v =>
    if spec.isEmpty then longFormat v 10 false else intFormat v "int" [] spec
  | .float x => formatFloatAdvanced x spec
  | .complex re im => formatComplexAdvanced re im spec
  | _ => pyObjectFormat o spec

/-! ## Lookups -/

/-- `get_integer`, unicode_format.h:112-141: `none` is the -1 for "not a number". The check comes
before the multiplication, so the accumulator cannot wrap. A digit past the point of overflow
raises even if a non-digit follows. -/
def fieldIntegerLoop : List Nat → Int → Py (Option Nat)
  | [], acc => .ok (some acc.toNat)
  | c :: cs, acc =>
    let digit := toDecimalDigit c
    if digit < 0 then .ok Option.none
    else if acc > (ssizeMax - digit) / 10 then
      .error (.valueError "Too many decimal digits in format string")
    else fieldIntegerLoop cs (acc * 10 + digit)

def fieldInteger (s : Str) : Py (Option Nat) :=
  if s.isEmpty then .ok Option.none else fieldIntegerLoop s 0

/-- `AttributeError`. -/
def attrError (o : GObj) (name : Str) : PyExc :=
  .named "AttributeError" s!"'{o.tpName}' object has no attribute '{toLeanString name}'"

/-- `getattr`, unicode_format.h:148-158. -/
def getattrG (o : GObj) (name : Str) : Py GObj :=
  let s := toLeanString name
  match o with
  | .int v =>
    if s == "real" || s == "numerator" then .ok (.int v)
    else if s == "imag" then .ok (.int 0)
    else if s == "denominator" then .ok (.int 1)
    else .error (attrError o name)
  | .bool b =>
    if s == "real" || s == "numerator" then .ok (.int (if b then 1 else 0))
    else if s == "imag" then .ok (.int 0)
    else if s == "denominator" then .ok (.int 1)
    else .error (attrError o name)
  | .float x =>
    if s == "real" then .ok (.float x)
    else if s == "imag" then .ok (.float (F64.zero false))
    else .error (attrError o name)
  | .complex re im =>
    if s == "real" then .ok (.float re)
    else if s == "imag" then .ok (.float im)
    else .error (attrError o name)
  | .user _ _ _ _ attr _ => attr name
  | _ => .error (attrError o name)

/-- `obj[key]`: `getitem_sequence`, `getitem_idx` and `getitem_str`, unicode_format.h:161-191. A
digit key reaches a mapping as an int. -/
def getitemG (o : GObj) (k : GKey) : Py GObj :=
  match o, k with
  | .str s, .idx n =>
    match s[n]? with
    | some c => .ok (.str [c])
    | Option.none => .error (.indexError "string index out of range")
  | .str _, .name _ => .error (.typeError "string indices must be integers, not 'str'")
  | .tuple items, .idx n =>
    match items[n]? with
    | some x => .ok x
    | Option.none => .error (.indexError "tuple index out of range")
  | .tuple _, .name _ => .error (.typeError "tuple indices must be integers or slices, not str")
  | .dict _, .idx n => .error (.keyError (toString n))
  | .dict items, .name s =>
    match items.lookup s with
    | some x => .ok x
    | Option.none => .error (.keyError (toLeanString (unicodeRepr s)))
  | .user _ _ _ _ _ (some item), k => item k
  | o, _ => .error (.typeError s!"'{o.tpName}' object is not subscriptable")

/-! ## Field names -/

/-- `AutoNumberState`. -/
inductive ANState where
  | init | auto | manual
  deriving Repr, DecidableEq

/-- What changes while a format string is processed. `kw` is the keys asked of the mapping. -/
structure FSt where
  an : ANState := .init
  n : Nat := 0
  kw : List Str := []
  deriving Repr, DecidableEq

def isFieldStop (c : Nat) : Bool := c == 91 || c == 46

/-- `autonumber_state_error`, unicode_format.h:85-105. -/
def autonumberStateError (state : ANState) (empty : Bool) : Py Unit :=
  if state == .manual then
    if empty then
      .error (.valueError "cannot switch from manual field specification to automatic field numbering")
    else .ok ()
  else if !empty then
    .error (.valueError "cannot switch from automatic field numbering to manual field specification")
  else .ok ()

/-- `field_name_split`, unicode_format.h:320-389, with `auto_number` present: first, its index,
the rest of the name, the state. -/
def fieldNameSplit (s : Str) (st : FSt) : Py (Str × Option Nat × Str × FSt) := do
  let first := s.takeWhile (fun c => !isFieldStop c)
  let rest := s.dropWhile (fun c => !isFieldStop c)
  let idx ← fieldInteger first
  let empty := first.isEmpty
  let numeric := empty || idx.isSome
  let an := if st.an == .init && numeric then (if empty then .auto else .manual) else st.an
  if numeric then autonumberStateError an empty else .ok ()
  if empty then .ok (first, some st.n, rest, { st with an, n := st.n + 1 })
  else .ok (first, idx, rest, { st with an })

/-- `_FieldNameIterator_attr`, unicode_format.h:213-238: up to `.` or `[`. -/
def attrName (s : Str) : Str × Str :=
  (s.takeWhile (fun c => !isFieldStop c), s.dropWhile (fun c => !isFieldStop c))

/-- A step of the rest of a field name. -/
inductive NameStep where
  | done
  | attr (name : Str) (rest : Str)
  | item (key : GKey) (rest : Str)
  deriving Repr, DecidableEq

/-- `FieldNameIterator_next`, unicode_format.h:274-311, with `_FieldNameIterator_item`, :240-271. -/
def fieldNameNext : Str → Py NameStep
  | [] => .ok .done
  | c :: t =>
    if c == 46 then
      let (name, rest) := attrName t
      if name.isEmpty then .error (.valueError "Empty attribute in format string")
      else .ok (.attr name rest)
    else if c == 91 then do
      let name := t.takeWhile (· != 93)
      let after := t.dropWhile (· != 93)
      if after.isEmpty then .error (.valueError "Missing ']' in format string")
      else
        let idx ← fieldInteger name
        if name.isEmpty then .error (.valueError "Empty attribute in format string")
        else
          match idx with
          | some n => .ok (.item (.idx n) after.tail)
          | Option.none => .ok (.item (.name name) after.tail)
    else .error (.valueError "Only '.' or '[' may follow ']' in format field specifier")

/-- The loop at the end of `get_field_object`, unicode_format.h:457-482. -/
def walkField : Nat → GObj → Str → Py GObj
  | 0, _, _ => .error .modelFuel
  | fuel + 1, o, rest => do
    match ← fieldNameNext rest with
    | .done => .ok o
    | .attr name r => walkField fuel (← getattrG o name) r
    | .item key r => walkField fuel (← getitemG o key) r

/-- `kwargs`: a function of the keys asked so far, the last one being this key. -/
abbrev KwMap := List Str → Py GObj

/-- The mapping of `str.format(**d)`: a plain dict. -/
def dictKw (items : List (Str × GObj)) : KwMap := fun hist =>
  let key := hist.getLastD []
  match items.lookup key with
  | some x => .ok x
  | Option.none => .error (.keyError (toLeanString (unicodeRepr key)))

/-- `get_field_object`, unicode_format.h:397-486. `args` is `none` for `format_map`, `kw` is `none`
when there are no keyword arguments. -/
def getFieldObject (input : Str) (args : Option (List GObj)) (kw : Option KwMap) (st : FSt) :
    Py (GObj × FSt) := do
  let (first, idx, rest, st) ← fieldNameSplit input st
  let (obj, st) ← match idx with
    | Option.none =>
      match kw with
      | Option.none => .error (.keyError (toLeanString (unicodeRepr first)))
      | some f =>
        let keys := st.kw ++ [first]
        .ok (← f keys, { st with kw := keys })
    | some index =>
      match args with
      | Option.none => .error (.valueError "Format string contains positional fields")
      | some items =>
        match items[index]? with
        | some x => .ok (x, st)
        | Option.none =>
          .error (.indexError s!"Replacement index {index} out of range for positional args tuple")
  return (← walkField (rest.length + 1) obj rest, st)

/-! ## The parser -/

/-- A field of a format string. `spec` is `none` when `format_spec->str` stays NULL. -/
structure MField where
  name : Str
  spec : Option Str
  conv : Nat
  expand : Bool
  deriving Repr, DecidableEq

/-- The search for the field name, unicode_format.h:572-590: the name, the character that stopped
it, what follows. A `[` skips to the `]`, so `:` and `!` are ordinary inside it. -/
def fieldNameScan : Nat → List Nat → Str → Nat → Py (Str × Nat × List Nat)
  | 0, _, _, _ => .error .modelFuel
  | _ + 1, [], acc, c => .ok (acc, c, [])
  | fuel + 1, x :: t, acc, _ =>
    if x == 123 then .error (.valueError "unexpected '{' in field name")
    else if x == 91 then
      fieldNameScan fuel (t.dropWhile (· != 93)) (acc ++ x :: t.takeWhile (· != 93)) x
    else if x == 125 || x == 58 || x == 33 then .ok (acc, x, t)
    else fieldNameScan fuel t (acc ++ [x]) x

/-- The format spec, unicode_format.h:622-641: braces nest, and any `{` asks for expansion. -/
def specScan : List Nat → Nat → Str → Bool → Py (Str × Bool × List Nat)
  | [], _, _, _ => .error (.valueError "unmatched '{' in format spec")
  | x :: t, count, acc, e =>
    if x == 123 then specScan t (count + 1) (acc ++ [x]) true
    else if x == 125 then
      if count == 1 then .ok (acc, e, t) else specScan t (count - 1) (acc ++ [x]) e
    else specScan t count (acc ++ [x]) e

/-- `parse_field`, unicode_format.h:554-650. `conv` stays 0 with no conversion, so an explicit NUL
after `!` reads as no conversion. -/
def parseField (s : List Nat) : Py (MField × List Nat) := do
  let (name, c, rest) ← fieldNameScan (s.length + 1) s [] 0
  let withSpec (conv : Nat) (r : List Nat) : Py (MField × List Nat) := do
    let (spec, expand, r') ← specScan r 1 [] false
    .ok ({ name, spec := some spec, conv, expand }, r')
  if c == 33 then
    match rest with
    | [] => .error (.valueError "end of string while looking for conversion specifier")
    | conv :: r =>
      match r with
      | [] => withSpec conv []
      | c2 :: r2 =>
        if c2 == 125 then .ok ({ name, spec := Option.none, conv, expand := false }, r2)
        else if c2 != 58 then .error (.valueError "expected ':' after conversion specifier")
        else withSpec conv r2
  else if c == 58 then withSpec 0 rest
  else if c != 125 then .error (.valueError "expected '}' before end of string")
  else .ok ({ name, spec := Option.none, conv := 0, expand := false }, rest)

def isBrace (c : Nat) : Bool := c == 123 || c == 125

/-- `MarkupIterator_next`, unicode_format.h:675-761: `none` at the end of the input, else the
literal text, the field if there is one, and what follows. -/
def markupNext (s : List Nat) : Py (Option (Str × Option MField × List Nat)) := do
  if s.isEmpty then return Option.none
  let lit0 := s.takeWhile (fun c => !isBrace c)
  match s.dropWhile (fun c => !isBrace c) with
  | [] => return some (lit0, Option.none, [])
  | c :: t =>
    match t with
    | [] =>
      if c == 125 then .error (.valueError "Single '}' encountered in format string")
      else .error (.valueError "Single '{' encountered in format string")
    | n :: r =>
      if c == 125 && c != n then .error (.valueError "Single '}' encountered in format string")
      else if c == n then return some (lit0 ++ [c], Option.none, r)
      else
        let (f, rest) ← parseField t
        return some (lit0, some f, rest)

/-! ## Rendering -/

/-- The `default:` of `do_conversion`. -/
def unknownConversion (conv : Nat) : PyExc :=
  if 32 < conv ∧ conv < 127 then .valueError s!"Unknown conversion specifier {Char.ofNat conv}"
  else .valueError s!"Unknown conversion specifier \\x{hexPlain conv}"

/-- `do_conversion`, unicode_format.h:765-791. -/
def doConversion (o : GObj) (conv : Nat) : Py GObj :=
  if conv == 114 then .str <$> reprG reprFuel o
  else if conv == 115 then .str <$> strG reprFuel o
  else if conv == 97 then .str <$> asciiG reprFuel o
  else .error (unknownConversion conv)

/-- `output_markup`, unicode_format.h:806-859: object first, then conversion, then the nested
fields of the spec, then rendering. The auto-numbering runs in that order. -/
def outputMarkup (expand : Str → FSt → Py (Str × FSt)) (args : Option (List GObj)) (kw : Option KwMap)
    (f : MField) (st : FSt) : Py (Str × FSt) := do
  let (obj, st) ← getFieldObject f.name args kw st
  let obj ← if f.conv != 0 then doConversion obj f.conv else .ok obj
  let (spec, st) ← if f.expand then expand (f.spec.getD []) st else .ok (f.spec.getD [], st)
  return (← renderField obj spec, st)

/-- `do_markup`, unicode_format.h:867-903. -/
def doMarkup (expand : Str → FSt → Py (Str × FSt)) (args : Option (List GObj)) (kw : Option KwMap) :
    Nat → List Nat → FSt → Str → Py (Str × FSt)
  | 0, _, _, _ => .error .modelFuel
  | fuel + 1, s, st, out => do
    match ← markupNext s with
    | Option.none => .ok (out, st)
    | some (literal, field, rest) =>
      match field with
      | Option.none => doMarkup expand args kw fuel rest st (out ++ literal)
      | some f =>
        let (text, st') ← outputMarkup expand args kw f st
        doMarkup expand args kw fuel rest st' (out ++ literal ++ text)

/-- `build_string`, unicode_format.h:910-934. -/
def buildString (args : Option (List GObj)) (kw : Option KwMap) : Nat → Str → FSt → Py (Str × FSt)
  | 0, _, _ => .error (.valueError "Max string recursion exceeded")
  | depth + 1, s, st => doMarkup (buildString args kw depth) args kw (s.length + 1) s st []

/-- `do_string_format`, unicode_format.h:941-956: `str.format`. -/
def doStringFormat (s : Str) (args : List GObj) (kw : Option KwMap) : Py Str := do
  let (r, _) ← buildString (some args) kw 2 s {}
  .ok r

/-- `do_string_format_map`, unicode_format.h:958-962: `str.format_map`. -/
def doStringFormatMap (s : Str) (m : KwMap) : Py Str := do
  let (r, _) ← buildString Option.none (some m) 2 s {}
  .ok r

/-! ## `_string` -/

/-- A tuple of `formatter_parser`. -/
abbrev ParserItem := Str × Option Str × Option Str × Option Str

/-- `formatteriter_next`, unicode_format.h:996-1060. A field with no spec gives an empty string,
and a NUL conversion gives `None`. -/
def parserItem (literal : Str) (field : Option MField) : ParserItem :=
  match field with
  | Option.none => (literal, Option.none, Option.none, Option.none)
  | some f =>
    (literal, some f.name, some (f.spec.getD []), if f.conv == 0 then Option.none else some [f.conv])

/-- `formatter_parser`, unicode_format.h:1103-1123, run to the end. -/
def formatterParser : Nat → List Nat → List ParserItem → Py (List ParserItem)
  | 0, _, _ => .error .modelFuel
  | fuel + 1, s, acc => do
    match ← markupNext s with
    | Option.none => .ok acc
    | some (literal, field, rest) => formatterParser fuel rest (acc ++ [parserItem literal field])

/-- `formatter_field_name_split`, unicode_format.h:1239-1284, with the iterator run to the end. With
no `auto_number`, an empty first part stays a string. -/
def fieldNameItems : Nat → Str → List (Bool × (Nat ⊕ Str)) → Py (List (Bool × (Nat ⊕ Str)))
  | 0, _, _ => .error .modelFuel
  | fuel + 1, rest, acc => do
    match ← fieldNameNext rest with
    | .done => .ok acc
    | .attr name r => fieldNameItems fuel r (acc ++ [(true, .inr name)])
    | .item (.idx n) r => fieldNameItems fuel r (acc ++ [(false, .inl n)])
    | .item (.name s) r => fieldNameItems fuel r (acc ++ [(false, .inr s)])

def formatterFieldNameSplit (s : Str) : Py ((Nat ⊕ Str) × List (Bool × (Nat ⊕ Str))) := do
  let first := s.takeWhile (fun c => !isFieldStop c)
  let rest := s.dropWhile (fun c => !isFieldStop c)
  let idx ← fieldInteger first
  let items ← fieldNameItems (rest.length + 1) rest []
  match idx with
  | some n => .ok (.inl n, items)
  | Option.none => .ok (.inr first, items)

/-- `expected str, got %s`, the first check of both `_string` functions. -/
def expectedStr (o : GObj) : PyExc := .typeError s!"expected str, got {o.tpName}"

/-- `_string.formatter_parser(o)`, run to the end. -/
def formatterParserObj : GObj → Py (List ParserItem)
  | .str s => formatterParser (s.length + 1) s []
  | o => .error (expectedStr o)

/-- `_string.formatter_field_name_split(o)`. -/
def formatterFieldNameSplitObj : GObj → Py ((Nat ⊕ Str) × List (Bool × (Nat ⊕ Str)))
  | .str s => formatterFieldNameSplit s
  | o => .error (expectedStr o)

end PyLean.UnicodeObj
