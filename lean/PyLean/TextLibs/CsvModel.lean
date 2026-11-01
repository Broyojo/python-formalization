import PyLean.TextLibs.Bits

/-!
Model of `Modules/_csv.c` and `Lib/csv.py`, CPython 3.14.7. Characters are code points, and
`EOL` and `NOT_SET` are the same out-of-range `Py_UCS4` sentinels as in the source, so each
comparison reads as it does there. `Sniffer` uses `re` and is modelled with it.

`PyNumber_Float` on a field is modelled for ASCII text only: `float()` also accepts non-ASCII
digits and spaces, which the difftest does not generate.
-/

namespace PyLean.TextLibs.Csv

open PyLean PyLean.TextLibs

/-- `csv.Error`. -/
def csvErr (m : String) : PyExc := .named "Error" m

def NOT_SET : Nat := 2 ^ 32 - 1
def EOL : Nat := 2 ^ 32 - 2

/-- `QuoteStyle`, `Modules/_csv.c:89-92`. -/
def QUOTE_MINIMAL : Int := 0
def QUOTE_ALL : Int := 1
def QUOTE_NONNUMERIC : Int := 2
def QUOTE_NONE : Int := 3
def QUOTE_STRINGS : Int := 4
def QUOTE_NOTNULL : Int := 5

/-- `DialectObj`, `Modules/_csv.c:109-121`. -/
structure Dialect where
  doublequote : Bool
  skipinitialspace : Bool
  strict : Bool
  quoting : Int
  delimiter : Nat
  quotechar : Nat
  escapechar : Nat
  lineterminator : List Nat
  deriving Repr, DecidableEq, Inhabited

/-- A Python object passed as a dialect parameter. -/
inductive Obj where
  | str (cps : List Nat)
  | none
  | int (n : Int)
  /-- A `bool`, which is an `int` subclass but not `PyLong_CheckExact`. -/
  | bool (b : Bool)
  /-- Anything else, by type name and truth value. -/
  | other (ty : String) (truth : Bool)
  deriving Repr, DecidableEq, Inhabited

def Obj.tyName : Obj → String
  | .str _ => "str"
  | .none => "NoneType"
  | .int _ => "int"
  | .bool _ => "bool"
  | .other t _ => t

/-- `PyObject_IsTrue`. -/
def Obj.truth : Obj → Bool
  | .str c => !c.isEmpty
  | .none => false
  | .int n => n != 0
  | .bool b => b
  | .other _ t => t

/-- `_set_bool`, `Modules/_csv.c:217-229`. -/
def setBool (src : Option Obj) (dflt : Bool) : Bool :=
  match src with
  | Option.none => dflt
  | some o => o.truth

/-- `_set_int`, `Modules/_csv.c:231-250`. -/
def setInt (name : String) (src : Option Obj) (dflt : Int) : Py Int :=
  match src with
  | Option.none => .ok dflt
  | some (.int n) =>
    if n < -(2 ^ 31) ∨ n > 2 ^ 31 - 1 then
      .error (.overflowError "Python int too large to convert to C int")
    else .ok n
  | some o => .error (.typeError s!"\"{name}\" must be an integer, not {o.tyName}")

/-- `_set_char_or_none`, `Modules/_csv.c:252-283`. -/
def setCharOrNone (name : String) (src : Option Obj) (dflt : Nat) : Py Nat :=
  match src with
  | Option.none => .ok dflt
  | some .none => .ok NOT_SET
  | some (.str [c]) => .ok c
  | some (.str s) =>
    .error (.typeError s!"\"{name}\" must be a unicode character or None, not a string of length {s.length}")
  | some o => .error (.typeError s!"\"{name}\" must be a unicode character or None, not {o.tyName}")

/-- `_set_char`, `Modules/_csv.c:285-313`. -/
def setChar (name : String) (src : Option Obj) (dflt : Nat) : Py Nat :=
  match src with
  | Option.none => .ok dflt
  | some (.str [c]) => .ok c
  | some (.str s) =>
    .error (.typeError s!"\"{name}\" must be a unicode character, not a string of length {s.length}")
  | some o => .error (.typeError s!"\"{name}\" must be a unicode character, not {o.tyName}")

/-- `_set_str`, `Modules/_csv.c:315-333`. -/
def setStr (name : String) (src : Option Obj) (dflt : List Nat) : Py (List Nat) :=
  match src with
  | Option.none => .ok dflt
  | some (.str s) => .ok s
  | some o => .error (.typeError s!"\"{name}\" must be a string, not {o.tyName}")

/-- `dialect_check_quoting`, `Modules/_csv.c:335-346`. -/
def checkQuoting (q : Int) : Py Unit :=
  if 0 ≤ q ∧ q ≤ 5 then .ok () else .error (.typeError "bad \"quoting\" value")

/-- `dialect_check_char`, `Modules/_csv.c:348-363`. -/
def checkChar (name : String) (c : Nat) (lt : List Nat) (allowspace : Bool) : Py Unit :=
  if c = 13 ∨ c = 10 ∨ (c = 32 ∧ !allowspace) then .error (.valueError s!"bad {name} value")
  else if lt.contains c then .error (.valueError s!"bad {name} or lineterminator value")
  else .ok ()

/-- `dialect_check_chars`, `Modules/_csv.c:365-373`. -/
def checkChars (n1 n2 : String) (c1 c2 : Nat) : Py Unit :=
  if c1 = c2 ∧ c1 ≠ NOT_SET then .error (.valueError s!"bad {n1} or {n2} value") else .ok ()

/-- The keyword arguments of `dialect_new`. -/
structure DArgs where
  delimiter : Option Obj := Option.none
  doublequote : Option Obj := Option.none
  escapechar : Option Obj := Option.none
  lineterminator : Option Obj := Option.none
  quotechar : Option Obj := Option.none
  quoting : Option Obj := Option.none
  skipinitialspace : Option Obj := Option.none
  strict : Option Obj := Option.none
  deriving Repr, DecidableEq, Inhabited

/-- Validation and conversion, `Modules/_csv.c:527-560`, in that order. -/
def dialectBuild (a : DArgs) : Py Dialect := do
  let delimiter ← setChar "delimiter" a.delimiter 44
  let doublequote := setBool a.doublequote true
  let escapechar ← setCharOrNone "escapechar" a.escapechar NOT_SET
  let lineterminator ← setStr "lineterminator" a.lineterminator [13, 10]
  let quotechar ← setCharOrNone "quotechar" a.quotechar 34
  let quoting ← setInt "quoting" a.quoting QUOTE_MINIMAL
  let skipinitialspace := setBool a.skipinitialspace false
  let strict := setBool a.strict false
  checkQuoting quoting
  let quoting := if a.quotechar = some .none ∧ a.quoting = Option.none then QUOTE_NONE else quoting
  let _ ← (if quoting ≠ QUOTE_NONE ∧ quotechar = NOT_SET then
      (Except.error (.typeError "quotechar must be set if quoting enabled") : Py Unit)
    else .ok ())
  checkChar "delimiter" delimiter lineterminator true
  checkChar "escapechar" escapechar lineterminator (!skipinitialspace)
  checkChar "quotechar" quotechar lineterminator (!skipinitialspace)
  checkChars "delimiter" "escapechar" delimiter escapechar
  checkChars "delimiter" "quotechar" delimiter quotechar
  checkChars "escapechar" "quotechar" escapechar quotechar
  return { doublequote, skipinitialspace, strict, quoting, delimiter, quotechar, escapechar,
           lineterminator }

/-- `get_char_or_None`, `Modules/_csv.c:172-180`. -/
def getCharOrNone (c : Nat) : Obj := if c = NOT_SET then .none else .str [c]

/-- The attributes `DIALECT_GETATTR` copies from a dialect, `Modules/_csv.c:504-519`. -/
def dialectAttrs (d : Dialect) (a : DArgs) : DArgs :=
  { delimiter := a.delimiter <|> some (.str [d.delimiter])
    doublequote := a.doublequote <|> some (.bool d.doublequote)
    escapechar := a.escapechar <|> some (getCharOrNone d.escapechar)
    lineterminator := a.lineterminator <|> some (.str d.lineterminator)
    quotechar := a.quotechar <|> some (getCharOrNone d.quotechar)
    quoting := a.quoting <|> some (.int d.quoting)
    skipinitialspace := a.skipinitialspace <|> some (.bool d.skipinitialspace)
    strict := a.strict <|> some (.bool d.strict) }

abbrev Registry := List (List Nat × Dialect)

/-- `get_dialect_from_registry`, `Modules/_csv.c:162-170`. -/
def registryGet (r : Registry) (name : List Nat) : Py Dialect :=
  match r.lookup name with
  | some d => .ok d
  | Option.none => .error (csvErr "unknown dialect")

/-- The `dialect` argument of `dialect_new`. -/
inductive DSrc where
  | absent
  | name (s : List Nat)
  | dialect (d : Dialect)
  deriving Repr, DecidableEq, Inhabited

/-- `dialect_new`, `Modules/_csv.c:434-575`. -/
def dialectNew (r : Registry) (src : DSrc) (a : DArgs) : Py Dialect := do
  let d? ← match src with
    | .absent => pure Option.none
    | .name s => some <$> registryGet r s
    | .dialect d => pure (some d)
  match d? with
  | Option.none => dialectBuild a
  | some d =>
    -- "Can we reuse this instance?"
    if a = {} then return d
    dialectBuild (dialectAttrs d a)

def strToList (s : String) : List Nat := s.toList.map Char.toNat

/-- `Dialect_reduce`, `Modules/_csv.c:582-587`. -/
def dialectReduce : Py Unit := .error (.typeError "cannot pickle 'Dialect' instances")

/-- `Dialect._validate`, `Lib/csv.py:111-116`: `_Dialect(self)`, with `TypeError` re-raised as
`csv.Error`. `csv.Dialect.__init__`, `Lib/csv.py:106-109`, only calls this. -/
def dialectValidate (a : DArgs) : Py Unit :=
  match dialectBuild a with
  | .ok _ => .ok ()
  | .error (.typeError m) => .error (csvErr m)
  | .error e => .error e

/-- `excel`, `excel_tab` and `unix_dialect`, `Lib/csv.py:118-141`. -/
def excel : Dialect := ⟨true, false, false, QUOTE_MINIMAL, 44, 34, NOT_SET, [13, 10]⟩
def excelTab : Dialect := { excel with delimiter := 9 }
def unixDialect : Dialect := ⟨true, false, false, QUOTE_ALL, 44, 34, NOT_SET, [10]⟩

def initialRegistry : Registry :=
  [(strToList "excel", excel), (strToList "excel-tab", excelTab), (strToList "unix", unixDialect)]

/-- `csv_register_dialect`, `Modules/_csv.c:1618-1641`. -/
def registerDialect (r : Registry) (name : List Nat) (src : DSrc) (a : DArgs) : Py Registry := do
  let d ← dialectNew r src a
  return if (r.lookup name).isSome then r.map (fun p => if p.1 = name then (name, d) else p)
         else r ++ [(name, d)]

/-- `_csv_unregister_dialect_impl`, `Modules/_csv.c:1652-1666`. -/
def unregisterDialect (r : Registry) (name : List Nat) : Py Registry :=
  if (r.lookup name).isSome then .ok (r.filter (·.1 != name))
  else .error (csvErr "unknown dialect")

/-- `_csv_list_dialects_impl`, `Modules/_csv.c:1611-1616`. -/
def listDialects (r : Registry) : List (List Nat) := r.map (·.1)

/-- `_csv_field_size_limit_impl`, `Modules/_csv.c:1694-1713`: the old limit and the new one. -/
def fieldSizeLimit (cur : Int) (new? : Option Obj) : Py (Int × Int) :=
  match new? with
  | Option.none => .ok (cur, cur)
  | some (.int n) =>
    if n < -(2 ^ 63) ∨ n > 2 ^ 63 - 1 then
      .error (.overflowError "Python int too large to convert to C ssize_t")
    else .ok (cur, n)
  | some _ => .error (.typeError "limit must be an integer")

/-! ### `float()` on ASCII text -/

def isAsciiSpace (c : Nat) : Bool :=
  c == 32 || (9 ≤ c && c ≤ 13) || (28 ≤ c && c ≤ 31)

def isDig (c : Nat) : Bool := 48 ≤ c && c ≤ 57

/-- A digit run with Python's underscore rule: `_` only between digits. -/
def digitRun : List Nat → Option (List Nat × List Nat)
  | [] => Option.none
  | c :: r =>
    if !isDig c then Option.none
    else
      let rec go : List Nat → List Nat → List Nat × List Nat
        | acc, 95 :: d :: t => if isDig d then go (d :: acc) t else (acc.reverse, 95 :: d :: t)
        | acc, d :: t => if isDig d then go (d :: acc) t else (acc.reverse, d :: t)
        | acc, [] => (acc.reverse, [])
      termination_by _ s => s.length
      some (go [c] r)

def digitsVal (d : List Nat) : Nat := d.foldl (fun x c => x * 10 + (c - 48)) 0

/-- `sign * n * 10 ^ k` as a double, nearest-even, overflowing to infinity. -/
def decToBits (sign n : Nat) (k : Int) : Nat :=
  if n = 0 then sign * 2 ^ 63
  else if k ≥ 0 then
    if k > 400 then f64.infBits sign
    else (f64.encodeRounded sign (n * 10 ^ k.toNat) 0).getD (f64.infBits sign)
  else
    let j := (-k).toNat
    if j > 400 + (Nat.log2 n) then sign * 2 ^ 63
    else
      let s := 4 * j + 64
      let d := 10 ^ j
      let q := n * 2 ^ s / d
      let q' := if n * 2 ^ s % d ≠ 0 then q ||| 1 else q
      (f64.encodeRounded sign q' (-(s : Int))).getD (f64.infBits sign)

def lowerAscii (s : List Nat) : List Nat := s.map fun c => if 65 ≤ c ∧ c ≤ 90 then c + 32 else c

/-- The mantissa and exponent of a decimal literal; `none` if malformed. -/
def parseDec (s : List Nat) : Option (Nat × Int) := do
  let (ip, r) := match digitRun s with
    | some x => x
    | Option.none => ([], s)
  let (fp, r, hadDot) ← match r with
    | 46 :: t =>
      match digitRun t with
      | some (d, u) => some (d, u, true)
      | Option.none => some ([], t, true)
    | _ => some ([], r, false)
  if ip.isEmpty && fp.isEmpty then Option.none
  let _ := hadDot
  let (e, r) ← match r with
    | 101 :: t | 69 :: t =>
      let (neg, u) := match t with
        | 43 :: v => (false, v)
        | 45 :: v => (true, v)
        | v => (false, v)
      match digitRun u with
      | some (d, v) =>
        let x : Int := digitsVal d
        some ((if neg then -x else x), v)
      | Option.none => Option.none
    | _ => some (0, r)
  if !r.isEmpty then Option.none
  return (digitsVal (ip ++ fp), e - fp.length)

/-- `float(text)` for ASCII text: the bit pattern, or `none` for `ValueError`. -/
def floatOf (text : List Nat) : Option Nat :=
  let t := text.dropWhile isAsciiSpace
  let t := (t.reverse.dropWhile isAsciiSpace).reverse
  let (sign, b) := match t with
    | 45 :: r => (1, r)
    | 43 :: r => (0, r)
    | r => (0, r)
  let l := lowerAscii b
  if l == strToList "inf" || l == strToList "infinity" then some (f64.infBits sign)
  else if l == strToList "nan" then some (f64.infBits sign + 2 ^ 51)
  else
    match parseDec b with
    | some (n, k) => some (decToBits sign n k)
    | Option.none => Option.none

/-! ### Reader -/

/-- `ParserState`, `Modules/_csv.c:83-87`. -/
inductive PState where
  | START_RECORD | START_FIELD | ESCAPED_CHAR | IN_FIELD | IN_QUOTED_FIELD
  | ESCAPE_IN_QUOTED_FIELD | QUOTE_IN_QUOTED_FIELD | EAT_CRNL | AFTER_ESCAPED_CRNL
  deriving Repr, DecidableEq, Inhabited

/-- What a parsed field is. -/
inductive Field where
  | str (cps : List Nat)
  | none
  | float (bits : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- The mutable part of `ReaderObj`, `Modules/_csv.c:123-137`. -/
structure RSt where
  fields : List Field := []
  state : PState := .START_RECORD
  field : List Nat := []
  unquoted : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- `parse_save_field`, `Modules/_csv.c:657-694`. -/
def parseSaveField (d : Dialect) (s : RSt) : Py RSt :=
  let q := d.quoting
  if s.unquoted ∧ s.field.isEmpty ∧ (q = QUOTE_NOTNULL ∨ q = QUOTE_STRINGS) then
    .ok { s with fields := s.fields ++ [.none] }
  else if s.unquoted ∧ !s.field.isEmpty ∧ (q = QUOTE_NONNUMERIC ∨ q = QUOTE_STRINGS) then
    match floatOf s.field with
    | some b => .ok { s with fields := s.fields ++ [.float b], field := [] }
    | Option.none => .error (.valueError "~could not convert string to float")
  else .ok { s with fields := s.fields ++ [.str s.field], field := [] }

/-- `parse_add_char`, `Modules/_csv.c:713-727`. -/
def parseAddChar (limit : Int) (s : RSt) (c : Nat) : Py RSt :=
  if (s.field.length : Int) ≥ limit then
    .error (csvErr s!"field larger than field limit ({limit})")
  else .ok { s with field := s.field ++ [c] }

def isNl (c : Nat) : Bool := c == 10 || c == 13

/-- `IN_FIELD`, `Modules/_csv.c:801-824`, shared with `AFTER_ESCAPED_CRNL`. -/
def inFieldStep (d : Dialect) (limit : Int) (s : RSt) (c : Nat) : Py RSt := do
  if isNl c || c == EOL then
    let s ← parseSaveField d s
    return { s with state := if c = EOL then .START_RECORD else .EAT_CRNL }
  else if c = d.escapechar then return { s with state := .ESCAPED_CHAR }
  else if c = d.delimiter then
    let s ← parseSaveField d s
    return { s with state := .START_FIELD }
  else parseAddChar limit s c

/-- `START_FIELD`, `Modules/_csv.c:747-780`. -/
def startFieldStep (d : Dialect) (limit : Int) (s0 : RSt) (c : Nat) : Py RSt := do
  let s := { s0 with unquoted := true }
  if isNl c || c == EOL then
    let s ← parseSaveField d s
    return { s with state := if c = EOL then .START_RECORD else .EAT_CRNL }
  else if c = d.quotechar ∧ d.quoting ≠ QUOTE_NONE then
    return { s with unquoted := false, state := .IN_QUOTED_FIELD }
  else if c = d.escapechar then return { s with state := .ESCAPED_CHAR }
  else if c = 32 ∧ d.skipinitialspace then return s
  else if c = d.delimiter then parseSaveField d s
  else
    let s ← parseAddChar limit s c
    return { s with state := .IN_FIELD }

/-- `parse_process_char`, `Modules/_csv.c:729-910`. -/
def parseProcessChar (d : Dialect) (limit : Int) (s : RSt) (c : Nat) : Py RSt :=
  match s.state with
  | .START_RECORD =>
    if c = EOL then .ok s
    else if isNl c then .ok { s with state := .EAT_CRNL }
    else startFieldStep d limit { s with state := .START_FIELD } c
  | .START_FIELD => startFieldStep d limit s c
  | .ESCAPED_CHAR =>
    if isNl c then do
      let s ← parseAddChar limit s c
      return { s with state := .AFTER_ESCAPED_CRNL }
    else do
      let s ← parseAddChar limit s (if c = EOL then 10 else c)
      return { s with state := .IN_FIELD }
  | .AFTER_ESCAPED_CRNL => if c = EOL then .ok s else inFieldStep d limit s c
  | .IN_FIELD => inFieldStep d limit s c
  | .IN_QUOTED_FIELD =>
    if c = EOL then .ok s
    else if c = d.escapechar then .ok { s with state := .ESCAPE_IN_QUOTED_FIELD }
    else if c = d.quotechar ∧ d.quoting ≠ QUOTE_NONE then
      if d.doublequote then .ok { s with state := .QUOTE_IN_QUOTED_FIELD }
      else .ok { s with state := .IN_FIELD }
    else parseAddChar limit s c
  | .ESCAPE_IN_QUOTED_FIELD => do
    let s ← parseAddChar limit s (if c = EOL then 10 else c)
    return { s with state := .IN_QUOTED_FIELD }
  | .QUOTE_IN_QUOTED_FIELD =>
    if d.quoting ≠ QUOTE_NONE ∧ c = d.quotechar then do
      let s ← parseAddChar limit s c
      return { s with state := .IN_QUOTED_FIELD }
    else if c = d.delimiter then do
      let s ← parseSaveField d s
      return { s with state := .START_FIELD }
    else if isNl c || c == EOL then do
      let s ← parseSaveField d s
      return { s with state := if c = EOL then .START_RECORD else .EAT_CRNL }
    else if !d.strict then do
      let s ← parseAddChar limit s c
      return { s with state := .IN_FIELD }
    else
      .error (csvErr
        s!"'{String.singleton (Char.ofNat d.delimiter)}' expected after '{String.singleton (Char.ofNat d.quotechar)}'")
  | .EAT_CRNL =>
    if isNl c then .ok s
    else if c = EOL then .ok { s with state := .START_RECORD }
    else .error (csvErr
      "new-line character seen in unquoted field - do you need to open the file with newline=''?")

/-- The `while (linelen--)` loop and the final `EOL`, `Modules/_csv.c:979-989`. -/
def parseLine (d : Dialect) (limit : Int) (s : RSt) (line : List Nat) : Py RSt := do
  let s ← line.foldlM (parseProcessChar d limit) s
  parseProcessChar d limit s EOL

/-- One input item. -/
inductive Line where
  | str (cps : List Nat)
  /-- An object of another type, by its type name. -/
  | notStr (ty : String)
  deriving Repr, DecidableEq, Inhabited

/-- The `do ... while` of `Reader_iternext_lock_held`, `Modules/_csv.c:944-990`. The result is
`none` for the iterator's end, the row, the unread lines and the number of lines read.
A failed read consumes the line it failed on. -/
def readerLoop (d : Dialect) (limit : Int) : (lines : List Line) → (s : RSt) → (n : Nat) →
    (Py (Option (List Field))) × List Line × Nat
  | [], s, n =>
    if !s.field.isEmpty ∨ s.state = .IN_QUOTED_FIELD then
      if d.strict then (.error (csvErr "unexpected end of data"), [], n)
      else
        match parseSaveField d s with
        | .ok s => (.ok (some s.fields), [], n)
        | .error e => (.error e, [], n)
    else (.ok Option.none, [], n)
  | .notStr t :: rest, _, n =>
    (.error (csvErr s!"iterator should return strings, not {t} (the file should be opened in text mode)"),
      rest, n)
  | .str l :: rest, s, n =>
    match parseLine d limit s l with
    | .error e => (.error e, rest, n + 1)
    | .ok s' =>
      if s'.state = .START_RECORD then (.ok (some s'.fields), rest, n + 1)
      else readerLoop d limit rest s' (n + 1)

/-- A whole iteration: the rows, and how it ended. `fuel` bounds the rows. -/
def readAll (d : Dialect) (limit : Int) : (fuel : Nat) → List Line → (n : Nat) →
    List (List Field) × Option PyExc × Nat
  | 0, _, n => ([], some .modelFuel, n)
  | fuel + 1, lines, n =>
    match readerLoop d limit lines {} n with
    | (.error e, _, n') => ([], some e, n')
    | (.ok Option.none, _, n') => ([], Option.none, n')
    | (.ok (some row), rest, n') =>
      let (rows, e, n'') := readAll d limit fuel rest n'
      (row :: rows, e, n'')

/-! ### Writer -/

/-- One item of a row: `text` is `str(field)`, and `num` is `PyNumber_Check(field)`. -/
inductive WField where
  | str (cps : List Nat)
  | none
  | other (text : List Nat) (num : Bool)
  deriving Repr, DecidableEq, Inhabited

/-- One character of `join_append_data`, `Modules/_csv.c:1183-1220`: the prefix it emits
before the character, whether the field must now be quoted, or the missing-escape error. -/
def joinChar (d : Dialect) (c : Nat) : Py (List Nat × Bool) :=
  if c = d.delimiter ∨ c = d.escapechar ∨ c = d.quotechar ∨ c = 10 ∨ c = 13 ∨
      d.lineterminator.contains c then
    let (pre, want, quoted) :=
      if d.quoting = QUOTE_NONE then ([], true, false)
      else
        let (pre, want) :=
          if c = d.quotechar then
            if d.doublequote then ([d.quotechar], false) else ([], true)
          else if c = d.escapechar then ([], true)
          else ([], false)
        (pre, want, !want)
    if want then
      if d.escapechar = NOT_SET then .error (csvErr "need to escape, but no escapechar set")
      else .ok (pre ++ [d.escapechar], quoted)
    else .ok (pre, quoted)
  else .ok ([], false)

/-- The field text with its escapes, and the final `*quoted`. -/
def joinField (d : Dialect) : List Nat → Bool → Py (List Nat × Bool)
  | [], q => .ok ([], q)
  | c :: cs, q => do
    let (pre, q1) ← joinChar d c
    let (rest, q2) ← joinField d cs (q || q1)
    return (pre ++ [c] ++ rest, q2)

/-- `join_append`, `Modules/_csv.c:1259-1300`, with both `join_append_data` phases. `field` is
`none` for the `NULL` field. -/
def joinAppend (d : Dialect) (buf : List Nat) (numFields : Nat) (field : Option (List Nat))
    (quoted : Bool) : Py (List Nat × Nat) := do
  let text := field.getD []
  let quoted ←
    if text.isEmpty ∧ d.delimiter = 32 ∧ d.skipinitialspace then
      if d.quoting = QUOTE_NONE ∨
          (field = Option.none ∧ (d.quoting = QUOTE_STRINGS ∨ d.quoting = QUOTE_NOTNULL)) then
        Except.error (csvErr "empty field must be quoted if delimiter is a space and skipinitialspace is true")
      else pure true
    else pure quoted
  let (body, q) ← joinField d text quoted
  let sep := if numFields > 0 then [d.delimiter] else []
  let open_ := if q then [d.quotechar] else []
  return (buf ++ sep ++ open_ ++ body ++ open_, numFields + 1)

/-- The per-field `quoted` of `csv_writerow_lock_held`, `Modules/_csv.c:1351-1367`. -/
def initialQuoted (d : Dialect) (f : WField) : Bool :=
  if d.quoting = QUOTE_NONNUMERIC then
    match f with
    | .other _ n => !n
    | _ => true
  else if d.quoting = QUOTE_ALL then true
  else if d.quoting = QUOTE_STRINGS then
    match f with
    | .str _ => true
    | _ => false
  else if d.quoting = QUOTE_NOTNULL then f != .none
  else false

/-- The field loop of `csv_writerow_lock_held`, `Modules/_csv.c:1347-1394`. -/
def writerowLoop (d : Dialect) : List WField → List Nat → Nat → Bool → Py (List Nat × Nat × Bool)
  | [], buf, n, nf => .ok (buf, n, nf)
  | f :: fs, buf, n, _ => do
    let text := match f with
      | .str s => some s
      | .none => Option.none
      | .other t _ => some t
    let (buf, n) ← joinAppend d buf n text (initialQuoted d f)
    writerowLoop d fs buf n (f == .none)

/-- `csv_writerow_lock_held`, `Modules/_csv.c:1326-1428`: the text written. -/
def writerow (d : Dialect) (row : List WField) : Py (List Nat) := do
  let (buf, n, nullField) ← writerowLoop d row [] 0 false
  let buf ←
    if n > 0 ∧ buf.isEmpty then
      if d.quoting = QUOTE_NONE ∨
          (nullField ∧ (d.quoting = QUOTE_STRINGS ∨ d.quoting = QUOTE_NOTNULL)) then
        Except.error (csvErr "single empty field record must be quoted")
      else
        let r ← joinAppend d buf (n - 1) Option.none true
        pure r.1
    else pure buf
  return buf ++ d.lineterminator

/-- `csv_writerows`, `Modules/_csv.c:1454-1477`: rows before a failure stay written. -/
def writerows (d : Dialect) : List (List WField) → List Nat × Option PyExc
  | [] => ([], Option.none)
  | r :: rs =>
    match writerow d r with
    | .error e => ([], some e)
    | .ok t =>
      let (out, e) := writerows d rs
      (t ++ out, e)

/-! ### `Lib/csv.py` -/

/-- A `DictReader` value: a string list for `restkey`, a field or `restval` otherwise. -/
inductive DVal where
  | field (f : Field)
  | rest (fs : List Field)
  /-- `restval`, which defaults to `None`. -/
  | restval
  deriving Repr, DecidableEq, Inhabited

/-- `dict(zip(...))` with later equal keys replacing the value in place. -/
def dictSet {α : Type} [DecidableEq α] (d : List (Option (List Nat) × α)) (k : Option (List Nat))
    (v : α) : List (Option (List Nat) × α) :=
  if (d.lookup k).isSome then d.map (fun p => if p.1 = k then (k, v) else p) else d ++ [(k, v)]

/-- The row-to-dict part of `DictReader.__next__`, `Lib/csv.py:185-193`. `restkey` is `none` by
default, which is what the key `None` means. -/
def dictRow (names : List (List Nat)) (row : List Field) (restkey : Option (List Nat)) :
    List (Option (List Nat) × DVal) :=
  let d0 := (names.zip row).foldl (fun d p => dictSet d (some p.1) (DVal.field p.2)) []
  let lf := names.length
  let lr := row.length
  if lf < lr then dictSet d0 restkey (DVal.rest (row.drop lf))
  else if lf > lr then (names.drop lr).foldl (fun d k => dictSet d (some k) DVal.restval) d0
  else d0

/-- `DictReader`, `Lib/csv.py:144-193`, driven to the end: `fieldnames` is the names0 list or the
first row. Blank rows are skipped by the `while row == []`. -/
def dictRead (d : Dialect) (limit : Int) (names0 : Option (List (List Nat))) (lines : List Line)
    (restkey : Option (List Nat)) :
    List (List (Option (List Nat) × DVal)) × Option PyExc :=
  let (rows, e, _) := readAll d limit (lines.length + 1) lines 0
  let toNames (r : List Field) : List (List Nat) :=
    r.map fun f => match f with
      | .str s => s
      | _ => []
  match names0, rows with
  | some names, rows => ((rows.filter (· != [])).map (dictRow names · restkey), e)
  | Option.none, [] => ([], e)
  | Option.none, h :: t => ((t.filter (· != [])).map (dictRow (toNames h) · restkey), e)

/-- `DictWriter._dict_to_list`, `Lib/csv.py:216-222`, with `extrasaction` as `raises`. -/
def dictToList (names : List (List Nat)) (restval : WField) (raises : Bool)
    (rowdict : List (List Nat × WField)) : Py (List WField) :=
  if raises ∧ rowdict.any (fun p => !names.contains p.1) then
    .error (.valueError "~dict contains fields not in fieldnames")
  else .ok (names.map fun k => (rowdict.lookup k).getD restval)

/-- `DictWriter.__init__`'s check of `extrasaction`, `Lib/csv.py:205-208`; the result is
whether it is `'raise'`. -/
def extrasactionCheck (s : List Nat) : Py Bool :=
  let l := lowerAscii s
  if l == strToList "raise" then .ok true
  else if l == strToList "ignore" then .ok false
  else .error (.valueError "~extrasaction must be 'raise' or 'ignore'")

/-- `DictWriter.writerow`, `Lib/csv.py:224-225`. -/
def dictWriterow (d : Dialect) (names : List (List Nat)) (restval : WField) (raises : Bool)
    (rowdict : List (List Nat × WField)) : Py (List Nat) := do
  writerow d (← dictToList names restval raises rowdict)

/-- `DictWriter.writerows`, `Lib/csv.py:227-228`, without its `map` being consumed lazily: a row
that fails stops the writing, as in `writerows`. -/
def dictWriterows (d : Dialect) (names : List (List Nat)) (restval : WField) (raises : Bool) :
    List (List (List Nat × WField)) → List Nat × Option PyExc
  | [] => ([], Option.none)
  | r :: rs =>
    match dictWriterow d names restval raises r with
    | .error e => ([], some e)
    | .ok t =>
      let (out, e) := dictWriterows d names restval raises rs
      (t ++ out, e)

/-- `DictWriter.writeheader`, `Lib/csv.py:212-214`. -/
def writeheader (d : Dialect) (names : List (List Nat)) : Py (List Nat) :=
  dictWriterow d names (.str []) true (names.map fun n => (n, WField.str n))

end PyLean.TextLibs.Csv
