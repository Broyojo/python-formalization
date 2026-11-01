import PyLean.JsonMod.CApi

/-!
`Lib/json/tool.py`: `_colorize_json` and `main`.

`main` is modelled after `argparse`: `ToolOpts` is `parser.parse_args()`, whose
own errors are out of scope. `input` is the text the input stream yields (the
newline translation of a real file happens before it). `can_colorize`, the theme
and the behaviour of the output stream are parameters. A float reaches `dump`
through `fl`, the Python value of a `parse_float`/`parse_constant` text.
-/

namespace PyLean.JsonMod

open PyLean

/-! ### `_colorize_json`, tool.py:17-41 -/

/-- The named groups of `_color_pattern`. -/
inductive CGroup where
  | key | string | number | boolean | null
  deriving DecidableEq, Repr

/-- `_group_to_theme_color`, tool.py@3.14.7:25-31. -/
def groupColor : CGroup → String
  | .key => "definition"
  | .string => "string"
  | .number => "number"
  | .boolean => "keyword"
  | .null => "keyword"

/-- A theme section: `theme[color]` and `theme.reset`. -/
structure Theme where
  color : String → PStr
  reset : PStr

/-- `(\\.|[^"\\])*"` after the opening quote: the number of characters taken.
`.` does not match a newline. Backtracking finds nothing else: every shorter
repetition is followed by a character that is not `"`. -/
def reStrBody : PStr → Option Nat
  | [] => none
  | 34 :: _ => some 1
  | 92 :: [] => none
  | 92 :: c :: t => if c = 10 then none else (reStrBody t).map (· + 2)
  | _ :: t => (reStrBody t).map (· + 1)

/-- `[0-9\-+.Ee]`. -/
def isNumChar (c : Nat) : Bool :=
  (48 ≤ c && c ≤ 57) || c == 45 || c == 43 || c == 46 || c == 69 || c == 101

/-- The length of `[0-9\-+.Ee]*`. -/
def numCharsLen : PStr → Nat
  | c :: t => if isNumChar c then numCharsLen t + 1 else 0
  | [] => 0

def hasPrefix (s : PStr) (p : String) : Bool := s.take (cs p).length == cs p

/-- `_color_pattern.match` at the start of `s`: the group and the length. -/
def colorMatch (s : PStr) : Option (CGroup × Nat) :=
  match s with
  | 34 :: t =>
    match reStrBody t with
    | some n => if (t.drop n).head? = some 58 then some (.key, n + 1) else some (.string, n + 1)
    | none => none
  | _ =>
    if hasPrefix s "NaN" then some (.number, 3)
    else if hasPrefix s "Infinity" then some (.number, 8)
    else if hasPrefix s "-Infinity" then some (.number, 9)
    else if numCharsLen s ≠ 0 then some (.number, numCharsLen s)
    else if hasPrefix s "true" then some (.boolean, 4)
    else if hasPrefix s "false" then some (.boolean, 5)
    else if hasPrefix s "null" then some (.null, 4)
    else none

/-- `re.sub(_color_pattern, _replace_match_callback, s)`, with fuel. -/
def colorizeLoop (th : Theme) : Nat → PStr → PStr
  | 0, s => s
  | _ + 1, [] => []
  | f + 1, c :: t =>
    match colorMatch (c :: t) with
    | some (g, n) =>
      -- `f"{theme[color]}{m}{theme.reset}"`, tool.py:37-38
      th.color (groupColor g) ++ (c :: t).take n ++ th.reset ++ colorizeLoop th f ((c :: t).drop n)
    | none => c :: colorizeLoop th f t

/-- `_colorize_json(json_str, theme)`, tool.py:34-41. -/
def colorizeJson (th : Theme) (s : PStr) : PStr := colorizeLoop th (s.length + 1) s

/-! ### `main`, tool.py:44-116 -/

/-- The value of `--indent`, `--tab`, `--no-indent`. -/
inductive ToolIndent where
  | num (n : Int)
  | tab
  | none

/-- `parser.parse_args()`, tool.py@3.14.7:47-73. -/
structure ToolOpts where
  sortKeys : Bool := false
  ensureAscii : Bool := true
  jsonLines : Bool := false
  indent : ToolIndent := .num 4
  compact : Bool := false

/-- `dump_args`, tool.py:76-83. -/
def toolArgs (o : ToolOpts) : EncArgs :=
  if o.compact then
    { sortKeys := o.sortKeys, ensureAscii := o.ensureAscii, indent := .none
      separators := some (cs ",", cs ":") }
  else
    { sortKeys := o.sortKeys, ensureAscii := o.ensureAscii
      indent := match o.indent with
        | .num n => .int n
        | .tab => .str [9]
        | .none => .none }

mutual
/-- A decoded value as the object `dump` receives. -/
def JVal.toE (fl : PStr → EVal) : JVal → EVal
  | .null => .none
  | .bool b => .bool b
  | .int n => .int n
  | .str s => .str s
  | .hook _ t => fl t
  | .arr xs => .list (JVal.toEList fl xs)
  | .obj kvs => .dict (JVal.toEItems fl kvs)
def JVal.toEList (fl : PStr → EVal) : List JVal → List EVal
  | [] => []
  | x :: xs => JVal.toE fl x :: JVal.toEList fl xs
def JVal.toEItems (fl : PStr → EVal) : List (PStr × JVal) → List (EKey × EVal)
  | [] => []
  | (k, x) :: xs => (.str k, JVal.toE fl x) :: JVal.toEItems fl xs
end

/-- `infile.readlines()`. -/
def readLines : PStr → List PStr
  | [] => []
  | c :: t =>
    if c = 10 then [10] :: readLines t
    else
      match readLines t with
      | [] => [[c]]
      | l :: ls => (c :: l) :: ls

/-- What `main` does to the outside world. -/
structure ToolRes where
  /-- The text written to the output stream. -/
  out : PStr
  /-- The exception it ends with. -/
  exit : Option PyExc
  deriving DecidableEq, Repr

/-- The exceptions `except ValueError` catches here. -/
def isValueError : PyExc → Bool
  | .valueError _ => true
  | .named c _ => c == "JSONDecodeError" || c == "UnicodeEncodeError"
  | _ => false

/-- `raise SystemExit(e)`, tool.py:115-116. -/
def toolExc (e : PyExc) : PyExc := if isValueError e then .named "SystemExit" e.message else e

/-- The configuration of `main`'s environment. -/
structure ToolEnv where
  /-- `Python value of a float text. -/
  fl : PStr → EVal
  /-- `t` when `can_colorize(file=outfile)`. -/
  theme : Option Theme := none
  /-- What writing a chunk to the output stream raises. -/
  wr : PStr → Option PyExc := fun _ => none

/-- One iteration of `for obj in objs`, tool.py:105-114. -/
def toolWrite (o : ToolOpts) (env : ToolEnv) (obj : JVal) : Yield :=
  let v := obj.toE env.fl
  let a := toolArgs o
  match env.theme with
  | some th =>
    match jsonDumps dumpsC a v with
    | .error e => yRaise e
    | .ok t => dumpTo (fun _ c => env.wr c) ([colorizeJson th t, [10]], none)
  | none =>
    let y := jsonDump a (fun _ c => env.wr c) v
    match y.2 with
    | some e => (y.1, some e)
    | none =>
      match env.wr [10] with
      | some e => (y.1, some e)
      | none => (y.1 ++ [[10]], none)

/-- The lines of `--json-lines`: `objs` is a generator, so the lines before a bad
one are written. -/
def toolLines (o : ToolOpts) (env : ToolEnv) : List PStr → Yield
  | [] => ([], none)
  | l :: ls =>
    match jsonLoads loadsC {} (.str l) with
    | .error e => yRaise e
    | .ok obj => yThen (toolWrite o env obj) (toolLines o env ls)

/-- `main()` after `parser.parse_args()`. -/
def toolMain (o : ToolOpts) (env : ToolEnv) (input : PStr) : ToolRes :=
  let y : Yield :=
    if o.jsonLines then toolLines o env (readLines input)
    else
      match jsonLoad loadsC {} (.ok (.str input)) with
      | .error e => yRaise e
      | .ok obj => toolWrite o env obj
  { out := y.1.flatten, exit := y.2.map toolExc }

end PyLean.JsonMod
