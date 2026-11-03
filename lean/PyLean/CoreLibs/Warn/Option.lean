import PyLean.CoreLibs.Warn.Filters

/-!
The `-W` option parser of `Lib/_py_warnings.py` (CPython 3.15.2): `_processoptions` (:350-355),
`_setoption` (:359-406), `_getaction` (:410-416) and `_getcategory` (:420-438). `warnings`
runs `_processoptions(sys.warnoptions)` while it is imported (Lib/warnings.py:94), so an exception
that escapes it makes `import warnings` fail.

Scope:
* Strings are lists of code points. `str.strip()` and `int()`'s whitespace are Python's
  `str.isspace` (exact: the Unicode `White_Space` characters CPython lists). `int(s)` of a str is
  mirrored for the decimal digits of ASCII, Arabic-Indic, Extended Arabic-Indic, Devanagari,
  Bengali and fullwidth forms, with single underscores between digits and the 4300-digit limit.
* `__import__(module, None, None, [klass])`, `getattr(m, klass)` and `re.compile` are callbacks
  that can raise; a looked-up attribute is a class (an object id) or not a class.
* `_OptionError` is `.named "_OptionError"`; `re.PatternError` has class name `PatternError`.
-/

namespace PyLean.CoreLibs.Warn

open PyLean

/-! ## Strings -/

/-- `str.isspace` for one character (`_PyUnicode_IsWhitespace`). -/
def pySpace (c : Char) : Bool :=
  let n := c.toNat
  (9 ≤ n && n ≤ 13) || (28 ≤ n && n ≤ 32) || n == 0x85 || n == 0xA0 || n == 0x1680 ||
  (0x2000 ≤ n && n ≤ 0x200A) || n == 0x2028 || n == 0x2029 || n == 0x202F || n == 0x205F ||
  n == 0x3000

/-- `s.strip()`. -/
def pyStrip (s : List Char) : List Char :=
  ((s.dropWhile pySpace).reverse.dropWhile pySpace).reverse

/-- `s.split(':')`. -/
def splitColon : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = ':' then [] :: splitColon cs
    else match splitColon cs with
      | p :: ps => (c :: p) :: ps
      | [] => [[c]]

/-- `s.rpartition('.')` when `'.'` is in `s`: the text before the last dot and after it. -/
def rpartDot (s : List Char) : List Char × List Char :=
  let r := s.reverse
  let after := r.takeWhile (· ≠ '.')
  let before := (r.dropWhile (· ≠ '.')).drop 1
  (before.reverse, after.reverse)

/-- `re.escape(s)`: `_special_chars_map` (Lib/re/__init__.py) gets a backslash. -/
def reSpecial (c : Char) : Bool := "()[]{}?*+-|^$\\.&~# \t\n\r\x0b\x0c".toList.contains c

def reEscape : List Char → List Char
  | [] => []
  | c :: cs => if reSpecial c then '\\' :: c :: reEscape cs else c :: reEscape cs

/-- `len(s) >= 2 and s[0] == s[-1] == '/'`. -/
def slashed (s : List Char) : Bool :=
  2 ≤ s.length && s.head? == some '/' && s.getLast? == some '/'

/-- `s[1:-1]`. -/
def inner (s : List Char) : List Char := (s.drop 1).dropLast

/-- The value of a decimal digit (`Py_UNICODE_TODECIMAL`) in the blocks the model covers. -/
def decDigit (c : Char) : Option Nat :=
  let n := c.toNat
  let blk := fun (z : Nat) => if z ≤ n && n ≤ z + 9 then some (n - z) else none
  (blk 0x30).orElse fun _ => (blk 0x660).orElse fun _ => (blk 0x6F0).orElse fun _ =>
    (blk 0x966).orElse fun _ => (blk 0x9E6).orElse fun _ => blk 0xFF10

/-- Digits with single underscores between them, most significant first. -/
def digitsU : List Char → Option (List Nat)
  | [] => none
  | [c] => (decDigit c).map ([·])
  | c :: '_' :: cs => do
    let d ← decDigit c
    let ds ← digitsU cs
    return d :: ds
  | c :: cs => do
    let d ← decDigit c
    let ds ← digitsU cs
    return d :: ds

def digitsVal (ds : List Nat) : Nat := ds.foldl (fun a d => 10 * a + d) 0

/-- `int(s)` for a str, base 10: `none` when it raises `ValueError`. -/
def pyIntOfStr (s : List Char) : Option Int :=
  let t := pyStrip s
  let (neg, body) := match t with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  match digitsU body with
  | none => none
  | some ds => if ds.length > 4300 then none
    else some (if neg then -(digitsVal ds : Int) else digitsVal ds)

/-! ## The parser -/

def optErr (m : String) : PyExc := .named "_OptionError" m

def isImportErr (e : PyExc) : Bool := isA e "ImportError"

/-- An attribute `getattr` finds: a class (its object id) or something else. -/
inductive Found where
  | cls (id : Nat)
  | nonclass

structure OEnv where
  fenv : FEnv
  /-- `__import__(module, None, None, [klass])`, a module id -/
  imp : List Char → List Char → Py Nat
  /-- `getattr(m, klass)`; module 0 is `builtins` -/
  getattr : Nat → List Char → Py Found
  /-- the object id of `Warning` -/
  warning : Nat

def str' (s : List Char) : String := String.ofList s

def actionOrder : List String := ["default", "always", "all", "ignore", "module", "once", "error"]

/-- `_getaction`, :410-416: the first action name the field is a prefix of. -/
def getaction (a : List Char) : Py String :=
  if a.isEmpty then .ok "default"
  else match actionOrder.find? (fun n => a.isPrefixOf n.toList) with
    | some n => .ok n
    | none => .error (optErr s!"invalid action: {pyReprStr (str' a)}")

/-- The module of a category name, :423-431: `builtins` (module 0) without a dot, else
`__import__` of the text before the last dot, an `ImportError` becoming `_OptionError`. -/
def gcModule (E : OEnv) (category : List Char) : Py (Nat × List Char) :=
  if !category.contains '.' then .ok (0, category)
  else
    let (module, klass) := rpartDot category
    match E.imp module klass with
    | .ok m => .ok (m, klass)
    | .error e =>
      if isImportErr e then .error (optErr s!"invalid module name: {pyReprStr (str' module)}")
      else .error e

/-- `getattr(m, klass)`, :432-435, an `AttributeError` becoming `_OptionError`. -/
def gcAttr (E : OEnv) (category : List Char) (m : Nat) (klass : List Char) : Py Found :=
  match E.getattr m klass with
  | .ok o => .ok o
  | .error e =>
    if isA e "AttributeError" then
      .error (optErr s!"unknown warning category: {pyReprStr (str' category)}")
    else .error e

/-- `issubclass(cat, Warning)`, :436-438: a non-class raises `TypeError`. -/
def gcCheck (E : OEnv) (category : List Char) : Found → Py Nat
  | .nonclass => .error (.typeError "issubclass() arg 1 must be a class")
  | .cls id =>
    if E.fenv.isWarn id then .ok id
    else .error (optErr s!"invalid warning category: {pyReprStr (str' category)}")

/-- `_getcategory`, :420-438. -/
def getcategory (E : OEnv) (category : List Char) : Py Nat :=
  if category.isEmpty then .ok E.warning
  else gcModule E category >>= fun mk => gcAttr E category mk.1 mk.2 >>= gcCheck E category

def isPatternErr (e : PyExc) : Bool := e.className == "PatternError"

/-- One step of the handler of :392-404: recompile the field without flags; a `PatternError`
names the field, another exception escapes in its place, success goes on with `k`. -/
def recheck (E : FEnv) (p : List Char) (what : String) (k : PyExc) : PyExc :=
  if p.isEmpty then k
  else match E.compile (str' p) false with
    | .error e2 =>
      if isPatternErr e2 then optErr s!"invalid regular expression for {what}: {pyReprStr (str' p)}"
      else e2
    | .ok () => k

/-- The handler of :392-406: the message, then the module; with neither at fault, `raise`. -/
def patternHandler (E : FEnv) (message module : List Char) (e : PyExc) : PyExc :=
  recheck E message "message" (recheck E module "module" e)

/-- The line field, :381-389. -/
def soLineno (lineno : List Char) : Py Int :=
  if lineno.isEmpty then .ok 0
  else match pyIntOfStr lineno with
    -- `lineno = int(lineno)` has already run: the message shows the int
    | some v => if v < 0 then .error (optErr s!"invalid lineno {v}") else .ok v
    | none => .error (optErr s!"invalid lineno {pyReprStr (str' lineno)}")

/-- The message field, :371-375: `/regex/` as written, else escaped. -/
def soMessage (message : List Char) : List Char :=
  if message.isEmpty then message else if slashed message then inner message else reEscape message

/-- The module field, :376-380: `/regex/` as written, else escaped and anchored at the end. -/
def soModule (module : List Char) : List Char :=
  if module.isEmpty then module else if slashed module then inner module else reEscape module ++ ['\\', 'z']

/-- The fields of `_setoption`, :360-389: the action, the category, the message and module
patterns, and the line. -/
def soParse (E : OEnv) (arg : List Char) : Py (String × Nat × List Char × List Char × Int) :=
  let parts := splitColon arg
  if parts.length > 5 then .error (optErr s!"too many fields (max 5): {pyReprStr (str' arg)}")
  else
    let parts := (parts ++ List.replicate (5 - parts.length) []).map pyStrip
    getaction (parts.getD 0 []) >>= fun a =>
    getcategory E (parts.getD 2 []) >>= fun cat =>
    soLineno (parts.getD 4 []) >>= fun ln =>
    .ok (a, cat, soMessage (parts.getD 1 []), soModule (parts.getD 3 []), ln)

/-- The `try: _wm.filterwarnings(...) except re.PatternError if message or module else ():` of
:390-406. -/
def soInstall (E : FEnv) (a : String) (cat : Nat) (message module : List Char) (ln : Int)
    (s : FState) : Py FState :=
  match filterwarnings E (.str a) (.str (str' message)) cat (.str (str' module)) (.int ln) false s with
  | .ok s' => .ok s'
  | .error e =>
    if (!message.isEmpty || !module.isEmpty) && isPatternErr e then .error (patternHandler E message module e)
    else .error e

/-- `_setoption(arg)`, :359-406. -/
def setoption (E : OEnv) (arg : List Char) (s : FState) : Py FState := do
  let (a, cat, message, module, ln) ← soParse E arg
  soInstall E.fenv a cat message module ln s


/-- `_processoptions(args)`, :350-355: the lines it prints to `sys.stderr`, the filters it leaves,
and the exception that escapes it, if any. -/
def processoptions (E : OEnv) : List (List Char) → FState → List String × FState × Option PyExc
  | [], s => ([], s, none)
  | a :: as, s =>
    match setoption E a s with
    | .ok s' => processoptions E as s'
    | .error e =>
      if e.className == "_OptionError" then
        let r := processoptions E as s
        (s!"Invalid -W option ignored: {e.message}\n" :: r.1, r.2)
      else ([], s, some e)

end PyLean.CoreLibs.Warn
