import PyLean.Core

/-!
`warnings.warn_explicit`, both twins: the C one, Python/_warnings.c (`warnings_warn_explicit_impl`
:1314-1349, `warn_explicit` :797-922, `get_filter` :541-596, `get_default_action` :430-455,
`filter_search` :460-538, `check_matched` :176-214, `already_warned` :600-649, `update_registry`
:652-666), and the Python one, Lib/_py_warnings.py:556-625.

Scope:
* A warning is its text and its category; a category is a class id, and `issubclass` is an
  `Env` callback that can raise. Building the message object (`str(message)` for a Warning,
  `category(message)` otherwise) is a callback of the call that can raise.
* The message is a Warning instance (its type the category) or another object (a str or a str
  subclass with no `__str__` of its own). C tests it with the exact `PyObject_TypeCheck` and takes
  `Py_TYPE`; Python's `isinstance(message, Warning)` and `message.__class__` read `__class__`
  (`ClsV`), which a class can override to lie or raise. Each read gives the same outcome; a
  Warning instance whose `__class__` is not a class is out of scope.
* The module attributes (`defaultaction`, `onceregistry`, `_showwarnmsg`, `WarningMessage`) can be
  there, deleted, or deleted with a module `__getattr__` that raises (`DfltV.raises`, ...): C's
  `PyObject_GetOptionalAttr` clears an exception whose class is under `AttributeError` (by the
  class relation) and propagates any other; Python's `_wm.x` propagates either. `_wm._lock`,
  `_wm._filters_version` and `_wm._get_filters` are there. `sys.modules['warnings']` is the
  `warnings` module for the lookups without import; C's `PyImport_Import` of `warnings` for
  `_showwarnmsg` is `Env.importW` (`sys.modules['warnings'] = None` makes it raise
  `ModuleNotFoundError`, a `builtins.__import__` hook can raise anything). With
  `sys.modules['warnings']` `None`, C's other lookups find nothing and use the values C read last;
  the model takes those to be the attributes' current values (they are when C read them after
  they last changed), and a module `__getattr__` together with it is out of scope.
* A filters-list item is a 5-tuple, a 5-element list (C refuses it, Python unpacks it), or
  something else (C refuses it; Python's unpacking raises what the call gives). Its action is a
  str, another hashable object, or an unhashable one; its message and module patterns are
  compiled regexes (callbacks, C or Python code, that can raise) or plain strs (what C's internal
  default filters hold); its line is an int or another object.
* The filters C searches are `warnings.filters` or the context's `_filters` (`WCfg.ctx`), a list or
  a tuple (`WCfg.tuple`); Python iterates either. `defaultaction` is a value or deleted;
  `onceregistry` a dict, another object, or deleted (C keeps what it read last of each).
* A registry is `None`, a dict, another mapping (C refuses it, Python uses it), or some other
  object. Its values are ints, each with whether it is an exact int (C stores `True`; a
  `'version'` that is a bool or an int subclass is not exact).
* `lineno` is an int, or another object that Python's `int()` converts (or fails on) and C's `int`
  converter refuses. `module` is omitted, `None`, a str, or another object whose regex match raises.
  `module_globals` is `None`, a dict, or another object: C checks it and runs `get_source_line`
  first; Python passes it to `linecache.getlines` when the warning is shown. Both outcomes are
  callbacks of the call.
* `_match_filename` is one `Env` callback: the C code calls the Python function.
* The show step (`ShowA`): `WarningMessage(...)` and the call of `_showwarnmsg` are callbacks that
  can raise; either attribute can be missing or `_showwarnmsg` not callable, and the twins
  differ there (C falls back to `show_warning` when `_showwarnmsg` is missing).
* An `OverflowError` that `already_warned` leaves set (`PyLong_AsLong` on a `'version'` outside
  C long) changes what runs after it, as measured on 3.15.2: a C callback (`re.Pattern.match`)
  sees it and fails with it; `_match_filename` fails with `SystemError`; a pattern's `match` or a
  metaclass `__subclasscheck__` written in Python fails with `SystemError` if it returns and with
  its own exception if it raises (the first such call in a process can report `SystemError`
  instead; the difftest warms these paths up); a filter line outside `Py_ssize_t` replaces it with
  its own `OverflowError`; with none of these, the result is `SystemError` (`... returned a result
  with an exception set`) unless the action is `error` or unknown, whose exception replaces it, and the show
  callback is not reached.
  Under that pending error, C's import of `warnings` in the show step is out of scope (measured:
  a raising `__import__` hook gives its own exception, `sys.modules['warnings'] = None` leaves
  the `OverflowError`); the model gives what the plain import gives, `SystemError`, and the
  difftest keeps the two apart.
-/

namespace PyLean.CoreLibs.Warn

open PyLean

/-- Registry keys: `(text, category, lineno)`, `(text, category)` and `'version'`. -/
inductive Key where
  | tri (text : String) (cat : Nat) (ln : Int)
  | pair (text : String) (cat : Nat)
  | version
  deriving DecidableEq, Repr

/-- A registry value: `int(v)`, and whether `type(v) is int`. -/
structure Val where
  n : Int
  exact : Bool
  deriving DecidableEq, Repr

/-- A registry dict, newest assignment first. -/
abbrev Reg := List (Key × Val)

def regGet (r : Reg) (k : Key) : Option Val := (r.find? (fun e => decide (e.1 = k))).map (·.2)
def regSet (r : Reg) (k : Key) (v : Val) : Reg := (k, v) :: r.filter (fun e => !decide (e.1 = k))

/-- The registry as `==` sees it: `True == 1`. -/
def norm (r : Reg) : List (Key × Int) := r.map (fun e => (e.1, e.2.n))

/-- `bool(registry.get(k))`. -/
def truthy (v : Option Val) : Bool := match v with | some x => x.n != 0 | none => false

def one : Val := ⟨1, true⟩
def cTrue : Val := ⟨1, false⟩
def exactInt (v : Int) : Val := ⟨v, true⟩

/-- A filter pattern. `regex`: a compiled pattern's `match`, and whether that method is C code;
`objErr` is what it raises on a module that is not a str. `plain`: a str. -/
inductive Pat where
  | regex (call : String → Py Bool) (cfunc : Bool) (objErr : PyExc)
  | plain (s : String)

/-- An action value: a str, another hashable object, or an unhashable one (its type name). -/
inductive AV where
  | str (s : String)
  | hashable (tp : String)
  | unhashable (tp : String)
  deriving DecidableEq, Repr

/-- A filter's line: an int, or another object (its type name). -/
inductive LnV where
  | int (v : Int)
  | obj (tp : String)
  deriving DecidableEq, Repr

/-- A filters-list item's fields. -/
structure Filter where
  action : AV
  msg : Option Pat
  cat : Nat
  mod : Option Pat
  ln : LnV

/-- One element of the filters list. -/
inductive Item where
  | tuple (f : Filter)
  | list5 (f : Filter)
  | other (unpackErr : PyExc)

/-- The base class of a builtin exception class (Objects/exceptions.c), by name: `except C:`
catches `C` and its subclasses. Classes not listed (user classes) have no known base here. -/
def excBase : String → Option String
  | "BrokenPipeError" | "ConnectionAbortedError" | "ConnectionRefusedError" | "ConnectionResetError" =>
    some "ConnectionError"
  | "ConnectionError" | "BlockingIOError" | "ChildProcessError" | "FileExistsError" | "FileNotFoundError"
  | "InterruptedError" | "IsADirectoryError" | "NotADirectoryError" | "PermissionError"
  | "ProcessLookupError" | "TimeoutError" => some "OSError"
  | "UnicodeDecodeError" | "UnicodeEncodeError" | "UnicodeTranslateError" => some "UnicodeError"
  | "UnicodeError" => some "ValueError"
  | "ModuleNotFoundError" | "ImportCycleError" => some "ImportError"
  | "KeyError" | "IndexError" => some "LookupError"
  | "OverflowError" | "ZeroDivisionError" | "FloatingPointError" => some "ArithmeticError"
  | "RecursionError" | "NotImplementedError" | "PythonFinalizationError" => some "RuntimeError"
  | "OSError" | "ValueError" | "ImportError" | "LookupError" | "ArithmeticError" | "RuntimeError"
  | "TypeError" | "AttributeError" | "NameError" | "AssertionError" | "SystemError" | "Warning" =>
    some "Exception"
  | "UnboundLocalError" => some "NameError"
  | "Exception" => some "BaseException"
  | _ => none

/-- Whether builtin class `c` is `base` or a subclass (the chains above are at most five long). -/
def excIsA (c base : String) : Bool :=
  let rec go : Nat → String → Bool
    | 0, _ => false
    | n + 1, k => k == base || match excBase k with
      | some p => go n p
      | none => false
  go 6 c

/-- The class relation `except` uses, over exception class names: `sub c b` is
`PyType_IsSubtype(c, b)`, whether `b` is in `c.__mro__` (the test of `PyErr_GivenExceptionMatches`).
The models take it as a parameter: the classes of the exceptions a callback raises are open (user
classes, `io.UnsupportedOperation`, which is both an `OSError` and a `ValueError`, ...), and a
metaclass `mro()` can drop intermediate bases, so for a non-builtin class the relation need not be
transitive: a class whose `mro()` is `[cls, UnicodeEncodeError, BaseException, object]` is under
`UnicodeEncodeError` but not under `ValueError`. Scope limit: classes are identified by name, so a
user class named `OSError` is the builtin `OSError` here. -/
structure Hier where
  sub : String → String → Bool

/-- A builtin class of the table (its MRO is fixed). -/
def isBuiltinExc (c : String) : Bool := (excBase c).isSome || c == "BaseException"

/-- What CPython guarantees of the relation: on a builtin class it is the builtin one, every
builtin ancestor included (`excIsA`); a non-builtin class is unconstrained (no transitivity, no
reflexivity: a custom `mro()` decides). -/
def HierOk (H : Hier) : Prop :=
  ∀ c b, isBuiltinExc c = true → H.sub c b = excIsA c b

/-- The builtin classes alone (every other class unrelated to every base): one relation. -/
def builtinHier : Hier := ⟨excIsA⟩

theorem builtinHier_ok : HierOk builtinHier := fun _ _ _ => rfl

/-- `except base:` for an exception, under the class relation `H`. -/
def isA (H : Hier) (e : PyExc) (base : String) : Bool := H.sub e.className base

/-- `warnings._showwarnmsg` and `warnings.WarningMessage` as the show step finds them: both there
(`WarningMessage(...)` and the call of `_showwarnmsg` are callbacks that can raise),
`_showwarnmsg` not callable, `_showwarnmsg` deleted, or `WarningMessage` deleted (the other
there, `WarningMessage(...)` succeeding); or deleted with a module `__getattr__` that raises `e`
for it: `_showwarnmsg` (`WarningMessage(...)` gives `wm`) or `WarningMessage`. -/
inductive ShowA where
  | call (wm : Py Unit) (fn : Py Unit)
  | noncallable (tp : String)
  | deleted
  | noWM
  | swRaises (wm : Py Unit) (e : PyExc)
  | wmRaises (e : PyExc)

/-- The Python-visible callbacks. -/
structure Env where
  /-- `issubclass(category, filter_category)` -/
  isSub : Nat → Nat → Py Bool
  /-- whether that `issubclass` runs Python code (a metaclass `__subclasscheck__`) -/
  isSubPy : Nat → Nat → Bool
  /-- `_py_warnings._match_filename(pattern, filename)`, Python code -/
  matchFilename : Pat → String → Py Bool
  /-- the show step -/
  shw : ShowA
  /-- the exception class relation (`PyType_IsSubtype`) -/
  hier : Hier
  /-- C's `PyImport_Import(warnings)` in `GET_WARNINGS_ATTR(_showwarnmsg, 1)`: it gives the
  `warnings` module, or raises -/
  importW : Py Unit

/-- `warnings.defaultaction`: a value, deleted (C then uses the str it read last), or deleted with
a module `__getattr__` that raises `e`. -/
inductive DfltV where
  | val (a : AV)
  | deleted (cached : String)
  | raises (e : PyExc) (cached : String)

/-- `warnings.onceregistry`: a dict, another object (its type name, with no `get`), deleted (C
then uses the dict it read last), or deleted with a module `__getattr__` that raises `e`. -/
inductive OnceV where
  | dict (r : Reg)
  | notDict (tp : String) (kept : Reg)
  | deleted (cached : Reg)
  | raises (e : PyExc) (cached : Reg)

/-- The module state `warn_explicit` reads besides the filters: whether C finds the filters in the
context variable (`_warnings_context _filters`) rather than `warnings.filters`, whether that
container is a tuple, `defaultaction`, `onceregistry`. -/
structure WCfg where
  ctx : Bool
  tuple : Bool
  dflt : DfltV
  once : OnceV

/-- The once registry's contents (empty for an object that is not a dict). -/
def onceReg : OnceV → Reg
  | .dict r => r
  | .notDict _ r => r
  | .deleted r => r
  | .raises _ r => r

/-- `message.__class__` as the Python twin reads it: not overridden (`type(message)`), another
class of the category table (its id, `__name__`, and whether it is a Warning subclass), or a read
that raises. C never reads it. -/
inductive ClsV where
  | own
  | cls (k : Nat) (name : String) (isWarn : Bool)
  | raises (e : PyExc)

/-- The `module` argument: omitted (C `NULL`), an explicit `None`, a str, or another object. -/
inductive ModArg where
  | omitted
  | none
  | some (s : String)
  | obj
  deriving DecidableEq

/-- The `lineno` argument: an int, or an object that `int()` turns into `pyInt` and C's `int`
converter refuses with `cErr`. -/
inductive LineArg where
  | int (v : Int)
  | obj (pyInt : Py Int) (cErr : PyExc)

/-- The `registry` argument: `None`, a dict, another mapping (with `get`, `clear` and item
assignment), or an object with none of them. -/
inductive RegArg where
  | none
  | dict (r : Reg)
  | mapping (r : Reg)
  | obj
  deriving DecidableEq

/-- The `module_globals` argument: `None`, a dict (C's `get_source_line` outcome, which can raise
from the loader's `get_source`), or another object (its type name). -/
inductive GlobA where
  | none
  | dict (cSrc : Py Unit)
  | obj (tp : String)

structure Call where
  text : String
  cat : Nat
  filename : String
  lineno : LineArg
  module : ModArg
  /-- `str(message)` for a Warning instance, `category(message)` otherwise -/
  mkMsg : Py Unit
  globs : GlobA
  /-- `linecache.getlines(filename, module_globals)` in the Python twin -/
  pyLines : Py Unit
  /-- whether the message is a Warning instance (`PyObject_TypeCheck`); then `cat` is its type -/
  inst : Bool
  /-- `message.__class__`, as Python's `isinstance` and `message.__class__` read it -/
  pyCls : ClsV

/-- What a call leaves: its result (`true` when the warning was shown), the registry passed in
(if a dict or mapping), and the once registry. -/
structure Res where
  out : Py Bool
  reg : Option Reg
  once : Reg

/-- `raise message` / `PyErr_SetObject(category, message)` for the `error` action. -/
def warnRaised (c : Call) : PyExc := .named "Warning" c.text
def unrecognized : PyExc := .named "RuntimeError" "~Unrecognized action in warnings.filters"
def leaked : PyExc := .named "SystemError" "~returned a result with an exception set"
/-- The error `PyLong_AsLong` leaves set, :619. -/
def longOverflow : PyExc := .overflowError "Python int too large to convert to C long"
def noMatchAttr : PyExc := .named "AttributeError" "'str' object has no attribute 'match'"
def noGetAttr : PyExc := .named "AttributeError" "~object has no attribute 'get'"
def regTypeErr : PyExc := .typeError "'registry' must be a dict or None"
def cmpTypeErr : PyExc := .typeError "~Can't compare str and object"
/-- `filter_search`'s message, :475-476, with the list's name. -/
def notTupleIn (nm : String) (i : Nat) : PyExc := .valueError s!"warnings.{nm} item {i} isn't a 5-tuple"
def notTuple (i : Nat) : PyExc := notTupleIn "filters" i
def actionTypeErr : PyExc := .typeError "~action must be a string"
def dfltTypeErr : PyExc := .typeError "~warnings.defaultaction must be a string"
def noModAttr (a : String) : PyExc := .named "AttributeError" s!"module 'warnings' has no attribute '{a}'"
def unhashableErr (tp : String) : PyExc :=
  .typeError s!"cannot use '{tp}' as a set element (unhashable type: '{tp}')"
/-- `raise message` for a message that is not an exception. -/
def notExc : PyExc := .typeError "exceptions must derive from BaseException"

/-- An attribute of the `warnings` module as a lookup finds it: there, missing (no module
`__getattr__`), or missing with a module `__getattr__` that raises `e`. -/
inductive AttrR (α : Type) where
  | found (a : α)
  | missing
  | raises (e : PyExc)

/-- `get_warnings_attr(interp, attr, try_import)`, _warnings.c:224-256: with `try_import` (and the
interpreter not finalizing) `import warnings`, whose error is cleared when its class has
`ImportError` in its MRO; otherwise `sys.modules['warnings']`, which may be absent; then
`PyObject_GetOptionalAttr`, which clears an error whose class has `AttributeError` in its MRO
(`_Py_module_getattro_impl` with `suppress`, Objects/moduleobject.c:1395-1399) and leaves any other
set. `.ok none` is `NULL` with no error set. -/
def getWarningsAttr {α : Type} (H : Hier) (tryImport : Bool) (importW : Py Unit) (inSysModules : Bool)
    (attr : AttrR α) : Py (Option α) :=
  let lookup : Py (Option α) := match attr with
    | .found a => .ok (some a)
    | .missing => .ok none
    | .raises e => if isA H e "AttributeError" then .ok none else .error e
  if tryImport then
    match importW with
    | .error e => if isA H e "ImportError" then .ok none else .error e
    | .ok () => lookup
  else if inSysModules then lookup else .ok none

def intMax : Int := 2 ^ 31 - 1
def longMax : Int := 2 ^ 63 - 1

/-- Python's show step, :619-625: `linecache.getlines`, `_wm.WarningMessage(...)`, then
`_wm._showwarnmsg(msg)`. -/
def pyShow (E : Env) (c : Call) : Py Bool := do
  c.pyLines
  match E.shw with
  | .call wm fn => do wm; fn; return true
  | .noncallable tp => .error (.typeError s!"'{tp}' object is not callable")
  | .deleted => .error (noModAttr "_showwarnmsg")
  | .noWM => .error (noModAttr "WarningMessage")
  | .swRaises wm e => do wm; .error e
  | .wmRaises e => .error e

/-- The `_showwarnmsg` lookup of the show step. -/
def swAttr : ShowA → AttrR Unit
  | .deleted => .missing
  | .swRaises _ e => .raises e
  | _ => .found ()

/-- The `WarningMessage` lookup of the show step. -/
def wmAttr : ShowA → AttrR Unit
  | .noWM => .missing
  | .wmRaises e => .raises e
  | _ => .found ()

/-- C's `call_show_warning`, :739-794: `_showwarnmsg` not found (`NULL` with no error) falls back
to `show_warning` (:669-736, which prints and clears every error), an error from its lookup or the
import propagates (:749-752), not callable raises, a `WarningMessage` not found raises
`RuntimeError`, an error from its lookup propagates, else `WarningMessage(...)` and the call. -/
def cShow (E : Env) : Py Bool :=
  -- `GET_WARNINGS_ATTR(interp, _showwarnmsg, 1)`, :749
  match getWarningsAttr E.hier true E.importW true (swAttr E.shw) with
  | .error e => .error e
  | .ok none => .ok true
  | .ok (some ()) =>
    match E.shw with
    | .noncallable _ => .error (.typeError "warnings._showwarnmsg() must be set to a callable")
    | s =>
      -- `GET_WARNINGS_ATTR(interp, WarningMessage, 0)`, :763
      match getWarningsAttr E.hier false (.ok ()) true (wmAttr s) with
      | .error e => .error e
      | .ok none => .error (.named "RuntimeError" "unable to get warnings.WarningMessage")
      | .ok (some ()) =>
        match s with
        | .call wm fn => do wm; fn; return true
        | _ => .ok true

/-- Whether C's show step takes the `show_warning` fallback, :750-755 (it prints to `sys.stderr`
itself; Python always goes through `_showwarnmsg`, so a record log never sees the warning). -/
def cFallback (E : Env) : Bool :=
  match getWarningsAttr E.hier true E.importW true (swAttr E.shw) with
  | .ok none => true
  | _ => false

/-! ## The Python twin, Lib/_py_warnings.py -/

/-- `pattern.match(s)`: a str has no `match`. -/
def pyMatch (m : Pat) (s : String) : Py Bool :=
  match m with
  | .regex call _ _ => call s
  | .plain _ => .error noMatchAttr

/-- The message test of the filter loop, _py_warnings.py:579. -/
def pyMsgOk (c : Call) (f : Filter) : Py Bool :=
  match f.msg with
  | .none => pure true
  | .some m => pyMatch m c.text

/-- The module test, :582-584: `mod.match(module)`, or `_match_filename` when `module` is `None`. -/
def pyModOk (E : Env) (c : Call) (f : Filter) : Py Bool :=
  match f.mod with
  | .none => pure true
  | .some m =>
    match c.module with
    | .some s => pyMatch m s
    | .obj =>
      match m with
      | .regex _ _ e => .error e
      | .plain _ => .error noMatchAttr
    | _ => E.matchFilename m c.filename

/-- `ln == 0 or lineno == ln`, :581: an object that is not an int equals neither. -/
def pyLnOk (l : LnV) (ln : Int) : Bool :=
  match l with
  | .int v => v == 0 || ln == v
  | .obj _ => false

/-- The filter test, _py_warnings.py:579-584: `and` short-circuits in this order. -/
def pyFilterMatches (E : Env) (c : Call) (ln : Int) (f : Filter) : Py Bool := do
  let g1 ← pyMsgOk c f
  if !g1 then return false
  let g2 ← E.isSub c.cat f.cat
  if !g2 then return false
  if !pyLnOk f.ln ln then return false
  pyModOk E c f

/-- The `for item in filters: action, msg, cat, mod, ln = item ... break` loop, :577-587 (any
iterable: a tuple of filters is searched like a list). -/
def pyFind (E : Env) (c : Call) (ln : Int) : List Item → Py (Option Filter)
  | [] => pure .none
  | it :: its =>
    match it with
    | .other e => .error e
    | .tuple f | .list5 f => do
      if ← pyFilterMatches E c ln f then pure (.some f) else pyFind E c ln its

/-- :568-572 on a dict or mapping: one of another filters version (by `!=`, so `True == 1`) is
cleared. -/
def pyRegPrep (ver : Int) (r0 : Reg) : Reg :=
  if ((regGet r0 .version).map (·.n)).getD 0 != ver then regSet [] .version (exactInt ver) else r0

/-- The `RuntimeError` of :613-615 formats `item`, the loop variable, which is unbound when the
filters list is empty. -/
def unboundItem : PyExc :=
  .named "UnboundLocalError" "cannot access local variable 'item' where it is not associated with a value"

/-- The actions, :588-625: `(result, registry, once registry)`. `bound` is whether the loop
variable `item` was ever assigned. An action that is not a str equals none of the names, and
`action in {"always", "all"}` (:601) hashes it. -/
def pyAction (E : Env) (K : WCfg) (c : Call) (ln : Int) (action : AV) (bound : Bool) (r1 : Reg)
    (raised : PyExc) : Py Bool × Reg × Reg :=
  let once := onceReg K.once
  let key := Key.tri c.text c.cat ln
  if action = .str "ignore" then (.ok false, r1, once)
  -- `raise message`, :593
  else if action = .str "error" then (.error raised, r1, once)
  else if action = .str "once" then
    let r2 := regSet r1 key one
    let ok := Key.pair c.text c.cat
    match K.once with
    | .dict o =>
      if truthy (regGet o ok) then (.ok false, r2, once)
      else (pyShow E c, r2, regSet o ok one)
    | .notDict _ _ => (.error noGetAttr, r2, once)
    | .deleted _ => (.error (noModAttr "onceregistry"), r2, once)
    | .raises e _ => (.error e, r2, once)
  else match action with
  | .unhashable tp => (.error (unhashableErr tp), r1, once)
  | _ =>
  if action = .str "always" ∨ action = .str "all" then (pyShow E c, r1, once)
  else if action = .str "module" then
    let r2 := regSet r1 key one
    let alt := Key.tri c.text c.cat 0
    if truthy (regGet r2 alt) then (.ok false, r2, once)
    else (pyShow E c, regSet r2 alt one, once)
  else if action = .str "default" then (pyShow E c, regSet r1 key one, once)
  else (.error (if bound then unrecognized else unboundItem), r1, once)

/-- The message step, _py_warnings.py:560-565: `isinstance(message, Warning)` holds at once for a
Warning instance (`PyObject_TypeCheck`); for another object it reads `__class__`
(`object_isinstance`, Objects/abstract.c:2603-2622: a raising read whose class is under
`AttributeError` is cleared and gives false, any other propagates; another class gives whether it
is a Warning subclass). Then `text = str(message)` and `category = message.__class__` (any error
propagates), or `message = category(message)`. The result is the call with Python's category, and
whether `message` claims a Warning class without being an exception (`raise message` then raises
`TypeError`). -/
def pyMsgStep (H : Hier) (c : Call) : Py (Call × Bool) :=
  if c.inst then
    c.mkMsg >>= fun () => match c.pyCls with
      | .own => .ok (c, false)
      | .cls k _ _ => .ok ({ c with cat := k }, false)
      | .raises e => .error e
  else match c.pyCls with
    | .cls k _ true => .ok ({ c with cat := k }, true)
    | .raises e => if isA H e "AttributeError" then c.mkMsg >>= fun () => .ok (c, false) else .error e
    | _ => c.mkMsg >>= fun () => .ok (c, false)

/-- `warn_explicit`, _py_warnings.py:556-625. `ver` is `_wm._filters_version`. -/
def pyWarnExplicit (E : Env) (K : WCfg) (fs : List Item) (ver : Int) (c0 : Call) (reg : RegArg) : Res :=
  let once := onceReg K.once
  let regOut : Option Reg := match reg with | .dict r | .mapping r => .some r | _ => .none
  -- `lineno = int(lineno)`, :559
  match ((match c0.lineno with | .int v => .ok v | .obj p _ => p) : Py Int) with
  | .error e => ⟨.error e, regOut, once⟩
  | .ok ln =>
  -- the message, :560-565
  match pyMsgStep E.hier c0 with
  | .error e => ⟨.error e, regOut, once⟩
  | .ok (c, pretend) =>
  let raised := if pretend then notExc else warnRaised c
  -- the registry, :568-572
  match reg with
  | .obj => ⟨.error noGetAttr, regOut, once⟩
  | .none | .dict _ | .mapping _ =>
  let r1 := pyRegPrep ver (match reg with | .dict r | .mapping r => r | _ => [])
  let res : Py Bool × Reg × Reg :=
    if truthy (regGet r1 (.tri c.text c.cat ln)) then (.ok false, r1, once)
    else
      match pyFind E c ln fs with
      | .error e => (.error e, r1, once)
      | .ok (.some f) => pyAction E K c ln f.action true r1 raised
      | .ok .none =>
        -- `action = _wm.defaultaction`, :587
        match K.dflt with
        | .deleted _ => (.error (noModAttr "defaultaction"), r1, once)
        | .raises e _ => (.error e, r1, once)
        | .val a => pyAction E K c ln a (!fs.isEmpty) r1 raised
  ⟨res.1, regOut.map (fun _ => res.2.1), res.2.2⟩

/-! ## The C twin, Python/_warnings.c -/

/-- A call into Python code with an error left set: its own exception if it raises, else
`SystemError`. -/
def underPending (r : Py Bool) : Py Bool :=
  match r with
  | .error e => .error e
  | .ok _ => .error leaked

/-- `PyObject_CallMethodOneArg(obj, "match", arg)` with an `OverflowError` possibly left set
(`pend`): C code fails with it, Python code with `SystemError` unless it raises. -/
def callPat (pend : Bool) (call : String → Py Bool) (cfunc : Bool) (s : String) : Py Bool :=
  if pend then
    if cfunc then .error longOverflow else underPending (call s)
  else call s

/-- The argument `check_matched` gets: a str, none (`NULL`: module omitted), or another object. -/
inductive Arg where
  | str (s : String)
  | null
  | obj

/-- The `module` argument as `check_matched` sees it. -/
def modArg (c : Call) : Arg := match c.module with | .some s => .str s | .obj => .obj | _ => .null

/-- `check_matched`, _warnings.c:176-214: `None` matches; a plain str compares equal to `arg`
(and matches nothing when there is no `arg`); a pattern is called on `arg`, or, with no `arg`,
`_match_filename(pattern, filename)` runs. -/
def checkMatched (E : Env) (pend : Bool) (obj : Option Pat) (arg : Arg) (filename : String) :
    Py Bool :=
  match obj with
  | .none => pure true
  | .some (.plain s) =>
    match arg with
    | .null => pure false
    -- `PyUnicode_Compare(obj, arg)` returns -1 for `s < a`, which with an error left set reads as
    -- a failure (:190-192)
    | .str a => if pend && decide (s < a) then .error longOverflow else pure (a == s)
    | .obj => .error cmpTypeErr
  | .some (.regex call cfunc objErr) =>
    match arg with
    | .str a => callPat pend call cfunc a
    -- the argument check of `match` raises before anything sees the pending error
    | .obj => .error objErr
    | .null => if pend then .error leaked else E.matchFilename (.regex call cfunc objErr) filename

/-- `PyLong_AsSsize_t` on the filter's line, :519-524. -/
def asSsize (l : LnV) : Py Int :=
  match l with
  | .obj _ => .error (.typeError "an integer is required")
  | .int v =>
    if v > ssizeMax ∨ v < -ssizeMax - 1 then
      .error (.overflowError "Python int too large to convert to C ssize_t")
    else .ok v

/-- `PyObject_IsSubclass`, :512: Python code under a pending error fails with `SystemError`. -/
def cIsSub (E : Env) (pend : Bool) (a b : Nat) : Py Bool :=
  if pend && E.isSubPy a b then underPending (E.isSub a b) else E.isSub a b

/-- One round of `filter_search`, :498-530, after the item and action checks: all three tests
run, in this order, before any is used. -/
def cFilterMatches (E : Env) (pend : Bool) (c : Call) (ln : Int) (mod : Arg) (f : Filter) :
    Py Bool := do
  let goodMsg ← checkMatched E pend f.msg (.str c.text) c.filename
  let goodMod ← checkMatched E pend f.mod mod c.filename
  let isSub ← cIsSub E pend c.cat f.cat
  let l ← asSsize f.ln
  pure (goodMsg && isSub && goodMod && (l == 0 || ln == l))

/-- `filter_search`'s loop, :470-537, over the list named `nm`: an item that is not a 5-tuple,
then an action that is not a str, stop the search. -/
def cFind (E : Env) (pend : Bool) (c : Call) (ln : Int) (mod : Arg) (nm : String) (i : Nat) :
    List Item → Py (Option Filter)
  | [] => pure .none
  | it :: its =>
    match it with
    | .other _ | .list5 _ => .error (notTupleIn nm i)
    | .tuple f =>
      match f.action with
      | .str _ => do
        if ← cFilterMatches E pend c ln mod f then pure (.some f) else cFind E pend c ln mod nm (i + 1) its
      | _ => .error actionTypeErr

/-- `get_warnings_context_filters` (:332-337) and `get_warnings_filters` (:356-360) refuse a
container that is not a list; the result is the name `filter_search` reports. -/
def cListName (K : WCfg) : Py String :=
  if K.tuple then
    .error (.valueError (if K.ctx then "_filters of warnings._warnings_context must be a list"
      else "_warnings.filters must be a list"))
  else .ok (if K.ctx then "_warnings_context _filters" else "filters")

/-- The `defaultaction` lookup. -/
def dfltAttr : DfltV → AttrR AV
  | .val a => .found a
  | .deleted _ => .missing
  | .raises e _ => .raises e

/-- `get_default_action`, :430-455: `NULL` with an error set returns it (:439-441); `NULL` with
none falls back to the str read last; a value that is not a str raises `TypeError`. -/
def cDefault (H : Hier) (K : WCfg) : Py String :=
  -- `GET_WARNINGS_ATTR(interp, defaultaction, 0)`, :437
  match getWarningsAttr H false (.ok ()) true (dfltAttr K.dflt) with
  | .error e => .error e
  | .ok none => match K.dflt with
    | .deleted s | .raises _ s => .ok s
    | .val (.str s) => .ok s
    | .val _ => .error dfltTypeErr
  | .ok (some (.str s)) => .ok s
  | .ok (some _) => .error dfltTypeErr

/-- `already_warned`, :600-649: `(error left set, warned, registry)`. A `'version'` that is not an
exact int is stale; one outside C long makes `PyLong_AsLong` return -1 with `OverflowError` set,
which nothing clears. -/
def cAlreadyWarned (ver : Int) (r : Reg) (k : Key) (shouldSet : Bool) : Bool × Bool × Reg :=
  let v := regGet r .version
  let pending := match v with
    | .some x => x.exact && decide (x.n > longMax ∨ x.n < -longMax - 1)
    | .none => false
  let upd := match v with
    | .none => true
    | .some x => !x.exact || (if pending then -1 else x.n) != ver
  if upd then
    let r' := regSet [] .version (exactInt ver)
    (pending, false, if shouldSet then regSet r' k cTrue else r')
  else if truthy (regGet r k) then (pending, true, r)
  else (pending, false, if shouldSet then regSet r k cTrue else r)

/-- The `onceregistry` lookup. -/
def onceAttr : OnceV → AttrR OnceV
  | .deleted _ => .missing
  | .raises e _ => .raises e
  | o => .found o

/-- `get_once_registry`, :402-426: `NULL` with an error set returns it (:410-412); `NULL` with
none falls back to the dict read last; an object that is not a dict raises `TypeError`. -/
def cOnceReg (H : Hier) (K : WCfg) : Py Reg :=
  -- `GET_WARNINGS_ATTR(interp, onceregistry, 0)`, :409
  match getWarningsAttr H false (.ok ()) true (onceAttr K.once) with
  | .error e => .error e
  | .ok none => .ok (onceReg K.once)
  | .ok (some (.notDict tp _)) => .error (.typeError s!"_warnings.onceregistry must be a dict, not '{tp}'")
  | .ok (some o) => .ok (onceReg o)

/-- The actions after `get_filter`, :861-909: `(error left set, result, registry, once
registry)`. With no caller registry, `once` uses `get_once_registry` (`cOnceReg`). -/
def cAction (E : Env) (K : WCfg) (ver : Int) (c : Call) (ln : Int) (action : String) (reg1 : Option Reg) :
    Bool × Py Bool × Option Reg × Reg :=
  let once := onceReg K.once
  let key := Key.tri c.text c.cat ln
  if action = "error" then (false, .error (warnRaised c), reg1, once)
  else if action = "ignore" then (false, .ok false, reg1, once)
  else if action = "always" ∨ action = "all" then (false, cShow E, reg1, once)
  else
    let reg2 := reg1.map (fun r => regSet r key cTrue)
    let pk := Key.pair c.text c.cat
    if action = "once" then
      match reg2 with
      | .none =>
        match cOnceReg E.hier K with
        | .error e => (false, .error e, reg2, once)
        | .ok o =>
          let (p, w, o') := cAlreadyWarned ver o pk true
          (p, if w then .ok false else cShow E, reg2, o')
      | .some r =>
        let (p, w, r') := cAlreadyWarned ver r pk true
        (p, if w then .ok false else cShow E, .some r', once)
    else if action = "module" then
      match reg2 with
      | .none => (false, cShow E, reg2, once)
      | .some r =>
        let (p, w, r') := cAlreadyWarned ver r pk true
        (p, if w then .ok false else cShow E, .some r', once)
    else if action = "default" then (false, cShow E, reg2, once)
    else (false, .error unrecognized, reg2, once)

/-- A pending `OverflowError` turns every result into `SystemError` but the exceptions that
replace it: the `error` action's warning (`PyErr_SetObject`) and the unknown-action `RuntimeError`
(`PyErr_Format`). -/
def withPending (c : Call) (pend : Bool) (out : Py Bool) : Py Bool :=
  if pend then
    match out with
    | .error e => if e = warnRaised c ∨ e = unrecognized then .error e else .error leaked
    | .ok _ => .error leaked
  else out

/-- `warnings.warn_explicit`: the clinic conversion of `lineno` to C `int`, then
`warnings_warn_explicit_impl` (:1314-1349: `module_globals` must be a dict, and `get_source_line`,
:1214-1296, runs before the lock), then `warn_explicit`, :797-922. `ver` is `filters_version`;
`fs` the filters `get_filter` searches. -/
def cWarnExplicit (E : Env) (K : WCfg) (fs : List Item) (ver : Int) (c : Call) (reg : RegArg) : Res :=
  let once := onceReg K.once
  let regOut : Option Reg := match reg with | .dict r | .mapping r => .some r | _ => .none
  match c.lineno with
  | .obj _ e => ⟨.error e, regOut, once⟩
  | .int ln =>
  if ln > intMax ∨ ln < -intMax - 1 then
    ⟨.error (.overflowError "Python int too large to convert to C int"), regOut, once⟩
  else
  -- :1328-1341
  match (match c.globs with
    | .none => .ok ()
    | .obj tp => .error (.typeError s!"module_globals must be a dict or a frozendict, not {tp}")
    | .dict src => src : Py Unit) with
  | .error e => ⟨.error e, regOut, once⟩
  | .ok () =>
  -- :812-813
  match c.module with
  | .none => ⟨.ok false, regOut, once⟩
  | .omitted | .some _ | .obj =>
  -- :815-818
  match reg with
  | .obj | .mapping _ => ⟨.error regTypeErr, regOut, once⟩
  | .none | .dict _ =>
  -- :822-833
  match c.mkMsg with
  | .error e => ⟨.error e, regOut, once⟩
  | .ok () =>
  let key := Key.tri c.text c.cat ln
  let (pend0, warned, reg1) : Bool × Bool × Option Reg := match reg with
    | .dict r =>
      let (p, w, r') := cAlreadyWarned ver r key false
      (p, w, .some r')
    | _ => (false, false, .none)
  if warned then ⟨withPending c pend0 (.ok false), reg1, once⟩
  else
    match cListName K with
    | .error e => ⟨.error e, reg1, once⟩
    | .ok nm =>
    match cFind E pend0 c ln (modArg c) nm 0 fs with
    | .error e => ⟨.error e, reg1, once⟩
    | .ok item =>
      let act : Py String := match item with
        | .some f => match f.action with | .str s => .ok s | _ => .error actionTypeErr
        -- with an error left set, a deleted `defaultaction` makes `get_default_action` return that
        -- error (`PyErr_Occurred`, :439-441)
        -- (a module `__getattr__` is not reached: the attribute lookup returns at once with the
        -- error set, Objects/moduleobject.c:1340-1344)
        | .none => match pend0, K.dflt with
          | true, .deleted _ | true, .raises _ _ => .error longOverflow
          | _, _ => cDefault E.hier K
      match act with
      | .error e => ⟨.error e, reg1, once⟩
      | .ok a =>
        let (p, out, r, o) := cAction E K ver c ln a reg1
        ⟨withPending c (pend0 || p) out, r, o⟩

/-- `.ok true`: the warning was shown. -/
def isShown : Py Bool → Bool
  | .ok true => true
  | _ => false

/-- Whether C `warn_explicit` showed the warning through `show_warning` rather than
`_showwarnmsg` (the Python twin never does). -/
def cFellBack (E : Env) (K : WCfg) (fs : List Item) (ver : Int) (c : Call) (reg : RegArg) : Bool :=
  isShown (cWarnExplicit E K fs ver c reg).out && cFallback E

end PyLean.CoreLibs.Warn
