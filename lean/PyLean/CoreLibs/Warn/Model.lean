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
* A filters-list item is a 5-tuple, a 5-element list (C refuses it, Python unpacks it), or
  something else (C refuses it; Python's unpacking raises what the call gives). Its action is a
  str or not; its message and module patterns are compiled regexes (callbacks, C or Python code,
  that can raise) or plain strs (what C's internal default filters hold); its line is an int.
  `defaultaction` is a str or not.
* A registry is `None`, a dict, or some other object. Its values are ints, each with whether it is
  an exact int (C stores `True`; a `'version'` that is a bool or an int subclass is not exact).
* `lineno` is an int, or another object that Python's `int()` converts (or fails on) and C's `int`
  converter refuses. `module` is omitted, `None`, a str, or another object whose regex match raises.
* `_match_filename` is one `Env` callback: the C code calls the Python function.
* `showwarning` (with the `linecache.getlines` and `WarningMessage` before it) is one `Env`
  callback that can raise.
* An `OverflowError` that `already_warned` leaves set (`PyLong_AsLong` on a `'version'` outside
  C long) changes what runs after it, as measured on 3.15.2: a C callback (`re.Pattern.match`)
  sees it and fails with it; `_match_filename` fails with `SystemError`; a pattern's `match` or a
  metaclass `__subclasscheck__` written in Python fails with `SystemError` if it returns and with
  its own exception if it raises (the first such call in a process can report `SystemError`
  instead; the difftest warms these paths up); a filter line outside `Py_ssize_t` replaces it with
  its own `OverflowError`; with none of these, the result is `SystemError` (`... returned a result
  with an exception set`) unless the action is `error` or unknown, whose exception replaces it, and the show
  callback is not reached.
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

/-- A filters-list item's fields. `action` is `none` when it is not a str. -/
structure Filter where
  action : Option String
  msg : Option Pat
  cat : Nat
  mod : Option Pat
  ln : Int

/-- One element of the filters list. -/
inductive Item where
  | tuple (f : Filter)
  | list5 (f : Filter)
  | other (unpackErr : PyExc)

/-- The Python-visible callbacks. -/
structure Env where
  /-- `issubclass(category, filter_category)` -/
  isSub : Nat → Nat → Py Bool
  /-- whether that `issubclass` runs Python code (a metaclass `__subclasscheck__`) -/
  isSubPy : Nat → Nat → Bool
  /-- `_py_warnings._match_filename(pattern, filename)`, Python code -/
  matchFilename : Pat → String → Py Bool
  /-- `linecache.getlines`, `WarningMessage(...)` and `_showwarnmsg(msg)` -/
  showMsg : Py Unit

/-- The `module` argument: omitted (C `NULL`), an explicit `None`, a str, or another object. -/
inductive ModArg where
  | omitted
  | none
  | some (s : String)
  | obj

/-- The `lineno` argument: an int, or an object that `int()` turns into `pyInt` and C's `int`
converter refuses with `cErr`. -/
inductive LineArg where
  | int (v : Int)
  | obj (pyInt : Py Int) (cErr : PyExc)

/-- The `registry` argument. -/
inductive RegArg where
  | none
  | dict (r : Reg)
  | obj

structure Call where
  text : String
  cat : Nat
  filename : String
  lineno : LineArg
  module : ModArg
  /-- `str(message)` for a Warning instance, `category(message)` otherwise -/
  mkMsg : Py Unit

/-- What a call leaves: its result (`true` when the warning was shown), the registry passed in
(if a dict), and the once registry. -/
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
def notTuple (i : Nat) : PyExc := .valueError s!"warnings.filters item {i} isn't a 5-tuple"
def actionTypeErr : PyExc := .typeError "~action must be a string"
def dfltTypeErr : PyExc := .typeError "~warnings.defaultaction must be a string"

def intMax : Int := 2 ^ 31 - 1
def longMax : Int := 2 ^ 63 - 1

def showOut (E : Env) : Py Bool := E.showMsg.map (fun _ => true)

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

/-- The filter test, _py_warnings.py:579-584: `and` short-circuits in this order. -/
def pyFilterMatches (E : Env) (c : Call) (ln : Int) (f : Filter) : Py Bool := do
  let g1 ← pyMsgOk c f
  if !g1 then return false
  let g2 ← E.isSub c.cat f.cat
  if !g2 then return false
  if !(f.ln == 0 || ln == f.ln) then return false
  pyModOk E c f

/-- The `for item in filters: action, msg, cat, mod, ln = item ... break` loop, :577-587. -/
def pyFind (E : Env) (c : Call) (ln : Int) : List Item → Py (Option Filter)
  | [] => pure .none
  | it :: its =>
    match it with
    | .other e => .error e
    | .tuple f | .list5 f => do
      if ← pyFilterMatches E c ln f then pure (.some f) else pyFind E c ln its

/-- `action` after the loop: the filter's, or `defaultaction` (:586-587); `none` when not a str. -/
def actionOf (item : Option Filter) (dflt : Option String) : Option String :=
  match item with | .some f => f.action | .none => dflt

/-- :568-572 on a dict: one of another filters version (by `!=`, so `True == 1`) is cleared. -/
def pyRegPrep (ver : Int) (r0 : Reg) : Reg :=
  if ((regGet r0 .version).map (·.n)).getD 0 != ver then regSet [] .version (exactInt ver) else r0

/-- The `RuntimeError` of :613-615 formats `item`, the loop variable, which is unbound when the
filters list is empty. -/
def unboundItem : PyExc :=
  .named "UnboundLocalError" "cannot access local variable 'item' where it is not associated with a value"

/-- The actions, :588-625: `(result, registry, once registry)`. `bound` is whether the loop
variable `item` was ever assigned. An action that is not a str equals none of the names. -/
def pyAction (E : Env) (c : Call) (ln : Int) (action : Option String) (bound : Bool) (r1 once : Reg) :
    Py Bool × Reg × Reg :=
  let key := Key.tri c.text c.cat ln
  if action = some "ignore" then (.ok false, r1, once)
  else if action = some "error" then (.error (warnRaised c), r1, once)
  else if action = some "once" then
    let r2 := regSet r1 key one
    let ok := Key.pair c.text c.cat
    if truthy (regGet once ok) then (.ok false, r2, once)
    else (showOut E, r2, regSet once ok one)
  else if action = some "always" ∨ action = some "all" then (showOut E, r1, once)
  else if action = some "module" then
    let r2 := regSet r1 key one
    let alt := Key.tri c.text c.cat 0
    if truthy (regGet r2 alt) then (.ok false, r2, once)
    else (showOut E, regSet r2 alt one, once)
  else if action = some "default" then (showOut E, regSet r1 key one, once)
  else (.error (if bound then unrecognized else unboundItem), r1, once)

/-- `warn_explicit`, _py_warnings.py:556-625. `ver` is `_wm._filters_version`. -/
def pyWarnExplicit (E : Env) (fs : List Item) (dflt : Option String) (ver : Int) (c : Call)
    (reg : RegArg) (once : Reg) : Res :=
  let regOut : Option Reg := match reg with | .dict r => .some r | _ => .none
  -- `lineno = int(lineno)`, :559
  match ((match c.lineno with | .int v => .ok v | .obj p _ => p) : Py Int) with
  | .error e => ⟨.error e, regOut, once⟩
  | .ok ln =>
  -- the message, :560-565
  match c.mkMsg with
  | .error e => ⟨.error e, regOut, once⟩
  | .ok () =>
  -- the registry, :568-572
  match reg with
  | .obj => ⟨.error noGetAttr, regOut, once⟩
  | .none | .dict _ =>
  let r1 := pyRegPrep ver (match reg with | .dict r => r | _ => [])
  let res : Py Bool × Reg × Reg :=
    if truthy (regGet r1 (.tri c.text c.cat ln)) then (.ok false, r1, once)
    else
      match pyFind E c ln fs with
      | .error e => (.error e, r1, once)
      | .ok item => pyAction E c ln (actionOf item dflt) (item.isSome || !fs.isEmpty) r1 once
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
def asSsize (v : Int) : Py Int :=
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

/-- `filter_search`'s loop, :470-537: an item that is not a 5-tuple, then an action that is not a
str, stop the search. -/
def cFind (E : Env) (pend : Bool) (c : Call) (ln : Int) (mod : Arg) (i : Nat) :
    List Item → Py (Option Filter)
  | [] => pure .none
  | it :: its =>
    match it with
    | .other _ | .list5 _ => .error (notTuple i)
    | .tuple f =>
      if f.action.isNone then .error actionTypeErr
      else do
        if ← cFilterMatches E pend c ln mod f then pure (.some f) else cFind E pend c ln mod (i + 1) its

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

/-- The actions after `get_filter`, :861-909: `(error left set, result, registry, once
registry)`. -/
def cAction (E : Env) (ver : Int) (c : Call) (ln : Int) (action : String) (reg1 : Option Reg)
    (once : Reg) : Bool × Py Bool × Option Reg × Reg :=
  let key := Key.tri c.text c.cat ln
  if action = "error" then (false, .error (warnRaised c), reg1, once)
  else if action = "ignore" then (false, .ok false, reg1, once)
  else if action = "always" ∨ action = "all" then (false, showOut E, reg1, once)
  else
    let reg2 := reg1.map (fun r => regSet r key cTrue)
    let pk := Key.pair c.text c.cat
    if action = "once" then
      match reg2 with
      | .none =>
        let (p, w, o) := cAlreadyWarned ver once pk true
        (p, if w then .ok false else showOut E, reg2, o)
      | .some r =>
        let (p, w, r') := cAlreadyWarned ver r pk true
        (p, if w then .ok false else showOut E, .some r', once)
    else if action = "module" then
      match reg2 with
      | .none => (false, showOut E, reg2, once)
      | .some r =>
        let (p, w, r') := cAlreadyWarned ver r pk true
        (p, if w then .ok false else showOut E, .some r', once)
    else if action = "default" then (false, showOut E, reg2, once)
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

/-- `warn_explicit`, :797-922, after the clinic conversion of `lineno` to C `int`
(`warnings_warn_explicit_impl`, :1314-1349). `ver` is `filters_version`; `fs` the filters list
`get_filter` searches. -/
def cWarnExplicit (E : Env) (fs : List Item) (dflt : Option String) (ver : Int) (c : Call)
    (reg : RegArg) (once : Reg) : Res :=
  let regOut : Option Reg := match reg with | .dict r => .some r | _ => .none
  match c.lineno with
  | .obj _ e => ⟨.error e, regOut, once⟩
  | .int ln =>
  if ln > intMax ∨ ln < -intMax - 1 then
    ⟨.error (.overflowError "Python int too large to convert to C int"), regOut, once⟩
  else
  -- :812-813
  match c.module with
  | .none => ⟨.ok false, regOut, once⟩
  | .omitted | .some _ | .obj =>
  -- :815-818
  match reg with
  | .obj => ⟨.error regTypeErr, regOut, once⟩
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
    match cFind E pend0 c ln (modArg c) 0 fs with
    | .error e => ⟨.error e, reg1, once⟩
    | .ok item =>
      match actionOf item dflt with
      | .none => ⟨.error dfltTypeErr, reg1, once⟩
      | .some a =>
        let (p, out, r, o) := cAction E ver c ln a reg1 once
        ⟨withPending c (pend0 || p) out, r, o⟩

end PyLean.CoreLibs.Warn
