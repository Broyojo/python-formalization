import PyLean.Core

/-!
`warnings.warn_explicit`, both twins: the C one, Python/_warnings.c (`warnings_warn_explicit_impl`
:1314-1349, `warn_explicit` :797-922, `get_filter` :541-596, `filter_search` :460-538,
`check_matched` :176-214, `already_warned` :600-649, `update_registry` :652-666), and the Python one,
Lib/_py_warnings.py:556-625.

Scope:
* A warning is its text and its category; a category is a class id, and `issubclass` is an
  `Env` callback that can raise. Building the message object (`category(message)`, `str(message)`)
  is the same in both twins and is not modelled.
* A filter is typed: its action a str, its message and module patterns callbacks (`re.match`, or
  the exact compare of an internal str filter) that can raise, its line an int. A filters list
  that is not a list of 5-tuples, and an action that is not a str, are out of scope.
* Registries hold int values (`True` is 1); `'version'` holds an int.
* `_match_filename` is one `Env` callback: the C code calls the Python function.
* `showwarning` is an `Env` callback that can raise.
* An `OverflowError` that `already_warned` leaves set (`PyLong_AsLong` on a `'version'` outside
  C long) changes what runs after it, as measured on 3.15.2: a C callback (`re.Pattern.match`)
  sees it and fails with it; `_match_filename` fails with `SystemError`; a pattern's `match` or a
  metaclass `__subclasscheck__` written in Python fails with `SystemError` if it returns and with
  its own exception if it raises (the first such call in a process can report `SystemError`
  instead; the difftest warms these paths up); a filter line
  outside `Py_ssize_t` replaces it with its own `OverflowError`; with none of these, the result is
  `SystemError` (`... returned a result with an exception set`) unless the action is `error`, whose
  warning replaces it, and the show callback is not reached.
-/

namespace PyLean.CoreLibs.Warn

open PyLean

/-- Registry keys: `(text, category, lineno)`, `(text, category)` and `'version'`. -/
inductive Key where
  | tri (text : String) (cat : Nat) (ln : Int)
  | pair (text : String) (cat : Nat)
  | version
  deriving DecidableEq, Repr

/-- A registry dict, newest assignment first. -/
abbrev Reg := List (Key × Int)

def regGet (r : Reg) (k : Key) : Option Int := (r.find? (fun e => decide (e.1 = k))).map (·.2)
def regSet (r : Reg) (k : Key) (v : Int) : Reg := (k, v) :: r.filter (fun e => !decide (e.1 = k))

/-- `bool(registry.get(k))` for int values. -/
def truthy (v : Option Int) : Bool := match v with | some x => x != 0 | none => false

/-- A filter pattern: its `match` method, and whether that method is C code (a compiled
`re.Pattern`) rather than Python code. -/
structure Pat where
  call : String → Py Bool
  cfunc : Bool

/-- One `warnings.filters` item `(action, message, category, module, lineno)`. -/
structure Filter where
  action : String
  msg : Option Pat
  cat : Nat
  mod : Option Pat
  ln : Int

/-- The Python-visible callbacks. -/
structure Env where
  /-- `issubclass(category, filter_category)` -/
  isSub : Nat → Nat → Py Bool
  /-- whether that `issubclass` runs Python code (a metaclass `__subclasscheck__`) -/
  isSubPy : Nat → Nat → Bool
  /-- `_py_warnings._match_filename(pattern, filename)`, Python code -/
  matchFilename : Pat → String → Py Bool
  /-- `_showwarnmsg(msg)` -/
  showMsg : Py Unit

/-- The `module` argument: omitted (C `NULL`), an explicit `None`, or a str. -/
inductive ModArg where
  | omitted
  | none
  | some (s : String)

structure Call where
  text : String
  cat : Nat
  filename : String
  lineno : Int
  module : ModArg

/-- What a call leaves: its result (`true` when the warning was shown), the registry passed in
(if any), and the once registry. -/
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

def intMax : Int := 2 ^ 31 - 1
def longMax : Int := 2 ^ 63 - 1

def showOut (E : Env) : Py Bool := E.showMsg.map (fun _ => true)

/-! ## The Python twin, Lib/_py_warnings.py -/

/-- The message test of the filter loop, _py_warnings.py:579. -/
def pyMsgOk (c : Call) (f : Filter) : Py Bool :=
  match f.msg with
  | .none => pure true
  | .some m => m.call c.text

/-- The module test, :582-584: `mod.match(module)`, or `_match_filename` when `module` is `None`. -/
def pyModOk (E : Env) (c : Call) (f : Filter) : Py Bool :=
  match f.mod with
  | .none => pure true
  | .some m =>
    match c.module with
    | .some s => m.call s
    | _ => E.matchFilename m c.filename

/-- The filter test, _py_warnings.py:579-584: `and` short-circuits in this order. -/
def pyFilterMatches (E : Env) (c : Call) (f : Filter) : Py Bool := do
  let g1 ← pyMsgOk c f
  if !g1 then return false
  let g2 ← E.isSub c.cat f.cat
  if !g2 then return false
  if !(f.ln == 0 || c.lineno == f.ln) then return false
  pyModOk E c f

/-- The `for item in filters: ... break` loop, :577-587. -/
def pyFind (E : Env) (c : Call) : List Filter → Py (Option Filter)
  | [] => pure .none
  | f :: fs => do
    if ← pyFilterMatches E c f then pure (.some f) else pyFind E c fs

/-- `action` after the loop: the filter's, or `defaultaction` (:586-587). -/
def actionOf (item : Option Filter) (dflt : String) : String :=
  match item with | .some f => f.action | .none => dflt

/-- :568-572: `None` becomes `{}`; a registry of another filters version is cleared. -/
def pyRegPrep (ver : Int) (reg : Option Reg) : Reg :=
  let r0 := reg.getD []
  if (regGet r0 .version).getD 0 != ver then regSet [] .version ver else r0

/-- The `RuntimeError` of :613-615 formats `item`, the loop variable, which is unbound when the
filters list is empty. -/
def unboundItem : PyExc :=
  .named "UnboundLocalError" "cannot access local variable 'item' where it is not associated with a value"

/-- The actions, :588-625: `(result, registry, once registry)`. `bound` is whether the loop
variable `item` was ever assigned. -/
def pyAction (E : Env) (c : Call) (action : String) (bound : Bool) (r1 once : Reg) :
    Py Bool × Reg × Reg :=
  let key := Key.tri c.text c.cat c.lineno
  if action = "ignore" then (.ok false, r1, once)
  else if action = "error" then (.error (warnRaised c), r1, once)
  else if action = "once" then
    let r2 := regSet r1 key 1
    let ok := Key.pair c.text c.cat
    if truthy (regGet once ok) then (.ok false, r2, once)
    else (showOut E, r2, regSet once ok 1)
  else if action = "always" ∨ action = "all" then (showOut E, r1, once)
  else if action = "module" then
    let r2 := regSet r1 key 1
    let alt := Key.tri c.text c.cat 0
    if truthy (regGet r2 alt) then (.ok false, r2, once)
    else (showOut E, regSet r2 alt 1, once)
  else if action = "default" then (showOut E, regSet r1 key 1, once)
  else (.error (if bound then unrecognized else unboundItem), r1, once)

/-- `warn_explicit`, _py_warnings.py:556-625. `ver` is `_wm._filters_version`. -/
def pyWarnExplicit (E : Env) (fs : List Filter) (dflt : String) (ver : Int) (c : Call)
    (reg : Option Reg) (once : Reg) : Res :=
  let r1 := pyRegPrep ver reg
  let res : Py Bool × Reg × Reg :=
    if truthy (regGet r1 (.tri c.text c.cat c.lineno)) then (.ok false, r1, once)
    else
      match pyFind E c fs with
      | .error e => (.error e, r1, once)
      | .ok item => pyAction E c (actionOf item dflt) (item.isSome || !fs.isEmpty) r1 once
  ⟨res.1, reg.map (fun _ => res.2.1), res.2.2⟩

/-! ## The C twin, Python/_warnings.c -/

/-- A call into Python code with an error left set: its own exception if it raises, else
`SystemError`. -/
def underPending (r : Py Bool) : Py Bool :=
  match r with
  | .error e => .error e
  | .ok _ => .error leaked

/-- A call into a pattern with an `OverflowError` possibly left set (`pend`): C code fails with
it, Python code with `SystemError`. -/
def callPat (pend : Bool) (m : Pat) (s : String) : Py Bool :=
  if pend then
    if m.cfunc then .error longOverflow else underPending (m.call s)
  else m.call s

/-- `check_matched`, _warnings.c:176-214: `None` matches; a pattern is called on `arg`, or, with
no `arg` (the module argument omitted), `_match_filename(pattern, filename)` runs. -/
def checkMatched (E : Env) (pend : Bool) (obj : Option Pat) (arg : Option String)
    (filename : String) : Py Bool :=
  match obj with
  | .none => pure true
  | .some m =>
    match arg with
    | .some a => callPat pend m a
    | .none => if pend then .error leaked else E.matchFilename m filename

/-- `PyLong_AsSsize_t` on the filter's line, :519-524. -/
def asSsize (v : Int) : Py Int :=
  if v > ssizeMax ∨ v < -ssizeMax - 1 then
    .error (.overflowError "Python int too large to convert to C ssize_t")
  else .ok v

/-- `PyObject_IsSubclass`, :512: Python code under a pending error fails with `SystemError`. -/
def cIsSub (E : Env) (pend : Bool) (a b : Nat) : Py Bool :=
  if pend && E.isSubPy a b then underPending (E.isSub a b) else E.isSub a b

/-- One round of `filter_search`, :498-530: all three tests run, in this order, before any is
used. -/
def cFilterMatches (E : Env) (pend : Bool) (c : Call) (mod : Option String) (f : Filter) :
    Py Bool := do
  let goodMsg ← checkMatched E pend f.msg (.some c.text) c.filename
  let goodMod ← checkMatched E pend f.mod mod c.filename
  let isSub ← cIsSub E pend c.cat f.cat
  let ln ← asSsize f.ln
  pure (goodMsg && isSub && goodMod && (ln == 0 || c.lineno == ln))

/-- `filter_search`'s loop, :470-537. -/
def cFind (E : Env) (pend : Bool) (c : Call) (mod : Option String) :
    List Filter → Py (Option Filter)
  | [] => pure .none
  | f :: fs => do
    if ← cFilterMatches E pend c mod f then pure (.some f) else cFind E pend c mod fs

/-- `already_warned`, :600-649: `(error left set, warned, registry)`. A `'version'` outside C
long makes `PyLong_AsLong` return -1 with `OverflowError` set, which nothing clears. -/
def cAlreadyWarned (ver : Int) (r : Reg) (k : Key) (shouldSet : Bool) : Bool × Bool × Reg :=
  let v := regGet r .version
  let pending := match v with
    | .some x => decide (x > longMax ∨ x < -longMax - 1)
    | .none => false
  let asLong := match v with
    | .some x => if pending then -1 else x
    | .none => 0
  let upd := v.isNone || asLong != ver
  if upd then
    let r' := regSet [] .version ver
    (pending, false, if shouldSet then regSet r' k 1 else r')
  else if truthy (regGet r k) then (pending, true, r)
  else (pending, false, if shouldSet then regSet r k 1 else r)

/-- The actions after `get_filter`, :861-909: `(error left set, result, registry, once
registry)`. -/
def cAction (E : Env) (ver : Int) (c : Call) (action : String) (reg1 : Option Reg) (once : Reg) :
    Bool × Py Bool × Option Reg × Reg :=
  let key := Key.tri c.text c.cat c.lineno
  if action = "error" then (false, .error (warnRaised c), reg1, once)
  else if action = "ignore" then (false, .ok false, reg1, once)
  else if action = "always" ∨ action = "all" then (false, showOut E, reg1, once)
  else
    let reg2 := reg1.map (fun r => regSet r key 1)
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

/-- A pending `OverflowError` turns every result but the `error` action's into `SystemError`. -/
def withPending (c : Call) (pend : Bool) (out : Py Bool) : Py Bool :=
  if pend then
    match out with
    | .error e => if e = warnRaised c then .error e else .error leaked
    | .ok _ => .error leaked
  else out

/-- `warn_explicit`, :797-922, with the clinic conversion of `lineno` to C `int` and the `module`
argument as given. `ver` is `filters_version`; `fs` the filters list `get_filter` searches. -/
def cWarnExplicit (E : Env) (fs : List Filter) (dflt : String) (ver : Int) (c : Call)
    (reg : Option Reg) (once : Reg) : Res :=
  if c.lineno > intMax ∨ c.lineno < -intMax - 1 then
    ⟨.error (.overflowError "Python int too large to convert to C int"), reg, once⟩
  else
  match c.module with
  | .none => ⟨.ok false, reg, once⟩
  | .omitted | .some _ =>
  let mod : Option String := match c.module with | .some s => .some s | _ => .none
  let key := Key.tri c.text c.cat c.lineno
  let (pend0, warned, reg1) : Bool × Bool × Option Reg := match reg with
    | .none => (false, false, .none)
    | .some r =>
      let (p, w, r') := cAlreadyWarned ver r key false
      (p, w, .some r')
  if warned then ⟨withPending c pend0 (.ok false), reg1, once⟩
  else
    match cFind E pend0 c mod fs with
    | .error e => ⟨.error e, reg1, once⟩
    | .ok item =>
      let (p, out, r, o) := cAction E ver c (actionOf item dflt) reg1 once
      ⟨withPending c (pend0 || p) out, r, o⟩

end PyLean.CoreLibs.Warn
