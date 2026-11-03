import PyLean.CoreLibs.Warn.Model

/-!
The filters-list API of `Lib/_py_warnings.py` (CPython 3.15.2), shared by both twins (the C
module replaces only `_filters_mutated_lock_held` and the lock): `filterwarnings` (:254-291),
`simplefilter` (:294-310), `_filters_mutated` (:313-317), `_add_filter` (:320-334),
`resetwarnings` (:337-341), `_filters_mutated_lock_held` (:117-118), `_setup_defaults`
(:920-928); and the C side, Python/_warnings.c: `_acquire_lock` (`warnings_acquire_lock_impl`
:370-379), `_release_lock` (:387-399), `_filters_mutated_lock_held` (:1357-1377), with
`warnings_lock` (:259-264), `warnings_unlock` (:267-272), `warnings_lock_held` (:275-278), and the
initial filters list, `init_filters` (:101-132) with `create_filter` (:78-97).

Scope:
* A filter item is `(action, message, category, module, lineno)`. A compiled pattern is its source
  and whether `re.I` was given: `re.Pattern.__eq__` compares exactly those (with `re.UNICODE`,
  which every str pattern has). A category is an object id: `filterwarnings` refuses anything but a
  Warning subclass, `simplefilter` stores any object. Classes compare by identity (a metaclass
  overriding `__eq__` is out of scope). A `lineno` that is a bool is stored as itself and compares
  as its int value; the model keeps the int.
* The filters list may hold other objects; `elem == item` for one of them is a callback that can
  raise (`list.remove` and `in` compare every element in order).
* `_wm._get_filters()` is a list, a tuple (someone assigned `warnings.filters = (...)`), or, when
  `warnings.filters` was deleted, the fresh `[]` that `_GlobalContext._filters` returns
  (:76-80), whose changes are lost.
* `re.compile` is a callback that can raise. `action not in {...}` hashes the action: a str is
  looked up, another hashable object is not in the set (its `repr` is in the message), an
  unhashable one raises `TypeError`.
* The lock is the C recursive mutex: its owner thread and level. `PyMutex_IsLocked` (:277) asks
  whether any thread holds it.
-/

namespace PyLean.CoreLibs.Warn

open PyLean

/-! ## Values -/

/-- A compiled pattern, as `re.Pattern.__eq__` sees it. -/
structure Rx where
  src : String
  ci : Bool
  deriving DecidableEq, Repr

/-- A filter item `_add_filter` builds. -/
structure FItem where
  action : String
  msg : Option Rx
  cat : Nat
  mod : Option Rx
  ln : Int
  deriving DecidableEq, Repr

/-- An element of the filters list: an item, or another object whose `==` against a new item
gives `eqRes`. -/
inductive Elem where
  | item (f : FItem)
  | other (id : Nat) (eqRes : Py Bool)

/-- What `_wm._get_filters()` returns. -/
inductive Cont where
  | list (xs : List Elem)
  | tuple (xs : List Elem)
  | deleted

/-- The filters container and the filters version (`_filters_version` in Python, the C
`filters_version` in C). -/
structure FState where
  cont : Cont
  ver : Int

/-- `action`: a str, another hashable object (its `repr`), or an unhashable object (its type name). -/
inductive ActA where
  | str (s : String)
  | obj (repr : String)
  | unhashable (tp : String)

/-- An argument checked with `isinstance(x, str)` or `isinstance(x, int)`. -/
inductive StrA where
  | str (s : String)
  | obj

inductive IntA where
  | int (v : Int)
  | obj

/-- The callbacks: `re.compile(src, re.I if ci else 0)`, `isinstance(c, type)`, and
`issubclass(c, Warning)` for a class `c` (`type.__subclasscheck__`, which runs no user code). -/
structure FEnv where
  compile : String → Bool → Py Unit
  isType : Nat → Bool
  isWarn : Nat → Bool
  /-- the exception class hierarchy -/
  hier : Hier

/-! ## `repr` of a str -/

def hexDigitsLower (n width : Nat) : String :=
  let ds := Nat.toDigits 16 n
  String.ofList (List.replicate (width - ds.length) '0' ++ ds)

/-- `str.isprintable` for one character, exact on the blocks the difftest draws from (ASCII,
Latin-1, General Punctuation, CJK Symbols, Arabic-Indic and fullwidth digits): controls, `Zs`
other than the space, `Zl`, `Zp`, the soft hyphen and the `Cf` format characters there are not
printable. -/
def printableC (c : Char) : Bool :=
  let n := c.toNat
  !(n < 32 || (127 ≤ n && n < 161) || n == 0xAD || n == 0x1680 || (0x2000 ≤ n && n ≤ 0x200F) ||
    (0x2028 ≤ n && n ≤ 0x202F) || (0x205F ≤ n && n ≤ 0x2064) || n == 0x3000 || n == 0xFEFF ||
    (0xD800 ≤ n && n ≤ 0xDFFF))

/-- One character of `unicode_repr` (Objects/unicodeobject.c). -/
def reprC (quote c : Char) : String :=
  if c == quote || c == '\\' then "\\" ++ c.toString
  else if c == '\t' then "\\t"
  else if c == '\n' then "\\n"
  else if c == '\r' then "\\r"
  else if printableC c then c.toString
  else if c.toNat < 256 then "\\x" ++ hexDigitsLower c.toNat 2
  else if c.toNat < 65536 then "\\u" ++ hexDigitsLower c.toNat 4
  else "\\U" ++ hexDigitsLower c.toNat 8

/-- `repr(s)`: single quotes unless the text has `'` and no `"`. -/
def pyReprStr (s : String) : String :=
  let quote := if s.toList.contains '\'' && !s.toList.contains '"' then '"' else '\''
  quote.toString ++ String.join (s.toList.map (reprC quote)) ++ quote.toString

/-! ## `_add_filter`, :320-334 -/

/-- `elem == item`. -/
def elemEq (it : FItem) : Elem → Py Bool
  | .item f => .ok (decide (f = it))
  | .other _ r => r

/-- `list.remove(item)`: the list without its first element equal to `item`, or `none` (the
`ValueError` that `_add_filter` catches). -/
def pyRemove (it : FItem) : List Elem → Py (Option (List Elem))
  | [] => .ok none
  | e :: es => do
    if ← elemEq it e then return some es
    match ← pyRemove it es with
    | some es' => return some (e :: es')
    | none => return none

/-- `item in filters`. -/
def pyContains (it : FItem) : List Elem → Py Bool
  | [] => .ok false
  | e :: es => do
    if ← elemEq it e then return true
    pyContains it es

def noAttr (tp attr : String) : PyExc := .named "AttributeError" s!"'{tp}' object has no attribute '{attr}'"

/-- `_add_filter(*item, append=append)`: under the lock (which cannot fail, and whose
`_filters_mutated_lock_held` therefore cannot either), remove a duplicate and insert at the front,
or append unless present; then the version moves on. -/
def addFilter (H : Hier) (it : FItem) (append : Bool) (s : FState) : Py FState := do
  let c ← match s.cont with
    | .deleted => pure Cont.deleted
    | .list xs =>
      if !append then do
        -- `try: filters.remove(item) except ValueError: pass`: a `ValueError` from an element's
        -- `__eq__` is taken for "not in the list"
        let r ← match pyRemove it xs with
          | .ok r => pure (r.getD xs)
          | .error e => if isA H e "ValueError" then pure xs else .error e
        pure (Cont.list (.item it :: r))
      else do
        if ← pyContains it xs then pure (Cont.list xs) else pure (Cont.list (xs ++ [.item it]))
    | .tuple xs =>
      if !append then .error (noAttr "tuple" "remove")
      else do
        if ← pyContains it xs then pure (Cont.tuple xs) else .error (noAttr "tuple" "append")
  pure ⟨c, s.ver + 1⟩

/-! ## `filterwarnings`, `simplefilter`, `resetwarnings` -/

def actionNames : List String := ["error", "ignore", "always", "all", "default", "module", "once"]

/-- `if action not in {...}: raise ValueError(f"invalid action: {action!r}")`. -/
def checkAction (a : ActA) : Py String :=
  match a with
  | .str s => if s ∈ actionNames then .ok s else .error (.valueError s!"invalid action: {pyReprStr s}")
  | .obj r => .error (.valueError s!"invalid action: {r}")
  | .unhashable tp => .error (.typeError s!"cannot use '{tp}' as a set element (unhashable type: '{tp}')")

/-- `if not isinstance(lineno, int)` / `if lineno < 0`. -/
def checkLineno (l : IntA) : Py Int :=
  match l with
  | .obj => .error (.typeError "lineno must be an int")
  | .int v => if v < 0 then .error (.valueError "lineno must be an int >= 0") else .ok v

/-- `re.compile(p, flags)` when `p` is non-empty, else `None`, :282-289. -/
def compileOpt (E : FEnv) (p : String) (ci : Bool) : Py (Option Rx) :=
  if p.isEmpty then .ok none
  else do
    E.compile p ci
    return some ⟨p, ci⟩

/-- The body of `filterwarnings` before `_add_filter`, :266-289: the checks in source order, then
the patterns; the item it passes on. -/
def fwPrep (E : FEnv) (action : ActA) (message : StrA) (category : Nat) (module : StrA)
    (lineno : IntA) : Py FItem := do
  let a ← checkAction action
  let m ← match message with
    | .str m => pure m
    | .obj => .error (.typeError "message must be a string")
  if !(E.isType category && E.isWarn category) then
    .error (.typeError "category must be a Warning subclass")
  let md ← match module with
    | .str m => pure m
    | .obj => .error (.typeError "module must be a string")
  let ln ← checkLineno lineno
  let mrx ← compileOpt E m true
  let drx ← compileOpt E md false
  return ⟨a, mrx, category, drx, ln⟩

/-- `filterwarnings`, :254-291. -/
def filterwarnings (E : FEnv) (action : ActA) (message : StrA) (category : Nat) (module : StrA)
    (lineno : IntA) (append : Bool) (s : FState) : Py FState := do
  let it ← fwPrep E action message category module lineno
  addFilter E.hier it append s

/-- The body of `simplefilter` before `_add_filter`, :304-309: no category check. -/
def sfPrep (action : ActA) (category : Nat) (lineno : IntA) : Py FItem := do
  let a ← checkAction action
  let ln ← checkLineno lineno
  return ⟨a, none, category, none, ln⟩

/-- `simplefilter`, :294-310. -/
def simplefilter (H : Hier) (action : ActA) (category : Nat) (lineno : IntA) (append : Bool) (s : FState) :
    Py FState := do
  let it ← sfPrep action category lineno
  addFilter H it append s

/-- `resetwarnings`, :337-341: `del _wm._get_filters()[:]`. -/
def resetwarnings (s : FState) : Py FState :=
  match s.cont with
  | .list _ => .ok ⟨.list [], s.ver + 1⟩
  | .deleted => .ok ⟨.deleted, s.ver + 1⟩
  | .tuple _ => .error (.typeError "'tuple' object does not support item deletion")

/-! ## The version and the lock -/

def lockErr : PyExc := .named "RuntimeError" "cannot release un-acquired lock"
def notHeldErr : PyExc := .named "RuntimeError" "warnings lock is not held"

/-- The C recursive mutex (`_PyRecursiveMutex`, Python/lock.c:402-454): its owning thread, if any,
and how many times more than once that thread holds it. -/
structure LockSt where
  owner : Option Nat
  level : Nat
  deriving DecidableEq, Repr

/-- `_acquire_lock()` from thread `t`, _warnings.c:370-379 (`warnings_lock`, :259-264, and
`_PyRecursiveMutex_Lock`, lock.c:402-412): `none` while another thread holds it (the call
blocks). -/
def cAcquire (t : Nat) (l : LockSt) : Option LockSt :=
  match l.owner with
  | some u => if u = t then some ⟨some t, l.level + 1⟩ else none
  | none => some ⟨some t, 0⟩

/-- `_release_lock()` from thread `t`, :387-399 (`warnings_unlock`, :267-272, and
`_PyRecursiveMutex_TryUnlock`, lock.c:440-454): refused unless `t` holds the lock. -/
def cRelease (t : Nat) (l : LockSt) : Py LockSt :=
  if l.owner = some t then
    if l.level > 0 then .ok ⟨l.owner, l.level - 1⟩ else .ok ⟨none, 0⟩
  else .error lockErr

/-- C `_filters_mutated_lock_held()`, :1357-1377: refuses unless the lock is held by some thread
(`warnings_lock_held`, :275-278, is `PyMutex_IsLocked`). -/
def cMutatedLockHeld (l : LockSt) (v : Int) : Py Int :=
  if l.owner.isNone then .error notHeldErr else .ok (v + 1)

/-- Python `_filters_mutated_lock_held()`, _py_warnings.py:117-118: no check. -/
def pyMutatedLockHeld (v : Int) : Int := v + 1

/-- `_filters_mutated()`, :313-317, on the C module from thread `t`: `with _wm._lock:`
(`_Lock.__enter__` and `__exit__`, Lib/warnings.py:79-85, are `_acquire_lock` and
`_release_lock`). `none` while another thread holds the lock. -/
def cFiltersMutated (t : Nat) (l : LockSt) (v : Int) : Option (Py (LockSt × Int)) :=
  (cAcquire t l).map fun l1 => do
    let v' ← cMutatedLockHeld l1 v
    let l2 ← cRelease t l1
    return (l2, v')

/-! ## The initial filters list -/

/-- The ids the defaults use. -/
structure DefaultCats where
  deprecation : Nat
  pending : Nat
  importW : Nat
  resource : Nat

/-- `create_filter(category, action, modname)`, _warnings.c:78-97: `(action, None, category,
modname or None, 0)`, the module name a plain str. -/
def createFilter (cat : Nat) (action : String) (modname : Option String) : Filter :=
  { action := .str action, msg := none, cat := cat, mod := modname.map Pat.plain, ln := .int 0 }

/-- `init_filters`, :101-132: empty in a debug build, else five filters. -/
def initFilters (debug : Bool) (K : DefaultCats) : List Item :=
  if debug then []
  else [.tuple (createFilter K.deprecation "default" (some "__main__")),
        .tuple (createFilter K.deprecation "ignore" none),
        .tuple (createFilter K.pending "ignore" none),
        .tuple (createFilter K.importW "ignore" none),
        .tuple (createFilter K.resource "ignore" none)]

/-- `_setup_defaults()`, _py_warnings.py:920-928, on a filters state: nothing in a debug build
(`hasattr(sys, 'gettotalrefcount')`), else one `filterwarnings` and four `simplefilter` calls,
each with `append=1`. -/
def setupDefaults (E : FEnv) (debug : Bool) (K : DefaultCats) (s : FState) : Py FState :=
  if debug then .ok s
  else do
    let s ← filterwarnings E (.str "default") (.str "") K.deprecation (.str "__main__") (.int 0) true s
    let s ← simplefilter E.hier (.str "ignore") K.deprecation (.int 0) true s
    let s ← simplefilter E.hier (.str "ignore") K.pending (.int 0) true s
    let s ← simplefilter E.hier (.str "ignore") K.importW (.int 0) true s
    simplefilter E.hier (.str "ignore") K.resource (.int 0) true s

end PyLean.CoreLibs.Warn
