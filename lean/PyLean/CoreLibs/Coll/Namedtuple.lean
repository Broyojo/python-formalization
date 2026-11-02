import PyLean.CoreLibs.Coll.ChainMap
import PyLean.StrSearch.Model

/-!
`collections.namedtuple`, Lib/collections/__init__.py:361-533 (CPython 3.15.2).

`namedtuple` generates a class, and part of it by compiling source text:
`eval(f'lambda _cls, {arg_list}: _tuple_new(_cls, ({arg_list}))')`, :446-447. So a class is
modelled as data (`NT`), and the compiler is modelled for what it does with the names:
identifiers in source are NFKC-normalised (Python/pegen.c `_PyPegen_new_identifier`,
Doc/reference/lexical_analysis.rst), the constants `None`, `True`, `False` are refused by
`_PyAST_Validate` (Python/ast.c `validate_name`), and a repeated parameter is a `SyntaxError`
from Python/symtable.c. The other uses of the field names, the class namespace, `_fields`,
`_asdict`, are plain strings, not normalised.

`str.isidentifier` and the NFKC map come from the Unicode database, so they are a
parameter `UniId`.

Field names are `str` after `map(str, field_names)`. `type(name) is not str` (:406) needs a
`__str__` returning a subclass, and `_sys.intern` refuses that for the type name; it is not
modelled. `__module__` and the `_tuplegetter` descriptors are out of scope. Values are abstract.
-/

namespace PyLean.CoreLibs.Coll

open PyLean

/-- What the Unicode database supplies. -/
structure UniId where
  isidentifier : String → Bool
  /-- `unicodedata.normalize('NFKC', s)`. -/
  nfkc : String → String

/-- `keyword.kwlist`, Lib/keyword.py. -/
def kwlist : List String :=
  ["False", "None", "True", "and", "as", "assert", "async", "await", "break", "class", "continue",
   "def", "del", "elif", "else", "except", "finally", "for", "from", "global", "if", "import", "in",
   "is", "lambda", "nonlocal", "not", "or", "pass", "raise", "return", "try", "while", "with", "yield"]

/-- `_iskeyword`. -/
def iskeyword (s : String) : Bool := kwlist.contains s

/-- `name.startswith('_')`. -/
def startsUnderscore (s : String) : Bool := s.toList.head? == some '_'

/-- `f'_{index}'`. -/
def posName (i : Nat) : String := "_" ++ toString i

/-- The `field_names` argument. -/
inductive FieldNames where
  | str (s : String)
  | list (l : List String)
  deriving Repr, DecidableEq

/-- `field_names.replace(',', ' ').split()`, :389. -/
def splitNames (s : String) : List String :=
  let cps := s.toList.map (fun c => if c = ',' then 32 else c.toNat)
  match StrSearch.strSplit cps none (-1) with
  | .ok l => l.map (fun w => String.ofList (w.map Char.ofNat))
  | .error _ => []

/-- :388-390. -/
def fieldList : FieldNames → List String
  | .str s => splitNames s
  | .list l => l

/-- The `if rename:` loop, :393-401. `seen` gets the original name. -/
def renameLoop (U : UniId) (seen : List String) (index : Nat) : List String → List String
  | [] => []
  | name :: t =>
    let bad := !U.isidentifier name || iskeyword name || startsUnderscore name || seen.contains name
    (if bad then posName index else name) :: renameLoop U (name :: seen) (index + 1) t

/-- The `for name in [typename] + field_names` loop, :403-411. -/
def checkNames (U : UniId) : List String → Py Unit
  | [] => .ok ()
  | name :: t =>
    if !U.isidentifier name then
      .error (.valueError ("Type names and field names must be valid identifiers: " ++ pyStrRepr name))
    else if iskeyword name then
      .error (.valueError ("Type names and field names cannot be a keyword: " ++ pyStrRepr name))
    else checkNames U t

/-- The second `seen` loop, :413-420. -/
def checkSeen (rename : Bool) (seen : List String) : List String → Py Unit
  | [] => .ok ()
  | name :: t =>
    if startsUnderscore name && !rename then
      .error (.valueError ("Field names cannot start with an underscore: " ++ pyStrRepr name))
    else if seen.contains name then
      .error (.valueError ("Encountered duplicate field name: " ++ pyStrRepr name))
    else checkSeen rename (name :: seen) t

/-- The first parameter name repeated in `seen ++ l`, the order `symtable_add_def` meets them. -/
def firstDup (seen : List String) : List String → Option String
  | [] => none
  | a :: t => if seen.contains a then some a else firstDup (a :: seen) t

/-- What `eval(code, namespace)`, :447-448, does with the field names: returns the parameter
names of `__new__`, `_cls` first dropped. -/
def compileNew (U : UniId) (names : List String) : Py (List String) :=
  let args := names.map U.nfkc
  match args.find? (fun a => a = "None" ∨ a = "True" ∨ a = "False") with
  | some c => .error (.valueError s!"identifier field can't represent '{c}' constant")
  | none =>
    match firstDup ["_cls"] args with
    | some a =>
      .error (.named "SyntaxError" s!"duplicate parameter '{a}' in function definition (<string>, line 1)")
    | none => .ok args

/-- `arg_list`, :433-435. -/
def argListOf (names : List String) : String :=
  ", ".intercalate names ++ (if names.length = 1 then "," else "")

/-- The class a `namedtuple` call returns, as data. -/
structure NT (ν : Type) where
  typename : String
  /-- `_fields`. -/
  fields : List String
  /-- The parameters of `__new__` after `_cls`: `__new__.__code__.co_varnames[1:]`. -/
  args : List String
  /-- `__new__.__defaults__`. -/
  defaults : List ν
  /-- `_field_defaults`. -/
  fieldDefaults : D String ν
  doc : String
  newDoc : String

/-- `dict(reversed(list(zip(reversed(field_names), reversed(defaults)))))`, :427-428. -/
def fieldDefaultsOf {ν : Type} (names : List String) (d : List ν) : D String ν :=
  D.update [] (names.reverse.zip d.reverse).reverse

/-- `namedtuple(typename, field_names, rename=rename, defaults=defaults)`, :388-534. -/
def namedtuple {ν : Type} (U : UniId) (typename : String) (fn : FieldNames) (rename : Bool)
    (defaults : Option (List ν)) : Py (NT ν) := do
  let names := fieldList fn
  let names := if rename then renameLoop U [] 0 names else names
  checkNames U (typename :: names)
  checkSeen rename [] names
  let d := defaults.getD []
  if d.length > names.length then
    throw (.typeError "Got more default values than field names")
  let args ← compileNew U names
  let arg_list := argListOf names
  return {
    typename, fields := names, args, defaults := d,
    fieldDefaults := fieldDefaultsOf names d,
    doc := typename ++ "(" ++ arg_list ++ ")",
    newDoc := "Create new instance of " ++ typename ++ "(" ++ arg_list ++ ")" }

variable {ν : Type}

/-! ### Instances: `__new__`, by CPython's call binding -/

/-- The value of each parameter not filled positionally, from `index i`: a keyword, else
`__defaults__` (which belong to the last `dl` of `n` parameters), else a `TypeError`. -/
def fillRest (kw : D String ν) (defaults : List ν) (n : Nat) : Nat → List String → Py (List ν)
  | _, [] => .ok []
  | i, x :: t => do
    let v ← match D.get? kw x with
      | some v => .ok v
      | none =>
        if i + defaults.length ≥ n then
          match defaults[i + defaults.length - n]? with
          | some v => .ok v
          | none => .error (.typeError "~missing argument")
        else .error (.typeError "~missing argument")
    let r ← fillRest kw defaults n (i + 1) t
    return v :: r

/-- Every keyword names a parameter not already taken by the first `np` positionals. -/
def checkKw (args : List String) (np : Nat) : D String ν → Py Unit
  | [] => .ok ()
  | p :: t =>
    if !args.contains p.1 then .error (.typeError "~unexpected keyword argument")
    else if (args.take np).contains p.1 then .error (.typeError "~multiple values")
    else checkKw args np t

/-- `T(*pos, **kw)`: binding to the parameters of `__new__`, `initialize_locals` in
Python/ceval.c. Every failure is a `TypeError`, whose text is not modelled. Keywords
match parameter names exactly: no normalisation happens at run time. -/
def ntCall (T : NT ν) (pos : List ν) (kw : D String ν) : Py (List ν) := do
  let n := T.args.length
  if pos.length > n then throw (.typeError "~too many positional arguments")
  checkKw T.args pos.length kw
  let r ← fillRest kw T.defaults n pos.length (T.args.drop pos.length)
  return pos ++ r

/-- `_make`, :155-160. -/
def ntMake (T : NT ν) (items : List ν) : Py (List ν) :=
  if items.length ≠ T.fields.length then
    .error (.typeError s!"Expected {T.fields.length} arguments, got {items.length}")
  else .ok items

/-- `_map(kwds.pop, field_names, self)`: the new values, and what is left in `kwds`. -/
def replLoop (kwds : D String ν) : List String → List ν → List ν × D String ν
  | n :: ns, v :: vs =>
    let (x, kwds') := match D.get? kwds n with
      | some w => (w, D.del kwds n)
      | none => (v, kwds)
    let (r, k) := replLoop kwds' ns vs
    (x :: r, k)
  | _, _ => ([], kwds)

/-- `_replace`, Lib/collections/__init__.py:463-467, also `__replace__`. `rk` is `repr` on the leftover list. -/
def ntReplace (T : NT ν) (vals : List ν) (kwds : D String ν) : Py (List ν) := do
  let (r, left) := replLoop kwds T.fields vals
  let result ← ntMake T r
  if !left.isEmpty then
    throw (.typeError ("Got unexpected field names: [" ++
      ", ".intercalate (left.map (fun p => pyStrRepr p.1)) ++ "]"))
  return result

/-- `__repr__`, :182-184. -/
def ntRepr (rv : ν → String) (T : NT ν) (vals : List ν) : String :=
  T.typename ++ "(" ++ ", ".intercalate ((T.fields.zip vals).map (fun p => p.1 ++ "=" ++ rv p.2)) ++ ")"

/-- `_asdict`, :186-188: `dict(zip(self._fields, self))`. -/
def ntAsdict (T : NT ν) (vals : List ν) : D String ν := D.update [] (T.fields.zip vals)

/-- `getattr(p, name)`: the descriptors live under the raw field name, :221-223. -/
def ntGetattr (T : NT ν) (vals : List ν) (name : String) : Option ν :=
  D.get? (T.fields.zip vals) name

/-- `p.name` written in source: the compiler normalises `name` first. -/
def ntSourceAttr (U : UniId) (T : NT ν) (vals : List ν) (name : String) : Option ν :=
  ntGetattr T vals (U.nfkc name)

end PyLean.CoreLibs.Coll
