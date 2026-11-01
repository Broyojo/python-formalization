import PyLean.TextLibs.Bits
import PyLean.Binary64.Dtoa

/-!
Model of `Modules/_csv.c` and of `Dialect`, `DictReader` and `DictWriter` in `Lib/csv.py`, CPython
3.14.7. `Sniffer` is not modelled. Characters are code points, and `EOL` and `NOT_SET` are the same
out-of-range `Py_UCS4` sentinels as in the source, so each comparison reads as it does there.

Everything the C code calls back into can fail or re-enter, so nothing here takes a plain list of
inputs. An object is an `Obj`, whose truth value, hash, attributes, `str()` and iterator are each
fallible, and an iterator is a script of `Step`s. Between two results a script may perform an `Eff`:
`next()` on the reader that is reading it, `field_size_limit`, or `writerow` on the writer that is
writing it. A script is the whole of what such an object can do that this C code can observe, so a
quantifier over scripts is one over those objects. Effects run through the same mutual recursion as
the outer call, with the object's state threaded through, which is what makes re-entry visible.

The one thing outside `Py` is `CRASH`, for a NULL dereference: the process dies, and nothing that
catches exceptions runs. It is written as an exception only so that it can be stated and compared.
-/

namespace PyLean.TextLibs.Csv

open PyLean PyLean.TextLibs

/-- `csv.Error`. -/
def csvErr (m : String) : PyExc := .named "Error" m

/-- A segmentation fault, as the difftest reports a killed child. Not a Python exception. -/
def CRASH : PyExc := .named "SegmentationFault" ""

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

/-- The names C prints for a type: `%T`, `tp_name` and `_PyType_Name`. -/
structure TyName where
  full : String
  tp : String
  short : String
  deriving Repr, DecidableEq, Inhabited

/-- How a `str`-keyed dict sees an object. `eqRaises` is `__eq__` raising during a probe, which
needs a stored key with the same hash; quantifying over `KeyProbe` covers that either way. -/
inductive KeyProbe where
  | hashRaises (e : PyExc)
  | eqRaises (e : PyExc)
  | noMatch
  | equals (k : List Nat)
  /-- It hashes as `k` and its `__eq__` raises, so a dict raises only if it holds a key equal to `k`. -/
  | eqRaisesAt (k : List Nat) (e : PyExc)
  deriving Repr, DecidableEq, Inhabited

mutual
  /-- A call back into `_csv` from inside a callback. Whatever it raises, the callback catches: a
  callback that lets it propagate is the same effect followed by `Step.raise`. -/
  inductive Eff where
    /-- `next(reader)` on the reader reading this iterator. -/
    | advance
    /-- `csv.field_size_limit(n)`. -/
    | setLimit (n : Obj)
    /-- `writer.writerow(row)` on the writer that called back. -/
    | writerow (row : Obj)

  /-- One event of an iterator: an effect, or the end of a `__next__` call. -/
  inductive Step where
    | eff (e : Eff)
    | ret (o : Obj)
    | raise (e : PyExc)
    | stop

  /-- A Python object as this module sees it. -/
  inductive Obj where
    /-- An exact `str`. -/
    | str (cps : List Nat)
    /-- A subclass of `str`: `PyUnicode_Check` holds, and hashing is its own. `__bool__` and
    `__iter__` of a subclass are not listed, because `other` already covers them wherever a string
    is not required. -/
    | strSub (ty : TyName) (cps : List Nat) (key : KeyProbe)
    | none
    /-- An exact `int`. -/
    | int (n : Int)
    /-- A `bool`, which is an `int` subclass but not `PyLong_CheckExact`. -/
    | bool (b : Bool)
    /-- An instance of `_csv.Dialect` with nothing of Python's in it: no class attribute shadows a
    getter, `tp_init` is `object_init`, and `lineterminator` is the `str` in `d`. -/
    | dialect (ty : TyName) (d : Dialect)
    /-- Any instance. `lt` is the object in the `lineterminator` slot, `NULL` until `_set_str` ran,
    `attrs` what the subclass's own attributes do, and `init` what its `tp_init` does when
    `type_call` runs it on this instance again. -/
    | dialectX (ty : TyName) (d : Dialect) (lt : Option Obj) (attrs : List (String × Except PyExc Obj))
        (init : Except PyExc Unit)
    /-- Anything else, by what it does: `PyObject_IsTrue`, dict lookup, attributes,
    `PyNumber_Check`, `PyObject_Str` and `PyObject_GetIter`. -/
    | other (ty : TyName) (truth : Except PyExc Bool) (key : KeyProbe)
        (attrs : List (String × Except PyExc Obj)) (number : Bool)
        (strv : List Eff × Except PyExc (List Nat)) (iter : Except PyExc (List Step))
    /-- A callable; each call takes the next item, and when they run out it returns `None`. -/
    | func (calls : List (List Eff × Except PyExc Obj))
end

instance : Inhabited Obj := ⟨.none⟩

def builtinTy (n : String) : TyName := ⟨n, n, n⟩
def dialectTy : TyName := ⟨"_csv.Dialect", "_csv.Dialect", "Dialect"⟩

def Obj.ty : Obj → TyName
  | .str _ => builtinTy "str"
  | .strSub t _ _ => t
  | .none => builtinTy "NoneType"
  | .int _ => builtinTy "int"
  | .bool _ => builtinTy "bool"
  | .dialect t _ => t
  | .dialectX t _ _ _ _ => t
  | .other t _ _ _ _ _ _ => t
  | .func _ => builtinTy "function"

/-- `PyObject_TypeCheck(o, dialect_type)`, with the settings in the C struct. -/
def Obj.asDialect : Obj → Option Dialect
  | .dialect _ d => some d
  | .dialectX _ d _ _ _ => some d
  | _ => Option.none

/-- `PyUnicode_Check`, with the text. -/
def Obj.asStr : Obj → Option (List Nat)
  | .str s => some s
  | .strSub _ s _ => some s
  | _ => Option.none

/-- `PyObject_IsTrue`. -/
def Obj.isTrue : Obj → Py Bool
  | .str c => .ok !c.isEmpty
  | .strSub _ c _ => .ok !c.isEmpty
  | .none => .ok false
  | .int n => .ok (n != 0)
  | .bool b => .ok b
  | .dialect _ _ => .ok true
  | .dialectX _ _ _ _ _ => .ok true
  | .other _ t _ _ _ _ _ => t
  | .func _ => .ok true

/-- Looking the object up in a dict whose keys are exact strings. -/
def Obj.dictKey : Obj → KeyProbe
  | .str s => .equals s
  | .strSub _ _ k => k
  | .other _ _ k _ _ _ _ => k
  | _ => .noMatch

/-- `dict_unhashable_type`, `Objects/dictobject.c:2352-2366`: a plain `TypeError` from `__hash__`
is re-raised with the key's type in it. -/
def dictHashErr (o : Obj) : PyExc → PyExc
  | .typeError m => .typeError s!"cannot use '{o.ty.full}' as a dict key ({m})"
  | e => e

/-- A lookup in a `str`-keyed dict that holds `present`: the matching key, or the exception. -/
def Obj.dictFind (o : Obj) (present : List Nat → Bool) : Py (Option (List Nat)) :=
  match o.dictKey with
  | .hashRaises e => .error (dictHashErr o e)
  | .eqRaises e => .error e
  | .noMatch => .ok Option.none
  | .equals k => .ok (if present k then some k else Option.none)
  | .eqRaisesAt k e => if present k then .error e else .ok Option.none

/-- `PyObject_Str` for an `int`, with the default limit of `sys.set_int_max_str_digits`. -/
def intText (n : Int) : Py (List Nat) :=
  let t := (toString n.natAbs).toList.map Char.toNat
  if t.length > 4300 then
    .error (.valueError "Exceeds the limit (4300 digits) for integer string conversion; use sys.set_int_max_str_digits() to increase the limit")
  else .ok (if n < 0 then 45 :: t else t)

def strToList (s : String) : List Nat := s.toList.map Char.toNat

/-- `PyObject_Str`: what it does first, and the text. -/
def Obj.pyStr : Obj → List Eff × Py (List Nat)
  | .str s => ([], .ok s)
  | .strSub _ s _ => ([], .ok s)
  | .none => ([], .ok (strToList "None"))
  | .int n => ([], intText n)
  | .bool b => ([], .ok (strToList (if b then "True" else "False")))
  | .dialect t _ => ([], .ok (strToList s!"<{t.tp} object>"))
  | .dialectX t _ _ _ _ => ([], .ok (strToList s!"<{t.tp} object>"))
  | .other _ _ _ _ _ s _ => s
  | .func _ => ([], .ok (strToList "<function>"))

/-- `PyNumber_Check`. -/
def Obj.isNumber : Obj → Bool
  | .int _ | .bool _ => true
  | .other _ _ _ _ n _ _ => n
  | _ => false

/-- `PyObject_GetIter`. -/
def Obj.getIter (o : Obj) : Py (List Step) :=
  let notIter : Py (List Step) := .error (.typeError s!"'{o.ty.tp}' object is not iterable")
  match o with
  | .str s => .ok (s.map fun c => .ret (.str [c]))
  | .strSub _ s _ => .ok (s.map fun c => .ret (.str [c]))
  | .other _ _ _ _ _ _ i => i
  | _ => notIter

/-- An iterator object from a script. -/
def iterObj (steps : List Step) : Obj :=
  .other ⟨"iterator", "iterator", "iterator"⟩ (.ok true) .noMatch [] false ([], .ok []) (.ok steps)

/-- `AttributeError`. -/
def attrErr (t : TyName) (n : String) : PyExc :=
  .named "AttributeError" s!"'{t.tp}' object has no attribute '{n}'"

/-- `_set_bool`, `Modules/_csv.c:217-229`. -/
def setBool (src : Option Obj) (dflt : Bool) : Py Bool :=
  match src with
  | Option.none => .ok dflt
  | some o => o.isTrue

/-- `_set_int`, `Modules/_csv.c:231-250`. -/
def setInt (name : String) (src : Option Obj) (dflt : Int) : Py Int :=
  match src with
  | Option.none => .ok dflt
  | some (.int n) =>
    if n < -(2 ^ 31) ∨ n > 2 ^ 31 - 1 then
      .error (.overflowError "Python int too large to convert to C int")
    else .ok n
  | some o => .error (.typeError s!"\"{name}\" must be an integer, not {o.ty.full}")

/-- `_set_char_or_none`, `Modules/_csv.c:252-283`. -/
def setCharOrNone (name : String) (src : Option Obj) (dflt : Nat) : Py Nat :=
  match src with
  | Option.none => .ok dflt
  | some .none => .ok NOT_SET
  | some o =>
    match o.asStr with
    | Option.none =>
      .error (.typeError s!"\"{name}\" must be a unicode character or None, not {o.ty.full}")
    | some [c] => .ok c
    | some s =>
      .error (.typeError s!"\"{name}\" must be a unicode character or None, not a string of length {s.length}")

/-- `_set_char`, `Modules/_csv.c:285-313`. -/
def setChar (name : String) (src : Option Obj) (dflt : Nat) : Py Nat :=
  match src with
  | Option.none => .ok dflt
  | some o =>
    match o.asStr with
    | Option.none => .error (.typeError s!"\"{name}\" must be a unicode character, not {o.ty.full}")
    | some [c] => .ok c
    | some s =>
      .error (.typeError s!"\"{name}\" must be a unicode character, not a string of length {s.length}")

/-- `_set_str`, `Modules/_csv.c:315-333`. -/
def setStr (name : String) (src : Option Obj) (dflt : List Nat) : Py (List Nat) :=
  match src with
  | Option.none => .ok dflt
  | some o =>
    match o.asStr with
    | some s => .ok s
    | Option.none => .error (.typeError s!"\"{name}\" must be a string, not {o.ty.full}")

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

/-- The arguments of `dialect_new` after `PyArg_ParseTupleAndKeywords`, each `NULL` if absent. -/
structure DArgs where
  dialect : Option Obj := Option.none
  delimiter : Option Obj := Option.none
  doublequote : Option Obj := Option.none
  escapechar : Option Obj := Option.none
  lineterminator : Option Obj := Option.none
  quotechar : Option Obj := Option.none
  quoting : Option Obj := Option.none
  skipinitialspace : Option Obj := Option.none
  strict : Option Obj := Option.none
  deriving Inhabited

/-- `quotechar == Py_None`. -/
def isNoneArg : Option Obj → Bool
  | some .none => true
  | _ => false

/-- Validation and conversion, `Modules/_csv.c:527-560`, in that order. -/
def dialectBuild (a : DArgs) : Py Dialect := do
  let delimiter ← setChar "delimiter" a.delimiter 44
  let doublequote ← setBool a.doublequote true
  let escapechar ← setCharOrNone "escapechar" a.escapechar NOT_SET
  let lineterminator ← setStr "lineterminator" a.lineterminator [13, 10]
  let quotechar ← setCharOrNone "quotechar" a.quotechar 34
  let quoting ← setInt "quoting" a.quoting QUOTE_MINIMAL
  let skipinitialspace ← setBool a.skipinitialspace false
  let strict ← setBool a.strict false
  checkQuoting quoting
  let quoting := if isNoneArg a.quotechar ∧ a.quoting.isNone then QUOTE_NONE else quoting
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

/-- What `Dialect_get_lineterminator` hands back: the object in the slot itself, which a value
compare could not tell from a copy, or `NULL`. -/
inductive LtRes where
  | stored (o : Obj)
  | null

/-- `Dialect_get_lineterminator`, `Modules/_csv.c:182-187`: `Py_XNewRef(self->lineterminator)`. The
slot is `NULL` on an instance `_set_str` has not reached, which a subclass `__del__` can see when
`dialect_new` fails before `:530`. -/
def dialectGetLineterminator (slot : Option Obj) : LtRes :=
  match slot with
  | some o => .stored o
  | Option.none => .null

/-- The getter returning `NULL` with no exception set, as the interpreter reports it. -/
def nullReturn : PyExc := .named "SystemError" "error return without exception set"

/-- The attribute read of `LOAD_ATTR` on the getter. -/
def ltAttr : LtRes → Py Obj
  | .stored o => .ok o
  | .null => .error nullReturn
/-- `Dialect_get_delimiter`, `Modules/_csv.c:189-194`. -/
def dialectGetDelimiter (d : Dialect) : Obj := getCharOrNone d.delimiter
/-- `Dialect_get_escapechar`, `Modules/_csv.c:196-201`. -/
def dialectGetEscapechar (d : Dialect) : Obj := getCharOrNone d.escapechar
/-- `Dialect_get_quotechar`, `Modules/_csv.c:203-208`. -/
def dialectGetQuotechar (d : Dialect) : Obj := getCharOrNone d.quotechar
/-- `Dialect_get_quoting`, `Modules/_csv.c:210-215`. -/
def dialectGetQuoting (d : Dialect) : Obj := .int d.quoting

/-- `PyObject_GetAttrString` on a dialect: `Dialect_getsetlist` and `Dialect_memberlist`,
`Modules/_csv.c:377-393`. `slot` is what the `lineterminator` slot holds. -/
def dialectGetattr (d : Dialect) (slot : Option Obj) (t : TyName) (n : String) : Py Obj :=
  match n with
  | "delimiter" => .ok (dialectGetDelimiter d)
  | "escapechar" => .ok (dialectGetEscapechar d)
  | "lineterminator" => ltAttr (dialectGetLineterminator slot)
  | "quotechar" => .ok (dialectGetQuotechar d)
  | "quoting" => .ok (dialectGetQuoting d)
  | "doublequote" => .ok (.bool d.doublequote)
  | "skipinitialspace" => .ok (.bool d.skipinitialspace)
  | "strict" => .ok (.bool d.strict)
  | _ => .error (attrErr t n)

/-- `PyObject_GetAttrString`. -/
def Obj.getattr (o : Obj) (n : String) : Py Obj :=
  match o with
  | .dialect t d => dialectGetattr d (some (.str d.lineterminator)) t n
  | .dialectX t d lt attrs _ =>
    match attrs.lookup n with
    | some r => r
    | Option.none => dialectGetattr d lt t n
  | .other t _ _ attrs _ _ _ =>
    match attrs.lookup n with
    | some r => r
    | Option.none => .error (attrErr t n)
  | _ => .error (attrErr o.ty n)

/-- `DIALECT_GETATTR`, `Modules/_csv.c:504-511`: any failure is cleared. -/
def getattrOr (o : Obj) (v : Option Obj) (n : String) : Option Obj :=
  match v with
  | some x => some x
  | Option.none =>
    match o.getattr n with
    | .ok x => some x
    | .error _ => Option.none

/-- The attributes copied from a dialect argument, `Modules/_csv.c:512-519`. -/
def dialectAttrs (o : Obj) (a : DArgs) : DArgs :=
  { a with
    delimiter := getattrOr o a.delimiter "delimiter"
    doublequote := getattrOr o a.doublequote "doublequote"
    escapechar := getattrOr o a.escapechar "escapechar"
    lineterminator := getattrOr o a.lineterminator "lineterminator"
    quotechar := getattrOr o a.quotechar "quotechar"
    quoting := getattrOr o a.quoting "quoting"
    skipinitialspace := getattrOr o a.skipinitialspace "skipinitialspace"
    strict := getattrOr o a.strict "strict" }

/-- The registry, `module_state->dialects`: a dict in insertion order. Each key is the object that
was registered, which a `str` subclass keeps with its own `__hash__` and `__eq__`. -/
abbrev Registry := List (Obj × Obj)

/-- Does a stored key equal a looked-up text? A key whose hash differs is never compared. -/
def keyAnswers (key : Obj) (k : List Nat) : Py Bool :=
  match key.dictKey with
  | .equals j => .ok (j == k)
  | .eqRaises e => .error e
  | .eqRaisesAt j e => if j == k then .error e else .ok false
  | _ => .ok false

/-- A dict lookup of a text: the entry, or the exception of a stored key's `__eq__`. -/
def regFind : Registry → List Nat → Py (Option (Obj × Obj))
  | [], _ => .ok Option.none
  | (key, v) :: r, k =>
    match keyAnswers key k with
    | .error e => .error e
    | .ok true => .ok (some (key, v))
    | .ok false => regFind r k

/-- A dict lookup of any object, `PyDict_GetItemRef`. -/
def regLookup (r : Registry) (name : Obj) : Py (Option (Obj × Obj)) :=
  match name.dictKey with
  | .hashRaises e => .error (dictHashErr name e)
  | .eqRaises e => .error e
  | .noMatch => .ok Option.none
  | .equals k => regFind r k
  | .eqRaisesAt k e =>
    match regFind r k with
    | .ok (some _) => .error e
    | x => x

/-- `get_dialect_from_registry`, `Modules/_csv.c:162-170`: `PyDict_GetItemRef` returning `-1`
leaves its exception, and `0` raises `csv.Error`. -/
def getDialectFromRegistry (r : Registry) (name : Obj) : Py Obj :=
  match regLookup r name with
  | .error e => .error e
  | .ok (some (_, d)) => .ok d
  | .ok Option.none => .error (csvErr "unknown dialect")

/-- `_csv_get_dialect_impl`, `Modules/_csv.c:1676-1681`. -/
def csvGetDialect (r : Registry) (name : Obj) : Py Obj := getDialectFromRegistry r name

/-- A positional and keyword argument list. Keyword names are unique, as in a dict. -/
structure Args where
  pos : List Obj := []
  kw : List (List Nat × Obj) := []
  deriving Inhabited

/-- `dialect_kws`, `Modules/_csv.c:405-416`. -/
def dialectKws : List String :=
  ["dialect", "delimiter", "doublequote", "escapechar", "lineterminator", "quotechar", "quoting",
   "skipinitialspace", "strict"]

/-- `vgetargskeywords`, `Python/getargs.c:1575-1879`, for the format `|OOOOOOOOO`: the object for
each entry of `dialect_kws`, positional arguments first. -/
def parseDialectArgs (a : Args) : Py (List (Option Obj)) :=
  let len := dialectKws.length
  let nargs := a.pos.length
  let nkw := a.kw.length
  if nargs + nkw > len then
    .error (.typeError s!"function takes at most {len} {if nargs == 0 then "keyword " else ""}arguments ({nargs + nkw} given)")
  else
    let slot (i : Nat) (name : String) : Option Obj :=
      if i < nargs then a.pos[i]? else a.kw.lookup (strToList name)
    let vals := dialectKws.zipIdx.map fun (n, i) => slot i n
    let used := (dialectKws.drop nargs).countP fun n => (a.kw.lookup (strToList n)).isSome
    if nkw - used > 0 then
      match (dialectKws.take nargs).zipIdx.find? (fun (n, _) => (a.kw.lookup (strToList n)).isSome) with
      | some (n, i) => .error (.typeError s!"argument for function given by name ('{n}') and position ({i + 1})")
      | Option.none => .error (.typeError "~this function got an unexpected keyword argument")
    else .ok vals

def argsOf : List (Option Obj) → DArgs
  | [a, b, c, d, e, f, g, h, i] => ⟨a, b, c, d, e, f, g, h, i⟩
  | _ => {}

/-- What `dialect_new` returns: the object it was given, or a new one. A result of `same` is the
same object as the argument, which equal contents would not show. `lt` is the object stored in the
slot of a new one. -/
inductive DRes where
  | same (o : Obj) (d : Dialect)
  | fresh (ty : TyName) (d : Dialect) (lt : Obj)
  deriving Inhabited

def DRes.dialect : DRes → Dialect
  | .same _ d | .fresh _ d _ => d

def DRes.obj : DRes → Obj
  | .same o _ => o
  | .fresh t d lt => .dialectX t d (some lt) [] (.ok ())

/-- The object `_set_str` stores: the argument itself, or the default. -/
def ltObj (a : DArgs) : Obj := a.lineterminator.getD (.str [13, 10])

def dialectFresh (ty : TyName) (a : DArgs) : Py DRes := do
  return .fresh ty (← dialectBuild a) (ltObj a)

/-- `dialect_new`, `Modules/_csv.c:434-575`. `ty` is the type being instantiated. -/
def dialectNew (r : Registry) (ty : TyName) (args : Args) : Py DRes := do
  let a := argsOf (← parseDialectArgs args)
  let dialect? ←
    match a.dialect with
    | Option.none => pure Option.none
    | some o =>
      match o.asStr with
      | some _ => some <$> getDialectFromRegistry r o
      | Option.none => pure (some o)
  let noOverrides := a.delimiter.isNone && a.doublequote.isNone && a.escapechar.isNone &&
    a.lineterminator.isNone && a.quotechar.isNone && a.quoting.isNone &&
    a.skipinitialspace.isNone && a.strict.isNone
  match dialect? with
  | Option.none => dialectFresh ty a
  | some o =>
    match o.asDialect with
    | some d => if noOverrides then return .same o d else dialectFresh ty (dialectAttrs o a)
    | Option.none => dialectFresh ty (dialectAttrs o a)

/-- `tp_init` in `type_call`, `Objects/typeobject.c:2382-2384`. It runs on whatever `tp_new` returned.
A new `_csv.Dialect` has `object_init`, and so does a reused instance with nothing of Python's in it.
A reused subclass instance runs its own `__init__`, with the arguments of this call. -/
def tpInit (res : DRes) : Py DRes :=
  match res with
  | .same (.dialectX _ _ _ _ (.error e)) _ => .error e
  | _ => .ok res

/-- `PyObject_Call(type, ...)` for `_csv.Dialect`. -/
def typeCall (r : Registry) (args : Args) : Py DRes := do
  tpInit (← dialectNew r dialectTy args)

/-- `_call_dialect`, `Modules/_csv.c:642-652`. -/
def callDialect (r : Registry) (inst : Option Obj) (kw : List (List Nat × Obj)) : Py DRes :=
  match inst with
  | some o => typeCall r ⟨[o], kw⟩
  | Option.none => typeCall r ⟨[], kw⟩

/-- `Dialect_reduce`, `Modules/_csv.c:582-587`. -/
def dialectReduce (t : TyName) : Py Unit := .error (.typeError s!"cannot pickle '{t.short}' instances")

/-- `o.__reduce_ex__(protocol)` or `o.__reduce__()` on a dialect: the class's own if it has one, and
`Dialect_reduce` otherwise, which is `METH_VARARGS` and ignores its arguments. -/
def dialectPickle (o : Obj) (method : String) : Py Unit :=
  match o with
  | .dialectX t _ _ attrs _ =>
    match attrs.lookup method with
    | some (.ok _) => .ok ()
    | some (.error e) => .error e
    | Option.none => dialectReduce t
  | _ => dialectReduce o.ty

/-- `Dialect._validate`, `Lib/csv.py:111-116`: `_Dialect(self)`, with `TypeError` re-raised as
`csv.Error`. -/
def dialectValidate (r : Registry) (self : Obj) : Py Unit :=
  match dialectNew r dialectTy ⟨[self], []⟩ with
  | .ok _ => .ok ()
  | .error (.typeError m) => .error (csvErr m)
  | .error e => .error e

/-- `Dialect.__init__`, `Lib/csv.py:106-109`. `_valid` is only stored. -/
def dialectInit (r : Registry) (self : Obj) : Py Unit := dialectValidate r self

/-- The attributes of the `Lib/csv.py` dialect classes, `Lib/csv.py:118-141`. -/
def dialectClass (name : String) (delimiter lineterminator : List Nat) (quoting : Int) : Obj :=
  .other ⟨name, name, name⟩ (.ok true) .noMatch
    [("delimiter", .ok (.str delimiter)), ("quotechar", .ok (.str [34])), ("escapechar", .ok .none),
     ("doublequote", .ok (.bool true)), ("skipinitialspace", .ok (.bool false)),
     ("lineterminator", .ok (.str lineterminator)), ("quoting", .ok (.int quoting))]
    false ([], .ok []) (.error (.typeError s!"'{name}' object is not iterable"))

def excel : Dialect := ⟨true, false, false, QUOTE_MINIMAL, 44, 34, NOT_SET, [13, 10]⟩
def excelTab : Dialect := { excel with delimiter := 9 }
def unixDialect : Dialect := ⟨true, false, false, QUOTE_ALL, 44, 34, NOT_SET, [10]⟩

/-- The registry after `import csv`. -/
def initialRegistry : Registry :=
  [(.str (strToList "excel"), .dialect dialectTy excel),
   (.str (strToList "excel-tab"), .dialect dialectTy excelTab),
   (.str (strToList "unix"), .dialect dialectTy unixDialect)]

/-- `PyArg_UnpackTuple(args, name, 1, 2, ...)`. -/
def unpack12 (name : String) : List Obj → Py (Obj × Option Obj)
  | [] => .error (.typeError s!"{name} expected at least 1 argument, got 0")
  | [a] => .ok (a, Option.none)
  | [a, b] => .ok (a, some b)
  | l => .error (.typeError s!"{name} expected at most 2 arguments, got {l.length}")

/-- `PyDict_SetItem` of a text: an equal key keeps its place and its key object, and a new key goes
last, as the object given. -/
def regPut (name d : Obj) : Registry → List Nat → Py Registry
  | [], _ => .ok [(name, d)]
  | (key, v) :: r, k =>
    match keyAnswers key k with
    | .error e => .error e
    | .ok true => .ok ((key, d) :: r)
    | .ok false => do return (key, v) :: (← regPut name d r k)

/-- `PyDict_SetItem`. -/
def regSet (r : Registry) (name d : Obj) : Py Registry :=
  match name.dictKey with
  | .hashRaises e => .error (dictHashErr name e)
  | .eqRaises e => .error e
  | .noMatch => .ok (r ++ [(name, d)])
  | .equals k => regPut name d r k
  | .eqRaisesAt k e =>
    match regFind r k with
    | .error e' => .error e'
    | .ok (some _) => .error e
    | .ok Option.none => .ok (r ++ [(name, d)])

/-- `csv_register_dialect`, `Modules/_csv.c:1618-1641`. `_call_dialect` at `:1632` can run Python: a
`__bool__`, an attribute of the dialect object, a subclass `__init__`. `during` is what those did to
the registry, for any `during`; `PyDict_SetItem` at `:1635` sees the result, and a failed call leaves
it there. The lookup of a string dialect happens first, in the registry as it stood. -/
def csvRegisterDialect (r : Registry) (during : Registry → Registry) (args : Args) : Registry × Py Unit :=
  match unpack12 "register_dialect" args.pos with
  | .error e => (r, .error e)
  | .ok (name, dialectObj) =>
    match name.asStr with
    | Option.none => (r, .error (.typeError "dialect name must be a string"))
    | some _ =>
      match callDialect r dialectObj args.kw with
      | .error e => (during r, .error e)
      | .ok d =>
        match regSet (during r) name d.obj with
        | .error e => (during r, .error e)
        | .ok r2 => (r2, .ok ())

/-- `PyDict_Pop` of a text. -/
def regDel : Registry → List Nat → Py (Option Registry)
  | [], _ => .ok Option.none
  | (key, v) :: r, k =>
    match keyAnswers key k with
    | .error e => .error e
    | .ok true => .ok (some r)
    | .ok false =>
      match regDel r k with
      | .error e => .error e
      | .ok (some r2) => .ok (some ((key, v) :: r2))
      | .ok Option.none => .ok Option.none

/-- `_csv_unregister_dialect_impl`, `Modules/_csv.c:1652-1666`. `PyDict_Pop` on an empty dict
returns `0` without hashing, `Objects/dictobject.c:3171-3176`. -/
def csvUnregisterDialect (r : Registry) (name : Obj) : Py Registry :=
  if r.isEmpty then .error (csvErr "unknown dialect")
  else
    let gone : Py (Option Registry) :=
      match name.dictKey with
      | .hashRaises e => .error (dictHashErr name e)
      | .eqRaises e => .error e
      | .noMatch => .ok Option.none
      | .equals k => regDel r k
      | .eqRaisesAt k e =>
        match regFind r k with
        | .error e' => .error e'
        | .ok (some _) => .error e
        | .ok Option.none => .ok Option.none
    match gone with
    | .error e => .error e
    | .ok (some r2) => .ok r2
    | .ok Option.none => .error (csvErr "unknown dialect")

/-- `_csv_list_dialects_impl`, `Modules/_csv.c:1611-1616`: `PyDict_Keys`, the key objects in insertion
order. -/
def csvListDialects (r : Registry) : List Obj := r.map (·.1)

/-- `_csv_field_size_limit_impl`, `Modules/_csv.c:1694-1713`: the value returned, which is the old
limit, and the limit now in force. -/
def fieldSizeLimit (cur : Int) (new? : Option Obj) : Py (Int × Int) :=
  match new? with
  | Option.none => .ok (cur, cur)
  | some (.int n) =>
    if n < -(2 ^ 63) ∨ n > 2 ^ 63 - 1 then
      .error (.overflowError "Python int too large to convert to C ssize_t")
    else .ok (cur, n)
  | some _ => .error (.typeError "limit must be an integer")

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
  | float (x : PyLean.Binary64.F64)
  deriving Repr, DecidableEq, Inhabited

/-- The mutable part of `ReaderObj`, `Modules/_csv.c:123-137`, that parsing touches.
`nullFields` is `self->fields == NULL`; `field` is `self->field[:self->field_len]`. -/
structure RSt where
  fields : List Field := []
  nullFields : Bool := false
  state : PState := .START_RECORD
  field : List Nat := []
  unquoted : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- `PyList_Append(self->fields, field)`, `Modules/_csv.c:688`. `PyList_Check(NULL)` reads through
the pointer, `Objects/listobject.c:535`. -/
def appendField (s : RSt) (f : Field) : Py RSt :=
  if s.nullFields then .error CRASH else .ok { s with fields := s.fields ++ [f] }

/-- `parse_save_field`, `Modules/_csv.c:657-694`. `PyNumber_Float` on a `str` is
`PyFloat_FromString`. A failed conversion leaves `field_len` as it was. -/
def parseSaveField (d : Dialect) (s : RSt) : Py RSt :=
  let q := d.quoting
  if s.unquoted ∧ s.field.isEmpty ∧ (q = QUOTE_NOTNULL ∨ q = QUOTE_STRINGS) then
    appendField s .none
  else if s.unquoted ∧ !s.field.isEmpty ∧ (q = QUOTE_NONNUMERIC ∨ q = QUOTE_STRINGS) then
    match PyLean.Binary64.PyFloat_FromString (.str s.field) with
    | .ok x => appendField { s with field := [] } (.float x)
    | .error e => .error e
  else appendField { s with field := [] } (.str s.field)

/-- The message at `Modules/_csv.c:888`. A `str` message holds a lone surrogate, which a Lean
`String` cannot, so then only the class is compared. -/
def expectedMsg (d : Dialect) : String :=
  let bad (c : Nat) : Bool := 0xD800 ≤ c && c ≤ 0xDFFF
  if bad d.delimiter || bad d.quotechar then "~'%c' expected after '%c'"
  else s!"'{String.singleton (Char.ofNat d.delimiter)}' expected after '{String.singleton (Char.ofNat d.quotechar)}'"

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
      .error (csvErr (expectedMsg d))
  | .EAT_CRNL =>
    if isNl c then .ok s
    else if c = EOL then .ok { s with state := .START_RECORD }
    else .error (csvErr
      "new-line character seen in unquoted field - do you need to open the file with newline=''?")

/-- `parse_process_char` with the state C leaves behind when it fails. Only `START_RECORD`, which
falls through to `START_FIELD`, and `START_FIELD` write the state before anything that can fail:
`Modules/_csv.c:745` and `:749`. Every other failing branch sets its state afterwards. -/
def parseProcessCharP (d : Dialect) (limit : Int) (s : RSt) (c : Nat) : RSt × Option PyExc :=
  match parseProcessChar d limit s c with
  | .ok s' => (s', Option.none)
  | .error e =>
    let started := s.state = .START_FIELD ∨ (s.state = .START_RECORD ∧ c ≠ EOL ∧ isNl c = false)
    (if started then { s with state := .START_FIELD, unquoted := true } else s, some e)

/-- The `while (linelen--)` loop, `Modules/_csv.c:979-986`. -/
def parseChars (d : Dialect) (limit : Int) : RSt → List Nat → RSt × Option PyExc
  | s, [] => (s, Option.none)
  | s, c :: cs =>
    match parseProcessCharP d limit s c with
    | (s', some e) => (s', some e)
    | (s', Option.none) => parseChars d limit s' cs

/-- `Modules/_csv.c:979-989`: the characters of one line, then `EOL`. -/
def parseLine (d : Dialect) (limit : Int) (s : RSt) (line : List Nat) : RSt × Option PyExc :=
  match parseChars d limit s line with
  | (s', some e) => (s', some e)
  | (s', Option.none) => parseProcessCharP d limit s' EOL

/-- `parse_reset`, `Modules/_csv.c:912-922`. `field` is cleared, and so is `self->fields`, which
gets a new list. -/
def parseReset (s : RSt) : RSt :=
  { s with fields := [], nullFields := false, field := [], state := .START_RECORD, unquoted := false }

/-- What a reader's `__next__` can reach. `limit` is `module_state->field_limit`. -/
structure RCtx where
  s : RSt := {}
  lineNum : Nat := 0
  acts : List Step
  limit : Int
  deriving Inhabited

/-- A failure that an enclosing `except` cannot catch. -/
def fatal (e : PyExc) : Bool := e == CRASH || e == .modelFuel

/-- The new limit after `csv.field_size_limit(n)`, called for its effect. -/
def applyLimit (cur : Int) (n : Obj) : Int :=
  match fieldSizeLimit cur (some n) with
  | .ok (_, l) => l
  | .error _ => cur

mutual
  /-- `PyIter_Next(self->input_iter)`: `none` for the end of input. Effects before the result run
  here, inside the outer `__next__`. -/
  def iterNext (d : Dialect) : Nat → RCtx → RCtx × Py (Option Obj)
    | 0, c => (c, .error .modelFuel)
    | fuel + 1, c =>
      match c.acts with
      | [] => (c, .ok Option.none)
      | .stop :: r => ({ c with acts := r }, .ok Option.none)
      | .raise e :: r => ({ c with acts := r }, .error e)
      | .ret o :: r => ({ c with acts := r }, .ok (some o))
      | .eff .advance :: r =>
        match readerNext d fuel { c with acts := r } with
        | (c', .error e) => if fatal e then (c', .error e) else iterNext d fuel c'
        | (c', .ok _) => iterNext d fuel c'
      | .eff (.setLimit n) :: r => iterNext d fuel { c with acts := r, limit := applyLimit c.limit n }
      | .eff (.writerow _) :: r => iterNext d fuel { c with acts := r }

  /-- `Reader_iternext_lock_held`, `Modules/_csv.c:924-996`: `none` is `StopIteration`.
  `Reader_iternext`, `Modules/_csv.c:998-1006`, only adds the critical section. -/
  def readerNext (d : Dialect) : Nat → RCtx → RCtx × Py (Option (List Field))
    | 0, c => (c, .error .modelFuel)
    | fuel + 1, c => readerLoop d fuel { c with s := parseReset c.s }

  /-- The `do ... while`, `Modules/_csv.c:944-990`. -/
  def readerLoop (d : Dialect) : Nat → RCtx → RCtx × Py (Option (List Field))
    | 0, c => (c, .error .modelFuel)
    | fuel + 1, c =>
      let finish (c : RCtx) : RCtx × Py (Option (List Field)) :=
        ({ c with s := { c.s with fields := [], nullFields := true } }, .ok (some c.s.fields))
      match iterNext d fuel c with
      | (c, .error e) => (c, .error e)
      | (c, .ok Option.none) =>
        if !c.s.field.isEmpty ∨ c.s.state = .IN_QUOTED_FIELD then
          if d.strict then (c, .error (csvErr "unexpected end of data"))
          else
            match parseSaveField d c.s with
            | .ok s => finish { c with s }
            | .error e => (c, .error e)
        else (c, .ok Option.none)
      | (c, .ok (some o)) =>
        match o.asStr with
        | Option.none =>
          (c, .error (csvErr s!"iterator should return strings, not {o.ty.tp} (the file should be opened in text mode)"))
        | some l =>
          if c.s.nullFields then (c, .error (csvErr "iterator has already advanced the reader"))
          else
            let c := { c with lineNum := (c.lineNum + 1) % 2 ^ 64 }
            match parseLine d c.limit c.s l with
            | (s, some e) => ({ c with s }, .error e)
            | (s, Option.none) =>
              if s.state = .START_RECORD then finish { c with s }
              else readerLoop d fuel { c with s }
end

/-- `csv_reader`, `Modules/_csv.c:1086-1128`: the dialect and the new reader. -/
def csvReader (reg : Registry) (limit : Int) (args : Args) : Py (Dialect × RCtx) := do
  let (iterator, dialect) ← unpack12 "reader" args.pos
  let acts ← iterator.getIter
  let d ← callDialect reg dialect args.kw
  return (d.dialect, { acts, limit })

/-- `list(reader)`: the rows, and how it ended. `calls` bounds the calls of `__next__` and `fuel`
each call. -/
def readAll (d : Dialect) (fuel : Nat) : (calls : Nat) → RCtx → List (List Field) × Option PyExc × RCtx
  | 0, c => ([], some .modelFuel, c)
  | calls + 1, c =>
    match readerNext d fuel c with
    | (c, .error e) => ([], some e, c)
    | (c, .ok Option.none) => ([], Option.none, c)
    | (c, .ok (some row)) =>
      let (rows, e, c) := readAll d fuel calls c
      (row :: rows, e, c)

/-! ### Writer -/

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

/-- What `self->num_fields++` does at `INT_MAX`, `Modules/_csv.c:149` and `:1297`. Signed overflow
is undefined in C; this is the wrap that the builds in use produce. -/
def cIntWrap (n : Int) : Int := (n + 2 ^ 31) % 2 ^ 32 - 2 ^ 31

/-- `join_append`, `Modules/_csv.c:1259-1300`, with both `join_append_data` phases. `field` is
`none` for the `NULL` field. -/
def joinAppend (d : Dialect) (buf : List Nat) (numFields : Int) (field : Option (List Nat))
    (quoted : Bool) : Py (List Nat × Int) := do
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
  return (buf ++ sep ++ open_ ++ body ++ open_, cIntWrap (numFields + 1))

/-- The `switch` of `csv_writerow_lock_held`, `Modules/_csv.c:1351-1367`. -/
def initialQuoted (d : Dialect) (f : Obj) : Bool :=
  if d.quoting = QUOTE_NONNUMERIC then !f.isNumber
  else if d.quoting = QUOTE_ALL then true
  else if d.quoting = QUOTE_STRINGS then (f.asStr).isSome
  else if d.quoting = QUOTE_NOTNULL then
    match f with
    | .none => false
    | _ => true
  else false

/-- What a writer's methods can reach: `rec` and `rec_len` as `buf`, `num_fields`, and `write`. `written` is
every argument `write` was called with, in order. -/
structure WCtx where
  buf : List Nat := []
  numFields : Int := 0
  written : List (List Nat) := []
  calls : List (List Eff × Py Obj) := []
  deriving Inhabited

def isTypeError : PyExc → Bool
  | .typeError _ => true
  | _ => false

def Obj.isNone : Obj → Bool
  | .none => true
  | _ => false

mutual
  /-- Effects inside a callback; only `writerow` touches a writer. -/
  def runEffs (d : Dialect) : Nat → WCtx → List Eff → WCtx × Py Unit
    | 0, c, _ => (c, .error .modelFuel)
    | _ + 1, c, [] => (c, .ok ())
    | fuel + 1, c, .writerow row :: es =>
      match writerowM d fuel c row with
      | (c', .error e) => if fatal e then (c', .error e) else runEffs d fuel c' es
      | (c', .ok _) => runEffs d fuel c' es
    | fuel + 1, c, _ :: es => runEffs d fuel c es

  /-- `csv_writerow_lock_held`, `Modules/_csv.c:1326-1428`. `csv_writerow`,
  `Modules/_csv.c:1437-1445`, only adds the critical section. The result is what `write` returned. -/
  def writerowM (d : Dialect) : Nat → WCtx → Obj → WCtx × Py Obj
    | 0, c, _ => (c, .error .modelFuel)
    | fuel + 1, c, seq =>
      match seq.getIter with
      | .error e =>
        (c, .error (if isTypeError e then csvErr s!"iterable expected, not {seq.ty.tp}" else e))
      | .ok steps =>
        match fieldLoop d fuel { c with buf := [], numFields := 0 } steps false with
        | (c, .error e) => (c, .error e)
        | (c, .ok nullField) => finishRow d fuel c nullField

  /-- The field loop, `Modules/_csv.c:1347-1397`: `null_field` at the end. -/
  def fieldLoop (d : Dialect) : Nat → WCtx → List Step → Bool → WCtx × Py Bool
    | 0, c, _, _ => (c, .error .modelFuel)
    | _ + 1, c, [], nf => (c, .ok nf)
    | _ + 1, c, .stop :: _, nf => (c, .ok nf)
    | _ + 1, c, .raise e :: _, _ => (c, .error e)
    | fuel + 1, c, .eff e :: r, nf =>
      match runEffs d fuel c [e] with
      | (c, .error x) => (c, .error x)
      | (c, .ok ()) => fieldLoop d fuel c r nf
    | fuel + 1, c, .ret f :: r, _ =>
      let quoted := initialQuoted d f
      let nf := f.isNone
      let append (c : WCtx) (text : Option (List Nat)) : WCtx × Py Bool :=
        match joinAppend d c.buf c.numFields text quoted with
        | .error e => (c, .error e)
        | .ok (buf, n) => fieldLoop d fuel { c with buf := buf, numFields := n } r nf
      match f.asStr with
      | some s => append c (some s)
      | Option.none =>
        if nf then append c Option.none
        else
          let (effs, res) := f.pyStr
          match runEffs d fuel c effs with
          | (c, .error x) => (c, .error x)
          | (c, .ok ()) =>
            match res with
            | .error e => (c, .error e)
            | .ok s => append c (some s)

  /-- `Modules/_csv.c:1399-1427`: the empty record check, the terminator, and `write`. -/
  def finishRow (d : Dialect) : Nat → WCtx → Bool → WCtx × Py Obj
    | 0, c, _ => (c, .error .modelFuel)
    | fuel + 1, c, nullField =>
      if c.numFields > 0 ∧ c.buf.isEmpty then
        if d.quoting = QUOTE_NONE ∨
            (nullField ∧ (d.quoting = QUOTE_STRINGS ∨ d.quoting = QUOTE_NOTNULL)) then
          (c, .error (csvErr "single empty field record must be quoted"))
        else
          let n := c.numFields - 1
          match joinAppend d c.buf n Option.none true with
          | .error e => ({ c with numFields := n }, .error e)
          | .ok (buf, n') => callWrite d fuel { c with buf := buf ++ d.lineterminator, numFields := n' }
      else callWrite d fuel { c with buf := c.buf ++ d.lineterminator }

  /-- `PyObject_CallOneArg(self->write, line)`, `Modules/_csv.c:1425`. -/
  def callWrite (d : Dialect) : Nat → WCtx → WCtx × Py Obj
    | 0, c => (c, .error .modelFuel)
    | fuel + 1, c =>
      let c := { c with written := c.written ++ [c.buf] }
      match c.calls with
      | [] => (c, .ok .none)
      | (effs, res) :: rest =>
        match runEffs d fuel { c with calls := rest } effs with
        | (c, .error x) => (c, .error x)
        | (c, .ok ()) => (c, res)
end

/-- The loop of `csv_writerows`, `Modules/_csv.c:1463-1475`. -/
def writerowsLoop (d : Dialect) (fuel : Nat) : WCtx → List Step → WCtx × Py Obj
  | c, [] => (c, .ok .none)
  | c, .stop :: _ => (c, .ok .none)
  | c, .raise e :: _ => (c, .error e)
  | c, .eff e :: r =>
    match runEffs d fuel c [e] with
    | (c, .error x) => (c, .error x)
    | (c, .ok ()) => writerowsLoop d fuel c r
  | c, .ret row :: r =>
    match writerowM d fuel c row with
    | (c, .error e) => (c, .error e)
    | (c, .ok _) => writerowsLoop d fuel c r

/-- `csv_writerows`, `Modules/_csv.c:1454-1477`. -/
def writerowsM (d : Dialect) (fuel : Nat) (c : WCtx) (seqseq : Obj) : WCtx × Py Obj :=
  match seqseq.getIter with
  | .error e => (c, .error e)
  | .ok steps => writerowsLoop d fuel c steps

/-- `PyObject_GetOptionalAttr(output_file, "write", ...)`: `AttributeError` means absent. -/
def optionalWrite (o : Obj) : Py (Option Obj) :=
  match o.getattr "write" with
  | .ok v => .ok (some v)
  | .error (.named "AttributeError" _) => .ok Option.none
  | .error e => .error e

/-- `csv_writer`, `Modules/_csv.c:1555-1599`: the dialect and the new writer. -/
def csvWriter (reg : Registry) (args : Args) : Py (Dialect × WCtx) := do
  let (outputFile, dialect) ← unpack12 "writer" args.pos
  let calls ← match ← optionalWrite outputFile with
    | some (.func calls) => pure calls
    | _ => throw (.typeError "argument 1 must have a \"write\" method")
  let d ← callDialect reg dialect args.kw
  return (d.dialect, { calls })

/-! ### `DictReader` and `DictWriter`, `Lib/csv.py:144-230` -/

/-- A value of a `DictReader` row. -/
inductive DVal where
  | field (f : Field)
  | rest (fs : List Field)
  /-- `restval`, opaque here. -/
  | restval
  deriving Repr, DecidableEq, Inhabited

/-- `==` on dict keys read from a file: strings and `None` by value, floats numerically, so `-0.0`
equals `0.0` and a NaN equals nothing. -/
def keyEq : Field → Field → Bool
  | .str a, .str b => a == b
  | .none, .none => true
  | .float a, .float b =>
    !a.isNaN && !b.isNaN && (a.bits == b.bits || (a.bits % 2 ^ 63 == 0 && b.bits % 2 ^ 63 == 0))
  | _, _ => false

/-- `d[k] = v`: an equal key keeps its place and its key object. -/
def dictSet (d : List (Field × DVal)) (k : Field) (v : DVal) : List (Field × DVal) :=
  if d.any (fun p => keyEq p.1 k) then d.map (fun p => if keyEq p.1 k then (p.1, v) else p)
  else d ++ [(k, v)]

/-- The dict building of `DictReader.__next__`, `Lib/csv.py:185-192`. -/
def dictRow (names row : List Field) (restkey : Field) : List (Field × DVal) :=
  let d0 := (names.zip row).foldl (fun d p => dictSet d p.1 (.field p.2)) []
  let lf := names.length
  let lr := row.length
  if lf < lr then dictSet d0 restkey (.rest (row.drop lf))
  else if lf > lr then (names.drop lr).foldl (fun d k => dictSet d k .restval) d0
  else d0

/-- A `DictReader`: `_fieldnames`, `restkey`, `line_num` and the wrapped reader. -/
structure DR where
  names : Option (List Field)
  restkey : Field
  lineNum : Nat := 0
  c : RCtx
  deriving Inhabited

/-- The `fieldnames` getter, `Lib/csv.py:159-167`. -/
def drFieldnames (d : Dialect) (fuel : Nat) (r : DR) : DR × Py Unit :=
  if r.names.isNone then
    match readerNext d fuel r.c with
    | (c, .error e) => ({ r with c }, .error e)
    | (c, .ok (some row)) => ({ r with c, names := some row, lineNum := c.lineNum }, .ok ())
    | (c, .ok Option.none) => ({ r with c, lineNum := c.lineNum }, .ok ())
  else ({ r with lineNum := r.c.lineNum }, .ok ())

/-- The `while row == []` of `DictReader.__next__`, `Lib/csv.py:183-184`. -/
def drSkipBlank (d : Dialect) (fuel : Nat) : (blanks : Nat) → RCtx → List Field →
    RCtx × Py (Option (List Field))
  | 0, c, _ => (c, .error .modelFuel)
  | n + 1, c, row =>
    if row.isEmpty then
      match readerNext d fuel c with
      | (c, .error e) => (c, .error e)
      | (c, .ok Option.none) => (c, .ok Option.none)
      | (c, .ok (some row)) => drSkipBlank d fuel n c row
    else (c, .ok (some row))

/-- `DictReader.__next__`, `Lib/csv.py:173-193`: `none` is `StopIteration`. -/
def drNext (d : Dialect) (fuel blanks : Nat) (r0 : DR) : DR × Py (Option (List (Field × DVal))) :=
  let first := if r0.lineNum == 0 then drFieldnames d fuel r0 else (r0, .ok ())
  match first with
  | (r, .error e) => (r, .error e)
  | (r, .ok ()) =>
    match readerNext d fuel r.c with
    | (c, .error e) => ({ r with c }, .error e)
    | (c, .ok Option.none) => ({ r with c }, .ok Option.none)
    | (c, .ok (some row)) =>
      let r := { r with c, lineNum := c.lineNum }
      match drSkipBlank d fuel blanks c row with
      | (c, .error e) => ({ r with c }, .error e)
      | (c, .ok Option.none) => ({ r with c }, .ok Option.none)
      | (c, .ok (some row)) =>
        match drFieldnames d fuel { r with c } with
        | (r, .error e) => (r, .error e)
        | (r, .ok ()) =>
          match r.names with
          | some names => (r, .ok (some (dictRow names row r.restkey)))
          | Option.none => (r, .error (.typeError "~zip() argument must support iteration"))

/-- `list(dictreader)`. -/
def drAll (d : Dialect) (fuel blanks : Nat) : (calls : Nat) → DR →
    List (List (Field × DVal)) × Option PyExc × DR
  | 0, r => ([], some .modelFuel, r)
  | calls + 1, r =>
    match drNext d fuel blanks r with
    | (r, .error e) => ([], some e, r)
    | (r, .ok Option.none) => ([], Option.none, r)
    | (r, .ok (some x)) =>
      let (xs, e, r) := drAll d fuel blanks calls r
      (x :: xs, e, r)

/-- `DictReader.__init__`, `Lib/csv.py:145-154`, for a `fieldnames` already a list, with
`self.reader = reader(f, dialect, *args, **kwds)`. -/
def drInit (reg : Registry) (limit : Int) (f : Obj) (names : Option (List Field)) (restkey : Field)
    (dialect : Obj) (kw : List (List Nat × Obj)) : Py (Dialect × DR) := do
  let (d, c) ← csvReader reg limit ⟨[f, dialect], kw⟩
  return (d, { names, restkey, c })

/-- `DictWriter.__init__`'s check of `extrasaction`, `Lib/csv.py:205-208`: whether it is `'raise'`.
`str.lower` has no non-ASCII source for the letters of either word, so `lowerAscii` decides the same
two comparisons. -/
def lowerAsciiS (s : List Nat) : List Nat := s.map fun c => if 65 ≤ c ∧ c ≤ 90 then c + 32 else c

def extrasactionCheck (s : List Nat) : Py Bool :=
  let l := lowerAsciiS s
  if l == strToList "raise" then .ok true
  else if l == strToList "ignore" then .ok false
  else .error (.valueError "~extrasaction must be 'raise' or 'ignore'")

/-- `DictWriter._dict_to_list`, `Lib/csv.py:216-222`: the generator's steps. The keys of `rowdict`
are strings here. -/
def dictToList (names : List (List Nat)) (restval : Obj) (raises : Bool)
    (rowdict : List (List Nat × Obj)) : Py (List Step) :=
  if raises ∧ rowdict.any (fun p => !names.contains p.1) then
    .error (.valueError "~dict contains fields not in fieldnames")
  else .ok (names.map fun k => .ret ((rowdict.lookup k).getD restval))

/-- `DictWriter.writerow`, `Lib/csv.py:224-225`. -/
def dictWriterow (d : Dialect) (fuel : Nat) (names : List (List Nat)) (restval : Obj) (raises : Bool)
    (c : WCtx) (rowdict : List (List Nat × Obj)) : WCtx × Py Obj :=
  match dictToList names restval raises rowdict with
  | .error e => (c, .error e)
  | .ok steps => writerowM d fuel c (iterObj steps)

/-- `map(self._dict_to_list, rowdicts)`: an item that raises raises from the iterator. -/
def mapSteps (names : List (List Nat)) (restval : Obj) (raises : Bool) :
    List (List (List Nat × Obj)) → List Step
  | [] => []
  | r :: rs =>
    match dictToList names restval raises r with
    | .error e => [.raise e]
    | .ok steps => .ret (iterObj steps) :: mapSteps names restval raises rs

/-- `DictWriter.writerows`, `Lib/csv.py:227-228`. -/
def dictWriterows (d : Dialect) (fuel : Nat) (names : List (List Nat)) (restval : Obj) (raises : Bool)
    (c : WCtx) (rows : List (List (List Nat × Obj))) : WCtx × Py Obj :=
  writerowsM d fuel c (iterObj (mapSteps names restval raises rows))

/-- `DictWriter.writeheader`, `Lib/csv.py:212-214`. -/
def writeheader (d : Dialect) (fuel : Nat) (c : WCtx) (names : List (List Nat)) : WCtx × Py Obj :=
  dictWriterow d fuel names (.str []) true c (names.map fun n => (n, Obj.str n))

end PyLean.TextLibs.Csv
