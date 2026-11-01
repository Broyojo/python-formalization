import PyLean.UnicodeObj.FormatStr

/-!
The iterators of `str`: Objects/unicodeobject.c:14602-14804.

`__reduce__` looks `iter` up in the builtins of the current frame before it reads the iterator,
and that lookup can run Python code, which can advance or exhaust this same iterator (issue
#101765). So the lookup is a function of the iterator's state, and it returns a new state.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- `unicodeiterobject`, with its type. `seq` is `none` once exhausted. -/
structure UIter where
  index : Int
  seq : Option Str
  /-- `_PyUnicodeASCIIIter_Type`, against `PyUnicodeIter_Type`. -/
  asciiType : Bool
  deriving Repr, DecidableEq

/-- `unicode_iter`, unicodeobject.c:14784-14804. `PyUnicode_IS_COMPACT_ASCII` is false for an
instance of a subclass of `str`, which is not compact. The `PyErr_BadInternalCall` for a non-`str`
cannot be reached: this is `tp_iter` of `str`. -/
def unicodeIter (s : Str) (exact : Bool) : UIter :=
  { index := 0, seq := some s, asciiType := exact && s.all (· < 128) }

/-- `unicode_char`, unicodeobject.c:1834-1855: the singleton below 256, a new string above. -/
def unicodeChar (ch : Nat) : Str × Kind :=
  if ch < 256 then ([ch], if ch < 128 then .ascii else .ucs1)
  else ([ch], kindOfMax ch)

/-- `unicodeiter_next`, unicodeobject.c:14628-14650. -/
def unicodeiterNext (it : UIter) : UIter × Option (Str × Kind) :=
  match it.seq with
  | none => (it, none)
  | some s =>
    if it.index < s.length then
      ({ it with index := it.index + 1 }, some (unicodeChar (s.getD it.index.toNat 0)))
    else ({ it with seq := none }, none)

/-- `unicode_ascii_iter_next`, unicodeobject.c:14653-14673: one byte, and the ASCII singleton. -/
def unicodeAsciiIterNext (it : UIter) : UIter × Option (Str × Kind) :=
  match it.seq with
  | none => (it, none)
  | some s =>
    if it.index < s.length then
      ({ it with index := it.index + 1 }, some ([s.getD it.index.toNat 0 % 256], .ascii))
    else ({ it with seq := none }, none)

/-- `tp_iternext` of the two types. -/
def UIter.next (it : UIter) : UIter × Option (Str × Kind) :=
  if it.asciiType then unicodeAsciiIterNext it else unicodeiterNext it

/-- `unicodeiter_len`, unicodeobject.c:14676-14683. -/
def unicodeiterLen (it : UIter) : Int :=
  match it.seq with
  | some s => (s.length : Int) - it.index
  | none => 0

/-- `PyLong_AsSsize_t`, Objects/longobject.c@3.14.7:628-680. It does not call `__index__`. -/
def longAsSsize : GObj → Py Int
  | .int v =>
    if v > ssizeMax ∨ v < ssizeMin then
      .error (.overflowError "Python int too large to convert to C ssize_t")
    else .ok v
  | .bool b => .ok (if b then 1 else 0)
  | _ => .error (.typeError "an integer is required")

/-- `unicodeiter_setstate`, unicodeobject.c:14712-14726. The conversion comes first, so it raises
for an exhausted iterator too. -/
def unicodeiterSetstate (it : UIter) (state : GObj) : Py UIter := do
  let index ← longAsSsize state
  match it.seq with
  | some s =>
    let index := if index < 0 then 0 else if index > s.length then (s.length : Int) else index
    .ok { it with index }
  | none => .ok it

/-- What the lookup of `iter` gives. -/
inductive BuiltinIter where
  /-- The object found, by a label. -/
  | found (label : Nat)
  /-- No such name: `PyMapping_GetOptionalItem` returns 0. -/
  | missing
  /-- The lookup raised. -/
  | raises (e : PyExc)
  deriving Repr

/-- The result of `__reduce__`: the callable, the string, and the index unless exhausted. -/
abbrev IterReduced := Nat × Str × Option Int

/-- `unicodeiter_reduce`, unicodeobject.c:14688-14707. `lookup` is `_PyEval_GetBuiltin`, which can
change the iterator, so nothing is read from it before. A NULL from the lookup goes through
`Py_BuildValue`, which passes on the exception that is set. -/
def unicodeiterReduce (lookup : UIter → UIter × BuiltinIter) (it : UIter) : UIter × Py IterReduced :=
  let (it', r) := lookup it
  match r with
  | .found f =>
    match it'.seq with
    | some s => (it', .ok (f, s, some it'.index))
    | none => (it', .ok (f, [], none))
  | .missing => (it', .error (.named "AttributeError" "iter"))
  | .raises e => (it', .error e)

/-- One step of a script on an iterator, as `__reduce__` runs them from inside its lookup. -/
inductive ISimple where
  | next
  | setstate (state : GObj)

def ISimple.run (it : UIter) : ISimple → UIter
  | .next => it.next.1
  | .setstate o =>
    match unicodeiterSetstate it o with
    | .ok it' => it'
    | .error _ => it

/-- The lookup of a script: what the `__getitem__` of the builtins does, then what it returns. -/
def scriptLookup (pre : List ISimple) (r : BuiltinIter) (it : UIter) : UIter × BuiltinIter :=
  (pre.foldl ISimple.run it, r)

/-- An operation of the difftest. -/
inductive IOp where
  | next
  | len
  | setstate (state : GObj)
  | reduce (pre : List ISimple) (r : BuiltinIter)

/-- What an operation shows. -/
inductive IOut where
  | item (x : Option (Str × Kind))
  | len (n : Int)
  | unit (r : Py Unit)
  | reduced (r : Py IterReduced)

def applyIOp (it : UIter) : IOp → UIter × IOut
  | .next => let (i, x) := it.next; (i, .item x)
  | .len => (it, .len (unicodeiterLen it))
  | .setstate o =>
    match unicodeiterSetstate it o with
    | .ok i => (i, .unit (.ok ()))
    | .error e => (it, .unit (.error e))
  | .reduce pre r =>
    let (i, x) := unicodeiterReduce (scriptLookup pre r) it
    (i, .reduced x)

def runIOps : UIter → List IOp → UIter × List IOut
  | it, [] => (it, [])
  | it, op :: t =>
    let (i, o) := applyIOp it op
    let (j, os) := runIOps i t
    (j, o :: os)

end PyLean.UnicodeObj
