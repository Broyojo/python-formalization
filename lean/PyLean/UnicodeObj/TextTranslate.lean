import PyLean.UnicodeObj.TextCase

/-!
`str.translate`, `PyUnicode_Translate` and `str.maketrans`,
Objects/unicodeobject.c:9096-9512 and :13135-13301.

The table is an abstract pure function from ordinal to what `__getitem__` does
(`Mapping`), which covers every dict, list or other mapping whose `__getitem__`
has no side effects. Error handlers: `str.translate` always passes `"ignore"`; the
only other mode modelled is `errors=NULL`/`"strict"`, which raises through
`unicode_translate_call_errorhandler`.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- What `PyMapping_GetOptionalItem(mapping, ch)` produces. -/
inductive MapItem where
  /-- Missing key, or `LookupError` from `__getitem__`. -/
  | missing
  | pyNone
  | int (v : Int)
  | str (s : Str)
  /-- Any other object. -/
  | wrong
  /-- `__getitem__` raised something that is not a `LookupError`. -/
  | raises (e : PyExc)
  deriving Repr, DecidableEq

abbrev Mapping := Nat → MapItem

/-- `*result` of `charmaptranslate_lookup`: NULL, None, a PyLong (with `*replace`)
or a PyUnicode. -/
inductive Looked where
  | null | pyNone
  | long (replace : Nat)
  | str (s : Str)
  deriving Repr, DecidableEq

/-- `charmaptranslate_lookup`, unicodeobject.c:9182-9233. `PyLong_AsLong`
failing returns -1, which lands in the same `value < 0` branch. -/
def charmaptranslateLookup (m : Mapping) (c : Nat) : Py Looked :=
  match m c with
  | .missing => .ok .null
  | .raises e => .error e
  | .pyNone => .ok .pyNone
  | .int v =>
    if v < 0 ∨ v > maxUnicode then
      .error (.valueError "character mapping must be in range(0x110000)")
    else .ok (.long v.toNat)
  | .str s => .ok (.str s)
  | .wrong => .error (.typeError "character mapping must return integer, None or str")

/-- `charmaptranslate_output`, unicodeobject.c:9239-9282: the characters written,
or `none` for an undefined mapping. -/
def charmaptranslateOutput (m : Mapping) (ch : Nat) : Py (Option Str) := do
  match ← charmaptranslateLookup m ch with
  | .null => .ok (some [ch])
  | .pyNone => .ok none
  | .long replace => .ok (some [replace])
  | .str s => .ok (some s)

/-- `ascii_table`: `0xff` is unset and `0xfe` is deletion. -/
abbrev AsciiTable := Nat → Nat

def tableSet (t : AsciiTable) (ch v : Nat) : AsciiTable := fun c => if c = ch then v else t c

/-- `unicode_fast_translate_lookup`, unicodeobject.c:9285-9331. -/
def fastTranslateLookup (m : Mapping) (ch : Nat) (t : AsciiTable) : Py (Bool × AsciiTable) := do
  match ← charmaptranslateLookup m ch with
  | .pyNone => .ok (true, tableSet t ch 0xfe)
  | .null => .ok (true, tableSet t ch ch)
  | .long replace =>
    if replace > 127 then .ok (false, t) else .ok (true, tableSet t ch replace)
  | .str s =>
    match s with
    | [replace] =>
      if replace > 127 then .ok (false, t) else .ok (true, tableSet t ch replace)
    | _ => .ok (false, t)

/-- `unicode_fast_translate`'s loop, unicodeobject.c:9358-9379. Returns `res`, the
writer contents and `*input_pos`. -/
def fastTranslateLoop (m : Mapping) (ignore : Bool) :
    List Nat → AsciiTable → Str → Nat → Py (Bool × Str × Nat)
  | [], _, out, pos => .ok (true, out, pos)
  | ch :: cs, t, out, pos => do
    let ch2 := t ch
    let step (t' : AsciiTable) (ch2 : Nat) : Py (Bool × Str × Nat) :=
      if ch2 = 0xfe then
        if ignore then fastTranslateLoop m ignore cs t' out (pos + 1)
        else .ok (false, out, pos)
      else fastTranslateLoop m ignore cs t' (out ++ [ch2]) (pos + 1)
    if ch2 = 0xff then
      let (translate, t') ← fastTranslateLookup m ch t
      if !translate then .ok (false, out, pos) else step t' (t' ch)
    else step t ch2

/-- The inner `while (collend < size)` of `_PyUnicode_TranslateCharmap`,
unicodeobject.c:9464-9474: the input left from `collend` on. -/
def collectUndefined (m : Mapping) : List Nat → Py (List Nat)
  | [] => .ok []
  | c :: cs => do
    match ← charmaptranslateLookup m c with
    | .pyNone => collectUndefined m cs
    | _ => .ok (c :: cs)

/-- `\xHH`, `\uHHHH` or `\UHHHHHHHH`, as `UnicodeTranslateError.__str__` prints
the single offending character (Objects/exceptions.c). -/
def escapeBadChar (c : Nat) : String :=
  if c ≤ 0xff then toLeanString (lit "\\x" ++ hexDigits 2 c)
  else if c ≤ 0xffff then toLeanString (lit "\\u" ++ hexDigits 4 c)
  else toLeanString (lit "\\U" ++ hexDigits 8 c)

/-- `strict_errors` on a `UnicodeTranslateError` (Python/codecs.c), with the text
of `UnicodeTranslateError.__str__` (Objects/exceptions.c). -/
def translateError (input : Str) (start stop : Nat) : PyExc :=
  let reason := "character maps to <undefined>"
  if stop = start + 1 then
    .named "UnicodeTranslateError"
      s!"can't translate character '{escapeBadChar (input.getD start 0)}' in position {start}: {reason}"
  else
    .named "UnicodeTranslateError"
      s!"can't translate characters in position {start}-{stop - 1}: {reason}"

/-- The outer `while (i<size)` of `_PyUnicode_TranslateCharmap`,
unicodeobject.c:9438-9492. `input` is the whole string. -/
def translateLoop (m : Mapping) (ignore : Bool) (input : Str) :
    Nat → Nat → List Nat → Str → Py Str
  | 0, _, _, _ => .error .modelFuel
  | _ + 1, _, [], out => .ok out
  | fuel + 1, i, ch :: cs, out => do
    match ← charmaptranslateOutput m ch with
    | some w => translateLoop m ignore input fuel (i + 1) cs (out ++ w)
    | none =>
      let rest ← collectUndefined m cs
      let collend := input.length - rest.length
      if ignore then translateLoop m ignore input fuel collend rest out
      else .error (translateError input i collend)

/-- `_PyUnicode_TranslateCharmap`, unicodeobject.c:9388-9502. -/
def translateCharmap (m : Mapping) (ignore : Bool) (input : Str) : Py Str :=
  if input.length = 0 then .ok input
  else
    let fuel := input.length + 1
    if isAscii input then do
      let (res, out, i) ← fastTranslateLoop m ignore input (fun _ => 0xff) [] 0
      if res then .ok out
      else translateLoop m ignore input fuel i (input.drop i) out
    else translateLoop m ignore input fuel 0 input []

/-- `unicode_translate`, unicodeobject.c:13297-13301. -/
def unicodeTranslate (s : Str) (m : Mapping) : Py Str := translateCharmap m true s

/-- `PyUnicode_Translate(str, mapping, NULL)`, unicodeobject.c:9505-9512. -/
def pyUnicodeTranslateStrict (s : Str) (m : Mapping) : Py Str := translateCharmap m false s

/-! ## `str.maketrans` -/

/-- A key of the dict argument. -/
inductive MkKey where
  | str (s : Str)
  | int (v : Int)
  | other
  deriving Repr, DecidableEq

/-- The first argument of `maketrans`. -/
inductive MkArg where
  | str (s : Str)
  /-- An exact `dict` or `frozendict`: `PyAnyDict_CheckExact`. -/
  | dict (items : List (MkKey × MapItem))
  | other
  deriving Repr, DecidableEq

abbrev TransDict := List (Int × MapItem)

/-- `PyDict_SetItem`: replace in place or append. -/
def dictSet : TransDict → Int → MapItem → TransDict
  | [], k, v => [(k, v)]
  | e :: es, k, v => if e.1 = k then (k, v) :: es else e :: dictSet es k v

/-- The `while (PyDict_Next ...)` loop, unicodeobject.c:13135-13171. The two
messages lack a space in the C source. -/
def maketransFromDict (items : List (MkKey × MapItem)) (d : TransDict) : Py TransDict :=
  match items with
  | [] => .ok d
  | (.str s, value) :: rest =>
    match s with
    | [c] => maketransFromDict rest (dictSet d c value)
    | _ => .error (.valueError "string keys in translatetable must be of length 1")
  | (.int k, value) :: rest => maketransFromDict rest (dictSet d k value)
  | (.other, _) :: _ =>
    .error (.typeError "keys in translate table mustbe strings or integers")

/-- The first loop of `unicode_maketrans_impl`, unicodeobject.c:13229-13243. -/
def maketransPairs (d : TransDict) : List Nat → List Nat → TransDict
  | x :: xs, y :: ys => maketransPairs (dictSet d x (.int y)) xs ys
  | _, _ => d

/-- The second loop, unicodeobject.c:13248-13256. -/
def maketransDelete (d : TransDict) (z : List Nat) : TransDict :=
  z.foldl (fun d (c : Nat) => dictSet d c .pyNone) d

/-- `unicode_maketrans_impl`, unicodeobject.c:13199-13277. -/
def unicodeMaketrans (x : MkArg) (y z : Option Str) : Py TransDict :=
  match y with
  | some y =>
    match x with
    | .str xs =>
      if xs.length != y.length then
        .error (.valueError "the first two maketrans arguments must have equal length")
      else
        let d := maketransPairs [] xs y
        match z with
        | some z => .ok (maketransDelete d z)
        | none => .ok d
    | _ => .error (.typeError
        "first maketrans argument must be a string if there is a second argument")
  | none =>
    match x with
    | .dict items => maketransFromDict items []
    | _ => .error (.typeError "if you give only one argument to maketrans it must be a dict")

/-- The table as a `Mapping`: `dict.__getitem__`. -/
def dictMapping (d : TransDict) : Mapping := fun c =>
  match d.find? (·.1 == (c : Int)) with
  | some e => e.2
  | none => .missing

end PyLean.UnicodeObj
