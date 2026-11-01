import PyLean.UnicodeObj.ObjectKinds

/-!
`PyUnicode_Join` and `_PyUnicode_JoinArray`: Objects/unicodeobject.c:10019-10209.

Once the items are in an array nothing here runs Python code, so the only fallible objects are
those of `PySequence_Fast`, Objects/abstract.c, before that. `PyUnicode_New` failing is allocation
failure, and is not modelled.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- An item of the sequence. -/
inductive JItem where
  /-- `PyUnicode_CheckExact`. -/
  | exact (s : Str)
  /-- An instance of a subclass of `str`. -/
  | sub (s : Str)
  /-- Anything else, by `tp_name`. -/
  | other (tpName : String)
  deriving Repr

/-- The separator: NULL, a `str`, or something else. -/
inductive JSep where
  | null
  | str (s : Str)
  | other (tpName : String)

/-- The iterable. -/
inductive JSeq where
  /-- An exact `list` or `tuple`: `PySequence_Fast` returns it, and nothing is iterated. -/
  | array (items : List JItem)
  /-- What `next` does, in order, ending in `StopIteration`. -/
  | iter (steps : List (Py JItem))
  /-- `PyObject_GetIter` raises this. -/
  | getIterFails (e : PyExc)

/-- `PySequence_List` of an iterator: the first exception ends it, whatever came before. -/
def iterList : List (Py JItem) → Py (List JItem)
  | [] => .ok []
  | .error e :: _ => .error e
  | .ok x :: t => do return x :: (← iterList t)

/-- `PySequence_Fast`, Objects/abstract.c. Only a `TypeError` from `PyObject_GetIter` is replaced,
not one raised while iterating. -/
def sequenceFast : JSeq → Py (List JItem)
  | .array items => .ok items
  | .iter steps => iterList steps
  | .getIterFails (.typeError _) => .error (.typeError "can only join an iterable")
  | .getIterFails e => .error e

/-- `PyUnicode_MAX_CHAR_VALUE` of a canonical string. -/
def strMaxValue (s : Str) : Nat :=
  match canonicalKind s with
  | .ascii => 127
  | .ucs1 => 255
  | .ucs2 => 65535
  | .ucs4 => 0x10ffff

/-- `%.80s`. -/
def tpName80 (n : String) : String := String.ofList (n.toList.take 80)

/-- The state of the pre-pass, unicodeobject.c:10107-10140. `last` is the width of `last_obj`. -/
structure JPass where
  sz : Nat
  maxchar : Nat
  useMemcpy : Bool
  last : Option Nat

/-- The pre-pass. `i` is the index in the array, and `seplen` is added from the second item on. -/
def joinPrepass (seplen : Nat) : Nat → List JItem → JPass → Py JPass
  | _, [], p => .ok p
  | i, .other tp :: _, _ =>
    .error (.typeError s!"sequence item {i}: expected str instance, {tpName80 tp} found")
  | i, x :: t, p =>
    let s : Str := match x with
      | .exact s | .sub s => s
      | .other _ => []
    let addSz := s.length + (if i != 0 then seplen else 0)
    if (addSz : Int) > ssizeMax - p.sz then
      .error (.overflowError "join() result is too long for a Python string")
    else
      let width := (canonicalKind s).width
      joinPrepass seplen (i + 1) t
        { sz := p.sz + addSz
          maxchar := max p.maxchar (strMaxValue s)
          useMemcpy := p.useMemcpy && (match p.last with | some w => w == width | none => true)
          last := some width }

/-- The text of an item. -/
def JItem.text : JItem → Str
  | .exact s | .sub s => s
  | .other _ => []

/-- The copy loops, unicodeobject.c:10157-10199. `use_memcpy` only chooses how bytes move, so both
loops are this one; `JoinMemcpySafe` is the fact that makes the `memcpy` one valid. -/
def joinCopy (sep : Str) (seplen : Nat) : Nat → List JItem → Str
  | _, [] => []
  | i, x :: t =>
    (if i != 0 && seplen != 0 then sep else []) ++ x.text ++ joinCopy sep seplen (i + 1) t

/-- What `_PyUnicode_JoinArray` returns. -/
inductive JOut where
  /-- The item itself: `Py_NewRef(items[0])`. -/
  | itself
  /-- A new string, its kind, and whether the `memcpy` path was taken. -/
  | fresh (text : Str) (kind : Kind) (memcpy : Bool)
  deriving Repr, DecidableEq

/-- `_PyUnicode_JoinArray`, unicodeobject.c:10045-10209. -/
def joinArray (separator : JSep) (items : List JItem) : Py JOut :=
  let run (sepText : Str) (seplen maxchar : Nat) (last : Option Nat) : Py JOut :=
    match joinPrepass seplen 0 items { sz := 0, maxchar, useMemcpy := true, last } with
    | .error e => .error e
    | .ok p => .ok (.fresh (joinCopy sepText seplen 0 items) (kindOfMax p.maxchar) p.useMemcpy)
  match items with
  | [] => .ok (.fresh [] .ascii true)
  | [.exact _] => .ok .itself
  | [_] => run [] 0 0 none
  | _ =>
    match separator with
    | .null => run [32] 1 32 (some 1)
    | .other tp =>
      .error (.typeError s!"separator: expected str instance, {tpName80 tp} found")
    | .str s => run s s.length (strMaxValue s) (some (canonicalKind s).width)

/-- `PyUnicode_Join`, unicodeobject.c:10020-10042. -/
def pyUnicodeJoin (separator : JSep) (seq : JSeq) : Py JOut := do
  joinArray separator (← sequenceFast seq)

end PyLean.UnicodeObj
